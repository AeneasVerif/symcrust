import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.RowCol
import Mathlib.Tactic.IntervalCases
import Aeneas
import Symcrust.Spec.NatBit
import Symcrust.Spec.Round
import Sha3.Spec

-- JSON sandbox
import Lean.Data.Json
open Lean Json

/-!
The spec of ML-KEM, based on: https://csrc.nist.gov/pubs/fips/203/final
-/

namespace Symcrust.Spec

open Aeneas.Notations.SRRange  -- allows the `[0:256:2*len]` notations to desugar to an `SRRange` instead of a `Std.Range`
open Aeneas.Notations.DivRange -- activates the `[start : >stop : /divisor]` notation
open Aeneas.Notations.MulRange -- activates the `[start : <stop : *mul]` notation

namespace Notations

  -- Overloading the `get_elem_tactic` so that notation `l[i]` works
  scoped macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| scalar_tac)

  /-!
  lemma add_stride_le_of_mod
    {stride n start : ℕ}
    (hdiv   : stride ∣ n)
    (hstart : start < n)
    (hmod   : start % stride = 0) :
    start + stride ≤ n := by
    obtain ⟨t, rfl⟩ :
      ∃ t, start = stride * t := by
        have h := Nat.mod_add_div start stride
        have h' : stride * (start / stride) = start := by
          simpa [hmod, zero_add] using h
        exact ⟨start / stride, h'.symm⟩
    rcases hdiv with ⟨q, rfl⟩
    have ht_lt_q : t < q := Nat.lt_of_mul_lt_mul_left hstart
    have : t + 1 ≤ q := Nat.succ_le_of_lt ht_lt_q
    have : stride * (t + 1) ≤ stride * q := Nat.mul_le_mul_left _ this
    simpa
  -/

  @[scalar_tac]
  theorem div_range_in_bounds {len start : ℕ}
    (h0 : 1 < len ∧ len ≤ 128 ∧ ∃ k, len = 128 / 2 ^ k)
    (h1 : start < 256 ∧ start % (2 * len) = 0) : start + 2 * len ≤ 256 := by
      rcases h0 with ⟨hlen_gt, hlen_le, ⟨k, hk⟩⟩
      have: k ≤ 6 := by
        have k_le : 2^k <= 2^6 := by
          rw [hk] at hlen_gt
          have: 0 < 2^k := by
            apply pow_pos
            decide
          have := (Nat.le_div_iff_mul_le this).mp hlen_gt
          have h : 2 * 2^k ≤ 2 * 2^6 := this
          apply Nat.le_of_mul_le_mul_left h
          decide
        contrapose! k_le
        apply Nat.pow_lt_pow_right (by decide)
        exact k_le
      interval_cases k <;> simp_all <;> omega

  @[scalar_tac]
  theorem mul_range_add_in_bounds {len start : ℕ}
    (h0 : 2 ≤ len ∧ len < 256 ∧ ∃ k, len = 2 * 2 ^ k)
    (h1 : start < 256 ∧ start % (2 * len) = 0) : start + 2 * len ≤ 256 := by
      rcases h0 with ⟨_, hlen_lt, ⟨k, hk⟩⟩
      have: k <= 6 := by
        contrapose hlen_lt
        simp_all
        have: 256 = 2 * 2^7 := by simp
        rw [this]
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by decide)
        exact hlen_lt
      interval_cases k <;> simp_all <;> omega

end Notations

open Notations

@[reducible] def Q : Nat := 3329
@[reducible] def Zq := ZMod Q
@[reducible] def Polynomial (n : ℕ := Q) := Vector (ZMod n) 256

abbrev Polynomial.length {m : ℕ} (p : Polynomial m) : ℕ := p.size

def Polynomial.zero (n := Q) : Polynomial n := Vector.replicate 256 0

instance {m} : HAdd (Polynomial m) (Polynomial m) (Polynomial m) where
  hAdd f g := Vector.map (fun i => f[i]! + g[i]!) (Vector.range 256)

instance {m} : HSub (Polynomial m) (Polynomial m) (Polynomial m) where
  hSub f g := Vector.map (fun i => f[i]! - g[i]!) (Vector.range 256)

def Polynomial.scalarMul (x : Polynomial n) (k : ZMod n) : Polynomial n := x.map fun v => v * k

instance {n} : HMul (Polynomial n) (ZMod n) (Polynomial n) where
  hMul := Polynomial.scalarMul

/-! # Algorithm 3 -/
def bitsToBytes {l : Nat} (b : Vector Bool (8 * l)) : Vector Byte l := Id.run do
  let mut B := Vector.replicate l 0
  for h: i in [0:8*l] do
    B := B.set (i/8) (B[i/8] + (b[i].toNat * (2 ^(i%8)) : BitVec 8))
  pure B

/--
info: [10#8, 1#8]
-/
#guard_msgs in
#eval (@bitsToBytes 2 ⟨ ⟨ [false, true, false, true, false, false, false, false,
                            true, false, false, false, false, false, false, false] ⟩,
                           by simp ⟩).toList

/-! # Algorithm 4 -/
def bytesToBits {l : Nat} (B : Vector Byte l) : Vector Bool (8 * l) := Id.run do
  let mut C := B
  let mut b := Vector.replicate (8 * l) false
  for hi: i in [0:l] do
    for hj: j in [0:8] do
      b := b.set (8*i + j) (C[i] % 2 ≠ 0)
      C := C.set i (C[i] / 2)
  pure b

#assert
  let b : Vector Bool (8 * 2) :=
    ⟨ ⟨ [false, true, false, true, false, false, false, false,
         true, false, false, false, false, false, false, false] ⟩, by simp ⟩
  bytesToBits (bitsToBytes b) = b

/-! # Cryptographic Functions -/
-- TODO: would be good to move this to the top of the file

-- TODO: Is using bytesToBits and bitsToBytes the correct behavior?
-- TODO: use Lists rather than Arrays in Sha3?
def sha3_256 (M : Array Byte) : Vector Byte 32 :=
  let M_bits := bytesToBits M.toVector
  bitsToBytes (Spec.SHA3_256 M_bits.toArray)

def sha3_512 (M : Array Byte) : Vector Byte 64 :=
  let M_bits := bytesToBits M.toVector
  bitsToBytes (Spec.SHA3_512 M_bits.toArray)

def shake256 (M : Array Byte) (x : ℕ) : Vector Byte (x / 8) :=
  let M_bits := bytesToBits M.toVector
  bitsToBytes ((Spec.SHAKE256 M_bits.toArray x).setWidth (8 * (x / 8)))

/-! # Pseudorandom function (PRF) -/

abbrev Η := {η : ℕ // η ∈ ({2, 3} : Set ℕ)}

def PRF (η : Η) (s : Vector Byte 32) (b : Byte) : Vector Byte (64 * η) :=
  (shake256 (s.toArray ++ #[b]) (8 * 64 * η)).cast (by scalar_tac)

/-! # Hash functions -/

def H (s : Array Byte) := sha3_256 s
def J (s : Array Byte) := shake256 s (8 * 32)
def G (s : Array Byte) : Vector Byte 32 × Vector Byte 32 :=
  let hash := sha3_512 s
  let a : Vector Byte 32 := (hash.extract 0 32).cast (by scalar_tac)
  let b : Vector Byte 32 := (hash.extract 32 64).cast (by scalar_tac)
  (a, b)


/-! # eXtendable-Output Function (XOF) -/

def XOF.init := Spec.SHAKE128Init
def XOF.absorb (ctx : Spec.Bitstring (Spec.b 6)) (B : Array Byte) : Spec.Bitstring (Spec.b 6) :=
  let B_bits := bytesToBits B.toVector
  Spec.SHAKE128Absorb ctx (B_bits).toArray
def XOF.squeeze (ctx : Spec.Bitstring (Spec.b 6)) (z : ℕ) : Spec.Bitstring (Spec.b 6) × Vector Byte z :=
  let (ctx, B) := Spec.SHAKE128Squeeze ctx (8 * z)
  (ctx, bitsToBytes B)

/-! # Compress -/

abbrev m (d : ℕ) : ℕ := if d < 12 then 2^d else Q

def compress (d : {d: ℕ // d < 12}) (x : Zq) : ZMod (m d) := ⌈ ((2^d.val : ℚ) / (Q : ℚ)) * x.val ⌋

def Polynomial.compress (d : {d: ℕ // d < 12}) (f : Polynomial) : Polynomial (m d) :=
  f.map (Spec.compress d)

/-! # Decompress -/
def decompress (d : {d: ℕ // d < 12}) (y : ZMod (m d)) : Zq := ⌈ ((Q : ℚ) / (2^d.val : ℚ)) * y.val ⌋

def Polynomial.decompress (d : {d: ℕ // d < 12}) (f : Polynomial (m d)) : Polynomial :=
  f.map (Spec.decompress d)

/-! # Algorithm 5 -/
def byteEncode (d : ℕ) (F : Polynomial (m d)) : Vector Byte (32 * d) := Id.run do
  let mut b := Vector.replicate (256 * d) false
  for hi: i in [0:256] do
    have : i * d ≤ 255 * d := by scalar_tac +nonLin
    let mut a : ℕ ← F[i].val
    for hj: j in [0:d] do
      b := b.set (i * d + j) (Bool.ofNat (a % 2))
      a := (a - b[i * d + j].toNat) / 2
  let B := bitsToBytes (Vector.cast (by ring_nf) b)
  pure B

/-! # Algorithm 6 -/
def byteDecode {d : ℕ} (B : Vector Byte (32 * d)) : Polynomial (m d) := Id.run do
  let b ← bytesToBits B
  let mut F := Polynomial.zero (m d)
  for hi: i in [0:256] do
    have : i * d ≤ 255 * d := by scalar_tac +nonLin
    F := F.set i (∑ (j : Fin d), b[i * d + j].toNat * 2^j.val)
  pure F

/-! # Algorithm 7 -/
def sampleNTT (B : Vector Byte 34) : Polynomial := Id.run do
  let mut ctx := XOF.init
  ctx := XOF.absorb ctx B.toArray -- TODO: Is this correct in terms of bytes-to-bits conversion?
  let mut a := Polynomial.zero
  let mut j : Nat := 0
  while hj : j < 256 do
    let (ctx', C) := XOF.squeeze ctx 3
    ctx := ctx'
    let d1 : Nat := C[0].val + 256 * (C[1].val % 16)
    let d2 : Nat := C[1].val/16 + 16 * C[2].val
    if d1 < Q then
      a := a.set j d1
      j := j + 1
    if h: d2 < Q ∧ j < 256 then
      a := a.set j d2
      j := j + 1
  pure a

/-! # Algorithm 8 -/

@[scalar_tac η.val]
theorem H.val (η : Η) : η.val ≤ 3 := by
  have := η.property
  scalar_tac

def samplePolyCBD {η:Η} (B : Vector Byte (64 * η)) : Polynomial := Id.run do
  let b := bytesToBits B
  let mut f := Polynomial.zero
  for hi: i in [0:256] do
    have : 2 * i * η ≤ 510 * η := by scalar_tac +nonLin
    let x := ∑ (j : Fin η), b[2 * i * η + j].toNat
    let y := ∑ (j : Fin η), b[2 * i * η + η + j].toNat
    f := f.set i (x - y)
  pure f

def ζ : ZMod Q := 17

/-! # Algorithm 9 -/
def ntt (f : Polynomial) : Polynomial := Id.run do
  let mut f := f
  let mut i := 1
  for h0: len in [128 : >1 : /= 2] do
    for h1: start in [0:256:2*len] do
      let zeta := ζ ^ (bitRev 7 i)
      i := i + 1
      for h: j in [start:start+len] do
        let t := zeta * f[j + len]
        f := f.set (j + len) (f[j] - t)
        f := f.set j (f[j] + t)
  pure f

/-! # Algorithm 10 -/
def invNtt (f : Polynomial) : Polynomial := Id.run do
  let mut f := f
  let mut i := 127
  for h0: len in [2 : <256 : *= 2] do
    for h1: start in [0:256:2*len] do
      let zeta := ζ ^(bitRev 7 i)
      i := i - 1
      for h: j in [start:start+len] do
        let t := f[j]
        f := f.set j (t + f[j + len])
        f := f.set (j + len) (zeta * (f[j + len] - t))
  f := f * (3303 : Zq)
  pure f

/-! # Algorithm 12 -/
def baseCaseMultiply (a0 a1 b0 b1 γ : Zq) : Zq × Zq :=
  let c0 := a0 * b0 + a1 * b1 * γ
  let c1 := a0 * b1 + a1 * b0
  (c0, c1)

/-! # Algorithm 11 -/
def multiplyNTTs (f g : Polynomial) : Polynomial := Id.run do
  let mut h := Polynomial.zero
  for h: i in [0:128] do
    let (c0, c1) := baseCaseMultiply f[2 * i] f[2 * i + 1] g[2 * i] g[2 * i + 1] (ζ^(2 * bitRev 7 i + 1))
    h := h.set (2 * i) c0
    h := h.set (2 * i + 1) c1
  pure h

/-! # ML-KEM parameter sets -/
-- TODO: would be good to move this to the top of the file

abbrev K := {k : ℕ // k ∈ ({2, 3, 4}: Set ℕ)}

inductive ParameterSet where
  | MLKEM512 : ParameterSet
  | MLKEM768 : ParameterSet
  | MLKEM1024 : ParameterSet

@[reducible, scalar_tac_simps] def k (p : ParameterSet) : K :=
  match p with
  | .MLKEM512 => ⟨ 2, by scalar_tac ⟩
  | .MLKEM768 => ⟨ 3, by scalar_tac ⟩
  | .MLKEM1024 => ⟨ 4, by scalar_tac ⟩

@[reducible, scalar_tac_simps] def η₁ (p : ParameterSet) : Η :=
  match p with
  | .MLKEM512 => ⟨ 3, by scalar_tac ⟩
  | .MLKEM768 => ⟨ 2, by scalar_tac ⟩
  | .MLKEM1024 => ⟨ 2, by scalar_tac ⟩

def η₂ : Η := ⟨ 2, by scalar_tac ⟩

@[reducible, scalar_tac_simps] def dᵤ (p : ParameterSet) : ℕ :=
  match p with
  | .MLKEM512 => 10
  | .MLKEM768 => 10
  | .MLKEM1024 => 11

@[reducible, scalar_tac_simps] def dᵥ (p : ParameterSet) : ℕ :=
  match p with
  | .MLKEM512 => 4
  | .MLKEM768 => 4
  | .MLKEM1024 => 5

/-! # Vectors and Matrices of Polynomials -/

@[reducible] def PolyVector (m : ℕ) (k : K) := Vector (Polynomial m) k
def PolyVector.zero (m : ℕ) (k : K) : PolyVector m k := Vector.replicate k (Polynomial.zero m)

def PolyVector.ofFn {m : ℕ} {k : K} (f : Fin k → Polynomial m) : PolyVector m k :=
  Vector.ofFn f

def PolyVector.set {k : K} {m : ℕ} (v : PolyVector m k) (i : ℕ) (f : Polynomial m) (h : i < k := by get_elem_tactic) : PolyVector m k :=
  Vector.set v i f

def PolyVector.add {k : K} {m : ℕ} (v w : PolyVector m k) : PolyVector m k :=
  Vector.ofFn fun i => v[i] + w[i]

instance {k} {m} : HAdd (PolyVector m k) (PolyVector m k) (PolyVector m k) where
  hAdd f g := PolyVector.add f g

def PolyVector.mulNTT {k : K} (v w : PolyVector Q k) : PolyVector Q k :=
  Vector.ofFn fun i => multiplyNTTs v[i] w[i]

instance {k} : HMul (PolyVector Q k) (PolyVector Q k) (PolyVector Q k) where
  hMul f g := PolyVector.mulNTT f g

def PolyVector.NTT {k : K} (v : PolyVector Q k) : (PolyVector Q k) :=
  v.map ntt

def PolyVector.invNTT {k : K} (v : PolyVector Q k) : (PolyVector Q k) :=
  v.map invNtt

def PolyVector.compressVec {k : K} (d : {d: ℕ // d < 12}) (v : PolyVector Q k) : PolyVector (m d) k :=
  v.map (Polynomial.compress d)

def PolyVector.decompress {k : K} (d : {d: ℕ // d < 12}) (v : PolyVector (m d) k) : PolyVector Q k :=
  v.map (Polynomial.decompress d)

def PolyVector.byteEncode {k : K} (d : ℕ) (v : PolyVector (m d) k) : Vector Byte (k * (32 * d)) := Id.run do
  (Vector.flatten (v.map (Spec.byteEncode d))).cast (by scalar_tac)

def PolyVector.byteDecode {k : K} (d : ℕ) (bytes : Vector Byte (32 * d * k)) : PolyVector (m d) k :=
  PolyVector.ofFn fun i =>
    have : 32 * d * (i + 1) ≤ 32 * d * k := by simp_scalar
    Spec.byteDecode ((bytes.extract (32 * d * i) (32 * d * (i + 1))).cast (by simp_scalar; ring_nf; scalar_tac))

@[reducible] def PolyMatrix (n : ℕ) (k : K) := Matrix (Fin k) (Fin k) (Polynomial n)
def PolyMatrix.zero (n : ℕ) (k : K) : PolyMatrix n k := Matrix.of (fun _ _ ↦ Polynomial.zero n)
def PolyMatrix.update {k : K} {n : ℕ} (M : PolyMatrix n k) (i j : ℕ) (val : Polynomial n)
  (hi : i < k := by get_elem_tactic) (_ : j < k := by get_elem_tactic) : PolyMatrix n k :=
  Matrix.updateRow M ⟨i, hi⟩ (fun k => if k = j then val else (M ⟨i,hi⟩ k))

/-- A ∘ v -/
def PolyMatrix.MulVectorNTT {k : K} (A : PolyMatrix Q k) (v : PolyVector Q k) : PolyVector Q k :=
  PolyVector.ofFn fun i => Id.run do
    let mut wi := Polynomial.zero
    for hj: j in [0:k] do
      wi := wi + (multiplyNTTs (A ⟨i, by scalar_tac⟩ ⟨j, by scalar_tac⟩) v[j])
    pure wi

/-- A ∘ v -/
instance {k} : HMul (PolyMatrix Q k) (PolyVector Q k) (PolyVector Q k) where
  hMul A v := PolyMatrix.MulVectorNTT A v

/-- v^t ∘ w -/
def PolyVector.innerProductNTT {k : K} (v : PolyVector Q k) (w : PolyVector Q k) : Polynomial := Id.run do
  let mut a := Polynomial.zero
  for hi: i in [0:k] do
    a := a + (multiplyNTTs v[i] w[i])
  pure a

/-! # Algorithm 13 -/

def kpke.keyGen (p : ParameterSet) (d : Vector Byte 32) :
  Vector Byte ((k p) * 384 + 32) × Vector Byte ((k p) * 384) := Id.run do

  let (ρ, σ) := G (d.toArray ++ #[Byte.ofNat (k p)])
  let mut N : ℕ := 0
  let mut A_hat := PolyMatrix.zero Q (k p)
  for hi: i in [0:k p] do
    for hj: j in [0:k p] do
      A_hat := PolyMatrix.update A_hat i j
        (sampleNTT (ρ ++ Vector.replicate 1 (Byte.ofNat j) ++ Vector.replicate 1 (Byte.ofNat i)))
  let mut s := PolyVector.zero Q (k p)
  for hi: i in [0:k p] do
    s := s.set i (samplePolyCBD (PRF (η₁ p) σ (Byte.ofNat N)))
    N := N + 1
  let mut e := PolyVector.zero Q (k p)
  for hi: i in [0:k p] do
    e := e.set i (samplePolyCBD (PRF (η₁ p) σ (Byte.ofNat N)))
    N := N + 1
  let s_hat := PolyVector.NTT s
  let e_hat := PolyVector.NTT e
  let t_hat := A_hat * s_hat + e_hat
  let ek_PKE := (PolyVector.byteEncode 12 t_hat) ++ ρ
  let dk_PKE := PolyVector.byteEncode 12 s_hat
  pure (ek_PKE, dk_PKE)


/-! # Algorithm 14 -/

def kpke.encrypt (p : ParameterSet)
  (ek_PKE : Vector Byte (384 * (k p) + 32))
  (m : Vector Byte 32)
  (r : Vector Byte 32) :
  Vector Byte (32 * ((dᵤ p) * (k p) + (dᵥ p))) := Id.run do

  let mut N : ℕ := 0
  let t_hat := PolyVector.byteDecode 12 ((ek_PKE.extract 0 ((k p) * 384)).cast (by cases p <;> scalar_tac))
  let ρ : Vector Byte 32 := (ek_PKE.extract (384 * (k p)) (384 * (k p) + 32)).cast (by cases p <;> scalar_tac)
  let mut A_hat := PolyMatrix.zero Q (k p)
  for hi: i in [0:k p] do
    for hj: j in [0:k p] do
      A_hat := PolyMatrix.update A_hat i j
        (sampleNTT (ρ ++ Vector.replicate 1 (Byte.ofNat j) ++ Vector.replicate 1 (Byte.ofNat i)))
  let mut y := PolyVector.zero Q (k p)
  for hi: i in [0:k p] do
    y := y.set i (samplePolyCBD (PRF (η₁ p) r (Byte.ofNat N)))
    N := N + 1
  let mut e₁ := PolyVector.zero Q (k p)
  for hi: i in [0:k p] do
    e₁ := e₁.set i (samplePolyCBD (PRF η₂ r (Byte.ofNat N)))
    N := N + 1
  let e₂ := samplePolyCBD (PRF η₂ r (Byte.ofNat N))
  let y_hat := PolyVector.NTT y
  let u := PolyVector.invNTT (A_hat.transpose * y_hat) + e₁
  let μ := Polynomial.decompress ⟨1, by scalar_tac⟩ (@byteDecode 1 m)
  let v := invNtt (PolyVector.innerProductNTT t_hat y_hat) + e₂ + μ
  let c₁ := PolyVector.byteEncode (dᵤ p) (PolyVector.compressVec ⟨ (dᵤ p), by cases p <;> scalar_tac ⟩ u)
  let c₂ := byteEncode (dᵥ p) (Polynomial.compress ⟨ (dᵥ p), by cases p <;> scalar_tac ⟩  v)
  (c₁ ++ c₂).cast (by cases p <;> scalar_tac)


/-! # Algorithm 15 -/

def kpke.decrypt (p : ParameterSet)
  (dk_PKE : Vector Byte (384 * (k p)))
  (c : Vector Byte (32 * ((dᵤ p) * (k p) + (dᵥ p)))) :
  Vector Byte 32 :=

  have : 32 * (dᵤ p) * (k p) ≤ 32 * ((dᵤ p) * (k p) + (dᵥ p)) := by simp_scalar; ring_nf; scalar_tac
  let c₁ : Vector Byte (32 * (dᵤ p) * (k p)) := (c.extract 0 (32 * (dᵤ p) * (k p))).cast (by simp_scalar)
  have : 32 * ((dᵤ p) * (k p) + (dᵥ p)) - 32 * (dᵤ p) * (k p) = 32 * (dᵥ p) := by simp_scalar; ring_nf; simp
  let c₂ : Vector Byte (32 * (dᵥ p)) := (c.extract (32 * (dᵤ p) * (k p)) (32 * ((dᵤ p) * (k p) + (dᵥ p)))).cast (by cases p <;> scalar_tac)
  let u' := PolyVector.decompress ⟨(dᵤ p), by cases p <;> scalar_tac⟩  (PolyVector.byteDecode (dᵤ p) c₁)
  let v' := Polynomial.decompress ⟨(dᵥ p) , by cases p <;> scalar_tac ⟩ (byteDecode c₂)
  let s_hat := PolyVector.byteDecode 12 (dk_PKE.cast (by simp_scalar))
  let w := v' - invNtt (PolyVector.innerProductNTT s_hat (PolyVector.NTT u'))
  let m := byteEncode 1 (Polynomial.compress ⟨1, by scalar_tac⟩ w)
  m


/-! # Algorithm 16 -/

def mlkem.keyGen_internal (p : ParameterSet)
  (d : Vector Byte 32)
  (z : Vector Byte 32) :
  (Vector Byte (384 * (k p) + 32)) × (Vector Byte (768 * (k p) + 96)) :=

  let (ek_PKE, dk_PKE) := kpke.keyGen p d
  let ek := ek_PKE.cast (by scalar_tac)
  let dk := (dk_PKE ++ ek ++ (H ek.toArray) ++ z).cast (by scalar_tac)
  (ek, dk)


/-! # Algorithm 17 -/

def mlkem.encaps_internal (p : ParameterSet)
  (ek : Vector Byte (384 * (k p) + 32))
  (m : Vector Byte 32) :
  Vector Byte 32 × Vector Byte (32 * ((dᵤ p) * (k p) + (dᵥ p))) :=

  let (K, r) := G ((m ++ (H ek.toArray))).toArray
  let c := kpke.encrypt p ek m r
  (K, c)


/-! # Algorithm 18 -/

def mlkem.decaps_internal (p : ParameterSet)
  (dk : Vector Byte (768 * (k p) + 96))
  (c : Vector Byte (32 * ((dᵤ p) * (k p) + (dᵥ p)))) :
  Vector Byte 32 :=

  let dk_PKE : Vector Byte (384 * (k p)) := (dk.extract 0 (384 * (k p))).cast (by scalar_tac)
  let ek_PKE : Vector Byte (384 * (k p) + 32) := (dk.extract (384 * (k p)) (768 * (k p) + 32)).cast (by scalar_tac)
  let h : Vector Byte 32 := (dk.extract (768 * (k p) + 32) (768 * (k p) + 64)).cast (by scalar_tac)
  let z : Vector Byte 32 := (dk.extract (768 * (k p) + 64) (768 * (k p) + 96)).cast (by scalar_tac)
  let m' := kpke.decrypt p dk_PKE c
  let (K', r') := G ((m' ++ h).toArray)
  let K_bar := J ((z ++ c).toArray)
  let c' := kpke.encrypt p ek_PKE m' r'
  let K' := if c ≠ c' then K_bar else K'
  K'


/-! # Algorithm 19 -/

/-! # Random byte generation -/
axiom randomBytes (length : ℕ) : Option (Vector Byte length)

/-
Not sure how to model randomness, so we simply take the random bytes as inputs.
-/
def mlkem.keygen (p: ParameterSet) (d z : Option (Vector Byte 32)) :
  Option ((Vector Byte (384 * (k p) + 32)) × (Vector Byte (768 * (k p) + 96))) := do
  let d ← d
  let z ← z
  let (ek, dk) := mlkem.keyGen_internal p d z
  return (ek, dk)


/-! # Algorithm 20 -/

/-
Not sure how to model randomness, so we simply take the random bytes as inputs.
-/
def mlkem.encaps (p: ParameterSet)
  (ek : Vector Byte (384 * (k p) + 32))
  (m : Option (Vector Byte 32)) :
  Option (Vector Byte 32 × Vector Byte (32 * ((dᵤ p) * (k p) + (dᵥ p)))) := do
  let m ← m
  let (K, c) := mlkem.encaps_internal p ek m
  return (K, c)

/-! # Algorithm 21 -/

def mlkem.decaps (p: ParameterSet)
  (dk : Vector Byte (768 * (k p) + 96))
  (c : Vector Byte (32 * ((dᵤ p) * (k p) + (dᵥ p)))) :
  Vector Byte 32 :=

  let K' := mlkem.decaps_internal p dk c
  K'



-- parsing JSON strings into Vector Byte (no library for it?)

/-- Convert a nibble (0..15) to its lowercase hex character. -/
def Byte.toHex (b : Byte) : Char :=
  if b < 10 then
    Char.ofNat ('0'.toNat + b.val)
  else
    Char.ofNat ('a'.toNat + (b.val - 10))

def Vector.toHex {n} (v : Vector Byte n) : String :=
  Id.run do
    let mut s := ""
    for b in v do
      s := s.push (Byte.toHex (b / 16))
      s := s.push (Byte.toHex (b % 16))
    pure s

instance {n} : ToString (Vector Byte n) where
  toString v := Vector.toHex v

def HexChar.toByte? (c : Char) : Option Byte :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + (c.toNat - 'A'.toNat))
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + (c.toNat - 'a'.toNat))
  else none

def Hex.toBytes? (s : String) : Option (Array Byte) :=
  let rec go : List Char → Array Byte → Option (Array Byte)
  | hi :: lo :: rest, acc => do
      let hi ← HexChar.toByte? hi
      let lo ← HexChar.toByte? lo
      go rest (acc.push (16 * hi + lo))
  | [], acc => some acc
  | _ , _   => none  -- (shouldn’t happen if length is even)
  go s.data #[]

def Hex.toVector? (s : String) (n : Nat) : Option (Vector Byte n) := do
  let arr ← Hex.toBytes? s
  if h : arr.size = n then
    pure ⟨arr, h⟩
  else
    none

open Lean Macro

syntax "x!" str : term
macro_rules
  | `(x! $s:str) => do
      let hex := s.getString
      if hex.length % 2 != 0 then
        Macro.throwError s!"hex!: odd number ({hex.length}) of hex characters (must be even)."
      let n := Lean.quote (hex.length / 2)
      let h := Lean.quote hex
      `(match Hex.toVector? $h $n with
        | some a => a
        | none => panic! ("hex!: invalid hex literal: " ++ $h))

--let d := hex!"7c9935a0b07694aa0c6d10e4db6b1add2fd81a25ccb148032dcd739936737f2d"
--let z := hex!"8626ed79d451140800e03b59b956f8210e556067407d13dc90fa9e8b872bfb8f"


def compare {n} (s : String) (v0 v1 : Vector Byte n) : IO Unit := do
  if v0 ≠ v1 then
    let cmp i (b: Byte) (h : i < n) : Byte := v0[i] - v1[i]
    let diff := Vector.mapFinIdx v0 cmp
    IO.println s!"{s} FAIL"
    IO.println s!"  expected: {v0}"
    IO.println s!"  got:      {v1}"
    IO.println s!"  diff:     {diff}"

def test_sha3_256 : IO Unit := do
  let h := x!"a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
  let h1 := Spec.SHA3_256 #[]
  let h1 := bitsToBytes h1
  compare "sha3_256" h h1
  IO.println s!"  You may ignore the following eval failure, it's expected."

#eval test_sha3_256

-- test 1.1 from https://github.com/usnistgov/ACVP-Server/tree/master/gen-val/json-files/ML-KEM-keyGen-FIPS203
def test_keyGen : IO Unit := do
  let d  := x!"BBA3C0F5DF044CDF4D9CAA53CA15FDE26F34EB3541555CFC54CA9C31B964D0C8"
  let z  := x!"0A64FDD51A8D91B3166C4958A94EFC3166A4F5DF680980B878DB8371B7624C96"
  let ek := x!"1CAB32BE749CA76124EE19907B9CCB7FD30F8B2C38DC970E81F9956C97A8BD3C6E37B07C29E60BB2B75C5258B572626A859ABA89DB3AABC571424618B26310278B8EC4E76ED07A10B864AABF37BFC9F364731050631421BFCB1C3B9153D4316A95089197A027AB80B39C362CE6D97EFF422244FB81AAF67354F03894CC25B2707939A4A06D302C59D106EB743678DAA3F1D1C3F46B03F0DAA0641835A548363180744E6B6235B84DB9A4628279A6EF7231499208E657A3F9BB6E3F782606B79FC9A38723576FA80898E8A6887D94C3ED774E46A86CFE705B34C6B5535865329C5A4A820F9114CE9A9C68495C726368B9E073CBBE627A7DE419F7F7B4AD221576F91FB1E66CFF9651BD6C25E3CC9CA49A570CF041E457658072B684E714BD6A86B3D05C7597A729E12E512C8D7E5B5C27049EFB0AC0E085B1B88347BFD314B4E4AB4B8875A489ADB8C9AE28008BAD36AAAD24683563BFAF19BDA8677AB7BAC7E33C3087B84A45246A2AB1AEF397750D386ACDAC63C87506166A0FAE18773F530E74545D54BC670DD7353B75B16373CB8A6269AF37097EE1B1640458153132AD80AB64F7A599B8670E301205043C136C56CA5A06DBFABA3204671C1B237B18824555B5DDB206A74ACE637005B363238378BDA5E198AD69B85CBB399E8B07CB899F9E93CF6CF62FCAFC9E4D77363CA2149E92197F2133223799C182CF5F182ECD35B5FDFCBF0A93A1350198F2F244F3216B442A22FDDB2F4F3BB8CBF0168D0220AA725A0E287DF08079A1DBB8747C02F0C2C829759A5D95B6237522E7F71AB5669390377E03A93AB7FC7E9FD6BB59C1B9B8CC966141B0BA6796E66829D6A403B1F5816C8557EE8841031B2ED6C6CCFE8A55B39B9273F8BA050B1B328C7B9A238A7B8324F16A7A474C0B5721B9C8246531E19208838356F3337768BCB3397B4E01CC26175B67A66DFCD11F07B295C20AB484A60E7D086DB39B8301845B654A484462508FA78506357BBBF42DBAC157BCA7769C099A0B1894D4A17256F504EBE50BE284656F653845A26B00856D76A8A5A166CD09D04705261EBAFA20687A1068D9B9E28326848B67A0A3994D2DBA4B7A8F623B901E17CBEE610847A2903301C58287"
  let dk := x!"C8D473A9EA0987F356FB309356A39E766633746B8FBAF03D588495E4B1CC87E4B283C871514182D3E1844D9ACB4FA5948BC38D85E05478BB699E41170FA593F7D74226D4597655C5DE80AC8C79181EE750121685C71797D3B5C240676637C7BDEBA61969508C3FABB4CD97CC53C529EBC993C4B883B2B52F42789F64C022620B624B8107E0E55FFE29280BB005DC66A83A0A219A0080F8E656729B29CBF8AA7866358694C94E477E499A055C8A8ECAC7338F461897329ED02B1EF0F0AB627B71B5322692268578B11E5EC203E674251C0182C10C775971247537358C0651EF21704CC68B57D5CF61C627C0AB30DE5743FB027B40D86071531F0C8B67092BAC18361FACEC1BFC53C65D512B3911156A991F462C8588D638526389E3CAAC808809EB7B50ACB83A10142C954B9AC938B983133D5D024303790DF848B7FB06AE4C751DAEDBAF08728A96C481B5A84B53FA37DEEAC6174C745F3C0821553CC88858C3DB392570AA388624CFA98E7232970B746BCF301642D92F3E452E3BF99E24329C470A57B31AA765C8952333A334102605BB8099555230287F07A813109C427E692393540FAD769831756701B481611472A060CA1E7C34F9412371C7658F4C69C9C0BC956404B88AB27BC89ED7F751E51781D95A1D0DCC476E7A8FD4A54272B5A9679B0227176D481035A3864FD747B52739B8FA801713BC0757347BC96A022487BFA5A3C0E30B9FBEAA6838553D9111351FF49A73970263B39CDF180F163972AB993C1630A89A06A2FF69A274F27A819C3727E2244B23163B320DD568B227B6589A402A5E16333C70C4D3264CAC8A80BDC64705675788CC20FE083635D25C89F387F5B39580737F06287F236B7CCCA4CC3A69AC0E84B33B20BA7661B8BA9B575CC555DC820481FA9941A8C259D962273536B36B0BB1E434B18A63BE405583925CCA14001FF9AA28EA7FFF525ABA151944607056F6CD5052C823D00F33651BFBF428257B388544654E9A14F2E595BB4CC5D5929A03F62BC2DC6C6B885D86969B298A06F0294CAE69337944C4AEB5B22E126AEB02BD34083637299D2C41080481C61CAB32BE749CA76124EE19907B9CCB7FD30F8B2C38DC970E81F9956C97A8BD3C6E37B07C29E60BB2B75C5258B572626A859ABA89DB3AABC571424618B26310278B8EC4E76ED07A10B864AABF37BFC9F364731050631421BFCB1C3B9153D4316A95089197A027AB80B39C362CE6D97EFF422244FB81AAF67354F03894CC25B2707939A4A06D302C59D106EB743678DAA3F1D1C3F46B03F0DAA0641835A548363180744E6B6235B84DB9A4628279A6EF7231499208E657A3F9BB6E3F782606B79FC9A38723576FA80898E8A6887D94C3ED774E46A86CFE705B34C6B5535865329C5A4A820F9114CE9A9C68495C726368B9E073CBBE627A7DE419F7F7B4AD221576F91FB1E66CFF9651BD6C25E3CC9CA49A570CF041E457658072B684E714BD6A86B3D05C7597A729E12E512C8D7E5B5C27049EFB0AC0E085B1B88347BFD314B4E4AB4B8875A489ADB8C9AE28008BAD36AAAD24683563BFAF19BDA8677AB7BAC7E33C3087B84A45246A2AB1AEF397750D386ACDAC63C87506166A0FAE18773F530E74545D54BC670DD7353B75B16373CB8A6269AF37097EE1B1640458153132AD80AB64F7A599B8670E301205043C136C56CA5A06DBFABA3204671C1B237B18824555B5DDB206A74ACE637005B363238378BDA5E198AD69B85CBB399E8B07CB899F9E93CF6CF62FCAFC9E4D77363CA2149E92197F2133223799C182CF5F182ECD35B5FDFCBF0A93A1350198F2F244F3216B442A22FDDB2F4F3BB8CBF0168D0220AA725A0E287DF08079A1DBB8747C02F0C2C829759A5D95B6237522E7F71AB5669390377E03A93AB7FC7E9FD6BB59C1B9B8CC966141B0BA6796E66829D6A403B1F5816C8557EE8841031B2ED6C6CCFE8A55B39B9273F8BA050B1B328C7B9A238A7B8324F16A7A474C0B5721B9C8246531E19208838356F3337768BCB3397B4E01CC26175B67A66DFCD11F07B295C20AB484A60E7D086DB39B8301845B654A484462508FA78506357BBBF42DBAC157BCA7769C099A0B1894D4A17256F504EBE50BE284656F653845A26B00856D76A8A5A166CD09D04705261EBAFA20687A1068D9B9E28326848B67A0A3994D2DBA4B7A8F623B901E17CBEE610847A2903301C5828747D4B351E049B7757A2545602C398D2EBCF7C28804BCC8862E270D7324AB435E0A64FDD51A8D91B3166C4958A94EFC3166A4F5DF680980B878DB8371B7624C96"

  let t0 ← IO.monoMsNow
  let (ek1, dk1) := mlkem.keyGen_internal ParameterSet.MLKEM512 d z
  let t1 ← IO.monoMsNow
  IO.println s!"Keygen for MLKEM512 in {t1 - t0} ms."
  compare "keyGen ek" ek ek1
  compare "kenGen dk" dk dk1

-- test 1.1 from https://github.com/usnistgov/ACVP-Server/blob/master/gen-val/json-files/ML-KEM-encapDecap-FIPS203
def test_encaps : IO Unit := do
  let ek := x!"ADB031A018722F19C25829150A8B94297C9519173A2C908AEBF76F86C9724A0354300C6AB58A90C7B18A2E828B5FD2CDEACA9810EC00FD8CBB22AA6AE641B5824055A91B27C1F73518953913FA2037D295F42B7E34AABE90D72A2453B215D886EBE28779D76F4830B01A73291B5A7186454A91D665B9E6C04FE808F76AC25E298B97195999F866DBFABD571B59549787F5E316A0C65F3E9132089B219E11712D245AF955ACBFA36D37BB2DFD570ECF90941BD369E8023B2FF65F04D5408FA84531604A5EACCF3D62221429A1D6B1BE5FEB04EBA0BB698B6B6AE4CF72317D96E99B0A840AB55C275B9979BB231926D7140FC9B8C8124B87532E854113532A809C714D492746BEA7C30AA869DD780B77D0BADBBA9D9FE6A09780B1EE7076F5E3CAF5F470D004CB53098BFA340248835EC782B34D612C53701259D2583360935D8B5F25051BF196214D1CC6B33A8A47F41A65B5A143DB3651885214307B0D938F9D253672A4587EBC6D9743A3AFB35A3098149B27C3EA0BAAC5942D9A92856EB0447D1709ED70A673AA1FEBA5398A821FA21B215FD78866C29B1E75C50815CC3F093B7CA70717A10CCF8C1880072230163008AA675A17759937CA672A56BBA772C527A5F9F12D53267419559A7A1A0A3003B64D34ABC8F4294210B140F517BEE86F393BB577E6A41EB64A4EF633C8BA941314528B67A24F4829E99C96BF92022307A763A9086F7C597340C8FBBB0689DC1D28800BAD710422A9334A406B203101A6C97A3D00AC6C095735E22CBC60B3A0760C8B0268FB5BB3D7D0543BAB599FD326608264EA477EE8F8C178898FE7387F15A6B40B13B069D3B574967F8487309495420F20B23456CF6D010AB19CABA9B27CAE79B09D7084D1863359B40F205556456AAD5F92A5A36B49B737866901CF6FB47B59A9C5783C2C5FD95087DA417F7410708290B619B701852B051272AE0428263C28CB025E1C1103B2718A0DDA5FC30394600879AF509B62C57B88A018FEDB09642872591582ABB4AC1408A5750902589406E2479D3BC5AD8016610D7BA18D984EBD951393FC2B83446D474AC8E2A634F66F181976B8C14F6078DE84113D8E728FAC101A23C86300D795CAE9875436CC"
  let m  := x!"E8D6BAC09B25469BEE582A7DEE9BD21890CD3F0AF4D7E19E30B3E24E657C149C"
  let K  := x!"6C832560DFE97BECADFBB340EE31AE868A73120806EED02839518E5627D32968"
  let c  := x!"3244E86669E69F0F238E3CD7F03EF31C4D3CF48CEF726955F06EB5099367310D5D9FC70D48A573458837319BD1691D1A699A68F7A9A8DB73D03620E9E4BC4B088E5E9C5E3638EB3354F6EF3C5E7AE5D57D0571F078E174CFBD6EAE2FD76DC2BED5A907EBA531E89B1BA8D2A8EBE7B4CA0DE96BFF28D278A70549AA0635BE50096F297F7BEF92C6AE9C11C4204CFF07E0598F14495AEFBD207B760DAD34FC0AD8F4000A1911F89FA3B59410C8151B9A8914AA71269EB7E2C329586D3C08F3F10939A497717CCFA3EC5082D46750905CEB703106C2D3E5CD71F138704A20898B5F80F5FDA03C08F8894C2874DE32DFF5C27EA0437A44663C0D6F6B85332AD0F5A0E48D1638BBD281797AF1ADED5C5F1EB87D4723E17BCA439EC469489A371A402EEEAADF1A1BD7C7DA409E9A6414E744167DF13AA1ED9EBDB354BC0DD04190DBA3EC48E5D1DB61C54FE881F8A1DA32EB512F2423EA7F9015DC8C2C3D5B5FEA438A88E6C877A6F4ED17FAB8918E53887996D23956502ED9D3D07BBE8EC899AF55813D39CCF6C2700AC8805517317338655A221268E654839C49D83344A1DE0E75FDD63549B7D57258601C1C74B0FDEF80CAB109C54393A7669E4BDB5CDD3BC21731C1E467784DC6A165194487A94FDAA9C177A0BD4AB009B7D7BBD9EEBDA386492F7903CA7C4345A41271D8B6816B1AC0841B8DB7E2D518B3A2B70386CB5BA159A11FC50420F94C001E1F8F0268A2E0A4A12485C08D0BB696CAC92C8866DE78F18BA7C0E5C4C2F450EAB9E2B126DBA80EF70FFB611A010EC3AA9FBCFB2058C2491B331E63AE27321C0098B49C9F7BD409C70DA376A338317217AF310788772E2A95D1BCC29355B486E3B1FA11753C7D39802D183AAE86C3CAD2EB4E70B3C679E47F01D7FDA48B629E5B8AF315847D20BE7A64EA4A16AB9B237F00A9DC659E01735290902F243E866129F120CF3EC01CD668A9827AB419B7F9994A305782C6CB82801C4DA0B9032034B890A761182E4108EF016AE48AE32ED05544EFC7AADC9D219B4E2F7E892EE58130B7413AD2CD6B5E04CEB2593E06165E37BC8BE981EEE1C638"

  let t0 ← IO.monoMsNow
  let (K1, c1) := mlkem.encaps_internal ParameterSet.MLKEM512 ek m
  let t1 ← IO.monoMsNow
  IO.println s!"Encaps for MLKEM512 in {t1 - t0} ms."
  compare "encaps K" K K1
  compare "encaps c" c c1

-- test 4.76 from https://github.com/usnistgov/ACVP-Server/blob/master/gen-val/json-files/ML-KEM-encapDecap-FIPS203
def test_decaps : IO Unit := do
  let dk := x!"54301038DA5911366D16C417BFD96AEB85C5DA4AA45AF32F88A700BB9A973AB62684A052D793379B3C2B253B01A4E512AB34C8D8A76F5EBA5F1B28451A66632872C489F3CA606C6B36336895C032386BB35E98B43C8136350616CCF82A4C24816F4354B7C197940A62537BB36F2B8DE32A6AF6CAA100845FB62184B82B29DCE2662CA94D93FB027DB3C8EF858D4223540E79AD5D204C99637FB66718CD04782E149A07354D6FB2C742A9849506BDDECC0548367421FA2B8599443C74192D6B4B67CC5E16F8880087AC578ABCADB5492CC1AC6916CE73AB2858797134676260B22B28B4A8917C5ABD876EDA706CE381AA4985827D492A736652DD6C1DADD10ADF045DBF416158B0384A991D8501BAA9A714B82788C263C16858C81B978FD353126222A46E1587718872BB11513CDA3A88B6547BC464CD612548E581DFE106382428BA8452A86AC6ECB50B7B3C1CBEA571513C63B8741A2CB82C5055CDB2CB00CE9036C220A25C1BA21891B520D435342136D0C15AAFC12DBCC810E9C256D397A3D23A6287282AAEC038649151886A19F9B583806839EE86A12D131FB3E6A1CA1C9CC48626037B5F3DA74C8A025CC61A76078B07D00AA6DAD32C4147CDAADB4DF644A8DBF4222C47AEEF774BDAFA5A48258BDEA84E7B8B6A5CA09243589EF7F1C249A2B344068FC8D874C33B6C4C2782EA86AADE7C10EFDCC93FB993147A3B636127711195C121C7506759389373F896843991125D5A0AB8FB34595166A9109DC2D19AE2738444716C9C21BD06DC8145458ACBA30981A95F8E141BD17B17A3F645E9B63747E370E8D873937A858048614F0645F4B461EF769D2A696706C2811E756163E4746BF00CFFC556AD7A2F0804A6BEDC6A59B1546727C602A99397C50FF818721D5319F63B058D03BC9DE57C1DB74FE14A0D083C25B17886200633D230946DE0A148781735555CCE797040BB479FA733C2A808EE1CB9A285CF863CBDB47172F3A68EEA614736C73C71FA4AD82C6CF13C5CD3179AD296BF3BD6815D13CBFF75A3A99B4824B7560227BE0BD809BD43AED7D951ECDB7273719560DCC0E8C13F70EC19B39348974173A550A5C52A248E191D46640799A4365F3C254757350B65764984180A9ABC9048679D6A84C61B7405EC82A403B79569C024CACA55D79BE23C943C159DDADB17011820C7D88D54071FC8AB142727BE747BBD253A26E92071DC34716F5037D1988A889302621A8465D08ABFD2215D97575D730C9495617EF3B69D0C7AA79965CA985BC147797D9688116A20F9626BAB1997FCEAACBFB439D655A566B0A4BD08472265439C00CE487955EBEA094AD00A6A5AC6FB9359F3C11A6E4B3B6C714F70F8A7B8B6524572B34B758DA270753B697415A964170374548B9D1FE43FD80C62A4D951E28182F2848B044A8352E11F5198547B71215E6287DFF13A18287148277883926396D9A07C0B0139577E4923AC41C9C31F0B6067C88B94CBB9921513ACF0AE80D7779D72C666B256B72A777B56A2D12007797B7BE6657650EB42B1060AADC5157FB819EBF707E51637CD8469645196765A2EBFE8483D62C5E2422C27BCA84E5A0F69F45609928A7E51948A9464D5093CF463A39C26447126C684160F3A4298EA0B5B0973A15403CDDF286BEBFA587FFBB5BFA7692A404ABE3BB14014AEAC418900E4588676A5E7A21553F50037262E3DD6253A8BBD985A679F638F709545AB322F6DE71192FB60C0A368A3B06C8CF5267D792D6C2518EA0A27855635E3E68891C141123A1F8C80AA5300B151AC9AE4342334265C457CA8809891EFF12B398A8465F25508836EE3075C898822BA7675AC359D80E85FF84112C8502932016E24531FB24AA0F744B8252B3D89B4A41721BFD779A826AA46F00720B9592A12307B27EB2B5502987AB477161B72F31BB8EF2C2F4EA83823B72CB16532768508835852A701C3522A7B71DA1CD8B5CCA512117990709797C8AAEA3B300B79A28460D22A2C3527CBB8529AA667064FA2039E22AD5ED740BFA353EB04B74A9C9328266561A76A12EC2C33766697DABBDE92A712B81712D2C4E1F335AA642774441E917650F8D92278A8C0444214A774B7996463527756935171D9FA61D0B50454F74ED50831EB3138DB7374A35387BBCB23E40388BB9228C3A66CDD2222524D7CB8DAE2E70FE3D97847AC35824F5D58B54DD943A440DBFF4216429146E2AC9383962420545163D6F82456E1B93E22A1B2E6875ADA12D4E194AE93EF5C3485EEBBE1BB13C560480DC3471CD950EB300CF2D18F38CAE7575B133526"
  let c  := x!"9068502093766BB27635F12F3569794C54227CB1828128AEFC5B715CDCD1E9080D59FB218D17EA0D212D158DDB5ED0FFDB4FA9401F4F23387D32AC8B788CFB7A319114425138744002648B07D5216A3EFB4964BC72E98A6EA2939FAF372CAB44CD5D8A929F66C41D644118ACDE5DA2F09B87F8A1F41F55924A7784D8552790CDF256958E35324381902D9A006FAE02933B017A8E55931B6A0CC8CE3B5723D85DE4C4585FAEC0BD80986224CDAEA443556EBF8BCFDE162C258B9E0AB00C2B9DE0190384C61988BCF362BD0493D40D276FFE4873811EF2851204626342921BFB6A75EB6079F58C030AB1D9C1844078E61C29DB88B5FDC463B7AD3F770E1CB8B526BD9B9A5AFADADAED0368BEE0FFABD9ADFEB0FBF6E6DC7A36115BA47A292D454D7A31F5601BD8BD5435B2EF464A474E37B12B7794F356F905FDBEB248B44003F2B43B925CDB98017A68A15B8B90E2D6DAB1B72AC2921CA92F55B3453C2865DECC094E77EC1E70F99A14CE22BBBF7D3C25F1ECBF96478D84DB4EB1F5E077777214CDA31165C2790172EF778435B56B712E3C5C6B2FDFA3B40B45F7065731EC1E33A8FB300F9FD1EAB14A77E5D8367329E0F834A76E889EC2C8F80E5C1098055F2D517EC381A01F37B1AA3923894D90E1A25A8F55D3DB782ADCD644A1B8A168BBF263C77F34B1A3388E76528FD4F91BFDD7D6499EF99CF663964421FFBB6C17CA9456A2E6A3681298628FA728D3FCFB3BDB65A22E7CFC962FB83007F249D543696A8EFBD9A3DBC7C090F2C82B38E76ACB653F18E78407EFDEA120AE61CDCC8C28CAD984D776B69FB201BA3E154F3C87F53CF84DEF777E50BE420DDFB9734065B8D541F983E69E7FB2B48A186BF8338F3234A0B785B2BA63AA875B28EEE98843C48F60BA500E93067F283155A21905836AC33CA8B06790DD800DD000CC42171775A07F704229FB6F9E5123ED032148DD0EC616530B98A68BE3DBAD2A5D24FFABEFD6D78F4484C8A9969DB7480F54A3DDAB445D3C6C489A9E296B612591A027D624032CD1B11452FEA69A178006E8429BEAB1FC089098BE7EA3D73518F3F5E7B59843"
  let K  := x!"32FE0534E517EC8F87A25578EA047417EC479EECE897D2BA5F9D41A521FAEDCC"

  let t0 ← IO.monoMsNow
  let K1 := mlkem.decaps_internal ParameterSet.MLKEM512 dk c
  let t1 ← IO.monoMsNow
  IO.println s!"Decaps for MLKEM512 in {t1 - t0} ms."
  compare "decaps K" K K1


-- individual test case
structure TestCase where
  tcId : Nat    -- Test case ID
  c    : String -- Ciphertext or encapsulated key (hex string)
  k    : String -- Expected key or output (hex string)
  deriving FromJson, Repr

-- collection of test cases
structure TestGroup where
  tgId  : Nat           -- Test group ID
  tests : Array TestCase
  deriving FromJson, Repr

-- top-level expectedResults JSON object.
structure ExpectedResults where
  vsId      : Nat
  algorithm : String
  mode      : String
  revision  : String
  isSample  : Bool
  testGroups : Array TestGroup
  deriving FromJson, Repr

def trying_json  : IO Unit := do
  let jsonText ← IO.FS.readFile "/home/fournet/symcrust/proofs/Symcrust/Spec/encapDecap.json"
  let jsonVal := Json.parse jsonText
  match jsonVal with
  | .error err =>
      IO.eprintln s!"Failed to parse JSON: {err}"
      return  -- exit early or handle the error
  | .ok j =>
      let x ← IO.ofExcept (fromJson? j : Except String TestGroup)
      let x := x.tests
      for t in x do
        -- let k := parseHexVector? t.k
        IO.println s!"Loaded test case {t.tcId} with c={t.c} and k={t.k}."
      /-
      let x ← IO.ofExcept (j.getObjVal? "testGroups")
      match x with
      | arr a =>
        let x ← IO.ofExcept (a[1]!.getObjVal? "tests")
        match x with
        | arr a =>
          IO.println s!"Loaded {a[1]!}."
          let x ← IO.ofExcept (a[1]!.getObjVal? "c")
          IO.println s!"Loaded {x}."
          match x with
          | str x =>
            IO.println s!"Loaded {x}."; return
          | _ => return
        | _ => return
      | _ => return
      -/

-- #eval main ()
--def test := mlkem.keygen ParameterSet.MLKEM512 (some (Vector.replicate 32 0)) (some (Vector.replicate 32 0))

-- #eval! test

end Symcrust.Spec

def main : IO Unit := do
  IO.println s!"Testing symcrust's formalization of the ML-KEM standard."
  Symcrust.Spec.test_keyGen
  Symcrust.Spec.test_encaps
  Symcrust.Spec.test_decaps
