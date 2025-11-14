import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Tactic.IntervalCases
import Aeneas
import Symcrust.Spec.NatBit
import Symcrust.Spec.Round
import Symcrust.Spec.Utils
import Symcrust.Spec.Sha3XOF

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

set_option grind.warning false

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

abbrev 𝔹 := Vector Byte

/-! # Algorithm 3 -/
def bitsToBytes {ℓ : Nat} (b : Vector Bool (8 * ℓ)) : 𝔹 ℓ := Id.run do
  let mut B := Vector.replicate ℓ 0
  for h: i in [0:8*ℓ] do
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
def bytesToBits {ℓ : Nat} (B : 𝔹 ℓ) : Vector Bool (8 * ℓ) := Id.run do
  let mut C := B
  let mut b := Vector.replicate (8 * ℓ) false
  for hi: i in [0:ℓ] do
    for hj: j in [0:8] do
      b := b.set (8 * i + j) (C[i] % 2 ≠ 0)
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
-- TODO: use Lists rather than Arrays in Sha3? (why??)
def sha3_256 {n} (M : 𝔹 n) : 𝔹 32 :=
  let M_bits := bytesToBits M
  bitsToBytes (Spec.SHA3_256 M_bits.toArray)

def sha3_512 {n} (M : 𝔹 n) : 𝔹 64 :=
  let M_bits := bytesToBits M
  bitsToBytes (Spec.SHA3_512 M_bits.toArray)

def shake256 {n} (M : 𝔹 n) (ℓ : ℕ) : 𝔹 ℓ :=
  let bits := (bytesToBits M).toArray
  bitsToBytes (Spec.SHAKE256 bits (8 * ℓ))

/-! # Pseudorandom function (PRF) -/

abbrev Η := {η : ℕ // η ∈ ({2, 3} : Set ℕ)}

def PRF (η : Η) (s : 𝔹 32) (b : Byte) : 𝔹 (64 * η) :=
  shake256 (s ++ Vector.singleton b) (64 * η)

/-! # Hash functions -/

def H {n} (s : 𝔹 n) := sha3_256 s
def J {n} (s : 𝔹 n) := shake256 s 32
def G {n} (s : 𝔹 n) : 𝔹 32 × 𝔹 32 :=
  let hash := sha3_512 s
  let a := hash.extract 0 32
  let b := hash.extract 32 64
  (a, b)


/-! # eXtendable-Output Function (XOF) -/

def XOF.init := Spec.SHAKE128.init

def XOF.absorb s (B : 𝔹 ℓ) :=
  Spec.SHAKE128.absorb s (bytesToBits B).toArray

def XOF.squeeze s ℓ  :=
  let (s, Z) := Spec.SHAKE128.squeeze s (8 * ℓ)
  (s, bitsToBytes Z)

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
def byteEncode (d : ℕ) (F : Polynomial (m d)) : 𝔹 (32 * d) := Id.run do
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
def byteDecode {d : ℕ} (B : 𝔹 (32 * d)) : Polynomial (m d) := Id.run do
  let b ← bytesToBits B
  let mut F := Polynomial.zero (m d)
  for hi: i in [0:256] do
    have : i * d ≤ 255 * d := by scalar_tac +nonLin
    F := F.set i (∑ (j : Fin d), b[i * d + j].toNat * 2^j.val)
  pure F

/-! # Algorithm 7 -/
def sampleNTT (B : 𝔹 34) := Id.run do
  let mut ctx := XOF.absorb XOF.init B
  let mut a := Polynomial.zero
  let mut j := 0
  while hj : j < 256 do
    let (ctx', C) := XOF.squeeze ctx 3 -- 24 bits
    ctx := ctx'
    let d₁ := C[0].val + 256 * (C[1].val % 16)
    let d₂ := C[1].val / 16 + 16 * C[2].val
    if d₁ < Q then
      a := a.set j d₁
      j := j + 1
    if h: d₂ < Q ∧ j < 256 then
      a := a.set j d₂
      j := j + 1
  pure a

/-! # Algorithm 8 -/

@[scalar_tac η.val]
theorem H.val (η : Η) : η.val ≤ 3 := by
  have := η.property
  scalar_tac

def samplePolyCBD {η:Η} (B : 𝔹 (64 * η)) : Polynomial := Id.run do
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
def ntt (f : Polynomial) := Id.run do
  let mut f := f
  let mut i := 1
  for h0: len in [128 : >1 : /= 2] do
    for h1: start in [0 : 256 : 2*len] do
      let zeta := ζ ^ (bitRev 7 i)
      i := i + 1
      for h: j in [start : start+len] do
        let t := zeta * f[j + len]
        f := f.set (j + len) (f[j] - t)
        f := f.set j         (f[j] + t)
  pure f

/-! # Algorithm 10 -/
def invNtt (f : Polynomial) : Polynomial := Id.run do
  let mut f := f
  let mut i := 127
  for h0: len in [2 : <256 : *= 2] do
    for h1: start in [0:256:2*len] do
      let zeta := ζ ^ bitRev 7 i
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

@[reducible, grind, scalar_tac_simps] def k (p : ParameterSet) : K :=
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

def PolyVector.byteEncode {k : K} (d : ℕ) (v : PolyVector (m d) k) : 𝔹 (k * (32 * d)) := Id.run do
  (Vector.flatten (v.map (Spec.byteEncode d))).cast (by grind)

def PolyVector.byteDecode {k : K} (d : ℕ) (bytes : 𝔹 (32 * d * k)) : PolyVector (m d) k :=
  PolyVector.ofFn fun i =>
    have : 32 * d * (i + 1) ≤ 32 * d * k := by simp_scalar
    Spec.byteDecode ((bytes.extract (32 * d * i) (32 * d * (i + 1))).cast (by simp_scalar; grind))

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

def kpke.keyGen (p : ParameterSet)
  (d : 𝔹 32) :
  𝔹 (384 * k p + 32) × 𝔹 (384 * k p) := Id.run do

  let (ρ, σ) := G (d ++ Vector.singleton (k p : Byte))
  let mut N : ℕ := 0
  let mut A_hat := PolyMatrix.zero Q (k p)
  for hi: i in [0:k p] do
    for hj: j in [0:k p] do
      A_hat := PolyMatrix.update A_hat i j
        (sampleNTT (ρ ++ Vector.singleton (j : Byte) ++ Vector.singleton (i : Byte)))
  let mut s := PolyVector.zero Q (k p)
  for hi: i in [0:k p] do
    s := s.set i (samplePolyCBD (PRF (η₁ p) σ N))
    N := N + 1
  let mut e := PolyVector.zero Q (k p)
  for hi: i in [0:k p] do
    e := e.set i (samplePolyCBD (PRF (η₁ p) σ N))
    N := N + 1
  let s_hat := PolyVector.NTT s
  let e_hat := PolyVector.NTT e
  let t_hat := A_hat * s_hat + e_hat
  let ek_PKE := (PolyVector.byteEncode 12 t_hat ++ ρ).cast (by grind)
  let dk_PKE := (PolyVector.byteEncode 12 s_hat).cast (by grind)
  pure (ek_PKE, dk_PKE)

/-! # Algorithm 14 -/

def kpke.encrypt (p : ParameterSet)
  (ek_PKE : 𝔹 (384 * k p + 32))
  (m : 𝔹 32)
  (r : 𝔹 32) :
  𝔹 (32 * (dᵤ p * k p + dᵥ p)) := Id.run do

  let mut N : ℕ := 0
  let t_hat := PolyVector.byteDecode 12 ((ek_PKE.extract 0 (384 * k p)).cast (by grind))
  let ρ : 𝔹 32 := (ek_PKE.extract (384 * k p) (384 * k p + 32)).cast (by cases p <;> scalar_tac)
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
  let c₁ := PolyVector.byteEncode (dᵤ p) (PolyVector.compressVec ⟨dᵤ p, by cases p <;> scalar_tac⟩ u)
  let c₂ := byteEncode (dᵥ p) (Polynomial.compress ⟨dᵥ p, by cases p <;> scalar_tac⟩ v)
  (c₁ ++ c₂).cast (by cases p <;> scalar_tac)

/-! # Algorithm 15 -/

def kpke.decrypt (p : ParameterSet)
  (dk_PKE : 𝔹 (384 * k p))
  (c : 𝔹 (32 * (dᵤ p * k p + dᵥ p))) :
  𝔹 32 :=

  let c₁ : 𝔹 (32 * dᵤ p * k p) := (c.extract 0 (32 * dᵤ p * k p)).cast (by grind)
  let c₂ : 𝔹 (32 * dᵥ p) := (c.extract (32 * dᵤ p * k p) (32 * (dᵤ p * k p + dᵥ p))).cast (by grind)
  let u' := PolyVector.decompress ⟨dᵤ p, by grind⟩ (PolyVector.byteDecode (dᵤ p) c₁)
  let v' := Polynomial.decompress ⟨dᵥ p, by grind⟩ (byteDecode c₂)
  let s_hat := PolyVector.byteDecode 12 dk_PKE
  let w := v' - invNtt (PolyVector.innerProductNTT s_hat (PolyVector.NTT u'))
  let m := byteEncode 1 (Polynomial.compress ⟨1, by grind⟩ w)
  m

/-! # Algorithm 16 -/

def mlkem.keyGen_internal (p : ParameterSet)
  (d z : 𝔹 32) :
  𝔹 (384 * k p + 32) × 𝔹 (768 * k p + 96) :=

  let (ek_PKE, dk_PKE) := @kpke.keyGen p d
  let ek := ek_PKE.cast (by scalar_tac)
  let dk := (dk_PKE ++ ek ++ H ek ++ z).cast (by scalar_tac)
  (ek, dk)

/-! # Algorithm 17 -/

def mlkem.encaps_internal (p : ParameterSet)
  (ek : 𝔹 (384 * k p + 32))
  (m : 𝔹 32) :
  𝔹 32 × 𝔹 (32 * (dᵤ p * k p + dᵥ p)) :=

  let (K, r) := G (m ++ H ek)
  let c := kpke.encrypt p ek m r
  (K, c)

/-! # Algorithm 18 -/

def mlkem.decaps_internal (p : ParameterSet)
  (dk : 𝔹 (768 * k p + 96))
  (c : 𝔹 (32 * (dᵤ p * k p + dᵥ p))) :
  𝔹 32 :=

  let dk_PKE : 𝔹 (384 * k p) := (dk.extract 0 (384 * k p)).cast (by scalar_tac)
  let ek_PKE : 𝔹 (384 * k p + 32) := (dk.extract (384 * k p) (768 * k p + 32)).cast (by scalar_tac)
  let h : 𝔹 32 := (dk.extract (768 * k p + 32) (768 * k p + 64)).cast (by scalar_tac)
  let z : 𝔹 32 := (dk.extract (768 * k p + 64) (768 * k p + 96)).cast (by scalar_tac)
  let m' := kpke.decrypt p dk_PKE c
  let (K', r') := G (m' ++ h)
  let K_bar := J (z ++ c)
  let c' := kpke.encrypt p ek_PKE m' r'
  let K' := if c ≠ c' then K_bar else K'
  K'

/-! # Algorithm 19 -/

/-! # Random byte generation -/
axiom randomBytes (length : ℕ) : Option (𝔹 length)

/-
Not sure how to model randomness, so we simply take the random bytes as inputs.
-/
def mlkem.keygen (p : ParameterSet)
  (d z : Option (𝔹 32)) :
  Option (𝔹 (384 * k p + 32) × 𝔹 (768 * k p + 96)) := do
  let d ← d
  let z ← z
  let (ek, dk) := mlkem.keyGen_internal p d z
  return (ek, dk)


/-! # Algorithm 20 -/

/-
Not sure how to model randomness, so we simply take the random bytes as inputs.
-/
def mlkem.encaps (p : ParameterSet)
  (ek : 𝔹 (384 * k p + 32))
  (m : Option (𝔹 32)) :
  Option (𝔹 32 × 𝔹 (32 * (dᵤ p * k p + dᵥ p))) := do
  let m ← m
  let (K, c) := mlkem.encaps_internal p ek m
  return (K, c)

/-! # Algorithm 21 -/

def mlkem.decaps (p : ParameterSet)
  (dk : 𝔹 (768 * k p + 96))
  (c : 𝔹 (32 * (dᵤ p * k p + dᵥ p))) :
  𝔹 32 :=

  let K' := mlkem.decaps_internal p dk c
  K'

end Symcrust.Spec
