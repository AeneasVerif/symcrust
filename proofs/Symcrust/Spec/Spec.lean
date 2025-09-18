import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.RowCol
import Aeneas
import Symcrust.Spec.NatBit
import Symcrust.Spec.Round
import Sha3.Spec

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
  theorem div_range_in_bounds {len start : ℕ} (h0 : 1 < len ∧ len ≤ 128 ∧ ∃ k, len = 128 / 2 ^ k)
    (h1 : start < 256 ∧ start % (2 * len) = 0) : start + 2 * len ≤ 256 := by
    sorry

  @[scalar_tac]
  theorem mul_range_add_in_bounds {len start : ℕ}
    (h0 : 2 ≤ len ∧ len < 256 ∧ ∃ k, len = 2 * 2 ^ k)
    (h1 : start < 256 ∧ start % (2 * len) = 0) : start + 2 * len ≤ 256 :=
    sorry

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


end Symcrust.Spec
