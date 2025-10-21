import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Matrix.Reflection
import Aeneas
import Symcrust.Spec.NatBit
import Symcrust.Spec.Round
import Symcrust.Spec.AES
import Symcrust.Spec.Utils
--import Symcrust.Brute
import Sha3.Spec

set_option grind.warning false

-- arguably more convenient than extract for splitting bitstrings
@[inline, expose] def Vector.slice (xs : Vector α n) (start : Nat) (len : Nat) (hlen: start + len ≤ n := by grind): Vector α len :=
  (Vector.extract xs start (start + len)).cast (by simp [hlen])

/-!
FrodoKEM specification, based on
* [ISO] ISO standard proposal: https://frodokem.org/files/FrodoKEM_standard_proposal_20241205.pdf
* [CFRG] CFRG Internet Draft: https://www.ietf.org/archive/id/draft-longa-cfrg-frodokem-00.html
-/

namespace Spec.Frodo

namespace Notations

  -- Overloading the `get_elem_tactic` so that notation `l[i]` works
  scoped macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| scalar_tac)

end Notations

open Notations


/-- # Frodo parameters (Table A.1 in [ISO], Section 9.1 in [CFRG]) -/

inductive parameterSet where
  | FrodoKEM640 : parameterSet
  | FrodoKEM976 : parameterSet
  | FrodoKEM1344 : parameterSet

@[reducible, scalar_tac_simps] def n (p : parameterSet) : ℕ :=
  match p with
  | .FrodoKEM640 => 640
  | .FrodoKEM976 => 976
  | .FrodoKEM1344 => 1344

@[reducible, scalar_tac_simps] def D (p : parameterSet) : ℕ :=
  match p with
  | .FrodoKEM640 => 15
  | .FrodoKEM976 => 16
  | .FrodoKEM1344 => 16

@[reducible, scalar_tac_simps] def B (p : parameterSet) : ℕ :=
  match p with
  | .FrodoKEM640 => 2
  | .FrodoKEM976 => 3
  | .FrodoKEM1344 => 4

@[reducible, scalar_tac_simps] def d (p : parameterSet) : ℕ :=
  match p with
  | .FrodoKEM640 => 12
  | .FrodoKEM976 => 10
  | .FrodoKEM1344 => 6

@[reducible, scalar_tac_simps] def lensec (p : parameterSet) : ℕ :=
  match p with
  | .FrodoKEM640 => 128
  | .FrodoKEM976 => 192
  | .FrodoKEM1344 => 256

@[reducible, scalar_tac_simps] def lenSE (p : parameterSet) : ℕ :=
  match p with
  | .FrodoKEM640 => 256
  | .FrodoKEM976 => 384
  | .FrodoKEM1344 => 512

@[reducible, scalar_tac_simps] def lensalt (p : parameterSet) : ℕ :=
  match p with
  | .FrodoKEM640 => 256
  | .FrodoKEM976 => 384
  | .FrodoKEM1344 => 512

/-- CDT of the error distribution -/
@[reducible] def T_X (p: parameterSet) : List ℕ :=
  match p with
  | .FrodoKEM640 => [4643, 13363, 20579, 25843, 29227, 31145, 32103, 32525, 32689, 32745, 32762, 32766, 32767]
  | .FrodoKEM976 => [5638, 15915, 23689, 28571, 31116, 32217, 32613, 32731, 32760, 32766, 32767]
  | .FrodoKEM1344 => [9142, 23462, 30338, 32361, 32725, 32765, 32767]

/-- Weights of the support values {0, +-1, +-2, ... +-d}, probability is weight/2^16, i.e., can use 16-bit random values to samples with T_X. -/
@[reducible] def P_X (p: parameterSet) : List ℕ :=
  match p with
  | .FrodoKEM640 => [9288, 8720, 7216, 5264, 3384, 1918, 958, 422, 164, 56, 17, 4, 1]
  | .FrodoKEM976 => [11278, 10277, 7774, 4882, 2545, 1101, 396, 118, 29, 6, 1]
  | .FrodoKEM1344 => [18286, 14320, 6876, 2023, 364, 40, 2]

@[reducible, scalar_tac_simps] def Q (p: parameterSet) : ℕ := 2^(D p)
@[reducible] def Zq (p: parameterSet) := ZMod (Q p)
@[reducible, scalar_tac_simps] def nbar : ℕ := 8
@[reducible] def lenA : ℕ := 128


@[scalar_tac_simps]
lemma B_le_D : ∀ p : parameterSet, B p ≤ D p := by
  intro p; cases p <;> scalar_tac

@[scalar_tac_simps]
lemma n_div_by_8 : ∀ p : parameterSet, 8 ∣ n p := by
  intro p; cases p <;> scalar_tac

@[scalar_tac_simps]
lemma lenT_X : ∀ p : parameterSet, List.length (T_X p) = (d p) + 1 := by
  intro p; cases p <;> rfl

-- Both lists have entries for all non-negative values.
@[scalar_tac_simps]
lemma lenT_X_eq_lenP_X : ∀ p : parameterSet, List.length (T_X p) = List.length (P_X p) := by
  intro p; cases p <;> rfl

lemma lenP_X_gt_0 : ∀ p : parameterSet, List.length (P_X p) > 0 := by
  intro p; cases p <;> simp

lemma P_X_zero : ∀ p : parameterSet, 2 * (T_X p)[0] + 2 = (P_X p)[0]'(by apply lenP_X_gt_0) := by
  intro p; cases p <;> rfl

lemma sum_P_X : ∀ p : parameterSet, (P_X p)[0]'(by apply lenP_X_gt_0) + 2*(P_X p).tail.sum = 2^16 := by
  intro p; cases p <;> rfl


-- lemma T_X_equiv_P_X : ∀ p : parameterSet,
--   ∀ i : {i : ℕ // i < List.length (T_X p) - 1},
--     (((T_X p)[i.val+1] - (T_X p)[i.val]) = (P_X p)[i.val+1]'(by rw [← lenT_X_eq_lenP_X]; omega)) := by
--   intro p; cases p <;> (simp [T_X, P_X]; brute)
lemma T_X_equiv_P_X : ∀ p : parameterSet,
  ∀ i : {i : ℕ // i < List.length (T_X p) - 1},
    (((T_X p)[i.val+1] - (T_X p)[i.val]) = (P_X p)[i.val+1]'(by rw [← lenT_X_eq_lenP_X]; omega)) := by
  intro p; cases p <;> (simp [T_X, P_X]; decide +kernel)

-- Matrices modulo q
@[reducible]
def MatrixQ (m n q : ℕ) := Matrix (Fin m) (Fin n) (ZMod q)

-- Integer matrices for sampling from the error distribution
@[reducible]
def MatrixZ (m n : ℕ) := Matrix (Fin m) (Fin n) ℤ
def MatrixZ.toQ {m n : ℕ} (q : ℕ) (M : (MatrixZ m n)) : MatrixQ m n q :=
  Matrix.of (fun i j ↦ M i j)

-- Bits and bit strings
abbrev Bit := Bool
abbrev Bitstring n := Vector Bit n
abbrev Bytestring n := Vector Byte n
abbrev 𝔹 := Bytestring

/- Pseudo-random matrix generation selection -/

inductive GenSelection where | aes | sha | fixed

-- # Algorithms

/-- # Octet encoding of bit strings ([CFRG, 6.1], [ISO, 7.1]) -/
def OctetEncodeOfBits {l : Nat} (b : Bitstring (8 * l)) : Vector Byte l := Id.run do
  let mut Octets := Vector.replicate l (0 : Byte)
  for hi: i in [0:l] do
    let mut byte : Byte := 0
    for hj: j in [0:8] do
      if b[8*i + j] then
        byte := byte ^^^ BitVec.ofNat 8 (2^j)
    Octets := Octets.set i byte
  pure Octets

/-- # Octet decoding to bit strings ([CFRG, 6.1], [ISO, 7.1]) -/
def OctetDecodeToBits {l : Nat} (bytes : Vector Byte l) : Bitstring (l * 8) := Id.run do
  let mut b := Vector.replicate (l * 8) false
  for hi: i in [0:l] do
    let byte := bytes[i]
    for hj: j in [0:8] do
      b := b.set (8*i + j) (byte.testBit j)
  pure b

@[simp] def Bitstring.toBytes {l : Nat} (b : Bitstring (8 * l)) : 𝔹 l :=
  OctetEncodeOfBits b

@[simp] def Bytestring.toBits {l : Nat} (bytes : 𝔹 l) : Bitstring (l * 8) :=
  OctetDecodeToBits bytes

/--
info: [10#8, 1#8]
-/
#guard_msgs in
#eval (@OctetEncodeOfBits 2 ⟨ ⟨ [false, true, false, true, false, false, false, false,
                            true, false, false, false, false, false, false, false] ⟩,
                           by simp ⟩).toList

#assert
  let b : Bitstring (8 * 2) :=
    ⟨ ⟨ [false, true, false, true, false, false, false, false,
         true, false, false, false, false, false, false, false] ⟩, by simp ⟩
  OctetDecodeToBits (OctetEncodeOfBits b) = b

-- # Symmetric components

-- moved here as the current spec uses bytes instead of bits
/- # AES -/
def AES128 (key : Bitstring 128) (message : Bitstring 128) : Bitstring 128 :=
  let block : 𝔹 16 := Spec.AES.aes128 key.toBytes message.toBytes
  block.toBits

/- # SHAKE -/

@[reducible] def SHAKE (p : parameterSet) (M : Bitstring m) d :=
  match p with
  | .FrodoKEM640  => Spec.SHAKE128 M.toArray d
  | .FrodoKEM976  => Spec.SHAKE256 M.toArray d
  | .FrodoKEM1344 => Spec.SHAKE256 M.toArray d

/-- # Encode a B-bit integer to a coefficient ([CFRG, 6.2], [ISO, 7.2]) -/
def ec (D : ℕ) (B : {B : ℕ // B ≤ D }) (val : ZMod (2^B.val)) : ZMod (2^D) := val.val * 2^(D - B)

/-- # Decode a coefficient to a B-bit integer ([CFRG, 6.2], [ISO, 7.2]) -/
def dc (D : ℕ) (B : {B : ℕ // B ≤ D}) (c : ZMod (2^D)) : ZMod (2^B.val) :=
  ⌊ (c.val : ℚ) *  2^B.val / (2^D : ℚ) + 1/2 ⌋

-- an equivalent definition using only integer operations
def dc' (D : ℕ) (B : {B : ℕ // B < D}) (c : ZMod (2^D)) : ZMod (2^B.val) :=
  let v := c + 1 <<< (D - B - 1)
  v.val >>> (D - B)

-- What about 2^D vs Q p ?

example : ∀ p : parameterSet,
  let val : (ZMod (2^(B p))) := 3
  dc (D p) ⟨B p, by cases p <;> scalar_tac⟩ (ec (D p) ⟨ (B p), by scalar_tac ⟩ val) = val := by
  intro p; cases p <;> decide +kernel

#eval ec 15 ⟨ 2, by simp ⟩ (dc 15 ⟨2, by simp⟩ (15000 : ZMod (2^15)))
#eval ec 16 ⟨ 3, by simp ⟩ 3
#eval dc 16 ⟨ 3, by simp⟩ (15000 : ZMod (2^16))

#eval dc' 5 ⟨2, by simp⟩  (27: ZMod (2^5))


-- reformulated on bit vectors for a given parameter set
def encode (p : parameterSet) (s : Bitstring (B p)) : Zq p := Id.run do
  let mut z : ℕ := 0
  for hk: k in [0:B p] do
    z := z + Bool.toNat s[k] * 2^k
  ec (D p) ⟨ B p, by scalar_tac ⟩ z

def decode (p : parameterSet) (z : Zq p) : Bitstring (B p) :=
  let n := dc (D p) ⟨ B p, by scalar_tac ⟩ z
  Vector.ofFn (fun k => Nat.testBit n.val k)

/-- # Matrix Encoding of Bit Strings ([CFRG, 6.2], [ISO, 7.2]) -/
def Encode (p : parameterSet) (b : Bitstring (B p * nbar * nbar)) : MatrixQ nbar nbar (Q p) :=
  Matrix.of (fun i j =>
    let c := b.slice ((i * nbar + j) * B p) (B p) (by cases p <;> scalar_tac)
    encode p c)

/-- # Matrix Decoding to Bit Strings ([CFRG, 6.2], [ISO, 7.2]) -/
def Decode (p : parameterSet) (C : MatrixQ nbar nbar (Q p)) : Bitstring (B p * nbar * nbar) := Id.run do
  let mut b := Vector.replicate (B p * nbar * nbar) false
  for hi: i in [0:nbar] do
    for hj: j in [0:nbar] do
      let c := decode p (C ⟨i, by scalar_tac⟩ ⟨j, by scalar_tac⟩)
      for hk: k in [0:(B p)] do
        have : (i * nbar + j) * B p + k < B p * nbar * nbar := by cases p <;> scalar_tac
        b := b.set ((i * nbar + j) * B p + k) c[k]
  pure b

set_option maxHeartbeats 1000000
example :
  let p := parameterSet.FrodoKEM640
  let bb : Bitstring (B p * 8 * 8) :=
    ⟨ ⟨ [false, true, false, true, false, false, false, false,
          true, false, false, false, false, false, false, false,
          false, true, false, true, false, false, false, false,
          true, false, false, false, false, false, false, false,
          false, true, false, true, false, false, false, false,
          true, false, false, false, false, true, false, false,
          false, true, false, true, false, false, false, false,
          true, false, false, false, false, false, false, false,
          false, true, false, true, false, false, false, false,
          true, false, false, false, false, false, true, false,
          false, true, false, true, false, true, false, false,
          true, false, false, false, false, false, false, false,
          false, true, false, true, false, false, false, false,
          true, false, false, false, false, false, false, true,
          false, true, false, true, true, false, false, false,
          true, false, false, false, true, false, false, false] ⟩, by simp [B, p] ⟩
  Decode p (Encode p bb) = bb := by simp ; native_decide


/-- # Index Bound Lemma for Packing/Unpacking Matrices -/
@[local scalar_tac ((i * n2 + j) * D + k)]
lemma Pack_arith {i j n1 n2 D k : ℕ} (hi: i < n1) (hj: j < n2) (hk: k < D) (hdiv : 8 ∣ n1 * n2) :
  (i * n2 + j) * D + k < 8 * (n1 * n2 * D / 8) := by
  have : i * n2 ≤ (n1 - 1) * n2 := by simp_scalar
  have :=
    calc
      i * n2 + n2  ≤ (n1 - 1) * n2 + n2 := by scalar_tac
      _ = (n1 - 1 + 1) * n2 := by ring_nf
      _ = n1 * n2 := by simp_scalar
  have : (i * n2 + j) * D ≤ (n1 * n2 - 1) * D := by simp_scalar
  have :=
    calc
      (i * n2 + j) * D + D ≤ (n1 * n2 - 1) * D + D := by simp_scalar
      _ = (n1 * n2 - 1 + 1) * D := by ring_nf
      _ = (n1 * n2) * D := by simp_scalar
  have : 8 ∣ n1 * n2 * D := by apply Nat.dvd_mul_right_of_dvd hdiv
  omega

/-- # Packing Matrices Modulo q to Bit Strings ([CFRG, 6.3], [ISO, 7.3]) -/
def Pack {n1 n2: ℕ} (p : parameterSet) (C : MatrixQ n1 n2 (Q p)) (hdiv: 8 ∣ n1 * n2 := by scalar_tac): Vector Byte (n1 * n2 * (D p) / 8) := Id.run do
  let mut b := Vector.replicate (8 * (n1 * n2 * (D p) / 8)) false
  for hi: i in [0:n1] do
    for hj: j in [0:n2] do
      let Cij := (C ⟨i, by scalar_tac⟩ ⟨j, by scalar_tac⟩ )
      for hk: k in [0:(D p)] do
        b := b.set ((i * n2 + j) * (D p) + k) (Nat.testBit Cij.val ((D p) - 1 - k))
  pure (OctetEncodeOfBits b)

/-- # Unpacking Bit Strings to Matrices Modulo q ([CFRG, 6.3], [ISO, 7.3]) -/
def Unpack {n1 n2 : ℕ} (p : parameterSet) (bytes : Vector Byte (n1 * n2 * D p / 8)) (hdiv: 8 ∣ n1 * n2 := by scalar_tac) : MatrixQ n1 n2 (Q p) :=
  let b := OctetDecodeToBits bytes
  Matrix.of (fun i j => Id.run do
    let mut Cij : Zq p := 0
    for hk: k in [0:D p] do
      Cij := Cij + Bool.toNat b[(i * n2 + j) * D p + k] * 2^(D p - 1 - k)
    pure Cij)

/-- # Sampling from the Error Distribution ([CFRG, 6.4], [ISO, 7.4]) -/
def Sample (p : parameterSet) (r : Bitstring 16): ℤ := Id.run do
  let t : ℕ := ∑ (j : Fin 15), ((Bool.toNat r[j+1]) * 2^j.val)
  let mut e : ℤ := 0
  for hi: i in [0:d p] do
    if t > (T_X p)[i] then
      e := e + 1
  pure ((-1)^(Bool.toNat r[0]) * e)

/-
set_option pp.rawOnError true
set_option maxRecDepth 100000
#eval Array.ofFn (fun i =>
  let b : Vector Byte 2 := #v[i % 256, i / 256]
  let r : Bitstring 16 := OctetDecodeToBits b
  Sample parameterSet.FrodoKEM640 r) (n := 2^16)
-/
#eval do
  let mut h := Array.replicate 0 32
  for i in [0:2^6] do
    let b : Vector Byte 2 := #v[i / 256, i % 256]
    let r : Bitstring (8 * 2) := OctetDecodeToBits b
    let s := (Sample parameterSet.FrodoKEM640 r + 16).toNat
    h := h.set! s (h[s]! + 1)
    IO.print s!"{h} "


example :
  let p := parameterSet.FrodoKEM640
 (Sample p ⟨ ⟨ [true, true, false, true, false, false, false, false,
                          true, false, false, false, true, false, true, true] ⟩,
                          by simp ⟩) = -4 := by native_decide


/-- # Matrix Sampling from the Error Distribution ([CFRG, 6.5], [ISO, 7.5]) -/

@[local scalar_tac i * n2 + j]
lemma SampleMatrix_arith {i j n1 n2 : ℕ}  (hi : i < n1) (hj : j < n2) :
  i * n2 + j < n1 * n2 := by
  have : i * n2 ≤ (n1 - 1) * n2 := by simp_scalar
  have :=
    calc
      i * n2 + n2  ≤ (n1 - 1) * n2 + n2 := by scalar_tac
      _ = (n1 - 1 + 1) * n2 := by ring_nf
      _ = n1 * n2 := by simp_scalar
  omega

def slice16 {n} (R: Bitstring (16 * n)) (i : Nat) (hi : i < n := by scalar_tac) : Bitstring 16 :=
  (R.extract (i * 16) ((i + 1) * 16)).cast (by scalar_tac)

def SampleMatrixZ (p : parameterSet) (n1 n2 : ℕ) (R : Bitstring (16 * (n1 * n2))) : MatrixZ n1 n2 :=
  Matrix.of fun i j =>
    Sample p (slice16 R (i * n2 + j))

def SampleMatrixQ (p : parameterSet) (n1 n2 : ℕ) (R : Bitstring (16 * (n1 * n2))) : MatrixQ n1 n2 (Q p)  :=
  Matrix.of fun i j =>
    Sample p (slice16 R (i * n2 + j))

/- # Convert 16-bit non-negative integer to bit string in little Endian format -/
def NatToBits16 (x : Nat) (hx : x < 2^16 := by scalar_tac) : Bitstring 16 := Id.run do
  let mut b := Vector.replicate 16 false
  for hi: i in [0:16] do
    b := b.set i (Nat.testBit x i)
  pure b

#eval NatToBits16 255
#eval Nat.toDigits 2 255
#check NatToBits16 117


/-- # Pseudo-random Generation of Matrix A with AES128 ([CFRG, 6.6.1], [ISO, 7.6.1]) -/

def Gen_AES128 (p : parameterSet) (seedA : Bitstring lenA) : MatrixQ (n p) (n p) (Q p) :=
  -- pre-compute all blocks
  let blocks : Vector (Vector (Bitstring 128) (n p / 8)) (n p) :=
    Vector.ofFn fun i =>
      Vector.ofFn fun j =>
        let b : Bitstring 128 :=
          have : n p < 2^16 := by cases p <;> scalar_tac
          NatToBits16 i ++ NatToBits16 (j * 8) ++ Vector.replicate (6 * 16) false
        --AES128 seedA b
        Vector.replicate 128 true
  -- use each block to fill in 8 values in matrix A
  Matrix.of (fun i j =>
    let y := j.val / 8
    let k := j.val % 8
    have hy : y < n p / 8 := by
      apply Nat.div_lt_div_of_lt_of_dvd _ j.2
      cases p <;> scalar_tac
    let block : Bitstring (16 * 8) := blocks[i][y].cast (by scalar_tac)
    let bits := slice16 block k
    let Cijpk : ℕ := ∑ (l : Fin 16), (bits[l].toNat * 2^l.val)
    Cijpk)

/-- # Pseudo-random Generation of Matrix A with SHAKE128 ([CFRG, 6.6.2], [ISO, 7.6.2]) -/

def Gen_SHAKE128 (p : parameterSet) (seedA : Bitstring lenA) : MatrixQ (n p) (n p) (Q p) :=
  let rows : Vector (Bitstring (16 * n p)) (n p) :=
    Vector.ofFn fun i =>
      have : i.val < 2^16 := by cases p <;> scalar_tac
      let b := NatToBits16 i.val ++ seedA
      Spec.SHAKE128 b.toArray (16 * n p)
  Matrix.of (fun i j =>
    let row := rows[i]
    let Cijpk : ℕ := ∑ (l : Fin 16), Bool.toNat row[ 16 * j.val + l ] * 2^l.val
    Cijpk)

def Gen (p : parameterSet) (gen : GenSelection) (seedA : Bitstring lenA) : MatrixQ (n p) (n p) (Q p) :=
  match gen with
  | .aes => Gen_AES128 p seedA
  | .sha => Gen_SHAKE128 p seedA
  | .fixed => Matrix.of (fun x y => (x.val + 13 * y.val) % (Q p)) -- UNSAFE, for testing purposes only

/- # Random bit generation -/
axiom randomBits (length : ℕ) : Bitstring length

/-- # Matrix Encoding of Signed Integer Matrix S^T as Bit String (needed in key generation) -/
def EncodeSigned (p : parameterSet) (ST : MatrixZ nbar (n p)) : Bitstring (16 * nbar * n p) := Id.run do
  let mut b := Vector.replicate (16 * nbar * n p) false
  for hi: i in [0:nbar] do
    for hj: j in [0:n p] do
      for hk: k in [0:16] do
        b := b.set ((i * n p + j) * 16 + k) (Int.testBit (ST ⟨ i, by scalar_tac ⟩ ⟨ j, by scalar_tac ⟩ ) k)
  pure b

/-- # Matrix Decoding of Bit String to Signed Integer Matrix S^T (needed in decapsulation) -/
--modified to directly produce a MatrixQ
def DecodeSigned (p : parameterSet) (b : Bitstring (16 * (nbar * n p))) : MatrixQ nbar (n p) (Q p) :=
  Matrix.of (fun i j =>
    let val : ℤ :=
      (- Bool.toNat b[(i * (n p) + j) * 16 + 15]) * 2^15 +
      ∑ (k : Fin 15), (Bool.toNat b[(i * (n p) + j) * 16 + k]) * 2^k.val
    val)

/- # Public-key and secret-key spaces -/
abbrev PK (p : parameterSet) :=
  Bitstring lenA ×
  Vector Byte ((n p * nbar * D p) / 8)
abbrev SK (p : parameterSet) :=
  Bitstring (lensec p + lenA + D p * n p * nbar + 16 * nbar * n p + lensec p)
/- # Ciphertext space -/
abbrev CT (p : parameterSet) :=
  Vector Byte ((nbar * n p * D p) / 8 + (nbar * nbar * D p) / 8) ×
  Bitstring (lensalt p)

/-- # Key Generation ([CFRG, 7.1], [ISO, 8.1]) -/

def KeyGen_internal (p : parameterSet) (gen : GenSelection)
  (s : Bitstring (lensec p))
  (seedSE : Bitstring (lenSE p))
  (z : Bitstring lenA) : PK p × SK p :=
  -- Generate A from pseudorandom seed
  let seedA := SHAKE p z lenA
  let A := Gen p gen seedA

  -- Generate pseudorandom bit string
  let (r_st, r_e) :=
    let bits0x5F := OctetDecodeToBits #v[0x5F]
    let r := SHAKE p (bits0x5F ++ seedSE) (32 * n p * nbar)
    ( r.slice 0                 (16 * (nbar * n p)) (by cases p <;> scalar_tac),
      r.slice (16 * nbar * n p) (16 * (n p * nbar)) (by cases p <;> scalar_tac))
  -- Sample matrix S transposed (S^T) and the error matrix E
  let ST := SampleMatrixZ p nbar (n p) r_st
  let E := SampleMatrixQ p (n p) nbar r_e
  -- Compute and pack B
  let S := MatrixZ.toQ (Q p) ST.transpose
  let B := A * S + E
  let b := Pack p B
  let b_bits := (OctetDecodeToBits b).cast (by cases p <;> scalar_tac)
  let pkh := SHAKE p (seedA ++ b_bits) (lensec p)
  let sk := s ++ seedA ++ b_bits ++ EncodeSigned p ST ++ pkh
  ((seedA, b), sk)

noncomputable
def KeyGen (p : parameterSet) (gen : GenSelection) : (PK p) × (SK p) :=
  -- Choose uniformly random seed s of bitlength lensec
  let s := randomBits (lensec p)
  -- Choose uniformly random seed seedSE of bitlength lenSE
  let seedSE := randomBits (lenSE p)
  -- Choose uniformly random seed z of bitlength lenA
  let z := randomBits lenA
  KeyGen_internal p gen s seedSE z

/-- # Encapsulation ([CFRG, 7.2], [ISO, 8.2]) -/

def Encrypt (p : parameterSet) (gen : GenSelection)
  (pkh   : Bitstring (lensec p))
  (u     : Bitstring (B p * nbar * nbar))
  (salt  : Bitstring (lensalt p))
  (seedA : Bitstring lenA)
  (B     : MatrixQ (n p) nbar (Q p))
  :
  /- k  -/ Bitstring (lensec p) ×
  /- B' -/ MatrixQ nbar (n p) (Q p) ×
  /- C  -/ MatrixQ nbar nbar (Q p)
  :=
  let (seedSE, k) :=
    let r := SHAKE p (pkh ++ u ++ salt) (lenSE p + lensec p)
    ( r.slice 0 (lenSE p),
      r.slice (lenSE p) (lensec p))

  let (r0,r1,r2) :=
    let bits0x96 := OctetDecodeToBits #v[0x96]
    let r := SHAKE p (bits0x96 ++ seedSE) (16 * (2 * nbar * n p + nbar * nbar))
    ( r.slice 0                                (16 * (nbar * n p)),
      r.slice (16 * (nbar * n p))              (16 * (nbar * n p)),
      r.slice (16 * (nbar * n p + nbar * n p)) (16 * (nbar * nbar)))

  let S' := SampleMatrixQ p nbar (n p) r0
  let E' := SampleMatrixQ p nbar (n p) r1
  let E'' := SampleMatrixQ p nbar nbar r2

  let A  := Gen p gen seedA
  let B' := S' * A + E'
  let V  := S' * B + E''
  let C := V + Encode p u
  (k, B', C)

def Encaps_internal (p : parameterSet) (gen : GenSelection)
  (pk   : PK p)
  (u    : Bitstring (B p * nbar * nbar))
  (salt : Bitstring (lensalt p)) : CT p × Bitstring (lensec p)
  :=
  let (seedA, b) := pk
  let b_bits := OctetDecodeToBits b
  let BB := Unpack p b
  let pkh := SHAKE p (seedA ++ b_bits) (lensec p)
  let (k, B', C) := Encrypt p gen pkh u salt seedA BB
  let c1 := Pack p B'
  let c2 := Pack p C
  let c1_bits := OctetDecodeToBits c1  -- TODO: Is this the correct input to SHAKE?
  let c2_bits := OctetDecodeToBits c2
  let ss := SHAKE p (c1_bits ++ c2_bits ++ salt ++ k) (lensec p)
  ((c1 ++ c2, salt), ss)

noncomputable
def Encaps (p : parameterSet) (gen : GenSelection) (pk : PK p) : CT p × (Bitstring (lensec p)) :=
  -- Choose uniformly random value u of bitlength lensec
  let u := randomBits (B p * nbar * nbar)
  -- Choose uniformly random value salt of bitlength lensalt
  let salt := randomBits (lensalt p)
  Encaps_internal p gen pk u salt


/-- # Decapsulation ([CFRG, 7.3], [ISO, 8.3]) -/
def Decaps (p : parameterSet) (gen : GenSelection) (ct : CT p) (sk : SK p) : Bitstring (lensec p) :=
  -- Parse secret key
  let s       := sk.slice 0 (lensec p)
  let seedA   := sk.slice (lensec p) lenA
  let b_bits  := sk.slice (lensec p + lenA) (n p * nbar * D p) (by cases p <;> scalar_tac)
  let ST_bits := sk.slice (lensec p + lenA + n p * nbar * D p) (16 * (nbar * n p)) (by cases p <;> scalar_tac)
  let pkh     := sk.slice (lensec p + lenA + n p * nbar * D p + 16 * (nbar * n p)) (lensec p) (by cases p <;> scalar_tac)

  let B :=
    let b := OctetEncodeOfBits (b_bits.cast (by cases p <;> scalar_tac))
    Unpack p b

  -- Parse ciphertext
  let c1 := (ct.1.extract 0 ((nbar * n p * D p) / 8)).cast (by cases p <;> scalar_tac)
  let c2 := (ct.1.extract   ((nbar * n p * D p) / 8) ((nbar * n p * D p) / 8 + (nbar^2 * D p) / 8)).cast (by cases p <;> scalar_tac)
  let salt := ct.2
  let B' := Unpack p c1
  let C := Unpack p c2
  let u' :=
    let ST := DecodeSigned p ST_bits
    let M := C - B' * ST.transpose
    Decode p M
  let (k', B'', C') := Encrypt p gen pkh u' salt seedA B
  let kHat := if B' = B'' ∧ C = C' then k' else s
  let c1_bits := OctetDecodeToBits c1
  let c2_bits := OctetDecodeToBits c2
  let ss := SHAKE p (c1_bits ++ c2_bits ++ salt ++ kHat) (lensec p)
  ss

-- basic testing

end Spec.Frodo

namespace Spec.FrodoTest

open Spec.Utils
open Spec.Frodo

@[simp] def parameterSet.all : List parameterSet :=
  [.FrodoKEM640, .FrodoKEM976, .FrodoKEM1344]

def parameterSet.tag : parameterSet → String
  | .FrodoKEM640 => "FrodoKEM640"
  | .FrodoKEM976 => "FrodoKEM976"
  | .FrodoKEM1344 => "FrodoKEM1344"

@[simp] def GenSelection.all : List GenSelection := [.fixed, .aes, .sha]

def GenSelection.tag : GenSelection → String
  | .aes => "AES"
  | .sha => "SHAKE"
  | .fixed => "FIXED"

def mkBits (seed : Nat := 42): Bitstring ℓ :=
  let input := Vector.ofFn (fun i => seed.testBit i) (n := 64)
  Spec.SHAKE128 input.toArray ℓ

def all := do
  for gen in GenSelection.all do
    for p in parameterSet.all do
      IO.println s!"Testing {parameterSet.tag p}/{GenSelection.tag gen}"
      let s      := mkBits (lensec p)
      let seedSE := mkBits (lenSE p)
      let z      := mkBits lenA
      let u      := mkBits (B p * nbar * nbar)
      let salt   := mkBits (lensalt p)
      let (ek, dk) ← time s!"keygen" (KeyGen_internal p gen s seedSE) z
      let (ct, ss) ← time s!"encaps" (Encaps_internal p gen ek u) salt
      let ss_dec   ← time s!"decaps" (Decaps p gen ct) dk
      IO.println s!"public key ({ek.2.size} bytes): {ek.2}"
      IO.println s!"ciphertext ({ct.1.size} bytes): {ct.1}"
      let v0 : Vector Byte (lensec p / 8) := OctetEncodeOfBits (ss.cast (by cases p <;> ring ))
      let v1 : Vector Byte (lensec p / 8) := OctetEncodeOfBits (ss_dec.cast (by cases p <;> ring ))
      expect ("shared secret") v0 v1

/-
  let p  := parameterSet.FrodoKEM640
  let gen := GenSelection.aes
  let s      := OctetDecodeToBits (v!"04A1064D6106CEAB73E59CFCA29FF642")
  let seedSE := OctetDecodeToBits (v!"B24174F7517C12581245A61E1936F15B11DBBBA5B01324FCA29FF6420DBF520C")
  let z      := OctetDecodeToBits (v!"F7517C12581245A61E1936F15B11DBBB")
  let u : Bitstring (B p * nbar * nbar) := OctetDecodeToBits (Vector.ofFn (fun i => i % 256))
  let salt : Bitstring (lensalt p) := OctetDecodeToBits (v!"45A61E1936F15B11DBBBA5B0B24174F7517C1258121324FCA29FF6420DBF520C")
  let (ek, dk) ← time "keygen" (KeyGen_internal p gen s seedSE) z
  IO.println s!"Public Key: ({ek.2.size} bytes) {ek.2}"


  let (ct, ss) ← time "encaps" (Encaps_internal p gen ek u) salt
  IO.println s!"Ciphertext: ({ct.1.size} bytes) {ct.1}"

  let ss_dec : Bitstring (8 * 16) ← time "decaps" (Decaps p gen ct) dk
  expect "Shared secret matches" (OctetEncodeOfBits ss) (OctetEncodeOfBits ss_dec)
-/

-- #eval test_frodo ()

end Spec.FrodoTest
