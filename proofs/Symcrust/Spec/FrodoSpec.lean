import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Vector.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.RowCol
import Aeneas
import Symcrust.Spec.NatBit
import Symcrust.Spec.Round
import Symcrust.Spec.AES
import Sha3.Spec

set_option grind.warning false

-- Function that returns a vector slice.
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


/- Conditions on parameters from Section 5 [ISO] and consistency checks -/

lemma D_pos : ∀ p : parameterSet, D p > 0 := by
  intro p; cases p <;> trivial

lemma D_leq_16 : ∀ p : parameterSet, D p ≤ 16 := by
  intro p; cases p <;> trivial

lemma n_pos : ∀ p : parameterSet, n p > 0 := by
  intro p; cases p <;> trivial

@[scalar_tac_simps]
lemma n_div_by_8 : ∀ p : parameterSet, 8 ∣ n p := by
  intro p; cases p <;> trivial

lemma nbar_pos : nbar > 0 := by
  scalar_tac

lemma nbar_div_by_8 : 8 ∣ nbar := by
  scalar_tac

lemma B_pos : ∀ p : parameterSet, B p > 0 := by
  intro p; cases p <;> trivial

@[scalar_tac_simps]
lemma B_le_D : ∀ p : parameterSet, B p ≤ D p := by
  intro p; cases p <;> trivial

lemma lenA_pos : lenA > 0 := by
  trivial

lemma lensec_pow : ∀ p : parameterSet, lensec p > 0 := by
  intro p; cases p <;> trivial

lemma lensec_B_nbar_nbar : ∀ p : parameterSet, lensec p = B p * nbar * nbar := by
  intro p; cases p <;> rfl

lemma lenSE_pos : ∀ p : parameterSet, lenSE p > 0 := by
  intro p; cases p <;> trivial

lemma lenSE_eq_2_lensec : ∀ p : parameterSet, lenSE p = 2 * lensec p := by
  intro p; cases p <;> rfl

lemma lensalt_pos : ∀ p : parameterSet, lensalt p > 0 := by
  intro p; cases p <;> trivial

lemma lensalt_eq_2_lensec : ∀ p : parameterSet, lensalt p = 2 * lensec p := by
  intro p; cases p <;> rfl

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

lemma T_X_equiv_P_X : ∀ p : parameterSet,
  ∀ i : {i : ℕ // i < List.length (T_X p) - 1},
    (((T_X p)[i.val+1] - (T_X p)[i.val]) = (P_X p)[i.val+1]'(by rw [← lenT_X_eq_lenP_X]; omega)) := by
  intro p; cases p <;> (simp [T_X, P_X]; decide +kernel)


-- Matrices modulo q
@[reducible] def MatrixQ (m n q : ℕ) := Matrix (Fin m) (Fin n) (ZMod q)
def MatrixQ.zero (m n q : ℕ) : MatrixQ m n q := Matrix.of (fun _ _ ↦ (0 : (ZMod q)))
def MatrixQ.update {m n q : ℕ} (M : MatrixQ m n q) (i : Fin m) (j : Fin n) (val : (ZMod q)) : MatrixQ m n q :=
  Matrix.updateRow M i (fun k => if k = j then val else (M i k))

-- Integer matrices for sampling from the error distribution
@[reducible] def MatrixZ (m n : ℕ) := Matrix (Fin m) (Fin n) ℤ
def MatrixZ.zero (m n : ℕ) : MatrixZ m n := Matrix.of (fun _ _ ↦ (0 : ℤ))
def MatrixZ.update {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) (j : Fin n) (val : ℤ) : Matrix (Fin m) (Fin n) ℤ :=
  Matrix.updateRow M i (fun k => if k = j then val else (M i k))
def MatrixZ.toQ {m n : ℕ} (q : ℕ) (M : (MatrixZ m n)) : MatrixQ m n q := Matrix.of (fun i j ↦ ((M i j) : (ZMod q)))

-- Bits and bit strings
abbrev Bit := Bool
abbrev Bitstring n := Vector Bit n

-- Byte strings
abbrev Bytestring n := Vector Byte n
abbrev 𝔹 := Bytestring


/- Pseudo-random matrix generation selection -/

inductive GenSelection where | aes | sha


-- # Algorithms

/-- # Octet encoding of bit strings ([CFRG, 6.1], [ISO, 7.1]) -/
def OctetEncodeOfBits {l : Nat} (b : Bitstring (8 * l)) : 𝔹 l := Id.run do
  let mut Octets := Vector.replicate l (0 : Byte)
  for hi: i in [0:l] do
    let mut byte : Byte := 0
    for hj: j in [0:8] do
      if b[8*i + j] then
        byte := byte ^^^ BitVec.ofNat 8 (2^j)
    Octets := Octets.set i byte
  pure Octets

/-- # Octet decoding to bit strings ([CFRG, 6.1], [ISO, 7.1]) -/
def OctetDecodeToBits {l : Nat} (bytes : 𝔹 l) : Bitstring (8 * l) := Id.run do
  let mut b := Vector.replicate (8 * l) false
  for hi: i in [0:l] do
    let byte := bytes[i]
    for hj: j in [0:8] do
      b := b.set (8*i + j) (byte.testBit j)
  pure b

@[simp] def Bitstring.bytes {l : Nat} (b : Bitstring (8 * l)) : 𝔹 l := OctetEncodeOfBits b
@[simp] def 𝔹.bits {l : Nat} (bytes : 𝔹 l) : Bitstring (8 * l) := OctetDecodeToBits bytes


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

/- # AES -/
def AES128 (key : Bitstring 128) (message : Bitstring 128) : Bitstring 128 :=
  let block : 𝔹 16 := Spec.AES.aes128 key.bytes message.bytes
  block.bits


/- # SHAKE -/

-- @[reducible] def SHAKE (p : parameterSet) :=
--   match p with
--   | .FrodoKEM640 => Spec.SHAKE128
--   | .FrodoKEM976 => Spec.SHAKE256
--   | .FrodoKEM1344 => Spec.SHAKE256

@[reducible] def SHAKE (p : parameterSet) (M : Bitstring m) d :=
  match p with
  | .FrodoKEM640  => Spec.SHAKE128 M.toArray d
  | .FrodoKEM976  => Spec.SHAKE256 M.toArray d
  | .FrodoKEM1344 => Spec.SHAKE256 M.toArray d


/-- # Encode a B-bit integer to a coefficient ([CFRG, 6.2], [ISO, 7.2]) -/
def ec (D : ℕ) (B : {B : Nat // B ≤ D }) (val : ZMod (2^B.val)) : ZMod (2^D) := val.val * 2^(D-B.val)

/-- # Decode a coefficient to a B-bit integer ([CFRG, 6.2], [ISO, 7.2]) -/
def dc (D : ℕ) (B : {B : Nat // B ≤ D}) (c : ZMod (2^D)) : ZMod (2^B.val) := ⌊ c.val * (( 2^B.val : ℚ ) / ( (2^D) : ℚ )) + 1/2 ⌋

example : ∀ p : parameterSet,
  let val : (ZMod (2^(B p))) := 3
  dc (D p) ⟨ (B p), by scalar_tac⟩ (ec (D p) ⟨ (B p), by scalar_tac ⟩ val) = val := by
  intro p; cases p <;> decide +kernel

#eval ec 15 ⟨ 2, by simp ⟩ (dc 15 ⟨2, by simp⟩ (15000 : ZMod (2^15)))
#eval ec 16 ⟨ 3, by simp ⟩ 3
#eval dc 16 ⟨ 3, by simp⟩ (15000 : ZMod (2^16))


/-- # Matrix Encoding of Bit Strings ([CFRG, 6.2], [ISO, 7.2]) -/
def Encode (p : parameterSet) (b : Bitstring ((B p) * nbar^2)) : MatrixQ nbar nbar (Q p) := Id.run do
  let mut C := MatrixQ.zero nbar nbar (Q p)
  for hi: i in [0:nbar] do
    for hj: j in [0:nbar] do
      let mut val : (ZMod (2^(B p))) := 0
      for hk: k in [0:(B p)] do
        have : (i * nbar + j) * (B p) + k < (B p) * nbar ^ 2 := by cases p <;> simp_scalar
        val := val + ((Bool.toNat b[(i * nbar + j) * (B p) + k]) * 2^k)
      C := MatrixQ.update C ⟨ i, by scalar_tac ⟩ ⟨ j, by scalar_tac ⟩ (ec (D p) ⟨ B p, by apply B_le_D⟩ val)
  pure C

/-- # Matrix Decoding to Bit Strings ([CFRG, 6.2], [ISO, 7.2]) -/
def Decode (p : parameterSet) (C : MatrixQ nbar nbar (Q p)) : Bitstring ((B p) * nbar^2) := Id.run do
  let mut b := Vector.replicate ((B p) * nbar^2) false
  for hi: i in [0:nbar] do
    for hj: j in [0:nbar] do
      let c := dc (D p) ⟨ B p, by apply B_le_D⟩ (C ⟨ i, by scalar_tac ⟩ ⟨ j, by scalar_tac ⟩ )
      for hk: k in [0:(B p)] do
        have : (i * nbar + j) * (B p) + k < (B p) * nbar^2 := by cases p <;> scalar_tac
        b := b.set ((i * nbar + j) * (B p) + k) (Nat.testBit c.val k)
  pure b

example :
  let p := parameterSet.FrodoKEM640
  let bb : Bitstring ((B p) * 8^2) :=
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
def Unpack {n1 n2 : ℕ} (p : parameterSet) (bytes : Vector Byte (n1 * n2 * (D p) / 8)) (hdiv: 8 ∣ n1 * n2 := by scalar_tac) : MatrixQ n1 n2 (Q p) := Id.run do
  let b := OctetDecodeToBits bytes
  let mut C := MatrixQ.zero n1 n2 (Q p)
  for hi: i in [0:n1] do
    for hj: j in [0:n2] do
      let mut Cij : (Zq p) := 0
      for hk: k in [0:(D p)] do
        Cij := Cij + ((Bool.toNat b[(i * n2 + j) * (D p) + k]) * 2^((D p) - 1 - k))
      C := MatrixQ.update C ⟨i, by scalar_tac⟩ ⟨j, by scalar_tac⟩ Cij
  pure C

/-- # Sampling from the Error Distribution ([CFRG, 6.4], [ISO, 7.4]) -/
def Sample (p : parameterSet) (r : Bitstring 16): ℤ := Id.run do
  let t : ℕ := ∑ (j : Fin 15), ((Bool.toNat r[j+1]) * 2^j.val)
  let mut e : ℤ := 0
  for hi: i in [0:(d p)] do
    if t > (T_X p)[i] then
      e := e + 1
  pure ((-1)^(Bool.toNat r[0]) * e)


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

def SampleMatrix (p : parameterSet) (n1 n2 : ℕ) (R : Vector (Bitstring 16) (n1 * n2)) : MatrixZ n1 n2 := Id.run do
  let mut E := MatrixZ.zero n1 n2
  for hi: i in [0:n1] do
    for hj: j in [0:n2] do
      E := MatrixZ.update E ⟨i, by scalar_tac⟩ ⟨j, by scalar_tac⟩ (Sample p R[i * n2 + j])
  pure E

/- # Convert 16-bit non-negative integer to bit string in little Endian format -/
def NatToBits16 (x : {x : ℕ // x < 2^16}) : Bitstring 16 := Id.run do
  let mut b := Vector.replicate 16 false
  for hi: i in [0:16] do
    b := b.set i (Nat.testBit x i)
  pure b

#eval NatToBits16 ⟨ 255, by linarith ⟩
#eval Nat.toDigits 2 255
#check NatToBits16 ⟨ 117, by linarith ⟩


/-- # Pseudo-random Generation of Matrix A with AES128 ([CFRG, 6.6.1], [ISO, 7.6.1]) -/
noncomputable
def Gen_AES128 (p : parameterSet) (seedA : Bitstring lenA) : MatrixQ (n p) (n p) (Q p) := Id.run do
  let mut A := MatrixQ.zero (n p) (n p) (Q p)
  for hi: i in [0:(n p)] do
    for hj: j in [0:(n p):8] do
      let b : Bitstring 128 :=
        NatToBits16 ⟨ i, by cases p <;> scalar_tac ⟩ ++ NatToBits16 ⟨ j, by cases p <;> scalar_tac ⟩ ++ Vector.replicate (6 * 16) false
      let block := AES128 seedA b
      for hk: k in [0:8] do
        let Cijpk : ℕ := ∑ (l : Fin 16), ((Bool.toNat block[ 16*k + l ]) * 2^l.val)
        A := MatrixQ.update A ⟨ i, by scalar_tac ⟩ ⟨ j + k, by cases p <;> scalar_tac ⟩ Cijpk
  pure A


/-- # Pseudo-random Generation of Matrix A with SHAKE128 ([CFRG, 6.6.2], [ISO, 7.6.2]) -/
def Gen_SHAKE128 (p : parameterSet) (seedA : Bitstring lenA) : MatrixQ (n p) (n p) (Q p) := Id.run do
  let mut A := MatrixQ.zero (n p) (n p) (Q p)
  for hi: i in [0:(n p)] do
    let b := (NatToBits16 ⟨ i, by cases p <;> scalar_tac ⟩) ++ seedA
    let row := Spec.SHAKE128 b.toArray (16*(n p))
    for hj: j in [0:(n p)] do
      let Cijpk : ℕ := ∑ (l : Fin 16), ((Bool.toNat row[ 16*j + l ]) * 2^l.val)
      A := MatrixQ.update A ⟨ i, by scalar_tac ⟩ ⟨ j, by scalar_tac ⟩ Cijpk
  pure A

noncomputable
def Gen (p : parameterSet) (gen : GenSelection) (seedA : Bitstring lenA) : MatrixQ (n p) (n p) (Q p) :=
  match gen with
  | .aes => Gen_AES128 p seedA
  | .sha => Gen_SHAKE128 p seedA


/- # Random bit generation -/
axiom randomBits (length : ℕ) : Bitstring length

/-- # Matrix Encoding of Signed Integer Matrix S^T as Bit String (needed in key generation) -/
def EncodeSigned (p : parameterSet) (ST : MatrixZ nbar (n p)) : Bitstring (16 * nbar * (n p)) := Id.run do
  let mut b := Vector.replicate (16 * nbar * (n p)) false
  for hi: i in [0:nbar] do
    for hj: j in [0:(n p)] do
      for hk: k in [0:16] do
        b := b.set ((i * (n p) + j) * 16 + k) (Int.testBit (ST ⟨ i, by scalar_tac ⟩ ⟨ j, by scalar_tac ⟩ ) k)
  pure b

/-- # Matrix Decoding of Bit String to Signed Integer Matrix S^T (needed in decapsulation) -/
def DecodeSigned (p : parameterSet) (b : Bitstring (16 * nbar * (n p))) : MatrixZ nbar (n p) := Id.run do
  let mut ST := MatrixZ.zero nbar (n p)
  for hi: i in [0:nbar] do
    for hj: j in [0:(n p)] do
      let val : ℤ :=
        (- Bool.toNat b[(i * (n p) + j) * 16 + 15]) * 2^15 +
        ∑ (k : Fin 15), (Bool.toNat b[(i * (n p) + j) * 16 + k]) * 2^k.val
      ST := MatrixZ.update ST ⟨ i, by scalar_tac ⟩ ⟨ j, by scalar_tac ⟩ val
  pure ST

/- # Public-key and secret-key spaces -/
abbrev PK (p : parameterSet) :=
  Bitstring (lenA) ×
  𝔹 ((n p) * nbar * (D p) / 8)
abbrev SK (p : parameterSet) :=
  Bitstring ((lensec p) + lenA + (D p) * (n p) * nbar + 16 * nbar * (n p) + (lensec p))
/- # Ciphertext space -/
abbrev CT (p : parameterSet) :=
  𝔹 (((n p) * nbar * (D p) / 8) + (nbar^2 * (D p) / 8)) ×
  Bitstring (lensalt p)


-- Take out the i-th 16 bit string from a bit string of 16*n bits.
def slice16 {n} (R: Bitstring (16 * n)) (i : Nat) (hi : i < n := by scalar_tac) : Bitstring 16 :=
  (R.extract (i * 16) ((i + 1) * 16)).cast (by scalar_tac)


/-- # Key Generation ([CFRG, 7.1], [ISO, 8.1]) -/
noncomputable
def KeyGen (p : parameterSet) (gen : GenSelection) : (PK p) × (SK p) :=
  -- Choose uniformly random seed s of bitlength lensec
  let s := randomBits (lensec p)
  -- Choose uniformly random seed seedSE of bitlength lenSE
  let seedSE := randomBits (lenSE p)
  -- Choose uniformly random seed z of bitlength lenA
  let z := randomBits lenA
  -- # Generate pseudorandom seed:
  let seedA := SHAKE p z lenA
  -- # Generate the matrix A:
  let A := Gen p gen seedA
  -- # Generate pseudorandom bit string:
  let bits0x5F := OctetDecodeToBits #v[0x5F]
  let r := SHAKE p ((bits0x5F) ++ seedSE) ( 16 * (2 * (n p) * nbar))
  -- # Sample matrix S transposed (S^T):
  let r_ST : Vector (Bitstring 16) (nbar * (n p)) :=
    Vector.ofFn fun i => slice16 r i
  let ST := SampleMatrix p nbar (n p) r_ST
  -- # Sample error matrix E
  let r_E : Vector (Bitstring 16) ((n p) * nbar) :=
    Vector.ofFn fun i => slice16 r ((n p) * nbar + i)
  let E := MatrixZ.toQ (Q p) (SampleMatrix p (n p) nbar r_E)
  -- Compute and pack B
  let S := MatrixZ.toQ (Q p) (ST.transpose)
  let B := A * S + E
  let b := Pack p B
  -- Compute pkh
  let b_bits := OctetDecodeToBits b -- TODO: check that this is correct as an input to SHAKE.
  have : lenA + 8 * (n p * nbar * D p / 8) = lenA + n p * nbar * D p := by cases p <;> scalar_tac
  let pkh := SHAKE p (seedA ++ b_bits) (lensec p)
  let pk := (seedA, b)
  let sk := (s ++ seedA ++ b_bits ++ EncodeSigned p ST ++ pkh).cast (by cases p <;> scalar_tac) -- TODO: bit strings vs byte arrays?
  (pk, sk)


/-- # Encapsulation ([CFRG, 7.2], [ISO, 8.2]) -/
noncomputable
def Encaps (p : parameterSet) (gen : GenSelection) (pk : PK p) : CT p × (Bitstring (lensec p)) :=
  -- Get public key components
  let seedA := pk.1
  let b := pk.2
  let b_bits := OctetDecodeToBits b
  -- Choose uniformly random value u of bitlength lensec
  let u := randomBits (lensec p)
  -- Choose uniformly random value salt of bitlength lensalt
  let salt := randomBits (lensalt p)
  -- Compute pkh
  let pkh := SHAKE p (seedA ++ b_bits) (lensec p)
  -- # Generate pseudorandom values:
  let prbits := SHAKE p (pkh ++ u ++ salt) (lenSE p + lensec p)
  let seedSE : Bitstring (lenSE p) := prbits.slice 0 (lenSE p)
  let k : Bitstring (lensec p) := prbits.slice (lenSE p) (lensec p)
  -- # Generate pseudorandom bit strings:
  let bits0x96 := OctetDecodeToBits #v[0x96]
  let r := SHAKE p (bits0x96 ++ seedSE) (16 * (2 * nbar * (n p) + nbar^2))
  -- # Sample matrices S' and E':
  let R_S' : Vector (Bitstring 16) (nbar * (n p)) :=
    Vector.ofFn fun i => slice16 r i
  let S' := MatrixZ.toQ (Q p) (SampleMatrix p nbar (n p) R_S')
  let R_E' : Vector (Bitstring 16) (nbar * (n p)) :=
    Vector.ofFn fun i => slice16 r ((n p) * nbar + i)
  let E' := MatrixZ.toQ (Q p) (SampleMatrix p nbar (n p) R_E')
  -- # Generate the matrix A:
  let A := Gen p gen seedA
  let B' := S' * A + E'
  let c1 := Pack p B'
  -- # Sample error matrix E'':
  let R_E'' : Vector (Bitstring 16) (nbar * nbar) :=
    Vector.ofFn fun i => slice16 r (2 * (n p) * nbar + i)
  let E'' := MatrixZ.toQ (Q p) (SampleMatrix p nbar nbar R_E'')
  let BB := Unpack p b
  let V := S' * BB + E''
  have : lensec p = (B p) * nbar ^ 2 := by cases p <;> scalar_tac
  let C := V + Encode p (u.cast (by scalar_tac))
  let c2 := Pack p C
  let c1_bits := OctetDecodeToBits c1  -- TODO: Is this the correct input to SHAKE?
  let c2_bits := OctetDecodeToBits c2
  let ss := SHAKE p (c1_bits ++ c2_bits ++ salt ++ k) (lensec p)
  ((((c1 ++ c2).cast (by cases p <;> scalar_tac)), salt), ss)


/-- # Decapsulation ([CFRG, 7.3], [ISO, 8.3]) -/
noncomputable
def Decaps (p : parameterSet) (gen : GenSelection) (ct : CT p) (sk : SK p) : Bitstring (lensec p) :=
  -- Parse ciphertext
  let c1 : Vector Byte (nbar * (n p) * (D p) / 8) :=
    (ct.1.extract 0 (nbar * (n p) * (D p) / 8)).cast (by cases p <;> scalar_tac)
  let c2 : Vector Byte (nbar^2 * (D p) / 8) :=
    (ct.1.extract (nbar * (n p) * (D p) / 8) ((nbar * (n p) * (D p) / 8) + (nbar^2 * (D p) / 8))).cast (by cases p <;> scalar_tac)
  let salt := ct.2
  -- Parse secret key
  let s : Bitstring (lensec p) :=
    sk.slice 0 (lensec p)
  let seedA : Bitstring lenA :=
    sk.slice (lensec p) lenA
  let b_bits : Bitstring ((n p) * nbar * (D p)) :=
    (sk.extract (lensec p + lenA) (lensec p + lenA + (n p) * nbar * (D p))).cast (by cases p <;> scalar_tac)
  let ST_bits : Bitstring (16 * (n p) * nbar) :=
    (sk.extract (lensec p + lenA + (n p) * nbar * (D p)) (lensec p + lenA + (n p) * nbar * (D p) + 16 * (n p) * nbar)).cast
    (by cases p <;> scalar_tac)
  let pkh : Bitstring (lensec p) :=
    (sk.extract (lensec p + lenA + (n p) * nbar * (D p) + 16 * (n p) * nbar) (2*(lensec p) + lenA + (n p) * nbar * (D p) + 16 * (n p) * nbar)).cast
    (by cases p <;> scalar_tac)
  --
  let B' := Unpack p c1
  let C := Unpack p c2
  let S := MatrixZ.toQ (Q p) (Matrix.transpose (DecodeSigned p (ST_bits.cast (by scalar_tac))))
  let M := C - B' * S
  let u' := Decode p M
  have : lensec p = (B p) * nbar ^ 2 := by cases p <;> scalar_tac
  -- # Generate pseudorandom values:
  let prbits := SHAKE p (pkh ++ u' ++ salt) (lenSE p + lensec p)
  let seedSE' : Bitstring (lenSE p) := prbits.slice 0 (lenSE p)
  let k' : Bitstring (lensec p) := prbits.slice (lenSE p) (lensec p)
  -- # Generate pseudorandom bit strings:
  let bits0x96 := OctetDecodeToBits #v[0x96]
  let r := SHAKE p (bits0x96 ++ seedSE') (16 * (2 * nbar * (n p) + nbar^2))
  -- # Sample matrices S' and E':
  let R_S' : Vector (Bitstring 16) (nbar * (n p)) :=
    Vector.ofFn fun i => slice16 r i
  let S' := MatrixZ.toQ (Q p) (SampleMatrix p nbar (n p) R_S')
  let R_E' : Vector (Bitstring 16) (nbar * (n p)) :=
    Vector.ofFn fun i => slice16 r ((n p) * nbar + i)
  let E' := MatrixZ.toQ (Q p) (SampleMatrix p nbar (n p) R_E')
  -- # Generate the matrix A:
  let A := Gen p gen seedA
  let B'' := S' * A + E'
  -- # Sample error matrix E'':
  let R_E'' : Vector (Bitstring 16) (nbar * nbar) :=
    Vector.ofFn fun i => slice16 r (2 * (n p) * nbar + i)
  let E'' := MatrixZ.toQ (Q p) (SampleMatrix p nbar nbar R_E'')
  let b := OctetEncodeOfBits (b_bits.cast (by cases p <;> scalar_tac))
  let B := Unpack p b
  let V := S' * B + E''
  let C' := V + Encode p u'
  let kHat := if B' = B'' ∧ C = C' then k' else s
  let c1_bits := OctetDecodeToBits c1
  let c2_bits := OctetDecodeToBits c2
  let ss := SHAKE p (c1_bits ++ c2_bits ++ salt ++ kHat) (lensec p)
  ss
