import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Matrix.Reflection
import Aeneas
import Symcrust.Spec.NatBit
import Symcrust.Spec.Round

/-!
FrodoKEM specification, based on
* [ISO] ISO standard proposal: https://frodokem.org/files/FrodoKEM_standard_proposal_20241205.pdf
* [CFRG] CFRG Internet Draft: https://www.ietf.org/archive/id/draft-longa-cfrg-frodokem-00.html
-/

namespace Symcrust.Spec

open Aeneas.Notations.SRRange  -- allows the `[0:256:2*len]` notations to desugar to an `SRRange` instead of a `Std.Range`
open Aeneas.Notations.DivRange -- activates the `[start : >stop : /divisor]` notation
open Aeneas.Notations.MulRange -- activates the `[start : <stop : *mul]` notation
open Aeneas.Notations.Range    -- activates the `aeneas_range_tactic`, so that we can overload it below

namespace Notations

  open Parser Lean.Parser Lean.Parser.Term
  open Lean Elab Term Meta Tactic

  /- TODO: improve `scalar_tac` so that we don't need to do this.
     It seems that sometimes `simp at *` and `simp_all` don't work in the presence of
     dependent types.
   -/
  def simpAsms : TacticM Unit :=
    withMainContext do
    let lctx ← getLCtx
    let decls ← lctx.getDecls
    let props ← decls.filterM (fun d => do pure (← inferType d.type).isProp)
    let props := (props.map fun d => d.fvarId).toArray
    Aeneas.Utils.simpAt false {} { declsToUnfold := #[``Membership.mem] } (.targets props false)

  elab "simp_asms" : tactic => simpAsms

  -- Overload the tactic to discharge the range proof obligations
  scoped macro_rules
  | `(tactic| aeneas_range_tactic) => `(tactic| (try simp_asms); saturate; scalar_tac)

  -- Overloading the `get_elem_tactic` so that notation `l[i]` works
  scoped macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| aeneas_range_tactic)

end Notations

open Notations

/-- # Frodo640 parameters (Table A.1 in [ISO], Section 9.1 in [CFRG]) -/
@[reducible] def D : ℕ := 15
@[reducible] def Q : ℕ := 2^D -- Q = 32768
@[reducible] def Zq := ZMod Q
@[reducible] def MatrixQ (m n : ℕ) := Matrix (Fin m) (Fin n) Zq
def MatrixQ.zero (m n : ℕ) : MatrixQ m n := Matrix.of (fun _ _ ↦ (0 : Zq))
def MatrixQ.update (M : MatrixQ m n) (i : Fin m) (j : Fin n) (val : Zq) : MatrixQ m n :=
  Matrix.updateRow M i (fun k => if k = j then val else ((M i k) : Zq))

@[reducible] def n : ℕ := 640
@[reducible] def nbar : ℕ := 8

inductive n1n2Case where
  | B : n1n2Case
  | B' : n1n2Case
  | C : n1n2Case
  | ST : n1n2Case

def n1n2Set (case : n1n2Case): ℕ × ℕ :=
  match case with
  | .B => (n, nbar)
  | .B' => (nbar, n)
  | .C => (nbar, nbar)
  | .ST => (nbar , n)

def n1 : ℕ := (n1n2Set n1n2Case.B).1
def n2 : ℕ := (n1n2Set n1n2Case.B).2
#eval n1
#eval n2

@[reducible] def B : ℕ := 2
@[reducible] def d : ℕ := 12

/-- CDT of the error distribution -/
@[reducible] def T_X : List ℕ := [4643, 13363, 20579, 25843, 29227, 31145, 32103, 32525, 32689, 32745, 32762, 32766, 32767]
/-- Weights of the support values {0, +-1, +-2, ... +-d}, probability is weight/2^16, i.e., can use 16-bit random values to samples with T_X. -/
def P_X : List ℕ := [9288, 8720, 7216, 5264, 3384, 1918, 958, 422, 164, 56, 17, 4, 1]

#assert
  List.length T_X = d + 1 -- Support of the distribution is {-d, -d+1, ..., 0, 1, ..., d}, tables correspond to non-neg values.
#assert
  List.length T_X = List.length P_X -- Both lists have entries for all non-negative values.
#assert
  2 * T_X[0] + 2 = P_X[0]
#assert
  P_X[0] + 2*P_X.tail.sum = 2^16
#assert
  ∀ i : ℕ , i < d → ((T_X[i+1]! - T_X[i]!) = P_X[i+1]!)

@[reducible] def lenA : ℕ := 128
@[reducible] def lensec : ℕ := 128
@[reducible] def lenSE : ℕ := 256
@[reducible] def lensalt : ℕ := 256

attribute [scalar_tac_simps] n nbar D B d n1 n2 n1n2Set


-- # Algorithms

/-- # Octet encoding of bit strings ([CFRG, 6.1], [ISO, 7.1]) -/
def OctetEncodeOfBits {l : Nat} (b : Vector Bool (8 * l)) : Vector Byte l := Id.run do
  let mut Octets := Vector.replicate l 0
  for hi: i in [0:l] do
    let mut byte : Byte := 0
    for hj: j in [0:8] do
      if b[8*i + j]! then
        byte := byte ^^^ BitVec.ofNat 8 (2^j)
    Octets := Octets.set i byte
  pure Octets

/-- # Octet decoding to bit strings ([CFRG, 6.1], [ISO, 7.1]) -/
def OctetDecodeToBits {l : Nat} (bytes : Vector Byte l) : Vector Bool (8 * l) := Id.run do
  let mut b := Vector.replicate (8 * l) false
  for hi: i in [0:l] do
    let byte := bytes[i]
    for hj: j in [0:8] do
      b := b.set (8*i + j) (byte.testBit j)
  pure b

/--
info: [10#8, 1#8]
-/
#guard_msgs in
#eval (@OctetEncodeOfBits 2 ⟨ ⟨ [false, true, false, true, false, false, false, false,
                            true, false, false, false, false, false, false, false] ⟩,
                           by simp ⟩).toList

#assert
  let b : Vector Bool (8 * 2) :=
    ⟨ ⟨ [false, true, false, true, false, false, false, false,
         true, false, false, false, false, false, false, false] ⟩, by simp ⟩
  OctetDecodeToBits (OctetEncodeOfBits b) = b

/-- # Encode a B-bit integer to a coefficient ([CFRG, 6.2], [ISO, 7.2]) -/
def ec (B : {B : Nat // B < D}) (val : ZMod (2^B.val)) : Zq := (val.val * (2^(D-B)))

/-- # Decode a coefficient to a B-bit integer ([CFRG, 6.2], [ISO, 7.2]) -/
def dc (B : {B : Nat // B < D}) (c : Zq) : ZMod (2^B.val) := ⌊ c.val * (( 2^B.val : ℚ ) / ( Q : ℚ )) ⌋

#assert
  let val : (ZMod (2^B)) := 3
 dc ⟨ B, by linarith ⟩ (ec ⟨B, by linarith⟩ val) = val

#eval ec ⟨ B, by linarith ⟩ (dc ⟨B, by linarith⟩ (15000 : Zq))
#eval ec ⟨ B, by linarith ⟩ 3
#eval dc ⟨B, by linarith⟩ (15000 : Zq)

/-- # Matrix Encoding of Bit Strings ([CFRG, 6.2], [ISO, 7.2]) -/
def Encode (b : Vector Bool (B * nbar^2)) : MatrixQ nbar nbar := Id.run do
  let mut C := MatrixQ.zero nbar nbar
  for hi: i in [0:nbar] do
    for hj: j in [0:nbar] do
      let mut val : (ZMod (2^B)) := 0
      for hk: k in [0:B] do
        val := val + ((Bool.toNat b[(i * nbar + j) * B + k]) * 2^k)
      C := MatrixQ.update C i j (ec ⟨ B, by linarith ⟩ val)
  pure C

/-- # Matrix Decoding to Bit Strings ([CFRG, 6.2], [ISO, 7.2]) -/
def Decode (C : MatrixQ nbar nbar) : Vector Bool (B * nbar^2) := Id.run do
  let mut b := Vector.replicate (B * nbar^2) false
  for hi: i in [0:nbar] do
    for hj: j in [0:nbar] do
      let c := dc ⟨B, by linarith⟩ (C i j)
      for hk: k in [0:B] do
        b := b.set ((i * nbar + j) * B + k) (Nat.testBit c.val k)
  pure b

#assert
  let bb : Vector Bool (2 * 8^2) :=
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
          true, false, false, false, true, false, false, false] ⟩, by simp ⟩
  Decode (Encode bb) = bb



/-- # Packing Matrices Modulo q to Bit Strings ([CFRG, 6.3], [ISO, 7.3]) -/
def Pack (C : MatrixQ n1 n2) : Vector Byte (D * n1 * n2 / 8) := Id.run do
  let mut b := Vector.replicate (8 * (D * n1 * n2 / 8)) false
  for hi: i in [0:n1] do
    for hj: j in [0:n2] do
      let Cij := (C ⟨i, by scalar_tac⟩ ⟨j, by scalar_tac⟩ )
      for hk: k in [0:D] do
        b := b.set ((i * n2 + j) * D + k) (Nat.testBit Cij.val (D - 1 - k))
  pure (OctetEncodeOfBits b)

/-- # Unpacking Bit Strings to Matrices Modulo q ([CFRG, 6.3], [ISO, 7.3]) -/
def Unpack (bytes : Vector Byte (D * n1 * n2 / 8)) : MatrixQ n1 n2 := Id.run do
  let b := OctetDecodeToBits bytes
  let mut C := MatrixQ.zero n1 n2
  for hi: i in [0:n1] do
    for hj: j in [0:n2] do
      let mut val : Zq := 0
      for hk: k in [0:D] do
        val := val + ((Bool.toNat b[(i * n2 + j) * D + k]) * 2^k)
      C := MatrixQ.update C ⟨i, by scalar_tac⟩ ⟨j, by scalar_tac⟩ val
  pure C



/-- # Sampling from the Error Distribution ([CFRG, 6.4], [ISO, 7.4]) -/
def Sample (r : Vector Bool 16) : ℤ := Id.run do
  let mut t : ℕ := 0
  for hj: j in [1:16] do
    t := t + ((Bool.toNat r[j]) * 2^(j-1))
  let mut e : ℤ := 0
  for hi: i in [0:d] do
    if t > T_X[i] then
      e := e + 1
  pure ((-1)^(Bool.toNat r[0]) * e)

/--
info: -4
-/
#guard_msgs in
#eval (Sample ⟨ ⟨ [true, true, false, true, false, false, false, false,
                          true, false, false, false, true, false, true, true] ⟩,
                          by simp ⟩)

/-- # Matrix Sampling from the Error Distribution ([CFRG, 6.5], [ISO, 7.5]) -/
def SampleMatrix (n1 n2 : ℕ) (R : List (Vector Bool 16)) (h : R.length = n1 * n2) : MatrixQ n1 n2 := Id.run do
  let mut E := MatrixQ.zero n1 n2
  for hi: i in [0:n1] do
    for hj: j in [0:n2] do
      have : i * n2 + j < n1 * n2 := by sorry
      E := MatrixQ.update E ⟨i, by scalar_tac⟩ ⟨j, by scalar_tac⟩ ((Sample R[i * n2 + j]): Zq)
  pure (E : MatrixQ n1 n2)

/- # AES -/
axiom AES128 (key : Vector Bool 128) (message : Vector Bool 128) : Vector Bool 128

/- # SHAKE -/
axiom SHAKE128 (in_length : ℕ) (input : Vector Bool in_length) (out_length : ℕ) : Vector Bool out_length
noncomputable def SHAKE := SHAKE128

/- Encode 16-bit integer into bit string in little Endian format -/
def NatToBits16 (x : {x : ℕ // x < 2^16}) : Vector Bool 16 := Id.run do
  let mut b := Vector.replicate 16 false
  for hi: i in [0:16] do
    b := b.set i (Nat.testBit x i)
  pure b

#eval NatToBits16 ⟨ 255, by linarith ⟩
#eval Nat.toDigits 2 255
#check NatToBits16 ⟨ 117, by linarith ⟩

/-- # Pseudo-random Generation of Matrix A with AES128 ([CFRG, 6.6.1], [ISO, 7.6.1]) -/
noncomputable
def Gen_AES128 (seedA : Vector Bool lenA) : MatrixQ n n := Id.run do
  let mut A := MatrixQ.zero n n
  for hi: i in [0:n] do
    for hj: j in [0:n:8] do
      let b := ((NatToBits16 ⟨ i, by scalar_tac ⟩).append (NatToBits16 ⟨ j, by scalar_tac ⟩)).append
                  (Vector.replicate (6 * 16) false)
      let block := AES128 seedA b
      for hk: k in [0:8] do
        let mut Cijpk : ℕ := 0
        for hl: l in [0:16] do
          Cijpk := Cijpk + (Bool.toNat block[ 16*k + l ]) * 2^l
        A := MatrixQ.update A i (j+k) Cijpk
  pure A

/-- # Pseudo-random Generation of Matrix A with SHAKE128 ([CFRG, 6.6.2], [ISO, 7.6.2]) -/
noncomputable
def Gen_SHAKE128 (seedA : Vector Bool lenA) : MatrixQ n n := Id.run do
  let mut A := MatrixQ.zero n n
  for hi: i in [0:n] do
    let b := (NatToBits16 ⟨ i, by scalar_tac ⟩).append seedA
    let row := SHAKE128 (lenA + 16) b (16*n)
    for hj: j in [0:n] do
      let mut Cijpk : ℕ := 0
      for hl: l in [0:16] do
        Cijpk := Cijpk + (Bool.toNat row[ 16*j + l ]) * 2^l
      A := MatrixQ.update A i j Cijpk
  pure A

noncomputable
def Gen := Gen_AES128

/- # Random bit generation -/
axiom randomBits (length : ℕ) : Vector Bool length

set_option diagnostics true

/-- # Key Generation ([CFRG, 7.1], [ISO, 8.1]) -/
noncomputable
def KeyGen : PK × SK := Id.run do
  let s := randomBits lensec
  let seedSE := randomBits lenSE
  let z := randomBits lenA
  -- Generate pseudorandom seed:
  let seedA := SHAKE lenA z lenA
  -- Generate the matrix A:
  let A := Gen seedA
  -- Generate pseudorandom bit string
  let bits0x5F := OctetDecodeToBits (Vector.replicate 1 0x5F)
  let r := SHAKE (8 + lenSE) ((bits0x5F).append seedSE) (32 * n * nbar)
  -- Sample transposed matrix S^T:
  let mut R_ST := []
  let ri := r
  for hi: i in [0:(n*nbar)] do
    let Ri := Vector.take ri 16
    R_ST := R_ST.append [Ri]
    let ri := Vector.drop ri 16
  have : R_ST.length = nbar * n := by sorry
  let ST := SampleMatrix nbar n R_ST (by apply this)
  -- Sample error matrix E
  let mut R_E := []
  for hi: i in [0:(n*nbar)] do
    let Ri := Vector.take ri 16
    R_E := R_E.append [Ri]
    let ri := Vector.drop ri 16
  have : R_E.length = n * nbar := by sorry
  let E := SampleMatrix n nbar R_E (by apply this)
  -- Compute B
  let S : (MatrixQ n nbar) := Matrix.transpose ST
  let test : Matrix (Fin n) (Fin nbar) Zq := Matrix.mulᵣ A S
  let test2 := test + test
  let test3 := E + E
  let B := A * S + E
  sorry

#check 0x5F

/-- # Encapsulation ([CFRG, 7.2], [ISO, 8.2]) -/
def Encaps (pk : PK) : CT := sorry

/-- # Decapsulation ([CFRG, 7.3], [ISO, 8.3]) -/
def Decaps (ct : CT) (sk : SK) : SS := sorry
