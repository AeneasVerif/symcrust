import Symcrust.Spec
import Symcrust.Properties.Polynomials

/-!
An auxiliary specification that we use to prove a refinement result.
This specification refines the specification in `Spec`, and is refined by the code.
It does not need to be trusted.

**Characterizing the functions of the spec:**
We start with "boring" theorems which allow us to characterize the functions of the specification
such as `bitsToByte`, `byteToBits`, `byteEncode` and `byteDecode`. For specification functions are
indeed written in a very algorithmic manner, while we actually need lemmas which allows us to do
proofs by extensionality (i.e., we want to characterize the value at index i for the buffer resulting
from calling, e.g., `bitsToBytes`). This is what those auxiliary theorems do.

**Proving the streaming version of the spec:**
The Rust code actually composes `compress` and `byteEncode` in a single
streaming implementation (and it does a similar thing with `byteDecode` and `decompress`).
This is the interesting part of the proof, which involves proving a tricky invariant: see for instance
`Stream.encode.spec`.

**Compress and decompress:**
The implementation of `compress` and `decompress` is also tricky as it has to be constant time, so
there is a bit of arithmetic reasoning there.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

/-!
# bitsToBytes
-/

def Target.bitsToBytes.body
  {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) (i : ℕ) :
  Vector Byte l :=
  B.set! (i/8) (B[i/8]!  + BitVec.ofNat 8 (Bool.toNat b[i]!) * BitVec.ofNat 8 (2 ^(i%8)))

def Target.bitsToBytes.recBody
  {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) (i : ℕ) :
  Vector Byte l :=
  List.foldl (body b) B (List.range' i (8 * l - i))

def Target.bitsToBytes {l : Nat} (b : Vector Bool (8 * l)) : Vector Byte l :=
  bitsToBytes.recBody b (Vector.replicate l 0) 0

theorem Target.bitsToBytes.eq_spec {l : Nat} (b : Vector Bool (8 * l)) :
  bitsToBytes b = Spec.bitsToBytes b := by
  unfold bitsToBytes Spec.bitsToBytes recBody body
  simp only [BitVec.ofNat_eq_ofNat, tsub_zero, Id.run, Id.pure_eq,
    Vector.Inhabited_getElem_eq_getElem!, Vector.set_eq_set!, Id.bind_eq, forIn'_eq_forIn,
    forIn_eq_forIn_range', size, add_tsub_cancel_right, Nat.div_one, List.forIn_yield_eq_foldl]

theorem Target.bitsToBytes.recBody.step_eq
  {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) (i : ℕ)
  (hi : i < 8 * l) :
  recBody b B i = recBody b (body b B i) (i + 1) := by
  unfold recBody
  have : 8 * l - i = (8 * l - (i+1)) + 1 := by omega
  simp only [this, List.range'_succ, List.foldl_cons]

irreducible_def Target.bitsToBytes.inv
  {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) (i j : ℕ) :=
  -- The prefix is properly set
  (∀ i' < i, ∀ j' < 8, B[i']!.testBit j' = b[8*i' + j']!) ∧
  -- We are updating the value at index i
  (∀ j' < j, B[i]!.testBit j' = b[8*i + j']!) ∧
  (i < l → ∀ j' ∈ [j:8], B[i]!.testBit j' = false) ∧
  -- The suffix is made of zeros
  (∀ i' ∈ [i+1:l], B[i']! = 0)

@[local simp, local simp_scalar_simps]
theorem decompose_ij (i j : ℕ) (hj : j < 8) :
  (8 * i + j) / 8 = i ∧ (8 * i + j) % 8 = j := by
  omega

@[local scalar_tac m d]
theorem m_d_pos (d : ℕ) : 0 < m d := by
  simp only [m]
  split <;> simp only [Nat.ofNat_pos, pow_pos]

def Target.bitsToBytes.body.spec
  {l:Nat} {b : Vector Bool (8 * l)} {B : Vector Byte l} {i j : ℕ} (hinv : inv b B i j)
  (hi : i < l) (hj : j < 8) :
  inv b (body b B (8 * i + j)) i (j + 1) := by
  simp only [body, inv] at *
  simp only [mem_std_range_step_one, and_imp, BitVec.ofNat_eq_ofNat, Nat.mul_add_mod_self_left] at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  split_conjs
  . intro i' hi' j' hj'
    simp_lists [h0]
  . -- This is the complex part of the proof, where we have
    -- to reason about bitwise manipulations
    intros j' hj'
    simp_scalar; simp_lists
    cases hb: b[8 * i + j]! <;> simp [hb]
    . by_cases hj'': j' = j
      . simp_all only [forall_const, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, le_refl]
      . have : j' < j := by omega
        simp_lists [h1]
    . simp [Byte.testBit]
      have : 256 = 2^8 := by rfl
      rw [this]; clear this
      simp only [Nat.testBit_mod_two_pow]
      simp_scalar
      by_cases hj'': j' = j <;> simp_scalar <;> simp_lists [*] -- TODO: simp_lists +split
  . intros hi' j' hj' hj''
    simp_lists
    simp only [hj, decompose_ij]
    cases hb: b[8 * i + j]! <;> simp
    . by_cases hj''': j' = j -- TODO: simp_lists +split
      . simp_lists
      . simp_lists [h2]
    . simp_scalar
      simp only [Byte.testBit, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.add_mod_mod]
      have : 256 = 2^8 := by rfl
      rw [this]; clear this
      simp_scalar
      have : BitVec.toNat B[i]! + 2 ^ j = 2 ^ j + BitVec.toNat B[i]! := by ring_nf
      rw [this]
      /- This proof is also subtle.
         We use the fact that: `B[i] < 2^j`
         which itself derives from the fact that: `∀ j' < j, B[i].testBit j' = 0`
      -/
      have : B[i]!.toNat < 2^j := by
        have hj : (BitVec.toNat B[i]!).testBit j = false := by
          simp_lists [h2]
        have := @Nat.lt_of_testBit (BitVec.toNat B[i]!) (2^j) j hj (by simp)
        apply this
        intro k hk
        simp_scalar
        by_cases hk' : k < 8
        . simp_lists [h2]
        . simp only [not_lt] at hk'
          have : BitVec.toNat B[i]! < 2^8 := by omega
          have : BitVec.toNat B[i]! < 2 ^ k := by simp_scalar
          simp_scalar
      have : ((2^j + B[i]!.toNat) >>> j).testBit (j' - j) = (2^j + B[i]!.toNat).testBit j' := by
        simp_scalar
      rw [← this]
      simp [Nat.shiftRight_eq_div_pow]
      simp_scalar
  . intros i' hi' hi''
    simp_lists [h3]

theorem Target.bitsToBytes.inv_8_imp_inv {l:Nat}
  {b : Vector Bool (8 * l)} {B : Vector Byte l} {i : ℕ}
  (hinv : inv b B i 8) :
  inv b B (i + 1) 0 := by
  simp only [inv] at *
  simp only [mem_std_range_step_one, isEmpty_Prop, not_and, not_lt, imp_self, IsEmpty.forall_iff,
    implies_true, BitVec.ofNat_eq_ofNat, and_imp, true_and, not_lt_zero', zero_le] at *
  obtain ⟨ h0, h1, h2 ⟩ := hinv
  split_conjs
  . intro i' hi' j' hj'
    by_cases hi'': i' = i
    . simp only [hi'']
      simp_lists [h1]
    . simp_lists [h0]
  . intros hi' j' hj'
    have : B[i+1]! = 0#8 := by
      simp_lists [h2]
    simp only [Byte.testBit, this, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
      Nat.zero_testBit]
  . simp_lists [*]

-- TODO: this one is useless
theorem Target.bitsToBytes.inv_0_imp {l:Nat}
  {b : Vector Bool (8 * l)} {B : Vector Byte l} {i : ℕ}
  (hinv : inv b B (i + 1) 0) :
  inv b B i 8 := by
  simp only [inv] at *
  simp only [not_lt_zero', IsEmpty.forall_iff, implies_true, mem_std_range_step_one, zero_le,
    true_and, BitVec.ofNat_eq_ofNat, and_imp, isEmpty_Prop, not_and, not_lt, imp_self] at *
  obtain ⟨ h0, h1, h2 ⟩ := hinv
  split_conjs
  . simp_lists [*]
  . simp_lists [*]
  . intros i' hi' hi''
    by_cases hi''': i' = i + 1
    . simp only [← hi'''] at h1
      have : ∀ j < 8, B[i']!.testBit j = false := by
        simp_lists [h1]
      natify; simp only [Nat.reducePow, Nat.zero_mod]
      apply Nat.eq_of_testBit_eq; simp only [Nat.zero_testBit]
      intros j
      by_cases hj: j < 8
      . simp_lists [h1]
      . simp only [not_lt] at hj
        have : B[i']!.toNat < 2^j := by simp_scalar -- TODO: also make it work with scalar_tac +nonLin
        simp_scalar
    . simp_lists [h2]

theorem Target.bitsToBytes.inv_last_imp {l:Nat}
  {b : Vector Bool (8 * l)} {B : Vector Byte l} (i j : ℕ)
  (hi : l ≤ i)
  (hinv : inv b B i j) :
  inv b B l 0 := by
  simp only [inv, mem_std_range_step_one, and_imp, BitVec.ofNat_eq_ofNat, not_lt_zero', le_refl,
    Vector.getElem!_default, Byte.testBit_default, le_add_iff_nonneg_right, zero_le,
    Bool.default_bool, implies_true, lt_self_iff_false, true_and] at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  split_conjs <;> simp_lists [*]

def Target.bitsToBytes.recBody.spec
  {l:Nat} {b : Vector Bool (8 * l)} {B : Vector Byte l} {i j : ℕ}
  (hinv : inv b B i j) (hi : i ≤ l) (hj : j ≤ 8) :
  inv b (recBody b B (8 * i + j)) l 0 := by
  if hi': i = l then
    -- We're done
    apply Target.bitsToBytes.inv_last_imp i j
    . omega
    . unfold recBody
      simp_scalar
      apply hinv
  else
    -- Increment j if possible
    if hj': j = 8 then
      simp only [hj'] at hinv ⊢
      have hinv1 := Target.bitsToBytes.inv_8_imp_inv hinv
      have hinv2 := spec hinv1 (by omega) (by omega)
      simp +arith at hinv2 ⊢
      apply hinv2
    else
      rw [Target.bitsToBytes.recBody.step_eq]; swap; omega
      generalize hacc1 : body b B (8 * i + j) = acc1 at *
      have hinv1 := Target.bitsToBytes.body.spec hinv (by omega) (by omega)
      rw [hacc1] at hinv1
      have hinv2 := spec hinv1 (by omega) (by omega)
      simp only at *
      apply hinv2
termination_by (l - i, 8 - j)
decreasing_by all_goals (simp_wf; omega)

irreducible_def Target.bitsToBytes.post {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) :=
  ∀ i < l, ∀ j < 8, B[i]!.testBit j = b[8*i + j]!

def Target.bitsToBytes.spec {l:Nat} (b : Vector Bool (8 * l)) :
  post b (bitsToBytes b) := by
  have hinv0 : inv b (Vector.replicate l 0) 0 0 := by
    simp only [BitVec.ofNat_eq_ofNat, inv, not_lt_zero', Byte.testBit, IsEmpty.forall_iff,
      implies_true, mul_zero, zero_add, mem_std_range_step_one, zero_le, true_and, and_imp]
    split_conjs <;> simp_lists
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.zero_testBit, implies_true]
  have hinv1 := recBody.spec hinv0 (by omega) (by omega)
  simp only [BitVec.ofNat_eq_ofNat, mul_zero, add_zero] at hinv1
  simp only [inv, not_lt_zero', le_refl, Vector.getElem!_default, Byte.testBit_default,
    le_add_iff_nonneg_right, zero_le, Bool.default_bool, implies_true, lt_self_iff_false,
    mem_std_range_step_one, true_and, BitVec.ofNat_eq_ofNat, and_imp] at hinv1
  obtain ⟨ h0, h1 ⟩ := hinv1
  unfold bitsToBytes
  simp only [BitVec.ofNat_eq_ofNat, post]
  -- TODO: introduce notation for this, plus apply symmetry to the equation
  glet hacc1 : acc1 := recBody b (Vector.replicate l 0#8) 0
  intro i hi j hj
  simp_lists [h0]

/-!
# bytesToBits
-/

def Target.byteToBits.body {l : Nat}
  (i : ℕ)
  (res : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (j : ℕ) : MProd (Vector Byte l) (Vector Bool (8 * l)) :=
  let C := res.fst
  let b := res.snd
  let b := b.set! (8*i + j) ((C[i]!) % 2 ≠ 0)
  let C := C.set! i (C[i]! / 2)
  ⟨ C, b ⟩

def Target.byteToBits.recBody {l : Nat}
  (i : ℕ)
  (res : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (j : ℕ) : MProd (Vector Byte l) (Vector Bool (8 * l)) :=
  List.foldl (Target.byteToBits.body i) res (List.range' j (8 - j))

def Target.byteToBits {l : Nat}
  (res : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (i : ℕ) :
  MProd (Vector Byte l) (Vector Bool (8 * l))
  :=
  List.foldl (Target.byteToBits.body i) res (List.range' 0 8)

def Target.bytesToBits.recBody
  {l : Nat} (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (i : ℕ) :
  MProd (Vector Byte l) (Vector Bool (8 * l)) :=
  List.foldl byteToBits acc (List.range' i (l - i))

def Target.bytesToBits {l : Nat} (B : Vector Byte l) : Vector Bool (8 * l) :=
  (Target.bytesToBits.recBody ⟨B, Vector.replicate (8 * l) false⟩ 0).snd

theorem Target.bytesToBits.eq_spec {l : Nat} (B : Vector Byte l) :
  Target.bytesToBits B = Spec.bytesToBits B := by
  unfold bytesToBits Spec.bytesToBits bytesToBits.recBody byteToBits byteToBits.body
  simp only [BitVec.ofNat_eq_ofNat, ne_eq, decide_not, tsub_zero, Id.run, Id.pure_eq,
    Vector.Inhabited_getElem_eq_getElem!, Vector.set_eq_set!, Id.bind_eq, forIn'_eq_forIn,
    forIn_eq_forIn_range', size, Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one,
    List.forIn_yield_eq_foldl, add_tsub_cancel_right]

def Target.bytesToBits.inv
  {l} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (i : ℕ) (acc : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (j : ℕ) :=
  let C := acc.fst
  let b := acc.snd
  -- prefix of b is properly set
  (∀ i' < i, ∀ j' < 8, b[8*i' + j']! = C0[i']!.testBit j') ∧
  -- ongoing update
  (∀ j' < j, b[8*i + j']! = C0[i]!.testBit j') ∧
  (∀ i' > i, i' < l → ∀ j < 8, b[8*i' + j]! = b0[8*i' + j]!) ∧ -- suffix of b is unchanged
  (∀ i' > i, i' < l → C[i']! = C0[i']!) ∧ -- suffix of C is unchanged
  (i < l → C[i]! = C0[i]! >>> j)

theorem Target.byteToBits.body.spec
  {l} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (i : ℕ) (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (j : ℕ)
  (hinv : bytesToBits.inv C0 b0 i acc j) (hi : i < l) (hj : j < 8) :
  bytesToBits.inv C0 b0 i (body i acc j) (j + 1) := by
  unfold body
  unfold bytesToBits.inv
  unfold bytesToBits.inv at hinv; simp only [gt_iff_lt] at hinv
  obtain ⟨ h0, h1, h2, h3, h4 ⟩ := hinv
  simp only [BitVec.ofNat_eq_ofNat, ne_eq, decide_not, gt_iff_lt]
  generalize hC : acc.fst = C at *
  generalize hb : acc.snd = b at *
  split_conjs
  . intro i' hi' j' hj
    simp only [hi, h4]
    simp_lists [h0]
  . intro j' hj'
    by_cases hj'': j' = j
    . simp only [hi, h4, hj'']
      simp_lists
      simp only [Nat.testBit_to_div_mod, Simp.decide_eq_not_decide, Nat.mod_two_not_eq_one,
        eq_iff_iff]
      natify; simp
      have : 2^j % 256 = 2^j := by
        have : 2^j ≤ 2^7 := by scalar_tac +nonLin
        simp_scalar
      simp only [Nat.shiftRight_eq_div_pow]
    . simp only [hi, h4]
      simp_lists [h1]
  . intro i' hi' hi'' j' hj'
    have : 8*i + j < 8*i' + j' := by scalar_tac
    simp_lists [h2]
  . intro i' hi' hi''
    simp_lists [h3]
  . simp_lists [h4, hi]
    natify
    simp only [BitVec.toNat_udiv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.div_div_eq_div_mul, forall_const]
    ring_nf

theorem Target.byteToBits.recBody.spec
  {l} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (i : ℕ) (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (j : ℕ)
  (hinv : bytesToBits.inv C0 b0 i acc j) (hi : i < l) (hj : j ≤ 8) :
  bytesToBits.inv C0 b0 i (recBody i acc j) 8 := by
  if hj1 : j = 8 then
    simp_all [recBody]
  else
    unfold recBody
    have : 8 - j = (8 - (j+1)) + 1 := by omega
    simp only [this, List.range'_succ]
    simp only [Nat.reduceSubDiff, List.foldl_cons]
    have hinv1 := body.spec C0 b0 i acc j hinv (by omega) (by omega)
    have hinv2 := spec C0 b0 i (body i acc j) (j + 1) hinv1 (by omega) (by omega)
    simp only [recBody, Nat.reduceSubDiff] at hinv2
    apply hinv2
termination_by 8 - j
decreasing_by omega

theorem Target.byteToBits.spec
  {l} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (i : ℕ) (acc : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (hinv : bytesToBits.inv C0 b0 i acc 8) (hi : i < l) :
  bytesToBits.inv C0 b0 (i + 1) (recBody i acc 8) 0 := by
  have hinv1 := byteToBits.recBody.spec C0 b0 i acc 8 hinv (by omega) (by simp)
  simp only [bytesToBits.inv, gt_iff_lt, not_lt_zero', IsEmpty.forall_iff, implies_true,
    BitVec.ushiftRight_zero, true_and] at hinv1 ⊢
  obtain ⟨ h0, h1, h2, h3, h4 ⟩ := hinv1
  generalize hbody: recBody i acc 8 = acc1 at *
  generalize hC1 : acc1.fst = C1 at *
  generalize hb1 : acc1.snd = b1 at *
  split_conjs
  . intro i' hi' j hj
    by_cases hi'': i' = i
    . simp only [hi'']
      simp_lists [h1]
    . simp_lists [h0]
  . intro j' hj'
    simp_lists [h2]
  . intro i' hi' hi''
    simp_lists [h3]
  . simp_lists [h3]

theorem Target.bytesToBits.recBody.step_eq
  {l : ℕ} (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (i : ℕ) (hi : i < l) :
  recBody acc i = recBody (byteToBits acc i) (i + 1) := by
  unfold recBody
  have : l - i = (l - (i+1)) + 1 := by omega
  simp only [this, List.range'_succ, List.foldl_cons]

theorem Target.bytesToBits.recBody.spec
  {l : Nat} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (i : ℕ) (hi : i ≤ l)
  (hinv : bytesToBits.inv C0 b0 i acc 0) :
  bytesToBits.inv C0 b0 l (recBody acc i) 0
 := by
 if hi1 : i = l then
  simp_all [recBody]
 else
  simp_scalar [Target.bytesToBits.recBody.step_eq, hi, hi1]
  have hinv1 := byteToBits.recBody.spec C0 b0 i acc 0 hinv (by omega) (by simp)
  have hinv2 := byteToBits.spec C0 b0 i (byteToBits acc i) hinv1 (by omega)
  have : byteToBits.recBody i (byteToBits acc i) 8 =
         byteToBits acc i := by
    unfold byteToBits.recBody
    simp only [tsub_self, List.range'_zero, List.foldl_nil]
  rw [this] at hinv2
  have hinv3 := spec C0 b0 (byteToBits acc i) (i + 1) (by omega) hinv2
  apply hinv3
termination_by l - i
decreasing_by omega

def Target.bytesToBits.post {l} (B : Vector Byte l) (b : Vector Bool (8 * l)) :=
  ∀ i < l, ∀ j < 8, b[8*i + j]! = B[i]!.testBit j

theorem Target.bytesToBits.spec
  {l : Nat} (B : Vector Byte l) :
  post B (bytesToBits B) := by
  unfold bytesToBits
  generalize hC0 : B = C0 at *
  generalize hb0 : Vector.replicate (8 * l) false = b0 at *
  generalize hacc0 : MProd.mk C0 b0 = acc0 at *
  have hinv0 : bytesToBits.inv C0 b0 0 acc0 0 := by
    unfold inv
    simp only [not_lt_zero', ← hacc0, IsEmpty.forall_iff, implies_true, mul_zero, zero_add,
      gt_iff_lt, BitVec.ushiftRight_zero, and_self]
  have hinv1 := recBody.spec C0 b0 acc0 0 (by omega) hinv0
  unfold inv at hinv1
  obtain ⟨ h0, h1, h2, h3, h4 ⟩ := hinv1
  unfold post
  intro i hi j hj
  generalize hacc1 : recBody acc0 0 = acc1 at *
  simp_lists [h0]

/-!
# byteEncode
-/

def Target.byteEncode.encodeElem.body (d : ℕ) (i : ℕ) (acc : MProd ℕ (Vector Bool (256 * d))) (j : ℕ) :
  MProd ℕ (Vector Bool (256 * d)) :=
  let b := acc.snd
  let a := acc.fst
  let b := b.set! (i * d + j) (Bool.ofNat (a % 2))
  let a := (a - Bool.toNat b[i * d + j]!) / 2
  ⟨ a, b ⟩

def Target.byteEncode.encodeElem.recBody (d : ℕ) (i : ℕ) (acc : MProd ℕ (Vector Bool (256 * d))) (j : ℕ) :
  MProd ℕ (Vector Bool (256 * d)) :=
  List.foldl (byteEncode.encodeElem.body d i) acc (List.range' j (d - j))

def Target.byteEncode.encodeElem (d : ℕ) (F : Polynomial (m d))
  (b : Vector Bool (256 * d)) (i : ℕ) :
  Vector Bool (256 * d) :=
  let a := F[i]!.val
  (encodeElem.recBody d i ⟨ a, b ⟩ 0).snd

def Target.byteEncode.encode.recBody (d : ℕ) (F : Polynomial (m d)) (b : Vector Bool (256 * d)) (i : ℕ) :
  Vector Bool (256 * d) :=
  List.foldl (byteEncode.encodeElem d F) b (List.range' i (256 - i))

def Target.byteEncode.encode (d : ℕ) (F : Polynomial (m d)) :
  Vector Bool (256 * d) :=
  encode.recBody d F (Vector.replicate (256 * d) false) 0

def Target.byteEncode (d : ℕ) (F : Polynomial (m d)) :
  Vector Byte (32 * d) :=
  bitsToBytes (Vector.cast (by ring_nf) (byteEncode.encode d F))

def Target.byteEncode.eq_spec (d : ℕ) (F : Polynomial (m d)) :
  byteEncode d F = Spec.byteEncode d F := by
  unfold byteEncode byteEncode.encode byteEncode.encode.recBody byteEncode.encodeElem byteEncode.encodeElem.recBody
    byteEncode.encodeElem.body Spec.byteEncode
  simp only [tsub_zero, bitsToBytes.eq_spec, Id.run, Vector.Inhabited_getElem_eq_getElem!,
    Id.pure_eq, Vector.set_eq_set!, Id.bind_eq, forIn'_eq_forIn, forIn_eq_forIn_range', size,
    add_tsub_cancel_right, Nat.div_one, List.forIn_yield_eq_foldl, Nat.reduceAdd,
    Nat.add_one_sub_one]

irreducible_def Target.byteEncode.encodeElem.body.inv
  (d : ℕ) (F : Polynomial (m d)) (acc : MProd ℕ (Vector Bool (256 * d))) (i : ℕ) (j : ℕ) :=
  let b := acc.snd
  let a := acc.fst
  -- The prefix is set
  (∀ i' < i, ∀ j' < d, b[i' * d + j']! = F[i']!.val.testBit j') ∧
  -- Encoding the current element
  (∀ j' < j, b[i * d + j']! = F[i]!.val.testBit j') ∧
  (∀ j' ∈ [j:d], b[i * d + j']! = false) ∧
  a = F[i]!.val / 2^j ∧
  -- The suffix is not set
  (∀ i' ∈ [i+1:256], ∀ j < d, b[i' * d + j]! = false)

def Target.byteEncode.encodeElem.body.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {acc : MProd ℕ (Vector Bool (256 * d))} {j : ℕ}
  (hinv : inv d F acc i j)
  (hi : i < 256 := by omega) (hj : j < d := by omega) :
  inv d F (body d i acc j) i (j + 1) := by
  simp only [inv, mem_std_range_step_one, and_imp, gt_iff_lt, body] at *
  obtain ⟨ h0, h1, h2, h3, h4 ⟩ := hinv
  generalize hb1: acc.snd = b1 at *
  generalize ha1: acc.fst = a1 at *
  have : i * d ≤ 255 * d := by scalar_tac +nonLin
  have : i * d + j < 256 * d := by omega
  split_conjs
  . intros i' hi' j' hj'
    have : i' * d + d ≤ i * d := by
      have : 1 * d ≤ i * d := by scalar_tac +nonLin
      have : i' * d ≤ (i - 1) * d := by scalar_tac +nonLin
      simp only [Nat.sub_mul] at this
      omega
    have : i' * d + j' < i * d + j := by omega
    simp_lists [h0]
  . intros j' hj'
    by_cases hj'': j' = j
    . simp only [hj'']; simp_lists
      simp only [Bool.ofNat, h3, ne_eq, Nat.mod_two_not_eq_zero, Nat.testBit,
        Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero]
      tauto
    . simp_lists [*]
  . intros j' hj' hj''
    have : i * d + j < i * d + j' := by omega
    have : i * d + j' < 256 * d := by omega
    simp_lists [h2]
  . simp_lists; simp only [h3]
    have : F[i]!.val / 2 ^ j - F[i]!.val / 2 ^ j % 2 =
           2 * (F[i]!.val / 2^j / 2) := by
      have := Nat.mod_def (F[i]!.val / 2 ^ j) 2
      omega
    rw [this]
    simp only [Nat.div_div_eq_div_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel_left₀]
    ring_nf
  . intros i' hi' hi'' j' hj'
    have : i * d + d ≤ i' * d := by
      have : 1 * d ≤ i' * d := by scalar_tac +nonLin
      have : i * d ≤ (i' - 1) * d := by scalar_tac +nonLin
      simp only [Nat.sub_mul] at this
      omega
    have : i * d + j < i' * d + j' := by omega
    have : i' * d ≤ 255 * d := by scalar_tac +nonLin
    have : i' * d + j' < 256 * d := by omega
    simp_lists [h4]

def Target.byteEncode.encodeElem.recBody.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {acc : MProd ℕ (Vector Bool (256 * d))} {j : ℕ}
  (hinv : body.inv d F acc i j)
  (hi : i < 256 := by omega) (hj : j ≤ d := by omega) :
  body.inv d F (recBody d i acc j) i d := by
  if hj' : j = d then
    simp only [hj', gt_iff_lt, le_refl] at *
    unfold recBody
    simp only [tsub_self, List.range'_zero, List.foldl_nil]
    apply hinv
  else
    have hinv1 := Target.byteEncode.encodeElem.body.spec hinv
    have hinv2 := spec hinv1
    have : recBody d i (body d i acc j) (j + 1) = recBody d i acc j := by
      unfold recBody
      have : d - j = (d - (j + 1)) + 1 := by omega
      rw [this]
      simp only [List.range'_succ, List.foldl_cons]
    simp only [this] at hinv2
    apply hinv2
termination_by d - j
decreasing_by simp_wf; omega

/- Remark: we're using the fact that b[.]! is defined and equal to false even if the index is out of bounds
   (this makes the property true even if `i + 1 = 256`) -/
theorem Target.byteEncode.encodeElem.body.inv_d_imp_inv
  {d : ℕ} {F : Polynomial (m d)} {acc : MProd ℕ (Vector Bool (256 * d))} {i : ℕ}
  (hinv : inv d F acc i d) :
  inv d F ⟨F[i+1]!.val, acc.snd⟩ (i + 1) 0 := by
  simp only [inv, mem_std_range_step_one, isEmpty_Prop, not_and, not_lt, imp_self,
    IsEmpty.forall_iff, implies_true, and_imp, true_and, not_lt_zero', zero_le, pow_zero,
    Nat.div_one] at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  split_conjs
  . intros i' hi' j' hj'
    by_cases hi'': i' = i
    . simp only [hi'']
      simp_lists [h1]
    . simp_lists [h0]
  . intros j' hj'
    by_cases h: i + 1 < 256
    . simp_lists [h3]
    . have : 256 * d ≤ (i + 1) * d := by scalar_tac +nonLin
      have : 256 * d ≤ (i + 1) * d + j' := by omega
      simp only [this, Vector.getElem!_default, Bool.default_bool]
  . simp_lists [h3]

irreducible_def Target.byteEncode.encode.inv
  (d : ℕ) (F : Polynomial (m d)) (b : Vector Bool (256 * d)) (i : ℕ) :=
  -- The prefix is set
  (∀ i' < i, ∀ j < d, b[i' * d + j]! = F[i']!.val.testBit j) ∧
  -- The suffix is not set
  (∀ i' ∈ [i:256], ∀ j < d, b[i' * d + j]! = false)

theorem Target.byteEncode.encodeElem.body_inv_0_imp_inv
  {d : ℕ} {F : Polynomial (m d)} {acc : MProd ℕ (Vector Bool (256 * d))} {i : ℕ}
  (hinv : body.inv d F acc i 0) :
  encode.inv d F acc.snd i := by
  simp only [body.inv, not_lt_zero', IsEmpty.forall_iff, implies_true, mem_std_range_step_one,
    zero_le, true_and, pow_zero, Nat.div_one, and_imp, encode.inv] at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  simp_lists [*]
  intros i' hi' hi'' j hj
  by_cases hi''': i' = i <;> simp_lists [*]

theorem Target.byteEncode.encodeElem.inv_imp_body_inv
  {d : ℕ} {F : Polynomial (m d)} {b : Vector Bool (256 * d)} {i : ℕ}
  (hinv : encode.inv d F b i) (hi : i < 256 := by omega) :
  body.inv d F ⟨ F[i]!.val, b ⟩ i 0 := by
  simp only [encode.inv, mem_std_range_step_one, and_imp, gt_iff_lt, body.inv, not_lt_zero',
    IsEmpty.forall_iff, implies_true, zero_le, true_and, pow_zero, Nat.div_one] at *
  obtain ⟨ h0, h1 ⟩ := hinv
  split_conjs <;> simp_lists [*]

def Target.byteEncode.encodeElem.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {b : Vector Bool (256 * d)}
  (hinv : encode.inv d F b i)
  (hi : i < 256 := by omega) :
  encode.inv d F (encodeElem d F b i) (i + 1) := by
  simp only [encodeElem]
  have := inv_imp_body_inv hinv
  have := Target.byteEncode.encodeElem.recBody.spec this
  have := body.inv_d_imp_inv this
  have := body_inv_0_imp_inv this
  simp only at this
  apply this

def Target.byteEncode.encode.recBody.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {b : Vector Bool (256 * d)}
  (hinv : inv d F b i)
  (hi : i ≤ 256 := by omega) :
  inv d F (recBody d F b i) 256 := by
  if hi' : i = 256 then
    simp only [hi', le_refl] at *
    simp only [recBody, tsub_self, List.range'_zero, List.foldl_nil, hinv]
  else
    have := encodeElem.spec hinv
    have := spec this
    have : recBody d F (encodeElem d F b i) (i + 1) = recBody d F b i := by
      simp only [recBody, Nat.reduceSubDiff]
      have : 256 - i = (255 - i) + 1 := by omega
      rw [this]
      simp only [List.range'_succ, List.foldl_cons]
    simp_all
termination_by 256 - i
decreasing_by simp_wf; omega

def Target.byteEncode.encode.spec (d : ℕ) (F : Polynomial (m d)) :
  ∀ i < 256, ∀ j < d, (encode d F)[i * d + j]! = F[i]!.val.testBit j := by
  have hinv0 : inv d F (Vector.replicate (256 * d) false) 0 := by
    simp only [inv, not_lt_zero', IsEmpty.forall_iff, implies_true, mem_std_range_step_one, zero_le,
      true_and]
    intros i hi j hj
    have : i * d ≤ 255 * d := by scalar_tac +nonLin
    simp_lists
  have hinv1 := recBody.spec hinv0
  generalize hb : encode d F = b at *
  have : recBody d F (Vector.replicate (256 * d) false) 0 = b := by
    simp only [← hb, encode]
  simp only [this] at hinv1
  simp only [inv, mem_std_range_step_one, isEmpty_Prop, not_and, not_lt, imp_self,
    IsEmpty.forall_iff, implies_true, and_true] at hinv1
  apply hinv1

/-- The important theorem! -/
def Target.byteEncode.spec (d : ℕ) (F : Polynomial (m d)) (hd : 0 < d := by omega) :
  ∀ i < 32 * d, ∀ j < 8,
    (byteEncode d F)[i]!.testBit j = F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d) := by
  intros i hi j hj
  unfold byteEncode
  have h0 := encode.spec d F
  generalize hb : (Vector.cast (by ring_nf) (encode d F) : Vector Bool (8 * (32 * d))) = b at *
  have h1 := Target.bitsToBytes.spec  b
  simp only [bitsToBytes.post] at h1
  generalize hb1 : bitsToBytes b = b1 at *
  simp_lists [h1]
  simp only [← hb, Vector.getElem!_cast]

  /- We have to play with the indices -/
  let ij := 8 * i + j
  let i' := ij / d
  let j' := ij % d
  have : i' < 256 := by
    simp +zetaDelta only
    simp_scalar

  have : j' < d := by
    simp +zetaDelta only
    scalar_tac +nonLin

  refold_let ij

  have : ij = i' * d + j' := by
    have := Nat.mod_add_div ij d
    simp +zetaDelta only [gt_iff_lt] at *
    ring_nf at *
    omega

  simp only [this, Nat.mul_add_mod_self_right]
  simp_lists [h0]
  simp +zetaDelta only [dvd_refl, Nat.mod_mod_of_dvd]
  simp_scalar

/-!
# Streamed byteEncode

Below, we prove that the streamed version of `byteEncode` is correct.
This is one of the interesting theorems.
-/

/-- `d`: the number of bits with which to encode an element
    `n`: the number of bytes in the accumulator
-/
structure Stream.EncodeState (n : ℕ) where
  b : List Byte
  bi : ℕ -- number of bytes written to `b`
  acc : BitVec (8 * n)
  acci : ℕ -- number of bits written to `acc`

def Stream.encode.body (d : ℕ) {n : ℕ} (x : ZMod (m d)) (s : EncodeState n) :
  EncodeState n :=
  let nBits := min d (8 * n - s.acci)
  let bits := BitVec.ofNat (8 * n) x.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  let xBits := d - nBits

  let acc := s.acc ||| (bits <<< s.acci)
  let acci := s.acci + nBits

  -- Flush
  if acci = 8 * n then
    let b := s.b.setSlice! s.bi acc.toLEBytes
    let bi := s.bi + n

    -- Encode the remaining bits
    let x := x.val >>> nBits
    let acc := BitVec.ofNat (8 * n) x
    let acci := xBits
    {b, bi, acc, acci}
  else
    {s with acc, acci}

def Stream.encode.recBody (d : ℕ) {n : ℕ} (F : Vector (ZMod (m d)) 256) (s : EncodeState n) (i : ℕ) :
  EncodeState n :=
  List.foldl (fun s i => encode.body d F[i]! s) s (List.range' i (256 - i))

def Stream.encode (d n : ℕ) (F : Vector (ZMod (m d)) 256) : List Byte :=
  let s : EncodeState n := {
    b := List.replicate (32 * d) 0,
    bi := 0,
    acc := 0,
    acci := 0,
  }
  (encode.recBody d F s 0).b

/-- Invariant about the lengths -/
def Stream.encode.length_inv (d n : ℕ) (b : List Byte) (bi acci i : ℕ) : Prop :=
  b.length = 32 * d ∧
  i ≤ 256 ∧
  -- This is the subtil part
  bi = n * ((d * i) / (8 * n)) ∧
  acci = (d * i) % (8 * n)

/-- The full invariant.

The best way of understanding the invariant and the proof, in particular the equations between the indices
(`i`, `s.bi`, `s.acci`, etc.) is to make a drawing. We typically have something like this:

                                        accumulator `s.acc` (`8 * n` bits)
                                       ______________________________________
                                      |                                      |
                                                                  `8 * s.bi + 8 * n`
  `8 * s.bi` bits encoded in `s.b`    `s.acci` bits in `s.acc`               |
|------------------------------------|------------------------|--------------|---------|
                                     |                        |   `nBits`      `xBits` |
                                     |                        |                        |
                                     |                     `d * i`                 `d * (i + 1)`
                                     |            (`i` elements encoded to `d * i`
                                     |             bits in `s.b` and `s.acc`)
                                     |                        |
                                     |                        |
                     `s.bi = ((d * i) / (8 * n)) * n`         |
                                     |________________________|
                                    `s.acci = (d * i) % (8 * n)`
-/
def Stream.encode.inv
  (d : ℕ) {n : ℕ} (F : Vector (ZMod (m d)) 256) (s : EncodeState n) (i : ℕ) : Prop :=
  -- The lengths are correct
  length_inv d n s.b s.bi s.acci i ∧
  -- The bits are properly set in the destination buffer
  (∀ i < s.bi, ∀ j < 8, s.b[i]!.testBit j = F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d)) ∧
  -- The bits are properly set in the accumulator
  (∀ j < s.acci, s.acc[j]! = F[(8 * s.bi + j) / d]!.val.testBit ((8 * s.bi + j) % d)) ∧
  (∀ j ∈ [s.acci:8*n], s.acc[j]! = false)

/--
Auxiliary lemma: `Stream.encode.body` preserves the length invariant.
-/
theorem Stream.encode.body.length_spec
  {i d n : ℕ} (x0 : ZMod (m d)) {s : EncodeState n} [NeZero (m d)]
  (hinv : length_inv d n s.b s.bi s.acci i)
  (hi : i < 256 := by omega)
  (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega) :
  let s1 := body d x0 s
  length_inv d n s1.b s1.bi s1.acci (i + 1) := by
  simp only [length_inv, body]
  glet nBits := min d (8 * n - s.acci)

  glet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  glet xBits := d - nBits

  glet acc := s.acc ||| (bits <<< s.acci)
  glet acci := s.acci + nBits

  glet b := s.b.setSlice! s.bi acc.toLEBytes
  glet bi := s.bi + n

  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv

  split
  . rename_i hif0

    -- Number of bytes in the output buffer
    have hBi : s.bi + n = n * (d * (i + 1) / (8 * n)) ∧
                xBits = (d * (i + 1)) % (8 * n) := by
      have hd0 := calc
        8 * s.bi + 8 * n + xBits = 8 * s.bi + s.acci + (nBits + xBits) := by simp only [← hif0, acci]; ring_nf
        _ = 8 * s.bi + s.acci + d := by
          have : nBits + xBits = d := by omega
          simp only [this, Nat.add_left_inj]
        _ = d * i + d := by
          -- Using the characterization of euclidean division
          have : 8 * s.bi + s.acci = d * i := by
            have hMod := Nat.mod_add_div (d * i) (8 * n)
            rw [← hMod]
            simp only [h2, h3]
            ring_nf
          omega
        _ = d * (i + 1) := by ring_nf

      have hd1 := calc
        (8 * s.bi + 8 * n + xBits) % (8 * n) = ((8 * s.bi + 8 * n) + xBits) % (8 * n) := by ring_nf
        _ = xBits % (8 * n) := by
          have : (8 * s.bi + 8 * n) % (8 * n) = 0 := by -- TODO: make simp_scalar work here
            simp only [h2, ← mul_assoc, Nat.add_mod_right, Nat.mul_mod_right]
          rw [Nat.add_mod]
          simp only [this, zero_add, dvd_refl, Nat.mod_mod_of_dvd]
        _ = xBits := by scalar_tac +nonLin

      have hd2 := calc
        (d * (i + 1)) / (8 * n) = (d * (i + 1) - (d * (i + 1)) % (8 * n)) / (8 * n)
            := by simp_scalar
        _ =  (8 * s.bi + 8 * n + xBits - xBits) / (8 * n) := by simp only [← hd0, hd1]
        _ = (8 * s.bi + 8 * n) / (8 * n) := by simp_scalar
        _ = s.bi / n + 1 := by
          simp_scalar

      have : s.bi + n = n * (d * (i + 1) / (8 * n)) := by
        simp_scalar [hd2, h2]
        ring_nf

      have : xBits = (d * (i + 1)) % (8 * n) := by
        simp only [← hd0, hd1]

      tauto

    have : b.length = 32 * d := by scalar_tac

    simp only
    split_conjs <;> tauto
  . have hLt : s.acci < 8 * n := by
      simp only [h3]
      simp_scalar
    have hLt' : s.acci + nBits < 8 * n := by omega
    have nBitsEq : nBits = d := by omega

    -- Number of bits in the accumulator
    have hAcci : acci = d * (i + 1) % (8 * n) := by
      simp only [acci]
      zmodify
      simp only [h3, ZMod.natCast_mod, Nat.cast_mul, nBitsEq, acci]
      ring_nf

    -- Number of bytes in the output buffer
    have hBi : s.bi = n * (d * (i + 1) / (8 * n)) := by
      -- Using the characterization of euclidean division
      have hMod := Nat.mod_add_div (d * i) (8 * n)
      have hMod' := Nat.mod_add_div (d * (i + 1)) (8 * n)
      --
      simp only [mul_assoc, ← h2, ← h3, ← hAcci] at hMod hMod'
      have : d * (i + 1) = d * i + d := by ring_nf
      conv at hMod' => rhs; rw [this]
      simp only [nBitsEq, acci] at hMod'
      have : 8 * s.bi = 8 * (n * (d * (i + 1) / (8 * n))) := by omega
      omega

    simp only
    tauto
/--
Auxiliary lemma. See `Stream.encode.body`.

This lemma proves important properties about the encoded bits in the accumulator
before we flush it (if we need to flush it).
-/
theorem Stream.encode.body.spec_before_flush
  {d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n}
  (hinv : inv d F s i) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega) :
  let x0 := F[i]!
  let nBits := d ⊓ (8 * n - s.acci)
  let bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))

  let acc := s.acc ||| (bits <<< s.acci)
  let acci := s.acci + nBits
  -- The masking is equivalent to a modulo
  bits.toNat = x0.val % 2^nBits ∧
  -- Accumulator: prefix (the bits are properly set)
  (∀ j < acci, acc[j]! = F[(8 * s.bi + j) / d]!.val.testBit ((8 * s.bi + j) % d)) ∧
  -- Accumulator: suffix (the bits are still equal to 0)
  (∀ j ∈ [acci:8*n], acc[j]! = false)

  := by

  simp only [inv, mem_std_range_step_one, and_imp] at hinv
  simp only
  obtain ⟨ ⟨ _, h0, h1, h2 ⟩, h3, h4, h5 ⟩ := hinv

  glet x0 := F[i]!
  glet nBits := d ⊓ (8 * n - s.acci)
  glet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  glet x := x0.val >>> nBits

  glet acc := s.acc ||| (bits <<< s.acci)
  glet acci := s.acci + nBits

  have hBitsEq : bits.toNat = x0.val % 2^nBits := by
    simp only [bits]
    simp only [BitVec.shiftLeft_sub_one_eq_mod]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_pow, bits]

    have : 2 < 2 ^(8*n) := by simp_scalar
    have : 2 ^ nBits < 2 ^ (8 * n) := by simp_scalar
    have : x0.val < 2 ^ (8 * n) := by scalar_tac
    simp_scalar

  -- Accumulator: prefix
  have hAccPre : ∀ j < acci, acc[j]! = F[(8 * s.bi + j) / d]!.val.testBit ((8 * s.bi + j) % d) := by
    intros j hj
    simp only [acci] at hj
    simp only [BitVec.getElem!_or, acc, acci]
    by_cases hj': j < s.acci -- TODO: simp_lists +split
    . simp_lists [h4]
    . simp_lists [h5]

      simp only [BitVec.getElem!_eq_testBit_toNat, hBitsEq, Nat.testBit_mod_two_pow, acci, acc]
      simp_scalar
      simp only [x0, acc, acci]

      have hij : (8 * s.bi + j) / d = i ∧
                 (8 * s.bi + j) % d = j - s.acci := by
        have := Nat.mod_add_div (d * i) (8 * n)
        have : 8 * s.bi = 8 * n * (d * i / (8 * n)) := by
          simp only [h1, x0, acc, acci]
          ring_nf

        have : 8 * s.bi + j = d * i + (j - s.acci) := by omega

        split_conjs
        . have hi : (8 * s.bi + j) / d = (d * i + (j - s.acci)) / d := by simp only [this]
          simp_scalar at hi
          apply hi
        . have hi : (8 * s.bi + j) % d = (d * i + (j - s.acci)) % d := by simp only [this]
          simp_scalar at hi
          apply hi
      simp only [hij]

  -- Accumulator: suffix
  have hAccPost : ∀ j ∈ [acci:8*n], acc[j]! = false := by
    simp only [mem_std_range_step_one, and_imp]
    intros j hj hj'
    simp only [BitVec.getElem!_or, Bool.or_eq_false_iff, acc]
    simp_lists [*]
    simp only [← h2, acc]
    simp only [BitVec.shiftLeft_sub_one_eq_mod, BitVec.ofNat_eq_ofNat, bits, acc]
    simp_lists

  tauto

/--
Auxiliary lemma.

This lemma handles the case of `Stream.encode.body` when there is no flush.
-/
theorem Stream.encode.body.spec_no_flush
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n} [NeZero (m d)]
  (hinv : inv d F s i) (hi : i < 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n)
  (hm : m d < 2^(8*n) := by omega)
  (hacci : ¬ s.acci + d ⊓ (8 * n - s.acci) = 8 * n)
  :
  inv d F (body d F[i]! s) (i + 1) := by
  -- Important intermediate results about the accumulator and `bits`
  have ⟨ hBitsEq, hAccPre, hAccPost ⟩ := Stream.encode.body.spec_before_flush hinv
  have hlinv := length_spec F[i]! hinv.left
  revert hlinv

  -- Unfold the body and the invariant
  simp only [inv, mem_std_range_step_one, and_imp] at hinv
  obtain ⟨ ⟨ _, h0, h1, h2 ⟩, h3, h4, h5 ⟩ := hinv
  simp only [body]
  simp_ifs
  simp only [inv]
  intro hlinv

  split_conjs <;> try tauto

/--
Auxiliary lemma.

This lemma introduces important properties about the output buffer (`s.b`)
after we flushed the accumulator.
-/
theorem Stream.encode.body.spec_with_flush_bi
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n}
  (hinv : inv d F s i)
  (hi : i < 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega)
  (h0 : s.acci + d ⊓ (8 * n - s.acci) = 8 * n := by omega) :
  let x0 := F[i]!
  let nBits := d ⊓ (8 * n - s.acci)
  let bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  let xBits := d - nBits
  let acc := s.acc ||| (bits <<< s.acci)
  -- Number of bytes in the output buffer
  (s.bi + n = n * (d * (i + 1) / (8 * n)) ∧ xBits = (d * (i + 1)) % (8 * n)) ∧
  -- Bits in the output buffer
  (∀ i < s.bi + n, ∀ j < 8,
      (s.b.setSlice! s.bi acc.toLEBytes)[i]!.testBit j =
        F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d))
  := by

  -- Important intermediate results about the accumulator and `bits`
  have ⟨ hBitsEq, hAccPre, hAccPost ⟩ := Stream.encode.body.spec_before_flush hinv
  have hlinv1 := length_spec F[i]! hinv.left
  simp only [body] at hlinv1
  simp_ifs at hlinv1

  -- Introducing abbreviations
  glet x0 := F[i]!
  glet nBits := d ⊓ (8 * n - s.acci)
  glet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  glet x := x0.val >>> nBits
  glet xBits := d - nBits

  glet acc := s.acc ||| (bits <<< s.acci)
  glet acci := s.acci + nBits

  obtain ⟨ ⟨ _, _, h1, h2 ⟩, h3, h4, h5 ⟩ := hinv
  obtain ⟨ _, _, hBi ⟩ := hlinv1

  -- Bits in the output buffer
  have :
    ∀ i < s.bi + n, ∀ j < 8,
      (s.b.setSlice! s.bi acc.toLEBytes)[i]!.testBit j =
        F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d) := by
    -- We have to do a case disjunction:
    intros i' hi' j hj
    have : acc.toLEBytes.length = n := by simp only [Nat.mul_mod_right, BitVec.toLEBytes_length,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
    have : s.bi + n ≤ s.b.length := by
      have :=
        calc s.bi + n = n * (d * (i + 1) / (8 * n)) := by omega
              _ = n * (d * (i + 1) / 8 / n) := by simp_scalar
              _ ≤ d * (i + 1) / 8 := by simp_scalar
              _ ≤ d * 256 / 8 := by
                -- TODO: improve
                have : d * (i + 1) ≤ d * 256 := by simp_scalar
                simp_scalar
              _ = 32 * d := by omega
      scalar_tac

    by_cases hi'': i' < s.bi -- TODO: simp_lists +split
    . simp_lists [h3]
    . simp_lists [hAccPre]
      have : 8 * s.bi + (8 * (i' - s.bi) + j) = 8 * i' + j := by omega
      simp only [this]

  tauto


/--
Auxiliary lemma.

This lemma handles the case of `Stream.encode.body` when there is a flush.
-/
theorem Stream.encode.body.spec_with_flush
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n} [NeZero (m d)]
  (hinv : inv d F s i) (hi : i < 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n)
  (hm : m d < 2^(8*n) := by omega)
  (h0 : s.acci + d ⊓ (8 * n - s.acci) = 8 * n)
  :
  inv d F (body d F[i]! s) (i + 1) := by
  -- Important intermediate results about the accumulator and `bits`
  have ⟨ hBitsEq, hAccPre, hAccPost ⟩ := Stream.encode.body.spec_before_flush hinv
  -- Intermediate results about the output buffer
  have ⟨ hBi, hsb ⟩ := Stream.encode.body.spec_with_flush_bi hinv
  revert h0 hBitsEq hAccPre hAccPost hBi hsb -- TODO: refold let doesn't apply to assumptions which happen before

  -- Unfold the body and the invariant
  unfold body
  simp only [inv, length_inv, mem_std_range_step_one, and_imp, and_assoc] at hinv
  obtain ⟨ _, h0, h1, h2, h3, h4, h5 ⟩ := hinv
  simp only

  -- Introducing abbreviations
  glet x0 := F[i]!
  glet nBits := d ⊓ (8 * n - s.acci)
  glet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  glet x := x0.val >>> nBits
  glet xBits := d - nBits

  glet acc := s.acc ||| (bits <<< s.acci)
  glet acci := s.acci + nBits

  intro h0 hBitsEq hAccPre hAccPost hBi hsb

  simp_ifs
  simp only [inv, length_inv, and_assoc]

  glet bits := BitVec.ofNat (8 * n) x &&& (1#(8*n) <<< nBits - 1#(8*n))

  split_conjs <;> try tauto
  . scalar_tac
  . intros j hj
    simp only [x, x0]

    have hij : (8 * (s.bi + n) + j) / d = i ∧
                (8 * (s.bi + n) + j) % d = nBits + j
                := by
      have hij := calc
        8 * (s.bi + n) + j = 8 * s.bi + 8 * n + j := by omega
        _ = 8 * s.bi + s.acci + nBits + j := by omega
        _ = d * i + nBits + j := by
          -- Property of euclidean division
          have hMod := Nat.mod_add_div (d * i) (8 * n)
          simp only [← h2, mul_assoc, ← h1] at hMod
          omega

      have : nBits + j < d := by omega
      have hi := calc
        (8 * (s.bi + n) + j) / d = (d * i + (nBits +j)) / d := by simp only [hij]; ring_nf
        _ = i := by simp_scalar

      have hj := calc
        (8 * (s.bi + n) + j) % d = (d * i + (nBits +j)) % d := by simp only [hij]; ring_nf
        _ = nBits + j := by simp_scalar

      simp only [hi, hj, Nat.add_left_inj, and_self]
    simp only [hij]
    simp only [BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, Bool.and_iff_right_iff_imp, decide_eq_true_eq]
    omega

  . simp only [mem_std_range_step_one, and_imp, x]
    intros j hj hj'
    simp only [BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, Bool.and_eq_false_imp, decide_eq_true_eq, x0, x]
    intros

    apply Nat.testBit_eq_false_of_lt
    have : m d ≤ 2 ^(nBits + j) := by
      unfold m Q
      split
      . scalar_tac +nonLin
      . have : 2^12 ≤ 2^(nBits + j) := by scalar_tac +nonLin
        omega

    scalar_tac +nonLin

/--
The important lemma about `Stream.encode.body`: calling this function once preserves the invariant
(but we encoded one more element, so the index goes from `i` to `i + 1`).
-/
theorem Stream.encode.body.spec
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n} [NeZero (m d)]
  (hinv : inv d F s i) (hi : i < 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega) :
  inv d F (body d F[i]! s) (i + 1) := by
  by_cases h0 : s.acci + d ⊓ (8 * n - s.acci) = 8 * n
  . apply spec_with_flush hinv <;> omega
  . apply Stream.encode.body.spec_no_flush hinv <;> omega

theorem Stream.encode.recBody.spec
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n} [NeZero (m d)]
  (hinv : inv d F s i) (hi : i ≤ 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega) :
  inv d F (recBody d F s i) 256 := by
  if hi: i = 256 then
    simp only [hi]
    unfold recBody
    simp only [tsub_self, List.range'_zero, List.foldl_nil]
    simp_all
  else
    unfold recBody
    have : 256 - i = (256 - (i+1)) + 1 := by omega
    rw [this, List.range'_succ]
    simp only [Nat.reduceSubDiff, List.foldl_cons]
    have hinv1 := body.spec hinv
    have hinv2 := spec hinv1
    unfold recBody at hinv2
    simp only [Nat.reduceSubDiff] at hinv2
    apply hinv2
termination_by 256 - i
decreasing_by omega

def Stream.encode.post (d : ℕ) (F : Vector (ZMod (m d)) 256) (b : List Byte ) : Prop :=
  b.length = 32 * d ∧
  (∀ i < 32 * d, ∀ j < 8, b[i]!.testBit j = F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d))

/-- Auxiliary spec for `Stream.encode`: we use the post-condition to prove that it is actually equal to `Spec.encode` -/
theorem Stream.encode.spec_aux
  (d n : ℕ) (F : Vector (ZMod (m d)) 256) [NeZero (m d)]
  (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega)
  (hn1 : n ∣ 32 := by omega) :
  post d F (encode d n F) := by
  unfold encode
  simp only
  glet s : EncodeState n := {
    b := List.replicate (32 * d) 0,
    bi := 0,
    acc := 0,
    acci := 0,
  }

  have hinv : inv d F s 0 := by
    unfold inv length_inv
    simp only [BitVec.ofNat_eq_ofNat, List.length_replicate, zero_le, mul_zero, Nat.zero_div,
      Nat.zero_mod, not_lt_zero', IsEmpty.forall_iff, implies_true, BitVec.getElem!_zero, zero_add,
      Bool.false_eq, mem_std_range_step_one, true_and, and_self, and_assoc, s]

  replace hinv := Stream.encode.recBody.spec hinv

  glet s1 := recBody d F s 0

  unfold inv length_inv at hinv
  simp only [le_refl, mem_std_range_step_one, and_imp, and_assoc, true_and] at hinv
  obtain ⟨ _, h0, h1, h2, h3, h4 ⟩ := hinv

  unfold post
  split_conjs
  . scalar_tac
  . intros i hi j hj

    have : s1.bi = 32 * d := by
      simp only [h0]
      have : d * 256 = 8 * (32 * d) := by ring_nf
      rw [this]
      simp_scalar
      -- TODO: we should be able to automate this
      have hn2 : n ∣ 32 * d := by apply Nat.dvd_mul_right_of_dvd hn1
      simp only [hn2, Nat.mul_div_cancel']

    simp_lists [h2]

/-- `Stream.encode` is equal to `Spec.encode` -/
theorem Stream.encode.spec
  (d n : ℕ) (F : Polynomial (m d))
  (hd : 0 < d := by omega)
  (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega)
  (hn1 : n ∣ 32 := by omega) :
  encode d n F = (Spec.byteEncode d F).toList := by
  -- Characterization of Stream.encode
  have h1 := encode.spec_aux d n F
  unfold post at h1
  obtain ⟨ h1, h1' ⟩ := h1
  -- Characterization of Spec.byteEncode
  rw [← Target.byteEncode.eq_spec]
  have h2 := Target.byteEncode.spec d F
  -- Using the extensional equality
  rw [List.eq_iff_forall_eq_getElem!]
  simp
  split_conjs
  . scalar_tac
  . intros i hi
    rw [Byte.eq_iff]
    simp_lists [*]

/-!
# Compress and encode
-/

def compressOpt (d : ℕ) (x : ℕ) : ℤ := if d < 12 then ⌈ ((2^d : ℚ) / (Q : ℚ)) * x ⌋ % 2^d else x

def Stream.compressOpt_encode.body (d : ℕ) {n : ℕ} (x : Spec.Zq) (s : EncodeState n) :=
  Stream.encode.body d (compressOpt d x.val) s

def Stream.compressOpt_encode.recBody (d : ℕ) {n : ℕ} (F : Vector (ZMod Q) 256) (s : EncodeState n) (i : ℕ) :
  EncodeState n :=
  List.foldl (fun s i => compressOpt_encode.body d F[i]! s) s (List.range' i (256 - i))

def Stream.compressOpt_encode
  (d n : ℕ) (F : Vector (ZMod Q) 256) : List Byte :=
  let s : EncodeState n := {
    b := List.replicate (32 * d) 0,
    bi := 0,
    acc := 0,
    acci := 0,
  }
  (compressOpt_encode.recBody d F s 0).b

def Stream.compressOpt_encode_eq (d n : ℕ) (F : Vector Zq 256) [NeZero (m d)]
  (hd : 0 < d := by omega)
  (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega)
  (hn1 : n ∣ 32 := by omega) :
  compressOpt_encode d n F = (Spec.byteEncode d (F.map (fun (x : Zq) => (compressOpt d x.val : ZMod (m d))))).toList := by
  have := Stream.encode.spec d n (F.map (fun (x : Zq) => (compressOpt d x.val : ZMod (m d))))
  rw [← this]; clear this
  --
  simp only [compressOpt_encode, compressOpt_encode.recBody, BitVec.ofNat_eq_ofNat, tsub_zero,
    encode, encode.recBody]
  apply congrArg
  apply List.forall_imp_foldl_eq
  . simp only
  . simp only [List.mem_range'_1, zero_le, zero_add, true_and]
    intros s i hi
    simp only [compressOpt_encode.body]
    simp_lists

/-!
# Compress
-/

/- Marking those definitions as irreducible because otherwise we get a "(kernel) deep recursion detected"
   when checking the proof term of one of the proofs below.
-/
irreducible_def compress.mulConstant : BitVec 64 := BitVec.ofNat 64 0x9d7dbb
irreducible_def compress.shiftConstant : ℕ := 35

def compress_bv (d : ℕ) (x : BitVec 64) : BitVec 64 :=
  let multiplication := x * compress.mulConstant
  let coefficient := (multiplication >>> (compress.shiftConstant - (d + 1)))
  let coefficient := (coefficient + 1) >>> 1
  let coefficient := coefficient &&& (1 <<< d) - 1#64
  coefficient

set_option maxHeartbeats 10000000 in
/-- The compression is implemented in a clever way.
    We brute force the proof by enumerating all the cases for `d < 12`, then using `bv_decide`.
-/
private theorem compress_bv_eq_aux (x : BitVec 64) (h : x < 3329#64) (d : ℕ) (hd : d < 12) :
  compress_bv d x = ((2^(d+1) * x + Q) / (2 * Q)) % BitVec.ofNat 64 (2^d)
  := by
  simp [compress_bv, compress.mulConstant, compress.shiftConstant, ← BitVec.ofNat_pow]
  cases d; simp; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  ring_nf at hd; simp at hd

def compress (d : ℕ) (x : ℕ) : ℕ :=
  let multiplication := x * 0x9d7dbb
  let coefficient := (multiplication >>> (35 - (d + 1)))
  let coefficient := (coefficient + 1) >>> 1
  let coefficient := coefficient &&& (1 <<< d) - 1
  coefficient

theorem compress_bv_eq (x : ℕ) (h : x < 3329) (d : ℕ) (hd : d < 12) :
  (compress_bv d x).toNat = compress d x := by
  simp only [compress_bv, BitVec.natCast_eq_ofNat, BitVec.ofNat_eq_ofNat, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_mul_mod, Nat.one_mod, BitVec.toNat_sub, Nat.add_one_sub_one, Nat.add_mod_mod, compress,
    Nat.reduceSubDiff]
  have : x * compress.mulConstant.toNat < 3329 * 0x9d7dbb := by
    simp only [compress.mulConstant, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceMul]
    omega
  have : (↑x * compress.mulConstant.toNat) >>> (compress.shiftConstant - (d + 1)) ≤ (↑x * compress.mulConstant.toNat) :=
    Nat.shiftRight_le _ _
  simp_scalar
  have : (18446744073709551615 + 1 <<< d) % 18446744073709551616 = (1 <<< d) - 1 := by
    have : 1 <<< d > 0 := by
      have := @Nat.le_shiftLeft 1 d
      omega
    have : 18446744073709551615 + 1 <<< d = 2^64 + ((1 <<< d) - 1) := by simp only [Nat.reducePow]; omega
    rw [this]; clear this
    simp only [Nat.reducePow, Nat.add_mod_left, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
      Nat.reduceAdd, gt_iff_lt]
    have := Nat.one_shiftLeft d
    have := @Nat.pow_lt_pow_of_lt 2 d 64 (by simp) (by omega)
    omega
  rw [this]; clear this
  simp only [compress.mulConstant, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    compress.shiftConstant, Nat.reduceSubDiff]

theorem compress_eq (x : ℕ) (h : x < 3329) (d : ℕ) (hd : d < 12) :
  compress d x = ⌈ ((2^d : ℚ) / (Q : ℚ)) * x ⌋ % (2^d)
  := by
  -- Use `compres_bv` as an intermediate step
  rw [← compress_bv_eq x h d hd]
  rw [compress_bv_eq_aux] <;> try (simp -failIfUnchanged; omega)

  -- Get rid of the `⌈ ... ⌋`
  have : ((2^d : ℚ) / (Q : ℚ)) * (x : ℚ) = ((2 ^ d * x : ℕ) : ℚ) / (Q : ℚ) := by
    simp only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_pow]; ring_nf
  rw [this]; clear this
  rw [Nat.rat_round_div]; swap; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

  -- Finish the proof by simplifying everything
  simp only [BitVec.ofNat_eq_ofNat, BitVec.natCast_eq_ofNat, Nat.cast_ofNat, BitVec.reduceMul,
    BitVec.toNat_umod, BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.mul_mod_mod, Nat.reduceMod, Nat.mod_add_mod, Int.ofNat_emod, Int.natCast_div,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Int.reduceMul]

  have : (2 ^ d : Int) % 18446744073709551616 = 2^d := by
    apply Int.emod_eq_of_lt
    . simp only [Nat.ofNat_nonneg, pow_nonneg]
    . have := @Nat.pow_lt_pow_of_lt 2 d 64 (by simp) (by omega)
      zify at this
      omega
  rw [this]; clear this

  congr
  simp only [← BitVec.ofNat_pow, BitVec.toNat_ofNat, Nat.reducePow, Int.ofNat_emod, Nat.cast_pow,
    Nat.cast_ofNat]
  have : (2^(d+1) : Int) ≤ 2^12 := by
    have := @Nat.pow_le_pow_right 2 (by simp) (d + 1) 12 (by omega)
    zify at this
    omega
  have : (2^(d + 1) : Int) % 18446744073709551616 = 2^(d+1) := by
    apply Int.emod_eq_of_lt
    . simp only [Nat.ofNat_nonneg, pow_nonneg]
    . omega
  rw [this]; clear this

  have := @Int.mul_nonneg (2^(d+1)) x (by simp) (by simp)
  have := @Int.mul_le_mul_of_nonneg_right (2^(d+1)) (2^12) x (by omega)
  have := @Int.emod_eq_of_lt (2 ^ (d + 1) * ↑x + 3329) 18446744073709551616
    (by omega) (by omega)
  rw [this]; clear this

  ring_nf

/-!
# Decompress
-/

def decompressOpt (d : ℕ) (y : ℕ) : ℤ := if d < 12 then ⌈ ((Q : ℚ) / (2^d : ℚ)) * y ⌋ else y

end Symcrust.SpecAux
