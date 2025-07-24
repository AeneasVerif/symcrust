import Symcrust.Spec

/-!
This file contains theorems about `Symcrust.Spec.bytesToBits` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to Algorithm 4 (Bytes to Bits).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.bytesToBits`.
    - `Lean spec (functional)` corresponds to `Target.bytesToBits`.
      - The theorem that mathematically characterizes `Target.bytesToBits` is `Target.bytesToBits.spec`.
    - `⟷₂` corresponds to  `Target.bytesToBits.eq_spec`.
    - There is no analogue for `Auxiliary spec`, `⟷₄`, or `Aeneas translation` because there is no
      single function in the Rust code that corresponds to this function.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

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
  simp only [BitVec.ofNat_eq_ofNat, ne_eq, decide_not, tsub_zero,
    Vector.Inhabited_getElem_eq_getElem!, Vector.set_eq_set!, bind_pure_comp, map_pure,
    forIn'_eq_forIn, forIn_eq_forIn_range', size, Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one,
    List.forIn_pure_yield_eq_foldl, add_tsub_cancel_right, Id.run_pure]

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
      simp only [Nat.testBit_eq_decide_div_mod_eq, Simp.decide_eq_not_decide, Nat.mod_two_not_eq_one,
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
