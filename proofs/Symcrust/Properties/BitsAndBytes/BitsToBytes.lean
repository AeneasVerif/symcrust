import Symcrust.Spec

/-!
This file contains theorems about `Symcrust.Spec.bitsToBytes` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to Algorithm 3 (Bits to Bytes).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.bitsToBytes`.
    - `Lean spec (functional)` corresponds to `Target.bitsToBytes`.
      - The theorem that mathematically characterizes `Target.bitsToBytes` is `Target.bitsToBytes.spec`.
    - `⟷₂` corresponds to  `Target.bitsToBytes.eq_spec`.
    - There is no analogue for `Auxiliary spec`, `⟷₄`, or `Aeneas translation` because there is no
      single function in the Rust code that corresponds to this function.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

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
  simp only [BitVec.ofNat_eq_ofNat, tsub_zero, Vector.Inhabited_getElem_eq_getElem!,
    Vector.set_eq_set!, bind_pure_comp, map_pure, forIn'_eq_forIn, forIn_eq_forIn_range', size,
    add_tsub_cancel_right, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]

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
  tlet acc1 := recBody b (Vector.replicate l 0#8) 0
  intro i hi j hj
  simp_lists [h0]
