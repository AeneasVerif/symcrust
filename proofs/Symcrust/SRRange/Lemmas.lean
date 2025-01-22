import Symcrust.SRRange.Basic

namespace Aeneas

namespace SRRange

/-!
# Lemmas about `SRRange`

We provide lemmas rewriting for loops over `Std.Range` in terms of `List.range'`.
-/

/-- Generalization of `mem_of_mem_range'` used in `forIn'_loop_eq_forIn'_range'` below. -/
private theorem mem_of_mem_range'_aux {r : SRRange} {a : Nat} (w₁ : (i - r.start) % r.step = 0)
    (w₂ : r.start ≤ i)
    (h : a ∈ List.range' i ((r.stop - i + r.step - 1) / r.step) r.step) : a ∈ r := by
  obtain ⟨j, h', rfl⟩ := List.mem_range'.1 h
  refine ⟨by omega, ?_⟩
  rw [Nat.lt_div_iff_mul_lt r.step_pos, Nat.mul_comm] at h'
  constructor
  · omega
  · rwa [Nat.add_comm, Nat.add_sub_assoc w₂, Nat.mul_add_mod_self_left]

theorem mem_of_mem_range' {r : SRRange} (h : x ∈ List.range' r.start r.size r.step) : x ∈ r := by
  unfold size at h
  apply mem_of_mem_range'_aux (by simp) (by simp) h

private theorem size_eq (r : SRRange) (h : i < r.stop) :
    (r.stop - i + r.step - 1) / r.step =
      (r.stop - (i + r.step) + r.step - 1) / r.step + 1 := by
  have w := r.step_pos
  if i + r.step < r.stop then -- Not sure this case split is strictly necessary.
    rw [Nat.div_eq_iff w, Nat.add_one_mul]
    have : (r.stop - (i + r.step) + r.step - 1) / r.step * r.step ≤
        (r.stop - (i + r.step) + r.step - 1) := Nat.div_mul_le_self _ _
    have : r.stop - (i + r.step) + r.step - 1 - r.step <
        (r.stop - (i + r.step) + r.step - 1) / r.step * r.step :=
      Nat.lt_div_mul_self w (by omega)
    omega
  else
    have : (r.stop - i + r.step - 1) / r.step = 1 := by
      rw [Nat.div_eq_iff w, Nat.one_mul]
      omega
    have : (r.stop - (i + r.step) + r.step - 1) / r.step = 0 := by
      rw [Nat.div_eq_iff] <;> omega
    omega

private theorem forIn'_loop_eq_forIn'_range' [Monad m] (r : SRRange)
    (maxSteps : Nat) (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) (i) (w₁) (w₂)
    (hMaxSteps : r.stop - i ≤ maxSteps) :
    forIn'.loop r f maxSteps init i w₁ w₂ =
      forIn' (List.range' i ((r.stop - i + r.step - 1) / r.step) r.step) init
        fun a h => f a (mem_of_mem_range'_aux w₁ w₂ h) := by
  have w := r.step_pos
  revert init i
  induction maxSteps <;> intros init i w₁ w₂ hMaxSteps
  . rw [forIn'.loop]
    simp only [forIn']
    have hEq : (r.stop - i + r.step - 1) / r.step = 0 := by
      have : r.stop - i + r.step - 1 < r.step := by omega
      simp [this]
    simp [hEq]
  . rename_i maxSteps hInd
    rw [forIn'.loop]
    split <;> rename_i h
    · simp only [size_eq r h, List.range'_succ, List.forIn'_cons]
      congr 1
      funext step
      split
      · simp
      · rw [hInd]
        omega
    · have : (r.stop - i + r.step - 1) / r.step = 0 := by
        rw [Nat.div_eq_iff] <;> omega
      simp [this]

@[simp] theorem forIn'_eq_forIn'_range' [Monad m] (r : SRRange)
    (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) :
    forIn' r init f =
      forIn' (List.range' r.start r.size r.step) init (fun a h => f a (mem_of_mem_range' h)) := by
  conv => lhs; simp only [forIn', SRRange.forIn']
  simp only [size]
  rw [forIn'_loop_eq_forIn'_range']
  simp [SRRange.sizeBound]

@[simp] theorem forIn_eq_forIn_range' [Monad m] (r : SRRange)
    (init : β) (f : Nat → β → m (ForInStep β)) :
    forIn r init f = forIn (List.range' r.start r.size r.step) init f := by
  simp only [forIn, forIn'_eq_forIn'_range']

end SRRange

end Aeneas
