import Aeneas
import Symcrust.Properties.While

open Aeneas.Std Result

open CustomLoops in
def resFlipCoin (flip : Nat → Bool) : Result Nat := do
  let mut numFlips := 0
  let mut heads := false
  while !heads do
    heads := flip numFlips
    numFlips := numFlips + 2
  ok numFlips

set_option pp.showLetValues true in
theorem resFlipCoinThm (flip : Nat → Bool) :
  resFlipCoin flip ≠ div → ∃ i, resFlipCoin flip = ok i ∧ 2 ∣ i := by
  intro hDiv
  unfold resFlipCoin
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  tlet loop_body : Unit → MProd Bool ℕ → Result (ForInStep (MProd Bool ℕ)) :=
    fun x r =>
      if r.fst = false then do
        pure PUnit.unit
        pure (ForInStep.yield ⟨flip r.snd, r.snd + 2⟩)
      else pure (ForInStep.done ⟨r.fst, r.snd⟩)
  have : ∃ r' e', CustomLoops.Result.Loop.forIn.loop loop_body ⟨false, 0⟩ = ok r' ∨
    CustomLoops.Result.Loop.forIn.loop loop_body ⟨false, 0⟩ = fail e' := by
    rcases hDiv2 : CustomLoops.Result.Loop.forIn.loop loop_body ⟨false, 0⟩ with r' | e'
    . apply Exists.intro r'
      apply Exists.intro Error.panic -- Need this because `Error` doesn't have `deriving Inhabited`
      simp
    . apply Exists.intro ⟨false, 0⟩
      apply Exists.intro e'
      simp
    . unfold resFlipCoin at hDiv
      rw [forIn, CustomLoops.instForInResultLoopUnit_symcrust] at hDiv
      simp at hDiv
      rw [CustomLoops.Result.Loop.forIn, hDiv2] at hDiv
      simp at hDiv
  rcases this with ⟨r, e, h2⟩
  let* ⟨r2, hr2⟩ ← CustomLoops.Result.Loop.forIn.progress_spec
  . unfold resFlipCoin at hDiv
    rw [forIn, CustomLoops.instForInResultLoopUnit_symcrust] at hDiv
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, ne_eq] at hDiv
    intro h2
    rw [h2] at hDiv
    simp at hDiv
  . intro e2
    let motive : MProd Bool ℕ → MProd Bool ℕ → Error → Prop := fun b _ _ =>
      CustomLoops.Result.Loop.forIn Lean.Loop.mk b loop_body ≠ fail e2
    apply CustomLoops.Result.Loop.forIn.loop.partial_correctness2 loop_body motive _ ⟨false, 0⟩ r e h2
    intro loop hloop b r e3
    constructor
    . intro h3 h4
      unfold loop_body at h3
      split at h3
      . next hb =>
        rw [pure, instPureResult] at h3
        simp only [bind_tc_ok] at h3
        have h5 := (hloop ⟨flip b.2, b.2 + 2⟩ r e).1 h3
        unfold motive at h5
        rw [CustomLoops.Result.Loop.forIn, CustomLoops.Result.Loop.forIn.loop] at h4
        unfold loop_body at h4 h5
        simp only [hb, ↓reduceIte, pure, bind_tc_ok] at h4
        rw [CustomLoops.Result.Loop.forIn] at h5
        simp only [hb, ↓reduceIte, pure, bind_tc_ok] at h4 h5
        rw [h4] at h5
        exact h5 rfl
      . next hb =>
        rw [CustomLoops.Result.Loop.forIn, CustomLoops.Result.Loop.forIn.loop] at h4
        simp [loop_body, hb, Bool.true_eq_false, ↓reduceIte, pure] at h4
    . intro h3
      unfold loop_body at h3
      split at h3
      . next hb =>
        simp [pure] at h3
        unfold motive
        rw [CustomLoops.Result.Loop.forIn, CustomLoops.Result.Loop.forIn.loop]
        intro h4
        unfold loop_body at h4
        simp only [hb, ↓reduceIte, pure, bind_tc_ok, loop_body] at h4
        have h5 := (hloop ⟨flip b.2, b.2 + 2⟩ ⟨false, 0⟩ e3).2 h3
        unfold motive loop_body at h5
        rw [CustomLoops.Result.Loop.forIn] at h5
        simp only [pure, bind_tc_ok, h4, ne_eq, not_true_eq_false, loop_body] at h5
      . simp [pure] at h3
  . rw [forIn, CustomLoops.instForInResultLoopUnit_symcrust]
    simp only [hr2, bind_tc_ok, ok.injEq, exists_eq_left', loop_body]
    let motive : MProd Bool ℕ → MProd Bool ℕ → Error → Prop := fun b r e => 2 ∣ b.2 → 2 ∣ r.2
    have : 2 ∣ 0 := by omega
    revert this
    apply CustomLoops.Result.Loop.forIn.loop.partial_correctness2 loop_body motive _ ⟨false, 0⟩ r2 e
    . left
      rw [CustomLoops.Result.Loop.forIn] at hr2
      rw [hr2]
    . intro loop hloop b r3 e3
      constructor
      . intro h3
        unfold loop_body at h3
        split at h3
        . next hb =>
          simp only [pure, bind_tc_ok] at h3
          intro hb2
          apply (hloop ⟨flip b.2, b.2 + 2⟩ r3 e).1 h3
          simp [hb2]
        . next hb =>
          simp only [pure, hb, bind_tc_ok, ok.injEq, loop_body] at h3
          unfold motive
          simp [← h3]
      . unfold loop_body
        split
        . next hb =>
          simp only [pure, bind_tc_ok, loop_body]
          intro h3 hb2
          apply (hloop ⟨flip b.2, b.2 + 2⟩ r3 e3).2 h3
          simp only [Nat.dvd_add_self_right, hb2]
        . simp [pure]
