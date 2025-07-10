import Aeneas

open Lean Aeneas Aeneas.Std Aeneas.SRRange Result

-- **TODO** Write a docstring-like comment explaining that this namespace has scoped instances which
-- override the instance defined in `src/lean/Init/While.lean` invoked by the `while` syntax

namespace CustomLoops

def Option.Loop.forIn.loop {β : Type u} (f : Unit → β → Option (ForInStep β)) (b : β) : Option β := do
  match ← f () b with
    | ForInStep.done b  => pure b
    | ForInStep.yield b => loop f b
partial_fixpoint

@[inline]
partial def Option.Loop.forIn {β : Type u} (_ : Loop) (init : β)
  (f : Unit → β → Option (ForInStep β)) : Option β :=
  forIn.loop f init

scoped instance : ForIn Option Loop Unit where
  forIn := Option.Loop.forIn

def Result.Loop.forIn.loop {β : Type u} (f : Unit → β → Result (ForInStep β)) (b : β) : Result β := do
  match ← f () b with
    | ForInStep.done b  => pure b
    | ForInStep.yield b => loop f b
partial_fixpoint

@[inline]
partial def Result.Loop.forIn {β : Type u} (_ : Loop) (init : β)
  (f : Unit → β → Result (ForInStep β)) : Result β :=
  forIn.loop f init

scoped instance : ForIn Result Loop Unit where
  forIn := Result.Loop.forIn

theorem Result.Loop.forIn.loop.partial_correctness {β : Type u} (f : Unit → β → Result (ForInStep β))
  (motive : β → β → Error → Prop) :
  (∀ (loop : β → Result β),
    (∀ b : β, ∀ r : β, ∀ e : Error, (loop b = ok r → motive b r e) ∧ (loop b = fail e → motive b r e)) →
      ∀ b : β, ∀ r : β, ∀ e : Error,
        ((do
          let __do_lift ← f () b
          match __do_lift with
            | ForInStep.done b => pure b
            | ForInStep.yield b => loop b) =
        ok r → motive b r e) ∧
        ((do
          let __do_lift ← f () b
          match __do_lift with
            | ForInStep.done b => pure b
            | ForInStep.yield b => loop b) =
        fail e → motive b r e)
  ) → ∀ (b r : β) (e : Error),
  (Loop.forIn.loop f b = ok r → motive b r e) ∧ (Loop.forIn.loop f b = fail e → motive b r e) := by
  intro h b r e
  let motive' : (β → Result β) → Prop := fun f' =>
    ∀ b : β, ∀ r : β, ∀ e : Error,
      (f' b = ok r → motive b r e) ∧
      (f' b = fail e → motive b r e)
  have motive'_admissible : @Lean.Order.admissible (β → Result β) Lean.Order.instCCPOPi motive' := by
    unfold Lean.Order.admissible
    intro motive'' hmotive'' hmotive'
    simp only [motive'] at hmotive'
    simp only [Lean.Order.CCPO.csup]
    unfold Lean.Order.fun_csup
    intro b r e
    simp only [Lean.Order.CCPO.csup, Lean.Order.flat_csup, ne_eq, exists_exists_and_eq_and]
    split
    . next h =>
      have hx := Classical.choose_spec h
      tlet x := Classical.choose h
      rcases hx with ⟨⟨f', h2, h3⟩, h1⟩
      specialize hmotive' f' h2 b r e
      rw [h3] at hmotive'
      exact hmotive'
    . simp
  apply Result.Loop.forIn.loop.fixpoint_induct f motive' motive'_admissible h

end CustomLoops
