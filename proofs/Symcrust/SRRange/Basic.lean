import Mathlib.Data.Nat.Defs

namespace Aeneas

-- TODO: PR for Lean.Std
/-- A "structural recursion" range type, that we use to implement for
    loops with structural induction.

    This is the same as `Std.Range`, but with a slighly different implementation
    of the loop inside the `forIn'` function, for which we introduce a fuel parameter.

    We do this because of issues with the kernel reducing definitions eagerly, leading
    to explosions in the presence of well-founded recursion. This this:
    https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/simp.20taking.20a.20long.20time.20on.20a.20small.20definition/near/495050322
  -/
structure SRRange where
  start : Nat := 0
  stop  : Nat
  step  : Nat := 1
  step_pos : 0 < step

instance : Membership Nat SRRange where
  mem r i := r.start ≤ i ∧ i < r.stop ∧ (i - r.start) % r.step = 0

namespace SRRange
universe u v

/-- The number of elements in the range. -/
@[simp] def size (r : SRRange) : Nat := (r.stop - r.start + r.step - 1) / r.step

/-- A bound of the number of elements in the range -/
@[simp] def sizeBound (r : SRRange) : Nat := r.stop - r.start

@[inline] protected def forIn' [Monad m] (range : SRRange) (init : β)
    (f : (i : Nat) → i ∈ range → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (maxSteps : Nat) (b : β) (i : Nat)
      (hs : (i - range.start) % range.step = 0) (hl : range.start ≤ i := by omega) : m β := do
    -- Introduce structural induction
    match maxSteps with
    | 0 => pure b
    | maxSteps+1 =>
      if h : i < range.stop then
        match (← f i ⟨hl, by omega, hs⟩ b) with
        | .done b  => pure b
        | .yield b =>
          have := range.step_pos
          loop maxSteps b (i + range.step) (by rwa [Nat.add_comm, Nat.add_sub_assoc hl, Nat.add_mod_left])
      else
        pure b
  have := range.step_pos
  loop range.sizeBound init range.start (by simp)

instance : ForIn' m SRRange Nat inferInstance where
  forIn' := SRRange.forIn'

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

end SRRange

end Aeneas
