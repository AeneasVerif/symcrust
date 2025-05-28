import Lean
import Mathlib.Tactic.Ring

namespace NormMod

theorem Int.neg_add_emod_self_left {a b c : ℤ} : (-a + b) % c = ((c - a) + b) % c := by
  conv => lhs; rw [← Int.add_emod_self_left]
  ring_nf

theorem Int.sub_eq_add_minus : ∀ (a b : Int), a - b = a + (-b) := by omega
theorem Int.add_minus_add_eq_minus_add : ∀ (a b c : Int), a + (-b + c) = (-b) + (a + c) := by omega
theorem Int.minus_add_minus_add_eq_minus_add : ∀ (a b c : Int), -a + (-b + c) = -(a + b) + c := by omega

open Lean.Parser.Tactic in
/-- A tactic to normalize modulo operations.

    We do the following:
    ```
    (x + y - 12) % 16 = (-12 + x + y) % 16          -- push the negative constant to the left
                      = (-12 + (x + y)) % 16        -- isolate it
                      = ((16 - 12) + (x + y)) % 16  -- add the modulus itself
                      = (4 + x + y) % 16
    ```
    TODO: it doesn't work well if we have `- x` somewhere in the expression
-/
macro "norm_mod" cfg:optConfig loc:(location)? : tactic =>
  `(tactic |
    -- TODO: repeteadly performing the operation causes issues
    -- repeat fail_if_no_progress
      -- Push to the left and isolate
      --ring_nf $cfg:optConfig $(loc)? <;> -- push to the left
      (try simp only [Int.add_assoc, Int.sub_eq_add_minus, Int.add_minus_add_eq_minus_add, Int.minus_add_minus_add_eq_minus_add] $(loc)?) <;> -- isolate the constant
      (try rw [Int.neg_add_emod_self_left] $(loc)?) <;> -- add the modulo
      ring_nf $cfg:optConfig $(loc)? -- normalize again
    )

end NormMod
