import Symcrust.SRRange.Basic

namespace Aeneas

namespace SRRange

namespace Notations

  /-- We need to update this macro rule for two reasons:
      - we need to use a more complex solving procedure.
        We simply use the simplifier with the `zetaDelta` option to unfold
        the local definitions.
      - we use our own definition of `Range`, which uses structural recursion
        rather than well-founded recursion. The use of well-founded recursion
        causes issues in the Lean kernel.
  -/
  scoped macro_rules
    | `([ $start : $stop : $step ]) =>
      `({ start := $start, stop := $stop, step := $step,
          step_pos := by simp +zetaDelta [] : SRRange })

end Notations

end SRRange

end Aeneas
