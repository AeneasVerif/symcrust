import Symcrust.DivRange.Basic

namespace Aeneas

namespace DivRange

example : Std.Range := [0:128]

namespace Notations
  scoped syntax:max "[" withoutPosition(term ":" ">" term ":" "/" term) "]" : term

  scoped macro_rules
    | `([ $start :  > $stop : /$step ]) =>
      `({ start := $start, stop := $stop, divisor := $step,
          divisor_pos := by simp +zetaDelta [] : DivRange })

  example : DivRange := [256:>1:/2]

end Notations

end DivRange

end Aeneas
