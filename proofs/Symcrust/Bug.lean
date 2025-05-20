import Lean

def f (n : Nat) : Nat := Id.run do
  let mut n := n
  let mut i := 1 -- We need to have two mutable variables
  for _ in [0:256] do -- We need the upper bound to be high
    i := i + 1
    n := n
  pure n

#check Lean.Meta.Simp.Config

set_option trace.profiler true
example : f 0 = 0 := by
  unfold f
  conv => lhs; simp only
  --simp -implicitDefEqProofs only
  --simp only [f]
