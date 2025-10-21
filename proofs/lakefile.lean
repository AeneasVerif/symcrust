import Lake
open Lake DSL

require aeneas from "../../aeneas/backends/lean"
require sha3 from "../../sha3/Sha3"

package «symcrust»

@[default_target]
lean_lib «Symcrust»

lean_exe spec_tests where
  root := `Symcrust.Spec.Test
  supportInterpreter := false
