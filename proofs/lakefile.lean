import Lake
open Lake DSL

require aeneas from "../../aeneas/backends/lean"

package «symcrust»

@[default_target]
lean_lib «Symcrust»
