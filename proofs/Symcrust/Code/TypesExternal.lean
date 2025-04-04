import Aeneas
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- [core::fmt::Arguments]
   Source: '/rustc/library/core/src/fmt/mod.rs', lines 319:0-319:24
   Name pattern: core::fmt::Arguments -/
structure core.fmt.Arguments where

/- [core::fmt::rt::Argument]
   Source: '/rustc/library/core/src/fmt/rt.rs', lines 92:0-92:23
   Name pattern: core::fmt::rt::Argument -/
structure core.fmt.rt.Argument where

/- [alloc::collections::TryReserveError]
   Source: '/rustc/library/alloc/src/collections/mod.rs', lines 58:0-58:26
   Name pattern: alloc::collections::TryReserveError -/
inductive alloc.collections.TryReserveError where
