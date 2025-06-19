-- [symcrust]: external functions.
import Aeneas
import Symcrust.Code.Types
open Aeneas.Std
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace Symcrust

/- [symcrust::common::SymCryptRandom] -/
def common.SymCryptRandom : MutRawPtr U8 → Usize → Result Unit := sorry

/- [symcrust::common::SymCryptModuleInit] -/
def common.SymCryptModuleInit : U32 → U32 → Result Unit := sorry

/- [symcrust::common::SymCryptWipe]:
   Source: 'src/common.rs', lines 48:4-48:54 -/
def common.SymCryptWipe : MutRawPtr U8 → Usize → Result Unit := sorry

/- [symcrust::common::random] -/
def common.random : Slice U8 → Result (common.Error × (Slice U8)) := sorry

/- [symcrust::common::wipe_slice]:
   Source: 'src/common.rs', lines 76:0-78:1 -/
def common.wipe_slice {T : Type} : Slice T → Result (Slice T) := sorry

/- [symcrust::hash::shake128_extract] -/
def hash.shake128_extract : hash.HashState → Slice U8 → Bool → Result (hash.HashState × (Slice U8)) := sorry

-- TODO: we shouldn't have this
/- [symcrust::common::{core::cmp::PartialEq<symcrust::common::Error> for symcrust::common::Error}#2::ne]:
   Source: '/rustc/library/core/src/cmp.rs', lines 261:4-261:37 -/
def common.PartialEqsymcrustcommonErrorsymcrustcommonError.ne
  : common.Error → common.Error → Result Bool := sorry

-- TODO: we shouldn't have this
/- [symcrust::key::{core::cmp::PartialEq<symcrust::key::Params> for symcrust::key::Params}#3::ne]:
   Source: '/rustc/library/core/src/cmp.rs', lines 261:4-261:37 -/
def key.PartialEqsymcrustkeyParamssymcrustkeyParams.ne
  : key.Params → key.Params → Result Bool := sorry

namespace Symcrust
