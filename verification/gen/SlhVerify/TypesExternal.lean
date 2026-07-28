/- gen/SlhVerify/TypesExternal.lean — hand-maintained external types.

   THIS FILE DECLARES NO TYPES, deliberately. It once carried a core-library
   error type introduced by `u32::try_from`; the de-plumbing patches removed
   that idiom from the verify path at source level, so the declaration was
   deleted under the dead-stub rule and only the module shell remains (Aeneas's
   split-file layout still expects the module to exist).

   An earlier header claimed the error type was still here, and the Aeneas
   "rename this template and fill the holes" boilerplate had never been removed;
   external review (round-6 NEW-12) flagged both. Corrected 2026-07-28. The file
   is hand-maintained (Aeneas does not regenerate it) and its bytes are
   sha256-pinned by check.sh Phase 0. -/
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048


