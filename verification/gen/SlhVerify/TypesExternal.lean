/- gen/SlhVerify/TypesExternal.lean — hand-maintained external types.
   The single external type is a core-library error type introduced by
   u32::try_from; it carries no cryptographic content. -/
-- This is a template file: rename it to "TypesExternal.lean" and fill the holes.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048


