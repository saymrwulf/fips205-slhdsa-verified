/- ──────────────────────────────────────────────────────────────────────────────
   gen/SlhVerify/FunsExternal.lean — hand-maintained external functions.

   TWO CLASSES of external, per honesty invariants H4/H5:

   (1) THE CRYPTOGRAPHIC BOUNDARY — the deliberate opaque axioms.
       The five SLH-DSA-SHA2-128s hash primitives, reached by name from the
       monomorphic verify path (verify_mono::oracle):
         · verify_mono.oracle.f      — F  (chain / FORS leaf)
         · verify_mono.oracle.h      — H  (Merkle node)
         · verify_mono.oracle.t_l    — T_len (WOTS+ pk compression)
         · verify_mono.oracle.t_len  — T_k   (FORS root compression)
         · verify_mono.oracle.h_msg  — H_msg (message digest)
       These are SHA-256-based; their correctness against FIPS 180-4 is the
       standing hash-oracle boundary (see TRUSTED-BASE.md). The apex
       certificate will carry EXACTLY these five beyond Lean's three kernel
       axioms — nothing else.

   (2) TRANSPILER PLUMBING — core-library externals Aeneas emits for this
       extraction config. These carry NO cryptographic content. The u32
       range Step machinery is DISCHARGED below with real definitions
       (2026-07-22). The try_from / is_err / &u32-Sub / wots-Take /
       Debug-fmt axioms were ELIMINATED at source level by the
       fips205-source de-plumbing patch (8 sites, semantics identical,
       differential-test-validated) and their declarations deleted here
       (dead-stub rule, 2026-07-23). Remaining as axioms: the Take
       iterator machinery used by helpers::to_int (slh_verify_internal's
       digest split — the apex round's de-plumbing item) and the zeroize
       blanket impls (never on the verify path). The #print axioms audit
       confirms only class (1) survives in any certificate cone.
   ────────────────────────────────────────────────────────────────────────────── -/
-- This is a template file: rename it to "FunsExternal.lean" and fill the holes.
import Aeneas
import SlhVerify.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open fips205

-- (the core::iter::adapters::take::Take::next axiom was here; DELETED
-- 2026-07-24 after de-plumbing round 2 removed the last Take iterator on the
-- verify path — to_int/base_2b now index-loop. dead-stub hygiene rule.)

/-- [core::iter::range::{impl core::iter::range::Step for u32}::backward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 290:16-290:74
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::backward_checked]
    Visibility: public -/
-- DISCHARGED (2026-07-22, proof phase): Aeneas.Std ships a real `Step`
-- instance only for `usize` (StepUsize); u32 ranges therefore extracted as
-- opaque axioms. These are the FAITHFUL models of Rust's `impl Step for u32`
-- (core/src/iter/range.rs), mirroring StepUsize: forward/backward via
-- u32::try_from(n)-then-checked_{add,sub}; steps_between = saturating
-- difference. Real defs, axiom-clean — so the range-loop cones (chain, and
-- every layer above) carry no plumbing axiom, only the kernel three + the
-- five hash oracles. NOT the deployed hash boundary; ordinary loop control.
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::backward_checked"]
def U32.Insts.CoreIterRangeStep.backward_checked
  : Std.U32 → Std.Usize → Result (Option Std.U32) :=
  fun start n =>
    if h : n.val < 2 ^ 32 then
      ok (Std.U32.checked_sub start (Std.U32.ofNatCore n.val (by omega)))
    else ok none

/-- [core::iter::range::{impl core::iter::range::Step for u32}::forward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 282:16-282:73
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::forward_checked]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::forward_checked"]
def U32.Insts.CoreIterRangeStep.forward_checked
  : Std.U32 → Std.Usize → Result (Option Std.U32) :=
  fun start n =>
    if h : n.val < 2 ^ 32 then
      ok (Std.U32.checked_add start (Std.U32.ofNatCore n.val (by omega)))
    else ok none

/-- [core::iter::range::{impl core::iter::range::Step for u32}::steps_between]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 271:16-271:84
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::steps_between]
    Visibility: public -/
@[rust_fun "core::iter::range::{core::iter::range::Step<u32>}::steps_between"]
def U32.Insts.CoreIterRangeStep.steps_between
  : Std.U32 → Std.U32 → Result (Std.Usize × (Option Std.Usize)) :=
  fun start end_ =>
    if h : start.val > end_.val then ok (0#usize, none)
    else
      let steps := Std.Usize.ofNatCore (end_.val - start.val) (by scalar_tac)
      ok (steps, some steps)

/-- [zeroize::{impl zeroize::Zeroize for Z}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.0/src/lib.rs', lines 274:4-274:25
    Name pattern: [zeroize::{zeroize::Zeroize<@Z>}::zeroize]
    Visibility: public -/
@[rust_fun "zeroize::{zeroize::Zeroize<@Z>}::zeroize"]
axiom zeroize.Zeroize.Blanket.zeroize
  {Z : Type} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) : Z → Result Z

/-- [zeroize::{impl zeroize::Zeroize for [Z; N]}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.0/src/lib.rs', lines 346:4-346:25
    Name pattern: [zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize]
    Visibility: public -/
@[rust_fun "zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize"]
axiom Array.Insts.ZeroizeZeroize.zeroize
  {Z : Type} {N : Std.Usize} (ZeroizeInst : zeroize.Zeroize Z) :
  Array Z N → Result (Array Z N)

/-- [zeroize::__internal::{impl zeroize::__internal::AssertZeroize for T}::zeroize_or_on_drop]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.0/src/lib.rs', lines 846:8-846:40
    Name pattern: [zeroize::__internal::{zeroize::__internal::AssertZeroize<@T>}::zeroize_or_on_drop]
    Visibility: public -/
@[rust_fun
  "zeroize::__internal::{zeroize::__internal::AssertZeroize<@T>}::zeroize_or_on_drop"]
axiom zeroize.__internal.AssertZeroize.Blanket.zeroize_or_on_drop
  {T : Type} (ZeroizeInst : zeroize.Zeroize T) : T → Result T

/-- [fips205::verify_mono::oracle::f]:
    Source: 'src/verify_mono.rs', lines 49:4-51:5 -/
axiom verify_mono.oracle.f
  (N : Std.Usize) :
  Slice Std.U8 → types.Adrs → Slice Std.U8 → Result (Array Std.U8 N)

/-- [fips205::verify_mono::oracle::h]:
    Source: 'src/verify_mono.rs', lines 54:4-56:5 -/
axiom verify_mono.oracle.h
  (N : Std.Usize) :
  Slice Std.U8 → types.Adrs → Slice Std.U8 → Slice Std.U8 → Result
    (Array Std.U8 N)

/-- [fips205::verify_mono::oracle::t_l]:
    Source: 'src/verify_mono.rs', lines 60:4-64:5 -/
axiom verify_mono.oracle.t_l
  {X : Std.Usize} {N : Std.Usize} :
  Slice Std.U8 → types.Adrs → Array (Array Std.U8 N) X → Result (Array
    Std.U8 N)

/-- [fips205::verify_mono::oracle::t_len]:
    Source: 'src/verify_mono.rs', lines 69:4-73:5 -/
axiom verify_mono.oracle.t_len
  {X : Std.Usize} {N : Std.Usize} :
  Slice Std.U8 → types.Adrs → Array (Array Std.U8 N) X → Result (Array
    Std.U8 N)

/-- [fips205::verify_mono::oracle::h_msg]:
    Source: 'src/verify_mono.rs', lines 81:4-85:5 -/
axiom verify_mono.oracle.h_msg
  (M : Std.Usize) :
  Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Result
    (Array Std.U8 M)

