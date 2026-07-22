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
       extraction config (u32::try_from, Result::is_err, the iterator Step /
       Take machinery driving `for` ranges, the zeroize blanket impls, the
       TryFromIntError Debug impl). These carry NO cryptographic content.
       They are adopted here as axioms so the model type-checks at phase 1
       (no certificates exist yet, so H4's cone requirement is vacuous). The
       proof phase will discharge each from Aeneas.Std / real definitions and
       the #print axioms audit will then confirm only class (1) survives in
       any certificate cone. Tracked as the phase-2 de-plumbing item.
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

/-- [core::convert::num::ptr_try_from_impls::{impl core::convert::TryFrom<usize, core::num::error::TryFromIntError> for u32}::try_from]:
    Source: '/rustc/library/core/src/convert/num.rs', lines 300:12-300:64
    Name pattern: [core::convert::num::ptr_try_from_impls::{core::convert::TryFrom<u32, usize, core::num::error::TryFromIntError>}::try_from]
    Visibility: public -/
@[rust_fun
  "core::convert::num::ptr_try_from_impls::{core::convert::TryFrom<u32, usize, core::num::error::TryFromIntError>}::try_from"]
axiom U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
  :
  Std.Usize → Result (core.result.Result Std.U32
    core.num.error.TryFromIntError)

/-- [core::convert::num::{impl core::convert::TryFrom<u64, core::num::error::TryFromIntError> for u32}::try_from]:
    Source: '/rustc/library/core/src/convert/num.rs', lines 300:12-300:64
    Name pattern: [core::convert::num::{core::convert::TryFrom<u32, u64, core::num::error::TryFromIntError>}::try_from]
    Visibility: public -/
@[rust_fun
  "core::convert::num::{core::convert::TryFrom<u32, u64, core::num::error::TryFromIntError>}::try_from"]
axiom U32.Insts.CoreConvertTryFromU64TryFromIntError.try_from
  :
  Std.U64 → Result (core.result.Result Std.U32
    core.num.error.TryFromIntError)

/-- [core::ops::arith::{impl core::ops::arith::Sub<&'_0 u32, u32> for u32}::sub]:
    Source: '/rustc/library/core/src/internal_macros.rs', lines 38:12-38:68
    Name pattern: [core::ops::arith::{core::ops::arith::Sub<u32, &'0 u32, u32>}::sub]
    Visibility: public -/
@[rust_fun "core::ops::arith::{core::ops::arith::Sub<u32, &'0 u32, u32>}::sub"]
axiom U32.Insts.CoreOpsArithSubShared0U32U32.sub
  : Std.U32 → Std.U32 → Result Std.U32

/-- [core::iter::adapters::take::{impl core::iter::traits::iterator::Iterator<Clause0_Item> for core::iter::adapters::take::Take<I>}::next]:
    Source: '/rustc/library/core/src/iter/adapters/take.rs', lines 36:4-36:55
    Name pattern: [core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>}::next]
    Visibility: public -/
@[rust_fun
  "core::iter::adapters::take::{core::iter::traits::iterator::Iterator<core::iter::adapters::take::Take<@I>, @Clause0_Item>}::next"]
axiom core.iter.adapters.take.Take.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type} {Clause0_Item : Type} (traitsiteratorIteratorInst :
  core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.take.Take I → Result ((Option Clause0_Item) ×
    (core.iter.adapters.take.Take I))

/-- [core::iter::range::{impl core::iter::range::Step for u32}::backward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 290:16-290:74
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::backward_checked]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::backward_checked"]
axiom U32.Insts.CoreIterRangeStep.backward_checked
  : Std.U32 → Std.Usize → Result (Option Std.U32)

/-- [core::iter::range::{impl core::iter::range::Step for u32}::forward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 282:16-282:73
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::forward_checked]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::forward_checked"]
axiom U32.Insts.CoreIterRangeStep.forward_checked
  : Std.U32 → Std.Usize → Result (Option Std.U32)

/-- [core::iter::range::{impl core::iter::range::Step for u32}::steps_between]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 271:16-271:84
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::steps_between]
    Visibility: public -/
@[rust_fun "core::iter::range::{core::iter::range::Step<u32>}::steps_between"]
axiom U32.Insts.CoreIterRangeStep.steps_between
  : Std.U32 → Std.U32 → Result (Std.Usize × (Option Std.Usize))

/-- [core::iter::traits::iterator::Iterator::take]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 1447:4-1449:20
    Name pattern: [core::iter::traits::iterator::Iterator::take]
    Visibility: public -/
@[rust_fun "core::iter::traits::iterator::Iterator::take"]
axiom core.iter.traits.iterator.Iterator.take.default
  {Self : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Std.Usize → Result (core.iter.adapters.take.Take Self)

/-- [core::num::error::{impl core::fmt::Debug for core::num::error::TryFromIntError}::fmt]:
    Source: '/rustc/library/core/src/num/error.rs', lines 9:9-9:14
    Name pattern: [core::num::error::{core::fmt::Debug<core::num::error::TryFromIntError>}::fmt]
    Visibility: public -/
@[rust_fun
  "core::num::error::{core::fmt::Debug<core::num::error::TryFromIntError>}::fmt"]
axiom core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt
  :
  core.num.error.TryFromIntError → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [core::result::{core::result::Result<T, E>}::is_err]:
    Source: '/rustc/library/core/src/result.rs', lines 646:4-646:38
    Name pattern: [core::result::{core::result::Result<@T, @E>}::is_err]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_err"]
axiom core.result.Result.is_err
  {T : Type} {E : Type} : core.result.Result T E → Result Bool

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

