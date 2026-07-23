/- drafts/ChainSpec.lean — WIP: Algorithm 5 (chain) fidelity.

   Goal: the extracted `chain_free` loop equals the explicit s-fold
   application of the (opaque) hash F, with hash-address set to
   i, i+1, …, i+s−1 in turn. Proving this rules out off-by-one loop
   bounds, a wrong address field, and wrong threading — the exact bug
   class the SLH-DSA verify path is exposed to. F stays opaque
   (verify_mono.oracle.f), so the certificate cone is the three kernel
   axioms + oracle.f only.
-/
import SlhVerify.Funs
open Aeneas Aeneas.Std Result ControlFlow
open fips205

set_option maxHeartbeats 2000000

namespace fips205

/-- The mathematical chaining fold, threading the address exactly as the
    extracted body does: at each step set the hash address to the current
    index, hash, advance the index (monadically, matching the u32 range
    iterator's `forward_checked`). Recursion on the step count.

    EFFECT-ORDER NOTE (audited 2026-07-23): the extracted loop increments the
    index FIRST (inside `IteratorRange.next`, via `forward_checked`, failing
    with `.panic` on overflow BEFORE any oracle call), while this fold hashes
    first and increments AFTER (failing with the add's overflow error). The
    two therefore agree only where neither increment can fail — which is
    exactly what the theorem's precondition `start.val + s < 2^32` provides
    (it makes every intermediate index < 2^32, so `forward_checked` always
    yields `some` and `start + 1#u32` always succeeds). The step-case proof
    must discharge BOTH monadic increments from that bound; do not weaken the
    precondition. -/
noncomputable def chainFoldN {N : Std.Usize} (pk_seed : Slice Std.U8) :
    types.Adrs → Array Std.U8 N → Std.U32 → Nat → Result (Array Std.U8 N)
  | _, tmp, _, 0 => ok tmp
  | adrs, tmp, start, (k+1) => do
      let adrs1 ← helpers.Adrs.set_hash_address adrs start
      let s ← lift (Array.to_slice tmp)
      let tmp1 ← verify_mono.oracle.f N pk_seed adrs1 s
      let start1 ← start + 1#u32
      chainFoldN pk_seed adrs1 tmp1 start1 k

/-- The loop over the range [start, start+s) equals the s-step fold. -/
theorem chain_free_loop_eq {N : Std.Usize} (pk_seed : Slice Std.U8) (s : Nat) :
    ∀ (start : Std.U32) (adrs : types.Adrs) (tmp : Array Std.U8 N),
      start.val + s < 2 ^ 32 →
      ∀ (stop : Std.U32), stop.val = start.val + s →
      verify_mono.chain_free_loop { start := start, «end» := stop } pk_seed adrs tmp
        = chainFoldN pk_seed adrs tmp start s := by
  induction s with
  | zero =>
    intro start adrs tmp _ stop hstop
    -- empty range: start.val = stop.val, so start = stop and lt is false
    have hse : start = stop := by
      apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold verify_mono.chain_free_loop chainFoldN
    rw [loop.eq_1]
    unfold verify_mono.chain_free_loop.body core.iter.range.IteratorRange.next
    simp [core.cmp.impls.PartialOrdU32.lt]
  | succ k ih =>
    intro start adrs tmp hb stop hstop
    -- non-empty: lt start stop is true, so the iterator yields `some start`
    -- and steps to start+1; one loop step then aligns with one fold step and
    -- the IH closes the tail.
    have hlt : start.val < stop.val := by omega
    unfold verify_mono.chain_free_loop chainFoldN
    rw [loop.eq_1]
    unfold verify_mono.chain_free_loop.body core.iter.range.IteratorRange.next
    -- OPEN FRONT (the crux): align the loop's monadic `forward_checked start 1`
    -- (a `Result U32`) with the fold's `start1 ← start + 1#u32`, then fold the
    -- continuation `loop body (…)` back into `chain_free_loop` and apply `ih`
    -- at start+1 / stop / k. Needs the U32 add-spec (no overflow from `hb`) and
    -- ControlFlow bind-normalisation. Tractable (dalek loop-spec pattern), WIP.
    sorry

end fips205
