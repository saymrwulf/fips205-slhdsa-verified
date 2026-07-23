/- drafts/ChainSpec.lean — WIP: Algorithm 5 (chain) fidelity.

   Goal: the extracted `chain_free` loop equals the explicit s-fold
   application of the (opaque) hash F, with hash-address set to
   i, i+1, …, i+s−1 in turn — ruling out off-by-one loop bounds, a wrong
   address field, and wrong threading. F stays opaque (oracle.f), so a
   finished certificate cone here is the three kernel axioms + oracle.f.

   STATUS (2026-07-23): the two mathematically-substantive increment
   lemmas are PROVEN and axiom-clean:
     · u32_succ   — the successful u32 index increment (start+1 = ok w).
     · fwd_succ   — the range iterator's `forward_checked start 1` = some w.
   The one open front is `chain_step` (one loop step = one fold step): the
   reduction is fully mechanised EXCEPT the final let-pair exposure. After
   `simp only [… fwd_succ hwok]` the loop-body scrutinee is
     `let (o,iter1) := (some start, {start:=w,end:=stop}); match o with …`
   which neither `simp only` nor `dsimp` iota/zeta-reduces, so
   `rw [match_ok_bind]` cannot see the underlying `bind` yet. NEXT TACTIC:
   force the let-pair with full `simp` (it did reduce it in probing),
   producing `match (do binds; ok (cont y)) with …`, THEN
   `rw [match_ok_bind]; simp only [bind_assoc, bind_ok, hwok]; rfl`. The
   fallback is the WP formulation (`loop.spec_decr_nat` + `spec_mono`, the
   dalek loop-spec pattern), which sidesteps the raw match/bind plumbing.
   Nothing here is claimed proven: this file carries sorries and lives in
   drafts/, never in Proofs/ or check.sh.

   RECORD NOTE: commit a2d8e5f's message body lost one backticked fragment
   to shell command-substitution (it reads "the let-pair  so"); the intended
   text was: the let-pair (o,iter1) := (some start, {start:=w,end:=stop}).
   This header is the authoritative technical record.
-/
import SlhVerify.Funs
open Aeneas Aeneas.Std Result ControlFlow
open fips205

set_option maxHeartbeats 4000000

namespace fips205

/-- The successful u32 increment as a clean equation (no overflow). PROVEN. -/
theorem u32_succ {start : Std.U32} (hb : start.val + 1 < 2 ^ 32) :
    ∃ w : Std.U32, start + 1#u32 = ok w ∧ w.val = start.val + 1 := by
  have he := Std.UScalar.add_equiv start (1#u32)
  cases hc : start + 1#u32 with
  | ok w =>
      refine ⟨w, rfl, ?_⟩
      rw [hc] at he
      have : (1#u32 : Std.U32).val = 1 := by rfl
      omega
  | fail e =>
      exfalso; rw [hc] at he; simp [Std.UScalar.inBounds] at he
      have : (1#u32 : Std.U32).val = 1 := by rfl
      omega
  | div => rw [hc] at he; simp at he

/-- The range iterator's forward step, when start+1 succeeds. PROVEN. -/
theorem fwd_succ {start w : Std.U32} (hw : start + 1#u32 = ok w) :
    U32.Insts.CoreIterRangeStep.forward_checked start 1#usize = ok (some w) := by
  unfold U32.Insts.CoreIterRangeStep.forward_checked
  have h1 : (1#usize : Std.Usize).val < 2 ^ 32 := by decide
  simp only [h1, dif_pos]
  have hone : Std.U32.ofNatCore (1#usize : Std.Usize).val h1 = (1#u32 : Std.U32) := by
    apply Std.UScalar.eq_of_val_eq; rfl
  rw [hone]
  unfold Std.U32.checked_add core.num.checked_add_UScalar Option.ofResult
  rw [hw]

/-- The outer match of `loop.eq_1` IS the Result bind (definitional). PROVEN. -/
theorem match_ok_bind {α β : Type} (m : Result α) (f : α → Result β) :
    (match m with | ok r => f r | fail e => fail e | div => div) = m >>= f := rfl

/-- The mathematical chaining fold, threading the address exactly as the
    extracted body does. See the EFFECT-ORDER NOTE: agreement holds precisely
    under `start.val + s < 2^32`, which makes every intermediate increment
    succeed. -/
noncomputable def chainFoldN {N : Std.Usize} (pk_seed : Slice Std.U8) :
    types.Adrs → Array Std.U8 N → Std.U32 → Nat → Result (Array Std.U8 N)
  | _, tmp, _, 0 => ok tmp
  | adrs, tmp, start, (k+1) => do
      let adrs1 ← helpers.Adrs.set_hash_address adrs start
      let s ← lift (Array.to_slice tmp)
      let tmp1 ← verify_mono.oracle.f N pk_seed adrs1 s
      let start1 ← start + 1#u32
      chainFoldN pk_seed adrs1 tmp1 start1 k

/-- One full loop step on a non-empty range = one fold step, tail as the
    continuation loop. OPEN (see file header — let-pair exposure). -/
theorem chain_step {N : Std.Usize} (pk_seed : Slice Std.U8) (start stop : Std.U32)
    (adrs : types.Adrs) (tmp : Array Std.U8 N)
    (hlt : start.val < stop.val) (hb : start.val + 1 < 2 ^ 32) :
    verify_mono.chain_free_loop { start := start, «end» := stop } pk_seed adrs tmp
      = (do
          let adrs1 ← helpers.Adrs.set_hash_address adrs start
          let s ← lift (Array.to_slice tmp)
          let tmp1 ← verify_mono.oracle.f N pk_seed adrs1 s
          let start1 ← start + 1#u32
          verify_mono.chain_free_loop { start := start1, «end» := stop } pk_seed adrs1 tmp1) := by
  obtain ⟨w, hwok, _⟩ := u32_succ hb
  have hd : decide (start.val < stop.val) = true := by simp [hlt]
  conv_lhs => rw [verify_mono.chain_free_loop, loop.eq_1]
  unfold verify_mono.chain_free_loop.body core.iter.range.IteratorRange.next
  simp only [core.cmp.impls.PartialOrdU32.lt, hd, if_true, bind_tc_ok, bind_ok,
    core.clone.impls.CloneU32.clone, fwd_succ hwok]
  sorry

/-- The loop over [start, start+s) equals the s-step fold. Base case PROVEN;
    succ case reduces to `chain_step` + the IH once `chain_step` closes. -/
theorem chain_free_loop_eq {N : Std.Usize} (pk_seed : Slice Std.U8) (s : Nat) :
    ∀ (start : Std.U32) (adrs : types.Adrs) (tmp : Array Std.U8 N),
      start.val + s < 2 ^ 32 →
      ∀ (stop : Std.U32), stop.val = start.val + s →
      verify_mono.chain_free_loop { start := start, «end» := stop } pk_seed adrs tmp
        = chainFoldN pk_seed adrs tmp start s := by
  induction s with
  | zero =>
    intro start adrs tmp _ stop hstop
    have hse : start = stop := by apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold verify_mono.chain_free_loop chainFoldN
    rw [loop.eq_1]
    unfold verify_mono.chain_free_loop.body core.iter.range.IteratorRange.next
    simp [core.cmp.impls.PartialOrdU32.lt]
  | succ k ih =>
    intro start adrs tmp hb stop hstop
    have hlt : start.val < stop.val := by omega
    have hb1 : start.val + 1 < 2 ^ 32 := by omega
    rw [chain_step pk_seed start stop adrs tmp hlt hb1]
    -- push the fold's step through, then apply ih at (w, stop, k)
    sorry

end fips205
