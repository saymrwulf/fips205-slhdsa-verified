/- Proofs/ChainSpec.lean — Algorithm 5 (chain / WOTS+ chaining) fidelity.

   THEOREM chain_free_loop_eq: the extracted `chain_free` loop equals the
   explicit s-fold application of the hash F, with the hash-address set to
   i, i+1, …, i+s−1 in turn. This rules out — machine-checked, for the
   monomorphic SHA2-128s `verify_mono` path (a private facade, not the
   deployed generic verifier) — an off-by-one loop bound and wrong state
   threading. It does NOT rule out a wrong ADRS field: `chainFoldN` calls the
   same extracted `set_hash_address` the loop does, so a wrong field would be
   copied into the fold and the theorem would still hold — the field is made
   VISIBLE in the certificate (a transliteration), not excluded by it. F stays
   opaque (verify_mono.oracle.f), so the certificate cone is the three kernel
   axioms + oracle.f, and nothing else (audited by check.sh Phase 3).

   The proof: an induction on the step count. `chain_step` is one loop step =
   one fold step, proven by unfolding the Aeneas `loop` fixpoint one turn
   (loop_unfold_bind), reducing the range iterator to a clean equation
   (fips205_hnext) and the loop body to a clean do-block (fips205_hbody), and
   aligning the monadic u32 index increment (u32_succ / fwd_succ) with the
   fold's. The succ case threads the IH under the opaque binds with
   bind_congr.
-/
import SlhVerify.Funs
open Aeneas Aeneas.Std Result ControlFlow
open fips205

set_option maxHeartbeats 4000000

namespace fips205

/-- The successful u32 increment as a clean equation (no overflow). -/
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

/-- The range iterator's forward step, when start+1 succeeds. -/
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

/-- The Aeneas `loop` fixpoint, unfolded one turn into a bind. The `casesOn`
    continuation matches loop's own reduction, so it closes by cases+rfl
    (a hand-written `match` would compile to a different, non-defeq matcher). -/
theorem loop_unfold_bind {α β : Type} (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = body x >>= (fun r => ControlFlow.casesOn r (fun c => loop body c) (fun d => ok d)) := by
  conv_lhs => rw [loop.eq_1]
  cases body x with
  | ok cf => cases cf <;> rfl
  | fail e => rfl
  | div => rfl

/-- The range iterator step on a non-empty range, as a clean equation. -/
theorem hnext {start stop w : Std.U32}
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#u32 = ok w) :
    core.iter.range.IteratorRange.next U32.Insts.CoreIterRangeStep
        { start := start, «end» := stop }
      = ok (some start, { start := w, «end» := stop }) := by
  unfold core.iter.range.IteratorRange.next
  simp only [core.cmp.impls.PartialOrdU32.lt, hd, decide_true, if_true,
    bind_tc_ok, bind_ok, core.clone.impls.CloneU32.clone, fwd_succ hwok]

/-- The loop body on a non-empty range reduces to a clean do-block. -/
theorem hbody {N : Std.Usize} (pk_seed : Slice Std.U8) (start stop w : Std.U32)
    (adrs : types.Adrs) (tmp : Array Std.U8 N)
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#u32 = ok w) :
    verify_mono.chain_free_loop.body pk_seed { start := start, «end» := stop } adrs tmp
      = (do
          let adrs1 ← helpers.Adrs.set_hash_address adrs start
          let s ← lift (Array.to_slice tmp)
          let tmp1 ← verify_mono.oracle.f N pk_seed adrs1 s
          ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.U32), adrs1, tmp1))) := by
  unfold verify_mono.chain_free_loop.body
  rw [hnext hd hwok]
  simp

/-- The mathematical chaining fold: at each step set the hash address to the
    current index, hash, advance the index (monadically, matching the u32
    range iterator). Recursion on the step count. Agreement with the extracted
    loop holds under `start.val + s < 2^32`, which makes every increment
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
    continuation loop. -/
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
  conv_lhs => rw [verify_mono.chain_free_loop, loop_unfold_bind]
  dsimp only
  rw [hbody pk_seed start stop w adrs tmp hd hwok]
  simp only [bind_assoc, bind_ok]
  conv_rhs => rw [show (start + 1#u32) = ok w from hwok]
  simp only [bind_tc_ok, bind_ok]
  rfl

/-- **Algorithm 5 fidelity.** The extracted chain loop over [start, start+s)
    equals the explicit s-fold hash-chain. -/
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
    obtain ⟨w, hwok, hwv⟩ := u32_succ hb1
    rw [chain_step pk_seed start stop adrs tmp hlt hb1]
    unfold chainFoldN
    rw [hwok]
    simp only [bind_tc_ok, bind_ok]
    have hbound : w.val + k < 2 ^ 32 := by omega
    have hstop' : stop.val = w.val + k := by omega
    apply bind_congr; intro adrs1
    apply bind_congr; intro s
    apply bind_congr; intro tmp1
    exact ih w adrs1 tmp1 hbound stop hstop'

end fips205
