/- Proofs/WotsSpec.lean — WOTS+ public-key recomputation (Algorithm 8), the
   chain loop.

   THEOREM wots_loop1_eq: the extracted WOTS+ chain loop
   (wots_pk_from_sig_free_loop1) equals the explicit fold that, at each index
   i in [0, LEN), sets the chain address to i and runs `chain_free` on
   sig[i] starting at digit msg[i] for W−1−msg[i] steps, updating tmp[i].
   This is the layer above chain: it consumes `chain_free` and pins that the
   LEN chains are run with the RIGHT start indices, step counts, and slots —
   the WOTS+ verification recomputation. Cone stays the three kernel axioms +
   the single hash oracle (chain's F).

   The proof mirrors ChainSpec exactly: usize increment (usize_succ /
   fwd_succ_usize), the StepUsize iterator step (hnext_usize), the loop body
   as a clean do-block (hbody1), one loop step = one fold step
   (wots_loop1_step), and the induction (wots_loop1_eq) threading the IH under
   the opaque binds with bind_congr. It reuses the generic loop_unfold_bind
   from ChainSpec.
-/
import Proofs.ChainSpec
open Aeneas Aeneas.Std Result ControlFlow
open fips205

set_option maxHeartbeats 4000000

namespace fips205

theorem usize_succ {start : Std.Usize} (hb : start.val + 1 < 2 ^ System.Platform.numBits) :
    ∃ w : Std.Usize, start + 1#usize = ok w ∧ w.val = start.val + 1 := by
  have he := Std.UScalar.add_equiv start (1#usize)
  cases hc : start + 1#usize with
  | ok w =>
      refine ⟨w, rfl, ?_⟩
      rw [hc] at he
      have : (1#usize : Std.Usize).val = 1 := by rfl
      omega
  | fail e =>
      exfalso; rw [hc] at he; simp [Std.UScalar.inBounds] at he
      have : (1#usize : Std.Usize).val = 1 := by rfl
      omega
  | div => rw [hc] at he; simp at he

-- StepUsize forward step, when start+1 succeeds.
theorem fwd_succ_usize {start w : Std.Usize} (hw : start + 1#usize = ok w) :
    core.iter.range.StepUsize.forward_checked start 1#usize = ok (some w) := by
  unfold core.iter.range.StepUsize.forward_checked Std.Usize.checked_add core.num.checked_add_UScalar Option.ofResult
  rw [hw]

-- the usize range iterator step on a non-empty range.
theorem hnext_usize {start stop w : Std.Usize}
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#usize = ok w) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := start, «end» := stop }
      = ok (some start, { start := w, «end» := stop }) := by
  unfold core.iter.range.IteratorRange.next
  simp only [core.iter.range.StepUsize, core.cmp.impls.PartialOrdUsize.lt, hd, decide_true,
    if_true, bind_tc_ok, bind_ok, core.clone.impls.CloneUsize.clone, fwd_succ_usize hwok]

theorem hbody1 {LEN N : Std.Usize} (sig : types.WotsSig LEN N) (pk_seed : Slice Std.U8)
    (msg : Array Std.U32 LEN) (start stop w : Std.Usize) (adrs : types.Adrs)
    (tmp : Array (Array Std.U8 N) LEN)
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#usize = ok w) :
    verify_mono.wots_pk_from_sig_free_loop1.body sig pk_seed msg
        { start := start, «end» := stop } adrs tmp
      = (do
          let i1 ← lift (Std.UScalar.cast .U32 start)
          let adrs1 ← helpers.Adrs.set_chain_address adrs i1
          let a ← Array.index_usize sig.data start
          let i2 ← Array.index_usize msg start
          let i3 ← W - 1#u32
          let i4 ← i3 - i2
          let a1 ← verify_mono.chain_free a i2 i4 pk_seed adrs1
          let a2 ← Array.update tmp start a1
          ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.Usize), adrs1, a2))) := by
  unfold verify_mono.wots_pk_from_sig_free_loop1.body
  rw [hnext_usize hd hwok]
  simp

noncomputable def wotsChainFold {LEN N : Std.Usize} (sig : types.WotsSig LEN N)
    (pk_seed : Slice Std.U8) (msg : Array Std.U32 LEN) :
    types.Adrs → Array (Array Std.U8 N) LEN → Std.Usize → Nat →
      Result (types.Adrs × Array (Array Std.U8 N) LEN)
  | adrs, tmp, _, 0 => ok (adrs, tmp)
  | adrs, tmp, i, (k+1) => do
      let i1 ← lift (Std.UScalar.cast .U32 i)
      let adrs1 ← helpers.Adrs.set_chain_address adrs i1
      let a ← Array.index_usize sig.data i
      let i2 ← Array.index_usize msg i
      let i3 ← W - 1#u32
      let i4 ← i3 - i2
      let a1 ← verify_mono.chain_free a i2 i4 pk_seed adrs1
      let a2 ← Array.update tmp i a1
      let i' ← i + 1#usize
      wotsChainFold sig pk_seed msg adrs1 a2 i' k

theorem wots_loop1_step {LEN N : Std.Usize} (sig : types.WotsSig LEN N)
    (pk_seed : Slice Std.U8) (msg : Array Std.U32 LEN) (start stop : Std.Usize)
    (adrs : types.Adrs) (tmp : Array (Array Std.U8 N) LEN)
    (hlt : start.val < stop.val) (hb : start.val + 1 < 2 ^ System.Platform.numBits) :
    verify_mono.wots_pk_from_sig_free_loop1 { start := start, «end» := stop } sig pk_seed adrs tmp msg
      = (do
          let i1 ← lift (Std.UScalar.cast .U32 start)
          let adrs1 ← helpers.Adrs.set_chain_address adrs i1
          let a ← Array.index_usize sig.data start
          let i2 ← Array.index_usize msg start
          let i3 ← W - 1#u32
          let i4 ← i3 - i2
          let a1 ← verify_mono.chain_free a i2 i4 pk_seed adrs1
          let a2 ← Array.update tmp start a1
          let i' ← start + 1#usize
          verify_mono.wots_pk_from_sig_free_loop1 { start := i', «end» := stop } sig pk_seed adrs1 a2 msg) := by
  obtain ⟨w, hwok, _⟩ := usize_succ hb
  have hd : decide (start.val < stop.val) = true := by simp [hlt]
  conv_lhs => rw [verify_mono.wots_pk_from_sig_free_loop1, loop_unfold_bind]
  dsimp only
  rw [hbody1 sig pk_seed msg start stop w adrs tmp hd hwok]
  simp only [bind_assoc, bind_ok]
  conv_rhs => rw [show (start + 1#usize) = ok w from hwok]
  simp only [bind_tc_ok, bind_ok]
  rfl

theorem wots_loop1_eq {LEN N : Std.Usize} (sig : types.WotsSig LEN N)
    (pk_seed : Slice Std.U8) (msg : Array Std.U32 LEN) (s : Nat) :
    ∀ (start : Std.Usize) (adrs : types.Adrs) (tmp : Array (Array Std.U8 N) LEN),
      start.val + s < 2 ^ System.Platform.numBits →
      ∀ (stop : Std.Usize), stop.val = start.val + s →
      verify_mono.wots_pk_from_sig_free_loop1 { start := start, «end» := stop } sig pk_seed adrs tmp msg
        = wotsChainFold sig pk_seed msg adrs tmp start s := by
  induction s with
  | zero =>
    intro start adrs tmp _ stop hstop
    have hse : start = stop := by apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold verify_mono.wots_pk_from_sig_free_loop1 wotsChainFold
    rw [loop.eq_1]
    unfold verify_mono.wots_pk_from_sig_free_loop1.body core.iter.range.IteratorRange.next
    simp [core.iter.range.StepUsize, core.cmp.impls.PartialOrdUsize.lt]
  | succ k ih =>
    intro start adrs tmp hb stop hstop
    have hlt : start.val < stop.val := by omega
    have hb1 : start.val + 1 < 2 ^ System.Platform.numBits := by scalar_tac
    obtain ⟨w, hwok, hwv⟩ := usize_succ hb1
    rw [wots_loop1_step sig pk_seed msg start stop adrs tmp hlt hb1]
    unfold wotsChainFold
    rw [hwok]
    simp only [bind_tc_ok, bind_ok]
    have hbound : w.val + k < 2 ^ System.Platform.numBits := by scalar_tac
    have hstop' : stop.val = w.val + k := by omega
    apply bind_congr; intro i1
    apply bind_congr; intro adrs1
    apply bind_congr; intro a
    apply bind_congr; intro i2
    apply bind_congr; intro i3
    apply bind_congr; intro i4
    apply bind_congr; intro a1
    apply bind_congr; intro a2
    exact ih w adrs1 a2 hbound stop hstop'

end fips205
