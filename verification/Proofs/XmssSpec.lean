/- Proofs/XmssSpec.lean — XMSS public-key-from-signature (Algorithm 10), the
   authentication-path Merkle loop.

   THEOREM xmss_loop_eq: the extracted auth-path loop
   (xmss_pk_from_sig_free_loop) equals the explicit fold that, at step k,
   sets the tree height to k+1, tests bit k of the leaf index, and on an even
   bit halves the tree index and hashes H(node ∥ auth[k]), on an odd bit sets
   the tree index to (i−1)/2 and hashes H(auth[k] ∥ node) — the FIPS 205
   Merkle-path recomputation. This is the layer above WOTS+: it pins the
   hash ORDER (the even/odd sibling rule), the tree-height/tree-index address
   schedule, and the auth-path indexing. H stays opaque
   (verify_mono.oracle.h), so the certificate cone is the three kernel axioms
   + oracle.h, audited by check.sh Phase 3.

   The proof is the chain/wots recipe on a u32 range (u32_succ / fwd_succ /
   hnext and loop_unfold_bind reused VERBATIM from ChainSpec), with one new
   feature: the loop body branches on the index bit, so the step lemma and
   the induction split with by_cases + if_pos/if_neg and thread the IH under
   the opaque binds of BOTH branches with bind_congr. The get_tree_index
   pair-bind destructures with rintro; differing pair matchers are
   definitionally bridged by structure eta.
-/
import Proofs.ChainSpec
open Aeneas Aeneas.Std Result ControlFlow
open fips205

set_option maxHeartbeats 4000000

namespace fips205

/-- The loop body on a non-empty range, as a clean do-block: the iterator is
    resolved (hnext) and both occurrences of start+1 — the iterator's forward
    step and the body's tree-height argument — are the same successor w. -/
theorem hbody_x {HP N : Std.Usize} (idx : Std.U32) (pk_seed : Slice Std.U8)
    (auth : Array (Array Std.U8 N) HP) (start stop w : Std.U32)
    (adrs : types.Adrs) (node : Array Std.U8 N)
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#u32 = ok w) :
    verify_mono.xmss_pk_from_sig_free_loop.body idx pk_seed auth
        { start := start, «end» := stop } adrs node
      = (do
          let adrs1 ← helpers.Adrs.set_tree_height adrs w
          let i1 ← idx >>> start
          let i2 ← lift (i1 &&& 1#u32)
          if i2 = 0#u32
          then
            let (i3, adrs2) ← helpers.Adrs.get_tree_index adrs1
            let tmp ← i3 / 2#u32
            let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
            let s0 ← lift (Array.to_slice node)
            let i4 ← lift (UScalar.cast .Usize start)
            let a ← Array.index_usize auth i4
            let s1 ← lift (Array.to_slice a)
            let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
            ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.U32), adrs3, node1))
          else
            let (i3, adrs2) ← helpers.Adrs.get_tree_index adrs1
            let i4 ← i3 - 1#u32
            let tmp ← i4 / 2#u32
            let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
            let i5 ← lift (UScalar.cast .Usize start)
            let a ← Array.index_usize auth i5
            let s0 ← lift (Array.to_slice a)
            let s1 ← lift (Array.to_slice node)
            let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
            ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.U32), adrs3, node1))) := by
  unfold verify_mono.xmss_pk_from_sig_free_loop.body
  rw [hnext hd hwok]
  simp [hwok]

/-- The mathematical Merkle-path fold: at step k set the tree height to k+1,
    test bit k of idx, and hash the current node with auth[k] in the order
    the bit dictates, halving the tree index. Recursion on the step count;
    the successor and the fallible scalar ops stay monadic, mirroring the
    extracted code exactly. -/
noncomputable def xmssFoldN {HP N : Std.Usize} (idx : Std.U32)
    (pk_seed : Slice Std.U8) (auth : Array (Array Std.U8 N) HP) :
    types.Adrs → Array Std.U8 N → Std.U32 → Nat → Result (Array Std.U8 N)
  | _, node, _, 0 => ok node
  | adrs, node, k, (s+1) => do
      let w ← k + 1#u32
      let adrs1 ← helpers.Adrs.set_tree_height adrs w
      let i1 ← idx >>> k
      let i2 ← lift (i1 &&& 1#u32)
      if i2 = 0#u32
      then
        let (i3, adrs2) ← helpers.Adrs.get_tree_index adrs1
        let tmp ← i3 / 2#u32
        let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
        let s0 ← lift (Array.to_slice node)
        let i4 ← lift (UScalar.cast .Usize k)
        let a ← Array.index_usize auth i4
        let s1 ← lift (Array.to_slice a)
        let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
        xmssFoldN idx pk_seed auth adrs3 node1 w s
      else
        let (i3, adrs2) ← helpers.Adrs.get_tree_index adrs1
        let i4 ← i3 - 1#u32
        let tmp ← i4 / 2#u32
        let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
        let i5 ← lift (UScalar.cast .Usize k)
        let a ← Array.index_usize auth i5
        let s0 ← lift (Array.to_slice a)
        let s1 ← lift (Array.to_slice node)
        let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
        xmssFoldN idx pk_seed auth adrs3 node1 w s

/-- One full loop step on a non-empty range = one fold step, tail as the
    continuation loop — in BOTH branches of the index-bit test. -/
theorem xmss_loop_step {HP N : Std.Usize} (idx : Std.U32) (pk_seed : Slice Std.U8)
    (auth : Array (Array Std.U8 N) HP) (start stop : Std.U32)
    (adrs : types.Adrs) (node : Array Std.U8 N)
    (hlt : start.val < stop.val) (hb : start.val + 1 < 2 ^ 32) :
    verify_mono.xmss_pk_from_sig_free_loop { start := start, «end» := stop }
        idx pk_seed adrs auth node
      = (do
          let w ← start + 1#u32
          let adrs1 ← helpers.Adrs.set_tree_height adrs w
          let i1 ← idx >>> start
          let i2 ← lift (i1 &&& 1#u32)
          if i2 = 0#u32
          then
            let (i3, adrs2) ← helpers.Adrs.get_tree_index adrs1
            let tmp ← i3 / 2#u32
            let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
            let s0 ← lift (Array.to_slice node)
            let i4 ← lift (UScalar.cast .Usize start)
            let a ← Array.index_usize auth i4
            let s1 ← lift (Array.to_slice a)
            let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
            verify_mono.xmss_pk_from_sig_free_loop { start := w, «end» := stop }
              idx pk_seed adrs3 auth node1
          else
            let (i3, adrs2) ← helpers.Adrs.get_tree_index adrs1
            let i4 ← i3 - 1#u32
            let tmp ← i4 / 2#u32
            let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
            let i5 ← lift (UScalar.cast .Usize start)
            let a ← Array.index_usize auth i5
            let s0 ← lift (Array.to_slice a)
            let s1 ← lift (Array.to_slice node)
            let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
            verify_mono.xmss_pk_from_sig_free_loop { start := w, «end» := stop }
              idx pk_seed adrs3 auth node1) := by
  obtain ⟨w, hwok, _⟩ := u32_succ hb
  have hd : decide (start.val < stop.val) = true := by simp [hlt]
  conv_lhs => rw [verify_mono.xmss_pk_from_sig_free_loop, loop_unfold_bind]
  dsimp only
  rw [hbody_x idx pk_seed auth start stop w adrs node hd hwok]
  simp only [bind_assoc, bind_ok]
  conv_rhs => rw [show (start + 1#u32) = ok w from hwok]
  simp only [bind_tc_ok, bind_ok]
  apply bind_congr; intro adrs1
  apply bind_congr; intro i1
  apply bind_congr; intro i2
  by_cases hc : i2 = 0#u32
  -- Per branch: expose the pair-bind (assoc), make the scrutinee concrete
  -- (bind_congr + rintro), then FULL simp: only full simp iota-reduces the
  -- pair matcher (the chain lesson); with assoc, ok-bind, and the loop def
  -- both sides normalize to the same right-nested chain.
  · rw [if_pos hc, if_pos hc]
    simp only [bind_assoc, bind_ok]
    apply bind_congr; rintro ⟨i3, adrs2⟩
    simp [bind_assoc, bind_ok, verify_mono.xmss_pk_from_sig_free_loop]
  · rw [if_neg hc, if_neg hc]
    simp only [bind_assoc, bind_ok]
    apply bind_congr; rintro ⟨i3, adrs2⟩
    simp [bind_assoc, bind_ok, verify_mono.xmss_pk_from_sig_free_loop]

/-- **Algorithm 10 fidelity.** The extracted XMSS auth-path loop over
    [start, start+s) equals the explicit Merkle-path fold. -/
theorem xmss_loop_eq {HP N : Std.Usize} (idx : Std.U32) (pk_seed : Slice Std.U8)
    (auth : Array (Array Std.U8 N) HP) (s : Nat) :
    ∀ (start : Std.U32) (adrs : types.Adrs) (node : Array Std.U8 N),
      start.val + s < 2 ^ 32 →
      ∀ (stop : Std.U32), stop.val = start.val + s →
      verify_mono.xmss_pk_from_sig_free_loop { start := start, «end» := stop }
          idx pk_seed adrs auth node
        = xmssFoldN idx pk_seed auth adrs node start s := by
  induction s with
  | zero =>
    intro start adrs node _ stop hstop
    have hse : start = stop := by apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold verify_mono.xmss_pk_from_sig_free_loop xmssFoldN
    rw [loop.eq_1]
    unfold verify_mono.xmss_pk_from_sig_free_loop.body core.iter.range.IteratorRange.next
    simp [core.cmp.impls.PartialOrdU32.lt]
  | succ k ih =>
    intro start adrs node hb stop hstop
    have hlt : start.val < stop.val := by omega
    have hb1 : start.val + 1 < 2 ^ 32 := by omega
    obtain ⟨w, hwok, hwv⟩ := u32_succ hb1
    rw [xmss_loop_step idx pk_seed auth start stop adrs node hlt hb1]
    unfold xmssFoldN
    rw [hwok]
    simp only [bind_tc_ok, bind_ok]
    have hbound : w.val + k < 2 ^ 32 := by omega
    have hstop' : stop.val = w.val + k := by omega
    apply bind_congr; intro adrs1
    apply bind_congr; intro i1
    apply bind_congr; intro i2
    by_cases hc : i2 = 0#u32
    · rw [if_pos hc, if_pos hc]
      apply bind_congr; rintro ⟨i3, adrs2⟩
      apply bind_congr; intro tmp
      apply bind_congr; intro adrs3
      apply bind_congr; intro s0
      apply bind_congr; intro i4
      apply bind_congr; intro a
      apply bind_congr; intro s1
      apply bind_congr; intro node1
      exact ih w adrs3 node1 hbound stop hstop'
    · rw [if_neg hc, if_neg hc]
      apply bind_congr; rintro ⟨i3, adrs2⟩
      apply bind_congr; intro i4
      apply bind_congr; intro tmp
      apply bind_congr; intro adrs3
      apply bind_congr; intro i5
      apply bind_congr; intro a
      apply bind_congr; intro s0
      apply bind_congr; intro s1
      apply bind_congr; intro node1
      exact ih w adrs3 node1 hbound stop hstop'

end fips205
