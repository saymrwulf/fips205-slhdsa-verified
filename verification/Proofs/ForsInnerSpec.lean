/- Proofs/ForsInnerSpec.lean — FORS inner Merkle authentication-path loop
   (Algorithm 17, one FORS tree).

   THEOREM fors_inner_loop_eq: the extracted inner loop
   (fors_pk_from_sig_free_loop0_loop0) equals the explicit auth-path fold for
   one FORS tree — at level j set the tree height to j+1, test bit j of the
   tree's leaf index indices[i], and hash the current node with auth.tree[j]
   in the bit-dictated order (even: node ∥ auth[j]; odd: auth[j] ∥ node),
   halving the tree index. Structurally the XMSS auth-path loop (XmssSpec),
   but the bit source is indices[i] >> j and the loop returns the (adrs, node)
   pair. Cone: kernel three + verify_mono.oracle.h.

   Split from the outer per-tree loop (ForsOuterSpec) so each file stays under
   the memory ceiling (METHOD-4 file split). Reuses u32_succ / fwd_succ /
   hnext / loop_unfold_bind from ChainSpec.
-/
import Proofs.ChainSpec
open Aeneas Aeneas.Std Result ControlFlow
open fips205

set_option maxHeartbeats 4000000

namespace fips205

/-- Inner loop body on a non-empty range, resolved to the successor w. -/
theorem hbody_fi {A K N : Std.Usize} (pk_seed : Slice Std.U8) (indices : Array Std.U32 K)
    (i : Std.U32) (auth : types.Auth A N) (start stop w : Std.U32)
    (adrs : types.Adrs) (node : Array Std.U8 N)
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#u32 = ok w) :
    verify_mono.fors_pk_from_sig_free_loop0_loop0.body pk_seed indices i auth
        { start := start, «end» := stop } adrs node
      = (do
          let adrs1 ← helpers.Adrs.set_tree_height adrs w
          let i2 ← lift (UScalar.cast .Usize i)
          let i3 ← Array.index_usize indices i2
          let i4 ← i3 >>> start
          let i5 ← lift (i4 &&& 1#u32)
          if i5 = 0#u32
          then
            let (i6, adrs2) ← helpers.Adrs.get_tree_index adrs1
            let tmp ← i6 / 2#u32
            let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
            let s0 ← lift (Array.to_slice node)
            let i7 ← lift (UScalar.cast .Usize start)
            let a ← Array.index_usize auth.tree i7
            let s1 ← lift (Array.to_slice a)
            let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
            ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.U32), adrs3, node1))
          else
            let (i6, adrs2) ← helpers.Adrs.get_tree_index adrs1
            let i7 ← i6 - 1#u32
            let tmp ← i7 / 2#u32
            let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
            let i8 ← lift (UScalar.cast .Usize start)
            let a ← Array.index_usize auth.tree i8
            let s0 ← lift (Array.to_slice a)
            let s1 ← lift (Array.to_slice node)
            let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
            ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.U32), adrs3, node1))) := by
  unfold verify_mono.fors_pk_from_sig_free_loop0_loop0.body
  rw [hnext hd hwok]
  simp [hwok]

/-- The inner Merkle-path fold for one FORS tree. -/
noncomputable def forsInnerFold {A K N : Std.Usize} (pk_seed : Slice Std.U8)
    (indices : Array Std.U32 K) (i : Std.U32) (auth : types.Auth A N) :
    types.Adrs → Array Std.U8 N → Std.U32 → Nat → Result (types.Adrs × Array Std.U8 N)
  | adrs, node, _, 0 => ok (adrs, node)
  | adrs, node, lvl, (s+1) => do
      let w ← lvl + 1#u32
      let adrs1 ← helpers.Adrs.set_tree_height adrs w
      let i2 ← lift (UScalar.cast .Usize i)
      let i3 ← Array.index_usize indices i2
      let i4 ← i3 >>> lvl
      let i5 ← lift (i4 &&& 1#u32)
      if i5 = 0#u32
      then
        let (i6, adrs2) ← helpers.Adrs.get_tree_index adrs1
        let tmp ← i6 / 2#u32
        let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
        let s0 ← lift (Array.to_slice node)
        let i7 ← lift (UScalar.cast .Usize lvl)
        let a ← Array.index_usize auth.tree i7
        let s1 ← lift (Array.to_slice a)
        let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
        forsInnerFold pk_seed indices i auth adrs3 node1 w s
      else
        let (i6, adrs2) ← helpers.Adrs.get_tree_index adrs1
        let i7 ← i6 - 1#u32
        let tmp ← i7 / 2#u32
        let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
        let i8 ← lift (UScalar.cast .Usize lvl)
        let a ← Array.index_usize auth.tree i8
        let s0 ← lift (Array.to_slice a)
        let s1 ← lift (Array.to_slice node)
        let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
        forsInnerFold pk_seed indices i auth adrs3 node1 w s

/-- One inner loop step = one fold step (both branches). -/
theorem fors_inner_step {A K N : Std.Usize} (pk_seed : Slice Std.U8) (indices : Array Std.U32 K)
    (i : Std.U32) (auth : types.Auth A N) (start stop : Std.U32)
    (adrs : types.Adrs) (node : Array Std.U8 N)
    (hlt : start.val < stop.val) (hb : start.val + 1 < 2 ^ 32) :
    verify_mono.fors_pk_from_sig_free_loop0_loop0 { start := start, «end» := stop }
        pk_seed adrs indices i node auth
      = (do
          let w ← start + 1#u32
          let adrs1 ← helpers.Adrs.set_tree_height adrs w
          let i2 ← lift (UScalar.cast .Usize i)
          let i3 ← Array.index_usize indices i2
          let i4 ← i3 >>> start
          let i5 ← lift (i4 &&& 1#u32)
          if i5 = 0#u32
          then
            let (i6, adrs2) ← helpers.Adrs.get_tree_index adrs1
            let tmp ← i6 / 2#u32
            let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
            let s0 ← lift (Array.to_slice node)
            let i7 ← lift (UScalar.cast .Usize start)
            let a ← Array.index_usize auth.tree i7
            let s1 ← lift (Array.to_slice a)
            let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
            verify_mono.fors_pk_from_sig_free_loop0_loop0 { start := w, «end» := stop }
              pk_seed adrs3 indices i node1 auth
          else
            let (i6, adrs2) ← helpers.Adrs.get_tree_index adrs1
            let i7 ← i6 - 1#u32
            let tmp ← i7 / 2#u32
            let adrs3 ← helpers.Adrs.set_tree_index adrs2 tmp
            let i8 ← lift (UScalar.cast .Usize start)
            let a ← Array.index_usize auth.tree i8
            let s0 ← lift (Array.to_slice a)
            let s1 ← lift (Array.to_slice node)
            let node1 ← verify_mono.oracle.h N pk_seed adrs3 s0 s1
            verify_mono.fors_pk_from_sig_free_loop0_loop0 { start := w, «end» := stop }
              pk_seed adrs3 indices i node1 auth) := by
  obtain ⟨w, hwok, _⟩ := u32_succ hb
  have hd : decide (start.val < stop.val) = true := by simp [hlt]
  conv_lhs => rw [verify_mono.fors_pk_from_sig_free_loop0_loop0, loop_unfold_bind]
  dsimp only
  rw [hbody_fi pk_seed indices i auth start stop w adrs node hd hwok]
  simp only [bind_assoc, bind_ok]
  conv_rhs => rw [show (start + 1#u32) = ok w from hwok]
  simp only [bind_tc_ok, bind_ok]
  apply bind_congr; intro adrs1
  apply bind_congr; intro i2
  apply bind_congr; intro i3
  apply bind_congr; intro i4
  apply bind_congr; intro i5
  by_cases hc : i5 = 0#u32
  · rw [if_pos hc, if_pos hc]
    simp only [bind_assoc, bind_ok]
    apply bind_congr; rintro ⟨i6, adrs2⟩
    simp [bind_assoc, bind_ok, verify_mono.fors_pk_from_sig_free_loop0_loop0]
  · rw [if_neg hc, if_neg hc]
    simp only [bind_assoc, bind_ok]
    apply bind_congr; rintro ⟨i6, adrs2⟩
    simp [bind_assoc, bind_ok, verify_mono.fors_pk_from_sig_free_loop0_loop0]

/-- **Algorithm 17 inner fidelity.** The extracted inner Merkle loop over
    [start, start+s) equals the explicit auth-path fold for one FORS tree. -/
theorem fors_inner_loop_eq {A K N : Std.Usize} (pk_seed : Slice Std.U8) (indices : Array Std.U32 K)
    (i : Std.U32) (auth : types.Auth A N) (s : Nat) :
    ∀ (start : Std.U32) (adrs : types.Adrs) (node : Array Std.U8 N),
      start.val + s < 2 ^ 32 →
      ∀ (stop : Std.U32), stop.val = start.val + s →
      verify_mono.fors_pk_from_sig_free_loop0_loop0 { start := start, «end» := stop }
          pk_seed adrs indices i node auth
        = forsInnerFold pk_seed indices i auth adrs node start s := by
  induction s with
  | zero =>
    intro start adrs node _ stop hstop
    have hse : start = stop := by apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold verify_mono.fors_pk_from_sig_free_loop0_loop0 forsInnerFold
    rw [loop.eq_1]
    unfold verify_mono.fors_pk_from_sig_free_loop0_loop0.body core.iter.range.IteratorRange.next
    simp [core.cmp.impls.PartialOrdU32.lt]
  | succ k ih =>
    intro start adrs node hb stop hstop
    have hlt : start.val < stop.val := by omega
    have hb1 : start.val + 1 < 2 ^ 32 := by omega
    obtain ⟨w, hwok, hwv⟩ := u32_succ hb1
    rw [fors_inner_step pk_seed indices i auth start stop adrs node hlt hb1]
    unfold forsInnerFold
    rw [hwok]
    simp only [bind_tc_ok, bind_ok]
    have hbound : w.val + k < 2 ^ 32 := by omega
    have hstop' : stop.val = w.val + k := by omega
    apply bind_congr; intro adrs1
    apply bind_congr; intro i2
    apply bind_congr; intro i3
    apply bind_congr; intro i4
    apply bind_congr; intro i5
    by_cases hc : i5 = 0#u32
    · rw [if_pos hc, if_pos hc]
      apply bind_congr; rintro ⟨i6, adrs2⟩
      apply bind_congr; intro tmp
      apply bind_congr; intro adrs3
      apply bind_congr; intro s0
      apply bind_congr; intro i7
      apply bind_congr; intro a
      apply bind_congr; intro s1
      apply bind_congr; intro node1
      exact ih w adrs3 node1 hbound stop hstop'
    · rw [if_neg hc, if_neg hc]
      apply bind_congr; rintro ⟨i6, adrs2⟩
      apply bind_congr; intro i7
      apply bind_congr; intro tmp
      apply bind_congr; intro adrs3
      apply bind_congr; intro i8
      apply bind_congr; intro a
      apply bind_congr; intro s0
      apply bind_congr; intro s1
      apply bind_congr; intro node1
      exact ih w adrs3 node1 hbound stop hstop'

end fips205
