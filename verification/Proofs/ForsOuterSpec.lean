/- Proofs/ForsOuterSpec.lean — FORS outer per-tree loop (Algorithm 17).

   THEOREM fors_outer_loop_eq: the extracted outer loop
   (fors_pk_from_sig_free_loop0) equals the explicit K-tree fold — for each
   tree i, compute the leaf with F at tree index (i << a) + indices[i], run
   the inner Merkle loop over the A levels, and write the result to root[i].
   Straight-line body (like HtSpec) that consumes the inner loop
   (fors_pk_from_sig_free_loop0_loop0) as an opaque sub-call — its own
   fidelity is fors_inner_loop_eq in ForsInnerSpec. Cone: kernel three +
   verify_mono.oracle.{f, h} (F for each leaf; H reached transitively through
   the referenced inner loop).

   Split from the inner loop (ForsInnerSpec) so each file stays under the
   memory ceiling (METHOD-4 file split). Reuses u32_succ / fwd_succ / hnext /
   loop_unfold_bind from ChainSpec.
-/
import Proofs.ChainSpec
open Aeneas Aeneas.Std Result ControlFlow
open fips205

set_option maxHeartbeats 4000000

namespace fips205

/-- Outer loop body on a non-empty range, resolved to the successor w. -/
theorem hbody_fo {A K N : Std.Usize} (sig_fors : types.ForsSig A K N) (pk_seed : Slice Std.U8)
    (a32 : Std.U32) (indices : Array Std.U32 K) (start stop w : Std.U32)
    (adrs : types.Adrs) (root : Array (Array Std.U8 N) K)
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#u32 = ok w) :
    verify_mono.fors_pk_from_sig_free_loop0.body sig_fors pk_seed a32 indices
        { start := start, «end» := stop } adrs root
      = (do
          let i1 ← lift (UScalar.cast .Usize start)
          let sk ← Array.index_usize sig_fors.private_key_value i1
          let adrs1 ← helpers.Adrs.set_tree_height adrs 0#u32
          let i2 ← start <<< a32
          let i3 ← lift (UScalar.cast .Usize start)
          let i4 ← Array.index_usize indices i3
          let i5 ← i2 + i4
          let adrs2 ← helpers.Adrs.set_tree_index adrs1 i5
          let s ← lift (Array.to_slice sk)
          let node_0 ← verify_mono.oracle.f N pk_seed adrs2 s
          let i6 ← lift (UScalar.cast .Usize start)
          let a ← Array.index_usize sig_fors.auth i6
          let auth ← types.Auth.Insts.CoreCloneClone.clone a
          let (adrs3, node_01) ←
            verify_mono.fors_pk_from_sig_free_loop0_loop0
              { start := 0#u32, «end» := a32 } pk_seed adrs2 indices start node_0 auth
          let i7 ← lift (UScalar.cast .Usize start)
          let a1 ← Array.update root i7 node_01
          ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.U32), adrs3, a1))) := by
  unfold verify_mono.fors_pk_from_sig_free_loop0.body
  rw [hnext hd hwok]
  simp

/-- The outer per-tree fold: at tree i, F-leaf then the inner Merkle loop,
    writing root[i]. The inner loop is consumed as an opaque sub-call. -/
noncomputable def forsOuterFold {A K N : Std.Usize} (sig_fors : types.ForsSig A K N)
    (pk_seed : Slice Std.U8) (a32 : Std.U32) (indices : Array Std.U32 K) :
    types.Adrs → Array (Array Std.U8 N) K → Std.U32 → Nat →
      Result (types.Adrs × Array (Array Std.U8 N) K)
  | adrs, root, _, 0 => ok (adrs, root)
  | adrs, root, i, (s+1) => do
      let i1 ← lift (UScalar.cast .Usize i)
      let sk ← Array.index_usize sig_fors.private_key_value i1
      let adrs1 ← helpers.Adrs.set_tree_height adrs 0#u32
      let i2 ← i <<< a32
      let i3 ← lift (UScalar.cast .Usize i)
      let i4 ← Array.index_usize indices i3
      let i5 ← i2 + i4
      let adrs2 ← helpers.Adrs.set_tree_index adrs1 i5
      let s0 ← lift (Array.to_slice sk)
      let node_0 ← verify_mono.oracle.f N pk_seed adrs2 s0
      let i6 ← lift (UScalar.cast .Usize i)
      let a ← Array.index_usize sig_fors.auth i6
      let auth ← types.Auth.Insts.CoreCloneClone.clone a
      let (adrs3, node_01) ←
        verify_mono.fors_pk_from_sig_free_loop0_loop0
          { start := 0#u32, «end» := a32 } pk_seed adrs2 indices i node_0 auth
      let i7 ← lift (UScalar.cast .Usize i)
      let a1 ← Array.update root i7 node_01
      let w ← i + 1#u32
      forsOuterFold sig_fors pk_seed a32 indices adrs3 a1 w s

/-- One outer loop step = one fold step (straight-line body). -/
theorem fors_outer_step {A K N : Std.Usize} (sig_fors : types.ForsSig A K N) (pk_seed : Slice Std.U8)
    (a32 : Std.U32) (indices : Array Std.U32 K) (start stop : Std.U32)
    (adrs : types.Adrs) (root : Array (Array Std.U8 N) K)
    (hlt : start.val < stop.val) (hb : start.val + 1 < 2 ^ 32) :
    verify_mono.fors_pk_from_sig_free_loop0 { start := start, «end» := stop }
        sig_fors pk_seed a32 adrs indices root
      = (do
          let i1 ← lift (UScalar.cast .Usize start)
          let sk ← Array.index_usize sig_fors.private_key_value i1
          let adrs1 ← helpers.Adrs.set_tree_height adrs 0#u32
          let i2 ← start <<< a32
          let i3 ← lift (UScalar.cast .Usize start)
          let i4 ← Array.index_usize indices i3
          let i5 ← i2 + i4
          let adrs2 ← helpers.Adrs.set_tree_index adrs1 i5
          let s ← lift (Array.to_slice sk)
          let node_0 ← verify_mono.oracle.f N pk_seed adrs2 s
          let i6 ← lift (UScalar.cast .Usize start)
          let a ← Array.index_usize sig_fors.auth i6
          let auth ← types.Auth.Insts.CoreCloneClone.clone a
          let (adrs3, node_01) ←
            verify_mono.fors_pk_from_sig_free_loop0_loop0
              { start := 0#u32, «end» := a32 } pk_seed adrs2 indices start node_0 auth
          let i7 ← lift (UScalar.cast .Usize start)
          let a1 ← Array.update root i7 node_01
          let w ← start + 1#u32
          verify_mono.fors_pk_from_sig_free_loop0 { start := w, «end» := stop }
            sig_fors pk_seed a32 adrs3 indices a1) := by
  obtain ⟨w, hwok, _⟩ := u32_succ hb
  have hd : decide (start.val < stop.val) = true := by simp [hlt]
  conv_lhs => rw [verify_mono.fors_pk_from_sig_free_loop0, loop_unfold_bind]
  dsimp only
  rw [hbody_fo sig_fors pk_seed a32 indices start stop w adrs root hd hwok]
  simp only [bind_assoc, bind_ok]
  conv_rhs => rw [show (start + 1#u32) = ok w from hwok]
  simp only [bind_tc_ok, bind_ok]
  -- Peel all 16 binds with bind_congr so the closing `rfl` only whnf's the
  -- small loop-tail, not the whole body threading the inner `loop` term
  -- (a bare `rfl` here blows the 4M-heartbeat whnf budget — the HtSpec body had
  -- no nested loop, so its rfl was cheap; the FORS outer body does).
  apply bind_congr; intro i1
  apply bind_congr; intro sk
  apply bind_congr; intro adrs1
  apply bind_congr; intro i2
  apply bind_congr; intro i3
  apply bind_congr; intro i4
  apply bind_congr; intro i5
  apply bind_congr; intro adrs2
  apply bind_congr; intro s0
  apply bind_congr; intro node_0
  apply bind_congr; intro i6
  apply bind_congr; intro a
  apply bind_congr; intro auth
  apply bind_congr; rintro ⟨adrs3, node_01⟩
  -- the pair `let` blocks further bind_congr (won't iota via simp only); the
  -- remaining tail (i7, a1, loop recursion) is small, so a full simp closes it
  -- cheaply — no whnf over the body, so no heartbeat blowup
  simp [bind_assoc, bind_ok, verify_mono.fors_pk_from_sig_free_loop0]

/-- **Algorithm 17 outer fidelity.** The extracted per-tree loop over
    [start, start+s) equals the explicit K-tree fold. -/
theorem fors_outer_loop_eq {A K N : Std.Usize} (sig_fors : types.ForsSig A K N)
    (pk_seed : Slice Std.U8) (a32 : Std.U32) (indices : Array Std.U32 K) (s : Nat) :
    ∀ (start : Std.U32) (adrs : types.Adrs) (root : Array (Array Std.U8 N) K),
      start.val + s < 2 ^ 32 →
      ∀ (stop : Std.U32), stop.val = start.val + s →
      verify_mono.fors_pk_from_sig_free_loop0 { start := start, «end» := stop }
          sig_fors pk_seed a32 adrs indices root
        = forsOuterFold sig_fors pk_seed a32 indices adrs root start s := by
  induction s with
  | zero =>
    intro start adrs root _ stop hstop
    have hse : start = stop := by apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold verify_mono.fors_pk_from_sig_free_loop0 forsOuterFold
    rw [loop.eq_1]
    unfold verify_mono.fors_pk_from_sig_free_loop0.body core.iter.range.IteratorRange.next
    simp [core.cmp.impls.PartialOrdU32.lt]
  | succ k ih =>
    intro start adrs root hb stop hstop
    have hlt : start.val < stop.val := by omega
    have hb1 : start.val + 1 < 2 ^ 32 := by omega
    obtain ⟨w, hwok, hwv⟩ := u32_succ hb1
    rw [fors_outer_step sig_fors pk_seed a32 indices start stop adrs root hlt hb1]
    unfold forsOuterFold
    rw [hwok]
    simp only [bind_tc_ok, bind_ok]
    have hbound : w.val + k < 2 ^ 32 := by omega
    have hstop' : stop.val = w.val + k := by omega
    apply bind_congr; intro i1
    apply bind_congr; intro sk
    apply bind_congr; intro adrs1
    apply bind_congr; intro i2
    apply bind_congr; intro i3
    apply bind_congr; intro i4
    apply bind_congr; intro i5
    apply bind_congr; intro adrs2
    apply bind_congr; intro s0
    apply bind_congr; intro node_0
    apply bind_congr; intro i6
    apply bind_congr; intro a
    apply bind_congr; intro auth
    apply bind_congr; rintro ⟨adrs3, node_01⟩
    apply bind_congr; intro i7
    apply bind_congr; intro a1
    exact ih w adrs3 a1 hbound stop hstop'

end fips205
