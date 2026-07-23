/- Proofs/HtSpec.lean — hypertree verification (Algorithm 12), the layer walk.

   THEOREM ht_loop_eq: the extracted hypertree loop (ht_verify_free_loop)
   equals the explicit d-layer fold that, at layer j, splits the tree index
   (idx_leaf = idx_tree mod 2^h' via mask+cast, then idx_tree >>= h'), sets
   the layer address to j and the tree address to the shifted index, and
   recomputes the node through xmss_pk_from_sig on the j-th XMSS signature.
   This pins the LAYER SCHEDULE of FIPS 205 hypertree verification: the
   mask-then-shift index split, the layer/tree-address order, the signature
   indexing, and the node threading. The final node = pk_root comparison
   lives one bind above, in ht_verify_free — the apex composition's job.

   HISTORY: the first extraction of this loop carried Result-conversion
   plumbing (try_from / is_err / unwrap and, transitively through the
   xmss/wots defs, a Take iterator and a &u32 Sub instance) — all AXIOMS,
   which the Phase-3 audit rightly rejected. The fips205-source de-plumbing
   patch (8 sites, semantics identical for every FIPS 205 parameter set,
   re-validated by the in-snapshot differential test) replaced them with
   real-definition constructs; after re-extraction the loop body is
   straight-line and this proof is the plain chain/wots recipe on a u32
   range — u32_succ / fwd_succ / hnext / loop_unfold_bind reused VERBATIM
   from ChainSpec, no branches, no side conditions beyond the range bound.
-/
import Proofs.ChainSpec
open Aeneas Aeneas.Std Result ControlFlow
open fips205

set_option maxHeartbeats 4000000

namespace fips205

/-- The loop body on a non-empty range, as a clean do-block (iterator
    resolved to the successor w). -/
theorem hbody_ht {D HP LEN N : Std.Usize} (a : Array (types.XmssSig HP LEN N) D)
    (pk_seed : Slice Std.U8) (hp32 : Std.U32)
    (start stop w : Std.U32) (idx_tree : Std.U64) (adrs : types.Adrs)
    (node : Array Std.U8 N)
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#u32 = ok w) :
    verify_mono.ht_verify_free_loop.body a pk_seed hp32
        { start := start, «end» := stop } idx_tree adrs node
      = (do
          let i ← 1#u64 <<< hp32
          let i1 ← i - 1#u64
          let i2 ← lift (idx_tree &&& i1)
          let idx_leaf ← lift (UScalar.cast .U32 i2)
          let idx_tree1 ← idx_tree >>> hp32
          let adrs1 ← helpers.Adrs.set_layer_address adrs start
          let adrs2 ← helpers.Adrs.set_tree_address adrs1 idx_tree1
          let i3 ← lift (UScalar.cast .Usize start)
          let xs ← Array.index_usize a i3
          let sig_tmp ← types.XmssSig.Insts.CoreCloneClone.clone xs
          let s0 ← lift (Array.to_slice node)
          let node1 ← verify_mono.xmss_pk_from_sig_free idx_leaf sig_tmp s0 pk_seed adrs2
          ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.U32),
                    idx_tree1, adrs2, node1))) := by
  unfold verify_mono.ht_verify_free_loop.body
  rw [hnext hd hwok]
  simp

/-- The mathematical hypertree fold: at layer j split the index, set the
    layer/tree addresses, recompute the node through xmss_pk_from_sig on
    signature j. All fallible scalar ops stay monadic, mirroring the
    extracted code exactly. -/
noncomputable def htFoldN {D HP LEN N : Std.Usize}
    (a : Array (types.XmssSig HP LEN N) D) (pk_seed : Slice Std.U8)
    (hp32 : Std.U32) :
    Std.U64 → types.Adrs → Array Std.U8 N → Std.U32 → Nat →
      Result (Array Std.U8 N)
  | _, _, node, _, 0 => ok node
  | idx_tree, adrs, node, j, (s+1) => do
      let i ← 1#u64 <<< hp32
      let i1 ← i - 1#u64
      let i2 ← lift (idx_tree &&& i1)
      let idx_leaf ← lift (UScalar.cast .U32 i2)
      let idx_tree1 ← idx_tree >>> hp32
      let adrs1 ← helpers.Adrs.set_layer_address adrs j
      let adrs2 ← helpers.Adrs.set_tree_address adrs1 idx_tree1
      let i3 ← lift (UScalar.cast .Usize j)
      let xs ← Array.index_usize a i3
      let sig_tmp ← types.XmssSig.Insts.CoreCloneClone.clone xs
      let s0 ← lift (Array.to_slice node)
      let node1 ← verify_mono.xmss_pk_from_sig_free idx_leaf sig_tmp s0 pk_seed adrs2
      let w ← j + 1#u32
      htFoldN a pk_seed hp32 idx_tree1 adrs2 node1 w s

/-- One full loop step on a non-empty range = one fold step, tail as the
    continuation loop. -/
theorem ht_loop_step {D HP LEN N : Std.Usize} (a : Array (types.XmssSig HP LEN N) D)
    (pk_seed : Slice Std.U8) (hp32 : Std.U32)
    (start stop : Std.U32) (idx_tree : Std.U64) (adrs : types.Adrs)
    (node : Array Std.U8 N)
    (hlt : start.val < stop.val) (hb : start.val + 1 < 2 ^ 32) :
    verify_mono.ht_verify_free_loop { start := start, «end» := stop }
        a pk_seed idx_tree hp32 adrs node
      = (do
          let i ← 1#u64 <<< hp32
          let i1 ← i - 1#u64
          let i2 ← lift (idx_tree &&& i1)
          let idx_leaf ← lift (UScalar.cast .U32 i2)
          let idx_tree1 ← idx_tree >>> hp32
          let adrs1 ← helpers.Adrs.set_layer_address adrs start
          let adrs2 ← helpers.Adrs.set_tree_address adrs1 idx_tree1
          let i3 ← lift (UScalar.cast .Usize start)
          let xs ← Array.index_usize a i3
          let sig_tmp ← types.XmssSig.Insts.CoreCloneClone.clone xs
          let s0 ← lift (Array.to_slice node)
          let node1 ← verify_mono.xmss_pk_from_sig_free idx_leaf sig_tmp s0 pk_seed adrs2
          let w ← start + 1#u32
          verify_mono.ht_verify_free_loop { start := w, «end» := stop }
            a pk_seed idx_tree1 hp32 adrs2 node1) := by
  obtain ⟨w, hwok, _⟩ := u32_succ hb
  have hd : decide (start.val < stop.val) = true := by simp [hlt]
  conv_lhs => rw [verify_mono.ht_verify_free_loop, loop_unfold_bind]
  dsimp only
  rw [hbody_ht a pk_seed hp32 start stop w idx_tree adrs node hd hwok]
  simp only [bind_assoc, bind_ok]
  conv_rhs => rw [show (start + 1#u32) = ok w from hwok]
  simp only [bind_tc_ok, bind_ok]
  rfl

/-- **Algorithm 12 fidelity.** The extracted hypertree loop over
    [start, start+s) equals the explicit layer fold. -/
theorem ht_loop_eq {D HP LEN N : Std.Usize} (a : Array (types.XmssSig HP LEN N) D)
    (pk_seed : Slice Std.U8) (hp32 : Std.U32) (s : Nat) :
    ∀ (start : Std.U32) (idx_tree : Std.U64) (adrs : types.Adrs) (node : Array Std.U8 N),
      start.val + s < 2 ^ 32 →
      ∀ (stop : Std.U32), stop.val = start.val + s →
      verify_mono.ht_verify_free_loop { start := start, «end» := stop }
          a pk_seed idx_tree hp32 adrs node
        = htFoldN a pk_seed hp32 idx_tree adrs node start s := by
  induction s with
  | zero =>
    intro start idx_tree adrs node _ stop hstop
    have hse : start = stop := by apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold verify_mono.ht_verify_free_loop htFoldN
    rw [loop.eq_1]
    unfold verify_mono.ht_verify_free_loop.body core.iter.range.IteratorRange.next
    simp [core.cmp.impls.PartialOrdU32.lt]
  | succ k ih =>
    intro start idx_tree adrs node hb stop hstop
    have hlt : start.val < stop.val := by omega
    have hb1 : start.val + 1 < 2 ^ 32 := by omega
    obtain ⟨w, hwok, hwv⟩ := u32_succ hb1
    rw [ht_loop_step a pk_seed hp32 start stop idx_tree adrs node hlt hb1]
    unfold htFoldN
    rw [hwok]
    simp only [bind_tc_ok, bind_ok]
    have hbound : w.val + k < 2 ^ 32 := by omega
    have hstop' : stop.val = w.val + k := by omega
    apply bind_congr; intro i
    apply bind_congr; intro i1
    apply bind_congr; intro i2
    apply bind_congr; intro idx_leaf
    apply bind_congr; intro idx_tree1
    apply bind_congr; intro adrs1
    apply bind_congr; intro adrs2
    apply bind_congr; intro i3
    apply bind_congr; intro xs
    apply bind_congr; intro sig_tmp
    apply bind_congr; intro s0
    apply bind_congr; intro node1
    exact ih w idx_tree1 adrs2 node1 hbound stop hstop'

end fips205
