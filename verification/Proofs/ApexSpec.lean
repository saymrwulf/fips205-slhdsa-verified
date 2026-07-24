/- Proofs/ApexSpec.lean — the APEX certificate.

   THEOREM slh_verify_128s_accepts_iff: the extracted verifier
   `verify_mono::slh_verify_128s` (a private, additive, `#![allow(dead_code)]`
   monomorphic re-expression of the deployed generic verify path — NOT the
   public `pk.verify()`, which it is not called by) returns `ok true` if and
   only if the recomputed hypertree root byte-equals the pinned public-key root
   pk.pk_root. Everything the verifier does after recomputing the root is
   exactly that byte comparison — there is no other acceptance path. The
   recomputation `slhVerifyRoot` is the extracted pipeline (H_msg digest →
   md/idx_tree/idx_leaf split → fors_pk_from_sig → ht recompute over xmss over
   wots over chain). #print axioms = kernel-3 + the five SHA-2 oracles.

   SCOPE — what this does NOT establish (external review round 1, 2026-07-24):
   • This proof is a STRUCTURAL FACTORIZATION, not a composition. It does NOT
     invoke any of the ten loop-fidelity theorems (chain_free_loop_eq, …,
     base2b_outer_loop_eq); it would remain provable if one were deleted. Those
     ten are independent local-fidelity lemmas, not links in this proof chain.
   • NOT "every loop": `base_2b`'s inner accumulation loop is threaded opaquely
     and has no certificate — yet it determines the FORS indices / WOTS digits,
     so a defect there could change the recomputed root while this theorem holds.
   • NOT the deployed public verifier: the bridge from `verify_mono` to the
     generic `pk.verify()` is the finite in-snapshot differential test, not a
     machine-checked refinement.
   • NOT closed-form FIPS 205 correctness: the folds are transliterations of the
     extracted loops with the hash primitives opaque.

   The one real lemma is arrayEqU8_spec: the library array equality
   `PartialEqArray.eq PartialEqU8` on two Array U8 N returns exactly the
   decidable byte-equality of their underlying lists (a List.allM induction).
   Everything else is unfolding the extracted verifier and threading the
   recomputation identically on both sides with bind_congr.
-/
import Proofs.InputPrepSpec
open Aeneas Aeneas.Std Result
open fips205

set_option maxHeartbeats 4000000

namespace fips205

/- ── the array-equality spec ───────────────────────────────────────────────── -/

/-- The `PartialEqU8` instance's `eq` reduces to decidable byte equality (both
    `impls.PartialEqU8.eq` and `liftFun2` are `@[reducible]`). -/
theorem byteEq (a b : Std.U8) :
    (core.cmp.PartialEqU8).eq a b = ok (decide (a = b)) := rfl

/-- allM of the byte-eq predicate over a zip = the decidable list equality,
    when the two lists have equal length. -/
theorem allM_byteEq : ∀ (l1 l2 : List Std.U8), l1.length = l2.length →
    List.allM (fun p : Std.U8 × Std.U8 => (core.cmp.PartialEqU8).eq p.1 p.2) (l1.zip l2)
      = ok (decide (l1 = l2)) := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 h
    cases l2 with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    intro l2 h
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      have hlen : xs.length = ys.length := by simp only [List.length_cons] at h; omega
      simp only [List.zip_cons_cons]
      by_cases hxy : x = y
      · subst hxy
        simp only [List.allM, core.cmp.PartialEqU8, core.cmp.impls.PartialEqU8.eq, liftFun2,
                   decide_true, bind_ok, reduceIte]
        rw [ih ys hlen]; congr 1; simp [List.cons.injEq]
      · have hp : (pure false : Result Bool) = ok false := rfl
        simp [List.allM, core.cmp.impls.PartialEqU8.eq, liftFun2, hxy, List.cons.injEq, hp]

/-- **The library array equality on `Array U8 N` is byte equality.** -/
theorem arrayEqU8_spec {N : Std.Usize} (a b : Array Std.U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b
      = ok (decide (a.val = b.val)) := by
  unfold core.array.equality.PartialEqArray.eq
  have hlen : a.length = b.length := by
    simp only [Array.length, a.property, b.property]
  simp only [hlen, if_true]
  exact allM_byteEq a.val b.val (by simpa only [Array.length] using hlen)

/- ── the composition: factor the final root comparison out of ht_verify ─────── -/

/-- ht_verify_free's recomputation up to (but excluding) the final root
    comparison: the XMSS node then the hypertree layer walk. -/
noncomputable def htVerifyRoot {D HP LEN N : Std.Usize}
    (m : Slice Std.U8) (sig_ht : types.HtSig D HP LEN N) (pk_seed : Slice Std.U8)
    (idx_tree : Std.U64) (idx_leaf : Std.U32) : Result (Array Std.U8 N) := do
  let d32 ← lift (UScalar.cast .U32 D)
  let hp32 ← lift (UScalar.cast .U32 HP)
  let adrs ← types.Adrs.Insts.CoreDefaultDefault.default
  let adrs1 ← helpers.Adrs.set_tree_address adrs idx_tree
  let xs ← Array.index_usize sig_ht.xmss_sigs 0#usize
  let sig_tmp ← types.XmssSig.Insts.CoreCloneClone.clone xs
  let node ← verify_mono.xmss_pk_from_sig_free idx_leaf sig_tmp m pk_seed adrs1
  verify_mono.ht_verify_free_loop { start := 1#u32, «end» := d32 }
    sig_ht.xmss_sigs pk_seed idx_tree hp32 adrs1 node

/-- ht_verify_free = recompute the root, then accept iff it byte-equals pk_root. -/
theorem ht_verify_free_split {D HP LEN N : Std.Usize}
    (m : Slice Std.U8) (sig_ht : types.HtSig D HP LEN N) (pk_seed : Slice Std.U8)
    (idx_tree : Std.U64) (idx_leaf : Std.U32) (pk_root : Array Std.U8 N) :
    verify_mono.ht_verify_free m sig_ht pk_seed idx_tree idx_leaf pk_root
      = (do let node ← htVerifyRoot m sig_ht pk_seed idx_tree idx_leaf
            ok (decide (node.val = pk_root.val))) := by
  unfold verify_mono.ht_verify_free htVerifyRoot
  simp only [bind_assoc]
  apply bind_congr; intro d32
  apply bind_congr; intro hp32
  apply bind_congr; intro adrs
  apply bind_congr; intro adrs1
  apply bind_congr; intro xs
  apply bind_congr; intro sig_tmp
  apply bind_congr; intro node
  apply bind_congr; intro node1
  exact arrayEqU8_spec node1 pk_root

/-- The full SLH-DSA recomputation up to the hypertree root: H_msg digest,
    the md/idx_tree/idx_leaf split, FORS pk, then the hypertree recompute.
    Byte-for-byte the extracted slh_verify_internal_free, with only the final
    ht_verify_free replaced by htVerifyRoot (comparison factored out). -/
noncomputable def slhVerifyRoot {A D HP K LEN N : Std.Usize} (H M : Std.Usize)
    (mprime : Slice Std.U8) (sig : types.SlhDsaSig A D HP K LEN N) (pk : types.SlhPublicKey N) :
    Result (Array Std.U8 N) := do
  let d32 ← lift (UScalar.cast .U32 D)
  let h32 ← lift (UScalar.cast .U32 H)
  let adrs ← types.Adrs.Insts.CoreDefaultDefault.default
  let s ← lift (Array.to_slice sig.randomness)
  let s1 ← lift (Array.to_slice pk.pk_seed)
  let s2 ← lift (Array.to_slice pk.pk_root)
  let digest ← verify_mono.oracle.h_msg M s s1 s2 mprime
  let i ← K * A
  let i1 ← i + 7#usize
  let index1 ← i1 / 8#usize
  let md ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) digest
      { start := 0#usize, «end» := index1 }
  let i2 ← H / D
  let i3 ← H - i2
  let i4 ← i3 + 7#usize
  let i5 ← i4 / 8#usize
  let index2 ← index1 + i5
  let tmp_idx_tree ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) digest
      { start := index1, «end» := index2 }
  let i6 ← 8#usize * D
  let i7 ← H + i6
  let i8 ← i7 - 1#usize
  let i9 ← i8 / i6
  let index3 ← index2 + i9
  let tmp_idx_leaf ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) digest
      { start := index2, «end» := index3 }
  let i10 ← h32 / d32
  let i11 ← h32 - i10
  let i12 ← i11 + 7#u32
  let i13 ← i12 / 8#u32
  let i14 ← helpers.to_int tmp_idx_tree i13
  let i15 ← h32 - i10
  let i16 ← 64#u32 - i15
  let i17 ← core.num.U64.MAX >>> i16
  let idx_tree ← lift (i14 &&& i17)
  let i18 ← 8#u32 * d32
  let i19 ← h32 + i18
  let i20 ← i19 - 1#u32
  let i21 ← i20 / i18
  let i22 ← helpers.to_int tmp_idx_leaf i21
  let i23 ← 64#u32 - i10
  let i24 ← core.num.U64.MAX >>> i23
  let idx_leaf ← lift (i22 &&& i24)
  let adrs1 ← helpers.Adrs.set_tree_address adrs idx_tree
  let adrs2 ← helpers.Adrs.set_type_and_clear adrs1 types.FORS_TREE
  let idx_leaf_u32 ← lift (UScalar.cast .U32 idx_leaf)
  let adrs3 ← helpers.Adrs.set_key_pair_address adrs2 idx_leaf_u32
  let s3 ← lift (Array.to_slice pk.pk_seed)
  let pk_fors ← verify_mono.fors_pk_from_sig_free sig.fors_sig md s3 adrs3
  let s4 ← lift (Array.to_slice pk_fors.key)
  let s5 ← lift (Array.to_slice pk.pk_seed)
  htVerifyRoot s4 sig.ht_sig s5 idx_tree idx_leaf_u32

/-- **APEX (generic).** slh_verify_internal_free returns `ok true` iff the
    recomputed hypertree root byte-equals the pinned public-key root — there is
    no acceptance path other than root equality. -/
theorem slh_verify_internal_accepts_iff {A D HP K LEN N : Std.Usize} (H M : Std.Usize)
    (mprime : Slice Std.U8) (sig : types.SlhDsaSig A D HP K LEN N) (pk : types.SlhPublicKey N) :
    verify_mono.slh_verify_internal_free H M mprime sig pk
      = (do let root ← slhVerifyRoot H M mprime sig pk
            ok (decide (root.val = pk.pk_root.val))) := by
  unfold verify_mono.slh_verify_internal_free slhVerifyRoot
  -- rewriting ht_verify_free's tail into (recompute >>= compare) and flattening
  -- makes both sides the identical do-block; simp closes it structurally
  -- (no whnf of the nested ht_verify_free_loop — the ForsOuter lesson).
  simp only [ht_verify_free_split, bind_assoc]

/-- **APEX (SHA2-128s facade entry).** The extracted `verify_mono::slh_verify_128s`
    accepts iff the recomputed root byte-equals pk.pk_root. Acceptance
    characterization only — see the file header for the four explicit
    non-claims (this is a structural factorization, NOT a composition of the
    ten loop certs; NOT the deployed public verifier; base_2b inner uncertified;
    NOT closed-form FIPS-205 correctness). -/
theorem slh_verify_128s_accepts_iff
    (mprime : Slice Std.U8)
    (sig : types.SlhDsaSig 12#usize 7#usize 9#usize 14#usize 35#usize 16#usize)
    (pk : types.SlhPublicKey 16#usize) :
    verify_mono.slh_verify_128s mprime sig pk
      = (do let root ← slhVerifyRoot 63#usize 30#usize mprime sig pk
            ok (decide (root.val = pk.pk_root.val))) := by
  unfold verify_mono.slh_verify_128s
  exact slh_verify_internal_accepts_iff 63#usize 30#usize mprime sig pk

end fips205
