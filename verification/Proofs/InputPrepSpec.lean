/- Proofs/InputPrepSpec.lean — input-preparation loop fidelity (FIPS 205
   helpers: to_int, to_byte, and the WOTS+ checksum loop).

   Three straight-line range-loop fidelity theorems, all KERNEL-3 CLEAN (pure
   byte/bit arithmetic — no hash oracle enters these). They pin the message-
   and index-preparation steps that feed the verify path:

   - to_int_loop_eq (Algorithm 2, toInt): the extracted big-endian byte→u64
     accumulation loop equals the explicit fold total ← (total≪8) + x[i].
   - to_byte_loop_eq (Algorithm 3, toByte): the extracted u32→byte loop equals
     the explicit fold writing s[n−1−i] and shifting total right by 8.
   - wots_csum_loop_eq: the WOTS+ checksum accumulation csum ← csum + (W−1−msg[i]).

   All three are the HtSpec straight-line recipe (no branches): hbody →
   step lemma (rfl close) → induction (bind_congr per bind, exact ih). to_int
   and the checksum use the usize range (usize_succ/fwd_succ_usize/hnext_usize
   from WotsSpec); to_byte uses the u32 range (u32_succ/fwd_succ/hnext from
   ChainSpec). loop_unfold_bind reused throughout.

   These are the last non-apex layer: after de-plumbing round 2 (to_int/base_2b
   index loops) the model carries NO plumbing axioms on the verify path.
-/
import Proofs.WotsSpec  -- transitively imports ChainSpec (u32 range helpers too)
open Aeneas Aeneas.Std Result ControlFlow
open fips205

set_option maxHeartbeats 4000000

namespace fips205

/- ── to_int (Algorithm 2): big-endian n-byte → u64 ─────────────────────────── -/

theorem hbody_ti (x : Slice Std.U8) (start stop w : Std.Usize) (total : Std.U64)
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#usize = ok w) :
    helpers.to_int_loop.body x { start := start, «end» := stop } total
      = (do
          let i1 ← total <<< 8#i32
          let i2 ← Slice.index_usize x start
          let i3 ← lift (core.convert.num.FromU64U8.from i2)
          let total1 ← i1 + i3
          ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.Usize), total1))) := by
  unfold helpers.to_int_loop.body
  rw [hnext_usize hd hwok]
  simp

noncomputable def toIntFold (x : Slice Std.U8) :
    Std.U64 → Std.Usize → Nat → Result Std.U64
  | total, _, 0 => ok total
  | total, i, (s+1) => do
      let i1 ← total <<< 8#i32
      let i2 ← Slice.index_usize x i
      let i3 ← lift (core.convert.num.FromU64U8.from i2)
      let total1 ← i1 + i3
      let i' ← i + 1#usize
      toIntFold x total1 i' s

theorem to_int_step (x : Slice Std.U8) (start stop : Std.Usize) (total : Std.U64)
    (hlt : start.val < stop.val) (hb : start.val + 1 < 2 ^ System.Platform.numBits) :
    helpers.to_int_loop { start := start, «end» := stop } x total
      = (do
          let i1 ← total <<< 8#i32
          let i2 ← Slice.index_usize x start
          let i3 ← lift (core.convert.num.FromU64U8.from i2)
          let total1 ← i1 + i3
          let i' ← start + 1#usize
          helpers.to_int_loop { start := i', «end» := stop } x total1) := by
  obtain ⟨w, hwok, _⟩ := usize_succ hb
  have hd : decide (start.val < stop.val) = true := by simp [hlt]
  conv_lhs => rw [helpers.to_int_loop, loop_unfold_bind]
  dsimp only
  rw [hbody_ti x start stop w total hd hwok]
  simp only [bind_assoc, bind_ok]
  conv_rhs => rw [show (start + 1#usize) = ok w from hwok]
  simp only [bind_tc_ok, bind_ok]
  rfl

/-- **Algorithm 2 (toInt) fidelity.** -/
theorem to_int_loop_eq (x : Slice Std.U8) (s : Nat) :
    ∀ (start : Std.Usize) (total : Std.U64),
      start.val + s < 2 ^ System.Platform.numBits →
      ∀ (stop : Std.Usize), stop.val = start.val + s →
      helpers.to_int_loop { start := start, «end» := stop } x total
        = toIntFold x total start s := by
  induction s with
  | zero =>
    intro start total _ stop hstop
    have hse : start = stop := by apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold helpers.to_int_loop toIntFold
    rw [loop.eq_1]
    unfold helpers.to_int_loop.body core.iter.range.IteratorRange.next
    simp [core.iter.range.StepUsize, core.cmp.impls.PartialOrdUsize.lt]
  | succ k ih =>
    intro start total hb stop hstop
    have hlt : start.val < stop.val := by omega
    have hb1 : start.val + 1 < 2 ^ System.Platform.numBits := by scalar_tac
    obtain ⟨w, hwok, hwv⟩ := usize_succ hb1
    rw [to_int_step x start stop total hlt hb1]
    unfold toIntFold
    rw [hwok]
    simp only [bind_tc_ok, bind_ok]
    have hbound : w.val + k < 2 ^ System.Platform.numBits := by scalar_tac
    have hstop' : stop.val = w.val + k := by omega
    apply bind_congr; intro i1
    apply bind_congr; intro i2
    apply bind_congr; intro i3
    apply bind_congr; intro total1
    exact ih w total1 hbound stop hstop'

/- ── to_byte (Algorithm 3): u32 → n big-endian bytes ───────────────────────── -/

theorem hbody_tb (n : Std.U32) (start stop w : Std.U32)
    (s : Array Std.U8 2#usize) (total : Std.U32)
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#u32 = ok w) :
    helpers.to_byte_loop.body n { start := start, «end» := stop } s total
      = (do
          let a ← lift (core.num.U32.to_le_bytes total)
          let i1 ← Array.index_usize a 0#usize
          let i2 ← n - 1#u32
          let i3 ← i2 - start
          let i4 ← lift (UScalar.cast .Usize i3)
          let a1 ← Array.update s i4 i1
          let total1 ← total >>> 8#i32
          ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.U32), a1, total1))) := by
  unfold helpers.to_byte_loop.body
  rw [hnext hd hwok]
  simp

noncomputable def toByteFold (n : Std.U32) :
    Array Std.U8 2#usize → Std.U32 → Std.U32 → Nat → Result (Array Std.U8 2#usize)
  | s, _, _, 0 => ok s
  | s, total, i, (k+1) => do
      let a ← lift (core.num.U32.to_le_bytes total)
      let i1 ← Array.index_usize a 0#usize
      let i2 ← n - 1#u32
      let i3 ← i2 - i
      let i4 ← lift (UScalar.cast .Usize i3)
      let a1 ← Array.update s i4 i1
      let total1 ← total >>> 8#i32
      let i' ← i + 1#u32
      toByteFold n a1 total1 i' k

theorem to_byte_step (n : Std.U32) (start stop : Std.U32)
    (s : Array Std.U8 2#usize) (total : Std.U32)
    (hlt : start.val < stop.val) (hb : start.val + 1 < 2 ^ 32) :
    helpers.to_byte_loop { start := start, «end» := stop } n s total
      = (do
          let a ← lift (core.num.U32.to_le_bytes total)
          let i1 ← Array.index_usize a 0#usize
          let i2 ← n - 1#u32
          let i3 ← i2 - start
          let i4 ← lift (UScalar.cast .Usize i3)
          let a1 ← Array.update s i4 i1
          let total1 ← total >>> 8#i32
          let i' ← start + 1#u32
          helpers.to_byte_loop { start := i', «end» := stop } n a1 total1) := by
  obtain ⟨w, hwok, _⟩ := u32_succ hb
  have hd : decide (start.val < stop.val) = true := by simp [hlt]
  conv_lhs => rw [helpers.to_byte_loop, loop_unfold_bind]
  dsimp only
  rw [hbody_tb n start stop w s total hd hwok]
  simp only [bind_assoc, bind_ok]
  conv_rhs => rw [show (start + 1#u32) = ok w from hwok]
  simp only [bind_tc_ok, bind_ok]
  rfl

/-- **Algorithm 3 (toByte) fidelity.** -/
theorem to_byte_loop_eq (n : Std.U32) (k : Nat) :
    ∀ (start : Std.U32) (s : Array Std.U8 2#usize) (total : Std.U32),
      start.val + k < 2 ^ 32 →
      ∀ (stop : Std.U32), stop.val = start.val + k →
      helpers.to_byte_loop { start := start, «end» := stop } n s total
        = toByteFold n s total start k := by
  induction k with
  | zero =>
    intro start s total _ stop hstop
    have hse : start = stop := by apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold helpers.to_byte_loop toByteFold
    rw [loop.eq_1]
    unfold helpers.to_byte_loop.body core.iter.range.IteratorRange.next
    simp [core.cmp.impls.PartialOrdU32.lt]
  | succ k ih =>
    intro start s total hb stop hstop
    have hlt : start.val < stop.val := by omega
    have hb1 : start.val + 1 < 2 ^ 32 := by omega
    obtain ⟨w, hwok, hwv⟩ := u32_succ hb1
    rw [to_byte_step n start stop s total hlt hb1]
    unfold toByteFold
    rw [hwok]
    simp only [bind_tc_ok, bind_ok]
    have hbound : w.val + k < 2 ^ 32 := by omega
    have hstop' : stop.val = w.val + k := by omega
    apply bind_congr; intro a
    apply bind_congr; intro i1
    apply bind_congr; intro i2
    apply bind_congr; intro i3
    apply bind_congr; intro i4
    apply bind_congr; intro a1
    apply bind_congr; intro total1
    exact ih w a1 total1 hbound stop hstop'

/- ── WOTS+ checksum accumulation ───────────────────────────────────────────── -/

theorem hbody_cs {LEN : Std.Usize} (msg : Array Std.U32 LEN)
    (start stop w : Std.Usize) (csum : Std.U32)
    (hd : decide (start.val < stop.val) = true) (hwok : start + 1#usize = ok w) :
    verify_mono.wots_pk_from_sig_free_loop0.body msg { start := start, «end» := stop } csum
      = (do
          let i1 ← W - 1#u32
          let i2 ← Array.index_usize msg start
          let i3 ← i1 - i2
          let csum1 ← csum + i3
          ok (cont (({ start := w, «end» := stop } : core.ops.range.Range Std.Usize), csum1))) := by
  unfold verify_mono.wots_pk_from_sig_free_loop0.body
  rw [hnext_usize hd hwok]
  simp

noncomputable def wotsCsumFold {LEN : Std.Usize} (msg : Array Std.U32 LEN) :
    Std.U32 → Std.Usize → Nat → Result Std.U32
  | csum, _, 0 => ok csum
  | csum, i, (s+1) => do
      let i1 ← W - 1#u32
      let i2 ← Array.index_usize msg i
      let i3 ← i1 - i2
      let csum1 ← csum + i3
      let i' ← i + 1#usize
      wotsCsumFold msg csum1 i' s

theorem wots_csum_step {LEN : Std.Usize} (msg : Array Std.U32 LEN)
    (start stop : Std.Usize) (csum : Std.U32)
    (hlt : start.val < stop.val) (hb : start.val + 1 < 2 ^ System.Platform.numBits) :
    verify_mono.wots_pk_from_sig_free_loop0 { start := start, «end» := stop } csum msg
      = (do
          let i1 ← W - 1#u32
          let i2 ← Array.index_usize msg start
          let i3 ← i1 - i2
          let csum1 ← csum + i3
          let i' ← start + 1#usize
          verify_mono.wots_pk_from_sig_free_loop0 { start := i', «end» := stop } csum1 msg) := by
  obtain ⟨w, hwok, _⟩ := usize_succ hb
  have hd : decide (start.val < stop.val) = true := by simp [hlt]
  conv_lhs => rw [verify_mono.wots_pk_from_sig_free_loop0, loop_unfold_bind]
  dsimp only
  rw [hbody_cs msg start stop w csum hd hwok]
  simp only [bind_assoc, bind_ok]
  conv_rhs => rw [show (start + 1#usize) = ok w from hwok]
  simp only [bind_tc_ok, bind_ok]
  rfl

/-- **WOTS+ checksum-loop fidelity.** -/
theorem wots_csum_loop_eq {LEN : Std.Usize} (msg : Array Std.U32 LEN) (s : Nat) :
    ∀ (start : Std.Usize) (csum : Std.U32),
      start.val + s < 2 ^ System.Platform.numBits →
      ∀ (stop : Std.Usize), stop.val = start.val + s →
      verify_mono.wots_pk_from_sig_free_loop0 { start := start, «end» := stop } csum msg
        = wotsCsumFold msg csum start s := by
  induction s with
  | zero =>
    intro start csum _ stop hstop
    have hse : start = stop := by apply Std.UScalar.eq_of_val_eq; omega
    subst hse
    unfold verify_mono.wots_pk_from_sig_free_loop0 wotsCsumFold
    rw [loop.eq_1]
    unfold verify_mono.wots_pk_from_sig_free_loop0.body core.iter.range.IteratorRange.next
    simp [core.iter.range.StepUsize, core.cmp.impls.PartialOrdUsize.lt]
  | succ k ih =>
    intro start csum hb stop hstop
    have hlt : start.val < stop.val := by omega
    have hb1 : start.val + 1 < 2 ^ System.Platform.numBits := by scalar_tac
    obtain ⟨w, hwok, hwv⟩ := usize_succ hb1
    rw [wots_csum_step msg start stop csum hlt hb1]
    unfold wotsCsumFold
    rw [hwok]
    simp only [bind_tc_ok, bind_ok]
    have hbound : w.val + k < 2 ^ System.Platform.numBits := by scalar_tac
    have hstop' : stop.val = w.val + k := by omega
    apply bind_congr; intro i1
    apply bind_congr; intro i2
    apply bind_congr; intro i3
    apply bind_congr; intro csum1
    exact ih w csum1 hbound stop hstop'

end fips205
