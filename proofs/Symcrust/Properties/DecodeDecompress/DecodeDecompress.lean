import Symcrust.Code
import Symcrust.Properties.DecodeDecompress.Decompress
import Symcrust.Properties.Basic

open Aeneas
open Std
open Result

/-!
This file contains theorems about `Symcrust.Spec.decompress` and `Symcrust.Spec.byteDecode` defined in
Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to (4.8) (Decompress) and Algorithm 6 (ByteDecode).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.decompress` and `Symcrust.Spec.byteDecode`.
    - `Lean spec (functional)` corresponds to `Symcrust.Spec.compress` and `Target.byteDecode`.
      - `Lean spec (monadic)` and `Lean spec (functional)` coincide for Decompress because the natural
        Lean translation of Nist's Decompress is already functional.
    - `Auxiliary spec` corresponds to `Symcrust.SpecAux.decompress` and `Stream.decode`.
      - Additionally, `Auxiliary spec` for the combination of decode and decompress that appears in the Rust
        code corresponds to `Stream.decode_decompressOpt`.
    - `Aeneas translation` corresponds to `Symcrust.ntt.poly_element_decode_and_decompress`.
    - `⟷₃` is bundled together with `⟷₂` in the form of `decompress_eq` and `Stream.decode.spec`.
    - `⟷₄` corresponds to `Symcrust.SpecAux.poly_element_decode_and_decompress.spec`.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Result Symcrust.ntt

attribute [-progress] UScalar.cast.progress_spec U32.sub_spec
attribute [local progress] UScalar.cast_inBounds_spec U32.sub_bv_spec

set_option maxHeartbeats 2000000

lemma mod_two_pow (x y d : ℕ) (hxy : x = y) : x % 2 ^ d = y &&& ((1 <<< d) - 1) := by
  rw [hxy]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, Bool.and_comm]

lemma List.flatMap_eq_map {α β} (l : List α) (f : α → β) : l.flatMap (fun x => [f x]) = l.map f := by
  induction l <;> simp_all

theorem decode_coefficient.early_load_progress_spec (b : Slice U8) (d : U32) (f : Std.Array U16 256#usize)
  (num_bytes_read : Usize) (acc n_bits_in_accumulator : U32) (i : Usize)
  (hinv : SpecAux.Stream.decode.length_inv (↑d) 4 ↑num_bytes_read ↑n_bits_in_accumulator ↑i)
  (hb1 : ∀ i < 256,
    ∑ (a : Fin d), (Bool.toNat (b[(d.val * i + a) / 8]!.val.testBit ((d * i + a) % 8))) * 2^a.val < Spec.m d)
  (hb2 : b.length = 32 * d.val) (hi : i.val < 256) (hd : 0 < d.val ∧ d.val ≤ 12)
  (hn_bits_in_accumulator : n_bits_in_accumulator = 0#u32) :
  ∃ num_bytes_read' acc' n_bits_in_accumulator' coefficient,
    (do
          let a ← slice_to_sub_array4 b num_bytes_read
          let accumulator1 ← ↑(core.num.U32.from_le_bytes a)
          let cb_src_read1 ← num_bytes_read + 4#usize
          let n_bits_to_decode ← min d 32#u32
          massert (n_bits_to_decode ≤ 32#u32)
          let i ← 1#u32 <<< n_bits_to_decode
          let i1 ← i - 1#u32
          let bits_to_decode ← ↑(accumulator1 &&& i1)
          let accumulator2 ← accumulator1 >>> n_bits_to_decode
          let n_bits_in_accumulator1 ← 32#u32 - n_bits_to_decode
          let coefficient1 : UScalar UScalarTy.U32
            ← ↑(UScalar.ofNat 0 (by decide : 0 ≤ UScalar.cMax UScalarTy.U32) ||| bits_to_decode)
          if d > n_bits_to_decode then do
              massert (n_bits_in_accumulator1 = 0#u32)
              let a1 ← slice_to_sub_array4 b cb_src_read1
              let accumulator3 ← ↑(core.num.U32.from_le_bytes a1)
              let cb_src_read2 ← cb_src_read1 + 4#usize
              let n_bits_to_decode1 ← d - n_bits_to_decode
              massert (n_bits_to_decode1 ≤ 32#u32)
              let i2 ← 1#u32 <<< n_bits_to_decode1
              let i3 ← i2 - 1#u32
              let bits_to_decode1 : UScalar UScalarTy.U32 ← ↑(accumulator3 &&& i3)
              let accumulator4 ← accumulator3 >>> n_bits_to_decode1
              let n_bits_in_accumulator2 ← 32#u32 - n_bits_to_decode1
              let i4 ← bits_to_decode1 <<< n_bits_to_decode
              let coefficient2 ← ↑(coefficient1 ||| i4)
              ok (cb_src_read2, accumulator4, n_bits_in_accumulator2, coefficient2)
            else ok (cb_src_read1, accumulator2, n_bits_in_accumulator1, coefficient1)) =
        ok (num_bytes_read', acc', n_bits_in_accumulator', coefficient) ∧
    let s0 : SpecAux.Stream.DecodeState d 4 := {
      F := poly_to_vector (to_poly f),
      num_bytes_read := num_bytes_read.val,
      acc := acc.val,
      num_bits_in_acc := n_bits_in_accumulator.val
    }
    let s1 :=
      {
        F := (poly_to_vector (to_poly f)).set i.val coefficient,
        num_bytes_read := num_bytes_read',
        acc := acc',
        num_bits_in_acc := n_bits_in_accumulator'
      }
    SpecAux.Stream.decode.body b.val (by simp [hb2]) s0 i.val = s1 ∧
    SpecAux.Stream.decode.length_inv d 4 num_bytes_read' n_bits_in_accumulator' (i + 1) ∧
    (∀ j < n_bits_in_accumulator'.val, acc'.val.testBit j =
      b[(8 * num_bytes_read'.val - n_bits_in_accumulator'.val + j) / 8]!.val.testBit
        ((8 * num_bytes_read'.val - n_bits_in_accumulator'.val + j) % 8)) ∧
    (∀ j ∈ [n_bits_in_accumulator'.val:32], acc'.val.testBit j = false) ∧
    coefficient < Spec.m d := by
  have hnum_bytes_read : ↑num_bytes_read + 3 < b.length := by
    simp only [SpecAux.Stream.decode.length_inv, hn_bits_in_accumulator, UScalar.ofNat_val_eq,
      add_zero, Nat.reduceMul, Nat.mod_eq_iff, OfNat.ofNat_ne_zero, mul_eq_zero, false_and,
      Nat.ofNat_pos, true_and, false_or] at hinv
    rcases hinv with ⟨hinv1, hinv2, ⟨k, hk⟩⟩
    rw [(by omega : num_bytes_read.val = 4 * k), hb2]
    have : 4 * k < 32 * d.val := by
      rw [← Nat.mul_lt_mul_left (by omega : 0 < 8), ← mul_assoc, ← mul_assoc]
      simp only [Nat.reduceMul, ← hk, mul_comm 256, Nat.mul_lt_mul_left (by omega : 0 < d.val)]
      exact hi
    omega
  let* ⟨accumulator1, haccumulator1⟩ ← slice_to_sub_array4_spec
  let* ⟨accumulator2, haccumulator2⟩ ← core.num.U32.from_le_bytes.progress_spec
  let* ⟨cb_src_read1, hsb_src_read1⟩ ← Usize.add_spec
  let* ⟨n_bits_to_decode, hn_bits_to_decode⟩ ← min_spec
  progress with massert_spec
  let* ⟨mask0, hmask0⟩ ← U32.ShiftLeft_spec
  have : ↑1#u32 ≤ mask0.val := by
    rw [hmask0, Nat.mod_eq_of_lt]
    . simp only [UScalar.ofNat_val_eq]
      exact Nat.le_shiftLeft
    . have : Min.min d.val 32 = d.val := by omega
      simp only [hn_bits_to_decode, U32.size, U32.numBits, UScalarTy.U32_numBits_eq, this]
      apply Nat.lt_of_le_of_lt _ (by scalar_tac +nonLin : 2 ^ d.val < 2 ^ 32)
      have : ∀ x < 13, 1 <<< x ≤ 2 ^ x := by brute
      exact this d.val (by omega)
  let* ⟨mask1, hmask1⟩ ← U32.sub_bv_spec
  let* ⟨bits_to_decode, hbits_to_decode⟩ ← UScalar.and_spec
  let* ⟨accumulator3, haccumulator3⟩ ← U32.ShiftRight_spec
  let* ⟨n_bits_in_accumulator1, hn_bits_in_accumulator1⟩ ← U32.sub_bv_spec
  let* ⟨coefficient1, hcoefficient1⟩ ← UScalar.or_spec
  simp only [id_eq, Array.getElem!_Nat_eq, Slice.getElem!_Nat_eq] at haccumulator1
  have h1 : (d > n_bits_to_decode) = False := by
    simp only [gt_iff_lt, UScalar.lt_equiv, hn_bits_to_decode, inf_lt_left, not_le, eq_iff_iff,
      iff_false, not_lt]
    omega
  have h2 : Min.min d.val 32 = d.val := by scalar_tac
  have h3 :
    ∀ hCast : 8 * (List.map U8.bv ↑accumulator1).length = 32, accumulator2.val =
    (BitVec.cast hCast (BitVec.fromLEBytes (List.map U8.bv ↑accumulator1)) : BitVec 32).toNat := by
    simp [UScalar.val, haccumulator2]
  have h4 :
    List.slice (↑num_bytes_read) (↑num_bytes_read + 4)
      (List.flatMap (fun (a : U8) => [BitVec.ofNat 8 ↑a]) b.val) =
      List.map U8.bv ↑accumulator1 := by
    rw [List.eq_iff_forall_eq_getElem!]
    simp only [Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv,
      BitVec.setWidth_eq, List.slice_length, List.length_flatMap, List.length_cons,
      List.length_nil, zero_add, List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
      add_tsub_cancel_left, id_eq, List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq,
      inf_eq_right, lt_inf_iff, and_imp]
    constructor
    . scalar_tac
    . intro i _ hi
      rw [List.getElem!_map_eq]
      . rw [haccumulator1 i hi]
        rw [List.getElem!_slice]
        . rw [List.flatMap_eq_map, List.getElem!_map_eq]
          scalar_tac
        . simp only [List.length_flatMap, List.length_cons, List.length_nil, zero_add,
            List.map_const', List.sum_replicate, smul_eq_mul, mul_one, add_lt_add_iff_left]
          scalar_tac
      . scalar_tac
  simp only [gt_iff_lt, ↓reduceIte, ok.injEq, Prod.mk.injEq, SpecAux.Stream.decode.body,
    UScalar.ofNat_val_eq, beq_self_eq_true, Nat.reduceMul,
    SpecAux.Stream.decode.pop_bits_from_acc, SpecAux.Stream.decode.load_acc,
    BitVec.natCast_eq_ofNat, List.bind_eq_flatMap, BitVec.setWidth'_eq, BitVec.ofNat_eq_ofNat,
    BitVec.shiftLeft_sub_one_eq_mod, BitVec.toNat_umod, BitVec.toNat_setWidth,
    BitVec.toNat_pow, BitVec.toNat_ofNat, Nat.reduceMod, Vector.set_eq_set!,
    Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U32_numBits_eq, Bvify.U32.UScalar_bv,
    BitVec.setWidth_eq, SpecAux.Stream.DecodeState.mk.injEq, Slice.getElem!_Nat_eq,
    mem_std_range_step_one, and_imp, and_assoc, exists_and_left, exists_eq_left', UScalar.val_or,
    UScalar.val_and, id_eq, List.length_map, List.Vector.length_val, BitVec.toNat_cast,
    Nat.zero_or, tsub_le_iff_right, true_and, Nat.testBit_shiftRight, Nat.add_left_inj, *]
  split_conjs
  . have hmod1 : 2 ^ d.val % 2 ^ 32 = 2 ^ d.val := by
      have : ∀ x < 13, 2 ^ x % 2 ^ 32 = 2 ^ x := by brute
      apply this
      omega
    have hmod2 :
      (BitVec.fromLEBytes
        (List.slice (↑num_bytes_read) (↑num_bytes_read + 4)
          (List.flatMap (fun (a : U8) => [BitVec.ofNat 8 ↑a]) b.val))).toNat % 4294967296 =
      (BitVec.fromLEBytes
        (List.slice (↑num_bytes_read) (↑num_bytes_read + 4)
          (List.flatMap (fun (a : U8) => [BitVec.ofNat 8 ↑a]) b.val))).toNat := by
      simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
      rw [(by omega : 4294967296 = 2 ^ 32)]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv,
        BitVec.setWidth_eq, List.flatMap_eq_map, List.slice_length, List.length_map,
        add_tsub_cancel_left]
      omega
    have hmod3 : 1 <<< d.val % U32.size = 1 <<< d.val := by scalar_tac
    rw [hmod1, hmod2, hmod3]
    congr
    apply mod_two_pow
    rw [h4]
  . congr
    simp only [BitVec.cast, BitVec.setWidth, BitVec.setWidth']
    split
    . congr -- Uses `h4` to close the difficult subgoals
    . scalar_tac -- `scalar_tac` derives a contradiction from the introduced hypothesis
  . unfold SpecAux.Stream.decode.length_inv
    simp only [Nat.reduceLeDiff, Nat.reduceMul]
    split_conjs
    . omega
    . simp only [mul_add, hinv.2.1, hn_bits_in_accumulator, UScalar.ofNat_val_eq, add_zero,
        Nat.reduceMul, mul_one]
      omega
    . have : d.val + (32 - d.val) = 32 := by omega
      rw [mul_add, mul_one, add_assoc, this, Nat.add_mod_right, ← hinv.2.2, hn_bits_in_accumulator]
      simp
  . intro j hj
    rw [BitVec.testBit_toNat, BitVec.getLsbD_eq_getElem, ← BitVec.getElem!_eq_getElem,
      BitVec.fromLEBytes_getElem!, List.getElem!_map_eq]
    . have : (8 * ↑num_bytes_read + 32 - (32 - ↑d) + j) % 8 = (d.val + j) % 8 := by omega
      simp only [Byte.testBit, haccumulator1 ((d.val + j) / 8) (by scalar_tac), UScalar.bv_toNat,
        mul_add, Nat.reduceMul, this]
      congr
      omega
    . simp only [List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.reduceMul]
      omega
    . simp only [List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.reduceMul]
      omega
  . intro j hj1 hj2
    apply Nat.testBit_eq_false_of_lt
    apply BitVec.toNat_lt_twoPow_of_le
    simp only [List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.reduceMul]
    omega
  . have : 1 <<< d.val % U32.size = 1 <<< d.val := by
      have : ∀ x < 13, 1 <<< x % U32.size = 1 <<< x := by brute
      exact this _ (by scalar_tac)
    rw [this]
    have :
      (BitVec.fromLEBytes (List.map U8.bv ↑accumulator1)).toNat &&& 1 <<< d.val - 1 =
      ∑ a : Fin d.val, ((b[(d.val * i + a.val) / 8]!).val.testBit ((↑d * i + ↑a) % 8)).toNat * 2 ^ a.val := by
      apply Nat.eq_of_testBit_eq
      intro j
      dcases hj : j < d
      . have : (1 <<< ↑d - 1).testBit j = true := by
          have : ∀ x < 13, ∀ y < x, (1 <<< x - 1).testBit y = true := by brute
          exact this d.val (by omega) j hj
        simp only [id_eq, Nat.testBit_and, ← BitVec.getElem!_eq_testBit_toNat,
          BitVec.fromLEBytes_getElem!, this, Bool.and_true, Slice.getElem!_Nat_eq,
          SpecAux.testBit_of_sum d (by omega) j hj]
        rw [List.getElem!_map_eq, haccumulator1 (j / 8) (by scalar_tac)]
        . have := hinv.2.1
          simp only [hn_bits_in_accumulator, UScalar.ofNat_val_eq, add_zero] at this
          simp only [← this, Nat.mul_add_mod_self_left]
          have : ↑num_bytes_read + j / 8 = ((8 * ↑num_bytes_read) + j) / 8 := by omega
          simp only [this, BitVec.getElem!_eq_testBit_toNat, UScalar.bv_toNat]
        . scalar_tac
      . have : ((BitVec.fromLEBytes (List.map U8.bv ↑accumulator1)).toNat
          &&& 1 <<< d.val - 1).testBit j = false := by
          simp only [id_eq, Nat.testBit_and, Bool.and_eq_false_imp]
          intro _
          apply Nat.testBit_eq_false_of_lt
          apply Nat.lt_of_lt_of_le (by scalar_tac : 1 <<< d.val - 1 < 1 <<< d.val)
          rw [Nat.one_shiftLeft]
          scalar_tac +nonLin
        rw [this]
        have : (∑ a : Fin d.val, ((b[(d.val * i.val + a.val) / 8]!).val.testBit
          ((d.val * i.val + a.val) % 8)).toNat * 2 ^ a.val).testBit j = false := by
          apply Nat.testBit_eq_false_of_lt
          apply Nat.lt_of_lt_of_le _ (by scalar_tac +nonLin : 2 ^ d.val ≤ 2 ^ j)
          apply SpecAux.sum_bits_lt (by omega)
        rw [this]
    rw [this]
    exact hb1 i.val (by omega)

theorem decode_coefficient.late_load_progress_spec (b : Slice U8) (d : U32) (f : Std.Array U16 256#usize)
  (num_bytes_read : Usize) (acc n_bits_in_accumulator : U32) (i : Usize)
  (hacc1 : (∀ j < n_bits_in_accumulator.val, acc.val.testBit j =
    b[(8 * num_bytes_read.val - n_bits_in_accumulator.val + j) / 8]!.val.testBit
      ((8 * num_bytes_read.val - n_bits_in_accumulator.val + j) % 8)))
  (hinv : SpecAux.Stream.decode.length_inv (↑d) 4 ↑num_bytes_read ↑n_bits_in_accumulator ↑i)
  (hb1 : ∀ i < 256,
    ∑ (a : Fin d), (Bool.toNat (b[(d.val * i + a) / 8]!.val.testBit ((d * i + a) % 8))) * 2^a.val < Spec.m d)
  (hb2 : b.length = 32 * d.val) (hi : i.val < 256) (hd : 0 < d.val ∧ d.val ≤ 12)
  (hn_bits_in_accumulator : ¬n_bits_in_accumulator = 0#u32) (n_bits_to_decode : U32)
  (hn_bits_to_decode : n_bits_to_decode.val = Min.min d.val n_bits_in_accumulator.val) (i' : U32)
  (hi' : ↑i' = 1 <<< ↑n_bits_to_decode % U32.size) (i1 : U32)
  (hi1 : ↑i1 = i'.val - 1) (bits_to_decode : U32) (hbits_to_decode : bits_to_decode.val = (acc &&& i1).val)
  (accumulator1 : U32) (n_bits_in_accumulator1 : U32)
  (hn_bits_in_accumulator1 : ↑n_bits_in_accumulator1 = n_bits_in_accumulator.val - ↑n_bits_to_decode)
  (coefficient1 : U32) (h : d > n_bits_to_decode)
  -- **TODO** Currently, the automation in this proof fails if I eliminate the following hypotheses, but
  -- none of these hypotheses ought to be necessary (except for potentially `__6` and `__12`).
  (__1 : [> let n_bits_to_decode ← min d n_bits_in_accumulator <])
  (__2 : [> let i' ← 1#u32 <<< n_bits_to_decode <])
  (__3 : i'.bv = U32.bv 1#u32 <<< n_bits_to_decode.val)
  (__4 : [> let i1 ← i' - 1#u32 <])
  (__5 : i1.bv = i'.bv - U32.bv 1#u32)
  (__6 : 1 ≤ i'.val)
  (__7 : [> let bits_to_decode ← ↑(acc &&& i1) <])
  (__8 : bits_to_decode.bv = acc.bv &&& i1.bv)
  (__9 : [> let accumulator1 ← acc >>> n_bits_to_decode <])
  (__10 : accumulator1.bv = acc.bv >>> n_bits_to_decode.val)
  (__11 : [> let n_bits_in_accumulator1 ← n_bits_in_accumulator - n_bits_to_decode <])
  (__12 : ↑n_bits_to_decode ≤ ↑n_bits_in_accumulator)
  (__13 : n_bits_in_accumulator1.bv = n_bits_in_accumulator.bv - n_bits_to_decode.bv)
  (_ : [> let coefficient1 ←
    ↑(@HOr.hOr U32 U32 U32 instHOrUScalar (UScalar.ofNat 0 (by decide)) bits_to_decode) <])
  (hcoefficient1 : ↑coefficient1 = @UScalar.val UScalarTy.U32
    (@HOr.hOr U32 U32 U32 instHOrUScalar (UScalar.ofNat 0 (by decide)) bits_to_decode))
  (__14 : coefficient1.bv =
    @HOr.hOr (BitVec UScalarTy.U32.numBits) (BitVec UScalarTy.U32.numBits) (BitVec UScalarTy.U32.numBits)
      instHOrOfOrOp (UScalar.ofNat 0 (by decide)).bv bits_to_decode.bv) :
  ∃ num_bytes_read' acc' n_bits_in_accumulator' coefficient,
    (do
          massert (n_bits_in_accumulator1 = 0#u32)
          let a ← slice_to_sub_array4 b num_bytes_read
          let accumulator2 ← ↑(core.num.U32.from_le_bytes a)
          let cb_src_read1 ← num_bytes_read + 4#usize
          let n_bits_to_decode1 ← d - n_bits_to_decode
          massert (n_bits_to_decode1 ≤ 32#u32)
          let i2 ← 1#u32 <<< n_bits_to_decode1
          let i3 ← i2 - 1#u32
          let bits_to_decode1 ← @toResult U32 (accumulator2 &&& i3)
          let accumulator3 ← accumulator2 >>> n_bits_to_decode1
          let n_bits_in_accumulator2 ← 32#u32 - n_bits_to_decode1
          let i4 ← bits_to_decode1 <<< n_bits_to_decode
          let coefficient2 : U32 ← ↑(coefficient1 ||| i4)
          ok (cb_src_read1, accumulator3, n_bits_in_accumulator2, coefficient2)) =
        ok (num_bytes_read', acc', n_bits_in_accumulator', coefficient) ∧
    @SpecAux.Stream.decode.body d.val 4
      (do
        let a ← b.val
        [↑↑a]
      ) (by simp [hb2])
      { F := poly_to_vector (to_poly f), num_bytes_read := ↑num_bytes_read, acc := ↑↑acc,
          num_bits_in_acc := ↑n_bits_in_accumulator }
        ↑i =
      { F := (poly_to_vector (to_poly f)).set (↑i) (↑coefficient) hi, num_bytes_read := ↑num_bytes_read',
        acc := ↑↑acc', num_bits_in_acc := ↑n_bits_in_accumulator' } ∧
    SpecAux.Stream.decode.length_inv (↑d) 4 (↑num_bytes_read') (↑n_bits_in_accumulator') (↑i + 1) ∧
      (∀ j < ↑n_bits_in_accumulator',
          acc'.val.testBit j =
            (b[(8 * ↑num_bytes_read' - ↑n_bits_in_accumulator' + j) / 8]!).val.testBit
              ((8 * ↑num_bytes_read' - ↑n_bits_in_accumulator' + j) % 8)) ∧
        (∀ (j : ℕ), n_bits_in_accumulator'.val ≤ j ∧ j < 32 → acc'.val.testBit j = false) ∧
        ↑coefficient < Spec.m ↑d := by
  progress with massert_spec
  have hnum_bytes_read : ↑num_bytes_read + 3 < b.length := by
    simp only [SpecAux.Stream.decode.length_inv, Nat.reduceMul, Nat.mod_eq_iff, OfNat.ofNat_ne_zero,
      Nat.add_eq_zero, mul_eq_zero, false_and, Nat.ofNat_pos, add_zero, true_and, false_or] at hinv
    rcases hinv with ⟨hinv1, hinv2, ⟨k, hk⟩⟩
    rw [(by omega : num_bytes_read.val = 4 * k), hb2]
    have : 4 * k < 32 * d.val := by
      rw [← Nat.mul_lt_mul_left (by omega : 0 < 8), ← mul_assoc, ← mul_assoc]
      simp only [Nat.reduceMul, ← hk, mul_comm 256, Nat.mul_lt_mul_left (by omega : 0 < d.val)]
      have : d.val * i + n_bits_in_accumulator ≤ d.val * 255 + n_bits_in_accumulator := by
        rw [Nat.add_le_add_iff_right]
        apply Nat.mul_le_mul_left
        omega
      apply Nat.lt_of_le_of_lt this
      have : n_bits_in_accumulator.val < d.val := by simp_all
      omega
    omega
  let* ⟨accumulator1, haccumulator1⟩ ← slice_to_sub_array4_spec
  let* ⟨accumulator2, haccumulator2⟩ ← core.num.U32.from_le_bytes.progress_spec
  let* ⟨cb_src_read1, hcb_src_read1⟩ ← Usize.add_spec
  let* ⟨n_bits_to_decode1, hn_bits_to_decode1⟩ ← U32.sub_bv_spec
  progress with massert_spec
  let* ⟨i2, hi2⟩ ← U32.ShiftLeft_spec
  have : 1 <<< ↑n_bits_to_decode1 % U32.size = 1 <<< n_bits_to_decode1.val := by
    rw [hn_bits_to_decode1, Nat.mod_eq_of_lt]
    have : 1 <<< (d.val - n_bits_to_decode.val) ≤ 1 <<< d.val := by
      simp only [Nat.one_shiftLeft]
      scalar_tac +nonLin
    apply Nat.lt_of_le_of_lt this
    have : ∀ x < 13, 1 <<< x < U32.size := by brute
    exact this d.val (by omega)
  let* ⟨i3, hi3⟩ ← U32.sub_bv_spec
  . simp only [UScalar.ofNat_val_eq, hi2, this, ge_iff_le]
    apply Nat.le_shiftLeft
  . let* ⟨bits_to_decode1, hbits_to_decode1⟩ ← UScalar.and_spec
    let* ⟨accumulator3, haccumulator3⟩ ← U32.ShiftRight_spec
    let* ⟨n_bits_in_accumulator2, hn_bits_in_accumulator2⟩ ← U32.sub_bv_spec
    let* ⟨i4, hi4⟩ ← U32.ShiftLeft_spec
    let* ⟨coefficient2, hcoefficient2⟩ ← UScalar.or_spec
    simp only [UScalar.neq_to_neq_val, UScalar.ofNat_val_eq] at hn_bits_in_accumulator
    simp only [id_eq, Array.getElem!_Nat_eq, Slice.getElem!_Nat_eq] at haccumulator1
    have hn_bits_in_accumulator' : ↑n_bits_in_accumulator < d.val := by
      have : d.val > n_bits_to_decode.val := by scalar_tac
      rw [hn_bits_to_decode] at this
      scalar_tac
    have hmod_u32 : 1 <<< ↑n_bits_in_accumulator % U32.size = 1 <<< n_bits_in_accumulator.val := by
      rw [Nat.mod_eq_of_lt]
      have : ∀ x < 13, ∀ y < x, 1 <<< y < U32.size := by brute
      exact this d.val (by omega) n_bits_in_accumulator hn_bits_in_accumulator'
    have h1 : Min.min d.val n_bits_in_accumulator.val = n_bits_in_accumulator.val := by scalar_tac
    have h2 : 2 ^ n_bits_in_accumulator.val % 4294967296 = 2 ^ n_bits_in_accumulator.val := by
      rw [Nat.mod_eq_of_lt]
      rw [(by decide : 4294967296 = 2 ^ 32)]
      scalar_tac +nonLin
    have h3 :
      ∀ hCast : 8 * (List.map U8.bv ↑accumulator1).length = 32, accumulator2.val =
      (BitVec.cast hCast (BitVec.fromLEBytes (List.map U8.bv ↑accumulator1)) : BitVec 32).toNat := by
      simp [UScalar.val, haccumulator2]
    have h4 :
      List.slice (↑num_bytes_read) (↑num_bytes_read + 4)
        (List.flatMap (fun (a : U8) => [BitVec.ofNat 8 ↑a]) b.val) =
        List.map U8.bv ↑accumulator1 := by
      rw [List.eq_iff_forall_eq_getElem!]
      simp only [Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv,
        BitVec.setWidth_eq, List.slice_length, List.length_flatMap, List.length_cons,
        List.length_nil, zero_add, List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
        add_tsub_cancel_left, id_eq, List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq,
        inf_eq_right, lt_inf_iff, and_imp]
      constructor
      . scalar_tac
      . intro i _ hi
        rw [List.getElem!_map_eq]
        . rw [haccumulator1 i hi]
          rw [List.getElem!_slice]
          . rw [List.flatMap_eq_map, List.getElem!_map_eq]
            scalar_tac
          . simp only [List.length_flatMap, List.length_cons, List.length_nil, zero_add,
              List.map_const', List.sum_replicate, smul_eq_mul, mul_one, add_lt_add_iff_left]
            scalar_tac
        . scalar_tac
    have h5 : 2 ^ (d.val - n_bits_in_accumulator.val) % 4294967296 =
      2 ^ (d.val - n_bits_in_accumulator.val) := by
      rw [Nat.mod_eq_of_lt]
      rw [(by decide : 4294967296 = 2 ^ 32)]
      scalar_tac +nonLin
    simp only [SpecAux.Stream.decode.body, beq_iff_eq, ↓reduceIte, gt_iff_lt, Nat.reduceMul,
      SpecAux.Stream.decode.pop_bits_from_acc, BitVec.natCast_eq_ofNat,
      Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U32_numBits_eq, Bvify.U32.UScalar_bv,
      BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod, tsub_self,
      SpecAux.Stream.decode.load_acc, List.bind_eq_flatMap, BitVec.setWidth'_eq, BitVec.toNat_or,
      BitVec.toNat_umod, UScalar.bv_toNat, BitVec.toNat_pow, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Vector.set_eq_set!,
      SpecAux.Stream.DecodeState.mk.injEq, Slice.getElem!_Nat_eq, and_imp, and_assoc,
      exists_and_left, exists_eq_left', UScalar.val_or, UScalar.ofNat_val_eq, UScalar.val_and,
      Nat.zero_or, tsub_le_iff_right, true_and, id_eq, Nat.testBit_shiftRight, Nat.add_left_inj, *]
    split_conjs
    . ext j hj
      simp only [Vector.Inhabited_getElem_eq_getElem!]
      dcases hij : i.val = j
      . rw [← hij, Vector.getElem!_set! (by omega), Vector.getElem!_set! (by omega)]
        congr 1
        . simp only [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
        . congr 1
          . have : 1 <<< (d.val - n_bits_in_accumulator.val) % U32.size =
              1 <<< (d.val - n_bits_in_accumulator.val) := by
              rw [Nat.mod_eq_of_lt]
              have : ∀ x < 13, ∀ y < x, 1 <<< (x - y) < U32.size := by brute
              exact this d.val (by omega) n_bits_in_accumulator.val hn_bits_in_accumulator'
            rw [this, Nat.one_shiftLeft]
            congr
            simp only [id_eq, List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq,
              Nat.reduceMul, h3, BitVec.toNat_cast, Nat.and_two_pow_sub_one_eq_mod]
            congr
            have :
              (BitVec.fromLEBytes
                (List.slice (↑num_bytes_read) (↑num_bytes_read + 4)
                  (List.flatMap (fun (a : U8) => [BitVec.ofNat 8 ↑a]) b.val))).toNat % 4294967296 =
              (BitVec.fromLEBytes
                (List.slice (↑num_bytes_read) (↑num_bytes_read + 4)
                  (List.flatMap (fun (a : U8) => [BitVec.ofNat 8 ↑a]) b.val))).toNat := by
              simp only [List.pure_def, List.bind_eq_flatMap, Nat.mod_succ_eq_iff_lt,
                Nat.succ_eq_add_one, Nat.reduceAdd]
              rw [(by decide : 4294967296 = 2 ^ 32)]
              apply BitVec.toNat_lt_twoPow_of_le
              simp only [List.slice_length, List.length_flatMap, List.length_cons, List.length_nil,
                zero_add, List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
                add_tsub_cancel_left]
              omega
            rw [this]
            apply Nat.eq_of_testBit_eq
            intro k
            dcases hk : k < 32
            . rw [← BitVec.getElem!_eq_testBit_toNat, ← BitVec.getElem!_eq_testBit_toNat,
                BitVec.fromLEBytes_getElem!, BitVec.fromLEBytes_getElem!, List.getElem!_map_eq]
              . congr
                rw [haccumulator1 (k / 8) (by scalar_tac), List.flatMap_eq_map, List.getElem!_slice,
                  List.getElem!_map_eq]
                . simp
                . scalar_tac
                . simp only [Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U8_numBits_eq,
                    Bvify.U8.UScalar_bv, BitVec.setWidth_eq, List.length_map, add_lt_add_iff_left]
                  scalar_tac
              . scalar_tac
            . rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
              . apply BitVec.toNat_lt_twoPow_of_le
                simp only [List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq,
                  Nat.reduceMul]
                omega
              . apply BitVec.toNat_lt_twoPow_of_le
                simp only [Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U8_numBits_eq,
                  Bvify.U8.UScalar_bv, BitVec.setWidth_eq, List.slice_length, List.length_flatMap,
                  List.length_cons, List.length_nil, zero_add, List.map_const', List.sum_replicate,
                  smul_eq_mul, mul_one, add_tsub_cancel_left]
                omega
          . simp only [U32.size, U32.numBits, UScalarTy.U32_numBits_eq, Nat.reducePow]
      . rw [Vector.getElem!_set!_ne (by omega), Vector.getElem!_set!_ne (by omega)]
    . simp only [BitVec.cast, BitVec.setWidth, BitVec.setWidth']
      split
      . congr -- Difficult subgoals closed with `h4`
      . scalar_tac -- Derives a contradiction from the most recently introduced hypothesis
    . unfold SpecAux.Stream.decode.length_inv
      simp only [Nat.reduceLeDiff, Nat.reduceMul]
      split_conjs
      . omega
      . simp only [mul_add, hinv.2.1, hn_bits_in_accumulator, UScalar.ofNat_val_eq, add_zero,
          Nat.reduceMul, mul_one]
        omega
      . have : d.val + (32 - (d.val - n_bits_in_accumulator.val)) = n_bits_in_accumulator.val + 32 := by
          omega
        rw [mul_add, mul_one, add_assoc, this, ← add_assoc, Nat.add_mod_right, ← hinv.2.2]
    . intro j hj
      have : @UScalar.val UScalarTy.U32 accumulator2 = accumulator2.bv.toNat := by simp
      simp only [this, haccumulator2, id_eq, BitVec.toNat_cast, BitVec.testBit_toNat]
      have h6 : (8 * (↑num_bytes_read + 4) - (32 - (d.val - ↑n_bits_in_accumulator)) + j) / 8 =
        ↑num_bytes_read + (d.val - ↑n_bits_in_accumulator + j) / 8 := by omega
      have h7 : (8 * (↑num_bytes_read + 4) - (32 - (d.val - ↑n_bits_in_accumulator)) + j) % 8 =
        (d.val - ↑n_bits_in_accumulator + j) % 8 := by omega
      rw [BitVec.getLsbD_eq_getElem, ← BitVec.getElem!_eq_getElem, BitVec.fromLEBytes_getElem!,
        List.getElem!_map_eq, haccumulator1 ((d.val - n_bits_in_accumulator.val + j) / 8) (by scalar_tac),
        U8.bv, Byte.testBit, UScalar.bv_toNat, h6, h7]
      . simp only [List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.reduceMul]
        omega
      . simp only [List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.reduceMul]
        omega
    . intro j hj1 hj2
      apply Nat.testBit_eq_false_of_lt
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [UScalarTy.numBits]
      omega
    . have :
        (↑acc : ℕ) &&& 1 <<< (↑n_bits_in_accumulator : ℕ) - 1 |||
          (↑accumulator2 &&& 1 <<< (↑d - ↑n_bits_in_accumulator) % U32.size - 1) <<<
            ↑n_bits_in_accumulator % U32.size =
        ∑ a : Fin d.val,
          ((b[(d.val * i + a.val) / 8]!).val.testBit ((↑d * i + ↑a) % 8)).toNat * 2 ^ a.val := by
        have : 1 <<< (d.val - ↑n_bits_in_accumulator) % U32.size =
          1 <<< (d.val - ↑n_bits_in_accumulator) := by
          have : ∀ x < 13, ∀ y < x, 1 <<< (x - y) % U32.size = 1 <<< (x - y) := by brute
          exact this d.val (by omega) n_bits_in_accumulator.val hn_bits_in_accumulator'
        rw [this]
        have :
          (↑accumulator2 &&& 1 <<< (↑d - ↑n_bits_in_accumulator) - 1) <<< ↑n_bits_in_accumulator % U32.size =
          (↑accumulator2 &&& 1 <<< (↑d - ↑n_bits_in_accumulator) - 1) <<< ↑n_bits_in_accumulator := by
          rw [Nat.mod_eq_of_lt]
          rw [Nat.shiftLeft_and_distrib] -- Not sure why this needs to be it's own `rw` call, but it does
          apply Nat.lt_of_le_of_lt Nat.and_le_right
          have : (1 <<< (d.val - ↑n_bits_in_accumulator) - 1) <<< ↑n_bits_in_accumulator < 1 <<< d.val := by
            have : ∀ x < 13, ∀ y < x, (1 <<< (x - y) - 1) <<< y < 1 <<< x := by brute
            exact this d.val (by omega) n_bits_in_accumulator.val hn_bits_in_accumulator'
          apply Nat.lt_trans this
          have : ∀ x < 13, 1 <<< x < U32.size := by brute
          exact this d.val (by omega)
        rw [this]
        apply Nat.eq_of_testBit_eq
        intro j
        dcases hj1 : j < d.val
        . rw [SpecAux.testBit_of_sum d.val (by omega) j hj1,
            SpecAux.bitwise_or_eq_and _ _ d.val n_bits_in_accumulator.val (by omega) (by omega)]
          . dcases hj2 : j < n_bits_in_accumulator.val
            . rw [SpecAux.testBit_of_add1 _ _ d.val n_bits_in_accumulator.val j (by omega) (by omega) hj2]
              . have : (1 <<< ↑n_bits_in_accumulator - 1).testBit j := by
                  have : ∀ x < 13, ∀ y < x, (1 <<< x - 1).testBit y := by brute
                  exact this n_bits_in_accumulator.val (by omega) j hj2
                rw [Nat.testBit_and, this, Bool.and_true, hacc1 j hj2, hinv.2.1]
                congr <;> omega
              . apply Nat.lt_of_le_of_lt Nat.and_le_right
                scalar_tac
              . apply Nat.lt_of_le_of_lt Nat.and_le_right
                scalar_tac
            . rw [SpecAux.testBit_of_add2 _ _ d.val n_bits_in_accumulator.val j (by omega) (by omega) hj1]
              . have : (1 <<< (↑d - ↑n_bits_in_accumulator) - 1).testBit (j - ↑n_bits_in_accumulator) := by
                  have : ∀ x < 13, ∀ y < x, (1 <<< x - 1).testBit y := by brute
                  exact this (↑d - ↑n_bits_in_accumulator) (by omega) (j - n_bits_in_accumulator.val) (by omega)
                rw [Nat.testBit_and, this, Bool.and_true, h3 (by simp)]
                simp only [id_eq, BitVec.toNat_cast, Slice.getElem!_Nat_eq]
                rw [← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!, List.getElem!_map_eq]
                . have h6 : ↑num_bytes_read + (j - ↑n_bits_in_accumulator) / 8 = (↑d * ↑i + j) / 8 := by
                    have : ↑num_bytes_read + (j - ↑n_bits_in_accumulator) / 8 =
                      (8 * ↑num_bytes_read + j - ↑n_bits_in_accumulator) / 8 := by omega
                    rw [this, hinv.2.1]
                    omega
                  have h7 : (j - ↑n_bits_in_accumulator) % 8 = (↑d * ↑i + j) % 8 := by
                    have : (j - ↑n_bits_in_accumulator + n_bits_in_accumulator.val) % 8 =
                      (d.val * i.val + j + n_bits_in_accumulator.val) % 8 →
                      (j - ↑n_bits_in_accumulator) % 8 = (d.val * i.val + j) % 8 := by omega
                    apply this
                    rw [Nat.add_assoc, Nat.add_comm j, ← Nat.add_assoc, ← hinv.2.1]
                    omega
                  rw [Byte.testBit, UScalar.bv_toNat, haccumulator1 _ (by omega), h6, h7]
                . scalar_tac
              . apply Nat.lt_of_le_of_lt Nat.and_le_right
                scalar_tac
              . apply Nat.lt_of_le_of_lt Nat.and_le_right
                scalar_tac
          . apply Nat.lt_of_le_of_lt Nat.and_le_right
            scalar_tac
          . apply Nat.lt_of_le_of_lt Nat.and_le_right
            scalar_tac
        . rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
          . exact Nat.lt_of_lt_of_le (SpecAux.sum_bits_lt (by omega) _) (by scalar_tac +nonLin : 2^d.val ≤ 2^j)
          . rw [SpecAux.bitwise_or_eq_and _ _ d.val n_bits_in_accumulator.val (by omega) (by omega)]
            . have :
                (↑acc &&& 1 <<< ↑n_bits_in_accumulator - 1) ≤ 1 <<< ↑n_bits_in_accumulator - 1 :=
                by exact Nat.and_le_right
              have :
                (1 <<< ↑n_bits_in_accumulator - 1) +
                (1 <<< (↑d - ↑n_bits_in_accumulator) - 1) <<< n_bits_in_accumulator.val < 2^j := by
                rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.shiftLeft_eq_mul_pow, Nat.mul_comm,
                  Nat.mul_sub, ← Nat.pow_add, Nat.mul_one]
                have : 2 ^ n_bits_in_accumulator.val - 1 +
                  (2 ^ (↑n_bits_in_accumulator + (d.val - ↑n_bits_in_accumulator)) - 2 ^ n_bits_in_accumulator.val) =
                  2 ^ n_bits_in_accumulator.val +
                  (2 ^ (↑n_bits_in_accumulator + (d.val - ↑n_bits_in_accumulator))
                    - 2 ^ n_bits_in_accumulator.val) - 1 := by
                  scalar_tac
                rw [this, Nat.add_sub_of_le, Nat.add_sub_of_le]
                . apply Nat.sub_one_lt_of_le
                  . exact Nat.two_pow_pos ↑d
                  . scalar_tac +nonLin
                . omega
                . rw [Nat.add_sub_of_le] <;> scalar_tac +nonLin
              apply Nat.lt_of_le_of_lt _ this
              apply Nat.add_le_add Nat.and_le_right
              simp [Nat.shiftLeft_eq, Nat.le_sub_one_iff_lt, Nat.mod_lt]
            . apply Nat.lt_of_le_of_lt Nat.and_le_right
              scalar_tac
            . apply Nat.lt_of_le_of_lt Nat.and_le_right
              scalar_tac
      rw [this]
      exact hb1 i.val (by omega)

@[progress]
def decode_coefficient.progress_spec (b : Slice U8) (d : U32) (f : Array U16 256#usize)
  (num_bytes_read : Usize) (acc : U32) (n_bits_in_accumulator : U32) (i : Usize)
  (hacc1 : (∀ j < n_bits_in_accumulator.val, acc.val.testBit j =
    b[(8 * num_bytes_read.val - n_bits_in_accumulator.val + j) / 8]!.val.testBit
      ((8 * num_bytes_read.val - n_bits_in_accumulator.val + j) % 8)))
  (hacc2 : ∀ j ∈ [n_bits_in_accumulator.val:32], acc.val.testBit j = false)
  (hinv : SpecAux.Stream.decode.length_inv d 4 num_bytes_read n_bits_in_accumulator i)
  (hb1 : ∀ i < 256,
    ∑ (a : Fin d), (Bool.toNat (b[(d.val * i + a) / 8]!.val.testBit ((d * i + a) % 8))) * 2^a.val < Spec.m d)
  (hb2 : b.length = 32 * d.val) (hi : i.val < 256) (hd : 0 < d.val ∧ d.val ≤ 12) :
  ∃ num_bytes_read' acc' n_bits_in_accumulator' coefficient,
    decode_coefficient b d num_bytes_read acc n_bits_in_accumulator (UScalar.ofNat 0) =
      ok (num_bytes_read', acc', n_bits_in_accumulator', coefficient) ∧
  let s0 : SpecAux.Stream.DecodeState d 4 := {
    F := poly_to_vector (to_poly f),
    num_bytes_read := num_bytes_read.val,
    acc := acc.val,
    num_bits_in_acc := n_bits_in_accumulator.val
  }
  let s1 :=
    {
      F := (poly_to_vector (to_poly f)).set i.val coefficient,
      num_bytes_read := num_bytes_read',
      acc := acc',
      num_bits_in_acc := n_bits_in_accumulator'
    }
  SpecAux.Stream.decode.body b.val (by simp [hb2]) s0 i.val = s1 ∧
  SpecAux.Stream.decode.length_inv d 4 num_bytes_read' n_bits_in_accumulator' (i + 1) ∧
  (∀ j < n_bits_in_accumulator'.val, acc'.val.testBit j =
    b[(8 * num_bytes_read'.val - n_bits_in_accumulator'.val + j) / 8]!.val.testBit
      ((8 * num_bytes_read'.val - n_bits_in_accumulator'.val + j) % 8)) ∧
  (∀ j ∈ [n_bits_in_accumulator'.val:32], acc'.val.testBit j = false) ∧
  coefficient < Spec.m d := by
  unfold decode_coefficient
  split
  . exact decode_coefficient.early_load_progress_spec b d f num_bytes_read acc n_bits_in_accumulator i
      hinv hb1 hb2 hi hd (by assumption)
  . next hn_bits_in_accumulator =>
    let* ⟨n_bits_to_decode, hn_bits_to_decode⟩ ← min_spec
    progress with massert_spec
    let* ⟨i', hi'⟩ ← U32.ShiftLeft_spec
    let* ⟨i1, hi1⟩ ← U32.sub_bv_spec
    . rw [hi', hn_bits_to_decode]
      tlet min_exp := Min.min d.val n_bits_in_accumulator.val
      have hmin_exp : min_exp < 13 := by omega
      have : ∀ min_exp < 13, ↑1#u32 ≤ 1 <<< min_exp % U32.size := by brute
      exact this min_exp hmin_exp
    . let* ⟨bits_to_decode, hbits_to_decode⟩ ← UScalar.and_spec
      let* ⟨accumulator1, haccumulator1⟩ ← U32.ShiftRight_spec
      let* ⟨n_bits_in_accumulator1, hn_bits_in_accumulator1⟩ ← U32.sub_bv_spec
      let* ⟨coefficient1, hcoefficient1⟩ ← UScalar.or_spec
      split
      . simp only [mem_std_range_step_one]
        apply decode_coefficient.late_load_progress_spec b d f num_bytes_read acc n_bits_in_accumulator i
          hacc1 hinv hb1 hb2 hi hd hn_bits_in_accumulator n_bits_to_decode hn_bits_to_decode i' hi' i1
          hi1 bits_to_decode hbits_to_decode accumulator1 n_bits_in_accumulator1 hn_bits_in_accumulator1
          coefficient1 <;> assumption
      . next hd =>
        replace hd : d = n_bits_to_decode := by scalar_tac
        simp only [UScalar.neq_to_neq_val, UScalar.ofNat_val_eq] at hn_bits_in_accumulator
        simp only [hd, left_eq_inf] at hn_bits_to_decode
        simp only [ok.injEq, Prod.mk.injEq, SpecAux.Stream.decode.body, beq_iff_eq,
          hn_bits_in_accumulator, ↓reduceIte, hd, hn_bits_to_decode, inf_of_le_left, gt_iff_lt,
          lt_self_iff_false, Nat.reduceMul, BitVec.natCast_eq_ofNat,
          Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U32_numBits_eq, Bvify.U32.UScalar_bv,
          BitVec.setWidth_eq, Vector.set_eq_set!, SpecAux.Stream.DecodeState.mk.injEq, and_assoc,
          exists_and_left, exists_eq_left', true_and]
        have hmodu32 : 1 <<< n_bits_to_decode.val % U32.size = 1 <<< n_bits_to_decode.val := by
          apply Nat.mod_eq_of_lt
          rw [← hd]
          tlet x := d.val
          have : ∀ x < 13, 1 <<< x < U32.size := by brute
          exact this x (by scalar_tac)
        split_conjs
        . simp only [SpecAux.Stream.decode.pop_bits_from_acc, hbits_to_decode, hi1, hi', hcoefficient1,
            Nat.reduceMul, UScalar.val_or, UScalar.ofNat_val_eq, Nat.zero_or, UScalar.val_and,
            BitVec.toNat_and, UScalar.bv_toNat]
          rw [hmodu32]
          congr
          tlet x := n_bits_to_decode.val
          have : ∀ x < 13, (1#32 <<< x - 1).toNat = 1 <<< x - 1 := by brute
          exact this x (by scalar_tac)
        . simp_all [SpecAux.Stream.decode.pop_bits_from_acc]
        . simp_all [SpecAux.Stream.decode.pop_bits_from_acc]
        . simp only [SpecAux.Stream.decode.length_inv, Nat.reduceLeDiff, Nat.reduceMul]
          split_conjs
          . scalar_tac
          . rw [hn_bits_in_accumulator1, mul_add, mul_one, add_assoc,
              Nat.add_sub_cancel' hn_bits_to_decode, ← hd]
            exact hinv.2.1
          . rw [hn_bits_in_accumulator1, mul_add, mul_one, add_assoc,
              Nat.add_sub_cancel' hn_bits_to_decode, ← hd]
            exact hinv.2.2
        . simp only [UScalar.lt_equiv, hn_bits_in_accumulator1, haccumulator1,
            Nat.testBit_shiftRight, Slice.getElem!_Nat_eq]
          intro j hj
          have : (8 * ↑num_bytes_read - ↑n_bits_in_accumulator + (↑n_bits_to_decode + j)) =
            (8 * ↑num_bytes_read - (↑n_bits_in_accumulator - ↑n_bits_to_decode) + j) := by
            simp [hinv.2.1]
            omega
          rw [hacc1 (n_bits_to_decode.val + j) (by omega), this, Slice.getElem!_Nat_eq]
        . simp only [mem_std_range_step_one, and_imp]
          intro j hj1 hj2
          rw [haccumulator1]
          simp only [Nat.testBit_shiftRight]
          dcases h : n_bits_to_decode.val + j < 32
          . simp only [mem_std_range_step_one, and_imp] at hacc2
            exact hacc2 (n_bits_to_decode.val + j) (by omega) h
          . apply Nat.testBit_eq_false_of_lt
            apply Nat.lt_of_lt_of_le _ (by scalar_tac +nonLin : 2^32 ≤ 2 ^ (n_bits_to_decode.val + j))
            scalar_tac
        . simp [hcoefficient1, hbits_to_decode, hi1, hi', hmodu32]
          unfold SpecAux.Stream.decode.length_inv at hinv
          rw [hinv.2.1] at hacc1
          have : acc.val &&& 1 <<< n_bits_to_decode.val - 1 =
            ∑ a : Fin d, (b[(d.val * i.val + a.val) / 8]!.val.testBit
              ((d.val * i.val + ↑a) % 8)).toNat * 2 ^ a.val := by
            apply Nat.eq_of_testBit_eq
            intro j
            dcases hj : j < d
            . simp only [add_tsub_cancel_right] at hacc1
              rw [SpecAux.testBit_of_sum d.val (by omega) j hj, ← hacc1 j (by scalar_tac)]
              simp only [Nat.testBit_and, Bool.and_eq_left_iff_imp]
              intro h
              tlet x := n_bits_to_decode.val
              have : ∀ x < 13, ∀ j < x, (1 <<< x - 1).testBit j = true := by brute
              exact this x (by scalar_tac) j (by scalar_tac)
            . rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
              . apply Nat.lt_of_lt_of_le _ (by scalar_tac +nonLin : 2 ^ d.val ≤ 2 ^ j)
                simp only [Slice.getElem!_Nat_eq, @SpecAux.sum_bits_lt d.val (by omega)]
              . apply Nat.and_lt_two_pow
                apply Nat.lt_of_lt_of_le _ (by scalar_tac +nonLin : 2 ^ d.val ≤ 2 ^ j)
                exact Nat.lt_of_lt_of_le (by omega) (by scalar_tac : 1 <<< n_bits_to_decode.val ≤ 2 ^ d.val)
          rw [this, ← hd]
          exact hb1 i.val hi

@[progress]
def decompress_coefficient.progress_spec (i : Usize) (d : U32) (coefficient : U32)
  (f : Array U16 256#usize) (hi : i.val < 256) (hd : 0 < d.val ∧ d.val ≤ 12)
  (hcoefficient : coefficient.val < Spec.m d) :
  ∃ err coefficient1 coefficient2 f', decompress_coefficient i d coefficient f =
    ok (err, coefficient1, f') ∧
  err = common.Error.NoError ∧
  coefficient1 = SpecAux.decompressOpt d coefficient ∧
  f' = f.set i coefficient2 ∧
  coefficient1.val = coefficient2.val := by
  unfold decompress_coefficient
  split
  . next hd =>
    let* ⟨i1, hi1⟩ ← U32.mul_spec
    . simp only [UScalar.lt_equiv, UScalar.ofNat_val_eq] at hd
      simp only [Spec.m, hd, ↓reduceIte] at hcoefficient
      have : coefficient.val < 2^12 := Nat.lt_trans hcoefficient (by scalar_tac +nonLin)
      simp_scalar
    . let* ⟨i2, hi2⟩ ← U32.sub_bv_spec
      let* ⟨coefficient2, h2⟩ ← U32.ShiftRight_spec
      let* ⟨coefficient3, h3⟩ ← U32.add_spec
      . have : i1.val < U32.max := by scalar_tac
        have : i1.val >>> i2.val ≤ i1.val := Nat.shiftRight_le ↑i1 ↑i2
        scalar_tac
      . let* ⟨coefficient4, h4⟩ ← U32.ShiftRight_IScalar_spec
        simp only [UScalar.lt_equiv, UScalar.ofNat_val_eq] at hd
        have : coefficient4 < Q := by
          simp only [Q.eq, UScalar.lt_equiv, UScalar.ofNat_val_eq]
          rw [h4, h3, h2, hi1, hi2]
          tlet x := coefficient.val
          tlet y := d.val
          have hx : x < 2^y := by simp_all [Spec.m, hd]
          simp only [Q.eq, UScalar.ofNat_val_eq, gt_iff_lt]
          have : ∀ y < 12, ∀ x < 2^y, ((x * 3329) >>> (y - 1) + 1) >>> 1 < 3329 := by brute
          exact this y hd x hx
        progress with massert_spec
        let* ⟨i3, hi3⟩ ← UScalar.cast_inBounds_spec
        let* ⟨pe_dst1, hpe_dst1⟩ ← Array.update_spec
        simp only [id_eq, Spec.Q, exists_and_left, exists_eq_left', h4, h3, h2, hi1, Q.eq,
          UScalar.ofNat_val_eq, hi2, true_and]
        constructor
        . tlet x := coefficient.val
          tlet y := d.val
          have : ∀ y < 12, ∀ x < Spec.m y,
            ↑(((x * 3329) >>> (y - 1) + 1) >>> 1) = SpecAux.decompressOpt y x := by brute
          exact this y hd x hcoefficient
        . apply Exists.intro i3
          simp [hpe_dst1, true_and, hi3, h4, h3, h2, hi1, hi2]
  . next hd =>
    replace hd : d.val = 12 := by scalar_tac
    split
    . have : Spec.m d.val ≤ Q := by simp [Spec.m, hd]
      scalar_tac
    . next hcoefficient =>
      let* ⟨i1, hi1⟩ ← UScalar.cast_inBounds_spec
      let* ⟨pe_dst1, hpe_dst1⟩ ← Array.update_spec
      unfold SpecAux.decompressOpt
      simp only [id_eq, Spec.Q, hd, lt_self_iff_false, ↓reduceIte, exists_and_left, exists_eq_left', true_and]
      apply Exists.intro i1
      simp_all

@[progress]
def poly_element_decode_and_decompress_loop.progress_spec (b : Slice U8) (d : U32)
  (f : Array U16 256#usize) (num_bytes_read : Usize) (acc : U32) (n_bits_in_accumulator : U32) (i : Usize)
  (hacc1 : (∀ j < n_bits_in_accumulator.val, acc.val.testBit j =
    b[(8 * num_bytes_read.val - n_bits_in_accumulator.val + j) / 8]!.val.testBit
      ((8 * num_bytes_read.val - n_bits_in_accumulator.val + j) % 8)))
  (hacc2 : ∀ j ∈ [n_bits_in_accumulator.val:32], acc.val.testBit j = false)
  (hb1 : ∀ i < 256,
    ∑ (a : Fin d), (Bool.toNat (b[(d.val * i + a) / 8]!.val.testBit ((d * i + a) % 8))) * 2^a.val < Spec.m d)
  (hb2 : b.length = 32 * d.val) (hi : i.val ≤ 256) (hd : 0 < d.val ∧ d.val ≤ 12)
  (hinv : SpecAux.Stream.decode.length_inv d 4 num_bytes_read n_bits_in_accumulator i) :
  ∃ res, poly_element_decode_and_decompress_loop b d f num_bytes_read acc n_bits_in_accumulator i = ok res ∧
  let s0 : SpecAux.Stream.DecodeState d 4 := {
    F := poly_to_vector (to_poly f),
    num_bytes_read := num_bytes_read.val,
    acc := acc.val,
    num_bits_in_acc := n_bits_in_accumulator.val
  }
  let s1 := SpecAux.Stream.decode_decompressOpt.recBody b.val (by simp [hb2]) s0 i.val
  res.1 = common.Error.NoError ∧
  poly_to_vector (to_poly res.2) = s1.F := by
  unfold poly_element_decode_and_decompress_loop
  simp only
  split
  . let* ⟨num_bytes_read', acc', n_bits_in_accumulator', coefficient, h1, h2, h3⟩ ←
      decode_coefficient.progress_spec b d f num_bytes_read acc n_bits_in_accumulator i hacc1 hacc2
        hinv hb1 hb2 (by simp_scalar)
    let* ⟨err, coefficient1, coefficient2, f', herr, hcoefficient', hf'⟩ ←
      decompress_coefficient.progress_spec
    let* ⟨i_succ, hi_succ⟩ ← Usize.add_spec
    let* ⟨res, hres1, hres2⟩ ← progress_spec
    simp only [hres1, hres2, true_and]
    unfold SpecAux.Stream.decode_decompressOpt.recBody SpecAux.Stream.decode_decompressOpt.body at *
    have : (256 - i.val) = (256 - (i.val + 1)) + 1 := by scalar_tac
    simp [this, List.range'_succ] at *
    have : 256 - i_succ.val = 255 - i.val := by scalar_tac
    simp [this] at *
    simp_scalar
    simp_all
    fcongr
    simp only [poly_to_vector, Spec.Q, to_poly, Fin.getElem!_fin, Array.getElem!_Nat_eq, id_eq]
    ext
    next j hj =>
    dcases hij : i = j
    . simp only [hij, Vector.Inhabited_getElem_eq_getElem!, Vector.getElem!_map_eq _ _ j hj]
      rw [Vector.getElem!_set! (by omega), Vector.getElem!_set! (by omega)]
    . simp only [Vector.Inhabited_getElem_eq_getElem!, ne_eq, hij, not_false_eq_true,
        Vector.getElem!_set!_ne, Vector.getElem!_map_eq _ _ j hj]
  . replace hi : i.val = 256 := by scalar_tac
    unfold SpecAux.Stream.decode_decompressOpt.recBody
    simp [hi]
termination_by 256 - i.val
decreasing_by scalar_decr_tac

@[progress]
def poly_element_decode_and_decompress.spec (b : Slice U8) (d : U32) (f : Array U16 256#usize)
  (hd : 0 < d.val ∧ d.val ≤ 12)
  (hb1 : ∀ i < 256,
    ∑ (a : Fin d), (Bool.toNat (b[(d.val * i + a) / 8]!.val.testBit ((d * i + a) % 8))) * 2^a.val < Spec.m d)
  (hb2 : b.length = 32 * d.val)
  (hf : ∀ i < 256, f[i]!.val = 0) :
  ∃ err f', poly_element_decode_and_decompress b d f = ok (err, f') ∧
  err = common.Error.NoError ∧
  poly_to_vector (to_poly f') = SpecAux.Stream.decode_decompressOpt d 4 b.val (by simp [hb2]) := by
  unfold poly_element_decode_and_decompress
  progress with massert_spec
  progress with massert_spec
  progress with poly_element_decode_and_decompress_loop.progress_spec as ⟨res, h1, h2⟩
  . simp [SpecAux.Stream.decode.inv, SpecAux.Stream.decode.length_inv]
  . apply Exists.intro res.1
    apply Exists.intro res.2
    simp only [← h1, h2, true_and]
    simp only [SpecAux.Stream.decode_decompressOpt]
    have heq : poly_to_vector (to_poly f) = Vector.replicate 256 0 := by
      ext
      next i hi =>
      simp_lists
      simp only [id_eq, Array.getElem!_Nat_eq] at hf
      simp [hf i hi]
    rw [heq]
    rfl

end Symcrust.SpecAux
