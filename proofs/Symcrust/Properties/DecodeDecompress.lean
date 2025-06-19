import Symcrust.Code
import Symcrust.Properties.DecodeDecompressSpecAux
import Symcrust.Properties.CompressEncode -- This file has `Symcrust.ntt.min_spec`
import Symcrust.Properties.Basic

open Aeneas
open Std
open Result

#setup_aeneas_simps

namespace Symcrust.ntt

open Result

attribute [-progress] UScalar.cast.progress_spec U32.sub_spec
attribute [local progress] UScalar.cast_inBounds_spec U32.sub_bv_spec

set_option maxHeartbeats 2000000

@[progress]
def decode_coefficient.progress_spec (b : Slice U8) (d : U32) (f : Array U16 256#usize)
  (num_bytes_read : Usize) (acc : U32) (n_bits_in_accumulator : U32) (i : Usize)
  (hacc1 : (∀ j < n_bits_in_accumulator.val, acc.val.testBit j =
    b[(8 * num_bytes_read.val - n_bits_in_accumulator.val + j) / 8]!.val.testBit
      ((8 * num_bytes_read.val - n_bits_in_accumulator.val + j) % 8)))
  (hacc2 : ∀ j ∈ [n_bits_in_accumulator.val:32], acc.val.testBit j = false)
  (hinv : SpecAux.Stream.decode.length_inv d 4 num_bytes_read n_bits_in_accumulator i)
  -- **TODO** `hb1` is needed to make `hacc` useful
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
  . next hn_bits_in_accumulator =>
    sorry -- Early load
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
      . sorry -- Late load
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
        split_conjs -- Will take this away, just focusing on the first subgoal for ease of readability
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
          -- This requires the complicated `hb1`
          sorry

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
        hinv hb2 (by simp_scalar)
    let* ⟨err, coefficient1, coefficient2, f', herr, hcoefficient', hf'⟩ ← decompress_coefficient.progress_spec
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
    -- Automation note: It would be nice if automation could produce this subgoal
    /- Attempting to perform `congr` results in maximum recursion depth being reached.
       I'm not sure whether that is an indication that it is simply too hard to find this rewrite,
       or whether there is room for improvement -/
    have :
      ((poly_to_vector (to_poly f)).set! ↑i ↑coefficient).set! i.val
        (ZMod.val (SpecAux.decompressOpt ↑d ↑coefficient)) =
      poly_to_vector (Vector.set! (to_poly f) (↑i) (SpecAux.decompressOpt ↑d ↑coefficient)) := by
      simp only [poly_to_vector, Spec.Q, to_poly, Fin.getElem!_fin, Array.getElem!_Nat_eq, id_eq]
      ext
      next j hj =>
      dcases hij : i = j
      . simp only [hij, Vector.Inhabited_getElem_eq_getElem!, Vector.getElem!_map_eq _ _ j hj]
        rw [Vector.getElem!_set! (by omega), Vector.getElem!_set! (by omega)]
      . simp only [Vector.Inhabited_getElem_eq_getElem!, ne_eq, hij, not_false_eq_true,
          Vector.getElem!_set!_ne, Vector.getElem!_map_eq _ _ j hj]
    rw [this]
  . replace hi : i.val = 256 := by scalar_tac
    progress with massert_spec
    . unfold SpecAux.Stream.decode.length_inv at hinv
      sorry -- **TODO** Discuss the necessity of proving this debug_assert statement
    . let* ⟨i1, hi1⟩ ← UScalar.cast_inBounds_spec
      let* ⟨i2, hi2⟩ ← U32.div_spec
      let* ⟨i3, hi3⟩ ← U32.mul_spec
      let* ⟨i4, hi4⟩ ← UScalar.cast_inBounds_spec
      progress with massert_spec
      . simp_all
        sorry -- **TODO** Discuss the necessity of proving this debug_assert statement
      . unfold SpecAux.Stream.decode_decompressOpt.recBody
        simp [hi]
termination_by 256 - i.val
decreasing_by scalar_decr_tac

@[progress]
def poly_element_decode_and_decompress.spec (b : Slice U8) (d : U32) (f : Array U16 256#usize)
  (hd : 0 < d.val ∧ d.val ≤ 12) (hb2 : b.length = 32 * d.val)
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
