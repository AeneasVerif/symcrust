import Symcrust.Code
import Symcrust.Properties.CompressEncodeSpecAux
import Symcrust.Properties.Basic

open Aeneas
open Std
open Result

#setup_aeneas_simps

namespace Symcrust.ntt

open Result

-- TODO: put this in a common file
attribute [scalar_tac_simps] Spec.Q

-- TODO: macro for this
@[simp, scalar_tac_simps, bvify_simps]
theorem COMPRESS_MULCONSTANT.spec : COMPRESS_MULCONSTANT.val = 10321339 := by prove_eval_global

@[simp, scalar_tac_simps, bvify_simps]
theorem COMPRESS_SHIFTCONSTANT.spec : COMPRESS_SHIFTCONSTANT.val = 35 := by prove_eval_global

attribute [-progress] UScalar.cast.progress_spec
attribute [local progress] UScalar.cast_inBounds_spec

-- TODO: move
attribute [simp_scalar_simps] ZMod.val_natCast ZMod.val_intCast

@[simp, simp_scalar_simps]
theorem ZMod.cast_intCast {n : ℕ} (a : ℤ) [NeZero n] : ((a : ZMod n).cast : ℤ) = a % ↑n := by
  simp only [ZMod.cast_eq_val, ZMod.val_intCast]

set_option maxHeartbeats 2000000

-- TODO: attribute local progress for name with namespaces
theorem compress_coeff.spec_aux (d coeff : U32) (hd : d.val ≤ 12) (hc: coeff.val < Spec.Q) :
  ∃ coeff', compress_coefficient d coeff = ok coeff' ∧
  coeff'.val = SpecAux.compressOpt d.val coeff.val
  := by
  unfold compress_coefficient
  split
  . let* ⟨ coeff1, coeff1_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ mulc, mulc_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ multiplication, multiplication_post ⟩ ← U64.mul_spec
    let* ⟨ i2, i2_post ⟩ ← U32.add_spec
    let* ⟨ i3, i3_post ⟩ ← U32.sub_spec
    let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← U64.ShiftRight_spec

    -- TODO: the shape of the post-condition for UScalar.sub is annoying
    have : i3.val = 35 - i2.val := by scalar_tac
    clear i3_post

    have : i4.val < U32.max := by
      simp only [UScalarTy.U32_numBits_eq, UScalarTy.U64_numBits_eq, Nat.reduceLeDiff,
        UScalar.cast_val_mod_pow_greater_numBits_eq, COMPRESS_MULCONSTANT.spec, Nat.reduceSubDiff,
        Nat.shiftRight_eq_div_pow, i4_post_1, multiplication_post, coeff1_post, mulc_post, this,
        i2_post]
      have : 2 ^ 23 ≤ 2 ^ (34 - d.val) := by
        apply Nat.pow_le_pow_right
        . simp
        . scalar_tac
      have := @Nat.div_le_div_left (2^23) (2^(34-d.val)) (coeff.val * 10321339) (by scalar_tac) (by simp)
      scalar_tac

    let* ⟨ coefficient1, coefficient1_post ⟩ ← UScalar.cast_inBounds_spec
    let* ⟨ coefficient2, coefficient2_post ⟩ ← U32.add_spec
    let* ⟨ coefficient3, coefficient3_post_1, coefficient3_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨ i5, i5_post_1, i5_post_2 ⟩ ← U32.ShiftLeft_spec

    have : i5.val = 1 <<< d.val := by
      simp only [i5_post_1]
      apply Nat.mod_eq_of_lt
      simp only [Nat.one_shiftLeft, U32.size]
      apply Nat.pow_lt_pow_of_lt <;> scalar_tac
    clear i5_post_1

    have : 0 < i5.val := by simp [*, Nat.one_shiftLeft]

    let* ⟨ i6, i6_post ⟩ ← U32.sub_spec

    have : i6.val = 1 <<< d.val - 1 := by scalar_tac

    simp only [UScalar.val_and, this, SpecAux.compressOpt, Nat.cast_ofNat]
    simp_ifs
    have := SpecAux.compress_eq coeff.val (by scalar_tac) d.val (by scalar_tac)
    simp only [Nat.cast_ofNat] at this
    simp only [← this, SpecAux.compress, Nat.reduceSubDiff, Nat.cast_inj]

    simp only [UScalarTy.U32_numBits_eq, UScalarTy.U64_numBits_eq, Nat.reduceLeDiff,
      UScalar.cast_val_mod_pow_greater_numBits_eq, COMPRESS_MULCONSTANT.spec, Nat.reduceSubDiff, *]
  · simp only [ok.injEq, SpecAux.compressOpt, Nat.cast_ofNat, exists_eq_left']
    simp_ifs

@[progress]
theorem compress_coeff.spec (d coeff : U32) (hd : d.val ≤ 12) (hc: coeff.val < Spec.Q) :
  ∃ coeff', compress_coefficient d coeff = ok coeff' ∧
  (coeff'.val : ZMod (Spec.m d.val)) = (SpecAux.compressOpt d.val coeff.val : ZMod (Spec.m d.val)) ∧
  coeff'.val < Spec.m d.val
  := by
  progress with compress_coeff.spec_aux as ⟨ coeff', h1 ⟩
  have : NeZero (Spec.m d.val) := by constructor; simp [Spec.m]; split <;> simp
  simp only [SpecAux.compressOpt, Nat.cast_ofNat, Spec.m] at *
  split <;> simp_all only [ite_true, ite_false, Nat.cast_inj, not_lt, Int.cast_natCast, and_self]
  zify
  simp_scalar

-- TODO: move
def to_bytes (b : Slice U8) : List Byte :=
  b.val.map fun x => x.bv

@[simp, simp_lists_simps]
theorem getElem!_to_bytes (b : Slice U8) (i : ℕ) :
  (to_bytes b)[i]! = b.val[i]! := by
  simp only [to_bytes, BitVec.natCast_eq_ofNat, Bvify.UScalar.BitVec_ofNat_setWidth,
    UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv, BitVec.setWidth_eq]
  by_cases hi: i < b.length
  . simp_lists
  . simp_lists -- TODO: simp_lists accepts function definitions like `default`
    simp only [default, BitVec.zero_eq, U8.ofNat_bv, UScalarTy.U8_numBits_eq]

@[simp, simp_lists_simps]
theorem to_bytes_update {b : Slice U8} (i : Usize) (x : U8) :
  to_bytes (b.set i x) = (to_bytes b).set i x.bv := by
  simp only [to_bytes, Slice.set_val_eq, List.map_set]

@[simp, simp_lists_simps, simp_scalar_simps, scalar_tac_simps, scalar_tac to_bytes b]
theorem to_bytes_length (b : Slice U8) : (to_bytes b).length = b.length := by
  simp only [to_bytes, List.length_map, Slice.length]

-- TODO: use the Std min in Rust
@[progress]
theorem min_spec (x y : U32) :
  ∃ z, min x y = ok z ∧ -- TODO: simp lemmas for `... = toResult ...`
  z.val = Min.min x.val y.val := by
  unfold min
  split <;> progress* <;> scalar_tac

-- TODO: move
attribute [simp_ifs_simps] true_and and_true

-- TODO: use U32.sub_bv_spec by default

-- TODO: mark the bvify lemmas as simp_scalar_simps
attribute [simp_scalar_simps]
  Bvify.UScalar.BitVec_ofNat_setWidth UScalarTy.U32_numBits_eq
  Bvify.U32.UScalar_bv BitVec.setWidth_eq
  Bvify.BitVec.ofNat_shift_U32_val

-- TODO: mark the scalar lemmas as simp_scalar_simps
attribute [simp_scalar_simps] U32.ofNat_bv BitVec.ofNat_eq_ofNat

set_option maxRecDepth 512

-- TODO: move
@[simp, simp_scalar_simps]
theorem one_le_pow (a n : ℕ) (h : 0 < a) : 1 ≤ a ^ n := by
  have : 0 < a ^n := by simp [*]
  omega

@[simp, progress_simps]
theorem Slice.index_mut_SliceIndexRangeUsizeSliceInst (s : Slice α) (r : core.ops.range.Range Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSliceInst α) s r = core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s := by
  rfl

-- TODO: equivalent definitions and theorems for Array, Vec
def _root_.Aeneas.Std.Slice.setSlice! {α : Type u} (s : Slice α) (i : ℕ) (s' : List α) : Slice α :=
  ⟨s.val.setSlice! i s', by scalar_tac⟩

@[simp_lists_simps]
theorem Slice.setSlice!_getElem!_prefix {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

@[simp_lists_simps]
theorem Slice.setSlice!_getElem!_middle {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j]! = s'[j - i]! := by
  simp only [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

theorem Slice.setSlice!_getElem!_suffix {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

@[progress]
theorem core.slice.index.SliceIndexRangeUsizeSlice.index_mut.progress_spec (r : core.ops.range.Range Usize) (s : Slice α)
  (h0 : r.start ≤ r.end_) (h1 : r.end_ ≤ s.length) :
  ∃ s1 index_mut_back, core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s = ok (s1, index_mut_back) ∧
  s1.val = s.val.slice r.start r.end_ ∧
  s1.length = r.end_ - r.start ∧
  ∀ s2, s2.length = s1.length → index_mut_back s2 = s.setSlice! r.start.val s2 := by sorry

-- TODO
@[progress]
theorem core.num.U32.to_le_bytes.progress_spec (x : U32) :
  ∃ y, toResult (core.num.U32.to_le_bytes x) = ok y ∧ y.val = x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8) := by
  sorry

-- TODO: not sure about the length check
@[progress]
theorem core.slice.Slice.copy_from_slice.progress_spec (copyInst : core.marker.Copy α) (s0 s1 : Slice α)
  (h : s0.length = s1.length) :
  core.slice.Slice.copy_from_slice copyInst s0 s1 = ok s1 := by sorry

attribute [simp_scalar_simps] reduceIte

@[simp, simp_lists_simps]
theorem Array.val_to_slice {α} {n} (a : Array α n) : a.to_slice.val = a.val := by
  simp only [Array.to_slice]

@[simp, scalar_tac_simps, simp_scalar_simps, simp_lists_simps]
theorem Slice.setSlice!_length {α : Type u} (s : Slice α) (i : ℕ) (s' : List α) :
  (s.setSlice! i s').length = s.length := by
  simp only [Slice.length, Slice.setSlice!, List.setSlice!_length]

@[simp, simp_lists_simps]
theorem to_bytes_setSlice! {b : Slice U8} (i : Usize) (s : List U8) :
  to_bytes (b.setSlice! i s) = (to_bytes b).setSlice! i (s.map U8.bv) := by
  simp [to_bytes, Slice.set_val_eq, List.map_set]
  sorry

attribute [simp_lists_simps] List.map_map

-- TODO: generalize
@[simp, simp_lists_simps, simp_scalar_simps]
theorem UScalar.bv_mk {ty} : (@UScalar.bv ty) ∘ UScalar.mk = id := by rfl

@[simp, simp_lists_simps, simp_scalar_simps]
theorem U8.bv_UScalar_mk : U8.bv ∘ UScalar.mk = id := by rfl

attribute [simp_lists_simps] List.map_id_fun List.map_id_fun' id_eq

@[simp, simp_lists_simps, simp_scalar_simps, scalar_tac a.to_slice]
theorem Array.to_slice_length (a : Array α n) :
  a.to_slice.length = n := by
  simp only [Slice.length, Array.to_slice, List.Vector.length_val]

-- TODO: collapse the proof
open SpecAux in
def encode_coefficient.progress_spec_aux
  (x : U32) (d : U32) (dst : Slice U8)
  (bi : Usize) (acc : U32) (acci : U32)
  (hx : x.val < Spec.m d.val)
  (hd : 0 < d.val ∧ d.val ≤ 12)
  (hDst : dst.length = 32 * d.val)
  (hbi : bi.val + 4 ≤ dst.length)
  (hacci : acci.val < 32)
  :
  ∃ dst1 bi1 acc1 acci1,
  encode_coefficient x d dst bi acc acci =
    ok (dst1, bi1, acc1, acci1) ∧
  let s0 : Stream.EncodeState 4 := {
    b := to_bytes dst
    bi := bi.val
    acc := acc.bv
    acci := acci.val
  }
  dst1.length = dst.length ∧
  -- It is actually more natural to write the equality in this direction
  Stream.encode.body d.val x.val s0 = { b := to_bytes dst1, bi := bi1.val, acc := acc1.bv, acci := acci1.val }
  := by
  -- The proof - TODO: collapse
  unfold Symcrust.ntt.encode_coefficient
  let* ⟨ i, i_post ⟩ ← U32.sub_spec
  let* ⟨ n_bits_to_encode, n_bits_to_encode_post ⟩ ← min_spec
  let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← U32.ShiftLeft_spec
  let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← U32.sub_bv_spec
  · -- TODO: we want to be able to do simp [*]: change the postcondition of sub
    simp [i1_post_1, n_bits_to_encode_post, U32.size]
    simp [Nat.shiftLeft_eq_mul_pow]
    have : 2^Min.min d.val i.val < 2^U32.numBits := by simp_scalar
    simp_scalar
  let* ⟨ bits_to_encode, bits_to_encode_post_1, bits_to_encode_post_2 ⟩ ← UScalar.and_spec
  let* ⟨ n_bits_in_coefficient1, n_bits_in_coefficient1_post ⟩ ← U32.sub_spec
  let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U32.ShiftLeft_spec
  let* ⟨ accumulator1, accumulator1_post_1, accumulator1_post_2 ⟩ ← UScalar.or_spec
  let* ⟨ n_bits_in_accumulator1, n_bits_in_accumulator1_post ⟩ ← U32.add_spec
  split
  . let* ⟨ i4, i4_post ⟩ ← Usize.add_spec
    -- TODO: improve code extraction to have better names when using tuples
    let* ⟨ dst1, index_mut_back, dst1_post_1, dst1_post_2 ⟩ ←
      core.slice.index.SliceIndexRangeUsizeSlice.index_mut.progress_spec
    let* ⟨ a, a_post ⟩ ← core.num.U32.to_le_bytes.progress_spec
    let* ⟨ s1, s1_post ⟩ ← Array.to_slice.progress_spec
    have : dst1.length = s1.length := by
      -- TODO: the simp_all in scalar_tac fails because of the posts of sub
      clear i2_post_1 n_bits_in_coefficient1_post
      scalar_tac
    let* ⟨ ⟩ ← core.slice.Slice.copy_from_slice.progress_spec
    let* ⟨ accumulator2, accumulator2_post_1, accumulator2_post_2 ⟩ ← U32.ShiftRight_spec
    simp only [Slice.length, Stream.encode.body, Nat.reduceMul, ZMod.val_natCast,
      BitVec.shiftLeft_sub_one_eq_mod, BitVec.ofNat_eq_ofNat, exists_and_left, exists_eq_left']
    -- TODO: the postcondition of subtraction is annoying, we should change it
    have n_bits_in_coefficient1_post' : n_bits_in_coefficient1.val = d.val - n_bits_to_encode.val := by scalar_tac
    clear i2_post_1 n_bits_in_coefficient1_post
    simp only [*]
    simp_scalar
    simp_lists [*]
    simp_scalar
  . simp [Stream.encode.body]
    simp_ifs
    -- TODO: the postcondition of subtraction is annoying, we should change it
    clear i2_post_1 n_bits_in_coefficient1_post
    simp only [*, Stream.encode.body.length_spec]
    simp_scalar

open SpecAux in
@[progress]
def encode_coefficient.progress_spec
  (x : U32) (d : U32) (dst : Slice U8)
  (bi : Usize) (acc : U32) (acci : U32)
  (hx : x.val < Spec.m d.val)
  (hd : 0 < d.val ∧ d.val ≤ 12)
  (i : Usize) -- this is a ghost value
  (hi : i.val < 256)
  (hinv : Stream.encode.length_inv d.val 4 (to_bytes dst) bi.val acci.val i.val)
  :
  ∃ dst1 bi1 acc1 acci1,
  encode_coefficient x d dst bi acc acci =
    ok (dst1, bi1, acc1, acci1) ∧
  let s0 : Stream.EncodeState 4 := {
    b := to_bytes dst
    bi := bi.val
    acc := acc.bv
    acci := acci.val
  }
  dst1.length = dst.length ∧
  Stream.encode.body d.val x.val s0 = { b := to_bytes dst1, bi := bi1.val, acc := acc1.bv, acci := acci1.val} ∧
  Stream.encode.length_inv d.val 4 (to_bytes dst1) bi1.val acci1.val (i + 1)
  := by
  -- The length invariant is preserved
  let s0 : Stream.EncodeState 4 := {
    b := to_bytes dst
    bi := bi.val
    acc := acc.bv
    acci := acci.val
  }
  have hinv1 := @Stream.encode.body.length_spec i.val d.val 4 x.val s0 _ hinv (by omega) (by omega) (by omega)
  simp only at hinv1

  -- We need those arithmetic facts for the safety
  have : dst.length = 32 * d.val ∧ bi.val + 4 ≤ dst.length ∧ acci.val < 32 := by
    unfold Stream.encode.length_inv at hinv

    have : bi.val + 4 ≤ dst.length := by
      have := calc
        (d.val * i.val) / 32 ≤ (d.val * 255) / 32 := by
          have : d.val * i.val ≤ d.val * 255 := by simp_scalar
          simp_scalar
        _ = 8 * d.val - 1 := by simp_scalar

      have := calc
        bi.val = 4 * ((d.val * i.val) / 32) := by omega
        _ ≤ 4 * (8 * d.val - 1) := by omega
        _ = 32 * d.val - 4 := by omega

      have : bi.val + 4 ≤ 32 * d.val := by omega

      scalar_tac

    simp_scalar

  progress with encode_coefficient.progress_spec_aux as ⟨ dst1, bi1, acc1, acci1, _, h ⟩
  -- The following is annoying - note that it is proven by `grind`
  simp only [Slice.length, Nat.reduceMul, exists_and_left, exists_eq_left']
  split_conjs <;> try tauto
  simp_all +zetaDelta only

attribute [local progress] wfArray_update wfArray_index

open SpecAux in
@[progress]
def poly_element_compress_and_encode_loop.progress_spec
  (f : Array U16 256#usize) (d : U32)
  (b : Slice U8) (bi : Usize) (acc : U32)
  (acci : U32) (i : Usize)
  (hwf : wfArray f)
  (hi : i.val ≤ 256)
  (hinv : Stream.encode.length_inv d.val 4 (to_bytes b) bi.val acci.val i.val)
  (hd : 0 < d.val ∧ d.val ≤ 12)
  :
  ∃ b1, poly_element_compress_and_encode_loop f d b bi acc acci i = ok b1 ∧
  let s0 : Stream.EncodeState 4 := {
    b := to_bytes b
    bi := bi.val
    acc := acc.bv
    acci := acci.val
  }
  let s1 := Stream.compressOpt_encode.recBody d.val (to_poly f) s0 i.val
  b1.length = b.length ∧
  s1.b = to_bytes b1 ∧
  s1.bi = b.length ∧
  s1.acci = 0
  := by
  unfold poly_element_compress_and_encode_loop
  simp only
  split
  . let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← wfArray_index
    let* ⟨ ⟩ ← massert_spec
    let* ⟨ coefficient1, coefficient1_post_1, coefficient1_post_2 ⟩ ← compress_coeff.spec
    let* ⟨ b1, bi1, acci1, i1, h0, h1, h2 ⟩ ← encode_coefficient.progress_spec
    · scalar_tac -- TODO: we shouldn't need this
    let* ⟨ i2, i2_post ⟩ ← Usize.add_spec
    let* ⟨ res, res_post, h5, h6, h7 ⟩ ← progress_spec
    -- We need to unfold one step of `List.foldl` in the goal, before simplifying everything
    unfold Stream.compressOpt_encode.recBody Stream.compressOpt_encode.body at *
    simp_scalar
    have : (256 - i.val) = (256 - (i.val + 1)) + 1 := by scalar_tac
    simp [this, List.range'_succ] at *
    have : 256 - i2.val = 255 - i.val := by scalar_tac
    simp [this] at *
    simp_scalar
    simp_all
  . unfold Stream.compressOpt_encode.recBody
    have hi : i.val = 256 := by scalar_tac
    simp_scalar
    simp only [getElem!_to_poly, id_eq, List.range'_zero, List.foldl_nil, Slice.length, true_and]
    simp [Stream.encode.length_inv, hi] at hinv
    revert hinv
    simp_scalar
    intro hinv
    let* ⟨ ⟩ ← massert_spec
    simp_scalar

termination_by 256 - i.val
decreasing_by scalar_decr_tac

open SpecAux in
@[progress]
def poly_element_compress_and_encode.spec (f : Array U16 256#usize) (d : U32) (b : Slice U8)
  (hd : 0 < d.val ∧ d.val ≤ 12)
  (hf : wfArray f)
  (hb1 : ∀ i < b.length, b[i]! = 0#u8)
  (hb2 : b.length = 32 * d.val)
  :
  ∃ b1, poly_element_compress_and_encode f d b = ok b1 ∧
  to_bytes b1 = Stream.compressOpt_encode d.val 4 (to_poly f) := by
  unfold poly_element_compress_and_encode
  progress*
  . simp only [Stream.encode.length_inv, to_bytes_length, Slice.length, UScalar.ofNat_val_eq,
    zero_le, mul_zero, Nat.reduceMul, Nat.zero_div, Nat.zero_mod, and_self, hb2]
  . have : to_bytes b = List.replicate (32 * ↑d) 0#8 := by
      rw [List.eq_iff_forall_eq_getElem!]
      simp only [to_bytes_length, Slice.length, hb2, List.length_replicate, getElem!_to_bytes,
        BitVec.natCast_eq_ofNat, Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U8_numBits_eq,
        Bvify.U8.UScalar_bv, BitVec.setWidth_eq, true_and]
      intros i hi
      simp only [Slice.length, Slice.getElem!_Nat_eq] at hb1
      simp_lists [hb1]
      simp only [U8.ofNat_bv, UScalarTy.U8_numBits_eq]
    simp_all [Stream.compressOpt_encode]

end Symcrust.ntt
