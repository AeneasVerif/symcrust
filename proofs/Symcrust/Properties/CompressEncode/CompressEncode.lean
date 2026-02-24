import Symcrust.Code
import Symcrust.Properties.CompressEncode.Compress
import Symcrust.Properties.Basic

open Aeneas
open Std
open Result

/-!
This file contains theorems about `Symcrust.Spec.byteEncode` and `Symcrust.Spec.compress` defined in
Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to (4.7) (Compress) and Algorithm 5 (ByteEncode).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.compress` and `Symcrust.Spec.byteEncode`.
    - `Lean spec (functional)` corresponds to `Symcrust.Spec.compress` and `Target.byteEncode`.
      - `Lean spec (monadic)` and `Lean spec (functional)` coincide for Compress because the natural
        Lean translation of Nist's Compress is already functional.
    - `Auxiliary spec` corresponds to `Symcrust.SpecAux.compress` and `Stream.encode`.
      - Additionally, `Auxiliary spec` for the combination of compress and encode that appears in the Rust
        code corresponds to `Stream.compressOpt_encode`.
    - `Aeneas translation` corresponds to `Symcrust.ntt.poly_element_compress_and_encode`.
    - `⟷₃` is bundled together with `⟷₂` in the form of `compress_eq` and `Stream.encode.spec`.
    - `⟷₄` corresponds to `Symcrust.SpecAux.poly_element_compress_and_encode.spec`.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Result Symcrust.ntt

attribute [-progress] UScalar.cast.progress_spec U32.sub_spec
attribute [local progress] UScalar.cast_inBounds_spec U32.sub_bv_spec

set_option maxHeartbeats 2000000

-- TODO: attribute local progress for name with namespaces
theorem compress_coeff.spec_aux (d coeff : U32) (hd : d.val ≤ 12) (hc: coeff.val < Spec.Q) :
  compress_coefficient d coeff ⦃ coeff' =>
    coeff'.val = SpecAux.compressOpt d.val coeff.val ⦄
  := by
  unfold compress_coefficient
  split
  . let* ⟨ coeff1, coeff1_post ⟩ ← UScalar.cast_inBounds_spec
    let* ⟨ mulc, mulc_post ⟩ ← UScalar.cast_inBounds_spec
    let* ⟨ multiplication, multiplication_post ⟩ ← U64.mul_spec
    let* ⟨ i2, i2_post ⟩ ← U32.add_spec
    let* ⟨ i3, i3_post ⟩ ← U32.sub_spec
    let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← U64.ShiftRight_spec

    -- TODO: the shape of the post-condition for UScalar.sub is annoying
    have : i3.val = 35 - i2.val := by scalar_tac
    clear i3_post

    have : i4.val < U32.max := by
      simp only [COMPRESS_MULCONSTANT.spec, Nat.reduceSubDiff, Nat.shiftRight_eq_div_pow,
        i4_post_1, multiplication_post, coeff1_post, mulc_post, this, i2_post]
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

    simp only [COMPRESS_MULCONSTANT.spec, Nat.reduceSubDiff, *]
  · simp only [compressOpt, Spec.Q, Nat.cast_ofNat, WP.spec_ok, right_eq_ite_iff]
    scalar_tac

@[progress]
theorem compress_coeff.spec (d coeff : U32) (hd : d.val ≤ 12) (hc: coeff.val < Spec.Q) :
  compress_coefficient d coeff ⦃ coeff' =>
    (coeff'.val : ZMod (Spec.m d.val)) = (SpecAux.compressOpt d.val coeff.val : ZMod (Spec.m d.val)) ∧
    coeff'.val < Spec.m d.val ⦄
  := by
  progress with compress_coeff.spec_aux as ⟨ coeff', h1 ⟩
  have : NeZero (Spec.m d.val) := by constructor; simp [Spec.m]; split <;> simp
  simp only [SpecAux.compressOpt, Nat.cast_ofNat, Spec.m] at *
  split <;> simp_all only [ite_true, ite_false, Nat.cast_inj, Std.not_lt, Int.cast_natCast, and_self]
  zify
  simp_scalar

theorem encode_coefficient.progress_spec_aux
  (x : U32) (d : U32) (dst : Aeneas.Std.Slice U8)
  (bi : Usize) (acc : U32) (acci : U32)
  (hx : x.val < Spec.m d.val)
  (hd : 0 < d.val ∧ d.val ≤ 12)
  (hDst : dst.length = 32 * d.val)
  (hbi : bi.val + 4 ≤ dst.length)
  (hacci : acci.val < 32)
  :
  encode_coefficient x d dst bi acc acci ⦃ dst1 bi1 acc1 acci1 =>
    let s0 : Stream.EncodeState 4 := {
      b := to_bytes dst
      bi := bi.val
      acc := acc.bv
      acci := acci.val
    }
    dst1.length = dst.length ∧
    -- It is actually more natural to write the equality in this direction
    Stream.encode.body d.val x.val s0 = { b := to_bytes dst1, bi := bi1.val, acc := acc1.bv, acci := acci1.val }
    ⦄
  := by
  have : 1 ≤ 2 ^ Min.min d.val (32 - acci.val) % U32.size := by
    have : 2 ^ Min.min d.val (32 - acci.val) < 2^U32.numBits := by simp_scalar
    simp_scalar
  unfold Symcrust.ntt.encode_coefficient
  progress*
  . simp only [Slice.length, Stream.encode.body, Nat.reduceMul, ZMod.val_natCast,
      BitVec.shiftLeft_sub_one_eq_mod, BitVec.ofNat_eq_ofNat]
    simp only [*]
    simp_scalar
    simp_lists [*]
    simp_scalar
  . simp [Stream.encode.body]
    simp_ifs
    simp only [*]
    simp_scalar

@[progress]
theorem encode_coefficient.progress_spec
  (x : U32) (d : U32) (dst : Aeneas.Std.Slice U8)
  (bi : Usize) (acc : U32) (acci : U32)
  (hx : x.val < Spec.m d.val)
  (hd : 0 < d.val ∧ d.val ≤ 12)
  (i : Usize) -- this is a ghost value
  (hi : i.val < 256)
  (hinv : Stream.encode.length_inv d.val 4 (to_bytes dst) bi.val acci.val i.val)
  :
  encode_coefficient x d dst bi acc acci ⦃ dst1 bi1 acc1 acci1 =>
    let s0 : Stream.EncodeState 4 := {
      b := to_bytes dst
      bi := bi.val
      acc := acc.bv
      acci := acci.val
    }
    dst1.length = dst.length ∧
    Stream.encode.body d.val x.val s0 = { b := to_bytes dst1, bi := bi1.val, acc := acc1.bv, acci := acci1.val} ∧
    Stream.encode.length_inv d.val 4 (to_bytes dst1) bi1.val acci1.val (i + 1)
    ⦄
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
  simp only [Slice.length]
  split_conjs <;> try tauto
  simp_all +zetaDelta only

attribute [local progress] wfArray_update wfArray_index

@[progress]
theorem poly_element_compress_and_encode_loop.progress_spec
  (f : Array U16 256#usize) (d : U32)
  (b : Aeneas.Std.Slice U8) (bi : Usize) (acc : U32)
  (acci : U32) (i : Usize)
  (hwf : wfArray f)
  (hi : i.val ≤ 256)
  (hinv : Stream.encode.length_inv d.val 4 (to_bytes b) bi.val acci.val i.val)
  (hd : 0 < d.val ∧ d.val ≤ 12)
  :
  poly_element_compress_and_encode_loop f d b bi acc acci i ⦃ b1 =>
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
    s1.acci = 0 ⦄
  := by
  unfold poly_element_compress_and_encode_loop
  simp only
  split
  . let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← wfArray_index
    let* ⟨ ⟩ ← massert_spec
    let* ⟨ coefficient1, coefficient1_post_1, coefficient1_post_2 ⟩ ← compress_coeff.spec
    let* ⟨ b1, bi1, acci1, i1, h0, h1, h2 ⟩ ← encode_coefficient.progress_spec
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
    simp only [getElem!_to_poly, List.range'_zero, List.foldl_nil]
    simp [Stream.encode.length_inv, hi] at hinv
    revert hinv
    simp_scalar
    intro hinv
    let* ⟨ ⟩ ← massert_spec
    simp_scalar

termination_by 256 - i.val
decreasing_by scalar_decr_tac

@[progress]
theorem poly_element_compress_and_encode.spec (f : Array U16 256#usize) (d : U32) (b : Aeneas.Std.Slice U8)
  (hd : 0 < d.val ∧ d.val ≤ 12)
  (hf : wfArray f)
  (hb1 : ∀ i < b.length, b[i]! = 0#u8)
  (hb2 : b.length = 32 * d.val)
  :
  poly_element_compress_and_encode f d b ⦃ b1 =>
    to_bytes b1 = Stream.compressOpt_encode d.val 4 (to_poly f) ⦄ := by
  unfold poly_element_compress_and_encode
  progress*
  . simp only [Stream.encode.length_inv, to_bytes_length, Slice.length, UScalar.ofNatCore_val_eq,
    zero_le, mul_zero, Nat.reduceMul, Nat.zero_div, Nat.zero_mod, and_self, hb2]
  . have : to_bytes b = List.replicate (32 * ↑d) 0#8 := by
      rw [List.eq_iff_forall_eq_getElem!]
      simp only [to_bytes_length, Slice.length, hb2, List.length_replicate, getElem!_to_bytes,
        BitVec.natCast_eq_ofNat, Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U8_numBits_eq,
        Bvify.U8.UScalar_bv, BitVec.setWidth_eq, true_and]
      intros i hi
      simp_lists_scalar [hb1]
    simp_all [Stream.compressOpt_encode]

end Symcrust.SpecAux
