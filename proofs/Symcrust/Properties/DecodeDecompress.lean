import Symcrust.Code
import Symcrust.Properties.DecodeDecompressSpecAux
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

/-
/- [symcrust::ntt::poly_element_decode_and_decompress]: loop 0:
   Source: 'src/ntt.rs', lines 41:8-753:5 -/
def ntt.poly_element_decode_and_decompress_loop
  (pb_src : Slice U8) (n_bits_per_coefficient : U32)
  (pe_dst : Array U16 256#usize) (cb_src_read : Usize) (accumulator : U32)
  (n_bits_in_accumulator : U32) (i : Usize) :
  Result (common.Error × (Array U16 256#usize))
  :=
  if i < key.MLWE_POLYNOMIAL_COEFFICIENTS
  then
    do
    let (cb_src_read1, accumulator1, n_bits_in_accumulator1, coefficient) ←
      ntt.decode_coefficient pb_src n_bits_per_coefficient cb_src_read
        accumulator n_bits_in_accumulator 0#u32
    let (_, _, pe_dst1) ←
      ntt.decompress_coefficient i n_bits_per_coefficient coefficient pe_dst
    let i1 ← i + 1#usize
    ntt.poly_element_decode_and_decompress_loop pb_src n_bits_per_coefficient
      pe_dst1 cb_src_read1 accumulator1 n_bits_in_accumulator1 i1
  else
    do
    massert (n_bits_in_accumulator = 0#u32)
    let i1 ←
      (↑(UScalar.cast .U32 key.MLWE_POLYNOMIAL_COEFFICIENTS) : Result U32)
    let i2 ← i1 / 8#u32
    let i3 ← n_bits_per_coefficient * i2
    let i4 ← (↑(UScalar.cast .Usize i3) : Result Usize)
    massert (cb_src_read = i4)
    ok (common.Error.NoError, pe_dst)
partial_fixpoint
-/

@[progress]
def poly_element_decode_and_decompress_loop.progress_spec (b : Slice U8) (d : U32)
  (f : Array U16 256#usize) (num_bytes_read : Usize) (acc : U32) (n_bits_in_accumulator : U32) (i : Usize) :
  ∃ res, poly_element_decode_and_decompress_loop b d f num_bytes_read acc n_bits_in_accumulator i = ok res ∧
  res.1 = common.Error.NoError ∧
  to_poly res.2 = sorry
  -- **TODO** Make `Stream.decode_decompress` which calls `Stream.decode_decompress_recBody` so that I can
  -- coherently form this condition

  := by
  sorry

/-
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
-/

@[progress]
def poly_element_decode_and_decompress.spec (b : Slice U8) (d : U32) (f : Array U16 256#usize)
  (hd : 0 < d.val ∧ d.val ≤ 12) (hb2 : b.length = 32 * d.val) :
  ∃ res, poly_element_decode_and_decompress b d f = ok res ∧
  res.1 = common.Error.NoError ∧
  let b' := ⟨(b.val.map U8.bv).toArray, by rw [List.size_toArray, List.length_map, ← Slice.length, hb2]⟩
  to_poly res.2 = (Spec.byteDecode b').map (SpecAux.decompressOpt d) := by
  unfold poly_element_decode_and_decompress
  progress*
  sorry
