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

@[progress]
def decode_coefficient.progress_spec (b : Slice U8) (d : U32) (f : Array U16 256#usize)
  (num_bytes_read : Usize) (acc : U32) (n_bits_in_accumulator : U32) (i : Usize)
  (hb2 : b.length = 32 * d.val) (hi : i.val < 256) :
  ∃ num_bytes_read' acc' n_bits_in_accumulator' coefficient,
    decode_coefficient b d num_bytes_read acc n_bits_in_accumulator (UScalar.ofNat 0) =
      ok (num_bytes_read', acc', n_bits_in_accumulator', coefficient) ∧
  let s0 : SpecAux.Stream.DecodeState d 4 := {
    F := poly_to_vector (to_poly f),
    num_bytes_read := num_bytes_read.val,
    acc := acc.val,
    num_bits_in_acc := n_bits_in_accumulator.val
  }
  let s1 := SpecAux.Stream.decode_decompressOpt.recBody b.val (by simp [hb2]) s0 i.val
  coefficient.val = s1.F[i.val]! ∧
  num_bytes_read' = s1.num_bytes_read ∧
  acc' = s1.acc ∧
  n_bits_in_accumulator' = s1.num_bits_in_acc := by
  sorry

@[progress]
def decompress_coefficient.progress_spec (i : Usize) (d : U32) (coefficient : U32)
  (f : Array U16 256#usize) (hi : i.val < 256) :
  ∃ err coefficient' f', decompress_coefficient i d coefficient f = ok (err, coefficient', f') ∧
  err = common.Error.NoError ∧
  coefficient' = SpecAux.decompressOpt d coefficient ∧
  f' = f.set i (UScalar.ofNat coefficient'.val sorry) -- **TODO** Is there a way to avoid putting in a long proof here?
  := by
  sorry

@[progress]
def poly_element_decode_and_decompress_loop.progress_spec (b : Slice U8) (d : U32)
  (f : Array U16 256#usize) (num_bytes_read : Usize) (acc : U32) (n_bits_in_accumulator : U32) (i : Usize)
  (hb2 : b.length = 32 * d.val) (hi : i.val ≤ 256) :
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
  . let* ⟨ num_bytes_read', acc', n_bits_in_accumulator', coefficient, h0, h1, h2, h3 ⟩ ←
      decode_coefficient.progress_spec b d f num_bytes_read acc n_bits_in_accumulator i hb2 (by simp_scalar)
    let* ⟨ err, coefficient', f', herr, hcoefficient', hf' ⟩ ← decompress_coefficient.progress_spec
    let* ⟨ i_succ, hi_succ ⟩ ← Usize.add_spec
    let* ⟨ res, hres1, hres2 ⟩ ← progress_spec
    simp only [hres1, hres2, true_and]
    sorry
  . sorry
termination_by 256 - i.val
decreasing_by scalar_decr_tac

@[progress]
def poly_element_decode_and_decompress.spec (b : Slice U8) (d : U32) (f : Array U16 256#usize)
  (hd : 0 < d.val ∧ d.val ≤ 12) (hb1 : sorry) (hb2 : b.length = 32 * d.val)
  (hf : ∀ i < 256, f[i]!.val = 0) :
  ∃ err f', poly_element_decode_and_decompress b d f = ok (err, f') ∧
  err = common.Error.NoError ∧
  poly_to_vector (to_poly f') = SpecAux.Stream.decode_decompressOpt d 4 b.val (by simp [hb2]) := by
  unfold poly_element_decode_and_decompress
  progress with massert_spec
  progress with massert_spec
  progress with poly_element_decode_and_decompress_loop.progress_spec as ⟨res, h1, h2⟩
  apply Exists.intro res.1
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
