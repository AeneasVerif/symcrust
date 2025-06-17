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
  let s1 :=
    {
      F := (poly_to_vector (to_poly f)).set i.val coefficient,
      num_bytes_read := num_bytes_read',
      acc := acc',
      num_bits_in_acc := n_bits_in_accumulator'
    }
  SpecAux.Stream.decode.body b.val (by simp [hb2]) s0 i.val = s1 ∧
  SpecAux.Stream.decode.length_inv d 4 num_bytes_read' n_bits_in_accumulator' (i + 1)
  := by
  sorry

@[progress]
def decompress_coefficient.progress_spec (i : Usize) (d : U32) (coefficient : U32)
  (f : Array U16 256#usize) (hi : i.val < 256) :
  ∃ err coefficient1 coefficient2 f', decompress_coefficient i d coefficient f = ok (err, coefficient1, f') ∧
  err = common.Error.NoError ∧
  coefficient1 = SpecAux.decompressOpt d coefficient ∧
  f' = f.set i coefficient2 ∧
  coefficient1.val = coefficient2.val
  := by
  sorry

set_option pp.analyze false in
@[progress]
def poly_element_decode_and_decompress_loop.progress_spec (b : Slice U8) (d : U32)
  (f : Array U16 256#usize) (num_bytes_read : Usize) (acc : U32) (n_bits_in_accumulator : U32) (i : Usize)
  (hb2 : b.length = 32 * d.val) (hi : i.val ≤ 256) (hnum_bytes_read : 8 * num_bytes_read.val ≤ 256 * d)
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
  . let* ⟨ num_bytes_read', acc', n_bits_in_accumulator', coefficient, h1, h2 ⟩ ←
      decode_coefficient.progress_spec b d f num_bytes_read acc n_bits_in_accumulator i hb2 (by simp_scalar)
    let* ⟨ err, coefficient1, coefficient2, f', herr, hcoefficient', hf' ⟩ ← decompress_coefficient.progress_spec
    let* ⟨ i_succ, hi_succ ⟩ ← Usize.add_spec
    let* ⟨ res, hres1, hres2 ⟩ ← progress_spec
    . unfold SpecAux.Stream.decode.length_inv at hinv
       -- I think that in order to prove this, we need `hnum_bytes_read` to be part of
       -- `SpecAux.Stream.decode.length_inv`
      sorry
    simp only [hres1, hres2, true_and]
    unfold SpecAux.Stream.decode_decompressOpt.recBody SpecAux.Stream.decode_decompressOpt.body at *
    have : (256 - i.val) = (256 - (i.val + 1)) + 1 := by scalar_tac
    simp [this, List.range'_succ] at *
    have : 256 - i_succ.val = 255 - i.val := by scalar_tac
    simp [this] at *
    simp_scalar
    simp_all
    -- Automation note: It would be nice if automation could produce this subgoal
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
      scalar_tac
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
