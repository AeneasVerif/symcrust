import Symcrust.Code
import Symcrust.Properties.CompressSpecAux

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
theorem COMPRESS_MULCONSTANT.spec : ntt.COMPRESS_MULCONSTANT.val = 10321339 := by prove_eval_global

@[simp, scalar_tac_simps, bvify_simps]
theorem COMPRESS_SHIFTCONSTANT.spec : ntt.COMPRESS_SHIFTCONSTANT.val = 35 := by prove_eval_global

@[simp, scalar_tac_simps, bvify_simps]
theorem Q.spec : ntt.Q.val = 3329 := by prove_eval_global

attribute [-progress] UScalar.cast.progress_spec
attribute [local progress] UScalar.cast_inBounds_spec

set_option maxHeartbeats 2000000

-- TODO: attribute local progress for name with namespaces
def compress_coeff.spec (d coeff : U32) (hd : d.val ≤ 12) (hc: coeff.val < Spec.Q) :
  ∃ coeff', compress_coefficient d coeff = ok coeff' ∧
  coeff'.val = SpecAux.compressOpt d.val coeff.val ∧
  coeff'.val < 2^d.val := by
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
      simp [*, Nat.shiftRight_eq_div_pow]
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

    split_conjs
    . simp [this, SpecAux.compressOpt]
      simp_ifs
      have := SpecAux.compress_eq coeff.val (by scalar_tac) d.val (by scalar_tac)
      simp only [Nat.cast_ofNat] at this
      simp only [← this, SpecAux.compress, Nat.reduceSubDiff, Nat.cast_inj]

      simp [*]
    . simp only [UScalar.val_and, this]
      simp only [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
      apply Nat.mod_lt
      simp
  · simp [SpecAux.compressOpt]
    simp_ifs
    have : d.val = 12 := by scalar_tac
    simp [this]
    scalar_tac



end Symcrust.ntt
