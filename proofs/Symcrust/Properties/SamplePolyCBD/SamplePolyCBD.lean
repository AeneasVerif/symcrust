import Symcrust.Spec
import Symcrust.Code.Funs
import Symcrust.Properties.Basic
import Symcrust.Brute
import Symcrust.Properties.SamplePolyCBD.Target2Proof

/-!
This file contains theorems about `Symcrust.Spec.samplePolyCBD` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to Algorithm 8 (SamplePolyCBD).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.samplePolyCBD`.
    - `Lean spec (functional)` corresponds to `Target.samplePolyCBD`.
      - The theorem that mathematically characterizes `Target.samplePolyCBD` is `Target.samplePolyCBD.spec`.
    - `Auxiliary spec` corresponds to `Target2.samplePolyCBD`.
    - `Aeneas translation` corresponds to `Symcrust.ntt.poly_element_sample_cbd_from_bytes`.
    - `⟷₂` corresponds to `Target.samplePolyCBD.eq_spec`.
    - `⟷₃` is bundled with `⟷₂` in the form of `Target2.samplePolyCBD.spec`.
    - `⟷₄` corresponds to `Symcrust.SpecAux.poly_element_sample_cbd_from_bytes.spec`.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec Symcrust.ntt
open Aeneas Aeneas.Std Aeneas.SRRange Result

set_option maxHeartbeats 1000000

@[progress]
def ntt.poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop.spec (f : Array U16 256#usize)
  (i j : Usize) (sample_bits : U32) (hi1 : i.val < 256) (hi2 : 8 ∣ i.val) (hj : j.val ≤ 8) :
  ∃ f' sample_bits',
  poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop f i sample_bits j = ok (f', sample_bits') ∧
  to_poly f' = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i j.val sample_bits).1 ∧
  sample_bits'.bv = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i j.val sample_bits).2 := by
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop Target2.samplePolyCBD.eta2_loop.inner_loop
  dcases hj : j < 8#usize
  . have hj' : j.val < 8 := by simp_all
    simp only [hj, ↓reduceIte, Q.eq, UScalar.lt_equiv, UScalar.ofNat_val_eq, Spec.Q, hj',
      BitVec.natCast_eq_ofNat, Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U32_numBits_eq,
      Bvify.U32.UScalar_bv, BitVec.setWidth_eq]
    let* ⟨ coefficient, coefficient_post_1, coefficient_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ sample_bits1, sample_bits1_post_1, sample_bits1_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨ coefficient1, coefficient1_post ⟩ ← core.num.U32.wrapping_sub.progress_spec
    let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ coefficient2, coefficient2_post ⟩ ← core.num.U32.wrapping_add.progress_spec
    let* ⟨ ⟩ ← massert_spec
    · simp only [U32.wrapping_add_val_eq, U32.wrapping_sub_val_eq, UScalar.val_and,
        UScalar.ofNat_val_eq, UScalar.size_UScalarTyU32, Nat.mod_add_mod, coefficient2_post,
        coefficient1_post, i1_post_1, coefficient_post_1, i2_post_1, i4_post_1, i3_post_1]
      olet hsample_bits' : sample_bits' := sample_bits.val &&& 15
      replace hsample_bits' : sample_bits' < 16 := by
        apply Nat.lt_succ_of_le
        rw [hsample_bits']
        exact Nat.and_le_right
      revert sample_bits'
      brute
    let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
    let* ⟨ i6, i6_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ pe_dst1, pe_dst1_post ⟩ ← Array.update_spec
    let* ⟨ j1, j1_post ⟩ ← Usize.add_spec
    let* ⟨ res_1, res_2, res_post_1, res_post_2 ⟩ ← spec
    apply Exists.intro res_1
    apply Exists.intro res_2
    simp only [Spec.Q, to_poly_set, BitVec.natCast_eq_ofNat, Bvify.BitVec.ofNat_shift_U32_val,
      true_and, res_post_1, pe_dst1_post, i6_post, coefficient2_post, coefficient1_post, i5_post,
      j1_post, sample_bits1_post_1, res_post_2]
    have h1 :
      UScalar.cast UScalarTy.U16 (core.num.U32.wrapping_add (core.num.U32.wrapping_sub i1 i2) i4) =
      (Target2.samplePolyCBD.eta2_loop.inner_loop.next_coefficient (↑i) (↑j) sample_bits.bv).2 := by
      simp only [core.num.U32.wrapping_sub, UScalar.wrapping_sub, UScalarTy.U32_numBits_eq,
        Bvify.U32.UScalar_bv, i1_post_2, coefficient_post_2, U32.ofNat_bv, i2_post_2,
        Target2.samplePolyCBD.eta2_loop.inner_loop.next_coefficient, BitVec.ofNat_eq_ofNat, Q.eq,
        UScalar.ofNat_val_eq, Nat.cast_ofNat, BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow,
        BitVec.toNat_ushiftRight, BitVec.toNat_and, UScalar.bv_toNat, BitVec.toNat_ofNat,
        Nat.reduceMod, Nat.mod_add_mod]
      rw [core.num.U32.wrapping_add, UScalar.wrapping_add]
      simp only [UScalarTy.U32_numBits_eq, Bvify.U32.UScalar_bv]
      apply UScalar.eq_of_val_eq
      simp only [UScalarTy.U32_numBits_eq, Bvify.U32.UScalar_bv, U32.ofNat_bv,
        U32.wrapping_sub_bv_eq, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, Nat.reducePow,
        UScalar.ofNat_val_eq, i4_post_2, i3_post_2, coefficient1_post, i1_post_2,
        coefficient_post_2, i2_post_2]
      olet hsample_bits' : sample_bits' := sample_bits.bv &&& 15#32
      olet hsample_bits'' : sample_bits'' := sample_bits.val &&& 15
      have : sample_bits'.toNat = sample_bits'' := by simp [hsample_bits', hsample_bits'']
      replace hsample_bits' : sample_bits' < 16#32 := by bv_decide
      replace hsample_bits'' : sample_bits'' < 16 := by
        rw [hsample_bits'']
        apply Nat.lt_succ_of_le
        exact Nat.and_le_right
      revert this
      revert sample_bits''
      revert sample_bits'
      brute
    constructor <;> (fcongr; simp [Target2.samplePolyCBD.eta2_loop.inner_loop.next_coefficient])
  . have hj' : ¬(j.val < 8) := by simp_all
    simp [hj, hj']
termination_by 8 - j.val
decreasing_by scalar_tac

@[progress]
def ntt.poly_element_sample_cbd_from_bytes_eta2_inner_loop.spec (f : Array U16 256#usize)
  (i : Usize) (sample_bits : U32) (hi1 : i.val < 256) (hi2 : 8 ∣ i.val) :
  ∃ f' sample_bits',
  poly_element_sample_cbd_from_bytes_eta2_inner_loop f i sample_bits = ok (f', sample_bits') ∧
  to_poly f' = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i 0 sample_bits).1 ∧
  sample_bits'.bv = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i 0 sample_bits).2 := by
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop
  let* ⟨ res_1, res_2, res_post_1, res_post_2 ⟩ ← poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop.spec
  simp [*]

@[progress]
def ntt.poly_element_sample_cbd_from_bytes_eta2_loop_loop.spec (b : Slice U8) (f : Array U16 256#usize)
  (src_i i : Usize) (hb : 64 * 2 + 1 ≤ b.length) (hsrc_i : ↑src_i + 3 < b.length) (hi : 8 ∣ i.val) :
  let B := (b.val.map (fun x => x.bv)).toArray
  let η : Η := ⟨2, by simp⟩
  let hB : 64 * η.val + 1 ≤ B.size := by simp [B]; omega
  ∃ f', poly_element_sample_cbd_from_bytes_eta2_loop_loop b f src_i i = ok f' ∧
  to_poly f' = Target2.samplePolyCBD.eta2_loop {η, pe_dst := (to_poly f), B, hB, src_i, i} := by
  simp only [Spec.Q]
  unfold poly_element_sample_cbd_from_bytes_eta2_loop_loop
  simp only [UScalar.lt_equiv, UScalar.ofNat_val_eq, key.MLWE_POLYNOMIAL_COEFFICIENTS_eq,
    Nat.ofNat_pos, ↓reduceIte]
  split
  . next hi' =>
    let* ⟨a, ha⟩ ← slice_to_sub_array4_spec
    let* ⟨sample_bits, hsample_bits⟩ ← core.num.U32.from_le_bytes.progress_spec
    let* ⟨src_i1, hsrc_i1⟩ ← Usize.add_spec
    let* ⟨i1, hi1⟩ ← UScalar.and_spec
    let* ⟨i2, hi2⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨i3, hi3⟩ ← UScalar.and_spec
    have : (↑(sample_bits &&& 1431655765#u32) : Nat) ≤ 1431655765 := by
      simp only [UScalar.val_and, UScalar.ofNat_val_eq]
      apply Nat.and_le_right
    have : (↑(i2 &&& 1431655765#u32) : Nat) ≤ 1431655765 := by
      simp only [UScalar.val_and, UScalar.ofNat_val_eq]
      apply Nat.and_le_right
    let* ⟨sample_bits1, hsample_bits1⟩ ← U32.add_spec
    let* ⟨f', sample_bits', hf', hsample_bits'⟩ ← poly_element_sample_cbd_from_bytes_eta2_inner_loop.spec
    let* ⟨i4, hi4⟩ ← Usize.add_spec
    have : ↑src_i1 + 3 < b.length := by
      rw [hsrc_i1]
      sorry
    let* ⟨f'', hf''⟩ ← spec
    rw [hf'']
    -- This goal is true (though `fcongr` yields a false goal). The LHS is one iteration ahead of the RHS
    conv => rhs; unfold Target2.samplePolyCBD.eta2_loop
    simp only [key.MLWE_POLYNOMIAL_COEFFICIENTS_eq, hi', ↓reduceIte, Spec.Q, UScalar.ofNat_val_eq,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth'_eq]
    rw [hf', hsample_bits1, hi1, hi3]
    simp only [Spec.Q, UScalar.val_and, UScalar.ofNat_val_eq, hi2, Nat.cast_add,
      BitVec.natCast_eq_ofNat, BitVec.ofNat_and, Bvify.UScalar.BitVec_ofNat_setWidth,
      UScalarTy.U32_numBits_eq, Bvify.U32.UScalar_bv, hsample_bits, BitVec.setWidth_eq,
      Bvify.BitVec.ofNat_shift_U32_val]
    fcongr
    have h1 : 8 * (List.slice (↑src_i) (↑src_i + 4) (List.map (fun x => x.bv) b.val)).length = 32 := by
      simp only [List.slice_length, List.length_map, add_tsub_cancel_left]
      scalar_tac
    rw [BitVec.setWidth_add, BitVec.setWidth_and, BitVec.setWidth_and, BitVec.setWidth_ushiftRight]
    . have h2 : ∀ h : 8 * (List.map U8.bv ↑a).length = 32,
        BitVec.cast h (BitVec.fromLEBytes (List.map U8.bv ↑a)) =
        BitVec.setWidth 32
          (BitVec.fromLEBytes (List.slice (↑src_i) (↑src_i + 4) (List.map (fun x => x.bv) b.val))) := by
        intro h
        have : List.map U8.bv ↑a = List.slice (↑src_i) (↑src_i + 4) (List.map (fun x => x.bv) b.val) := by
          rw [List.eq_iff_forall_eq_getElem!]
          constructor
          . simp only [List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq,
              List.slice_length, add_tsub_cancel_left, right_eq_inf]
            simp only [Slice.length] at hsrc_i
            omega
          . intro i hi
            simp only [Array.getElem!_Nat_eq, Slice.getElem!_Nat_eq] at ha
            rw [List.getElem!_map_eq, ha i (by omega), List.getElem!_slice, List.getElem!_map_eq] <;> scalar_tac
        rw [← BitVec.setWidth_eq (BitVec.fromLEBytes (List.map U8.bv ↑a)), BitVec.cast_setWidth, this]
      have h3 : 1431655765#32 =
        BitVec.setWidth 32 1431655765#(8 * (List.slice (↑src_i) (↑src_i + 4)
          (List.map (fun x => x.bv) b.val)).length) := by
        rw [BitVec.setWidth_ofNat_of_le]
        simp only [List.slice_length, List.length_map, add_tsub_cancel_left]
        scalar_tac
      rw [h2, h3]
    . omega
    . omega
  . next hi =>
    simp only [ok.injEq, exists_eq_left']
    unfold Target2.samplePolyCBD.eta2_loop
    simp [hi]
termination_by 256 - i.val
decreasing_by scalar_tac

@[progress]
def ntt.poly_element_sample_cbd_from_bytes_eta2_loop.spec (b : Slice U8) (f : Array U16 256#usize)
  (hb : 64 * 2 + 1 ≤ b.length) :
  let B := (b.val.map (fun x => x.bv)).toArray
  let η : Η := ⟨2, by simp⟩
  let hB : 64 * η.val + 1 ≤ B.size := by simp [B]; omega
  ∃ f', poly_element_sample_cbd_from_bytes_eta2_loop b f = ok f' ∧
  to_poly f' = Target2.samplePolyCBD.eta2_loop {η, pe_dst := (to_poly f), B, hB, src_i := 0, i := 0} := by
  simp only [Spec.Q]
  unfold poly_element_sample_cbd_from_bytes_eta2_loop
  let* ⟨f', hf'⟩ ← poly_element_sample_cbd_from_bytes_eta2_loop_loop.spec
  rw [hf']

@[progress]
def ntt.poly_element_sample_cbd_from_bytes_eta3_loop.spec (b : Slice U8) (f : Array U16 256#usize)
  (hb : 64 * 3 + 1 ≤ b.length) :
  let B := (b.val.map (fun x => x.bv)).toArray
  let η : Η := ⟨3, by simp⟩
  let hB : 64 * η.val + 1 ≤ B.size := by simp [B]; omega
  ∃ f', poly_element_sample_cbd_from_bytes_eta3_loop b f = ok f' ∧
  to_poly f' = Target2.samplePolyCBD.eta3_loop {η, pe_dst := Polynomial.zero, B, hB, src_i := 0, i := 0} := by
  sorry

@[progress]
def ntt.poly_element_sample_cbd_from_bytes.spec (b : Slice U8) (eta : U32) (f : Array U16 256#usize)
  (heta : eta.val = 2 ∨ eta.val = 3) (hb : 64 * eta.val + 1 ≤ b.length) :
  let B := b.val.toArray.map (fun x => x.bv)
  let η : Η := ⟨eta, by simp [heta]⟩
  let hB : 64 * η.val + 1 ≤ B.size := by simp [B]; omega
  ∃ f', poly_element_sample_cbd_from_bytes b eta f = ok f' ∧
  to_poly f' = Target2.samplePolyCBD B hB := by
  unfold poly_element_sample_cbd_from_bytes Target2.samplePolyCBD
  rcases heta with heta | heta
  . simp only [Nat.not_eq, heta, UScalar.ofNat_val_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      Nat.succ_ne_self, Nat.lt_add_one, Nat.reduceLT, or_false, or_self,
      UScalar.val_not_eq_imp_not_eq, ↓reduceIte, Spec.Q, List.map_toArray]
    let* ⟨f', hf'⟩ ← ntt.poly_element_sample_cbd_from_bytes_eta2_loop.spec
    rw [hf']
    -- This goal is true because `pe_dst` does not impact the output when `i` and `src_i` are `0`
    sorry
  . replace heta : eta = 3#u32 := by scalar_tac
    simp only [heta, ↓reduceIte, Spec.Q, UScalar.ofNat_val_eq, List.map_toArray]
    let* ⟨f', hf'⟩ ← poly_element_sample_cbd_from_bytes_eta3_loop.spec
    rw [hf']

end Symcrust.SpecAux
