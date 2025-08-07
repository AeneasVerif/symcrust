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

/-
@[reducible]
def ntt.poly_element_sample_cbd_from_bytes_eta2_inner_loop
  (pe_dst : Array U16 256#usize) (i : Usize) (sample_bits : U32) :
  Result ((Array U16 256#usize) × U32)
  :=
  ntt.poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop pe_dst i
    sample_bits 0#usize
-/

/-
def Target2.samplePolyCBD.eta3_loop.inner_loop (pe_dst : Polynomial) (i : ℕ) (sample_bits : BitVec 32) :
  Polynomial × BitVec 32 :=
-/

@[progress]
def ntt.poly_element_sample_cbd_from_bytes_eta2_inner_loop.spec (f : Array U16 256#usize)
  (i : Usize) (sample_bits : U32) :
  ∃ f' sample_bits',
  poly_element_sample_cbd_from_bytes_eta2_inner_loop f i sample_bits = ok (f', sample_bits') ∧
  to_poly f' = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i sample_bits).1 ∧
  sample_bits'.bv = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i sample_bits).2 := by
  sorry

/-
def ntt.poly_element_sample_cbd_from_bytes_eta2_loop_loop
  (pb_src : Slice U8) (pe_dst : Array U16 256#usize) (src_i : Usize)
  (i : Usize) :
  Result (Array U16 256#usize)
  :=
-/

@[progress]
def ntt.poly_element_sample_cbd_from_bytes_eta2_loop_loop.spec (b : Slice U8) (f : Array U16 256#usize)
  (src_i i : Usize) (hb : 64 * 2 + 1 ≤ b.length) :
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
  . next hi =>
    have : ↑src_i + 3 < b.length := by sorry -- **TODO** Add precondition to the spec
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
    let* ⟨f'', hf''⟩ ← spec
    rw [hf'']
    -- This goal is true (though `fcongr` yields a false goal). The LHS is one iteration ahead of the RHS
    conv => rhs; unfold Target2.samplePolyCBD.eta2_loop
    simp only [key.MLWE_POLYNOMIAL_COEFFICIENTS_eq, hi, ↓reduceIte, Spec.Q, UScalar.ofNat_val_eq,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth'_eq]
    rw [hf', hsample_bits1, hi1, hi3]
    simp only [Spec.Q, UScalar.val_and, UScalar.ofNat_val_eq, hi2, Nat.cast_add,
      BitVec.natCast_eq_ofNat, BitVec.ofNat_and, Bvify.UScalar.BitVec_ofNat_setWidth,
      UScalarTy.U32_numBits_eq, Bvify.U32.UScalar_bv, hsample_bits, BitVec.setWidth_eq,
      Bvify.BitVec.ofNat_shift_U32_val]
    fcongr
    sorry
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
