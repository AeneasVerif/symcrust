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

set_option maxHeartbeats 2000000

theorem ntt.poly_element_sample_cbd_from_bytes_eta2_inner_loop.spec.aux
  (f : Std.Array U16 256#usize) (i : Usize) (sample_bits : U32) (hi1 : i.val < 256) (hi2 : 8 ∣ i.val)
  (coefficient_1 : U32)
  (coefficient_post_1_1 : ↑coefficient_1 = ↑(sample_bits &&& 15#u32))
  (sample_bits1_1 : U32)
  (sample_bits1_post_1_1 : ↑sample_bits1_1 = ↑sample_bits >>> 4)
  (sample_bits1_post_2_1 : sample_bits1_1.bv = sample_bits.bv >>> 4) (i1_1 : U32)
  (i1_post_1_1 : ↑i1_1 = ↑(coefficient_1 &&& 3#u32))
  (i2_1 : U32) (i2_post_1_1 : ↑i2_1 = ↑coefficient_1 >>> 2) (i2_post_2_1 : i2_1.bv = coefficient_1.bv >>> 2)
  (coefficient1_1 : U32) (coefficient1_post_1 : coefficient1_1 = core.num.U32.wrapping_sub i1_1 i2_1) (i3_1 : U32)
  (i3_post_1_1 : ↑i3_1 = ↑coefficient1_1 >>> 16) (i3_post_2_1 : i3_1.bv = coefficient1_1.bv >>> 16) (i4_1 : U32)
  (i4_post_1_1 : ↑i4_1 = ↑(3329#u32 &&& i3_1)) (coefficient2_1 : U32)
  (coefficient2_post_1 : coefficient2_1 = core.num.U32.wrapping_add coefficient1_1 i4_1) (i5_1 : Usize)
  (i5_post_1 : ↑i5_1 = i.val + 0) (i6_1 : U16) (i6_post_1 : i6_1 = UScalar.cast UScalarTy.U16 coefficient2_1)
  (pe_dst1_1 : Std.Array U16 256#usize) (pe_dst1_post_1 : pe_dst1_1 = f.set i5_1 i6_1) (j1_1 : Usize)
  (j1_post_1 : j1_1.val = 1) (coefficient_2 : U32)
  (coefficient_post_1_2 : ↑coefficient_2 = ↑(sample_bits1_1 &&& 15#u32)) (sample_bits1_2 : U32)
  (sample_bits1_post_1_2 : ↑sample_bits1_2 = ↑sample_bits1_1 >>> 4)
  (sample_bits1_post_2_2 : sample_bits1_2.bv = sample_bits1_1.bv >>> 4) (i1_2 : U32)
  (i1_post_1_2 : ↑i1_2 = ↑(coefficient_2 &&& 3#u32))
  (i2_2 : U32) (i2_post_1_2 : ↑i2_2 = ↑coefficient_2 >>> 2) (i2_post_2_2 : i2_2.bv = coefficient_2.bv >>> 2)
  (coefficient1_2 : U32) (coefficient1_post_2 : coefficient1_2 = core.num.U32.wrapping_sub i1_2 i2_2) (i3_2 : U32)
  (i3_post_1_2 : ↑i3_2 = ↑coefficient1_2 >>> 16) (i3_post_2_2 : i3_2.bv = coefficient1_2.bv >>> 16) (i4_2 : U32)
  (i4_post_1_2 : ↑i4_2 = ↑(3329#u32 &&& i3_2)) (coefficient2_2 : U32)
  (coefficient2_post_2 : coefficient2_2 = core.num.U32.wrapping_add coefficient1_2 i4_2) (i5_2 : Usize)
  (i5_post_2 : ↑i5_2 = ↑i + j1_1.val) (i6_2 : U16) (i6_post_2 : i6_2 = UScalar.cast UScalarTy.U16 coefficient2_2)
  (pe_dst1_2 : Std.Array U16 256#usize) (pe_dst1_post_2 : pe_dst1_2 = pe_dst1_1.set i5_2 i6_2) (j1_2 : Usize)
  (j1_post_2 : ↑j1_2 = j1_1.val + 1) (h : j1_2 < 8#usize) (coefficient_3 : U32)
  (coefficient_post_1_3 : ↑coefficient_3 = ↑(sample_bits1_2 &&& 15#u32))
  (sample_bits1_3 : U32)
  (sample_bits1_post_1_3 : ↑sample_bits1_3 = ↑sample_bits1_2 >>> 4)
  (sample_bits1_post_2_3 : sample_bits1_3.bv = sample_bits1_2.bv >>> 4) (i1_3 : U32)
  (i1_post_1_3 : ↑i1_3 = ↑(coefficient_3 &&& 3#u32))
  (i2_3 : U32) (i2_post_1_3 : ↑i2_3 = ↑coefficient_3 >>> 2) (i2_post_2_3 : i2_3.bv = coefficient_3.bv >>> 2)
  (coefficient1_3 : U32) (coefficient1_post_3 : coefficient1_3 = core.num.U32.wrapping_sub i1_3 i2_3) (i3_3 : U32)
  (i3_post_1_3 : ↑i3_3 = ↑coefficient1_3 >>> 16) (i3_post_2_3 : i3_3.bv = coefficient1_3.bv >>> 16) (i4_3 : U32)
  (i4_post_1_3 : ↑i4_3 = ↑(ntt.Q &&& i3_3)) (i4_post_2_3 : i4_3.bv = ntt.Q.bv &&& i3_3.bv) (coefficient2_3 : U32)
  (coefficient2_post_3 : coefficient2_3 = core.num.U32.wrapping_add coefficient1_3 i4_3) (i5_3 : Usize)
  (i5_post_3 : ↑i5_3 = i.val + ↑j1_2) (i6_3 : U16) (i6_post_3 : i6_3 = UScalar.cast UScalarTy.U16 coefficient2_3)
  (pe_dst1_3 : Std.Array U16 256#usize) (pe_dst1_post_3 : pe_dst1_3 = pe_dst1_2.set i5_3 i6_3) (j1_3 : Usize)
  (j1_post_3 : ↑j1_3 = j1_2.val + 1) (h_1 : j1_3 < 8#usize) (coefficient_4 : U32)
  (coefficient_post_1_4 : ↑coefficient_4 = ↑(sample_bits1_3 &&& 15#u32))
  (sample_bits1_4 : U32)
  (sample_bits1_post_1_4 : ↑sample_bits1_4 = ↑sample_bits1_3 >>> 4)
  (sample_bits1_post_2_4 : sample_bits1_4.bv = sample_bits1_3.bv >>> 4) (i1_4 : U32)
  (i1_post_1_4 : ↑i1_4 = ↑(coefficient_4 &&& 3#u32))
  (i2_4 : U32) (i2_post_1_4 : ↑i2_4 = ↑coefficient_4 >>> 2) (i2_post_2_4 : i2_4.bv = coefficient_4.bv >>> 2)
  (coefficient1_4 : U32) (coefficient1_post_4 : coefficient1_4 = core.num.U32.wrapping_sub i1_4 i2_4) (i3_4 : U32)
  (i3_post_1_4 : ↑i3_4 = ↑coefficient1_4 >>> 16) (i3_post_2_4 : i3_4.bv = coefficient1_4.bv >>> 16) (i4_4 : U32)
  (i4_post_1_4 : ↑i4_4 = ↑(ntt.Q &&& i3_4)) (i4_post_2_4 : i4_4.bv = ntt.Q.bv &&& i3_4.bv) (coefficient2_4 : U32)
  (coefficient2_post_4 : coefficient2_4 = core.num.U32.wrapping_add coefficient1_4 i4_4) (i5_4 : Usize)
  (i5_post_4 : ↑i5_4 = i.val + ↑j1_3) (i6_4 : U16) (i6_post_4 : i6_4 = UScalar.cast UScalarTy.U16 coefficient2_4)
  (pe_dst1_4 : Std.Array U16 256#usize) (pe_dst1_post_4 : pe_dst1_4 = pe_dst1_3.set i5_4 i6_4) (j1_4 : Usize)
  (j1_post_4 : ↑j1_4 = j1_3.val + 1) (h_2 : j1_4 < 8#usize) (coefficient_5 : U32)
  (coefficient_post_1_5 : ↑coefficient_5 = ↑(sample_bits1_4 &&& 15#u32))
  (sample_bits1_5 : U32)
  (sample_bits1_post_1_5 : ↑sample_bits1_5 = ↑sample_bits1_4 >>> 4)
  (sample_bits1_post_2_5 : sample_bits1_5.bv = sample_bits1_4.bv >>> 4) (i1_5 : U32)
  (i1_post_1_5 : ↑i1_5 = ↑(coefficient_5 &&& 3#u32))
  (i2_5 : U32) (i2_post_1_5 : ↑i2_5 = ↑coefficient_5 >>> 2) (i2_post_2_5 : i2_5.bv = coefficient_5.bv >>> 2)
  (coefficient1_5 : U32) (coefficient1_post_5 : coefficient1_5 = core.num.U32.wrapping_sub i1_5 i2_5) (i3_5 : U32)
  (i3_post_1_5 : ↑i3_5 = ↑coefficient1_5 >>> 16) (i3_post_2_5 : i3_5.bv = coefficient1_5.bv >>> 16) (i4_5 : U32)
  (i4_post_1_5 : ↑i4_5 = ↑(ntt.Q &&& i3_5)) (i4_post_2_5 : i4_5.bv = ntt.Q.bv &&& i3_5.bv) (coefficient2_5 : U32)
  (coefficient2_post_5 : coefficient2_5 = core.num.U32.wrapping_add coefficient1_5 i4_5) (i5_5 : Usize)
  (i5_post_5 : ↑i5_5 = i.val + ↑j1_4) (i6_5 : U16) (i6_post_5 : i6_5 = UScalar.cast UScalarTy.U16 coefficient2_5)
  (pe_dst1_5 : Std.Array U16 256#usize) (pe_dst1_post_5 : pe_dst1_5 = pe_dst1_4.set i5_5 i6_5) (j1_5 : Usize)
  (j1_post_5 : ↑j1_5 = j1_4.val + 1) (h_3 : j1_5 < 8#usize) (coefficient_6 : U32)
  (coefficient_post_1_6 : ↑coefficient_6 = ↑(sample_bits1_5 &&& 15#u32))
  (sample_bits1_6 : U32)
  (sample_bits1_post_1_6 : ↑sample_bits1_6 = ↑sample_bits1_5 >>> 4)
  (sample_bits1_post_2_6 : sample_bits1_6.bv = sample_bits1_5.bv >>> 4) (i1_6 : U32)
  (i1_post_1_6 : ↑i1_6 = ↑(coefficient_6 &&& 3#u32))
  (i2_6 : U32) (i2_post_1_6 : ↑i2_6 = ↑coefficient_6 >>> 2) (i2_post_2_6 : i2_6.bv = coefficient_6.bv >>> 2)
  (coefficient1_6 : U32) (coefficient1_post_6 : coefficient1_6 = core.num.U32.wrapping_sub i1_6 i2_6) (i3_6 : U32)
  (i3_post_1_6 : ↑i3_6 = ↑coefficient1_6 >>> 16) (i3_post_2_6 : i3_6.bv = coefficient1_6.bv >>> 16) (i4_6 : U32)
  (i4_post_1_6 : ↑i4_6 = ↑(ntt.Q &&& i3_6)) (i4_post_2_6 : i4_6.bv = ntt.Q.bv &&& i3_6.bv) (coefficient2_6 : U32)
  (coefficient2_post_6 : coefficient2_6 = core.num.U32.wrapping_add coefficient1_6 i4_6) (i5_6 : Usize)
  (i5_post_6 : ↑i5_6 = i.val + ↑j1_5) (i6_6 : U16) (i6_post_6 : i6_6 = UScalar.cast UScalarTy.U16 coefficient2_6)
  (pe_dst1_6 : Std.Array U16 256#usize) (pe_dst1_post_6 : pe_dst1_6 = pe_dst1_5.set i5_6 i6_6) (j1_6 : Usize)
  (j1_post_6 : ↑j1_6 = j1_5.val + 1) (h_4 : j1_6 < 8#usize) (coefficient_7 : U32)
  (coefficient_post_1_7 : ↑coefficient_7 = ↑(sample_bits1_6 &&& 15#u32))
  (sample_bits1_7 : U32)
  (sample_bits1_post_1_7 : ↑sample_bits1_7 = ↑sample_bits1_6 >>> 4)
  (sample_bits1_post_2_7 : sample_bits1_7.bv = sample_bits1_6.bv >>> 4) (i1_7 : U32)
  (i1_post_1_7 : ↑i1_7 = ↑(coefficient_7 &&& 3#u32))
  (i2_7 : U32) (i2_post_1_7 : ↑i2_7 = ↑coefficient_7 >>> 2) (i2_post_2_7 : i2_7.bv = coefficient_7.bv >>> 2)
  (coefficient1_7 : U32) (coefficient1_post_7 : coefficient1_7 = core.num.U32.wrapping_sub i1_7 i2_7) (i3_7 : U32)
  (i3_post_1_7 : ↑i3_7 = ↑coefficient1_7 >>> 16) (i3_post_2_7 : i3_7.bv = coefficient1_7.bv >>> 16) (i4_7 : U32)
  (i4_post_1_7 : ↑i4_7 = ↑(ntt.Q &&& i3_7)) (i4_post_2_7 : i4_7.bv = ntt.Q.bv &&& i3_7.bv) (coefficient2_7 : U32)
  (coefficient2_post_7 : coefficient2_7 = core.num.U32.wrapping_add coefficient1_7 i4_7) (i5_7 : Usize)
  (i5_post_7 : ↑i5_7 = i.val + ↑j1_6) (i6_7 : U16) (i6_post_7 : i6_7 = UScalar.cast UScalarTy.U16 coefficient2_7)
  (pe_dst1_7 : Std.Array U16 256#usize) (pe_dst1_post_7 : pe_dst1_7 = pe_dst1_6.set i5_7 i6_7) (j1_7 : Usize)
  (j1_post_7 : ↑j1_7 = j1_6.val + 1) (h_5 : j1_7 < 8#usize) (coefficient : U32)
  (coefficient_post_1 : ↑coefficient = ↑(sample_bits1_7 &&& 15#u32))
  (sample_bits1 : U32)
  (sample_bits1_post_1 : ↑sample_bits1 = ↑sample_bits1_7 >>> 4)
  (sample_bits1_post_2 : sample_bits1.bv = sample_bits1_7.bv >>> 4) (i1 : U32)
  (i1_post_1 : ↑i1 = ↑(coefficient &&& 3#u32)) (i2 : U32)
  (i2_post_1 : ↑i2 = ↑coefficient >>> 2) (i2_post_2 : i2.bv = coefficient.bv >>> 2) (coefficient1 : U32)
  (coefficient1_post : coefficient1 = core.num.U32.wrapping_sub i1 i2) (i3 : U32)
  (i3_post_1 : ↑i3 = ↑coefficient1 >>> 16) (i3_post_2 : i3.bv = coefficient1.bv >>> 16) (i4 : U32)
  (i4_post_1 : ↑i4 = ↑(ntt.Q &&& i3)) (i4_post_2 : i4.bv = ntt.Q.bv &&& i3.bv) (coefficient2 : U32)
  (coefficient2_post : coefficient2 = core.num.U32.wrapping_add coefficient1 i4) (i5 : Usize)
  (i5_post : ↑i5 = i.val + ↑j1_7) (i6 : U16) (i6_post : i6 = UScalar.cast UScalarTy.U16 coefficient2)
  (pe_dst1 : Std.Array U16 256#usize) (pe_dst1_post : pe_dst1 = pe_dst1_7.set i5 i6) (j1 : Usize)
  (j1_post : ↑j1 = j1_7.val + 1) (k : ℕ) (hk : k < 256) :
  ((((((((Vector.set! (to_poly f) ↑i
                                    ↑↑(UScalar.cast UScalarTy.U16
                                          (core.num.U32.wrapping_add (core.num.U32.wrapping_sub i1_1 i2_1) i4_1))).set!
                                (↑i + 1)
                                ↑↑(UScalar.cast UScalarTy.U16
                                      (core.num.U32.wrapping_add (core.num.U32.wrapping_sub i1_2 i2_2) i4_2))).set!
                            (↑i + 2)
                            ↑↑(UScalar.cast UScalarTy.U16
                                  (core.num.U32.wrapping_add (core.num.U32.wrapping_sub i1_3 i2_3) i4_3))).set!
                        (↑i + 3)
                        ↑↑(UScalar.cast UScalarTy.U16
                              (core.num.U32.wrapping_add (core.num.U32.wrapping_sub i1_4 i2_4) i4_4))).set!
                    (↑i + 4)
                    ↑↑(UScalar.cast UScalarTy.U16
                          (core.num.U32.wrapping_add (core.num.U32.wrapping_sub i1_5 i2_5) i4_5))).set!
                (↑i + 5)
                ↑↑(UScalar.cast UScalarTy.U16
                      (core.num.U32.wrapping_add (core.num.U32.wrapping_sub i1_6 i2_6) i4_6))).set!
            (↑i + 6)
            ↑↑(UScalar.cast UScalarTy.U16 (core.num.U32.wrapping_add (core.num.U32.wrapping_sub i1_7 i2_7) i4_7))).set!
        (↑i + 7) ↑↑(UScalar.cast UScalarTy.U16 (core.num.U32.wrapping_add (core.num.U32.wrapping_sub i1 i2) i4)))[k] =
    ((((((((Vector.set! (to_poly f) ↑i
                                    ↑((4294967296 - (↑sample_bits &&& 15) >>> 2 + (↑sample_bits &&& 15 &&& 3) +
                                          (3329 &&&
                                            ((4294967296 - (↑sample_bits &&& 15) >>> 2 + (↑sample_bits &&& 15 &&& 3)) %
                                                4294967296) >>>
                                              16)) %
                                        4294967296)).set!
                                (↑i + 1)
                                ↑((4294967296 - (↑sample_bits >>> 4 &&& 15) >>> 2 + (↑sample_bits >>> 4 &&& 15 &&& 3) +
                                      (3329 &&&
                                        ((4294967296 - (↑sample_bits >>> 4 &&& 15) >>> 2 +
                                              (↑sample_bits >>> 4 &&& 15 &&& 3)) %
                                            4294967296) >>>
                                          16)) %
                                    4294967296)).set!
                            (↑i + 2)
                            ↑((4294967296 - (↑sample_bits >>> 8 &&& 15) >>> 2 + (↑sample_bits >>> 8 &&& 15 &&& 3) +
                                  (3329 &&&
                                    ((4294967296 - (↑sample_bits >>> 8 &&& 15) >>> 2 +
                                          (↑sample_bits >>> 8 &&& 15 &&& 3)) %
                                        4294967296) >>>
                                      16)) %
                                4294967296)).set!
                        (↑i + 3)
                        ↑((4294967296 - (↑sample_bits >>> 12 &&& 15) >>> 2 + (↑sample_bits >>> 12 &&& 15 &&& 3) +
                              (3329 &&&
                                ((4294967296 - (↑sample_bits >>> 12 &&& 15) >>> 2 +
                                      (↑sample_bits >>> 12 &&& 15 &&& 3)) %
                                    4294967296) >>>
                                  16)) %
                            4294967296)).set!
                    (↑i + 4)
                    ↑((4294967296 - (↑sample_bits >>> 16 &&& 15) >>> 2 + (↑sample_bits >>> 16 &&& 15 &&& 3) +
                          (3329 &&&
                            ((4294967296 - (↑sample_bits >>> 16 &&& 15) >>> 2 + (↑sample_bits >>> 16 &&& 15 &&& 3)) %
                                4294967296) >>>
                              16)) %
                        4294967296)).set!
                (↑i + 5)
                ↑((4294967296 - (↑sample_bits >>> 20 &&& 15) >>> 2 + (↑sample_bits >>> 20 &&& 15 &&& 3) +
                      (3329 &&&
                        ((4294967296 - (↑sample_bits >>> 20 &&& 15) >>> 2 + (↑sample_bits >>> 20 &&& 15 &&& 3)) %
                            4294967296) >>>
                          16)) %
                    4294967296)).set!
            (↑i + 6)
            ↑((4294967296 - (↑sample_bits >>> 24 &&& 15) >>> 2 + (↑sample_bits >>> 24 &&& 15 &&& 3) +
                  (3329 &&&
                    ((4294967296 - (↑sample_bits >>> 24 &&& 15) >>> 2 + (↑sample_bits >>> 24 &&& 15 &&& 3)) %
                        4294967296) >>>
                      16)) %
                4294967296)).set!
        (↑i + 7)
        ↑((4294967296 - (↑sample_bits >>> 28 &&& 15) >>> 2 + (↑sample_bits >>> 28 &&& 15 &&& 3) +
              (3329 &&&
                ((4294967296 - (↑sample_bits >>> 28 &&& 15) >>> 2 + (↑sample_bits >>> 28 &&& 15 &&& 3)) %
                    4294967296) >>>
                  16)) %
            4294967296))[k] := sorry

/-
@[progress]
def ntt.poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop.spec (f : Array U16 256#usize)
  (i : Usize) (sample_bits : U32) (hi1 : i.val < 256) (hi2 : 8 ∣ i.val) (j : Usize)
  (hf : ∀ k < j.val, f[k]! = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i sample_bits).1[k]!)
  :
  ∃ f' sample_bits',
  poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop f i sample_bits j = ok (f', sample_bits') ∧
  ∀ k < j.val, f'[k]! = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i sample_bits).1[k]! ∧
  to_poly f' = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i sample_bits).1 ∧
  sample_bits'.bv = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i sample_bits).2 := by
-/

-- This proof contains a lot of repeated code because `Target2.samplePolyCBD.eta2_loop.inner_loop` manually
-- unfolds the loop body of `poly_element_sample_cbd_from_bytes_eta2_inner_loop` 8 times.
@[progress]
def ntt.poly_element_sample_cbd_from_bytes_eta2_inner_loop.spec (f : Array U16 256#usize)
  (i : Usize) (sample_bits : U32) (hi1 : i.val < 256) (hi2 : 8 ∣ i.val) :
  ∃ f' sample_bits',
  poly_element_sample_cbd_from_bytes_eta2_inner_loop f i sample_bits = ok (f', sample_bits') ∧
  to_poly f' = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i sample_bits).1 ∧
  sample_bits'.bv = (Target2.samplePolyCBD.eta2_loop.inner_loop (to_poly f) i sample_bits).2 := by
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  simp only [UScalar.lt_equiv, UScalar.ofNat_val_eq, Nat.ofNat_pos, ↓reduceIte, Q.eq, Spec.Q,
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
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  simp only [UScalar.lt_equiv, j1_post, UScalar.ofNat_val_eq, Nat.one_lt_ofNat, ↓reduceIte, Q.eq]
  let* ⟨ coefficient, coefficient_post_1, coefficient_post_2 ⟩ ← UScalar.and_spec
  let* ⟨ sample_bits1, sample_bits1_post_1, sample_bits1_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
  let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← UScalar.and_spec
  let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
  let* ⟨ coefficient1, coefficient1_post ⟩ ← core.num.U32.wrapping_sub.progress_spec
  let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
  let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← UScalar.and_spec
  let* ⟨ coefficient2, coefficient2_post ⟩ ← core.num.U32.wrapping_add.progress_spec
  let* ⟨ ⟩ ← massert_spec
  · sorry
  let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
  let* ⟨ i6, i6_post ⟩ ← UScalar.cast.progress_spec
  let* ⟨ pe_dst1, pe_dst1_post ⟩ ← Array.update_spec
  let* ⟨ j1, j1_post ⟩ ← Usize.add_spec
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  split
  . let* ⟨ coefficient, coefficient_post_1, coefficient_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ sample_bits1, sample_bits1_post_1, sample_bits1_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨ coefficient1, coefficient1_post ⟩ ← core.num.U32.wrapping_sub.progress_spec
    let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ coefficient2, coefficient2_post ⟩ ← core.num.U32.wrapping_add.progress_spec
    let* ⟨ ⟩ ← massert_spec
    · sorry
    let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
    let* ⟨ i6, i6_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ pe_dst1, pe_dst1_post ⟩ ← Array.update_spec
    let* ⟨ j1, j1_post ⟩ ← Usize.add_spec
    unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
    split
    . let* ⟨ coefficient, coefficient_post_1, coefficient_post_2 ⟩ ← UScalar.and_spec
      let* ⟨ sample_bits1, sample_bits1_post_1, sample_bits1_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← UScalar.and_spec
      let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ coefficient1, coefficient1_post ⟩ ← core.num.U32.wrapping_sub.progress_spec
      let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← UScalar.and_spec
      let* ⟨ coefficient2, coefficient2_post ⟩ ← core.num.U32.wrapping_add.progress_spec
      let* ⟨ ⟩ ← massert_spec
      · sorry
      let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
      let* ⟨ i6, i6_post ⟩ ← UScalar.cast.progress_spec
      let* ⟨ pe_dst1, pe_dst1_post ⟩ ← Array.update_spec
      let* ⟨ j1, j1_post ⟩ ← Usize.add_spec
      unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
      split
      . let* ⟨ coefficient, coefficient_post_1, coefficient_post_2 ⟩ ← UScalar.and_spec
        let* ⟨ sample_bits1, sample_bits1_post_1, sample_bits1_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
        let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← UScalar.and_spec
        let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
        let* ⟨ coefficient1, coefficient1_post ⟩ ← core.num.U32.wrapping_sub.progress_spec
        let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
        let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← UScalar.and_spec
        let* ⟨ coefficient2, coefficient2_post ⟩ ← core.num.U32.wrapping_add.progress_spec
        let* ⟨ ⟩ ← massert_spec
        · sorry
        let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
        let* ⟨ i6, i6_post ⟩ ← UScalar.cast.progress_spec
        let* ⟨ pe_dst1, pe_dst1_post ⟩ ← Array.update_spec
        let* ⟨ j1, j1_post ⟩ ← Usize.add_spec
        unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
        split
        . let* ⟨ coefficient, coefficient_post_1, coefficient_post_2 ⟩ ← UScalar.and_spec
          let* ⟨ sample_bits1, sample_bits1_post_1, sample_bits1_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
          let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← UScalar.and_spec
          let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
          let* ⟨ coefficient1, coefficient1_post ⟩ ← core.num.U32.wrapping_sub.progress_spec
          let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
          let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← UScalar.and_spec
          let* ⟨ coefficient2, coefficient2_post ⟩ ← core.num.U32.wrapping_add.progress_spec
          let* ⟨ ⟩ ← massert_spec
          · sorry
          let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
          let* ⟨ i6, i6_post ⟩ ← UScalar.cast.progress_spec
          let* ⟨ pe_dst1, pe_dst1_post ⟩ ← Array.update_spec
          let* ⟨ j1, j1_post ⟩ ← Usize.add_spec
          unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
          split
          . let* ⟨ coefficient, coefficient_post_1, coefficient_post_2 ⟩ ← UScalar.and_spec
            let* ⟨ sample_bits1, sample_bits1_post_1, sample_bits1_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
            let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← UScalar.and_spec
            let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
            let* ⟨ coefficient1, coefficient1_post ⟩ ← core.num.U32.wrapping_sub.progress_spec
            let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
            let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← UScalar.and_spec
            let* ⟨ coefficient2, coefficient2_post ⟩ ← core.num.U32.wrapping_add.progress_spec
            let* ⟨ ⟩ ← massert_spec
            · sorry
            let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
            let* ⟨ i6, i6_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ pe_dst1, pe_dst1_post ⟩ ← Array.update_spec
            let* ⟨ j1, j1_post ⟩ ← Usize.add_spec
            unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
            split
            . let* ⟨ coefficient, coefficient_post_1, coefficient_post_2 ⟩ ← UScalar.and_spec
              let* ⟨ sample_bits1, sample_bits1_post_1, sample_bits1_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
              let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← UScalar.and_spec
              let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
              let* ⟨ coefficient1, coefficient1_post ⟩ ← core.num.U32.wrapping_sub.progress_spec
              let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
              let* ⟨ i4, i4_post_1, i4_post_2 ⟩ ← UScalar.and_spec
              let* ⟨ coefficient2, coefficient2_post ⟩ ← core.num.U32.wrapping_add.progress_spec
              let* ⟨ ⟩ ← massert_spec
              · sorry
              let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
              let* ⟨ i6, i6_post ⟩ ← UScalar.cast.progress_spec
              let* ⟨ pe_dst1, pe_dst1_post ⟩ ← Array.update_spec
              let* ⟨ j1, j1_post ⟩ ← Usize.add_spec
              unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
              simp only [UScalar.lt_equiv, Nat.reduceAdd, UScalar.ofNat_val_eq, lt_self_iff_false,
                ↓reduceIte, ok.injEq, Prod.mk.injEq, and_assoc, exists_and_left, exists_eq_left',
                BitVec.reduceShiftRightShiftRight, to_poly_set, Spec.Q, add_zero, *]
              unfold Target2.samplePolyCBD.eta2_loop.inner_loop
                Target2.samplePolyCBD.eta2_loop.inner_loop.next_coefficient
              simp only [BitVec.ofNat_eq_ofNat, Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
                BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight,
                BitVec.toNat_and, UScalar.bv_toNat, BitVec.toNat_ofNat, Nat.reduceMod,
                Nat.mod_add_mod, BitVec.reduceShiftRightShiftRight, and_true]
              ext k hk
              -- `apply ntt.poly_element_sample_cbd_from_bytes_eta2_inner_loop.spec.aux` struggles
              -- to instantiate all of the arguments
              sorry
            . simp only [progress_simps]
              scalar_tac
          . simp only [progress_simps]
            scalar_tac
        . simp only [progress_simps]
          scalar_tac
      . simp only [progress_simps]
        scalar_tac
    . simp only [progress_simps]
      scalar_tac
  . simp only [progress_simps]
    scalar_tac

  /-
  let f' : Std.Array U16 256#usize := sorry
  have hsample_bits' : ∃ sample_bits' : U32, sample_bits'.bv = sample_bits.bv >>> 32 := by
    apply Exists.intro $ U32.ofNat (sample_bits.val >>> 32) (by scalar_tac)
    simp
  rcases hsample_bits' with ⟨sample_bits', hsample_bits'⟩
  apply Exists.intro f'
  apply Exists.intro sample_bits'
  split_conjs
  . sorry
  . sorry
  . simp only [hsample_bits', Target2.samplePolyCBD.eta2_loop.inner_loop, Spec.Q,
      Target2.samplePolyCBD.eta2_loop.inner_loop.next_coefficient, BitVec.ofNat_eq_ofNat, Q.eq,
      UScalar.ofNat_val_eq, Nat.cast_ofNat, BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow,
      BitVec.toNat_ushiftRight, BitVec.toNat_and, UScalar.bv_toNat, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.mod_add_mod, BitVec.reduceShiftRightShiftRight]
  -/
  /-
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  simp only [UScalar.lt_equiv, j1_post, UScalar.ofNat_val_eq, Nat.one_lt_ofNat, ↓reduceIte, Q.eq]
  progress*
  . simp only [U32.wrapping_add_val_eq, U32.wrapping_sub_val_eq, UScalar.val_and,
      UScalar.ofNat_val_eq, UScalar.size_UScalarTyU32, Nat.mod_add_mod, *]
    olet hsample_bits' : sample_bits' := ↑sample_bits >>> 4 &&& 15
    replace hsample_bits' : sample_bits' < 16 := by
      apply Nat.lt_succ_of_le
      rw [hsample_bits']
      exact Nat.and_le_right
    revert sample_bits'
    brute
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  simp only [UScalar.lt_equiv, Nat.reduceAdd, UScalar.ofNat_val_eq, Nat.reduceLT, ↓reduceIte, Q.eq, *]
  progress*
  . simp only [U32.wrapping_add_val_eq, U32.wrapping_sub_val_eq, UScalar.val_and,
      UScalar.ofNat_val_eq, UScalar.size_UScalarTyU32, Nat.mod_add_mod, *]
    olet hsample_bits' : sample_bits' := ↑sample_bits >>> 4 >>> 4 &&& 15
    replace hsample_bits' : sample_bits' < 16 := by
      apply Nat.lt_succ_of_le
      rw [hsample_bits']
      exact Nat.and_le_right
    revert sample_bits'
    brute
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  simp only [UScalar.lt_equiv, Nat.reduceAdd, UScalar.ofNat_val_eq, Nat.reduceLT, ↓reduceIte, Q.eq, *]
  progress*
  . simp only [U32.wrapping_add_val_eq, U32.wrapping_sub_val_eq, UScalar.val_and,
      UScalar.ofNat_val_eq, UScalar.size_UScalarTyU32, Nat.mod_add_mod, *]
    olet hsample_bits' : sample_bits' := ↑sample_bits >>> 4 >>> 4 >>> 4 &&& 15
    replace hsample_bits' : sample_bits' < 16 := by
      apply Nat.lt_succ_of_le
      rw [hsample_bits']
      exact Nat.and_le_right
    revert sample_bits'
    brute
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  simp only [UScalar.lt_equiv, Nat.reduceAdd, UScalar.ofNat_val_eq, Nat.reduceLT, ↓reduceIte, Q.eq, *]
  progress*
  . simp only [U32.wrapping_add_val_eq, U32.wrapping_sub_val_eq, UScalar.val_and,
      UScalar.ofNat_val_eq, UScalar.size_UScalarTyU32, Nat.mod_add_mod, *]
    olet hsample_bits' : sample_bits' := ↑sample_bits >>> 4 >>> 4 >>> 4 >>> 4 &&& 15
    replace hsample_bits' : sample_bits' < 16 := by
      apply Nat.lt_succ_of_le
      rw [hsample_bits']
      exact Nat.and_le_right
    revert sample_bits'
    brute
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  simp only [UScalar.lt_equiv, Nat.reduceAdd, UScalar.ofNat_val_eq, Nat.reduceLT, ↓reduceIte, Q.eq, *]
  progress*
  . simp only [U32.wrapping_add_val_eq, U32.wrapping_sub_val_eq, UScalar.val_and,
      UScalar.ofNat_val_eq, UScalar.size_UScalarTyU32, Nat.mod_add_mod, *]
    olet hsample_bits' : sample_bits' := ↑sample_bits >>> 4 >>> 4 >>> 4 >>> 4 >>> 4 &&& 15
    replace hsample_bits' : sample_bits' < 16 := by
      apply Nat.lt_succ_of_le
      rw [hsample_bits']
      exact Nat.and_le_right
    revert sample_bits'
    brute
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  simp only [UScalar.lt_equiv, Nat.reduceAdd, UScalar.ofNat_val_eq, Nat.reduceLT, ↓reduceIte, Q.eq, *]
  progress*
  . simp only [U32.wrapping_add_val_eq, U32.wrapping_sub_val_eq, UScalar.val_and,
      UScalar.ofNat_val_eq, UScalar.size_UScalarTyU32, Nat.mod_add_mod, *]
    olet hsample_bits' : sample_bits' := ↑sample_bits >>> 4 >>> 4 >>> 4 >>> 4 >>> 4 >>> 4 &&& 15
    replace hsample_bits' : sample_bits' < 16 := by
      apply Nat.lt_succ_of_le
      rw [hsample_bits']
      exact Nat.and_le_right
    revert sample_bits'
    brute
  unfold poly_element_sample_cbd_from_bytes_eta2_inner_loop_loop
  simp only [UScalar.lt_equiv, Nat.reduceAdd, UScalar.ofNat_val_eq, Nat.reduceLT, ↓reduceIte, Q.eq, *]
  progress*
  . simp only [U32.wrapping_add_val_eq, U32.wrapping_sub_val_eq, UScalar.val_and,
      UScalar.ofNat_val_eq, UScalar.size_UScalarTyU32, Nat.mod_add_mod, *]
    olet hsample_bits' : sample_bits' := ↑sample_bits >>> 4 >>> 4 >>> 4 >>> 4 >>> 4 >>> 4 >>> 4 &&& 15
    replace hsample_bits' : sample_bits' < 16 := by
      apply Nat.lt_succ_of_le
      rw [hsample_bits']
      exact Nat.and_le_right
    revert sample_bits'
    brute
  sorry
  -/

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
