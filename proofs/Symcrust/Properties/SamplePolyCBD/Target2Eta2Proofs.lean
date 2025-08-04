import Symcrust.Spec
import Symcrust.Code.Funs
import Symcrust.Brute
import Symcrust.Properties.SamplePolyCBD.Target2Code

/-!
This file contains theorems about `Symcrust.Spec.samplePolyCBD` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to Algorithm 8 (SamplePolyCBD).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.samplePolyCBD`.
    - `Lean spec (functional)` corresponds to `Target.samplePolyCBD`.
      - The theorem that mathematically characterizes `Target.samplePolyCBD` is `Target.samplePolyCBD.spec`.
    - `Auxiliary spec` corresponds to `Target2.samplePolyCBD`.
    - `⟷₂` corresponds to `Target.samplePolyCBD.eq_spec`.
    - Analogues for later portions of the verification pipeline appear in other files.

  `Target2.samplePolyCBD.eta2_loop.spec` (which is the critical theorem in this file) proves `⟷₃` when `η = 2`
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.Std Aeneas.SRRange

set_option maxHeartbeats 1000000

def Target2.samplePolyCBD.eta2_loop.inner_loop.preserves_below (pe_dst : Polynomial) (i : ℕ)
  (sample_bits : BitVec 32) (k : ℕ) (hk : k < i) :
  (eta2_loop.inner_loop pe_dst i sample_bits).1[k]! = pe_dst[k]! := by
  unfold inner_loop
  simp only [Q]
  rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne,
    Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne]
  all_goals omega

def Target2.samplePolyCBD.eta2_loop.inner_loop.preserves_above (pe_dst : Polynomial) (i : ℕ)
  (sample_bits : BitVec 32) (k : ℕ) (hk : i + 7 < k) :
  (eta2_loop.inner_loop pe_dst i sample_bits).1[k]! = pe_dst[k]! := by
  unfold inner_loop
  simp only [Q]
  rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne,
    Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne]
  all_goals omega

def Target2.samplePolyCBD.eta2_loop.spec {s : Target2.samplePolyCBDState}
  (BVector : Vector Byte (64 * s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!)
  (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4)
  (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i)
  (i : ℕ) (hi : i < 256) (hη : s.η.1 = 2) : (eta2_loop s)[i]! = (Target.samplePolyCBD BVector)[i]! := by
  unfold eta2_loop
  split
  . simp only [UScalar.ofNat_val_eq, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth'_eq]
    apply eta2_loop.spec
    . simp only [Vector.eq_mk, hBVector]
    . intro j hj1
      simp only at hj1
      simp only
      by_cases hj2 : j < s.i
      . rw [eta2_loop.inner_loop.preserves_below]
        . exact hs1 j hj2
        . exact hj2
      . next hs4 =>
        olet hsample_bits : sample_bits :=
          ((BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
              1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
            (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
              1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
        rw [Target.samplePolyCBD.spec BVector j (by scalar_tac),
          ← Symcrust.SpecAux.Target.bytesToBits.eq_spec]
        have hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8,
          (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j := by
          intro i hi j hj
          rw [Target.bytesToBits.spec BVector i hi j hj, hBVector, Vector.getElem!_eq_toArray_getElem!,
            ← Array.Inhabited_getElem_eq_getElem!, Array.getElem_extract]
          . simp
          . simp only [Array.size_extract, tsub_zero, lt_inf_iff]
            have := s.hB
            omega
        unfold inner_loop
        simp only [Q, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum]
        have hj3 : j = s.i ∨ j = s.i + 1 ∨ j = s.i + 2 ∨ j = s.i + 3 ∨
                   j = s.i + 4 ∨ j = s.i + 5 ∨ j = s.i + 6 ∨ j = s.i + 7 := by omega
        rcases hj3 with hj3 | hj3 | hj3 | hj3 | hj3 | hj3 | hj3 | hj3
        . sorry
        . sorry
        . sorry
        . sorry
        . sorry
        . sorry
        . sorry
        . sorry
    . intro j hj1 hj2
      simp only at hj2
      simp only [ReduceZMod.reduceZMod]
      rw [eta2_loop.inner_loop.preserves_above]
      . exact hs2 j hj1 (by omega)
      . omega
    . simp only
      omega
    . simp [hs4]
    . simp [hs5]
    . exact hi
    . simp [hη]
  . next hi2 =>
    simp only [key.MLWE_POLYNOMIAL_COEFFICIENTS, eval_global, key.MLWE_POLYNOMIAL_COEFFICIENTS_body,
      UScalar.ofNat_val_eq, not_lt] at hi2
    exact hs1 i (by omega)
termination_by ↑key.MLWE_POLYNOMIAL_COEFFICIENTS - s.i
decreasing_by scalar_tac

end Symcrust.SpecAux
