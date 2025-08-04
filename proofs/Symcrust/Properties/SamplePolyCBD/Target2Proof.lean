import Symcrust.Spec
import Symcrust.Code.Funs
import Symcrust.Brute
import Symcrust.Properties.SamplePolyCBD.Target2Eta2Proofs
import Symcrust.Properties.SamplePolyCBD.Target2Eta3Proofs

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
    - `⟷₃` is bundled with `⟷₂` in the form of `Target2.samplePolyCBD.spec`.
    - Analogues for later portions of the verification pipeline appear in other files.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.Std Aeneas.SRRange

set_option maxHeartbeats 1000000

def Target2.samplePolyCBD.spec {η : Η} (B : Array Byte) (hB : 64 * η.1 + 1 ≤ B.size) :
  let Bvector : Vector Byte (64 * η.1) := ⟨B.take (64 * η.1), by simp; omega⟩
  samplePolyCBD B hB = Spec.samplePolyCBD Bvector := by
  intro BVector
  rw [← Target.samplePolyCBD.eq_spec]
  rw [Vector.eq_iff_forall_eq_getElem!]
  intro i hi
  unfold samplePolyCBD
  have hBVector : BVector = ⟨B.take (64 * η.1), by simp; omega⟩ := by rfl
  have hs1 : ∀ j < 0, Polynomial.zero[j]! = (Target.samplePolyCBD BVector)[j]! := by simp
  have hs2 : ∀ j < 256, 0 ≤ j → Polynomial.zero[j]! = 0 := by
    intro j hj1 hj2
    rw [Polynomial.zero, Vector.getElem!_replicate hj1]
  have hs3 : 0 = 0 := rfl -- Used to discharge `hs3` in `eta3_loop.spec` and `eta2_loop.spec` by `assumption`
  split
  . apply eta3_loop.spec <;> assumption
  . have : η.1 = 2 := by
      have hη := η.2
      simp only [Set.instMembership, Set.Mem, insert, Set.insert, setOf, singleton, Set.singleton] at hη
      omega
    have : 8 ∣ 0 := by simp
    have : 4 ∣ 0 := by simp
    apply eta2_loop.spec <;> assumption

end Symcrust.SpecAux
