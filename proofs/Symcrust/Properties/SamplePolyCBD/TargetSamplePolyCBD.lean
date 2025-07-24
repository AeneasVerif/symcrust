import Symcrust.Spec
import Symcrust.Code.Funs
import Symcrust.Brute
import Symcrust.Properties.CompressEncode.CompressEncode

/-!
This file contains theorems about `Symcrust.Spec.samplePolyCBD` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to Algorithm 8 (SamplePolyCBD).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.samplePolyCBD`.
    - `Lean spec (functional)` corresponds to `Target.samplePolyCBD`.
      - The theorem that mathematically characterizes `Target.samplePolyCBD` is `Target.samplePolyCBD.spec`.
    - `⟷₂` corresponds to `Target.samplePolyCBD.eq_spec`.
    - Analogues for later portions of the verification pipeline appear in other files.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.Std Aeneas.SRRange

set_option maxHeartbeats 1000000

def Target.samplePolyCBD.body {rangeStart : Nat} {η : Η} (b : Vector Bool (8 * (64 * ↑η))) (f : Polynomial)
  (i : { x // x ∈ List.range' rangeStart (256 - rangeStart) }) : Polynomial :=
  have hi := i.2
  have : 2 * i.1 * η ≤ 510 * η := by
    simp only [List.mem_range'_1] at hi
    scalar_tac +nonLin
  let x := ∑ (j : Fin η), Bool.toNat b[2 * i.1 * η + j]
  let y := ∑ (j : Fin η), Bool.toNat b[2 * i.1 * η + η + j]
  f.set! i (x - y)

def Target.samplePolyCBD.recBody {η : Η} (b : Vector Bool (8 * (64 * ↑η))) (f : Polynomial) (i : Nat) : Polynomial :=
  List.foldl (body b) f (List.range' i (256 - i)).attach

def Target.samplePolyCBD {η : Η} (B : Vector Byte (64 * η)) : Polynomial :=
  let b := Spec.bytesToBits B
  let f := Polynomial.zero
  samplePolyCBD.recBody b f 0

def Target.samplePolyCBD.eq_spec {η : Η} (B : Vector Byte (64 * η)) :
  samplePolyCBD B = Spec.samplePolyCBD B := by
  unfold samplePolyCBD samplePolyCBD.recBody samplePolyCBD.body Spec.samplePolyCBD
  simp only [Nat.sub_zero, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum, List.mem_range'_1,
    zero_le, zero_add, true_and, List.foldl_subtype, List.unattach_attach, bind_pure_comp, map_pure,
    forIn'_eq_forIn, forIn_eq_forIn_range', size, tsub_zero, Nat.reduceAdd, Nat.add_one_sub_one,
    Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]

def Target.samplePolyCBD.spec_aux {η : Η} (b : Vector Bool (8 * (64 * ↑η))) (f : Polynomial)
  (rangeStart : ℕ) (i : { x // x ∈ List.range' rangeStart (256 - rangeStart) }) :
  (List.foldl (body b) f (List.range' rangeStart (256 - rangeStart)).attach)[i.1]! =
  ∑ x : Fin η, (b[2 * i.1 * ↑η + ↑x]!.toNat : ZMod Q) - ∑ x : Fin η, (b[2 * i.1 * ↑η + ↑η + ↑x]!.toNat : ZMod Q) := by
  rcases i with ⟨i, hi⟩
  -- **TODO** Look at the proofs for similar functions to recall how to best do this induction/recursion
  sorry

def Target.samplePolyCBD.spec {η : Η} (B : Vector Byte (64 * η)) (i : ℕ) (hi : i < 256) :
  let b := Spec.bytesToBits B
  have : 2 * i * η ≤ 510 * η := by scalar_tac +nonLin
  let x := ∑ (j : Fin η), Bool.toNat b[2 * i * η + j]
  let y := ∑ (j : Fin η), Bool.toNat b[2 * i * η + η + j]
  (samplePolyCBD B)[i]! = x - y := by
  unfold samplePolyCBD recBody
  simp only [Q, Nat.sub_zero, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum]
  rw [spec_aux (Spec.bytesToBits B) Polynomial.zero 0 ⟨i, by simp [hi]⟩]
