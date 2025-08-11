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

lemma Target.samplePolyCBD.recBody.preserves_below {η : Η} (b : Vector Bool (8 * (64 * ↑η)))
  (f : Polynomial) (i : Nat) (hi : i < 256) : ∀ j < i, (recBody b f i)[j]! = f[j]! := by
  intro j hj
  dcases hi2 : i = 255
  . simp only [Q, recBody, List.attach, hi2, Nat.reduceSub, List.range'_one, List.attachWith_cons,
      List.attachWith_nil, List.foldl_cons, body, Nat.reduceMul, Vector.Inhabited_getElem_eq_getElem!,
      Nat.cast_sum, List.foldl_nil]
    rw [Vector.getElem!_set!_ne]
    omega
  . have hi2 : i ∈ List.range' i (256 - i) := by simp [hi]
    have recBodyUnfold :
      recBody b (body b f ⟨i, hi2⟩) (i + 1) = recBody b f i := by
      simp [recBody, Nat.reduceSubDiff]
      have : 256 - i = (255 - i) + 1 := by omega
      rw [List.attach, List.attach]
      simp only [Nat.reduceSubDiff, List.foldl_attachWith, this, List.range'_succ,
        List.attachWith_cons, List.foldl_cons]
      rfl
    rw [← recBodyUnfold, preserves_below b (body b f ⟨i, hi2⟩) (i + 1) (by omega) j (by omega)]
    simp only [Q, body, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum]
    rw [Vector.getElem!_set!_ne]
    omega

def Target.samplePolyCBD.body.spec {rangeStart : Nat} {η : Η} (b : Vector Bool (8 * (64 * ↑η))) (f : Polynomial)
  (hRangeStart : rangeStart ∈ List.range' rangeStart (256 - rangeStart))
  (hf : ∀ j < rangeStart, f[j]! =
    ∑ x : Fin η.val, ↑b[2 * j * ↑η + ↑x]!.toNat - ∑ x : Fin η.val, ↑b[2 * j * ↑η + ↑η + ↑x]!.toNat) :
  ∀ j < rangeStart + 1, (body b f ⟨rangeStart, hRangeStart⟩)[j]! =
    ∑ x : Fin η.val, ↑b[2 * j * ↑η + ↑x]!.toNat -
    ∑ x : Fin η.val, ↑b[2 * j * ↑η + ↑η + ↑x]!.toNat := by
  intro j hj
  simp only [Q, body, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum]
  simp only [List.mem_range'_1, le_refl, lt_add_iff_pos_right, tsub_pos_iff_lt, true_and] at hRangeStart
  rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hj with hj | hj
  . rw [Vector.getElem!_set!_ne (by omega), hf j hj]
  . rw [hj, Vector.getElem!_set!]
    omega

def Target.samplePolyCBD.spec_aux {η : Η} (b : Vector Bool (8 * (64 * ↑η))) (f : Polynomial)
  (rangeStart : ℕ) (hRangeStart : rangeStart < 256)
  (hf : ∀ i < rangeStart,
    f[i]! = ∑ x : Fin η, (b[2 * i * ↑η + ↑x]!.toNat : ZMod Q) -
            ∑ x : Fin η, (b[2 * i * ↑η + ↑η + ↑x]!.toNat : ZMod Q)) :
  ∀ i < 256,
    (recBody b f rangeStart)[i]! =
    ∑ x : Fin η, (b[2 * i * ↑η + ↑x]!.toNat : ZMod Q) -
    ∑ x : Fin η, (b[2 * i * ↑η + ↑η + ↑x]!.toNat : ZMod Q) := by
  intro i hi
  dcases hRangeStart2 : rangeStart = 255
  . rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hi with hi | hi
    . simp only [hRangeStart2, Q] at hf
      simp only [Q, recBody, List.attach, hRangeStart2, Nat.reduceSub, List.range'_one,
        List.attachWith_cons, List.attachWith_nil, List.foldl_cons, body, Nat.reduceMul,
        Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum, List.foldl_nil]
      rw [Vector.getElem!_set!_ne (by omega), hf i hi]
    . simp only [Q, recBody, List.attach, hRangeStart2, Nat.reduceSub, List.range'_one,
        List.attachWith_cons, List.attachWith_nil, List.foldl_cons, body, Nat.reduceMul,
        Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum, List.foldl_nil, hi, Nat.lt_add_one,
        and_self, Vector.getElem!_set!]
  . by_cases hi2 : i < rangeStart
    . rw [recBody.preserves_below b f rangeStart (by omega) i hi2, hf i hi2]
    . have hRangeStart : rangeStart ∈ List.range' rangeStart (256 - rangeStart) := by simp [hRangeStart]
      replace hi2 : i ∈ List.range' rangeStart (256 - rangeStart) := by
        simp only [List.mem_range'_1]
        omega
      have recBodyUnfold :
        recBody b (body b f ⟨rangeStart, hRangeStart⟩) (rangeStart + 1) = recBody b f rangeStart := by
        simp [recBody, Nat.reduceSubDiff]
        have : 256 - rangeStart = (255 - rangeStart) + 1 := by omega
        rw [List.attach, List.attach]
        simp only [Nat.reduceSubDiff, List.foldl_attachWith, this, List.range'_succ,
          List.attachWith_cons, List.foldl_cons]
        rfl
      rw [← recBodyUnfold]
      have := body.spec b f (by omega) hf
      exact spec_aux b (body b f ⟨rangeStart, hRangeStart⟩) (rangeStart + 1) (by omega) this i hi
termination_by 256 - rangeStart

def Target.samplePolyCBD.spec {η : Η} (B : Vector Byte (64 * η)) (i : ℕ) (hi : i < 256) :
  let b := Spec.bytesToBits B
  have : 2 * i * η ≤ 510 * η := by scalar_tac +nonLin
  let x := ∑ (j : Fin η), Bool.toNat b[2 * i * η + j]
  let y := ∑ (j : Fin η), Bool.toNat b[2 * i * η + η + j]
  (samplePolyCBD B)[i]! = x - y := by
  simp only [Q, samplePolyCBD, spec_aux (Spec.bytesToBits B) Polynomial.zero 0 (by simp) (by simp) i hi,
    Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum]
