import Symcrust.Properties.CompressEncode.CompressEncode
import Mathlib.Algebra.BigOperators.Fin
import Symcrust.Properties.DecodeDecompress.HelperLemmas
import Symcrust.Brute

/-!
This file contains theorems about `Symcrust.Spec.byteDecode` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to Algorithm 6 (ByteDecode).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.byteDecode`.
    - `Lean spec (functional)` corresponds to `Target.byteDecode`.
      - The theorem that mathematically characterizes `Target.byteDecode` is `Target.byteDecode.spec`.
    - `⟷₂` corresponds to `Target.byteDecode.eq_spec`.
    - Analogues for later portions of the verification pipeline appear in other files.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

def Target.byteDecode.decodeCoefficient {m d : ℕ} (b : Vector Bool (8 * (32 * d)))
  (F : Polynomial m) (i : ℕ) : Polynomial m :=
  F.set! i (∑ (j : Fin d), (Bool.toNat b[i * d + j]!) * 2^j.val)

def Target.byteDecode.recBody {m d : ℕ} (b : Vector Bool (8 * (32 * d))) (F : Polynomial m) (i : Nat) : Polynomial m :=
  List.foldl (byteDecode.decodeCoefficient b) F (List.range' i (256 - i))

def Target.byteDecode (d : ℕ) (B : Vector Byte (32 * d)) : Polynomial (m d) :=
  let b := bytesToBits B
  let F := Polynomial.zero (m d)
  byteDecode.recBody b F 0

def Target.byteDecode.eq_spec {d : ℕ} (B : Vector Byte (32 * d)) :
  byteDecode d B = Spec.byteDecode B := by
  unfold byteDecode recBody byteDecode.decodeCoefficient Spec.byteDecode
  simp only [bytesToBits.eq_spec, tsub_zero, Vector.Inhabited_getElem_eq_getElem!,
    Vector.set_eq_set!, bind_pure_comp, map_pure, forIn'_eq_forIn, forIn_eq_forIn_range', size,
    Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure,
    Id.run_map]
  congr

irreducible_def Target.byteDecode.decodeCoefficient.inv {m d : ℕ} (b : Vector Bool (8 * (32 * d)))
  (F : Polynomial m) (i : ℕ) : Prop :=
  -- Coefficients below `i` have been set
  (∀ i' < i, F[i']! = (∑ (j : Fin d), (Bool.toNat b[i' * d + j]!) * 2^j.val)) ∧
  -- Coefficients at or above `i` have not yet been set
  ∀ i' ∈ [i:256], F[i']! = 0

def Target.byteDecode.decodeCoefficient.spec {m d : ℕ} (b : Vector Bool (8 * (32 * d)))
  (F : Polynomial m) (i : ℕ) (hinv : inv b F i) (hi : i < 256 := by omega) :
  inv b (decodeCoefficient b F i) (i + 1) := by
  unfold decodeCoefficient
  simp_all only [inv, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    mem_std_range_step_one, and_imp, gt_iff_lt]
  rcases hinv with ⟨hinv1, hinv2⟩
  constructor
  . intro i' i'_lt_i_add_one
    dcases i_eq_i' : i = i'
    . rw [Vector.getElem!_set!]
      . rw [i_eq_i']
      . simp_all
    . rw [Vector.getElem!_set!_ne]
      . exact hinv1 i' (by omega)
      . exact i_eq_i'
  . intro i' i_add_one_le_i' i'_lt_256
    specialize hinv2 i' (by linarith) i'_lt_256
    rw [Vector.getElem!_set!_ne] <;> scalar_tac

def Target.byteDecode.recBody.spec {m d i : ℕ} (b : Vector Bool (8 * (32 * d))) (F : Polynomial m)
  (hF : decodeCoefficient.inv b F i) (hi : i < 256 := by omega) :
  decodeCoefficient.inv b (@recBody m d b F i) 256 := by
  have := decodeCoefficient.spec b F i hF
  dcases i_eq_255 : i = 255
  . simp [recBody, decodeCoefficient, i_eq_255, decodeCoefficient.inv] at *
    exact this
  . have recBodyUnfold : recBody b (byteDecode.decodeCoefficient b F i) (i + 1)  = recBody b F i := by
      simp [recBody, Nat.reduceSubDiff]
      have : 256 - i = (255 - i) + 1 := by omega
      rw [this]
      simp only [List.range'_succ, List.foldl_cons]
    rw [← recBodyUnfold]
    exact @spec m d (i+1) b (decodeCoefficient b F i) this (by omega)

def Target.byteDecode.decodeCoefficient.inv_0 {d : ℕ} (b : Vector Bool (8 * (32 * d))) :
  decodeCoefficient.inv b (Polynomial.zero (m d)) 0 := by simp [inv]

def Target.byteDecode.spec_aux {d : ℕ} (B : Vector Byte (32 * d)) :
  ∀ i < 256, (byteDecode d B)[i]! = ((∑ (j : Fin d), (Bool.toNat (bytesToBits B)[i * d + j]!) * 2^j.val) : ZMod (m d)) := by
  unfold byteDecode
  intro i i_lt_256
  simp only
  have h0 := @decodeCoefficient.inv_0 d (bytesToBits B)
  have h := recBody.spec (bytesToBits B) (Polynomial.zero (m d)) h0 (by omega : 0 < 256)
  rw [decodeCoefficient.inv] at h
  simp [h.1 i i_lt_256]

def Target.byteDecode.spec {d : ℕ} (B : Vector Byte (32 * d)) (hd : d < 13)
  (hB : ∀ i < 256, ∑ (a : Fin d),
    Bool.toNat (B[(d * i + a) / 8]!.testBit ((d * i + a) % 8)) * 2 ^ a.val < m d) :
  ∀ i < 256,
    (∀ j < d, (byteDecode d B)[i]!.val.testBit j = B[(d * i + j) / 8]!.testBit ((d * i + j) % 8)) ∧
    (∀ j : Nat, d ≤ j → (byteDecode d B)[i]!.val.testBit j = false) := by
  intro i i_lt_256
  rw [@spec_aux d B i i_lt_256]
  constructor
  . intro j j_lt_d
    have : B[(d * i + j) / 8]!.testBit ((d * i + j) % 8) = (bytesToBits B)[d * i + j]! := by
      have := bytesToBits.spec B
      rw [bytesToBits.post] at this
      rw [← this]
      . have : 8 * ((d * i + j) / 8) + (d * i + j) % 8 = d * i + j := by omega
        rw [this]
      . have : ((d * i + j) / 8) * 8 < 256 * d → (d * i + j) / 8 < 32 * d := by omega
        apply this
        have : (d * i + j) / 8 * 8 ≤ d * i + j := by omega
        apply Nat.lt_of_le_of_lt this
        have : j < d * 256 - d * i → d * i + j < 256 * d := by omega
        apply this
        rw [← Nat.mul_sub_left_distrib]
        have : d * 1 ≤ d * (256 - i) := by apply Nat.mul_le_mul <;> omega
        omega
      . simp_scalar
    rw [this]
    have h1 := Target.bytesToBits.spec B
    simp only [bytesToBits.post] at h1
    have h2 : ∀ j < d, (bytesToBits B)[i * d + j]! = B[(i * d + j) / 8]!.testBit ((i * d + j) % 8) := by
      intro j j_lt_d
      have : i * d + j < 256 * d := by
        have : j < 256 * d - i * d → i * d + j < 256 * d := by omega
        apply this
        rw [← Nat.mul_sub_right_distrib]
        have : 1 ≤ 256 - i := by omega
        exact Nat.lt_of_lt_of_le (by omega : j < 1 * d) (Nat.mul_le_mul_right d this)
      have : (i * d + j) / 8 < 32 * d := by omega
      have h2 := h1 ((i * d + j) / 8) this ((i * d + j) % 8) (by omega)
      have : 8 * ((i * d + j) / 8) + (i * d + j) % 8 = i * d + j := by scalar_tac
      rw [this] at h2
      exact h2
    simp only [Fin.is_lt, h2]
    rw [mul_comm d i, h2 j j_lt_d, mul_comm i d]
    specialize hB i i_lt_256
    let f := fun (x : Fin d) => (B[(d * i + ↑x) / 8]!.testBit ((d * i + ↑x) % 8))
    have h3 :=
      testBit_of_sum_mod_md d hd j j_lt_d $ fun (x : Fin d) => (B[(d * i + ↑x) / 8]!.testBit ((d * i + ↑x) % 8))
    rcases h3 with h3 | h3
    . rw [h3]
    . omega
  . intro j d_le_j
    apply Nat.testBit_eq_false_of_lt
    apply Nat.lt_of_lt_of_le (sum_bits_lt_mod_md hd _) (by scalar_tac +nonLin : 2 ^ d ≤ 2 ^ j)
