import Symcrust.Spec.Spec
import Mathlib.Algebra.BigOperators.Fin
import Symcrust.Brute

/-!
This file contains various helper lemmas used in the DecodeDecompress files.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

lemma testBit_of_sum_mod_md :
  ∀ d < 13, ∀ j : Nat, ∀ hj : j < d, ∀ f : Fin d → Bool,
  (∑ (x : Fin d), (f x).toNat * (2 : ZMod (m d)) ^ (x : ℕ)).val.testBit j = f ⟨j, hj⟩ ∨
  ∑ (x : Fin d), Bool.toNat (f x) * 2 ^ x.val ≥ m d := by
  decide +native -- `brute` used to be able to solve this, but after the refactor, the dependency on `hj` is a problem

lemma testBit_of_sum :
  ∀ d < 13, ∀ j : Nat, ∀ hj : j < d, ∀ f : Fin d → Bool,
  (∑ (x : Fin d), (f x).toNat * 2 ^ (x : ℕ)).testBit j = f ⟨j, hj⟩ := by
  decide +native -- `brute` used to be able to solve this, but after the refactor, the dependency on `hj` is a problem

lemma bitwise_or_eq_and (x y d accSize : ℕ) (hd : d < 13) (h : accSize < d) (hx : x < 2^accSize)
  (hy : y < 2^(d - accSize)) : x ||| (y <<< accSize) = x + (y <<< accSize) := by
  revert y
  revert x
  revert accSize
  revert d
  brute

lemma testBit_of_add1 (x y d accSize k : ℕ) (hd : d < 13) (h : accSize < d) (hk : k < accSize)
  (hx : x < 2^accSize) (hy : y < 2^(d - accSize)) : (x + y <<< accSize).testBit k = x.testBit k := by
  revert k
  revert y
  revert x
  revert accSize
  revert d
  brute

lemma testBit_of_add2 (x y d accSize k : ℕ) (hd : d < 13) (h : accSize < k + 1) (hk : k < d)
  (hx : x < 2^accSize) (hy : y < 2^(d - accSize)) : (x + y <<< accSize).testBit k = y.testBit (k - accSize) := by
  revert y
  revert x
  revert accSize
  revert k
  revert d
  brute

lemma sum_bits_lt {d : ℕ} (hd : d < 13) (f : Fin d → Bool) :
  ∑ a : Fin d, (f a).toNat * 2 ^ a.val < 2 ^ d := by
  revert d
  brute

theorem sum_bits_lt_mod_md {d : ℕ} (hd : d < 13) (f : Fin d → Bool) :
  (∑ a : Fin d, (f a).toNat * (2 : ZMod (m d)) ^ a.val).val < 2 ^ d := by
  revert d
  brute

lemma sum_shift_lt (x y xBits d : ℕ) (hx : x < 2 ^ xBits) (hy : y < 2 ^ (d - xBits)) (hd : d < 13)
  (hXBits : xBits < d) : x + y <<< xBits < 2^d := by
  revert y
  revert x
  revert xBits
  revert d
  brute

lemma lt_num_bits {n num_bits : ℕ} {x : BitVec (8 * n)} (h : ∀ j ∈ [num_bits: 8 * n], x[j]! = false) :
  x.toNat < 2 ^ num_bits := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [← BitVec.getElem!_eq_testBit_toNat]
  simp only [mem_std_range_step_one, and_imp] at h
  dcases hi2 : i < 8 * n
  . exact h i hi hi2
  . rw [BitVec.getElem!_eq_false]
    omega

lemma sum_le_sum1 {d num_bits : ℕ} (hd1 : d < 13) (hd2 : num_bits < d) (f : Fin d → Bool) :
  ∑ a : Fin num_bits, (f ⟨a, by omega⟩).toNat * 2 ^ a.val ≤ ∑ a : Fin d, (f a).toNat * 2 ^ a.val := by
  revert num_bits
  revert d
  brute

lemma sum_le_sum2 {d num_bits : ℕ} (hd1 : d < 13) (hd2 : num_bits < d) (f : Fin d → Bool) :
  ∑ a : Fin (d - num_bits), (f ⟨a.val + num_bits, by omega⟩).toNat * 2 ^ a.val ≤ ∑ a : Fin d, (f a).toNat * 2 ^ a.val := by
  revert num_bits
  revert d
  brute

lemma md_le_two_pow_d {d : ℕ} (hd : d < 13) : m d ≤ 2 ^ d := by
  unfold m
  split
  . exact Nat.le_refl (2 ^ d)
  . simp only [Q, (by omega : d = 12), Nat.reducePow, Nat.reduceLeDiff]
