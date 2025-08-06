import Symcrust.Spec
import Symcrust.Code.Funs
import Symcrust.Brute
import Symcrust.Properties.SamplePolyCBD.Target2Code

/-!
This file contains helper lemmas that are used in both `Target2Eta2Proofs.lean` and `Target2Eta3Proofs.lean`
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.Std Aeneas.SRRange

set_option maxHeartbeats 1000000

lemma testBitMod256 (a k : ℕ) (hk : k < 6) : (a % 256).testBit k = a.testBit k := by
  have hk2 : decide (k < 6) := by simp [hk]
  rw [← Nat.testBit_two_pow_sub_one] at hk2
  rw [← Bool.and_true (a.testBit k), ← hk2, ← Nat.testBit_and, (by decide : 256 = 2^8),
    Nat.testBit_mod_two_pow]
  simp_scalar
  simp [hk2]

lemma BitVec.getElem!_eq_mask_ne_zero {x : BitVec 64} (k : ℕ) (hk : k < 64) :
  x[k]! = ((x &&& BitVec.ofNat 64 (2^k)) != 0#64) := by
  rw [(by revert k; brute : BitVec.ofNat 64 (2 ^ k) = 1#64 <<< k),
    ← BitVec.twoPow_eq, BitVec.and_twoPow, BitVec.getLsbD_eq_getElem hk, BitVec.getElem!_eq_getElem _ _ hk]
  by_cases h : x[k]
  . simp only [h, ↓reduceIte, Bool.true_eq, bne_iff_ne, ne_eq]
    clear h
    revert k
    brute
  . simp [h]

lemma Nat.mod_eq_of_bits_eq (x y n : ℕ) (hx : ∀ i < n, x.testBit i = y.testBit i) : x % 2^n = y % 2^n := by
  rw [← BitVec.toNat_ofNat, ← BitVec.toNat_ofNat, BitVec.toNat_inj]
  ext i hi
  rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem, BitVec.getElem!_eq_testBit_toNat,
    BitVec.getElem!_eq_testBit_toNat]
  simp only [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, hi, decide_true, hx i hi, Bool.true_and]

lemma testBitOfAdd {x1 x2 y1 y2 : ℕ} (n : ℕ) (hx : ∀ i < n, x1.testBit i = x2.testBit i)
  (hy : ∀ i < n, y1.testBit i = y2.testBit i) : ∀ i < n, (x1 + y1).testBit i = (x2 + y2).testBit i := by
  intro i hi
  rw [← Bool.true_and ((x1 + y1).testBit i), ← Bool.true_and ((x2 + y2).testBit i), ← decide_eq_true hi,
    ← Nat.testBit_mod_two_pow, ← Nat.testBit_mod_two_pow]
  conv => lhs; rw [Nat.add_mod]
  conv => rhs; rw [Nat.add_mod]
  rw [Nat.mod_eq_of_bits_eq x1 x2 _ hx, Nat.mod_eq_of_bits_eq y1 y2 _ hy]
