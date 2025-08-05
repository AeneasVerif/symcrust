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

lemma testBitOfAdd {x1 x2 y1 y2 : ℕ} (n : ℕ) (hx : ∀ i < n, x1.testBit i = x2.testBit i)
  (hy : ∀ i < n, y1.testBit i = y2.testBit i) : ∀ i < n, (x1 + y1).testBit i = (x2 + y2).testBit i := by
  sorry
