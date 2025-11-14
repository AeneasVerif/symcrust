import Symcrust.Spec

/-!
Properties about the polynomials
-/

#setup_aeneas_simps

namespace Symcrust

open Aeneas

/-!
# Polynomials
-/

namespace Spec

theorem Polynomial.eq_iff {n} (f g : Polynomial n) :
  f = g ↔ ∀ i < 256, f[i]! = g[i]! := by
  simp only [Vector.eq_iff_forall_eq_getElem!]

theorem Polynomial.eq_iff' (f g : Polynomial n) :
  f = g ↔ ∀ i < 128, (f[2 * i]! = g[2 * i]! ∧ f[2 * i + 1]! = g[2 * i + 1]!) := by
  rw [Polynomial.eq_iff]
  constructor <;> intros heq i hi
  . have h0 := heq (2 * i) (by omega)
    have h1 := heq (2 * i + 1) (by omega)
    simp only [h0, h1, and_self]
  . have h0 := heq (i / 2) (by omega)
    have h1 : 2 * (i / 2) = i ∨ 2 * (i / 2) + 1 = i := by omega
    cases h1 <;> simp_all only

@[simp, simp_lists_simps]
theorem Polynomial.getElem!_add (f g : Polynomial n) (i : Nat) :
  (f + g)[i]! = f[i]! + g[i]! := by
  simp [instHAddPolynomial]
  by_cases hi: i < 256
  . simp_lists
  . simp_lists
    simp [default]

@[simp, simp_lists_simps]
theorem Polynomial.getElem!_mul (f : Polynomial n) (x : ZMod n) (i : Nat) :
  (f * x)[i]! = f[i]! * x := by
  cases f; rename_i f hf
  fsimp only [instHMulPolynomialZMod, scalarMul]
  dcases hi : i < 256 <;> simp_lists
  fsimp only [default, zero_mul]

theorem Polynomial.add_assoc (f g h : Polynomial n) : f + g + h = f + (g + h) := by
  simp only [eq_iff, getElem!_add]
  intro i hi
  ring_nf

theorem Polynomial.add_comm (f g : Polynomial n) : f + g = g + f := by
  simp only [eq_iff, getElem!_add]
  intro i hi
  apply AddCommMagma.add_comm

@[simp]
theorem Polynomial.zero_add (f : Polynomial n) : Polynomial.zero n + f = f := by
  rw [eq_iff]
  simp +contextual only [zero, getElem!_add, Vector.getElem!_replicate, _root_.zero_add,
    implies_true]

@[simp]
theorem Polynomial.add_zero (f : Polynomial n) : f + Polynomial.zero n = f := by
  rw [eq_iff]
  simp +contextual only [zero, getElem!_add, Vector.getElem!_replicate, _root_.add_zero,
    implies_true]

@[simp, simp_lists_simps]
theorem Polynomial.zero_getElem! (i : Nat) :
  (Polynomial.zero n)[i]! = 0 := by
  simp [Polynomial.zero]
  by_cases hi: i < 256 <;>
  simp_all only [not_lt, Vector.getElem!_default, Vector.getElem!_replicate, default]

end Spec

end Symcrust
