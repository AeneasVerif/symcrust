import Symcrust.Spec

/-!
Properties about the polynomials
-/

attribute [-simp] List.getElem!_eq_getElem?_getD List.reduceReplicate Aeneas.SRRange.foldWhile_step

namespace Symcrust.Spec

open Aeneas

/-!
# Polynomials
-/

@[simp]
theorem Polynomial.getElem_eq_getElem! {i : Nat} (hi : i < 256)
  (p : Polynomial n) :
  p[i] = p[i]! := by
  unfold getElem getElem! instGetElemPolynomialNatZModLtOfNat instGetElem?OfGetElemOfDecidable decidableGetElem?
  simp; split_ifs; simp

@[simp]
theorem Polynomial.getElem!_eq  {n} (l : List (ZMod n)) (h : l.length = 256) (i : Nat) :
  (⟨ l, h ⟩ : Polynomial n)[i]! = l[i]! := by
  conv => lhs; unfold Polynomial getElem! instGetElem?OfGetElemOfDecidable
  simp only
  unfold decidableGetElem? instGetElemPolynomialNatZModLtOfNat
  simp only [dite_eq_ite]
  split_ifs <;> simp_all only [not_lt, List.getElem!_default]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some, *]
  rfl

@[simp]
theorem Polynomial.set_eq {n} (l : List (ZMod n)) (h : l.length = 256) (i : Nat) (x : ZMod n) :
  Polynomial.set ⟨ l, h ⟩ i x = (⟨ l.set i x, by simp [h] ⟩ : Polynomial n) := by rfl

theorem Polynomial.eq_iff (f g : Polynomial n) :
  f = g ↔ ∀ i < 256, f[i]! = g[i]! := by
  cases f; rename_i f hf
  cases g; rename_i g hg
  simp
  simp only [List.eq_iff_eq_getElem!, true_and, hf, hg]

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
  cases f; rename_i f hf
  cases g; rename_i g hg
  simp [instHAddPolynomial]
  dcases hi : i < 256
  . simp [*]
  . simp at hi
    simp [*, default]

@[simp, simp_lists_simps]
theorem Polynomial.getElem!_mul (f : Polynomial n) (x : ZMod n) (i : Nat) :
  (f * x)[i]! = f[i]! * x := by
  cases f; rename_i f hf
  fsimp only [instHMulPolynomialZMod, scalarMul, getElem!_eq]
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

theorem Polynomial.set_comm {i j : Nat} (h : Nat.not_eq i j)
  (p : Polynomial n) (x y : ZMod n) :
  (p.set i x).set j y = (p.set j y).set i x := by
  cases p; simp [*]
  rw [List.set_comm]
  simp only [Nat.not_eq, ne_eq, lt_or_lt_iff_ne] at h
  omega

@[simp_lists_simps]
theorem Polynomial.set_comm' {i j : Nat} (h : j < i)
  (p : Polynomial n) (x y : ZMod n) :
  (p.set i x).set j y = (p.set j y).set i x := by
  rw [Polynomial.set_comm]
  omega

@[simp_lists_simps]
theorem Polynomial.getElem!_set_self {i : Nat} (hi : i < 256)
  (p : Polynomial n) (x : ZMod n) :
  (p.set i x)[i]! = x := by
  cases p; simp [*]

@[simp_lists_simps]
theorem Polynomial.getElem!_set_neq {i j : Nat} (h : i ≠ j)
  (p : Polynomial n) (x : ZMod n) :
  (p.set i x)[j]! = p[j]! := by
  cases p; simp [*]

@[simp]
theorem Polynomial.zero_add (f : Polynomial n) : Polynomial.zero n + f = f := by
  simp +contextual only [zero, eq_iff, getElem!_add, getElem!_eq, List.getElem!_replicate,
    _root_.zero_add, implies_true]

@[simp]
theorem Polynomial.add_zero (f : Polynomial n) : f + Polynomial.zero n = f := by
  simp +contextual only [zero, eq_iff, getElem!_add, getElem!_eq, List.getElem!_replicate,
    _root_.add_zero, implies_true]

@[simp, simp_lists_simps]
theorem Polynomial.zero_getElem! (i : Nat) :
  (Polynomial.zero n)[i]! = 0 := by
  simp [Polynomial.zero]
  dcases i < 256 <;>
  simp_all only [List.getElem!_replicate, not_lt, List.length_replicate, List.getElem!_length_le, default]

end Symcrust.Spec
