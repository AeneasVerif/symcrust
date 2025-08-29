import Lean
import Aeneas

/-  This file contains various types and definitions used by `brute`. The important ones are:
    - `IsNatLike`: A typeclass which defines the set of types that `brute` supports. Currently,
      it is possible to build `IsNatLike t` instances for the types `Nat`, `BitVec n` and
      `UScalar t'` where `t' ≠ UScalarTy.Usize`.
    - `mkFoldN` for `N ∈ [1, 2, 3, 4, 5]`: These are the functions that `brute` evaluates to
      confirm that `f` (the decidable function obtained by extracting all of the original goal's
      supported universal quantifiers) is true for all applicable inputs. For example, if given
      the original goal `∀ x < b, ∀ y < x, f x y`, `brute` would confirm that the goal holds
      by evaluating `mkFold2 b (fun x => x) f true`.
    - `ofMkFoldNEqTrue` for `N ∈ [1, 2, 3, 4, 5]`: These are the lemmas relating `mkFoldN` to the
      original goal that `brute` builds a proof term for. -/

open Lean Meta Parser Elab Tactic Aeneas Aeneas.Std

namespace Brute

inductive IsNatLikePf (t : Type) where
  | isNatPf : t = Nat → IsNatLikePf t
  | isBitVecPf : PSigma (fun n : Nat => t = BitVec n) → IsNatLikePf t
  | isUScalarPf : PSigma (fun t' : UScalarTy => t' ≠ UScalarTy.Usize ∧ t = UScalar t') → IsNatLikePf t

class IsNatLike (t : Type) where
  pf : IsNatLikePf t

instance (t : Type) [h : IsNatLike t] : LT t where
  lt :=
    match h.pf with
    | .isNatPf pf => fun x y => cast pf x < cast pf y
    | .isBitVecPf pf => fun x y => cast pf.2 x < cast pf.2 y
    | .isUScalarPf pf => fun x y => cast pf.2.2 x < cast pf.2.2 y

def UScalar.ofNat' {t : UScalarTy} (x : Nat) : UScalar t :=
  UScalar.ofNat (x % (UScalar.cMax t + 1)) (Nat.le_of_lt_succ (Nat.mod_lt _ (by simp)))

lemma UScalar.ofNat'_val_eq {t : UScalarTy} (ht : t ≠ UScalarTy.Usize) (x : UScalar t) :
  UScalar.ofNat' x.val = x := by
  unfold UScalar.ofNat'
  have : x.val % (UScalar.cMax t + 1) = x := by
    simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
    rw [← UScalar.bv_toNat, UScalar.cMax_eq_pow_cNumBits, UScalarTy.cNumBits]
    . simp only [UScalar.bv_toNat, Nat.ofNat_pos, SimpScalar.one_le_pow, Nat.sub_add_cancel]
      apply BitVec.toNat_lt_twoPow_of_le
      rfl
    . exact ht
  simp [this]

def mkFold1 {t : Type} [h : IsNatLike t] (b : t) (f : t → Bool) (acc : Bool) : Bool :=
  match h.pf with
  | .isNatPf pf =>
    Fin.foldr (cast pf b)
      (fun (x : Fin (cast pf b)) (acc : Bool) => acc && f (cast pf.symm x.1)) acc
  | .isBitVecPf pf =>
    Fin.foldr (cast pf.2 b).toNat
      (fun (x : Fin (cast pf.2 b).toNat) (acc : Bool) => acc && f (cast pf.2.symm x.1)) acc
  | .isUScalarPf pf =>
    Fin.foldr (cast pf.2.2 b).val
      (fun (x : Fin (cast pf.2.2 b).val) (acc : Bool) => acc && f
        (cast pf.2.2.symm (UScalar.ofNat' x.1))) acc

theorem ofMkFold1EqTrueAux {t : Type} [h : IsNatLike t] (b : t) (f : t → Bool)
  (acc : Bool) : mkFold1 b f acc = (acc ∧ ∀ x < b, f x) := by
  unfold mkFold1
  split
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [gt_iff_lt, eq_iff_iff]
    induction (cast ht b) generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      rw [ih (acc && f (cast ht.symm b'))]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.symm b')
          simp only [cast_cast, cast_eq, lt_add_iff_pos_right, zero_lt_one, forall_const] at h2
          exact h2
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [BitVec.natCast_eq_ofNat, gt_iff_lt, eq_iff_iff]
    rw [LT.lt, instLTBitVec]
    simp only [gt_iff_lt]
    induction (cast ht.2 b).toNat generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      rw [ih (acc && f (@cast (BitVec ht.fst) t ht.2.symm (BitVec.ofNat ht.fst b')))]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.symm ((BitVec.ofNat ht.fst b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [ne_eq, UScalar.lt_equiv, gt_iff_lt, eq_iff_iff]
    induction (cast ht.2.2 b).val generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      rw [ih (acc && f (@cast (UScalar ht.fst) t ht.2.2.symm (UScalar.ofNat' b')))]
      constructor
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← h2, ← hx, UScalar.ofNat'_val_eq ht.2.1, cast_cast, cast_eq]
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.2.symm ((UScalar.ofNat' b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)

theorem ofMkFold1EqTrue {t : Type} [h : IsNatLike t] (b : t) (f : t → Bool) :
  mkFold1 b f true → ∀ x < b, f x := by
  simp only [ofMkFold1EqTrueAux, true_and, imp_self]

def mkFold2 {t1 t2 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : t1 → t2 → Bool) (acc : Bool) : Bool :=
  match h1.pf with
  | .isNatPf pf =>
    Fin.foldr (cast pf b1)
      (fun (x : Fin (cast pf b1)) (acc : Bool) =>
        mkFold1 (b2 (cast pf.symm x.1)) (f (cast pf.symm x.1)) acc) acc
  | .isBitVecPf pf =>
    Fin.foldr (cast pf.2 b1).toNat
      (fun (x : Fin (cast pf.2 b1).toNat) (acc : Bool) =>
        mkFold1 (b2 (cast pf.2.symm x.1)) (f (cast pf.2.symm x.1)) acc) acc
  | .isUScalarPf pf =>
    Fin.foldr (cast pf.2.2 b1).val
      (fun (x : Fin (cast pf.2.2 b1).val) (acc : Bool) =>
        mkFold1 (b2 (cast pf.2.2.symm (UScalar.ofNat' x.1)))
          (f (cast pf.2.2.symm (UScalar.ofNat' x.1))) acc) acc

theorem ofMkFold2EqTrueAux {t1 t2 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] (b1 : t1)
  (b2 : t1 → t2) (f : t1 → t2 → Bool) (acc : Bool) :
  mkFold2 b1 b2 f acc = (acc ∧ ∀ x < b1, ∀ y < b2 x, f x y) := by
  unfold mkFold2
  split
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [gt_iff_lt, eq_iff_iff]
    induction (cast ht b1) generalizing acc
    . simp
    . next b1' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' := mkFold1 (b2 (cast ht.symm b1')) (f (cast ht.symm b1')) acc
      rw [ih acc', ofMkFold1EqTrueAux (b2 (cast ht.symm b1')) (f (cast ht.symm b1')) acc]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.symm b1')
          simp only [cast_cast, cast_eq, lt_add_iff_pos_right, zero_lt_one, forall_const] at h2
          exact h2
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [BitVec.natCast_eq_ofNat, gt_iff_lt, eq_iff_iff]
    rw [LT.lt, instLTBitVec]
    simp only [gt_iff_lt]
    induction (cast ht.2 b1).toNat generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        @mkFold1 t2 h2 (b2 (cast ht.2.symm (BitVec.ofNat ht.1 b')))
          (f (cast ht.2.symm (BitVec.ofNat ht.1 b'))) acc
      rw [ih acc', ofMkFold1EqTrueAux (b2 (cast ht.2.symm (BitVec.ofNat ht.1 b')))]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.symm ((BitVec.ofNat ht.fst b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [ne_eq, UScalar.lt_equiv, gt_iff_lt, eq_iff_iff]
    induction (cast ht.2.2 b1).val generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        mkFold1 (b2 (cast ht.2.2.symm (UScalar.ofNat' b')))
          (f (cast ht.2.2.symm (UScalar.ofNat' b'))) acc
      rw [ih acc', ofMkFold1EqTrueAux (b2 (cast ht.2.2.symm (UScalar.ofNat' b')))]
      constructor
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [UScalar.ofNat'_val_eq ht.2.1, cast_cast, cast_eq] at h2
          exact h2
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.2.symm ((UScalar.ofNat' b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)

theorem ofMkFold2EqTrue {t1 t2 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : t1 → t2 → Bool) : mkFold2 b1 b2 f true → ∀ x < b1, ∀ y < b2 x, f x y := by
  simp only [ofMkFold2EqTrueAux, true_and, imp_self]

def mkFold3 {t1 t2 t3 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] [h3 : IsNatLike t3] (b1 : t1)
  (b2 : t1 → t2) (b3 : t1 → t2 → t3) (f : t1 → t2 → t3 → Bool) (acc : Bool) : Bool :=
  match h1.pf with
  | .isNatPf pf =>
    Fin.foldr (cast pf b1)
      (fun (x : Fin (cast pf b1)) (acc : Bool) =>
        mkFold2 (b2 (cast pf.symm x.1)) (b3 (cast pf.symm x.1)) (f (cast pf.symm x.1)) acc) acc
  | .isBitVecPf pf =>
    Fin.foldr (cast pf.2 b1).toNat
      (fun (x : Fin (cast pf.2 b1).toNat) (acc : Bool) =>
        mkFold2 (b2 (cast pf.2.symm x.1)) (b3 (cast pf.2.symm x.1)) (f (cast pf.2.symm x.1)) acc) acc
  | .isUScalarPf pf =>
    Fin.foldr (cast pf.2.2 b1).val
      (fun (x : Fin (cast pf.2.2 b1).val) (acc : Bool) =>
        mkFold2 (b2 (cast pf.2.2.symm (UScalar.ofNat' x.1))) (b3 (cast pf.2.2.symm (UScalar.ofNat' x.1)))
          (f (cast pf.2.2.symm (UScalar.ofNat' x.1))) acc) acc

theorem ofMkFold3EqTrueAux {t1 t2 t3 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] [h3 : IsNatLike t3]
  (b1 : t1) (b2 : t1 → t2) (b3 : t1 → t2 → t3) (f : t1 → t2 → t3 → Bool) (acc : Bool) :
  mkFold3 b1 b2 b3 f acc = (acc ∧ ∀ x < b1, ∀ y < b2 x, ∀ z < b3 x y, f x y z) := by
  unfold mkFold3
  split
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [gt_iff_lt, eq_iff_iff]
    induction (cast ht b1) generalizing acc
    . simp
    . next b1' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' := mkFold2 (b2 (cast ht.symm b1')) (b3 (cast ht.symm b1')) (f (cast ht.symm b1')) acc
      rw [ih acc', ofMkFold2EqTrueAux (b2 (cast ht.symm b1'))]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.symm b1')
          simp only [cast_cast, cast_eq, lt_add_iff_pos_right, zero_lt_one, forall_const] at h2
          exact h2
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [BitVec.natCast_eq_ofNat, gt_iff_lt, eq_iff_iff]
    rw [LT.lt, instLTBitVec]
    simp only [gt_iff_lt]
    induction (cast ht.2 b1).toNat generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        mkFold2 (b2 (cast ht.2.symm (BitVec.ofNat ht.fst b')))
          (b3 (cast ht.2.symm (BitVec.ofNat ht.fst b')))
          (f (cast ht.2.symm (BitVec.ofNat ht.fst b'))) acc
      rw [ih acc', ofMkFold2EqTrueAux (b2 (cast ht.2.symm (BitVec.ofNat ht.1 b')))]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.symm ((BitVec.ofNat ht.fst b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [ne_eq, UScalar.lt_equiv, gt_iff_lt, eq_iff_iff]
    induction (cast ht.2.2 b1).val generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        mkFold2 (b2 (cast ht.2.2.symm (UScalar.ofNat' b'))) (b3 (cast ht.2.2.symm (UScalar.ofNat' b')))
          (f (cast ht.2.2.symm (UScalar.ofNat' b'))) acc
      rw [ih acc', ofMkFold2EqTrueAux (b2 (cast ht.2.2.symm (UScalar.ofNat' b')))]
      constructor
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [UScalar.ofNat'_val_eq ht.2.1, cast_cast, cast_eq] at h2
          exact h2
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.2.symm ((UScalar.ofNat' b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)

theorem ofMkFold3EqTrue {t1 t2 t3 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] [h3 : IsNatLike t3]
  (b1 : t1) (b2 : t1 → t2) (b3 : t1 → t2 → t3) (f : t1 → t2 → t3 → Bool) :
  mkFold3 b1 b2 b3 f true →  ∀ x < b1, ∀ y < b2 x, ∀ z < b3 x y, f x y z := by
  simp only [ofMkFold3EqTrueAux, true_and, imp_self]

def mkFold4 {t1 t2 t3 t4 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] [h3 : IsNatLike t3]
  [h4 : IsNatLike t4] (b1 : t1) (b2 : t1 → t2) (b3 : t1 → t2 → t3) (b4 : t1 → t2 → t3 → t4)
  (f : t1 → t2 → t3 → t4 → Bool) (acc : Bool) : Bool :=
  match h1.pf with
  | .isNatPf pf =>
    Fin.foldr (cast pf b1)
      (fun (x : Fin (cast pf b1)) (acc : Bool) =>
        mkFold3 (b2 (cast pf.symm x.1)) (b3 (cast pf.symm x.1)) (b4 (cast pf.symm x.1))
          (f (cast pf.symm x.1)) acc) acc
  | .isBitVecPf pf =>
    Fin.foldr (cast pf.2 b1).toNat
      (fun (x : Fin (cast pf.2 b1).toNat) (acc : Bool) =>
        mkFold3 (b2 (cast pf.2.symm x.1)) (b3 (cast pf.2.symm x.1)) (b4 (cast pf.2.symm x.1))
          (f (cast pf.2.symm x.1)) acc) acc
  | .isUScalarPf pf =>
    Fin.foldr (cast pf.2.2 b1).val
      (fun (x : Fin (cast pf.2.2 b1).val) (acc : Bool) =>
        mkFold3 (b2 (cast pf.2.2.symm (UScalar.ofNat' x.1))) (b3 (cast pf.2.2.symm (UScalar.ofNat' x.1)))
          (b4 (cast pf.2.2.symm (UScalar.ofNat' x.1))) (f (cast pf.2.2.symm (UScalar.ofNat' x.1))) acc) acc

theorem ofMkFold4EqTrueAux {t1 t2 t3 t4 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] [h3 : IsNatLike t3]
  [h4 : IsNatLike t4] (b1 : t1) (b2 : t1 → t2) (b3 : t1 → t2 → t3) (b4 : t1 → t2 → t3 → t4)
  (f : t1 → t2 → t3 → t4 → Bool) (acc : Bool) :
  mkFold4 b1 b2 b3 b4 f acc = (acc ∧ ∀ x < b1, ∀ y < b2 x, ∀ z < b3 x y, ∀ a < b4 x y z, f x y z a) := by
  unfold mkFold4
  split
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [gt_iff_lt, eq_iff_iff]
    induction (cast ht b1) generalizing acc
    . simp
    . next b1' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        mkFold3 (b2 (cast ht.symm b1')) (b3 (cast ht.symm b1')) (b4 (cast ht.symm b1'))
          (f (cast ht.symm b1')) acc
      rw [ih acc', ofMkFold3EqTrueAux (b2 (cast ht.symm b1'))]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.symm b1')
          simp only [cast_cast, cast_eq, lt_add_iff_pos_right, zero_lt_one, forall_const] at h2
          exact h2
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [BitVec.natCast_eq_ofNat, gt_iff_lt, eq_iff_iff]
    rw [LT.lt, instLTBitVec]
    simp only [gt_iff_lt]
    induction (cast ht.2 b1).toNat generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        mkFold3 (b2 (cast ht.2.symm (BitVec.ofNat ht.fst b')))
          (b3 (cast ht.2.symm (BitVec.ofNat ht.fst b')))
          (b4 (cast ht.2.symm (BitVec.ofNat ht.fst b')))
          (f (cast ht.2.symm (BitVec.ofNat ht.fst b'))) acc
      rw [ih acc', ofMkFold3EqTrueAux (b2 (cast ht.2.symm (BitVec.ofNat ht.1 b')))]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.symm ((BitVec.ofNat ht.fst b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [ne_eq, UScalar.lt_equiv, gt_iff_lt, eq_iff_iff]
    induction (cast ht.2.2 b1).val generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        mkFold3 (b2 (cast ht.2.2.symm (UScalar.ofNat' b'))) (b3 (cast ht.2.2.symm (UScalar.ofNat' b')))
          (b4 (cast ht.2.2.symm (UScalar.ofNat' b'))) (f (cast ht.2.2.symm (UScalar.ofNat' b'))) acc
      rw [ih acc', ofMkFold3EqTrueAux (b2 (cast ht.2.2.symm (UScalar.ofNat' b')))]
      constructor
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [UScalar.ofNat'_val_eq ht.2.1, cast_cast, cast_eq] at h2
          exact h2
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.2.symm ((UScalar.ofNat' b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)

theorem ofMkFold4EqTrue {t1 t2 t3 t4 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] [h3 : IsNatLike t3]
  [h4 : IsNatLike t4] (b1 : t1) (b2 : t1 → t2) (b3 : t1 → t2 → t3) (b4 : t1 → t2 → t3 → t4)
  (f : t1 → t2 → t3 → t4 → Bool) :
  mkFold4 b1 b2 b3 b4 f true → ∀ x < b1, ∀ y < b2 x, ∀ z < b3 x y, ∀ a < b4 x y z, f x y z a := by
  simp only [ofMkFold4EqTrueAux, true_and, imp_self]

def mkFold5 {t1 t2 t3 t4 t5 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] [h3 : IsNatLike t3]
  [h4 : IsNatLike t4] [h5 : IsNatLike t5] (b1 : t1) (b2 : t1 → t2) (b3 : t1 → t2 → t3)
  (b4 : t1 → t2 → t3 → t4) (b5 : t1 → t2 → t3 → t4 → t5) (f : t1 → t2 → t3 → t4 → t5 → Bool) (acc : Bool) : Bool :=
  match h1.pf with
  | .isNatPf pf =>
    Fin.foldr (cast pf b1)
      (fun (x : Fin (cast pf b1)) (acc : Bool) =>
        mkFold4 (b2 (cast pf.symm x.1)) (b3 (cast pf.symm x.1)) (b4 (cast pf.symm x.1))
          (b5 (cast pf.symm x.1)) (f (cast pf.symm x.1)) acc) acc
  | .isBitVecPf pf =>
    Fin.foldr (cast pf.2 b1).toNat
      (fun (x : Fin (cast pf.2 b1).toNat) (acc : Bool) =>
        mkFold4 (b2 (cast pf.2.symm x.1)) (b3 (cast pf.2.symm x.1)) (b4 (cast pf.2.symm x.1))
          (b5 (cast pf.2.symm x.1)) (f (cast pf.2.symm x.1)) acc) acc
  | .isUScalarPf pf =>
    Fin.foldr (cast pf.2.2 b1).val
      (fun (x : Fin (cast pf.2.2 b1).val) (acc : Bool) =>
        mkFold4 (b2 (cast pf.2.2.symm (UScalar.ofNat' x.1)))
          (b3 (cast pf.2.2.symm (UScalar.ofNat' x.1)))
          (b4 (cast pf.2.2.symm (UScalar.ofNat' x.1)))
          (b5 (cast pf.2.2.symm (UScalar.ofNat' x.1)))
          (f (cast pf.2.2.symm (UScalar.ofNat' x.1))) acc) acc

theorem ofMkFold5EqTrueAux {t1 t2 t3 t4 t5 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] [h3 : IsNatLike t3]
  [h4 : IsNatLike t4] [h5 : IsNatLike t5] (b1 : t1) (b2 : t1 → t2) (b3 : t1 → t2 → t3)
  (b4 : t1 → t2 → t3 → t4) (b5 : t1 → t2 → t3 → t4 → t5) (f : t1 → t2 → t3 → t4 → t5 → Bool) (acc : Bool) :
  mkFold5 b1 b2 b3 b4 b5 f acc =
  (acc ∧ ∀ x < b1, ∀ y < b2 x, ∀ z < b3 x y, ∀ a < b4 x y z, ∀ b < b5 x y z a, f x y z a b) := by
  unfold mkFold5
  split
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [gt_iff_lt, eq_iff_iff]
    induction (cast ht b1) generalizing acc
    . simp
    . next b1' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        mkFold4 (b2 (cast ht.symm b1')) (b3 (cast ht.symm b1')) (b4 (cast ht.symm b1'))
          (b5 (cast ht.symm b1')) (f (cast ht.symm b1')) acc
      rw [ih acc', ofMkFold4EqTrueAux (b2 (cast ht.symm b1'))]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.symm b1')
          simp only [cast_cast, cast_eq, lt_add_iff_pos_right, zero_lt_one, forall_const] at h2
          exact h2
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [BitVec.natCast_eq_ofNat, gt_iff_lt, eq_iff_iff]
    rw [LT.lt, instLTBitVec]
    simp only [gt_iff_lt]
    induction (cast ht.2 b1).toNat generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        mkFold4 (b2 (cast ht.2.symm (BitVec.ofNat ht.fst b')))
          (b3 (cast ht.2.symm (BitVec.ofNat ht.fst b')))
          (b4 (cast ht.2.symm (BitVec.ofNat ht.fst b')))
          (b5 (cast ht.2.symm (BitVec.ofNat ht.fst b')))
          (f (cast ht.2.symm (BitVec.ofNat ht.fst b'))) acc
      rw [ih acc', ofMkFold4EqTrueAux (b2 (cast ht.2.symm (BitVec.ofNat ht.1 b')))]
      constructor
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, cast_cast, cast_eq] at h2
          exact h2
      . simp only [Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.symm ((BitVec.ofNat ht.fst b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [ne_eq, UScalar.lt_equiv, gt_iff_lt, eq_iff_iff]
    induction (cast ht.2.2 b1).val generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      tlet acc' :=
        mkFold4
          (b2 (cast ht.2.2.symm (UScalar.ofNat' b')))
          (b3 (cast ht.2.2.symm (UScalar.ofNat' b')))
          (b4 (cast ht.2.2.symm (UScalar.ofNat' b')))
          (b5 (cast ht.2.2.symm (UScalar.ofNat' b')))
          (f (cast ht.2.2.symm (UScalar.ofNat' b'))) acc
      rw [ih acc', ofMkFold4EqTrueAux (b2 (cast ht.2.2.symm (UScalar.ofNat' b')))]
      constructor
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2 h3
        simp only [h1, true_and]
        intro x hx
        rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with hx | hx
        . exact h3 x hx
        . rw [← hx] at h2
          simp only [UScalar.ofNat'_val_eq ht.2.1, cast_cast, cast_eq] at h2
          exact h2
      . simp only [ne_eq, Bool.and_eq_true, and_assoc, and_imp]
        intro h1 h2
        simp only [h1, true_and]
        constructor
        . specialize h2 (cast ht.2.2.symm ((UScalar.ofNat' b')))
          simp only [cast_cast, cast_eq, BitVec.toNat_ofNat] at h2
          exact h2 $ Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_self b')
        . intro x hx
          exact h2 x (by omega)

theorem ofMkFold5EqTrue {t1 t2 t3 t4 t5 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] [h3 : IsNatLike t3]
  [h4 : IsNatLike t4] [h5 : IsNatLike t5] (b1 : t1) (b2 : t1 → t2) (b3 : t1 → t2 → t3)
  (b4 : t1 → t2 → t3 → t4) (b5 : t1 → t2 → t3 → t4 → t5) (f : t1 → t2 → t3 → t4 → t5 → Bool) :
  mkFold5 b1 b2 b3 b4 b5 f true →
  ∀ x < b1, ∀ y < b2 x, ∀ z < b3 x y, ∀ a < b4 x y z, ∀ b < b5 x y z a, f x y z a b := by
  simp only [ofMkFold5EqTrueAux, true_and, imp_self]

end Brute
