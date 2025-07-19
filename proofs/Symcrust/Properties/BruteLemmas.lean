import Lean
import Aeneas

open Lean Meta Parser Elab Tactic Aeneas Aeneas.Std

namespace Brute

class IsNatLike (t : Type) where
  pf : PSum (t = Nat) (PSum (PSigma (fun n : Nat => t = BitVec n))
    (PSigma (fun t' : UScalarTy => t' ≠ UScalarTy.Usize ∧ t = UScalar t')))

instance (t : Type) [h : IsNatLike t] : LT t where
  lt :=
    match h.pf with
    | .inl pf => fun x y => cast pf x < cast pf y
    | .inr (.inl pf) => fun x y => cast pf.2 x < cast pf.2 y
    | .inr (.inr pf) => fun x y => cast pf.2.2 x < cast pf.2.2 y

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

def mkFold1 {t : Type} [h : IsNatLike t] (b : t) (f : (x : t) → Bool) (acc : Bool) : Bool :=
  match h.pf with
  | .inl pf =>
    Fin.foldr (cast pf b)
      (fun (x : Fin (cast pf b)) (acc : Bool) => acc && f (cast pf.symm x.1)) acc
  | .inr (.inl pf) =>
    Fin.foldr (cast pf.2 b).toNat
      (fun (x : Fin (cast pf.2 b).toNat) (acc : Bool) => acc && f (cast pf.2.symm x.1)) acc
  | .inr (.inr pf) =>
    Fin.foldr (cast pf.2.2 b).val
      (fun (x : Fin (cast pf.2.2 b).val) (acc : Bool) => acc && f
        (cast pf.2.2.symm (UScalar.ofNat' x.1))) acc

theorem ofMkFold1EqTrueAux {t : Type} [h : IsNatLike t] (b : t) (f : (x : t) → Bool)
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

theorem ofMkFold1EqTrue {t : Type} [h : IsNatLike t] (b : t) (f : (x : t) → Bool) :
  mkFold1 b f true → ∀ x < b, f x := by
  simp only [ofMkFold1EqTrueAux, true_and, imp_self]

def mkFold2 {t1 t2 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : (x : t1) → (y : t2) → Bool) (acc : Bool) : Bool :=
  match h1.pf with
  | .inl pf =>
    Fin.foldr (cast pf b1)
      (fun (x : Fin (cast pf b1)) (acc : Bool) =>
        mkFold1 (b2 (cast pf.symm x.1)) (f (cast pf.symm x.1)) acc) acc
  | .inr (.inl pf) =>
    Fin.foldr (cast pf.2 b1).toNat
      (fun (x : Fin (cast pf.2 b1).toNat) (acc : Bool) =>
        mkFold1 (b2 (cast pf.2.symm x.1)) (f (cast pf.2.symm x.1)) acc) acc
  | .inr (.inr pf) =>
    Fin.foldr (cast pf.2.2 b1).val
      (fun (x : Fin (cast pf.2.2 b1).val) (acc : Bool) =>
        mkFold1 (b2 (cast pf.2.2.symm (UScalar.ofNat' x.1)))
          (f (cast pf.2.2.symm (UScalar.ofNat' x.1))) acc) acc

theorem ofMkFold2EqTrueAux {t1 t2 : Type} [h1 : IsNatLike t1] [h2 : IsNatLike t2] (b1 : t1)
  (b2 : t1 → t2) (f : (x : t1) → (y : t2) → Bool) (acc : Bool) :
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
      rw [ih acc', ofMkFold1EqTrueAux (b2 (cast ht.2.symm (BitVec.ofNat ht.1 b')))
        (f (cast ht.2.symm (BitVec.ofNat ht.1 b'))) acc]
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
  (f : (x : t1) → (y : t2) → Bool) : mkFold2 b1 b2 f true → ∀ x < b1, ∀ y < b2 x, f x y := by
  simp only [ofMkFold2EqTrueAux, true_and, imp_self]

end Brute
