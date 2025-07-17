import Lean
import Aeneas

-- This file defines `brute`, a terminal tactic for brute force enumeration. It doesn't make sense to leave
-- this file here in the long term, but I am putting it here for now to make it easy to test on SymCrust proofs

open Lean Meta Parser Elab Tactic Aeneas Aeneas.Std

initialize registerTraceClass `brute.debug

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

def mkFold1 {t : Type} [h : IsNatLike t] (b : t) (f : (x : t) → (hx : x < b) → Bool) (acc : Bool) : Bool :=
  match h' : h.pf with
  | .inl pf =>
    Fin.foldr (cast pf b)
      (fun (x : Fin (cast pf b)) (acc : Bool) => acc && f (cast pf.symm x.1)
        (by rw [LT.lt, instLTOfIsNatLike, h']; simp)) acc
  | .inr (.inl pf) =>
    Fin.foldr (cast pf.2 b).toNat
      (fun (x : Fin (cast pf.2 b).toNat) (acc : Bool) => acc && f (cast pf.2.symm x.1)
        (by
          rw [BitVec.natCast_eq_ofNat, LT.lt, instLTOfIsNatLike, h']
          simp only [gt_iff_lt, cast_cast, cast_eq]
          exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.2
        )
      ) acc
  | .inr (.inr pf) =>
    Fin.foldr (cast pf.2.2 b).val
      (fun (x : Fin (cast pf.2.2 b).val) (acc : Bool) => acc && f
        (cast pf.2.2.symm (UScalar.ofNat x.1
          (by
            rw [UScalar.cMax_eq_pow_cNumBits, UScalarTy.cNumBits]
            . have hb : (cast pf.2.2 b).val ≤ UScalar.max pf.1 := by
                rw [UScalar.val, UScalar.max]
                apply Nat.le_of_lt_succ
                simp only [ne_eq, UScalar.bv_toNat, Nat.succ_eq_add_one, Nat.ofNat_pos,
                  SimpScalar.one_le_pow, Nat.sub_add_cancel]
                apply BitVec.toNat_lt_twoPow_of_le
                rfl
              rw [UScalar.max] at hb
              omega
            . exact pf.2.1
          )
        ))
        (by rw [LT.lt, instLTOfIsNatLike, h']; simp)
      ) acc

/-
theorem ofMkFold1BitVecEqTrueAux (b n : Nat) (hbn : b < 2 ^ n)
  (f : (x : BitVec n) → (hx : x < b) → Bool) (acc : Bool) :
  mkFold1BitVec b n hbn f acc = (acc ∧ ∀ x : BitVec n, ∀ hx : x < b, f x hx) := by
  simp only [mkFold1BitVec, BitVec.natCast_eq_ofNat]
  induction b generalizing acc
  . simp
  . next b ih =>
    simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last, eq_iff_iff]
    let f' : (x : BitVec n) → x < ↑b → Bool := fun x hx => f x $ by
      revert hx
      simp only [BitVec.natCast_eq_ofNat, BitVec.lt_def, BitVec.toNat_ofNat, Nat.cast_add,
        Nat.cast_one, BitVec.ofNat_eq_ofNat, BitVec.toNat_add, Nat.add_mod_mod, Nat.mod_add_mod]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have : BitVec.ofNat n b < ↑(b + 1) := by
      simp only [Nat.cast_add, BitVec.natCast_eq_ofNat, Nat.cast_one, BitVec.ofNat_eq_ofNat,
        BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.add_mod_mod, Nat.mod_add_mod]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hbn, Nat.lt_succ]
    rw [ih (by omega) f' (acc && f (BitVec.ofNat n b) this)]
    constructor
    . simp only [Bool.and_eq_true, and_assoc, and_imp]
      intro h1 h2 h3
      simp only [h1, true_and]
      intro x hx
      dcases hxb : x.toNat = b
      . have : x = (BitVec.ofNat n b) := by
          apply BitVec.eq_of_toNat_eq
          rw [hxb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [this, h2]
      . apply h3
        revert hx
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.lt_def,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
    . simp only [Bool.and_eq_true, and_assoc, and_imp]
      intro h1 h2
      simp only [h1, h2 (BitVec.ofNat n b) this, true_and]
      intro x hx
      apply h2

theorem ofMkFold1BitVecEqTrue (b n : Nat) (hbn : b < 2 ^ n)
  (f : (x : BitVec n) → (hx : x < b) → Bool) :
  mkFold1BitVec b n hbn f true → ∀ x : BitVec n, ∀ hx : x < b, f x hx := by
  simp only [ofMkFold1BitVecEqTrueAux, BitVec.natCast_eq_ofNat, true_and, imp_self]

theorem ofMkFold1EqTrueAux (b : Nat) (f : (x : Nat) → (hx : x < b) → Bool) (acc : Bool) :
  mkFold1 b f acc = (acc ∧ ∀ x : Nat, ∀ hx : x < b, f x hx) := by
  simp only [mkFold1, eq_iff_iff]
  induction b generalizing acc
  . simp
  . next b ih =>
    let f' : (x : ℕ) → x < b → Bool := fun x hx => f x (by omega)
    simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
    rw [ih f' (acc && f b (by omega))]
    constructor
    . simp only [and_imp]
      intro h1 h2
      simp only [Bool.and_eq_true] at h1
      constructor
      . exact h1.1
      . intro x hx
        by_cases hxb : x = b
        . simp only [hxb, h1.2]
        . exact h2 x (by omega)
    . rintro ⟨h1, h2⟩
      simp only [Bool.and_eq_true, and_assoc]
      split_conjs
      . exact h1
      . exact h2 b (by omega)
      . intro x hx
        exact h2 x (by omega)

theorem ofMkFold1EqTrue (b : Nat) (f : (x : Nat) → (hx : x < b) → Bool) :
  mkFold1 b f true → ∀ x : Nat, ∀ hx : x < b, f x hx := by
  simp only [ofMkFold1EqTrueAux, true_and, imp_self]
-/

set_option pp.proofs false in
theorem ofMkFold1EqTrueAux {t : Type} [h : IsNatLike t] (b : t) (f : (x : t) → (hx : x < b) → Bool)
  (acc : Bool) : mkFold1 b f acc = (acc ∧ ∀ x : t, ∀ hx : x < b, f x hx) := by
  unfold mkFold1
  split
  . next ht hpf =>
    simp only [eq_iff_iff]
    -- Automation note: `olet hb' : b' := cast ht b` fails here because `generalize` fails
    rcases (Exists.intro (cast ht b) rfl : ∃ b' : Nat, b' = cast ht b) with ⟨b', hb'⟩
    simp only [← hb', Fin.coe_cast]
    have : ∃ f' : (x : Nat) → x < b' → Bool,
      ∀ x : t, ∀ hx : x < b, f x hx = f' (cast ht x)
        (by
          rw [LT.lt, instLTOfIsNatLike, hpf] at hx
          simp only [gt_iff_lt, ← hb'] at hx
          exact hx) := by
      apply Exists.intro $
        fun x hx => f (cast ht.symm x)
          (by
            rw [LT.lt, instLTOfIsNatLike , hpf]
            simp only [gt_iff_lt, cast_cast, cast_eq]
            omega
          )
      simp
    rcases this with ⟨f', hf'⟩
    simp only [hf', cast_cast, cast_eq]
    clear hf' f
    induction b' generalizing acc
    . simp only [Fin.foldr_zero, iff_self_and]
      intro h1 x hx
      rw [LT.lt, instLTOfIsNatLike, hpf] at hx
      simp only [gt_iff_lt, ← hb', not_lt_zero'] at hx
    . next b' ih =>
      let f'' : (x : ℕ) → x < b' → Bool := fun x hx => f' x (by omega)
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      -- The sorry in the below specialize call isn't provable because of how the induction interacts
      -- with `hb'`
      specialize ih (acc && f' b' (by omega)) (by sorry) f''
      sorry
  . sorry
  . sorry

theorem ofMkFold1EqTrue {t : Type} [h : IsNatLike t] (b : t) (f : (x : t) → (hx : x < b) → Bool) :
  mkFold1 b f true → ∀ x : t, ∀ hx : x < b, f x hx := by
  simp only [ofMkFold1EqTrueAux, true_and, imp_self]

/-
def mkFold2 (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Bool)
  (acc : Bool) : Bool :=
  Fin.foldr b1 (fun (x : Fin b1) (acc : Bool) => mkFold1 (b2 x.1 x.2) (f x.1 x.2) acc) acc

theorem ofMkFold2EqTrueAux (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Bool) (acc : Bool) :
  mkFold2 b1 b2 f acc = (acc ∧ ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx, f x hx y hy) := by
  simp only [mkFold2, eq_iff_iff]
  induction b1 generalizing acc
  . simp
  . next b1 ih1 =>
    simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
    tlet acc' := mkFold1 (b2 b1 (by omega)) (f b1 (by omega)) acc
    let b2' := fun (x : Nat) (hx : x < b1) => b2 x (by omega)
    let f' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2' x hx) => f x (by omega) y hy
    rw [ih1 b2' f' acc', ofMkFold1EqTrueAux (b2 b1 (by omega)) (f b1 (by omega)) acc]
    constructor
    . rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [h1, true_and]
      intro x hx y hy
      rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with x_lt_b1 | x_eq_b1
      . exact h3 x x_lt_b1 y hy
      . simp only [x_eq_b1]
        simp only [x_eq_b1] at hy
        exact h2 y hy
    . rintro ⟨h1, h2⟩
      constructor
      . simp only [h1, true_and]
        intro y hy
        exact h2 b1 (by omega) y hy
      . intro x hx y hy
        exact h2 x _ y hy

theorem ofMkFold2EqTrue (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Bool) :
  mkFold2 b1 b2 f true → ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx, f x hx y hy := by
  simp only [ofMkFold2EqTrueAux, true_and, imp_self]

def mkFold3 (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Bool)
  (acc : Bool) : Bool :=
  Fin.foldr b1 (fun (x : Fin b1) (acc : Bool) => mkFold2 (b2 x.1 x.2) (b3 x.1 x.2) (f x.1 x.2) acc) acc

theorem ofMkFold3EqTrueAux (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Bool)
  (acc : Bool) : mkFold3 b1 b2 b3 f acc = (acc ∧ ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx,
    ∀ z : Nat, ∀ hz : z < b3 x hx y hy, f x hx y hy z hz) := by
  simp only [mkFold3, eq_iff_iff]
  induction b1 generalizing acc
  . simp
  . next b1 ih1 =>
    simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
    tlet acc' := mkFold2 (b2 b1 (by omega)) (b3 b1 (by omega)) (f b1 (by omega)) acc
    let b3' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2 x (by omega)) => b3 x (by omega) y hy
    let b2' := fun (x : Nat) (hx : x < b1) => b2 x (by omega)
    let f' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2' x hx) => f x (by omega) y hy
    rw [ih1 b2' b3' f' acc', ofMkFold2EqTrueAux (b2 b1 (by omega)) (b3 b1 (by omega)) (f b1 (by omega)) acc]
    constructor
    . rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [h1, true_and]
      intro x hx y hy
      rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with x_lt_b1 | x_eq_b1
      . exact h3 x x_lt_b1 y hy
      . simp only [x_eq_b1]
        simp only [x_eq_b1] at hy
        exact h2 y hy
    . rintro ⟨h1, h2⟩
      constructor
      . simp only [h1, true_and]
        intro y hy
        exact h2 b1 (by omega) y hy
      . intro x hx y hy
        exact h2 x _ y hy

theorem ofMkFold3EqTrue (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Bool) :
  mkFold3 b1 b2 b3 f true → ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx,
    ∀ z : Nat, ∀ hz : z < b3 x hx y hy, f x hx y hy z hz := by
  simp only [ofMkFold3EqTrueAux, true_and, imp_self]

def mkFold4 (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (b4 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) →
    (a : Nat) → (ha : a < b4 x hx y hy z hz) → Bool)
  (acc : Bool) : Bool :=
  Fin.foldr b1 (fun (x : Fin b1) (acc : Bool) => mkFold3 (b2 x.1 x.2) (b3 x.1 x.2) (b4 x.1 x.2) (f x.1 x.2) acc) acc

theorem ofMkFold4EqTrueAux (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (b4 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) →
    (a : Nat) → (ha : a < b4 x hx y hy z hz) → Bool)
  (acc : Bool) : mkFold4 b1 b2 b3 b4 f acc = (acc ∧ ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx,
    ∀ z : Nat, ∀ hz : z < b3 x hx y hy, ∀ a : Nat, ∀ ha : a < b4 x hx y hy z hz, f x hx y hy z hz a ha) := by
  simp only [mkFold4, eq_iff_iff]
  induction b1 generalizing acc
  . simp
  . next b1 ih1 =>
    simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
    tlet acc' := mkFold3 (b2 b1 (by omega)) (b3 b1 (by omega)) (b4 b1 (by omega)) (f b1 (by omega)) acc
    let b4' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2 x (by omega)) (z : Nat)
      (hz : z < b3 x (by omega) y (by omega)) => b4 x (by omega) y hy z hz
    let b3' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2 x (by omega)) => b3 x (by omega) y hy
    let b2' := fun (x : Nat) (hx : x < b1) => b2 x (by omega)
    let f' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2' x hx) => f x (by omega) y hy
    rw [ih1 b2' b3' b4' f' acc',
      ofMkFold3EqTrueAux (b2 b1 (by omega)) (b3 b1 (by omega)) (b4 b1 (by omega)) (f b1 (by omega)) acc]
    constructor
    . rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [h1, true_and]
      intro x hx y hy
      rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with x_lt_b1 | x_eq_b1
      . exact h3 x x_lt_b1 y hy
      . simp only [x_eq_b1]
        simp only [x_eq_b1] at hy
        exact h2 y hy
    . rintro ⟨h1, h2⟩
      constructor
      . simp only [h1, true_and]
        intro y hy
        exact h2 b1 (by omega) y hy
      . intro x hx y hy
        exact h2 x _ y hy

theorem ofMkFold4EqTrue (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (b4 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) →
    (a : Nat) → (ha : a < b4 x hx y hy z hz) → Bool) :
  mkFold4 b1 b2 b3 b4 f true → ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx,
    ∀ z : Nat, ∀ hz : z < b3 x hx y hy, ∀ a : Nat, ∀ ha : a < b4 x hx y hy z hz, f x hx y hy z hz a ha := by
  simp only [ofMkFold4EqTrueAux, true_and, imp_self]

def mkFold5 (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (b4 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Nat)
  (b5 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) →
    (a : Nat) → (ha : a < b4 x hx y hy z hz) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) →
    (a : Nat) → (ha : a < b4 x hx y hy z hz) → (b : Nat) → (hb : b < b5 x hx y hy z hz a ha) → Bool)
  (acc : Bool) : Bool :=
  Fin.foldr b1 (fun (x : Fin b1) (acc : Bool) =>
    mkFold4 (b2 x.1 x.2) (b3 x.1 x.2) (b4 x.1 x.2) (b5 x.1 x.2) (f x.1 x.2) acc) acc

theorem ofMkFold5EqTrueAux (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (b4 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Nat)
  (b5 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) →
    (a : Nat) → (ha : a < b4 x hx y hy z hz) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) →
    (a : Nat) → (ha : a < b4 x hx y hy z hz) → (b : Nat) → (hb : b < b5 x hx y hy z hz a ha) → Bool)
  (acc : Bool) : mkFold5 b1 b2 b3 b4 b5 f acc = (acc ∧ ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx,
    ∀ z : Nat, ∀ hz : z < b3 x hx y hy, ∀ a : Nat, ∀ ha : a < b4 x hx y hy z hz, ∀ b : Nat,
    ∀ hb : b < b5 x hx y hy z hz a ha, f x hx y hy z hz a ha b hb) := by
  simp only [mkFold5, eq_iff_iff]
  induction b1 generalizing acc
  . simp
  . next b1 ih1 =>
    simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
    tlet acc' := mkFold4 (b2 b1 (by omega)) (b3 b1 (by omega)) (b4 b1 (by omega)) (b5 b1 (by omega)) (f b1 (by omega)) acc
    let b5' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2 x (by omega)) (z : Nat)
      (hz : z < b3 x (by omega) y (by omega)) (a : Nat) (ha : a < b4 x (by omega) y (by omega) z (by omega)) =>
      b5 x (by omega) y hy z hz a ha
    let b4' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2 x (by omega)) (z : Nat)
      (hz : z < b3 x (by omega) y (by omega)) => b4 x (by omega) y hy z hz
    let b3' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2 x (by omega)) => b3 x (by omega) y hy
    let b2' := fun (x : Nat) (hx : x < b1) => b2 x (by omega)
    let f' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2' x hx) => f x (by omega) y hy
    rw [ih1 b2' b3' b4' b5' f' acc',
      ofMkFold4EqTrueAux (b2 b1 (by omega)) (b3 b1 (by omega)) (b4 b1 (by omega)) (b5 b1 (by omega)) (f b1 (by omega)) acc]
    constructor
    . rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [h1, true_and]
      intro x hx y hy
      rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with x_lt_b1 | x_eq_b1
      . exact h3 x x_lt_b1 y hy
      . simp only [x_eq_b1]
        simp only [x_eq_b1] at hy
        exact h2 y hy
    . rintro ⟨h1, h2⟩
      constructor
      . simp only [h1, true_and]
        intro y hy
        exact h2 b1 (by omega) y hy
      . intro x hx y hy
        exact h2 x _ y hy

theorem ofMkFold5EqTrue (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (b4 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Nat)
  (b5 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) →
    (a : Nat) → (ha : a < b4 x hx y hy z hz) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) →
    (a : Nat) → (ha : a < b4 x hx y hy z hz) → (b : Nat) → (hb : b < b5 x hx y hy z hz a ha) → Bool) :
  mkFold5 b1 b2 b3 b4 b5 f true → ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx, ∀ z : Nat,
    ∀ hz : z < b3 x hx y hy, ∀ a : Nat, ∀ ha : a < b4 x hx y hy z hz, ∀ b : Nat,
    ∀ hb : b < b5 x hx y hy z hz a ha, f x hx y hy z hz a ha b hb := by
  simp only [ofMkFold5EqTrueAux, true_and, imp_self]
-/

/-- A terminal tactic that attempts to prove goals of the form `∀ x y z ..., f x y z ...` via brute force.
    Currently, `brute` only supports goals consisting of a string of universally quantified upper-bounded Nats
    (e.g. `∀ a < x₁, ∀ b < x₂ ...`) followed by a decidable function `f : Nat → ... → Nat → Bool`

    Currently, we only support goals with at most five bounded Nats. -/
syntax (name := brute) "brute" : tactic

/-- A structure that holds info for binders of the form `∀ x < b, ...`-/
structure BinderInfo where
  x : FVarId -- The universally quantified variable
  b : Expr -- The value that the variable is upper bounded by
  hxb : FVarId -- The variable whose type is `x < b`
  isNatLikeInst : Expr -- An Expr whose type is `IsNatLike t` where `x : t` and `b : t`

instance : ToMessageData BinderInfo where
  toMessageData := fun ⟨x, b, hxb, isNatLikeInst⟩ => m!"({Expr.fvar x}, {b}, {Expr.fvar hxb}, {isNatLikeInst})"

/-- A helper definition to make it easier to construct the type of `IsNatLike`'s β type -/
def IsNatLikeβType (t : Type) :=
  PSum
    (PSigma (fun n : Nat => t = BitVec n))
    (PSigma (fun t' : UScalarTy => t' ≠ UScalarTy.Usize ∧ t = UScalar t'))

/-- A helper definition to make it easier to construct the type of `IsNatLike`'s ββ type -/
def IsNatLikeββType (t : Type) := PSigma (fun t' : UScalarTy => t' ≠ UScalarTy.Usize ∧ t = UScalar t')

/-- If `t` is an Expr corresponding to `Nat`, `BitVec n`, or `UScalar t'`, then `getIsNatLike` returns
    an Expr whose type is `IsNatLike t`. Otherwise, `getIsNatLike` returns `none`. -/
def getIsNatLikeInstance (t : Expr) : MetaM (Option Expr) := do
  match t with
  | .const ``Nat _ =>
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    let pSumβ ← mkAppM ``IsNatLikeβType #[t]
    let pSumPf ← mkAppOptM ``PSum.inl #[none, some pSumβ, rflPf]
    let inst ← mkAppM ``IsNatLike.mk #[pSumPf]
    return some inst
  | .app (.const ``BitVec _) n =>
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    let pSigmaβBody :=
      mkApp3 (mkConst ``Eq [2]) (.sort 1) (.app (.const ``BitVec []) n) (.app (.const ``BitVec []) (.bvar 0))
    let pSigmaβ := Expr.lam `n (mkConst ``Nat) pSigmaβBody .default
    let pSigmaPf ← mkAppOptM ``PSigma.mk #[none, some pSigmaβ, n, rflPf]
    let pInnerSumβ ← mkAppM ``IsNatLikeββType #[t]
    let pInnserSumPf ← mkAppOptM ``PSum.inl #[none, some pInnerSumβ, pSigmaPf]
    let pSumα ← mkAppM ``Eq #[t, mkConst ``Nat]
    let pSumPf ← mkAppOptM ``PSum.inr #[some pSumα, none, pInnserSumPf]
    let inst ← mkAppM ``IsNatLike.mk #[pSumPf]
    return some inst
  | _ => return none -- **TODO** UScalar support

/-- If `b1` has a NatLike type and `b2 : b1 < d` then returns a `BinderInfo` corresponding to
    `b1`, `b1`'s Natlike type, and `b2`. Otherwise returns `none` -/
def popBoundBinders (b1 b2 : FVarId) : TacticM (Option BinderInfo) := do
  let lctx ← getLCtx
  let some b1LocalDecl := lctx.find? b1
    | throwError "{decl_name%} :: Unable to find type of goal binder {Expr.fvar b1}"
  let some b2LocalDecl := lctx.find? b2
    | throwError "{decl_name%} :: Unable to find type of goal binder {Expr.fvar b2}"
  let b1Type := b1LocalDecl.type
  let b2Type := b2LocalDecl.type
  let some isNatLikeInst ← getIsNatLikeInstance b1Type
    | return none -- Don't pop any binders if `b1`
  let b1UpperBound ←
    match b2Type with
    | .app (.app (.app (.app (.const ``LT.lt _) _) _) x) y =>
      if x != Expr.fvar b1 then return none
      else pure y
    | _ => return none
  return some ⟨b1, b1UpperBound, b2, isNatLikeInst⟩

/-- Recursively calls `popBoundBinders` as many times as `goalBinders` allows -/
def popAllBoundBinders (goalBinders : Array FVarId) (acc : Array BinderInfo) : TacticM (Array BinderInfo) := do
  match goalBinders with
  | ⟨b1 :: b2 :: restBinders⟩ =>
    let some binderInfo ← popBoundBinders b1 b2
      | return acc
    popAllBoundBinders ⟨restBinders⟩ $ acc.push binderInfo
  | _ => return acc

@[tactic brute]
def evalBrute : Tactic
| `(tactic| brute) => withMainContext do
  let pf ← forallTelescope (← getMainTarget).consumeMData (cleanupAnnotations := true) $ fun xs g => do
    trace[brute.debug] "xs: {xs}, g: {g}"
    let boundBinders ← popAllBoundBinders (xs.map Expr.fvarId!) #[]
    match boundBinders with
    | #[⟨x, b, hxb, isNatLikeInst⟩] =>
      let boundFVars := #[.fvar x, .fvar hxb]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppOptM ``mkFold1 #[none, some isNatLikeInst, b, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let foldResPf := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      let pf ← mkAppOptM ``ofMkFold1EqTrue #[none, some isNatLikeInst, b, f, foldResPf]
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
      /-
      match xType with
      | .Nat =>
        let boundFVars := #[.fvar x, .fvar hxb]
        let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
        trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
        let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
        trace[brute.debug] "f: {f}"
        let res ← mkAppM ``mkFold1 #[b, f, mkConst ``true]
        trace[brute.debug] "res: {res}"

        let levels := (collectLevelParams {} res).params.toList
        let auxDeclName ← Term.mkAuxName `_brute
        let decl := Declaration.defnDecl $
          mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
        addAndCompile decl

        let rflPrf ← mkEqRefl (toExpr true)
        let levelParams := levels.map .param
        let pf := mkApp3 (mkConst ``ofMkFold1EqTrue) b f <|
          mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
        mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
      | .BitVec n =>
        let boundFVars := #[.fvar x, .fvar hxb]
        let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
        trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
        let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
        trace[brute.debug] "f: {f}"
        let res ← mkAppM ``mkFold1BitVec' #[n, b, f, mkConst ``true]
        trace[brute.debug] "res: {res}"

        let levels := (collectLevelParams {} res).params.toList
        let auxDeclName ← Term.mkAuxName `_brute
        let decl := Declaration.defnDecl $
          mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
        addAndCompile decl

        let rflPrf ← mkEqRefl (toExpr true)
        let levelParams := levels.map .param
        -- `n = 32` is temporarily hard coded for testing purposes
        let pf := mkApp4 (mkConst ``ofMkFold1BitVec'EqTrue) n b f <|
          mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
        mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
      | _ => throwError "Only Nat support is implemented currently"
    -/
    /- **TODO** Uncomment these cases to reason about more than one universal binder
    | #[(x, hx, xBound), (y, hy, yBound)] =>
      let boundFVars := #[.fvar x, .fvar hx, .fvar y, .fvar hy]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let yBound ← mkLambdaFVars #[Expr.fvar x, Expr.fvar hx] yBound
      let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppM ``mkFold2 #[xBound, yBound, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let pf := mkApp4 (mkConst ``ofMkFold2EqTrue) xBound yBound f <|
        mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | #[(x, hx, xBound), (y, hy, yBound), (z, hz, zBound)] =>
      let boundFVars := #[.fvar x, .fvar hx, .fvar y, .fvar hy, .fvar z, .fvar hz]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let yBound ← mkLambdaFVars #[.fvar x, .fvar hx] yBound
      let zBound ← mkLambdaFVars #[.fvar x, .fvar hx, .fvar y, .fvar hy] zBound
      let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppM ``mkFold3 #[xBound, yBound, zBound, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let pf := mkApp5 (mkConst ``ofMkFold3EqTrue) xBound yBound zBound f <|
        mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | #[(x, hx, xBound), (y, hy, yBound), (z, hz, zBound), (a, ha, aBound)] =>
      let boundFVars := #[.fvar x, .fvar hx, .fvar y, .fvar hy, .fvar z, .fvar hz, .fvar a, .fvar ha]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let yBound ← mkLambdaFVars #[.fvar x, .fvar hx] yBound
      let zBound ← mkLambdaFVars #[.fvar x, .fvar hx, .fvar y, .fvar hy] zBound
      let aBound ← mkLambdaFVars #[.fvar x, .fvar hx, .fvar y, .fvar hy, .fvar z, .fvar hz] aBound
      let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppM ``mkFold4 #[xBound, yBound, zBound, aBound, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let pf := mkApp6 (mkConst ``ofMkFold4EqTrue) xBound yBound zBound aBound f <|
        mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | #[(x, hx, xBound), (y, hy, yBound), (z, hz, zBound), (a, ha, aBound), (b, hb, bBound)] =>
      let boundFVars := #[.fvar x, .fvar hx, .fvar y, .fvar hy, .fvar z, .fvar hz, .fvar a, .fvar ha, .fvar b, .fvar hb]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let yBound ← mkLambdaFVars #[.fvar x, .fvar hx] yBound
      let zBound ← mkLambdaFVars #[.fvar x, .fvar hx, .fvar y, .fvar hy] zBound
      let aBound ← mkLambdaFVars #[.fvar x, .fvar hx, .fvar y, .fvar hy, .fvar z, .fvar hz] aBound
      let bBound ← mkLambdaFVars #[.fvar x, .fvar hx, .fvar y, .fvar hy, .fvar z, .fvar hz, .fvar a, .fvar ha] bBound
      let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppM ``mkFold5 #[xBound, yBound, zBound, aBound, bBound, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let pf := mkApp7 (mkConst ``ofMkFold5EqTrue) xBound yBound zBound aBound bBound f <|
        mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    -/
    | _ => throwError "Not yet implemented (boundBinders: {boundBinders})"
  trace[brute.debug] "pf: {pf}"
  trace[brute.debug] "pf type: {← inferType pf}"
  let g ← getMainGoal
  g.assign pf
| _ => throwUnsupportedSyntax

-- Both of these work with minimal delay and no stack overflow
example : ∀ n : Nat, n < 2^15 → n >>> 15 = 0 := by
  brute

example : ∀ n : Nat, n < 2^20 → n >>> 20 = 0 := by
  brute

example : ∀ n < 5, ∀ m < 6, n * m ≤ 20 := by
  brute

example : ∀ x < 5, ∀ y < x, ∀ z < x + y, x + y + z ≤ 100 := by
  brute

example : ∀ f : Fin 3 → Bool, ∀ x < 3, f x ∨ ¬f x := by
  decide +native

-- Note that the comment even explicitly says this instance can be slow for larger bit vectors
#check BitVec.instDecidableForallBitVec

set_option trace.profiler true in
theorem test : ∀ x : BitVec 32, x < 2^20 → x = x := by
  brute

set_option trace.profiler true in
theorem test2 : ∀ x : ℕ, x < 16 → x = x := by
  brute

set_option trace.profiler true in
theorem test3 : ∀ x < 2^20, x = x := by
  brute

end Brute

-- 21 -> 1.5 s
-- 22 -> 3 s
-- 23 -> 6 s
