import Lean
import Aeneas

/-  This file contains various types and definitions used by `brute`. The important ones are:
    - `IsNatLike`: A typeclass which defines the set of types that `brute` supports. Currently,
      it is possible to build `IsNatLike t` instances for the types `Nat`, `BitVec n` and
      `UScalar t'` where `t' ≠ UScalarTy.Usize`.
    - `mkFold1`: The primary function that `brute` uses to build the computation verifying
      the correctness of `brute`'s given goal. Depending on whether the first explicit argument
      passed to `mkFold1` is `none`, it either evaluates to `mkFold1UpperBounded` or
      `mkFold1NoUpperBound`.
    - `natLikeSucc`: A function that takes in a NatLike value `b` and either returns `none` if it
      is the maximal value of its type (e.g. `15#4 ↦ none`), or `some (b + 1)` if there is a
      value of the same type as `b` which is one greater than `b`. This function is used to
      obtain an exclusive upper (e.g. `< 5`) from an inclusive upper bound (e.g. `≤ 4`).
    - `ofMkFold1None`/`ofMkFold1SomeLt`/`ofMkFold1SomeLe`: The lemmas that `brute` uses
      to derive `brute`'s given goal from a successful evaluation of the `mkFold1` calls.
    - `ofMkFold1Triv`: This is a lemma used by `brute` on goals with two or more NatLike
      universal quantifiers. The easiest way to understand how this lemma is used is to
      look at examples in BruteProofExamples.lean. -/

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

instance (t : Type) [h : IsNatLike t] : LE t where
  le :=
    match h.pf with
    | .isNatPf pf => fun x y => cast pf x ≤ cast pf y
    | .isBitVecPf pf => fun x y => cast pf.2 x ≤ cast pf.2 y
    | .isUScalarPf pf => fun x y => cast pf.2.2 x ≤ cast pf.2.2 y

instance (t : Type) [h : IsNatLike t] : Inhabited t where
  default :=
    match h.pf with
    | .isNatPf pf => cast pf.symm 0
    | .isBitVecPf pf => cast pf.2.symm 0
    | .isUScalarPf pf => cast pf.2.2.symm (UScalar.ofNat 0 (Nat.zero_le _))

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

def mkFold1UpperBounded {t : Type} [h : IsNatLike t] (b : t) (f : t → Bool) (acc : Bool) : Bool :=
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

def mkFold1NoUpperBound {t : Type} [h : IsNatLike t] (f : t → Bool) (acc : Bool) : Bool :=
  match h.pf with
  | .isNatPf _ => false -- Cannot fold over all Nats without an upper bound
  | .isBitVecPf pf => -- Use `2 ^ {size of the bitvector}` as an upper bound
    Fin.foldr (2 ^ pf.1)
      (fun (x : Fin (2 ^ pf.1)) (acc : Bool) => acc && f (cast pf.2.symm x.1)) acc
  | .isUScalarPf pf => -- Use `2 ^ {number of bits in the UScalar}` as an upper bound
    Fin.foldr (2 ^ pf.1.numBits)
      (fun (x : Fin (2 ^ pf.1.numBits)) (acc : Bool) => acc && f
        (cast pf.2.2.symm (UScalar.ofNat' x.1))) acc

def mkFold1 {t : Type} [h : IsNatLike t] (bOpt : Option t) (f : t → Bool) (acc : Bool) : Bool :=
  match bOpt with
  | some b => mkFold1UpperBounded b f acc
  | none => mkFold1NoUpperBound f acc

theorem ofMkFold1UpperBoundedEqTrue {t : Type} [h : IsNatLike t] (b : t) (f f' : t → Bool)
  (acc : Bool) : (∀ x < b, f' x → f x) → mkFold1UpperBounded b f' acc → (acc ∧ ∀ x < b, f x) := by
  unfold mkFold1UpperBounded
  split
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [gt_iff_lt, eq_iff_iff]
    induction (cast ht b) generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      intro h hb'
      let h' : ∀ (x : t), cast ht x < b' → f' x = true → f x = true := by
        intro x hx hf
        exact h x (by omega) hf
      specialize ih (acc && f' (cast ht.symm b')) h' hb'
      simp only [Bool.and_eq_true, and_assoc] at ih
      simp only [ih, true_and]
      intro x hx
      rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hx
      rcases hx with hx | hx
      . exact ih.2.2 x hx
      . apply h
        . omega
        . simp only [← ih.2.1, ← hx, cast_cast, cast_eq]
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [BitVec.natCast_eq_ofNat, gt_iff_lt, eq_iff_iff]
    rw [LT.lt, instLTBitVec]
    simp only [gt_iff_lt]
    induction (cast ht.2 b).toNat generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      intro h hb'
      let h' : ∀ (x : t), (cast ht.2 x).toNat < b' → f' x = true → f x = true := by
        intro x hx hf
        exact h x (by omega) hf
      specialize ih (acc && f' (@cast (BitVec ht.fst) t ht.2.symm (BitVec.ofNat ht.fst b'))) h' hb'
      simp only [Bool.and_eq_true, and_assoc] at ih
      simp only [ih, true_and]
      intro x hx
      rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hx
      rcases hx with hx | hx
      . exact ih.2.2 x hx
      . apply h
        . omega
        . simp only [← ih.2.1, ← hx, BitVec.ofNat_toNat, BitVec.setWidth_eq, cast_cast, cast_eq]
  . next ht hpf =>
    rw [LT.lt, instLTOfIsNatLike, hpf]
    simp only [BitVec.natCast_eq_ofNat, gt_iff_lt, eq_iff_iff]
    rw [LT.lt, instLTUScalar]
    simp only [gt_iff_lt]
    induction (cast ht.2.2 b).val generalizing acc
    . simp
    . next b' ih =>
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
      intro h hb'
      let h' : ∀ (x : t), (cast ht.2.2 x).val < b' → f' x = true → f x = true := by
        intro x hx hf
        exact h x (by omega) hf
      specialize ih (acc && f' (@cast (UScalar ht.fst) t ht.2.2.symm (UScalar.ofNat' b'))) h' hb'
      simp only [Bool.and_eq_true, and_assoc] at ih
      simp only [ih, true_and]
      intro x hx
      rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hx
      rcases hx with hx | hx
      . exact ih.2.2 x hx
      . apply h
        . omega
        . simp only [← ih.2.1, ne_eq, ← hx, UScalar.ofNat'_val_eq ht.2.1, cast_cast, cast_eq]

theorem ofMkFold1SomeLt {t : Type} [h : IsNatLike t] (b : t) (f f' : t → Bool) :
  (∀ x < b, f' x → f x) → mkFold1 (some b) f' true → ∀ x < b, f x := by
  simp only [mkFold1]
  intro hf h' x hx
  exact (ofMkFold1UpperBoundedEqTrue b f f' true hf h').2 x hx

theorem ofMkFold1NoneEqTrue {t : Type} [h : IsNatLike t] (f f' : t → Bool)
  (acc : Bool) : (∀ x : t, f' x → f x) → mkFold1NoUpperBound f' acc → (acc ∧ ∀ x : t, f x) := by
  unfold mkFold1NoUpperBound
  split
  . simp
  . next ht hpf =>
    simp only [BitVec.natCast_eq_ofNat]
    intro hf
    conv => intro h; rhs; intro x; rw [← true_implies (f x = true), ← eq_true (BitVec.isLt (cast ht.snd x))]
    induction 2^ht.1 generalizing acc
    . simp
    . next b ih =>
      intro h
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last] at h
      specialize ih (acc && f' (cast ht.2.symm (BitVec.ofNat ht.fst b))) h
      simp only [Bool.and_eq_true, and_assoc] at ih
      simp only [ih, true_and]
      intro x hx
      rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hx
      rcases hx with hx | hx
      . exact ih.2.2 x hx
      . simp only [← hx, BitVec.ofNat_toNat, BitVec.setWidth_eq, cast_cast, cast_eq] at ih
        exact hf x ih.2.1
  . next ht hpf =>
    simp only [ne_eq]
    intro hf
    conv => intro h; rhs; intro x; rw [← true_implies (f x = true), ← eq_true (UScalar.hmax (cast ht.snd.right x))]
    induction 2^ht.1.numBits generalizing acc
    . simp
    . next b ih =>
      intro h
      simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last] at h
      specialize ih (acc && f' (cast ht.2.2.symm (UScalar.ofNat' b))) h
      simp only [ne_eq, Bool.and_eq_true, and_assoc] at ih
      simp only [ih, ne_eq, true_and]
      intro x hx
      rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hx
      rcases hx with hx | hx
      . exact ih.2.2 x hx
      . simp only [UScalar.ofNat', ← hx] at ih
        conv at ih =>
          arg 2; arg 1; arg 1; arg 1; arg 2; arg 1
          rw [Nat.mod_eq_of_lt (by
            simp only [UScalar.cMax]
            split
            . next heq =>
              exfalso
              exact ht.2.1 heq
            . rw [Nat.lt_succ_iff]
              exact UScalar.hrBounds (cast ht.snd.right x)
          )]
        simp only [UScalar.ofNat_val, cast_cast, cast_eq] at ih
        exact hf x ih.2.1

theorem ofMkFold1None {t : Type} [h : IsNatLike t] (f f' : t → Bool) :
  (∀ x : t, f' x → f x) → mkFold1 none f' true → ∀ x : t, f x := by
  simp only [mkFold1]
  intro hf h' x
  exact (ofMkFold1NoneEqTrue f f' true hf h').2 x

/-- Examines `b` and checks whether it can be incremented by 1. If it can, `some (b + 1)`
    is returned. Otherwise, `none` is returned. -/
def natLikeSucc {t : Type} [h : IsNatLike t] (b : t) : Option t :=
  match h.pf with
  | .isNatPf pf => some $ cast pf.symm $ (cast pf b) + 1
  | .isBitVecPf pf =>
    if (cast pf.2 b).toNat == 2 ^ pf.1 - 1 then none
    else some $ cast pf.2.symm $ (cast pf.2 b) + 1
  | .isUScalarPf pf =>
    if h : cast pf.2.2 b == UScalar.max pf.1 then none
    else
      let sum := (cast pf.2.2 b).val + (@UScalar.ofNat pf.1 1 (by cases pf.1 <;> decide)).val
      some $ cast pf.2.2.symm $ UScalar.mk sum

lemma le_iff_lt_natLikeSucc_some {t : Type} [ht : IsNatLike t] {x b b' : t} (hb : natLikeSucc b = some b') : x ≤ b ↔ x < b' := by
  rw [LE.le, LT.lt, instLEOfIsNatLike, instLTOfIsNatLike]
  unfold natLikeSucc at hb
  rcases heq : @IsNatLike.pf t ht with ht | ht | ht
  . simp only [ge_iff_le, gt_iff_lt]
    simp only [heq, Option.some.injEq] at hb
    rw [← hb]
    simp only [cast_cast, cast_eq]
    omega
  . simp only [ge_iff_le, gt_iff_lt]
    simp only [heq, beq_iff_eq, BitVec.ofNat_eq_ofNat, Option.ite_none_left_eq_some, Option.some.injEq] at hb
    rw [← hb.2, LT.lt, instLTBitVec, LE.le, instLEBitVec]
    simp only [heq, BitVec.lt_def, gt_iff_lt, cast_cast, cast_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat, Nat.add_mod_mod]
    rw [Nat.mod_eq_of_lt] <;> omega
  . simp only [ne_eq, UScalar.le_equiv, ge_iff_le, UScalar.lt_equiv, gt_iff_lt]
    simp only [heq, ne_eq, beq_iff_eq, UScalar.ofNat_val_eq, Nat.cast_add, BitVec.natCast_eq_ofNat,
      Bvify.UScalar.BitVec_ofNat_setWidth, BitVec.setWidth_eq, Nat.cast_one, BitVec.ofNat_eq_ofNat,
      dite_eq_ite, Option.ite_none_left_eq_some, Option.some.injEq, UScalar.max] at hb
    rw [← hb.2]
    simp only [heq, ne_eq, UScalar.lt_equiv, gt_iff_lt, cast_cast, cast_eq]
    rw [BitVec.add_def]
    simp only [UScalar.bv_toNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    . conv => rhs; rhs; rw [UScalar.val, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt]
      . omega
      . have : (cast ht.2.2 b).val < 2^ht.1.numBits := UScalar.hmax (cast ht.snd.right b)
        omega
    . cases heq : ht.1 <;> try decide -- `decide` covers all cases except `UScalarTy.Usize`
      exfalso
      exact ht.2.1 heq

lemma le_iff_lt_natLikeSucc_none {t : Type} [ht : IsNatLike t] {x b : t} (hb : natLikeSucc b = none) : x ≤ b := by
  rw [LE.le, instLEOfIsNatLike]
  unfold natLikeSucc at hb
  rcases heq : @IsNatLike.pf t ht with ht | ht | ht
  . simp [heq] at hb
  . simp only [ge_iff_le]
    simp only [heq, beq_iff_eq, BitVec.ofNat_eq_ofNat, ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not] at hb
    rw [BitVec.le_def, hb, Nat.le_iff_lt_add_one]
    simp only [Nat.ofNat_pos, SimpScalar.one_le_pow, Nat.sub_add_cancel]
    exact BitVec.isLt (cast (instLTOfIsNatLike._proof_1 t ht) x)
  . simp only [ne_eq, UScalar.le_equiv, ge_iff_le]
    simp only [heq, ne_eq, beq_iff_eq, UScalar.ofNat_val_eq, Nat.cast_add, BitVec.natCast_eq_ofNat,
      Bvify.UScalar.BitVec_ofNat_setWidth, BitVec.setWidth_eq, Nat.cast_one, BitVec.ofNat_eq_ofNat,
      dite_eq_ite, ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not] at hb
    rw [hb]
    exact ScalarTac.UScalar.bounds (cast (instLTOfIsNatLike._proof_2 t ht) x)

theorem ofMkFold1SomeLe {t : Type} [ht : IsNatLike t] (b : t) (f f' : t → Bool) :
  (∀ x ≤ b, f' x → f x) → mkFold1 (natLikeSucc b) f' true → ∀ x ≤ b, f x := by
  unfold mkFold1
  split
  . next b' hb =>
    intro hf h x hx
    have : ∀ x < b', f' x = true → f x = true := by
      intro x hx h
      rw [← le_iff_lt_natLikeSucc_some hb] at hx
      exact hf x hx h
    rw [le_iff_lt_natLikeSucc_some hb] at hx
    exact (ofMkFold1UpperBoundedEqTrue b' f f' true this h).2 x hx
  . next hb =>
    intro hf h x hx
    simp only [eq_true (le_iff_lt_natLikeSucc_none hb), forall_const] at hf
    exact (ofMkFold1NoneEqTrue f f' true hf h).2 x

theorem ofMkFold1Triv {t1 t2 : Type} [IsNatLike t1] [h2 : IsNatLike t2] (f : t1 → t2 → Bool) (x : t1)
  (b : Option t2) (h : mkFold1 b (f x) true = true) :
  mkFold1 b (fun _ => mkFold1 b (f x) true) true = true := by
  rw [h]
  simp only [mkFold1, mkFold1UpperBounded, Bool.and_true, ne_eq, mkFold1NoUpperBound]
  split
  . next b' =>
    rcases @IsNatLike.pf t2 h2 with h2 | h2 | h2
    . simp only
      induction (cast h2 b')
      . simp
      . next b' ih =>
        simp [Fin.foldr_succ_last, ih]
    . simp only
      induction (cast h2.2 b').toNat
      . simp
      . next b' ih =>
        simp [Fin.foldr_succ_last, ih]
    . simp only
      induction (cast h2.2.2 b').val
      . simp
      . next b' ih =>
        simp [Fin.foldr_succ_last, ih]
  . rcases heq : @IsNatLike.pf t2 h2 with h2 | h2 | h2
    . simp [mkFold1, mkFold1NoUpperBound, heq] at h
    . simp only
      induction 2 ^ h2.1
      . simp
      . next b' ih =>
        simp [Fin.foldr_succ_last, ih]
    . simp only
      induction 2 ^ h2.1.numBits
      . simp
      . next b' ih =>
        simp [Fin.foldr_succ_last, ih]

end Brute
