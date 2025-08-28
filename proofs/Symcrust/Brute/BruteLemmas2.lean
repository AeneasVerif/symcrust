import Lean
import Aeneas

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

------------------------------------------------------------------------------------------------------------------

theorem ofMkFold1SomeLt {t : Type} [h : IsNatLike t] (b : t) (f f' : t → Bool) :
  (∀ x < b, f' x → f x) → mkFold1 (some b) f' true → ∀ x < b, f x := by
  simp only [mkFold1]
  intro hf h' x hx
  exact (ofMkFold1UpperBoundedEqTrue b f f' true hf h').2 x hx

theorem ofMkFold1None {t : Type} [h : IsNatLike t] (f f' : t → Bool) :
  (∀ x : t, f' x → f x) → mkFold1 none f' true → ∀ x : t, f x := by
  sorry

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

theorem ofMkFold1SomeLe {t : Type} [h : IsNatLike t] (b : t) (f f' : t → Bool) :
  (∀ x ≤ b, f' x → f x) → mkFold1 (natLikeSucc b) f' true → ∀ x ≤ b, f x := by
  sorry

theorem ofMkFold1Triv {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (f : t1 → t2 → Bool) (x : t1)
  (b : Option t2) (h : mkFold1 b (f x) true = true) :
  mkFold1 b (fun x_1 => mkFold1 b (f x) true) true = true := by
  rw [h]
  sorry

------------------------------------------------------------------------------------------------------------------

theorem bruteTacticProof2 {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (f : t1 → t2 → Bool) :
  ∀ x : t1, ∀ y : t2, f x y := by
  intro x
  apply ofMkFold1None (f x) (fun _ => (mkFold1 none (f x) true))
  . intro y h
    apply ofMkFold1None (f x) (f x)
    . exact fun y h => h
    . exact h
  . revert x
    apply ofMkFold1None
      (fun x => mkFold1 none (fun _ => mkFold1 none (f x) true) true)
      (fun x' => (mkFold1 none (f x') true))
    . intro x
      exact ofMkFold1Triv f x none
    . sorry -- Can prove via computation

theorem bruteTacticProof2SomeLtLt {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : t1 → t2 → Bool) :
  ∀ x < b1, ∀ y < b2 x, f x y := by
  intro x hx
  apply ofMkFold1SomeLt (b2 x) (f x) (fun _ => (mkFold1 (some (b2 x)) (f x) true))
  . intro y hy h
    apply ofMkFold1SomeLt (b2 x) (f x) (f x)
    . exact fun y hy h => h
    . exact h
    . exact hy
  . revert x hx
    apply ofMkFold1SomeLt b1 _ (fun x' => (mkFold1 (some (b2 x')) (f x') true))
    . intro x hx
      exact ofMkFold1Triv f x (some (b2 x))
    . sorry -- Can prove via computation

theorem bruteTacticProof2SomeLtLe {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : t1 → t2 → Bool) :
  ∀ x < b1, ∀ y ≤ b2 x, f x y := by
  intro x hx
  apply ofMkFold1SomeLe (b2 x) (f x) (fun _ => (mkFold1 (natLikeSucc (b2 x)) (f x) true))
  . intro y hy h
    apply ofMkFold1SomeLe (b2 x) (f x) (f x)
    . exact fun y hy h => h
    . exact h
    . exact hy
  . revert x hx
    apply ofMkFold1SomeLt b1 _ (fun x' => (mkFold1 (natLikeSucc (b2 x')) (f x') true))
    . intro x hx
      exact ofMkFold1Triv f x (natLikeSucc (b2 x))
    . sorry -- Can prove via computation

theorem bruteTacticProof2SomeLeLt {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : t1 → t2 → Bool) :
  ∀ x ≤ b1, ∀ y < b2 x, f x y := by
  intro x hx
  apply ofMkFold1SomeLt (b2 x) (f x) (fun _ => (mkFold1 (some (b2 x)) (f x) true))
  . intro y hy h
    apply ofMkFold1SomeLt (b2 x) (f x) (f x)
    . exact fun y hy h => h
    . exact h
    . exact hy
  . revert x hx
    apply ofMkFold1SomeLe b1 _ (fun x' => (mkFold1 (some (b2 x')) (f x') true))
    . intro x hx
      exact ofMkFold1Triv f x (some (b2 x))
    . sorry -- Can prove via computation

theorem bruteTacticProof2SomeLeLe {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : t1 → t2 → Bool) :
  ∀ x ≤ b1, ∀ y ≤ b2 x, f x y := by
  intro x hx
  apply ofMkFold1SomeLe (b2 x) (f x) (fun _ => (mkFold1 (natLikeSucc (b2 x)) (f x) true))
  . intro y hy h
    apply ofMkFold1SomeLe (b2 x) (f x) (f x)
    . exact fun y hy h => h
    . exact h
    . exact hy
  . revert x hx
    apply ofMkFold1SomeLe b1 _ (fun x' => (mkFold1 (natLikeSucc (b2 x')) (f x') true))
    . intro x hx
      exact ofMkFold1Triv f x (natLikeSucc (b2 x))
    . sorry -- Can prove via computation

theorem bruteTacticProof3 {t1 t2 t3 : Type} [IsNatLike t1] [IsNatLike t2] [IsNatLike t3] (f : t1 → t2 → t3 → Bool) :
  ∀ x : t1, ∀ y : t2, ∀ z : t3, f x y z := by
  intro x y
  apply ofMkFold1None (f x y) (fun _ => (mkFold1 none (f x y) true))
  . intro z h
    apply ofMkFold1None (f x y) (f x y)
    . exact fun y h => h
    . exact h
  . revert y
    apply ofMkFold1None
      (fun y' => mkFold1 none (fun _ => mkFold1 none (f x y') true) true)
      (fun y' => mkFold1 none (f x y') true)
    . intro y
      exact ofMkFold1Triv (f x) y none
    . revert x
      apply ofMkFold1None _ (fun x' => mkFold1 none (fun y' => mkFold1 none (f x' y') true) true)
      . intro x h
        rw [h]
      . sorry -- Can prove via computation

theorem bruteTacticProof4 {t1 t2 t3 t4 : Type} [IsNatLike t1] [IsNatLike t2] [IsNatLike t3] [IsNatLike t4]
  (f : t1 → t2 → t3 → t4 → Bool) :
  ∀ x : t1, ∀ y : t2, ∀ z : t3, ∀ a : t4, f x y z a := by
  intro x y z
  apply ofMkFold1None (f x y z) (fun _ => (mkFold1 none (f x y _) true))
  . intro a h
    apply ofMkFold1None (f x y z) (f x y z)
    . exact fun a h => h
    . exact h
  . revert z
    apply ofMkFold1None _ (fun z' => mkFold1 none (f x y z') true)
    . intro z
      exact ofMkFold1Triv (f x y) z none
    . revert y
      apply ofMkFold1None _ (fun y' => mkFold1 none (fun z' => mkFold1 none (f x y' z') true) true)
      . intro y h
        rw [h]
      . revert x
        apply ofMkFold1None _
          (fun x' => mkFold1 none (fun y' => mkFold1 none (fun z' => mkFold1 none (f x' y' z') true) true) true)
        . intro x h
          rw [h]
        . sorry -- Can prove via computation

theorem bruteTacticProof5 {t1 t2 t3 t4 t5 : Type}
  [IsNatLike t1] [IsNatLike t2] [IsNatLike t3] [IsNatLike t4] [IsNatLike t5]
  (f : t1 → t2 → t3 → t4 → t5 → Bool) :
  ∀ x : t1, ∀ y : t2, ∀ z : t3, ∀ a : t4, ∀ b : t5, f x y z a b := by
  intro x y z a
  apply ofMkFold1None (f x y z a) (fun _ => (mkFold1 none (f x y z _) true))
  . intro b h
    apply ofMkFold1None (f x y z a) (f x y z a)
    . exact fun b h => h
    . exact h
  . revert a
    apply ofMkFold1None _ (fun a' => mkFold1 none (f x y z a') true)
    . intro a
      exact ofMkFold1Triv (f x y z) a none
    . revert z
      apply ofMkFold1None _ (fun z' => mkFold1 none (fun a' => mkFold1 none (f x y z' a') true) true)
      . intro z h
        rw [h]
      . revert y
        apply ofMkFold1None _
          (fun y' => mkFold1 none (fun z' => mkFold1 none (fun a' => mkFold1 none (f x y' z' a') true) true) true)
        . intro y h
          rw [h]
        . revert x
          apply ofMkFold1None _
            (fun x' => mkFold1 none
              (fun y' =>
                mkFold1 none (fun z' => mkFold1 none (fun a' => mkFold1 none (f x' y' z' a') true) true) true) true)
          . intro x h
            rw [h]
          . sorry -- Can prove via computation

theorem bruteTermProof1 {t1 : Type} [IsNatLike t1] (f : t1 → Bool) :
  ∀ x : t1, f x :=
  fun x =>
    ofMkFold1None
      f
      f
      (fun x hf => hf)
      sorry
      x

theorem bruteTermProof1SomeLt {t1 : Type} [IsNatLike t1] (b : t1) (f : t1 → Bool) :
  ∀ x < b, f x :=
  fun x hx =>
    ofMkFold1SomeLt
      b
      f
      f
      (fun x hx hf => hf)
      sorry
      x hx

theorem bruteTermProof2SomeLtNone {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (b1 : t1) (f : t1 → t2 → Bool) :
  ∀ x < b1, ∀ y : t2, f x y :=
  fun x hx =>
    ofMkFold1None
      (f x)
      (fun x_1 => mkFold1 none (f x) true)
      (fun y h => ofMkFold1None (f x) (f x) (fun y' hf => hf) h y)
      (ofMkFold1SomeLt
        b1
        (fun x' => mkFold1 none (fun x_1 => mkFold1 none (f x') true) true)
        (fun x' => mkFold1 none (f x') true)
        (fun x' hx' => ofMkFold1Triv f x' none)
        (by sorry)
        x hx
      )

theorem bruteTermProof2NoneSomeLt {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (b2 : t1 → t2) (f : t1 → t2 → Bool) :
  ∀ x : t1, ∀ y < b2 x, f x y :=
  fun x =>
    ofMkFold1SomeLt
      (b2 x)
      (f x)
      (fun x_1 => mkFold1 (some (b2 x)) (f x) true)
      (fun y hy h => ofMkFold1SomeLt (b2 x) (f x) (f x) (fun y' _ hf => hf) h y hy)
      (ofMkFold1None
        (fun x' => mkFold1 (some (b2 x')) (fun x_1 => mkFold1 (some (b2 x')) (f x') true) true)
        (fun x' => mkFold1 (some (b2 x')) (f x') true)
        (fun x' => ofMkFold1Triv f x' (some (b2 x')))
        (by sorry)
        x
      )

theorem bruteTermProof2SomeLtLt {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : t1 → t2 → Bool) :
  ∀ x < b1, ∀ y < b2 x, f x y :=
  fun x hx =>
    ofMkFold1SomeLt
      (b2 x)
      (f x)
      (fun x_1 => mkFold1 (some (b2 x)) (f x) true)
      (fun y hy h => ofMkFold1SomeLt (b2 x) (f x) (f x) (fun y' _ hf => hf) h y hy)
      (ofMkFold1SomeLt
        b1
        (fun x' => mkFold1 (some (b2 x')) (fun x_1 => mkFold1 (some (b2 x')) (f x') true) true)
        (fun x' => mkFold1 (some (b2 x')) (f x') true)
        (fun x' hx' => ofMkFold1Triv f x' (some (b2 x')))
        (by sorry)
        x hx
      )

theorem bruteTermProof2SomeLtLe {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : t1 → t2 → Bool) :
  ∀ x < b1, ∀ y ≤ b2 x, f x y :=
  fun x hx =>
    ofMkFold1SomeLe
      (b2 x)
      (f x)
      (fun x_1 => mkFold1 (natLikeSucc (b2 x)) (f x) true)
      (fun y hy h => ofMkFold1SomeLe (b2 x) (f x) (f x) (fun y' _ hf => hf) h y hy)
      (ofMkFold1SomeLt
        b1
        (fun x' =>
          mkFold1 (natLikeSucc (b2 x')) (fun x_1 => mkFold1 (natLikeSucc (b2 x')) (f x') true) true)
        (fun x' => mkFold1 (natLikeSucc (b2 x')) (f x') true)
        (fun x' hx' => ofMkFold1Triv f x' (natLikeSucc (b2 x')))
        sorry
        x hx
      )

theorem bruteTermProof2SomeLeLe {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (b1 : t1) (b2 : t1 → t2)
  (f : t1 → t2 → Bool) :
  ∀ x ≤ b1, ∀ y ≤ b2 x, f x y :=
  fun x hx =>
    ofMkFold1SomeLe
      (b2 x)
      (f x)
      (fun x_1 => mkFold1 (natLikeSucc (b2 x)) (f x) true)
      (fun y hy h => ofMkFold1SomeLe (b2 x) (f x) (f x) (fun y hy h => h) h y hy)
      (ofMkFold1SomeLe
        b1
        (fun x =>
          mkFold1 (natLikeSucc (b2 x)) (fun x_1 => mkFold1 (natLikeSucc (b2 x)) (f x) true) true)
        (fun x' => mkFold1 (natLikeSucc (b2 x')) (f x') true)
        (fun x hx => ofMkFold1Triv f x (natLikeSucc (b2 x)))
        sorry
        x hx
      )

theorem bruteTermProof2NoneNone {t1 t2 : Type} [IsNatLike t1] [IsNatLike t2] (f : t1 → t2 → Bool) :
  ∀ x : t1, ∀ y : t2, f x y :=
  fun x =>
    ofMkFold1None
      (f x)
      (fun x_1 => mkFold1 none (f x) true)
      (fun y h => ofMkFold1None (f x) (f x) (fun y' hf => hf) h y)
      (ofMkFold1None
        (fun x' => mkFold1 (none : Option t2) (fun x_1 => mkFold1 (none : Option t2) (f x') true) true)
        (fun x' => mkFold1 (none : Option t2) (f x') true)
        (fun x' => ofMkFold1Triv f x' none)
        sorry -- Proof by computation
        x
      )

#print bruteTermProof2NoneNone

theorem bruteTermProof3NoneNoneNone {t1 t2 t3 : Type} [IsNatLike t1] [IsNatLike t2] [IsNatLike t3]
  (f : t1 → t2 → t3 → Bool) :
  ∀ x : t1, ∀ y : t2, ∀ z : t3, f x y z :=
  fun x y =>
    ofMkFold1None
      (f x y)
      (fun x_1 => mkFold1 none (f x y) true)
      (fun z h => ofMkFold1None (f x y) (f x y) (fun z' h => h) h z)
      (ofMkFold1None
        (fun y' => mkFold1 none (fun x_1 => mkFold1 none (f x y') true) true)
        (fun y' => mkFold1 none (f x y') true)
        (fun y' => ofMkFold1Triv (f x) y' none)
        (ofMkFold1None
          (fun x => mkFold1 none (fun y' => mkFold1 none (f x y') true) true)
          (fun x' => mkFold1 none (fun y' => mkFold1 none (f x' y') true) true)
          (fun _ h => Eq.mpr (id (congrArg (fun _a => _a = true) h)) (Eq.refl true))
          (by sorry) -- Proof by computation
          x
        )
        y
      )

theorem bruteTermProof4 {t1 t2 t3 t4 : Type} [IsNatLike t1] [IsNatLike t2] [IsNatLike t3] [IsNatLike t4]
  (f : t1 → t2 → t3 → t4 → Bool) : ∀ x : t1, ∀ y : t2, ∀ z : t3, ∀ a : t4, f x y z a :=
  fun x y z =>
    ofMkFold1None
      (f x y z)
      (fun x_1 => mkFold1 none (f x y z) true)
      (fun a h => ofMkFold1None (f x y z) (f x y z) (fun a h => h) h a)
      (ofMkFold1None
        (fun z' => mkFold1 none (fun x_2 => mkFold1 none (f x y z') true) true)
        (fun z' => mkFold1 none (f x y z') true)
        (fun z' => ofMkFold1Triv (f x y) z' none)
        (ofMkFold1None
          (fun x_1 => mkFold1 none (fun z' => mkFold1 none (f x x_1 z') true) true)
          (fun y' => mkFold1 none (fun z' => mkFold1 none (f x y' z') true) true)
          (fun _ h => Eq.mpr (id (congrArg (fun _a => _a = true) h)) (Eq.refl true))
          (ofMkFold1None
            (fun x =>
              mkFold1 none (fun y' => mkFold1 none (fun z' => mkFold1 none (f x y' z') true) true) true)
            (fun x' =>
              mkFold1 none (fun y' => mkFold1 none (fun z' => mkFold1 none (f x' y' z') true) true) true)
            (fun _ h => Eq.mpr (id (congrArg (fun _a => _a = true) h)) (Eq.refl true))
            sorry -- Proof by computation
            x
          )
          y
        )
        z
      )

theorem bruteTermProof5 {t1 t2 t3 t4 t5 : Type}
  [IsNatLike t1] [IsNatLike t2] [IsNatLike t3] [IsNatLike t4] [IsNatLike t5]
  (f : t1 → t2 → t3 → t4 → t5 → Bool) :
  ∀ x : t1, ∀ y : t2, ∀ z : t3, ∀ a : t4, ∀ b : t5, f x y z a b :=
  fun x y z a =>
    ofMkFold1None
      (f x y z a)
      (fun x_1 => mkFold1 none (f x y z a) true)
      (fun b h => ofMkFold1None (f x y z a) (f x y z a) (fun b h => h) h b)
      (ofMkFold1None
        (fun x_1 => mkFold1 none (fun x_2 => mkFold1 none (f x y z x_1) true) true)
        (fun a' => mkFold1 none (f x y z a') true)
        (fun a' => ofMkFold1Triv (f x y z) a' none)
        (ofMkFold1None
          (fun x_1 => mkFold1 none (fun a' => mkFold1 none (f x y x_1 a') true) true)
          (fun z' => mkFold1 none (fun a' => mkFold1 none (f x y z' a') true) true)
          (fun z h => Eq.mpr (id (congrArg (fun _a => _a = true) h)) (Eq.refl true))
          (ofMkFold1None
            (fun x_1 =>
              mkFold1 none
                (fun z' => mkFold1 none (fun a' => mkFold1 none (f x x_1 z' a') true) true) true)
            (fun y' =>
              mkFold1 none
                (fun z' => mkFold1 none (fun a' => mkFold1 none (f x y' z' a') true) true) true)
            (fun y h => Eq.mpr (id (congrArg (fun _a => _a = true) h)) (Eq.refl true))
            (ofMkFold1None
              (fun x =>
                mkFold1 none
                  (fun y' =>
                    mkFold1 none
                      (fun z' => mkFold1 none (fun a' => mkFold1 none (f x y' z' a') true) true)
                      true)
                  true)
              (fun x' =>
                mkFold1 none
                  (fun y' =>
                    mkFold1 none
                      (fun z' => mkFold1 none (fun a' => mkFold1 none (f x' y' z' a') true) true)
                      true)
                  true)
              (fun x h => Eq.mpr (id (congrArg (fun _a => _a = true) h)) (Eq.refl true))
              sorry
              x
            )
            y
          )
          z
        )
        a
      )

end Brute
