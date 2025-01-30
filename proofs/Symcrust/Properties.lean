import Symcrust.Arith
import Symcrust.BarrettReduction
import Symcrust.MontReduction
import Symcrust.SpecAux
import Symcrust.NatBit

import Symcrust.Funs

open Aeneas
open Std
open Result


namespace Aeneas.Std

@[reducible]
def ScalarTy.bitWidth (ty : ScalarTy) : Nat :=
  match ty with
  | Isize | Usize => size_num_bits
  | I8 | U8 => 8
  | I16 | U16 => 16
  | I32 | U32 => 32
  | I64 | U64 => 64
  | I128 | U128 => 128

theorem ScalarTy.unsigned_min_eq_zero (ty : ScalarTy) (h : ¬ty.isSigned) :
  Scalar.min ty = 0 := by
  cases ty <;> simp_all <;> rfl

theorem ScalarTy.unsigned_max_eq_pow_bitWidth (ty : ScalarTy) (h : ¬ty.isSigned) :
  Scalar.max ty = 2 ^ ty.bitWidth - 1 := by
  cases ty <;> simp_all <;> try rfl
  simp [Scalar.max, Usize.max, Usize.refined_max, Usize.smax]

set_option maxRecDepth 1000

open Result

/-- Bit vector representation of a scalar -/
def Scalar.bv {ty} (x : Scalar ty) : BitVec ty.bitWidth :=
  if ty.isSigned then BitVec.ofInt _ x.val else BitVec.ofNat _ x.toNat


@[simp]
theorem Scalar.bv_toNat_eq {ty : ScalarTy} (x : Scalar ty) (h : ¬ ty.isSigned := by simp) :
  (Scalar.bv x).toNat  = x.val := by
  have := x.hmin
  have := x.hmax
  simp [Scalar.bv, h]
  simp [ScalarTy.unsigned_max_eq_pow_bitWidth, ScalarTy.unsigned_min_eq_zero, h] at *
  simp [*]
  have : x.val < 2 ^ ty.bitWidth := by omega
  apply Int.emod_eq_of_lt <;> omega

theorem core.num.Scalar.wrapping_add_bv_unsigned_eq {ty} (x y : Scalar ty) (hs : ¬ ty.isSigned := by simp) :
  (Scalar.wrapping_add x y).bv = x.bv + y.bv := by
  sorry

theorem core.num.Scalar.wrapping_add_val_unsigned_eq {ty} (x y : Scalar ty) (hs : ¬ ty.isSigned := by simp) :
  (Scalar.wrapping_add x y).val = (x.val + y.val) % 2^ty.bitWidth := by
  sorry

@[simp] theorem core.num.U8.wrapping_add_val_eq (x y : U8) :
  (core.num.U8.wrapping_add x y).val = (x.val + y.val) % (U8.max + 1) :=
  core.num.Scalar.wrapping_add_val_unsigned_eq x y

@[simp] theorem core.num.U16.wrapping_add_val_eq (x y : U16) :
  (core.num.U16.wrapping_add x y).val = (x.val + y.val) % (U16.max + 1) :=
  core.num.Scalar.wrapping_add_val_unsigned_eq x y

@[simp] theorem core.num.U32.wrapping_add_val_eq (x y : U32) :
  (core.num.U32.wrapping_add x y).val = (x.val + y.val) % (U32.max + 1) :=
  core.num.Scalar.wrapping_add_val_unsigned_eq x y

@[simp] theorem core.num.U64.wrapping_add_val_eq (x y : U64) :
  (core.num.U64.wrapping_add x y).val = (x.val + y.val) % (U64.max + 1) :=
  core.num.Scalar.wrapping_add_val_unsigned_eq x y

@[simp] theorem core.num.U128.wrapping_add_val_eq (x y : U128) :
  (core.num.U128.wrapping_add x y).val = (x.val + y.val) % (U128.max + 1) :=
  core.num.Scalar.wrapping_add_val_unsigned_eq x y

@[simp] theorem core.num.U8.wrapping_add_bv_eq (x y : U8) :
  (core.num.U8.wrapping_add x y).bv = x.bv + y.bv :=
  core.num.Scalar.wrapping_add_bv_unsigned_eq x y

@[simp] theorem core.num.U16.wrapping_add_bv_eq (x y : U16) :
  (core.num.U16.wrapping_add x y).bv = x.bv + y.bv :=
  core.num.Scalar.wrapping_add_bv_unsigned_eq x y

@[simp] theorem core.num.U32.wrapping_add_bv_eq (x y : U32) :
  (core.num.U32.wrapping_add x y).bv = x.bv + y.bv :=
  core.num.Scalar.wrapping_add_bv_unsigned_eq x y

@[simp] theorem core.num.U64.wrapping_add_bv_eq (x y : U64) :
  (core.num.U64.wrapping_add x y).bv = x.bv + y.bv :=
  core.num.Scalar.wrapping_add_bv_unsigned_eq x y

@[simp] theorem core.num.U128.wrapping_add_bv_eq (x y : U128) :
  (core.num.U128.wrapping_add x y).bv = x.bv + y.bv :=
  core.num.Scalar.wrapping_add_bv_unsigned_eq x y

theorem core.num.Scalar.wrapping_add_toNat_unsigned_eq {ty} (x y : Scalar ty) (hs : ¬ ty.isSigned := by simp) :
  (Scalar.wrapping_add x y).toNat = (x.toNat + y.toNat) % 2^ty.bitWidth := by
  sorry

@[simp] theorem core.num.U8.wrapping_add_toNat_eq (x y : U8) :
  (core.num.U8.wrapping_add x y).toNat = (x.toNat + y.toNat) % (U8.max + 1) :=
  core.num.Scalar.wrapping_add_toNat_unsigned_eq x y

@[simp] theorem core.num.U16.wrapping_add_toNat_eq (x y : U16) :
  (core.num.U16.wrapping_add x y).toNat = (x.toNat + y.toNat) % (U16.max + 1) :=
  core.num.Scalar.wrapping_add_toNat_unsigned_eq x y

@[simp] theorem core.num.U32.wrapping_add_toNat_eq (x y : U32) :
  (core.num.U32.wrapping_add x y).toNat = (x.toNat + y.toNat) % (U32.max + 1) :=
  core.num.Scalar.wrapping_add_toNat_unsigned_eq x y

@[simp] theorem core.num.U64.wrapping_add_toNat_eq (x y : U64) :
  (core.num.U64.wrapping_add x y).toNat = (x.toNat + y.toNat) % (U64.max + 1) :=
  core.num.Scalar.wrapping_add_toNat_unsigned_eq x y

@[simp] theorem core.num.U128.wrapping_add_toNat_eq (x y : U128) :
  (core.num.U128.wrapping_add x y).toNat = (x.toNat + y.toNat) % (U128.max + 1) :=
  core.num.Scalar.wrapping_add_toNat_unsigned_eq x y

theorem core.num.Scalar.wrapping_sub_val_unsigned_eq {ty} (x y : Scalar ty) (hs : ¬ ty.isSigned := by simp) :
  (Scalar.wrapping_sub x y).val = (x.val - y.val) % 2^ty.bitWidth := by
  sorry

@[simp] theorem core.num.U8.wrapping_sub_val_eq (x y : U8) :
  (core.num.U8.wrapping_sub x y).val = (x.val - y.val) % (U8.max + 1) :=
  core.num.Scalar.wrapping_sub_val_unsigned_eq x y

@[simp] theorem core.num.U16.wrapping_sub_val_eq (x y : U16) :
  (core.num.U16.wrapping_sub x y).val = (x.val - y.val) % (U16.max + 1) :=
  core.num.Scalar.wrapping_sub_val_unsigned_eq x y

@[simp] theorem core.num.U32.wrapping_sub_val_eq (x y : U32) :
  (core.num.U32.wrapping_sub x y).val = (x.val - y.val) % (U32.max + 1) :=
  core.num.Scalar.wrapping_sub_val_unsigned_eq x y

@[simp] theorem core.num.U64.wrapping_sub_val_eq (x y : U64) :
  (core.num.U64.wrapping_sub x y).val = (x.val - y.val) % (U64.max + 1) :=
  core.num.Scalar.wrapping_sub_val_unsigned_eq x y

@[simp] theorem core.num.U128.wrapping_sub_val_eq (x y : U128) :
  (core.num.U128.wrapping_sub x y).val = (x.val - y.val) % (U128.max + 1) :=
  core.num.Scalar.wrapping_sub_val_unsigned_eq x y

theorem core.num.Scalar.wrapping_sub_toNat_unsigned_eq {ty} (x y : Scalar ty) (hs : ¬ ty.isSigned := by simp) :
  (Scalar.wrapping_sub x y).toNat = ((x.val - y.val) % 2^ty.bitWidth).toNat := by
  sorry

@[simp] theorem core.num.U8.wrapping_sub_toNat_eq (x y : U8) :
  (core.num.U8.wrapping_sub x y).toNat = ((x.val - y.val) % (U8.max + 1)).toNat :=
  core.num.Scalar.wrapping_sub_toNat_unsigned_eq x y

@[simp] theorem core.num.U16.wrapping_sub_toNat_eq (x y : U16) :
  (core.num.U16.wrapping_sub x y).toNat = ((x.val - y.val) % (U16.max + 1)).toNat :=
  core.num.Scalar.wrapping_sub_toNat_unsigned_eq x y

@[simp] theorem core.num.U32.wrapping_sub_toNat_eq (x y : U32) :
  (core.num.U32.wrapping_sub x y).toNat = ((x.val - y.val) % (U32.max + 1)).toNat :=
  core.num.Scalar.wrapping_sub_toNat_unsigned_eq x y

@[simp] theorem core.num.U64.wrapping_sub_toNat_eq (x y : U64) :
  (core.num.U64.wrapping_sub x y).toNat = ((x.val - y.val) % (U64.max + 1)).toNat :=
  core.num.Scalar.wrapping_sub_toNat_unsigned_eq x y

@[simp] theorem core.num.U128.wrapping_sub_toNat_eq (x y : U128) :
  (core.num.U128.wrapping_sub x y).toNat = ((x.val - y.val) % (U128.max + 1)).toNat :=
  core.num.Scalar.wrapping_sub_toNat_unsigned_eq x y

-- TODO: scalar_tac_simp?
@[simp] theorem Int.mod_toNat_val (n m : Int) (h : m ≠ 0) :
  (n % m).toNat = n % m := by
  simp only [Int.ofNat_toNat, ne_eq, h, not_false_eq_true, Int.emod_nonneg, sup_of_le_left]

@[pspec] theorem core.num.Scalar.ShiftRight_val_unsigned_eq {ty0 ty1} (x : Scalar ty0) (y : Scalar ty1)
  (hs : ¬ ty0.isSigned) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ ty0.bitWidth) :
  ∃ z, x >>> y = ok z ∧
  z.val = x.val >>> y.toNat
  := by
  sorry

@[pspec] theorem core.num.Scalar.ShiftLeft_val_unsigned_eq {ty0 ty1} (x : Scalar ty0) (y : Scalar ty1)
  (hs : ¬ ty0.isSigned) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ ty0.bitWidth) :
  ∃ z, x <<< y = ok z ∧
  z.val = x.val >>> y.toNat
  := by
  sorry

end Aeneas.Std

namespace Symcrust -- TODO: fix namespace issues

def ntt.SymCryptMlKemModAdd' (a : U32) (b : U32) : Result U32 :=
  do
  massert (a < ntt.Q)
  massert (b < ntt.Q)
  let i ← a + b
  let res := core.num.U32.wrapping_sub i ntt.Q
  let i1 ← res >>> 16#i32
  (if i1 = 0#u32 then ok () else massert (i1 = 65535#u32))
  let res1 := core.num.U32.wrapping_add res (ntt.Q &&& i1)
  massert (res1 < ntt.Q)
  Result.ok res1

-- TODO: move
@[simp]
def bind_eq_iff (x : Result α) (y y' : α → Result β) :
  ((Bind.bind x y) = (Bind.bind x y')) ↔
  ∀ v, x = ok v → y v = y' v := by
  dcases x <;> simp_all

@[simp]
def ntt.SymCryptMlKemModAdd_eq (a : U32) (b : U32) :
  SymCryptMlKemModAdd a b = SymCryptMlKemModAdd' a b := by
  unfold SymCryptMlKemModAdd SymCryptMlKemModAdd'
  simp
  intros
  split <;> simp

@[simp]
theorem ntt.Q_eq : Q = 3329#u32 := by
  unfold Q Q_body eval_global
  simp

attribute [local simp] Spec.Q -- TODO: add this to the scalar_tac simp set

-- TODO: move
@[pspec]
theorem massert_spec (b : Bool) (h : b) :
  massert b = ok () := by
  simp [massert, *]

-- TODO: move
@[pspec]
theorem massert_decide_spec (b : Prop) [Decidable b] (h : b) :
  massert (decide b) = ok () := by
  simp [massert, *]

-- TODO: generalize, move
@[simp] theorem core.num.U32.and_val (x y : U32) :
  (x &&& y).val = Int.land x.val y.val := by
  sorry

-- TODO: move
theorem Int.eq_of_testBit_eq {x y : Int}
  (pred : ∀ (i : ℕ), x.testBit i = y.testBit i) : x = y := by
  cases x <;> cases y <;> rename_i x y <;> simp only [Int.testBit] at pred
  . have : x = y := by
      apply Nat.eq_of_testBit_eq
      apply pred
    rw [this]
  . -- Contradiction
    sorry
  . -- Contradiction
    sorry
  . have : x = y := by
      apply Nat.eq_of_testBit_eq
      intro i
      replace pred := pred i
      simp at pred
      apply pred
    rw [this]

@[simp]
theorem Int.testBit_zero (i : Nat) : Int.testBit 0 i = false := by
  unfold Int.testBit; simp

-- TODO: move
@[simp] theorem Int.land_zero_right (x : Int) :
  Int.land x 0 = 0 := by
  apply Int.eq_of_testBit_eq
  intro i
  simp

-- TODO: move
@[simp] theorem Int.land_zero_left (x : Int) :
  Int.land 0 x = 0 := by
  apply Int.eq_of_testBit_eq
  intro i
  simp

@[simp]
theorem Int.testBit_pos_eq_nat_testBit (x i : Nat) :
  (x : Int).testBit i = x.testBit i := by
  unfold Int.testBit; simp

example (x : BitVec 32) (h : x ≤ BitVec.ofInt 32 (2^4)) :
  x >>> 5 = 0 := by
  bv_decide

#eval (BitVec.ofNat 32 (2^32-1)) >>> 31
#eval (BitVec.ofInt 32 (2^32))
#eval (BitVec.ofNat 32 (2^32-1)) &&& 0
#check Int.bmod

example (n m : BitVec 32) (hn : n < BitVec.ofInt 32 (2 ^ 16)) (hm : m < BitVec.ofInt 32 (2 ^ 16)) :
  m &&& ((BitVec.ofNat 32 (2^32 - 1) - n) >>> 16) = m := by
  bv_decide

theorem Int.testBit_two_pow_sub_succ {x : Int} {n : ℕ} (h₁ : 0 ≤ x) (h₂ : x < 2 ^ n) (i : ℕ) :
  (2 ^ n - (x + 1)).testBit i = (i < n && !x.testBit i) := by
  have hx : x = x.toNat := by omega
  have h1 := @Nat.testBit_two_pow_sub_succ x.toNat n (by norm_cast at *; omega) i
  simp at *
  have h2 := Int.testBit_pos_eq_nat_testBit (2 ^ n - (x + 1).toNat) i
  have : (2^n - (x + 1).toNat : Nat) = 2 ^n - (x + 1) := by
    norm_cast at *
    omega
  rw [this] at h2; clear this
  rw [h2]; clear h2

  have : 2 ^ n - (x.toNat + 1) = 2 ^ n - (x + 1).toNat := by
    norm_cast at *
    omega
  rw [this] at h1; clear this
  rw [h1]; clear h1

  have : x.toNat.testBit i = x.testBit i := by
    sorry
  simp [this]

#check Nat.testBit_shiftRight

@[simp] theorem Int.testBit_shiftRight {i j : Nat} (x : Int) :
  (x >>> i).testBit j = x.testBit (i + j) := by
  sorry

@[simp] theorem Int.testBit_int_shiftRight {i : Int} {j : Nat} (x : Int) :
  (x >>> i).testBit j = x.testBit (i.toNat + j) := by
  sorry

/-theorem Int.testBit_shiftLeft {i j : Nat}  (x : Int) :
  (x <<< i).testBit j = (j ≥ i && x.testBit (j - i)) := by sorry-/

#check Nat.testBit_eq_false_of_lt

theorem Int.testBit_pos_eq_false_of_lt {n : Int} {i : ℕ} (h : 0 ≤ n) (h : n < 2 ^ i) :
  n.testBit i = false := by
  sorry

-- TODO: move
theorem ntt.SymCryptMlKemMod_underflow_eq
  (n m : Int) (hn0 : 0 ≤ n) (hn : n < 2 ^ 12) (hm0 : 0 ≤ m) (hm : m < 2 ^ 12):
  Int.land m ((2^32 - 1 - n) >>> (16 : Nat)) = m := by
  apply Int.eq_of_testBit_eq
  intro i
  have h : 2^32 - 1 - n = 2^32 - (n + 1) := by ring_nf
  rw [h]; clear h
  have := @Int.testBit_two_pow_sub_succ n 32 (by omega) (by omega) (16 + i)
  simp [-Int.reducePow]
  rw [this]; clear this
  intro hi
  dcases hi : i < 12
  . simp; split_conjs
    . omega
    . have hi : n < 2^(16 + i) := by
        have := @Int.pow_le_pow_of_le_right 2 (by simp) 12 (16 + i) (by omega)
        norm_cast at *
        omega
      apply @Int.testBit_pos_eq_false_of_lt n (16 + i) (by omega) hi
  . -- Contradiction
    have hi : m < 2^i := by
      have := @Int.pow_le_pow_of_le_right 2 (by simp) 12 i (by omega)
      norm_cast at *
      omega
    have := @Int.testBit_pos_eq_false_of_lt m i (by omega) hi
    simp_all

#check Aeneas.Std.core.num.Scalar.ShiftRight_val_unsigned_eq

theorem ntt.SymCryptMlKemMod'_spec (a : U32) (b : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) :
  ∃ (c : U32), ntt.SymCryptMlKemModAdd' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) + (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemModAdd'
  simp at *
  progress
  progress
  progress as ⟨ c1, hc1 ⟩
  progress as ⟨ c2, hc2 ⟩
  simp at *
  -- TODO: handle this properly with progress
  have hIf : (if c2 = 0#u32 then ok () else massert (c2 = 65535#u32)) = ok () := by
    split <;> simp_all
    sorry
  progress; clear hIf
  --
  progress
  . sorry -- This is the assert
  . simp
    -- There are two cases depending on whether `a + b - q` is `< 0` or not
    dcases hlt : 0 ≤ a.val + b.val - 3329
    . -- No underflow
      let c : Int := a.val + b.val - 3329
      have : 0 ≤ c ∧ c < 3329 := by scalar_tac
      have hcMod : c % (U32.max + 1) = c := by
        apply Int.emod_eq_of_lt <;> scalar_tac
      have hc2Eq : c2.val = 0 := by
        rw [hc2, hc1, hcMod]
        rw [Int.shiftRight_eq_div_pow]
        apply Int.ediv_eq_zero_of_lt <;>
        scalar_tac
      rw [hc2Eq]
      simp [*]
      rw [hcMod]
      simp +zetaDelta [Spec.Zq]
      split_conjs
      . rfl
      . scalar_tac
    . -- Underflow
      simp at hlt
      have hAnd : Int.land 3329 c2.val = 3329 := by
        -- This is the tricky proof
        have hc1Mod :=
          calc
            (c1.val - 3329) % (U32.max + 1) =
              (U32.max + 1 - (3329 - c1.val)) % (U32.max + 1) := by
              have := @Int.add_emod_self_left (U32.max + 1) (c1.val - 3329)
              rw [← this]
              ring_nf
            _ = U32.max + 1 - (3329 - c1.val) := by
              apply Int.emod_eq_of_lt <;> scalar_tac

        rw [hc2, hc1Mod]
        have hEq := ntt.SymCryptMlKemMod_underflow_eq (3329 - c1.val - 1) 3329 (by scalar_tac) (by scalar_tac) (by simp) (by simp)
        ring_nf at hEq
        simp [U32.max]
        ring_nf
        apply hEq
      rw [hAnd]
      simp

      have hMod : c1.val % (U32.max + 1) = c1.val := by
        apply Int.emod_eq_of_lt <;> scalar_tac
      rw [hMod]
      split_conjs
      . simp [*]
      . scalar_tac

end Symcrust
