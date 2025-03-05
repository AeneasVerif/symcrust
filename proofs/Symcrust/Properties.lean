import Symcrust.BarrettReduction
import Symcrust.MontReduction
import Symcrust.SpecAux
import Symcrust.NatBit

import Symcrust.Funs

open Aeneas
open Std
open Result


namespace Aeneas.Std


/-
theorem ScalarTy.unsigned_min_eq_zero (ty : ScalarTy) (h : ¬ty.isSigned) :
  Scalar.min ty = 0 := by
  cases ty <;> simp_all <;> rfl

theorem ScalarTy.unsigned_max_eq_pow_bitWidth (ty : ScalarTy) (h : ¬ty.isSigned) :
  Scalar.max ty = 2 ^ ty.bitWidth - 1 := by
  cases ty <;> simp_all <;> try rfl
  simp [Scalar.max, Usize.max, Usize.refined_max, Usize.smax]
-/

--set_option maxRecDepth 1000
set_option maxHeartbeats 500000

open Result

/-
/-- Bit vector representation of a scalar -/
def Scalar.bv_ {ty} (x : Scalar ty) : BitVec ty.bitWidth :=
  if ty.isSigned then BitVec.ofInt _ x.val else BitVec.ofNat _ x.toNat

@[simp] theorem Scalar.bv_U8 (x : U8) : Scalar.bv_ x = x.toNat := by rfl
@[simp] theorem Scalar.bv_U16 (x : U16) : Scalar.bv_ x = x.toNat := by rfl
@[simp] theorem Scalar.bv_U32 (x : U32) : Scalar.bv_ x = x.toNat := by rfl
@[simp] theorem Scalar.bv_U64 (x : U64) : Scalar.bv_ x = x.toNat := by rfl
@[simp] theorem Scalar.bv_U128 (x : U128) : Scalar.bv_ x = x.toNat := by rfl
@[simp] theorem Scalar.bv_Usize (x : Usize) : Scalar.bv_ x = x.toNat := by rfl
@[simp] theorem Scalar.bv_I8 (x : I8) : Scalar.bv_ x = x.val := by rfl
@[simp] theorem Scalar.bv_I16 (x : I16) : Scalar.bv_ x = x.val := by rfl
@[simp] theorem Scalar.bv_I32 (x : I32) : Scalar.bv_ x = x.val := by rfl
@[simp] theorem Scalar.bv_I64 (x : I64) : Scalar.bv_ x = x.val := by rfl
@[simp] theorem Scalar.bv_I128 (x : I128) : Scalar.bv_ x = x.val := by rfl
@[simp] theorem Scalar.bv_Isize (x : Isize) : Scalar.bv_ x = x.val := by rfl
-/

/-
@[simp]
theorem Scalar.bv_toNat_eq {ty : ScalarTy} (x : Scalar ty) (h : ¬ ty.isSigned := by simp) :
  (Scalar.bv_ x).toNat  = x.toNat := by
  have := x.hmin
  have := x.hmax
  simp [Scalar.bv_, h]
  simp [ScalarTy.unsigned_max_eq_pow_bitWidth, ScalarTy.unsigned_min_eq_zero, h] at *
  have h := (System.Platform.getNumBits ()).property
  dcases ty <;> simp_all <;> (try omega) <;>
  dcases h <;> simp_all <;> omega

@[simp] theorem U8.bv_toNat_eq (x : U8) : x.bv.toNat = x.toNat := by apply Scalar.bv_toNat_eq; simp
@[simp] theorem U16.bv_toNat_eq (x : U16) : x.bv.toNat = x.toNat := by apply Scalar.bv_toNat_eq; simp
@[simp] theorem U32.bv_toNat_eq (x : U32) : x.bv.toNat = x.toNat := by apply Scalar.bv_toNat_eq; simp
@[simp] theorem U64.bv_toNat_eq (x : U64) : x.bv.toNat = x.toNat := by apply Scalar.bv_toNat_eq; simp
@[simp] theorem U128.bv_toNat_eq (x : U128) : x.bv.toNat = x.toNat := by apply Scalar.bv_toNat_eq; simp
-/

/-
theorem core.num.Scalar.wrapping_add_bv_unsigned_eq {ty} (x y : Scalar ty) (hs : ¬ ty.isSigned := by simp) :
  (Scalar.wrapping_add x y).bv_ = x.bv_ + y.bv_ := by
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

theorem core.num.Scalar.wrapping_sub_bv_unsigned_eq {ty} (x y : Scalar ty) (hs : ¬ ty.isSigned := by simp) :
  (Scalar.wrapping_sub x y).bv_ = x.bv_ - y.bv_ := by
  sorry

@[simp] theorem core.num.U8.wrapping_sub_bv_eq (x y : U8) :
  (core.num.U8.wrapping_sub x y).bv = x.bv - y.bv :=
  core.num.Scalar.wrapping_sub_bv_unsigned_eq x y

@[simp] theorem core.num.U16.wrapping_sub_bv_eq (x y : U16) :
  (core.num.U16.wrapping_sub x y).bv = x.bv - y.bv :=
  core.num.Scalar.wrapping_sub_bv_unsigned_eq x y

@[simp] theorem core.num.U32.wrapping_sub_bv_eq (x y : U32) :
  (core.num.U32.wrapping_sub x y).bv = x.bv - y.bv :=
  core.num.Scalar.wrapping_sub_bv_unsigned_eq x y

@[simp] theorem core.num.U64.wrapping_sub_bv_eq (x y : U64) :
  (core.num.U64.wrapping_sub x y).bv = x.bv - y.bv :=
  core.num.Scalar.wrapping_sub_bv_unsigned_eq x y

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
-/

/- TODO: scalar_tac_simp?
@[simp] theorem Int.mod_toNat_val (n m : Int) (h : m ≠ 0) :
  (n % m).toNat = n % m := by
  simp only [Int.ofNat_toNat, ne_eq, h, not_false_eq_true, Int.emod_nonneg, sup_of_le_left]-/

/-theorem core.num.Scalar.ShiftRight_val_unsigned_eq {ty0 ty1} (x : Scalar ty0) (y : Scalar ty1)
  (hs : ¬ ty0.isSigned) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ ty0.bitWidth) :
  ∃ z, x >>> y = ok z ∧
  z.val = x.val >>> y.toNat
  := by
  sorry

theorem core.num.Scalar.ShiftRight_bv_unsigned_eq {ty0 ty1} (x : Scalar ty0) (y : Scalar ty1)
  (hs : ¬ ty0.isSigned) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ ty0.bitWidth) :
  ∃ z, x >>> y = ok z ∧ z.bv_ = x.bv_ >>> y.toNat
  := by
  sorry

@[pspec] theorem U8.ShiftRight_bv_unsigned_eq (x : U8) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 8) :
  ∃ (z : U8), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply core.num.Scalar.ShiftRight_bv_unsigned_eq <;> simp [*]

@[pspec] theorem U16.ShiftRight_bv_unsigned_eq (x : U16) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 16) :
  ∃ (z : U16), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply core.num.Scalar.ShiftRight_bv_unsigned_eq <;> simp [*]

@[pspec] theorem U32.ShiftRight_bv_unsigned_eq (x : U32) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 32) :
  ∃ (z : U32), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply core.num.Scalar.ShiftRight_bv_unsigned_eq <;> simp [*]

@[pspec] theorem U64.ShiftRight_bv_unsigned_eq (x : U64) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 64) :
  ∃ (z : U64), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply core.num.Scalar.ShiftRight_bv_unsigned_eq <;> simp [*]

@[pspec] theorem U128.ShiftRight_bv_unsigned_eq (x : U128) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 128) :
  ∃ (z : U128), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply core.num.Scalar.ShiftRight_bv_unsigned_eq <;> simp [*]

@[pspec] theorem Usize.ShiftRight_bv_unsigned_eq (x : Usize) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ size_num_bits) :
  ∃ (z : Usize), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply core.num.Scalar.ShiftRight_bv_unsigned_eq <;> simp_all

theorem core.num.Scalar.ShiftLeft_val_unsigned_eq {ty0 ty1} (x : Scalar ty0) (y : Scalar ty1)
  (hs : ¬ ty0.isSigned) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ ty0.bitWidth) :
  ∃ z, x <<< y = ok z ∧ z.val = x.val <<< y.val -- TODO: can't use y.toNat?
  := by
  sorry

theorem core.num.Scalar.ShiftLeft_bv_unsigned_eq {ty0 ty1} (x : Scalar ty0) (y : Scalar ty1)
  (hs : ¬ ty0.isSigned) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ ty0.bitWidth) :
  ∃ z, x <<< y = ok z ∧ z.bv_ = x.bv_ <<< y.toNat
  := by
  sorry

@[pspec] theorem U8.ShiftLeft_bv_unsigned_eq (x : U8) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 8) :
  ∃ (z : U8), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply core.num.Scalar.ShiftLeft_bv_unsigned_eq <;> simp [*]

@[pspec] theorem U16.ShiftLeft_bv_unsigned_eq (x : U16) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 16) :
  ∃ (z : U16), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply core.num.Scalar.ShiftLeft_bv_unsigned_eq <;> simp [*]

@[pspec] theorem U32.ShiftLeft_bv_unsigned_eq (x : U32) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 32) :
  ∃ (z : U32), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply core.num.Scalar.ShiftLeft_bv_unsigned_eq <;> simp [*]

@[pspec] theorem U64.ShiftLeft_bv_unsigned_eq (x : U64) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 64) :
  ∃ (z : U64), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply core.num.Scalar.ShiftLeft_bv_unsigned_eq <;> simp [*]

@[pspec] theorem U128.ShiftLeft_bv_unsigned_eq (x : U128) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ 128) :
  ∃ (z : U128), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply core.num.Scalar.ShiftLeft_bv_unsigned_eq <;> simp [*]

@[pspec] theorem Usize.ShiftLeft_bv_unsigned_eq (x : Usize) (y : Scalar ty1) (hy0 : 0 ≤ y.val) (hy1 : y.val ≤ size_num_bits) :
  ∃ (z : Usize), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply core.num.Scalar.ShiftLeft_bv_unsigned_eq <;> simp_all-/

end Aeneas.Std

namespace Symcrust

open Aeneas.Arith
set_option maxHeartbeats 500000

/-!
Addition modulo
-/
def ntt.SymCryptMlKemModAdd' (a : U32) (b : U32) : Result U32 :=
  do
  massert (a < ntt.Q)
  massert (b < ntt.Q)
  let i ← a + b
  let (res : U32) ← ↑(core.num.U32.wrapping_sub i ntt.Q)
  let i1 ← res >>> 16#i32
  (if i1 = 0#u32 then ok () else massert (i1 = 65535#u32))
  let (i2 : U32) ← ↑(ntt.Q &&& i1)
  let (res1 : U32) ← ↑(core.num.U32.wrapping_add res i2)
  massert (res1 < ntt.Q)
  ok res1

@[simp]
def ntt.SymCryptMlKemModAdd_eq (a : U32) (b : U32) :
  SymCryptMlKemModAdd a b = SymCryptMlKemModAdd' a b := by
  unfold SymCryptMlKemModAdd SymCryptMlKemModAdd'
  simp
  intros
  split <;> simp

-- TODO: register those as `scalar_tac_simp`?
@[simp, scalar_tac_simp, bvify_simps] theorem ntt.Q_eq : Q = 3329#u32 := by rfl
@[simp] theorem ntt.NegQInvModR_eq : ntt.NegQInvModR = 3327#u32 := by rfl
@[simp] theorem ntt.Rmask_eq : ntt.Rmask = 65535#u32 := by rfl
@[simp] theorem ntt.Rlog2_eq : ntt.Rlog2 = 16#u32 := by rfl

attribute [local simp] Spec.Q -- TODO: add this to the scalar_tac simp set

-- TODO: generalize, move
/-@[simp] theorem core.num.U32.and_val (x y : U32) :
  (x &&& y).val = (x.bv &&& y.bv).toNat := by
  sorry-/

/-
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
-/

/-
theorem Scalar.eq_equiv_bv__eq {ty : ScalarTy} (x y : Scalar ty) :
  x = y ↔ x.bv_ = y.bv_ := by
  rw [Scalar.eq_equiv]
  rw [BitVec.toNat_eq]
  unfold Scalar.bv_
  split <;> simp <;>
  sorry

theorem U8.eq_equiv_bv_eq (x y : U8) : x = y ↔ x.bv = y.bv := by apply Scalar.eq_equiv_bv__eq
theorem U16.eq_equiv_bv_eq (x y : U16) : x = y ↔ x.bv = y.bv := by apply Scalar.eq_equiv_bv__eq
theorem U32.eq_equiv_bv_eq (x y : U32) : x = y ↔ x.bv = y.bv := by apply Scalar.eq_equiv_bv__eq
theorem U64.eq_equiv_bv_eq (x y : U64) : x = y ↔ x.bv = y.bv := by apply Scalar.eq_equiv_bv__eq
theorem U128.eq_equiv_bv_eq (x y : U128) : x = y ↔ x.bv = y.bv := by apply Scalar.eq_equiv_bv__eq
theorem Usize.eq_equiv_bv_eq (x y : Usize) : x = y ↔ x.bv = y.bv := by apply Scalar.eq_equiv_bv__eq

theorem Scalar.ofIntCore_bv {ty : ScalarTy} (x : Int) h :
  (@Scalar.ofIntCore ty x h).bv_ = if ty.isSigned then BitVec.ofInt _ x else BitVec.ofNat _ x.toNat :=
  by sorry

@[simp] theorem U8.ofInt_bv (x : Int) h : U8.bv (U8.ofInt x h) = BitVec.ofNat _ x.toNat := by apply Scalar.ofIntCore_bv
@[simp] theorem U16.ofInt_bv (x : Int) h : U16.bv (U16.ofInt x h) = BitVec.ofNat _ x.toNat := by apply Scalar.ofIntCore_bv
@[simp] theorem U32.ofInt_bv (x : Int) h : U32.bv (U32.ofInt x h) = BitVec.ofNat _ x.toNat := by apply Scalar.ofIntCore_bv
@[simp] theorem U64.ofInt_bv (x : Int) h : U64.bv (U64.ofInt x h) = BitVec.ofNat _ x.toNat := by apply Scalar.ofIntCore_bv
@[simp] theorem U128.ofInt_bv (x : Int) h : U128.bv (U128.ofInt x h) = BitVec.ofNat _ x.toNat := by apply Scalar.ofIntCore_bv
@[simp] theorem Usize.ofInt_bv (x : Int) h : Usize.bv (Usize.ofInt x h) = BitVec.ofNat _ x.toNat := by apply Scalar.ofIntCore_bv-/

/-
theorem Scalar.add_bv_spec {ty} {x y : Scalar ty} (hmin : Scalar.min ty ≤ x.val + y.val) (hmax : x.val + y.val ≤ Scalar.max ty) :
  ∃ (z : Scalar ty), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv_ = x.bv_ + y.bv_ := by sorry

theorem U8.add_bv_spec {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
  ∃ (z : U8), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec; scalar_tac; apply hmax

theorem U16.add_bv_spec {x y : U16} (hmax : x.val + y.val ≤ U16.max) :
  ∃ (z : U16), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec; scalar_tac; apply hmax

theorem U32.add_bv_spec {x y : U32} (hmax : x.val + y.val ≤ U32.max) :
  ∃ (z : U32), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec; scalar_tac; apply hmax

theorem U64.add_bv_spec {x y : U64} (hmax : x.val + y.val ≤ U64.max) :
  ∃ (z : U64), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec; scalar_tac; apply hmax

theorem U128.add_bv_spec {x y : U128} (hmax : x.val + y.val ≤ U128.max) :
  ∃ (z : U128), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec; scalar_tac; apply hmax

theorem Usize.add_bv_spec {x y : Usize} (hmax : x.val + y.val ≤ Usize.max) :
  ∃ (z : Usize), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec; scalar_tac; apply hmax

theorem I8.add_bv_spec {x y : I8} (hmin : I8.min ≤ x.val + y.val) (hmax : x.val + y.val ≤ I8.max) :
  ∃ (z : I8), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec <;> scalar_tac

theorem I16.add_bv_spec {x y : I16} (hmin : I16.min ≤ x.val + y.val) (hmax : x.val + y.val ≤ I16.max) :
  ∃ (z : I16), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec <;> scalar_tac

theorem I32.add_bv_spec {x y : I32} (hmin : I32.min ≤ x.val + y.val) (hmax : x.val + y.val ≤ I32.max) :
  ∃ (z : I32), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec <;> scalar_tac

theorem I64.add_bv_spec {x y : I64} (hmin : I64.min ≤ x.val + y.val) (hmax : x.val + y.val ≤ I64.max) :
  ∃ (z : I64), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec <;> scalar_tac

theorem I128.add_bv_spec {x y : I128} (hmin : I128.min ≤ x.val + y.val) (hmax : x.val + y.val ≤ I128.max) :
  ∃ (z : I128), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec <;> scalar_tac

theorem Isize.add_bv_spec {x y : Isize} (hmin : Isize.min ≤ x.val + y.val) (hmax : x.val + y.val ≤ Isize.max) :
  ∃ (z : Isize), x + y = ok z ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv :=
  by apply Scalar.add_bv_spec <;> scalar_tac

theorem Scalar.sub_bv_spec {ty} {x y : Scalar ty} (hmin : Scalar.min ty ≤ x.val - y.val) (hmax : x.val - y.val ≤ Scalar.max ty) :
  ∃ (z : Scalar ty), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv_ = x.bv_ - y.bv_ := by sorry

theorem U8.sub_bv_spec {x y : U8} (hmin : 0 ≤ x.val - y.val) (hmax : x.val - y.val ≤ U8.max) :
  ∃ (z : U8), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec; scalar_tac; apply hmax

theorem U16.sub_bv_spec {x y : U16} (hmin : 0 ≤ x.val - y.val) (hmax : x.val - y.val ≤ U16.max) :
  ∃ (z : U16), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec; scalar_tac; apply hmax

theorem U32.sub_bv_spec {x y : U32} (hmin : 0 ≤ x.val - y.val) (hmax : x.val - y.val ≤ U32.max) :
  ∃ (z : U32), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec; scalar_tac; apply hmax

theorem U64.sub_bv_spec {x y : U64} (hmin : 0 ≤ x.val - y.val) (hmax : x.val - y.val ≤ U64.max) :
  ∃ (z : U64), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec; scalar_tac; apply hmax

theorem U128.sub_bv_spec {x y : U128} (hmin : 0 ≤ x.val - y.val) (hmax : x.val - y.val ≤ U128.max) :
  ∃ (z : U128), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec; scalar_tac; apply hmax

theorem Usize.sub_bv_spec {x y : Usize} (hmin : 0 ≤ x.val - y.val) (hmax : x.val - y.val ≤ Usize.max) :
  ∃ (z : Usize), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec; scalar_tac; apply hmax

theorem I8.sub_bv_spec {x y : I8} (hmin : I8.min ≤ x.val - y.val) (hmax : x.val - y.val ≤ I8.max) :
  ∃ (z : I8), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec <;> scalar_tac

theorem I16.sub_bv_spec {x y : I16} (hmin : I16.min ≤ x.val - y.val) (hmax : x.val - y.val ≤ I16.max) :
  ∃ (z : I16), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec <;> scalar_tac

theorem I32.sub_bv_spec {x y : I32} (hmin : I32.min ≤ x.val - y.val) (hmax : x.val - y.val ≤ I32.max) :
  ∃ (z : I32), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec <;> scalar_tac

theorem I64.sub_bv_spec {x y : I64} (hmin : I64.min ≤ x.val - y.val) (hmax : x.val - y.val ≤ I64.max) :
  ∃ (z : I64), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec <;> scalar_tac

theorem I128.sub_bv_spec {x y : I128} (hmin : I128.min ≤ x.val - y.val) (hmax : x.val - y.val ≤ I128.max) :
  ∃ (z : I128), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec <;> scalar_tac

theorem Isize.sub_bv_spec {x y : Isize} (hmin : Isize.min ≤ x.val - y.val) (hmax : x.val - y.val ≤ Isize.max) :
  ∃ (z : Isize), x - y = ok z ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv :=
  by apply Scalar.sub_bv_spec <;> scalar_tac

theorem Scalar.mul_bv_spec {ty} {x y : Scalar ty} (hmin : Scalar.min ty ≤ x.val * y.val) (hmax : x.val * y.val ≤ Scalar.max ty) :
  ∃ (z : Scalar ty), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv_ = x.bv_ * y.bv_ := by sorry

set_option scalarTac.nonLin true

theorem U8.mul_bv_spec {x y : U8} (hmax : x.val * y.val ≤ U8.max) :
  ∃ (z : U8), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec; scalar_tac; apply hmax

theorem U16.mul_bv_spec {x y : U16} (hmax : x.val * y.val ≤ U16.max) :
  ∃ (z : U16), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec; scalar_tac; apply hmax

theorem U32.mul_bv_spec {x y : U32} (hmax : x.val * y.val ≤ U32.max) :
  ∃ (z : U32), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec; scalar_tac; apply hmax

theorem U64.mul_bv_spec {x y : U64} (hmax : x.val * y.val ≤ U64.max) :
  ∃ (z : U64), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec; scalar_tac; apply hmax

theorem U128.mul_bv_spec {x y : U128} (hmax : x.val * y.val ≤ U128.max) :
  ∃ (z : U128), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec; scalar_tac; apply hmax

theorem Usize.mul_bv_spec {x y : Usize} (hmax : x.val * y.val ≤ Usize.max) :
  ∃ (z : Usize), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec; scalar_tac; apply hmax

theorem I8.mul_bv_spec {x y : I8} (hmin : I8.min ≤ x.val * y.val) (hmax : x.val * y.val ≤ I8.max) :
  ∃ (z : I8), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec <;> scalar_tac

theorem I16.mul_bv_spec {x y : I16} (hmin : I16.min ≤ x.val * y.val) (hmax : x.val * y.val ≤ I16.max) :
  ∃ (z : I16), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec <;> scalar_tac

theorem I32.mul_bv_spec {x y : I32} (hmin : I32.min ≤ x.val * y.val) (hmax : x.val * y.val ≤ I32.max) :
  ∃ (z : I32), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec <;> scalar_tac

theorem I64.mul_bv_spec {x y : I64} (hmin : I64.min ≤ x.val * y.val) (hmax : x.val * y.val ≤ I64.max) :
  ∃ (z : I64), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec <;> scalar_tac

theorem I128.mul_bv_spec {x y : I128} (hmin : I128.min ≤ x.val * y.val) (hmax : x.val * y.val ≤ I128.max) :
  ∃ (z : I128), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec <;> scalar_tac

theorem Isize.mul_bv_spec {x y : Isize} (hmin : Isize.min ≤ x.val * y.val) (hmax : x.val * y.val ≤ Isize.max) :
  ∃ (z : Isize), x * y = ok z ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv :=
  by apply Scalar.mul_bv_spec <;> scalar_tac

set_option scalarTac.nonLin false
-/

/-
theorem Scalar.unsigned_ofInt_bv_lt_equiv {ty} (h : ¬ ty.isSigned) (x y : Int) (hx) (hy) :
  (@Scalar.ofInt ty x hx).bv_ < (@Scalar.ofInt ty y hy).bv_ ↔ x < y := by
  sorry

@[simp] theorem U8.toNat_mod_max_eq (x : U8) : x.toNat % (U8.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U8.toNat_mod_max_eq' (x : U8) : x.toNat % 256 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U16.toNat_mod_max_eq (x : U16) : x.toNat % (U16.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U16.toNat_mod_max_eq' (x : U16) : x.toNat % 65536 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U32.toNat_mod_max_eq (x : U32) : x.toNat % (U32.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U32.toNat_mod_max_eq' (x : U32) : x.toNat % 4294967296 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U64.toNat_mod_max_eq (x : U64) : x.toNat % (U64.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U64.toNat_mod_max_eq' (x : U64) : x.toNat % 18446744073709551616 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U128.toNat_mod_max_eq (x : U128) : x.toNat % (U128.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U128.toNat_mod_max_eq' (x : U128) : x.toNat % 340282366920938463463374607431768211456 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem Usize.toNat_mod_max_eq (x : Usize) : x.toNat % (Usize.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp] theorem U8.val_mod_max_eq (x : U8) : x.val % (U8.max + 1) = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem U8.val_mod_max_eq' (x : U8) : x.val % 256 = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem U16.val_mod_max_eq (x : U16) : x.val % (U16.max + 1) = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem U16.val_mod_max_eq' (x : U16) : x.val % 65536 = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem U32.val_mod_max_eq (x : U32) : x.val % (U32.max + 1) = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem U32.val_mod_max_eq' (x : U32) : x.val % 4294967296 = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem U64.val_mod_max_eq (x : U64) : x.val % (U64.max + 1) = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem U64.val_mod_max_eq' (x : U64) : x.val % 18446744073709551616 = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem U128.val_mod_max_eq (x : U128) : x.val % (U128.max + 1) = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem U128.val_mod_max_eq' (x : U128) : x.val % 340282366920938463463374607431768211456 = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac

@[simp] theorem Usize.val_mod_max_eq (x : Usize) : x.val % (Usize.max + 1) = x.val := by
  apply Int.emod_eq_of_lt <;> scalar_tac-/

-- TODO: improve scalar_tac to reason about inequalities between bitvectors?

/-
/-- We're not using this theorem, but we keep the proof here because it can be useful if we want
    to generalize the NTT. -/
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
-/

/-
theorem Nat.eq_iff_intCast_eq (n m : Nat) : n = m ↔ (n : Int) = (m : Int) := by omega
theorem Nat.lt_iff_intCast_eq (n m : Nat) : n < m ↔ (n : Int) < (m : Int) := by omega
theorem Nat.le_iff_intCast_eq (n m : Nat) : n ≤ m ↔ (n : Int) ≤ (m : Int) := by omega

-- TODO: generalize
--@[simp] theorem U32.zmod_val_eq_mod (n : Nat) (x : U32) : ZMod.val (x.val : ZMod n) = x.val % n := by sorry
--@[simp] theorem U32.zmod_cast_int_eq_mod (n : Nat) (x : U32) : ZMod.cast (x.val : ZMod n) = x.val % n := by sorry

-- TODO: generalize
/-@[simp] theorem U8.val_max_zero_eq (x : U8) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem U16.val_max_zero_eq (x : U16) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem U32.val_max_zero_eq (x : U32) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem U64.val_max_zero_eq (x : U64) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem U128.val_max_zero_eq (x : U128) : x.val ⊔ 0 = x.val := by scalar_tac
@[simp] theorem Usize.val_max_zero_eq (x : Usize) : x.val ⊔ 0 = x.val := by scalar_tac-/
-/

theorem Int.neg_add_emod_self_left {a b c : ℤ} : (-a + b) % c = ((c - a) + b) % c := by
  conv => lhs; rw [← Int.add_emod_self_left]
  ring_nf

theorem Int.sub_eq_add_minus : ∀ (a b : Int), a - b = a + (-b) := by omega
theorem Int.add_minus_add_eq_minus_add : ∀ (a b c : Int), a + (-b + c) = (-b) + (a + c) := by omega
theorem Int.minus_add_minus_add_eq_minus_add : ∀ (a b c : Int), -a + (-b + c) = -(a + b) + c := by omega

open Lean.Parser.Tactic in
/-- A tactic to normalize modulo operations.

    We do the following:
    ```
    (x + y - 12) % 16 = (-12 + x + y) % 16          -- push the negative constant to the left
                      = (-12 + (x + y)) % 16        -- isolate it
                      = ((16 - 12) + (x + y)) % 16  -- add the modulus itself
                      = (4 + x + y) % 16
    ```
    TODO: it doesn't work well if we have `- x` somewhere in the expression
-/
macro "norm_mod" cfg:optConfig loc:(location)? : tactic =>
  `(tactic |
    -- TODO: repeteadly performing the operation causes issues
    -- repeat fail_if_no_progress
      -- Push to the left and isolate
      --ring_nf $cfg:optConfig $(loc)? <;> -- push to the left
      (try simp only [Int.add_assoc, Int.sub_eq_add_minus, Int.add_minus_add_eq_minus_add, Int.minus_add_minus_add_eq_minus_add] $(loc)?) <;> -- isolate the constant
      (try rw [Int.neg_add_emod_self_left] $(loc)?) <;> -- add the modulo
      ring_nf $cfg:optConfig $(loc)? -- normalize again
    )

/-
theorem ZMod.castInt_val_sub {n : ℕ} [NeZero n] {a b : ZMod n} :
  (a - b).val = (a.val - (b.val : Int)) % n := by
  sorry

/- TODO: move -/
attribute [zify_simps] BitVec.toNat_eq BitVec.lt_def BitVec.le_def
                       BitVec.toNat_umod BitVec.toNat_add BitVec.toNat_sub BitVec.toNat_ofNat
                       BitVec.toNat_and BitVec.toNat_or BitVec.toNat_xor
attribute [zify_simps] ZMod.eq_iff_mod ZMod.val_intCast ZMod.val_add ZMod.val_sub ZMod.val_mul
                       ZMod.castInt_val_sub
attribute [zify_simps] Nat.eq_iff_intCast_eq Nat.lt_iff_intCast_eq Nat.le_iff_intCast_eq -- TODO: remove?
attribute [zify_simps] U32.bv_toNat_eq U32.toNat -- TODO: complete
-/

attribute [local bvify_simps, local scalar_tac_simp] Spec.Q

-- TODO: generalize and move
--attribute [bvify_simps] U32.eq_equiv_bv_eq U32.wrapping_sub_bv_eq
--attribute [bvify_simps] UScalarTy.U32_numBits_eq U32.ofNat_bv

-- TODO: use this to prototype `progress_simp_post`
example
  (a : U32)
  (b : U32)
  (ha : (↑a : ℕ) < 3329)
  (hb : (↑b : ℕ) < 3329)
  (this_1 : a.bv < 3329#32)
  (this : b.bv < 3329#32)
  (c1 : U32)
  (hc1 : (↑c1 : ℕ) = (↑a : ℕ) + (↑b : ℕ))
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (hc2 : c2 = core.num.U32.wrapping_sub c1 3329#u32) :
  ∃ c,
  (do
        let i1 ← c2 >>> 16#i32
        if i1 = 0#u32 then ok () else massert (decide (i1 = 65535#u32))
        let __discr ← (↑(3329#u32 &&& i1) : Result U32)
        let __discr ← (↑(core.num.U32.wrapping_add c2 __discr) : Result U32)
        massert (decide ((↑__discr : ℕ) < 3329))
        ok __discr) =
      ok c ∧
    (↑(↑c : ℕ) : Spec.Zq) = (↑(↑a : ℕ) : Spec.Zq) + (↑(↑b : ℕ) : Spec.Zq) ∧ (↑c : ℕ) < 3329
  := by
  progress as ⟨ c3, hc3 ⟩
  -- we want to reduce `16#i32.toNat` to `16`
  simp only [IScalar.toNat, IScalar.ofInt_val_eq, Int.reduceToNat] at hc3
  sorry


-- TODO: move, use in progress
@[simp] theorem massert_ok (b : Bool) : massert b = ok () ↔ b := by simp [massert]

-- TODO: minimize and move
example
  (a : U32)
  (b : U32)
  (ha : (↑a : ℕ) < 3329)
  (hb : (↑b : ℕ) < 3329)
  (c1 : U32)
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (hc2 : c2 = core.num.U32.wrapping_sub c1 3329#u32)
  (c3 : U32)
  (hc3 : c3.bv = c2.bv >>> 16#i32.toNat) :
  (c1.bv - 3329#32 + (3329#32 &&& c3.bv)) % 3329#32 = (a.bv + b.bv) % 3329#32
  := by
  bv_tac

-- TODO: generalize and move
@[simp] theorem UScalar.size_UScalarTyU32 : UScalar.size .U32 = U32.size := by scalar_tac

@[progress]
theorem ntt.SymCryptMlKemModAdd'_spec (a : U32) (b : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) :
  ∃ (c : U32), ntt.SymCryptMlKemModAdd' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) + (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemModAdd'
  fsimp at *
  progress
  progress
  progress with U32.add_bv_spec as ⟨ c1, hc1 ⟩
  progress as ⟨ c2, hc2 ⟩
  progress as ⟨ c3, hc3 ⟩

  -- TODO: handle this properly with progress
  have hIf : (if c3 = 0#u32 then ok () else massert (c3 = 65535#u32)) = ok () := by
    split <;> simp
    bv_tac
  progress with hIf; clear hIf

  progress as ⟨ c4, hc4 ⟩
  progress as ⟨ c5, hc5 ⟩

  -- Prove the post-condition (we also need this prove that the assert holds)
  have hPost :
    (c5.val : Spec.Zq) = (a.val : Spec.Zq) + (b.val : Spec.Zq) ∧
    c5.val < Spec.Q := by

    /- We use bitvectors to automate the proofs -/
    have hc5' : c5.bv = (a.bv + b.bv) % 3329#32 ∧ c5.bv < 3329#32 := by
      bv_tac

    /- We need to convert the bit vectors and ZMod elements to ℕ -/
    natify at *
    fsimp_all [U32.size, U32.numBits]
    /- There just remains simple arithmetic reasonings -/
    scalar_tac

  -- Finish the proof
  progress
  -- Post-condition
  apply hPost

/-!
Subtraction modulo
-/

def ntt.SymCryptMlKemModSub' (a : U32) (b : U32) : Result U32 := do
  let i ← 2#u32 * ntt.Q
  massert (a < i)
  massert (b <= ntt.Q)
  let (res : U32) ← ↑(core.num.U32.wrapping_sub a b)
  let i1 ← res >>> 16#i32
  (if i1 = 0#u32 then ok () else massert (i1 = 65535#u32))
  let (i2 : U32) ← ↑(ntt.Q &&& i1)
  let (res1 : U32) ← ↑(core.num.U32.wrapping_add res i2)
  massert (res1 < ntt.Q)
  ok res1

@[simp]
def ntt.SymCryptMlKemModSub_eq (a : U32) (b : U32) :
  SymCryptMlKemModSub a b = SymCryptMlKemModSub' a b := by
  unfold SymCryptMlKemModSub SymCryptMlKemModSub'
  simp
  intros
  split <;> simp

-- TODO: move
example
  (a : U32)
  (b : U32)
  (h0 : a.bv < 6658#32)
  (h1 : ¬(a.bv - b.bv) >>> 16 = 0#32)
  (this : b.bv = 3329#32) :
  (a.bv - 3329#32) >>> 16 = 65535#32
  := by
  bv_decide

#eval 0x00000cb8#32
#eval 0x00000d00#32

example
  (a b : BitVec 32)
  (h0 : a < 3329#32)
  (h1 : b < 3329#32) :
  (a - b + (3329#32 &&& (a - b) >>> 16)) % 3329#32 = (a + 3329#32 - b) % 3329#32
  := by

  bv_decide

example
  (a : U32)
  (b : U32)
  (h0 : a.bv < 6658#32)
  (h1 : b.val = 3329) :
  (a.bv - b.bv + (3329#32 &&& (a.bv - b.bv) >>> 16)) % 3329#32 = (a.bv + 3329#32 - b.bv) % 3329#32
  := by
  have : b.bv = 3329#32 := by sorry -- TODO: bvify doesn't do this
  bv_decide

example
  (a : U32)
  (b : U32)
  (h : (↑a : ℕ) < 3329 ∧ (↑b : ℕ) < 3329 ∨ (↑a : ℕ) < 6658 ∧ (↑b : ℕ) = 3329)
  (c1 : U32)
  (hc1 : c1 = core.num.U32.wrapping_sub a b)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16#i32.toNat)
  (c3 : U32)
  (hc3_1 : c3.bv = 3329#32 &&& c2.bv)
  (c4 : U32)
  (hc3 : c4 = core.num.U32.wrapping_add c1 c3) :
  c4.bv % 3329#32 = (a.bv + 3329#32 - b.bv) % 3329#32
  := by
  dcases h <;>
  bvify 32 at * <;>
  rename_i h <;>
  obtain ⟨ h0, h1 ⟩ := h <;>
  simp_all <;> clear hc3_1 hc3 c1 c2 c3 c4 hc1 hc2
  . bv_decide
  . have : b.bv = 3329#32 := by sorry -- TODO: bvify doesn't do this
    bv_decide

-- TODO: move
@[simp, natify_simps]
theorem ZMod.val_sub' {n : ℕ} [NeZero n] (a b : ZMod n) : (a - b).val =
  (a.val + (n - b.val)) % n := by sorry

-- TODO: move
theorem ZMod_Nat_eq_imp_mod_eq {n : ℕ} {a b : Nat} (h : (a : ZMod n) = (b : ZMod n)) :
  a % n = b % n := by sorry

/-- We first introduce a general, auxiliary version of the spec, that we later split in two.
    One of them is used to subtract numbers in the NTT, the other is used in the Montgomery
    multiplication to put the number back in the bounds.

    TODO: remove
 -/
theorem ntt.SymCryptMlKemModSub'_aux_spec' (a : U32) (b : U32)
  (h : (a.val < Spec.Q ∧ b.val < Spec.Q) ∨ (a.val < 2 * Spec.Q ∧ b.val = Spec.Q)) :
  ∃ (c : U32), ntt.SymCryptMlKemModSub' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemModSub'
  simp at *
  progress as ⟨ twoQ, hTwoQ ⟩
  progress -- massert
  clear twoQ hTwoQ
  progress -- massert

  progress as ⟨ c1, hc1 ⟩
  progress as ⟨ c2, hc2 ⟩

  have hIf : (if c2 = 0#u32 then ok () else massert (c2 = 65535#u32)) = ok () := by
    -- TODO: better precondition
    -- TODO: simplify
    dcases h <;>
    split <;> simp <;>
    bvify 32 at * <;>
    simp only [Int.reduceToNat] at hc2 <;> -- TODO: add Int.reduceToNat to bvify, scalar_tac, etc.
    simp_all
    . bv_decide
    . -- TODO: bvify needs to split the conjunctions!!
      have : a.bv < 6658#32 := by simp [*] -- TODO
      have : b.bv = 3329#32 := by sorry -- TODO: bvify
      clear hc1 hc2 c1 c2
      simp [*]
      bv_decide

  progress with hIf; clear hIf

  progress as ⟨ c3, hc3 ⟩
  progress as ⟨ c4, hc3 ⟩

  -- Prove the post-condition (we also need this prove that the assert holds)
  have hPost :
    (c4.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
    c4.val < Spec.Q := by

    have ⟨ hbvEq, hbvLt ⟩ : c4.bv % 3329#32 = (a.bv + 3329#32 - b.bv) % 3329#32 ∧
               c4.bv < 3329#32 := by
      -- TODO: add to bvify
      simp only [IScalar.toNat, IScalar.ofInt_val_eq, Int.reduceToNat, UScalarTy.U32_numBits_eq,
        U32.ofNat_bv] at *
      dcases h
      . bv_tac
      . -- TODO: bvify needs to split the conjunctions
        have ha : a.bv < 6658#32 := by bvify 32 at *; simp [*]
        have hb : b.bv = 3329#32 := by sorry
        simp_all
        clear * - ha -- TODO: bv_decide sometimes fails when there are too many hypotheses: we should clear the useless ones
        -- have : b.bv  6658#32 := by bvify 32 at * ; simp [*]
        split_conjs
        . bv_tac
        . bv_tac

    natify at *
    simp at *
    norm_mod

    split_conjs
    . rw [hbvEq]
      have : (4294967296 - ↑b + (↑a + 3329)) % 4294967296 =
             (a.val + (3329 - b.val)) := by scalar_tac +nonLin
      rw [this]
      -- TODO: zmodify
      scalar_tac +nonLin
    . apply hbvLt

  progress -- massert
  apply hPost

example
  (a : U32)
  (b : U32)
  (ha : a.val < b.val + 3329)
  (c1 : U32)
  (c2 : U32)
  (hb : b.bv ≤ 3329#32)
  (hc1 : c1.bv = a.bv - b.bv)
  (hc2 : c2.bv = c1.bv >>> 16)
  (_ : c2.bv ≠ 0#32) :
  c2.bv = 65535#32
  := by
  have : a.bv < b.bv + 3329#32 := by
    sorry -- TODO
  bv_tac

-- TODO: move
theorem BitVec.lt_pow_ofNat_le {n : Nat} (a b : Nat) (h0 : b < 2^n) (h1 : a ≤ b) :
  BitVec.ofNat n a ≤ BitVec.ofNat n b := by
  have : 0 < 2^n := by simp
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; omega
  simp [*]

@[aesop safe forward (pattern := a ≤ b)]
theorem BitVec.if_lt_pow_ofNat_le {n : Nat} (a b : Nat) (h0 : a ≤ b) :
  if b < 2^n then BitVec.ofNat n a ≤ BitVec.ofNat n b else True := by
  split
  . apply BitVec.lt_pow_ofNat_le <;> assumption
  . simp

-- TODO: move
theorem BitVec.lt_pow_ofNat_lt {n : Nat} (a b : Nat) (h0 : b < 2^n) (h0 : a < b) :
  BitVec.ofNat n a < BitVec.ofNat n b := by
  have : 0 < 2^n := by simp
  have : a % 2^n = a := by apply Nat.mod_eq_of_lt; omega
  have : b % 2^n = b := by apply Nat.mod_eq_of_lt; omega
  simp [*]

@[aesop safe forward (pattern := a < b)]
theorem BitVec.if_lt_pow_ofNat_lt {n : Nat} (a b : Nat) (h0 : a < b) :
  if b < 2^n then BitVec.ofNat n a < BitVec.ofNat n b else True := by
  split
  . apply BitVec.lt_pow_ofNat_lt <;> assumption
  . simp

@[aesop safe forward]
theorem BitVec'.if_lt_pow_ofNat_lt (a b : Nat) (h0 : a < b) :
  if b < U32.max then BitVec.ofNat 32 a < BitVec.ofNat 32 b else True := by
  split
  . apply BitVec.lt_pow_ofNat_lt <;> scalar_tac
  . simp

theorem Nat.le_imp_if_le (a b : Nat) (h : a ≤ b) (p q : Prop) : (if a ≤ b then p else q) ↔ p := by simp [*]
theorem Nat.lt_imp_if_lt (a b : Nat) (h : a < b) (p q : Prop) : (if a < b then p else q) ↔ p := by simp [*]

-- TODO: remove the one above
theorem ntt.SymCryptMlKemModSub'_aux_spec (a : U32) (b : U32)
  (_ : a.val ≤ 2*3329)
  (ha : a.val < b.val + 3329)
  (hb : b.val ≤ 3329) :
  ∃ (c : U32), ntt.SymCryptMlKemModSub' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemModSub'
  simp at *
  progress as ⟨ twoQ, hTwoQ ⟩
  progress -- massert
  clear twoQ hTwoQ
  progress -- massert

  progress as ⟨ c1, hc1 ⟩
  progress as ⟨ c2, hc2 ⟩

  -- TODO: automate this with bvify
  have : a.bv < b.bv + 3329#32 := by
    saturate
    simp (maxDischargeDepth := 1) (disch := scalar_tac) only [Nat.le_imp_if_le, Nat.lt_imp_if_lt] at *
    fsimp only [U32.BitVec_ofNat_val_eq] at *
    fsimp [BitVec.ofNat_add, U32.BitVec_ofNat_val_eq] at *
    assumption

  have hIf : (if c2 = 0#u32 then ok () else massert (c2 = 65535#u32)) = ok () := by
    -- TODO: better precondition
    -- TODO: simplify
    bvify 32 at *
    simp at hc2
    -- TODO:
    split <;> simp
    bv_tac

  progress with hIf; clear hIf

  progress as ⟨ c3, hc3 ⟩
  progress as ⟨ c4, hc3 ⟩

  -- Prove the post-condition (we also need this prove that the assert holds)
  have hPost :
    (c4.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
    c4.val < Spec.Q := by

    have ⟨ hbvEq, hbvLt ⟩ : c4.bv % 3329#32 = (a.bv + 3329#32 - b.bv) % 3329#32 ∧
               c4.bv < 3329#32 := by
      -- TODO: add to bvify
      simp only [IScalar.toNat, IScalar.ofInt_val_eq, Int.reduceToNat, UScalarTy.U32_numBits_eq,
        U32.ofNat_bv] at *
      bv_tac

    natify at *
    fsimp at *
    norm_mod

    split_conjs
    . rw [hbvEq]
      have : (4294967296 - ↑b + (↑a + 3329)) % 4294967296 =
             (a.val + (3329 - b.val)) := by scalar_tac +nonLin
      rw [this]
      scalar_tac +nonLin
    . apply hbvLt

  progress -- massert
  apply hPost

theorem ntt.SymCryptMlKemModSub'_spec (a : U32) (b : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) :
  ∃ (c : U32), ntt.SymCryptMlKemModSub' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  progress with SymCryptMlKemModSub'_aux_spec
  simp_all

theorem ntt.SymCryptMlKemModSub'_sub_Q_spec (a : U32) (b : U32)
  (ha : a.val < 2 * Spec.Q) (hb : b.val = Spec.Q) :
  ∃ (c : U32), ntt.SymCryptMlKemModSub' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  progress with SymCryptMlKemModSub'_aux_spec
  simp_all

-- TODO: having too many theorems like this can make the context explode
theorem UScalar_mul_bound {ty : UScalarTy} (x y : UScalar ty) :
  x.val * y.val ≤ UScalar.max ty * UScalar.max ty := by
  have := x.hmax
  have := y.hmax
  have := @Int.mul_le_mul x.val y.val (UScalar.max ty) (UScalar.max ty) (by scalar_tac) (by scalar_tac)
  omega

@[nonlin_scalar_tac x.val * y.val]
theorem U8.mul_bound (x y : U8) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ U8.max * U8.max := by
  have := UScalar_mul_bound x y
  scalar_tac

@[nonlin_scalar_tac x.val * y.val]
theorem U16.mul_bound (x y : U16) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ U16.max * U16.max := by
  have := UScalar_mul_bound x y
  scalar_tac

@[nonlin_scalar_tac x.val * y.val]
theorem U32.mul_bound (x y : U8) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ U32.max * U32.max := by
  have := UScalar_mul_bound x y
  scalar_tac

@[nonlin_scalar_tac x.val * y.val]
theorem U64.mul_bound (x y : U64) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ U64.max * U64.max := by
  have := UScalar_mul_bound x y
  scalar_tac

@[nonlin_scalar_tac x.val * y.val]
theorem U128.mul_bound (x y : U128) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ U128.max * U128.max := by
  have := UScalar_mul_bound x y
  scalar_tac

@[nonlin_scalar_tac x.val * y.val]
theorem Usize.mul_bound (x y : Usize) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ Usize.max * Usize.max := by
  have := UScalar_mul_bound x y
  scalar_tac

-- TODO: move
@[simp] theorem UScalar.bv_and {ty} (x y : UScalar ty) : (x &&& y).bv = x.bv &&& y.bv := by rfl
@[simp] theorem UScalar.bv_or {ty} (x y : UScalar ty) : (x ||| y).bv = x.bv ||| y.bv := by rfl
@[simp] theorem IScalar.bv_and {ty} (x y : IScalar ty) : (x &&& y).bv = x.bv &&& y.bv := by rfl
@[simp] theorem IScalar.bv_or {ty} (x y : IScalar ty) : (x ||| y).bv = x.bv ||| y.bv := by rfl

--set_option scalarTac.nonLin true

@[push_cast, simp] -- TODO: this doesn't work
theorem ZMod.intCast_mod_atLeastTwo (a : ℤ) (b : ℕ) [b.AtLeastTwo] :
  ((a % (@OfNat.ofNat ℤ b instOfNatAtLeastTwo) : ℤ) : ZMod b) = (a : ZMod b) := by
  have : @OfNat.ofNat ℤ b instOfNatAtLeastTwo = b := by
    unfold OfNat.ofNat instOfNatAtLeastTwo
    simp
  rw [this]
  simp

@[local push_cast, local simp] -- TODO: doesn't get automatically applied!?
theorem ZMod.intCast_mod' (a : ℤ) (b : ℕ) (bz : Int) (h : bz = b) :
  ((a % bz) : ZMod b) = (a : ZMod b) := by
  simp [*]


@[local simp] theorem bv_and_65535_eq_mod (x : BitVec 32) : x &&& 65535#32 = x % 65536#32 := by bv_decide
@[local simp] theorem bv_shift_16_eq_div (x : BitVec 32) : x >>> 16 = x / 65536#32 := by bv_decide

@[local simp]
theorem mod_4294967296_65536_eq (x : Nat) : ((x % 4294967296) % 65536) = x % 65536 := by
  rw [Nat.mod_mod_of_dvd]
  omega

@[local simp]
theorem mod_65536_4294967296_eq (x : Nat) : ((x % 65536) % 4294967296) = x % 65536 := by
  apply Nat.mod_eq_of_lt; omega

/-!
Montgomery reduction
-/

theorem mont_reduce_no_divide_bv_spec (a b bMont tR : U32)
  (hbMont : bMont.bv = (b.bv * ntt.NegQInvModR.bv) &&& ntt.Rmask.bv)
  (htR : tR.bv = a.bv * b.bv + ((a.bv * bMont.bv) &&& ntt.Rmask.bv) * 3329) :
  tR.bv &&& ntt.Rmask.bv = 0 := by
  /- The proof strategy is as follows:
     - we first simplify the BitVec expressions (by using the fact that bit masking is equivalent to modulo, etc.)
     - go to ℤ and simplify further
     - go to ZMod
   -/
  simp at *
  simp [*]; clear hbMont htR

  -- Reason in ℤ and simplify the modulus
  zify; simp [- EuclideanDomain.mod_eq_zero]

  -- Go to ZMod
  have : 0 = 0 % (65536 : Int) := by simp
  rw [this]; clear this
  have : (65536 : Int) = (65536 : Nat) := by simp
  rw [this]; clear this
  rw [← ZMod_int_cast_eq_int_cast_iff]
  simp

  -- TODO: casting problems: automate that
  simp [ZMod.intCast_mod'] -- TODO: doesn't get automatically applied?

  -- Finish
  simp [mul_assoc]
  ring_nf
  have : (11075584 : ZMod 65536) = 0 := by rfl
  rw [this]; simp

-- TODO: move
@[aesop unsafe 50% apply]
theorem Nat.le_trans (a0 a1 b0 b1 : Nat) (h0 : a0 ≤ a1) (h2 : b0 ≤ b1) : a0 * b0 ≤ a1 * b1 := by
  have := @Nat.mul_le_mul_left b0 b1 a0 (by assumption)
  have := @Nat.mul_le_mul_right a0 a1 b1 (by assumption)
  omega

@[aesop unsafe 50% apply]
theorem Nat.lt_trans (a0 a1 b0 b1 : Nat) (h0 : a0 < a1) (h2 : b0 < b1) : a0 * b0 < a1 * b1 := by
  apply Nat.mul_lt_mul_of_lt_of_lt <;> assumption

@[aesop unsafe 50% apply]
theorem Nat.le_lt_trans (a0 a1 b0 b1 : Nat) (h0 : a0 ≤ a1) (h1 : 0 < a1) (h2 : b0 < b1) : a0 * b0 < a1 * b1 := by
  have := @Nat.mul_le_mul_left b0 b1 a0 (by assumption)
  have := @Nat.mul_le_mul_right a0 a1 b1 (by assumption)
  omega

@[aesop unsafe 50% apply]
theorem Nat.lt_le_trans (a0 a1 b0 b1 : Nat) (h0 : a0 < a1) (h1 : b0 ≤ b1) (h2 : 0 < b1) : a0 * b0 < a1 * b1 := by
  have := @Nat.mul_le_mul_left b0 b1 a0 (by assumption)
  have := @Nat.mul_le_mul_right a0 a1 b1 (by assumption)
  omega

syntax "scalar_tac_non_lin0" : tactic

-- TODO: we shouldn't need a maxRuleApplicationDepth of 4: 2 should be enough:
-- 1 for a backward rule + 1 for scalar_tac
macro_rules
| `(scalar_tac_non_lin0) => `(aesop)
/-
aesop (config := {strategy := .breadthFirst,
                      maxRuleApplicationDepth := 4,
                      enableSimp := true,
                      useSimpAll := false}) (add safe (by scalar_tac))
-/

syntax "scalar_tac_non_lin" : tactic

macro_rules
| `(tactic|scalar_tac_non_lin) =>
  `(tactic|(first | apply Nat.le_trans <;> scalar_tac
                  | apply Nat.lt_trans <;> scalar_tac
                  | apply Nat.le_lt_trans <;> scalar_tac
                  | apply Nat.lt_le_trans <;> scalar_tac))

theorem mont_reduce_bv_spec (a b bMont tR t : U32)
  (haBound : a.val < 3329)
  (hbBound : b.val < 3329)
  (hbMont : bMont.bv = (b.bv * ntt.NegQInvModR.bv) &&& ntt.Rmask.bv)
  (htR : tR.bv = a.bv * b.bv + ((a.bv * bMont.bv) &&& ntt.Rmask.bv) * 3329)
  (ht : t.bv = tR.bv >>> 16) :
  (t.val : ZMod Spec.Q) = (a.val : ZMod Spec.Q) * b.val * (U16.size : ZMod Spec.Q)⁻¹ ∧
  t.val < 2 * Spec.Q := by
  have hEq := mont_reduce_no_divide_bv_spec a b bMont tR hbMont htR
  have habLt : a.val * b.val < 3329 * U16.size := by
    scalar_tac_non_lin

  have hMont := mont_reduce_spec 3329 U16.size 3327 (a.val * b.val)
    (by simp [U16.size, U16.numBits]; exists 16) (by simp [U16.size, U16.numBits]) (by simp)
    (by scalar_tac_non_lin) (by simp [U16.size, U16.numBits]; constructor)
  -- Simplify the bit vector operations
  simp [mont_reduce] at hMont

  obtain ⟨ hMont, hBounds ⟩ := hMont
  rw [htR, hbMont] at ht
  simp [bv_and_65535_eq_mod] at ht -- TODO: why is this theorem not automatically applied?

  natify at ht; simp at ht
  natify; simp
  rw [ht]

  have : (a.val * b.val + a.val * (b.val * 3327) % 65536 * 3329) % 4294967296 =
         a.val * b.val + a.val * (b.val * 3327) % 65536 * 3329 := by
    apply Nat.mod_eq_of_lt
    scalar_tac
  rw [this]; clear this

  simp [U16.size, U16.numBits] at *
  zify
  simp [← mul_assoc, hMont, hBounds]

set_option maxHeartbeats 1000000

example (abMont abMontAnd : U32)
  (h : (abMont &&& 65535#u32).val * 3329#u32.val ≤ 65535 * 3329) :
  abMontAnd.val * 3329#u32.val ≤ U32.max :=
  by
  -- TODO: fix this
  assumption

#check UScalar.and_spec
@[progress]
theorem ntt.SymCryptMlKemMontMul_spec (a : U32) (b : U32) (bMont : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) --(hbMont : bMont.val < Spec.Q * Spec.Q)
  (hbMont : bMont.bv = (b.bv * ntt.NegQInvModR.bv) &&& Rmask.bv) :
  ∃ (c : U32), ntt.SymCryptMlKemMontMul a b bMont = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) * (b.val : Spec.Zq) * (2^16)⁻¹ ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemMontMul
  /-have : a.bv < 3329#32 := by -- TODO: bvfy?
    simp [U32.bv]
    scalar_tac
  have : b.bv < 3329#32 := by -- TODO: bvfy?
    simp [U32.bv]
    scalar_tac-/
  fsimp at *
  progress
  progress

  have bMontLe : bMont.val ≤ 65535 := by
    have : bMont.bv ≤ 65535#32 := by bv_decide
    natify at this; fsimp_all
  progress

  progress with U32.mul_bv_spec as ⟨ b1, hb1, hb1' ⟩
  simp at hb1'

  progress as ⟨ b2, hb2 ⟩

  have bMontLe : bMont = b2 := by
    bvify 32
    simp [*]
  progress -- massert

  -- TODO: scalar_tac is not good at reasoning about upper bounds in the presence of multiplication
  have : a.val * b.val ≤ 3329 * 3329 := by scalar_tac_non_lin
  progress with U32.mul_bv_spec as ⟨ ab, hab, hab' ⟩

  have : a.val * bMont.val ≤ 3329 * 65535 := by scalar_tac_non_lin
  progress with U32.mul_bv_spec as ⟨ abMont, _, habMont ⟩

  progress as ⟨ abMontAnd, _, habMontAnd ⟩

  have : (abMont &&& 65535#u32).val ≤ 65535 := by
    have : (U32.bv (abMont &&& 65535#u32)) ≤ 65535#32 := by
      -- TODO: remove the simp
      simp only [UScalar.bv_and, UScalarTy.U32_numBits_eq, U32.ofNat_bv, bv_and_65535_eq_mod]
      bv_tac
    natify at this; fsimp_all

  -- TODO: removing this assert makes progress fail below when attempting to
  -- unify expressions
  have : abMontAnd.val * (3329#u32).val ≤ U32.max := by
    have : abMontAnd.val * 3329 ≤ 65536 * 3329 := by
      scalar_tac_non_lin
    scalar_tac
  progress with U32.mul_bv_spec as ⟨ res1 ⟩

  progress with U32.add_bv_spec as ⟨ res2 ⟩

  progress as ⟨ res3, _, hres3bv ⟩
  have : res3 = 0#u32 := by
    have := mont_reduce_no_divide_bv_spec a b bMont res2 (by simp [*]) (by simp [*])
    simp at this
    simp [U32.eq_equiv_bv_eq, hres3bv, this]
  progress

  progress as ⟨ res4, hRes4 ⟩
  simp at hRes4

  -- Here we need to use the fact that we performed a Montgomery multiplication to get
  -- the bounds and the rest
  have hMontReduce :=
    mont_reduce_bv_spec a b bMont res2 res4 (by omega) (by omega) (by simp [*])
      (by simp[*]) (by simp[*])

  progress with ntt.SymCryptMlKemModSub'_sub_Q_spec as ⟨ res4, hRes4Eq, hRes4Bound ⟩
  simp at hRes4Bound

  simp [hRes4Eq, hRes4Bound]
  simp [hMontReduce]
  -- TODO: why does (3329 : ZMod 3329) doesn't get simplified?
  have : (3329 : ZMod 3329) = 0 := by rfl
  simp [this, U16.size, U16.numBits]
  rfl

theorem ntt.MlKemZetaBitRevTimesR_map_val_eq :
  List.map UScalar.val ntt.MlKemZetaBitRevTimesR.val =
  List.map (fun i => (17^bitRev 7 i * 2^16) % 3329) (List.range' 0 128) := by
  native_decide

theorem ntt.MlKemZetaBitRevTimesR_map_all_eq :
  List.all ntt.MlKemZetaBitRevTimesR.val (fun x => x.val < 3329) := by
  native_decide

theorem ntt.MlKemZetaBitRevTimesRTimesNegQInvModR_map_val_eq :
  List.map UScalar.val ntt.MlKemZetaBitRevTimesRTimesNegQInvModR.val =
  List.map (fun i => (((17^bitRev 7 i * 2^16) % 3329) * 3327) %  2^16) (List.range' 0 128) := by
  native_decide

-- TODO: generalize and move
@[simp]
theorem List.getElem!_range' (i start n: ℕ) :
  (List.range' start n)[i]! = if i < n then start + i else 0 := by
  revert start i
  induction n <;> intro i start
  . simp
  . rename_i n hInd
    unfold List.range'
    dcases i
    . simp
    . rename_i i
      have := hInd i (start + 1)
      simp [this]
      simp_all
      ring_nf

theorem array_map_eq_range'_all_imp_index_usize_eq_pred {α β} [Inhabited α] {a : Std.Array α n}
  {f : α → β} {g : ℕ → β} {p : α → Bool}
  (hEq : List.map f a = List.map g (List.range' 0 n.val))
  (hPred : List.all a p)
  (i : Usize) (h : i.val < n.val) :
  ∃ v, Array.index_usize a i = ok v ∧
  f v = g i.val ∧ p v := by
  let rec aux1 (l : List α) (i : Nat) (hi : i < l.length) (start : Nat)
            (hEq : List.map f l = List.map g (List.range' start l.length)) :
            f (l[i]!) = g (start + i) := by
    match l with
    | [] =>  simp at hi
    | hd :: l =>
      simp at hEq
      simp [List.range'] at hEq
      dcases i
      . simp at *
        simp [hEq]
      . rename_i i
        simp at hi
        simp [hi]
        have := aux1 l i hi (start + 1) (by simp [hEq])
        simp_all
        ring_nf

  progress as ⟨ v, hv ⟩
  rw [hv]
  have h := aux1 a i.val (by scalar_tac) 0 (by simp[hEq])
  simp at h
  simp [h]

  let rec aux2 (l : List α) (i : Nat) (hi : i < l.length) (start : Nat)
            (hPred : List.all l p) :
            p (l[i]!) := by
    match l with
    | [] =>  simp at hi
    | hd :: l =>
      dcases i
      . simp at *
        simp [hPred]
      . rename_i i
        simp at hi
        simp [hi]
        simp at hPred
        have := aux2 l i hi (start + 1) (by simp; tauto)
        simp_all
  have := aux2 a i.val (by scalar_tac) 0 (by simp[hPred])
  apply this

theorem array_map_eq_range'_imp_index_usize_eq {α β} [Inhabited α] {a : Std.Array α n}
  {f : α → β} {g : ℕ → β}
  (hEq : List.map f a = List.map g (List.range' 0 n.val))
  (i : Usize) (h : i.val < n.val) :
  ∃ v, Array.index_usize a i = ok v ∧
  f v = g i.val := by
  have hPred : List.all a.val (fun _ => true) := by simp
  progress with array_map_eq_range'_all_imp_index_usize_eq_pred
  simp [*]

@[progress]
theorem ntt.MlKemZetaBitRevTimesR_index_spec (k : Usize) (h : k.val < 128) :
  ∃ v, Array.index_usize ntt.MlKemZetaBitRevTimesR k = ok v ∧
  (v.val : ZMod Spec.Q) = Spec.ζ^(bitRev 7 k.val) * 65536 ∧
  v.val < 3329
  := by
  have := array_map_eq_range'_all_imp_index_usize_eq_pred ntt.MlKemZetaBitRevTimesR_map_val_eq ntt.MlKemZetaBitRevTimesR_map_all_eq
  progress as ⟨ v, hv, hv' ⟩
  simp at hv'
  simp only [hv']
  simp [hv]
  simp [Spec.ζ]
  simp [ZMod.intCast_mod']

@[progress]
theorem ntt.MlKemZetaBitRevTimesRTimesNegQInvModR_index_spec' (k : Usize) (h : k.val < 128) :
  ∃ v, Array.index_usize ntt.MlKemZetaBitRevTimesRTimesNegQInvModR k = ok v ∧
  BitVec.ofNat 32 v.val = (BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329) * 3327#32) &&& 65535#32
  := by
  have := array_map_eq_range'_imp_index_usize_eq ntt.MlKemZetaBitRevTimesRTimesNegQInvModR_map_val_eq
  progress as ⟨ v, hv ⟩
  simp only [bv_and_65535_eq_mod]
  zify
  rw [hv]
  simp

def to_poly (a : Array U16 256#usize) : Spec.Polynomial :=
  ⟨ List.map (fun x => (x.val : Spec.Zq)) a.val, by simp ⟩

@[simp]
theorem index_to_poly (a : Array U16 256#usize) (i : ℕ) :
  (to_poly a)[i]! = ((a.val[i]!) : Spec.Zq) := by
  simp [to_poly]

@[simp]
theorem to_poly_update (a : Array U16 256#usize) (i : Usize) (x : U16) :
  to_poly (Std.Array.set a i x) = Spec.Polynomial.set (to_poly a) i.val (x.val : Spec.Zq) := by
  sorry

-- TODO: generalize
--@[simp] theorem core.convert.num.FromU32U16.val_from_eq x : (core.convert.num.FromU32U16.from x).val = x.val := by rfl

attribute [local simp] Spec.Polynomial.set Spec.Polynomial.get!
attribute [-simp] List.getElem!_eq_getElem?_getD

@[simp]
theorem to_poly_get!_eq (a : Array U16 256#usize) (i : Nat) :
  (to_poly a)[i]! = ((a.val)[i]!.val : Spec.Zq) := by
  simp [to_poly, Spec.Polynomial.get!, getElem!]
  sorry

@[local simp]
theorem mod_3329_mod_4294967296_eq (x : Int) :
  x % 3329 % 4294967296 = x % 3329 := by
  apply Int.emod_eq_of_lt <;> omega

@[progress]
theorem ntt.SymCryptMlKemMontMul_twiddle_spec (k : Usize) (c : U32) (twiddleFactor : U32) (twiddleFactorMont : U32)
  (hc : c.val < Spec.Q) (hb : twiddleFactor.val < Spec.Q)
  (htf : twiddleFactor.bv = BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329))
  (htfMont : twiddleFactorMont.bv = (twiddleFactor.bv * 3327#32) &&& 65535#32) :
  ∃ (d : U32), ntt.SymCryptMlKemMontMul c twiddleFactor twiddleFactorMont = ok d ∧
  (d.val : Spec.Zq) = (c.val : Spec.Zq) * (Spec.ζ^(bitRev 7 k.val)) ∧
  d.val < Spec.Q := by
  progress as ⟨ d, hEq, hLt ⟩
  simp at htfMont
  natify at htf; simp at htf
  natify at htfMont; simp at htfMont
  simp [*]
  ring_nf
  simp [Spec.ζ]
  have : 17 ^ bitRev 7 ↑k * 65536 % 3329 % 4294967296 = 17 ^ bitRev 7 ↑k * 65536 % 3329 := by
    scalar_tac
  rw [this]; clear this
  simp
  have : (c.val : Spec.Zq) * (17 ^ bitRev 7 ↑k * 65536) * 65536⁻¹ =
          (c.val : Spec.Zq) * 17 ^ bitRev 7 k.val * (65536⁻¹ * 65536) := by ring_nf
  rw [this]; clear this
  have : (65536⁻¹ : Spec.Zq) * (65536 : Spec.Zq) = 1 := by native_decide
  rw [this]
  simp

set_option maxHeartbeats 2000000

/-@[simp]
theorem List.set_get!_eq_set [Inhabited α] (l : List α) (i : Nat) (x : α) (h : i < l.length):
  (l.set i x)[i]! = x := by simp [*]-/

-- TODO: make the inequality check more robust
@[simp]
theorem List.set_getElem!_eq_getElem! [Inhabited α] (l : List α) (i j : Nat) (x : α) (h : i ≠ j):
  (l.set i x)[j]! = l[j]! := by sorry

-- TODO: U32.val should give a ℕ, not an ℤ (and the spec for sub should be: ∃ z, x - y = ok z ∧ x.val = y.val + z.val)

def wfArray {n} (a : Array U16 n) : Prop :=
  ∀ i, i < n.val → a.val[i]!.val < 3329

-- TODO: local attribute for progress
theorem wfArray_update {n : Usize} (v : Std.Array U16 n) (i : Usize) (x : U16)
  (hbound : i.val < v.length)
  (hx : x.val < 3329)
  (hWf : wfArray v) :
  ∃ nv, v.update i x = ok nv ∧ nv = v.set i x ∧
  wfArray nv := by
  progress as ⟨ nv, hnv ⟩
  simp [wfArray] at *
  simp [hnv, toResult]
  intro j hj
  dcases hLt : j = i.val <;> simp [*]

theorem wfArray_index {n : Usize} (v : Std.Array U16 n) (i : Usize)
  (hbound : i.val < v.length)
  (hWf : wfArray v) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! ∧ x.val < 3329 := by
  progress as ⟨ x ⟩
  simp [wfArray] at hWf
  simp [*]
  replace hWf := hWf i.val (by scalar_tac)
  scalar_tac

/-!
NTT
-/

-- TODO: generalize and move
attribute [scalar_tac_simp] core.convert.num.FromU32U16.from_val_eq

-- TODO: cast simp lemmas

-- TODO: progress is too slow, probably because of scalar_tac
-- TODO: termination_by is too slow
@[progress]
def ntt.SymCryptMlKemPolyElementNTTLayerC.inner_loop_loop_spec
  (peSrc : Array U16 256#usize) (k : Usize) (len : Usize) (start : Usize)
  (twiddleFactor : U32) (twiddleFactorMont : U32) (j : Usize)
  (hStart : start.val + 2 * len.val ≤ 256)
  (hjLe : j.val ≤ len.val)
  (htf : twiddleFactor.bv = BitVec.ofNat 32 (17 ^ bitRev 7 k.val * 65536 % 3329))
  (htfBound : twiddleFactor.val < 3329)
  (htfMont : twiddleFactorMont.bv = (BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329) * 3327#32) &&& 65535#32)
  -- TODO: use get notations
  (hBounds : wfArray peSrc)
  :
  ∃ peSrc', inner_loop_loop peSrc len start twiddleFactor twiddleFactorMont j = ok peSrc' ∧
  to_poly peSrc' = SpecAux.nttLayerInner (to_poly peSrc) k.val len.val start.val j.val ∧
  wfArray peSrc' := by

  rw [inner_loop_loop]
  dcases hjLt : ¬ j < len <;> simp [hjLt]
  . unfold SpecAux.nttLayerInner
    have : ¬ j.val < len.val := by scalar_tac
    simp only [this]; clear this
    simp [*]
  . progress as ⟨ start_j, h_start_j ⟩
    progress with wfArray_index as ⟨ c0 ⟩

    -- assert
    have hc0Bound := hBounds start_j.val (by scalar_tac)
    progress

    progress as ⟨ start_j_len, h_start_j_len ⟩
    progress with wfArray_index as ⟨ c1 ⟩

    -- assert
    have hc1Bound := hBounds start_j_len.val (by scalar_tac)
    progress

    -- TODO: progress triggers as "maximum recursion depth has been reached"
    have ⟨ c1TimesTwiddle, hEq, hC1TimesTwiddle ⟩ :=
      ntt.SymCryptMlKemMontMul_twiddle_spec k (core.convert.num.FromU32U16.from c1) twiddleFactor twiddleFactorMont
        (by simp; scalar_tac) htfBound htf (by simp[htf, htfMont])
    simp [hEq]; clear hEq

    progress with SymCryptMlKemModSub'_spec as ⟨ c1' ⟩

    progress as ⟨ c0' ⟩

    progress as ⟨ c0'', hc0'' ⟩
    have : c0''.val = c0'.val := by scalar_tac
    clear hc0''
    progress with wfArray_update as ⟨ peSrc1, hPeSrc1 ⟩
    progress as ⟨ c1'', hc1'' ⟩
    have : c1''.val = c1'.val := by scalar_tac
    clear hc1''
    progress with wfArray_update as ⟨ peSrc2, hPeSrc2 ⟩

    progress as ⟨ j1 ⟩

    progress as ⟨ peSrc3, hPeSrc3 ⟩

    -- The postcondition
    unfold SpecAux.nttLayerInner
    have : j.val < len.val := by scalar_tac
    simp only [this]; clear this
    simp [hPeSrc1, hPeSrc2, hPeSrc3]
    simp [*]
termination_by len.val - j.val
decreasing_by scalar_decr_tac

#check ZMod_int_cast_eq_int_cast_iff

-- TODO: move
theorem ZMod_nat_cast_eq_nat_cast_iff (n : ℕ) (a b : ℕ) :
  ((a : ZMod n) = (b : ZMod n)) ↔ (a % n = b % n) := by
  zify
  have := ZMod_int_cast_eq_int_cast_iff n a b
  simp at this
  apply this

-- TODO: private attribute for all the auxiliary theorems
-- TODO: extract_minimized_goal
private theorem convert_twiddleFactor_eq
  (k : Usize)
  (twiddleFactor : U16)
  (hft : twiddleFactor.val = Spec.ζ ^ bitRev 7 k.val * 65536)
  (hftBound : twiddleFactor.val < 3329) :
  (core.convert.num.FromU32U16.from twiddleFactor).bv = BitVec.ofNat 32 (17 ^ bitRev 7 k.val * 65536 % 3329)
  := by
  natify at *
  simp at *
  have : twiddleFactor.val % 3329 = twiddleFactor.val := by
    apply Nat.mod_eq_of_lt; scalar_tac
  rw [this] at hft; clear this
  rw [hft]

  have : 17 ^ bitRev 7 ↑k * 65536 % 3329 % 4294967296 =
         17 ^ bitRev 7 ↑k * 65536 % 3329 := by
    scalar_tac
  rw [this]; clear this

  rw [← ZMod_nat_cast_eq_nat_cast_iff]
  simp [Spec.ζ]

theorem ntt.SymCryptMlKemPolyElementNTTLayerC_loop_spec
  -- Some ghost values
  (layer : ℕ) -- the layer
  (hLayer : layer < 7)
  (step : ℕ) -- the current step inside the layer (i.e., the number of times we incremented `start`)
  (hStep : step ≤ 2^layer)
  --
  (peSrc : Array U16 256#usize)
  (k : Usize) (len : Usize) (start : Usize)
  (hWf : wfArray peSrc)
  (hk : k.val = 2^layer + step)
  (hStart : start.val = 2 * len.val * step)
  (hLen : len.val = 2^(7-layer))
  :
  ∃ peSrc', SymCryptMlKemPolyElementNTTLayerC_loop peSrc k len start = ok peSrc' ∧
  to_poly peSrc' = SpecAux.nttLayer (to_poly peSrc) k.val len.val start.val (by simp [hLen]) ∧
  wfArray peSrc'
  := by
  rw [SymCryptMlKemPolyElementNTTLayerC_loop]
  dcases hLt: ¬ start < 256#usize <;> simp only [hLt] <;> simp
  . unfold SpecAux.nttLayer
    have : ¬ start.val < 256 := by scalar_tac
    simp only [this]; simp [*]
  . -- Getting those arithmetic facts is actually non trivial
    have : 2^layer ≤ 2^6 := by apply Nat.pow_le_pow_of_le <;> omega
    have : step < 2^layer := by
      have : ¬ step = 2^layer := by
        intro hContra
        simp [hContra] at hStart
        simp [hLen] at hStart
        simp [Nat.mul_assoc] at hStart
        rw [← Nat.pow_add] at hStart
        have : 7 - layer + layer = 7 := by omega
        rw [this] at hStart; clear this
        simp at hStart
        scalar_tac
      omega
    have : start.val + 2 * len.val ≤ 256 := by
      simp [hLen, hStart]
      have :=
        calc
          2 * 2 ^ (7 - layer) * step + 2 * 2 ^ (7 - layer)
          = (2 * 2^(7 - layer)) * (step + 1) := by ring_nf
          _ ≤ (2 * 2^(7 - layer)) * 2^layer := by apply Nat.mul_le_mul <;> omega
          _ = 2 * (2^(7 - layer) * 2^layer) := by ring_nf
          _ = 2 * 2 ^ (7 - layer + layer) := by rw [← Nat.pow_add]
          _ = 2 * 2 ^ 7 := by
            have : 7 - layer + layer = 7 := by omega
            rw [this]
      omega
    have : k.val < 128 := by
      rw [hk]
      have : 2^layer ≤ 2^6 := by apply Nat.pow_le_pow_of_le <;> omega
      simp at *
      have : step < 2^6 := by
        have := @Nat.pow_le_pow_of_le 2 layer 6 (by simp) (by omega)
        omega
      scalar_tac

    /- TODO: progress fails here
       `progress` attempts to use assumption `hLen : ↑len = 2 ^ (7 - layer)` (!?)
       and it causes issues because the term in the goal is:
       `MlKemZetaBitRevTimesR.index_usize k`
       We should:
       1. fix the assumption matching to only match the relevant assumptions (we should check
          the type!)
       2. mark the constant bodies as irreducible
    -/
    progress as ⟨ twiddleFactor, hft, hftBound ⟩
    progress as ⟨ twiddleFactorMont, hftMont ⟩
    progress as ⟨ k', hk' ⟩

    have : (core.convert.num.FromU32U16.from twiddleFactor).bv =
           BitVec.ofNat 32 (17 ^ bitRev 7 k.val * 65536 % 3329) :=
      convert_twiddleFactor_eq k twiddleFactor hft hftBound
    progress as ⟨ peSrc1, _, hPeSrc1 ⟩

    progress as ⟨ twoLen, hTwoLen ⟩
    progress as ⟨ start', hStart' ⟩

    have : k'.val ≤ 128 := by scalar_tac

    have : start'.val = 2 * len.val * (step + 1) := by
      ring_nf
      simp [hStart', hTwoLen]
      -- TODO: those facts are annoying
      have : start.val + 2 * len.val = start.val + 2 * len.val := by scalar_tac
      rw [this]
      simp [hStart]
      ring_nf
    have := ntt.SymCryptMlKemPolyElementNTTLayerC_loop_spec layer hLayer (step + 1) (by scalar_tac)

    progress as ⟨ peSrc2, hPeSrc2 ⟩

    -- Proving the post-condition
    unfold SpecAux.nttLayer
    have hLt : start.val < 256 := by scalar_tac
    simp only [hLt]; simp
    simp [hPeSrc2, hPeSrc1, hk', hTwoLen, hStart']
    simp [*]
termination_by 256 - k.val
decreasing_by scalar_decr_tac


-- TODO: scalar_tac fails with `maximum recursion depth reached`
-- TODO: we need to guard against the looping equalities
example (peSrc : Std.Array U16 256#usize)
  (k len : Usize)
  (hWf : wfArray peSrc)
  (hk : k.val = 2 ^ k.val.log2 ∧ -- This is the problem
        k.val.log2 < 7)
  :
  k.val.log2 ≤ 7 := by
  set_option trace.ScalarTac true in
  scalar_tac

example (peSrc : Std.Array U16 256#usize)
  (k len : Usize)
  (hWf : wfArray peSrc)
  (hk : k.val = 2 ^ k.val.log2 ∧ k.val.log2 < 7)
  (hLen : len.val = 128 / k.val)
  (hLenPos : 0 < len.val) :
  k.val.log2 ≤ 7 := by
  set_option trace.ScalarTac true in
  scalar_tac

-- TODO: extract_goal fails
example (i j : Nat) (h : i ≤ 7) :
  let j := i
  j ≤ 7 := by
  intro j
  extract_goal
  omega


set_option maxRecDepth 1000 in
@[progress]
theorem ntt.SymCryptMlKemPolyElementNTTLayer_spec
  (peSrc : Array U16 256#usize)
  (k : Usize) (len : Usize)
  (hWf : wfArray peSrc)
  -- Putting many preconditions to get rid of the ghost while making sure `progress`
  -- goes through automatically
  (hk : 2^(k.val.log2) = k.val ∧ k.val.log2 < 7)
  (hLen : len.val = 128 / k.val)
  (hLenPos : 0 < len.val)
  :
  ∃ peSrc', SymCryptMlKemPolyElementNTTLayer peSrc k len = ok peSrc' ∧
  to_poly peSrc' = SpecAux.nttLayer (to_poly peSrc) k.val len.val 0 hLenPos ∧
  wfArray peSrc'
  := by
  let step := k.val.log2
  have : len.val = 2 ^ (7 - step) := by
    rw [hLen]
    rw [← hk.left]
    have :=
      calc 128 / 2^step = 2^7 / 2^step := by simp
           _ = 2^(7-step) := by rw [Nat.pow_div] <;> scalar_tac
    rw [this]
  have := ntt.SymCryptMlKemPolyElementNTTLayerC_loop_spec step (by scalar_tac) 0 (by simp)
  unfold SymCryptMlKemPolyElementNTTLayer
  progress as ⟨ peSrc1, hEq, hWf ⟩; clear this
  tauto

@[progress]
theorem ntt.SymCryptMlKemPolyElementNTT_spec (peSrc : Std.Array U16 256#usize)
  (hWf : wfArray peSrc) :
  ∃ peSrc1, SymCryptMlKemPolyElementNTT peSrc = ok peSrc1 ∧
  to_poly peSrc1 = Spec.ntt (to_poly peSrc) ∧ wfArray peSrc1
  := by
  unfold SymCryptMlKemPolyElementNTT
  progress as ⟨ peSrc1 ⟩; simp [Nat.log2]
  progress as ⟨ peSrc2 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc3 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc4 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc5 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc6 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc7 ⟩; try simp [Nat.log2]
  rw [← SpecAux.ntt_eq]
  unfold SpecAux.ntt
  simp [*]

/-!
INTT
-/

@[progress]
def ntt.SymCryptMlKemPolyElementINTTLayerC.inner_loop_loop_spec
  (peSrc : Array U16 256#usize) (k : Usize) (len : Usize) (start : Usize)
  (twiddleFactor : U32) (twiddleFactorMont : U32) (j : Usize)
  (hStart : start.val + 2 * len.val ≤ 256)
  (hjLe : j.val ≤ len.val)
  (htf : twiddleFactor.bv = BitVec.ofNat 32 (17 ^ bitRev 7 k.val * 65536 % 3329))
  (htfBound : twiddleFactor.val < 3329)
  (htfMont : twiddleFactorMont.bv = (BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329) * 3327#32) &&& 65535#32)
  -- TODO: use get notations
  (hBounds : wfArray peSrc)
  :
  ∃ peSrc', inner_loop_loop peSrc len start twiddleFactor twiddleFactorMont j = ok peSrc' ∧
  to_poly peSrc' = SpecAux.invNttLayerInner (to_poly peSrc) k.val len.val start.val j.val ∧
  wfArray peSrc' := by

  rw [inner_loop_loop]
  dcases hjLt : ¬ j < len <;> simp [hjLt]
  . unfold SpecAux.invNttLayerInner
    have : ¬ j.val < len.val := by scalar_tac
    fsimp only [this]; clear this
    fsimp [*]
  . progress as ⟨ start_j, h_start_j ⟩
    progress with wfArray_index as ⟨ c0, hc0 ⟩

    -- assert
    have hc0Bound := hBounds start_j.val (by scalar_tac)
    progress

    progress as ⟨ start_j_len, h_start_j_len ⟩
    progress with wfArray_index as ⟨ c1, hc1 ⟩

    -- assert
    have hc1Bound := hBounds start_j_len.val (by scalar_tac)
    progress

    progress with SymCryptMlKemModAdd'_spec as ⟨ tmp, htmp ⟩
    progress with SymCryptMlKemModSub'_spec as ⟨ c1', hc1' ⟩

    -- TODO: progress triggers as "maximum recursion depth has been reached"
    have ⟨ c1'', hEq, hc1'' ⟩ :=
      ntt.SymCryptMlKemMontMul_twiddle_spec k c1' twiddleFactor twiddleFactorMont
        (by fsimp; scalar_tac) htfBound htf (by fsimp[htf, htfMont])
    fsimp [hEq]; clear hEq

    progress as ⟨ tmp_u16, h_tmp_u16 ⟩

    have : tmp_u16.val < 3329 := by scalar_tac -- TODO
    progress with wfArray_update as ⟨ peSrc1, hPeSrc1 ⟩
    progress as ⟨ c1''_u16, hc1''_u16 ⟩
    have : c1''_u16.val < 3329 := by scalar_tac -- TODO
    progress with wfArray_update as ⟨ peSrc2, hPeSrc2 ⟩

    progress as ⟨ j1, hj1 ⟩

    progress as ⟨ peSrc3, hPeSrc3, hWfPeSrc3 ⟩

    -- The postcondition
    unfold SpecAux.invNttLayerInner

    let c0s := (to_poly peSrc)[start.val + j.val]!;
    let c1s := (to_poly peSrc)[start.val + j.val + len.val]!;
    let zetas := Spec.ζ ^ bitRev 7 k.val;
    let f1 := (to_poly peSrc).set (start.val + j.val) (c0s + c1s);
    let f2 := f1.set (start.val + j.val + len.val) (zetas * (c1s - c0s));
    let f3 := SpecAux.invNttLayerInner f2 k.val len.val start.val (j.val + 1)

    have : (UScalar.cast UScalarTy.U16 tmp).val = tmp.val := by scalar_tac -- TODO: fix this
    have : (UScalar.cast UScalarTy.U16 c1'').val = c1''.val := by scalar_tac -- TODO: fix this
    have hf1_eq : f1 = to_poly peSrc1 := by
      unfold f1
      fsimp [hPeSrc1, h_start_j, h_tmp_u16, htmp]
      fsimp +zetaDelta [*]
    have hf2_eq : f2 = to_poly peSrc2 := by
      unfold f2
      fsimp [hPeSrc2, hf1_eq, h_start_j_len, h_start_j, hc1''_u16, hc1'', hc1']
      have : zetas * (c1s - c0s) = (↑↑c1 - ↑↑c0) * Spec.ζ ^ bitRev 7 k.val := by
        unfold c0s c1s zetas
        fsimp [hc0, hc1]
        ring_nf
        fsimp [*]
      fsimp [*]
    have hf3_eq : f3 = to_poly peSrc3 := by
      unfold f3
      fsimp [hPeSrc3, hj1, hf2_eq]

    have : j.val < len.val := by scalar_tac
    fsimp only [this]; clear this
    fsimp +zetaDelta at hf3_eq
    fsimp +zetaDelta [hf3_eq, hWfPeSrc3]
termination_by len.val - j.val
decreasing_by scalar_decr_tac

theorem ntt.SymCryptMlKemPolyElementINTTLayerC_loop_spec
  -- Some ghost values
  (layer : ℕ) -- the layer
  (hLayer : layer < 7)
  (step : ℕ) -- the current step inside the layer (i.e., the number of times we decremented `start`)
  (hStep : step ≤ 2^(6-layer))
  --
  (peSrc : Array U16 256#usize)
  (k : Usize) (len : Usize) (start : Usize)
  (hWf : wfArray peSrc)
  (hk : k.val + 1 = 2^(7 - layer) - step)
  (hStart : start.val = 2 * len.val * step)
  (hLen : len.val = 2^(layer + 1))
  :
  ∃ peSrc', SymCryptMlKemPolyElementINTTLayerC_loop peSrc k len start = ok peSrc' ∧
  to_poly peSrc' = SpecAux.invNttLayer (to_poly peSrc) k.val len.val start.val (by fsimp [hLen]) ∧
  wfArray peSrc'
  := by
  rw [SymCryptMlKemPolyElementINTTLayerC_loop]
  dcases hLt: ¬ start < 256#usize <;> simp only [hLt] <;> simp
  . unfold SpecAux.invNttLayer
    have : ¬ start.val < 256 := by scalar_tac
    fsimp only [this]; fsimp [*]
  . -- Getting those arithmetic facts is actually non trivial - TODO: factor out
    have : 2^layer ≤ 2^6 := by apply Nat.pow_le_pow_of_le <;> omega
    have : step < 2^(6 - layer) := by
      have : ¬ step = 2^(6 - layer) := by
        intro hContra
        fsimp [hLen] at hStart
        fsimp [hContra] at hStart
        fsimp [Nat.mul_assoc] at hStart
        rw [← Nat.pow_add] at hStart
        have : layer + 1 + (6 - layer) = 7 := by omega
        rw [this] at hStart; clear this
        fsimp at hStart
        scalar_tac
      omega
    have : start.val + 2 * len.val ≤ 256 := by
      fsimp [hLen, hStart]
      have :=
        calc
          2 * 2 ^ (layer + 1) * step + 2 * 2 ^ (layer + 1)
          = (2 * 2^(layer + 1)) * (step + 1) := by ring_nf
          _ ≤ (2 * 2^(layer + 1)) * 2^(6 - layer):= by apply Nat.mul_le_mul <;> omega
          _ = 2 * (2^(layer + 1) * 2^(6 - layer)) := by ring_nf
          _ = 2 * 2 ^ (layer + 1 + (6 - layer)) := by rw [← Nat.pow_add]
          _ = 2 * 2 ^ 7 := by
            have : layer + 1 + (6 - layer) = 7 := by omega
            rw [this]
      omega
    have : k.val < 128 := by
      suffices k.val + 1 ≤ 128 by omega
      rw [hk]
      have : 2^(7 - layer) ≤ 2^7 := by apply Nat.pow_le_pow_of_le <;> omega
      fsimp at *
      have : step < 2^6 := by
        have := @Nat.pow_le_pow_of_le 2 (6 - layer) 6 (by fsimp) (by omega)
        omega
      scalar_tac
    have : 0 < k.val := by
      have : k.val ≠ 0 := by
        intro hContra
        fsimp [hContra] at *
        have : 2 ^ (7 - layer) = 2 * 2 ^ (6 - layer) := by
          have : 7 - layer = (6 - layer) + 1 := by omega
          rw [this]
          rw [Nat.pow_add_one]
          ring_nf
        omega
      omega

    progress as ⟨ twiddleFactor, hft, hftBound ⟩
    progress as ⟨ twiddleFactorMont, hftMont ⟩
    progress as ⟨ k', hk' ⟩

    -- Recursive call
    have hRec := ntt.SymCryptMlKemPolyElementINTTLayerC_loop_spec layer hLayer (step + 1) (by omega)
    unfold SymCryptMlKemPolyElementINTTLayerC.inner_loop -- TODO: add the reducible attribute

    have : (core.convert.num.FromU32U16.from twiddleFactor).bv =
           BitVec.ofNat 32 (17 ^ bitRev 7 k.val * 65536 % 3329) :=
      convert_twiddleFactor_eq k twiddleFactor hft hftBound
    progress as ⟨ peSrc1, _, hPeSrc1 ⟩

    progress as ⟨ twoLen, hTwoLen ⟩
    progress as ⟨ start', hStart' ⟩

    have : start'.val = 2 * len.val * (step + 1) := by
      ring_nf
      fsimp [hStart', hTwoLen, hStart]
      ring_nf

    progress as ⟨ peSrc2, hPeSrc2 ⟩

    -- Proving the post-condition
    unfold SpecAux.invNttLayer
    have hLt : start.val < 256 := by scalar_tac
    fsimp only [hLt]; fsimp
    fsimp [hPeSrc2, hPeSrc1, hk', hTwoLen, hStart']
    fsimp [*]

@[progress]
theorem ntt.SymCryptMlKemPolyElementINTTLayer_spec
  (peSrc : Array U16 256#usize)
  (k : Usize) (len : Usize)
  (hWf : wfArray peSrc)
  -- Putting many preconditions to get rid of the ghost while making sure `progress`
  -- goes through automatically
  (hLen : 2^(len.val.log2) = len.val ∧ 1 ≤ len.val.log2 ∧ len.val.log2 ≤ 7)
  (hk : k.val + 1 = 256 / len.val)
  (hLenPos : 0 < len.val)
  :
  ∃ peSrc', SymCryptMlKemPolyElementINTTLayer peSrc k len = ok peSrc' ∧
  to_poly peSrc' = SpecAux.invNttLayer (to_poly peSrc) k.val len.val 0 hLenPos ∧
  wfArray peSrc'
  := by
  let step := len.val.log2 - 1
  have : k.val + 1 = 2 ^ (7 - step) := by
    rw [hk]
    rw [← hLen.left]
    have :=
      calc 256 / 2^len.val.log2 = 2^8 / 2^len.val.log2 := by simp [step]
           _ = 2^(8-len.val.log2) := by rw [Nat.pow_div] <;> scalar_tac
    rw [this]
    simp [step]
    scalar_tac
  have := ntt.SymCryptMlKemPolyElementINTTLayerC_loop_spec step (by scalar_tac) 0 (by simp)
  unfold SymCryptMlKemPolyElementINTTLayer
  have : len.val = 2 ^ (len.val.log2 - 1 + 1) := by
    have : len.val.log2 - 1 + 1 = len.val.log2 := by omega
    rw [this]
    rw [hLen.left]
  progress as ⟨ peSrc1, hEq, hWf ⟩
  tauto

-- TODO: move
@[simp] theorem ntt.MLWE_POLYNOMIAL_COEFFICIENTS_eq : ntt.MLWE_POLYNOMIAL_COEFFICIENTS.val = 256 := by
  -- TODO: why does rfl fail here?
  simp [ntt.MLWE_POLYNOMIAL_COEFFICIENTS, toResult, MLWE_POLYNOMIAL_COEFFICIENTS_body, eval_global]

@[simp] theorem ntt.INTTFixupTimesRsqr_eq : ntt.INTTFixupTimesRsqr.val = 1441 := by rfl
@[simp] theorem ntt.INTTFixupTimesRsqr_bv_eq : ntt.INTTFixupTimesRsqr.bv = 1441#32 := by rfl

@[simp] theorem ntt.INTTFixupTimesRsqrTimesNegQInvModR_bv_eq : INTTFixupTimesRsqrTimesNegQInvModR.bv = 10079#32 := by rfl

@[progress]
theorem ntt.SymCryptMlKemPolyElementINTTAndMulR_loop_spec_aux
  (peSrc : Std.Array U16 256#usize) (i : Usize)
  (hi : i.val ≤ 256) (hWf : wfArray peSrc) :
  ∃ peSrc', ntt.SymCryptMlKemPolyElementINTTAndMulR_loop peSrc i = ok peSrc' ∧
  (∀ (j : Nat), j < i.val → (to_poly peSrc')[j]! = (to_poly peSrc)[j]!) ∧
  (∀ (j : Nat), i.val ≤ j → j < 256 →
    (to_poly peSrc')[j]! = (to_poly peSrc)[j]! * (3303 : Spec.Zq) * 2^16) ∧
  wfArray peSrc' := by
  rw [SymCryptMlKemPolyElementINTTAndMulR_loop]
  simp
  split <;> rename_i h
  . progress with wfArray_index as ⟨ x ⟩
    progress with ntt.SymCryptMlKemMontMul_spec as ⟨ xTimes ⟩
    progress as ⟨ xTimes', hxTimes' ⟩
    have : xTimes'.val = xTimes.val := by scalar_tac -- TODO
    clear hxTimes'
    progress with wfArray_update as ⟨ peSrc1, hPeSrc1 ⟩
    progress as ⟨ i1 ⟩
    progress as ⟨ peSrc2, h1, h2 ⟩
    split_conjs
    . intro j hj
      fsimp [Array.update] at *
      have := h1 j (by omega)
      rw [this]; clear this
      fsimp [*]
    . intro j hj0 hj1
      simp at *
      dcases hij : j = i.val
      . have := h1 j (by scalar_tac)
        rw [this]; clear this
        have : i.val < peSrc.val.length := by scalar_tac
        fsimp [*]
        -- TODO: reduceZMod
        have : ((2^16)⁻¹ : ZMod 3329) = 169 := by native_decide
        rw [this]; clear this
        ring_nf
        -- Here again, we want to reduce ZMod
        rfl
      . have hij' : i1.val ≤ j := by scalar_tac
        have := h2 j (by scalar_tac) (by scalar_tac)
        fsimp [this, hPeSrc1]
        simp [hij]
    . simp [*]
  . have : i.val = 256 := by scalar_tac
    fsimp [*]
    intro j hj0 hj1
    -- Contradiction
    omega
termination_by 256 - i.val
decreasing_by scalar_decr_tac

-- TODO: move up
@[simp]
theorem to_poly_getElem!_eq (a : Std.Array U16 256#usize) (i : Nat) :
  (to_poly a)[i]! = a.val[i]! := by
  simp [to_poly]
  simp [getElem!, decidableGetElem?]
  conv => lhs; simp only [getElem, Spec.Polynomial.get!]
  simp [getElem!, decidableGetElem?]
  dcases h: i < 256 <;> simp [h]
  rfl

-- TODO: move
@[simp]
theorem getElem!_cons_succ [Inhabited α] (hd : α) (tl : List α) (i : Nat) :
  getElem! (hd :: tl) (i + 1) = getElem! tl i := by
  simp [getElem!, decidableGetElem?]

@[simp]
theorem getElem!_cons_zero [Inhabited α] (hd : α) (tl : List α) :
  getElem! (hd :: tl) 0 = hd := by
  simp [getElem!, decidableGetElem?]

@[progress]
theorem ntt.SymCryptMlKemPolyElementINTTAndMulR_loop_spec (peSrc : Std.Array U16 256#usize)
  (hWf : wfArray peSrc) :
  ∃ peSrc', ntt.SymCryptMlKemPolyElementINTTAndMulR_loop peSrc 0#usize = ok peSrc' ∧
  to_poly peSrc' = (to_poly peSrc) * (3303 : Spec.Zq) * (2^16 : Spec.Zq) ∧
  wfArray peSrc' := by
  progress as ⟨ peSrc', _, h ⟩
  simp [HMul.hMul, Spec.Polynomial.scalarMul, to_poly, *]

  have aux (f f' : List U16) (hLen : f'.length = f.length)
    (hEq : ∀ i, i < f.length → (f'[i]!.val : Spec.Zq) = f[i]!.val * 3303 * 2^16) :
    List.map (fun x => (x.val : Spec.Zq)) f' =
    List.map ((fun v => Mul.mul v (2^16 : Spec.Zq)) ∘ (fun v => Mul.mul v 3303) ∘ fun x => (x.val : Spec.Zq)) f := by
    revert f'; induction f
    . simp_all
    . rename_i hd tl hInd
      intro f' hLen hi
      dcases f'
      . simp at hLen
      . rename_i hd' tl'
        simp at *
        have := hInd tl' (by simp [*])
          (by
            intro i hLen
            have := hi (i + 1) (by omega)
            simp [hLen] at this
            apply this)
        simp [*]
        have := hi 0 (by omega)
        simp at this
        apply this

  rw [aux] <;> simp [*]
  simp at h
  apply h

@[progress]
theorem ntt.SymCryptMlKemPolyElementINTTAndMulR_spec (peSrc : Std.Array U16 256#usize)
  (hWf : wfArray peSrc) :
  ∃ peSrc1, SymCryptMlKemPolyElementINTTAndMulR peSrc = ok peSrc1 ∧
  to_poly peSrc1 = Spec.invNtt (to_poly peSrc) * (2^16 : Spec.Zq) ∧ wfArray peSrc1
  := by
  unfold SymCryptMlKemPolyElementINTTAndMulR
  progress as ⟨ peSrc1 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc2 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc3 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc4 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc5 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc6 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc7 ⟩; try simp [Nat.log2]
  progress as ⟨ peSrc8 ⟩
  rw [← SpecAux.invNtt_eq]
  unfold SpecAux.invNtt
  simp [*]

end Symcrust
