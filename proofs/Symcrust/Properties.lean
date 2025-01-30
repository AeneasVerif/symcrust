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

def ScalarTy.bitWidth (ty : ScalarTy) : Nat :=
  match ty with
  | Isize | Usize => size_num_bits
  | I8 | U8 => 8
  | I16 | U16 => 16
  | I32 | U32 => 32
  | I64 | U64 => 64
  | I128 | U128 => 128

@[simp] theorem ScalarTy.Isize_bitWidth : Isize.bitWidth = size_num_bits := by rfl
@[simp] theorem ScalarTy.I8_bitWidth : I8.bitWidth = 8 := by rfl
@[simp] theorem ScalarTy.I16_bitWidth : I16.bitWidth = 16 := by rfl
@[simp] theorem ScalarTy.I32_bitWidth : I32.bitWidth = 32 := by rfl
@[simp] theorem ScalarTy.I64_bitWidth : I64.bitWidth = 64 := by rfl
@[simp] theorem ScalarTy.I128_bitWidth : I128.bitWidth = 128 := by rfl
@[simp] theorem ScalarTy.Usize_bitWidth : Usize.bitWidth = size_num_bits := by rfl
@[simp] theorem ScalarTy.U8_bitWidth : U8.bitWidth = 8 := by rfl
@[simp] theorem ScalarTy.U16_bitWidth : U16.bitWidth = 16 := by rfl
@[simp] theorem ScalarTy.U32_bitWidth : U32.bitWidth = 32 := by rfl
@[simp] theorem ScalarTy.U64_bitWidth : U64.bitWidth = 64 := by rfl
@[simp] theorem ScalarTy.U128_bitWidth : U128.bitWidth = 128 := by rfl

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
def Scalar.bv_ {ty} (x : Scalar ty) : BitVec ty.bitWidth :=
  if ty.isSigned then BitVec.ofInt _ x.val else BitVec.ofNat _ x.toNat

def U8.bv (x : U8) : BitVec 8 := Scalar.bv_ x
def U16.bv (x : U16) : BitVec 16 := Scalar.bv_ x
def U32.bv (x : U32) : BitVec 32 := Scalar.bv_ x
def U64.bv (x : U64) : BitVec 64 := Scalar.bv_ x
def U128.bv (x : U128) : BitVec 128 := Scalar.bv_ x
def Usize.bv (x : Usize) : BitVec size_num_bits := Scalar.bv_ x
def I8.bv (x : I8) : BitVec 8 := Scalar.bv_ x
def I16.bv (x : I16) : BitVec 16 := Scalar.bv_ x
def I32.bv (x : I32) : BitVec 32 := Scalar.bv_ x
def I64.bv (x : I64) : BitVec 64 := Scalar.bv_ x
def I128.bv (x : I128) : BitVec 128 := Scalar.bv_ x
def Isize.bv (x : Isize) : BitVec size_num_bits := Scalar.bv_ x

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

-- TODO: scalar_tac_simp?
@[simp] theorem Int.mod_toNat_val (n m : Int) (h : m ≠ 0) :
  (n % m).toNat = n % m := by
  simp only [Int.ofNat_toNat, ne_eq, h, not_false_eq_true, Int.emod_nonneg, sup_of_le_left]

theorem core.num.Scalar.ShiftRight_val_unsigned_eq {ty0 ty1} (x : Scalar ty0) (y : Scalar ty1)
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
  := by apply core.num.Scalar.ShiftLeft_bv_unsigned_eq <;> simp_all

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
  (x &&& y).val = (x.bv &&& y.bv).toNat := by
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

#check Aeneas.Std.core.num.Scalar.ShiftRight_val_unsigned_eq

#check Scalar.eq_equiv

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
@[simp] theorem Usize.ofInt_bv (x : Int) h : Usize.bv (Usize.ofInt x h) = BitVec.ofNat _ x.toNat := by apply Scalar.ofIntCore_bv

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
  apply Int.emod_eq_of_lt <;> scalar_tac

-- TODO: improve scalar_tac to reason about inequalities between bitvectors?

theorem ntt.SymCryptMlKemMod'_spec (a : U32) (b : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) :
  ∃ (c : U32), ntt.SymCryptMlKemModAdd' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) + (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemModAdd'
  -- TODO: automate those
  have : a.bv < 3329#32 := by
    simp [U32.bv, Scalar.bv_]
    scalar_tac
  have : b.bv < 3329#32 := by
    simp [U32.bv, Scalar.bv_]
    scalar_tac
  simp at *
  progress
  progress
  progress with U32.add_bv_spec as ⟨ c1, hc1 ⟩
  progress as ⟨ c2, hc2 ⟩
  simp at *

  -- TODO: handle this properly with progress
  have hIf : (if c2 = 0#u32 then ok () else massert (c2 = 65535#u32)) = ok () := by
    split <;> try simp
    progress
    simp [U32.eq_equiv_bv_eq] at *
    bv_decide
  progress; clear hIf

  -- Prove the post-condition
  have hPost :
    let c := core.num.U32.wrapping_add (core.num.U32.wrapping_sub c1 3329#u32) (3329#u32 &&& c2)
    (c.val : Spec.Zq) = (a.val : Spec.Zq) + (b.val : Spec.Zq) ∧
    c.val < Spec.Q := by
    simp
    -- There are two cases depending on whether `a + b - q` is `< 0` or not
    dcases hlt : 0 ≤ a.val + b.val - 3329
    . -- No underflow
      -- TODO: automate
      have : 3329#32 ≤ a.bv + b.bv := by
        simp [BitVec.le_def]
        rw [Nat.mod_eq_of_lt] <;> omega

      -- The important part of the proof, that we prove with bv_decide
      have hc2Eq : c2.toNat = 0 := by -- TODO: automate
        have h : c2.bv = 0#32 := by bv_decide
        have h : c2.bv.toNat = 0 := by rw [h]; simp
        simp at h
        scalar_tac
      simp [hc2Eq]; clear hc2

      let c : Int := a.val + b.val - 3329
      have : 0 ≤ c ∧ c < 3329 := by scalar_tac
      have hcMod : c % (U32.max + 1) = c := by
        apply Int.emod_eq_of_lt <;> scalar_tac

      simp [*]
      rw [hcMod]
      simp +zetaDelta [Spec.Zq]
      split_conjs
      . rfl
      . scalar_tac
    . -- Underflow
      simp at hlt

      have : a.bv + b.bv < 3329#32 := by
        simp [BitVec.lt_def]
        rw [Nat.mod_eq_of_lt] <;> omega

      -- The important part of the proof, that we prove with bv_decide
      have hc2Eq : 3329 &&& c2.toNat = 3329 := by -- TODO: automate
        have h : 3329#32 &&& c2.bv = 3329#32 := by bv_decide
        have h : (3329#32 &&& c2.bv).toNat = 3329 := by
          simp [h]
        simp at h
        apply h
      simp [hc2Eq]; clear hc2

      split_conjs
      . simp [*]
      . scalar_tac

  -- Finish the proof
  progress
  . -- massert
    simp at hPost
    apply hPost.right
  . simp at *
    apply hPost

end Symcrust
