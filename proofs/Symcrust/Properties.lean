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

/-!
Addition modulo
-/
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

-- TODO: register those as `scalar_tac_simp`?
@[simp] theorem ntt.Q_eq : Q = 3329#u32 := by rfl
@[simp] theorem ntt.NegQInvModR_eq : ntt.NegQInvModR = 3327#u32 := by rfl
@[simp] theorem ntt.Rmask_eq : ntt.Rmask = 65535#u32 := by rfl
@[simp] theorem ntt.Rlog2_eq : ntt.Rlog2 = 16#u32 := by rfl

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

-- TODO: move
theorem ZMod.eq_iff_mod (p : ℕ) (x y : ZMod p) :
  x = y ↔ x.val = y.val := by
  sorry

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

set_option maxHeartbeats 500000

theorem Nat.eq_iff_intCast_eq (n m : Nat) : n = m ↔ (n : Int) = (m : Int) := by omega
theorem Nat.lt_iff_intCast_eq (n m : Nat) : n < m ↔ (n : Int) < (m : Int) := by omega
theorem Nat.le_iff_intCast_eq (n m : Nat) : n ≤ m ↔ (n : Int) ≤ (m : Int) := by omega

-- TODO: generalize
@[simp] theorem U32.zmod_val_eq_mod (n : Nat) (x : U32) : ZMod.val (x.val : ZMod n) = x.val % n := by sorry
@[simp] theorem U32.zmod_cast_int_eq_mod (n : Nat) (x : U32) : ZMod.cast (x.val : ZMod n) = x.val % n := by sorry

-- TODO: generalize
@[simp] theorem U32.val_max_zero_eq (x : U32) : x.val ⊔ 0 = x.val := by scalar_tac

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

-- TODO: move this example
example
  (a : U32)
  (b : U32)
  (c1 : U32)
  (hc1 : c1.val = ↑a + ↑b)
  (c2 : U32)
  (hEq : (c1.bv - 3329#32 + (3329#32 &&& c2.bv)) % 3329#32 = (a.bv + b.bv) % 3329#32)
  (hLt : c1.bv - 3329#32 + (3329#32 &&& c2.bv) < 3329#32) :
  (((c1.val - 3329 + ((3329 &&& c2.toNat) : Nat)) % (U32.max + 1 : Int)) : ZMod Spec.Q) = ↑↑a + ↑↑b ∧
  (c1.val - 3329 + ((3329 &&& c2.toNat) : Nat)) % (↑U32.max + 1) < 3329
  := by
  -- TODO: move
  zify at *
  simp [U32.max] at *
  norm_mod

  /- We can now prove the two post-conditions -/
  split_conjs
  . have hab : (a.val + b.val) % 4294967296 = a.val + b.val := by
      apply Int.emod_eq_of_lt <;> scalar_tac
    rw [hab] at hEq
    apply hEq
  . apply hLt

@[pspec]
theorem ntt.SymCryptMlKemModAdd'_spec (a : U32) (b : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) :
  ∃ (c : U32), ntt.SymCryptMlKemModAdd' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) + (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemModAdd'
  have : a.bv < 3329#32 := by -- TODO: bvfy?
    simp [U32.bv]
    scalar_tac
  have : b.bv < 3329#32 := by -- TODO: bvfy?
    simp [U32.bv]
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

  -- Prove the post-condition (we also need this prove that the assert holds)
  have hPost :
    let c := core.num.U32.wrapping_add (core.num.U32.wrapping_sub c1 3329#u32) (3329#u32 &&& c2)
    (c.val : Spec.Zq) = (a.val : Spec.Zq) + (b.val : Spec.Zq) ∧
    c.val < Spec.Q := by
    simp

    /- We use bitvectors to automate the proofs -/
    have hEq : ((c1.bv - 3329#32 + (3329#32 &&& c2.bv)) % 3329#32) = (a.bv + b.bv) % 3329#32 := by
      bv_decide
    have hLt : (c1.bv - 3329#32 + (3329#32 &&& c2.bv)) < 3329#32 := by
      bv_decide

    /- We need to convert the bit vector, ℕ and ZMod elements to ℤ -/
    zify at *
    simp [U32.max] at *
    norm_mod

    /- We can now prove the two post-conditions -/
    split_conjs
    . have hab : (a.val + b.val) % 4294967296 = a.val + b.val := by
        apply Int.emod_eq_of_lt <;> scalar_tac
      rw [hab] at hEq
      apply hEq
    . apply hLt

  -- Finish the proof
  progress
  . -- massert
    simp at hPost
    apply hPost.right
  . simp at *
    apply hPost

/-!
Subtraction modulo
-/

def ntt.SymCryptMlKemModSub' (a : U32) (b : U32) : Result U32 := do
  let i ← 2#u32 * ntt.Q
  massert (a < i)
  massert (b <= ntt.Q)
  let res := core.num.U32.wrapping_sub a b
  let i1 ← res >>> 16#i32
  (if i1 = 0#u32 then ok () else massert (i1 = 65535#u32))
  let res1 := core.num.U32.wrapping_add res (ntt.Q &&& i1)
  massert (res1 < ntt.Q)
  Result.ok res1

@[simp]
def ntt.SymCryptMlKemModSub_eq (a : U32) (b : U32) :
  SymCryptMlKemModSub a b = SymCryptMlKemModSub' a b := by
  unfold SymCryptMlKemModSub SymCryptMlKemModSub'
  simp
  intros
  split <;> simp

/-- We first introduce a general, auxiliary version of the spec, that we later split in two.
    One of them is used to subtract numbers in the NTT, the other is used in the Montgomery
    multiplication to put the number back in the bounds.
 -/
theorem ntt.SymCryptMlKemModSub'_aux_spec (a : U32) (b : U32)
  (h : (a.val < Spec.Q ∧ b.val < Spec.Q) ∨ (a.val < 2 * Spec.Q ∧ b.val = Spec.Q)) :
  ∃ (c : U32), ntt.SymCryptMlKemModSub' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemModSub'

  simp at *
  progress as ⟨ twoQ, hTwoQ ⟩
  progress
  clear twoQ hTwoQ
  progress
  progress as ⟨ c2, hc2 ⟩
  simp at *

  -- TODO: handle this properly with progress
  have hIf : (if c2 = 0#u32 then ok () else massert (c2 = 65535#u32)) = ok () := by
    dcases h
    -- TODO: automate this
    . have : a.bv < 3329#32 := by
        simp [U32.bv]
        scalar_tac
      have : b.bv < 3329#32 := by -- TODO: bvfy?
        simp [U32.bv]
        scalar_tac
      split <;> try simp
      progress
      simp [U32.eq_equiv_bv_eq] at *
      bv_decide
    . have : a.bv < 6658#32 := by
        simp [U32.bv]
        scalar_tac
      have : b.bv = 3329#32 := by -- TODO: bvfy?
        simp [U32.bv, *]
      split <;> try simp
      progress
      simp [U32.eq_equiv_bv_eq] at *
      bv_decide
  progress; clear hIf

  -- Prove the post-condition (we also need this prove that the assert holds)
  have hPost :
    let c := core.num.U32.wrapping_add (core.num.U32.wrapping_sub a b) (3329#u32 &&& c2)
    (c.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
    c.val < Spec.Q := by

    /- We use bitvectors to automate the proofs -/
    have ⟨ hEq, hLt ⟩ :
      ((a.bv - b.bv + (3329#32 &&& c2.bv)) % 3329#32) = (a.bv + 3329#32 - b.bv) % 3329#32 ∧
      (a.bv - b.bv + (3329#32 &&& c2.bv)) < 3329#32 := by
      dcases h
      . have : a.bv < 3329#32 := by -- TODO: bvfy?
          simp [U32.bv]
          scalar_tac
        have : b.bv < 3329#32 := by -- TODO: bvfy?
          simp [U32.bv]
          scalar_tac
        bv_decide
      . have : a.bv < 6658#32 := by
          simp [U32.bv]
          scalar_tac
        have : b.bv = 3329#32 := by -- TODO: bvfy?
          simp [U32.bv, *]
        bv_decide

    /- We need to convert the bit vector, ℕ and ZMod elements to ℤ -/
    zify at *
    simp [U32.max] at *
    norm_mod

    have hb : ((4294967296 - b.toNat : Nat) : Int) = 4294967296 - b.val := by scalar_tac
    rw [hb] at hEq hLt

    /- We can now prove the two post-conditions -/
    split_conjs
    . rw [hEq]
      have h :=
        calc
          (4294967296 - b.val + (a.val + 3329)) % 4294967296 = (4294967296 + (a.val + 3329 - b.val)) % 4294967296 := by ring_nf
          _ = (a.val + 3329 - b.val) % 4294967296 := by simp
      simp [h]; clear h
      ring_nf
      have h : (3329 + (a.val - b.val)) % 4294967296 = 3329 + (a.val - b.val) := by
        apply Int.emod_eq_of_lt <;> scalar_tac
      simp [h]; clear h

      simp [← Int.sub_emod]
    . apply hLt

  -- Finish the proof
  progress
  . -- massert
    simp at hPost
    apply hPost.right
  . simp at *
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

-- TODO: generalize and move


-- TODO: automatic simplification when using bv_decide? simp_ctx tactic?
@[simp] theorem U8.bv_ofInt (x : Int) (h) : U8.bv (U8.ofInt x h) = BitVec.ofNat _ x.toNat := by simp [U8.bv]
@[simp] theorem U16.bv_ofInt (x : Int) (h) : U16.bv (U16.ofInt x h) = BitVec.ofNat _ x.toNat := by simp [U16.bv]
@[simp] theorem U32.bv_ofInt (x : Int) (h) : U32.bv (U32.ofInt x h) = BitVec.ofNat _ x.toNat := by simp [U32.bv]
@[simp] theorem U64.bv_ofInt (x : Int) (h) : U64.bv (U64.ofInt x h) = BitVec.ofNat _ x.toNat := by simp [U64.bv]
@[simp] theorem U128.bv_ofInt (x : Int) (h) : U128.bv (U128.ofInt x h) = BitVec.ofNat _ x.toNat := by simp [U128.bv]
@[simp] theorem Usize.bv_ofInt (x : Int) (h) : Usize.bv (Usize.ofInt x h) = BitVec.ofNat _ x.toNat := by simp [Usize.bv]

-- TODO: option that we give to scalar_tac upon calling it (rather than global option)
-- TODO: scalar_tac can't reason about upper bounds such as: `a < b ∧ c < d → a * c < b * d`
-- (we need aesop to saturate the context)

-- TODO: having too many theorems like this can make the context explode
theorem Scalar_mul_bound {ty : ScalarTy} (h : ¬ ty.isSigned) (x y : Scalar ty) :
  0 ≤ x.val * y.val ∧ x.val * y.val ≤ Scalar.max ty * Scalar.max ty := by
  have := x.hmin
  have := x.hmax
  have := y.hmin
  have := y.hmax
  have : Scalar.min ty = 0 := by dcases ty <;> simp_all [Scalar.min]
  have := Aeneas.ScalarTac.Int.pos_mul_pos_is_pos y.val x.val (by omega) (by omega)
  have := @Int.mul_le_mul x.val y.val (Scalar.max ty) (Scalar.max ty) (by omega) (by omega)
  omega

@[nonlin_scalar_tac x.val * y.val]
theorem U8.mul_bound (x y : U8) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ (2^8 - 1) * (2^8 - 1) := by
  have := Scalar_mul_bound (by simp) x y
  scalar_tac

@[nonlin_scalar_tac x.val * y.val]
theorem U16.mul_bound (x y : U16) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ (2^16 - 1) * (2^16 - 1) := by
  have := Scalar_mul_bound (by simp) x y
  scalar_tac

@[nonlin_scalar_tac x.val * y.val]
theorem U32.mul_bound (x y : U8) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ (2^32 - 1) * (2^32 - 1) := by
  have := Scalar_mul_bound (by simp) x y
  scalar_tac

@[nonlin_scalar_tac x.val * y.val]
theorem U64.mul_bound (x y : U64) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ (2^64 - 1) * (2^64 - 1) := by
  have := Scalar_mul_bound (by simp) x y
  scalar_tac

@[nonlin_scalar_tac x.val * y.val]
theorem U128.mul_bound (x y : U128) : 0 ≤ x.val * y.val ∧ x.val * y.val ≤ (2^128 - 1) * (2^128 - 1) := by
  have := Scalar_mul_bound (by simp) x y
  simp [Scalar.max, U128.max] at *
  omega

-- TODO: generalize
-- TODO: the infered type of `abMont &&& 65535#u32` is `Scalar ...` while it should be `U32`
@[simp]
theorem U32.bv_and (x y : U32) : U32.bv (x &&& y) = x.bv &&& y.bv := by
  -- This should derive directly from the definition of U32.hAnd, but for now this definition is a `sorry`...
  sorry

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
theorem mod_4294967296_65536_eq (x : Int) : ((x % 4294967296) % 65536) = x % 65536 := by
  rw [Int.emod_emod_of_dvd]
  omega

@[local simp]
theorem mod_65536_4294967296_eq (x : Int) : ((x % 65536) % 4294967296) = x % 65536 := by
  apply Int.emod_eq_of_lt <;> omega

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

set_option scalarTac.nonLin true

theorem mont_reduce_bv_spec (a b bMont tR t : U32)
  (haBound : a.val < 3329)
  (hbBound : b.val < 3329)
  (hbMont : bMont.bv = (b.bv * ntt.NegQInvModR.bv) &&& ntt.Rmask.bv)
  (htR : tR.bv = a.bv * b.bv + ((a.bv * bMont.bv) &&& ntt.Rmask.bv) * 3329)
  (ht : t.bv = tR.bv >>> 16) :
  (t.val : ZMod Spec.Q) = (a.val : ZMod Spec.Q) * b.val * (2^16 : ZMod Spec.Q)⁻¹ ∧
  t.val < 2 * Spec.Q := by
  have hEq := mont_reduce_no_divide_bv_spec a b bMont tR hbMont htR
  have habLt : (a.val * b.val).toNat < 3329 * 2 ^ 16 := by
    have : (a.val * b.val).toNat = a.toNat * b.toNat := by
      have ha : a.val = a.toNat := by scalar_tac
      have hb : b.val = b.toNat := by scalar_tac
      rw [ha, hb]
      scalar_tac
    rw [this]; clear this
    apply Nat.mul_lt_mul_of_lt_of_lt <;> scalar_tac

  have hMont := mont_reduce_spec 3329 (2^16) 3327 (a.val * b.val).toNat (by simp; exists 16) (by simp) (by simp)
    habLt (by constructor)
  -- Simplify the bit vector operations
  simp [mont_reduce] at hMont
  have : a.val * b.val ⊔ 0 = a.val * b.val := by
    scalar_tac

  simp [this] at hMont; clear this
  replace ⟨ hMont, hBounds ⟩ := hMont
  rw [htR, hbMont] at ht
  simp [bv_and_65535_eq_mod] at ht -- TODO: why is this theorem not automatically applied?

  zify at ht; simp at ht
  zify; simp
  rw [ht]

  have : (a.val * b.val + a.val * (b.val * 3327 % 65536) % 65536 * 3329) % 4294967296 =
         a.val * b.val + a.val * (b.val * 3327 % 65536) % 65536 * 3329 := by
    apply Int.emod_eq_of_lt
    . scalar_tac
    . have : a.val * b.val ≤ 3329 * 3329 := by
        apply Int.mul_le_mul <;> (try omega); scalar_tac
      have : a.val * (b.val * 3327 % 65536) % 65536 * 3329 ≤ 65536 * 3329 := by
        apply Int.mul_le_mul <;> (try omega)
      omega
  rw [this]; clear this

  have : a.val * (b.val * 3327 % 65536) % 65536 =
         (a.val * b.val * 3327) % 65536 := by
    apply ZMod_eq_imp_mod_eq
    simp [ZMod.intCast_mod', mul_assoc] -- TODO: doesn't get automatically applied?
  rw [this]

  simp [hMont, hBounds]
  apply ZMod_eq_imp_mod_eq
  simp

  -- TODO: conversion issues
  simp [ZMod.intCast_mod'] -- TODO: doesn't get automatically applied?
  ring_nf

set_option scalarTac.nonLin false

set_option maxHeartbeats 1000000

@[pspec]
theorem ntt.SymCryptMlKemMontMul_spec (a : U32) (b : U32) (bMont : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) --(hbMont : bMont.val < Spec.Q * Spec.Q)
  (hbMont : bMont.bv = (b.bv * ntt.NegQInvModR.bv) &&& Rmask.bv) :
  ∃ (c : U32), ntt.SymCryptMlKemMontMul a b bMont = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) * (b.val : Spec.Zq) * (2^16)⁻¹ ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemMontMul
  have : a.bv < 3329#32 := by -- TODO: bvfy?
    simp [U32.bv]
    scalar_tac
  have : b.bv < 3329#32 := by -- TODO: bvfy?
    simp [U32.bv]
    scalar_tac
  simp at *
  progress
  progress

  have bMontLe : bMont.val ≤ 65535 := by
    have : bMont.bv ≤ 65535#32 := by bv_decide
    zify at this; simp_all
  progress

  progress with U32.mul_bv_spec as ⟨ b1, hb1, hb1' ⟩
  simp at hb1'

  have bMontLe : bMont = b1 &&& 65535#u32 := by
    have : bMont.bv = b1.bv &&& 65535#32 := by bv_decide
    simp at this
    zify at this; simp at this
    simp_all [Scalar.eq_equiv]
  progress

  -- TODO: scalar_tac is not good at reasoning about upper bounds in the presence of multiplication
  have : a.val * b.val ≤ 3329 * 3329 := by
    have := @Int.mul_le_mul a.val b.val 3329 3329 (by scalar_tac) (by scalar_tac) (by scalar_tac) (by simp)
    scalar_tac
  progress with U32.mul_bv_spec as ⟨ ab, hab, hab' ⟩

  have : a.val * bMont.val ≤ 3329 * 65535 := by
    have := @Int.mul_le_mul a.val bMont.val 3329 65535 (by scalar_tac) (by scalar_tac) (by scalar_tac) (by simp)
    scalar_tac
  progress with U32.mul_bv_spec as ⟨ abMont, _, habMont ⟩

  have : (abMont &&& 65535#u32).val ≤ 65535 := by
    have : (U32.bv (abMont &&& 65535#u32)) ≤ 65535#32 := by simp; bv_decide -- TODO: remove the simp
    zify at this; simp_all

  have : (abMont &&& 65535#u32).val * 3329#u32.val ≤ 65535 * 3329 := by
    have := @Int.mul_le_mul (abMont &&& 65535#u32).val 3329 65535 3329 (by scalar_tac) (by scalar_tac) (by scalar_tac) (by simp)
    simp at *
    scalar_tac
  progress with U32.mul_bv_spec as ⟨ res1 ⟩

  progress with U32.add_bv_spec as ⟨ res2 ⟩

  have : res2 &&& 65535#u32 = 0#u32 := by
    have := mont_reduce_no_divide_bv_spec a b bMont res2 (by simp [*]) (by simp [*])
    simp at this
    simp [U32.eq_equiv_bv_eq, this]
  progress

  progress as ⟨ res3, hRes3 ⟩
  simp at hRes3

  -- Here we need to use the fact that we performed a Montgomery multiplication to get
  -- the bounds and the rest
  have hMontReduce :=
    mont_reduce_bv_spec a b bMont res2 res3 (by omega) (by omega) (by simp [*])
      (by simp[*]) (by simp[*])

  progress with ntt.SymCryptMlKemModSub'_sub_Q_spec as ⟨ res4, hRes4Eq, hRes4Bound ⟩
  simp at hRes4Bound

  simp [hRes4Eq, hRes4Bound]
  simp [hMontReduce]
  rfl

theorem ntt.MlKemZetaBitRevTimesR_map_val_eq :
  List.map Scalar.val ntt.MlKemZetaBitRevTimesR.val =
  List.map (fun i => (17^bitRev 7 i * 2^16) % 3329) (List.range' 0 128) := by
  native_decide

theorem ntt.MlKemZetaBitRevTimesRTimesNegQInvModR_map_val_eq :
  List.map U16.toNat ntt.MlKemZetaBitRevTimesRTimesNegQInvModR.val =
  List.map (fun i => (((17^bitRev 7 i * 2^16) % 3329) * 3327) %  2^16) (List.range' 0 128) := by
  native_decide

@[simp]
theorem Array.val_length_eq (n : Usize) (a : Std.Array α n) :
  a.val.length = n.toNat := by
  cases a; simp; omega

-- TODO: List.getD
@[simp]
theorem List.index_range' (i start n: ℕ) :
  (List.range' start n).index i = if i < n then start + i else 0 := by
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
      ring_nf

theorem array_map_val_eq_range'_imp_index_usize_eq {α β} [Inhabited α] {a : Std.Array α n} {f : α → β} {g : ℕ → β}
  (hEq : List.map f a = List.map g (List.range' 0 n.toNat)) (i : Usize) (h : i.toNat < n.toNat) :
  ∃ v, Array.index_usize a i = ok v ∧
  f v = g i.toNat := by
  let rec aux (l : List α) (i : Nat) (hi : i < l.length) (start : Nat)
            (hEq : List.map f l = List.map g (List.range' start l.length)) :
            f (List.index l i) = g (start + i) := by
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
        have := aux l i hi (start + 1) (by simp [hEq])
        rw [this]; ring_nf

  progress as ⟨ v, hv ⟩
  rw [hv]
  -- TODO: we should use List.getD now
  have h := aux a i.toNat (by scalar_tac) 0 (by simp[hEq])
  simp at h
  simp [h]

@[pspec]
theorem ntt.MlKemZetaBitRevTimesR_index_spec (k : Usize) (h : k.val < 128) :
  ∃ v, Array.index_usize ntt.MlKemZetaBitRevTimesR k = ok v ∧
  --v.bv = BitVec.ofNat 32 (17 ^ bitRev 7 k.toNat * 65536 % 3329)
  (v.val : ZMod Spec.Q) = Spec.ζ^(bitRev 7 k.toNat) * 65536
  := by
  have := array_map_val_eq_range'_imp_index_usize_eq ntt.MlKemZetaBitRevTimesR_map_val_eq
  progress as ⟨ v, hv ⟩
  rw [hv]
  simp [Spec.ζ]
  simp [ZMod.intCast_mod']

@[pspec]
theorem ntt.MlKemZetaBitRevTimesRTimesNegQInvModR_index_spec' (k : Usize) (h : k.val < 128) :
  ∃ v, Array.index_usize ntt.MlKemZetaBitRevTimesRTimesNegQInvModR k = ok v ∧
  BitVec.ofNat 32 v.toNat = (BitVec.ofNat _ ((17^(bitRev 7 k.toNat) * 65536) % 3329) * 3327#32) &&& 65535#32
  := by
  have := array_map_val_eq_range'_imp_index_usize_eq ntt.MlKemZetaBitRevTimesRTimesNegQInvModR_map_val_eq
  progress as ⟨ v, hv ⟩
  simp only [bv_and_65535_eq_mod]
  zify
  rw [hv]
  simp

-- TODO: we need to get rid of List.update/List.index
@[simp]
theorem List.update_eq_set (l : List α) (i : Nat) (x : α) :
  l.update i x = l.set i x := by
  revert i
  induction l <;> intro i
  . simp
  . dcases i
    . simp at *
    . simp [*]

-- TODO: we need to get rid of List.update/List.index
@[simp]
theorem List.index_eq_get [Inhabited α] (l : List α) (i : Nat) :
  l.index i = l[i]! := by
  revert i
  induction l <;> intro i
  . simp
  . dcases i
    . simp at *
    . simp [*]

def to_poly (a : Array U16 256#usize) : Spec.Polynomial :=
  ⟨ List.map (fun x => (x.val : Spec.Zq)) a.val, by simp ⟩

@[simp]
theorem index_to_poly (a : Array U16 256#usize) (i : ℕ) :
  List.index (to_poly a) i = ((List.index a.val i) : Spec.Zq) := by
  sorry

@[simp]
theorem to_poly_update (a : Array U16 256#usize) (i : Usize) (x : U16) :
  to_poly (Array.update a i x) = Spec.Polynomial.set (to_poly a) i.toNat (x.val : Spec.Zq) := by
  sorry

-- TODO: generalize
@[simp] theorem core.convert.num.FromU32U16.val_from_eq x : (core.convert.num.FromU32U16.from x).val = x.val := by rfl

-- TODO: generalize
@[simp] theorem U32.add_toNat_eq (x y : U32) : (x.val + y.val).toNat = x.toNat + y.toNat := by scalar_tac
@[simp] theorem Usize.add_toNat_eq (x y : Usize) : (x.val + y.val).toNat = x.toNat + y.toNat := by scalar_tac

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

@[pspec]
theorem ntt.SymCryptMlKemMontMul_twiddle_spec (k : Usize) (c : U32) (twiddleFactor : U32) (twiddleFactorMont : U32)
  (hc : c.val < Spec.Q) (hb : twiddleFactor.val < Spec.Q)
  (htf : twiddleFactor.bv = BitVec.ofNat _ ((17^(bitRev 7 k.toNat) * 65536) % 3329))
  (htfMont : twiddleFactorMont.bv = (twiddleFactor.bv * 3327#32) &&& 65535#32) :
  ∃ (d : U32), ntt.SymCryptMlKemMontMul c twiddleFactor twiddleFactorMont = ok d ∧
  (d.val : Spec.Zq) = (c.val : Spec.Zq) * (Spec.ζ^(bitRev 7 k.toNat)) ∧
  d.val < Spec.Q := by
  progress as ⟨ d, hEq, hLt ⟩
  simp at htfMont
  zify at htf; simp at htf
  zify at htfMont; simp at htfMont
  simp [*]
  split_conjs
  . simp [ZMod.intCast_mod']
    ring_nf
    simp [Spec.ζ]
    have : (c.val : Spec.Zq) * 65536⁻¹ * 17 ^ bitRev 7 k.toNat * 65536 =
           (c.val : Spec.Zq) * 17 ^ bitRev 7 k.toNat * (65536⁻¹ * 65536) := by ring_nf
    rw [this]
    have : (65536⁻¹ : Spec.Zq) * (65536 : Spec.Zq) = 1 := by native_decide
    rw [this]
    simp
  . simp at hLt
    apply hLt

set_option maxHeartbeats 2000000

@[simp]
theorem List.set_get!_eq_set [Inhabited α] (l : List α) (i : Nat) (x : α) (h : i < l.length):
  (l.set i x)[i]! = x := by sorry

-- TODO: make the inequality check more robust
@[simp]
theorem List.set_get!_eq_get! [Inhabited α] (l : List α) (i j : Nat) (x : α) (h : i ≠ j):
  (l.set i x)[j]! = l[j]! := by sorry

-- TODO: progress is too slow, probably because of scalar_tac
-- TODO: termination_by is too slow
def ntt.SymCryptMlKemPolyElementNTTLayerC.inner_loop_loop_spec
  (peSrc : Array U16 256#usize) (k : Usize) (len : Usize) (start : Usize)
  (twiddleFactor : U32) (twiddleFactorMont : U32) (j : Usize)
  (hStart : start.toNat + 2 * len.toNat ≤ 256)
  (hjLe : j.toNat ≤ len.toNat)
  (htf : twiddleFactor.bv = BitVec.ofNat 32 (17 ^ bitRev 7 k.toNat * 65536 % 3329))
  (htfBound : twiddleFactor.val < 3329)
  (htfMont : twiddleFactorMont.bv = (BitVec.ofNat _ ((17^(bitRev 7 k.toNat) * 65536) % 3329) * 3327#32) &&& 65535#32)
  -- TODO: use get notations
  (hBounds : ∀ i, i < 256 → (List.index peSrc.val i).val < 3329)
  :
  ∃ peSrc', inner_loop_loop peSrc len start twiddleFactor twiddleFactorMont j = ok peSrc' ∧
  to_poly peSrc' = SpecAux.nttLayerInner (to_poly peSrc) k.toNat len.toNat start.toNat j.toNat := by

  rw [inner_loop_loop]
  dcases hjLt : ¬ j < len <;> simp [hjLt]
  . unfold SpecAux.nttLayerInner
    have : ¬ j.toNat < len.toNat := by scalar_tac
    simp only [this]; clear this
    simp
  . progress as ⟨ start_j, h_start_j ⟩
    progress as ⟨ c0 ⟩

    -- assert
    have hc0Bound := hBounds start_j.toNat (by scalar_tac)
    progress

    progress as ⟨ start_j_len, h_start_j_len ⟩
    progress as ⟨ c1 ⟩

    -- assert
    have hc1Bound := hBounds start_j_len.toNat (by scalar_tac)
    progress

    -- TODO: progress triggers as "maximum recursion depth has been reached"
    have ⟨ c1TimesTwiddle, hEq, hC1TimesTwiddle ⟩ :=
      ntt.SymCryptMlKemMontMul_twiddle_spec k (core.convert.num.FromU32U16.from c1) twiddleFactor twiddleFactorMont
        (by simp; scalar_tac) htfBound htf (by simp[htf, htfMont])
    simp [hEq]; clear hEq

    progress with SymCryptMlKemModSub'_spec as ⟨ c1' ⟩
    progress as ⟨ c0' ⟩

    progress as ⟨ c0'' ⟩
    progress as ⟨ peSrc1, hPeSrc1 ⟩
    progress as ⟨ c1'' ⟩
    progress as ⟨ peSrc2, hPeSrc2 ⟩

    progress as ⟨ j1 ⟩

    have hAddEq : (start.val + j.val + len.val).toNat = start.toNat + j.toNat + len.toNat := by scalar_tac

    have hWfPeSrc1 : ∀ i < 256, ((peSrc1.val).index i).val < 3329 := by
      simp [hPeSrc1, h_start_j]
      intro i hi
      have h0 : start.toNat + j.toNat < peSrc.val.length := by scalar_tac
      simp at h0
      have h1 : i < peSrc.val.length := by scalar_tac
      dcases h2 : i = start.toNat + j.toNat <;> simp [h0, h1, h2]
      . simp only [Spec.Q] at *
        omega
      . replace hBounds := hBounds i hi
        simp at hBounds
        apply hBounds

    have hWfPeSrc2 : ∀ i < 256, ((peSrc2.val).index i).val < 3329 := by
      simp [hPeSrc2, h_start_j, h_start_j_len, hAddEq]
      intro i hi
      have h0 : start.toNat + j.toNat + len.toNat < peSrc1.val.length := by scalar_tac
      simp at h0
      have h1 : i < peSrc1.val.length := by scalar_tac
      dcases h2 : i = start.toNat + j.toNat + len.toNat <;> simp [h0, h1, h2]
      . simp only [Spec.Q] at *
        omega
      . replace hBounds := hWfPeSrc1 i hi
        simp at hBounds
        apply hBounds
    progress as ⟨ peSrc3, hPeSrc3 ⟩

    -- The postcondition
    unfold SpecAux.nttLayerInner
    have : j.toNat < len.toNat := by scalar_tac
    simp only [this]; clear this
    simp [hPeSrc1, hPeSrc2, hPeSrc3]
    simp [*]
termination_by len.toNat - j.toNat
decreasing_by scalar_decr_tac

end Symcrust
