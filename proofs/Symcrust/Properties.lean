import Symcrust.BarrettReduction
import Symcrust.MontReduction
import Symcrust.SpecAux
import Symcrust.NatBit
import Symcrust.Funs
import Symcrust.NormMod

open Aeneas
open Std
open Result


namespace Symcrust

open Aeneas.Arith

set_option maxHeartbeats 2000000

example (abMont abMontAnd : U32)
  (h : (abMont &&& 65535#u32).val * 3329#u32.val ≤ 65535 * 3329) :
  abMontAnd.val * 3329#u32.val ≤ U32.max :=
  by
  -- TODO: fix this
  sorry
  -- sassumption

@[local simp, local bvify_simps] theorem bv_and_65535_eq_mod (x : BitVec 32) : x &&& 65535#32 = x % 65536#32 := by bv_decide
@[local simp, local bvify_simps] theorem bv_shift_16_eq_div (x : BitVec 32) : x >>> 16 = x / 65536#32 := by bv_decide

-- TODO: we need a reduceZMod simproc
@[local simp]
theorem mod_4294967296_65536_eq (x : Nat) : ((x % 4294967296) % 65536) = x % 65536 := by
  rw [Nat.mod_mod_of_dvd]; omega

@[local simp]
theorem mod_65536_4294967296_eq (x : Nat) : ((x % 65536) % 4294967296) = x % 65536 := by
  apply Nat.mod_eq_of_lt; omega

@[local simp]
theorem mod_int_4294967296_65536_eq (x : Int) : ((x % 4294967296) % 65536) = x % 65536 := by
  rw [Int.emod_emod_of_dvd]; omega

@[local simp]
theorem mod_int_65536_4294967296_eq (x : Int) : ((x % 65536) % 4294967296) = x % 65536 := by
  apply Int.emod_eq_of_lt <;> omega

attribute [local simp] Spec.Polynomial.set Spec.Polynomial.get!
attribute [-simp] List.getElem!_eq_getElem?_getD

@[simp, scalar_tac_simp, bvify_simps] theorem ntt.Q_eq : Q = 3329#u32 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem ntt.NegQInvModR_eq : ntt.NegQInvModR = 3327#u32 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem ntt.Rmask_eq : ntt.Rmask = 65535#u32 := by rfl
@[simp, scalar_tac_simp, bvify_simps] theorem ntt.Rlog2_eq : ntt.Rlog2 = 16#u32 := by rfl

-- TODO: rfl fails here because the number of bits is unknown
@[simp] theorem ntt.MLWE_POLYNOMIAL_COEFFICIENTS_eq : ntt.MLWE_POLYNOMIAL_COEFFICIENTS.val = 256 := by
  fsimp [ntt.MLWE_POLYNOMIAL_COEFFICIENTS, toResult, MLWE_POLYNOMIAL_COEFFICIENTS_body, eval_global]

@[simp] theorem ntt.INTTFixupTimesRsqr_eq : ntt.INTTFixupTimesRsqr.val = 1441 := by rfl
@[simp] theorem ntt.INTTFixupTimesRsqr_bv_eq : ntt.INTTFixupTimesRsqr.bv = 1441#32 := by rfl

@[simp] theorem ntt.INTTFixupTimesRsqrTimesNegQInvModR_bv_eq : INTTFixupTimesRsqrTimesNegQInvModR.bv = 10079#32 := by rfl

attribute [local simp, local scalar_tac_simp, local bvify_simps] Spec.Q

def to_poly (a : Array U16 256#usize) : Spec.Polynomial :=
  ⟨ List.map (fun x => (x.val : Spec.Zq)) a.val, by simp ⟩

@[simp]
theorem getElem!_to_poly (a : Array U16 256#usize) (i : ℕ) :
  (to_poly a)[i]! = ((a.val[i]!) : Spec.Zq) := by
  simp [to_poly]
  dcases hi : i < a.val.length <;> simp_all
  rfl

@[simp]
theorem to_poly_set (a : Array U16 256#usize) (i : Usize) (x : U16) :
  to_poly (Std.Array.set a i x) = Spec.Polynomial.set (to_poly a) i.val (x.val : Spec.Zq) := by
  simp only [to_poly, Spec.Q, id_eq, Array.set_val_eq, List.map_set, Spec.Polynomial.set]

@[simp]
theorem to_poly_getElem!_eq (a : Std.Array U16 256#usize) (i : Nat) :
  (to_poly a)[i]! = a.val[i]! := by
  fsimp [to_poly]
  fsimp [getElem!, decidableGetElem?]
  conv => lhs; simp only [getElem, Spec.Polynomial.get!]
  fsimp [getElem!, decidableGetElem?]
  dcases h: i < 256 <;> simp [h]
  rfl

@[local simp]
theorem mod_3329_mod_4294967296_eq (x : Int) :
  x % 3329 % 4294967296 = x % 3329 := by
  apply Int.emod_eq_of_lt <;> omega

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
  fsimp
  intros
  split <;> fsimp

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
  fsimp
  intros
  split <;> fsimp

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
  fsimp at *
  progress as ⟨ twoQ, hTwoQ ⟩
  progress -- massert
  clear twoQ hTwoQ
  progress -- massert

  progress as ⟨ c1, hc1 ⟩
  progress as ⟨ c2, hc2 ⟩

  have hIf : (if c2 = 0#u32 then ok () else massert (c2 = 65535#u32)) = ok () := by
    dcases h <;> split <;> bv_tac
  progress with hIf; clear hIf

  progress as ⟨ c3, hc3 ⟩
  progress as ⟨ c4, hc3 ⟩

  -- Prove the post-condition (we also need this prove that the assert holds)
  have hPost :
    (c4.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
    c4.val < Spec.Q := by

    have ⟨ hbvEq, hbvLt ⟩ : c4.bv % 3329#32 = (a.bv + 3329#32 - b.bv) % 3329#32 ∧
               c4.bv < 3329#32 := by
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
  fsimp at *
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
    split <;> bv_tac

  progress with hIf; clear hIf

  progress as ⟨ c3, hc3 ⟩
  progress as ⟨ c4, hc3 ⟩

  -- Prove the post-condition (we also need this prove that the assert holds)
  have hPost :
    (c4.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
    c4.val < Spec.Q := by

    have ⟨ hbvEq, hbvLt ⟩ : c4.bv % 3329#32 = (a.bv + 3329#32 - b.bv) % 3329#32 ∧
               c4.bv < 3329#32 := by
      bv_tac

    natify at *
    fsimp at *
    norm_mod

    split_conjs
    . rw [hbvEq]
      have : (4294967296 - ↑b + (↑a + 3329)) % 4294967296 =
             (a.val + (3329 - b.val)) := by scalar_tac
      rw [this]
      scalar_tac
    . apply hbvLt

  progress -- massert
  apply hPost

theorem ntt.SymCryptMlKemModSub'_spec (a : U32) (b : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) :
  ∃ (c : U32), ntt.SymCryptMlKemModSub' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  progress with SymCryptMlKemModSub'_aux_spec
  fsimp_all

theorem ntt.SymCryptMlKemModSub'_sub_Q_spec (a : U32) (b : U32)
  (ha : a.val < 2 * Spec.Q) (hb : b.val = Spec.Q) :
  ∃ (c : U32), ntt.SymCryptMlKemModSub' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  progress with SymCryptMlKemModSub'_aux_spec
  fsimp_all

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
  fsimp at *
  fsimp [*]; clear hbMont htR

  -- Reason in ℤ and simplify the modulus
  natify; fsimp [- EuclideanDomain.mod_eq_zero]

  -- Go to ZMod
  have : 0 = 0 % (65536 : Nat) := by fsimp
  rw [this]; clear this
  rw [← ZMod_nat_cast_eq_nat_cast_iff]
  fsimp

  -- Finish
  fsimp [mul_assoc]
  ring_nf
  have : (11075584 : ZMod 65536) = 0 := by rfl
  rw [this]; fsimp

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
    scalar_tac +nonLin

  have hMont := mont_reduce_spec 3329 U16.size 3327 (a.val * b.val)
    (by fsimp [U16.size, U16.numBits]; exists 16) (by fsimp [U16.size, U16.numBits]) (by fsimp)
    (by scalar_tac +nonLin) (by fsimp [U16.size, U16.numBits]; constructor)
  -- Simplify the bit vector operations
  fsimp [mont_reduce] at hMont

  obtain ⟨ hMont, hBounds ⟩ := hMont
  rw [htR, hbMont] at ht
  fsimp [bv_and_65535_eq_mod] at ht -- TODO: why is this theorem not automatically applied?

  natify at ht; fsimp at ht
  natify; fsimp
  rw [ht]

  have : (a.val * b.val + a.val * (b.val * 3327) % 65536 * 3329) % 4294967296 =
         a.val * b.val + a.val * (b.val * 3327) % 65536 * 3329 := by
    apply Nat.mod_eq_of_lt
    scalar_tac
  rw [this]; clear this

  fsimp [U16.size, U16.numBits] at *
  zify
  fsimp [← mul_assoc, hMont, hBounds]

@[progress]
theorem ntt.SymCryptMlKemMontMul_spec (a : U32) (b : U32) (bMont : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) --(hbMont : bMont.val < Spec.Q * Spec.Q)
  (hbMont : bMont.bv = (b.bv * ntt.NegQInvModR.bv) &&& Rmask.bv) :
  ∃ (c : U32), ntt.SymCryptMlKemMontMul a b bMont = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) * (b.val : Spec.Zq) * (2^16)⁻¹ ∧
  c.val < Spec.Q := by
  unfold SymCryptMlKemMontMul
  fsimp at *
  progress
  progress

  have bMontLe : bMont.val ≤ 65535 := by
    have : bMont.bv ≤ 65535#32 := by bv_decide
    natify at this; fsimp_all
  progress

  progress with U32.mul_bv_spec as ⟨ b1, hb1, hb1' ⟩
  fsimp at hb1'

  progress as ⟨ b2, hb2 ⟩

  have bMontLe : bMont = b2 := by
    bvify 32
    fsimp [*]
  progress -- massert

  -- TODO: scalar_tac is not good at reasoning about upper bounds in the presence of multiplication
  have : a.val * b.val ≤ 3329 * 3329 := by scalar_tac +nonLin
  progress with U32.mul_bv_spec as ⟨ ab, hab, hab' ⟩

  have : a.val * bMont.val ≤ 3329 * 65535 := by scalar_tac +nonLin
  progress with U32.mul_bv_spec as ⟨ abMont, _, habMont ⟩

  progress as ⟨ abMontAnd, _, habMontAnd ⟩

  have : (abMont &&& 65535#u32).val ≤ 65535 := by
    have : (U32.bv (abMont &&& 65535#u32)) ≤ 65535#32 := by bv_tac
    natify at this; fsimp_all

  -- TODO: removing this assert makes progress fail below when attempting to
  -- unify expressions
  have : abMontAnd.val * (3329#u32).val ≤ U32.max := by
    have : abMontAnd.val * 3329 ≤ 65536 * 3329 := by
      scalar_tac +nonLin
    scalar_tac
  progress with U32.mul_bv_spec as ⟨ res1 ⟩

  progress with U32.add_bv_spec as ⟨ res2 ⟩

  progress as ⟨ res3, _, hres3bv ⟩
  have : res3 = 0#u32 := by
    have := mont_reduce_no_divide_bv_spec a b bMont res2 (by fsimp [*]) (by fsimp [*])
    fsimp at this
    fsimp [U32.eq_equiv_bv_eq, hres3bv, this]
  progress

  progress as ⟨ res4, hRes4 ⟩
  fsimp at hRes4

  -- Here we need to use the fact that we performed a Montgomery multiplication to get
  -- the bounds and the rest
  have hMontReduce :=
    mont_reduce_bv_spec a b bMont res2 res4 (by omega) (by omega) (by fsimp [*])
      (by fsimp[*]) (by fsimp[*])

  progress with ntt.SymCryptMlKemModSub'_sub_Q_spec as ⟨ res4, hRes4Eq, hRes4Bound ⟩
  fsimp at hRes4Bound

  fsimp [hRes4Eq, hRes4Bound]
  fsimp [hMontReduce]
  -- TODO: why does (3329 : ZMod 3329) doesn't get simplified?
  have : (3329 : ZMod 3329) = 0 := by rfl
  fsimp [this, U16.size, U16.numBits]
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

theorem array_map_eq_range'_all_imp_index_usize_eq_pred {α β} [Inhabited α] {a : Std.Array α n}
  {f : α → β} {g : ℕ → β} {p : α → Bool}
  (hEq : List.map f a = List.map g (List.range' 0 n'))
  (hPred : List.all a p)
  (i : Usize) (h : i.val < n.val)
  (hn : n.val = n' := by simp) :
  ∃ v, Array.index_usize a i = ok v ∧
  f v = g i.val ∧ p v := by
  let rec aux1 (l : List α) (i : Nat) (hi : i < l.length) (start : Nat)
            (hEq : List.map f l = List.map g (List.range' start l.length)) :
            f (l[i]!) = g (start + i) := by
    match l with
    | [] =>  fsimp at hi
    | hd :: l =>
      fsimp at hEq
      fsimp [List.range'] at hEq
      dcases i
      . fsimp at *
        fsimp [hEq]
      . rename_i i
        fsimp at hi
        fsimp [hi]
        have := aux1 l i hi (start + 1) (by fsimp [hEq])
        fsimp_all
        ring_nf

  progress as ⟨ v, hv ⟩
  rw [hv]
  have h := aux1 a i.val (by scalar_tac) 0 (by fsimp [hn, hEq])
  fsimp at h
  fsimp [h]

  let rec aux2 (l : List α) (i : Nat) (hi : i < l.length) (start : Nat)
            (hPred : List.all l p) :
            p (l[i]!) := by
    match l with
    | [] =>  fsimp at hi
    | hd :: l =>
      dcases i
      . fsimp at *
        fsimp [hPred]
      . rename_i i
        fsimp at hi
        fsimp [hi]
        fsimp at hPred
        have := aux2 l i hi (start + 1) (by fsimp; tauto)
        fsimp_all
  have := aux2 a i.val (by scalar_tac) 0 (by fsimp[hPred])
  apply this

theorem array_map_eq_range'_imp_index_usize_eq {α β} [Inhabited α] {a : Std.Array α n}
  {f : α → β} {g : ℕ → β}
  (hEq : List.map f a = List.map g (List.range' 0 n'))
  (i : Usize) (h : i.val < n.val) (hn : n.val = n' := by simp):
  ∃ v, Array.index_usize a i = ok v ∧
  f v = g i.val := by
  have hPred : List.all a.val (fun _ => true) := by fsimp
  progress with array_map_eq_range'_all_imp_index_usize_eq_pred
  fsimp [*]

theorem ntt.MlKemZetaBitRevTimesR_index_spec (k : Usize) (h : k.val < 128) :
  ∃ v, Array.index_usize ntt.MlKemZetaBitRevTimesR k = ok v ∧
  (v.val : ZMod Spec.Q) = Spec.ζ^(bitRev 7 k.val) * 65536 ∧
  v.val < 3329
  := by
  have h := array_map_eq_range'_all_imp_index_usize_eq_pred ntt.MlKemZetaBitRevTimesR_map_val_eq ntt.MlKemZetaBitRevTimesR_map_all_eq
  progress with h as ⟨ v, hv, hv' ⟩
  fsimp at hv'
  fsimp only [hv']
  fsimp [hv]
  simp [Spec.ζ]

theorem ntt.MlKemZetaBitRevTimesRTimesNegQInvModR_index_spec' (k : Usize) (h : k.val < 128) :
  ∃ v, Array.index_usize ntt.MlKemZetaBitRevTimesRTimesNegQInvModR k = ok v ∧
  BitVec.ofNat 32 v.val = (BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329) * 3327#32) &&& 65535#32
  := by
  have h := array_map_eq_range'_imp_index_usize_eq ntt.MlKemZetaBitRevTimesRTimesNegQInvModR_map_val_eq
  progress with h as ⟨ v, hv ⟩
  fsimp only [bv_and_65535_eq_mod]
  natify
  rw [hv]
  fsimp

-- If we put the attribute directly on the declarations above, for some reason, the theorems do not get properly scoped
attribute [local progress] ntt.MlKemZetaBitRevTimesR_index_spec ntt.MlKemZetaBitRevTimesRTimesNegQInvModR_index_spec'

@[progress]
theorem ntt.SymCryptMlKemMontMul_twiddle_spec (k : Usize) (c : U32) (twiddleFactor : U32) (twiddleFactorMont : U32)
  (hc : c.val < Spec.Q) (hb : twiddleFactor.val < Spec.Q)
  (htf : twiddleFactor.bv = BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329))
  (htfMont : twiddleFactorMont.bv = (twiddleFactor.bv * 3327#32) &&& 65535#32) :
  ∃ (d : U32), ntt.SymCryptMlKemMontMul c twiddleFactor twiddleFactorMont = ok d ∧
  (d.val : Spec.Zq) = (c.val : Spec.Zq) * (Spec.ζ^(bitRev 7 k.val)) ∧
  d.val < Spec.Q := by
  progress as ⟨ d, hEq, hLt ⟩
  fsimp at htfMont
  natify at htf; fsimp at htf
  natify at htfMont; fsimp at htfMont
  fsimp [*]
  ring_nf
  fsimp [Spec.ζ]
  have : 17 ^ bitRev 7 ↑k * 65536 % 3329 % 4294967296 = 17 ^ bitRev 7 ↑k * 65536 % 3329 := by
    scalar_tac
  rw [this]; clear this
  fsimp
  have : (c.val : Spec.Zq) * (17 ^ bitRev 7 ↑k * 65536) * 65536⁻¹ =
          (c.val : Spec.Zq) * 17 ^ bitRev 7 k.val * (65536⁻¹ * 65536) := by ring_nf
  rw [this]; clear this
  have : (65536⁻¹ : Spec.Zq) * (65536 : Spec.Zq) = 1 := by native_decide
  rw [this]
  fsimp

def wfArray {n} (a : Array U16 n) : Prop :=
  ∀ i, i < n.val → a.val[i]!.val < 3329

theorem wfArray_update {n : Usize} (v : Std.Array U16 n) (i : Usize) (x : U16)
  (hbound : i.val < v.length)
  (hx : x.val < 3329)
  (hWf : wfArray v) :
  ∃ nv, v.update i x = ok nv ∧ nv = v.set i x ∧
  wfArray nv := by
  progress as ⟨ nv, hnv ⟩
  fsimp [wfArray] at *
  fsimp [hnv, toResult]
  intro j hj
  dcases hLt : j = i.val <;> fsimp [*]

theorem wfArray_index {n : Usize} (v : Std.Array U16 n) (i : Usize)
  (hbound : i.val < v.length)
  (hWf : wfArray v) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! ∧ x.val < 3329 := by
  progress as ⟨ x ⟩
  fsimp [wfArray] at hWf
  fsimp [*]
  replace hWf := hWf i.val (by scalar_tac)
  scalar_tac

/-!
NTT
-/

@[progress]
def ntt.SymCryptMlKemPolyElementNTTLayerC.inner_loop_loop_spec
  (peSrc : Array U16 256#usize) (k : Usize) (len : Usize) (start : Usize)
  (twiddleFactor : U32) (twiddleFactorMont : U32) (j : Usize)
  (hStart : start.val + 2 * len.val ≤ 256)
  (hjLe : j.val ≤ len.val)
  (htf : twiddleFactor.bv = BitVec.ofNat 32 (17 ^ bitRev 7 k.val * 65536 % 3329))
  (htfBound : twiddleFactor.val < 3329)
  (htfMont : twiddleFactorMont.bv = (BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329) * 3327#32) &&& 65535#32)
  (hBounds : wfArray peSrc)
  :
  ∃ peSrc', inner_loop_loop peSrc len start twiddleFactor twiddleFactorMont j = ok peSrc' ∧
  to_poly peSrc' = SpecAux.nttLayerInner (to_poly peSrc) k.val len.val start.val j.val ∧
  wfArray peSrc' := by

  rw [inner_loop_loop]
  dcases hjLt : ¬ j < len <;> fsimp [hjLt]
  . unfold SpecAux.nttLayerInner
    have : ¬ j.val < len.val := by scalar_tac
    fsimp only [this]; clear this
    fsimp [*]
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
        (by fsimp; scalar_tac) htfBound htf (by fsimp[htf, htfMont])
    fsimp [hEq]; clear hEq

    progress with SymCryptMlKemModSub'_spec as ⟨ c1' ⟩

    progress as ⟨ c0' ⟩

    progress as ⟨ c0'', hc0'' ⟩
    have : c0''.val = c0'.val := by sorry
    clear hc0''
    progress with wfArray_update as ⟨ peSrc1, hPeSrc1 ⟩
    progress as ⟨ c1'', hc1'' ⟩
    have : c1''.val = c1'.val := by sorry
    clear hc1''
    progress with wfArray_update as ⟨ peSrc2, hPeSrc2 ⟩

    progress as ⟨ j1 ⟩

    progress as ⟨ peSrc3, hPeSrc3 ⟩

    -- The postcondition
    unfold SpecAux.nttLayerInner
    have : j.val < len.val := by scalar_tac
    fsimp only [this]; clear this
    fsimp [hPeSrc1, hPeSrc2, hPeSrc3]
    fsimp [*]
termination_by len.val - j.val
decreasing_by scalar_decr_tac

private theorem convert_twiddleFactor_eq
  (k : Usize)
  (twiddleFactor : U16)
  (hft : twiddleFactor.val = Spec.ζ ^ bitRev 7 k.val * 65536)
  (hftBound : twiddleFactor.val < 3329) :
  (core.convert.num.FromU32U16.from twiddleFactor).bv = BitVec.ofNat 32 (17 ^ bitRev 7 k.val * 65536 % 3329)
  := by
  natify at *
  fsimp at *
  have : twiddleFactor.val % 3329 = twiddleFactor.val := by
    apply Nat.mod_eq_of_lt; scalar_tac
  rw [this] at hft; clear this
  rw [hft]

  have : 17 ^ bitRev 7 ↑k * 65536 % 3329 % 4294967296 =
         17 ^ bitRev 7 ↑k * 65536 % 3329 := by
    scalar_tac
  rw [this]; clear this

  rw [← ZMod_nat_cast_eq_nat_cast_iff]
  fsimp [Spec.ζ]

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
  to_poly peSrc' = SpecAux.nttLayer (to_poly peSrc) k.val len.val start.val (by fsimp [hLen]) ∧
  wfArray peSrc'
  := by
  rw [SymCryptMlKemPolyElementNTTLayerC_loop]
  dcases hLt: ¬ start < 256#usize <;> fsimp only [hLt] <;> fsimp
  . unfold SpecAux.nttLayer
    have : ¬ start.val < 256 := by scalar_tac
    fsimp only [this]; fsimp [*]
  . -- Getting those arithmetic facts is actually non trivial
    have : 2^layer ≤ 2^6 := by apply Nat.pow_le_pow_of_le <;> omega
    have : step < 2^layer := by
      have : ¬ step = 2^layer := by
        intro hContra
        fsimp [hContra] at hStart
        fsimp [hLen] at hStart
        fsimp [Nat.mul_assoc] at hStart
        rw [← Nat.pow_add] at hStart
        have : 7 - layer + layer = 7 := by omega
        rw [this] at hStart; clear this
        fsimp at hStart
        scalar_tac
      omega
    have : start.val + 2 * len.val ≤ 256 := by
      fsimp [hLen, hStart]
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
      fsimp at *
      have : step < 2^6 := by
        have := @Nat.pow_le_pow_of_le 2 layer 6 (by fsimp) (by omega)
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
      fsimp [hStart', hTwoLen]
      fsimp [hStart]
      ring_nf
    have := ntt.SymCryptMlKemPolyElementNTTLayerC_loop_spec layer hLayer (step + 1) (by scalar_tac)

    progress as ⟨ peSrc2, hPeSrc2 ⟩

    -- Proving the post-condition
    unfold SpecAux.nttLayer
    have hLt : start.val < 256 := by scalar_tac
    fsimp only [hLt]; fsimp
    fsimp [hPeSrc2, hPeSrc1, hk', hTwoLen, hStart']
    fsimp [*]
termination_by 256 - k.val
decreasing_by scalar_decr_tac

@[progress]
theorem ntt.SymCryptMlKemPolyElementNTTLayer_spec
  (peSrc : Array U16 256#usize)
  (k : Usize) (len : Usize)
  (hWf : wfArray peSrc)
  /- We could have less preconditions, but if we instantiate the variables with concrete parameters
     we can discharge those with calls to the simplifer, so we take advantage of that (less proof work on our side). -/
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
      calc 128 / 2^step = 2^7 / 2^step := by fsimp
           _ = 2^(7-step) := by rw [Nat.pow_div] <;> scalar_tac
    rw [this]
  have := ntt.SymCryptMlKemPolyElementNTTLayerC_loop_spec step (by scalar_tac) 0 (by fsimp)
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
  progress as ⟨ peSrc1 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc2 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc3 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc4 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc5 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc6 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc7 ⟩; fsimp [Nat.log2]
  rw [← SpecAux.ntt_eq]
  unfold SpecAux.ntt
  fsimp [*]

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
  (hBounds : wfArray peSrc)
  :
  ∃ peSrc', inner_loop_loop peSrc len start twiddleFactor twiddleFactorMont j = ok peSrc' ∧
  to_poly peSrc' = SpecAux.invNttLayerInner (to_poly peSrc) k.val len.val start.val j.val ∧
  wfArray peSrc' := by

  rw [inner_loop_loop]
  dcases hjLt : ¬ j < len <;> fsimp [hjLt]
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

    -- TODO: progress triggers a "maximum recursion depth has been reached"
    -- the problem comes from the unification of terms by singleAssumptionTac
    have ⟨ c1'', hEq, hc1'' ⟩ :=
      ntt.SymCryptMlKemMontMul_twiddle_spec k c1' twiddleFactor twiddleFactorMont
        (by fsimp; scalar_tac) htfBound htf (by fsimp[htf, htfMont])
    fsimp [hEq]; clear hEq

    progress as ⟨ tmp_u16, h_tmp_u16 ⟩

    have : tmp_u16.val < 3329 := by sorry -- TODO
    progress with wfArray_update as ⟨ peSrc1, hPeSrc1 ⟩
    progress as ⟨ c1''_u16, hc1''_u16 ⟩
    have : c1''_u16.val < 3329 := by sorry -- TODO
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

    have : (UScalar.cast UScalarTy.U16 tmp).val = tmp.val := by sorry -- TODO: fix this
    have : (UScalar.cast UScalarTy.U16 c1'').val = c1''.val := by sorry -- TODO: fix this
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
  dcases hLt: ¬ start < 256#usize <;> fsimp only [hLt] <;> fsimp
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
  /- We could have less preconditions, but if we instantiate the variables with concrete parameters
     we can discharge those with calls to the simplifer, so we take advantage of that (less proof work on our side). -/
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
      calc 256 / 2^len.val.log2 = 2^8 / 2^len.val.log2 := by fsimp [step]
           _ = 2^(8-len.val.log2) := by rw [Nat.pow_div] <;> scalar_tac
    rw [this]
    fsimp [step]
    scalar_tac
  have := ntt.SymCryptMlKemPolyElementINTTLayerC_loop_spec step (by scalar_tac) 0 (by fsimp)
  unfold SymCryptMlKemPolyElementINTTLayer
  have : len.val = 2 ^ (len.val.log2 - 1 + 1) := by
    have : len.val.log2 - 1 + 1 = len.val.log2 := by omega
    rw [this]
    rw [hLen.left]
  progress as ⟨ peSrc1, hEq, hWf ⟩
  tauto

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
  fsimp
  split <;> rename_i h
  . progress with wfArray_index as ⟨ x ⟩
    progress with ntt.SymCryptMlKemMontMul_spec as ⟨ xTimes ⟩
    progress as ⟨ xTimes', hxTimes' ⟩
    have : xTimes'.val = xTimes.val := by sorry -- TODO
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
      fsimp at *
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
        fsimp [hij]
    . fsimp [*]
  . have : i.val = 256 := by scalar_tac
    fsimp [*]
    intro j hj0 hj1
    -- Contradiction
    omega
termination_by 256 - i.val
decreasing_by scalar_decr_tac

@[progress]
theorem ntt.SymCryptMlKemPolyElementINTTAndMulR_loop_spec (peSrc : Std.Array U16 256#usize)
  (hWf : wfArray peSrc) :
  ∃ peSrc', ntt.SymCryptMlKemPolyElementINTTAndMulR_loop peSrc 0#usize = ok peSrc' ∧
  to_poly peSrc' = (to_poly peSrc) * (3303 : Spec.Zq) * (2^16 : Spec.Zq) ∧
  wfArray peSrc' := by
  progress as ⟨ peSrc', _, h ⟩
  fsimp [HMul.hMul, Spec.Polynomial.scalarMul, to_poly, *]

  have aux (f f' : List U16) (hLen : f'.length = f.length)
    (hEq : ∀ i, i < f.length → (f'[i]!.val : Spec.Zq) = f[i]!.val * 3303 * 2^16) :
    List.map (fun x => (x.val : Spec.Zq)) f' =
    List.map ((fun v => Mul.mul v (2^16 : Spec.Zq)) ∘ (fun v => Mul.mul v 3303) ∘ fun x => (x.val : Spec.Zq)) f := by
    revert f'; induction f
    . fsimp_all
    . rename_i hd tl hInd
      intro f' hLen hi
      dcases f'
      . fsimp at hLen
      . rename_i hd' tl'
        fsimp at *
        have := hInd tl' (by fsimp [*])
          (by
            intro i hLen
            have := hi (i + 1) (by omega)
            fsimp [hLen] at this
            apply this)
        fsimp [*]
        have := hi 0 (by omega)
        fsimp at this
        apply this

  rw [aux] <;> fsimp [*]
  fsimp at h
  apply h

@[progress]
theorem ntt.SymCryptMlKemPolyElementINTTAndMulR_spec (peSrc : Std.Array U16 256#usize)
  (hWf : wfArray peSrc) :
  ∃ peSrc1, SymCryptMlKemPolyElementINTTAndMulR peSrc = ok peSrc1 ∧
  to_poly peSrc1 = Spec.invNtt (to_poly peSrc) * (2^16 : Spec.Zq) ∧ wfArray peSrc1
  := by
  unfold SymCryptMlKemPolyElementINTTAndMulR
  progress as ⟨ peSrc1 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc2 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc3 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc4 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc5 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc6 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc7 ⟩; fsimp [Nat.log2]
  progress as ⟨ peSrc8 ⟩
  rw [← SpecAux.invNtt_eq]
  unfold SpecAux.invNtt
  fsimp [*]

end Symcrust
