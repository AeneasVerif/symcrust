import Symcrust.Code
import Symcrust.Properties.Ntt.BarrettReduction
import Symcrust.Properties.Ntt.MontReduction
import Symcrust.Properties.Ntt.NttSpecAux
import Symcrust.Properties.Basic

open Aeneas
open Std
open Result

#setup_aeneas_simps

namespace Symcrust

open Aeneas.Arith

set_option maxHeartbeats 10000000
set_option maxRecDepth 2048
set_option linter.dupNamespace false -- This option is needed because `Ntt.lean` is in an `Ntt` directory

@[local simp, local grind =] theorem bv_and_65535_eq_mod (x : BitVec 32) : x &&& 65535#32 = x % 65536#32 := by bv_decide
@[local simp, local grind =] theorem bv_shift_16_eq_div (x : BitVec 32) : x >>> 16 = x / 65536#32 := by bv_decide
@[local simp, local grind =] theorem nat_and_65535_eq_mod (x : Nat) : x &&& 65535 = x % 65536 := by apply Nat.and_two_pow_sub_one_eq_mod x 16

-- TODO: remove those simps
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

/-!
We want to use specifications which manipulate bit-vector representations
-/
attribute [-progress] U32.add_spec U32.mul_spec
attribute [local progress] U32.add_bv_spec U32.mul_bv_spec

/-!
The code uses casts from `U32` to `U16` but the `U32` values then fit into `U16`: we can
thus use a simpler version of the specification for the casts, which doesn't mention
bit-vectors.
-/
attribute [-progress] UScalar.cast.progress_spec
attribute [local progress] UScalar.cast_inBounds_spec

@[local simp]
theorem Nat_mod_3329_mod_4294967296_eq (x : Nat) :
  x % 3329 % 4294967296 = x % 3329 := by
  apply Nat.mod_eq_of_lt; omega

@[local simp]
theorem Int_mod_3329_mod_4294967296_eq (x : Int) :
  x % 3329 % 4294967296 = x % 3329 := by
  apply Int.emod_eq_of_lt <;> omega

namespace ntt

/-!
# "Simple" Reduction Modulo
-/

def mod_reduce' (a : U32) : Result U32 := do
  let i ← 2#u32 * ntt.Q
  massert (a < i)
  let res ← (↑(core.num.U32.wrapping_sub a ntt.Q) : Result U32)
  let i1 ← res >>> 16#i32
  massert (i1 = 0#u32 || i1 = 65535#u32)
  let i2 ← (↑(ntt.Q &&& i1) : Result U32)
  let res1 ← (↑(core.num.U32.wrapping_add res i2) : Result U32)
  massert (res1 < ntt.Q)
  ok res1

@[simp, progress_simps]
def mod_reduce_eq (a : U32) :
  mod_reduce a = mod_reduce' a := by
  unfold mod_reduce mod_reduce'
  fsimp
  intros
  split <;> fsimp [*]

@[local progress]
theorem mod_reduce'_spec (a : U32)
  (ha : a.val < 2 * Spec.Q) :
  ∃ (a' : U32), mod_reduce' a = ok a' ∧
  (a'.val : Spec.Zq) = (a.val : Spec.Zq) ∧
  a'.val < Spec.Q := by
  unfold mod_reduce'
  progress* <;> bv_tac 32

/-!
# Addition Modulo
-/
@[local progress]
theorem mod_add_spec (a : U32) (b : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q) :
  ∃ (c : U32), mod_add a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) + (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  unfold mod_add
  progress*

/-!
# Subtraction Modulo
-/

def mod_sub' (a : U32) (b : U32) : Result U32 := do
  massert (a < ntt.Q)
  massert (b < ntt.Q)
  let res ← (↑(core.num.U32.wrapping_sub a b) : Result U32)
  let i ← res >>> 16#i32
  massert (i = 0#u32 || i = 65535#u32)
  let i1 ← (↑(ntt.Q &&& i) : Result U32)
  let res1 ← (↑(core.num.U32.wrapping_add res i1) : Result U32)
  massert (res1 < ntt.Q)
  ok res1

@[simp, progress_simps]
def mod_sub_eq (a : U32) (b : U32) :
  mod_sub a b = mod_sub' a b := by
  unfold mod_sub mod_sub'
  fsimp
  intros
  split <;> fsimp [*]

@[local progress]
theorem mod_sub'_spec (a : U32) (b : U32)
  (_ : a.val < 3329)
  (_ : b.val < 3329) :
  ∃ (c : U32), mod_sub' a b = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) - (b.val : Spec.Zq) ∧
  c.val < Spec.Q := by
  unfold mod_sub'
  progress* <;> bv_tac 32

/-!
# Montgomery Reduction
-/

theorem mont_reduce_bv_spec (a b bMont tR t : U32)
  (haBound : a.val < 3329)
  (hbBound : b.val < 3329)
  (hbMont : bMont.bv = (b.bv * NEG_Q_INV_MOD_R.bv) &&& RMASK.bv)
  (htR : tR.bv = a.bv * b.bv + ((a.bv * bMont.bv) &&& RMASK.bv) * 3329)
  (ht : t.bv = tR.bv >>> 16) :
  (t.val : ZMod Spec.Q) = (a.val : ZMod Spec.Q) * b.val * (U16.size : ZMod Spec.Q)⁻¹ ∧
  t.val < 2 * Spec.Q := by
  have habLt : a.val * b.val < 3329 * U16.size := by
    scalar_tac +nonLin

  have hMont := mont_reduce_spec 3329 U16.size 3327 (a.val * b.val)
    (by fsimp [U16.size, U16.numBits]; exists 16) (by fsimp [U16.size, U16.numBits]) (by fsimp)
    habLt (by fsimp [U16.size, U16.numBits]; constructor)
  -- Simplify the bit vector operations
  fsimp [mont_reduce] at hMont

  obtain ⟨ hMont, hBounds ⟩ := hMont
  rw [htR, hbMont] at ht
  fsimp at ht

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

theorem mont_mul_spec (a : U32) (b : U32) (bMont : U32)
  (ha : a.val < Spec.Q) (hb : b.val < Spec.Q)
  (hbMont : bMont.bv = (b.bv * NEG_Q_INV_MOD_R.bv) &&& RMASK.bv) :
  ∃ (c : U32), mont_mul a b bMont = ok c ∧
  (c.val : Spec.Zq) = (a.val : Spec.Zq) * (b.val : Spec.Zq) * (2^16)⁻¹ ∧
  c.val < Spec.Q := by
  unfold mont_mul
  fsimp at *
  progress
  progress

  have bMontLe : bMont.val ≤ 65535 := by bv_tac 32
  progress

  progress as ⟨ b1, hb1, hb1' ⟩
  fsimp at hb1'

  progress as ⟨ b2, hb2 ⟩

  have bMontLe : bMont = b2 := by bv_tac 32
  progress -- massert

  have : a.val * b.val ≤ 3329 * 3329 := by scalar_tac +nonLin
  progress as ⟨ ab, hab, hab' ⟩

  have : a.val * bMont.val ≤ 3329 * 65535 := by scalar_tac +nonLin
  progress as ⟨ abMont, _, habMont ⟩

  progress as ⟨ abMontAnd, _, habMontAnd ⟩

  have : (abMont &&& 65535#u32).val ≤ 65535 := by bv_tac 32
  progress as ⟨ res1 ⟩

  progress as ⟨ res2 ⟩
  progress as ⟨ res3, hRes3 ⟩

  -- Here we need to use the fact that we performed a Montgomery multiplication to get
  -- the bounds and the rest
  have hMontReduce :=
    mont_reduce_bv_spec a b bMont res2 res3 (by omega) (by omega) (by fsimp [*])
      (by fsimp[*]) (by fsimp[*])

  progress as ⟨ res3, hRes3Eq, hRes3Bound ⟩
  fsimp at hRes3Bound

  fsimp [hRes3Eq, hRes3Bound]
  fsimp [hMontReduce]
  fsimp [this, U16.size, U16.numBits]

local progress_array_spec (name := ZETA_BIT_REV_TIMES_R_spec)
  ZETA_BIT_REV_TIMES_R[i]!
  { v =>
    (v.val : ZMod Spec.Q) = Spec.ζ^(bitRev 7 i) * 65536 ∧
     v.bv.zeroExtend 32 = BitVec.ofNat 32 (17 ^ bitRev 7 i * 65536 % 3329) ∧
     v.val < 3329 }
  by native_decide

local progress_array_spec (name := ZETA_BIT_REV_TIMES_R_TIMES_NEG_Q_INV_MOD_R_spec)
  ZETA_BIT_REV_TIMES_R_TIMES_NEG_Q_INV_MOD_R[k]!
  { v => BitVec.ofNat 32 v.val = (BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329) * 3327#32) &&& 65535#32 }
  by native_decide

local progress_array_spec (name := ZETA_TO_TIMES_BIT_REV_PLUS_1_TIMES_R_spec)
  ZETA_TO_TIMES_BIT_REV_PLUS_1_TIMES_R[i]!
  { v =>
    BitVec.ofNat 32 v.val = BitVec.ofNat _ ((17^(2 * bitRev 7 i + 1) * 2^16) % 3329) ∧ -- TODO: remove this?
    v.val = (17^(2 * bitRev 7 i + 1) * 2^16) % 3329 ∧
    v.val ≤ 3318 }
  by native_decide

@[local progress]
theorem mont_mul_twiddle_spec (k : Usize) (c : U32) (twiddleFactor : U32) (twiddleFactorMont : U32)
  (hc : c.val < Spec.Q) (hb : twiddleFactor.val < Spec.Q)
  (htf : twiddleFactor.bv = BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329))
  (htfMont : twiddleFactorMont.bv = (twiddleFactor.bv * 3327#32) &&& 65535#32) :
  ∃ (d : U32), mont_mul c twiddleFactor twiddleFactorMont = ok d ∧
  (d.val : Spec.Zq) = (c.val : Spec.Zq) * (Spec.ζ^(bitRev 7 k.val)) ∧
  d.val < Spec.Q := by
  progress with mont_mul_spec as ⟨ d, hEq, hLt ⟩
  fsimp at htfMont
  natify at htf; fsimp at htf
  natify at htfMont; fsimp at htfMont
  fsimp [*]
  ring_nf
  fsimp [Spec.ζ]

attribute [local progress] wfArray_update wfArray_index

@[simp]
theorem wfArray_zetaTwoTimesBitRevPlus1TimesR : wfArray ZETA_TO_TIMES_BIT_REV_PLUS_1_TIMES_R := by
  simp [wfArray_iff_forAll]; native_decide

/-!
# NTT
-/

@[progress]
def poly_element_ntt_layer_c.inner_loop_loop_spec
  (peSrc : Array U16 256#usize) (k : Usize) (len : Usize) (start : Usize)
  (twiddleFactor : U32) (twiddleFactorMont : U32) (j : Usize)
  (hStart : start.val + 2 * len.val ≤ 256)
  (htf : twiddleFactor.bv = BitVec.ofNat 32 (17 ^ bitRev 7 k.val * 65536 % 3329))
  (htfBound : twiddleFactor.val < 3329)
  (htfMont : twiddleFactorMont.bv = (BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329) * 3327#32) &&& 65535#32)
  (hBounds : wfArray peSrc)
  :
  ∃ peSrc', inner_loop_loop peSrc len start twiddleFactor twiddleFactorMont j = ok peSrc' ∧
  to_poly peSrc' = SpecAux.nttLayerInner (to_poly peSrc) k.val len.val start.val j.val ∧
  wfArray peSrc' := by
  unfold inner_loop_loop
  progress* <;> unfold SpecAux.nttLayerInner <;> simp_ifs <;> simp [*]
termination_by len.val - j.val
decreasing_by scalar_decr_tac

theorem poly_element_ntt_layer_c_loop_spec
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
  ∃ peSrc', poly_element_ntt_layer_c_loop peSrc k len start = ok peSrc' ∧
  to_poly peSrc' = SpecAux.nttLayer (to_poly peSrc) k.val len.val start.val (by fsimp [hLen]) ∧
  wfArray peSrc'
  := by
  unfold poly_element_ntt_layer_c_loop
  by_cases hLt: start < 256#usize <;> fsimp only [hLt] <;> fsimp
  swap
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

    progress as ⟨ twiddleFactor, hft, hftBound ⟩
    progress as ⟨ twiddleFactorMont, hftMont ⟩
    progress as ⟨ k', hk' ⟩

    have : (core.convert.num.FromU32U16.from twiddleFactorMont).bv =
            BitVec.ofNat 32 (17 ^ bitRev 7 ↑k * 65536 % 3329) * 3327#32 &&& 65535#32 := by
      simp at hftMont; simp; apply hftMont
    progress as ⟨ peSrc1, _, hPeSrc1 ⟩

    progress as ⟨ twoLen, hTwoLen ⟩
    progress as ⟨ start', hStart' ⟩

    have : k'.val ≤ 128 := by scalar_tac

    have : start'.val = 2 * len.val * (step + 1) := by
      ring_nf
      fsimp [hStart', hTwoLen]
      fsimp [hStart]
      ring_nf
    have := poly_element_ntt_layer_c_loop_spec layer hLayer (step + 1) (by scalar_tac)

    progress as ⟨ peSrc2, hPeSrc2 ⟩

    -- Proving the post-condition
    unfold SpecAux.nttLayer
    have hLt : start.val < 256 := by scalar_tac
    fsimp only [hLt]; fsimp
    fsimp [hPeSrc2, hPeSrc1, hk', hTwoLen, hStart']
    fsimp [*]
termination_by 256 - k.val
decreasing_by scalar_decr_tac

@[local progress]
theorem poly_element_ntt_layer_spec
  (peSrc : Array U16 256#usize)
  (k : Usize) (len : Usize)
  (hWf : wfArray peSrc)
  /- We could have less preconditions, but if we instantiate the variables with concrete parameters
     we can discharge those with calls to the simplifer, so we take advantage of that (less proof work on our side). -/
  (hk : 2^(k.val.log2) = k.val ∧ k.val.log2 < 7)
  (hLen : len.val = 128 / k.val)
  (hLenPos : 0 < len.val)
  :
  ∃ peSrc', poly_element_ntt_layer peSrc k len = ok peSrc' ∧
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
  have := poly_element_ntt_layer_c_loop_spec step (by scalar_tac) 0 (by fsimp)
  unfold poly_element_ntt_layer
  progress as ⟨ peSrc1, hEq, hWf ⟩; clear this
  tauto

@[progress]
theorem poly_element_ntt_spec (peSrc : Std.Array U16 256#usize)
  (hWf : wfArray peSrc) :
  ∃ peSrc1, poly_element_ntt peSrc = ok peSrc1 ∧
  to_poly peSrc1 = Spec.ntt (to_poly peSrc) ∧ wfArray peSrc1
  := by
  unfold poly_element_ntt
  progress* by fsimp [Nat.log2_def]
  rw [← SpecAux.ntt_eq]
  unfold SpecAux.ntt
  fsimp [*]

/-!
# INTT
-/
@[progress] -- TODO: `local progress` doesn't work because Lean makes the spec local to namespace `poly_element_intt_layer_c`
def poly_element_intt_layer_c.inner_loop_loop_spec
  (peSrc : Array U16 256#usize) (k : Usize) (len : Usize) (start : Usize)
  (twiddleFactor : U32) (twiddleFactorMont : U32) (j : Usize)
  (hStart : start.val + 2 * len.val ≤ 256)
  (htf : twiddleFactor.bv = BitVec.ofNat 32 (17 ^ bitRev 7 k.val * 65536 % 3329))
  (htfBound : twiddleFactor.val < 3329)
  (htfMont : twiddleFactorMont.bv = (BitVec.ofNat _ ((17^(bitRev 7 k.val) * 65536) % 3329) * 3327#32) &&& 65535#32)
  (hBounds : wfArray peSrc)
  :
  ∃ peSrc', inner_loop_loop peSrc len start twiddleFactor twiddleFactorMont j = ok peSrc' ∧
  to_poly peSrc' = SpecAux.invNttLayerInner (to_poly peSrc) k.val len.val start.val j.val ∧
  wfArray peSrc' := by
  unfold inner_loop_loop
  progress*
  . unfold SpecAux.invNttLayerInner
    simp_ifs
    fsimp [*]
    ring_nf
  . unfold SpecAux.invNttLayerInner
    simp_ifs
    fsimp [*]
termination_by len.val - j.val
decreasing_by scalar_decr_tac

theorem poly_element_intt_layer_c_loop_spec
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
  ∃ peSrc', poly_element_intt_layer_c_loop peSrc k len start = ok peSrc' ∧
  to_poly peSrc' = SpecAux.invNttLayer (to_poly peSrc) k.val len.val start.val (by fsimp [hLen]) ∧
  wfArray peSrc'
  := by
  unfold poly_element_intt_layer_c_loop
  dcases hLt: start < 256#usize <;> fsimp only [hLt] <;> fsimp
  swap
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
    have hRec := poly_element_intt_layer_c_loop_spec layer hLayer (step + 1) (by omega)

    have :
     (core.convert.num.FromU32U16.from twiddleFactorMont).bv =
      BitVec.ofNat 32 (17 ^ bitRev 7 ↑k * 65536 % 3329) * 3327#32 &&& 65535#32 := by
      simp at hftMont; simp; apply hftMont
    progress as ⟨ peSrc1, _, hPeSrc1 ⟩

    progress as ⟨ twoLen, hTwoLen ⟩
    progress as ⟨ start', hStart' ⟩

    have : start'.val = 2 * len.val * (step + 1) := by
      ring_nf
      fsimp [hStart', hTwoLen, hStart]
      ring_nf
    progress as ⟨ peSrc2, hPeSrc2 ⟩ -- TODO: progress by

    -- Proving the post-condition
    unfold SpecAux.invNttLayer
    have hLt : start.val < 256 := by scalar_tac
    fsimp only [hLt]; fsimp
    fsimp [hPeSrc2, hPeSrc1, hk', hTwoLen, hStart']
    fsimp [*]

@[local progress]
theorem poly_element_intt_layer_spec
  (peSrc : Array U16 256#usize)
  (k : Usize) (len : Usize)
  (hWf : wfArray peSrc)
  /- We could have less preconditions, but if we instantiate the variables with concrete parameters
     we can discharge those with calls to the simplifer, so we take advantage of that (less proof work on our side). -/
  (hLen : 2^(len.val.log2) = len.val ∧ 1 ≤ len.val.log2 ∧ len.val.log2 ≤ 7)
  (hk : k.val + 1 = 256 / len.val)
  (hLenPos : 0 < len.val)
  :
  ∃ peSrc', poly_element_intt_layer peSrc k len = ok peSrc' ∧
  to_poly peSrc' = SpecAux.invNttLayer (to_poly peSrc) k.val len.val 0 hLenPos ∧
  wfArray peSrc'
  := by
  let step := len.val.log2 - 1
  have hk' : k.val + 1 = 2 ^ (7 - step) := by
    rw [hk]
    rw [← hLen.left]
    have :=
      calc 256 / 2^len.val.log2 = 2^8 / 2^len.val.log2 := by fsimp [step]
           _ = 2^(8-len.val.log2) := by rw [Nat.pow_div] <;> scalar_tac
    rw [this]
    fsimp [step]
    scalar_tac
  have := poly_element_intt_layer_c_loop_spec step (by scalar_tac) 0 (by fsimp)
  unfold poly_element_intt_layer
  have hLen' : 2 ^ (len.val.log2 - 1 + 1) = len.val := by
    have : len.val.log2 - 1 + 1 = len.val.log2 := by omega
    rw [this]
    rw [hLen.left]
  progress as ⟨ peSrc1, hEq, hWf ⟩
  fsimp [*]

@[local progress]
theorem poly_element_intt_and_mul_r_loop_spec_aux
  (peSrc : Std.Array U16 256#usize) (i : Usize)
  (hi : i.val ≤ 256) (hWf : wfArray peSrc) :
  ∃ peSrc', poly_element_intt_and_mul_r_loop peSrc i = ok peSrc' ∧
  (∀ (j : Nat), j < i.val → (to_poly peSrc')[j]! = (to_poly peSrc)[j]!) ∧
  (∀ (j : Nat), i.val ≤ j → j < 256 →
    (to_poly peSrc')[j]! = (to_poly peSrc)[j]! * (3303 : Spec.Zq) * 2^16) ∧
  wfArray peSrc' := by
  unfold poly_element_intt_and_mul_r_loop
  fsimp
  split <;> rename_i h
  . progress as ⟨ x ⟩
    progress with mont_mul_spec as ⟨ xTimes ⟩ by (fsimp [*])
    progress as ⟨ xTimes', hxTimes' ⟩
    progress as ⟨ peSrc1, hPeSrc1 ⟩
    progress as ⟨ i1 ⟩
    progress as ⟨ peSrc2, h1, h2 ⟩
    -- TODO: this should be automated
    fsimp at *
    split_conjs
    . intro j hj
      simp_lists [h1]
      fsimp [*]
    . intro j hj0 hj1
      dcases hij : j = i.val
      . simp_lists [h1]
        fsimp [*]
        ring_nf
        fsimp
      . simp_lists [h2]
        fsimp [*]
    . fsimp [*]
  . fsimp [*]
    -- Contradiction
    scalar_tac
termination_by 256 - i.val
decreasing_by scalar_decr_tac

@[local progress]
theorem poly_element_intt_and_mul_r_loop_spec (peSrc : Std.Array U16 256#usize)
  (hWf : wfArray peSrc) :
  ∃ peSrc', poly_element_intt_and_mul_r_loop peSrc 0#usize = ok peSrc' ∧
  to_poly peSrc' = (to_poly peSrc) * (3303 : Spec.Zq) * (2^16 : Spec.Zq) ∧
  wfArray peSrc' := by
  progress as ⟨ peSrc', _, h ⟩
  split_conjs
  . fsimp [Spec.Polynomial.eq_iff]
    intro i hi
    fsimp at h
    simp_lists_scalar [h]
  . fsimp [*]

@[progress]
theorem poly_element_intt_and_mul_r_spec (peSrc : Std.Array U16 256#usize)
  (hWf : wfArray peSrc) :
  ∃ peSrc1, poly_element_intt_and_mul_r peSrc = ok peSrc1 ∧
  to_poly peSrc1 = Spec.invNtt (to_poly peSrc) * (2^16 : Spec.Zq) ∧ wfArray peSrc1
  := by
  unfold poly_element_intt_and_mul_r
  progress* by fsimp [Nat.log2_def]
  rw [← SpecAux.invNtt_eq]
  unfold SpecAux.invNtt
  fsimp [*]

/-!
# Multiply and Accumulate
-/

-- TODO: move
-- TODO: an annoying point is that we simplify before saturating, so it's not always easy
-- to properly write the scalar_tac lemmas so that they get applied properly.
-- Maybe we should saturate twice?
-- TODO: if we don't put the type annotation, the type inference fails but it doesn't
-- get detected by `scalar_tac`, leading to failures afterwards
@[local scalar_tac x.val &&& (65535 : ℕ)]
private theorem and_RMASK (x : U32) : x.val &&& 65535 ≤ 65535 := by
  have : (x &&& 65535#32) ≤ 65535 := by bv_tac 32
  natify at this
  simp only [BitVec.natCast_eq_ofNat, Bvify.UScalar.BitVec_ofNat_setWidth, UScalarTy.U32_numBits_eq,
    Bvify.U32.UScalar_bv, BitVec.setWidth_eq, UScalar.bv_toNat, Nat.reducePow, Nat.reduceMod,
    nat_and_65535_eq_mod, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, ge_iff_le] at *
  assumption

local grind_pattern and_RMASK => x.val &&& (65535 : ℕ)

section
  -- TODO: failure cases of scalar_tac +nonLin

  /- TODO: we should implement tactics to automatically refold parts of the code back into
     functions. -/

  /-- Auxiliary helper: the reduced multiplication performed by multiply and accumulate.

      This computes:
      red(a1b1) *
   -/
  private def mul_acc_mont_reduce (i : Usize) (a1b1 : U32) : Result U32 := do
    let i12 ← ((core.num.U32.wrapping_mul a1b1 NEG_Q_INV_MOD_R) : Result U32)
    let inv ← (↑(i12 &&& RMASK) : Result U32)
    let i13 ← inv * Q
    let i14 ← a1b1 + i13
    let a1b11 ← i14 >>> RLOG2
    let i15 ← ZETA_TO_TIMES_BIT_REV_PLUS_1_TIMES_R.index_usize i
    let i16 ← (↑(UScalar.cast UScalarTy.U32 i15) : Result U32)
    let a1b1zetapow ← a1b11 * i16
    pure a1b1zetapow

  -- TODO: automate the refold
  private theorem fold_mul_acc_mont_reduce (i : Usize) (a1b1 : U32) (f : U32 → Result α) :
    (do
      let i12 ← ((core.num.U32.wrapping_mul a1b1 NEG_Q_INV_MOD_R) : Result U32)
      let inv ← (↑(i12 &&& RMASK) : Result U32)
      let i13 ← inv * Q
      let i14 ← a1b1 + i13
      let a1b11 ← i14 >>> RLOG2
      let i15 ← ZETA_TO_TIMES_BIT_REV_PLUS_1_TIMES_R.index_usize i
      let i16 ← (↑(UScalar.cast UScalarTy.U32 i15) : Result U32)
      let a1b1zetapow ← a1b11 * i16
      f a1b1zetapow) =
    (do
      let a1b1zetapow ← mul_acc_mont_reduce i a1b1
      f a1b1zetapow)
    := by
    simp only [mul_acc_mont_reduce, bind_assoc_eq, bind_tc_ok, pure]

  theorem mlKem_mont_reduce_bounds_mul_acc (x : Nat) (h : x ≤ 3328*3328) :
    mont_reduce 3329 (2 ^ 16) 3327 x ≤ 3498 := by
    have := mont_reduce_bounds 3329 (2^16) 3327 (3328 * 3328) 3329 (by simp) (by native_decide)
    simp at *
    apply this x h

  @[local progress]
  theorem mul_acc_mont_reduce_spec (i : Usize) (a1b1 : U32)
    (hi : i.val < 128) (h1 : a1b1.val ≤ 3328 * 3328) :
    ∃ a1b1zetapow, mul_acc_mont_reduce i a1b1 = ok a1b1zetapow ∧
    a1b1zetapow.val ≤ 3498 * 3328 ∧
    (a1b1zetapow.val : Spec.Zq) = (a1b1.val : Spec.Zq) * Spec.ζ ^ (2 * bitRev 7 i.val + 1)
    := by
    unfold mul_acc_mont_reduce
    /- First step: reduce a1b1 -/
    let* ⟨ i12, i12_post ⟩ ← core.num.U32.wrapping_mul.progress_spec
    let* ⟨ inv, inv_post_1, inv_post_2 ⟩ ← UScalar.and_spec
    have : inv.val = (a1b1.val * NEG_Q_INV_MOD_R.val) % 2^16 := by fsimp [U32.size, U32.numBits, *]
    let* ⟨ i13, i13_post_1, i13_post_2 ⟩ ← U32.mul_bv_spec
    let* ⟨ i14, i14_post_1, i14_post_2 ⟩ ← U32.add_bv_spec
    let* ⟨ a1b11, a1b11_post ⟩ ← U32.ShiftRight_spec

    /- Prove the result of the Montgomery reduction -/
    have : a1b1.val + inv.val * 3329 ≤ U32.max := by scalar_tac
    have ha1b1_eq : a1b11.val = (a1b1.val + inv.val * Q.val) / 2^16 ∧ a1b11.val ≤ 65535 := by bv_tac 32
    have ha1b11_eq : (a1b11.val : Spec.Zq) = (a1b1.val : Spec.Zq) * 169 := by
      have ⟨ hMont, _ ⟩ := mont_reduce_spec 3329 (2^16) 3327 a1b1.val
        (by fsimp [U16.size, U16.numBits]; exists 16) (by fsimp [U16.size, U16.numBits]) (by fsimp)
        (by scalar_tac) (by fsimp; constructor)
      fsimp [mont_reduce] at hMont
      fsimp [inv_post_1, i12_post, U32.size, U32.numBits] at ha1b1_eq
      zify at ha1b1_eq
      zify
      fsimp [ha1b1_eq, hMont]
      fsimp [Int.mul_emod]
    have : a1b11.val ≤ 3498 := by
       have hBound := mlKem_mont_reduce_bounds_mul_acc a1b1.val (by scalar_tac)
       fsimp [mont_reduce] at hBound
       fsimp [inv_post_1, i12_post, U32.size, U32.numBits] at ha1b1_eq
       zify at ha1b1_eq
       scalar_tac

    /- Second step: multiply by ζ^(2*bitRev(i) + 1) -/
    let* ⟨ i15, i15_post_1, i15_post ⟩ ← ZETA_TO_TIMES_BIT_REV_PLUS_1_TIMES_R_spec
    let* ⟨ i16, i16_post ⟩ ← UScalar.cast_inBounds_spec
    have hpost1 : a1b11.val * i16.val ≤ 3498 * 3328 := by scalar_tac +nonLin
    let* ⟨ a1b1zetapow, a1b1zetapow_post, a1b1zetapow_post_2 ⟩ ← U32.mul_bv_spec

    /- Prove the post-condition -/
    have hpost2 : (a1b1zetapow.val : Spec.Zq) = (a1b1.val : Spec.Zq) * Spec.ζ ^ (2 * bitRev 7 i.val + 1) := by
      fsimp [a1b1zetapow_post, i16_post, i15_post, ha1b11_eq, Spec.ζ]
      ring_nf
      fsimp

    split_conjs
    . scalar_tac
    . apply hpost2

  private def update_acc (i : Usize) (c0 c1 : U32) (paDst : Array U32 256#usize) : Result (Array U32 256#usize) := do
    let paDst1 ← paDst.update i c0
    let i' ← i + 1#usize
    let paDst2 ← paDst1.update i' c1
    pure paDst2

  -- TODO: automate the refold
  private theorem fold_update_acc (i : Usize) (c0 c1 : U32) (paDst : Array U32 256#usize) (f : Array U32 256#usize → Result α) :
    (do
      let paDst1 ← paDst.update i c0
      let i' ← i + 1#usize
      let paDst2 ← paDst1.update i' c1
      f paDst2) =
    (do
      let paDst2 ← update_acc i c0 c1 paDst
      f paDst2)
    := by
    simp only [update_acc, bind_assoc_eq, bind_tc_ok, pure]

  -- TODO: move
  /-- Well-formed accumulator-/
  def wfAcc (f g : Array U16 256#usize) (B0 B1 : Nat) (i : Nat) (acc0 acc : Array U32 256#usize) : Prop :=
    -- The bounds
    (∀ j < i, acc[2 * j]! ≤ B0 + B1 ∧ acc[2 * j + 1]! ≤ B0 + B1) ∧
    (∀ j, i ≤ j → j < 128 → acc0[2 * j]! ≤ B0 ∧ acc0[2 * j + 1]! ≤ B0) ∧
    -- The values
    (∀ j < i, (acc[2 * j]! : Spec.Zq) = acc0[2 * j]! + SpecAux.baseCaseMultiply0 (to_poly f) (to_poly g) j ∧
              (acc[2 * j + 1]! : Spec.Zq) = acc0[2 * j + 1]! + SpecAux.baseCaseMultiply1 (to_poly f) (to_poly g) j) ∧
    (∀ j, i ≤ j → j < 128 → acc[2 * j]! = acc0[2 * j]! ∧ acc[2 * j + 1]! = acc0[2 * j + 1]!)

  def wfAcc_zero (f g : Array U16 256#usize) (B0 B1 : Nat) (acc : Array U32 256#usize)
    (h : ∀ j, j < 128 → acc[2 * j]! ≤ B0 ∧ acc[2 * j + 1]! ≤ B0) :
    wfAcc f g B0 B1 0 acc acc := by
    fsimp [wfAcc] at *
    apply h

  def wfAcc_128 {f g : Array U16 256#usize} {B0 B1 : Nat} {i : Nat} {acc0 acc : Array U32 256#usize}
    (h : wfAcc f g B0 B1 i acc0 acc) (hi : 128 ≤ i) :
    wfAcc f g B0 B1 128 acc0 acc := by
    fsimp [wfAcc] at *
    simp_lists [h]
    omega

  @[local progress]
  theorem wfAcc_index {f g : Array U16 256#usize} {B0 B1 : Nat} {i0 : Nat}
    {i : Usize}
    {acc0 acc : Array U32 256#usize}
    (hWf : wfAcc f g B0 B1 i0 acc0 acc)
    (hi0 : 2 * i0 ≤ i.val) (hi : i.val < 256) :
    ∃ x, acc.index_usize i = ok x ∧ x = acc0.val[i.val]! ∧ x.val ≤ B0 := by
    progress as ⟨ x ⟩
    unfold wfAcc at hWf
    -- TODO: this should be automated
    obtain ⟨ _, h0, _, h1 ⟩ := hWf
    replace h0 := h0 (i.val / 2) (by omega) (by omega)
    replace h1 := h1 (i.val / 2) (by omega) (by omega)
    have heq : 2 * (i.val / 2) = i ∨ 2 * (i.val / 2) + 1 = i := by omega
    cases heq <;> rename_i heq <;>
    fsimp [heq] at h0 h1 <;>
    scalar_tac

  @[progress] -- TODO: `local` doesn't work
  theorem update_acc_spec {f g : Array U16 256#usize} {B0 B1 : Nat} {i0 : Nat} {i : Usize} {c0 c1 : U32}
    {paDst0 paDst : Array U32 256#usize}
    {a1b1zetapow : U32}
    -- Those terms act as a pattern to automatically instantiate a1b1zetapow -- TODO: instantiation patterns for progress
    {a1b1: U32} {i0':Nat} (_ : (a1b1zetapow.val : Spec.Zq) = a1b1 * Spec.ζ ^ (2 * bitRev 7 i0' + 1))
    --
    (hwf : wfAcc f g B0 B1 i0 paDst0 paDst)
    (hi0 : i0 < 128)
    (hc0bound : c0.val ≤ B0 + B1) (hc1bound : c1.val ≤ B0 + B1)
    (hc0 : c0.val = paDst0[i.val]! + f[i.val]! * g[i.val]! + f[i.val + 1]! * g[i.val + 1]! * Spec.ζ ^ (2 * bitRev 7 i0 + 1))
    (hc1 : c1.val = paDst0[i.val + 1]! + f[i.val]! * g[i.val + 1]! + f[i.val + 1]! * g[i.val]!)
    (hi : i.val = 2 * i0) :
    ∃ paDst', update_acc i c0 c1 paDst = ok paDst' ∧
    wfAcc f g B0 B1 (i0 + 1) paDst0 paDst' := by
    rw [update_acc]
    progress*
    unfold wfAcc at *
    obtain ⟨ h0, h1, h2, h3 ⟩ := hwf
    -- TODO: this should be mostly automated
    split_conjs <;> intro j hj
    . dcases hjeq : j = i0
      . simp_lists_scalar [*]
      . simp_lists_scalar [*]
    . intro hj'
      simp_lists_scalar [*]
    . dcases hjeq : j = i0
      . fsimp [*]
        simp_lists
        have hi0 : 2 * i0 = i.val := by omega
        fsimp [hi0, hc0, hc1, SpecAux.baseCaseMultiply0 , SpecAux.baseCaseMultiply1]
        ring_nf
        fsimp
      . simp_lists [*]
    . intro hj'
      simp_lists [*]

  -- TODO: no post-processing of the post-conditions in progress

  @[simp, scalar_tac_simps, grind]
  abbrev montMulStepBound : Nat := 3328 * 3328 + 3328 * 3498

  theorem poly_element_mul_and_accumulate_loop_spec
    (peSrc1 peSrc2 : Array U16 256#usize)
    (paDst0 paDst : Array U32 256#usize) (i0 : Nat) (i : Usize)
    (B0 : Nat)
    (hb0 : B0 + montMulStepBound ≤ U32.max)
    (hwf1 : wfArray peSrc1) (hwf2 : wfArray peSrc2)
    (hwf3 : wfAcc peSrc1 peSrc2 B0 montMulStepBound i0 paDst0 paDst)
    (hi : i0 = i.val)
    :
    ∃ paDst', poly_element_mul_and_accumulate_loop peSrc1 peSrc2 paDst i = ok paDst' ∧
    wfAcc peSrc1 peSrc2 B0 montMulStepBound 128 paDst0 paDst'
    := by
    unfold poly_element_mul_and_accumulate_loop
    fsimp only [fold_mul_acc_mont_reduce, fold_update_acc]
    fsimp
    progress* by (scalar_tac +nonLin)
    fsimp [*]; ring_nf
    apply wfAcc_128 hwf3 (by scalar_tac)
  termination_by 128 - i.val
  decreasing_by scalar_decr_tac
end

attribute [local progress] poly_element_mul_and_accumulate_loop_spec

@[local progress]
theorem poly_element_mul_and_accumulate_spec
  (peSrc1 peSrc2 : Array U16 256#usize)
  (paDst : Array U32 256#usize)
  (B0 : Nat)
  (hBounds : ∀ j, j < 128 → paDst[2 * j]! ≤ B0 ∧ paDst[2 * j + 1]! ≤ B0)
  (hb0 : B0 + montMulStepBound ≤ U32.max)
  (hwf1 : wfArray peSrc1) (hwf2 : wfArray peSrc2)
  :
  ∃ paDst', poly_element_mul_and_accumulate peSrc1 peSrc2 paDst = ok paDst' ∧
  wfAcc peSrc1 peSrc2 B0 montMulStepBound 128 paDst paDst'
  := by
  unfold poly_element_mul_and_accumulate
  have hwf := wfAcc_zero peSrc1 peSrc2 B0 montMulStepBound paDst hBounds
  progress as ⟨ paDst1, hPost ⟩
  apply hPost

/-!
# Reduce and Add
-/

@[scalar_tac_simps, bvify_simps, grind] abbrev reduceAddInputBound : Nat := 4*3328*3328 + 4*3494*3312
@[scalar_tac_simps, bvify_simps, grind] abbrev reduceAddStepBound : Nat := 4711


section
  /-- Auxiliary helper: the reduced multiplication performed by reduce and add.

      This computes:
      red(a1b1) *
   -/
  private def reduce_add_mont_reduce (a : U32) : Result U32 := do
    let i2 ← core.num.U32.wrapping_mul a ntt.NEG_Q_INV_MOD_R
    let inv ← (↑(i2 &&& ntt.RMASK) : Result U32)
    let i3 ← inv * ntt.Q
    let i4 ← a + i3
    let a1 ← i4 >>> ntt.RLOG2
    pure a1

  -- TODO: automate the refold
  private theorem fold_reduce_add_mont_reduce (a : U32) (f : U32 → Result α) :
    (do
      let i2 ← core.num.U32.wrapping_mul a ntt.NEG_Q_INV_MOD_R
      let inv ← (↑(i2 &&& ntt.RMASK) : Result U32)
      let i3 ← inv * ntt.Q
      let i4 ← a + i3
      let a1 ← i4 >>> ntt.RLOG2
      f a1) =
    (do
      let a1 ← reduce_add_mont_reduce a
      f a1)
    := by
    simp only [reduce_add_mont_reduce, bind_assoc_eq, bind_tc_ok, pure]

  theorem mlKem_mont_reduce_bounds_reduce_add (x : Nat) (h : x ≤ reduceAddInputBound) :
    mont_reduce 3329 (2 ^ 16) 3327 x ≤ 4711 := by
    have := mont_reduce_bounds 3329 (2^16) 3327 reduceAddInputBound 3329 (by simp) (by native_decide)
    simp at *
    apply this x h

  @[local progress]
  theorem reduce_add_mont_reduce_spec (a : U32) (h1 : a.val ≤ reduceAddInputBound) :
    ∃ a1, reduce_add_mont_reduce a = ok a1 ∧
    a1.val ≤ reduceAddStepBound ∧
    (a1.val : Spec.Zq) = (a.val : Spec.Zq) * 169
    := by
    unfold reduce_add_mont_reduce
    let* ⟨ amul, amul_post ⟩ ← core.num.U32.wrapping_mul.progress_spec
    let* ⟨ inv, inv_post_1, inv_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ invq, invq_post_1, invq_post_2 ⟩ ← U32.mul_bv_spec
    let* ⟨ ainvq, ainvq_post_1, ainvq_post_2 ⟩ ← U32.add_bv_spec
    let* ⟨ a1, a1_post_1, a1_post_2 ⟩ ← U32.ShiftRight_spec

    /- Prove the result of the Montgomery reduction -/
    have ha1_eq : a1.val = (a.val + inv.val * Q.val) / 2^16 := by bv_tac 32
    have hPost1 : (a1.val : Spec.Zq) = (a.val : Spec.Zq) * 169 := by
      have ⟨ hMont, _ ⟩ := mont_reduce_spec 3329 (2^16) 3327 a.val
        (by fsimp [U16.size, U16.numBits]; exists 16) (by fsimp [U16.size, U16.numBits]) (by fsimp)
        (by scalar_tac) (by fsimp; constructor)
      fsimp [mont_reduce] at hMont
      fsimp [inv_post_1, amul_post, U32.size, U32.numBits] at ha1_eq
      zify at ha1_eq
      zify
      fsimp [ha1_eq, hMont]
      fsimp [Int.mul_emod]
    have hPost2 : a1.val ≤ 4711 := by
       have hBound := mlKem_mont_reduce_bounds_reduce_add a.val (by scalar_tac)
       fsimp [mont_reduce] at hBound
       fsimp [inv_post_1, amul_post, U32.size, U32.numBits] at ha1_eq
       zify at ha1_eq
       scalar_tac

    /- Finish -/
    fsimp [hPost1, hPost2]

  private def reduce_add_normalize (c1 : U32) : Result U32 := do
    let i5 ← 2#u32 * ntt.Q
    let c2 ← (↑(core.num.U32.wrapping_sub c1 i5) : Result U32)
    let i6 ← c2 >>> 16#i32
    let i7 ← (↑(ntt.Q &&& i6) : Result U32)
    let c3 ← (↑(core.num.U32.wrapping_add c2 i7) : Result U32)
    let i8 ← c3 >>> 16#i32
    let i9 ← (↑(ntt.Q &&& i8) : Result U32)
    let c4 ← (↑(core.num.U32.wrapping_add c3 i9) : Result U32)
    pure c4

  -- TODO: automate the refold
  private theorem fold_reduce_add_normalize (a : U32) (f : U32 → Result α) :
    (do
      let i5 ← 2#u32 * ntt.Q
      let c2 ← (↑(core.num.U32.wrapping_sub a i5) : Result U32)
      let i6 ← c2 >>> 16#i32
      let i7 ← (↑(ntt.Q &&& i6) : Result U32)
      let c3 ← (↑(core.num.U32.wrapping_add c2 i7) : Result U32)
      let i8 ← c3 >>> 16#i32
      let i9 ← (↑(ntt.Q &&& i8) : Result U32)
      let c4 ← (↑(core.num.U32.wrapping_add c3 i9) : Result U32)
      f c4) =
    (do
      let c4 ← reduce_add_normalize a
      f c4)
    := by
    simp only [reduce_add_normalize, bind_assoc_eq, bind_tc_ok, pure]

  @[local progress]
  theorem reduce_add_normalize_spec (a : U32) (h1 : a.val ≤ 3328 + reduceAddStepBound) :
    ∃ a1, reduce_add_normalize a = .ok a1 ∧
    a1.val ≤ 3328 ∧
    (a1.val : Spec.Zq) = (a.val : Spec.Zq) := by
    unfold reduce_add_normalize
    let* ⟨ i5, i5_post_1, i5_post_2 ⟩ ← U32.mul_bv_spec
    let* ⟨ c2, c2_post ⟩ ← core.num.U32.wrapping_sub.progress_spec
    let* ⟨ i6, i6_post_1, i6_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨ i7, i7_post_1, i7_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ c3, c3_post ⟩ ← core.num.U32.wrapping_add.progress_spec
    let* ⟨ i8, i8_post_1, i8_post_2 ⟩ ← U32.ShiftRight_IScalar_spec
    let* ⟨ i9, i9_post_1, i9_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ c4, c4_post ⟩ ← core.num.U32.wrapping_add.progress_spec

    have : (c4.val : Spec.Zq) = (a.val : Spec.Zq) ∧ c4.val ≤ 3328 := by bv_tac 32
    fsimp [this]

  attribute [-progress] wfArray_index wfArray_update
  attribute [local progress] Array.index_usize_spec Array.update_spec

  -- TODO: better elaboration of let (x, y) ← ...
  theorem montgomery_reduce_and_add_poly_element_accumulator_to_poly_element_loop_spec
    (paSrc0 paSrc : Array U32 256#usize)
    (paDst0 paDst : Array U16 256#usize)
    (i : Usize)
    -- Assumptions about the source
    (hsrcBeg : ∀ j < i.val, paSrc[j]! = 0#u32)
    (hsrcEndEq : ∀ j ≥ i.val, j < 256 → paSrc[j]! = paSrc0[j]!)
    (hsrcEndIneq : ∀ j ≥ i.val, j < 256 → paSrc0[j]! ≤ reduceAddInputBound)
    -- Assumptions about the destination
    (hdstBegIneq : ∀ j < i.val, paDst[j]!.val ≤ 3328)
    (hdstBegEq : ∀ j < i.val, (paDst[j]! : Spec.Zq) = (paDst0[j]! : Spec.Zq) + (paSrc0[j]! : Spec.Zq) * 169)
    (hdstEndIneq : ∀ j ≥ i.val, j < 256 → paDst0[j]!.val ≤ 3328)
    (hdstEndEq : ∀ j ≥ i.val, j < 256 → paDst[j]!.val = paDst0[j]!)
    --
    :
    ∃ paSrc1 paDst1, montgomery_reduce_and_add_poly_element_accumulator_to_poly_element_loop paSrc paDst i = ok (paSrc1, paDst1) ∧
    --
    (∀ j < 256, paSrc1[j]! = 0#u32) ∧
    (∀ j < 256, paDst1[j]!.val ≤ 3328) ∧
    (∀ j < 256, (paDst1[j]!.val : Spec.Zq) = (paDst0[j]!.val : Spec.Zq) + (paSrc0[j]!.val : Spec.Zq) * 169)
    := by
    unfold montgomery_reduce_and_add_poly_element_accumulator_to_poly_element_loop
    fsimp only [fold_reduce_add_mont_reduce, fold_reduce_add_normalize]
    fsimp

    split
    . let* ⟨ a, a_post ⟩ ← Array.index_usize_spec
      have : a.val ≤ reduceAddInputBound := by simp_lists_scalar [*]
      let* ⟨ paSrc1, paSrc1_post ⟩ ← Array.update_spec
      let* ⟨ i1, i1_post_1 ⟩ ← Array.index_usize_spec
      have : i1.val ≤ 3328 := by simp_lists_scalar [*]
      let* ⟨ a1, a1_post_1, a1_post_2 ⟩ ← reduce_add_mont_reduce_spec
      let* ⟨ c1, c1_post_1, c1_post_2 ⟩ ← U32.add_bv_spec
      let* ⟨ c4, c4_post_1, c4_post_2 ⟩ ← reduce_add_normalize_spec
      let* ⟨ i10, i10_post ⟩ ← UScalar.cast_inBounds_spec
      let* ⟨ paDst1, paDst1_post ⟩ ← Array.update_spec
      let* ⟨ i11, i11_post ⟩ ← Usize.add_spec

      -- TODO: this should be automated
      have : ∀ j < i11.val, paSrc1[j]! = 0#u32 := by
        intro j hj; dcases hji : j = i.val <;> simp_lists [*]

      have : ∀ j ≥ i11.val, j < 256 → paSrc1[j]! = paSrc0[j]! := by
        intro j hj0 hj1
        dcases hji : j = i.val + 1 <;> simp_lists [*]

      have : ∀ j ≥ i11.val, j < 256 → paSrc0[j]!.val ≤ reduceAddInputBound := by
        intro j hj0 hj1
        dcases hji : j = i.val + 1 <;> simp_lists [*]

      have : ∀ j < i11.val, paDst1[j]!.val ≤ 3328 := by
        intro j hj0
        dcases hji : j = i.val <;> simp_lists [*]

      have : ∀ j < i11.val, (paDst1[j]!.val : Spec.Zq) = ↑↑paDst0[j]! + ↑↑paSrc0[j]! * 169 := by
        intro j hj
        dcases hji : j = i.val <;> simp_lists_scalar [*]

      have : ∀ j ≥ i11.val, j < 256 → paDst0[j]!.val ≤ 3328 := by
        intro j hj0 hj1
        dcases hji : j = i.val + 1 <;> simp_lists [*]

      have : ∀ j ≥ i11.val, j < 256 → paDst1[j]!.val = ↑paDst0[j]! := by
        intro j hj0 hj1
        dcases hji : j = i.val + 1 <;> simp_lists [*]

      let* ⟨ res_1, res_2, res_post_1, res_post_2, res_post_3 ⟩ ←
        montgomery_reduce_and_add_poly_element_accumulator_to_poly_element_loop_spec paSrc0 paSrc1 paDst0 paDst1
      fsimp at *
      split_conjs
      . apply res_post_1
      . apply res_post_2
      . apply res_post_3
    . fsimp at *
      split_conjs <;> intros j hj
      . apply hsrcBeg; scalar_tac
      . apply hdstBegIneq; scalar_tac
      . apply hdstBegEq; scalar_tac
  termination_by 256 - i.val
  decreasing_by scalar_decr_tac

end

attribute [local progress] montgomery_reduce_and_add_poly_element_accumulator_to_poly_element_loop_spec

@[local progress]
theorem montgomery_reduce_and_add_poly_element_accumulator_to_poly_element_spec
    (paSrc : Array U32 256#usize)
    (paDst : Array U16 256#usize)
    -- Assumptions about the source
    (hsrcEndIneq : ∀ j < 256, paSrc[j]!.val ≤ reduceAddInputBound)
    -- Assumptions about the destination
    (hdst : ∀ j < 256, paDst[j]!.val ≤ 3328)
    --
    :
    ∃ paSrc1 paDst1, montgomery_reduce_and_add_poly_element_accumulator_to_poly_element paSrc paDst = ok (paSrc1, paDst1) ∧
    --
    (∀ j < 256, paSrc1[j]! = 0#u32) ∧
    (∀ j < 256, paDst1[j]!.val ≤ 3328) ∧
    (∀ j < 256, (paDst1[j]!.val : Spec.Zq) = (paDst[j]!.val : Spec.Zq) + (paSrc[j]!.val : Spec.Zq) * 169) := by
    unfold montgomery_reduce_and_add_poly_element_accumulator_to_poly_element

    -- TODO: progress by
    progress with montgomery_reduce_and_add_poly_element_accumulator_to_poly_element_loop_spec paSrc paSrc paDst paDst as ⟨ paSrc1, paDst1 ⟩
    grind
/-
# MulR
-/

attribute [-progress] mont_mul_twiddle_spec -- TODO: this shouldn't be marked with `progress`
attribute [local progress] mont_mul_spec

@[local progress]
theorem poly_element_mul_r_loop_spec
  (peSrc : Array U16 256#usize) (peDst : Array U16 256#usize) (i : Usize)
  (hwf : wfArray peSrc)
  :
  ∃ peDst1, poly_element_mul_r_loop peSrc peDst i = ok peDst1 ∧
  (∀ j < i.val, peDst1[j]! = peDst[j]!) ∧
  (∀ j ≥ i.val, j < 256 → (peDst1[j]! : Spec.Zq) = peSrc[j]! * 2^16) := by
  unfold poly_element_mul_r_loop
  split
  . let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← wfArray_index
    let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← mont_mul_spec by (fsimp [*])
    let* ⟨ i4, i4_post ⟩ ← UScalar.cast_inBounds_spec
    let* ⟨ peDst1, peDst1_post ⟩ ← Array.update_spec
    let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
    let* ⟨ peDest2, res_post_1, res_post_2 ⟩ ← poly_element_mul_r_loop_spec
    -- TODO: this hould be automated
    split_conjs
    . intros j hj
      fsimp at *
      simp_lists [res_post_1]
      fsimp [*]
    . intros j hj0 hj1
      fsimp at *
      dcases hj : j = i.val
      . fsimp [*]
        ring_nf
        fsimp
      . simp_lists_scalar [res_post_2]
  . fsimp
    intro j hj0 hj1
    -- Contradiction
    scalar_tac
termination_by 256 - i.val
decreasing_by scalar_decr_tac

@[local progress]
theorem poly_element_mul_r_spec
  (peSrc : Array U16 256#usize) (peDst : Array U16 256#usize)
  (hwf : wfArray peSrc) :
  ∃ peDst1, poly_element_mul_r peSrc peDst = ok peDst1 ∧
  (∀ j < 256, (peDst1[j]!.val : Spec.Zq) = peSrc[j]!.val * 2^16) := by
  unfold poly_element_mul_r
  progress as ⟨ peDst1 ⟩
  -- TODO: this should be automated
  fsimp at *
  assumption

/-!
# Add
-/
@[local progress]
def poly_element_add_loop_spec
  (peSrc1 : Array U16 256#usize) (peSrc2 : Array U16 256#usize)
  (peDst : Array U16 256#usize) (i : Usize)
  (hwf1 : wfArray peSrc1) (hwf2 : wfArray peSrc2) :
  ∃ peDst1, poly_element_add_loop peSrc1 peSrc2 peDst i = ok peDst1 ∧
  (∀ j < i.val, peDst1[j]!.val = peDst[j]!.val) ∧
  (∀ j ≥ i.val, j < 256 → peDst1[j]!.val ≤ 3328) ∧
  (∀ j ≥ i.val, j < 256 → (peDst1[j]!.val : Spec.Zq) = peSrc1[j]! + peSrc2[j]!) := by
  unfold poly_element_add_loop
  split
  . let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← wfArray_index
    let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← wfArray_index
    let* ⟨ i5, i5_post_1, i5_post_2 ⟩ ← mod_add_spec
    let* ⟨ i6, i6_post ⟩ ← UScalar.cast_inBounds_spec
    let* ⟨ peDst1, peDst1_post ⟩ ← Array.update_spec -- TODO: by default it is wfArray_update
    let* ⟨ i7, i7_post ⟩ ← Usize.add_spec
    let* ⟨ peDst2, peDst2_post_1, peDst2_post_2, peDst2_post_3 ⟩ ← poly_element_add_loop_spec
    -- TODO: this should be automated
    fsimp at *
    split_conjs
    . intro j hj
      simp_lists [peDst2_post_1, peDst1_post, Array.set_val_eq]
    . intro j hj0 hj1
      dcases hji : i.val = j
      . fsimp [*]; scalar_tac
      . simp_lists [peDst2_post_2]
    . intro j hj0 hj1
      dcases hji : i.val = j
      . fsimp [*]
      . simp_lists_scalar [peDst2_post_3]
  . fsimp at *
    split_conjs <;> intros <;> scalar_tac -- Contradiction
termination_by 256 - i.val
decreasing_by scalar_decr_tac

@[local progress]
def poly_element_add_spec
  (peSrc1 : Array U16 256#usize) (peSrc2 : Array U16 256#usize)
  (peDst : Array U16 256#usize)
  (hwf1 : wfArray peSrc1) (hwf2 : wfArray peSrc2) :
  ∃ peDst1, poly_element_add peSrc1 peSrc2 peDst = ok peDst1 ∧
  (∀ j < 256, peDst1[j]!.val ≤ 3328) ∧
  (∀ j < 256, (peDst1[j]!.val : Spec.Zq) = peSrc1[j]!.val + peSrc2[j]!.val) := by
  unfold poly_element_add
  progress
  -- TODO: this should be automated
  fsimp at *
  split_conjs <;> assumption

/-!
# Sub
-/
@[local progress]
def poly_element_sub_loop_spec
  (peSrc1 : Array U16 256#usize) (peSrc2 : Array U16 256#usize)
  (peDst : Array U16 256#usize) (i : Usize)
  (hwf1 : wfArray peSrc1) (hwf2 : wfArray peSrc2) :
  ∃ peDst1, poly_element_sub_loop peSrc1 peSrc2 peDst i = ok peDst1 ∧
  (∀ j < i.val, peDst1[j]!.val = peDst[j]!.val) ∧
  (∀ j ≥ i.val, j < 256 → peDst1[j]!.val ≤ 3328) ∧
  (∀ j ≥ i.val, j < 256 → (peDst1[j]!.val : Spec.Zq) = peSrc1[j]! - peSrc2[j]!) := by
  unfold poly_element_sub_loop
  split
  . let* ⟨ i1, i1_post_1, i1_post_2 ⟩ ← wfArray_index
    let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← wfArray_index
    let* ⟨ i5, i5_post_1, i5_post_2 ⟩ ← mod_sub'_spec
    let* ⟨ i6, i6_post ⟩ ← UScalar.cast_inBounds_spec
    let* ⟨ peDst1, peDst1_post ⟩ ← Array.update_spec -- TODO: by default it is wfArray_update
    let* ⟨ i7, i7_post ⟩ ← Usize.add_spec
    let* ⟨ peDst2, peDst2_post_1, peDst2_post_2, peDst2_post_3 ⟩ ← poly_element_sub_loop_spec
    -- TODO: this should be automated
    fsimp at *
    split_conjs
    . intro j hj
      simp_lists [peDst2_post_1, peDst1_post, Array.set_val_eq]
    . intro j hj0 hj1
      dcases hji : i.val = j
      . fsimp [*]; scalar_tac
      . simp_lists [peDst2_post_2]
    . intro j hj0 hj1
      dcases hji : i.val = j
      . fsimp [*]
      . simp_lists_scalar [peDst2_post_3]
  . fsimp at *
    split_conjs <;> intros <;> scalar_tac -- Contradiction
termination_by 256 - i.val
decreasing_by scalar_decr_tac

@[local progress]
def poly_element_sub_spec
  (peSrc1 : Array U16 256#usize) (peSrc2 : Array U16 256#usize)
  (peDst : Array U16 256#usize)
  (hwf1 : wfArray peSrc1) (hwf2 : wfArray peSrc2) :
  ∃ peDst1, poly_element_sub peSrc1 peSrc2 peDst = ok peDst1 ∧
  (∀ j < 256, peDst1[j]!.val ≤ 3328) ∧
  (∀ j < 256, (peDst1[j]!.val : Spec.Zq) = peSrc1[j]!.val - peSrc2[j]!.val) := by
  unfold poly_element_sub
  progress
  -- TODO: this should be automated
  fsimp at *
  split_conjs <;> assumption

end ntt

end Symcrust
