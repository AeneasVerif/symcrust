import Symcrust.Spec
import Symcrust.Properties.Polynomials

/-!
An auxiliary specification that we use to prove a refinement result.
This specification refines the specification in `Spec`, and is refined by the code.
It does not need to be trusted.
-/

attribute [-simp] List.getElem!_eq_getElem?_getD List.reduceReplicate Aeneas.SRRange.foldWhile_step

-- TODO: move and update Array.update_subslice to use it
def List.setSlice! {α} (s : List α) (i : ℕ) (s' : List α) : List α := sorry

def Array.setSlice! {α} (a : Array α) (i : ℕ) (s : List α) : Array α := sorry

def Vector.setSlice! {α} {n} (x : Vector α n) (i : ℕ) (s : List α) : Vector α n := sorry

/-!
# Conversion to little-endian
-/
open Symcrust.Spec -- for Bytes

def BitVec.toLEBytes {n : ℕ} (b : BitVec n) : List Byte :=
  if n > 0 then
    b.setWidth 8 :: BitVec.toLEBytes ((b >>> 8).setWidth (n - 8))
  else []

def BitVec.toBEBytes {n : ℕ} (b : BitVec n) : List Byte :=
  List.reverse b.toLEBytes

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

--open Aeneas.Notations.SRRange
--open Aeneas.Notations.DivRange
--open Aeneas.Notations.MulRange
--open Aeneas.Notations.Range
--open Spec.Notations

/-!
# BitVec
-/

-- TODO: move
@[simp, bvify_simps]
theorem BitVec.ofNat_mul (n : ℕ) (x y : ℕ) : BitVec.ofNat n (x * y) = BitVec.ofNat n x * BitVec.ofNat n y := by
  conv => lhs; unfold BitVec.ofNat
  conv => rhs; simp only [BitVec.mul_def]
  simp only [Fin.ofNat'_eq_cast, Nat.cast_mul, BitVec.toFin_ofNat]

-- TODO: move
theorem BitVec.ofNat_pow (n : ℕ) (x d : ℕ) : BitVec.ofNat n (x ^ d) = (BitVec.ofNat n x)^d := by
  conv => rhs; unfold HPow.hPow instHPow Pow.pow BitVec.instPowNat_mathlib; simp only
  unfold BitVec.ofNat
  simp only [Fin.ofNat'_eq_cast, Nat.cast_pow]

@[simp]
theorem BitVec.toNat_pow (n : ℕ) (x : BitVec n) (d : ℕ) :
  BitVec.toNat (x ^ d) = (x.toNat^d) % 2^n := by sorry


-- TODO: move
attribute [simp_lists_simps] and_true true_and implies_true

/-!
# byteEncode

TODO: remove those?
-/

def byteEncodeToBits {n} (d : ℕ) (f : List (ZMod n)) : List Bool :=
  List.flatten (List.map (fun a => (List.map (fun i => a.val.testBit i) (List.range d))) f)

def bitsToBytes1 (l : ℕ) (b : List Bool) : List Byte :=
  List.map (fun i => BitVec.ofBoolListLE (List.map (fun j => b[8 * i + j]!) (List.range 8))) (List.range l)

def encodeNatToBytes (d : ℕ) (coeff : ℕ) (nBitsInAcc : ℕ) (nBitsInCoeff : ℕ) (acc : List Bool)
  (hBitsInAcc : nBitsInAcc < 32 := by omega)
  : List Byte :=
  let nBitsToEncode := min nBitsInCoeff (32 - nBitsInAcc)
  let bitsToEncode := List.take nBitsToEncode coeff.bits
  let nBitsInCoeff := nBitsInCoeff - nBitsToEncode
  let acc := acc ++ bitsToEncode
  let nBitsInAcc := nBitsInAcc + nBitsToEncode
  if h: nBitsInAcc = 32 then
    let out := BitVec.toLEBytes (BitVec.ofBoolListLE acc)
    if h: nBitsInCoeff > 0 then
      out ++ encodeNatToBytes d coeff 0 nBitsInCoeff []
    else out
  else
    if h: nBitsInCoeff > 0 then encodeNatToBytes d coeff nBitsInAcc nBitsInCoeff acc
    else []
termination_by nBitsInCoeff
decreasing_by
  scalar_decr_tac
  scalar_decr_tac

/-!
# Auxiliary theorems
TODO: move
-/

-- TODO: move
@[simp]
def List.Inhabited_getElem_eq_getElem! {α} [Inhabited α] (l : List α) (i : ℕ) (hi : i < l.length) :
  l[i] = l[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some, hi]

attribute [-simp] Array.set!_eq_setIfInBounds

-- TODO: move
@[simp]
theorem Array.set_eq_set! (a : Array α) (i : ℕ) (x : α) (hi : i < a.size) :
  a.set i x hi = a.set! i x := by
  simp only [Array.set, Array.set!, Array.setIfInBounds, hi, ↓reduceDIte]

-- TODO: move
@[simp]
theorem Vector.set_eq_set! (v : Vector α n) (i : ℕ) (x : α) (hi : i < n) :
  v.set i x hi = v.set! i x := by
  simp only [Vector.set, Array.set_eq_set!, Vector.set!]

@[simp]
def Array.Inhabited_getElem_eq_getElem! {α} [Inhabited α] (l : Array α) (i : ℕ) (hi : i < l.size) :
  l[i] = l[i]! := by
  sorry

@[simp]
def Vector.Inhabited_getElem_eq_getElem! {α} [Inhabited α] (l : Vector α n) (i : ℕ) (hi : i < n) :
  l[i] = l[i]! := by
  sorry

-- TODO: move
@[simp, simp_lists_simps]
theorem Array.getElem!_default {α : Type u} [Inhabited α] (a : Array α) (i : ℕ) (hi : a.size ≤ i) :
  a[i]! = default := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hi, Array.getElem?_eq_none,
    Option.getD_none]

@[simp, simp_lists_simps]
theorem Vector.getElem!_default {α : Type u} [Inhabited α] {n} (v : Vector α n) (i : ℕ) (hi : n ≤ i) :
  v[i]! = default := by
  unfold getElem! instGetElem?OfGetElemOfDecidable decidableGetElem?
  simp only [Inhabited_getElem_eq_getElem!, dite_eq_ite]
  simp_ifs
  rfl

set_option maxHeartbeats 500000

-- TODO: remove
@[local simp]
theorem MProd_mk_eq (x : MProd α β) : ⟨ x.fst, x.snd ⟩ = x := by simp only

attribute [-simp] foldl_range'_eq_foldWhile

-- TODO: this pattern often appears
@[simp]
theorem List.foldl_Prod_to_MProd_fst_eq {α β : Type u} {γ : Type v} (f : α → β → γ → α × β)
  (a0 : α) (b0 : β) (l) :
  (List.foldl (fun b a => MProd.mk (f b.fst b.snd a).fst (f b.fst b.snd a).snd) ⟨a0, b0⟩ l).fst =
  (List.foldl (fun b a => (f b.fst b.snd a)) (a0, b0) l).fst := by sorry

-- TODO: this pattern often appears
@[simp]
theorem List.foldl_Prod_to_MProd_snd_eq {α β : Type u} {γ : Type v} (f : α → β → γ → α × β)
  (a0 : α) (b0 : β) (l) :
  (List.foldl (fun b a => MProd.mk (f b.fst b.snd a).fst (f b.fst b.snd a).snd) ⟨a0, b0⟩ l).snd =
  (List.foldl (fun b a => (f b.fst b.snd a)) (a0, b0) l).snd := by sorry

-- TODO: simp_lists on vectors and arrays

@[simp, simp_lists_simps]
theorem Vector.set!_getElem!_eq {α : Type u}
  [Inhabited α] {n i j : ℕ} {x : α} {xs : Vector α n}
  (hi : i < n ∧ j = i) :
  (xs.set! i x)[j]! = x := by sorry

@[simp, simp_lists_simps]
theorem Vector.set!_getElem!_neq {α : Type u}
  [Inhabited α] {n i j : ℕ} {x : α} {xs : Vector α n}
  (h : i < n ∧ j < n ∧ i ≠ j) :
  (xs.set! i x)[j]! = xs[j]! := by sorry

@[simp]
theorem decide_eq_not_decide (a b : Prop) [Decidable a] [Decidable b] :
  decide a = !decide b ↔ a = ¬ b := by
  constructor <;> intros h
  sorry
  sorry

@[simp]
theorem not_decide_eq_decide (a b : Prop) [Decidable a] [Decidable b] :
  !decide a = decide b ↔ ¬ a = b := by
  constructor <;> intros h
  sorry
  sorry

/-!
# bitsToBytes
-/

def Target.bitsToBytes.body
  {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) (i : ℕ) :
  Vector Byte l :=
  B.set! (i/8) (B[i/8]!  + BitVec.ofNat 8 (Bool.toNat b[i]!) * BitVec.ofNat 8 (2 ^(i%8)))

def Target.bitsToBytes.recBody
  {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) (i : ℕ) :
  Vector Byte l :=
  List.foldl (body b) B (List.range' i (8 * l - i))

def Target.bitsToBytes {l : Nat} (b : Vector Bool (8 * l)) : Vector Byte l :=
  bitsToBytes.recBody b (Vector.replicate l 0) 0

-- TODO: remove this simp lemma
attribute [-simp] foldl_range'_eq_foldWhile

theorem Target.bitsToBytes.eq_spec {l : Nat} (b : Vector Bool (8 * l)) :
  bitsToBytes b = Spec.bitsToBytes b := by
  unfold bitsToBytes Spec.bitsToBytes recBody body
  simp [Id.run]

theorem Target.bitsToBytes.recBody.step_eq
  {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) (i : ℕ)
  (hi : i < 8 * l) :
  recBody b B i = recBody b (body b B i) (i + 1) := by
  unfold recBody
  have : 8 * l - i = (8 * l - (i+1)) + 1 := by omega
  simp [this, List.range'_succ]

irreducible_def Target.bitsToBytes.inv
  {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) (i j : ℕ) :=
  -- The prefix is properly set
  (∀ i' < i, ∀ j' < 8, B[i']!.testBit j' = b[8*i' + j']!) ∧
  -- We are updating the value at index i
  (∀ j' < j, B[i]!.testBit j' = b[8*i + j']!) ∧
  (i < l → ∀ j' ∈ [j:8], B[i]!.testBit j' = false) ∧
  -- The suffix is made of zeros
  (∀ i' ∈ [i+1:l], B[i']! = 0)

-- TODO: remove?
@[local simp]
theorem mem_range'_step_one (x start len : ℕ) :
  x ∈ List.range' start len ↔ (start ≤ x ∧ x < start + len) := by
  simp [List.mem_range']
  constructor <;> intro h
  . obtain ⟨ i, h ⟩ := h
    omega
  . exists x - start
    omega

@[local simp]
theorem mem_std_range_step_one (x n0 n1 : ℕ) :
  x ∈ [n0:n1] ↔ (n0 ≤ x ∧ x < n1) := by
  simp [Membership.mem, Nat.mod_one]

@[local simp]
theorem decompose_ij (i j : ℕ) (hj : j < 8) :
  (8 * i + j) / 8 = i ∧ (8 * i + j) % 8 = j := by
  omega

def Target.bitsToBytes.body.spec
  {l:Nat} {b : Vector Bool (8 * l)} {B : Vector Byte l} {i j : ℕ} (hinv : inv b B i j)
  (hi : i < l) (hj : j < 8) :
  inv b (body b B (8 * i + j)) i (j + 1) := by
  simp only [body, inv] at *
  simp at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  split_conjs
  . intro i' hi' j' hj'
    simp_lists [h0]
  . -- This is the complex part of the proof, where we have
    -- to reason about bitwise manipulations
    intros j' hj'
    simp [hj, hj']
    simp_lists
    cases hb: b[8 * i + j]! <;> simp [hb]
    . by_cases hj'': j' = j
      . simp_all
      . have : j' < j := by omega
        simp_lists [h1]
    . have : j % 8 = j := by omega
      simp [this]; clear this
      simp [Byte.testBit]
      have : 256 = 2^8 := by rfl
      rw [this]; clear this
      simp only [Nat.testBit_mod_two_pow]
      have : j' < 8 := by omega
      simp [this]; clear this
      have : BitVec.toNat B[i]! + 2 ^ j = 2 ^ j + BitVec.toNat B[i]! := by ring_nf
      rw [this]; clear this
      by_cases hj'': j' = j
      . simp [hj'']
        simp [Nat.testBit_two_pow_add_eq]
        simp [hb]
        simp_lists [h2]
      . have hj'' : j' < j := by omega
        simp [Nat.testBit_two_pow_add_gt, hj'']
        simp_lists [h1]
  . intros hi' j' hj' hj''
    simp_lists
    simp [hj, hj'']
    cases hb: b[8 * i + j]! <;> simp
    . by_cases hj''': j' = j
      . simp_lists
        simp [default, Byte.testBit]
      . simp_lists [h2]
    . have : j % 8 = j := by omega
      rw [this]; clear this
      simp [Byte.testBit]
      have : 256 = 2^8 := by rfl
      rw [this]; clear this
      simp only [Nat.testBit_mod_two_pow]
      simp; intro _
      have : BitVec.toNat B[i]! + 2 ^ j = 2 ^ j + BitVec.toNat B[i]! := by ring_nf
      rw [this]
      /- This proof is also subtle.
         We use the fact that: `B[i] < 2^j`
         which itself derives from the fact that: `∀ j' < j, B[i].testBit j' = 0`
      -/
      have : B[i]!.toNat < 2^j := by
        have hj : (BitVec.toNat B[i]!).testBit j = false := by
          simp_lists [h2]
        have := @Nat.lt_of_testBit (BitVec.toNat B[i]!) (2^j) j hj (by simp)
        apply this
        intro k hk
        simp [Nat.testBit_two_pow]
        by_cases hk' : k < 8
        . simp_lists [h2]
          simp
          omega
        . simp at hk'
          have : BitVec.toNat B[i]! < 2^8 := by omega
          have : BitVec.toNat B[i]! < 2 ^ k := by
            -- TODO: scalar_tac +nonLin
            have : 2^8 ≤ 2^k := by
              apply Nat.pow_le_pow_right <;> omega
            omega
          rw [Nat.testBit_eq_false_of_lt]
          . simp; omega
          . omega
      have : ((2^j + B[i]!.toNat) >>> j).testBit (j' - j) = (2^j + B[i]!.toNat).testBit j' := by
        simp
        have : j + (j' - j) = j' := by omega
        simp [this]
      rw [← this]
      simp [Nat.shiftRight_eq_div_pow]
      have : BitVec.toNat B[i]! / 2 ^ j = 0 := by
        apply Nat.div_eq_of_lt
        omega
      simp [this]
      have : j' - j = (j' - j - 1) + 1 := by omega
      rw [this]
      simp [Nat.testBit_add_one]
  . intros i' hi' hi''
    simp_lists [h3]

-- TODO: simp_lists simplifies and_true true_and, etc.

theorem Target.bitsToBytes.inv_8_imp_inv {l:Nat}
  {b : Vector Bool (8 * l)} {B : Vector Byte l} {i : ℕ}
  (hinv : inv b B i 8) :
  inv b B (i + 1) 0 := by
  simp only [inv] at *; simp at *
  obtain ⟨ h0, h1, h2 ⟩ := hinv
  split_conjs
  . intro i' hi' j' hj'
    by_cases hi'': i' = i
    . simp [hi'']
      simp_lists [h1]
    . simp_lists [h0]
  . intros hi' j' hj'
    have : B[i+1]! = 0#8 := by
      simp_lists [h2]
    simp [this, Byte.testBit]
  . simp_lists [*]

-- TODO: this one is useless
theorem Target.bitsToBytes.inv_0_imp {l:Nat}
  {b : Vector Bool (8 * l)} {B : Vector Byte l} {i : ℕ}
  (hinv : inv b B (i + 1) 0) :
  inv b B i 8 := by
  simp only [inv] at *; simp at *
  obtain ⟨ h0, h1, h2 ⟩ := hinv
  split_conjs
  . simp_lists [*]
  . simp_lists [*]
  . intros i' hi' hi''
    by_cases hi''': i' = i + 1
    . simp [← hi'''] at h1
      have : ∀ j < 8, B[i']!.testBit j = false := by
        simp_lists [h1]
      natify; simp
      apply Nat.eq_of_testBit_eq; simp
      intros j
      by_cases hj: j < 8
      . simp_lists [h1]
      . simp at hj
        have : B[i']!.toNat < 2^j := by
          -- TODO: scalar_tac +nonLin
          have : B[i']!.toNat < 2^8 := by omega
          have : 2^8 ≤ 2^j := by
            apply Nat.pow_le_pow_right <;> omega
          omega
        have := Nat.testBit_eq_false_of_lt this
        apply this
    . simp_lists [h2]

theorem Target.bitsToBytes.inv_last_imp {l:Nat}
  {b : Vector Bool (8 * l)} {B : Vector Byte l} (i j : ℕ)
  (hi : l ≤ i)
  (hinv : inv b B i j) :
  inv b B l 0 := by
  simp [inv] at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  split_conjs
  . intros i' hi' j' hj'
    simp_lists [h0]
  . intros i' hi' hi''
    simp_lists [h3]

def Target.bitsToBytes.recBody.spec
  {l:Nat} {b : Vector Bool (8 * l)} {B : Vector Byte l} {i j : ℕ}
  (hinv : inv b B i j) (hi : i ≤ l) (hj : j ≤ 8) :
  inv b (recBody b B (8 * i + j)) l 0 := by
  if hi': i = l then
    -- We're done
    apply Target.bitsToBytes.inv_last_imp i j
    . omega
    . unfold recBody
      have : 8 * l - (8 * i + j) = 0 := by omega
      simp [this]
      apply hinv
  else
    -- Increment j if possible
    if hj': j = 8 then
      simp [hj'] at hinv ⊢
      have hinv1 := Target.bitsToBytes.inv_8_imp_inv hinv
      have hinv2 := spec hinv1 (by omega) (by omega)
      simp +arith at hinv2 ⊢
      apply hinv2
    else
      --simp at *
      rw [Target.bitsToBytes.recBody.step_eq]; swap; omega
      generalize hacc1 : body b B (8 * i + j) = acc1 at *
      have hinv1 := Target.bitsToBytes.body.spec hinv (by omega) (by omega)
      rw [hacc1] at hinv1
      have hinv2 := spec hinv1 (by omega) (by omega)
      simp +arith at *
      apply hinv2
termination_by (l - i, 8 - j)
decreasing_by all_goals (simp_wf; omega)

irreducible_def Target.bitsToBytes.post {l:Nat} (b : Vector Bool (8 * l)) (B : Vector Byte l) :=
  ∀ i < l, ∀ j < 8, B[i]!.testBit j = b[8*i + j]!


-- TODO: move
attribute [simp_lists_simps] List.getElem!_replicate

-- TODO: move
@[simp, simp_lists_simps]
theorem Array.getElem!_replicate {α : Type u} [Inhabited α] {i n : ℕ} {a : α} (h : i < n) :
  (Array.replicate n a)[i]! = a := by
  unfold getElem! Array.instGetElem?NatLtSize Array.get!Internal
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  simp_ifs
  simp

-- TODO: move
@[simp, simp_lists_simps]
theorem Vector.getElem!_replicate {α : Type u} [Inhabited α] {i n : ℕ} {a : α} (h : i < n) :
 (Vector.replicate n a)[i]! = a := by
 unfold getElem! instGetElem?OfGetElemOfDecidable Vector.instGetElemNatLt decidableGetElem? Vector.get
 simp; simp_lists
 split_ifs
 simp

def Target.bitsToBytes.spec {l:Nat} (b : Vector Bool (8 * l)) :
  post b (bitsToBytes b) := by
  have hinv0 : inv b (Vector.replicate l 0) 0 0 := by
    simp [inv, Byte.testBit]
    split_conjs <;> simp_lists; simp
  have hinv1 := recBody.spec hinv0 (by omega) (by omega)
  simp at hinv1
  simp [inv] at hinv1
  obtain ⟨ h0, h1 ⟩ := hinv1
  unfold bitsToBytes
  simp [post]
  -- TODO: introduce notation for this, plus apply symmetry to the equation
  generalize hacc1 : recBody b (Vector.replicate l 0#8) 0 = acc1 at *
  intro i hi j hj
  simp_lists [h0]

/-!
# bytesToBits
-/

attribute [-simp] Array.set!_eq_setIfInBounds

def byteToBits (b : Byte) : Vector Bool 8 := b.toNat.bitsn 8

def Target.byteToBits.body {l : Nat}
  (i : ℕ)
  (res : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (j : ℕ) : MProd (Vector Byte l) (Vector Bool (8 * l)) :=
  let C := res.fst
  let b := res.snd
  let b := b.set! (8*i + j) ((C[i]!) % 2 ≠ 0)
  let C := C.set! i (C[i]! / 2)
  ⟨ C, b ⟩

def Target.byteToBits.recBody {l : Nat}
  (i : ℕ)
  (res : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (j : ℕ) : MProd (Vector Byte l) (Vector Bool (8 * l)) :=
  List.foldl (Target.byteToBits.body i) res (List.range' j (8 - j))

def Target.byteToBits {l : Nat}
  (res : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (i : ℕ) :
  MProd (Vector Byte l) (Vector Bool (8 * l))
  :=
  List.foldl (Target.byteToBits.body i) res (List.range' 0 8)

def Target.bytesToBits.recBody
  {l : Nat} (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (i : ℕ) :
  MProd (Vector Byte l) (Vector Bool (8 * l)) :=
  List.foldl byteToBits acc (List.range' i (l - i))

def Target.bytesToBits {l : Nat} (B : Vector Byte l) : Vector Bool (8 * l) :=
  (Target.bytesToBits.recBody ⟨B, Vector.replicate (8 * l) false⟩ 0).snd

theorem Target.bytesToBits.eq_spec {l : Nat} (B : Vector Byte l) :
  Target.bytesToBits B = Spec.bytesToBits B := by
  unfold bytesToBits Spec.bytesToBits bytesToBits.recBody byteToBits byteToBits.body
  simp [Id.run]

--instance Inhabited : Byte := ⟨ 0, by simp ⟩
--instance Inhabited : Byte := ⟨

-- TODO: move
--@[simp]
theorem List.forall_imp_foldl_attach (l0 : List β) (f: α → β → α) (g: α → {x:β // x ∈ l0} → α)
  (h : ∀ a, ∀ x : { x // x ∈ l0 }, f a x = g a x) :
  List.foldl f init l0 = List.foldl g init l0.attach := by
  sorry

def Target.bytesToBits.inv
  {l} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (i : ℕ) (acc : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (j : ℕ) :=
  let C := acc.fst
  let b := acc.snd
  -- prefix of b is properly set
  (∀ i' < i, ∀ j' < 8, b[8*i' + j']! = C0[i']!.testBit j') ∧
  -- ongoing update
  (∀ j' < j, b[8*i + j']! = C0[i]!.testBit j') ∧
  (∀ i' > i, i' < l → ∀ j < 8, b[8*i' + j]! = b0[8*i' + j]!) ∧ -- suffix of b is unchanged
  (∀ i' > i, i' < l → C[i']! = C0[i']!) ∧ -- suffix of C is unchanged
  (i < l → C[i]! = C0[i]! >>> j)

theorem Target.byteToBits.body.spec
  {l} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (i : ℕ) (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (j : ℕ)
  (hinv : bytesToBits.inv C0 b0 i acc j) (hi : i < l) (hj : j < 8) :
  bytesToBits.inv C0 b0 i (body i acc j) (j + 1) := by
  unfold body
  unfold bytesToBits.inv
  unfold bytesToBits.inv at hinv; simp at hinv
  obtain ⟨ h0, h1, h2, h3, h4 ⟩ := hinv
  simp
  generalize hC : acc.fst = C at *
  generalize hb : acc.snd = b at *
  split_conjs
  . intro i' hi' j' hj
    simp [h4, hi]
    simp_lists [h0]
  . intro j' hj'
    by_cases hj'': j' = j
    . simp [*]
      simp_lists
      simp [Nat.testBit_to_div_mod]
      natify; simp
      have : 2^j % 256 = 2^j := by
        apply Nat.mod_eq_of_lt
        have : 2^j ≤ 2^7 := by -- TODO: scalar_tac
          apply Nat.pow_le_pow_right <;> omega
        omega
      simp [this, Nat.shiftRight_eq_div_pow]
    . simp [*]
      simp_lists [h1]
  . intro i' hi' hi'' j' hj'
    have : 8*i + j < 8*i' + j' := by scalar_tac
    simp_lists [h2]
  . intro i' hi' hi''
    simp_lists [h3]
  . simp_lists [h4, hi]
    natify
    simp [Nat.div_div_eq_div_mul, Nat.shiftRight_eq_div_pow]
    ring_nf

theorem Target.byteToBits.recBody.spec
  {l} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (i : ℕ) (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (j : ℕ)
  (hinv : bytesToBits.inv C0 b0 i acc j) (hi : i < l) (hj : j ≤ 8) :
  bytesToBits.inv C0 b0 i (recBody i acc j) 8 := by
  if hj1 : j = 8 then
    simp_all [recBody]
  else
    unfold recBody
    have : 8 - j = (8 - (j+1)) + 1 := by omega
    simp only [this, List.range'_succ]
    simp
    have hinv1 := body.spec C0 b0 i acc j hinv (by omega) (by omega)
    have hinv2 := spec C0 b0 i (body i acc j) (j + 1) hinv1 (by omega) (by omega)
    simp [recBody] at hinv2
    apply hinv2
termination_by 8 - j
decreasing_by omega

theorem Target.byteToBits.spec
  {l} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (i : ℕ) (acc : MProd (Vector Byte l) (Vector Bool (8 * l)))
  (hinv : bytesToBits.inv C0 b0 i acc 8) (hi : i < l) :
  bytesToBits.inv C0 b0 (i + 1) (recBody i acc 8) 0 := by
  have hinv1 := byteToBits.recBody.spec C0 b0 i acc 8 hinv (by omega) (by simp)
  simp [bytesToBits.inv] at hinv1 ⊢
  obtain ⟨ h0, h1, h2, h3, h4 ⟩ := hinv1
  generalize hbody: recBody i acc 8 = acc1 at *
  generalize hC1 : acc1.fst = C1 at *
  generalize hb1 : acc1.snd = b1 at *
  split_conjs
  . intro i' hi' j hj
    by_cases hi'': i' = i
    . simp [hi'']
      simp_lists [h1]
    . simp_lists [h0]
  . intro j' hj'
    simp_lists [h2]
  . intro i' hi' hi''
    simp_lists [h3]
  . simp_lists [h3]

theorem Target.bytesToBits.recBody.step_eq
  {l : ℕ} (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (i : ℕ) (hi : i < l) :
  recBody acc i = recBody (byteToBits acc i) (i + 1) := by
  unfold recBody
  have : l - i = (l - (i+1)) + 1 := by omega
  simp [this, List.range'_succ]

theorem Target.bytesToBits.recBody.spec
  {l : Nat} (C0 : Vector Byte l) (b0 : Vector Bool (8 * l))
  (acc : MProd (Vector Byte l) (Vector Bool (8 * l))) (i : ℕ) (hi : i ≤ l)
  (hinv : bytesToBits.inv C0 b0 i acc 0) :
  bytesToBits.inv C0 b0 l (recBody acc i) 0
 := by
 if hi1 : i = l then
  simp_all [recBody]
 else
  simp (disch := omega) only [Target.bytesToBits.recBody.step_eq, hi, hi1]
  have hinv1 := byteToBits.recBody.spec C0 b0 i acc 0 hinv (by omega) (by simp)
  have hinv2 := byteToBits.spec C0 b0 i (byteToBits acc i) hinv1 (by omega)
  have : byteToBits.recBody i (byteToBits acc i) 8 =
         byteToBits acc i := by
    unfold byteToBits.recBody
    simp
  rw [this] at hinv2
  have hinv3 := spec C0 b0 (byteToBits acc i) (i + 1) (by omega) hinv2
  apply hinv3
termination_by l - i
decreasing_by omega

def Target.bytesToBits.post {l} (B : Vector Byte l) (b : Vector Bool (8 * l)) :=
  ∀ i < l, ∀ j < 8, b[8*i + j]! = B[i]!.testBit j

theorem Target.bytesToBits.spec
  {l : Nat} (B : Vector Byte l) :
  post B (bytesToBits B) := by
  unfold bytesToBits
  generalize hC0 : B = C0 at *
  generalize hb0 : Vector.replicate (8 * l) false = b0 at *
  generalize hacc0 : MProd.mk C0 b0 = acc0 at *
  have hinv0 : bytesToBits.inv C0 b0 0 acc0 0 := by
    unfold inv
    simp [← hacc0]
  have hinv1 := recBody.spec C0 b0 acc0 0 (by omega) hinv0
  unfold inv at hinv1
  obtain ⟨ h0, h1, h2, h3, h4 ⟩ := hinv1
  unfold post
  intro i hi j hj
  generalize hacc1 : recBody acc0 0 = acc1 at *
  simp_lists [h0]

/-!
# byteEncode
-/

def Target.byteEncode.encodeElem.body (d : ℕ) (i : ℕ) (acc : MProd ℕ (Vector Bool (256 * d))) (j : ℕ) :
  MProd ℕ (Vector Bool (256 * d)) :=
  let b := acc.snd
  let a := acc.fst
  let b := b.set! (i * d + j) (Bool.ofNat (a % 2))
  let a := (a - Bool.toNat b[i * d + j]!) / 2
  ⟨ a, b ⟩

def Target.byteEncode.encodeElem.recBody (d : ℕ) (i : ℕ) (acc : MProd ℕ (Vector Bool (256 * d))) (j : ℕ) :
  MProd ℕ (Vector Bool (256 * d)) :=
  List.foldl (byteEncode.encodeElem.body d i) acc (List.range' j (d - j))

def Target.byteEncode.encodeElem (d : ℕ) (F : Polynomial (m d))
  (b : Vector Bool (256 * d)) (i : ℕ) :
  Vector Bool (256 * d) :=
  let a := F[i]!.val
  (encodeElem.recBody d i ⟨ a, b ⟩ 0).snd

def Target.byteEncode.encode.recBody (d : ℕ) (F : Polynomial (m d)) (b : Vector Bool (256 * d)) (i : ℕ) :
  Vector Bool (256 * d) :=
  List.foldl (byteEncode.encodeElem d F) b (List.range' i (256 - i))

def Target.byteEncode.encode (d : ℕ) (F : Polynomial (m d)) :
  Vector Bool (256 * d) :=
  encode.recBody d F (Vector.replicate (256 * d) false) 0

def Target.byteEncode (d : ℕ) (F : Polynomial (m d)) :
  Vector Byte (32 * d) :=
  bitsToBytes (Vector.cast (by ring_nf) (byteEncode.encode d F))

def Target.byteEncode.eq_spec (d : ℕ) (F : Polynomial (m d)) :
  byteEncode d F = Spec.byteEncode d F := by
  unfold byteEncode byteEncode.encode byteEncode.encode.recBody byteEncode.encodeElem byteEncode.encodeElem.recBody
    byteEncode.encodeElem.body Spec.byteEncode
  simp [Id.run, Target.bitsToBytes.eq_spec]

irreducible_def Target.byteEncode.encodeElem.body.inv
  (d : ℕ) (F : Polynomial (m d)) (acc : MProd ℕ (Vector Bool (256 * d))) (i : ℕ) (j : ℕ) :=
  let b := acc.snd
  let a := acc.fst
  -- The prefix is set
  (∀ i' < i, ∀ j' < d, b[i' * d + j']! = F[i']!.val.testBit j') ∧
  -- Encoding the current element
  (∀ j' < j, b[i * d + j']! = F[i]!.val.testBit j') ∧
  (∀ j' ∈ [j:d], b[i * d + j']! = false) ∧
  a = F[i]!.val / 2^j ∧
  -- The suffix is not set
  (∀ i' ∈ [i+1:256], ∀ j < d, b[i' * d + j]! = false)

-- TODO: move
@[simp]
theorem Bool.toNat_ofNat_mod2 (x : ℕ) : (Bool.ofNat (x % 2)).toNat = x % 2 := by
  have := @Nat.mod_lt x 2 (by simp)
  cases h: x % 2 <;> simp [Bool.ofNat]
  omega

def Target.byteEncode.encodeElem.body.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {acc : MProd ℕ (Vector Bool (256 * d))} {j : ℕ}
  (hinv : inv d F acc i j)
  (hi : i < 256 := by omega) (hj : j < d := by omega) :
  inv d F (body d i acc j) i (j + 1) := by
  simp [inv, body] at *
  obtain ⟨ h0, h1, h2, h3, h4 ⟩ := hinv
  generalize hb1: acc.snd = b1 at *
  generalize ha1: acc.fst = a1 at *
  have : i * d ≤ 255 * d := by scalar_tac +nonLin
  have : i * d + j < 256 * d := by omega
  split_conjs
  . intros i' hi' j' hj'
    have : i' * d + d ≤ i * d := by
      have : 1 * d ≤ i * d := by scalar_tac +nonLin
      have : i' * d ≤ (i - 1) * d := by scalar_tac +nonLin
      simp only [Nat.sub_mul] at this
      omega
    have : i' * d + j' < i * d + j := by omega
    simp_lists [h0]
  . intros j' hj'
    by_cases hj'': j' = j
    . simp [hj'']; simp_lists
      simp [h3, Nat.testBit, Bool.ofNat, Nat.shiftRight_eq_div_pow]
      tauto
    . simp_lists [*]
  . intros j' hj' hj''
    have : i * d + j < i * d + j' := by omega
    have : i * d + j' < 256 * d := by omega
    simp_lists [h2]
  . simp_lists; simp [h3]
    have : F[i]!.val / 2 ^ j - F[i]!.val / 2 ^ j % 2 =
           2 * (F[i]!.val / 2^j / 2) := by
      have := Nat.mod_def (F[i]!.val / 2 ^ j) 2
      omega
    rw [this]
    simp [Nat.div_div_eq_div_mul]
    ring_nf
  . intros i' hi' hi'' j' hj'
    have : i * d + d ≤ i' * d := by
      have : 1 * d ≤ i' * d := by scalar_tac +nonLin
      have : i * d ≤ (i' - 1) * d := by scalar_tac +nonLin
      simp only [Nat.sub_mul] at this
      omega
    have : i * d + j < i' * d + j' := by omega
    have : i' * d ≤ 255 * d := by scalar_tac +nonLin
    have : i' * d + j' < 256 * d := by omega
    simp_lists [h4]

def Target.byteEncode.encodeElem.recBody.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {acc : MProd ℕ (Vector Bool (256 * d))} {j : ℕ}
  (hinv : body.inv d F acc i j)
  (hi : i < 256 := by omega) (hj : j ≤ d := by omega) :
  body.inv d F (recBody d i acc j) i d := by
  if hj' : j = d then
    simp [hj'] at *
    unfold recBody
    simp
    apply hinv
  else
    have hinv1 := Target.byteEncode.encodeElem.body.spec hinv
    have hinv2 := spec hinv1
    have : recBody d i (body d i acc j) (j + 1) = recBody d i acc j := by
      unfold recBody
      have : d - j = (d - (j + 1)) + 1 := by omega
      rw [this]
      simp [List.range'_succ]
    simp [this] at hinv2
    apply hinv2
termination_by d - j
decreasing_by simp_wf; omega

/- Remark: we're using the fact that b[.]! is defined and equal to false even if the index is out of bounds
   (this makes the property true even if `i + 1 = 256`) -/
theorem Target.byteEncode.encodeElem.body.inv_d_imp_inv
  {d : ℕ} {F : Polynomial (m d)} {acc : MProd ℕ (Vector Bool (256 * d))} {i : ℕ}
  (hinv : inv d F acc i d) :
  inv d F ⟨F[i+1]!.val, acc.snd⟩ (i + 1) 0 := by
  simp [inv] at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  split_conjs
  . intros i' hi' j' hj'
    by_cases hi'': i' = i
    . simp [hi'']
      simp_lists [h1]
    . simp_lists [h0]
  . intros j' hj'
    by_cases h: i + 1 < 256
    . simp_lists [h3]
    . have : 256 * d ≤ (i + 1) * d := by scalar_tac +nonLin
      have : 256 * d ≤ (i + 1) * d + j' := by omega
      simp [this]
  . simp_lists [h3]

irreducible_def Target.byteEncode.encode.inv
  (d : ℕ) (F : Polynomial (m d)) (b : Vector Bool (256 * d)) (i : ℕ) :=
  -- The prefix is set
  (∀ i' < i, ∀ j < d, b[i' * d + j]! = F[i']!.val.testBit j) ∧
  -- The suffix is not set
  (∀ i' ∈ [i:256], ∀ j < d, b[i' * d + j]! = false)

theorem Target.byteEncode.encodeElem.body_inv_0_imp_inv
  {d : ℕ} {F : Polynomial (m d)} {acc : MProd ℕ (Vector Bool (256 * d))} {i : ℕ}
  (hinv : body.inv d F acc i 0) :
  encode.inv d F acc.snd i := by
  simp [body.inv, encode.inv] at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  simp_lists [*]
  intros i' hi' hi'' j hj
  by_cases hi''': i' = i <;> simp_lists [*]

theorem Target.byteEncode.encodeElem.inv_imp_body_inv
  {d : ℕ} {F : Polynomial (m d)} {b : Vector Bool (256 * d)} {i : ℕ}
  (hinv : encode.inv d F b i) (hi : i < 256 := by omega) :
  body.inv d F ⟨ F[i]!.val, b ⟩ i 0 := by
  simp [body.inv, encode.inv] at *
  obtain ⟨ h0, h1 ⟩ := hinv
  split_conjs <;> simp_lists [*]

def Target.byteEncode.encodeElem.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {b : Vector Bool (256 * d)}
  (hinv : encode.inv d F b i)
  (hi : i < 256 := by omega) :
  encode.inv d F (encodeElem d F b i) (i + 1) := by
  simp [encodeElem]
  have := inv_imp_body_inv hinv
  have := Target.byteEncode.encodeElem.recBody.spec this
  have := body.inv_d_imp_inv this
  have := body_inv_0_imp_inv this
  simp at this
  apply this

def Target.byteEncode.encode.recBody.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {b : Vector Bool (256 * d)}
  (hinv : inv d F b i)
  (hi : i ≤ 256 := by omega) :
  inv d F (recBody d F b i) 256 := by
  if hi' : i = 256 then
    simp [hi'] at *
    simp [recBody, hinv]
  else
    have := encodeElem.spec hinv
    have := spec this
    have : recBody d F (encodeElem d F b i) (i + 1) = recBody d F b i := by
      simp [recBody]
      have : 256 - i = (255 - i) + 1 := by omega
      rw [this]
      simp [List.range'_succ]
    simp_all
termination_by 256 - i
decreasing_by simp_wf; omega

def Target.byteEncode.encode.spec (d : ℕ) (F : Polynomial (m d)) :
  ∀ i < 256, ∀ j < d, (encode d F)[i * d + j]! = F[i]!.val.testBit j := by
  have hinv0 : inv d F (Vector.replicate (256 * d) false) 0 := by
    simp [inv]
    intros i hi j hj
    have : i * d ≤ 255 * d := by scalar_tac +nonLin
    simp_lists
  have hinv1 := recBody.spec hinv0
  generalize hb : encode d F = b at *
  have : recBody d F (Vector.replicate (256 * d) false) 0 = b := by
    simp [← hb, encode]
  simp [this] at hinv1
  simp [inv] at hinv1
  apply hinv1

-- TODO: move
@[simp, simp_lists_simps]
theorem Vector.getElem!_cast {n m : ℕ} {α : Type u_1} [Inhabited α] (h: n = m) (v : Vector α n) (i : ℕ):
  (Vector.cast h v)[i]! = v[i]! := by sorry

/-- The important theorem! -/
def Target.byteEncode.spec (d : ℕ) (F : Polynomial (m d)) (hd : 0 < d) :
  ∀ i < 32 * d, ∀ j < 8,
    (byteEncode d F)[i]!.testBit j = F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d) := by
  intros i hi j hj
  unfold byteEncode
  have h0 := encode.spec d F
  generalize hb : (Vector.cast (by ring_nf) (encode d F) : Vector Bool (8 * (32 * d))) = b at *
  have h1 := Target.bitsToBytes.spec  b
  simp [bitsToBytes.post] at h1
  generalize hb1 : bitsToBytes b = b1 at *
  simp_lists [h1]
  simp [← hb]

  /- We have to play with the indices -/
  let ij := 8 * i + j
  let i' := ij / d
  let j' := ij % d
  have : i' < 256 := by
    simp +zetaDelta
    rw [Nat.div_lt_iff_lt_mul] <;> omega

  have : j' < d := by
    simp +zetaDelta
    apply Nat.mod_lt; omega -- TODO: scalar_tac +zetaDelta

  refold_let ij

  have : ij = i' * d + j' := by
    have := Nat.mod_add_div ij d
    simp +zetaDelta at *
    ring_nf at *
    omega

  simp [this]
  simp_lists [h0]
  simp +zetaDelta

  have : ((8 * i + j) / d * d + (8 * i + j) % d) / d = (8 * i + j) / d := by
    have : (8 * i + j) / d * d = d * ((8 * i + j) / d) := by ring_nf
    rw [this]; clear this
    rw [Nat.mul_add_div] <;> try omega
    simp only [Nat.mod_div_self, add_zero]

  rw [this]

/-!
# Streamed byteEncode

Below, we prove that the streamed version of `byteEncode` is correct.
-/

/-- `d`: the number of bits with which to encode an element
    `n`: the number of bytes in the accumulator
-/
structure Stream.EncodeState (d n : ℕ) where
  b : Vector Byte (32 * d)
  bi : ℕ -- number of bytes written to `b`
  acc : BitVec (8 * n)
  acci : ℕ -- number of bits written to `acc`

def Stream.encode.body {d n : ℕ} (x : ZMod (m d)) (s : EncodeState d n) :
  EncodeState d n :=
  let nBits := min d (8 * n - s.acci)
  let bits := BitVec.ofNat (8 * n) x.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  let xBits := d - nBits

  let acc := s.acc ||| (bits <<< s.acci)
  let acci := s.acci + nBits

  -- Flush
  if acci = 8 * n then
    let b := s.b.setSlice! s.bi acc.toLEBytes
    let bi := s.bi + n

    -- Encode the remaining bits
    let x := x.val >>> nBits
    let acc := BitVec.ofNat (8 * n) x
    let acci := xBits
    {b, bi, acc, acci}
  else
    {s with acc, acci}

def Stream.encode.inv
  {d n : ℕ} (F : Vector (ZMod (m d)) 256) (s : EncodeState d n) (i : ℕ) : Prop :=
  -- The lengths are correct
  i ≤ 256 ∧
  s.bi = n * ((d * i) / (8 * n)) ∧
  s.acci = (d * i) % (8 * n) ∧
  -- The bits are properly set in the destination buffer
  (∀ i < s.bi, ∀ j < 8, s.b[i]!.testBit j = F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d)) ∧
  -- The bits are properly set in the accumulator
  (∀ j < s.acci, s.acc[j]! = F[(8 * s.bi + j) / d]!.val.testBit ((8 * s.bi + j) % d)) ∧
  (∀ j ∈ [s.acci:8*n], s.acc[j]! = false)


macro "glet" h:ident " : " x:ident " := " e:term : tactic =>
  -- TODO: don't manage to make the syntax `generalize $h : ...` work
  `(tactic| (generalize h: $e = $x at *; rename _ => $h; replace $h := Eq.symm $h))

macro "glet" x:ident " := " e:term : tactic =>
  `(tactic| (let $x := $e; refold_let $x at *))

@[simp, simp_lists_simps] theorem BitVec.getElem!_or {n} (x y : BitVec n) (i : ℕ) :
  (x ||| y)[i]! = (x[i]! || y[i]!) := by sorry

@[simp, simp_lists_simps] theorem BitVec.getElem!_and {n} (x y : BitVec n) (i : ℕ) :
  (x ^^^ y)[i]! = (x[i]!&& y[i]!) := by sorry

attribute [simp_lists_simps] Bool.false_or Bool.or_false

-- TODO: move and use more
@[simp, simp_lists_simps]
theorem BitVec.getElem!_eq_false {w : ℕ} (x : BitVec w) (i : ℕ) (hi : w ≤ i) :
  x[i]! = false := by
  unfold getElem! instGetElem?OfGetElemOfDecidable decidableGetElem?
  simp
  split_ifs <;> simp_all
  . omega
  . rfl

-- TODO: move and use more
theorem BitVec.getElem!_eq_getElem {w : ℕ} (x : BitVec w) (i : ℕ) (hi : i < w) :
  x[i]! = x[i] := by
  unfold getElem! instGetElem?OfGetElemOfDecidable decidableGetElem?
  simp
  split_ifs; simp_all

theorem BitVec.getElem!_eq_testBit_toNat {w : ℕ} (x : BitVec w) (i : ℕ) :
  x[i]! = x.toNat.testBit i := by
  by_cases i < w
  . have : x[i]! = x[i] := by
      simp [BitVec.getElem!_eq_getElem, *]
    rw [this]
    simp [BitVec.getElem_eq_testBit_toNat]
  . simp_all
    have : x.toNat < 2^w := by omega
    apply Nat.testBit_eq_false_of_lt
    have : 2^w ≤ 2^i := by apply Nat.pow_le_pow_right <;> omega
    omega

@[simp]
theorem BitVec.and_two_pow_sub_one_eq_mod {w} (x : BitVec w) (n : Nat) :
  x &&& 2#w ^ n - 1#w = x % 2#w ^ n := by
  by_cases hn : n < w
  . simp [← BitVec.ofNat_pow]
    natify
    simp
    have : 2^n < 2^w := by
      apply Nat.pow_lt_pow_of_lt <;> omega
    -- TODO: simp_arith
    simp (disch := omega) [Nat.mod_eq_of_lt]
    have : 1 ≤ 2^n := by
      have : 2^0 ≤ 2^n := by apply Nat.pow_le_pow_of_le <;> omega
      omega
    have : 2 ^ w - 1 + 2 ^ n = 2^w + (2^n - 1) := by omega
    rw [this]
    simp (disch := omega) [Nat.mod_eq_of_lt]
  . simp [← BitVec.ofNat_pow]
    simp at hn
    have : BitVec.ofNat w (2 ^ n) = 0 := by
      unfold BitVec.ofNat Fin.ofNat'
      have : 2^n % 2^w = 0 := by
        have : n = w + (n - w) := by omega
        rw [this, Nat.pow_add]
        simp only [Nat.mul_mod_right]
      simp only [this]
      simp only [Fin.mk_zero', BitVec.ofNat_eq_ofNat, BitVec.ofNat, Fin.ofNat'_eq_cast, Nat.cast_zero]
    rw [this]
    simp
    natify
    simp
    by_cases hw: 0 < w
    . have : (2 ^ w - 1 % 2 ^ w) % 2 ^ w = 2^w - 1 := by
        have hLt : 1 < 2^w := by
          have : 2^0 < 2^w := by -- TODO: scalar_tac +nonLin
            apply Nat.pow_lt_pow_of_lt <;> omega
          omega
        have : (2^w - 1) % 2^w = 2^w - 1 := by apply Nat.mod_eq_of_lt; omega
        rw [← this]
        zmodify
        simp only [Nat.one_mod_two_pow, Nat.ofNat_pos, pow_pos, Nat.cast_pred, CharP.cast_eq_zero,
          zero_sub, hw]
      simp [this]
    . have : x.toNat < 2^w := by omega
      simp_all

attribute [natify_simps] BitVec.toNat_twoPow

@[simp]
theorem BitVec.shiftLeft_sub_one_eq_mod {w} (x : BitVec w) (n : Nat) :
  x &&& 1#w <<< n - 1#w = x % 2 ^ n := by
  simp only [BitVec.ofNat_eq_ofNat]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  have : 1#w * BitVec.twoPow w n = 2#w ^ n := by
    have : 1#w = 1 := by simp
    rw [this]
    ring_nf
    natify; simp only [toNat_pow, BitVec.toNat_ofNat]
    zmodify
    simp only [ZMod.natCast_mod, Nat.cast_ofNat]
  rw [this]
  simp only [BitVec.and_two_pow_sub_one_eq_mod]

@[simp]
theorem BitVec.getElem!_zero (w i : ℕ ) : (0#w)[i]! = false := by
  simp [BitVec.getElem!_eq_testBit_toNat]

-- TODO: equivalent of those theorems for Lists, Arrays
theorem Vector.setSlice!_getElem!_prefix {α} [Inhabited α]
  {n : ℕ} (v : Vector α n) (s : List α) (i j : ℕ) (h : j < i) :
  (v.setSlice! i s)[j]! = v[j]! := by sorry

theorem Vector.setSlice!_getElem!_suffix {α} [Inhabited α]
  {n : ℕ} (v : Vector α n) (s : List α) (i j : ℕ) (h : i + s.length < j ∧ j < n) :
  (v.setSlice! i s)[j]! = v[j]! := by sorry

@[simp, simp_lists_simps]
theorem Vector.setSlice!_getElem!_same {α} [Inhabited α]
  {n : ℕ} (v : Vector α n) (s : List α) (i j : ℕ) (h : j < i ∨ (i + s.length < j ∧ j < n)) :
  (v.setSlice! i s)[j]! = v[j]! := by
  cases h <;> simp_lists [Vector.setSlice!_getElem!_prefix, Vector.setSlice!_getElem!_suffix]

@[simp, simp_lists_simps]
theorem Vector.setSlice!_getElem!_slice {α} [Inhabited α]
  {n : ℕ} (v : Vector α n) (s : List α) (i j : ℕ) (h : i ≤ j ∧ j < i + s.length ∧ j < n) :
  (v.setSlice! i s)[j]! = s[j - i]! := by sorry

@[simp, simp_lists_simps]
theorem BitVec.testBit_getElem!_toLEBytes {w:ℕ} (x : BitVec w) (i j : ℕ) (h : j < 8) :
  x.toLEBytes[i]!.testBit j = x[8 * i + j]! := by sorry

attribute [scalar_tac_simps] Vector.size_toArray

@[simp]
theorem BitVec.toLEBytes_length {w} (v : BitVec w) (h : w % 8 = 0) :
  v.toLEBytes.length = w / 8 := by sorry

@[simp, simp_lists_simps]
theorem BitVec.getElem!_shiftLeft_false {w} (v : BitVec w) (n i : ℕ) (h : i < n ∨ w ≤ i) :
  (v <<< n)[i]! = false := by
  simp [BitVec.getElem!_eq_testBit_toNat, h]
  omega

@[simp, simp_lists_simps]
theorem BitVec.getElem!_shiftLeft_eq {w} (v : BitVec w) (n i : ℕ) (h : n ≤ i ∧ i < w) :
  (v <<< n)[i]! = v[i - n]! := by
  simp [BitVec.getElem!_eq_testBit_toNat, h]

@[simp, simp_lists_simps]
theorem BitVec.getElem!_shiftRight {w} (v : BitVec w) (n i : ℕ) :
  (v >>> n)[i]! = v[n + i]! := by
  simp [BitVec.getElem!_eq_testBit_toNat]

@[simp, simp_lists_simps]
theorem BitVec.getElem!_mod_pow2_eq {w} (x : BitVec w) (i j : ℕ) (h : j < i) :
  (x % 2#w ^ i)[j]! = x[j]! := by
  simp [BitVec.getElem!_eq_testBit_toNat]
  by_cases hw : w = 0
  . simp_all
    cases i <;> simp_all
  . -- TODO: scalar_tac +nonLin
    by_cases hw: w = 1
    . simp_all
      cases i <;> simp_all
    . have : 2 < 2^w := by
        have : 2^1 < 2^w := by apply Nat.pow_lt_pow_of_lt <;> omega
        omega
      simp (disch := omega) [Nat.mod_eq_of_lt]
      by_cases hi: i < w
      . -- TODO: scalar_tac +nonLin
        have : 2^i < 2^w := by
          apply Nat.pow_lt_pow_of_lt <;> omega
        simp (disch := omega) [Nat.mod_eq_of_lt]
        omega
      . -- TODO: scalar_tac +nonLin
        have : 2^i % 2^w = 0 := by
          have : i = w + (i - w) := by omega
          rw [this]
          simp [Nat.pow_add]
        simp [this]

@[simp, simp_lists_simps]
theorem BitVec.getElem!_mod_pow2_false {w} (x : BitVec w) (i j : ℕ) (h : i ≤ j) :
  (x % 2#w ^ i)[j]! = false := by
  simp [BitVec.getElem!_eq_testBit_toNat, h]
  have : x.toNat < 2^w := by omega
  by_cases hw: w ≤ 1
  . have hw : w = 0 ∨ w = 1 := by omega
    cases hw <;> simp_all
    cases i <;> simp_all [Nat.mod_one]
    apply Nat.testBit_eq_false_of_lt
    -- TODO: scalar_tac +nonLin
    have : 2^1 ≤ 2^j := by apply Nat.pow_le_pow_of_le <;> omega
    omega
  . -- TODO: scalar_tac +nonLin
    have : 2^1 < 2^w := by apply Nat.pow_lt_pow_of_lt <;> omega
    simp (disch := omega) [Nat.mod_eq_of_lt]
    by_cases hi: i < w
    . -- TODO: scalar_tac +nonLin
      have : 2^i < 2^w := by apply Nat.pow_lt_pow_of_lt <;> omega
      simp (disch := omega) [Nat.mod_eq_of_lt]
      omega
    . -- TODO: scalar_tac +nonLin
      have : 2^i % 2^w = 0 := by
        have : i = w + (i - w) := by omega
        rw [this]
        simp [Nat.pow_add]
      simp [this]
      have : w ≤ j := by omega
      apply Nat.testBit_eq_false_of_lt
      -- TODO: scalar_tac +nonLin
      have : 2^w ≤ 2^j := by apply Nat.pow_le_pow_of_le <;> omega
      omega

/--
Auxiliary lemma. See `Stream.encode.body`.

This lemma proves important properties about the encoded bits in the accumulator
before we flush it (if we need to flush it).
-/
theorem Stream.encode.body.spec_before_flush
  {d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState d n}
  (hinv : inv F s i) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega) :
  let x0 := F[i]!
  let nBits := d ⊓ (8 * n - s.acci)
  let bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))

  let acc := s.acc ||| (bits <<< s.acci)
  let acci := s.acci + nBits
  -- The masking is equivalent to a modulo
  bits.toNat = x0.val % 2^nBits ∧
  -- Accumulator: prefix (the bits are properly set)
  (∀ j < acci, acc[j]! = F[(8 * s.bi + j) / d]!.val.testBit ((8 * s.bi + j) % d)) ∧
  -- Accumulator: suffix (the bits are still equal to 0)
  (∀ j ∈ [acci:8*n], acc[j]! = false)

  := by

  simp [inv] at hinv
  simp only
  obtain ⟨ h0, h1, h2, h3, h4, h5 ⟩ := hinv

  glet x0 := F[i]!
  glet nBits := d ⊓ (8 * n - s.acci)
  glet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  glet x := x0.val >>> nBits

  glet acc := s.acc ||| (bits <<< s.acci)
  glet acci := s.acci + nBits

  have hBitsEq : bits.toNat = x0.val % 2^nBits := by
    simp only [bits]
    simp only [BitVec.shiftLeft_sub_one_eq_mod]
    simp

    have : 2 < 2 ^(8*n) := by -- TODO: scalar_tac +nonLin
      have : 2^8 ≤ 2^(8*n) := by -- TODO: scalar_tac +nonLin
        apply Nat.pow_le_pow_right <;> omega
      omega

    have : 2 ^ nBits < 2 ^ (8 * n) := by -- TODO: scalar_tac +nonLin
      apply Nat.pow_lt_pow_right <;> omega

    have : x0.val < 2 ^ (8 * n) := by
      have : x0.val < m d := by apply ZMod.val_lt
      omega

    simp (disch := omega) only [Nat.mod_eq_of_lt]

  -- Accumulator: prefix
  have hAccPre : ∀ j < acci, acc[j]! = F[(8 * s.bi + j) / d]!.val.testBit ((8 * s.bi + j) % d) := by
    intros j hj
    simp [acci] at hj
    simp [acc]
    by_cases hj': j < s.acci -- TODO: simp_lists +split
    . simp_lists [h4]
    . simp_lists [h5]

      simp [BitVec.getElem!_eq_testBit_toNat, hBitsEq]
      have : j - s.acci < nBits := by omega
      simp [this]; clear this -- TODO: simp_arith

      simp [x0]

      have hij : (8 * s.bi + j) / d = i ∧
                 (8 * s.bi + j) % d = j - s.acci := by
        have := Nat.mod_add_div (d * i) (8 * n)
        have : 8 * s.bi = 8 * n * (d * i / (8 * n)) := by
          simp [h1]
          ring_nf

        have : 8 * s.bi + j = d * i + (j - s.acci) := by omega

        split_conjs
        -- TODO: simp arith expressions
        . have hi : (8 * s.bi + j) / d = (d * i + (j - s.acci)) / d := by simp [this]
          simp (disch := omega) [Nat.mul_add_div, Nat.div_eq_of_lt] at hi
          apply hi
        . have hi : (8 * s.bi + j) % d = (d * i + (j - s.acci)) % d := by simp [this]
          simp (disch := omega) [Nat.mul_add_div, Nat.mod_eq_of_lt] at hi
          apply hi
      simp [hij]

  -- Accumulator: suffix
  have hAccPost : ∀ j ∈ [acci:8*n], acc[j]! = false := by
    simp
    intros j hj hj'
    simp [acc]
    simp_lists [*]
    simp [← h2]
    simp [bits]
    simp_lists

  tauto

/--
Auxiliary lemma.

This lemma handles the case of `Stream.encode.body` when there is no flush.
-/
theorem Stream.encode.body.spec_no_flush
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState d n} [NeZero (m d)]
  (hinv : inv F s i) (hi : i < 255 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n)
  (hm : m d < 2^(8*n) := by omega)
  (hacci : ¬ s.acci + d ⊓ (8 * n - s.acci) = 8 * n)
  :
  inv F (body F[i]! s) (i + 1) := by
  -- Important intermediate results about the accumulator and `bits`
  have ⟨ hBitsEq, hAccPre, hAccPost ⟩ := Stream.encode.body.spec_before_flush hinv
  revert hBitsEq hAccPre hAccPost -- TODO: refold let doesn't apply to assumptions which happen before

  -- Unfold the body and the invariant
  unfold body
  simp [inv] at hinv
  obtain ⟨ h0, h1, h2, h3, h4, h5 ⟩ := hinv
  simp only

  -- Introducing abbreviations
  glet x0 := F[i]!
  glet nBits := d ⊓ (8 * n - s.acci)
  glet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  glet x := x0.val >>> nBits
  glet xBits := d - nBits

  glet acc := s.acc ||| (bits <<< s.acci)
  glet acci := s.acci + nBits

  intro hBitsEq hAccPre hAccPost
  simp_ifs

  simp only [inv]

  have hLt : s.acci < 8 * n := by
      simp [h2]
      apply Nat.mod_lt
      omega
  have hLt' : s.acci + nBits < 8 * n := by omega
  have nBitsEq : nBits = d := by omega

  -- Number of bits in the accumulator
  have hAcci : acci = d * (i + 1) % (8 * n) := by
    simp [acci]
    simp [Nat.left_distrib]
    have := Nat.mod_eq_of_lt hLt'
    rw [← this]
    zmodify
    have := Nat.mod_eq_of_lt hLt
    rw [← this] at h2
    zmodify at h2
    simp [h2]
    simp [nBitsEq]

  -- Number of bytes in the output buffer
  have hBi : s.bi = n * (d * (i + 1) / (8 * n)) := by
    -- Using the characterization of euclidean division
    have hMod := Nat.mod_add_div (d * i) (8 * n)
    have hMod' := Nat.mod_add_div (d * (i + 1)) (8 * n)
    --
    simp only [mul_assoc, ← h1, ← h2, ← hAcci] at hMod hMod'
    have : d * (i + 1) = d * i + d := by ring_nf
    conv at hMod' => rhs; rw [this]
    simp [acci, nBitsEq] at hMod'
    have : 8 * s.bi = 8 * (n * (d * (i + 1) / (8 * n))) := by omega
    omega

  split_conjs <;> try tauto

/--
Auxiliary lemma.

This lemma introduces important properties about the output buffer (`s.b`)
after we flushed the accumulator.
-/
theorem Stream.encode.body.spec_with_flush_bi
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState d n}
  (hinv : inv F s i)
  (hi : i < 255 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega)
  (h0 : s.acci + d ⊓ (8 * n - s.acci) = 8 * n := by omega) :
  let x0 := F[i]!
  let nBits := d ⊓ (8 * n - s.acci)
  let bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  let xBits := d - nBits
  let acc := s.acc ||| (bits <<< s.acci)
  -- Number of bytes in the output buffer
  (s.bi + n = n * (d * (i + 1) / (8 * n)) ∧ xBits = (d * (i + 1)) % (8 * n)) ∧
  -- Bits in the output buffer
  (∀ i < s.bi + n, ∀ j < 8,
      (s.b.setSlice! s.bi acc.toLEBytes)[i]!.testBit j =
        F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d))
  := by

  -- Important intermediate results about the accumulator and `bits`
  have ⟨ hBitsEq, hAccPre, hAccPost ⟩ := Stream.encode.body.spec_before_flush hinv
  revert hinv h0 hBitsEq hAccPre hAccPost -- TODO: refold let doesn't apply to assumptions which happen before

  -- Introducing abbreviations
  glet x0 := F[i]!
  glet nBits := d ⊓ (8 * n - s.acci)
  glet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  glet x := x0.val >>> nBits
  glet xBits := d - nBits

  glet acc := s.acc ||| (bits <<< s.acci)
  glet acci := s.acci + nBits

  intro hinv h0 hBitsEq hAccPre hAccPost
  obtain ⟨ _, h1, h2, h3, h4, h5 ⟩ := hinv

  -- Number of bytes in the output buffer
  have hBi : s.bi + n = n * (d * (i + 1) / (8 * n)) ∧
              xBits = (d * (i + 1)) % (8 * n) := by
    have hd0 := calc
      8 * s.bi + 8 * n + xBits = 8 * s.bi + s.acci + (nBits + xBits) := by simp only [← h0, acci]; ring_nf
      _ = 8 * s.bi + s.acci + d := by
        have : nBits + xBits = d := by omega
        simp [this]
      _ = d * i + d := by
        -- Using the characterization of euclidean division
        have : 8 * s.bi + s.acci = d * i := by
          have hMod := Nat.mod_add_div (d * i) (8 * n)
          rw [← hMod]
          simp [h1, h2]
          ring_nf
        omega
      _ = d * (i + 1) := by ring_nf

    have hd1 := calc
      (8 * s.bi + 8 * n + xBits) % (8 * n) = ((8 * s.bi + 8 * n) + xBits) % (8 * n) := by ring_nf
      _ = xBits % (8 * n) := by
        have : (8 * s.bi + 8 * n) % (8 * n) = 0 := by
          simp [h1, ← mul_assoc]
        rw [Nat.add_mod ]
        simp [this]
      _ = xBits := by
        apply Nat.mod_eq_of_lt
        omega

    have hd2 := calc
      (d * (i + 1)) / (8 * n) = (d * (i + 1) - (d * (i + 1)) % (8 * n)) / (8 * n)
          := by rw [Nat.div_eq_sub_mod_div]
      _ =  (8 * s.bi + 8 * n + xBits - xBits) / (8 * n) := by simp only [← hd0, hd1]
      _ = (8 * s.bi + 8 * n) / (8 * n) := by
        have : 8 * s.bi + 8 * n + xBits - xBits = 8 * s.bi + 8 * n := by omega
        rw [this]
      _ = s.bi / n + 1 := by
        simp (disch := omega)
        simp [← Nat.div_div_eq_div_mul]

    have : s.bi + n = n * (d * (i + 1) / (8 * n)) := by
      simp (disch := omega) [hd2, h1]
      ring_nf

    have : xBits = (d * (i + 1)) % (8 * n) := by
      simp only [← hd0, hd1]

    tauto

  -- Bits in the output buffer
  have :
    ∀ i < s.bi + n, ∀ j < 8,
      (s.b.setSlice! s.bi acc.toLEBytes)[i]!.testBit j =
        F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d) := by
    -- We have to do a case disjunction:
    intros i' hi' j hj
    have : acc.toLEBytes.length = n := by simp
    have : s.bi + n ≤ s.b.size := by
      have :=
        -- TODO: scalar_tac +nonLin below
        calc s.bi + n = n * (d * (i + 1) / (8 * n)) := by omega
              _ = n * (d * (i + 1) / 8 / n) := by rw [← Nat.div_div_eq_div_mul]
              _ ≤ d * (i + 1) / 8 := by simp [Nat.mul_div_le]
              _ ≤ d * 256 / 8 := by apply Nat.div_le_div_right; scalar_tac +nonLin
              _ = 32 * d := by omega
      scalar_tac

    by_cases hi'': i' < s.bi -- TODO: simp_lists +split
    . simp_lists [h3]
    . simp_lists [hAccPre]
      have : 8 * s.bi + (8 * (i' - s.bi) + j) = 8 * i' + j := by omega
      simp [this]

  tauto


/--
Auxiliary lemma.

This lemma handles the case of `Stream.encode.body` when there is a flush.
-/
theorem Stream.encode.body.spec_with_flush
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState d n} [NeZero (m d)]
  (hinv : inv F s i) (hi : i < 255 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n)
  (hm : m d < 2^(8*n) := by omega)
  (h0 : s.acci + d ⊓ (8 * n - s.acci) = 8 * n)
  :
  inv F (body F[i]! s) (i + 1) := by
  -- Important intermediate results about the accumulator and `bits`
  have ⟨ hBitsEq, hAccPre, hAccPost ⟩ := Stream.encode.body.spec_before_flush hinv
  -- Intermediate results about the output buffer
  have ⟨ hBi, hsb ⟩ := Stream.encode.body.spec_with_flush_bi hinv
  revert h0 hBitsEq hAccPre hAccPost hBi hsb -- TODO: refold let doesn't apply to assumptions which happen before

  -- Unfold the body and the invariant
  unfold body
  simp [inv] at hinv
  obtain ⟨ h0, h1, h2, h3, h4, h5 ⟩ := hinv
  simp only

  -- Introducing abbreviations
  glet x0 := F[i]!
  glet nBits := d ⊓ (8 * n - s.acci)
  glet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  glet x := x0.val >>> nBits
  glet xBits := d - nBits

  glet acc := s.acc ||| (bits <<< s.acci)
  glet acci := s.acci + nBits

  intro h0 hBitsEq hAccPre hAccPost hBi hsb

  simp_ifs
  simp only [inv]

  glet bits := BitVec.ofNat (8 * n) x &&& (1#(8*n) <<< nBits - 1#(8*n))

  split_conjs <;> try tauto
  . intros j hj
    simp [bits, x, x0]

    have hij : (8 * (s.bi + n) + j) / d = i ∧
                (8 * (s.bi + n) + j) % d = nBits + j
                := by
      have hij := calc
        8 * (s.bi + n) + j = 8 * s.bi + 8 * n + j := by omega
        _ = 8 * s.bi + s.acci + nBits + j := by omega
        _ = d * i + nBits + j := by
          -- Property of euclidean division
          have hMod := Nat.mod_add_div (d * i) (8 * n)
          simp [mul_assoc, ← h1, ← h2] at hMod
          omega

      have : nBits + j < d := by omega
      have hi := calc
        (8 * (s.bi + n) + j) / d = (d * i + (nBits +j)) / d := by simp [hij]; ring_nf
        _ = i + (nBits + j) / d := by rw [Nat.mul_add_div]; omega -- TODO: simp_arith
        _ = i := by rw [Nat.div_eq_of_lt] <;> omega -- TODO: simp_arith

      have hj := calc
        (8 * (s.bi + n) + j) % d = (d * i + (nBits +j)) % d := by simp only [hij]; ring_nf
        _ = (nBits + j) % d := by rw [Nat.mul_add_mod_self_left]
        _ = nBits + j := by apply Nat.mod_eq_of_lt; omega -- TODO: simp_arith

      simp only [hi, hj, Nat.add_left_inj, and_self]
    simp [hij]
    simp [BitVec.getElem!_eq_testBit_toNat]
    omega
  . simp [bits, x]
    intros j hj hj'
    simp [BitVec.getElem!_eq_testBit_toNat, x0]
    intros

    apply Nat.testBit_eq_false_of_lt
    have : m d ≤ 2 ^(nBits + j) := by -- TODO: scalar_tac +nonLin
      unfold m Q
      split
      . apply Nat.pow_le_pow_of_le <;> omega
      . have : 2^12 ≤ 2^(nBits + j) := by
          apply Nat.pow_le_pow_of_le <;> try omega
        omega

    have : F[i]!.val < m d := by apply ZMod.val_lt
    omega

/--
The important lemma about `Stream.encode.body`: calling this function once preserves the invariant
(but we encoded one more element, so the index goes from `i` to `i + 1`).

The best way of understanding the proof, in particular the equations between the indices (`i`, `s.bi`, `s.acci`, etc.)
is to make a drawing. We typically have something like this:

                                                                  `8 * s.bi + 8 * n`
  `8 * s.bi` bits encoded in `s.b`    `s.acci` bits in `s.acc`               |
|------------------------------------|------------------------|--------------|---------|
                                                              |   `nBits`      `xBits` |
                                                           `d * i`                 `d * (i + 1)`
                                                  (`i` elements encoded to `d * i`
                                                   bits in `s.b` and `s.acc`)

-/
theorem Stream.encode.body.spec
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState d n} [NeZero (m d)]
  (hinv : inv F s i) (hi : i < 255 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n)
  (hm : m d < 2^(8*n) := by omega) :
  inv F (body F[i]! s) (i + 1) := by
  by_cases h0 : s.acci + d ⊓ (8 * n - s.acci) = 8 * n
  . apply spec_with_flush hinv <;> omega
  . apply Stream.encode.body.spec_no_flush hinv <;> omega

/-!
# Compress
-/

/- Marking those definitions as irreducible because otherwise we get a "(kernel) deep recursion detected"
   when checking the proof term of one of the proofs below.
-/
irreducible_def compress.mulConstant : BitVec 64 := BitVec.ofNat 64 0x9d7dbb
irreducible_def compress.shiftConstant : ℕ := 35

def compress_bv (d : ℕ) (x : BitVec 64) : BitVec 64 :=
  let multiplication := x * compress.mulConstant
  let coefficient := (multiplication >>> (compress.shiftConstant - (d + 1)))
  let coefficient := (coefficient + 1) >>> 1
  let coefficient := coefficient &&& (1 <<< d) - 1#64
  coefficient

set_option maxHeartbeats 10000000 in
/-- The compression is implemented in a clever way.
    We brute force the proof by enumerating all the cases for `d < 12`, then using `bv_decide`.
-/
private theorem compress_bv_eq_aux (x : BitVec 64) (h : x < 3329#64) (d : ℕ) (hd : d < 12) :
  compress_bv d x = ((2^(d+1) * x + Q) / (2 * Q)) % BitVec.ofNat 64 (2^d)
  := by
  simp [compress_bv, compress.mulConstant, compress.shiftConstant, ← BitVec.ofNat_pow]
  cases d; simp; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  ring_nf at hd; simp at hd

def compress (d : ℕ) (x : ℕ) : ℕ :=
  let multiplication := x * 0x9d7dbb
  let coefficient := (multiplication >>> (35 - (d + 1)))
  let coefficient := (coefficient + 1) >>> 1
  let coefficient := coefficient &&& (1 <<< d) - 1
  coefficient

theorem compress_bv_eq (x : ℕ) (h : x < 3329) (d : ℕ) (hd : d < 12) :
  (compress_bv d x).toNat = compress d x := by
  simp [compress_bv, compress]
  have : x * compress.mulConstant.toNat < 3329 * 0x9d7dbb := by simp [compress.mulConstant]; omega
  have : (↑x * compress.mulConstant.toNat) >>> (compress.shiftConstant - (d + 1)) ≤ (↑x * compress.mulConstant.toNat) :=
    Nat.shiftRight_le _ _
  simp (disch := omega) [Nat.mod_eq_of_lt]
  have : (18446744073709551615 + 1 <<< d) % 18446744073709551616 = (1 <<< d) - 1 := by
    have : 1 <<< d > 0 := by
      have := @Nat.le_shiftLeft 1 d
      omega
    have : 18446744073709551615 + 1 <<< d = 2^64 + ((1 <<< d) - 1) := by simp; omega
    rw [this]; clear this
    simp only [Nat.reducePow, Nat.add_mod_left, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
      Nat.reduceAdd, gt_iff_lt]
    have := Nat.one_shiftLeft d
    have := @Nat.pow_lt_pow_of_lt 2 d 64 (by simp) (by omega)
    omega
  rw [this]; clear this
  simp [compress.mulConstant, compress.shiftConstant]

theorem compress_eq (x : ℕ) (h : x < 3329) (d : ℕ) (hd : d < 12) :
  compress d x = ⌈ ((2^d : ℚ) / (Q : ℚ)) * x ⌋ % (2^d)
  := by
  -- Use `compres_bv` as an intermediate step
  rw [← compress_bv_eq x h d hd]
  rw [compress_bv_eq_aux] <;> try (simp -failIfUnchanged; omega)

  -- Get rid of the `⌈ ... ⌋`
  have : ((2^d : ℚ) / (Q : ℚ)) * (x : ℚ) = ((2 ^ d * x : ℕ) : ℚ) / (Q : ℚ) := by
    simp; ring_nf
  rw [this]; clear this
  rw [Nat.rat_round_div]; swap; simp

  -- Finish the proof by simplifying everything
  simp only [BitVec.ofNat_eq_ofNat, BitVec.natCast_eq_ofNat, Nat.cast_ofNat, BitVec.reduceMul,
    BitVec.toNat_umod, BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.mul_mod_mod, Nat.reduceMod, Nat.mod_add_mod, Int.ofNat_emod, Int.natCast_div,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Int.reduceMul]

  have : (2 ^ d : Int) % 18446744073709551616 = 2^d := by
    apply Int.emod_eq_of_lt
    . simp
    . have := @Nat.pow_lt_pow_of_lt 2 d 64 (by simp) (by omega)
      zify at this
      omega
  rw [this]; clear this

  congr
  simp [← BitVec.ofNat_pow]
  have : (2^(d+1) : Int) ≤ 2^12 := by
    have := @Nat.pow_le_pow_right 2 (by simp) (d + 1) 12 (by omega)
    zify at this
    omega
  have : (2^(d + 1) : Int) % 18446744073709551616 = 2^(d+1) := by
    apply Int.emod_eq_of_lt
    . simp
    . omega
  rw [this]; clear this

  have := @Int.mul_nonneg (2^(d+1)) x (by simp) (by simp)
  have := @Int.mul_le_mul_of_nonneg_right (2^(d+1)) (2^12) x (by omega)
  have := @Int.emod_eq_of_lt (2 ^ (d + 1) * ↑x + 3329) 18446744073709551616
    (by omega) (by omega)
  rw [this]; clear this

  ring_nf

/-!
# Compress then BytesToBits then Encode
-/

end Symcrust.SpecAux
