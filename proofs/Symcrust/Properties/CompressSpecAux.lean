import Symcrust.Spec
import Symcrust.Properties.Polynomials

/-!
An auxiliary specification that we use to prove a refinement result.
This specification refines the specification in `Spec`, and is refined by the code.
It does not need to be trusted.
-/

attribute [-simp] List.getElem!_eq_getElem?_getD List.reduceReplicate Aeneas.SRRange.foldWhile_step

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


/-!
# ByteEncode
-/

def byteEncodeToBits {n} (d : ℕ) (f : List (ZMod n)) : List Bool :=
  List.flatten (List.map (fun a => (List.map (fun i => a.val.testBit i) (List.range d))) f)

def bitsToBytes1 (l : ℕ) (b : List Bool) : List Byte :=
  List.map (fun i => BitVec.ofBoolListLE (List.map (fun j => b[8 * i + j]!) (List.range 8))) (List.range l)

def BitVec.toLEBytes {n : ℕ} (b : BitVec n) : List Byte :=
  if n > 0 then
    b.setWidth 8 :: BitVec.toLEBytes ((b >>> 8).setWidth (n - 8))
  else []

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
# BytesToBits
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

--instance Inhabited : Byte := ⟨ 0, by simp ⟩
--instance Inhabited : Byte := ⟨

-- TODO: move
--@[simp]
theorem List.forall_imp_foldl_attach (l0 : List β) (f: α → β → α) (g: α → {x:β // x ∈ l0} → α)
  (h : ∀ a, ∀ x : { x // x ∈ l0 }, f a x = g a x) :
  List.foldl f init l0 = List.foldl g init l0.attach := by
  sorry

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

theorem Target.bytesToBits_eq_Spec {l : Nat} (B : Vector Byte l) :
  Target.bytesToBits B = Spec.bytesToBits B := by
  unfold bytesToBits Spec.bytesToBits bytesToBits.recBody byteToBits byteToBits.body
  simp [Id.run]
  rfl

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
    simp
  . intro i' hi' hi''
    simp_lists [h3]
  . simp_lists [h3]; simp

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
# BytesToBits then Encode
-/



#exit

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
