import Symcrust.Spec
import Symcrust.Properties.Polynomials
import Symcrust.Properties.BitsAndBytes.BitsToBytes
import Symcrust.Properties.BitsAndBytes.BytesToBits
import Symcrust.Brute

/-!
This file contains theorems about `Symcrust.Spec.byteEncode` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to Algorithm 5 (ByteEncode).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.byteEncode`.
    - `Lean spec (functional)` corresponds to `Target.byteEncode`.
      - The theorem that mathematically characterizes `Target.byteEncode` is `Target.byteEncode.spec`.
    - `⟷₂` corresponds to `Target.byteEncode.eq_spec`.
    - Analogues for later portions of the verification pipeline appear in other files.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

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
  simp only [tsub_zero, bitsToBytes.eq_spec, Vector.Inhabited_getElem_eq_getElem!,
    Vector.set_eq_set!, bind_pure_comp, map_pure, forIn'_eq_forIn, forIn_eq_forIn_range', size,
    add_tsub_cancel_right, Nat.div_one, List.forIn_pure_yield_eq_foldl, Nat.reduceAdd,
    Nat.add_one_sub_one, List.forIn_yield_eq_foldlM, idRun_foldl, Id.run_map]
  simp only [Id.run, Functor.map]

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

def Target.byteEncode.encodeElem.body.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {acc : MProd ℕ (Vector Bool (256 * d))} {j : ℕ}
  (hinv : inv d F acc i j)
  (hi : i < 256 := by omega) (hj : j < d := by omega) :
  inv d F (body d i acc j) i (j + 1) := by
  simp only [inv, mem_std_range_step_one, and_imp, body] at *
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
    . simp only [hj'']; simp_lists
      simp only [Bool.ofNat, h3, ne_eq, Nat.mod_two_not_eq_zero, Nat.testBit,
        Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero]
      tauto
    . simp_lists [*]
  . intros j' hj' hj''
    have : i * d + j < i * d + j' := by omega
    have : i * d + j' < 256 * d := by omega
    simp_lists [h2]
  . simp_lists; simp only [h3]
    have : F[i]!.val / 2 ^ j - F[i]!.val / 2 ^ j % 2 =
           2 * (F[i]!.val / 2^j / 2) := by
      have := Nat.mod_def (F[i]!.val / 2 ^ j) 2
      omega
    rw [this]
    simp only [Nat.div_div_eq_div_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel_left₀]
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
    simp only [hj', le_refl] at *
    unfold recBody
    simp only [tsub_self, List.range'_zero, List.foldl_nil]
    apply hinv
  else
    have hinv1 := Target.byteEncode.encodeElem.body.spec hinv
    have hinv2 := spec hinv1
    have : recBody d i (body d i acc j) (j + 1) = recBody d i acc j := by
      unfold recBody
      have : d - j = (d - (j + 1)) + 1 := by omega
      rw [this]
      simp only [List.range'_succ, List.foldl_cons]
    simp only [this] at hinv2
    apply hinv2
termination_by d - j

/- Remark: we're using the fact that b[.]! is defined and equal to false even if the index is out of bounds
   (this makes the property true even if `i + 1 = 256`) -/
theorem Target.byteEncode.encodeElem.body.inv_d_imp_inv
  {d : ℕ} {F : Polynomial (m d)} {acc : MProd ℕ (Vector Bool (256 * d))} {i : ℕ}
  (hinv : inv d F acc i d) :
  inv d F ⟨F[i+1]!.val, acc.snd⟩ (i + 1) 0 := by
  simp only [inv, mem_std_range_step_one, isEmpty_Prop, not_and, not_lt, imp_self,
    IsEmpty.forall_iff, implies_true, and_imp, true_and, not_lt_zero', zero_le, pow_zero,
    Nat.div_one] at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  split_conjs
  . intros i' hi' j' hj'
    by_cases hi'': i' = i
    . simp only [hi'']
      simp_lists [h1]
    . simp_lists [h0]
  . intros j' hj'
    by_cases h: i + 1 < 256
    . simp_lists [h3]
    . have : 256 * d ≤ (i + 1) * d := by scalar_tac +nonLin
      have : 256 * d ≤ (i + 1) * d + j' := by omega
      simp only [this, Vector.getElem!_default, Bool.default_bool]
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
  simp only [body.inv, not_lt_zero', IsEmpty.forall_iff, implies_true, mem_std_range_step_one,
    zero_le, true_and, pow_zero, Nat.div_one, and_imp, encode.inv] at *
  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv
  simp_lists [*]
  intros i' hi' hi'' j hj
  by_cases hi''': i' = i <;> simp_lists [*]

theorem Target.byteEncode.encodeElem.inv_imp_body_inv
  {d : ℕ} {F : Polynomial (m d)} {b : Vector Bool (256 * d)} {i : ℕ}
  (hinv : encode.inv d F b i) (hi : i < 256 := by omega) :
  body.inv d F ⟨ F[i]!.val, b ⟩ i 0 := by
  simp only [encode.inv, mem_std_range_step_one, and_imp, body.inv, not_lt_zero',
    IsEmpty.forall_iff, implies_true, zero_le, true_and, pow_zero, Nat.div_one] at *
  obtain ⟨ h0, h1 ⟩ := hinv
  split_conjs <;> simp_lists [*]

def Target.byteEncode.encodeElem.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {b : Vector Bool (256 * d)}
  (hinv : encode.inv d F b i)
  (hi : i < 256 := by omega) :
  encode.inv d F (encodeElem d F b i) (i + 1) := by
  simp only [encodeElem]
  have := inv_imp_body_inv hinv
  have := Target.byteEncode.encodeElem.recBody.spec this
  have := body.inv_d_imp_inv this
  have := body_inv_0_imp_inv this
  simp only at this
  apply this

def Target.byteEncode.encode.recBody.spec
  {d : ℕ} {F : Polynomial (m d)} {i : ℕ} {b : Vector Bool (256 * d)}
  (hinv : inv d F b i)
  (hi : i ≤ 256 := by omega) :
  inv d F (recBody d F b i) 256 := by
  if hi' : i = 256 then
    simp only [hi', le_refl] at *
    simp only [recBody, tsub_self, List.range'_zero, List.foldl_nil, hinv]
  else
    have := encodeElem.spec hinv
    have := spec this
    have : recBody d F (encodeElem d F b i) (i + 1) = recBody d F b i := by
      simp only [recBody, Nat.reduceSubDiff]
      have : 256 - i = (255 - i) + 1 := by omega
      rw [this]
      simp only [List.range'_succ, List.foldl_cons]
    simp_all
termination_by 256 - i
decreasing_by simp_wf; omega

def Target.byteEncode.encode.spec (d : ℕ) (F : Polynomial (m d)) :
  ∀ i < 256, ∀ j < d, (encode d F)[i * d + j]! = F[i]!.val.testBit j := by
  have hinv0 : inv d F (Vector.replicate (256 * d) false) 0 := by
    simp only [inv, not_lt_zero', IsEmpty.forall_iff, implies_true, mem_std_range_step_one, zero_le,
      true_and]
    intros i hi j hj
    have : i * d ≤ 255 * d := by scalar_tac +nonLin
    simp_lists
  have hinv1 := recBody.spec hinv0
  generalize hb : encode d F = b at *
  have : recBody d F (Vector.replicate (256 * d) false) 0 = b := by
    simp only [← hb, encode]
  simp only [this] at hinv1
  simp only [inv, mem_std_range_step_one, isEmpty_Prop, not_and, not_lt, imp_self,
    IsEmpty.forall_iff, implies_true, and_true] at hinv1
  apply hinv1

/-- The important theorem! -/
def Target.byteEncode.spec (d : ℕ) (F : Polynomial (m d)) (hd : 0 < d := by omega) :
  ∀ i < 32 * d, ∀ j < 8,
    (byteEncode d F)[i]!.testBit j = F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d) := by
  intros i hi j hj
  unfold byteEncode
  have h0 := encode.spec d F
  generalize hb : (Vector.cast (by ring_nf) (encode d F) : Vector Bool (8 * (32 * d))) = b at *
  have h1 := Target.bitsToBytes.spec  b
  simp only [bitsToBytes.post] at h1
  generalize hb1 : bitsToBytes b = b1 at *
  simp_lists [h1]
  simp only [← hb, Vector.getElem!_cast]

  /- We have to play with the indices -/
  let ij := 8 * i + j
  let i' := ij / d
  let j' := ij % d
  have : i' < 256 := by
    simp +zetaDelta only
    simp_scalar

  have : j' < d := by
    simp +zetaDelta only
    scalar_tac +nonLin

  refold_let ij

  have : i' * d + j' = ij := by
    have := Nat.mod_add_div ij d
    simp +zetaDelta only at *
    ring_nf at *
    omega
  grind

end Symcrust.SpecAux
