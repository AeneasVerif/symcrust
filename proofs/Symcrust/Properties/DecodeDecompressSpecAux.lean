import Symcrust.Properties.CompressEncodeSpecAux
import Mathlib.Algebra.BigOperators.Fin
import Symcrust.Properties.Brute

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

/-!
# Misc lemmas

All or almost all of these could be proven more elegantly, but it is often quicker to just brute force them
**TODO** Move these to its own helper file
-/

lemma testBit_of_sum_mod_md :
  ∀ d < 13, ∀ j : Nat, ∀ hj : j < d, ∀ f : Fin d → Bool,
  (∑ (x : Fin d), (f x).toNat * (2 : ZMod (m d)) ^ (x : ℕ)).val.testBit j = f ⟨j, hj⟩ ∨
  ∑ (x : Fin d), Bool.toNat (f x) * 2 ^ x.val ≥ m d := by
  brute

lemma testBit_of_sum :
  ∀ d < 13, ∀ j : Nat, ∀ hj : j < d, ∀ f : Fin d → Bool,
  (∑ (x : Fin d), (f x).toNat * 2 ^ (x : ℕ)).testBit j = f ⟨j, hj⟩ := by
  brute

lemma bitwise_or_eq_and (x y d accSize : ℕ) (hd : d < 13) (h : accSize < d) (hx : x < 2^accSize)
  (hy : y < 2^(d - accSize)) : x ||| (y <<< accSize) = x + (y <<< accSize) := by
  revert y
  revert x
  revert accSize
  revert d
  brute

lemma testBit_of_add1 (x y d accSize k : ℕ) (hd : d < 13) (h : accSize < d) (hk : k < accSize)
  (hx : x < 2^accSize) (hy : y < 2^(d - accSize)) : (x + y <<< accSize).testBit k = x.testBit k := by
  revert k
  revert y
  revert x
  revert accSize
  revert d
  brute

lemma testBit_of_add2 (x y d accSize k : ℕ) (hd : d < 13) (h : accSize < k + 1) (hk : k < d)
  (hx : x < 2^accSize) (hy : y < 2^(d - accSize)) : (x + y <<< accSize).testBit k = y.testBit (k - accSize) := by
  revert y
  revert x
  revert accSize
  revert k
  revert d
  brute

lemma sum_bits_lt {d : ℕ} (hd : d < 13) (f : Fin d → Bool) :
  ∑ a : Fin d, (f a).toNat * 2 ^ a.val < 2 ^ d := by
  revert d
  brute

theorem sum_bits_lt_mod_md {d : ℕ} (hd : d < 13) (f : Fin d → Bool) :
  (∑ a : Fin d, (f a).toNat * (2 : ZMod (m d)) ^ a.val).val < 2 ^ d := by
  revert d
  brute

lemma sum_shift_lt (x y xBits d : ℕ) (hx : x < 2 ^ xBits) (hy : y < 2 ^ (d - xBits)) (hd : d < 13)
  (hXBits : xBits < d) : x + y <<< xBits < 2^d := by
  revert y
  revert x
  revert xBits
  revert d
  brute

lemma lt_num_bits {n num_bits : ℕ} {x : BitVec (8 * n)} (h : ∀ j ∈ [num_bits: 8 * n], x[j]! = false) :
  x.toNat < 2 ^ num_bits := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [← BitVec.getElem!_eq_testBit_toNat]
  simp only [mem_std_range_step_one, and_imp] at h
  dcases hi2 : i < 8 * n
  . exact h i hi hi2
  . rw [BitVec.getElem!_eq_false]
    omega

lemma sum_le_sum1 {d num_bits : ℕ} (hd1 : d < 13) (hd2 : num_bits < d) (f : Fin d → Bool) :
  ∑ a : Fin num_bits, (f ⟨a, by omega⟩).toNat * 2 ^ a.val ≤ ∑ a : Fin d, (f a).toNat * 2 ^ a.val := by
  revert num_bits
  revert d
  brute

lemma sum_le_sum2 {d num_bits : ℕ} (hd1 : d < 13) (hd2 : num_bits < d) (f : Fin d → Bool) :
  ∑ a : Fin (d - num_bits), (f ⟨a.val + num_bits, by omega⟩).toNat * 2 ^ a.val ≤ ∑ a : Fin d, (f a).toNat * 2 ^ a.val := by
  revert num_bits
  revert d
  brute

lemma md_le_two_pow_d {d : ℕ} (hd : d < 13) : m d ≤ 2 ^ d := by
  unfold m
  split
  . exact Nat.le_refl (2 ^ d)
  . simp only [Q, (by omega : d = 12), Nat.reducePow, Nat.reduceLeDiff]

/-!
# Target byteDecode

Below, we prove that the functional version of `byteDecode` is correct. This version of `byteDecode` is meant to be
as similar as possible to `Spec.byteDecode` without being monadic.
-/
def Target.byteDecode.decodeCoefficient {m d : ℕ} (b : Vector Bool (8 * (32 * d)))
  (F : Polynomial m) (i : ℕ) : Polynomial m :=
  F.set! i (∑ (j : Fin d), (Bool.toNat b[i * d + j]!) * 2^j.val)

def Target.byteDecode.recBody {m d : ℕ} (b : Vector Bool (8 * (32 * d))) (F : Polynomial m) (i : Nat) : Polynomial m :=
  List.foldl (byteDecode.decodeCoefficient b) F (List.range' i (256 - i))

def Target.byteDecode (m d : ℕ) (B : Vector Byte (32 * d)) : Polynomial m :=
  let b := bytesToBits B
  let F := Polynomial.zero m
  byteDecode.recBody b F 0

def Target.byteDecode.eq_spec {m d : ℕ} (B : Vector Byte (32 * d)) :
  byteDecode m d B = Spec.byteDecode B := by
  unfold byteDecode recBody byteDecode.decodeCoefficient Spec.byteDecode
  simp only [bytesToBits.eq_spec, Id.pure_eq, Vector.Inhabited_getElem_eq_getElem!,
    Vector.set_eq_set!, Id.bind_eq, forIn'_eq_forIn, forIn_eq_forIn_range', size, tsub_zero,
    Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one, List.forIn_yield_eq_foldl]
  congr

irreducible_def Target.byteDecode.decodeCoefficient.inv {m d : ℕ} (b : Vector Bool (8 * (32 * d)))
  (F : Polynomial m) (i : ℕ) : Prop :=
  -- Coefficients below `i` have been set
  (∀ i' < i, F[i']! = (∑ (j : Fin d), (Bool.toNat b[i' * d + j]!) * 2^j.val)) ∧
  -- Coefficients at or above `i` have not yet been set
  ∀ i' ∈ [i:256], F[i']! = 0

def Target.byteDecode.decodeCoefficient.spec {m d : ℕ} (b : Vector Bool (8 * (32 * d)))
  (F : Polynomial m) (i : ℕ) (hinv : inv b F i) (hi : i < 256 := by omega) :
  inv b (decodeCoefficient b F i) (i + 1) := by
  unfold decodeCoefficient
  simp_all only [inv, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    mem_std_range_step_one, and_imp, gt_iff_lt, and_self, Vector.getElem!_set!]
  rcases hinv with ⟨hinv1, hinv2⟩
  constructor
  . intro i' i'_lt_i_add_one
    dcases i_eq_i' : i = i'
    . rw [Vector.getElem!_set!]
      . rw [i_eq_i']
      . simp_all
    . rw [Vector.getElem!_set!_ne]
      . exact hinv1 i' (by omega)
      . exact i_eq_i'
  . intro i' i_add_one_le_i' i'_lt_256
    specialize hinv2 i' (by linarith) i'_lt_256
    rw [Vector.getElem!_set!_ne] <;> scalar_tac

def Target.byteDecode.recBody.spec {m d i : ℕ} (b : Vector Bool (8 * (32 * d))) (F : Polynomial m)
  (hF : decodeCoefficient.inv b F i) (hi : i < 256 := by omega) :
  decodeCoefficient.inv b (@recBody m d b F i) 256 := by
  have := decodeCoefficient.spec b F i hF
  dcases i_eq_255 : i = 255
  . simp [recBody, decodeCoefficient, i_eq_255, decodeCoefficient.inv] at *
    exact this
  . have recBodyUnfold : recBody b (byteDecode.decodeCoefficient b F i) (i + 1)  = recBody b F i := by
      simp [recBody, Nat.reduceSubDiff]
      have : 256 - i = (255 - i) + 1 := by omega
      rw [this]
      simp only [List.range'_succ, List.foldl_cons]
    rw [← recBodyUnfold]
    exact @spec m d (i+1) b (decodeCoefficient b F i) this (by omega)

def Target.byteDecode.decodeCoefficient.inv_0 {m d : ℕ} (b : Vector Bool (8 * (32 * d))) :
  decodeCoefficient.inv b (Polynomial.zero m) 0 := by simp [inv]

def Target.byteDecode.spec_aux {m d : ℕ} (B : Vector Byte (32 * d)) :
  ∀ i < 256, (byteDecode m d B)[i]! = ((∑ (j : Fin d), (Bool.toNat (bytesToBits B)[i * d + j]!) * 2^j.val) : ZMod m) := by
  unfold byteDecode
  intro i i_lt_256
  simp only
  have h0 := @decodeCoefficient.inv_0 m d (bytesToBits B)
  have h := recBody.spec (bytesToBits B) (Polynomial.zero m) h0 (by omega : 0 < 256)
  rw [decodeCoefficient.inv] at h
  simp [h.1 i i_lt_256]

def Target.byteDecode.spec {d : ℕ} (B : Vector Byte (32 * d)) (hd : d < 13)
  (hB : ∀ i < 256, ∑ (a : Fin d),
    Bool.toNat (B[(d * i + a) / 8]!.testBit ((d * i + a) % 8)) * 2 ^ a.val < m d) :
  ∀ i < 256,
    (∀ j < d, (byteDecode (m d) d B)[i]!.val.testBit j = B[(d * i + j) / 8]!.testBit ((d * i + j) % 8)) ∧
    (∀ j : Nat, d ≤ j → (byteDecode (m d) d B)[i]!.val.testBit j = false) := by
  intro i i_lt_256
  rw [@spec_aux (m d) d B i i_lt_256]
  constructor
  . intro j j_lt_d
    have : B[(d * i + j) / 8]!.testBit ((d * i + j) % 8) = (bytesToBits B)[d * i + j]! := by
      have := bytesToBits.spec B
      rw [bytesToBits.post] at this
      rw [← this]
      . have : 8 * ((d * i + j) / 8) + (d * i + j) % 8 = d * i + j := by omega
        rw [this]
      . have : ((d * i + j) / 8) * 8 < 256 * d → (d * i + j) / 8 < 32 * d := by omega
        apply this
        have : (d * i + j) / 8 * 8 ≤ d * i + j := by omega
        apply Nat.lt_of_le_of_lt this
        have : j < d * 256 - d * i → d * i + j < 256 * d := by omega
        apply this
        rw [← Nat.mul_sub_left_distrib]
        have : d * 1 ≤ d * (256 - i) := by simp_scalar
        omega
      . simp_scalar
    rw [this]
    have h1 := Target.bytesToBits.spec B
    simp only [bytesToBits.post] at h1
    have h2 : ∀ j < d, (bytesToBits B)[i * d + j]! = B[(i * d + j) / 8]!.testBit ((i * d + j) % 8) := by
      intro j j_lt_d
      have : i * d + j < 256 * d := by
        have : j < 256 * d - i * d → i * d + j < 256 * d := by omega
        apply this
        rw [← Nat.mul_sub_right_distrib]
        have : 1 ≤ 256 - i := by omega
        exact Nat.lt_of_lt_of_le (by omega : j < 1 * d) (Nat.mul_le_mul_right d this)
      have : (i * d + j) / 8 < 32 * d := by omega
      have h2 := h1 ((i * d + j) / 8) this ((i * d + j) % 8) (by omega)
      have : 8 * ((i * d + j) / 8) + (i * d + j) % 8 = i * d + j := by scalar_tac
      rw [this] at h2
      exact h2
    simp only [Fin.is_lt, h2]
    rw [mul_comm d i, h2 j j_lt_d, mul_comm i d]
    specialize hB i i_lt_256
    let f := fun (x : Fin d) => (B[(d * i + ↑x) / 8]!.testBit ((d * i + ↑x) % 8))
    have h3 :=
      testBit_of_sum_mod_md d hd j j_lt_d $ fun (x : Fin d) => (B[(d * i + ↑x) / 8]!.testBit ((d * i + ↑x) % 8))
    rcases h3 with h3 | h3
    . rw [h3]
    . omega
  . intro j d_le_j
    apply Nat.testBit_eq_false_of_lt
    apply Nat.lt_of_lt_of_le (sum_bits_lt_mod_md hd _) (by scalar_tac +nonLin : 2 ^ d ≤ 2 ^ j)

/-!
# Streamed byteDecode

Below, we prove that the streamed version of `byteDecode` is correct.
-/

/-- `d`: the number of bits used to represent an element/coefficient
    `n`: the number of bytes in the accumulator
-/
structure Stream.DecodeState (d n : ℕ) where
  F : Vector ℕ 256
  num_bytes_read : ℕ
  acc : BitVec (8 * n)
  num_bits_in_acc : ℕ

/-- A helper function that isolates some code that appears multiple times in `ntt.decode_coefficient` -/
def Stream.decode.load_acc {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d) (s : DecodeState d n) :
  BitVec (8 * n) :=
  let bytes_to_decode := List.slice s.num_bytes_read (s.num_bytes_read + n) b
  let acc := BitVec.fromLEBytes bytes_to_decode
  acc.setWidth' (by simp_scalar)

/-- A helper function that isolates some code that appears multiple times in `ntt.decode_coefficient`.
    `Stream.decode.pop_bits_from_acc` outputs:
    - `bits_to_decode` (As many bits of the next coefficient as could be retrieved from `acc`)
    - An updated `acc`
    - An updated `num_bits_in_acc` -/
def Stream.decode.pop_bits_from_acc {n : ℕ} (acc : BitVec (8 * n))
  (num_bits_to_decode num_bits_in_acc : ℕ) : BitVec (8 * n) × BitVec (8 * n) × ℕ :=
  let mask := (1#(8*n) <<< num_bits_to_decode) - 1
  let bits_to_decode := acc &&& mask
  let updated_acc := acc >>> num_bits_to_decode
  let updated_num_bits_in_acc := num_bits_in_acc - num_bits_to_decode
  (bits_to_decode, updated_acc, updated_num_bits_in_acc)

def Stream.decode.body {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d) (s : DecodeState d n) (i : ℕ) :
  DecodeState d n :=
  if s.num_bits_in_acc == 0 then
    let acc1 := load_acc b hb s
    let num_bytes_read := s.num_bytes_read + n
    let num_bits_in_acc := 8 * n
    -- `d < num_bits_in_acc` in practice, but because `d` and `n` are parameters here, we need to use `min`
    let num_bits_to_decode := min d num_bits_in_acc
    let (bits_to_decode, acc2, num_bits_in_acc) := pop_bits_from_acc acc1 num_bits_to_decode num_bits_in_acc
    let F := s.F.set! i bits_to_decode.toNat
    {s with F, num_bytes_read, acc := acc2, num_bits_in_acc}
  else
    -- Here, the `min` is nontrivial because `s.num_bits_in_acc` might genuinely be less than `d`
    let num_bits_to_decode := min d s.num_bits_in_acc
    let (bits_to_decode, acc1, num_bits_in_acc) :=
      pop_bits_from_acc s.acc num_bits_to_decode s.num_bits_in_acc
    if d > num_bits_to_decode then
      let acc2 := load_acc b hb s
      let num_bytes_read := s.num_bytes_read + n
      -- Using the name `num_bits_to_decode1` to match Funs.lean's `n_bits_to_decode1`
      let num_bits_to_decode1 := d - num_bits_to_decode
      let (bits_to_decode1, acc3, num_bits_in_acc2) := pop_bits_from_acc acc2 num_bits_to_decode1 (8 * n)
      let coefficient := bits_to_decode ||| (bits_to_decode1 <<< num_bits_to_decode)
      let F := s.F.set! i coefficient.toNat
      {s with F, num_bytes_read, acc := acc3, num_bits_in_acc := num_bits_in_acc2}
    else
      let F := s.F.set! i bits_to_decode.toNat
      {s with F, acc := acc1, num_bits_in_acc}

def Stream.decode.recBody {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d) (s : DecodeState d n) (i : ℕ) :
  DecodeState d n :=
  List.foldl (fun s i => body b hb s i) s (List.range' i (256 - i))

def Stream.decode (d n : ℕ) (b : List Byte) (hb : b.length = 32 * d) : Vector ℕ 256 :=
  let s : DecodeState d n := {
    F := Vector.replicate 256 0,
    num_bytes_read := 0,
    acc := 0,
    num_bits_in_acc := 0
  }
  (decode.recBody b hb s 0).F

def Stream.decode.length_inv (d n : ℕ) (num_bytes_read num_bits_in_acc i : ℕ) : Prop :=
  i ≤ 256 ∧
  8 * num_bytes_read = d * i + num_bits_in_acc ∧
  (d * i + num_bits_in_acc) % (8 * n) = 0

def Stream.decode.inv {d n : ℕ} (b : List Byte) (s : DecodeState d n) (i : ℕ) : Prop :=
  -- The lengths are correct
  length_inv d n s.num_bytes_read s.num_bits_in_acc i ∧
  -- All coefficients up to i have been properly set in F
  (∀ j < i, ∀ k < d, s.F[j]!.testBit k = b[(d * j + k) / 8]!.testBit ((d * j + k) % 8)) ∧
  -- All bits are properly set in the accummulator
  (∀ j < s.num_bits_in_acc, s.acc[j]! =
    b[(8 * s.num_bytes_read - s.num_bits_in_acc + j) / 8]!.testBit
      ((8 * s.num_bytes_read - s.num_bits_in_acc + j) % 8)) ∧
  (∀ j ∈ [s.num_bits_in_acc:8*n], s.acc[j]! = false) ∧
  -- All coefficients in F are less than `m d`
  (∀ j < i, s.F[j]! < m d)

def Stream.decode.body.length_spec {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256 := by omega) (hdn : d < 8 * n := by omega)
  (hinv : length_inv d n s.num_bytes_read s.num_bits_in_acc i) :
  let s1 := body b hb s i; length_inv d n s1.num_bytes_read s1.num_bits_in_acc (i + 1) := by
  simp only [length_inv, body]
  simp only [length_inv] at hinv
  obtain ⟨hinv0, hinv1, hinv2⟩ := hinv
  constructor
  . omega
  . split
    . next num_bits_in_acc_eq_zero =>
      simp only [beq_iff_eq] at num_bits_in_acc_eq_zero
      simp only [num_bits_in_acc_eq_zero, add_zero] at hinv2
      simp only [pop_bits_from_acc, BitVec.setWidth'_eq, BitVec.ofNat_eq_ofNat,
        BitVec.shiftLeft_sub_one_eq_mod]
      constructor
      . simp_scalar [mul_add] -- Automation note: We need `mul_add` to ensure that `hinv1` is applied
      . simp_scalar [mul_add, mul_one]
        have : d * i + d + (8 * n - d) = d * i + 8 * n := by omega
        simp only [this, Nat.add_mod_right, hinv2]
    . next num_bits_in_acc_ne_zero =>
      split
      . next num_bits_in_acc_lt_d =>
        simp only [gt_iff_lt, inf_lt_left, not_le] at num_bits_in_acc_lt_d
        simp only [pop_bits_from_acc, BitVec.setWidth'_eq, BitVec.ofNat_eq_ofNat,
          BitVec.shiftLeft_sub_one_eq_mod]
        constructor
        . simp_scalar [mul_add] -- Automation note: We need `mul_add` to ensure that `hinv1` is applied
        . simp_scalar [mul_add, mul_one]
          have : d * i + d + (8 * n - (d - s.num_bits_in_acc)) = d * i + s.num_bits_in_acc + 8 * n := by
            omega
          simp only [this, Nat.add_mod_right, hinv2]
      . next hmin =>
        simp only [gt_iff_lt, inf_lt_left, not_le, not_lt] at hmin
        simp only [hinv1, pop_bits_from_acc, hmin, inf_of_le_left, BitVec.ofNat_eq_ofNat,
          BitVec.shiftLeft_sub_one_eq_mod]
        constructor
        . /- Automation note: I'm suprised `scalar_nf; omega` succeeds but none of the following work:
             - `scalar_tac`
             - `simp_scalar`
             - `scalar_eq_nf` -/
          scalar_nf
          omega
        . scalar_nf at hinv2
          scalar_nf
          have : d + d * i + (s.num_bits_in_acc - d) = d * i + s.num_bits_in_acc := by omega
          rw [this, hinv2]

def Stream.decode.load_acc.spec {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (j : ℕ) (hj : j < 8 * n) :
  let res := load_acc b hb s;
  res[j]! = b[(8 * s.num_bytes_read + j) / 8]!.testBit ((8 * s.num_bytes_read + j) % 8) := by
  -- Automation note: `simp_lists_scalar [load_acc, List.slice]` does not close this goal
  -- but `simp [load_acc, List.slice]; simp_lists_scalar` does.
  simp only [load_acc, List.slice, BitVec.setWidth'_eq, Nat.mul_add_mod_self_left]
  simp_lists_scalar

/- **TODO** Need an assumption that the next `num_bits_to_decode` bits of `acc`
   yield a number that is `≤ m d`. When `d < 12`, this is equivalent to saying
   `2 ^ num_bits_to_decode ≤ m d`, but when `d = num_bits_to_decode = 12`, the
   assumption is more complicated. This assumption is to facilitate the proof of
   `h0 : ∀ j < num_bits_to_decode, (res.1.toNat : ZMod (m d)).val.testBit j = res.1[j]!` -/
def Stream.decode.pop_bits_from_acc.spec {n : ℕ} (d : ℕ) (acc : BitVec (8 * n))
  (num_bits_to_decode num_bits_in_acc : ℕ) (hd : d < 13) (h1 : num_bits_to_decode ≤ d)
  (h2 : ∀ j ∈ [num_bits_in_acc:8*n], acc[j]! = false)
  (h3 : ∑ (a : Fin num_bits_to_decode), (Bool.toNat acc[a.val]!) * 2^a.val < m d) :
  let res := pop_bits_from_acc acc num_bits_to_decode num_bits_in_acc;
  (res.1.toNat < m d) ∧
  (∀ j < num_bits_to_decode, res.1[j]! = acc[j]!) ∧
  (∀ j ∈ [num_bits_to_decode: 8 * n], res.1[j]! = false) ∧
  (∀ j < num_bits_in_acc - num_bits_to_decode, res.2.1[j]! = acc[j + num_bits_to_decode]!) ∧
  (∀ j ∈ [num_bits_in_acc - num_bits_to_decode: 8*n], res.2.1[j]! = false) ∧
  res.2.2 = num_bits_in_acc - num_bits_to_decode := by
  intro res
  simp only [ZMod.val_natCast, mem_std_range_step_one, and_imp]
  have heq : ∀ j < num_bits_to_decode, res.1[j]! = acc[j]! := by
    intro j hj
    simp only [pop_bits_from_acc, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod, res]
    exact BitVec.getElem!_mod_pow2_eq acc num_bits_to_decode j hj
  have heq_false : ∀ (j : ℕ), num_bits_to_decode ≤ j → j < 8 * n → res.1[j]! = false := by
    intro j hj1 hj2
    simp only [res, pop_bits_from_acc, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod]
    exact BitVec.getElem!_mod_pow2_false acc num_bits_to_decode j hj1
  have : res.1.toNat = ∑ (a : Fin num_bits_to_decode), (Bool.toNat acc[a.val]!) * 2^a.val := by
    conv => arg 2; arg 2; intro x; arg 1; arg 1; rw [← heq x.1 x.2]
    apply Nat.eq_of_testBit_eq
    intro i
    dcases hi1 : i < num_bits_to_decode
    . rw [← BitVec.getElem!_eq_testBit_toNat, testBit_of_sum num_bits_to_decode (by omega) i hi1]
    . dcases hi2 : i < 8 * n
      . rw [← BitVec.getElem!_eq_testBit_toNat, heq_false i (by omega) hi2]
        apply Eq.symm
        apply Nat.testBit_eq_false_of_lt
        exact Nat.lt_of_lt_of_le (sum_bits_lt (by omega) _) (by scalar_tac +nonLin)
      . rw [BitVec.getElem!_toNat_eq_false res.1 i (by omega)]
        apply Eq.symm
        apply Nat.testBit_eq_false_of_lt
        exact Nat.lt_of_lt_of_le (sum_bits_lt (by omega) _) (by scalar_tac +nonLin)
  split_conjs
  . rw [this]
    exact h3
  . exact heq
  . exact heq_false
  . simp [res, pop_bits_from_acc, add_comm]
  . intro j hj1 hj2
    simp only [pop_bits_from_acc, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod,
      BitVec.getElem!_shiftRight, res]
    simp only [mem_std_range_step_one, and_imp, res] at h2
    -- **NOTE** If `num_bits_to_decode + j` is out of bounds, we rely on the default behavior of
    -- `BitVec.getElem!` as defined by `BitVec.getElem!_eq_false`
    dcases bounds_check : num_bits_to_decode + j < 8 * n
    . exact h2 (num_bits_to_decode + j) (by omega) bounds_check
    . simp_all only [tsub_le_iff_right, not_lt, BitVec.getElem!_eq_false]
  . simp [res, pop_bits_from_acc]

/-- Yields `Stream.decode.body.spec` in the case that the accumulator does not need to be loaded at all -/
def Stream.decode.body.spec_no_load {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hd1 : d < 13) (hi : i < 256) (hdn : d < 8 * n := by omega)
  (hb2 : ∀ i < 256, ∑ (a : Fin d), (Bool.toNat (b[(d * i + a) / 8]!.testBit ((d * i + a) % 8))) * 2^a.val < m d)
  (hinv : inv b s i) (hd2 : d ≤ s.num_bits_in_acc) (h_num_bits_in_acc : s.num_bits_in_acc ≠ 0) :
  let s1 := body b hb s i; inv b s1 (i + 1) := by
  unfold inv at hinv
  obtain ⟨hinv1, hinv2, hinv3, hinv4, hinv5⟩ := hinv
  unfold inv
  constructor -- Automation note: I'm surprised that `split_conjs` doesn't do anything here
  . apply length_spec <;> simp_all
  . simp only [body, beq_iff_eq, h_num_bits_in_acc, ↓reduceIte, hd2, inf_of_le_left, gt_iff_lt,
      lt_self_iff_false, mem_std_range_step_one, and_imp]
    unfold length_inv at hinv1
    have : ∑ (a : Fin d), s.acc[a.val]!.toNat * 2 ^ a.val < m d := by
      conv => arg 1; arg 2; intro a; arg 1; arg 1; rw [hinv3 a.val (by omega)]
      rw [(by omega : 8 * s.num_bytes_read - s.num_bits_in_acc = d * i)]
      exact hb2 i hi
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := pop_bits_from_acc.spec d s.acc d s.num_bits_in_acc hd1 (d.le_refl) hinv4 this
    split_conjs
    . intro j j_le_i k k_lt_d
      dcases hj : i = j
      . rw [hj, Vector.getElem!_set!]
        . have : 8 * s.num_bytes_read - s.num_bits_in_acc = d * i := by omega
          rw [← BitVec.getElem!_eq_testBit_toNat, h1 k k_lt_d, hinv3 k (by omega), this, hj]
        . omega
      . rw [Vector.getElem!_set!_ne hj, hinv2 j (by omega) k k_lt_d]
    . intro j hj
      -- Automation: It is unsurprising but unfortunate that this lemma needs to be added manually
      have : 8 * s.num_bytes_read - (s.num_bits_in_acc - d) =
        8 * s.num_bytes_read - s.num_bits_in_acc + d := by
        omega
      rw [h3 j hj, hinv3 (j + d) (by scalar_tac), h5, this]
      scalar_nf
    . intro j hj1 hj2
      simp only [mem_std_range_step_one, and_imp] at h4
      exact h4 j hj1 hj2
    . intro j hj
      dcases hij : i = j
      . simp_lists [hij]
        exact h0
      . simp only [ne_eq, hij, not_false_eq_true, Vector.getElem!_set!_ne]
        exact hinv5 j (by omega)

/-- Yields `Stream.decode.body.spec` in the case that the accumulator needs to be loaded immediately -/
def Stream.decode.body.spec_early_load {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hd : d < 13) (hi : i < 256 := by omega) (hdn : d < 8 * n := by omega)
  (hb2 : ∀ i < 256, ∑ (a : Fin d), (Bool.toNat (b[(d * i + a) / 8]!.testBit ((d * i + a) % 8))) * 2^a.val < m d)
  (hinv : inv b s i) (h_num_bits_in_acc : s.num_bits_in_acc = 0) :
  let s1 := body b hb s i; inv b s1 (i + 1) := by
  unfold inv at hinv
  obtain ⟨hinv1, hinv2, hinv3, hinv4, hinv5⟩ := hinv
  simp only [mem_std_range_step_one, and_imp] at hinv4
  unfold inv
  constructor -- Automation note: `split_conjs` likewise fails here
  . apply length_spec <;> simp_all
  . simp only [body, h_num_bits_in_acc, beq_self_eq_true, ↓reduceIte, BitVec.setWidth'_eq,
      mem_std_range_step_one, and_imp]
    unfold length_inv at hinv1
    simp only [h_num_bits_in_acc, add_zero] at hinv1
    have : ∑ a : Fin (min d (8 * n)), (load_acc b hb s)[a.val]!.toNat * 2 ^ a.val < m d := by
      conv => arg 1; arg 2; intro a; rw [load_acc.spec b hb s a (by omega)]
      rw [(by omega : min d (8 * n) = d), hinv1.2.1]
      exact hb2 i hi
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      pop_bits_from_acc.spec d (load_acc b hb s) (min d (8 * n)) (8 * n) hd (by simp) (by simp) this
    split_conjs
    . intro j j_le_i k k_lt_d
      dcases hj : i = j
      . rw [hj, Vector.getElem!_set!]
        . simp only [lt_inf_iff, and_imp] at h1
          simp only [ZMod.val_natCast, ← BitVec.getElem!_eq_testBit_toNat, h1 k k_lt_d (by omega)]
          rw [load_acc.spec b hb s k (by omega), Byte.testBit, ← BitVec.getElem!_eq_testBit_toNat]
          scalar_tac
        . omega
      . rw [Vector.getElem!_set!_ne hj, hinv2 j (by omega) k k_lt_d]
    . intro j hj
      rw [h5] at hj
      have : (8 * s.num_bytes_read + (j + min d (8 * n))) =
        (8 * (s.num_bytes_read + n) - (8 * n - min d (8 * n)) + j) := by omega
      rw [h3 j hj, h5, load_acc.spec b hb s (j + (min d (8 * n))) (by omega), this]
    . intro j hj1 hj2
      rw [h5] at hj1
      simp only [mem_std_range_step_one, tsub_le_iff_right, and_imp] at h4
      exact h4 j (by omega) hj2
    . intro j hj
      dcases hij : i = j
      . simp_lists [hij]
        exact h0
      . simp only [ne_eq, hij, not_false_eq_true, Vector.getElem!_set!_ne]
        exact hinv5 j (by omega)

theorem Stream.decode.body.spec_late_load_aux {d n : ℕ} (b : List Byte) (hb1 : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256 := by omega) (hdn : d < 8 * n := by omega)
  (hb2 : ∀ i < 256, ∑ (a : Fin d), (Bool.toNat (b[(d * i + a) / 8]!.testBit ((d * i + a) % 8))) * 2^a.val < m d)
  (hd1 : d < 13) (hd2 : s.num_bits_in_acc < d) (hinv1 : length_inv d n s.num_bytes_read s.num_bits_in_acc i)
  (hinv2 : ∀ j < i, ∀ k < d, s.F[j]!.testBit k = b[(d * j + k) / 8]!.testBit ((d * j + k) % 8))
  (hinv3 :
    ∀ j < s.num_bits_in_acc,
      s.acc[j]! =
        b[(8 * s.num_bytes_read - s.num_bits_in_acc + j) / 8]!.testBit
          ((8 * s.num_bytes_read - s.num_bits_in_acc + j) % 8))
  (hinv4 : ∀ j ∈ [s.num_bits_in_acc: 8 * n], s.acc[j]! = false)
  (sum_load_acc_lt_md : ∑ a : Fin (d - s.num_bits_in_acc), (load_acc b hb1 s)[a.val]!.toNat * 2 ^ a.val < m d)
  (j : ℕ) (j_le_i : j < i + 1) (k : Nat) (k_lt_d : k < d) :
    (s.F.set! i
                ↑((pop_bits_from_acc s.acc s.num_bits_in_acc s.num_bits_in_acc).1.toNat |||
                    (pop_bits_from_acc (load_acc b hb1 s) (d - s.num_bits_in_acc) (8 * n)).1.toNat <<<
                        s.num_bits_in_acc %
                      2 ^ (8 * n)))[j]!.testBit
        k =
      b[(d * j + k) / 8]!.testBit ((d * j + k) % 8) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := pop_bits_from_acc.spec d
    (load_acc b hb1 s) (d - s.num_bits_in_acc) (8 * n) hd1 (by simp) (by simp) sum_load_acc_lt_md
  dcases hj : i = j
  . have : ∑ a : Fin s.num_bits_in_acc, s.acc[a.val]!.toNat * 2 ^ a.val < m d := by
      conv => arg 1; arg 2; intro a; arg 1; arg 1; rw [hinv3 a.val (by omega)]
      unfold length_inv at hinv1
      rw [(by omega : 8 * s.num_bytes_read - s.num_bits_in_acc = d * i)]
      have := sum_le_sum1 hd1 hd2 $ fun (a : Fin d) => b[(d * i + a.val) / 8]!.testBit ((d * i + a.val) % 8)
      exact Nat.lt_of_le_of_lt this $ hb2 i hi
    obtain ⟨h0', h1', h2', h3', h4', h5'⟩ :=
      pop_bits_from_acc.spec d s.acc s.num_bits_in_acc s.num_bits_in_acc hd1 (by omega) hinv4 this
    -- Automation note: This `simp_lists_scalar` is pretty slow. It would be nice to have
    -- `simp_lists_scalar?` for here
    simp_lists_scalar
    tlet x := (pop_bits_from_acc s.acc s.num_bits_in_acc s.num_bits_in_acc).1
    tlet y := (pop_bits_from_acc (load_acc b hb1 s) (d - s.num_bits_in_acc) (8 * n)).1
    have hx : x.toNat < 2^s.num_bits_in_acc := lt_num_bits h2'
    have hy : y.toNat < 2^(d - s.num_bits_in_acc) := lt_num_bits h2
    have testBit_of_add : ∀ a < d, (x.toNat + y.toNat <<< s.num_bits_in_acc).testBit a =
      if a < s.num_bits_in_acc then x.toNat.testBit a else y.toNat.testBit (a - s.num_bits_in_acc) := by
      intro a ha
      split
      . next ha =>
        exact testBit_of_add1 x.toNat y.toNat d s.num_bits_in_acc a hd1 hd2 ha hx hy
      . next ha =>
        apply testBit_of_add2 x.toNat y.toNat d s.num_bits_in_acc a hd1 (by omega) (by omega) hx hy
    have heq1 : y.toNat <<< s.num_bits_in_acc % 2 ^ (8 * n) = y.toNat <<< s.num_bits_in_acc := by
      apply Nat.mod_eq_of_lt
      have : y.toNat < 2 ^ (8 * n - s.num_bits_in_acc) → y.toNat <<< s.num_bits_in_acc < 2 ^ (8 * n) := by
        rw [Nat.shiftLeft_eq y.toNat s.num_bits_in_acc]
        have : 2 ^ (8 * n) = 2 ^ (8 * n - s.num_bits_in_acc) * 2 ^ s.num_bits_in_acc := by
          rw [← Nat.pow_add, Nat.sub_add_cancel]
          omega
        rw [this, Nat.mul_lt_mul_right]
        . exact id
        . omega
      apply this
      have : 2 ^ (d - s.num_bits_in_acc) < 2 ^ (8 * n - s.num_bits_in_acc) := by scalar_tac +nonLin
      exact Nat.lt_trans hy this
    rw [heq1, bitwise_or_eq_and x.toNat y.toNat d s.num_bits_in_acc hd1 hd2 hx hy, testBit_of_add k k_lt_d]
    split
    . next hk =>
      have : d * j + s.num_bits_in_acc - s.num_bits_in_acc + k = d * j + k := by omega
      rw [← BitVec.getElem!_eq_testBit_toNat, h1' k hk, hinv3 k hk, hinv1.2.1, hj, this]
    . next hk =>
      simp only [not_lt] at hk
      rw [← BitVec.getElem!_eq_testBit_toNat, h1 (k - s.num_bits_in_acc) (by omega), load_acc.spec b hb1 s]
      . have : d * j + s.num_bits_in_acc + (k - s.num_bits_in_acc) = d * j + k := by
          omega
        rw [hinv1.2.1, hj, this]
      . omega
  . simp_lists -- Automation note: It would be nice to have `simp_lists?` to avoid non-terminal simps
    exact hinv2 j (by omega) k k_lt_d

/-- Yields `Stream.decode.body.spec` in the case that the accumulator needs to be loaded after popping
    less than a full coefficient's worth of bits -/
def Stream.decode.body.spec_late_load {d n : ℕ} (b : List Byte) (hb1 : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256 := by omega) (hdn : d < 8 * n := by omega)
  (hb2 : ∀ i < 256, ∑ (a : Fin d), (Bool.toNat (b[(d * i + a) / 8]!.testBit ((d * i + a) % 8))) * 2^a.val < m d)
  (hinv : inv b s i) (hd1 : d < 13) (hd2 : s.num_bits_in_acc < d) (h_num_bits_in_acc : s.num_bits_in_acc ≠ 0) :
  let s1 := body b hb1 s i; inv b s1 (i + 1) := by
  unfold inv at hinv
  obtain ⟨hinv1, hinv2, hinv3, hinv4, hinv5⟩ := hinv
  unfold inv
  constructor -- Automation note: `split_conjs` likewise fails here
  . apply length_spec <;> simp_all
  . simp only [body, beq_iff_eq, h_num_bits_in_acc, ↓reduceIte, gt_iff_lt, inf_lt_left, not_le, hd2,
      BitVec.setWidth'_eq, BitVec.toNat_or, BitVec.toNat_shiftLeft, mem_std_range_step_one, and_imp]
    -- Automation note: This `simp_lists_scalar` is pretty slow. It would be nice to have
    -- `simp_lists_scalar?` for here
    simp_lists_scalar
    have sum_load_acc_lt_md : ∑ a : Fin (d - s.num_bits_in_acc), (load_acc b hb1 s)[a.val]!.toNat * 2 ^ a.val < m d := by
      conv => arg 1; arg 2; intro a; rw [load_acc.spec b hb1 s a (by omega)]
      rw [hinv1.2.1]
      apply Nat.lt_of_le_of_lt _ (hb2 i hi)
      have := sum_le_sum2 hd1 hd2 $ fun (a : Fin d) => b[(d * i + a.val) / 8]!.testBit ((d * i + a.val) % 8)
      simp only at this
      conv at this => arg 1; arg 2; intro a; rw [add_comm a.val, ← add_assoc]
      exact this
    split_conjs
    . exact spec_late_load_aux b hb1 s i hi hdn hb2 hd1 hd2 hinv1 hinv2 hinv3 hinv4 sum_load_acc_lt_md
    . intro j hj
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := pop_bits_from_acc.spec d
        (load_acc b hb1 s) (d - s.num_bits_in_acc) (8 * n) hd1 (by simp) (by simp) sum_load_acc_lt_md
      rw [h5] at hj
      have : (8 * s.num_bytes_read + (j + (d - s.num_bits_in_acc))) =
        (8 * (s.num_bytes_read + n) - (8 * n - (d - s.num_bits_in_acc)) + j) := by
        omega
      rw [h3 j hj, h5, load_acc.spec b hb1 s (j + (d - s.num_bits_in_acc)) (by omega), this]
    . intro j hj1 hj2
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
        pop_bits_from_acc.spec d (load_acc b hb1 s) (d - s.num_bits_in_acc) (8 * n) hd1 (by simp) (by simp) sum_load_acc_lt_md
      simp only [mem_std_range_step_one, tsub_le_iff_right, and_imp] at h4
      exact h4 j (by simp_lists_scalar) hj2
    . intro j hj
      dcases hij : i = j
      . simp_lists [hij]
        obtain ⟨h0, h1, h2, h3, h4, h5⟩ := pop_bits_from_acc.spec d
          (load_acc b hb1 s) (d - s.num_bits_in_acc) (8 * n) hd1 (by simp) (by simp) sum_load_acc_lt_md
        have : ∑ a : Fin s.num_bits_in_acc, s.acc[a.val]!.toNat * 2 ^ a.val < m d := by
          conv => arg 1; arg 2; intro a; arg 1; arg 1; rw [hinv3 a.val (by omega)]
          unfold length_inv at hinv1
          rw [(by omega : 8 * s.num_bytes_read - s.num_bits_in_acc = d * i)]
          have := sum_le_sum1 hd1 hd2 $ fun (a : Fin d) => b[(d * i + a.val) / 8]!.testBit ((d * i + a.val) % 8)
          exact Nat.lt_of_le_of_lt this $ hb2 i hi
        obtain ⟨h0', h1', h2', h3', h4', h5'⟩ :=
          pop_bits_from_acc.spec d s.acc s.num_bits_in_acc s.num_bits_in_acc hd1 (by omega) hinv4 this
        tlet x := (pop_bits_from_acc s.acc s.num_bits_in_acc s.num_bits_in_acc).1
        tlet y := (pop_bits_from_acc (load_acc b hb1 s) (d - s.num_bits_in_acc) (8 * n)).1
        have hx : x.toNat < 2^s.num_bits_in_acc := lt_num_bits h2'
        have hy : y.toNat < 2^(d - s.num_bits_in_acc) := lt_num_bits h2
        have testBit_of_add : ∀ a < d, (x.toNat + y.toNat <<< s.num_bits_in_acc).testBit a =
          if a < s.num_bits_in_acc then x.toNat.testBit a else y.toNat.testBit (a - s.num_bits_in_acc) := by
          intro a ha
          split
          . next ha =>
            exact testBit_of_add1 x.toNat y.toNat d s.num_bits_in_acc a hd1 hd2 ha hx hy
          . next ha =>
            apply testBit_of_add2 x.toNat y.toNat d s.num_bits_in_acc a hd1 (by omega) (by omega) hx hy
        have heq1 : y.toNat <<< s.num_bits_in_acc % 2 ^ (8 * n) = y.toNat <<< s.num_bits_in_acc := by
          apply Nat.mod_eq_of_lt
          have : y.toNat < 2 ^ (8 * n - s.num_bits_in_acc) → y.toNat <<< s.num_bits_in_acc < 2 ^ (8 * n) := by
            rw [Nat.shiftLeft_eq y.toNat s.num_bits_in_acc]
            have : 2 ^ (8 * n) = 2 ^ (8 * n - s.num_bits_in_acc) * 2 ^ s.num_bits_in_acc := by
              rw [← Nat.pow_add, Nat.sub_add_cancel]
              omega
            rw [this, Nat.mul_lt_mul_right]
            . exact id
            . omega
          apply this
          have : 2 ^ (d - s.num_bits_in_acc) < 2 ^ (8 * n - s.num_bits_in_acc) := by scalar_tac +nonLin
          exact Nat.lt_trans hy this
        have : x.toNat + y.toNat <<< s.num_bits_in_acc =
          ∑ (a : Fin d),
            (Bool.toNat (b[(8 * s.num_bytes_read - s.num_bits_in_acc + a) / 8]!.testBit
              ((8 * s.num_bytes_read  - s.num_bits_in_acc + a) % 8))) * 2^a.val := by
          apply Nat.eq_of_testBit_eq
          intro a
          by_cases ha : a < d
          . let f := fun (a : Fin d) =>
              b[(8 * s.num_bytes_read - s.num_bits_in_acc + ↑a) / 8]!.testBit
                ((8 * s.num_bytes_read  - s.num_bits_in_acc + ↑a) % 8)
            rw [testBit_of_add a ha, testBit_of_sum d hd1 a ha f]
            split
            . next ha2 =>
              rw [← BitVec.getElem!_eq_testBit_toNat, h1' a ha2, hinv3 a ha2]
            . next ha2 =>
              have : 8 * s.num_bytes_read + (a - s.num_bits_in_acc) = 8 * s.num_bytes_read + a - s.num_bits_in_acc := by
                omega
              have : 8 * s.num_bytes_read + (a - s.num_bits_in_acc) = 8 * s.num_bytes_read - s.num_bits_in_acc + a := by
                rw [this]
                apply Nat.sub_add_comm
                rw [hinv1.2.1]
                omega
              rw [← BitVec.getElem!_eq_testBit_toNat, h1 (a - s.num_bits_in_acc) (by omega),
                load_acc.spec b hb1 s (a - s.num_bits_in_acc) (by omega), this]
          . rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
            . exact Nat.lt_of_lt_of_le (sum_bits_lt hd1 _) (by scalar_tac +nonLin)
            . exact Nat.lt_of_lt_of_le (sum_shift_lt x.toNat y.toNat s.num_bits_in_acc d hx hy hd1 hd2) (by scalar_tac +nonLin)
        rw [heq1, bitwise_or_eq_and x.toNat y.toNat d s.num_bits_in_acc hd1 hd2 hx hy, this, hinv1.2.1, add_tsub_cancel_right]
        exact hb2 i hi
      . simp only [ne_eq, hij, not_false_eq_true, Vector.getElem!_set!_ne]
        exact hinv5 j (by omega)

def Stream.decode.body.spec {d n : ℕ} (b : List Byte) (hb1 : b.length = 32 * d) (hd : d < 13)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256) (hdn : d < 8 * n)
  (hb2 : ∀ i < 256, ∑ (a : Fin d), (Bool.toNat (b[(d * i + a) / 8]!.testBit ((d * i + a) % 8))) * 2^a.val < m d)
  (hinv : inv b s i) : let s1 := body b hb1 s i; inv b s1 (i + 1) := by
  dcases h_num_bits_in_acc : s.num_bits_in_acc = 0
  . exact spec_early_load b hb1 s i hd hi hdn hb2 hinv h_num_bits_in_acc
  . rcases Nat.lt_or_ge s.num_bits_in_acc d with hd2 | hd2
    . exact spec_late_load b hb1 s i hi hdn hb2 hinv hd hd2 h_num_bits_in_acc
    . exact spec_no_load b hb1 s i hd hi hdn hb2 hinv hd2 h_num_bits_in_acc

theorem Stream.decode.recBody.spec {d n : ℕ} (b : List Byte) (hb1 : b.length = 32 * d) (hd : d < 13)
  (s : DecodeState d n) (i : ℕ) (hi : i ≤ 256) (hdn : d < 8 * n)
  (hb2 : ∀ i < 256, ∑ (a : Fin d), (Bool.toNat (b[(d * i + a) / 8]!.testBit ((d * i + a) % 8))) * 2^a.val < m d)
  (hinv : inv b s i) : let s1 := recBody b hb1 s i; inv b s1 256 := by
  if hi : i = 256 then
    simp only [hi]
    unfold recBody
    simp only [tsub_self, List.range'_zero, List.foldl_nil]
    simp_all
  else
    unfold recBody
    have : 256 - i = (256 - (i+1)) + 1 := by omega
    rw [this, List.range'_succ]
    simp only [Nat.reduceSubDiff, List.foldl_cons]
    have hinv1 := body.spec b hb1 hd s i (by omega) hdn hb2 hinv
    have hinv2 := spec b hb1 hd (body b hb1 s i) (i + 1) (by omega) hdn hb2 hinv1
    unfold recBody at hinv2
    simp only [Nat.reduceSubDiff] at hinv2
    exact hinv2

theorem Stream.decode.spec_aux {d n : ℕ} (B : Vector Byte (32 * d)) (hd : d < 13) (hdn : d < 8 * n)
  (hB : ∀ i < 256, ∑ (a : Fin d), (Bool.toNat (B[(d * i + a) / 8]!.testBit ((d * i + a) % 8))) * 2^a.val < m d) :
  ∀ i < 256,
    (∀ j < d, (decode d n B.toList B.toList_length)[i]!.testBit j =
      B[(d * i + j) / 8]!.testBit ((d * i + j) % 8)) ∧
    (∀ j : Nat, d ≤ j → (decode d n B.toList B.toList_length)[i]!.testBit j = false) := by
  intro i hi
  simp only [← Array.getElem!_toList, ← Vector.getElem!_toArray] at hB
  let s : DecodeState d n := { F := Vector.replicate 256 0, num_bytes_read := 0, acc := 0, num_bits_in_acc := 0 }
  have hinv0 : inv B.toList s 0 := by
    unfold inv
    split_conjs
    . simp only [length_inv, zero_le, mul_zero, add_zero, Nat.zero_mod, and_self, s]
    . simp_lists
    . simp_lists
    . simp only [mem_std_range_step_one, and_imp, s]
      intro j hj1 hj2
      simp only [BitVec.ofNat_eq_ofNat, BitVec.getElem!_zero, s]
    . simp only [not_lt_zero', IsEmpty.forall_iff, implies_true, s]
  have hinv := recBody.spec B.toList B.toList_length hd s 0 (by omega) hdn hB hinv0
  obtain ⟨h0, h1, h2, h3, h4⟩ := hinv
  unfold decode
  constructor
  . intro j hj
    rw [h1 i hi j hj, Array.getElem!_toList, Vector.getElem!_toArray]
  . intro j hj
    apply Nat.testBit_eq_false_of_lt
    apply Nat.lt_of_lt_of_le _ (by scalar_tac +nonLin : 2 ^ d ≤ 2 ^ j)
    exact Nat.lt_of_lt_of_le (h4 i hi) (md_le_two_pow_d hd)

theorem Stream.decode.spec {d n : ℕ} (B : Vector Byte (32 * d)) (hd : d < 13) (hdn : d < 8 * n)
  (hB : ∀ i < 256, ∑ (a : Fin d), (Bool.toNat (B[(d * i + a) / 8]!.testBit ((d * i + a) % 8))) * 2^a.val < m d) :
  decode d n B.toList B.toList_length = (Spec.byteDecode B : Spec.Polynomial (m d)).map (fun x => x.val) := by
  rw [← Target.byteDecode.eq_spec]
  rw [Vector.eq_iff_forall_eq_getElem!]
  intro i hi
  rw [Vector.getElem!_map_eq _ _ _ hi]
  apply Nat.eq_of_testBit_eq
  intro j
  dcases hj : j < d
  . rw [(Target.byteDecode.spec B hd hB i hi).1 j hj, (spec_aux B hd hdn hB i hi).1 j hj]
  . rw [(Target.byteDecode.spec B hd hB i hi).2 j (by omega), (spec_aux B hd hdn hB i hi).2 j (by omega)]

/-!
# Decompress
-/

def decompressOpt (d : ℕ) (y : ℕ) : Spec.Zq :=
  if d < 12 then ⌈ ((Q : ℚ) / ((2 : ℚ)^d)) * y ⌋ else y

def decompress (d : ℕ) (y : ℕ) : ℕ :=
  if d < 12 then
    let coefficient := y * Q
    let coefficient := coefficient >>> (d - 1)
    let coefficient := coefficient + 1
    coefficient >>> 1
  else
    y

theorem decompress_eq (d : ℕ) (hd : d < 12) (y : ℕ) (h : y < 2^d) :
  decompress d y = ⌈ ((Q : ℚ) / (2^d : ℚ)) * y ⌋ % Q := by
  revert y
  revert d
  brute

/-!
# Decode and decompress
-/

def Stream.decode_decompressOpt.body {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : Stream.DecodeState d n) (coefficient_idx : ℕ) : Stream.DecodeState d n :=
  let s' := decode.body b hb s coefficient_idx
  {s' with F := s'.F.set! coefficient_idx (decompressOpt d s'.F[coefficient_idx]!).val}

def Stream.decode_decompressOpt.recBody {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : Stream.DecodeState d n) (i : ℕ) : Stream.DecodeState d n :=
  List.foldl (fun s i => decode_decompressOpt.body b hb s i) s (List.range' i (256 - i))

def Stream.decode_decompressOpt (d n : ℕ) (b : List Byte) (hb : b.length = 32 * d) : Vector ℕ 256 :=
  let s : DecodeState d n := {
    F := Vector.replicate 256 0,
    num_bytes_read := 0,
    acc := 0,
    num_bits_in_acc := 0
  }
  (decode_decompressOpt.recBody b hb s 0).F

def Stream.decode_decompressOpt_eq (d n : ℕ) (B : Vector Byte (32 * d)) (hd : d < 13) (hdn : d < 8 * n)
  (hB : ∀ i < 256, ∑ a : Fin d, (B[(d * i + ↑a) / 8]!.testBit ((d * i + ↑a) % 8)).toNat * 2 ^ a.val < m d) :
  decode_decompressOpt d n B.toList B.toList_length =
    (Spec.byteDecode B).map (fun (x : ZMod (m d)) => (decompressOpt d x.val).val) := by
  have : (Spec.byteDecode B).map (fun (x : ZMod (m d)) => (decompressOpt d x.val).val) =
    ((Spec.byteDecode B).map (fun (x : ZMod (m d)) => x.val)).map (fun x => (decompressOpt d x).val) := by
    simp only [Vector.map_map, Vector.map_inj_left, Function.comp_apply, implies_true]
  rw [this, ← Stream.decode.spec B hd hdn hB]
  simp only [decode_decompressOpt, decode_decompressOpt.recBody, BitVec.ofNat_eq_ofNat, tsub_zero,
    decode, decode.recBody]
  simp only [Vector.map, Vector.eq_mk, ← Array.toList_inj, Array.toList_map]
  sorry -- Mildly stuck here
