import Symcrust.Properties.CompressEncodeSpecAux
import Mathlib.Algebra.BigOperators.Fin
import Symcrust.Properties.Brute

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

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

def Target.byteDecode.spec1 {m d : ℕ} (B : Vector Byte (32 * d)) :
  ∀ i < 256, (byteDecode m d B)[i]! = ((∑ (j : Fin d), (Bool.toNat (bytesToBits B)[i * d + j]!) * 2^j.val) : ZMod m) := by
  unfold byteDecode
  intro i i_lt_256
  simp only
  have h0 := @decodeCoefficient.inv_0 m d (bytesToBits B)
  have h := recBody.spec (bytesToBits B) (Polynomial.zero m) h0 (by omega : 0 < 256)
  rw [decodeCoefficient.inv] at h
  simp [h.1 i i_lt_256]

theorem Finset.univ_sum_eq_range {β} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
  ∑ (j : Fin n), f j = ∑ j ∈ Finset.range n, f j := by
  match n with
  | 0 => simp
  | n'+1 =>
   simp [Finset.sum_range_succ, Fin.sum_univ_succAbove, Fin.sum_univ_castSucc]
   -- recursive call
   simp [Finset.univ_sum_eq_range]

theorem Finset.sum_range_decompose {m : ℕ} (f : ℕ → ZMod m) (d i : ℕ) (h : i < d) :
  ∑ j ∈ Finset.range d, f j = ∑ j ∈ Finset.range i, f j + f i + ∑ j ∈ Finset.range (d - i - 1), f (i + j + 1) := by
  have : d = i + 1 + (d - i - 1) := by omega
  -- Remark: we could also use: Finset.sum_range_add_sum_Ico
  conv => lhs; rw [this]; simp only [Finset.sum_range_add]
  simp
  congr
  apply funext; intro j
  congr 1; omega

theorem sum_pow_two_eq (n : ℕ) : ∑ i ∈ Finset.range n, 2^i = 2^n - 1 := by
  match n with
  | 0 => simp
  | n'+1 =>
   simp [Finset.sum_range_succ, Nat.pow_add_one]
   simp [sum_pow_two_eq]
   omega

theorem sum_lt_testBit_eq_false (n d i : ℕ) (h : i < d) (f : ℕ → ℕ) :
  (∑ j ∈ Finset.range n, f j * 2 ^ (d + j)).testBit i = false := by
  have : ∑ j ∈ Finset.range n, f j * 2 ^ (d + j) = 2 ^ d * (∑ j ∈ Finset.range n, f j * 2 ^ j) := by
    simp only [Nat.pow_add]
    conv => lhs; arg 2; ext; arg 2; rw [Nat.mul_comm]
    simp only [← Nat.mul_assoc, ← Finset.sum_mul]
    exact Nat.mul_comm (∑ i ∈ Finset.range n, f i * 2 ^ i) (2 ^ d)
  simp [this, Nat.testBit_two_pow_mul]
  intro h
  omega

-- `testBitOfSum` currently takes 15-45s on my computer to typecheck. This isn't unacceptably slow,
-- but adding special treatment for goals of the form `∀ f : Fin d → Bool, ...` might make this faster
set_option profiler true in
theorem testBitOfSum :
  ∀ d < 12, ∀ j : Nat, ∀ hj : j < d, ∀ k < j + 1, ∀ f : Fin d → Bool,
  (∑ (x : Fin d), (f x).toNat * (2 : ZMod (m d)) ^ (x : ℕ)).val.testBit j = f ⟨j, hj⟩ := by
  brute

def Target.byteDecode.spec2 {d : ℕ} (B : Vector Byte (32 * d)) (hd : d < 12):
  ∀ i < 256, ∀ j < d, (byteDecode (m d) d B)[i]!.val.testBit j = B[(d * i + j) / 8]!.testBit ((d * i + j) % 8) := by
  intro i i_lt_256 j j_lt_d
  rw [@spec1 (m d) d B i i_lt_256]
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
  have h := Target.bytesToBits.spec B
  simp only [bytesToBits.post] at h
  have h' : ∀ j < d, (bytesToBits B)[i * d + j]! = B[(i * d + j) / 8]!.testBit ((i * d + j) % 8) := by
    intro j j_lt_d
    have : i * d + j < 256 * d := by
      have : j < 256 * d - i * d → i * d + j < 256 * d := by omega
      apply this
      rw [← Nat.mul_sub_right_distrib]
      have : 1 ≤ 256 - i := by omega
      exact Nat.lt_of_lt_of_le (by omega : j < 1 * d) (Nat.mul_le_mul_right d this)
    have : (i * d + j) / 8 < 32 * d := by omega
    have h' := h ((i * d + j) / 8) this ((i * d + j) % 8) (by omega)
    have : 8 * ((i * d + j) / 8) + (i * d + j) % 8 = i * d + j := by scalar_tac
    rw [this] at h'
    exact h'
  simp only [Fin.is_lt, h']
  rw [mul_comm d i, h' j j_lt_d]
  exact testBitOfSum d hd j j_lt_d 0 (Nat.zero_lt_succ j) _

/-!
# Streamed byteDecode

Below, we prove that the streamed version of `byteDecode` is correct.
-/

/-- `d`: the number of bits used to represent an element/coefficient
    `n`: the number of bytes in the accumulator
-/
structure Stream.DecodeState (d n : ℕ) where
  F : Vector (ZMod (m d)) 256
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

def Stream.decode (d n : ℕ) (b : List Byte) (hb : b.length = 32 * d) : Vector (ZMod (m d)) 256 :=
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
  (∀ j < i, ∀ k < d, s.F[j]!.val.testBit k = b[(d * j + k) / 8]!.testBit ((d * j + k) % 8)) ∧
  -- All bits are properly set in the accummulator
  (∀ j < s.num_bits_in_acc, s.acc[j]! =
    b[(8 * s.num_bytes_read - s.num_bits_in_acc + j) / 8]!.testBit
      ((8 * s.num_bytes_read - s.num_bits_in_acc + j) % 8)) ∧
  ∀ j ∈ [s.num_bits_in_acc:8*n], s.acc[j]! = false

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
  (num_bits_to_decode num_bits_in_acc : ℕ)
  (h : ∀ j ∈ [num_bits_in_acc:8*n], acc[j]! = false):
  let res := pop_bits_from_acc acc num_bits_to_decode num_bits_in_acc;
  (res.1.toNat : ZMod (m d)).val = res.1.toNat ∧
  (∀ j < num_bits_to_decode, res.1[j]! = acc[j]!) ∧
  (∀ j ∈ [num_bits_to_decode: 8 * n], res.1[j]! = false) ∧
  (∀ j < num_bits_in_acc - num_bits_to_decode, res.2.1[j]! = acc[j + num_bits_to_decode]!) ∧
  (∀ j ∈ [num_bits_in_acc - num_bits_to_decode: 8*n], res.2.1[j]! = false) ∧
  res.2.2 = num_bits_in_acc - num_bits_to_decode := by
  intro res
  simp only [ZMod.val_natCast, mem_std_range_step_one, and_imp]
  split_conjs
  . have : res.1.toNat < m d := by
      sorry -- Not provable yet, need the appropriate assumption about `acc`
    rw [Nat.mod_eq_of_lt this]
  . intro j hj
    simp only [pop_bits_from_acc, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod, res]
    exact BitVec.getElem!_mod_pow2_eq acc num_bits_to_decode j hj
  . intro j hj1 hj2
    simp only [res, pop_bits_from_acc, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod]
    exact BitVec.getElem!_mod_pow2_false acc num_bits_to_decode j hj1
  . simp [res, pop_bits_from_acc, add_comm]
  . intro j hj1 hj2
    simp only [pop_bits_from_acc, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod,
      BitVec.getElem!_shiftRight, res]
    simp only [mem_std_range_step_one, and_imp, res] at h
    -- **NOTE** If `num_bits_to_decode + j` is out of bounds, we rely on the default behavior of
    -- `BitVec.getElem!` as defined by `BitVec.getElem!_eq_false`
    dcases bounds_check : num_bits_to_decode + j < 8 * n
    . exact h (num_bits_to_decode + j) (by omega) bounds_check
    . simp_all only [tsub_le_iff_right, not_lt, BitVec.getElem!_eq_false]
  . simp [res, pop_bits_from_acc]

/-- Yields `Stream.decode.body.spec` in the case that the accumulator does not need to be loaded at all -/
def Stream.decode.body.spec_no_load {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256 := by omega) (hdn : d < 8 * n := by omega)
  (hinv : inv b s i) (hd : d ≤ s.num_bits_in_acc) (h_num_bits_in_acc : s.num_bits_in_acc ≠ 0) :
  let s1 := body b hb s i; inv b s1 (i + 1) := by
  unfold inv at hinv
  obtain ⟨hinv1, hinv2, hinv3, hinv4⟩ := hinv
  unfold inv
  constructor -- Automation note: I'm surprised that `split_conjs` doesn't do anything here
  . apply length_spec <;> simp_all
  . simp only [body, beq_iff_eq, h_num_bits_in_acc, ↓reduceIte, hd, inf_of_le_left, gt_iff_lt,
      lt_self_iff_false, mem_std_range_step_one, and_imp]
    unfold length_inv at hinv1
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := pop_bits_from_acc.spec d s.acc d s.num_bits_in_acc hinv4
    split_conjs
    . intro j j_le_i k k_lt_d
      dcases hj : i = j
      . rw [hj, Vector.getElem!_set!]
        . have : 8 * s.num_bytes_read - s.num_bits_in_acc = d * i := by omega
          rw [h0, ← BitVec.getElem!_eq_testBit_toNat, h1 k k_lt_d, hinv3 k (by omega), this, hj]
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

/-- Yields `Stream.decode.body.spec` in the case that the accumulator needs to be loaded immediately -/
def Stream.decode.body.spec_early_load {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256 := by omega) (hdn : d < 8 * n := by omega)
  (hinv : inv b s i) (h_num_bits_in_acc : s.num_bits_in_acc = 0) :
  let s1 := body b hb s i; inv b s1 (i + 1) := by
  unfold inv at hinv
  obtain ⟨hinv1, hinv2, hinv3, hinv4⟩ := hinv
  simp only [mem_std_range_step_one, and_imp] at hinv4
  unfold inv
  constructor -- Automation note: `split_conjs` likewise fails here
  . apply length_spec <;> simp_all
  . simp only [body, h_num_bits_in_acc, beq_self_eq_true, ↓reduceIte, BitVec.setWidth'_eq,
      mem_std_range_step_one, and_imp]
    unfold length_inv at hinv1
    simp only [h_num_bits_in_acc, add_zero] at hinv1
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      pop_bits_from_acc.spec d (load_acc b hb s) (min d (8 * n)) (8 * n) (by simp)
    split_conjs
    . intro j j_le_i k k_lt_d
      dcases hj : i = j
      . rw [hj, Vector.getElem!_set!]
        . simp only [lt_inf_iff, ZMod.val_natCast, and_imp] at h0
          simp only [lt_inf_iff, and_imp] at h1
          simp only [ZMod.val_natCast, h0, ← BitVec.getElem!_eq_testBit_toNat, h1 k k_lt_d (by omega)]
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

-- **TODO** Need to modify this lemma: `x` and `y` shouldn't have the same upper bound
set_option profiler true in -- This takes 10-20s to typecheck
lemma bitwise_or_eq_and (x y d : ℕ) (hd : d < 13) (hx : x < 2^d) (hy : y < 2^d) : x ||| (y <<< d) = x + (y <<< d) := by
  revert y
  revert x
  revert d
  brute

/-- A temporary lemma to make it easier to work on this proof without constantly rerunning the slow
    `simp_lists_scalar` call in `spec_late_load`. -/
theorem Stream.decode.body.extracted_1 {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256 := by omega) (hdn : d < 8 * n := by omega) (hd : s.num_bits_in_acc < d)
  (h_num_bits_in_acc : s.num_bits_in_acc ≠ 0) (hinv1 : length_inv d n s.num_bytes_read s.num_bits_in_acc i)
  (hinv2 : ∀ j < i, ∀ k < d, s.F[j]!.val.testBit k = b[(d * j + k) / 8]!.testBit ((d * j + k) % 8))
  (hinv3 :
    ∀ j < s.num_bits_in_acc,
      s.acc[j]! =
        b[(8 * s.num_bytes_read - s.num_bits_in_acc + j) / 8]!.testBit
          ((8 * s.num_bytes_read - s.num_bits_in_acc + j) % 8))
  (hinv4 : ∀ j ∈ [s.num_bits_in_acc: 8 * n], s.acc[j]! = false)
  (h0 :
    ∀ j < d - s.num_bits_in_acc,
      (↑(pop_bits_from_acc (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n)).1.toNat : ZMod (m d)).val.testBit j =
        (pop_bits_from_acc (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n)).1[j]!)
  (h1 :
    ∀ j < d - s.num_bits_in_acc,
      (pop_bits_from_acc (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n)).1[j]! = (load_acc b hb s)[j]!)
  (h2 :
    ∀ j ∈ [d - s.num_bits_in_acc: 8 * n],
      (pop_bits_from_acc (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n)).1[j]! = false)
  (h3 :
    ∀ j < 8 * n - (d - s.num_bits_in_acc),
      (pop_bits_from_acc (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n)).2.1[j]! =
        (load_acc b hb s)[j + (d - s.num_bits_in_acc)]!)
  (h4 :
    ∀ j ∈ [8 * n - (d - s.num_bits_in_acc): 8 * n],
      (pop_bits_from_acc (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n)).2.1[j]! = false)
  (h5 : (pop_bits_from_acc (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n)).2.2 = 8 * n - (d - s.num_bits_in_acc))
  (j : ℕ) (j_le_i : j < i + 1) (k : ℕ) (k_lt_d : k < d) (hj : i = j) :
  (s.F.set! i
              ↑((pop_bits_from_acc s.acc s.num_bits_in_acc s.num_bits_in_acc).1.toNat |||
                  (pop_bits_from_acc (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n)).1.toNat <<< s.num_bits_in_acc %
                    2 ^ (8 * n)))[j]!.val.testBit
      k =
    b[(d * j + k) / 8]!.testBit ((d * j + k) % 8) := by
  obtain ⟨h0', h1', h2', h3', h4', h5'⟩ :=
    pop_bits_from_acc.spec d s.acc s.num_bits_in_acc s.num_bits_in_acc hinv4
  simp_lists_scalar
  tlet x := (pop_bits_from_acc s.acc s.num_bits_in_acc s.num_bits_in_acc).1
  tlet y := (pop_bits_from_acc (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n)).1
  have heq1 : y.toNat <<< s.num_bits_in_acc % 2 ^ (8 * n) = y.toNat <<< s.num_bits_in_acc := by
    apply Nat.mod_eq_of_lt
    have test : y.toNat < 2^(d - s.num_bits_in_acc) := sorry
    have : y.toNat < 2 ^ (8 * n - s.num_bits_in_acc) → y.toNat <<< s.num_bits_in_acc < 2 ^ (8 * n) := by
      rw [Nat.shiftLeft_eq y.toNat s.num_bits_in_acc]
      simp only [gt_iff_lt] at hdn hd
      have test2 := hd
      -- This is true because s.num_bits_in_acc < d < 8 * n
      sorry
    apply this
    have : 2 ^ (d - s.num_bits_in_acc) < 2 ^ (8 * n - s.num_bits_in_acc) := by scalar_tac +nonLin
    exact Nat.lt_trans test this
  have heq2 : (x.toNat + y.toNat <<< s.num_bits_in_acc) % m d = x.toNat + y.toNat <<< s.num_bits_in_acc := by
    sorry
  have heq3 : (x.toNat + y.toNat <<< s.num_bits_in_acc).testBit k =
    if k < s.num_bits_in_acc then x.toNat.testBit k else y.toNat.testBit (k - s.num_bits_in_acc) := by
    split
    . next hk =>
      sorry
    . next hk =>
      sorry
  rw [heq1, bitwise_or_eq_and x.toNat y.toNat s.num_bits_in_acc sorry sorry sorry, heq2, heq3]
  split
  . next hk =>
    have : d * j + s.num_bits_in_acc - s.num_bits_in_acc + k = d * j + k := by omega
    rw [← BitVec.getElem!_eq_testBit_toNat, h1' k hk, hinv3 k hk, hinv1.2.1, hj, this]
  . next hk =>
    simp only [not_lt] at hk
    rw [← BitVec.getElem!_eq_testBit_toNat, h1 (k - s.num_bits_in_acc) (by omega), load_acc.spec b hb s]
    . have : d * j + s.num_bits_in_acc + (k - s.num_bits_in_acc) = d * j + k := by
        omega
      rw [hinv1.2.1, hj, this]
    . omega

/-- Yields `Stream.decode.body.spec` in the case that the accumulator needs to be loaded after popping
    less than a full coefficient's worth of bits -/
def Stream.decode.body.spec_late_load {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256 := by omega) (hdn : d < 8 * n := by omega)
  (hinv : inv b s i) (hd : s.num_bits_in_acc < d) (h_num_bits_in_acc : s.num_bits_in_acc ≠ 0) :
  let s1 := body b hb s i; inv b s1 (i + 1) := by
  unfold inv at hinv
  obtain ⟨hinv1, hinv2, hinv3, hinv4⟩ := hinv
  unfold inv
  constructor -- Automation note: `split_conjs` likewise fails here
  . apply length_spec <;> simp_all
  . simp only [body, beq_iff_eq, h_num_bits_in_acc, ↓reduceIte, gt_iff_lt, inf_lt_left, not_le, hd,
      BitVec.setWidth'_eq, BitVec.toNat_or, BitVec.toNat_shiftLeft, mem_std_range_step_one, and_imp]
    -- Automation note: This `simp_lists_scalar` is pretty slow. It would be nice to have
    -- `simp_lists_scalar?` for here
    simp_lists_scalar
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
      pop_bits_from_acc.spec d (load_acc b hb s) (d - s.num_bits_in_acc) (8 * n) (by simp)
    split_conjs
    . intro j j_le_i k k_lt_d
      dcases hj : i = j
      . simp_lists
        obtain ⟨h0', h1', h2', h3', h4', h5'⟩ :=
          pop_bits_from_acc.spec d s.acc s.num_bits_in_acc s.num_bits_in_acc hinv4
        simp_scalar
        sorry
      . simp_lists -- Automation note: It would be nice to have `simp_lists?` to avoid non-terminal simps
        exact hinv2 j (by omega) k k_lt_d
    . intro j hj
      rw [h5] at hj
      have : (8 * s.num_bytes_read + (j + (d - s.num_bits_in_acc))) =
        (8 * (s.num_bytes_read + n) - (8 * n - (d - s.num_bits_in_acc)) + j) := by
        omega
      rw [h3 j hj, h5, load_acc.spec b hb s (j + (d - s.num_bits_in_acc)) (by omega), this]
    . intro j hj1 hj2
      simp only [mem_std_range_step_one, tsub_le_iff_right, and_imp] at h4
      exact h4 j (by simp_lists_scalar) hj2

def Stream.decode.body.spec {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256 := by omega) (hdn : d < 8 * n := by omega)
  (hinv : inv b s i) : let s1 := body b hb s i; inv b s1 (i + 1) := by
  dcases h_num_bits_in_acc : s.num_bits_in_acc = 0
  . exact spec_early_load b hb s i hi hdn hinv h_num_bits_in_acc
  . rcases Nat.lt_or_ge s.num_bits_in_acc d with hd | hd
    . exact spec_late_load b hb s i hi hdn hinv hd h_num_bits_in_acc
    . exact spec_no_load b hb s i hi hdn hinv hd h_num_bits_in_acc
