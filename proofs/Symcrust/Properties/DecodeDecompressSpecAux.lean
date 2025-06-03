import Symcrust.Properties.CompressEncodeSpecAux
import Mathlib.Algebra.BigOperators.Fin

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

theorem Finset.sum_range_decompose (f : ℕ → ℕ) (d i : ℕ) (h : i < d) :
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

/-- Auxiliary lemma for `Target.byteDecode.spec2` -/
theorem testBitOfSum {m d : ℕ} {f : Fin d → Bool} (j k : ℕ) (hj : j < d) (hk : k ≤ j) :
  (∑ (x : Fin d), (f x).toNat * (2 : ZMod m) ^ (x : ℕ)).val.testBit j = f ⟨j, hj⟩ := by
  let f' : ℕ → Bool := fun x => if h : x < d then f ⟨x, h⟩ else false
  have f'_eq_f : ∀ x : Fin d, f' x.val = f x := fun x => dif_pos x.isLt
  simp only [← f'_eq_f]
  let sum_formula := fun x => (f' x).toNat * (2 : ZMod m) ^ (x : ℕ)
  rw [Finset.univ_sum_eq_range d sum_formula]
  -- **TODO** sum_formula has output type ZMod m but sum_range_decompose_sum_formula requires
  -- the function's output type to be ℕ (so `rw [Finset.sum_range_decompose sum_formula d j hj]`
  -- does not yet work)
  sorry

def Target.byteDecode.spec2 {m d : ℕ} (B : Vector Byte (32 * d)) :
  ∀ i < 256, ∀ j < d, (byteDecode m d B)[i]!.val.testBit j = B[(d * i + j) / 8]!.testBit ((d * i + j) % 8) := by
  intro i i_lt_256 j j_lt_d
  rw [@spec1 m d B i i_lt_256]
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
  exact testBitOfSum j 0 j_lt_d (zero_le j)

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
    let bytes_to_decode := List.slice s.num_bytes_read (s.num_bytes_read + n) b
    let acc1 : BitVec (8 * bytes_to_decode.length) := BitVec.fromLEBytes bytes_to_decode
    -- I use the name `acc1'` rather than `acc2` so that `acc2` corresponds with `accumulator2` in Funs.lean
    let acc1' : BitVec (8 * n) := acc1.setWidth' (by simp_scalar)
    let num_bytes_read := s.num_bytes_read + n
    let num_bits_in_acc := 8 * n
    -- `d < num_bits_in_acc` in practice, but because `d` and `n` are parameters here, we need to use `min`
    let num_bits_to_decode := min d num_bits_in_acc
    let (bits_to_decode, acc2, num_bits_in_acc) :=
      Stream.decode.pop_bits_from_acc acc1' num_bits_to_decode num_bits_in_acc
    let F := s.F.set! i bits_to_decode.toNat
    {s with F, num_bytes_read, acc := acc2, num_bits_in_acc}
  else
    -- Here, the `min` is nontrivial because `s.num_bits_in_acc` might genuinely be less than `d`
    let num_bits_to_decode := min d s.num_bits_in_acc
    let mask := (1#(8*n) <<< num_bits_to_decode) - 1
    let bits_to_decode := s.acc &&& mask
    let acc1 := s.acc >>> num_bits_to_decode
    let num_bits_in_acc := s.num_bits_in_acc - num_bits_to_decode
    if d > num_bits_to_decode then
      let bytes_to_decode := List.slice s.num_bytes_read (s.num_bytes_read + n) b
      let acc2 : BitVec (8 * bytes_to_decode.length) := BitVec.fromLEBytes bytes_to_decode
      let acc2' : BitVec (8 * n) := acc2.setWidth' (by simp_scalar)
      let num_bytes_read := s.num_bytes_read + n
      -- Using the name `num_bits_to_decode1` to match Funs.lean's `n_bits_to_decode1`
      let num_bits_to_decode1 := d - num_bits_to_decode
      let (bits_to_decode1, acc3, num_bits_in_acc2) := Stream.decode.pop_bits_from_acc acc2' num_bits_to_decode1 (8 * n)
      let coefficient := bits_to_decode ||| (bits_to_decode1 <<< num_bits_to_decode)
      let F := s.F.set! i coefficient.toNat
      {s with F, num_bytes_read, acc := acc3, num_bits_in_acc := num_bits_in_acc2}
    else
      let F := s.F.set! i bits_to_decode.toNat
      {s with F, acc := acc1, num_bits_in_acc}

def Stream.decode.recBody {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d) (s : DecodeState d n) (i : ℕ) :
  DecodeState d n :=
  List.foldl (fun s i => decode.body b hb s i) s (List.range' i (256 - i))

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
  ∀ j < i, ∀ k < d, s.F[j]!.val.testBit k = b[(d * j + k) / 8]!.testBit ((d * j + k) % 8) ∧
  -- All bits are properly set in the accummulator
  ∀ j < s.num_bits_in_acc, s.acc[j]! = b[(d * i + j) / 8]!.testBit ((d * i + j) % 8) ∧
  ∀ j ∈ [s.num_bits_in_acc:8*n], s.acc[j]! = false

def Stream.decode.body.length_spec {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : DecodeState d n) (i : ℕ) (hi : i < 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega) (hinv : length_inv d n s.num_bytes_read s.num_bits_in_acc i) :
  let s1 := body b hb s i; length_inv d n s1.num_bytes_read s1.num_bits_in_acc (i + 1) := by
  simp only [length_inv, body]
  simp only [length_inv] at hinv
  obtain ⟨hinv0, hinv1, hinv2⟩ := hinv
  constructor
  . omega
  . split
    . next num_bits_in_acc_eq_zero =>
      sorry
    . next num_bits_in_acc_ne_zero =>
      split
      . next num_bits_in_acc_lt_d =>
        simp only [gt_iff_lt, inf_lt_left, not_le] at num_bits_in_acc_lt_d
        simp only [BitVec.setWidth'_eq]
        sorry
      . constructor
        . next hmin =>
          simp only [gt_iff_lt, inf_lt_left, not_le, not_lt] at hmin
          simp only [hinv1, hmin, inf_of_le_left]
          /- Automation note: I'm suprised `scalar_nf; omega` succeeds but none of the following work:
             - `scalar_tac`
             - `simp_scalar`
             - `scalar_eq_nf` -/
          scalar_nf
          omega
        . next hmin =>
          simp only [gt_iff_lt, inf_lt_left, not_le, not_lt] at hmin
          simp only [hmin, inf_of_le_left]
          scalar_nf at hinv2
          scalar_nf
          have : d + d * i + (s.num_bits_in_acc - d) = d * i + s.num_bits_in_acc := by omega
          rw [this, hinv2]
