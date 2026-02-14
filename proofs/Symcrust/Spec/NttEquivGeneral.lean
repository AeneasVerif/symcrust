import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Init.Data.BitVec.Lemmas

/-!
# General NTT–CRT equivalence

This file develops the theory of the Number Theoretic Transform (NTT) as a
Chinese Remainder Theorem (CRT) isomorphism for a general prime `q` and a
primitive `2^d`-th root of unity `ζ` in `ZMod q`, acting on the polynomial
ring `ZMod q [X] / (X^(2^k) + 1)`.

The two parameters `k` and `d` are independent:
- `k` determines the polynomial: `X^(2^k) + 1`.
- `d` determines the root of unity: `ζ` has order `2^d`.

The NTT decomposition tree has `min(k, d - 1)` levels of splitting,
producing `2^min(k, d - 1)` leaf quotient rings, each of degree
`2^(k - min(k, d - 1))`.

Examples:
- ML-KEM (`q = 3329`, `k = d = 8`, `ζ = 17`): 7 splits, 128 quadratic leaves.
- ML-DSA (`q = 8380417`, `k = 8`, `d = 9`, `ζ = 1753`): 8 splits, 256 linear leaves.
- Partial NTT (`k = 10`, `d = 5`): 4 splits, 16 leaves of degree 64.

For the ML-KEM parameters:
  The NTT is a ring isomorphism from `Rq` to the product `Tq` of `128` rings defined by
  quadratic polynomials `X^2 - ζ^k` for some integer `k`. It works through repeated
  decomposition of the involved rings according to the following scheme.

  `Rq = Z[X] ⧸ (X^256 + 1) = Z[X] ⧸ (X^256 - ζ^128)`
  `   ≅ Z[X] ⧸ (X^128 - ζ^64) × Z[X] ⧸ (X^128 + ζ^64) = Z[X] ⧸ (X^128 - ζ^64) × Z[X] ⧸ (X^128 - ζ^192)`
  `   ≅ Z[X] ⧸ (X^64 - ζ^32) × Z[X] ⧸ (X^64 - ζ^160) × Z[X] ⧸ (X^64 - ζ^96) × Z[X] ⧸ (X^64 - ζ^224)`
  `   ≅ ...`

  Continuing this way leads to a scheme of exponents `(x_exp, ζ_exp)` for the
  polynomials `X^x_exp - ζ^ζ_exp` as follows:

  `l=0: (256, 128)`
  `l=1: (128, 64), (128, 192)`
  `l=2: (64, 32), (64, 160), (64, 96), (64, 224)`
  `l=3: (32, 16), (32, 144), (32, 80), (32, 208), ...`
  `l=4: (16, 8), (16, 136), ...`
  `l=5: (8, 4), (8, 132), ...`
  `l=6: (4, 2), (4, 130), ...`
  `l=7: (2, 1), (2, 129), ...`

  The second number, `ζ_exp`, if numbered with `i = 0, ..., i = 2 ^ l - 1` in the order defined
  by the above decomposition is given by `2^(7-l) + (BitRev l i) * 2^(8-l)`.

  This means that the ring for `(l, i)` decomposes as the product of the rings for `(l+1, 2i)`
  and `(l+1, 2i+1)`.
-/

/-- Parameters for the NTT decomposition.
  - `q` is a prime modulus.
  - `k` determines the polynomial ring `ZMod q [X] / (X^(2^k) + 1)`.
  - `d` determines the order of the root of unity (`ζ` has order `2^d`).
  - `ζ` is a primitive `2^d`-th root of unity in `ZMod q`.
  The tree depth is `min(k, d - 1)` levels.
  -/
structure NTTParams where
  /-- The prime modulus. -/
  q : ℕ
  /-- The polynomial degree exponent.  The polynomial ring is
      `ZMod q [X] / (X^(2^k) + 1)`. -/
  k : ℕ
  /-- The root-of-unity order exponent.  `ζ` has multiplicative
      order `2^d` in `ZMod q`. -/
  d : ℕ
  /-- A primitive `2^d`-th root of unity in `ZMod q`. -/
  ζ : ZMod q
  /-- `q` is prime. -/
  q_prime : Nat.Prime q
  /-- The polynomial degree exponent is at least `1`
      (otherwise `X^1 + 1` is linear and there is nothing to decompose). -/
  k_pos : 0 < k
  /-- The root-of-unity order exponent is at least 1
      (needed so that `ζ^(2^(d-1)) = -1`). -/
  d_pos : 0 < d
  /-- `ζ` has multiplicative order exactly `2^d` in `ZMod q`.
      This implies in particular that `q ≡ 1 [MOD 2^d]`
      (since `(ZMod q)ˣ` has order `q − 1`). -/
  ζ_order : orderOf ζ = 2 ^ d

namespace NTTParams

variable (P : NTTParams)

instance : Fact (Nat.Prime P.q) := ⟨P.q_prime⟩

/-- The coefficient ring `ZMod q`. -/
abbrev Zq := ZMod P.q


/-! ## Basic properties derived from the axioms -/

lemma q_pos : 0 < P.q := Nat.Prime.pos P.q_prime  -- unused here but might be useful

lemma q_ne_zero : P.q ≠ 0 := Nat.Prime.ne_zero P.q_prime  -- unused here but might be useful

lemma q_ge_two : 2 ≤ P.q := Nat.Prime.two_le P.q_prime

lemma ζ_ne_zero : P.ζ ≠ 0 := by
  intro h
  have : orderOf P.ζ = 0 := by rw [h, orderOf_zero]
  rw [P.ζ_order] at this
  exact absurd this (by positivity)

lemma ζ_isUnit : IsUnit P.ζ := by  -- unused here but might be useful
  rw [isUnit_iff_ne_zero]
  exact P.ζ_ne_zero

lemma ζ_ne_one : P.ζ ≠ 1 := by  -- unused here but might be useful
  intro h
  have h1 : orderOf P.ζ = 1 := by rw [h, orderOf_one]
  rw [P.ζ_order] at h1
  -- h1 : 2 ^ P.d = 1, but P.d ≥ 1 so 2 ^ P.d ≥ 2
  have h2 : 1 < 2 ^ P.d := Nat.one_lt_pow P.d_pos.ne' (by norm_num)
  omega

/-- `ζ ^ (2^d) = 1`: the defining property of a `2^d`-th root of unity. -/
theorem ζ_pow_two_pow_d : P.ζ ^ (2 ^ P.d) = 1 :=
  pow_orderOf_eq_one P.ζ |>.symm ▸ by rw [P.ζ_order]

/-- `ζ ^ (2^k) = 1` when `d ≤ k`. -/
theorem ζ_pow_two_pow_k (hdk : P.d ≤ P.k) : P.ζ ^ (2 ^ P.k) = 1 := by  -- unused here but might be useful
  have h : 2 ^ P.d ∣ 2 ^ P.k := Nat.pow_dvd_pow 2 hdk
  obtain ⟨m, hm⟩ := h
  rw [hm, pow_mul, P.ζ_pow_two_pow_d, one_pow]

/-- `ζ ^ m ≠ 1` for `0 < m < 2^d`: primitivity. -/
theorem ζ_pow_ne_one (m : ℕ) (hm_pos : 0 < m) (hm_lt : m < 2 ^ P.d) :
    P.ζ ^ m ≠ 1 := by
  intro h
  have h_dvd : orderOf P.ζ ∣ m := orderOf_dvd_of_pow_eq_one h
  rw [P.ζ_order] at h_dvd
  exact Nat.not_lt.mpr (Nat.le_of_dvd hm_pos h_dvd) hm_lt

/-- `ζ ^ (2^(d-1)) = -1`.
    Proof sketch: `(ζ^(2^(d-1)))² = ζ^(2^d) = 1`, so `ζ^(2^(d-1))` is a square root
    of unity in the field `ZMod q`.  Since `q` is an odd prime, the only square roots of
    1 are `±1`.  By primitivity `ζ^(2^(d-1)) ≠ 1`, so it must be `-1`. -/
theorem ζ_pow_two_pow_pred_d : P.ζ ^ (2 ^ (P.d - 1)) = -1 := by
  have hk := P.d_pos
  -- ζ^(2^(d-1)) squares to 1
  have hsq : (P.ζ ^ (2 ^ (P.d - 1))) ^ 2 = 1 := by
    rw [← pow_mul]
    have : 2 ^ (P.d - 1) * 2 = 2 ^ P.d := by
      have : P.d - 1 + 1 = P.d := Nat.succ_pred_eq_of_pos hk
      calc 2 ^ (P.d - 1) * 2 = 2 ^ (P.d - 1 + 1) := by ring
        _ = 2 ^ P.d := by rw [this]
    rw [this]
    exact P.ζ_pow_two_pow_d
  -- So it is ±1: in `ZMod q` (a field), x² = 1 means (x-1)(x+1) = 0
  set x := P.ζ ^ (2 ^ (P.d - 1)) with hx_def
  have h_or : x = 1 ∨ x = -1 := by
    have hfact : (x - 1) * (x + 1) = 0 := by
      have : x ^ 2 - 1 = 0 := sub_eq_zero.mpr hsq
      calc (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
        _ = 0 := this
    rcases mul_eq_zero.mp hfact with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact eq_neg_of_add_eq_zero_left h
  -- But x ≠ 1 by primitivity
  cases h_or with
  | inl h1 => exact absurd h1 (P.ζ_pow_ne_one _ (by positivity) (by
      exact Nat.pow_lt_pow_right (by omega) (by omega)))
  | inr h => exact h

/-- Powers of `ζ` with distinct exponents mod `2^d` are distinct. -/
lemma ζ_pow_injective (m n : ℕ) (hm : m < 2 ^ P.d) (hn : n < 2 ^ P.d)
    (h : P.ζ ^ m = P.ζ ^ n) : m = n :=
  pow_injOn_Iio_orderOf
    (P.ζ_order ▸ hm)
    (P.ζ_order ▸ hn)
    h

/-- `ζ^m - ζ^n` is nonzero when `m` and `n` are distinct mod `2^d`. -/
lemma ζ_pow_sub_ne_zero (m n : ℕ) (h : m % (2 ^ P.d) ≠ n % (2 ^ P.d)) :
    P.ζ ^ m - P.ζ ^ n ≠ 0 := by
  intro heq
  have : P.ζ ^ m = P.ζ ^ n := sub_eq_zero.mp heq
  rw [← pow_mod_orderOf P.ζ m, ← pow_mod_orderOf P.ζ n, P.ζ_order] at this
  exact h (P.ζ_pow_injective _ _
    (Nat.mod_lt m (by positivity))
    (Nat.mod_lt n (by positivity))
    this)

/-- `ζ^m - ζ^n` is a unit when `m` and `n` are distinct mod `2^d`. -/
theorem ζ_pow_sub_isUnit (m n : ℕ) (h : m % (2 ^ P.d) ≠ n % (2 ^ P.d)) :
    IsUnit (P.ζ ^ m - P.ζ ^ n) := by
  have hne := P.ζ_pow_sub_ne_zero m n h
  have : (P.ζ ^ m - P.ζ ^ n) ^ (P.q - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hne
  exact IsUnit.of_pow_eq_one this (show P.q - 1 ≠ 0 by have := P.q_ge_two; omega)

end NTTParams


/-! ## BitRev: bit reversal function

  `BitRev b i` reverses the `b`-bit representation of `i`.
  This is used to index the twiddle factors in the NTT decomposition tree. -/

/-- Reverse the `b`-bit representation of `i ∈ Fin (2^b)`. -/
def BitRev (b : ℕ) (i : Fin (2 ^ b)) : Fin (2 ^ b) :=
  let ibits := BitVec.ofNat b i.val
  (ibits.reverse).toFin

/- BitRev is its own inverse. -/
lemma BitRev_inv (b : ℕ) (i : Fin (2 ^ b)) : BitRev b (BitRev b i) = i := by
  simp [BitRev]

/- BitRev is injective. -/
lemma BitRev_inj (b : ℕ) (i j : Fin (2 ^ b)) (hij : i ≠ j) : BitRev b i ≠ BitRev b j :=
  fun h => hij (by rw [← BitRev_inv b i, ← BitRev_inv b j, h])


/-! ### BitVec helper lemmas for BitRev -/

/-- For integers 2i and 2i+1, their BitVec representations are the same except for bit 0. -/
lemma BitVec_ofNat_double_vs_double_plus_one
    (b : ℕ) (i : ℕ)
    (j : Nat) (hj : 0 ≠ j) :
  (BitVec.ofNat b (2 * i)).getLsbD j = (BitVec.ofNat b (2 * i + 1)).getLsbD j := by
  simp only [BitVec.getLsbD, BitVec.ofNat]
  show (⟨(2 * i) % 2 ^ b, by omega⟩ : Fin (2 ^ b)).val.testBit j =
        (⟨(2 * i + 1) % 2 ^ b, by omega⟩ : Fin (2 ^ b)).val.testBit j
  cases j with | zero => omega | succ j' => grind

/-- For the same numbers, if their BitVec representations are reversed, they are the same
    except for the most significant bit. -/
lemma BitVec_ofNat_double_vs_double_plus_one_reverse
    (b : ℕ) (i : ℕ)
    (j : Nat) (hjb : j < (b-1)) :
  (BitVec.ofNat b (2 * i)).reverse.getLsbD j = (BitVec.ofNat b (2 * i + 1)).reverse.getLsbD j := by
  simp only [BitVec.getLsbD_reverse, BitVec.getMsbD]
  simp (config := {decide := true}) only [show j < b by omega]
  apply BitVec_ofNat_double_vs_double_plus_one; omega

/-- The least significant bit of an even number is zero. -/
lemma BitVec_ofNat_double_lsb (b : ℕ) (i : ℕ)  :
  (BitVec.ofNat b (2 * i)).getLsbD 0 = false := by
  rw [BitVec.getLsbD_ofNat]
  simp

/-- The most significant bit of the bit reverse of an even number is zero. -/
lemma BitVec_ofNat_double_reverse_msb (b : ℕ) (i : ℕ) (hb : b > 0) :
  (BitVec.ofNat b (2 * i)).reverse.getLsbD (b-1) = false := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
  simp only [show b - 1 < b by omega, show b - 1 - (b - 1) = 0 by omega]
  exact BitVec_ofNat_double_lsb _ _

/-- The least significant bit of an odd number is one. -/
lemma BitVec_ofNat_double_plus_one_lsb (b : ℕ) (i : ℕ) (hb : b > 0) :
  (BitVec.ofNat b (2 * i + 1)).getLsbD 0 = true := by
  simp [BitVec.getLsbD_ofNat]; exact hb

/-- The most significant bit of the bit reverse of an odd number is one. -/
lemma BitVec_ofNat_double_plus_one_reverse_msb (b : ℕ) (i : ℕ) (hb : b > 0) :
  (BitVec.ofNat b (2 * i + 1)).reverse.getLsbD (b-1) = true := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
  simp [hb]
  exact BitVec_ofNat_double_plus_one_lsb _ _ hb


/-! ### Key structural lemmas for BitRev -/

/-- Bit reversal of an odd number (2i+1) equals bit reversal of the even number (2i)
    plus 2^(b-1), where b is the number of bits. -/
lemma BitRev_odd_from_even (b : ℕ) (hb : b > 0) (i : Fin (2 ^ (b - 1))) :
  let i₁ : Fin (2 ^ b) := ⟨2 * i.val, by rw [← mul_pow_sub_one (Nat.pos_iff_ne_zero.mp hb)]; omega⟩
  let i₂ : Fin (2 ^ b) := ⟨2 * i.val + 1, by rw [← mul_pow_sub_one (Nat.pos_iff_ne_zero.mp hb)]; omega⟩
  (BitRev b i₂).val = (BitRev b i₁).val + 2^(b - 1) := by
  intro i₁ i₂
  simp only [i₁, i₂, BitRev]
  show (BitVec.ofNat b (2 * i.val + 1)).reverse.toNat =
        (BitVec.ofNat b (2 * i.val)).reverse.toNat + 2^(b - 1)

  have h_pow_lt : 2 ^ (b - 1) < 2 ^ b := Nat.pow_lt_pow_right (by omega) (by omega)

  -- Prove BitVec equality, then take toNat of both sides
  suffices h : (BitVec.ofNat b (2 * i.val + 1)).reverse =
                (BitVec.ofNat b (2 * i.val)).reverse + (BitVec.twoPow b (b - 1)) by
    have : (BitVec.ofNat b (2 * i.val + 1)).reverse.toNat =
            ((BitVec.ofNat b (2 * i.val)).reverse + (BitVec.twoPow b (b - 1))).toNat := by rw [h]
    rw [this, BitVec.toNat_add, BitVec.toNat_twoPow]
    have : (BitVec.ofNat b (2 * i.val)).reverse.toNat < 2 ^ (b - 1) := by
      apply BitVec.toNat_lt_of_msb_false
      rw [BitVec.msb_eq_getLsbD_last]
      exact BitVec_ofNat_double_reverse_msb b i.val hb
    have h_no_overflow : (BitVec.ofNat b (2 * i.val)).reverse.toNat + 2 ^ (b - 1) < 2 ^ b := by
      rw [← mul_pow_sub_one (Nat.pos_iff_ne_zero.mp hb)]; omega
    rw [Nat.mod_eq_of_lt h_pow_lt, Nat.mod_eq_of_lt h_no_overflow]

  -- Prove the BitVec equality bit-by-bit
  apply BitVec.eq_of_getLsbD_eq
  intro j hj

  by_cases hjb : j = b - 1
  · subst hjb
    rw [BitVec_ofNat_double_plus_one_reverse_msb b i.val hb]
    rw [BitVec.getLsbD_add]
    · rw [BitVec_ofNat_double_reverse_msb b i.val hb]
      rw [BitVec.getLsbD_twoPow]
      simp [hb]
      simp [BitVec.carry]
      rw [Nat.mod_eq_of_lt h_pow_lt, Nat.mod_self]
      exact Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < 2))
    · omega
  · have hjb_lt : j < b - 1 := by omega
    rw [BitVec.getLsbD_add]
    · have h_twoPow_zero : (BitVec.twoPow b (b - 1)).getLsbD j = false := by
        rw [BitVec.getLsbD_twoPow]
        grind
      have h_carry_zero : BitVec.carry j (BitVec.ofNat b (2 * i.val)).reverse (BitVec.twoPow b (b - 1)) false = false := by
        simp [BitVec.carry]
        rw [Nat.mod_eq_of_lt h_pow_lt]
        rw [Nat.dvd_iff_mod_eq_zero.mp (by apply Nat.pow_dvd_pow; omega : 2 ^ j ∣ 2 ^ (b - 1))]
        exact Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < 2))
      simp only [h_twoPow_zero, h_carry_zero, Bool.xor_false]
      exact (BitVec_ofNat_double_vs_double_plus_one_reverse b i.val j hjb_lt).symm
    · omega

/-- Bit reversal (of width b) of an even b-bit number (2*i) is the same as bit
    reversal (of width b-1) of half the number (i). -/
lemma BitRev_even_from_half (b : ℕ) (hb : b > 0) (i : Fin (2 ^ (b - 1))) :
  let i₁ : Fin (2 ^ b) := ⟨2 * i.val, by rw [← mul_pow_sub_one (Nat.pos_iff_ne_zero.mp hb)]; omega⟩
  (BitRev b i₁).val = (BitRev (b-1) i).val := by
  intro i₁
  simp only [i₁, BitRev]
  show (BitVec.ofNat b (2 * i.val)).reverse.toNat = (BitVec.ofNat (b-1) i.val).reverse.toNat

  have h_bound : (BitVec.ofNat b (2 * i.val)).reverse.toNat < 2 ^ (b - 1) := by
    apply BitVec.toNat_lt_of_msb_false
    rw [BitVec.msb_eq_getLsbD_last]
    exact BitVec_ofNat_double_reverse_msb b i.val hb

  have h_preserve : (BitVec.ofNat b (2 * i.val)).reverse.toNat =
       (BitVec.ofNat (b-1) ((BitVec.ofNat b (2 * i.val)).reverse.toNat)).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_bound]

  have h_i : (BitVec.ofNat (b-1) ((BitVec.ofNat b (2 * i.val)).reverse.toNat)).toNat
    = (BitVec.ofNat (b-1) i.val).reverse.toNat := by
    suffices h : (BitVec.ofNat (b-1) ((BitVec.ofNat b (2 * i.val)).reverse.toNat)) =
                 (BitVec.ofNat (b-1) i.val).reverse by rw [h]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h_div : 2 * i.val / 2 = i.val := Nat.mul_div_cancel_left i.val (by omega : 0 < 2)
    rw [BitVec.getLsbD_ofNat, BitVec.getLsbD_reverse, BitVec.getMsbD]
    rw [← BitVec.getLsbD, BitVec.getLsbD_reverse, BitVec.getMsbD, BitVec.getLsbD_ofNat]
    simp [Nat.lt_of_lt_pred hj]
    grind
  grind


/-! ## Polynomial ring and NTT tree structure

  The NTT decomposes `Zq[X] / (X^(2^k) + 1)` into a product of quotient
  rings via repeated binary splitting.  Each node in the binary tree is
  indexed by a *level* `l` (root = 0) and a position `i ∈ Fin (2^l)`.

  At node `(l, i)` the quotient ring is `Zq[X] / (fq l i)` where
    `fq l i = X^(x_exp l) − ζ^(ζ_exp l i)`.

  The exponents are:
    `x_exp l   = 2^(k - l)`        (degree of the X-monomial)
    `ζ_exp l i = 2^(d-1-l) + BitRev(l,i) · 2^(d-l)`  (power of ζ)

  The tree has valid nodes at levels `l = 0, …, d-1`
  (so levels are `Fin d`), and splitting happens at `l < d-1`.
-/

open Polynomial

namespace NTTParams

variable (P : NTTParams)

/-- Shorthand for the polynomial ring over `Zq`. -/
abbrev Poly := (ZMod P.q)[X]

/-- `X^n` as a polynomial over `Zq`. -/
noncomputable def xn (n : Nat) : P.Poly := monomial n 1

/-- `ζ` as a constant polynomial. -/
noncomputable def ζ_poly : P.Poly := C P.ζ

/-- The X-exponent at level `l`: degree of the modulus polynomial.
    `x_exp l = 2^(k - l)`.
    Requires `l ≤ k` for the subtraction to be meaningful. -/
def x_exp (l : Fin P.d) (_hl : l.val ≤ P.k) : ℕ := 2 ^ (P.k - l.val)

/-- The ζ-exponent at level `l` and position `i`:
    `ζ_exp l i = 2^(d-1-l) + BitRev(l,i) · 2^(d-l)`.
    This is the power of `ζ` that appears in the modulus polynomial `fq l i`. -/
def ζ_exp (l : Fin P.d) (i : Fin (2 ^ l.val)) : ℕ :=
  2 ^ (P.d - 1 - l.val) + (BitRev l i).val * 2 ^ (P.d - l.val)

/-- The ζ-exponent is bounded by `2^d`. -/
lemma ζ_exp_ubound (l : Fin P.d) (i : Fin (2 ^ l.val)) :
    P.ζ_exp l i < 2 ^ P.d := by
  unfold ζ_exp
  have hl : l.val < P.d := l.isLt
  have hi_bound : (BitRev l.val i).val < 2 ^ l.val := (BitRev l.val i).isLt
  -- Key identity: 2^d = 2^l · 2^(d-l) and 2^(d-l) = 2 · 2^(d-1-l)
  have h_total : 2 ^ P.d = 2 ^ l.val * 2 ^ (P.d - l.val) := by
    rw [← pow_add]; congr 1; omega
  calc 2 ^ (P.d - 1 - l.val) + (BitRev l.val i).val * 2 ^ (P.d - l.val)
    _ < 2 ^ (P.d - l.val) + (BitRev l.val i).val * 2 ^ (P.d - l.val) := by
        apply Nat.add_lt_add_right
        exact Nat.pow_lt_pow_right (by omega) (by omega)
    _ = ((BitRev l.val i).val + 1) * 2 ^ (P.d - l.val) := by ring
    _ ≤ 2 ^ l.val * 2 ^ (P.d - l.val) := by
        apply Nat.mul_le_mul_right; omega
    _ = 2 ^ P.d := h_total.symm

/-- Distinct positions give distinct ζ-exponents. -/
lemma ζ_exp_ne (l : Fin P.d) (i j : Fin (2 ^ l.val)) (hij : i ≠ j) :
    P.ζ_exp l i ≠ P.ζ_exp l j := by
  intro h
  simp only [ζ_exp] at h
  have h_eq : (BitRev l.val i).val = (BitRev l.val j).val := by
    have hpos : 0 < 2 ^ (P.d - l.val) := by positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (by omega)
  exact BitRev_inj l.val i j hij (Fin.ext h_eq)

/-- Distinct positions give distinct ζ-exponents mod `2^d`. -/
lemma ζ_exp_ne_mod (l : Fin P.d) (i j : Fin (2 ^ l.val)) (hij : i ≠ j) :
    P.ζ_exp l i % (2 ^ P.d) ≠ P.ζ_exp l j % (2 ^ P.d) := by
  have hi := P.ζ_exp_ubound l i
  have hj := P.ζ_exp_ubound l j
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  exact P.ζ_exp_ne l i j hij

/-- The difference `ζ^(ζ_exp l i) - ζ^(ζ_exp l j)` is a unit when `i ≠ j`. -/
lemma ζ_exp_diff_isUnit (l : Fin P.d) (i j : Fin (2 ^ l.val)) (hij : i ≠ j) :
    IsUnit (P.ζ ^ (P.ζ_exp l i) - P.ζ ^ (P.ζ_exp l j)) :=
  P.ζ_pow_sub_isUnit _ _ (P.ζ_exp_ne_mod l i j hij)

/-- The polynomial defining the quotient ring at node `(l, i)` in the NTT tree:
    `fq l i = X^(2^(k-l)) − ζ^(ζ_exp l i)`. -/
noncomputable
def fq (l : Fin P.d) (i : Fin (2 ^ l.val)) (hl : l.val ≤ P.k) : P.Poly :=
  P.xn (P.x_exp l hl) - P.ζ_poly ^ (P.ζ_exp l i)

/-- The ideal generated by `fq l i`. -/
noncomputable
abbrev Iq (l : Fin P.d) (i : Fin (2 ^ l.val)) (hl : l.val ≤ P.k) :=
  Ideal.span {P.fq l i hl}

/-- The quotient ring at node `(l, i)`. -/
abbrev Sq (l : Fin P.d) (i : Fin (2 ^ l.val)) (hl : l.val ≤ P.k) :=
  (ZMod P.q)[X] ⧸ P.Iq l i hl

/-- Two polynomials `fq l i` and `fq l j` at the same level are coprime when `i ≠ j`.
    Proof: the Bézout coefficients are `−C d⁻¹` and `C d⁻¹` where
    `d = ζ^(ζ_exp l i) − ζ^(ζ_exp l j)`, which is a unit. -/
theorem fq_coprime (l : Fin P.d) (i j : Fin (2 ^ l.val)) (hij : i ≠ j)
    (hl : l.val ≤ P.k) :
    IsCoprime (P.fq l i hl) (P.fq l j hl) := by
  let d := P.ζ ^ P.ζ_exp l i - P.ζ ^ P.ζ_exp l j
  have hd : IsUnit d := P.ζ_exp_diff_isUnit l i j hij
  simp only [fq, IsCoprime]
  use -C d⁻¹, C d⁻¹
  simp only [xn, ζ_poly, x_exp]
  ring_nf
  rw [← C_pow, ← C_pow, ← C_mul, ← C_mul, ← C_sub,
      show d⁻¹ * P.ζ ^ P.ζ_exp l i - d⁻¹ * P.ζ ^ P.ζ_exp l j = d⁻¹ * d by ring,
      ZMod.inv_mul_of_unit d hd, C_1]

/-- The ideals `Iq l i` and `Iq l j` are coprime when `i ≠ j`. -/
lemma Iq_coprime (l : Fin P.d) (i j : Fin (2 ^ l.val)) (hij : i ≠ j)
    (hl : l.val ≤ P.k) :
    IsCoprime (P.Iq l i hl) (P.Iq l j hl) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (P.fq_coprime l i j hij hl)

/-- The butterfly factorization: a parent polynomial factors as the product
    of its two children in the NTT tree.
    `fq(l+1, 2i) · fq(l+1, 2i+1) = fq(l, i)`.
    Algebraically: `(X^n − ζ^a)(X^n + ζ^a) = X^{2n} − ζ^{2a}`. -/
lemma fq_prod (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k) :
    P.fq ⟨l.val + 1, by omega⟩
      ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by omega) *
    P.fq ⟨l.val + 1, by omega⟩
      ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by omega) =
    P.fq l i (by omega) := by
  -- BitRev identities
  have h_odd := BitRev_odd_from_even (l.val + 1) (by omega) i
  simp at h_odd
  have h_even := BitRev_even_from_half (l.val + 1) (by omega) i
  simp at h_even
  -- ζ_poly^(2^(d-1)) = -1 at the polynomial level
  have h_ζp : P.ζ_poly ^ (2 ^ (P.d - 1)) = -1 := by
    simp only [ζ_poly, ← C_pow, P.ζ_pow_two_pow_pred_d, map_neg, map_one]
  -- Key arithmetic: 2^l · 2^(d-(l+1)) = 2^(d-1)
  have h_merge : 2 ^ l.val * 2 ^ (P.d - (l.val + 1)) = 2 ^ (P.d - 1) := by
    rw [← pow_add]; congr 1; omega
  -- ζ-exponent of odd child = ζ-exponent of even child + 2^(d-1)
  have h_ζ_split : P.ζ_exp ⟨l.val + 1, by omega⟩
      ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ =
      P.ζ_exp ⟨l.val + 1, by omega⟩
      ⟨2 * i.val, by simp [pow_succ]; omega⟩ + 2 ^ (P.d - 1) := by
    simp only [ζ_exp, h_odd, add_mul]
    linarith [h_merge]
  -- Unfold fq (keeping xn, ζ_poly, x_exp, ζ_exp abstract)
  simp only [fq]
  -- Rewrite odd child's ζ power as negation of even child's:
  -- ζ_poly^(e + 2^(d-1)) = ζ_poly^e · ζ_poly^(2^(d-1)) = ζ_poly^e · (-1) = -ζ_poly^e
  simp only [h_ζ_split, pow_add, h_ζp, mul_neg_one, sub_neg_eq_add]
  -- Now: (xn n - a)(xn n + a) = xn m - a'
  -- Apply difference of squares: (x - y)(x + y) = x·x - y·y
  have h_ds : ∀ (x y : P.Poly), (x - y) * (x + y) = x * x - y * y := fun x y => by ring
  rw [h_ds]
  -- Simplify monomial product and ζ power product
  simp only [xn, monomial_mul_monomial, one_mul, ← pow_add, x_exp, ζ_exp, h_even]
  -- Now: monomial (A+A) 1 - ζ_poly^(B+B) = monomial C 1 - ζ_poly^D
  -- where A = 2^(k-(l+1)), B = even_ζ_exp (with BitRev l i), C = 2^(k-l), D = parent ζ_exp
  -- Prove the x-exponent identity: A + A = C
  have hx : 2 ^ (P.k - (l.val + 1)) + 2 ^ (P.k - (l.val + 1)) = 2 ^ (P.k - l.val) := by
    rw [← two_mul, mul_comm, ← pow_succ]; congr 1; omega
  -- Prove the ζ-exponent identity: B + B = D
  have h1 : 2 * 2 ^ (P.d - 1 - (l.val + 1)) = 2 ^ (P.d - 1 - l.val) := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  have h2 : 2 * 2 ^ (P.d - (l.val + 1)) = 2 ^ (P.d - l.val) := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  have hζ : (2 ^ (P.d - 1 - (l.val + 1)) +
      (BitRev l.val i).val * 2 ^ (P.d - (l.val + 1))) +
    (2 ^ (P.d - 1 - (l.val + 1)) +
      (BitRev l.val i).val * 2 ^ (P.d - (l.val + 1))) =
    2 ^ (P.d - 1 - l.val) + (BitRev l.val i).val * 2 ^ (P.d - l.val) := by
    calc _ = 2 * 2 ^ (P.d - 1 - (l.val + 1)) +
          (BitRev l.val i).val * (2 * 2 ^ (P.d - (l.val + 1))) := by ring
      _ = 2 ^ (P.d - 1 - l.val) +
          (BitRev l.val i).val * 2 ^ (P.d - l.val) := by rw [h1, h2]
  rw [hx, hζ]

/-- Iterated butterfly factorization: a polynomial at level `l` factors as the
    product of `2^m` polynomials at level `l + m`.
    `fq(l, i) = ∏ j : Fin(2^m), fq(l+m, 2^m·i + j)`. -/
lemma fq_prod_iter (l : Fin P.d) (i : Fin (2 ^ l.val)) (m : ℕ)
    (hm_d : l.val + m < P.d) (hm_k : l.val + m ≤ P.k) :
    let idx : Fin (2 ^ m) → Fin (2 ^ (l.val + m)) := fun j => ⟨2 ^ m * i.val + j.val, by
      calc 2 ^ m * i.val + j.val
          < 2 ^ m * i.val + 2 ^ m := Nat.add_lt_add_left j.isLt _
        _ = 2 ^ m * (i.val + 1) := by ring
        _ ≤ 2 ^ m * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
        _ = 2 ^ (l.val + m) := by rw [← Nat.pow_add, Nat.add_comm]⟩
    ∏ j : Fin (2 ^ m), P.fq ⟨l.val + m, by omega⟩ (idx j) (by omega) =
    P.fq l i (by omega) := by
  intro idx
  induction m generalizing l i with
  | zero =>
    simp only [Nat.pow_zero, Fintype.prod_subsingleton _ (0 : Fin 1)]
    simp [idx]
  | succ m' ih =>
    simp only [Nat.pow_succ] at idx

    -- Define intermediate level l' = l + m'
    let l' : Fin P.d := ⟨l.val + m', by omega⟩

    -- Define intermediate index function at level l'
    let idx' : Fin (2 ^ m') → Fin (2 ^ l'.val) := fun j => ⟨2 ^ m' * i.val + j.val, by
      simp only [l']
      calc 2 ^ m' * i.val + j.val
          < 2 ^ m' * i.val + 2 ^ m' := Nat.add_lt_add_left j.isLt _
        _ = 2 ^ m' * (i.val + 1) := by ring
        _ ≤ 2 ^ m' * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
        _ = 2 ^ (l.val + m') := by rw [← Nat.pow_add, Nat.add_comm]⟩

    -- Rewrite ∏ Fin (2^m' * 2) as ∏ Fin (2^m') of pairs
    have h_prod_eq : ∏ j : Fin (2 ^ m' * 2),
        P.fq ⟨l.val + (m' + 1), by omega⟩ (idx j) (by omega) =
      ∏ j : Fin (2 ^ m'),
        (P.fq ⟨l.val + (m' + 1), by omega⟩ (idx ⟨2*j.val, by omega⟩) (by omega) *
         P.fq ⟨l.val + (m' + 1), by omega⟩ (idx ⟨2*j.val+1, by omega⟩) (by omega)) := by
      let pair : Fin (2 ^ m') × Fin 2 → Fin (2 ^ m' * 2) :=
        fun ⟨a, b⟩ => ⟨2 * a.val + b.val, by have ha := a.isLt; have hb := b.isLt; omega⟩
      have hpair_bij : Function.Bijective pair := by
        constructor
        · intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h; grind
        · intro j
          use (⟨j.val / 2, by have := j.isLt; omega⟩, ⟨j.val % 2, Nat.mod_lt _ (by omega)⟩)
          apply Fin.ext; grind
      have hrhs : ∏ j : Fin (2 ^ m'),
          (P.fq ⟨l.val + (m' + 1), by omega⟩ (idx ⟨2*j.val, by omega⟩) (by omega) *
           P.fq ⟨l.val + (m' + 1), by omega⟩ (idx ⟨2*j.val+1, by omega⟩) (by omega)) =
        ∏ p : Fin (2 ^ m') × Fin 2,
          P.fq ⟨l.val + (m' + 1), by omega⟩ (idx (pair p)) (by omega) := by
        trans ∏ a : Fin (2 ^ m'), ∏ b : Fin 2,
          P.fq ⟨l.val + (m' + 1), by omega⟩ (idx (pair (a, b))) (by omega)
        · congr 1; ext a; rw [Fin.prod_univ_two]; rfl
        · rw [← Finset.prod_product']; rfl
      rw [hrhs]
      exact (Fintype.prod_bijective pair hpair_bij _ _ (fun _ => rfl)).symm

    -- Each pair equals fq l' (idx' j) by fq_prod
    have h_pairs : ∀ j : Fin (2 ^ m'),
        P.fq ⟨l.val + (m' + 1), by omega⟩ (idx ⟨2*j.val, by omega⟩) (by omega) *
        P.fq ⟨l.val + (m' + 1), by omega⟩ (idx ⟨2*j.val+1, by omega⟩) (by omega) =
        P.fq l' (idx' j) (by simp only [l']; omega) := by
      intro j
      have hl'_d : l'.val + 1 < P.d := by simp only [l']; omega
      have hl'_k : l'.val + 1 ≤ P.k := by simp only [l']; omega
      have hmul := P.fq_prod l' (idx' j) hl'_d hl'_k
      convert hmul using 3 <;> ext <;> simp only [idx, idx', Nat.pow_succ] <;> ring

    -- Apply induction hypothesis
    have h_ih := ih l i (by omega : l.val + m' < P.d) (by omega : l.val + m' ≤ P.k)

    -- Final assembly
    grind

/-- A descendant polynomial divides its ancestor:
    `fq(l+m, 2^m·i + j) ∣ fq(l, i)`. -/
lemma fq_dvd_ancestor (l : Fin P.d) (i : Fin (2 ^ l.val)) (m : ℕ)
    (hm_d : l.val + m < P.d) (hm_k : l.val + m ≤ P.k)
    (j : Fin (2 ^ m)) :
    P.fq ⟨l.val + m, by omega⟩ ⟨2 ^ m * i.val + j.val, by
      calc 2 ^ m * i.val + j.val
        < 2 ^ m * i.val + 2 ^ m := Nat.add_lt_add_left j.isLt _
        _ = 2 ^ m * (i.val + 1) := by ring
        _ ≤ 2 ^ m * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
        _ = 2 ^ (l.val + m) := by rw [← Nat.pow_add]; ring_nf⟩ (by omega) ∣
    P.fq l i (by omega) := by
  have h := P.fq_prod_iter l i m hm_d hm_k
  simp at h
  rw [← h]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

/-- The ancestor ideal is contained in every descendant ideal:
    `Iq(l, i) ≤ Iq(l+m, 2^m·i + j)`. -/
lemma Iq_le_descendant (l : Fin P.d) (i : Fin (2 ^ l.val)) (m : ℕ)
    (hm_d : l.val + m < P.d) (hm_k : l.val + m ≤ P.k)
    (j : Fin (2 ^ m)) :
    P.Iq l i (by omega) ≤ P.Iq ⟨l.val + m, by omega⟩ ⟨2 ^ m * i.val + j.val, by
      calc 2 ^ m * i.val + j.val
        < 2 ^ m * i.val + 2 ^ m := Nat.add_lt_add_left j.isLt _
        _ = 2 ^ m * (i.val + 1) := by ring
        _ ≤ 2 ^ m * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
        _ = 2 ^ (l.val + m) := by rw [← Nat.pow_add]; ring_nf⟩ (by omega) :=
  Ideal.span_singleton_le_span_singleton.mpr (P.fq_dvd_ancestor l i m hm_d hm_k j)


/-! ### CRT isomorphism -/

/-- The quotient ring at level `l` is isomorphic to a product of two child quotient rings
    at level `l+1`. This is the one-step CRT decomposition. -/
noncomputable
def crtIq (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k) :
    P.Sq l i (by omega) ≃+*
      (P.Sq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by omega)) ×
      (P.Sq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by omega)) := by
  let I₁ := P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by omega)
  let I₂ := P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by omega)
  have coprime : IsCoprime
      (P.fq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by omega))
      (P.fq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by omega)) :=
    P.fq_coprime _ _ _ (by simp) _
  have prod : I₁ * I₂ = P.Iq l i (by omega) := by
    simp only [I₁, I₂, Iq, Ideal.span_singleton_mul_span_singleton,
               P.fq_prod l i hl_d hl_k]
  exact (Ideal.quotEquivOfEq prod).symm.trans <|
    Ideal.quotientMulEquivQuotientProd I₁ I₂
      ((Ideal.isCoprime_span_singleton_iff _ _).mpr coprime)

lemma crtIq_fst (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k) (f : P.Poly) :
    (P.crtIq l i hl_d hl_k (Ideal.Quotient.mk (P.Iq l i (by omega)) f)).1 =
      Ideal.Quotient.mk
        (P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by omega)) f := by
  simp [crtIq, RingEquiv.trans_apply, Ideal.quotientMulEquivQuotientProd_fst]

lemma crtIq_snd (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k) (f : P.Poly) :
    (P.crtIq l i hl_d hl_k (Ideal.Quotient.mk (P.Iq l i (by omega)) f)).2 =
      Ideal.Quotient.mk
        (P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by omega)) f := by
  simp [crtIq, RingEquiv.trans_apply, Ideal.quotientMulEquivQuotientProd_snd]


/-! ### Iterated m-fold CRT isomorphism -/

/-- The quotient ring at level `l` and index `i` is isomorphic to a product of `2^m`
    quotient rings at level `l+m`. This is the m-fold generalization of `crtIq`. -/
noncomputable
def crtIq_iter (l : Fin P.d) (i : Fin (2 ^ l.val)) (m : ℕ)
    (hm_d : l.val + m < P.d) (hm_k : l.val + m ≤ P.k) :
    let idx : Fin (2 ^ m) → Fin (2 ^ (l.val + m)) := fun j => ⟨2 ^ m * i.val + j.val, by
      calc 2 ^ m * i.val + j.val
          < 2 ^ m * i.val + 2 ^ m := Nat.add_lt_add_left j.isLt _
        _ = 2 ^ m * (i.val + 1) := by ring
        _ ≤ 2 ^ m * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
        _ = 2 ^ (l.val + m) := by rw [← Nat.pow_add]; ring_nf⟩
    P.Sq l i (by omega) ≃+* Π j : Fin (2 ^ m),
      P.Sq ⟨l.val + m, by omega⟩ (idx j) (by omega) := by
  intro idx
  let I : Fin (2 ^ m) → Ideal P.Poly := fun j =>
    P.Iq ⟨l.val + m, by omega⟩ (idx j) (by omega)
  have coprime : Pairwise (fun j₁ j₂ => IsCoprime (I j₁) (I j₂)) := by
    intro j₁ j₂ hjk
    simp only [I]
    apply P.Iq_coprime
    simp only [idx, Ne, Fin.mk.injEq]
    omega
  have inf_eq : iInf I = P.Iq l i (by omega) := by
    simp only [I, Iq]
    rw [Ideal.iInf_span_singleton]
    · have prod_eq : ∏ j : Fin (2 ^ m),
          P.fq ⟨l.val + m, by omega⟩ (idx j) (by omega) = P.fq l i (by omega) :=
        P.fq_prod_iter l i m hm_d hm_k
      rw [prod_eq]
    · intro j₁ j₂ hjk
      have h : IsCoprime (I j₁) (I j₂) := coprime hjk
      simp only [I, Iq] at h
      rwa [Ideal.isCoprime_span_singleton_iff] at h
  let e1 : P.Poly ⧸ P.Iq l i (by omega) ≃+* P.Poly ⧸ iInf I :=
    Ideal.quotientEquiv (P.Iq l i (by omega)) (iInf I) (RingEquiv.refl _) (by simp [inf_eq])
  let e2 : P.Poly ⧸ iInf I ≃+* (Π j : Fin (2 ^ m), P.Poly ⧸ I j) :=
    Ideal.quotientInfRingEquivPiQuotient I coprime
  exact e1.trans e2

/-- Two ideals `Iq` are equal if their level and index `Fin` values are equal. -/
lemma Iq_fin_cast (l l' : Fin P.d) (i : Fin (2 ^ l.val)) (i' : Fin (2 ^ l'.val))
    (hl_k : l.val ≤ P.k) (hl'_k : l'.val ≤ P.k)
    (hl : l = l') (hi_val : i.val = i'.val) :
    P.Iq l i hl_k = P.Iq l' i' hl'_k := by
  subst hl
  cases i; cases i'
  simp only at hi_val
  subst hi_val
  rfl

/-- `crtIq_iter` applied to `mk f` evaluates to `mk f` in each component. -/
lemma crtIq_iter_mk_eval (l : Fin P.d) (i : Fin (2 ^ l.val)) (m : ℕ)
    (hm_d : l.val + m < P.d) (hm_k : l.val + m ≤ P.k)
    (f : P.Poly) (j : Fin (2 ^ m)) :
    (P.crtIq_iter l i m hm_d hm_k
      (Ideal.Quotient.mk (P.Iq l i (by omega)) f)) j =
      Ideal.Quotient.mk (P.Iq ⟨l.val + m, by omega⟩
        ⟨2 ^ m * i.val + j.val, by
          calc 2 ^ m * i.val + j.val
            < 2 ^ m * i.val + 2 ^ m := Nat.add_lt_add_left j.isLt _
            _ = 2 ^ m * (i.val + 1) := by ring
            _ ≤ 2 ^ m * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
            _ = 2 ^ (l.val + m) := by rw [← Nat.pow_add]; ring_nf⟩ (by omega)) f := by
  simp only [crtIq_iter, RingEquiv.trans_apply]
  apply Ideal.Quotient.eq.mpr
  simp

/-- Base case: When `m = 0`, `crtIq_iter` at index `0 : Fin 1` gives back the identity. -/
lemma crtIq_iter_zero_eval (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hm_d : l.val + 0 < P.d) (hm_k : l.val + 0 ≤ P.k) (f : P.Poly) :
    (P.crtIq_iter l i 0 hm_d hm_k (Ideal.Quotient.mk (P.Iq l i (by omega)) f)) (0 : Fin 1) =
      Ideal.Quotient.mk (P.Iq ⟨l.val + 0, by omega⟩
        ⟨2 ^ 0 * i.val + 0, by norm_num⟩ (by omega)) f := by
  simp only [crtIq_iter]
  apply Ideal.Quotient.eq.mpr
  simp [sub_self]

end NTTParams


/-! ## Polynomial splitting utilities

  These are generic utilities for splitting a polynomial `f` of degree `≤ 2n−1`
  into low and high halves: `f = low + X^n · high`, where both halves have
  degree `< n`.  They are used by the NTT butterfly. -/

section PolySplit

open Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Split a polynomial into low and high halves at position `n`.
    Given `f` with degree `≤ 2n−1`, returns `(low, high)` with
    `f = low + X^n · high` and both parts of degree `< n`. -/
noncomputable
def poly_split (n : ℕ) (f : R[X]) (_hf : f.degree ≤ (2*n - 1 : ℕ)) : R[X] × R[X] :=
  let low := ∑ i ∈ Finset.range n, f.coeff i • X ^ i
  let high := ∑ i ∈ Finset.range n, f.coeff (i + n) • X ^ i
  (low, high)

omit [Nontrivial R] in
/-- The result of `poly_split` satisfies `f = low + X^n · high`. -/
lemma poly_split_eq (n : ℕ) (hn : 0 < n) (f : R[X]) (hf : f.degree ≤ (2*n - 1 : ℕ)) :
    let (low, high) := poly_split n f hf
    f = low + X ^ n * high := by
  simp only [poly_split]
  ext i
  simp only [coeff_add, Finset.mul_sum, finset_sum_coeff,
             coeff_smul, coeff_X_pow, coeff_mul]
  by_cases hi : i < n
  · simp [hi]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun p hp => ?_
    split_ifs with h1 h2 <;> try rfl
    simp [Finset.mem_antidiagonal] at hp
    omega
  · simp [hi]
    push_neg at hi
    by_cases hi2 : i - n < n
    · rw [Finset.sum_eq_single (i - n)]
      · rw [Finset.sum_eq_single (n, i - n)]
        · grind
        · grind
        · intro h; exfalso; apply h; simp [Finset.mem_antidiagonal, Nat.add_sub_cancel' hi]
      · intro x hx hxne; apply Finset.sum_eq_zero; intro p hp; split_ifs with h1 h2 <;> try rfl
        simp [Finset.mem_antidiagonal] at hp; omega
      · grind
    · push_neg at hi2
      have hi_large : 2 * n ≤ i := by omega
      have hfi : f.coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        calc f.degree ≤ (2*n - 1 : ℕ) := hf
             _ < (2*n : WithBot ℕ) := by exact Nat.cast_lt.mpr (by omega : 2*n - 1 < 2*n)
             _ ≤ i := by exact Nat.cast_le.mpr hi_large
      rw [hfi]; symm; refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun p hp => ?_
      split_ifs with h1 h2 <;> (simp [Finset.mem_antidiagonal] at hp; grind)

/-- Both parts of `poly_split` have degree `< n`. -/
lemma poly_split_degree_lt {n : ℕ} (hn : n ≠ 0) (f : R[X])
    (hf : f.degree ≤ (2 * n - 1 : ℕ)) :
    (poly_split n f hf).1.degree < n ∧ (poly_split n f hf).2.degree < n := by
  have aux : ∀ (g : ℕ → R),
      (∑ i ∈ Finset.range n, g i • X ^ i : R[X]).degree < n := by
    intro g
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    by_cases he : (Finset.range n).Nonempty
    · have h_bound : (Finset.range n).sup (fun i => (g i • X ^ i : R[X]).degree) ≤ (n - 1 : ℕ) := by
        apply Finset.sup_le
        intro i hi
        have : i < n := Finset.mem_range.mp hi
        calc (g i • X ^ i : R[X]).degree
          ≤ (X ^ i).degree := Polynomial.degree_smul_le _ _
          _ = i := Polynomial.degree_X_pow i
          _ ≤ (n - 1 : ℕ) := by exact_mod_cast (Nat.lt_iff_le_pred (Nat.pos_of_ne_zero hn)).mp this
      calc (Finset.range n).sup (fun i => (g i • X ^ i).degree)
        ≤ (n - 1 : ℕ) := h_bound
        _ < n := by exact_mod_cast (Nat.sub_one_lt_of_lt (Nat.pos_of_ne_zero hn))
    · simp [Finset.not_nonempty_iff_eq_empty.mp he]
  simp only [poly_split]
  exact ⟨aux (f.coeff ·), aux (fun i => f.coeff (i + n))⟩

omit [Nontrivial R] in
/-- Degree bound for `low ± C c · high` when both have degree `< n`. -/
lemma degree_add_sub_C_mul_lt {n : ℕ} (low high : R[X]) (c : R) (hc : c ≠ 0)
    (hlow : low.degree < n) (hhigh : high.degree < n) :
    (low + C c * high).degree < n ∧ (low - C c * high).degree < n := by
  have hC : (C c).degree = 0 := Polynomial.degree_C hc
  have hChigh : (C c * high).degree ≤ high.degree := by
    calc (C c * high).degree
      ≤ (C c).degree + high.degree := Polynomial.degree_mul_le _ _
      _ = high.degree := by simp [hC]
  constructor
  · calc (low + C c * high).degree
      ≤ max low.degree (C c * high).degree := Polynomial.degree_add_le _ _
      _ ≤ max low.degree high.degree := max_le_max le_rfl hChigh
      _ < n := max_lt hlow hhigh
  · calc (low - C c * high).degree
      ≤ max low.degree (C c * high).degree := Polynomial.degree_sub_le _ _
      _ ≤ max low.degree high.degree := max_le_max le_rfl hChigh
      _ < n := max_lt hlow hhigh

omit [Nontrivial R] in
/-- Convert degree `< n` to degree `≤ n - 1`. -/
lemma degree_lt_to_le_pred {p : R[X]} {n : ℕ} (hn : 0 < n) (h : p.degree < n) :
    p.degree ≤ (n - 1 : ℕ) := by
  rcases hp : p.degree with _ | d
  · exact bot_le
  · rw [hp] at h
    exact WithBot.coe_le_coe.mpr (Nat.lt_iff_le_pred hn |>.mp (WithBot.coe_lt_coe.mp h))

end PolySplit


/-! ## NTT butterfly

  The butterfly operation splits a polynomial into two halves and combines them with
  a twiddle factor.  We prove it agrees with the CRT isomorphism `crtIq`. -/

namespace NTTParams

open Polynomial

variable (P : NTTParams)

/-- NTT butterfly at level `l`, splitting a polynomial at position `2^(k-(l+1))`.
    Given a polynomial `f` with degree `≤ 2^(k-l) - 1`, produces a pair
    `(low + C twiddle · high, low − C twiddle · high)` where `twiddle = ζ^(ζ_exp(l+1, 2i))`. -/
noncomputable
def ntt_butterfly_poly (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ)) : P.Poly × P.Poly :=
  have h2n : 2 * 2 ^ (P.k - (l.val + 1)) = 2 ^ (P.k - l.val) := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  have hdeg : f.degree ≤ (2 * 2 ^ (P.k - (l.val + 1)) - 1 : ℕ) := by rw [h2n]; exact hf
  let (low, high) := poly_split (2 ^ (P.k - (l.val + 1))) f hdeg
  let exp := P.ζ_exp ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩
  let twiddle := P.ζ ^ exp
  (low + C twiddle * high, low - C twiddle * high)

/-- Degree bounds on both components of the NTT butterfly. -/
lemma ntt_butterfly_poly_degree (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ)) :
    (P.ntt_butterfly_poly l i hl_d hl_k f hf).1.degree ≤ (2 ^ (P.k - (l.val + 1)) - 1 : ℕ) ∧
    (P.ntt_butterfly_poly l i hl_d hl_k f hf).2.degree ≤ (2 ^ (P.k - (l.val + 1)) - 1 : ℕ) := by
  simp only [ntt_butterfly_poly]
  have h2n : 2 * 2 ^ (P.k - (l.val + 1)) = 2 ^ (P.k - l.val) := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  have hdeg : f.degree ≤ (2 * 2 ^ (P.k - (l.val + 1)) - 1 : ℕ) := by rw [h2n]; exact hf
  have hn : 2 ^ (P.k - (l.val + 1)) ≠ 0 := by positivity
  have hlow := (poly_split_degree_lt hn f hdeg).1
  have hhigh := (poly_split_degree_lt hn f hdeg).2
  have hc : P.ζ ^ P.ζ_exp ⟨l.val + 1, by omega⟩
      ⟨2 * i.val, by simp [pow_succ]; omega⟩ ≠ 0 :=
    pow_ne_zero _ P.ζ_ne_zero
  have h_deg_lt := degree_add_sub_C_mul_lt _ _ _ hc hlow hhigh
  exact ⟨degree_lt_to_le_pred (by positivity) h_deg_lt.1,
         degree_lt_to_le_pred (by positivity) h_deg_lt.2⟩

/-- NTT butterfly on quotient rings: produces the pair of quotient ring elements
    in the two child rings. -/
noncomputable
def ntt_butterfly (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ)) :
    (P.Sq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by omega)) ×
    (P.Sq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by omega)) :=
  let (p1, p2) := P.ntt_butterfly_poly l i hl_d hl_k f hf
  (Ideal.Quotient.mk (P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by omega)) p1,
   Ideal.Quotient.mk (P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by omega)) p2)

/-- The butterfly operation agrees with the CRT isomorphism:
    `ntt_butterfly l i f = crtIq l i [f]`. -/
theorem ntt_butterfly_eq_crt (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ)) :
    P.ntt_butterfly l i hl_d hl_k f hf =
      P.crtIq l i hl_d hl_k (Ideal.Quotient.mk (P.Iq l i (by omega)) f) := by
  let l' : Fin P.d := ⟨l.val + 1, by omega⟩
  let i₁ : Fin (2 ^ l'.val) := ⟨2 * i.val, by simp [l', pow_succ]; omega⟩
  let i₂ : Fin (2 ^ l'.val) := ⟨2 * i.val + 1, by simp [l', pow_succ]; omega⟩
  let I₁ := P.Iq l' i₁ (by omega)
  let I₂ := P.Iq l' i₂ (by omega)
  let n := 2 ^ (P.k - (l.val + 1))
  let exp := P.ζ_exp l' i₁
  let twiddle := P.ζ ^ exp
  let low : P.Poly := ∑ j ∈ Finset.range n, f.coeff j • X ^ j
  let high : P.Poly := ∑ j ∈ Finset.range n, f.coeff (j + n) • X ^ j

  have h2n : 2 * n = 2 ^ (P.k - l.val) := by
    simp only [n]; rw [mul_comm, ← pow_succ]; congr 1; omega
  have hf' : f.degree ≤ (2 * n - 1 : ℕ) := by rw [h2n]; exact hf
  have split_eq : f = low + X ^ n * high :=
    poly_split_eq n (by simp only [n]; positivity) f hf'

  simp only [ntt_butterfly, ntt_butterfly_poly, poly_split]
  ext
  · rw [P.crtIq_fst]
    show Ideal.Quotient.mk I₁ (low + C twiddle * high) = Ideal.Quotient.mk I₁ f
    have Xn_eq_twiddle : Ideal.Quotient.mk I₁ (X ^ n) =
                         Ideal.Quotient.mk I₁ (C twiddle) := by
      simp only [Ideal.Quotient.eq, I₁, Iq, fq, xn, ζ_poly, x_exp, l', i₁, exp, twiddle, n,
                 Ideal.mem_span_singleton]
      use 1
      rw [X_pow_eq_monomial]
      simp
    symm
    calc Ideal.Quotient.mk I₁ f
      _ = Ideal.Quotient.mk I₁ low + Ideal.Quotient.mk I₁ (X ^ n) *
            Ideal.Quotient.mk I₁ high := by simp [split_eq, map_add, map_mul]
      _ = Ideal.Quotient.mk I₁ low + Ideal.Quotient.mk I₁ (C twiddle) *
            Ideal.Quotient.mk I₁ high := by rw [Xn_eq_twiddle]
      _ = Ideal.Quotient.mk I₁ (low + C twiddle * high) := by simp [map_add, map_mul]
  · rw [P.crtIq_snd]
    show Ideal.Quotient.mk I₂ (low - C twiddle * high) = Ideal.Quotient.mk I₂ f
    have h_odd := BitRev_odd_from_even (l.val + 1) (by omega) i
    simp at h_odd
    have h_merge : 2 ^ l.val * 2 ^ (P.d - (l.val + 1)) = 2 ^ (P.d - 1) := by
      rw [← pow_add]; congr 1; omega
    have h_ζ_split : P.ζ_exp l' i₂ = exp + 2 ^ (P.d - 1) := by
      simp only [l', i₂, i₁, exp, ζ_exp, h_odd, add_mul]
      linarith [h_merge]
    have Xn_eq_neg_twiddle : Ideal.Quotient.mk I₂ (X ^ n) =
                             Ideal.Quotient.mk I₂ (-C twiddle) := by
      have hζ_half : (C P.ζ : P.Poly) ^ (2 ^ (P.d - 1)) = -1 := by
        rw [← C_pow, P.ζ_pow_two_pow_pred_d, map_neg, map_one]
      have hζ_i₂ : P.ζ_poly ^ (P.ζ_exp l' i₂) = -C twiddle := by
        simp only [ζ_poly, h_ζ_split, pow_add, hζ_half, mul_neg_one, twiddle, exp, ← C_pow]
      simp only [Ideal.Quotient.eq, I₂, Iq, sub_neg_eq_add, Ideal.mem_span_singleton]
      exact ⟨1, by simp only [fq, xn, x_exp, l', n, hζ_i₂]; rw [X_pow_eq_monomial]; ring⟩
    symm
    calc Ideal.Quotient.mk I₂ f
      _ = Ideal.Quotient.mk I₂ low + Ideal.Quotient.mk I₂ (X ^ n) *
            Ideal.Quotient.mk I₂ high := by simp [split_eq, map_add, map_mul]
      _ = Ideal.Quotient.mk I₂ low + Ideal.Quotient.mk I₂ (-C twiddle) *
            Ideal.Quotient.mk I₂ high := by rw [Xn_eq_neg_twiddle]
      _ = Ideal.Quotient.mk I₂ (low - C twiddle * high) := by simp [map_mul]; ring

/-- The first butterfly component maps to the same quotient class as f in the first child ring. -/
lemma ntt_butterfly_poly_fst_eq_mod (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ)) :
    Ideal.Quotient.mk
      (P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by omega))
      (P.ntt_butterfly_poly l i hl_d hl_k f hf).1 =
    Ideal.Quotient.mk
      (P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by omega)) f := by
  have := congr_arg (·.1) (P.ntt_butterfly_eq_crt l i hl_d hl_k f hf)
  simp only [ntt_butterfly] at this
  rw [P.crtIq_fst] at this
  exact this

/-- The second butterfly component maps to the same quotient class as f in the second child ring. -/
lemma ntt_butterfly_poly_snd_eq_mod (l : Fin P.d) (i : Fin (2 ^ l.val))
    (hl_d : l.val + 1 < P.d) (hl_k : l.val + 1 ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ)) :
    Ideal.Quotient.mk
      (P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by omega))
      (P.ntt_butterfly_poly l i hl_d hl_k f hf).2 =
    Ideal.Quotient.mk
      (P.Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by omega)) f := by
  have := congr_arg (·.2) (P.ntt_butterfly_eq_crt l i hl_d hl_k f hf)
  simp only [ntt_butterfly] at this
  rw [P.crtIq_snd] at this
  exact this


/-! ### Iterated m-fold butterfly -/

/-- Apply NTT butterfly `m` times, producing `2^m` polynomials.
    Given a polynomial `f` at level `l` with appropriate degree bound, applies `m` butterfly
    operations to decompose it into `2^m` polynomials. -/
noncomputable
def ntt_butterfly_poly_iter (l : Fin P.d) (i : Fin (2 ^ l.val)) (m : ℕ)
    (hm_d : l.val + m < P.d) (hm_k : l.val + m ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ)) :
    Fin (2 ^ m) → P.Poly :=
  match m with
  | 0 => fun _ => f
  | m' + 1 =>
      have hl_d : l.val + 1 < P.d := by omega
      have hl_k : l.val + 1 ≤ P.k := by omega
      have hm'_d : (l.val + 1) + m' < P.d := by omega
      have hm'_k : (l.val + 1) + m' ≤ P.k := by omega
      let p1 := (P.ntt_butterfly_poly l i hl_d hl_k f hf).1
      let p2 := (P.ntt_butterfly_poly l i hl_d hl_k f hf).2
      have hf1 : p1.degree ≤ (2 ^ (P.k - (l.val + 1)) - 1 : ℕ) :=
        (P.ntt_butterfly_poly_degree l i hl_d hl_k f hf).1
      have hf2 : p2.degree ≤ (2 ^ (P.k - (l.val + 1)) - 1 : ℕ) :=
        (P.ntt_butterfly_poly_degree l i hl_d hl_k f hf).2
      let rec1 := ntt_butterfly_poly_iter ⟨l.val + 1, by omega⟩
        ⟨2 * i.val, by simp [pow_succ]; omega⟩ m' hm'_d hm'_k p1 hf1
      let rec2 := ntt_butterfly_poly_iter ⟨l.val + 1, by omega⟩
        ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ m' hm'_d hm'_k p2 hf2
      fun j => if h : j.val < 2 ^ m' then
                 rec1 ⟨j.val, by omega⟩
               else
                 rec2 ⟨j.val - 2 ^ m', by
                   have hj : j.val < 2 ^ (m' + 1) := j.prop
                   have hge : 2 ^ m' ≤ j.val := Nat.not_lt.mp h
                   have hpow : 2 ^ (m' + 1) = 2 ^ m' + 2 ^ m' := by ring
                   calc j.val - 2 ^ m' < 2 ^ (m' + 1) - 2 ^ m' := Nat.sub_lt_sub_right hge hj
                     _ = 2 ^ m' := by simp [hpow]⟩

/-- Apply NTT butterfly `m` times, producing `2^m` quotient ring elements. -/
noncomputable
def ntt_butterfly_iter (l : Fin P.d) (i : Fin (2 ^ l.val)) (m : ℕ)
    (hm_d : l.val + m < P.d) (hm_k : l.val + m ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ)) :
    (j : Fin (2 ^ m)) → P.Sq ⟨l.val + m, by omega⟩ ⟨2 ^ m * i.val + j.val, by
      calc 2 ^ m * i.val + j.val
        _ < 2 ^ m * i.val + 2 ^ m := by omega
        _ = (i.val + 1) * 2 ^ m := by ring
        _ ≤ 2 ^ l.val * 2 ^ m := by apply Nat.mul_le_mul_right; omega
        _ = 2 ^ (l.val + m) := by rw [← Nat.pow_add]⟩ (by omega) :=
  fun j =>
    Ideal.Quotient.mk (P.Iq ⟨l.val + m, by omega⟩ ⟨2 ^ m * i.val + j.val, by
      calc 2 ^ m * i.val + j.val
        _ < 2 ^ m * i.val + 2 ^ m := by omega
        _ = (i.val + 1) * 2 ^ m := by ring
        _ ≤ 2 ^ l.val * 2 ^ m := by apply Nat.mul_le_mul_right; omega
        _ = 2 ^ (l.val + m) := by rw [← Nat.pow_add]⟩ (by omega))
      (P.ntt_butterfly_poly_iter l i m hm_d hm_k f hf j)

/-- `ntt_butterfly_iter` is just `mk (ntt_butterfly_poly_iter ...)`. -/
lemma ntt_butterfly_iter_eq_mk (l : Fin P.d) (i : Fin (2 ^ l.val)) (m : ℕ)
    (hm_d : l.val + m < P.d) (hm_k : l.val + m ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ))
    (j : Fin (2 ^ m)) :
    P.ntt_butterfly_iter l i m hm_d hm_k f hf j =
      Ideal.Quotient.mk (P.Iq ⟨l.val + m, by omega⟩ ⟨2 ^ m * i.val + j.val, by
        calc 2 ^ m * i.val + j.val
          _ < 2 ^ m * i.val + 2 ^ m := by omega
          _ = (i.val + 1) * 2 ^ m := by ring
          _ ≤ 2 ^ l.val * 2 ^ m := by apply Nat.mul_le_mul_right; omega
          _ = 2 ^ (l.val + m) := by rw [← Nat.pow_add]⟩ (by omega))
        (P.ntt_butterfly_poly_iter l i m hm_d hm_k f hf j) := by
  rfl


/-! #### Reindex lemmas -/

/-- Reindex an Iq ideal: for the first half (`j < 2^m'`), the flat index
    at level `l + (m'+1)` equals the split index at level `(l+1) + m'`. -/
lemma Iq_reindex_fst (l : Fin P.d) (i : Fin (2 ^ l.val)) (m' : ℕ)
    (hm_d : l.val + (m' + 1) < P.d) (hm_k : l.val + (m' + 1) ≤ P.k)
    (j : Fin (2 ^ (m' + 1))) (hj : j.val < 2 ^ m') :
    P.Iq ⟨l.val + (m' + 1), by omega⟩ ⟨2 ^ (m' + 1) * i.val + j.val, by
          calc 2 ^ (m' + 1) * i.val + j.val
            < 2 ^ (m' + 1) * i.val + 2 ^ (m' + 1) := Nat.add_lt_add_left j.isLt _
            _ = 2 ^ (m' + 1) * (i.val + 1) := by ring
            _ ≤ 2 ^ (m' + 1) * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
            _ = 2 ^ (l.val + (m' + 1)) := by rw [← Nat.pow_add]; ring_nf⟩ (by omega) =
        P.Iq ⟨(l.val + 1) + m', by omega⟩ ⟨2 ^ m' * (2 * i.val) + j.val, by
          calc 2 ^ m' * (2 * i.val) + j.val
            < 2 ^ m' * (2 * i.val) + 2 ^ m' := by omega
            _ = 2 ^ m' * (2 * i.val + 1) := by ring
            _ ≤ 2 ^ m' * 2 ^ (l.val + 1) := by apply Nat.mul_le_mul_left; omega
            _ = 2 ^ ((l.val + 1) + m') := by rw [← Nat.pow_add]; ring_nf⟩ (by simp; omega) := by
  apply P.Iq_fin_cast <;> simp <;> ring

/-- Reindex an Iq ideal: for the second half (`j ≥ 2^m'`), the flat index
    at level `l + (m'+1)` equals the split index at level `(l+1) + m'`. -/
lemma Iq_reindex_snd (l : Fin P.d) (i : Fin (2 ^ l.val)) (m' : ℕ)
    (hm_d : l.val + (m' + 1) < P.d) (hm_k : l.val + (m' + 1) ≤ P.k)
    (j : Fin (2 ^ (m' + 1))) (hj : 2 ^ m' ≤ j.val) :
    have hj_sub : j.val - 2 ^ m' < 2 ^ m' := by
      have : 2 ^ (m' + 1) = 2 * 2 ^ m' := by rw [Nat.pow_succ]; ring
      omega
    P.Iq ⟨l.val + (m' + 1), by omega⟩ ⟨2 ^ (m' + 1) * i.val + j.val, by
          calc 2 ^ (m' + 1) * i.val + j.val
            < 2 ^ (m' + 1) * i.val + 2 ^ (m' + 1) := Nat.add_lt_add_left j.isLt _
            _ = 2 ^ (m' + 1) * (i.val + 1) := by ring
            _ ≤ 2 ^ (m' + 1) * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
            _ = 2 ^ (l.val + (m' + 1)) := by rw [← Nat.pow_add]; ring_nf⟩ (by omega) =
        P.Iq ⟨(l.val + 1) + m', by omega⟩ ⟨2 ^ m' * (2 * i.val + 1) + (j.val - 2 ^ m'), by
          calc 2 ^ m' * (2 * i.val + 1) + (j.val - 2 ^ m')
            < 2 ^ m' * (2 * i.val + 1) + 2 ^ m' := by omega
            _ = 2 ^ m' * (2 * i.val + 2) := by ring
            _ ≤ 2 ^ m' * 2 ^ (l.val + 1) := by apply Nat.mul_le_mul_left; omega
            _ = 2 ^ ((l.val + 1) + m') := by rw [← Nat.pow_add]; ring_nf⟩ (by simp; omega) := by
  apply P.Iq_fin_cast
  · simp; ring
  · simp
    have h2m : 2 ^ (m' + 1) = 2 * 2 ^ m' := by rw [Nat.pow_succ]; ring
    simp only [h2m]; zify [hj]; ring


/-! #### Equation lemmas for ntt_butterfly_poly_iter -/

/-- Equation lemma: `ntt_butterfly_poly_iter` at `m'+1` for `j < 2^m'` equals the recursive
    call on the first butterfly component. -/
private lemma ntt_butterfly_poly_iter_succ_fst (l : Fin P.d) (i : Fin (2 ^ l.val))
    (m' : ℕ)
    (hm_d : l.val + (m' + 1) < P.d) (hm_k : l.val + (m' + 1) ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ))
    (j : Fin (2 ^ (m' + 1))) (hj : j.val < 2 ^ m') :
    P.ntt_butterfly_poly_iter l i (m' + 1) hm_d hm_k f hf j =
      P.ntt_butterfly_poly_iter ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩
        m' (by simp; omega) (by simp; omega)
        (P.ntt_butterfly_poly l i (by omega) (by omega) f hf).1
        (P.ntt_butterfly_poly_degree l i (by omega) (by omega) f hf).1
        ⟨j.val, by omega⟩ := by
  conv_lhs => unfold ntt_butterfly_poly_iter; dsimp only []
  rw [dif_pos hj]

/-- Equation lemma: `ntt_butterfly_poly_iter` at `m'+1` for `¬ j < 2^m'` equals the recursive
    call on the second butterfly component. -/
private lemma ntt_butterfly_poly_iter_succ_snd (l : Fin P.d) (i : Fin (2 ^ l.val))
    (m' : ℕ)
    (hm_d : l.val + (m' + 1) < P.d) (hm_k : l.val + (m' + 1) ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ))
    (j : Fin (2 ^ (m' + 1))) (hj : ¬ j.val < 2 ^ m') :
    have hj_sub : j.val - 2 ^ m' < 2 ^ m' := by
      have : 2 ^ (m' + 1) = 2 * 2 ^ m' := by rw [Nat.pow_succ]; ring
      omega
    P.ntt_butterfly_poly_iter l i (m' + 1) hm_d hm_k f hf j =
      P.ntt_butterfly_poly_iter ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩
        m' (by simp; omega) (by simp; omega)
        (P.ntt_butterfly_poly l i (by omega) (by omega) f hf).2
        (P.ntt_butterfly_poly_degree l i (by omega) (by omega) f hf).2
        ⟨j.val - 2 ^ m', hj_sub⟩ := by
  show P.ntt_butterfly_poly_iter l i (m' + 1) hm_d hm_k f hf j = _
  conv_lhs => unfold ntt_butterfly_poly_iter; dsimp only []
  rw [dif_neg hj]


/-! #### Iterated m-fold CRT theorem -/

/-- Case 1 of the iterated m-fold CRT theorem: first half (`j < 2^m'`). -/
private lemma ntt_butterfly_iter_eq_crt_fst (l : Fin P.d) (i : Fin (2 ^ l.val))
    (m' : ℕ) (hm_d : l.val + (m' + 1) < P.d) (hm_k : l.val + (m' + 1) ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ))
    (j : Fin (2 ^ (m' + 1))) (hj : j.val < 2 ^ m')
    (IH : P.ntt_butterfly_iter ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩
            m' (by simp; omega) (by simp; omega)
            (P.ntt_butterfly_poly l i (by omega) (by omega) f hf).1
            (P.ntt_butterfly_poly_degree l i (by omega) (by omega) f hf).1 =
          P.crtIq_iter ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩
            m' (by simp; omega) (by simp; omega)
            (Ideal.Quotient.mk (P.Iq ⟨l.val + 1, by omega⟩
              ⟨2 * i.val, by simp [pow_succ]; omega⟩ (by simp; omega))
              (P.ntt_butterfly_poly l i (by omega) (by omega) f hf).1)) :
    P.ntt_butterfly_iter l i (m' + 1) hm_d hm_k f hf j =
      P.crtIq_iter l i (m' + 1) hm_d hm_k (Ideal.Quotient.mk (P.Iq l i (by omega)) f) j := by
  have ideal_eq := P.Iq_reindex_fst l i m' hm_d hm_k j hj
  have IH_j := congr_fun IH ⟨j.val, by omega⟩
  rw [P.ntt_butterfly_iter_eq_mk, P.crtIq_iter_mk_eval] at IH_j
  rw [P.crtIq_iter_mk_eval, P.ntt_butterfly_iter_eq_mk,
      P.ntt_butterfly_poly_iter_succ_fst l i m' hm_d hm_k f hf j hj]
  apply Ideal.Quotient.eq.mpr
  rw [ideal_eq]
  have hsplit : ∀ (a b c : P.Poly), a - c = (a - b) + (b - c) := fun a b c => by ring
  rw [hsplit _ (P.ntt_butterfly_poly l i (by omega) (by omega) f hf).1 f]
  exact Ideal.add_mem _
    (Ideal.Quotient.eq.mp IH_j)
    (P.Iq_le_descendant ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩
      m' (by simp; omega) (by simp; omega) ⟨j.val, hj⟩
      (Ideal.Quotient.eq.mp (P.ntt_butterfly_poly_fst_eq_mod l i (by omega) (by omega) f hf)))

/-- Case 2 of the m-fold CRT theorem: second half (`j ≥ 2^m'`). -/
private lemma ntt_butterfly_iter_eq_crt_snd (l : Fin P.d) (i : Fin (2 ^ l.val))
    (m' : ℕ) (hm_d : l.val + (m' + 1) < P.d) (hm_k : l.val + (m' + 1) ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ))
    (j : Fin (2 ^ (m' + 1))) (hj : ¬ j.val < 2 ^ m')
    (IH : P.ntt_butterfly_iter ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩
            m' (by simp; omega) (by simp; omega)
            (P.ntt_butterfly_poly l i (by omega) (by omega) f hf).2
            (P.ntt_butterfly_poly_degree l i (by omega) (by omega) f hf).2 =
          P.crtIq_iter ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩
            m' (by simp; omega) (by simp; omega)
            (Ideal.Quotient.mk (P.Iq ⟨l.val + 1, by omega⟩
              ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩ (by simp; omega))
              (P.ntt_butterfly_poly l i (by omega) (by omega) f hf).2)) :
    P.ntt_butterfly_iter l i (m' + 1) hm_d hm_k f hf j =
      P.crtIq_iter l i (m' + 1) hm_d hm_k (Ideal.Quotient.mk (P.Iq l i (by omega)) f) j := by
  have hj' : 2 ^ m' ≤ j.val := Nat.not_lt.mp hj
  have hj_sub : j.val - 2 ^ m' < 2 ^ m' := by
    have : 2 ^ (m' + 1) = 2 * 2 ^ m' := by rw [Nat.pow_succ]; ring
    omega
  have ideal_eq := P.Iq_reindex_snd l i m' hm_d hm_k j hj'
  have IH_j := congr_fun IH ⟨j.val - 2 ^ m', hj_sub⟩
  rw [P.ntt_butterfly_iter_eq_mk, P.crtIq_iter_mk_eval] at IH_j
  rw [P.crtIq_iter_mk_eval, P.ntt_butterfly_iter_eq_mk,
      P.ntt_butterfly_poly_iter_succ_snd l i m' hm_d hm_k f hf j hj]
  apply Ideal.Quotient.eq.mpr
  rw [ideal_eq]
  have hsplit : ∀ (a b c : P.Poly), a - c = (a - b) + (b - c) := fun a b c => by ring
  rw [hsplit _ (P.ntt_butterfly_poly l i (by omega) (by omega) f hf).2 f]
  exact Ideal.add_mem _
    (Ideal.Quotient.eq.mp IH_j)
    (P.Iq_le_descendant ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩
      m' (by simp; omega) (by simp; omega) ⟨j.val - 2 ^ m', hj_sub⟩
      (Ideal.Quotient.eq.mp (P.ntt_butterfly_poly_snd_eq_mod l i (by omega) (by omega) f hf)))

/-- The iterated m-fold butterfly operation agrees with the m-fold CRT isomorphism.
    This is the main theorem: applying `m` recursive butterfly operations produces the same
    result as the abstract CRT isomorphism decomposing into `2^m` quotient rings. -/
theorem ntt_butterfly_iter_eq_crt (l : Fin P.d) (i : Fin (2 ^ l.val)) (m : ℕ)
    (hm_d : l.val + m < P.d) (hm_k : l.val + m ≤ P.k)
    (f : P.Poly) (hf : f.degree ≤ (2 ^ (P.k - l.val) - 1 : ℕ)) :
    P.ntt_butterfly_iter l i m hm_d hm_k f hf =
      P.crtIq_iter l i m hm_d hm_k (Ideal.Quotient.mk (P.Iq l i (by omega)) f) := by
  match m with
  | 0 =>
    ext j; fin_cases j
    simp only [ntt_butterfly_iter, ntt_butterfly_poly_iter]
    rw [← P.crtIq_iter_zero_eval]; rfl
  | m' + 1 =>
    ext j
    by_cases hj : j.val < 2 ^ m'
    · exact P.ntt_butterfly_iter_eq_crt_fst l i m' hm_d hm_k f hf j hj
          (ntt_butterfly_iter_eq_crt ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp [pow_succ]; omega⟩
            m' (by simp; omega) (by simp; omega) _ _)
    · exact P.ntt_butterfly_iter_eq_crt_snd l i m' hm_d hm_k f hf j hj
          (ntt_butterfly_iter_eq_crt ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp [pow_succ]; omega⟩
            m' (by simp; omega) (by simp; omega) _ _)

end NTTParams


/-! ## ML-KEM instantiation -/

/-- The ML-KEM parameters: `q = 3329`, `k = d = 8`, `ζ = 17`.
    Here `ζ = 17` is a primitive `256`-th root of unity.  Since `k = d`,
    the NTT tree stops at quadratic leaves. -/
noncomputable def MLKEM_NTTParams : NTTParams where
  q := 3329
  k := 8
  d := 8
  ζ := 17
  q_prime := by native_decide
  k_pos := by omega
  d_pos := by omega
  ζ_order := by
    apply (orderOf_eq_iff (show 0 < 2 ^ 8 by norm_num)).mpr
    exact ⟨by native_decide, fun m hm_pos hm_lt => by interval_cases m <;> native_decide⟩

open NTTParams Polynomial in
/-- **ML-KEM NTT theorem.**  Applying 7 levels of butterfly operations to a polynomial
    `f ∈ (ZMod 3329)[X]` of degree `≤ 255` produces the same result as the
    CRT isomorphism into `128` quotient rings `(ZMod 3329)[X] / ⟨X² − ζ^(2·BitRev(7,j)+1)⟩`.

    This is the formal statement that the butterfly NTT algorithm computes the
    Chinese Remainder Theorem decomposition of `ℤ₃₃₂₉[X]/(X²⁵⁶+1)`. -/
theorem mlkem_ntt_eq_crt
    (f : (ZMod 3329)[X])
    (hf : f.degree ≤ 255) :
    MLKEM_NTTParams.ntt_butterfly_iter
      ⟨0, by decide⟩ ⟨0, by simp⟩ 7 (by decide) (by decide) f (by simpa using hf) =
    MLKEM_NTTParams.crtIq_iter
      ⟨0, by decide⟩ ⟨0, by simp⟩ 7 (by decide) (by decide)
      (Ideal.Quotient.mk (MLKEM_NTTParams.Iq ⟨0, by decide⟩ ⟨0, by simp⟩ (by decide)) f) :=
  MLKEM_NTTParams.ntt_butterfly_iter_eq_crt ⟨0, by decide⟩ ⟨0, by simp⟩ 7
    (by decide) (by decide) f (by simpa using hf)


/-! ## ML-DSA instantiation -/

/-- The ML-DSA parameters: `q = 8380417`, `k = 8`, `d = 9`, `ζ = 1753`.
    Here `ζ = 1753` is a primitive `512`-th root of unity.  Since `d = k + 1`,
    the NTT tree decomposes all the way to linear leaves. -/
noncomputable def MLDSA_NTTParams : NTTParams where
  q := 8380417
  k := 8
  d := 9
  ζ := 1753
  q_prime := by native_decide
  k_pos := by omega
  d_pos := by omega
  ζ_order := by
    apply (orderOf_eq_iff (show 0 < 2 ^ 9 by norm_num)).mpr
    exact ⟨by native_decide, fun m hm_pos hm_lt => by interval_cases m <;> native_decide⟩

open NTTParams Polynomial in
/-- **ML-DSA NTT theorem.**  Applying 8 levels of butterfly operations to a polynomial
    `f ∈ (ZMod 8380417)[X]` of degree `≤ 255` produces the same result as the
    CRT isomorphism into `256` quotient rings `(ZMod 8380417)[X] / ⟨X − ζ^(2·BitRev(8,j)+1)⟩`.

    Since `d = 9 > k = 8`, the NTT fully decomposes to 256 *linear* factors,
    giving a complete evaluation representation.  This is the formal statement
    that the butterfly NTT algorithm computes the CRT decomposition of
    `ℤ₈₃₈₀₄₁₇[X]/(X²⁵⁶+1)`. -/
theorem mldsa_ntt_eq_crt
    (f : (ZMod 8380417)[X])
    (hf : f.degree ≤ 255) :
    MLDSA_NTTParams.ntt_butterfly_iter
      ⟨0, by decide⟩ ⟨0, by simp⟩ 8 (by decide) (by decide) f (by simpa using hf) =
    MLDSA_NTTParams.crtIq_iter
      ⟨0, by decide⟩ ⟨0, by simp⟩ 8 (by decide) (by decide)
      (Ideal.Quotient.mk (MLDSA_NTTParams.Iq ⟨0, by decide⟩ ⟨0, by simp⟩ (by decide)) f) :=
  MLDSA_NTTParams.ntt_butterfly_iter_eq_crt ⟨0, by decide⟩ ⟨0, by simp⟩ 8
    (by decide) (by decide) f (by simpa using hf)
