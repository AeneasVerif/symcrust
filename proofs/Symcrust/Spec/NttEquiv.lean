import Lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Ring.Prod

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

import Init.Data.BitVec.Lemmas

set_option maxRecDepth 2500
set_option maxHeartbeats 100000
--set_option diagnostics true


/- In this file, "the thesis" refers to https://kannwischer.eu/thesis/phd-thesis-2023-01-03.pdf -/

/- The Kyber prime q and root of unity ζ -/

@[simp]
def q := 3329

@[simp]
lemma q_isPrime : Nat.Prime q := by native_decide
instance : Fact (Nat.Prime q) := ⟨q_isPrime⟩

lemma q_nonzero : q ≠ 0 := by trivial
lemma q_minus_one_fact : (q - 1) = 2^8 * 13 := rfl

example : (q-2)*q = 2^16 * 169 - 1 := by simp

def zeta := 17
theorem zeta_coprime : Nat.Coprime zeta q := by rfl


/-- Finite ring Zq --/

@[reducible]
def Zq := ZMod q
lemma Zq_cyclic : IsCyclic Zqˣ := by
  apply ZMod.isCyclic_units_prime q_isPrime

def Fq := Field Zq

namespace Zq
  open scoped ZMod
  open Nat

  def mk_elem (n : Fin q) : Zq := n
  def one : Zq := 1
  def ζ : Zq := zeta

  lemma zeta_ne_one : ζ ≠ 1 := by trivial
  lemma zeta_ne_zero : ζ ≠ 0 := by trivial

  theorem zeta_isUnit : IsUnit ζ := by
    rw [isUnit_iff_ne_zero]
    exact zeta_ne_zero

  lemma zeta_mul_inv_zeta_eq_one : ζ * ζ⁻¹ = 1 := by
    apply div_self zeta_ne_zero

  lemma inv_zeta_mul_zeta_eq_one : ζ⁻¹ * ζ = 1 := by
    rw [mul_comm]
    exact zeta_mul_inv_zeta_eq_one

  lemma inv_zeta_val : ζ⁻¹ = 1175 := by
    exact ZMod.inv_eq_of_mul_eq_one q ζ 1175 (by rfl : ζ * 1175 = 1)

  lemma inv_zeta_eq_zeta_pow : ζ⁻¹ = ζ ^ 255 := by
    rw [inv_zeta_val] ; rfl

  theorem zeta_256_eq : ζ ^ 256 = 1 := by rfl

  theorem zeta_128_eq : ζ ^ 128 = - 1 := by rfl

  example : ζ ^ 2 = 289 := by rfl

  example : ζ ^ 13 = 939 := by rfl

  lemma zeta_pow_m_neq_one (m : Nat) (hu : m < 256) (hl : 0 < m) : ζ ^ m ≠ 1 := by
    decide +revert

  theorem zeta_order_eq_256 : orderOf ζ = 256 := by
    apply (orderOf_eq_iff (by decide)).mpr
    constructor
    · exact zeta_256_eq
    · exact zeta_pow_m_neq_one

  lemma diff_mod (m k : Nat) (h₀ : m ≥ k) (h₁ : (m - k) % 256 = 0) : (m % 256) = (k % 256) := by
    grind

  lemma zeta_pow_sub_zeta_pow_ne_zero (m k : Nat) (h : (m % 256) ≠ (k % 256)) : ζ^m - ζ^k ≠ 0 := by
    intro hyp
    by_cases h₀ : k ≤ m
    · have hmk : k + (m - k) = m := by grind
      have hzpow : ζ ^ ((m-k) % 256) ≠ 1 := by
        apply zeta_pow_m_neq_one (((m-k) % 256))
        · grind
        · by_contra h0
          simp at h0
          apply diff_mod at h0
          contradiction
          apply h₀
      have : ζ^k * (ζ^(m-k) - 1) = 0 := by
        calc
          ζ^k * (ζ^(m-k) - 1 ) = ζ^(k + (m-k)) - ζ^k := by ring
          _ = ζ^m - ζ^k := by rw [hmk]
          _ = 0 := by exact hyp
      have hzk : ζ^k ≠ 0 := by apply pow_ne_zero k zeta_ne_zero
      apply eq_zero_or_eq_zero_of_mul_eq_zero at this
      cases this with
      | inl ll => contradiction
      | inr rr =>
        apply sub_eq_zero.mp at rr
        rw [← pow_mod_orderOf ζ (m-k)] at rr
        simp [Zq.zeta_order_eq_256] at rr
        contradiction
    · simp at h₀
      have hkm : m + (k - m ) = k := by grind
      have hzpow : ζ ^ ((k-m) % 256) ≠ 1 := by
        apply zeta_pow_m_neq_one (((k-m) % 256))
        · grind
        · by_contra h0
          simp at h0
          apply diff_mod at h0 ; symm at h0
          contradiction
          apply (le_of_lt h₀)
      have : ζ^m * (1-ζ^(k-m)) = 0 := by
        calc
          ζ^m * (1-ζ^(k-m)) = ζ^m - ζ^(m + (k-m)) := by ring
          _ = ζ^m - ζ^k := by rw [hkm]
          _ = 0 := by exact hyp
      have hzm : ζ^m ≠ 0 := by apply pow_ne_zero m zeta_ne_zero
      apply eq_zero_or_eq_zero_of_mul_eq_zero at this
      cases this with
      | inl ll => contradiction
      | inr rr =>
        apply sub_eq_zero.mp at rr
        rw [← pow_mod_orderOf ζ (k-m)] at rr
        simp [Zq.zeta_order_eq_256] at rr ; symm at rr
        contradiction

  theorem zeta_pow_sub_zeta_pow_isUnit (m k : Nat) (h : (m % 256) ≠ (k % 256)) : IsUnit (ζ^m - ζ^k) := by
    have q_isPrime_fact : Fact (Nat.Prime q) := ⟨q_isPrime⟩
    have : (ζ^m - ζ^k) ^ (q-1) = 1 := by
      apply ZMod.pow_card_sub_one_eq_one (zeta_pow_sub_zeta_pow_ne_zero m k h)
    apply IsUnit.of_pow_eq_one this
    decide


end Zq

/- The BitRev₇ function from the ML-KEM specification [Section 4.3]
     "Define BitRev₇(𝑖) to be the integer represented by bit-reversing
      the unsigned 7-bit value that corresponds to the input integer
      𝑖 ∈ {0,…,127}." -/
def BitRev₇ (i : Fin 128) : Fin 128 :=
  let ibits := BitVec.ofNat 7 i.val
  (ibits.reverse).toFin

#eval BitRev₇ 1

example : BitRev₇ 3  = 96 := by rfl
example : BitRev₇ 0  = 0 := by rfl
example : BitRev₇ 127 = 127 := by rfl
example : BitRev₇ 1  = 64 := by rfl
example : BitRev₇ 2  = 32 := by rfl

/- Define a more general version that allows the bitsize b of the
    integers to be any positive integer (instead of only b=7). -/
def BitRev (b : ℕ) (i : Fin (2 ^ b)) : Fin (2 ^ b) :=
  let ibits := BitVec.ofNat b i.val
  (ibits.reverse).toFin

#eval BitRev 7 2

example : BitRev 0 0 = 0 := by rfl
example : BitRev 3 1 = 4 := by rfl
example : BitRev 7 0 = 0 := by rfl
example : BitRev 7 2 = 32 := by rfl

lemma BitRev_equal : ∀ i : Fin 128, BitRev₇ i = BitRev 7 i := by
  intro i; rfl

lemma BitVec_reverse_reverse_eq {n : ℕ} (v : BitVec n) : v.reverse.reverse = v := by sorry
  -- This seems to exist in Mathlib v4.25: Use the below?
  -- simpa using BitVec.reverse_reverse v

lemma BitRev_inv (b : ℕ) (i : Fin (2 ^ b)) : BitRev b (BitRev b i) = i := by
  simp [BitRev, BitVec_reverse_reverse_eq]

lemma BitRev₇_inv (i : Fin 128) : BitRev₇ (BitRev₇ i) = i := by
  decide +revert

lemma BitRev_inj (b : ℕ) (i j : Fin (2 ^ b)) (hij : i ≠ j) : BitRev b i ≠ BitRev b j := by
  intro h
  have h' : BitRev b (BitRev b i) = BitRev b (BitRev b j) := congr_arg (BitRev b) h
  rw [BitRev_inv, BitRev_inv] at h'
  exact hij h'

/-- For natural numbers n and m < 2^b, if they differ only in the least significant bit,
    then their BitVec representations differ only in bit 0. -/
lemma BitVec_ofNat_double_vs_double_plus_one (b : ℕ) (i : ℕ) (hi : 2 * i < 2 ^ b) (hi2 : 2 * i + 1 < 2 ^ b)
    (j : Nat) (hj : 0 < j) (hjb : j < b) :
  (BitVec.ofNat b (2 * i)).getLsbD j = (BitVec.ofNat b (2 * i + 1)).getLsbD j := by
  rw [BitVec.getLsbD, BitVec.getLsbD, BitVec.ofNat, BitVec.ofNat]
  show (⟨(2 * i) % 2 ^ b, by omega⟩ : Fin (2 ^ b)).val.testBit j =
        (⟨(2 * i + 1) % 2 ^ b, by omega⟩ : Fin (2 ^ b)).val.testBit j
  rw [Fin.val_mk, Fin.val_mk, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi2]
  cases j with
  | zero => omega
  | succ j' =>
    rw [Nat.testBit_succ, Nat.testBit_succ]
    have h1 : 2 * i / 2 = i := Nat.mul_div_cancel_left i (by omega : 0 < 2)
    have h2 : (2 * i + 1) / 2 = i := by omega
    rw [h1, h2]

lemma BitVec_ofNat_double_vs_double_plus_one_reverse (b : ℕ) (i : ℕ) (hi : 2 * i < 2 ^ b) (hi2 : 2 * i + 1 < 2 ^ b)
    (j : Nat) (hjb : j < (b-1)) :
  (BitVec.ofNat b (2 * i)).reverse.getLsbD j = (BitVec.ofNat b (2 * i + 1)).reverse.getLsbD j := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
  have : j < b := by grind
  simp only [this, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
  simp only [this, decide_true, Bool.true_and]
  apply BitVec_ofNat_double_vs_double_plus_one
  apply hi ; apply hi2 ; grind ; grind

lemma BitVec_ofNat_double_lsb (b : ℕ) (i : ℕ) (hi : 2 * i < 2 ^ b) :
  (BitVec.ofNat b (2 * i)).getLsbD 0 = false := by
  rw [BitVec.getLsbD, BitVec.ofNat]
  show (⟨(2 * i) % 2 ^ b, by omega⟩ : Fin (2 ^ b)).val.testBit 0 = false
  rw [Fin.val_mk, Nat.mod_eq_of_lt hi, Nat.testBit_zero]
  simp [Nat.mul_mod_right]

lemma BitVec_ofNat_double_reverse_msb (b : ℕ) (i : ℕ) (hb : b > 0) (hi : 2 * i < 2 ^ b) :
  (BitVec.ofNat b (2 * i)).reverse.getLsbD (b-1) = false := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
  simp [hb]
  apply BitVec_ofNat_double_lsb
  exact hi

lemma BitVec_ofNat_double_plus_one_lsb (b : ℕ) (i : ℕ) (hi : 2 * i + 1 < 2 ^ b) :
  (BitVec.ofNat b (2 * i + 1)).getLsbD 0 = true := by
  rw [BitVec.getLsbD, BitVec.ofNat]
  show (⟨(2 * i + 1) % 2 ^ b, by omega⟩ : Fin (2 ^ b)).val.testBit 0 = true
  rw [Fin.val_mk, Nat.mod_eq_of_lt hi, Nat.testBit_zero]
  simp [Nat.add_mod, Nat.mul_mod_right]

lemma BitVec_ofNat_double_plus_one_reverse_msb (b : ℕ) (i : ℕ) (hb : b > 0) (hi : 2 * i + 1 < 2 ^ b) :
  (BitVec.ofNat b (2 * i + 1)).reverse.getLsbD (b-1) = true := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
  simp [hb]
  apply BitVec_ofNat_double_plus_one_lsb
  exact hi

/-- Bit reversal of an odd number (2i+1) equals bit reversal of the even number (2i)
    plus 2^(b-1), where b is the number of bits. This is because adding 1 sets the LSB,
    which becomes the MSB after reversal.
-/
lemma BitRev_odd_from_even (b : ℕ) (hb : b > 0) (i : Fin (2 ^ (b - 1))) :
  let i₂ : Fin (2 ^ b) := ⟨2 * i.val + 1, by
    have : 2 ^ b = 2 * 2 ^ (b - 1) := by cases b; omega; simp [Nat.pow_succ]; ring
    omega⟩
  let i₁ : Fin (2 ^ b) := ⟨2 * i.val, by
    have : 2 ^ b = 2 * 2 ^ (b - 1) := by cases b; omega; simp [Nat.pow_succ]; ring
    omega⟩
  (BitRev b i₂).val = (BitRev b i₁).val + 2^(b - 1) := by
  intro i₂ i₁
  simp only [i₁, i₂, BitRev]

  have h2ip1_lt : 2 * i.val + 1 < 2 ^ b := by
    have : 2 ^ b = 2 * 2 ^ (b - 1) := by cases b; omega; simp [Nat.pow_succ]; ring
    omega
  have h2i_lt : 2 * i.val < 2 ^ b := by
    have : 2 ^ b = 2 * 2 ^ (b - 1) := by cases b; omega; simp [Nat.pow_succ]; ring
    omega

  show (BitVec.ofNat b (2 * i.val + 1)).reverse.toNat =
        (BitVec.ofNat b (2 * i.val)).reverse.toNat + 2^(b - 1)

  have h_pow_lt : 2 ^ (b - 1) < 2 ^ b := by
    cases b; omega
    apply Nat.pow_lt_pow_succ; linarith

  have h_pos : 0 < 2 ^ (b - 1) := Nat.pow_pos (by omega : 0 < 2)

  -- Prove BitVec equality, then take toNat of both sides
  suffices h : (BitVec.ofNat b (2 * i.val + 1)).reverse =
                (BitVec.ofNat b (2 * i.val)).reverse + (BitVec.twoPow b (b - 1)) by
    -- Extract numeric equality from BitVec equality
    have : (BitVec.ofNat b (2 * i.val + 1)).reverse.toNat =
            ((BitVec.ofNat b (2 * i.val)).reverse + (BitVec.twoPow b (b - 1))).toNat := by
      rw [h]
    rw [this, BitVec.toNat_add, BitVec.toNat_twoPow]
    -- Show no overflow in the addition
    have h_small : (BitVec.ofNat b (2 * i.val)).reverse.toNat < 2 ^ (b - 1) := by
      apply BitVec.toNat_lt_of_msb_false
      rw [BitVec.msb_eq_getLsbD_last]
      exact BitVec_ofNat_double_reverse_msb b i.val hb h2i_lt
    have h_no_overflow : (BitVec.ofNat b (2 * i.val)).reverse.toNat + 2 ^ (b - 1) < 2 ^ b := by
      have : 2 ^ b = 2 * 2 ^ (b - 1) := by cases b; omega; simp [Nat.pow_succ]; ring
      omega
    rw [Nat.mod_eq_of_lt h_pow_lt, Nat.mod_eq_of_lt h_no_overflow]

  -- Prove the BitVec equality bit-by-bit
  apply BitVec.eq_of_getLsbD_eq
  intro j hj

  by_cases hjb : j = b - 1
  · -- At MSB (bit b-1): LHS is true, RHS is false + true
    subst hjb
    rw [BitVec_ofNat_double_plus_one_reverse_msb b i.val hb h2ip1_lt]
    rw [BitVec.getLsbD_add]
    · rw [BitVec_ofNat_double_reverse_msb b i.val hb h2i_lt]
      rw [BitVec.getLsbD_twoPow]
      simp [hb]
      simp [BitVec.carry]
      rw [Nat.mod_eq_of_lt h_pow_lt]
      simp [Nat.mod_self]
      exact Nat.mod_lt _ h_pos
    · omega
  · -- At other bits: both sides have the same bit (twoPow contributes 0)
    have hjb_lt : j < b - 1 := by omega
    rw [BitVec.getLsbD_add]
    · have h_twoPow_zero : (BitVec.twoPow b (b - 1)).getLsbD j = false := by
        rw [BitVec.getLsbD_twoPow]
        simp
        omega
      rw [h_twoPow_zero]
      have h_carry_zero : BitVec.carry j (BitVec.ofNat b (2 * i.val)).reverse (BitVec.twoPow b (b - 1)) false = false := by
        simp [BitVec.carry]
        rw [Nat.mod_eq_of_lt h_pow_lt]
        have h_pos : 0 < 2 ^ j := Nat.pow_pos (by omega : 0 < 2)
        have h_dvd : 2 ^ j ∣ 2 ^ (b - 1) := by
          apply Nat.pow_dvd_pow; omega
        rw [Nat.dvd_iff_mod_eq_zero.mp h_dvd]
        simp
        exact Nat.mod_lt _ h_pos
      rw [h_carry_zero]
      simp
      exact (BitVec_ofNat_double_vs_double_plus_one_reverse b i.val h2i_lt h2ip1_lt j hjb_lt).symm
    · omega

lemma BitRev_even_from_half (b : ℕ) (hb : b > 0) (i : Fin (2 ^ (b - 1))) :
  let i₁ : Fin (2 ^ b) := ⟨2 * i.val, by
    have : 2 ^ b = 2 * 2 ^ (b - 1) := by cases b; omega; simp [Nat.pow_succ]; ring
    omega⟩
  (BitRev b i₁).val = (BitRev (b-1) i).val := by
  intro i₁
  simp only [i₁, BitRev]

  -- Show toNat values are equal
  show (BitVec.ofNat b (2 * i.val)).reverse.toNat = (BitVec.ofNat (b-1) i.val).reverse.toNat

  have h2i_lt : 2 * i.val < 2 ^ b := by
    have : 2 ^ b = 2 * 2 ^ (b - 1) := by cases b; omega; simp [Nat.pow_succ]; ring
    omega

  -- After reversing, the LSB becomes MSB
  have h_msb : (BitVec.ofNat b (2 * i.val)).reverse.getLsbD (b - 1) = false :=
    BitVec_ofNat_double_reverse_msb b i.val hb h2i_lt

  -- Since MSB is 0, the b-bit reversed value fits in b-1 bits
  have h_bound : (BitVec.ofNat b (2 * i.val)).reverse.toNat < 2 ^ (b - 1) := by
    apply BitVec.toNat_lt_of_msb_false
    rw [BitVec.msb_eq_getLsbD_last]
    exact h_msb

  -- Since the reversed value fits in b-1 bits, converting via ofNat preserves the value
  have h_preserve : (BitVec.ofNat b (2 * i.val)).reverse.toNat =
       (BitVec.ofNat (b-1) ((BitVec.ofNat b (2 * i.val)).reverse.toNat)).toNat := by
    rw [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h_bound]

  -- Now we need to show that this equals (BitVec.ofNat (b-1) i.val).reverse.toNat
  have h_i : (BitVec.ofNat (b-1) ((BitVec.ofNat b (2 * i.val)).reverse.toNat)).toNat
    = (BitVec.ofNat (b-1) i.val).reverse.toNat := by
    -- Prove bit vector equality, then toNat equality follows
    suffices h : (BitVec.ofNat (b-1) ((BitVec.ofNat b (2 * i.val)).reverse.toNat)) =
                 (BitVec.ofNat (b-1) i.val).reverse by
      rw [h]

    -- Prove bit-by-bit equality
    apply BitVec.eq_of_getLsbD_eq
    intro j hj

    -- LHS: get bit j of ofNat (b-1) (reverse of 2*i in b bits)
    rw [BitVec.getLsbD_ofNat]
    -- RHS: get bit j of reverse of i in (b-1) bits
    rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
    simp [hj]
    -- Both sides should extract the same bit from the reversed (b-1) bit representation
    rw [← BitVec.getLsbD, BitVec.getLsbD_reverse, BitVec.getMsbD]
    simp [Nat.lt_of_lt_pred hj]
    -- Show: (BitVec.ofNat b (2*i)).getLsbD (b-1-j) = i.testBit (b-2-j)
    rw [BitVec.getLsbD_ofNat]
    have hj_bound : b - 1 - j < b := by omega
    simp [hj_bound]
    -- Key: testBit of 2*i at (b-1-j) equals testBit of i at (b-2-j)
    -- because 2*i shifts left, so bit k of i becomes bit k+1 of 2*i
    have h_shift : b - 1 - j = (b - 1 - 1 - j) + 1 := by omega
    rw [h_shift, Nat.testBit_succ]
    have h_div : 2 * i.val / 2 = i.val := Nat.mul_div_cancel_left i.val (by omega : 0 < 2)
    rw [h_div]

  -- Combine the results
  calc (BitVec.ofNat b (2 * i.val)).reverse.toNat
      = (BitVec.ofNat (b - 1) (BitVec.ofNat b (2 * i.val)).reverse.toNat).toNat := h_preserve
    _ = (BitVec.ofNat (b - 1) i.val).reverse.toNat := h_i


open Polynomial

@[reducible]
def Poly := Zq[X]

namespace Poly

  noncomputable
  def xn (n : Nat) : Zq[X] := monomial n Zq.one

  noncomputable def one : Zq[X] := monomial 0 1
  noncomputable def ζ : Zq[X] := monomial 0 Zq.ζ
  noncomputable def ζ_inv : Zq[X]:= monomial 0 (ZMod.inv q Zq.ζ)

  theorem zeta_128_eq : ζ ^ 128 = - one := by
    simp only [one, ζ, monomial_pow]
    simp [Zq.zeta_128_eq]

  theorem zeta_exp_p_128_eq (x : ℕ) : ζ ^ (x + 128) = - ζ ^ x := by
    simp [pow_add ζ x 128, zeta_128_eq, one]

  /- # The Kyber ring Rq -/
  def Rq := Zq[X] ⧸ Ideal.span {xn 256 + 1}


  /- The NTT is a ring isomorphism from Rq to the product Tq of 128 rings defined by
     quadratic polynomials X^2 - ζ^k for some integer k. It works through repeated
     decomposition of the involved rings according to the following scheme.

     Rq = Z[X] ⧸ (X^256 + 1) = Z[X] ⧸ (X^256 - ζ^128)
        ≅ Z[X] ⧸ (X^128 - ζ^64) × Z[X] ⧸ (X^128 + ζ^64) = Z[X] ⧸ (X^128 - ζ^64) × Z[X] ⧸ (X^128 - ζ^192)
        ≅ Z[X] ⧸ (X^64 - ζ^32) × Z[X] ⧸ (X^64 - ζ^160) × Z[X] ⧸ (X^64 - ζ^96) × Z[X] ⧸ (X^64 - ζ^224)
        ≅ ...

    Continuing this way leads to a scheme of exponents (x_exp, ζ_exp) for the
    polynomials X^x_exp - ζ^ζ_exp as follows:

    l=0: (256, 128)
    l=1: (128, 64), (128, 192)
    l=2: (64, 32), (64, 160), (64, 96), (64, 224)
    l=3: (32, 16), (32, 144), (32, 80), (32, 208), ...
    l=4: (16, 8), (16, 136), ...
    l=5: (8, 4), (8, 132), ...
    l=6: (4, 2), (4, 130), ...
    l=7: (2, 1), (2, 129), ...

    The second number, ζ_exp, if numbered with i = 0, ..., i = 2 ^ l - 1 in the order defined
    by the above decomposition is given by 2^(7-l) + (BitRev l i) * 2^(8-l).

    This means that the ring for (l, i) decomposes as the product of the rings for (l+1, 2i) and (l+1, 2i+1).
  -/

  /- Define the polynomial that defines the i-th quotiont ring
     at level l down from Rq:
     fq (l, i) = X^x_exp - ζ^ζ_exp
               = X^(2^(8-l)) - ζ^(2^(7-l) + (BitRev l i)*2^(8-l)) -/

  --@[simp]
  def x_exp (l : Fin 8) : ℕ := 2 ^ (8 - l.val)
  --@[simp]
  def ζ_exp (l : Fin 8) (i : Fin (2 ^ l.val)) : ℕ :=
    (x_exp l)/2 + (BitRev l i).val * (x_exp l)

  lemma ζ_exp_ubound (l : Fin 8) (i : Fin (2 ^ l.val)) : ζ_exp l i < 2 ^ 8 := by
    decide +revert

  lemma ζ_exp_not_eq (l : Fin 8) (i j : Fin (2 ^ l.val)) (hij : i ≠ j) : ζ_exp l i ≠ ζ_exp l j := by
      intro h
      simp only [ζ_exp] at h
      have h_mul : (BitRev l i).val * x_exp l = (BitRev l j).val * x_exp l := by
        have : x_exp l / 2 + (BitRev l i).val * x_exp l = x_exp l / 2 + (BitRev l j).val * x_exp l := h
        linarith
      have hx_pos : 0 < x_exp l := by unfold x_exp; apply Nat.two_pow_pos
      have h_bitrev : (BitRev l i).val = (BitRev l j).val := Nat.eq_of_mul_eq_mul_right hx_pos h_mul
      have : BitRev l i = BitRev l j := Fin.ext h_bitrev
      exact BitRev_inj l i j hij this

  lemma ζ_exp_not_eq_mod (l : Fin 8) (i j : Fin (2 ^ l.val)) (hij : i ≠ j) : (ζ_exp l i) % 256 ≠ (ζ_exp l j) % 256 := by
      have hi : ζ_exp l i < 256 := by convert ζ_exp_ubound l i
      have hj : ζ_exp l j < 256 := by convert ζ_exp_ubound l j
      rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]; exact ζ_exp_not_eq l i j hij

  lemma ζ_exp_diff_IsUnit (l : Fin 8) (i j : Fin (2 ^ l.val)) (hij : i ≠ j) : IsUnit (Zq.ζ^(ζ_exp l i) - Zq.ζ^(ζ_exp l j)) := by
      apply Zq.zeta_pow_sub_zeta_pow_isUnit
      exact ζ_exp_not_eq_mod l i j hij


  noncomputable
  def fq (l : Fin 8) (i : Fin (2 ^ l.val)) :=
    xn (x_exp l) - ζ ^ (ζ_exp l i)

  example : fq 0 0 = xn 256 + 1 := by
    simp [fq, ζ_exp, x_exp, BitRev, zeta_128_eq, one]
  example : fq 7 0 = xn 2 - ζ := by
    simp [fq, ζ_exp, x_exp, BitRev, BitVec.reverse]
  example : fq 7 2 = xn 2 - ζ ^ 65 := by
    simp [fq, ζ_exp, x_exp, BitRev, BitVec.reverse, BitVec.msb]

  /- Define the i-th quotient ring at level l down from Rq defined by (fq l i). -/
  def Sq (l : Fin 8) (i : Fin (2 ^ l.val)) :=
    Zq[X] ⧸ Ideal.span {fq l i}

  example : Sq 0 0 = (Zq[X] ⧸ Ideal.span {xn 256 + 1}) := by
    simp [Sq, fq, ζ_exp, x_exp, zeta_128_eq, one]
  example : Sq 1 1 = (Zq[X] ⧸ Ideal.span {xn 128 - ζ^192}) := by
    simp [Sq, fq, ζ_exp, x_exp, BitRev, BitVec.reverse, BitVec.msb]
  example : Sq 7 1 = (Zq[X] ⧸ Ideal.span {xn 2 - ζ^129}) := by
    simp [Sq, fq, ζ_exp, x_exp, BitRev, BitVec.reverse, BitVec.msb]


  /- # Two polynomials (fq l i) and (fq l j) are coprime if i ≠ j.-/
  theorem fq_coprime (l : Fin 8) (i j : Fin (2 ^ l.val)) (hij : i ≠ j): IsCoprime (fq l i) (fq l j) := by
    rw [fq, fq, IsCoprime]
    use -monomial 0 (Ring.inverse (Zq.ζ^ζ_exp l i - Zq.ζ^ζ_exp l j))
    use monomial 0 (Ring.inverse (Zq.ζ^ζ_exp l i - Zq.ζ^ζ_exp l j))
    rw [mul_sub, mul_sub, xn]
    ring_nf
    rw [← mul_sub_left_distrib, ζ]
    simp
    rw [← C.map_pow (Zq.ζ) (ζ_exp l i), ← C.map_pow (Zq.ζ) (ζ_exp l j), ← C.map_sub (Zq.ζ^(ζ_exp l i)), ← C.map_mul, ← C.map_one]
    rw [ZMod.inv_mul_of_unit (Zq.ζ ^ ζ_exp l i - Zq.ζ ^ ζ_exp l j) (ζ_exp_diff_IsUnit l i j hij)]


  lemma fq_mul (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) :
    let l' : Fin 8 := ⟨l.val + 1, by omega⟩
    let i₁ : Fin (2 ^ l'.val) := ⟨2 * i.val, by simp [l']; omega⟩
    let i₂ : Fin (2 ^ l'.val) := ⟨2 * i.val + 1, by simp [l']; omega⟩
    fq l' i₁ * fq l' i₂ = fq l i := by
    intro l' i₁ i₂
    simp only [fq, x_exp, ζ_exp, i₁, i₂, l']
    -- Need to show: (X^(2^(8-l'-1)) - ζ^k1) * (X^(2^(8-l'-1)) - ζ^k2) = X^(2^(8-l)) - ζ^k
    -- where the exponents relate via BitRev_odd_from_even
    have hl'_pos : l.val + 1 > 0 := by omega
    have i_bound : i.val < 2 ^ l.val := i.isLt
    have i_fin : i = (⟨i.val, i_bound⟩ : Fin (2 ^ l.val)) := by rfl
    have h_bitrev := BitRev_odd_from_even (l.val + 1) hl'_pos (⟨i.val, by omega⟩ : Fin (2 ^ l.val))
    simp at h_bitrev
    -- Use h_bitrev to relate the zeta exponents, then simplify algebraically
    rw [h_bitrev]
    rw [add_mul, ← pow_add]
    have h_arith : l.val + (8 - (l.val + 1)) = 7 := by omega
    rw [h_arith]
    simp [pow_add, zeta_128_eq, one]
    ring_nf
    simp [xn, ζ, Zq.one]
    have h_pow : 2 ^ (7 - l.val) * 2 = 2 ^ (8 - l.val) := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    have h_pow_half : 2 ^ (8 - l.val) / 2 = 2 ^ (7 - l.val) := by
       omega
    have : 2 ∣ (2 ^ (7 - l.val)) := by
      have : 1 ≤ 7 - l.val := by omega
      exact Nat.pow_dvd_pow 2 this
    rw [h_pow, h_pow_half, Nat.div_mul_cancel this]
    ring_nf
    congr 1
    -- Show: BitRev(l+1, 2*i) * 2^(7-l) * 2 = BitRev(l, i) * 2^(8-l)
    rw [mul_assoc, h_pow]
    congr 3
    -- Now need: BitRev(l+1, i*2).val = BitRev(l, i).val
    have h_even := BitRev_even_from_half (l.val + 1) hl'_pos i
    simp at h_even
    convert h_even using 2
    ring_nf


  lemma fq_mul_four (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 6) :
    let l'' : Fin 8 := ⟨l.val + 2, by omega⟩
    let i₁ : Fin (2 ^ l''.val) := ⟨4 * i.val, by grind⟩
    let i₂ : Fin (2 ^ l''.val) := ⟨4 * i.val + 1, by grind⟩
    let i₃ : Fin (2 ^ l''.val) := ⟨4 * i.val + 2, by grind⟩
    let i₄ : Fin (2 ^ l''.val) := ⟨4 * i.val + 3, by grind⟩
    fq l'' i₁ * fq l'' i₂ * fq l'' i₃ * fq l'' i₄ = fq l i := by
    intro l'' i₁ i₂ i₃ i₄

    -- Apply fq_mul twice: first at level l+1, then at level l
    have hl' : l.val < 7 := by omega
    have hl'' : l.val + 1 < 7 := by omega

    let l' : Fin 8 := ⟨l.val + 1, by omega⟩
    let i₁' : Fin (2 ^ l'.val) := ⟨2 * i.val, by simp [l']; omega⟩
    let i₂' : Fin (2 ^ l'.val) := ⟨2 * i.val + 1, by simp [l']; omega⟩

    -- First pair: fq l'' i₁ * fq l'' i₂ = fq l' i₁'
    have eq₁₂ : fq l'' i₁ * fq l'' i₂ = fq l' i₁' := by
      have h := fq_mul l' i₁' hl''
      convert h using 2
      · ext; simp [i₁, i₁', l', l'']; ring_nf
      · ext; simp [i₂, i₁', l', l'']; ring_nf

    -- Second pair: fq l'' i₃ * fq l'' i₄ = fq l' i₂'
    have eq₃₄ : fq l'' i₃ * fq l'' i₄ = fq l' i₂' := by
      have h := fq_mul l' i₂' hl''
      convert h using 2
      · ext; simp [i₃, i₂', l', l'']; ring_nf
      · ext; simp [i₄, i₂', l', l'']; ring_nf

    -- Combine: fq l' i₁' * fq l' i₂' = fq l i
    have eq_final : fq l' i₁' * fq l' i₂' = fq l i := fq_mul l i hl'

    -- Put it all together
    calc fq l'' i₁ * fq l'' i₂ * fq l'' i₃ * fq l'' i₄
        = (fq l'' i₁ * fq l'' i₂) * (fq l'' i₃ * fq l'' i₄) := by ring
      _ = fq l' i₁' * fq l' i₂' := by rw [eq₁₂, eq₃₄]
      _ = fq l i := eq_final


  noncomputable
  def crt_Sq_1 (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) :
    let l' : Fin 8 := ⟨l.val + 1, by omega⟩
    let i₁ : Fin (2 ^ l'.val) := ⟨2 * i.val, by grind⟩
    let i₂ : Fin (2 ^ l'.val) := ⟨2 * i.val + 1, by grind⟩
    let I₁ := Ideal.span {fq l' i₁}
    let I₂ := Ideal.span {fq l' i₂}
    Zq[X] ⧸ Ideal.span {fq l i} ≃+* (Zq[X] ⧸ I₁) × (Zq[X] ⧸ I₂) :=
  by
    intro l' i₁ i₂ I₁ I₂
    have coprime : IsCoprime I₁ I₂ := by
      rw [Ideal.isCoprime_span_singleton_iff]
      apply fq_coprime
      simp [i₁, i₂]
    have prod :
      I₁ * I₂ =
       Ideal.span {fq l i} := by
      rw [Ideal.span_singleton_mul_span_singleton]
      rw [fq_mul l i hl]
    rw [← prod]
    apply Ideal.quotientMulEquivQuotientProd I₁ I₂ coprime


  noncomputable
  def crt_Sq_2 (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 6) :
    -- Decomposition at two levels down: l'' = l + 2
    let l'' : Fin 8 := ⟨l.val + 2, by omega⟩
    -- The ring indices are 4i, 4i+1, 4i+2, 4i+3.
    let idx : Fin 4 → Fin (2 ^ l''.val) := fun k => ⟨4 * i.val + k.val, by grind⟩
    -- Define the polynomial for each ring.
    let f : Fin 4 → Zq[X] := fun k => fq l'' (idx k)
    -- And the corresponding ideals.
    let I := fun k => Ideal.span {f k}

    Zq[X] ⧸ Ideal.span {fq l i} ≃+* (Zq[X] ⧸ I 0) × (Zq[X] ⧸ I 1) × (Zq[X] ⧸ I 2) × (Zq[X] ⧸ I 3) :=
  by
    intro l'' idx f I

    -- Show they are pairwise coprime
    have coprime : Pairwise (fun j k => IsCoprime (I j) (I k)) := by
      intro j k hjk
      fin_cases j <;> fin_cases k <;> simp [I] at hjk ⊢
      all_goals {
        rw [Ideal.isCoprime_span_singleton_iff]
        apply fq_coprime
        simp [idx]
      }

    -- Show their infimum is the original ideal
    have inf_eq : iInf I = Ideal.span {fq l i} := by
      rw [Ideal.iInf_span_singleton]
      · have prod_eq : ∏ k : Fin 4, f k = fq l i := by
          calc ∏ k : Fin 4, f k
              = f 0 * f 1 * f 2 * f 3 := by simp only [Fin.prod_univ_four]
            _ = fq l'' (idx 0) * fq l'' (idx 1) * fq l'' (idx 2) * fq l'' (idx 3) := rfl
            _ = fq l i := fq_mul_four l i hl
        rw [prod_eq]
      · intro j k hjk
        have h : IsCoprime (I j) (I k) := coprime hjk
        simp only [I] at h
        rwa [Ideal.isCoprime_span_singleton_iff] at h

    -- Apply the Chinese Remainder Theorem
    rw [← inf_eq]
    let crt := Ideal.quotientInfRingEquivPiQuotient I coprime
    -- Convert from (i : Fin 4) → R ⧸ I i to product type
    refine crt.trans ?_
    let piToProduct : ((i : Fin 4) → Zq[X] ⧸ I i) ≃+* _ := {
      toFun := fun f => (f 0, f 1, f 2, f 3)
      invFun := fun (a, b, c, d) => fun i =>
        match i with
        | 0 => a
        | 1 => b
        | 2 => c
        | 3 => d
      left_inv := fun f => by
        ext i
        fin_cases i <;> rfl
      right_inv := fun (a, b, c, d) => by
        simp
      map_mul' := fun f g => rfl
      map_add' := fun f g => rfl
    }
    exact piToProduct

end Poly
