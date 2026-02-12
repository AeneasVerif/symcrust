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
import Aeneas
import Symcrust.Spec

open Aeneas.Notations.SRRange  -- allows the `[0:256:2*len]` notations to desugar to an `SRRange` instead of a `Std.Range`
open Aeneas.Notations.DivRange -- activates the `[start : >stop : /divisor]` notation
open Aeneas.Notations.MulRange -- activates the `[start : <stop : *mul]` notation
open Symcrust.Spec.Notations -- activates custom get_elem_tactic and bounds-checking theorems


set_option maxRecDepth 2500
set_option maxHeartbeats 400000
--set_option diagnostics true


/- The Kyber prime q and root of unity ζ -/

@[simp]
def Q : Nat := 3329

@[simp]
lemma Q_isPrime : Nat.Prime Q := by native_decide
instance : Fact (Nat.Prime Q) := ⟨Q_isPrime⟩

lemma Q_nonzero : Q ≠ 0 := by trivial
lemma Q_minus_one_fact : (Q - 1) = 2^8 * 13 := rfl

example : (Q-2)*Q = 2^16 * 169 - 1 := by simp

def zeta := 17
theorem zeta_coprime : Nat.Coprime zeta Q := by rfl


/-- Finite ring Zq --/

@[reducible]
def Zq := ZMod Q
lemma Zq_cyclic : IsCyclic Zqˣ := by
  apply ZMod.isCyclic_units_prime Q_isPrime

namespace Zq
  open scoped ZMod
  open Nat

  def mk_elem (n : Fin q) : Zq := n
  def one : Zq := 1
  def ζ : Zq := zeta

  lemma zeta_ne_one : ζ ≠ 1 := by trivial
  lemma zeta_ne_zero : ζ ≠ 0 := by trivial

  lemma zeta_pow_ne_zero (k : ℕ) : ζ^k ≠ 0 := by
    apply pow_ne_zero k zeta_ne_zero

  theorem zeta_isUnit : IsUnit ζ := by
    rw [isUnit_iff_ne_zero]
    exact zeta_ne_zero

  lemma zeta_mul_inv_zeta_eq_one : ζ * ζ⁻¹ = 1 := by
    apply div_self zeta_ne_zero

  lemma inv_zeta_mul_zeta_eq_one : ζ⁻¹ * ζ = 1 := by
    rw [mul_comm]
    exact zeta_mul_inv_zeta_eq_one

  lemma inv_zeta_val : ζ⁻¹ = 1175 := by
    exact ZMod.inv_eq_of_mul_eq_one Q ζ 1175 (by rfl : ζ * 1175 = 1)

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

  lemma zeta_pow_sub_zeta_pow_ne_zero (m k : Nat) (h : (m % 256) ≠ (k % 256)) : ζ^m - ζ^k ≠ 0 := by
    intro heq
    have heq : ζ^m = ζ^k := sub_eq_zero.mp heq
    rw [← pow_mod_orderOf ζ m, ← pow_mod_orderOf ζ k, zeta_order_eq_256] at heq
    exact h (pow_injOn_Iio_orderOf
      (show m % 256 < orderOf ζ by rw [zeta_order_eq_256]; exact Nat.mod_lt m (by omega))
      (show k % 256 < orderOf ζ by rw [zeta_order_eq_256]; exact Nat.mod_lt k (by omega))
      heq)

  theorem zeta_pow_sub_zeta_pow_isUnit (m k : Nat) (h : (m % 256) ≠ (k % 256)) : IsUnit (ζ^m - ζ^k) := by
    have : (ζ^m - ζ^k) ^ (Q-1) = 1 := by
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

example : BitRev 0 0 = 0 := by rfl
example : BitRev 3 1 = 4 := by rfl
example : BitRev 7 0 = 0 := by rfl
example : BitRev 7 2 = 32 := by rfl

lemma BitRev_equal : ∀ i : Fin 128, BitRev₇ i = BitRev 7 i := by
  intro i; rfl

/- BitRev is its own inverse. -/
lemma BitRev_inv (b : ℕ) (i : Fin (2 ^ b)) : BitRev b (BitRev b i) = i := by
  simp [BitRev]

/- BitRev is injective. -/
lemma BitRev_inj (b : ℕ) (i j : Fin (2 ^ b)) (hij : i ≠ j) : BitRev b i ≠ BitRev b j :=
  fun h => hij (by rw [← BitRev_inv b i, ← BitRev_inv b j, h])


/- Properties relating Bit Vectors of consecutive integers. -/
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
    -- Extract numeric equality from BitVec equality
    have : (BitVec.ofNat b (2 * i.val + 1)).reverse.toNat =
            ((BitVec.ofNat b (2 * i.val)).reverse + (BitVec.twoPow b (b - 1))).toNat := by rw [h]
    rw [this, BitVec.toNat_add, BitVec.toNat_twoPow]
    -- Show no overflow in the addition
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
  · -- At MSB (bit b-1): LHS is true, RHS is false + true
    subst hjb
    rw [BitVec_ofNat_double_plus_one_reverse_msb b i.val hb]
    rw [BitVec.getLsbD_add]
    · rw [BitVec_ofNat_double_reverse_msb b i.val hb]
      rw [BitVec.getLsbD_twoPow]
      simp [hb]
      simp [BitVec.carry]
      rw [← Nat.pow_mod, Nat.mod_eq_of_lt h_pow_lt]
      simp [Nat.mod_self]
      exact Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < 2))
    · omega
  · -- At other bits: both sides have the same bit (twoPow contributes 0)
    have hjb_lt : j < b - 1 := by omega
    rw [BitVec.getLsbD_add]
    · have h_twoPow_zero : (BitVec.twoPow b (b - 1)).getLsbD j = false := by
        rw [BitVec.getLsbD_twoPow]
        grind
      have h_carry_zero : BitVec.carry j (BitVec.ofNat b (2 * i.val)).reverse (BitVec.twoPow b (b - 1)) false = false := by
        simp [BitVec.carry]
        rw [← Nat.pow_mod, Nat.mod_eq_of_lt h_pow_lt]
        rw [Nat.dvd_iff_mod_eq_zero.mp (by apply Nat.pow_dvd_pow; omega : 2 ^ j ∣ 2 ^ (b - 1))]
        exact Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < 2))
      simp only [h_twoPow_zero, h_carry_zero, Bool.xor_false]
      exact (BitVec_ofNat_double_vs_double_plus_one_reverse b i.val j hjb_lt).symm
    · omega

/-- Bit reversal (of width b) of an even b-bit number (2*i) is the same as bit
    reversal (of width b-1) of half the number (i). This is as integers,
    i.e. ignoring the zero in the most significant bit. -/
lemma BitRev_even_from_half (b : ℕ) (hb : b > 0) (i : Fin (2 ^ (b - 1))) :
  let i₁ : Fin (2 ^ b) := ⟨2 * i.val, by rw [← mul_pow_sub_one (Nat.pos_iff_ne_zero.mp hb)]; omega⟩
  (BitRev b i₁).val = (BitRev (b-1) i).val := by
  intro i₁
  simp only [i₁, BitRev]

  -- Show toNat values are equal
  show (BitVec.ofNat b (2 * i.val)).reverse.toNat = (BitVec.ofNat (b-1) i.val).reverse.toNat

  -- Since MSB is 0, the b-bit reversed value fits in b-1 bits
  have h_bound : (BitVec.ofNat b (2 * i.val)).reverse.toNat < 2 ^ (b - 1) := by
    apply BitVec.toNat_lt_of_msb_false
    rw [BitVec.msb_eq_getLsbD_last]
    exact BitVec_ofNat_double_reverse_msb b i.val hb

  -- Since the reversed value fits in b-1 bits, converting via ofNat preserves the value
  have h_preserve : (BitVec.ofNat b (2 * i.val)).reverse.toNat =
       (BitVec.ofNat (b-1) ((BitVec.ofNat b (2 * i.val)).reverse.toNat)).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_bound]

  -- This equals (BitVec.ofNat (b-1) i.val).reverse.toNat
  have h_i : (BitVec.ofNat (b-1) ((BitVec.ofNat b (2 * i.val)).reverse.toNat)).toNat
    = (BitVec.ofNat (b-1) i.val).reverse.toNat := by
    -- Prove bit vector equality, then toNat equality follows
    suffices h : (BitVec.ofNat (b-1) ((BitVec.ofNat b (2 * i.val)).reverse.toNat)) =
                 (BitVec.ofNat (b-1) i.val).reverse by rw [h]
    -- Prove bit-by-bit equality
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h_div : 2 * i.val / 2 = i.val := Nat.mul_div_cancel_left i.val (by omega : 0 < 2)
    -- LHS: get bit j of ofNat (b-1) (reverse of 2*i in b bits)
    -- RHS: get bit j of reverse of i in (b-1) bits
    rw [BitVec.getLsbD_ofNat, BitVec.getLsbD_reverse, BitVec.getMsbD]
    rw [← BitVec.getLsbD, BitVec.getLsbD_reverse, BitVec.getMsbD, BitVec.getLsbD_ofNat]
    simp [Nat.lt_of_lt_pred hj]
    grind
  -- Combine the results
  grind

open Polynomial

@[reducible]
def Poly := Zq[X]

namespace Poly

  noncomputable
  def xn (n : Nat) : Zq[X] := monomial n Zq.one

  noncomputable def one : Zq[X] := monomial 0 1
  noncomputable def ζ : Zq[X] := monomial 0 Zq.ζ
  theorem zeta_128_eq : ζ ^ 128 = - one := by
    simp only [one, ζ, monomial_pow]
    simp [Zq.zeta_128_eq]

  /- # The Kyber ring Rq -/
  abbrev Rq := Zq[X] ⧸ Ideal.span {xn 256 + 1}


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

  /- Below, we define the polynomial that defines the i-th quotiont ring
     at level l down from Rq:
     fq (l, i) = X^x_exp - ζ^ζ_exp
               = X^(2^(8-l)) - ζ^(2^(7-l) + (BitRev l i)*2^(8-l)) -/

  /- First the exponents. -/
  def x_exp (l : Fin 8) : ℕ := 2 ^ (8 - l.val)
  def ζ_exp (l : Fin 8) (i : Fin (2 ^ l.val)) : ℕ :=
    (x_exp l)/2 + (BitRev l i).val * (x_exp l)

  /- x_exp is positive. -/
  lemma x_exp_pos (l : Fin 8) : 0 < x_exp l := by unfold x_exp; apply Nat.two_pow_pos

  /- Some properties of ζ_exp. -/
  lemma ζ_exp_ubound (l : Fin 8) (i : Fin (2 ^ l.val)) : ζ_exp l i < 2 ^ 8 := by
    decide +revert

  lemma ζ_exp_not_eq (l : Fin 8) (i j : Fin (2 ^ l.val)) (hij : i ≠ j) : ζ_exp l i ≠ ζ_exp l j := by
      intro h; simp only [ζ_exp] at h
      exact BitRev_inj l i j hij (Fin.ext (Nat.eq_of_mul_eq_mul_right (x_exp_pos l) (by omega)))

  lemma ζ_exp_not_eq_mod (l : Fin 8) (i j : Fin (2 ^ l.val)) (hij : i ≠ j) : (ζ_exp l i) % 256 ≠ (ζ_exp l j) % 256 := by
      have hi : ζ_exp l i < 256 := ζ_exp_ubound l i
      have hj : ζ_exp l j < 256 := ζ_exp_ubound l j
      rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      exact ζ_exp_not_eq l i j hij

  lemma ζ_exp_diff_IsUnit (l : Fin 8) (i j : Fin (2 ^ l.val)) (hij : i ≠ j) : IsUnit (Zq.ζ^(ζ_exp l i) - Zq.ζ^(ζ_exp l j)) := by
      apply Zq.zeta_pow_sub_zeta_pow_isUnit
      exact ζ_exp_not_eq_mod l i j hij

  /- The polynomial
     fq (l, i) = X^x_exp - ζ^ζ_exp
               = X^(2^(8-l)) - ζ^(2^(7-l) + (BitRev l i)*2^(8-l)). -/
  noncomputable
  def fq (l : Fin 8) (i : Fin (2 ^ l.val)) :=
    xn (x_exp l) - ζ ^ (ζ_exp l i)

  example : fq 0 0 = xn 256 + 1 := by
    simp [fq, ζ_exp, x_exp, BitRev, zeta_128_eq, one]
  example : fq 7 0 = xn 2 - ζ := by
    simp [fq, ζ_exp, x_exp, BitRev, BitVec.reverse]
  example : fq 7 1 = xn 2 - ζ ^ 129 := by
    simp [fq, ζ_exp, x_exp, BitRev, BitVec.reverse]
  example : fq 7 1 = xn 2 + ζ := by
    simp [fq, ζ_exp, x_exp, BitRev, BitVec.reverse]
    conv_lhs => rw [show (129 : ℕ) = 128 + 1 from rfl, pow_add, zeta_128_eq]
    simp [one]
  example : fq 7 2 = xn 2 - ζ ^ 65 := by
    simp [fq, ζ_exp, x_exp, BitRev, BitVec.reverse, BitVec.msb]

  /- Define the ideal generated by fq. -/
  noncomputable
  abbrev Iq (l : Fin 8) (i : Fin (2 ^ l.val)) :=
    Ideal.span {fq l i}

  /- The quotient ring defined by Iq. -/
  abbrev Sq (l : Fin 8) (i : Fin (2 ^ l.val)) := Zq[X] ⧸ Iq l i

  example : Rq = Sq 0 0 := by
    rw [Sq, Rq, Iq, fq, ζ_exp, x_exp]
    simp [zeta_128_eq, one]
  example : (Sq 7 0) = (Zq[X] ⧸ Ideal.span {X^2 - ζ}) := by
    unfold Sq Iq fq ζ_exp x_exp xn BitRev
    norm_num
    conv_lhs => rw [show (↑(7 : Fin 8) : ℕ) = 7 by rfl]
    have h2 : (0#7).reverse.toNat = 0 := by native_decide
    simp only [h2, Zq.one, X]
    norm_num


  /- Two polynomials (fq l i) and (fq l j) are coprime if i ≠ j.-/
  theorem fq_coprime (l : Fin 8) (i j : Fin (2 ^ l.val)) (hij : i ≠ j): IsCoprime (fq l i) (fq l j) := by
    let d := Zq.ζ^ζ_exp l i - Zq.ζ^ζ_exp l j
    have hd : IsUnit d := ζ_exp_diff_IsUnit l i j hij
    simp only [fq, IsCoprime]
    use -C d⁻¹, C d⁻¹
    simp only [xn, ζ, monomial_zero_left, Zq.one]
    ring_nf
    rw [← C_pow, ← C_pow, ← C_mul, ← C_mul, ← C_sub,
        show d⁻¹ * Zq.ζ ^ ζ_exp l i - d⁻¹ * Zq.ζ ^ ζ_exp l j = d⁻¹ * d by ring,
        ZMod.inv_mul_of_unit d hd, C_1]

  /- Then the corresponding ideals are also coprime. -/
  lemma Iq_coprime (l : Fin 8) (i j : Fin (2 ^ l.val)) (hij : i ≠ j): IsCoprime (Iq l i) (Iq l j) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr (fq_coprime _ _ _ hij)

  /- Multiplying two fq polynomials at the same level l+1 and with consecutive indices
     2i and 2i+1 yields the polynomial at level l with index i.
     In other words an fq polynomial at level l factors into two consecutively indexed fq polynomials
     at the level l+1, one further down, provided it is not in the bottom (highest numbered) level. -/
  lemma fq_mul (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) :
    fq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩ *
    fq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩ = fq l i := by

    /- Some properties of l.val. -/
    have h_arith : l.val + (8 - (l.val + 1)) = 7 := by omega
    have h_pow : 2 ^ (7 - l.val) * 2 = 2 ^ (8 - l.val) := by rw [← Nat.pow_succ]; congr 1; omega
    have h_pow_half : 2 ^ (8 - l.val) / 2 = 2 ^ (7 - l.val) := by omega
    have h_div : 2 ∣ 2 ^ (7 - l.val) := Nat.pow_dvd_pow 2 (by omega : 1 ≤ 7 - l.val)

    /- Use the result expressing BitRev of the odd number in terms of the even one. -/
    have h_bitrev := BitRev_odd_from_even (l.val + 1) (by omega) (⟨i.val, by omega⟩ : Fin (2 ^ l.val))
    simp at h_bitrev
    /- And the one expressing BitRev of the double. -/
    have h_even := BitRev_even_from_half (l.val + 1) (by omega) i
    simp at h_even

    simp only [fq, x_exp, ζ_exp, h_bitrev, add_mul, ← pow_add, h_arith]
    simp [pow_add, zeta_128_eq, one]
    ring_nf
    simp [xn, ζ, Zq.one, h_pow, h_pow_half, Nat.div_mul_cancel h_div]
    ring_nf
    congr 1
    rw [mul_assoc, h_pow]
    congr 3
    convert h_even using 2
    ring_nf

  /- Generalization of fq_mul: A polynomial at level l and position/index i in the tree
     factors as a product of the corresponding consecutive 2^k polynomials at level l+k
    (if they exist in the tree). -/
  lemma fq_mul_k (l : Fin 8) (i : Fin (2 ^ l.val)) (k : Fin 8) (hlk : k.val < 8 - l.val) :
    let idx : Fin (2 ^ k.val) → Fin (2 ^ (l.val + k.val)) := fun j => ⟨2 ^ k.val * i.val + j.val, by
      calc 2 ^ k.val * i.val + j.val
          < 2 ^ k.val * i.val + 2 ^ k.val := Nat.add_lt_add_left j.isLt _
        _ = 2 ^ k.val * (i.val + 1) := by ring
        _ ≤ 2 ^ k.val * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
        _ = 2 ^ (l.val + k.val) := by rw [← Nat.pow_add, Nat.add_comm]⟩
    ∏ j : Fin (2 ^ k.val), fq ⟨l.val + k.val, by omega⟩ (idx j) = fq l i := by
    intro idx
    induction k using Fin.inductionOn generalizing l i with
    | zero =>
      -- Base case: k = 0, product of 1 element
      simp only [Fin.val_zero, Nat.pow_zero, Fintype.prod_subsingleton _ (0 : Fin 1)]
      simp [idx]
    | succ k' ih =>
      -- Inductive case: split the product into pairs using fq_mul
      -- ∏ j : Fin (2^(k'+1)), fq ⟨l.val + k.val, _⟩ (idx j)
      --   = ∏ j : Fin (2^k'), (fq ⟨l.val + k.val, _⟩ (idx (2j)) * fq ⟨l.val + k.val, _⟩ (idx (2j+1)))
      --   = ∏ j : Fin (2^k'), fq l' (idx' j)   -- by fq_mul
      --   = fq l i                              -- by induction hypothesis
      simp only [Fin.val_succ, Nat.pow_succ] at idx

      -- Note: k'.succ.val = k'.val + 1 and k'.castSucc.val = k'.val
      have hk'_eq : k'.castSucc.val = k'.val := rfl
      have hk : k'.succ.val = k'.val + 1 := rfl
      -- Define intermediate level l' = l + k' (one level below l+k)
      let l' : Fin 8 := ⟨l.val + k'.val, by omega⟩
      have hl' : l'.val < 7 := by simp only [l']; omega

      -- Define intermediate index function for level l'
      let idx' : Fin (2 ^ k'.val) → Fin (2 ^ l'.val) := fun j => ⟨2 ^ k'.val * i.val + j.val, by
        simp only [l']
        calc 2 ^ k'.val * i.val + j.val
            < 2 ^ k'.val * i.val + 2 ^ k'.val := Nat.add_lt_add_left j.isLt _
          _ = 2 ^ k'.val * (i.val + 1) := by ring
          _ ≤ 2 ^ k'.val * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
          _ = 2 ^ (l.val + k'.val) := by rw [← Nat.pow_add, Nat.add_comm]⟩

      -- Rewrite ∏ j : Fin (2^k' * 2), ... as ∏ j : Fin (2^k'), (... * ...)
      have h_prod_eq : ∏ j : Fin (2 ^ k'.val * 2), fq ⟨l.val + k'.succ.val, by omega⟩ (idx j)
                     = ∏ j : Fin (2 ^ k'.val), (fq ⟨l.val + k'.succ.val, by omega⟩ (idx ⟨2*j.val, by omega⟩) * fq ⟨l.val + k'.succ.val, by omega⟩ (idx ⟨2*j.val+1, by omega⟩)) := by
        -- Define the pairing: Fin (n * 2) ≃ Fin n × Fin 2, where pair (a, b) maps to 2a + b
        let pair : Fin (2 ^ k'.val) × Fin 2 → Fin (2 ^ k'.val * 2) :=
          fun ⟨a, b⟩ => ⟨2 * a.val + b.val, by have ha := a.isLt; have hb := b.isLt; omega⟩
        have hpair_bij : Function.Bijective pair := by
          constructor
          · intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h ; grind
          · intro j
            use (⟨j.val / 2, by have := j.isLt; omega⟩, ⟨j.val % 2, Nat.mod_lt _ (by omega)⟩)
            apply Fin.ext ; grind
        -- Rewrite RHS as product over Fin n × Fin 2
        have hrhs : ∏ j : Fin (2 ^ k'.val), (fq ⟨l.val + k'.succ.val, by omega⟩ (idx ⟨2*j.val, by omega⟩) * fq ⟨l.val + k'.succ.val, by omega⟩ (idx ⟨2*j.val+1, by omega⟩))
                  = ∏ p : Fin (2 ^ k'.val) × Fin 2, fq ⟨l.val + k'.succ.val, by omega⟩ (idx (pair p)) := by
          trans ∏ a : Fin (2 ^ k'.val), ∏ b : Fin 2, fq ⟨l.val + k'.succ.val, by omega⟩ (idx (pair (a, b)))
          · congr 1; ext a; rw [Fin.prod_univ_two]; rfl
          · rw [← Finset.prod_product']; rfl
        rw [hrhs]
        -- Now use bijection
        exact (Fintype.prod_bijective pair hpair_bij _ _ (fun _ => rfl)).symm

      -- Each pair equals fq l' (idx' j) by fq_mul
      have h_pairs : ∀ j : Fin (2 ^ k'.val),
          fq ⟨l.val + k'.succ.val, by omega⟩ (idx ⟨2*j.val, by omega⟩) * fq ⟨l.val + k'.succ.val, by omega⟩ (idx ⟨2*j.val+1, by omega⟩) = fq l' (idx' j) := by
        intro j
        -- Apply fq_mul at level l' with index idx' j
        have hmul := fq_mul l' (idx' j) hl'
        -- hmul : fq (l'+1) ⟨2*(idx' j).val, _⟩ * fq (l'+1) ⟨2*(idx' j).val+1, _⟩ = fq l' (idx' j)
        -- We need to show:
        --   l'' = l' + 1
        --   idx ⟨2j, _⟩ = ⟨2(idx' j).val, _⟩
        --   idx ⟨2j+1, _⟩ = ⟨2(idx' j).val+1, _⟩
        convert hmul using 3 <;> ext <;> simp only [idx, idx', Fin.val_succ, Nat.pow_succ] <;> ring

      -- Apply induction hypothesis
      have hlk' : k'.castSucc.val < 8 - l.val := by omega
      have h_ih := ih l i hlk'

      -- Final assembly
      grind

  /-- A polynomial `fq` at a descendant node divides the polynomial `fq` at an ancestor node
      in the NTT decomposition tree. At level `l` and index `i`, the polynomial `fq l i` factors
      as a product of `2^k` polynomials at level `l+k`. The `j`-th descendant divides `fq l i`. -/
  lemma fq_dvd_ancestor (l : Fin 8) (i : Fin (2 ^ l.val)) (k : ℕ)
      (hk : k < 8 - l.val) (j : Fin (2 ^ k)) :
      fq ⟨l.val + k, by omega⟩ ⟨2 ^ k * i.val + j.val, by
        calc 2 ^ k * i.val + j.val
          < 2 ^ k * i.val + 2 ^ k := Nat.add_lt_add_left j.isLt _
          _ = 2 ^ k * (i.val + 1) := by ring
          _ ≤ 2 ^ k * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
          _ = 2 ^ (l.val + k) := by rw [← Nat.pow_add]; ring_nf⟩ ∣ fq l i := by
    have h := fq_mul_k l i ⟨k, by omega⟩ hk
    simp only [Fin.val_mk] at h
    rw [← h]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

  /-- The ideal at an ancestor level is contained in the ideal at any descendant level.
      This follows from the fact that the descendant's generator divides the ancestor's. -/
  lemma Iq_le_descendant (l : Fin 8) (i : Fin (2 ^ l.val)) (k : ℕ)
      (hk : k < 8 - l.val) (j : Fin (2 ^ k)) :
      Iq l i ≤ Iq ⟨l.val + k, by omega⟩ ⟨2 ^ k * i.val + j.val, by
        calc 2 ^ k * i.val + j.val
          < 2 ^ k * i.val + 2 ^ k := Nat.add_lt_add_left j.isLt _
          _ = 2 ^ k * (i.val + 1) := by ring
          _ ≤ 2 ^ k * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
          _ = 2 ^ (l.val + k) := by rw [← Nat.pow_add]; ring_nf⟩ :=
    Ideal.span_singleton_le_span_singleton.mpr (fq_dvd_ancestor l i k hk j)

  /-- The quotient ring at level l and index i is isomorphic
      to a product of 2 quotient rings at level l+1. -/
  noncomputable
  def crtIq (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) :
    Sq l i ≃+*
      (Sq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩) ×
      (Sq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩) := by
    let I₁ := Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩
    let I₂ := Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩

    have coprime : IsCoprime (fq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩)
                             (fq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩) :=
      fq_coprime _ _ _ (by simp)

    have prod : I₁ * I₂ = Iq l i := by
      simp only [I₁, I₂, Iq, Ideal.span_singleton_mul_span_singleton, fq_mul l i hl]

    -- Instead of rw, use explicit composition: Iq l i ≃ I₁ * I₂ ≃ I₁ × I₂
    exact (Ideal.quotEquivOfEq prod).symm.trans <|
      Ideal.quotientMulEquivQuotientProd I₁ I₂
        ((Ideal.isCoprime_span_singleton_iff _ _).mpr coprime)

  lemma crtIq_fst (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) (f : Zq[X]) :
    (crtIq l i hl (Ideal.Quotient.mk (Iq l i) f)).1 =
      Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩) f := by
    simp [crtIq, RingEquiv.trans_apply, Ideal.quotientMulEquivQuotientProd_fst]

  lemma crtIq_snd (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) (f : Zq[X]) :
    (crtIq l i hl (Ideal.Quotient.mk (Iq l i) f)).2 =
      Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩) f := by
    simp [crtIq, RingEquiv.trans_apply, Ideal.quotientMulEquivQuotientProd_snd]

  /-- General version: The quotient ring at level l and index i is isomorphic
      to a product of 2^k quotient rings at level l+k. -/
  noncomputable
  def crtIq_k (l : Fin 8) (i : Fin (2 ^ l.val)) (k : Fin 8) (hlk : k.val < 8 - l.val) :
    -- The ring indices are 2^k * i, 2^k * i + 1, ..., 2^k * i + 2^k - 1
    let idx : Fin (2 ^ k.val) → Fin (2 ^ (l.val + k.val)) := fun j => ⟨2 ^ k.val * i.val + j.val, by
      calc 2 ^ k.val * i.val + j.val
          < 2 ^ k.val * i.val + 2 ^ k.val := Nat.add_lt_add_left j.isLt _
        _ = 2 ^ k.val * (i.val + 1) := by ring
        _ ≤ 2 ^ k.val * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
        _ = 2 ^ (l.val + k.val) := by rw [← Nat.pow_add, Nat.add_comm]⟩

    Sq l i ≃+* Π j : Fin (2 ^ k.val), Sq ⟨l.val + k.val, by omega⟩ (idx j) :=
  by
    intro idx

    -- Define I as shorthand for Iq ⟨l.val + k.val, by omega⟩ ∘ idx
    let I : Fin (2 ^ k.val) → Ideal Zq[X] := fun j => Iq ⟨l.val + k.val, by omega⟩ (idx j)

    -- Show they are pairwise coprime
    have coprime : Pairwise (fun j₁ j₂ => IsCoprime (I j₁) (I j₂)) := by
      intro j₁ j₂ hjk
      simp only [I]
      apply Iq_coprime
      simp only [idx, Ne, Fin.mk.injEq]
      omega

    -- Show their infimum is the original ideal
    have inf_eq : iInf I = Iq l i := by
      simp only [I, Iq]
      rw [Ideal.iInf_span_singleton]
      · have prod_eq : ∏ j : Fin (2 ^ k.val), fq ⟨l.val + k.val, by omega⟩ (idx j) = fq l i := by
          have h := fq_mul_k l i k hlk
          exact h
        rw [prod_eq]
      · intro j₁ j₂ hjk
        have h : IsCoprime (I j₁) (I j₂) := coprime hjk
        simp only [I, Iq] at h
        rwa [Ideal.isCoprime_span_singleton_iff] at h

    -- Compose the quotient equivalence from inf_eq with the CRT isomorphism
    -- This avoids the rw that creates Eq.mpr
    let e1 : Zq[X] ⧸ Iq l i ≃+* Zq[X] ⧸ iInf I :=
      Ideal.quotientEquiv (Iq l i) (iInf I) (RingEquiv.refl _) (by simp [inf_eq])
    let e2 : Zq[X] ⧸ iInf I ≃+* (Π j : Fin (2 ^ k.val), Zq[X] ⧸ I j) :=
      Ideal.quotientInfRingEquivPiQuotient I coprime
    exact e1.trans e2


  /-====================================================================-/

  /-- Split a polynomial into low and high halves at position n.
      Given f ∈ Zq[X] with degree ≤ 2n-1, splits it as f = low + X^n * high,
      where low has degree < n and high has degree < n. -/
  noncomputable
  def poly_split (n : ℕ) (f : Zq[X]) (_hf : f.degree ≤ (2*n - 1 : ℕ)) : Zq[X] × Zq[X] :=
    let low := Finset.sum (Finset.range n) (fun i => Polynomial.coeff f i • Polynomial.X ^ i)
    let high := Finset.sum (Finset.range n) (fun i => Polynomial.coeff f (i + n) • Polynomial.X ^ i)
    (low, high)

  /-- The result of poly_split satisfies f = low + X^n * high. -/
  lemma poly_split_eq (n : ℕ) (hn : 0 < n) (f : Zq[X]) (hf : f.degree ≤ (2*n - 1 : ℕ)) :
    let (low, high) := poly_split n f hf
    f = low + Polynomial.X ^ n * high := by
    -- Prove by showing coefficients are equal
    simp only [poly_split]
    ext i
    simp only [Polynomial.coeff_add, Finset.mul_sum, Polynomial.finset_sum_coeff,
               Polynomial.coeff_smul, Polynomial.coeff_X_pow, Polynomial.coeff_mul]
    -- Case split on whether i < n
    by_cases hi : i < n
    · -- Case i < n: only low part contributes
      simp [hi]
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun p hp => ?_
      split_ifs with h1 h2 <;> try rfl
      simp [Finset.mem_antidiagonal] at hp
      omega
    · -- Case i >= n: potentially high part contributes
      simp [hi]
      push_neg at hi
      by_cases hi2 : i - n < n
      · -- i - n < n, so high contributes at position i - n
        rw [Finset.sum_eq_single (i - n)]
        · rw [Finset.sum_eq_single (n, i - n)]
          · grind
          · grind
          · intro h; exfalso; apply h; simp [Finset.mem_antidiagonal, Nat.add_sub_cancel' hi]
        · intro x hx hxne; apply Finset.sum_eq_zero; intro p hp; split_ifs with h1 h2 <;> try rfl
          simp [Finset.mem_antidiagonal] at hp; omega
        · grind
      · -- i - n >= n, so i >= 2n and coeff is 0
        push_neg at hi2
        have hi_large : 2 * n ≤ i := by omega
        have hfi : f.coeff i = 0 := by
          apply Polynomial.coeff_eq_zero_of_degree_lt
          calc f.degree ≤ (2*n - 1 : ℕ) := hf
               _ < (2*n : WithBot ℕ) := by exact Nat.cast_lt.mpr (by omega : 2*n - 1 < 2*n)
               _ ≤ i := by exact Nat.cast_le.mpr hi_large
        rw [hfi]; symm; refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun p hp => ?_
        split_ifs with h1 h2 <;> (simp [Finset.mem_antidiagonal] at hp; grind)

  /-- Both parts of poly_split have degree < n -/
  lemma poly_split_degree_lt {n : ℕ} (hn : n ≠ 0) (f : Zq[X])
      (hf : f.degree ≤ (2 * n - 1 : ℕ)) :
      (poly_split n f hf).1.degree < n ∧ (poly_split n f hf).2.degree < n := by
    have aux : ∀ (g : ℕ → Zq),
        (∑ i ∈ Finset.range n, g i • X ^ i : Zq[X]).degree < n := by
      intro g
      refine (Polynomial.degree_sum_le _ _).trans_lt ?_
      by_cases he : (Finset.range n).Nonempty
      · have h_bound : (Finset.range n).sup (fun i => (g i • X ^ i : Zq[X]).degree) ≤ (n - 1 : ℕ) := by
          apply Finset.sup_le
          intro i hi
          have : i < n := Finset.mem_range.mp hi
          calc (g i • X ^ i : Zq[X]).degree
            ≤ (X ^ i).degree := Polynomial.degree_smul_le _ _
            _ = i := Polynomial.degree_X_pow i
            _ ≤ (n - 1 : ℕ) := by exact_mod_cast (Nat.lt_iff_le_pred (Nat.pos_of_ne_zero hn)).mp this
        calc (Finset.range n).sup (fun i => (g i • X ^ i).degree)
          ≤ (n - 1 : ℕ) := h_bound
          _ < n := by exact_mod_cast (Nat.sub_one_lt_of_lt (Nat.pos_of_ne_zero hn))
      · simp [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [poly_split]
    exact ⟨aux (f.coeff ·), aux (fun i => f.coeff (i + n))⟩

  /-- The low part of poly_split has degree < n -/
  lemma poly_split_fst_degree_lt {n : ℕ} (hn : n ≠ 0) (f : Zq[X])
      (hf : f.degree ≤ (2 * n - 1 : ℕ)) :
      (poly_split n f hf).1.degree < n :=
    (poly_split_degree_lt hn f hf).1

  /-- The high part of poly_split has degree < n -/
  lemma poly_split_snd_degree_lt {n : ℕ} (hn : n ≠ 0) (f : Zq[X])
      (hf : f.degree ≤ (2 * n - 1 : ℕ)) :
      (poly_split n f hf).2.degree < n :=
    (poly_split_degree_lt hn f hf).2

  /-- Degree bound for low ± C c * high when both have degree < n -/
  lemma degree_add_sub_C_mul_lt {n : ℕ} (low high : Zq[X]) (c : Zq) (hc : c ≠ 0)
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

  /-- Convert degree < n to degree ≤ n - 1 -/
  lemma degree_lt_to_le_pred {p : Zq[X]} {n : ℕ} (hn : 0 < n) (h : p.degree < n) :
      p.degree ≤ (n - 1 : ℕ) := by
    rcases hp : p.degree with _ | d
    · exact bot_le
    · rw [hp] at h
      exact WithBot.coe_le_coe.mpr (Nat.lt_iff_le_pred hn |>.mp (WithBot.coe_lt_coe.mp h))

  /-- NTT butterfly at level l, splitting at position 2^(7-l).
      Given a polynomial representative f with degree ≤ 2^(8-l) - 1,
      computes (l + ζ^exp * r, l - ζ^exp * r)
      where exp is the appropriate twiddle factor exponent. -/
  noncomputable
  def ntt_butterfly_poly (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) : Zq[X] × Zq[X] :=
    have : 2 * 2 ^ (7 - l.val) = 2 ^ (8 - l.val) := by ring_nf; rw [← Nat.pow_succ]; congr; omega
    have hdeg : f.degree ≤ (2 * (2 ^ (7 - l.val)) - 1 : ℕ) := by rw [this]; exact hf
    let (low, high) := poly_split (2 ^ (7 - l.val)) f hdeg
    let exp := ζ_exp ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩
    let twiddle := Zq.ζ ^ exp
    (low + C twiddle * high, low - C twiddle * high)

  /-- Degree bounds on the two components of the NTT butterfly. -/
  lemma ntt_butterfly_poly_degree (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      (ntt_butterfly_poly l i hl f hf).1.degree ≤ (2 ^ (8 - (l.val + 1)) - 1 : ℕ) ∧
      (ntt_butterfly_poly l i hl f hf).2.degree ≤ (2 ^ (8 - (l.val + 1)) - 1 : ℕ) := by
    simp only [ntt_butterfly_poly]
    have eq1 : 2 * 2 ^ (7 - l.val) = 2 ^ (8 - l.val) := by
      ring_nf; rw [← Nat.pow_succ]; congr; omega
    have hdeg : f.degree ≤ (2 * (2 ^ (7 - l.val)) - 1 : ℕ) := by
      calc f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ) := hf
        _ = (2 * 2 ^ (7 - l.val) - 1 : ℕ) := by rw [← eq1]
    have hn : 2 ^ (7 - l.val) ≠ 0 := by positivity
    have hlow := poly_split_fst_degree_lt hn f hdeg
    have hhigh := poly_split_snd_degree_lt hn f hdeg
    have hc : Zq.ζ ^ ζ_exp ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩ ≠ 0 :=
      pow_ne_zero _ Zq.zeta_ne_zero
    have neq : 2 ^ (7 - l.val) = 2 ^ (8 - (l.val + 1)) := by congr 1; omega
    have h_deg_lt := degree_add_sub_C_mul_lt _ _ _ hc hlow hhigh
    exact ⟨degree_lt_to_le_pred (by positivity) (neq ▸ h_deg_lt.1),
           degree_lt_to_le_pred (by positivity) (neq ▸ h_deg_lt.2)⟩

  lemma ntt_butterfly_poly_fst_degree (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      (ntt_butterfly_poly l i hl f hf).1.degree ≤ (2 ^ (8 - (l.val + 1)) - 1 : ℕ) :=
    (ntt_butterfly_poly_degree l i hl f hf).1

  lemma ntt_butterfly_poly_snd_degree (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      (ntt_butterfly_poly l i hl f hf).2.degree ≤ (2 ^ (8 - (l.val + 1)) - 1 : ℕ) :=
    (ntt_butterfly_poly_degree l i hl f hf).2


  /-- NTT butterfly map on a polynomial with bounded degree.
      Given a polynomial f with degree ≤ 2^(8-l) - 1, computes the butterfly transformation
      and returns the pair of quotient ring elements in the child rings. -/
  noncomputable
  def ntt_butterfly (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      (Zq[X] ⧸ Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩) ×
      (Zq[X] ⧸ Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩) :=
    let (p1, p2) := ntt_butterfly_poly l i hl f hf
    (Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩) p1,
     Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩) p2)

  /-- The butterfly operation agrees with the CRT isomorphism.
      This theorem shows that the explicit butterfly computation produces the same result
      as applying the abstract CRT isomorphism to the quotient element. -/
  theorem ntt_butterfly_eq_crt (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      ntt_butterfly l i hl f hf = crtIq l i hl (Ideal.Quotient.mk (Iq l i) f) := by

    let l' : Fin 8 := ⟨l.val + 1, by omega⟩
    let i₁ : Fin (2 ^ l'.val) := ⟨2 * i.val, by simp [l']; omega⟩
    let i₂ : Fin (2 ^ l'.val) := ⟨2 * i.val + 1, by simp [l']; omega⟩
    let I₁ := Iq l' i₁
    let I₂ := Iq l' i₂
    let n := 2 ^ (7 - l.val)
    let exp := ζ_exp l' i₁
    let low : Zq[X] := ∑ i ∈ Finset.range n, f.coeff i • Polynomial.X ^ i
    let high : Zq[X] := ∑ i ∈ Finset.range n, f.coeff (i + n) • Polynomial.X ^ i
    let twiddle := Zq.ζ ^ exp

    -- Use poly_split_eq to get f = low + X^n * high
    have h0 : (l.val + 1) - 1 = l.val := by omega
    have h1 : 8 - l.val = (7 - l.val) + 1 := by omega
    have h2 : 2 ^ (8 - l.val) = 2 * 2 ^ (7 - l.val) := by rw [h1, pow_succ]; omega
    have h3 : 7 - l.val = 8 - (l.val + 1) := by omega
    have h4 : (7 - l.val) + l.val = 7 := by omega
    have h5 : 2 ^ (7 - l.val) * 2 ^ l.val = 128 := by rw [← Nat.pow_add, h4];
    have h6 : C Zq.ζ ^ 128 = C (Zq.ζ ^ 128) := by simp
    have hf' : f.degree ≤ (2 * n - 1 : ℕ) := by
      calc f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ) := hf
        _ = (2 * n - 1 : ℕ) := by rw [h2]
    have split_eq : f = low + Polynomial.X ^ n * high :=
      poly_split_eq n (by simp only [n]; apply Nat.one_le_two_pow) f hf'

    -- Unfold the LHS (butterfly side)
    simp only [ntt_butterfly, ntt_butterfly_poly, poly_split]
    -- The goal is now an equality of pairs
    -- Split into two components: .1 and .2
    ext
    · -- First component
      -- Use the proved lemma to extract the first component of the CRT
      rw [crtIq_fst]
      show Ideal.Quotient.mk I₁ (low + Polynomial.C twiddle * high) =
           Ideal.Quotient.mk I₁ f

      -- Show that X^n ≡ C twiddle (mod I₁) since I₁ = ⟨X^n - ζ^exp⟩
      have Xn_eq_twiddle : Ideal.Quotient.mk I₁ (Polynomial.X ^ n) =
                           Ideal.Quotient.mk I₁ (Polynomial.C twiddle) := by
        simp only [Ideal.Quotient.eq, I₁, Iq, fq, xn, ζ, x_exp, l', i₁, exp, twiddle, n, Zq.one, Ideal.mem_span_singleton]
        use 1
        rw [Polynomial.X_pow_eq_monomial, h3]
        simp

      -- Combine: f = low + X^n * high ≡ low + C twiddle * high (mod I₁)
      symm
      calc Ideal.Quotient.mk I₁ f
        _ = Ideal.Quotient.mk I₁ low + Ideal.Quotient.mk I₁ (Polynomial.X ^ n) * Ideal.Quotient.mk I₁ high := by simp [split_eq, map_add, map_mul]
        _ = Ideal.Quotient.mk I₁ low + Ideal.Quotient.mk I₁ (Polynomial.C twiddle) * Ideal.Quotient.mk I₁ high := by rw [Xn_eq_twiddle]
        _ = Ideal.Quotient.mk I₁ (low + Polynomial.C twiddle * high) := by simp [map_add, map_mul]
    · -- Second component
      -- Use the proved lemma to extract the second component of the CRT
      rw [crtIq_snd]
      show Ideal.Quotient.mk I₂ (low - Polynomial.C twiddle * high) =
           Ideal.Quotient.mk I₂ f

      -- Show that X^n ≡ -C twiddle (mod I₂)
      have Xn_eq_neg_twiddle : Ideal.Quotient.mk I₂ (Polynomial.X ^ n) =
                               Ideal.Quotient.mk I₂ (-Polynomial.C twiddle) := by
        simp only [Ideal.Quotient.eq, I₂, Iq, fq, xn, ζ, x_exp, l', i₁, i₂, exp, twiddle, n, Zq.one, ζ_exp, Ideal.mem_span_singleton]
        use 1
        rw [Polynomial.X_pow_eq_monomial, h3, BitRev_odd_from_even]
        · -- Main goal: show Polynomial equality
          simp [h0, add_mul]
          ring_nf
          simp [h5, h6, Zq.zeta_128_eq]
        · -- Side goal: l + 1 > 0
          omega

      -- Combine: f = low + X^n * high ≡ low - C twiddle * high (mod I₂)
      symm
      calc Ideal.Quotient.mk I₂ f
        _ = Ideal.Quotient.mk I₂ low + Ideal.Quotient.mk I₂ (Polynomial.X ^ n) * Ideal.Quotient.mk I₂ high := by simp [split_eq, map_add, map_mul]
        _ = Ideal.Quotient.mk I₂ low + Ideal.Quotient.mk I₂ (-Polynomial.C twiddle) * Ideal.Quotient.mk I₂ high := by rw [Xn_eq_neg_twiddle]
        _ = Ideal.Quotient.mk I₂ (low - Polynomial.C twiddle * high) := by simp [map_mul]; ring

  /-- The first butterfly component maps to the same quotient class as f in the first child ring. -/
  lemma ntt_butterfly_poly_fst_eq_mod (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7)
      (f : Zq[X]) (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩) (ntt_butterfly_poly l i hl f hf).1 =
      Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩) f := by
    have := congr_arg (·.1) (ntt_butterfly_eq_crt l i hl f hf)
    simp only [ntt_butterfly] at this
    rw [crtIq_fst] at this
    exact this

  /-- The second butterfly component maps to the same quotient class as f in the second child ring. -/
  lemma ntt_butterfly_poly_snd_eq_mod (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7)
      (f : Zq[X]) (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩) (ntt_butterfly_poly l i hl f hf).2 =
      Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩) f := by
    have := congr_arg (·.2) (ntt_butterfly_eq_crt l i hl f hf)
    simp only [ntt_butterfly] at this
    rw [crtIq_snd] at this
    exact this

  /-! ### Generalization to a k-fold recursive application of the butterfly. -/

  /-- Apply NTT butterfly k times, producing 2^k polynomials.
      Given a polynomial f at level l with appropriate degree bound, applies k butterfly
      operations to decompose it into 2^k polynomials. -/
  noncomputable
  def ntt_butterfly_poly_k (l : Fin 8) (i : Fin (2 ^ l.val)) (k : Fin 8)
      (hlk : k.val < 8 - l.val) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      Fin (2 ^ k.val) → Zq[X] :=
    match k with
    | ⟨0, _⟩ =>
      -- Base case: k = 0, return single polynomial
      fun _ => f
    | ⟨k' + 1, hk⟩ =>
      -- Recursive case: apply butterfly once, then recurse on both results
      have hlk' : k' < 8 - l.val := by grind
      have hl : l.val < 7 := by grind
      have hlk'_next : k' < 8 - (l.val + 1) := by grind
      let p1 := (ntt_butterfly_poly l i hl f hf).1
      let p2 := (ntt_butterfly_poly l i hl f hf).2
      -- The butterfly produces components with degree ≤ 2^(8-(l+1)) - 1
      have hf1 : p1.degree ≤ (2 ^ (8 - (l.val + 1)) - 1 : ℕ) :=
        ntt_butterfly_poly_fst_degree l i hl f hf
      have hf2 : p2.degree ≤ (2 ^ (8 - (l.val + 1)) - 1 : ℕ) :=
        ntt_butterfly_poly_snd_degree l i hl f hf
      let rec1 := ntt_butterfly_poly_k ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩
                    ⟨k', by omega⟩ hlk'_next p1 hf1
      let rec2 := ntt_butterfly_poly_k ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩
                    ⟨k', by omega⟩ hlk'_next p2 hf2
      fun j => if h : j.val < 2 ^ k' then
                 rec1 ⟨j.val, by omega⟩
               else
                 rec2 ⟨j.val - 2 ^ k', by
                   have hj : j.val < 2 ^ (k' + 1) := j.prop
                   have hge : 2 ^ k' ≤ j.val := Nat.not_lt.mp h
                   have hpow : 2 ^ (k' + 1) = 2 ^ k' + 2 ^ k' := by ring
                   calc j.val - 2 ^ k' < 2 ^ (k' + 1) - 2 ^ k' := Nat.sub_lt_sub_right hge hj
                     _ = 2 ^ k' := by simp [hpow]⟩


  /-- Apply NTT butterfly k times, producing 2^k quotient ring elements.
      Given a polynomial f at level l with appropriate degree bound, applies k butterfly
      operations to decompose it into 2^k quotient ring elements, one for each child ring.
      Returns an element of the product of all 2^k child quotient rings. -/
  noncomputable
  def ntt_butterfly_k (l : Fin 8) (i : Fin (2 ^ l.val)) (k : Fin 8)
      (hlk : k.val < 8 - l.val) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      (j : Fin (2 ^ k.val)) → Sq ⟨l.val + k.val, by omega⟩ ⟨2 ^ k.val * i.val + j.val, by
        have hj : j.val < 2 ^ k.val := j.prop
        have hi : i.val < 2 ^ l.val := i.prop
        calc 2 ^ k.val * i.val + j.val
          _ < 2 ^ k.val * i.val + 2 ^ k.val := by omega
          _ = (i.val + 1) * 2 ^ k.val := by ring
          _ ≤ 2 ^ l.val * 2 ^ k.val := by apply Nat.mul_le_mul_right; omega
          _ = 2 ^ (l.val + k.val) := by rw [← Nat.pow_add]
      ⟩ :=
    fun j =>
      let poly := ntt_butterfly_poly_k l i k hlk f hf j
      Ideal.Quotient.mk (Iq ⟨l.val + k.val, by omega⟩ ⟨2 ^ k.val * i.val + j.val, by
        have hj : j.val < 2 ^ k.val := j.prop
        have hi : i.val < 2 ^ l.val := i.prop
        calc 2 ^ k.val * i.val + j.val
          _ < 2 ^ k.val * i.val + 2 ^ k.val := by omega
          _ = (i.val + 1) * 2 ^ k.val := by ring
          _ ≤ 2 ^ l.val * 2 ^ k.val := by apply Nat.mul_le_mul_right; omega
          _ = 2 ^ (l.val + k.val) := by rw [← Nat.pow_add]
      ⟩) poly


  /-! ### Helper lemmas for the general theorem below. -/

  /-- `ntt_butterfly_k` is just `mk (ntt_butterfly_poly_k ...)`. This avoids unfolding
      `ntt_butterfly_k` (which contains large `calc` proof terms) in downstream proofs. -/
  lemma ntt_butterfly_k_eq_mk (l : Fin 8) (i : Fin (2 ^ l.val)) (k : Fin 8)
      (hlk : k.val < 8 - l.val) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ))
      (j : Fin (2 ^ k.val)) :
      ntt_butterfly_k l i k hlk f hf j =
        Ideal.Quotient.mk (Iq ⟨l.val + k.val, by omega⟩ ⟨2 ^ k.val * i.val + j.val, by
          have hj : j.val < 2 ^ k.val := j.prop
          have hi : i.val < 2 ^ l.val := i.prop
          calc 2 ^ k.val * i.val + j.val
            _ < 2 ^ k.val * i.val + 2 ^ k.val := by omega
            _ = (i.val + 1) * 2 ^ k.val := by ring
            _ ≤ 2 ^ l.val * 2 ^ k.val := by apply Nat.mul_le_mul_right; omega
            _ = 2 ^ (l.val + k.val) := by rw [← Nat.pow_add]⟩)
          (ntt_butterfly_poly_k l i k hlk f hf j) := by
    rfl

  /-- Two ideals Iq are equal if their level and index Fin values are equal. -/
  lemma Iq_fin_cast (l l' : Fin 8) (i : Fin (2 ^ l.val)) (i' : Fin (2 ^ l'.val))
      (hl : l = l') (hi_val : i.val = i'.val) :
      Iq l i = Iq l' i' := by
    subst hl
    cases i; cases i'
    simp only at hi_val
    subst hi_val
    rfl

  /-- Key lemma: crtIq_k applied to mk f evaluates to mk f in each component.
      This captures the fundamental property of the CRT isomorphism: it maps the quotient
      class of f to the tuple of quotient classes of f in each component ring. -/
  lemma crtIq_k_mk_eval (l : Fin 8) (i : Fin (2 ^ l.val)) (k : Fin 8)
      (hlk : k.val < 8 - l.val) (f : Zq[X]) (j : Fin (2 ^ k.val)) :
      (crtIq_k l i k hlk (Ideal.Quotient.mk (Iq l i) f)) j =
        Ideal.Quotient.mk (Iq ⟨l.val + k.val, by omega⟩
          ⟨2 ^ k.val * i.val + j.val, by
            calc 2 ^ k.val * i.val + j.val
              < 2 ^ k.val * i.val + 2 ^ k.val := Nat.add_lt_add_left j.isLt _
              _ = 2 ^ k.val * (i.val + 1) := by ring
              _ ≤ 2 ^ k.val * 2 ^ l.val := Nat.mul_le_mul_left _ i.isLt
              _ = 2 ^ (l.val + k.val) := by rw [← Nat.pow_add]; ring_nf⟩) f := by
    -- Unfold crtIq_k: it's e1.trans e2 where e1 is quotientEquiv and e2 is quotientInfRingEquivPiQuotient
    simp only [crtIq_k, RingEquiv.trans_apply]
    -- The quotientEquiv just moves f across equal ideals
    -- quotientInfRingEquivPiQuotient maps mk f to (j ↦ mk f) componentwise
    -- Use Ideal.Quotient.eq to show both sides are in the same equivalence class
    apply Ideal.Quotient.eq.mpr
    simp

  /-- Base case: When k=0, crtIq_k is a ring isomorphism to a product over Fin 1.
      For the unique element 0 : Fin 1, since 2^0 * i + 0 = i and l + 0 = l,
      the ideal Iq ⟨l+0, ⟨2^0*i+0⟩⟩ equals Iq l i definitionally (up to proofs).
      This lemma states that evaluating the CRT at index 0 gives back the identity. -/
  lemma crtIq_k_zero_eval (l : Fin 8) (i : Fin (2 ^ l.val)) (hlk : 0 < 8 - l.val)
      (f : Zq[X]) :
      (crtIq_k l i 0 hlk (Ideal.Quotient.mk (Iq l i) f)) (0 : Fin 1) =
        Ideal.Quotient.mk (Iq ⟨l.val + 0, l.isLt⟩ ⟨2^0 * i.val + 0, by norm_num⟩) f := by
    -- Unfold crtIq_k to see the composition
    simp only [crtIq_k]
    -- It's (quotientEquiv ... ≫ quotientInfRingEquivPiQuotient ...) applied to mk f, then evaluated at 0
    -- Use the fact that for Fin 1, the product structure is trivial
    -- Let's work with Ideal.Quotient.eq to show they're equal in the quotient
    apply Ideal.Quotient.eq.mpr
    -- Show RingEquiv.refl f - f ∈ Iq ⟨l+0, ⟨2^0*i+0⟩⟩
    simp [sub_self]


  /-- Reindex an Iq ideal: for the first half (j < 2^k'), the flat index
      `2^(k'+1) * i + j` at level `l + (k'+1)` equals the split index
      `2^k' * (2*i) + j` at level `(l+1) + k'`. -/
  lemma Iq_reindex_fst (l : Fin 8) (i : Fin (2 ^ l.val)) (k' : ℕ)
      (hk : k' + 1 < 8 - l.val) (j : Fin (2 ^ (k' + 1)))
      (hj : j.val < 2 ^ k') :
      Iq ⟨l.val + (k' + 1), by omega⟩ ⟨2^(k'+1) * i.val + j.val, by
            calc 2^(k'+1) * i.val + j.val
              < 2^(k'+1) * i.val + 2^(k'+1) := Nat.add_lt_add_left j.isLt _
              _ = 2^(k'+1) * (i.val + 1) := by ring
              _ ≤ 2^(k'+1) * 2^l.val := Nat.mul_le_mul_left _ i.isLt
              _ = 2^(l.val + (k' + 1)) := by rw [← Nat.pow_add]; ring_nf⟩ =
          Iq ⟨(l.val + 1) + k', by omega⟩ ⟨2^k' * (2 * i.val) + j.val, by
            calc 2^k' * (2 * i.val) + j.val
              < 2^k' * (2 * i.val) + 2^k' := by omega
              _ = 2^k' * (2 * i.val + 1) := by ring
              _ ≤ 2^k' * 2^(l.val + 1) := by apply Nat.mul_le_mul_left; omega
              _ = 2^((l.val + 1) + k') := by rw [← Nat.pow_add]; ring_nf⟩ := by
    apply Iq_fin_cast <;> simp <;> ring

  /-- Reindex an Iq ideal: for the second half (j ≥ 2^k'), the flat index
      `2^(k'+1) * i + j` at level `l + (k'+1)` equals the split index
      `2^k' * (2*i+1) + (j - 2^k')` at level `(l+1) + k'`. -/
  lemma Iq_reindex_snd (l : Fin 8) (i : Fin (2 ^ l.val)) (k' : ℕ)
      (hk : k' + 1 < 8 - l.val) (j : Fin (2 ^ (k' + 1)))
      (hj : 2 ^ k' ≤ j.val) :
      have hj_sub : j.val - 2^k' < 2^k' := by
        have : 2^(k'+1) = 2 * 2^k' := by rw [Nat.pow_succ]; ring
        omega
      Iq ⟨l.val + (k' + 1), by omega⟩ ⟨2^(k'+1) * i.val + j.val, by
            calc 2^(k'+1) * i.val + j.val
              < 2^(k'+1) * i.val + 2^(k'+1) := Nat.add_lt_add_left j.isLt _
              _ = 2^(k'+1) * (i.val + 1) := by ring
              _ ≤ 2^(k'+1) * 2^l.val := Nat.mul_le_mul_left _ i.isLt
              _ = 2^(l.val + (k' + 1)) := by rw [← Nat.pow_add]; ring_nf⟩ =
          Iq ⟨(l.val + 1) + k', by omega⟩ ⟨2^k' * (2 * i.val + 1) + (j.val - 2^k'), by
            calc 2^k' * (2 * i.val + 1) + (j.val - 2^k')
              < 2^k' * (2 * i.val + 1) + 2^k' := by omega
              _ = 2^k' * (2 * i.val + 2) := by ring
              _ ≤ 2^k' * 2^(l.val + 1) := by apply Nat.mul_le_mul_left; omega
              _ = 2^((l.val + 1) + k') := by rw [← Nat.pow_add]; ring_nf⟩ := by
    apply Iq_fin_cast
    · simp; ring
    · simp
      have h2k : 2^(k'+1) = 2 * 2^k' := by rw [Nat.pow_succ]; ring
      simp only [h2k]; zify [hj]; ring


  /-! ### Equation lemmas for ntt_butterfly_poly_k

  These capture the result of unfolding the recursive `ntt_butterfly_poly_k` at successor
  `k'+1` and resolving the `dif` branch. By proving these separately, the main CRT proofs
  avoid inlining the large unfolded term, keeping kernel proof terms small. -/

  /-- Equation lemma: `ntt_butterfly_poly_k` at `k'+1` for `j < 2^k'` equals the recursive
      call on the first butterfly component. -/
  private lemma ntt_butterfly_poly_k_succ_fst (l : Fin 8) (i : Fin (2 ^ l.val))
      (k' : ℕ) (hk : k' + 1 < 8)
      (hlk : k' + 1 < 8 - l.val) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ))
      (hl : l.val < 7) (hlk'_next : k' < 8 - (l.val + 1))
      (j : Fin (2 ^ (k' + 1))) (hj : j.val < 2 ^ k') :
      ntt_butterfly_poly_k l i ⟨k' + 1, hk⟩ hlk f hf j =
        ntt_butterfly_poly_k ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩
          ⟨k', by omega⟩ hlk'_next
          (ntt_butterfly_poly l i hl f hf).1
          (ntt_butterfly_poly_fst_degree l i hl f hf)
          ⟨j.val, by omega⟩ := by
    conv_lhs => unfold ntt_butterfly_poly_k; dsimp only []
    rw [dif_pos hj]

  /-- Equation lemma: `ntt_butterfly_poly_k` at `k'+1` for `¬ j < 2^k'` equals the recursive
      call on the second butterfly component. -/
  private lemma ntt_butterfly_poly_k_succ_snd (l : Fin 8) (i : Fin (2 ^ l.val))
      (k' : ℕ) (hk : k' + 1 < 8)
      (hlk : k' + 1 < 8 - l.val) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ))
      (hl : l.val < 7) (hlk'_next : k' < 8 - (l.val + 1))
      (j : Fin (2 ^ (k' + 1))) (hj : ¬ j.val < 2 ^ k') :
      have hj_sub : j.val - 2^k' < 2^k' := by
        have : 2^(k'+1) = 2 * 2^k' := by rw [Nat.pow_succ]; ring
        omega
      ntt_butterfly_poly_k l i ⟨k' + 1, hk⟩ hlk f hf j =
        ntt_butterfly_poly_k ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩
          ⟨k', by omega⟩ hlk'_next
          (ntt_butterfly_poly l i hl f hf).2
          (ntt_butterfly_poly_snd_degree l i hl f hf)
          ⟨j.val - 2 ^ k', hj_sub⟩ := by
    show ntt_butterfly_poly_k l i ⟨k' + 1, hk⟩ hlk f hf j = _
    conv_lhs => unfold ntt_butterfly_poly_k; dsimp only []
    rw [dif_neg hj]


  /-! ### General CRT theorem -/

  /-- Case 1 of the k-fold CRT theorem: first half (j < 2^k'). -/
  private lemma ntt_butterfly_k_eq_crt_fst (l : Fin 8) (i : Fin (2 ^ l.val))
      (k' : ℕ) (hk : k' + 1 < 8)
      (hlk : k' + 1 < 8 - l.val) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ))
      (hl : l.val < 7) (hlk'_next : k' < 8 - (l.val + 1))
      (j : Fin (2 ^ (k' + 1))) (hj : j.val < 2 ^ k')
      -- Induction hypothesis
      (IH : ntt_butterfly_k ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩
              ⟨k', by omega⟩ hlk'_next
              (ntt_butterfly_poly l i hl f hf).1
              (ntt_butterfly_poly_fst_degree l i hl f hf) =
            crtIq_k ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩
              ⟨k', by omega⟩ hlk'_next
              (Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩)
                (ntt_butterfly_poly l i hl f hf).1)) :
      ntt_butterfly_k l i ⟨k' + 1, hk⟩ hlk f hf j =
        crtIq_k l i ⟨k' + 1, hk⟩ hlk (Ideal.Quotient.mk (Iq l i) f) j := by
    have ideal_eq := Iq_reindex_fst l i k' (by omega) j hj
    -- Prepare IH at the specific index
    have IH_j := congr_fun IH ⟨j.val, by omega⟩
    rw [ntt_butterfly_k_eq_mk, crtIq_k_mk_eval] at IH_j
    -- Unfold LHS and RHS
    rw [crtIq_k_mk_eval, ntt_butterfly_k_eq_mk,
        ntt_butterfly_poly_k_succ_fst l i k' hk hlk f hf hl hlk'_next j hj]
    -- Avoid quotient_mk_ideal_eq transport; decompose membership directly
    apply Ideal.Quotient.eq.mpr
    rw [ideal_eq]
    have hsplit : ∀ (a b c : Zq[X]), a - c = (a - b) + (b - c) := fun a b c => by ring
    rw [hsplit _ (ntt_butterfly_poly l i hl f hf).1 f]
    exact Ideal.add_mem _
      (Ideal.Quotient.eq.mp IH_j)
      (Iq_le_descendant ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩
        k' (by omega) ⟨j.val, hj⟩
        (Ideal.Quotient.eq.mp (ntt_butterfly_poly_fst_eq_mod l i hl f hf)))

  /-- Case 2 of the k-fold CRT theorem: second half (j ≥ 2^k'). -/
  private lemma ntt_butterfly_k_eq_crt_snd (l : Fin 8) (i : Fin (2 ^ l.val))
      (k' : ℕ) (hk : k' + 1 < 8)
      (hlk : k' + 1 < 8 - l.val) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ))
      (hl : l.val < 7) (hlk'_next : k' < 8 - (l.val + 1))
      (j : Fin (2 ^ (k' + 1))) (hj : ¬ j.val < 2 ^ k')
      -- Induction hypothesis
      (IH : ntt_butterfly_k ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩
              ⟨k', by omega⟩ hlk'_next
              (ntt_butterfly_poly l i hl f hf).2
              (ntt_butterfly_poly_snd_degree l i hl f hf) =
            crtIq_k ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩
              ⟨k', by omega⟩ hlk'_next
              (Ideal.Quotient.mk (Iq ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩)
                (ntt_butterfly_poly l i hl f hf).2)) :
      ntt_butterfly_k l i ⟨k' + 1, hk⟩ hlk f hf j =
        crtIq_k l i ⟨k' + 1, hk⟩ hlk (Ideal.Quotient.mk (Iq l i) f) j := by
    have hj' : 2 ^ k' ≤ j.val := Nat.not_lt.mp hj
    have hj_sub : j.val - 2^k' < 2^k' := by
      have : 2^(k'+1) = 2 * 2^k' := by rw [Nat.pow_succ]; ring
      omega
    have ideal_eq := Iq_reindex_snd l i k' (by omega) j hj'
    -- Prepare IH at the specific index
    have IH_j := congr_fun IH ⟨j.val - 2 ^ k', hj_sub⟩
    rw [ntt_butterfly_k_eq_mk, crtIq_k_mk_eval] at IH_j
    -- Unfold LHS and RHS
    rw [crtIq_k_mk_eval, ntt_butterfly_k_eq_mk,
        ntt_butterfly_poly_k_succ_snd l i k' hk hlk f hf hl hlk'_next j hj]
    -- Goal: mk Iq₁ (poly_k ... p2 ... ⟨j-2^k'⟩) = mk Iq₁ f
    -- Avoid quotient_mk_ideal_eq transport; instead decompose membership directly
    apply Ideal.Quotient.eq.mpr
    rw [ideal_eq]
    -- Goal: (poly_k ...) - f ∈ Iq₂
    -- Split: (poly_k - p2) + (p2 - f), both in Iq₂
    have hsplit : ∀ (a b c : Zq[X]), a - c = (a - b) + (b - c) := fun a b c => by ring
    rw [hsplit _ (ntt_butterfly_poly l i hl f hf).2 f]
    exact Ideal.add_mem _
      (Ideal.Quotient.eq.mp IH_j)
      (Iq_le_descendant ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩
        k' (by omega) ⟨j.val - 2 ^ k', hj_sub⟩
        (Ideal.Quotient.eq.mp (ntt_butterfly_poly_snd_eq_mod l i hl f hf)))

  /-- The k-fold butterfly operation agrees with the k-fold CRT isomorphism.
      This theorem shows that applying k recursive butterfly operations produces the same result
      as applying the abstract CRT isomorphism to decompose into 2^k quotient rings. -/
  theorem ntt_butterfly_k_eq_crt (l : Fin 8) (i : Fin (2 ^ l.val)) (k : Fin 8)
      (hlk : k.val < 8 - l.val) (f : Zq[X])
      (hf : f.degree ≤ (2 ^ (8 - l.val) - 1 : ℕ)) :
      ntt_butterfly_k l i k hlk f hf = crtIq_k l i k hlk (Ideal.Quotient.mk (Iq l i) f) := by
    match k with
    | ⟨0, _⟩ =>
      ext j; fin_cases j
      simp only [ntt_butterfly_k, ntt_butterfly_poly_k]
      rw [← crtIq_k_zero_eval]; rfl
    | ⟨k' + 1, hk⟩ =>
      have hlk' : k' + 1 < 8 - l.val := hlk
      have hl : l.val < 7 := by omega
      have hlk'_next : k' < 8 - (l.val + 1) := by omega
      ext j
      by_cases hj : j.val < 2 ^ k'
      · exact ntt_butterfly_k_eq_crt_fst l i k' hk hlk' f hf hl hlk'_next j hj
            (ntt_butterfly_k_eq_crt ⟨l.val + 1, by omega⟩ ⟨2 * i.val, by simp; omega⟩
              ⟨k', by omega⟩ hlk'_next _ _)
      · exact ntt_butterfly_k_eq_crt_snd l i k' hk hlk' f hf hl hlk'_next j hj
            (ntt_butterfly_k_eq_crt ⟨l.val + 1, by omega⟩ ⟨2 * i.val + 1, by simp; omega⟩
              ⟨k', by omega⟩ hlk'_next _ _)


/-! # Algorithm 9 from the ML-KEM specification -/
  def ntt (f : Symcrust.Spec.Polynomial) := Id.run do
    let mut f := f
    let mut i := 1
    for h0: len in [128 : >1 : /= 2] do
      for h1: start in [0 : 256 : 2*len] do
        let zeta : Symcrust.Spec.Zq := Zq.ζ ^ ((BitRev 7 i).val)
        i := i + 1
        for h: j in [start : start+len] do
          let t := zeta * f[j + len]
          f := f.set (j + len) (f[j] - t)
          f := f.set j         (f[j] + t)
    pure f


  /-! ## Specialized NTT and CRT for ML-KEM

  We specialize `ntt_butterfly_poly_k` and `crtIq_k` to the ML-KEM parameters l=0, i=0, k=7.
  The NTT function takes a polynomial f of degree ≤ 255 and produces 128 polynomials.
  The CRT isomorphism decomposes Rq into 128 quotient rings.
  The equivalence theorem follows directly from `ntt_butterfly_k_eq_crt`.
  -/

  /-- The NTT for ML-KEM: takes a polynomial of degree ≤ 255 and produces 2^7 polynomials.
      This is just `ntt_butterfly_poly_k` at l=0, i=0, k=7. -/
  noncomputable
  def ntt_MLKEM (f : Zq[X]) (hf : f.degree ≤ 255) : Fin (2^7) → Zq[X] :=
    have hf' : f.degree ≤ (2 ^ (8 - (0 : Fin 8).val) - 1 : ℕ) := by simp; exact hf
    ntt_butterfly_poly_k (l := ⟨0, by omega⟩) (i := ⟨0, by simp⟩)
      (k := ⟨7, by omega⟩) (hlk := by decide) (f := f) (hf := hf')

  /-- The specialized NTT agrees with the CRT decomposition: for any polynomial f of degree ≤ 255,
      mapping each output polynomial into the appropriate quotient ring gives
      the same result as applying the CRT isomorphism `crtIq_k 0 0 7` to [f] ∈ Rq.
      This is a direct corollary of `ntt_butterfly_k_eq_crt`. -/
  theorem ntt_MLKEM_eq_crt (f : Zq[X]) (hf : f.degree ≤ 255) (j : Fin (2^7)) :
      ntt_butterfly_k ⟨0, by omega⟩ ⟨0, by simp⟩ ⟨7, by omega⟩ (by decide) f
        (by simp; exact hf) j =
      crtIq_k 0 0 7 (by decide) (Ideal.Quotient.mk (Iq 0 0) f) j := by
    exact congr_fun (ntt_butterfly_k_eq_crt ⟨0, by omega⟩ ⟨0, by simp⟩
      ⟨7, by omega⟩ (by decide) f (by simp; exact hf)) j

end Poly
