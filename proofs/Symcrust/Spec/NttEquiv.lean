import Lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option maxRecDepth 2500


/- In this file, "the thesis" refers to https://kannwischer.eu/thesis/phd-thesis-2023-01-03.pdf -/

/- The Kyber prime q and root of unity ζ -/

@[simp]
def q := 3329

@[simp]
lemma q_isPrime : Nat.Prime q := by native_decide

lemma q_nonzero : q ≠ 0 := by trivial
lemma q_minus_one_fact : (q - 1) = 2^8 * 13 := rfl

example : (q-2)*q = 2^16 * 169 - 1 := by simp

def zeta := 17

instance : Fact (Nat.Prime q) := ⟨q_isPrime⟩

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

  theorem zeta_coprime : Nat.Coprime ζ.val q := by rfl

  theorem zeta_isUnit : IsUnit ζ := by
    apply (ZMod.isUnit_iff_coprime ζ.val q).mpr
    exact zeta_coprime

  theorem zeta_ne_one : ζ ≠ 1 := by trivial
  theorem zeta_ne_zero : ζ ≠ 0 := by trivial

  theorem zeta_mul_inv_zeta_eq_one : ζ * ζ⁻¹ = 1 := by
    simp
    rw [ZMod.mul_inv_eq_gcd]
    have : ↑((gcd) ζ.val q) = (1 : Zq) := rfl
    apply this

  theorem inv_zeta_mul_zeta_eq_one : ζ⁻¹ * ζ = 1 := by
    rw [mul_comm]
    exact zeta_mul_inv_zeta_eq_one

  theorem inv_zeta_val : ζ⁻¹ = 1175 := by
    have h : ζ * 1175 = 1 := by rfl
    calc
      ζ⁻¹ = ζ⁻¹ * 1 := by simp
      _ = ζ⁻¹ * ζ * 1175 := by rw [← h, mul_assoc]
      _ = 1 * 1175 := by rw [inv_zeta_mul_zeta_eq_one]
      _ = 1175 := by simp

  theorem inv_zeta_eq_zeta_pow : ζ⁻¹ = ζ ^ 255 := by
    rw [inv_zeta_val]
    rfl

  -- zeta ^ 256 = 1
  theorem zeta_256_eq : ζ ^ 256 = 1 := by rfl

  theorem zeta_128_eq : ζ ^ 128 = - 1 := by rfl

  theorem zeta_2_eq : ζ ^ 2 = 289 := by rfl

  theorem zeta_13_eq : ζ ^ 13 = 939 := by rfl

  lemma zeta_order_div_256 :  orderOf ζ ∣ 256 := by
    apply orderOf_dvd_of_pow_eq_one zeta_256_eq

  theorem zeta_order_eq_256 : orderOf ζ = 256 := by
    have : 0 < 256 := by decide
    apply (orderOf_eq_iff this).mpr
    constructor
    · exact zeta_256_eq
    · intro m hlt hgt
      decide +revert

  theorem zeta_pow_non_zero (m : Nat) : ζ ^ m ≠ 0 := by
    intro h
    rw [← mod_add_div m 256] at h
    simp [pow_add] at h
    apply zeta_ne_zero
    cases h with
    | inl hl => exact hl.left
    | inr hr => exact hr.left

  theorem zeta_pow_m_neq_one (m : Nat) (hl : 0 < m) (hu : m < 256) : ζ ^ m ≠ 1 := by
    have : 0 < 256 := by decide
    apply ((orderOf_eq_iff this).mp zeta_order_eq_256).right
    repeat linarith

  lemma diff_mod (m k : Nat) (h₀ : m ≥ k) (h₁ : (m - k) % 256 = 0) : (m % 256) = (k % 256) := by
    grind

  lemma zeta_pow_sub_zeta_pow_ne_zero (m k : Nat) (h : (m % 256) ≠ (k % 256)) : ζ^m - ζ^k ≠ 0 := by
    intro hyp
    by_cases h₀ : k ≤ m
    · have hmk : k + (m - k) = m := by
        rw [← Nat.add_sub_assoc h₀ k, Nat.add_sub_cancel_left]
      have hmkmod : (m - k) % 256 < 256 := by
        apply Nat.mod_lt
        decide
      have hzpow : ζ ^ ((m-k) % 256) ≠ 1 := by
        apply zeta_pow_m_neq_one (((m-k) % 256))
        · by_contra h0
          simp at h0
          apply diff_mod at h0
          contradiction
          apply h₀
        exact hmkmod
      have : ζ^k * (ζ^(m-k) - 1) = 0 := by
        calc
          ζ^k * (ζ^(m-k) - 1 ) = ζ^(k + (m-k)) - ζ^k := by ring
          _ = ζ^m - ζ^k := by rw [hmk]
          _ = 0 := by exact hyp
      have hzk : ζ^k ≠ 0 := by apply zeta_pow_non_zero
      apply eq_zero_or_eq_zero_of_mul_eq_zero at this
      cases this with
      | inl ll => contradiction
      | inr rr =>
        apply sub_eq_zero.mp at rr
        rw [← pow_mod_orderOf ζ (m-k)] at rr
        simp [Zq.zeta_order_eq_256] at rr
        contradiction
    · simp at h₀
      have hkm : m + (k - m ) = k := by
        rw [← Nat.add_sub_assoc (le_of_lt h₀) m, Nat.add_sub_cancel_left]
      have hkmmod : (k - m) % 256 < 256 := by
        apply Nat.mod_lt
        decide
      have hzpow : ζ ^ ((k-m) % 256) ≠ 1 := by
        apply zeta_pow_m_neq_one (((k-m) % 256))
        · by_contra h0
          simp at h0
          apply diff_mod at h0 ; symm at h0
          contradiction
          apply (le_of_lt h₀)
        exact hkmmod
      have : ζ^m * (1-ζ^(k-m)) = 0 := by
        calc
          ζ^m * (1-ζ^(k-m)) = ζ^m - ζ^(m + (k-m)) := by ring
          _ = ζ^m - ζ^k := by rw [hkm]
          _ = 0 := by exact hyp
      have hzm : ζ^m ≠ 0 := by apply zeta_pow_non_zero
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

  /- # Definition of the ring structure in the Kyber ring. -/
  def TqAux (splits baseLevel zetaPow: Nat) :=
    match splits with
    | 0 => Zq[X] ⧸ Ideal.span {xn (2^(baseLevel + 1)) - ζ ^ (zetaPow)}
    | k + 1 =>
      TqAux k (baseLevel-1) (zetaPow/2) × TqAux k (baseLevel-1) (zetaPow/2 + 128)

  #check TqAux 0 7 128 -- This is the ring Zq[X] ⧸ Ideal.span {xn 256 + 1}
  #check TqAux 0 6 64  -- This is the ring Zq[X] ⧸ Ideal.span {xn 128 - zeta ^ 64}
  #check TqAux 0 6 192  -- This is the ring Zq[X] ⧸ Ideal.span {xn 128 + zeta ^ 64}
  example : TqAux 1 7 128 = ((TqAux 0 6 64) × (TqAux 0 6 192)) := by simp [TqAux]
  example : TqAux 2 4 128 = (((TqAux 0 2 32) × (TqAux 0 2 160)) × ((TqAux 0 2 96) × (TqAux 0 2 224))) := by simp [TqAux]


  /- # The corresponding polynomials. -/
  noncomputable
  def PiAux (level zetaPow : Nat) :=
    match level with
    | 0 => xn 2 - ζ ^ zetaPow
    | k + 1 => (PiAux k (zetaPow/2)) * (PiAux k ((zetaPow/2) + 128))

  example : PiAux 0 1 = xn 2 - ζ := by simp [PiAux]
  example : PiAux 1 2 = xn 4 - ζ ^ 2 := by
    simp [PiAux, xn, Zq.one, zeta_exp_p_128_eq]
    ring_nf
    simp [sub_eq_add_neg, add_comm]

  /- # Explicit formula for the polynomials. -/
  theorem pi_lk (l k : Nat) (h₁ : (2 ^ l) ∣ k) (h₂ : l < 8): PiAux l k = xn (2 ^ (l + 1)) - ζ ^ k := by
    match l with
    | 0 => simp [PiAux, xn]
    | m + 1 =>
      have h₃ : 2 ∣ k := by apply Nat.dvd_of_pow_dvd _ h₁ ; simp
      have h₄ : 2 * 2 ^ m ∣ k := by
         calc
           2 * 2 ^ m = 2 ^ (m + 1) := by ring_nf
           _ ∣ k := by apply h₁
      have h₅ : 2 * (k / 2) = k - (k % 2) := by omega
      have h₆ : 2 * (k / 2) = k := by
        have : k % 2 = 0 := by apply Nat.mod_eq_zero_of_dvd h₃
        rw[this, Nat.sub_zero] at h₅
        exact h₅
      have h₇ : 2 ^ m ∣ k / 2 := by
        rw [←h₆] at h₄
        apply Nat.dvd_of_mul_dvd_mul_left Nat.two_pos h₄
      have h₈ : 2 ^ m ∣ 128 := by
        have : m ≤ 7 := by
          apply Nat.le_of_lt
          apply Nat.lt_of_add_lt_add_right h₂
        apply Nat.pow_dvd_pow 2 this
      simp [PiAux]
      rw [pi_lk m (k / 2), pi_lk m]
      ring_nf
      simp [PiAux, xn, one, Zq.one]
      simp [zeta_128_eq, monomial_pow, one]
      rw [Nat.div_mul_cancel]
      ring_nf

      apply h₃
      apply Nat.dvd_add h₇ h₈
      linarith
      apply h₇
      linarith

  theorem Tq_Pi_correspondence_0 (l k : Nat) (h₁ : (2 ^ l) ∣ k) (h₂ : l < 8) :
        (TqAux 0 l k) = (Zq[X] ⧸ Ideal.span {PiAux l k}) := by
    rw [TqAux, pi_lk l k h₁ h₂]

  example : TqAux 0 7 128 = (Zq[X] ⧸ Ideal.span {xn 256 + 1}) := by
    simp [Tq_Pi_correspondence_0, pi_lk, zeta_128_eq, one]

  example : TqAux 0 6 64 = (Zq[X] ⧸ Ideal.span {xn 128 - ζ ^ 64}) := by
    simp [Tq_Pi_correspondence_0, pi_lk]

  example : TqAux 0 6 192 = (Zq[X] ⧸ Ideal.span {xn 128 + ζ ^ 64}) := by
    simp [Tq_Pi_correspondence_0, pi_lk, zeta_exp_p_128_eq]


  theorem Tq_Pi_correspondence_1 (l k : Nat) (h₁ : (2 ^ (l+1)) ∣ k) (h₂ : l < 7) :
        (TqAux 1 (l+1) k) = ((Zq[X] ⧸ Ideal.span {PiAux l (k/2)}) × (Zq[X] ⧸ Ideal.span {PiAux l (k/2 + 128)})) := by
    have h₃ : 2 ^ l ∣ (k / 2) := by
      refine (Nat.dvd_div_iff_mul_dvd ?_).mpr ?_
      apply Nat.dvd_of_pow_dvd _ h₁
      simp
      rw [Eq.symm Nat.pow_succ']
      apply h₁
    simp [TqAux]
    rw [pi_lk l (k/2), pi_lk l (k/2 + 128)]
    · refine (Nat.dvd_add_iff_right ?_).mp ?_
      exact h₃
      apply Nat.pow_dvd_pow 2 (Nat.le_of_lt h₂)
    · linarith
    · exact h₃
    · linarith


#check IsCoprime
  theorem PiAux_coprime (l k m: Nat) (h₀ : (2 ^ l) ∣ k) (h₁ : (2 ^ l) ∣ m) (h₂ : l < 8) (h₃: m % 256 ≠ k % 256):
      IsCoprime (PiAux l k) (PiAux l m) := by
    have diffUnit : IsUnit (Zq.ζ^m - Zq.ζ^k) := by
      apply Zq.zeta_pow_sub_zeta_pow_isUnit
      exact h₃
    rw [pi_lk, pi_lk]
    rw [IsCoprime]
    use monomial 0 (Ring.inverse (Zq.ζ^m - Zq.ζ^k))
    use -monomial 0 (Ring.inverse (Zq.ζ^m - Zq.ζ^k))
    rw [mul_sub, mul_sub, xn]
    simp [monomial_mul_monomial, mul_one, add_zero, one_mul]
    ring_nf
    rw [← mul_sub_left_distrib, ζ]
    simp
    rw [← C.map_pow (Zq.ζ) m, ← C.map_pow (Zq.ζ), ← C.map_sub (Zq.ζ^m), ← C.map_mul, ← C.map_one]
    have : (Zq.ζ^m - Zq.ζ^k)⁻¹ * (Zq.ζ^m - Zq.ζ^k) = 1 := by
      exact ZMod.inv_mul_of_unit (Zq.ζ ^ m - Zq.ζ ^ k) diffUnit
    rw [this]
    tauto
    repeat assumption
