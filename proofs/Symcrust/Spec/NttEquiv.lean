import Lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
--import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.Tactic.Ring

set_option maxRecDepth 2000


/- In this file, "the thesis" refers to https://kannwischer.eu/thesis/phd-thesis-2023-01-03.pdf -/

/- The Kyber prime q and root of unity ζ -/

@[simp]
def q := 3329

lemma q_nonzero : q ≠ 0 := by trivial

def zeta := 17

example : (q - 1) = 2^8 * 13 := rfl
example : (q-2)*q = 2^16 * 169 - 1 := by simp

/-- Finite ring Zq --/

@[reducible]
def Zq := ZMod q

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

  -- zeta ^ m ≠ 0
  theorem zeta_pow_non_zero_aux (m : Nat) (hm : m ≤ 256) : ζ ^ m ≠ 0 := by
    intro h
    have pow_eq : (ζ ^ m) * ζ ^ (256 - m) = 0 * zeta ^ (256 - m) := by simp [h]
    ring_nf at pow_eq
    simp [← pow_add] at pow_eq
    have hm : m + (256 - m) = 256 := by
      simp [← Nat.add_sub_assoc hm m]
    simp [hm] at pow_eq
    rw [zeta_256_eq] at pow_eq
    trivial

  theorem zeta_pow_non_zero (m : Nat) : ζ ^ m ≠ 0 := by
    intro h
    rw [← mod_add_div m 256] at h
    simp [pow_add] at h
    -- Get rid of zeta ^ (256 * ...)
    simp [pow_mul, zeta_256_eq] at h
    -- Finish the proof by using the fact that: m % 256 < 256
    have h_256_pos : 256 > 0 := by simp
    have h_lt := mod_lt m h_256_pos
    have h_lt := le_of_lt h_lt
    simp [zeta_pow_non_zero_aux _ h_lt] at h

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
  def TqAux (height baseLevel zetaPow: Nat) :=
    match height with
    | 0 => Zq[X] ⧸ Ideal.span {xn (2^(baseLevel + 1)) - ζ ^ (zetaPow)}
    | k + 1 =>
      TqAux k baseLevel (zetaPow/2) × TqAux k baseLevel (zetaPow/2 + 128)

  #check TqAux 0 7 128 -- This is the ring Zq[X] ⧸ Ideal.span {xn 256 + 1}
  #check TqAux 0 6 64  -- This is the ring Zq[X] ⧸ Ideal.span {xn 128 - zeta ^ 64}
  #check TqAux 0 6 192  -- This is the ring Zq[X] ⧸ Ideal.span {xn 128 + zeta ^ 64}
  #check TqAux 1 6 128 -- This is the product of (TqAux 0 6 64) × (TqAux 0 6 192)


  /- # The corresponding polynomials. -/
  noncomputable
  def PiAux (level zetaPow : Nat) :=
    match level with
    | 0 => xn 2 - ζ ^ zetaPow
    | k + 1 => (PiAux k (zetaPow/2)) * (PiAux k ((zetaPow/2) + 128))

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
      have h₉ : m < 8 := by
        calc
          m = m + 1 - 1 := by rw[Nat.add_sub_cancel]
          _ < 8 - 1 := by apply Nat.lt_of_add_lt_add_right h₂
          _ < 8 := by simp
      simp [PiAux]
      rw [pi_lk m (k / 2), pi_lk m]
      ring_nf
      simp [PiAux, xn, one, Zq.one]
      ring_nf
      simp [zeta_128_eq, monomial_pow, one]
      rw [Nat.div_mul_cancel]
      apply h₃
      apply Nat.dvd_add h₇ h₈
      apply h₉
      apply h₇
      apply h₉

  theorem Tq_Pi_correspondence (l k : Nat) (h₁ : (2 ^ l) ∣ k) (h₂ : l < 8) :
        (TqAux 0 l k) = (Zq[X] ⧸ Ideal.span {PiAux l k}) := by
    rw [TqAux, pi_lk l k h₁ h₂]

  example : TqAux 0 7 128 = (Zq[X] ⧸ Ideal.span {xn 256 + 1}) := by
    simp [Tq_Pi_correspondence, pi_lk, zeta_128_eq, one]

  example : TqAux 0 6 64 = (Zq[X] ⧸ Ideal.span {xn 128 - ζ ^ 64}) := by
    simp [Tq_Pi_correspondence, pi_lk]

  example : TqAux 0 6 192 = (Zq[X] ⧸ Ideal.span {xn 128 + ζ ^ 64}) := by
    simp [Tq_Pi_correspondence, pi_lk, zeta_exp_p_128_eq]
