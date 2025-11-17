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
set_option maxHeartbeats 50000
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


  noncomputable
  def f_lk (l k : Nat) := xn (2 ^ (l + 1)) - ζ ^ k

  theorem f_lk_mul (l k : Nat) : (f_lk l k) * (f_lk l (k + 128)) = f_lk (l+1) (2*k) := by
    simp [f_lk]
    ring_nf
    simp [zeta_128_eq, one, xn, monomial_pow, Zq.one]
    ring_nf


  /- # Two polynomials are coprime if m and k are not equal mod 256. -/
  theorem f_lk_coprime (l k m: Nat) (h: m % 256 ≠ k % 256):
      IsCoprime (f_lk l k) (f_lk l m) := by
    have diffUnit : IsUnit (Zq.ζ^m - Zq.ζ^k) := by
      apply Zq.zeta_pow_sub_zeta_pow_isUnit
      exact h
    rw [f_lk, f_lk, IsCoprime]
    use monomial 0 (Ring.inverse (Zq.ζ^m - Zq.ζ^k))
    use -monomial 0 (Ring.inverse (Zq.ζ^m - Zq.ζ^k))
    rw [mul_sub, mul_sub, xn]
    ring_nf
    rw [← mul_sub_left_distrib, ζ]
    simp
    rw [← C.map_pow (Zq.ζ) m, ← C.map_pow (Zq.ζ), ← C.map_sub (Zq.ζ^m), ← C.map_mul, ← C.map_one]
    rw [ZMod.inv_mul_of_unit (Zq.ζ ^ m - Zq.ζ ^ k) diffUnit]

  /- # The corresponding ideals are coprime -/
  theorem f_lk_Ideals_coprime (l k m: Nat) (h: m % 256 ≠ k % 256):
      IsCoprime (Ideal.span {f_lk l k}) (Ideal.span {f_lk l m}) := by
    apply (Ideal.isCoprime_span_singleton_iff (f_lk l k) (f_lk l m)).mpr
    exact f_lk_coprime l k m h

  /- # CRT for one decomposition from Rq -/
  /- Zq[X] ⧸ (X^256 + 1) ≃+* Zq[X] ⧸ (X^128 - ζ^64) ×  Zq[X] ⧸ (X^128 + ζ^64) -/
  noncomputable
  def crt_Rq_1 :
    (Zq[X] ⧸ Ideal.span {f_lk 7 128}) ≃+*
    (Zq[X] ⧸ Ideal.span {f_lk 6 64}) × (Zq[X] ⧸ Ideal.span {f_lk 6 192}) := by
    have coprime : IsCoprime (Ideal.span {f_lk 6 64}) (Ideal.span {f_lk 6 192}) := by
      apply f_lk_Ideals_coprime
      grind
    have prod : (Ideal.span {f_lk 6 64}) * (Ideal.span {f_lk 6 192}) = Ideal.span {f_lk 7 128} := by
      simp [Ideal.span_singleton_mul_span_singleton (f_lk 6 64) (f_lk 6 192)]
      simp [f_lk_mul]
    rw [← prod]
    apply Ideal.quotientMulEquivQuotientProd (Ideal.span {f_lk 6 64}) (Ideal.span {f_lk 6 192}) coprime

  /- # CRT for one decomposition from any Rlk as long as the power at ζ is even -/
  /- Zq[X] ⧸ (X^(2^(l+1)) - ζ^(2k)) ≃+* Zq[X] ⧸ (X^(2^l) - ζ^k) ×  Zq[X] ⧸ (X^(2^l) + ζ^k) -/
  noncomputable
  def crt_Rlk_1 (l k : Nat) :
    (Zq[X] ⧸ Ideal.span {f_lk (l + 1) (2*k)}) ≃+*
    (Zq[X] ⧸ Ideal.span {f_lk l k}) × (Zq[X] ⧸ Ideal.span {f_lk l (k + 128)}) := by
    have coprime : IsCoprime (Ideal.span {f_lk l k}) (Ideal.span {f_lk l (k + 128)}) := by
      apply f_lk_Ideals_coprime
      grind
    have prod :
      (Ideal.span {f_lk l k}) * (Ideal.span {f_lk l (k + 128)}) =
       Ideal.span {f_lk (l + 1) (2*k)} := by
      simp [Ideal.span_singleton_mul_span_singleton (f_lk l k) (f_lk l (k + 128)), f_lk_mul]
    rw [← prod]
    apply Ideal.quotientMulEquivQuotientProd (Ideal.span {f_lk l k}) (Ideal.span {f_lk l (k + 128)}) coprime


  /- The BitRev₇ function from the ML-KEM specification [Section 4.3]
     "Define BitRev₇(𝑖) to be the integer represented by bit-reversing
      the unsigned 7-bit value that corresponds to the input integer
      𝑖 ∈ {0,…,127}." -/
  def BitRev₇ (i : Fin 128) : Fin 128 :=
    have : i.val < 2 ^ 7 := by exact i.isLt
    let ibits := BitVec.ofNatLT i.val this
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
    have : i.val < 2 ^ b := by exact i.isLt
    let ibits := BitVec.ofNatLT i.val this
    (ibits.reverse).toFin

  #eval BitRev 7 2

  example : BitRev 0 0 = 0 := by rfl
  example : BitRev 3 1 = 4 := by rfl
  example : BitRev 7 0 = 0 := by rfl
  example : BitRev 7 2 = 32 := by rfl

  lemma BitRev_equal : ∀ i : Fin 128, BitRev₇ i = BitRev 7 i := by
    intro i; rfl

  lemma BitVec_reverse_reverse_eq {n : ℕ} (v : BitVec n) : v.reverse.reverse = v := by sorry
    -- This seems to exist in Mathlib v4.25.

  lemma BitRev_inv (b : ℕ) (i : Fin (2 ^ b)) : BitRev b (BitRev b i) = i := by
    simp [BitRev, BitVec_reverse_reverse_eq]

  lemma BitRev₇_inv (i : Fin 128) : BitRev₇ (BitRev₇ i) = i := by
    decide +revert

  lemma BitRev_inj (b : ℕ) (i j : Fin (2 ^ b)) (hij : i ≠ j) : BitRev b i ≠ BitRev b j := by
    intro h
    have h' : BitRev b (BitRev b i) = BitRev b (BitRev b j) := congr_arg (BitRev b) h
    rw [BitRev_inv, BitRev_inv] at h'
    exact hij h'


  /-- Bit reversal of an odd number (2i+1) equals bit reversal of the even number (2i)
      plus 2^(b-1), where b is the number of bits. This is because adding 1 sets the LSB,
      which becomes the MSB after reversal.
  -/
  lemma BitRev_odd_from_even (b : ℕ) (hb : b > 0) (i : Fin (2 ^ (b - 1))) :
    let i₂ : Fin (2 ^ b) := ⟨2 * i.val + 1, by
      have : 2 ^ b = 2 * 2 ^ (b - 1) := by
        cases b
        · omega
        · simp [Nat.pow_succ]; ring
      omega⟩
    let i₁ : Fin (2 ^ b) := ⟨2 * i.val, by
      have : 2 ^ b = 2 * 2 ^ (b - 1) := by
        cases b
        · omega
        · simp [Nat.pow_succ]; ring
      omega⟩
    (BitRev b i₂).val = (BitRev b i₁).val + 2^(b - 1) := by
    intro i₂ i₁
    have : Nat.testBit i₁.val 0 = false := by
      grind
    have : Nat.testBit i₂.val 0 = true := by
      grind
    have : i₁.val / 2 = i₂.val / 2 := by grind
    have : ∀ j : ℕ , Nat.testBit i₁.val (j+1) = Nat.testBit i₂.val (j+1) := by
      grind
    have : (BitVec.ofNat b i₁.val)[0] = false := by
      simp [i₁]
      sorry
    sorry

  #check BitVec.msb

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

    This means that the ring for for (l, i) decomposes as the product of the rings for (l+1, 2i) and (l+1, 2i+1).
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
    simp [fq, ζ_exp, x_exp, BitRev, BitVec.reverse, BitVec.msb, Nat.testBit]

  /- Define the i-th quotient ring at level l down from Rq defined by (fq l i). -/
  def Sq (l : Fin 8) (i : Fin (2 ^ l.val)) :=
    Zq[X] ⧸ Ideal.span {fq l i}

  example : Sq 0 0 = (Zq[X] ⧸ Ideal.span {xn 256 + 1}) := by
    simp [Sq, fq, ζ_exp, x_exp, zeta_128_eq, one]
  example : Sq 1 1 = (Zq[X] ⧸ Ideal.span {xn 128 - ζ^192}) := by
    simp [Sq, fq, ζ_exp, x_exp, BitRev, BitVec.reverse, BitVec.msb]
  example : Sq 7 1 = (Zq[X] ⧸ Ideal.span {xn 2 - ζ^129}) := by
    simp [Sq, fq, ζ_exp, x_exp, BitRev, BitVec.reverse, BitVec.msb, Nat.testBit]


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
    simp only [fq]
    sorry


  noncomputable
  def crt_Sq_1 (l : Fin 8) (i : Fin (2 ^ l.val)) (hl : l.val < 7) :
    let l' : Fin 8 := ⟨l.val + 1, by omega⟩
    let i₁ : Fin (2 ^ l'.val) := ⟨2 * i.val, by simp [l']; omega⟩
    let i₂ : Fin (2 ^ l'.val) := ⟨2 * i.val + 1, by simp [l']; omega⟩
    Zq[X] ⧸ Ideal.span {fq l i} ≃+* (Zq[X] ⧸ Ideal.span {fq l' i₁}) × (Zq[X] ⧸ Ideal.span {fq l' i₂}) :=
  by
    intro l' i₁ i₂
    have coprime : IsCoprime (Ideal.span {fq l' i₁}) (Ideal.span {fq l' i₂}) := by
      rw [Ideal.isCoprime_span_singleton_iff]
      apply fq_coprime
      simp [i₁, i₂]
    have prod :
      (Ideal.span {fq l' i₁}) * (Ideal.span {fq l' i₂}) =
       Ideal.span {fq l i} := by
      rw [Ideal.span_singleton_mul_span_singleton]
      rw [fq_mul l i hl]
    rw [← prod]
    apply Ideal.quotientMulEquivQuotientProd (Ideal.span {fq l' i₁}) (Ideal.span {fq l' i₂}) coprime
