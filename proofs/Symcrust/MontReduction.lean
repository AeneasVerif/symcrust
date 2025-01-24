import Lean
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Qify
import Mathlib.Data.Rat.Floor

import Aeneas

namespace Symcrust

set_option maxHeartbeats 1000000

/-!
We need a few arithmetic facts that are not in Mathlib.
TODO: PR for Mathlib?
-/

-- We have to prove a few inequalities involving non-linear arithmetic
set_option scalarTac.nonLin true

/- In this file, "the thesis" refers to https://kannwischer.eu/thesis/phd-thesis-2023-01-03.pdf -/

-- TODO: this should be in mathlib
theorem Int.gcd_add_mul_self (a b k : ℤ) :
  Int.gcd a (b + k * a) = Int.gcd a b := by
  apply Eq.symm
  have h := @Int.gcd_greatest a (b + k * a) (Int.gcd a b) (by simp)
  simp only [Nat.cast_inj] at h
  apply h
  . apply Int.gcd_dvd_left
  . apply dvd_add
    . apply Int.gcd_dvd_right
    . rw [dvd_mul]
      exists 1, gcd a b
      simp only [isUnit_one, IsUnit.dvd, one_mul, true_and]
      split_conjs
      apply Int.gcd_dvd_left
      rfl

  . intro e div_a div_bk
    have div_ka : e ∣ k * a := by
      rw [dvd_mul]
      exists 1, e
      simp [*]
    have div_b : e ∣ b := by
      have h : e ∣ (b + k * a) + (- k * a) := by
        apply dvd_add <;> simp [*]
      simp only [neg_mul, add_neg_cancel_right] at h
      apply h
    apply Int.dvd_gcd <;> assumption

-- TODO: this should be in mathlib
theorem Int.gcd_mod_same {a b : ℤ} :
  Int.gcd (a % b) b = Int.gcd a b := by
  have h1 : a % b = a - b * (a / b) := by
    have heq := Int.ediv_add_emod a b
    linarith
  have h2 := Int.gcd_add_mul_self b a (- (a / b))
  rw [h1]
  simp only [neg_mul] at h2
  conv at h2 => lhs; rw [Int.gcd_comm]
  conv => rhs; rw [Int.gcd_comm]
  convert h2 using 2
  ring_nf

theorem cancel_right_div_gcd_pos {m a b : ℤ}
  (c : Int) (hm : 0 < m) (hgcd : Int.gcd m c = 1)
  (h : (a * c) % m = (b * c) % m) :
  a % m = b % m := by
  have heq := Int.ModEq.cancel_right_div_gcd hm h
  simp only [hgcd, Nat.cast_one, EuclideanDomain.div_one] at heq
  apply heq

theorem cancel_right_div_gcd {m : ℤ} (a b c : Int) (hgcd : Int.gcd c m = 1)
  (h : (a * c) % m = (b * c) % m) :
  a % m = b % m := by
  rw [Int.gcd_comm] at hgcd
  if hm : m = 0 then
    simp_all only [Int.gcd_zero_left, EuclideanDomain.mod_zero, mul_eq_mul_right_iff]
    dcases hc : c = 0 <;> simp_all
  else
    if m ≤ 0 then
      have hm' : 0 < -m := by int_tac
      have hgcd' : Int.gcd (-m) c = 1 := by simp [hgcd]
      have hf := @cancel_right_div_gcd_pos (-m) a b c hm' hgcd'
      simp only [Int.emod_neg] at hf
      apply hf
      assumption
    else
      have hm : 0 < m := by simp_all
      have heq := Int.ModEq.cancel_right_div_gcd hm h
      simp only [hgcd, Nat.cast_one, EuclideanDomain.div_one] at heq
      apply heq

theorem cancel_left_div_gcd {m : ℤ} (a b c : Int) (hgcd : Int.gcd c m = 1)
  (h : (c * a) % m = (c * b) % m) :
  a % m = b % m := by
  have heq := cancel_right_div_gcd a b c hgcd
  apply heq
  ring_nf at *
  apply h

theorem times_mod_imp_div_mod (n : ℕ) (a b c : ℤ)
  (hdiv : a % b = 0)
  (hgcd : Int.gcd b n = 1)
  (heq : a % n = (c * b) % n) :
  (a / b) % n = c % n := by
  -- step 1: multiply by b on both sides
  apply (cancel_right_div_gcd (a / b) c b (by assumption))
  -- step 2: simplify (... / b) * b
  rw [Int.ediv_mul_cancel_of_emod_eq_zero hdiv]
  -- End of the proof
  apply heq

/-!
We need to prove equalities of the shape: `a % n = b % n`.

When encoutering such an equality the proof strategy is to simply cast the integers into `ZMod` which,
being a ring, is convenient to work in. Below, we list a few simp theorems which are necessary for this to work.
-/
theorem ZMod_int_cast_eq_int_cast_iff (n : ℕ) (a b : ℤ) :
  ((a : ZMod n) = (b : ZMod n)) ↔ (a % n = b % n) :=
  ZMod.intCast_eq_intCast_iff a b n

/-- The important theorem to convert a goal about equality modulo into a goal about the equalit of two terms in `ZMod` -/
theorem ZMod_eq_imp_mod_eq {n : ℕ} {a b : ℤ}
  (h : (a : ZMod n) = (b : ZMod n)) :
  a % n = b % n :=
  (@ZMod_int_cast_eq_int_cast_iff n a b).mp h

theorem mod_eq_imp_ZMod_eq {n : ℕ} {a b : ℤ}
  (h : a % n = b % n) :
  (a : ZMod n) = (b : ZMod n) :=
  (@ZMod_int_cast_eq_int_cast_iff n a b).mpr h

theorem ZMod_val_injective {n : ℕ} [NeZero n] {a b : ZMod n} (h : a.val = b.val) :
  a = b :=
  ZMod.val_injective n h

theorem ZMod.mul_inv_eq_int_gcd {n : ℕ} (a : ℤ) :
  (a : ZMod n) * (a : ZMod n)⁻¹ = Int.gcd a n := by
  if hn : n = 0 then
    simp only [hn, CharP.cast_eq_zero, Int.gcd_zero_right]
    rw [ZMod.mul_inv_eq_gcd]
    simp only [hn, Nat.gcd_zero_right]

    have h := @ZMod.intCast_eq_intCast_iff' (ZMod.val (a : ZMod n)) (Int.natAbs a) n
    simp only [Int.cast_natCast, Int.natCast_natAbs, hn, CharP.cast_eq_zero,
      EuclideanDomain.mod_zero] at h
    unfold ZMod.val
    rw [hn]
    simp only [Nat.cast_inj]
    rfl
  else
    have hn : 0 < n := by cases n <;> simp_all only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
      and_false, not_false_eq_true, Aeneas.Simp.neq_imp, lt_add_iff_pos_left, add_pos_iff,
      zero_lt_one, or_true, not_true_eq_false]
    rw [ZMod.mul_inv_eq_gcd]
    rw [← Int.gcd_natCast_natCast]
    have hnz : NeZero n := by simp [neZero_iff, *]
    rw [← ZMod.cast_eq_val]
    -- Simplify `↑↑a`
    rw [ZMod.coe_intCast]
    rw [Int.gcd_mod_same]

/-- A theorem to work with division when converting integers to elements of `ZMod` -/
theorem div_to_ZMod {n : ℕ} {a b : ℤ} [NeZero n] (hDiv : b ∣ a) (hgcd : Int.gcd b n = 1) :
  ((a / b) : ZMod n) = (a : ZMod n) * (b : ZMod n)⁻¹ := by
  have h : (a / b) % (n : Int) = ((a % (n : Int)) * (b : ZMod n)⁻¹.cast) % (n : Int) := by
    apply times_mod_imp_div_mod
    . rw [← Int.dvd_iff_emod_eq_zero]
      assumption
    . assumption
    . apply ZMod_eq_imp_mod_eq
      simp only [Int.cast_mul, ZMod.intCast_mod, ZMod.intCast_cast, ZMod.cast_id', id_eq]
      rw [mul_assoc]
      have := @ZMod.mul_inv_eq_int_gcd n b
      rw [mul_comm] at this
      rw [this]
      rw [hgcd]
      simp
  have h1 := mod_eq_imp_ZMod_eq h
  rw [h1]
  simp

/-- Montegomery reduction -/
def mont_reduction (q R a : Nat) (minus_q_minus_1 : Int) : Int :=
  let f := (a * minus_q_minus_1) % R
  let t := (a + f * q) / R
  t

def mont_reduction_spec
  (q: Nat)
  (R: Nat)
  (minus_q_minus_1: Int)
  (a: Nat)
  (h_R: R > q ∧ exists n, R = 2 ^ n)
  (h_q_minus_1: (minus_q_minus_1 * q) % R = (-1) % R)
  (h_q: 0 < q)
  (h_a: a < q * R)
  (h_q_R: Nat.Coprime R q) :
  let t := mont_reduction q R a minus_q_minus_1
  t % (q : Int) = (a * (R: ZMod q)⁻¹.val) % q ∧
  0 ≤ t ∧ t < 2 * q
  := by
  let f := (a * minus_q_minus_1) % R
  let t := (a + f * q) / R

  -- Having this is in the context is useful as it triggers simplifications
  have : NeZero q := by constructor; omega

  -- Main goal
  have h_t: t % (q : Int) = (a * ((R : ZMod q)⁻¹.val : Int)) % q := by
    apply ZMod_eq_imp_mod_eq
    simp only [ZMod.natCast_val, Int.cast_mul, Int.cast_natCast, ZMod.intCast_cast, ZMod.cast_id',
      id_eq, t, f]
    rw [div_to_ZMod]
    . simp
    . rw [Int.dvd_iff_emod_eq_zero]
      have hZero : 0 = 0 % (R : Int) := by simp
      rw [hZero]
      apply ZMod_eq_imp_mod_eq
      simp only [Int.reduceNeg, ← ZMod_int_cast_eq_int_cast_iff, Int.cast_mul, Int.cast_natCast,
        Int.cast_neg, Int.cast_one, t, f] at h_q_minus_1
      simp [mul_assoc, h_q_minus_1]
    . simp [← Nat.coprime_iff_gcd_eq_one, *]

  -- Secondary goals
  have h_t1 : 0 ≤ t := by int_tac

  have h_t2 : t < 2 * q := by
    simp +zetaDelta only [gt_iff_lt, Int.reduceNeg, ZMod.natCast_val] at *; clear t f
    have h': (↑a + ↑a * minus_q_minus_1 % ↑R * ↑q) < R * q + R * q := by
      apply Int.add_lt_add
      have := @Int.ofNat_lt a (q * R)
      . simp_all only [Nat.cast_mul, iff_true, gt_iff_lt]
        rw [Int.mul_comm]
        simp [*]
      . apply mul_lt_mul_of_pos_right
        . int_tac
        . simp [*]
    apply Int.ediv_lt_of_lt_mul
    . int_tac
    . conv => rhs; rw [Int.mul_assoc]; rhs; rw [Int.mul_comm]
      int_tac

  simp +zetaDelta [mont_reduction, *]

theorem bmod_eq_emod_eq_iff (n: ℕ) (a b: ℤ) :
  (a % n = b % n) ↔ (Int.bmod a n = Int.bmod b n) := by
  simp only [Int.bmod]
  apply Iff.intro <;> intro h
  . rw [h]
  . if h_a: a % n < (n + 1) / 2 then
      if h_b: b % n < (n + 1) / 2 then
        simp only [h_a, ↓reduceIte, h_b] at h
        exact h
      else
        simp only [h_a, ↓reduceIte, h_b] at h
        have ha' : 0 ≤ a % n := by apply Int.emod_nonneg; linarith
        have hb' : b % n - n < 0 := by
          have h : b % n < n := by apply Int.emod_lt_of_pos; linarith
          linarith
        linarith
    else
      if h_b: b % n < (n + 1) / 2 then
        simp only [h_a, ↓reduceIte, h_b] at h
        have ha' : 0 ≤ b % n := by apply Int.emod_nonneg; linarith
        have hb' : a % n - n < 0 := by
          have h : a % n < n := by apply Int.emod_lt_of_pos; linarith
          linarith
        linarith
      else
        simp only [h_a, ↓reduceIte, h_b, sub_left_inj] at h
        exact h

theorem ZMod_int_cast_eq_int_cast_bmod_iff (n : ℕ) (a b : ℤ) :
  ((a : ZMod n) = (b : ZMod n)) ↔ (Int.bmod a n = Int.bmod b n) := by
  apply Iff.trans
  apply ZMod_int_cast_eq_int_cast_iff
  apply bmod_eq_emod_eq_iff

/- Admitted for now, proving equality equivalence between bmod and ZMod -/
theorem ZMod_eq_imp_bmod_eq {n : ℕ} {a b : ℤ}
  (h : (a : ZMod n) = (b : ZMod n)) :
  Int.bmod a n = Int.bmod b n :=
  (@ZMod_int_cast_eq_int_cast_bmod_iff n a b).mp h

/-- The rounding of `x` to the nearest integer.
    If `x = y + 1/2` for some `y ∈ ℤ` then `round(x) = y + 1`
 -/
def round (x: ℚ) : Int := ⌊ x + 1/2 ⌋

theorem def_ediv (a b: ℤ) : b * (a / b) = a - a % b := by
  have h: a % b + b * (a / b) = a % b + (a - a % b) := (calc
    a % b + b * (a / b) = b * (a / b) + a % b := by apply add_comm
    _ = a := by apply Int.ediv_add_emod
    _ = a % b + (a - a % b) := by field_simp
  )
  apply Int.add_left_cancel
  exact h

private theorem small_emod_inj {a b:ℤ} (n:ℤ)
  (h_mod: a % n = b % n) (h_a: 0 ≤ a) (h_a': a < n) (h_b: 0 ≤ b) (h_b': b < n)
  : a = b := calc
  a = n * (a / n) + a % n := by apply Eq.symm; apply Int.ediv_add_emod
  _ = n * 0 + a % n := by rw [Int.ediv_eq_zero_of_lt h_a h_a']
  _ = n * 0 + b % n := by rw [h_mod]
  _ = n * (b / n) + b % n := by rw [←Int.ediv_eq_zero_of_lt h_b h_b']
  _ = b := by apply Int.ediv_add_emod

private theorem barrett_reduction_lemma (x: Int) (m: Nat) (h_m: 0 < m) :
  round ((x : ℚ) / m) = (x - Int.bmod x m) / (m : ℚ) := by

  simp only [Int.bmod]
  let r := x % m;
  dcases h: r < (m + 1) / 2
  . simp +zetaDelta only [h, ↓reduceIte]

    have h': round ((x:ℚ) / m) = x / m := by
      simp only [round, one_div]
      field_simp

      -- This is equivalent to a goal which only uses integers
      suffices h : (x * 2 + ↑m) / ↑(m * 2) = x / ↑m by
        conv => lhs; arg 1; lhs; norm_cast
        conv => lhs; arg 1; rhs; norm_cast
        rw [Rat.floor_intCast_div_natCast, h]

      -- Continuing with integers
      have heq := Int.ediv_add_emod (x * 2 + m) (m * 2)
      rw [Int.add_emod] at heq

      -- We're going to use Euclide's division lemma which uniquely defines the quotient and the remainder
      have h1 := calc
        (x * 2 % (↑m * 2) + ↑m % (↑m * 2)) % (↑m * 2) = (2 * (x % ↑m) + ↑m % (↑m * 2)) % (↑m * 2) := by
          have h: x * 2 % (↑m * 2) = 2 * (x % ↑m) := by
             rw [← Int.mul_emod_mul_of_pos]
             ring_nf
             simp
          rw [h]
        _ = 2 * (x % m) + m := by
          simp only [Int.add_emod_emod]
          apply Int.emod_eq_of_lt
          . int_tac
          . omega

      rw [h1] at heq; clear h1
      ring_nf at heq
      simp only [add_assoc, add_right_inj] at heq

      have h2 : ↑m * ((↑m + x * 2) / (↑m * 2)) * 2 + x % ↑m * 2 =
                (↑m * ((↑m + x * 2) / (↑m * 2)) + x % ↑m) * 2 := by ring_nf
      simp [h2] at heq; clear h2

      have hu := @Int.ediv_emod_unique x m (x % m) ((x * 2 + m) / (m * 2)) (by simp [h_m])
      have hu := hu.mpr
      simp only [and_true, and_imp] at hu
      apply Eq.symm
      apply hu
      conv => rhs; rw [← heq]
      ring_nf
      . apply Int.emod_nonneg; linarith
      . apply Int.emod_lt_of_pos; simp only [Nat.cast_pos]; exact h_m
    rw [h']
    field_simp
    have h_rw: (x / m) * m = x - x % m := by rw [←def_ediv]; apply mul_comm
    qify at h_rw; exact h_rw

  . simp +zetaDelta only [h, ↓reduceIte]

    have h': round ((x:ℚ) / m) = (x / m) + 1 := by
      simp only [round, one_div]
      field_simp

      have h_rw : (((x * 2 + m) : ℤ) : ℚ) / ((m * 2) : ℕ) = (↑x * 2 + ↑m) / (↑m * 2) := by simp
      rw [← h_rw, Rat.floor_intCast_div_natCast]; clear h_rw
      -- (x * 2 + ↑m) / ↑(m * 2) = x / ↑m + 1

      have h_rw: x/m + 1 = (x + m) / m := by
        rw [Int.add_ediv_of_dvd_right]
        simp only [add_right_inj]
        rw [Int.ediv_self]
        linarith
        apply Int.dvd_refl


      rw [h_rw]; clear h_rw

      have hu := @Int.ediv_emod_unique (x + m) m (x % m) ((x * 2 + m) / (m * 2)) (by simp [h_m])
      have hu := hu.mpr
      simp only [Int.add_emod_self, and_true, and_imp] at hu
      apply Eq.symm
      apply hu

      have h_goal: x % ↑m + ↑m * ((x * 2 + ↑m) / (↑m * 2)) = x + ↑m := by
        clear hu; clear hu

        have heq := Int.ediv_add_emod (x * 2 + m) (m * 2)
        rw [Int.add_emod] at heq

        have h1 : (x * 2 % (↑m * 2) + ↑m % (↑m * 2)) % (↑m * 2) = 2 * (x % m) - m := by
          clear heq
          apply (small_emod_inj (m * 2))
          . have h_rw : (x * 2 % (↑m * 2) + ↑m % (↑m * 2)) % (↑m * 2) % (↑m * 2) = (2 * (x % m) + m) % (m * 2) := (calc
              (x * 2 % (↑m * 2) + ↑m % (↑m * 2)) % (↑m * 2) % (↑m * 2) = ((x * 2) % (↑m * 2) + ↑m) % (↑m * 2) := by field_simp
              _ = (2 * (x % m) + m) % (m * 2) := by
                have h_rw: (x * 2) % (↑m * 2) = (2 * x) % (2 * m) := by ring_nf
                rw [h_rw] -- Need to put in the write form to apply Int.mul_emod_mul_of_pos, which is @simp
                simp
            )
            rw [h_rw]; clear h_rw
            apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
            ring_nf
            field_simp
          . apply Int.emod_nonneg; linarith
          . apply Int.emod_lt_of_pos; linarith
          . have h_le2: 2 * ((m + 1) / 2) - m ≤ 2 * (x % m) - m := by linarith
            have h_le1 : 0 ≤ 2 * (((m:ℤ) + 1) / 2) - m := by
              if h: Even ((m:ℤ) + 1) then
                rw [Int.two_mul_ediv_two_of_even h]; simp
              else
                rw [Int.two_mul_ediv_two_of_odd] <;> try simp only [add_sub_cancel_right, sub_self,
                  le_refl]
                simp only [Int.not_even_iff_odd] at h
                exact h
            apply le_trans h_le1 h_le2
          . have h: (x % m) < m := by apply Int.emod_lt_of_pos; omega
            -- TODO: scalar_tac fails here
            omega

        rw [h1] at heq; clear h1
        ring_nf at heq

        have h_rw: ↑m + x * 2 = -↑m + (2 * (↑m + x) ) := by ring
        rw [h_rw] at heq; clear h_rw
        rw [add_assoc] at heq
        apply Int.add_left_cancel at heq

        ring_nf at heq

        have h2 : ↑m * ((↑m + x * 2) / (↑m * 2)) * 2 + x % ↑m * 2 =
                  2 * (x % ↑m + ↑m * ((x * 2 + ↑m) / (↑m * 2))) := by ring_nf
        simp only [h2] at heq; clear h2
        have h2: ↑m * 2 + x * 2 = 2 * (x + ↑m) := by ring_nf
        simp only [h2] at heq; clear h2
        simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, not_false_eq_true, Aeneas.Simp.neq_imp,
          or_false] at heq
        exact heq

      . exact h_goal
      . apply Int.emod_nonneg; linarith
      . apply Int.emod_lt_of_pos; linarith

    rw [h']
    field_simp
    rw [add_mul]
    field_simp
    have h_rw: (x / m) * m = x - x % m := by rw [←def_ediv]; apply mul_comm
    qify at h_rw; rw [h_rw]
    ring_nf

private theorem mul_cancel_le_mul (a b c : ℚ) (h_a: 0 < a) (h: a * b ≤ a * c) : b ≤ c := by
  exact (mul_le_mul_left h_a).mp h

private theorem ediv_le_add_one (x: ℤ) : (x + 1) / 2 ≤ x / 2 + 1 := by
  have h: x / 2 + 1 = (x + 2) / 2 := by
    rw [←Int.add_mul_ediv_left] <;> simp
  rw [h]
  apply Int.ediv_le_ediv <;> simp

private theorem bmod_bounds (a: ℤ) (b: ℕ) (h_b: 0 < b) : |(Int.bmod a b : ℚ)| ≤ (b:ℚ)/2 := by
  apply abs_le.mpr
  apply And.intro
  . have h: - (b/2) ≤ Int.bmod a b := by
         apply Int.le_bmod; exact h_b

    qify at h
    apply le_trans ?_ h
    apply neg_le_neg

    apply mul_cancel_le_mul 2
    simp only [Nat.ofNat_pos]
    ring_nf
    have h2: (b/2) * 2 ≤ (b: ℤ) := by
      conv => rhs; rw [← (Int.ediv_add_emod b 2)]; rfl
      have h': (b: ℤ) / 2 * 2 = 2 * (↑b / 2) := by apply Int.mul_comm
      rw [h']
      apply Int.le_add_of_nonneg_right
      exact Int.le.intro_sub (b % Int.natAbs 2 + 0) rfl
    qify at h2; exact h2

  . have h: Int.bmod a b ≤ b / 2 := by
      apply Int.le_of_lt_add_one
      have h': (b + 1) / 2 ≤ (b:ℤ) / 2 + 1 := by apply ediv_le_add_one
      apply lt_of_lt_of_le _ h'
      apply Int.bmod_lt
      exact h_b

    qify at h
    apply le_trans h
    apply mul_cancel_le_mul 2
    simp only [Nat.ofNat_pos]
    ring_nf
    have h2: (b/2) * 2 ≤ (b: ℤ) := by
      conv => rhs; rw [← (Int.ediv_add_emod b 2)]; rfl
      have h': (b: ℤ) / 2 * 2 = 2 * (↑b / 2) := by apply Int.mul_comm
      rw [h']
      apply Int.le_add_of_nonneg_right
      exact Int.le.intro_sub (b % Int.natAbs 2 + 0) rfl
    qify at h2; exact h2

private theorem barrett_reduction_bounds
  (N: ℕ)
  (h_N: 0 < N)
  (R: ℕ)
  (h_R: exists b, R = 2 ^ b)
  (A: ℕ)
  (h_A: A = round (R / N))
  (v: ℤ)
  (h_v: |v| < R)
  (o: ℤ)
  (h_o: o = (v - (N * round ((v * A) / R))))
  : |o| < N
  := by
  rw [h_o]

  have h_Rne_zero : R ≠ 0 := by
    let ⟨ w, h ⟩ := h_R;
    rw [h];
    apply pow_ne_zero;
    simp

  have h_rw1 : ((v * A) : ℚ) = (↑(v * ↑A)) := by simp

  qify
  rw [h_rw1, barrett_reduction_lemma]
  swap; omega
  rw [h_A]

  have h_rw2 : ((R : ℤ) : ℚ) = (R : ℚ) := by simp

  qify
  rw [← h_rw2, barrett_reduction_lemma (↑R) (↑N)]
  swap; exact h_N
  qify
  ring_nf


  have h_simp1 : (↑v * ↑N * ↑R * (↑N)⁻¹ * (↑R)⁻¹ : ℚ) = ↑v := (calc
      (↑v * ↑N * ↑R * (↑N)⁻¹ * (↑R)⁻¹ : ℚ) = (↑v * (↑N * (↑N)⁻¹) * (↑R * (↑R)⁻¹)) := by ring
      _ = ↑v * (↑R * (↑R)⁻¹) := by rw [Rat.mul_inv_cancel]; simp only [mul_one]; qify at h_N; linarith
      _ = ↑v := by rw [Rat.mul_inv_cancel]; simp only [mul_one]; qify at h_Rne_zero; exact h_Rne_zero
  )

  rw [h_simp1]
  simp only [sub_self, zero_add, gt_iff_lt]

  have h_simp2 : (↑v * ↑N * ↑(Int.bmod (↑R) N) * (↑N)⁻¹ * (↑R)⁻¹ : ℚ) = (↑v * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ : ℚ) := (calc
    (↑v * ↑N * ↑(Int.bmod (↑R) N) * (↑N)⁻¹ * (↑R)⁻¹ : ℚ) = ↑v * (↑N * (↑N)⁻¹) * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ := by ring
    _ = (↑v * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ : ℚ) := by rw [Rat.mul_inv_cancel]; simp only [mul_one]; qify at h_N; linarith
  )

  rw [h_simp2]

  have h_le : |(↑v * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ + ↑N * ↑(Int.bmod (v * round (↑R * (↑N)⁻¹)) R) * (↑R)⁻¹ : ℚ)| ≤ |(↑v * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ : ℚ)| + |(↑N * ↑(Int.bmod (v * round (↑R * (↑N)⁻¹)) R) * (↑R)⁻¹ : ℚ)| := by apply abs_add

  apply lt_of_le_of_lt h_le

  simp only [abs_mul, Nat.abs_cast]

  have h_le2: |↑v| * |↑(Int.bmod (↑R) N)| * |(↑R)⁻¹| ≤ |↑v| * (N:ℚ)/2 * |(↑R)⁻¹| := (calc
    (|↑v| * |↑(Int.bmod (↑R) N)| * |(↑R)⁻¹| : ℚ) = |↑(Int.bmod (↑R) N)| * (|↑v| * |(↑R)⁻¹|) := by ring
    _ ≤ (N:ℚ)/2 * (|↑v| * |(↑R)⁻¹|) := by
      apply mul_le_mul
      apply bmod_bounds
      exact h_N
      simp only [le_refl]
      simp only [abs_nonneg, mul_nonneg]; linarith
    _ = |↑v| * (N:ℚ)/2 * |(↑R)⁻¹| := by ring
  )

  have h_le3: ↑N * |↑(Int.bmod (v * round (↑R * (↑N)⁻¹)) R)| * |(↑R)⁻¹| ≤ ↑N * (R:ℚ)/2 * |(↑R)⁻¹| := (calc
    ↑N * |↑(Int.bmod (v * round (↑R * (↑N)⁻¹)) R)| * |(↑R)⁻¹| = |↑(Int.bmod (v * round (↑R * (↑N)⁻¹)) R)| * (↑N * |(↑R)⁻¹|) := by ring
    _ ≤ (R:ℚ)/2 * (↑N * |(↑R)⁻¹|) := by
      apply mul_le_mul
      apply bmod_bounds
      apply Nat.pos_iff_ne_zero.mpr
      exact h_Rne_zero
      simp only [le_refl]
      simp only [Nat.cast_nonneg, abs_nonneg, mul_nonneg]
      linarith
    _ = ↑N * (R:ℚ)/2 * |(↑R)⁻¹| := by ring
  )

  have h_le4:  |↑v| * |↑(Int.bmod (↑R) N)| * |(↑R)⁻¹| + ↑N * |↑(Int.bmod (v * round (↑R * (↑N)⁻¹)) R)| * |(↑R)⁻¹| ≤ |↑v| * (N:ℚ)/2 * |(↑R)⁻¹| +  ↑N * (R:ℚ)/2 * |(↑R)⁻¹| := by
    apply add_le_add h_le2 h_le3

  apply lt_of_le_of_lt h_le4

  have h_tmp: 0 < ↑N / 2 * |((↑R)⁻¹ : ℚ)| := by
    apply mul_pos_iff.mpr
    apply Or.intro_left
    apply And.intro
    ring_nf
    apply mul_pos <;> simp only [Nat.cast_pos, one_div, inv_pos, Nat.ofNat_pos]
    exact h_N
    simp only [abs_pos, ne_eq, inv_eq_zero, Nat.cast_eq_zero]
    exact h_Rne_zero

  have h_aux : (|↑v| : ℚ) * ↑N / 2 * |(↑R)⁻¹| <  |↑R| * ↑N / 2 * |(↑R)⁻¹| := (calc
     (|↑v| : ℚ) * ↑N / 2 * |(↑R)⁻¹| =  (|↑v| : ℚ) * (↑N / 2 * |(↑R)⁻¹|) := by ring
     _ <  |↑R| * (↑N / 2 * |(↑R)⁻¹|) := by
      apply mul_lt_mul
      qify at h_v
      apply lt_of_lt_of_le h_v
      . simp
      . simp
      . apply h_tmp
      . simp
     _ = |↑R| * ↑N / 2 * |(↑R)⁻¹| := by ring
  )

  have h : (|↑v| : ℚ) * ↑N / 2 * |(↑R)⁻¹| + ↑N * ↑R / 2 * |(↑R)⁻¹| < |↑R| * ↑N / 2 * |(↑R)⁻¹| + ↑N * ↑R / 2 * |(↑R)⁻¹| := by
    linarith

  apply lt_of_lt_of_le h
  field_simp
  ring_nf
  have h_simp3: (↑R * ↑N * |(↑R)⁻¹| : ℚ) = ↑N := (calc
    (↑R * ↑N * |(↑R)⁻¹| : ℚ) = ↑N * (↑R * |(↑R)⁻¹|) := by ring
    _ =  ↑N * (|↑R| * |(↑R)⁻¹|) := by simp
    _ =  ↑N * |↑R * (↑R)⁻¹| := by rw [abs_mul]
    _ = ↑N := by
      rw [Rat.mul_inv_cancel]
      simp only [abs_one, mul_one]
      qify at h_Rne_zero
      exact h_Rne_zero
  )

  rw [h_simp3]

private theorem qify_le (a b: Int) (h: (a: ℚ) < (b: ℚ)) : a < b := by
  qify
  apply h

def barrett_reduction (N: Nat) -- odd modulus
  (R: Nat) -- = 2 ^ b
  (A: Nat) -- Precomputed
  (v: Int) :=
  let k := round (((v * A) : ℚ) / R)
  let c := N * k
  let o := v - c
  o

/- Inherited from Goutam's writeup -/
def barrett_reduction_spec
  (N: Nat) -- odd modulus
  (h_N: 0 < N)
  (R: Nat) -- = 2 ^ b
  (h_R: exists b, R = 2 ^ b)
  (A: Nat) -- Precomputed
  (h_A: A = round (R / N))
  (v: Int)
  (h_v: |v| < R) :
  let o := barrett_reduction N R A v
  o % N = v % N ∧ |o| < N
:= by
  let k := round (((v * A) : ℚ) / R)
  let c := N * k
  let o := v - c

  simp +zetaDelta only [barrett_reduction]; split_conjs
  . apply ZMod_eq_imp_mod_eq -- We move to ZMod to leverage many useful lemmas there
    simp [k, c, o] -- Which are all conveniently annotated with @simp

  . apply barrett_reduction_bounds N h_N R h_R A h_A v h_v o
    simp +zetaDelta

end Symcrust
