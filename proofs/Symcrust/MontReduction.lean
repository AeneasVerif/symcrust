import Lean
import Mathlib.Algebra.Algebra.ZMod
--import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.RingTheory.Int.Basic
--import Std.Data.Int.DivMod
--import Std.Data.Nat.Gcd
import Aesop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Qify

--import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Floor
--import Mathlib.Data.Int.Parity

import Aeneas

set_option maxHeartbeats 500000

-- We have to prove a few inequalities involving non-linear arithmetic
set_option scalarTac.nonLin true

/- In this file, "the thesis" refers to https://kannwischer.eu/thesis/phd-thesis-2023-01-03.pdf -/

-- TODO: this should be in mathlib
theorem Int.gcd_add_mul_self (a b k : ℤ) :
  Int.gcd a (b + k * a) = Int.gcd a b := by
  apply Eq.symm
  have h := @Int.gcd_greatest a (b + k * a) (Int.gcd a b) (by simp)
  simp at h
  apply h
  . apply Int.gcd_dvd_left
  . apply dvd_add
    . apply Int.gcd_dvd_right
    . rw [dvd_mul]
      exists 1, gcd a b
      simp
      apply Int.gcd_dvd_left
  . intro e div_a div_bk
    have div_ka : e ∣ k * a := by
      rw [dvd_mul]
      exists 1, e
      simp [*]
    have div_b : e ∣ b := by
      have h : e ∣ (b + k * a) + (- k * a) := by
        apply dvd_add <;> simp [*]
      simp at h
      apply h
    apply Int.dvd_gcd <;> assumption

theorem Int.gcd_mod_same {a b : ℤ} :
  Int.gcd (a % b) b = Int.gcd a b := by
  have h1 : a % b = a - b * (a / b) := by
    have heq := Int.ediv_add_emod a b
    linarith
  have h2 := Int.gcd_add_mul_self b a (- (a / b))
  rw [h1]
  simp at h2
  conv at h2 => lhs; rw [Int.gcd_comm]
  conv => rhs; rw [Int.gcd_comm]
  convert h2 using 2
  ring_nf

-- TODO: which representation should we use for the inverse?
theorem ZMod.inv_inv_eq (n : ℕ) (a : ZMod n) :
  ZMod.inv n a = a⁻¹ := by rfl

theorem ZMod.inv_cancels_left_pos {a : ℤ} {b : ℕ}
  (H_b : 0 < b)
  (H_c: Int.gcd a b = 1) :
  ((ZMod.inv b a).val * a) % b = (1 : ℤ) % b := by
  have H : NeZero b := by
    simp [neZero_iff]
    intro; linarith
  have h_one: ZMod.inv b (↑ a) * ↑ a = (1 : ZMod b) := by
    have h_r: (↑a)⁻¹ * ↑a = ZMod.inv b (↑ a) * ↑ a := by
       trivial
    rw [← h_r]
    rw [mul_comm]
    rw [ZMod.mul_inv_eq_gcd]
    rw [← Int.gcd_natCast_natCast]
    simp
    rw [ZMod.coe_intCast]
    simp [Int.gcd_mod_same, H_c]
  have h_one': ZMod.inv b (↑ a) * ↑ a = (1 : ℤ) := by
    simp [h_one]
  have h_cast : (inv b ↑a * ↑a).val = ((inv b ↑a).val : Int) * a % ↑b := by
    have h := @ZMod.coe_intCast b (((ZMod.inv b a).val : Int) * a)
    simp_all
  rw [h_one] at h_cast
  rw [← h_cast]
  have h := @ZMod.val_intCast b 1 _
  simp at h
  rw [h]

-- TODO: remove assumption that the gcd is 1
@[simp] theorem ZMod.inv_cancels_left {a : ℤ} {b : ℕ}
  (H_c: Int.gcd a b = 1) :
  ((ZMod.inv b a).val * a) % b = (1 : ℤ) % b := by
  if hb : b = 0 then
    simp [hb] at H_c
    rw [hb]; simp
    have h : a = 1 ∨ a = - 1 := by
      have h := Int.natAbs_eq a
      rw [H_c] at h
      simp at h
      apply h
    cases h <;> simp_all
    decide
    decide
  else
    have hb : 0 < b := by cases b <;> simp_all
    apply ZMod.inv_cancels_left_pos hb H_c

@[simp] theorem ZMod.inv_cancels_right {a : ℤ} {b : Nat}
  (H_c: Int.gcd a b = 1) :
  (a * (ZMod.inv b a).val) % b = (1 : ℤ) % b := by
  rw [mul_comm]
  simp [*]

-- TODO: remove?
theorem ZMod.nat_inv_cancels_left {a b : ℕ}
  (H_c: Nat.Coprime a b) :
  ((ZMod.inv b a).val * a) % b = (1 : ℤ) % b := by
  rw [Nat.coprime_iff_gcd_eq_one] at H_c
  rw [← Int.gcd_natCast_natCast] at H_c
  have h := ZMod.inv_cancels_left H_c
  simp at h
  apply h

theorem cancel_right_div_gcd_pos {m a b : ℤ}
  (c : Int) (hm : 0 < m) (hgcd : Int.gcd m c = 1)
  (h : (a * c) % m = (b * c) % m) :
  a % m = b % m := by
  have heq := Int.ModEq.cancel_right_div_gcd hm h
  simp [hgcd] at heq
  apply heq

theorem cancel_right_div_gcd {m : ℤ} (a b c : Int) (hgcd : Int.gcd m c = 1)
  (h : (a * c) % m = (b * c) % m) :
  a % m = b % m := by
  if hm : m = 0 then
    simp_all
    if hc : c = 0 then
      simp_all
    else
      simp_all
  else
    if m ≤ 0 then
      have hm' : 0 < -m := by
        -- TODO: this would be trivial with int_tac
        simp_all
        rw [lt_iff_not_ge]
        intro
        have h : m = 0 := by linarith
        simp_all
      have hgcd' : Int.gcd (-m) c = 1 := by simp [hgcd]
      have hf := @cancel_right_div_gcd_pos (-m) a b c hm' hgcd'
      simp at hf
      apply hf
      assumption
    else
      have hm : 0 < m := by simp_all
      have heq := Int.ModEq.cancel_right_div_gcd hm h
      simp [hgcd] at heq
      apply heq

theorem cancel_left_div_gcd {m : ℤ} (a b c : Int) (hgcd : Int.gcd m c = 1)
  (h : (c * a) % m = (c * b) % m) :
  a % m = b % m := by
  have heq := cancel_right_div_gcd a b c hgcd
  apply heq
  ring_nf at *
  apply h

theorem mod_mul_left (c : Int) (h : a % m = b % m):
  (c * a) % m = (c * b) % m :=
  Int.ModEq.mul_left c h

theorem mod_mul_right (c : Int) (h : a % m = b % m):
  (a * c) % m = (b * c) % m :=
  Int.ModEq.mul_right c h

theorem mod_add_left (c : Int) (h : a % m = b % m):
  (c + a) % m = (c + b) % m :=
  Int.ModEq.add_left c h

theorem mod_add_right (c : Int) (h : a % m = b % m):
  (a + c) % m = (b + c) % m :=
  Int.ModEq.add_right c h

@[simp] theorem minus_mod_eq_iff (n a b : ℤ) :
  (-a) % n = (-b) % n ↔ a % n = b % n := by
  constructor <;> intro h
  . have h := mod_add_left a h
    have h := mod_add_left b h
    ring_nf at h
    simp [h]
  . have h := mod_add_left (-a) h
    have h := mod_add_left (-b) h
    ring_nf at h
    simp [h]

@[simp] theorem minus_mod_eq_zero_iff (n a : ℤ) :
  (-a) % n = 0 ↔ a % n = 0 := by
--  have h := minus_mod_eq_iff n a 0
  simp_all

@[simp] theorem zero_eq_minus_mod_iff (n a : ℤ) :
  0 = (-a) % n ↔ 0 = a % n := by
  have h := minus_mod_eq_iff n 0 a
  simp_all

/-@[simp] theorem minus_eq (a b : ℤ) :
  - a = b ↔ a = - b := by
  sorry-/

@[simp] theorem mod_mul_mod_eq (n : ℕ) (a b : ℤ) :
  ((a % n) * b) % n = (a * b) % n := by
  simp [Int.mul_emod]

attribute [local simp] NeZero.of_pos Int.emod_eq_of_lt
-- TODO: local reducible Int.ModEq

theorem times_mod_imp_div_mod (n : ℕ) (a b c : ℤ)
  (hdiv : a % b = 0)
  (hgcd : Int.gcd n b = 1)
  (heq : a % n = (c * b) % n) :
  (a / b) % n = c % n := by
  -- step 1: multiply by b on both sides
  apply (cancel_right_div_gcd (a / b) c b (by assumption))
  -- step 2: simplify (... / b) * b
  rw [Int.ediv_mul_cancel_of_emod_eq_zero hdiv]
  -- End of the proof
  apply heq

/-
  Attempt at a different style of proofs: whenever we have to prove
  an equality between modulus, we go into ZMod.
 -/
theorem ZMod_int_cast_eq_int_cast_iff (n : ℕ) (a b : ℤ) :
  ((a : ZMod n) = (b : ZMod n)) ↔ (a % n = b % n) :=
  ZMod.intCast_eq_intCast_iff a b n

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
  ↑a * ZMod.inv n ↑a = Int.gcd a n := by
  if hn : n = 0 then
    simp [hn]
    rw [ZMod.inv_inv_eq]
    rw [ZMod.mul_inv_eq_gcd]
    simp [hn]

    have h := @ZMod.intCast_eq_intCast_iff' (ZMod.val (a : ZMod n)) (Int.natAbs a) n
    simp [hn] at h
    unfold ZMod.val
    rw [hn]
    simp
    rfl
  else
    have hn : 0 < n := by cases n <;> simp_all
    rw [ZMod.inv_inv_eq]
    rw [ZMod.mul_inv_eq_gcd]
    rw [← Int.gcd_natCast_natCast]
    have hnz : NeZero n := by simp [neZero_iff, *]
    rw [← ZMod.cast_eq_val]
    -- Simplify `↑↑a`
    rw [ZMod.coe_intCast]
    rw [Int.gcd_mod_same]

-- TODO: this rule applies a rewriting, so it can't be applied by aesop
theorem div_to_ZMod {n : ℕ} {a b : ℤ}
  (hdiv : a % b = 0) (hgcd : Int.gcd n b = 1) :
  ((a / b) : ZMod n) = (a : ZMod n) * (ZMod.inv n b) := by
  have hgcd' : Int.gcd b n = 1 := by rw [Int.gcd_comm]; apply hgcd
  have h : (a / b) % (n : Int) = ((a % (n : Int)) * (ZMod.inv n b).val) % n := by
    apply times_mod_imp_div_mod <;> try assumption
    rw [mul_assoc]
    rw [Int.mul_emod]
    rw [ZMod.inv_cancels_left] <;> try assumption
    conv => rhs; lhs; lhs; simp
    rw [← Int.mul_emod]
    simp
  have h1 := mod_eq_imp_ZMod_eq h
  rw [h1]
  simp

-- This rule is compatible with aesop (not the one above)
theorem div_to_ZMod_impl (n : ℕ) (a b : ℤ) (c : ZMod n)
  (hdiv : a % b = 0) (hgcd : Int.gcd n b = 1)
  (h : (a : ZMod n) = (b : ZMod n) * c) :
  ((a / b) : ZMod n) = c := by
  rw [div_to_ZMod] <;> try assumption
  rw [h]
  have heq : ((↑b * c * ZMod.inv n ↑b) : ZMod n) =
         (c * (↑b * ZMod.inv n ↑b)) := by ring_nf
  rw [heq]
  rw [ZMod.mul_inv_eq_int_gcd]
  rw [Int.gcd_comm]
  simp [hgcd]

theorem ZMod_inv_eq (n : ℕ) (a b c : ℤ)
  (hgcd : Int.gcd a n = 1)
  (h : (b : ZMod n) = (c : ZMod n) * (a : ZMod n)) :
  (ZMod.inv n a) * (b : ZMod n)  = (c : ZMod n) := by
  rw [h]
  have heq: ZMod.inv n ↑a * (↑c * ↑a) =
            ↑c * (↑a * ZMod.inv n ↑a) := by ring_nf
  rw [heq]
  rw [ZMod.mul_inv_eq_int_gcd]
  simp [hgcd]

-- Pushing the inverses to the left
theorem ZMod_inv_comm (n : ℕ) (a : ℤ) (b : ZMod n) :
  b * (ZMod.inv n a) = (ZMod.inv n a) * b := by
  rw [mul_comm]

-- ZMod.natCast_val
theorem test (n : Nat) [NeZero n] (x : ZMod n) : (x.val).cast = x := by
  simp [ZMod.natCast_val]

theorem Nat.NeZero_pos (n : Nat) [NeZero n] : 0 < n := by
  rename_i h
  cases h
  omega

theorem Nat.pos_NeZero {n : Nat} (h : 0 < n) : NeZero n := by
  constructor
  omega

/- Algorihm 6 from the thesis -/
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
  (h_q_R: Nat.Coprime q R) :
  let t := mont_reduction q R a minus_q_minus_1
  t % (q : Int) = (a * (ZMod.inv q R).val) % q ∧ 0 ≤ t ∧ t < 2 * q
  := by
  let f := (a * minus_q_minus_1) % R
  let t := (a + f * q) / R

  -- Having this is in the context is useful as it triggers simplifications
  have _ := Nat.pos_NeZero h_q

  -- Main goal
  have h_t: t % (q : Int) = (a * ((ZMod.inv q R).val : Int)) % q := by
    apply ZMod_eq_imp_mod_eq
    simp [f, t]
    rw [div_to_ZMod]
    . simp
    . have hZero : 0 = 0 % (R : Int) := by simp
      rw [hZero]
      apply ZMod_eq_imp_mod_eq
      simp [← ZMod_int_cast_eq_int_cast_iff] at h_q_minus_1
      simp [mul_assoc, h_q_minus_1]
    . simp [Nat.coprime_iff_gcd_eq_one, *]

  -- Secondary goals
  have h_t1 : 0 ≤ t := by scalar_tac

  have h_t2 : t < 2 * q := by
    simp [t, f] at *; clear t f
    have h': (↑a + ↑a * minus_q_minus_1 % ↑R * ↑q) < R * q + R * q := by
      apply Int.add_lt_add
      have := @Int.ofNat_lt a (q * R)
      . simp_all
        rw [Int.mul_comm]
        simp [*]
      . apply mul_lt_mul_of_pos_right
        . scalar_tac
        . simp [*]
    apply Int.ediv_lt_of_lt_mul
    . scalar_tac
    . conv => rhs; rw [Int.mul_assoc]; rhs; rw [Int.mul_comm]
      scalar_tac

  simp [mont_reduction, *]

theorem bmod_eq_emod_eq_iff (n: ℕ) (a b: ℤ) :
  (a % n = b % n) ↔ (Int.bmod a n = Int.bmod b n) := by
  simp [Int.bmod]
  apply Iff.intro <;> intro h
  . rw [h]
  . if h_a: a % n < (n + 1) / 2 then
      if h_b: b % n < (n + 1) / 2 then
        simp [h_a, h_b] at h
        exact h
      else
        simp [h_a, h_b] at h
        have ha' : 0 ≤ a % n := by apply Int.emod_nonneg; linarith
        have hb' : b % n - n < 0 := by
          have h : b % n < n := by apply Int.emod_lt_of_pos; linarith
          linarith
        linarith
    else
      if h_b: b % n < (n + 1) / 2 then
        simp [h_a, h_b] at h
        have ha' : 0 ≤ b % n := by apply Int.emod_nonneg; linarith
        have hb' : a % n - n < 0 := by
          have h : a % n < n := by apply Int.emod_lt_of_pos; linarith
          linarith
        linarith
      else
        simp [h_a, h_b] at h
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

def arr (n: ℚ) : Int := ⌊ n + 1/2 ⌋

theorem mul_cancel_eq_mul (a b c : ℚ) (h_a: 0 < a) (h: a * b = a * c) : b = c := by
  apply mul_eq_mul_left_iff.mp at h
  cases h
  . assumption
  . linarith

theorem def_ediv (a b: ℤ) : b * (a / b) = a - a % b := by
  have h: a % b + b * (a / b) = a % b + (a - a % b) := (calc
    a % b + b * (a / b) = b * (a / b) + a % b := by apply add_comm
    _ = a := by apply Int.ediv_add_emod
    _ = a % b + (a - a % b) := by field_simp
  )
  apply Int.add_left_cancel
  exact h

theorem small_emod_inj {a b:ℤ} (n:ℤ) (h_mod: a % n = b % n) (h_a: 0 ≤ a) (h_a': a < n) (h_b: 0 ≤ b) (h_b': b < n)
  : a = b := calc
  a = n * (a / n) + a % n := by apply Eq.symm; apply Int.ediv_add_emod
  _ = n * 0 + a % n := by rw [Int.ediv_eq_zero_of_lt h_a h_a']
  _ = n * 0 + b % n := by rw [h_mod]
  _ = n * (b / n) + b % n := by rw [←Int.ediv_eq_zero_of_lt h_b h_b']
  _ = b := by apply Int.ediv_add_emod


/- Lemma 9 from Goutam's writeup.
  We use the variable `x` and `m` instead of `R` and `N` in the writeup to match with
  the variables used in the definition of bmod
 -/
theorem barrett_lemma9 (x: Int) (m: Nat) (h_m: 0 < m) : arr ((x : ℚ) / m) = (x - Int.bmod x m) / (m : ℚ) := by
  /- This lemma basically consists of reconciling the definition of bmod that is now in Lean's Stdlib
     with the one from Goutam's writeup, which is based on arr above -/

  simp [Int.bmod]
  let r := x % m;
  if h: r < (m + 1) / 2 then
    simp [h]
    have h': arr ((x:ℚ) / m) = x / m := by
      simp [arr]
      field_simp
      have h_rw: (((x * 2 + m) : ℤ) : ℚ) / ((m * 2) : ℕ) = (↑x * 2 + ↑m) / (↑m * 2) := by simp

      rw [← h_rw, Rat.floor_intCast_div_natCast]; clear h_rw

      have heq := Int.ediv_add_emod (x * 2 + m) (m * 2)
      rw [Int.add_emod] at heq

      have h1 : (x * 2 % (↑m * 2) + ↑m % (↑m * 2)) % (↑m * 2) =
                2 * (x % m) + m := (calc
         (x * 2 % (↑m * 2) + ↑m % (↑m * 2)) % (↑m * 2) = (2 * (x % ↑m) + ↑m % (↑m * 2)) % (↑m * 2) := by
           have h: x * 2 % (↑m * 2) = 2 * (x % ↑m) := by
             rw [← Int.mul_emod_mul_of_pos]
             ring_nf
             simp
           rw [h]

         _ = 2 * (x % m) + m := by
           simp
           apply Int.emod_eq_of_lt
           . have h: 0 ≤ x % ↑m := by apply Int.emod_nonneg; linarith
             linarith
           . have h: 2 * (x % ↑m) < ↑m := by
               have h_bm : Int.bmod x m = x % m := by simp [Int.bmod, h]
               have h_le := @Int.bmod_le x m (by simp [h_m])
               rw [h_bm] at h_le
               apply Int.mul_le_of_le_ediv at h_le <;> simp
               linarith
             linarith
      )


      rw [h1] at heq; clear h1
      ring_nf at heq
      simp [add_assoc] at heq

      have h2 : ↑m * ((↑m + x * 2) / (↑m * 2)) * 2 + x % ↑m * 2 =
                (↑m * ((↑m + x * 2) / (↑m * 2)) + x % ↑m) * 2 := by ring_nf
      simp [h2] at heq; clear h2

      have hu := @Int.ediv_emod_unique x m (x % m) ((x * 2 + m) / (m * 2)) (by simp [h_m])
      have hu := hu.mpr
      simp at hu
      apply Eq.symm
      apply hu
      conv => rhs; rw [← heq]
      ring_nf
      . apply Int.emod_nonneg; linarith
      . apply Int.emod_lt_of_pos; simp; exact h_m
    rw [h']
    field_simp
    have h_rw: (x / m) * m = x - x % m := by rw [←def_ediv]; apply mul_comm
    qify at h_rw; exact h_rw

  else
    simp [h]

    have h': arr ((x:ℚ) / m) = (x / m) + 1 := by
      simp [arr]
      field_simp

      have h_rw : (((x * 2 + m) : ℤ) : ℚ) / ((m * 2) : ℕ) = (↑x * 2 + ↑m) / (↑m * 2) := by simp
      rw [← h_rw, Rat.floor_intCast_div_natCast]; clear h_rw

      have h_rw: x/m + 1 = (x + m) / m := by
        rw [Int.add_ediv_of_dvd_right]
        simp
        rw [Int.ediv_self]
        linarith
        apply Int.dvd_refl


      rw [h_rw]; clear h_rw

      have hu := @Int.ediv_emod_unique (x + m) m (x % m) ((x * 2 + m) / (m * 2)) (by simp [h_m])
      have hu := hu.mpr
      simp at hu
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
                rw [Int.two_mul_ediv_two_of_odd] <;> try simp
                simp at h
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
        simp [h2] at heq; clear h2
        have h2: ↑m * 2 + x * 2 = 2 * (x + ↑m) := by ring_nf
        simp [h2] at heq; clear h2
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
    ring


theorem mul_cancel_le_mul (a b c : ℚ) (h_a: 0 < a) (h: a * b ≤ a * c) : b ≤ c := by
  exact (mul_le_mul_left h_a).mp h

theorem ediv_le_add_one (x: ℤ) : (x + 1) / 2 ≤ x / 2 + 1 := by
  have h: x / 2 + 1 = (x + 2) / 2 := by
    rw [←Int.add_mul_ediv_left] <;> simp
  rw [h]
  apply Int.ediv_le_ediv <;> simp

theorem bmod_bounds (a: ℤ) (b: ℕ) (h_b: 0 < b) : |(Int.bmod a b : ℚ)| ≤ (b:ℚ)/2 := by
  apply abs_le.mpr
  apply And.intro
  . have h: - (b/2) ≤ Int.bmod a b := by
         apply Int.le_bmod; exact h_b

    qify at h
    apply le_trans ?_ h
    apply neg_le_neg

    apply mul_cancel_le_mul 2
    simp
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
    simp
    ring_nf
    have h2: (b/2) * 2 ≤ (b: ℤ) := by
      conv => rhs; rw [← (Int.ediv_add_emod b 2)]; rfl
      have h': (b: ℤ) / 2 * 2 = 2 * (↑b / 2) := by apply Int.mul_comm
      rw [h']
      apply Int.le_add_of_nonneg_right
      exact Int.le.intro_sub (b % Int.natAbs 2 + 0) rfl
    qify at h2; exact h2


theorem barrett_bounds
  (N: ℕ)
  (h_N: 0 < N)
  (R: ℕ)
  (h_R: exists b, R = 2 ^ b)
  (A: ℕ)
  (h_A: A = arr (R / N))
  (v: ℤ)
  (h_v: |v| < R)
  (o: ℤ)
  (h_o: o = (v - (N * arr ((v * A) / R))))
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
  rw [h_rw1, barrett_lemma9]
  swap; apply Nat.pos_iff_ne_zero.mpr; exact h_Rne_zero -- Why is this not handled by linarith?
  rw [h_A]

  have h_rw2 : ((R : ℤ) : ℚ) = (R : ℚ) := by simp

  qify
  rw [← h_rw2, barrett_lemma9 (↑R) (↑N)]
  swap; exact h_N
  qify
  ring_nf


  have h_simp1 : (↑v * ↑N * ↑R * (↑N)⁻¹ * (↑R)⁻¹ : ℚ) = ↑v := (calc
      (↑v * ↑N * ↑R * (↑N)⁻¹ * (↑R)⁻¹ : ℚ) = (↑v * (↑N * (↑N)⁻¹) * (↑R * (↑R)⁻¹)) := by ring
      _ = ↑v * (↑R * (↑R)⁻¹) := by rw [Rat.mul_inv_cancel]; simp; qify at h_N; linarith
      _ = ↑v := by rw [Rat.mul_inv_cancel]; simp; qify at h_Rne_zero; exact h_Rne_zero
  )

  rw [h_simp1]
  simp

  have h_simp2 : (↑v * ↑N * ↑(Int.bmod (↑R) N) * (↑N)⁻¹ * (↑R)⁻¹ : ℚ) = (↑v * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ : ℚ) := (calc
    (↑v * ↑N * ↑(Int.bmod (↑R) N) * (↑N)⁻¹ * (↑R)⁻¹ : ℚ) = ↑v * (↑N * (↑N)⁻¹) * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ := by ring
    _ = (↑v * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ : ℚ) := by rw [Rat.mul_inv_cancel]; simp; qify at h_N; linarith
  )

  rw [h_simp2]

  have h_le : |(↑v * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ + ↑N * ↑(Int.bmod (v * arr (↑R * (↑N)⁻¹)) R) * (↑R)⁻¹ : ℚ)| ≤ |(↑v * ↑(Int.bmod (↑R) N) * (↑R)⁻¹ : ℚ)| + |(↑N * ↑(Int.bmod (v * arr (↑R * (↑N)⁻¹)) R) * (↑R)⁻¹ : ℚ)| := by apply abs_add

  apply lt_of_le_of_lt h_le

  simp [abs_mul]

  have h_le2: |↑v| * |↑(Int.bmod (↑R) N)| * |(↑R)⁻¹| ≤ |↑v| * (N:ℚ)/2 * |(↑R)⁻¹| := (calc
    (|↑v| * |↑(Int.bmod (↑R) N)| * |(↑R)⁻¹| : ℚ) = |↑(Int.bmod (↑R) N)| * (|↑v| * |(↑R)⁻¹|) := by ring
    _ ≤ (N:ℚ)/2 * (|↑v| * |(↑R)⁻¹|) := by apply mul_le_mul; apply bmod_bounds; exact h_N; simp; simp [mul_nonneg]; linarith
    _ = |↑v| * (N:ℚ)/2 * |(↑R)⁻¹| := by ring
  )

  have h_le3: ↑N * |↑(Int.bmod (v * arr (↑R * (↑N)⁻¹)) R)| * |(↑R)⁻¹| ≤ ↑N * (R:ℚ)/2 * |(↑R)⁻¹| := (calc
    ↑N * |↑(Int.bmod (v * arr (↑R * (↑N)⁻¹)) R)| * |(↑R)⁻¹| = |↑(Int.bmod (v * arr (↑R * (↑N)⁻¹)) R)| * (↑N * |(↑R)⁻¹|) := by ring
    _ ≤ (R:ℚ)/2 * (↑N * |(↑R)⁻¹|) := by apply mul_le_mul; apply bmod_bounds; apply Nat.pos_iff_ne_zero.mpr; exact h_Rne_zero; simp; simp [mul_nonneg]; linarith
    _ = ↑N * (R:ℚ)/2 * |(↑R)⁻¹| := by ring
  )

  have h_le4:  |↑v| * |↑(Int.bmod (↑R) N)| * |(↑R)⁻¹| + ↑N * |↑(Int.bmod (v * arr (↑R * (↑N)⁻¹)) R)| * |(↑R)⁻¹| ≤ |↑v| * (N:ℚ)/2 * |(↑R)⁻¹| +  ↑N * (R:ℚ)/2 * |(↑R)⁻¹| := by
    apply add_le_add h_le2 h_le3

  apply lt_of_le_of_lt h_le4

  have h_tmp: 0 < ↑N / 2 * |((↑R)⁻¹ : ℚ)| := by
    apply mul_pos_iff.mpr
    apply Or.intro_left
    apply And.intro
    ring_nf
    apply mul_pos <;> simp
    exact h_N
    simp
    exact h_Rne_zero

  have h_aux : (|↑v| : ℚ) * ↑N / 2 * |(↑R)⁻¹| <  |↑R| * ↑N / 2 * |(↑R)⁻¹| := (calc
     (|↑v| : ℚ) * ↑N / 2 * |(↑R)⁻¹| =  (|↑v| : ℚ) * (↑N / 2 * |(↑R)⁻¹|) := by ring
     _ <  |↑R| * (↑N / 2 * |(↑R)⁻¹|) := by apply mul_lt_mul; qify at h_v; apply lt_of_lt_of_le h_v; simp; simp; apply h_tmp; simp
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
    _ = ↑N := by rw [Rat.mul_inv_cancel]; simp; qify at h_Rne_zero; exact h_Rne_zero
  )

  rw [h_simp3]

theorem qify_le (a b: Int) (h: (a: ℚ) < (b: ℚ)) : a < b := by
  qify
  apply h

/- Inherited from Goutam's writeup -/
def barrett_reduction
  (N: Nat) -- odd modulus
  (h_N: 0 < N)
  (R: Nat) -- = 2 ^ b
  (h_R: exists b, R = 2 ^ b)
  (A: Nat) -- Precomputed
  (h_A: A = arr (R / N))
  (v: Int)
  (h_v: |v| < R) :
  { o: Int // o % N = v % N ∧ |o| < N }
:=
  let k := arr (((v * A) : ℚ) / R)
  let c := N * k
  let o := v - c

  have h_o : o % N = v % N := by
    simp [o]
    apply ZMod_eq_imp_mod_eq -- We move to ZMod to leverage many useful lemmas there
    simp [k, c, o] -- Which are all conveniently annotated with @simp

  /- We do this proof in the external barrett_bounds lemma -/
  have h1: |o| < N := by
    apply barrett_bounds N h_N R h_R A h_A v h_v o
    simp

  ⟨ o, ⟨ h_o, h1 ⟩ ⟩
