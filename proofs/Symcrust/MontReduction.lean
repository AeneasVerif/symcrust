import Symcrust.Arith

import Aeneas

namespace Symcrust

set_option maxHeartbeats 1000000

-- We have to prove a few inequalities involving non-linear arithmetic
set_option scalarTac.nonLin true

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

end Symcrust
