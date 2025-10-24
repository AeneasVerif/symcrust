import Mathlib.Tactic.Qify
import Mathlib.Data.Rat.Floor

import Aeneas

namespace Symcrust

open Aeneas.Arith

set_option maxHeartbeats 1000000

/-- The rounding of `x` to the nearest integer.
    If `x = y + 1/2` for some `y ∈ ℤ` then `round(x) = y + 1`
 -/
def round (x: ℚ) : Int := ⌊ x + 1/2 ⌋

theorem def_ediv (a b: ℤ) : b * (a / b) = a - a % b := by
  have h: a % b + b * (a / b) = a % b + (a - a % b) := (calc
    a % b + b * (a / b) = b * (a / b) + a % b := by apply add_comm
    _ = a := by apply Int.ediv_add_emod
    _ = a % b + (a - a % b) := by simp
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

private theorem barrett_reduce_lemma (x: Int) (m: Nat) (h_m: 0 < m) :
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
          . scalar_tac +nonLin
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
      simp only [Int.add_emod_right, and_true, and_imp] at hu
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
              (x * 2 % (↑m * 2) + ↑m % (↑m * 2)) % (↑m * 2) % (↑m * 2) = ((x * 2) % (↑m * 2) + ↑m) % (↑m * 2) := by simp
              _ = (2 * (x % m) + m) % (m * 2) := by
                have h_rw: (x * 2) % (↑m * 2) = (2 * x) % (2 * m) := by ring_nf
                rw [h_rw] -- Need to put in the write form to apply Int.mul_emod_mul_of_pos, which is @simp
                simp
            )
            rw [h_rw]; clear h_rw
            apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
            ring_nf
            simp
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
    simp [field]
    rw [add_mul]
    simp
    have h_rw: (x / m) * m = x - x % m := by rw [←def_ediv]; apply mul_comm
    qify at h_rw; rw [h_rw]
    ring_nf

private theorem mul_cancel_le_mul (a b c : ℚ) (h_a: 0 < a) (h: a * b ≤ a * c) : b ≤ c := by
  exact (mul_le_mul_iff_right₀ h_a).mp h

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

private theorem barrett_reduce_bounds
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
  rw [h_rw1, barrett_reduce_lemma]
  swap; omega
  rw [h_A]

  have h_rw2 : ((R : ℤ) : ℚ) = (R : ℚ) := by simp

  qify
  rw [← h_rw2, barrett_reduce_lemma (↑R) (↑N)]
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
  simp
  ring_nf
  have h_simp3: (↑N * ↑R * (↑R)⁻¹ : ℚ) = ↑N := (calc
    (↑N * ↑R * (↑R)⁻¹ : ℚ) = ↑N * (↑R * (↑R)⁻¹) := by ring
    _ =  ↑N * (|↑R| * |(↑R)⁻¹|) := by simp
    _ =  ↑N * |↑R * (↑R)⁻¹| := by rw [abs_mul]
    _ = ↑N := by
      rw [Rat.mul_inv_cancel]
      simp only [abs_one, mul_one]
      qify at h_Rne_zero
      exact h_Rne_zero
  )

  simp [h_simp3]

private theorem qify_le (a b: Int) (h: (a: ℚ) < (b: ℚ)) : a < b := by
  qify
  apply h

def barrett_reduce (N: Nat) -- odd modulus
  (R: Nat) -- = 2 ^ b
  (A: Nat) -- Precomputed
  (v: Int) :=
  let k := round (((v * A) : ℚ) / R)
  let c := N * k
  let o := v - c
  o

/- Inherited from Goutam's writeup -/
def barrett_reduce_spec
  (N: Nat) -- odd modulus
  (h_N: 0 < N)
  (R: Nat) -- = 2 ^ b
  (h_R: exists b, R = 2 ^ b)
  (A: Nat) -- Precomputed
  (h_A: A = round (R / N))
  (v: Int)
  (h_v: |v| < R) :
  let o := barrett_reduce N R A v
  o % N = v % N ∧ |o| < N
:= by
  let k := round (((v * A) : ℚ) / R)
  let c := N * k
  let o := v - c

  simp +zetaDelta only [barrett_reduce]; split_conjs
  . apply ZMod_eq_imp_mod_eq -- We move to ZMod to leverage many useful lemmas there
    simp -- Which are all conveniently annotated with @simp

  . apply barrett_reduce_bounds N h_N R h_R A h_A v h_v o
    simp +zetaDelta

end Symcrust
