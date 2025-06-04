import Mathlib.Data.Nat.Bits
import Mathlib.Data.Rat.Floor

namespace Aeneas

def rat_round (x : ℚ) : Int := ⌊x + 1/2⌋
notation:max "⌈ " x " ⌋" => rat_round x

theorem Nat.rat_round_div (x y : ℕ) (hy : y ≠ 0) : ⌈ (x : ℚ) / (y : ℚ) ⌋ = (2 * x + y) / (2 * y) := by
  simp only [rat_round]
  have : (x : ℚ) / y + 1 / 2 = ((2 * x + y : ℕ) : ℚ) / ((2 * y : ℕ) : ℚ) := by
    simp; ring_nf; simp [*]; ring_nf
  rw [this]
  rw [Rat.floor_natCast_div_natCast]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

end Aeneas
