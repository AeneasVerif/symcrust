import Lean
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Init.Data.Int.Bitwise.Lemmas
import Mathlib.Data.Int.Bitwise
import Aeneas

/-!
Introducing an alternative for `Nat.ofBits`: we want to manipulate lists of bits.
TODO: is this really useful?
-/

def Nat.ofBits' (bits : List Bool) : Nat := List.foldr Nat.bit 0 bits

@[simp] theorem Nat.ofBits'_nil : Nat.ofBits' [] = 0 := by simp only [ofBits', List.foldr_nil]
@[simp] theorem Nat.ofBits'_cons {bits : List Bool} :
  Nat.ofBits' (b :: bits) = Nat.bit b (ofBits' bits) := by simp only [ofBits', List.foldr_cons]

def bitRev (n : Nat) (i : Nat) : Nat :=
  -- Convert to bits
  let bits := i.bits
  -- Make sure we have n bits - note that the list of bits goes from bits
  -- of lower weight to bits of heigher weights
  let bits := bits.take n
  let bits := bits ++ List.replicate (n - bits.length) false
  -- Reverse
  let bits := List.reverse bits
  -- Convert
  Nat.ofBits' bits

#assert List.map (bitRev 2) [0, 1, 2, 3] = [0, 2, 1, 3]
#assert List.map (bitRev 3) [0, 1, 2, 3, 4, 5, 6, 7] = [0, 4, 2, 6, 1, 5, 3, 7]

theorem Nat.bits_append_bit_bodd_div2 (n : Nat) (h : n ≠ 0) :
  (bit n.bodd n.div2).bits = n.bodd :: n.div2.bits := by
  cases h: n.bodd <;> try simp_all only [ne_eq, implies_true, bits_append_bit]
  unfold bit
  simp only [cond_false]

  have := Nat.mod_two_of_bodd n

  have := Nat.bit0_bits (n / 2) (by simp_all only [Bool.toNat_false, ne_eq, Nat.div_eq_zero_iff,
    OfNat.ofNat_ne_zero, not_false_eq_true, Aeneas.Simp.neq_imp, false_or, not_lt]; omega)

  have hDiv : n.div2 = n / 2 := Nat.div2_val n
  rw [hDiv]

  simp_all only [Bool.toNat_false]

-- TODO: this should be in Mathlib
/-- This is the important reasoning theorem about `bits`, together with `Nat.zero_bits` -/
theorem Nat.bits_bit_decomp (n : Nat) (h : n ≠ 0) :
  n.bits = n.bodd :: n.div2.bits := by
  have hBit := Nat.bit_decomp n
  conv => lhs; rw [← hBit]
  simp only [Nat.bits_append_bit_bodd_div2 n h]

@[simp]
theorem Nat.ofBits'_bits (n : Nat) :
  Nat.ofBits' n.bits = n := by
  if h: n = 0 then
    simp only [ofBits', h, zero_bits, List.foldr_nil]
  else
    have hBit := Nat.bit_decomp n
    conv => lhs; rw [← hBit]

    simp only [ofBits', Nat.bits_append_bit_bodd_div2 n h, List.foldr_cons]

    have hDiv : n.div2 = n / 2 := Nat.div2_val n
    rw [hDiv]

    have hMod : n.bodd.toNat = n % 2 := by
      rw [← Nat.mod_two_of_bodd]

    have hInd := ofBits'_bits (n / 2)
    simp only [ofBits'] at hInd

    cases h:n.bodd <;> simp_all only [Bool.toNat_true, Bool.toNat_false]

@[simp]
theorem Nat.bits_div_two (n : Nat) :
  (n / 2).bits = n.bits.drop 1 := by
  dcases h: n = 0 <;> simp_all only [Nat.zero_div, zero_bits, List.drop_nil, List.drop_one]
  have := Nat.bits_bit_decomp n h
  rw [this]
  simp only [List.tail_cons]
  have hDiv : n.div2 = n / 2 := Nat.div2_val n
  rw [hDiv]

@[simp]
theorem Nat.bits_div_pow (n i : Nat) :
  (n / 2^i).bits = n.bits.drop i := by
  revert n
  induction i <;> intro n
  . simp_all only [pow_zero, Nat.div_one, List.drop_zero]
  . rename_i i hInd
    rw [Nat.pow_add_one]
    rw [← Nat.div_div_eq_div_mul]
    simp only [bits_div_two, List.drop_one]
    rw [hInd]
    simp only [List.tail_drop]

@[simp]
theorem Nat.bits_shiftRight (n i : Nat) :
  (n >>> i).bits = n.bits.drop i := by
  simp only [shiftRight_eq_div_pow, bits_div_pow]

-- TODO: move
example (n m : Nat) (hn : n < 2 ^ 12) (hm : m < 2 ^ 12):
  ((2^32 - 1 - n) >>> 16) &&& m = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h : 2^32 - 1 - n = 2^32 - (n + 1) := by simp
  rw [h]; clear h
  have := @Nat.testBit_two_pow_sub_succ n 32 (by omega) (16 + i)
  simp [-Nat.reducePow]
  rw [this]; clear this
  intro hi
  dcases hi : i < 12
  . simp; split_conjs
    . omega
    . have hi : n < 2^(16 + i) := by
        have := @Nat.pow_le_pow_of_le_right 2 (by simp) 12 (16 + i) (by omega)
        omega
      apply @Nat.testBit_eq_false_of_lt n (16 + i) hi
  . -- Contradiction
    have hi : m < 2^i := by
      have := @Nat.pow_le_pow_of_le_right 2 (by simp) 12 i (by omega)
      omega
    have := @Nat.testBit_eq_false_of_lt m i hi
    simp_all
