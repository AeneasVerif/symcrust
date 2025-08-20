import Symcrust.Spec
import Symcrust.Code.Funs
import Symcrust.Brute
import Symcrust.Properties.SamplePolyCBD.Target2Code
import Symcrust.Properties.SamplePolyCBD.Target2HelperLemmas

/-!
This file contains theorems about `Symcrust.Spec.samplePolyCBD` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to Algorithm 8 (SamplePolyCBD).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.samplePolyCBD`.
    - `Lean spec (functional)` corresponds to `Target.samplePolyCBD`.
      - The theorem that mathematically characterizes `Target.samplePolyCBD` is `Target.samplePolyCBD.spec`.
    - `Auxiliary spec` corresponds to `Target2.samplePolyCBD`.
    - `⟷₂` corresponds to `Target.samplePolyCBD.eq_spec`.
    - Analogues for later portions of the verification pipeline appear in other files.

  `Target2.samplePolyCBD.eta2_loop.spec` (which is the critical theorem in this file) proves `⟷₃` when `η = 2`.

  **Note** although the various `Target2.samplePolyCBD.eta2_loop.spec.aux_` lemmas appear to be extremely similar,
  there are enough minor changes to the indices that appear in the arguments that there is not a convenient way
  to combine all of these lemmas into one parameterized theorem.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.Std Aeneas.SRRange

set_option maxHeartbeats 1000000

def Target2.samplePolyCBD.eta2_loop.inner_loop_unrolled.preserves_below (pe_dst : Polynomial) (i : ℕ)
  (sample_bits : BitVec 32) (k : ℕ) (hk : k < i) :
  (eta2_loop.inner_loop_unrolled pe_dst i sample_bits).1[k]! = pe_dst[k]! := by
  unfold inner_loop_unrolled
  simp_lists [Q]

def Target2.samplePolyCBD.eta2_loop.inner_loop_unrolled.preserves_above (pe_dst : Polynomial) (i : ℕ)
  (sample_bits : BitVec 32) (k : ℕ) (hk : i + 7 < k) :
  (eta2_loop.inner_loop_unrolled pe_dst i sample_bits).1[k]! = pe_dst[k]! := by
  unfold inner_loop_unrolled
  simp_lists [Q]

def Target2.samplePolyCBD.eta2_loop.inner_loop.equals_unrolled (pe_dst : Polynomial) (i : ℕ)
  (sample_bits : BitVec 32) : inner_loop pe_dst i 0 sample_bits = inner_loop_unrolled pe_dst i sample_bits := by
  simp [inner_loop, inner_loop_unrolled]

lemma Fin.unfold2 {α} [AddCommMonoid α] {n : Nat} (hn : n = 2) (f : Fin n → α) :
  ∑ x : Fin n, f x = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  rw [Finset.sum, Multiset.map, Multiset.sum, Finset.univ, Fintype.elems, Fin.fintype]
  simp only [List.finRange, List.ofFn, Fin.foldr, hn, Fin.foldr.loop, Multiset.lift_coe, List.map_cons,
    List.map_nil, Multiset.coe_foldr, List.foldr_cons, List.foldr_nil, add_zero, add_assoc]

lemma shiftDistribMask1431655765Core {x y : BitVec 64} (shift : Nat) (hs : shift ∈ [0,4,8,12,16,20,24,28])
  (k : Nat) (hk : k ∈ [0,1,2,3]) :
  (((x &&& 1431655765#64) + (y &&& 1431655765#64)) >>> shift) &&& BitVec.ofNat 64 (2^k : Nat) =
  ((x &&& 1431655765#64) >>> shift + (y &&& 1431655765#64) >>> shift) &&& BitVec.ofNat 64 (2^k : Nat) := by
  simp at hs hk
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs <;>
  rcases hk with hk | hk | hk | hk <;>
  simp [hs, hk] <;> bv_decide

/-- Distributing `>>>` over `+` is not valid in general, but this lemma is true because
    of the masks applied to `x` and `y`. -/
lemma shiftDistribMask1431655765 {x y shift k : ℕ} (hx : x < 2^64) (hy : y < 2^64)
  (hShift1 : 4 ∣ shift) (hShift2 : shift < 29) (hk : k < 4) :
  (((x &&& 1431655765) + (y &&& 1431655765)) >>> shift).testBit k =
  ((x &&& 1431655765) >>> shift + (y &&& 1431655765) >>> shift).testBit k := by
  have hk : k ∈ [0,1,2,3] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hs : shift ∈ [0,4,8,12,16,20,24,28] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  -- **TODO** Modify `bvify` so that `bvify` can automate the following rewrites
  have h1 : (x &&& 1431655765) = BitVec.toNat ((BitVec.ofNat 64 x &&& 1431655765#64)) := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt]
    omega
  have h2 : (y &&& 1431655765) = BitVec.toNat ((BitVec.ofNat 64 y &&& 1431655765#64)) := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt]
    omega
  have h3 : (BitVec.ofNat 64 x &&& 1431655765#64).toNat + (BitVec.ofNat 64 y &&& 1431655765#64).toNat =
    ((BitVec.ofNat 64 x &&& 1431655765#64) + (BitVec.ofNat 64 y &&& 1431655765#64)).toNat := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, BitVec.toNat_add]
    have : x &&& 1431655765 ≤ 1431655765 := Nat.and_le_right
    have : y &&& 1431655765 ≤ 1431655765 := Nat.and_le_right
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> omega
  have h4 :
    (((BitVec.ofNat 64 x &&& 1431655765#64) >>> shift).toNat +
     ((BitVec.ofNat 64 y &&& 1431655765#64) >>> shift).toNat) =
    (((BitVec.ofNat 64 x &&& 1431655765#64) >>> shift) +
     ((BitVec.ofNat 64 y &&& 1431655765#64) >>> shift)).toNat := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, BitVec.toNat_add]
    have : x &&& 1431655765 ≤ 1431655765 := Nat.and_le_right
    have : y &&& 1431655765 ≤ 1431655765 := Nat.and_le_right
    have : (x &&& 1431655765) >>> shift ≤ (x &&& 1431655765) := Nat.shiftRight_le _ _
    have : (y &&& 1431655765) >>> shift ≤ (y &&& 1431655765) := Nat.shiftRight_le _ _
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> omega
  rw [h1, h2, h3, ← BitVec.toNat_ushiftRight, ← BitVec.toNat_ushiftRight, ← BitVec.toNat_ushiftRight, h4,
    ← BitVec.getElem!_eq_testBit_toNat, ← BitVec.getElem!_eq_testBit_toNat, BitVec.getElem!_eq_mask_ne_zero,
    BitVec.getElem!_eq_mask_ne_zero, shiftDistribMask1431655765Core] <;> omega

/-- Each `Target2.samplePolyCBD.eta2_loop.spec.aux_` theorem is intended to prove the same basic result. The
    difference between them is `hj3` and the index of `(Target.bytesToBits BVector)` referenced in the goal.
    For `Target2.samplePolyCBD.eta2_loop.spec.aux_`, `hj3` states that `j = s.i + _` and the index of
    `(Target.bytesToBits BVector)` referenced in the goal is `2 * (s.i + _) * ↑s.η + ↑x`

    Because the indices change for each `Target2.samplePolyCBD.eta2_loop.spec.aux_`, the proofs themselves
    have minor differences (such as the values which `hBytesToBits` is instantiated with) but the overall
    structure of the proofs is shared. -/
theorem Target2.samplePolyCBD.eta2_loop.spec.aux0 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!) (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4) (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i) (hη : s.η.val = 2)
  (hs6 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS) (j : ℕ) (hj1 : j < s.i + 8) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i) :
  (↑↑(inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).2 : ZMod 3329) =
    ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * s.i * s.η.val + x.val]!.toNat -
      ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * s.i * s.η.val + s.η.val + x.val]!.toNat := by
  simp only [hη, Nat.mul_assoc 2 s.i 2, Nat.mul_comm s.i 2, ← Nat.mul_assoc 2 2 s.i, Nat.reduceMul,
    Nat.mul_comm 4 s.i, ← hs3, Fin.unfold2, Nat.mul_comm s.src_i 8]
  specialize hBytesToBits s.src_i (by scalar_tac)
  rw [hBytesToBits 0 (by omega), hBytesToBits 1 (by omega), hBytesToBits 2 (by omega), hBytesToBits 3 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_add_mod]
  olet hsample_bits_slice : sample_bits_slice := sample_bits.toNat % 4294967296 &&& 15
  olet hs_B_byte : s_B_byte := s.B[s.src_i]!
  replace hs_B_byte : sample_bits_slice = (s_B_byte &&& 5) + ((s_B_byte >>> 1) &&& 5) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' <;> (try rw [hmin]; decide +native)
    have hy'' : y' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 15#8 = 2#8^4 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 4
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 (x' + y') k (by omega), Nat.mod_eq_of_lt]
        . apply testBitOfAdd 4 _ _ k hk2
          . intro i hi
            simp only [hx', hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . simp_scalar
              congr 1
              revert i
              decide
            . scalar_tac
          . intro i hi
            simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . simp_scalar
              congr 1
              revert i
              decide
            . scalar_tac
        . have : (BitVec.toNat s_B_byte &&& 5) ≤ 5 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 1) &&& 5 ≤ 5 := Nat.and_le_right
          omega
      . have : (s_B_byte &&& 5#8) + (s_B_byte >>> 1 &&& 5#8) < 2^4 := by
          clear hs_B_byte hBytesToBits
          revert s_B_byte
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 16 = 2^4), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 16 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

/-- Each `Target2.samplePolyCBD.eta2_loop.spec.aux_` theorem is intended to prove the same basic result. The
    difference between them is `hj3` and the index of `(Target.bytesToBits BVector)` referenced in the goal.
    For `Target2.samplePolyCBD.eta2_loop.spec.aux_`, `hj3` states that `j = s.i + _` and the index of
    `(Target.bytesToBits BVector)` referenced in the goal is `2 * (s.i + _) * ↑s.η + ↑x`

    Because the indices change for each `Target2.samplePolyCBD.eta2_loop.spec.aux_`, the proofs themselves
    have minor differences (such as the values which `hBytesToBits` is instantiated with) but the overall
    structure of the proofs is shared. -/
theorem Target2.samplePolyCBD.eta2_loop.spec.aux1 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!) (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4) (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i) (hη : s.η.val = 2)
  (hs6 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS) (j : ℕ) (hj1 : j < s.i + 8) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 1) :
  (↑↑(inner_loop.next_coefficient s.i 1
    (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).2 : ZMod 3329) =
    ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 1) * ↑s.η + ↑x]!.toNat -
      ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 1) * ↑s.η + ↑s.η + ↑x]!.toNat := by
  simp only [hη, Nat.mul_assoc 2 (s.i + 1) 2, Nat.mul_comm (s.i + 1) 2, ← Nat.mul_assoc 2 2 (s.i + 1),
    Nat.reduceMul, Nat.mul_add 4, Nat.mul_comm 4 s.i, ← hs3, Fin.unfold2, Nat.mul_comm s.src_i 8]
  conv in 8 * s.src_i + 4 + 0 => rw [(by omega : 8 * s.src_i + 4 + 0 = 8 * s.src_i + 4)]
  conv in 8 * s.src_i + 4 + 1 => rw [(by omega : 8 * s.src_i + 4 + 1 = 8 * s.src_i + 5)]
  conv in 8 * s.src_i + 4 + 2 + 0 => rw [(by omega : 8 * s.src_i + 4 + 2 + 0 = 8 * s.src_i + 6)]
  conv in 8 * s.src_i + 4 + 2 + 1 => rw [(by omega : 8 * s.src_i + 4 + 2 + 1 = 8 * s.src_i + 7)]
  rw [hBytesToBits s.src_i (by scalar_tac) 4 (by omega),
      hBytesToBits s.src_i (by scalar_tac) 5 (by omega),
      hBytesToBits s.src_i (by scalar_tac) 6 (by omega),
      hBytesToBits s.src_i (by scalar_tac) 7 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_add_mod]
  olet hsample_bits_slice : sample_bits_slice := (sample_bits.toNat % 4294967296) >>> 4 &&& 15
  olet hs_B_byte : s_B_byte := s.B[s.src_i]!
  replace hs_B_byte : sample_bits_slice = (s_B_byte >>> 4 &&& 5) + ((s_B_byte >>> 5) &&& 5) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' <;> (try rw [hmin]; decide +native)
    have hy'' : y' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 15#8 = 2#8^4 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 4
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 ((x' + y') >>> 4) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hy, shiftDistribMask1431655765 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hy, ← hy', ← hx']
          apply testBitOfAdd 4 _ _ k hk2
          . intro i hi
            simp only [hx', hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . simp_scalar
              congr 1
              revert i
              decide
            . scalar_tac
          . intro i hi
            simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            by_cases hi2 : i < 3
            . rw [(by omega : (1 + (4 + i)) / 8 = 0), (by omega : (1 + (4 + i)) % 8 = 5 + i),
                List.getElem!_slice, hs_B_byte, Array.getElem!_toList, Nat.add_zero]
              . congr 1
                revert i
                decide
              . scalar_tac
            . have h1 : Nat.testBit 1431655765 (4 + i) = false := by revert i; decide
              have h2 : Nat.testBit 5 i = false := by revert i; decide
              simp only [h1, Bool.and_false, h2]
        . have : (BitVec.toNat s_B_byte >>> 4) &&& 5 ≤ 5 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 5) &&& 5 ≤ 5 := Nat.and_le_right
          omega
      . have : (s_B_byte >>> 4 &&& 5#8) + (s_B_byte >>> 5 &&& 5#8) < 2^4 := by
          clear hs_B_byte hBytesToBits
          revert s_B_byte
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 16 = 2^4), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 16 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

/-- Each `Target2.samplePolyCBD.eta2_loop.spec.aux_` theorem is intended to prove the same basic result. The
    difference between them is `hj3` and the index of `(Target.bytesToBits BVector)` referenced in the goal.
    For `Target2.samplePolyCBD.eta2_loop.spec.aux_`, `hj3` states that `j = s.i + _` and the index of
    `(Target.bytesToBits BVector)` referenced in the goal is `2 * (s.i + _) * ↑s.η + ↑x`

    Because the indices change for each `Target2.samplePolyCBD.eta2_loop.spec.aux_`, the proofs themselves
    have minor differences (such as the values which `hBytesToBits` is instantiated with) but the overall
    structure of the proofs is shared. -/
theorem Target2.samplePolyCBD.eta2_loop.spec.aux2 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!) (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4) (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i) (hη : s.η.val = 2)
  (hs6 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS) (j : ℕ) (hj1 : j < s.i + 8) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 2) :
  (↑↑(inner_loop.next_coefficient s.i 2
          (inner_loop.next_coefficient s.i 1
              (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).2 : ZMod 3329) =
    ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 2) * ↑s.η + ↑x]!.toNat -
      ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 2) * ↑s.η + ↑s.η + ↑x]!.toNat := by
  simp only [hη, Nat.mul_assoc 2 (s.i + 2) 2, Nat.mul_comm (s.i + 2) 2, ← Nat.mul_assoc 2 2 (s.i + 2),
    Nat.reduceMul, Nat.mul_add 4, Nat.mul_comm 4 s.i, ← hs3, Fin.unfold2, Nat.mul_comm s.src_i 8]
  conv in 8 * s.src_i + 8 + 0 => rw [(by omega : 8 * s.src_i + 8 + 0 = 8 * (s.src_i + 1) + 0)]
  conv in 8 * s.src_i + 8 + 1 => rw [(by omega : 8 * s.src_i + 8 + 1 = 8 * (s.src_i + 1) + 1)]
  conv in 8 * s.src_i + 8 + 2 + 0 => rw [(by omega : 8 * s.src_i + 8 + 2 + 0 = 8 * (s.src_i + 1) + 2)]
  conv in 8 * s.src_i + 8 + 2 + 1 => rw [(by omega : 8 * s.src_i + 8 + 2 + 1 = 8 * (s.src_i + 1) + 3)]
  rw [hBytesToBits (s.src_i + 1) (by scalar_tac) 0 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 1 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 2 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 3 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat, Nat.reduceAdd,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_add_mod, ← Nat.shiftRight_add]
  olet hsample_bits_slice : sample_bits_slice := (sample_bits.toNat % 4294967296) >>> 8 &&& 15
  olet hs_B_byte : s_B_byte := s.B[s.src_i + 1]!
  replace hs_B_byte : sample_bits_slice = (s_B_byte &&& 5) + ((s_B_byte >>> 1) &&& 5) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' <;> (try rw [hmin]; decide +native)
    have hy'' : y' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 15#8 = 2#8^4 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 4
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 ((x' + y') >>> 8) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hy, shiftDistribMask1431655765 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hy, ← hy', ← hx']
          apply testBitOfAdd 4 _ _ k hk2
          . intro i hi
            simp only [hx', hx, Nat.testBit_shiftRight, Nat.testBit_and, ←
              BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!, Nat.ofNat_pos,
              Nat.add_div_left, Nat.add_mod_left]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . simp_scalar
              congr 1
              revert i
              decide
            . scalar_tac
          . intro i hi
            simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [(by omega : (1 + (8 + i)) / 8 = 1), (by omega : (1 + (8 + i)) % 8 = 1 + i),
              List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . congr 1
              revert i
              decide
            . scalar_tac
        . have : BitVec.toNat s_B_byte &&& 5 ≤ 5 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 1) &&& 5 ≤ 5 := Nat.and_le_right
          omega
      . have : (s_B_byte &&& 5#8) + (s_B_byte >>> 1 &&& 5#8) < 2^4 := by
          clear hs_B_byte hBytesToBits
          revert s_B_byte
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 16 = 2^4), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 16 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

/-- Each `Target2.samplePolyCBD.eta2_loop.spec.aux_` theorem is intended to prove the same basic result. The
    difference between them is `hj3` and the index of `(Target.bytesToBits BVector)` referenced in the goal.
    For `Target2.samplePolyCBD.eta2_loop.spec.aux_`, `hj3` states that `j = s.i + _` and the index of
    `(Target.bytesToBits BVector)` referenced in the goal is `2 * (s.i + _) * ↑s.η + ↑x`

    Because the indices change for each `Target2.samplePolyCBD.eta2_loop.spec.aux_`, the proofs themselves
    have minor differences (such as the values which `hBytesToBits` is instantiated with) but the overall
    structure of the proofs is shared. -/
theorem Target2.samplePolyCBD.eta2_loop.spec.aux3 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!) (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4) (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i) (hη : s.η.val = 2)
  (hs6 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS) (j : ℕ) (hj1 : j < s.i + 8) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 3) :
  (↑↑(inner_loop.next_coefficient s.i 3
          (inner_loop.next_coefficient s.i 2
              (inner_loop.next_coefficient s.i 1
                  (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).1).2 : ZMod 3329) =
    ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 3) * ↑s.η + ↑x]!.toNat -
      ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 3) * ↑s.η + ↑s.η + ↑x]!.toNat := by
  simp only [hη, Nat.mul_assoc 2 (s.i + 3) 2, Nat.mul_comm (s.i + 3) 2, ← Nat.mul_assoc 2 2 (s.i + 3),
    Nat.reduceMul, Nat.mul_add 4, Nat.mul_comm 4 s.i, ← hs3, Fin.unfold2, Nat.mul_comm s.src_i 8]
  conv in 8 * s.src_i + 12 + 0 => rw [(by omega : 8 * s.src_i + 12 + 0 = 8 * (s.src_i + 1) + 4)]
  conv in 8 * s.src_i + 12 + 1 => rw [(by omega : 8 * s.src_i + 12 + 1 = 8 * (s.src_i + 1) + 5)]
  conv in 8 * s.src_i + 12 + 2 + 0 => rw [(by omega : 8 * s.src_i + 12 + 2 + 0 = 8 * (s.src_i + 1) + 6)]
  conv in 8 * s.src_i + 12 + 2 + 1 => rw [(by omega : 8 * s.src_i + 12 + 2 + 1 = 8 * (s.src_i + 1) + 7)]
  rw [hBytesToBits (s.src_i + 1) (by scalar_tac) 4 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 5 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 6 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 7 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat, Nat.reduceAdd,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_add_mod, ← Nat.shiftRight_add]
  olet hsample_bits_slice : sample_bits_slice := (sample_bits.toNat % 4294967296) >>> 12 &&& 15
  olet hs_B_byte : s_B_byte := s.B[s.src_i + 1]!
  replace hs_B_byte : sample_bits_slice = ((s_B_byte >>> 4) &&& 5) + ((s_B_byte >>> 5) &&& 5) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' <;> (try rw [hmin]; decide +native)
    have hy'' : y' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 15#8 = 2#8^4 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 4
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 ((x' + y') >>> 12) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hy, shiftDistribMask1431655765 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hy, ← hy', ← hx']
          apply testBitOfAdd 4 _ _ k hk2
          . intro i hi
            simp only [hx', hx, Nat.testBit_shiftRight, Nat.testBit_and,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . rw [(by omega : (12 + i) / 8 = 1), (by omega : (12 + i) % 8 = 4 + i)]
              simp_scalar
              congr 1
              revert i
              decide
            . scalar_tac
          . intro i hi
            simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            by_cases hi2 : i < 3
            . rw [(by omega : (1 + (12 + i)) / 8 = 1), (by omega : (1 + (12 + i)) % 8 = 5 + i),
                List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
              . congr 1
                revert i
                decide
              . scalar_tac
            . have h1 : Nat.testBit 1431655765 (12 + i) = false := by revert i; decide
              have h2 : Nat.testBit 5 i = false := by revert i; decide
              simp only [h1, Bool.and_false, h2]
        . have : (BitVec.toNat s_B_byte >>> 4) &&& 5 ≤ 5 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 5) &&& 5 ≤ 5 := Nat.and_le_right
          omega
      . have : (s_B_byte >>> 4 &&& 5#8) + (s_B_byte >>> 5 &&& 5#8) < 2^4 := by
          clear hs_B_byte hBytesToBits
          revert s_B_byte
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 16 = 2^4), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 16 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

/-- Each `Target2.samplePolyCBD.eta2_loop.spec.aux_` theorem is intended to prove the same basic result. The
    difference between them is `hj3` and the index of `(Target.bytesToBits BVector)` referenced in the goal.
    For `Target2.samplePolyCBD.eta2_loop.spec.aux_`, `hj3` states that `j = s.i + _` and the index of
    `(Target.bytesToBits BVector)` referenced in the goal is `2 * (s.i + _) * ↑s.η + ↑x`

    Because the indices change for each `Target2.samplePolyCBD.eta2_loop.spec.aux_`, the proofs themselves
    have minor differences (such as the values which `hBytesToBits` is instantiated with) but the overall
    structure of the proofs is shared. -/
theorem Target2.samplePolyCBD.eta2_loop.spec.aux4 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!) (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4) (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i) (hη : s.η.val = 2)
  (hs6 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS) (j : ℕ) (hj1 : j < s.i + 8) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 4) :
  (↑↑(inner_loop.next_coefficient s.i 4
          (inner_loop.next_coefficient s.i 3
              (inner_loop.next_coefficient s.i 2
                  (inner_loop.next_coefficient s.i 1
                      (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).1).1).2 : ZMod 3329) =
    ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 4) * ↑s.η + ↑x]!.toNat -
      ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 4) * ↑s.η + ↑s.η + ↑x]!.toNat := by
  simp only [hη, Nat.mul_assoc 2 (s.i + 4) 2, Nat.mul_comm (s.i + 4) 2, ← Nat.mul_assoc 2 2 (s.i + 4),
    Nat.reduceMul, Nat.mul_add 4, Nat.mul_comm 4 s.i, ← hs3, Fin.unfold2, Nat.mul_comm s.src_i 8]
  conv in 8 * s.src_i + 16 + 0 => rw [(by omega : 8 * s.src_i + 16 + 0 = 8 * (s.src_i + 2) + 0)]
  conv in 8 * s.src_i + 16 + 1 => rw [(by omega : 8 * s.src_i + 16 + 1 = 8 * (s.src_i + 2) + 1)]
  conv in 8 * s.src_i + 16 + 2 + 0 => rw [(by omega : 8 * s.src_i + 16 + 2 + 0 = 8 * (s.src_i + 2) + 2)]
  conv in 8 * s.src_i + 16 + 2 + 1 => rw [(by omega : 8 * s.src_i + 16 + 2 + 1 = 8 * (s.src_i + 2) + 3)]
  rw [hBytesToBits (s.src_i + 2) (by scalar_tac) 0 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 1 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 2 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 3 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat, Nat.reduceAdd,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_add_mod, ← Nat.shiftRight_add]
  olet hsample_bits_slice : sample_bits_slice := (sample_bits.toNat % 4294967296) >>> 16 &&& 15
  olet hs_B_byte : s_B_byte := s.B[s.src_i + 2]!
  replace hs_B_byte : sample_bits_slice = (s_B_byte &&& 5) + ((s_B_byte >>> 1) &&& 5) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' <;> (try rw [hmin]; decide +native)
    have hy'' : y' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 15#8 = 2#8^4 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 4
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 ((x' + y') >>> 16) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hy, shiftDistribMask1431655765 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hy, ← hy', ← hx']
          apply testBitOfAdd 4 _ _ k hk2
          . intro i hi
            simp only [hx', hx, Nat.testBit_shiftRight, Nat.testBit_and, ←
              BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!, Nat.ofNat_pos,
              Nat.add_div_left, Nat.add_mod_left]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . rw [(by omega : (16 + i) / 8 = 2), (by omega : (16 + i) % 8 = i)]
              simp_scalar
              congr 1
              revert i
              decide
            . scalar_tac
          . intro i hi
            simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [(by omega : (1 + (16 + i)) / 8 = 2), (by omega : (1 + (16 + i)) % 8 = 1 + i),
              List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . congr 1
              revert i
              decide
            . scalar_tac
        . have : BitVec.toNat s_B_byte &&& 5 ≤ 5 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 1) &&& 5 ≤ 5 := Nat.and_le_right
          omega
      . have : (s_B_byte &&& 5#8) + (s_B_byte >>> 1 &&& 5#8) < 2^4 := by
          clear hs_B_byte hBytesToBits
          revert s_B_byte
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 16 = 2^4), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 16 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

/-- Each `Target2.samplePolyCBD.eta2_loop.spec.aux_` theorem is intended to prove the same basic result. The
    difference between them is `hj3` and the index of `(Target.bytesToBits BVector)` referenced in the goal.
    For `Target2.samplePolyCBD.eta2_loop.spec.aux_`, `hj3` states that `j = s.i + _` and the index of
    `(Target.bytesToBits BVector)` referenced in the goal is `2 * (s.i + _) * ↑s.η + ↑x`

    Because the indices change for each `Target2.samplePolyCBD.eta2_loop.spec.aux_`, the proofs themselves
    have minor differences (such as the values which `hBytesToBits` is instantiated with) but the overall
    structure of the proofs is shared. -/
theorem Target2.samplePolyCBD.eta2_loop.spec.aux5 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!) (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4) (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i) (hη : s.η.val = 2)
  (hs6 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS) (j : ℕ) (hj1 : j < s.i + 8) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 5) :
  (↑↑(inner_loop.next_coefficient s.i 5
      (inner_loop.next_coefficient s.i 4
      (inner_loop.next_coefficient s.i 3
      (inner_loop.next_coefficient s.i 2
      (inner_loop.next_coefficient s.i 1
      (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).1).1).1).2 : ZMod 3329) =
    ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 5) * ↑s.η + ↑x]!.toNat -
      ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 5) * ↑s.η + ↑s.η + ↑x]!.toNat := by
  simp only [hη, Nat.mul_assoc 2 (s.i + 5) 2, Nat.mul_comm (s.i + 5) 2, ← Nat.mul_assoc 2 2 (s.i + 5),
    Nat.reduceMul, Nat.mul_add 4, Nat.mul_comm 4 s.i, ← hs3, Fin.unfold2, Nat.mul_comm s.src_i 8]
  conv in 8 * s.src_i + 20 + 0 => rw [(by omega : 8 * s.src_i + 20 + 0 = 8 * (s.src_i + 2) + 4)]
  conv in 8 * s.src_i + 20 + 1 => rw [(by omega : 8 * s.src_i + 20 + 1 = 8 * (s.src_i + 2) + 5)]
  conv in 8 * s.src_i + 20 + 2 + 0 => rw [(by omega : 8 * s.src_i + 20 + 2 + 0 = 8 * (s.src_i + 2) + 6)]
  conv in 8 * s.src_i + 20 + 2 + 1 => rw [(by omega : 8 * s.src_i + 20 + 2 + 1 = 8 * (s.src_i + 2) + 7)]
  rw [hBytesToBits (s.src_i + 2) (by scalar_tac) 4 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 5 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 6 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 7 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat, Nat.reduceAdd,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_add_mod, ← Nat.shiftRight_add]
  olet hsample_bits_slice : sample_bits_slice := (sample_bits.toNat % 4294967296) >>> 20 &&& 15
  olet hs_B_byte : s_B_byte := s.B[s.src_i + 2]!
  replace hs_B_byte : sample_bits_slice = ((s_B_byte >>> 4) &&& 5) + ((s_B_byte >>> 5) &&& 5) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' <;> (try rw [hmin]; decide +native)
    have hy'' : y' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 15#8 = 2#8^4 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 4
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 ((x' + y') >>> 20) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hy, shiftDistribMask1431655765 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hy, ← hy', ← hx']
          apply testBitOfAdd 4 _ _ k hk2
          . intro i hi
            simp only [hx', hx, Nat.testBit_shiftRight, Nat.testBit_and,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . rw [(by omega : (20 + i) / 8 = 2), (by omega : (20 + i) % 8 = 4 + i)]
              simp_scalar
              congr 1
              revert i
              decide
            . scalar_tac
          . intro i hi
            simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            by_cases hi2 : i < 3
            . rw [(by omega : (1 + (20 + i)) / 8 = 2), (by omega : (1 + (20 + i)) % 8 = 5 + i),
                List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
              . congr 1
                revert i
                decide
              . scalar_tac
            . have h1 : Nat.testBit 1431655765 (20 + i) = false := by revert i; decide
              have h2 : Nat.testBit 5 i = false := by revert i; decide
              simp only [h1, Bool.and_false, h2]
        . have : (BitVec.toNat s_B_byte >>> 4) &&& 5 ≤ 5 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 5) &&& 5 ≤ 5 := Nat.and_le_right
          omega
      . have : (s_B_byte >>> 4 &&& 5#8) + (s_B_byte >>> 5 &&& 5#8) < 2^4 := by
          clear hs_B_byte hBytesToBits
          revert s_B_byte
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 16 = 2^4), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 16 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

/-- Each `Target2.samplePolyCBD.eta2_loop.spec.aux_` theorem is intended to prove the same basic result. The
    difference between them is `hj3` and the index of `(Target.bytesToBits BVector)` referenced in the goal.
    For `Target2.samplePolyCBD.eta2_loop.spec.aux_`, `hj3` states that `j = s.i + _` and the index of
    `(Target.bytesToBits BVector)` referenced in the goal is `2 * (s.i + _) * ↑s.η + ↑x`

    Because the indices change for each `Target2.samplePolyCBD.eta2_loop.spec.aux_`, the proofs themselves
    have minor differences (such as the values which `hBytesToBits` is instantiated with) but the overall
    structure of the proofs is shared. -/
theorem Target2.samplePolyCBD.eta2_loop.spec.aux6 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!) (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4) (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i) (hη : s.η.val = 2)
  (hs6 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS) (j : ℕ) (hj1 : j < s.i + 8) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 6) :
  (↑↑(inner_loop.next_coefficient s.i 6
      (inner_loop.next_coefficient s.i 5
      (inner_loop.next_coefficient s.i 4
      (inner_loop.next_coefficient s.i 3
      (inner_loop.next_coefficient s.i 2
      (inner_loop.next_coefficient s.i 1
      (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).1).1).1).1).2 : ZMod 3329) =
    ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 6) * ↑s.η + ↑x]!.toNat -
      ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 6) * ↑s.η + ↑s.η + ↑x]!.toNat := by
  simp only [hη, Nat.mul_assoc 2 (s.i + 6) 2, Nat.mul_comm (s.i + 6) 2, ← Nat.mul_assoc 2 2 (s.i + 6),
    Nat.reduceMul, Nat.mul_add 4, Nat.mul_comm 4 s.i, ← hs3, Fin.unfold2, Nat.mul_comm s.src_i 8]
  conv in 8 * s.src_i + 24 + 0 => rw [(by omega : 8 * s.src_i + 24 + 0 = 8 * (s.src_i + 3) + 0)]
  conv in 8 * s.src_i + 24 + 1 => rw [(by omega : 8 * s.src_i + 24 + 1 = 8 * (s.src_i + 3) + 1)]
  conv in 8 * s.src_i + 24 + 2 + 0 => rw [(by omega : 8 * s.src_i + 24 + 2 + 0 = 8 * (s.src_i + 3) + 2)]
  conv in 8 * s.src_i + 24 + 2 + 1 => rw [(by omega : 8 * s.src_i + 24 + 2 + 1 = 8 * (s.src_i + 3) + 3)]
  rw [hBytesToBits (s.src_i + 3) (by scalar_tac) 0 (by omega),
      hBytesToBits (s.src_i + 3) (by scalar_tac) 1 (by omega),
      hBytesToBits (s.src_i + 3) (by scalar_tac) 2 (by omega),
      hBytesToBits (s.src_i + 3) (by scalar_tac) 3 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat, Nat.reduceAdd,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_add_mod, ← Nat.shiftRight_add]
  olet hsample_bits_slice : sample_bits_slice := (sample_bits.toNat % 4294967296) >>> 24 &&& 15
  olet hs_B_byte : s_B_byte := s.B[s.src_i + 3]!
  replace hs_B_byte : sample_bits_slice = (s_B_byte &&& 5) + ((s_B_byte >>> 1) &&& 5) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' <;> (try rw [hmin]; decide +native)
    have hy'' : y' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 15#8 = 2#8^4 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 4
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 ((x' + y') >>> 24) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hy, shiftDistribMask1431655765 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hy, ← hy', ← hx']
          apply testBitOfAdd 4 _ _ k hk2
          . intro i hi
            simp only [hx', hx, Nat.testBit_shiftRight, Nat.testBit_and, ←
              BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!, Nat.ofNat_pos,
              Nat.add_div_left, Nat.add_mod_left]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . rw [(by omega : (24 + i) / 8 = 3), (by omega : (24 + i) % 8 = i)]
              simp_scalar
              congr 1
              revert i
              decide
            . scalar_tac
          . intro i hi
            simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [(by omega : (1 + (24 + i)) / 8 = 3), (by omega : (1 + (24 + i)) % 8 = 1 + i),
              List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . congr 1
              revert i
              decide
            . scalar_tac
        . have : BitVec.toNat s_B_byte &&& 5 ≤ 5 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 1) &&& 5 ≤ 5 := Nat.and_le_right
          omega
      . have : (s_B_byte &&& 5#8) + (s_B_byte >>> 1 &&& 5#8) < 2^4 := by
          clear hs_B_byte hBytesToBits
          revert s_B_byte
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 16 = 2^4), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 16 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

/-- Each `Target2.samplePolyCBD.eta2_loop.spec.aux_` theorem is intended to prove the same basic result. The
    difference between them is `hj3` and the index of `(Target.bytesToBits BVector)` referenced in the goal.
    For `Target2.samplePolyCBD.eta2_loop.spec.aux_`, `hj3` states that `j = s.i + _` and the index of
    `(Target.bytesToBits BVector)` referenced in the goal is `2 * (s.i + _) * ↑s.η + ↑x`

    Because the indices change for each `Target2.samplePolyCBD.eta2_loop.spec.aux_`, the proofs themselves
    have minor differences (such as the values which `hBytesToBits` is instantiated with) but the overall
    structure of the proofs is shared. -/
theorem Target2.samplePolyCBD.eta2_loop.spec.aux7 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!) (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4) (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i) (hη : s.η.val = 2)
  (hs6 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS) (j : ℕ) (hj1 : j < s.i + 8) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
          1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 7) :
  (↑↑(inner_loop.next_coefficient s.i 7
      (inner_loop.next_coefficient s.i 6
      (inner_loop.next_coefficient s.i 5
      (inner_loop.next_coefficient s.i 4
      (inner_loop.next_coefficient s.i 3
      (inner_loop.next_coefficient s.i 2
      (inner_loop.next_coefficient s.i 1
      (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).1).1).1).1).1).2 : ZMod 3329) =
    ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 7) * ↑s.η + ↑x]!.toNat -
      ∑ x : Fin s.η.val, ↑(Target.bytesToBits BVector)[2 * (s.i + 7) * ↑s.η + ↑s.η + ↑x]!.toNat := by
  simp only [hη, Nat.mul_assoc 2 (s.i + 7) 2, Nat.mul_comm (s.i + 7) 2, ← Nat.mul_assoc 2 2 (s.i + 7),
    Nat.reduceMul, Nat.mul_add 4, Nat.mul_comm 4 s.i, ← hs3, Fin.unfold2, Nat.mul_comm s.src_i 8]
  conv in 8 * s.src_i + 28 + 0 => rw [(by omega : 8 * s.src_i + 28 + 0 = 8 * (s.src_i + 3) + 4)]
  conv in 8 * s.src_i + 28 + 1 => rw [(by omega : 8 * s.src_i + 28 + 1 = 8 * (s.src_i + 3) + 5)]
  conv in 8 * s.src_i + 28 + 2 + 0 => rw [(by omega : 8 * s.src_i + 28 + 2 + 0 = 8 * (s.src_i + 3) + 6)]
  conv in 8 * s.src_i + 28 + 2 + 1 => rw [(by omega : 8 * s.src_i + 28 + 2 + 1 = 8 * (s.src_i + 3) + 7)]
  rw [hBytesToBits (s.src_i + 3) (by scalar_tac) 4 (by omega),
      hBytesToBits (s.src_i + 3) (by scalar_tac) 5 (by omega),
      hBytesToBits (s.src_i + 3) (by scalar_tac) 6 (by omega),
      hBytesToBits (s.src_i + 3) (by scalar_tac) 7 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat, Nat.reduceAdd,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_add_mod, ← Nat.shiftRight_add]
  olet hsample_bits_slice : sample_bits_slice := (sample_bits.toNat % 4294967296) >>> 28 &&& 15
  olet hs_B_byte : s_B_byte := s.B[s.src_i + 3]!
  replace hs_B_byte : sample_bits_slice = ((s_B_byte >>> 4) &&& 5) + ((s_B_byte >>> 5) &&& 5) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 1431655765 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' <;> (try rw [hmin]; decide +native)
    have hy'' : y' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 1431655765 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 15#8 = 2#8^4 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 4
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 ((x' + y') >>> 28) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hy, shiftDistribMask1431655765 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hy, ← hy', ← hx']
          apply testBitOfAdd 4 _ _ k hk2
          . intro i hi
            simp only [hx', hx, Nat.testBit_shiftRight, Nat.testBit_and,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . rw [(by omega : (28 + i) / 8 = 3), (by omega : (28 + i) % 8 = 4 + i)]
              simp_scalar
              congr 1
              revert i
              decide
            . scalar_tac
          . intro i hi
            simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            by_cases hi2 : i < 3
            . rw [(by omega : (1 + (28 + i)) / 8 = 3), (by omega : (1 + (28 + i)) % 8 = 5 + i),
                List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
              . congr 1
                revert i
                decide
              . scalar_tac
            . have h1 : Nat.testBit 1431655765 (28 + i) = false := by revert i; decide
              have h2 : Nat.testBit 5 i = false := by revert i; decide
              simp only [h1, Bool.and_false, h2]
        . have : (BitVec.toNat s_B_byte >>> 4) &&& 5 ≤ 5 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 5) &&& 5 ≤ 5 := Nat.and_le_right
          omega
      . have : (s_B_byte >>> 4 &&& 5#8) + (s_B_byte >>> 5 &&& 5#8) < 2^4 := by
          clear hs_B_byte hBytesToBits
          revert s_B_byte
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 16 = 2^4), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 16 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

def Target2.samplePolyCBD.eta2_loop.spec {s : Target2.samplePolyCBDState}
  (BVector : Vector Byte (64 * s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!)
  (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 8 = s.i * 4)
  (hs4 : 8 ∣ s.i) (hs5 : 4 ∣ s.src_i)
  (i : ℕ) (hi : i < 256) (hη : s.η.1 = 2) : (eta2_loop s)[i]! = (Target.samplePolyCBD BVector)[i]! := by
  unfold eta2_loop
  split
  . simp only [UScalar.ofNat_val_eq, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth'_eq]
    apply eta2_loop.spec
    . simp only [Vector.eq_mk, hBVector]
    . intro j hj1
      simp only at hj1
      simp only
      by_cases hj2 : j < s.i
      . rw [eta2_loop.inner_loop.equals_unrolled, eta2_loop.inner_loop_unrolled.preserves_below]
        . exact hs1 j hj2
        . exact hj2
      . next hs6 =>
        olet hsample_bits : sample_bits :=
          ((BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
              1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
            (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
              1431655765#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
        rw [Target.samplePolyCBD.spec BVector j (by scalar_tac),
          ← Symcrust.SpecAux.Target.bytesToBits.eq_spec]
        have hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8,
          (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j := by
          intro i hi j hj
          rw [Target.bytesToBits.spec BVector i hi j hj, hBVector, Vector.getElem!_eq_toArray_getElem!,
            ← Array.Inhabited_getElem_eq_getElem!, Array.getElem_extract]
          . simp
          . simp only [Array.size_extract, tsub_zero, lt_inf_iff]
            have := s.hB
            omega
        rw [inner_loop.equals_unrolled]
        unfold inner_loop_unrolled
        simp only [Q, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum]
        have hj3 : j = s.i ∨ j = s.i + 1 ∨ j = s.i + 2 ∨ j = s.i + 3 ∨
                   j = s.i + 4 ∨ j = s.i + 5 ∨ j = s.i + 6 ∨ j = s.i + 7 := by omega
        rcases hj3 with hj3 | hj3 | hj3 | hj3 | hj3 | hj3 | hj3 | hj3
        . simp_lists [hj3]
          apply eta2_loop.spec.aux0 <;> assumption
        . simp_lists [hj3]
          apply eta2_loop.spec.aux1 <;> assumption
        . simp_lists [hj3]
          apply eta2_loop.spec.aux2 <;> assumption
        . simp_lists [hj3]
          apply eta2_loop.spec.aux3 <;> assumption
        . simp_lists [hj3]
          apply eta2_loop.spec.aux4 <;> assumption
        . simp_lists [hj3]
          apply eta2_loop.spec.aux5 <;> assumption
        . simp_lists [hj3]
          apply eta2_loop.spec.aux6 <;> assumption
        . simp_lists [hj3]
          apply eta2_loop.spec.aux7 <;> assumption
    . intro j hj1 hj2
      simp only at hj2
      simp only [ReduceZMod.reduceZMod]
      rw [inner_loop.equals_unrolled, inner_loop_unrolled.preserves_above]
      . exact hs2 j hj1 (by omega)
      . omega
    . simp only
      omega
    . simp [hs4]
    . simp [hs5]
    . exact hi
    . simp [hη]
  . next hi2 =>
    simp only [key.MLWE_POLYNOMIAL_COEFFICIENTS, eval_global, key.MLWE_POLYNOMIAL_COEFFICIENTS_body,
      UScalar.ofNat_val_eq, not_lt] at hi2
    exact hs1 i (by omega)
termination_by ↑key.MLWE_POLYNOMIAL_COEFFICIENTS - s.i
decreasing_by scalar_tac

end Symcrust.SpecAux
