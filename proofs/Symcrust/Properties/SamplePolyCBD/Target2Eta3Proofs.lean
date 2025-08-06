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

  `Target2.samplePolyCBD.eta3_loop.spec` (which is the critical theorem in this file) proves `⟷₃` when `η = 3`.

  **Note** although the various `Target2.samplePolyCBD.eta3_loop.spec.aux` lemmas appear to be extremely similar,
  there are enough minor changes to the indices that appear in the arguments that there is not a convenient way
  to combine all of these lemmas into one parameterized theorem.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.Std Aeneas.SRRange

set_option maxHeartbeats 1000000

def Target2.samplePolyCBD.eta3_loop.inner_loop.preserves_below (pe_dst : Polynomial) (i : ℕ)
  (sample_bits : BitVec 32) (k : ℕ) (hk : k < i) :
  (eta3_loop.inner_loop pe_dst i sample_bits).1[k]! = pe_dst[k]! := by
  unfold inner_loop
  simp only [Q]
  rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne] <;> omega

def Target2.samplePolyCBD.eta3_loop.inner_loop.preserves_above (pe_dst : Polynomial) (i : ℕ)
  (sample_bits : BitVec 32) (k : ℕ) (hk : i + 3 < k) :
  (eta3_loop.inner_loop pe_dst i sample_bits).1[k]! = pe_dst[k]! := by
  unfold inner_loop
  simp only [Q]
  rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne] <;> omega

lemma Fin.unfold3 {α} [AddCommMonoid α] {n : Nat} (hn : n = 3) (f : Fin n → α) :
  ∑ x : Fin n, f x = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ := by
  rw [Finset.sum, Multiset.map, Multiset.sum, Finset.univ, Fintype.elems, Fin.fintype]
  simp only [List.finRange, List.ofFn, Fin.foldr, hn, Fin.foldr.loop, Multiset.lift_coe, List.map_cons,
    List.map_nil, Multiset.coe_foldr, List.foldr_cons, List.foldr_nil, add_zero, add_assoc]

lemma shiftDistribMask2396745Core {x y z : BitVec 64} (shift : Nat) (hs : shift ∈ [6,12,18]) (k : Nat) :
  (((x &&& 2396745#64) + (y &&& 2396745#64) + (z &&& 2396745#64)) >>> shift) &&& BitVec.ofNat 64 (2^k : Nat) =
  ((x &&& 2396745#64) >>> shift + (y &&& 2396745#64) >>> shift + (z &&& 2396745#64) >>> shift)
    &&& BitVec.ofNat 64 (2^k : Nat) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with hs | hs | hs <;> simp only [hs] <;> bv_decide

/-- Distributing `>>>` over `+` is not valid in general, but this lemma is true because
    of the masks applied to `x`, `y`, and `z`. -/
lemma shiftDistribMask2396745 {x y z shift k : ℕ} (hx : x < 2^64) (hy : y < 2^64) (hz : z < 2^64)
  (hShift : shift = 6 ∨ shift = 12 ∨ shift = 18) (hk : k < 6) :
  (((x &&& 2396745) + (y &&& 2396745) + (z &&& 2396745)) >>> shift).testBit k =
  ((x &&& 2396745) >>> shift + (y &&& 2396745) >>> shift + (z &&& 2396745) >>> shift).testBit k := by
  have hs : shift ∈ [6,12,18] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have h1 : (x &&& 2396745) = BitVec.toNat ((BitVec.ofNat 64 x &&& 2396745#64)) := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt]
    omega
  have h2 : (y &&& 2396745) = BitVec.toNat ((BitVec.ofNat 64 y &&& 2396745#64)) := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt]
    omega
  have h3 : (z &&& 2396745) = BitVec.toNat ((BitVec.ofNat 64 z &&& 2396745#64)) := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt]
    omega
  have h4 :
    ((BitVec.ofNat 64 x &&& 2396745#64).toNat + (BitVec.ofNat 64 y &&& 2396745#64).toNat +
     (BitVec.ofNat 64 z &&& 2396745#64).toNat) =
    ((BitVec.ofNat 64 x &&& 2396745#64) + (BitVec.ofNat 64 y &&& 2396745#64) +
     (BitVec.ofNat 64 z &&& 2396745#64)).toNat := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, BitVec.toNat_add]
    have : x &&& 2396745 ≤ 2396745 := Nat.and_le_right
    have : y &&& 2396745 ≤ 2396745 := Nat.and_le_right
    have : z &&& 2396745 ≤ 2396745 := Nat.and_le_right
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> omega
  have h5 :
    (((BitVec.ofNat 64 x &&& 2396745#64) >>> shift).toNat + ((BitVec.ofNat 64 y &&& 2396745#64) >>> shift).toNat +
     ((BitVec.ofNat 64 z &&& 2396745#64) >>> shift).toNat) =
    (((BitVec.ofNat 64 x &&& 2396745#64) >>> shift) + ((BitVec.ofNat 64 y &&& 2396745#64) >>> shift) +
     ((BitVec.ofNat 64 z &&& 2396745#64) >>> shift)).toNat := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, BitVec.toNat_add]
    have : x &&& 2396745 ≤ 2396745 := Nat.and_le_right
    have : y &&& 2396745 ≤ 2396745 := Nat.and_le_right
    have : z &&& 2396745 ≤ 2396745 := Nat.and_le_right
    have : (x &&& 2396745) >>> shift ≤ (x &&& 2396745) := Nat.shiftRight_le _ _
    have : (y &&& 2396745) >>> shift ≤ (y &&& 2396745) := Nat.shiftRight_le _ _
    have : (z &&& 2396745) >>> shift ≤ (z &&& 2396745) := Nat.shiftRight_le _ _
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> try omega
    rw [Nat.mod_eq_of_lt] <;> omega
  rw [h1, h2, h3, h4, ← BitVec.toNat_ushiftRight, ← BitVec.toNat_ushiftRight, ← BitVec.toNat_ushiftRight,
    ← BitVec.toNat_ushiftRight, h5, ← BitVec.getElem!_eq_testBit_toNat, ← BitVec.getElem!_eq_testBit_toNat,
    BitVec.getElem!_eq_mask_ne_zero, BitVec.getElem!_eq_mask_ne_zero, shiftDistribMask2396745Core] <;> omega

theorem Target2.samplePolyCBD.eta3_loop.spec.aux0 (s : samplePolyCBDState)
  (BVector : Vector Byte (64 * s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!)
  (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 4 = s.i * 3) (hη : s.η.val = 3)
  (hs4 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS)
  (j : ℕ) (hj1 : j < s.i + 4) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
          (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 2 &&&
          2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i) :
  ((((Vector.set! s.pe_dst s.i ↑↑(inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).2).set! (s.i + 1)
                ↑↑(inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).2).set!
            (s.i + 2)
            ↑↑(inner_loop.next_coefficient s.i 2
                    (inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).2).set!
        (s.i + 3)
        ↑↑(inner_loop.next_coefficient s.i 3
                (inner_loop.next_coefficient s.i 2
                    (inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).1).2)[j]! =
    ∑ (x : Fin s.η.val), ↑(Target.bytesToBits BVector)[2 * j * ↑s.η + ↑x]!.toNat -
      ∑ (x : Fin s.η.val), ↑(Target.bytesToBits BVector)[2 * j * ↑s.η + ↑s.η + ↑x]!.toNat := by
  rw [Vector.getElem!_set!_ne (by omega), Vector.getElem!_set!_ne (by omega),
    Vector.getElem!_set!_ne (by omega), Vector.getElem!_set! (by scalar_tac)]
  simp only [hj3, hη, Nat.mul_assoc 2 s.i 3, ← hs3, Nat.mul_comm s.src_i 4,
    ← Nat.mul_assoc 2 4 s.src_i, Nat.reduceMul, Fin.unfold3 hη]
  specialize hBytesToBits s.src_i (by scalar_tac)
  rw [hBytesToBits 0 (by omega), hBytesToBits 1 (by omega), hBytesToBits 2 (by omega),
    hBytesToBits 3 (by omega), hBytesToBits 4 (by omega), Nat.add_assoc,
    hBytesToBits 5 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight,
    BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod,
    Nat.mod_add_mod]
  olet hsample_bits_slice : sample_bits_slice := sample_bits.toNat % 4294967296 &&& 63
  olet hs_B_byte : s_B_byte := s.B[s.src_i]!
  replace hs_B_byte : sample_bits_slice = (s_B_byte &&& 9) +
    ((s_B_byte >>> 1) &&& 9) + ((s_B_byte >>> 2) &&& 9) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hz : z := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 2
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hz' : z' := (z &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' hz' <;> (try rw [hmin]; decide +native)
    have hx'' : z' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hz']
      exact Nat.and_le_right
    have hy'' : y' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hz'' : x' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 63#8 = 2#8^6 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 6
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 (x' + y' + z') k (by omega), Nat.mod_eq_of_lt]
        . apply testBitOfAdd 6 _ _ k hk2
          . intro i hi
            apply testBitOfAdd 6 _ _ i hi
            . intro j hj
              simp only [hx', hx, Nat.testBit_and, Nat.testBit_shiftRight,
                ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
              rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
              . simp_scalar
                congr 1
                revert j
                brute
              . scalar_tac
            . intro j hj
              simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
                ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
              rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
              . simp_scalar
                congr 1
                revert j
                brute
              . scalar_tac
          . intro i hi
            simp only [hz', hz, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte, Array.getElem!_toList]
            . simp_scalar
              congr 1
              revert i
              brute
            . scalar_tac
        . have : BitVec.toNat s_B_byte &&& 9 ≤ 9 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 1) &&& 9 ≤ 9 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte >>> 2) &&& 9 ≤ 9 := Nat.and_le_right
          omega
      . have : (s_B_byte &&& 9#8) + (s_B_byte >>> 1 &&& 9#8) + (s_B_byte >>> 2 &&& 9#8) < 2^6 := by
          clear hs_B_byte hBytesToBits
          revert s_B_byte
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 64 = 2^6), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 64 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

theorem Target2.samplePolyCBD.eta3_loop.spec.aux1 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!)
  (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 4 = s.i * 3) (hη : s.η.val = 3)
  (hs4 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS)
  (j : ℕ) (hj1 : j < s.i + 4) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
          (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 2 &&&
          2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 1) :
  ((((Vector.set! s.pe_dst s.i ↑↑(inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).2).set! (s.i + 1)
                ↑↑(inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).2).set!
            (s.i + 2)
            ↑↑(inner_loop.next_coefficient s.i 2
                    (inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).2).set!
        (s.i + 3)
        ↑↑(inner_loop.next_coefficient s.i 3
                (inner_loop.next_coefficient s.i 2
                    (inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).1).2)[j]! =
    ∑ (x : Fin s.η.val), ↑(Target.bytesToBits BVector)[2 * j * ↑s.η + ↑x]!.toNat -
      ∑ (x : Fin s.η.val), ↑(Target.bytesToBits BVector)[2 * j * ↑s.η + ↑s.η + ↑x]!.toNat := by
  rw [Vector.getElem!_set!_ne (by omega), Vector.getElem!_set!_ne (by omega),
    Vector.getElem!_set! (by scalar_tac)]
  simp only [hj3, hη, Nat.mul_assoc 2 (s.i + 1) 3, Nat.mul_comm (s.i + 1) 3,
    Nat.mul_add 3 s.i 1, Nat.mul_comm 3 s.i, ← hs3, Nat.mul_comm s.src_i 4, mul_one,
    Nat.mul_add 2 (4 * s.src_i) 3, ← Nat.mul_assoc 2 4 s.src_i, Nat.reduceMul,
    Nat.add_assoc, Fin.unfold3 hη, add_zero, Nat.reduceAdd]
  conv in 8 * s.src_i + 8 => rw [(by omega : 8 * s.src_i + 8 = 8 * (s.src_i + 1) + 0)]
  conv in 8 * s.src_i + 9 => rw [(by omega : 8 * s.src_i + 9 = 8 * (s.src_i + 1) + 1)]
  conv in 8 * s.src_i + 10 => rw [(by omega : 8 * s.src_i + 10 = 8 * (s.src_i + 1) + 2)]
  conv in 8 * s.src_i + 11 => rw [(by omega : 8 * s.src_i + 11 = 8 * (s.src_i + 1) + 3)]
  rw [hBytesToBits s.src_i (by scalar_tac) 6 (by omega),
      hBytesToBits s.src_i (by scalar_tac) 7 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 0 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 1 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 2 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 3 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight,
    BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod,
    Nat.mod_add_mod]
  olet hsample_bits_slice : sample_bits_slice := (sample_bits.toNat % 4294967296) >>> 6 &&& 63
  olet hs_B_byte0 : s_B_byte0 := s.B[s.src_i]!
  olet hs_B_byte1 : s_B_byte1 := s.B[s.src_i + 1]!
  have hs_B_byte : sample_bits_slice =
    (((s_B_byte0 >>> 6) ||| (s_B_byte1 <<< 2)) &&& 9) +
    (((s_B_byte0 >>> 7) ||| (s_B_byte1 <<< 1)) &&& 9) +
    (s_B_byte1 &&& 9) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hz : z := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 2
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hz' : z' := (z &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' hz' <;> (try rw [hmin]; decide +native)
    have hz'' : z' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hz']
      exact Nat.and_le_right
    have hy'' : y' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 63#8 = 2#8^6 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 6
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
        rw [testBitMod256 ((x' + y' + z') >>> 6) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hz', hy, hz, shiftDistribMask2396745 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hz, ← hy, ← hz', ← hy', ← hx']
          apply testBitOfAdd 6 _ _ k hk2
          . intro i hi
            apply testBitOfAdd 6 _ _ i hi
            . intro j hj
              simp only [hx', hx, Nat.testBit_and, Nat.testBit_shiftRight,
                ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
              rw [List.getElem!_slice, hs_B_byte0, hs_B_byte1, Array.getElem!_toList]
              . simp only [BitVec.getElem!_or, BitVec.getElem!_shiftRight]
                by_cases hj2 : j < 2
                . simp_scalar
                  congr 1
                  . simp only [Bool.eq_self_or]
                    rw [BitVec.getElem!_shiftLeft_false]
                    . simp
                    . omega
                  . revert j; brute
                . rw [(by omega : (6 + j) / 8 = 1), BitVec.getElem!_shiftLeft_eq _ _ _ (by omega),
                    BitVec.getElem!_eq_false _ (6 + j) (by omega)]
                  simp_scalar
                  congr 1
                  . congr; omega
                  . revert j; brute
              . scalar_tac
            . intro j hj
              simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
                ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
              rw [List.getElem!_slice, hs_B_byte0, hs_B_byte1, Array.getElem!_toList]
              . simp only [BitVec.getElem!_or, BitVec.getElem!_shiftRight]
                by_cases hj2 : j < 1
                . simp_scalar
                  simp only [← add_assoc, Nat.reduceAdd]
                  congr 1
                  . simp only [Bool.eq_self_or]
                    rw [BitVec.getElem!_shiftLeft_false]
                    . simp
                    . omega
                  . revert j; brute
                . rw [(by omega : (1 + (6 + j)) / 8 = 1), BitVec.getElem!_shiftLeft_eq _ _ _ (by omega),
                    BitVec.getElem!_eq_false _ (7 + j) (by omega)]
                  simp_scalar
                  congr 1
                  . congr; omega
                  . revert j; brute
              . scalar_tac
          . intro i hi
            simp only [hz', hz, hx, Nat.testBit_and, Nat.testBit_shiftRight,
              ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte1, Array.getElem!_toList]
            . rw [(by omega : (2 + (6 + i)) / 8 = 1), (by omega : (2 + (6 + i)) % 8 = i)]
              congr 1
              revert i
              brute
            . scalar_tac
        . have : ((s_B_byte0 >>> 6 ||| s_B_byte1 <<< 2).toNat &&& 9) ≤ 9 := Nat.and_le_right
          have : ((s_B_byte0 >>> 7 ||| s_B_byte1 <<< 1).toNat &&& 9) ≤ 9 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte1 &&& 9) ≤ 9 := Nat.and_le_right
          omega
      . have : (((s_B_byte0 >>> 6 ||| s_B_byte1 <<< 2) &&& 9#8) +
          ((s_B_byte0 >>> 7 ||| s_B_byte1 <<< 1) &&& 9#8) + (s_B_byte1 &&& 9#8)) < 2^6 := by
          clear hs_B_byte0 hs_B_byte1 hBytesToBits
          revert s_B_byte0 s_B_byte1
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 64 = 2^6), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 64 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hs_B_byte0 hs_B_byte1 hBytesToBits
  revert hs_B_byte
  revert s_B_byte0 s_B_byte1
  revert sample_bits_slice
  brute

theorem Target2.samplePolyCBD.eta3_loop.spec.aux2 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!)
  (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 4 = s.i * 3) (hη : s.η.val = 3)
  (hs4 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS)
  (j : ℕ) (hj1 : j < s.i + 4) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
          (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 2 &&&
          2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 2) :
  ((((Vector.set! s.pe_dst s.i ↑↑(inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).2).set! (s.i + 1)
                ↑↑(inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).2).set!
            (s.i + 2)
            ↑↑(inner_loop.next_coefficient s.i 2
                    (inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).2).set!
        (s.i + 3)
        ↑↑(inner_loop.next_coefficient s.i 3
                (inner_loop.next_coefficient s.i 2
                    (inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).1).2)[j]! =
    ∑ (x : Fin s.η.val), ↑(Target.bytesToBits BVector)[2 * j * ↑s.η + ↑x]!.toNat -
      ∑ (x : Fin s.η.val), ↑(Target.bytesToBits BVector)[2 * j * ↑s.η + ↑s.η + ↑x]!.toNat := by
  rw [Vector.getElem!_set!_ne (by omega), Vector.getElem!_set! (by scalar_tac)]
  simp only [hj3, hη, Nat.mul_assoc 2 (s.i + 2) 3, Nat.mul_comm (s.i + 2) 3,
    Nat.mul_add 3 s.i 2, Nat.mul_comm 3 s.i, ← hs3, Nat.mul_comm s.src_i 4, mul_one,
    Nat.mul_add 2 (4 * s.src_i) 6, ← Nat.mul_assoc 2 4 s.src_i, Nat.reduceMul,
    Nat.add_assoc, Fin.unfold3 hη, add_zero, Nat.reduceAdd]
  conv in 8 * s.src_i + 12 => rw [(by omega : 8 * s.src_i + 12 = 8 * (s.src_i + 1) + 4)]
  conv in 8 * s.src_i + 13 => rw [(by omega : 8 * s.src_i + 13 = 8 * (s.src_i + 1) + 5)]
  conv in 8 * s.src_i + 14 => rw [(by omega : 8 * s.src_i + 14 = 8 * (s.src_i + 1) + 6)]
  conv in 8 * s.src_i + 15 => rw [(by omega : 8 * s.src_i + 15 = 8 * (s.src_i + 1) + 7)]
  conv in 8 * s.src_i + 16 => rw [(by omega : 8 * s.src_i + 16 = 8 * (s.src_i + 2) + 0)]
  conv in 8 * s.src_i + 17 => rw [(by omega : 8 * s.src_i + 17 = 8 * (s.src_i + 2) + 1)]
  rw [hBytesToBits (s.src_i + 1) (by scalar_tac) 4 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 5 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 6 (by omega),
      hBytesToBits (s.src_i + 1) (by scalar_tac) 7 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 0 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 1 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight,
    BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod,
    Nat.mod_add_mod]
  olet hsample_bits_slice : sample_bits_slice :=
    (sample_bits.toNat % 4294967296) >>> 6 >>> 6 &&& 63
  olet hs_B_byte1 : s_B_byte1 := s.B[s.src_i + 1]!
  olet hs_B_byte2 : s_B_byte2 := s.B[s.src_i + 2]!
  have hs_B_byte : sample_bits_slice =
    ((s_B_byte1 >>> 4) &&& 9) +
    (((s_B_byte1 >>> 5) ||| (s_B_byte2 <<< 3)) &&& 9) +
    (((s_B_byte1 >>> 6) ||| (s_B_byte2 <<< 2)) &&& 9) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hz : z := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 2
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hz' : z' := (z &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' hz' <;> (try rw [hmin]; decide +native)
    have hz'' : z' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hz']
      exact Nat.and_le_right
    have hy'' : y' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 63#8 = 2#8^6 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 6
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, ← Nat.shiftRight_add,
          Nat.reduceAdd]
        rw [testBitMod256 ((x' + y' + z') >>> 12) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hz', hy, hz, shiftDistribMask2396745 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hz, ← hy, ← hz', ← hy', ← hx']
          apply testBitOfAdd 6 _ _ k hk2
          . intro i hi
            apply testBitOfAdd 6 _ _ i hi
            . intro j hj
              simp only [hx', hx, Nat.testBit_and, Nat.testBit_shiftRight,
                ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
              rw [List.getElem!_slice, hs_B_byte1, Array.getElem!_toList]
              . by_cases hj2 : j < 4
                . rw [(by omega : (12 + j) / 8 = 1)]
                  simp_scalar
                  congr 1
                  . congr 1; omega
                  . revert j; brute
                . have h1 : Nat.testBit 2396745 (12 + j) = false := by revert j; decide
                  have h2 : Nat.testBit 9 j = false := by revert j; decide
                  simp [h1, h2]
              . scalar_tac
            . intro j hj
              simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
                ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
              rw [List.getElem!_slice, hs_B_byte1, hs_B_byte2, Array.getElem!_toList]
              . simp only [BitVec.getElem!_or, BitVec.getElem!_shiftRight]
                by_cases hj2 : j < 3
                . rw [(by omega : (1 + (12 + j)) / 8 = 1), (by omega : (1 + (12 + j)) % 8 = 5 + j)]
                  congr 1
                  . simp only [Bool.eq_self_or]
                    rw [BitVec.getElem!_shiftLeft_false]
                    . simp
                    . omega
                  . revert j; decide
                . rw [(by omega : (1 + (12 + j)) / 8 = 2),
                    (by omega : (1 + (12 + j)) % 8 = j - 3),
                    BitVec.getElem!_shiftLeft_eq _ _ _ (by omega),
                    BitVec.getElem!_eq_false _ (5 + j) (by omega)]
                  simp_scalar
                  congr 1
                  revert j
                  decide
              . scalar_tac
          . intro i hi
            simp only [hz', hz, hx, Nat.testBit_and, Nat.testBit_shiftRight, BitVec.getElem!_or,
              BitVec.getElem!_shiftRight, ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte1, hs_B_byte2, Array.getElem!_toList]
            . by_cases hi2 : i < 2
              . rw [(by omega : (2 + (12 + i)) / 8 = 1), (by omega : (2 + (12 + i)) % 8 = 6 + i),
                  BitVec.getElem!_shiftLeft_false _ _ _ (by omega)]
                simp_scalar
                congr 1
                revert i
                decide
              . rw [(by omega : (2 + (12 + i)) / 8 = 2), (by omega : (2 + (12 + i)) % 8 = i - 2),
                  BitVec.getElem!_eq_false _ (6 + i) (by omega), BitVec.getElem!_shiftLeft_eq _ _ _ (by omega)]
                simp_scalar
                congr 1
                revert i
                decide
            . scalar_tac
        . have : ((s_B_byte1 >>> 5 ||| s_B_byte2 <<< 3).toNat &&& 9) ≤ 9 := Nat.and_le_right
          have : ((s_B_byte1 >>> 6 ||| s_B_byte2 <<< 2).toNat &&& 9) ≤ 9 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte1 >>> 4 &&& 9) ≤ 9 := Nat.and_le_right
          omega
      . have : (s_B_byte1 >>> 4 &&& 9#8) + ((s_B_byte1 >>> 5 ||| s_B_byte2 <<< 3) &&& 9#8) +
          ((s_B_byte1 >>> 6 ||| s_B_byte2 <<< 2) &&& 9#8) < 2^6 := by
          clear hs_B_byte1 hs_B_byte2 hBytesToBits
          revert s_B_byte1 s_B_byte2
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 64 = 2^6), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 64 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hs_B_byte1 hs_B_byte2 hBytesToBits
  revert hs_B_byte
  revert s_B_byte1 s_B_byte2
  revert sample_bits_slice
  brute

theorem Target2.samplePolyCBD.eta3_loop.spec.aux3 {s : samplePolyCBDState}
  (BVector : Vector Byte (64 * ↑s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!)
  (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 4 = s.i * 3) (hη : s.η.val = 3)
  (hs4 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS)
  (j : ℕ) (hj1 : j < s.i + 4) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
          (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 2 &&&
          2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j)
  (hj3 : j = s.i + 3) :
  ((((Vector.set! s.pe_dst s.i ↑↑(inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).2).set! (s.i + 1)
                ↑↑(inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).2).set!
            (s.i + 2)
            ↑↑(inner_loop.next_coefficient s.i 2
                    (inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).2).set!
        (s.i + 3)
        ↑↑(inner_loop.next_coefficient s.i 3
                (inner_loop.next_coefficient s.i 2
                    (inner_loop.next_coefficient s.i 1
                        (inner_loop.next_coefficient s.i 0 (BitVec.setWidth 32 sample_bits)).1).1).1).2)[j]! =
    ∑ (x : Fin s.η.val), ↑(Target.bytesToBits BVector)[2 * j * ↑s.η + ↑x]!.toNat -
      ∑ (x : Fin s.η.val), ↑(Target.bytesToBits BVector)[2 * j * ↑s.η + ↑s.η + ↑x]!.toNat := by
  rw [Vector.getElem!_set! (by scalar_tac)]
  simp only [hj3, hη, Nat.mul_assoc 2 (s.i + 3) 3, Nat.mul_comm (s.i + 3) 3,
    Nat.mul_add 3 s.i 3, Nat.mul_comm 3 s.i, ← hs3, Nat.mul_comm s.src_i 4, mul_one,
    Nat.mul_add 2 (4 * s.src_i) 9, ← Nat.mul_assoc 2 4 s.src_i, Nat.reduceMul,
    Nat.add_assoc, Fin.unfold3 hη, add_zero, Nat.reduceAdd]
  conv in 8 * s.src_i + 18 => rw [(by omega : 8 * s.src_i + 18 = 8 * (s.src_i + 2) + 2)]
  conv in 8 * s.src_i + 19 => rw [(by omega : 8 * s.src_i + 19 = 8 * (s.src_i + 2) + 3)]
  conv in 8 * s.src_i + 20 => rw [(by omega : 8 * s.src_i + 20 = 8 * (s.src_i + 2) + 4)]
  conv in 8 * s.src_i + 21 => rw [(by omega : 8 * s.src_i + 21 = 8 * (s.src_i + 2) + 5)]
  conv in 8 * s.src_i + 22 => rw [(by omega : 8 * s.src_i + 22 = 8 * (s.src_i + 2) + 6)]
  conv in 8 * s.src_i + 23 => rw [(by omega : 8 * s.src_i + 23 = 8 * (s.src_i + 2) + 7)]
  rw [hBytesToBits (s.src_i + 2) (by scalar_tac) 2 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 3 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 4 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 5 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 6 (by omega),
      hBytesToBits (s.src_i + 2) (by scalar_tac) 7 (by omega)]
  unfold inner_loop.next_coefficient
  simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
    BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight,
    BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod,
    Nat.mod_add_mod]
  olet hsample_bits_slice : sample_bits_slice :=
    (sample_bits.toNat % 4294967296) >>> 6 >>> 6 >>> 6 &&& 63
  olet hs_B_byte2 : s_B_byte2 := s.B[s.src_i + 2]!
  replace hs_B_byte2 : sample_bits_slice = ((s_B_byte2 >>> 2) &&& 9) +
    ((s_B_byte2 >>> 3) &&& 9) + ((s_B_byte2 >>> 4) &&& 9) := by
    rw [hsample_bits_slice, hsample_bits]
    simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.natCast_eq_ofNat, BitVec.ofNat_and,
      Nat.cast_ofNat, BitVec.ofNat_eq_ofNat]
    have sHB := s.hB
    have hmin : min (s.B.size - s.src_i) 4 = 4 := by scalar_tac
    simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
    olet hz : z := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 2
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList)).toNat
    olet hx' : x' := (x &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hy' : y' := (y &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    olet hz' : z' := (z &&& 2396745 % 2 ^ (8 * min (s.B.size - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' hz' <;> (try rw [hmin]; decide +native)
    have hz'' : z' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hz']
      exact Nat.and_le_right
    have hy'' : y' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hy']
      exact Nat.and_le_right
    have hx'' : x' < 2396745 + 1 := by
      apply Nat.lt_succ_of_le
      rw [hx']
      exact Nat.and_le_right
    have hx_bound : x < 2^64 := by
      rw [hx]
      apply BitVec.toNat_lt_twoPow_of_le
      simp only [List.slice_length, Array.length_toList, add_tsub_cancel_left]
      omega
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . rw [(by decide : 63#8 = 2#8^6 - 1#8), BitVec.and_two_pow_sub_one_eq_mod]
      ext k hk1
      by_cases hk2 : k < 6
      . simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_mod_pow2_eq _ _ _ hk2,
          BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add,
          BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, ← Nat.shiftRight_add,
          Nat.reduceAdd]
        rw [testBitMod256 ((x' + y' + z') >>> 18) k (by omega), Nat.mod_eq_of_lt]
        . rw [hx', hy', hz', hy, hz, shiftDistribMask2396745 hx_bound (by omega) (by omega) (by omega) hk2,
            ← hz, ← hy, ← hz', ← hy', ← hx']
          apply testBitOfAdd 6 _ _ k hk2
          . intro i hi
            apply testBitOfAdd 6 _ _ i hi
            . intro j hj
              simp only [hx', hx, Nat.testBit_and, Nat.testBit_shiftRight,
                ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
              rw [List.getElem!_slice, hs_B_byte2, Array.getElem!_toList]
              . rw [(by omega : (18 + j) / 8 = 2)]
                simp_scalar
                congr 1
                . congr 1; omega
                . revert j; brute
              . scalar_tac
            . intro j hj
              simp only [hy', hy, hx, Nat.testBit_and, Nat.testBit_shiftRight,
                ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
              rw [List.getElem!_slice, hs_B_byte2, Array.getElem!_toList]
              . by_cases hj2 : j < 5
                . rw [(by omega : (1 + (18 + j)) / 8 = 2), (by omega : (1 + (18 + j)) % 8 = 3 + j)]
                  congr 1
                  revert j
                  decide
                . have h1 : Nat.testBit 2396745 (18 + j) = false := by revert j; decide
                  have h2 : Nat.testBit 9 j = false := by revert j; decide
                  simp only [h1, Bool.and_false, h2]
              . scalar_tac
          . intro i hi
            simp only [hz', hz, hx, Nat.testBit_and, Nat.testBit_shiftRight, BitVec.getElem!_or,
              BitVec.getElem!_shiftRight, ← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
            rw [List.getElem!_slice, hs_B_byte2, Array.getElem!_toList]
            . by_cases hi2 : i < 4
              . rw [(by omega : (2 + (18 + i)) / 8 = 2), (by omega : (2 + (18 + i)) % 8 = 4 + i)]
                simp_scalar
                congr 1
                revert i
                decide
              . have h1 : Nat.testBit 2396745 (18 + i) = false := by revert i; decide
                have h2 : (s.B[s.src_i + 2]!)[4 + i]! = false := by rw [BitVec.getElem!_eq_false]; omega
                simp only [h1, Bool.and_false, h2, Bool.false_and]
            . scalar_tac
        . have : (BitVec.toNat s_B_byte2 >>> 2 &&& 9) ≤ 9 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte2 >>> 3 &&& 9) ≤ 9 := Nat.and_le_right
          have : (BitVec.toNat s_B_byte2 >>> 4 &&& 9) ≤ 9 := Nat.and_le_right
          omega
      . have : ((s_B_byte2 >>> 2 &&& 9#8) + (s_B_byte2 >>> 3 &&& 9#8) + (s_B_byte2 >>> 4 &&& 9#8)) < 2^6 := by
          clear hs_B_byte2 hBytesToBits
          revert s_B_byte2
          decide +native -- **TODO** Once `brute` supports unbounded UScalars, `brute` should be faster
        rw [← BitVec.getElem!_eq_getElem, ← BitVec.getElem!_eq_getElem,
          BitVec.getElem!_mod_pow2_false _ _ _ (by omega), BitVec.getElem!_eq_testBit_toNat,
          ← Nat.mod_eq_of_lt this]
        simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod, BitVec.ofNat_eq_ofNat,
          BitVec.toNat_pow, Nat.reduceDvd, Nat.mod_mod_of_dvd, Bool.false_eq]
        rw [(by decide : 64 = 2^6), Nat.testBit_mod_two_pow,
          Bool.and_eq_false_eq_eq_false_or_eq_false]
        left
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    . rw [hmin]; omega
    . rw [hmin, Nat.mod_eq_of_lt] <;> omega
  replace hsample_bits_slice : sample_bits_slice < 64 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte2
  revert sample_bits_slice
  brute

def Target2.samplePolyCBD.eta3_loop.spec {s : Target2.samplePolyCBDState}
  (BVector : Vector Byte (64 * s.η))
  (hBVector : BVector = ⟨s.B.take (64 * s.η), by have := s.hB; simp; omega⟩)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD BVector)[j]!)
  (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 4 = s.i * 3)
  (i : ℕ) (hi : i < 256) (hη : s.η.1 = 3) : (eta3_loop s)[i]! = (Target.samplePolyCBD BVector)[i]! := by
  unfold eta3_loop
  split
  . simp only [UScalar.ofNat_val_eq, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth'_eq]
    apply eta3_loop.spec
    . simp only [Vector.eq_mk, hBVector]
    . intro j hj1
      simp only at hj1
      simp only
      by_cases hj2 : j < s.i
      . rw [eta3_loop.inner_loop.preserves_below]
        . exact hs1 j hj2
        . exact hj2
      . next hs4 =>
        olet hsample_bits : sample_bits :=
          ((BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) &&&
                2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
              (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 1 &&&
                2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)) +
            (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toList) >>> 2 &&&
              2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toList).length)))
        rw [Target.samplePolyCBD.spec BVector j (by scalar_tac), ← Symcrust.SpecAux.Target.bytesToBits.eq_spec]
        have hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8,
          (Target.bytesToBits BVector)[8 * i + j]! = s.B[i]!.testBit j := by
          intro i hi j hj
          rw [Target.bytesToBits.spec BVector i hi j hj, hBVector, Vector.getElem!_eq_toArray_getElem!,
            ← Array.Inhabited_getElem_eq_getElem!, Array.getElem_extract]
          . simp
          . simp only [Array.size_extract, tsub_zero, lt_inf_iff]
            have := s.hB
            omega
        unfold inner_loop
        simp only [Q, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum]
        have hj3 : j = s.i ∨ j = s.i + 1 ∨ j = s.i + 2 ∨ j = s.i + 3 := by omega
        rcases hj3 with hj3 | hj3 | hj3 | hj3
        . apply eta3_loop.spec.aux0 <;> assumption
        . apply eta3_loop.spec.aux1 <;> assumption
        . apply eta3_loop.spec.aux2 <;> assumption
        . apply eta3_loop.spec.aux3 <;> assumption
    . intro j hj1 hj2
      simp only at hj2
      simp only [ReduceZMod.reduceZMod]
      rw [eta3_loop.inner_loop.preserves_above]
      . exact hs2 j hj1 (by omega)
      . omega
    . simp only
      omega
    . exact hi
    . simp [hη]
  . next hi2 =>
    simp only [key.MLWE_POLYNOMIAL_COEFFICIENTS, eval_global, key.MLWE_POLYNOMIAL_COEFFICIENTS_body,
      UScalar.ofNat_val_eq, not_lt] at hi2
    exact hs1 i (by omega)
termination_by ↑key.MLWE_POLYNOMIAL_COEFFICIENTS - s.i
decreasing_by scalar_tac

end Symcrust.SpecAux
