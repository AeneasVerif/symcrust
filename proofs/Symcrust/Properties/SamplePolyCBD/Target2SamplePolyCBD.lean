import Symcrust.Spec
import Symcrust.Code.Funs
import Symcrust.Brute
import Symcrust.Properties.SamplePolyCBD.TargetSamplePolyCBD

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
    - `⟷₃` is bundled with `⟷₂` in the form of `Target2.samplePolyCBD.spec`.
    - Analogues for later portions of the verification pipeline appear in other files.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.Std Aeneas.SRRange

set_option maxHeartbeats 1000000

structure Target2.samplePolyCBDState where
  η : Η
  pe_dst : Polynomial
  B : Vector Byte (64 * η) -- This relates to `pb_src` in the Aeneas translated code
  src_i : ℕ
  i : ℕ

theorem Target2.samplePolyCBD.eta2_loop.inner_loop.i7_proof (sample_bits : BitVec 32) :
  let coefficient := sample_bits &&& 15;
  let i1 := coefficient &&& 3;
  let i2 := coefficient >>> 2;
  let coefficient1 := i1 - i2;
  let i3 := coefficient1 >>> 16;
  let i4 := ↑↑ntt.Q &&& i3;
  let coefficient2 := coefficient1 + i4;
  coefficient2.toNat ≤ UScalar.cMax UScalarTy.U16 := by
  intro coefficient i1 i2 coefficient1 i3 i4 coefficient2
  unfold coefficient2 i4 i3 coefficient1 i1 i2 coefficient
  olet hsample_bits' : sample_bits' := sample_bits &&& 15
  replace hsample_bits' : sample_bits' < 16 := by
    rw [hsample_bits', LT.lt, instLTBitVec]
    simp only [BitVec.ofNat_eq_ofNat, gt_iff_lt, BitVec.toNat_and, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod]
    rw [Nat.lt_succ_iff]
    apply Nat.and_le_right
  revert sample_bits'
  brute

def Target2.samplePolyCBD.eta2_loop.inner_loop (pe_dst : Polynomial) (i j : ℕ) (sample_bits : BitVec 32) :
  Polynomial × BitVec 32 :=
  if j < 8#usize then
    let coefficient := sample_bits &&& 15
    let sample_bits1 := sample_bits >>> 4
    let i1 := coefficient &&& 3
    let i2 := coefficient >>> 2
    let coefficient1 := i1 - i2 -- `BitVec.sub_def` indicates that `BitVec`'s subtraction is wrapping
    let i3 := coefficient1 >>> 16
    let i4 := ntt.Q &&& i3
    let coefficient2 := coefficient1 + i4
    let i5 := i + j
    let i6 := U16.ofNat coefficient2.toNat $ by apply inner_loop.i7_proof
    let pe_dst1 := pe_dst.set! i5 i6
    let j1 := j + 1
    inner_loop pe_dst1 i j1 sample_bits1
  else
    (pe_dst, sample_bits)
termination_by 8 - j
decreasing_by scalar_tac

def Target2.samplePolyCBD.eta2_loop (s : Target2.samplePolyCBDState) : Polynomial :=
  if s.i < key.MLWE_POLYNOMIAL_COEFFICIENTS then
    let a := List.slice s.src_i (s.src_i + 4) s.B.1.toList
    let sample_bits := BitVec.fromLEBytes a
    let src_i1 := s.src_i + 4
    let i1 := (sample_bits &&& 1431655765#u32)
    let i2 := sample_bits >>> 1
    let i3 := i2 &&& 1431655765#u32
    let sample_bits1 := i1 + i3
    let sample_bits2 := sample_bits1.setWidth' (by scalar_tac)
    let (pe_dst1, _) := eta2_loop.inner_loop s.pe_dst s.i 0 sample_bits2
    let i4 := s.i + 8
    eta2_loop {η := s.η, pe_dst := pe_dst1, B := s.B, src_i := src_i1, i := i4}
  else
    s.pe_dst
termination_by key.MLWE_POLYNOMIAL_COEFFICIENTS - s.i
decreasing_by scalar_tac

theorem Target2.samplePolyCBD.eta3_loop.inner_loop.i6_proof (sample_bits : BitVec 32) :
  let coefficient := sample_bits &&& 63;
  let i1 := coefficient &&& 3;
  let i2 := coefficient >>> 3;
  let coefficient1 := i1 - i2;
  let i3 := coefficient1 >>> 16;
  let i4 := ↑↑ntt.Q &&& i3;
  let coefficient2 := coefficient1 + i4;
  coefficient2.toNat ≤ UScalar.cMax UScalarTy.U16 := by
  intro coefficient i1 i2 coefficient1 i3 i4 coefficient2
  unfold coefficient2 i4 i3 coefficient1 i1 i2 coefficient
  olet hsample_bits' : sample_bits' := sample_bits &&& 63
  replace hsample_bits' : sample_bits' < 64 := by
    rw [hsample_bits', LT.lt, instLTBitVec]
    simp only [BitVec.ofNat_eq_ofNat, gt_iff_lt, BitVec.toNat_and, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod]
    rw [Nat.lt_succ_iff]
    apply Nat.and_le_right
  revert sample_bits'
  brute

def Target2.samplePolyCBD.eta3_loop.inner_loop.next_coefficient (i j : ℕ) (sample_bits : BitVec 32) :
  BitVec 32 × UScalar UScalarTy.U16 :=
  let coefficient := sample_bits &&& 63
  let sample_bits1 := sample_bits >>> 6
  let i1 := coefficient &&& 3
  let i2 := coefficient >>> 3
  let coefficient1 := i1 - i2 -- `BitVec.sub_def` indicates that `BitVec`'s subtraction is wrapping
  let i3 := coefficient1 >>> 16
  let i4 := ntt.Q &&& i3
  let coefficient2 := coefficient1 + i4
  let i5 := i + j
  let i6 := U16.ofNat coefficient2.toNat $ by apply inner_loop.i6_proof
  (sample_bits1, i6)

/-- This is a simplified and unrolled version of the Aeneas translation, structured for ease verification -/
def Target2.samplePolyCBD.eta3_loop.inner_loop (pe_dst : Polynomial) (i : ℕ) (sample_bits : BitVec 32) :
  Polynomial × BitVec 32 :=
  let (sample_bits1, coefficient1) := inner_loop.next_coefficient i 0 sample_bits
  let (sample_bits2, coefficient2) := inner_loop.next_coefficient i 1 sample_bits1
  let (sample_bits3, coefficient3) := inner_loop.next_coefficient i 2 sample_bits2
  let (sample_bits4, coefficient4) := inner_loop.next_coefficient i 3 sample_bits3
  let pe_dst1 := pe_dst.set! i coefficient1
  let pe_dst2 := pe_dst1.set! (i + 1) coefficient2
  let pe_dst3 := pe_dst2.set! (i + 2) coefficient3
  let pe_dst4 := pe_dst3.set! (i + 3) coefficient4
  (pe_dst4, sample_bits4)

def Target2.samplePolyCBD.eta3_loop (s : Target2.samplePolyCBDState) : Polynomial :=
  if s.i < key.MLWE_POLYNOMIAL_COEFFICIENTS then
    let a := List.slice s.src_i (s.src_i + 4) s.B.1.toList
    let sample_bits := BitVec.fromLEBytes a
    let src_i1 := s.src_i + 3
    let i1 := (sample_bits &&& 2396745#u32)
    let i2 := sample_bits >>> 1
    let i3 := i2 &&& 2396745#u32
    let i4 := i1 + i3
    let i5 := sample_bits >>> 2
    let i6 := i5 &&& 2396745#u32
    let sample_bits1 := i4 + i6
    let sample_bits2 := sample_bits1.setWidth' (by scalar_tac)
    let (pe_dst1, _) := eta3_loop.inner_loop s.pe_dst s.i sample_bits2
    let i7 := s.i + 4
    eta3_loop {η := s.η, pe_dst := pe_dst1, B := s.B, src_i := src_i1, i := i7}
  else
    s.pe_dst
termination_by key.MLWE_POLYNOMIAL_COEFFICIENTS - s.i
decreasing_by scalar_tac

def Target2.samplePolyCBD {η : Η} (B : Vector Byte (64 * η)) : Polynomial :=
  if η.1 = 3 then samplePolyCBD.eta3_loop {η := η, pe_dst := Polynomial.zero, B := B, src_i := 0, i := 0}
  else samplePolyCBD.eta2_loop {η := η, pe_dst := Polynomial.zero, B := B, src_i := 0, i := 0}

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
  sorry

def Target2.samplePolyCBD.eta3_loop.spec {η : Η} (s : Target2.samplePolyCBDState)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD s.B)[j]!)
  (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 4 = s.i * 3)
  (i : ℕ) (hi : i < 256) (hη : s.η.1 = 3) : (eta3_loop s)[i]! = (Target.samplePolyCBD s.B)[i]! := by
  unfold eta3_loop
  split
  . simp only [UScalar.ofNat_val_eq, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, BitVec.setWidth'_eq]
    apply eta3_loop.spec
    . exact η
    . intro j hj1
      simp only at hj1
      simp only
      by_cases hj2 : j < s.i
      . rw [eta3_loop.inner_loop.preserves_below]
        . exact hs1 j hj2
        . exact hj2
      . next hs4 =>
        olet hsample_bits : sample_bits :=
          ((BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList) &&&
                2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList).length)) +
              (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList) >>> 1 &&&
                2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList).length)) +
            (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList) >>> 2 &&&
              2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList).length)))
        have j_upper_bound : j < 256 := by
          -- `s.i + 4 ≤ 256` because `s.i < 256` (from `hs4`) and `4 ∣ s.i` from `hs3`
          -- Since `j < s.i + 4` (from `hj1`) it follows that `j < 256` as desired
          sorry
        rw [Target.samplePolyCBD.spec s.B j (by omega), ← Symcrust.SpecAux.Target.bytesToBits.eq_spec]
        have hBytesToBits := Target.bytesToBits.spec s.B
        unfold Target.bytesToBits.post at hBytesToBits
        unfold inner_loop
        simp only [Q, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum]
        have hj3 : j = s.i ∨ j = s.i + 1 ∨ j = s.i + 2 ∨ j = s.i + 3 := by omega
        rcases hj3 with hj3 | hj3 | hj3 | hj3
        . rw [Vector.getElem!_set!_ne (by omega), Vector.getElem!_set!_ne (by omega),
            Vector.getElem!_set!_ne (by omega), Vector.getElem!_set! (by omega)]
          simp only [hj3, hη, Nat.mul_assoc 2 s.i 3, ← hs3, Nat.mul_comm s.src_i 4,
            ← Nat.mul_assoc 2 4 s.src_i, Nat.reduceMul, Fin.unfold3 hη]
          specialize hBytesToBits s.src_i (by omega)
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
            sorry
          replace hsample_bits_slice : sample_bits_slice < 64 := by
            rw [hsample_bits_slice]
            exact Nat.lt_succ_of_le Nat.and_le_right
          clear hBytesToBits
          revert s_B_byte
          revert sample_bits_slice
          brute
        . rw [Vector.getElem!_set!_ne (by omega), Vector.getElem!_set!_ne (by omega),
            Vector.getElem!_set! (by omega)]
          simp only [hj3, hη, Nat.mul_assoc 2 (s.i + 1) 3, Nat.mul_comm (s.i + 1) 3,
            Nat.mul_add 3 s.i 1, Nat.mul_comm 3 s.i, ← hs3, Nat.mul_comm s.src_i 4, mul_one,
            Nat.mul_add 2 (4 * s.src_i) 3, ← Nat.mul_assoc 2 4 s.src_i, Nat.reduceMul,
            Nat.add_assoc, Fin.unfold3 hη, add_zero, Nat.reduceAdd]
          conv in 8 * s.src_i + 8 => rw [(by omega : 8 * s.src_i + 8 = 8 * (s.src_i + 1) + 0)]
          conv in 8 * s.src_i + 9 => rw [(by omega : 8 * s.src_i + 9 = 8 * (s.src_i + 1) + 1)]
          conv in 8 * s.src_i + 10 => rw [(by omega : 8 * s.src_i + 10 = 8 * (s.src_i + 1) + 2)]
          conv in 8 * s.src_i + 11 => rw [(by omega : 8 * s.src_i + 11 = 8 * (s.src_i + 1) + 3)]
          rw [hBytesToBits s.src_i (by omega) 6 (by omega),
              hBytesToBits s.src_i (by omega) 7 (by omega),
              hBytesToBits (s.src_i + 1) (by omega) 0 (by omega),
              hBytesToBits (s.src_i + 1) (by omega) 1 (by omega),
              hBytesToBits (s.src_i + 1) (by omega) 2 (by omega),
              hBytesToBits (s.src_i + 1) (by omega) 3 (by omega)]
          unfold inner_loop.next_coefficient
          simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
            BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight,
            BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod,
            Nat.mod_add_mod]
          olet hsample_bits_slice : sample_bits_slice := (sample_bits.toNat % 4294967296) >>> 6 &&& 63
          olet hs_B_byte0 : s_B_byte0 := s.B[s.src_i]!
          olet hs_B_byte1 : s_B_byte1 := s.B[s.src_i + 1]!
          replace hs_B_byte0 : sample_bits_slice = sorry := by -- **TODO**
            sorry
          replace hs_B_byte1 : sample_bits_slice = sorry := by -- **TODO**
            sorry
          replace hsample_bits_slice : sample_bits_slice < 64 := by
            rw [hsample_bits_slice]
            exact Nat.lt_succ_of_le Nat.and_le_right
          clear hBytesToBits
          revert hs_B_byte0 hs_B_byte1
          revert s_B_byte0 s_B_byte1
          revert sample_bits_slice
          -- Once I finish the statements of `hs_B_byte0` and `hs_B_byte1` this should be provable via `brute`
          sorry
        . rw [Vector.getElem!_set!_ne (by omega), Vector.getElem!_set! (by omega)]
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
          rw [hBytesToBits (s.src_i + 1) (by omega) 4 (by omega),
              hBytesToBits (s.src_i + 1) (by omega) 5 (by omega),
              hBytesToBits (s.src_i + 1) (by omega) 6 (by omega),
              hBytesToBits (s.src_i + 1) (by omega) 7 (by omega),
              hBytesToBits (s.src_i + 2) (by omega) 0 (by omega),
              hBytesToBits (s.src_i + 2) (by omega) 1 (by omega)]
          unfold inner_loop.next_coefficient
          simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
            BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight,
            BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod,
            Nat.mod_add_mod]
          olet hsample_bits_slice : sample_bits_slice :=
            (sample_bits.toNat % 4294967296) >>> 6 >>> 6 &&& 63
          olet hs_B_byte1 : s_B_byte1 := s.B[s.src_i + 1]!
          olet hs_B_byte2 : s_B_byte2 := s.B[s.src_i + 2]!
          replace hs_B_byte1 : sample_bits_slice = sorry := by -- **TODO**
            sorry
          replace hs_B_byte2 : sample_bits_slice = sorry := by -- **TODO**
            sorry
          replace hsample_bits_slice : sample_bits_slice < 64 := by
            rw [hsample_bits_slice]
            exact Nat.lt_succ_of_le Nat.and_le_right
          clear hBytesToBits
          revert hs_B_byte1 hs_B_byte2
          revert s_B_byte1 s_B_byte2
          revert sample_bits_slice
          -- Once I finish the statements of `hs_B_byte1` and `hs_B_byte2` this should be provable via `brute`
          sorry
        . rw [Vector.getElem!_set! (by omega)]
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
          rw [hBytesToBits (s.src_i + 2) (by omega) 2 (by omega),
              hBytesToBits (s.src_i + 2) (by omega) 3 (by omega),
              hBytesToBits (s.src_i + 2) (by omega) 4 (by omega),
              hBytesToBits (s.src_i + 2) (by omega) 5 (by omega),
              hBytesToBits (s.src_i + 2) (by omega) 6 (by omega),
              hBytesToBits (s.src_i + 2) (by omega) 7 (by omega)]
          unfold inner_loop.next_coefficient
          simp only [BitVec.ofNat_eq_ofNat, ntt.Q.eq, UScalar.ofNat_val_eq, Nat.cast_ofNat,
            BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ushiftRight,
            BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod,
            Nat.mod_add_mod]
          olet hsample_bits_slice : sample_bits_slice :=
            (sample_bits.toNat % 4294967296) >>> 6 >>> 6 >>> 6 &&& 63
          olet hs_B_byte2 : s_B_byte2 := s.B[s.src_i + 2]!
          replace hs_B_byte2 : sample_bits_slice = sorry := by -- **TODO**
            sorry
          replace hsample_bits_slice : sample_bits_slice < 64 := by
            rw [hsample_bits_slice]
            exact Nat.lt_succ_of_le Nat.and_le_right
          clear hBytesToBits
          revert hs_B_byte2 s_B_byte2
          revert sample_bits_slice
          -- Once I finish the statement of `hs_B_byte2` this should be provable via `brute`
          sorry
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

def Target2.samplePolyCBD.eta2_loop.spec {η : Η} (s : Target2.samplePolyCBDState) (i : ℕ) (hi : i < 256)
  (hη : s.η.1 = 2) : (eta2_loop s)[i]! = (Target.samplePolyCBD s.B)[i]! := by
  sorry

def Target2.samplePolyCBD.spec {η : Η} (B : Vector Byte (64 * η)) : samplePolyCBD B = Spec.samplePolyCBD B := by
  rw [← Target.samplePolyCBD.eq_spec]
  rw [Vector.eq_iff_forall_eq_getElem!]
  intro i hi
  unfold samplePolyCBD
  split
  . have hs1 : ∀ j < 0, Polynomial.zero[j]! = (Target.samplePolyCBD B)[j]! := by simp
    have hs2 : ∀ j < 256, 0 ≤ j → Polynomial.zero[j]! = 0 := by
      intro j hj1 hj2
      rw [Polynomial.zero, Vector.getElem!_replicate hj1]
    have hs3 : 0 * 4 = 0 * 3 := by simp
    apply eta3_loop.spec <;> assumption
  . have : η.1 = 2 := by
      have hη := η.2
      simp only [Set.instMembership, Set.Mem, insert, Set.insert, setOf, singleton, Set.singleton] at hη
      omega
    apply eta2_loop.spec <;> assumption

end Symcrust.SpecAux
