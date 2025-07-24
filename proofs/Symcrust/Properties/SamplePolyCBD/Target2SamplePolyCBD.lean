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
set_option brute.trust true

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

set_option brute.trust true in
theorem Target2.samplePolyCBD.eta3_loop.spec.aux0 (s : samplePolyCBDState)
  (hs1 : ∀ j < s.i, s.pe_dst[j]! = (Target.samplePolyCBD s.B)[j]!) (hs2 : ∀ j < 256, s.i ≤ j → s.pe_dst[j]! = 0)
  (hs3 : s.src_i * 4 = s.i * 3) (hη : s.η.val = 3) (hs4 : s.i < ↑key.MLWE_POLYNOMIAL_COEFFICIENTS) (j : ℕ)
  (hj1 : j < s.i + 4) (hj2 : ¬j < s.i)
  (sample_bits : BitVec (8 * (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList).length))
  (hsample_bits :
    sample_bits =
      (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList) &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList).length)) +
          (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList) >>> 1 &&&
            2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList).length)) +
        (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList) >>> 2 &&&
          2396745#(8 * (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList).length)))
  (hBytesToBits : ∀ i < 64 * s.η.val, ∀ j < 8, (Target.bytesToBits s.B)[8 * i + j]! = s.B[i]!.testBit j)
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
    ∑ (x : Fin s.η.val), ↑(Target.bytesToBits s.B)[2 * j * ↑s.η + ↑x]!.toNat -
      ∑ (x : Fin s.η.val), ↑(Target.bytesToBits s.B)[2 * j * ↑s.η + ↑s.η + ↑x]!.toNat := by
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
    -- Automation note: The automation has a hard time dealing with `min`, hence why I frequently have
    -- to use `rcases hmin with hmin | hmin <;> (rw [hmin]; ...)` instead of calling a single tactic directly
    have hmin : min (192 - s.src_i) 4 = 3 ∨ min (192 - s.src_i) 4 = 4 := by scalar_tac
    simp [List.slice_length, Array.length_toList, Vector.size_toArray,
      add_tsub_cancel_left, ← BitVec.getElem!_eq_getElem, BitVec.getElem!_and, hη]
    olet hz : z := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList)).toNat >>> 2
    olet hy : y := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList)).toNat >>> 1
    olet hx : x := (BitVec.fromLEBytes (List.slice s.src_i (s.src_i + 4) s.B.toArray.toList)).toNat
    olet hx' : x' := (x &&& 2396745 % 2 ^ (8 * min (192 - s.src_i) 4))
    olet hy' : y' := (y &&& 2396745 % 2 ^ (8 * min (192 - s.src_i) 4))
    olet hz' : z' := (z &&& 2396745 % 2 ^ (8 * min (192 - s.src_i) 4))
    rw [Nat.mod_eq_of_lt] at hx' hy' hz' <;> (try rcases hmin with hmin | hmin <;> (rw [hmin]; decide))
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
      have : BitVec.ofNat 8 (x' + y' + z') % 2#8 ^ 6 = BitVec.ofNat 8 (x' + y' + z') := by
        clear hx' hy' hz'; revert x'; revert y'; revert z'; brute
      rw [this, BitVec.add_def, BitVec.add_def]
      clear this
      ext k hk
      simp only [← BitVec.getElem!_eq_getElem, BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat,
        Nat.reducePow, BitVec.toNat_and, Nat.reduceMod, BitVec.toNat_ushiftRight, Nat.mod_add_mod]
      have : ((x' + y' + z') % 256).testBit k = (x' + y' + z').testBit k := by
        olet ha : a := x' + y' + z'
        replace ha : a < 2396746 * 3 := by omega
        revert a
        revert k
        brute
      rw [this, Nat.mod_eq_of_lt]
      . rw [hy] at hy'
        rw [hz] at hz'
        rw [hx', hy', hz']

        let xBound := x % 2^6
        have h1 : ∀ k < 8, (xBound &&& 2396745).testBit k = (BitVec.toNat s_B_byte &&& 9).testBit k := by
          sorry
        have h2 : ∀ k < 8, ((xBound >>> 1) &&& 2396745).testBit k = (BitVec.toNat s_B_byte &&& 9).testBit k := by
          sorry
        have h3 : ∀ k < 8, ((xBound >>> 2) &&& 2396745).testBit k = (BitVec.toNat s_B_byte &&& 9).testBit k := by
          sorry
        revert h1 h2 h3
        clear hx hy hz hx' hy' hz'
        revert x

        -- Plan: Write a lemma that says if (bottom n bits of a) = (bottom n bits of b) then
        -- (a + c).testBit k = (b + c).testBit k (so long as `k ≤ n`)

        sorry
        /-
        replace hx' : ∀ k < 8, x'.testBit k = (BitVec.toNat s_B_byte &&& 9).testBit k := by
          intro k hk
          rw [hx', hx]
          simp only [Nat.testBit_and]
          sorry
        replace hy' : ∀ k < 8, y'.testBit k =
          ((BitVec.toNat s_B_byte >>> 1) &&& 9).testBit k := by
          sorry
        replace hz' : ∀ k < 8, z'.testBit k =
          ((BitVec.toNat s_B_byte >>> 2) &&& 9).testBit k := by
          sorry
        clear this hBytesToBits hs_B_byte
        revert hx' hy' hz'
        revert s_B_byte
        revert z'
        revert y'
        revert x'
        revert k
        sorry -- brute
        -/
      . have : BitVec.toNat s_B_byte &&& 9 ≤ 9 := Nat.and_le_right
        have : (BitVec.toNat s_B_byte >>> 1) &&& 9 ≤ 9 := Nat.and_le_right
        have : (BitVec.toNat s_B_byte >>> 2) &&& 9 ≤ 9 := Nat.and_le_right
        omega
    . clear hx' hy' hz'
      revert z'; revert y'; revert x'; rcases hmin with hmin | hmin <;> (rw [hmin]; brute)
    . clear hx' hy' hz'
      rw [Nat.mod_eq_of_lt]
      . revert z'; revert y'; revert x'; brute
      . revert z'; revert y'; revert x'; rcases hmin with hmin | hmin <;> (rw [hmin]; brute)
  replace hsample_bits_slice : sample_bits_slice < 64 := by
    rw [hsample_bits_slice]
    exact Nat.lt_succ_of_le Nat.and_le_right
  clear hBytesToBits
  revert s_B_byte
  revert sample_bits_slice
  brute

/-
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
        rw [Target.samplePolyCBD.spec s.B j (by scalar_tac), ← Symcrust.SpecAux.Target.bytesToBits.eq_spec]
        have hBytesToBits := Target.bytesToBits.spec s.B
        unfold Target.bytesToBits.post at hBytesToBits
        unfold inner_loop
        simp only [Q, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum]
        have hj3 : j = s.i ∨ j = s.i + 1 ∨ j = s.i + 2 ∨ j = s.i + 3 := by omega
        rcases hj3 with hj3 | hj3 | hj3 | hj3
        . apply eta3_loop.spec.aux0 <;> assumption
        . rw [Vector.getElem!_set!_ne (by omega), Vector.getElem!_set!_ne (by omega),
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
        . rw [Vector.getElem!_set!_ne (by omega), Vector.getElem!_set! (by scalar_tac)]
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
        . rw [Vector.getElem!_set! (by scalar_tac)]
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
-/

end Symcrust.SpecAux
