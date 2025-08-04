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
  B : Array Byte
  hB : 64 * η.1 + 1 ≤ B.size
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

def Target2.samplePolyCBD.eta2_loop.inner_loop.next_coefficient (i j : ℕ) (sample_bits : BitVec 32) :
  BitVec 32 × UScalar UScalarTy.U16 :=
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
  (sample_bits1, i6)

/-- This is a simplified and unrolled version of the Aeneas translation, structured for ease verification -/
def Target2.samplePolyCBD.eta2_loop.inner_loop (pe_dst : Polynomial) (i : ℕ) (sample_bits : BitVec 32) :
  Polynomial × BitVec 32 :=
  let (sample_bits1, coefficient1) := inner_loop.next_coefficient i 0 sample_bits
  let (sample_bits2, coefficient2) := inner_loop.next_coefficient i 1 sample_bits1
  let (sample_bits3, coefficient3) := inner_loop.next_coefficient i 2 sample_bits2
  let (sample_bits4, coefficient4) := inner_loop.next_coefficient i 3 sample_bits3
  let (sample_bits5, coefficient5) := inner_loop.next_coefficient i 4 sample_bits4
  let (sample_bits6, coefficient6) := inner_loop.next_coefficient i 5 sample_bits5
  let (sample_bits7, coefficient7) := inner_loop.next_coefficient i 6 sample_bits6
  let (sample_bits8, coefficient8) := inner_loop.next_coefficient i 7 sample_bits7
  let pe_dst1 := pe_dst.set! i coefficient1
  let pe_dst2 := pe_dst1.set! (i + 1) coefficient2
  let pe_dst3 := pe_dst2.set! (i + 2) coefficient3
  let pe_dst4 := pe_dst3.set! (i + 3) coefficient4
  let pe_dst5 := pe_dst4.set! (i + 4) coefficient5
  let pe_dst6 := pe_dst5.set! (i + 5) coefficient6
  let pe_dst7 := pe_dst6.set! (i + 6) coefficient7
  let pe_dst8 := pe_dst7.set! (i + 7) coefficient8
  (pe_dst8, sample_bits8)

def Target2.samplePolyCBD.eta2_loop (s : Target2.samplePolyCBDState) : Polynomial :=
  if s.i < key.MLWE_POLYNOMIAL_COEFFICIENTS then
    let a := List.slice s.src_i (s.src_i + 4) s.B.1
    let sample_bits := BitVec.fromLEBytes a
    let src_i1 := s.src_i + 4
    let i1 := (sample_bits &&& 1431655765#u32)
    let i2 := sample_bits >>> 1
    let i3 := i2 &&& 1431655765#u32
    let sample_bits1 := i1 + i3
    let sample_bits2 := sample_bits1.setWidth' (by scalar_tac)
    let (pe_dst1, _) := eta2_loop.inner_loop s.pe_dst s.i sample_bits2
    let i4 := s.i + 8
    eta2_loop {η := s.η, pe_dst := pe_dst1, B := s.B, hB := s.hB, src_i := src_i1, i := i4}
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
    let a := List.slice s.src_i (s.src_i + 4) s.B.1
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
    eta3_loop {η := s.η, pe_dst := pe_dst1, B := s.B, hB := s.hB, src_i := src_i1, i := i7}
  else
    s.pe_dst
termination_by key.MLWE_POLYNOMIAL_COEFFICIENTS - s.i
decreasing_by scalar_tac

def Target2.samplePolyCBD {η : Η} (B : Array Byte) (hB : 64 * η.1 + 1 ≤ B.size) : Polynomial :=
  if η.1 = 3 then samplePolyCBD.eta3_loop {η, pe_dst := Polynomial.zero, B, hB, src_i := 0, i := 0}
  else samplePolyCBD.eta2_loop {η, pe_dst := Polynomial.zero, B, hB, src_i := 0, i := 0}

end Symcrust.SpecAux
