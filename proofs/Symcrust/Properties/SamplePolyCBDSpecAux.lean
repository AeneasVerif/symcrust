import Symcrust.Spec
import Symcrust.Code.Funs
import Symcrust.Properties.Brute

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.Std Aeneas.SRRange

set_option maxHeartbeats 1000000

def Target.samplePolyCBD.body {rangeStart : Nat} {η : Η} (b : Vector Bool (8 * (64 * ↑η))) (f : Polynomial)
  (i : { x // x ∈ List.range' rangeStart (256 - rangeStart) }) : Polynomial :=
  have hi := i.2
  have : 2 * i.1 * η ≤ 510 * η := by
    simp only [List.mem_range'_1] at hi
    scalar_tac +nonLin
  let x := ∑ (j : Fin η), Bool.toNat b[2 * i.1 * η + j]
  let y := ∑ (j : Fin η), Bool.toNat b[2 * i.1 * η + η + j]
  f.set! i (x - y)

def Target.samplePolyCBD.recBody {η : Η} (b : Vector Bool (8 * (64 * ↑η))) (f : Polynomial) (i : Nat) : Polynomial :=
  List.foldl (body b) f (List.range' i (256 - i)).attach

def Target.samplePolyCBD {η : Η} (B : Vector Byte (64 * η)) : Polynomial :=
  let b := bytesToBits B
  let f := Polynomial.zero
  samplePolyCBD.recBody b f 0

def Target.samplePolyCBD.eq_spec {η : Η} (B : Vector Byte (64 * η)) :
  samplePolyCBD B = Spec.samplePolyCBD B := by
  unfold samplePolyCBD samplePolyCBD.recBody samplePolyCBD.body Spec.samplePolyCBD
  simp only [Nat.sub_zero, Vector.Inhabited_getElem_eq_getElem!, Nat.cast_sum, List.mem_range'_1,
    zero_le, zero_add, true_and, List.foldl_subtype, List.unattach_attach, bind_pure_comp, map_pure,
    forIn'_eq_forIn, forIn_eq_forIn_range', size, tsub_zero, Nat.reduceAdd, Nat.add_one_sub_one,
    Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]

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

def Target2.samplePolyCBD.eta3_loop.inner_loop (pe_dst : Polynomial) (i j : ℕ) (sample_bits : BitVec 32) :
  Polynomial × BitVec 32 :=
  if j < 4#usize then
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
    let pe_dst1 := pe_dst.set! i5 i6
    let j1 := j + 1
    inner_loop pe_dst1 i j1 sample_bits1
  else
    (pe_dst, sample_bits)
termination_by 4 - j
decreasing_by scalar_tac

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
    let (pe_dst1, _) := eta3_loop.inner_loop s.pe_dst s.i 0 sample_bits2
    let i7 := s.i + 4
    eta3_loop {η := s.η, pe_dst := pe_dst1, B := s.B, src_i := src_i1, i := i7}
  else
    s.pe_dst
termination_by key.MLWE_POLYNOMIAL_COEFFICIENTS - s.i

def Target2.samplePolyCBD (η : Η) (B : Vector Byte (64 * η)) : Polynomial :=
  if η.1 = 3 then samplePolyCBD.eta3_loop {η := η, pe_dst := Polynomial.zero, B := B, src_i := 0, i := 0}
  else samplePolyCBD.eta2_loop {η := η, pe_dst := Polynomial.zero, B := B, src_i := 0, i := 0}
