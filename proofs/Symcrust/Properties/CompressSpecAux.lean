import Symcrust.Spec
import Symcrust.Properties.Polynomials

/-!
An auxiliary specification that we use to prove a refinement result.
This specification refines the specification in `Spec`, and is refined by the code.
It does not need to be trusted.
-/

attribute [-simp] List.getElem!_eq_getElem?_getD List.reduceReplicate Aeneas.SRRange.foldWhile_step

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

/-!
# ByteEncode
-/

#check BitVec
#check BitVec.ofNat

def byteEncodeToBits (d : ℕ) (f : List (ZMod n)) : List Bool :=
  List.flatten (List.map (fun a => (List.map (fun i => a.val.testBit i) (List.range d))) f)

def bitsToBytes1 (l : ℕ) (b : List Bool) : List Byte :=
  List.map (fun i => BitVec.ofBoolListLE (List.map (fun j => b[8 * i + j]!) (List.range 8))) (List.range l)

def BitVec.toLEBytes {n : ℕ} (b : BitVec n) : List Byte :=
  if n > 0 then
    b.setWidth 8 :: BitVec.toLEBytes ((b >>> 8).setWidth (n - 8))
  else []

def encodeNatToBytes (d : ℕ) (coeff : ℕ) (nBitsInAcc : ℕ) (nBitsInCoeff : ℕ) (acc : List Bool)
  (hBitsInCoeff : 0 < nBitsInCoeff := by omega)
  (hBitsInAcc : nBitsInAcc < 32 := by omega)
  : List Byte :=
  let nBitsToEncode := min nBitsInCoeff (32 - nBitsInAcc)
  let bitsToEncode := List.take nBitsToEncode coeff.bits
  let nBitsInCoeff := nBitsInCoeff - nBitsToEncode
  let acc := acc ++ bitsToEncode
  let nBitsInAcc := nBitsInAcc + nBitsToEncode
  if h: nBitsInAcc = 32 then
    let out := BitVec.toLEBytes (BitVec.ofBoolListLE acc)
    if h: nBitsInCoeff > 0 then
      out ++ encodeNatToBytes d coeff 0 nBitsInCoeff []
    else out
  else
    if h: nBitsInCoeff > 0 then encodeNatToBytes d coeff nBitsInAcc nBitsInCoeff acc
    else []
termination_by nBitsInCoeff
decreasing_by
  scalar_decr_tac

def encodeToBytes (d : ℕ) (f : List ℕ) (bitsInAcc bitsInCoeff : ℕ)
  (acc : List Bool)
  : List Byte :=
  let nBitsToEncode := min (bitsInCoeff, 32 - bitsInAcc)
  let bitsToEncode := List.take nBitsToEncode
  sorry

/-
#[inline(always)]
fn inner_loop(pb_dst: &mut [u8], cb_dst_written: &mut usize, accumulator: &mut u32,
              n_bits_in_accumulator: &mut u32, mut n_bits_in_coefficient: u32, mut coefficient: u32,
) {
    while {
        let n_bits_to_encode = min(n_bits_in_coefficient, 32-*n_bits_in_accumulator);

        let bits_to_encode = coefficient & ((1<<n_bits_to_encode)-1);
        coefficient >>= n_bits_to_encode;
        n_bits_in_coefficient -= n_bits_to_encode;

        *accumulator |= bits_to_encode << *n_bits_in_accumulator;
        *n_bits_in_accumulator += n_bits_to_encode;
        if *n_bits_in_accumulator == 32
        {
            pb_dst[*cb_dst_written..*cb_dst_written+4].copy_from_slice(&u32::to_le_bytes(*accumulator));
            *cb_dst_written += 4;
            *accumulator = 0;
            *n_bits_in_accumulator = 0;
        };
        n_bits_in_coefficient > 0
    } {}
}
inner_loop(pb_dst, &mut cb_dst_written, &mut accumulator, &mut n_bits_in_accumulator, n_bits_in_coefficient, coefficient);
-/

/-!
# BitsToBytes
-/

def bitsToBytes (l : Nat) {n:Nat} (b : List Bool) : List Byte :=
  List

def bitsToBytes (l : Nat) {n:Nat} (b : Vector Bool n) (h : n = 8 * l := by ring_nf) : Vector Byte l := Id.run do
  let mut B := Vector.replicate l 0
  for h: i in [0:8*l] do
    B := B.set (i/8) (B[i/8]  + ((b[i]).toUInt8 * ((2 ^(i%8)).toUInt8)))
  pure B

/-!
# Compress
-/
#exit

@[simp] def COMPRESS_MULCONSTANT := BitVec.ofNat 64 0x9d7dbb
@[simp] def COMPRESS_SHIFTCONSTANT := 35

-- TODO: move
@[simp, bvify_simps]
theorem BitVec.ofNat_mul (n : ℕ) (x y : ℕ) : BitVec.ofNat n (x * y) = BitVec.ofNat n x * BitVec.ofNat n y := by
  conv => lhs; unfold BitVec.ofNat
  conv => rhs; simp only [BitVec.mul_def]
  simp only [Fin.ofNat'_eq_cast, Nat.cast_mul, BitVec.toFin_ofNat]

-- TODO: move
theorem BitVec.ofNat_pow (n : ℕ) (x d : ℕ) : BitVec.ofNat n (x ^ d) = (BitVec.ofNat n x)^d := by
  conv => rhs; unfold HPow.hPow instHPow Pow.pow BitVec.instPowNat_mathlib; simp only
  unfold BitVec.ofNat
  simp only [Fin.ofNat'_eq_cast, Nat.cast_pow]

@[simp] def compress.mulConstant : BitVec 64 := BitVec.ofNat 64 0x9d7dbb
@[simp] def compress.shiftConstant : ℕ := 35

def compress (x : BitVec 64) (d : ℕ) : BitVec 64 :=
  let multiplication := x * compress.mulConstant
  let coefficient := (multiplication >>> (compress.shiftConstant - (d + 1)))
  let coefficient := (coefficient + 1) >>> 1
  let coefficient := coefficient &&& (1 <<< d) - 1#64
  coefficient

set_option maxHeartbeats 10000000 in
/-- The compression is implemented in a clever way.
    We brute force the proof by enumerating all the cases for `d < 12`, then using `bv_decide`.
-/
private theorem compress_eq_aux (x : BitVec 64) (h : x < 3329#64) (d : ℕ) (hd : d < 12) :
  compress x d = ((2^(d+1) * x + Q) / (2 * Q)) % BitVec.ofNat 64 (2^d)
  := by
  simp [compress, ← BitVec.ofNat_pow]
  cases d; simp; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  cases d; simp; bv_decide; rename_i d
  ring_nf at hd; simp at hd

theorem compress_eq (x : BitVec 64) (h : x < 3329#64) (d : ℕ) (hd : d < 12) :
  compress x d = ⌈ ((2^d : ℚ) / (Q : ℚ)) * x.toNat ⌋ % (2^d)
  := by
  -- Getting rid of the `⌈ ... ⌋`
  have : ((2^d : ℚ) / (Q : ℚ)) * (x.toNat : ℚ) = ((2 ^ d * x.toNat : ℕ) : ℚ) / (Q : ℚ) := by
    simp; ring_nf
  rw [this]; clear this
  rw [Nat.rat_round_div]; swap; simp

  -- Small rewrite
  have : ((2 * ↑(2 ^ d * x.toNat) + ↑Q) / (2 * ↑Q) : Int) =
         (((2^(d+1) * x.toNat + Q) / (2 * Q)) : Int) := by
    simp; ring_nf
  rw [this]; clear this

  -- Finish the proof by simplifying everything
  rw [compress_eq_aux x h d hd]
  simp only [BitVec.ofNat_eq_ofNat, ← BitVec.ofNat_pow, Nat.cast_ofNat, BitVec.reduceMul,
    Int.reduceMul]
  natify
  norm_cast
  simp only [BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.mod_mul_mod, Nat.reduceMod, Nat.mod_add_mod, BitVec.natCast_eq_ofNat]

  -- Getting rid of the modulo
  congr
  have : 2 ^(d+1) ≤ 2^12 := by apply Nat.pow_le_pow_of_le_right <;> omega
  have : 2 ^ (d + 1) * x.toNat ≤ 2^12 * 3328 := by
    natify at h
    scalar_tac +nonLin
  omega

end Symcrust.SpecAux
