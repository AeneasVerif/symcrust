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
open Aeneas.SRRange

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
  compress x d = ((2^(d+1) * x.toNat + Q) / (2 * Q)) % (2^d)
  := by
  have := compress_eq_aux x h d hd
  rw [this]
  simp only [BitVec.ofNat_eq_ofNat, Nat.cast_ofNat, BitVec.reduceMul, BitVec.natCast_eq_ofNat,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
  natify
  simp only [← BitVec.ofNat_pow, BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mul_mod, Nat.reduceMod, Nat.mod_add_mod]

end Symcrust.SpecAux
