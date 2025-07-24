import Symcrust.Spec
import Symcrust.Properties.Polynomials
import Symcrust.Properties.BitsAndBytes.BitsToBytes
import Symcrust.Properties.BitsAndBytes.BytesToBits
import Symcrust.Properties.CompressEncode.StreamEncode
import Symcrust.Brute

/-!
This file contains theorems about `Symcrust.Spec.compress` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to (4.7) (Compress).
    - `Lean spec (monadic/functional)` corresponds to `Symcrust.Spec.compress`.
      - There is no need to distinguish `Lean spec (monadic)` from `Lean spec (functional)` for this
        function because the natural Lean translation of the Nist specification is already functional.
    - `Auxiliary spec` corresponds to `Symcrust.SpecAux.compress`.
    - `⟷₃` is bundled together with `⟷₂` in the form of `compress_eq`.
    - Analogues for later portions of the verification pipeline appear in other files.

Additionally, this file also contains `Stream.compressOpt_encode` (along with the theorem about it
`Stream.compressOpt_encode_eq`). These can be viewed as the analogues to `Auxiliary spec` and `⟷₃`
for a function that combines Nist's compress and encode functions.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

/-!
# Compress and encode
-/

def compressOpt (d : ℕ) (x : ℕ) : ℤ := if d < 12 then ⌈ ((2^d : ℚ) / (Q : ℚ)) * x ⌋ % 2^d else x

def Stream.compressOpt_encode.body (d : ℕ) {n : ℕ} (x : Spec.Zq) (s : EncodeState n) :=
  Stream.encode.body d (compressOpt d x.val) s

def Stream.compressOpt_encode.recBody (d : ℕ) {n : ℕ} (F : Vector (ZMod Q) 256) (s : EncodeState n) (i : ℕ) :
  EncodeState n :=
  List.foldl (fun s i => compressOpt_encode.body d F[i]! s) s (List.range' i (256 - i))

def Stream.compressOpt_encode
  (d n : ℕ) (F : Vector (ZMod Q) 256) : List Byte :=
  let s : EncodeState n := {
    b := List.replicate (32 * d) 0,
    bi := 0,
    acc := 0,
    acci := 0,
  }
  (compressOpt_encode.recBody d F s 0).b

def Stream.compressOpt_encode_eq (d n : ℕ) (F : Vector Zq 256) [NeZero (m d)]
  (hd : 0 < d := by omega)
  (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega)
  (hn1 : n ∣ 32 := by omega) :
  compressOpt_encode d n F = (Spec.byteEncode d (F.map (fun (x : Zq) => (compressOpt d x.val : ZMod (m d))))).toList := by
  have := Stream.encode.spec d n (F.map (fun (x : Zq) => (compressOpt d x.val : ZMod (m d))))
  rw [← this]; clear this
  --
  simp only [compressOpt_encode, compressOpt_encode.recBody, BitVec.ofNat_eq_ofNat, tsub_zero,
    encode, encode.recBody]
  apply congrArg
  apply List.forall_imp_foldl_eq
  . simp only
  . simp only [List.mem_range'_1, zero_le, zero_add, true_and]
    intros s i hi
    simp only [compressOpt_encode.body]
    simp_lists

/-!
# Compress
-/

def compress (d : ℕ) (x : ℕ) : ℕ :=
  let multiplication := x * 0x9d7dbb
  let coefficient := (multiplication >>> (35 - (d + 1)))
  let coefficient := (coefficient + 1) >>> 1
  let coefficient := coefficient &&& (1 <<< d) - 1
  coefficient

theorem compress_eq (x : ℕ) (h : x < 3329) (d : ℕ) (hd : d < 12) :
  compress d x = ⌈ ((2^d : ℚ) / (Q : ℚ)) * x ⌋ % (2^d)
  := by
  revert d x
  brute

end Symcrust.SpecAux
