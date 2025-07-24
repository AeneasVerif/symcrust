import Mathlib.Algebra.BigOperators.Fin
import Symcrust.Properties.DecodeDecompress.StreamDecode
import Symcrust.Brute

/-!
This file contains theorems about `Symcrust.Spec.decompress` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to (4.8) (Decompress).
    - `Lean spec (monadic/functional)` corresponds to `Symcrust.Spec.decompress`.
      - There is no need to distinguish `Lean spec (monadic)` from `Lean spec (functional)` for this
        function because the natural Lean translation of the Nist specification is already functional.
    - `Auxiliary spec` corresponds to `Symcrust.SpecAux.decompress`.
    - `⟷₃` is bundled together with `⟷₂` in the form of `decompress_eq`.
    - Analogues for later portions of the verification pipeline appear in other files.

Additionally, this file also contains `Stream.decode_decompressOpt` (along with the theorem about it
`Stream.decode_decompressOpt_eq`). These can be viewed as the analogues to `Auxiliary spec` and `⟷₃`
for a function that combines Nist's compress and encode functions.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

def decompressOpt (d : ℕ) (y : ℕ) : Spec.Zq :=
  if d < 12 then ⌈ ((Q : ℚ) / ((2 : ℚ)^d)) * y ⌋ else y

def decompress (d : ℕ) (y : ℕ) : ℕ :=
  if d < 12 then
    let coefficient := y * Q
    let coefficient := coefficient >>> (d - 1)
    let coefficient := coefficient + 1
    coefficient >>> 1
  else
    y

theorem decompress_eq (d : ℕ) (hd : d < 12) (y : ℕ) (h : y < 2^d) :
  decompress d y = ⌈ ((Q : ℚ) / (2^d : ℚ)) * y ⌋ % Q := by
  revert y
  revert d
  brute

def Stream.decode_decompressOpt.body {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : Stream.DecodeState d n) (coefficient_idx : ℕ) : Stream.DecodeState d n :=
  let s' := decode.body b hb s coefficient_idx
  {s' with F := s'.F.set! coefficient_idx (decompressOpt d s'.F[coefficient_idx]!).val}

def Stream.decode_decompressOpt.recBody {d n : ℕ} (b : List Byte) (hb : b.length = 32 * d)
  (s : Stream.DecodeState d n) (i : ℕ) : Stream.DecodeState d n :=
  List.foldl (fun s i => decode_decompressOpt.body b hb s i) s (List.range' i (256 - i))

def Stream.decode_decompressOpt (d n : ℕ) (b : List Byte) (hb : b.length = 32 * d) : Vector ℕ 256 :=
  let s : DecodeState d n := {
    F := Vector.replicate 256 0,
    num_bytes_read := 0,
    acc := 0,
    num_bits_in_acc := 0
  }
  (decode_decompressOpt.recBody b hb s 0).F

lemma Stream.decode_decompressOpt.recBody.inv (d n : ℕ) (B : Vector Byte (32 * d)) (s1 s2 : Stream.DecodeState d n)
  (i j : ℕ) (hi : i ≤ 256) (hj : j < i) (h : s1.F[j]! = s2.F[j]!) :
  (decode_decompressOpt.recBody B.toList B.toList_length s1 i).F[j]! = s2.F[j]! := by
  unfold recBody body
  dcases hi : i = 256
  . simp [hi, h]
  . replace hi : i < 256 := by omega
    have : (List.range' i (256 - i)) = i :: (List.range' (i + 1) (256 - (i + 1))) := by
      rw [List.range'_eq_cons_iff]
      simp only [tsub_pos_iff_lt, Nat.reduceSubDiff, List.range'_inj, Nat.add_left_inj, or_true,
        and_true, true_and]
      omega
    rw [this, List.foldl_cons]
    have : (recBody B.toList B.toList_length (body B.toList B.toList_length s1 i) (i + 1)).F[j]! = s2.F[j]! := by
      apply inv d n B _ _ _ _ (by omega) (by omega)
      unfold body decode.body
      simp only [beq_iff_eq, gt_iff_lt, inf_lt_left, not_le, BitVec.toNat_or,
        BitVec.toNat_shiftLeft]
      split
      . rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne] <;> omega
      . split
        . rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne] <;> omega
        . rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne] <;> omega
    rw [← this]
    rfl

lemma Stream.decode.recBody.inv (d n : ℕ) (B : Vector Byte (32 * d)) (s1 s2 : Stream.DecodeState d n)
  (i j : ℕ) (hi : i ≤ 256) (hj : j < i) (h : s1.F[j]! = s2.F[j]!) :
  (decode.recBody B.toList B.toList_length s1 i).F[j]! = s2.F[j]! := by
  unfold recBody
  dcases hi : i = 256
  . simp [hi, h]
  . replace hi : i < 256 := by omega
    have : (List.range' i (256 - i)) = i :: (List.range' (i + 1) (256 - (i + 1))) := by
      rw [List.range'_eq_cons_iff]
      simp only [tsub_pos_iff_lt, Nat.reduceSubDiff, List.range'_inj, Nat.add_left_inj, or_true,
        and_true, true_and]
      omega
    rw [this, List.foldl_cons, ← recBody]
    apply inv d n B _ _ _ _ (by omega) (by omega)
    unfold body
    split
    . rw [Vector.getElem!_set!_ne] <;> omega
    . simp only [gt_iff_lt, inf_lt_left, not_le, BitVec.toNat_or, BitVec.toNat_shiftLeft]
      split
      . rw [Vector.getElem!_set!_ne] <;> omega
      . rw [Vector.getElem!_set!_ne] <;> omega

def Stream.decode_decompress_eq_aux (d n : ℕ) (B : Vector Byte (32 * d)) (s1 s2 : Stream.DecodeState d n)
  (hd : d < 13) (hdn : d < 8 * n)
  (hB : ∀ i < 256, ∑ a : Fin d, (B[(d * i + ↑a) / 8]!.testBit ((d * i + ↑a) % 8)).toNat * 2 ^ a.val < m d)
  (i j : ℕ) (hi : i ≤ j) (hj : j < 256)
  (h1 : s1.num_bytes_read = s2.num_bytes_read)
  (h2 : s1.acc = s2.acc)
  (h3 : s1.num_bits_in_acc = s2.num_bits_in_acc)
  (h4 : ∀ k ≥ i, s1.F[k]! = s2.F[k]!) :
  (decode_decompressOpt.recBody B.toList B.toList_length s1 i).F[j]! =
    (decompressOpt d (decode.recBody B.toList B.toList_length s2 i).F[j]!).val := by
  unfold decode_decompressOpt.recBody decode.recBody
  have : (List.range' i (256 - i)) = i :: (List.range' (i + 1) (256 - (i + 1))) := by
    rw [List.range'_eq_cons_iff]
    simp only [tsub_pos_iff_lt, Nat.reduceSubDiff, List.range'_inj, Nat.add_left_inj, or_true,
      and_true, true_and]
    omega
  simp only [this, List.foldl_cons]
  rw [← decode_decompressOpt.recBody, ← decode.recBody]
  dcases hij : i = j
  . tlet s1' := decode_decompressOpt.body B.toList B.toList_length s1 i
    tlet s2' := decode.body B.toList B.toList_length s2 i
    have h5 : (decompressOpt d (decode.recBody B.toList B.toList_length s2' (i + 1)).F[j]!).val =
      (decompressOpt d s2'.F[j]!).val := by congr 2; apply Stream.decode.recBody.inv <;> omega
    rw [Stream.decode_decompressOpt.recBody.inv d n B s1' s1' (i + 1) j (by omega) (by omega) rfl, h5]
    unfold s1' s2' decode_decompressOpt.body
    simp only [hij]
    rw [Vector.getElem!_set! (by omega)]
    unfold decode.body decode.load_acc decode.pop_bits_from_acc
    simp only [h3, beq_iff_eq, h1, gt_iff_lt, inf_lt_left, not_le, h2, BitVec.toNat_or,
      BitVec.toNat_shiftLeft]
    split
    . simp only
      rw [Vector.getElem!_set!, Vector.getElem!_set!]
      . -- This is an annoying goal because neither `rw [h1]` nor `simp [h1]` immediately work
        congr 5
        . congr
        . simp [h1]
        . rw [h1]
      . simp only [hj, and_self]
      . simp only [hj, and_self]
    . split
      . simp only [BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod, BitVec.toNat_umod,
          BitVec.toNat_pow, BitVec.toNat_ofNat, BitVec.setWidth'_eq, BitVec.toNat_setWidth]
        rw [h1, Vector.getElem!_set!, Vector.getElem!_set!] <;> omega
      . simp_lists
  . rw [decode_decompress_eq_aux _ _ _ _ _ hd hdn hB (i + 1) j (by omega) hj]
    . simp only [decode_decompressOpt.body, decode.body, h3, beq_iff_eq, h1, gt_iff_lt, inf_lt_left,
        not_le, h2, BitVec.toNat_or, BitVec.toNat_shiftLeft, decode.load_acc]
      split
      . simp
      . split
        . simp
        . simp
    . simp only [decode_decompressOpt.body, decode.body, h3, beq_iff_eq, decode.pop_bits_from_acc,
        decode.load_acc, BitVec.setWidth'_eq, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod,
        BitVec.toNat_umod, BitVec.toNat_setWidth, BitVec.toNat_pow, BitVec.toNat_ofNat, h1, gt_iff_lt,
        inf_lt_left, not_le, h2, BitVec.toNat_or, BitVec.toNat_shiftLeft]
      split
      . rw [h1]
      . split
        . rw [h1]
        . simp
    . simp only [decode_decompressOpt.body, decode.body, h3, beq_iff_eq, decode.pop_bits_from_acc,
        decode.load_acc, BitVec.setWidth'_eq, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod,
        BitVec.toNat_umod, BitVec.toNat_setWidth, BitVec.toNat_pow, BitVec.toNat_ofNat, h1, gt_iff_lt,
        inf_lt_left, not_le, h2, BitVec.toNat_or, BitVec.toNat_shiftLeft]
      split
      . simp
      . split
        . simp
        . simp
    . intro k hk
      simp only [decode_decompressOpt.body, decode.body, h3, beq_iff_eq, decode.pop_bits_from_acc,
        decode.load_acc, BitVec.setWidth'_eq, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_sub_one_eq_mod,
        BitVec.toNat_umod, BitVec.toNat_setWidth, BitVec.toNat_pow, BitVec.toNat_ofNat, h1, gt_iff_lt,
        inf_lt_left, not_le, h2, BitVec.toNat_or, BitVec.toNat_shiftLeft]
      split
      . simp only
        rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne]
        . exact h4 k (by omega)
        . omega
        . omega
        . omega
      . split
        . simp only
          rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne]
          . exact h4 k (by omega)
          . omega
          . omega
          . omega
        . simp only
          rw [Vector.getElem!_set!_ne, Vector.getElem!_set!_ne, Vector.getElem!_set!_ne]
          . exact h4 k (by omega)
          . omega
          . omega
          . omega
termination_by 256 - i

def Stream.decode_decompressOpt_eq (d n : ℕ) (B : Vector Byte (32 * d)) (hd : d < 13) (hdn : d < 8 * n)
  (hB : ∀ i < 256, ∑ a : Fin d, (B[(d * i + ↑a) / 8]!.testBit ((d * i + ↑a) % 8)).toNat * 2 ^ a.val < m d) :
  decode_decompressOpt d n B.toList B.toList_length =
    (Spec.byteDecode B).map (fun (x : ZMod (m d)) => (decompressOpt d x.val).val) := by
  have : (Spec.byteDecode B).map (fun (x : ZMod (m d)) => (decompressOpt d x.val).val) =
    ((Spec.byteDecode B).map (fun (x : ZMod (m d)) => x.val)).map (fun x => (decompressOpt d x).val) := by
    simp only [Vector.map_map, Vector.map_inj_left, Function.comp_apply, implies_true]
  rw [this, ← Stream.decode.spec B hd hdn hB]
  simp only [decode_decompressOpt, decode_decompressOpt.recBody, BitVec.ofNat_eq_ofNat, tsub_zero,
    decode, decode.recBody]
  simp only [Vector.map, Vector.eq_mk, ← Array.toList_inj, Array.toList_map]
  rw [List.eq_iff_forall_eq_getElem!]
  constructor
  . simp
  . intro i hi
    simp only [Array.length_toList, Vector.size_toArray] at hi
    rw [← decode_decompressOpt.recBody, ← decode.recBody]
    simp only [Array.getElem!_toList, Vector.getElem!_toArray]
    let s0 : Stream.DecodeState d n :=
      { F := Vector.replicate 256 0, num_bytes_read := 0, acc := 0#(8 * n), num_bits_in_acc := 0 }
    rw [decode_decompress_eq_aux d n B s0 s0 hd hdn hB 0 i (by omega) hi rfl rfl rfl (by simp)]
    rw [List.getElem!_map_eq]
    . simp only [Array.getElem!_toList, Vector.getElem!_toArray]
      rfl
    . simp [hi]
