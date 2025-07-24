import Symcrust.Spec
import Symcrust.Properties.Polynomials
import Symcrust.Properties.BitsAndBytes.BitsToBytes
import Symcrust.Properties.BitsAndBytes.BytesToBits
import Symcrust.Properties.CompressEncode.TargetEncode
import Symcrust.Brute

/-!
This file contains theorems about `Symcrust.Spec.byteEncode` defined in Symcrust.Spec.Spec.lean.

`Nist spec ⟷₁ Lean spec (monadic) ⟷₂ Lean spec (functional) ⟷₃ Auxiliary spec ⟷₄ Aeneas translation`
  - In the above verification pipeline:
    - `Nist spec` corresponds to Algorithm 5 (ByteEncode).
    - `Lean spec (monadic)` corresponds to `Symcrust.Spec.byteEncode`.
    - `Lean spec (functional)` corresponds to `Target.byteEncode`.
    - `Auxiliary spec` corresponds to `Stream.encode`.
    - `⟷₃` is bundled together with `⟷₂` in the form of `Stream.encode.spec`.
    - Analogues for later portions of the verification pipeline appear in other files.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

/-- `d`: the number of bits with which to encode an element
    `n`: the number of bytes in the accumulator
-/
structure Stream.EncodeState (n : ℕ) where
  b : List Byte
  bi : ℕ -- number of bytes written to `b`
  acc : BitVec (8 * n)
  acci : ℕ -- number of bits written to `acc`

def Stream.encode.body (d : ℕ) {n : ℕ} (x : ZMod (m d)) (s : EncodeState n) :
  EncodeState n :=
  let nBits := min d (8 * n - s.acci)
  let bits := BitVec.ofNat (8 * n) x.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  let xBits := d - nBits

  let acc := s.acc ||| (bits <<< s.acci)
  let acci := s.acci + nBits

  -- Flush
  if acci = 8 * n then
    let b := s.b.setSlice! s.bi acc.toLEBytes
    let bi := s.bi + n

    -- Encode the remaining bits
    let x := x.val >>> nBits
    let acc := BitVec.ofNat (8 * n) x
    let acci := xBits
    {b, bi, acc, acci}
  else
    {s with acc, acci}

def Stream.encode.recBody (d : ℕ) {n : ℕ} (F : Vector (ZMod (m d)) 256) (s : EncodeState n) (i : ℕ) :
  EncodeState n :=
  List.foldl (fun s i => encode.body d F[i]! s) s (List.range' i (256 - i))

def Stream.encode (d n : ℕ) (F : Vector (ZMod (m d)) 256) : List Byte :=
  let s : EncodeState n := {
    b := List.replicate (32 * d) 0,
    bi := 0,
    acc := 0,
    acci := 0,
  }
  (encode.recBody d F s 0).b

/-- Invariant about the lengths -/
def Stream.encode.length_inv (d n : ℕ) (b : List Byte) (bi acci i : ℕ) : Prop :=
  b.length = 32 * d ∧
  i ≤ 256 ∧
  -- This is the subtil part
  bi = n * ((d * i) / (8 * n)) ∧
  acci = (d * i) % (8 * n)

/-- The full invariant.

The best way of understanding the invariant and the proof, in particular the equations between the indices
(`i`, `s.bi`, `s.acci`, etc.) is to make a drawing. We typically have something like this:

                                        accumulator `s.acc` (`8 * n` bits)
                                       ______________________________________
                                      |                                      |
                                                                  `8 * s.bi + 8 * n`
  `8 * s.bi` bits encoded in `s.b`    `s.acci` bits in `s.acc`               |
|------------------------------------|------------------------|--------------|---------|
                                     |                        |   `nBits`      `xBits` |
                                     |                        |                        |
                                     |                     `d * i`                 `d * (i + 1)`
                                     |            (`i` elements encoded to `d * i`
                                     |             bits in `s.b` and `s.acc`)
                                     |                        |
                                     |                        |
                     `s.bi = ((d * i) / (8 * n)) * n`         |
                                     |________________________|
                                    `s.acci = (d * i) % (8 * n)`
-/
def Stream.encode.inv
  (d : ℕ) {n : ℕ} (F : Vector (ZMod (m d)) 256) (s : EncodeState n) (i : ℕ) : Prop :=
  -- The lengths are correct
  length_inv d n s.b s.bi s.acci i ∧
  -- The bits are properly set in the destination buffer
  (∀ i < s.bi, ∀ j < 8, s.b[i]!.testBit j = F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d)) ∧
  -- The bits are properly set in the accumulator
  (∀ j < s.acci, s.acc[j]! = F[(8 * s.bi + j) / d]!.val.testBit ((8 * s.bi + j) % d)) ∧
  (∀ j ∈ [s.acci:8*n], s.acc[j]! = false)

/--
Auxiliary lemma: `Stream.encode.body` preserves the length invariant.
-/
theorem Stream.encode.body.length_spec
  {i d n : ℕ} (x0 : ZMod (m d)) {s : EncodeState n} [NeZero (m d)]
  (hinv : length_inv d n s.b s.bi s.acci i)
  (hi : i < 256 := by omega)
  (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega) :
  let s1 := body d x0 s
  length_inv d n s1.b s1.bi s1.acci (i + 1) := by
  simp only [length_inv, body]
  tlet nBits := min d (8 * n - s.acci)

  tlet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  tlet xBits := d - nBits

  tlet acc := s.acc ||| (bits <<< s.acci)
  tlet acci := s.acci + nBits

  tlet b := s.b.setSlice! s.bi acc.toLEBytes
  tlet bi := s.bi + n

  obtain ⟨ h0, h1, h2, h3 ⟩ := hinv

  split
  . rename_i hif0

    -- Number of bytes in the output buffer
    have hBi : s.bi + n = n * (d * (i + 1) / (8 * n)) ∧
                xBits = (d * (i + 1)) % (8 * n) := by
      have hd0 := calc
        8 * s.bi + 8 * n + xBits = 8 * s.bi + s.acci + (nBits + xBits) := by simp only [← hif0, acci]; ring_nf
        _ = 8 * s.bi + s.acci + d := by
          have : nBits + xBits = d := by omega
          simp only [this, Nat.add_left_inj]
        _ = d * i + d := by
          -- Using the characterization of euclidean division
          have : 8 * s.bi + s.acci = d * i := by
            have hMod := Nat.mod_add_div (d * i) (8 * n)
            rw [← hMod]
            simp only [h2, h3]
            ring_nf
          omega
        _ = d * (i + 1) := by ring_nf

      have hd1 := calc
        (8 * s.bi + 8 * n + xBits) % (8 * n) = ((8 * s.bi + 8 * n) + xBits) % (8 * n) := by ring_nf
        _ = xBits % (8 * n) := by
          have : (8 * s.bi + 8 * n) % (8 * n) = 0 := by -- TODO: make simp_scalar work here
            simp only [h2, ← mul_assoc, Nat.add_mod_right, Nat.mul_mod_right]
          rw [Nat.add_mod]
          simp only [this, zero_add, dvd_refl, Nat.mod_mod_of_dvd]
        _ = xBits := by scalar_tac +nonLin

      have hd2 := calc
        (d * (i + 1)) / (8 * n) = (d * (i + 1) - (d * (i + 1)) % (8 * n)) / (8 * n)
            := by simp_scalar
        _ =  (8 * s.bi + 8 * n + xBits - xBits) / (8 * n) := by simp only [← hd0, hd1]
        _ = (8 * s.bi + 8 * n) / (8 * n) := by simp_scalar
        _ = s.bi / n + 1 := by
          simp_scalar

      have : s.bi + n = n * (d * (i + 1) / (8 * n)) := by
        simp_scalar [hd2, h2]
        ring_nf

      have : xBits = (d * (i + 1)) % (8 * n) := by
        simp only [← hd0, hd1]

      tauto

    have : b.length = 32 * d := by scalar_tac

    simp only
    split_conjs <;> tauto
  . have hLt : s.acci < 8 * n := by
      simp only [h3]
      simp_scalar
    have hLt' : s.acci + nBits < 8 * n := by omega
    have nBitsEq : nBits = d := by omega

    -- Number of bits in the accumulator
    have hAcci : acci = d * (i + 1) % (8 * n) := by
      simp only [acci]
      zmodify
      simp only [h3, ZMod.natCast_mod, Nat.cast_mul, nBitsEq, acci]
      ring_nf

    -- Number of bytes in the output buffer
    have hBi : s.bi = n * (d * (i + 1) / (8 * n)) := by
      -- Using the characterization of euclidean division
      have hMod := Nat.mod_add_div (d * i) (8 * n)
      have hMod' := Nat.mod_add_div (d * (i + 1)) (8 * n)
      --
      simp only [mul_assoc, ← h2, ← h3, ← hAcci] at hMod hMod'
      have : d * (i + 1) = d * i + d := by ring_nf
      conv at hMod' => rhs; rw [this]
      simp only [nBitsEq, acci] at hMod'
      have : 8 * s.bi = 8 * (n * (d * (i + 1) / (8 * n))) := by omega
      omega

    simp only
    tauto

-- This lemma is needed for `scalar_tac` to succeed in one of `Stream.encode.body.spec_before_flush`'s subgoals
attribute [local scalar_tac m d] Symcrust.SpecAux.m_d_pos

/--
Auxiliary lemma. See `Stream.encode.body`.

This lemma proves important properties about the encoded bits in the accumulator
before we flush it (if we need to flush it).
-/
theorem Stream.encode.body.spec_before_flush
  {d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n}
  (hinv : inv d F s i) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega) :
  let x0 := F[i]!
  let nBits := d ⊓ (8 * n - s.acci)
  let bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))

  let acc := s.acc ||| (bits <<< s.acci)
  let acci := s.acci + nBits
  -- The masking is equivalent to a modulo
  bits.toNat = x0.val % 2^nBits ∧
  -- Accumulator: prefix (the bits are properly set)
  (∀ j < acci, acc[j]! = F[(8 * s.bi + j) / d]!.val.testBit ((8 * s.bi + j) % d)) ∧
  -- Accumulator: suffix (the bits are still equal to 0)
  (∀ j ∈ [acci:8*n], acc[j]! = false)

  := by

  simp only [inv, mem_std_range_step_one, and_imp] at hinv
  simp only
  obtain ⟨ ⟨ _, h0, h1, h2 ⟩, h3, h4, h5 ⟩ := hinv

  tlet x0 := F[i]!
  tlet nBits := d ⊓ (8 * n - s.acci)
  tlet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  tlet x := x0.val >>> nBits

  tlet acc := s.acc ||| (bits <<< s.acci)
  tlet acci := s.acci + nBits

  have hBitsEq : bits.toNat = x0.val % 2^nBits := by
    simp only [bits]
    simp only [BitVec.shiftLeft_sub_one_eq_mod]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_pow, bits]

    have : 2 < 2 ^(8*n) := by simp_scalar
    have : 2 ^ nBits < 2 ^ (8 * n) := by simp_scalar
    have : x0.val < 2 ^ (8 * n) := by scalar_tac
    simp_scalar

  -- Accumulator: prefix
  have hAccPre : ∀ j < acci, acc[j]! = F[(8 * s.bi + j) / d]!.val.testBit ((8 * s.bi + j) % d) := by
    intros j hj
    simp only [acci] at hj
    simp only [BitVec.getElem!_or, acc, acci]
    by_cases hj': j < s.acci -- TODO: simp_lists +split
    . simp_lists [h4]
    . simp_lists [h5]

      simp only [BitVec.getElem!_eq_testBit_toNat, hBitsEq, Nat.testBit_mod_two_pow, acci, acc]
      simp_scalar
      simp only [x0, acc, acci]

      have hij : (8 * s.bi + j) / d = i ∧
                 (8 * s.bi + j) % d = j - s.acci := by
        have := Nat.mod_add_div (d * i) (8 * n)
        have : 8 * s.bi = 8 * n * (d * i / (8 * n)) := by
          simp only [h1, x0, acc, acci]
          ring_nf

        have : 8 * s.bi + j = d * i + (j - s.acci) := by omega

        split_conjs
        . have hi : (8 * s.bi + j) / d = (d * i + (j - s.acci)) / d := by simp only [this]
          simp_scalar at hi
          apply hi
        . have hi : (8 * s.bi + j) % d = (d * i + (j - s.acci)) % d := by simp only [this]
          simp_scalar at hi
          apply hi
      simp only [hij]

  -- Accumulator: suffix
  have hAccPost : ∀ j ∈ [acci:8*n], acc[j]! = false := by
    simp only [mem_std_range_step_one, and_imp]
    intros j hj hj'
    simp only [BitVec.getElem!_or, Bool.or_eq_false_iff, acc]
    simp_lists [*]
    simp only [← h2, acc]
    simp only [BitVec.shiftLeft_sub_one_eq_mod, BitVec.ofNat_eq_ofNat, bits, acc]
    simp_lists

  tauto

/--
Auxiliary lemma.

This lemma handles the case of `Stream.encode.body` when there is no flush.
-/
theorem Stream.encode.body.spec_no_flush
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n} [NeZero (m d)]
  (hinv : inv d F s i) (hi : i < 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n)
  (hm : m d < 2^(8*n) := by omega)
  (hacci : ¬ s.acci + d ⊓ (8 * n - s.acci) = 8 * n)
  :
  inv d F (body d F[i]! s) (i + 1) := by
  -- Important intermediate results about the accumulator and `bits`
  have ⟨ hBitsEq, hAccPre, hAccPost ⟩ := Stream.encode.body.spec_before_flush hinv
  have hlinv := length_spec F[i]! hinv.left
  revert hlinv

  -- Unfold the body and the invariant
  simp only [inv, mem_std_range_step_one, and_imp] at hinv
  obtain ⟨ ⟨ _, h0, h1, h2 ⟩, h3, h4, h5 ⟩ := hinv
  simp only [body]
  simp_ifs
  simp only [inv]
  intro hlinv

  split_conjs <;> try tauto

/--
Auxiliary lemma.

This lemma introduces important properties about the output buffer (`s.b`)
after we flushed the accumulator.
-/
theorem Stream.encode.body.spec_with_flush_bi
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n}
  (hinv : inv d F s i)
  (hi : i < 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega)
  (h0 : s.acci + d ⊓ (8 * n - s.acci) = 8 * n := by omega) :
  let x0 := F[i]!
  let nBits := d ⊓ (8 * n - s.acci)
  let bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  let xBits := d - nBits
  let acc := s.acc ||| (bits <<< s.acci)
  -- Number of bytes in the output buffer
  (s.bi + n = n * (d * (i + 1) / (8 * n)) ∧ xBits = (d * (i + 1)) % (8 * n)) ∧
  -- Bits in the output buffer
  (∀ i < s.bi + n, ∀ j < 8,
      (s.b.setSlice! s.bi acc.toLEBytes)[i]!.testBit j =
        F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d))
  := by

  -- Important intermediate results about the accumulator and `bits`
  have ⟨ hBitsEq, hAccPre, hAccPost ⟩ := Stream.encode.body.spec_before_flush hinv
  have hlinv1 := length_spec F[i]! hinv.left
  simp only [body] at hlinv1
  simp_ifs at hlinv1

  -- Introducing abbreviations
  tlet x0 := F[i]!
  tlet nBits := d ⊓ (8 * n - s.acci)
  tlet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  tlet x := x0.val >>> nBits
  tlet xBits := d - nBits

  tlet acc := s.acc ||| (bits <<< s.acci)
  tlet acci := s.acci + nBits

  obtain ⟨ ⟨ _, _, h1, h2 ⟩, h3, h4, h5 ⟩ := hinv
  obtain ⟨ _, _, hBi ⟩ := hlinv1

  -- Bits in the output buffer
  have :
    ∀ i < s.bi + n, ∀ j < 8,
      (s.b.setSlice! s.bi acc.toLEBytes)[i]!.testBit j =
        F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d) := by
    -- We have to do a case disjunction:
    intros i' hi' j hj
    have : acc.toLEBytes.length = n := by simp only [Nat.mul_mod_right, BitVec.toLEBytes_length,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
    have : s.bi + n ≤ s.b.length := by
      have :=
        calc s.bi + n = n * (d * (i + 1) / (8 * n)) := by omega
              _ = n * (d * (i + 1) / 8 / n) := by simp_scalar
              _ ≤ d * (i + 1) / 8 := by simp_scalar
              _ ≤ d * 256 / 8 := by
                -- TODO: improve
                have : d * (i + 1) ≤ d * 256 := by simp_scalar
                simp_scalar
              _ = 32 * d := by omega
      scalar_tac

    by_cases hi'': i' < s.bi -- TODO: simp_lists +split
    . simp_lists [h3]
    . simp_lists [hAccPre]
      have : 8 * s.bi + (8 * (i' - s.bi) + j) = 8 * i' + j := by omega
      simp only [this]

  tauto


/--
Auxiliary lemma.

This lemma handles the case of `Stream.encode.body` when there is a flush.
-/
theorem Stream.encode.body.spec_with_flush
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n} [NeZero (m d)]
  (hinv : inv d F s i) (hi : i < 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n)
  (hm : m d < 2^(8*n) := by omega)
  (h0 : s.acci + d ⊓ (8 * n - s.acci) = 8 * n)
  :
  inv d F (body d F[i]! s) (i + 1) := by
  -- Important intermediate results about the accumulator and `bits`
  have ⟨ hBitsEq, hAccPre, hAccPost ⟩ := Stream.encode.body.spec_before_flush hinv
  -- Intermediate results about the output buffer
  have ⟨ hBi, hsb ⟩ := Stream.encode.body.spec_with_flush_bi hinv

  -- Unfold the body and the invariant
  unfold body
  simp only [inv, length_inv, mem_std_range_step_one, and_imp, and_assoc] at hinv
  obtain ⟨ _, h0, h1, h2, h3, h4, h5 ⟩ := hinv
  simp only

  -- Introducing abbreviations
  tlet x0 := F[i]!
  tlet nBits := d ⊓ (8 * n - s.acci)
  tlet bits := BitVec.ofNat (8 * n) x0.val &&& (1#(8*n) <<< nBits - 1#(8*n))
  tlet x := x0.val >>> nBits
  tlet xBits := d - nBits

  tlet acc := s.acc ||| (bits <<< s.acci)
  tlet acci := s.acci + nBits

  simp_ifs
  simp only [inv, length_inv, and_assoc]

  tlet bits := BitVec.ofNat (8 * n) x &&& (1#(8*n) <<< nBits - 1#(8*n))

  split_conjs <;> try tauto
  . scalar_tac
  . intros j hj
    simp only [x, x0]

    have hij : (8 * (s.bi + n) + j) / d = i ∧
                (8 * (s.bi + n) + j) % d = nBits + j
                := by
      have hij := calc
        8 * (s.bi + n) + j = 8 * s.bi + 8 * n + j := by omega
        _ = 8 * s.bi + s.acci + nBits + j := by omega
        _ = d * i + nBits + j := by
          -- Property of euclidean division
          have hMod := Nat.mod_add_div (d * i) (8 * n)
          simp only [← h2, mul_assoc, ← h1] at hMod
          omega

      have : nBits + j < d := by omega
      have hi := calc
        (8 * (s.bi + n) + j) / d = (d * i + (nBits +j)) / d := by simp only [hij]; ring_nf
        _ = i := by simp_scalar

      have hj := calc
        (8 * (s.bi + n) + j) % d = (d * i + (nBits +j)) % d := by simp only [hij]; ring_nf
        _ = nBits + j := by simp_scalar

      simp only [hi, hj, Nat.add_left_inj, and_self]
    simp only [hij]
    simp only [BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, Bool.and_eq_right_iff_imp, decide_eq_true_eq]
    omega

  . simp only [mem_std_range_step_one, and_imp, x]
    intros j hj hj'
    simp only [BitVec.getElem!_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, Bool.and_eq_false_imp, decide_eq_true_eq, x0, x]
    intros

    apply Nat.testBit_eq_false_of_lt
    have : m d ≤ 2 ^(nBits + j) := by
      unfold m Q
      split
      . scalar_tac +nonLin
      . have : 2^12 ≤ 2^(nBits + j) := by scalar_tac +nonLin
        omega

    scalar_tac +nonLin

/--
The important lemma about `Stream.encode.body`: calling this function once preserves the invariant
(but we encoded one more element, so the index goes from `i` to `i + 1`).
-/
theorem Stream.encode.body.spec
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n} [NeZero (m d)]
  (hinv : inv d F s i) (hi : i < 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega) :
  inv d F (body d F[i]! s) (i + 1) := by
  by_cases h0 : s.acci + d ⊓ (8 * n - s.acci) = 8 * n
  . apply spec_with_flush hinv <;> omega
  . apply Stream.encode.body.spec_no_flush hinv <;> omega

theorem Stream.encode.recBody.spec
  {i d n : ℕ} {F : Vector (ZMod (m d)) 256} {s : EncodeState n} [NeZero (m d)]
  (hinv : inv d F s i) (hi : i ≤ 256 := by omega) (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega) :
  inv d F (recBody d F s i) 256 := by
  if hi: i = 256 then
    simp only [hi]
    unfold recBody
    simp only [tsub_self, List.range'_zero, List.foldl_nil]
    simp_all
  else
    unfold recBody
    have : 256 - i = (256 - (i+1)) + 1 := by omega
    rw [this, List.range'_succ]
    simp only [Nat.reduceSubDiff, List.foldl_cons]
    have hinv1 := body.spec hinv
    have hinv2 := spec hinv1
    unfold recBody at hinv2
    simp only [Nat.reduceSubDiff] at hinv2
    apply hinv2
termination_by 256 - i
decreasing_by omega

def Stream.encode.post (d : ℕ) (F : Vector (ZMod (m d)) 256) (b : List Byte ) : Prop :=
  b.length = 32 * d ∧
  (∀ i < 32 * d, ∀ j < 8, b[i]!.testBit j = F[(8 * i + j) / d]!.val.testBit ((8 * i + j) % d))

/-- Auxiliary spec for `Stream.encode`: we use the post-condition to prove that it is actually equal to `Spec.encode` -/
theorem Stream.encode.spec_aux
  (d n : ℕ) (F : Vector (ZMod (m d)) 256) [NeZero (m d)]
  (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega)
  (hn1 : n ∣ 32 := by omega) :
  post d F (encode d n F) := by
  unfold encode
  simp only
  tlet s : EncodeState n := {
    b := List.replicate (32 * d) 0,
    bi := 0,
    acc := 0,
    acci := 0,
  }

  have hinv : inv d F s 0 := by
    unfold inv length_inv
    simp only [BitVec.ofNat_eq_ofNat, List.length_replicate, zero_le, mul_zero, Nat.zero_div,
      Nat.zero_mod, not_lt_zero', IsEmpty.forall_iff, implies_true, BitVec.getElem!_zero, zero_add,
      Bool.false_eq, mem_std_range_step_one, true_and, and_self, and_assoc, s]

  replace hinv := Stream.encode.recBody.spec hinv

  tlet s1 := recBody d F s 0

  unfold inv length_inv at hinv
  simp only [le_refl, mem_std_range_step_one, and_imp, and_assoc, true_and] at hinv
  obtain ⟨ _, h0, h1, h2, h3, h4 ⟩ := hinv

  unfold post
  split_conjs
  . scalar_tac
  . intros i hi j hj

    have : s1.bi = 32 * d := by
      simp only [h0]
      have : d * 256 = 8 * (32 * d) := by ring_nf
      rw [this]
      simp_scalar
      -- TODO: we should be able to automate this
      have hn2 : n ∣ 32 * d := by apply Nat.dvd_mul_right_of_dvd hn1
      simp only [hn2, Nat.mul_div_cancel']

    simp_lists [h2]

/-- `Stream.encode` is equal to `Spec.encode` -/
theorem Stream.encode.spec
  (d n : ℕ) (F : Polynomial (m d))
  (hd : 0 < d := by omega)
  (hn : 0 < n := by omega)
  (hdn : d < 8 * n := by omega)
  (hm : m d < 2^(8*n) := by omega)
  (hn1 : n ∣ 32 := by omega) :
  encode d n F = (Spec.byteEncode d F).toList := by
  -- Characterization of Stream.encode
  have h1 := encode.spec_aux d n F
  unfold post at h1
  obtain ⟨ h1, h1' ⟩ := h1
  -- Characterization of Spec.byteEncode
  rw [← Target.byteEncode.eq_spec]
  have h2 := Target.byteEncode.spec d F
  -- Using the extensional equality
  rw [List.eq_iff_forall_eq_getElem!]
  simp
  split_conjs
  . scalar_tac
  . intros i hi
    rw [Byte.eq_iff]
    simp_lists [*]

end Symcrust.SpecAux
