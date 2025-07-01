import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Defs
import Aeneas
import Symcrust.Spec.NatBit
import Symcrust.Spec.Round

/-!
The spec of ML-KEM, based on: https://csrc.nist.gov/pubs/fips/203/final
-/

namespace Symcrust.Spec

open Aeneas.Notations.SRRange  -- allows the `[0:256:2*len]` notations to desugar to an `SRRange` instead of a `Std.Range`
open Aeneas.Notations.DivRange -- activates the `[start : >stop : /divisor]` notation
open Aeneas.Notations.MulRange -- activates the `[start : <stop : *mul]` notation

namespace Notations

  -- Overloading the `get_elem_tactic` so that notation `l[i]` works
  scoped macro_rules
  | `(tactic| get_elem_tactic) => `(tactic| scalar_tac)

  @[scalar_tac]
  theorem div_range_in_bounds {len start : ℕ} (h0 : 1 < len ∧ len ≤ 128 ∧ ∃ k, len = 128 / 2 ^ k)
    (h1 : start < 256 ∧ start % (2 * len) = 0) : start + 2 * len ≤ 256 :=
    sorry

  @[scalar_tac]
  theorem mul_range_add_in_bounds {len start : ℕ}
    (h0 : 2 ≤ len ∧ len < 256 ∧ ∃ k, len = 2 * 2 ^ k)
    (h1 : start < 256 ∧ start % (2 * len) = 0) : start + 2 * len ≤ 256 :=
    sorry

end Notations

open Notations

@[reducible] def Q : Nat := 3329
@[reducible] def Zq := ZMod Q
@[reducible] def Polynomial (n : ℕ := Q) := Vector (ZMod n) 256

abbrev Polynomial.length {m : ℕ} (p : Polynomial m) : ℕ := p.size

def Polynomial.zero (n := Q) : Polynomial n := Vector.replicate 256 0

instance {m} : HAdd (Polynomial m) (Polynomial m) (Polynomial m) where
  hAdd f g := Vector.map (fun i => f[i]! + g[i]!) (Vector.range 256)

def Polynomial.scalarMul (x : Polynomial n) (k : ZMod n) : Polynomial n := x.map fun v => v * k

instance : HMul (Polynomial n) (ZMod n) (Polynomial n) where
  hMul := Polynomial.scalarMul

/-- # Algorithm 3 -/
def bitsToBytes {l : Nat} (b : Vector Bool (8 * l)) : Vector Byte l := Id.run do
  let mut B := Vector.replicate l 0
  for h: i in [0:8*l] do
    B := B.set (i/8) (B[i/8] + BitVec.ofNat 8 (Bool.toNat b[i]) * BitVec.ofNat 8 (2 ^(i%8)))
  pure B

/--
info: [10#8, 1#8]
-/
#guard_msgs in
#eval (@bitsToBytes 2 ⟨ ⟨ [false, true, false, true, false, false, false, false,
                            true, false, false, false, false, false, false, false] ⟩,
                           by simp ⟩).toList

/-- # Algorithm 4 -/
def bytesToBits {l : Nat} (B : Vector Byte l) : Vector Bool (8 * l) := Id.run do
  let mut C := B
  let mut b := Vector.replicate (8 * l) false
  for hi: i in [0:l] do
    for hj: j in [0:8] do
      b := b.set (8*i + j) (C[i] % 2 ≠ 0)
      C := C.set i (C[i] / 2)
  pure b

#assert
  let b : Vector Bool (8 * 2) :=
    ⟨ ⟨ [false, true, false, true, false, false, false, false,
         true, false, false, false, false, false, false, false] ⟩, by simp ⟩
  bytesToBits (bitsToBytes b) = b

/-- # Compress -/
def compress (d : {d: ℕ // d < 12}) (x : Zq) : ZMod (2^d.val) := ⌈ ((2^d.val : ℚ) / (Q : ℚ)) * x.val⌋

/-- # Decompress -/
def decompress (d : {d: ℕ // d < 12}) (y : ZMod (2^d.val)) : Zq := ⌈ ((Q : ℚ) / (2^d.val : ℚ)) * y.val⌋

/-- # Algorithm 5 -/
abbrev m (d : ℕ) : ℕ := if d < 12 then 2^d else Q
def byteEncode (d : ℕ) (F : Polynomial (m d)) : Vector Byte (32 * d) := Id.run do
  let mut b := Vector.replicate (256 * d) false
  for hi: i in [0:256] do
    have : i * d ≤ 255 * d := by scalar_tac +nonLin
    let mut a : ℕ ← F[i].val
    for hj: j in [0:d] do
      b := b.set (i * d + j) (Bool.ofNat (a % 2))
      a := (a - Bool.toNat b[i * d + j]) / 2
  let B := bitsToBytes (Vector.cast (by ring_nf) b)
  pure B

/-- # Algorithm 6 -/
def byteDecode {m} (B : Vector Byte (32 * d)) : Polynomial m := Id.run do
  let b ← bytesToBits B
  let mut F := Polynomial.zero m
  for hi: i in [0:256] do
    have : i * d ≤ 255 * d := by scalar_tac +nonLin
    F := F.set i (∑ (j : Fin d), (Bool.toNat b[i * d + j]) * 2^j.val)
  pure F

/-
# eXtendable-Output Function (XOF)
-/
namespace SHAKE128 -- TODO: remove the axioms
  axiom Context : Type
  axiom init : Context
  axiom absorb : Context → List Byte → Context
  axiom squeeze : Context → (x:ℕ) → Context × Vector Byte (x / 8)
end SHAKE128

axiom SHA3_512 : List Byte → Vector Byte 32 × Vector Byte 32
noncomputable def G := SHA3_512

noncomputable def XOF.init := SHAKE128.init
noncomputable def XOF.absorb := SHAKE128.absorb
noncomputable def XOF.squeeze (ctx : SHAKE128.Context) (z : Nat) : SHAKE128.Context × Vector Byte z:=
  let (ctx, out) := SHAKE128.squeeze ctx (8 * z)
  (ctx, Vector.cast (by simp) out)

/-- # Algorithm 7 -/
noncomputable -- TODO: remove the noncomputable
def sampleNTT (B : {l : List Byte // l.length = 34 }) : Polynomial := Id.run do
  let mut ctx := XOF.init
  ctx := XOF.absorb ctx B
  let mut a := Polynomial.zero
  let mut j : Nat := 0
  while hj: j < 256 do
    let (ctx', C) := XOF.squeeze ctx 3
    ctx := ctx'
    let d1 : Nat := C[0].val + 256 * (C[1].val % 16)
    let d2 := C[1].val/16 + 16 * C[2].val
    if d1 < Q then
      a := a.set j d1
      j := j + 1
    if h: d2 < Q ∧ j < 256 then
      a := a.set j d2
      j := j + 1
  pure a

/-- # Algorithm 8 -/
abbrev Η := {η : ℕ // η ∈ ({2, 3}: Set ℕ)}

@[scalar_tac η.val]
theorem H.val (η : Η) : η.val ≤ 3 := by
  have := η.property
  scalar_tac

noncomputable -- TODO: remove the noncomputable
def samplePolyCBD {η:Η} (B : Vector Byte (64 * η)): Polynomial := Id.run do
  let b := bytesToBits B
  let mut f := Polynomial.zero
  for hi: i in [0:256] do
    have : 2 * i * η ≤ 510 * η := by scalar_tac +nonLin
    let x := ∑ (j : Fin η), Bool.toNat b[2 * i * η + j]
    let y := ∑ (j : Fin η), Bool.toNat b[2 * i * η + η + j]
    f := f.set! i (x - y)
  pure f

def ζ : ZMod Q := 17

/-- # Algorithm 9 -/
def ntt (f : Polynomial) : Polynomial := Id.run do
  let mut f := f
  let mut i := 1
  for h0: len in [128 : >1 : /= 2] do
    for h1: start in [0:256:2*len] do
      let zeta := ζ ^ (bitRev 7 i)
      i := i + 1
      for h: j in [start:start+len] do
        let t := zeta * f[j + len]
        f := f.set (j + len) (f[j] - t)
        f := f.set j (f[j] + t)
  pure f

/-- # Algorithm 10 -/
def invNtt (f : Polynomial) : Polynomial := Id.run do
  let mut f := f
  let mut i := 127
  for h0: len in [2 : <256 : *= 2] do
    for h1: start in [0:256:2*len] do
      let zeta := ζ ^(bitRev 7 i)
      i := i - 1
      for h: j in [start:start+len] do
        let t := f[j]
        f := f.set j (t + f[j + len])
        f := f.set (j + len) (zeta * (f[j + len] - t))
  f := f * (3303 : Zq)
  pure f

/-- # Algorithm 12 -/
def baseCaseMultiply (a0 a1 b0 b1 γ : Zq) : Zq × Zq :=
  let c0 := a0 * b0 + a1 * b1 * γ
  let c1 := a0 * b1 + a1 * b0
  (c0, c1)

/-- # Algorithm 11 -/
def multiplyNTTs (f g : Polynomial) : Polynomial := Id.run do
  let mut h : Polynomial := Polynomial.zero
  for h: i in [0:128] do
    let (c0, c1) := baseCaseMultiply f[2 * i] f[2 * i + 1] g[2 * i] g[2 * i + 1] (ζ^(2 * bitRev 7 i + 1))
    h := h.set (2 * i) c0
    h := h.set (2 * i + 1) c1
  pure h

/-- # Algorithm 13 -/ -- TODO: k ∈ {2,3,4}
def kpke.keyGen {k : ℕ} (d : Vector Byte 32) : Vector Byte (384 * k + 32) × Vector Byte (384 * k) := Id.run do
  --let kv : Vector Byte 1 := ⟨ ⟨ [Byte.ofNat k] ⟩, by simp ⟩
  let (ρ, σ) := G (d.toList ++ [Byte.ofNat k])
  let mut N := 0
  for i in [0:k] do
    for j in [0:k] do
      sorry -- TODO: we need matrices
  sorry

end Symcrust.Spec
