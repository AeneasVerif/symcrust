import Aeneas
import Aeneas.List
import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Bits

import Symcrust.SRRange

/-!
The spec of ML-KEM, based on: https://csrc.nist.gov/pubs/fips/203/final
-/

-- TODO: move
namespace List

def enumerateAux (n : Nat) (i : Nat) : List Nat :=
  if h: i ≥ n then []
  else i :: enumerateAux n (i + 1)
termination_by n - i
decreasing_by omega

def enumerate (n : Nat) : List Nat := enumerateAux n 0

end List

namespace Symcrust.Spec

-- TODO: List.index, update are not useful anymore

@[reducible] def Byte := UInt8

/-- Algorithm 3 -/
def bitsToBytes (b : List Bool) : List Byte := Id.run do
  let l := b.length / 8
  let mut B := List.replicate l 0
  for i in [:8*l] do
    B := B.set (i/8) (B.get! (i/8) + ((b.get! i).toUInt8 * ((2 ^(i%8) : Nat).toUInt8)))
  pure B

#eval bitsToBytes [false, true, false, true, false, false, false, false,
                   true, false, false, false, false, false, false, false]

/-- Algorithm 4 -/
def bytesToBits (B : List Byte) : List Bool := Id.run do
  let l := B.length
  let mut C := B
  let mut b : List Bool := List.replicate (8 * l) false
  for i in [:l] do
    for j in [:8*l] do
      b := b.set (8*i + j) ((C.get! i) % 2 ≠ 0)
      C := C.set i (C.get! i / 2)
  pure b

#assert let b := [false, true, false, true, false, false, false, false,
                true, false, false, false, false, false, false, false]
      bytesToBits (bitsToBytes b) = b

-- TODO: algorithm 5: ByteEncode

-- TODO: algorithm 6: ByteDecode

@[reducible] def Q : Nat := 3329

namespace SHAKE128
  axiom Context : Type
  axiom init : Context
  axiom absorb : Context → List Byte → Context
  axiom squeeze : Context → (z:ℕ) → Context × {l : List Byte // l.length = z}
end SHAKE128

noncomputable def XOF.init := SHAKE128.init
noncomputable def XOF.absorb := SHAKE128.absorb
noncomputable def XOF.squeeze := SHAKE128.squeeze

@[reducible] def Zq := ZMod Q
@[reducible] def Polynomial := { l : List Zq // l.length = 256 }

def Polynomial.get! (x : Polynomial) (n : ℕ)  : Zq := x.val.get! n
def Polynomial.set (x : Polynomial) (n : ℕ) (v : Zq) : Polynomial :=
  ⟨ x.val.set n v, by cases x; simp_all ⟩

/-- This activates nice notations -/
instance : GetElem Polynomial Nat Zq (fun _ _ => True) where
  getElem p i _ := p.get! i

def Polynomial.scalarMul (x : Polynomial) (k : Zq) : Polynomial :=
  ⟨ x.val.map fun v => v * k,
    by cases x; simp_all ⟩

instance : HMul Polynomial Zq Polynomial where
  hMul := Polynomial.scalarMul

/-- Algorithm 7
TODO: input has length 34
-/
noncomputable
def sampleNTT (B : {l : List Byte // l.length = 34 }) : Polynomial := Id.run do
  let mut ctx := XOF.init
  ctx := XOF.absorb ctx B
  let mut j : Nat := 0
  while j < 256 do
    sorry
  sorry

-- TODO: algorithm 8

def bitRev (n : Nat) (i : Nat) : Nat :=
  -- Convert to bits
  let bits := i.bits
  -- Make sure we have n bits - note that the list of bits goes from bits
  -- of lower weight to bits of heigher weights
  let bits := bits.take n
  let bits := bits ++ List.replicate (n - bits.length) false
  -- Reverse
  let bits := List.reverse bits
  -- Convert
  (bits.mapIdx (fun i b => b.toNat * 2 ^ i)).sum

#assert List.map (bitRev 2) (List.enumerate 4) = [0, 2, 1, 3]
#assert List.map (bitRev 3) (List.enumerate 8) = [0, 4, 2, 6, 1, 5, 3, 7]

def ζ : ZMod Q := 17

open Aeneas.SRRange.Notations -- the [0:256:2*len] notations desugars to an `SRRange` instead of a `Std.Range`

/-- Algorithm 9 -/
def ntt (f : Polynomial) : Polynomial := Id.run do
  let mut f := f
  let mut i := 1
  for k in [0:8] do
    let len := 2 ^ (7 - k)
    for start in [0:256:2*len] do
      let zeta := ζ ^ (bitRev 7 i)
      i := i + 1
      for j in [start:start+len] do
        let t := zeta * f[j + len]!
        f := f.set (j + len) (f[j]! - t)
        f := f.set j (f[j]! + t)
  pure f

/-- Algorithm 10 -/
def invNtt (f : Polynomial) : Polynomial := Id.run do
  let mut f := f
  let i := 127 -- FIXME: `simp` takes a very long time because of this
  for k in [1:8] do
    let len := 2 ^ k
    for start in [0:256:2*len] do
      let zeta := ζ ^(bitRev 7 i)
      let i := i - 1
      for j in [start:start+len] do
        let t := f[j]!
        f := f.set j (t + f[j + len]!)
        f := f.set (j + len) (zeta * (f[j + len]! - t))
  f := f * (3303 : Zq)
  pure f

end Symcrust.Spec
