import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Vector.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.RowCol
import Aeneas
import Symcrust.Spec.NatBit
import Symcrust.Spec.Round
import Symcrust.Spec.Utils
open Lean

set_option grind.warning false

/-
  Executable specification of SHA128 aligned to FIPS-197
-/

namespace Spec.AES

abbrev 𝔹 := Vector Byte

-- arithmetic in GF(2^8)

private def byte (n : Nat) : Byte := BitVec.ofNat 8 n

@[inline] private def xtime (b : Byte) : Byte :=
  let shifted := b <<< 1
  if b.getMsbD 0 then shifted ^^^ byte 0x1b else shifted

private def mul (a b : Byte) := Id.run do
  let mut r : Byte := 0
  let mut x := a
  let mut y := b
  for i in [0:8] do
    if y.getLsbD i then
      r := r ^^^ x
    x := xtime x
  pure r

private def pow (a : Byte) (b : Nat) :=
  if b = 0 then 1
  else
    let half   := pow a (b / 2)
    let square := mul half half
    if b % 2 = 0 then
      square
    else
      mul square a
  termination_by b

private def inv (a : Byte) := pow a 254

lemma inv_test :
  let b := byte 42
  mul b (inv b) = byte 1 := by native_decide


-- AES transformations

private def subByte (b : Byte) :=
  let i := inv b
  i ^^^ i.rotateLeft 1 ^^^ i.rotateLeft 2 ^^^ i.rotateLeft 3 ^^^ i.rotateLeft 4 ^^^ byte 0x63

abbrev Word := 𝔹 4
abbrev State := Vector Word 4 --was: Matrix (Fin 4) (Fin 4) Byte
abbrev KeyWords := State --key schedules, will need a wider type for AES-192 and AES-256

def subWord (w : Word) : Word := Vector.map subByte w

def rotWord (w : Word) : Word := Vector.ofFn (fun i => w[(i + 1) % 4])

instance : XorOp Word where
  xor w₀ w₁ := Vector.ofFn (fun i => w₀[i] ^^^ w₁[i])

def rconWord (rc : Byte) : Word := #v[rc, 0, 0, 0]

def key_round (keys : KeyWords) (rc : Byte) :=
  let w0 := keys[0]
  let w1 := keys[1]
  let w2 := keys[2]
  let w3 := keys[3]
  let tmp := subWord (rotWord w3) ^^^ rconWord rc
  let w0' := w0 ^^^ tmp
  let w1' := w1 ^^^ w0'
  let w2' := w2 ^^^ w1'
  let w3' := w3 ^^^ w2'
  #v[w0', w1', w2', w3']

def bytesToState (v : 𝔹 16) : State :=
  Vector.ofFn fun c =>
    Vector.ofFn fun r =>
      v[c.val * 4 + r.val]

def stateToBytes (s : State) : 𝔹 16 :=
  Vector.ofFn fun i =>
    s[i.val / 4][i.val % 4]

lemma stateToBytes_bytesToState v : stateToBytes (bytesToState v) = v := by
  simp [stateToBytes, bytesToState]
  apply Vector.ext
  intro i hi
  simp
  grind

private def mul02 b := xtime b
private def mul03 b := mul02 b ^^^ b

def mixColumn (col : Word) :=
  let a0 := col[0]
  let a1 := col[1]
  let a2 := col[2]
  let a3 := col[3]
  #v[ mul02 a0 ^^^ mul03 a1 ^^^       a2 ^^^       a3,
            a0 ^^^ mul02 a1 ^^^ mul03 a2 ^^^       a3,
            a0 ^^^       a1 ^^^ mul02 a2 ^^^ mul03 a3,
      mul03 a0 ^^^       a1 ^^^       a2 ^^^ mul02 a3]

def mixColumns (s : State) : State := Vector.map mixColumn s

def subBytes (s : State) : State := Vector.map (Vector.map subByte) s

def shiftRows (s : State) : State :=
  Vector.ofFn fun c =>
    Vector.ofFn fun r =>
      s[(c + r) % 4][r]

def rounds := 10
def roundConstant : 𝔹 rounds := Vector.map byte
  #v[ 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36 ]

instance : XorOp State where
  xor s rk :=
    Vector.ofFn fun c =>
      Vector.ofFn fun r =>
        s[c][r] ^^^ rk[c][r]

def round (r : Nat) (s : State) :=
  let s := subBytes s
  let s := shiftRows s
  if r = rounds - 1 then s else mixColumns s

def aes128 (key plain : 𝔹 16) : 𝔹 16 := Id.run do
  let mut keys  := bytesToState key
  let mut state := bytesToState plain ^^^ keys
  for r in [0 : rounds] do
    keys  := key_round keys roundConstant[r]!
    state := round r state ^^^ keys
  return stateToBytes state

end Spec.AES

open Spec.Utils
