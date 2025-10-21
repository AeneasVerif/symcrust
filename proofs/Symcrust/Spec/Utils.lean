import Mathlib.Data.List.Defs
import Mathlib.Data.Vector.Defs
import Aeneas

-- JSON sandbox
import Lean.Data.Json
open Lean Json

/- trying out to parse actual JSON test vectors at scale; TBC -/

-- individual test case
structure TestCase where
  tcId : Nat    -- Test case ID
  c    : String -- Ciphertext or encapsulated key (hex string)
  k    : String -- Expected key or output (hex string)
  deriving FromJson, Repr

-- collection of test cases
structure TestGroup where
  tgId  : Nat           -- Test group ID
  tests : Array TestCase
  deriving FromJson, Repr

-- top-level expectedResults JSON object.
structure ExpectedResults where
  vsId      : Nat
  algorithm : String
  mode      : String
  revision  : String
  isSample  : Bool
  testGroups : Array TestGroup
  deriving FromJson, Repr

def trying_json  : IO Unit := do
  let jsonText ← IO.FS.readFile "/home/fournet/symcrust/proofs/Symcrust/Spec/encapDecap.json"
  let jsonVal := Json.parse jsonText
  match jsonVal with
  | .error err =>
      IO.eprintln s!"Failed to parse JSON: {err}"
      return  -- exit early or handle the error
  | .ok j =>
      let x ← IO.ofExcept (fromJson? j : Except String TestGroup)
      let x := x.tests
      for t in x do
        -- let k := parseHexVector? t.k
        IO.println s!"Loaded test case {t.tcId} with c={t.c} and k={t.k}."
      /-
      let x ← IO.ofExcept (j.getObjVal? "testGroups")
      match x with
      | arr a =>
        let x ← IO.ofExcept (a[1]!.getObjVal? "tests")
        match x with
        | arr a =>
          IO.println s!"Loaded {a[1]!}."
          let x ← IO.ofExcept (a[1]!.getObjVal? "c")
          IO.println s!"Loaded {x}."
          match x with
          | str x =>
            IO.println s!"Loaded {x}."; return
          | _ => return
        | _ => return
      | _ => return
      -/

namespace Spec.Utils

open Lean

abbrev Bytes (n : Nat) := Vector Byte n

def Byte.toHex (b : Byte) : Char :=
  if b < 10 then
    Char.ofNat ('0'.toNat + b.val)
  else
    Char.ofNat ('a'.toNat + (b.val - 10))

def Vector.toHex {n} (v : Bytes n) (trunc : Option Nat := .some 96): String :=
  Id.run do
    let mut s := ""
    for b in v do
      s := s.push (Byte.toHex (b / 16))
      s := s.push (Byte.toHex (b % 16))
    match trunc with
    | .some ℓ => s :=  s.take (ℓ - 13) ++ "..." ++ s.drop (n * 2 - 13)
    | .none => ()
    pure s

instance instToStringBytes {n} : ToString (Bytes n) where
  toString v := Vector.toHex v

def HexChar.toByte? (c : Char) : Option Byte :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + (c.toNat - 'A'.toNat))
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + (c.toNat - 'a'.toNat))
  else none

def Hex.toBytes? (s : String) : Option (Array Byte) :=
  let rec go : List Char → Array Byte → Option (Array Byte)
    | hi :: lo :: rest, acc => do
        let hi ← HexChar.toByte? hi
        let lo ← HexChar.toByte? lo
        go rest (acc.push (16 * hi + lo))
    | [], acc => some acc
    | _, _ => none
  go s.data #[]

def Hex.toVector? (s : String) (n : Nat) : Option (Bytes n) := do
  let arr ← Hex.toBytes? s
  if h : arr.size = n then
    pure ⟨arr, h⟩
  else
    none

syntax "v!" str : term
macro_rules
  | `(v! $s:str) => do
      let hex := s.getString
      if hex.length % 2 ≠ 0 then
        Macro.throwError s!"hex!: odd number ({hex.length}) of hex characters (must be even)."
      let n := Lean.quote (hex.length / 2)
      let h := Lean.quote hex
      `(match Hex.toVector? $h $n with
        | some a => a
        | none => panic! ("hex!: invalid hex literal: " ++ $h))

def expect {n} (label : String) (expected actual : Bytes n) : IO Unit := do
  if expected ≠ actual then
    let diff := Vector.ofFn (n := n) fun i => expected[i]! - actual[i]!
    IO.println s!"✘ {label}"
    IO.println s!"  expected: {expected}"
    IO.println s!"  got:      {actual}"
    IO.println s!"  diff:     {diff}"

def time {α β} (label : String) (f : α → β) (x : α) : IO β := do
  let t0 ← IO.monoMsNow
  let y := f x
  let t1 ← IO.monoMsNow
  IO.println s!"{label} in {t1 - t0} ms."
  pure y

end Spec.Utils
