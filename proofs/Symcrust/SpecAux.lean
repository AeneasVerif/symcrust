import Symcrust.Spec
import Init.Data.Range

/-!
An auxiliary specification that we use to prove a refinement result.
This specification refines the specification in `Spec`, and is refined by the code.
It does not need to be trusted.
-/

namespace Symcrust.SpecAux

open Symcrust.Spec

-- Small test
def replicate' (n : Nat) (x : α) : List α := Id.run do
  let mut l := []
  for _ in [0:n] do
    l := x :: l
  pure l

theorem replicate'_eq n (x : α) : replicate' n x = List.replicate n x := by
  suffices replicate' n x = [] ++ List.replicate n x by
    simp_all
  simp only [replicate', Id.run, Id.pure_eq, Id.bind_eq, Std.Range.forIn_eq_forIn_range',
    Std.Range.size, tsub_zero, add_tsub_cancel_right, Nat.div_one, List.forIn_yield_eq_foldl]
  generalize hi: 0 = i
  generalize hl : [] = l
  have hRepl : l = List.replicate i x := by simp_all
  clear hi hl
  revert i l
  induction n <;> intro i l <;> simp_all [List.range']
  rename_i n hInd
  intro hRepl
  replace hInd := hInd (i + 1)
  simp [List.replicate] at hInd
  simp [hInd]
  omega

/-
def ntt (f : Polynomial) : Polynomial := Id.run do
  let mut f := f
  let mut i : Nat := 1
  for k in [0:8] do
    let len:Nat := 2 ^ (7 - k)
    for start in [0:256:2*len] do
      let zeta := ζ ^ (bitRev 7 i)
      i := i + 1
      for j in [start:start+len] do
        let t := zeta * f[j + len]!
        f := f.set (j + len) (f[j]! - t)
        f := f.set j (f[j]! + t)
-/

#print ntt

local macro_rules
| `([ $start : $stop : $step ]) =>
  `({ start := $start, stop := $stop, step := $step, step_pos := by simp +zetaDelta [] : Std.Range })


/- Introduce auxiliary definitions to isolate the different loops inside the target specification -/
namespace Target

  def nttLayerInner (f : Polynomial) (k : Nat) (i : Nat) (l : Nat) : Polynomial := Id.run do
    let mut f := f
    let mut i := i
    let len := 2 ^ (7 - k)
    let start := 2 * len * l
    let zeta := ζ ^ (bitRev 7 i)
    for j in [start:start+len] do
      let t := zeta * f[j + len]!
      f := f.set (j + len) (f[j]! - t)
      f := f.set j (f[j]! + t)
    pure f

  def nttLayer (f : Polynomial) (k : Nat) (i : Nat) : Polynomial × Nat := Id.run do
    let mut f := f
    let mut i := i
    let len := 2 ^ (7 - k)
    for l in [0:256/(2*len)] do -- FIXME
      let i0 := i
      i := i + 1
      f := nttLayerInner f k i0 l
    pure (f, i)

  def ntt (f : Polynomial) : Polynomial := Id.run do
    let mut fi := (f, 1)
    for k in [0:8] do
      fi := nttLayer fi.1 k fi.2
    pure fi.1

  -- TODO: this takes a long time!
  theorem ntt_eq (f : Polynomial) : ntt f = Spec.ntt f := by
    rw [ntt, Spec.ntt]
    unfold nttLayer
    unfold nttLayerInner
    simp [Id.run]
    rfl

end Target

def nttLayerInner (f : Polynomial) (k : Nat) (len : Nat)
  (start : Nat) (j : Nat) : Polynomial :=
  if j < len then
    let c0 := f[start + j]!
    let c1 := f[start + j + len]!
    let zeta := ζ ^ bitRev 7 k
    let f := f.set (start + j) (c0 + c1 * zeta)
    let f := f.set (start + j + len) (c0 - c1 * zeta)
    nttLayerInner f k len start (j + 1)
  else f

def nttLayer (f : Polynomial) (k : Nat) (len : Nat) (start : Nat) (hLen : 0 < len := by decide) :
  Polynomial :=
  if start < 256 then
    let k := k + 1
    let f := nttLayerInner f k len start 0
    nttLayer f k len (start + 2 * len) hLen
  else f

def ntt (f : Polynomial) : Polynomial :=
  let f := nttLayer f 1 128 0
  let f := nttLayer f 2 64 0
  let f := nttLayer f 4 32 0
  let f := nttLayer f 8 16 0
  let f := nttLayer f 16 8 0
  let f := nttLayer f 32 4 0
  let f := nttLayer f 64 2 0
  f

#check Lean.Meta.Simp.Config

-- TODO: this lemma should exist somewhere
theorem fun_eq_arg_eq_imp_eq {α β : Type} (f g : α → β) (x y : α) :
  f = g → x = y → f x = g y := by
  simp +contextual

#check List.set_set_perm

-- TODO: move, also update the neq test
theorem Polynomial.set_set_neq {i j : Nat} (h : i ≠ j)
  (p : Polynomial) (x y : Zq) :
  (p.set i x).set j y = (p.set j y).set i x := by sorry

theorem Polynomial.get_set_neq {i j : Nat} (h : i ≠ j)
  (p : Polynomial) (x : Zq) :
  (p.set i x).get! j = p.get! j := by sorry

def nttLayerInner_eq
  (f : Polynomial) (k : Nat) (len : Nat)
  (start : Nat) (j : Nat) (l : Nat)
  (hLen : len = 2 ^ (7 - k))
  (hStart : start + j = 2 * len * l)
  :
  nttLayerInner f i len start j = Target.nttLayerInner f k i l
  := by
  -- Unfold the definitions and simplify
  unfold Target.nttLayerInner
  simp
  -- Generalize the goal for the induction
  simp only [← hLen, ← hStart]
  clear hLen hStart
  -- We do the induction on len - j
  generalize hSteps : len - j = steps
  -- We need this fact (we get it by doing a case disjunction - the case where
  -- it is false is trivial)
  dcases hLe : ¬ j ≤ len
  . -- len < j
    simp_all
    -- Simplify the lhs
    have h : ¬ j < len := by omega
    simp only [h, nttLayerInner, ↓reduceIte]
    -- Simplify the rhs
    have hRange : List.range' (start + j) len 1 = [] := by sorry
    simp only [Id.run, hRange, List.foldl_nil]
  . -- The real proof: j ≤ len
    revert f
    revert len j hLe hSteps
    induction steps <;> intro len j hLe hSteps f <;> unfold nttLayerInner
    . -- zero
      have : len = j := by omega
      simp_all [Id.run]
      have hRange : List.range' (start + j) j 1 = [] := by sorry
      simp [hRange]
    . -- succ
      rename_i steps hInd
      dcases hLe' : ¬ j < len
      . -- Simple case
        simp [hLe']
        have hRange : List.range' (start + j) len 1 = [] := by sorry
        simp [hRange, Id.run]
      . -- Recursive case
        simp [hLe']
        replace hInd := hInd len (j + 1) (by omega) (by omega)
        simp [hInd, Id.run]
        -- Perform one step of computation on the right:
        have hRange: List.range' (start + j) len 1 =
                     (start + j) :: List.range' (start + (j + 1)) len 1 := by
          sorry
        simp [hRange]
        -- Several `Polynomial.set` operations are inverted in the continutations
        apply fun_eq_arg_eq_imp_eq <;> try rfl
        apply fun_eq_arg_eq_imp_eq <;> try rfl
        -- Working on the interesting part: we need to swap the two updates
        have h1 := @Polynomial.set_set_neq (start + j) (start + j + len) (by omega)
        simp [h1]
        ring_nf
        have h2 := @Polynomial.get_set_neq (start + j + len) (start + j) (by omega)
        simp [h2, getElem!, getElem]
        ring_nf

end Symcrust.SpecAux
