import Symcrust.Spec

/-!
An auxiliary specification that we use to prove a refinement result.
This specification refines the specification in `Spec`, and is refined by the code.
It does not need to be trusted.
-/

attribute [-simp] List.getElem!_eq_getElem?_getD List.reduceReplicate Aeneas.SRRange.foldWhile_step

namespace Symcrust.Spec

open Aeneas Aeneas.SRRange

/-!
# Polynomials
-/

@[simp]
theorem Polynomial.getElem!_eq (l : List Zq) (h : l.length = 256) (i : Nat) :
  (⟨ l, h ⟩ : Polynomial)[i]! = l[i]! := by
  conv => lhs; simp [getElem!, getElem, get!]
  conv => rhs; simp [getElem!]

@[simp]
theorem Polynomial.set_eq (l : List Zq) (h : l.length = 256) (i : Nat) (x : Zq) :
  Polynomial.set ⟨ l, h ⟩ i x = (⟨ l.set i x, by simp [h] ⟩ : Polynomial) := by
  simp [set]

theorem Polynomial.eq_iff (f g : Polynomial) :
  f = g ↔ ∀ i < 256, f[i]! = g[i]! := by
  cases f; rename_i f hf
  cases g; rename_i g hg
  simp
  simp only [List.eq_iff_eq_getElem!, true_and, hf, hg]

theorem Polynomial.eq_iff' (f g : Polynomial) :
  f = g ↔ ∀ i < 128, (f[2 * i]! = g[2 * i]! ∧ f[2 * i + 1]! = g[2 * i + 1]!) := by
  rw [Polynomial.eq_iff]
  constructor <;> intros heq i hi
  . have h0 := heq (2 * i) (by omega)
    have h1 := heq (2 * i + 1) (by omega)
    simp only [h0, h1, and_self]
  . have h0 := heq (i / 2) (by omega)
    have h1 : 2 * (i / 2) = i ∨ 2 * (i / 2) + 1 = i := by omega
    cases h1 <;> simp_all only

@[simp]
theorem Polynomial.getElem!_add (f g : Polynomial) (i : Nat) :
  (f + g)[i]! = f[i]! + g[i]! := by
  cases f; rename_i f hf
  cases g; rename_i g hg
  simp [instHAddPolynomial]
  dcases hi : i < 256
  . simp [*]
  . simp at hi
    simp [*, default]

theorem Polynomial.add_assoc (f g h : Polynomial) : f + g + h = f + (g + h) := by
  simp only [eq_iff, getElem!_add]
  intro i hi
  ring_nf

theorem Polynomial.add_comm (f g : Polynomial) : f + g = g + f := by
  simp only [eq_iff, getElem!_add]
  intro i hi
  apply AddCommMagma.add_comm

theorem Polynomial.set_comm {i j : Nat} (h : Nat.not_eq i j)
  (p : Polynomial) (x y : Zq) :
  (p.set i x).set j y = (p.set j y).set i x := by
  cases p; simp [*]
  rw [List.set_comm]
  simp only [Nat.not_eq, ne_eq, lt_or_lt_iff_ne] at h
  omega

theorem Polynomial.getElem!_set_self {i : Nat} (hi : i < 256)
  (p : Polynomial) (x : Zq) :
  (p.set i x)[i]! = x := by
  cases p; simp [*]

theorem Polynomial.getElem!_set_neq {i j : Nat} (h : i ≠ j)
  (p : Polynomial) (x : Zq) :
  (p.set i x)[j]! = p[j]! := by
  cases p; simp [*]

@[simp]
theorem Polynomial.zero_add (f : Polynomial) : Polynomial.zero + f = f := by
  simp +contextual only [zero, eq_iff, getElem!_add, getElem!_eq, List.getElem!_replicate,
    _root_.zero_add, implies_true]

@[simp]
theorem Polynomial.add_zero (f : Polynomial) : f + Polynomial.zero = f := by
  simp +contextual only [zero, eq_iff, getElem!_add, getElem!_eq, List.getElem!_replicate,
    _root_.add_zero, implies_true]

@[simp]
theorem Polynomial.zero_getElem! (i : Nat) :
  Polynomial.zero[i]! = 0 := by
  simp [Polynomial.zero]
  dcases i < 256 <;>
  simp_all only [List.getElem!_replicate, not_lt, List.length_replicate, List.getElem!_length_le, default]

end Symcrust.Spec

namespace Symcrust.SimpLists

open Symcrust.Spec

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic in
scoped syntax (name := natify) "simp_lists" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| simp_lists $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic|
    simp -decide (maxDischargeDepth := 1) (disch := omega) only
      [List.getElem!_set_neq, List.getElem!_set_self,
       Polynomial.getElem!_set_neq, Polynomial.getElem!_set_self,
       $args,*] $[at $location]?)

end Symcrust.SimpLists

namespace Symcrust.SpecAux

open Symcrust.Spec
open SimpLists
open Aeneas.SRRange

-- TODO: this lemma should exist somewhere
private theorem fun_eq_arg_eq_imp_eq {α β : Type} (f g : α → β) (x y : α) :
  f = g → x = y → f x = g y := by
  simp +contextual

/-!
# Auxiliary helpers
-/

/- Introduce auxiliary definitions to isolate the different loops inside the target specification -/
namespace Target

  open Aeneas.Notations.SRRange
  open Aeneas.Notations.DivRange
  open Aeneas.Notations.MulRange
  open Symcrust.Spec.Notations

  def nttLayerInner (f : Polynomial) (i len start : Nat) : Polynomial := Id.run do
    let mut f := f
    let mut i := i
    let zeta := ζ ^ (bitRev 7 i)
    for j in [start:start+len] do
      let t := zeta * f[j + len]!
      f := f.set (j + len) (f[j]! - t)
      f := f.set j (f[j]! + t)
    pure f

  def nttLayer (f : Polynomial) (i len : Nat) (hLen : 0 < len := by assumption) : Polynomial × Nat := Id.run do
    let mut f := f
    let mut i := i
    for start in [0:256:2*len] do
      let i0 := i
      i := i + 1
      f := nttLayerInner f i0 len start
    pure (f, i)

  def ntt (f : Polynomial) : Polynomial := Id.run do
    let mut fi := (f, 1)
    for h: len in [128 : >1 : /= 2] do
      fi := nttLayer fi.1 fi.2 len (by simp [Membership.mem] at *; omega)
    pure fi.1

  theorem ntt_eq (f : Polynomial) : ntt f = Spec.ntt f := by
    rw [ntt, Spec.ntt]
    unfold nttLayer
    unfold nttLayerInner
    simp only [Id.run]
    rfl

  def invNttLayerInner (f : Polynomial) (i len start : Nat) : Polynomial := Id.run do
    let mut f := f
    let zeta := ζ ^(bitRev 7 i)
    for j in [start:start+len] do
      let t := f[j]!
      f := f.set j (t + f[j + len]!)
      f := f.set (j + len) (zeta * (f[j + len]! - t))
    pure f

  def invNttLayer (f : Polynomial) (i len : Nat) (hLen : 0 < len := by assumption) : Polynomial × Nat := Id.run do
    let mut f := f
    let mut i := i
    for start in [0:256:2*len] do
      let i0 := i
      i := i - 1
      f := invNttLayerInner f i0 len start
    pure (f, i)

  def invNtt (f : Polynomial) : Polynomial := Id.run do
    let mut fi := (f, 127)
    let mut i := 127
    for h: len in [2 : <256 : *= 2] do
      fi := invNttLayer fi.1 fi.2 len (by simp +zetaDelta [Membership.mem] at *; omega)
    pure (fi.1 * (3303 : Zq))

  theorem invNtt_eq (f : Polynomial) : invNtt f = Spec.invNtt f := by
    rw [invNtt, Spec.invNtt]
    unfold invNttLayer
    unfold invNttLayerInner
    simp only [Id.run]
    rfl
end Target

/-!
# The auxiliary specs
-/

def nttLayerInner (f : Polynomial) (i : Nat) (len : Nat)
  (start : Nat) (j : Nat) : Polynomial :=
  if j < len then
    let c0 := f[start + j]!
    let c1 := f[start + j + len]!
    let zeta := ζ ^ bitRev 7 i
    let f := f.set (start + j) (c0 + c1 * zeta)
    let f := f.set (start + j + len) (c0 - c1 * zeta)
    nttLayerInner f i len start (j + 1)
  else f

def nttLayer (f : Polynomial) (i : Nat) (len : Nat) (start : Nat) (hLen : 0 < len := by simp) :
  Polynomial :=
  if start < 256 then
    let f := nttLayerInner f i len start 0
    nttLayer f (i + 1) len (start + 2 * len) hLen
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

def invNttLayerInner (f : Polynomial) (i : Nat) (len : Nat)
  (start : Nat) (j : Nat) : Polynomial :=
  if j < len then
    let c0 := f[start + j]!
    let c1 := f[start + j + len]!
    let zeta := ζ ^ bitRev 7 i
    let f := f.set (start + j) (c0 + c1)
    let f := f.set (start + j + len) (zeta * (c1 - c0))
    invNttLayerInner f i len start (j + 1)
  else f

def invNttLayer (f : Polynomial) (i : Nat) (len : Nat) (start : Nat) (hLen : 0 < len := by simp) :
  Polynomial :=
  if start < 256 then
    let f := invNttLayerInner f i len start 0
    invNttLayer f (i - 1) len (start + 2 * len) hLen
  else f

def invNtt (f : Polynomial) : Polynomial :=
  let f := invNttLayer f 127 2 0
  let f := invNttLayer f 63 4 0
  let f := invNttLayer f 31 8 0
  let f := invNttLayer f 15 16 0
  let f := invNttLayer f 7 32 0
  let f := invNttLayer f 3 64 0
  let f := invNttLayer f 1 128 0
  f * (3303 : Zq)

/-!
# The proofs about the NTT
-/

private theorem nttLayerInner_eq
  (f : Polynomial) (i len start : Nat) :
  nttLayerInner f i len start 0 = Target.nttLayerInner f i len start
  := by
  -- Unfold the definitions and simplify
  generalize hj : 0 = j
  unfold Target.nttLayerInner
  simp only [Id.run, Id.pure_eq, Id.bind_eq, Aeneas.SRRange.forIn_eq_forIn_range',
    Aeneas.SRRange.size, add_tsub_cancel_left, add_tsub_cancel_right, Nat.div_one,
    List.forIn_yield_eq_foldl, zero_lt_one, Aeneas.SRRange.foldl_range', mul_one]
  have : start = start + j := by simp only [self_eq_add_right, hj]
  conv => rhs; arg 5; rw [this]
  clear this
  -- We do the induction on len - j
  generalize hSteps : len - j = steps
  clear hj
  -- We need this fact (we get it by doing a case disjunction - the case where
  -- it is false is trivial)
  dcases hLe : ¬ j ≤ len
  . -- Simple case: len < j
    simp_all only [not_le]
    -- Simplify the lhs
    have h : ¬ j < len := by omega
    simp [h, nttLayerInner, ↓reduceIte, *]
  . -- Interesting case: j ≤ len
    revert f
    revert len j
    induction steps <;> intro len j hSteps hLe f <;> unfold nttLayerInner
    . -- zero
      have : len = j := by omega
      simp_all only [tsub_self, le_refl, lt_self_iff_false, ite_false]
      simp only [lt_self_iff_false, not_false_eq_true, Aeneas.SRRange.foldWhile_id, implies_true]
    . -- succ
      rename_i steps hInd
      dcases hLe' : ¬ j < len
      . -- Simple case
        simp only [↓reduceIte, add_lt_add_iff_left, not_false_eq_true, Aeneas.SRRange.foldWhile_id,
          implies_true, hLe']
      . -- Recursive case
        simp only [↓reduceIte, add_lt_add_iff_left, Aeneas.SRRange.foldWhile_step, Subtype.forall,
          hLe']
        replace hInd := hInd len (j + 1) (by omega) (by omega)
        simp only [hInd]
        -- Several `Polynomial.set` operations are inverted in the continutations
        -- We first zoom into the interesting terms
        apply fun_eq_arg_eq_imp_eq <;> try rfl
        clear hInd
        -- Working on the interesting part: we need to swap the two updates
        rw [Polynomial.set_comm] <;> try omega
        rw [Polynomial.getElem!_set_neq] <;> try omega
        ring_nf

private theorem nttLayer_eq_fst_aux (f : Polynomial) (i len start : Nat) (hLenLt : 0 < len) :
  let p : MProd _ _ := foldWhile 256 (2 * len) (by omega) (fun b a => ⟨Target.nttLayerInner b.1 b.2 len a, b.2 + 1⟩) start ⟨f, i⟩
  nttLayer f i len start hLenLt = p.fst := by
  simp only
  unfold nttLayer foldWhile
  split
  . rename_i hLt
    simp only
    have := nttLayerInner_eq f i len start
    rw [this]; clear this
    have := nttLayer_eq_fst_aux (Target.nttLayerInner f i len start) (i + 1) len (start + 2 * len) hLenLt
    simp only at this
    rw [this]
  . simp_all

private theorem nttLayer_eq_fst_arith
  (len : Nat) (hLen : ∃ k, k ≤ 7 ∧ len = 2 ^k) :
  (255 / (2 * len) + 1) * (2 * len) = 256 := by
  -- We simply brute force the proof by making a case disjunction on k
  -- TODO: the proof is quite simple but the theorem must be generalized (and the proof is then induction)
  replace ⟨ k, hLen ⟩ := hLen
  repeat (cases k <;> simp_all <;> rename_i k <;> try omega)

private theorem nttLayer_eq_fst (f : Polynomial) (i len : Nat)
  (hLen : 0 < len) (hkLen : ∃ k, k ≤ 7 ∧ len = 2 ^ k) :
  nttLayer f i len 0 hLen = (Target.nttLayer f i len).fst := by
  unfold Target.nttLayer
  simp only [Id.run, Id.pure_eq, Id.bind_eq, forIn_eq_forIn_range', size, tsub_zero,
    Nat.succ_add_sub_one, Nat.ofNat_pos, mul_pos_iff_of_pos_left, hLen, Nat.add_div_right,
    List.forIn_yield_eq_foldl, foldl_range', zero_add]
  have := nttLayer_eq_fst_arith len hkLen
  simp only [this]
  have := nttLayer_eq_fst_aux f i len 0 hLen
  simp only at this
  simp only [this]

private theorem  nttLayer_eq_snd_aux
  (x : α) (f : α → Nat → Nat → α)
  (i start len step : ℕ):
  (List.foldl (fun (b : MProd _ _) a => ⟨f b.fst b.snd a, b.snd + 1⟩) ⟨x, i⟩
    (List.range' start len step)).snd =
  i + len
  := by
  revert x i start
  induction len <;> intro x i start
  . simp_all
  . rename_i len hInd
    simp_all [List.range']
    ring_nf

private theorem nttLayer_eq_snd
  (f : Polynomial) (i len : Nat) (hLen : 0 < len) :
  (Target.nttLayer f i len).snd = i + 255 / (2 * len) + 1 := by
  unfold Target.nttLayer
  simp only [Id.run, Id.pure_eq, Id.bind_eq, Aeneas.SRRange.forIn_eq_forIn_range',
    Aeneas.SRRange.size, tsub_zero, Nat.succ_add_sub_one, Nat.ofNat_pos, mul_pos_iff_of_pos_left,
    pow_pos, Nat.add_div_right, List.forIn_yield_eq_foldl, hLen]
  have := nttLayer_eq_snd_aux f (fun x y => Target.nttLayerInner x y len) i
  simp only [this, add_right_inj]
  ring_nf

private theorem nttLayer_eq_aux (f : Polynomial) (i len : Nat)
  (hLen : 0 < len) (hkLen : ∃ k, k ≤ 7 ∧ len = 2 ^ k) :
  (nttLayer f i len 0 (by simp [hLen]), i + 255 / (2 * len) + 1) = Target.nttLayer f i len := by
  have := nttLayer_eq_fst f i len hLen
  have := nttLayer_eq_snd f i len hLen
  cases h: Target.nttLayer f i len
  simp_all

private theorem nttLayer_eq (f : Polynomial) (len : Nat) (hLen : 0 < len)
  (hkLen : len = 2 ^ (Nat.log2 len) ∧ Nat.log2 len ≤ 7) :
  (nttLayer f i len 0 hLen, i + 255 / (2 * len) + 1) = Target.nttLayer f i len := by
  rw [nttLayer_eq_aux]
  exists len.log2
  tauto

private theorem ntt_eq_target (f : Polynomial) :
  ntt f = Target.ntt f := by
  unfold ntt Target.ntt
  simp [Id.run, Aeneas.divRange, Aeneas.divRange.loop]
  repeat (rw [← nttLayer_eq] <;> simp [Nat.log2])

/-- This is the important theorem -/
theorem ntt_eq (f : Polynomial) :
  ntt f = Spec.ntt f := by
  rw [ntt_eq_target, Target.ntt_eq]

/-!
# The proofs about the NTT⁻¹
-/

private theorem invNttLayerInner_eq
  (f : Polynomial) (i len start : Nat) :
  invNttLayerInner f i len start 0 = Target.invNttLayerInner f i len start
  := by
  -- Unfold the definitions and simplify
  generalize hj : 0 = j
  unfold Target.invNttLayerInner
  simp only [Id.run, Id.pure_eq, Id.bind_eq, forIn_eq_forIn_range', size, add_tsub_cancel_left,
    add_tsub_cancel_right, Nat.div_one, List.forIn_yield_eq_foldl, zero_lt_one, foldl_range',
    mul_one]
  have : start = start + j := by simp only [self_eq_add_right, hj]
  conv => rhs; arg 5; rw [this]
  clear this
  -- We do the induction on len - j
  generalize hSteps : len - j = steps
  clear hj
  -- We need this fact (we get it by doing a case disjunction - the case where
  -- it is false is trivial)
  dcases hLe : ¬ j ≤ len
  . -- Simple case: len < j
    simp_all only [not_le]
    -- Simplify the lhs
    have h : ¬ j < len := by omega
    simp [h, invNttLayerInner, ↓reduceIte, *]
  . -- Interesting case: j ≤ len
    revert f
    revert len j
    induction steps <;> intro len j hSteps hLe f <;> unfold invNttLayerInner
    . -- zero
      have : len = j := by omega
      simp_all only [tsub_self, le_refl, lt_self_iff_false, ite_false]
      simp only [lt_self_iff_false, not_false_eq_true, Aeneas.SRRange.foldWhile_id, implies_true]
    . -- succ
      rename_i steps hInd
      dcases hLe' : ¬ j < len
      . -- Simple case
        simp only [↓reduceIte, add_lt_add_iff_left, not_false_eq_true, Aeneas.SRRange.foldWhile_id,
          implies_true, hLe']
      . -- Recursive case
        simp only [hLe', ↓reduceIte, add_lt_add_iff_left, foldWhile_step]
        replace hInd := hInd len (j + 1) (by omega) (by omega)
        simp only [hInd]
        -- Several `Polynomial.set` operations are inverted in the continutations
        -- We first zoom into the interesting terms
        apply fun_eq_arg_eq_imp_eq <;> try rfl
        clear hInd
        -- Working on the interesting part: we need to simplify a write/read
        rw [Polynomial.getElem!_set_neq]; omega

private theorem invNttLayer_eq_fst_aux (f : Polynomial) (i len start : Nat) (hLenLt : 0 < len) :
  let p : MProd _ _ := foldWhile 256 (2 * len) (by omega) (fun b a => ⟨Target.invNttLayerInner b.1 b.2 len a, b.2 - 1⟩) start ⟨f, i⟩
  invNttLayer f i len start hLenLt = p.fst := by
  simp only
  unfold invNttLayer foldWhile
  split
  . rename_i hLt
    simp only
    have := invNttLayerInner_eq f i len start
    rw [this]; clear this
    have := invNttLayer_eq_fst_aux (Target.invNttLayerInner f i len start) (i - 1) len (start + 2 * len) hLenLt
    simp only at this
    rw [this]
  . simp_all

private theorem invNttLayer_eq_fst_arith
  (len : Nat) (hLen : ∃ k, k ≤ 7 ∧ len = 2 ^k) :
  (255 / (2 * len) + 1) * (2 * len) = 256 := by
  -- We simply brute force the proof by making a case disjunction on k
  -- TODO: the proof is quite simple but the theorem must be generalized (and the proof is then induction)
  replace ⟨ k, hLen ⟩ := hLen
  repeat (cases k <;> simp_all <;> rename_i k <;> try omega)

private theorem invNttLayer_eq_fst (f : Polynomial) (i len : Nat)
  (hLen : 0 < len) (hkLen : ∃ k, k ≤ 7 ∧ len = 2 ^ k) :
  invNttLayer f i len 0 hLen = (Target.invNttLayer f i len).fst := by
  unfold Target.invNttLayer
  simp only [Id.run, Id.pure_eq, Id.bind_eq, forIn_eq_forIn_range', size, tsub_zero,
    Nat.succ_add_sub_one, Nat.ofNat_pos, mul_pos_iff_of_pos_left, hLen, Nat.add_div_right,
    List.forIn_yield_eq_foldl, foldl_range', zero_add]
  have := invNttLayer_eq_fst_arith len hkLen
  simp only [this]
  have := invNttLayer_eq_fst_aux f i len 0 hLen
  simp only at this
  simp only [this]

private theorem  invNttLayer_eq_snd_aux
  (x : α) (f : α → Nat → Nat → α)
  (i start len step : ℕ):
  (List.foldl (fun (b : MProd _ _) a => ⟨f b.fst b.snd a, b.snd - 1⟩) ⟨x, i⟩
    (List.range' start len step)).snd =
  i - len
  := by
  revert x i start
  induction len <;> intro x i start
  . simp_all
  . rename_i len hInd
    simp_all [List.range']
    omega

private theorem invNttLayer_eq_snd
  (f : Polynomial) (i len : Nat) (hLen : 0 < len) :
  (Target.invNttLayer f i len hLen).snd = i - (255 / (2 * len) + 1) := by
  unfold Target.invNttLayer
  simp only [Id.run, Id.pure_eq, Id.bind_eq, Aeneas.SRRange.forIn_eq_forIn_range',
    Aeneas.SRRange.size, tsub_zero, Nat.succ_add_sub_one, Nat.ofNat_pos, mul_pos_iff_of_pos_left,
    pow_pos, Nat.add_div_right, List.forIn_yield_eq_foldl, hLen]
  have := invNttLayer_eq_snd_aux f (fun x y => Target.invNttLayerInner x y len) i
  simp only [this, add_right_inj]

private theorem invNttLayer_eq_aux (f : Polynomial) (i len : Nat)
  (hLen : 0 < len) (hkLen : ∃ k, k ≤ 7 ∧ len = 2 ^ k) :
  (invNttLayer f i len 0 (by simp [hLen]), i - (255 / (2 * len) + 1)) = Target.invNttLayer f i len := by
  have := invNttLayer_eq_fst f i len hLen
  have := invNttLayer_eq_snd f i len hLen
  cases h: Target.invNttLayer f i len
  simp_all

private theorem invNttLayer_eq (f : Polynomial) (len : Nat) (hLen : 0 < len)
  (hkLen : len = 2 ^ (Nat.log2 len) ∧ Nat.log2 len ≤ 7) :
  (invNttLayer f i len 0 hLen, i - (255 / (2 * len) + 1)) = Target.invNttLayer f i len := by
  rw [invNttLayer_eq_aux]
  exists len.log2
  tauto

private theorem invNtt_eq_target (f : Polynomial) :
  invNtt f = Target.invNtt f := by
  unfold invNtt Target.invNtt
  simp [Id.run, Aeneas.mulRange]
  repeat (rw [← invNttLayer_eq] <;> try simp [Nat.log2])

/-- This is the important theorem -/
theorem invNtt_eq (f : Polynomial) :
  invNtt f = Spec.invNtt f := by
  rw [invNtt_eq_target, Target.invNtt_eq]

/-!
# Multiply NTTs
-/

/-- Auxiliary helper -/
private def baseCaseMultiply0 (f g : Polynomial) (i : Nat) : Zq :=
  let a0 := f[2 * i]!
  let a1 := f[2 * i + 1]!
  let b0 := g[2 * i]!
  let b1 := g[2 * i + 1]!
  let γ := ζ^(2 * bitRev 7 i + 1)
  a0 * b0 + a1 * b1 * γ

/-- Auxiliary helper -/
private def baseCaseMultiply1 (f g : Polynomial) (i : Nat) : Zq :=
  let a0 := f[2 * i]!
  let a1 := f[2 * i + 1]!
  let b0 := g[2 * i]!
  let b1 := g[2 * i + 1]!
  let γ := ζ^(2 * bitRev 7 i + 1)
  a0 * b1 + a1 * b0 * γ

private theorem baseCaseMultiply_eq (f g : Polynomial) (i : Nat) :
  baseCaseMultiply f[2 * i]! f[2 * i + 1]! g[2 * i]! g[2 * i + 1]! (ζ^(2 * bitRev 7 i + 1)) =
  (baseCaseMultiply0 f g i, baseCaseMultiply1 f g i) := by
  simp [baseCaseMultiply, baseCaseMultiply0, baseCaseMultiply1]

/-- The definition we will use in the proofs of refinement with the code -/
def multiplyNTTs (f g h : Polynomial) (i : Nat) : Polynomial :=
  if i < 128 then
    let (c0, c1) := baseCaseMultiply f[2 * i]! f[2 * i + 1]! g[2 * i]! g[2 * i + 1]! (ζ^(2 * bitRev 7 i + 1))
    let h := h.set (2 * i) (h[2 * i]! + c0)
    let h := h.set (2 * i + 1) (h[2 * i + 1]! + c1)
    multiplyNTTs f g h (i + 1)
  else h

/-- The important equation which allows reasoning about `multiplyNTTs` -/
private theorem multiplyNTTs_getElem! (f g h : Polynomial) (i j : Nat) (hj : j < 128) :
  (multiplyNTTs f g h i)[2 * j]! = (if j < i then h[2 * j]! else h[2 * j]! + baseCaseMultiply0 f g j) ∧
  (multiplyNTTs f g h i)[2 * j + 1]! = (if j < i then h[2 * j + 1]! else h[2 * j + 1]! + baseCaseMultiply1 f g j) := by
  unfold multiplyNTTs
  simp [baseCaseMultiply_eq]
  split <;> rename_i hi
  . have hind h := multiplyNTTs_getElem! f g h (i + 1) j hj
    dcases hij0 : j < i
    . simp only [hij0, ↓reduceIte]
      simp_lists [hind]
      have : j < i + 1 := by omega
      simp only [this, ↓reduceIte, and_self]
    . -- i ≤ j
      simp only [not_lt] at hij0
      dcases hij1 : j = i
      . simp_all only
        have : i < i + 1 := by omega
        simp only [this, ↓reduceIte, lt_self_iff_false]
        simp_lists
        simp only [and_self]
      . -- i < j
        have : ¬ j < i := by omega
        simp only [this, ↓reduceIte]
        simp_lists [hind]
        have : ¬ j < i + 1 := by omega
        simp only [this, ↓reduceIte, and_self]
  . simp only [not_lt] at hi
    have hij : j < i := by omega
    simp only [hij, ↓reduceIte, and_self]

/-- Auxiliary helper -/
private def multiplyNTTs_pure (f g h : Polynomial) (i : Nat) : Polynomial :=
  if i < 128 then
    let (c0, c1) := baseCaseMultiply f[2 * i]! f[2 * i + 1]! g[2 * i]! g[2 * i + 1]! (ζ^(2 * bitRev 7 i + 1))
    let h := h.set (2 * i) c0
    let h := h.set (2 * i + 1) c1
    multiplyNTTs_pure f g h (i + 1)
  else h

/-- The important equation which allows reasoning about `multiplyNTTs_pure` -/
private theorem multiplyNTTs_pure_getElem! (f g h : Polynomial) (i j : Nat) (hj : j < 128) :
  (multiplyNTTs_pure f g h i)[2 * j]! = (if j < i then h[2 * j]! else baseCaseMultiply0 f g j) ∧
  (multiplyNTTs_pure f g h i)[2 * j + 1]! = (if j < i then h[2 * j + 1]! else baseCaseMultiply1 f g j) := by
  unfold multiplyNTTs_pure
  simp [baseCaseMultiply_eq]
  split <;> rename_i hi
  . have hind h := multiplyNTTs_pure_getElem! f g h (i + 1) j hj
    dcases hij0 : j < i
    . simp only [hij0, ↓reduceIte]
      simp_lists [hind]
      have : j < i + 1 := by omega
      simp only [this, ↓reduceIte, and_self]
    . -- i ≤ j
      simp only [not_lt] at hij0
      dcases hij1 : j = i
      . simp_all only
        have : i < i + 1 := by omega
        simp only [this, ↓reduceIte, lt_self_iff_false]
        simp_lists
        simp only [and_self]
      . -- i < j
        have : ¬ j < i := by omega
        simp only [this, ↓reduceIte]
        simp_lists [hind]
        have : ¬ j < i + 1 := by omega
        simp only [this, ↓reduceIte, and_self]
  . simp only [not_lt] at hi
    have hij : j < i := by omega
    simp only [hij, ↓reduceIte, and_self]

private def Target.multiplyNTTs_inner (f g h : Polynomial) (i0 : Nat) : Polynomial := Id.run do
  let mut h := h
  for i in [i0:128] do
    let (c0, c1) := baseCaseMultiply f[2 * i]! f[2 * i + 1]! g[2 * i]! g[2 * i + 1]! (ζ^(2 * bitRev 7 i + 1))
    h := h.set (2 * i) c0
    h := h.set (2 * i + 1) c1
  pure h

/--
Linking `Target.multiplyNTTs` to `Spec.multiplyNTTs`
-/
private theorem Target.multiplyNTTs_inner_eq_spec (f g : Polynomial) :
  Target.multiplyNTTs_inner f g Polynomial.zero 0 = Spec.multiplyNTTs f g := by
  unfold Target.multiplyNTTs_inner Spec.multiplyNTTs
  simp only
  generalize 0 = i -- annoying that we have to do this
  simp only [Id.pure_eq, Id.bind_eq, Std.Range.forIn_eq_forIn_range', Std.Range.size,
    add_tsub_cancel_right, Nat.div_one, List.forIn_yield_eq_foldl, zero_lt_one, foldl_range',
    mul_one, forIn_eq_forIn_range', size]

/--
Linking `Target.multiplyNTTs` to `multiplyNTTs_pure`
-/
private theorem Target.multiplyNTTs_inner_eq (f g : Polynomial) :
  Target.multiplyNTTs_inner f g Polynomial.zero 0 = multiplyNTTs_pure f g Polynomial.zero 0 := by
  unfold Target.multiplyNTTs_inner
  simp only [Id.run, Id.pure_eq, Id.bind_eq, Std.Range.forIn_eq_forIn_range', Std.Range.size,
    tsub_zero, Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one, List.forIn_yield_eq_foldl,
    zero_lt_one, foldl_range', mul_one, zero_add]
  -- Using a useful equation satisfied by `foldWhile`
  rw [← eq_foldWhile]
  intro h i
  conv => lhs; unfold multiplyNTTs_pure

private theorem multiplyNTTs_eq_multiplyNTTs_pure (f g : Polynomial) :
  multiplyNTTs f g Polynomial.zero 0 = multiplyNTTs_pure f g Polynomial.zero 0 := by
  simp only [Polynomial.eq_iff']
  intro i hi
  simp_lists [multiplyNTTs_getElem!, multiplyNTTs_pure_getElem!]
  simp only [not_lt_zero', ↓reduceIte, Polynomial.zero_getElem!, zero_add, and_self]

private theorem multiplyNTTs_add_zero (f g h : Polynomial) :
  multiplyNTTs f g h 0 = multiplyNTTs f g Polynomial.zero 0 + h := by
  simp only [Polynomial.eq_iff']
  intro i hi
  simp_lists [multiplyNTTs_getElem!, multiplyNTTs_pure_getElem!]
  simp only [not_lt_zero', ↓reduceIte, Polynomial.getElem!_add]
  simp_lists [multiplyNTTs_getElem!, multiplyNTTs_pure_getElem!]
  simp only [not_lt_zero', ↓reduceIte, Polynomial.zero_getElem!, zero_add]
  ring_nf
  simp only [and_self]

theorem multiplyNTTs_eq (f g h : Polynomial) :
  multiplyNTTs f g h 0 = Spec.multiplyNTTs f g + h := by
  rw [multiplyNTTs_add_zero]
  rw [multiplyNTTs_eq_multiplyNTTs_pure]
  rw [← Target.multiplyNTTs_inner_eq_spec]
  rw [Target.multiplyNTTs_inner_eq]

end Symcrust.SpecAux
