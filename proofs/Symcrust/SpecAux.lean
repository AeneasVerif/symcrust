import Symcrust.Spec

/-!
An auxiliary specification that we use to prove a refinement result.
This specification refines the specification in `Spec`, and is refined by the code.
It does not need to be trusted.
-/

namespace Symcrust.SpecAux

open Symcrust.Spec

/- Introduce auxiliary definitions to isolate the different loops inside the target specification -/
namespace Target

  open Aeneas.Notations.SRRange
  open Aeneas.Notations.DivRange
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
    for h: len in [128 : >1 : /2] do
      fi := nttLayer fi.1 fi.2 len (by simp [Membership.mem] at *; omega)
    pure fi.1

  theorem ntt_eq (f : Polynomial) : ntt f = Spec.ntt f := by
    rw [ntt, Spec.ntt]
    unfold nttLayer
    unfold nttLayerInner
    simp [Id.run]
    rfl

end Target

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

-- TODO: move, also update the neq test
theorem Polynomial.set_set_neq {i j : Nat} (h : i ≠ j)
  (p : Polynomial) (x y : Zq) :
  (p.set i x).set j y = (p.set j y).set i x := by sorry

theorem Polynomial.get_set_neq {i j : Nat} (h : i ≠ j)
  (p : Polynomial) (x : Zq) :
  (p.set i x).get! j = p.get! j := by sorry

-- TODO: this lemma should exist somewhere
private theorem fun_eq_arg_eq_imp_eq {α β : Type} (f g : α → β) (x y : α) :
  f = g → x = y → f x = g y := by
  simp +contextual

private theorem nttLayerInner_eq
  (f : Polynomial) (i len start : Nat)
  :
  nttLayerInner f i len start 0 = Target.nttLayerInner f i len start
  := by
  -- Unfold the definitions and simplify
  unfold Target.nttLayerInner
  generalize hj : 0 = j
  simp only [Id.run, Id.pure_eq, Id.bind_eq, Aeneas.SRRange.forIn_eq_forIn_range',
    Aeneas.SRRange.size, add_tsub_cancel_left, add_tsub_cancel_right, Nat.div_one,
    List.forIn_yield_eq_foldl, zero_lt_one, Aeneas.SRRange.foldl_range', mul_one]
  have : start = start + j := by simp only [self_eq_add_right, hj]
  conv => rhs; arg 5; rw [this]
  clear this
  -- We do the induction on len - j
  generalize hSteps : len - j = steps
  have ⟨ j', hj' ⟩ : {n:Nat // n = start + j} := ⟨ start, by omega ⟩
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
    revert len j j'
    induction steps <;> intro len j hSteps j' hj' hLe f <;> unfold nttLayerInner
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
        simp only [↓reduceIte, add_lt_add_iff_left, Aeneas.SRRange.foldhile_step, Subtype.forall,
          hLe']
        replace hInd := hInd len (j + 1) (by omega) (j' + 1) (by omega) (by omega)
        simp only [hInd]
        -- Several `Polynomial.set` operations are inverted in the continutations
        -- We first zoom into the interesting terms
        apply fun_eq_arg_eq_imp_eq <;> try rfl
        clear hInd
        -- Working on the interesting part: we need to swap the two updates
        have h1 := @Polynomial.set_set_neq (start + j) (start + j + len) (by omega)
        simp only [h1]
        ring_nf
        have h2 := @Polynomial.get_set_neq (start + j + len) (start + j) (by omega)
        simp only [getElem!, dite_true, getElem, h2]
        ring_nf

open Aeneas.SRRange

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
  simp only [Id.pure_eq, Id.bind_eq, Aeneas.SRRange.forIn_eq_forIn_range', Aeneas.SRRange.size,
    tsub_zero, Nat.succ_add_sub_one, List.forIn_yield_eq_foldl]
  simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, hLen, Nat.add_div_right, foldl_range',
    zero_add]
  have : (255 / (2 * len) + 1) * (2 * len) = 256 := nttLayer_eq_fst_arith len hkLen
  simp only [this]
  have := nttLayer_eq_fst_aux f i len 0 hLen
  simp only at this
  simp only [this]
  simp [Id.run]

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

theorem nttEq (f : Polynomial) :
  ntt f = Target.ntt f := by
  unfold ntt Target.ntt
  simp [Id.run, Aeneas.divRange, Aeneas.divRange.loop]
  repeat (rw [← nttLayer_eq] <;> simp [Nat.log2])

end Symcrust.SpecAux
