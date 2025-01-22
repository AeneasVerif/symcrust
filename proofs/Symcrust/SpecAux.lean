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
  open Symcrust.Spec.Notations

  def nttLayerInner (f : Polynomial) (k : Nat) (i : Nat) (start : Nat) : Polynomial := Id.run do
    let mut f := f
    let mut i := i
    let len := 2 ^ (7 - k)
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
    for start in [0:256:2*len] do
      let i0 := i
      i := i + 1
      f := nttLayerInner f k i0 start
    pure (f, i)

  def ntt (f : Polynomial) : Polynomial := Id.run do
    let mut fi := (f, 1)
    for k in [0:7] do
      fi := nttLayer fi.1 k fi.2
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
  (f : Polynomial) (k i : Nat) (len : Nat)
  (start : Nat)
  (hLen : len = 2 ^ (7 - k))
  :
  nttLayerInner f i len start 0 = Target.nttLayerInner f k i start
  := by
  -- Unfold the definitions and simplify
  unfold Target.nttLayerInner
  simp only [Id.pure_eq, Id.bind_eq, Aeneas.SRRange.forIn_eq_forIn_range', Aeneas.SRRange.size,
    add_tsub_cancel_left, add_tsub_cancel_right, Nat.div_one, List.forIn_yield_eq_foldl]
  -- Generalize the goal for the induction
  simp only [← hLen]
  clear hLen
  generalize hj : 0 = j
  -- We do the induction on len - j
  generalize hSteps : len - j = steps
  have ⟨ j', hj' ⟩ : {n:Nat // n = start + j} := ⟨ start, by omega ⟩
  have hRange : List.range' start len 1 = List.range' j' (len + start- j') 1 := by
    have h0 : start = j' := by omega
    have h1 : len + start - j' = len := by omega
    simp [h0, h1]
  clear hj
  simp only [hRange]; clear hRange
  -- We need this fact (we get it by doing a case disjunction - the case where
  -- it is false is trivial)
  dcases hLe : ¬ j ≤ len
  . -- Simple case: len < j
    simp_all only [not_le]
    -- Simplify the lhs
    have h : ¬ j < len := by omega
    simp only [h, nttLayerInner, ↓reduceIte]
    -- Simplify the rhs
    have hRange : List.range' (start + j) (len + start - (start + j)) 1 = [] := by
      simp only [List.range'_eq_nil]; omega
    simp [Id.run, hRange]
  . -- Interesting case: j ≤ len
    revert f
    revert len j j'
    induction steps <;> intro len j hSteps j' hj' hLe f <;> unfold nttLayerInner
    . -- zero
      have : len = j := by omega
      simp_all only [tsub_self, le_refl, lt_self_iff_false, ite_false, Id.run]
      have hRange : List.range' (start + j) (j + start - (start + j)) = [] := by
        simp; omega
      simp [hRange]
    . -- succ
      rename_i steps hInd
      dcases hLe' : ¬ j < len
      . -- Simple case
        simp only [hLe', ↓reduceIte]
        have hRange : List.range' j' (len + start - j') = [] := by
          simp only [List.range'_eq_nil]; omega
        simp [hRange, Id.run]
      . -- Recursive case
        simp only [hLe', ↓reduceIte]
        replace hInd := hInd len (j + 1) (by omega) (j' + 1) (by omega) (by omega)
        simp only [hInd, Id.run]
        -- Perform one step of computation on the right:
        have : len + start - j' > 0 := by omega
        have hRange: List.range' j' (len + start - j') =
                     j' :: List.range' (j' + 1) (len + start - (j' + 1)) := by
          simp only [List.range'_eq_cons_iff, tsub_pos_iff_lt, List.range'_inj, or_true, and_true,
            true_and]
          omega
        simp only [hRange, List.foldl_cons]
        -- Several `Polynomial.set` operations are inverted in the continutations
        apply fun_eq_arg_eq_imp_eq <;> try rfl
        apply fun_eq_arg_eq_imp_eq <;> try rfl
        simp only [hj']
        -- Working on the interesting part: we need to swap the two updates
        have h1 := @Polynomial.set_set_neq (start + j) (start + j + len) (by omega)
        simp only [h1]
        ring_nf
        have h2 := @Polynomial.get_set_neq (start + j + len) (start + j) (by omega)
        simp only [getElem!, dite_true, getElem, h2]
        ring_nf

private def fold_while {α : Type u} (f : α → Nat → α) (max step : Nat) (hStep : 0 < step) (i : Nat) (init : α) : α :=
  if i < max then fold_while f max step hStep (i + step) (f init i)
  else init
termination_by max - i
decreasing_by omega

private theorem foldl_range' (f : α → Nat → α) (start len step : Nat) (hStep : 0 < step) (init : α) :
  List.foldl f init (List.range' start len step) = fold_while f (start + len * step) step hStep start init := by
  cases len
  . simp only [List.range'_zero, List.foldl_nil, zero_mul, add_zero]
    unfold fold_while
    simp
  . rename_i len
    simp only [List.range', List.foldl_cons]
    have := foldl_range' f (start + step) len step hStep (f init start)
    simp only [this]
    conv => rhs; unfold fold_while
    have : start < start + (len + 1) * step := by
      ring_nf
      omega
    simp only [this, ↓reduceIte]
    ring_nf

private theorem nttLayer_eq_fst_aux (f : Polynomial) (k : Nat) (len : Nat) (i start : Nat)
  (hk : k ≤ 7)
  (hLen : len = 2 ^ (7 - k))
  (hLenLt : 0 < len) :
  let p : MProd _ _ := fold_while (fun b a => ⟨Target.nttLayerInner b.1 k b.2 a, b.2 + 1⟩) 256 (2 * len) (by omega) start ⟨f, i⟩
  nttLayer f i len start hLenLt = p.fst := by
  simp only
  unfold nttLayer fold_while
  split
  . rename_i hLt
    simp only
    have := nttLayerInner_eq f k i len start (hLen)
    rw [this]; clear this
    have := nttLayer_eq_fst_aux (Target.nttLayerInner f k i start) k len (i + 1) (start + 2 * len) hk hLen hLenLt
    simp only at this
    rw [this]
  . simp_all

private theorem nttLayer_eq_fst_arith {k : ℕ} (hk : k ≤ 7) :
  (255 / (2 * 2 ^ (7 - k)) + 1) * (2 * 2 ^ (7 - k)) = 256 := by
  -- We simply brute force the proof by making a case disjunction on k
  -- TODO: the proof is quite simple but the theorem must be generalized (and the proof is then induction)
  repeat (cases k <;> simp_all <;> rename_i k <;> try omega)

private theorem nttLayer_eq_fst (f : Polynomial) (i k : Nat) (len : Nat)
  (hk : k ≤ 7) (hLen : len = 2 ^ (7 - k)) :
  nttLayer f i len 0 (by simp [hLen]) = (Target.nttLayer f k i).fst := by
  unfold Target.nttLayer
  simp only [Id.pure_eq, Id.bind_eq, Aeneas.SRRange.forIn_eq_forIn_range', Aeneas.SRRange.size,
    tsub_zero, Nat.succ_add_sub_one, Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos,
    Nat.add_div_right, List.forIn_yield_eq_foldl]
  simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos, foldl_range', hk,
    nttLayer_eq_fst_arith, zero_add]
  have := nttLayer_eq_fst_aux f k len i 0 hk hLen (by simp[hLen])
  simp only at this
  simp only [this]
  simp [Id.run, hLen]

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

private theorem nttLayer_eq_snd_arith {k : ℕ} (hk : k ≤ 7) :
  255 / (2 * 2 ^ (7 - k)) + 1 = 2 ^ k := by
  -- We simply brute force the proof by making a case disjunction on k
  -- TODO: the proof is quite simple but the theorem must be generalized (and the proof is then induction)
  repeat (cases k <;> simp_all <;> rename_i k <;> try omega)

private theorem nttLayer_eq_snd
  (f : Polynomial) (i k : Nat) (hk : k ≤ 7) :
  (Target.nttLayer f k i).snd = i + 2 ^ k := by
  unfold Target.nttLayer
  simp only [Id.run, Id.pure_eq, Id.bind_eq, Aeneas.SRRange.forIn_eq_forIn_range',
    Aeneas.SRRange.size, tsub_zero, Nat.succ_add_sub_one, Nat.ofNat_pos, mul_pos_iff_of_pos_left,
    pow_pos, Nat.add_div_right, List.forIn_yield_eq_foldl]
  have := nttLayer_eq_snd_aux f (fun x y => Target.nttLayerInner x k y) i
  simp only [this, add_right_inj]
  apply nttLayer_eq_snd_arith hk

private theorem nttLayer_eq_aux (f : Polynomial) (k : Nat) (len : Nat)
  (hk : k ≤ 7) (hLen : len = 2 ^ (7 - k)) :
  (nttLayer f i len 0 (by simp [hLen]), i + 2 ^ k) = Target.nttLayer f k i := by
  have := nttLayer_eq_fst f i k len hk hLen
  have := nttLayer_eq_snd f i k hk
  cases h: Target.nttLayer f k i
  simp_all

private theorem nttLayer_eq (f : Polynomial) (k : Nat)
  (hk : k ≤ 7) :
  (nttLayer f i (2 ^ (7 - k)) 0 (by simp), i + 2 ^ k) = Target.nttLayer f k i := by
  rw [nttLayer_eq_aux] <;> simp [*]

theorem nttEq (f : Polynomial) :
  ntt f = Target.ntt f := by
  unfold ntt Target.ntt
  simp only [Id.run, Id.pure_eq, Id.bind_eq, Std.Range.forIn_eq_forIn_range', Std.Range.size,
    tsub_zero, Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one, List.range', zero_add,
    List.forIn_yield_eq_foldl, List.foldl_cons, List.foldl_nil]
  repeat (rw [← nttLayer_eq] <;> simp)

end Symcrust.SpecAux
