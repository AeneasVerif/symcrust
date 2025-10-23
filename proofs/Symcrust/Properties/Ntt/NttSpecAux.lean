import Symcrust.Spec
import Symcrust.Properties.Polynomials

/-!
An auxiliary specification that we use to prove a refinement result.
This specification refines the specification in `Spec`, and is refined by the code.
It does not need to be trusted.
-/

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas.SRRange

-- TODO: move
@[simp] theorem MProd_mk_eq (x : MProd α β) : ⟨ x.fst, x.snd ⟩ = x := by simp only


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
      f := f.set! (j + len) (f[j]! - t)
      f := f.set! j (f[j]! + t)
    pure f

  def nttLayer (f : Polynomial) (i len : Nat) (hLen : 0 < len := by assumption) :
    MProd Polynomial Nat := Id.run do
    let mut f := f
    let mut i := i
    for start in [0:256:2*len] do
      let i0 := i
      i := i + 1
      f := nttLayerInner f i0 len start
    pure ⟨ f, i ⟩

  def ntt (f : Polynomial) : Polynomial := Id.run do
    let mut fi := ⟨ f, 1 ⟩
    for h: len in [128 : >1 : /= 2] do
      fi := nttLayer fi.1 fi.2 len (by simp [Membership.mem] at *; omega)
    pure fi.1

  theorem ntt_eq (f : Polynomial) : ntt f = Spec.ntt f := by
    rw [ntt, Spec.ntt]
    unfold nttLayer
    unfold nttLayerInner
    simp only [MProd_mk_eq, bind_pure_comp, map_pure, forIn_eq_forIn_range', size,
      add_tsub_cancel_left, add_tsub_cancel_right, Nat.div_one, List.forIn_pure_yield_eq_foldl,
      bind_pure, Id.run_pure, tsub_zero, Nat.succ_add_sub_one, forIn'_eq_forIn,
      Aeneas.DivRange.forIn_eq_forIn_divRange, Nat.one_lt_ofNat,
      Aeneas.DivRange.foldl_divRange_foldWhile, Aeneas.DivRange.foldWhile_step, Nat.reduceDiv,
      ne_eq, Nat.add_eq_left, OfNat.ofNat_ne_zero, not_false_eq_true, Vector.getElem!_set!_ne,
      Nat.reduceMul, Nat.reduceAdd, List.range'_one, List.foldl_cons, List.foldl_nil, Nat.ofNat_pos,
      Nat.div_self, lt_self_iff_false, Aeneas.DivRange.foldWhile_id,
      Vector.Inhabited_getElem_eq_getElem!, Vector.set_eq_set!]

  def invNttLayerInner (f : Polynomial) (i len start : Nat) : Polynomial := Id.run do
    let mut f := f
    let zeta := ζ ^(bitRev 7 i)
    for j in [start:start+len] do
      let t := f[j]!
      f := f.set! j (t + f[j + len]!)
      f := f.set! (j + len) (zeta * (f[j + len]! - t))
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
    simp only [bind_pure_comp, map_pure, forIn_eq_forIn_range', size, add_tsub_cancel_left,
      add_tsub_cancel_right, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure,
      tsub_zero, Nat.succ_add_sub_one, Aeneas.ReduceZMod.reduceZMod, MProd_mk_eq,
      Vector.Inhabited_getElem_eq_getElem!, Vector.set_eq_set!, forIn'_eq_forIn,
      Aeneas.MulRange.forIn_eq_forIn_MulRange, Aeneas.MulRange.foldl_MulRange_foldWhile,
      Nat.reduceLT, Aeneas.MulRange.foldWhile_step, Nat.reduceMul, ne_eq, Nat.left_eq_add,
      OfNat.ofNat_ne_zero, not_false_eq_true, Vector.getElem!_set!_ne, Nat.reduceAdd, Nat.reduceDiv,
      List.range'_one, List.foldl_cons, List.foldl_nil, lt_self_iff_false,
      Aeneas.MulRange.foldWhile_id]

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
    let f := f.set! (start + j) (c0 + c1 * zeta)
    let f := f.set! (start + j + len) (c0 - c1 * zeta)
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
    let f := f.set! (start + j) (c0 + c1)
    let f := f.set! (start + j + len) (zeta * (c1 - c0))
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

/-- Auxiliary helper -/
private def nttLayerInner_body (i len start : Nat) (f : Polynomial) (j : Nat) : Polynomial :=
  let c0 := f[start + j]!
  let c1 := f[start + j + len]!
  let zeta := ζ ^ bitRev 7 i
  let f := f.set! (start + j) (c0 + c1 * zeta)
  let f := f.set! (start + j + len) (c0 - c1 * zeta)
  f

private theorem nttLayerInner_eq
  (f : Polynomial) (i len start : Nat) :
  nttLayerInner f i len start 0 = Target.nttLayerInner f i len start
  := by
  have := eq_foldWhile len 1 (by simp) (fun f j => nttLayerInner f i len start j)
    (nttLayerInner_body i len start) 0 f
    (by intro f i
        simp [nttLayerInner_body]
        conv => lhs; unfold nttLayerInner)
  simp at this
  rw [this]; clear this
  unfold Target.nttLayerInner
  simp only [bind_pure_comp, map_pure, forIn_eq_forIn_range', size, add_tsub_cancel_left,
    add_tsub_cancel_right, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
  simp only [zero_lt_one, foldl_range'_eq_foldWhile, mul_one]
  conv => rhs; rw [foldWhile_shift_start]
  have : start + len - start = len := by omega
  rw [this]; clear this
  apply foldWhile_forall_eq_imp_eq
  intro f i h0 h1
  simp only [nttLayerInner_body]
  simp_lists
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
  -- TODO: the proof is quite simple but the theorem must be generalized (and the proof is then by induction)
  replace ⟨ k, hLen ⟩ := hLen
  repeat (cases k <;> simp_all <;> rename_i k <;> try omega)

private theorem nttLayer_eq_fst (f : Polynomial) (i len : Nat)
  (hLen : 0 < len) (hkLen : ∃ k, k ≤ 7 ∧ len = 2 ^ k) :
  nttLayer f i len 0 hLen = (Target.nttLayer f i len).fst := by
  unfold Target.nttLayer
  simp only [bind_pure_comp, map_pure, forIn_eq_forIn_range', size, tsub_zero, Nat.succ_add_sub_one,
    List.forIn_pure_yield_eq_foldl, MProd_mk_eq, bind_pure, Id.run_pure]
  simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, hLen, Nat.add_div_right,
    foldl_range'_eq_foldWhile, zero_add]
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
  simp only [bind_pure_comp, map_pure, forIn_eq_forIn_range', size, tsub_zero, Nat.succ_add_sub_one,
    List.forIn_pure_yield_eq_foldl, MProd_mk_eq, bind_pure, Id.run_pure]
  simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, hLen, Nat.add_div_right]
  have := nttLayer_eq_snd_aux f (fun x y => Target.nttLayerInner x y len) i
  simp only [this]
  ring_nf

private theorem nttLayer_eq_aux (f : Polynomial) (i len : Nat)
  (hLen : 0 < len) (hkLen : ∃ k, k ≤ 7 ∧ len = 2 ^ k) :
  ⟨ nttLayer f i len 0 (by simp [hLen]), i + 255 / (2 * len) + 1 ⟩ = Target.nttLayer f i len := by
  have := nttLayer_eq_fst f i len hLen
  have := nttLayer_eq_snd f i len hLen
  cases h: Target.nttLayer f i len
  simp_all

private theorem nttLayer_eq (f : Polynomial) (len : Nat) (hLen : 0 < len)
  (hkLen : len = 2 ^ (Nat.log2 len) ∧ Nat.log2 len ≤ 7) :
  ⟨ nttLayer f i len 0 hLen, i + 255 / (2 * len) + 1 ⟩ = Target.nttLayer f i len := by
  rw [nttLayer_eq_aux]
  exists len.log2
  tauto

private theorem ntt_eq_target (f : Polynomial) :
  ntt f = Target.ntt f := by
  unfold ntt Target.ntt
  simp only [bind_pure_comp, map_pure, Aeneas.DivRange.forIn'_eq_forIn_divRange,
    List.forIn'_pure_yield_eq_foldl, Id.run_pure]
  simp only [Aeneas.divRange, Nat.reduceAdd, Aeneas.divRange.loop, gt_iff_lt, Nat.one_lt_ofNat,
    ↓dreduceIte, Nat.reduceDiv, lt_self_iff_false, List.attach_cons, List.attach_nil, List.map_nil,
    List.map_cons, List.foldl_cons, List.foldl_nil]
  repeat (rw [← nttLayer_eq] <;> simp only [Nat.log2, ge_iff_le, Nat.reduceLeDiff, ↓reduceIte,
    Nat.reduceDiv, le_refl, Nat.ofNat_pos, Nat.div_self, Nat.not_ofNat_le_one, zero_add,
    Nat.reduceAdd, Nat.reducePow, and_self])

/-- This is the important theorem -/
theorem ntt_eq (f : Polynomial) :
  ntt f = Spec.ntt f := by
  rw [ntt_eq_target, Target.ntt_eq]

/-!
# The proofs about the NTT⁻¹
-/

/-- Auxiliary helper -/
def invNttLayerInner_body (i len start : Nat) (f : Polynomial) (j : Nat) : Polynomial :=
  let c0 := f[start + j]!
  let c1 := f[start + j + len]!
  let zeta := ζ ^ bitRev 7 i
  let f := f.set! (start + j) (c0 + c1)
  let f := f.set! (start + j + len) (zeta * (c1 - c0))
  f

private theorem invNttLayerInner_eq
  (f : Polynomial) (i len start : Nat) :
  invNttLayerInner f i len start 0 = Target.invNttLayerInner f i len start
  := by
  have := eq_foldWhile len 1 (by simp) (fun f j => invNttLayerInner f i len start j)
    (invNttLayerInner_body i len start) 0 f
    (by intro f i
        simp [invNttLayerInner_body]
        conv => lhs; unfold invNttLayerInner)
  simp at this
  rw [this]; clear this
  unfold Target.invNttLayerInner
  simp only [bind_pure_comp, map_pure, forIn_eq_forIn_range', size, add_tsub_cancel_left,
    add_tsub_cancel_right, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
  simp only [zero_lt_one, foldl_range'_eq_foldWhile, mul_one]
  conv => rhs; rw [foldWhile_shift_start]
  have : start + len - start = len := by omega
  rw [this]; clear this
  apply foldWhile_forall_eq_imp_eq
  intro f i h0 h1
  simp only [invNttLayerInner_body]
  simp_lists
  ring_nf

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
  -- TODO: the proof is quite simple but the theorem must be generalized (and the proof is then by induction)
  replace ⟨ k, hLen ⟩ := hLen
  repeat (cases k <;> simp_all <;> rename_i k <;> try omega)

private theorem invNttLayer_eq_fst (f : Polynomial) (i len : Nat)
  (hLen : 0 < len) (hkLen : ∃ k, k ≤ 7 ∧ len = 2 ^ k) :
  invNttLayer f i len 0 hLen = (Target.invNttLayer f i len).fst := by
  unfold Target.invNttLayer
  simp only [bind_pure_comp, map_pure, forIn_eq_forIn_range', size, tsub_zero, Nat.succ_add_sub_one,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, hLen, Nat.add_div_right,
    foldl_range'_eq_foldWhile, zero_add]
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
  simp only [bind_pure_comp, map_pure, forIn_eq_forIn_range', size, tsub_zero, Nat.succ_add_sub_one,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, hLen, Nat.add_div_right]
  have := invNttLayer_eq_snd_aux f (fun x y => Target.invNttLayerInner x y len) i
  simp only [this]

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
  simp only [Aeneas.ReduceZMod.reduceZMod, bind_pure_comp, map_pure,
    Aeneas.MulRange.forIn'_eq_forIn_MulRange, List.forIn'_pure_yield_eq_foldl, Id.run_pure]
  -- Unfold the `mulRange`
  simp only [Aeneas.ReduceZMod.reduceZMod, List.attach, Aeneas.mulRange, Nat.reduceLT, ↓reduceIte,
    Nat.reduceMul, lt_self_iff_false, List.attachWith_cons, List.attachWith_nil, List.foldl_cons,
    List.foldl]
  repeat (rw [← invNttLayer_eq] <;> try simp only [Nat.log2, ge_iff_le, Nat.reduceLeDiff,
    ↓reduceIte, Nat.reduceDiv, le_refl, Nat.ofNat_pos, Nat.div_self, Nat.not_ofNat_le_one, zero_add,
    Nat.reduceAdd, Nat.reducePow, and_self])

/-- This is the important theorem -/
theorem invNtt_eq (f : Polynomial) :
  invNtt f = Spec.invNtt f := by
  rw [invNtt_eq_target, Target.invNtt_eq]

/-!
# Multiply NTTs
-/

/-- Auxiliary helper -/
def baseCaseMultiply0 (f g : Polynomial) (i : Nat) : Zq :=
  let a0 := f[2 * i]!
  let a1 := f[2 * i + 1]!
  let b0 := g[2 * i]!
  let b1 := g[2 * i + 1]!
  let γ := ζ^(2 * bitRev 7 i + 1)
  a0 * b0 + a1 * b1 * γ

/-- Auxiliary helper -/
def baseCaseMultiply1 (f g : Polynomial) (i : Nat) : Zq :=
  let a0 := f[2 * i]!
  let a1 := f[2 * i + 1]!
  let b0 := g[2 * i]!
  let b1 := g[2 * i + 1]!
  a0 * b1 + a1 * b0

private theorem baseCaseMultiply_eq (f g : Polynomial) (i : Nat) :
  baseCaseMultiply f[2 * i]! f[2 * i + 1]! g[2 * i]! g[2 * i + 1]! (ζ^(2 * bitRev 7 i + 1)) =
  (baseCaseMultiply0 f g i, baseCaseMultiply1 f g i) := by
  simp [baseCaseMultiply, baseCaseMultiply0, baseCaseMultiply1]

/-- The definition we will use in the proofs of refinement with the code -/
def multiplyNTTs (f g h : Polynomial) (i : Nat) : Polynomial :=
  if i < 128 then
    let c0 := baseCaseMultiply0 f g i
    let c1 := baseCaseMultiply1 f g i
    let h := h.set! (2 * i) (h[2 * i]! + c0)
    let h := h.set! (2 * i + 1) (h[2 * i + 1]! + c1)
    multiplyNTTs f g h (i + 1)
  else h

/-- The important equation which allows reasoning about `multiplyNTTs` -/
private theorem multiplyNTTs_getElem! (f g h : Polynomial) (i j : Nat) (hj : j < 128) :
  (multiplyNTTs f g h i)[2 * j]! = (if j < i then h[2 * j]! else h[2 * j]! + baseCaseMultiply0 f g j) ∧
  (multiplyNTTs f g h i)[2 * j + 1]! = (if j < i then h[2 * j + 1]! else h[2 * j + 1]! + baseCaseMultiply1 f g j) := by
  unfold multiplyNTTs
  simp
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
    let h := h.set! (2 * i) c0
    let h := h.set! (2 * i + 1) c1
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
    h := h.set! (2 * i) c0
    h := h.set! (2 * i + 1) c1
  pure h

/--
Linking `Target.multiplyNTTs` to `Spec.multiplyNTTs`
-/
private theorem Target.multiplyNTTs_inner_eq_spec (f g : Polynomial) :
  Target.multiplyNTTs_inner f g Polynomial.zero 0 = Spec.multiplyNTTs f g := by
  unfold Target.multiplyNTTs_inner Spec.multiplyNTTs
  simp only
  simp only [bind_pure_comp, map_pure, Std.Range.forIn_eq_forIn_range', Std.Range.size, tsub_zero,
    Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure,
    Id.run_pure, Vector.Inhabited_getElem_eq_getElem!, Vector.set_eq_set!, forIn'_eq_forIn,
    forIn_eq_forIn_range', size]

/--
Linking `Target.multiplyNTTs` to `multiplyNTTs_pure`
-/
private theorem Target.multiplyNTTs_inner_eq (f g : Polynomial) :
  Target.multiplyNTTs_inner f g Polynomial.zero 0 = multiplyNTTs_pure f g Polynomial.zero 0 := by
  unfold Target.multiplyNTTs_inner
  simp only [bind_pure_comp, map_pure, Std.Range.forIn_eq_forIn_range', Std.Range.size, tsub_zero,
    Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one, List.forIn_pure_yield_eq_foldl, bind_pure,
    Id.run_pure]
  simp only [zero_lt_one, foldl_range'_eq_foldWhile, mul_one, zero_add]
  -- Using a useful equation satisfied by `foldWhile`
  rw [← eq_foldWhile]
  intro h i
  conv => lhs; unfold multiplyNTTs_pure

private theorem multiplyNTTs_eq_multiplyNTTs_pure (f g : Polynomial) :
  multiplyNTTs f g Polynomial.zero 0 = multiplyNTTs_pure f g Polynomial.zero 0 := by
  simp only [Polynomial.eq_iff']
  intro i hi
  simp_lists [multiplyNTTs_getElem!, multiplyNTTs_pure_getElem!]

private theorem multiplyNTTs_add_zero (f g h : Polynomial) :
  multiplyNTTs f g h 0 = multiplyNTTs f g Polynomial.zero 0 + h := by
  simp only [Polynomial.eq_iff']
  intro i hi
  simp_lists [multiplyNTTs_getElem!, multiplyNTTs_pure_getElem!]
  simp only [not_lt_zero', ↓reduceIte]
  ring_nf
  simp only [and_self]

theorem multiplyNTTs_eq (f g h : Polynomial) :
  multiplyNTTs f g h 0 = Spec.multiplyNTTs f g + h := by
  rw [multiplyNTTs_add_zero]
  rw [multiplyNTTs_eq_multiplyNTTs_pure]
  rw [← Target.multiplyNTTs_inner_eq_spec]
  rw [Target.multiplyNTTs_inner_eq]

end Symcrust.SpecAux
