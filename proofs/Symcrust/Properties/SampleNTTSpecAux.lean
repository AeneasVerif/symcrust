import Symcrust.Spec

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

noncomputable def Target.sampleNTT.loop (ctx : SHAKE128.Context) (a : Polynomial) (j : ℕ)
  : Option Polynomial :=
  let (ctx', C) := XOF.squeeze ctx 3
  let d1 := C[0].val + 256 * (C[1].val % 16)
  let d2 := C[1].val/16 + 16 * C[2].val
  if hj : j < 256 then
    if d1 < Q then
      let a1 := a.set j d1
      if h1 : d2 < Q ∧ j + 1 < 256 then
        let a2 := a1.set (j + 1) d2
        loop ctx' a2 (j + 2)
      else
        loop ctx' a1 (j + 1)
    else
      if h1 : d2 < Q ∧ j < 256 then
        let a1 := a.set j d2
        loop ctx' a1 (j + 1)
      else
        loop ctx' a j
  else a
partial_fixpoint

noncomputable def Target.sampleNTT (B : {l : List Byte // l.length = 34 }) : Option Polynomial :=
  sampleNTT.loop (XOF.absorb XOF.init B) Polynomial.zero 0

theorem Target.sampleNTT.eq_spec (B : {l : List Byte // l.length = 34 }) :
  ∀ r1 r2, sampleNTT B = some r1 → Spec.sampleNTT B = some r2 → r1 = r2 := by
  intro r1 r2
  unfold Spec.sampleNTT
  rw [forIn, instForInOptionOLoopUnit]
  simp only [Vector.Inhabited_getElem_eq_getElem!, Option.pure_def, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, ReduceZMod.reduceZMod, Vector.set_eq_set!, Option.bind_eq_bind,
    Option.bind_some]
  rw [OLoop.forIn]
  tlet inner_loop : Unit → MProd Polynomial (MProd SHAKE128.Context ℕ) →
    Option (ForInStep (MProd Polynomial (MProd SHAKE128.Context ℕ))) :=
    (fun x (r : MProd Polynomial (MProd SHAKE128.Context ℕ)) =>
      if h : r.snd.snd < 256 then
        if (XOF.squeeze r.snd.fst 3).2[0]!.val + 256 * ((XOF.squeeze r.snd.fst 3).2[1]!.val % 16) < Q then
          if h_1 :
              (XOF.squeeze r.snd.fst 3).2[1]!.val / 16 + 16 * (XOF.squeeze r.snd.fst 3).2[2]!.val < Q ∧
                r.snd.snd + 1 < 256 then
            some
              (ForInStep.yield
                ⟨(Vector.set! r.fst r.snd.snd
                        (↑(XOF.squeeze r.snd.fst 3).2[0]!.val +
                          256 * ↑((XOF.squeeze r.snd.fst 3).2[1]!.val % 16))).set!
                    (r.snd.snd + 1)
                    (↑((XOF.squeeze r.snd.fst 3).2[1]!.val / 16) + 16 * ↑(XOF.squeeze r.snd.fst 3).2[2]!.val),
                  (XOF.squeeze r.snd.fst 3).1, r.snd.snd + 1 + 1⟩)
          else
            some
              (ForInStep.yield
                ⟨Vector.set! r.fst r.snd.snd
                    (↑(XOF.squeeze r.snd.fst 3).2[0]!.val + 256 * ↑((XOF.squeeze r.snd.fst 3).2[1]!.val % 16)),
                  (XOF.squeeze r.snd.fst 3).1, r.snd.snd + 1⟩)
        else
          if h :
              (XOF.squeeze r.snd.fst 3).2[1]!.val / 16 + 16 * (XOF.squeeze r.snd.fst 3).2[2]!.val < Q ∧
                r.snd.snd < 256 then
            some
              (ForInStep.yield
                ⟨Vector.set! r.fst r.snd.snd
                    (↑((XOF.squeeze r.snd.fst 3).2[1]!.val / 16) + 16 * ↑(XOF.squeeze r.snd.fst 3).2[2]!.val),
                  (XOF.squeeze r.snd.fst 3).1, r.snd.snd + 1⟩)
          else some (ForInStep.yield ⟨r.fst, (XOF.squeeze r.snd.fst 3).1, r.snd.snd⟩)
      else some (ForInStep.done ⟨r.fst, r.snd.fst, r.snd.snd⟩))
  intro h1 h2
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
  rcases h2 with ⟨r3, h3, h2⟩
  revert h3
  rw [← h2]
  unfold sampleNTT at h1
  conv => rhs; rw [← Option.some_inj, ← h1]
  clear h1
  apply OLoop.forIn.loop.partial_correctness inner_loop (fun x r => loop x.2.1 x.1 x.2.2 = r.1)
  intro loop1 hloop1 b r ih
  simp only [ReduceZMod.reduceZMod, dite_eq_ite, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff, inner_loop] at ih
  rcases ih with ⟨inner_loop_res, h3, h4⟩
  split at h3
  . next hb =>
    split at h3
    . next h5 =>
      split at h3
      . next h6 =>
        simp only [ReduceZMod.reduceZMod, Option.some.injEq, inner_loop] at h3
        simp only [← h3, inner_loop] at h4
        specialize hloop1 ⟨(Vector.set! b.fst b.snd.snd
          (↑(XOF.squeeze b.snd.fst 3).2[0]!.val + 256 * ↑((XOF.squeeze b.snd.fst 3).2[1]!.val % 16))).set!
          (b.snd.snd + 1) (↑((XOF.squeeze b.snd.fst 3).2[1]!.val / 16) + 16 * ↑(XOF.squeeze b.snd.fst 3).2[2]!.val),
          (XOF.squeeze b.snd.fst 3).1, b.snd.snd + 1 + 1⟩ r h4
        rw [← hloop1]
        conv => lhs; unfold loop
        simp [*]
      . next h6 =>
        simp only [ReduceZMod.reduceZMod, Option.some.injEq, inner_loop] at h3
        simp only [← h3, inner_loop] at h4
        specialize hloop1 ⟨Vector.set! b.fst b.snd.snd
          (↑(XOF.squeeze b.snd.fst 3).2[0]!.val + 256 * ↑((XOF.squeeze b.snd.fst 3).2[1]!.val % 16)),
          (XOF.squeeze b.snd.fst 3).1, b.snd.snd + 1⟩ r h4
        simp only [ReduceZMod.reduceZMod, inner_loop] at hloop1
        rw [← hloop1]
        conv => lhs; unfold loop
        simp only [Vector.Inhabited_getElem_eq_getElem!, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          ReduceZMod.reduceZMod, Vector.set_eq_set!, dite_eq_ite, inner_loop]
        rw [ite_cond_eq_true _ _ (eq_true hb), ite_cond_eq_true _ _ (eq_true h5),
          ite_cond_eq_false _ _ (eq_false h6)]
    . next h5 =>
      split at h3
      . next h6 =>
        simp only [ReduceZMod.reduceZMod, Option.some.injEq, inner_loop] at h3
        simp only [← h3, inner_loop] at h4
        specialize hloop1 ⟨Vector.set! b.fst b.snd.snd
          (↑((XOF.squeeze b.snd.fst 3).2[1]!.val / 16) + 16 * ↑(XOF.squeeze b.snd.fst 3).2[2]!.val),
          (XOF.squeeze b.snd.fst 3).1, b.snd.snd + 1⟩ r h4
        simp only [ReduceZMod.reduceZMod, inner_loop] at hloop1
        rw [← hloop1]
        conv => lhs; unfold loop
        simp [*]
      . next h6 =>
        simp only [Option.some.injEq, inner_loop] at h3
        simp only [← h3, inner_loop] at h4
        rw [← hloop1 ⟨b.fst, (XOF.squeeze b.snd.fst 3).1, b.snd.snd⟩ r h4]
        simp only [inner_loop]
        conv => lhs; unfold loop
        simp only [Vector.Inhabited_getElem_eq_getElem!, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          ReduceZMod.reduceZMod, Vector.set_eq_set!, dite_eq_ite, inner_loop]
        rw [ite_cond_eq_true _ _ (eq_true hb), ite_cond_eq_false _ _ (eq_false h5),
          ite_cond_eq_false _ _ (eq_false h6)]
  . next hb =>
    simp only [Option.some.injEq, inner_loop] at h3
    simp only [← h3, Option.some.injEq, inner_loop] at h4
    rw [← h4]
    unfold loop
    simp [*]
