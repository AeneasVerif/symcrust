import Symcrust.Spec

#setup_aeneas_simps

namespace Symcrust.SpecAux

open Symcrust.Spec
open Aeneas Aeneas.SRRange

set_option maxHeartbeats 1000000

noncomputable def Target.sampleNTT.loop (ctx : SHAKE128.Context) (a : Polynomial) (j : ℕ)
  (hj : j < 256) : Option Polynomial :=
  let (ctx', C) := XOF.squeeze ctx 3
  let d1 := C[0].val + 256 * (C[1].val % 16)
  let d2 := C[1].val/16 + 16 * C[2].val
  if d1 < Q then
    let a1 := a.set j d1
    if h1 : d2 < Q ∧ j + 1 < 256 then
      let a2 := a1.set (j + 1) d2
      if h2 : j + 2 < 256 then loop ctx' a2 (j + 2) (by omega)
      else a2
    else
      if h2 : j + 1 < 256 then loop ctx' a1 (j + 1) (by omega)
      else a1
  else
    if h1 : d2 < Q ∧ j < 256 then
      let a1 := a.set j d2
      if h2 : j + 1 < 256 then loop ctx' a1 (j + 1) (by omega)
      else a1
    else
      loop ctx' a j (by omega)
partial_fixpoint

noncomputable def Target.sampleNTT (B : {l : List Byte // l.length = 34 }) : Option Polynomial :=
  sampleNTT.loop (XOF.absorb XOF.init B) Polynomial.zero 0 (by omega)

#check Option.some_inj

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
  have ih := OLoop.forIn.loop.partial_correctness inner_loop
    (fun x r => ∀ hx : x.2.2 < 256, loop x.2.1 x.1 x.2.2 hx = r.1)
  conv at ih => rhs; rhs; rhs; rw [forall_comm]
  apply ih
  clear ih
  intro loop1 hloop1 b r ih hb
  simp only [ReduceZMod.reduceZMod, dite_eq_ite, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff, inner_loop] at ih
  rcases ih with ⟨inner_loop_res, h3, h4⟩
  split at h3
  . next hb =>
    split at h3
    . sorry
    . next h5 =>
      split at h3
      . next h6 =>
        simp only [ReduceZMod.reduceZMod, Option.some.injEq, inner_loop] at h3
        simp only [← h3, inner_loop] at h4
        specialize hloop1 ⟨Vector.set! b.fst b.snd.snd
          (↑((XOF.squeeze b.snd.fst 3).2[1]!.val / 16) + 16 * ↑(XOF.squeeze b.snd.fst 3).2[2]!.val),
          (XOF.squeeze b.snd.fst 3).1, b.snd.snd + 1⟩ r h4
        simp only [ReduceZMod.reduceZMod, inner_loop] at hloop1
        -- Not sure that it's possible to prove `hloop1`'s `hx`. And upon further consideration,
        -- I don't know if `Target.sampleNTT.loop` should take `hj` as an argument (as opposed to
        -- checking whether `j < 256` at the beginning and immediately returning `a` if it isn't)
        sorry
      . next h6 =>
        simp only [Option.some.injEq, inner_loop] at h3
        simp only [← h3, inner_loop] at h4
        rw [← hloop1 ⟨b.fst, (XOF.squeeze b.snd.fst 3).1, b.snd.snd⟩ r h4 (by omega)]
        simp only [inner_loop]
        conv => lhs; unfold loop
        simp only [Vector.Inhabited_getElem_eq_getElem!, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          ReduceZMod.reduceZMod, Vector.set_eq_set!, dite_eq_ite, inner_loop]
        rw [ite_cond_eq_false _ _ (by simp [h5]), ite_cond_eq_false _ _ (by simp [h6])]
  . sorry

  /-

  have ih := OLoop.forIn.loop.partial_correctness inner_loop
    (fun x r => /- x.1 = Polynomial.zero → x.2.1 = XOF.absorb XOF.init ↑B → x.2.2 = 0 → -/ r1 = r.1)
  -- conv at ih => rhs; rhs; rhs; rw [forall_comm]; rhs; rw [forall_comm]; rhs; rw [forall_comm]
  apply ih <;> try simp only
  intro loop1 hloop1 b r ih -- hb1 hb2 hb3
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at ih
  rcases ih with ⟨inner_loop_res, h3, h4⟩
  split at h4
  . next b2 =>
    simp only [Option.some.injEq] at h4
    rw [← h4]
    clear h4 r
    unfold sampleNTT at h1
    revert h1
    -- Attempting `apply Target.sampleNTT.loop.partial_correctness (fun x a j hj r => r = b2.1)`
    -- here fails because `x`, `a`, `j`, `hj`, and `r` aren't correctly related to `b`
    have ih := Target.sampleNTT.loop.partial_correctness
      (fun x a j hj r => b.1 = a → b.2.1 = x → b.2.2 = j → r = b2.1)
    conv at ih =>
      rhs; rhs; rhs; rhs; rhs; rhs; rw [forall_comm]; rhs; rw [forall_comm]; rhs; rw [forall_comm]
    apply ih
    . sorry
    . sorry
    . sorry
    . sorry
  . apply hloop1 <;> assumption

  /- This code works and is promising, but I need to modify the motive to constraint `x`
  apply OLoop.forIn.loop.partial_correctness inner_loop (fun x r => r1 = r.1)
  intro loop1 hloop1 b r ih
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at ih
  rcases ih with ⟨inner_loop_res, h3, h4⟩
  split at h4
  . next b2 =>
    simp only [Option.some.injEq] at h4
    rw [← h4]
    clear h4 r
    unfold sampleNTT at h1
    revert h1
    -- Attempting `apply Target.sampleNTT.loop.partial_correctness (fun x a j hj r => r = b2.1)`
    -- here fails because `x`, `a`, `j`, `hj`, and `r` aren't correctly related to `b`
    have ih := Target.sampleNTT.loop.partial_correctness
      (fun x a j hj r => b.1 = a → b.2.2 = j → r = b2.1)
    conv at ih => rhs; rhs; rhs; rhs; rhs; rhs; rw [forall_comm]; rhs; rw [forall_comm]
    apply ih
    . sorry
    . sorry
    . sorry

    /-
    apply Target.sampleNTT.loop.partial_correctness (fun x a j hj r => r = b2.1)
    intro loop2 hloop2 ctx a j hj r ih
    simp only [Vector.Inhabited_getElem_eq_getElem!, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      ReduceZMod.reduceZMod, Vector.set_eq_set!, dite_eq_ite] at ih
    split at ih
    . next h4 =>
      sorry
    . next h4 =>
      split at ih
      . split at ih
        . next h5 hj' =>
          exact hloop2 (XOF.squeeze ctx 3).1 _ (j + 1) hj' r ih
        . next h5 hj' =>
          simp only [ReduceZMod.reduceZMod, Option.some.injEq] at ih
          rw [← ih]
          simp only [ReduceZMod.reduceZMod, dite_eq_ite, inner_loop] at h3
          split at h3
          . next h6 =>
            split at h3
            . next h7 =>
              split at h3
              . simp at h3
              . simp at h3
            . next h7 =>
              split at h3
              . simp at h3
              . simp at h3
          . next h6 =>
            simp only [Option.some.injEq, ForInStep.done.injEq, inner_loop] at h3
            simp only [ReduceZMod.reduceZMod, ← h3, inner_loop]
            -- Note that `hj` gives `j < 256` but `h6` gives `¬(b.2.2 < 256)`. I think I may need
            -- to derive a contradiction from these facts
            sorry
      . exact hloop2 (XOF.squeeze ctx 3).1 a j hj r ih
      -/
  . next b2 =>
    exact hloop1 b2 r h4
  -/
  -/

#check forall_comm
