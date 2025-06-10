import Lean
import Aeneas

-- This file defines `brute`, a terminal tactic for brute force enumeration. It doesn't make sense to leave
-- this file here in the long term, but I am putting it here for now to make it easy to test on SymCrust proofs

open Lean Meta Parser Elab Tactic

initialize registerTraceClass `brute.debug

namespace Brute

def mkFold1 (f : Nat → Bool) (b : Nat) (acc : Bool) : Bool :=
  (List.range' 0 b).foldr
    (fun (x : Nat) (acc : Bool) => acc && f x) acc

def mkFold1' (b : Nat) (f : (x : Nat) → (hx : x < b) → Bool) (acc : Bool) : Bool :=
  Fin.foldr b
    (fun (x : Fin b) (acc : Bool) => acc && f x.1 x.2) acc

theorem ofMkFold1EqTrueAux (f : Nat → Bool) (b : Nat) (acc : Bool) :
  mkFold1 f b acc = (acc ∧ ∀ x < b, f x) := by
  simp only [mkFold1, eq_iff_iff]
  induction b generalizing acc
  . simp
  . next b ih =>
    simp only [List.range'_1_concat, Nat.zero_add, List.foldr_append, List.foldr_cons,
      List.foldr_nil, ih (acc && f b), Bool.and_eq_true]
    constructor
    . simp only [and_imp]
      intro hacc hfb hb
      constructor
      . exact hacc
      . intro x hx
        by_cases hxb : x = b
        . rw [hxb, hfb]
        . exact hb x (by omega)
    . simp only [and_imp]
      intro hacc h
      constructor
      . rw [hacc, h b (by omega), and_self]
      . intro x hxb
        exact h x (by omega)

theorem ofMkFold1EqTrue (f : Nat → Bool) (b : Nat) :
  mkFold1 f b true → ∀ x < b, f x := by simp only [ofMkFold1EqTrueAux f b true, true_and, imp_self]

theorem ofMkFold1'EqTrueAux (b : Nat) (f : (x : Nat) → (hx : x < b) → Bool) (acc : Bool) :
  mkFold1' b f acc = (acc ∧ ∀ x : Nat, ∀ hx : x < b, f x hx) := by
  simp only [mkFold1', eq_iff_iff]
  induction b generalizing acc
  . simp
  . next b ih =>
    let f' : (x : ℕ) → x < b → Bool := fun x hx => f x (by omega)
    simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
    rw [ih f' (acc && f b (by omega))]
    constructor
    . simp only [and_imp]
      intro h1 h2
      simp only [Bool.and_eq_true] at h1
      constructor
      . exact h1.1
      . intro x hx
        by_cases hxb : x = b
        . simp only [hxb, h1.2]
        . exact h2 x (by omega)
    . rintro ⟨h1, h2⟩
      simp only [Bool.and_eq_true, and_assoc]
      split_conjs
      . exact h1
      . exact h2 b (by omega)
      . intro x hx
        exact h2 x (by omega)

theorem ofMkFold1'EqTrue (b : Nat) (f : (x : Nat) → (hx : x < b) → Bool) :
  mkFold1' b f true → ∀ x : Nat, ∀ hx : x < b, f x hx := by
  simp only [ofMkFold1'EqTrueAux, true_and, imp_self]

def mkFold2 (f : Nat → Nat → Bool) (b1 : Nat) (b2 : Nat → Nat) (acc : Bool) : Bool :=
  (List.range' 0 b1).foldr (fun (x : Nat) (acc : Bool) => mkFold1 (f x) (b2 x) acc) acc

def mkFold2'' (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Bool)
  (acc : Bool) : Bool :=
  Fin.foldr b1 (fun (x : Fin b1) (acc : Bool) => mkFold1' (b2 x.1 x.2) (f x.1 x.2) acc) acc

theorem ofMkFold2EqTrueAux (f : Nat → Nat → Bool) (b1 : Nat) (b2 : Nat → Nat) (acc : Bool) :
  mkFold2 f b1 b2 acc = (acc ∧ ∀ x < b1, ∀ y < b2 x, f x y) := by
  simp only [mkFold2, eq_iff_iff]
  induction b1 generalizing acc
  . simp
  . next b1 ih1 =>
    simp only [List.range'_1_concat, Nat.zero_add, List.foldr_append, List.foldr_cons, List.foldr_nil]
    tlet acc' := mkFold1 (f b1) (b2 b1) acc
    rw [ih1 acc', ofMkFold1EqTrueAux (f b1) (b2 b1) acc]
    constructor
    . rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [h1, true_and]
      intro x hx y hy
      rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with x_lt_b1 | x_eq_b1
      . exact h3 x x_lt_b1 y hy
      . rw [x_eq_b1]
        rw [x_eq_b1] at hy
        exact h2 y hy
    . rintro ⟨h1, h2⟩
      constructor
      . simp only [h1, true_and]
        intro y hy
        exact h2 b1 (by omega) y hy
      . intro x hx y hy
        exact h2 x (by omega) y (by omega)

theorem ofMkFold2EqTrue (f : Nat → Nat → Bool) (b1 : Nat) (b2 : Nat → Nat) :
  mkFold2 f b1 b2 true → ∀ x < b1, ∀ y < (b2 x), f x y := by
  simp only [ofMkFold2EqTrueAux f b1 b2 true, true_and, imp_self]

theorem ofMkFold2''EqTrueAux (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Bool) (acc : Bool) :
  mkFold2'' b1 b2 f acc = (acc ∧ ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx, f x hx y hy) := by
  simp only [mkFold2'', eq_iff_iff]
  induction b1 generalizing acc
  . simp
  . next b1 ih1 =>
    simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
    tlet acc' := mkFold1' (b2 b1 (by omega)) (f b1 (by omega)) acc
    let b2' := fun (x : Nat) (hx : x < b1) => b2 x (by omega)
    let f' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2' x hx) => f x (by omega) y hy
    rw [ih1 b2' f' acc', ofMkFold1'EqTrueAux (b2 b1 (by omega)) (f b1 (by omega)) acc]
    constructor
    . rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [h1, true_and]
      intro x hx y hy
      rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with x_lt_b1 | x_eq_b1
      . exact h3 x x_lt_b1 y hy
      . simp only [x_eq_b1]
        simp only [x_eq_b1] at hy
        exact h2 y hy
    . rintro ⟨h1, h2⟩
      constructor
      . simp only [h1, true_and]
        intro y hy
        exact h2 b1 (by omega) y hy
      . intro x hx y hy
        exact h2 x _ y hy

theorem ofMkFold2''EqTrue (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Bool) :
  mkFold2'' b1 b2 f true → ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx, f x hx y hy := by
  simp only [ofMkFold2''EqTrueAux, true_and, imp_self]

def mkFold3 (f : Nat → Nat → Nat → Bool) (b1 : Nat) (b2 : Nat → Nat) (b3 : Nat → Nat → Nat) (acc : Bool) : Bool :=
  (List.range' 0 b1).foldr (fun (x : Nat) (acc : Bool) => mkFold2 (f x) (b2 x) (b3 x) acc) acc

def mkFold3'' (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Bool)
  (acc : Bool) : Bool :=
  Fin.foldr b1 (fun (x : Fin b1) (acc : Bool) => mkFold2'' (b2 x.1 x.2) (b3 x.1 x.2) (f x.1 x.2) acc) acc

theorem ofMkFold3EqTrueAux (f : Nat → Nat → Nat → Bool) (b1 : Nat) (b2 : Nat → Nat) (b3 : Nat → Nat → Nat)
  (acc : Bool) : mkFold3 f b1 b2 b3 acc = (acc ∧ ∀ x < b1, ∀ y < b2 x, ∀ z < b3 x y, f x y z) := by
  simp only [mkFold3, eq_iff_iff]
  induction b1 generalizing acc
  . simp
  . next b1 ih1 =>
    simp only [List.range'_1_concat, Nat.zero_add, List.foldr_append, List.foldr_cons, List.foldr_nil]
    tlet acc' := mkFold2 (f b1) (b2 b1) (b3 b1) acc
    rw [ih1 acc', ofMkFold2EqTrueAux (f b1) (b2 b1) (b3 b1) acc]
    constructor
    . rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [h1, true_and]
      intro x hx y hy
      rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with x_lt_b1 | x_eq_b1
      . exact h3 x x_lt_b1 y hy
      . rw [x_eq_b1]
        rw [x_eq_b1] at hy
        exact h2 y hy
    . rintro ⟨h1, h2⟩
      constructor
      . simp only [h1, true_and]
        intro y hy
        exact h2 b1 (by omega) y hy
      . intro x hx y hy
        exact h2 x (by omega) y (by omega)

theorem ofMkFold3EqTrue (f : Nat → Nat → Nat → Bool) (b1 : Nat) (b2 : Nat → Nat) (b3 : Nat → Nat → Nat) :
  mkFold3 f b1 b2 b3 true → ∀ x < b1, ∀ y < (b2 x), ∀ z < (b3 x y), f x y z := by
  simp only [ofMkFold3EqTrueAux f b1 b2 b3 true, true_and, imp_self]

theorem ofMkFold3''EqTrueAux (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Bool)
  (acc : Bool) : mkFold3'' b1 b2 b3 f acc = (acc ∧ ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx,
    ∀ z : Nat, ∀ hz : z < b3 x hx y hy, f x hx y hy z hz) := by
  simp only [mkFold3'', eq_iff_iff]
  induction b1 generalizing acc
  . simp
  . next b1 ih1 =>
    simp only [Fin.foldr_succ_last, Fin.coe_castSucc, Fin.val_last]
    tlet acc' := mkFold2'' (b2 b1 (by omega)) (b3 b1 (by omega)) (f b1 (by omega)) acc
    let b3' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2 x (by omega)) => b3 x (by omega) y hy
    let b2' := fun (x : Nat) (hx : x < b1) => b2 x (by omega)
    let f' := fun (x : Nat) (hx : x < b1) (y : Nat) (hy : y < b2' x hx) => f x (by omega) y hy
    rw [ih1 b2' b3' f' acc', ofMkFold2''EqTrueAux (b2 b1 (by omega)) (b3 b1 (by omega)) (f b1 (by omega)) acc]
    constructor
    . rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [h1, true_and]
      intro x hx y hy
      rcases Nat.lt_or_eq_of_le $ Nat.le_of_lt_succ hx with x_lt_b1 | x_eq_b1
      . exact h3 x x_lt_b1 y hy
      . simp only [x_eq_b1]
        simp only [x_eq_b1] at hy
        exact h2 y hy
    . rintro ⟨h1, h2⟩
      constructor
      . simp only [h1, true_and]
        intro y hy
        exact h2 b1 (by omega) y hy
      . intro x hx y hy
        exact h2 x _ y hy

theorem ofMkFold3''EqTrue (b1 : Nat) (b2 : (x : Nat) → (hx : x < b1) → Nat)
  (b3 : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → Nat)
  (f : (x : Nat) → (hx : x < b1) → (y : Nat) → (hy : y < b2 x hx) → (z : Nat) → (hz : z < b3 x hx y hy) → Bool) :
  mkFold3'' b1 b2 b3 f true → ∀ x : Nat, ∀ hx : x < b1, ∀ y : Nat, ∀ hy : y < b2 x hx,
    ∀ z : Nat, ∀ hz : z < b3 x hx y hy, f x hx y hy z hz := by
  simp only [ofMkFold3''EqTrueAux, true_and, imp_self]

/-- A terminal tactic that attempts to prove goals of the form `∀ x y z ..., f x y z ...` via brute force.
    Currently, `brute` only supports goals consisting of a string of universally quantified upper-bounded Nats
    (e.g. `∀ a < x₁, ∀ b < x₂ ...`) followed by a decidable function `f : Nat → ... → Nat → Bool`

    Currently, we only support goals exactly of the form `∀ x < d, f x` or `∀ x < d1, ∀ y < d2, f x y` -/
syntax (name := brute) "brute" : tactic

/-- If `b1 : Nat` and `b2 : b1 < d` then returns `some d`. Otherwise returns `none` -/
def popBoundBinders (b1 b2 : FVarId) : TacticM (Option Expr) := do
  let lctx ← getLCtx
  let some b1LocalDecl := lctx.find? b1
    | throwError "{decl_name%} :: Unable to find type of goal binder {Expr.fvar b1}"
  let some b2LocalDecl := lctx.find? b2
    | throwError "{decl_name%} :: Unable to find type of goal binder {Expr.fvar b2}"
  let b1Type := b1LocalDecl.type
  let b2Type := b2LocalDecl.type
  if b1Type != mkConst ``Nat then return none
  let b1UpperBound ←
    match b2Type with
    | .app (.app (.app (.app (.const ``LT.lt _) _) _) x) y =>
      if x != Expr.fvar b1 then return none
      else pure y
    | _ => return none
  return some b1UpperBound

/-- Recursively calls `popBoundBinders` as many times as `goalBinders` allows -/
def popAllBoundBinders (goalBinders : Array FVarId) (acc : Array (FVarId × FVarId × Expr)) :
  TacticM (Array (FVarId × FVarId × Expr)) := do
  match goalBinders with
  | ⟨b1 :: b2 :: restBinders⟩ =>
    let some b1UpperBound ← popBoundBinders b1 b2
      | return acc
    popAllBoundBinders ⟨restBinders⟩ $ acc.push (b1, b2, b1UpperBound)
  | _ => return acc

@[tactic brute]
def evalBrute : Tactic
| `(tactic| brute) => withMainContext do
  let pf ← forallTelescope (← getMainTarget) $ fun xs g => do
    let boundBinders ← popAllBoundBinders (xs.map Expr.fvarId!) #[]
    match boundBinders with
    | #[(x, hx, xBound)] =>
      let boundFVars := #[.fvar x, .fvar hx]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppM ``mkFold1' #[xBound, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let pf := mkApp3 (mkConst ``ofMkFold1'EqTrue) xBound f <|
        mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | #[(x, hx, xBound), (y, hy, yBound)] =>
      let boundFVars := #[.fvar x, .fvar hx, .fvar y, .fvar hy]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let yBound ← mkLambdaFVars #[Expr.fvar x, Expr.fvar hx] yBound
      let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppM ``mkFold2'' #[xBound, yBound, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let pf := mkApp4 (mkConst ``ofMkFold2''EqTrue) xBound yBound f <|
        mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | #[(x, hx, xBound), (y, hy, yBound), (z, hz, zBound)] =>
      let boundFVars := #[.fvar x, .fvar hx, .fvar y, .fvar hy, .fvar z, .fvar hz]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let yBound ← mkLambdaFVars #[.fvar x, .fvar hx] yBound
      let zBound ← mkLambdaFVars #[.fvar x, .fvar hx, .fvar y, .fvar hy] zBound
      let f ← mkLambdaFVars boundFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppM ``mkFold3'' #[xBound, yBound, zBound, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let pf := mkApp5 (mkConst ``ofMkFold3''EqTrue) xBound yBound zBound f <|
        mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | _ => throwError "Not yet implemented"
  trace[brute.debug] "pf: {pf}"
  trace[brute.debug] "pf type: {← inferType pf}"
  let g ← getMainGoal
  g.assign pf
| _ => throwUnsupportedSyntax

-- Both of these work with minimal delay and no stack overflow
example : ∀ n : Nat, n < 2^15 → n >>> 15 = 0 := by
  brute

example : ∀ n : Nat, n < 2^20 → n >>> 20 = 0 := by
  brute

example : ∀ n < 5, ∀ m < 6, n * m ≤ 20 := by
  brute

example : ∀ x < 5, ∀ y < x, ∀ z < x + y, x + y + z ≤ 100 := by
  brute

example : ∀ f : Fin 3 → Bool, ∀ x < 3, f x ∨ ¬f x := by
  decide +native

end Brute
