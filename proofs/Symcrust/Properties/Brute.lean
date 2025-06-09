import Lean

-- This file defines `brute`, a terminal tactic for brute force enumeration. It doesn't make sense to leave
-- this file here in the long term, but I am putting it here for now to make it easy to test on SymCrust proofs

open Lean Meta Parser Elab Tactic

namespace Brute

/-- A terminal tactic that attempts to prove goals of the form `∀ x y z ..., f x y z ...` via brute force.
    Currently, `brute` only supports goals consisting of a string of universally quantified upper-bounded Nats
    (e.g. `∀ a < x₁, ∀ b < x₂ ...`) followed by a decidable function `f : Nat → ... → Nat → Bool`

    Currently, we only support goals exactly of the form `∀ x < d, f x` -/
syntax (name := brute) "brute" : tactic

/-- If `goalBinders` has the form `#[(x : Nat), (h : x < d)]` then returns `d` -/
def popGoalBinders (goalBinders : Array FVarId) : TacticM Expr := do
  match goalBinders with
  | #[b1, b2] =>
    let lctx ← getLCtx
    let some b1LocalDecl := lctx.find? b1
      | throwError "{decl_name%} :: Unable to find type of goal binder {Expr.fvar b1}"
    let some b2LocalDecl := lctx.find? b2
      | throwError "{decl_name%} :: Unable to find type of goal binder {Expr.fvar b2}"
    let b1Type := b1LocalDecl.type
    let b2Type := b2LocalDecl.type
    if b1Type != mkConst ``Nat then throwError "{decl_name%} :: Wrong b1Type: {b1Type}"
    let b1UpperBound ←
      match b2Type with
      | .app (.app (.app (.app (.const ``LT.lt _) _) _) x) y =>
        if x != Expr.fvar b1 then
          throwError "{decl_name%} :: Second binder type does not have the form {Expr.fvar b1} < _: {b2Type}"
        else
          pure y
      | _ => throwError "{decl_name%} :: Wrong b2Type: {b2Type}"
    return b1UpperBound
  | _ => throwError "Wrong number of goal binders"

/-- Recursively calls `popGoalBinders` as many times as `goalBinders` allows -/
def popAllGoalBinders (goalBinders : Array FVarId) : TacticM (Array (FVarId × Expr)) := do
  match goalBinders with
  | ⟨b1 :: b2 :: restBinders⟩ =>
    try
      let b1UpperBound ← popGoalBinders #[b1, b2]
      return #[(b1, b1UpperBound)]
    catch _ =>
      throwError "Not implemented yet"
  | _ => throwError "Wrong number of goal binders"

def mkFold (f : Nat → Bool) (b : Nat) (acc : Bool) : Bool :=
  (List.range' 0 b).foldr
    (fun (x : Nat) (acc : Bool) => acc && f x) acc

theorem ofMkFoldEqTrueAux (f : Nat → Bool) (b : Nat) (acc : Bool) :
  mkFold f b acc = (acc ∧ ∀ x < b, f x) := by
  simp only [mkFold, eq_iff_iff]
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

theorem ofMkFoldEqTrue (f : Nat → Bool) (b : Nat) :
  mkFold f b true → ∀ x < b, f x := by simp only [ofMkFoldEqTrueAux f b true, true_and, imp_self]

@[tactic brute]
def evalBrute : Tactic
| `(tactic| brute) => withMainContext do
  let g ← getMainGoal
  let (goalBinders, g') ← g.intros
  g'.withContext do
    let #[(x, xBound)] ← popAllGoalBinders goalBinders
      | throwError "Unexpected output from popAllGoalBinders"
    let f ← mkLambdaFVars #[Expr.fvar x] (← mkDecide (← g'.getType))
    let res ← mkAppM ``mkFold #[f, xBound, mkConst ``true]

    let levels := (collectLevelParams {} res).params.toList
    let auxDeclName ← Term.mkAuxName `_brute
    let decl := Declaration.defnDecl {
      name := auxDeclName
      levelParams := levels
      type := mkConst ``Bool
      value := res
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl

    let rflPrf ← mkEqRefl (toExpr true)
    let levelParams := levels.map .param
    let pf := mkApp3 (mkConst ``ofMkFoldEqTrue) f xBound <|
      mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
    g'.assign $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf (goalBinders.map Expr.fvar)]
| _ => throwUnsupportedSyntax

-- Both of these work with minimal delay and no stack overflow
example : ∀ n : Nat, n < 2^15 → n >>> 15 = 0 := by
  brute

example : ∀ n : Nat, n < 2^20 → n >>> 20 = 0 := by
  brute

end Brute
