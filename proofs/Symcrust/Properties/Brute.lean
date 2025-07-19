import Lean
import Aeneas
import Symcrust.Properties.BruteLemmas

-- This file defines `brute`, a terminal tactic for brute force enumeration. It doesn't make sense to leave
-- this file here in the long term, but I am putting it here for now to make it easy to test on SymCrust proofs

open Lean Meta Parser Elab Tactic Aeneas Aeneas.Std

initialize registerTraceClass `brute.debug

namespace Brute

/-- A terminal tactic that attempts to prove goals of the form `∀ x y z ..., f x y z ...` via brute force.
    Currently, `brute` only supports goals consisting of a string of universally quantified upper-bounded Nats
    (e.g. `∀ a < x₁, ∀ b < x₂ ...`) followed by a decidable function `f : Nat → ... → Nat → Bool`

    Currently, we only support goals with at most four bounded Nats.

    **TODO** Add comment about the restriction on dependently-typed goals (e.g. goals of the form
    `∀ x, ∀ hx : x < b, p hx`)

    **TODO** Add comment about the restriction on NatLike types (can't have dependencies between the universally
    quantified NatLike types (e.g. `∀ n : Nat, n < b → ∀ y : BitVec n, ...`)) -/
syntax (name := brute) "brute" : tactic

/-- A structure that holds info for binders of the form `∀ x < b, ...`-/
structure BinderInfo where
  x : FVarId -- The universally quantified variable
  b : Expr -- The value that the variable is upper bounded by
  hxb : FVarId -- The variable whose type is `x < b`
  isNatLikeInst : Expr -- An Expr whose type is `IsNatLike t` where `x : t` and `b : t`

instance : ToMessageData BinderInfo where
  toMessageData := fun ⟨x, b, hxb, isNatLikeInst⟩ => m!"({Expr.fvar x}, {b}, {Expr.fvar hxb}, {isNatLikeInst})"

/-- A helper definition to make it easier to construct the type of `IsNatLike`'s β type -/
def IsNatLikeβType (t : Type) :=
  PSum
    (PSigma (fun n : Nat => t = BitVec n))
    (PSigma (fun t' : UScalarTy => t' ≠ UScalarTy.Usize ∧ t = UScalar t'))

/-- A helper definition to make it easier to construct the type of `IsNatLike`'s ββ type -/
def IsNatLikeββType (t : Type) := PSigma (fun t' : UScalarTy => t' ≠ UScalarTy.Usize ∧ t = UScalar t')

/-- If `t` is an Expr corresponding to `Nat`, `BitVec n`, or `UScalar t'`, then `getIsNatLike` returns
    an Expr whose type is `IsNatLike t`. Otherwise, `getIsNatLike` returns `none`. -/
def getIsNatLikeInstance (t : Expr) : MetaM (Option Expr) := do
  match t with
  | .const ``Nat _ =>
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    let pSumβ ← mkAppM ``IsNatLikeβType #[t]
    let pSumPf ← mkAppOptM ``PSum.inl #[none, some pSumβ, rflPf]
    let inst ← mkAppM ``IsNatLike.mk #[pSumPf]
    return some inst
  | .app (.const ``BitVec _) n =>
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    let pSigmaβBody :=
      mkApp3 (mkConst ``Eq [2]) (.sort 1) (.app (.const ``BitVec []) n) (.app (.const ``BitVec []) (.bvar 0))
    let pSigmaβ := Expr.lam `n (mkConst ``Nat) pSigmaβBody .default
    let pSigmaPf ← mkAppOptM ``PSigma.mk #[none, some pSigmaβ, n, rflPf]
    let pInnerSumβ ← mkAppM ``IsNatLikeββType #[t]
    let pInnserSumPf ← mkAppOptM ``PSum.inl #[none, some pInnerSumβ, pSigmaPf]
    let pSumα ← mkAppM ``Eq #[t, mkConst ``Nat]
    let pSumPf ← mkAppOptM ``PSum.inr #[some pSumα, none, pInnserSumPf]
    let inst ← mkAppM ``IsNatLike.mk #[pSumPf]
    return some inst
  | _ => return none -- **TODO** UScalar support

/-- If `b1` has a NatLike type and `b2 : b1 < d` then returns a `BinderInfo` corresponding to
    `b1`, `b1`'s Natlike type, and `b2`. Otherwise returns `none` -/
def popBoundBinders (b1 b2 : FVarId) : TacticM (Option BinderInfo) := do
  let lctx ← getLCtx
  let some b1LocalDecl := lctx.find? b1
    | throwError "{decl_name%} :: Unable to find type of goal binder {Expr.fvar b1}"
  let some b2LocalDecl := lctx.find? b2
    | throwError "{decl_name%} :: Unable to find type of goal binder {Expr.fvar b2}"
  let b1Type := b1LocalDecl.type
  let b2Type := b2LocalDecl.type
  let some isNatLikeInst ← getIsNatLikeInstance b1Type
    | return none -- Don't pop any binders if `b1`
  let b1UpperBound ←
    match b2Type with
    | .app (.app (.app (.app (.const ``LT.lt _) _) _) x) y =>
      if x != Expr.fvar b1 then return none
      else pure y
    | _ => return none
  return some ⟨b1, b1UpperBound, b2, isNatLikeInst⟩

/-- Recursively calls `popBoundBinders` as many times as `goalBinders` allows -/
def popAllBoundBinders (goalBinders : Array FVarId) (acc : Array BinderInfo) : TacticM (Array BinderInfo) := do
  match goalBinders with
  | ⟨b1 :: b2 :: restBinders⟩ =>
    let some binderInfo ← popBoundBinders b1 b2
      | return acc
    popAllBoundBinders ⟨restBinders⟩ $ acc.push binderInfo
  | _ => return acc

@[tactic brute]
def evalBrute : Tactic
| `(tactic| brute) => withMainContext do
  let pf ← forallTelescope (← getMainTarget).consumeMData (cleanupAnnotations := true) $ fun xs g => do
    trace[brute.debug] "xs: {xs}, g: {g}"
    let boundBinders ← popAllBoundBinders (xs.map Expr.fvarId!) #[]
    match boundBinders with
    | #[⟨x, b, hxb, inst⟩] =>
      let boundFVars := #[.fvar x, .fvar hxb]
      let natLikeFVars := #[.fvar x]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let f ← mkLambdaFVars natLikeFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppOptM ``mkFold1 #[none, some inst, b, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let foldResPf := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      let pf ← mkAppOptM ``ofMkFold1EqTrue #[none, some inst, b, f, foldResPf]
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | #[⟨x, b1, hxb1, inst1⟩, ⟨y, b2, hyb2, inst2⟩] =>
      let boundFVars := #[.fvar x, .fvar hxb1, .fvar y, .fvar hyb2]
      let natLikeFVars := #[.fvar x, .fvar y]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let b2 ← mkLambdaFVars #[.fvar x] b2
      let f ← mkLambdaFVars natLikeFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppOptM ``mkFold2 #[none, none, inst1, inst2, b1, b2, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let foldResPf := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      let pf ← mkAppOptM ``ofMkFold2EqTrue #[none, none, inst1, inst2, b1, b2, f, foldResPf]
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | #[⟨x, b1, hxb1, inst1⟩, ⟨y, b2, hyb2, inst2⟩, ⟨z, b3, hzb3, inst3⟩] =>
      let boundFVars := #[.fvar x, .fvar hxb1, .fvar y, .fvar hyb2, .fvar z, .fvar hzb3]
      let natLikeFVars := #[.fvar x, .fvar y, .fvar z]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let b2 ← mkLambdaFVars #[.fvar x] b2
      let b3 ← mkLambdaFVars #[.fvar x, .fvar y] b3
      let f ← mkLambdaFVars natLikeFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppOptM ``mkFold3 #[none, none, none, inst1, inst2, inst3, b1, b2, b3, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let foldResPf := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      let pf ← mkAppOptM ``ofMkFold3EqTrue #[none, none, none, inst1, inst2, inst3, b1, b2, b3, f, foldResPf]
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | #[⟨x, b1, hxb1, inst1⟩, ⟨y, b2, hyb2, inst2⟩, ⟨z, b3, hzb3, inst3⟩, ⟨a, b4, hab4, inst4⟩] =>
      let boundFVars := #[.fvar x, .fvar hxb1, .fvar y, .fvar hyb2, .fvar z, .fvar hzb3, .fvar a, .fvar hab4]
      let natLikeFVars := #[.fvar x, .fvar y, .fvar z, .fvar a]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let b2 ← mkLambdaFVars #[.fvar x] b2
      let b3 ← mkLambdaFVars #[.fvar x, .fvar y] b3
      let b4 ← mkLambdaFVars #[.fvar x, .fvar y, .fvar z] b4
      let f ← mkLambdaFVars natLikeFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppOptM ``mkFold4
        #[none, none, none, none, inst1, inst2, inst3, inst4, b1, b2, b3, b4, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let foldResPf := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      let pf ← mkAppOptM ``ofMkFold4EqTrue
        #[none, none, none, none, inst1, inst2, inst3, inst4, b1, b2, b3, b4, f, foldResPf]
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | #[⟨x, b1, hxb1, inst1⟩, ⟨y, b2, hyb2, inst2⟩, ⟨z, b3, hzb3, inst3⟩, ⟨a, b4, hab4, inst4⟩,
        ⟨b, b5, hbb5, inst5⟩] =>
      let boundFVars :=
        #[.fvar x, .fvar hxb1, .fvar y, .fvar hyb2, .fvar z, .fvar hzb3, .fvar a, .fvar hab4, .fvar b, .fvar hbb5]
      let natLikeFVars := #[.fvar x, .fvar y, .fvar z, .fvar a, .fvar b]
      let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
      trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
      let b2 ← mkLambdaFVars #[.fvar x] b2
      let b3 ← mkLambdaFVars #[.fvar x, .fvar y] b3
      let b4 ← mkLambdaFVars #[.fvar x, .fvar y, .fvar z] b4
      let b5 ← mkLambdaFVars #[.fvar x, .fvar y, .fvar z, .fvar a] b5
      let f ← mkLambdaFVars natLikeFVars (← mkDecide (← mkForallFVars unboundFVars g))
      trace[brute.debug] "f: {f}"
      let res ← mkAppOptM ``mkFold5
        #[none, none, none, none, none, inst1, inst2, inst3, inst4, inst5, b1, b2, b3, b4, b5, f, mkConst ``true]
      trace[brute.debug] "res: {res}"

      let levels := (collectLevelParams {} res).params.toList
      let auxDeclName ← Term.mkAuxName `_brute
      let decl := Declaration.defnDecl $
        mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
      addAndCompile decl

      let rflPrf ← mkEqRefl (toExpr true)
      let levelParams := levels.map .param
      let foldResPf := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
      let pf ← mkAppOptM ``ofMkFold5EqTrue
        #[none, none, none, none, none, inst1, inst2, inst3, inst4, inst5, b1, b2, b3, b4, b5, f, foldResPf]
      mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' pf boundFVars]
    | _ => throwError "Not yet implemented (boundBinders: {boundBinders})"
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

example : ∀ x < 5, ∀ y < x, ∀ z < x + y, ∀ a < 3, x + y + z + a ≤ 100 := by
  brute

example : ∀ x < 5, ∀ y < x, ∀ z < x + y, ∀ a < 3, ∀ b < a, x + y + z + a + b ≤ 100 := by
  brute

example : ∀ f : Fin 3 → Bool, ∀ x < 3, f x ∨ ¬f x := by
  decide +native

-- **NOTE** Current approach prevents NatLike types from depending on earlier variables

-- This works
example : ∀ n < 5, ∀ m : BitVec 8, m < 3 → n * m ≤ 20 := by
  brute

-- This fails
/-
example : ∀ n < 5, ∀ m : BitVec n, m < 3 → n * m ≤ 20 := by
  brute
-/

end Brute
