import Lean
import Aeneas
import Symcrust.Brute.BruteLemmas2

-- This file defines `brute`, a terminal tactic for brute force enumeration. It doesn't make sense to leave
-- this file here in the long term, but I am putting it here for now to make it easy to test on SymCrust proofs

open Lean Meta Parser Elab Tactic Aeneas Aeneas.Std

initialize registerTraceClass `brute.debug

namespace Brute

/-- A terminal tactic that attempts to prove goals of the form `∀ x y z ..., f x y z ...` via brute force.
    Brute requires that its goals consist of a string of universal quantifiers followed by a computable
    function and that each of the universal quantifiers match one of the following forms:
    - `∀ x : Nat, x < b → ...`
    - `∀ x : Nat, x ≤ b → ...`
    - `∀ x : BitVec n, ...`
    - `∀ x : BitVec n, x < b → ...`
    - `∀ x : BitVec n, x ≤ b → ...`
    - `∀ x : UScalar _, ...`
    - `∀ x : UScalar _, x < b → ...`
    - `∀ x : UScalar _, x ≤ b → ...`

    When a universal quantifier includes a `<` or `≤` condition, `brute` only checks over the values
    below the given upper bound. When the universal quantifier does not include such a condition and
    the type being quantified over is finite, `brute` checks over all values of the given type. -/
syntax (name := brute) "brute" : tactic

inductive BoundType where
  | ltUpperBound (b : Expr)
  | leUpperBound (b : Expr)
  | noUpperBound

instance : ToMessageData BoundType where
  toMessageData := fun
    | .ltUpperBound b => m!"< {b}"
    | .leUpperBound b => m!"≤ {b}"
    | .noUpperBound => m!"no upper bound"

/-- A structure that holds info for binders of the form `∀ x < b, ...` or `∀ x ≤ b, ...` or `∀ x, ...` -/
structure BinderInfo where
  x : FVarId -- The universally quantified variable
  b : BoundType -- The value that the variable is upper bounded by
  hxb : Option FVarId -- The variable whose type is `x < b` or `x ≤ b` (if present)
  isNatLikeInst : Expr -- An Expr whose type is `IsNatLike t` where `x : t` and `b : t`

instance : ToMessageData BinderInfo where
  toMessageData := fun ⟨x, b, hxb, isNatLikeInst⟩ => m!"({Expr.fvar x}, {b}, {hxb.map Expr.fvar}, {isNatLikeInst})"

/-- Retrieves the `UScalarTy` associated with a `U_` abbreviation. -/
def getSizeTyFromAbbrev (t : Expr) : Option Expr :=
  match t with
  | .const ``U8 _ => some $ mkConst ``UScalarTy.U8
  | .const ``U16 _ => some $ mkConst ``UScalarTy.U16
  | .const ``U32 _ => some $ mkConst ``UScalarTy.U32
  | .const ``U64 _ => some $ mkConst ``UScalarTy.U64
  | .const ``U128 _ => some $ mkConst ``UScalarTy.U128
  | _ => none

/-- If `t` is an Expr corresponding to `Nat`, `BitVec n`, or `UScalar t'`, then `getIsNatLike` returns
    an Expr whose type is `IsNatLike t`. Otherwise, `getIsNatLike` returns `none`. -/
def getIsNatLikeInstance (t : Expr) : MetaM (Option Expr) := do
  match t with
  | .const ``Nat _ =>
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    let isNatPf ← mkAppOptM ``IsNatLikePf.isNatPf #[none, rflPf]
    let inst ← mkAppM ``IsNatLike.mk #[isNatPf]
    return some inst
  | .app (.const ``BitVec _) n =>
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    let pSigmaβBody :=
      mkApp3 (mkConst ``Eq [2]) (.sort 1) (.app (.const ``BitVec []) n) (.app (.const ``BitVec []) (.bvar 0))
    let pSigmaβ := Expr.lam `n (mkConst ``Nat) pSigmaβBody .default
    let pSigmaPf ← mkAppOptM ``PSigma.mk #[none, some pSigmaβ, n, rflPf]
    let isBitVecPf ← mkAppOptM ``IsNatLikePf.isBitVecPf #[none, pSigmaPf]
    let inst ← mkAppM ``IsNatLike.mk #[isBitVecPf]
    return some inst
  | .app (.const ``UScalar _) (.const ``Usize _) => return none
  | .app (.const ``UScalar _) sizeTy => -- Matches with all `UScalar` types except `Usize`
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    let sizeTyNeUsizePf ← mkAppOptM ``UScalarTy.noConfusion #[mkConst ``False, sizeTy, mkConst ``Usize]
    let andPf ← mkAppM ``And.intro #[sizeTyNeUsizePf, rflPf]
    let pSigmaβBody :=
      mkApp2 (mkConst ``And)
        (mkApp3 (mkConst ``Ne [2]) (.sort 1) (.bvar 0) (mkConst ``Usize))
        (mkApp3 (mkConst ``Eq [2]) (.sort 1)
          (.app (.const ``UScalar []) sizeTy)
          (.app (.const ``UScalar []) (.bvar 0))
        )
    let pSigmaβ := Expr.lam `n (mkConst ``UScalarTy) pSigmaβBody .default
    let pSigmaPf ← mkAppOptM ``PSigma.mk #[none, pSigmaβ, sizeTy, andPf]
    let isUScalarPf ← mkAppOptM ``IsNatLikePf.isUScalarPf #[none, pSigmaPf]
    let inst ← mkAppM ``IsNatLike.mk #[isUScalarPf]
    return some inst
  | .const ``U8 _ | .const ``U16 _ | .const ``U32 _ | .const ``U64 _ | .const ``U128 _ =>
    let some sizeTy := getSizeTyFromAbbrev t
      | return none
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    let sizeTyNeUsizePf ← mkAppOptM ``UScalarTy.noConfusion #[mkConst ``False, sizeTy, mkConst ``UScalarTy.Usize]
    let andPf ← mkAppM ``And.intro #[sizeTyNeUsizePf, rflPf]
    let pSigmaβBody :=
      mkApp2 (mkConst ``And)
        (mkApp3 (mkConst ``Ne [1]) (mkConst ``UScalarTy) (.bvar 0) (mkConst ``UScalarTy.Usize))
        (mkApp3 (mkConst ``Eq [2]) (.sort 1)
          (.app (.const ``UScalar []) sizeTy)
          (.app (.const ``UScalar []) (.bvar 0))
        )
    let pSigmaβ := Expr.lam `n (mkConst ``UScalarTy) pSigmaβBody .default
    let pSigmaPf ← mkAppOptM ``PSigma.mk #[none, pSigmaβ, sizeTy, andPf]
    let isUScalarPf ← mkAppOptM ``IsNatLikePf.isUScalarPf #[none, pSigmaPf]
    let inst ← mkAppM ``IsNatLike.mk #[isUScalarPf]
    return some inst
  | _ => return none

/-- If `b1` has a NatLike type and `b2 : b1 < d` then returns a `BinderInfo` corresponding to
    `b1`, `b1`'s Natlike type, and `b2`. Otherwise returns `none`. -/
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
  let (b1UpperBound, hxb) ←
    match b2Type with
    | .app (.app (.app (.app (.const ``LT.lt _) _) _) x) y =>
      if x != Expr.fvar b1 then return none
      else pure (.ltUpperBound y, some b2)
    | .app (.app (.app (.app (.const ``LE.le _) _) _) x) y =>
      if x != Expr.fvar b1 then return none
      else pure (.leUpperBound y, some b2)
    | _ =>
      if b1Type == mkConst ``Nat then return none -- Brute can't support unbounded Nats
      else pure (.noUpperBound, none)
  return some ⟨b1, b1UpperBound, hxb, isNatLikeInst⟩

/-- Recursively calls `popBoundBinders` as many times as `goalBinders` allows. -/
def popAllBoundBinders (goalBinders : Array FVarId) (acc : Array BinderInfo) : TacticM (Array BinderInfo) := do
  match goalBinders with
  | ⟨[b]⟩ =>
    let lctx ← getLCtx
    let some bLocalDecl := lctx.find? b
      | throwError "{decl_name%} :: Unable to find type of goal binder {Expr.fvar b}"
    let bType := bLocalDecl.type
    let some isNatLikeInst ← getIsNatLikeInstance bType
      | return acc -- Don't pop this last binder
    let binderInfo := ⟨b, .noUpperBound, none, isNatLikeInst⟩
    return acc.push binderInfo
  | ⟨b1 :: b2 :: restBinders⟩ =>
    let some binderInfo ← popBoundBinders b1 b2
      | return acc
    if binderInfo.hxb.isSome then -- Two binders (`x` and `hxb` were popped)
      popAllBoundBinders ⟨restBinders⟩ $ acc.push binderInfo
    else -- Only one binder was popped
      popAllBoundBinders ⟨b2 :: restBinders⟩ $ acc.push binderInfo
  | _ => return acc

/-- Determines the optional upper bound that needs to be passed into `mkFold1` based on the BoundType `b` and
    the relevant NatLikeInst `inst`. -/
def upperBoundExprFromBoundType (b : BoundType) (inst : Expr) : TacticM Expr := do
  match b with
  | .ltUpperBound b => mkAppM ``some #[b]
  | .leUpperBound b => mkAppOptM ``natLikeSucc #[none, inst, b]
  | .noUpperBound => -- Return `none` of the appropriate type
    match inst with
    | .app (.app (.const ``IsNatLike.mk _) (.const ``Nat _)) _ =>
      throwError "{decl_name%} :: Cannot derive an upper bound for type Nat"
    | .app (.app (.const ``IsNatLike.mk _) t) _ =>
      mkAppOptM ``none #[t]
    | _ => throwError "{decl_name%} :: Invalid IsNatLike instance {inst}"

/-- Applies the appropriate to derive the original goal from the successful computation of the fold function. -/
def buildOfMkFoldProof (b : BoundType) (inst f f' hf : Expr) : TacticM Expr := do
  match b with
  | .ltUpperBound b => mkAppOptM ``ofMkFold1SomeLt #[none, inst, b, f, f', hf]
  | .leUpperBound b => mkAppOptM ``ofMkFold1SomeLe #[none, inst, b, f, f', hf]
  | .noUpperBound =>
    match inst with
    | .app (.app (.const ``IsNatLike.mk _) t) _ => mkAppOptM ``ofMkFold1None #[t, inst, f, f', hf]
    | _ => throwError "{decl_name%} :: Invalid IsNatLike instance {inst}"

-- **TODO** Write a doc string explaining what `x` and `hf` mean, and more broadly what this function is building
-- Also, don't overload the name `hf` as I currently do
def buildHfProofBaseCase (b : BoundType) (inst f : Expr) : TacticM Expr := do
  match b with
  | .ltUpperBound b =>
    match inst with
    | .app (.app (.const ``IsNatLike.mk _) t) _ =>
      let x ← mkFreshExprMVar t
      let hxType ← mkAppM ``LT.lt #[x, b]
      let hx ← mkFreshExprMVar hxType
      let hfType ← mkAppM ``Eq #[← mkAppM' f #[x], mkConst ``true]
      let hf ← mkFreshExprMVar hfType
      mkLambdaFVars #[x, hx, hf] hf
    | _ => throwError "{decl_name%} :: Invalid IsNatLike instance {inst}"
  | .leUpperBound b =>
    match inst with
    | .app (.app (.const ``IsNatLike.mk _) t) _ =>
      let x ← mkFreshExprMVar t
      let hxType ← mkAppM ``LE.le #[x, b]
      let hx ← mkFreshExprMVar hxType
      let hfType ← mkAppM ``Eq #[← mkAppM' f #[x], mkConst ``true]
      let hf ← mkFreshExprMVar hfType
      mkLambdaFVars #[x, hx, hf] hf
    | _ => throwError "{decl_name%} :: Invalid IsNatLike instance {inst}"
  | .noUpperBound =>
    match inst with
    | .app (.app (.const ``IsNatLike.mk _) t) _ =>
      let x ← mkFreshExprMVar t
      let hfType ← mkAppM ``Eq #[← mkAppM' f #[x], mkConst ``true]
      let hf ← mkFreshExprMVar hfType
      mkLambdaFVars #[x, hf] hf
    | _ => throwError "{decl_name%} :: Invalid IsNatLike instance {inst}"

def bruteCore (xs : Array Expr) (g : Expr) (boundBinders : List BinderInfo) :
  TacticM (Expr × Expr × Array Expr) := do
  match boundBinders with
  | [] => throwError "Goal does not match the form required by brute, consider trying native_decide instead"
  | [⟨x, b, hxbOpt, inst⟩] =>
    let boundFVars :=
      match hxbOpt with
      | some hxb => #[.fvar x, .fvar hxb]
      | none => #[.fvar x]
    let natLikeFVars := #[.fvar x]
    let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
    trace[brute.debug] "boundFVars: {boundFVars}, unboundFVars: {unboundFVars}"
    let f ← mkLambdaFVars natLikeFVars (← mkDecide (← mkForallFVars unboundFVars g))
    let hfPf ← buildHfProofBaseCase b inst f
    trace[brute.debug] "f: {f}"
    trace[brute.debug] "hfPf: {hfPf} (type : {← inferType hfPf})"
    let res ← mkAppOptM ``mkFold1 #[none, inst, ← upperBoundExprFromBoundType b inst, f, mkConst ``true]
    trace[brute.debug] "res: {res}"
    return (res, ← buildOfMkFoldProof b inst f f hfPf, boundFVars)
  | ⟨x, b, hxbOpt, inst⟩ :: restBoundBinders =>
    throwError "Not implemented yet"

@[tactic brute]
def evalBrute : Tactic
| `(tactic| brute) => withMainContext do
  let pf ← forallTelescope (← getMainTarget).consumeMData (cleanupAnnotations := true) $ fun xs g => do
    trace[brute.debug] "xs: {xs}, g: {g}"
    let boundBinders ← popAllBoundBinders (xs.map Expr.fvarId!) #[]
    let (res, ofMkFoldProof, boundFVars) ← bruteCore xs g boundBinders.toList

    let levels := (collectLevelParams {} res).params.toList
    let auxDeclName ← Term.mkAuxName `_brute
    let decl := Declaration.defnDecl $
      mkDefinitionValEx auxDeclName levels (mkConst ``Bool) res .abbrev .safe [auxDeclName]
    addAndCompile decl

    let rflPrf ← mkEqRefl (toExpr true)
    let levelParams := levels.map .param
    let foldResPf := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf

    let pf ← mkAppOptM' ofMkFoldProof $ Array.append #[foldResPf] (boundFVars.map some)
    mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, pf]

  trace[brute.debug] "pf: {pf}"
  trace[brute.debug] "pf type: {← inferType pf}"
  let g ← getMainGoal
  g.assign pf
| _ => throwUnsupportedSyntax

end Brute
