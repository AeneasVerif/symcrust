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
deriving Inhabited

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
deriving Inhabited

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

def typeFromInst (inst : Expr) : TacticM Expr :=
  match inst with
  | .app (.app (.const ``IsNatLike.mk _) t) _ => pure t
  | _ => throwError "{decl_name%} :: Invalid IsNatLike instance {inst}"

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
def popBoundBinders (poppedNatLikeGoalBinders : Array Expr)
  (b1 b2 : FVarId) : TacticM (Option BinderInfo) := do
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
      else
        let abstractedY ← mkLambdaFVars poppedNatLikeGoalBinders y
        pure (.ltUpperBound abstractedY, some b2)
    | .app (.app (.app (.app (.const ``LE.le _) _) _) x) y =>
      if x != Expr.fvar b1 then return none
      else
        let abstractedY ← mkLambdaFVars poppedNatLikeGoalBinders y
        pure (.leUpperBound abstractedY, some b2)
    | _ =>
      if b1Type == mkConst ``Nat then return none -- Brute can't support unbounded Nats
      else pure (.noUpperBound, none)
  return some ⟨b1, b1UpperBound, hxb, isNatLikeInst⟩

/-- Recursively calls `popBoundBinders` as many times as `goalBinders` allows. `poppedNatLikeGoalBinders`
    contains all of the `goalBinders` popped so far which contain fvars with Natlike types (these
    are exactly the fvars that need to be abstracted out of future upper bounds). -/
def popAllBoundBinders (poppedNatLikeGoalBinders : Array Expr) (remainingGoalBinders : Array FVarId)
  (acc : Array BinderInfo) : TacticM (Array BinderInfo) := do
  match remainingGoalBinders with
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
    let some binderInfo ← popBoundBinders poppedNatLikeGoalBinders b1 b2
      | return acc
    if binderInfo.hxb.isSome then -- Two binders (`x` and `hxb` were popped)
      popAllBoundBinders (poppedNatLikeGoalBinders.push (.fvar b1)) ⟨restBinders⟩ $ acc.push binderInfo
    else -- Only one binder was popped
      popAllBoundBinders (poppedNatLikeGoalBinders.push (.fvar b1)) ⟨b2 :: restBinders⟩ $ acc.push binderInfo
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

def bruteBaseCase1 (xs : Array Expr) (g : Expr) (x : FVarId) (b : BoundType)
  (hxbOpt : Option FVarId) (inst : Expr) : TacticM Expr := do
  let boundFVars :=
    match hxbOpt with
    | some hxb => #[.fvar x, .fvar hxb]
    | none => #[.fvar x]
  let unboundFVars := xs.filter (fun fvar => !boundFVars.contains fvar)
  let f ← mkLambdaFVars #[.fvar x] (← mkDecide (← mkForallFVars unboundFVars g))
  /- `hfPf` is one of the following (depending on the bound type of `b`):
      - `(fun x hf => hf) : ∀ (x : t1), f x = true → f x = true`
      - `(fun x hx hf => hf) : ∀ x < b, f x = true → f x = true`
      - `(fun x hx hf => hf) : ∀ x ≤ b, f x = true → f x = true` -/
  let hfPf ←
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
  let mkFold1Call ← mkAppOptM ``mkFold1 #[none, inst, ← upperBoundExprFromBoundType b inst, f, mkConst ``true]
  let ofMkFoldProof ← buildOfMkFoldProof b inst f f hfPf

  let levels := (collectLevelParams {} mkFold1Call).params.toList
  let auxDeclName ← Term.mkAuxName `_brute
  let decl := Declaration.defnDecl $
    mkDefinitionValEx auxDeclName levels (mkConst ``Bool) mkFold1Call .abbrev .safe [auxDeclName]
  addAndCompile decl

  let rflPrf ← mkEqRefl (toExpr true)
  let levelParams := levels.map .param
  let foldResPf := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf

  let pf ← mkAppOptM' ofMkFoldProof $ Array.append #[foldResPf] (boundFVars.map some)
  mkLambdaFVars boundFVars $ ← mkAppOptM ``of_decide_eq_true #[none, none, pf]

def buildComputationResBase_aux (prefixBoundTypes : List BoundType) (prefixInsts : Array Expr)
  (usedPrefixMVars : Array Expr) (unusedPrefixMVars : Array Expr) (innerLamBody : Expr) : TacticM (Option Expr × Expr) := do
  match prefixBoundTypes with
  | [] => return (none, innerLamBody)
  | nextPrefixBoundType :: prefixBoundTypes =>
    let nextPrefixInst := prefixInsts[0]!
    let prefixInsts := prefixInsts.drop 1
    let nextPrefixMVar := unusedPrefixMVars[0]!
    let unusedPrefixMVars := unusedPrefixMVars.drop 1

    trace[brute.debug] "nextPrefixMVar type: {← inferType nextPrefixMVar}"

    match nextPrefixBoundType with
    | .noUpperBound =>
      let (_, innerLamBody) ← buildComputationResBase_aux prefixBoundTypes prefixInsts (usedPrefixMVars.push nextPrefixMVar) unusedPrefixMVars innerLamBody
      let innerLam ← mkLambdaFVars #[nextPrefixMVar] innerLamBody (binderInfoForMVars := .default)
      let res ← mkAppOptM ``mkFold1 #[none, nextPrefixInst, ← mkAppOptM ``none #[← inferType nextPrefixMVar], innerLam, mkConst ``true]
      return (some innerLam, res)
    | .ltUpperBound b =>
      let (_, innerLamBody) ← buildComputationResBase_aux prefixBoundTypes prefixInsts (usedPrefixMVars.push nextPrefixMVar) unusedPrefixMVars innerLamBody
      let innerLam ← mkLambdaFVars #[nextPrefixMVar] innerLamBody (binderInfoForMVars := .default)
      let res ← mkAppOptM ``mkFold1 #[none, nextPrefixInst, ← mkAppM ``some #[← mkAppM' b usedPrefixMVars], innerLam, mkConst ``true]
      return (some innerLam, res)
    | .leUpperBound b =>
      let (_, innerLamBody) ← buildComputationResBase_aux prefixBoundTypes prefixInsts (usedPrefixMVars.push nextPrefixMVar) unusedPrefixMVars innerLamBody
      let innerLam ← mkLambdaFVars #[nextPrefixMVar] innerLamBody (binderInfoForMVars := .default)
      let res ← mkAppOptM ``mkFold1 #[none, nextPrefixInst, ← mkAppM ``some #[← mkAppM' b usedPrefixMVars], innerLam, mkConst ``true]
      return (some innerLam, res)

def buildComputationResBase (prefixBinderInfos : Array BinderInfo)
  (t f : Expr) (b : BoundType) (inst : Expr) : TacticM (Option Expr × Expr × Expr) := do
  let prefixTypes ← prefixBinderInfos.mapM (fun bInfo => typeFromInst bInfo.isNatLikeInst)
  let prefixBoundTypes := prefixBinderInfos.map (fun bInfo => bInfo.b)
  let prefixInsts := prefixBinderInfos.map (fun bInfo => bInfo.isNatLikeInst)

  let freshPrefixMVars ← prefixTypes.mapM (fun t => mkFreshExprMVar (some t))

  /- mkFold1 (none : Option t1)
      (fun (x' : t1) => mkFold1 (none : Option t2)
        (fun (y' : t2) => mkFold1 (none : Option t3) (f x' y') true) true) true = true`
  -/

  trace[brute.debug] "{decl_name%} :: bp1"

  -- `mkFold1 (some b1) (fun x' => mkFold1 (some (b2 x')) (f x') true) true = true`
  -- `mkFold1 (some b1) (fun x' => mkFold1 none (f x') true) true = true`

  /- Depending on b2, `innerLam` is either:
      - `(fun (x' : t1) => mkFold1 (none : Option t2) (f x') true)`
      - `(fun (x' : t1) => mkFold1 (some (b2 x')) (f x') true)` -/
  let innerLamBody ← -- **TODO** Rename innerMostLam?
    match b with
    | .noUpperBound => mkAppOptM ``mkFold1 #[none, inst, ← mkAppOptM ``none #[t], ← mkAppM' f freshPrefixMVars, mkConst ``true]
    | .ltUpperBound b => mkAppOptM ``mkFold1 #[none, inst, ← mkAppM ``some #[← mkAppM' b freshPrefixMVars], ← mkAppM' f freshPrefixMVars, mkConst ``true]
    | .leUpperBound b => mkAppOptM ``mkFold1 #[none, inst, ← mkAppM ``some #[← mkAppM' b freshPrefixMVars], ← mkAppM' f freshPrefixMVars, mkConst ``true]
  -- let innerLam ← mkLambdaFVars #[(freshPrefixMVars[freshPrefixMVars.size - 1]!)] innerLamBody

  trace[brute.debug] "{decl_name%} :: bp2"
  trace[brute.debug] "{decl_name%} :: innerLamBody: {innerLamBody}"
  trace[brute.debug] "{decl_name%} :: innerLamBody type: {← inferType innerLamBody}"

  /- Depending on b1, `mkFold1Call` is:
    - `mkFold1 (none : Option t1) innerLam true`
    - `mkFold1 (some b1) innerLam true` -/
  let (fold1InnerLamOpt, mkFold1Call) ← buildComputationResBase_aux prefixBoundTypes.toList prefixInsts #[] freshPrefixMVars innerLamBody

  trace[brute.debug] "{decl_name%} :: bp3"

  let levels := (collectLevelParams {} mkFold1Call).params.toList
  let auxDeclName ← Term.mkAuxName `_brute
  let decl := Declaration.defnDecl $
    mkDefinitionValEx auxDeclName levels (mkConst ``Bool) mkFold1Call .abbrev .safe [auxDeclName]
  addAndCompile decl

  trace[brute.debug] "{decl_name%} :: decl to be compiled: {mkFold1Call}"

  let rflPrf ← mkEqRefl (toExpr true)
  let levelParams := levels.map .param
  return (fold1InnerLamOpt, mkFold1Call, mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf)

def buildComputationResFinalRecursive (prefixFVars natLikeFVars : Array Expr) (prefixBinderInfos : Array BinderInfo)
  (computationInnerLamOpt : Option Expr) (computationResIsTrue : Expr) : TacticM Expr := do
  let computationInnerLam := computationInnerLamOpt.get!
  let x' ← mkFreshExprMVar $ ← inferType natLikeFVars[0]!
  let h ← mkFreshExprMVar $
    ← mkAppM ``Eq #[← mkAppOptM' computationInnerLam #[x'], mkConst ``true]

  match prefixBinderInfos[0]!.b with
  | .noUpperBound =>
    let arg3 ← mkLambdaFVars #[x', h] h
    return ← mkAppOptM ``ofMkFold1None
      #[none, prefixBinderInfos[0]!.isNatLikeInst, computationInnerLam, computationInnerLam, arg3, computationResIsTrue, natLikeFVars[0]!]
  | .ltUpperBound b =>
    let hx' ← mkFreshExprMVar $ ← mkAppM ``LT.lt #[x', b]
    let arg3 ← mkLambdaFVars #[x', hx', h] h
    return ← mkAppOptM ``ofMkFold1SomeLt
      #[none, prefixBinderInfos[0]!.isNatLikeInst, b, computationInnerLam,
        computationInnerLam, arg3, computationResIsTrue, natLikeFVars[0]!, prefixFVars[1]!]
  | .leUpperBound b =>
    let hx' ← mkFreshExprMVar $ ← mkAppM ``LT.lt #[x', b]
    let arg3 ← mkLambdaFVars #[x', hx', h] h
    return ← mkAppOptM ``ofMkFold1SomeLe
      #[none, prefixBinderInfos[0]!.isNatLikeInst, b, computationInnerLam,
        computationInnerLam, arg3, computationResIsTrue, natLikeFVars[0]!, prefixFVars[1]!]

def buildComputationResRecursive (prefixFVars natLikeFVars : Array Expr) (prefixBinderInfos : Array BinderInfo)
  (t f : Expr) (b : BoundType) (inst : Expr) (computationInnerLamOpt : Option Expr)
  (computationRes computationResIsTrue : Expr) : TacticM Expr := do -- **TODO** Generalize based on `b`
  trace[brute.debug] "{decl_name%} :: natLikeFVars at start: {natLikeFVars}"
  if hsize0 : natLikeFVars.size <= 1 then
    return computationResIsTrue
  else
    if hsize1 : natLikeFVars.size == 2 then
      return ← buildComputationResFinalRecursive prefixFVars natLikeFVars prefixBinderInfos computationInnerLamOpt computationResIsTrue
    else
      let lastPrefixFVars :=
        if prefixBinderInfos[prefixBinderInfos.size - 1]!.hxb.isSome then
          #[prefixFVars[prefixFVars.size - 2]!, prefixFVars[prefixFVars.size - 1]!]
        else
          #[prefixFVars[prefixFVars.size - 1]!]
      let secondLastPrefixFVars :=
        if prefixBinderInfos[prefixBinderInfos.size - 2]!.hxb.isSome then
          #[prefixFVars[prefixFVars.size - lastPrefixFVars.size - 2]!, prefixFVars[prefixFVars.size - lastPrefixFVars.size - 1]!]
        else
          #[prefixFVars[prefixFVars.size - lastPrefixFVars.size - 1]!]
      let prefixFVarsTaken := prefixFVars.take (prefixFVars.size - lastPrefixFVars.size)
      let natLikeFVarsTaken := natLikeFVars.take (natLikeFVars.size - 1)
      let natLikeFVarsTake2 := natLikeFVars.take (natLikeFVars.size - 2)

      let prefixTypes ← prefixBinderInfos.mapM (fun bInfo => typeFromInst bInfo.isNatLikeInst)
      let prefixBoundTypes := prefixBinderInfos.map (fun bInfo => bInfo.b)
      let prefixInsts := prefixBinderInfos.map (fun bInfo => bInfo.isNatLikeInst)

      let lastPrefixType := prefixTypes[prefixTypes.size - 1]!
      let secondLastPrefixType := prefixTypes[prefixTypes.size - 2]!
      let lastPrefixBoundType := prefixBoundTypes[prefixBoundTypes.size - 1]!
      let lastPrefixInst := prefixInsts[prefixInsts.size - 1]!
      let secondLastPrefixInst := prefixInsts[prefixInsts.size - 2]!

      let prefixBinderInfos := prefixBinderInfos.take (prefixBinderInfos.size - 1)

      let y' ← mkFreshExprMVar secondLastPrefixType
      let z' ← mkFreshExprMVar lastPrefixType

      trace[brute.debug] "{decl_name%} :: bp1"

      -- `arg1 = (fun y' => mkFold1 none (fun z' => mkFold1 none (f x y' z') true) true)`
      let arg1InnerLamBody ← mkAppOptM ``mkFold1 #[none, inst, ← mkAppOptM ``none #[t], ← mkAppM' f (natLikeFVarsTake2 ++ #[y', z']), mkConst ``true]
      let arg1InnerLam ← mkLambdaFVars #[z'] arg1InnerLamBody
      let arg1LamBody ← mkAppOptM ``mkFold1 #[none, lastPrefixInst, ← mkAppOptM ``none #[lastPrefixType], arg1InnerLam, mkConst ``true]
      let arg1 ← mkLambdaFVars #[y'] arg1LamBody (binderInfoForMVars := .default)
      let arg2 := arg1 -- `arg2` is identical to `arg1`

      trace[brute.debug] "{decl_name%} :: bp2"
      trace[brute.debug] "{decl_name%} :: b: {b}"

      -- `h : (fun y' => mkFold1 none (fun z' => mkFold1 none (f x y' z') true) true) y' = true`
      let h ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppOptM' arg1 #[y'], mkConst ``true]
      -- `arg3 = (fun _ h => h)` or `arg3 = (fun y' hy' h => h)`
      let arg3 ←
        match prefixBinderInfos[prefixBinderInfos.size - 1]!.b with
        | .noUpperBound => mkLambdaFVars #[y', h] h
        | .ltUpperBound b =>
          let hy' ← mkFreshExprMVar $ ← mkAppM ``LT.lt #[y', ← mkAppM' b natLikeFVars]
          mkLambdaFVars #[y', hy', h] h
        | .leUpperBound b =>
          let hy' ← mkFreshExprMVar $ ← mkAppM ``LE.le #[y', ← mkAppM' b natLikeFVars]
          mkLambdaFVars #[y', hy', h] h

      trace[brute.debug] "{decl_name%} :: bp3"

      let arg4 ←
        buildComputationResRecursive prefixFVarsTaken natLikeFVarsTaken prefixBinderInfos lastPrefixType f
          lastPrefixBoundType lastPrefixInst computationInnerLamOpt computationRes computationResIsTrue

      trace[brute.debug] "{decl_name%} :: arg1: {arg1}"
      trace[brute.debug] "{decl_name%} :: arg2: {arg2}"
      trace[brute.debug] "{decl_name%} :: arg3: {arg3}"
      trace[brute.debug] "{decl_name%} :: arg4: {arg4}"
      trace[brute.debug] "{decl_name%} :: secondLastPrefixInst: {secondLastPrefixInst}"
      trace[brute.debug] "{decl_name%} :: lastPrefixFVars: {lastPrefixFVars}"
      trace[brute.debug] "{decl_name%} :: b: {b}"
      -- **TODO** Fix naming confusion where `lastPrefixFVars` aligns with `secondLastPrefixInst` (this is caused by the fact that
      -- in `buildArg3`, `prefixFVars` is set to `prefixFVars.take (prefixFVars.size - lastPrefixFVars.size)` but nothing analogous is
      -- done to `prefixBinderInfos`)

      match b with
      | .noUpperBound => mkAppOptM ``ofMkFold1None $ #[none, secondLastPrefixInst, arg1, arg2, arg3, arg4] ++ (secondLastPrefixFVars.map some)
      | .ltUpperBound b =>
        mkAppOptM ``ofMkFold1SomeLt $
          #[none, inst, ← mkAppM' b natLikeFVars, arg1, arg2, arg3, arg4] ++ (secondLastPrefixFVars.map some)
      | .leUpperBound b =>
        mkAppOptM ``ofMkFold1SomeLe $
          #[none, inst, ← mkAppM' b natLikeFVars, arg1, arg2, arg3, arg4] ++ (secondLastPrefixFVars.map some)
termination_by natLikeFVars.size
decreasing_by
  simp only [beq_iff_eq] at hsize0 hsize1
  simp
  omega

def buildArg3 (prefixFVars natLikeFVars : Array Expr) (prefixBinderInfos : Array BinderInfo)
  (t f : Expr) (b : BoundType) (inst : Expr) (computationInnerLamOpt : Option Expr)
  (computationRes computationResIsTrue : Expr) : TacticM Expr := do
  let lastPrefixFVars :=
    if prefixBinderInfos[prefixBinderInfos.size - 1]!.hxb.isSome then
      #[prefixFVars[prefixFVars.size - 2]!, prefixFVars[prefixFVars.size - 1]!]
    else
      #[prefixFVars[prefixFVars.size - 1]!]
  let natLikeFVarsTaken := natLikeFVars.take (natLikeFVars.size - 1)

  let prefixTypes ← prefixBinderInfos.mapM (fun bInfo => typeFromInst bInfo.isNatLikeInst)
  let prefixBoundTypes := prefixBinderInfos.map (fun bInfo => bInfo.b)
  let prefixInsts := prefixBinderInfos.map (fun bInfo => bInfo.isNatLikeInst)

  let lastPrefixType := prefixTypes[prefixTypes.size - 1]!
  let lastPrefixBoundType := prefixBoundTypes[prefixBoundTypes.size - 1]!
  let lastPrefixInst := prefixInsts[prefixInsts.size - 1]!

  let x' ← mkFreshExprMVar lastPrefixType

  match b with
  | .noUpperBound =>
    trace[brute.debug] "{decl_name%} :: bp1"
    trace[brute.debug] "x': {x'}"
    trace[brute.debug] "prefixFVars: {prefixFVars}"
    trace[brute.debug] "natLikeFVars: {natLikeFVars}"

    -- `arg1 = (fun (x' : t1) => mkFold1 (none : Option t2) (fun (_ : t2) => mkFold1 none (f x') true) true)`
    let arg1InnerLamBody ← mkAppOptM ``mkFold1 #[none, inst, ← mkAppOptM ``none #[t], ← mkAppM' f (natLikeFVarsTaken.push x'), mkConst ``true]
    let arg1InnerLam ← mkLambdaFVars #[← mkFreshExprMVar t] arg1InnerLamBody
    let arg1LamBody ← mkAppOptM ``mkFold1 #[none, inst, ← mkAppOptM ``none #[t], arg1InnerLam, mkConst ``true]
    let arg1 ← mkLambdaFVars #[x'] arg1LamBody

    trace[brute.debug] "{decl_name%} :: bp2"

    -- `arg2 = (fun (x' : t1) => mkFold1 none (f x') true)`
    let arg2LamBody ← mkAppOptM ``mkFold1 #[none, inst, ← mkAppOptM ``none #[t], ← mkAppM' f (natLikeFVarsTaken.push x'), mkConst ``true]
    let arg2 ← mkLambdaFVars #[x'] arg2LamBody

    trace[brute.debug] "{decl_name%} :: bp3"

    /- Depending on `lastPrefixBoundType`, `arg3` is equal to:
      - `(fun (x' : t1) => ofMkFold1Triv f x' (none : Option t2))`
      - `(fun (x' : t1) (hx' : x' < b1) => ofMkFold1Triv f x' (none : Option t2))`
      - `(fun (x' : t1) (hx' : x' ≤ b1) => ofMkFold1Triv f x' (none : Option t2))` -/
    let arg3LamBody ← mkAppOptM ``ofMkFold1Triv #[none, none, lastPrefixInst, inst, ← mkAppM' f natLikeFVarsTaken, x', ← mkAppOptM ``none #[t]]
    let arg3 ←
      match lastPrefixBoundType with
      | .noUpperBound => mkLambdaFVars #[x'] arg3LamBody
      | .ltUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LT.lt #[lastPrefixType, none, x', ← mkAppM' b1 natLikeFVarsTaken]
        mkLambdaFVars #[x', hx'] arg3LamBody
      | .leUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LE.le #[lastPrefixType, none, x', ← mkAppM' b1 natLikeFVarsTaken]
        mkLambdaFVars #[x', hx'] arg3LamBody

    trace[brute.debug] "{decl_name%} :: bp4"

    trace[brute.debug] "{decl_name%} :: arg3: {arg3}"
    trace[brute.debug] "{decl_name%} :: arg3 type: {← inferType arg3}"

    let computationResIsTrue ←
      buildComputationResRecursive prefixFVars natLikeFVars prefixBinderInfos t f b inst computationInnerLamOpt computationRes computationResIsTrue

    match lastPrefixBoundType with -- **TODO** Recurse instead of using computaitonRes if needed
    | .noUpperBound =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1None #[lastPrefixType, lastPrefixInst, arg1, arg2, arg3, computationResIsTrue]
      mkAppM' ofMkFold1Res lastPrefixFVars
    | .ltUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLt #[lastPrefixType, lastPrefixInst, ← mkAppM' b1 natLikeFVarsTaken, arg1, arg2, arg3, computationResIsTrue]
      mkAppM' ofMkFold1Res lastPrefixFVars
    | .leUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLe #[lastPrefixType, lastPrefixInst, ← mkAppM' b1 natLikeFVarsTaken, arg1, arg2, arg3, computationResIsTrue]
      mkAppM' ofMkFold1Res lastPrefixFVars
  | .ltUpperBound b =>
    trace[brute.debug] "{decl_name%} :: bp1"

    -- `arg1 = (fun (x' : t1) => mkFold1 (some (b x')) (fun (_ : t2) => mkFold1 (some (b x')) (f x') true) true)`
    let arg1InnerLamBody ← mkAppOptM ``mkFold1 #[none, inst, ← mkAppM ``some #[← mkAppM' b (natLikeFVarsTaken.push x')], ← mkAppM' f (natLikeFVarsTaken.push x'), mkConst ``true]
    let arg1InnerLam ← mkLambdaFVars #[← mkFreshExprMVar t] arg1InnerLamBody
    let arg1LamBody ← mkAppOptM ``mkFold1 #[none, inst, ← mkAppM ``some #[← mkAppM' b (natLikeFVarsTaken.push x')], arg1InnerLam, mkConst ``true]
    let arg1 ← mkLambdaFVars #[x'] arg1LamBody

    trace[brute.debug] "{decl_name%} :: bp2"

    -- `arg2 = (fun (x' : t1) => mkFold1 (some (b2 x')) (f x') true)`
    let arg2LamBody ← mkAppOptM ``mkFold1 #[none, inst, ← mkAppM ``some #[← mkAppM' b (natLikeFVarsTaken.push x')], ← mkAppM' f (natLikeFVarsTaken.push x'), mkConst ``true]
    let arg2 ← mkLambdaFVars #[x'] arg2LamBody

    trace[brute.debug] "{decl_name%} :: bp3"

    /- Depending on `b1`, `arg3` is equal to:
      - `(fun (x' : t1) => ofMkFold1Triv f x' (some (b2 x')))`
      - `(fun (x' : t1) (hx' : x' < b1) => ofMkFold1Triv f x' (some (b2 x')))`
      - `(fun (x' : t1) (hx' : x' ≤ b1) => ofMkFold1Triv f x' (some (b2 x')))` -/
    let arg3LamBody ←
      mkAppOptM ``ofMkFold1Triv #[none, none, lastPrefixInst, inst, ← mkAppM' f natLikeFVarsTaken, x', ← mkAppM ``some #[← mkAppM' b (natLikeFVarsTaken.push x')]]
    let arg3 ←
      match lastPrefixBoundType with
      | .noUpperBound => mkLambdaFVars #[x'] arg3LamBody
      | .ltUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LT.lt #[lastPrefixType, none, x', ← mkAppM' b1 natLikeFVarsTaken]
        mkLambdaFVars #[x', hx'] arg3LamBody
      | .leUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LE.le #[lastPrefixType, none, x', ← mkAppM' b1 natLikeFVarsTaken]
        mkLambdaFVars #[x', hx'] arg3LamBody

    trace[brute.debug] "{decl_name%} :: bp4"

    let computationResIsTrue ←
      buildComputationResRecursive prefixFVars natLikeFVars prefixBinderInfos t f (.ltUpperBound b)
        inst computationInnerLamOpt computationRes computationResIsTrue

    match lastPrefixBoundType with
    | .noUpperBound =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1None #[lastPrefixType, lastPrefixInst, arg1, arg2, arg3, computationResIsTrue]
      mkAppM' ofMkFold1Res lastPrefixFVars
    | .ltUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLt #[lastPrefixType, lastPrefixInst, ← mkAppM' b1 natLikeFVarsTaken, arg1, arg2, arg3, computationResIsTrue]
      mkAppM' ofMkFold1Res lastPrefixFVars
    | .leUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLe #[lastPrefixType, lastPrefixInst, ← mkAppM' b1 natLikeFVarsTaken, arg1, arg2, arg3, computationResIsTrue]
      mkAppM' ofMkFold1Res lastPrefixFVars
  | .leUpperBound b =>
    -- `arg1 = (fun (x' : t1) => mkFold1 (natLikeSucc (b2 x')) (fun (_ : t2) => mkFold1 (natLikeSucc (b2 x')) (f x') true) true)`
    let arg1InnerLamBody ←
      mkAppOptM ``mkFold1 #[none, inst, ← mkAppOptM ``natLikeSucc #[none, inst, ← mkAppM' b (natLikeFVarsTaken.push x')], ← mkAppM' f (natLikeFVarsTaken.push x'), mkConst ``true]
    let arg1InnerLam ← mkLambdaFVars #[← mkFreshExprMVar t] arg1InnerLamBody
    let arg1LamBody ←
      mkAppOptM ``mkFold1 #[none, inst, ← mkAppOptM ``natLikeSucc #[none, inst, ← mkAppM' b (natLikeFVarsTaken.push x')], arg1InnerLam, mkConst ``true]
    let arg1 ← mkLambdaFVars #[x'] arg1LamBody

    -- `arg2 = (fun (x' : t1) => mkFold1 (natLikeSucc (b2 x')) (f x') true)`
    let arg2LamBody ←
      mkAppOptM ``mkFold1 #[none, inst, ← mkAppOptM ``natLikeSucc #[none, inst, ← mkAppM' b (natLikeFVarsTaken.push x')], ← mkAppM' f (natLikeFVarsTaken.push x'), mkConst ``true]
    let arg2 ← mkLambdaFVars #[x'] arg2LamBody

    /- Depending on `b1`, `arg3` is equal to:
      - `(fun (x' : t1) => ofMkFold1Triv f x' (natLikeSucc (b2 x')))`
      - `(fun (x' : t1) (hx' : x' < b1) => ofMkFold1Triv f x' (natLikeSucc (b2 x')))`
      - `(fun (x' : t1) (hx' : x' ≤ b1) => ofMkFold1Triv f x' (natLikeSucc (b2 x')))` -/
    let arg3LamBody ←
      mkAppOptM ``ofMkFold1Triv
        #[none, none, lastPrefixInst, inst, ← mkAppM' f natLikeFVarsTaken, x', ← mkAppOptM ``natLikeSucc #[none, inst, ← mkAppM' b (natLikeFVarsTaken.push x')]]
    let arg3 ←
      match lastPrefixBoundType with
      | .noUpperBound => mkLambdaFVars #[x'] arg3LamBody
      | .ltUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LT.lt #[lastPrefixType, none, x', ← mkAppM' b1 natLikeFVarsTaken]
        mkLambdaFVars #[x', hx'] arg3LamBody
      | .leUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LE.le #[lastPrefixType, none, x', ← mkAppM' b1 natLikeFVarsTaken]
        mkLambdaFVars #[x', hx'] arg3LamBody

    let computationResIsTrue ←
      buildComputationResRecursive prefixFVars natLikeFVars prefixBinderInfos t f (.leUpperBound b)
        inst computationInnerLamOpt computationRes computationResIsTrue

    match lastPrefixBoundType with
    | .noUpperBound =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1None #[lastPrefixType, lastPrefixInst, arg1, arg2, arg3, computationResIsTrue]
      mkAppM' ofMkFold1Res lastPrefixFVars
    | .ltUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLt #[lastPrefixType, lastPrefixInst, ← mkAppM' b1 natLikeFVarsTaken, arg1, arg2, arg3, computationResIsTrue]
      mkAppM' ofMkFold1Res lastPrefixFVars
    | .leUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLe #[lastPrefixType, lastPrefixInst, ← mkAppM' b1 natLikeFVarsTaken, arg1, arg2, arg3, computationResIsTrue]
      mkAppM' ofMkFold1Res lastPrefixFVars

def bruteCore (binderInfos : Array BinderInfo) (unboundBinders : Array Expr) (g : Expr) : TacticM Expr := do
  let finalBinderInfo := binderInfos[binderInfos.size - 1]!
  let finalBinderFVars :=
    match finalBinderInfo.hxb with
    | some hxb => #[Expr.fvar finalBinderInfo.x, Expr.fvar hxb]
    | none => #[Expr.fvar finalBinderInfo.x]
  let t ← typeFromInst finalBinderInfo.isNatLikeInst
  let inst := finalBinderInfo.isNatLikeInst

  trace[brute.debug] "bp1"

  let binderInfosPrefix := binderInfos.take (binderInfos.size - 1)
  let natLikeFVars := binderInfos.map (fun bInfo => Expr.fvar bInfo.x)
  let prefixNatLikeFVars := binderInfosPrefix.map (fun bInfo => Expr.fvar bInfo.x)
  let prefixFVars := Array.flatten $
    binderInfosPrefix.map
    (fun bInfo =>
      match bInfo.hxb with
      | some hxb => #[Expr.fvar bInfo.x, Expr.fvar hxb]
      | none => #[Expr.fvar bInfo.x])

  trace[brute.debug] "bp2"

  let f ← mkLambdaFVars natLikeFVars (← mkDecide (← mkForallFVars unboundBinders g))
  let fWithPrefix ← mkAppM' f prefixNatLikeFVars

  trace[brute.debug] "bp3"

  /- `arg1` is one of the following (depending on the bound type of finalBinderInfo)
      - `(fun (_ : t) => mkFold1 (none : Option t) fWithPrefix true) : t → Bool`
      - `(fun (_ : t) => mkFold1 (some (finalBinderInfo.b prefixNatLikeFVars)) fWithPrefix true)`
      - `(fun (_ : t) => mkFold1 (natLikeSucc (finalBinderInfo.b prefixNatLikeFVars)) fWithPrefix true)` -/
  let arg1 ←
    match finalBinderInfo.b with
    | .noUpperBound =>
      let lamBody ←
        mkAppOptM ``mkFold1
          #[none, inst, ← mkAppOptM ``none #[t], fWithPrefix, mkConst ``true]
      pure $ Expr.lam `_ t lamBody .default
    | .ltUpperBound b =>
      let lamBody ←
        mkAppOptM ``mkFold1
          #[none, inst, ← mkAppM ``some #[← mkAppM' b prefixNatLikeFVars], fWithPrefix, mkConst ``true]
      pure $ Expr.lam `_ t lamBody .default
    | .leUpperBound b =>
      let lamBody ←
        mkAppOptM ``mkFold1
          #[none, inst, ← mkAppOptM ``natLikeSucc #[none, inst, ← mkAppM' b prefixNatLikeFVars], fWithPrefix, mkConst ``true]
      pure $ Expr.lam `_ t lamBody .default

  trace[brute.debug] "bp4"

  /- `arg2` is one of the following (depending on the bound type of finalBinderInfo)
      - `(fun (y : t) (h : arg1 y = true) => ofMkFold1None (f x) (f x) (fun (y' : t) (hf : f x y' = true) => hf) h y)`
      - `(fun (y : t) (hy : y < (b2 x)) (h : arg1 y = true) =>`
            `ofMkFold1SomeLt (b2 x) (f x) (f x) (fun (y' : t) (hy' : y' < b2 x) (hf : f x y' = true) => hf) h y hy)`
      - `(fun (y : t) (hy : y ≤ (b2 x)) (h : arg1 y = true) =>`
            `ofMkFold1SomeLe (b2 x) (f x) (f x) (fun (y' : t) (hy' : y' ≤ b2 x) (hf : f x y' = true) => hf) h y hy)` -/
  let arg2 ←
    match finalBinderInfo.b with
    | .noUpperBound =>
      let y ← mkFreshExprMVar t
      let y' ← mkFreshExprMVar t
      let h ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' arg1 #[y], mkConst ``true]
      let hf ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' fWithPrefix #[y'], mkConst ``true]
      let innerLam ← mkLambdaFVars #[y', hf] hf
      let lamBody ← mkAppOptM ``ofMkFold1None #[none, inst, fWithPrefix, fWithPrefix, innerLam, h, y]
      mkLambdaFVars #[y, h] lamBody
    | .ltUpperBound b =>
      let y ← mkFreshExprMVar t
      let y' ← mkFreshExprMVar t
      let hy ← mkFreshExprMVar $ ← mkAppM ``LT.lt #[y, ← mkAppM' b prefixNatLikeFVars]
      let hy' ← mkFreshExprMVar $ ← mkAppM ``LT.lt #[y', ← mkAppM' b prefixNatLikeFVars]
      let h ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' arg1 #[y], mkConst ``true]
      let hf ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' fWithPrefix #[y'], mkConst ``true]
      let innerLam ← mkLambdaFVars #[y', hy', hf] hf
      let lamBody ← mkAppOptM ``ofMkFold1SomeLt #[none, inst, ← mkAppM' b prefixNatLikeFVars, fWithPrefix, fWithPrefix, innerLam, h, y, hy]
      mkLambdaFVars #[y, hy, h] lamBody
    | .leUpperBound b =>
      let y ← mkFreshExprMVar t
      let y' ← mkFreshExprMVar t
      let hy ← mkFreshExprMVar $ ← mkAppM ``LE.le #[y, ← mkAppM' b prefixNatLikeFVars]
      let hy' ← mkFreshExprMVar $ ← mkAppM ``LE.le #[y', ← mkAppM' b prefixNatLikeFVars]
      let h ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' arg1 #[y], mkConst ``true]
      let hf ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' fWithPrefix #[y'], mkConst ``true]
      let innerLam ← mkLambdaFVars #[y', hy', hf] hf
      let lamBody ← mkAppOptM ``ofMkFold1SomeLe #[none, inst, ← mkAppM' b prefixNatLikeFVars, fWithPrefix, fWithPrefix, innerLam, h, y, hy]
      mkLambdaFVars #[y, hy, h] lamBody

  trace[brute.debug] "bp5"

  let (computationInnerLamOpt, computationRes, computationResIsTrue) ← buildComputationResBase binderInfosPrefix t f finalBinderInfo.b inst

  trace[brute.debug] "bp5.5"

  let arg3 ← buildArg3 prefixFVars prefixNatLikeFVars binderInfosPrefix t f finalBinderInfo.b inst computationInnerLamOpt computationRes computationResIsTrue

  trace[brute.debug] "bp6"

  let res ←
    match finalBinderInfo.b with
    | .noUpperBound =>
      let ofMkFold1Call ← mkAppOptM ``ofMkFold1None #[none, inst, fWithPrefix, arg1, arg2, arg3]
      let lamBody ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' ofMkFold1Call finalBinderFVars]
      mkLambdaFVars (prefixFVars ++ finalBinderFVars) lamBody
    | .ltUpperBound b =>
      let ofMkFold1Call ← mkAppOptM ``ofMkFold1SomeLt #[none, inst, ← mkAppM' b prefixNatLikeFVars, fWithPrefix, arg1, arg2, arg3]
      let lamBody ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' ofMkFold1Call finalBinderFVars]
      mkLambdaFVars (prefixFVars ++ finalBinderFVars) lamBody
    | .leUpperBound b =>
      let ofMkFold1Call ← mkAppOptM ``ofMkFold1SomeLe #[none, inst, ← mkAppM' b prefixNatLikeFVars, fWithPrefix, arg1, arg2, arg3]
      let lamBody ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' ofMkFold1Call finalBinderFVars]
      mkLambdaFVars (prefixFVars ++ finalBinderFVars) lamBody

  return res

@[tactic brute]
def evalBrute : Tactic
| `(tactic| brute) => withMainContext do
  let pf ← forallTelescope (← getMainTarget).consumeMData (cleanupAnnotations := true) $ fun xs g => do
    trace[brute.debug] "xs: {xs}, g: {g}"
    let binderInfos ← popAllBoundBinders #[] (xs.map Expr.fvarId!) #[]
    match binderInfos.toList with
    | [] => throwError "Goal does not match the form required by brute, consider trying native_decide instead"
    | [⟨x, b, hxbOpt, inst⟩] => bruteBaseCase1 xs g x b hxbOpt inst
    | _ =>
      let unboundFVars := xs.filter
        (fun fvar =>
          !(binderInfos.map (fun b => Expr.fvar b.x)).contains fvar &&
          !((binderInfos.filterMap (fun b => b.hxb)).map Expr.fvar).contains fvar
        )
      bruteCore binderInfos unboundFVars g
  trace[brute.debug] "pf: {pf}"
  trace[brute.debug] "pf type: {← inferType pf}"
  let g ← getMainGoal
  g.assign pf
| _ => throwUnsupportedSyntax

end Brute
