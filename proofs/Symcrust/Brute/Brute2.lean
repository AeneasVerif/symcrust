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

-- **TODO** Modify depending on `b1` and `b2` (currently assume both are `.noUpperBound`)
def buildBruteCase2ComputationRes (t1 t2 f : Expr) (b1 b2 : BoundType) (inst1 inst2 : Expr) : TacticM Expr := do
  let x' ← mkFreshExprMVar t1

  -- `mkFold1 (some b1) (fun x' => mkFold1 (some (b2 x')) (f x') true) true = true`
  -- `mkFold1 (some b1) (fun x' => mkFold1 none (f x') true) true = true`

  /- Depending on b2, `innerLam` is either:
      - `(fun (x' : t1) => mkFold1 (none : Option t2) (f x') true)`
      - `(fun (x' : t1) => mkFold1 (some (b2 x')) (f x') true)` -/
  let innerLamBody ←
    match b2 with
    | .noUpperBound => mkAppOptM ``mkFold1 #[none, inst2, ← mkAppOptM ``none #[t2], ← mkAppM' f #[x'], mkConst ``true]
    | .ltUpperBound b2x => mkAppOptM ``mkFold1 #[none, inst2, ← mkAppM ``some #[b2x], ← mkAppM' f #[x'], mkConst ``true]
    | .leUpperBound b2x => mkAppOptM ``mkFold1 #[none, inst2, ← mkAppM ``some #[b2x], ← mkAppM' f #[x'], mkConst ``true]
  let innerLam ← mkLambdaFVars #[x'] innerLamBody

  /- Depending on b1, `mkFold1Call` is:
    - `mkFold1 (none : Option t1) innerLam true`
    - `mkFold1 (some b1) innerLam true` -/
  let mkFold1Call ←
    match b1 with
    | .noUpperBound => mkAppOptM ``mkFold1 #[none, inst1, ← mkAppOptM ``none #[t1], innerLam, mkConst ``true]
    | .ltUpperBound b1 => mkAppOptM ``mkFold1 #[none, inst1, ← mkAppM ``some #[b1], innerLam, mkConst ``true]
    | .leUpperBound b1 => mkAppOptM ``mkFold1 #[none, inst1, ← mkAppM ``some #[b1], innerLam, mkConst ``true]

  let levels := (collectLevelParams {} mkFold1Call).params.toList
  let auxDeclName ← Term.mkAuxName `_brute
  let decl := Declaration.defnDecl $
    mkDefinitionValEx auxDeclName levels (mkConst ``Bool) mkFold1Call .abbrev .safe [auxDeclName]
  addAndCompile decl

  trace[brute.debug] "{decl_name%} :: decl to be compiled: {mkFold1Call}"

  let rflPrf ← mkEqRefl (toExpr true)
  let levelParams := levels.map .param
  return mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf

def buildBruteCase2Arg3 (xFVars : Array Expr) (t1 t2 f : Expr) (b1 b2 : BoundType) (inst1 inst2 : Expr)
  (computationRes : Expr) : TacticM Expr := do
  match b2 with
  | .noUpperBound =>
    let x' ← mkFreshExprMVar t1

    -- `arg1 = (fun (x' : t1) => mkFold1 (none : Option t2) (fun (_ : t2) => mkFold1 none (f x') true) true)`
    let arg1InnerLamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppOptM ``none #[t2], ← mkAppM' f #[x'], mkConst ``true]
    let arg1InnerLam ← mkLambdaFVars #[← mkFreshExprMVar t2] arg1InnerLamBody
    let arg1LamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppOptM ``none #[t2], arg1InnerLam, mkConst ``true]
    let arg1 ← mkLambdaFVars #[x'] arg1LamBody

    -- `arg2 = (fun (x' : t1) => mkFold1 none (f x') true)`
    let arg2LamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppOptM ``none #[t2], ← mkAppM' f #[x'], mkConst ``true]
    let arg2 ← mkLambdaFVars #[x'] arg2LamBody

    /- Depending on `b1`, `arg3` is equal to:
      - `(fun (x' : t1) => ofMkFold1Triv f x' (none : Option t2))`
      - `(fun (x' : t1) (hx' : x' < b1) => ofMkFold1Triv f x' (none : Option t2))`
      - `(fun (x' : t1) (hx' : x' ≤ b1) => ofMkFold1Triv f x' (none : Option t2))` -/
    let arg3LamBody ← mkAppOptM ``ofMkFold1Triv #[none, none, inst1, inst2, f, x', ← mkAppOptM ``none #[t2]]
    let arg3 ←
      match b1 with
      | .noUpperBound => mkLambdaFVars #[x'] arg3LamBody
      | .ltUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LT.lt #[t1, none, x', b1]
        mkLambdaFVars #[x', hx'] arg3LamBody
      | .leUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LE.le #[t1, none, x', b1]
        mkLambdaFVars #[x', hx'] arg3LamBody

    match b1 with
    | .noUpperBound =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1None #[t1, inst1, arg1, arg2, arg3, computationRes]
      mkAppM' ofMkFold1Res xFVars
    | .ltUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLt #[t1, inst1, b1, arg1, arg2, arg3, computationRes]
      mkAppM' ofMkFold1Res xFVars
    | .leUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLe #[t1, inst1, b1, arg1, arg2, arg3, computationRes]
      mkAppM' ofMkFold1Res xFVars
  | .ltUpperBound b2x => -- **TODO** Need to make `b2x` use `x'` rather than the loose bvar it currently has
    let x' ← mkFreshExprMVar t1

    -- `arg1 = (fun (x' : t1) => mkFold1 (some (b2 x')) (fun (_ : t2) => mkFold1 (some (b2 x')) (f x') true) true)`
    let arg1InnerLamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppM ``some #[b2x], ← mkAppM' f #[x'], mkConst ``true]
    let arg1InnerLam ← mkLambdaFVars #[← mkFreshExprMVar t2] arg1InnerLamBody
    let arg1LamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppM ``some #[b2x], arg1InnerLam, mkConst ``true]
    let arg1 ← mkLambdaFVars #[x'] arg1LamBody

    -- `arg2 = (fun (x' : t1) => mkFold1 (some (b2 x')) (f x') true)`
    let arg2LamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppM ``some #[b2x], ← mkAppM' f #[x'], mkConst ``true]
    let arg2 ← mkLambdaFVars #[x'] arg2LamBody

    /- Depending on `b1`, `arg3` is equal to:
      - `(fun (x' : t1) => ofMkFold1Triv f x' (some (b2 x')))`
      - `(fun (x' : t1) (hx' : x' < b1) => ofMkFold1Triv f x' (some (b2 x')))`
      - `(fun (x' : t1) (hx' : x' ≤ b1) => ofMkFold1Triv f x' (some (b2 x')))` -/
    let arg3LamBody ← mkAppOptM ``ofMkFold1Triv #[none, none, inst1, inst2, f, x', ← mkAppM ``some #[b2x]]
    let arg3 ←
      match b1 with
      | .noUpperBound => mkLambdaFVars #[x'] arg3LamBody
      | .ltUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LT.lt #[t1, none, x', b1]
        mkLambdaFVars #[x', hx'] arg3LamBody
      | .leUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LE.le #[t1, none, x', b1]
        mkLambdaFVars #[x', hx'] arg3LamBody

    match b1 with
    | .noUpperBound =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1None #[t1, inst1, arg1, arg2, arg3, computationRes]
      mkAppM' ofMkFold1Res xFVars
    | .ltUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLt #[t1, inst1, b1, arg1, arg2, arg3, computationRes]
      mkAppM' ofMkFold1Res xFVars
    | .leUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLe #[t1, inst1, b1, arg1, arg2, arg3, computationRes]
      mkAppM' ofMkFold1Res xFVars
  | .leUpperBound b2x => -- **TODO** Need to make `b2x` use `x'` rather than the loose bvar it currently has
    let x' ← mkFreshExprMVar t1

    -- `arg1 = (fun (x' : t1) => mkFold1 (natLikeSucc (b2 x')) (fun (_ : t2) => mkFold1 (natLikeSucc (b2 x')) (f x') true) true)`
    let arg1InnerLamBody ←
      mkAppOptM ``mkFold1 #[none, inst2, ← mkAppOptM ``natLikeSucc #[none, inst2, b2x], ← mkAppM' f #[x'], mkConst ``true]
    let arg1InnerLam ← mkLambdaFVars #[← mkFreshExprMVar t2] arg1InnerLamBody
    let arg1LamBody ←
      mkAppOptM ``mkFold1 #[none, inst2, ← mkAppOptM ``natLikeSucc #[none, inst2, b2x], arg1InnerLam, mkConst ``true]
    let arg1 ← mkLambdaFVars #[x'] arg1LamBody

    -- `arg2 = (fun (x' : t1) => mkFold1 (natLikeSucc (b2 x')) (f x') true)`
    let arg2LamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppOptM ``natLikeSucc #[none, inst2, b2x], ← mkAppM' f #[x'], mkConst ``true]
    let arg2 ← mkLambdaFVars #[x'] arg2LamBody

    /- Depending on `b1`, `arg3` is equal to:
      - `(fun (x' : t1) => ofMkFold1Triv f x' (natLikeSucc (b2 x')))`
      - `(fun (x' : t1) (hx' : x' < b1) => ofMkFold1Triv f x' (natLikeSucc (b2 x')))`
      - `(fun (x' : t1) (hx' : x' ≤ b1) => ofMkFold1Triv f x' (natLikeSucc (b2 x')))` -/
    let arg3LamBody ← mkAppOptM ``ofMkFold1Triv #[none, none, inst1, inst2, f, x', ← mkAppOptM ``natLikeSucc #[none, inst2, b2x]]
    let arg3 ←
      match b1 with
      | .noUpperBound => mkLambdaFVars #[x'] arg3LamBody
      | .ltUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LT.lt #[t1, none, x', b1]
        mkLambdaFVars #[x', hx'] arg3LamBody
      | .leUpperBound b1 =>
        let hx' ← mkFreshExprMVar $ ← mkAppOptM ``LE.le #[t1, none, x', b1]
        mkLambdaFVars #[x', hx'] arg3LamBody

    match b1 with
    | .noUpperBound =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1None #[t1, inst1, arg1, arg2, arg3, computationRes]
      mkAppM' ofMkFold1Res xFVars
    | .ltUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLt #[t1, inst1, b1, arg1, arg2, arg3, computationRes]
      mkAppM' ofMkFold1Res xFVars
    | .leUpperBound b1 =>
      let ofMkFold1Res ← mkAppOptM ``ofMkFold1SomeLe #[t1, inst1, b1, arg1, arg2, arg3, computationRes]
      mkAppM' ofMkFold1Res xFVars

def bruteBaseCase2 (xs : Array Expr) (g : Expr) (x y : FVarId) (b1 b2 : BoundType)
  (hxb1Opt hyb2Opt : Option FVarId) (inst1 inst2 : Expr) : TacticM Expr := do
  let xFVars : Array Expr :=
    match hxb1Opt with
    | some hxb1 => #[.fvar x, .fvar hxb1]
    | none => #[.fvar x]
  let yFVars : Array Expr :=
    match hyb2Opt with
    | some hyb2 => #[.fvar y, .fvar hyb2]
    | none => #[.fvar y]
  let unboundFVars := xs.filter (fun fvar => !xFVars.contains fvar && !yFVars.contains fvar)
  let t1 ← -- `x : t2`
    match inst1 with
    | .app (.app (.const ``IsNatLike.mk _) t) _ => pure t
    | _ => throwError "{decl_name%} :: Invalid IsNatLike instance {inst1}"
  let t2 ← -- `y : t2`
    match inst2 with
    | .app (.app (.const ``IsNatLike.mk _) t) _ => pure t
    | _ => throwError "{decl_name%} :: Invalid IsNatLike instance {inst2}"
  let f ← mkLambdaFVars #[.fvar x, .fvar y] (← mkDecide (← mkForallFVars unboundFVars g))
  let fx ← mkAppM' f #[.fvar x]

  /- `arg1` is one of the following (depending on the bound type of b2)
      - `(fun (_ : t2) => mkFold1 (none : Option t2) (f x) true) : t2 → Bool`
      - `(fun (_ : t2) => mkFold1 (some (b2 x)) (f x) true)`
      - `(fun (_ : t2) => mkFold1 (natLikeSucc (b2 x)) (f x) true)` -/
  let arg1 ←
    match b2 with
    | .noUpperBound =>
      let lamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppOptM ``none #[t2], fx, mkConst ``true]
      pure $ Expr.lam `_ t2 lamBody .default
    | .ltUpperBound b2x =>
      let lamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppM ``some #[b2x], fx, mkConst ``true]
      pure $ Expr.lam `_ t2 lamBody .default
    | .leUpperBound b2x =>
      let lamBody ← mkAppOptM ``mkFold1 #[none, inst2, ← mkAppOptM ``natLikeSucc #[none, inst2, b2x], fx, mkConst ``true]
      pure $ Expr.lam `_ t2 lamBody .default

  /- `arg2` is one of the following (depending on the bound type of b2)
      - `(fun (y : t2) (h : arg1 y = true) => ofMkFold1None (f x) (f x) (fun (y' : t2) (hf : f x y' = true) => hf) h y)`
      - `(fun (y : t2) (hy : y < (b2 x)) (h : arg1 y = true) =>`
            `ofMkFold1SomeLt (b2 x) (f x) (f x) (fun (y' : t2) (hy' : y' < b2 x) (hf : f x y' = true) => hf) h y hy)`
      - `(fun (y : t2) (hy : y ≤ (b2 x)) (h : arg1 y = true) =>`
            `ofMkFold1SomeLe (b2 x) (f x) (f x) (fun (y' : t2) (hy' : y' ≤ b2 x) (hf : f x y' = true) => hf) h y hy)` -/
  let arg2 ←
    match b2 with
    | .noUpperBound =>
      let y ← mkFreshExprMVar t2
      let y' ← mkFreshExprMVar t2
      let h ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' arg1 #[y], mkConst ``true]
      let hf ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' fx #[y'], mkConst ``true]
      let innerLam ← mkLambdaFVars #[y', hf] hf
      let lamBody ← mkAppOptM ``ofMkFold1None #[none, inst2, fx, fx, innerLam, h, y]
      mkLambdaFVars #[y, h] lamBody
    | .ltUpperBound b2x =>
      let y ← mkFreshExprMVar t2
      let y' ← mkFreshExprMVar t2
      let hy ← mkFreshExprMVar $ ← mkAppM ``LT.lt #[y, b2x]
      let hy' ← mkFreshExprMVar $ ← mkAppM ``LT.lt #[y', b2x]
      let h ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' arg1 #[y], mkConst ``true]
      let hf ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' fx #[y'], mkConst ``true]
      let innerLam ← mkLambdaFVars #[y', hy', hf] hf
      let lamBody ← mkAppOptM ``ofMkFold1SomeLt #[none, inst2, b2x, fx, fx, innerLam, h, y, hy]
      mkLambdaFVars #[y, hy, h] lamBody
    | .leUpperBound b2x =>
      let y ← mkFreshExprMVar t2
      let y' ← mkFreshExprMVar t2
      let hy ← mkFreshExprMVar $ ← mkAppM ``LE.le #[y, b2x]
      let hy' ← mkFreshExprMVar $ ← mkAppM ``LE.le #[y', b2x]
      let h ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' arg1 #[y], mkConst ``true]
      let hf ← mkFreshExprMVar $ ← mkAppM ``Eq #[← mkAppM' fx #[y'], mkConst ``true]
      let innerLam ← mkLambdaFVars #[y', hy', hf] hf
      let lamBody ← mkAppOptM ``ofMkFold1SomeLe #[none, inst2, b2x, fx, fx, innerLam, h, y, hy]
      mkLambdaFVars #[y, hy, h] lamBody

  let computationRes ← buildBruteCase2ComputationRes t1 t2 f b1 b2 inst1 inst2
  let arg3 ← buildBruteCase2Arg3 xFVars t1 t2 f b1 b2 inst1 inst2 computationRes

  trace[brute.debug] "x : {Expr.fvar x}"
  trace[brute.debug] "y : {Expr.fvar y}"
  trace[brute.debug] "t1 : {t1}"
  trace[brute.debug] "t2 : {t2}"
  trace[brute.debug] "f : {f}"
  trace[brute.debug] "f type: {← inferType f}"
  trace[brute.debug] "fx : {fx}"
  trace[brute.debug] "fx type: {← inferType fx}"
  trace[brute.debug] "arg1: {arg1}"
  trace[brute.debug] "arg1 type: {← inferType arg1}"
  trace[brute.debug] "arg2: {arg2}"
  trace[brute.debug] "arg2 type: {← inferType arg2}"
  trace[brute.debug] "computationRes: {computationRes}"
  trace[brute.debug] "computationRes type: {← inferType computationRes}"
  trace[brute.debug] "arg3: {arg3}"
  trace[brute.debug] "arg3 type: {← inferType arg3}"

  let res ←
    match b2 with
    | .noUpperBound =>
      let ofMkFold1Call ← mkAppOptM ``ofMkFold1None #[none, inst2, fx, arg1, arg2, arg3]
      let lamBody ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' ofMkFold1Call yFVars]
      mkLambdaFVars (xFVars ++ yFVars) lamBody
    | .ltUpperBound b2x =>
      let ofMkFold1Call ← mkAppOptM ``ofMkFold1SomeLt #[none, inst2, b2x, fx, arg1, arg2, arg3]
      let lamBody ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' ofMkFold1Call yFVars]
      mkLambdaFVars (xFVars ++ yFVars) lamBody
    | .leUpperBound b2x =>
      let ofMkFold1Call ← mkAppOptM ``ofMkFold1SomeLe #[none, inst2, b2x, fx, arg1, arg2, arg3]
      let lamBody ← mkAppOptM ``of_decide_eq_true #[none, none, ← mkAppM' ofMkFold1Call yFVars]
      mkLambdaFVars (xFVars ++ yFVars) lamBody

  trace[brute.debug] "x : {Expr.fvar x}"
  trace[brute.debug] "y : {Expr.fvar y}"
  trace[brute.debug] "t1 : {t1}"
  trace[brute.debug] "t2 : {t2}"
  trace[brute.debug] "f : {f}"
  trace[brute.debug] "f type: {← inferType f}"
  trace[brute.debug] "fx : {fx}"
  trace[brute.debug] "fx type: {← inferType fx}"
  trace[brute.debug] "arg1: {arg1}"
  trace[brute.debug] "arg1 type: {← inferType arg1}"
  trace[brute.debug] "arg2: {arg2}"
  trace[brute.debug] "arg2 type: {← inferType arg2}"
  trace[brute.debug] "arg3: {arg3}"
  trace[brute.debug] "arg3 type: {← inferType arg3}"

  return res

def bruteCore (xs : Array Expr) (g : Expr) (boundBinders : List BinderInfo) : TacticM Expr := do
  match boundBinders with
  | [] => throwError "Goal does not match the form required by brute, consider trying native_decide instead"
  | [⟨x, b, hxbOpt, inst⟩] => bruteBaseCase1 xs g x b hxbOpt inst
  | [⟨x, b1, hxb1Opt, inst1⟩, ⟨y, b2, hyb2Opt, inst2⟩] => bruteBaseCase2 xs g x y b1 b2 hxb1Opt hyb2Opt inst1 inst2
  | ⟨x, b, hxbOpt, inst⟩ :: restBoundBinders =>
    throwError "Not implemented yet"

@[tactic brute]
def evalBrute : Tactic
| `(tactic| brute) => withMainContext do
  let pf ← forallTelescope (← getMainTarget).consumeMData (cleanupAnnotations := true) $ fun xs g => do
    trace[brute.debug] "xs: {xs}, g: {g}"
    let boundBinders ← popAllBoundBinders (xs.map Expr.fvarId!) #[]
    bruteCore xs g boundBinders.toList
  trace[brute.debug] "pf: {pf}"
  trace[brute.debug] "pf type: {← inferType pf}"
  let g ← getMainGoal
  g.assign pf
| _ => throwUnsupportedSyntax

end Brute
