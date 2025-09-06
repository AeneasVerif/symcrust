import Lean
import Aeneas
import Symcrust.Brute.BruteLemmasOld

open Lean Meta Parser Elab Tactic Aeneas Aeneas.Std

initialize registerTraceClass `brute.debug

namespace Brute

/-- A terminal tactic that attempts to prove goals of the form `∀ x y z ..., f x y z ...` via brute force.
    This version of `brute` only supports goals consisting of a string of universally quantified upper-bounded
    Nat-like types followed by a decidable function `f` (e.g. `∀ a < x₁, ∀ b < x₂ f a b` where the types of
    `a` and `b` have `IsNatLike` instances). Additionally, this version of `brute` only supports goals with at most
    five bounded quantifiers. -/
syntax (name := brute) "brute" : tactic

/-- A structure that holds info for binders of the form `∀ x < b, ...`-/
structure BinderInfo where
  x : FVarId -- The universally quantified variable.
  b : Expr -- The value that the variable is upper bounded by. `b` cannot contain `x`
  hxb : FVarId -- The variable whose type is `x < b`.
  isNatLikeInst : Expr -- An Expr whose type is `IsNatLike t` where `x : t` and `b : t`.

instance : ToMessageData BinderInfo where
  toMessageData := fun ⟨x, b, hxb, isNatLikeInst⟩ => m!"({Expr.fvar x}, {b}, {Expr.fvar hxb}, {isNatLikeInst})"

/-- Retrieves the `UScalarTy` associated with a `U_` abbreviation -/
def getSizeTyFromAbbrev (t : Expr) : Option Expr :=
  match t with
  | .const ``U8 _ => some $ mkConst ``UScalarTy.U8
  | .const ``U16 _ => some $ mkConst ``UScalarTy.U16
  | .const ``U32 _ => some $ mkConst ``UScalarTy.U32
  | .const ``U64 _ => some $ mkConst ``UScalarTy.U64
  | .const ``U128 _ => some $ mkConst ``UScalarTy.U128
  | _ => none

/-- If `t` is an Expr corresponding to `Nat`, `BitVec n`, or `UScalar t'` (where `t' ≠ Usize`), then
    `getIsNatLike` returns an Expr whose type is `IsNatLike t`. Otherwise, `getIsNatLike` returns `none`. -/
def getIsNatLikeInstance (t : Expr) : MetaM (Option Expr) := do
  match t with
  | .const ``Nat _ =>
    -- `rflPf := (rfl : t = Nat)`
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    -- `isNatPf := (isNatPf rflPf : IsNatLikePf t)`
    let isNatPf ← mkAppOptM ``IsNatLikePf.isNatPf #[none, rflPf]
    -- `inst := (IsNatLike.mk isNatPf : IsNatLike t)`
    let inst ← mkAppM ``IsNatLike.mk #[isNatPf]
    return some inst
  | .app (.const ``BitVec _) n =>
    -- `rflPf := (rfl : t = t)`
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    -- `pSigmaβBody := (t = BitVec (Expr.bvar 0))`. This is not well typed until enclosed in a lambda
    let pSigmaβBody :=
      mkApp3 (mkConst ``Eq [2]) (.sort 1) (.app (.const ``BitVec []) n) (.app (.const ``BitVec []) (.bvar 0))
    -- `pSigmaβ := (λ (n : Nat) => pSigmaβBody : ∀ n, Sort _)`
    let pSigmaβ := Expr.lam `n (mkConst ``Nat) pSigmaβBody .default
    -- `pSigmaPf := (PSigma.mk n rflPf : PSigma pSigmaβ`
    let pSigmaPf ← mkAppOptM ``PSigma.mk #[none, some pSigmaβ, n, rflPf]
    -- `isBitVecPf := (IsNatLikePf.isBitVecPf pSigmaPf : IsNatLikePf t)`
    let isBitVecPf ← mkAppOptM ``IsNatLikePf.isBitVecPf #[none, pSigmaPf]
    -- `inst := (IsNatLike.mk isBitVecPf : IsNatLike t)`
    let inst ← mkAppM ``IsNatLike.mk #[isBitVecPf]
    return some inst
  | .app (.const ``UScalar _) (.const ``Usize _) => return none
  | .app (.const ``UScalar _) sizeTy => -- Matches with all `UScalar` types except `Usize`
    -- `rflPf := (rfl : t = t)`
    let rflPf ← mkAppOptM ``Eq.refl #[some (.sort 1), some t]
    -- `sizeTyNeUsizePf := (UScalarTy.noConfusion : sizeTy = Usize → False)`
    let sizeTyNeUsizePf ← mkAppOptM ``UScalarTy.noConfusion #[mkConst ``False, sizeTy, mkConst ``Usize]
    -- `andPf : (⟨sizeTyNeUsizePf, rflPf⟩ : sizeTy = Usize → False ∧ t = t`
    let andPf ← mkAppM ``And.intro #[sizeTyNeUsizePf, rflPf]
    -- `pSigmaβBody := (((Expr.bvar 0) ≠ Usize) ∧ (UScalar sizeTy = UScalar (Expr.bvar 0)))`. This is not well typed until enclosed in a lambda
    let pSigmaβBody :=
      mkApp2 (mkConst ``And)
        (mkApp3 (mkConst ``Ne [2]) (.sort 1) (.bvar 0) (mkConst ``Usize))
        (mkApp3 (mkConst ``Eq [2]) (.sort 1)
          (.app (.const ``UScalar []) sizeTy)
          (.app (.const ``UScalar []) (.bvar 0))
        )
    -- `pSigmaβ := ((λ t' : UScalarTy => pSigmaβBody) : ∀ t', Sort _)`
    let pSigmaβ := Expr.lam `t' (mkConst ``UScalarTy) pSigmaβBody .default
    -- `pSigmaPf := (PSigma.mk sizeTy andPf : PSigma pSigmaβ)`
    let pSigmaPf ← mkAppOptM ``PSigma.mk #[none, pSigmaβ, sizeTy, andPf]
    -- `isUScalarPf := (IsNatLikePf.isUScalarPf pSigmaPf : IsNatLikePf t)`
    let isUScalarPf ← mkAppOptM ``IsNatLikePf.isUScalarPf #[none, pSigmaPf]
    -- `inst := (IsNatLike.mk isUScalarPf : IsNatLike t)`
    let inst ← mkAppM ``IsNatLike.mk #[isUScalarPf]
    return some inst
  | .const ``U8 _ | .const ``U16 _ | .const ``U32 _ | .const ``U64 _ | .const ``U128 _ =>
    -- This code is identical to the preceding case except that `getSizeTyFromAbbrev` is called to obtain `sizeTy`
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
    let pSigmaβ := Expr.lam `t' (mkConst ``UScalarTy) pSigmaβBody .default
    let pSigmaPf ← mkAppOptM ``PSigma.mk #[none, pSigmaβ, sizeTy, andPf]
    let isUScalarPf ← mkAppOptM ``IsNatLikePf.isUScalarPf #[none, pSigmaPf]
    let inst ← mkAppM ``IsNatLike.mk #[isUScalarPf]
    return some inst
  | _ => return none

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

/-- Iterates through `goalBinders` and gathers as many pairs of binders of the form `∀ x < b` as `goalBinders`
    allows. `popAllBoundBinders` then returns an array of the corresponding `BinderInfo`s. Note that the total
    number of `goalBinders` may exceed the number of binder pairs gathered by `popBoundBinders` if `goalBinders`
    contains binders that are not of the form `∀ x < b`.

    For example, from the original goal `∀ x < b, ∀ y < x, ∀ z : Fin y, f x y z`, `goalBinders` would be
    `#[x : Nat, hx : x < b, y : Nat, hy : y < x, z : Fin y]` and `popAllBoundBinders` would
    return the BinderInfos for `(x, hx)` and `(y, hy)`. -/
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
    /-  This version of `brute` produces a hardcoded proof which depends on the total number of bound binders.
        If there are `N` bound binders, then `brute`:
        - Builds a call to `mkFoldN`, with the appropriate arguments
        - Compiles that call into a definition with the auxiliary definition `_brute`
          - This step is required because `Lean.ofReduceBool`, the axiom which allows `brute` and `native_decide`
            to trust the compiler's evaluation, requires that the argument it is provided is a constant. See
            the docstrings for `Lean.ofReduceBool` and `Lean.reduceBool` for more details.
        - Uses the compiler to confirm that the compiled definition evaluates to `true` (by invoking `Lean.ofReduceBool`)
        - Constructs a proof term for the original goal using `ofMkFoldNEqTrue`

       Each of the cases below are extremely similar, only substantively differing in which `mkFoldN` and
       `ofMkFoldNEqTrue` constants to use. -/
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

end Brute
