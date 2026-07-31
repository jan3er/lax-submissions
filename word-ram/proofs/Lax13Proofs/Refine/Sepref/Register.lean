import Lax13Proofs.Refine.Sepref.SignaturePrep
import Lax13Proofs.Refine.Sepref.Attrs

/-!
# Sepref operation registration and assertion interfaces

The P1.B port of the active half of `Sepref_Combinator_Setup.thy` and
`Sepref_Rules.thy`'s `intf_of_assn` table.  A registration adds an
`intf_type` theorem to `id_rules`; the existing `IdOp` phase therefore sees
the conceptual type on its next invocation.

The source also emits one arity and one monadification equation for each
monadic constant.  Lean's `Monadify.flattenPass` is arity-polymorphic and
walks arbitrary application spines, so those equations would duplicate the
generic implementation.  The eight-argument gate below is the executable
control for that substitution.
-/

open Lean Elab Meta

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## Assertion-to-interface binding (`Sepref_Rules.thy`, lines 32--41) -/

/-- The source's True-valued `intf_of_assn` judgment.  Its propositions are
configuration records consumed by `inferAssnInterface`, not logical data. -/
def intfOfAssn {α κ : Type} (_R : α → κ → Assn) (_I : Type) : Prop := True

@[simp] theorem intfOfAssn_def {α κ : Type} (R : α → κ → Assn) (I : Type) :
    intfOfAssn R I ↔ True := Iff.rfl

theorem intfOfAssnI {α κ : Type} (R : α → κ → Assn) (I : Type) :
    intfOfAssn R I := trivial

namespace Register

/-- Instantiate an `intf_of_assn` declaration and expose its relation and
interface slots. -/
def assnInterfacePairs : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for n in ← Lean.labelled `intf_of_assn do
    let (_, _, ty) ← forallMetaTelescope (← IdOp.ruleType n)
    match ty.getAppFnArgs with
    | (``intfOfAssn, #[_, _, R, I]) => out := out.push (R, I)
    | _ => pure ()
  return out

/-- Abstract carrier of an assertion relation, used by the source's
`intf_of_assn_fallback` when no configured conceptual interface matches. -/
def assnAbstractType (R : Expr) : MetaM Expr := do
  match ← whnf (← inferType R) with
  | .forallE _ α _ _ => return α
  | ty => throwError "sepref_register: expected an assertion relation, but got{indentExpr ty}"

/-- Resolve an assertion relation through `intf_of_assn`, followed by the
source's abstract-carrier fallback. -/
def inferAssnInterface (R : Expr) : MetaM Expr := do
  for (pat, I) in ← assnInterfacePairs do
    if ← withReducible (isDefEq pat R) then
      return ← instantiateMVars I
  assnAbstractType R

/-- Build the conceptual type of a monadic operator from its parameter and
result assertion relations. -/
def monadicInterface (args : Array Expr) (result : Expr) : MetaM Expr := do
  let mut out ← mkAppM ``NRest #[← inferAssnInterface result, mkConst ``ECost]
  for R in args.reverse do
    out ← mkArrow (← inferAssnInterface R) out
  return out

/-- Check the source-level invariant that registration describes all
parameters of a monadic operator. -/
def checkArity (op : Expr) (arity : Nat) : MetaM Unit := do
  let mut ty ← inferType op
  for _ in [:arity] do
    match ← whnf ty with
    | .forallE _ _ body _ => ty := body
    | finalTy => throwError "sepref_register: supplied {arity} input assertions, but the operator has type{indentExpr finalTy}"
  let finalTy ← whnf ty
  match finalTy.getAppFnArgs with
  | (``NRest, #[_, _]) => pure ()
  | _ => throwError "sepref_register: the operator's result is not NRest:{indentExpr finalTy}"

/-- Add `<basename>_itype : op ::ᵢ I` and register it in `id_rules`. -/
def addRegistration (declName : Name) (op I : Expr) : TermElabM Unit := do
  let type ← mkAppOptM ``intf_type #[none, some op, some I]
  let value ← mkAppM ``itypeI #[op, I]
  let type ← Term.levelMVarToParam (← instantiateMVars type)
  let value ← Term.levelMVarToParam (← instantiateMVars value)
  let us := (collectLevelParams (collectLevelParams {} type) value).params
  addDecl (.thmDecl { name := declName, levelParams := us.toList, type, value })
  let some ext := (← Lean.labelExtensionMapRef.get)[`id_rules]?
    | throwError "sepref_register: id_rules attribute is unavailable"
  ext.add declName .global
  logInfo m!"sepref_register {declName}:{indentExpr type}"

end Register

/-! ## Commands -/

open Register in
/-- Register a monadic operation from the assertion relations on all of its
arguments and result.  This is the assertion-directed form needed by large
signatures. -/
elab "sepref_register" nm:ident " : " op:term " using " "[" args:term,* "]"
    " => " result:term : command => do
  Command.liftTermElabM do
    let op ← Term.elabTerm op none
    let args ← args.getElems.mapM (Term.elabTerm · none)
    let result ← Term.elabTerm result none
    Term.synthesizeSyntheticMVarsNoPostponing
    checkArity op args.size
    let I ← monadicInterface args result
    let declName := ((← getCurrNamespace) ++ nm.getId).appendAfter "_itype"
    addRegistration declName (← instantiateMVars op) (← instantiateMVars I)

open Register in
/-- Register an operation at an explicitly supplied conceptual type, the
source's `:: TYPE(...)` escape hatch. -/
elab "sepref_register" nm:ident " : " op:term " as " I:term : command => do
  Command.liftTermElabM do
    let op ← Term.elabTerm op none
    let I ← Term.elabType I
    Term.synthesizeSyntheticMVarsNoPostponing
    let declName := ((← getCurrNamespace) ++ nm.getId).appendAfter "_itype"
    addRegistration declName (← instantiateMVars op) (← instantiateMVars I)

/-! ## Eight-array acceptance gate -/

namespace RegisterGate

noncomputable section

/-- A deliberately distinct conceptual array interface. -/
opaque ArrayI : Type

/-- Test assertion with the same concrete ownership as `arrayAssn` but an
interface override discoverable only through `intf_of_assn`. -/
def arrayIAssn : List ℕ → String → Assn := arrayAssn

@[intf_of_assn] theorem intfOfAssn_arrayI : intfOfAssn arrayIAssn ArrayI := trivial

opaque wideArrayOp :
  List ℕ → List ℕ → List ℕ → List ℕ → List ℕ → List ℕ → List ℕ → List ℕ →
    NRest ℕ ECost

sepref_register wideArrayOp : wideArrayOp using [
  arrayIAssn, arrayIAssn, arrayIAssn, arrayIAssn,
  arrayIAssn, arrayIAssn, arrayIAssn, arrayIAssn] => natAssn

example : wideArrayOp ::ᵢ
    (ArrayI → ArrayI → ArrayI → ArrayI → ArrayI → ArrayI → ArrayI → ArrayI →
      NRest ℕ ECost) :=
  wideArrayOp_itype

opaque explicitOp : ℕ → NRest ℕ ECost

sepref_register explicitOp : explicitOp as (Bool → NRest ℕ ECost)

example : explicitOp ::ᵢ (Bool → NRest ℕ ECost) := explicitOp_itype

/- TYPE annotations override the registered interface at an occurrence. -/
example : ID (wideArrayOp :::ᵢ Bool) (wideArrayOp :::ᵢ Bool) Bool := by
  sepref_id_op

end

end RegisterGate

end Lax13Proofs.Refine.Sepref
