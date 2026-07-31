import Lax13Proofs.Refine.Sepref.Register
import Lax13Proofs.Refine.Sepref.SignatureTool

/-!
# Interface operation and implementation declarations

Tower-expansion P1.C's Lean rendering of the active declaration layer in
the pinned `Sepref_Combinator_Setup.thy` and `Sepref_Intf_Util.thy`.

The source commands do three distinct jobs:

* `sepref_decl_intf` introduces a nominal conceptual type and records its
  logical carrier;
* `sepref_decl_op` defines an operation and its precondition, checks and
  registers its conceptual type, and records the proved `fref` fact;
* `sepref_decl_impl` composes a raw heap rule with that `fref` fact through
  `FCOMP`, then registers the result as a translation rule.

Isabelle's commands synthesize the parametricity goal from its relation
syntax. Lean has no separate relation-type parser: the command therefore
takes the fully elaborated `fref` statement and its proof. This is an
explicit-proof frontend delta, not a semantic one—the generated facts and
the implementation composition are the same public judgments, and callers
never invoke metaprogramming or `FCOMP` themselves.
-/

open Lean Elab Meta

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## Interface configuration judgments -/

/-- True-valued nominal-interface rewrite record, corresponding to the
source's private `__itype_rewrite` theorem collection. -/
def interfaceTypeEq (_I _T : Type) : Prop := True

@[simp] theorem interfaceTypeEq_def (I T : Type) : interfaceTypeEq I T ↔ True := Iff.rfl

theorem interfaceTypeEqI (I T : Type) : interfaceTypeEq I T := trivial

/-- The source's True-valued `INTF_OF_REL` configuration judgment. -/
def intfOfRel {α β : Type} (_R : Set (α × β)) (_I : Type) : Prop := True

@[simp] theorem intfOfRel_def {α β : Type} (R : Set (α × β)) (I : Type) :
    intfOfRel R I ↔ True := Iff.rfl

theorem intfOfRelI {α β : Type} (R : Set (α × β)) (I : Type) : intfOfRel R I := trivial

namespace IntfUtil

/-- Instantiate nominal-interface rewrite declarations. -/
def interfaceTypePairs : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for n in ← Lean.labelled `sepref_itype_rewrite do
    let (_, _, ty) ← forallMetaTelescope (← IdOp.ruleType n)
    match ty.getAppFnArgs with
    | (``interfaceTypeEq, #[I, T]) => out := out.push (I, T)
    | _ => pure ()
  return out

/-- Instantiate configured relation-interface declarations. -/
def relInterfacePairs : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for n in ← Lean.labelled `intf_of_rel do
    let (_, _, ty) ← forallMetaTelescope (← IdOp.ruleType n)
    match ty.getAppFnArgs with
    | (``intfOfRel, #[_, _, R, I]) => out := out.push (R, I)
    | _ => pure ()
  return out

/-- Abstract/right carrier of a relation, used by the source's fallback. -/
def relAbstractType (R : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType R)
  let pair ← match ty with
    | .forallE _ pair body _ =>
        match body with
        | .sort .zero => pure ()
        | _ => throwError "INTF_OF_REL: expected a set-valued relation, got{indentExpr ty}"
        pure pair
    | _ => throwError "INTF_OF_REL: expected a set-valued relation, got{indentExpr ty}"
  match ← whnf pair with
  | .app (.app (.const ``Prod _) _) abstract => return abstract
  | _ => throwError "INTF_OF_REL: expected a binary relation, got{indentExpr ty}"

/-- Resolve a relation through `intf_of_rel`, followed by the source's
abstract-carrier fallback. -/
partial def inferRelInterface (R : Expr) : MetaM Expr := do
  for (pat, I) in ← relInterfacePairs do
    if ← withReducible (isDefEq pat R) then
      return ← instantiateMVars I
  let (head, args) := R.consumeMData.getAppFnArgs
  if head == ``listRel && !args.isEmpty then
    return ← mkAppM ``List #[← inferRelInterface args.back!]
  if head == ``optionRel && !args.isEmpty then
    return ← mkAppM ``Option #[← inferRelInterface args.back!]
  if head == ``prodRel && args.size >= 2 then
    return ← mkAppM ``Prod
      #[← inferRelInterface args[args.size - 2]!, ← inferRelInterface args.back!]
  if head == ``sumRel && args.size >= 2 then
    return ← mkAppM ``Sum
      #[← inferRelInterface args[args.size - 2]!, ← inferRelInterface args.back!]
  if head == ``funRel && args.size >= 2 then
    return ← mkArrow
      (← inferRelInterface args[args.size - 2]!) (← inferRelInterface args.back!)
  if head == ``NRest.nrestRel && !args.isEmpty then
    let inner ← inferRelInterface args.back!
    match (← relAbstractType R).getAppFnArgs with
    | (n, #[_, cost]) =>
        if n == ``NRest then return ← mkAppM ``NRest #[inner, cost]
        else pure ()
    | _ => pure ()
  relAbstractType R

/-- Rewrite nominal interface atoms, then recurse through type application
and function space. This is the source's `normalize_itype` role. -/
partial def normalizeInterfaceType (e : Expr) : MetaM Expr := do
  for (pat, rhs) in ← interfaceTypePairs do
    if ← withReducible (isDefEq pat e) then
      return ← instantiateMVars rhs
  match e with
  | .forallE n dom body bi =>
      let dom' ← normalizeInterfaceType dom
      withLocalDecl n bi dom' fun x => do
        let body' ← normalizeInterfaceType (body.instantiate1 x)
        mkForallFVars #[x] body'
  | .app f a =>
      let f' ← normalizeInterfaceType f
      let a' ←
        try
          if (← inferType a).isSort then normalizeInterfaceType a else pure a
        catch _ => pure a
      return mkApp f' a'
  | _ => return e

/-- Enforce the source invariant that a conceptual interface normalizes to
the operation's actual logical type. -/
def checkOperationInterface (op I : Expr) : MetaM Unit := do
  let actual ← instantiateMVars (← inferType op)
  let logical ← instantiateMVars (← normalizeInterfaceType I)
  unless ← withReducible (isDefEq actual logical) do
    throwError "sepref_decl_op: conceptual interface does not normalize to the operation type\n  operation:{indentExpr actual}\n  interface:{indentExpr I}\n  normalized:{indentExpr logical}"

def prefixed (pfx : String) : Name → Name
  | .str p s => .str p (pfx ++ s)
  | n => .str n pfx

def suffixed (suffix : String) (n : Name) : Name := n.appendAfter suffix

end IntfUtil

/-! ## Commands -/

/-- Declare a nominal conceptual interface. Type parameters use the same
compact shape as the source, for example
`sepref_decl_intf (α, β) MapI is α → Option β`. -/
syntax (name := seprefDeclIntf)
  "sepref_decl_intf " ("(" ident,* ")")? ident " is " term : command

elab_rules : command
  | `(command| sepref_decl_intf $[($args,*)]? $nm:ident is $logical:term) => do
      let xs : Array (TSyntax `ident) := args.map (·.getElems) |>.getD #[]
      let xterms : Array (TSyntax `term) := xs.map fun x => ⟨x.raw⟩
      let rwName : TSyntax `ident := ⟨mkIdentFrom nm (nm.getId.appendAfter "_itype_rewrite")⟩
      let lhs ← `(term| $nm $xterms*)
      if xs.isEmpty then
        Command.elabCommand (← `(command| opaque $nm : Type))
      else
        Command.elabCommand (← `(command| opaque $nm ($xs* : Type) : Type))
      if xs.isEmpty then
        Command.elabCommand (← `(command|
          @[sepref_itype_rewrite] theorem $rwName :
              interfaceTypeEq $lhs $logical := trivial))
      else
        Command.elabCommand (← `(command|
          @[sepref_itype_rewrite] theorem $rwName ($xs* : Type) :
              interfaceTypeEq $lhs $logical := trivial))

/-- Internal checked registration step used by `sepref_decl_op`. -/
elab "sepref_decl_op_check " op:term " as " I:term : command => do
  Command.liftTermElabM do
    let op ← Term.elabTerm op none
    let I ← Term.elabType I
    Term.synthesizeSyntheticMVarsNoPostponing
    IntfUtil.checkOperationInterface (← instantiateMVars op) (← instantiateMVars I)

/-- Executable inspection form for the relation-interface synthesizer. -/
elab "#guard_rel_interface " R:term " is " I:term : command => do
  Command.liftTermElabM do
    let R ← Term.elabTerm R none
    let I ← Term.elabType I
    Term.synthesizeSyntheticMVarsNoPostponing
    let actual ← IntfUtil.inferRelInterface (← instantiateMVars R)
    unless ← withReducible (isDefEq actual (← instantiateMVars I)) do
      throwError "#guard_rel_interface failed\n  inferred:{indentExpr actual}\n  expected:{indentExpr I}"

/-- Declare one monadic interface operation. The command defines
`op_<name>` and `pre_<name>`, checks/registers the conceptual interface,
and stores `op_<name>_fref` in `sepref_fref_thms`.

The body is explicitly monadic. Pure source operations are written as
`NRest.returnT ...`; preconditioned source mops include their `assert` in
the body. This makes the cost-carrying operation boundary visible. -/
syntax (name := seprefDeclOp)
  "sepref_decl_op " ident (ppSpace bracketedBinder)* " : " term " := " term
  ppLine "interface" " := " term
  ppLine "precondition" " := " term
  ppLine "parametricity" " : " term " := " term : command

elab_rules : command
  | `(command| sepref_decl_op $base:ident $bs* : $ty:term := $body:term
        interface := $I:term
        precondition := $preTerm:term
        parametricity : $frefTy:term := $proof:term) => do
      let opId : TSyntax `ident := ⟨mkIdentFrom base (IntfUtil.prefixed "op_" base.getId)⟩
      let preId : TSyntax `ident := ⟨mkIdentFrom base (IntfUtil.prefixed "pre_" base.getId)⟩
      let regId : TSyntax `ident :=
        ⟨mkIdentFrom base (IntfUtil.suffixed "_registration" opId.getId)⟩
      let frefId : TSyntax `ident :=
        ⟨mkIdentFrom base (IntfUtil.suffixed "_fref" opId.getId)⟩
      Command.elabCommand (← `(command|
        noncomputable def $opId $bs* : $ty := $body))
      Command.elabCommand (← `(command| def $preId $bs* := $preTerm))
      Command.elabCommand (← `(command| sepref_decl_op_check $opId as $I))
      Command.elabCommand (← `(command| sepref_register $regId : $opId as $I))
      Command.elabCommand (← `(command|
        @[sepref_fref_thms] theorem $frefId $bs* : $frefTy := $proof))

/-- Compose a raw heap rule with an interface operation's `fref` theorem,
then register the checked result. The trailing proof solves exactly the
visible `attainsSup`/normalization obligations left by `sepref_fcomp_checked`.
-/
syntax (name := seprefDeclImpl)
  "sepref_decl_impl " ident " : " term
  ppLine "using " term ", " term " := " term : command

elab_rules : command
  | `(command| sepref_decl_impl $nm:ident : $target:term
        using $raw:term, $frefRule:term := $proof:term) => do
      Command.elabCommand (← `(command|
        @[sepref_fr_rules] theorem $nm : $target := by
          sepref_fcomp_checked $raw, $frefRule
          exact $proof))

/-! ## Full declaration-layer acceptance gate -/

namespace IntfUtilGate

noncomputable section

sepref_decl_intf CounterI is Unit

sepref_decl_intf (α, β) PairI is α × β

example (α β : Type) : interfaceTypeEq (PairI α β) (α × β) :=
  PairI_itype_rewrite α β

/-- A heap relation associated with the new nominal interface. -/
abbrev counterAssn : Unit → Unit → Assn := fun _ _ => (□ : Assn)

@[intf_of_assn] theorem counterAssn_intf : intfOfAssn counterAssn CounterI := trivial

@[intf_of_rel] theorem counterRel_intf :
    intfOfRel (Set.diagonal Unit) CounterI := trivial

#guard_rel_interface (Set.diagonal Unit) is CounterI

-- Standard relators preserve configured nominal interfaces recursively.
#guard_rel_interface (listRel (Set.diagonal Unit)) is List CounterI
#guard_rel_interface (prodRel (Set.diagonal Unit) (Set.diagonal Unit)) is
  CounterI × CounterI

-- An unconfigured relation follows the abstract-carrier fallback.
#guard_rel_interface (Set.univ : Set (ℕ × Bool)) is Bool

sepref_decl_op pairRead (α β : Type) : α × β → NRest (α × β) ECost :=
    fun x => NRest.returnT x
  interface := ∀ α β : Type, PairI α β → NRest (α × β) ECost
  precondition := (fun _ : α × β => True)
  parametricity : ((op_pairRead α β, op_pairRead α β) ∈
      fref (fun _ : α × β => True) (Set.diagonal (α × β))
        (fun _ => NRest.nrestRel (Set.diagonal (α × β)))) := by
    intro x y _ hxy
    change x = y at hxy
    subst y
    exact NRest.nrestRel_of_le (le_of_eq (NRest.concFun_diagonal _).symm)

example : op_pairRead ::ᵢ
    (∀ α β : Type, PairI α β → NRest (α × β) ECost) :=
  op_pairRead_registration_itype

sepref_decl_op counterRead : Unit → NRest ℕ ECost := fun _ => NRest.returnT 7
  interface := CounterI → NRest ℕ ECost
  precondition := (fun _ : Unit => True)
  parametricity : ((op_counterRead, op_counterRead) ∈
      fref (fun _ : Unit => True) (Set.diagonal Unit)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ))) := by
    intro x y _ hxy
    cases x
    cases y
    exact NRest.nrestRel_of_le (le_of_eq (NRest.concFun_diagonal _).symm)

example : op_counterRead ::ᵢ (CounterI → NRest ℕ ECost) :=
  op_counterRead_registration_itype

sepref_decl_impl counterRead_impl :
    (SignatureGate.signatureConstFun, op_counterRead) ∈
      hfref
        (compPRE (Set.diagonal Unit) (fun _ => True) (fun _ _ => True)
          (fun x => (op_counterRead x).nofailT))
        SignatureGate.signatureRS (fun _ _ => natAssn)
  using SignatureGate.signature_hfref, op_counterRead_fref :=
    fun _ _ => attains_sup_sv singleValued_diagonal

-- The implementation command really entered the public rule database.
run_cmd do
  let rules ← Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  unless rules.contains ``counterRead_impl do
    throwError "sepref_decl_impl gate: generated theorem was not registered"

/-- info: 'Lax13Proofs.Refine.Sepref.IntfUtilGate.counterRead_impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterRead_impl

end

end IntfUtilGate

end Lax13Proofs.Refine.Sepref
