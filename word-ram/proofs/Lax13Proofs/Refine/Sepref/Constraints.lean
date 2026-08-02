import Lax13Proofs.Refine.Sepref.Attrs
import Lax13Proofs.Refine.Sepref.Basic
import Lax13Proofs.Refine.Autoref.Solver

/-!
Deferred constraints: the port of `thys/sepref/Sepref_Constraints.thy`.

Source pin as `Sepref/Basic.lean`'s header: `isabelle_llvm_time`
@ `42dd7f5` (full SHA `42dd7f59998d76047bb4b6bce76d8f67b53a08b6`),
`thys/sepref/Sepref_Constraints.thy`, fetched whole (420 lines) and
quoted in `plans/word-ram/refinement-tower/p4-sepref-deep-extracts.md`
§5. The theory is 48 lines of object level and 370 of ML; the object
level is ported verbatim below, and the ML — `WITH_SLOT` / `ON_SLOT` /
`create_slot_tac` / `ensure_slot_tac` / `to_slot_tac` /
`solve_constraint_tac` / `safe_constraint_tac` / `constraint_tac` /
`process_constraint_slot` / `solve_constraint_slot` — is re-expressed as
a `MetaM` store plus three tactics.

## Judgment calls

**P4/D-cd — the SLOT is data, not a subgoal.** The source keeps deferred
constraints in a *designated subgoal* of the proof state:
`CONSTRAINT_SLOT (PROP P &&& PROP Q &&& …)`, created by
`create_slot_tac` (`Thm.implies_intr` of `CONSTRAINT_SLOT True`, then
`defer_tac`) and folded into with `insert_slot_rl1`/`insert_slot_rl2`.
That design is forced by Isabelle's substrate: an ML tactic is a
`thm -> thm Seq.seq`, so the *only* channel a tactic has for carrying
state from one step of a proof to another is the goal list itself, and a
goal that must survive arbitrary later tactics has to be protected by a
constant those tactics do not match. Lean's `MetaM` has ordinary mutable
state and first-class `MVarId`s, so the store is an `IO.Ref` holding the
postponed metavariables and the goal list is left alone. Everything the
source's slot buys is kept: constraints accumulate across the whole
synthesis, are processed once at the end, and an unsolved one surfaces
by name. What is *not* kept is the source's ability to `apply` a tactic
to the slot from Isar — the debugging entry points (`sepref_dbg_print_slot`,
`sepref_dbg_constraints`) replace it. Fallback if a consumer needs the
constraints as real goals: `sepref_dbg_constraints` already returns them
as goals; make that the default and drop the store.

**P4/D-ce — one solver, dispatched through the P2 registry.** The
source's `constraint_tac` is a bespoke pair of rule nets
(`constraint_rules` / `safe_constraint_rules`) with a `SAFE` combinator
distinguishing "this rule application is unique" from "this one
backtracks". Both nets are ported as label databases; the *dispatch* into
them is a `TaggedSolver` (`Autoref/Solver.lean`, wave B2), registered for
the head constant `CONSTRAINT`, which is what the brief asks for and
what makes `Sepref/Translate.lean`'s side-condition dispatcher a
one-liner. The `SAFE`-versus-unsafe distinction survives as the two
databases and the order in which `solveStep` consults them.

**P4/D-cf — `CONSTRAINT is_pure R` is the shape that works end to end.**
It is the only constraint waves A–B generate (`recover_pure`,
`frame_thms` 3–5). The safe rules registered below decide it for every
assertion the IR layer defines: `pureAssn` and `invalidAssn` are pure,
`natAssn` and `arrayAssn` are *not*, and the latter two are flagged with
`CN_FALSE` exactly as the source prescribes ("adding safe rules
introducing this can be used to indicate unsolvable constraints early"),
so a synthesis that demands purity of an owning assertion fails at the
constraint rather than in the slot.

**P4/D-cg — `split_constraint_rls` is absent.** The source's
`atomize_conj[symmetric] imp_conjunction all_conjunction conjunction_imp`
turn Isabelle's meta-conjunction `&&&` into object conjunction so that a
composite constraint can be split. Lean has no `&&&`: a rule with several
premises produces several goals, and each is stored separately. Nothing
to port.
-/

open Lean Elab Meta

universe u

namespace Lax13Proofs.Refine.Sepref

open Ir

/-! ## 1. The object level (source lines 6–47) -/

/-- The source's `CONSTRAINT P x ≡ P x`, its `[simp]` included below. A
tag: it marks a side condition as *deferrable* — solvable now if the
rules decide it, and postponed to the constraint store otherwise. -/
def CONSTRAINT {α : Sort u} (P : α → Prop) (x : α) : Prop := P x

@[simp] theorem CONSTRAINT_def {α : Sort u} (P : α → Prop) (x : α) :
    CONSTRAINT P x ↔ P x := Iff.rfl

/-- The source's `CONSTRAINT_D`. -/
theorem CONSTRAINT_D {α : Sort u} {P : α → Prop} {x : α} (h : CONSTRAINT P x) : P x := h

/-- The source's `CONSTRAINT_I`. -/
theorem CONSTRAINT_I {α : Sort u} {P : α → Prop} {x : α} (h : P x) : CONSTRAINT P x := h

/-- The source's `CN_FALSE P x ≡ False`: "Special predicate to indicate
unsolvable constraint. The constraint solver refuses to put those into
slot. Thus, adding safe rules introducing this can be used to indicate
unsolvable constraints early." -/
def CN_FALSE {α : Sort u} (_P : α → Prop) (_x : α) : Prop := False

@[simp] theorem CN_FALSE_def {α : Sort u} (P : α → Prop) (x : α) :
    CN_FALSE P x ↔ False := Iff.rfl

/-- The source's `CN_FALSEI`. -/
theorem CN_FALSEI {α : Sort u} {P : α → Prop} {x : α} (h : CN_FALSE P x) : P x :=
  absurd h (by simp)

/-! ## 2. The purity rule base (P4/D-cf)

`safe_constraint_rules` in the source's sense: unconditional (so they
*must* be safe, by its own `check_unsafe_constraint_rl`) or uniquely
applicable. -/

-- `pure R` is pure — wave A's `pure_pure`, in the database.
attribute [safe_constraint_rules] pure_pure

/-- `invalid_assn R` is pure: it is a `⌜⌝` by construction (wave A's
`invalidAssn`, P4/D-c). The source gets this from
`is_pure_iff_pure_assn`. -/
@[safe_constraint_rules] theorem isPure_invalidAssn {α κ : Type} (R : α → κ → Assn) :
    isPure (invalidAssn R) :=
  ⟨fun a c => purePart (R a c), fun _ _ => rfl⟩

/-- Wave A's `pure_hn_ctxt`, as a *conditional* rule: `hn_ctxt` is
transparent, so purity passes through it. -/
@[constraint_rules] theorem isPure_hnCtxt {α κ : Type} {P : α → κ → Assn} (h : isPure P) :
    isPure (hnCtxt P) := pure_hn_ctxt h

/-- A scalar cell is *not* pure — it owns the cell. Registered as the
source's early-failure flag rather than left to fail in the slot. -/
@[safe_constraint_rules] theorem cn_isPure_natAssn (h : CN_FALSE isPure natAssn) :
    isPure natAssn := CN_FALSEI h

/-- Neither is an array. -/
@[safe_constraint_rules] theorem cn_isPure_arrayAssn (h : CN_FALSE isPure arrayAssn) :
    isPure arrayAssn := CN_FALSEI h

/-- The fact behind `cn_isPure_natAssn`: a cell assertion is satisfied by
a state that is not `0`, so it is not a `⌜⌝`. -/
theorem not_isPure_natAssn : ¬ isPure natAssn := by
  rintro ⟨P', hP⟩
  have h0 : natAssn 0 "x" ((Cells.single "x" (0 : Val), 0, 0), (0 : ECost)) := ⟨⟨rfl, rfl⟩, rfl⟩
  rw [hP 0 "x"] at h0
  have h1 : (Cells.single "x" (0 : Val), ((0 : Cells (List Val)), (0 : HCells))) = 0 :=
    congrArg (fun p => p.1) h0.2
  have h2 := congrFun (congrArg Prod.fst h1) "x"
  simp [Cells.single] at h2

/-! ## 3. The constraint store (P4/D-cd)

The source's slot, as data. `none` is "no slot"; `some gs` is a slot
holding the postponed goals in insertion order. -/

namespace Constraints

/-- The source's `CONSTRAINT_SLOT` subgoal, as an `IO.Ref` (P4/D-cd);
declared in `Sepref/Attrs.lean` because an `initialize` value is
unavailable to its own module. -/
abbrev slotRef : IO.Ref (Option (Array MVarId)) := constraintSlotRef

/-- The source's `has_slot`. -/
def hasSlot : IO Bool := return (← slotRef.get).isSome

/-- The source's `create_slot_tac`: fail if a slot is already present. -/
def createSlot : CoreM Unit := do
  if ← hasSlot then throwError "sepref: a constraint slot already exists"
  slotRef.set (some #[])

/-- The source's `ensure_slot_tac` (`TRY create_slot_tac`). -/
def ensureSlot : IO Unit := do
  unless ← hasSlot do slotRef.set (some #[])

/-- The source's `remove_slot_tac`, which also *checks* the slot is
empty — the source discharges `CONSTRAINT_SLOT True` by `TrueI`, which
only applies when everything was moved out. -/
def removeSlot : MetaM Unit := do
  match ← slotRef.get with
  | none => pure ()
  | some gs =>
    let open_ ← gs.filterM fun g => return !(← g.isAssigned)
    slotRef.set none
    unless open_.isEmpty do
      throwError "sepref: the constraint slot is not empty ({open_.size} unsolved)"

/-- Drop the slot without checking — for error recovery. -/
def clearSlot : IO Unit := slotRef.set none

/-- The source's `to_slot_tac`: defer this goal to the slot. -/
def addConstraint (g : MVarId) : CoreM Unit := do
  match ← slotRef.get with
  | none => throwError "sepref: no constraint slot (run the 'preproc' phase first)"
  | some gs => slotRef.set (some (gs.push g))

/-- The slot's current contents, unassigned entries only. -/
def slotGoals : MetaM (Array MVarId) := do
  match ← slotRef.get with
  | none => return #[]
  | some gs => gs.filterM fun g => return !(← g.isAssigned)

/-! ### Recognizers (the source's `is_constraint_goal` /
`is_slottable_constraint_goal`) -/

/-- The source's `is_constraint_goal`, after stripping binders. -/
def isConstraintGoal? (ty : Expr) : Option (Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``CONSTRAINT, #[_, P, x]) => some (P, x)
  | _ => none

/-- The source's `is_slottable_constraint_goal`: a `CN_FALSE`-flagged
constraint is refused. -/
def isSlottable (ty : Expr) : Bool :=
  match isConstraintGoal? ty with
  | some (P, _) => (P.getAppFnArgs.1 != ``CN_FALSE)
  | none => false

/-! ### The solver (the source's `solve_step_tac` / `safe_step_tac`) -/

/-- Resolve one goal against the two databases, safe rules first
(the source's `DETERM o resolve_from_net_tac scn_net ORELSE'
resolve_from_net_tac cn_net`). Returns the new goals, or `none` if no
rule applied. -/
def resolveStep (g : MVarId) : MetaM (Option (List MVarId)) := do
  let safeRules ← (try labelled `safe_constraint_rules catch _ => pure #[])
  let unsafeRules ← (try labelled `constraint_rules catch _ => pure #[])
  for n in safeRules ++ unsafeRules do
    let st ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels n)
      return some gs
    catch _ => st.restore
  return none

/-- The source's `wrap_tac (solve_step_tac …)`: simplify with
`constraint_simps` / `constraint_abbrevs`, then resolve, to exhaustion.
`budget` is the source's implicit `REPEAT_ALL_NEW` depth. -/
partial def solveLoop (budget : Nat) (g : MVarId) : MetaM (List MVarId) := do
  if ← g.isAssignedOrDelayedAssigned then return []
  if budget == 0 then return [g]
  match ← resolveStep g with
  | none => return [g]
  | some gs =>
    let mut out : List MVarId := []
    for g' in gs do
      out := out ++ (← solveLoop (budget - 1) g')
    return out

/-- The source's `solve_constraint_tac`: the goal must be a `CONSTRAINT`,
`CONSTRAINT_I` strips the tag, and the rule nets must close it. -/
def solveConstraint (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  if (isConstraintGoal? ty).isNone then
    throwError "sepref: not a CONSTRAINT goal:{indentExpr ty}"
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``CONSTRAINT_I)
  let mut rest : List MVarId := []
  for g' in gs do rest := rest ++ (← solveLoop 32 g')
  unless rest.isEmpty do
    let tys ← rest.mapM fun g' => do return indentExpr (← instantiateMVars (← g'.getType))
    throwError "sepref: the constraint{indentExpr ty}\nwas not solved; open \
      subgoals:{MessageData.joinSep tys ""}"

/-- The source's `constraint_tac`: "Solve, or apply safe rules and defer
to constraint slot". A `CN_FALSE`-flagged constraint is never
deferred. -/
def constraintTac (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let some (P, x) := isConstraintGoal? ty
    | throwError "sepref: not a CONSTRAINT goal:{indentExpr ty}"
  try
    solveConstraint g
  catch e =>
    -- The source's `safe_constraint_tac THEN_ALL_NEW slot_constraint_tac`:
    -- what the safe rules could not decide is postponed, unless it was
    -- flagged unsolvable.
    unless isSlottable ty do
      throwError "sepref: the constraint{indentExpr (mkApp P x)}\nis flagged \
        unsolvable (CN_FALSE) and cannot be deferred.\n{e.toMessageData}"
    addConstraint g

/-- The source's `process_constraint_slot`: apply the safe rules to every
constraint in the slot, keeping what does not close. -/
def processConstraints : MetaM Unit := do
  for g in ← slotGoals do
    try solveConstraint g catch _ => pure ()

/-- The source's `solve_constraint_slot`: solve everything in the slot,
and report — by name and statement — what is left. -/
def solveConstraintSlot : MetaM (Array MVarId) := do
  let mut open_ : Array MVarId := #[]
  for g in ← slotGoals do
    try solveConstraint g catch _ => open_ := open_.push g
  return open_

/-- The slot, as a message (the source's `print_slot_tac`). -/
def slotMessage : MetaM MessageData := do
  let gs ← slotGoals
  if gs.isEmpty then return m!"sepref: the constraint slot is empty"
  let tys ← gs.mapM fun g => do return indentExpr (← instantiateMVars (← g.getType))
  return m!"sepref: constraint slot ({gs.size}):{MessageData.joinSep tys.toList ""}"

end Constraints

/-! ## 4. The tactics and the solver registration -/

/-- The source's `method_setup solve_constraint`: the `CONSTRAINT` tag is
optional there (`solve_constraint'_tac`); here the tag-free form is
handled by `CONSTRAINT_I`'s `try`. -/
elab "solve_constraint" : tactic => do
  let g ← Tactic.getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if (Constraints.isConstraintGoal? ty).isSome then
    Constraints.solveConstraint g
  else
    let rest ← Constraints.solveLoop 32 g
    unless rest.isEmpty do
      throwError "sepref: the constraint{indentExpr ty}\nwas not solved"
  Tactic.replaceMainGoal []

/-- The source's `method_setup safe_constraint`: solve or defer. -/
elab "safe_constraint" : tactic => do
  let g ← Tactic.getMainGoal
  Constraints.constraintTac g
  Tactic.replaceMainGoal []

/-- Print the slot — the source's `method_setup print_slot`. -/
elab "print_slot" : tactic => do
  logInfo (← Constraints.slotMessage)

section Solver

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

-- The source dispatches constraints through its own `constraint_tac`;
-- P4/D-ce routes that dispatch through the P2 `TaggedSolver` registry so
-- that `Sepref/Translate.lean`'s `side_cond_dispatch` has one mechanism
-- for every side condition it meets.
declare_solver SEPREF_CONSTRAINT for CONSTRAINT at 0
    with "Sepref: deferred constraints (Sepref_Constraints.thy)" :=
  solve_constraint

end Solver

/-! ## 5. Gate (ledger D4, refute-before-prove) -/

namespace ConstraintsGate

open Lax13Proofs.Refine.Sepref.Constraints

/-- Positive: a pure relation's purity is decided by the safe rules. -/
example : CONSTRAINT isPure (pureAssn ({(0, 0)} : Set (ℕ × ℕ))) := by solve_constraint

/-- Positive: the invalid marker is pure whatever it marks. -/
example : CONSTRAINT isPure (invalidAssn natAssn) := by solve_constraint

/-- Positive: purity passes through `hn_ctxt` (the conditional rule). -/
example : CONSTRAINT isPure (hnCtxt (pureAssn ({(0, 0)} : Set (ℕ × ℕ)))) := by
  solve_constraint

/-- Positive: dispatch through the P2 registry reaches the same solver. -/
example : CONSTRAINT isPure (pureAssn ({(0, 0)} : Set (ℕ × ℕ))) := by tagged_solver

/-- **Negative control.** A cell assertion is not pure, and the
`CN_FALSE` flag says so *at the constraint*, not in the slot. -/
example : ¬ isPure natAssn := not_isPure_natAssn

-- The store round-trips: a slot is created, a constraint is deferred
-- into it, and `removeSlot` refuses to close over an unsolved one.
run_cmd Elab.Command.liftTermElabM do
  Constraints.clearSlot
  Constraints.ensureSlot
  unless ← Constraints.hasSlot do throwError "gate: ensureSlot did not create a slot"
  let ty ← Term.elabTerm (← `(CONSTRAINT isPure natAssn)) none
  let g ← Meta.mkFreshExprSyntheticOpaqueMVar ty
  Constraints.addConstraint g.mvarId!
  unless (← Constraints.slotGoals).size == 1 do throwError "gate: the slot did not take it"
  let bad ← (try (do let _ ← Constraints.removeSlot; pure false) catch _ => pure true)
  unless bad do throwError "gate: removeSlot accepted an unsolved constraint"
  Constraints.clearSlot

end ConstraintsGate

end Lax13Proofs.Refine.Sepref
