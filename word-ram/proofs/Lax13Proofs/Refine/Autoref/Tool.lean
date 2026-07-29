import Lax13Proofs.Refine.Autoref.Translate

/-!
The tool: the four phases registered in the source's priority order, the
`autoref` entry point, and the generic-algorithm solvers.

Port of `thys/Automatic_Refinement/Tool/Autoref_Tool.thy` and
`thys/Automatic_Refinement/Tool/Autoref_Gen_Algo.thy` of AFP
`Automatic_Refinement` (Lammich) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 — AFP for Isabelle2025-2,
release 2026-02-06. The verbatim source text this file is checked
against is `plans/word-ram/refinement-tower/p2-tool-extracts.md` §5
(`Autoref_Gen_Algo.thy`) and §7 (`Autoref_Tool.thy`).

## The source, verbatim

§7.1, the phase registration — the extract's headline finding, that the
pipeline has *four* phases and not three:

```isabelle
declaration ‹fn phi => let open Autoref_Phases in
  I
  #> register_phase "id_op" 10 Autoref_Id_Ops.id_phase phi
  #> register_phase "rel_inf" 20
       Autoref_Rel_Inf.roi_phase phi
  #> register_phase "fix_rel" 22
       Autoref_Fix_Rel.phase phi
  #> register_phase "trans" 30
       Autoref_Translate.trans_phase phi
end
›
```

§7.2, the method:

```isabelle
text ‹Main method›
method_setup autoref = ‹let
    open Refine_Util
    val autoref_flags =
          parse_bool_config "trace" Autoref_Phases.cfg_trace
      ||  parse_bool_config "debug" Autoref_Phases.cfg_debug
      ||  parse_bool_config "keep_goal" Autoref_Phases.cfg_keep_goal

    val autoref_phases =
      Args.$$$ "phases" |-- Args.colon |-- Scan.repeat1 Args.name

  in
    parse_paren_lists autoref_flags
    |-- Scan.option (Scan.lift (autoref_phases)) >>
    ( fn phases => fn ctxt => SIMPLE_METHOD' (
      (
        case phases of
          NONE => Autoref_Phases.all_phases_tac
        | SOME names => Autoref_Phases.phases_tacN names
      ) (Autoref_Phases.init_data ctxt)
    ))
  end
› "Automatic Refinement"
```

§7.5, the casting tag and the notation locale:

```isabelle
text ‹General casting-tag, that allows type-casting on concrete level, while
  being identity on abstract level.›
definition [simp]: "CAST ≡ id"
lemma [autoref_itype]: "CAST ::⇩i I →⇩i I" by simp

locale autoref_syn begin
  notation (input) APP (infixl "$" 900)
  notation (input) rel_ANNOT (infix ":::" 10)
  notation (input) ind_ANNOT (infix "::#" 10)
  notation OP ("OP")
  notation (input) ABS (binder "λ''" 10)
end

hide_const (open) PROTECT ANNOT OP APP ABS ID_FAIL rel_annot ind_annot
```

§5, `Autoref_Gen_Algo.thy` — where the `GEN_OP` side condition is
actually discharged:

```isabelle
definition [simp, autoref_tag_defs]: "GEN_ALGO_tag P ≡ P"
lemma GEN_ALGO_tagI: "P ⟹ GEN_ALGO_tag P" by simp
abbreviation "SIDE_GEN_ALGO P ≡ PREFER_tag (GEN_ALGO_tag P)"

structure ga_side_thms = Named_Sorted_Thms (
  val name = @{binding autoref_ga_rules}
  val description = "Additional rules for generic algorithm side conditions"
  val sort = K I
  val transform = transform_ga_rule )

fun decl_setup phi = I
#> Tagged_Solver.declare_solver @{thms GEN_ALGO_tagI} @{binding GEN_ALGO}
    "Autoref: Generic algorithm side condition solver"
    ( side_ga_tac) phi
#> Autoref_Phases.declare_solver @{thms GEN_OP_tagI} @{binding GEN_OP}
    "Autoref: Generic algorithm operation instantiation"
    ( side_ga_op_tac) phi
```

with the extract's note on the second one:

> `side_ga_op_tac = SOLVED' (Autoref_Tacticals.REPEAT_ON_SUBGOAL
> (Autoref_Translate.trans_step_tac ctxt))` — i.e. the `GEN_OP` solver
> re-invokes the *translate* phase's own step tactic to instantiate the
> schematic operator (`eq := (=)`) and check it refines under the stated
> relator, recursively.

## Substrate deltas and departures, each flagged

**O1 — the extra-rules vehicle is the local context, plus an explicit
list.** The tutorial's derivations bind rules on the fly with
`assumes [autoref_rules]: "(ai,a)∈⟨R⟩option_rel"` and
`notes [autoref_rules] = IdI[of src]`. Lean has no attribute on a local
hypothesis, so `autoref` collects every hypothesis of the local context
whose type is, or ends in, `(c, a) ∈ R` and passes them to the pipeline
as `State.extras` — which `fix_rel` and `trans` consult ahead of the
databases (`Autoref/FixRel.lean` delta F4). `autoref [r₁, r₂]` names
extra rules explicitly, the analogue of `notes`. Both are the vehicle;
neither is an attribute, and that is the whole of the departure.

**O2 — `autoref_synth` is the `schematic_goal` + `concrete_definition`
analogue.** The source's derivations are `schematic_goal "(?f::?'c,a)∈?R"
by autoref`, in which *both* the concrete term and its type are
schematic. Lean has no schematic goal at the top level of a declaration:
a theorem statement is a closed term. Two vehicles cover the two halves:

* the `autoref` *tactic*, on a goal `(?c, a) ∈ ?R` — reachable by
  `refine ⟨?γ, ?c, ?R, ?_⟩` against
  `∃ (γ : Type) (c : γ) (R : Set (γ × α)), (c, a) ∈ R`, which is
  Lean's honest rendering of a schematic goal with a schematic type;
* the `autoref_synth` *command*, which elaborates the abstract term,
  runs the pipeline against genuinely fresh `?γ`/`?c`/`?R`
  metavariables, and adds the *resulting* theorem to the environment —
  and, when the synthesized term is closed, a definition holding it, in
  the shape `concrete_definition` gives the source's derivations.

The command is what the acceptance file uses, because it is the form in
which the synthesized term can be named, `#eval`ed and `#guard`ed
(ledger D4).

**O3 — `keep_goal` reports and rolls back.** The source's
`cfg_keep_goal` makes the driver "return the goal state unchanged"
instead of failing, so `apply (autoref (keep_goal))` leaves an
inspectable goal. Here the failure message is reported as `info` and the
metavariable context is restored to its pre-run state, which is the same
contract: the goal survives, the diagnosis is visible.

**O4 — `autoref_ga_rules` and `side_ga_tac` are absent.** The `GEN_ALGO`
solver in the source resolves against the `autoref_ga_rules` database,
whose attribute is not registered (wave B2's `Autoref/Attrs.lean` is
frozen; it is a "bonus" row of the extract's §9 table). The `GEN_ALGO`
solver below is therefore assumption-and-simp, and a generic-algorithm
side condition beyond that is reported by name. `GEN_OP` — the one the
acceptance examples actually exercise — is ported exactly: it re-enters
the translate phase, which is what `side_ga_op_tac` does.

**O5 — `Autoref_Gen_Algo.thy` is folded into this file**, because its
whole content is two solver registrations that need the translate phase
(`GEN_OP`) or a database that does not exist (`GEN_ALGO`), and because
the source itself imports it only from `Autoref_Tool.thy`.
`Autoref_Phases.declare_solver` versus `Tagged_Solver.declare_solver`
collapses too, for the reason `Autoref/Phases.lean` delta P5 gives.

**O6 — the `autoref_syn` locale is not ported, and nothing is hidden.**
Wave B2 already made `$ᵃ` / `:::` / `::#` global notation
(`Autoref/Tagging.lean` delta T3) rather than locale-scoped, because
Lean's notation is namespace-scoped and the tags live in
`Lax13Proofs.Refine`, which a consumer opens deliberately. The source's
`hide_const (open)` has no counterpart and needs none: `OP`, `APP` and
friends are already qualified names in a helper-only namespace.
`CAST` is ported with its `[autoref_itype]` fact — the source records
that it "does currently not work", and this port inherits that status
unchanged and unexercised.

**O8 — the tactic re-marks the goal's metavariables as assignable.**
Recorded at `runAutoref` below: Lean's `refine ⟨?γ, ?c, ?R, ?_⟩` marks
its holes synthetic-opaque, meaning "do not let unification guess these",
whereas an Isabelle schematic variable is by definition what unification
guesses. Since the pipeline exists to determine `?c` and `?R`, it sets
them (and the goal's other metavariables, `?γ` among them) back to
`natural` first. The `autoref_synth` command creates them natural to
begin with and is unaffected.

**O7 — `autoref_higher_order_rule` is absent.** The extract's §7.3
records it as "a convenience for lifting partially-applied facts, not
part of the core phase pipeline and not consulted by any of the
tutorial's acceptance examples". Nothing here consults it either.
-/

open Lean Meta Elab

namespace Lax13Proofs.Refine

/-! ### The casting tag (`Autoref_Tool.thy` §7.5) -/

/-- The source's `CAST ≡ id`, its "General casting-tag, that allows
type-casting on concrete level, while being identity on abstract level".
The source's own follow-up comment records that this "does currently not
work" as a general-purpose cast; the port inherits that status. -/
def CAST {α : Type} : α → α := id

/-- The source's `CAST` definition, with the source's own `[simp]`. -/
@[simp] theorem CAST_def {α : Type} (x : α) : CAST x = x := rfl

/-- The source's `lemma [autoref_itype]: "CAST ::⇩i I →⇩i I"`. -/
@[autoref_itype] theorem CAST_itype {α : Type} (I : Interface) :
    (CAST (α := α)) ::ᵢ (I →ᵢ I) := trivial

/-! ### Generic algorithms (`Autoref_Gen_Algo.thy`, delta O5) -/

/-- The source's `GEN_ALGO_tag P ≡ P`. -/
def GEN_ALGO_tag (P : Prop) : Prop := P

/-- The source's `GEN_ALGO_tag` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem GEN_ALGO_tag_def (P : Prop) : GEN_ALGO_tag P ↔ P := Iff.rfl

/-- The source's `GEN_ALGO_tagI`. -/
theorem GEN_ALGO_tagI {P : Prop} (h : P) : GEN_ALGO_tag P := h

/-- The source's `SIDE_GEN_ALGO P ≡ PREFER_tag (GEN_ALGO_tag P)`. -/
abbrev SIDE_GEN_ALGO (P : Prop) : Prop := PREFER_tag (GEN_ALGO_tag P)

section Solvers

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

-- The source's `GEN_ALGO` solver, `Tagged_Solver.declare_solver
-- @{thms GEN_ALGO_tagI} @{binding GEN_ALGO} "Autoref: Generic algorithm
-- side condition solver" side_ga_tac` — without `autoref_ga_rules`
-- (delta O4).
declare_solver GEN_ALGO for GEN_ALGO_tag at 0
    with "Autoref: Generic algorithm side condition solver" :=
  simp only [GEN_ALGO_tag_def, REMOVE_INTERNAL_def]
  try (first | assumption | simp)

-- The source's `GEN_OP` solver, `Autoref_Phases.declare_solver
-- @{thms GEN_OP_tagI} @{binding GEN_OP} "Autoref: Generic algorithm
-- operation instantiation" side_ga_op_tac`, whose tactic is
-- `SOLVED' (REPEAT_ON_SUBGOAL (Autoref_Translate.trans_step_tac ctxt))`
-- — i.e. the translate phase, re-entered.
declare_solver GEN_OP for GEN_OP_tag at 0
    with "Autoref: Generic algorithm operation instantiation" :=
  apply GEN_OP_tagI
  autoref_trans

end Solvers

namespace Autoref

/-! ### Phase registration (`Autoref_Tool.thy` §7.1) -/

initialize
  registerPhase "id_op" 10 idPhase
  registerPhase "rel_inf" 20 roiPhase
  registerPhase "fix_rel" 22 fixRelPhase
  registerPhase "trans" 30 transPhase

/-! ### The `autoref` entry point (`Autoref_Tool.thy` §7.2) -/

/-- Read the source's parenthesised boolean flags, rejecting anything
else by name — the supervision-legibility requirement applied to the
method's own arguments. -/
def parseFlags (flags : Array Ident) : MetaM Config := do
  let mut cfg : Config := {}
  for f in flags do
    match f.getId.toString with
    | "trace" => cfg := { cfg with trace := true }
    | "debug" => cfg := { cfg with debug := true }
    | "keep_goal" => cfg := { cfg with keepGoal := true }
    | s => throwError "autoref: unknown flag '{s}'; the flags are trace, debug, keep_goal"
  return cfg

/-- Run the pipeline on one goal, with the given configuration, extra
rules and (optionally) a restricted phase list. Reports the trace, and
honours `keep_goal` (delta O3): returns `true` when the goal was
closed. -/
def runAutoref (goal : MVarId) (cfg : Config) (extras : Array Expr)
    (phaseNames : Option (Array String)) : TermElabM Bool := do
  let ty ← instantiateMVars (← goal.getType)
  let some (_, a, _) := parseRefine? ty
    | throwError "autoref: the goal is not of the form `(?c, a) ∈ ?R`:{indentExpr ty}"
  -- Delta O8: `refine ⟨?γ, ?c, ?R, ?_⟩` creates its named holes as
  -- *synthetic opaque* metavariables, which unification is forbidden to
  -- guess — and guessing them is precisely this pipeline's job (the
  -- source's `schematic_goal` has no such restriction: an Isabelle
  -- schematic variable is assignable by definition). Every metavariable
  -- of the goal is therefore re-marked natural before the run.
  for m in (ty.collectMVars {}).result do
    m.setKind .natural
  let st : State := { goal, abs := a, extras, cfg }
  let saved ← saveState
  try
    let st ← match phaseNames with
      | none => allPhasesTac st
      | some ns => phasesTacN ns st
    for m in st.log do logInfo m
    return true
  catch e =>
    if cfg.keepGoal then
      saved.restore
      logInfo m!"{e.toMessageData}"
      return false
    else
      throw e

end Autoref

open Autoref in
/-- The source's `autoref` method, "Automatic Refinement": close a goal
`(?c, a) ∈ ?R` by synthesizing the concrete term `?c` and the relator
`?R`.

* `autoref (trace)` / `(debug)` / `(keep_goal)` are the source's three
  parenthesised boolean flags;
* `autoref phases: id_op rel_inf` is the source's phase restriction;
* `autoref [r₁, r₂]` names extra rules — the `notes [autoref_rules] = …`
  analogue (delta O1). Refinement hypotheses of the local context are
  always available as rules and need not be named. -/
syntax (name := autorefTac) "autoref"
  (" [" term,+ "]")? ("(" ident,* ")")? (&" phases" ": " ident+)? : tactic

open Autoref Tactic in
elab_rules : tactic
  | `(tactic| autoref $[[$rs,*]]? $[($fs,*)]? $[phases : $ps*]?) => do
    let cfg ← parseFlags ((fs.map (·.getElems)).getD #[])
    let goal ← getMainGoal
    let named ← match rs with
      | none => pure #[]
      | some rs => rs.getElems.mapM fun r => Term.elabTerm r none
    let extras := named ++ (← collectExtras goal)
    let names := (ps.map fun ps => ps.map (·.getId.toString))
    let closed ← runAutoref goal cfg extras names
    if closed then replaceMainGoal [] else replaceMainGoal [goal]

/-! ### `autoref_synth` — the `schematic_goal` + `concrete_definition`
analogue (delta O2) -/

/-- Synthesize a concrete term and a relator for an abstract term, and
add the resulting theorem to the environment:

```
autoref_synth my_thm for [1,2,3] ++ [4 : ℕ]
```

adds `my_thm : (c, [1,2,3] ++ [4]) ∈ R` with `c` and `R` the
pipeline's, and — when `c` is closed — `my_thm_impl : List ℕ := c`, the
source's `concrete_definition`. Binders may be given between the name
and `for`; a binder of refinement shape is an extra rule, which is the
`assumes [autoref_rules]` analogue (delta O1). `(trace)` and `(debug)`
are the method's flags. -/
syntax (name := autorefSynth) "autoref_synth" ("(" ident,* ")")? ident
  (ppSpace bracketedBinder)* " for " term : command

open Autoref in
elab_rules : command
  | `(command| autoref_synth $[($fs,*)]? $nm:ident $bs* for $t:term) => do
    Command.liftTermElabM do
      let cfg ← parseFlags ((fs.map (·.getElems)).getD #[])
      -- The declaration is added under the *current* namespace, which is
      -- what the archive's namespace audit checks and what a `theorem`
      -- would do by itself.
      let declName := (← getCurrNamespace) ++ nm.getId
      Term.elabBinders bs fun xs => do
        let a ← Term.elabTerm t none
        Term.synthesizeSyntheticMVarsNoPostponing
        let a ← instantiateMVars a
        let α ← inferType a
        let lvl ← getLevel α
        let γ ← mkFreshExprMVar (mkSort lvl)
        let c ← mkFreshExprMVar γ
        let R ← mkFreshExprMVar (← mkAppM ``Set #[← mkAppM ``Prod #[γ, α]])
        let goal ← mkFreshExprSyntheticOpaqueMVar (← mkRefine c a R)
        let extras ← collectExtras goal.mvarId!
        let _ ← runAutoref goal.mvarId! cfg extras none
        let cVal ← instantiateMVars c
        let RVal ← instantiateMVars R
        let proof ← instantiateMVars goal
        if proof.hasExprMVar then
          let mvs := (proof.collectMVars {}).result
          let mut msg := m!""
          for m in mvs do
            msg := msg ++ m!"\n  ?{m.name} : {← instantiateMVars (← m.getType)}"
          throwError "autoref_synth: the synthesized proof still contains \
            metavariables — some relator was never fixed:{msg}"
        let type ← mkForallFVars xs (← mkRefine cVal a RVal)
        let value ← mkLambdaFVars xs proof
        let type ← Term.levelMVarToParam (← instantiateMVars type)
        let value ← Term.levelMVarToParam (← instantiateMVars value)
        let us := (collectLevelParams (collectLevelParams {} type) value).params
        addDecl (.thmDecl { name := declName, levelParams := us.toList, type, value })
        -- The source's `concrete_definition`, when the term is closed.
        unless cVal.hasFVar || cVal.hasExprMVar do
          let ity ← instantiateMVars (← inferType cVal)
          let iName := declName.appendAfter "_impl"
          let dv : DefinitionVal :=
            { name := iName
              levelParams := []
              type := ity
              value := cVal
              hints := .abbrev
              safety := .safe }
          addAndCompile (.defnDecl dv)
        if cfg.trace || cfg.debug then
          logInfo m!"autoref_synth {declName}:\n  concrete{indentExpr cVal}\n  \
            relator{indentExpr RVal}"

end Lax13Proofs.Refine
