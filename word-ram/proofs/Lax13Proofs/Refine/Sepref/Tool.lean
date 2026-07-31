import Lax13Proofs.Refine.Sepref.Translate
import Lax13Proofs.Refine.Sepref.IdOp
import Lax13Proofs.Refine.Sepref.Monadify

/-!
The Sepref tool: the port of `thys/sepref/Sepref_Tool.thy`.

Source pin as `Sepref/Basic.lean`'s header (`isabelle_llvm_time`
@ `42dd7f5`); the theory was fetched whole (404 lines). Its four
initialization lemmas (`CONS_init`, `ID_init`, `TRANS_init`,
`infer_post_triv`) are ported below, its `Sepref.sepref_tac` phase list
is `seprefPipeline`, and its `sepref_dbg_*` method table (source lines
184–287) is reproduced one entry for one entry.

The source's driver, verbatim:

```isabelle
fun sepref_tac dbg ctxt =
  (K Sepref_Constraints.ensure_slot_tac)
  THEN' Sepref_Basic.PHASES'
    [ ("preproc",preproc_tac,0),
      ("cons_init",cons_init_tac,2),
      ("id",id_tac true,0),
      ("monadify",monadify_tac false,0),
      ("opt_init",fn ctxt => resolve_tac ctxt @{thms TRANS_init},1),
      ("trans",trans_tac,~1),
      ("opt",opt_tac,~1),
      ("cons_solve1",cons_solve_tac false,~1),
      ("cons_solve2",cons_solve_tac false,~1),
      ("constraints",fn ctxt => K (Sepref_Constraints.solve_constraint_slot ctxt
         THEN Sepref_Constraints.remove_slot_tac),~1)
    ] (Sepref_Basic.flag_phases_ctrl ctxt dbg) ctxt
```

## Judgment calls

**P4/D-cw — the pipeline is a `MetaM` fold over an `hnRefine` goal, and
every phase is a `Phase`.** The source's `PHASES'` is a tactic
combinator over a goal *interval*; P2 already rendered that machinery as
`Autoref/Phases.lean`'s `Phase` record and `runPhase` driver, and its
failure envelope — `"<tool>: phase '<name>' (priority <n>) failed.\n…"`
— is what wave B2's `id_op` and `monadify` already emit. The Sepref
pipeline reuses the *envelope* (`seprefPhase` below builds exactly that
string, with `sepref` in place of `autoref`) but not the *registry*: the
Autoref registry is keyed on a `(?c, a) ∈ ?R` state, this pipeline's
state is an `hnRefine` metavariable, and there is exactly one consumer.
Recorded as a departure from "reuse the P2 plumbing" in the narrow
sense; the legibility contract the plan cares about is met literally.

**P4/D-cx — `preproc` checks, it does not simplify.** The source's
`preproc_tac` is `Sepref_Rules.prepare_hfref_synth_tac THEN'
Simplifier.simp_tac` with the `sepref_preproc` set: it turns an `hfref`
synthesis goal into an `hn_refine` one (uncurrying the argument tuple)
and normalizes the abstract program. Our entry points *build* an
`hnRefine` goal directly (`sepref_synth`, `Sepref/Definition.lean`), so
there is no `hfref`-to-`hnr` step to take; what remains is the shape
check and `Constraints.ensureSlot`, which the source does in the same
breath (`K Sepref_Constraints.ensure_slot_tac THEN' …`). The
`sepref_preproc` simp set is declared and applied to the abstract
program, so a consumer's preprocessing lemma has somewhere to go.
Tower-expansion P1.A adds theorem conversion and composition from an
`hfref` signature (`Signature.lean` / `SignatureTool.lean`). The remaining
piece here is narrower: P1.B must connect a schematic signature *goal* to
this synthesis pipeline, the role of `prepare_hfref_synth_tac`; it is not
silently supplied by the conversion frontend.

**P4/D-cy — `cons_init` and `opt_init` are shape phases with nothing to
do, and the two `cons_solve` passes collapse to one check.** The source's
`cons_init_tac` is `weaken_post_tac THEN' resolve CONS_init`: it
*introduces* the consequence step so that the synthesized postcondition
and result assertion may differ from the ones the goal asks for, and
`cons_solve_tac` (run twice, because its `PHASES'` addresses one goal
per phase) discharges the two entailments that step leaves. Here the
goal's postcondition is a metavariable throughout — that is what
`preproc` checks — so `CONS_init`'s two entailments are
`?Γ' ⊢ ?Γc'` and `hn_ctxt R x y ⊢ hn_ctxt ?Rc x y`, both closed by
`infer_post_triv` before anything has been synthesized, and the whole
step is the identity. `cons_init` and `opt_init` therefore run nothing,
and `cons_solve` *checks* that translate closed the goal rather than
inferring anything. All four lemmas — `CONS_init`, `TRANS_init`, `CNV`,
`infer_post_triv` — are ported and are what a signature-driven front end
(P4/D-cx's fallback, where the caller *does* state a postcondition)
would resolve through; `weaken_hnr_post` is exercised in
`Sepref/Frame.lean`'s gate. Recorded here rather than silently: the
phases are in the list, under the source's names and in the source's
order, and they are honest no-ops.

**P4/D-de — the debugging table's absences.** Ported: `preproc`,
`cons_init`, `id`, `id_keep`, `monadify`, `monadify_keep`, `opt_init`,
`trans`, `trans_keep`, `trans_step`, `side`, `side_keep`, `opt`,
`cons_solve`, `cons_solve_keep`, `constraints`, `print_slot`,
`prepare_frame`, `frame`, `frame_step`, `frame_step_keep`, `merge`, plus
three of ours (`align_goal`, `cond`, `recover_pure`). Absent, each for a
reason already recorded: `sepref_dbg_monadify_arity` / `_comb` /
`_check_EVAL` / `_mark_params` / `_dup` / `_remove_pass` and
`sepref_dbg_id_init` / `_step` / `_solve` (wave B2 exposed its phases as
`#monadify` / `#sepref_id_op` commands instead of per-sub-phase
tactics — its call, its files); `sepref_dbg_side_unfold` (the source's
`Id_Op.unprotect_conv` plus `bind_ref_tag_def` unfolding, which P4/D-dd's
tag stripping does once for the whole pipeline);
`sepref_dbg_side_bounds` (P4/D-cs: no bounds obligations exist);
`sepref_to_hoare` (starts from an `hfref` goal, P4/D-cx). The source's
rule-conversion role of `sepref_to_hnr` is now provided by P1.A's
`to_hnr` and exercised through `sepref_fcomp`; goal preparation remains
P1.B as stated above.

**P4/D-cz — `opt` is a no-op pass, deliberately.** The source's
`opt_tac` simplifies the synthesized program with `sepref_opt_simps`
(`Monad.bind_laws`, `APP_def`, the `case_*`-return push-ins) and then
resolves `CNV_I`. Our synthesized programs are first-order `Ir.Com`
terms built by rule application: they contain no monad-law redexes, no
tagged applications and no `case_prod`. `opt` therefore runs the
(currently empty) `sepref_opt_simps` set over the program and stops.
`TRANS_init`/`CNV` are ported so the phase has the source's shape.
Fallback: the set exists; a consumer's cleanup lemma goes in it and the
phase applies it with no further change.
-/

open Lean Elab Meta

universe u

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. The initialization lemmas (source lines 11–28) -/

/-- The source's `CONS_init`. -/
theorem CONS_init {α κ : Type} {Γ Γ' Γc' : Assn} {c : Com} {d : κ} {R Rc : α → κ → Assn}
    {a : NRest α ECost} (h : hnRefine Γ c Γ' d R a) (hpost : Γ' ⊢ Γc')
    (hres : ∀ (x : α) (y : κ), hnCtxt R x y ⊢ hnCtxt Rc x y) :
    hnRefine Γ c Γc' d Rc a :=
  hnRefine_cons h (entails_refl Γ) hpost hres

/-- The source's `ID_init`. -/
theorem ID_init {α κ : Type} {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {a a' : NRest α ECost} {T : Type} (hid : ID a a' T) (h : hnRefine Γ c Γ' d R a') :
    hnRefine Γ c Γ' d R a := by
  have : a = a' := hid
  rw [this]; exact h

/-- The source's `CNV c c'` (from `Refine_Util`): the tag the
optimization phase resolves through. -/
def CNV {α : Sort u} (c c' : α) : Prop := c = c'

/-- The source's `CNV_I`. -/
theorem CNV_I {α : Sort u} (c : α) : CNV c c := rfl

/-- The source's `TRANS_init`. -/
theorem TRANS_init {α κ : Type} {Γ Γ' : Assn} {c c' : Com} {d : κ} {R : α → κ → Assn}
    {a : NRest α ECost} (h : hnRefine Γ c Γ' d R a) (hc : CNV c c') :
    hnRefine Γ c' Γ' d R a := by
  have : c = c' := hc
  rw [← this]; exact h

/-- The source's `infer_post_triv`. -/
theorem infer_post_triv (P : Assn) : P ⊢ P := entails_refl P

/-! ## 2. The pipeline -/

namespace Tool

open Translate Frame

/-- The source's `Sepref.sepref_tac dbg` flag, plus the trace switch
`Autoref/Phases.lean`'s `Config` has. -/
structure Config where
  /-- The source's `dbg`: keep the goal and report, instead of failing. -/
  debugMode : Bool := false
  /-- Report each phase's progress. -/
  tracing : Bool := false
  deriving Inhabited, Repr

/-- The pipeline's state: the one `hnRefine` goal, the tagged abstract
program the `id` phase produced, and the trace. -/
structure State where
  /-- The `hnRefine ?Γ ?c ?Γ' d R m` goal every phase reads and rewrites. -/
  goal : MVarId
  /-- The source's channel from `id_op` to `monadify`: the abstract
  program with the identification phase's tags on it. The *goal* keeps
  the untagged program (P4/D-dd). -/
  tagged : Option Expr := none
  /-- The configuration. -/
  cfg : Config := {}
  /-- The trace, when `cfg.tracing` is set. -/
  log : Array MessageData := #[]

/-- One phase of the source's `PHASES'` list. -/
structure Phase where
  /-- The phase's name, as the source's `PHASES'` records it. -/
  name : String
  /-- Its ordinal — the Sepref pipeline's own numbering, continuing
  `Sepref/IdOp.lean`'s 10 and `Sepref/Monadify.lean`'s 20–70. -/
  prio : Nat
  /-- What it does. -/
  run : State → TermElabM State

/-- `Autoref/Phases.lean`'s `runPhase` envelope, at `sepref` (P4/D-cw):
every failure names the phase and its priority, and carries whatever the
phase itself said. -/
def runPhase (ph : Phase) (st : State) : TermElabM State := do
  let st' ←
    try ph.run st
    catch e =>
      let msg ← e.toMessageData.toString
      -- The sub-phases of `id`/`monadify` already wrap themselves; do not
      -- wrap twice.
      if msg.startsWith "sepref: phase" then throwError msg
      else throwError "sepref: phase '{ph.name}' (priority {ph.prio}) failed.\n{msg}"
  if st'.cfg.tracing then
    return { st' with log := st'.log.push m!"phase '{ph.name}' ({ph.prio}) succeeded" }
  return st'

/-! ### Stripping the tags (P4/D-dd)

The `id_op` phase's whole output is the abstract program with tags added
— `$ᵃ` applications, `λ₂` abstractions, `PR_CONST` atoms — and
`monadify`'s input must carry them, because its rule databases are
pattern nets keyed on them. The *translate* phase's rules, on the other
hand, are stated on the bare mop layer (`Sepref/IrOps.lean`), which is
the source's arrangement too (its `hn_bind` is stated at
`NREST.bindT$m$(λ⇩2x. f x)` because its resolution is syntactic; ours can
be stated bare because Lean's `isDefEq` unfolds — P2's
`Autoref/Translate.lean` delta T2 makes the same observation). What Lean
does *not* do reliably is unify a rule's bare conclusion against a
goal buried under four layers of identity wrapper: the unifier meets
`APP` at the head and does not commit to the delta step that would expose
`bindT`.

So the tags are stripped between `monadify` and `trans`. Every one of
them is a `def` for the identity, so the stripped term is
*definitionally* the tagged one and the monadify equation retypes to it
by `mkExpectedTypeHint` — no new proof obligation, no lost information.
`COPY` is deliberately not stripped: it is a *semantic* marker (a
parameter that must be duplicated), and a program still carrying one
should fail translate by name, not silently lose it.

**P4/D-dd** — recorded as a judgment call because it is a departure from
the source's arrangement: the source keeps the tags all the way through
translate and strips them in its `opt` phase's post-pass. Fallback if a
consumer needs tagged rules: state the rules tagged, as the source does,
and delete this pass. -/

/-- The identity wrappers `id_op` and `monadify` add, and where the
payload sits. -/
def stripTags (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    match x.getAppFnArgs with
    | (``Lax13Proofs.Refine.APP, #[_, _, f, a]) => return .done (mkApp f a)
    | (``APP', #[_, _, f, a]) => return .done (mkApp f a)
    | (``Lax13Proofs.Refine.PROTECT, #[_, y]) => return .done y
    | (``Lax13Proofs.Refine.OP, #[_, y]) => return .done y
    | (``Lax13Proofs.Refine.ANNOT, #[_, y, _]) => return .done y
    | (``PROTECT2, #[_, y, _]) => return .done y
    | (``PR_CONST, #[_, y]) => return .done y
    | (``UNPROTECT, #[_, y]) => return .done y
    | (``SP, #[_, y]) => return .done y
    | _ => return .continue)

/-! ### The phases -/

/-- The source's `preproc_tac`, at P4/D-cx: create the constraint slot
and check that the goal really is an `hnRefine` synthesis goal. -/
def preprocPhase : Phase where
  name := "preproc"
  prio := 1
  run := fun st => do
    Constraints.ensureSlot
    let ty ← instantiateMVars (← st.goal.getType)
    let some (_, _, Γ, c, Γ', _, _, _) := parseHnRefine? ty
      | throwError "the goal is not an hnRefine synthesis goal:{indentExpr ty}"
    unless c.getAppFn.isMVar do
      throwError "the goal's program is already fixed{indentExpr c}\n(a synthesis \
        goal has a metavariable there; use `sepref_dbg_trans` to *check* a program)"
    unless Γ'.getAppFn.isMVar do
      throwError "the goal's postcondition is already fixed{indentExpr Γ'}\n(a \
        synthesis goal has a metavariable there)"
    unless (Frame.conjuncts Γ).size > 0 do
      throwError "the goal's precondition owns nothing:{indentExpr Γ}"
    return st

/-- The source's `cons_init_tac = weaken_post_tac THEN' resolve
CONS_init` (P4/D-cy). Both entailments it produces are metavariable-post
identities at this point, so `weaken_hnr_post_triv` and
`infer_post_triv` discharge them and the phase is where the *shape* is
established, not where work happens. -/
def consInitPhase : Phase where
  name := "cons_init"
  prio := 5
  run := fun st => return st

/-- The source's `id_tac true`: `resolve ID_init` then
`Id_Op.id_tac Normal`, i.e. wave B2's `idOpCore` on the abstract side,
with the goal rewritten through `ID_init`. -/
def idPhase : Phase where
  name := "id"
  prio := 10
  run := fun st => do
    let ty ← instantiateMVars (← st.goal.getType)
    let some (_, _, _, _, _, _, _, m) := parseHnRefine? ty
      | throwError "the goal is not an hnRefine goal"
    let (m', _T, _pf) ← IdOp.idOpCore {} m
    -- `ID_init` is what the source resolves here; the port keeps the
    -- *untagged* program in the goal (P4/D-dd) and passes the tagged one
    -- to `monadify` as data, so no rewriting happens. `ID_init` is proved
    -- above and is what a signature-driven front end would use.
    return { st with tagged := some m' }

/-- The source's `monadify_tac false`: wave B2's `monadifyCore`, with the
`pps` read out of the precondition's `hn_ctxt` conjuncts — the source's
`mark_params` input, `strip_star P |> map_filter (dest_hn_ctxt_opt #>
map_option #2)`. -/
def monadifyPhase : Phase where
  name := "monadify"
  prio := 20
  run := fun st => do
    let ty ← instantiateMVars (← st.goal.getType)
    let some (_, _, Γ, _, _, _, _, m) := parseHnRefine? ty
      | throwError "the goal is not an hnRefine goal"
    let pps := (Frame.conjuncts Γ).filterMap fun c =>
      match c.getAppFnArgs with
      | (``hnCtxt, #[_, _, _, a, _]) => some a
      | _ => none
    let tagged := st.tagged.getD m
    let (m'T, pf) ← Monadify.monadifyCore pps tagged
    let m' ← stripTags m'T
    if m' == m then return st
    let pf ← mkExpectedTypeHint pf (← mkEq m m')
    let newTy := mkAppN ty.consumeMData.getAppFn (ty.consumeMData.getAppArgs.set! 7 m')
    let g' ← mkFreshExprSyntheticOpaqueMVar newTy
    let prf ← mkAppM ``hnRefine_abs_cong #[pf, g']
    unless ← isDefEq (← inferType prf) ty do
      throwError "the monadified program does not fit the goal"
    st.goal.assign prf
    return { st with goal := g'.mvarId! }

/-- The source's `("opt_init", resolve TRANS_init, 1)`. -/
def optInitPhase : Phase where
  name := "opt_init"
  prio := 75
  run := fun st => return st

/-- The source's `trans_tac`. -/
def transPhase : Phase where
  name := "trans"
  prio := 80
  run := fun st => do
    Translate.transTac { debugMode := st.cfg.debugMode } st.goal
    return st

/-- The source's `opt_tac`, at P4/D-cz: the `sepref_opt_simps` set over
the synthesized program. -/
def optPhase : Phase where
  name := "opt"
  prio := 85
  run := fun st => do
    let ty ← instantiateMVars (← st.goal.getType)
    let some (_, _, _, c, _, _, _, _) := parseHnRefine? ty
      | return st
    let some ext ← getSimpExtension? `sepref_opt_simps | return st
    let ctx ← Simp.mkContext {} (simpTheorems := #[← ext.getTheorems])
      (congrTheorems := ← getSimpCongrTheorems)
    let (r, _) ← Meta.simp c ctx
    unless r.expr == c do
      throwError "the optimizer changed the synthesized program, but the \
        `CNV` step that would install the change is not wired \
        (P4/D-cz):{indentExpr r.expr}"
    return st

/-- The source's `cons_solve_tac`: `infer_post_triv ORELSE' side_frame_tac`
(P4/D-cy). At this point the postcondition metavariable is already
instantiated by `trans`, so there is nothing left to infer; the phase
checks that. -/
def consSolvePhase : Phase where
  name := "cons_solve"
  prio := 90
  run := fun st => do
    if ← st.goal.isAssigned then return st
    throwError "the translation left the goal open"

/-- The source's `("constraints", solve_constraint_slot THEN
remove_slot_tac, ~1)`. -/
def constraintsPhase : Phase where
  name := "constraints"
  prio := 95
  run := fun st => do
    let open_ ← Constraints.solveConstraintSlot
    if open_.isEmpty then
      Constraints.removeSlot
      return st
    let tys ← open_.mapM fun g => do return indentExpr (← instantiateMVars (← g.getType))
    Constraints.clearSlot
    throwError "{open_.size} constraint(s) could not be \
      solved:{MessageData.joinSep tys.toList ""}"

/-- The source's phase list, in its order. -/
def seprefPipeline : Array Phase :=
  #[preprocPhase, consInitPhase, idPhase, monadifyPhase, optInitPhase,
    transPhase, optPhase, consSolvePhase, constraintsPhase]

/-- The source's `sepref_tac`. -/
def seprefTac (cfg : Config) (goal : MVarId) : TermElabM Unit := do
  let mut st : State := { goal, cfg }
  try
    for ph in seprefPipeline do
      st ← runPhase ph st
  catch e =>
    Constraints.clearSlot
    throw e
  for m in st.log do logInfo m

/-- Run only the named phases — the source's `phases:` argument, and how
the `sepref_dbg_*` table below is built. -/
def seprefPhases (cfg : Config) (names : Array String) (goal : MVarId) :
    TermElabM MVarId := do
  for n in names do
    unless seprefPipeline.any (·.name == n) do
      throwError "sepref: no phase named '{n}'; the phases are \
        {String.intercalate " → " (seprefPipeline.map (·.name)).toList}"
  let mut st : State := { goal, cfg }
  for ph in seprefPipeline do
    if names.contains ph.name then st ← runPhase ph st
  return st.goal

end Tool

/-! ## 3. The entry points -/

open Tool in
/-- The source's `method_setup sepref`: "Automatic refinement to
Imperative/HOL", here to the word-RAM IR. -/
elab "sepref" : tactic => do
  let g ← Tactic.getMainGoal
  for m in ((← instantiateMVars (← g.getType)).collectMVars {}).result do
    m.setKind .natural
  seprefTac {} g
  Tactic.replaceMainGoal []

open Tool in
/-- The source's `method_setup sepref_dbg_keep`: the whole pipeline, in
debug mode. -/
elab "sepref_dbg_keep" : tactic => do
  let g ← Tactic.getMainGoal
  for m in ((← instantiateMVars (← g.getType)).collectMVars {}).result do
    m.setKind .natural
  seprefTac { debugMode := true, tracing := true } g
  Tactic.replaceMainGoal []

/-! ### The `sepref_dbg_*` table (source lines 184–287)

One entry for one entry. The frame family (`sepref_dbg_frame`,
`_merge`, `_prepare_frame`) is in `Sepref/Frame.lean`; the translate
family (`sepref_dbg_trans`, `_trans_keep`, `_trans_step`, `_side`,
`_side_keep`, `_align_goal`, `_cond`) is in `Sepref/Translate.lean`;
the `id`/`monadify` families are wave B2's `sepref_id_op` and
`monadify`. What is left is the driver's own. -/

open Tool in
/-- The source's `sepref_dbg_preproc`. -/
elab "sepref_dbg_preproc" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases {} #["preproc"] g
  Tactic.replaceMainGoal [g']

open Tool in
/-- The source's `sepref_dbg_cons_init`. -/
elab "sepref_dbg_cons_init" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases {} #["cons_init"] g
  Tactic.replaceMainGoal [g']

open Tool in
/-- The source's `sepref_dbg_id`. -/
elab "sepref_dbg_id" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases {} #["id"] g
  Tactic.replaceMainGoal [g']

open Tool in
/-- The source's `sepref_dbg_id_keep`. -/
elab "sepref_dbg_id_keep" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases { debugMode := true } #["id"] g
  Tactic.replaceMainGoal [g']

open Tool in
/-- The source's `sepref_dbg_monadify`. -/
elab "sepref_dbg_monadify" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases {} #["monadify"] g
  Tactic.replaceMainGoal [g']

open Tool in
/-- The source's `sepref_dbg_monadify_keep`. -/
elab "sepref_dbg_monadify_keep" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases { debugMode := true } #["monadify"] g
  Tactic.replaceMainGoal [g']

open Tool in
/-- The source's `sepref_dbg_opt_init`. -/
elab "sepref_dbg_opt_init" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases {} #["opt_init"] g
  Tactic.replaceMainGoal [g']

open Tool in
/-- The source's `sepref_dbg_opt`. -/
elab "sepref_dbg_opt" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases {} #["opt"] g
  Tactic.replaceMainGoal [g']

open Tool in
/-- The source's `sepref_dbg_cons_solve`. -/
elab "sepref_dbg_cons_solve" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases {} #["cons_solve"] g
  Tactic.replaceMainGoal (if ← g'.isAssigned then [] else [g'])

open Tool in
/-- The source's `sepref_dbg_cons_solve_keep`. -/
elab "sepref_dbg_cons_solve_keep" : tactic => do
  let g ← Tactic.getMainGoal
  try
    let g' ← seprefPhases { debugMode := true } #["cons_solve"] g
    Tactic.replaceMainGoal (if ← g'.isAssigned then [] else [g'])
  catch e => logInfo (← e.toMessageData.toString)

open Tool in
/-- The source's `sepref_dbg_constraints`. -/
elab "sepref_dbg_constraints" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← seprefPhases {} #["constraints"] g
  Tactic.replaceMainGoal (if ← g'.isAssigned then [] else [g'])

/-- Print the constraint slot — the source's `print_slot`, under the
`sepref_dbg_*` name the table gives it. -/
elab "sepref_dbg_print_slot" : tactic => do
  logInfo (← Constraints.slotMessage)

open Tool in
/-- Report what the pipeline would fail with, as `info` — the
`Autoref/Solver.lean` precedent, so a gate can pin a failure envelope
without leaving a failing declaration behind. -/
elab "sepref_trace" : tactic => do
  let g ← Tactic.getMainGoal
  for m in ((← instantiateMVars (← g.getType)).collectMVars {}).result do
    m.setKind .natural
  try
    seprefTac {} g
    Tactic.replaceMainGoal []
  catch e => logInfo (← e.toMessageData.toString)

/-- The list of phases, for `#eval` and for messages. -/
def seprefPhaseList : String :=
  String.intercalate " → "
    (Tool.seprefPipeline.map (fun p => s!"{p.name}({p.prio})")).toList

end Lax13Proofs.Refine.Sepref
