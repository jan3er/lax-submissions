import Lax13Proofs.Refine.Autoref.Tagging

/-!
The phase driver: a priority-ordered pipeline of passes over one
translation state.

Port of `thys/Automatic_Refinement/Tool/Autoref_Phases.thy` of AFP
`Automatic_Refinement` (Lammich) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 — AFP for Isabelle2025-2,
release 2026-02-06. The verbatim source text this file is checked
against is `plans/word-ram/refinement-tower/p2-tool-extracts.md` §6.
Design record §3, P2 row 4:

> Autoref phases: id-ops, fix-rel, translate (`Autoref_Phases`,
> `Autoref_Id_Ops`, `Autoref_Fix_Rel`, `Autoref_Translate`,
> `Autoref_Tagging`) → `Autoref/Tool.lean` (phases under source names):
> locales carrying phase state → structures threaded through a `MetaM`
> pipeline.

This file is the *structure threaded through the pipeline* and the
driver that threads it. The four phases themselves are in
`Autoref/IdOps.lean` (`id_op`, `rel_inf`), `Autoref/FixRel.lean`
(`fix_rel`) and `Autoref/Translate.lean` (`trans`), which is the
source's own file split; `Autoref/Tool.lean` registers them in the
source's priority order.

## The source, verbatim

`Autoref_Phases.thy` has no lemmas and no `attribute_setup` /
`method_setup` — it is entirely ML infrastructure. Its citable form is
the module signature, which documents the record every phase must
implement:

```ml
signature AUTOREF_PHASES = sig
  type phase = {
    init: Proof.context -> Proof.context,
    tac: Proof.context -> int -> int -> tactic,
    analyze: Proof.context -> int -> int -> thm -> bool,
    pretty_failure: Proof.context -> int -> int -> thm -> Pretty.T
  }

  val register_phase: string -> int -> phase ->
    morphism -> Context.generic -> Context.generic
  val delete_phase: string -> morphism -> Context.generic -> Context.generic
  val get_phases: Proof.context -> (string * int * phase) list

  val get_phase: string -> Proof.context -> (string * int * phase) option

  val init_phase: (string * int * phase) -> Proof.context -> Proof.context
  val init_phases:
    (string * int * phase) list -> Proof.context -> Proof.context

  val init_data: Proof.context -> Proof.context

  val declare_solver: thm list -> binding -> string
    -> (Proof.context -> tactic') -> morphism
    -> Context.generic -> Context.generic

  val phase_tac: (string * int * phase) -> Proof.context -> tactic'
  val phases_tac: (string * int * phase) list -> Proof.context -> tactic'
  val all_phases_tac: Proof.context -> tactic'

  val phases_tacN: string list -> Proof.context -> tactic'
  val phase_tacN: string -> Proof.context -> tactic'

  val cfg_debug: bool Config.T
  val cfg_trace: bool Config.T
  val cfg_keep_goal: bool Config.T
end
```

and the structural description the extract gives of the driver:

> phases are kept in a priority-sorted `Generic_Data` list (`phase_data`,
> `register_phase`/`delete_phase`/`get_phases`); `do_phase` runs one
> phase's `tac` under `DETERM`, times it if `cfg_trace`, then branches on
> `analyze` into either the continuation (`THEN_INTERVAL`, chaining to
> the next phase) or `handle_fail_tac`, which prints `pretty_failure`'s
> output under `cfg_debug` and then either fails the tactic (default)
> or, if `cfg_keep_goal` is set, returns the goal state unchanged.

## Substrate deltas and departures, each flagged

**P0 — the wave is six modules where design record §7 lists one.** §7's
P2 skeleton is `Autoref/{Relators,Param,Solver,Tool}`; wave B2 already
split `Tagging.lean` out of it (its delta T1) for the reason the source
itself splits `Autoref_Tagging.thy` out. This wave splits the rest the
same way and for the same reason: `Autoref/{Phases,IdOps,FixRel,
Translate,Tool,BindingsHOL}.lean` stand one-for-one against
`Tool/Autoref_{Phases,Id_Ops,Fix_Rel,Translate,Tool}.thy` and
`Autoref_Bindings_HOL.thy`, so that a reader checking this port against
the extract checks one file against one theory, and so that each
phase's *constants*, its *calculus* and its *implementation* live
together — which is how the source arranges them and what the fidelity
charter's "the sources' design wins by default" means here. Folding all
five into `Tool.lean` would have produced one 2000-line module whose
correspondence to the extract had to be reconstructed by eye. Recorded
as a departure from §7's file list, not from the source.
(`Autoref_Gen_Algo.thy` is the one theory that does *not* get its own
module — `Autoref/Tool.lean` delta O5 says why.)

**P1 — the phase record carries an explicit state, not a
`Proof.context`.** The source's four phases communicate through the
proof context (each phase's `init` installs its rule nets there) and
through the goal state (each phase rewrites the goal its successor
reads). Design record §3 prescribes the Lean rendering — "locales
carrying phase state → structures threaded through a `MetaM` pipeline" —
and `State` below is that structure. It carries the *goal* (so the
source's goal-state channel survives verbatim: `id_op` and `rel_inf`
really do rewrite `(?c, a) ∈ ?R` into `(?c, a') ∈ ?R`, exactly as the
source's `ID_init` / `ROI_init` resolutions do) plus the three pieces of
data that have nowhere else to live: the interface `id_op` assigned, the
extra rules the call site supplied, and the configuration.

**P1a — the pipeline monad is `TermElabM`, not `MetaM`.** Design record
§3 says "a `MetaM` pipeline", and every phase body below is a `MetaM`
computation; the signature is one level up because the `trans` phase
discharges side conditions through wave B2's `tagged_solver`, which is a
`TacticM` tactic, and `Lean.Elab.Tactic.run` — the only way to run a
tactic on a metavariable — lands in `TermElabM`. Nothing else in the
pipeline uses the extra capability.

**P2 — `tac`'s goal interval becomes the single `goal` field.** The
source's `tac : Proof.context -> int -> int -> tactic` operates on a
*range* `i..j` of subgoals, because an Isabelle tactic may split one
goal into many and the phase driver must know which ones are its own.
A `MetaM` pass returning a new `State` needs no interval: a phase that
manufactures subgoals discharges them itself (`fix_rel`, `trans`) or
threads the one it produced (`id_op`, `rel_inf`).

**P3 — `analyze` returns the failure message it found, and
`pretty_failure` renders it.** The source splits the two because an
Isabelle tactic cannot carry a message: `analyze` returns `bool` and the
driver calls `pretty_failure` on the goal state afterwards. Here
`analyze` returns `Option MessageData` — `none` for the source's `true`
— and `prettyFailure` is still a separate hook, because it is also
applied to *exceptions* thrown from inside `run`, which is where the
phases actually report (a Lean exception carries its message, so the
common case needs no `analyze` at all). Both hooks are kept so that a
phase can report either way, as the source's do.

**P4 — the registry is an `IO.Ref`, not an environment extension.** A
`Phase` holds `MetaM` closures, which no environment extension can
serialise; the source's `Generic_Data` holds ML closures for the same
reason and is likewise not part of any persistent theory content. The
registration therefore happens in `initialize` blocks (`Autoref/Tool.lean`),
which Lean runs once per process at import time — the same "runs when
the theory is loaded" semantics the source's `declaration` blocks have.
`register_phase` / `delete_phase` / `get_phases` / `get_phase` are ported
one for one; `init_phases` is `Phase.init` run by the driver;
`init_data` has no counterpart, because there is no lazily-initialised
context data to guard (delta P1 removed the channel it guarded).

**P5 — `declare_solver` is `Autoref/Solver.lean`'s `declare_solver`.**
The source wraps `Tagged_Solver.declare_solver` here only to force
`init_data`; with no context data to initialise (P4), the wrapper has no
content, and wave B2's command is used directly.

**P6 — the failure format is uniform, and that is the point.** The
extract records that the source has "no single shared error format" —
each phase renders its own leftovers. The plan's supervision-legibility
watch item asks for the opposite: *every* pipeline failure must name its
phase and its unmet side condition. So `runPhase` wraps whatever the
phase reports in one envelope naming the phase and its priority, and the
phases fill the envelope with the offending subterm. This is an
addition, not a loss: each phase's own message is still its own.
-/

open Lean Meta Elab

namespace Lax13Proofs.Refine

namespace Autoref

/-! ### Configuration (the source's three `Config.T` flags) -/

/-- The source's `cfg_trace` / `cfg_debug` / `cfg_keep_goal`, as one
record rather than three context options (wave B2's delta S5: Lean's
`set_option` plumbing buys nothing at three flags, and the `autoref`
method takes them as parenthesised arguments anyway). -/
structure Config where
  /-- The source's `cfg_trace`: report each phase's progress. -/
  trace : Bool := false
  /-- The source's `cfg_debug`: report a failing phase's diagnosis even
  when the failure is caught. -/
  debug : Bool := false
  /-- The source's `cfg_keep_goal`: on failure leave the goal in the
  proof state instead of failing outright. -/
  keepGoal : Bool := false
  deriving Inhabited, Repr

/-! ### The state threaded through the pipeline (delta P1) -/

/-- The pipeline state. `goal` is the source's goal-state channel — the
`(?c, a) ∈ ?R` goal each phase reads and rewrites; the rest is the
context channel. -/
structure State where
  /-- The current `(?c, a) ∈ ?R` goal. `id_op` and `rel_inf` replace it
  with the same goal over a rewritten abstract term; `trans` closes it. -/
  goal : MVarId
  /-- The abstract term the pipeline was started on, kept for messages. -/
  abs : Expr
  /-- The interface `id_op` assigned to `abs`. -/
  intf : Interface := .const "i_std"
  /-- Extra refinement rules supplied by the call site: the source's
  `assumes [autoref_rules]` / `notes [autoref_rules] = …` (delta O1 in
  `Autoref/Tool.lean`). Each is a proof term whose type is, or ends in,
  `(c, a) ∈ R`. -/
  extras : Array Expr := #[]
  /-- The source's three config flags. -/
  cfg : Config := {}
  /-- The trace, when `cfg.trace` is set. -/
  log : Array MessageData := #[]

/-- Append a trace line, if tracing is on. -/
def State.note (st : State) (msg : MessageData) : State :=
  if st.cfg.trace then { st with log := st.log.push msg } else st

/-! ### The phase record (the source's `type phase`) -/

/-- The source's

```ml
type phase = {
  init: Proof.context -> Proof.context,
  tac: Proof.context -> int -> int -> tactic,
  analyze: Proof.context -> int -> int -> thm -> bool,
  pretty_failure: Proof.context -> int -> int -> thm -> Pretty.T
}
```

with `tac` renamed `run` (it is not a tactic — delta P2) and `analyze`
returning the message it found rather than a `bool` (delta P3). -/
structure Phase where
  /-- The phase's name, as `register_phase` records it. -/
  name : String
  /-- The source's `init`. -/
  init : State → TermElabM State := pure
  /-- The source's `tac` (delta P2). -/
  run : State → TermElabM State
  /-- The source's `analyze`: `none` is the source's `true` — the phase
  closed everything it was supposed to (delta P3). -/
  analyze : State → TermElabM (Option MessageData) := fun _ => pure none
  /-- The source's `pretty_failure`, applied to whatever `run` threw or
  `analyze` reported (delta P3). -/
  prettyFailure : State → MessageData → TermElabM MessageData := fun _ m => pure m

/-! ### The registry (delta P4) -/

/-- The source's `phase_data` `Generic_Data` store. -/
initialize phasesRef : IO.Ref (Array (String × Nat × Phase)) ← IO.mkRef #[]

/-- The source's `register_phase`. Re-registering a name replaces the
earlier entry, so that a double import cannot double-run a phase. -/
def registerPhase (name : String) (prio : Nat) (ph : Phase) : IO Unit :=
  phasesRef.modify fun ps => (ps.filter (·.1 != name)).push (name, prio, ph)

/-- The source's `delete_phase`. -/
def deletePhase (name : String) : IO Unit :=
  phasesRef.modify fun ps => ps.filter (·.1 != name)

/-- The source's `get_phases`: every registered phase, in priority
order (lowest priority number first — the source's `id_op` 10 →
`rel_inf` 20 → `fix_rel` 22 → `trans` 30). Ties break on the name, so
the order does not depend on registration order. -/
def getPhases : IO (Array (String × Nat × Phase)) := do
  return (← phasesRef.get).qsort fun a b =>
    a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1)

/-- The source's `get_phase`. -/
def getPhase (name : String) : IO (Option (String × Nat × Phase)) := do
  return (← getPhases).find? (·.1 == name)

/-- The registry as a string, for `#eval` and for failure messages. -/
def phaseList : IO String := do
  let ps ← getPhases
  return String.intercalate " → " (ps.map (fun p => s!"{p.1}({p.2.1})")).toList

/-! ### The driver -/

/-- The source's `do_phase`: run one phase, and on failure report *which
phase* failed and *what* it could not do (delta P6). -/
def runPhase (nm : String) (prio : Nat) (ph : Phase) (st : State) : TermElabM State := do
  let st ← ph.init st
  let st ←
    try
      ph.run st
    catch e =>
      let inner ← ph.prettyFailure st e.toMessageData
      throwError "autoref: phase '{nm}' (priority {prio}) failed.\n{inner}"
  match ← ph.analyze st with
  | some m =>
    let inner ← ph.prettyFailure st m
    throwError "autoref: phase '{nm}' (priority {prio}) left work undone.\n{inner}"
  | none =>
    return st.note m!"phase '{nm}' (priority {prio}) succeeded"

/-- The source's `phases_tac`: run the given phases in order. -/
def phasesTac (phases : Array (String × Nat × Phase)) (st : State) : TermElabM State := do
  let mut st := st
  for (nm, prio, ph) in phases do
    st ← runPhase nm prio ph st
  return st

/-- The source's `all_phases_tac`. -/
def allPhasesTac (st : State) : TermElabM State := do
  phasesTac (← getPhases) st

/-- The source's `phases_tacN`: run only the named phases, in registry
order. An unknown name is an error that lists the registry — the
supervision-legibility requirement applied to the driver's own
argument. -/
def phasesTacN (names : Array String) (st : State) : TermElabM State := do
  let ps ← getPhases
  for n in names do
    unless ps.any (·.1 == n) do
      throwError "autoref: no phase named '{n}'; registered phases: {← phaseList}"
  phasesTac (ps.filter (fun p => names.contains p.1)) st

/-- The source's `phase_tacN`. -/
def phaseTacN (name : String) (st : State) : TermElabM State :=
  phasesTacN #[name] st

/-! ### Term utilities shared by the phases

The source keeps these on the ML side of `Autoref_Tagging.thy`
(`untag_conv` and the `APP`/`ABS`/`OP`-aware term walks every phase
runs). `Autoref/Tagging.lean` holds the tag *constants*; the walks over
them are here, where all four phases can reach them. -/

/-- Parse a refinement goal `(c, a) ∈ R` into `(c, a, R)`. -/
def parseRefine? (ty : Expr) : Option (Expr × Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, coll, elem]) =>
    match elem.getAppFnArgs with
    | (``Prod.mk, #[_, _, c, a]) => some (c, a, coll)
    | _ => none
  | _ => none

/-- Build a refinement goal `(c, a) ∈ R`. -/
def mkRefine (c a R : Expr) : MetaM Expr := do
  mkAppM ``Membership.mem #[R, ← mkAppM ``Prod.mk #[c, a]]

/-- Match the source's `f$a` (`APP f a`). -/
def isAPP? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``APP, #[_, _, f, x]) => some (f, x)
  | _ => none

/-- Match the source's `ANNOT t a`, returning the term and the
annotation. -/
def isANNOT? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``ANNOT, #[_, t, a]) => some (t, a)
  | _ => none

/-- Match the source's `OP x`. -/
def isOP? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``OP, #[_, x]) => some x
  | _ => none

/-- Match the source's `t ::: R` (`ANNOT t (rel_annot R)`), returning
`(t, R)`. -/
def isRelANNOT? (e : Expr) : Option (Expr × Expr) := do
  let (t, a) ← isANNOT? e
  match a.getAppFnArgs with
  | (``rel_annot, #[_, _, R]) => some (t, R)
  | _ => none

/-- Match an *operator occurrence* `OP f ::: R`: the shape `fix_rel`
collects constraints from and `trans` resolves rules against. -/
def isOpRel? (e : Expr) : Option (Expr × Expr) := do
  let (t, R) ← isRelANNOT? e
  let f ← isOP? t
  some (f, R)

/-- Peel a tagged application spine `f $ᵃ x₁ $ᵃ … $ᵃ xₙ`, returning the
head and the arguments in order. -/
partial def peelAPP (e : Expr) : Expr × Array Expr :=
  match isAPP? e with
  | some (f, x) => let (h, args) := peelAPP f; (h, args.push x)
  | none => (e, #[])

/-- The simp set of the source's `autoref_tag_defs` — `PROTECT_def`,
`ANNOT_def`, `OP_def`, `APP_def`, as `Autoref/Tagging.lean` tagged them.
This is what the source's `trans_tac` post-pass and its
`REMOVE_INTERNAL_conv` both run. -/
def tagDefsContext : MetaM Simp.Context := do
  let some ext ← getSimpExtension? `autoref_tag_defs
    | throwError "autoref: the simp set 'autoref_tag_defs' is not registered"
  Simp.mkContext {} (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)

/-- Strip every autoref tag from a term, returning the cleaned term.
The source's `untag_conv`; also its `trans_tac` post-pass, which is
where the synthesized concrete term loses its `$`s. -/
def untag (e : Expr) : MetaM Expr := do
  let (r, _) ← Meta.simp e (← tagDefsContext)
  return r.expr

end Autoref

end Lax13Proofs.Refine
