import Lax13Proofs.Refine.Autoref.Tagging

/-!
The side-condition solver registry: solvers keyed by tag, dispatched by
priority.

Port of `thys/Automatic_Refinement/Lib/Tagged_Solver.thy` (and, through
it, `Lib/Prio_List.thy`) of AFP `Automatic_Refinement` (Lammich) at the
pin recorded in `plans/word-ram/refinement-tower/design.md` §1 — AFP for
Isabelle2025-2, release 2026-02-06. Design record §3, P2 row 3:

> tagged solvers, priority lists (`Tagged_Solver`, `Prio_List`,
> `Attr_Comb`) → `Autoref/Solver.lean`: side-condition solver registry.
> ML functor gymnastics → ordinary Lean 4 extension points; DiscrTree
> replaces `Anti_Unification`-based indexing (a strict improvement the
> charter's rule 3 permits: infrastructure, not calculus).

## The source

`Tagged_Solver.thy` is pure ML — there is no Isar surface to quote
beyond one `method_setup` line, so the citable form of the source is its
ML *signature*, which is the interface the port is measured against:

```ml
signature TAGGED_SOLVER = sig
  type solver = thm list * string * string * (Proof.context -> tactic')

  val get_solvers: Proof.context -> solver list
  val declare_solver: thm list -> binding -> string
    -> (Proof.context -> tactic') -> morphism
    -> Context.generic -> Context.generic

  val lookup_solver: string -> Context.generic -> solver option
  val add_triggers: string -> thm list -> morphism ->
    Context.generic -> Context.generic

  val delete_solver: string -> morphism -> Context.generic -> Context.generic

  val tac_of_solver: Proof.context -> solver -> tactic'

  val get_potential_solvers: Proof.context -> int -> thm -> solver list
  val get_potential_tacs: Proof.context -> int -> thm -> tactic' list

  val solve_greedy_step_tac: Proof.context -> tactic'
  val solve_greedy_tac: Proof.context -> tactic'
  val solve_greedy_keep_tac: Proof.context -> tactic'

  val solve_full_step_tac: Proof.context -> tactic'
  val solve_full_tac: Proof.context -> tactic'
  val solve_full_keep_tac: Proof.context -> tactic'

  val cfg_keep: bool Config.T
  val cfg_trace: bool Config.T
  val cfg_full: bool Config.T
  val cfg_step: bool Config.T

  val solve_tac: Proof.context -> tactic'

  val pretty_solvers: Proof.context -> Pretty.T
end

method_setup tagged_solver =
  "Select tactic to solve goal by pattern"
```

and `Prio_List.thy`, the ordering structure `Tagged_Solver` stores its
solvers in — "a list of items with insertion operation relative to other
items (after, before) and relative to absolute positions (first, last)":

```ml
signature PRIO_LIST = sig
  type T
  type item

  val empty: T
  val add_first: T -> item -> T
  val add_last: T -> item -> T
  val add_before: T -> item -> item -> T
  val add_after: T -> item -> item -> T

  val delete: item -> T -> T

  val prio_of: (item -> bool) -> (item * item -> bool) -> T -> int
  val contains: T -> item -> bool

  val dest: T -> item list

  val merge: T * T -> T
  val merge': T * T -> item list * T
end
```

(Both fetched 2026-07-29 from the mirror the P2 extract files use,
`isabelle-prover/mirror-afp-devel` at `master` — the same mirror and the
same justification as `p2-autoref-extracts.md`'s header. Neither file
is covered by an extract in `plans/`, because both are ML: the extract
convention of this campaign is to quote Isar, and there is none here
beyond the `method_setup` binder line above. The two signature blocks
are therefore reproduced in this header, and *this header is the
citable form of the source* for anything downstream wants to check.)

`solver` reads: **trigger theorems**, **name**, **description**,
**tactic**. That four-field shape, the priority ordering, and the
`potential solvers → try them → report` dispatch are what this file
ports.

## Role

A "side condition" is a goal the translation pipeline manufactures
rather than one the user wrote: `SIDE_PRECOND (l ≠ [])` from
`autoref_hd`, single-valuedness of a relator, a `GEN_OP` instance, a
deferred constraint. Each family has its own decision procedure, and no
single tactic should know about all of them. `Tagged_Solver` is the
indirection: a *tag* constant marks the family, each decision procedure
registers itself against a tag, and the pipeline discharges everything
it manufactures with one call to `tagged_solver`. Wave C's rule files
register into it; nothing registers here except this file's own demo.

## What this seed does *not* do

Stated against the signature above, in the P1 style (the `refine_vcg`
header's "this is the *seed* of the abstract VCG, and its maturity is
stated honestly"):

**S1 — triggers are head constants, not trigger theorems.** The
source's first `solver` component is a `thm list` matched against the
goal by `Anti_Unification`; here it is one `Name`, the head constant of
the goal. Source triggers that discriminate below the head — two
`SIDE_PRECOND` solvers keyed on the *shape* of the precondition, say —
collapse onto the same tag here. The consequences are contained and
worth naming: a solver must fail cleanly on a goal it does not handle,
and `tagged_solver_full` (which walks the whole candidate list) exists
precisely so that a coarse trigger stays recoverable. Refining `trigger`
to a pattern is a change behind `TaggedSolver.potential` and nothing
else.

**S2 — the registry is a linear scan, not a DiscrTree.** Design record
P2 row 3 promises DiscrTree in place of `Anti_Unification` indexing;
what is implemented is a filter over the registry array. At spine scope
(a handful of solvers, called once per manufactured side condition) the
difference is unmeasurable, and pretending otherwise would be the
dishonest option. The DiscrTree upgrade is, again, local to
`TaggedSolver.potential`.

**S3 — priority is a `Nat`, not a `Prio_List`.** The source orders
solvers by *relative* insertion (`add_first` / `add_last` /
`add_before` / `add_after`), reads a position back with `prio_of`, and
merges two orders when contexts merge. A numeric key was chosen instead
because a Lean persistent environment extension is a flat array whose
entries arrive in import order: relative insertion would have to be
replayed at import time and would not be confluent across independent
imports, whereas a `Nat` sorts deterministically however the modules are
arranged. Higher wins; ties break on the solver name, so the order is
total and reproducible. `delete_solver`, `add_triggers` and `merge` have
no counterpart.

**S4 — the tactic payload is stored syntax, not an ML closure.** The
source stores `Proof.context -> tactic'`, a closure over its declaration
context. We store the `Syntax` of the tactic together with the
namespace and `open` declarations in force where it was declared, and
re-elaborate it at dispatch time inside that name-resolution context —
so a solver written in one module resolves its own constants when run
from another (the demo below exercises exactly this). What is *not*
captured is term-level context: a solver tactic must not depend on
section `variable`s or local hypotheses of its declaration site.

**S5 — no goal addressing, no config flags.** `tactic'` in the source is
`int -> tactic`, and `get_potential_solvers` takes a goal index; here
every entry point acts on the main goal. The four `Config.T` flags
become tactic *names* — `tagged_solver` (greedy), `tagged_solver_full`
(backtracking, `cfg_full`), `tagged_solver_step` (one step, goals kept,
`cfg_step` + `cfg_keep`), `tagged_solver_trace` (`cfg_trace`) — because
Lean's `set_option` plumbing buys nothing at four flags.
`solve_full_keep_tac` has no counterpart. `pretty_solvers` is
`TaggedSolver.explain`.

**S6 — greedy is one step, not a loop.** The source's
`solve_greedy_tac` iterates `solve_greedy_step_tac` to exhaustion.
`tagged_solver` here dispatches once and requires the chosen solver to
close the goal, which is what a side-condition solver does; a solver
that wants to recurse calls `tagged_solver` again from inside its own
tactic. Recorded rather than worked around: the iteration is
three lines whenever a consumer needs it, and a bounded loop with no
consumer is a maintenance liability.

**S7 — the record and its extension live one module upstream.**
`structure TaggedSolver` (the port of the source's `type solver`, field
for field) and the persistent environment extension holding the registry
are declared in `Autoref/Attrs.lean`, not here. This is P1's delta B7
again, in its sharper form: an `initialize` value is unavailable to its
own module, so a `declare_solver` *in this file* — which the gate below
needs — dies with `cannot evaluate [init] declaration … in the same
module`. `Attrs.lean` is the module that exists for this constraint, and
the split costs nothing: everything that reasons about the record is
here, and the field comments there point at the deltas above.

The dispatch failure messages carry the plan's supervision-legibility
requirement: every failure names the tag it dispatched on and every
solver it considered, with priorities. The message text is built by the
`TaggedSolver.*Msg` functions below, and the gate at the bottom of this
file checks those functions' output verbatim.
-/

open Lean Elab Meta Tactic

namespace Lax13Proofs.Refine

namespace TaggedSolver

variable {m : Type → Type}

/-- The source's `declare_solver`: add a solver to the registry. This is
the API wave C's rule files use, either directly or through the
`declare_solver` command below. -/
def add [Monad m] [MonadEnv m] (s : TaggedSolver) : m Unit :=
  modifyEnv fun env => taggedSolverExt.addEntry env s

/-- The source's `get_solvers`: every registered solver, in no
particular order. -/
def all [Monad m] [MonadEnv m] : m (Array TaggedSolver) := do
  return taggedSolverExt.getState (← getEnv)

/-- The source's `lookup_solver`. -/
def lookup [Monad m] [MonadEnv m] (n : Name) : m (Option TaggedSolver) := do
  return (← all).find? (·.name == n)

/-- Sort by priority, higher first, ties broken on the name so that the
order is total and does not depend on import order (delta S3). -/
def byPriority (ss : Array TaggedSolver) : Array TaggedSolver :=
  ss.qsort fun a b => a.prio > b.prio || (a.prio == b.prio && Name.lt a.name b.name)

/-- The source's `get_potential_solvers`: the solvers that claim `tag`,
in the order `tagged_solver` will try them (delta S1, S2). -/
def potential [Monad m] [MonadEnv m] (tag : Name) : m (Array TaggedSolver) := do
  return byPriority ((← all).filter (·.trigger == tag))

/-- Every tag some registered solver claims, deduplicated and sorted —
what a "no solver for this tag" message offers instead. -/
def tags [Monad m] [MonadEnv m] : m (Array Name) := do
  let ts := (← all).map (·.trigger)
  let ts := ts.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
  return ts.qsort Name.lt

/-! ### Messages (the supervision-legibility requirement) -/

/-- One solver, as it appears in a message. -/
def describe (s : TaggedSolver) : String := s!"{s.name} (priority {s.prio})"

/-- A candidate list, as it appears in a message. -/
def solverList (ss : Array TaggedSolver) : String :=
  if ss.isEmpty then "(none)" else String.intercalate ", " (ss.map describe).toList

/-- A tag list, as it appears in a message. -/
def tagList (ns : Array Name) : String :=
  if ns.isEmpty then "(none)" else String.intercalate ", " (ns.map toString).toList

/-- The message when no solver claims the tag at all. -/
def noSolverMsg (tag : Name) (known : Array Name) : String :=
  s!"tagged_solver: no solver is registered for tag '{tag}'; registered tags: {tagList known}"

/-- The message when the highest-priority solver was committed to and
failed (`tagged_solver`, greedy). -/
def greedyFailMsg (tag : Name) (cands : Array TaggedSolver) : String :=
  s!"tagged_solver: the highest-priority solver for tag '{tag}' failed; \
candidates in priority order: {solverList cands}; 'tagged_solver_full' would try the rest"

/-- The message when every candidate was tried and every one failed
(`tagged_solver_full`). -/
def fullFailMsg (tag : Name) (cands : Array TaggedSolver) : String :=
  s!"tagged_solver_full: every solver for tag '{tag}' failed; \
tried, in priority order: {solverList cands}"

/-- The message when a solver ran but left the goal open. -/
def openGoalMsg (tag : Name) (s : TaggedSolver) : String :=
  s!"tagged_solver: solver {describe s} ran on tag '{tag}' but did not close the goal; \
use 'tagged_solver_step' to keep what it produced"

/-- The source's `pretty_solvers`, narrowed to one tag: what
`tagged_solver` would do with a goal headed by `tag`, as a string. Both
branches are the messages the dispatcher itself throws, so checking this
function checks the dispatcher's legibility. -/
def explain [Monad m] [MonadEnv m] (tag : Name) : m String := do
  let cands ← potential tag
  if cands.isEmpty then
    return noSolverMsg tag (← tags)
  else
    return s!"tagged_solver: solvers for tag '{tag}', in priority order: {solverList cands}"

/-! ### Dispatch -/

/-- Run a stored solver's tactic in the name-resolution context it was
declared in (delta S4). -/
def run (s : TaggedSolver) : TacticM Unit :=
  withTheReader Core.Context
    (fun ctx => { ctx with currNamespace := s.ns, openDecls := s.openDecls })
    (evalTactic s.tac)

/-- The tag a goal dispatches on: the head constant of its type
(delta S1). -/
def goalTag (goal : MVarId) : MetaM Name := do
  let ty ← instantiateMVars (← goal.getType)
  match (← whnfR ty).getAppFn with
  | .const n _ => return n
  | _ => throwError "tagged_solver: the goal has no head constant to dispatch on:{indentExpr ty}"

/-- The dispatcher. `full` walks the whole candidate list with
backtracking (the source's `cfg_full`); otherwise the highest-priority
candidate is committed to (greedy). `keep` retains whatever the solver
left open (the source's `cfg_keep`); otherwise the solver must close the
goal. -/
def dispatch (full keep : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  let tag ← goalTag goal
  let cands ← potential tag
  if cands.isEmpty then throwError (noSolverMsg tag (← tags))
  let rest := (← getGoals).drop 1
  -- Every failure path below restores this state before throwing. A
  -- solver can fail *after* changing the goal list — `demo_step` in the
  -- gate does exactly that, splitting its goal and then being refused
  -- for not closing it — and a dispatcher that threw from there would
  -- leave `rest` dropped on the floor.
  let st ← saveState
  let attempt (s : TaggedSolver) : TacticM Unit := do
    setGoals [goal]
    run s
    let remaining ← getGoals
    unless keep || remaining.isEmpty do throwError (openGoalMsg tag s)
    setGoals (remaining ++ rest)
  if full then
    for s in cands do
      try
        attempt s
        return
      catch _ => st.restore
    throwError (fullFailMsg tag cands)
  else
    try
      attempt cands[0]!
    catch e =>
      let cause ← e.toMessageData.toString
      st.restore
      throwError s!"{greedyFailMsg tag cands}. The solver failed with: {cause}"

end TaggedSolver

/-! ### The tactics and the declaration command -/

/-- The source's `tagged_solver` method, greedy (its default: `cfg_full`
is off): dispatch on the goal's tag, commit to the highest-priority
solver that claims it, and require it to close the goal. -/
syntax (name := taggedSolverTac) "tagged_solver" : tactic

/-- The source's `solve_full_tac` (`cfg_full`): try every solver that
claims the goal's tag, in priority order, until one closes the goal. -/
syntax (name := taggedSolverFullTac) "tagged_solver_full" : tactic

/-- The source's `solve_greedy_keep_tac` (`cfg_step` + `cfg_keep`): one
greedy dispatch step, keeping whatever the solver left open. -/
syntax (name := taggedSolverStepTac) "tagged_solver_step" : tactic

/-- The source's `cfg_trace`, as a tactic: dispatch greedily, but report
failure as an `info` message instead of throwing. This is what the gate
below uses to check the dispatcher's own failure text without leaving a
failing declaration in the environment. -/
syntax (name := taggedSolverTraceTac) "tagged_solver_trace" : tactic

elab_rules : tactic
  | `(tactic| tagged_solver) => TaggedSolver.dispatch (full := false) (keep := false)
  | `(tactic| tagged_solver_full) => TaggedSolver.dispatch (full := true) (keep := false)
  | `(tactic| tagged_solver_step) => TaggedSolver.dispatch (full := false) (keep := true)
  | `(tactic| tagged_solver_trace) => do
      try TaggedSolver.dispatch (full := false) (keep := false)
      catch e => logInfo (← e.toMessageData.toString)

open Lean.Parser.Tactic in
/-- The source's `declare_solver`, as a command:

```
declare_solver my_solver for MyTag at 100 with "what it does" :=
  <tactic sequence>
```

registers `<tactic sequence>` as a solver for goals headed by the
constant `MyTag`, at priority `100`. The priority defaults to `0` and
the description to the empty string. The tactic is stored as syntax and
re-elaborated in this command's namespace and `open` context whenever it
is dispatched (delta S4).

**Delta S8 — the keywords are `for` / `at` / `with`, not `prio` /
`descr`.** A token declared by `syntax` is reserved against identifiers
everywhere downstream, and this module is on the archive root's import
path: declaring `prio` and `descr` would have made two ordinary words
unusable as identifiers archive-wide (it broke this file's own
`let prio := …` first). `for`, `at` and `with` are already Lean
keywords, so reusing them reserves nothing new. -/
syntax (name := declareSolverCmd) "declare_solver " ident " for " ident
  (" at " num)? (" with " str)? " := " tacticSeq : command

elab_rules : command
  | `(command| declare_solver $n:ident for $tr:ident
        $[at $p:num]? $[with $d:str]? := $t:tacticSeq) => do
      let priority := match p with | some p => p.getNat | none => 0
      let description := match d with | some d => d.getString | none => ""
      Command.liftTermElabM do
        let trigger ← realizeGlobalConstNoOverloadWithInfo tr
        TaggedSolver.add
          { name := n.getId, trigger, prio := priority, descr := description,
            tac := t.raw, ns := ← getCurrNamespace, openDecls := ← getOpenDecls }

/-! ### The executable gate (design record ledger D4)

Two demo solvers at different priorities on one demo tag, plus a tag
with no solver at all. Everything the plan asks the gate to show —
dispatch, priority order, and a failure message that names the tag — is
checked here, and every check is either a `#guard_msgs` on the
dispatcher's own message functions or an `example` that must elaborate.
Nothing in this section leaves an error or a `sorry` behind: the two
failure demonstrations use `fail_if_success` and `tagged_solver_trace`.

The demo tag and the demo solvers live in a nested namespace and the
`example`s do not; that is on purpose, and it is the check for delta
S4's name-resolution capture: `demo_low`'s tactic says
`unfold DemoGoal`, an unqualified name that only resolves inside
`Demo`, and it is dispatched from outside it. -/

namespace Demo

-- A `declare_solver` body is *stored*, not run, so the two tactic
-- linters see a tactic block that never executes and never closes a
-- goal. They are right about the syntax and wrong about the file.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The demo tag: a side condition saying a number is small. -/
def DemoGoal (n : Nat) : Prop := n ≤ 10

/-- A second tag, deliberately left without a solver. -/
def UntaggedGoal (n : Nat) : Prop := n = n

/-- What `demo_high` closes, and all it closes. -/
theorem demoGoal_zero : DemoGoal 0 := Nat.zero_le _

declare_solver demo_high for DemoGoal at 100
    with "closes DemoGoal 0, and nothing else" :=
  first
    | exact demoGoal_zero
    | fail "demo_high only closes DemoGoal 0"

declare_solver demo_low for DemoGoal at 50
    with "closes any concrete DemoGoal n with n at most 10" :=
  unfold DemoGoal
  omega

/-- A third tag, whose solver deliberately leaves work behind — the
`keep` / `openGoalMsg` path. -/
def DemoStep (n : Nat) : Prop := n ≤ 10 ∧ n ≤ 20

declare_solver demo_step for DemoStep at 10
    with "splits the conjunction, leaving both halves open" :=
  unfold DemoStep
  constructor

end Demo

section Gate

open TaggedSolver

-- `tagged_solver_trace` reports instead of closing, which is exactly
-- what `linter.unusedTactic` complains about.
set_option linter.unusedTactic false

-- (a) Dispatch solves a tagged goal. `DemoGoal 0` is what the
-- highest-priority solver handles, so greedy dispatch closes it.
example : Demo.DemoGoal 0 := by tagged_solver

-- (a′) …and the *lower*-priority solver's tactic resolves `DemoGoal`
-- unqualified from outside `Demo`, which is delta S4's capture working.
example : Demo.DemoGoal 3 := by tagged_solver_full

-- (b) Priority order is respected — three ways.
--
-- First, at the data level: the candidate list is in priority order.
/-- info: demo_high (priority 100), demo_low (priority 50) -/
#guard_msgs in
#eval show CoreM Unit from do
  IO.println (solverList (← potential ``Demo.DemoGoal))

-- Second, at the dispatch level, and this is the discriminating test:
-- on `DemoGoal 3` *both* solvers apply, `demo_low` would succeed, and
-- greedy dispatch nonetheless fails — because it committed to the
-- higher-priority `demo_high`, which does not handle `3`. Backtracking
-- dispatch then finds `demo_low`.
example : Demo.DemoGoal 3 := by
  fail_if_success tagged_solver
  tagged_solver_full

-- Third, in the failure text itself: the message names the tag, both
-- candidates with their priorities, and the cause reported by the
-- solver that was committed to. (`logInfo` in a tactic appends the goal
-- it fired on, which is why the expected output has a second line —
-- welcome, in a trace.)
/--
info: tagged_solver: the highest-priority solver for tag 'Lax13Proofs.Refine.Demo.DemoGoal' failed; candidates in priority order: demo_high (priority 100), demo_low (priority 50); 'tagged_solver_full' would try the rest. The solver failed with: demo_high only closes DemoGoal 0
⊢ Lax13Proofs.Refine.Demo.DemoGoal 3
-/
#guard_msgs in
example : Demo.DemoGoal 3 := by
  tagged_solver_trace
  tagged_solver_full

-- (c) The failure message on an unhandled tag names the tag, and offers
-- the tags that do have solvers.
/--
info: tagged_solver: no solver is registered for tag 'Lax13Proofs.Refine.Demo.UntaggedGoal'; registered tags: Lax13Proofs.Refine.Demo.DemoGoal, Lax13Proofs.Refine.Demo.DemoStep
-/
#guard_msgs in
#eval show CoreM Unit from do
  IO.println (← explain ``Demo.UntaggedGoal)

example : Demo.UntaggedGoal 3 := by
  fail_if_success tagged_solver
  rfl

-- The `pretty_solvers` branch of `explain`, for a tag that does have
-- solvers.
/-- info: tagged_solver: solvers for tag 'Lax13Proofs.Refine.Demo.DemoGoal', in priority order: demo_high (priority 100), demo_low (priority 50) -/
#guard_msgs in
#eval show CoreM Unit from do
  IO.println (← explain ``Demo.DemoGoal)

-- `lookup_solver`, and the fields that came back out of the registry.
/-- info: some (demo_low, trigger Lax13Proofs.Refine.Demo.DemoGoal, priority 50) -/
#guard_msgs in
#eval show CoreM Unit from do
  match ← lookup `demo_low with
  | none => IO.println "none"
  | some s => IO.println s!"some ({s.name}, trigger {s.trigger}, priority {s.prio})"

-- `byPriority` is a *total* order: equal priorities break on the name,
-- so the candidate list does not depend on import order (delta S3).
#guard (byPriority #[
    { (default : TaggedSolver) with name := `b, prio := 1 },
    { (default : TaggedSolver) with name := `a, prio := 1 },
    { (default : TaggedSolver) with name := `c, prio := 9 }]).map (·.name)
  == #[`c, `a, `b]

-- `keep`, both ways round. `demo_step` splits its goal and stops, so
-- `tagged_solver` — which requires the solver to *close* the goal —
-- must refuse, while `tagged_solver_step` hands the two halves back.
-- The refusal is `openGoalMsg` nested inside `greedyFailMsg`, and the
-- goals `demo_step` produced are rolled back before it is reported:
-- `tagged_solver_step` below starts from the unsplit goal.
/--
info: tagged_solver: the highest-priority solver for tag 'Lax13Proofs.Refine.Demo.DemoStep' failed; candidates in priority order: demo_step (priority 10); 'tagged_solver_full' would try the rest. The solver failed with: tagged_solver: solver demo_step (priority 10) ran on tag 'Lax13Proofs.Refine.Demo.DemoStep' but did not close the goal; use 'tagged_solver_step' to keep what it produced
-/
#guard_msgs in
example : Demo.DemoStep 3 := by
  tagged_solver_trace
  tagged_solver_step
  · omega
  · omega

-- …and a solver that does close its goal leaves nothing behind, so the
-- step form is a no-op difference there.
example : Demo.DemoGoal 0 := by tagged_solver_step

end Gate

end Lax13Proofs.Refine
