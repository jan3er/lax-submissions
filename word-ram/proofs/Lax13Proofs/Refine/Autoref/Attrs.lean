import Mathlib.Tactic

/-!
The shared rule-database attributes of the Autoref layer.

Design record `plans/word-ram/refinement-tower/design.md` §10 default 3:
"the `@[refine_vcg]`/`@[param]`/`@[sepref…]` attribute set is one shared
implementation parameterized by DB name (one meta module, not five)".
This is that module for P2, and after wave B2 it carries the phase's
*complete* attribute set. It declares attributes and nothing else — no
definition, no lemma — because of the substrate constraint P1 already
paid for once (`NREST/BackwardsReasoning.lean`, delta B7): Lean runs
`initialize` blocks at *import* time, so an attribute is not available
to the module that declares it. Every rule that wants a tag therefore
has to live downstream of this file, and the cheapest way to arrange
that is a file that declares the tags and stops.

The databases, and what each is (ledger D1 — Isabelle's
`named_theorems` and its `Item_Net` indexing become Lean persistent
attributes and DiscrTree/label sets; the rule *format* is unchanged).

Wave A (relators and parametricity):

* `relator_props` — the source's `named_theorems relator_props` of
  `Automatic_Refinement`'s `Relators.thy`: the structural facts about
  relators that the relator-side solvers consume (monotonicity,
  single-valuedness, …).
* `param` — the source's `[param]` rule database of
  `Parametricity/Param_Tool.thy`, the parametricity rules keyed on the
  head constant of the related term. **Registered here for wave B's
  use**: `Autoref/Param.lean` cannot both declare the attribute and tag
  its own rules with it, which is exactly the constraint above.
* `refine_rel_defs` — the source's `named_theorems refine_rel_defs`, a
  simp set collecting each relator's unfolding lemma
  (`fun_rel_def`, `prod_rel_def`, … in the source; the `mem_…_iff`
  membership lemmas of `Autoref/Relators.lean` here).

Wave B2 (the tag layer and the Autoref rule databases proper). These
seven are registered *now*, all at once, so that no later wave has to
come back to this file: the constraint above means every module that
wants to tag a rule must already be downstream of the declaration, and
the cheapest way to guarantee that for waves C and beyond is to declare
the whole set before any of it is populated. The names are fixed by the
source — they are what `Autoref_Tagging.thy`, `Autoref_Id_Ops.thy`,
`Autoref_Fix_Rel.thy` and every consumer in
`plans/word-ram/refinement-tower/p2-tutorial-extracts.md` §3–§4 write:

* `autoref_tag_defs` — the source's simp set of tag-unfolding lemmas
  (`PROTECT_def`, `ANNOT_def`, `OP_def`, `APP_def`), the set the source's
  rules discharge themselves against with `unfolding autoref_tag_defs`
  (tutorial extract §3, `autoref_list_eq`). Populated by
  `Autoref/Tagging.lean`, which is why this one is a *simp* set: that is
  what the source uses it as.
* `autoref_rules` — the main translation rule database
  (`(concrete, abstract) ∈ R` facts). Every worked example in the
  tutorial extract declares into it.
* `autoref_rules_raw` — the same database in un-preprocessed form
  (tutorial extract §4: `notes [autoref_rules_raw] = IdI[where …]`,
  the escape hatch when the rule's type must be pinned by hand).
* `autoref_itype` — interface-type declarations for constants
  (tutorial extract §4: `notes [autoref_itype] = itypeI[where 't=… and
  I=i_std]`), consumed by the operation-identification phase over
  `CONST_INTF`/`ID_OP`.
* `autoref_struct_expand` — structural-expansion rewrites, the
  `(=) = list_eq (=)` family of tutorial extract §3 that redirects an
  overloaded operator to a parametrisable one before rule lookup.
* `autoref_op_pat` — operation patterns, the
  `E``{v} ≡ op_succ$E$v` family of tutorial extract §2.1 that rewrites a
  raw term into tagged `OP`/`APP` form for identification.
* `autoref_tyrel` — type-relator overrides, the `ty_REL[where …]`
  mechanism of tutorial extract §2.5 by which a user pins the default
  relator for an abstract type.

All of these except `autoref_tag_defs` are *label* attributes (a rule set
a tactic enumerates), following the `register_label_attr refine_vcg`
precedent of `NREST/BackwardsReasoning.lean`.

**Registration only.** Nothing populates the wave-B2 databases here or
in wave B2 at all — wave C's rule files do. The tag *constants* those
rules are stated over land in `Autoref/Tagging.lean`, and the
side-condition solver registry that dispatches on them in
`Autoref/Solver.lean`.

## The one non-attribute database (wave B2)

`Autoref/Solver.lean` ports `Tagged_Solver.thy`, whose store is not a
theorem set but a record store — solvers with names, triggers,
priorities and tactics. A Lean persistent environment extension is what
that is, and it is subject to the *same* import-time constraint as an
attribute, for the same reason: `initialize` runs at import, so the
extension object cannot be evaluated in its own module, and a
`declare_solver` in `Solver.lean` itself would fail with
`cannot evaluate [init] declaration … in the same module`. So the
extension is declared here, where every declaration in this file already
lives for that reason, and `Autoref/Solver.lean` — downstream — holds
the port proper: the API, the dispatcher, the tactics, the
`declare_solver` command, and the fidelity ledger for all of it. The
record's field documentation is here because the record is; its
justification against the source's `type solver` is there.
-/

namespace Lax13Proofs.Refine

/-- The source's `named_theorems relator_props` (`Relators.thy`):
structural facts about relators — monotonicity, single-valuedness, and
the like — that the relator-side solvers enumerate. -/
register_label_attr relator_props

/-- The source's `[param]` rule database (`Param_Tool.thy`):
parametricity rules, keyed in the source by the head constant of the
related term. Declared here rather than in `Autoref/Param.lean` because
a Lean attribute is unavailable to its own defining module. -/
register_label_attr param

/-- The source's `named_theorems refine_rel_defs`: the simp set of
relator unfolding lemmas. -/
register_simp_attr refine_rel_defs

/-- The source's `autoref_tag_defs` (`Autoref_Tagging.thy`): the simp set
of tag-unfolding lemmas — `PROTECT_def`, `ANNOT_def`, `OP_def`,
`APP_def` — that the source's own rules discharge themselves against
with `unfolding autoref_tag_defs`. Populated by `Autoref/Tagging.lean`. -/
register_simp_attr autoref_tag_defs

/-- The source's `autoref_rules`: the main translation rule database of
`(concrete, abstract) ∈ R` facts. Populated by wave C. -/
register_label_attr autoref_rules

/-- The source's `autoref_rules_raw`: `autoref_rules` in
un-preprocessed form, the escape hatch used when a rule's type must be
pinned by hand. Populated by wave C. -/
register_label_attr autoref_rules_raw

/-- The source's `autoref_itype`: interface-type declarations for
constants, consumed by the operation-identification phase over
`CONST_INTF` / `ID_OP`. Populated by wave C. -/
register_label_attr autoref_itype

/-- The source's `autoref_struct_expand`: structural-expansion rewrites
redirecting an overloaded operator to a parametrisable one before rule
lookup. Populated by wave C. -/
register_label_attr autoref_struct_expand

/-- The source's `autoref_op_pat`: operation patterns rewriting a raw
term into tagged `OP` / `APP` form for identification. Populated by
wave C. -/
register_label_attr autoref_op_pat

/-- The source's `autoref_tyrel`: type-relator overrides, by which a
user pins the default relator for an abstract type. Populated by
wave C. -/
register_label_attr autoref_tyrel

/-! ### P4, wave B2: the Sepref front-phase databases

Five more, and here for the reason every database in this file is here:
Lean runs `initialize` at *import* time, so `Sepref/IdOp.lean` and
`Sepref/Monadify.lean` cannot both declare their attributes and tag
their own rules with them. The names are the source's, from
`thys/sepref/Sepref_Id_Op.thy` and `thys/sepref/Sepref_Monadify.thy` of
`isabelle_llvm_time` @ `42dd7f5`.

All five are `named_theorems_rev` in the source, not `named_theorems`.
The distinction is *order*: Isabelle's `named_theorems` prepends, so
`get` yields the most recently declared rule first, and Lammich's
`Named_Theorems_Rev` (`Refine_Imperative_HOL.Named_Theorems_Rev`)
appends, so `get` yields rules in declaration order — which is what the
Sepref phases want, because a later, more specific arity or pattern
equation must not shadow an earlier general one. Lean's
`register_label_attr` + `Lean.labelled` gives declaration order
(imported modules first, then the current module in declaration order),
which *is* the `named_theorems_rev` order; no reversal is applied
anywhere. Where a database is consumed as a **simp set** rather than as
an ordered rule list — which is how all five are consumed, following the
source's own `addsimps (Named_Theorems_Rev.get …)` — the order is
immaterial to the result and matters only for termination, and the
source's own `SP_cong`/`PR_CONST_cong` congruence discipline is what
guarantees that (`Sepref/Monadify.lean`).

* `id_rules` — the source's
  `named_theorems_rev id_rules "Operation identification rules"`:
  conceptual typings `c ::⇩i TYPE('T)`, keyed on `c`.
* `pat_rules` — its
  `named_theorems_rev pat_rules "Operation pattern rules"`: the
  backtrackable pattern rewrites applied before type inference.
* `def_pat_rules` — its `named_theorems_rev def_pat_rules "Definite
  operation pattern rules (not backtracked over)"`, which the source's
  `id_tac` runs from its own net, *before* `pat_rules`.
* `sepref_monadify_arity` — its `named_theorems_rev
  sepref_monadify_arity "Sepref.Monadify: Arity alignment equations"`:
  the eta-expansion equations of monadify step 1.
* `sepref_monadify_comb` — its `named_theorems_rev
  sepref_monadify_comb "Sepref.Monadify: Combinator equations"`: the
  `EVAL`-introducing equations of monadify step 2.
-/

/-- The source's `named_theorems_rev id_rules`
(`Sepref_Id_Op.thy`): conceptual typings `c ::ᵢ I`, consulted by the
`id_op` phase's leaf case. -/
register_label_attr id_rules

/-- The source's `named_theorems_rev pat_rules`
(`Sepref_Id_Op.thy`): operation pattern rules, rewriting surface
encodings into abstract operations before type inference. -/
register_label_attr pat_rules

/-- The source's `named_theorems_rev def_pat_rules`
(`Sepref_Id_Op.thy`): definite operation pattern rules, not backtracked
over, run before `pat_rules`. -/
register_label_attr def_pat_rules

/-- The source's `named_theorems_rev sepref_monadify_arity`
(`Sepref_Monadify.thy`): arity-alignment (eta-expansion) equations,
monadify step 1. -/
register_label_attr sepref_monadify_arity

/-- The source's `named_theorems_rev sepref_monadify_comb`
(`Sepref_Monadify.thy`): combinator equations introducing `EVAL` tags,
monadify step 2. -/
register_label_attr sepref_monadify_comb

section SolverRegistry

open Lean

/-- The source's
`type solver = thm list * string * string * (Proof.context -> tactic')`
of `Tagged_Solver.thy`. Declared here rather than in
`Autoref/Solver.lean` for the reason every declaration in this file is
here: its environment extension is an `initialize` value, unavailable to
its own module. The port's rationale, and the deltas S1–S6 the field
comments cite, are in `Autoref/Solver.lean`'s header. -/
structure TaggedSolver where
  /-- The solver's name, as written at its `declare_solver` — the
  source's `binding`. -/
  name : Name
  /-- The head constant of the goals this solver claims. The source
  keeps a list of *trigger theorems* here (delta S1). -/
  trigger : Name
  /-- Dispatch priority; higher runs first, ties break on `name`. The
  source keeps a relative position in a `Prio_List` (delta S3). -/
  prio : Nat
  /-- What the solver does, for the dispatcher's failure messages — the
  source's description string. -/
  descr : String
  /-- The tactic, as syntax. The source stores an ML closure
  (delta S4). -/
  tac : Syntax
  /-- The namespace in force where `tac` was declared (delta S4). -/
  ns : Name
  /-- The `open` declarations in force where `tac` was declared
  (delta S4). -/
  openDecls : List OpenDecl
deriving Inhabited

/-- The solver registry: the source's context-generic `Prio_List` store,
as a persistent environment extension (ledger D1). Entries survive into
`.olean`s, so a solver declared in one module dispatches in every module
downstream of it. Read and written through `Autoref/Solver.lean`'s
`TaggedSolver.all` / `TaggedSolver.add`. -/
initialize taggedSolverExt :
    SimplePersistentEnvExtension TaggedSolver (Array TaggedSolver) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (init := #[]) (fun acc es => acc ++ es)
  }

end SolverRegistry

end Lax13Proofs.Refine
