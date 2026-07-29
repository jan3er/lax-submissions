import Mathlib.Tactic

/-!
The shared rule-database attributes of the Autoref layer.

Design record `plans/word-ram/refinement-tower/design.md` §10 default 3:
"the `@[refine_vcg]`/`@[param]`/`@[sepref…]` attribute set is one shared
implementation parameterized by DB name (one meta module, not five)".
This is that module for P2. It declares attributes and nothing else — no
definition, no lemma — because of the substrate constraint P1 already
paid for once (`NREST/BackwardsReasoning.lean`, delta B7): Lean runs
`initialize` blocks at *import* time, so an attribute is not available
to the module that declares it. Every rule that wants a tag therefore
has to live downstream of this file, and the cheapest way to arrange
that is a file that declares the tags and stops.

The three databases, and what each is (ledger D1 — Isabelle's
`named_theorems` and its `Item_Net` indexing become Lean persistent
attributes and DiscrTree/label sets; the rule *format* is unchanged):

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

`relator_props` and `param` are *label* attributes (a rule set a tactic
enumerates), following the `register_label_attr refine_vcg` precedent of
`NREST/BackwardsReasoning.lean`; `refine_rel_defs` is a simp set,
because that is what the source uses it as.
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

end Lax13Proofs.Refine
