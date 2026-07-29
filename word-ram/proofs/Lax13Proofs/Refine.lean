import Lax13Proofs.Refine.Cost.ACost
import Lax13Proofs.Refine.NREST.Basic
import Lax13Proofs.Refine.NREST.Pw
import Lax13Proofs.Refine.NREST.Sanity
import Lax13Proofs.Refine.NREST.Rec
import Lax13Proofs.Refine.NREST.Combinators
import Lax13Proofs.Refine.NREST.DataRefinement
import Lax13Proofs.Refine.NREST.TimeRefinement
import Lax13Proofs.Refine.NREST.BackwardsReasoning

/-!
The refinement tower: a fidelity-first port of the Isabelle NREST/Sepref
stack onto the endorsed word RAM.

The campaign plan, the pinned sources, the component maps and the
deviation ledger live in `plans/word-ram/refinement-tower/design.md`;
the verbatim Isabelle definitions every module here is checked against
live in `plans/word-ram/refinement-tower/source-extracts.md`. Read the
design record first: it is what makes a departure from the source
citable, and each module's header records the departures that module
actually made.

This is P1's first two slices — the currency type, the NREST monad
core, and the recursion/loop combinators built on it:

* `Refine/Cost/ACost.lean` — `('a,'b) acost` (`Abstract_Cost.thy`),
  pointwise algebra and lattice, `cost n x`, and `ECost`.
* `Refine/NREST/Basic.lean` — the `nrest` datatype, its complete
  lattice, and `RETURNT` / `SPEC` / `consume` / `bindT` / `ASSERT`
  (`NREST.thy`).
* `Refine/NREST/Pw.lean` — `nofailT`, `inresT`, the pointwise
  principles, monotonicity, and the four monad laws at the source's own
  carriers.
* `Refine/NREST/Sanity.lean` — the executable gate (design record ledger
  D4): `#guard` spot checks and Plausible property checks of those laws
  at a finite carrier.
* `Refine/NREST/Rec.lean` — general recursion: the flat orderings,
  `mono2`, `RECT` / `RECT'` and their unfold and mono rules, the
  `refine_mono` seed lemmas, and the fuel approximants that make the
  fixed point executably checkable (`NREST.thy`, `RefineG_Domain.thy`,
  `Refine_Mono_Prover.thy`).
* `Refine/NREST/Combinators.lean` — `consumea`, `MIf` / `monadic_If`,
  `whileT` / `whileIET` / `monadic_WHILEIT`, and `FOREACH`
  (`NREST.thy`; `FOREACH` from AFP `NREST`'s `Refine_Foreach.thy`,
  which is where it exists at all).

and P1's second slice — the two refinement operators the tower composes:

* `Refine/NREST/DataRefinement.lean` — `conc_fun` / `⇓R` and `abs_fun`
  (`Data_Refinement.thy`), the `br` relation constructor, the bind and
  consume refinement rules, `nrest_rel`.
* `Refine/NREST/TimeRefinement.lean` — `timerefine` / `⇓C`,
  `timerefineA`, the `wfR`/`wfR'`/`wfR''` finite-support predicates, the
  exchange-rate composition `pp`, the identity rate `TId`
  (`Time_Refinement.thy`), and the `⇓R`/`⇓C` commutation of
  `NREST_Main.thy`.

Each of the two carries its own executable gate, in the `Sanity`
namespace of `Sanity.lean`.

and P1's third slice — backwards reasoning and the abstract VCG:

* `Refine/NREST/BackwardsReasoning.lean` — the resource type classes
  `nonneg` / `needname` / `drm` / `needname_zero`
  (`NREST_Type_Classes.thy`), the `gwp` predicate transformer with its
  `minus_cost` / `minus_potential` / `minus_p_m` layers, the bind rule,
  the `progress` side condition, the `[vcg_rules']` suite, the
  consequence rules, the well-founded loop rule and its `whileIET`
  vcg form, and a first `refine_vcg` attribute and tactic
  (`NREST_Backwards_Reasoning.thy`; `RECT_wf_induct` from `NREST.thy`,
  `lift_acost` from `Enat_Cost.thy`). Its header records the one
  refutation the port turned up: mathlib's truncated `Sub ℕ∞` does not
  satisfy the `needname` axiom `top - a = top`, so the source's own
  subtraction is declared here as `ResSub`.

P1's remaining item is the acceptance program of design record §10.4
(abstract masked depth-capped BFS against `bfs_spec`'s vocabulary).
-/
