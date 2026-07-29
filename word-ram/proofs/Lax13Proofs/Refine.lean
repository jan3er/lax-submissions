import Lax13Proofs.Refine.Cost.ACost
import Lax13Proofs.Refine.NREST.Basic
import Lax13Proofs.Refine.NREST.Pw
import Lax13Proofs.Refine.NREST.Sanity
import Lax13Proofs.Refine.NREST.Rec
import Lax13Proofs.Refine.NREST.Combinators

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

Still to come in P1, per design record §3: `DataRefinement`,
`TimeRefinement`, `BackwardsReasoning`.
-/
