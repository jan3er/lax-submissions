# Submission polish: structural fixes ahead of the one-axiom rule

Plan written 2026-07-27, from a survey of every concept package in this
repository. Companion plans live in the `lax` repo: `one-axiom-plan.md`
(the rule and its enforcement) and `website-plan.md` (the claim-page
rewrite that the rule enables).

**The survey's headline:** the one-axiom rule is already de facto practice
here — all 28 concept modules across Lax1, Lax2, Lax5, and Lax11 declare
exactly 0 or 1 axioms, and the design vocabulary ("theorem-concept",
"definition-concept", "the concept's obligation") assumes it. Nothing in
this plan is a migration to the rule. What the survey *did* find are three
structural habits the rule makes expensive later, all fixable now while
everything is a mutable draft:

1. **Definitions living inside theorem-concepts.** Reusable vocabulary
   (`WeaklySparse`, `wcol`, `GraphParam`, the instance encodings) sits in
   the module of the first claim that needed it. Once anything downstream
   depends on such a concept, the definition can never move: concept ids
   are permanent dependency targets and definitional identity is nominal —
   a later, textually identical copy elsewhere is a *different term*.
   Future statements about that notion would then have to import a
   theorem-concept just for its vocabulary, muddying what "imported by"
   means.
2. **Conjunctions of independently provable claims.** One observed case
   (Lax2). Each direction has its own literature proof and could be
   separately stated, proven, bountied, and assumed downstream; as one
   axiom the proof must deliver both at once and the network hides the
   structure.
3. **Near-duplicate vocabulary across theorem-concepts.** Two unrelated
   `EncodesInstance` defs in Lax11 (VertexCover's graph+k, Courcelle's
   graph+expr) — the placement pitfall showing up as duplication instead
   of hoisting.

## Preconditions

- **Check archive state first.** `lax pull-db` and confirm which of Lax1,
  Lax2, Lax5, Lax11 have content on the server and that all are still
  `draft`. Everything below renames Lean names and moves defs between
  modules, which changes statement texts and (where noted) def namespaces;
  that is only possible while the affected submission is a mutable draft
  and nothing *registered* depends on it. If anything has registered, its
  items below are dead — strike them, don't work around them.
- Re-run `lax build` and re-submit each touched draft when its items land;
  Lax2 depends on Lax1, so re-submit in id order.

## Lax2 (`twin-width-mixed-minor-number`) — the conjunction

`Lax2.FunctionalEquivalence` currently defines `GraphParam` and
`FunctionallyEquivalent` and states the equivalence as one axiom whose
type is an `∧` of two independently provable directions
(`Main.lean` proves both at once).

- **New definition-concept `Lax2/GraphParameters.lean`** (`type:
  definition`): `GraphParam` and `FunctionallyEquivalent`, with the
  annotation text about the uniform signature. `GraphParam` explicitly
  claims to be "the uniform signature shared by all graph parameters in
  this archive" — archive-wide vocabulary has no business inside one
  theorem's module.
- **Two new theorem-concepts**, one per direction, stated directly over
  `Lax1.TwinWidth.twinWidth` and `Lax2.MixedMinorNumber.mixedMinorNumber`
  (no `GraphParam` needed):
  - `Lax2/TwinWidthFromMixedMinorNumber.lean` —
    `∃ f, ∀ G, twinWidth G ≤ f (mixedMinorNumber G)`
  - `Lax2/MixedMinorNumberFromTwinWidth.lean` — the mirror bound.
- **Keep `Lax2.FunctionalEquivalence` as the headline theorem-concept**,
  its axiom id and statement unchanged (it is the submission's title
  claim), now importing `GraphParameters` instead of defining anything.
- **Proof package:** split `Main.lean` along the two directions; each
  direction becomes a proof concluding its concept. Add a small glue
  proof concluding the equivalence with the two directions as
  `assumptions`. The network then shows equivalence = dir₁ ∧ dir₂
  honestly, and each direction is independently citable.

## Lax5 (`monadic-dependence-neighborhood-complexity`) — execute D6's caveat

- **Move `WeaklySparse` from `WeaklySparseDependent.lean` to
  `GraphClasses.lean`.** The design record (design.md, D6) placed it in
  the theorem-concept with the explicit caveat "move it to concept 1 if we
  ever state more around it" — but that move is only possible *before*
  dependencies accrue, so do it now, unconditionally. The axiom
  `nowhereDense_of_weaklySparse_of_monadicallyDependent` keeps its id;
  the def's namespace changes
  (`Lax5.WeaklySparseDependent.WeaklySparse` →
  `Lax5.GraphClasses.WeaklySparse`), so the axiom's statement text and
  the proof package's references update with it.
- **New definition-concept `Lax5/WeakColoring.lean`** (`type:
  definition`): `wreach`, `wcol`, and `HasSubpolynomialWcol` move out of
  `NowhereDenseWcol.lean`, together with the wcol prose of its
  annotation. Weak coloring numbers are a central sparsity notion; more
  statements around them are a certainty, and today they can only be
  reached through a theorem-concept. `NowhereDenseWcol` keeps only its
  axiom (id unchanged) and the theorem-specific notes, importing the new
  concept. Update `Lax5Proofs/NowhereDenseWcol.lean` and
  `NowhereDenseNeighborhoods.lean` references.
- No action: `HasAlmostLinearNC` already lives in the definition-concept
  `NeighborhoodComplexity` and is shared by both theorem-concepts that
  conclude with it — this is the pattern the rest of the repo should
  match. `AdlerAdler`, `AlmostLinearNC`, `NowhereDenseNC` are def-free
  theorem-concepts already.

## Lax11 (`ram-linear-time`) — the encoding block and the name clash

- **New definition-concept `Lax11/InstanceEncoding.lean`** (or extend
  `CliqueExpr` — decide when writing it; a separate concept keeps
  `CliqueExpr` purely about the expression type): the expression-tree
  encoding block currently private to `Courcelle.lean` (`nodeCount`,
  `parent`, `opCode`, `vertexName`, `children`, `EncodesExprTree`,
  `EncodesExpr`, and Courcelle's `EncodesInstance`), importing
  `GraphEncoding` and `CliqueExpr`. Any future MSO/clique-width
  algorithmic claim needs exactly this vocabulary; today it is trapped in
  one theorem's module. `Courcelle.lean` keeps only its axiom and notes.
- **Resolve the `EncodesInstance` name clash.** VertexCover's
  `EncodesInstance` (graph + parameter k) and Courcelle's (graph + expr)
  are unrelated defs sharing a name in sibling namespaces. Rename to
  say what they encode (e.g. `EncodesParamInstance` /
  `EncodesModelCheckingInstance`) as they move — VertexCover's is small
  and claim-shaped; it may either stay in `VertexCover.lean` under the
  clearer name or join the new encoding concept.
- No action: `ConnectedComponents`' `label`/`ccLabels` define the object
  the claim is *about* — genuinely claim-local, stays. `Mso`,
  `GraphEncoding`, `Ram`, `RamComputes`, `CliqueExpr` are already clean
  definition-concepts.

## Lax1 (`twin-width-treewidth-separation`) — optional

Structurally clean (two definition-concepts, one def-free
theorem-concept; the `∃ … ∧ …` in `ExponentialSeparation` is one genuine
claim, not a splittable conjunction). One optional item: the axiom name
`twin_width_can_be_exponential_in_treewidth` is the sentence style that
D7 (design.md) later rejected for mathlib style. Renaming changes the
statement id and `Lax1Proofs/Main.lean`; do it only if touching Lax1
anyway, and before anything external assumes the statement.

## Styleguide additions (README.md §styleguide)

Codify what the fixes establish, so the next submission doesn't reopen
the holes:

- **One axiom per concept module**, zero for definition-concepts —
  matching the archive-side rule (`one-axiom-plan.md` in the lax repo);
  state it here first since this repo is the reference implementation.
- **Definition placement:** a theorem-concept states one axiom over
  imported vocabulary. A def may stay in a theorem-concept only when it
  is the claim-local object the statement is about (ConnectedComponents'
  `ccLabels`); any notion that could plausibly appear in a second
  statement goes in a definition-concept *now*, because it cannot move
  later. When in doubt, hoist.
- **Conjunctions:** never `∧` independently provable claims into one
  axiom — split into sibling theorem-concepts plus, if the conjunction
  itself is the headline, a glue proof assuming both. An `∃` whose body
  is a conjunction describing one witness (Lax1) is one claim and fine.

## Sequencing

1. Preconditions check (archive state of all four).
2. Lax5 and Lax11 items (independent of each other and of Lax1/Lax2).
3. Lax1 optional rename, then Lax2 (its concepts import Lax1's draft).
4. README styleguide additions.
5. Re-submit touched drafts; verify on the site that statement ids,
   proof conclusions, and the proven set are unchanged where promised
   (only namespaces of moved defs may differ).
