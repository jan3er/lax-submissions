# Flagship: almost linear neighborhood complexity of monadically dependent classes

Target: Theorem 2 of <https://arxiv.org/abs/2607.10941> (Dreier, Mählmann,
McCarty, Pilipczuk, Toruńczyk): for every monadically dependent class *C*,
every G ∈ C and A ⊆ V(G) satisfy |{N(v) ∩ A : v ∈ V(G)}| ≤ |A|^(1+o(1)).

Scope assumption (confirm): Theorem 2 only — the merge-width results
(Theorems 4, 5) are out of scope.

## Formal shape of the headline theorem

The o(1) unfolds to: for every ε > 0 there is c such that for all G ∈ C and
A ⊆ V(G), the number of neighborhood traces on A is at most c · |A|^(1+ε)
(real `rpow` on the cast). A graph class is a collection of finite graphs;
candidate encoding `∀ n, SimpleGraph (Fin n) → Prop` or
`Set (Σ n, SimpleGraph (Fin n))` — to be settled in statement design.

## Pipeline map (what the proof needs, and where each bit lives)

Endorsement surface (concepts):

1. FO logic on colored graphs / transductions — mathlib has
   `FirstOrder.Language.graph`, `SimpleGraph.structure`, and full formula
   syntax/semantics; transductions (color + interpret φ(x,y) + take induced
   subgraph, up to iso) must be built on top. **Highest-risk, most reusable
   concept.**
2. Monadic dependence — "C does not transduce the class of all graphs"
   (paper's definition). OPEN DECISION: transduction-based (faithful,
   reusable, needs 1) vs. a purely combinatorial equivalent
   (flip-breakability / forbidden patterns, DMT STOC'24) which avoids FO
   entirely but is not the literature's primary definition.
3. Neighborhood complexity — the trace-count function; trivial definition.
4. Nowhere dense (shallow minors) — needed only to *state* the two imported
   sparsity ingredients below.
5. Ingredient theorem: monadically dependent + weakly sparse (K_{t,t}-free)
   ⇒ nowhere dense (paper's Corollary 6; check the paper's citation for the
   intended source/proof).
6. Ingredient theorem: nowhere dense classes have neighborhood complexity
   |A|^(1+ε) (sparsity2 notes: Ch. 2 generalized coloring numbers +
   Tutorial 6 / Ch. 4; original Eickmeyer et al.).
7. Headline theorem concept.

Proof-package-only machinery (invisible to reviewers, can be ugly):

- VC dimension + Sauer–Shelah: **already in pinned mathlib**
  (`Finset.vcDim`, `Finset.card_le_card_shatterer`,
  `Finset.card_shatterer_le_sum_vcDim`). No concept needed.
- Bounded VC dimension of neighborhood set systems in monadically
  dependent classes (unbounded VC ⇒ transduce all graphs; needs real FO
  reasoning against definition 2).
- Haussler's packing lemma (Hamming graph of a VC-d family has ≤ d|F|
  edges) — not in mathlib; pick the most formalizable proof in step 1.
- The paper's iterative decomposition (Section 2): bipartite reduction,
  twin-free normalization, Hamming-graph extraction, VC-dim-decreasing
  recursion, finishing via ingredients 5+6.

## Decisions (settled with Jan, 2026-07-24)

- A. Monadic dependence is defined the standard way, via FO logic and
  transductions. Use mathlib's ModelTheory if it supports what we need;
  if not, formalize FO from the ground up — either way this route.
- B. One big submission for now; split later if needed.
- C. Scope is Theorem 2 only; merge-width is out of scope.
- D. Corollary 6: prove 6b (nowhere dense ⇒ almost linear NC, radius 1,
  via the sparsity2 chain in `pipeline.md` §3a); state 6a (weakly sparse
  + mon dep ⇒ nowhere dense) as a concept with its proof obligation left
  open. Nowhere dense joins the concept surface.

## Plan

0. ✅ Feedback on plan (this revision).
1. ✅ Source survey: `pipeline.md` (paper App. A in full; per-lemma
   sources + formalization notes; restructurings R1–R3; the complete
   radius-1 Corollary-6b chain in §3a). Still open to revision as
   statement design surfaces issues.
2. ✅ Statement design: `design.md` rev 3, frozen with Jan 2026-07-24.
   10 concepts (transductions on arbitrary relational structures, graphs
   as the special case; 2 open obligations: Cor 6a + Adler–Adler);
   headline module `AlmostLinearNC`, shared predicate `HasAlmostLinearNC`.
3. ✅ Concept package written and green: **Lax5** in
   `monadic-dependence-neighborhood-complexity/` (10 modules,
   `lax build` OK; manifest + abstract filled). Deltas from `design.md`
   are recorded at its end. Pending Jan's read of the actual Lean files.
4. Proof package. Use `sorry`-stubs to get an end-to-end skeleton of the
   Section-2 argument compiling before filling in; big ingredients last.
   - 4a ✅ Top level compiles (3 sorries): `Lemma21.lean` states Lem 21
     in semi-induced form (on the class itself; the bipartite encoding
     is pushed below this interface) + ingredient [VC] against
     `Finset.vcDim`; `Theorem2.lean` derives the headline conclusion
     theorem from Lem 21' via trace representatives — glue fully
     proved; `Corollary6.lean` composes Cor 6 from the 6a/6b concept
     axioms (proved); `Corollary6b.lean` is the stubbed 6b conclusion.
   - 4b next: pull DMMPT26 App. A and state the set-system layer
     (Lem 7/8/19, Lem 12) and sparsification machinery (Lem 23–26)
     faithfully; design the bipartite-class + definable-family
     encodings (R1) under Lem 21'.
   - 4c: the 6b chain (§3a), coarse-to-fine; densification last.

Guideline: first principles, weigh pros and cons carefully — flagship
standards. Rewrite this file as things crystalize.
