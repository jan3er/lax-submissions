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
   - 4b ✅ (statements + encodings; builds green): App. A stated from
     the fetched source (`references/dmmpt26/`, untracked). New proof
     modules: `SetSystems` (VPos/VNeg = merge relations, Hamming edges
     as posPairs; Lem 7 proved both halves; Cor 9 proved modulo HLW;
     vcDim restriction/zero helpers proved; Lem 8 + Lem 19 sorried),
     `Sampling` (Lem 12, generic relation form, denominator
     `150(ln|X|+1)` so |X| = 1 is fine), `Sparsification` (bundled
     structure, parts = tuple fibers, no partition objects;
     `sparsFormulas` R1 recursion; Lem 25/26 stated with explicit
     `stepLoss d x = 600(d+1)(log x + 2)²`), `TransductionCalculus`
     (image class + monos + `Transduces.trans` proved),
     `SparsGraphs` (fixed `sparsTransduction k`, class
     `sparsGraphs C k` = image ∩ K_{k+1,k+1}-free; weakly sparse /
     mon dep / NC + Lem 23' + Lem 24 proved),
     `Asymptotics` (polylog absorption, sorried).
     Key design finds: (i) R1 collapses to a *single* formula tuple
     per k — the merge sign is read off emptiness of the S-predicate,
     so Lem 23's transduction guesses nothing; (ii) A ∩ B ≠ ∅ breaks
     the k^k-count in Lem 24, so the machinery takes `Disjoint A B`
     and Lem 21' will split B = (B∖A) ∪ (B∩A), |B∩A| ≤ |A|; (iii) the
     only calculus fact needed anywhere is transitivity + monos —
     induced-subgraph closure is inside the image-class definition.
   - 4b' ✅ Lem 21' proved from [VC] + Lem 26 + Lem 24 + absorption
     (as planned: B split off A, |A| = 1 edge case via powerset,
     Lem-24 constant uniformized by summing over i ≤ d).
     Leaves discharged since: realizeIn_liftFormula (sumMap expansion
     + `realize_onFormula`); polylog absorption (`log_le_rpow_div`);
     Lem 26 from Lem 25 (downward induction, `DimLE 0 → Terminal`);
     Lem 19 (deletion process as downward induction on |X| with
     invariant `μ(X) ≥ m/2 + (m/2H(n))·H(|X|)`, `harmonic` from
     mathlib, drop identity `card_image_erase_add_card_vPos`);
     HLW Lem 8 (induction on ground set; v-edges counted by VNeg
     members; rest injects into edges of erase-v projection ⊕ edges
     of VNeg family — double-lift edges are VNeg edges); Cor-6-side
     counting of Lem 24 (reps per label tuple, neighborhood of a rep
     = its label set via A∩B = ∅, ≤ k^k reps per trace via piFinset,
     transport along `orderIsoOfFin` preimage). SetSystems and
     Asymptotics are sorry-free.
   - Lem 12 ✅ (simplified FOCS'24: powers-of-2 buckets, sample
     p = 1/2^(j+1); per-vertex success ≥ 1/16 via
     (1+1/(M−1))^M ≤ e² < 8; expectation as weighted sum over
     `X.powerset`, marginalization by `sum_nbij'` to `(X∖N).powerset`).
     Sampling, SetSystems, Asymptotics all sorry-free.
   - Lem 23 ✅ (`sparsGraphOn_mem_sparsGraphs`): the fixed R1 formulas
     realize the label graph on `A ∪ reps`; the two side colors define
     exactly that carrier. Biclique-freeness is a direct pigeonhole:
     a copied `K_{k+1,k+1}` would inject `Fin (k+1)` label choices into
     `Fin k` at a representative vertex.
   - `Transduces.trans` ✅: explicit syntactic composition with summed
     color blocks; second-stage colors are pulled back along the first
     embedding, atomic relations are substituted by the first
     interpretation, and every second-stage quantifier is relativized
     to the first-stage domain. The exact-range clauses prove the
     realization induction at quantifiers.
   - 4b'' remaining leaves (each a focused session; 2 sorries in 4b
     scope + Cor 6b which is 4c): Lem 25 (step; combinatorial half
     from Lem 19 + Cor 9 + Lem 7 + Lem 12, then the R1 definability
     discharge — semantics of `mergeFormula`); [VC].
   - 4c: the 6b chain (§3a), coarse-to-fine; densification last.

Guideline: first principles, weigh pros and cons carefully — flagship
standards. Rewrite this file as things crystalize.
