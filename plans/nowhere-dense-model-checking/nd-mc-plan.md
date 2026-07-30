# Nowhere dense model checking plan (rev 4 — P0 gate cleared, 2026-07-28)

Rev 4 (2026-07-28): **Jan read the design note and approved; the P0
gate is cleared and P1 starts.** The three deltas proposed at the end
of `nd-mc-design.md` fold in: (1) **D8 tightened** — the capped
W-distance matrix and its precomputed formula-variant family are
dropped; capped distance profiles as colors on *all* vertices (batch
included) subsume them, and the variant family is demoted to a
fallback inside R2. (2) **D4 sharpened** — flat radius schedule with
sharp cap ρ* = ρ⁻(0,q), table locality radius ρ⁻(1,q−1), game
constants per the design note's (d) table (the notes' Lem 4.2 `2s+1`
→ `2s+2` slip recorded there). (3) **R1 renamed to its kernel** — the
augmentation density theorem (in-degree bound for transitive-fraternal
augmentations, NO05), sitting in P6 with a 3–5 session budget,
patterned on Lax12's `Densification`; cover *existence* (D10) is
dischargeable from Lax12 wcol alone, so P3 carries no part of R1. No
change to the concept surface, C0, the gates, or the phase order; the
D8/D9/D4/R1 texts below stand as rev 2/3 wrote them, read through
these deltas — the design note is the precise statement of record.

Rev 3 (Jan, in session — wrap-up; **the plan is accepted, execution
starts next session at P0**): two changes. First, the RAM half is
cross-campaign gated: **P5–P7 do not start until the IMP+ toolkit
campaign (`plans/word-ram/imp-toolkit-plan.md`) is closed** — its
remaining P4–P7 (library, pilot retrofit, remaining retrofits, pins)
are the machinery and the pin discipline this campaign's programs
stand on. The math core P0–P4 is not gated and proceeds immediately;
the two campaigns meet at the D12 gate, and if the toolkit closes
first, the gate never binds. Second, the open questions are closed by
their recommended defaults so nothing blocks the start: Q1 = claim
the reserved init slot **Lax3**, folder
`nowhere-dense-model-checking`; Q2 = the real-ε side-condition bound;
Q3 = the colored-graph surface; Q4 = the four citable theorems of
D11. All four are folded into the decision record below and remain
revisable until the P1 statement freeze, where Jan reviews the actual
Lean statements — that gate, not this rev, is the surface's point of
no return.

Rev 2 (Jan, in session): **the splitter isolates instead of removes.**
Splitter's move deletes the incident edges of its batch W and keeps
the vertices; the game is won when the arena is edgeless. Vertices
never disappear, which deletes the two worst objects of rev 1 in one
stroke: the substitution readout (no virtual vertices — a tuple may
sit on W and the same rewrite covers it) and the avoid-W side
conditions of the removal translation. The per-level translation
becomes one exact, quantifier-free rewrite of adjacency and distance
atoms through recorded colors (W-membership, old-neighbor marks,
capped distance profiles, with the capped W-distance matrix selecting
among finitely many precomputed formula variants); the recursion's
base case becomes "arena edgeless: evaluate by color lookup"; and on
the RAM the graph is materialized once — every arena is a vertex mask
+ isolation bits + profile arrays, undone by the toolkit's Trail.
D1, D8–D11, L2–L4, the step budgets and risk R2 are rewritten below;
Q5 is resolved (the isolation game is the surfaced concept). What
rev 2 does *not* change: locality is still applied at every arena —
the profile disjunct of a rewritten guard is not a distance guard in
the new metric, so per-level re-localization stays, and with it the
mutual typeTables/sentenceEval shape.

Rev 1 (2026-07-28): initial plan.

Goal: **first-order model checking is fixed-parameter tractable on
nowhere dense graph classes** (Grohe–Kreutzer–Siebertz), on the Lax13
word RAM, in time f(φ, ε, C) · n^(1+ε) for every ε > 0.

The route is **not** the original GKS proof. Jan's warning, confirmed
by the sources: the rank-preserving locality arguments of the original
GKS submission are both ugly and broken — Dreier–Toruńczyk
(arXiv 2606.23180, "A Rank-Preserving Locality Theorem") record fixing
an error of exactly this kind in the merge-width pipeline (spotted by
Mählmann), and Grohe–Schweikardt (arXiv 2606.11993) independently
published a repair of theirs, noting the game-based approach "is more
prone to errors … since tracing invariants for games turns out to be
often subtle". We take the 2606.23180 locality theorem as the logic
engine: its proof is a **syntactic rewriting** — five lemmas, no EF
games, no types, effective by construction — which is the most
formalization-friendly shape a locality theorem has ever had. Around
it we rebuild the GKS algorithm assembly (splitter game + sparse
neighborhood covers), with two structural simplifications the new
locality theorem buys:

1. **GKS §5 disappears.** Their scatter sentences need the distance-r
   independent set problem solved separately (their Theorem 5.1, via
   quasi-wideness). The 2606.23180 scatter sentences only ask for the
   size of *one predetermined inclusion-wise maximal* r-scattered set,
   computable by a greedy pass. The whole distance-r independence
   subroutine and its UQW machinery drop out of the algorithm.
2. **GKS §7 is replaced wholesale.** No rank-preserving Gaifman normal
   form, no colored-structure expansions: the rewriting is equivalent
   on the *unmodified* structure, works for any number of free
   variables, and is a Lean function with a correctness lemma —
   "effectively computable" comes for free.

Monadically stable machinery (Flipper game, Lax5's EF/LocalTypes core)
is **not** on the critical path: the syntactic proof needs no EF games,
and for a monotone target class the splitter game strictly dominates
flips. It stays in the fallback column (references/maehlmann-thesis
Ch. 11–12 for cover-based recursion bookkeeping, if GKS §8 fights us).

## Sources

| ref | what we take |
|-----|--------------|
| arXiv 2606.23180 (Dreier–Toruńczyk, fetched, → `references/rploc`) | the whole logic engine: distFO, distance rank, horizon functions, scatter sentences, Thm 1 (locality), Cor 7 (normal form), Lem 5/8/9/11/12 |
| GKS, JACM 2017 (arXiv 1311.3899, **to fetch** in P0) | §6 sparse neighborhood covers (existence + computation), §8 algorithm assembly (to be rebuilt on the new engine), §4 splitter game bounds as cross-check |
| sparsity notes ed2019 ch. 4 §4 (`references/sparsity-lectures`) | (ℓ,m,r)-splitter game Def 4.1; Lem 4.2 "nowhere dense ⇒ Splitter wins", proved from UQW with an explicit path-maintenance strategy — the same notes Lax12 formalizes, same definitional universe. We adapt both to the isolation variant (rev 2): the strategy isolates the same path systems it used to delete |
| arXiv 2502.18065 v1→v2 (merge-width MC, **to fetch** in P0) | how the locality theorem is consumed downstream; formula-table conventions |
| Lax12, Lax13, Lax11 (this repo) | see reuse survey |

## Reuse survey

Cross-submission reuse is by concept-package `require` (spec: pinned
git+rev+subDir; draft deps warn, registration later needs registered
deps). Nothing is copied.

- **Lax12** (sparsity-lectures) — the combinatorial engine, all four
  already endorsed and proved:
  - `NowhereDense` (shallow-minor form) — the headline hypothesis,
    verbatim.
  - `uniformlyQuasiWide_of_nowhereDense` — feeds the splitter-game win
    (notes Lem 4.2 derives the strategy from exactly this statement).
  - `hasSubpolynomialWcol_of_nowhereDense` — cover degree n^ε; its
    formalization notes already say the subgraph-uniform form is "what
    downstream localization arguments consume". This campaign is that
    downstream.
  - `hasSubpolynomialDensity_of_nowhereDense` — edge bounds for BFS
    cost accounting (arenas are subgraphs of members).
  - `wcol`/`wreach`/orderings (`Equiv.Perm (Fin n)`, walk-based) — the
    cover construction speaks this language directly.
- **Lax13** (word-ram) — `Program`, `ComputesInTime`, the compiler and
  reasoning kit, and the IMP+ toolkit (frame rule, `Spec`, `run_vcg`,
  `Lib` incl. stack/trail/queue — the queue is BFS's core structure)
  for every program phase.
- **Lax11** (ram-linear-time) — `GraphEncoding` (CSR) reused as the
  input format; `Mso.lean` as the house pattern for logic syntax
  (Fin-indexed variables, snoc-levels, total `Sat`); the Courcelle
  campaign as the template for statement discipline and phasing.
- **Lax5** — *not* a dependency. Its EF/LocalTypes/BallSwap core was
  built for Adler–Adler; the syntactic route never plays a game. At
  most its walk-distance lemma patterns get imitated proofs-side.

## The statement (target concept, C0)

House style of Lax11's Courcelle: one program and one constant after
the class data, the sentence and ε; before the graph and the word
length; inputs restricted to encodings that fit.

```lean
axiom exists_almostLinearTime_program_modelChecking :
    ∀ (C : GraphClass), NowhereDense C →
    ∀ (φ : FO 0) (ε : ℝ), 0 < ε →
      ∃ (p : Program) (c : ℕ) (T : List ℕ → ℕ),
        (∀ x, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
          ComputesInTime w p
            {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w}
            (fun _ => if Sat G Fin.elim0 φ then [1] else [0])
            T
```

- `FO 0`: plain first-order sentences on graphs (adjacency, equality;
  Mso.lean pattern minus set variables). The headline quantifies over
  *ordinary* FO; distFO is engine-room.
- Hypothesis is `Lax12.NowhereDense C` verbatim — the endorsed
  definition, not a re-statement.
- Time bound: `n^(1+ε)` has no elementary ℕ spelling, so the bound
  function is existential with a real-valued side condition, the same
  `(m : ℝ) ^ ε` idiom as Lax12's `HasSubpolynomialWcol`. Adopted at
  rev 3 over the ℕ-only variant
  `∀ j, ∃ c T, ∀ x, T x ^ j ≤ c * (x.length + 1) ^ (j+1)`.
- Working lemma behind it (proofs-side): the per-graph promise form —
  ∀ t : ℕ → ℕ, φ, ε, ∃ p c T, ∀ G with
  `∀ r, ¬ HasShallowMinor G r (⊤ : SimpleGraph (Fin (t r)))` — from
  which the class form follows by choice. The program depends on
  finitely many values of t (radii ≤ a computable horizon of φ, ε).
- Input is the graph alone (CSR). Unlike Courcelle's k-expression,
  *nothing* auxiliary is input: covers, orderings, splitter moves are
  all computed. That is the content of the theorem and the main new
  algorithmic weight.

## Decision record

- **D1 (route).** Logic engine = 2606.23180 verbatim; assembly = GKS
  §8 rebuilt on it; splitter game in the **isolation variant** (rev 2)
  of the (ℓ,m,r) batch form of notes ed2019 Def 4.1 — splitter's batch
  keeps its vertices and loses its incident edges, the win condition
  is an edgeless arena — with the UQW-based win proof (Lem 4.2,
  adapted) on top of Lax12's `uniformlyQuasiWide_of_nowhereDense`.
  GKS §5 eliminated by greedy scatter choice; GKS §7 eliminated by
  the locality theorem; GKS's vertex removal eliminated by isolation.
- **D2 (one submission).** Single new submission — folder
  `nowhere-dense-model-checking`, id **Lax3**, the first reserved init
  slot (rev 3; Lax4 stays free, the natural home for a future
  merge-width submission) — requiring the Lax12, Lax13,
  Lax11 concept packages. The locality theorem is a citable concept
  *inside* it; a future merge-width submission requires this concept
  package. Registration can only happen after Lax11/12/13 register —
  acceptable, drafts are replaceable meanwhile.
- **D3 (logic lives on colored graphs).** distFO is formalized over
  finite L-colored graphs (`SimpleGraph (Fin n)` + `Fin L → Fin n →
  Prop`), not general relational signatures. The Gaifman graph of a
  colored graph is the graph itself, killing a whole layer. The
  concept's formalization notes state the specialization honestly
  (2606.23180 speaks of finite relational signatures; colored graphs
  are the full strength consumed by model checking on graph classes,
  the same way Lax11's Mso.lean pins MSO₁ and defers MSO₂). Unary
  distance atoms are kept — they cost one easy base case and keep the
  concept faithful. Finite structures only; the paper's ∞ scatter
  value degenerates. (Adopted at rev 3.)
- **D4 (horizon functions).** Concepts state the theorem for the
  paper's concrete pair ρ⁻ = 9^((k+q+1)q), ρ⁺ = 9^((k+q)(q+1));
  proofs work against an abstract `Horizon` structure bundling the two
  inequalities (eq. 1) — exactly the properties the paper's proofs
  use, which the paper itself itemizes.
- **D5 (rank as predicate).** Syntax `DistFO L k` type-indexed by free
  variables (house pattern), plus a predicate `DRank k' q φ` mirroring
  the paper's "distance rank (k,q)" (k' ≥ type index). The paper's
  Obs. 4/6 become monotonicity lemmas of the predicate; no reindexing.
  The separation lemma tracks variable *sets* by a `UsesOnly`
  predicate over `Fin k`, not by re-typing — splits without
  substitution.
- **D6 (scatter choice as parameter).** `ScatterChoice` = a function
  from (colored graph, radius, vertex set) to ℕ together with the
  property "size of some inclusion-wise maximal r-scattered subset".
  The locality theorem is stated for every such choice (that is the
  paper's "fix arbitrarily and once and for all"). Two instances:
  `greedyChoice` in Fin-order (computable — the one the machine runs
  and the one the recursion's correctness invariant carries at every
  arena) and `maxChoice` (yields Cor 7, the Gaifman-style normal
  form).
- **D7 (rewriting as functions).** Every "effectively computable" in
  the paper becomes a Lean function on syntax returning formula lists,
  with a separate soundness lemma. No finiteness-of-rank-q-formulas
  argument anywhere — formula *lists*, driven by the input sentence,
  replace GKS's "finitely many types" bookkeeping.
- **D8 (algorithm architecture).** All formula-level computation
  happens at program-construction time in Lean; the RAM program
  manipulates only the graph, color arrays, and truth tables. This
  works because the pipeline stays inside the **binary fragment**
  (no unary distance atoms): input FO has none, and the locality
  rewriting and the isolation rewrite introduce none — a closure
  lemma proves it. Rewritten formulas reference fresh color *slots*
  whose graph-dependent *interpretation* (W-membership, old-neighbor
  marks, capped distance profiles to the isolated batch) is computed
  at runtime; the only other graph-dependent datum is the capped
  W-distance matrix, ranging over a bounded set that indexes a finite
  family of precomputed formula variants — the program measures the
  matrix and selects the variant.
- **D9 (recursion shape).** Mutual recursion descending the isolation
  splitter game tree, on colored arenas that all share the original
  vertex numbering: `typeTables` (which of the finitely many
  single-variable local formulas hold at each vertex) and
  `sentenceEval` (truth of a sentence list). At each arena: locality
  theorem → scatter sentences over local β's + trivial local
  sentences; scatter evaluated by the Fin-order greedy over β-tables;
  β-tables by sparse cover, per cluster the splitter batch W (≤ m
  vertices, strategy from notes Lem 4.2), then the **isolation
  rewrite**: W's incident edges are deleted and the atoms translated
  exactly — adjacency through W-membership and old-neighbor colors,
  distance atoms through capped distance profiles, the capped
  W-distance matrix selecting the formula variant (D8). The rewrite
  is uniform in the tuple — vertices of W included, no case split,
  no readout — and preserves drank and radii. Its profile disjuncts
  are not distance guards in the new metric, so the next level's
  locality application re-localizes them; isolated vertices fall out
  of subsequent covers and evaluate by lookup. The game bound ℓ ends
  every branch at an edgeless arena, where every formula evaluates by
  color-table lookup. This is the GKS §8 role, re-derived; P0 checks
  it against their text before anything freezes.
- **D10 (cover layer).** Sparse neighborhood covers as their own
  def-concept (radius r, spread 2r, degree) + theorem-concept
  "existence with degree ≤ wcol_{2r}" (ordering-based construction) —
  composing with Lax12's wcol theorem to degree n^ε. Arenas are
  subgraphs of members in the full sense — vertex subsets *and* edge
  deletions — which is precisely the `⊑`-uniformity Lax12's wcol and
  density theorems already carry. The ordering/cover *computation* on
  the RAM follows GKS §6 (P0 pins the exact subroutine; see R1).
- **D11 (concept surface).** Definitions: `FO`, colored graphs +
  walk-distance API, `DistFO` + `Sat` + `DRank` + horizon, scatter
  choice + scatter sentences, splitter game, neighborhood covers.
  Citable theorems: **locality theorem** (Thm 1 of 2606.23180, with
  Cor 7 as companion), **splitter-game win** (isolation form; notes
  Lem 4.2 / GKS Thm 4.2), **sparse cover existence** (GKS §6),
  **headline C0**. Four independently endorsable claims; obligations
  parallelize across night campaigns. Internals (separation lemma,
  isolation rewrite, evaluator) stay proofs-side.
- **D12 (milestone gate).** Hard review gate with Jan after P4 (math
  core complete, before RAM work): statements frozen, feasibility of
  the RAM half re-judged with measured elaboration costs in hand.

## Proof architecture (lemma DAG)

Layer L0 — definitions (concepts): as in D11.

Layer L1 — locality engine (2606.23180, proofs-side unless noted):
1. `semLocal` — local + DRank(k,q) ⇒ semantically ρ⁻(k,q)-local
   (Lem 5; induction with the telescoping bound; needs the induced-
   subgraph relativization API from L0).
2. `separate` — the separation lemma (Lem 8): function + soundness;
   structural induction, three-way case split of the local quantifier,
   triangle-inequality arguments on walk distances.
3. `clusters` — Vitali-style grouping (Lem 9) + cluster partition with
   distance-test determinacy (Cor 10). Pure finite combinatorics.
4. `scatterCore` — maximal-scattered-set exchange argument (Lem 11).
5. `farQuant` — far quantification (Lem 12): assembles 3+4 into the
   boolean combination; the finickiest formula-building (case
   disjunction over (I, m, R) configurations guarded by distance
   atoms).
6. `locality` — Thm 1 by structural induction over 2+5; `normalForm`
   — Cor 7 via `maxChoice`. **Concept axiom discharged here.**

Layer L2 — sparse combinatorics:
7. `SplitterGame` def (isolation form: splitter's batch keeps its
   vertices and loses its incident edges; win = edgeless arena;
   (ℓ,m,r) batch parameters); win monotone under `⊑`-subarenas
   (vertex subsets and edge deletions — one lemma, both moves only
   help the splitter).
8. `splitterWins_of_nowhereDense` — from Lax12 UQW, notes Lem 4.2
   adapted to isolation: ℓ = N_r(2s_r+1), m = ℓ(r+1); the
   path-maintenance strategy isolates the maintained path systems,
   cutting the same connections deletion did, and the lingering
   isolated vertices sit outside every later ball. Strategy is an
   explicit function (BFS paths to prior connector vertices) — the
   same object the RAM later implements. **Concept.** (The removal
   form and the round-slack equivalence between the two games stay
   proofs-side, only if a source cross-check wants them.)
9. `NeighborhoodCover` def; `cover_of_wcol` — clusters from
   weak-reachability sets of an ordering, degree ≤ wcol_{2r}, spread
   2r; + Lax12 wcol ⇒ degree ≤ c·n^ε. **Concept.**

Layer L3 — abstract algorithm (proofs-side):
10. `isolateBatch` — the isolation rewrite: truth over arena A of a
    binary-fragment formula at **any** tuple equals truth, over A
    with W's incident edges deleted, of the translated formula —
    given the recorded colors (W-membership, old-neighbor marks,
    capped distance profiles) and the formula variant selected by
    the capped W-distance matrix. Drank and radii preserved; bound
    and free variables uniformly; no avoid-W hypotheses, no virtual
    vertices. One lemma where rev 1 had two.
11. `evaluator` — the D9 mutual recursion, by strong induction on
    game depth; correctness: at every arena it computes exactly
    `Sat`-truth (greedy scatter choice carried uniformly). Base:
    edgeless arenas evaluate by color-table lookup.
12. `reduction` — FO qr q ↪ distFO drank (0,q); top-level assembly:
    math-core checkpoint theorem "the evaluator decides φ on every
    graph satisfying the promise" (no time bound — internal, the P4
    exit criterion).

Layer L4 — RAM realization (Lax13 toolkit):
14. Primitives: truncated BFS over the masked CSR (skips isolation
    bits; queue + visited-trail; cost = edges touched),
    distance-profile arrays (m BFS runs per cluster), vertex masks
    for arenas. The graph is materialized **once**; every arena is
    masks + profiles, wound back by Trail on return — no CSR
    re-extraction, no vertex renumbering.
15. Ordering + cover program (GKS §6; R1) — on the masked view.
16. Recursion driver: bounded-depth (ℓ unrolled or toolkit stack),
    per-arena: cover pass, per-cluster splitter batch (BFS), profile
    pass, matrix-measured variant select, table cascade; greedy
    scatter pass; boolean combination.
17. Cost accounting: recursion tree × per-level n^(1+ε) via Lax12
    density + cover degree; one shared "cost algebra" module for the
    c·m^(1+ε) sums (patterns from Lax12/Lax5 asymptotics), then C0.

## Steps

- [x] **P0 — sources and design notes** (DONE 2026-07-28 @ 6e87f84;
  gate cleared same day, deltas folded at rev 4).
  Fetch GKS 1311.3899 and merge-width 2502.18065 sources into
  `references/` (`gks`, `mw`; 2606.23180 → `references/rploc`, README
  with fetch date + license each). Write `nd-mc-design.md` here
  settling, against the fetched texts: (a) the exact isolation
  rewrite statement — profile colors, matrix-indexed variants, the
  uniform-tuple claim — cross-checked against how GKS §8 reads types
  at removed vertices (our rewrite must recover everything theirs
  does); (b) the cover-computation subroutine of GKS §6,
  as pseudocode with its cost argument; (c) the binary-fragment
  closure claim across all rewriting stages; (d) the radius schedule
  (expected constant ρ* = ρ⁻(1,q) across levels — verify no growth);
  (e) the formula-table size functions (symbolic only — never
  evaluated on concrete φ). **Gate: Jan reads the design note.**
- [ ] **P1 — scaffold + L0 concepts** (2–3 sessions). Claim the Lax3
  init slot (D2), lakefile requires (Lax12/Lax13/Lax11 pinned),
  worktree-seed wiring. All L0 concept files with house-style
  frontmatter + formalization notes; C0 and the three theorem
  concepts stated as axioms; walk-distance API module proofs-side.
  **Gate: Jan endorse-reviews the surface; statements freeze.**
- [x] **P2 — locality engine** — done 2026-07-28, 3 sessions.
  Sessions 1–2 landed semLocal/clusters/scatterCore/syntax lemmas and
  forced one surface revision (guard-set `exL`, endorsed via
  `exl-guard-decision.md`; the whole-context guard made the two
  axioms unprovable). Session 3: `separate` (2-way guard-side split,
  statement gained `1 ≤ a`, `1 ≤ b`), `farQuant`, BC-algebra +
  `sat_scatterFml`, assembly. Both concept axioms discharged
  (`Lax3Proofs.Assembly.locality`/`normalForm`, assumptions: []);
  acceptance met: zero sorry, no statement drift beyond the recorded
  revision.
- [x] **P3 — splitter + covers** — done 2026-07-28, 1 session
  (three parallel Opus tracks). L2 items 7–9 as designed:
  `SplitterMono` (win antitone under `≤`-subarenas — one lemma covers
  both moves since vertex restriction is `deleteVerts` of the
  complement — plus budget/batch monotonicity), `SplitterWin`
  (discharge against Lax12 UQW only; strategy surfaced proofs-side as
  functions `pathSet`/`genSet`/`batch`/`nextArena` with `Reached` and
  the reusable `splitterWins_of_reached` — the objects L4's program
  correctness consumes; `2s+1 → 2s+2` slip fixed as recorded),
  `CoverConstruction` (wreach fibers of an `Nat.sInf_mem`-attained
  ordering; kernel-only). `SplitterBasics` holds the `Iff.rfl` clause
  lemmas of `SplitterWins`/`deleteVerts` (namespace-audit
  discipline). Acceptance met: full `lax build` green, audit clean,
  zero sorry, no statement drift.
- [x] **P4 — abstract evaluator** — done 2026-07-28, 1 session (three
  parallel + one serialized Opus track). L3 items 10–12 with three
  as-built deltas over design §(a), all strengthenings: (1) `iso` is
  **total on DistFO** — cumulative profile colors plus a per-color
  cumulative distance family absorb the unary atom, so the
  binary-fragment closure obligation of D8/(c) is gone; (2) the §(a)
  guard translation had a genuine rank gap (ρ⁺(k+1,q) > ρ⁻(k+1,q)) —
  fixed by the two-case `exL` translation (guard kept as `exL` in the
  new metric ∨ color-guarded `exU` for near-batch witnesses; colors
  are rank-free, so drank is preserved exactly); (3) the sentence
  phase of D9 collapses — scatter atoms evaluate inline as Fin-order
  greedy over the local table of their β at the same arena, so the
  recursion is two functions on (budget, phase), not three. Modules:
  Isolate (sat_iso/drank_iso/radiiLe_of_drank), Relativize (β↾cluster
  with marker color, sat_rel uniform in the tuple), Reduction
  (toDistFO + rank), Evaluator (recursion + correctness under the
  antidiagonal invariant k'+q' ≤ q_top keeping all radii ≤
  ρ⁻(0,q_top); checkpoint `evaluator_decides`, kernel three + Lax12
  UQW only). Deferred to P7: the edgeless-arena unary evaluation
  (base case is `Sat` math-side, a color-lookup algorithm
  machine-side).

  **D12 as-built record (gate passed on Jan's overnight mandate
  "keep going until ndmc is complete"; flagged for morning review).**
  Statements frozen: the concept surface is untouched since the P2
  guard-set `exL` revision — P3/P4 were proofs-only; the four
  discharged theorem concepts carry exactly the intended assumption
  footprints (locality/normalForm/covers: none; splitter win: Lax12
  UQW; checkpoint: Lax12 UQW). Elaboration costs measured: every P4
  module elaborates in ≤ ~4 s incremental, full proofs package 2034
  jobs with no hotspots — R4 is not binding. L4 re-judgment: the
  evaluator names the exact objects the program must materialize
  (clusterOf/centerOf/HasBatch batch/enumOf/stepArena/stepColoring/
  stepFormula), the P3 strategy functions realize HasBatch, and the
  toolkit closed with Spec-form guidance — the RAM half proceeds on
  plan (P5–P7), risk concentrated in P6/R1 as budgeted.

**Cross-campaign gate (rev 3): P5–P7 start only once
`word-ram/imp-toolkit-plan.md` is closed** (its P4 library through P7
pins). The two campaigns meet at the D12 gate: if the toolkit is
still open when P4 finishes here, sessions go to the toolkit next,
not to a premature P5.

- [x] **P5 — RAM primitives** — done 2026-07-29 (overnight
  continuation, Jan's "keep going until ndmc is complete" mandate).
  RamBfs (masked depth-capped BFS, threshold-form Spec = the
  cumulative profile colors, cost in-Spec), RamBfsPaths (parents +
  path extraction, PathOracle recipe), RamScatter (greedy + exclusion
  BFS, fully walked), RamElim (Matula–Beck bucket elimination —
  rank counts down so one k serves InDegLE and BackDegLE;
  `implements` fully discharged; a correctness fix en route: the
  degree invariant was false at eliminated vertices). All kernel
  three, all with compiled #guard demos.
- [x] **P6 — ordering + cover, math and programs** — done
  2026-07-29. **R1 retired unconditionally**: Augmentation (the
  design-note densification-transfer route is invalid — star square —
  in-degree structure is essential; wcol-canonical existence),
  AugmentedDensity (the awarding route: one-sided witness claims cap
  collisions at d+1; joint in-degree/density recursion, no residual
  hypothesis), OrderedCovers (GKS 6.5/6.6 via meet_of_walk, 3 rounds
  per doubling), CoverDegree (closed budgets, six-hypothesis
  end-to-end cover degree ≤ ⌈c·m^δ⌉, cluster mass). Programs:
  RamAugment (NewArc rule — AugStep for any injective rank, no
  acyclicity invariant; GreedyFratRound was over-strong and was
  narrowed repo-wide, FratForward deleted), RamCover (wreach fibre =
  predecessor-ball bridge; f = first catch at r). GreedyFratRound/
  ElimPre integration refactor executed (waves A/A2).
- [ ] **P7 — driver, cost algebra, C0** — IN PROGRESS, state at the
  2026-07-29 wrap-up (branch f4d706f, full lax build green, 3440
  jobs, zero violations, zero sorry, kernel-three footprints
  throughout; NIGHTLOG has the session map):
  **Done**: BotEval (edgeless base case, k + 2^L candidates),
  SplitterWinOracle (the win at any path oracle), FormulaTables
  (per-depth tables, choice-sharing with the Evaluator PROVED),
  RamDriver (the unrolled recursion; `driver_correct` proved from
  named walk obligations; ALL semantic glue discharged — the descent
  needs no splitter win, only the base; two masks per depth keep
  ReachedO an equality; mb = ℓ(2cap+1)); walks discharged:
  ReadbackStep, Decode/Sentence (repaired forms), cluster+level
  mathematics, scatter phase, both frames, cover single-turn +
  coverPass_spec, padding + expansion/chain core, base-case
  repr/bot/base specs (the generated exU branch is unsound-but-
  unreachable, documented), ordering-phase primitive kit + rank
  inversion. Waves A/A2 repaired the obligation surfaces (memory
  clauses, word bounds, bits, Sized, PlayOk threading, ball-chain
  aliasing, CSR save/restore, width threading with zero proof-body
  rewrites in RamElim).
  **Assembly wave A3 — done 2026-07-29** (single Opus owner, 9 files,
  +1295/−778, engines byte-identical, falsification-gated). As built:
  (1) clobbering fixed by **per-depth names** (`ordName`/`xofName`/
  `xmmName`/`asgName`/`xpName`/`curName`; save/restore was rejected as
  cost-fatal — caller-arena-sized per-turn copies are the n² the
  touched-only mandate forbids); RamCover untouched, its answers
  copied once per level by `coverPhase`'s `coverSave`; the Frames
  debts `hA`/`hV`/`hinnerTab` are now satisfiable by `driverAt (j+1)`.
  (2) The guard alone was NOT sound: `PathOracle` does not make an
  unreachable ancestor's contribution vacuous, so the guarded batch
  needs `OracleGuarded` (oracle offers ∅ off `WithinDist`, matching
  the RamBfsPaths recipe) threaded through DescendStep/
  ClusterStepImplements/levelImplements. Play recording: `RecordsPlay`
  (list-matched — the `ℕ → Fin n` draft was refutable at n = 0, gate
  caught it) + `PlayRec` in **equality form** (`ReachedO` at the game
  arena itself; ≤ could never descend), REPLACING PlayOk end to end
  (`playOk_of_playRec` keeps the capital); `playRec_zero/_succ/.congr`
  landed. Supervisor review fixed `playRec_succ`'s interface: `hstep`
  now premised on `RecordsPlay σ j rounds`, not bare length (`batchO`
  varies with rounds' arenas/connectors, so the ∀-length form was
  undischargeable by the walk). (3) All clause repairs landed:
  BatchData words (EnumStep CLOSED outright), LevelPre colour words,
  CoverHeld ord index bound (chosen over OrdersBy — weaker,
  sufficient), `DepthMem` all-depths memory (TablesSized shape; a
  layout wave must cut it to j ≤ ℓ), LevelMem + par/path/wa,
  WordBound ∧ mb < B, BotMem/BaseArrs into BaseImplements AND
  LevelImplements + colour-bits hypothesis, CoverState + B + word
  pair (coverTurnImplements now IS RamCover.Implements;
  coverPass_spec one line), CoverImplements + CsrGraph, hcolread and
  hplay threaded into the surfaces (satellite hypotheses deleted).
  (4) exU untouched as documented. (5) tgt widening still deferred.
  **Waves C/D/E — CORRECTNESS HALF CLOSED 2026-07-29 (session 2,
  commits dc1ca67…9d28d4b, ten waves).** Every obligation of the
  driver stack is discharged and the end-to-end checkpoint is proved:
  **`RamDriverRoot.driverRoot_decides_sentence`** — the driver's
  output bit equals `Sat G φ`, at R = 0, costs parametric; hypotheses
  are only the input word (+ `CsrSimple` — the Lax11 encoding
  explicitly permits repeated targets, so nodup is root input data),
  the parameter equations, `hQ` (UQW at radius 2·cap, a hypothesis
  over Lax12 *definitions* — the endorsed Lax12 axioms enter only
  when C0 derives `hQ` from nowhere-denseness), and cost side
  conditions. Kernel three exactly, lean_verify'd. Session findings
  (eleven falsification-caught defects, all counterexampled, two as
  compiled theorems in `RamDriverWrites`): bits-not-words twice, two
  in-place-aliasing spec gaps, `OrderImplements` word/graph gaps,
  `OrderMem` itg/ntg words, `ElimMem` drops the rank bound (bridged
  freeze-preservingly by `elimRank_spec`/`elimCert_spec`; proper
  repair = one conjunct + export, recorded), `orderCom` PROGRAM BUG
  (second elimination on un-re-zeroed elm/bh had NO RUN — repaired by
  `elimRezeroCom`, review-marked), `clusterFrames` circularity (fixed
  via `InnerAvail`), two over-strong `TurnFrozen` clauses. Design
  pivots: **the path-oracle layer was deleted** — `SplitterWinRec`'s
  recorded-batch game replaced it (machine specs are existential;
  oracle-function batches provably underivable — C₄ witness;
  faithfulness absorbed into `splitterWins_of_reachedR`), and the
  augment walk (`RamDriverAugment`, 5277 lines over three
  continuations) closed hypothesis-free with the in/out-degree
  exchange `slotCnt_out_eq` as its one non-obvious cost fact.
  **SUPERSEDED 2026-07-30 (Jan): the cost wave below is FROZEN, not
  executed** — the campaign continues in `nd-mc-rebase-plan.md`
  (program layer re-derived through the refinement tower; items
  (1)/(3-math)/(4) survive there as its P3, (6) as its P4; (2) and
  (5) die with the hand-walked engines). This text is kept verbatim
  as the fallback contract should the rebase hit a structural
  blocker.
  **Then the cost wave** (next session): (1) solve the Kl/Ks
  recursion; (2) touched-only retrofit — LOAD-BEARING, the recursion
  as stated is n^ℓ since per-turn phases charge the whole arena
  ([[touched-only-costs]]; `clusterLoad`'s 16n² first); (3) R > 0:
  the two tgt couplings in `OrderImplements`'s docstring (fratSlots D
  > ns, K₁,₄ witness; W vs in-degrees) — this buys the cover-degree
  bound; (4) derive `hQ` from Lax12 UQW (brings in the endorsed
  axioms as intended); (5) `ElimMem` one-conjunct repair + delete
  both re-sequencing bridges; (6) the Spec→ComputesInTime bridge, C0
  discharged.
- [ ] **P8 — polish and draft submission** (1–2 sessions).
  abstract.md, manifest, `lax build`, plans/NIGHTLOG records, draft
  `lax submit` (never `--register`; freeze-consent rule).

## Feasibility judgment

This is the largest campaign in the repo — the theorem GKS got a
best-paper award for, with the algorithm actually implemented. Against
the Courcelle yardstick (17 sessions): the logic engine alone is
Courcelle-sized but purely syntactic (the paper is 12 pages of
self-contained rewriting, unusually well matched to Lean); the math
core P0–P4 lands around 15–26 sessions; the RAM half P5–P7 another
13–20 with the toolkit amortizing the glue and the graph materialized
once (rev 2: arenas are masks + profiles, never re-extracted). Call
it **30–48 sessions** end to end, with the D12 gate as the honest
re-forecast point. The rev-3 toolkit gate orders work across
campaigns without adding any: the math core never waits, and the RAM
half was always going to consume the finished toolkit rather than
race it. What
makes it *possible* at all is that four load-bearing walls already
stand endorsed and proved: nowhere denseness, UQW, subpolynomial wcol,
subpolynomial density (Lax12), and the machine + verification toolkit
(Lax13/Lax11).

Risks: **R1** cover computation within n^(1+ε) on the RAM — the one
place the source might hide algorithmic detail; P0 confronts it first,
and its fallback (a coarser but still n^ε-degree construction) changes
no statement, only constants. **R2** the isolation rewrite — still new
writing (no paper states it over distFO), but rev 2 shrank it to one
uniform-tuple lemma with no readout and no avoid-W side conditions;
what remains is the profile/matrix bookkeeping, fixed in P0's design
note and sanity-checked by Jan before P4 consumes it. **R3** real-exponent cost sums —
mitigated by one shared cost-algebra module and Lax12's existing
c·m^ε patterns. **R4** elaboration performance of formula-heavy proofs
— the rewriting functions are never evaluated on concrete sentences;
everything stays symbolic. **R5** registration ordering (needs
Lax11/12/13 registered first) — sequencing, not risk; drafts fine
meanwhile. If R1+R2 both go badly, the honest fallback is registering
the locality theorem + splitter + covers as the citable core and
carrying C0 as an open obligation of the draft — the archive is built
for exactly that.

## Open questions (all closed at rev 3)

Closed by their recommended defaults at the rev-3 wrap-up; each
remains revisable until the P1 statement freeze.

- **Q1 → Lax3.** Claim the reserved init slot Lax3, folder
  `nowhere-dense-model-checking`. Lax4 stays free (natural home for
  a future merge-width submission).
- **Q2 → real-ε form.** The side-condition bound
  `(T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)`, matching Lax12's
  `^ ε` idiom.
- **Q3 → colored graphs.** The locality theorem concept is stated
  over finite colored graphs, the general-signature specialization
  spelled out in its formalization notes.
- **Q4 → four citable theorems.** Locality, splitter-game win,
  sparse covers, headline C0, per D11.
- **Q5 → isolation game** (resolved at rev 2): the isolation-form
  (ℓ,m,r) batch game is the surfaced concept; the removal form
  appears at most proofs-side for source cross-checks.
