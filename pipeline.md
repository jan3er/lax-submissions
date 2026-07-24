# Pipeline survey (step 1 deliverable, draft for iteration)

Target: Theorem 2 of arXiv:2607.10941 (DMMPT26 below). This document maps
every ingredient of the proof to a chosen source and records how it will
formalize. Companion to `todo.md`.

## 0. What the pinned mathlib already has

- **Sauer–Shelah**: `Finset.vcDim`, `Finset.card_le_card_shatterer`
  (Pajor variant), `Finset.card_shatterer_le_sum_vcDim` in
  `Mathlib.Combinatorics.SetFamily.Shatter`. Finset-of-Finsets based; the
  paper's set-system language maps onto it directly. Nothing to state, and
  little to prove.
- **First-order logic**: `Mathlib.ModelTheory.*` has languages, terms,
  `BoundedFormula`/`Formula` syntax, full semantics (`Formula.Realize`),
  and crucially `FirstOrder.Language.graph` with `SimpleGraph.structure`
  (`Mathlib.ModelTheory.Graph`). Missing: interpretations/transductions,
  unary expansions as a packaged notion, quantifier rank. We build those.
- **Absent entirely**: Haussler/HLW packing, shallow minors, weak coloring
  numbers, quasi-wideness, nowhere denseness.

## 1. Dependency tree of Theorem 2 (paper numbering)

    Thm 2  (main; reduction to bipartite twin-free via a transduction)
    └─ Lem 21 (mon dep bipartite twin-free: |B| ≤ |A|·subpoly(|A|))
       ├─ [VC] mon dep class ⇒ neighborhood systems have VCdim ≤ d
       ├─ Lem 26 (iterate Lem 25 ≤ d times from trivial 0-sparsification)
       │  └─ Lem 25 (key step: k-sparsification → (k+1)-sparsification,
       │     dimension −1, size /polylog, definability maintained)
       │     ├─ Lem 19 (subset X of A making Hamming graphs dense;
       │     │          potential-function/harmonic-sum argument)
       │     ├─ Cor 9 ← Lem 8 (HLW: Hamming graph of VC-d family
       │     │                 has ≤ d|F| edges)
       │     ├─ Lem 10 ← Lem 7 (v-positive/v-negative families drop
       │     │                  VC-dim; Sauer–Shelah-style induction step)
       │     └─ Lem 12 (bipartite, no isolated vertices ⇒ large Y',
       │        unique neighbors in X'; = FOCS'24 [13] Lemma 10)
       └─ Lem 24 (terminal sparsification is small)
          ├─ Lem 23 (the sparsification graph H is produced by a *fixed*
          │          transduction T_{k,c}; needs "finitely many formulas
          │          of qrank ≤ c up to equivalence" — see R1 below)
          └─ Cor 6 (mon dep + K_{t,t}-free ⇒ almost linear NC)
             ├─ (6a) mon dep + weakly sparse ⇒ nowhere dense
             └─ (6b) nowhere dense ⇒ almost linear NC   [radius 1]

Transduction infrastructure used throughout: composition/transitivity
(twice: Thm 2 reduction, Lem 24), closure under induced subgraphs,
"guessing" unary predicates.

## 2. Restructuring recommendations (proof-package internal)

- **R1 — kill quantifier rank.** Lemma 23 rests on "up to logical
  equivalence there are finitely many formulas of quantifier rank ≤ c
  over a finite relational signature" — classical, but among the hardest
  single things to formalize (normal forms / rank-c type enumeration),
  and mathlib has no quantifier rank. Instead: the induction of Lem 25/26
  produces the defining formulas *explicitly* — after i steps the formula
  tuple is determined by the sign vector σ ∈ {+,−}^i (≤ 2^d tuples) plus
  a fixed per-step predicate/formula template. So define, by recursion on
  k, an explicit finite family Φ_k of formula tuples; strengthen the
  sparsification invariant to "functions defined by some tuple in Φ_k";
  let the transduction of Lem 23 guess among |Φ_k| tuples. The
  quantifier-rank bookkeeping ("complexity ≤ c") disappears from the
  whole development. Faithfulness is unaffected: this is proof-package
  material.
- **R2 — Corollary 6 as a named theorem-concept.** State "every weakly
  sparse monadically dependent class has almost linear neighborhood
  complexity" as its own concept. It is exactly the interface Lem 24
  consumes, it is a clean citable classical fact, and it decouples the
  paper's new contribution (the reduction, Appendix A) from the classical
  sparsity pipeline (6a+6b). Whether we *prove* it now is the main open
  scope question (§4).
- **R3 — edge cases in the headline statement.** |A| ∈ {0,1} makes
  c·|A|^(1+ε) fail literally (trace count is ≥ 1). Use `A.Nonempty`
  hypothesis or `(|A|+1)`-style padding — decide in statement design;
  formalization notes must argue the convention.

## 3. Ingredient-by-ingredient: chosen source + formalization notes

| # | Ingredient | Source | Effort | Notes |
|---|---|---|---|---|
| 1 | Transductions, mon dep (definitions) | DMMPT26 §2 | medium | On mathlib ModelTheory; expansion language = graph + k unary rels (small custom language). Non-copying transductions only — the paper needs nothing more. |
| 2 | Transduction calculus (composition, induced-subgraph closure, mon dep preserved) | folklore; write ourselves | **high** | Formula substitution across expansions; the workhorse. Most reusable artifact of the whole project. |
| 3 | Lem 7 (VC drop for v-positive/negative) | DMMPT26 App. A.2 | low | Self-contained, half page; adapt to `Finset.vcDim` (paper's −∞ for ∅ handled by hypotheses). |
| 4 | Lem 8 (HLW packing) | HLW'94 Lem 2.4 | medium | Elementary induction (~1 page); no probabilistic content. Alternative presentation: Matoušek, Geometric Discrepancy §5. |
| 5 | Lem 19 (dense Hamming subset) | DMMPT26 App. A.3 | low–medium | Deletion process + harmonic-number potential; needs only `Real.log` inequalities and careful counting ("each Hamming edge counted once"). |
| 6 | Lem 12 (unique-neighbor subset) | FOCS'24 (arXiv:2311.18740) Lem 10 | medium | Degree bucketing by powers of 1.1 + independent sampling p=1/d + Markov + (1−1/d)^d ≤ 1/e + first-moment. Formalize via counting/averaging over the finite cube (no measure theory needed) or `PMF`. |
| 7 | [VC] mon dep ⇒ bounded VCdim of neighborhood systems | "easy to see" in DMMPT26; write ourselves (check Mählmann thesis for citable writeup) | **high** | Contrapositive: unbounded shattering ⇒ semi-induced powerset bipartite graphs ⇒ transduce all bipartite graphs ⇒ all graphs. Needs concrete FO encodings + item 2. |
| 8 | Sparsification machinery, Lem 23–26, Lem 21, Thm 2 | DMMPT26 App. A.4 | medium–high | Mostly careful finite combinatorics; definability side via R1. The Thm-2 reduction also needs the transduction "G ↦ semi-induced twin-free bipartite" (uses item 2). |
| 9 | Cor 6a (weakly sparse + mon dep ⇒ nowhere dense) | Flipping & forking (arXiv:2505.16745) Lem 3.15, App. A; alt: Mählmann thesis Lem 13.7 | **very high** — LEFT OPEN | Needs: subdivision characterization of somewhere dense, order-type uniformization (Ramsey), subdivision surgery, transduction of all bipartite graphs from induced ℓ-subdivisions. Stated as a concept, proof left as an open obligation. |
| 10 | Cor 6b (nowhere dense ⇒ almost linear NC, radius 1) | sparsity2 notes, r = 1 specialization — full chain in §3a | **high** | In scope, proved. Radius-1 collapses the general route dramatically: no uniform quasi-wideness, no ladder/order-dimension machinery (see §3a). |

Sources digested so far: DMMPT26 §2 + App. A in full; FOCS'24 Lem 10
proof; flipfork Lem 3.15 proof sketch; sparsity2 Ch. 5 §4, Ch. 2 §§2,3,6
(Thm 6.3 proof in full), Ch. 1 §3 (densification) — everything item 10
needs.

## 3a. The Corollary-6b chain at radius 1 (sparsity2 notes, specialized)

Statement to prove: for a nowhere dense class C, ∀ε ∃c ∀G∈C, A⊆V(G):
`|{N(v) ∩ A}| ≤ c·|A|^(1+ε)`. Proof plan, bottom-up (chapter/lemma
numbers are sparsity2's):

1. **Definitions**: depth-r minors (branch sets of radius ≤ r), grads
   ∇_r and topological grads ∇̃_r, nowhere dense (∀r ∃t: K_t not a
   depth-r minor of any member), WReach_r, wcol_r, adm_r. Only nowhere
   dense (with shallow minors) surfaces as a concept; the rest is proof
   package.
2. **K_{t,t}-freeness**: nowhere dense ⇒ ∃t: no member contains K_{t,t}
   as subgraph (K_{t,t} has K_t as a depth-1 minor). Easy.
3. **Elementary VC bounds** (replaces Ch. 5 Thm 4.2 + Cor 3.8, killing
   uqw/Ch. 4 entirely): in a K_{t,t}-free graph, the systems
   {N(u) ∩ ·}, {N[u] ∩ ·}, and {WReach_1[u] ∩ ·} have VC dimension
   O(t + log t). Argument: a shattered m-set has 2^(m−t) trace-realizers
   containing a fixed t-subset; they are distinct, ≥ 2^(m−t) − m of them
   avoid the shattered set and are fully adjacent to the t-subset ⇒
   K_{t,t} once 2^(m−t) − m ≥ t. Then Sauer–Shelah (mathlib) turns VC
   bounds into polynomial trace counts.
4. **Density of nowhere dense classes** (Ch. 1 Thm 3.1, needed at r=1:
   ∇_1(G) ≤ f(ε)·n^ε): Dvořák's densification. Ingredients: min-degree
   cleanup (Lem 3.2, easy), multiplicative Chernoff for Bernoulli sums
   (derive from mathlib's mgf Chernoff `measure_ge_le_exp_mul_mgf` +
   sub-Gaussian toolkit in `Probability.Moments`; Hoeffding alone is too
   weak in the small-mean regime), densification step (Lem 3.4,
   probabilistic, ~2 pages), shallow-minor composition (Ch. 1 Lem 2.12).
   Iterates O(1/ε²) times through *increasing* depths — this is where
   the full ∀r strength of nowhere denseness is consumed. Hardest single
   piece of the 6b chain.
5. **wcol_2 ≤ n^ε**: adm_2 ≤ 1 + 12·⌈∇̃_1⌉³ (Ch. 2 Lem 3.2 at r=2:
   greedy fan-minimizing order; if it fails, fans of length-≤2 paths
   assemble a dense depth-1 topological minor — Lem 4.1/4.2); ∇̃_1 ≤ ∇_1
   (trivial); wcol_2 ≤ 1 + 2(adm_2−1)⁴ (Ch. 2 Lem 2.5 + 2.6 at r=2: BFS
   tree + milestone-signature arguments, concrete and short at r=2).
6. **Counting** (Ch. 2 Thm 6.3 at r=1, with Ch. 5 Lem 4.3's two
   Sauer–Shelah patches): fix σ with wcol_2(G,σ) ≤ d; B := ∪_{a∈A}
   WReach_1[a] (|B| ≤ d|A|); local separators X[u] := WReach_1[u] ∩ B;
   Claim 3 (paths of length ≤1 from u to A pass X[u]), Claim 4 (equal
   separator + equal profile on it ⇒ equal profile on A), Claim 5
   (X ⊆ WReach_2[φ(X)]). Patches: #profiles on a separator ≤ poly(d)
   via item 3; #realized separators ≤ |B|·(1+d^k) via VC of the
   WReach_1 system restricted to Z_b := B ∩ WReach_2[b]. Yields
   #profiles ≤ |A| · poly(d) = |A| · n^ε'.
7. **Localization + assembly** (Ch. 5 Lem 4.4 + Thm 4.1 at r=1): close C
   under subgraphs (preserves nowhere dense by definition); D := A ∪
   {witness + neighbor per realized trace}, |D| ≤ poly(|A|) via item 3's
   polynomial trace bound; apply item 6 to G[D]; rescale ε by the
   polynomial degrees. At r=1 "profiles" can be dropped for plain traces
   N(v) ∩ A throughout (a trace plus "is v ∈ A and which a = v" data;
   bookkeeping only).

Effort estimate for §3a: item 4 is the bulk; items 5–7 are careful but
routine; item 3 is short. Everything is finite combinatorics over
`SimpleGraph (Fin n)` + one excursion into finite probability (item 4).

## 4. Scope decision (settled with Jan, 2026-07-24)

**Option (ii)**: prove 6b (via §3a), leave 6a as a stated open
obligation. Consequences for the concept surface:

- "Nowhere dense" (with shallow minors) becomes a definition-concept.
- 6a ("weakly sparse + monadically dependent ⇒ nowhere dense") is a
  theorem-concept whose proof obligation stays open — a well-defined
  bounty for a follow-up submission.
- Optionally also state the converse (nowhere dense ⇒ monadically
  dependent, Adler–Adler), likewise open, so the surface carries the
  full equivalence "on weakly sparse classes: monadically dependent =
  nowhere dense" that motivated the submission. Decide in step 2.
- 6b (radius-1 almost-linear NC of nowhere dense classes) is a
  theorem-concept, proved.
- The headline theorem's proof then uses the 6a and 6b statements as
  axioms of this submission's own concept package — allowed, and the
  build stays green with 6a undischarged.

## 5. Next actions (step 1 wrap-up → step 2)

- [x] Scope: option (ii) — prove 6b, leave 6a open.
- [x] Survey the 6b chain at r=1 (§3a).
- [x] Statement design: `design.md` rev 3, frozen with Jan 2026-07-24
      (all decisions D1–D9 settled; transductions generalized to
      arbitrary relational structures per Jan).
- [x] Step 3: concept package Lax5 builds, `lax build` pipeline OK
      (scaffold was pre-allocated; manifest + abstract written).
- [ ] Step 4: proof package — `sorry`-stub the Section-2 skeleton first,
      big ingredients (§3a item 4, HLW, [VC]) last. Sub-state in
      `todo.md` (4a top-level skeleton green; 4b App-A layer; 4c §3a).
