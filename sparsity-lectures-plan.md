# Plan: extract the sparsity material into its own submission

Goal: the vendored catalog port in
`monadic-dependence-neighborhood-complexity/proofs/Lax5Proofs/Source/Catalog/SparsityLectures/`
(~7k lines, 19 modules) becomes its own submission **`sparsity-lectures/`**
(id allocated by `lax init`; called **LaxS** below). Everything in it is from
the sparsity lecture notes of Pilipczuk, Pilipczuk, Siebertz — hence the name.
Three deliverables:

1. **Standalone concepts for the gems hidden in the proofs** — uniform
   quasi-wideness, coloring numbers/admissibility, subpolynomial density,
   nd ⇒ UQW, nd ⇒ subpolynomial wcol — each a citable, endorsable unit.
2. **A naturally embedded proof package** — no `Source/Catalog/*/Full.lean`
   vendor layout; thematic modules under `LaxSProofs/`, docstrings, proper
   namespaces, and frontmattered proofs.
3. **A visible proof network** — glue proofs with `assumptions:` inside LaxS
   (headline wcol theorem assumes the chain pieces), and Lax5 re-drafted so
   its sparsity-based theorems visibly *assume* LaxS statements instead of
   silently containing their proofs. Today Lax5 has zero `assumptions:`
   anywhere.

## Architecture decision: LaxS is strictly upstream of Lax5

LaxS **must not** import Lax5's concepts. If LaxS-concepts pinned Lax5 while
Lax5-proofs pinned LaxS, any re-draft of either side moves its record triple
and breaks the other's pin — an unresolvable repin cycle (the Lax1→Lax2
repin dance, but circular). Therefore:

- LaxS has its **own definition-concepts**, textually mirroring Lax5's
  flagship idiom where the notion already exists there (walk-based shallow
  minors over `Fin n`, `GraphClass`, `wcol` via `sInf` — copy the shapes of
  `Lax5/NowhereDenseClasses.lean`, `Lax5/WeakColoring.lean`,
  `Lax5/GraphClasses.lean`). Nominal duplication across submissions is
  acceptable and noted in the formalization notes; textual mirroring makes
  the Lax5-side bridge a pointwise-trivial transport.
- Dependency direction after the dust settles:
  `Lax5-proofs ──requires──▶ LaxS-concepts` (git-pinned). Nothing else.
- Consequence: the existing catalog↔Lax5 bridge work *splits and moves up*:
  the hard half (catalog idiom `{V : Type}`+instances ↔ flagship `Fin n`
  idiom — today's `NowhereDenseBridge.lean` 1442 lines, `NowhereDenseWcol.lean`
  bridge, `QuasiWideness.lean`) becomes LaxS-internal (ported source ↔ LaxS
  concepts); the residual Lax5-side bridge (LaxS defs ↔ Lax5 defs, textually
  identical) is near-trivial.

## Concept surface (draft — refine in Phase 0, Jan signs off)

Definition-concepts (zero axioms each):
- graph classes (mirror `Lax5/GraphClasses.lean`)
- shallow minors + nowhere dense (mirror `Lax5/NowhereDenseClasses.lean`)
- shallow topological minors (needed to *state* the admissibility bound;
  Phase 0 decides whether it earns concept-hood or the chain is stated so
  it stays proof-internal)
- edge density of shallow minors (grad / subpolynomial-density predicate)
- weak/strong coloring numbers (wreach/sreach, `wcol`/`scol` via `sInf`;
  mirror `Lax5/WeakColoring.lean` for wcol)
- admissibility
- uniform quasi-wideness

Theorem-concepts (one axiom per module — the one-axiom rule):
1. nowhere dense ⇒ uniformly quasi-wide (`NDImpliesUQW`) — headline gem
2. nowhere dense ⇒ subpolynomial density of shallow minors
   (`NDSubpolynomialDensity`, Nešetřil–Ossona de Mendez)
3. admissibility bounded via density of shallow topological minors
   (`AdmBoundByTopGrad`, the 1470-line workhorse)
4. wcol/scol bounded in terms of admissibility (the
   `ColoringNumberOrdering` + `StrongColoringBoundByAdm` +
   `ColoringNumberEquivalence` chain; Phase 0 decides one vs. two
   statements — never `∧` independently provable claims)
5. nowhere dense ⇒ subpolynomial weak coloring numbers — the headline,
   discharged by a **glue proof assuming 2–4** (the Lax2 `Main.lean`
   pattern), making the internal network visible

Proof-internal (no concepts): Preliminaries, ChernoffBound, Densification,
Odd/EvenStepReduction, ShallowMinorComposition, TreeCounting, plus copies of
whatever `Lax5Proofs.Ramsey` / `Lax5Proofs.BipartiteRamsey` material
`NDImpliesUQW` consumes (LaxS cannot require Lax5's proof package; copying
into a proof package is fine — proofs absorb the ugliness).

## Lax5 re-draft (after LaxS is a submitted draft)

- Delete `Lax5Proofs/Source/` entirely.
- `proofs/lakefile.toml`: add git-pinned `[[require]]` on LaxS-concepts at
  its submitted record triple (`lax pull-db` to confirm).
- Reroute, adding `assumptions:` frontmatter:
  - `NowhereDenseWcol.lean`: assume LaxS's nd ⇒ subpoly-wcol; transport
    across the textually-identical defs.
  - `AdlerAdler.lean` (+ `QuasiWideness.lean`): assume LaxS's nd ⇒ UQW.
  - `Corollary6a.lean`: retarget its catalog-def usage (`ShallowMinor`,
    `NowhereDense`, copy-closure argument) to LaxS defs.
  - `BipartiteRamsey.lean`: retarget its `ShallowTopologicalMinor` import
    to LaxS (concept or a local def copy, per Phase 0's call).
- Same-spirit audit *inside* Lax5: where a proof of concept B contains the
  composition through already-proved concept A (e.g. `Theorem2.lean` vs
  `Corollary6b`/`WeaklySparseDependent`), re-express with `assumptions:` on
  A instead of importing A's proof. Zero mathematical change; the network
  becomes visible on the archive.
- Update `abstract.md` (proof-provenance paragraph now names the LaxS
  dependency), rebuild, `lax build --replay`, resubmit draft, repin note:
  Lax1/Lax2 are untouched by all of this.

## Phases and who does what

Fable (this plan's author) orchestrates and reviews; **Opus agents do the
writing**. One agent per phase, sequential, review between phases. Jan
checkpoints: end of Phase 0 (concept list + statement drafts) and before
each `lax submit`.

- **P0 — detailed design (Opus)**: read the 19 catalog modules + the three
  Lax5 bridge files + Corollary6a; append to this file a `## Design` section
  with (a) full Lean drafts of every LaxS concept module, (b) module map
  old-path → new-path for the proof package, (c) exact list of Ramsey
  lemmas to copy, (d) the Lax5 diff list, file by file. Decisions delegated
  to P0: topological-minor concept-hood; one vs. two chain statements;
  whether grad is stated per-class or per-graph.
- **P1 — scaffold + concepts (Opus)**: `lax init sparsity-lectures`; write
  the concept package per the design; `lake build` green; full styleguide
  compliance (no Classical, docstrings everywhere, formalization notes).
- **P2 — proof package (Opus, biggest)**: port the catalog modules into
  `LaxSProofs/` under natural names/namespaces, write the LaxS-internal
  bridges (absorbing today's NowhereDenseBridge et al. where they apply),
  frontmattered proofs incl. the glue proof with `assumptions:`;
  `lax build sparsity-lectures --replay` green.
- **P3 — submit**: commit, push, `lax submit sparsity-lectures` (draft),
  `lax pull-db`. [Jan checkpoint]
- **P4 — Lax5 reroute (Opus)**: per the list above; `lake build` against
  the pushed LaxS commit during development, final `lax build --replay`,
  resubmit Lax5 draft. [Jan checkpoint]
- **P5 — wrap-up**: README submission list gains LaxS; memory + this plan
  updated; NIGHTLOG-style session notes if relayed.

## Known risks / gotchas

- The catalog port lives in `{V : Type}` + `DecidableEq`/`Fintype`
  instances; LaxS concepts are `Fin n`-canonical and Classical-free. The
  bridging exists but must be re-homed and re-aimed — budget most of P2
  for it.
- `NDImpliesUQW/Full.lean` imports `Lax5Proofs.BipartiteRamsey` and
  `Lax5Proofs.Ramsey` — the port is not currently self-contained. P0 must
  produce the exact copy list.
- `lax init` allocates the real id; all `LaxS` placeholders resolve then.
- Never `lake update`; toolchain/mathlib pins are archive-wide.
- Jan's unrelated WIP (`vc-contracts/`, `vc-night-brief.md`, NIGHTLOG.md
  edits) stays unstaged.

## Design

Output of Phase P0. `LaxS` is the placeholder id; `lax init` fixes it.

### Delegated decisions, decided

**(1) Shallow topological minors do *not* earn a definition-concept.**
**[Reversed in P1.5 on Jan's directive "use that form" — the surface now
carries `Lax12/ShallowTopologicalMinors.lean` and the admissibility bound
is stated in the notes' topological form; see the P1.5 log and the updated
`AdmissibilityBound` draft in section (a). The rationale below is kept as
the record of what was traded away.]** The
admissibility bound is stated over ordinary shallow minors:

    HasDensityAtMost G r d → adm G r ≤ 1 + 6 * r * d ^ 3

Rationale. (a) The catalog's `ShallowTopologicalMinorModel` is an
edge-indexed family of routed paths with `Sym2.Mem.other` plumbing
(`edgeTail`, `edgeTail_mem`, two interior-avoidance clauses); restyling
that into flagship idiom is possible but drags real formalization noise
onto the endorsement surface, which is exactly what the styleguide keeps
out. (b) The pipeline never needs the sharper form: in
`NDSubpolynomialWcol/Full.lean` the topological minor produced inside
`adm_le_of_topGrad_bound`'s hypothesis is *immediately* converted to a
shallow minor (`shallowTopologicalMinor_toShallowMinor`) so that the
density bound applies. Stating the hypothesis over shallow minors makes
that conversion an implementation detail of the LaxS proof and shortens
the glue. (c) The stated form is strictly implied by the catalog theorem
(every shallow topological minor is a shallow minor, so the shallow-minor
hypothesis is the stronger one), hence dischargeable with a two-line
bridge. (d) A later submission wanting topological grad can add its own
definition-concept; nothing here has to move.

The catalog also takes the hypothesis at depth `r - 1` and concludes at
radius `r`. LaxS takes hypothesis and conclusion both at `r`. This is
again implied (depth-`(r-1)` minors are depth-`r` minors, so the depth-`r`
hypothesis is stronger) and removes truncated `ℕ` subtraction from a
concept statement. Cost: the archive records `∇_r`-based rather than
`∇̃_{r-1}`-based admissibility. Flagged for Jan below.

Consequence for the proof packages: `ShallowTopologicalMinorModel` stays
proof-internal, and it stays proof-internal *twice* — LaxS needs it for
`BipartiteRamsey`, Lax5 needs it for `NowhereDenseBridge`. Duplication in
proof packages is free.

**(2) The coloring-number chain is two theorem-concepts, not one.**

    LaxS.StrongColoringBound.scol_le_of_adm : scol G r ≤ 1 + (adm G r - 1) ^ r
    LaxS.WeakColoringBound.wcol_le_of_scol  : wcol G r ≤ 1 + r * (scol G r - 1) ^ r

These are Lemma 2.5 and Lemma 2.6 of the notes, with disjoint proofs
(`StrongColoringBoundByAdm/Full.lean` + `TreeCounting.lean`, 1083 lines,
versus `ColoringNumberOrdering/Full.lean`, 406 lines). Each is citable and
downstream-usable on its own; collapsing them into Corollary 2.7 would
bury a bounty inside another statement. The one-axiom rule forbids putting
both in one module, and conjoining them is forbidden outright.

Corollary 2.7 (`wcol ≤ 1 + r·(adm-1)^(r²)`) gets **no** concept of its
own: it is pure arithmetic over the two, with no independent content, and
turning it into a third theorem-concept discharged by a glue proof would
add a review unit that says nothing new. Its 20 lines of arithmetic move
into the headline glue proof, which therefore assumes four statements
(density, admissibility bound, and the two chain links). The catalog file
`ColoringNumberEquivalence/Full.lean` disappears.

**(3) Density is stated both per-graph and per-class, in one
definition-concept.** `LaxS/ShallowMinorDensity.lean` carries

    HasDensityAtMost G r d          -- per graph: every depth-r minor H has ≤ d·|V(H)| edges
    HasSubpolynomialDensity C       -- per class: ≤ c·m^(1+ε) for every depth-r minor of a member

The per-graph predicate is what the admissibility statement takes as a
hypothesis; the per-class predicate is what the Nešetřil–Ossona de Mendez
theorem concludes. They are the same idea at two quantifier depths, which
is exactly the shape of the flagship `Lax5/WeakColoring.lean` (`wcol` plus
`HasSubpolynomialWcol`), so they belong in one review unit. No numeric
`grad` parameter is introduced: no statement consumes a number, and a
`sInf`-defined grad would be surface nothing uses. The class-level bound
uses a multiplicative constant rather than the catalog's size threshold,
matching `HasSubpolynomialWcol`; the two are equivalent because a graph on
`m` vertices has at most `m²` edges.

**Headline glue assumptions.** `LaxS.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense`
is proved by a glue proof with

    assumptions:
      - LaxS.NowhereDenseDensity.hasSubpolynomialDensity_of_nowhereDense
      - LaxS.AdmissibilityBound.adm_le_of_hasTopologicalDensityAtMost
      - LaxS.StrongColoringBound.scol_le_of_adm
      - LaxS.WeakColoringBound.wcol_le_of_scol

and nothing else (the subgraph-closure lemma, the "a shallow minor has
no more vertices than its host" lemma, the P1.5 addition "a depth-`r`
topological minor is a depth-`r` minor", and the monotonicity of `adm`
in the radius are axiom-free helpers). This
reproduces `NDSubpolynomialWcol/Full.lean` step for step; see
"Verification of the composition" below.

### (a) Concept modules, in full

Seven definition-concepts (six as drafted in P0, plus
`ShallowTopologicalMinors` added in P1.5), six theorem-concepts.
`LaxS.lean` imports them in this order.

#### `concepts/LaxS/GraphClasses.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Graph classes
type: definition
---
A graph class is a set of finite simple graphs. A class contains, for
each number of vertices *n*, some of the simple graphs on the canonical
*n*-element vertex type.

# Formalization notes

Every finite simple graph is isomorphic to a graph on some `Fin n`, so
ranging over the canonical carriers loses no generality. Closure under
isomorphism is deliberately not required: no statement of this
submission needs it, and all hypotheses range over concrete members.
`GraphClass` is an abbreviation, so class membership is plain
application `C n G` throughout the submission, and any identically
shaped abbreviation elsewhere denotes literally the same function type.
-/

namespace LaxS.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end LaxS.GraphClasses
```

Mirrors `Lax5/GraphClasses.lean` verbatim, minus `allGraphs` and
`WeaklySparse` (no LaxS statement mentions either). Because `GraphClass`
is an `abbrev`, `LaxS.GraphClasses.GraphClass` and
`Lax5.GraphClasses.GraphClass` are the *same* type — the Lax5 transport
needs no coercion at all.

#### `concepts/LaxS/NowhereDenseClasses.lean`

Textually identical to `Lax5/NowhereDenseClasses.lean` except for the
namespace and the `open` line; reproduced here in full because the Lax5
transport depends on the field names matching one for one.

```lean
import LaxS.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
---
title: Nowhere dense graph classes
type: definition
---
A graph *H* is a depth-*r* minor of a graph *G* if *H* can be obtained
from *G* by deleting vertices and edges and contracting pairwise
disjoint connected subgraphs of radius at most *r*. A graph class is
nowhere dense if for every depth *r* there is a *t* such that no member
has the complete graph on *t* vertices as a depth-*r* minor.

# Formalization notes

A depth-`r` minor is witnessed by a `ShallowMinorModel`: pairwise
disjoint branch sets, one per vertex of `H`, and an edge of `G` between
the branch sets of any two adjacent vertices of `H`. The radius
condition — every element of a branch set is reached from its center by
a walk of length at most `r` staying inside the branch set — subsumes
connectivity of the branch sets, so no separate connectivity field is
carried. `center_mem` is not derivable: it also rules out empty branch
sets, as the standard definition requires. `⊤ : SimpleGraph (Fin t)` is
mathlib's complete graph.
-/

namespace LaxS.NowhereDenseClasses

open LaxS.GraphClasses

/-- A model of `H` as a depth-`r` minor of `G`: pairwise disjoint branch
sets, each spanned by walks of length at most `r` from a center vertex
(hence connected of radius at most `r`), with an edge of `G` between the
branch sets of any two adjacent vertices of `H`. -/
structure ShallowMinorModel {V W : Type*} (r : ℕ) (H : SimpleGraph W)
    (G : SimpleGraph V) where
  /-- The branch set of each vertex of `H`. -/
  branch : W → Set V
  /-- The center of each branch set. -/
  center : W → V
  /-- Centers lie in their branch sets (so branch sets are nonempty). -/
  center_mem : ∀ u, center u ∈ branch u
  /-- Distinct branch sets are disjoint. -/
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  /-- Every vertex of a branch set is reached from the center by a walk
  of length at most `r` inside the branch set. -/
  radius_le : ∀ u, ∀ x ∈ branch u, ∃ w : G.Walk (center u) x,
    w.length ≤ r ∧ ∀ y ∈ w.support, y ∈ branch u
  /-- Adjacent vertices of `H` have adjacent branch sets. -/
  adj : ∀ u v, H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

/-- `H` is a minor of `G` at depth `r`. -/
def HasShallowMinor {V W : Type*} (G : SimpleGraph V) (r : ℕ)
    (H : SimpleGraph W) : Prop :=
  Nonempty (ShallowMinorModel r H G)

/-- A graph class is nowhere dense if for every depth `r` some complete
graph is not a depth-`r` minor of any member. -/
def NowhereDense (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ HasShallowMinor G r (⊤ : SimpleGraph (Fin t))

end LaxS.NowhereDenseClasses
```

#### `concepts/LaxS/ShallowMinorDensity.lean`

```lean
import LaxS.NowhereDenseClasses
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Edge density of shallow minors
type: definition
---
A graph *G* has depth-*r* density at most *d* if every depth-*r* minor
*H* of *G* has at most *d* · |V(H)| edges — the standard "grad" bound on
how dense the shallow minors of a sparse graph can be. A graph class has
subpolynomial density if for every depth *r* and every ε > 0 there is a
constant *c* such that every depth-*r* minor *H* of a member, on *m*
vertices, has at most *c* · *m*^(1+ε) edges: shallow-minor edge counts
*m*^(1+o(1)).

# Formalization notes

Both predicates are stated over the shallow-minor relation of the
nowhere dense concept, so one notion of depth-*r* minor serves the whole
submission. Minors range over the canonical carriers `Fin m`: every
finite graph is isomorphic to one of those and the shallow-minor
relation is invariant under isomorphism, so nothing is lost.

Edges are counted as the natural cardinality (`Set.ncard`) of
`edgeSet`, which needs no decidability instance and is the exact count
on the finite carriers used here. `HasDensityAtMost` counts edges rather
than twice the edges, matching the usual `|E(H)| ≤ d · |V(H)|` form (the
greatest reduced average density is then at most `2 · d`).

No numeric density parameter is introduced. Every statement of this
submission either supplies a concrete bound `d` or concludes the
class-level predicate, so a `sInf`-defined grad would be review surface
that no claim consumes. The class-level bound carries a multiplicative
constant instead of the size threshold used in the literature proof; the
two agree because a graph on *m* vertices has at most *m*² edges, and
the constant form matches the subpolynomial bound of the coloring-number
concept.
-/

namespace LaxS.ShallowMinorDensity

open LaxS.GraphClasses LaxS.NowhereDenseClasses

/-- Every depth-`r` minor of `G`, on `m` vertices, has at most `d · m`
edges. -/
def HasDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (r d : ℕ) : Prop :=
  ∀ (m : ℕ) (H : SimpleGraph (Fin m)), HasShallowMinor G r H →
    H.edgeSet.ncard ≤ d * m

/-- Every depth-`r` minor of every member of the class, on `m` vertices,
has at most `c · m^(1+ε)` edges, where `c` depends only on the depth `r`
and on `ε > 0`: shallow-minor edge counts `m^(1+o(1))`. -/
def HasSubpolynomialDensity (C : GraphClass) : Prop :=
  ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), HasShallowMinor G r H →
        (H.edgeSet.ncard : ℝ) ≤ c * (m : ℝ) ^ (1 + ε)

end LaxS.ShallowMinorDensity
```

#### `concepts/LaxS/ShallowTopologicalMinors.lean`

Added in P1.5 (reversing decision (1)); the authoritative text is
`sparsity-lectures/concepts/Lax12/ShallowTopologicalMinors.lean`. It
states Definitions 2.15 and 2.16 of Chapter 1 of the notes, in the
flagship idiom — a `Prop`-valued six-field structure, no `Sym2`, no
decidability instances, zero axioms:

```lean
structure ShallowTopologicalMinorModel {V W : Type*} (r : ℕ) (H : SimpleGraph W)
    (G : SimpleGraph V) where
  principal : W → V
  principal_inj : Function.Injective principal
  walk : ∀ (u v : W), H.Adj u v → G.Walk (principal u) (principal v)
  length_le : ∀ (u v : W) (h : H.Adj u v), (walk u v h).length ≤ 2 * r + 1
  principal_eq : ∀ (u v : W) (h : H.Adj u v) (w : W),
    principal w ∈ (walk u v h).support → w = u ∨ w = v
  disjoint : ∀ (u v : W) (h : H.Adj u v) (u' v' : W) (h' : H.Adj u' v') (x : V),
    x ∈ (walk u v h).support → x ∈ (walk u' v' h').support →
      x ∉ Set.range principal → (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')

def HasShallowTopologicalMinor {V W : Type*} (G : SimpleGraph V) (r : ℕ)
    (H : SimpleGraph W) : Prop :=
  Nonempty (ShallowTopologicalMinorModel r H G)

def HasTopologicalDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (r d : ℕ) : Prop :=
  ∀ (m : ℕ) (H : SimpleGraph (Fin m)), HasShallowTopologicalMinor G r H →
    H.edgeSet.ncard ≤ d * m
```

Connecting walks are indexed by adjacent *pairs* rather than by the edge
set, which is what keeps `Sym2` off the surface; both orientations of an
edge carry a walk and the two are not tied to each other, because
`disjoint` concludes that the two edges agree and therefore never fires
on one edge's two orientations. `HasTopologicalDensityAtMost` mirrors
`ShallowMinorDensity.HasDensityAtMost` clause for clause; no numeric ∇̃
is introduced, for the reason given there.

#### `concepts/LaxS/ColoringNumbers.lean`

```lean
import LaxS.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Generalized coloring numbers
type: definition
---
Fix a linear ordering of the vertices of a graph *G*. A vertex *u* is
weakly *r*-reachable from *v* if some path from *v* to *u* of length at
most *r* has *u* as its smallest vertex, and strongly *r*-reachable from
*v* if some path from *v* to *u* of length at most *r* has *v* as its
smallest vertex apart from *u* itself. The weak *r*-coloring number
wcol_r(*G*) and the strong *r*-coloring number scol_r(*G*) are the
minima, over all orderings, of the largest number of vertices weakly
respectively strongly *r*-reachable from a single vertex. A graph class
has subpolynomial weak coloring numbers if for every radius *r* and
every ε > 0 there is a constant *c* such that every subgraph *H* of a
member, on *m* vertices, satisfies wcol_r(*H*) ≤ *c* · *m*^ε.

# Formalization notes

An ordering of the vertices is a permutation `π` of `Fin m` assigning
each vertex its position. Both reachability sets are stated with walks,
as in the nowhere dense concept: shortcutting a walk to a path only
shrinks its support, so walks of length at most `r` reach exactly the
vertices that such paths do. In `wreach` the `π`-minimality of `u` on
the whole support already forces `π u ≤ π v`; in `sreach` only the
interior of the walk is constrained, so `π u ≤ π v` is a separate
conjunct. Both sets contain `v`.

`wcol` and `scol` are the least achievable bounds `k`, `Nat.sInf`s over
nonempty sets — `k = m` works for any ordering — so the convention
`Nat.sInf ∅ = 0` is never exercised; the counts are `Set.ncard`. Weak
and strong coloring numbers are one review unit because they are the
same construction differing in a single clause, and every relation
between them is read off that contrast.

The class-level bound is uniform over subgraph copies (`⊑`) of members,
each measured by its own vertex count `m`; this is the literature form
for subgraph-closed classes, and the uniformity is what localization
arguments downstream consume. At `m = 0` both sides vanish, so no
nonemptiness hypothesis is needed.
-/

namespace LaxS.ColoringNumbers

open scoped SimpleGraph
open LaxS.GraphClasses

/-- The set of vertices weakly `r`-reachable from `v` in `G` under the
vertex ordering `π` (vertex `u` sits at position `π u`): the endpoints
`u` of walks from `v` of length at most `r` on whose support `u` is
`π`-minimal. Contains `v` itself. -/
def wreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | ∃ w : G.Walk v u, w.length ≤ r ∧ ∀ y ∈ w.support, π u ≤ π y}

/-- The set of vertices strongly `r`-reachable from `v` in `G` under the
vertex ordering `π`: the vertices `u` at or before `v` that are the
endpoint of a walk from `v` of length at most `r` all of whose other
vertices come strictly after `v`. Contains `v` itself. -/
def sreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | π u ≤ π v ∧ ∃ w : G.Walk v u, w.length ≤ r ∧
    ∀ y ∈ w.support, y ≠ v → y ≠ u → π v < π y}

/-- The weak `r`-coloring number of `G`: the least `k` such that under
some vertex ordering every vertex weakly `r`-reaches at most `k`
vertices. -/
noncomputable def wcol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | ∃ π : Equiv.Perm (Fin n), ∀ v, (wreach G π r v).ncard ≤ k}

/-- The strong `r`-coloring number of `G`: the least `k` such that under
some vertex ordering every vertex strongly `r`-reaches at most `k`
vertices. -/
noncomputable def scol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | ∃ π : Equiv.Perm (Fin n), ∀ v, (sreach G π r v).ncard ≤ k}

/-- Every subgraph of every member of the class, on `m` vertices, has
weak `r`-coloring number at most `c · m^ε`, where `c` depends only on
the radius `r` and on `ε > 0`: weak coloring numbers `m^{o(1)}`. -/
def HasSubpolynomialWcol (C : GraphClass) : Prop :=
  ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
        (wcol H r : ℝ) ≤ c * (m : ℝ) ^ ε

end LaxS.ColoringNumbers
```

`wreach`, `wcol` and `HasSubpolynomialWcol` are byte-for-byte the Lax5
declarations, so `LaxS.ColoringNumbers.wcol = Lax5.WeakColoring.wcol`
holds by `rfl` and the Lax5-side transport of the headline is definitional.

#### `concepts/LaxS/Admissibility.lean`

```lean
import LaxS.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Nat.Lattice

/-!
---
title: Admissibility
type: definition
---
Fix a linear ordering of the vertices of a graph *G*. An admissible
family of size *k* at a vertex *v* consists of *k* paths of length at
most *r* that start at *v*, end at vertices smaller than *v*, and are
pairwise disjoint apart from *v*. The *r*-admissibility adm_r(*G*) is
the minimum over all orderings of the largest *k* + 1 for which some
vertex of *G* carries an admissible family of size *k*. Counting *v*
itself is the usual convention: it makes admissibility at least 1 and at
most the strong *r*-coloring number.

# Formalization notes

The ordering is a permutation `π` of `Fin n`, as in the coloring-number
concept, and the family is indexed by `Fin k`, so its size is the
parameter of the structure rather than a derived cardinality. Paths are
stated as walks, as everywhere in this submission: bypassing a walk to a
path shrinks its support, so a family of walks meeting only in `v`
yields a family of paths meeting only in `v` of the same size, and the
two readings define the same largest `k`.

The endpoints of a family are automatically pairwise distinct — a shared
endpoint would lie on two paths and differ from `v` — so no injectivity
field is carried. `HasAdmAtMost G r k` says that some ordering admits no
family of `k` paths anywhere, and `adm` is the least such `k`. The set
is nonempty (`k = n + 1` always qualifies, since a family's endpoints
are `k` distinct vertices other than `v`), so `Nat.sInf ∅ = 0` is never
exercised; on the empty graph every bound holds vacuously and `adm`,
`wcol`, `scol` are all `0`.
-/

namespace LaxS.Admissibility

open LaxS.GraphClasses

/-- An admissible family of `k` paths at `v` under the ordering `π`:
`k` walks of length at most `r` out of `v`, each ending strictly before
`v` in the ordering, pairwise meeting only in `v`. -/
structure AdmFamily {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (r k : ℕ) (v : Fin n) where
  /-- The endpoint of each path. -/
  target : Fin k → Fin n
  /-- The path from `v` to each endpoint. -/
  path : ∀ i, G.Walk v (target i)
  /-- Every endpoint comes strictly before `v` in the ordering. -/
  target_lt : ∀ i, π (target i) < π v
  /-- Every path has length at most `r`. -/
  length_le : ∀ i, (path i).length ≤ r
  /-- Distinct paths meet only in `v`. -/
  meet_eq : ∀ i j, i ≠ j → ∀ y ∈ (path i).support,
    y ∈ (path j).support → y = v

/-- Some vertex ordering admits no admissible family of `k` paths at any
vertex: the `r`-admissibility is at most `k`. -/
def HasAdmAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ) : Prop :=
  ∃ π : Equiv.Perm (Fin n), ∀ (v : Fin n) (j : ℕ),
    Nonempty (AdmFamily G π r j v) → j + 1 ≤ k

/-- The `r`-admissibility of `G`: the least bound achieved by some
vertex ordering. -/
noncomputable def adm {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | HasAdmAtMost G r k}

end LaxS.Admissibility
```

#### `concepts/LaxS/UniformQuasiWideness.lean`

```lean
import LaxS.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

/-!
---
title: Uniform quasi-wideness
type: definition
---
A set *A* of vertices is distance-*r* independent in *G* if any two
distinct vertices of *A* are at distance more than *r*. A graph class is
uniformly quasi-wide if for every radius *r* there are a threshold
function *N* and a separator bound *s* such that in every member *G*,
every vertex set *A* of size at least *N*(*m*) contains a distance-*r*
independent subset of size at least *m* of *G* − *S*, for some set *S*
of at most *s* vertices.

# Formalization notes

Distance is stated with walks: two vertices are at distance more than
`r` exactly when every walk between them is longer than `r`, which needs
no metric, connectivity or decidability instance. Deleting a vertex set
is modelled by isolating it — `deleteVerts G S` keeps the carrier and
drops every edge incident to `S` — so every set in the statement lives
in the same vertex type and no subtype plumbing enters the surface.
Since the witness satisfies `B ⊆ A \ S`, the isolated vertices are not
in `B` and distance-`r` independence in the isolated graph is the same
as in the induced subgraph on the complement of `S`.

Sets and `Set.ncard` are used throughout, as in the other concepts of
this submission. The threshold `N` may depend on the requested size `m`,
while the separator bound `s` may not: that uniformity in `s` is the
"uniform" of uniform quasi-wideness and is the whole strength of the
notion. `DistIndependent` and `deleteVerts` are stated for an arbitrary
vertex type, since both are pointwise notions and the proofs consuming
them work over intermediate carriers.
-/

namespace LaxS.UniformQuasiWideness

open LaxS.GraphClasses

/-- A set of vertices is distance-`r` independent in `G` when every walk
between two distinct members is longer than `r`. -/
def DistIndependent {V : Type*} (G : SimpleGraph V) (r : ℕ) (A : Set V) : Prop :=
  A.Pairwise fun u v => ∀ p : G.Walk u v, r < p.length

/-- `G` with the vertices of `S` isolated: every edge incident to `S` is
removed and the vertex type is unchanged. This models `G − S`. -/
def deleteVerts {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

/-- A graph class is uniformly quasi-wide if for every radius `r` there
are a threshold function `N` and a separator bound `s` such that in
every member, every vertex set of size at least `N m` contains a
distance-`r` independent subset of size at least `m` after deleting at
most `s` vertices. -/
def UniformlyQuasiWide (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ (N : ℕ → ℕ) (s : ℕ),
    ∀ (m n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Set (Fin n), N m ≤ A.ncard →
        ∃ S B : Set (Fin n),
          S.ncard ≤ s ∧ B ⊆ A \ S ∧ m ≤ B.ncard ∧
          DistIndependent (deleteVerts G S) r B

end LaxS.UniformQuasiWideness
```

`DistIndependent` and `deleteVerts` are the catalog declarations with
`{V : Type}` relaxed to `{V : Type*}` and `Finset` replaced by `Set`, so
the ported step-reduction lemmas can use the concept definitions directly
rather than a proof-package copy.

#### `concepts/LaxS/NowhereDenseUQW.lean`

```lean
import LaxS.NowhereDenseClasses
import LaxS.UniformQuasiWideness

/-!
---
title: Nowhere dense classes are uniformly quasi-wide
type: theorem
---
Every nowhere dense graph class is uniformly quasi-wide: for every
radius *r* there are a threshold function *N* and a separator bound *s*
such that in every member, every vertex set of size at least *N*(*m*)
contains a distance-*r* independent subset of size at least *m* after
deleting at most *s* vertices.

# Formalization notes

Hypothesis and conclusion are the shared predicates of the two imported
definition concepts, so the statement adds nothing of its own. The
strength of the theorem is entirely in the quantifier order already
carried by `UniformlyQuasiWide`: the separator bound depends on the
class and the radius alone, not on the requested size or on the member.
The converse implication holds on subgraph-closed classes but is a
separate claim with a separate proof and is not stated here.
-/

namespace LaxS.NowhereDenseUQW

open LaxS.GraphClasses LaxS.NowhereDenseClasses LaxS.UniformQuasiWideness

/-- Nowhere dense graph classes are uniformly quasi-wide. -/
axiom uniformlyQuasiWide_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    UniformlyQuasiWide C

end LaxS.NowhereDenseUQW
```

Discharged by the catalog's

    nd_implies_uqw (C : GraphClass) : IsNowhereDense C → UniformlyQuasiWide C

(`NDImpliesUQW/Full.lean:494`). Quantifier map: the catalog's `C` ranges
over `{V : Type}` with `DecidableEq`/`Fintype`; the concept's `C` ranges
over `Fin n`. The bridge instantiates the catalog theorem at the *copy
closure* `fun H => ∃ n G, C n G ∧ H ⊑ G` (already written as
`copyClosure` in `Lax5Proofs/QuasiWideness.lean`), which is nowhere dense
in the catalog sense whenever `C` is nowhere dense in the concept sense,
and then specialises to `G` itself via `H ⊑ G` reflexivity. The remaining
gap is `Finset` versus `Set`: `A.toFinset` in, `Set.ncard_coe_finset`
out.

#### `concepts/LaxS/NowhereDenseDensity.lean`

```lean
import LaxS.NowhereDenseClasses
import LaxS.ShallowMinorDensity

/-!
---
title: Nowhere dense classes have subpolynomial shallow-minor density
type: theorem
---
Every nowhere dense graph class has subpolynomial density: for every
depth *r* and every ε > 0 there is a constant *c* such that every
depth-*r* minor of a member, on *m* vertices, has at most
*c* · *m*^(1+ε) edges. Together with the reverse implication — which is
immediate, since a large clique as a shallow minor forces quadratically
many edges — this is the density characterization of nowhere denseness
of Nešetřil and Ossona de Mendez.

# Formalization notes

Both hypothesis and conclusion are the shared predicates of the imported
definition concepts. The bound is uniform over all members of the class
and all their depth-*r* minors, with the constant depending only on the
depth and on ε; that uniformity is what the coloring-number chain
downstream consumes. Only the stated direction is claimed: the easy
converse is a separate statement and is not conjoined here.
-/

namespace LaxS.NowhereDenseDensity

open LaxS.GraphClasses LaxS.NowhereDenseClasses LaxS.ShallowMinorDensity

/-- Nowhere dense graph classes have subpolynomial shallow-minor
density. -/
axiom hasSubpolynomialDensity_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    HasSubpolynomialDensity C

end LaxS.NowhereDenseDensity
```

Discharged by

    nd_subpolynomial_density (C : GraphClass) (hC : IsNowhereDense C) (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj],
        (∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W) (G : SimpleGraph W),
          C G ∧ IsShallowMinor H G r) →
        N ≤ Fintype.card V →
        (H.edgeFinset.card : ℝ) < (Fintype.card V : ℝ) ^ (1 + ε)

(`NDSubpolynomialDensity/Full.lean:973`). Quantifier map: `C` ↦ copy
closure of the concept class as above; `H` ↦ the concept's `H : SimpleGraph (Fin m)`
with `Fintype.card (Fin m) = m`; the catalog's shallow-minor-of-a-member
hypothesis is exactly `HasShallowMinor G r H` after the walk/path
repacking. Threshold to constant: take `c := max 1 (N ^ 2)`. For `m ≥ N`
the catalog bound gives `< m ^ (1+ε) ≤ c · m ^ (1+ε)`; for `1 ≤ m < N`,
`edges ≤ m² ≤ N² ≤ c ≤ c · m ^ (1+ε)`; for `m = 0` both sides are `0`.
`H.edgeSet.ncard = H.edgeFinset.card` via `Set.ncard_coe_finset` under
`Classical.decRel`.

#### `concepts/LaxS/AdmissibilityBound.lean`

Restated in P1.5 to the notes' Lemma 3.2 form (Chapter 2, 2019/20
edition), index-shifted by one so that no truncated `ℕ` subtraction
enters a concept statement.

```lean
import LaxS.Admissibility
import LaxS.ShallowTopologicalMinors

/-!
---
title: Admissibility is bounded by topological shallow-minor density
type: theorem
---
If every depth-*r* topological minor of a graph *G* has at most
*d* · |V| edges, then the (*r*+1)-admissibility of *G* is at most
1 + 6 · (*r*+1) · *d*³. …

The source lecture notes state this as Lemma 3.2 of Chapter 2 (2019/20
edition): adm_*r*(*G*) ≤ 1 + 6*r*⌈∇̃_{*r*−1}(*G*)⌉³.

# Formalization notes

… the shifted form ranges over exactly the instances *r* ≥ 1 of the
notes' form, which are all of its instances with a defined hypothesis;
`d` plays the notes' ⌈∇̃_{*r*−1}(*G*)⌉. …
-/

namespace LaxS.AdmissibilityBound

open LaxS.Admissibility LaxS.ShallowTopologicalMinors

/-- A depth-`r` topological edge-density bound `d` for `G` bounds the
`(r+1)`-admissibility of `G` by `1 + 6 · (r+1) · d ^ 3`. -/
axiom adm_le_of_hasTopologicalDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n))
    (r d : ℕ) (h : HasTopologicalDensityAtMost G r d) :
    adm G (r + 1) ≤ 1 + 6 * (r + 1) * d ^ 3

end LaxS.AdmissibilityBound
```

Discharged by

    adm_le_of_topGrad_bound {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V) (r d : ℕ)
      (hd : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
        IsShallowTopologicalMinor H G (r - 1) → H.edgeFinset.card ≤ d * Fintype.card W) :
      ∃ (ord : LinearOrder V), letI := ord; adm G r ≤ 1 + 6 * r * d ^ 3

(`AdmBoundByTopGrad/Full.lean:1456`), now at `r := r + 1`, where
`(r + 1) - 1` reduces to `r` definitionally: the catalog theorem and the
concept statement have the *same* content, so the bridge only has to
translate idioms. Quantifier map: `hd` is supplied from
`HasTopologicalDensityAtMost G r d` by repacking the catalog's
`ShallowTopologicalMinorModel` (edge-indexed routed paths, `Sym2`
plumbing) into the concept's pair-indexed walk model and back —
`walk u v h` for one orientation, its reverse for the other — and
transporting `H : SimpleGraph W` to `SimpleGraph (Fin (Fintype.card W))`.
The conclusion's `∃ ord` becomes the concept's `∃ π` in `HasAdmAtMost`
via `rankPerm`, and `adm G (r + 1)` (`sInf`) is then bounded by
`Nat.sInf_le`. The shallow-minor weakening that the P0 draft needed
(`shallowTopologicalMinor_toShallowMinor` plus depth monotonicity) is no
longer part of this discharge; it moves to the headline glue, which is
the only place that has to convert an ordinary-minor density bound into
a topological one.

#### `concepts/LaxS/StrongColoringBound.lean`

```lean
import LaxS.Admissibility
import LaxS.ColoringNumbers

/-!
---
title: Strong coloring numbers are bounded by admissibility
type: theorem
---
The strong *r*-coloring number of a graph is at most
1 + (adm_r − 1)^*r*, where adm_r is its *r*-admissibility. Together with
the trivial bound adm_r ≤ scol_r this says that admissibility and the
strong coloring number are functionally equivalent parameters.

# Formalization notes

Both parameters are the minima over vertex orderings defined in the
imported concepts, and the statement is the minimized form: the
literature proves it for each ordering separately, and the minimized
form follows because the right-hand side is monotone in adm_r, so an
ordering optimal for admissibility witnesses the bound. Natural
subtraction `adm_r − 1` is harmless: admissibility counts the vertex
itself, so it is at least 1 on every nonempty graph, and on the empty
graph both sides degenerate to a true inequality.
-/

namespace LaxS.StrongColoringBound

open LaxS.Admissibility LaxS.ColoringNumbers

/-- The strong `r`-coloring number is at most `1 + (adm_r - 1) ^ r`. -/
axiom scol_le_of_adm {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    scol G r ≤ 1 + (adm G r - 1) ^ r

end LaxS.StrongColoringBound
```

Discharged by

    scol_le_one_add_adm_sub_one_pow {V : Type*} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) (r : ℕ) : scol G r ≤ 1 + (adm G r - 1) ^ r

(`StrongColoringBoundByAdm/Full.lean:760`), which is the same inequality
per ordering. Quantifier map: let `k := adm G r` and pick the witnessing
`π` of `HasAdmAtMost G r k`; the `LinearOrder` is `LinearOrder.lift' π`.
Catalog admissibility under that order is `≤ k` because a catalog
path-family is a concept walk-family, and concept `scol` is `≤` catalog
`scol` under that order because a catalog `SReach` element is reached by
a path, hence by a walk (`Nat.sInf_le` with `π` as the witness).

#### `concepts/LaxS/WeakColoringBound.lean`

```lean
import LaxS.ColoringNumbers

/-!
---
title: Weak coloring numbers are bounded by strong coloring numbers
type: theorem
---
The weak *r*-coloring number of a graph is at most
1 + *r* · (scol_r − 1)^*r*, where scol_r is its strong *r*-coloring
number. With the trivial bound scol_r ≤ wcol_r this says that the two
generalized coloring numbers are functionally equivalent parameters.

# Formalization notes

Both parameters are the minima over vertex orderings defined in the
imported concept, and the statement is the minimized form: the
literature proves it for each ordering separately, and the minimized
form follows because the right-hand side is monotone in scol_r, so an
ordering optimal for the strong coloring number witnesses the bound. The
proof idea is that a weakly reachable vertex is found by a bounded
search tree of strongly reachable vertices, of depth *r* and branching
scol_r − 1. Natural subtraction is harmless: strong coloring numbers
count the vertex itself, so they are at least 1 on every nonempty graph.
-/

namespace LaxS.WeakColoringBound

open LaxS.ColoringNumbers

/-- The weak `r`-coloring number is at most `1 + r · (scol_r - 1) ^ r`. -/
axiom wcol_le_of_scol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    wcol G r ≤ 1 + r * (scol G r - 1) ^ r

end LaxS.WeakColoringBound
```

Discharged by

    wcol_le_of_scol {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (r : ℕ) :
      wcol G r ≤ 1 + r * (scol G r - 1) ^ r

(`ColoringNumberOrdering/Full.lean:395`), same inequality per ordering.
Quantifier map: pick `π` witnessing `scol G r`, order by
`LinearOrder.lift' π`; catalog `scol` under it is `≤` concept `scol`
(`SReach ⊆ sreach`), and concept `wcol` is `≤` catalog `wcol` under it
(`wreach ⊆ WReach`, the existing `wreach_subset_WReach`).

#### `concepts/LaxS/NowhereDenseWcol.lean`

Textually the Lax5 concept of the same name, over the LaxS definitions.

```lean
import LaxS.NowhereDenseClasses
import LaxS.ColoringNumbers

/-!
---
title: Nowhere dense classes have subpolynomial weak coloring numbers
type: theorem
---
Every nowhere dense graph class has subpolynomial weak coloring
numbers: for every radius *r* and every ε > 0 there is a constant *c*
such that every subgraph *H* of a member, on *m* vertices, satisfies
wcol_r(*H*) ≤ *c* · *m*^ε.

# Formalization notes

The hypothesis is the shallow-minor definition of the nowhere dense
concept; the conclusion is the shared predicate `HasSubpolynomialWcol`
of the coloring-number concept. Since nowhere denseness survives taking
subgraphs, the uniformity of that predicate over subgraph copies of
members loses nothing here. This is the headline of the submission and
is the composition of the four preceding theorem concepts: subpolynomial
shallow-minor density, the admissibility bound, and the two links of the
coloring-number chain.
-/

namespace LaxS.NowhereDenseWcol

open LaxS.GraphClasses LaxS.NowhereDenseClasses LaxS.ColoringNumbers

/-- Nowhere dense graph classes have subpolynomial weak coloring
numbers. -/
axiom hasSubpolynomialWcol_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    HasSubpolynomialWcol C

end LaxS.NowhereDenseWcol
```

#### Verification of the composition

`NDSubpolynomialWcol/Full.lean` (182 lines) is exactly the glue we
reproduce; step by step, with the LaxS glue on the right.

| catalog step | LaxS glue |
| --- | --- |
| `ε₁ := ε / (3·r² + 1)` | same |
| `obtain ⟨N, hN⟩ := nd_subpolynomial_density C hC (r-1) ε₁` | `obtain ⟨c₁, hc₁⟩ := hasSubpolynomialDensity_of_nowhereDense (subgraphClosure C) _ r ε₁`; set `c₁' := max c₁ 0` |
| `d := ⌈n^ε₁⌉₊ + N` | `d := ⌈c₁' * (m:ℝ)^ε₁⌉₊` |
| `hd_bound` by case split on `N ≤ m` (large: density bound, `card_le_of_isShallowTopologicalMinor`; small: `edges ≤ m²`) | one case: `edges K ≤ c₁' · k^(1+ε₁) = c₁' · k · k^ε₁ ≤ c₁' · k · m^ε₁ ≤ d · k`, using `k ≤ m` for shallow minors. The threshold case split disappears with the constant-form density predicate |
| `obtain ⟨ord, hadm⟩ := adm_le_of_topGrad_bound G r d hd_bound` | `have hadm := adm_le_of_hasTopologicalDensityAtMost H r d hd_top` (no ordering escapes; `adm` is already the minimum), where `hd_top : HasTopologicalDensityAtMost H r d` comes from `hd_bound : HasDensityAtMost H r d` by the axiom-free helper "a depth-`r` topological minor is a depth-`r` minor" (`MinorBridge`, P1.5); the conclusion arrives at radius `r + 1`, and `adm H r ≤ adm H (r + 1)` — every admissible family at radius `r` is one at radius `r + 1` — brings it back to the radius the headline needs, avoiding a case split on `r = 0` |
| `hwcol := wcol_le_of_adm G r` | `scol_le_of_adm H r` then `wcol_le_of_scol H r`, composed by the same three lines that `ColoringNumberEquivalence.wcol_le_of_adm` runs: `hsub : scol - 1 ≤ (adm - 1)^r` by `Nat.sub_le_iff_le_add`, then `Nat.pow_le_pow_left` and `← Nat.pow_mul` |
| `hnat_bound : wcol ≤ 1 + r·(6·r·d³)^(r²)` | identical |
| `hd_le : d ≤ (N+2)·n^ε₁`, `hexp : ε₁·3r² ≤ ε`, `hd_pow`, `hrpow_le`, final `calc` | identical with `(c₁' + 1)` in place of `(N + 2)` and `m` in place of `n`; `n = 0` case becomes `m = 0`, where `wcol H r = 0` |

Nothing else is used. `subgraphClosure` nowhere-denseness and
`k ≤ m` for shallow minors are axiom-free helpers, so the computed
assumption set is exactly the four statements listed above.

### (b) Proof-package module map

The `X/Full.lean` layout is dropped; `LaxSProofs/` is flat, like
`Lax5Proofs/`. Namespaces are `LaxSProofs.<ModuleName>`.

**Ported source** (the `{V : Type}` + instances idiom, kept intact —
these files are where the ugliness lives).

| old | new | adaptation |
| --- | --- | --- |
| `Preliminaries/Full.lean` (10) | `LaxSProofs/ShallowMinors.lean` | merged; pure rename |
| `ShallowMinor/Full.lean` (30) | `LaxSProofs/ShallowMinors.lean` | merged; pure rename |
| `NowhereDense/Full.lean` (22) | `LaxSProofs/ShallowMinors.lean` | merged; pure rename |
| `ShallowMinorComposition/Full.lean` (183) | `LaxSProofs/ShallowMinors.lean` | merged; pure rename (`ShallowReduct`, `shallowMinor_trans`, `nowhereDense_shallowReduct`) |
| `ShallowTopologicalMinor/Full.lean` (401) | `LaxSProofs/TopologicalMinors.lean` | pure rename; still needed by `BipartiteRamsey` and by the admissibility bound |
| `ColoringNumbers/Full.lean` (35) | `LaxSProofs/OrderedParameters.lean` | merged; pure rename |
| `Admissibility/Full.lean` (33) | `LaxSProofs/OrderedParameters.lean` | merged; pure rename |
| `ColoringNumberOrdering/Full.lean` (406) | `LaxSProofs/OrderedParameterBounds.lean` | pure rename (`adm_le_scol`, `scol_le_wcol`, `wcol_le_of_scol`) |
| `StrongColoringBoundByAdm/TreeCounting.lean` (310) | `LaxSProofs/TreeCounting.lean` | pure rename; nothing graph-theoretic in it |
| `StrongColoringBoundByAdm/Full.lean` (773) | `LaxSProofs/ScolByAdm.lean` | pure rename |
| `ColoringNumberEquivalence/Full.lean` (36) | *deleted* | its content is the arithmetic of the headline glue proof, which now runs at the concept level |
| `AdmBoundByTopGrad/Full.lean` (1470) | `LaxSProofs/AdmByDensity.lean` | pure rename |
| `ChernoffBound/Full.lean` (327) | `LaxSProofs/ChernoffBound.lean` | pure rename |
| `Densification/Full.lean` (937) | `LaxSProofs/Densification.lean` | pure rename |
| `NDSubpolynomialDensity/Full.lean` (980) | `LaxSProofs/DensityOfShallowMinors.lean` | pure rename |
| `UniformQuasiWideness/Full.lean` (35) | `LaxSProofs/StepReduction.lean` | merged; **real work, small**: `DistIndependent`/`deleteVerts` are deleted here and taken from the concept `LaxS.UniformQuasiWideness` instead (they are already polymorphic there); only the `{V : Type}`-indexed `UniformlyQuasiWide` predicate survives, under a name like `IsUniformlyQuasiWide` |
| `OddStepReduction/Full.lean` (128) | `LaxSProofs/StepReduction.lean` | merged; pure rename modulo the `DistIndependent` retarget |
| `EvenStepReduction/Full.lean` (237) | `LaxSProofs/StepReduction.lean` | merged; pure rename modulo the retarget |
| `NDImpliesUQW/Full.lean` (514) | `LaxSProofs/QuasiWidenessInduction.lean` | pure rename plus Ramsey import retarget (see (c)) |
| `NDSubpolynomialWcol/Full.lean` (182) | *deleted* | replaced by the archive-visible glue proof `LaxSProofs/NowhereDenseWcol.lean` |

Two `Lax5Proofs` files are copied wholesale into LaxS (see (c)):
`LaxSProofs/Ramsey.lean`, `LaxSProofs/BipartiteRamsey.lean`.

**New: LaxS-internal bridges** (ported idiom ↔ LaxS concept surface).
This is where today's Lax5 bridge code lands, retargeted.

- `LaxSProofs/MinorBridge.lean` — seeded by the shallow-minor halves of
  `Lax5Proofs/QuasiWideness.lean` and `Lax5Proofs/NowhereDenseWcol.lean`:
  - `copyClosure` / `subgraphClosure` (`fun H => ∃ n G, C n G ∧ H ⊑ G`) —
    from `QuasiWideness.copyClosure` and `NowhereDenseWcol.copyClosure`
    (currently duplicated in three Lax5 files; one copy in LaxS);
  - `isShallowMinor_of_copy` — from `QuasiWideness`, verbatim;
  - `shallowMinorModel_of_isShallowMinor` (catalog ⇒ concept, paths are
    walks) — from `QuasiWideness`, verbatim;
  - `isShallowMinor_of_shallowMinorModel` (concept ⇒ catalog, via
    `Walk.bypass`) — from `Corollary6a`, verbatim;
  - `isNowhereDense_copyClosure_of_nowhereDense` and its `Fin (t+1)` vs
    `Fin t` index shuffling — from `QuasiWideness` and
    `NowhereDenseWcol.copyClosure_isNowhereDense` (the two existing
    versions differ only in which clique index they cast; keep one);
  - **new**: canonicalization `SimpleGraph W ≃g SimpleGraph (Fin (Fintype.card W))`
    for shallow minors, so `HasDensityAtMost` (over `Fin m`) and the
    catalog hypotheses (over `{W : Type}`) convert both ways;
  - **new**: `H.edgeSet.ncard = H.edgeFinset.card` under `Classical.decRel`;
  - **new**: `|V(H)| ≤ |V(G)|` for shallow minors (branch sets are
    disjoint and nonempty), replacing the catalog's
    `card_le_of_isShallowTopologicalMinor`;
  - **new**: `nowhereDense_subgraphClosure` at the concept level, for the
    glue proof;
  - **new (P1.5)**: `hasTopologicalDensityAtMost_of_hasDensityAtMost` —
    a depth-`r` topological minor is a depth-`r` minor (take as branch
    sets the principal vertices together with the interiors of the
    connecting walks; radius at most `r` because a walk of length at
    most `2r+1` splits into two halves of length at most `r`), so an
    ordinary-minor density bound yields the topological one. Axiom-free,
    consumed by the headline glue — this is the P1.5 replacement for the
    weakening that used to sit inside the admissibility concept;
  - **new (P1.5)**: the two-way repacking of the concept's pair-indexed
    `ShallowTopologicalMinorModel` against the catalog's edge-indexed
    one (`Sym2.Mem.other`, `edgeTail`), for the admissibility discharge.
- `LaxSProofs/OrderBridge.lean` — seeded by the ordering half of
  `Lax5Proofs/NowhereDenseWcol.lean`:
  - `OrderedCopy`, `orderedCopyEquiv`, `rankPerm` — verbatim;
  - `wreach_subset_WReach` and `submitted_wcol_le_catalog` — verbatim,
    renamed;
  - **new**: the converse direction `orderOfPerm π := LinearOrder.lift' π`,
    under which `π x ≤ π y ↔ x ≤ y` definitionally;
  - **new**: `sreach` siblings — `sreach_subset_SReach` (walk ⇒ bypass to
    path) and `SReach_subset_sreach` (paths are walks) — and the
    corresponding `scol` inequalities;
  - **new**: `AdmFamily ↔ IsAdmFamily` both ways (bypass in one
    direction, inclusion in the other) and the resulting
    `adm`-vs-`admVertex`/`adm` inequalities, including `j < Fintype.card V`
    so that the catalog's `Finset.sup (range (card V))` sees the family;
  - **new (P1.5)**: `adm G r ≤ adm G (r + 1)` — an admissible family at
    radius `r` is one at radius `r + 1`, so `HasAdmAtMost` is
    antitone in the radius — used by the glue to consume the
    index-shifted admissibility bound at every radius.

**New: frontmattered proofs** (one per statement).

- `LaxSProofs/NowhereDenseUQW.lean` → `LaxS.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense`.
  Body: today's `Lax5Proofs/QuasiWideness.uqw_of_nowhereDense`, with the
  `Finset`→`Set` repackaging added.
- `LaxSProofs/NowhereDenseDensity.lean` → `…hasSubpolynomialDensity_of_nowhereDense`.
  Body: new (threshold→constant, carrier canonicalization).
- `LaxSProofs/AdmissibilityBound.lean` →
  `…adm_le_of_hasTopologicalDensityAtMost`. Body: near-verbatim
  `adm_le_of_topGrad_bound` at `r := r + 1` — model repacking,
  `rankPerm`, `Nat.sInf_le`; no weakening step any more.
- `LaxSProofs/StrongColoringBound.lean` → `…scol_le_of_adm`.
- `LaxSProofs/WeakColoringBound.lean` → `…wcol_le_of_scol`.
- `LaxSProofs/NowhereDenseWcol.lean` → `…hasSubpolynomialWcol_of_nowhereDense`,
  the glue with the four `assumptions:`. Body: the table above; imports
  only the five concept modules and `MinorBridge`, no ported source at
  all — that is the point of the exercise.

Root module `LaxSProofs.lean` imports all of the above.

### (c) Ramsey copy list

`NDImpliesUQW/Full.lean` uses exactly two identifiers from the two Lax5
proof modules:

- `Lax5Proofs.Ramsey.ramsey` (line 339, 349) — two-colour Ramsey;
- `Lax5Proofs.BipartiteRamsey.iterated_bipartite_ramsey` (line 382, 414)
  — Lemma 3.10.

Nothing else. Their dependency closure inside those two files, however, is
everything both files contain:

- `Ramsey.lean` (239 lines): `ramsey` uses `compl_induce_eq` (lines 87,
  136); `multicolor_ramsey` uses `ramsey`; `bipartite_ramsey` uses
  `multicolor_ramsey`. All three public declarations are in the closure.
- `BipartiteRamsey.lean` (737 lines): `iterated_bipartite_ramsey` → `R_star`,
  `iterStep`; `iterStep` → `bipartite_ramsey`,
  `topologicalMinorModel_of_subgraph`; `bipartite_ramsey` →
  `Ramsey.multicolor_ramsey` and the private colouring helpers
  (`localNeighborPair`, `localPairCodeBound`, `localPairCode`,
  `localNeighborPair_symm`, `localPairCode_symm`, `localPairCode_injective`,
  `commonNeighborCodes`, `mem_commonNeighborCodes`,
  `commonNeighborCodes_symm`, `edgeColor`, `edgeColor_symm`,
  `exists_commonNeighbor_of_edgeColor_eq`). Every declaration in the file
  is in the closure.

**Minimal copy list = both files, verbatim.** Nothing can be dropped.
Concretely:

- `Lax5Proofs/Ramsey.lean` → `LaxSProofs/Ramsey.lean`, namespace
  `Lax5Proofs.Ramsey` → `LaxSProofs.Ramsey`; imports unchanged
  (mathlib only).
- `Lax5Proofs/BipartiteRamsey.lean` → `LaxSProofs/BipartiteRamsey.lean`,
  namespace `Lax5Proofs.BipartiteRamsey` → `LaxSProofs.BipartiteRamsey`;
  `import Lax5Proofs.Ramsey` → `import LaxSProofs.Ramsey`, and
  `import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor.Full`
  → `import LaxSProofs.TopologicalMinors` with the matching `open`.

LaxS requires no Lax5 package of any kind; the copies are the reason it
does not have to.

Side effect for Lax5: `Lax5Proofs/BipartiteRamsey.lean`'s only consumer in
Lax5 was `NDImpliesUQW/Full.lean`, so after the reroute it is dead code —
see (d). `Lax5Proofs/Ramsey.lean` stays: `NowhereDenseBridge.lean` uses
`Ramsey.multicolor_ramsey`.

### (d) Lax5 diff list

#### Deletions

- `proofs/Lax5Proofs/Source/` — the entire tree, 21 files, ~7.0k lines.
- `proofs/Lax5Proofs/BipartiteRamsey.lean` (737 lines) — sole consumer was
  the deleted `NDImpliesUQW/Full.lean`; verified by grep, nothing else in
  `Lax5Proofs` mentions `BipartiteRamsey` (`TupleRamsey.lean:520` is an
  unrelated comment).

#### New files

- `proofs/Lax5Proofs/ShallowMinors.lean` (~62 lines) — verbatim re-home of
  the catalog `Preliminaries`, `ShallowMinor` and `NowhereDense` modules
  under `Lax5Proofs.ShallowMinors`. Needed because `NowhereDenseBridge`
  and `Corollary6a` are stated over the *polymorphic* graph classes and
  the path-based minor model; retargeting them to LaxS concepts would mean
  rewriting a 1442-line file for zero gain.
- `proofs/Lax5Proofs/TopologicalMinors.lean` (~401 lines) — verbatim
  re-home of the catalog `ShallowTopologicalMinor` module. `NowhereDenseBridge`
  builds a `ShallowTopologicalMinorModel` at line 287 and calls
  `shallowTopologicalMinor_toShallowMinor` at line 387, which pulls in the
  file's private routing helpers.

This is the resolution of the "`BipartiteRamsey.lean`'s use of catalog
`ShallowTopologicalMinor`" question in the plan, and it is aligned with
decision (1): the file leaves Lax5 entirely, so there is nothing to
retarget there; the remaining Lax5 consumer of topological minors is
`NowhereDenseBridge`, served by a local copy of the catalog development
rather than by the LaxS concept. That is unchanged by the P1.5 reversal of
decision (1): the LaxS concept exists on the endorsement surface, but
`NowhereDenseBridge` is a 1442-line proof stated in the catalog idiom and
has no reason to be retargeted to it.

#### `proofs/lakefile.toml`

Add, after the mathlib require:

```toml
[[require]]
name = "LaxS"
git = "https://github.com/lax-archive/lax-submissions"
rev = "<LaxS draft commit>"
subDir = "sparsity-lectures/concepts"
```

`lax pull-db` first; the triple must equal LaxS's current record verbatim.

#### `proofs/Lax5Proofs.lean`

Drop the 20 `Source.Catalog…` imports and `import Lax5Proofs.BipartiteRamsey`;
add `import Lax5Proofs.ShallowMinors` and `import Lax5Proofs.TopologicalMinors`.

#### `proofs/Lax5Proofs/NowhereDenseBridge.lean`

Import/`open` retarget only, no proof changes:
`Lax5Proofs.Source.Catalog.SparsityLectures.{Preliminaries,NowhereDense,ShallowMinor}`
→ `Lax5Proofs.ShallowMinors`, `….ShallowTopologicalMinor` →
`Lax5Proofs.TopologicalMinors`. Keeps `import Lax5Proofs.Ramsey`. No
`assumptions:` (it declares no proof; `isLocallyNowhereDense_iff_isNowhereDense`
is a helper).

#### `proofs/Lax5Proofs/Corollary6a.lean`

Import/`open` retarget as above. **No `assumptions:`.** Audit result: its
proof of `Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent`
composes `NowhereDenseBridge`, `SubdividedBicliqueRamsey` and
`CrossingTransduction`, none of which is a proved Lax5 concept statement —
this is a from-scratch proof and stays one.

#### `proofs/Lax5Proofs/QuasiWideness.lean`

Rewritten, ~40 lines, no frontmatter (helper). **Moves to LaxS:**
`copyClosure`, `isShallowMinor_of_copy`,
`shallowMinorModel_of_isShallowMinor`,
`isNowhereDense_copyClosure_of_nowhereDense` — the whole catalog-facing
half. **Stays in Lax5:** `uqw_of_nowhereDense`, restated as a transport of
`LaxS.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense`:

- repack `Lax5.NowhereDenseClasses.ShallowMinorModel` ↔
  `LaxS.NowhereDenseClasses.ShallowMinorModel` field for field (identical
  fields, nominally distinct structures — ~15 lines, both directions);
- convert the concept's `Set`/`ncard` witnesses into the `Finset`/`card`
  shape `AdlerAdler.lean` consumes (`Set.toFinset`, `Set.ncard_coe_finset`);
- `LaxS.UniformQuasiWideness.DistIndependent` and `deleteVerts` are plain
  defs, so `AdlerAdler`'s uses need only the changed `open`.

New import: `LaxS.NowhereDenseUQW` (and `LaxS.UniformQuasiWideness`).
Dropped: `Lax5Proofs.Source.Catalog….NDImpliesUQW.Full`.

#### `proofs/Lax5Proofs/AdlerAdler.lean`

`import Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness.Full`
→ `import LaxS.UniformQuasiWideness`; `open …UniformQuasiWideness` →
`open LaxS.UniformQuasiWideness`. Add frontmatter:

```yaml
conclusion: Lax5.AdlerAdler.monadicallyDependent_of_nowhereDense
assumptions:
  - LaxS.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense
```

and a sentence in `# Proof strategy` saying uniform quasi-wideness is now
assumed from LaxS rather than reproved.

#### `proofs/Lax5Proofs/NowhereDenseWcol.lean`

Rewritten, ~35 lines. **Moves to LaxS:** `copyClosure`,
`copyClosure_isNowhereDense`, `OrderedCopy`, `orderedCopyEquiv`,
`rankPerm`, `wreach_subset_WReach`, `submitted_wcol_le_catalog` — i.e.
everything except the frontmattered theorem. **Stays in Lax5:** the
theorem, now

```yaml
conclusion: Lax5.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense
assumptions:
  - LaxS.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense
```

with body: transport `Lax5.NowhereDenseClasses.NowhereDense C` to
`LaxS.NowhereDenseClasses.NowhereDense C` by the shallow-minor-model
repacking (shared with `QuasiWideness.lean`, so put the repacking in one
of the two and import it), apply the LaxS statement, and convert
`LaxS.ColoringNumbers.HasSubpolynomialWcol C` to
`Lax5.WeakColoring.HasSubpolynomialWcol C` — the two unfold to the same
term (`wreach` and `wcol` are byte-identical definitions), so this is
`rfl` modulo the `GraphClass` abbrev, which is literally the same type.

#### `proofs/Lax5Proofs/Corollary6b.lean`

`import Lax5Proofs.NowhereDenseWcol` → `import Lax5.NowhereDenseWcol`; the
call `Lax5Proofs.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense C h 2 δ hδ`
(line ~92) becomes `Lax5.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense C h 2 δ hδ`.
Add to its frontmatter:

```yaml
assumptions:
  - Lax5.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense
```

Audit result: this is the clearest internal-network case — a proof of one
Lax5 statement literally importing the proof of another.

#### `proofs/Lax5Proofs/Corollary6.lean`

Rewired to compose the two *statements* instead of importing the two
proofs: `import Lax5Proofs.Corollary6a` / `Corollary6b` →
`import Lax5.WeaklySparseDependent` / `import Lax5.NowhereDenseNC`, body

```lean
theorem hasAlmostLinearNC_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    HasAlmostLinearNC C :=
  Lax5.NowhereDenseNC.hasAlmostLinearNC_of_nowhereDense C
    (Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent C hs hd)
```

Still a helper (no frontmatter — the archive has no concept for this
composition); the visible effect is on `Theorem2`.

#### `proofs/Lax5Proofs/Theorem2.lean`

No proof change. Audit result: today `Theorem2 → Lemma21 → SparsGraphs →
Corollary6 → {Corollary6a, Corollary6b}`, so the proof of the headline
statement *contains* the proofs of two other Lax5 statements. After the
`Corollary6.lean` rewiring its axiom set becomes exactly those two
statements, so add:

```yaml
conclusion: Lax5.AlmostLinearNC.hasAlmostLinearNC_of_monadicallyDependent
assumptions:
  - Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent
  - Lax5.NowhereDenseNC.hasAlmostLinearNC_of_nowhereDense
```

(`assumptions` must *equal* the computed set — P4 confirms against
`lax build` output before committing; `Lemma21.lean`, `SparsGraphs.lean`
and everything below them are helpers and contribute nothing else.)

Resulting Lax5 proof network, previously invisible:

    LaxS.NowhereDenseUQW.uqw_of_nd ──▶ Lax5.AdlerAdler.md_of_nd
    LaxS.NowhereDenseWcol.wcol_of_nd ─▶ Lax5.NowhereDenseWcol.wcol_of_nd
                                        └─▶ Lax5.NowhereDenseNC.nc_of_nd ─┐
    Lax5.WeaklySparseDependent.nd_of_ws_md ──────────────────────────────┴─▶ Lax5.AlmostLinearNC.nc_of_md

#### `abstract.md`, `manifest.yaml`

- `abstract.md`: the proof-provenance paragraph now says that the
  coloring-number and quasi-wideness inputs are *assumed* from the
  sparsity-lectures submission rather than contained, and that the
  submission's own network makes the Corollary-6 composition visible. Note
  the deliberate nominal duplication of the shallow-minor and
  weak-coloring definitions across the two submissions and that the
  transport is definitional.
- `manifest.yaml`: optionally add a bibEntry for the Pilipczuk–Pilipczuk–Siebertz
  lecture notes, which are now an external dependency rather than vendored
  source. No other key changes (`id`, pins, authors unchanged).

#### Order of operations

`lake build` in `proofs/` against the pushed LaxS commit throughout;
`lax build monadic-dependence-neighborhood-complexity --replay` at the
end; resubmit as draft. Lax1 and Lax2 are untouched — nothing pins Lax5.

### (e) Open questions for Jan

- **Sharpness of the admissibility statement.** ~~LaxS states
  `HasDensityAtMost G r d → adm G r ≤ 1 + 6·r·d³`; the source proves the
  sharper `∇̃_{r-1}`-topological form.~~ **Answered by Jan ("use that
  form") and executed in P1.5:** the sharp topological form is what the
  surface states, over a new definition-concept
  `ShallowTopologicalMinors` whose model has six fields and no `Sym2`
  plumbing, with the radius index shifted by one to avoid truncated
  subtraction.
- **Should `adm_r ≤ scol_r ≤ wcol_r` (Prop. 2.4) get concepts?** Both are
  already proved in `ColoringNumberOrdering/Full.lean` and would be two
  cheap theorem-concepts completing the "functionally equivalent
  parameters" story. Recommendation: no — nothing in the submission
  consumes them, and each is an extra endorsement unit for a triviality.
  Cheap to add later in a separate submission.
- **`wcol` and `scol` in one concept or two?** They share a module here
  (`LaxS/ColoringNumbers.lean`, "Generalized coloring numbers"), which
  breaks exact module-level mirroring of `Lax5/WeakColoring.lean` though
  the individual declarations stay byte-identical. Recommendation: one
  module — the two differ in a single clause and every statement about
  them is about the contrast.
- **Title and scope of the submission.** "Sparsity lectures" is a source
  name, not a result name. Recommendation: title it after the content,
  e.g. *Nowhere Dense Classes: Quasi-Wideness, Density, and Generalized
  Coloring Numbers*, and keep `sparsity-lectures/` as the directory.
- **Should the headline glue also expose a `nd ⇒ UQW`-side headline?**
  LaxS currently has two independent headlines (UQW and subpolynomial
  wcol) with no statement joining them. Recommendation: leave it — they
  are genuinely separate results of the notes, and inventing a
  conjunction would violate the no-`∧` rule.

### P1 log

**Allocated id: `Lax12`** (`lax init sparsity-lectures`, CLI 0.1.8). Every
`LaxS` of the design is `Lax12`, every `LaxSProofs` is `Lax12Proofs`;
directory stays `sparsity-lectures/`.

Written: `concepts/Lax12/{GraphClasses, NowhereDenseClasses,
ShallowMinorDensity, ColoringNumbers, Admissibility, UniformQuasiWideness,
NowhereDenseUQW, NowhereDenseDensity, AdmissibilityBound,
StrongColoringBound, WeakColoringBound, NowhereDenseWcol}.lean`, root
`concepts/Lax12.lean` (twelve import lines, nothing else), `abstract.md`,
`manifest.yaml` (title as chosen by Jan's brief, one bibEntry for the
lecture notes, `authors: []` as scaffolded).

**Deviations from the design drafts: none.** Every module compiles exactly
as drafted in Design section (a), modulo the `LaxS` → `Lax12` rename. In
particular the `deleteVerts` `loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩`
term is correct as drafted (`SimpleGraph.loopless` has type `Std.Irrefl Adj`
at this pin, a class with an `irrefl` field — not a bare `Irreflexive`, so
the anonymous constructor is required and `G.loopless v h.1` does *not*
typecheck). No import path needed adjusting; no statement, docstring or
name was touched.

Verified textual identity against Lax5, as required for the P4 transport:

- `Lax5/NowhereDenseClasses.lean` vs `Lax12/NowhereDenseClasses.lean`:
  `diff` after `s/Lax5/Lax12/g` is empty — identical file.
- `wreach`, `wcol`, `HasSubpolynomialWcol` in `Lax12/ColoringNumbers.lean`
  are byte-identical (docstring included) to their `Lax5/WeakColoring.lean`
  counterparts; `GraphClass` is the same `abbrev`, so the transport is
  definitional.
- `Lax12.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense` has the
  same shape as the Lax5 axiom of the same name.

Build status: `lake build` in `sparsity-lectures/concepts/` green (2005
jobs); `lax build sparsity-lectures` green end to end — no rule violations
reported (the proof package is still the empty scaffold). Self-check: zero
`sorry`, zero `Classical`, zero theorems/lemmas/examples in the concept
package; one `axiom` in each of the six theorem-concepts, zero in each of
the six definition-concepts; `title`/`type` frontmatter and a
`# Formalization notes` section in all twelve module docstrings; every
declaration and structure field docstringed; `autoImplicit = false` from
the scaffold's lakefile.

Notes for P2:

- Package/lib names are `Lax12` and `Lax12Proofs`; `proofs/lakefile.toml`
  already requires `../concepts` by path.
- The concept-side names the glue proof must conclude/assume are
  `Lax12.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense` assuming
  `Lax12.NowhereDenseDensity.hasSubpolynomialDensity_of_nowhereDense`,
  `Lax12.AdmissibilityBound.adm_le_of_hasDensityAtMost`,
  `Lax12.StrongColoringBound.scol_le_of_adm`,
  `Lax12.WeakColoringBound.wcol_le_of_scol`.
- `Lax12.UniformQuasiWideness.{DistIndependent, deleteVerts}` are
  `{V : Type*}`-polymorphic `Set`-based defs, so the ported step-reduction
  modules can `open` them directly instead of carrying copies (design (b)).
- Nothing was committed; `git status` shows `sparsity-lectures/` untracked
  and Jan's unrelated WIP still unstaged.

### P1.5 log

Jan's directive "use that form" — measured against
`references/sparsity-lectures/form-check.md`, which checks every concept
against the actual notes — reverses P0 decision (1) and puts the
admissibility bound into the notes' Lemma 3.2 shape. Written:
`concepts/Lax12/ShallowTopologicalMinors.lean`, a seventh
definition-concept stating Definitions 2.15/2.16 of Chapter 1 (depth-*r*
topological minor as an injective choice of principal vertices plus
connecting walks of length at most `2r+1` that avoid all principal
vertices except their own endpoints and meet each other only in
principal vertices, plus the per-graph predicate
`HasTopologicalDensityAtMost`, zero axioms). Restated:
`AdmissibilityBound` now declares
`adm_le_of_hasTopologicalDensityAtMost : HasTopologicalDensityAtMost G r d → adm G (r+1) ≤ 1 + 6*(r+1)*d^3`,
verbatim the notes' `adm_r ≤ 1 + 6r⌈∇̃_{r−1}⌉³` at `r := r+1` and
verbatim the content of the catalog theorem `adm_le_of_topGrad_bound`,
so the P2 discharge is now idiom translation with no weakening step; the
weakening it used to perform (topological ⇒ ordinary minor) moves to the
headline glue as an axiom-free `MinorBridge` helper, alongside the
`adm G r ≤ adm G (r+1)` monotonicity the shifted index calls for.
Docstrings: attribution in `NowhereDenseDensity` no longer claims the
theorem for Nešetřil–Ossona de Mendez (the notes credit the presented
proof to Dvořák and state Theorem 3.1 of Chapter 1 in threshold form);
`NowhereDenseWcol` records that the notes' Theorem 3.4 of Chapter 2
quantifies over members only and why the subgraph-uniform form here is
equivalent; every concept corresponding to a numbered item of the notes
now cites that number, its chapter, and the 2019/20 edition. Consistency:
root module, `abstract.md` (thirteen review units, seven definitions, the
topological admissibility statement, the index shift), `manifest.yaml`
(bibEntry replaced by the form-check's, the 2019/20 edition with its
per-chapter compilation dates), and this plan's Design section (a), (b),
(d) and (e). Superseding the P1 log: the concept-side name the P2 glue
assumes is `Lax12.AdmissibilityBound.adm_le_of_hasTopologicalDensityAtMost`,
and the module docstrings of `NowhereDenseClasses` and `ColoringNumbers`
now carry an extra source-citation paragraph, so the files are no longer
byte-identical to their Lax5 counterparts — the *declarations*, on which
the P4 transport rests, still are.

Encoding call for the new concept: connecting walks are indexed by
adjacent pairs `(u, v)` rather than by `Sym2` edges, so both orientations
of an edge carry a walk; the disjointness field concludes that the two
edges agree, hence never fires on one edge's two orientations and forces
no relation between them, while for genuinely distinct edges it gives
exactly the notes' internal disjointness. Six fields, `Prop`-valued, no
`Sym2`, no `DecidableEq`/`Fintype`, walks rather than paths as everywhere
in this submission.

Build status: `lake build` in `sparsity-lectures/concepts/` green (2006
jobs, zero errors, zero warnings); `lax build sparsity-lectures` green
with no rule violations. Zero `sorry`, zero `Classical`, one axiom in
each of the six theorem-concepts, zero in each of the seven
definition-concepts. Nothing committed.
