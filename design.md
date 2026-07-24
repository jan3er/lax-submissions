# Statement design (step 2 deliverable, rev 3 — frozen)

Exact Lean forms for the concept surface of the flagship submission
(Theorem 2 of DMMPT26). Companion to `todo.md` and `pipeline.md`. All
design decisions are settled — the notes below state each design choice
as prose, and the decision record at the end keeps the ledger. Lean
snippets are final modulo step-3 polish.

Transductions are defined between classes of **arbitrary relational
structures** — one formula per relation symbol of the target language
plus a domain (selection) formula — and graph transductions are the
special case over mathlib's `Language.graph`. The symmetric-irreflexive
projection is absorbable (see concept 3's notes), so no projection
operator appears on the surface.

Everything below was checked against the pinned mathlib
(`c5ea00351c28e24afc9f0f84379aa41082b1188f`): `Language.graph` +
`SimpleGraph.structure` (ModelTheory/Graph), `Language.sum` with its
`sumStructure` instance (Basic.lean:734) and `isRelational_sum`,
`IsRelational` (`Language.graph` derives it), `Formula.Realize`
(free-variable type `Fin r`, valuation `![…]`), `IsContained`/`⊑` and
`completeBipartiteGraph` (Combinatorics/SimpleGraph/Copy, Basic),
`SimpleGraph.Walk`, `Set.ncard`, `Real.rpow`. There is no `Language.mk₂`
at the pin; the color language is a small custom inductive in the style
of mathlib's `graphRel`.

## Concept partition (10 concepts, 2 with open obligations)

    1  GraphClasses            (def)          —
    2  Transductions           (def)          —              [structures]
    3  GraphTransductions      (def)          imports 1, 2
    4  MonadicDependence       (def)          imports 1, 3
    5  NeighborhoodComplexity  (def)          imports 1
    6  NowhereDenseClasses     (def)          imports 1
    7  WeaklySparseDependent   (thm, OPEN)    imports 4, 6   [Cor 6a]
    8  NowhereDenseNC          (thm, proved)  imports 5, 6   [Cor 6b]
    9  AlmostLinearNC          (thm, proved)  imports 4, 5   [Thm 2]
    10 AdlerAdler              (thm, OPEN)    imports 4, 6   [converse]

The headline concept 9 imports only the definitions it mentions; its
*proof* additionally consumes the axioms of 7 and 8 (own-package
statements are legal axioms for the proof package, cf. `pipeline.md` §4).

## 1. GraphClasses (definition-concept)

A graph class is a set of finite simple graphs; members are taken on the
canonical vertex types `Fin n` (statements-over-canonical-types rule).

```lean
/-- A class of finite simple graphs: for each number of vertices, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

/-- The class of all finite simple graphs. -/
def allGraphs : GraphClass := fun _ _ => True
```

Pi-Prop rather than `Set (Σ n, SimpleGraph (Fin n))` (D1): membership
is direct application `C n G`; statements read `∀ n G, C n G → …` with
no sigma projections or `⟨n, G⟩ ∈ C` anonymous-constructor noise. We
lose `∈` notation only. The rejected broader alternatives are recorded
in the decision record.

`abbrev` (not `def`) so `C n G` needs no unfolding anywhere — same
rationale as `GraphParam` in Lax1. Iso-closure is deliberately *not*
required: none of the stated results needs it, and every quantifier
ranges over concrete members.

Only *class-level* quantification is pinned to the canonical `Fin n`;
*graph-level* definitions (`traceCount`, `ShallowMinorModel`,
`HasShallowMinor` in concepts 5–6) are stated over an arbitrary vertex
type, à la Lax1's generic `twinWidth`.

## 2. Transductions (definition-concept, on arbitrary structures)

Non-copying first-order transductions between classes of structures:
expand the input by finitely many unary color predicates, select the
output universe by a domain formula, and interpret each relation symbol
of the target language by a formula. This is the literature's
interpretation/transduction pipeline stated once, at its natural
generality; graphs are a special case (concept 3).

```lean
/-- A class of finite structures of the language `L`, one predicate per
canonical carrier `Fin n`. -/
abbrev StructureClass (L : FirstOrder.Language) : Type _ :=
  ∀ n : ℕ, L.Structure (Fin n) → Prop

/-- The relation symbols of the color language: `k` unary predicates. -/
inductive ColorRel (k : ℕ) : ℕ → Type
  | color (i : Fin k) : ColorRel k 1

/-- The language consisting of `k` unary color predicates. -/
def colorLanguage (k : ℕ) : FirstOrder.Language :=
  ⟨fun _ => Empty, ColorRel k⟩

/-- The language `L` expanded by `k` unary color predicates. -/
abbrev withColors (L : FirstOrder.Language) (k : ℕ) : FirstOrder.Language :=
  L.sum (colorLanguage k)

/-- Color sets as a structure of the color language. -/
def colorStructure {M : Type*} {k : ℕ} (colors : Fin k → Set M) :
    (colorLanguage k).Structure M where
  RelMap | .color i => fun x => x 0 ∈ colors i

/-- The formula `φ` of the colored language holds of the tuple `v` in the
structure `M` expanded by the color sets `colors`. -/
def RealizeIn {L : FirstOrder.Language} {n k : ℕ} (M : L.Structure (Fin n))
    (colors : Fin k → Set (Fin n)) {α : Type} (φ : (withColors L k).Formula α)
    (v : α → Fin n) : Prop :=
  letI := M; letI := colorStructure colors
  φ.Realize v

/-- A non-copying transduction from `L`-structures to `L'`-structures:
finitely many unary colors, a domain formula selecting the output
universe, and one formula per relation symbol of the target language. -/
structure Transduction (L L' : FirstOrder.Language) where
  /-- The number of unary color predicates. -/
  colors : ℕ
  /-- The formula selecting the elements of the output structure. -/
  domain : (withColors L colors).Formula (Fin 1)
  /-- The formula interpreting each relation symbol of the target. -/
  rel : ∀ {r : ℕ}, L'.Relations r → (withColors L colors).Formula (Fin r)

/-- `C` transduces `D`: a single transduction produces every member of
`D` from some colored member of `C`, up to isomorphism — the embedding
`f` identifies the output structure with the substructure of selected
elements. -/
def Transduces {L L' : FirstOrder.Language} [L'.IsRelational]
    (C : StructureClass L) (D : StructureClass L') : Prop :=
  ∃ T : Transduction L L',
    ∀ (m : ℕ) (N : L'.Structure (Fin m)), D m N →
      ∃ (n : ℕ) (M : L.Structure (Fin n)), C n M ∧
        ∃ (colors : Fin T.colors → Set (Fin n)) (f : Fin m ↪ Fin n),
          (∀ x : Fin n, x ∈ Set.range f ↔ RealizeIn M colors T.domain ![x]) ∧
          ∀ {r : ℕ} (R : L'.Relations r) (v : Fin r → Fin m),
            N.RelMap R v ↔ RealizeIn M colors (T.rel R) (f ∘ v)
```

Notes:

- **Selection semantics (D9).** The domain formula plus the condition
  `range f = {x | δ(x)}` is the standard interpretation shape. It is
  equivalent, as a relation on classes, to the
  arbitrary-induced-substructure convention of DMMPT26 §2: colors are
  existentially quantified, so an arbitrary subset is selected by a
  fresh color `c` with `δ := c(x)`. Formalization notes will state this.
- `[L'.IsRelational]` keeps the definition honest: a transduction only
  interprets relations, so target function symbols must not exist
  (rather than being silently unconstrained). The input language is
  unrestricted — formulas over `withColors L k` handle function symbols
  of `L` fine. `Language.graph` derives `IsRelational` in mathlib.
- Colors form a sum language (`L` is arbitrary, so a bespoke combined
  language is not an option): relation symbols of the expansion are
  `Sum.inl R` / `Sum.inr (.color i)`. This wrapping appears only when
  *writing concrete formulas*, i.e. in the proof package, where local
  abbreviations will hide it.
- The `letI` plumbing (mathlib wants structures as instances for
  `Formula.Realize`; ours are data) is confined to `RealizeIn`.
- `Transduction` is a bundled structure so the proof-package calculus
  (composition, color-guessing, …) can name and manipulate
  transductions as objects.

## 3. GraphTransductions (definition-concept)

Graphs are structures of mathlib's `Language.graph`; graph transductions
are structure transductions between the induced structure classes.

```lean
/-- The members of a graph class, as structures of the language of
graphs (via mathlib's `SimpleGraph.structure`). -/
def structureClass (C : GraphClass) : StructureClass FirstOrder.Language.graph :=
  fun n S => ∃ G : SimpleGraph (Fin n), C n G ∧ S = G.structure

/-- `C` transduces `D` as graph classes: the corresponding classes of
graph structures are related by a first-order transduction. -/
def Transduces (C D : GraphClass) : Prop :=
  Transductions.Transduces (structureClass C) (structureClass D)
```

Notes:

- **The symmetric-irreflexive projection is absorbed.** The target
  structures here are honest graph structures, so the interpreting
  formula must define adjacency *exactly*. This is equivalent to the
  usual "interpret by any `φ`, then project onto symmetric irreflexive"
  convention: replace `φ` by its symmetrization
  `x ≠ y ∧ φ(x, y) ∧ φ(y, x)`, which is again a formula. No projection
  operator on the surface; the formalization notes carry the argument,
  and no edge-convention choice is left to make.
- `structureClass` matches members up to equality of structures on the
  same carrier, which up to the embedding `f` in `Transduces` is
  exactly "isomorphic to".
- **Separate concept (D8).** Not folded into `MonadicDependence`:
  "graph classes transduce each other" is reviewable and reusable
  independently of dependence (monadic stability, ordered graphs, … in
  follow-ups).

## 4. MonadicDependence (definition-concept)

Paper §2 definition: a class is monadically dependent iff it does not
transduce the class of all graphs.

```lean
/-- A graph class is monadically dependent if it does not transduce the
class of all finite simple graphs. -/
def MonadicallyDependent (C : GraphClass) : Prop :=
  ¬ GraphTransductions.Transduces C allGraphs
```

One line over concepts 1–3; the reviewable content is that this *is* the
literature's definition (todo.md decision A).

## 5. NeighborhoodComplexity (definition-concept)

```lean
/-- The number of distinct neighborhood traces `N(v) ∩ A` that vertices
of `G` leave on the set `A`. -/
noncomputable def traceCount {V : Type} (G : SimpleGraph V)
    (A : Set V) : ℕ :=
  {S : Set V | ∃ v : V, S = G.neighborSet v ∩ A}.ncard

/-- Every graph in the class leaves at most `c · |A|^(1+ε)` neighborhood
traces on every nonempty vertex subset `A`, where `c` depends only on
`ε > 0`: neighborhood complexity `|A|^(1+o(1))`. -/
def HasAlmostLinearNC (C : GraphClass) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Set (Fin n), A.Nonempty →
        (traceCount G A : ℝ) ≤ c * (A.ncard : ℝ) ^ (1 + ε)
```

Notes:

- **Degenerate `A` (D2).** `A.Nonempty` hypothesis (not `(|A|+1)`
  padding). Only `A = ∅` breaks the literal inequality (`0^(1+ε) = 0`
  while the empty set always has the single trace `∅`); `|A| = 1` is
  already fine. Nonempty is the honest paper-level convention, and no
  content is lost: the empty set has exactly one trace. Formalization
  notes will say precisely this.
- **Sets, not Finsets (D2').** `A : Set` with `Set.ncard` avoids
  `DecidableRel G.Adj` / `filter` plumbing entirely (class members live
  on `Fin n`, so everything is finite anyway), and the trace
  `G.neighborSet v ∩ A` is then literally the paper's `N(v) ∩ A`.
  Mirrors Lax1's `ncard` usage.
- `traceCount` is graph-level, hence over an arbitrary `{V : Type}`
  (concept 1's canonical-types rule applies only to class-level
  quantification, as in `HasAlmostLinearNC`).
- Exponent via `Real.rpow` on casts; `c : ℝ` (a `ℕ` constant would be
  equivalent but reads worse under multiplication).
- The `∀ε ∃c ∀G,A` quantifier shape is fixed *here once*; concepts 8
  and 9 both conclude this named predicate, giving the uniform surface
  pipeline.md §5 asked for.

## 6. NowhereDenseClasses (definition-concept)

Shallow minors via branch sets of bounded radius; nowhere dense = for
every depth, some clique is excluded as a depth-r minor.

```lean
/-- A model of `H` as a depth-`r` minor of `G`: pairwise disjoint branch
sets, each spanned by walks of length at most `r` from a center vertex
(hence connected of radius at most `r`), with an edge of `G` between the
branch sets of any two adjacent vertices of `H`. -/
structure ShallowMinorModel {V W : Type} (r : ℕ) (H : SimpleGraph W)
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
def HasShallowMinor {V W : Type} (G : SimpleGraph V) (r : ℕ)
    (H : SimpleGraph W) : Prop :=
  Nonempty (ShallowMinorModel r H G)

/-- A graph class is nowhere dense if for every depth `r` some complete
graph is not a depth-`r` minor of any member. -/
def NowhereDense (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ HasShallowMinor G r (⊤ : SimpleGraph (Fin t))
```

Notes:

- The walk-based radius field packages "G[branch u] is connected with
  radius ≤ r" in one condition with no induced-subgraph/subtype
  machinery; connectivity is derivable and hence not a field
  (carry-nothing-derivable). `center_mem` is *not* derivable (it also
  rules out empty branch sets, as the standard definition requires).
- `⊤ : SimpleGraph (Fin t)` is mathlib's complete graph.
- `ShallowMinorModel` and `HasShallowMinor` are graph-level and so
  stated over arbitrary vertex types (the Set/walk-based forms need no
  instances); only `NowhereDense` quantifies over `Fin n`.
- Grads/`∇_r`, weak coloring numbers, admissibility — the whole §3a
  toolchain — are proof-package internal and do not surface.

## 7. WeaklySparseDependent (theorem-concept, obligation left OPEN)

Corollary 6a; decision D of `todo.md` (state, don't prove).

```lean
/-- A graph class is weakly sparse if some complete bipartite graph
`K_{t,t}` occurs in no member as a subgraph. -/
def WeaklySparse (C : GraphClass) : Prop :=
  ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ completeBipartiteGraph (Fin t) (Fin t) ⊑ G

/-- Every weakly sparse monadically dependent graph class is nowhere
dense. -/
axiom nowhereDense_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    NowhereDense C
```

- `WeaklySparse` lives here, not in `GraphClasses` (D6): it is used by
  exactly this statement, and the concept's reviewable idea ("weakly
  sparse + dependent ⇒ nowhere dense") includes its hypothesis
  vocabulary. Move it to concept 1 if we ever state more around it.
- `⊑` is mathlib's subgraph containment (`SimpleGraph.Copy`), scoped
  notation `open scoped SimpleGraph`. `t = 0` does not trivialize the
  negation (`K_{0,0} ⊑ G` always holds), so no `t ≥ 1` side condition.
- Abstract will advertise this open obligation as a deliberate bounty
  (source: flipfork arXiv:2505.16745 Lem 3.15 / Mählmann thesis 13.7).

## 8. NowhereDenseNC (theorem-concept, proved)

Corollary 6b at radius 1, the `pipeline.md` §3a chain.

```lean
/-- Nowhere dense graph classes have almost linear neighborhood
complexity. -/
axiom hasAlmostLinearNC_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    HasAlmostLinearNC C
```

## 9. AlmostLinearNC (theorem-concept, proved) — Theorem 2

```lean
/-- Monadically dependent graph classes have almost linear neighborhood
complexity (Theorem 2 of DMMPT26). -/
axiom hasAlmostLinearNC_of_monadicallyDependent
    (C : GraphClass) (h : MonadicallyDependent C) :
    HasAlmostLinearNC C
```

## 10. AdlerAdler (theorem-concept, obligation OPEN)

```lean
/-- Nowhere dense graph classes are monadically dependent. -/
axiom monadicallyDependent_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    MonadicallyDependent C
```

Included (D5, settled): five lines over already-present definitions, and
the surface then carries the full classical equivalence "on weakly
sparse classes, monadically dependent = nowhere dense" (7 + this) — the
story motivating the submission — plus a second well-defined bounty.
(Adler–Adler prove nowhere dense ⇒ monadically *stable*; the dependent
version is the weakening we need and is how DMMPT26 cites the
equivalence.)

## Decision record

All decisions are settled and folded into the concept notes above; this
section is the ledger.

Rev 2 (Jan's feedback):

- Transductions are defined on arbitrary relational structures;
  graph transductions are the `Language.graph` special case.
- D3 (edge symmetrization convention) — dissolved: the target
  structures are honest graph structures, symmetrization is absorbed
  into the interpreting formula (concept 3 notes).
- D4 (fresh language vs sum) — dissolved: arbitrary `L` forces
  `Language.sum`; colors are the `ColorRel` inductive.
- **D1** `GraphClass = ∀ n, SimpleGraph (Fin n) → Prop`.
  Broader alternatives evaluated and rejected: typeclass encodings
  (classes are quantified-over first-class values with no canonical
  instances), arbitrary `[Fintype V]` carriers (universe bump to
  `Type 1`, instance binders + Fintype-vs-Finite convention on the
  surface, finiteness no longer structural; convenience for constructed
  graphs on non-canonical carriers is proof-package-only and cheap via
  transport), iso-quotients (heavy, nothing needs it), bundled
  structures (projection noise, no invariants to attach).
- Refinement (from the D1 discussion): *graph-level* definitions —
  `traceCount`, `ShallowMinorModel`, `HasShallowMinor` — are stated
  over an arbitrary `{V : Type}` (no instances needed with the
  Set/walk-based forms), à la Lax1's generic `twinWidth`; only
  class-level quantification uses the canonical `Fin n`. Applied in
  the snippets above.

Rev 3 (Jan, 2026-07-24 — all recommendations accepted):
- **D2** `A.Nonempty` hypothesis; **D2'** `A : Set` + `ncard`.
- **D5** Adler–Adler converse concept included.
- **D6** `WeaklySparse` lives in concept 7.
- **D8** `GraphTransductions` is its own concept.
- **D9** Selection via domain formula + `range f = δ`-set.
- **D7** Naming (Jan: `NC` shorthand, no "Counting", mathlib-style axiom
  names — NOT Lax1's sentence style). Definition-concepts spell notions
  out; theorem-concepts abbreviate: modules 7–10 are
  `WeaklySparseDependent`, `NowhereDenseNC`, `AlmostLinearNC` (headline),
  `AdlerAdler`; the shared predicate is `HasAlmostLinearNC`. Axioms are
  `conclusion_of_hypotheses` with lowerCamelized predicates:
  `nowhereDense_of_weaklySparse_of_monadicallyDependent`,
  `hasAlmostLinearNC_of_nowhereDense`,
  `hasAlmostLinearNC_of_monadicallyDependent`,
  `monadicallyDependent_of_nowhereDense`.
  `traceCount`, `RealizeIn`, `structureClass` stay.

Step 3 (2026-07-24): realized as **Lax5** in
`monadic-dependence-neighborhood-complexity/`; concept package and
`lax build` pipeline are green. Deltas discovered while building:

- Module 6 is `NowhereDenseClasses` (a `NowhereDense` def inside a
  `NowhereDense` module trips the duplicate-namespace lint; mirrors
  `GraphClasses`).
- `colorLanguage` needs `deriving Language.IsRelational` (as mathlib's
  `Language.graph` does) so the `Structure.funMap` default fires, and
  `colorStructure` carries `@[implicit_reducible]` (required of defs of
  class type; same attribute as mathlib's `SimpleGraph.structure`).
- Walk import at the pin is `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`.
- Carriers are `Type*` (universe polymorphism is free generality for the
  graph-level defs; the class level stays on `Fin n`).
