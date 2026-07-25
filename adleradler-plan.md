# Adler–Adler backward direction: proof plan (rev 1)

Target: discharge the last open obligation of the Lax5 submission,
`Lax5.AdlerAdler.monadicallyDependent_of_nowhereDense`
(nowhere dense ⇒ monadically dependent), with standard axioms only.

This is the "backward" half of the classical equivalence whose forward
half (weakly sparse + mon dep ⇒ nowhere dense) was discharged as Cor 6a.

## Sources and shape of the argument

No known proof avoids first-order locality. The formalizable route is
the specialization to vertex deletions of flip-breakability
(`references/flipbreak/`, §"Flip-Breakability Implies Monadic
Dependence", Lemma `fb-shatter`), which is itself the modern form of
Adler–Adler via uniform quasi-wideness:

1. **Shattering extraction.** If `Transduces C allGraphs`, the edge
   formula φ of the transduction (with its k colors) *monadically
   shatters* arbitrarily large vertex sets in members of C: producing
   the powerset bipartite graph P_d (vertices [d] ⊔ 2^[d], edges i–S
   iff i ∈ S) yields, in some colored G ∈ C, a set W of size d and
   realizers (v_R)_{R ⊆ W} with φ(v_R, w) ⟺ w ∈ R. Elementary.

2. **Uniform quasi-wideness** (Nešetřil–Ossona de Mendez). Nowhere
   dense ⇒ for every radius r there are N : ℕ → ℕ and s such that any
   W with |W| ≥ N(m) in a member G contains, after deleting a set S of
   ≤ s vertices, a subset W' of size m that is pairwise r-independent
   in G − S. **Already formalized, sorry-free, in Jan's catalog**
   (`~/git/autoformalize/4/catalog`, `SparsityLectures/NDImpliesUQW` +
   its Ramsey chain); ported below.

3. **Locality core** (the genuinely new formalization; no Gaifman
   normal form, no syntax transformations — see design below). For
   every rank bound q there are radius/rank/color parameters R, Q, t
   (functions of q, k, s only) and a *coloring* of the vertices —
   the rank-Q local EF type of the radius-R ball around each vertex in
   G − S, decorated with distance-to-center and S-adjacency — taking at
   most t values, such that: for any w₁, w₂ with equal colors that are
   far apart in G − S, and any v ∈ G − S far from both, every formula
   φ(x,y) of rank ≤ q over the colored graph language satisfies
   φ(v,w₁) ⟺ φ(v,w₂) *in G* (S present; S-hops are absorbed by the
   decorations, so no formula rewriting for deletions is needed).

4. **Assembly** (flipbreak endgame + a realizer-escapes-S twist).
   Choose parameters in dependency order: q := qrank φ; locality
   thresholds from q; UQW radius r' from those; UQW gives (N, s);
   decorations from s; color count t; m := 2(s+1)(t+1); d := N(m).
   Shatter W of size d, run UQW, split W' into 2(s+1) blocks of t+1:
   each has a monochromatic pair; form s+1 disjoint foursomes
   (a₁,a₂,b₁,b₂). The realizers of the s+1 distinct traces {a₁,b₁}
   are distinct vertices, so one of them, v, avoids S. Disagreement
   φ(v,a₁) ≠ φ(v,a₂) forces (by 3) v to be near a₁ or a₂ in G − S;
   likewise near b₁ or b₂; the triangle inequality then contradicts
   the r'-independence of W'.

Steps 1, 2, 4 are established technology (catalog port + finite
combinatorics + the plumbing style of `CrossingTransduction.lean`).
Step 3 is the mountain; its design is fixed below so that *everything
is semantic* — the only formula induction in the whole development is
the standard "back-and-forth family ⇒ agreement" lemma.

## Design of the locality core

Fix G on Fin n, colors : Fin k → Set (Fin n), S with |S| ≤ s
(enumerated, with padding, as Fin s → Fin n). All distances d* and
balls are taken in `deleteVerts G S` (same vertex type; S-vertices are
isolated there, so they lie in no ball and are d*-unreachable — this
makes them permanent "identity" elements handled by decoration alone).

### LocalTypes: the finite invariant

- `AtomData ℓ` := adjacency + equality patterns on Fin ℓ, color bits
  (Fin ℓ → Fin k → Bool), S-adjacency bits (Fin ℓ → Fin s → Bool),
  and distance-to-center values (Fin ℓ → Fin (R+1)). Finite.
- `LType : ℕ → ℕ → Type`, `LType 0 ℓ = AtomData ℓ`,
  `LType (j+1) ℓ = AtomData ℓ × Finset (LType j (ℓ+1))`; Fintype and
  DecidableEq by recursion. The color count bound t is
  `card (LType Q 1)` — uniform in the graph. This replaces "finitely
  many formulas of rank Q up to equivalence" (per the R1 philosophy of
  `pipeline.md`, quantifier-rank enumeration is never formalized).
- `τ j (t : Fin ℓ → V)` computed by recursion, the (j+1)-level Finset
  ranging over the ball B_R(w) around the center. Key lemmas:
  - restriction: τ (j+1) determines τ j;
  - extension (both directions): equal τ (j+1) of tuples ⇒ every
    one-point extension on one side is matched on the other with equal
    τ j — this is literally Finset.ext plus the recursion, and is the
    entire content of "EF equivalence" here;
  - distance transfer: equal τ j preserves ball-internal distances
    ≤ 2^(j−1) between tuple entries (midpoint halving induction);
    ball-internal distance equals d* in the regime used (paths of
    length ≤ R − centerdist stay in the ball).

### EFAgreement: the only formula induction

`qrank : BoundedFormula → ℕ` (structural). A *back-and-forth system*
on (G, colors) is F : ℕ → Set (finite partial injections V ⇀ V)
preserving adjacency, equality and colors, with one-point forward and
backward extension F(j+1) → F(j). Theorem: σ ∈ F j, qrank φ ≤ j,
free-variable assignment into dom σ ⇒ `RealizeIn` agrees on the tuple
and its σ-image. Induction over BoundedFormula (relational language,
variables-only terms). S-adjacency and distance decorations are *not*
atoms of the language; they only live in the invariant clauses.

### BallSwap: the cluster game

Goal: from color(w₁) = color(w₂) (equal τ Q of decorated R-balls),
d*(w₁,w₂) and d*(v,wᵢ) large, build a back-and-forth system whose
level-q member contains {v↦v, w₁↦w₂, w₂↦w₁}. Position at budget j:

    σ = g ∪ h ∪ id_O, where
    g  : forward mirror, tuple position with τ-equality at budget
         j + L between (ball of w₁; w₁::dom g) and (ball of w₂;
         w₂::ran g)  [L := distance-preservation slack, ~2q+O(1)]
    h  : backward mirror, symmetric, anchored w₂ ↦ w₁
    O  : identity part; every o ∈ O − S keeps d* > 3^j from both
         active regions Active₁ := {w₁} ∪ dom g ∪ ran h and
         Active₂ := {w₂} ∪ dom h ∪ ran g; o ∈ S unconstrained
         (S-adjacency decoration makes S transparent)
    radius bookkeeping: Active_i ⊆ B_{ρ}(w_i) with ρ + Σ_{i<j} 3^i
         bounded by the static budget ρ_max ~ 3^(q+1)

Extension at budget j+1, Spoiler plays x:
- x ∈ dom σ (or ran σ for backward): answer along σ.
- x ∈ S: identity. Atoms against mirror elements are preserved by the
  S-adjacency decoration; no distance clause applies.
- d*(x, Active₁) ≤ 3^j: forward-mirror move (if x is nearer ran h,
  it extends h backward; both cases are τ-extension of the
  appropriate mirror). The answer's distances to O and to the other
  active region are controlled by the distance-transfer lemma and the
  decorations; nearness to *both* active regions is excluded by the
  static gap d*(w₁,w₂).
- d*(x, Active₂) ≤ 3^j: symmetric.
- otherwise: new identity element. Geometric sums (Σ_{i<j} 3^i < 3^j)
  keep all farness clauses invariant, so identity elements are never
  adjacent to mirror elements on either side.

The two mirrors swap the two ball regions wholesale, which is why no
cross-consistency conditions between g and h are needed (left pairs
near-w₁/near-w₂ map to right pairs near-w₂/near-w₁; both far). No
threshold counting / basic local sentences ever appear — fresh
Spoiler elements are answered by the identity because both game sides
are the *same* graph. This is the decisive simplification over
formalizing Gaifman's theorem.

Conclusion (the only statement Assembly consumes):

    swap lemma: for all φ(x,y) with qrank ≤ q over withColors graph k,
    all v ∉ S with d*(v,w₁), d*(v,w₂) > 3^q, if color(w₁) = color(w₂)
    and d*(w₁,w₂) > gap(q), then
    RealizeIn G colors φ ![v,w₁] ↔ RealizeIn G colors φ ![v,w₂].

Exact numeric thresholds (R, Q, L, gap, ρ_max) will be fixed
generously during implementation (everything ≤ 3^(q+c) for small c);
the plan commits only to the dependency order: all are functions of
(q, k, s) alone, with s entering only through decorations, never
through radii or ranks — that is what breaks the circularity in the
parameter fixing of step 4.

## Module plan (proofs package)

- `Source/Catalog/SparsityLectures/{Ramsey, MulticolorRamsey,
  BipartiteRamsey, IterativeBipartiteRamsey, OddStepReduction,
  EvenStepReduction, UniformQuasiWideness, NDImpliesUQW}` — port from
  catalog-4 (v4.29.0-rc2 → v4.30.0, the established path). NOTE:
  native `Lax5Proofs/{Ramsey,BipartiteRamsey}.lean` (from the Cor 6a
  work) may already cover part of the chain; reconcile during the
  port rather than duplicating.
- `Lax5Proofs/QuasiWideness.lean` — encoding bridge: concept
  `NowhereDense C` ⇒ catalog `IsNowhereDense (copyClosure C)` (the
  easy direction: catalog paths are concept walks) ⇒ UQW statement
  specialized to members of C.
- `Lax5Proofs/LocalTypes.lean` — the finite invariant.
- `Lax5Proofs/EFAgreement.lean` — qrank + agreement theorem.
- `Lax5Proofs/BallSwap.lean` — the cluster game and swap lemma.
- `Lax5Proofs/AdlerAdler.lean` — powerset graphs, shattering
  extraction, parameter fixing, pigeonhole, contradiction; final
  theorem matching the concept axiom statement; axiom audit.

Attribution (for `manifest.yaml` / formalization notes): theorem
Adler–Adler (nowhere dense classes are monadically stable, a fortiori
dependent); proof route follows flip-breakability §4.3 specialized to
deletions (uniform quasi-wideness), with the locality input
reformulated as a semantic ball-swap argument in place of Gaifman's
theorem; UQW port credited as in the existing SparsityLectures
modules (sparsity lectures, Ch. on wideness).

## Order of work

1. Plan (this document). ✓
2. UQW chain port; build green; commit.
3. ND → UQW bridge (`QuasiWideness.lean`); commit.
4. `LocalTypes.lean`; commit.
5. `EFAgreement.lean`; commit.
6. `BallSwap.lean` — the long pole; may land in several commits
   (position structure + extension cases + conclusion).
7. `AdlerAdler.lean` assembly; rewire `Corollary6.lean`-style consumers
   if any; `lean_verify` audit of the headline theorem; update
   `abstract.md`, `pipeline.md`, `todo.md`, memory; commit.

## Risks / fallbacks

- The swap-lemma bookkeeping is the only real risk. Mitigations baked
  into the design: distances preserved *exactly* via decoration (not
  via rank), only two mirrored clusters ever exist, identity handles
  everything else, and all farness clauses are simple `3^j`
  inequalities with geometric-sum maintenance.
- If tuple-indexed `LType` recursion fights the elaborator, fall back
  to lists with a length invariant (`τ : ℕ → List V → …`).
- The port is low-risk: same source catalog and toolchain jump as the
  five modules already ported for Cor 6b/6a.
