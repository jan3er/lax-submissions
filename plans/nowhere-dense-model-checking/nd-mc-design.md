# ND-MC design note (P0, 2026-07-28)

Settles items (a)–(e) of plan P0 against the fetched texts. Sources
now in `references/`: `rploc` (arXiv 2606.23180, read end to end),
`gks` (arXiv 1311.3899, §4/§6/§8 read closely), `mw` (arXiv
2502.18065, v1 and v2, model-checking part read for conventions).
Each has a README with fetch date and license. Everything below is
design, not statement text; nothing here freezes before the P1 gate.

Two results of the cross-checks change the plan for the better, one
names a real new proof obligation:

1. **(a) The matrix-indexed variant family of D8 collapses.** The
   isolation rewrite needs no formula variants at all: capped
   distance profiles, recorded as colors on *every* vertex of the
   arena — including the batch vertices themselves — already carry
   the W-distance matrix (`p_j(w_i) = dist(w_i, w_j)`). One uniform
   quantifier-free translation per formula, one correctness lemma,
   zero graph-dependent formula selection. R2 shrinks again.
2. **(d) The radius schedule is confirmed flat**, with the sharper
   constant ρ* = ρ⁻(0,q) (the plan's ρ⁻(1,q) is a safe over-bound).
   The reason is architectural and worth stating as the invariant:
   the isolation rewrite preserves distance rank, and every arena
   re-runs the locality theorem fresh at unchanged rank, so no radius
   anywhere ever exceeds the top-level ρ⁻(0,q).
3. **(b) R1 has exactly one hard kernel**: the in-degree bound for
   transitive-fraternal augmentations on nowhere dense classes
   (GKS §6 cites it to Nešetřil–Ossona de Mendez; it is *not* in the
   sparsity notes and *not* in Lax12). Everything else in the cover
   pipeline is elementary or already endorsed. Named and budgeted
   below.

## (a) The isolation rewrite

### Setting

Arena `A`: a colored graph (fixed vertex set `Fin n`, edge set,
color rows) in the binary fragment of distFO (no unary distance
atoms — see (c)). Batch `W = {w_1, …, w_m'}`, `m' ≤ m`. New arena
`A' = A` minus all edges incident to `W` (Lax12's `deleteVerts`,
which is *already* the isolation form — carrier kept, incident edges
dropped; the UQW concept speaks this language natively).

Recorded data, computed at runtime, all per-batch:

- **Profiles**: for `j ∈ [m']` and `a ∈ {0, 1, …, ρ*, >ρ*}`, color
  `D_{j,a} = {v : dist^A(v, w_j) = a}` (capped at the global radius
  bound ρ* of (d)). This is the only color family. The rev-2 palette
  collapses into it: W-membership is `D_{j,0}`, old-neighbor marks
  are `D_{j,1}`, and the capped W-distance matrix is the profile
  rows *at* W vertices (`w_i ∈ D_{j,a}` iff `T_{ij} = a`). Nothing
  else is recorded.

### The translation `iso : Formula → Formula`

Purely syntactic, defined once, independent of the graph:

- `x = y`, color atoms (including ancestor-level `D`-atoms): unchanged.
  Vertices persist, so equality needs no readout — this is rev 2's win
  and it survives contact with the sources.
- `E(x,y) ↦ E'(x,y) ∨ ⋁_j [(D_{j,0}(x) ∧ D_{j,1}(y)) ∨ (D_{j,1}(x) ∧ D_{j,0}(y))]`.
- `dist(x,y) ≤ d ↦ dist'(x,y) ≤ d ∨ ⋁_j ⋁_{a+b≤d} (D_{j,a}(x) ∧ D_{j,b}(y))`
  (primed atoms in the new metric of `A'`; `a, b ≤ ρ*` recorded values
  only, sound since `d ≤ ρ*`).
- Boolean connectives, quantifiers: structural. A local guard
  `dist(x̄,y) ≤ ρ⁺(·)` translates like any distance atom; the result
  is a disjunction, hence *not* a guard — the quantifier degrades to
  unrestricted at the same rank (allowed by the drank definition).
  Locality is lost, rank is kept; the next level re-localizes.

### Correctness lemma (`isolateBatch`, L3 item 10)

For **every** tuple `ā ∈ V^k` (on or off `W`, no side conditions):

    A ⊨ φ(ā)  ⟺  A' + recorded colors ⊨ iso(φ)(ā)

Metric kernel (the one walk lemma everything reduces to):

    dist^A(x,y) = min( dist^{A'}(x,y), min_j (p_j(x) + p_j(y)) )

with `p_j(v) = dist^A(v, w_j)`, min over ∞. Proof: ≥ — a shortest
A-path either avoids W entirely (then every edge survives into `A'`)
or passes some `w_j` (then its length is ≥ `p_j(x) + p_j(y)`); ≤ —
paths witness. Covers the on-batch cases uniformly: `x = w_i` gives
`p_i(x) = 0` and the `j = i` disjunct reads `p_i(y)` off `y`'s
profile; `x, y` both on `W` reads the matrix off `x`'s profile row.
Elementary over Lax12's walk-based distance API (Lax5 walk-lemma
patterns imitated proofs-side, no dependency).

Preserved exactly: drank `(k,q)`, every atom radius, free and bound
variables, the binary fragment (c). Not preserved: locality of
guards (by design).

### Cross-check against GKS §8 (their reading of types at removed vertices)

Their per-cluster step (Lemma 8.2, `redlem`) removes Splitter's batch
and expands the remainder with exact-distance predicates
`Q_{ij} = {v : dist^G(v, w_j) = i}`, then selects a rewritten formula
`φ^θ` per atomic q-type θ of the removed tuple, and needs the
auxiliary formulas `ξ_j(x̄,ȳ) = ξ(y_j)` to read truth *at* removed
vertices. Recovery map:

| GKS §8 | here |
|---|---|
| `Q_{ij}` distance predicates | profiles `D_{j,a}` (identical data, capped) |
| atomic q-type θ of `w̄` | profile rows + colors *at* W vertices |
| variant family `φ^θ` | single `iso(φ)` (θ is now in the structure) |
| readout `ξ(y_j)` at removed vertices | nothing — W vertices persist; tables are computed at them like anywhere else; once isolated they fall out of covers and evaluate by lookup |

Everything their translation delivers, `iso` delivers; the two pieces
of machinery that existed only because their vertices disappeared
(θ-variants, readout formulas) have no residue. **Fallback** if the
Lean proof of `isolateBatch` surprises us: rev-2's matrix-indexed
variant family is strictly more general and drops back in with the
same downstream shape; nothing else moves. I consider this unlikely —
the correctness lemma above is atom-by-atom.

## (b) Cover computation (GKS §6, the R1 area)

### What the sources actually contain

GKS §6 splits cleanly:

1. **Cover from an ordering** (their Lemma 6.9 + Theorem 6.2 proof):
   with `<` witnessing `wcol_{2r}(G) ≤ s`, the clusters
   `X_{2r}[G,<,v] = {w : v ∈ wreach_{2r}[G,<,w]} = N_{2r}^{G∖S(v)}(v)`
   (`S(v)` = predecessors of `v`) form an r-neighborhood cover,
   radius ≤ 2r, degree ≤ s. Computation: process vertices in
   ascending order; BFS to depth 2r from `v` in the current graph;
   delete `v`; also record the cover-assignment `f(v)` = first
   cluster whose core ball catches `v` (their Remark 6.10, no extra
   cost). Cost `O(n^{1+2δ})` given degree ≤ `n^δ`, by charging each
   BFS to `Σ_v |X_v| = Σ_v d(v) ≤ n^{1+δ}` — their eq. (mt2)
   argument, elementary. *Class-free*: covering property and radius
   hold for an arbitrary ordering; only the degree needs `<` good.
2. **Ordering computation**: r rounds of tight transitive-fraternal
   augmentation. Round `i`: orientation `H⃗_i` with `Δ⁻ ≤ d_i`; add
   transitive arcs `(u,v)` for `u→w→v` and fraternal edges `uv` for
   `u→w←v`; orient the fraternal edges by greedy degeneracy of the
   fraternity graph; `d_{i+1} ≤ d_i + d_i² + (degeneracy bound)`.
   After r rounds, the *degeneracy order* of the underlying graph of
   `H⃗_r` witnesses `wcol_r(G) ≤ 2(d_r+1)²` (their Lemma 6.6, proof
   elementary given their path Lemma 6.5, which is an induction on
   path length). Everything is linear-time given the arc lists,
   `O(n·d_i²)` per round.

### What Lax12 gives, and the one gap

Endorsed and proved: `HasSubpolynomialWcol` (subgraph-uniform, `⊑`,
ordering as `Equiv.Perm (Fin n)`, walk-based `wreach`) — this
discharges the *existence* half of the cover theorem-concept
(D10/L2.9) directly: order by choice from the wcol bound, clusters as
above. Also `HasSubpolynomialDensity` (every depth-r minor of every
member, `c·m^{1+ε}` edges) — the tool the gap's proof consumes.

**The gap (R1 kernel, named):** the bound `d_r ≤ c·n^δ` for the
*computed* orientations on nowhere dense inputs. GKS cite NO05
(Cor 4.2/Thm 4.3); the sparsity notes ed2019 have no fraternal
augmentation content at all (checked), so this is new formalization
with no notes-source and no Lax12 concept to lean on. The required
statement, phrased over Lax12 vocabulary:

> **Augmentation density theorem** (proofs-side, Lax3). For every
> nowhere dense `C`, `r ∈ ℕ`, `δ > 0` there is `c` such that for
> every subgraph `G` (n vertices) of a member, the r-round
> augmentation process above, started from a greedy degeneracy
> orientation, admits fraternal orientations with
> `Δ⁻(H⃗_i) ≤ c·n^δ` for all `i ≤ r` — and the greedy per-round
> degeneracy choice achieves this.

Proof plan (NO05 §4 shape): maintain the invariant that each
`H_i`-edge is realized by a G-path of length ≤ `2^i`; the load-bearing
lemma is the *fraternity densification*: if the fraternity graph of
an orientation with `Δ⁻ ≤ d` has a subgraph of average degree
`> f(d, k)`, then `G` has a dense shallow minor at depth `O(2^i)` —
a private-witness extraction argument, the same genre as Lax12's
`Densification` module (large adm ⇒ dense minor), which is the
in-house pattern to imitate. Consumed by `HasSubpolynomialDensity`
at depth `2^r`-ish. Budget: this is the campaign's only genuinely
new sparse-combinatorics block; 3–5 sessions inside P6, and P6's
8-session upper estimate already anticipated R1 peaking there.

Efficiency nicety declined: GKS note `⌈log_{3/2} r⌉ + 1` rounds
suffice; we take r rounds for ease, as they do.

**Fallback** (constants only, as the plan requires): none needed for
the *statement* — the cover theorem-concept is discharged by Lax12
wcol regardless. If the augmentation theorem resists, the campaign
fallback from the plan applies (register locality + splitter +
cover-existence; carry C0 open) — I found no cheaper ordering
algorithm in the sources, and the tempting radius-for-degree trades
(Awerbuch–Peleg covers) are unsound here: their radius grows with
1/δ while the game parameters must be fixed *before* δ is chosen
(δ = ε/(2ℓ) with ℓ depending on the game radius). Recording this
dead end so nobody walks into it at 3am.

### Pseudocode pinned (P6 target)

```
order(G):                            # masked CSR view
  H⃗ ← greedy degeneracy orientation of G          # bucket queue, O(n+m)
  repeat r_g times:
    arcs ← H⃗ ∪ {(u,v) : u→w→v}                    # per w: in×in, in×out pairs
    F ← {uv : u→w←v}
    H⃗ ← arcs ∪ greedyDegeneracyOrient(F)          # O(n·d²) total
  return degeneracy order of und(H⃗)               # bucket queue again

cover(G, <, 2r_c):
  for v ascending in <: BFS depth 2r_c from v; emit X_v; record f(w)
                        for newly caught w; delete v                # O(n^{1+2δ})
```

## (c) Binary-fragment closure

`BinaryFragment`: no unary distance atoms (`dist(x,Y) < r`). The
closure claims, each a lemma on the respective rewrite function,
proved by the same structural induction that proves its soundness:

1. **FO ↪ distFO** (L3.12 reduction) introduces *no* distance atoms:
   an FO formula of qr ≤ q is verbatim a distFO formula of drank
   (k,q) (unrestricted ∃ is in the syntax; the radius constraints are
   vacuous). Trivial induction.
2. **Locality rewriting** preserves the fragment. Checked against
   every formula the rploc proofs construct: Lem 8 emits one-sided
   atoms and annulus guards, all binary; Lem 12 emits pairwise
   `dist(a_i,a_j) ≤ d` tests, ball guards, and counting formulas over
   cluster balls, all binary; scatter sentences carry an input β
   unchanged. Unary atoms appear in rploc only as *input* base cases,
   never as output.
3. **`iso`** emits color atoms (ordinary unary relations, not unary
   distance atoms) and primed binary distance atoms. By inspection
   of (a).
4. **The evaluator's base case** consumes color and equality atoms
   only.

Cost of keeping unary distance atoms in the *concept* (D3
faithfulness): one extra base case per structural induction
proofs-side — in Lem 5 it is semantically r-local since
`dist(x,Y) < r` depends on `N_r(x)` only; in Lem 8 it sits on one
side of the split like any unary atom. Cheap, and the concept stays
honest to the paper.

## (d) Radius schedule

Fix `q` = quantifier rank of the input sentence after the FO ↪ distFO
reduction (drank `(0,q)`). Horizon: the paper's concrete pair
`ρ⁻(k,q) = 9^{(k+q+1)q}`, `ρ⁺(k,q) = 9^{(k+q)(q+1)}` on the concept
surface; proofs against the abstract two-inequality `Horizon`
structure (D4), of which the proofs use nothing else (verified: every
inequality invoked in rploc's five proofs is one of the two, or the
derived chain `ρ⁻(a,b) ≤ ρ⁺(a,b) ≤ ρ⁻(a−1,b+1)`).

**Invariant (no growth).** Every formula ever manufactured by the
pipeline has drank `(k',q')` with `k'+q' ≤ q+…` dominated so that its
atom radii are ≤ ρ* := ρ⁻(0,q) = 9^{(q+1)q}. Proof shape: the
locality theorem consumes drank `(k,q)` and emits drank `(k,q)`
(atoms ≤ ρ⁻(k,q)); `iso` preserves drank and atom radii exactly;
sub-β's of scatter sentences have drank `(k+i, q−i)` with strictly
smaller ρ⁻. Since every level restarts locality at the rank it
received, radii are monotone non-increasing along every branch of
the recursion. The plan's ρ⁻(1,q) over-bound is retired for the
sharp ρ⁻(0,q).

Derived constants, all fixed per (φ, ε) at construction time:

| constant | value | role |
|---|---|---|
| ρ* | ρ⁻(0,q) | cap on every atom radius, profile cap, BFS depth cap |
| r_c | ρ⁻(1,q−1) | table locality radius: max semantic locality of any tabled β (worst case i = 1 in scatter drank) |
| cover | radius ≤ 2r_c, degree n^δ | per arena, from (b) |
| r_g | 2r_c | splitter game radius (cluster ⊆ N_{2r_c}(center)) |
| ℓ | N_{r_g}(2s_{r_g} + 2) | game length, from Lax12 UQW margins |
| m | ℓ·(r_g + 1) | batch size |
| δ | ε/(2ℓ) | cover degree exponent (GKS's recurrence, reused verbatim) |
| scatter radii | 4R, R = 9^t·ρ⁻(k+1,q−1), t < k | finitely many per rank, ≤ ρ* |
| greedy cap | k+q+1 picks per scatter sentence | mw convention, exclusion-BFS per pick |

Note on ℓ: the notes' Lemma 4.2 states `ℓ := N_r(2s_r+1)` but its
proof uses `2s_r+2` (needs `s_r+1` pairwise disjoint paths so one
avoids S). We take the `+2` form; slip to be silently fixed by the
formalization, worth a line in the win-proof's notes.

**Isolation-form win proof (notes Lem 4.2 adapted; L2 item 8).** The
strategy is unchanged in form: `W_i` := the still-in-arena vertices
of BFS-paths `P_{j,i}` (length ≤ r_g, in the arena where `v_j` was
played) from each earlier connector vertex; `|W_i| ≤ (i−1)(r_g+1) ≤ m`.
Two ingredients replace "removed vertices are gone":

1. *Isolation is permanent*: arenas only lose edges (balls are
   induced subgraphs, batches only delete), so a vertex isolated at
   round `i` has no incident edge in any later arena. Every connector
   vertex is isolated the round it is played (the paths end at it),
   and playing an isolated vertex loses immediately (its r-ball is a
   single vertex, edgeless) — so in a surviving play all connector
   picks are distinct and never previously isolated.
2. *Path disjointness*: if `u` lay on an earlier pair's path `Q_j`
   (isolated at round `i_{2j}`) and also on a later pair's path
   `Q_{j'}`, then `u` carries a `Q_{j'}`-edge in an arena after
   `i_{2j}` — contradiction. So the `s+1` pairs' paths are disjoint,
   one avoids `S`, and its endpoints violate
   `DistIndependent (deleteVerts G S) r B` — which is *literally* the
   conclusion shape of Lax12's `uniformlyQuasiWide_of_nowhereDense`
   (walk-based, deleteVerts = isolation). The impedance between the
   source and the endorsed UQW is zero; this was rev 2's bet and it
   checks out.

Also confirmed from GKS §4: win monotonicity under `⊑` (their
Remark on superset removal, extended to vertex-subset arenas) is what
links the algorithm's arena (a cover cluster with the batch isolated)
to the game's arena (the full ball) — one lemma, L2 item 7.

## (e) Formula-table size functions (symbolic only)

Currency (mw conventions adopted): per-arena *sentence bits* and
per-vertex *table rows* — a bit per formula in a fixed list, plus
per-arena scatter values capped at k+q+1. No type objects; lists
driven by the input sentence (D7). The mw uniform reformulation
("tp is a computable function of ltp and stp") is the shape of the
evaluator's correctness statement at each arena.

Construction-time recursion (never evaluated on concrete φ — R4):

    T_0     := {φ̂}                                    (sentences)
    B_j     := scatter-β's and local components of locRW(T_j)
    T_{j+1} := iso-translations of B_j's cluster-relativized
               formulas, closed under locRW components     (tables)

with symbolic size bounds `N_{j+1} = g(N_j, q, m, ρ*)` where `g` is
whatever the rewrite functions produce — enormous, elementary, and
never normalized. Everything the program tables at depth `j` is in
`T_j`; the lists are Lean terms produced by `ℓ`-fold iteration at
program-construction time, so the RAM manipulates only bit arrays
indexed by (formula-position, vertex) — D8 holds with the variant
family gone.

Signature schedule: depth-`j` formulas reference profile colors of
all ancestor batches, so the color signature grows by `m·(ρ*+2)`
slots per level, total `L_max = L_0 + ℓ·m·(ρ*+2)` — fixed at
construction time; runtime keeps per-level color arrays on the
Trail. Cost bounds only ever see the symbolic constants
`c(φ,ε) = max_j N_j` and `L_max`.

## Evaluator call graph (D9 made precise, for P4)

Mutual recursion, termination by (game depth, phase) lexicographic:

- `sentenceEval(arena, sentences)`: locRW each sentence → boolean
  combo of trivial local sentences (⊤/⊥ — with 0 free variables the
  local-guard disjunction is empty, so local sentences are decided
  syntactically) and scatter sentences. Each `scatter(r, β, t)`:
  `typeTables(arena, β)` (local, 1 free var), then Fin-order greedy
  over the β-table, ≤ k+q+1 picks, exclusion-BFS radius r per pick.
- `typeTables(arena, fmls)`: for local β — cover pass (b) at radius
  r_c; per cluster: center = Connector's move, Splitter's batch W by
  the strategy (BFS paths to ancestor connector vertices, from
  per-level BFS trees kept on the stack, GKS Remark 4.4's cost),
  profiles by m BFS runs, then recurse at depth+1:
  `typeTables(cluster∖W-edges, iso(β↾cluster))` — β's bit at v is
  read in v's assigned cluster `f(v)` (semantic locality, Lem 5,
  plus ball-preservation `N_{r_c}(v)` ⊆ cluster ⇒ induced structures
  agree). For non-local formulas (the iso-translations): locRW
  first → local parts as above + scatter parts via
  `sentenceEval(arena, ·)` *at the same arena* (phase decreases;
  its own typeTables calls descend).
- Base (depth ℓ or arena edgeless): every binary atom between
  distinct vertices is false; evaluation by color-row lookup and
  per-color-class counting capped at q (unary-only FO evaluation),
  `O(n)` per arena.

Correctness invariant carried everywhere: `Sat` for scatter
sentences is parameterized by the greedy `ScatterChoice` in Fin
order at that arena (D6); the locality theorem holds for every
choice, the program computes exactly this one.

Cost per arena: cover `n^{1+2δ}` + per-cluster (m+1 BFS runs +
strategy) charged to `Σ|X| ≤ n^{1+δ}` + scatter passes
`c(φ,ε)·(k+q+1)·edges` + base `O(n)`; edges ≤ `c·n^{1+δ}` by Lax12
density (arenas are subgraphs of members — `⊑`-uniformity consumed
as predicted). Recurrence and its solution: GKS's, verbatim
(`T(j,n) ≤ Σ_X c·T(j−1,n_X) + c·n^{1+δ}` ⇒ `c^ℓ·n^{1+ε}`), with
their `n_1` threshold trick (brute force below `n_1`, `n^{δ/2} ≥ 2`
absorbs constants) as the cost-algebra pattern for P7/R3.

## Source notes (for P1–P4 statement writing)

- rploc lemma map (compiled numbering → plan names): Lem 5
  `semLocal` (needs k ≥ 1; restructure the paper's evaluation-trace
  argument as structural induction with a strengthened
  agreement statement — concept surface untouched), Lem 8 `separate`
  (the induction must carry *all* free-variable partitions: case 3
  re-applies the IH to `α(x̄ȳ)` under the original split after
  splitting off `z` — this is why D5's `UsesOnly` set-tracking,
  not re-typing, is right), Lem 9 `clusters`-Vitali (state with
  index maps `I ⊆ [k]`, `m : [k] → I` directly, as the Cor-10 proof
  actually uses), Cor 10 cluster partition (c = 8; tests
  `dist(a_i,a_j) ≤ d`, `d ≤ 8·9^{k−1}r`; R ranges over the finite
  set `{9^t·r : t < k}`), Lem 11 `scatterCore` (the margin
  hypothesis (eq:margin) is the elegant pivot; H ≥ 4R+r), Lem 12
  `farQuant` (case disjunction over (I, m, R) guarded by distance
  tests; scatter values needed only up to k+1 ≤ k+q). Thm 1 proof
  detail worth keeping: the k = 0 quantifier case is exactly
  `scatter(4ρ⁻(1,q−1), ψ, 1)` — the evaluator's sentence path in
  miniature.
- mw v1→v2: v1 proved its Theorem 4.1 by EF games/types; the error
  Mählmann spotted lives there; v2 outsources to the rploc note and
  keeps only the consumption lemmas. Both versions kept in
  `references/mw` for the diff; the consumption conventions we
  adopt (ltp/stp currency, k+q greedy cap, localglobal′ shape) are
  v2's.
- GKS §5 and §7: confirmed dead for us — §5 (distance-r independent
  set / UQW-based Theorem 5.1) is obviated by the predetermined
  greedy scatter choice; §7 (FO⁺, EF⁺ games, star expansions
  `G⋆𝒳q`) is replaced by the rploc engine plus `iso`. Neither
  needs fetching into concepts.

## Plan deltas proposed (for Jan at the gate)

1. **D8 tightened**: drop "capped W-distance matrix selecting among
   finitely many precomputed formula variants"; the profile colors
   (including at batch vertices) subsume it. Rev-2's variant family
   demoted to fallback inside R2.
2. **D4 sharpened**: ρ* = ρ⁻(0,q); table locality radius ρ⁻(1,q−1);
   game constants as in the (d) table, with the notes' `2s+1` → `2s+2`
   slip noted.
3. **R1 renamed to its kernel**: the augmentation density theorem
   (statement above), sitting in P6 with a 3–5 session budget,
   patterned on Lax12's `Densification`; cover *existence* (D10)
   confirmed dischargeable from Lax12 wcol alone, so P3 carries no
   part of R1.
4. No change to the concept surface, the statement C0, the gates, or
   the phase order.
