# Corollary 6a proof plan (draft for iteration)

Target: discharge the open obligation
`Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent`
(weakly sparse + monadically dependent ⇒ nowhere dense), so that the
headline theorem's `#print axioms` reports standard axioms only.

Primary source: Mählmann's thesis (Lemma 13.7/13.8 + the §2 star-crossing
transduction), fetched to `references/maehlmann-thesis/` (untracked).
Secondary: flipping-and-forking App. A (`references/flipfork/`),
flip-breakability §4 Ramsey lemmas (`references/flipbreak/`).

## Route

Contrapositive. Assume ¬NowhereDense: some depth `r` has `K_t` as a
depth-`r` minor of members for all `t`; weak sparseness gives `t₀` with no
`K_{t₀,t₀}` subgraph anywhere in `C`. Derive `Transduces C allGraphs`.

Chain, with per-step sources:

1. **Bridge (shallow minor → subdivided biclique subgraph).** Ours (the
   thesis starts from the subdivision definition of nowhere denseness; our
   frozen concept uses shallow minors, so this gap is ours to close).
   From a `ShallowMinorModel` of `K_t` at depth `r`: prune to connection
   paths `P_uv` (center-to-center through the two branch trees, length
   ≤ 4r+3). Ramsey the *connection type* over 4-tuples of branch indices:
   color = full coincidence pattern (which positions of `P_uv`, `P_wx`
   are equal) + path lengths. On a homogeneous set the equality pattern
   collapses: shared positions force equal position pairs (a≠b yields a
   within-path repetition), sharing lives inside the common branch tree,
   so each branch has a hub vertex `h_u` with pairwise internally disjoint
   path segments of one uniform length `ℓ+1` to the other hubs. Output:
   for every `s` some member contains an exact `ℓ`-subdivided biclique of
   order `s` as a **subgraph**, `ℓ ≤ L(r)` uniform (class-level pigeonhole
   over `ℓ`). `ℓ = 0` is the immediate weak-sparseness contradiction.
   Only equalities and lengths are Ramseyed here; edges are step 2's job.

2. **Induced upgrade (thesis Lemma 13.8, formalized verbatim).** Bipartite
   Ramsey on atomic types of path pairs; principal sets WLOG independent;
   direct principal-principal edges give semi-induced bicliques (kill via
   `t₀`); shortest-path renormalization inside each path's vertex set
   gives uniform positions `k₁<…<k_{ℓ'}` (kills shortcuts, `ℓ' ∈ [ℓ]`);
   any cross-path or principal-path edge pattern yields a semi-induced
   biclique via order-type splitting (kill via `t₀`). Output: for every
   `s` some member contains an exact `ℓ'`-subdivided `K_{s,s}` as an
   **induced** subgraph, `ℓ' ≥ 1` fixed (pigeonhole again).

3. **Transduction (thesis §2 hardness picture).** Star-`ℓ'`-crossing
   transduction: colors mark the copy's principals and the internal
   vertices of *kept* paths (per target bipartite graph); interpreting
   formula φ(x,y) = "some path of length `ℓ'+1` from x to y with all
   internal vertices blue" (built by recursion on `ℓ'`). Induced-ness +
   exact length make φ define exactly the kept adjacency: blue internals
   confine the path to the copy, induced-ness confines it to a single
   subdivision path. Gives `Transduces C allBipartite`. Then the standard
   incidence encoding (`allBipartite` ⊇ incidence graphs, x~y iff common
   edge-vertex neighbor) gives `Transduces allBipartite allGraphs`;
   compose with the proved `Transduces.trans`. Contradiction with
   monadic dependence.

## New proof-package modules

- `Lax5Proofs/Ramsey.lean` — finite Ramsey, self-contained (nothing in
  pinned mathlib): subset Ramsey for `m`-uniform hypergraphs, any finite
  color set (induction on `m`); tuple reformulation "color depends only
  on order type"; bipartite product version (thesis Lemma 4.15 /
  flip-breakability Lemma 4.4). Reusable beyond this submission.
- `Lax5Proofs/MinorSubdivision.lean` — step 1. Shared def: an explicit
  `SubdividedBiclique` witness structure (principals + paths + uniform
  length + disjointness [+ induced flag or a separate Prop]) so steps
  1→2→3 compose without re-encoding.
- `Lax5Proofs/InducedSubdivision.lean` — step 2 (thesis 13.8).
- `Lax5Proofs/CrossingTransduction.lean` — step 3: path formula,
  correctness against an induced copy, incidence step, composition.
- `Lax5Proofs/Corollary6a.lean` — glue: contrapositive assembly, class
  pigeonholes, final theorem; rewire `Corollary6.lean` to consume it
  (same pattern as the 6b rewiring, 4d) and re-audit `#print axioms`.

## Order of work / step boundaries

1. Ramsey toolbox (independent, reusable; enables everything).
2. `SubdividedBiclique` def + step-1 bridge.
3. Step-2 induced upgrade.
4. Step-3 transduction + incidence + composition.
5. Glue, rewiring, axiom audit, todo/pipeline update.

Each is a commit-sized unit; iteration checkpoint with Jan after 1, 2,
and 4.

## Open decisions (input wanted)

- **Bridge output shape.** Proposed: subgraph-level exact-`ℓ` subdivided
  biclique (thesis 13.8's input), keeping all edge-cleanup in step 2.
  Alternative: fuse steps 1+2 into one Ramsey pass (single homogeneous
  set, adjacency colors included). Split matches the sources and keeps
  the bridge's Ramsey colors small; fused saves one extraction layer.
- **Bipartite→all-graphs.** Proposed: thesis-faithful two-step via
  `Transduces.trans` (proved). Alternative: single transduction with
  edge-hub encoding (right principals as edge gadgets), avoiding the
  composition. Two-step is less bespoke formula plumbing.
- **Formalization-notes stance for the bridge.** The bridge is folklore
  (implicit in the classical minor/subdivision equivalence); notes will
  argue it as the depth-`r`-minor-to-subdivision Ramsey argument rather
  than citing a specific numbered lemma. OK?
