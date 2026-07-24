# Corollary 6a proof plan (rev 2, after recycling survey)

Target: discharge the open obligation
`Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent`
(weakly sparse + monadically dependent ⇒ nowhere dense), so that the
headline theorem's `#print axioms` reports standard axioms only.

Primary source: Mählmann's thesis (Lemma 13.7/13.8 + the §2 star-crossing
transduction), `references/maehlmann-thesis/` (untracked). Secondary:
flipping-and-forking App. A (`references/flipfork/`), flip-breakability §4
(`references/flipbreak/`).

## Recycling: `~/git/autoformalize/4/catalog/Catalog/`

Jan formalized most of this before (toolchain v4.29.0-rc2 vs our
v4.30.0; the `Lax5Proofs/Source/Catalog/SparsityLectures/*` modules were
already ported from this same catalog, so the port path is established).
Directly reusable, sorry-free-looking:

- **Ramsey toolbox**: `SparsityLectures/{Ramsey,MulticolorRamsey,
  BipartiteRamsey,IterativeBipartiteRamsey}` + `MonadicDependence/
  BipartiteRamsey` (~1600 lines total). Kills the "nothing in mathlib"
  problem.
- **`MonadicDependence/NowhereDenseBridge`** (965 lines): shallow-minor
  nowhere-denseness ⟺ local subdivision-based nowhere-denseness — this
  IS the step-1 bridge (candidate paths → Ramsey-uniform length →
  canonical pattern → trim → clean subdivision). **CORRECTION (found
  during the port): NOT done both directions.** Forward (local ⇐
  shallow-minor) is proved; the backward direction — the load-bearing
  one for 13.7 — has its steps 1–3 proved but steps 4–6 (trim paths,
  build subdivision, extract bound) left as `sorry` scaffold leaves.
  The catalog's `formalization-notes.md` has a detailed close plan;
  step 4 alone is estimated there at 1–2 focused sessions and wants
  strengthening of steps 1–3 (IsPath walks, shared-suffix pattern bits,
  interior-collision handling via a thicker step-3 Ramsey or an extra
  Ramsey round).
- **`MonadicDependence/SubdividedBicliqueRamsey`** (2445 lines): thesis
  Lemma 13.8 (subgraph subdivided biclique ⇒ biclique or induced
  r′-subdivided biclique), already done.
- **`MonadicDependence/WeaklySparseMonDepIsNowhereDense`** (439 lines):
  the 13.7 glue (negate ND, r = 0 biclique case, r ≥ 1 via 13.8 +
  pigeonhole) — reusable as a template, but its endpoint differs (below).
- Support defs: `Subdivision`, `Biclique`, `WeaklySparse`, local
  `NowhereDense`, crossing definitions.

**Definition mismatches to bridge during the port** (the catalog's
`GraphClass` is instance-carrying over arbitrary vertex types; Lax5's is
`∀ n, SimpleGraph (Fin n) → Prop`; the 4c ports already established the
translation pattern):

1. Catalog `IsNowhereDense` (shallow minor) ↔ concept
   `Lax5.NowhereDenseClasses.NowhereDense` — same content, encoding glue.
2. Catalog `IsWeaklySparse` ↔ concept `WeaklySparse` (`⊑` vs
   `IsContained` — same notion, small glue).
3. **The real gap**: catalog `IsMonadicallyDependent` is the thesis
   Thm 2.3(3) forbidden-patterns characterization; our concept is
   transduction-based. We do NOT port that definition or Thm 2.3.
   Instead, the final step of 13.7 ("star r′-crossings are forbidden in
   mon dep classes", definitional in the catalog) becomes a real
   transduction argument for us — and only the *star* case is needed:
   13.8's output is honest induced subdivided bicliques, so flips,
   clique/half-graph crossings and comparability grids are all skipped.

## The one genuinely new proof: star-crossing transduction

If `C` contains, for a fixed `ℓ ≥ 1`, induced exact-`ℓ`-subdivided
bicliques of every order, then `Transduces C allGraphs`
(contradicting concept `MonadicallyDependent`). Thesis §2 hardness
picture:

- Colors mark the copy's principals and internal vertices of *kept*
  paths (chosen per target bipartite graph); φ(x,y) = "some path of
  length `ℓ+1` from x to y with all internal vertices blue" (formula by
  recursion on `ℓ`). Induced-ness + exact length confine any such path
  to a single subdivision path of the copy, so φ defines exactly the
  kept adjacency ⇒ `Transduces C allBipartite`.
- Incidence encoding (x~y iff common edge-vertex neighbor) gives
  `Transduces allBipartite allGraphs`; compose with the proved
  `Transduces.trans`. In-repo precedent for this style: the 4b'' [VC]
  proof (common-colored-neighbor formula = the ℓ = 1 case).

## Module plan (proofs package)

- Ports are folded in as native `Lax5Proofs/*.lean` modules (Jan's
  call, superseding the Source/Catalog mirror proposal). **Done for the
  Ramsey batch**: `Ramsey.lean` (two-color `ramsey` + `multicolor_ramsey`),
  `BipartiteRamsey.lean` (`bipartite_ramsey`, `iterated_bipartite_ramsey`),
  `TupleRamsey.lean` (`orderType`, `tuple_ramsey`,
  `bipartite_tuple_ramsey` = thesis Lemma 4.15), `Subdivision.lean`
  (`subdividedClique`, `subdividedBiclique`, `biclique`). Builds green,
  standard axioms only. NowhereDenseBridge and SubdividedBicliqueRamsey
  get the same native treatment in step 2.
- `Lax5Proofs/CrossingTransduction.lean` — the new transduction proof.
- `Lax5Proofs/Corollary6a.lean` — 13.7 glue adapted from
  `WeaklySparseMonDepIsNowhereDense`: concept-encoding bridges (1)(2),
  endpoint replaced by `CrossingTransduction`; rewire `Corollary6.lean`
  to consume the proved theorem (same pattern as the 6b rewiring in 4d);
  re-audit `#print axioms`.

## Order of work

1. ~~Port the Ramsey toolbox + Subdivision/Biclique defs; build green.~~ ✓
2. ~~Port NowhereDenseBridge and SubdividedBicliqueRamsey; build
   green.~~ ✓ (`NowhereDenseBridge.lean` — `IsLocallyNowhereDense`,
   `isLocallyNowhereDense_iff_isNowhereDense`, 3 sorries carried in the
   backward steps 4–6; `SubdividedBicliqueRamsey.lean` —
   `subdividedBiclique_ramsey`, sorry-free, standard axioms.)
2b. **NEW: close bridge backward steps 4–6** (real proof work, size
   comparable to or larger than step 3; see catalog close plan). Options
   to decide with Jan: (a) follow the close plan — strengthen steps 1–3
   (IsPath + suffix bits, or the blown-up interior-tuple Ramsey color
   variant that avoids a separate collision round at the cost of bounds,
   acceptable since the contract is qualitative); (b) any alternate
   route Jan prefers.
3. `CrossingTransduction.lean` (the new work).
4. `Corollary6a.lean` glue + encoding bridges + rewiring + axiom audit;
   update `todo.md`/`pipeline.md`.

Iteration checkpoints with Jan after 2 and 3.

## Open decisions (input wanted)

- ~~**Port location/attribution.**~~ Resolved: fold ports in as native
  `Lax5Proofs/*.lean` modules, native naming, no Source/Catalog mirror.
- **Bipartite→all-graphs**: two-step via `Transduces.trans` (proposed)
  vs a single edge-hub transduction. Two-step is thesis-faithful and
  less formula plumbing.
- **Formalization-notes stance**: bridge + 13.8 credited to thesis
  Ch. 13 (+ folklore for the bridge); transduction step credited to
  thesis §2 / flip-breakability hardness. OK?
