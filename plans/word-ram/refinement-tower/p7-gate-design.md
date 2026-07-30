# P7 design note — the gate: RamBfs re-derived through the tower

2026-07-30, supervisor-authored.

## Target and metrics (from the plan)

Re-derive the masked depth-capped BFS, exporting a statement of the
shape of `bfs_spec` (nowhere-dense-model-checking
`Lax3Proofs/RamBfs.lean:1064`): a cells-based
`Spec B (cells n,src,off,tgt,alv,dist,q hold the input) (program)
(∃ D, dist = arrOf n D ∧ ∀ v, ∀ k ≤ d, D v ≤ k ↔ distance-threshold)
(linear in n, ns)`. Gate: **authored ≤ 400 lines** (abstract program +
abstract proof + annotations + patches; tower and library excluded),
**zero hand frame clauses**, supervision interventions counted.
Baseline: `RamBfs.lean` = 1,201 lines.

Counting rule (fixed now, both sides measured identically): raw wc of
the BFS-specific files authored in P7. Reuse of P1's
`Refine/Examples/Bfs.lean` (1,051 lines, the level-based abstract BFS
with `bfsAlg_correct`, WD lemmas, cost potential) is *reported
separately*: it was P1's acceptance artifact, already banked; P7
imports it as library but discloses the dependency in the telemetry so
Jan can judge the accounting either way.

## Package-boundary decision (P7/S-1)

The export lives in word-ram and must NOT import Lax3/Lax12
(cross-submission dependencies would grow word-ram's manifest). So the
exported theorem states the threshold post via P1's own `masked`/`WD`
over the mask derived from the `alv` array (`fun v => alv[v]! ≠ 0`),
at `arrOf`-shaped cells exactly parallel to `bfs_spec`. Shape-match
with `bfs_spec` is made inspectable by pinning the adjacency
characterization (`masked` adjacency = `G.Adj` ∧ both endpoints alive)
next to the export; actual replacement inside Lax3 is out of scope
(it would edit the endorsed ND-MC package) and recorded as such.

## Route

1. **Wave A — the middle refinement (abstract, no P6/P5 dependency).**
   A first-order queue-based program `bfsQ` at the mop/combinator
   layer: dist as `List ℕ` (sentinel `d+1`), one-shot queue as array +
   head/tail indices (the baseline's `Queue.drain` discipline), CSR
   `(off, tgt)` reads, mask reads, all data first-order. Prove
   `bfsQ ≤ (threshold-post SPEC with linear budget)` at the NREST
   layer with `refine_vcg`/`gwp`, reusing Bfs.lean's WD/threshold
   mathematics wherever it fits. Route freedom (flagged): refine off
   `bfsAlg` through `⇓R`, or prove the queue invariant directly
   against `bfsSpec`-shaped post (the Frontier-style invariant:
   queue = current-level remainder ++ next level; expected cheaper —
   the level machinery was built for the potential argument, which
   the direct route re-derives per-vertex). Costs at the ir-mop layer
   + user structural currencies (the P4-acceptance pattern), linear
   `a·n + b·ns + c`.
2. **Wave B — synthesis + export (needs A; P6-B optional).**
   `sepref_synth` on `bfsQ` (plain-array ops; queue-as-indices —
   IicfQueue consumption optional, its own exercise already gates P6),
   bounds via `ir_bound_vcg` (B linear in n, ns, d — the baseline's
   hypotheses `n<B, ns<B, d+1<B, M z<B` are the model), cashing via
   `spec_of_hnRefine` (P5), the export theorem in bfs_spec's shape,
   demo run on the baseline's five-vertex path with the mask on/off
   (`#guard`), telemetry + gate verdict.

Flag ranges: supervisor P7/S-*; wave A P7/D-a…; wave B P7/D-ba….
