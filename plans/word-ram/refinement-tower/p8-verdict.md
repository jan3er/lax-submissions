# P8 — campaign verdict, ledger review, and handoff

2026-07-31, supervisor-authored. Campaign executed P0–P8 under full
delegated authority (progress log 2026-07-29); Jan evaluates this
record and the artifacts it points to.

## 1. What was built (one paragraph)

A faithful Lean 4 port of the Lammich/Haslbeck cost-carrying
refinement stack — NREST monad with currency costs, Autoref relators
and rule databases, Sepref `hn_refine` synthesis over a purpose-built
word-RAM IR with time-credit separation logic, and (beyond the source,
ledger D3) a *verified* code generator into the endorsed IMP+ `Com`
with constant-factor cost cashing — plus an IICF collections layer
(arrays, trail-backed touched-only arrays, stack, queue, CSR,
bitmask), all under `word-ram/proofs/Lax13Proofs/Refine/`. Programs
written against the abstract NREST layer are synthesized into deep IR
programs mechanically by `sepref`/`sepref_synth`, and cashed into
cells-based `Spec`/`Solves`/`computesInTime` statements. Every phase
closed with a passing, pinned acceptance; the whole tree is
axiom-clean, `lax`-audit-clean, 3,041 build jobs green.

## 2. The P7 gate verdict

Re-derivation of the masked depth-capped BFS (baseline:
`Lax3Proofs/RamBfs.lean`, 1,201 raw lines, cost `51n + 44ns + 30`).

| criterion | target | result |
|---|---|---|
| hand frame/memory clauses | 0 | **PASS — 0** (strict reading: 3 registered `MERGE_arrayAssn_*` DB rules + 1 assertion equation in the export assembly = 4; none applied by hand) |
| authored lines | ≤ 400 | **MISS — 2,957 raw / 1,922 Lean** (1,814 net of the 108-line pinned `Com`), ≈2.5× the baseline raw-for-raw, plus disclosed reuse of P1's `Bfs.lean` graph core |
| supervision interventions | counted | 3 mid-wave authorizations, 2 overload resumes, 1 model switch (infra) |
| cost | — (not a criterion) | `56n + 40ns + 33` **computed** vs `51n + 44ns + 30` hand-tuned — within 12% with zero tuning |
| synthesis | — | whole program (3 nested loops, two-array tuple states) in 49 s, demo green on the baseline's own arena |

**Where the miss lives** (measured, §14 of `BfsQSynth.lean`):

1. **The queue invariant, ≈⅓ of wave A.** The fourteen clauses of the
   baseline's `Frontier`, re-proved at the List level. This cost is
   *intrinsic to queue-BFS at any abstraction level* — the tower
   neither caused nor could remove it. The gate's 400 was calibrated
   as "the math-side share of the original" on the assumption the
   math-side share was small; it is not — it is most of the baseline
   too.
2. **The bounds pass, 560 lines.** The genuinely new cost, the price
   of ledger D-a (the IR's untruncated arithmetic) with no bounded
   types in the representation. P5's toy telemetry ("~10
   lines/program") did not survive contact with a program whose write
   indices are invariant-bounded; the honest mechanism
   (`bigStepB_of_inv` via `bpre`: in-range facts free from the run,
   only creation-site `<B` goals) is now built and reusable, but the
   per-program invariant/walk share remains real.
3. What the tower **did remove is the entire machine half**: no `Run`,
   no `Env`, no `wvars`/`warrs` frame bookkeeping, no symbolic
   execution, no hand frame reasoning anywhere in 2,957 lines. That
   half is roughly the baseline's other ~600 lines *plus* the part of
   its math that is entangled with the machine — and it is the half
   that does not survive program changes.

## 3. Adoption analysis (the decision the gate was for)

Options, in the imp-toolkit-P5-verdict style:

- **(a) Adopt the tower as the default for algorithmic campaigns,
  with eyes open.** The per-program marginal cost after this campaign
  is: abstract program + its correctness (unavoidable anywhere),
  loop variants (small), bounds invariants + walks (the 560-line
  class, shrinking as `bpre` idioms accrete), synthesis annotations
  (small). The frame/machine half — historically the dominant *and
  least reusable* cost, and the one that produced the ND-MC campaign's
  eight refutable obligations — is gone. Recommended when programs
  are frame-heavy, mutation-rich, or expected to be revised.
- **(b) Bounded-value assertions (`wordAssn`) retrofit.** Re-opened by
  P7: P5's rejection rested on toy telemetry that did not transfer.
  Moving `<B` into the arithmetic hnr rules would surface bounds as
  synthesis side conditions (the source's own architecture, where
  machine words carry the bound in the type) and could retire most of
  the 560-line class — at the price of a full P4 rule-layer thaw and
  side-condition traffic in every synthesis. Worth a one-session spike
  before the next big algorithmic campaign, not worth blocking one on.
- **(c) Keep both stacks.** Direct `Spec` proofs for small,
  frame-light programs (the P5 harness and kit remain first-class);
  the tower for the rest. This is the de-facto state and costs
  nothing to keep.

**Supervisor recommendation: (a) + the (b) spike.** The gate's line
criterion missed, but the thing it was a proxy for — eliminating the
non-reusable machine-half labor and its defect class — was achieved,
measured, and is visible in the artifact.

## 4. Deviation-ledger review (final)

- **D1** (Lean substrate) — held; the one structural surprise was
  Lean-simp's refusal of `SP`-congruence blocking → explicit
  `rewriteDB` walker (P4/B2), and weak HO unification → first-order
  `absAgree` pre-match (P7/D-bg). Both are the D1 class, both pinned.
- **D2** (word-RAM IR, not LLVM) — held end to end; parametric-w
  statements land at `computesInTime` (P5) and the cells-based `Spec`
  (P7) exactly as intended.
- **D3** (verified codegen) — delivered; cash factor exactly 4,
  simulation without `Classical.choice`.
- **D4** (refute-before-prove) — earned its keep repeatedly: refuted
  the P5 design's side-condition placement, defeq-mop collision,
  self-caught a wrong CSR cross-check, and killed the unsound route-2
  bounds lemma before it was built.
- **D5** (trail arrays default) — built, with the touched-only cost
  theorem (`treset_cost_touched_only`); not yet exercised by a
  recursive-arena consumer.
- **D6** (no recursion, loop-form only) — never pinched; every P7
  loop is `while`-form.
- **N1** (SL at the synthesis layer) — vindicated: the SL is what the
  solver consumes; the human writes none of it (frame criterion PASS).
- **N2** (own small SL, not iris-lean) — held; `fri` + the Sepref
  match rules carried the entire campaign.
- **N3** (tape-free tower, one boundary wrapper) — held; the P5
  harness is that wrapper, and the P7 export needed no tapes at all.
- **New, recorded in-phase:** destination-descriptor `hnRefine`
  (P4/D-a), invalid/dead/junk ownership split (P4/D-c), MK_FREE as
  entailment (P4/D-d), fused-guard `CondRefine` (P4/D-af),
  `monadicWhileIT` as the exchangeable loop (P4/D-ea), composite
  assertions opaque to the matcher → raw-synthesis + wrapper idiom
  (P6/D-bc), `bpre`/`bigStepB_of_inv` (P7/D-bk).

## 5. Handoff notes (for the next campaign or thaw wave)

**Traps (will bite again):** `omega` is blind through the `Ir.Val`
abbrev — bind indices at `ℕ`; `decide` times out on string-chain
arithmetic — use `decide +kernel`; `split at` on library matches
leaks splitters the root `lax` audit catches and `lake build` does
not; scratch cells are consumed from the precondition in written
order; the operator phase does not backtrack across rule choice —
order junk cells so junk-destination rules cannot misfire (or use
`mopSucc`-style dedicated in-place ops).

**Thaw queue (single wave, low risk, none blocking):** dedupe the
P6-A/P6-B convention pair (`hnRefine_res_cast'`≙`hnRefine_reinterp`
etc.); move `mopPair`/`ExchOk`/`irWhileIT_mono` to their named homes;
fold `le_spec_of_bindT_returnT` + `bindT_returnT_gen` into
`NREST/Pw.lean`; move `filled` out of `Examples/ArrayFill`; P1 export
of `RECT` fuel-stability retires `LOOP_VARIANT` wholesale (the single
best ergonomic improvement available); symmetric rule-side `prodAssn`
splitting in `frameMatch`; `mop_move` with a live destination.

**Open items, disclosed:** `inres` never ported (P2 carry-over,
unneeded so far); dependent `hfcomp`; abstract-twin equalities
(`fcCountOf = List.filter.length`-class) `#guard`ed not proved;
`sepref_copy_rules` empty; the (b) spike above.

**Landing:** campaign branch `worktree-refine-p0`; main gained only
ND-MC files since the branch point (no overlap) — merge from the main
checkout is clean. The worktree stays until Jan retires it.
