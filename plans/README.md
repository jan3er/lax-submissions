# plans/ — campaign records

Process history of the submissions in this repository: statement designs,
proof-pipeline surveys, per-campaign plans, and overnight relay briefs.
Each file carries its status in its own header. Folder names mirror the
submission directories at the repo root. New campaigns start their plan
and brief files here, not at the root.

**Open campaigns**

| plan | what |
|------|------|
| `nowhere-dense-model-checking/nd-mc-plan.md` | FO model checking is FPT on nowhere dense classes (GKS), rebuilt on the Dreier–Toruńczyk rank-preserving locality theorem (arXiv 2606.23180) instead of the broken GKS locality; splitter game + sparse covers on top of Lax12, RAM realization on Lax13/Lax11. Math core P0–P4 complete; P5/P6 done; P7 correctness half done 2026-07-29 (`driverRoot_decides_sentence`, kernel-three). The P7 cost wave is **frozen as fallback** — superseded 2026-07-30 by the rebase plan below; only C0 + P8 remain, and they land there. |
| `nowhere-dense-model-checking/nd-mc-rebase-plan.md` | the ND-MC RAM program layer re-derived through the refinement tower against the frozen correctness-half spec surface; C0 discharged on tower-computed costs (touched-only via trail arrays), then draft submission. Rev 1 OPEN 2026-07-30, direction approved by Jan (fastest-to-rebased, no eval gates); P0 = tower readiness (dependent `hfcomp`, `wordAssn` spike, `RECT` fuel-stability, trail-array acceptance) with a hard fallback checkpoint; FLAGs 1–3 open, none blocking. |

**Proposed campaigns**

| plan | what |
|------|------|
| `pcp-theorem/pcp-plan.md` | the PCP theorem by Dinur gap amplification — the first formal hardness artifact in any assistant. Machine-free Amplification Theorem as the P7 flagship (explicit size-linear gap-doubling transformation on constraint graphs, no machine model anywhere); PCP proper at P8 over the word RAM with tower-verified reduction cost. Five-submission ladder: `constraint-graphs/`, `spectral-expanders/`, `linearity-testing/`, `gap-amplification/`, `pcp-theorem/`. Rev 1 PROPOSAL 2026-07-29, queued behind the RAM campaigns (flag 2 resolved by Jan same day: waits until the dust settles on tower + ND-MC RAM) — flags 1, 3, 4 (charter scope, NP-over-RAM surface, split) open. |

Everything else is closed — most recently
`word-ram/refinement-tower-plan.md` (P0–P8 in three sessions; closing
verdict and adoption analysis in `word-ram/refinement-tower/p8-verdict.md`,
adoption resolved 2026-07-30 by the ND-MC rebase decision).

The live cross-campaign log stays at the root (`NIGHTLOG.md`) and cites
these files by their original root-level names. The map:

| then (repo root)                                            | now                                          |
|-------------------------------------------------------------|----------------------------------------------|
| `design.md`, `pipeline.md`, `cor6a-plan.md`, `adleradler-plan.md` | `monadic-dependence-neighborhood-complexity/` |
| `todo.md`                                                   | `monadic-dependence-neighborhood-complexity/implementation-log.md` |
| `ram-stack-plan.md`                                         | `ram-linear-time/`                           |
| `cc-night-brief.md`                                         | `ram-linear-time/ram-stack-night-brief.md`   |
| `courcelle-plan.md`, `courcelle-night-brief.md`             | `ram-linear-time/`                           |
| `word-ram-plan.md`                                          | `word-ram/`                                  |
| `sparsity-lectures-plan.md`                                 | `sparsity-lectures/`                         |
| `ramsey-fundamentals-plan.md`                               | `finite-ramsey/`                             |
| `vc-ladder-plan.md`, `vc-night-brief.md`, `vc-fib-plan.md`, `vc-fib-night-brief.md`, `vc-rung-b-plan.md`, `vc-contracts/` | `vertex-cover-ladder/` |
| `submission-polish.md`                                      | `./` (cross-cutting)                         |

The two renames fix misleading names: `todo.md` was a completed
implementation log with no open tasks, and `cc-night-brief.md` was the
relay brief for the `ram-stack-plan.md` step-6 campaign (the `CC.lean`
driver), not a Courcelle document.
