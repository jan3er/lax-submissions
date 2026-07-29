# plans/ — campaign records

Process history of the submissions in this repository: statement designs,
proof-pipeline surveys, per-campaign plans, and overnight relay briefs.
Each file carries its status in its own header. Folder names mirror the
submission directories at the repo root. New campaigns start their plan
and brief files here, not at the root.

**Open campaigns**

| plan | what |
|------|------|
| `nowhere-dense-model-checking/nd-mc-plan.md` | FO model checking is FPT on nowhere dense classes (GKS), rebuilt on the Dreier–Toruńczyk rank-preserving locality theorem (arXiv 2606.23180) instead of the broken GKS locality; splitter game + sparse covers on top of Lax12, RAM realization on Lax13/Lax11. Rev 3 accepted — isolation splitter game, Q1–Q5 closed (Lax3, real-ε bound, colored-graph surface, four citable theorems); P0 starts next session; RAM phases P5–P7 gated on the IMP+ toolkit campaign closing. |
| `word-ram/refinement-tower-plan.md` | port Lammich's refinement stack (NREST → Sepref-style synthesis → purpose-built IR → verified codegen into IMP+) so algorithmic results cost what mathematical results cost: write the algorithm abstractly, synthesize program + invariants + obligations. Fidelity-first charter (stay close to the Isabelle source). Rev 2 accepted 2026-07-29, flags resolved, runs in parallel with ND-MC; P0 (sources + design record, hard review gate) next. |

Everything else is closed.

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
