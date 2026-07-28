# plans/ — campaign records

Process history of the submissions in this repository: statement designs,
proof-pipeline surveys, per-campaign plans, and overnight relay briefs.
Every file here is closed — its status line is in its own header. Folder
names mirror the submission directories at the repo root. New campaigns
start their plan and brief files here, not at the root.

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
