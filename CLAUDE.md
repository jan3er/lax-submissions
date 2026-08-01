# lax-submissions

One directory per submission; each holds two Lake packages: `concepts/` (endorsement surface) and `proofs/` (requires `../concepts`).

Standing workflow from Jan (2026-08-01): work **sequentially in the already-warm `main` checkout**. Do not create worktrees, seed fresh checkouts, parallelize workers, or add planning/brief ceremony unless Jan explicitly asks for it. Technical briefs are references, not mandatory process; when their seemingly required process sections conflict with this rule, this rule wins. Preserve unrelated WIP, keep each edit narrowly owned, build against the warm package state, review the concrete result, and commit before starting the next task.

The default supervisor rhythm is deliberately small:

1. Read the exact pinned source and the immediately relevant landed APIs.
2. Give one worker one coherent leaf, one owned file, and the semantic/build gates that actually determine correctness.
3. Let the worker run uninterrupted for about an hour. Do not poll, interrupt, or ask for status unless new information genuinely changes the task.
4. Review the concrete result for source semantics, preconditions, ownership, and cost claims. A checklist-complete but semantically weakened theorem is not complete.
5. Request only focused corrections, replay the narrow build, update the campaign record briefly, and commit that boundary before selecting the next leaf.

Inherited plans, retrospectives, and briefs are evidence about technical scope; they do not authorize extra workflow. Do not reread or restate the whole campaign when the next source leaf is already known. Do not create a plan document, worker brief, audit matrix, or parallel wave merely because an older document has a section for one. The proof is the work; process exists only when it removes a demonstrated risk.

Jan explicitly authorizes and requires staging and committing task-owned files throughout this project. Do not stop to re-request permission at an ordinary completed boundary. Stage only the files belonging to that boundary and leave unrelated WIP alone.

The worktree workflow is now opt-in only. If Jan explicitly requests an isolated worktree, enter it before editing and run `.claude/worktree-seed.sh <submission>` once before building or touching lean-lsp. Never run a bare cold `lake build` in a fresh worktree, and never hand-copy or symlink `.lake` between checkouts. To land explicitly requested worktree work, commit its branch, fast-forward `main` from the main checkout, then remove the worktree.

- Build with `lake build` inside the package directory, `concepts/` before `proofs/`. Keep the build warm — the `lean-lsp` MCP tools time out against a cold build. On a fresh checkout run `lake exe cache get` first to pull the mathlib build cache (minutes instead of hours).
- Toolchain is pinned in each package's `lean-toolchain`, mathlib by git rev in `lakefile.toml`. Never run `lake update`.
- Commit at the end of every task (stage only the task's files; leave Jan's unrelated WIP unstaged).
- Campaign plans, night briefs, and other process records live in `plans/<submission-name>/` (index and old-name map in `plans/README.md`). Never leave them at the repo root; the root holds only `README.md`, `CLAUDE.md`, and `NIGHTLOG.md`.
- `plans/worker-brief-template.md` is conditional tooling for an explicitly requested parallel/isolated wave or an unusually risky handoff. Default sequential workers receive the compact task packet defined at the top of that file. “Required” sections are required only after the supervisor deliberately chooses the full template. The August correction in `plans/subagent-retro-2026-07.md` explains why the July parallel-wave findings must not be generalized into default ceremony.
- The `lean-lsp` MCP server (`.mcp.json`) gives goal states (`lean_goal`), diagnostics, hover docs, `lean_multi_attempt`, and search (LeanSearch, Loogle, `lean_local_search`). Prefer these over rebuilding to inspect proof state. Remote search tools are rate-limited — batch queries. After changing imports or the toolchain, run `lean_build` to rebuild and restart the LSP; goal/diagnostic answers are stale until then.
