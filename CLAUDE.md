# lax-submissions

One directory per submission; each holds two Lake packages: `concepts/` (endorsement surface) and `proofs/` (requires `../concepts`).

Standing workflow from Jan (2026-08-01): work **sequentially in the already-warm `main` checkout**. Do not create worktrees, seed fresh checkouts, parallelize workers, or add planning/brief ceremony unless Jan explicitly asks for it. Technical briefs are references, not mandatory process; when their seemingly required process sections conflict with this rule, this rule wins. Preserve unrelated WIP, keep each edit narrowly owned, build against the warm package state, review the concrete result, and commit before starting the next task.

The worktree workflow is now opt-in only. If Jan explicitly requests an isolated worktree, enter it before editing and run `.claude/worktree-seed.sh <submission>` once before building or touching lean-lsp. Never run a bare cold `lake build` in a fresh worktree, and never hand-copy or symlink `.lake` between checkouts. To land explicitly requested worktree work, commit its branch, fast-forward `main` from the main checkout, then remove the worktree.

- Build with `lake build` inside the package directory, `concepts/` before `proofs/`. Keep the build warm — the `lean-lsp` MCP tools time out against a cold build. On a fresh checkout run `lake exe cache get` first to pull the mathlib build cache (minutes instead of hours).
- Toolchain is pinned in each package's `lean-toolchain`, mathlib by git rev in `lakefile.toml`. Never run `lake update`.
- Commit at the end of every task (stage only the task's files; leave Jan's unrelated WIP unstaged).
- Campaign plans, night briefs, and other process records live in `plans/<submission-name>/` (index and old-name map in `plans/README.md`). Never leave them at the repo root; the root holds only `README.md`, `CLAUDE.md`, and `NIGHTLOG.md`.
- Proof-worker subagent briefs are instantiated from `plans/worker-brief-template.md`; the sections marked (required) never drop. Evidence base: `plans/subagent-retro-2026-07.md`.
- The `lean-lsp` MCP server (`.mcp.json`) gives goal states (`lean_goal`), diagnostics, hover docs, `lean_multi_attempt`, and search (LeanSearch, Loogle, `lean_local_search`). Prefer these over rebuilding to inspect proof state. Remote search tools are rate-limited — batch queries. After changing imports or the toolchain, run `lean_build` to rebuild and restart the LSP; goal/diagnostic answers are stale until then.
