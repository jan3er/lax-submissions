# lax-submissions

One directory per submission; each holds two Lake packages: `concepts/` (endorsement surface) and `proofs/` (requires `../concepts`).

- Build with `lake build` inside the package directory, `concepts/` before `proofs/`. Keep the build warm — the `lean-lsp` MCP tools time out against a cold build. On a fresh checkout run `lake exe cache get` first to pull the mathlib build cache (minutes instead of hours).
- Toolchain is pinned in each package's `lean-toolchain`, mathlib by git rev in `lakefile.toml`. Never run `lake update`.
- The `lean-lsp` MCP server (`.mcp.json`) gives goal states (`lean_goal`), diagnostics, hover docs, `lean_multi_attempt`, and search (LeanSearch, Loogle, `lean_local_search`). Prefer these over rebuilding to inspect proof state. Remote search tools are rate-limited — batch queries. After changing imports or the toolchain, run `lean_build` to rebuild and restart the LSP; goal/diagnostic answers are stale until then.
