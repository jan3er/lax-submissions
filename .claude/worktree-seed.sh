#!/usr/bin/env bash
# Seed a fresh worktree of lax-submissions so its first build is incremental
# instead of cold. Usage, from anywhere inside the worktree:
#
#   .claude/worktree-seed.sh <submission> [<submission>...]
#
# Two steps:
#   1. Copy every package's own `.lake/build` from the main checkout (all
#      submissions — sibling path requires mean one submission's build can
#      reach into another's tree). Lake's content-hash traces rebuild whatever
#      differs, so a stale copy costs nothing but the rebuild it saves.
#   2. `lax build --only proofs` each named submission: writes the gitignored
#      `lake-manifest.json` and `.lake/package-overrides.json`, which resolve
#      mathlib and friends to the machine-wide read-only warm store
#      (~/.lax/warm) in place — no clone, no hardlinks, no `.lake/packages`
#      tree in the submission at all. Without them plain `lake build` would
#      re-resolve and re-clone mathlib.
set -euo pipefail

top=$(git rev-parse --show-toplevel)
main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")

if [ "$top" != "$main" ]; then
  for build in "$main"/*/concepts/.lake/build "$main"/*/proofs/.lake/build; do
    [ -d "$build" ] || continue
    dest="$top/${build#"$main"/}"
    [ -e "$dest" ] && continue
    mkdir -p "$(dirname "$dest")"
    cp -a "$build" "$dest"
  done
fi

[ $# -gt 0 ] || echo "worktree-seed: build dirs copied; pass submission names to also seed manifests (lax build --only proofs <submission>)"
for sub in "$@"; do
  (cd "$top" && lax build --only proofs "$sub")
done
