#!/usr/bin/env bash
# Seed a fresh worktree of lax-submissions so its first build is incremental
# instead of cold. Pure file copy — no build step, no arguments. Usage, from
# anywhere inside the worktree:
#
#   .claude/worktree-seed.sh
#
# For every package in the main checkout, copy into the worktree:
#   - .lake/build                    the package's own compiled artifacts
#     (all submissions: one submission's build reaches into another's tree
#     through the sibling overrides);
#   - lake-manifest.json             the locked dependency manifest;
#   - .lake/package-overrides.json   the redirects that resolve mathlib and
#     friends to the machine-wide read-only warm store (~/.lax/warm) in place
#     — no clone, no .lake/packages tree at all — plus the cross-submission
#     entries sibling-overrides.sh adds.
#
# All three are checkout-independent: warm-store overrides use absolute store
# paths, sibling overrides are relative, and the worktree replicates the repo
# layout. Lake's content-hash traces rebuild whatever differs, so a stale copy
# costs nothing but the rebuild it saves. If a package in main has no
# manifest/overrides yet (never built there), run
# `lax build --only proofs <submission>` once for it instead.
set -euo pipefail

top=$(git rev-parse --show-toplevel)
main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")

if [ "$top" = "$main" ]; then
  echo "worktree-seed: already in the main checkout; nothing to seed"
  exit 0
fi

for pkg in "$main"/*/concepts "$main"/*/proofs; do
  [ -d "$pkg" ] || continue
  rel=${pkg#"$main"/}
  for f in .lake/build .lake/package-overrides.json lake-manifest.json; do
    src="$pkg/$f"
    dest="$top/$rel/$f"
    [ -e "$src" ] || continue
    [ -e "$dest" ] && continue
    mkdir -p "$(dirname "$dest")"
    cp -a "$src" "$dest"
  done
done
echo "worktree-seed: builds, manifests, and overrides copied from $main"

# Point the rev-pinned cross-submission requires at *this* worktree, in case
# main was last left in `lax build` state (which drops those redirects).
cd "$top" && .claude/sibling-overrides.sh
