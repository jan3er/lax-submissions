#!/usr/bin/env bash
# Prepare a machine and a checkout for lax submission development: everything
# needed before the first `lake build`, and nothing that belongs to a
# particular submission. Idempotent, non-interactive, no arguments:
#
#   .claude/dev-setup.sh
#
# It is the whole-machine counterpart of worktree-seed.sh. That script seeds a
# *worktree* from a warm main checkout; this one creates the warmth in the
# first place, on a container that has none.
#
# The work splits in two, along the line the cloud environment cache draws:
#
#   the machine half   `.claude/cloud-setup.sh` — the lax CLI, elan and the
#                      pinned toolchain, the warm mathlib store. Lives under
#                      ~/.elan and ~/.lax, shared by every checkout on the
#                      machine, ~4 min cold. Belongs in the environment's
#                      **Setup script** field, whose filesystem snapshot is
#                      reused by later sessions; this script just calls it, and
#                      the call costs ~3 s once the snapshot has it.
#
#   the checkout half  steps 2 and 3 below — the archive database refresh and
#                      each package's lake-manifest.json and
#                      .lake/package-overrides.json. Per-checkout, gitignored,
#                      and cheap, so it runs on every session start: the
#                      repository is cloned fresh each time, lakefiles move as
#                      the campaign moves, and archive records go stale
#                      whenever a dependency is re-submitted.
#
# So a cloud session normally runs the machine half from its cached snapshot
# and only the checkout half at session start. Running this whole script is
# still correct anywhere — a laptop, a worktree, a container whose cache
# expired — because the machine half short-circuits when it is already done.
#
# Neither half touches the submissions' own `.lake/build`, so a fresh checkout
# still compiles each package once. Two optional knobs close that gap, both
# unset by default:
#
#   LAX_SEED_CAPTURES=all            install the archive's published build
#   LAX_SEED_CAPTURES="word-ram ..." artifacts from ghcr instead of compiling
#                                    (`.claude/capture-seed.sh`, seconds). The
#                                    usual choice — but it can only help where
#                                    the tree still matches a submitted commit.
#   LAX_SETUP_BUILD="word-ram ..."   compile those submissions' packages,
#                                    concepts before proofs. What you need when
#                                    the working tree has moved past the last
#                                    submission and no capture matches it.
#
# What it deliberately does not do: `lax login` (a browser device flow) and
# anything that talks to the archive server. Submitting is Jan's step, from
# Jan's machine.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"

step() { printf '\n=== dev-setup: %s\n' "$1" >&2; }
note() { printf '    %s\n' "$1" >&2; }

# --- 1. the machine half ---------------------------------------------------

"$root/.claude/cloud-setup.sh"

npm_root=$(npm root -g)
export LAX_DIST="$npm_root/lax-archive/dist"
export REPO_ROOT="$root"

# --- 2. the archive database clone -----------------------------------------
# Cross-submission requires are pinned to these records, and re-submitting a
# dependency moves its record — so this is refreshed per session, not cached
# with the machine half. Non-fatal: a checkout with no cross-submission edges
# builds without it, and a stale record is a mismatch sibling-overrides.sh
# reports by name.

step "archive database"
if lax pull-db >&2; then
  note "records at $HOME/.lax/lax-database"
else
  note "WARNING: pull-db failed; cross-submission pins cannot be resolved"
fi

# --- 3. the per-package generated files ------------------------------------
# seedManifest writes the complete manifest (path requires first, then the warm
# workspace's locked mathlib closure verbatim) and seedOverrides the redirects
# to the store, exactly as `lax build` would — so lake resolves nothing,
# clones nothing, and runs no post_update hook. Only packages missing a file
# are touched; an existing pair may already carry sibling entries, and
# rewriting it from the pins alone would drop them.

step "package manifests and overrides"
node --input-type=module <<'JS'
import fs from "node:fs";
import path from "node:path";
const warm = await import(`file://${process.env.LAX_DIST}/submission-validation/host/warmstore.js`);
const ws = warm.warmDir();
const root = process.env.REPO_ROOT;

if (!warm.warmReady(ws)) {
  console.error(`    skipped: no warm store at ${ws}; nothing to point the overrides at`);
  process.exit(0);
}

/** Every [[require]] of a lakefile. They are the whitelisted TOML the spec
 * allows, so the same line scanner sibling-overrides.sh uses is enough. */
function requires(file) {
  const found = [];
  let cur = null;
  for (const raw of fs.readFileSync(file, "utf8").split("\n")) {
    const line = raw.trim();
    if (line === "[[require]]") { cur = {}; found.push(cur); continue; }
    if (line.startsWith("[")) { cur = null; continue; }
    const m = /^(\w+)\s*=\s*"([^"]*)"$/u.exec(line);
    if (m && cur !== null) cur[m[1]] = m[2];
  }
  return found;
}

let seeded = 0, kept = 0;
for (const submission of fs.readdirSync(root).sort()) {
  for (const kind of ["concepts", "proofs"]) {
    const dir = path.join(root, submission, kind);
    const file = path.join(dir, "lakefile.toml");
    if (!fs.existsSync(file)) continue;
    if (fs.existsSync(path.join(dir, "lake-manifest.json")) &&
        fs.existsSync(path.join(dir, ".lake", "package-overrides.json"))) { kept++; continue; }
    // Path requires are the ones lake resolves in-tree: a proof package's own
    // '../concepts', plus the sibling requires the one unpinnable pair still
    // carries. Rev-pinned cross-submission requires are sibling-overrides.sh's
    // job — it reads the archive records this script cannot invent.
    const deps = requires(file)
      .filter((r) => r.path !== undefined)
      .map((r) => ({ name: r.name, dir: r.path }));
    warm.seedManifest(ws, dir, deps);
    warm.seedOverrides(ws, dir);
    seeded++;
  }
}
console.error(`    seeded ${seeded} package(s), left ${kept} existing pair(s) alone`);
JS

# The cross-submission half: rev-pinned requires redirected to this checkout's
# sibling folders. Reports every pin that no longer matches its archive record.
"$root/.claude/sibling-overrides.sh" >&2 || \
  note "WARNING: sibling-overrides.sh failed; cross-submission builds will use the pins"

# --- 4. optional: warm the submissions themselves --------------------------
# Two ways, and captures are usually the one you want: seconds and a download
# against minutes of compilation, for any submission whose tree still matches
# the commit the archive built. LAX_SETUP_BUILD compiles the working tree
# instead, which is what you need when it has moved past the last submission.

if [ -n "${LAX_SEED_CAPTURES:-}" ]; then
  step "capture seeding (LAX_SEED_CAPTURES)"
  # "1" or "all" means every submission with a capture; otherwise a folder list
  case "$LAX_SEED_CAPTURES" in
    1|all) "$root/.claude/capture-seed.sh" >&2 || note "WARNING: capture seeding failed" ;;
    *) "$root/.claude/capture-seed.sh" $LAX_SEED_CAPTURES >&2 || note "WARNING: capture seeding failed" ;;
  esac
fi

if [ -n "${LAX_SETUP_BUILD:-}" ]; then
  step "submission builds (LAX_SETUP_BUILD)"
  for submission in $LAX_SETUP_BUILD; do
    for kind in concepts proofs; do
      dir="$root/$submission/$kind"
      [ -d "$dir" ] || continue
      note "lake build in $submission/$kind"
      (cd "$dir" && LAKE_ARTIFACT_CACHE=false lake build >&2) || \
        note "WARNING: $submission/$kind did not build"
    done
  done
fi

# `lax doctor` is the authority on whether this worked, so end with its verdict
# rather than a claim of our own. One problem is expected and correct here:
# `github auth`, which only `lax login`'s browser device flow can satisfy and
# which nothing short of `lax submit` needs.
step "ready"
lax doctor 2>&1 | grep -vE '✓' >&2 || true
