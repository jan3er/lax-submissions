#!/usr/bin/env bash
# Prepare a machine for lax submission development: everything a checkout of
# this repository needs before the first `lake build`, and nothing that belongs
# to a particular submission. Idempotent, non-interactive, no arguments:
#
#   .claude/dev-setup.sh
#
# It is the whole-machine counterpart of worktree-seed.sh. That script seeds a
# *worktree* from a warm main checkout; this one creates the warmth in the
# first place, on a container that has none — which is what a fresh Claude Code
# on the web session is. `.claude/hooks/session-start.sh` runs it at session
# start so the agent wakes up able to build.
#
# The five things it installs, in dependency order:
#
#   1. the lax CLI          npm package `lax-archive`; also the source of the
#                           archive pins every later step reads, so it goes
#                           first (~5 s).
#   2. elan + the toolchain elan itself is instant, but it installs toolchains
#                           lazily — the 2.7 GB `leanprover/lean4:v4.30.0`
#                           download otherwise lands on whoever first types
#                           `lean`. Installed eagerly here (~40 s).
#   3. the database clone   ~/.lax/lax-database, the archive records
#                           sibling-overrides.sh resolves cross-submission
#                           pins against (~5 s).
#   4. the warm store       ~/.lax/warm/<toolchain>-<mathlibrev>: mathlib at
#                           the archive pin, downloaded via `lake exe cache
#                           get` and built once. This is the expensive step
#                           (4.6 GB of artifacts, 7.5 GB on disk) and the one
#                           that makes every later build incremental. Built by
#                           calling the CLI's own ensureLocalWarm, so it can
#                           never drift from the pins `lax build` enforces.
#                           The CLI warns it takes 10-30 minutes; measured
#                           here on a web container, 177 s.
#   5. the generated files  each package's lake-manifest.json and
#                           .lake/package-overrides.json, written by the CLI's
#                           own seedManifest/seedOverrides — the redirects that
#                           resolve mathlib to the warm store in place, with no
#                           clone and no .lake/packages tree in the submission.
#                           Then sibling-overrides.sh adds the
#                           cross-submission half.
#
# Steps 1-4 live outside the repository, under ~/.elan and ~/.lax, and are
# shared by every checkout and worktree on the machine. Step 5 is per-checkout
# and gitignored. Existing generated files are left alone, so running this over
# a checkout that already builds costs seconds and changes nothing. Measured
# 2026-08-08 on a fresh web container: ~4 min cold end to end, 3 s warm.
#
# Optional: LAX_SETUP_BUILD="finite-ramsey word-ram" also runs `lake build` in
# those submissions' packages (concepts before proofs), so the session wakes
# with their artifacts on disk too, not just mathlib's. Unset by default —
# a cold submission build is hours, not minutes.
#
# What it deliberately does not do: `lax login` (a browser device flow) and
# anything that talks to the archive server. Submitting is Jan's step, from
# Jan's machine.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"

step() { printf '\n=== dev-setup: %s\n' "$1" >&2; }
note() { printf '    %s\n' "$1" >&2; }

# --- 1. the lax CLI --------------------------------------------------------
# It carries the archive pins, so it has to exist before anything reads them.
# Only installed when missing: a session start is no place to silently move the
# CLI (and with it the pins) under a running campaign. Upgrade deliberately,
# with `lax update`.

step "lax CLI"
if command -v lax >/dev/null 2>&1; then
  note "already installed: $(lax --version)"
else
  npm install -g lax-archive >&2
  note "installed: $(lax --version)"
fi

# Every later step reads the pins and the warm-store helpers straight out of
# the installed CLI, so this script can never enforce a different environment
# than `lax build` does. LAX_DIST carries the module directory into each node
# heredoc below; the heredocs are quoted, so nothing in them is shell-expanded.
npm_root=$(npm root -g)
export LAX_DIST="$npm_root/lax-archive/dist"
export REPO_ROOT="$root"

toolchain=$(node --input-type=module <<'JS'
const pins = await import(`file://${process.env.LAX_DIST}/submission-validation/pins.js`);
process.stdout.write(pins.LEAN_TOOLCHAIN);
JS
)

# --- 2. elan and the pinned toolchain --------------------------------------

step "Lean toolchain ($toolchain)"
if ! command -v elan >/dev/null 2>&1; then
  curl -sSf https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --default-toolchain none >&2
  export PATH="$HOME/.elan/bin:$PATH"
fi
# Unlike the installer's --default-toolchain, this actually downloads — but it
# is an error, not a no-op, when the toolchain is already there, so guard it.
if elan toolchain list 2>/dev/null | grep -qF "$toolchain"; then
  note "already installed"
else
  elan toolchain install "$toolchain" >&2
fi
elan default "$toolchain" >&2
note "$(lean --version)"

# --- 3. the archive database clone -----------------------------------------
# Cross-submission requires are pinned to these records. Non-fatal: a checkout
# with no cross-submission edges builds without it, and the failure mode we
# care about (a stale or missing record) is one sibling-overrides.sh reports.

step "archive database"
if lax pull-db >&2; then
  note "records at $HOME/.lax/lax-database"
else
  note "WARNING: pull-db failed; cross-submission pins cannot be resolved"
fi

# --- 4. the warm mathlib store ---------------------------------------------
# The expensive one. ensureLocalWarm returns immediately when the store is
# already marked ready, so this is a no-op on every run but the first.

step "warm mathlib store"
node --input-type=module <<'JS'
const warm = await import(`file://${process.env.LAX_DIST}/submission-validation/host/warmstore.js`);
const ws = warm.warmDir();
if (warm.warmReady(ws)) {
  console.error(`    already built: ${ws}`);
} else if ((await warm.ensureLocalWarm({ echo: true })) === undefined) {
  console.error("    FAILED: the warm store was not built; see the log above");
  process.exit(1);
}
JS

# --- 5. the per-package generated files ------------------------------------
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

# --- 6. optional: warm the submissions themselves --------------------------

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
