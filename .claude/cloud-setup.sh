#!/usr/bin/env bash
# The machine half of the lax development environment: the lax CLI, elan and
# the pinned toolchain, and the warm mathlib store. Everything here lives
# outside the repository, under ~/.elan and ~/.lax, and is shared by every
# checkout and worktree on the machine. Nothing here reads the checkout — the
# script is deliberately self-contained, so it can run before the repository
# exists.
#
# This is the script to paste into the **Setup script** field of the cloud
# environment dialog at claude.ai/code. That is the only place whose work gets
# cached: Anthropic snapshots the filesystem once the setup script completes
# and reuses that snapshot for every later session, so the ~4 minutes below are
# paid roughly once a week (the cache rebuilds when the script changes, when
# the allowed hosts change, or after about seven days) instead of once per
# session. A SessionStart hook runs after that snapshot is taken, so work done
# there is never cached — which is why the expensive steps live here and not in
# `.claude/hooks/session-start.sh`.
#
# Measured cold 2026-08-08 on a web container, against a five-minute budget:
#
#     lax CLI (npm)                    4 s
#     elan + leanprover/lean4:v4.30.0  39 s   (2.7 GB)
#     warm mathlib store               177 s  (4.6 GB fetched, 7.5 GB on disk)
#     ---------------------------------------
#     total                            ~3 min 40 s
#
# That leaves roughly a minute of headroom. The warm store is one `lake exe
# cache get` download and cannot be split, so if mathlib's CDN has a slow day
# this can overrun five minutes. Overrunning is not fatal — the cache simply
# does not build, and `.claude/dev-setup.sh` from the SessionStart hook
# finishes the job per session instead — but it does mean every session pays
# for it. If that becomes common, the documented escape hatch is to let the
# hook launch the warm build in the background.
#
# Exits zero even when a step fails: a non-zero setup script makes the session
# fail to start outright, and every failure here is one the hook can retry.
set -uo pipefail

export PATH="$HOME/.elan/bin:$PATH"

step() { printf '\n=== cloud-setup: %s\n' "$1" >&2; }
note() { printf '    %s\n' "$1" >&2; }

# --- 1. the lax CLI --------------------------------------------------------
# First, because it carries the archive pins every later step reads. Installing
# it does *not* pull in elan or mathlib: the package has no install scripts and
# seven pure-JS dependencies. The toolchain is a manual prerequisite `lax
# doctor` only points at, and the warm store is built by `lax init` or `lax
# build` — neither of which is reachable here, so this script triggers the
# CLI's own provisioning directly instead.

step "lax CLI"
if command -v lax >/dev/null 2>&1; then
  note "already installed: $(lax --version)"
else
  npm install -g lax-archive >&2 || note "WARNING: npm install failed"
fi

lax_dist="$(npm root -g)/lax-archive/dist"
if [ ! -d "$lax_dist" ]; then
  note "FAILED: the lax CLI is not installed; nothing else can be provisioned"
  exit 0
fi
export LAX_DIST="$lax_dist"

toolchain=$(node --input-type=module <<'JS'
const pins = await import(`file://${process.env.LAX_DIST}/submission-validation/pins.js`);
process.stdout.write(pins.LEAN_TOOLCHAIN);
JS
)

# --- 2. elan and the pinned toolchain --------------------------------------
# elan installs toolchains lazily, so the 2.7 GB download would otherwise land
# on whoever first types `lean` — inside a session, uncached. Force it now.

step "Lean toolchain ($toolchain)"
if ! command -v elan >/dev/null 2>&1; then
  curl -sSf https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --default-toolchain none >&2 || note "WARNING: elan install failed"
  export PATH="$HOME/.elan/bin:$PATH"
fi
# Unlike the installer's --default-toolchain, this actually downloads — but it
# is an error, not a no-op, when the toolchain is already there, so guard it.
if elan toolchain list 2>/dev/null | grep -qF "$toolchain"; then
  note "already installed"
else
  elan toolchain install "$toolchain" >&2 || note "WARNING: toolchain install failed"
fi
elan default "$toolchain" >&2 || true
note "$(lean --version 2>&1 | tail -1)"

# --- 3. the warm mathlib store ---------------------------------------------
# ~/.lax/warm/<toolchain>-<mathlibrev>: mathlib at the archive pin, fetched
# with `lake exe cache get` and built once, then sealed read-only. Every
# submission build replays it in place through package overrides. Built by
# calling the CLI's own ensureLocalWarm, so it cannot drift from the pins `lax
# build` enforces. The CLI warns this takes 10-30 minutes; measured here, 177 s.

step "warm mathlib store"
node --input-type=module <<'JS'
const warm = await import(`file://${process.env.LAX_DIST}/submission-validation/host/warmstore.js`);
const ws = warm.warmDir();
if (warm.warmReady(ws)) {
  console.error(`    already built: ${ws}`);
} else if ((await warm.ensureLocalWarm({ echo: true })) === undefined) {
  console.error("    WARNING: the warm store was not built; the session hook will retry");
}
JS

step "done"
exit 0
