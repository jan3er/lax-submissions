#!/usr/bin/env bash
# SessionStart hook: make a fresh Claude Code on the web container able to
# build before the agent's first turn. All the work is in
# `.claude/dev-setup.sh`; this wrapper only decides whether to run it and
# publishes the environment the session then needs.
#
# Synchronous on purpose. The measured cold run is about five minutes and the
# hook budget is ten, and the whole point is that the session wakes up warm —
# an async hook would let the agent start `lake build` or the lean-lsp tools
# against a half-installed toolchain, which is the one failure this is meant
# to prevent. Later sessions on a cached container re-run it in seconds.
#
# Local checkouts are left alone: Jan's machine is already warm, and its store
# is the source worktree-seed.sh copies from.
set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ] && [ -z "${LAX_SETUP_FORCE:-}" ]; then
  exit 0
fi

root="${CLAUDE_PROJECT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

# Published to every shell of the session:
#   elan's bin       lake and lean, installed under $HOME by dev-setup.sh;
#   the artifact
#   cache off        with it on, lake writes .hash files beside the shared
#                    oleans, which the sealed read-only store fails with
#                    EACCES (warmstore.ts). It is already off by default at
#                    the pinned lake v4.30.0 — verified here by a bare `lake
#                    build` against the sealed store — so this is belt and
#                    braces: it is what every lax build path sets explicitly,
#                    and it keeps a hand-run `lake build` identical to them
#                    even if that default ever moves.
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  {
    echo 'export PATH="$HOME/.elan/bin:$PATH"'
    echo 'export LAKE_ARTIFACT_CACHE=false'
  } >> "$CLAUDE_ENV_FILE"
fi

"$root/.claude/dev-setup.sh"
