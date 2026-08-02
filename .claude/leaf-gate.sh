#!/usr/bin/env bash
# Per-leaf acceptance gates as one command (tower-expansion-plan.md, gate
# law; ledger E31). Usage, from anywhere inside the checkout:
#
#   .claude/leaf-gate.sh <submission> [--no-consumer]
#
# Runs the mechanical checks a leaf must pass on the day it lands:
#   - concepts then proofs `lake build` (independent replay, not the
#     worker's report)
#   - `lax build --only proofs <submission>` (root-module + namespace
#     audit; its violation output is the report)
#   - the ND-MC consumer compile gate, unless --no-consumer or the leaf
#     IS the consumer (skip it only when the leaf touches no exported
#     surface)
# and prints, for gate (iii), the ledger's last entry and last commit —
# the entry-precedes-landing check is the supervisor's, not automatable.
#
# Exit 0 = mechanical gates green (gate iii still needs the supervisor).
set -u

sub="${1:?usage: leaf-gate.sh <submission> [--no-consumer]}"
shift || true
run_consumer=1
[ "${1:-}" = "--no-consumer" ] && run_consumer=0

consumer="nowhere-dense-model-checking"
root="$(cd "$(dirname "$0")/.." && pwd)"
fail=0

step() { printf '\n== %s\n' "$1"; }

step "$sub/concepts: lake build"
( cd "$root/$sub/concepts" && lake build ) || fail=1

step "$sub/proofs: lake build"
( cd "$root/$sub/proofs" && lake build ) || fail=1

step "lax build --only proofs $sub (root-module + namespace audit)"
( cd "$root" && lax build --only proofs "$sub" ) || fail=1

if [ "$sub" != "$consumer" ] && [ "$run_consumer" -eq 1 ]; then
  step "consumer compile gate: $consumer/proofs lake build"
  ( cd "$root/$consumer/proofs" && lake build ) || fail=1
fi

step "gate (iii) reminder — ledger entry must precede the landing"
ledger="$root/plans/word-ram/tower-expansion/ledger.md"
if [ -f "$ledger" ]; then
  printf 'last ledger heading: %s\n' "$(grep '^### ' "$ledger" | tail -1)"
  git -C "$root" log -1 --format='last ledger commit:  %h %ad %s' \
    --date=short -- "$ledger"
fi

echo
if [ "$fail" -eq 0 ]; then
  echo "LEAF GATE: mechanical checks PASS (confirm gate iii manually)"
else
  echo "LEAF GATE: FAIL"
  exit 1
fi
