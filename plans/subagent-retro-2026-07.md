# Subagent retrospective — July 2026 campaigns

Status: COMPLETE 2026-07-30. Cross-cutting process review, no Lean content.
Companion artifact: `worker-brief-template.md` (the compounding output of this
retro — new waves start from it).

## Corpus

Every worker transcript on disk from the July campaigns: **72 subagent
transcripts** across 12 supervisor sessions (2026-07-24 → 07-29), ~50 MB,
4,644 tool calls. Covers: word-RAM relay sessions 12–18, Lax11 V-waves,
submission polish, sparsity/ramsey extraction, IMP+ toolkit phases and P5
retrofits, VC ladder overnight run (S0–S7, B1–B7), ND-MC P1 units and P7
waves (A3, C1–C3, D1–D4, E1–E1c, E2). Workers were Opus `general-purpose`
agents throughout (supervision model holds).

Git was the second source (Jan's suggestion): workers themselves rarely
commit (briefs forbid it; the supervisor commits per wave), so commit
history gives **wave-level** repair signal, not worker-level error signal —
11 of 316 commits since 07-24 carry repair language, concentrated in ND-MC
P7 ("surfaces repaired" ×3, "orderCom no-run defect") and refinement-tower
P7. Used here to identify which waves were rework; the transcripts say why.

## Findings, ranked by cost

### 1. Orientation tax — the dominant overhead (~⅓ of every worker)

Median **35%** of a worker's messages (mean 38%) happen before its first
Write/Edit: re-reading files, re-deriving context the supervisor already
had. For the 300–450-message ND-MC agents that is 60–170 messages of
runway per spawn. Serial re-spawn chains pay it repeatedly:

| chain | task | agents | wall time |
|-------|------|--------|-----------|
| E1 → E1b → E1c | augment `implements` | 3 | 12:08–15:34 (07-29) |
| B4 → B4b → B4c | rung-B `solve_run` | 3 | 00:26–02:19 (07-28) |

Both chains were one obligation each. E1's handoff report estimated "~600
lines remaining" — the obligation was under-scoped at brief time, and each
successor re-oriented from scratch even though the predecessor's final
report was excellent.

**Fixes** (in template): briefs carry a *state-of-the-world* section with
exact `file:line` anchors and the load-bearing definitions inlined, not
pointed at; successor briefs embed the predecessor's report verbatim with
an explicit "trust this, do not re-verify green modules" clause; obligations
whose estimate exceeds ~1 agent-session get split *before* spawning, not
after two handoffs.

### 2. Refutable surfaces caused the largest rework waves (known; now quantified)

The A3 assembly-repair agent alone is 397 messages with 52 error-bearing
tool results — an entire agent spent repairing supervisor-authored
obligation surfaces, followed by further "surfaces repaired" waves (A3, C+D1,
D4). This is the empirical base of the refute-before-prove practice (eight
refutable obligations found mid-proof). Nothing new to decide — the
standing practice (Plausible/`#guard` falsification before proof, python
differential tests for RAM programs) directly targets the biggest avoidable
cost class found in this corpus. The template makes the falsification gate
a named brief section so it cannot be dropped.

### 3. Compile-loop iteration vs LSP iteration

811 `lake build` + 229 `lake env lean` invocations corpus-wide, versus
~220 lean-lsp MCP calls. Partly rational — in parallel waves `lake build
<own module>` *is* the ownership gate, and LSP answers go stale after
edits — but the heavy tail is expensive: the worst agents ran 100+ Bash
calls with dozens of full-build error harvests where `lean_goal` /
`lean_multi_attempt` at the stuck position would have answered in
seconds. Observed costs: two builds blown past 600 s into background, one
whnf-heartbeat death (`Lax15Proofs/Loop.lean`, logged as a Lean trap).
Compliance bright spot: only 2 `lean_build` MCP calls in 72 transcripts —
the "don't rebuild via MCP" rule held.

**Fix**: template states the division explicitly — LSP tools for
tactic-level iteration, `lake build <module>` as a gate you run when you
believe you are done (or to refresh LSP after big edits), never as the
inner loop.

### 4. Shell-idiom file handling bypasses the harness's safety and wastes calls

789 grep/rg + 711 sed/awk/cat/head calls: workers slice files with
`sed -n` instead of Read and rewrite whole files with `cat > file <<EOF`
or python heredocs instead of Edit. Consequences observed: 31
"File has not been read yet" Write/Edit rejections (workers writing
blind), and full-file rewrites that carry silent-clobber risk in shared
worktrees. (Python heredocs for *differential testing* are the good twin —
keep those.)

**Fix**: template hygiene line — Read/Edit for files, `cat >` rewrites only
for files the worker itself created this session.

### 5. Ownership clauses work; their absence had measurable cost

Brief archaeology (all 72 first-messages scanned for protective clauses)
shows the discipline arriving in layers: no-commit clauses from 07-27
noon, worktree pinning from 07-28, strict file-ownership + frozen-imports
+ satellite-file structure from 07-29. The 07-27 sessions ran parallel
agents in the *main checkout*, and their reports carry the bill: repeated
"foreign modified files appeared, left alone" reasoning, and one near-miss
where a worker recommended deleting five files that belonged to a sibling.
The 07-29 ND-MC waves, with full ownership clauses, have zero
contamination incidents — siblings' files explicitly respected in every
report. Conclusion: the current clause set is load-bearing; the template
freezes it so new campaigns don't rediscover it clause by clause.

### 6. Worker report quality is high — canonize the format

The final reports are the best part of the corpus: honest failure
accounting (S4 reverted a non-converging proof *rather than leaving it
half-proved*, with a repair plan filed in NIGHTLOG), defect flags with
severity, "what is frozen / what remains / next action" structure, Lean
traps recorded where the next agent will look. One worker (B4b) even
imposed a correct stop-rule on its own milestone ("if not green by 02:40,
stop — B5+B6 cannot fit"). The template's report section is copied from
the observed best reports, and the revert-don't-half-prove rule is now
explicit.

### 7. External losses (no workflow change)

The first E2 spawn died at 19 messages on the monthly spend limit
(15:35, 07-29); the wave resumed 18:24 after Jan's reset. Pure external
cost, but worth one habit: don't launch a fresh multi-hundred-message wave
when the budget is near its edge — checkpoint first (the E2 re-spawn had
to be re-briefed anyway).

## What was *not* found

Worth recording the nulls: no real rate-limit incidents (an early "139
hits" count was hex-string false positives; remote-search batching is
working), no exact-repeat retry loops beyond 6 corpus-wide, no namespace
violations reported post-audit-gate, no worker ignoring a no-commit or
ownership clause once present, and no dishonest success claims — every
admitted failure checked out as genuinely reported.

## Actions taken

1. `plans/worker-brief-template.md` — checked-in brief template encoding
   findings 1, 3, 4, 5, 6. New waves instantiate it instead of re-deriving
   the clause set from memory.
2. Memory updated: retro pointer + template pointer so future supervisor
   sessions start from the template.
3. No CLAUDE.md change proposed — the clauses are supervisor-to-worker,
   not repo-wide policy.

## Open recommendations for the ND-MC rebase (P0 next)

- Size the tower-rebase obligations against the E1/B4 chain lesson: any
  obligation estimated over one agent-session gets split at brief time.
- Keep the refutation gate as a named section in every rebase brief
  (rebase plan already mandates falsification-first; the template gives it
  a place to live).
- Budget check before launching the long waves.

## Tower-expansion P1.A calibration addendum — 2026-07-31

The first Codex-worker calibration wave used three normal collaboration
subagents on disjoint satellite files plus a read-only reviewer. The
template's ownership and report clauses held: no worker touched a sibling
file, staged, or committed, even though all untracked leaves were visible in
one shared worktree. The inline source pins and exact owned declarations
kept orientation bounded; no successor chain was needed.

The falsification/review split paid twice before supervisor acceptance:

- a fixed-name `hnRefine` instance cannot be promoted to the universally
  name-parametric `hfref` signature (now a compiled negative theorem);
- independently flattening the input and result relations of nested
  dependent composition loses their shared witness (now a compiled
  counterexample and a correlated-residue replacement).

One operational correction entered the template. Seed state must be an
explicit supervisor-provided fact, including the manifest path. A redundant
seed attempt in a fresh worktree hit `ENOSPC` after partially populating the
warm package farm; the edit-free failed worktree was removed and the wave
continued in the already-seeded campaign worktree. Workers therefore never
launch or retry seeding themselves when a manifest is missing.

Jan clarified worker transport during the wave: normal Codex collaboration
subagents are the default; a nested `codex exec` process is unnecessary.
This changes transport only. The same brief, ownership, falsification,
module-build, supervisor-review, and root-build gates remain binding.

## August correction — do not generalize a parallel-wave retro into default workflow

Jan's 2026-08-01 correction supersedes the workflow generalization in the
July conclusions. The July data came from large parallel waves with disjoint
files and cold or isolated checkouts. Its ownership clauses remain useful in
that setting, but “instantiate the full template for every proof worker” was
not a valid repo-wide conclusion.

During the Codex takeover, applying that conclusion universally caused the
process to dominate the proofs:

- already-warm `main` was abandoned for fresh worktrees whose seed cost was
  about ten minutes per submission;
- dependency-ordered Lean leaves were parallelized, adding coordination and
  dirty-tree reasoning without reducing the critical path;
- workers were repeatedly polled or interrupted instead of receiving one
  coherent leaf and an uninterrupted working window;
- source work was delayed while mandatory-looking brief sections, campaign
  plans, and audit records were reconstructed;
- checklist-shaped assignments made plausible semantic weakenings easier to
  miss, so supervisor correction rounds increased.

The corrected default is sequential and source-first: warm `main`, one worker,
one leaf, roughly one uninterrupted hour, semantic review, focused build, and
commit. The full July template is now conditional tooling for an explicitly
requested parallel/isolated wave or a specifically recorded handoff risk.
“Required” means required after selecting that mode, not required before any
worker may prove anything.

This is not a rejection of supervision. The supervisor still owns source
selection, narrow file ownership, semantic and cost review, verification, and
commits. It is a correction in where supervision pays: at the source boundary
and acceptance review, rather than in continuous process narration.
