# Worker brief template

Status: **CONDITIONAL** from 2026-08-01.

This template records safeguards that paid for themselves in July's large,
parallel, isolated waves. It is not the default way to assign sequential proof
work. Applying every section to every worker caused a measurable takeover
slowdown: cold worktrees and seeding, repeated orientation, parallel
coordination, status polling, and briefs that became larger than the next proof
leaf.

## Default: compact sequential task packet

On the already-warm `main`, do not instantiate the full template. Give one
worker one coherent leaf containing only:

- the exact pinned source path/commit and the source declarations to preserve;
- the one file the worker owns and the landed APIs it may reuse;
- semantic hazards that could produce a plausible but weaker port;
- the exact focused build and substantive gates for acceptance;
- “touch only this file; do not stage or commit.”

Then leave the worker uninterrupted for roughly an hour. Do not poll it on a
timer. When it finishes, inspect the file itself, request a focused correction
if necessary, replay the build, and commit before assigning the next leaf.
Worker reports may be short: result, build, unresolved defect, and files
touched.

## When the full template applies

Use the sections below only when Jan explicitly requests a parallel or isolated
wave, or when the supervisor records a concrete handoff risk that the compact
packet cannot control. Once the full template is deliberately selected, its
sections marked “required” do not drop. They are requirements of that mode,
not repo-wide ceremony.

---

## 1. Identity and goal (required)

One paragraph: wave name, campaign, the exact declarations to produce
(fully qualified), and what "done" means (module builds green, zero sorry,
statements byte-identical to the surface / new satellite file).

## 2. State of the world (required in full-template mode)

The retro measured a median 35% of every worker's messages spent
re-deriving context the supervisor already had. This section is where that
goes instead. Include *inline*, not as pointers:

- Checkout path, package dir, namespace, green commit, and job count. In the
  default workflow this is the already-warm `main` and there is no seed step.
  If Jan explicitly requested a worktree, also include its **seed state** (the
  exact `lake-manifest.json` checked by the supervisor). The supervisor owns
  that opt-in seed; the worker never launches or retries it.
- The load-bearing definitions and lemma statements the task composes
  against, quoted, with `file:line` anchors.
- What is FROZEN (files, surfaces, imports) vs what the worker owns.
- Known traps relevant to this task (whnf blowups, `set` before
  `simp only`, splitter discipline, …) — copy from NIGHTLOG, don't cite it.

For re-spawns/successors: embed the predecessor's final report verbatim,
plus one line: "Trust this report; do not re-verify modules it declares
green."

## 3. File ownership (required in full-template mode)

The July clause set, verbatim-adaptable — zero contamination incidents
once all four lines were present:

- Create and own `<file(s)>` and ONLY them; imports `<frozen list>`.
- You MUST NOT edit any existing file; sibling agents own their leaves;
  the supervisor wires roots.
- Build ONLY your module: `lake build <Module>` from the proofs dir.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Falsification gate (required in full-template mode for authored obligations)

Refute before prove: before any proof attempt on a *newly authored*
statement, falsify it — `Plausible`, `#guard` on small cases, python
differential tests for RAM programs. If a statement survives no
falsification attempt, say which attempts were run. A refuted statement is
a *result*: record the counterexample and stop on that obligation; do not
"fix" the statement yourself unless the brief delegates surface authority.

## 5. Working method

- Iterate at the LSP: `lean_goal` / `lean_multi_attempt` /
  `lean_diagnostic_messages` at the stuck position. `lake build` is a
  gate you run when you believe you're done (or to refresh the LSP after
  large edits), never the inner loop. Never `lean_build` (MCP), never
  `lake update`, never a bare unseeded `lake build` in a fresh worktree.
- Files: Read before you write; Edit for changes. `cat >` full-file
  rewrites only for files you created this session. Python heredocs are
  for differential testing, not file surgery.
- Remote search tools are rate-limited: batch queries.
- Landed proofs are capital: thread parameters through existing lemmas,
  don't re-prove them.

## 6. Budget and stop rule (required in full-template mode)

State the size estimate and what to do at the boundary:

- Estimated scope: `<n lemmas / ~lines>`. If mid-task the honest estimate
  of the *remainder* exceeds one agent-session, stop at the current green
  boundary and report — do not start a piece you cannot finish.
- If one lemma resists after `<N>` distinct approaches, record the goal
  state + attempts in the report and move on.
- Never leave a half-proved lemma: revert to the last green state and
  file the attempt (the S4 rule).

## 7. Report format (required in full-template mode)

End with a report the next agent can resume from cold:

- **Done** — declarations landed, with `file:line`.
- **Frozen/untouched** — what you verified you did not change.
- **Defects found** — anything wrong in the given surfaces/programs, with
  evidence (this outranks progress; a found defect is the report's lead).
- **Remaining + next action** — concrete, with the first command to run.
- **Traps** — Lean gotchas hit, in NIGHTLOG-ready form.
- Honesty over completeness: a reverted proof with a repair plan is a
  good outcome; a hidden sorry is the only bad one.
