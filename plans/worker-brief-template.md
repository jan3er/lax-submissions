# Worker brief template

Status: LIVE from 2026-07-30. Instantiate this for every proof-worker
subagent; derived from the July retro (`subagent-retro-2026-07.md`), which
measured what each section pays for. Sections marked (required) were each
missing from some July brief at observable cost. Drop a section only with a
reason; add task specifics freely — this is a floor, not a ceiling.

---

## 1. Identity and goal (required)

One paragraph: wave name, campaign, the exact declarations to produce
(fully qualified), and what "done" means (module builds green, zero sorry,
statements byte-identical to the surface / new satellite file).

## 2. State of the world (required — kills the orientation tax)

The retro measured a median 35% of every worker's messages spent
re-deriving context the supervisor already had. This section is where that
goes instead. Include *inline*, not as pointers:

- Worktree path, package dir, namespace, green commit + job count.
- The load-bearing definitions and lemma statements the task composes
  against, quoted, with `file:line` anchors.
- What is FROZEN (files, surfaces, imports) vs what the worker owns.
- Known traps relevant to this task (whnf blowups, `set` before
  `simp only`, splitter discipline, …) — copy from NIGHTLOG, don't cite it.

For re-spawns/successors: embed the predecessor's final report verbatim,
plus one line: "Trust this report; do not re-verify modules it declares
green."

## 3. File ownership (required for parallel waves)

The July clause set, verbatim-adaptable — zero contamination incidents
once all four lines were present:

- Create and own `<file(s)>` and ONLY them; imports `<frozen list>`.
- You MUST NOT edit any existing file; sibling agents own their leaves;
  the supervisor wires roots.
- Build ONLY your module: `lake build <Module>` from the proofs dir. On a
  lake lock conflict, wait briefly and retry.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Falsification gate (required for authored obligations)

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

## 6. Budget and stop rule (required — kills 3-agent chains)

State the size estimate and what to do at the boundary:

- Estimated scope: `<n lemmas / ~lines>`. If mid-task the honest estimate
  of the *remainder* exceeds one agent-session, stop at the current green
  boundary and report — do not start a piece you cannot finish.
- If one lemma resists after `<N>` distinct approaches, record the goal
  state + attempts in the report and move on.
- Never leave a half-proved lemma: revert to the last green state and
  file the attempt (the S4 rule).

## 7. Report format (required)

End with a report the next agent can resume from cold:

- **Done** — declarations landed, with `file:line`.
- **Frozen/untouched** — what you verified you did not change.
- **Defects found** — anything wrong in the given surfaces/programs, with
  evidence (this outranks progress; a found defect is the report's lead).
- **Remaining + next action** — concrete, with the first command to run.
- **Traps** — Lean gotchas hit, in NIGHTLOG-ready form.
- Honesty over completeness: a reverted proof with a repair plan is a
  good outcome; a hidden sorry is the only bad one.
