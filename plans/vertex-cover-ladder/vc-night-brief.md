# Relay brief: Lax11 vertex cover, the 2^k discharge

You are one session in a relay of fresh Opus sessions. Jan is away; an
orchestrator relaunches sessions and reads only `NIGHTLOG.md` and
`git log`. Your job: execute the **next incomplete milestone**, commit
only green work, log, and exit.

Context to read first (in this order, skim don't study):
1. `NIGHTLOG.md` — tail only: what previous VC sessions did.
2. `vc-ladder-plan.md` — **the plan. The algorithm, the invariant `J`,
   the potential `P`/`f`, and the decision record VC1–VC6 are fixed
   there; implement them, do not redesign them.** The potential and
   invariant were stress-tested on paper; if a proof obligation seems
   to fail, suspect your formalization first, and if the arithmetic
   itself is genuinely wrong, write a precise counterexample to the
   log and stop — that is signal, not failure.
3. `ram-linear-time/concepts/Lax11/VertexCover.lean` — the statement
   to discharge (frozen).
4. `ram-linear-time/proofs/Lax11Proofs/CCPhases.lean` and
   `CCMain.lean` — the house pattern: invariant as a def over a pure
   state, `Run.while_pot`, `arrOf`, frame conditions, `.mono` slack,
   `computesInTime_of_run`, conclusion frontmatter.
5. `ram-linear-time/proofs/Lax11Proofs/Reasoning.lean` — the kit.

## Endgame

A proof-package theorem, statement verbatim from the concept, with

```
/--
---
conclusion: Lax11.VertexCover.exists_fptTime_program_vertexCover
---
... prose + # Proof strategy + # Attribution ...
-/
```

Witness: the compiled `vcCom` with an explicit numeral constant.

## Milestones (one per session; V1 and V4 may split — say so in the log)

- **V0 (every session, first).** Dirty tree: assess, keep only
  near-green WIP, otherwise stash and log. Never build on WIP you
  don't understand.
- **V1a — `VCSpec.lean`, graph side.** `Ok`, the ℕ∞ bridge (one
  lemma, quarantined), the branch lemma, `¬ Ok M 0` under an
  uncovered edge, cover-on-exhaustion through
  `EncodesGraph.adj_iff`.
- **V1b — `VCSpec.lean`, config side.** Pure config, marking,
  frame-health, `J`, the four preservation lemmas (push, flip, pop,
  exits), `f`/`P` and the drop lemmas of plan §VC4.
- **V2 — `vcCom` + smoke.** The program (plan §algorithm), `vcCom_ok`,
  `#eval` the compiled machine program on the plan's test graphs
  *before any Run proofs*. Log the step counts.
- **V3 — the scan lemma** (plan §V3: `while_pot`, potential
  `a·(2m−j) + b·(n−u)`).
- **V4 — the outer loop.** Body transition lemma (case split on
  mode/found/bud), then `Run.while_pot` with
  `Φ = U·(x.length+1)·P ∘ decode`. The hard milestone; two sessions
  before escalating, and split body-lemma / assembly if needed.
- **V5 — assembly and audit.** Reads (+ one `read` for `k`),
  `write ans`, `computesInTime_of_run`, the endgame theorem,
  `lake build` green in `proofs/`, `lean_verify`: only `propext`,
  `Classical.choice`, `Quot.sound`. Commit.
- **V6 — wrap-up (Jan-visible; log prominently).** `abstract.md`
  final paragraph (statement no longer open), `notes.md`, achieved
  constant in the log. **No concept edits.**

## Guardrails

- **Never edit `concepts/`**, `vc-ladder-plan.md`, or the machine
  model. Plan decision VC5: no multiplication, no word RAM — do not
  "improve" the substrate.
- Only `Lax11Proofs`-prefixed declarations. Never `simp` with
  pattern-matching concept definitions (splitter leakage); use the
  `rfl` lemmas in `Machine.lean`.
- Loose constants everywhere; `.mono` early; never fight for tight
  bounds. Exception: the `−3` in `f` (plan §VC4) is load-bearing.
- Commit only green work (builds clean, zero `sorry`); stage only
  your files (never `NIGHTLOG.md`, `asdf`, unrelated WIP). Commit
  style: `Lax11 vc: ...`.
- Mathlib-style names; docstrings in the voice of the existing files.
- No `lake update`. Prefer `lean-lsp` tools; batch remote searches.
  Watch item: stale LSP diagnostics after an external `lake build` —
  rebuild via `lean_build` or trust `lake build`.
- Three failures on one approach → different decomposition; genuinely
  stuck → precise stuck-report to the log and exit. Do not thrash.

## Log protocol

Append (never rewrite) to `NIGHTLOG.md` before exiting:

```
## VC session <k> — <UTC time>
Milestone: V<i> — done | partial | stuck
Commits: <hashes + one-liners, or "none">
State: <2–5 lines>
Next: <the single next action>
Decisions: <anything Jan should review, or "none">
```

Keep your final printed message under 10 lines — only the orchestrator
reads it.
