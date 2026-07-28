# Overnight brief: Lax11 driver, step 6 (the search proof)

You are one session in an overnight relay of fresh Opus sessions. Jan
is away; a cheap orchestrator relaunches sessions and reads only
`NIGHTLOG.md` and `git log`. Your job: execute the **next incomplete
milestone** below, commit only green work, log, and exit.

Context to read first (in this order, skim don't study):
1. `NIGHTLOG.md` — what previous sessions did; which milestone is next.
2. `ram-stack-plan.md` — the plan; steps 1–5 are done, this is step 6.
3. `ram-linear-time/proofs/Lax11Proofs/CC.lean` — the program and the
   cost-potential argument (docstring).
4. `ram-linear-time/proofs/Lax11Proofs/CCPhases.lean` — the proved
   phase lemmas; **this file fixes the house pattern** (invariant as a
   def, `Run.while_count`/`Run.while_pot`, `arrOf`, frame conditions,
   `.mono` slack).
5. `ram-linear-time/proofs/Lax11Proofs/Reasoning.lean` — the kit.

## Endgame

Prove, in `Lax11Proofs`, the exact statement of the concept axiom, with
witness `ccProgram` (`concepts/Lax11/ConnectedComponents.lean:64`):

```lean
∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  ComputesInTime p {x | EncodesGraph x n G} (fun _ => ccLabels G)
    (fun x => c * (x.length + 1))
```

marked with the house conclusion frontmatter (see
`monadic-dependence-neighborhood-complexity/proofs/Lax5Proofs/Theorem2.lean`
for the format):

```
/--
---
conclusion: Lax11.ConnectedComponents.exists_linearTime_program_ccLabels
---
... prose + proof strategy ...
-/
```

## Strategic instruction (from the step-6 review — follow it)

**Do not state the graph theory on `Env`.** Define a pure model of the
search state and prove the BFS mathematics against it with no
environment in sight; the `Env`-level lemmas only say "the arrays
represent this pure state" and chain `Run` steps. This keeps mathlib
reachability reasoning out of the `simp [Env.setVar]` mire and is the
reusable pattern Courcelle will want.

## Milestones

**M0 (every session, first).** If the working tree is dirty: assess the
leftover WIP. Keep it if it is close to green, otherwise `git stash`
and note that in the log. Never build on WIP you don't understand.

**M1 — `CCSpec.lean`: the pure search state and the graph lemmas.**
A structure for the search state (labelling `ℕ → ℕ` with marker `n`,
queue contents, `head`/`tail`/`u`/`sc` as naturals), the BFS invariant
as a pure predicate, and its preservation lemmas: one scan step, one
expand step, one new-root step, plus the termination facts (`tail ≤ n`,
each vertex enqueued at most once). Graph side, against
`SimpleGraph (Fin n)` directly:
- adjacency transport through the encoding via `EncodesGraph.adj_iff`
  (state it once for the off/tgt lists the program reads in);
- an adjacency-closed set containing `u` contains `u`'s component
  (induction on `Reachable`/`Walk`);
- the least-vertex characterization: `Labels.label_eq` in
  `proofs/Lax11Proofs/Labels.lean` already exists — use it;
- the final-state lemma: when the sweep finishes, the pure labelling
  equals `fun v => label G v` on `[0, n)`.
Acceptance: file green, no `sorry`, committed.

**M2 — the scan loop.** A `Run` lemma for
`.while (.lt (.var "j") (.var "jend")) scanBody` in the CCPhases style:
hypothesis "arrays/scalars represent pure state `s` + pure invariant",
conclusion "represent `s'` + invariant + what the scan did + cost".
Cost by `Run.while_pot` — the enqueue branch costs more than the skip
branch, paid from the `c₀·(n − tail)` term; the scan itself from
`c₁·(2m − sc)`. The potential is the one in `CC.lean`'s docstring; it
must be a function of the scalars (that is what `sc` is for). Mind
`hdef`: the invariant must carry the in-bounds facts for every array
read (`tgt`, `lab`, `q`, `off` lengths), since out-of-bounds is stuck.

**M3 — `expandBody` and `drain`.** Same shape, one level up; `drain`
is `while_pot` with the global potential. Remember `head` moves *after*
the scan (the program was shaped for exactly this invariant).

**M4 — the outer sweep and `ccCom` end to end.** Compose: reads
(`readLoop_run`, committed), `initLab_run`, the sweep, `writeLoop_run`.
Choose the initial extents for `initEnv`: `off ↦ n+1`, `tgt ↦ 2m`,
`lab ↦ n`, `q ↦ n`. Conclusion: for every `x` with `EncodesGraph x n G`,
`Run ccCom (initEnv ext x) σ' K` with `σ'.out = ccLabels G` and
`K ≤ a·n + b·m + d` for explicit numerals.

**M5 — assembly and audit.** `computesInTime_of_run` + `ccCom_ok`
discharge to the machine; convert the bound using `n ≤ x.length` and
`2m ≤ x.length` (should follow from `EncodesGraph.length_eq` — if it
doesn't, derive what does and adjust the constant). State the endgame
theorem with the conclusion frontmatter. Then: `lake build` clean in
`proofs/`, axiom audit (`lean_verify` or `#print axioms`) shows only
`propext`, `Classical.choice`, `Quot.sound`. Commit.

**M6 (only if the night allows) — wrap-up.** Plan step 7:
formalization notes / honesty ledger (D2, D4, D5, D7, D16; and move the
"global queue + `sc` counter, both free" argument from `CC.lean`'s
docstring into the notes), abstract, build-output.

One milestone per session, then exit — even if you feel fast. M1 and
M2 may be split across two sessions each if needed; say so in the log.

## Guardrails

- **Never edit `concepts/`** — the surface is frozen. Don't edit
  `ram-stack-plan.md` either; log instead, Jan revises the plan.
- Only `Lax11Proofs`-prefixed declarations in the proof package. Never
  `simp` with a concept definition that was written by pattern matching
  (splitter leakage — see the plan's watch item); use the `rfl` lemmas
  in `Machine.lean`.
- `Reasoning.lean` may gain *generic* lemmas (arrOf helpers, kit
  rules); driver-specific material goes in `CCSpec`/`CCPhases`/new
  files, imported from `Lax11Proofs.lean`.
- Commit only green work: builds clean, zero `sorry`. Stage only your
  files (never `NIGHTLOG.md`, `asdf`, or unrelated WIP). Commit message
  in the style of `git log` (`Lax11 driver: ...`).
- Loose constants everywhere; never fight for a tight bound — take
  slack with `.mono` early.
- Mathlib-style names (`concl_of_hyps`); docstrings in the voice of the
  existing files.
- No `lake update`. Prefer the `lean-lsp` MCP tools over rebuild loops;
  batch remote searches (rate-limited). If MCP is unavailable, fall
  back to `lake build` in `ram-linear-time/proofs/`.
- If an approach fails three times, log what and why, try a different
  decomposition. If the milestone is genuinely stuck, write a precise
  stuck-report to the log and exit — do not thrash.

## Log protocol

Append (never rewrite) to `NIGHTLOG.md` before exiting:

```
## Session <k> — <UTC time>
Milestone: M<i> — done | partial | stuck
Commits: <hashes + one-liners, or "none">
State: <2–5 lines: what exists now, what's proved, what's left>
Next: <the single next action for the following session>
Decisions: <anything Jan should review in the morning, or "none">
```

Keep your final printed message under 10 lines — only the orchestrator
reads it.
