# Relay brief: the Fibonacci vertex cover submission

You are one session in a relay of fresh Opus sessions. Jan is away for
the night; the orchestrator (a Fable session) launches you with a
milestone assignment, reads only your final message, `NIGHTLOG.md`,
and `git log`, and decides what the next session does. Your job:
execute **your assigned milestone only**, commit only green work, log,
and exit.

Context to read first (in this order; skim, don't study):

1. Your assignment prompt (the milestone and any session-specific
   notes from the orchestrator — they override this file).
2. `NIGHTLOG.md` — tail only: what previous VCF sessions did.
3. `vc-fib-plan.md` — **the plan. The statement, decision record
   VF1–VF8, the algorithm, the invariant `J`, the potential `P`/`f`,
   and the transition table T1–T8 are fixed there; implement them, do
   not redesign them.** If an obligation seems to fail, suspect your
   formalization first; a genuine arithmetic counterexample goes to
   the log, precisely, and you stop — that is signal, not failure.
4. The house pattern, in the existing 2^k campaign:
   `ram-linear-time/proofs/Lax11Proofs/VCSpec.lean` (pure model),
   `VC.lean` (program + smoke), `VCScan.lean` (scan lemma),
   `VCLoop.lean` (outer `while_pot`), `VCMain.lean` (assembly,
   conclusion frontmatter). Imitate these files; they are the
   previous rung of the same ladder.
5. The kit: `word-ram/proofs/Lax13Proofs/Reasoning.lean` (Run rules,
   `while_pot`), `Machine.lean`, `Compile.lean`; concepts
   `word-ram/concepts/Lax13/RamComputes.lean`,
   `ram-linear-time/concepts/Lax11/GraphEncoding.lean`,
   `ram-linear-time/concepts/Lax11/VertexCover.lean`.

## Where the work lives

The new submission directory is `vertex-cover-fibonacci/` (id
allocated by `lax init`; adjust `LaxN` names to the actual id — the
orchestrator's prompt or the scaffold commit fixes it). Its `proofs/`
package imports the pinned Lax11Proofs/Lax13Proofs — the working-tree
copies of those files are identical to the pins (HEAD = 0bbcfec), so
read them locally but **never edit anything outside
`vertex-cover-fibonacci/`**.

## Guardrails

- **Never edit**: other submissions, `vc-fib-plan.md`, the machine
  model, lakefile pins after S0. No `lake update`, ever.
- Concept surface: fixed after S0 (statement verbatim from the plan).
  If your milestone is proof-side and the concept seems wrong, log it
  and stop; do not edit concepts.
- Only `LaxNProofs`-prefixed declarations in proofs. Never `simp`
  with pattern-matching concept definitions (splitter leakage); use
  the `rfl`-lemma idiom.
- Loose constants everywhere; `.mono` early; never fight for tight
  bounds. Exceptions (load-bearing, from the plan): the `−3` in `f`,
  the `+2` on stored phase-0 frames.
- No multiplication in the program; `fib` is never computed at run
  time (VF5).
- Commit only green work (`lake build` clean in the package you
  touched, zero `sorry`); stage only your task's files — never
  `NIGHTLOG.md`, never other submissions, never generated files
  (`build-output.json`, `lake-manifest.json` stay untracked). Commit
  style: `LaxN vcfib: <what>` (actual id).
- Mathlib-style names (`concl_of_hyps`); docstrings in the voice of
  the existing files.
- Prefer `lean-lsp` MCP tools over rebuilding; batch remote searches.
  After an external `lake build`, LSP diagnostics can be stale —
  `lean_build` or trust the command line.
- Three failures on one approach → try a different decomposition;
  genuinely stuck → precise stuck-report to the log and exit. Do not
  thrash. Never leave the tree dirty with WIP you don't understand —
  stash and log.

## Log protocol

Append (never rewrite, never stage) to `NIGHTLOG.md` before exiting:

    ## VCF session <j> — <UTC time>
    Milestone: S<i> — done | partial | stuck
    Commits: <hashes + one-liners, or "none">
    State: <2–5 lines>
    Next: <the single next action>
    Decisions: <anything the orchestrator or Jan should review, or "none">

Your final printed message: under 12 lines, milestone status first —
only the orchestrator reads it. Include anything the *next* session
must know that is too small for the log.
