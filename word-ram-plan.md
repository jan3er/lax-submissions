# Word-RAM extraction plan

Rev 1, 2026-07-27. Owner: orchestrator session (Fable). Jan is AFK; decisions
below are settled unless marked **JAN-FLAG**. Coding is outsourced to Opus
agents phase by phase; the orchestrator reviews every phase before the next
starts. This document is the contract: agents follow it, deviations need an
orchestrator decision first.

## Goal

Extract the RAM fundamentals out of Lax11 into a new standalone submission
carrying the **archive-canonical word RAM**, with a general-purpose verified
proof pipeline (IMP+ compiler + reasoning kit) that downstream submissions
reuse via a proofs-package require. Then port Lax11's three example results
(connected components, Courcelle–Makowsky–Rotics, vertex cover 2^k) onto the
new architecture.

Architecture after the dust settles:

- `word-ram/` — **new submission** (id allocated by `lax init`; below called
  `Lax13`). Concepts: the word RAM and the timed-computation predicate — pure
  model, zero axioms, all definition-concepts. Proofs package: no proof
  obligations; carries the whole pipeline kit as helpers (the archive ignores
  helpers, downstream imports them via a proofs require — spec-legal,
  "discouraged but allowed" warning is accepted and by design).
- `ram-linear-time/` — **Lax11, rewritten in place** (keeps its id and draft
  slot). Drops the `Ram`/`RamComputes` concepts; the remaining concepts
  (encodings, CC, MSO, CliqueExpr, Courcelle, VertexCover) import `Lax13`.
  Proofs require `Lax13` concepts + `Lax13Proofs`. Whether Courcelle/VC later
  split into their own submissions is **JAN-FLAG: deferred**, out of scope.

## The model (settled)

Cells hold naturals; the semantics is parameterized by a word length `w : ℕ`.
One uniform rule: **every value produced by the machine is reduced mod 2^w,
and every address used to touch memory is reduced mod 2^w** (so memory is the
canonical 2^w-cell store). `read` reduces the input number mod 2^w — the
machine stays total; honesty about oversized inputs lives in statement-side
admissibility, matching the existing design taste.

Instruction set (operands `lit/mem/ind` unchanged, accumulator architecture
unchanged):

- tape/memory: `read a`, `write o`, `load o`, `store a`, `storeInd a`
- arithmetic on the accumulator: `add o` (wraps mod 2^w), `sub o`
  (**truncated**, natural-number monus), `mul o` (wraps), `div o` (floor,
  `x / 0 = 0` as in Lean's `Nat`)
- bitwise on the accumulator: `and o`, `or o`, `xor o` (`Nat.land/lor/xor`),
  `shiftl o` (wraps mod 2^w), `shiftr o`
- control: `jump l`, `jzero l`, `jgtz l`, `halt`

`mod` is omitted (derivable: `a - b * (a / b)` in three instructions, exact
because no intermediate wraps). `not` is omitted (xor with the all-ones word;
a program obtains `2^w − 1` in O(w) once by doubling until wraparound — this
is also how a program can learn `w`, so no "read w" instruction exists).

Why monus and not wraparound subtraction: the accumulator-jump architecture
tests `a > b` by `sub` + `jgtz`, which is exactly why AHU give their integer
RAM signed subtraction; on an unsigned carrier monus is the same
load-bearing choice. Ring subtraction is derivable in O(1) after the O(w)
all-ones prelude, and the monus machine and the wraparound machine simulate
each other with constant overhead, so no statable claim depends on the
choice — the formalization notes of the concept must say all of this.
**JAN-FLAG: monus-vs-wraparound `sub` is my call under autonomy; it is the
one model decision worth a second look.**

Time is the intrinsic step count, one unit per instruction — honest now for
`mul` too, precisely because words are bounded. No space measure (derivable
later as a new definition-concept over `run`; space is automatically ≤ 2^w).
Randomness deliberately absent; note in the formalization notes that a
randomized program is a deterministic one consuming a random word list,
definable downstream over the same machine.

## Statement conventions (settled)

- `ComputesInTime (w : ℕ) (p : Program) (D : Set (List ℕ)) (f) (T)` — `w` is
  an explicit first argument; theorem-concepts quantify it visibly:
  `∃ p, ∀ …, ∀ w, c * (n + 1) ≤ 2 ^ w → ComputesInTime w p …`.
  `∃ p` **before** `∀ w`: one program uniform in the word length, so `w`
  cannot smuggle advice.
- Word-length hypotheses are written as explicit inequalities against `2 ^ w`
  (`c * (x.length + 1) ≤ 2 ^ w`, `numbers < 2 ^ w`), never via logarithms —
  consistent with the repo's no-asymptotics style.
- Admissibility sets `D` carry "all entries fit" conditions where honesty
  requires them.

## The proof pipeline (design intent)

IMP+ stays on **unbounded ℕ semantics**: pipeline users prove functional
correctness and cost on clean natural-number semantics, plus one extra
obligation — a **max-value bound** on every intermediate value of the
program, stated as a function of the input (e.g. `M n = c * (n + 1)`).
The kit's transfer theorem then reads, schematically:

    imp_correct + imp_cost ≤ C + imp_values ≤ M
      → ∀ w, M < 2^w → ComputesInTime w (compile prog) D f (c' * C)

so `w` appears exactly once, at the boundary. The Reasoning layer extends the
existing Hoare-style rules with compositional value-bound tracking (the
examples only use add/sub, so bounds are sums of inputs plus literal
constants; the kit should make the common case one lemma application). New
instructions (mul/div/bitwise/shifts) get IMP+ surface syntax and compile
support, but no example depends on them — smoke tests only.

Kit modules (fundamentals `proofs/`, all helpers, imitating the current ones):
`Machine` (step lemmas), `Imp` (AST + big-step cost semantics), `Bounds`
(value tracking), `Compile`, `Simulation` (compiler correctness under
no-overflow), `Reasoning` (composition rules), `Smoke` (end-to-end sanity
incl. one program exercising mul/shift).

## Phases

Each phase: one Opus agent, briefed with this file + the relevant existing
sources; orchestrator reviews (concepts: every line — they are the
endorsement surface; proofs: interfaces, axiom hygiene via `lean_verify`,
build green) and commits before the next phase starts.

1. **Scaffold + concepts.** `lax init word-ram` (id from archive), write
   `Lax13/Ram.lean` and `Lax13/RamComputes.lean` per the spec above, imitating
   the current Lax11 concept prose; manifest (authors: Jan Dreier; bib: AHU,
   Cook–Reckhow, Hagerup "Sorting and searching on the word RAM",
   Fredman–Willard), abstract.md. Build green. Gate: orchestrator full read.
2. **Pipeline kit.** Port + extend the kit into `Lax13Proofs` per the design
   intent, on the new word semantics. Gate: transfer theorem exists with the
   schematic shape above; smoke programs (echo, sum, one mul/shift program)
   verified end to end; `lean_verify` shows background-only axioms.
3. **CC port** (smallest example, validates the pipeline): rewrite Lax11
   concepts to import `Lax13`, port the CC proof stack. During development the
   requires may use local `path` for iteration speed; phase 6 flips them.
4. **VC port** (VCSpec/VCScan/VCLoop/VCMain stack).
5. **Courcelle port** (MSO stack + TreeFold + drivers — the big one; may be
   split across two agent runs at the orchestrator's discretion).
6. **Plumbing + submit.** Flip requires to git pins, `lax build` both
   submissions, commit, push, `lax submit word-ram` (draft), repin Lax11 to
   the pushed commit, `lax build`, `lax submit ram-linear-time` (draft).
   Registration stays with Jan.

## Repo hygiene (parallel sparsity session)

- Touch only: `word-ram/`, `ram-linear-time/`, `word-ram-plan.md`, memory.
- Never touch: `NIGHTLOG.md`, `sparsity-lectures-plan.md`,
  `monadic-dependence-neighborhood-complexity/`, `twin-width-*`, `todo.md`,
  the stale `*-night-brief.md` / `vc-contracts/` leftovers.
- Stage by explicit path only; never `git add -A`. Commit at phase ends.

## Progress log

- [x] Plan written (rev 1).
- [x] Phase 1 scaffold + concepts — id **Lax13** allocated; concepts, manifest,
  abstract written and reviewed line-by-line (one notes fix: literal
  non-reduction also differs for `sub`, not only div/shifts); `lake build`
  and `lax build` green.
- [x] Phase 2a pipeline semantic core — Machine/Imp/Bounds/Compile/Simulation
  in Lax13Proofs (1932 lines); `BigStepB` threads cost + value bound through
  one derivation; `compileProgram_runsTo` proved, constant `3*idxLen + 13`,
  additive 0; build + lean_verify clean. Expr collapsed to one `bin` node
  (old names live as simp-abbrevs); Labels.lean correctly left to the CC
  example. Word-length hypothesis bundled as `Layout.FitsWords B w`
  (span covers `temps + |scalars| + |arrays| * B`).
- [x] Phase 2b reasoning layer + transfer + smoke — `Run` over `BigStepB`
  (drop-in port of the Lax11 rules), six `evalB` iff-simp lemmas make bound
  side conditions `simp; omega`-dischargeable; `Solves` bundle +
  `computesInTime_of_solves` conclude concept-level `ComputesInTime`
  (`B` is a function of the input; time separated by `L.const * K ≤ T`);
  three smoke programs green incl. mul/shiftl. Note for downstream: word
  hypothesis goes against `max B (L.span B)` (`fitsWords_of_max_le`).
- [x] Phase 3 CC vertical slice — Lax11 Ram/RamComputes deleted; GraphEncoding
  + ConnectedComponents rewritten over Lax13 (statement: fitting condition is
  a conjunct in `D`, since a fixed graph has encodings of every length and an
  arrow form would be vacuous — accepted deviation; one constant 2604 serves
  time and word bound; `B x = x.length` via new `mem_lt_length`); CC proof
  stack ported (8 modules), roots trimmed, dev path-requires wired. Orchestrator
  fixed ≤-vs-word prose imprecision in three spots. Both builds green,
  lean_verify background-only.
- [x] Phase 4 VC vertical slice + kit polish — evalB intro/`hdef` lemma
  family + nine size simp lemmas added to Reasoning (all eight repo loop
  `hdef`s now one-liners); VertexCover rewritten over Lax13 with honest
  fitting conjunct `c * (|x| + k + 1) ≤ 2 ^ w` (k linear because the
  parameter is an input entry and stack extent is k; deliberately NOT
  2^k-coupled — notes argue it), constant 33300 unchanged, defeq-checked;
  VC proof stack ported; InstanceEncoding correctly deferred to Phase 5
  (it imports CliqueExpr). Orchestrator tightened two axiom-docstring
  imprecisions. All three packages green.
- [ ] Phase 5 Courcelle vertical slice
- [ ] Phase 3 CC port
- [ ] Phase 4 VC port
- [ ] Phase 5 Courcelle port
- [ ] Phase 6 plumbing + drafts submitted
