# IMP+ toolkit plan

Rev 1, 2026-07-28. **Status: OPEN, phase 1 not started.** Owner: unassigned;
Jan to allocate. Decisions below are settled unless marked **JAN-FLAG**.
This document is the contract: implementing sessions follow it, deviations
need an owner decision first.

Scope is **proofs-only**. No concept surface anywhere in the repo changes,
no `lean-toolchain` or mathlib pin moves, and the machine model
(`Lax13/Ram.lean`, `Lax13/RamComputes.lean`) is not touched. A phase that
finds itself wanting to edit a concept has misread the plan.

## Goal

Lower the marginal cost of the *next* algorithmic result. Today an
algorithm submission pays for the machine level from primitives; the kit in
`word-ram/proofs/Lax13Proofs/` stops at `Run` and hands the user a
judgment, not a toolbox. Make the machine level a library — proved once in
Lax13Proofs, composed downstream — so that a new algorithm costs its
mathematics plus a program, and not much else.

## The evidence

Lax15 (`vertex-cover-ladder`) is 10,940 proof lines. They divide:

| | lines | share |
|---|---|---|
| pure mathematics (`Config`, `Config3`, `Residual`, `Solver`, `Repeats`, `MainFpt`) | 2,755 | 25% |
| program text, no proofs (`Program`, `Program3`) | 1,028 | 10% |
| **machine glue** (`Phases`, `Phases3`, `Loop`, `Loop3`, `Sweep3`, `Main`, `Main3`) | **7,142** | **65%** |

Two thirds of the campaign was machine glue, and almost none of it came
from Lax11 despite Lax11 having built the same kinds of object. The whole
cross-package proof reuse is `readLoop_run` plus four `List` lemmas.
Session 6 of the VCF relay recorded the failure in its own words: "Lax11's
lemmas re-proved here since `VCLoop` is not imported."

The counter-example is the same lemma. `readLoop_run`
(`ram-linear-time/proofs/Lax11Proofs/CCPhases.lean:47`) is parameterized in
the array and limit names, and it is used **eight times** across `CCSweep`,
`CourcelleMain`, `TreeFoldMain` and Lax15's `Main`. Packaging a machine-level
operation as a parameterized run lemma is *already known to work here*. The
plan is to do it nine more times, and to automate what surrounds it.

### Where the glue goes

Four mechanical categories. `countBlock_run`
(`vertex-cover-ladder/proofs/Lax15Proofs/Phases.lean:823`) exhibits all four
in 30 lines of proof for a five-line block with two nested `ite`s;
`seenBlock_run` immediately below it takes 70.

1. **Symbolic execution by hand.** `Run.seq` / `Run.assign` / `.mono`
   chained manually, `evalB` side conditions discharged one expression at a
   time.
2. **Frame conditions by hand.** `(∀ y, y ≠ "ro" → y ≠ "cnted" → …)` in
   roughly ninety statements, destructured again at every call site.
   `Scanned` / `not_scanned_ne` (`Phases.lean:947`) is a hand-rolled
   instance of a rule that is syntactic.
3. **The value bound threaded through every signature.** `2 < B`,
   `n + 1 < B`, `2m < B`, `k + 1 < B`. VCF session 6 records the bound
   *moving* — `n < B` to `n + 1 < B`, because the push writes `top + 1` —
   and propagating through every lemma below it.
4. **Ad-hoc statement shapes.** Every phase lemma is a bespoke
   `∃ ρ' K, Run … ∧ K ≤ … ∧ frames ∧ (case ∨ case ∨ case)`, so composition
   is `obtain` plus manual reassembly rather than a term.

Session 6 also hit nested `Run.seq`/`Run.ite` terms blowing the whnf
heartbeat limit, and `(B := B)` needing to be passed explicitly because `B`
appears in no hypothesis that determines it. Both are symptoms of there
being no interface.

## What is kept (settled, not up for redesign)

- **The deep embedding of `Com`.** The compiler needs a syntactic object.
  A shallow monadic front end is out of scope; see "Not in scope".
- **Unbounded IMP+ with the value bound at the boundary.** `Imp.lean`'s
  argument stands: functional correctness on clean `ℕ` arithmetic, the word
  length entering once. The `B` obligation is intrinsic — `x + y` can leave
  the words even when `x` and `y` do not — so it is to be *automated*, not
  removed.
- **The aliasing-free environment** (`Imp.lean:24-31`): names denote
  disjoint objects. This is a better fit for the domain than separation
  logic and is exactly what lets the frame rule of phase 1 be syntactic.
  It is not to be given up.
- **`Run` with cost as an upper bound** (`Reasoning.lean:292`) and
  **`Run.while_potential`** (`Reasoning.lean:378`). The potential form is time
  credits in first-order clothing; it is the hard part and it is right.
- **`Transfer.Solves` as the single boundary predicate.** Unchanged.

## Prior art, and what is taken from it

**Lammich's Isabelle stack.** The Isabelle Refinement Framework's `nres`
monad, its cost-carrying successor `NREST` (Haslbeck–Lammich, *Refinement
with Time*; *For a Few Dollars More*), `Sepref`, and Isabelle-LLVM.

- *Taken:* the NREST **shape**. This repo is already 80% of the way there
  without having named it — `Solver.lean` is the abstract algorithm, `Rep`
  is the data refinement, `Run` is the concrete layer. The two things NREST
  has that we lack are that the refinement relation is **composed from
  per-component relations** (so a phase touching only the marks does not
  re-establish all eleven conjuncts of `Rep`), and that correctness and
  cost **ride one ordering** instead of being separate conjuncts of every
  lemma. Phases 2 and 4 import those two properties without importing the
  monad.
- *Taken:* the currency/amortization idea, already present as `while_potential`.
- *Not taken:* `Sepref`. Its synthesis is thousands of lines of Isabelle/ML
  resting on Isabelle's transfer and parametricity infrastructure. The Lean
  analogue is a spec-lemma set plus a VCG, which is phases 2–4 arrived at
  honestly and at a tenth the cost.
- *Not taken:* Imperative/HOL's heap monad and separation logic. We do not
  need them; see "What is kept".

**`Std.Do`** (Lean 4.30, our pinned toolchain: `Std/Do/{Triple,WP,PredTrans,
SPred}.lean`, with `mvcgen` / `mspec` and `forIn` invariants). It models
shallow monadic Lean programs and has no cost dimension, so it is not a
drop-in for a deep embedding with a step count. Its *design* — Hoare
triples plus a VCG driven by an attribute-registered spec set — is the
model phases 2 and 3 copy. This matters: the tactic we write is a
known-good shape rather than an experiment.

## Phases

Each phase lands green with zero `sorry`, is committed on its own, and is
reviewed before the next starts. Every phase that adds a match-defined
function to the kit **materializes its equation lemmas upstream** — the
standing kit rule discovered in word-ram phase 6, without which a
downstream `simp [f]` leaks `Lax13Proofs`-named splitters into a consumer
package and the archive's namespace check rejects it.

### P1 — The frame rule · `Lax13Proofs/Frame.lean`

The same induction that already proves `Run.out_eq` for `Com.NoWrite`
(`Reasoning.lean:443-484`), three more times, driven by syntax instead of
by a hand-written predicate per lemma.

```lean
def Com.wvars : Com → List String   -- scalars possibly assigned
def Com.warrs : Com → List String   -- arrays possibly stored into
def Com.reads : Com → Prop          -- contains a `read`

theorem Run.frame_var (h : Run B c σ σ' K) (hy : y ∉ c.wvars) : σ'.vars y = σ.vars y
theorem Run.frame_arr (h : Run B c σ σ' K) (ha : a ∉ c.warrs) : σ'.arrs a = σ.arrs a
theorem Run.frame_inp (h : Run B c σ σ' K) (hr : ¬ c.reads)   : σ'.inp  = σ.inp
```

Membership is decided by `decide` on concrete syntax, so a call site pays
one `by decide` where it now carries a universally quantified conjunct.

**Acceptance.** `Scanned` and `not_scanned_ne` (`Phases.lean:947-958`)
deleted and their uses rewritten through `Run.frame_var`; the frame
conjuncts of `readLoop_run` (`CCPhases.lean:47`) dropped from its statement
with all eight call sites still green.

### P2 — Spec triples · `Lax13Proofs/Spec.lean`

An interface phase lemmas are *stated in* and compose *as terms*. Rev-1
proposal — the implementing session may adjust the exact shape, but the
obligations are fixed:

```lean
def Spec (B : ℕ) (P : Env → Prop) (c : Com) (Q : Env → Env → Prop) (K : ℕ) : Prop :=
  ∀ σ, P σ → ∃ σ', Run B c σ σ' K ∧ Q σ σ'
```

with `Spec.seq`, `Spec.ite`, `Spec.conseq`, `Spec.frame`, `Spec.mono`,
`Spec.while_potential` (re-cut from `Run.while_potential`) and **`Spec.forRange`** — a
counter-from-`a`-to-`b` combinator, since every scan in the repo is
currently a hand-built `while` plus invariant plus potential.

`Q` is relational (initial *and* final environment) because phase lemmas
say things like `ρ'.vars "ro" = ρ.vars "ro" + 1`. `B` becomes a section
variable carried by the structure, which closes the `(B := B)`
metavariable trap of VCF session 6.

**Acceptance.** Two consecutive phase lemmas of `Phases.lean` restated as
`Spec`s and composed with `Spec.seq` and `Spec.frame` alone — no `obtain`,
no manual reassembly.

### P3 — The `run_step` tactic · `Lax13Proofs/Tactic.lean`

The single largest lever. Walk the `Com`, apply the matching `Run`/`Spec`
rule, normalize the environment chain with the existing simp set
(`Reasoning.lean:60-90`), accumulate the cost as a numeral, and **collect
every `< B` obligation into one deferred goal** discharged at the end by
`omega` against the invariant. Split on `ite` conditions; leave the
functional content as the only goal a human sees.

Two hard requirements, both from VCF session 6:

- The term is built **incrementally as a `have` chain**, never as one
  nested application. Deeply nested `Run.seq`/`Run.ite` over `set`-bound
  environments blows the whnf heartbeat limit.
- No `if_neg (by decide)` / `if_pos rfl` inside `simp only` or `rw` lists —
  they leave a metavariable or silently fail to fire. Named hypotheses or
  plain `simp`.

**Acceptance.** `countBlock_run` (`Phases.lean:823`) proved in ≤ 5 lines
and `seenBlock_run` in ≤ 12, both with unchanged statements, and the file's
elaboration time no worse than today's. If the tactic is slower than the
hand proofs, it has failed and the phase is not done.

### P4 — The data-structure library · `Lax13Proofs/Lib/`

The heavy lifting, done once. Each structure: an abstraction relation, and
its operations exported as `Spec`s with cost.

| module | abstraction | operations | consumers today |
|---|---|---|---|
| `Lib/Ind.lean` | `Finset (Fin n)` as a 0/1 array | test, mark, unmark | Lax11 VC, Lax11 CC, Lax15 rungs B and C |
| `Lib/Stack.lean` | `List α` as array + count | push, pop, peek | Lax11 VC frames, Lax15 rung B frames |
| `Lib/Trail.lean` | undo log with truncate-to-height | record, unwind | Lax15 rungs B and C |
| `Lib/Queue.lean` | FIFO as array + head/tail | push, advance, drain | Lax11 CC, Lax15 rung C |
| `Lib/Csr.lean` | offsets + targets block structure | **row scan, full owner-advancing scan** | six sites, below |

`Lib/Csr.lean` is the one that pays for the phase on its own. The
owner-advancing scan with its amortized potential is written from scratch
at `Phases.lean:462` (`rowLoop_run`), `Phases.lean:1004`
(`descendScan_run`), `Phases3.lean:1320` (`rowScan3_run`),
`Sweep3.lean:231` (`drain3_run`), `Sweep3.lean:506` (`rootSweep_run`), and
again in Lax11's `VCScan`. Six times.

**Placement decision (settled).** `Lib/Csr.lean` is stated purely over "an
offsets array and a targets array" — no `SimpleGraph`, no `Fin n`. The
bridge to `Lax11.GraphEncoding` stays in Lax11. The kit must not acquire a
graph dependency.

**Acceptance.** Each module ships with a `#guard`-checked worked example in
the kit, and `Lib/Csr`'s scan combinator instantiates to `rowLoop_run`'s
statement.

### P5 — Pilot retrofit: the Lax11 CC driver

`CC`, `CCPhases`, `CCGraph`, `CCSearch`, `CCSweep`, `CCMain` — 1,655 lines,
the smallest driver with both a queue and a mark array. Port onto the kit.
Statements of the exported theorems (`CCMain`'s endgame in particular) do
not change; only the proofs do.

**Gate.** If the six files do not come out at **≤ 40% of 1,655 lines**, stop
and bring the design back to Jan rather than proceeding to P6. The point of
the pilot is to find that out for 1,655 lines instead of for 20,000.

### P6 — The rest of the retrofit

In order, each behind the same 40% gate and each committed separately:
Lax11 VC (`VC*`, ~1,900 lines), Lax11 Courcelle / TreeFold (~2,900), Lax15
rung B glue (`Phases`, `Loop`, `Main`, 2,919), Lax15 rung C glue
(`Phases3`, `Sweep3`, `Loop3`, `Main3`, 4,223). Any one of these may be
declared out of scope by the owner without invalidating the others — the
kit is useful with no retrofits at all, and the retrofits are for the
*next* campaign's benefit, not this one's.

### P7 — Pins and drafts

Lax13 gains files in its proofs package; Lax11 and Lax15 re-pin to the new
rev. No concept surface moves, so no statement changes and no abstract
rewrite. Drafts re-submitted.

**JAN-FLAG.** `lax submit --register` is not to be run by any session in
this campaign. Registration needs fresh explicit confirmation from Jan, and
the server state recorded in the registration memo (Lax14/Lax12/Lax5 still
registered, `pull-db` broken) is unresolved and untouched by this work.

## Not in scope

- **The NREST port.** The abstract side (2,755 lines in Lax15) is already
  clean and paper-shaped; automating the 7,142 lines of glue pays more,
  sooner, and any NREST layer would want phases 1–4 underneath it anyway.
  Revisit only after P5's gate is passed and the numbers are in.
- **`Sepref`-style synthesis**, separation logic, a heap monad.
- **A shallow monadic front end** for IMP+ (interpreting `Com` into a state
  monad to reach `Std.Do`'s `mvcgen`). It adds a third semantics to keep in
  sync. Reconsider only if P3's tactic proves inadequate, and then as its
  own plan.
- **Concrete syntax for `Com`** (a `do`-like macro over
  `.seq (.seq (.seq …))`). Genuinely wanted — `Program.lean` is 300 lines of
  nested constructors — but it buys review confidence, not proof lines, so
  it is deferred behind P1–P4 and is a good standalone task for a short
  session.
- **The machine model, every concept surface, `lake update`.**

## Watch items

- **Elaboration time is a first-class acceptance criterion.** A kit that
  makes proofs shorter and builds slower is a regression. Record wall-clock
  `lake build` per phase in the progress log.
- **Equation-lemma materialization** for every new match-defined kit
  function, per the word-ram phase-6 standing rule. A downstream
  `simp [f]`/`split` on an unrealized upstream match leaks foreign names.
- **`Rep` is a nested conjunction** and its projections are written
  `h.2.2.2.2.2.2.2.2.2.2` (`Phases.lean:200-231`). Any retrofit phase that
  touches a `Rep` makes it a `structure` first; `Rep.of_vars_eq`
  (`Phases.lean:233`) should then fall out of P1 rather than be
  hand-written.
- **Abstraction relations must stay cheap.** Resist stating `Lib` relations
  over `Multiset`/`Finset` machinery whose `decide`/`simp` cost dominates.
  `arrOf` + a pointwise function is the shape that has worked.
- **The kit is helper-only.** The archive ignores helpers and downstream
  imports them through a proofs require; the "discouraged but allowed"
  warning is accepted and by design. Nothing in this campaign changes that.

## Progress log

- [ ] P1 frame rule
- [ ] P2 spec triples
- [ ] P3 `run_step` tactic
- [ ] P4 data-structure library
- [ ] P5 pilot retrofit (Lax11 CC) — **gate: ≤ 40% of 1,655 lines**
- [ ] P6 remaining retrofits
- [ ] P7 pins and drafts (registration excluded, JAN-FLAG)
