# IMP+ toolkit plan

Rev 1, 2026-07-28. **Status: OPEN, P1 built and half accepted.** Decisions
below are settled unless marked **JAN-FLAG**. This document is the
contract: implementing sessions follow it, deviations need an owner
decision first.

**Working model (Jan, 2026-07-28).** Fable supervises — plan, sequencing,
review, acceptance calls, commits — and **Opus subagents write the
proofs**. A supervising session spawns an Opus agent per proof-shaped
unit of work rather than editing Lean itself, so the supervisor keeps
context for the whole campaign instead of burning it on one file. See
"Handoff notes" at the end.

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

**Gate re-cut (owner decision, Jan, 2026-07-28, mid-P5).** The 40%
denominator included `CC.lean` (170 lines of program text, fixed by
definition) and `CCGraph.lean` (242 lines of graph mathematics), neither
of which the kit targets — the campaign's own evidence table splits
math / program / glue and aims at glue only. Jan authorized re-setting
the target on that split: **the four glue files (`CCPhases`, `CCSearch`,
`CCSweep`, `CCMain`, baseline 1,263 lines) come out at ≤ 40%, i.e.
≤ 505 lines.** `CC.lean` is untouched; `CCGraph` is measured and
reported but ungated. The stop-and-return-to-Jan consequence of a miss
is unchanged.

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

- [x] **P1 frame rule — done, both acceptance tests passed.**
- [x] **P2 spec triples — done, acceptance passed.**
- [x] **P3 `run_vcg` tactic — done, acceptance passed.**
- [x] **P4 data-structure library — done, both acceptance criteria passed.**
- [x] **P5 pilot retrofit (Lax11 CC) — done; gate MISSED** (1,152 vs 505
  on the re-cut glue gate). Per the plan: **stopped**, P6 not started,
  verdict and options below for Jan.
- [ ] P6 remaining retrofits — **blocked on Jan's call** (see P5 verdict)
- [ ] P7 pins and drafts (registration excluded, JAN-FLAG)

### P1, as built (2026-07-28)

`word-ram/proofs/Lax13Proofs/Frame.lean`, imported from
`Lax13Proofs.lean`. Everything below is green with zero `sorry` across
all three packages.

- `Com.wvars`, `Com.warrs`, `Com.reads` as planned, plus decision
  procedures for `Com.reads` **and for `Com.NoWrite`** — the latter so
  the output tape joins the other three fields in being framed by one
  `by decide`, instead of `Run.out_eq` needing `simp [Com.NoWrite]`.
- `Run.frame_var`, `Run.frame_arr`, `Run.frame_inp`, on `BigStep` first
  (`BigStep.vars_eq` / `.arrs_eq` / `.inp_eq`) and lifted, following
  `BigStep.out_eq`. Plus `Run.frame_vars_eqOn` / `frame_arrs_eqOn` for
  the whole-function case.
- Equation lemmas materialized in-package for all three new match
  definitions, per the standing kit rule.

**Two shape decisions taken, both minor, both reversible.**

1. `Com.reads` is `Prop`-valued as the plan writes it, with a
   hand-written `Decidable` instance by the same recursion, rather than
   `Bool`-valued. It keeps `reads`/`NoWrite` in one style.
2. **The framed name is an explicit argument**: `h.frame_var "m"
   (by decide)`, not `h.frame_var (y := "m") (by decide)`. These are
   used inside `rw` chains, where the implicit form needs a named
   argument at every step. This also makes the retrofit textually a
   one-for-one swap: `hvar₄ "m" (by decide) (by decide)` becomes
   `r₄.frame_var "m" (by decide)`.

**Acceptance, part 1 — done.** `readLoop_run`
(`Lax11Proofs/CCPhases.lean`) lost three of its four frame conjuncts
(`arrs` off its own array, `out`, `vars` off `i`/`t`); `σ'.inp = rest`
stays, being a consumption fact and not a frame condition. `ReadInv`
lost the same three and with them its `σ` parameter — the invariant no
longer mentions the initial environment at all. **All twelve** call
sites rewritten and green (the plan said eight; Lax15's two `Main`s
added four more): `CCSweep`, `VCMain`, `TreeFoldMain` ×2,
`CourcelleMain` ×4, `Lax15Proofs/Main`, `Lax15Proofs/Main3` ×2. Two
`@[simp]` lemmas were added next to `readLoop` — `warrs_readLoop`,
`wvars_readLoop` — so that a call site with a *bound* name discharges
its obligation by `by simp [h]` against the disequality it already has.

**Acceptance, part 2 — done (2026-07-28).** `Scanned` /
`not_scanned_ne` and the parallel `Scanned3` / `not_scanned3_ne` are
deleted. `ScanInv` and `ScanInv3` frame against `descendScan.wvars` /
`descendScan3.wvars`, as the survey predicted, and the eight
`obtain ⟨h1,…,h9⟩ := not_scanned_ne hy` blocks are gone.

- Two kit lemmas carried the retrofit. **`Run.frame_var_sub`** frames a
  sub-phase against an enclosing command's list — `h.frame_var_sub y
  hsub hy` — which is what the invariant's conjunct needs at every turn,
  since a turn is a `slotStep` but the invariant speaks of the whole
  scan. **`notMem_wvars_ne`** turns a frame hypothesis into the
  disequality an older lemma still asks for, `by decide` per name.
- The inclusions `slotStep.wvars ⊆ descendScan.wvars` and
  `ownerAdvance.wvars ⊆ descendScan.wvars` are `by decide`, proved once
  per file and named. Measured: both, plus `"m2" ∉ descendScan.wvars`,
  elaborate in well under a second at default heartbeats.
- Six of the eight sites became a **one-line term**, `(r.frame_var_sub y
  hsub hy).trans (hfr y hy)`, once the turn's run was given a name
  (`have rslot : Run B slotStep ρ₁ … := …` ahead of the `refine` that
  used to build it inline). That naming is worth doing on its own: it is
  also what P3's tactic will produce.
- The two `hI₀` sites — the invariant on the scan's seven-`setVar`
  register prefix — stayed `simp`, since the prefix of a right-nested
  `seq` is not a subterm and so has no run to frame off. They cost one
  `notMem_wvars_ne … (by decide)` per name.
- `hall` / `hfrall`, the hand-rolled frame chains through the two block
  lemmas, went away with their only uses.

**A statement shrank too.** `descendScan3_run` exported
`∀ y, ¬ Scanned3 y → τ'.vars y = τ.vars y`; the conjunct is deleted and
its one consumer (`Loop3.lean`, for `"n"`) now reads the fact off the
run it already holds, `hrun₀.frame_var "n" (by decide)`. This is the
`readLoop_run` pattern of part 1, and it is the shape every phase lemma
should end up in.

Net: **−14 lines** across `Phases`, `Phases3` and `Loop3`, +17 in the
kit. The point is not the count — it is that none of the eight sites
mentions a variable name any more.

**Timings.** Full `lake build` after the change: `word-ram/proofs`
2,955 jobs / 8.5 s; `ram-linear-time/proofs` 3,012 jobs / 1 min 16 s;
`vertex-cover-ladder/proofs` 3,017 jobs / 2 min 41 s. No before-numbers
were taken, and P1 changes too little proof text for a regression to
hide; from P2 on, take the baseline first.

**Line count.** Call sites came out line-neutral, as expected — P1 pays
in the *statement* (four conjuncts and one parameter off `readLoop_run`
and `ReadInv`, ~14 lines of proof) and in not having to re-establish
frames when phases compose. The line win the campaign is after is P2–P4.

### P2, as built (2026-07-28)

`word-ram/proofs/Lax13Proofs/Spec.lean`, imported from `Lax13Proofs.lean`
and by `Lax15Proofs/Program.lean`. Green with zero `sorry` across all
three packages.

`Spec B P c Q K` is the rev-1 definition unchanged. What shipped with
it: `Spec.run` and **`Spec.of_exists`** (the bridge from the existing
`∃ ρ' K, Run … ∧ K ≤ … ∧ Q` phase-lemma shape, which every retrofit will
cross), `mono`, `conseq`, `pre`, `post`, `frame`, `skip`, `assign`,
`store`, `seq`, `seq'`, `ite`, `while_potential`, `while_count` and
`forRange`.

Three shape decisions, all reversible:

1. **`Spec.frame` strengthens a postcondition rather than being a rule
   with a frame premise.** `h.frame` conjoins all four frame conditions
   — `wvars`, `warrs`, `reads`, `NoWrite` — onto `Q`, asking the caller
   nothing. A user picks the one wanted with `by decide`. This is what
   makes the composite below mention no intermediate state.
2. **The loop rules keep `Run.while_potential`'s step obligation
   verbatim**, existential cost and all. A `Spec`'s single `K` cannot
   express a per-turn cost that varies, and that is exactly what an
   amortized loop needs, so the potential stays where it works and the
   `Spec` packages only the *exported* constant.
3. **`Spec.forRange` is stated over `while x < m do c`, not over a new
   `Com` combinator.** Every flat scan in the repo already has that
   syntax; a combinator would have meant editing program text and every
   cost proof underneath it. The caller owes a body spec that moves `x`
   up by one, and `x ≤ N`, `x, m < B`; it owes neither a potential nor a
   variant, and gets back `σ'.vars x = N` rather than a failed condition
   to read again.

`lt_of_condLt_true` and `le_of_condLt_false` **moved into the kit** from
`Lax15Proofs/Phases.lean`, where they had been sitting as local lemmas
with eighteen uses across three files. `Spec.forRange` needs them, they
are about `Cond` and not about vertex cover, and the move is invisible
at the call sites — but note the failure mode it caused on the way:
until the Lax15 copies were deleted, every use was an *ambiguous term*
error, not a shadowing warning.

**Acceptance — passed.** `countBlock_run` and `seenBlock_run` are now
`countBlock_spec` and `seenBlock_spec`, and `countSeenBlock_spec` is
their composition, built by

    ((countBlock_spec h1B).frame.pre …).seq (seenBlock_spec h1B).frame hmid hpost

with `hmid` and `hpost` written entirely in frame lookups
(`hQ.2.1 "seen" (by decide)`) — no `obtain`, no reassembled `refine`,
no `Run` mentioned. The composite is stated **in the slot's initial
environment only**: the intermediate state is gone, because each half's
registers cross the other half by the frame rule. The two verdicts are
named (`CountVerdict`, `SeenVerdict`, `abbrev` so that `rcases` still
sees the disjunction) rather than written twice.

`descendScan_run`'s residual-slot branch consumes the composite: two
`obtain`s became one, and the six hand-written translations from the
intermediate environment (`hseenρ₃`, `ht1ρ₃`, `hfoundρ₃`, `hvρ₃`,
`hv₃u`, `hv₃w`) became `by simp` against the `setVar` that is now the
only thing between the two environments. The arrays, the input and the
output tape come off `rblk` by `frame_arrs_eqOn` / `frame_inp` /
`out_eq`, all `by decide`.

**Numbers.** `Phases.lean` +22 lines net (the two `abbrev` verdicts and
the composite's own statement, against 25 lines saved at the call site
and 14 by the two lemmas leaving for the kit); `Spec.lean` is 300 lines
including its header. Elaboration: `Lax15Proofs.Phases` 18 s before and
after, full `vertex-cover-ladder/proofs` 1 min 55 s against the 2 min
41 s recorded in P1 — no regression, and the interface costs nothing at
elaboration time.

The line win is still ahead: P2 pays when phases are *written* in
`Spec`, not when one composition is retrofitted. What P2 proves is that
a real pair of phase lemmas fits the interface and composes as a term.

### P3, as built (2026-07-28)

`word-ram/proofs/Lax13Proofs/Tactic.lean` (626 lines including seven
worked examples), imported from `Lax13Proofs.lean`. Green with zero
`sorry` across all three packages. Written by an Opus subagent under
supervision, per the working model.

**The tactic is `run_vcg`, not `run_step`** — it executes a whole
block and closes the goal, so the planned name would have lied. It
takes a goal `Spec B P c Q K` *or* the legacy
`∃ σ' K', Run … ∧ K' ≤ K ∧ Q` shape, walks skip / assign / store /
seq / ite, splits every `ite` on its arithmetic test (the split
hypothesis is inaccessible by design — reachable by `simp_all` /
`omega` / `‹_›`, never by a guessed name), discharges each `< B` and
array-range obligation with `omega`-then-`simp; omega` where the
precondition covers it, defers the rest, checks the cost itself, and
leaves one postcondition goal per control-flow path in that path's
final environment. `run_vcg [spec₁, …]` steps *over* a named
sub-program by its `Spec` instead of into it — that is how loops and
already-proved phases enter a block, and an unhandled `while` /
`read` / `write` with no matching spec is a clear error, not a goal
with metavariables.

Both VCF-session-6 hard requirements are honored: the derivation is
built as a `have` chain via `assert` with consumed runs cleared
(never one nested term), and no `if_neg (by decide)` inside rewrite
lists. The helper rules live in `RunStep` — the kit's `Run` rules
restated with every argument explicit and in fixed order, plus
per-`Bop` evaluation lemmas so values normalize to `m + n` and four
`cond_*` lemmas so splits are on `ρ.vars "x" = 0`, not on a `Bool`.

**Deviations from the plan's P3 text, both recorded and accepted.**
No attribute-registered spec set — the bracket-argument mechanism
covers the acceptance targets (`recordFound` is simply walked
through) and the attribute can be added when P4 gives it a customer.
And the `< B` obligations are deferred individually rather than
merged into one conjunction — `omega` proves conjunctions natively,
so the merge bought nothing, and separate goals report better.

**Acceptance — passed.** `countBlock_spec`: 21 proof lines → **2**
(`run_vcg <;> simp_all` plus a comment). `seenBlock_spec`: 51 → **3**
(`run_vcg <;> (try simp_all) <;> omega`). Statements byte-for-byte
unchanged, cost constants 20 and 30 untouched. Elaboration of
`Phases.lean` is neutral: supervisor-measured 22.1 s wall / 39.0 s
user before, 20.9 s wall / 39.2 s user after, same machine, same
method (`lake env lean`). The subagent's ~35 s "before" numbers were
taken under load; wall time on this machine swings and the
multi-threaded user time is the steadier figure — take three samples
before claiming a regression either way. Full
`vertex-cover-ladder/proofs` build 1 min 52 s against P2's 1 min 55 s.

**For P4.** State `Lib/*` postconditions as `abbrev` — `run_vcg`
head-normalizes the postcondition goal, so an `abbrev` verdict
arrives as a disjunction `simp_all` can chew, a `def` arrives opaque.
`run_vcg [·]` is the seam P4 aims at: each `Lib` operation exported
as a `Spec` on a named `def push : Com` becomes one step of a
caller's block, matched by `isDefEq` without unfolding. `Lib/Csr`'s
amortized scan stays hand-written (loops are content, not
bookkeeping); the tactic removes the straight-line text around it.
Metaprogramming notes for whoever touches `Tactic.lean` next:
`MVarId.changeLocalDecl` renumbers fvars (re-read after), and
`Lax13Proofs.Imp.Expr` collides with `Lean.Expr`, so the walk writes
both fully qualified.

### P4, as built (2026-07-28)

`word-ram/proofs/Lax13Proofs/Lib/` — `Basic`, `Ind`, `Stack`, `Trail`,
`Queue`, `Csr` plus the `Lib.lean` aggregator, ~2,850 lines, imported
from `Lax13Proofs.lean`. Green with zero `sorry` across all three
packages; built as four Opus-subagent units (Ind, Stack+Trail, Queue,
Csr), each reviewed and committed separately (P4a–P4d), plus a
supervisor read-through of every line at the end.

**The shape.** Fixed by unit 1 and written into `Lib/Ind.lean`'s
header as a numbered note (points 0–7) that later units followed
verbatim; read it before writing a sixth module. The load-bearing
choices: per-module namespaces inside `Lib` (`Ind.test`, `Stack.push`,
`Queue.push` coexist); relations are plain `def`s over `arrOf` + a
pointwise cell function with every pointwise invariant *inside* the
relation (the `Finset`/`List` views of the plan's table are derived
sections, never the relation — same resolution as P1's `Bool`/`Prop`
and for the same cost reason); operations are `Com` defs parameterized
in every name they touch; each exports one `Spec` plus its four frame
facts as `@[simp]` (call-site names are bound variables, so `simp`,
not `decide`); pre/postconditions are `abbrev`s; every array read's
obligations are pre-loaded via `Spec.pre` in **both** `getD` forms and
scalar bounds in state form (the two refinements units 1–2 paid for);
every relation ships `of_eq` + `setVar_iff` or composites cannot
close; every module ends in a worked example `#guard`-checked
**through the compiler and the machine** via `Lib.runOut`.

**The modules, and the consumer-evidenced deviations.**

- `Ind`: test/mark/unmark at cost 3; the 0/1 bound lives in the
  relation so every op's word obligation is `1 < B`.
- `Stack`: push/pop/peek at cost 7/7/5; capacity and entry bound in
  the relation; `setTop`/`raise` exported as push's halves
  because *neither consumer has a single-array stack* (three or four
  arrays share one top; a parallel push is n stores + one bump).
- `Trail`: logs **indices into one companion array**, undo writes
  `0` — no (index, old-value) pairs, because no consumer has them.
  `unwind` is the kit's first exported loop: `Spec.while_count`, cost
  `12·(h−base) + 4`, one `Spec` with the loop inside.
- `Queue`: the plan's `advance` ships as `front` + `advance`, because
  in both consumers the head read and the head bump are separated by
  the whole row scan (their comments say why); `drain` is a
  **combinator with the body open** over `Spec.while_potential` — the
  turn cost is the dequeued vertex's degree, so `while_count` cannot
  state it.
- `Csr`: relation over two arrays and *no scalar* (its `setVar_iff`
  is unconditional; `of_eq` is free across every mark/label store);
  `owner_lt`/`owner_unique`/`off_lt` replace the hand-derived
  `hult`/`owner_unique`/`hOB` of both drivers. One `Com` (`scan`), two
  combinators: `rowScan_spec` (per-row, `(Kb+4)·len + 4`, step in
  `∃ K'` form so it nests as a `Queue.drain_spec` step) and
  `ownerScan_spec` (two-pointer amortized; the caller declares
  `Δj`/`Δu`/cost per turn and **never writes the potential**). Neither
  combinator mentions the relation — forced by the acceptance test,
  since `rowLoop_run` has no offsets array in its hypotheses; the
  relation supplies the combinators' inputs as separate lemmas.
  `loadRow`/`slot` shipped beyond the plan's two ops (every site opens
  with them); `loadRow_spec` is the kit's one hand-written spec — its
  second read follows a write of `j`, and the general rule is recorded
  in the module header: *a read of a scalar after a write to another
  scalar in the same block must enter `run_vcg` as one handed `Spec`*.

**Acceptance — both passed.** Every module's `#guard` example runs
the compiled machine program (`Ind` `[1,0]`/32 steps, `Stack`
`[7,7,5]`/64, `Trail` `[1,1,0,0]`/143, `Queue` `[5,5,7]`/90, `Csr`
`[0,1,0,2,1,0,2,1]`/301). And the Csr criterion was demonstrated for
real: **`rowLoop_run` is re-proved through `rowScan_spec` with its
statement byte-for-byte unchanged** — proof 220 → 202 lines (the
`while_potential` plumbing left; the ~180 lines of mark/trail
bookkeeping are caller content and stayed), `Phases.lean` elaboration
neutral (20.5/38.6 s before, 21.3/38.4 s after, 3 samples).

**Survey evidence for P5's gate** (from the Csr unit): of the seven
scan-shaped loops at the six sites, five are direct instances of the
two Csr combinators (`rowLoop_run` retrofitted; `rowScan3_run`,
CC's `scan_run`, `descendScan_run`'s outer loop, VC's `scan_run`
covered); `drain3_run` is `Queue.drain_spec` with a Csr row scan as
its body, and `rootSweep_run` is a counter loop (`Spec.forRange`
territory), not a CSR scan.

**Timings.** Per-file elaboration: Ind 4.5 s, Stack 5.4 s, Trail
7.9 s, Queue 5.7 s, Csr 6.4 s; `word-ram/proofs` no-op ~2 s; full
`vertex-cover-ladder/proofs` 1 min 39 s against P3's 1 min 52 s. Both
downstream packages import kit modules, not the root, so `Lib` reaches
them only when a retrofit asks it to (verified by trace: nothing
downstream rebuilds).

**Supervisor review (Jan's request).** Every line of the session's
output re-read at the end. One change made: `Csr.step` renamed
`Csr.off_le_succ` — it collided semantically with `Queue.step` (an
operation lemma) and with its own module's step vocabulary. Flags left
open, in priority order for a pre-P5 look:

1. **`tryClose` in `Tactic.lean`**: a deferred obligation whose
   discharger partially succeeds surfaces as a hard error instead of a
   leftover goal (hit by units 1 and 2, worked around by point-5
   pre-loading everywhere). Root-cause before P5 leans on the tactic
   at scale.
2. **`run_vcg [·]` matches handed specs by command text, first match
   wins**: a block using one operation twice with the same names takes
   the first spec both times and fails loudly but confusingly.
   Match-and-pop (ordered consumption) is the candidate fix.
3. **Lax15 `Phases3.lean` has a local `structure Queue`**: the P6
   rung-C retrofit will hit the P2 ambiguous-term failure mode if it
   `open`s the Lib namespace; rename the local one first.

### P5, as built (2026-07-28)

Six commits: pre-P5 tactic flags (`847538b`), P5a CCPhases (`dd7fea0`),
gate re-cut (`27866fd`), P5b kit gaps (`58c1882`), P5c CCSearch
(`ac4569f`), P5d kit gaps (`cf7572d`), P5e CCSweep+CCMain (`02f27e8`).
All built by Opus subagents under supervision, one unit per agent, each
reviewed and committed separately. Three packages green throughout, zero
`sorry`, exported statements (`ccCom_solves`,
`exists_linearTime_program_ccLabels`, `readLoop_run`) byte-identical,
cmp-verified.

**The number.** The four glue files landed at 145 + 494 + 372 + 141 =
**1,152** against the re-cut gate of 505 (40% of the 1,263 glue
baseline). **The gate is missed by 2.3×**, and per the plan the campaign
stops here: P6 is not started pending Jan.

**Why, by glue category** — the pilot's real product. The plan's four
categories behaved differently:

1. **Symbolic execution shrinks hard.** `scanBody_run` 151→88 (−42%),
   `ccCom_run` 153→93 (−39%), CCPhases 218→145 (−33%) with all three
   loops on `Spec.forRange`/`Lib.Fill`. Where glue is walking a block,
   `run_vcg` deletes it.
2. **Composition shrinks when grouped.** The unit-C lesson: a handed
   spec makes its post-state opaque, so it restates facts *per phase*;
   a frame lookup inside one spec pays *per fact*. Handing four
   consecutive commands as ONE prefix-matched spec is what took 60
   lines off `ccCom_run`; handing the phases separately would have
   grown it.
3. **Invariant hand-off does not shrink and can grow.** `expandBody_run`
   +11 on the kit route (P5d, recorded in CCSearch's header):
   re-establishing `ScanInv`/`DrainInv` field by field across each
   opaque step costs more than the hand-built reads the kit removes.
   Same call at two smaller sites (`Queue.push` at `scanBody`,
   relation conversion beats two lines).
4. **Relational-potential loops keep their content.** `outerBody_run`
   unchanged at 120: its cost is relational in the global potential,
   which `Spec`'s constant `K` cannot state. `sweep_spec` shows the
   boundary: `Spec.while_potential` + `.frame` converts the potential
   to a constant at the *outermost* wrap only.

**The structural reason the gate was unreachable here**: ~330 lines of
the four files are Base/Live/enqueue/sweep *mathematics* and another
large block is invariant/statement text — the CC driver keeps its math
in the glue files, unlike the Lax15 evidence (where math sits in
`Config`/`Solver` files) from which the 65%-glue figure and the 40%
gate were derived. Even at zero machine glue the four files floor near
~470. Net honest motion: 1,263 → 1,152 (−9%) on the driver that had
the least removable glue, while **elaboration got faster at every
single site** (CCPhases −45%, CCSearch/CCSweep −13%, CCSweep again
−1 s in P5e; not one regression all pilot).

**The kit grew by ~900 lines** it did not have at P4 — all
consumer-driven, all one-time: tape rules (`Spec.read`/`write`,
`run_vcg` walking both), `Spec.forRangeZero`, explicit `forRange`
args, `Lib/Fill`, seq-**prefix** spec matching (`SeqSplit`/`seq_split`
+ `usePrefix`), relational `Queue.drain_run` (now the primitive;
`drain_spec` derived), `Csr.ownerScan_run`, `LoadRowPost` naming its
state. Plus four latent bugs root-caused and fixed: `tryClose`
swallowing partial discharger failures (Lean's `Tactic.run` resets
`recover`), first-match-wins spec reuse, `mdata`-wrapped goals
rejected, `costTac`'s unreachable `omega` branch.

**Open kit gaps, priority order for whatever comes next**: (1) `inpTac`
runs `simp_all` over the whole context and can diverge on innocuous
hypothesis pairs, surfacing as a recursion-depth error at the `run_vcg`
call naming nothing — have `tryClose` defer instead of propagate, and
name the obligation in the error. (2) The straight-line `Lib` post-state
abbrevs (`SlotPost`, `PushPost`, `FrontPost`, `AdvancePost`) should name
their final state as `LoadRowPost` now does. (3) `RunStep.read`'s
post-state mentions `σ` three times — k consecutive reads give a
3^k-sized term. (4) No `run_vcg … with h` naming form for handed
postconditions (hence the `SetupPost`/`Swept` abbrevs). (5) `Queue.Pre`
demands `t + 1 < B` even for `front`. (6) Handed specs elaborate before
the walk, so they cannot mention data an earlier step produced —
inherent, but undocumented until `sweep_spec`'s docstring.

**Options for Jan** (owner call; the plan stops here by design):

- **(a) Close the retrofit arm: declare P6 out of scope** — the plan
  explicitly allows this ("the kit is useful with no retrofits at all")
  — and go to P7 (pins + drafts), which closes the campaign and
  un-gates the ND-MC RAM phases. The pilot's evidence is that the kit's
  economics favor *new* code written in `Spec` form from the start
  (grouping chosen up front, invariants stated once, no hand-off tax),
  which is exactly what ND-MC P5–P7 will write. This is my
  recommendation.
- **(b) P6 selectively**, only where symbolic-execution glue dominates
  (the Lax15 rung-B/C `Phases`/`Phases3` block lemmas match category 1;
  the P4 survey found five of seven loops are direct Csr instances),
  under a per-file go/no-go instead of a blanket 40%.
- **(c) Re-design toward the NREST-shaped fix** for category 3 (the
  hand-off tax) — per-component refinement relations so a phase
  touching only the marks does not re-establish the whole invariant.
  That is the plan's own "revisit only after P5's numbers are in"
  clause; the numbers are now in, and they say category 3 is the
  binding constraint on retrofits.

## Handoff notes

The next session picks up at **P5, the pilot retrofit of the Lax11 CC
driver** (`CC`, `CCPhases`, `CCGraph`, `CCSearch`, `CCSweep`,
`CCMain`, 1,655 lines), behind the hard gate: **≤ 40% of 1,655
lines or stop and bring the design back to Jan.** The P4 as-built
note above carries the retrofit recipe the Csr unit left: the drain
body decomposes as `Queue.front_spec` + `Csr.loadRow_spec` +
`Csr.rowScan_spec` + `Queue.advance_spec` under `Queue.drain_spec`;
build the `Csr` relation once from `SearchEnv`'s fields and carry it
with `of_eq`; `Csr.off_lt`/`Csr.lt` replace `hOB`/`hTB`; keep the row
scan's cost a *term* at the drain step. Address flag 1 (and ideally 2)
above before or at the start of P5. Statements of exported theorems do
not change; only proofs do.
Working model, per Jan: **Fable supervises, Opus subagents write the
Lean.** Concretely — the supervisor holds the plan, decides scope and
acceptance, runs the builds and commits; each proof-shaped unit (one
lemma family, one file's retrofit, the tactic) goes to an Opus agent
with the relevant statement, the acceptance test, and a pointer to this
plan. Do not let the supervisor read whole 1,800-line proof files: that
is what the context is being saved for.

Standing facts a spawned agent needs and will not find on its own:

- Build with `lake build` inside the package directory; `concepts/`
  before `proofs/`. The three packages take 8 s / 1 min 16 s / 2 min 41 s
  from cold-ish, so batch edits before rebuilding.
- The packages use **sibling path requires**, so a change in
  `word-ram/proofs` is visible to Lax11 and Lax15 with no re-pin during
  development. Re-pinning is P7's job.
- A new match-defined kit function needs its equation lemmas
  materialized in `Lax13Proofs` — see the note in `Frame.lean`.
- Frame obligations: `by decide` for a literal name, `by simp [h]` for a
  bound one given the disequality.
