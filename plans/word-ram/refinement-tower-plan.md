# Refinement tower plan — a Sepref/NREST port for the word RAM

Rev 3, 2026-07-29 (revs 1–2 earlier the same day). **Status: OPEN —
accepted by Jan 2026-07-29, all four JAN-FLAGs resolved; P0 is the next
session's work and does not pause for review.** This document is the
contract: implementing sessions follow it, deviations need an owner
decision first.

**Working model** (unchanged from the IMP+ toolkit campaign): Fable
supervises — plan, sequencing, review, acceptance calls, commits — and
Opus subagents write the Lean. Scope is **proofs-only**: no concept
surface anywhere in the repo changes, no `lean-toolchain` or mathlib pin
moves, and the machine model (`Lax13/Ram.lean`, `Lax13/RamComputes.lean`)
is not touched.

## The fidelity charter (the governing rule)

Jan, 2026-07-29: the Isabelle Refinement Framework's years of production
experience are **much higher priors than our own experiments**. Unless
there are *extremely good reasons*, stay close to the source.

Operationally:

1. **Ported components follow the source's design** — judgment shapes,
   phase structure, rule organization, even internal phase names, so that
   their debugging methodology and papers remain usable as manuals.
2. **Deviations are ledger entries** (see "Deviation ledger"). Each entry
   records the source's design, the source's *rationale* (researched in
   the papers/sources, not guessed), our deviation, our reason, and the
   fallback if the deviation proves wrong. Admissible reason classes:
   *substrate-forced* (Isabelle/ML → Lean 4, HOL → DTT) or
   *extremely good reason* (documented, Jan-visible).
3. **Our own campaign lessons enter as additions and library
   conventions** — refutation tooling, default instances — never as
   changes to ported judgments or calculus. Where a local conclusion
   conflicts with the source's design, the source wins by default; the
   ledger records the conflict.

## Goal

Make algorithmic results cost what mathematical results cost. Today an
algorithm is verified *directly*: the IMP+ program and its invariants are
hand-authored, then proved with the Lax13 kit. The ND-MC RAM record shows
where that spends supervision: hand-authored intermediate obligations were
the site of essentially every failure (all eight RamDriverIO obligations
refutable as written; `symCom` an unsatisfiable stub; the n² full-array
init cost mistake; ball-chain aliasing), while the proofs themselves were
never the hard part. The math half of the same campaign — where every
statement is frozen in advance and objects are persistent — ran at a
fraction of the friction.

The tower inverts the workflow, following Lammich's stack: write the
algorithm **once, abstractly**, prove it there (a math-side-shaped proof),
and *synthesize* the imperative program, its invariants, and its
obligations mechanically. The refutable-obligation failure class becomes
unrepresentable because nobody authors the obligations.

The IMP+ toolkit plan pre-registered this decision: "Revisit [the NREST
port] only after P5's gate is passed and the numbers are in." The numbers
are in: the retrofit gate missed 2.3× (1,152 vs 505), and the categories
that missed are exactly the ones synthesis removes (invariant hand-off,
frame threading) rather than the ones tactics compress.

## Architecture

Four layers, top three ported, bottom one ours:

```
  abstract algorithm         NREST monad: nondeterminism + resource
    |  refine (⊑)            currencies; proofs live here (math-shaped)
    v
  structured refinement      relators, rule DBs (Autoref-style)
    |  sepref translate      hn_refine judgment, SL with time credits,
    v                        frame inference, linearity discipline
  IR ("irM")                 purpose-built monadic IR, word-RAM op set,
    |  verified codegen      per-op cost, SL lives here
    v
  IMP+ Com                   the endorsed bottom; `computesInTime`
                             statements land here, unchanged in meaning
```

Two structural decisions already made in conversation with Jan
(2026-07-29), recorded here as settled:

- **The bottom stays the word RAM.** The claims (C0-style) are
  trans-dichotomous word-RAM claims; the machine model is part of the
  theorems' meaning and is the endorsed, already-future-proof layer.
- **The middle layer is a purpose-built IR, not literal LLVM.** Literal
  LLVM fails on word size (fixed i64 vs parametric w = Θ(log n) —
  lowering through it yields bounded-input theorems, not asymptotic ones)
  and buys nothing since Isabelle artifacts don't port as code anyway.
  The IR follows the *shape* of Isabelle-LLVM's basic layer; if a
  cost-carrying Lean-LLVM semantics ever materializes in the ecosystem,
  it slots in as a **sibling target of the same IR** (fan-out), never as
  a serial layer above IMP+.

## Sources (canonical; P0 pins exact versions)

| source | what it is the source *for* |
|---|---|
| AFP `Refine_Monadic` (Lammich) | nres monad, refinement calculus, pw-reasoning, `refine_vcg` |
| Haslbeck's NREST (ITP'19 *Refinement with Time*; ESOP'21 *For a Few Dollars More*; thesis 2021) | resource-currency generalization, `timerefine`/exchange rates, cost-carrying `hn_refine` |
| AFP `Automatic_Refinement` (Lammich, ITP'13) | relators, rule-DB machinery, side-condition solvers |
| AFP `Refine_Imperative_HOL` (Sepref, ITP'15/JAR) | the synthesis tool: phase pipeline, hnr rule DB, frame inference, linearity, IICF interface style |
| Isabelle-LLVM (Lammich, ITP'19–) | the two-stage lowering shape; the basic-layer IR design; evidence the back end is swappable |
| `Std.Do` (our pinned toolchain) | local evidence that attribute-driven Hoare/VCG machinery hosts well in Lean 4 |

Sources are consulted via targeted fetches (AFP browser, authors'
repositories); nothing is vendored into this repo. Design notes and
extracts go to `plans/word-ram/refinement-tower/`.

## Relation to existing work

- **The IMP+ kit is not deprecated.** It becomes (a) the proof harness
  for the P5 code generator — `Spec`/`run_vcg` prove the per-constructor
  lowering lemmas — and (b) the tool for any residual hand-written
  program. Its `while_potential` is the bottom-level shadow of the
  credits the tower carries.
- **ND-MC finishes on the current kit.** No replatforming mid-campaign;
  this tower does not block, touch, or wait for ND-MC files. Namespace
  isolation is total (own subtree, no edits outside it). The two
  campaigns run **in parallel** (Jan, 2026-07-29): this one is not
  gated on ND-MC's C0, and its sessions operate in their own worktrees
  alongside the ND-MC ones.
- The IMP+ plan's "aliasing-free environment beats separation logic"
  finding **stands for the bottom layer** and is *not* contradicted:
  IMP+ keeps its aliasing-free environment. The tower's SL lives at the
  IR/synthesis layer, where the source says it is load-bearing (ownership
  of refinement assertions under destructive update). Charter rule 3
  applied; see ledger N1.

## Phases

Each phase lands green with zero `sorry`, is committed on its own, and is
reviewed before the next starts. The standing kit rule applies throughout:
every match-defined function materializes its equation lemmas upstream
(namespace/splitter discipline). Elaboration wall-clock is recorded per
phase. Every executable layer gets `Decidable`/`#eval` instances and
Plausible property checks the day it lands (ledger D4) — obligations and
rules are fuzzed before they are proved.

### P0 — Sources and the design record · budget 1–2 sessions

Acquire and pin the sources; read them against our substrate. Deliverable:
`plans/word-ram/refinement-tower/design.md` — a component-by-component map
(Isabelle artifact → Lean counterpart → substrate delta), the opened
deviation ledger, a draft of the `hn_refine` statement in Lean, the IR op
set, and the package-placement decision (JAN-FLAG 1). The design record
is **flagged for Jan's review post-hoc** (flag 4 resolution: no hard
gate — the campaign proceeds at its own cadence; Jan's comments fold in
as plan revisions). Nothing in P0 writes Lean.

### P1 — NREST core · budget 2–3 sessions

Port `Refine_Monadic` in its NREST generalization directly (the source's
own end state; plain nres is the degenerate instance): the monad with
resource-valued results over currency maps, `⊑`, SPECT/RETURNT/bindT/
ASSERT/REC/WHILE/FOREACH, pointwise reasoning, the monotonicity framework,
`timerefine` with exchange rates, and the abstract VCG driven by
attribute-registered refinement rules.
*Acceptance:* the masked depth-capped BFS algorithm (RamBfs's content)
specified and refined abstract-to-abstract, cost riding the ordering, in
textbook shape.

### P2 — Relators and rule databases · budget 1–2 sessions

Port `Automatic_Refinement`'s spine: the relator zoo (`fun_rel`,
`prod_rel`, `list_rel`, `option_rel`, …), attribute-based rule databases,
and the side-condition solver hooks. Substrate translation is the work
here (locales → structures/typeclasses, named_theorems → attributes).
*Acceptance:* an autoref-style derivation reproducing a tutorial example
from the source distribution.

### P3 — The IR and its separation logic with credits · budget 2–3 sessions

The purpose-built monadic IR, shaped after Isabelle-LLVM's basic layer,
instantiated to the word-RAM op set: ℕ scalars and ℕ arrays (matching
IMP+'s clean-ℕ data model with the word bound at the boundary), arithmetic
/comparison/indexing ops, structured seq/ite/while, an explicit cost per
op. Over its state: separation-logic assertions **with time credits**
following ESOP'21 ($-assertions pay costs), the frame rule, and the
entailment/frame solver (`sep_auto` analogue).
*Acceptance:* hand-proved credit-carrying triples for array get/set/fill.

### P4 — `hn_refine` and the translate phase · budget 3–5 sessions

The heart, ported at maximum fidelity: the cost-carrying `hn_refine`
judgment; Sepref's phase pipeline **under the source's own phase names**
(operator identification, monadify, translate, cleanup) so `sepref_dbg_*`
debugging methodology transfers; the hnr rule database with `fcomp`
composition against pure relators; the linearity/ownership discipline for
destructive updates; frame inference per the source's algorithm (it is
algorithmic, not raw higher-order unification — this is what makes it
portable to Lean's weaker HOU), with explicit annotation as the documented
fallback where inference fails.
*Acceptance:* synthesis of IR code plus proof for small annotated abstract
programs (array reverse; filter-count), with legible failure states at
each phase.

### P5 — The verified code generator, IR → IMP+ `Com` · budget 2–3 sessions

Compile structured IR to `Com` against a layout map; per-constructor
correctness and cost lemmas proved **with the existing IMP+ kit**;
constant-factor cost preservation end to end; the cashing theorem — an
`hn_refine` triple at the IR plus the codegen theorem yields a
`Transfer.Solves`/`computesInTime` statement of the shape the concept
surfaces consume. This is the one component without an Isabelle original
(their final LLVM step is a trusted printer; ours is verified into the
deep embedding — ledger D3, an upgrade the deep embedding affords, not a
design change).
*Acceptance:* P4's toy programs land at `computesInTime` mechanically.

### P6 — Collections (IICF port, narrow) · budget 2–3 sessions

The IICF interface style, instantiated to the structures this repo
actually uses: plain arrays; Trail-backed touched-only arrays **as the
default array instance** (ledger D5 — a library convention, the calculus
is untouched); CSR graphs; stack; queue; bitmask sets. Each: abstract
interface, hnr rules, credit specs.
*Acceptance:* every structure's rules are consumed by the P4 translator
on an exercise program without bespoke tactic work.

### P7 — The gate: RamBfs re-derived · budget 1–2 sessions

Re-derive the masked depth-capped BFS through the tower, exporting the
same Spec-shaped postcondition `RamBfs.lean` exports today, consumable by
`RamCover` unchanged. Measured against the direct-verification baseline
(`RamBfs.lean` @ 570a49e, **1,201 lines**):

- **authored lines** — abstract program + abstract proof + annotations +
  manual patches; tower and library excluded;
- **hand-written frame/memory clauses** — target **zero**;
- **supervision interventions** — counted from the session log.

Gate proposal (JAN-FLAG 2): authored ≤ **400 lines** (≈ math-side share
of the original) with zero hand frame clauses. Pass ⇒ the tower is the
default for the next algorithmic campaign. Miss ⇒ P8 records why, with
options, in the imp-toolkit-P5-verdict style.

### P8 — Wrap · budget 1 session

Deviation-ledger review with Jan; handoff notes; adoption decision;
index/README and memory updates.

**Total budget: 15–24 sessions.** At observed campaign velocity (recent
phases landing at their lower bounds) this is roughly two to three weeks
of overnight work — set expectations by the budget, not the recent luck.

## Deviation ledger (seeded; P0 completes it)

| id | source design | our position | reason class |
|---|---|---|---|
| D1 | Isabelle/ML tactics, locales, named_theorems | Lean 4 metaprograms, structures/typeclasses, attributes | substrate-forced |
| D2 | Imperative/HOL heap / LLVM as target | purpose-built word-RAM IR bottoming at IMP+ `Com` | extremely good reason: the claims' meaning lives on the endorsed word RAM; fixed-width LLVM cannot state parametric-w theorems (conv. w/ Jan 2026-07-29) |
| D3 | final LLVM emission is a trusted printer | codegen verified into the deep embedding | upgrade afforded by the deep embedding; no design intent changed |
| D4 | (no analogue) | executable instances + Plausible fuzzing gate every layer | addition, not deviation — an agent workforce needs refutation-before-proof |
| D5 | IICF leaves cost-spec shape per instance | touched-only, Trail-backed arrays are the *default* instance | library convention; NREST calculus untouched (n² lesson, ND-MC record) |
| N1 | SL + ownership at the synthesis layer | **adopted as-is**, although the IMP+ record argued aliasing-free-beats-SL — that finding was about direct `Com` verification, not synthesis; source wins per charter | non-deviation (charter rule 3) |
| N2 | — | iris-lean **not** adopted for P3; the source's own small SL is ported instead; iris-lean stays a watch item | non-deviation; maturity risk on our pinned toolchain |

## Not in scope

- **Replatforming ND-MC.** It finishes on the current kit; C0 does not
  wait for this campaign.
- **Literal LLVM semantics** as a layer, in either direction (rejected
  with reasons above; fan-out to a future Lean-LLVM sibling target stays
  possible by construction).
- **Concept surfaces, the machine model, `lake update`.**
- **Concrete surface syntax** for abstract programs (a `do`-macro front
  end); the source's combinator style is the deliverable, sugar is a
  separate short task later.
- **Porting IICF beyond the named structures.** Breadth follows demand
  from the next consumer campaign.

## Watch items

- **Elaboration time is a first-class acceptance criterion** (house
  rule). Rule-DB-driven tactics are where Lean elaboration typically
  degrades; record wall-clock per phase, compare against the kit-only
  baseline at P7.
- **Lean's higher-order unification is weaker than Isabelle's.** The
  mitigation is fidelity itself — Sepref's frame inference and operator
  identification are algorithmic — plus the annotation fallback. If a
  phase finds itself fighting `isDefEq`, that is a design smell to raise,
  not to grind through.
- **DTT/universe friction in the relator layer.** `Std.Do` is the local
  existence proof that this class of machinery hosts well; if relators
  force universe gymnastics, prefer the source's monomorphic instances
  over clever polymorphism.
- **Namespace/splitter discipline** per the standing audit rules; the
  tower is helper-only, the archive ignores it, downstream reaches it
  through proofs requires (the accepted "discouraged but allowed"
  pattern).
- **Supervision legibility.** Every synthesis failure must name its phase
  and its unmet side condition; a tool that fails opaquely spends the
  scarce resource this campaign exists to save.

## JAN-FLAGs (all resolved by Jan, 2026-07-29)

1. **Package placement: `word-ram/proofs/Lax13Proofs/Refine/`** —
   helper-only, reachable via the established sibling-requires pattern,
   no new package plumbing. (Recommendation accepted.)
2. **P7 gate as proposed**: authored ≤ 400 lines, zero hand-written
   frame/memory clauses, exported Spec shape consumable by `RamCover`
   unchanged. (Recommendation accepted.)
3. **Sequencing: NOT blocked by ND-MC** — Jan overrode the
   start-after-C0 recommendation; execution can begin next session, in
   parallel with the ND-MC campaign, each in its own worktree.
4. **P0's design record is NOT a hard review gate** (Jan, 2026-07-29,
   revising the rev-2 resolution). It is written and flagged for Jan's
   post-hoc review; P1 may start without waiting. Review comments fold
   in as revisions — the fidelity charter and the deviation ledger are
   the standing protections in the meantime.

## Progress log

(campaign accepted 2026-07-29; P0 next)
