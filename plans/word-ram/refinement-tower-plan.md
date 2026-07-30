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

- **2026-07-30 — P6 COMPLETE (one session vs 2–3 budget; acceptance
  PASSED: every structure's rules consumed by the P4 translator on
  exercise programs, zero frame clauses, zero bespoke tactics).**
  Design record `p6-iicf-design.md` (69f164f) + extracts (e9ec5cd).
  **P6-A** (arrays, 521d8d3→merge 3eef624): `Iicf/{Basic,IicfArray,
  IicfTrailArray,ExercisesA}.lean`; mop_array_fill and ALL THREE
  trail-array impls synthesized by our own sepref_synth (the pop-loop
  reset included); the D5 characteristic theorem
  `treset_cost_touched_only` (reset cost a function of the touch
  counter alone). **P6-B** (structures, b7ada37→merge a76f5a6):
  `Iicf/{IicfStack,IicfQueue,IicfCsr,IicfBitmask}.lean`; all ten op
  bodies synthesized, composite rules as four-line wrappers (D-bc:
  the frame matcher cannot look inside composite assertions — raw
  synthesis + wrapper is the pattern); nine exercises incl. a
  cross-structure loop (stack pop + bmInsert). **Pipeline findings
  (P4 untouched, recorded for a future thaw):** (1) frameMatch splits
  goals but never rule-side prodAssn — route tuple state through
  hnr_mop_pair; (2) operator phase does not backtrack across rule
  choice (junk-destination binop beats in-place when scratch is free)
  — forced stack-grows-downward + write-twice dodges; a mop_move with
  live destination is the clean fix; (3) two arrayAssn conjuncts in
  one prodAssn loop state trip proveConjEq inside sepref_ac (valid
  permutation, in-situ rfl failure) — read-only arrays belong in the
  frame anyway; (4) hnr_bind blocks value-dependent guard rules —
  branch on the returned value, convert back by lemma. Convention
  divergence at merge (flagged, not reworked): P6-B's
  hnRefine_reinterp/hnr_pre_ex_pure duplicate P6-A's
  hnRefine_res_cast'/hnr_pre_*_conv in role; init-from-junk takes
  concrete xs (B) vs junkArrayOfLen (A); dedupe queued for P8 or a
  thaw wave. New mathlib import: Combinatorics.Colex (one simp
  lemma). P7 opened the same night: gate design note
  `p7-gate-design.md` (4c895c7 — counting rule fixed, package
  boundary P7/S-1: export in word-ram at P1's masked/WD over the
  alv-derived mask, no Lax3/Lax12 imports); wave A (bfsQ middle
  refinement) dispatched satellite.

- **2026-07-30 — P5 COMPLETE (one session vs 2–3 budget; acceptance
  PASSED: the P4 toys land at machine-level `computesInTime`
  mechanically).** Design record `p5-codegen-design.md` (113718a +
  Spec-shape addendum — the P7 consumer `bfs_spec` is a cells-based
  `Spec`, so the primary cashing export is Spec-shaped; the
  Solves/computesInTime route wraps it with the tape harness, ledger
  N3). **A1** (`Codegen/{Embed,BigStepB,Sim}.lean`, 115aa60→merge
  c6a3fa5): name-identical embed, `Ir.BigStepB` — refuted the design's
  "creation-sites-only" side conditions (literal guards need bounded
  cond evaluation, P5/D-i), simulation `embed_sim` with the cash factor
  EXACTLY 4 (every weight is the embedded op's IMP+ cost on the nose;
  no Classical.choice). **A2** (`Codegen/Harness.lean`, 47c8f9a→merge
  32b115d): readScalars/readArr/writeScalar/writeArr + three marshal
  glue lemmas from `initEnv` to `σ'.out`, machine-gate runs incl. cost
  cross-checks; kit had NO tape-loop Spec lemmas (all new; Fill reused
  for the read loop). **B** (`Codegen/{BoundVcg,Cash}.lean` +
  `Codegen/Examples/EndToEnd.lean`, c032bdc): `bwp` bounds-VCG +
  `runs_while`; `spec_of_hnRefine` (hypothesis-form readout, P5/D-af);
  cost chain affordability → SPEC bound → `cash_le_ecash` (tight) →
  numeral; filter-count `K = 32n+17`, reverse `K = 49n−2`, axioms
  pinned, machine runs #guarded. **Bounds telemetry closes P5/D-a: the
  annotation proper is ~10 lines/program (6+1 `<B` goals) — the
  `wordAssn` retrofit is NOT taken; P4 stays frozen.** Refuted/found en
  route: `omega` is blind through the `Ir.Val` abbrev (bind indices at
  ℕ); the root `lax` gate caught a `List.lookup` splitter leak that
  `lake build` misses. Backlog: computable twins vs
  `List.filter`/`List.reverse` #guarded not proved; a writes-none
  `Spec` combinator; per-toy `B x = x.sum + 2` is coarse. P6 opened the
  same night: design record `p6-iicf-design.md` (69f164f; IICF over
  fixed cells, init-from-junk replaces new/free, impls synthesized by
  our own sepref_synth per the source's "by sepref" idiom,
  trail-backed touched-only arrays as the D5 default), extracts
  e9ec5cd; waves P6-A (arrays+trail) and P6-B (stack/queue/CSR/bitmask)
  dispatched satellite.

- **2026-07-30 — P4 COMPLETE (one session, under the 3–5 budget;
  acceptance PASSED). Wave C f427b67, acceptance 0cd0f72.** **Wave C**
  `Sepref/{Constraints,Frame,Translate,Tool,Definition}.lean` + Attrs
  (+3,304 l): CONSTRAINT/CN_FALSE with the slot as a MetaM store (D-cd),
  frame_tac = P3's `fri` plus the Sepref match rules (D-ch), `hnr_bind`
  with `abstractPost` junking binder-dependent conjuncts (D-ct), tuple
  states via `hnCtxt_prodAssn` + split-retry + `mopPair` (D-cu),
  `LOOP_VARIANT` caller-supplied (D-cv, dies when Rec.lean exports
  fuel-stability), nine-phase driver under the source's phase names +
  the 11-entry `sepref_dbg_*` table, `sepref` tactic + `sepref_synth`
  command. **Synthesis is by metavariable instantiation — the source's
  own mechanism (D-cm); the fallback two-step mode was never needed.**
  Refuted mid-build: definitionally-equal mops collide (each mop needs
  its own currency). Flags D-ca…de. **Acceptance
  `Sepref/Examples/Acceptance.lean` (762 l, 323 authored):** in-place
  array reverse + filter-count (an If inside a While body) written at
  the user layer (`monadicWhileIT`/`MIf`, user currencies), pushed
  through `⇓C irE` (new `ExchOk` calculus + `irWhileIT_mono`), then
  synthesized mechanically — **zero hand frame clauses, synthesis
  2.8 s/1.8 s, axioms pinned clean, zero wave-C defects found**. 13
  positive `#guard`s on computable twins, 3 pinned negative controls,
  and a pinned 34-line legible `trans`-phase failure naming the missing
  `junkCell`. Flags D-ea…ee (notably: `whileIET` is definitionally
  cost-free so `monadicWhileIT` is the exchangeable user loop; a
  measured-loop destination is the loop state, with the array-shaped
  corollary recovered by entailment). Backlog carried to P5+:
  reverse=`List.reverse` proved only by sample (List.set invariant,
  out of P4 scope); ExchOk/`irWhileIT_mono`/`mopPair` placement moves
  at next thaws; dependent `hfcomp`; unfueled while rule; `inres`
  still unported. **P4-gate seed for P7: 323 authored lines for two
  synthesized programs, 0 frame clauses.** P5 opened the same night:
  design record `refinement-tower/p5-codegen-design.md` (113718a) —
  embed/agree, `Ir.BigStepB` with creation-site-only side conditions,
  simulation at cash factor ≤ 4, Spec-layer I/O harness, cashing
  theorem; the value bound is a genuine per-program obligation (P5/D-a:
  IR bounds VCG now, `wordAssn` retrofit recorded as fallback if P7
  telemetry demands it); waves A1 (embed/sim) + A2 (harness) satellite.

- **2026-07-30 (overnight) — P4 waves A+B landed (extracts ab58c34, A
  fb594c3, B1 e5e417b, B2 5915bc7 merged d771d6d); wave C (translate/
  frame/tool) dispatched.** Deep extracts: all ten `Sepref_*.thy`
  fetched whole at the pin (full SHA 42dd7f59…) — correction: the
  cost-carrying MERGE calculus EXISTS in `Sepref_Basic.thy` (ported,
  not derived); the If/While translate-rule gap stands. **Wave A**
  `Sepref/{Basic,Rules}.lean` (963+413 l): `hnRefine` clause-for-clause
  with the source's `'c` kept as a destination-descriptor parameter
  `d : κ` (P4/D-a — supersedes design §5's ∃ᵃ draft; that shape is the
  scalar instance); `pureAssn` generic (D-b); `invalid_assn` split into
  the verbatim pure marker + `deadAssn`/`junkCell` ownership sinks
  (D-c — no dealloc in the substrate); MK_FREE degenerates to
  entailment, bind = the source's own `hnr_bind_manual_free` shape as
  `hnr_seq` (D-d, proof follows the source's cost threading; the two
  cost lemmas it needed are `enat_resSub_add` + `leCostECost_add_right`);
  MERGE entailment-form (D-e); pass rule pays skip (D-f); GC stays
  credits-only (D-g). fref/hfref/hrComp/attainsSup/`hfcomp` at the
  non-dependent instance (dependent form = named backlog). No design
  objections; `returnT a ≤ m` needed no vocabulary delta. Agent flags
  D-h..D-p (incl. `leof` not ported — augment_res premise unfolded).
  **Wave B1** `Sepref/{Attrs,IrOps,CombRules}.lean` (70+820+651 l):
  the three Translate DBs; mop layer at pinned ir.* currencies (F4);
  six `@[sepref_fr_rules]` in hnCtxt discipline (aset destructive =
  the linearity showcase; scratch = caller-owned `junkCell`, D-ab);
  exchange lemmas — equality at MIf, ≤ at the loop (both reasons
  recorded), concrete map `irE` + `wfR''_irE`; `CondRefine` fused-guard
  judgment (D-af, substrate-forced — no bool cells); `hnr_If` via
  MERGE; **`hnr_while_measured`** landed via the fueled route — post
  is `Γ` with the result riding the judgment's own R-slot (self-
  composing; induction = plain Nat.rec, no WellFounded plumbing), no
  INV premise (invariant rides `nofailT`); unfueled general rule's
  blocker named: Rec.lean lacks `nofailT (RECT B s) → ∃ n, fuelIter
  B n s = RECT B s` (D-ai). Vacuity pinned explicitly (badInv gate).
  Flags D-aa..D-aj. **Wave B2** (parallel satellite, seeded worktree)
  `Sepref/{IdOp,Monadify}.lean` (1008+1151 l) + 5 DBs in
  Autoref/Attrs.lean: PROTECT2/λ₂/PR_CONST/ID calculus verbatim with
  the protect walk + DF_SOLVE_FWD stuck-trace driver; monadify's six
  sub-phases as term-level `monadifyCore (pps, a) → (a', h : a = a')`
  (goal wrapping is wave C's, D-bk); arity/comb equations for
  returnT/MIf/whileT/whileIET (Bfs-evidenced coverage; whileIT does
  not exist in P1 — it is whileIET). Four substrate bugs refuted and
  pinned: Lean accepts `@[congr] SP_cong` but rewrites under SP anyway
  → explicit `rewriteDB` walker (ACCEPTED, supervisor, substrate-
  forced — the biggest structural delta from the source text); pattern
  DBs are rule-nets, not simp sets; net matching needs `withReducible`;
  DB entries need universe instantiation. Flags renumbered m..ab →
  ba..bp at merge (range collision). Backlog accumulated for later
  waves: result-pairing for tuple loop states (REQUIRED in wave C),
  `bindT_mono_res`/`mono2_monadicWhileBody`/`monadicWhileIT_unfold_pure`
  /`bindT_returnT_gen` placement moves at next P1 thaw, dependent
  `hfcomp`, `sepref_copy_rules` unpopulated, unfueled while rule.
  Verification at each wave: lake green (3,014 jobs at merge), lax
  audit from archive root, axioms ⊆ {propext, Classical.choice,
  Quot.sound} on all spot-checked decls. Session note: repeated
  server-side 529 overloads cost the early night ~1.5 h of agent
  restarts (no work lost — on-disk state + transcript resume).

- **2026-07-29 (late) — P3 COMPLETE (one session, under the 2–3-session
  budget) — acceptance passed.** Three waves + one extraction, commits
  600d985/bb7ff84/0c19fee/888efde. Extraction:
  `p3-sl-deep-extracts.md` (byte-exact `cost_framework` locale,
  `Frame_Infer.thy`, `Basic_VCG` surface, AFP sep-algebra chain,
  `ll_load/ll_store` + range rules). **Wave A** `Ir/{Syntax,Semantics}`
  (D-a…D-i): `Val = ℕ`, binops ARE `Imp.Bop` (reused, not copied),
  16 `"ir.*"` currencies, `Cost = ACost String ℕ`, deterministic
  `BigStep` charging one currency per op, `evalFuel` twin proved
  equivalent both directions, out-of-range access stuck. **Wave B**
  `Ir/{Assn,Wp,Triples}` (2,408 l, D-j…D-x): AFP class stack
  `PreSepAlgebra→SepAlgebra→StrongerSepAlgebra→UniqueZeroSepAlgebra`
  with `Tsa`/Pi/Prod/`ACost` instances (D-j: typeclass surface is the
  source's own compositional carrier); carrier `AState = (Cells Val ×
  Cells (List Val)) × ECost` — §10.1 default taken, runs consume
  finite `Cost`, balances are `ℕ∞` (D-e); `¤c`/`¤¤n k` for the
  source's `$`/`$$` (D-l — `$` is Lean's antiquotation token; one
  header defect fixed in supervisor review); locales rendered per
  D-o/D-p: `generic_wp` a one-field class (frame/cons rules inherited
  by instance as the source inherits by interpretation), and **all six
  `cost_framework` locale axioms PROVED at `(leCostECost,
  minusECost)`** — the locale's assumptions became theorems; `wp` over
  `BigStep` with `wp_comm_inf` from determinism, per-op equations,
  `wp_seq` = the source's `wp_bind`; per-op credit triples exact + GC
  forms, `while_triple` = `llc_while_annot_rule` with
  invariant-carried credits (ESOP'21 discipline, D-x); D-q: IR
  statements have no result value → generic layer at `R = Unit`,
  results read from destination cells (design §5 updated post-hoc,
  this entry's session). Arrays are ONE cell, not a `sep_set_img`
  family (D-m — no IR op splits an array; index side conditions are
  `i < xs.length`). **Wave C** `Ir/{Attrs,SepSolver}` +
  `Examples/ArrayFill` (1,985 l, D-y…D-ak): `Frame_Infer.thy` whole —
  tags + four structural rules 1:1, the ML search loop as a `TacticM`
  solver keeping start/extract/round/end, `rotations_tac` as O(k)
  index selection through the same `fri_prems_cong` (D-y), credits by
  numeral arithmetic with ge/le reductions (D-aa), GC absorbs credits
  greedily at the back (D-ab), `entails_refl` first at end — the frame
  metavariable is instantiated by the residue, **no HOU anywhere**;
  five rule DBs as attributes (`fri_prepare_simps/fri_rules/
  fri_red_rules/fri_end_rules/vcg_rules`, the last populated with the
  IR op rules, closing wave B's D-u); `#guard_msgs`-pinned failure
  messages naming the unmatched conjunct. **Acceptance (the plan's
  criterion, met): hand-proved credit-carrying triples for array
  get/set/fill** — concrete IR programs, exact vectors (`get` =
  1·ir.aget; `set` = 1·ir.aset; `fill` = (n+1)·ir.while + n·ir.aset +
  n·ir.add via an invariant carrying `k • payload`), ALL frame
  reasoning solver-discharged (zero manual `sepConj`/`ac_rfl`/rotation
  steps in the acceptance file), the n=3 run derived from the exact
  triple down to `BigStep` with the full 16-currency vector
  `#guard`-pinned, Plausible cost-as-function-of-n on the `evalFuel`
  twin, and `fill_no_wrong_cost` (a wrong vector admits no derivation,
  by determinism). Verification: 3,007 jobs green, lax audit OK from
  archive root, axioms ⊆ {propext, Classical.choice, Quot.sound} on
  49 spot-checked decls across waves, wall-clocks recorded in
  reports (SepSolver 7.1 s full / 2.4 s net of gate). **P4 handoff**
  (also in `SepSolver.lean`'s header + wave reports): entry points
  `fri`/`fri_core`/`ir_frame`/`ir_frame_gc`, `irTriple_frame`/
  `irHtriple_frame` (= `htriple_vcg_frame_erule`), state readers
  `ptoVar_of_frame` etc., shapers `irTriple_pure`/`irTriple_ex`;
  gaps: goal-side `∃ᵃ` not solver-handled (port `fri_exI` if needed),
  `fri_red_rules` populated but not yet enumerated by the round loop
  (~20 l), `sepImp` has no consumer, no `PRECOND`/`PRIO` registry
  (`declare_solver` is the wiring point), solver never backtracks
  across rounds (complete while `fri_rules` = {refl}; revisit if P4
  registers overlapping rules), `x := y ⊕ y` needs monadify's
  duplicate-arg split, `inres` still unported (P2 carry-over).
  **P4 starts next session** at design §3's Sepref map + §5's updated
  `hnRefine`.

- **2026-07-29 (late) — GOVERNANCE: full project authority delegated
  to the supervising agent** (Jan, in-session: "i fully give up
  authority on this project, its all yours, you do not need to flag
  things for review for me. i will evaluate the final product").
  Consequences, recorded as owner decisions: the JAN-FLAG mechanism
  and the interim review queue are retired; the fidelity charter, the
  deviation ledger, and the D-flag discipline are UNCHANGED (they are
  what makes the final product evaluable — they now serve the final
  evaluation instead of interim review). Standing queue dispositions
  (owner = supervisor): P0 design record — accepted as-is (two phases
  of consumption constitute the review; defects surface as ledger
  events); `pw_conc_inres` refutation — resolution stands (true
  direction + hypothesis-free `bindT_refine`); B1 `ResSub` — stands
  (HOL-faithful minus-as-class, counterexamples `#guard`ed); FOREACH
  provenance — stands (AFP pre-currency, ledger-noted); §10.4
  vocabulary adjustment — stands; P2 extra-rules vehicle — stands
  (substrate-forced, no `notes`-attribute analogue); `#guard_msgs`
  DB-size canary — stays (deliberate); `autoref_nat_lit` catch-all —
  keep, revisit scheduled with the P4 backlog. Budget/phase structure
  and acceptance gates unchanged; P7's numeric gate remains the
  product-level evaluation target.

- **2026-07-29 — P2 COMPLETE (one session, at the budget's lower
  bound) — acceptance passed.** Four waves: A (single-owner) landed
  `Autoref/Attrs.lean` (the shared DB-attribute module of §10 default
  3 — all ten Autoref DB names registered by session end) and
  `Autoref/Relators.lean` (the zoo `funRel`/`prodRel`/`optionRel`/
  `sumRel`/`listRel` + characteristic suite under source names), plus
  the P1 thaw relocations (`br`/`relComp`/`SingleValued` →
  Relators with byte-identical statements; `consumea` → Basic;
  `ResSub` + backlog instances → ACost; **`inres` was a no-op** — P1
  had never ported it; still open, needs a fetch of the source's
  `inres` section). B1/B2 (parallel Opus satellites, seeded
  worktrees): `Param.lean` (33 `@[param]` rules incl. the `list_eq`
  route, `parametricity` seed tactic — no DiscrTree/`param_fo`/
  `to_relAPP`, flagged) and `Tagging.lean` + `Solver.lean`
  (tag layer axiom-free; `TaggedSolver` priority registry with
  `declare_solver`; its D4 gate caught a real dispatch bug). C
  (single-owner): `Phases`/`IdOps`/`FixRel`/`Translate`/`Tool`/
  `BindingsHOL` — the pipeline at the source's real order
  **id_op(10) → rel_inf(20) → fix_rel(22) → trans(30)** (the
  `p2-tool-extracts.md` pass corrected this record's three-phase
  framing; `rel_inf` is a phase of its own), uniform failure envelope
  naming phase + unmet side condition, `autoref` tactic +
  `autoref_synth` command, `autoref_rules` at 26 rules.
  **Acceptance: the source distribution's own tutorial — the
  `Autoref_Bindings_HOL.thy` §Examples suite — 7 of 8 entries
  reproduced mechanically (0 manual rule applications, synthesized
  terms `#guard`-checked in value, `hd`'s `SIDE_PRECOND` through the
  solver registry, the `GEN_OP`+`struct_expand` `list_eq` route
  exercised), 1 adapted (Isabelle sort-annotation pitfall with no
  Lean analogue — substrate note).** Legibility proven by
  `#guard_msgs` negative controls. Elaboration: Relators 41 s (4.2 s
  net of its D4 gate), Param 13.7 s (4.8 s net), others 2–8 s; whole
  package 2,999 jobs green, root lax audit OK, axioms clean.
  **Flagged for Jan** (adds to the P0/P1 standing queue): the
  extra-rules vehicle (Lean has no `notes [autoref_rules]` — local
  `(c,a) ∈ R` hypotheses are swept + `autoref [rules]` takes
  explicit ones); the `#guard_msgs` DB-size canary; `autoref_nat_lit`
  as a leaf-only ℕ catch-all (P4-relevant). **Backlog → P3/P4:**
  `ID_abs`/`ABS` ported, unexercised until monadify brings lambdas;
  `STRUCT_EQ` registered, unexercised (Collections material); trans
  rule choices untraced; six bonus DBs (`autoref_hom`,
  `autoref_post_simps`, `autoref_ga_rules`, …) need one
  Attrs-unfreeze wave; DiscrTree indexing absent everywhere (linear
  scans, flagged per site). **P3 starts next session** (IR + SL with
  credits; `p3-ir-sl-extracts.md` already in the repo).

- **2026-07-29 — P1 COMPLETE (one session, under the 2–3-session
  budget) — acceptance passed.** `BackwardsReasoning.lean` (1,964 l):
  gwp per source, vcg rule suite, progress, While rule, seed
  `@[refine_vcg]` tactic with an in-file costed-loop demo. **B1
  fidelity event:** mathlib's `Sub ℕ∞` truncates (`⊤−⊤=0`) where
  Isabelle's `enat` has `∞−∞=∞`; the ported `minus_p_m_bindT` is FALSE
  under mathlib's minus — resolved with a `ResSub` class (`-ᵣ`),
  HOL-faithfully, counterexamples `#guard`ed. `Examples/Bfs.lean`
  (1,051 l): the acceptance program — abstract masked depth-capped BFS
  (RamBfs's content: `d+1` sentinel, threshold-iff postcondition, F4
  currency budget) refined `bfsAlg ≤ bfsSpec` with `refine_vcg` driving
  to 12 one-line goals. **Telemetry (P7-gate seed): 481 authored lines
  (30 algorithm + 30 spec/invariant + 421 proof), 0 manual rule
  applications, 0 hand frame clauses** vs the 1,201-line RamBfs
  baseline — at the abstract level only; the tower below it is P3–P5's
  job. D4 checked the spec itself (decidable `WD` twin, negative
  controls, Plausible differential tests); no authored statement
  refuted. Honest limitation recorded: `⊑` alone admits result-free
  programs; non-vacuity is evidenced by the gate, not proved.
  Vocabulary adjustment vs design.md §10.4: mathlib `SimpleGraph`
  inside Lax13Proofs (cannot import Lax3/Lax12); the `WithinDist`
  bridge is the P7 consumer's one-liner.
  **Phase review (supervisor):** acceptance criterion met — specified
  and refined abstract-to-abstract, cost riding the ordering, textbook
  shape. Six vcg-hardening backlog items recorded by the acceptance
  session (progress_consume placement, wfR2 closure lemmas →
  TimeRefinement, spec-boundary Decidable pattern, sc_solve/norm_cost,
  MIf goal doubling → the P4 MERGE work, small-lemma rule for cost
  side conditions). Flagged-for-Jan queue before P2 builds on this:
  P0 design record (flag 4), pw_conc_inres refutation (S6), B1/ResSub,
  FOREACH provenance, §10.4 adjustment. **P2 starts next session.**

- **2026-07-29 — P1 wave 2 landed: Rec, Combinators, DataRefinement,
  TimeRefinement (two Opus satellites in parallel worktrees).**
  `Rec.lean` (581 l): `RECT = if mono2 B then gfp B x else ⊤` verbatim,
  lattice gfp with no ccpo machinery (the source derives everything
  downstream from the gfp form); fuel approximants make the fixed point
  kernel-checkable. `Combinators.lean` (617 l): `MIf`/`whileT`/
  `monadic_WHILEIT` per `NREST.thy`; FOREACH is absent from the cost
  artifact — ported from AFP `Refine_Foreach.thy` (pre-currency, ℕ∞).
  `DataRefinement.lean` (873 l): `⇓R`/`concFun`, `br`, `nrest_rel`,
  bind/consume refinement rules; **`pw_conc_inres` is refutable under
  the same-carrier `inresT` reading** (witness recorded in the module
  header) — only the true direction ported, the source's hypothesis-
  free `bindT_refine` shape used instead; substrate mismatch, not a
  source defect. `TimeRefinement.lean` (1081 l): `⇓C`/`timerefineA`,
  `wfR`/`wfR'`/`wfR''`, `pp` composition, `TId`, `timerefine_bindT_ge`
  (proof shortened past the source's `limRef` chain, statement
  unchanged), `⇓R`/`⇓C` commutation from `NREST_Main.thy` as an
  inequality (no equality exists — `⇓C` is not Sup-continuous). All
  green: 2974 jobs, lax audit from root OK, axioms clean, D4 gates ran
  on all four files (one agent-authored gate assertion falsified and
  corrected — never-exiting loop over an empty-result body is
  `SUCCEEDT`, not `FAILT`). Elaboration: 13.4 s + 21.6 s. Backlog from
  deviation flags: move `relComp`/`SingleValued`/`br` to
  `Autoref/Relators.lean` in P2; move `consumea`/`consume_alt2` into
  `Basic.lean` next time it thaws; upstream candidates
  `finsum_comm_of_support`, unbundled `gfp`, the `WithBot` lemma trio.
  Remaining P1: `BackwardsReasoning` (gwp + `needname`/`drm` classes),
  then the abstract masked-BFS acceptance.

- **2026-07-29 — P1 slice 1 landed (same session as P0).** `Refine/`
  exists: `Cost/ACost.lean` (currency type, pointwise lattice, `cost`,
  `ECost`), `NREST/Basic.lean` (`NRest` with the source's order and
  complete lattice built the source's way — mathlib has no
  `CompleteLattice (WithTop β)` to transport across; `returnT`/`spec`/
  `consume`/`bindT`/`assert` verbatim shapes), `NREST/Pw.lean`
  (`nofailT`/`inresT`, pw suite, `consume`/`bindT` monotonicity, the
  four monad laws at the source's own generality per F7),
  `NREST/Sanity.lean` (D4 gate: decidable finite instance, executable
  twins with proved agreement theorems, 13 `#guard`s + 6 Plausible
  `#test`s, negative controls confirm the harness discriminates — no
  divergence from source found). Build green 2970 jobs, `lax` audit
  passes, `#print axioms` clean on the laws; elaboration wall-clock
  31.7 s for the five new modules (recorded per house rule). Agent
  deviations D-a…D-i all reviewed and accepted, none touching ported
  judgment shapes; three local `WithBot` lemmas are upstream-candidate
  mathlib gaps. Remaining P1: `Rec`, `Combinators`, `DataRefinement`,
  `TimeRefinement` (satellite-parallel now that the `NRest` API is
  frozen), then `BackwardsReasoning` (+ the `needname`/`drm` class
  port), then the abstract masked-BFS acceptance program.

- **2026-07-29 — P0 complete (one session, at budget's lower bound).**
  Deliverables: `refinement-tower/design.md` (the design record —
  pinned sources, component-by-component maps for P1–P6, `hn_refine`
  drafted in Lean, IR op set v0.1, module skeleton, completed deviation
  ledger with new D6/N3, fidelity notes F1–F5, P1 defaults) and
  `refinement-tower/source-extracts.md` (verbatim `acost`/`nrest`/
  `bindT`/`timerefine`/`hn_refine` + theory listings, with provenance).
  Pins: AFP Isabelle2025-2 (2026-02-06) for Refine_Monadic /
  Automatic_Refinement / Refine_Imperative_HOL / NREST;
  `isabelle_llvm_time` @ 42dd7f5 (ESOP'21 artifact — the canonical
  cost-carrying stack); `isabelle_llvm` branch 2023 @ b44b639;
  Haslbeck thesis mediaTUM 1596032; `Std.Do`+`mvcgen` verified present
  in the pinned v4.30.0 toolchain (evidence only, not a dependency —
  note F5). Key P0 findings: NREST has a maintained AFP entry; the
  artifact's `thys/sepref` reuses the AFP Sepref file names one-for-one
  (fidelity is cheap); two scope facts entered the ledger — D6 (no
  general recursion at the concrete layer; IMP+ has no procedures) and
  N3 (the tower is tape-free; one kit-proved boundary wrapper at P5,
  matching `bfs_spec`'s already-tape-free export shape). Design record
  flagged for Jan's post-hoc review per flag 4. **P1 is unblocked** and
  starts next session: `Refine/Cost/ACost.lean` + `Refine/NREST/*` per
  design.md §3/§7/§10.
