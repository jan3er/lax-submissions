# Tower expansion plan — aggressive porting of the remaining refinement stack

Rev 6, 2026-08-02. **Status: OPEN — next is the leaf-gate script, then
P4.5.B (element-level ownership).**

Position: P0–P4 complete. P5.A complete and final — the eight interface
families are the battle-tested surface rule 5 protects; never reopened.
P5.B/C landed all twelve implementation families, to be re-seated by P5.E,
not re-derived. P4.5.A.1–A.3 are landed (range ownership, the costed O(1)
allocator, LIFO deallocation on two availability flavours — ledger E25–E28);
P4.5.B/C and the first P5.E re-seat close the phase. P5.D and `Impl_Heapmap`
are gated behind P4.5. The new **P4.6 synthesis probe** runs immediately
after P4.5 and before P5.D/E breadth.

Revision history, superseded decisions, and the reasoning behind each live
in `tower-expansion/ledger.md` (E31 indexes the plan's own revisions); this
document states only what currently binds.

This document is the contract: implementing sessions follow it, deviations
need an owner decision first.

## Governance and working model

Supervision is cost-tiered (Jan, 2026-08-02). **Opus supervises day to
day**: sequencing, briefs, independent build replay, acceptance of clause-1
(source-mirroring) work, commits. **Fable reviews at phase boundaries** and
owns the acceptance calls on clause-2 (authored) surfaces — cost layers,
invented relations, substrate architecture. The evidence for the split is in
ledger E31: worker output in the record is consistently strong, while the
recurring failure class is supervisor state-tracking and prose verdicts, and
the mid-phase review that produced F6–F11 was the highest-leverage single
session in the record — one boundary review is cheaper than the rework it
prevents. Proof workers are GPT-5.6-Sol via `codex exec`. Where practical,
one subagent owns a coherent phase or subphase; the supervisor audits its
source map and diff, requests corrections, independently rebuilds, and
commits. A worker's green report is not acceptance evidence until the
supervisor replays the relevant build and axiom gates.

Main-tree work is authorized. **Work sequentially on the already-warm
`main`** (Jan, 2026-08-01): no fresh worktrees, no parallel workers, no
brief-derived ceremony; this rule overrides seemingly required process
sections in inherited briefs. Finish one concrete proof task, review and
commit it, then start the next. Briefs remain technical reference only.

**Closure rule.** A finding, ledger entry, or plan obligation is closed only
by an edit that names the compiled artifact — theorem or `#guard` — that
closes it. Prose closures are not closures. Both false closures in the
campaign record ("finding 2 closed by finding 3"; §2.4's cost verdict) were
prose; every verdict that was compiled held.

Scope is **proofs-only**: no concept-surface changes and no toolchain or
mathlib pin moves. For the machine model, see the three-way table in the
fidelity charter — the endorsed machine is frozen; the IR is not.

**Falsification is provenance-scoped, per declaration — not per file, and
not blanket.** Every falsification-catchable defect this campaign has
produced (E20, F11) sat in the **authored cost layer**; not one sat in a
ported statement. Where our statement mirrors a statement Isabelle has
machine-checked, that proof *is* the falsification evidence and re-testing
it is redundant — but the exemption holds per *declaration*, never per file:
`ImplHeap.lean` is a port for its algorithms and an authored artifact for
its costs, because no pinned source carries a cost-carrying IICF at all
(F7). The rule:

1. **Mirrors a pinned source statement → exempt.** Source review,
   typechecking, kernel guards, and the build suffice. This preserves the
   waiver's intent and its velocity, which were real: ~15k lines, zero
   `sorry`, interfaces exact against source.
2. **No source counterpart → refute-before-prove, no exemption.** Every
   `*Cost` definition, currency vector, closed form, invented relation, and
   any generalization beyond what the source states. These have never been
   checked by anyone, here or upstream.
3. **Cost claims are unconditional** (`compiled-costs-both-directions`). A
   cost function that no theorem consumes is not exempt — it is the *most*
   likely to be wrong, since nothing else constrains it. E20 is the case in
   point: two cost functions were wrong precisely because nothing read them.

**Making it checkable rather than a judgment call.** Each module header
carries a source table mapping source declaration → Lean declaration. **A
declaration absent from its module's source table is authored by definition,
and clause 2 applies to it.** Where a file has no source table, every
declaration in it is authored. A reviewer checks two lists instead of
forming an opinion about a file's character.

`c1089c4`'s P3.C relaxations remain authorized for what they covered:
transcriptions of machine-checked AFP/IHT asymptotic theory, which are
clause-1 declarations. They are not authority for clause-2 declarations in
any phase.

## Mandate

Jan, 2026-07-31: *building infrastructure by porting known
Lammich/Haslbeck-style ideas is an order of magnitude cheaper than
hand-coding even a single submission — port aggressively; when in doubt,
it is better to port more than less.*

The evidence behind the mandate, from our own records:

- The tower campaign ported the entire four-layer stack in **three
  sessions** against a 15–24 session budget, every phase at or under its
  lower bound (`refinement-tower-plan.md`, progress log). Hand-coding the
  single RamBfs baseline had cost 1,201 lines and produced eight
  refutable obligations; the synthesized re-derivation had zero hand
  frame clauses and a computed cost within 12% of hand-tuned.
- Downstream failures repeatedly traced to partial ports of coherent source
  families rather than to the source machinery itself.
- The July worker retro (`plans/subagent-retro-2026-07.md`): refutable
  supervisor-authored surfaces are the largest rework class — exactly
  the class synthesis and tooling make unrepresentable.

The mandate applies to the source slices frozen by P0. Within a scheduled
slice, breadth is the default: port its coherent public declaration family,
not merely the theorem demanded by today's example. A plausible consumer
can justify selecting a slice during P0 or reconsidering one at P10; it does
not expand a live phase.

## The fidelity charter (inherited, one amendment)

Rules 1–3 of `refinement-tower-plan.md` apply verbatim: ported components
follow the source's design (judgment shapes, phase structure, rule
organization, internal names — the source's papers stay usable as
manuals); deviations are ledger entries with the source's researched
rationale and a fallback; our campaign lessons enter as additions and
library conventions, never as changes to ported judgments — where a local
conclusion conflicts with the source, the source wins by default.

**Amendment (rule 4, from the mandate): inside a scheduled source slice,
when in doubt, port more, not less.** Port the slice's coherent public
declaration family rather than stopping at "enough for the current
consumer". Whether to add a new source slice, example campaign, consumer
adaptation, or cross-submission repair is the opposite decision: defer it,
record it for P10, and keep the live phase source-faithful.

**Scope firewall.** P0's landed port map freezes active source slices and
phase assignments. Consumer examples run only after the source-facing API
is green and may not shape its judgments or automation. A consumer can
force an in-phase correction only by exposing that a scheduled source
declaration was mistranslated or omitted. Deferred, excluded, stretch,
revisit, and inventory-only items are not latent tasks during P1–P9.

**Amendment (rule 5, Jan 2026-08-02): guarantee fidelity outranks
representation fidelity.** Jan's ordering, verbatim:

> *"it is crucial to me that downstream consumers can use the same
> battle-tested isabelle interface with all guarantees. if an implementation
> yields the same guarantees but differs internally thats a bit less bad.
> but we had bad experiences in developing velocity when deviating from
> source. i want to port onto the modern stack you found."*

A downstream consumer must be able to program against the battle-tested
Isabelle interface and get *the source's guarantees*. This law retired the
P4-era "allocation is rejected" decision and produced P4.5. The three
classes, in descending severity:

1. **Guarantee deviation — forbidden.** A ported operation whose Lean
   statement is strictly weaker than the pinned source statement: extra
   preconditions, a partial result where the source is total, a success
   condition the source does not impose. Two are landed, both with the same
   added conjunct `boundedPush _ 0 ≠ none` against an unconditional source
   push: `arlAppendOp_refines` over `arrayListReadyRel`
   (`ArrayList.lean:362,415`, against `arl_append_hnr_aux`) and
   `daPushOp_refines` over `daReadyRel` (`DArrayList.lean:174,193`). Ledger
   E16. These require an owner decision before landing, not a module-header
   note; both are cleared by P5.E once P4.5 lands.
2. **Representation deviation — acceptable, ledgered.** Same guarantees,
   different internals: a different concrete encoding, a different proof
   route, a Lean-idiomatic restructuring. Ledger entry, then land.
3. **Substrate rendering — expected.** Isabelle/HOL vs Lean/mathlib
   spellings, tactic differences, locale packaging. Module header only.

A precondition that the *source also carries*, stated at the same scope as
the source states it, is not a guarantee deviation. Scope is the whole
question: a global program-level side condition (the source's "given
`malloc` succeeds", our "total allocation ≤ `2 ^ w`") preserves the
guarantee; the same condition pushed down onto each individual operation
destroys it. When rendering a source precondition, keep its scope.

**Velocity note (Jan, 2026-08-02).** Deviating from source has repeatedly
cost development velocity on this project. Rule 5 is therefore also an
economic rule, not only a correctness one: the cheapest path is the
source's, and a deviation must earn itself against that baseline.

**What "the machine model is frozen" means — three distinct things, only
one of them frozen.** The phrase was applied to all three during P1–P5,
which is what produced the class-1 deviations above.

| | what it is | status |
|---|---|---|
| **Endorsed machine** | `word-ram/concepts/Lax13/Ram.lean`: `State`, `Op`, `Instr`, `run`, `RunsTo`. The submission surface the endorsed theorems quantify over. | **Frozen permanently.** Changing it changes the claim and invalidates endorsement. |
| **The IR** | `Refine/Ir/Syntax.lean`: `Com`, `Cond`, `Operand`. Proofs-side scaffolding compiled to the endorsed machine by `Refine/Codegen/`. | **Not frozen.** New operations are allowed when they compile down and carry honest cost. Binding D3 still applies: verified codegen coverage before executable capital. |
| **"Allocation is rejected"** | A P4-era design decision, recorded as if it followed from the row above. | **Retired 2026-08-02.** It does not follow, and it is the direct cause of the guarantee deviations. |

## Sources (pins carried forward; P0 completes the table)

Carried unchanged from the tower campaign (`refinement-tower/design.md`):
AFP Isabelle2025-2 (2026-02-06) for `Refine_Monadic` /
`Automatic_Refinement` / `Refine_Imperative_HOL` / NREST;
**`isabelle_llvm_time` @ 42dd7f5** (the ESOP'21 artifact — canonical
cost-carrying stack, our primary source); `isabelle_llvm` branch 2023 @
b44b639; Haslbeck thesis (mediaTUM 1596032).

New sources this campaign pins in P0:

| source | what it is the source *for* |
|---|---|
| Zhan & Haslbeck, IJCAR'18 (`Imperative_HOL_Time` / SepLogicTime, + AFP `Amortized_Complexity`) | amortized analysis with time credits in separation-logic assertions; dynamic-array development (and a deferred skew-heap source, X16) |
| Haslbeck, `Sepreftime` | timed union-find and its source-native Kruskal validation; single-currency credit and foreach shapes used by the scheduled adaptations |
| AFP `Collections` (ICF, Lammich–Lochbihler) | the locale-based container-interface style at breadth; iterator discipline |
| Zhan & Haslbeck `Asymptotics_1D` / `_2D` / `_Recurrences` | the scheduled asymptotic machinery; mathlib `Asymptotics` is its Lean substrate |
| AFP `Landau_Symbols`, `Akra_Bazzi` (Eberl); Guéneau–Charguéraud–Pottier, ESOP'18 *A Fistful of Dollars* | semantic references only; they add no active source slice or API (ledger E2) |

Sources are consulted via targeted fetches; nothing is vendored. Design
notes and extracts go to `plans/word-ram/tower-expansion/`.

## Downstream-consumer boundary

ND-MC evidence motivates several source-slice selections, but it does not
design P1–P8. No consumer-specific API repair widens those phases.

**The firewall is one-directional, and the reverse direction is now a gate
(2026-08-02).** `nowhere-dense-model-checking/proofs/lakefile.toml` requires
`Lax13Proofs`, so tower changes propagate into ND-MC's build whether or not we
touch their files. P4.5.A.1's carrier widening broke two of their modules
(`Refine/AugmentSynth`, `Refine/ScatterSynth`) — sixteen sites spelling an
`AState` literally — and *our own gates could not see it*, because no landed
structure of ours constructs one: only probes do, and those were fixed in the
same commit that broke them. Same failure class as F9.

So **ND-MC must compile after every tower leaf that touches an exported
surface.** A full ND-MC build is 2m47s, which is per-leaf affordable. The
guarantee is specific and worth naming: strengthening a tower lemma leaves
ND-MC compiling, while *adding a hypothesis* — slipping an assumption onto
consumers — breaks it immediately, and that is the direction our own gates are
worst at catching.

**Compile gate only.** A break has exactly two dispositions: a genuine
interface break, which is fixed in the tower; or mechanical fallout, which is
a token edit in place. No ND-MC design work, no new lemmas there, no API added
for their benefit — anything else is recorded and goes to P9. This keeps the
firewall's purpose (consumer needs must not widen tower phases) while removing
its blind spot. P9 is the sole integration
boundary: it instantiates the frozen tower APIs, records consumer gaps for
handoff, and may send work back only when it demonstrates a source-fidelity
defect in a scheduled declaration. C0, B7, and the ND-MC P5 remain owned by
the ND-MC campaign.

One dated handoff obligation rides with the gate: P4.5 changed the cost
substrate (O(1) allocation, LIFO free, availability resources), and ND-MC's
residue arithmetic — `g2_exists` and the E-mem budget chain — was compiled
against the pre-P4.5 forms. Before the ND-MC campaign resumes its residue,
it re-runs that existence probe against the post-P4.5 cost model (the gate
is recorded in its plan); the tower owes nothing there beyond keeping the
compile gate green.

**Why each phase exists — traceability table.** Each entry is backed by a
compiled probe in the ND-MC record; P9 is the gate that has to cash these
claims. This is traceability, not authority: it does not license any
consumer work before P9.

| ND-MC blocker (compiled evidence) | missing infrastructure | phase here |
|---|---|---|
| THE SEAM — `orderCom` has no synthesized counterpart; whole-phase synthesis over 15 arrays judged intractable because `sepref_synth` goals are hand-holed (`Refine/OrderBridge.lean:36`, `Sepref/Definition.lean:24`) | `hfref` signature machinery + `FCOMP` composition | P1 |
| R1.6 — no member list exists; every pass carrier-bounded (`Refine/OrderBlockProbe.lean:65`) | FOREACH/`nfoldli` iteration layer: member lists as abstract iteration structure, refined downward | P2 |
| Uniform-per-turn `hKl` structurally loses the Σ\|X_c\| saving; no-escape theorem: no arithmetic interface between carrier closed form and arena form (`nd-mc-rebase-plan.md:243`, `Refine/OrderBlockProbe.lean:253`) | currency-vector budgets end-to-end, collapse once at cash; the `norm_cost`/`sc_solve` toolchain | P3 |
| Touched-only charging re-derived by hand per engine; per-arena credit threading ad hoc (`touched-only-costs` standing law) | credit-carrying composite assertions; amortization discipline | P4 |
| B7 gate findings were prose-audit escapes, found only by compiled probes (`nd-mc-rebase-plan.md:31`) | executable gates: slot sweep, cost probe harness | P8 |

Rev 5 adds one row the original could not have: every P5 structure's
`empty`/`new`/`copy` sits at a caller-owned boundary, so no closed IR program
can *construct* one — which P9 would have hit head-on at the consumer gate.
That is what P4.5 exists to remove.

Sequencing consequences recorded at acceptance (JAN-FLAG 1) are unchanged:
ND-MC's C0 residue resumes on this campaign's P1–P4 exports rather than on
hand repair; P9 executes the order-phase pilot as the consumer gate and hands
its output back to the ND-MC campaign, which runs its own B7 re-run and P5
under its own plan; and the ND-MC plan's two open supervisor recommendations
(the `Spec→ComputesInTime` bridge-seam probe, and the provisional-P5 draft
decision) stay owned there and are not preempted here.

## 2026-08-02 mid-phase review findings

Six findings from the P5 mid-phase review. F6–F8 correct P0; F9–F11 are
process failures. Each has a consequence scheduled below.

- **F6 — the IICF is not merely dead in the artifact, it is superseded.**
  P0's F1 established that `isabelle_llvm_time`'s `sepref/IICF/` is out of
  the build closure. The review found *what replaced it*. `thys/ROOT` keeps
  the IICF directories on the theory path but the `theories` entry building
  `"sepref/IICF/IICF"` is inside `(* … *)`; the only built target is
  `"examples/sorting/Sorting_Export_Code"`. That target's container
  substrate is `sepref/Hnr_Primitives_Experiment.thy` — *"Arrays and Option
  Arrays … monadic operations on lists and lists with explicit ownership"* —
  imported directly by `Sorting_Setup.thy`, which opens by shadowing the old
  assertion (`hide_const (open) LLVM_DS_Array.array_assn`) and documents
  `myswap` as *"swapping elements on array using option arrays internally"*.
  The timed development routed around the IICF deliberately: costing moves
  and swaps precisely needs element-level ownership, which the IICF's
  `hr_comp` style does not provide. The abandoned attempt is still visible
  as a `sorry`-ed `lift_acost` experiment block at `IICF_Array.thy:89–139`.
  *Consequence:* phase **P4.5** ports the successor substrate.

- **F7 — E7's premise is false: no cost-carrying IICF exists in any pin.**
  E7 scheduled P5 implementations "against Sepreftime's cost-carrying IICF
  (`enat`)". Sepreftime's `IICF_Array_List.thy` carries no cost text at all
  — plain `sep_auto` Hoare triples, no credits. AFP's IICF is uncosted by
  design; `isabelle_llvm_time`'s is dead. So the entire currency-vector cost
  layer of P5.B/C is authored from nothing, not adapted. `port-map.md`'s
  description of Sepreftime's IICF as "cost copies" is inaccurate and is
  corrected there. *Consequence:* ledger correction, and P4.5 supplies the
  cost-carrying substrate E7 assumed already existed.

- **F8 — source selection *within* the IICF was forced and correct; the
  "dead code" framing was not a source-quality verdict.** Tree listings:
  AFP 23 files, Sepreftime 30, both LLVM trees 22. `IICF_Array_Map`,
  `IICF_Array_Map_Total`, and `IICF_Array_of_Array_List` exist **only** in
  the LLVM trees, so the three leaves citing `isabelle_llvm_time` had no
  alternative. Diffing the pinned dead copy against the live
  `isabelle_llvm` 2023 copy: `IICF_Array_of_Array_List` and `IICF_Abs_Heap`
  byte-identical; the rest differ by 1–4 lines (debug leftovers,
  whitespace, `Mreturn` vs `return`, one `hrr_comp` arity). The text we
  ported is the live text. *Consequence:* no re-port needed on these
  grounds; cite the live pin for provenance where the text is identical.

- **F9 — the per-leaf gate could not see the archive law.** P5.B/C leaves
  landed "unrooted", gated by `lake build` alone. `lax build`'s
  `[root-module]` check requires the root to import every module of the
  package, so the archive gate had been failing since the first unrooted
  leaf, unobserved. Root-wiring all twelve (2026-08-02, `834b637`) built
  green at 3,275 jobs with no conflicts — but exposed two real
  `[namespace]` violations, both `GetElem?.match_1.splitter` from a
  `split at h` over a `getElem?` match, at `ArrayOfArrayList.lean:141`
  and `ArrayMapMap.lean:145`. *Consequence:* gate law below.

- **F10 — the deviation register stopped before the implementation
  campaign.** `ledger.md`'s last entry E15 predates every P5.B/C leaf.
  The register's own protocol (§5) requires an entry *before* landing.
  Twelve leaves landed with their deviations recorded only in module
  headers. *Consequence:* backfilled 2026-08-02; gate law below.

- **F11 — recorded fidelity checks are inert.** `implHeapSwimSourceCom` /
  `implHeapSinkSourceCom` (`ImplHeap.lean:519,536`) record the source's
  program shape and are referenced by no theorem. `ammSource*Bound`
  (`ArrayMapMap.lean:632–635`), `amtxSource*Bound`
  (`ArrayMatrix.lean:561–564`) and `daPinnedSourceBounds`
  (`DArrayList.lean:39`) record the source's cost bounds and are guarded
  only by `#guard`s restating their own definitions. Separately,
  `fillCost n` (`IicfArray.lean:256`) — the price of every array
  initialization, consumed at symbolic size by `ufInitCost`, `tinitCost`,
  `amtInitCost`, `amEmptyCost`, `ammEmptyCost`, `amtxDefaultCost` — has no
  theorem for symbolic `n`; the only facts are six `decide` evaluations at
  `n = 3`. *Consequence:* P4.5 and P6 items below.

## Phases

Each phase lands green with zero `sorry`, is committed on its own, and is
reviewed before the next builds on it. Every executable layer gets
`Decidable`/`#eval` instances and Plausible checks the day it lands
(ledger D4). Elaboration wall-clock recorded per phase. Dependency shape:
P1 → P2 → P3 forms the source/API spine; P4 followed P3; **P4.5 follows P4
and gates the remainder of P5**; **P4.6 — the orderCom synthesis probe —
runs immediately after P4.5's acceptance and before P5.D/P5.E breadth**,
because its outcome reprioritizes them (E30); P5 waves follow their declared
P1/P2/P4/P4.5 dependencies; P6–P8 run after the relevant APIs freeze; P9
alone integrates the consumer; P10 wraps and reviews backlog.

**Gate law (2026-08-02, from F9/F10).** A leaf is not green until, on the
day it lands: (i) it is imported from the package root — the "unrooted leaf"
pattern is retired, since it defeats `lax build`'s `[root-module]` check;
(ii) `lax build --only proofs word-ram` runs and its violation count is
reported, not just `lake build`; (iii) any departure from a pinned statement
has a `ledger.md` entry *before* the commit, per §5 of that file; (iv) the
ND-MC compile gate runs when the leaf touches an exported surface. A
worker's `lake build` report is not acceptance evidence for any of the four.
**The mechanical checks run as one command, `.claude/leaf-gate.sh word-ram`
(E31).** Landing that script precedes P4.5.B, and its first use validates
it; a gate that exists only as supervisor prose has already failed silently
once (F9). This is not P8 pulled forward — P8's Lean-side commands
(`#slot_sweep`, `#cost_probe`) stay where they are.

**The D4 clause above binds from P4.5, read through the provenance rule.**
"Every executable layer gets `Decidable`/`#eval` instances and Plausible
checks the day it lands" is contract text, but `Plausible` appears in **zero**
of the twenty P5 files. `#guard` is used well (8–22 per implementation file);
the falsification half is simply absent. D4 is therefore enforced as: clause-2
declarations (no source counterpart — every `*Cost`, currency vector, closed
form, and invented relation) carry Plausible checks and compiled negative
controls on the day they land; clause-1 declarations do not need them. The
per-leaf question a reviewer asks is not "is this file a port?" but "which of
these declarations are missing from the module's source table?".

P4.5's allocator and ownership layer are clause-2 throughout — they are
authored claims about a machine substrate with no source statement behind
them — so they carry Plausible checks, and the O(1)-allocation result and the
no-reuse invariant get compiled negative controls specifically. The no-reuse
invariant is the one whose violation silently restores an O(n) cost, so it
gets a control that fails loudly if reuse is ever introduced.

### P0 — Port map and new pins · budget 1 session

Diff the existing 69-file `Refine/` port against the pinned sources'
theory graphs and enumerate **everything** unported: theories skipped
whole, sections skipped inside ported theories (the progress log already
names many: `inres`, dependent `hfcomp` beyond the ND-MC port,
`sepref_copy_rules`, the six bonus Autoref DBs, `param_fo`/`to_relAPP`,
`ID_abs`/`ABS` exercise, GenCF), and the artifact's example suite. This is
an inventory: only the slices subsequently assigned a wave are active.
Pin the new sources. Deliverable:
`tower-expansion/port-map.md` — per item: source location, size,
dependencies, validation role, wave assignment, or an explicit exclusion
reason (rule 4: exclusions carry the burden). Opens this campaign's
deviation ledger. Nothing in P0 writes
Lean. Once P0 lands, only rows assigned to P1–P10 are active scope;
excluded, deferred, stretch, and inventory-only rows are reconsidered only
at P10.

### P1 — Signature machinery: `hfref`/`FCOMP` · budget 2–3 sessions

The judgments already exist (P4 wave A: `fref`/`hfref`/`hfcomp`
non-dependent; ND-MC P0: dependent `hfcomp` green). What is missing is
the machinery *around* them, ported at maximum fidelity from
`Sepref_Rules.thy` / `Sepref_Definition.thy` / `Sepref_Intf_Util.thy`:
`to_hnr`/`to_hfref` conversion, `FCOMP` composition with pure relators
and precondition intersection, the signature→goal derivation
(`prepare_hfref_synth_tac`'s role — retiring D-da's hand-holed
`hnRefine` goals), `sepref_register`/interface-type discipline
(`intf_of_assn`, TYPE annotations) so operators identify at scale.
*Acceptance:* (a) an existing pinned synthesis (`BfsQSynth`) re-derived
from an `hfref` signature with zero hand-written goal text, byte-identical
Com; (b) an `FCOMP` chain composing two synthesized operations against a
pure relator, reproducing a source tutorial example; (c) a multi-argument
(≥ 8 arrays) toy phase synthesized from its signature — the seam's shape
at exercise scale.

### P2 — Iteration layer: FOREACH/`nfoldli` · budget 1–2 sessions

Port the foreach stack in its cost-carrying form: `nfoldli` and the
FOREACH family with currencies. This is the E5 authored vector lift from
AFP's rule/invariant organization and the pinned single-currency
NREST/Sepreftime cost forms, not a transcription from the ESOP artifact.
iteration-list refinement (`list_set_rel`, `it_to_sorted_list`
discipline), the Autoref and Sepref rule sets for iteration
(`Sepref_Foreach`-class), so "iterate over exactly this set, in some
order, paying per element" is a first-class abstract operation.
*Acceptance:* the arena-walk exemplar — an abstract `nfoldli` over a
member list charging one currency per member, synthesized to a masked
concrete walk, with a **compiled carrier-blindness probe**: cost a
function of |members| alone, `#guard`ed at a 2-member arena inside a
100-cell carrier (the exact property ND-MC's E2b measured and the order
phase lacks).

### P3 — Currency discipline and asymptotics · budget 3–6 sessions total

P3.A/B are complete; allow 2–4 further sessions for P3.C's full
declaration-family port rather than compressing it to the consumer examples.

P3.A/B port per-operation currency usage, exchange composition,
`norm_cost`/`sc_solve`, and the source-native introsort budget spine. P3.C
then ports the pinned `Imperative_HOL_Time` `Asymptotics_1D`,
`Asymptotics_2D`, and `Asymptotics_Recurrences` machinery into mathlib
`Asymptotics`, preserving the source's declaration families and order:
one- and two-dimensional carriers; polylog, stability, and eventual
monotonicity; O/Ω/Θ introduction, elimination, composition, comparison,
and normalization; and the source recurrence theorem families. Isabelle's
ML registry/normalizer is rendered as named Lean rules unless a separately
scheduled tactic is required; it is not falsely claimed as a text port.
Mathlib's existing Akra–Bazzi theorem is reused and documented, not
duplicated. AFP Landau/Akra–Bazzi and CFML remain semantic references only.

Only after the source-facing layer is complete do BfsQ and introsort attach
cash-boundary demonstrations. P3.C imports no ND-MC module and introduces
no ND-MC-specific recurrence API.

*Acceptance:* a source→Lean declaration table for all three selected
theories, with every public declaration landed or explicitly excluded for
substrate/dead-code reasons; source-shaped 1D, genuine product-filter 2D,
and recurrence gates; then BfsQ O(n + ns) derived mechanically from its
exact vector/cash theorem and introsort O(n log n) from its exact source
upper-bound cash polynomial. No Θ consumer claim is made from an O-only
upper bound.

### P4 — Credits and amortization · COMPLETE 2026-08-01

P4 landed the four waves locked in `tower-expansion/p4-design.md`: A1 generic
amortization, A2 bounded dynamic array, B1 pure union-find, and B2 timed
loop-form union-find. It ports and validates the source credit calculus
before consumer adaptation: generic time-credit assertions and rules,
potential-carrying data-structure assertions, the pay-on-entry/spend-on-touch
discipline, and the scheduled dynamic-array and timed union-find developments.

The machine model remains frozen and allocation is rejected. A2 combines the
source-faithful generic/abstract amortization theorem with an explicitly
bounded executable adapter over caller-owned preallocated buffers; it must not
claim unbounded allocation.

> **Superseded 2026-08-02 (rev 5).** "Allocation is rejected" was a design
> decision, not a consequence of the frozen machine — see the three-way table
> in the fidelity charter. It is retired by P4.5. P4's landed results stand
> unchanged: the bounded caller-owned adapter remains correct and remains the
> right statement for a caller that supplies its own buffer. What changes is
> that it is no longer the *only* available statement, so the operations P4
> and P5 left at caller-owned boundaries can be given their source-strength
> unconditional forms. A2's "must not claim unbounded allocation" stays
> binding for the A2 adapter itself. B2 renders the source recursion as loops and
derives local vector costs. Routine direct ports use source review,
typechecking, kernel guards, and builds; focused compiled differential tests
are reserved for the authored vector-reclaim, bounded-array, and union-find
loop seams. P4 otherwise exports generic credit/data-structure machinery. The
arena bundle and touched-only reset theorem are P9 consumer instantiations and
may not shape P4's judgments or automation.

*Acceptance:* source→Lean declaration coverage for the selected SLTC and
amortization slices; the source-faithful abstract dynamic-array amortized-O(1)
result plus its explicitly bounded caller-owned executable adapter, with no
unbounded-allocation claim; and timed union-find green against the frozen
generic credit API.

### P4.5 — Ownership substrate: EO arrays and a costed allocator · budget 2–3 sessions

**New in rev 5, from F6/F7 and Jan's rule 5.** Port the container substrate
the pinned artifact actually uses for cost-carrying code, so that P5's
interfaces can be given their source-strength guarantees instead of
caller-owned approximations.

Source slice, all at `isabelle_llvm_time@42dd7f5`:

| file | size | carries cost | note |
|---|---|---|---|
| `thys/sepref/Hnr_Primitives_Experiment.thy` | 985 L | **yes** (`acost`, `lift_acost`) | the real target: `mop_oarray_new/extract/upd/free`, `eoarray_assn`, registered `sepref_fr_rules`. carries **no live `sorry`** — the `FREE_eoarray_assn` attempt at `:318–325` is inside a comment block (`:316–326`) whose author's note says the rule *does not hold* (ledger E23) |
| `thys/ds/Proto_EOArray.thy` | 186 L | no | earlier no-cost prototype; shape reference |
| `thys/sepref/IICF/Impl/Proto_IICF_EOArray.thy` | 298 L | no | the bridge from EO arrays back into IICF interfaces — the shape that satisfies Jan's "same interface, different internals" |

**A. Range ownership and the allocator.** Give arrays the source's ownership
granularity, then allocate on top of it.

Our carrier owns an array **name** all-or-nothing (`Tsa`, `Assn.lean:450`),
so no runtime-computed base pointer can designate an independently-ownable
region. The source owns an address **range** (`ll_range`), splittable index by
index. Unconditional `push` needs reallocation, reallocation needs unboundedly
many independently-ownable regions, and a static `Layout.arrays` means those
regions must be sub-ranges of one array. So range ownership is the phase's
content and the allocator is a short program on top of it.

Architecture (D-A1): one reserved array name carrying a second, per-index
view; `acells` sends that name to `Tsa.zero`, which is a soundness
requirement rather than hygiene. Additive by construction — the twelve landed
structures use non-heap names and do not change. **No new `Ir.Com`
constructor**: a heap access is `aget`/`aset` on the heap name at a computed
index, so the currency table, `embed`, `weight`/`cash`, `BigStepB`,
`bpre`/`bwp` and `embed_sim` are inherited and binding **D3 is discharged by
inheritance rather than extended**.

The allocator is then `p := hp; hp := hp + n` — two existing constructors,
cost two `irUnit`s, O(1) in `n`. Two properties it rests on:

- **`alloc n` is O(1), not O(n)** (ledger E24). Substrate, not optimisation:
  the source charges `n` to the **`malloc` currency** because a real LLVM
  `malloc` costs proportionally to the block it returns, while
  `Lax13/Ram.lean` has no `malloc` — `2 ^ w` zeroed cells already exist. The
  source has no fill loop either; `narrayo_new` never writes the contents,
  which is sound because `lo_init` makes an all-`None` EO array own no element
  memory for any concrete contents. This dissolves the O(n)-init × n-arenas →
  n² problem the campaign has been working around structure by structure.
  Zeroness is established at machine entry and consumed linearly (E27):
  no-reuse of *zeroed* space is a consequence of the split law rather than
  an enforced invariant, and reuse of *raw* space (E28) does not disturb
  the bound.
- **Exhaustion is a global side condition, and it already exists.**
  `Layout.FitsWords (B x) w` (`Compile.lean:85`), consumed only by
  `computesInTime_of_spec`, **is** "total allocation ≤ `2 ^ w`" stated once at
  program level; array lengths are already existential per input
  (`Cash.lean:385`). P4.5 adds **no second** exhaustion statement — a
  per-operation copy is precisely the rule-5 violation that produced the
  conditional append.

Deallocation is **landed, on two availability flavours** (ledger E23 as
amended, E27, E28): zeroed (`avail`) and raw (`availRaw`), zeroed entailing
raw and not conversely — the O(1) boundary sits at *knowing* a region reads
zero, not at never having touched it. `free` is one instruction, LIFO only;
use-after-free is underivable by linearity. The `MK_FREE` frame rule stays
unstated because the source declares it false. "Peak memory equals total
allocation" is repealed: only the **live set must fit, plus whatever LIFO
cannot reclaim**.

**Consumer space budget (E29) — the law the repeal does not lift.** The
global exhaustion condition `Layout.FitsWords (B x) w` quantifies over every
admissible word length, and the consumer headline's domain (ND-MC C0)
admits `2 ^ w` **linear in `|x|`** — the seam probe's
`no_word_size_for_sparse` mechanism. Address space on that path is
therefore strictly scarcer than time: the time budget is `n^{1+ε}`, but
live + LIFO-unreclaimable allocation must stay `O(|x|)`. Even touched-only
per-arena *fresh* allocation (Σ|X_c| ≈ n^{1+ε}) blows it. Three
consequences bind P4.5's remaining leaves, P5.E, and P9:

- Loop-interior structures (per-turn, per-arena) either reuse — raw
  allocation over LIFO-freed space, or caller-owned buffers — or must be
  shown live-set-bounded. Geometric-growth leaks under LIFO are
  live-set-bounded and tolerable; unfreed per-turn buffers are not.
- Zeroed availability out of reused memory costs O(n) and has no theorem
  (E28), so trail/touched-only reset remains the loop-interior discipline
  for structures needing clean state per arena. The allocator does not
  supersede the touched-only law; it complements it.
- **Registration discipline.** Which rule enters `sepref_fr_rules` as the
  synthesis default is a per-family decision recorded at re-seat time:
  allocating forms for setup-scale operations, reuse/in-place forms for
  loop-interior operations. Synthesis must not be able to silently pick an
  allocating form inside a loop and fail only at the bridge, sessions
  later.

Leaf sequence: **A.1** the heap view, **A.2** the allocator, **A.3**
deallocation — all landed 2026-08-02 (`7b9ed53`, `64a0498`, `65d7af1`;
ledger E25–E28); **B** and **C** below remain. Detail in
`p4.5-design.md` §4.

**B. Element-level ownership.** Port `mop_oarray_extract` / `mop_oarray_upd`
and `eoarray_assn`: slot-wise `Some`/`None` ownership, `extract` requiring
`xs!i ≠ None` and yielding `xs[i := None]`, `upd` the converse. This is what
makes move/swap costs exact and is the mechanism behind the source's
`myswap`.

**C. The IICF bridge.** Port `Proto_IICF_EOArray.thy`: EO arrays presented
through the IICF interfaces P5.A already landed. This is the join that lets a
consumer keep the battle-tested interface while the implementation changes
underneath.

*Acceptance:* `alloc` green with proved O(1) cost and verified codegen; the
ownership layer green; at least one P5.B structure re-seated (see P5.E) and
its previously conditional operation restated **unconditionally** under only
the global address-space side condition; the **compiled space-budget probe**
(E29): a driver-shaped skeleton — setup allocation, then turns × levels of
arena passes over LIFO-reused or caller-owned storage — fits the smallest
admissible word on a C0-shaped domain, with the negative control that the
same skeleton on per-turn fresh zeroed allocation provably does not (the
`no_word_size_for_sparse` shape aimed at the heap pointer); zero `sorry`;
gate law satisfied.

### P4.6 — orderCom whole-phase synthesis probe · budget ≤ 1 session

The retry Jan ordered on 2026-08-02 ("ahead of the ND-MC cost residue"),
slotted at the earliest point its dependencies allow (ledger E30): it needs
P1's signature machinery (landed) and P4.5's constructible structures —
nothing in P5.D, P5.E breadth, or P6 is load-bearing for a capped probe,
and every session spent there before the probe risks being on the branch
the probe kills. It runs right after P4.5's acceptance re-seat and before
P5.D/E breadth.

The "whole-phase synthesis over 15 arrays is intractable" verdict is stale
for checkable reasons: the recorded cause was hand-holed `sepref_synth`
goals (`Refine/OrderBridge.lean:36`, `Sepref/Definition.lean:24`), assigned
to and landed in P1; `transComb` stable-partitioning `hnr_seq` behind
`hnr_bind` killed the 2^depth retranslation blowup (>9 min → 49 s on one
real program — exactly what a whole phase would hit hardest); and P4.5
gives a closed IR program somewhere to get its structures from. Nobody has
retested since. At the measured exponent 1.28–1.35, a phase 8× BFS's op
count extrapolates to ~12–15 minutes: slow, and affordable once.

**Run it as a measured probe, not an open-ended attempt:** count
`orderCom`'s ops, full rule DB, wall-clock cap, record where the time goes
against BfsQ's 49 s. Outcome routing:

- **Lands, carrier-blind** — the criterion is P9's, checked here: the
  empty-arena charge is O(1), compiled. A synthesis that completes but
  reproduces `hKo`'s size-blind cost kills no floor and routes as a miss.
  On a landing, the order/cover phases are re-derived rather than repaired,
  most of the ND-MC cost residue stops existing, and the remaining
  P5.D/P6 content is re-reviewed against what the synthesis actually
  consumed before those phases run at breadth.
- **Misses the cap** — P7 gets its target profile from a real phase
  instead of P0's synthetic 3–5× program, and the ND-MC residue proceeds
  as planned. Worth having either way.

Also favoring the early slot: `hKo`'s size-blind `orderPhaseCost n ns W` is
the compiled interface floor's main driver
(`C0Probe.level_interface_floor`), and a synthesized order phase replaces
it with a derived cost instead of a hand-written constant.

*Practical constraint:* cannot run concurrently with an ND-MC wave — ND-MC
requires `Lax13Proofs`, so rebuilding the tower contends on the Lake lock
and invalidates the consumer build; that contention already cost one wasted
ND-MC baseline on 2026-08-02.

### P5 — IICF breadth · budget 2–3 sessions (A–C landed; D/E rescoped in rev 5)

The mandate's phase. Port the exact source IICF/collections surface assigned
by P0, honoring X5/E9 and every other recorded exclusion. Each structure:
abstract
interface, hnr rules in signature form (P1), credit specs, synthesized
implementations per the source's "by sepref" idiom.
*Acceptance:* uniform source-shaped rule-consumption gates per
implementation family with zero bespoke tactic work, followed—after the
P4/P5 APIs freeze—by one source-native Kruskal cross-structure validation.
Invented per-structure exercises do not become API requirements.

**Rev 5 rescope.**

- **P5.A — landed, not reopened.** The eight interface families are the
  battle-tested surface Jan's rule 5 protects, and review confirmed them
  exact against source (`Set` 11/11, `Map` 7/7, `List` 22/22, side
  conditions at source strength and source scope). P4.5 changes what sits
  *under* this layer, never the layer itself.
- **P5.B/P5.C — landed, to be re-seated by P5.E, not re-derived.** The
  abstract refinement layers and seven of nine `*ExecSpec_refines` seams are
  sound capital. What changes is the substrate beneath the executable layer.
- **P5.D — gated behind P4.5.** `List_Mset`, `List_MsetO`, `List_SetO`,
  `List_Set` and the iterator discipline land on the new substrate; they must
  not add further caller-owned boundaries.
- **`Impl_Heapmap` — gated behind P4.5** for the same reason, and behind the
  `ImplHeap` repair below.
- **P5.E (new) — re-seat the landed leaves.** Per structure, in dependency
  order: replace the caller-owned `*In`/ready-relation boundary with the
  P4.5 allocator, restate every operation the source states unconditionally
  at source strength, and delete the now-unnecessary ready relations. The
  first targets are `ArrayList` and `DArray_List` — the two landed class-1
  guarantee deviations (ledger E16) — and deleting `arrayListReadyRel` and
  `daReadyRel` while restating both pushes unconditionally is the acceptance
  test for P4.5. Re-seating is *statement strengthening plus substrate
  substitution*; the representation theory and the abstract refinement layer
  are reused, not rewritten. E29 qualifies the re-seat: deletion applies to
  the ready *relations*, not to the bounded caller-owned operation forms,
  which remain landed capital for loop-interior use; and each re-seat
  records its registration-default decision — allocating vs reuse form per
  operation — as E29 requires.

- **Hygiene, folded into P5.E (ledger E21).** Five global attribute
  mutations land unrestored: `attribute [irreducible]` on `marlPred`
  (`MSArrayList.lean:402`), `arlPred` (`ArrayList.lean:571`),
  `arlSelectCap` (`ArrayList.lean:643`), `ammZeroCount`
  (`ArrayMapMap.lean:306`), and the `sepref_fr_rules` erasure at
  `ImplHeap.lean:1113`. The first leaks into `IndexedArrayList.lean:952`
  and `ArrayOfArrayList.lean:619` and forces `simp` workarounds; the last
  cancels a registration that no file makes. `Intf/ListList.lean:74`+`:79`
  is the correct paired pattern to follow. Also
  `aalOuterSelectionSupported : Prop := False` with
  `aalOuterSelection_unsupported : ¬ … := by simp`
  (`ArrayOfArrayList.lean:866–869`) is presented as "a checked negative
  capability" but is `¬False` — it references neither the IR nor the
  structure, so it checks nothing. Delete it or replace it with a real
  statement about the substrate; after P4.5 the capability it denies may
  simply exist.
- **`ImplHeap` repair — CLOSED 2026-08-02 (ledger E20, E22).** The defect
  was that no theorem joined the exec specs to `implHeapSwim` /
  `implHeapPopMin?`. Six seam theorems now close it as **equations, not
  bounds**: the synthesized loops equal `AbsHeap`'s own `heapSwimFuel` /
  `heapSinkFuel` motions on the active prefix, leave the inactive suffix
  untouched, terminate, and cost exactly the (corrected) closed forms.
  **Supervisor correction:** the review's "vacuous invariant" finding was
  wrong. `irWhileIT_of_not_inv` (`Sepref/IrOps.lean:234`) makes a failed
  invariant equal `NRest.fail`, the top of the order, so strengthening an
  `irWhileIT` invariant enlarges the spec and *weakens* every `hnRefine`
  rule beneath it. `True` was the strongest available choice; the real
  invariants belong as seam hypotheses, which is where they now are. The
  repair also found `implHeapSwimCost`/`implHeapSinkCost` were **wrong** —
  both omitted the `ir.skip` units the loop bodies pay — a direct instance
  of F11: the cost function nobody consumed was the cost function nobody
  checked. Forward-compatible with P5.E: the insert precondition is
  isolated as `implHeapInsertPre`, so no seam statement mentions
  `arrayListReadyRel` and P5.E discharges one hypothesis rather than
  restating theorems.
- **Dead fidelity checks — close or delete (F11).** Prove
  `implHeapSwimCom ≡ implHeapSwimSourceCom` and relate each `*SourceBound`
  constant to the corresponding `*Cost`, or delete them and move the shape
  into prose. A recorded source bound that no theorem compares against ours
  is decoration, and under rule 5 the comparison is the point.
- **`fillCost n` general theorem — P6, blocking the cost story (F11).**
  With P4.5's O(1) `alloc`, several of its consumers may disappear
  entirely; the remainder still need a symbolic-`n` theorem.

### P6 — Debt closure: thaw queue and open items · budget 1–2 sessions

Close the disclosed debt instead of carrying it: `inres` (open since
P2-tower), `sepref_copy_rules` (empty), `mop_move` with a live
destination (the operator-phase dodge killer), symmetric rule-side
`prodAssn` splitting in `frameMatch` (the p8-verdict thaw queue's named
items), convention-pair dedupes (P6-A/P6-B), the six bonus Autoref DBs,
abstract-twin equalities promoted from `#guard` to proof, `RECT`
fuel-stability, and the generic `RECT`/gfp order-isomorphism transport needed
to land the source's omitted `flatCurrs_whileT`. Consumer-local loop repairs
are not part of this phase.
*Acceptance:* the p8-verdict thaw queue and open-items list both empty —
each entry closed or re-ledgered with an explicit reason.

### P7 — Frame-layer performance · budget 1–2 sessions

(The orderCom synthesis retry formerly slotted at this boundary is now
phase **P4.6**; if it missed its cap, its telemetry is P7's primary profile
input in place of P0's synthetic program.)

The measured scaling wall: synthesis exponent 1.28–1.35 in op count and
`fri` alone 28% of a 100-op synthesis. Attack the frame/entailment layer with
the source's own disciplines first (Termtab-style first-order pre-match
served once already — `absAgree`), then profile-driven: entailment-rule
indexing, residue caching, round-loop early exit.
*Acceptance:* freeze a source-neutral `FrameScale3to5` fixture before the
optimization work; its 3×–5× cases are the primary benchmark and must run in
≤ 60 s with `fri` share ≤ 15%. The historical ND-MC/BFS probe is secondary,
read-only, and non-gating. A primary-fixture miss lands as a verdict note,
not consumer-specific tactic work.

### P8 — Executable gates (ours; ledger E4) · budget 1 session

Not a port — the D4-class addition the retro demands: turn the standing
laws from supervisor prose into commands. `#slot_sweep` — given a root
theorem, check every hypothesis has a registered producer whose
conclusion matches, and print the unproducible residue. `#cost_probe` —
the compiled-costs-both-directions harness (floor probe + closed-form
witness) as one invocation. Brief-gate emitter — the worker-brief
falsification section generated from the obligation, not hand-written.
*Acceptance:* frozen generic fixtures mechanically expose (i) an
unproducible hypothesis and (ii) a cost-floor mismatch. The archived B7
case is secondary read-only regression evidence when replayable; P8 neither
reconstructs nor modifies ND-MC state.

### P9 — Consumer gate: the ND-MC order phase · budget 2–3 sessions

The sole consumer-integration phase. The ordering phase is synthesized from an
`hfref` signature (P1) — the 21-pass, 15-array phase that today exists
only as hand-written `orderCom` — iterating member lists (P2), budgeted
in currencies (P3), and instantiating P4's generic credits with the local
arena bundle and touched-only reset theorem. These two local constructions
land here, after the generic credit API is frozen. The name-generating
recursion (`botCom`, per-depth assembly)
remains hand-written capital per the pinned tower/hand boundary; only the
phase bodies move.
*Acceptance (gate):* synthesized phase lands with zero hand frame
clauses; its cost text is **carrier-blind** — the empty-arena charge is
O(1), compiled, killing the premise of the no-escape floor; the five
`g2_plug` gap hypotheses (`hKo_gap`…`hbnd_gap`) acquire honest producers
from the synthesized cost text. Gaps that do not prove a mistranslated or
omitted scheduled source declaration are handed to the ND-MC campaign and
do not widen P1–P8.

### P10 — Wrap · budget 1 session

Deviation-ledger and declaration-coverage review; explicit disposition of
the quarantined P10 backlog; verdict and handoff notes; README/index and
memory updates.

**Total budget: 17–29 sessions** (P4.6 adds ≤ 1). The tower campaign beat the same-shaped
budget 5×; set expectations by the budget, not the precedent — P1 and P9
carry genuine design risk (signature machinery meets Lean's weaker HOU;
the seam is the largest synthesis attempted).

## Deviation ledger (inherited + seeded; P0 completes)

D1–D5, N1–N3 of the tower campaign are inherited unchanged and remain
binding. New seeds:

| id | source design | our position | reason class |
|---|---|---|---|
| E1 | sources organize collections by their own package layout | ported into the existing `Refine/` subtree under its conventions | substrate/layout; judgment shapes untouched |
| E2 | IHT `Asymptotics_1D/2D/Recurrences`; AFP/CFML are semantic references | faithful IHT declaration-family port over mathlib `Asymptotics`, then cash-boundary examples | substrate rendering; concrete vectors remain primary |
| E3 | (no analogue) | arena bundle as a P9 consumer instantiation, not P4 infrastructure | local addition; generic credit calculus untouched |
| E4 | (no analogue) | executable gates: `#slot_sweep`, `#cost_probe`, brief emitters | addition, not deviation — D4's rationale (agent workforce needs refutation tooling) |

## Not in scope

- **ND-MC work before P9**, including C0, B7, its P5, `CostRecurrence`
  packaging, bridge probes, and provisional drafts. P9 hands off; it does
  not discharge the ND-MC campaign.
- **Code export to real hardware; literal LLVM** — unchanged from the
  tower plan.
- **Concept surfaces, the machine model, `lake update`.**
- **Surface syntax** (a `do`-macro front end) — still a separate short
  task; the combinator style remains the deliverable.
- Any source slice not assigned to P1–P10 by P0. P10 may reconsider the
  quarantined inventory; live phases may not.

## Watch items

Inherited: elaboration time as acceptance criterion; weak HOU (P1 is the
phase most exposed — the signature machinery is algorithmic in the
source, which is the mitigation; fighting `isDefEq` is a design smell to
raise, not grind through); DTT/universe friction; namespace/splitter
discipline; supervision legibility (every synthesis failure names its
phase and unmet side condition).

New: **consumer coupling.** P1–P8 do not edit or import ND-MC. P9 consumes
only frozen tower APIs. A consumer failure becomes tower work only when it
proves a scheduled source declaration was mistranslated or omitted.

## JAN-FLAGs (all resolved 2026-07-31 — Jan delegated resolution to the supervisor at acceptance)

1. **Sequencing vs C0 — RESOLVED: source infrastructure first.** No ND-MC
   action runs inside P1–P8. Bridge probes, provisional drafts, and other
   ND-MC work remain solely in that campaign after P9's handoff.
2. **P9 placement — RESOLVED: here**, as this campaign's consumer gate
   (the tower campaign's P7 precedent). The ND-MC plan keeps ownership
   of B7/C0/P5 on the handoff.
3. **P5 breadth list — RESOLVED by P0.** The exact P5 table is fixed,
   including X5/E9's exclusion of deterministic hash implementations;
   live phases may not revive excluded or stretch rows.
4. **Governance — RESOLVED by Jan directly at acceptance**: full
   autonomy carries over. The flag mechanism is retired for this
   campaign; the fidelity charter, the deviation ledger, and the D-flag
   discipline remain unchanged as the evaluable record serving Jan's
   final evaluation.

## Progress log

- **2026-08-02 — Rev 6 (Fable review session): P4.5.A recorded, probe
  re-slotted, space-budget law, mechanized gates, plan superseded in
  place.** Landed after the session-close entry below and recorded here:
  **P4.5.A.1–A.3 are green** — range ownership (`7b9ed53`), the costed
  O(1) allocator (`64a0498`), deallocation on two availability flavours
  (`65d7af1`; E23 amended by `b39293c`) — with ledger E25–E28 the full
  record; on the consumer side, the ND-MC compile gate (`dcdca31`) and the
  ND-MC word-bound repair W1–W3 landed. Rev 6 changes, from an external
  review of the plan (ledger E29–E31): (1) the **consumer space-budget
  law** (E29) — address space is scarcer than time on the C0 path; live +
  LIFO-unreclaimable allocation must fit a word linear in `|x|`;
  registration discipline for allocating vs reuse forms; a compiled
  space-budget probe added to P4.5's acceptance. (2) The orderCom synthesis
  retry is re-slotted from the P7 boundary to new **P4.6**, immediately
  after P4.5 (E30) — its dependencies are P1 and P4.5 only, and its outcome
  reprioritizes P5.D/P6 and the ND-MC residue; "lands" now requires
  carrier-blind, compiled. (3) Governance (E31): Opus supervises day to day
  (Jan's cost decision), Fable reviews at phase boundaries and owns
  clause-2 acceptance; the closure rule — closures name their compiled
  artifact; the gate law is mechanized as `.claude/leaf-gate.sh`. (4) The
  plan's revision archaeology is folded into ledger E31 per the
  supersede-in-place rule. The ND-MC plan gains the `g2_exists`
  re-validation gate ahead of its residue. `.claude/leaf-gate.sh` landed
  and was validated end-to-end the same session (concepts 505, proofs
  3,277, lax audit, consumer build 3,549 jobs): its FAIL verdict is
  exactly the two known pre-existing `GetElem?.match_1.splitter`
  violations — the gate is strict on purpose, so clearing those two small
  repairs is the first chore of the next session. **Next: the two
  splitter repairs, then P4.5.B.**

- **2026-08-02 — Session close: campaign is READY TO RESUME AT P4.5.A.**
  State a next session can rely on without re-deriving it:
  *Green* — `lake build` 3,275 jobs; `lax build --only proofs word-ram` 2
  violations, both the single pre-existing `GetElem?.match_1.splitter`,
  located to `ArrayOfArrayList.lean:141` and `ArrayMapMap.lean:145` (a
  `split at h` over a `getElem?` match); zero `sorry`/`admit`/`native_decide`
  in the package; working tree clean.
  *Landed this session* — all twelve P5.B/C leaves root-imported (`834b637`);
  rev 5 substrate correction with P4.5, rule 5, and the gate law (`1ccaa53`);
  `ImplHeap`'s executable-to-abstract seam closed with six equations
  (`eb07d99`); rev 2's ND-MC traceability table restored (`55a737b`); the
  falsification law re-scoped by provenance per declaration (`8419dd1`);
  ledger backfilled E16–E22.
  *Decisions closed* — Jan confirmed the 2026-07-31 falsification waiver was
  his and delegated the forward call; `larray` resolved as argued exclusion
  X17; the ND-MC delay caused by inserting P4.5 is accepted by Jan.
  *Open, carried forward* — the two `GetElem?` namespace violations (small,
  local: replace the `split at h` with a route that generates no foreign
  splitter); `fillCost`'s missing symbolic-`n` theorem, which is Claude-era
  debt from `521d8d3`, not P5's — **check first whether P4.5's O(1)
  allocator deletes its consumers outright before anyone invests in proving
  it**; five unrestored attribute mutations and the circular
  `aalOuterSelection_unsupported`, both folded into P5.E (E21); seven helper
  lemmas sitting in `ImplHeap.lean` that belong in `AbsHeap.lean` /
  `ArrayList.lean` / `Intf/List.lean`.
  **Next: P4.5.A — the costed allocator.** Port `mop_oarray_new` from
  `Hnr_Primitives_Experiment.thy` as an IR operation over a bump allocator;
  prove the O(1) result and the no-reuse invariant with compiled negative
  controls (clause 2 — it is authored, so no exemption); carry D3 codegen
  coverage before anything depends on it. Sequentially, on warm `main`.

- **2026-08-02 — REV 5: P5 paused mid-phase; substrate correction ordered.**
  A mid-phase review of the landed P5 output produced six findings (F6–F11
  above). The load-bearing one is F6: the artifact's IICF is not merely out
  of its build closure, it is *superseded* by an explicit-ownership container
  layer (`Hnr_Primitives_Experiment.thy`) that the only built target actually
  uses — and P0 had already named that file in F1 without acting on it. F7
  then found that E7's premise was false outright: no pinned source has a
  cost-carrying IICF, so P5's entire currency layer is authored rather than
  adapted. Jan's decision the same day set a guarantee-fidelity law (rule 5)
  ranking interface guarantees above representation, retired the P4-era
  "allocation is rejected" decision, and ordered the port onto the successor
  stack. New phase P4.5 ports a costed bump allocator — expressible in the
  existing IR with **no endorsed-machine change**, and O(1) rather than the
  source's O(n) because `Lax13/Ram.lean` starts memory zeroed — plus
  element-level ownership and the IICF bridge. P5.A is explicitly not
  reopened; P5.B/C are re-seated by the new P5.E, not re-derived.
  Also landed this session: all twelve P5.B/C leaves root-imported
  (`834b637`, 3,275 jobs green, no aggregate conflicts), which exposed F9 —
  the archive gate had been unobservable to the per-leaf `lake build` since
  the first unrooted leaf, and two real `[namespace]` violations with it. A
  gate law now requires root-wiring, `lax build`, and a ledger entry on the
  day a leaf lands. **Next: P4.5.A costed allocator; `ImplHeap` seam repair
  and ledger backfill in flight.**

- **2026-08-02 — P5.C Abs_Heapmap green (4/5 families; 3/4 heap
  families).** New unrooted `Iicf/Impl/AbsHeapmap.lean` ports the source pair
  of a distinct one-based key heap and partial key/value map, its exact domain
  and priority-view invariants, indexed key/value/priority primitives, and
  permutation/commutation theory for swim, sink, and repair. Insert, set,
  arbitrary change, decrease/increase, arbitrary remove, peek, and pop preserve
  the representation and have exact abstract-map semantics. All twelve map and
  priority-map frefs are registered. This semantic layer intentionally exposes
  no IR rules or vector costs. Supervisor replay: 2,991 jobs; source/fref,
  kernel-three, and zero-placeholder gates pass. **Next: P5.C Impl_Heapmap.**

- **2026-08-02 — P5.C Impl_Heap green (3/5 families; 2/4 heap families).**
  New unrooted `Iicf/Impl/ImplHeap.lean` composes the caller-owned `ArrayList`
  representation through `AbsHeap`, specializes the executable source to
  natural elements and identity priority, and ports the exact one-based
  update/value/exchange/valid/prio seams. Swim and optimized tie-left sink are
  explicit IR loops with operational `irWhileIT` specifications and registered
  `hnRefine` proofs; public insert composes bounded append with swim, while pop
  composes root read, exchange, logical shrink, sink, and result pairing with
  path-sensitive vector costs. Empty allocation remains intentionally semantic
  and unsupported; insert requires the caller-owned ready relation. Provenance
  records both the generic Sepreftime pin and its executable
  `isabelle_llvm_time` specialization. Supervisor replay: 2,995 jobs; source,
  fref/executable registration, branch-cost, kernel-three, and zero-placeholder
  gates pass. **Next: P5.C Abs_Heapmap.**

- **2026-08-01 — P5.C Abs_Heap green (2/5 families; 1/4 heap families).**
  New unrooted `Iicf/Impl/AbsHeap.lean` ports the pure one-based list heap:
  navigation, invariant and root-minimum theory, update/exchange/append/
  butlast primitives, and the actual source-shaped swim, optimized sink,
  repair, insert, peek, and pop algorithms. Review rejected an interim
  insertion-sort normalization and restored the recursive heap motions; a
  second correction restored the source `change_key` seam by proving repair
  after an arbitrary valid cell update, with explicit decreased- and
  increased-priority cases. The five multiset/prio-bag frefs are semantic and
  intentionally expose no executable rules or vector costs at this abstract
  layer. Supervisor replay: 2,988 jobs; motion regressions, source/fref
  registration, kernel-three, and zero-placeholder gates pass. **Next: P5.C
  Impl_Heap.**

- **2026-08-01 — P5.C Array_Matrix green (1/5 families).** New unrooted
  `Iicf/Impl/ArrayMatrix.lean` ports the general `N × M` row-major relation,
  bounded-support and zero-preservation theory, semantic tabulation/new, and
  rectangular plus source-specialized square get/set refinements. Executable
  caller-owned default fill and get/set are synthesized; get/set compute the
  physical index with actual `mul` and `add` before `aget`/`aset`, with exact
  vector costs. Allocation and the source's higher-order heap callback remain
  explicit unsupported boundaries, while the generic semantic new rule keeps
  the source's pure zero-unique relation. Supervisor replay: 2,988 jobs;
  relation/index, registration, command/currency, kernel-three, and zero-
  placeholder gates pass. **Next: P5.C Abs_Heap.**

- **2026-08-01 — P5.B complete: ArrayMap_Map green (8/8 implementation
  families; 3/3 map families).** New unrooted
  `Iicf/Impl/ArrayMapMap.lean` ports Sepreftime's cardinality-carrying map on
  the honest two-array option encoding plus an owned scalar equal to the
  exact finite domain cardinality. Empty, membership, present-key lookup, and
  update retain their source contracts; fresh insertion alone increments the
  scalar, and the synthesized update cost differs from overwrite by exactly
  one `add`. SepLogicTime scalar costs remain provenance rather than false
  `ECost` equalities; allocation/free remain unsupported. Supervisor replay:
  2,988 jobs; relation/cardinality, registration, branch/currency,
  kernel-three, and zero-placeholder gates pass. **Next: P5.C.**

- **2026-08-01 — P5.B Array_Map_Total green (7/8 implementation families;
  2/3 map families).** New unrooted `Iicf/Impl/ArrayMapTotal.lean` preserves
  the source's deliberately partial dense-map relation: the one backing array
  has length `N`, present abstract entries constrain their cells, and absent
  entries remain arbitrary garbage. Custom empty, present-key lookup, and
  update retain the fixed-key bound and double relation composition. Their
  caller-owned commands have exact fill/aget/aset vector costs and whole-state
  bridges; allocation/free/export remain unsupported. Supervisor replay:
  2,987 jobs; registration, command/currency, kernel-three, and zero-
  placeholder gates pass. **Next: P5.B ArrayMap_Map.**

- **2026-08-01 — P5.B Array_Map green (6/8 implementation families; 1/3
  map families).** New unrooted `Iicf/Impl/ArrayMap.lean` replaces the
  source's allocated array of options with two caller-owned fixed arrays: a
  proved-canonical 0/1 presence array and an unrestricted value array, so no
  natural sentinel is reserved. Generic empty/update/delete/lookup/contains
  rules refine the map interface; caller-owned empty and all four point
  operations have synthesized exact vector-cost commands and whole-state
  bridges. Allocation/free/export remain explicit unsupported boundaries.
  Supervisor replay: 2,987 jobs; relation, registration, command/currency,
  kernel-three, and zero-placeholder gates pass. **Next: P5.B
  Array_Map_Total.**

- **2026-08-01 — P5.B Array_of_Array_List green (5/8 implementation
  families; 5/5 sequence families).** New unrooted
  `Iicf/Impl/ArrayOfArrayList.lean` ports the generic nested-list relation,
  empty/push/pop/index/update/length/take semantic rules, and exact executable
  rules once a caller has supplied the selected row's owned buffer and scalar
  metadata. The IR cannot allocate/free or store and dynamically select an
  outer array of row pointers, so those source operations are explicitly
  excluded rather than represented by placeholder costs. Strict spare-cell
  push bounds, registration, command/currency, kernel-three, and zero-
  placeholder gates pass. Supervisor replay: 2,993 jobs. **Next: P5.B
  Array_Map.**

- **2026-08-01 — P5.B Indexed_Array_List green (4/8 implementation
  families).** New unrooted `Iicf/Impl/IndexedArrayList.lean` couples a fixed
  logical array list with a sentinel-valued inverse-position array and proves
  the distinctness/bounds/index invariant through swap, append, and butlast.
  All seven source operations have synthesized exact-cost commands, including
  branch-sensitive contains. Generic rules are registered through `ialRel N A`;
  append genuinely consumes the source below-identity condition, while
  index/contains retain the needed two-way uniqueness assumptions. Empty stays
  a two-buffer caller-owned boundary. Supervisor replay: 2,992 jobs; invariant,
  generic-registration, command/currency, kernel-three, and zero-placeholder
  gates pass. **Next: P5.B Array_of_Array_List.**

- **2026-08-01 — P5.B MS_Array_List green (3/8 implementation families).**
  New unrooted `Iicf/Impl/MSArrayList.lean` pins the source's fixed maximum
  `N` to both owned buffer length and runtime capacity. Caller-owned empty-size
  remains nonallocating. All seven executable operations have synthesized or
  semantically identical reused commands with exact vector costs; append has
  only set/increment and butlast only decrements length. The custom-empty folds
  and both source synthesis examples are retained at the honest caller-owned
  boundary. Supervisor replay: 2,991 jobs; relation/precision, registration,
  command/currency, kernel-three, and zero-placeholder gates pass. **Next:
  P5.B Indexed_Array_List.**

- **2026-08-01 — P5.B DArray_List green (2/8 implementation families).** New
  unrooted `Iicf/Impl/DArrayList.lean` ports the source's narrow dynamic-array
  list surface: composed pure-element assertion, actual `dyn_da` identity cast,
  combined assertion and empty fact, plus empty/push rules. Empty remains a
  pure caller-owned boundary because the IR has no allocator. Push reuses P4's
  fallible dispatcher and exact branch-sensitive vector cost; source scalar
  bounds 12/23 are provenance-only and are not fabricated as `ECost`s.
  Supervisor replay: 2,987 jobs; relation, registration, branch/currency,
  kernel-three, and zero-placeholder gates pass. **Next: P5.B MS_Array_List.**

- **2026-08-01 — P5.B Array_List green (1/8 implementation families).** New
  unrooted `Iicf/Impl/ArrayList.lean` adapts the source representation to P4's
  caller-owned `BoundedArray`. Append reuses P4's honest bounded/fallible
  growth rule; length, is-empty, last, butlast, get, set, and swap have
  synthesized command rules with exact `ECost` vectors. Butlast performs the
  source's conditional logical-capacity shrink without reallocating the
  physical buffer. Fresh empty, sized empty, and copy remain pure boundaries
  because the substrate has no allocator. Supervisor replay: 2,990 jobs;
  registration, command-shape, currency, kernel-three, and zero-placeholder
  gates pass. **Next: P5.B DArray_List.**

- **2026-08-01 — P5.A COMPLETE.** The root now explicitly imports all eight
  interface families: Set, Map, List, List_List, Matrix, Multiset, Prio_Bag,
  and Prio_Map. The aggregate gate preserves every leaf's registration and
  kernel checks. Final supervisor gates: concepts 505 jobs, rooted proofs
  3,263 jobs, and `lax build --only proofs word-ram` archive/import audit green;
  zero placeholders. **Next: P5.B concrete bounded sequence/map families.**

- **2026-08-01 — P5.A Prio_Map interface green (8/8 leaves).** New unrooted
  `Iicf/Intf/PrioMap.lean` ports the conversion helpers and all seven priority-
  map operations with their exact presence, monotonicity, nonempty, key-
  uniqueness, and below-identity requirements. Peek/pop preserve global-minimum
  witnesses; pop returns the exact related delete remainder. Proper-below-id,
  diagonal, registration, and kernel gates pass. Supervisor replay: 2,987 jobs;
  kernel-three and zero placeholders. **Next: root-wire all eight P5.A leaves
  and run the package/archive boundary.**

- **2026-08-01 — P5.A Prio_Bag interface green (7/8).** New unrooted leaf
  `Iicf/Intf/PrioBag.lean` ports the general cross-relation priority proofs and
  both zero-cost nondeterministic minimum operations. Registrations retain the
  source's below-identity restriction without weakening their outer function
  precondition; empty inputs fail through the internal assertion. Pop returns
  an exact related erase remainder. All generic, diagonal, registration, and
  kernel gates pass. Supervisor replay: 2,985 jobs; kernel-three and zero
  placeholders. **Next: P5.A Prio_Map.**

- **2026-08-01 — P5.A Multiset interface green (6/8).** New unrooted leaf
  `Iicf/Intf/Multiset.lean` ports the full multiset-relational algebra and all
  nine cost-silent operations. Bi-unique requirements are retained for
  deletion, subtraction, membership, and count; nonempty pick returns a
  related element/remainder decomposition under a zero-cost specification.
  All registrations, source pattern/custom-empty dispositions, and kernel
  guards pass. Supervisor replay: 2,984 jobs; kernel-three and zero
  placeholders. **Next: P5.A Prio_Bag.**

- **2026-08-01 — P5.A Matrix interface/theory green (5/8).** New unrooted
  `Iicf/Intf/Matrix.lean` ports the matrix relator and five operations together
  with the source file's full portable pointwise theory: row-major div/mod
  conversions, unary/binary fold refinements, nonzero support, and the finite
  interruptible comparison refinement. Isabelle-only heap code-generation
  locales have explicit dispositions; no fake concrete API is emitted. All
  operation registrations and kernel guards pass. Supervisor replay: 2,985
  jobs; kernel-three and zero placeholders. **Next: P5.A Multiset.**

- **2026-08-01 — P5.A List_List interface green (4/8).** New unrooted leaf
  `Iicf/Intf/ListList.lean` ports all eight nested-list operations and six
  semantic fold equalities with exact bounds and product shapes. A nominal
  `ListListI` is limited to repairing the interface normalizer's inability to
  expand nested `ListI`; semantics remain `List (List α)`. All registrations,
  diagonal frefs, custom-empty disposition, and kernel guards pass. Supervisor
  replay: 2,985 jobs; kernel-three and zero placeholders. **Next: P5.A Matrix.**

- **2026-08-01 — P5.A List interface green (3/8).** New unrooted leaf
  `Iicf/Intf/List.lean` ports the list-relational support and all twenty-two
  cost-silent operations with the source's bound, nonempty, and tuple-shaped
  preconditions. The index/contains single-valued requirements and semantic
  get/set swap expansion are preserved. All registrations, diagonal frefs,
  source automation dispositions, and kernel guards pass. Supervisor replay:
  2,984 jobs; kernel-three and zero placeholders. **Next: P5.A List_List.**

- **2026-08-01 — P5.A Map interface green (2/8).** New unrooted leaf
  `Iicf/Intf/Map.lean` ports the key-supported bidirectional `mapRel`, nominal
  `MapI`, and all seven cost-silent operations. Update/delete retain both key
  single-valued requirements; checked lookup retains its nonempty paired-input
  precondition and zero-cost unique specification. All registrations, diagonal
  frefs, pattern/locale dispositions, and kernel guards pass. Supervisor replay:
  2,984 jobs; kernel-three and zero placeholders. **Next: P5.A List interface.**

- **2026-08-01 — P5.A Set interface green (1/8).** New unrooted leaf
  `Iicf/Intf/Set.lean` defines the source's bidirectional `setRel`, nominal
  `SetI`, relation inference, and all eleven cost-silent operations, including
  nonempty nondeterministic pick. Required single-valued/converse conditions
  are preserved, all registrations and diagonal frefs are gated, and the
  Isabelle-only pattern/locale mechanisms have explicit Lean dispositions.
  Supervisor replay: 2,983 jobs; kernel-three and zero placeholders. **Next:
  P5.A Map interface.**

- **2026-08-01 — P4 COMPLETE.** Root-imported `Iicf/UnionFindTime.lean`
  packages initialization, bounds-checked comparison with path compression,
  and union-by-size into a timed implementation certificate. Exact `ECost`
  vectors are bounded pointwise by `heightUb`, whose Theta(log n) certificate
  is carried explicitly; no inverse-Ackermann claim is made. Both union
  orientations, comparison outcomes, compression shapes, and no-op branches
  are gated, and all public boundaries stay within kernel-three. The archive
  import audit caught and repaired one direct Batteries import by routing it
  through mathlib. Final gates: focused leaf 3,000 jobs, concepts 505, proofs
  and proofs-only lax 3,255; zero placeholders. **Next: P5 IICF breadth.**

- **2026-08-01 — P4.B2 union-by-size boundary green.** The timed leaf now
  performs two measured finds and links the smaller representative below the
  larger, updating the winning size. Both orientations preserve `rankInvar`
  and `UfArrays.Wf`; the abstract result is exactly `perUnion`. Equal roots are
  a non-mutating no-op, while index validity remains the source precondition.
  Exact branch costs, `heightUb` phase bounds, orientation/no-op gates, and the
  public `hnr_ufUnion` kernel guard pass. Supervisor replay: 2,998 jobs; zero
  placeholders. **Next: final B2 interface interpretation and root wiring.**

- **2026-08-01 — P4.B2 comparison boundary green.** Bounds-checked same-set
  comparison now composes two find/compress phases, preserves the abstract
  relation and both arrays' invariants, and compares the representatives. Its
  exact vector cost is branch-sensitive: invalid inputs return false without
  mutation, while valid inputs expose the sum of both measured phases and the
  final equality test. The phase heights and rewrite counts are bounded by
  `heightUb`. True/false forest gates and the public `hnr_ufCompare` kernel
  guard pass. Supervisor replay: 2,998 jobs; zero placeholders. **Next:
  union-by-size and its two rank-preservation branches.**

- **2026-08-01 — P4.B2 path-compression boundary green.** The unrooted timed
  union-find leaf now follows the found path and rewrites every visited parent
  to the representative. The measured loop preserves `ufaAlpha`, `ufaInvar`,
  `rankInvar`, and the size array; its exact vector cost uses the number of
  executed rewrites, proved at most the starting height. `hnr_ufCompress`
  composes with the representative left by find. Compressed and two-edge-chain
  gates pin the resulting arrays and distinct costs. Supervisor replay: 2,998
  jobs; kernel-three and zero placeholders. **Next: comparison.**

- **2026-08-01 — P4.B2 height-sensitive find boundary green.** The unrooted
  `Iicf/UnionFindTime.lean` leaf now implements root search as a manually
  composed measured loop. Its exact vector cost is indexed by `heightOf`, its
  public HNR rule preserves `ufAssn` and returns `repOf`, and singleton,
  compressed, and two-edge-chain gates distinguish the expected costs. A
  preliminary length-bounded Theta(n) loop was rejected rather than landed.
  Focused Lake replay: 2,998 jobs; kernel-three and zero placeholders. **Next:
  path compression in the same leaf.**

- **2026-08-01 — P4.B2 initialization boundary green.** New leaf
  `Iicf/UnionFindTime.lean` lands the timed MOP/assertion surface, an exact-cost
  parent-range loop, and two-array initialization from caller-owned buffers.
  The result is proved to satisfy both `ufaInvar` and `rankInvar`; its synthesized
  vector costs and kernel-three guards are green. Focused Lake build: 2,997
  jobs; zero placeholders. The leaf remains deliberately unrooted while B2 is
  open. **Next: bounded root-search and path-compression loops.**

- **2026-08-01 — P4.A2 COMPLETE.** New root-imported leaf
  `Iicf/IicfDynamicArray.lean` proves functional snoc, the standard and nested
  vector-potential inequalities, and the A1 reclaim/consume amortized push.
  Its caller-owned adapter exposes physical buffer length, logical length, and
  logical capacity; pushes either write in place, grow only inside already-owned
  storage, or fails cleanly when full. Exact loop-free success and non-mutating
  failure programs synthesize with an explicit physical-capacity operand.
  Whole-tree synthesis timed out in `isDefEq`; manual `hnr_If`/`hnr_bind`
  composition closes the dispatcher without tower changes. Three evaluator
  gates pin functional output and complete IR cost vectors, including unchanged
  state on failure. Kernel-three guard green; full proofs 3,251 jobs and
  proofs-only lax green; zero placeholders. **Next: P4.B2 timed loop-form
  union-find.**

- **2026-08-01 — P4.B1 COMPLETE.** The accepted operations boundary now
  extends through the pinned height/rank/logarithmic source slice.
  `Iicf/UnionFindAbstract.lean` proves bounded-fuel height equations under
  `ufaInvar`, compression and union height effects, the source rank invariant,
  `2^height ≤ length`, and the ceiling-log upper bound with its Θ(log n)
  wrapper. Small singleton/chain/compression probes and kernel-three guards are
  green. Supervisor replay: focused leaf 1,992 jobs, full proofs 3,250 jobs,
  and proofs-only lax green; zero placeholders. **Next: P4.A2 bounded dynamic
  array, sequentially on warm main.**

- **2026-07-31 — P4.A1 COMPLETE; P4.B1 operations boundary accepted.**
  `Sepref/Amortization.lean` lands the complete generic vector-amortization
  slice: 17 public declarations, a 12-row source table, and 11 kernel-three
  guards. Its genuinely authored two-currency seam is checked through a proved
  correspondence with the actual `NRest.reclaim`, covering exact residual,
  insufficient potential, currency isolation, and top subtraction. The direct
  source-shaped remainder needs no ceremonial falsification suite.
  `Iicf/UnionFindAbstract.lean` has a green first boundary through the AFP PER
  family, finite-fuel representative equations, abstraction, init/find/union,
  and compression correctness; six small probes cover singleton, chains,
  compression, and both union directions. Height/rank/logarithmic rows remain
  explicitly open for the B1 successor. Independent audit caught and repaired
  a weakened `per_supset_rel`, two missing AFP helpers, disconnected A1 tests,
  and incomplete B1 probes before acceptance. Supervisor replay: A1 2,960
  jobs, B1 1,992, concepts 505, full proofs 3,250, and
  `lax build --only proofs word-ram` green; zero placeholders and no new target
  warnings. **Next: finish B1 height/rank theory; A2 briefing may proceed from
  the frozen A1 API.**

- **2026-07-31 — P3.C COMPLETE; asymptotic source families and consumer
  gates green.** `Examples/AsymptoticConsumers.lean` closes the phase with
  exactly two O-only consumers. The seven-coordinate BfsQ account projects
  exactly to `22*n + 15*ns + 13` and is O(n + ns) over the genuine product
  filter. The exact introsort upper-bound cash polynomial is O(n log n); no
  unsupported Theta or lower-bound claim and no ND-MC dependency was added.
  The final A–E source audit covers 131 rows: 126 live declarations and five
  documented exclusions, with no omissions, duplicates, or
  misclassifications. The consumer leaf carries two kernel-three guards.
  Supervisor replay: focused consumer module 3,190 jobs, concepts 505, full
  proofs 3,244, and `lax build --only proofs word-ram` green; zero
  `sorry`/`admit`/`native_decide` and no new warnings. **Next: P4, generic
  credits and amortization.**

- **2026-07-31 — P3.C-E COMPLETE; recurrence families and source-facing P3.C
  green.** `Asymptotics/Recurrences.lean` maps all 18 scheduled rows from
  `Asymptotics_Recurrences.thy`: 12 generic declarations and six source
  validation-example rows. The four O/Ω successor-recurrence theorems, three Θ
  wrappers, logarithmic helper, and three genuine-product-filter bivariate
  exports retain source premise strength and Landau direction. The two source
  examples remain validation definitions/private gates. Mathlib's fixed-shrink
  Akra–Bazzi endpoints are documented but not misapplied to `n-1` recurrences
  or duplicated. Independent review found the semantics faithful and caught
  three missing principal-export guards; the worker added those guards without
  changing any theorem or proof. Final coverage is ten kernel-three guards.
  Supervisor replay: focused module 2,248 jobs, concepts 505, full proofs
  3,243, and `lax build --only proofs word-ram` green; zero
  `sorry`/`admit`/`native_decide` and no new warnings. **Next: P3.C-F,
  bounded BfsQ/introsort consumer demonstrations and the complete A–E source
  table audit.**

- **2026-07-31 — P3.C-D COMPLETE; two-dimensional composition and
  normalization green.** `Asymptotics/TwoDimensionalComposition.lean` maps
  all 12 live declarations in the remaining `Asymptotics_2D.thy` ranges plus
  the `landau_util_2d.ML` substrate exclusion. O/Ω/Θ composition preserves
  both independent inner-coordinate growth premises and natural composition
  before casting. The `polylog2` comparison remains deliberately partial—one
  coordinate strict, the other weak—and the named normalization family does
  not claim a global simplifier. Six principal exports carry kernel-three
  guards; representative checks cover Θ composition, both comparison branches,
  and multiplication normalization. Independent semantic review found no
  source-fidelity defect. Supervisor replay: focused module 1,989 jobs,
  concepts 505, full proofs 3,075, and `lax build --only proofs word-ram`
  green; zero `sorry`/`admit`/`native_decide` and no new warnings. **Next:
  P3.C-E, the complete scheduled recurrence family.**

- **2026-07-31 — P3.C-C COMPLETE; genuine product-filter two-dimensional
  foundations green.** `Asymptotics/TwoDimensional.lean` maps all 26 scheduled
  declarations from `Asymptotics_2D.thy` lines 5–270, 467–559, and 638–669:
  the four Landau faces over literal `atTop ×ˢ atTop`, `polylog2`, stability
  and eventual norm-monotonicity, O/Ω extraction, and 1D-to-2D little-o and Θ
  lifting. The disjoint P3.C-D composition/comparison/normalization ranges did
  not leak into this leaf. Natural multiplication remains before coercion;
  Ω remains reverse big-O. Twelve principal exports carry kernel-three guards
  and representative positive checks exercise independent thresholds,
  coordinate lifts, extraction, and multiplication. Independent semantic
  review found no source-fidelity defect. Supervisor replay: focused module
  1,988 jobs, concepts 505, full proofs 3,074, and
  `lax build --only proofs word-ram` green; zero `sorry`/`admit`/
  `native_decide` and no new warnings. **Next: P3.C-D, two-coordinate
  composition, comparison, and named normalization.**

- **2026-07-31 — P3.C-B COMPLETE; one-dimensional operations and
  normalization green.** `Asymptotics/OneDimensionalOperations.lean` accounts
  for all 32 live public declarations in the scheduled `Asymptotics_1D.thy`
  lines 386–854 family and records four exact exclusions: composition for
  O/Ω/Θ, natural division and subtraction before coercion, ceiling and log
  bounds, Θ addition, and the named normalization-rule family. The dead
  `polylog_power_compose` proof ending in `oops`, the supporting ML registry,
  the source attribute, and the master-theorem method are classified rather
  than silently omitted. Twelve principal exports carry kernel-three guards;
  negative controls preserve composition direction, truncation, and
  nonnegativity premises. Independent semantic review found no source-fidelity
  defect. Supervisor replay: focused module 1,987 jobs, concepts 505, full
  proofs 3,073, and `lax build --only proofs word-ram` green; zero
  `sorry`/`admit` and no new warnings. **Next: P3.C-C, genuine product-filter
  two-dimensional foundations and lifting.**

- **2026-07-31 — P3.C-A COMPLETE; one-dimensional asymptotic foundations
  green.** `Asymptotics/OneDimensional.lean` ports the complete scheduled
  `Asymptotics_1D.thy` lines 7–384 family: eventual nonnegativity, `polylog`,
  positive-natural scaling stability, eventual norm-monotonicity, O/Ω
  introduction and extraction, and the four eventual-growth consequences. Its
  38-row source table accounts for five source/substrate definitions and 33
  public theorems. Isabelle Ω is pinned as reverse mathlib big-O; natural-valued
  boundaries cast only in Landau premises and return natural witnesses. Three
  compiled negative controls reject reversed polylog comparison, zero scaling,
  and monotone-norm addition without nonnegativity; positive gates cover strict
  polylog order, stability/monotonicity closure, and both extractors. Thirteen
  principal exports carry kernel-three guards. Independent semantic review
  found no source-fidelity defect. Supervisor replay: focused module 1,986 jobs,
  concepts 505, full proofs 3,072, and `lax build --only proofs word-ram` green;
  zero `sorry`/`admit` and no new warnings. **Next: P3.C-B, the remaining 1D
  composition, arithmetic, ceiling/log, Θ-addition, and named normalization
  families.**

- **2026-07-31 — Rev 4 focus firewall; source machinery first.** At Jan's
  direction, the contract was pruned of latent consumer side-tracks. P0's
  landed map now freezes active source slices; “port more” means complete a
  scheduled declaration family, not add sources or adaptations mid-phase.
  P3.C is the faithful IHT 1D/2D/recurrence machinery before BfsQ/introsort
  demonstrations; P4 exports generic credits before P9's arena
  instantiation; P7/P8 use generic primary fixtures; P9 is the sole ND-MC
  integration boundary. Edmonds–Karp, stretch rows, consumer-triggered
  revisits, and independent AFP/CFML excursions are quarantined for P10 or a
  later campaign. P6 now owns the real omitted-source debt
  `flatCurrs_whileT` through generic `RECT` transport.

- **2026-07-31 — P3.B COMPLETE; currency house style and the introsort
  budget spine green.** `Examples/IntrosortBudget.lean` audits the four pinned
  sorting theories plus the imported partition and final-insertion phase
  accounts. `phaseCost` establishes the named-vector convention;
  `partitionBudget` is the exact source `introsort_aux_cost`; and
  `IntrosortAccount` keeps recursive control, partition work, heap fallback,
  top-level dispatch, the `slice_part_sorted` token, and insertion finish
  visible. `topLevelAccount` is exactly `introsort3_cost`, `recursiveAccount`
  is exactly `introsort_aux_cost`, and the TId-style `recursiveUpdateRate`
  theorem replaces (rather than double-counts) the first-phase token.
  `introsortSpine_consumes` witnesses the coherent top-level account in NREST
  without claiming sorting functional correctness. The final
  `introsort_cost3` upper-bound vector keeps
  the locale comparison currency explicit; `introsortBudget_normal` is proved
  structurally with `norm_cost`/`sc_solve`. Finite collapsed rates connect the
  outer `slice_sort` token to the exact top-level account and named operation
  upper bound. Refute-before-prove gates cover `n=0`, `n=8,d=6`, heap-phase
  deletion, `slice_part_sorted`, vector-before-cash discipline, and the local
  IR's zero price for source `load`. Ledger E15 records why the exact source
  unit projection—not the smaller local codegen price map—is the honest cash
  boundary, and why the later synthesized source matrices remain collapsed.
  `introsortBudget_cash` exchanges once to Unit and flattens once, exactly
  reproducing `4693 + 5 log n + 231 n + 455 n log n`. Focused module build is
  green at 2,985 jobs; full package builds are green at 505 concepts and 3,066
  proofs jobs; `lax build --only proofs word-ram` is green. Its first run caught
  and the worker removed four `native_decide` generated axioms. Zero
  `sorry`/`admit`. **Next: P3.C, the mathlib asymptotic face.**

- **2026-07-31 — P3.A COMPLETE; currency automation, shallow VCG splitting,
  flatten-once cash boundary, and BFS exact vector green.**
  `NREST/Automation{Attrs,}.lean` ports `norm_cost`, `norm_pp`, the structural
  `leqSidecon` transition family, public `sc_solve`/debug variants, and
  canonical upper-bound synthesis; `costmult` is recorded as having no Lean
  analogue beyond additive scalar action. `NREST/VcgCaseSplit.lean` ports the
  corrected Sepreftime `MoreCurrAutomation.thy:73–131` splitter at exact pin
  `c1c987b45ec886d289ba215768182ac87b82f20d`, deliberately restricted to
  `gwp`/`progress` program heads that are `Option`/`Sum` matches, with a
  negative non-match control. `NREST/FlattenCurrencies.lean` gives the Unit
  order isomorphism, structural laws through genuine nondeterministic bind,
  codegen exchange, and one cash collapse; ledger E14 records why conditional
  while transport waits for generic `RECT` conjugacy. `BfsQ.bfsQTotal_normal`
  pins the complete seven-coordinate abstract account via `norm_cost`/`sc_solve`
  without importing flattening or code generation. Downstream,
  `BfsQSynth.flatCost_cash_bfsQTotal` crosses exchange→Unit→flatten to exactly
  `56n + 40ns + 33`; `BfsQSynth` consumes the coordinate theorem and no longer
  uses its four `decide +kernel` subaccount oracles. Principal exports have pinned
  kernel-three axiom guards. Focused Automation, FlattenCurrencies,
  VcgCaseSplit, BfsQ, and BfsQSynth builds are green. Supervisor replay:
  concepts build 505 jobs; the full proofs root builds 3,065 jobs; and
  `lax build --only proofs word-ram` is green, with zero new `sorry`/`admit`
  and only the previously recorded warnings. **Next: P3.B, currency house
  style and the introsort budget spine; P3.C remains the later asymptotic
  face.**

- **2026-07-31 — P2.B COMPLETE; iteration-list/Autoref discipline and
  nested for combinators green.** `Autoref/Foreach.lean` ports
  `list_set_rel`, the `autoref_nfoldli` rule, source `LIST_FOREACH'` and its
  vector parametricity rule. Observable `itToSortedListE` results are proved
  to be distinct `listSetRel` enumerations of exactly the input set, retaining
  the source ordering witness and the declared vector bound; the two-member
  sorted-list gate is compiled. `NREST/For.lean` ports the one-, two-, and
  three-index recursion combinators and proves their full traversals equal
  one/two/three nested `nfoldli`s over `List.range (n + 1)`, with a cube-shape
  gate. Ledger E13 records use of the source's own proved closed forms for the
  multi-index definitions. The root imports both modules. Concepts build 505
  jobs; full proofs root builds 3,061 jobs; `lax build --only proofs word-ram`
  is green; zero sorry/admit and no new warnings. **Next: P3.A, currency
  normalization and side-condition automation.**

- **2026-07-31 — P2.A COMPLETE; currency-vector member iteration and
  compiled carrier-blindness green.** `NREST/Foreach.lean` adds the authored
  E5 vector `nfoldli`, append/assert/relational-refinement laws, inert
  invariant/energy annotations, an exact invariant-and-cost rule, the
  `FOREACHociE`/`FOREACHciE` family, and the source decomposition through
  `itToSortedListE`/`LIST_FOREACHE`. `Sepref/Foreach.lean` adds the
  source-shaped hnr lowering bridge and synthesizes a masked index walk.
  Its compiled IR is pinned: `while k < kend`, reading `members[k]` and only
  then `carrier[u]`; the carrier is framed read-only and cannot determine
  the bound. The 2-member/100-cell gate proves the loop exactly equals the
  abstract `nfoldli` plus three guard charges and pins 4 `aget`, 4 `add`,
  2 `skip`, 3 `while`, with kernel-three synthesized/abstract judgments.
  NR-9 closes. Concepts build 505 jobs; full proofs root builds 3,059 jobs;
  `lax build --only proofs word-ram` is green; zero sorry/admit and no new
  warnings (the root replay retains its recorded warnings). **Next: P2.B,
  iteration-list refinement, Autoref
  iteration rules, and RECT for-loop nesting.**

- **2026-07-31 — P1.C COMPLETE; P1 signature machinery closed.**
  `Sepref/IntfUtil.lean` lands the `sepref_decl_intf`, `sepref_decl_op`,
  and `sepref_decl_impl` layer. Nominal interface declarations support
  parameters and feed a checked logical-type normalizer. `INTF_OF_REL`
  lookup preserves configured interfaces through list/option/product/sum/
  function/NREST relators and retains the source abstract-carrier fallback.
  Operation declarations define `op_…`/`pre_…`, validate and register the
  conceptual type, and publish the proved `fref` fact; implementation
  declarations perform checked FCOMP and install the result in
  `sepref_fr_rules`. The root-imported gate declares a fresh `CounterI`,
  its operation, and a composed concrete implementation entirely through
  those commands, then checks the public rule database. Ledger E12 records
  the explicit-proof Lean frontend in place of Isabelle's relation parser
  and after-QED ML transformation. SIG-8 closes. Concepts build 505 jobs;
  full proofs root builds 3,057 jobs in 80 s after the initial 120 s replay
  timed out at 3,046/3,057; no new warnings and zero sorry/admit.
  **Next: P2.A, currency-vector `nfoldli`/FOREACH and its refinement rules.**

- **2026-07-31 — P1.B COMPLETE; signature-driven synthesis and operation
  registration green.** `sepref_synth` now accepts an `hfref` signature,
  unfolds its three generic binders into the existing translation pipeline,
  and packages the synthesized program back into the signature theorem.
  `SignaturePrep.lean` pins a small chain and an eight-array phase with no
  written `hnRefine` judgment. `BfsQSignature.lean` regenerates the entire
  three-loop `BfsQSynth` command from signature data and proves its result
  tuple and `Com` definitionally equal to the landed implementation.
  `Register.lean` ports the True-valued `intfOfAssn` registry, abstract-type
  fallback, assertion-directed `sepref_register`, direct conceptual-type
  override, and `id_rules` installation; its eight-array operator resolves
  a deliberately non-native interface eight times and TYPE annotation wins
  at an occurrence. Debt SIG-6 and SIG-7 closes. Ledger E11 records direct
  transparent preparation and Lean's arity-polymorphic monadifier in place
  of Isabelle `Term_Synth` and generated arity/mcomb equations. Concepts
  build 505 jobs; full proofs root builds 3,056 jobs in 117 s; root
  `lax build --only proofs word-ram` OK; new BFS theorem kernel-three; zero
  sorry/admit and no new warnings. **Next: P1.C, the `sepref_decl_op` /
  `sepref_decl_intf` / `sepref_decl_impl` declaration layer.**

- **2026-07-31 — P1.A COMPLETE; signature composition frontend green.**
  Four new root-imported modules land the half-size calibration wave:
  `Signature.lean` (exact `compPRE`, safe `to_hnr`/`to_hfref`, pure and
  heap `FCOMP`, dependent result branch), `SignatureTool.lean`
  (`sepref_fcomp` dispatch from either `hfref` or a generalized
  `hnRefine` family, pure `fref ∘ fref`, visible `attainsSup` residue,
  bounded checked normalization), `SignatureFlatten.lean` (correlated
  dependent-composition residue and two-layer eliminator), and
  `SignatureNorm.lean` (the source `hr_comp` laws plus `one_time` and
  attained-supremum helpers). Two tempting surfaces are now compiled
  negative controls: a fixed `hnRefine` instance is not a signature, and
  independently composing dependent input/output relations is unsound
  because it loses their shared witness. Debt SIG-2–SIG-5 closes; ledger
  E10 records transparent Lean theorem/tactic frontends in place of
  Isabelle theorem attributes. Concepts build 505 jobs; full proofs root
  build 3,053 jobs in 135 s, root `lax build` OK, kernel-three axiom
  probes, zero new warnings and zero sorry/admit.
  Calibration feedback is folded into the worker template/retro. A
  redundant fresh-worktree seed hit ENOSPC before edits; the empty failed
  worktree was removed and the wave continued in the already-seeded
  campaign worktree. **Next: P1.B, signature→goal preparation and
  `sepref_register`/interface-type discipline.**

- **2026-07-31 — Rev 3 / P0 COMPLETE; CODEX-ONLY.** Jan: "we only use
  codex, not claude." The active working model and README are amended:
  Codex supervises and GPT-5.6-Sol via `codex exec` is the only worker
  path; the earlier non-Codex hard-wave fallback is withdrawn. P0 lands
  `tower-expansion/{port-map,ledger,debt-register}.md`: the 69-file /
  47,054-line baseline reconciled against the pinned theory graphs; pins
  for `isabelle_llvm_time`, `isabelle_llvm`, Sepreftime, and
  Imperative_HOL_Time verified upstream; every unported component assigned
  to a wave or an argued exclusion. Findings that bind later phases:
  no source has currency-vector FOREACH (E5, authored adaptation); the
  primary artifact's IICF is dead/no-cost (E7, P5 is cost adaptation);
  introsort is P3's native exemplar and Sepreftime supplies timed
  Kruskal/union-find (E6); deterministic hash maps are excluded on cost
  honesty grounds (E9). The debt register carries 52 individually owned
  rows, including closed/verify dispositions for dependent `hfcomp`, the
  unfueled loop rule, recursive trail acceptance, and the scaling probe.
  No Lean changed and no build was required. **Next: P1.A, the half-size
  GPT-5.6-Sol calibration wave (`to_hnr`/`to_hfref`, `comp_PRE`, FCOMP,
  dependent-composition flattening).**

- **2026-07-31 — Rev 2: ACCEPTED.** Jan: full autonomy carries over,
  flags resolved by supervisor taste (dispositions recorded above), and
  the worker model changes — proof workers are **GPT-5.6-Sol via
  `codex exec`** (verified installed and authenticated, codex-cli
  0.145.0, default model `gpt-5.6-sol`). Rev 2 retained a non-Codex
  alternative for the hardest waves; Rev 3 withdraws it. First Sol wave
  in P1 is a half-size calibration wave. P0 is unblocked and starts next
  session.

- **2026-07-31 — Rev 1 authored** (this session), from: the ND-MC C0
  blocker analysis (compiled floors, THE SEAM, R1.6), the tower
  campaign's closing records (`p8-verdict.md` thaw queue and open
  items), the July worker retro, and Jan's port-aggressively mandate.
  Awaiting acceptance; P0 is ready to start the session after.
