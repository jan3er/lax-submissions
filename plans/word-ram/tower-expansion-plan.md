# Tower expansion plan — aggressive porting of the remaining refinement stack

Rev 4, 2026-07-31. **Status: OPEN — accepted by Jan 2026-07-31 ("full
autonomy ports over. resolve by your taste"); JAN-FLAGs resolved below
by the supervisor under that grant. Codex-only governance confirmed by
Jan 2026-07-31; normal Codex subagent transport confirmed during P1.A;
P0, P1, P2, P3.A, P3.B, and P3.C-A complete; P3.C-B next. The source-first scope
firewall below was added at Jan's request on 2026-07-31.** This document is
the contract: implementing sessions follow it, deviations need an owner
decision first.

## Governance and working model

Codex supervises plan, sequencing, source review, acceptance calls, and
commits. Where practical, one subagent owns a coherent phase or subphase;
the supervisor audits its source map and diff, requests corrections,
independently rebuilds, and commits. Main-tree work is authorized for this
campaign. Parallel agents receive disjoint files, and every worker brief is
instantiated from `plans/worker-brief-template.md` with its required sections
intact. A worker's green report is not acceptance evidence until the
supervisor replays the build, lax, and axiom gates.

Scope is **proofs-only**: no concept-surface changes, toolchain or mathlib
pin moves, or machine-model changes. Refute-before-prove,
compiled-costs-both-directions, and root namespace/splitter audit remain
standing laws.

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
design P1–P8. No ND-MC module is imported or edited before P9, and no
consumer-specific API repair widens those phases. P9 is the sole integration
boundary: it instantiates the frozen tower APIs, records consumer gaps for
handoff, and may send work back only when it demonstrates a source-fidelity
defect in a scheduled declaration. C0, B7, and the ND-MC P5 remain owned by
the ND-MC campaign.

## Phases

Each phase lands green with zero `sorry`, is committed on its own, and is
reviewed before the next builds on it. Every executable layer gets
`Decidable`/`#eval` instances and Plausible checks the day it lands
(ledger D4). Elaboration wall-clock recorded per phase. Dependency shape:
P1 → P2 → P3 forms the source/API spine; P4 follows P3; P5 waves follow
their declared P1/P2/P4 dependencies; P6–P8 run after the relevant APIs
freeze; P9 alone integrates the consumer; P10 wraps and reviews backlog.

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

### P4 — Credits and amortization · budget 2–3 sessions

P4 ports and validates the source credit calculus before any consumer
adaptation: generic time-credit assertions and rules, potential-carrying
data-structure assertions, the pay-on-entry/spend-on-touch discipline, and
the scheduled source-native dynamic-array and timed union-find developments.
It exports only generic credit machinery. The arena bundle and touched-only
reset theorem are P9 consumer instantiations and may not shape P4's
judgments or automation.

*Acceptance:* source→Lean declaration coverage for the selected SLTC and
amortization slices, the dynamic-array amortized-O(1) result, and timed
union-find green against the frozen generic credit API.

### P5 — IICF breadth · budget 2–3 sessions

The mandate's phase. Port the exact source IICF/collections surface assigned
by P0, honoring X5/E9 and every other recorded exclusion. Each structure:
abstract
interface, hnr rules in signature form (P1), credit specs, synthesized
implementations per the source's "by sepref" idiom.
*Acceptance:* uniform source-shaped rule-consumption gates per
implementation family with zero bespoke tactic work, followed—after the
P4/P5 APIs freeze—by one source-native Kruskal cross-structure validation.
Invented per-structure exercises do not become API requirements.

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

**Total budget: 17–28 sessions.** The tower campaign beat the same-shaped
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
