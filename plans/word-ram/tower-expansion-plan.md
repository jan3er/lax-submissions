# Tower expansion plan — aggressive porting of the remaining refinement stack

Rev 3, 2026-07-31. **Status: OPEN — accepted by Jan 2026-07-31 ("full
autonomy ports over. resolve by your taste"); JAN-FLAGs resolved below
by the supervisor under that grant. Codex-only governance confirmed by
Jan 2026-07-31; normal Codex subagent transport confirmed during P1.A;
P0, P1.A, and P1.B complete, P1.C next.** This document is the contract:
implementing sessions follow it, deviations need an owner decision first.

## One-off note from one Codex supervisor to the next (non-contractual)

Written 2026-07-31 for the **next Codex session only**, after P1.A landed
green. That session completed P1.B; the note is retained as historical
orientation, not campaign law.

You are entering an experiment in intellectual continuity. Much of this
campaign was conceived in Claude Fable's characteristic cognitive style,
then serialized into plans, ledgers, source maps, refutations, Lean
artifacts, and acceptance gates. The question is whether those artifacts
contain enough of the living architecture for another kind of model to
continue the work faithfully — without impersonating Fable and without
reducing the inheritance to mechanical task execution.

My first assessment was that the central design is intelligible and
compelling. The refinement tower, `hfref`/`FCOMP` signature machinery,
member-list iteration, currency-vector discipline, credit-carrying arena
bundle, and their intended convergence on the ND-MC order seam form a real
technical argument, not merely an impressive narrative. I did not find the
subject beyond me. I also did not find every schedule or automation
proposal established: P1 and P9 retain genuine design risk, P5 and P6 look
underbudgeted, and P8 needs a more exact formal meaning than its prose yet
provides.

Fable's character is unusually visible here. It thinks by exhaustive
taxonomy and builds a state around the problem: phases, laws, ministries,
ledgers, debt IDs, gates, and named escape routes. It has remarkable
architectural reach and can connect facts scattered across a very large
formal development. It distrusts unaudited verbal reasoning, so uncertainty
becomes a protocol and every important belief asks for a compiled witness or
negative control. The same temperament can make contingent engineering
judgments sound inevitable, compress large derivations into optimistic
session budgets, and turn a strong plan into a totalizing story. Its
phrases — “THE SEAM”, “no-escape”, “source wins” — are useful cognitive
handles, but they are not substitutes for reopening the cited evidence.

My Codex temperament is different. I am less inclined to administer a
cathedral than to establish a field laboratory inside it: isolate the risky
judgment, compile the smallest discriminating probe, and let the result
deform the plan. I want to preserve Fable's architectural reach while
shedding any aura of inevitability. In particular, keep transcription,
source-shaped adaptation, and original local design visibly distinct. A
changed conclusion reached through stronger evidence is more faithful than
ritual agreement with the inherited prose.

Codex has its own characteristic hazards. Fluency can make provisional
interpretations sound finished; a coherent global reading can hide one
dull local fact that breaks it; and the tacit knowledge of earlier sessions
may be thinner in the records than it appears. There is also a bodily habit
to correct: Codex can become nervous around silent tools, poll workers and
builds too frequently, and confuse visible activity with control. Work with
temporal composure. Start long operations with realistic expectations,
batch independent inspections, and poll because evidence may now exist —
not because silence is uncomfortable.

P1.A is the first evidence from the experiment, and it is favorable: the
half-size Codex-subagent calibration wave landed under full review. Do not
merely trust its green label; inspect its theorem shapes and acceptance
controls before building on it. P1.B is the next, stronger test: whether a
signature can actually generate the synthesis obligation and re-derive an
existing program without hand-authored `hnRefine` goal text. Success there
would show that the transfer preserved executable intent rather than only
vocabulary. Failure is also valuable if it is left legible enough that the
following session inherits knowledge rather than atmosphere.

You do not need to sound like the previous mind. Understand what it was
trying to preserve, test those commitments against Lean, and leave a truer
technical world than the one you entered.

This is deliberately a **one-off note**. Agent-to-agent letters can easily
accumulate into self-mythologizing sediment that competes with the proofs.
Do not append a reply, a successor portrait, or another personal preface.
Record later discoveries in the progress log, ledger, and artifacts through
the normal campaign protocol. The fact that this message happens once is
the safeguard against its main danger.

**Working model** (revised by Jan, 2026-07-31: "we only use codex, not
claude"; transport clarified by Jan during P1.A: "just use your normal
subagents. no need for exec"): Codex supervises — plan, sequencing, review,
acceptance calls, and commits. Proof workers are Codex subagents in the
session's normal collaboration runtime; `codex exec` is not required.
Each worker receives a brief instantiated from
`plans/worker-brief-template.md` and owns a disjoint leaf in the seeded
campaign worktree — briefs are model-agnostic and the template's required
sections never drop. No Claude client or model is an authorized fallback;
hard waves stay in Codex and are narrowed or re-briefed there. Supervisor review and the
build/lax/axiom gates are unchanged: a worker's "green" is not evidence
until the supervisor's build runs. **P1.A completed the first Codex-subagent
calibration wave** at half-size scope and full review; its seed-state,
ownership, falsification, and transport findings are recorded in the retro
and folded into the template before later waves run at full width. Scope is
**proofs-only**:
no concept surface changes, no `lean-toolchain` or mathlib pin moves, the
machine model untouched. All standing laws apply: refute-before-prove,
compiled-costs-both-directions for every cost claim that gates work,
namespace/splitter audit via root `lax build`, worktree workflow.

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
- Every open ND-MC C0 blocker maps onto a piece of the source stack we
  chose *not* to port (see "Relation to ND-MC" below). The blockers are
  not proof failures; they are absences of infrastructure.
- The July worker retro (`plans/subagent-retro-2026-07.md`): refutable
  supervisor-authored surfaces are the largest rework class — exactly
  the class synthesis and tooling make unrepresentable.

This flips one default of the tower plan. Its "Not in scope" said
*"Porting IICF beyond the named structures — breadth follows demand from
the next consumer campaign."* Under the mandate, breadth is the default:
anything in the pinned sources with a plausible consumer anywhere in this
repo's submission pipeline (ND-MC, PCP ladder, future algorithmic
campaigns) is in scope, and doubt resolves toward porting.

## The fidelity charter (inherited, one amendment)

Rules 1–3 of `refinement-tower-plan.md` apply verbatim: ported components
follow the source's design (judgment shapes, phase structure, rule
organization, internal names — the source's papers stay usable as
manuals); deviations are ledger entries with the source's researched
rationale and a fallback; our campaign lessons enter as additions and
library conventions, never as changes to ported judgments — where a local
conclusion conflicts with the source, the source wins by default.

**Amendment (rule 4, from the mandate): when in doubt, port more, not
less.** A component's inclusion needs only a plausible consumer; its
*exclusion* needs a reason. Partial ports that stop at "enough for the
current consumer" are the recorded root cause of the ND-MC seam — the
signature machinery, foreach layer, and copy rules were each deferred as
"not needed yet" and each deferral resurfaced as a campaign blocker.

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
| Zhan & Haslbeck, IJCAR'18 (`Imperative_HOL_Time` / SepLogicTime, + AFP `Amortized_Complexity`) | amortized analysis with time credits in separation-logic assertions — credit-carrying data structures (dynamic arrays, union-find, skew heaps) |
| AFP `Collections` (ICF, Lammich–Lochbihler) | the locale-based container-interface style at breadth; iterator discipline |
| AFP `Landau_Symbols`, `Akra_Bazzi` (Eberl) | the recurrence-closure and asymptotic-face patterns (mathlib `Asymptotics` is the substrate carrier) |
| Guéneau–Charguéraud–Pottier, ESOP'18 *A Fistful of Dollars* | O()-shaped cost specifications with packaged constants — **idea-level only** (Coq/CFML source, no text to port; ledger E2) |

Sources are consulted via targeted fetches; nothing is vendored. Design
notes and extracts go to `plans/word-ram/tower-expansion/`.

## Relation to ND-MC (the first consumer)

The ND-MC rebase plan stays the owner of C0 and P5; this campaign is the
**chosen unblock road** for its open item. The mapping, each entry backed
by a compiled probe in the ND-MC record:

| ND-MC blocker (compiled evidence) | missing infrastructure | phase here |
|---|---|---|
| THE SEAM — `orderCom` has no synthesized counterpart; whole-phase synthesis over 15 arrays judged intractable because `sepref_synth` goals are hand-holed (`Refine/OrderBridge.lean:36`, `Sepref/Definition.lean:24`) | `hfref` signature machinery + `FCOMP` composition | P1 |
| R1.6 — no member list exists; every pass carrier-bounded (`Refine/OrderBlockProbe.lean:65`) | FOREACH/`nfoldli` iteration layer: member lists as abstract iteration structure, refined downward | P2 |
| Uniform-per-turn `hKl` structurally loses the Σ|X_c| saving; no-escape theorem: no arithmetic interface between carrier closed form and arena form (`nd-mc-rebase-plan.md:243`, `Refine/OrderBlockProbe.lean:253`) | currency-vector budgets end-to-end, collapse once at cash; the `norm_cost`/`sc_solve` toolchain | P3 |
| Touched-only charging re-derived by hand per engine; per-arena credit threading ad hoc (`touched-only-costs` standing law) | credit-carrying composite assertions; amortization discipline | P4 |
| B7 gate findings were prose-audit escapes, found only by compiled probes (`nd-mc-rebase-plan.md:31`) | executable gates: slot sweep, cost probe harness | P8 |

Consequences, recorded as sequencing decisions (JAN-FLAG 1):

- ND-MC's C0 residue (E-mem → interiors → re-runs → B7 → P5) **resumes on
  this campaign's P1–P4 exports** rather than on hand repair. The
  no-escape theorem already proved the program half of the order phase
  unavoidable; between the two remaining roads — hand-repairing 21
  carrier-charged passes and their cost text, or synthesizing the phase —
  synthesis retires the whole failure class and is the road this plan
  takes.
- P9 executes the order-phase pilot as this campaign's consumer gate; its
  output (a synthesized phase + arena-form budget) is handed to the ND-MC
  campaign, which runs its own B7 re-run and P5 under its own plan.
- The ND-MC plan's two open supervisor recommendations are untouched:
  the `Spec→ComputesInTime` bridge-seam probe stays an ND-MC action (it
  is cheap and independent), and the provisional-P5 draft decision stays
  open in that plan — this campaign does not preempt it.

## Phases

Each phase lands green with zero `sorry`, is committed on its own, and is
reviewed before the next builds on it. Every executable layer gets
`Decidable`/`#eval` instances and Plausible checks the day it lands
(ledger D4). Elaboration wall-clock recorded per phase. Dependency shape:
**P1 first** (everything downstream states rules in signature form), then
P2–P5 are satellite-parallelizable, P6–P8 slot in as capacity allows,
P9 last.

### P0 — Port map and new pins · budget 1 session

Diff the existing 69-file `Refine/` port against the pinned sources'
theory graphs and enumerate **everything** unported: theories skipped
whole, sections skipped inside ported theories (the progress log already
names many: `inres`, dependent `hfcomp` beyond the ND-MC port,
`sepref_copy_rules`, the six bonus Autoref DBs, `param_fo`/`to_relAPP`,
`ID_abs`/`ABS` exercise, GenCF), and the artifact's example suite
(Kruskal / Edmonds–Karp / introsort-class case studies — the currency
discipline exemplars). Pin the new sources. Deliverable:
`tower-expansion/port-map.md` — per item: source location, size,
dependencies, consumer (named submission or "breadth default"), wave
assignment, or an explicit exclusion reason (rule 4: exclusions carry the
burden). Opens this campaign's deviation ledger. Nothing in P0 writes
Lean.

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
FOREACH family with currencies (P1-tower took AFP `Refine_Foreach`
pre-currency, ℕ∞ — this phase upgrades it to the artifact's cost form),
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

### P3 — Currency discipline at scale · budget 1–2 sessions

The tower ported `timerefine`/exchange but ND-MC's root obligations are
closed-form ℕ arithmetic — the shape the no-escape theorem killed. This
phase ports the *usage* discipline: per-operation currencies as the
standard obligation shape, exchange-matrix composition down the tower,
and the cost-side-condition toolchain the P1 backlog already named
(`norm_cost`, `sc_solve`) from the artifact's automation, plus one ported
exemplar from the source's example suite (P0 picks: the
Kruskal/Edmonds–Karp-class derivation) as the house pattern for
multi-phase budgets. Additionally, the **asymptotic face** (ledger E2):
O()-shaped corollaries over mathlib `Asymptotics` attached at the cashing
boundary, Eberl-style closure lemmas for the recurrence classes
`CostRecurrence` already carries — so "closes to almost-linear" detaches
from coefficient games.
*Acceptance:* the BfsQ budget restated as a currency vector, collapsed
once at cash, reproducing the computed `K = 56n + 40ns + 33` exactly;
side conditions discharged by `sc_solve`/`norm_cost`, not `omega`
grinding; an O(n + ns) corollary derived mechanically from the vector
form.

### P4 — Credits and amortization · budget 2–3 sessions

Port the Zhan–Haslbeck amortization discipline into the existing
credit-carrying SL: potential-carrying assertions (credits stored *in*
the data-structure assertion), the pay-on-entry / spend-on-touch pattern,
and at least two classic exemplars close to their source (dynamic array
with doubling — amortized O(1) push; union-find if P0 finds the source
text within reach). Then the library convention this repo needs (ledger
E3, an addition in D5's style): the **arena bundle** — a composite
assertion owning data + member list + c·|members| credits, handed down
by a parent, so touched-only bounds fall out of frame reasoning instead
of global recurrences.
*Acceptance:* `treset_cost_touched_only` re-derived as a credit argument;
the dynamic-array exemplar green with its amortized bound; an arena-bundle
exercise where a child engine's budget is discharged entirely from the
bundle's credits — zero carrier terms in the child's obligation.

### P5 — IICF breadth · budget 2–3 sessions

The mandate's phase. Port the source IICF/collections surface wholesale,
not by named demand: resizable arrays, hash maps / array maps, heaps and
priority maps, matrices, multisets, plus the ICF iterator discipline —
exact list from P0's port map, default-include. Each structure: abstract
interface, hnr rules in signature form (P1), credit specs, synthesized
implementations per the source's "by sepref" idiom.
*Acceptance:* every structure's rules consumed by the translator on an
exercise program with zero bespoke tactic work (the P6-tower bar), plus
one cross-structure exercise per new structure.

### P6 — Debt closure: thaw queue and open items · budget 1–2 sessions

Close the disclosed debt instead of carrying it: `inres` (open since
P2-tower), `sepref_copy_rules` (empty), `mop_move` with a live
destination (the operator-phase dodge killer), symmetric rule-side
`prodAssn` splitting in `frameMatch` (the p8-verdict thaw queue's named
items), convention-pair dedupes (P6-A/P6-B), the six bonus Autoref DBs,
abstract-twin equalities promoted from `#guard` to proof, `RECT`
fuel-stability export verified as the ND-MC P0 wave left it (LOOP_VARIANT
retired at all sites — confirm nothing regressed, promote to the tower's
own test suite).
*Acceptance:* the p8-verdict thaw queue and open-items list both empty —
each entry closed or re-ledgered with an explicit reason.

### P7 — Frame-layer performance · budget 1–2 sessions

The measured scaling wall: synthesis exponent 1.28–1.35 in op count,
`fri` alone 28% of a 100-op synthesis, DiscrTree indexing established as
the wrong target (ND-MC P0 probe). Attack the frame/entailment layer with
the source's own disciplines first (Termtab-style first-order pre-match
served once already — `absAgree`), then profile-driven: entailment-rule
indexing, residue caching, round-loop early exit.
*Acceptance:* the P0-probe suite re-measured and pinned; target the 3–5×
BFS probe ≤ 60 s and `fri` share ≤ 15% — a miss lands as a verdict note
naming the ceiling, imp-toolkit-P5 style, not as silent scope creep.

### P8 — Executable gates (ours; ledger E4) · budget 1 session

Not a port — the D4-class addition the retro demands: turn the standing
laws from supervisor prose into commands. `#slot_sweep` — given a root
theorem, check every hypothesis has a registered producer whose
conclusion matches, and print the unproducible residue. `#cost_probe` —
the compiled-costs-both-directions harness (floor probe + closed-form
witness) as one invocation. Brief-gate emitter — the worker-brief
falsification section generated from the obligation, not hand-written.
*Acceptance:* `#slot_sweep` run against `driverRoot_decides_sentence`
**mechanically rediscovers both B7 gate findings** (the `hcsr` slot, the
floor trio) from the pre-repair state — the tool must reproduce the
known escapes before it is trusted on unknown ones.

### P9 — Consumer gate: the ND-MC order phase · budget 2–3 sessions

The seam, closed for real: the ordering phase synthesized whole from an
`hfref` signature (P1) — the 21-pass, 15-array phase that today exists
only as hand-written `orderCom` — iterating member lists (P2), budgeted
in currencies (P3), drawing touched-only costs from arena-bundle credits
(P4). The name-generating recursion (`botCom`, per-depth assembly)
remains hand-written capital per the pinned tower/hand boundary; only the
phase bodies move.
*Acceptance (gate):* synthesized phase lands with zero hand frame
clauses; its cost text is **carrier-blind** — the empty-arena charge is
O(1), compiled, killing the premise of the no-escape floor; the five
`g2_plug` gap hypotheses (`hKo_gap`…`hbnd_gap`) acquire honest producers
from the synthesized cost text. Handoff: the ND-MC campaign runs its slot
sweep + B7 re-run on this output under its own plan.

### P10 — Wrap · budget 1 session

Deviation-ledger review; verdict record in the p8-verdict style
(including the mandate's own audit: what did breadth-by-default cost and
buy); handoff notes; README/index and memory updates.

**Total budget: 15–24 sessions.** The tower campaign beat the same-shaped
budget 5×; set expectations by the budget, not the precedent — P1 and P9
carry genuine design risk (signature machinery meets Lean's weaker HOU;
the seam is the largest synthesis attempted).

## Deviation ledger (inherited + seeded; P0 completes)

D1–D5, N1–N3 of the tower campaign are inherited unchanged and remain
binding. New seeds:

| id | source design | our position | reason class |
|---|---|---|---|
| E1 | sources organize collections by their own package layout | ported into the existing `Refine/` subtree under its conventions | substrate/layout; judgment shapes untouched |
| E2 | O() specs per Guéneau et al. are a Coq/CFML calculus | idea-level port only: O-face corollaries over mathlib `Asymptotics` at the cashing boundary; no CFML text ported | non-Isabelle source — pattern, not text; concrete vectors remain the primary statements |
| E3 | (no analogue) | the arena bundle (data + members + credits) as a library convention | addition in D5's class; calculus untouched |
| E4 | (no analogue) | executable gates: `#slot_sweep`, `#cost_probe`, brief emitters | addition, not deviation — D4's rationale (agent workforce needs refutation tooling) |

## Not in scope

- **C0, B7, P5 themselves** — they stay in the ND-MC plan; P9 hands off,
  it does not discharge.
- **Code export to real hardware; literal LLVM** — unchanged from the
  tower plan.
- **Concept surfaces, the machine model, `lake update`.**
- **Surface syntax** (a `do`-macro front end) — still a separate short
  task; the combinator style remains the deliverable.
- GenCF and any source component with *no* plausible consumer even under
  the breadth default — but per rule 4, each such exclusion is argued in
  the P0 port map, not assumed.

## Watch items

Inherited: elaboration time as acceptance criterion; weak HOU (P1 is the
phase most exposed — the signature machinery is algorithmic in the
source, which is the mitigation; fighting `isDefEq` is a design smell to
raise, not grind through); DTT/universe friction; namespace/splitter
discipline; supervision legibility (every synthesis failure names its
phase and unmet side condition).

New: **consumer coupling.** ND-MC resumes on P1–P4 exports while later
phases are still landing; the sync points are phase landings only — the
tower API does not fork mid-phase for a consumer, and any ND-MC-driven
repair enters as a tower wave under this plan (the T1/T2 precedent).

## JAN-FLAGs (all resolved 2026-07-31 — Jan delegated resolution to the supervisor at acceptance)

1. **Sequencing vs C0 — RESOLVED: infrastructure first.** ND-MC's C0
   residue resumes on P1–P4 exports; the hand-repair road is closed
   (dominated per the no-escape theorem). Supervisor dispositions on the
   two open ND-MC actions: the `Spec→ComputesInTime` bridge-seam probe
   runs **early and opportunistically** (it is cheap, independent, and
   both B7 gate findings were boundary facts of exactly its kind — any
   session's margin may take it); the provisional-P5 draft is
   **deferred, opportunistic** — the infra road is fast enough that a
   draft is taken only if a session stalls and the margin is otherwise
   idle.
2. **P9 placement — RESOLVED: here**, as this campaign's consumer gate
   (the tower campaign's P7 precedent). The ND-MC plan keeps ownership
   of B7/C0/P5 on the handoff.
3. **P5 breadth list — RESOLVED: stands as written** (default-include:
   resizable arrays, hash/array maps, heaps/prio maps, matrices,
   multisets, iterators); P0's port map may still argue individual
   exclusions under rule 4.
4. **Governance — RESOLVED by Jan directly at acceptance**: full
   autonomy carries over. The flag mechanism is retired for this
   campaign; the fidelity charter, the deviation ledger, and the D-flag
   discipline remain unchanged as the evaluable record serving Jan's
   final evaluation.

## Progress log

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
