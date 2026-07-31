# Tower expansion deviation ledger

Opened 2026-07-31 by P0 of `tower-expansion-plan.md`. This is the
campaign-local register. The tower campaign's ledger remains authoritative
for the inherited entries; this file records their force here, the four
entries seeded by the accepted plan, and the P0 findings that changed the
shape of later phases.

Status vocabulary:

- **binding** — a standing design constraint for all later phases;
- **accepted** — a campaign decision whose consequences are scheduled;
- **verify** — already implemented before this campaign, but P6 must check
  that the export and its consumers have not regressed;
- **closed** — no further campaign work is attached to the entry.

**Scope firewall.** A revisit trigger is a P10/backlog note, not authority to
start work during P1–P9. The only exception is a defect that prevents the
current scheduled phase from satisfying a source-fidelity acceptance gate.
Consumer demand cannot add a source slice, local adaptation, or
cross-submission repair to a live phase.

## 1. Inherited charter entries

| id | status | source design / expectation | position in this repository | consequence here |
|---|---|---|---|---|
| D1 | binding | Isabelle/HOL, ML tactics, locales, and HOL's inhabited types | Lean 4/mathlib substrate; theorem shapes stay source-faithful while tactics, locale packaging, and HOL-only conveniences receive explicit Lean renderings | Every substrate-forced change remains a named delta in the affected module; weak higher-order unification is never repaired by changing a judgment. |
| D2 | binding | LLVM shallow semantics below Sepref | The concrete layer is the endorsed first-order word-RAM IR. | P1–P6 may extend synthesis infrastructure and rules, but not the machine model. |
| D3 | binding | trusted Isabelle/LLVM export route | Verified `Ir` to IMP+ code generation and cashing. | New operations need verified codegen coverage before becoming executable capital. |
| D4 | binding | source examples are largely proof-script gates | Every executable layer gets computable twins, positive checks, and negative/refutation controls when it lands. | P8 turns the same discipline into reusable commands; phase acceptance cannot rest on prose or a worker's build report. |
| D5 | binding | ordinary arrays are the default mutable container | Trail-backed touched-only arrays are the repo default when sparse reset is semantically available. | P4 exports generic credit machinery; P9 alone instantiates the arena bundle and touched-only consumer argument. |
| D6 | binding | general recursion exists in the source | Executable programs remain loop-form at the tower/hand boundary. | P2 may port recursion combinators, but P9's name-generating recursion remains hand-written capital. |
| N1 | binding | separation logic is an implementation proof layer | The SL is consumed by synthesis, not written as per-program frame clauses. | Zero hand frame clauses remains an acceptance condition for synthesized consumers. |
| N2 | binding | source automation is Isabelle-specific | The repository keeps its small credit-carrying SL and `fri`/`refine_vcg`; it does not import Iris or auto2. | P4 reads `SLTC_Automation` for architecture only; P7 optimizes the existing solver. |
| N3 | binding | source extraction has machine-specific wrappers | The tower stays tape-free, with a wrapper only at the external `Spec`/`Solves` boundary. | P1–P9 do not move tape bookkeeping into refinement judgments. |

The full rationale and the earlier campaign's review are in
`../refinement-tower/design.md` and `../refinement-tower/p8-verdict.md`.

## 2. Entries seeded by the accepted expansion plan

| id | status | source design | campaign position | acceptance consequence |
|---|---|---|---|---|
| E1 | accepted | Source collections follow AFP/IICF package layouts. | Ports live under the existing `Lax13Proofs/Refine/` layout and naming conventions. | Judgment shapes and rule grouping stay source-faithful even where file splits differ. |
| E2 | accepted | IHT provides `Asymptotics_1D`, `_2D`, and `_Recurrences`; AFP/CFML supply semantic background. | Port the IHT declaration families faithfully over mathlib `Asymptotics`, then attach cash-boundary examples while keeping concrete currency vectors primary. | P3.C carries a complete source map and source-shaped gates before BfsQ/introsort demonstrations; no CFML, ND-MC, or duplicate Akra–Bazzi API. |
| E3 | accepted | No direct source analogue. | Add the arena bundle only as a P9 consumer instantiation of the frozen P4 credit API. | It cannot shape P4 judgments or automation; P9's child engine is paid from bundle credits with no carrier term. |
| E4 | accepted | No direct source analogue. | Add executable `#slot_sweep`, `#cost_probe`, and brief-gate emission. | P8 trusts generic frozen missing-producer and cost-floor fixtures; archived B7 is secondary read-only evidence. |

## 3. P0 findings and new entries

### E5 — currency-vector FOREACH is an authored adaptation

**Status: accepted.** No pinned source contains the cost-carrying,
multi-currency FOREACH promised by the plan. `isabelle_llvm_time` has no
cost FOREACH; AFP NREST and Sepreftime carry single-currency `enat`
versions; the existing Lean `Combinators.lean` carries the earlier
single-currency port.

P2 therefore derives a currency-vector `nfoldli`/FOREACH layer from three
shape sources: AFP `Refine_Monadic` for organization and invariants, AFP
NREST/Sepreftime for the single-currency cost statement, and
`Sepref_Foreach` for hnr-rule structure. It must not describe the result as
a transcription from the ESOP'21 artifact. The compiled carrier-blindness
probe is the soundness/fitness gate for the adaptation.

**Landed in P2.A.** `NREST/Foreach.lean` keeps the AFP recursion,
invariant/energy annotation, relational rule, and list-decomposition shapes
while lifting every scalar charge to `ECost`. `Sepref/Foreach.lean` renders
the iterator hnr conclusion as an explicit lowering premise. Its compiled
2-member walk over a 100-cell carrier proves exact vector cost and pins an
IR condition whose bound is the member count, not the carrier length.

### E6 — the exemplar suite is retargeted and adapted

**Status: accepted.** The primary artifact has sorting/introsort, not the
Kruskal or Edmonds–Karp examples assumed by the accepted plan. Those case
studies, including timed union-find, live in Sepreftime and use
single-currency `enat`.

- P3's currency-native house exemplar is the primary artifact's introsort
  budget spine.
- Timed union-find is an unconditional P4 source development. Kruskal is a
  source-native post-freeze validation after the required P4/P5 APIs land;
  it does not design those APIs.
- Edmonds–Karp is outside active P0–P10 scope. It is neither part of
  acceptance nor an idle-margin task; reconsider it only at P10 or in a
  later campaign.

Every adapted theorem must separate source-derived content from currency
lifting glue in its module header.

### E7 — P5 is cost adaptation, not a wholesale text port

**Status: accepted.** At `isabelle_llvm_time` 42dd7f5 the `sepref/IICF/`
tree is outside the built session, absent from `thys.txt`, and almost
entirely lacks cost vocabulary. The usable cost-carrying container sources
are the artifact's array fragments and dynamic array plus Sepreftime's
single-currency IICF; mature no-cost twins supply shape.

P5 ports the exact P0-fixed interface table, but each
implementation's vector cost statement is a derivation, following the
existing `CombRules.lean` precedent. Source file size is planning evidence,
not a claim that dead or no-cost text was mechanically translated.

### E8 — two skeleton drifts are recorded retroactively

**Status: accepted; verify in P6.** The closed tower campaign silently
departed from its design skeleton in two layout-only ways:

1. IICF lives in a flat `Iicf/` directory rather than an `Intf/`/`Impl/`
   split.
2. Verified codegen is split across seven focused `Codegen/` modules rather
   than the provisional design's smaller grouping.

Both layouts are clearer at the landed scale and change no judgments. P6
updates the stale root aggregator so the actual structure, not the old
skeleton, is the public index.

### E9 — deterministic hash maps are excluded from resolved flag 3

**Status: accepted.** The plan's resolved breadth list named hash maps.
P0 excludes their implementations because this deterministic word-RAM cost
calculus has no honest worst-case O(1) hashing theorem and no randomized
expected-cost layer. Bounded key spaces use array maps. An ordered-map/RBT
option for sparse unbounded keys is deferred to X16/P10; it is not active P5
scope.

This is a real deviation from the accepted list, not a wording cleanup.
Revisit it at P10 if a consumer needs sparse unbounded keys where the log
factor matters, or after randomized-cost infrastructure lands.

### E10 — signature conversion and FCOMP use transparent Lean frontends

**Status: accepted.** The source implements `to_hnr`, `to_hfref`, and
`FCOMP` as Isabelle theorem attributes which destruct and rebuild theorem
objects. In Lean, the landed `hfref` judgment is definitionally the whole
quantified `hnRefine` family, so P1.A exposes the conversions as transparent
theorems and `FCOMP` as the goal-directed `sepref_fcomp` tactic. The tactic
dispatches both `hfref` and generalized `hnRefine` families, the dependent
and non-dependent result shapes, and pure `fref ∘ fref`; it leaves
`attainsSup` visible as an ordinary proof obligation. A separate checked
mode applies the supported source normalization laws and rejects surviving
composition artifacts.

This is a D1 substrate rendering, not a change to the source judgments:
`compPRE`, the no-fail guard, witness-dependent result assertion, and
attained-supremum premise are unchanged. Revisit only if a later command
needs theorem-value transformation independent of a goal; P1.B's
signature-to-synthesis preparation is a separate missing layer and is not
claimed by this entry.

### E11 — signature preparation is bounded and registration reuses generic monadification

**Status: accepted.** Isabelle's `prepare_hfref_synth_tac` resolves
`hfsynth_hnr_from_hfI` through the general `Term_Synth` framework, then
discharges `hfsynth_ID_R_D` premises through `intf_of_assn`. Its
`sepref_register` generates a conceptual-typing theorem and, for a monadic
constant, one arity equation and one `mcomb` equation specialized to that
constant's argument count.

Lean's `hfref` is transparently the quantified `hnRefine` family. P1.B
therefore performs only the bounded conversion this consumer needs:
introduce the concrete argument, abstract argument, and precondition proof;
run the existing synthesis pipeline on the exposed judgment; and close the
signature consequence with the stated post/result assertions. It does not
port a general-purpose `Term_Synth` engine. `intfOfAssn` remains the
configuration database for assertion-directed operation registration, with
the source's abstract-carrier fallback and the existing `CTYPE_ANNOT` as the
per-occurrence override.

Registration emits the source's `intf_type` theorem into `id_rules`, but no
per-operator arity or `mcomb` theorem. `Monadify.flattenPass` already walks
arbitrary application spines left-to-right and is independent of arity;
generating equations would duplicate rather than configure that pass. The
compiled controls are deliberately stronger than a small equivalence test:
an eight-array signature synthesizes end to end, an eight-argument operator
identifies at eight assertion-derived `ArrayI` inputs, and the complete
three-loop BFS is regenerated byte-identically from `hfref` data.

This is a Lean-substrate substitution, not a weakened public judgment.
Revisit if a future combinator needs non-generic eta expansion, if signature
preparation must transform a non-transparent refinement judgment, or if a
consumer needs non-reflexive post/result consequence solving during
preparation.

### E12 — declaration commands use explicit Lean statements and proof terms

**Status: accepted.** Isabelle's `sepref_decl_op` parses a relation language,
analyzes its precondition/arguments/result, defines pure and optional mop
variants, and enters an after-QED callback that derives and registers the
parametricity family. `sepref_decl_impl` discovers the matching interface
fact, transforms theorem objects through FCOMP, and derives optional op/mop
variants under command flags.

Lean has no separate Isabelle relation parser or after-QED theorem-attribute
pipeline. P1.C keeps the semantic boundary explicit: `sepref_decl_op` takes
the cost-carrying operation definition, conceptual interface, precondition,
and complete `fref` statement/proof; it checks the interface against the
logical type and registers both products. `sepref_decl_impl` takes its result
statement plus raw and `fref` facts, invokes checked FCOMP itself, exposes the
honest `attainsSup` residue to the trailing proof, and registers the result.
Pure source operations are written with `NRest.returnT`, and asserted source
mops include `NRest.assert` in their declared body. The source command flags
are consequently not a second hidden derivation path.

This is a D1 frontend rendering: the public facts remain `intf_type`, `fref`,
`hfref`, and `sepref_fr_rules`, and the full interface-to-implementation gate
uses no caller-authored metaprogramming or direct FCOMP. Revisit if P5 finds a
repeated pure-to-mop wrapper worth generating, or needs a source flag whose
derived theorem cannot be expressed by the explicit command surface.

### E13 — multi-index recursion combinators expose the source's closed forms

**Status: accepted.** Sepreftime defines lexicographically recursive
`for_rec2`/`for_rec3`, introduces private closed forms `for_rec2'`/`for_rec3'`,
and proves the full square/cube calls equal two/three nested `nfoldli`s. Lean
can encode the public equations with well-founded recursion, but that would
add termination machinery which no campaign consumer observes.

P2.B therefore exposes the source's proved closed forms directly as
`forRec2`/`forRec3`, alongside the structurally recursive exact `forRec`, and
proves the same full-traversal equalities. This is a representation delta,
not a traversal or cost delta: endpoint order, inclusive range, monadic bind
order, and the one/two/three nested-fold results are unchanged. Revisit if a
consumer needs to unfold an intermediate public `for_rec2`/`for_rec3`
recursive equation rather than use the full square/cube theorem.

### E14 — scheduled debt: while flattening

**Status: accepted; assigned to P6.** Sepreftime's `flatCurrs_whileT` was not
ported in P3.A. In this repository `whileT` is defined through the guarded
greatest fixed point `RECT`; unlike the structural and bind laws, transporting
it requires a generic `RECT`/`gfp` conjugacy theorem across a complete-lattice
order isomorphism, which `Rec.lean` does not currently expose. The delivered
`flatCurrs_iSup` and exact `flatCurrs_bindT` cover the current cash-boundary
consumers, so P3.A correctly avoided an ad hoc loop proof. P6 must add the
generic theorem in `Rec.lean` that `RECT` commutes with an order
isomorphism/conjugate body, then port `flatCurrs_whileT` and add a terminating
nondeterministic-loop gate. This is fixed source debt, not consumer-triggered
scope.

### E15 — introsort keeps exact named stages but collapses later synthesized rates

**Status: accepted.** In `Sorting_Introsort.thy`, `ub_introsort5` proves
`timerefineA (introsort5_TR l h) (cost ''slice_sort'' 1) ≤ ?x`;
`introsort5_acost`, `introsort5_cost`, and `introsort_cost3` then name and
simplify that synthesized upper bound. The displayed operation vector is not
an equality exposing the internal `introsort5_TR` row. The source also later
applies `project_all`, assigning unit price to every currency in the displayed
vector, and proves the resulting scalar formula exactly.

P3.B retains both statement strengths. `operationBudget` is exactly the
source's `introsort_cost3` upper-bound formula, with the locale-parametric
comparison name still explicit. `operationUpperRate` is a finite collapsed
rate from the outer `slice_sort` token to that named upper bound; it is not
presented as the omitted chain of partition, insertion, heap, compare/swap,
and LLVM exchange matrices. `abstractPhaseRate` similarly packages exact
`introsort3_cost` in one outer row. The immediately following source stage is
not collapsed: `recursiveAccount` is exact `introsort_aux_cost`, and
`recursiveUpdateRate` is the source-shaped TId update that replaces
`slice_part_sorted` with that recursive account. The compiled
`topLevel_to_expanded` theorem rules out the tempting but incorrect hybrid
that retains the token while also adding recursive work. Theorems connect the
outer token, exact top-level stage, expanded stage, and final operation upper
bound; `introsortSpine_consumes` checks the coherent top-level stage in NREST.

The local verified IR cannot serve as the final price map: its sixteen
currencies omit source operations such as `load`, `store`, `ofs_ptr`, and
`icmp_*`. The compiled `localIRCash_drops_source_load_gate` shows that its
code-generation cash exchange prices a real source `load` charge at zero.
P3.B therefore uses the source's own finite unit projection and P3.A's
Unit-currency flattening, reproducing `4693 + 5 log n + 231 n + 455 n log n`
exactly. This is a local-machine-boundary adaptation, not a changed source
bound. Revisit if a consumer needs a later individual synthesized rate or if
the local IR grows a justified lowering for every source operation; then port the
relevant source matrices and prove their `pp` composition refines the
collapsed upper rate.

## 4. Corrections that are not deviations

These P0 discoveries change citations or scheduling without changing a
judgment:

| finding | disposition |
|---|---|
| Timed union-find exists in Sepreftime. | P4.B is unconditional rather than a conditional stretch. |
| Dynamic-table potential mathematics lives primarily in AFP `Dynamic_Tables`, not only `Amortized_Complexity`. | Both entries are pinned; the artifact dynamic array remains the currency-native primary source. |
| Dependent `hfcomp` and the unfueled loop rule landed during the ND-MC readiness wave. | They enter `debt-register.md` as closed/verify items; P1 does not re-port them. P1 still ports the surrounding signature machinery. |
| The scaling probe found the frame/entailment layer, not rule lookup, to be the wall. | P7 targets `fri`/`proveConjEq`; DiscrTree is explicitly not the first intervention. |

## 5. Ledger protocol for P1–P10

Every later wave that departs from a pinned statement or changes an
accepted entry adds an entry here before landing. The entry records:

1. the exact source statement or architecture;
2. the Lean statement/architecture chosen;
3. whether the cause is substrate, local machine boundary, or a repo
   addition;
4. a compiled refutation when the source-shaped route is claimed
   impossible;
5. the fallback or revisit trigger.

Local implementation discoveries that do not change a campaign decision
belong in module headers and `debt-register.md`, not as ledger inflation.
