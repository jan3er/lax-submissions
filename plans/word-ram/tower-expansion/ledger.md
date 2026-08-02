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

### E16 — array-list append is conditional where the source rule is unconditional

**Status: accepted; verify before P5 closes.** Sepreftime's
`Refine_Imperative_HOL/IICF/Impl/IICF_Array_List.thy` at `c1c987b` states

```
arl_append_hnr_aux:
  (uncurry arl_append, uncurry (RETURN oo op_list_append))
    ∈ (is_array_list^d *_a id_assn^k) →_a is_array_list
```

with no precondition slot (source `:177`). Append is unconditionally total
because `arl_append` (source `:30–42`) branches into
`array_grow a (2*len) default` when the physical array is full (source
`:38`), and `arl_append_rule` (source
`:87`) is a plain `sep_auto` triple over `is_array_list l a` alone. The
dynamic-array file `IICF_DArray_List.thy` has the same unconditional push.

`ArrayList.lean:415` registers `arlAppendOp_refines` not over
`arrayListRel` but over `arrayListReadyRel` (`:362`), which adds the
conjunct `boundedPush p.1 0 ≠ none`. `DArrayList.lean:193` registers
`daPushOp_refines` over `daReadyRel` (`:174`) with the identical added
conjunct. Neither relation has a source counterpart. This is the campaign's
first **weakened public guarantee**, not a representation choice: a caller
holding only `arrayListAssn`/`daAssn` can no longer conclude that append
succeeds, and physical exhaustion stays observable as `NRest.fail`
(`ArrayList.lean:376–379`) or as the exec dispatcher's `ok` flag
(`ArrayList.lean:163`).

Cause: substrate, and specifically D2. The endorsed machine's instruction
set (`word-ram/concepts/Lax13/Ram.lean:161`) and the IR command type
(`Lax13Proofs/Refine/Ir/Syntax.lean:134–155`, ten constructors: `skip`,
`const`, `copy`, `binop`, `aget`, `aset`, `seq`, `ite`, `while`) contain no
allocation instruction, so no program can produce the fresh doubled buffer
that `array_grow` returns.

**No compiled refutation exists.** Nothing in the repository proves that an
unconditional source-shaped append rule is underivable; the argument is the
architectural absence above, read off the `Com` constructor list. If this
entry is to be closed rather than carried, that refutation is what is
missing.

The neighbouring fixed-capacity family is *not* affected and must not be
lumped in: `MSArrayList.lean:237` restricts `marlReadyRel` to
`p.1.length < N`, which is exactly the source's own
`[λ((l,a),_). length a < M]` guard on `marl_push_back_impl`
(`isabelle_llvm_time` `IICF_MS_Array_List.thy:131–132`). That one is
source-faithful.

Revisit trigger: any P9/consumer use of a P5.B sequence whose append cannot
be shown to sit in the ready relation, or the arrival of an allocation
capability in the IR. Fallback if a consumer needs the unconditional rule:
carry the ready relation in the consumer's own invariant, and record that
the consumer, not the container, discharges exhaustion.

### E17 — allocation, deallocation, and pointer boundaries are demoted to pure models

**Status: accepted.** Across P5.B/C every source operation that allocates,
frees, copies into fresh storage, or exports a pointer is replaced by a pure
value model plus, where meaningful, an establishment operation over
caller-supplied storage. The pattern is uniform, so it is one entry:

| file | source construct (repo/file) | Lean disposition |
|---|---|---|
| `ArrayList.lean:96–108` | `arl_empty`, `arl_empty_sz` (Sepreftime `IICF_Array_List.thy:20–28`, `Array.new`-backed) | `arlEmptyModel`/`arlEmptySizeModel` as pure models, plus the added `arlEmptyIn`/`arlEmptySizeIn` over a caller-owned buffer; `arlEmptyOp_refines` (`:400`) and `arlEmptySizeOp_refines` (`:404`) are deliberately **not** tagged `@[sepref_fref_thms]`, and no exec rule exists |
| `ArrayList.lean:174` | `arl_copy` (source `:44–47`), whose rule yields two separately owned arrays: `< is_array_list l a > arl_copy a <λr. is_array_list l a * is_array_list l r>` (source `:84`) | `arlCopyModel s = s`. The *pure* refinement stays faithful because the abstract operation is itself identity (`Intf/List.lean:304`: `op_list_copy` is `fun xs => NRest.returnT xs`), and `arlCopyOp_refines` (`:408`) is registered; **no heap rule is claimed**, so the source's ownership-duplication content is dropped, not weakened |
| `ArrayList.lean:191–200` | source shrink (allocating) | logical-capacity reduction inside the same owned buffer; `arlShrinkCapacity` retains the source's `4·n < cap ∧ 16 ≤ 2·n` decision but never copies |
| `ArrayMapTotal.lean:60–61`, `:327` | `amt1_init` (`isabelle_llvm_time` `IICF_Array_Map_Total.thy:14`) and the derived `MK_FREE (amt_assn N V) ?fr` (source `:101`) | `amtInitIn` fills an already-owned `N`-cell array; the `MK_FREE`/pointer-export family is dropped with no zero-cost stand-in |
| `ArrayMap.lean:564–567`, `:641` | `am_assn_free`, allocation-backed `am2_empty`, LLVM export, pointer regression | `amEmpty_exec_hnr` over caller-owned arrays only |
| `ArrayMapMap.lean:17`, `:614–616` | `new_liam` (Sepreftime `IICF_ArrayMap_Map.thy`) | caller-owned array + caller-owned scalar cell initialization |
| `ArrayMatrix.lean:315–319`, `:541–543` | the general tabulator, which allocates and calls a higher-order heap callback | `amtxTabulateOp` keeps full semantics and a registered *pure* rule (`:322`) but is given **no** executable rule; `amtxDefault_exec_hnr` is the honest caller-owned fill |
| `ArrayOfArrayList.lean:242`, `:595–598` | `aal_free`; and the outer array of pointers to independently owned rows | `aal_free` unrepresented; there is no command for selecting `s.rows[i]`, and every executable rule begins after the caller has supplied the selected row's array/length/capacity cells |
| `ImplHeap.lean:19–23` | allocating heap creation and growth | empty is a semantic model with no executable rule; insertion is exposed only from the ready relation (see E16) |

Cause: substrate (D2), the same missing allocation capability cited in E16.

Two honesty notes belong with this entry rather than in the module headers:

1. `ArrayOfArrayList.lean:866–869` defines
   `aalOuterSelectionSupported : Prop := False` and proves
   `aalOuterSelection_unsupported : ¬ aalOuterSelectionSupported` by `simp`.
   This is a **marker, not a compiled refutation**: the predicate is
   definitionally `False`, so the theorem says nothing about the IR. Read as
   a refutation of outer pointer-array selection it would be circular.
2. No file emits a zero-cost placeholder for a dropped allocation operation
   (`ArrayMap.lean:641`, `ArrayMapTotal.lean:19`, `ArrayMapMap.lean:614–616`,
   `ArrayMatrix.lean:543`, `ArrayOfArrayList.lean:952`,
   `MSArrayList.lean:690`). That restraint is correct and is the reason the
   demotions are recorded as dropped content rather than as mispriced
   content.

Revisit trigger: an IR allocation/free capability, or a consumer that needs
two independently owned copies of one container (the `arl_copy` case is the
first that would break).

### E18 — correction to E7: no pinned IICF source carries cost text, and the whole P5.B/C cost layer is authored

**Status: accepted; corrects E7 and `port-map.md:210`.** E7 records that the
`isabelle_llvm_time` `sepref/IICF/` tree "almost entirely lacks cost
vocabulary" and names "Sepreftime's single-currency IICF" as a *usable
cost-carrying* container source. `port-map.md:210` calls the Sepreftime
sequence files "cost copies (8.8 / 3.1 / 8.5 / 16.9 KB)". **That premise is
false**, and P5.B/C were built on it.

Re-verified in this backfill against the pinned trees:

- Sepreftime `Refine_Imperative_HOL/IICF/Impl/IICF_Array_List.thy` @
  `c1c987b` contains **no** cost, credit, `enat`, or `acost` text at all.
  Its rules are plain `sep_auto` Hoare triples in
  Separation_Logic_Imperative_HOL (`:84`, `:87`, `:162–188`). Its only
  `$`-shaped token is the `op_arl_empty_sz$N` application at `:217`.
- The `isabelle_llvm_time` @ `42dd7f5` files
  `IICF_Array_List.thy`, `IICF_Array_Map.thy`, `IICF_Array_Map_Total.thy`,
  `IICF_Array_of_Array_List.thy`, `IICF_Indexed_Array_List.thy`,
  `IICF_MS_Array_List.thy`, `Heaps/IICF_Abs_Heap.thy`,
  `Heaps/IICF_Impl_Heap.thy`, `Heaps/IICF_Abs_Heapmap.thy` likewise match
  zero lines of `acost|timerefine|enat|cost`.
- `IICF_Abs_Heap.thy` is byte-identical between the two trees, so the
  "Sepreftime cost copy" of the heap layer is not a cost copy either.

Not re-verified in this backfill (no local checkout was available):
Sepreftime `IICF_ArrayMap_Map.thy` and `IICF_Array_Matrix.thy`. The scalar
`enat` bounds quoted in `ArrayMapMap.lean:19–22` (`n+3` empty, `6` update,
`2` membership/lookup) and `ArrayMatrix.lean:20–22` (`3*N*M+3` tabulate,
`N*M+1` default fill, `1` get/set) are **header assertions, not verified
here**. Both headers already mark them as provenance only and do not equate
them with `ECost`; `DArrayList.lean:39–50` does the same for the source's
12/23 pair, and gates it with `#guard` so it can never drift into the IR
algebra.

Consequence: **every** vector cost in P5.B/C is authored, not translated —
each `*Cost` definition, each `Com` program, each `*_exec_hnr` rule, and each
`*_exec_refines` bridge. The authored cost definitions are:

| file | authored cost definitions |
|---|---|
| `ArrayList.lean` | `arlLengthCost` `:666`, `arlIsEmptyCost` `:667`, `arlLastCost` `:669`, `arlGetCost` `:671`, `arlSetCost` `:672`, `arlButlastCost` `:674`, `arlSwapCost` `:678` |
| `DArrayList.lean` | none of its own; reuses P4's `boundedExecCost` (`:214`) |
| `MSArrayList.lean` | `marlAppendCost` `:409`, `marlButlastCost` `:412`, and five abbreviations `:415–419` |
| `IndexedArrayList.lean` | `ialSwapCost` `:975`, `ialLengthCost` `:980`, `ialIndexCost` `:981`, `ialButlastCost` `:982`, `ialAppendCost` `:985`, `ialGetCost` `:989`, `ialContainsCost` `:990` |
| `ArrayOfArrayList.lean` | five row abbreviations `:599–603`, `aalRowPopCost` `:624`, `aalRowTakeCost` `:660` |
| `ArrayMap.lean` | `amEmptyCost` `:329`, `amLookupCost` `:331`, `amContainsCost` `:333`, `amUpdateCost` `:334`, `amDeleteCost` `:336` |
| `ArrayMapTotal.lean` | `amtInitCost` `:217`, `amtLookupCost` `:218`, `amtUpdateCost` `:219` |
| `ArrayMapMap.lean` | `ammPackCost` `:340`, `ammEmptyCost` `:343`, `ammContainsCost` `:346`, `ammLookupCost` `:348`, `ammUpdateCost` `:351` |
| `ArrayMatrix.lean` | `amtxDefaultCost` `:386`, `amtxGetCost` `:389`, `amtxSetCost` `:392` |
| `AbsHeap.lean`, `AbsHeapmap.lean` | none — see E20 |
| `ImplHeap.lean` | `implHeapUpdateCost` `:262`, `implHeapValueCost` `:265`, `implHeapExchangeCost` `:268`, `implHeapValidCost` `:271`, `implHeapSwimCost` `:490`, `implHeapSinkCost` `:501`, `implHeapInsertCost?` `:1077`, `implHeapPopMinCost` `:1092` |

A second, structural consequence follows and is recorded here rather than
inflating a further entry. Because the P5.A interface operations are
cost-silent, a positive-cost IR program cannot refine them at the same
`NRest` type (`ArrayList.lean:531–534`). P5.B/C therefore replace the
source's single `sepref_decl_impl` conclusion — one `hfref` fact linking the
abstract operation to the implementation — with **two surfaces plus a
bridge**: a cost-silent `fref` at the value level, an exact-budget
`hnRefine` at the IR level, and `*_exec_refines` lemmas connecting the two.
That is a departure from the source's rule shape, not only from its cost
text. It also means no single landed fact says "this command implements this
list operation at this price".

Cause: repo addition on top of a substrate boundary. This is E7's own
"derivation, following the `CombRules.lean` precedent" discipline applied at
scale; what E7 got wrong is only the claim that a cost-carrying source
existed to derive *from*.

Do not rewrite E7. Its scheduling conclusion (P5 ports the interface table
and derives vector costs) survives; only its source-availability premise is
withdrawn here. `port-map.md:210`'s "cost copies" wording should be read as
size evidence, exactly as E7's own last sentence already instructs.

Revisit trigger: if a currency-native container source is later located in
any pinned tree, re-derive the affected `*Cost` definitions against it
before any consumer depends on the authored numbers.

### E19 — monomorphization and representation substitution in the map and matrix families

**Status: accepted.** Three source representations have no faithful image in
a natural-number-array IR, and were substituted rather than dropped:

1. **`ArrayMapTotal` value type.** The source is
   `amt1_init :: nat ⇒ 'a::llvm_rep amt1 nres`,
   `amt1_init N ≡ RETURN (replicate N init)`
   (`isabelle_llvm_time` `IICF_Array_Map_Total.thy:14`), polymorphic over any
   LLVM-representable element with that type's own `init`. `ArrayMapTotal.lean:28`
   fixes the concrete carrier to `List ℕ` and the abstract map to
   `ℕ → Option ℕ`, and `:58` fixes the fill value to `0`
   (`amtInitModel N = List.replicate N 0`). Genericity is recovered one level
   up: `amtRel` (`:36`) and `amtAssn` (`:45`) compose through
   `mapRel (Set.diagonal ℕ) (thePure A)`, reproducing the source's double
   composition, and `amtAssn_comp` (`:52`) proves the two associations agree.
   The source relation's non-single-valuedness is *preserved*, not
   introduced: source `amt1_rel` (`:12`) constrains only present keys, and
   `amt1Rel` (`:28`) does the same. The header's "intentionally not
   single-valued" is therefore source-faithful and is not a deviation.
2. **`ArrayMap`/`ArrayMapMap` absence encoding.** The source owns one array
   of `'a option`. No natural can serve as an absent-value sentinel, so
   `ArrayMap.lean:25–32` uses two caller-owned arrays of equal length — a
   canonical 0/1 `present` array with a well-formedness constraint plus an
   unrestricted `values` array — and `amConcrete` (`:34`) reads them as the
   source's option array. `ArrayMapMap.lean:30–34` extends that with the
   source `is_liam`'s third owned cell holding `card (dom M)`, proved equal
   to `(ammDomain N m).card` (`:45`).
3. **`ImplHeap` instantiation.** The generic Sepreftime locale is kept only
   at its executable specialization — natural elements, identity priority,
   array-list carrier (`ImplHeap.lean:12–17`, `:33`). The generic locale
   parameters are not exposed.

Cause: substrate for (1) and (2) (the IR's only aggregate is a
natural-number array); local machine boundary for (3), following the
executable source's own global instantiation.

No compiled refutation is claimed for any of the three, and none is needed:
each is a representation change with the composition theorems proved
(`amtAssn_comp`, `amConcrete`, `amm1Rel`). Revisit if a consumer needs a
non-`ℕ` element type at the *concrete* layer rather than through `thePure`,
or a heap over a non-identity priority.

### E20 — abstract heap layers are cost-free, and `ImplHeap`'s loop layer proves less than its names suggest

**Status: accepted for the abstract layers; OPEN for `ImplHeap`.**

`AbsHeap.lean:11` and `AbsHeapmap.lean:11–12` declare themselves semantic
layers with no IR commands, heap assertions, allocation rules, or vector
costs. That is confirmed: neither file defines any `*Cost` or any
`hnRefine`, and every operation is a bare `NRest.returnT` or an `assert`-
guarded `returnT`, i.e. priced at zero (`AbsHeap.lean:1312–1332`,
`AbsHeapmap.lean:1193–1253`). The corresponding sources also carry no cost
text (E18), so the *shape* is faithful; the campaign-relevant fact is that
these two layers contribute nothing to any currency vector, and the
`Impl_Heapmap` layer that would price the heapmap operations is still
unported. Any consumer composing `hm*Op` today gets a free priority map.
`AbsHeap` is at least closed by `ImplHeap`. Also recorded per D1:
`AbsHeap.lean:12–16` replaces the source's `RECT` swim and optimized-sink
programs with explicit fuel-bounded structural recursion whose public
wrappers supply fuel from the one-based position/list length, and
`:18–20` adds the `[Inhabited α]` needed to keep source `val_of` total
outside its validity precondition.

`ImplHeap.lean` is the weaker case and the reason this entry stays open:

- `implHeapSwimLoopInv` (`:571`) and `implHeapSinkLoopInv` (`:781`) are both
  `fun _ => True`. The `irWhileIT` rules are therefore instantiated with
  vacuous invariants and carry no heap property across the loop.
- The executable specifications are, by the file's own statement
  (`:561–566`), the `irWhileIT` programs themselves. So
  `implHeapSwim_exec_hnr` (`:758`) and `implHeapSink_exec_hnr` (`:1017`)
  prove that a command refines its own denotation at its own price. The
  closed forms `implHeapSwimCost` (`:490`) and `implHeapSinkCost` (`:501`)
  are not connected to them.
- Grepping the file finds **no theorem relating `implHeapSwimExecSpec`
  (`:725`) or `implHeapSinkExecSpec` (`:987`) to the abstract
  `implHeapSwim` (`:88`) or `implHeapPopMin?` (`:100`).** The value-level
  facts (`implHeapPopMinOp_refines` `:1389`) and the IR-level facts
  (`implHeapPopMin_exec_hnr` `:1202`) exist side by side with nothing
  joining them — the E18 bridge is present for the array families and
  absent here.

The file's header does not overclaim, and the `:562–566` comment explicitly
refuses to substitute the closed forms for an unproved loop theorem. The
deviation is that the heap's executable layer, unlike every other P5.B/C
family, currently delivers no semantic content at the IR level.

Cause: repo gap, not substrate. A source-shaped route exists: a real loop
invariant plus a swim/sink execution theorem. No compiled refutation is
claimed and none would be honest.

**RESOLVED 2026-08-02 — and the first bullet above was wrong.**

*Correction: `True` was the correct invariant, not a vacuous shortcut.* An
`irWhileIT` invariant is an assertion *inside the abstract program*:
`irWhileIT_of_not_inv` (`Sepref/IrOps.lean:234`) gives
`¬ I s → irWhileIT I bf f s = NRest.fail`, and `fail` is the top of `NRest`.
Since `hnRefine` requires `program ≤ spec`, strengthening `I` enlarges the
spec and makes every rule below it **strictly weaker**. Populating
`implHeapSwimLoopInv`/`implHeapSinkLoopInv` would therefore have weakened
`implHeapSwim_exec_hnr`, `implHeapSink_exec_hnr`, `implHeapInsert_exec_hnr`
and `implHeapPopMin_exec_hnr`. The supervisor's original defect report
(and the first bullet above) mistook the strongest available choice for a
weakening. The loops' real invariants (`parent = idx / 2` plus index bounds
for swim, `idx ≤ len / 2` for sink) belong where they now are: as
hypotheses of the seam theorems, where they cost nothing and prove more.

*The actual deviation — the missing seam — is closed.* Six theorems, all
**equations rather than bounds**: `implHeapSwimLoopSpec_run` (`:1227`),
`implHeapSwimExecSpec_run` (`:1306`), `implHeapSinkLoopSpec_run` (`:1501`),
`implHeapSinkExecSpec_run` (`:1637`), `implHeapInsertExecSpec_run`
(`:1745`), `implHeapPopMinExecSpec_run` (`:1796`). By induction on the
abstract fuel, the synthesized loops equal the `heapSwimFuel`/`heapSinkFuel`
motions of `AbsHeap` on the active prefix, leave the inactive suffix
untouched, terminate, and cost exactly `implHeapSwimCost`/`implHeapSinkCost`.
The E18 bridge that was present for the array families and absent here now
exists. Axioms for all six: `[propext, Classical.choice, Quot.sound]`.

*Defect found during the repair:* `implHeapSwimCost` (`:490`) and
`implHeapSinkCost` (`:501`) were **wrong** — both omitted the `ir.skip`
units the loop bodies' `mopPair`s pay (2 per iteration for swim, 1 for
sink). Nothing referenced them, so correcting them weakened nothing, and
every previously pinned currency count is unchanged. This is a direct
instance of F11: a cost function that no theorem consumed was also a cost
function that nobody had checked.

*Forward-compatibility with P4.5/P5.E:* the insert precondition is isolated
as `implHeapInsertPre` with `implHeapInsertPre_of_readyRel`, so no seam
statement mentions `boundedPush` or `arrayListReadyRel`; P5.E discharges one
hypothesis rather than restating theorems. `implHeapPopMinExecSpec_run`
takes only `s.Wf` and `s.length ≠ 0`. Pop's statement is honestly weaker on
one point: the exec spec's physical buffer differs from `implHeapPopMin?`'s
in the single discarded slot, so it asserts `bufOut.take u.length = u.active`
plus exact metadata rather than full buffer equality.

*Gate:* `lake build` 3,275 jobs green; `lax build` violation count unchanged
at 2 (both the pre-existing `GetElem?.match_1.splitter`); no `sorry`,
`admit`, `native_decide`, or new axiom. Independently replayed by the
supervisor, not taken from the worker's report.

### E21 — five global attribute mutations are never restored

**Status: accepted; assigned to P6.** `Intf/ListList.lean:74`+`:79` shows
the correct pattern: `attribute [-intf_of_rel] listRel_intf`, the local
declaration that needs the hole, then `attribute [intf_of_rel] listRel_intf`
restoring the database. The P5.B/C implementation leaves do not pair their
mutations:

| site | mutation | restored? |
|---|---|---|
| `ArrayList.lean:571` | `attribute [irreducible] arlPred` | no |
| `ArrayList.lean:643` | `attribute [irreducible] arlSelectCap` | no |
| `MSArrayList.lean:402` | `attribute [irreducible] marlPred` | no |
| `ArrayMapMap.lean:306` | `attribute [irreducible] ammZeroCount` | no |
| `ImplHeap.lean:1113` | `attribute [-sepref_fr_rules] arlAppend_exec_hnr` | no |

Each `irreducible` is set immediately after the corresponding
`@[sepref_fr_rules]` rule (`ArrayList.lean:565`, `:595`,
`MSArrayList.lean:395`, `ArrayMapMap.lean:297`) so that synthesis matches
the wrapper rather than unfolding it. Since the attribute is global and
never reverted, every downstream cost computation must re-open the
definition by hand. Verified workaround sites:

- `marlPred` leaks out of `MSArrayList` into `IndexedArrayList.lean:952` and
  `ArrayOfArrayList.lean:619`, forcing `simp [… marlPred …]` at
  `IndexedArrayList.lean:1068` and `ArrayOfArrayList.lean:637`;
- `arlPred`/`arlSelectCap` force the same at `ArrayList.lean:745`, `:754`,
  `:761`;
- `ammZeroCount` forces it at `ArrayMapMap.lean:380`.

`ImplHeap.lean:1113` is different in kind — it erases a rule from the global
`sepref_fr_rules` label set (`Refine/Sepref/Attrs.lean:50`) so that
`implHeapAppendRaw_exec_hnr` (`:1115`) can take its place, and never
restores it. Note for the P6 owner: `ArrayList.lean:163` declares
`arlAppend_exec_hnr` **without** `@[sepref_fr_rules]`, and no other file in
the tree registers it, so which registration this erasure cancels could not
be determined from the source text in this backfill. The mutation is global
and unrestored either way.

Cause: repo addition (a synthesis-control convenience), not substrate. No
compiled refutation is relevant; the paired pattern demonstrably works one
directory over.

Revisit: P6 restores each mutation at the end of its owning section
(`attribute [semireducible]`, respectively re-adding the label) and deletes
the `simp` workarounds it makes unnecessary. Do this before any further
consumer imports these files, since the leak grows with each importer.

## 4. Corrections that are not deviations

These P0 discoveries change citations or scheduling without changing a
judgment:

| finding | disposition |
|---|---|
| Timed union-find exists in Sepreftime. | P4.B is unconditional rather than a conditional stretch. |
| Dynamic-table potential mathematics lives primarily in AFP `Dynamic_Tables`, not only `Amortized_Complexity`. | Both entries are pinned; the artifact dynamic array remains the currency-native primary source. |
| Dependent `hfcomp` and the unfueled loop rule landed during the ND-MC readiness wave. | They enter `debt-register.md` as closed/verify items; P1 does not re-port them. P1 still ports the surrounding signature machinery. |
| The scaling probe found the frame/entailment layer, not rule lookup, to be the wall. | P7 targets `fri`/`proveConjEq`; DiscrTree is explicitly not the first intervention. |
| **2026-08-02.** The plan's P4.5 source table calls `FREE_eoarray_assn` "one `sorry`" in `Hnr_Primitives_Experiment.thy`. It is inside a comment block (`:316–326`) and the file has no live `sorry`; the author's note says the rule **does not hold**. | Declining to state a false theorem is not a deviation. The frame-rule half leaves the ledger; the decision to exclude deallocation *itself* moves to **E23**, which argues it on our own terms. The plan's source table and X17(c) are amended to cite E23. |
| **2026-08-02.** The plan glosses our O(1) allocation as avoiding the source's fill loop. The source has no fill loop — `narrayo_new` never writes contents, and `lo_init` is why that is sound. | The conclusion (O(1) here, O(n) there) stands; the reason is the `malloc` currency versus a pre-existing zeroed address space. Recorded precisely in **E24** and in `p4.5-design.md` §2, so no worker looks for a loop that is not there. |

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

**Backfill note, 2026-08-02.** Entries E16–E21 were written *after* the work
they describe had landed, and that is a process failure against the rule
stated at the top of this section. Between E15 (2026-07-31 21:04) and this
note, all twelve P5.B/P5.C implementation leaves landed —
`ArrayList`, `DArrayList`, `MSArrayList`, `IndexedArrayList`,
`ArrayOfArrayList`, `ArrayMap`, `ArrayMapTotal`, `ArrayMapMap`,
`ArrayMatrix`, `AbsHeap`, `ImplHeap`, `AbsHeapmap` — and not one added an
entry here. Their deviations were recorded only in the module headers, which
made them invisible at campaign level; E18's correction to E7 in particular
would have been caught before eight files were built on the withdrawn
premise, and E16's weakened append rule should never have landed without an
entry. E16–E21 are transcriptions from those headers, verified against the
cited `file:line` and, where a pinned checkout was reachable, against the
source text; claims that could not be re-verified are marked as such inside
the entries. The rule is unchanged: the entry precedes the landing.

### E22 — the synthesized heap commands are not the source's command shapes

**Status: accepted (rule-5 class 2 — same guarantees, different internals).**
Added 2026-08-02 during the E20 repair.

`ImplHeap.lean:583,600` record the source's `swim_impl` and `sink_impl`
program shapes as `implHeapSwimSourceCom` / `implHeapSinkSourceCom`. F11
listed them as recorded-but-unchecked fidelity data and scheduled the
obvious repair: prove the synthesized command equals the recorded shape.

**That equality is false.** The synthesized `implHeapSwimCom` /
`implHeapSinkCom` diverge from the source shapes in three places:

1. swim advances `(idx, parent)` by two divisions where the source uses
   `copy` followed by `div`;
2. swim exits by `parent := parent * 0` where the source uses
   `parent := 0`;
3. sink advances and exits by `idx := idx * 0 + _` where the source uses a
   `copy` (sink also permutes register names).

These are artifacts of what the synthesis tool emits for the corresponding
monadic combinators, not decisions taken in this file.

Cause: repo tooling, not substrate and not a source misreading.

*What replaces the equality.* Syntactic identity with the source program is
not the property that matters; computing the source's motions at an honest
price is. E20's `implHeapSwimLoopSpec_run` / `implHeapSinkLoopSpec_run`
prove exactly that — the synthesized loops equal `AbsHeap`'s own
`heapSwimFuel` / `heapSinkFuel` motions — which is why the three
divergences are semantic no-ops. This is a stronger statement than the
syntactic equality F11 asked for.

*Guard.* Both `SourceCom` definitions are retained as data and the
**disequality** is machine-checked (`ImplHeap.lean:2244,2247`), so no
future edit can silently reintroduce an equality claim. The three
divergences are documented at `:551–552` and in the header above
`implHeapSwimSourceCom`.

*Revisit trigger.* If P7 changes what the synthesis tool emits for these
combinators, re-check whether the divergences narrow; the disequality
`#guard`s will fail loudly if they close entirely, which is the desired
signal rather than a regression.

### E23 — deallocation is excluded by our decision, not by a source gap

**Status: accepted (rule-5 class 3 — a capability we decline to provide).**
Added 2026-08-02, opening P4.5. **Supersedes the stated basis of X17(c) and
of the plan's P4.5 exclusion sentence.**

*What the plan said.* Rev 5 recorded that deallocation is excluded "with the
source's own evidence: the artifact's `MK_FREE` rule for `eoarray_assn` is
its single `sorry`."

*What the source actually says.* `Hnr_Primitives_Experiment.thy` carries **no
live `sorry`**. The `FREE_eoarray_assn` attempt at `:318–325` sits inside a
comment block opened at `:316` and closed at `:326`, headed by the author's
own verdict: *"This rule does not hold! The elements must be de-allocated
first! for explicit ownership management, free the array manually using
`mop_oarray_free`!"* And `mop_oarray_free` itself (`:328`) **is** ported-ready
and proved (`hnr_eoarray_free`, `:330–340`) under the precondition
`set xs ⊆ {None}`.

*Consequences, in both directions.*

1. The excluded `MK_FREE (eoarray_assn A)` frame rule is not a deferred
   obligation; it is **false**, and for a reason intrinsic to explicit
   ownership — an automatic frame-level free would discard element ownership
   the array does not hold. Declining to state a false theorem is not a
   deviation, so this half leaves the ledger entirely and is recorded in §4.
2. Excluding *deallocation itself* is therefore **our** decision and needs
   our own argument, which is: a non-reusing bump allocator is precisely what
   buys E24's O(1) allocation, and free plus O(1)-because-never-reused are
   the same trade taken once. Adding `free` without reuse would be free
   capability with no benefit; adding it *with* reuse forfeits E24 and every
   downstream cost claim that rests on it.

*Consequence stated plainly, as rule 4 requires:* **peak memory equals total
allocation.** Every structure built on this substrate holds its address range
for the life of the program. Combined with E24's global exhaustion side
condition, a program's total allocation across its whole run must fit in
`2 ^ w`.

*Revisit trigger.* A consumer whose live set is small but whose total
allocation over time is not — the shape where reuse actually pays. At that
point the correct move is a second allocator with its own cost story, not a
`free` bolted onto this one: E24's O(1) must not be quietly inherited by an
allocator that can return a touched cell.

### E24 — `alloc n` is O(1) here and O(n) in the source, because the substrates differ

**Status: accepted (rule-5 class 1 — strictly stronger guarantee).**
Added 2026-08-02, opening P4.5.A.

*Source.* `Hnr_Primitives_Experiment.thy:202`

```
cost'_narray_new n = cost ''malloc'' n + cost ''free'' 1 + cost ''if'' 1
                   + cost ''if'' 1 + cost ''icmp_eq'' 1 + cost ''ptrcmp_eq'' 1
```

*Ours.* A constant currency vector, independent of `n`.

*Cause: substrate.* Not optimisation, and the distinction is load-bearing
enough that the plan's own gloss is corrected here. The source's `n` is **not
an initialisation loop** — `narrayo_new` is `narray_new`
(`Proto_EOArray.thy:147`), which is a null-check plus a raw `array_new`
(`LLVM_DS_NArray.thy:14–15`) and never writes the contents. It is sound to
hand back garbage because `lo_init` (`Proto_EOArray.thy:114`) makes an
all-`None` EO array own **no** element memory for *any* concrete contents.
The `n` is charged to the `malloc` currency because a real LLVM `malloc` is
honestly modelled as costing proportionally to the block it returns. On
`Lax13/Ram.lean` there is no `malloc`: `2 ^ w` cells already exist and
already hold zero, so allocation is reading a pointer cell, adding `n`, and
writing it back. We are not performing the source's work faster; we are on a
machine where that work does not exist.

*The five trailing constants* (`free 1`, two `if`s, `icmp_eq`, `ptrcmp_eq`)
are the source's null-check, its `llc_if`, and the deallocation it prepays
through `narray_assn` (`LLVM_DS_NArray.thy:10`). Under E23 we do not
deallocate, so the prepaid half has no counterpart; the branch half has one
only if our allocator branches. Our constant is ours, and the correspondence
is *shape* (constant overhead at allocation), not term-by-term.

*Preconditions this bound rests on — both proved, neither assumed.*

- **No reuse.** Fresh cells are zero only because the allocator never returns
  a cell twice. Stated and enforced as an invariant, not a comment. If reuse
  is ever added, this entry is void and every consumer cost claim resting on
  it reverts to an O(n)-init story.
- **Global exhaustion.** Total allocation ≤ `2 ^ w`, stated **once at program
  level**, mirroring the source's standing "given `malloc` succeeds". Rule 5
  forbids pushing it onto individual operations; that push is exactly what
  produced the conditional `append` (E16) that P5.E exists to remove.

*Why this is class 1 rather than a weakening.* The source's guarantee is
"allocation yields an all-`None` EO array at cost `cost'_narray_new n`". Ours
is the same postcondition at a strictly smaller cost under a side condition
the source also carries. Nothing about the *interface* changes — which is
what rule 5 protects.

*Compiled controls (falsification clause 2 — this is authored, not mirrored).*
Negative controls must compile: an allocator that could return an already-
handed-out cell must be refutable, and the claim that fresh memory reads zero
must fail if the no-reuse invariant is dropped.

*Revisit trigger.* E23's, plus: if D3 codegen shows the pointer-cell update
costs more than a constant on some path, the constant changes but the class
does not.

### E25 — P4.5.A is range ownership, not an allocator

**Status: accepted (re-scope of an accepted phase, taken under the standing
autonomy grant).** Added 2026-08-02, before any P4.5.A work was assigned.
Full argument and the rejected alternative: `p4.5-design.md` §4.

*What the plan directs.* "Render `mop_oarray_new` as an IR operation … reserve
a heap-pointer cell, allocate by reading and advancing it", and *prove* two
consequences: that `alloc n` is O(1), and that exhaustion is a global side
condition stated once at program level.

*Why that is the wrong target.* Both consequences are already properties of
the landed substrate, and the thing that actually blocks the phase's own
acceptance test is a third thing the plan does not name.

1. **O(1) is already the architecture's premise.** `Imp.lean:305-313`'s
   docstring: "an array costs nothing, since the machine's memory starts
   zeroed, and the lengths exist only to make an out-of-range access stuck."
2. **Sizing is already per-input.** `Cash.lean:385-405` quantifies the array
   lengths existentially per input, for exactly the reason E24 needs: "an
   algorithm sizes its arrays by what it reads".
3. **The global exhaustion condition already exists**, stated once and only
   once, as `Layout.FitsWords (B x) w` (`Compile.lean:76,85`), consumed
   solely by `computesInTime_of_spec`. Authoring a second one would be the
   rule-5 violation the phase exists to remove.
4. **The real blocker is `Tsa`.** `Cells γ := String → Tsa γ` with
   `a ## b ↔ a = 0 ∨ b = 0` (`Assn.lean:450-469,676`) makes an array **name**
   owned all-or-nothing. Source `push` is unconditional because the source
   *reallocates*; reallocation needs unboundedly many independently-ownable
   regions; `Layout.arrays` is a static list, so regions cannot be names; so
   regions must be sub-ranges of one array. That is `ll_range`, which judgment
   call D-m (`Assn.lean:72-83`) deliberately declined on the ground that "P5's
   lowering never needs a sub-range". P4.5 is where that stops being true.

*Chosen architecture.* One reserved array name carrying a second, per-index
view: `AState` gains `ℕ → Tsa Val`, `acells` sends the heap name to
`Tsa.zero`, and `p ↦ₕ xs` owns `[p, p + xs.length)` and splits at any point.
Name-partitioning the two views is a **soundness** requirement, not hygiene —
a name ownable in both views would make framing a range across a whole-name
`aset` unsound.

*Cause: local machine boundary.* Our arrays are named objects and the source's
are address ranges; P4.5 is the first consumer that needs the source's
granularity, so the boundary moves here rather than being worked around a
thirteenth time.

*Consequences that shrink the phase, recorded so the budget is not
re-spent.* No new `Ir.Com` constructor is required — a heap access is
`aget`/`aset` on the heap name at a computed index. So the sixteen currencies,
`Currency.all`, `embed`, `weight`/`cash`, `BigStepB`, `bpre`/`bwp` and
`embed_sim` are **inherited unchanged**, and binding **D3 is discharged by
inheritance rather than extended**. The allocator itself becomes
`p := hp; hp := hp + n` — two existing constructors, cost two `irUnit`s.

*Falsification (clause 2 — authored, no source counterpart).* The split/join
algebra needs compiled negative controls: overlapping ranges must not be
simultaneously ownable, and the heap name must not be ownable in the
whole-name view.

*Revisit trigger.* If A.1 cannot preserve every landed `ptoArr` interface
lemma, stop and re-decide rather than weakening them — twelve structures rest
on them, and a weakened array assertion is the F11 failure mode (a guarantee
nobody re-checked) at carrier level.

### E26 — the assertion carrier now has a heap component

**Status: accepted (E25's architecture, landed).** Added 2026-08-02 as P4.5.A.1
landed. Design detail: `p4.5-design.md` §4.3.

`AState` is widened in place from `(Cells Val × Cells (List Val)) × ECost` to
`(Cells Val × Cells (List Val) × HCells) × ECost`, with
`HCells := ℕ → Tsa Val`, `hcells s i := Tsa.ofOption ((s.arrs heapName).bind
(·[i]?))`, and

```lean
acells s a = if a = heapName then 0 else Tsa.ofOption (s.arrs a)
```

`ptoH p xs` owns `[p, p + xs.length)` and splits and rejoins as an equation
(`ptoH_append`, `ptoH_focus`, `ptoH_extract`, `ptoH_nil`).

*Why the `acells` partition is soundness and not hygiene.* The same
`s.arrs heapName` is visible through two views. If the heap name were ownable
in both, framing a range assertion across a whole-name `aset` on it would be
unsound, because the two views are not disjoint in the underlying state.
Zeroing the heap name in `acells` makes the whole-name view of it unownable,
which restores disjointness. A pleasant consequence, and the reason no landed
lemma needed a side condition: `ptoArr_arrs` and friends are **vacuous** at
the heap name — their hypothesis `Ar a = .triv xs` cannot hold there — so they
are preserved *verbatim*, statement byte-identical, rather than guarded.
Machine-checked by `not_irSTATE_ptoArr_heapName`, over a gate state that
deliberately *has* a heap array, so the control is about the partition and not
about absence.

*What did not change, and why that is the point.* No `Ir.Com` constructor, no
currency, no `Currency.all` entry: a heap access is `aget`/`aset` on the heap
name at a computed index. `Syntax.lean`, `Semantics.lean` and the whole of
`Codegen/` are untouched at this boundary, so `embed`, `weight`/`cash`,
`BigStepB`, `bpre`/`bwp` and `embed_sim` carry over unchanged and **binding D3
is discharged by inheritance**. Verified by diff, not asserted.

*Cost of the widening.* Fifteen sites in ten files spell an `AState` literally
and needed one tuple component added; none needed a proof change, and none is
in `Refine/Iicf/Impl/` — all fifteen are probe or example scaffolding. The
twelve landed structures have an empty diff.

*Two routes rejected, both recorded in the design note* — the mangled-scalar-
name view (**unsound**: it makes `ptoVar_setVar` false) and a separate
`HState` abstraction (**forks the logic**: `hnRefine` is over `irSTATE`, so
nothing built on it could ever be `sepref_synth`-reachable).

*Revisit trigger.* If a consumer ever needs more than one heap, `heapName`
becomes a parameter and `HCells` becomes `String → ℕ → Tsa Val`. The algebra
above is unaffected; only the partition predicate widens.

### E27 — the allocator is unconditional because availability is a resource

**Status: accepted (E25's A.2, landed).** Added 2026-08-02.

```lean
def avail (hp k : ℕ) : Assn := (hpName ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate k 0)
def allocCost (_n : ℕ) : ECost := irUnit Currency.copy + irUnit Currency.add
def allocProg (pc nc : String) : Com :=
  (Com.copy pc hpName).seq (Com.binop Imp.Bop.add hpName hpName nc)

@[sepref_fr_rules]
theorem hnr_mop_alloc (pc nc : String) (hp n k : ℕ) :
  hnRefine (junkCell pc ∗ avail hp (n + k) ∗ hnCtxt natAssn n nc) (allocProg pc nc)
    (avail (hp + n) k ∗ hnCtxt natAssn n nc) pc heapBlockAssn (mopAlloc n)
```

*The design point.* Ownership cannot be conjured, so the allocator must own
what it hands out. The naive arrangement is a precondition `hp + n ≤ limit`,
which would re-create per-operation conditionality and defeat the phase.
Instead the unallocated space is a **resource in an assertion**, exactly as
credits are: `avail hp (n + k)` for arbitrary leftover `k` is a decomposition
of what the caller already owns, not an inequality the operation imposes.
`mopAlloc` carries no `assert`, matching the source's `hnr_eoarray_new'`,
which has no precondition either. The distinction — the operation *costs*
something rather than *requires* something — is the one rule 5 turns on.

*Consequences that are theorems rather than assertions.*

- **No reuse follows from linearity.** Handing out `[hp, hp+n)` removes it from
  the availability resource, so it cannot be handed out twice
  (`alloc_no_reuse`, `avail_owns_nothing_below`, `alloc_succ_disj`). E24
  demanded this as an enforced invariant; it is better than that — it is a
  consequence of the split law, with nothing to enforce.
- **Zero contents come from the machine, once.** `avail_of_entry` reads the
  resource off an entry state of `Imp.initEnv`'s shape, discharged once rather
  than per call.
- **Cost is an equation and `n`-free** (`allocCost_const`). Because it is
  proved as an exact `irTriple`, the figure is pinned by the kernel rather
  than asserted — over- or under-charging fails the proof.

*Reachability, checked not assumed.* `sepref_synth` was driven at a hole and
emitted `allocProg "p" "n"` from the registered rule, pinned by `#guard`. This
is the criterion A.1's first attempt failed and it is now a standing gate.

*No second exhaustion condition was authored.* `Layout.FitsWords` remains the
only one. The relation between the availability size and `Layout.span` is
recorded **in prose**, and the file does not import `Compile` — a refinement
rule has no business seeing which layout a program compiles under. A first
draft stated that relation as two lemmas whose statements mentioned neither
`avail` nor anything else in the file (`m ≤ B → m ≤ L.span B`, true of any
`m`); they were deleted as decoration of the F11 kind. `debt-register.md`
SEP-16 records the prose-only status, the deletion, and the closure test at
the `Codegen/` boundary.
