# Tower expansion P0 — port map and pins

Status: **LANDED 2026-07-31** (P0 deliverable of
`plans/word-ram/tower-expansion-plan.md`; authored under the full-autonomy
grant). This document is the enumeration the plan demanded: the existing
69-file `Refine/` port diffed against the pinned sources' theory graphs,
every unported item assigned a wave or an argued exclusion (rule 4:
exclusions carry the burden). Companion files in this directory:
`ledger.md` (the campaign's deviation ledger, opened here) and
`debt-register.md` (the fine-grained open-debt list that feeds P6).

Method: three surveys run 2026-07-31 — (a) local inventory of
`word-ram/proofs/Lax13Proofs/Refine/` with per-file source attributions
and every skip/deferral recorded in the tower campaign's progress log,
`p8-verdict.md`, and the ND-MC rebase records; (b) the full tree of
`isabelle_llvm_time` @ 42dd7f5 including its session ROOT and the
authors' own `thys.txt` manifest (build-closure verified — see finding
F1); (c) theory listings of the AFP entries and satellite repos below.
Sizes are source-file KB unless marked as Lean lines.

## 1. Pins

Carried unchanged from `refinement-tower/design.md` §1:

| source | pin | canonical for |
|---|---|---|
| `isabelle_llvm_time` (Haslbeck–Lammich, ESOP'21) | github.com/lammich/isabelle_llvm_time @ **42dd7f59998d76047bb4b6bce76d8f67b53a08b6** | everything cost-carrying: `acost`, NREST-with-currencies, `timerefine`, cost `hn_refine`, Sepref-with-cost, the sorting suite, the amortized dynamic array |
| `isabelle_llvm` branch 2023 | github.com/lammich/isabelle_llvm @ **b44b6391ac00d8268e04dba4627a22d599e24dd6** | mature no-cost concrete-layer and IICF shapes |
| AFP `Refine_Monadic`, `Automatic_Refinement`, `Refine_Imperative_HOL`, `NREST` | AFP for Isabelle2025-2 (release 2026-02-06) | maintained no-cost originals; rule organization; the Sepref guides as manuals |

New pins (this campaign; the plan's P0 mandate):

| source | pin | canonical for |
|---|---|---|
| **`maxhaslbeck/Sepreftime`** (ITP'19 "Refinement with Time" artifact) — *discovered in P0, see F3* | github.com/maxhaslbeck/Sepreftime @ **c1c987b45ec886d289ba215768182ac87b82f20d** (branch `main`) | the case-study suite the ESOP artifact lacks: Kruskal (+`MinWeightBasis`), Edmonds–Karp + `Augmenting_Path_BFS`, **`Union_Find_Time`**, Floyd–Warshall + `Recursion_Combinators`; a *cost-carrying* IICF over SepLogicTime; `moreCurr/` (`Flatten_Currencies`, `MoreCurrAutomation`). Costs there are single-currency `enat` — adaptations to `acost` are ledgered (E6) |
| **`bzhan/Imperative_HOL_Time`** (Zhan–Haslbeck, IJCAR'18 SepLogicTime) | github.com/bzhan/Imperative_HOL_Time @ **09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec** (branch `master`) | time credits in SL assertions (`SLTC`), the amortized exemplars (`IHT_Dynamic_Array_More`, `IHT_Skew_Heap`), the `Asymptotics_1D/2D/Recurrences` closure layer. Note: **no union-find case study here** — that lives in Sepreftime |
| AFP `Collections` (ICF, Lammich–Lochbihler) | AFP Isabelle2025-2 | iterator discipline (`Iterator/`), interface breadth as reference; the locale framework itself is excluded (X4) |
| AFP `Amortized_Complexity` (Nipkow et al.) + AFP `Dynamic_Tables` | AFP Isabelle2025-2 | potential-function math for the P4 exemplars (the full dynamic-table analysis is in `Dynamic_Tables`, not `Amortized_Complexity` — P0 correction) |
| AFP `Landau_Symbols`, `Akra_Bazzi` (Eberl) | AFP Isabelle2025-2 | asymptotic-face and recurrence-closure *patterns*; mathlib `Asymptotics` remains the carrier (ledger E2) |
| Guéneau–Charguéraud–Pottier, ESOP'18 | paper only | idea-level (E2): O()-corollaries with packaged constants at the cashing boundary; no text to port |

Fetch vehicle note: AFP theory listings in this survey were taken from
the GitHub mirror `isabelle-prover/mirror-afp-2025` @ 400ee45
(2025-12-18). Porting-time extracts must be fetched against the pinned
Isabelle2025-2 release; for these long-stable entries the drift risk is
negligible but the discrepancy is named here rather than hidden.

Pin verification, 2026-07-31: GitHub's commit endpoint resolved
`isabelle_llvm_time` at full SHA
`42dd7f59998d76047bb4b6bce76d8f67b53a08b6` and `isabelle_llvm` at
`b44b6391ac00d8268e04dba4627a22d599e24dd6`; `git ls-remote` resolved
Sepreftime `main` to `c1c987b45ec886d289ba215768182ac87b82f20d` and
Imperative_HOL_Time `master` to
`09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`.

## 2. P0 findings — where the plan's assumptions were wrong

These four findings correct assumptions written into the accepted plan;
each has a consequence recorded in the ledger.

- **F1 — the artifact's IICF is dead code.** Grep of every
  `sepref/IICF/` file at 42dd7f5 for cost vocabulary
  (`acost|SPECT|lift_acost`): only `IICF_Array.thy` has any (partial).
  The IICF directory is commented out of the session ROOT and absent
  from the build closure of the only built target
  (`Sorting_Export_Code`, 89 theories, zero IICF files); the authors'
  own `thys.txt` manifest excludes it. The artifact's real cost-carrying
  container surface is: arrays + option/EO arrays
  (`Hnr_Primitives_Experiment.thy`, `ds/Proto_EOArray.thy`) and the
  amortized dynamic array (`examples/dynarray/Dynamic_Array.thy`).
  *Consequence (ledger E7):* P5 is a **cost-adaptation campaign, not a
  text port** — interfaces from the artifact's `Intf/` (interface-level
  text is fine), implementations written against Sepreftime's
  cost-carrying IICF (`enat`) and the no-cost twins (AFP
  `Refine_Imperative_HOL`, `isabelle_llvm` 2023) for shape, with every
  impl's currency cost text a derivation in the `CombRules.lean`
  precedent.
- **F2 — no cost-form FOREACH exists in any pinned source.** The
  artifact has none (all iteration is `whileT`/`monadic_WHILEIT`/RECT;
  its `nfoldli` uses are non-cost leftovers via `Refine_Monadic_Thin`).
  AFP `NREST`'s and Sepreftime's `Refine_Foreach.thy` are single-currency
  `enat`. *Consequence (ledger E5):* P2's deliverable is an **authored
  currency-vector FOREACH/nfoldli**, derived — not transcribed — from
  three shape sources (AFP `Refine_Monadic` rule organization, AFP
  `NREST`/Sepreftime `enat` cost forms, Sepreftime `Sepref_Foreach` hnr
  forms). The plan's phrase "upgrades it to the artifact's cost form"
  has no source text behind it.
- **F3 — the artifact has no Kruskal, Edmonds–Karp, or BFS.** Its
  example suite is the sorting/introsort chain (+ dead non-cost KMP /
  Bin_Search / Prim). The Kruskal/EK-class derivations the plan told P0
  to pick live in **Sepreftime** (new pin above). *Consequence (ledger
  E6):* P3's house exemplar is retargeted to the **introsort budget
  spine** (currency-vector-native, in the primary pin); the **Kruskal
  chain** is ported from Sepreftime as the multi-structure budget
  exemplar once P2 (foreach) and P4.B (union-find) land, with the
  `enat`→`acost` adaptation ledgered; Edmonds–Karp is
  deferred-opportunistic, not scheduled.
- **F4 — union-find with time is within reach.** The plan made P4's
  union-find conditional on finding source text.
  `Sepreftime/Examples/Kruskal/Union_Find_Time.thy` (46.6 KB, with
  `UnionFind.thy`/`UnionFind_Impl.thy`) is that text; P4.B includes it
  unconditionally. Same `enat`→`acost`/SL adaptation class as E6.
- **F5 (minor).** mathlib may already carry an Akra–Bazzi/master-theorem
  formalization usable as the recurrence-closure endpoint; P3 checks
  `lean_local_search`/mathlib before porting any Eberl closure pattern,
  consistent with E2 (mathlib `Asymptotics` is the carrier).

## 3. Baseline — what is already ported (the diff's left side)

`word-ram/proofs/Lax13Proofs/Refine/`: 69 files, 47,054 lines, namespace
`Lax13Proofs.Refine.*`. Per-layer, with the source theories they cover:

| layer | files / lines | source theories covered |
|---|---|---|
| `Cost/` | 1 / 317 | `Abstract_Cost.thy`, `Enat_Cost.thy` (full) |
| `NREST/` | 8 / 6,508 | `NREST.thy` core+RECT+combinators, `NREST_Misc`, `Data_Refinement`, `Time_Refinement`, `NREST_Backwards_Reasoning`, `NREST_Type_Classes`; FOREACH from AFP `NREST` (`enat`, see F2); `NREST_Automation` read, **not ported** |
| `Autoref/` | 11 / 6,246 | `Relators`, `Param_Tool`+`Param_HOL`, `Autoref_Tagging`, `Tagged_Solver`, `Autoref_Phases`, `Autoref_Id_Ops`, `Autoref_Fix_Rel`, `Autoref_Translate`, `Autoref_Tool`+`Gen_Algo` (spine), `Autoref_Bindings_HOL` (partial) |
| `Ir/` | 7 / 5,085 | ours (D2: `Syntax`, `Semantics`) + `Sep_Algebra_Add`/`Sep_Generic_Wp`/`LLVM_Shallow_RS` shapes + `Frame_Infer` (full solver) |
| `Sepref/` | 18 / 12,742 | `Sepref_Basic`, `Sepref_Rules` (composition layer incl. dependent `hfcomp`), `Sepref_Id_Op`, `Sepref_Monadify`, `Sepref_Constraints`, `Sepref_Frame`, `Sepref_Translate`, `Sepref_Tool`, `Sepref_Definition` (command only); `CombRules`/`IrOps` content ours (derived — the artifact has no cost If/While hnr rules); + post-campaign T1/T2 waves (`Bounds`, `IrOpsExtra`) |
| `Codegen/` | 7 / 3,891 | ours (D3) — verified IR→IMP+ replaces the source's trusted printer |
| `Iicf/` | 8 / 3,923 | conventions + 6 structures (array, trail array, stack, queue, CSR, bitmask); **not** the source IICF framework |
| `Examples/` | 9 / 8,342 | acceptance/gate programs (BfsQ family) + probes |

Baseline caveats the port map inherits: `Refine.lean` (the subtree
aggregator) is stale — it imports only P1–P3 modules and its narrative
index stops at P1 (fix queued in P6, debt-register item G1); three files
are explicitly not capital (`Examples/T1Probe.lean`,
`Sepref/Examples/WordAssnSpike.lean`, `Examples/BfsQBounded.lean` — the
first is marked for deletion once its fix lands, the other two are the
spike for the rejected `wordAssn` option); the D4 gate coverage of the
`Sepref/` core is entirely indirect (debt-register G2).

The ND-MC consumer tree (`Lax3Proofs/Refine/`, 26 files / 21,736 lines)
is *not* infrastructure and is not part of this diff.

## 4. The port map (the diff's right side)

Per phase; **wave** = suggested landing wave within the phase. "Sol"
waves go to GPT-5.6-Sol workers per the plan's working model; the first
P1 wave is the half-size calibration wave.

### P1 — signature machinery

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| `to_hnr`/`to_hfref` normalization, `comp_PRE`, the `FCOMP` attribute (composition with pure relators + precondition intersection) | `Sepref_Rules.thy` (91.6 KB; the fref/hfref/hfcomp judgments incl. dependent `hfcomp` are already ported — this is the *machinery around* them) | — | THE SEAM (`OrderBridge.lean:36`) | **P1.A (calibration, half-size)** |
| `hrrCompDep` flattening lemma | local residue (`nd-mc-rebase-plan.md:298`; bites loop composition) | — | seam loop-composition | P1.A |
| signature→goal derivation: `sepref_definition`/`sepref_thm` goal preparation (retires hand-holed `hnRefine` goals) | `Sepref_Definition.thy` (6.2 KB) + `Sepref_Tool.thy` glue (16.5 KB; command shell already ported) | P1.A | every synthesis; ND-MC order phase | P1.B |
| `sepref_register` + interface-type discipline (`intf_of_assn`, TYPE annotations) | `Sepref_Combinator_Setup.thy` (19.8 KB; only the arity-equation schema is ported) + the register half of `Sepref_Id_Op.thy` | P1.A | operator identification at 15-array scale | P1.B |
| `sepref_decl_op`/`sepref_decl_intf`/`sepref_decl_impl` commands | `Sepref_Intf_Util.thy` (56.3 KB) | P1.B | P5 consumes for every container | P1.C — landed (`Sepref/IntfUtil.lean`, E12) |

Acceptance stays as the plan wrote it (BfsQSynth re-derived signature-only
+ FCOMP tutorial chain + ≥8-array toy).

### P2 — iteration layer

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| currency-vector `nfoldli` + FOREACH family + their hnr/sepref rules — **authored, E5** | shape sources: AFP `Refine_Monadic/Refine_Foreach.thy` (81.5 KB, rule organization + invariant style); AFP `NREST/Refine_Foreach.thy` (15.4 KB, `enat` cost form); Sepreftime `Refine_Foreach.thy` (17.0 KB) + `Sepref_Foreach.thy` (34.0 KB — size-identical to the AFP no-cost copy); existing `Combinators.lean` FOREACH (ℕ∞). Landed: `NREST/Foreach.lean`, `Sepref/Foreach.lean`. | P1 (rules in signature form) | R1.6 member lists; arena walks | P2.A — landed |
| iteration-list refinement: `list_set_rel`, `it_to_sorted_list` discipline | `Refine_Foreach.thy` §sorted-list + Collections `Iterator/` core: `Proper_Iterator` (9.4 KB), `It_to_It` (4.7 KB), `Idx_Iterator` (4.3 KB); `SetIterator`(+`Operations`) (39.1+38.3 KB) as reference, not text. Landed: `Autoref/Foreach.lean`, `NREST/Foreach.lean` result discipline. | P2.A | "iterate over exactly this set" as abstract op | P2.B — landed |
| Autoref rule set for iteration | `Refine_Foreach.thy` autoref setup + `Lib/Foldi.thy` (4.9 KB). Landed: `autoref_nfoldli`, `LIST_FOREACHPrimeE_param`, sorted-list gates in `Autoref/Foreach.lean`. | P2.A | autoref'd abstract programs | P2.B — landed |
| `Recursion_Combinators` (for-loops over RECT, nesting discipline) | Sepreftime `FloydWarshall/Recursion_Combinators.thy` (4.4 KB). Landed: `NREST/For.lean`; ledger E13. | P1 | nested per-arena passes (order phase) | P2.B — landed |

Acceptance as planned (arena-walk exemplar with compiled
carrier-blindness probe).

### P3 — currency discipline at scale

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| `sc_solve` (+`'`/`_debug`/`_upperbound`), the `norm_cost` lemma bundle, `norm_pp` | `NREST_Automation.thy` (11.1 KB — note `norm_cost` is a lemma bundle, not a method) | — | every cost side condition; `g2_plug` gaps | P3.A — landed (`NREST/Automation{Attrs,}.lean`) |
| shallow VCG program-head case splitter | Sepreftime `moreCurr/MoreCurrAutomation.thy:73–131` at exact pin `c1c987b45ec886d289ba215768182ac87b82f20d` | P3.A automation | `gwp`/`progress` goals headed by `Option`/`Sum` matches | P3.A — landed (`NREST/VcgCaseSplit.lean`) |
| currency flattening / collapse-once-at-cash | Sepreftime `moreCurr/Flatten_Currencies.thy` (12.4 KB) at exact pin `c1c987b45ec886d289ba215768182ac87b82f20d`; `AbstractSepreftime.thy` (131 KB) surveyed for dropped laws | P3.A | the cash boundary; ND-MC arena-form budgets | P3.A — landed (`NREST/FlattenCurrencies.lean`) |
| currency house-style conventions | `Sorting_Setup.thy` (63.3 KB — extract the conventions: named per-op currencies, spec forms), | P3.A | all downstream phases | P3.B |
| multi-phase budget exemplar: the introsort budget spine (**E6 retarget**) | `Sorting_Quicksort_Scheme.thy` (25.0 KB) + `Sorting_Introsort.thy` (32.8 KB) abstract halves, + `Sorting_Partially_Sorted.thy` (5.6 KB) | P2, P3.A | house pattern for multi-phase budgets | P3.B |
| asymptotic face: O()-corollaries at the cashing boundary, recurrence closures for `CostRecurrence` | mathlib `Asymptotics` carrier (E2); patterns from IHT `Asymptotics_1D` (40.7 KB) / `Asymptotics_Recurrences` (28.2 KB), `Landau_Symbols` simproc patterns, `Akra_Bazzi`/`Master_Theorem` — check mathlib first (F5) | P3.A | "closes to almost-linear" detached from coefficients | P3.C |

Acceptance as planned (BfsQ as currency vector reproducing
`K = 56n + 40ns + 33`; `sc_solve` discharge; mechanical O(n + ns)).

### P4 — credits and amortization

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| time-credit assertion discipline: credits stored in DS assertions, pay-on-entry / spend-on-touch | `SLTC.thy` (32.8 KB) + `SLTC_More.thy` (21.8 KB); `SLTC_Automation.thy` (41.3 KB) architecture only — auto2 is not our carrier, `fri`/`refine_vcg` stay (X7) | P3 | touched-only as frame reasoning | P4.A |
| dynamic array, amortized O(1) push | **primary: artifact `examples/dynarray/Dynamic_Array.thy` (49.3 KB — currency-native: `TR_dynarray` exchange rates, `augment_amor_assn` potential-carrying assertions)**; secondary: `IHT_Dynamic_Array(_More)` (7.6+8.1 KB), `Amortized_Examples.thy` §dyn-table + `Dynamic_Tables/Tables_nat.thy` (22.9 KB) for the potential math | P4.A | resizable arrays (P5); credit exemplar #1 | P4.A |
| union-find with credits (**F4: unconditional**) | Sepreftime `Union_Find_Time.thy` (46.6 KB) + `UnionFind.thy`/`UnionFind_Impl.thy` (2.2+2.9 KB); `enat`→`acost` + SLTC→our-SL adaptation (E6-class) | P4.A | Kruskal exemplar; credit exemplar #2 | P4.B |
| skew heap (credit exemplar #3, stretch) | `Skew_Heap_Analysis.thy` (7.5 KB) + `IHT_Skew_Heap.thy` (10.8 KB) | P4.A | breadth default | P4.B stretch |
| the arena bundle (ledger E3, ours): composite assertion owning data + member list + c··members· credits | no source | P2 (member lists), P4.A | ND-MC touched-only; P9 | P4.C |
| `treset_cost_touched_only` re-derived as a credit argument; child-engine budget from bundle credits | local | P4.C | acceptance | P4.C |
| Kruskal chain (multi-structure budget exemplar, **E6**) | Sepreftime `Kruskal/`: `MinWeightBasis` (18.1), `Kruskal` (9.1), `Kruskal_Refine` (16.9), `Kruskal_Time` (5.3), `Kruskal_Impl` (19.7), `MaxNode_Impl` (11.8), `UGraph_Impl` (10.1) ≈ 91 KB; `enat`→`acost` | P2, P4.B, parts of P5 | the house cross-structure derivation | P4.C / P5 seam |

### P5 — IICF breadth (default-include; all cost-adaptations per E7)

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| the 8 interfaces: Set, Map, List, List_List, Matrix, Multiset, Prio_Bag, Prio_Map | artifact `Intf/` (3.4 / 6.9 / 7.4 / 3.7 / 19.9 / 8.6 / 5.7 / 6.5 KB) — interface text is monad-level, portable despite F1 | P1.C (`sepref_decl_*`) | everything below | P5.A |
| array lists / resizable arrays: `Array_List`, `DArray_List` (dynamic-array-backed), `MS_Array_List`, `Indexed_Array_List`, `Array_of_Array_List` | Sepreftime cost copies (8.8 / 3.1 / 8.5 / 16.9 KB) + artifact `Array_of_Array_List` (9.1, + `ds/` twin 14.5 shape); no-cost twins for shape | P4.A (dyn array), P5.A | ND-MC member lists; general | P5.B |
| array maps: `Array_Map`, `Array_Map_Total`, `ArrayMap_Map` | artifact (7.7 / 4.2 KB, dead — shape) + Sepreftime `IICF_ArrayMap_Map` (6.5 KB, cost) | P5.A | bounded-key maps (the honest hash-map replacement, X5) | P5.B |
| matrices: `Matrix` intf + array matrix | AFP `IICF_Array_Matrix` (23.5 KB) + Sepreftime (10.4 KB, cost) | P5.A | Floyd–Warshall-class; PCP constraint graphs | P5.C |
| heaps / prio maps: `Abs_Heap`, `Impl_Heap`, `Abs_Heapmap`, `Impl_Heapmap` | Sepreftime cost copies (33.6 / 6.5 / 50.5 / 32.7 KB); artifact copies dead (F1); `isabelle_llvm` 2023 shapes | P5.A/B | Dijkstra/Prim-class; PCP expanders | P5.C |
| multisets & list sets: `List_Mset`, `List_MsetO`, `List_SetO`, `List_Set` | AFP/Sepreftime (5.4 / 4.3 / 5.3 / 4.4 KB) | P5.A | sorting-class specs | P5.D |
| RBT map/set (ordered maps for unbounded keys — the worst-case-honest replacement for hash maps, X5) | Sepreftime `IICF_RbtMap_Map` (4.5 KB) + `IICF_Rbt_Set` (15.2 KB) | P5.A | breadth default | P5.D stretch |
| ICF iterator discipline as library convention | consumed from P2.B | P2 | all containers | P5.D |

Acceptance as planned (translator consumes every structure's rules on an
exercise with zero bespoke tactics + one cross-structure exercise each).

### P6 — debt closure

Work list = **`debt-register.md`** (opened by this P0; ~40 items with
citations). New-source items within it: the `inres` section of
`NREST.thy`; `Refine_Leof.thy` (10.6 KB — small, port under rule 4;
`Sepref/Basic.lean` P4/D-k names the consumer); the copy machinery
(`COPY` in `Sepref_Monadify.thy:61`, `hnr_pure_COPY`/`fold_COPY` in
`Sepref_Tool.thy:317–328`, per-impl hnr copy rules — note: **no
`Sepref_Copy.thy` exists in any source**; the plan's
"`sepref_copy_rules`" item resolves to these sites); artifact
`Refine_Heuristics.thy` (7.1 KB); `Lib/Indep_Vars.thy` (1.6 KB, INDEP —
prerequisite of `autoref_higher_order_rule`, delta O7). Everything else
in the register is local repair, no fetch.

### P7 — frame-layer performance

No new sources (the attack list stays: entailment-rule indexing, residue
caching, round-loop early exit; `Termtab`-style pre-match already
served). The P0-probe suite to re-measure is pinned in
`nd-mc-rebase-plan.md:330–340` (DiscrTree established as the wrong
target).

### P8 — executable gates

Ours (ledger E4); no sources. Unchanged from the plan.

### P9 — consumer gate

No port items; consumes P1–P4 exports. Unchanged from the plan.

## 5. Exclusions (rule 4 — each argued)

| id | component | reason | revisit trigger |
|---|---|---|---|
| X1 | LLVM-specific layers of the artifact: `basic/` (shallow LLVM semantics, memory model, codegen + `LLVM_Builder.ml`, preproc), `vcg/` `*_RS` files beyond the already-ported `Sep_Generic_Wp` shapes, `ds/` (LLVM heap structures), `lib/` word/integer theories, `Sorting_Export_Code`, benchmarks | machine-specific; our substrate is the word-RAM IR + verified `Codegen/` (ledgers D2/D3) | never — the boundary is the tower/hand pin |
| X2 | `others/deep`, `others/simple`, `prototypes/` | excluded from the source's own build; dead experiments | never |
| X3 | GenCF (`Collections/GenCF/`: `Gen_Set`/`Gen_Map`/… + `Impl_*`) | Autoref-side generic-algorithm layer whose role our Sepref path covers; no consumer in any pipeline; the plan already presumed exclusion | an Autoref-only (non-Sepref) consumer appears |
| X4 | the ICF locale framework proper (`ICF/spec`, `gen_algo`, `impl`, `tools/Locale_Code`) | superseded by IICF within the source line itself; `Locale_Code` is an Isabelle-specific code-gen trick; iterator discipline is extracted separately (P2.B) | never |
| X5 | hash-map implementations (`Impl_Array_Hash_Map` 70.5 KB, `HashMap`, hash parts of `IICF_Sepl_Binding`) — **a deviation from resolved JAN-FLAG 3's list, argued**: | no cost-honest story on a deterministic word-RAM (worst-case per-op O(1) fails adversarially; expected-time needs randomized machinery our cost calculus does not carry); every current consumer has bounded key spaces served exactly by array maps (P5.B); ordered/unbounded keys served worst-case-honestly by RBT (P5.D) | a consumer with sparse unbounded keys where log factors matter; or randomized-cost infrastructure lands |
| X6 | `Refine_Det`, `Refine_Transfer`, `Refine_Pfun`, `Refine_Automation`, `Autoref_Monadic`, `Code_Target_ICF` | the Isabelle code-generator road (nres → executable SML); our executable face is `Codegen/` (D3) + D4 computable twins | never |
| X7 | auto2 automation (`SLTC_Automation` ML, `sep_time_steps.ML`, auto2 itself) | automation substrate, not calculus; architecture read at P4.A, carrier stays `fri`/`refine_vcg` (D-class precedent: the tower already made this call for Isabelle's ML tactics) | never |
| X8 | `Automatic_Refinement/Lib` substrate: `Misc.thy` (167 KB), `Refine_Util`, antiquotation/ML tooling (`Mpat_Antiquot`, `Mk_Term_Antiquot`, `Attr_Comb`, `Select_Solve`, `Anti_Unification`, `Named_Sorted_Thms`) | substrate role played by mathlib + Lean 4 metaprogramming; `Named_Sorted_Thms`' ordering guarantee already documented in `Sepref/IdOp.lean` | `Anti_Unification`: if Autoref heuristic quality (delta F6 work) demands it |
| X9 | Collections `Lib` oddments: `Robdd` (121.7 KB), tries, finger trees (`FT*`), `Dlist_add`, binomial/pairing-heap breadth | no plausible consumer in ND-MC / PCP / any named pipeline; heap needs covered by array heaps (P5.C) + skew heap (P4.B stretch) | a consumer names one |
| X10 | splay trees & pairing heaps (`Splay_Tree_Analysis*`, `Pairing_Heap_*`, `IHT_Splay_Tree`) | amortized-analysis breadth beyond the three chosen exemplars; splay potentials are real-valued/log-shaped — poor fit for the ℕ-valued credit SL without new machinery; no consumer | a consumer needs self-adjusting structures |
| X11 | Edmonds–Karp / `Augmenting_Path_BFS` chain (Sepreftime, ≈146 KB) | exemplar role filled by introsort spine (P3.B) + Kruskal chain (P4.C); max-flow has no consumer in any pipeline. **Deferred-opportunistic, not excluded** — it is the natural stress test if P9 needs a second large consumer | P9 wants a second consumer-scale exercise; or an idle-margin session |
| X12 | `Landau_Real_Products` decision procedure (73.9 KB + simproc ML), `Akra_Bazzi_Real`/`Approximation` numerics | pattern-level port only (E2); mathlib `Asymptotics` + (per F5) possibly mathlib's own Akra–Bazzi are the carriers | P3.C finds mathlib's closure layer insufficient |
| X13 | Sepreftime root layer (`HNR.thy`, `SepLog_Automatic`, `Set_Impl`, …) and IHT machine layer (`Heap_Time_Monad`, `Array_Time`, `Ref_Time`, `Transpile`) | superseded by the ESOP artifact's sepref (our primary source) and by our own machine layer; only the case studies, foreach, `moreCurr`, SLTC discipline, and asymptotics feed ports | never |
| X14 | Userguides (`Sepref_Guide_*`, ICF/Refine_Monadic userguides) | manuals, not port targets — they stay the workers' documentation, per the fidelity charter | — |
| X15 | surface syntax (`do`-macro front end); GenCF-style code export; concept surfaces; machine model; `lake update` | carried from the plan's "Not in scope" verbatim | per plan |

## 6. Deviation ledger

Opened as `ledger.md` in this directory: inherits D1–D5/N1–N3 (tower)
and E1–E4 (plan seeds) by reference, adds **E5** (authored
currency FOREACH — no source text), **E6** (exemplar retarget: introsort
spine as house pattern; Kruskal/union-find ported from Sepreftime with
`enat`→`acost` adaptation), **E7** (P5 as cost-adaptation, not text
port), **E8** (retroactive recording of two silent skeleton drifts found
by this survey: the `Iicf/` flat layout vs design.md §7's `Intf/`/`Impl/`
split, and the `Codegen/` file split), and **E9** (X5's hash-map
exclusion, a deviation from the resolved flag-3 list).

## 7. Size and sequencing summary

Rough new-source volume per phase (KB of source text to be read/ported;
authored items counted by their shape sources): P1 ≈ 165; P2 ≈ 150
(mostly shape sources for an authored layer); P3 ≈ 200 (about half
extract-only); P4 ≈ 210; P5 ≈ 260; P6 ≈ 30 + local. The plan's
dependency shape is unchanged: P1 first, P2–P5 satellite-parallelizable
after it, P6–P8 fitted in margins, P9 last. The plan's budgets stand;
nothing found in P0 moves them, though P5's E7 finding shifts its
character from transcription toward derivation, which historically runs
*slower* per KB — watch at the first P5 wave.

Worker note for the P1 calibration wave: every brief must carry the
relevant extract (fetched fresh at the pin) — the extract files of the
tower campaign (`refinement-tower/p4-sepref-extracts.md`,
`p4-sepref-deep-extracts.md`) already hold the `Sepref_Rules.thy`
composition sections and should be the wave's starting point.
