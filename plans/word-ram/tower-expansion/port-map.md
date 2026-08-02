# Tower expansion P0 — port map and pins

Status: **LANDED 2026-07-31** (P0 deliverable of
`plans/word-ram/tower-expansion-plan.md`; authored under the full-autonomy
grant). This document is the enumeration the plan demanded: the existing
69-file `Refine/` port diffed against the pinned sources' theory graphs,
every unported item assigned a wave or an argued exclusion (rule 4:
exclusions carry the burden). Companion files in this directory:
`ledger.md` (the campaign's deviation ledger, opened here) and
`debt-register.md` (the fine-grained open-debt list that feeds P6).

This landed map freezes active scope. Only rows assigned unconditionally
to P1–P10 are live work. Inventory, exclusion, deferred, stretch, and
revisit rows are P10 backlog and cannot be pulled into a live phase by a
consumer. Inside an active row, workers port the coherent source declaration
family rather than extracting only the current example's lemma.

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

These five findings correct assumptions written into the accepted plan;
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
  `enat`→`acost` adaptation ledgered. Edmonds–Karp is outside active P0–P10
  scope and may be reconsidered only at P10 or in a later campaign.
- **F4 — union-find with time is within reach.** The plan made P4's
  union-find conditional on finding source text.
  `Sepreftime/Examples/Kruskal/Union_Find_Time.thy` (46.6 KB, with
  `UnionFind.thy`/`UnionFind_Impl.thy`) is that text; P4.B includes it
  unconditionally. Same `enat`→`acost`/SL adaptation class as E6.
- **F5 (resolved).** The pinned mathlib carries
  `AkraBazziRecurrence.isBigO_asympBound`, its reverse-O theorem, and
  `isTheta_asympBound`. P3.C reuses and documents those endpoints while
  faithfully porting the scheduled IHT 1D/2D/recurrence declaration
  families; it does not open an independent AFP Akra–Bazzi source slice.

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

Per phase; **wave** records the historical or planned landing subdivision.
Worker allocation follows the current governance in the campaign plan;
old calibration labels do not prescribe a model, worker type, or task size.

### P1 — signature machinery

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| `to_hnr`/`to_hfref` normalization, `comp_PRE`, the `FCOMP` attribute (composition with pure relators + precondition intersection) | `Sepref_Rules.thy` (91.6 KB; the fref/hfref/hfcomp judgments incl. dependent `hfcomp` are already ported — this is the *machinery around* them) | — | THE SEAM (`OrderBridge.lean:36`) | **P1.A — landed** |
| `hrrCompDep` flattening lemma | local residue (`nd-mc-rebase-plan.md:298`; bites loop composition) | — | seam loop-composition | P1.A |
| signature→goal derivation: `sepref_definition`/`sepref_thm` goal preparation (retires hand-holed `hnRefine` goals) | `Sepref_Definition.thy` (6.2 KB) + `Sepref_Tool.thy` glue (16.5 KB; command shell already ported) | P1.A | every synthesis; large-arity phase synthesis | P1.B |
| `sepref_register` + interface-type discipline (`intf_of_assn`, TYPE annotations) | `Sepref_Combinator_Setup.thy` (19.8 KB; only the arity-equation schema is ported) + the register half of `Sepref_Id_Op.thy` | P1.A | operator identification at 15-array scale | P1.B |
| `sepref_decl_op`/`sepref_decl_intf`/`sepref_decl_impl` commands | `Sepref_Intf_Util.thy` (56.3 KB) | P1.B | P5 consumes for every container | P1.C — landed (`Sepref/IntfUtil.lean`, E12) |

Acceptance stays as the plan wrote it (BfsQSynth re-derived signature-only
+ FCOMP tutorial chain + ≥8-array toy).

### P2 — iteration layer

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| currency-vector `nfoldli` + FOREACH family + their hnr/sepref rules — **authored, E5** | shape sources: AFP `Refine_Monadic/Refine_Foreach.thy` (81.5 KB, rule organization + invariant style); AFP `NREST/Refine_Foreach.thy` (15.4 KB, `enat` cost form); Sepreftime `Refine_Foreach.thy` (17.0 KB) + `Sepref_Foreach.thy` (34.0 KB — size-identical to the AFP no-cost copy); existing `Combinators.lean` FOREACH (ℕ∞). Landed: `NREST/Foreach.lean`, `Sepref/Foreach.lean`. | P1 (rules in signature form) | generic member-list walks | P2.A — landed |
| iteration-list refinement: `list_set_rel`, `it_to_sorted_list` discipline | `Refine_Foreach.thy` §sorted-list + Collections `Iterator/` core: `Proper_Iterator` (9.4 KB), `It_to_It` (4.7 KB), `Idx_Iterator` (4.3 KB); `SetIterator`(+`Operations`) (39.1+38.3 KB) as reference, not text. Landed: `Autoref/Foreach.lean`, `NREST/Foreach.lean` result discipline. | P2.A | "iterate over exactly this set" as abstract op | P2.B — landed |
| Autoref rule set for iteration | `Refine_Foreach.thy` autoref setup + `Lib/Foldi.thy` (4.9 KB). Landed: `autoref_nfoldli`, `LIST_FOREACHPrimeE_param`, sorted-list gates in `Autoref/Foreach.lean`. | P2.A | autoref'd abstract programs | P2.B — landed |
| `Recursion_Combinators` (for-loops over RECT, nesting discipline) | Sepreftime `FloydWarshall/Recursion_Combinators.thy` (4.4 KB). Landed: `NREST/For.lean`; ledger E13. | P1 | generic nested bounded passes | P2.B — landed |

Acceptance as planned (arena-walk exemplar with compiled
carrier-blindness probe).

### P3 — currency discipline at scale

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| `sc_solve` (+`'`/`_debug`/`_upperbound`), the `norm_cost` lemma bundle, `norm_pp` | `NREST_Automation.thy` (11.1 KB — note `norm_cost` is a lemma bundle, not a method) | — | generic cost side conditions | P3.A — landed (`NREST/Automation{Attrs,}.lean`) |
| shallow VCG program-head case splitter | Sepreftime `moreCurr/MoreCurrAutomation.thy:73–131` at exact pin `c1c987b45ec886d289ba215768182ac87b82f20d` | P3.A automation | `gwp`/`progress` goals headed by `Option`/`Sum` matches | P3.A — landed (`NREST/VcgCaseSplit.lean`) |
| currency flattening / collapse-once-at-cash | Sepreftime `moreCurr/Flatten_Currencies.thy` (12.4 KB) at exact pin `c1c987b45ec886d289ba215768182ac87b82f20d`; `AbstractSepreftime.thy` (131 KB) surveyed for dropped laws | P3.A | generic cash boundary | P3.A — landed (`NREST/FlattenCurrencies.lean`) |
| currency house-style conventions | `Sorting_Setup.thy` (63.3 KB — named per-op currencies and cost-carrying spec forms). Landed: list-built named phase accounts, finite exchange rows, vector-before-cash gates. | P3.A | all downstream phases | P3.B — landed (`Examples/IntrosortBudget.lean`) |
| multi-phase budget exemplar: the introsort budget spine (**E6 retarget**) | `Sorting_Quicksort_Scheme.thy` (25.0 KB) + `Sorting_Introsort.thy` (32.8 KB) abstract halves + `Sorting_Partially_Sorted.thy` (5.6 KB), with the imported phase accounts audited in `Sorting_Quicksort_Partition.thy` and `Sorting_Final_insertion_Sort.thy`. Landed: exact `introsort3_cost` top-level account, exact `introsort_aux_cost` recursive account, a TId-style theorem replacing `slice_part_sorted` without double-counting it, coherent NREST consumption, exact `introsort_cost3` upper-bound vector, and exact `project_all` scalar. Ledger E15 records which later upper-rate chain remains collapsed. | P2, P3.A | house pattern for multi-phase budgets | P3.B — landed (`Examples/IntrosortBudget.lean`) |
| faithful asymptotic machinery: 1D/2D polylog carriers, stability/eventual monotonicity, O/Ω/Θ intro/elimination/composition/comparison/normalization rules, and recurrence theorem families | IHT `Asymptotics_1D.thy` (864 lines), `Asymptotics_2D.thy` (676), `Asymptotics_Recurrences.thy` (589), plus the directly supporting `landau_util{,_2d}.ML` registry/normalizer architecture at pin `09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`; mathlib `Asymptotics` is the carrier, its fixed-shrink Akra–Bazzi endpoint is documented, and no duplicate recurrence framework is introduced (F5). P3.C-A/B landed the complete 1D families; P3.C-C/D landed genuine product-filter 2D foundations, composition, partial comparison, and normalization; P3.C-E landed all 18 recurrence rows; P3.C-F landed exact O-only BfsQ and introsort consumer gates. Final audit: 131 rows, 126 live, five exclusions. | P3.A/B | generic asymptotic API; post-port BfsQ/introsort demonstrations | P3.C — complete |

Acceptance: complete declaration map for the three IHT theories and
source-shaped 1D/2D/recurrence gates, followed by BfsQ O(n + ns) on the
genuine product filter and introsort O(n log n) from their exact cash
upper bounds. No ND-MC import or API is permitted.

### P4 — credits and amortization

Design status: **COMPLETE 2026-08-01** in `p4-design.md`. Worker graph was
A1 → A2 and A1+B1 → B2. Allocation is rejected; A2's executable face is a
bounded caller-owned preallocated adapter and may not claim unbounded growth.
The generic/abstract amortization theorem remains source-faithful.

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| time-credit assertion discipline: credits stored in DS assertions, pay-on-entry / spend-on-touch | `SLTC.thy` (32.8 KB) + `SLTC_More.thy` (21.8 KB); `SLTC_Automation.thy` (41.3 KB) architecture only — auto2 is not our carrier, `fri`/`refine_vcg` stay (X7); exact ranges/pins/blobs in `p4-design.md` | P3 | generic potential-carrying assertions | **P4.A1 — complete (`Sepref/Amortization.lean`)** |
| dynamic array, amortized O(1) push | **primary: artifact `examples/dynarray/Dynamic_Array.thy` (49.3 KB — currency-native: `TR_dynarray` exchange rates, `augment_amor_assn` potential-carrying assertions)**; secondary: `IHT_Dynamic_Array(_More)` (7.6+8.1 KB), `Amortized_Examples.thy` §dyn-table + `Dynamic_Tables/Tables_nat.thy` (22.9 KB) for the potential math. Source concrete implementation is undefined/unfinished at primary lines 1097–1107; executable Lean adapter is bounded and caller-owned per P4-DYN-1. | P4.A1 | bounded arrays (P5); credit exemplar #1 | **P4.A2 — complete (`Iicf/IicfDynamicArray.lean`)** |
| pure union-find representation, correctness, and logarithmic height theory | Sepreftime `UnionFind.thy` + pure `Union_Find_Time.thy:20–649,813–828`, with AFP `Partial_Equivalence_Relation.thy:11–75`; exact pins/blobs in `p4-design.md` | P3 | timed union-find proof base | **P4.B1 — complete (`Iicf/UnionFindAbstract.lean`)** |
| union-find with credits (**F4: unconditional**) | Sepreftime `UnionFind_Impl.thy` + executable `Union_Find_Time.thy:651–811,832–1204`; `enat`→`acost`, SLTC→our-SL, caller-owned arrays, recursion→loop adaptation (E6/P4-UF-1) | P4.A1, P4.B1 | Kruskal exemplar; credit exemplar #2 | **P4.B2 — complete (`Iicf/UnionFindTime.lean`)** |
| Kruskal chain (source-native post-freeze validation, **E6**) | Sepreftime `Kruskal/`: `MinWeightBasis` (18.1), `Kruskal` (9.1), `Kruskal_Refine` (16.9), `Kruskal_Time` (5.3), `Kruskal_Impl` (19.7), `MaxNode_Impl` (11.8), `UGraph_Impl` (10.1) ≈ 91 KB; `enat`→`acost` | P2, P4.B2, required P5 families | validates frozen generic APIs; does not design them | P5 post-freeze gate |

### P5 — exact P0-fixed IICF table (all cost-adaptations per E7)

> **Rev 5 corrections, 2026-08-02.** Three things in this table are wrong and
> are corrected in place below.
>
> 1. **"Sepreftime cost copies" is inaccurate** (plan finding F7). Sepreftime's
>    `IICF_Array_List.thy` carries no cost text at all — plain `sep_auto`
>    Hoare triples, no credits. AFP's IICF is uncosted by design and the
>    artifact's is dead, so **no pinned source has a cost-carrying IICF**. The
>    entire currency-vector layer of P5.B/C is authored, not adapted. E7's
>    premise is corrected in `ledger.md`.
> 2. **"artifact … dead" is not a source-quality verdict** (F8). Diffed
>    against the live `isabelle_llvm` 2023 tree: `IICF_Array_of_Array_List`
>    and `IICF_Abs_Heap` are byte-identical; the rest differ by 1–4 lines
>    (debug leftovers, whitespace, `Mreturn`/`return`, one `hrr_comp` arity).
>    The text ported is the live text. Also: `IICF_Array_Map`,
>    `IICF_Array_Map_Total` and `IICF_Array_of_Array_List` exist **only** in
>    the LLVM trees (AFP 23 files, Sepreftime 30, both LLVM trees 22), so
>    those leaves had no alternative source. No re-port is owed on these
>    grounds.
> 3. **The IICF is superseded, and this table has no row for its successor**
>    (F6). Added below as the P4.5 row.

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| **ownership substrate: costed allocator + EO arrays + IICF bridge** | artifact `sepref/Hnr_Primitives_Experiment.thy` (985 L, **the only cost-carrying container text in any pin**; 1 `sorry` at `FREE_eoarray_assn`), `ds/Proto_EOArray.thy` (186 L, no cost), `sepref/IICF/Impl/Proto_IICF_EOArray.thy` (298 L, the interface bridge) | P4 | **gates P5.D, `Impl_Heapmap`, and the P5.E re-seat** | **P4.5 — new in rev 5** |

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| the 8 interfaces: Set, Map, List, List_List, Matrix, Multiset, Prio_Bag, Prio_Map | artifact `Intf/` (3.4 / 6.9 / 7.4 / 3.7 / 19.9 / 8.6 / 5.7 / 6.5 KB) — interface text is monad-level, portable despite F1 | P1.C (`sepref_decl_*`) | everything below | **P5.A — complete; all 8 root-imported and archive-green** |
| array lists / resizable arrays: `Array_List`, `DArray_List` (dynamic-array-backed), `MS_Array_List`, `Indexed_Array_List`, `Array_of_Array_List` | Sepreftime cost copies (8.8 / 3.1 / 8.5 / 16.9 KB) + artifact `Array_of_Array_List` (9.1, + `ds/` twin 14.5 shape); no-cost twins for shape | P4.A (dyn array), P5.A | bounded sequences; general | **P5.B — all five sequence families green as unrooted leaves (5/5 sequence families; 5/8 P5.B implementation families); array maps next** |
| array maps: `Array_Map`, `Array_Map_Total`, `ArrayMap_Map` | artifact (7.7 / 4.2 KB, dead — shape) + Sepreftime `IICF_ArrayMap_Map` (6.5 KB, cost) | P5.A | bounded-key maps (the honest hash-map replacement, X5) | **P5.B complete — all three map families green as unrooted leaves (3/3 map families; 8/8 P5.B implementation families)** |
| matrices: `Matrix` intf + array matrix | AFP `IICF_Array_Matrix` (23.5 KB) + Sepreftime (10.4 KB, cost) | P5.A | Floyd–Warshall-class; PCP constraint graphs | **P5.C — `Array_Matrix` green as an unrooted leaf (1/1 matrix family; 4/5 P5.C families)** |
| heaps / prio maps: `Abs_Heap`, `Impl_Heap`, `Abs_Heapmap`, `Impl_Heapmap` | Sepreftime cost copies (33.6 / 6.5 / 50.5 / 32.7 KB); artifact copies dead (F1); `isabelle_llvm` 2023 shapes | P5.A/B | Dijkstra/Prim-class; PCP expanders | **P5.C — `Abs_Heap`, `Impl_Heap`, and `Abs_Heapmap` green as unrooted leaves (3/4 heap families; 4/5 P5.C families); `Impl_Heapmap` next** |
| multisets & list sets: `List_Mset`, `List_MsetO`, `List_SetO`, `List_Set` | AFP/Sepreftime (5.4 / 4.3 / 5.3 / 4.4 KB) | P5.A, **P4.5** | sorting-class specs | P5.D — **gated behind P4.5 (rev 5)**; must not add caller-owned boundaries |
| ICF iterator discipline as library convention | consumed from P2.B | P2 | all containers | P5.D |
| **re-seat landed P5.B/C leaves onto the P4.5 substrate** | no new source; statement strengthening + substrate substitution over landed files | P4.5 | every consumer that must *construct* a structure | **P5.E — new in rev 5.** First target `ArrayList`: delete `arrayListReadyRel` and restate append unconditionally, matching source `arl_append_hnr_aux` |
| plain arrays: `larray` family (`larray1_rel`, `larray_assn`, `la_replicate`, `la_replicate_init`, `la_grow_init`, `la_length`, `la_is_empty`, `la_get`, `la_set`, `larray_swap`, `la_free`, `larray_boundD`) and `replicate_init`/`grow_init` | artifact `IICF_Array.thy:11–60,189–205,233–398` | — | general | **RESOLVED 2026-08-02 → argued exclusion X17.** Found as negative space (in zero code files and zero planning documents); excluded on the merits, not by omission. Access half duplicates seam-proved `ArrayList`; construction half is subsumed and improved by P4.5's O(1) zeroed allocation; deallocation falls under P4.5's recorded exclusion (basis amended 2026-08-02, ledger E23). Three revisit triggers recorded at X17 |

Acceptance: uniform source-shaped rule-consumption gates per implementation
family with zero bespoke tactics, then the one source-native Kruskal
post-freeze validation. Invented exercises do not shape APIs.

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
prerequisite of `autoref_higher_order_rule`, delta O7).

| item | source (size) | deps | consumer | wave |
|---|---|---|---|---|
| generic `RECT`/gfp order-isomorphism transport and `flatCurrs_whileT` | Sepreftime `moreCurr/Flatten_Currencies.thy` (12.4 KB), especially the omitted while law; local `NREST/Rec.lean` supplies `RECT` and receives the substrate-generic transport theorem | P3.A flattening API | closes fixed source debt E14; terminating nondeterministic-loop gate | **P6 — unconditional** |

Everything else in the register is local repair, no fetch.

### P7 — frame-layer performance

No new sources (the attack list stays: entailment-rule indexing, residue
caching, round-loop early exit; `Termtab`-style pre-match already
served). The frozen source-neutral `FrameScale3to5` fixture is primary;
the historical ND-MC probe is secondary, read-only, and non-gating.

### P8 — executable gates

Ours (ledger E4); no sources. Generic missing-producer and cost-floor
fixtures are primary; archived B7 evidence is secondary and read-only.

### P9 — consumer gate

No port items. It owns the local arena bundle and touched-only reset
instantiation and consumes the frozen P1–P5 exports. Consumer gaps cannot
widen earlier phases unless they prove a scheduled source-fidelity defect.

## 5. Exclusions (rule 4 — each argued)

| id | component | reason | revisit trigger |
|---|---|---|---|
| X1 | LLVM-specific layers of the artifact: `basic/` (shallow LLVM semantics, memory model, codegen + `LLVM_Builder.ml`, preproc), `vcg/` `*_RS` files beyond the already-ported `Sep_Generic_Wp` shapes, `ds/` (LLVM heap structures), `lib/` word/integer theories, `Sorting_Export_Code`, benchmarks | machine-specific; our substrate is the word-RAM IR + verified `Codegen/` (ledgers D2/D3) | never — the boundary is the tower/hand pin |
| X2 | `others/deep`, `others/simple`, `prototypes/` | excluded from the source's own build; dead experiments | never |
| X3 | GenCF (`Collections/GenCF/`: `Gen_Set`/`Gen_Map`/… + `Impl_*`) | Autoref-side generic-algorithm layer whose role our Sepref path covers; no consumer in any pipeline; the plan already presumed exclusion | an Autoref-only (non-Sepref) consumer appears |
| X4 | the ICF locale framework proper (`ICF/spec`, `gen_algo`, `impl`, `tools/Locale_Code`) | superseded by IICF within the source line itself; `Locale_Code` is an Isabelle-specific code-gen trick; iterator discipline is extracted separately (P2.B) | never |
| X5 | hash-map implementations (`Impl_Array_Hash_Map` 70.5 KB, `HashMap`, hash parts of `IICF_Sepl_Binding`) — **a deviation from resolved JAN-FLAG 3's list, argued**: | no cost-honest story on a deterministic word-RAM (worst-case per-op O(1) fails adversarially; expected-time needs randomized machinery our cost calculus does not carry); current bounded key spaces are served exactly by array maps (P5.B); an ordered-map/RBT option for sparse unbounded keys is deferred with X16 | P10 review if a consumer needs sparse unbounded keys where log factors matter, or randomized-cost infrastructure lands |
| X6 | `Refine_Det`, `Refine_Transfer`, `Refine_Pfun`, `Refine_Automation`, `Autoref_Monadic`, `Code_Target_ICF` | the Isabelle code-generator road (nres → executable SML); our executable face is `Codegen/` (D3) + D4 computable twins | never |
| X7 | auto2 automation (`SLTC_Automation` ML, `sep_time_steps.ML`, auto2 itself) | automation substrate, not calculus; architecture read at P4.A, carrier stays `fri`/`refine_vcg` (D-class precedent: the tower already made this call for Isabelle's ML tactics) | never |
| X8 | `Automatic_Refinement/Lib` substrate: `Misc.thy` (167 KB), `Refine_Util`, antiquotation/ML tooling (`Mpat_Antiquot`, `Mk_Term_Antiquot`, `Attr_Comb`, `Select_Solve`, `Anti_Unification`, `Named_Sorted_Thms`) | substrate role played by mathlib + Lean 4 metaprogramming; `Named_Sorted_Thms`' ordering guarantee already documented in `Sepref/IdOp.lean` | `Anti_Unification`: if Autoref heuristic quality (delta F6 work) demands it |
| X9 | Collections `Lib` oddments: `Robdd` (121.7 KB), tries, finger trees (`FT*`), `Dlist_add`, binomial/pairing-heap breadth | outside the source slices unconditionally assigned by P0; active heap coverage is the scheduled array-heap/prio-map family | P10 review only |
| X10 | splay trees & pairing heaps (`Splay_Tree_Analysis*`, `Pairing_Heap_*`, `IHT_Splay_Tree`) | amortized-analysis breadth beyond the three chosen exemplars; splay potentials are real-valued/log-shaped — poor fit for the ℕ-valued credit SL without new machinery; no consumer | a consumer needs self-adjusting structures |
| X11 | Edmonds–Karp / `Augmenting_Path_BFS` chain (Sepreftime, ≈146 KB) | exemplar role is already filled by the scheduled introsort and Kruskal sources; max-flow is not part of active P0–P10 | P10 review or a later consumer campaign only |
| X12 | independent AFP `Landau_Real_Products` decision procedure (73.9 KB + simproc ML), `Akra_Bazzi_Real`/`Approximation` numerics | P3.C ports only dependencies required by the selected IHT declarations; mathlib already supplies the Akra–Bazzi endpoint. Missing convenience automation becomes recorded debt, not a new source excursion | P10 review only |
| X13 | Sepreftime root layer (`HNR.thy`, `SepLog_Automatic`, `Set_Impl`, …) and IHT machine layer (`Heap_Time_Monad`, `Array_Time`, `Ref_Time`, `Transpile`) | superseded by the ESOP artifact's sepref (our primary source) and by our own machine layer; only the case studies, foreach, `moreCurr`, SLTC discipline, and asymptotics feed ports | never |
| X14 | Userguides (`Sepref_Guide_*`, ICF/Refine_Monadic userguides) | manuals, not port targets — they stay the workers' documentation, per the fidelity charter | — |
| X15 | surface syntax (`do`-macro front end); GenCF-style code export; concept surfaces; machine model; `lake update` | carried from the plan's "Not in scope" verbatim | per plan |
| X16 | skew-heap and RBT stretch rows formerly attached to P4.B/P5.D | useful breadth, but not unconditionally assigned by P0; “stretch” is not executable scope under the firewall | P10 review only |
| X17 | `IICF_Array.thy`'s length-carrying array family (`larray1_rel`, `larray_assn`, `la_replicate`, `la_replicate_init`, `la_grow_init`, `la_length`, `la_is_empty`, `la_get`, `la_set`, `larray_swap`, `la_free`, `larray_boundD`, `:233-398`) and the abstract `replicate_init` / `grow_init` families (`:11-60`, `:189-205`) | **Argued exclusion, 2026-08-02 (rev 5), resolving the negative-space row above.** Three halves, three reasons. (a) *Access* — `la_length`/`la_is_empty`/`la_get`/`la_set`/`larray_swap` duplicate landed, seam-proved `ArrayList` operations; `larray1_rel = br snd (\u03bb(n,xs). n = length xs)` is literally `BoundedArray.Wf`'s length invariant (`IicfDynamicArray.lean:321`). Porting them adds a second spelling of proved capital. (b) *Construction and growth* — subsumed **and improved** by P4.5: a zeroed bump allocation is O(1) where `la_replicate_init` and `la_grow_init` pay O(n), because the endorsed machine starts `mem := fun _ => 0` and a non-reusing allocator never returns a touched cell. Porting `larray` here would install a second, strictly worse mechanism for the job P4.5 exists to do. (c) *Deallocation* — `la_free`/`larray_mk_free` fall under P4.5's recorded exclusion of deallocation. **Basis amended 2026-08-02 (ledger E23):** the original citation — "the source's own evidence that its `MK_FREE` rule is the artifact's single `sorry`" — is void, because that `sorry` is inside a comment block and the artifact does prove `mop_oarray_free`. The clause survives on E23's own argument (non-reuse is what buys the O(1) allocation, so `free` either forfeits it or buys nothing); clauses (a) and (b) are independently sufficient, so the row is amended rather than reopened. Standing fact behind all three: `larray` lives in the superseded IICF (F6), and P4.5 ports its successor. **Revisit triggers:** (i) if P4.5.A's allocator fails to land, `la_replicate` and `la_grow_init` become the fallback route for sized construction and this row reopens immediately; (ii) `grow_init`'s *shape* is a required read for P5.E when it re-seats `ArrayList`'s append, since growth-with-init is exactly the operation append needs at capacity \u2014 consult it as a shape reference even though it is not ported; (iii) if a consumer needs a length-carrying array without `ArrayList`'s append/capacity machinery, reconsider. |

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

The original P0 source-volume estimates predate the Rev 4 scope firewall
and are superseded; they are not authority to pull adjacent source families
into a live phase. The tables above define the exact assignments, and the
Rev 4 campaign-plan budgets govern. Dependency shape is P1 → P2 → P3,
then P4, with P5 waves following their declared P1/P2/P4 dependencies;
P6–P8 follow the APIs they audit, P9 alone integrates the consumer, and P10
reviews backlog. P5's E7 finding makes its assigned rows derivations rather
than text transcription but does not widen that table.

Worker note for the P1 calibration wave: every brief must carry the
relevant extract (fetched fresh at the pin) — the extract files of the
tower campaign (`refinement-tower/p4-sepref-extracts.md`,
`p4-sepref-deep-extracts.md`) already hold the `Sepref_Rules.thy`
composition sections and should be the wave's starting point.
