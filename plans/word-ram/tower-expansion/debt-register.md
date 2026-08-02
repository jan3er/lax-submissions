# Tower expansion debt register

P0 inventory, 2026-07-31. This is the fine-grained queue behind P6 and
the cross-phase items P1–P8 must retire on the way. It reconciles the
tower verdict, the refinement-tower progress log, the ND-MC readiness
wave, and live module headers. It is intentionally more precise than the
plan's phase prose: an item is closed only by a cited implementation or a
recorded exclusion.

Status vocabulary:

- **OPEN Pn** — owned by that tower-expansion phase;
- **VERIFY P6** — implemented already; P6 checks imports, tests, and stale
  callers before marking it closed here;
- **CLOSED** — evidence already exists and no cleanup remains;
- **EXCLUDED** — intentionally absent, with the reason in `port-map.md` or
  `ledger.md`.

## A. Signature and composition machinery

| id | status | debt | evidence / source | closure test |
|---|---|---|---|---|
| SIG-1 | VERIFY P6 | Dependent `hfcomp` was an open tower item. | `Sepref/Rules.lean` now exports `hfcomp_dep`, `hfcomp_dep_sv`, and a dependent bind consumer; ND-MC P0.1 records green. | Root import sees the positive controls and no consumer carries a local substitute. |
| SIG-2 | CLOSED | `to_hnr`/`to_hfref`, `comp_PRE`, and the source's `FCOMP` composition attribute were absent. | `Sepref/Signature.lean` ports the exact precondition/converters and both composition branches; `SignatureTool.lean` exports `sepref_fcomp`/checked mode. Ledger E10 records the Lean frontend rendering. | Direct `hfref`, generalized `hnRefine`, dependent-result, and pure `fref ∘ fref` gates compile without applying `hfcomp` by hand. |
| SIG-3 | CLOSED | Iterated dependent composition had no flattening lemma. | `Sepref/SignatureFlatten.lean` exports `hrrCompDep_flatten`, the correlated residue I/E family, and a two-stage consumer. | The module also refutes independent input/output relation composition, pinning the shared-witness requirement. |
| SIG-4 | CLOSED | `hr_comp_precise`, `hr_comp_the_pure`, `hr_comp_assoc`, and `hr_comp_prod_conv` were listed as skipped. | `SignatureNorm.lean` ports the three active source laws and their pure helper; source inspection proves `hr_comp_precise` is inside a comment and declares no theorem. | Root import compiles the normalizer; checked FCOMP exercises identity/pure normalization and deterministic residue rejection. |
| SIG-5 | CLOSED | `one_time`/`one_time_attains_sup` and the `attains_sup_mop_*` family were absent. | `SignatureNorm.lean` ports `oneTime`, return/consume/assert/fail/spec closure, `one_time_attains_sup`, and return/spec helpers. | A non-single-valued two-result SPEC gate attains its supremum by uniform time rather than relation functionality. |
| SIG-6 | CLOSED | `sepref_definition`/`sepref_thm` prepared only hand-holed `hnRefine` goals. | `Sepref/Definition.lean` now prepares `hfref` targets; `SignaturePrep.lean` and `Examples/BfsQSignature.lean` are root-imported controls. | `bfsQFromSignature` contains no written `hnRefine`; its generated result tuple and `Com` are definitionally equal to `bfsQSynth_impl`. |
| SIG-7 | CLOSED | `sepref_register`, `intf_of_assn`, and TYPE/interface annotations were absent. | `Sepref/Register.lean` provides assertion-interface lookup/fallback and both inferred and explicit registration forms; existing `CTYPE_ANNOT` supplies occurrence overrides. Ledger E11 records generic monadification. | The registered eight-array operator identifies at eight `ArrayI` inputs inferred from `arrayIAssn`; the signature-only eight-array phase also synthesizes end to end. |
| SIG-8 | CLOSED | `sepref_decl_op`, `sepref_decl_intf`, and `sepref_decl_impl` command layer is absent. | `Sepref/IntfUtil.lean`; source `Sepref_Intf_Util.thy`; ledger E12. | A fresh parameter-capable nominal interface, relation mapping, operation, checked-FCOMP implementation, and public rule registration compile without bespoke metaprogramming. |

## B. NREST and loop layer

| id | status | debt | evidence / source | closure test |
|---|---|---|---|---|
| NR-1 | OPEN P6 | The source's `inres` section was never ported. | Tower verdict open items; `NREST/Basic.lean`/`Pw.lean` currently expose only `inresT`. | Port the source section and add a gate covering its intended carrier, without resurrecting the refuted same-carrier `pw_conc_inres` statement. |
| NR-2 | CLOSED | `pw_conc_inres` in its same-carrier reading is refutable. | `NREST/DataRefinement.lean` records the witness and the hypothesis-free replacement. | No action; this row prevents a future worker treating it as an unfinished proof. |
| NR-3 | OPEN P6 | `leof` was skipped; `augment_res` premises are unfolded instead. | Tower P4 wave-A record; source `Refine_Leof.thy`. | Port `Refine_Leof.thy` and replace local unfoldings where the named rule applies. |
| NR-4 | OPEN P6 | `progress_bind` is proved locally in `Examples/Bfs.lean`. | File header around `progress_bind`; intended home is backwards reasoning/Pw. | Move the reusable lemma and leave the example importing it. |
| NR-5 | OPEN P6 | `le_spec_of_bindT_returnT` and `bindT_returnT_gen` are in downstream modules. | Tower verdict thaw queue; intended home `NREST/Pw.lean`. | Move without duplicate declarations and keep all old consumers green. |
| NR-6 | OPEN P6 | `bindT_mono_res`, `mono2_monadicWhileBody`, and `monadicWhileIT_unfold_pure` have thaw-placement debt. | Tower P4 progress log. | Each reusable NREST lemma lives in the lowest non-cyclic module that states its vocabulary. |
| NR-7 | VERIFY P6 | The unfueled `hnr_while` rule landed after the tower verdict refuted the proposed global fuel lemma. | `Sepref/CombRules.lean` R0/D-b; `NREST/Rec.lean` `NoFuelBound.no_fuel_bound`; ND-MC P0.3. | Root tests exercise `hnr_while`; no rule database lookup requires `LOOP_VARIANT`. |
| NR-8 | OPEN P6 | Consumers still carry obsolete `LOOP_VARIANT` hypotheses and compatibility wrappers. | `Examples/BfsQ*.lean`, `Iicf/Iicf{Stack,Queue,Csr,Bitmask,TrailArray}.lean`; comments already say the DB no longer reads them. | Remove dead hypotheses/annotations at every site while retaining measured-rule tests as calculus coverage. |
| NR-9 | CLOSED | Currency-vector `nfoldli`/FOREACH and its refinement rules were absent. | `NREST/Foreach.lean`, `Sepref/Foreach.lean`; ledger E5. | The synthesized 2-member walk in a 100-cell carrier is definitionally pinned and proved equal to its abstract `nfoldli` plus member-count guard cost. |

## C. Sepref frame, copy, and operator layer

| id | status | debt | evidence / source | closure test |
|---|---|---|---|---|
| SEP-1 | OPEN P6 | `sepref_copy_rules` is declared but empty. | `Sepref/Attrs.lean`; source sites are `COPY` in `Sepref_Monadify.thy` and `hnr_pure_COPY`/`fold_COPY` in `Sepref_Tool.thy`. No source `Sepref_Copy.thy` exists. | A destructive operation with a still-live parameter synthesizes the required `Com.copy` through the DB. |
| SEP-2 | OPEN P6 | `mop_move` has no rule with a live destination. | Tower verdict; `IicfTrailArray.lean` and `BfsQSynth.lean` document write-twice/in-place dodges. | An exercise overwrites a live destination without junk ordering tricks. |
| SEP-3 | OPEN P6 | `frameMatch` splits goal-side `prodAssn` but not rule-side tuples. | Tower verdict and IICF P6 findings. | A rule returning a tuple matches a tuple state symmetrically, without routing through a bespoke `mopPair`. |
| SEP-4 | OPEN P6 | Two array assertions inside one tuple can fail `proveConjEq` under a valid permutation. | Tower P6 finding; current workaround frames read-only arrays. | A pinned reproducer synthesizes in situ or the limitation is re-ledgered with a source-backed boundary. |
| SEP-5 | OPEN P6 | Operator selection does not backtrack after a frame failure. | Tower P6 finding; junk-destination binop can shadow the in-place rule. | A negative-first rule ordering still reaches the applicable rule, or a documented deterministic priority discipline makes the bad ordering unrepresentable. |
| SEP-6 | OPEN P6 | `hnr_bind` blocks value-dependent guard rules. | Tower P6 finding; workaround branches on the returned value and converts back. | A minimal returned-value guard synthesizes directly, or the conversion becomes a named reusable combinator. |
| SEP-7 | OPEN P6 | P6-A and P6-B duplicate the composite-assertion convention (`hnRefine_res_cast'` versus `hnRefine_reinterp`; `hnr_pre_*_conv` versus `hnr_pre_ex_pure`/`hnr_pre_pure_star`). | `Iicf/Basic.lean`, `Iicf/IicfStack.lean`, tower verdict. | One canonical family remains; downstream modules import it from the shared home. |
| SEP-8 | OPEN P6 | Init-from-junk conventions diverge: concrete contents versus `junkArrayOfLen`. | Tower P6 merge finding. | One public rule shape is chosen and all structures use it; any lower-level alternate is clearly private. |
| SEP-9 | OPEN P6 | `mopPair`, `ExchOk`, and `irWhileIT_mono` are not in their named homes. | Tower verdict thaw queue; definitions are spread across Sepref acceptance/combination modules. | Move each to the lowest shared module without import cycles. |
| SEP-10 | OPEN P6 | Monadify has no general duplicate-argument split. | `Ir/SepSolver.lean` handoff; source copy discipline is related but not identical. | `x := y ⊕ y` synthesizes without a bespoke operation rule. |
| SEP-11 | OPEN P6 | `fri_exI`/goal-side existential support is absent. | `Ir/SepSolver.lean` P4 handoff. | A frame target containing `∃ᵃ` is solved by the registered calculus. |
| SEP-12 | OPEN P6 | `PRECOND`/`PRIO` side-condition registry is absent from `fri`. | `Ir/SepSolver.lean` D-ac/D-ae; P3 uses a fixed tactic list. | Side conditions dispatch through a named, inspectable registry and failure names the attempted solvers. |
| SEP-13 | OPEN P6 | `sepImp` has no consumer and no gate. | `Ir/Assn.lean`; tower P3 handoff. | Either add the source-shaped consumer/test or explicitly exclude it as dead vocabulary. |
| SEP-16 | OPEN P4.5 | The allocator's availability size is related to `Layout.span` only in prose. | `Refine/Sepref/HeapAlloc.lean` header, D-A3; a first attempt stated `avail_size_le_span` / `avail_size_lt_two_pow`, which mentioned neither `avail` nor `heapName` and were deleted for that reason (they also bought a `Refine/Sepref → Compile` edge). | A theorem at the `Codegen/` boundary relating the reserved heap array's length `ext heapName` to `B` and thence to `FitsWords.span`, stated where `initEnv` and `Solves` already live — not in a refinement rule. |
| SEP-14 | OPEN P7 | Dead scratch cells accumulate across bind blocks. | ND-MC P0.5 scaling verdict names release-at-`hnr_bind` as first-payoff intervention. | The P7 probe measures the resulting exponent and pins semantic equivalence. |
| SEP-15 | OPEN P7 | `fri`/`proveConjEq` walks long conjunct lists repeatedly. | ND-MC P0.5: `fri` is 28% at 100 ops; rule pre-match is below 0.5%. | P7 pins ≤60 s at 3–5× BFS and `fri` share ≤15%, or lands a measured ceiling verdict. |

## D. Autoref and database breadth

| id | status | debt | evidence / source | closure test |
|---|---|---|---|---|
| AR-1 | OPEN P6 | The `param_fo` first-order rule conversion and `to_relAPP` relator-prefix conversion attributes are absent. | `Autoref/Param.lean` gap list and `p2-autoref-extracts.md`; the latter needs a Lean rendering because this port has no Isabelle `relAPP` syntax. | Port both transformations or ledger the exact Lean-substrate replacement, then exercise each on a source-shaped rule. |
| AR-2 | OPEN P6 | `ID_abs`/`ABS` has no dedicated acceptance exercise. | Tower P2 backlog; `Autoref/Tagging.lean` defines the vocabulary. | A higher-order tutorial example passes through identification, relator fixing, and translation. |
| AR-3 | OPEN P6 | `Lib/Indep_Vars.thy` / `INDEP` is absent. | P0 source diff; prerequisite of `autoref_higher_order_rule`. | Port the small theory and consume it in AR-2 or explicitly remove the dependent higher-order target. |
| AR-4 | OPEN P6 | `Refine_Heuristics.thy` was skipped. | P0 source diff, 7.1 KB. | Port its source-visible rules and pin a case where they change a residual goal. |
| AR-5 | OPEN P6 | `Refine.lean` is a stale aggregator: imports stop before Sepref/IICF/Codegen and the narrative ends at early P2. | Live file inspection in P0. | Root aggregator imports the public capital modules and describes the landed layer graph without importing telemetry spikes. |
| AR-6 | OPEN P6 | Core Sepref rule DBs have only indirect acceptance coverage. | P0 baseline caveat. | Add a compact direct gate enumerating/populating each public DB and pin at least one positive lookup per DB. |
| AR-7 | OPEN P6 | Six Autoref databases are missing: `autoref_op_pat_def`, `autoref_hom`, `autoref_rel_intf`, `autoref_rel_indirect`, `autoref_post_simps`, and `autoref_ga_rules`. | `p2-tool-extracts.md` registry; gaps are named in `IdOps.lean`, `Translate.lean`, and `Tool.lean`. | Register, populate, and directly exercise all six, or give an item-by-item exclusion under rule 4. |
| AR-8 | OPEN P6 | `STRUCT_EQ` is registered but unexercised. | Tower P2 backlog; Collections is the named consumer. | A collection-shaped equality reaches structural expansion through the normal pipeline. |
| AR-9 | OPEN P6 | Translation rule choices have no trace surface. | Tower P2 backlog; phase failures are legible, successful choice paths are not. | Trace mode names the chosen translation rule and rejected alternatives without changing synthesis. |
| AR-10 | OPEN P6 | The DB-size `#guard_msgs` canary is brittle as breadth grows. | Tower P2 flagged queue. | Replace it with a semantic lookup/ordering check or record why an exact-size canary remains intentional. |

## E. Examples, tests, and public-surface cleanup

| id | status | debt | evidence / source | closure test |
|---|---|---|---|---|
| TEST-1 | OPEN P6 | `filled` lives in `Examples/ArrayFill.lean` despite reuse potential. | Tower verdict thaw queue. | Move it and its generic lemmas to the lowest appropriate list/array helper module. |
| TEST-2 | OPEN P6 | `Examples/T1Probe.lean` is telemetry marked for deletion or reduction after its fix landed. | File header; ND-MC T1/T2 waves are green. | Delete it or retain only a small regression gate that fails on the old bug. |
| TEST-3 | OPEN P6 | `Sepref/Examples/WordAssnSpike.lean` and `Examples/BfsQBounded.lean` are rejected-route spikes, not capital. | P0 baseline caveat; ND-MC P0.2 adopted `BRefine`, rejected `wordAssn`. | Reduce to named negative controls or move their findings to records and delete the modules. |
| TEST-4 | OPEN P6 | Filter-count correctness is sample-guarded rather than proved (`fcCountOf = List.filter.length`). | Tower verdict; `Codegen/Examples/EndToEnd.lean` guards. | Prove the general equality and make the executable guard a corollary. |
| TEST-5 | OPEN P6 | Reverse's executable twin equals `List.reverse` only on samples. | Tower P5 backlog; `Codegen/Examples/EndToEnd.lean`. | Prove the general twin equality from the `List.set` invariant. |
| TEST-6 | OPEN P6 | A writes-none `Spec` combinator is missing. | Tower P5 backlog. | Add the combinator and replace one hand-expanded proof in the codegen examples. |
| TEST-7 | OPEN P6 | Per-toy value bounds such as `B x = x.sum + 2` are deliberately coarse. | Tower P5 telemetry. | Decide whether a shared tight bound API has a consumer; tighten it or explicitly close as example-only. |
| TEST-8 | VERIFY P6 | Recursive-arena trail acceptance was missing at tower close. | `Examples/TrailRecursion.lean`; ND-MC P0.4 records first-try synthesis and n-free cost signature. | Root gate imports the acceptance and retains the negative naive-shape control. |
| TEST-9 | VERIFY P6 | The synthesis-scaling artifact was deleted after measurement. | ND-MC rebase plan records 16→100 ops, exponent 1.28–1.35, and profile split. | P7 reconstructs a pinned reproducible probe before optimizing; P6 merely verifies the record has a stable entry point. |
| TEST-10 | OPEN P8 | Standing slot and cost audits exist only as prose/manual probes. | Plan ledger E4. | `#slot_sweep` and `#cost_probe` reproduce the known B7 misses from pre-repair fixtures. |

## F. Explicit non-debt

The following are not permitted to drift back into the queue without the
listed trigger:

| item | disposition |
|---|---|
| Same-carrier `pw_conc_inres` | Refuted; NR-2 is the permanent record. |
| Global theorem `nofailT (RECT B s) → ∃ n, fuelIter B n s = RECT B s` | Refuted in `NREST/Rec.lean`; the unfueled rule uses fixed-point induction instead. |
| DiscrTree indexing as the first scaling repair | Rejected by measurement; P7 starts with SEP-14/SEP-15. |
| Deterministic O(1) hash-map implementations | Excluded by ledger E9 until randomized-cost infrastructure or a forcing consumer exists. |
| LLVM layers, GenCF, ICF locale/codegen machinery, auto2, and source userguides | Excluded in `port-map.md` X1–X4, X6–X8, X13–X15. |

## G. P6 completion rule

P6 is complete only when every row marked **OPEN P6** or **VERIFY P6** is
changed in this file to **CLOSED** or **EXCLUDED**, with a commit/theorem
or ledger citation. Moving a row to another phase requires a reason in the
campaign progress log; silently dropping rows is not a valid disposition.
