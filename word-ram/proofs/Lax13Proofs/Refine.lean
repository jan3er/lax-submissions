import Lax13Proofs.Refine.Cost.ACost
import Lax13Proofs.Refine.NREST.Basic
import Lax13Proofs.Refine.NREST.Pw
import Lax13Proofs.Refine.NREST.Sanity
import Lax13Proofs.Refine.NREST.Rec
import Lax13Proofs.Refine.NREST.Combinators
import Lax13Proofs.Refine.Autoref.Attrs
import Lax13Proofs.Refine.Autoref.Relators
import Lax13Proofs.Refine.Autoref.Tagging
import Lax13Proofs.Refine.Autoref.Solver
import Lax13Proofs.Refine.Autoref.Param
import Lax13Proofs.Refine.Autoref.Phases
import Lax13Proofs.Refine.Autoref.IdOps
import Lax13Proofs.Refine.Autoref.FixRel
import Lax13Proofs.Refine.Autoref.Translate
import Lax13Proofs.Refine.Autoref.Tool
import Lax13Proofs.Refine.Autoref.BindingsHOL
import Lax13Proofs.Refine.NREST.DataRefinement
import Lax13Proofs.Refine.NREST.TimeRefinement
import Lax13Proofs.Refine.NREST.BackwardsReasoning
import Lax13Proofs.Refine.Ir.Syntax
import Lax13Proofs.Refine.Ir.Semantics
import Lax13Proofs.Refine.Ir.Assn
import Lax13Proofs.Refine.Ir.Wp
import Lax13Proofs.Refine.Ir.Triples
import Lax13Proofs.Refine.Ir.Heap
import Lax13Proofs.Refine.Ir.Attrs
import Lax13Proofs.Refine.Ir.SepSolver
import Lax13Proofs.Refine.Examples.Bfs
import Lax13Proofs.Refine.Examples.ArrayFill
import Lax13Proofs.Refine.Examples.AutorefTutorial

/-!
The refinement tower: a fidelity-first port of the Isabelle NREST/Sepref
stack onto the endorsed word RAM.

The campaign plan, the pinned sources, the component maps and the
deviation ledger live in `plans/word-ram/refinement-tower/design.md`;
the verbatim Isabelle definitions every module here is checked against
live in `plans/word-ram/refinement-tower/source-extracts.md`. Read the
design record first: it is what makes a departure from the source
citable, and each module's header records the departures that module
actually made.

This is P1's first two slices — the currency type, the NREST monad
core, and the recursion/loop combinators built on it:

* `Refine/Cost/ACost.lean` — `('a,'b) acost` (`Abstract_Cost.thy`),
  pointwise algebra and lattice, `cost n x`, `ECost`, and the resource
  subtraction `ResSub` / `-ᵣ` of `NREST_Type_Classes.thy` with its `ℕ∞`
  and `acost` instances.
* `Refine/NREST/Basic.lean` — the `nrest` datatype, its complete
  lattice, and `RETURNT` / `SPEC` / `consume` / `consumea` / `bindT` /
  `ASSERT` (`NREST.thy`).
* `Refine/NREST/Pw.lean` — `nofailT`, `inresT`, the pointwise
  principles, monotonicity, and the four monad laws at the source's own
  carriers.
* `Refine/NREST/Sanity.lean` — the executable gate (design record ledger
  D4): `#guard` spot checks and Plausible property checks of those laws
  at a finite carrier.
* `Refine/NREST/Rec.lean` — general recursion: the flat orderings,
  `mono2`, `RECT` / `RECT'` and their unfold and mono rules, the
  `refine_mono` seed lemmas, and the fuel approximants that make the
  fixed point executably checkable (`NREST.thy`, `RefineG_Domain.thy`,
  `Refine_Mono_Prover.thy`).
* `Refine/NREST/Combinators.lean` — `MIf` / `monadic_If`,
  `whileT` / `whileIET` / `monadic_WHILEIT`, and `FOREACH`
  (`NREST.thy`; `FOREACH` from AFP `NREST`'s `Refine_Foreach.thy`,
  which is where it exists at all).

and P1's second slice — the two refinement operators the tower composes:

* `Refine/NREST/DataRefinement.lean` — `conc_fun` / `⇓R` and `abs_fun`
  (`Data_Refinement.thy`), the `br` relation constructor, the bind and
  consume refinement rules, `nrest_rel`.
* `Refine/NREST/TimeRefinement.lean` — `timerefine` / `⇓C`,
  `timerefineA`, the `wfR`/`wfR'`/`wfR''` finite-support predicates, the
  exchange-rate composition `pp`, the identity rate `TId`
  (`Time_Refinement.thy`), and the `⇓R`/`⇓C` commutation of
  `NREST_Main.thy`.

Each of the two carries its own executable gate, in the `Sanity`
namespace of `Sanity.lean`.

and P1's third slice — backwards reasoning and the abstract VCG:

* `Refine/NREST/BackwardsReasoning.lean` — the resource type classes
  `nonneg` / `needname` / `drm` / `needname_zero`
  (`NREST_Type_Classes.thy`), the `gwp` predicate transformer with its
  `minus_cost` / `minus_potential` / `minus_p_m` layers, the bind rule,
  the `progress` side condition, the `[vcg_rules']` suite, the
  consequence rules, the well-founded loop rule and its `whileIET`
  vcg form, and a first `refine_vcg` attribute and tactic
  (`NREST_Backwards_Reasoning.thy`; `RECT_wf_induct` from `NREST.thy`,
  `lift_acost` from `Enat_Cost.thy`). Its header records the one
  refutation the port turned up: mathlib's truncated `Sub ℕ∞` does not
  satisfy the `needname` axiom `top - a = top`, so the source's own
  subtraction is used, under the name `ResSub` (declared in
  `Cost/ACost.lean`).

and P2's first wave — relators and the shared rule-database attributes:

* `Refine/Autoref/Attrs.lean` — the `relator_props`, `param` and
  `refine_rel_defs` databases (design record §10 default 3; a Lean
  attribute is unavailable to its own defining module, so the tags live
  in a module of their own).
* `Refine/Autoref/Relators.lean` — the relator zoo of AFP
  `Automatic_Refinement`'s `Relators.thy`: `relComp`, `SingleValued`,
  `br` (relocated from `DataRefinement.lean`), and `funRel` (`→ᵣ`),
  `prodRel` (`×ᵣ`), `optionRel`, `sumRel`, `listRel` with `fun_relI` /
  `fun_relD` / `list_rel_induct` and the `[relator_props]` mono family.
  Pure HOL, one layer below the monad: it imports no `NREST` module.
* `Refine/Autoref/Param.lean` — P2 wave B1: the parametricity rules of
  `Parametricity/Param_HOL.thy` and the `Let`-tagging helpers of
  `Param_Tool.thy`, the pure-HOL operator bindings of
  `Autoref_Bindings_HOL.thy` that the P2 acceptance example consumes
  (`nat` layer, `append`/`Nil`/`Cons`, the option constructors,
  `is_None`/`is_Nil`, `list_eq` with `autoref_list_eq_aux` and
  `list_eq_expand`), all in the `@[param]` database, and the seed
  `parametricity` tactic. Pure relation material like `Relators.lean`:
  no `NREST` module in its import closure.

and P2's wave B2 — the tag layer and the side-condition solver registry:

* `Refine/Autoref/Tagging.lean` — `Autoref_Tagging.thy`'s term
  protection (`PROTECT`, `ANNOT`, `OP`, `APP` with `$ᵃ`, `ABS`) and
  annotation (`rel_annot` / `:::`, `ind_annot` / `::#`), plus the
  interface layer of `Autoref_Id_Ops.thy` (`Interface`, `intfAPP`,
  `i_fun` / `→ᵢ`, `CONST_INTF` / `::ᵢ`, `ID_OP`). Its header records how
  Isabelle's axiomatic `typedecl` / `consts` are rendered without
  axioms, and why the module exists at all next to design record §7's
  four-file P2 skeleton.
* `Refine/Autoref/Solver.lean` — `Tagged_Solver.thy` / `Prio_List.thy`:
  the `TaggedSolver` registry (declared, with its environment extension,
  in `Attrs.lean` for the delta-B7 reason), the `declare_solver`
  command, and the `tagged_solver` / `_full` / `_step` / `_trace`
  dispatchers, whose failure messages name the tag dispatched on and
  every solver considered. Its header carries the two ML signatures the
  port is measured against and its honest-limitations list.

and P2's wave C — the Autoref phase pipeline and its entry point. The
design record §7 lists one module, `Autoref/Tool.lean`; the port keeps
the *source's* file split instead (`Autoref/Phases.lean`, delta P0), so
that each phase's constants, its calculus and its implementation stay in
one place and a reader can check a file against one Isabelle theory:

* `Refine/Autoref/Phases.lean` — `Autoref_Phases.thy`: the `Phase`
  record, the priority-ordered registry, the driver, and the `State`
  threaded through it (design record §3 P2 row 4, "locales carrying
  phase state → structures threaded through a `MetaM` pipeline"). Every
  pipeline failure is wrapped here in an envelope naming the phase and
  its priority.
* `Refine/Autoref/IdOps.lean` — `Autoref_Id_Ops.thy`: the `ID_OP`
  calculus, the `Autoref_Rel_Inf` calculus, `i_annot` / `:::ᵢ`, and the
  first two phases — `id_op` (priority 10: operation identification,
  `autoref_op_pat` rewriting, interface typing) and `rel_inf`
  (priority 20: relator skeletons threaded through the application
  structure by `CNV_ANNOT`).
* `Refine/Autoref/FixRel.lean` — `Autoref_Fix_Rel.thy`: `PRIO_TAG` and
  its family, `CONSTRAINT`, `PREFER_tag` / `DEFER_tag` / `GEN_OP`,
  `TYREL`, the priority-sorted rule database, and the `fix_rel` phase
  (priority 22).
* `Refine/Autoref/Translate.lean` — `Autoref_Translate.thy`:
  `autoref_APP` / `autoref_ABS` / `autoref_beta`, `REMOVE_INTERNAL`,
  `SIDE_PRECOND` with its `PRECOND` / `PRECOND_OPT` solvers, and the
  `trans` phase (priority 30) with its `REMOVE_INTERNAL_EQ` post-pass.
* `Refine/Autoref/Tool.lean` — `Autoref_Tool.thy` (and
  `Autoref_Gen_Algo.thy`, folded in): the four phases registered in the
  source's order `id_op`(10) → `rel_inf`(20) → `fix_rel`(22) →
  `trans`(30), the `GEN_ALGO` / `GEN_OP` solvers, the `autoref` tactic
  with the source's `trace` / `debug` / `keep_goal` flags and `phases:`
  argument, and the `autoref_synth` command — the Lean vehicle for the
  source's `schematic_goal … by autoref` plus `concrete_definition`.
* `Refine/Autoref/BindingsHOL.lean` — `Autoref_Bindings_HOL.thy`: the
  `autoref_rules` database (wave B1's bindings, tagged across the module
  boundary), the generic layer under `PRIO_TAG_GEN_ALGO`, `autoref_hd`,
  `autoref_list_eq` with its `GEN_OP` premise, the `autoref_op_pat`
  rules, and structural expansion with the `STRUCT_EQ` solver.

and P3's wave A — the IR, the one layer of the tower the sources do not
have (ledger D2/D3), whose *rule granularity* — one op, one currency,
one future `hn_refine` rule — is what P4's fidelity consumes:

* `Refine/Ir/Syntax.lean` — the deep three-address syntax of design
  record §6: `Val`, `Operand` (cells and literals), `Cond`
  (`eq` / `lt`), and `Com` — `const`, `copy`, the nine `binop`s (IMP+'s
  own `Bop`, reused so that "exactly IMP+'s `Bop`" is true by
  construction), `aget`, `aset`, `seq` / `ite` / `while` and `skip` —
  together with the sixteen op currencies (`ir.add`, …) that the
  semantics charges, wave B's triples pay in and P5's price map is
  indexed by. Its header records what is deliberately *absent*
  (alloc/free, tapes, calls and recursion, `len`) with the ledger entry
  for each, and pins by `#guard` every arithmetic convention the IR
  inherits from the machine.
* `Refine/Ir/Semantics.lean` — `State` (partial, tape-free, aliasing-free
  by names) and the cost-indexed big-step relation `BigStep c s s' κ`
  over `ACost String ℕ`, mirroring `Imp.BigStep` construct for
  construct: determinism, the inversion suite the wave-B `wp` unfolds
  against, cost additivity over `seq`, the loop's guard unfolding, and
  the frame-shaped invariants that no op grows the name space or resizes
  an array. Its D4 gate is the fuel-indexed evaluator `evalFuel` with
  agreement in both directions, three programs pinned by final state and
  exact cost vector, Plausible property checks of the loop's cost as a
  function of its iteration count, and two negative controls.

and P3's wave B — the IR's separation logic with time credits, ported
from `Sep_Generic_Wp.thy`, `Sep_Algebra_Add.thy`, `Frame_Infer.thy` and
`LLVM_Shallow_RS.thy` (extracts `p3-ir-sl-extracts.md`,
`p3-sl-deep-extracts.md`):

* `Refine/Ir/Assn.lean` — the separation algebra and the assertion
  language: the class stack `PreSepAlgebra` → `SepAlgebra` →
  `StrongerSepAlgebra` → `UniqueZeroSepAlgebra` with instances for
  `Tsa` (the source's `tsa_opt`), maps, pairs and the credit half;
  `∗` / `□` / `⌜⌝` / `EXACT` / `purePart` / `∃ᵃ` / `⊢` and their laws;
  `FST` / `SND`; the carrier `AState = (Cells Val × Cells (List Val)) ×
  ECost` (the source's `ll_astate` at named cells, ledger D2) with
  `¤c` (`$c`), `¤¤n k` (`$$`), `GC`, `x ↦ᵥ v`, `a ↦ₐ xs`; `STATE` /
  `POSTCOND` / `irα` / `irSTATE`; and the five extraction lemmas the
  triples run on. Its D4 gate checks the PCM laws by computation on a
  decidable image of the carrier and carries the two negative controls
  (a name cannot be owned twice; different balances are different
  assertions).
* `Refine/Ir/Wp.lean` — `generic_wp_defs` / `generic_wp` as `htripleF` /
  `htriple` / `htriple_as_F_eq` plus the class `WpCommInf`, from which
  `frame_rule`, `cons_rule` and `htriple_to_gc` follow; the
  `cost_framework` locale as a class over `(I, minus)` with its six
  assumptions *proved* at the IR's instance
  (`leCostECost` / `minusECost`, the source's
  `le_cost_ecost` / `minus_ecost_cost`); and `Ir.wp` over `BigStep`,
  with `wp_comm_inf` from determinism, one equation per constructor,
  `wp_seq` (the source's `wp_bind`), `wp_ite`, `wp_while_unfold` and the
  well-founded `wp_while_wf`.
* `Refine/Ir/Triples.lean` — the per-op credit-carrying triples in the
  mould of `ll_load_rule` / `ll_store_rule` (`skip`, `const`, `copy`,
  one rule for all nine `binop`s plus its in-place instance, `aget`,
  `aset`), each in an exact and a garbage-collecting form
  (`irTriple` / `irHtriple = htripleGc GC irα`, the source's
  `llvm_htriple`), the structural rules `seq` / `ite` and the
  invariant-and-measure loop rule `while_triple`
  (`llc_while_annot_rule`). Its D4 gate proves the composed triple for
  wave A's `roundtrip`, runs it end to end at wave A's own state, drives
  wave A's `countdown` through the loop rule with per-iteration credits,
  and shows that a triple with too few credits is not derivable.
* `Refine/Ir/Heap.lean` — P4.5.A.1's range ownership (`ll_range`, ledger
  **E25**): the assertion `p ↦ₕ xs` over `AState`'s reserved-heap
  component, split / join / single-index focus as *equations*
  (`ptoH_append`, `ptoH_focus`, `ptoH_extract`), and the heap-view
  `aget` / `aset` triples in `Triples.lean`'s own shape and logic. Its
  gate carries both negative controls decision D-A1 turns on —
  overlapping ranges do not compose, and the heap name is unownable in
  the whole-name view — plus a non-vacuity witness at a concrete state.

and P3's wave C — frame inference and the phase's acceptance:

* `Refine/Ir/Attrs.lean` — the five rule databases of `Frame_Infer.thy`
  and `Basic_VCG.thy` (`fri_prepare_simps`, `fri_rules`,
  `fri_red_rules`, `fri_end_rules`, `vcg_rules`), declared in a module
  of their own for the import-time constraint P1's delta B7 documents.
* `Refine/Ir/SepSolver.lean` — the port of `thys/lib/Frame_Infer.thy`:
  the tags `FRI_END` / `FRAME_INFER` / `FRAME` / `ENTAILS` /
  `IsSepRed`, the four structural rules `fri_prepare` / `fri_end` /
  `fri_step_rl` / `fri_reduce_rl` with `fri_startI`'s two entry clauses,
  the credit reductions (`is_sep_red` at `¤¤n j` versus `¤¤n k`), the
  `GC` absorption chain, `fri_extract`, and the `start / extract /
  round / end` search loop as a `MetaM` proof-term builder — rotation
  rendered as an index-selection permutation equality through
  `fri_prems_cong`, no higher-order unification anywhere. Its user
  surface is `fri` (both front ends), `ir_entails`, `fri_trace`, and
  `ir_frame` / `ir_frame_gc`, the latter two applying a triple through
  `irTriple_frame` / `irHtriple_frame` — the triple-level form of
  `htriple_vcg_frame_erule`, whose two side conditions are one `fri`
  call each. It registers wave B's `aget_rule_pure` and its own
  `aset_rule_pure` into `vcg_rules` for P4. Its D4 gate closes
  six- and seven-conjunct entailments under nontrivial permutations,
  splits credits across the turnstile in both directions, absorbs
  leftovers into `GC`, and pins four failure messages with
  `#guard_msgs` through a `#fri_report` command that runs the solver on
  a synthetic goal and leaves nothing in the environment.
* `Refine/Examples/ArrayFill.lean` — P3's acceptance: the array get,
  set and fill *programs*, with credit-carrying triples whose frame
  reasoning goes through the solver and nowhere else (no
  `sepConj_assoc` chain, no `ac_rfl`, no `irSTATE_rot`). `fill` is
  `while i < n do { A[i] := v; i := i + one }`, proved by
  `while_triple` against an invariant carrying `k` copies of the
  per-iteration payload `ir.while + ir.aset + ir.add`; its triple's
  credit vector is `(n+1)·ir.while + n·ir.aset + n·ir.add`. Its gate
  runs the triple down to a `BigStep` at a concrete state with the cost
  vector `#guard`-pinned, and checks the cost-as-a-function-of-`n`
  claim on wave A's executable twin with Plausible.

and P2's acceptance:

* `Refine/Examples/AutorefTutorial.lean` — the eight derivations that
  close `Autoref_Bindings_HOL.thy`'s `subsection "Examples"`, the
  reproduction target the extraction recommended, run *mechanically*:
  every concrete term and every relator below is the pipeline's, no rule
  is applied by hand. Its D4 gate `#guard`s each synthesized term
  against the abstract term it refines, and two negative controls check
  — message for message — that a pipeline failure names its phase and
  its unmet side condition.

and P1's acceptance program, design record §10.4:

* `Refine/Examples/Bfs.lean` — the masked depth-capped BFS of
  `Lax3Proofs.RamBfs`, specified as one `NRest.spec` (the
  threshold-iff postcondition, an explicit currency budget) and
  refined abstract-to-abstract by `gwp_specifies_I` + `refine_vcg`,
  with the classical frontier invariant and a touched-only energy
  annotation on the `whileIET` term. Its header records the package
  adjustment of §10.4 (mathlib graph vocabulary in place of Lax3's,
  the postcondition shape unchanged so P7 consumes it) and its own
  executable D4 gate.
-/
