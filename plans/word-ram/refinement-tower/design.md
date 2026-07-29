# Refinement tower — the P0 design record

Written 2026-07-29 (P0 of `../refinement-tower-plan.md`, rev 3).
**Status: complete; flagged for Jan's post-hoc review** (plan flag 4: no
hard gate — P1 may start; review comments fold in as revisions).
Companion: `source-extracts.md` holds the verbatim source definitions
this record argues from.

Everything here is subordinate to the fidelity charter: the sources'
design wins by default, deviations live in the ledger at the end, and
the ledger entry — not this record's prose — is the citable form of any
departure.

## 1. Sources, pinned

| source | pin | canonical for |
|---|---|---|
| AFP `Refine_Monadic` (Lammich) | AFP for **Isabelle2025-2** (release 2026-02-06), [entry](https://www.isa-afp.org/entries/Refine_Monadic.html) | refinement-calculus rule organization, `refine_vcg` architecture, mono prover, WHILE/FOREACH/REC combinator design |
| AFP `Automatic_Refinement` (Lammich) | AFP Isabelle2025-2, [entry](https://www.isa-afp.org/entries/Automatic_Refinement.html) | relator zoo, parametricity rule format, tagged solvers, Autoref phase pipeline |
| AFP `Refine_Imperative_HOL` (Sepref, Lammich) | AFP Isabelle2025-2, [entry](https://www.isa-afp.org/entries/Refine_Imperative_HOL.html) | Sepref phase architecture and debugging methodology at maturity (its guides `Sepref_Guide_Quickstart`/`_Reference` are the manuals); IICF interface style |
| AFP `NREST` (Haslbeck) | AFP Isabelle2025-2, [entry](https://www.isa-afp.org/entries/NREST.html) | the maintained nrest core (6 theories) |
| `isabelle_llvm_time` (Haslbeck–Lammich, ESOP'21 artifact) | github.com/lammich/isabelle_llvm_time @ **42dd7f5** (master tip, 2021-03-02) | **the only place the full cost-carrying stack exists**: currency `acost`, nrest over currencies, `timerefine`, cost-carrying `hn_refine`, Sepref-with-cost, SL with time credits, IICF-with-cost |
| `isabelle_llvm` (Lammich) | github.com/lammich/isabelle_llvm branch `2023` @ **b44b639** (2024-03-25; v2.0 line, Isabelle-2023) | the basic-layer shape at maturity, two-stage lowering, evidence the back end is swappable |
| `Std.Do` + `Std.Tactic.Do` | pinned toolchain `leanprover/lean4:v4.30.0` (local: `Std.Do.{SPred,WP,Triple,PostCond}`, `mvcgen`) | local evidence that attribute-driven Hoare/VCG machinery hosts well in Lean 4; *not* a dependency (see fidelity note F5) |

Papers (the manuals the charter says must stay usable):
Haslbeck–Lammich, *Refinement with Time* (ITP'19); Haslbeck–Lammich,
*For a Few Dollars More* (ESOP'21; extended TOPLAS'22); Haslbeck,
*Verified Quantitative Analysis of Imperative Algorithms* (TUM thesis
2021, [mediaTUM 1596032](https://mediatum.ub.tum.de/1596032)); Lammich,
*Automatic Data Refinement* (ITP'13); Lammich, *Refinement to
Imperative/HOL* (ITP'15, JAR'19); Lammich, *Generating Verified LLVM
from Isabelle/HOL* (ITP'19); Lammich, *Refinement of Parallel
Algorithms down to LLVM* (ITP'22, JAR'24).

**Where sources differ, canonicity is:** `isabelle_llvm_time` for
anything cost-carrying (it is the paper artifact; frozen but complete);
the AFP entries for anything the artifact shares with the maintained
no-cost originals (rule organization, phase internals, tool
architecture — the AFP text is newer and documented); `isabelle_llvm`
branch `2023` for the concrete-layer shape. The artifact's `thys/sepref`
deliberately reuses the AFP Sepref file names one-for-one, so the two
can be read side by side; we inherit that property (§4).

## 2. What the sources are, against our substrate

One paragraph of orientation, because every mapping below leans on it.
The Isabelle stack is: **NREST** — a nondeterminism monad whose results
carry a resource valuation (`α → Option cost` under a top element
`FAIL`), ordered pointwise, with `bindT` summing consumed resources;
proofs at this level are ordinary math over `⊑`. **Autoref** — a
relator language and rule databases that mechanize data refinement
between abstract types. **Sepref** — a syntax-directed synthesizer: a
judgment `hn_refine Γ c Γ' R m` ("imperative `c` refines abstract `m`
under ownership `Γ`, delivering `R`-related results, paying costs out
of time credits"), plus a four-phase pipeline that *constructs* `c` and
its proof from `m` by composing registered `hn_refine` rules, with
frame inference filling the gaps. **LLVM layer** — a shallow monadic
concrete language with a separation logic over (memory, credit-balance)
states and a wp-based VCG; the final printing to LLVM text is trusted.
Our substrate differs in three structural ways: the concrete bottom is
the endorsed word RAM reached through IMP+ (aliasing-free named
environment, no heap, no allocation, tapes for I/O); the concrete
program must be a *deep* term (P5 verifies codegen instead of trusting
a printer); and the metaprogramming/type-theory substrate is Lean 4
(DTT, weaker HOU, discrimination trees, no locales). Every delta in the
maps below traces to one of these three or to the Isabelle/ML → Lean 4
translation.

## 3. Component maps, phase by phase

Format: source artifact → Lean counterpart (module names under
`Lax13Proofs/Refine/`, see §7) → substrate delta. "=" means ported with
no delta beyond notation.

### P1 — NREST core

| source artifact | Lean counterpart | substrate delta |
|---|---|---|
| `('a,'b) acost = acostC ('a ⇒ 'b)`, pointwise `0/+/≤`; `cost n x`; `ecost = (string, enat) acost` (`Abstract_Cost.thy`, `Enat_Cost.thy`) | `Cost/ACost.lean`: `structure ACost (κ γ) where toFun : κ → γ`, pointwise instances; `ECost := ACost String ℕ∞` | `enat → ℕ∞`; currency names stay `String` (F1). Plain functions + a `wfR`-style finite-support predicate, **not** `Finsupp` (F2) |
| `('a,'b) nrest = FAILi \| REST ('a ⇒ 'b option)`, `'b :: {complete_lattice, monoid_add}` | `NREST/Basic.lean`: `inductive NRest (α γ : Type)` with `fail`, `rest (α → WithBot γ)`; classes on the operations, not the type | HOL sort constraints → instance arguments on operations. `'b option` under the source's None-bottom pointwise order *is* mathlib's `WithBot γ` — same object, mathlib's name, its lattice for free (F6). Monomorphic universes (`Type`) per plan watch item |
| `≤` (flat under `FAILi` = top), complete-lattice instance on nrest | same file: `LE`/`CompleteLattice` instances | = (mathlib order library replaces HOL's) |
| `RETURNT`, `SPECT`, `SPEC P t`, `FAILT = ⊤`, `SUCCEEDT = ⊥`, `consume`, `bindT = Sup {consume (f x) t₁ …}`, `ASSERT` | same names: `NRest.returnT`, `.spec`, `.consume`, `.bindT`, `.assert` | `Sup` over a set-comprehension → `sSup` over `Set (NRest α γ)`; monad laws ride the lattice exactly as in the source |
| pointwise reasoning: `nofailT`, `inresT`, pw lemma suite (`NREST.thy`, `NREST_Misc.thy`) | `NREST/Pw.lean`, same names | = |
| `RECT` (fixed point over the flat/lattice structure), mono framework (`Refine_Mono_Prover`, `NREST_Type_Classes.thy`) | `NREST/Rec.lean`: fixpoint via mathlib's lattice `lfp/gfp` on the nrest order; monotone side goals | Isabelle's mono *prover* (ML) → `@[refine_mono]` simp/aesop set + mathlib `mono`-style tactic. No `partial_function` package: define the fixpoint as the source's own lattice fixpoint, which needs no package |
| `WHILET`/`WHILEIT`, `FOREACH` family (`RefineG_While`, `Refine_Foreach`), `MIf`, monadic ops (`Monadic_Operations.thy`) | `NREST/Combinators.lean`, source names kept (`whileT`, `whileIT`, `foreach…`) | = (each combinator with its currency, e.g. the source's `''call''`-style loop-overhead currencies become IR-op-named currencies, §6) |
| data refinement `⇓R` / `conc_fun` (`Data_Refinement.thy`) | `NREST/DataRefinement.lean`: `NRest.concFun (R : Set (γc × γa))` | relations stay sets of pairs, concrete-first (F3) |
| `timerefine` / `⇓C`, `timerefineA`, `wfR` (`Time_Refinement.thy`) | `NREST/TimeRefinement.lean`, same names | `Sum_any` → finite-support sum (`∑ᶠ`); `wfR` verbatim |
| the VCG: `gwp` + vcg rules + `progress` side conditions (`NREST_Backwards_Reasoning.thy`; architecture per `RefineMonadicVCG` / `Refine_Basic`'s `refine_vcg`) | `NREST/BackwardsReasoning.lean`: `gwp`, `@[refine_vcg]` attribute, `refine_vcg` tactic | named_theorems → persistent attribute + DiscrTree; tactic in Lean 4 meta. Same rule names, same `progress` obligation shape |

P1 acceptance restated concretely: RamBfs's content (masked depth-capped
BFS) written as `SPEC`-to-`SPEC` refinement chains with `whileIT`, cost
riding the order, in the shape of the source's `Breadth_First_Search`
example (which exists in `Refine_Monadic` precisely as the textbook
form — we reproduce it with costs).

### P2 — Relators and rule databases

| source artifact | Lean counterpart | substrate delta |
|---|---|---|
| relators as sets of pairs: `fun_rel` (`R → S`), `prod_rel`, `option_rel`, `list_rel`, `nres_rel` … (`Relators.thy`) | `Autoref/Relators.lean`, same names, `Set (β × α)` concrete-first | = (F3). Composition is `Set`-relation composition |
| parametricity rules + `@[param]` DB (`Parametricity`, `Param_Tool`, `Param_HOL`) | `Autoref/Param.lean` + `@[param]` attribute | named_theorems → attribute; rule *format* unchanged |
| tagged solvers, priority lists (`Tagged_Solver`, `Prio_List`, `Attr_Comb`) | `Autoref/Solver.lean`: side-condition solver registry | ML functor gymnastics → ordinary Lean 4 extension points; DiscrTree replaces `Anti_Unification`-based indexing (a strict improvement the charter's rule 3 permits: infrastructure, not calculus) |
| Autoref phases: id-ops, fix-rel, translate (`Autoref_Phases`, `Autoref_Id_Ops`, `Autoref_Fix_Rel`, `Autoref_Translate`, `Autoref_Tagging`) | `Autoref/Tool.lean` (phases under source names) | locales carrying phase state → structures threaded through a `MetaM` pipeline |

Scope note (unchanged from the plan): P2 ports the *spine* — what
Sepref's `fcomp`/`FCOMP` and side conditions consume. The full
`Autoref_Gen_Algo`/`Autoref_Bindings_HOL` breadth follows demand.

### P3 — The IR and its separation logic with credits

The IR is ours (ledger D2/D3); what is ported is the *shape* of the
artifact's concrete layer: a small-step-free, wp-style semantics over a
(state, credit-balance) pair, a separation logic whose assertions own
pieces of the state and hold credits, `htriple`s for each primitive op,
and a generic-wp file (`Sep_Generic_Wp.thy`) whose structure we follow
for the frame rule and the entailment/frame solver.

| source artifact | Lean counterpart | substrate delta |
|---|---|---|
| shallow `'a llM` over (memory, cost) with error/nonterm (`thys/basic/kernel`, ESOP'21 §4) | **deep** `Ir/Syntax.lean`: `Ir.Com` (op set §6), `Ir/Semantics.lean`: cost-indexed big-step (mirrors IMP+'s `BigStep`) | ledger D2: deep, named-cell, three-address; the *rule granularity* (one op = one cost = one hnr rule) is preserved, which is what fidelity of P4 needs |
| state: LLVM memory + credit balance `(s, cr)`; `llSTATE` | `Ir/Assn.lean`: state = tape-free partial environment (finite scalar map + finite array map) × credit balance; PCM = disjoint names | no heap, no allocation: ownership carves the *name space*, not addresses (D2 continued; the aliasing-free-environment finding of the IMP+ campaign survives *below* the SL, N1) |
| SL: `∗`, `emp`, pure `↑φ`, points-to, `$`-credits (`ESOP'21 §3`, `Sep_Lift.thy`, `LLVM_Shallow_RS.thy`) | same connective set: `x ↦ᵥ n` (scalar cell), `a ↦ₐ xs` (array with its length), `$c` (credits, currency-valued) | credits are `ACost String ℕ` at the IR too — currency-per-op (§6), cashed only at P5 (F4) |
| `wp`, `htriple`, frame rule, `sep_auto`-style entailment/frame solver (`Sep_Generic_Wp.thy`, `LLVM_VCG_Main.thy`) | `Ir/Wp.lean`, `Ir/Triples.lean`, `Ir/SepSolver.lean` | the solver is ported as the source has it: *algorithmic*, syntax-directed on assertion structure — no reliance on HOU (plan watch item) |

P3 acceptance: hand-proved credit-carrying triples for array get/set
and (as a derived program) fill.

### P4 — `hn_refine` and the translate phase

| source artifact | Lean counterpart | substrate delta |
|---|---|---|
| `hn_refine` (extract §4 of `source-extracts.md`) | `Sepref/Basic.lean`: `hnRefine`, draft in §5 below | deep `Ir.Com` in place of shallow `llM`; otherwise clause-for-clause |
| `hn_ctxt`, `pure R`, `invalid_assn`/`hn_invalid`, `MK_FREE` (linearity) | same names (`hnCtxt`, `pureRel`, `hnInvalid`) | = ; `hn_ctxt`'s whole job (keeping matching syntax-directed) is *more* load-bearing under Lean's weaker HOU, not less |
| rule format `hfref`/`fref`, composition `FCOMP` (`Sepref_Rules.thy`) | `Sepref/Rules.lean`, same names | = |
| phase 1 operator identification (`Sepref_Id_Op.thy`) | `Sepref/IdOp.lean`, `@[sepref_id_rules]` | interface-tagging via `mop`-style monadic ops kept; Lean macro/elab pass |
| phase 2 monadify (`Sepref_Monadify.thy`) | `Sepref/Monadify.lean` | = (ANF-ization with explicit evaluation order and duplicate-argument splitting) |
| phase 3 translate (`Sepref_Translate.thy`) + frame inference/merging (`Sepref_Frame.thy`) + deferred constraints (`Sepref_Constraints.thy`) | `Sepref/Translate.lean`, `Sepref/Frame.lean`, `Sepref/Constraints.lean` | the frame inferencer is ported per the source's algorithm (structural alignment of `hn_ctxt`-tagged conjuncts), with explicit annotation as documented fallback |
| phase 4 cleanup + tool driver, `sepref_dbg_*` step-through (`Sepref_Tool.thy`, `Sepref_Definition.thy`) | `Sepref/Tool.lean`, `Sepref/Definition.lean`; `sepref_dbg_*` names kept | supervision-legibility requirement from the plan lands here: every failure names phase + unmet side condition |

Scope decision recorded as ledger **D6**: translate targets
loop-structured programs only — abstract `RECT` must be refined to
`whileT`-form before synthesis, because IMP+ `Com` has no
procedures/recursion to compile general recursion into. The source
itself treats WHILE as the recursion instance it is, so this is a
restriction of *coverage*, not a change of any judgment.

**Source gap found by the P2–P4 deep read** (2026-07-29,
`p4-sepref-extracts.md`): the cost artifact contains **no
`hnr_If` / `hn_monadic_WHILE`-style control-flow hnr rules under any
name** (grep across its `thys/sepref/*.thy`); its examples route
control flow through `RECT`-side machinery. The if/while hnr rule
*shapes* therefore come from the no-cost AFP `Refine_Imperative_HOL`
twin, and P4 must **derive** their cost-carrying versions (branch
merging à la `MERGE`, plus the loop rule paying per-iteration credits
per the ESOP'21 discipline) rather than transcribe them. This is
recorded here so P4 budgets it as derivation work, with the derived
rules checked against the no-cost shapes clause by clause.

### P5 — Verified codegen, IR → IMP+ `Com`

No Isabelle original (their printer is trusted; ledger D3). Design:
`Codegen/Compile.lean` — structural `Ir.Com → Com` (names map to
names, three-address ops to small `Expr`s, IR conds to `Cond.eq/lt`);
per-constructor correctness+cost lemmas proved with the kit
(`Spec`/`run_vcg`); `Codegen/Cash.lean` — the cashing theorem:
`hnRefine` triple + per-currency price map (a `timerefineA` instance,
F4) + boundary wrapper ⇒ `Transfer.Solves`-shaped export ⇒
`computesInTime` via the existing `Transfer.lean`, untouched.

Boundary wrapper (ledger note N3): the tower is tape-free; a thin
hand-written IMP+ prologue/epilogue (kit-proved once, in the library)
moves input tape → arrays and result → output tape. This matches the
consumer shape that already exists: `bfs_spec`'s pre/post mention only
arrays and scalars, no tapes.

### P6 — IICF, narrow

| source artifact | Lean counterpart |
|---|---|
| `IICF/Intf` + `IICF/Impl` split; `mop_…` cost-carrying interface ops; hnr rule + assertion per structure (`IICF_Array`, `IICF_List`, `IICF_Map`, artifact `IICF/`) | `IICF/Intf/…`, `IICF/Impl/…` for: plain arrays; **Trail-backed touched-only arrays as the default array instance** (ledger D5); CSR graphs; stack; queue; bitmask sets — each: abstract interface (`mop` naming kept), hnr rules, currency specs |

Existing capital threads in here: `Lib/Trail.lean`, `Lib/Csr.lean`,
`Lib/Queue.lean`, `Lib/Stack.lean`, `Lib/Fill.lean` become the *proof
backends* of the P6 implementations — landed proofs are capital; P6
wraps them in interfaces, it does not re-prove them.

## 4. Phase names and debugging methodology

Inherited verbatim, per the charter: `sepref` phases are named
operator-identification / monadify / translate / cleanup; step-through
debugging is exposed under `sepref_dbg_*`; the abstract VCG is
`refine_vcg`; the mono set is `refine_mono`; parametricity is `param`.
The ITP'15 paper, the Sepref guides, and Haslbeck's thesis ch. 3–5
remain the operating manuals.

## 5. The `hn_refine` statement, drafted in Lean

Direct port of the extract (P0 writes no Lean; this is the P4 target,
recorded now so the P1–P3 interfaces aim at it):

```lean
namespace Lax13Proofs.Refine

/-- Credit-carrying assertions over the IR's (environment, balance)
pair; `∗`, `emp`, `↑`, `$`, `↦ᵥ`, `↦ₐ` from `Ir/Assn.lean`. -/
-- Assn : Type   llState : Assn → Ir.State × Cost → Prop

/-- `hnRefine Γ c Γ' R m`: under ownership `Γ` and any frame `F`, with
the credit balance `cr`, the IR program `c` refines the abstract
`m : NRest α ECost` — some abstract result `ra` whose cost `Ca` the
abstract program admits covers the run: `c`'s `wp`, started with the
balance topped up by `Ca`, lands in `Γ' ∗ R ra r ∗ F ∗ GC`, `GC`
absorbing surplus credits. Vacuously true when `m` fails. -/
def hnRefine (Γ : Assn) (c : Ir.Com) (Γ' : Assn)
    (R : α → Ir.Val → Assn) (m : NRest α ECost) : Prop :=
  m.nofail →
    ∀ (F : Assn) (s : Ir.State) (cr : Cost) (M : α → Option ECost),
      m = .rest M →
      llState (Γ ∗ F) (s, cr) →
      ∃ (ra : α) (Ca : ECost), some Ca ≤ M ra ∧
        Ir.wp c (fun r => llState (Γ' ∗ R ra r ∗ F ∗ GC))
          (s, cr + Ca.cash)
```

Deltas against the extract, all typing/substrate: `Ir.Com` deep;
`Ca.cash` names the `enat→ℕ` lowering of the abstract cost into the
balance carrier (the source's `lift_acost` handled the same seam;
whether the balance is `ACost String ℕ` or `ACost String ℕ∞` is P3's
first decision — default `ℕ∞` to match the source, restrict at the
codegen boundary). `some Ca ≤ M ra` is the extract's `M ra ≥ Some Ca`.
The ∀-quantified frame `F` bakes in the frame rule exactly as the
source does.

## 6. The IR op set (v0.1)

Values: `ℕ`, clean (unbounded) exactly as IMP+ — the word bound enters
once, at the existing `Bounds`/`Transfer` boundary. State: finite
`String`-keyed scalar cells and array cells; **no tapes** (N3), **no
allocation** (arrays are pre-existing named objects, lengths carried by
`↦ₐ`; IMP+ arrays cost nothing to exist).

Operations — three-address, one currency each, currency named by the op
(`cost "ir.add" 1` style, F4):

| op | form | lowers to (P5) |
|---|---|---|
| const | `x := n` | `assign x (lit n)` |
| copy | `x := y` | `assign x (var y)` |
| binop (×9) | `x := y ⊕ z`, ⊕ ∈ {add, sub, mul, div, and, or, xor, shiftl, shiftr} | `assign x (bin ⊕ …)` — exactly IMP+'s `Bop`, exactly the machine's arithmetic set |
| aget | `x := a[i]` | `assign x (get a (var i))` |
| aset | `a[i] := v` | `store a (var i) (var v)` |
| seq / ite / while | conditions `eq u v` / `lt u v` over cells and literals | structural; conds map onto `Cond.eq/lt` |

Deliberately absent: `alloc`/`free` (no heap), tapes (N3), calls and
recursion (D6), `len` (lengths live in assertions, as in the source's
array points-to). Everything here is one-instruction-cheap on the
machine through the existing compiler; nothing requires a new IMP+ or
machine capability — the scope guard "concept surfaces and machine
model untouched" is structural, not aspirational.

## 7. Placement and module skeleton

`word-ram/proofs/Lax13Proofs/Refine/` (flag 1, resolved), namespace
`Lax13Proofs.Refine.*` — inside the proofs prefix, so the namespace
audit passes by construction; helper-only, archive ignores it,
downstream reaches it through proofs-requires.

```
Refine/Cost/ACost.lean                    P1
Refine/NREST/{Basic,Pw,Rec,Combinators,DataRefinement,
              TimeRefinement,BackwardsReasoning}.lean   P1
Refine/Autoref/{Relators,Param,Solver,Tool}.lean        P2
Refine/Ir/{Syntax,Semantics,Assn,Wp,Triples,SepSolver}.lean  P3
Refine/Sepref/{Basic,Rules,IdOp,Monadify,Frame,Constraints,
               Translate,Tool,Definition}.lean          P4
Refine/Codegen/{Compile,Cash}.lean                      P5
Refine/IICF/{Intf,Impl}/…                               P6
```

Every executable layer gets `Decidable`/`#eval` instances and Plausible
checks the day it lands (plan, ledger D4): P1's finite-instance fuzzing
runs nrest ops at small sampled resource maps; P3/P5 differential-test
`Ir.Semantics` against the compiled `Com` run using the kit's existing
evaluator harness (`Smoke.lean` pattern, `demoRun` shape).

## 8. Deviation ledger (completed; supersedes the plan's seed)

| id | source design | our position | class / rationale | fallback |
|---|---|---|---|---|
| D1 | Isabelle/ML tactics, locales, named_theorems, `Anti_Unification` rule indexing | Lean 4 metaprograms, structures/typeclasses, persistent attributes, DiscrTree indexing | substrate-forced | none needed (mechanical) |
| D2 | concrete layer = shallow SSA-style `llM` over heap memory + trusted printer; SL owns heap addresses | concrete layer = deep three-address `Ir.Com` over named cells, no heap/alloc; SL owns *names*; bottoms at IMP+ `Com` | extremely good reason (recorded pre-P0, conv. Jan 2026-07-29): the claims' meaning lives on the endorsed word RAM; fixed-width LLVM cannot state parametric-`w` theorems. Rule granularity (one op / one cost / one hnr rule) is preserved, which is what P4's fidelity actually consumes | if named-cell SL fights the Sepref rule shapes, fall back to an address-carved flat-array heap under the same assertions (source-shaped), still bottoming at IMP+ |
| D3 | final LLVM emission is a trusted printer | codegen verified into the deep embedding (P5) | upgrade the deep embedding affords; no design intent changed | trusted-reify escape hatch is *not* acceptable here (the endorsement surface is the point); if P5 stalls, scope shrinks before trust grows |
| D4 | (no analogue) | executable instances + Plausible fuzzing gate every layer | addition (refute-before-prove, ND-MC record) | — |
| D5 | IICF leaves cost-spec shape per instance | Trail-backed touched-only arrays are the *default* array instance | library convention; calculus untouched (n² init lesson) | plain-array instance remains available per instance |
| D6 | Sepref synthesizes general recursion (`RECT` → heap-monad recursion) | translate targets loop-form only; `RECT` must be refined to `whileT` before synthesis | substrate-forced: IMP+ `Com` has no procedures; the word-RAM claims never needed general recursion (RamBfs is loops) | if a consumer needs it: verified defunctionalization pass at the abstract level (stays out of the calculus) |
| N1 | SL + ownership at the synthesis layer | adopted as-is; the IMP+ "aliasing-free beats SL" finding stands *below* the SL (the IR state is still aliasing-free by names; SL adds ownership/linearity for destructive update, which is what the source says it is for) | non-deviation (charter rule 3) | — |
| N2 | (source has its own small SL) | iris-lean not adopted; the source's small SL ported (P3); `Std.Do` not a dependency (F5); both stay watch items | non-deviation; maturity risk on pinned toolchain | — |
| N3 | source programs are heap-in/heap-out; no I/O | the tower is tape-free; one kit-proved IMP+ boundary wrapper moves tape→arrays→tape at P5; exported statements stay in `bfs_spec`'s (tape-free `Spec`) shape | non-deviation: no source analogue exists; ported components untouched | — |

## 9. Fidelity notes (conforming choices worth recording)

- **F1** Currency names are `String`, as in the source (`cost "…" k`);
  no enum-typed currencies, so exchange maps stay data, not types.
- **F2** `acost` carriers are plain functions plus the source's own
  `wfR` finite-support predicate — *not* mathlib `Finsupp` — because
  every `timerefine` lemma's statement shape depends on it.
- **F3** Refinement relations are `Set (concrete × abstract)` with
  membership statements `(c, a) ∈ R`, matching the source text
  verbatim; mathlib supports this with zero friction, and the relator
  algebra is theirs.
- **F4** Cost currencies survive down to the IR (per-op currencies);
  collapsing to a single time unit happens once, in P5's cashing
  theorem, as a `timerefineA` instance next to the layout constant
  `L.const`. This is the ESOP'21 architecture exactly, and it is what
  makes per-phase cost accounting legible to review.
- **F5** `Std.Do`/`mvcgen` (present in v4.30.0, verified locally) is
  used as *evidence and idiom reference* (attribute-registered spec
  lemmas driving a VCG) but not as a dependency: its `SPred` is a
  state-tuple logic over Lean monads, not a PCM separation logic over
  our deep IR, and its `Triple` speaks about Lean programs, not `Ir.Com`
  / `NRest`. Wrapping it would be a deviation from the source with no
  reason class.
- **F6** Result maps are `α → WithBot γ`, not `α → Option γ`:
  Isabelle's `'b option` result carrier under the source's None-bottom
  pointwise order is definitionally mathlib's `WithBot γ`, and using
  mathlib's name buys the whole lattice structure of result maps
  (`NRest α γ ≅ WithTop (α → WithBot γ)`) instead of re-proving it.
  Statement shapes change only `Some t` ↦ `(t : WithBot γ)`.
- **F7** The monad laws are stated at the source's own generality and
  no more: left identity generic in the resource class, right identity
  and associativity monomorphic at `ℕ∞` and `ACost κ ℕ∞` — exactly
  where `nres_bind_right_identity`/`nres_bind_assoc`/
  `nres_acost_bind_assoc` sit in the source (they need `+`/`Sup`
  continuity, and the source chose instances over a continuity class).
  The `nonneg`/`needname`/`drm`/`needname_zero` classes of
  `NREST_Type_Classes.thy` belong to the `gwp`/backwards-reasoning
  side and are ported there, when that file lands.

## 10. Defaults handed to P1 (decided here, cheap to revise)

1. Balance carrier at the IR: `ACost String ℕ∞` (source-matching);
   restrict to finite at the codegen boundary. First P3 commit may
   flip to `ACost String ℕ` if `ℕ∞` arithmetic grinds — one-line ledger
   note if so.
2. `NRest` stays in `Type`, both parameters; no universe polymorphism
   until a consumer forces it.
3. The `@[refine_vcg]`/`@[param]`/`@[sepref…]` attribute set is one
   shared implementation parameterized by DB name (one meta module, not
   five).
4. P1's acceptance program is the *abstract* masked depth-capped BFS
   against `bfs_spec`'s postcondition vocabulary (`WithinDist` on
   `masked G M`), so the P7 gate consumes P1's artifact unchanged.

## 11. What P0 did not do

No Lean was written (per plan). No sources were vendored (targeted
fetches only; extracts in `source-extracts.md`). The `isabelle_llvm`
2023-branch basic layer was mapped at directory/shape level only — P3
re-reads `Sep_Generic_Wp.thy` and the kernel in detail when it lands
the IR; the artifact's `thys/vcg`+`thys/basic` file list is recorded in
the extracts for that purpose.
