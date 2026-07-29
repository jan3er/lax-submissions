# Source extracts — verbatim, with provenance

P0 companion to `design.md`. These are the load-bearing definitions of
the sources, quoted verbatim so that fidelity arguments in the design
record and in later phases can be checked against text rather than
memory. Everything here was fetched 2026-07-29 from the pinned versions
recorded in `design.md`.

## The currency type (`acost`)

`isabelle_llvm_time` @ 42dd7f5, `thys/cost/Abstract_Cost.thy`:

```isabelle
datatype ('a, 'b) acost = acostC (the_acost: "'a ⇒ 'b")

type_synonym cost = "(string, nat) acost"

(* zero, plus, order are pointwise: *)
"zero_acost = acostC (λ_. 0)"
"plus_acost (acostC a) (acostC b) = acostC (λx. a x + b x)"
"less_eq_acost a b = (∀x. the_acost a x ≤ the_acost b x)"

(* one unit of one currency: *)
"cost n x = acostC ((the_acost 0)(n := x))"
```

The abstract-level cost carrier is `ecost = (string, enat) acost`
(`Enat_Cost.thy`); currencies are named by strings throughout.

## The monad (`nrest`)

`isabelle_llvm_time` @ 42dd7f5, `thys/nrest/NREST.thy` (the AFP `NREST`
entry, Isabelle2025-2, carries the same core):

```isabelle
datatype ('a,'b) nrest = FAILi | REST "'a ⇒ ('b::{complete_lattice,monoid_add}) option"

definition RETURNT :: "'a ⇒ ('a, 'b::{complete_lattice, monoid_add}) nrest" where
  "RETURNT x ≡ REST (λe. if e=x then Some 0 else None)"

abbreviation "FAILT ≡ top::(_,_::{complete_lattice, monoid_add}) nrest"
abbreviation "SUCCEEDT ≡ bot::(_,_::{complete_lattice, monoid_add}) nrest"
abbreviation SPECT where "SPECT ≡ REST"

definition "SPEC P t = REST (λv. if P v then Some (t v) else None)"

fun less_eq_nrest where
  "_ ≤ FAILi ⟷ True" |
  "(REST a) ≤ (REST b) ⟷ a ≤ b" |
  "FAILi ≤ (REST _) ⟷ False"

definition consume where "consume M t ≡ case M of
  FAILi ⇒ FAILT | REST X ⇒ REST (map_option ((+) t) o (X))"

definition bindT :: "('b,'c::{complete_lattice, monoid_add}) nrest ⇒ ('b ⇒ ('a,'c) nrest)
  ⇒ ('a,'c) nrest" where
  "bindT M f ≡ case M of FAILi ⇒ FAILT | REST X ⇒ Sup { consume (f x) t1 |x t1. X x = Some t1}"

definition "iASSERT ret Φ ≡ if Φ then ret () else top"
definition "ASSERT ≡ iASSERT RETURNT"
```

Notes: the result map is partial (`Some t` = result achievable at cost
`t`); `⊑` is the pointwise order under `FAILi` as top; `bindT` is a
`Sup` over `consume`, so the monad laws and everything else ride on the
complete-lattice structure of the resource type.

## Currency exchange (`timerefine`)

`isabelle_llvm_time` @ 42dd7f5, `thys/nrest/Time_Refinement.thy`:

```isabelle
definition timerefine ::"('b ⇒ ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost)
                             ⇒ ('a, ('b,'d) acost) nrest ⇒ ('a, ('c,'d) acost) nrest" ("⇓C")
  where "⇓C R m = (case m of FAILi ⇒ FAILi |
                REST M ⇒ REST (λr. case M r of None ⇒ None |
                  Some cm ⇒ Some (acostC (λcc. Sum_any (λac. the_acost cm ac *
                                     the_acost (R ac) cc)))))"

definition timerefineA ::"('b ⇒ ('c,'d::…) acost) ⇒ (('b,'d) acost) ⇒ (('c,'d) acost)"
  where "timerefineA R cm = (acostC (λcc. Sum_any (λac. the_acost cm ac *
                              the_acost (R ac) cc)))"

definition "wfR R = (finite {(s,f). the_acost (R s) f ≠ 0})"
```

An exchange rate `R` prices each abstract currency in concrete
currencies; `Sum_any` needs the finite support that `wfR` supplies.

## The synthesis judgment (`hn_refine`, cost-carrying)

`isabelle_llvm_time` @ 42dd7f5, `thys/sepref/Sepref_Basic.thy`:

```isabelle
definition "hn_refine Γ c Γ' R m ≡
  nofailT m ⟶
  (∀F s cr M. m = REST M ⟶
      llSTATE (Γ ∧* F) (s,cr) ⟶
      (∃ra Ca. M ra ≥ Some Ca
        ∧ wp c (λr. llSTATE (Γ' ∧* R ra r ∧* F ∧* GC)) (s, cr+Ca)
      )
  )"

definition hn_ctxt :: "('a⇒'c⇒assn) ⇒ 'a ⇒ 'c ⇒ assn" where
  "hn_ctxt P a c ≡ P a c"

definition pure :: "('b × 'a) set ⇒ 'a ⇒ 'b ⇒ assn" where
  "pure R ≡ (λa c. ↑((c,a)∈R))"

lemma hn_refine_frame:
  assumes hnr: "hn_refine P' c Q' R m"
  assumes ent: "P ⊢ P' ** F"
  shows "hn_refine P c (Q' ** F) R m"
```

Notes read off the definition, used by the design record:

- the machine state is a pair `(s, cr)` of memory and a *credit
  balance*; `llSTATE` evaluates a separation-logic assertion against
  it;
- the judgment quantifies over an arbitrary frame `F` — the frame rule
  is baked into the definition, `hn_refine_frame` only rearranges it;
- `m`'s cost `Ca` for the chosen abstract result is *added to the
  balance* before running `c`: `wp … (s, cr + Ca)`. `wp` charges each
  op's cost against the balance, so "the run costs at most `Ca` plus
  whatever credits `Γ` already held" is the whole cost content;
- `GC` in the postcondition absorbs leftover credits (their garbage
  collector for surplus time);
- `hn_ctxt` is an opaque tag whose only job is to keep frame inference
  and rule matching syntax-directed — the HOU-avoidance device the
  design record leans on;
- `pure R` embeds an ordinary refinement relation (a set of pairs,
  concrete component first) as an ownership-free assertion.

## Phase pipeline file names

`isabelle_llvm_time` @ 42dd7f5, `thys/sepref/` (same names as AFP
`Refine_Imperative_HOL`, which is the richer, documented no-cost
original):

```
Sepref_Id_Op.thy          — operator identification
Sepref_Monadify.thy       — monadify
Sepref_Translate.thy      — translate
Sepref_Frame.thy          — frame inference and merging
Sepref_Rules.thy          — hfref/fref rule format, FCOMP
Sepref_Constraints.thy    — deferred side-condition constraints
Sepref_Definition.thy     — user-facing definition commands
Sepref_Combinator_Setup.thy, Sepref_Basic.thy, Sepref_Tool.thy
IICF/ (Intf/ + Impl/)     — interface/implementation split
```

`thys/nrest/` in the same artifact:

```
NREST.thy, NREST_Misc.thy, NREST_Auxiliaries (AFP),
Data_Refinement.thy        — ⇓R / conc_fun
Time_Refinement.thy        — ⇓C / timerefine, wfR
NREST_Backwards_Reasoning.thy — gwp, the cost VCG
NREST_Automation.thy, NREST_Type_Classes.thy, Refine_Heuristics.thy,
Monadic_Operations.thy, NREST_Main.thy
```

`thys/vcg/` (the separation-logic/wp layer the IR port follows in
shape): `Sep_Generic_Wp.thy`, `LLVM_Shallow_RS.thy`,
`LLVM_Memory_RS.thy`, `Sep_Lift.thy`, `Sep_Value_RS.thy`,
`Sep_Array_Block_RS.thy`, `Sep_Block_Allocator_RS.thy`,
`LLVM_VCG_Main.thy`; `thys/basic/` = `kernel/` + `preproc/` +
`LLVM_Basic_Main.thy`; `thys/cost/` = `Abstract_Cost.thy`,
`Enat_Cost.thy`.

## Monad laws — the source's own generality

`isabelle_llvm_time` @ 42dd7f5, `thys/nrest/NREST.thy`. Left identity
is generic; right identity and associativity are stated *monomorphically*
at `enat` and at `(_, enat) acost` — the continuity of `+` over `Sup`
they need is taken from the instance, not from a class:

```isabelle
lemma nres_bind_left_identity[simp]:
  fixes f :: "'a ⇒ ('b,'c::{complete_lattice,zero,monoid_add}) nrest"
  shows "bindT (RETURNT x) f = f x"

lemma nres_bind_right_identity[simp]:
  fixes M :: "('b,enat) nrest"
  shows "bindT M RETURNT = M"

lemma nres_bind_assoc[simp]:
  fixes M :: "('a,enat) nrest"
  shows "bindT (bindT M (λx. f x)) g = bindT M (λx. bindT (f x) g)"

lemma nres_acost_bind_assoc[simp]:
  fixes M :: "('a,(_,enat) acost) nrest"
  shows "bindT (bindT M (λx. f x)) g = bindT M (λx. bindT (f x) g)"

lemma consume_RETURNT: "consume (RETURNT x) T = SPECT [x ↦ T]"

definition nofailT :: "('a,_) nrest ⇒ bool" where "nofailT S ≡ S≠FAILT"

definition inresT :: "(_,'ac) nrest ⇒ _ ⇒ 'cc ⇒ bool"
  where "inresT S x t ≡ REST ([x↦lift t]) ≤ S"
```

(The `lift` in `inresT` is the currency seam; the same-carrier instance
is what P1 ports first, per design.md.)

## The resource type classes (`NREST_Type_Classes.thy`)

`isabelle_llvm_time` @ 42dd7f5. These serve the `gwp`/backwards-
reasoning side (`minus` structure for paying costs), not the monad
laws; ported with `BackwardsReasoning`:

```isabelle
class nonneg = ord + zero +
  assumes needname_nonneg: "0 ≤ x"

class needname = complete_lattice + minus + plus +
  assumes top_absorb, minus_plus_assoc2, le_diff_if_add_le,
          add_leD2, add_le_if_le_diff

class drm = minus + plus + ord + Inf + Sup +
  assumes diff_right_mono, diff_left_mono, minus_continousInf,
          minus_continousSup, plus_left_mono

class needname_zero = needname + nonneg + drm + ordered_comm_monoid_add
                      + mult_zero +
  assumes needname_minus_absorb: "x - 0 = x"
          needname_plus_absorb: "0 + x = x"
```

## AFP theory listings (Isabelle2025-2, 2026-02-06)

`Refine_Monadic`: Refine_Chapter, Refine_Mono_Prover, Refine_Misc,
RefineG_Transfer, RefineG_Domain, RefineG_Recursion, RefineG_Assert,
Refine_Basic, Refine_Leof, Refine_Heuristics, Refine_More_Comb,
RefineG_While, Refine_While, Refine_Det, Refine_Pfun, Refine_Transfer,
Refine_Foreach, Refine_Automation, Autoref_Monadic, Refine_Monadic;
examples: Breadth_First_Search, WordRefine.

`Automatic_Refinement`: Refine_Util_Bootstrap1, Mpat_Antiquot,
Mk_Term_Antiquot, Refine_Util, Attr_Comb, Named_Sorted_Thms, Prio_List,
Tagged_Solver, Anti_Unification, Misc, Foldi, Indep_Vars, Select_Solve,
Mk_Record_Simp, Refine_Lib; Relators, Param_Tool, Param_HOL,
Parametricity; Autoref_Phases, Autoref_Data, Autoref_Tagging,
Autoref_Id_Ops, Autoref_Fix_Rel, Autoref_Relator_Interface,
Autoref_Translate, Autoref_Gen_Algo, Autoref_Tool,
Autoref_Bindings_HOL.

`Refine_Imperative_HOL`: Sepref_Basic, Sepref_Monadify,
Sepref_Constraints, Sepref_Frame, Sepref_Rules, Sepref_Translate,
Sepref_Definition, Sepref_Tool, Sepref_Id_Op (via Sepref_Basic
session), Sepref_Misc, Pf_Mono_Prover, PO_Normalizer, Term_Synth,
User_Smashing, Structured_Apply; IICF: IICF_List, IICF_Set, IICF_Array,
IICF_Map, IICF_Matrix, IICF_Prio_Bag, IICF_Prio_Map and list/array
variants; examples: Sepref_Dijkstra, Sepref_DFS, Sepref_NDFS,
Worklist_Subsumption; guides: Sepref_Guide_Quickstart,
Sepref_Guide_Reference.

`NREST` (AFP): NREST_Auxiliaries, NREST, DataRefinement,
RefineMonadicVCG, SepLogic_Misc, Refine_Foreach. Depends on
Automatic_Refinement, Refine_Monadic, Case_Labeling.
