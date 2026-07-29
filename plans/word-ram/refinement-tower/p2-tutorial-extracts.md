# P2 source extracts — tutorial reproduction target

Companion to `p2-autoref-extracts.md` (relators/parametricity/tagging) and
`design.md` §3 P2. Fetched 2026-07-29, verbatim, from AFP `Automatic_Refinement`,
`Collections`, and `Refine_Monadic`, Isabelle2025-2. Mirror used:
**`isabelle-prover/mirror-afp-devel`**, same choice and same justification as
the companion extract file (the task's `mirror-afp-2025-1` path convention was
not re-tested here; devel is the established working mirror for this campaign).
Files fetched via raw.githubusercontent.com at commit tip of `master` on
2026-07-29, and directory listings via the GitHub contents API
(`api.github.com/repos/isabelle-prover/mirror-afp-devel/contents/...`):

- `thys/Automatic_Refinement/Autoref_Bindings_HOL.thy` (32611 bytes)
- `thys/Collections/Examples/Autoref/Simple_DFS.thy` (19488 bytes)
- `thys/Collections/Examples/Autoref/Coll_Test.thy` (13067 bytes, listed/skimmed only)
- `thys/Collections/Examples/Autoref/ICF_Only_Test.thy` (1307 bytes, listed/skimmed only)
- `thys/Collections/Examples/Autoref/Succ_Graph.thy` (2966 bytes, listed/skimmed only)
- `thys/Collections/Examples/Autoref/Combined_TwoSat.thy` (7847 bytes, listed/skimmed only)
- `thys/Collections/Userguides/Refine_Monadic_Userguide.thy` (39885 bytes, grepped only)
- `thys/Collections/Userguides/ICF_Userguide.thy` (25148 bytes, grepped only — no autoref content)
- `thys/Refine_Monadic/examples/WordRefine.thy` (2369 bytes)
- `thys/Refine_Monadic/Autoref_Monadic.thy` (1939 bytes)
- `thys/Collections/Examples/Refine_Monadic/Foreach_Refine.thy`,
  `Refine_Fold.thy`, `Bfs_Impl.thy` (listed/grepped only)
- `thys/Refine_Monadic/examples/Breadth_First_Search.thy` (listed/grepped only)

## 1. `thys/Automatic_Refinement/` — full file listing

Top level:

```
Automatic_Refinement.thy          1163
Autoref_Bindings_HOL.thy         32611
Lib/                 (dir)
Parametricity/       (dir)
ROOT                                721
Tool/                (dir)
document/            (dir)
```

`Lib/`:

```
Anti_Unification.thy       4995
Attr_Comb.thy               3281
Cond_Rewr_Conv.ML           1161
Foldi.thy                   4860
Indep_Vars.thy              1639
Misc.thy                  167003
Mk_Record_Simp.thy          1201
Mk_Term_Antiquot.thy        6771
Mpat_Antiquot.thy          10203
Named_Sorted_Thms.thy       2066
Prio_List.thy               2620
Refine_Lib.thy                314
Refine_Util.thy            32778
Refine_Util_Bootstrap1.thy  1830
Revert_Abbrev.ML            1200
Select_Solve.thy            6428
Tagged_Solver.thy           8981
```

`Parametricity/`:

```
Param_Chapter.thy    100
Param_HOL.thy      26180
Param_Tool.thy     11767
Parametricity.thy     73
Relators.thy       38057
```

`Tool/`:

```
Autoref_Chapter.thy            102
Autoref_Data.thy               1094
Autoref_Fix_Rel.thy           31989
Autoref_Gen_Algo.thy            2491
Autoref_Id_Ops.thy             21654
Autoref_Phases.thy              7059
Autoref_Relator_Interface.thy   3774
Autoref_Tagging.thy              6452
Autoref_Tool.thy                 6947
Autoref_Translate.thy           10136
```

**No file inside `Automatic_Refinement/` is named `*Test*`/`*Example*`/
`*Tutorial*`.** But per the task's instruction to also check for a test
section at the bottom of `Autoref_Bindings_HOL.thy`: there is one. It closes
the file with a bare `subsection "Examples"` containing eight small
`schematic_goal`/`autoref` invocations that use **only pure-HOL bindings**
(no Collections dependency at all — this file lives inside
`Automatic_Refinement` itself, one level more "in scope" than anything in
`Collections`). This turns out to be the best P2 acceptance candidate; it is
extracted in full in §4, and its prerequisite operator bindings in §3.

## 2. Collections tutorial — `Examples/Autoref/`

`Collections/` top level:

```
Collections_Entrypoints_Chapter.thy   451
Examples/            (dir)
GenCF/                (dir)
ICF/                  (dir)
Iterator/             (dir)
Lib/                  (dir)
ROOT                                 4417
Refine_Dflt.thy                      2673
Refine_Dflt_ICF.thy                  2512
Refine_Dflt_Only_ICF.thy              916
Userguides/           (dir)
document/             (dir)
```

`Collections/Examples/`:

```
Autoref/              (dir)
Collection_Examples.thy    164
Examples_Chapter.thy       272
ICF/                  (dir)
Refine_Monadic/       (dir)
```

`Collections/Examples/Autoref/`:

```
Coll_Test.thy                       13067
Collection_Autoref_Examples.thy       153
Collection_Autoref_Examples_Chapter.thy  282
Combined_TwoSat.thy                  7847
ICF_Only_Test.thy                    1307
ICF_Test.thy                         8408
Nested_DFS.thy                      42408
Simple_DFS.thy                      19488
Succ_Graph.thy                       2966
```

`Collections/Userguides/`:

```
ICF_Userguide.thy             25148
Refine_Monadic_Userguide.thy  39885
Userguides_Chapter.thy           188
```

**Resolution note:** no file literally named `Autoref_Tutorial.thy` exists.
`Refine_Monadic_Userguide.thy` line 244–245 says (of the Autoref prototype):
*"Usage examples are in `ex/Automatic-Refinement`"* — the pre-consolidation
AFP path that is now `Collections/Examples/Autoref/`, confirming this is the
right directory. Within it, `Coll_Test.thy` and `ICF_Only_Test.thy` are flat
regression-test batteries: `schematic_goal` after `schematic_goal`, **no
narrative prose**, and Collections-data-structure-bound from their very
first example (`ahm_rel`, `dflt_ahs_rel`, `list_map_rel`, `dflt_ahm_rel`
appear inside the first 20 lines of `Coll_Test.thy`; `lm.rel` in
`ICF_Only_Test.thy`). `Combined_TwoSat.thy` and `Nested_DFS.thy` are full case
studies but pull in the Containers framework / RBT maps respectively — richer
narrative, heavier scope. **`Simple_DFS.thy` is the file that matches "the
classic Autoref tutorial"**: it has genuine explanatory prose, is structured
as a single running example (spec → correctness proof → three successive
autoref derivations of increasing sophistication), and one of its lemmas is
explicitly labelled `text ‹Correctness theorem presented in the paper›` —
i.e. it *is* the worked example from the original Autoref publication. It is
extracted below.

### 2.1 Header and custom relator (`succg_rel`)

```isabelle
section ‹\isaheader{Simple DFS Algorithm}›
theory Simple_DFS
imports 
  Collections.Refine_Dflt 
begin



section ‹Graphs Implemented by Successor Function›
subsection ‹Refinement relation›
definition "E_of_succ succ ≡ {(u,v). v∈succ u}"
definition [to_relAPP]: "succg_rel R ≡ (R → ⟨R⟩list_set_rel) O br E_of_succ (λ_. True)"


consts i_graph :: "interface ⇒ interface"
  \<comment> ‹Define the conceptual type of graphs.›

lemmas [autoref_rel_intf] = REL_INTFI[of "succg_rel" i_graph]
  \<comment> ‹Declare ‹succg_rel› to be a relator for graphs.›


lemma in_id_succg_rel_iff: "(s,E)∈⟨Id⟩succg_rel ⟷ (∀v. distinct (s v) ∧ set (s v) = E``{v})"  
  \<comment> ‹Simplification in case of identity refinements for nodes›
  unfolding succg_rel_def br_def E_of_succ_def list_set_rel_def
  by (auto; force dest: fun_relD)
  
  
subsection ‹Successor Operation›
definition [simp]: "op_succ E u ≡ E``{u}"
  \<comment> ‹Define the abstract successor operation.›

context begin interpretation autoref_syn .
  lemma [autoref_op_pat]: "E``{v} ≡ op_succ$E$v" by simp
  \<comment> ‹Declare a rewrite rule to operation identification.›
end

lemma refine_succg_succs[autoref_rules]: 
  "(λsuccs v. succs v,op_succ)∈⟨R⟩succg_rel→R→⟨R⟩list_set_rel"
  \<comment> ‹Declare implementation of successor function to Autoref.›
  apply (intro fun_relI)
  apply (auto simp add: succg_rel_def br_def E_of_succ_def dest: fun_relD)
  done
```

Relators/bindings consumed: `fun_rel` (`→`, in scope, P2), `br`
(bijection-restriction combinator, from `Automatic_Refinement`'s
`Relators.thy`, in scope), **`list_set_rel`** (Collections/ICF distinct-list
set representation — **OUT OF SCOPE, P6 material**), plus the
`autoref_rel_intf`/`autoref_op_pat`/`autoref_rules` attribute hooks (in
scope, already covered by the companion extract file).

### 2.2 Abstract DFS program

```isabelle
section ‹DFS Algorithm›
text ‹
  We define a simple DFS-algorithm, prove a simple correctness
  property, and do data refinement to an efficient implementation.
›

subsection ‹Definition›

text ‹Recursive DFS-Algorithm. 
  ‹E› is the edge relation of the graph, ‹tgt› the node to 
  search for, and ‹src› the start node.
  Already explored nodes are 
  stored in ‹V›.›

context 
  fixes E :: "('v×'v) set" and src :: 'v and tgt :: 'v
begin
  definition dfs :: "bool nres" where
    "dfs ≡ do {
      (_,r) ← RECT (λdfs (V,v). 
        if v=tgt then RETURN (V,True)
        else do {
          let V = insert v V;
          FOREACHc (E``{v}) (λ(V,brk). ¬brk) (λv' (V,brk). 
            if v'∉V then dfs (V,v') else RETURN (V,False)
          ) (V,False)
        }) ({},src);
      RETURN r
    }"
```

`dfs` is built from `RECT` and `FOREACHc` — monadic combinators from
`Refine_Monadic`, not from `Automatic_Refinement` — so its correctness proof
(`dfs_correct`, immediately following in the source, eliding here per the
Gaps note) belongs to the Refine_Monadic layer, not the Autoref spine. It is
included only as the abstract program the three autoref examples below
refine.

### 2.3 Example 1 — `dfs_impl_refine_aux` (`autoref_monadic` + `concrete_definition`)

```isabelle
subsection ‹Data Refinement and Determinization›

text ‹
  Next, we use automatic data refinement and transfer to generate an
  executable algorithm. We fix the node-type to natural numbers,
  and the successor-function to return a list-set. 
  The implementation of the visited set is left open, and Autoref's heuristics
  will choose one (default for nat set: red-black-trees).
›

text ‹In our first example, we use ‹autoref_monadic›, which combines the 
  Autoref tool and the determinization of the Monadic Refinement Framework.›
  
schematic_goal dfs_impl_refine_aux:
  fixes succi and E :: "('a::linorder × 'a) set" and tgt src :: 'a
  assumes [autoref_rules]: "(succi,E)∈⟨Id⟩succg_rel"
  notes [autoref_rules] = IdI[of src] IdI[of tgt]
  shows "RETURN (?f::?'c) ≤ ⇓?R (dfs E src tgt)"
  unfolding dfs_def by autoref_monadic 

text ‹We define a new constant from the synthesis result›
concrete_definition dfs_impl for succi src tgt uses dfs_impl_refine_aux
text ‹Set up code equations for the recursion combinators›
prepare_code_thms dfs_impl_def
text ‹And export the algorithm to all supported target languages›
export_code dfs_impl in Haskell
export_code dfs_impl checking SML OCaml? Haskell? Scala
```

Relators consumed: `succg_rel` (custom, wraps `list_set_rel` — OUT OF
SCOPE), `Id` (in scope). Bindings: `IdI` (generic identity-relation
introduction rule), and the `autoref_monadic` tactic itself, which (per
`Refine_Monadic/Autoref_Monadic.thy`, ML elided) is literally
`resolve_tac @{thms autoref_monadicI} THEN' Autoref_Phases.all_phases_tac
THEN' RefineG_Transfer.post_transfer_tac` — i.e. Autoref's phase pipeline
followed by the Monadic Refinement Framework's determinization/transfer
phase. The determinization half is OUT OF SCOPE for P2 (that's P3+
territory); only the `Autoref_Phases.all_phases_tac` half is P2's spine.

### 2.4 Example 2 — plain `autoref`, no determinization

```isabelle
subsubsection ‹Using only Autoref›

text ‹Here we show the result of Autoref, without the determinization phase of
  the Monadic Refinement Framework: ›
schematic_goal 
  fixes succi and E :: "('a::linorder × 'a) set" and tgt src :: 'a
  assumes [autoref_rules]: "(succi,E)∈⟨Id⟩succg_rel"
  notes [autoref_rules] = IdI[of src] IdI[of tgt]
  shows "(?f::?'c, dfs E src tgt) ∈ ?R"
  unfolding dfs_def[abs_def] 
  apply (autoref (trace))
  done
```

Same relators/bindings as §2.3 minus the monadic layer — this is the
*purest* Autoref-only derivation in the tutorial, but it is still gated on
`succg_rel`/`list_set_rel` (OUT OF SCOPE).

### 2.5 Example 3 — hashset override via `autoref_tyrel`

```isabelle
subsubsection ‹Choosing Different Implementations›
text ‹Ad-hoc override of implementation selection heuristics: Using hashset for the visited set›  
schematic_goal dfs_impl_refine_aux2:
  fixes succi and E :: "(('a::hashable) × 'a) set" and tgt src :: 'a
  assumes [autoref_rules]: "(succi,E)∈⟨Id⟩succg_rel"
  notes [autoref_rules] = IdI[of src] IdI[of tgt]
  notes [autoref_tyrel] = ty_REL[where 'a="'a set" and R="⟨Id⟩dflt_ahs_rel"] 
  shows "(?f::?'c, dfs E src tgt) ∈ ?R"
  unfolding dfs_def[abs_def] 
  apply autoref_monadic
  done
```

Adds `dflt_ahs_rel` (Collections hash-set — OUT OF SCOPE) via the
`autoref_tyrel`/`ty_REL` override mechanism (the *phase itself* — "let the
user pin down a default relator for an abstract type" — is in-scope spine
machinery; this particular *instance* of it is not). Two further examples
follow in the source (`dfs_impl_refine_aux3`/`3'`: generic node type with a
custom comparator, pulling in `dflt_rs_rel`/`rbt_map_rel`/`comp2lt` and the
Containers framework) — not quoted; see Gaps.

## 3. Pure-HOL operator bindings behind the recommended example (`Autoref_Bindings_HOL.thy`)

The recommended reproduction target (§4, first entry) needs only: nat
literals/numerals, list `Nil`/`Cons`, and `append`. The other seven entries
in the same "Examples" section additionally need `hd`, list equality,
option equality, and list emptiness-testing — bindings for all of these are
included below for completeness, since they all sit in the same file/section
and cost nothing extra to extract.

Generic order/equality/numeral layer (fallback for arbitrary types honoring
`PRIO_TAG_GEN_ALGO`, overridden by the nat-specific rules below when
applicable):

```isabelle
  lemma [autoref_rules]: 
    assumes "PRIO_TAG_GEN_ALGO"
    shows "((<), (<)) ∈ Id→Id→bool_rel"
    and "((≤), (≤)) ∈ Id→Id→bool_rel"
    and "((=), (=)) ∈ Id→Id→bool_rel"
    and "(numeral x,OP (numeral x) ::: Id) ∈ Id"
    and "(uminus,uminus) ∈ Id → Id"
    and "(0,0) ∈ Id"
    and "(1,1) ∈ Id"
    by auto
```

`nat` bindings (`nat_rel` is `Id` specialised to `nat`; covers the numeral
literals `[1,2,3]`/`4` used throughout §4):

```isabelle
    lemma autoref_nat[autoref_rules]:
      "(0, 0::nat) ∈ nat_rel"
      "(Suc, Suc) ∈ nat_rel → nat_rel"
      "(1, 1::nat) ∈ nat_rel"
      "(numeral n::nat,numeral n::nat) ∈ nat_rel"
      "((<), (<) ::nat ⇒ _) ∈ nat_rel → nat_rel → bool_rel"
      "((≤), (≤) ::nat ⇒ _) ∈ nat_rel → nat_rel → bool_rel"
      "((=), (=) ::nat ⇒ _) ∈ nat_rel → nat_rel → bool_rel"
      "((+) ::nat⇒_,(+))∈nat_rel→nat_rel→nat_rel"
      "((-) ::nat⇒_,(-))∈nat_rel→nat_rel→nat_rel"
      "((div) ::nat⇒_,(div))∈nat_rel→nat_rel→nat_rel"
      "((*), (*))∈nat_rel→nat_rel→nat_rel"
      "((mod), (mod))∈nat_rel→nat_rel→nat_rel"
      by auto
```

List `Nil`/`Cons`/`append` (exactly what the recommended example needs):

```isabelle
  lemma autoref_append[autoref_rules]: 
    "(append, append)∈⟨R⟩list_rel → ⟨R⟩list_rel → ⟨R⟩list_rel"
    by (auto simp: list_rel_def list_all2_appendI)

  lemma refine_list[autoref_rules]:
    "(Nil,Nil)∈⟨R⟩list_rel"
    "(Cons,Cons)∈R → ⟨R⟩list_rel → ⟨R⟩list_rel"
    "(case_list,case_list)∈Rr→(R→⟨R⟩list_rel→Rr)→⟨R⟩list_rel→Rr"
    apply (force dest: fun_relD split: list.split)+
    done
```

List equality (needed by the two `[1,2,3] = []` / `[1,2] = [2,3::nat]`
examples — note the `GEN_OP`-driven structural-expansion route, a nice small
showcase of the tagging/solver-phase discipline: `(=)` on lists is *proved
equal to* `list_eq (=)` and then `list_eq` is what actually carries a
`[param]`/`autoref_rules` binding):

```isabelle
  fun list_eq :: "('a ⇒ 'a ⇒ bool) ⇒ 'a list ⇒ 'a list ⇒ bool" where
    "list_eq eq [] [] ⟷ True"
  | "list_eq eq (a#l) (a'#l') 
       ⟷ (if eq a a' then list_eq eq l l' else False)"
  | "list_eq _ _ _ ⟷ False"

  lemma autoref_list_eq_aux: "
    (list_eq,list_eq) ∈ 
      (R → R → Id) → ⟨R⟩list_rel → ⟨R⟩list_rel → Id"
  proof (intro fun_relI, goal_cases)
    case (1 eq eq' l1 l1' l2 l2')
    thus ?case
      apply -
      apply (induct eq' l1' l2' arbitrary: l1 l2 rule: list_eq.induct)
      apply simp
      apply (case_tac l1)
      apply simp
      apply (case_tac l2)
      apply (simp)
      apply (auto dest: fun_relD) []
      apply (case_tac l1)
      apply simp
      apply simp
      apply (case_tac l2)
      apply simp
      apply simp
      done
  qed

  lemma list_eq_expand[autoref_struct_expand]: "(=) = (list_eq (=))"
  proof (intro ext)
    fix l1 l2 :: "'a list"
    show "(l1 = l2) ⟷ list_eq (=) l1 l2"
      apply (induct "(=) :: 'a ⇒ _" l1 l2 rule: list_eq.induct)
      apply simp_all
      done
  qed

  lemma autoref_list_eq[autoref_rules (overloaded)]:
    "GEN_OP eq (=) (R→R→Id) ⟹ (list_eq eq, (=)) 
    ∈ ⟨R⟩list_rel → ⟨R⟩list_rel → Id"
    unfolding autoref_tag_defs
    apply (subst list_eq_expand)
    apply (parametricity add: autoref_list_eq_aux)
    done
```

`hd` (needed by the two `hd [a,b,c::'a::numeral]` examples):

```isabelle
  lemma autoref_hd[autoref_rules]:
    "⟦ SIDE_PRECOND (l'≠[]); (l,l') ∈ ⟨R⟩list_rel ⟧ ⟹
      (hd l,(OP hd ::: ⟨R⟩list_rel → R)$l') ∈ R"
    apply (simp add: ANNOT_def)
    apply (cases l')
    apply simp
    apply (cases l)
    apply auto
    done
```

`option_rel`'s `None`/`Some` (needed by the `a = None` example):

```isabelle
    lemma autoref_opt[autoref_rules]:
      "(None,None)∈⟨R⟩option_rel"
      "(Some,Some)∈R → ⟨R⟩option_rel"
      "(case_option,case_option)∈Rr→(R → Rr)→⟨R⟩option_rel → Rr"
      "(rec_option,rec_option)∈Rr→(R → Rr)→⟨R⟩option_rel → Rr"
      by (auto split: option.split 
        simp: option_rel_def case_option_def[symmetric]
        dest: fun_relD)
```

`is_None` (the actual operator `a = None` gets rewritten to, via
`autoref_op_pat`, before the rule below fires — the rewrite lemma itself is
elided, see Gaps):

```isabelle
    definition [simp]: "is_None a ≡ case a of None ⇒ True | _ ⇒ False"
    lemma autoref_is_None[param,autoref_rules]: 
      "(is_None,is_None)∈⟨R⟩option_rel → Id"
      by (auto split: option.splits)
```

`is_Nil` (analogous rewrite target for `[] = a`):

```isabelle
  definition [simp]: "is_Nil a ≡ case a of [] ⇒ True | _ ⇒ False"
  lemma autoref_is_Nil[param,autoref_rules]: 
    "(is_Nil,is_Nil)∈⟨R⟩list_rel → bool_rel"
    by (auto split: list.splits)
```

## 4. The self-contained pure-HOL reproduction target — `Autoref_Bindings_HOL.thy` §"Examples", in full

```isabelle
subsection "Examples"

text ‹Be careful to make the concrete type a schematic type variable.
  The default behaviour of ‹schematic_lemma› makes it a fixed variable,
  that will not unify with the infered term!›
schematic_goal 
  "(?f::?'c,[1,2,3]@[4::nat])∈?R"
  by autoref

schematic_goal 
  "(?f::?'c,[1::nat,
    2,3,4,5,6,7,8,9,0,1,43,5,5,435,5,1,5,6,5,6,5,63,56
  ]
  )∈?R"
  apply (autoref)
  done

schematic_goal 
  "(?f::?'c,[1,2,3] = [])∈?R"
  by autoref

text ‹
  When specifying custom refinement rules on the fly, be careful with
  the type-inference between ‹notes› and ‹shows›. It's
  too easy to ,,decouple'' the type ‹'a› in the autoref-rule and
  the actual goal, as shown below!
›

schematic_goal 
  notes [autoref_rules] = IdI[where 'a="'a"]
  notes [autoref_itype] = itypeI[where 't="'a::numeral" and I=i_std]
  shows "(?f::?'c, hd [a,b,c::'a::numeral])∈?R"
  txt ‹The autoref-rule is bound with type ‹'a::typ›, while
    the goal statement has ‹'a::numeral›!›
  apply (autoref (keep_goal))
  txt ‹We get an unsolved goal, as it finds no rule to translate 
    ‹a››
  oops

text ‹Here comes the correct version. Note the duplicate sort annotation
  of type ‹'a›:›
schematic_goal 
  notes [autoref_rules_raw] = IdI[where 'a="'a::numeral"]
  notes [autoref_itype] = itypeI[where 't="'a::numeral" and I=i_std]
  shows "(?f::?'c, hd [a,b,c::'a::numeral])∈?R"
  by (autoref)

text ‹Special cases of equality: Note that we do not require equality
  on the element type!›
schematic_goal 
  assumes [autoref_rules]: "(ai,a)∈⟨R⟩option_rel"
  shows "(?f::?'c, a = None)∈?R"
  apply (autoref (keep_goal))
  done


schematic_goal 
  assumes [autoref_rules]: "(ai,a)∈⟨R⟩list_rel"  
  shows "(?f::?'c, [] = a)∈?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  shows "(?f::?'c, [1,2] = [2,3::nat])∈?R"
  apply (autoref (keep_goal))
  done


end
```

Every relator in this section is one of `Id`/`nat_rel`, `⟨R⟩list_rel`, or
`⟨R⟩option_rel`; every operator (`@`, `Nil`/`Cons`, `(=)`, `hd`) is bound by
an `autoref_rules`/`param` entry quoted in §3. No Collections import, no
`autoref_monadic`, no `concrete_definition` — a bare `schematic_goal … by
autoref` (or `apply (autoref (keep_goal)); done`) is the entire derivation.

## 5. Refine_Monadic's own examples — checked, no autoref usage found

`Refine_Monadic/` top level (relevant entries only):

```
Autoref_Monadic.thy    1939
Refine_Basic.thy      73138
Refine_Foreach.thy    81491
Refine_While.thy       54291
examples/             (dir)
```

`Refine_Monadic/examples/`:

```
Breadth_First_Search.thy   19497
Example_Chapter.thy          349
Examples.thy                  102
WordRefine.thy               2369
```

`Collections/Examples/Refine_Monadic/`:

```
Bfs_Impl.thy          8092
Foreach_Refine.thy    5169
Refine_Fold.thy       4450
Refine_Monadic_Examples.thy    201
Refine_Monadic_Examples_Chapter.thy  315
```

None of these files use the `autoref`/`autoref_monadic` **tactics**. Each
does contain exactly one `schematic_goal` (`Foreach_Refine.thy`,
`Refine_Fold.thy`, `Bfs_Impl.thy`), but every one is a plain refinement goal
of the shape `RETURN ?f ≤ concrete_program` discharged by `refine_rcg`/
`refine_vcg` — hand-written data refinement, not Autoref-synthesised.
`WordRefine.thy` (quoted in full below, 2369 bytes, since it's the smallest
and most plausible candidate the task flagged) is likewise entirely
hand-written: it defines `word_nat_rel` by hand and proves `test_impl_refine`
by `refine_rcg`/`refine_dref_type`, never invoking `autoref`.

```isabelle
section \<open>Machine Words\<close>
theory WordRefine
imports "../Refine_Monadic" "HOL-Library.Word"
begin

text \<open>This theory provides a simple example to show refinement of natural
  numbers to machine words. The setup is not yet very elaborated, but shows 
  the direction to go.
\<close>

subsection \<open>Setup\<close>
definition [simp]: "word_nat_rel \<equiv> build_rel (unat) (\<lambda>_. True)"
lemma word_nat_RELEATES[refine_dref_RELATES]: 
  "RELATES word_nat_rel" by (simp add: RELATES_def)

lemma [simp, relator_props]: 
  "single_valued word_nat_rel" unfolding word_nat_rel_def
  by blast

lemma [simp]: "right_unique (\<lambda>c a. a = unat c)" 
  by (rule right_uniqueI) blast

lemma [simp, relator_props]: "single_valued (converse word_nat_rel)" 
  by (auto intro: injI)

lemmas [refine_hsimp] = 
  word_less_nat_alt word_le_nat_alt unat_sub iffD1[OF unat_add_lem]

subsection \<open>Example\<close>
type_synonym word32 = "32 word"

definition test :: "nat \<Rightarrow> nat \<Rightarrow> nat set nres" where "test x0 y0 \<equiv> do {
  let S={};
  (S,_,_) \<leftarrow> WHILE (\<lambda>(S,x,y). x>0) (\<lambda>(S,x,y). do {
    let S=S\<union>{y};
    let x=x - 1;
    ASSERT (y<x0+y0);
    let y=y + 1;
    RETURN (S,x,y)
  }) (S,x0,y0);
  RETURN S
}"

lemma "y0>0 \<Longrightarrow> test x0 y0 \<le> SPEC (\<lambda>S. S={y0 .. y0 + x0 - 1})"
  \<comment> \<open>Choosen pre-condition to get least trouble when proving\<close>
  unfolding test_def
  apply (intro WHILE_rule[where I="\<lambda>(S,x,y). 
    x+y=x0+y0 \<and> x\<le>x0 \<and>
    S={y0 .. y0 + (x0-x) - 1}"] 
    refine_vcg)
  by auto

definition test_impl :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 set nres" where 
  "test_impl x y \<equiv> do {
    let S={};
    (S,_,_) \<leftarrow> WHILE (\<lambda>(S,x,y). x>0) (\<lambda>(S,x,y). do {
      let S=S\<union>{y}; 
      let x=x - 1;
      let y=y + 1;
      RETURN (S,x,y)
    }) (S,x,y);
    RETURN S
  }"

lemma test_impl_refine: 
  assumes "x'+y'<2^LENGTH(32)"
  assumes "(x,x')\<in>word_nat_rel" 
  assumes "(y,y')\<in>word_nat_rel" 
  shows "test_impl x y \<le> \<Down>(\<langle>word_nat_rel\<rangle>set_rel) (test x' y')"
proof -
  from assms show ?thesis
    unfolding test_impl_def test_def
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (auto simp: refine_hsimp refine_rel_defs)
  done
qed

end
```

(Left in raw ASCII-cartouche form as fetched, rather than transliterated to
Unicode like the other extracts above, since this file is quoted in full as
negative evidence — "not an autoref example" — rather than as reproduction
material; no operator-binding table is derived from it.)

`Autoref_Monadic.thy` (the bridge theory living in `Refine_Monadic`, imported
by anything that wants `autoref_monadic`) confirms the phase-pipeline
composition described in §2.3: its `method_setup autoref_monadic` (ML
elided, per the same convention as the companion file's treatment of
`Param_Tool.thy`) is literally `resolve_tac @{thms autoref_monadicI} THEN'
IF_SOLVED (Autoref_Phases.all_phases_tac ctxt) (RefineG_Transfer.post_transfer_tac …) (K all_tac)`
— Autoref's phases, then (if they succeeded) the Refinement Monad's
determinization/transfer. It ships no examples of its own.

## Gaps

- The task's suggested filename pattern (`Autoref_Tutorial.thy` or similar)
  does not exist anywhere in `Automatic_Refinement/`, `Collections/`, or
  `Refine_Monadic/`; the closest matches are `Simple_DFS.thy` (narrative,
  used above) and the flat `Coll_Test.thy`/`ICF_Only_Test.thy`/`ICF_Test.thy`
  regression batteries (listed, not extracted — see §2 resolution note).
- `dfs_correct` and the `reachable`/closure lemmas around it
  (`Simple_DFS.thy` lines ~74–79, ~300–346) were elided from §2.1/§2.2: they
  use Isabelle's reflexive-transitive-closure notation (`E\<^sup>*`) which
  falls outside the small, hand-checked Unicode substitution table used for
  this extract, and they are correctness-proof plumbing rather than autoref
  derivation text, so nothing about the *tutorial's autoref usage* is lost by
  leaving them out in prose-paraphrase form instead of verbatim.
- `dfs_impl_refine_aux3`/`dfs_impl_refine_aux3'` (`Simple_DFS.thy` lines
  ~377–407: generic node type + custom comparator via `dflt_rs_rel`/
  `rbt_map_rel`/`comp2lt`/the Containers framework) are mentioned but not
  quoted — same OUT-OF-SCOPE Collections-data-structure territory as §2.5,
  and add no new spine mechanism beyond what §2.5's `autoref_tyrel` already
  shows.
- Two commented-out (`(*...*)`) alternative `notes [autoref_itype] =
  itypeI[of a "⟨I⟩\<^sub>ii_option"]`-style lines were dropped from the §4
  quote of the `a = None` / `[] = a` examples (they are dead code in the
  source, superseded by the live `assumes [autoref_rules]` lines immediately
  below them) — the two commented `(*notes …*)` lines right before those
  `assumes` lines, specifically.
- The `is_None_pat`/`is_Nil_pat` `autoref_op_pat` rewrite lemmas (the
  `a=None ≡ (OP is_None ::: …)$a` -style rules that redirect `(=)` to
  `is_None`/`is_Nil` before the §3 rules fire) were elided from §3 — they're
  interface-level (`\<^sub>i`) annotation machinery, one layer above the
  relator-level `autoref_rules` the task asked for ("their `autoref_rules`/
  `param` declarations and relator setup"), and are already the subject of
  the companion file's `Autoref_Id_Ops.thy`/`Autoref_Tagging.thy` section.
- All commented-out (`(* … *)`) `autoref_itype` blocks throughout
  `Autoref_Bindings_HOL.thy` (interface declarations for `prod`/`option`/
  `list` — e.g. the block at what would be lines ~267–276, ~306–315,
  ~420–442 in the live file) were skipped for the same reason: dead code,
  interface-level, and already out of the `autoref_rules`/`param`/relator
  scope the task specified.
- Did not re-verify the `mirror-afp-2025-1` vs `mirror-afp-devel` path
  question independently for `Collections`/`Refine_Monadic` — inherited the
  companion file's finding and used `mirror-afp-devel` throughout to keep
  the two extract files internally consistent.
- Isabelle source symbols were transliterated from the raw ASCII
  `\<foo>`-cartouche encoding (confirmed via `od -c` on the raw fetched
  bytes — `Automatic_Refinement`'s theories are *not* stored as literal
  UTF-8 arrows in the repo) to their standard Unicode equivalents, matching
  the companion file's rendering convention, via a fixed, manually verified
  substitution table (`\<in>`→∈, `\<rightarrow>`→→, `\<langle>`/`\<rangle>`→⟨⟩,
  `\<Longrightarrow>`→⟹, `\<lambda>`→λ, `\<open>`/`\<close>`→‹›, etc. — diffed
  round-trip against the raw source for every quoted block in this file to
  confirm no token was silently dropped or mis-mapped, except the two
  intentional elisions noted above). The one exception is `WordRefine.thy`
  (§5), left in raw ASCII-cartouche form since it's quoted as negative
  evidence, not reproduction material. `\<^sup>` (superscript, used only for
  `E\<^sup>*`) was avoided by trimming quotes rather than added to the table.
  `\<comment>` was left as the literal keyword `\<comment>` (it is an Isar
  keyword, not a symbol with a single-codepoint Unicode rendering), with
  only its `\<open>...\<close>` argument converted to `‹...›`.

## Recommendation

**Target the `Autoref_Bindings_HOL.thy` §"Examples" list append entry**:
`schematic_goal "(?f::?'c,[1,2,3]@[4::nat])∈?R" by autoref` (§4, first
entry). Justification: it is the simplest possible non-trivial exercise of
the full P2 spine — relator inference (`nat_rel`, `⟨nat_rel⟩list_rel`),
operator identification and rule-DB lookup (`autoref_append`, `refine_list`'s
`Nil`/`Cons`, `autoref_nat`'s numeral rules), and the phase pipeline, all in
one `by autoref` call — while touching *zero* Collections data structures and
*zero* Refine_Monadic determinization machinery, unlike every candidate in
`Simple_DFS.thy` (all three of which are permanently gated on
`list_set_rel`/`dflt_ahs_rel`, P6 material) or in `Coll_Test.thy`/
`ICF_Only_Test.thy` (gated from their first line). It is also, literally,
inside the entry being ported (`Automatic_Refinement`, not a downstream
consumer session), so reproducing it needs no cross-session import story at
all for the Lean port. Once that lands, the second (`[1,2,3] = []`) and
fifth/sixth (`a = None`, `[] = a`) entries in the same list are natural
follow-on acceptance targets in the same P2 wave: they exercise the
`GEN_OP`/structural-expansion solver phase (list/option/`is_None`/`is_Nil`
rewriting) that plain `append` doesn't touch, at essentially no extra
porting cost since their bindings are already extracted in §3 above.
