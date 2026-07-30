# P6 IICF Extracts

Source: `github.com/lammich/isabelle_llvm_time` @ `42dd7f59998d76047bb4b6bce76d8f67b53a08b6` (pinned).
Fetched whole-file via raw.githubusercontent.com; local copies saved under
`/home/jan/.claude/jobs/2a430b98/tmp/` as `IICF.thy`, `IICF_List.thy`, `IICF_Set.thy`,
`IICF_Map.thy`, `IICF_Array.thy`, `IICF_Array_List.thy`, `IICF_Array_Map_Total.thy`.

These extracts are for the P6 IICF-collections port. House style: verbatim Isabelle in
` ```isabelle ` fences, one numbered `#` section per item, provenance line under each block
(`<file>, lines a–b`), proof bodies elided to signature + one-line idea unless the statement
itself IS the content (hnr rules, cost annotations — those are quoted in full).

---

# 1. IICF architecture

`IICF.thy` itself carries almost no prose — it is a pure import hub gathering the interface
(`Intf/`) and implementation (`Impl/`) theories, plus a small `experiment` regression block.
The architecture is stated by its **directory structure and import list**, not by running text:

```isabelle
section \<open>The LLVM Imperative Isabelle Collection Framework\<close>
theory IICF
imports 
  (* Sets *)
  "Intf/IICF_Set"

  (* Multisets *)
  "Intf/IICF_Multiset"
  "Intf/IICF_Prio_Bag"

  "Impl/Heaps/IICF_Impl_Heap"
  

  (* Maps *)
  "Intf/IICF_Map"
  "Intf/IICF_Prio_Map"

  "Impl/IICF_Array_Map"
  "Impl/IICF_Array_Map_Total"

  
  "Impl/Heaps/IICF_Impl_Heapmap"
    
  (* Lists *)
  "Intf/IICF_List"

  "Impl/IICF_Array"
  "Impl/IICF_Array_List"
  "Impl/IICF_Array_of_Array_List"
  (* Matrix *)
  (*"Intf/IICF_Matrix"*)


begin
```
IICF.thy, lines 1–34.

**Reading of the split.** `Intf/*` theories fix an *abstract data type* (list, set, map — plain
HOL types under a parametricity relation such as `\<langle>A\<rangle>list_rel`, `\<langle>A\<rangle>set_rel`,
`\<langle>K,V\<rangle>map_rel`) and declare its operations twice: a **pure** `op_*` (a plain HOL function,
used for rewriting/patterns) and a **cost-monadic** `mop_*` (an `nres`/NREST computation, the
thing sepref actually refines). `Impl/*` theories fix one concrete LLVM-level representation
(array, resizable array, ...) and, for every `mop_*`/`op_*` of the interface it implements,
supply an `hn_refine` ("hnr") rule from a **raw** assertion straight to the LLVM operation, then
compose that raw rule with the interface's own parametricity lemma via `FCOMP` to produce the
final rule that sepref's rule database (`sepref_fr_rules`) sees. This FCOMP step is exactly the
"cost-carrying fork": the interface layer's `mop_*` is refined *without* committing to a cost, and
the Impl layer's raw hnr rule is where a concrete named-currency cost enters; composing them
propagates that cost up to the interface type.

**Interface-type / `intf_of_assn` mechanism.** Each interface theory registers a nominal HOL
type via `sepref_decl_intf` to stand for the abstract type of the interface (so error messages
and internal bookkeeping refer to `i_map`, `i_list`, ... rather than raw HOL types), e.g.:
```isabelle
sepref_decl_intf ('k,'v) i_map is "'k \<rightharpoonup> 'v"
```
IICF_Map.thy, line 69.

An implementation registers, for its own assertion, which interface type it stands for via the
`intf_of_assn` lemma-attribute:
```isabelle
lemma amt_assn_intf[intf_of_assn]: "intf_of_assn V TYPE('v) \<Longrightarrow> intf_of_assn (amt_assn V N) (TYPE((nat,'v)i_map))"
  by simp
```
IICF_Array_Map_Total.thy, lines 70–71.

**`is_pure` / `is_init`.** Assertions that are actually pure (no separation-logic footprint,
just an equality-like relation) are marked so frame-inference constraint-solving can special-case
them, e.g. `array_assn A` is explicitly registered as *not* automatically pure via a
`CN_FALSEI` safe-constraint (it has a real heap footprint even though its element assertion `A`
may be pure):
```isabelle
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "array_assn A" for A]
```
IICF_Array.thy, line 78.

Element types that possess a canonical "zero/init" value usable for replicate-style allocation
are captured by the `is_init`/`GEN_ALGO` synthesis mechanism, consumed by the `replicate_init`
locale (see §3):
```isabelle
locale replicate_init = 
  fixes repl :: "'a \<Rightarrow> nat \<Rightarrow> 'a list"  
  assumes repl_def[simp]: "repl i n = replicate n i"
begin
  context fixes i::'a begin
    sepref_register "repl i" 
  end
  lemma replicate_init_param:
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn"
    assumes INIT: "GEN_ALGO i (is_init A)"
    shows "(RETURN o replicate_init_raw, RETURN o PR_CONST (repl i)) \<in> nat_rel \<rightarrow>\<^sub>f \<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>nres_rel"
```
IICF_Array.thy, lines 13–26 (abridged; proof body omitted).

**hnr rule naming convention** observed uniformly across the fetched files: a raw hnr fact is
proved under a name ending `_hnr_aux` (or `_hnr_raw`), then handed to
`sepref_decl_impl <name>: <fact>` (interface-registering) or `sepref_decl_impl (ismop) <name>.refine`
(when composing a `sepref_definition`'s `.refine` lemma) or `sepref_decl_impl (no_mop) ... uses
<parametricity-lemma>` (when the interface op has no separate mop, e.g. replicate-init). The
command derives and stores a lemma named `<name>_hnr` in the context — e.g. `array_free_hnr` is
referenced immediately after being produced:
```isabelle
sepref_decl_impl array_free: hn_array_free_raw .
lemmas array_mk_free[sepref_frame_free_rules] = hn_MK_FREEI[OF array_free_hnr]
```
IICF_Array.thy, lines 226–227.

---

# 2. Interface layer pattern (IICF_List / IICF_Set / IICF_Map)

## 2.1 The `sepref_decl_op` command

Every interface operation is declared with a single `sepref_decl_op <name>: <pure-def> ::
<parametricity-type>` invocation. This one command (defined outside the fetched files, in
`Sepref_Combinator_Setup.thy`) is what silently generates the paired `op_<name>` (pure HOL
constant) and `mop_<name>` (NREST-monadic constant with an `ASSERT` guard for the precondition
and a `RETURNT` of the pure result) plus their parametricity/refinement facts and
`sepref_register`ing. **Crucially, in this pinned commit the abstract `mop_*` constants generated
by `sepref_decl_op` carry NO explicit named-currency cost annotation at the interface layer** —
no `consume`/`$cost` term appears anywhere in `IICF_List.thy`, `IICF_Set.thy`, or `IICF_Map.thy`
(grep-confirmed: zero hits for `consume` or `cost` in all three). The interface layer states
functional refinement only; cost enters exclusively at the Impl layer's raw hnr rule (§3) and is
propagated upward through `FCOMP`. See §7 (Gaps) — this is the single most important structural
fact for the port's cost design.

## 2.2 IICF_List.thy — list interface

Parametricity lemmas used by the ops (verbatim):
```isabelle
lemma param_index[param]: 
  "\<lbrakk>single_valued A; single_valued (A\<inverse>)\<rbrakk> \<Longrightarrow> (index,index) \<in> \<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> nat_rel"
  unfolding index_def[abs_def] find_index_def 
  apply (subgoal_tac "(((=), (=)) \<in> A \<rightarrow> A \<rightarrow> bool_rel)")
  apply parametricity
  by (simp add: pres_eq_iff_svb)
```
IICF_List.thy, lines 7–12.

```isabelle
lemma swap_param[param]: "\<lbrakk> i<length l; j<length l; (l',l)\<in>\<langle>A\<rangle>list_rel; (i',i)\<in>nat_rel; (j',j)\<in>nat_rel\<rbrakk>
  \<Longrightarrow> (swap l' i' j', swap l i j)\<in>\<langle>A\<rangle>list_rel"
  unfolding swap_def
  by parametricity
```
IICF_List.thy, lines 17–20.

All declared list operations, verbatim:
```isabelle
sepref_decl_op list_empty: "[]" :: "\<langle>A\<rangle>list_rel" .
context notes [simp] = eq_Nil_null begin
  sepref_decl_op list_is_empty: "\<lambda>l. l=[]" :: "\<langle>A\<rangle>list_rel \<rightarrow>\<^sub>f bool_rel" .
end
  
sepref_decl_op list_replicate: replicate :: "nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .


definition op_list_copy :: "'a list \<Rightarrow> 'a list" where [simp]:  "op_list_copy l \<equiv> l"
sepref_decl_op (no_def) list_copy: "op_list_copy" :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_prepend: "(#)" :: "A \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_append: "\<lambda>xs x. xs@[x]" :: "\<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_concat: "(@)" :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_take: take :: "[\<lambda>(i,l). i\<le>length l]\<^sub>f nat_rel \<times>\<^sub>r \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_drop: drop :: "[\<lambda>(i,l). i\<le>length l]\<^sub>f nat_rel \<times>\<^sub>r \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_length: length :: "\<langle>A\<rangle>list_rel \<rightarrow> nat_rel" .
sepref_decl_op list_get: nth :: "[\<lambda>(l,i). i<length l]\<^sub>f \<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> A" .
sepref_decl_op list_set: list_update :: "[\<lambda>((l,i),_). i<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r A \<rightarrow> \<langle>A\<rangle>list_rel" .
context notes [simp] = eq_Nil_null begin
  sepref_decl_op list_hd: hd :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A" .
  sepref_decl_op list_tl: tl :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
  sepref_decl_op list_last: last :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A" .
  sepref_decl_op list_butlast: butlast :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
  sepref_decl_op list_pop_last: "(\<lambda>l. (last l, butlast l))" :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A \<times>\<^sub>r \<langle>A\<rangle>list_rel" .
end
sepref_decl_op list_contains: "\<lambda>x l. x\<in>set l" :: "A \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel" 
  where "single_valued A" "single_valued (A\<inverse>)" .
sepref_decl_op list_swap: swap :: "[\<lambda>((l,i),j). i<length l \<and> j<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_rotate1: rotate1 :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_rev: rev :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_index: index :: "\<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> nat_rel" 
  where "single_valued A" "single_valued (A\<inverse>)" .
```
IICF_List.thy, lines 42–73.

Pattern declarations (`op_list_*` recognized from raw HOL syntax during monadification), verbatim:
```isabelle
lemma [def_pat_rules]:
  "[] \<equiv> op_list_empty"
  "(=) $l$[] \<equiv> op_list_is_empty$l"
  "(=) $[]$l \<equiv> op_list_is_empty$l"
  "replicate$n$v \<equiv> op_list_replicate$n$v"
  "Cons$x$xs \<equiv> op_list_prepend$x$xs"
  "(@) $xs$(Cons$x$[]) \<equiv> op_list_append$xs$x"
  "(@) $xs$ys \<equiv> op_list_concat$xs$ys"
  "take$i$l \<equiv> op_list_take$i$l"
  "drop$i$l \<equiv> op_list_drop$i$l"
  "op_list_concat$xs$(Cons$x$[]) \<equiv> op_list_append$xs$x"
  "length$xs \<equiv> op_list_length$xs"
  "nth$l$i \<equiv> op_list_get$l$i"
  "list_update$l$i$x \<equiv> op_list_set$l$i$x"
  "hd$l \<equiv> op_list_hd$l"
  "hd$l \<equiv> op_list_hd$l"
  "tl$l \<equiv> op_list_tl$l"
  "tl$l \<equiv> op_list_tl$l"
  "last$l \<equiv> op_list_last$l"
  "butlast$l \<equiv> op_list_butlast$l"
  "(\<in>) $x$(set$l) \<equiv> op_list_contains$x$l"
  "swap$l$i$j \<equiv> op_list_swap$l$i$j"
  "rotate1$l \<equiv> op_list_rotate1$l"
  "rev$l \<equiv> op_list_rev$l"
  "index$l$x \<equiv> op_list_index$l$x"
  by (auto intro!: eq_reflection)
```
IICF_List.thy, lines 76–101.

Fcomp pre-normalization simp set for standard preconditions:
```isabelle
lemma list_rel_pres_neq_nil[fcomp_prenorm_simps]: "(x',x)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> x'\<noteq>[] \<longleftrightarrow> x\<noteq>[]" by auto
lemma list_rel_pres_length[fcomp_prenorm_simps]: "(x',x)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> length x' = length x" by (rule list_rel_imp_same_length)

declare list_rel_imp_same_length[sepref_bounds_dest]
```
IICF_List.thy, lines 105–108.

Custom-empty locale pattern (reused verbatim by array/al/larray impls — this is the standard
idiom for letting an implementation override the *generic* empty-op with its own more specific
allocation while keeping the same interface constant):
```isabelle
locale list_custom_empty = 
  fixes rel empty and op_custom_empty :: "'a list"
  assumes customize_hnr_aux: "(uncurry0 empty,uncurry0 (RETURN (op_list_empty::'a list))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a rel"
  assumes op_custom_empty_def: "op_custom_empty = op_list_empty"
begin
  sepref_register op_custom_empty :: "'c list"

  lemma fold_custom_empty:
    "[] = op_custom_empty"
    "op_list_empty = op_custom_empty"
    "mop_list_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all

  lemmas custom_hnr[sepref_fr_rules] = customize_hnr_aux[folded op_custom_empty_def]
end
```
IICF_List.thy, lines 110–124.

`swap` generic-unfolding lemmas (used by Impl layer to implement swap via get/get/set/set,
see IICF_Array.thy's `array_swap`):
```isabelle
lemma gen_swap: "swap xs i j = (let
  xi = op_list_get xs i;
  xj = op_list_get xs j;
  xs = op_list_set xs i xj;
  xs = op_list_set xs j xi 
  in xs)"
  by (auto simp: swap_def)

lemma gen_mop_list_swap: "mop_list_swap l i j = do {
    xi \<leftarrow> mop_list_get l i;
    xj \<leftarrow> mop_list_get l j;
    l \<leftarrow> mop_list_set l i xj;
    l \<leftarrow> mop_list_set l j xi;
    RETURN l
  }"
  unfolding mop_list_swap_def
  by (auto simp: pw_eq_iff refine_pw_simps gen_swap)

lemmas gen_op_list_swap = gen_swap[folded op_list_swap_def]
```
IICF_List.thy, lines 127–145. Note again: `mop_list_swap`'s generic unfolding shows a plain
monadic bind chain — no cost term. Cost is entirely absent at this layer.

## 2.3 IICF_Set.thy — set interface

```isabelle
definition [simp]: "op_set_is_empty s \<equiv> s={}"
lemma op_set_is_empty_param[param]: "(op_set_is_empty,op_set_is_empty)\<in>\<langle>A\<rangle>set_rel \<rightarrow> bool_rel" by auto

context 
  notes [simp] = IS_LEFT_UNIQUE_def (* Argh, the set parametricity lemmas use single_valued (K\<inverse>) here. *)
begin

sepref_decl_op set_empty: "{}" :: "\<langle>A\<rangle>set_rel" .
sepref_decl_op (no_def) set_is_empty: op_set_is_empty :: "\<langle>A\<rangle>set_rel \<rightarrow> bool_rel" .
sepref_decl_op set_member: "(\<in>)" :: "A \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> bool_rel" where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_insert: Set.insert :: "A \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_delete: "\<lambda>x s. s - {x}" :: "A \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" 
  where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_union: "(\<union>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" .
sepref_decl_op set_inter: "(\<inter>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_diff: "(-) ::_ set \<Rightarrow> _" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_subseteq: "(\<subseteq>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> bool_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_subset: "(\<subset>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> bool_rel" where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" .

(* TODO: We may want different operations here: pick with predicate returning option,
  pick with remove, ... *)    
sepref_decl_op set_pick: "RES" :: "[\<lambda>s. s\<noteq>{}]\<^sub>f \<langle>K\<rangle>set_rel \<rightarrow> K" by auto

end
```
IICF_Set.thy, lines 7–30.

Patterns:
```isabelle
lemma pat_set[def_pat_rules]:
  "{} \<equiv> op_set_empty"
  "(\<in>) \<equiv> op_set_member"    
  "Set.insert \<equiv> op_set_insert"
  "(\<union>) \<equiv> op_set_union"
  "(\<inter>) \<equiv> op_set_inter"
  "(-) \<equiv> op_set_diff"
  "(\<subseteq>) \<equiv> op_set_subseteq"
  "(\<subset>) \<equiv> op_set_subset"
  by (auto intro!: eq_reflection)
  
lemma pat_set2[pat_rules]: 
  "(=) $s${} \<equiv> op_set_is_empty$s"
  "(=) ${}$s \<equiv> op_set_is_empty$s"

  "(-) $s$(Set.insert$x${}) \<equiv> op_set_delete$x$s"
  "SPEC$(\<lambda>\<^sub>2x. (\<in>) $x$s) \<equiv> op_set_pick s"
  "RES$s \<equiv> op_set_pick s"
  by (auto intro!: eq_reflection)
```
IICF_Set.thy, lines 35–53. Note `op_set_pick`'s spec is `RES` (nondeterministic choice over the
whole set) — the mop generated for it has no cost, and correspondingly the implementation cannot
be a plain array/hash pick without extra reasoning (relevant if P6 needs a "pick" op — flag for Gaps).

`set_custom_empty` locale (same idiom as `list_custom_empty`):
```isabelle
locale set_custom_empty = 
  fixes empty and op_custom_empty :: "'a set"
  assumes op_custom_empty_def: "op_custom_empty = op_set_empty"
begin
  sepref_register op_custom_empty :: "'ax set"

  lemma fold_custom_empty:
    "{} = op_custom_empty"
    "op_set_empty = op_custom_empty"
    "mop_set_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all
end
```
IICF_Set.thy, lines 56–67.

## 2.4 IICF_Map.thy — map interface

Map relation (this is the parametricity-relation analogue of `list_rel`/`set_rel` for maps —
central to the port's `map_rel` design):
```isabelle
definition [to_relAPP]: "map_rel K V \<equiv> (K \<rightarrow> \<langle>V\<rangle>option_rel)
  \<inter> { (mi,m). dom mi \<subseteq> Domain K \<and> dom m \<subseteq> Range K }"
```
IICF_Map.thy, lines 7–8. (A commented-out stricter variant adding `ran` constraints is left in
place, lines 9–13 — evidence the authors considered and rejected requiring `ran` containment.)

Interface type declaration:
```isabelle
sepref_decl_intf ('k,'v) i_map is "'k \<rightharpoonup> 'v"

lemma [synth_rules]: "\<lbrakk>INTF_OF_REL K TYPE('k); INTF_OF_REL V TYPE('v)\<rbrakk> 
  \<Longrightarrow> INTF_OF_REL (\<langle>K,V\<rangle>map_rel) TYPE(('k,'v) i_map)" by simp
```
IICF_Map.thy, lines 69–72.

All declared map operations, verbatim (note the two which need explicit side-conditions
`single_valued K`/`single_valued (K\<inverse>)` for the key relation, and the raw `dom`
parametricity lemma each op's proof leans on):
```isabelle
lemma param_dom[param]: "(dom,dom)\<in>\<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K\<rangle>set_rel"
  apply (clarsimp simp: set_rel_def; safe)
  apply (erule (1) map_rel_obtain2; auto)
  apply (erule (1) map_rel_obtain1; auto)
  done

sepref_decl_op map_empty: "Map.empty" :: "\<langle>K,V\<rangle>map_rel" .

sepref_decl_op map_is_empty: "(=) Map.empty" :: "\<langle>K,V\<rangle>map_rel \<rightarrow> bool_rel"
  apply (rule fref_ncI)
  apply parametricity
  apply (rule fun_relI; auto)
  done

sepref_decl_op map_update: "\<lambda>k v m. m(k\<mapsto>v)" :: "K \<rightarrow> V \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K,V\<rangle>map_rel"
  where "single_valued K" "single_valued (K\<inverse>)"
  apply (rule fref_ncI)
  apply parametricity
  unfolding map_rel_def
  apply (intro fun_relI)
  apply (elim IntE; rule IntI)
  apply (intro fun_relI)
  apply parametricity
  apply (simp add: pres_eq_iff_svb)
  apply auto
  done
  
sepref_decl_op map_delete: "\<lambda>k m. fun_upd m k None" :: "K \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K,V\<rangle>map_rel"
  where "single_valued K" "single_valued (K\<inverse>)"
  apply (rule fref_ncI)
  apply parametricity
  unfolding map_rel_def
  apply (intro fun_relI)
  apply (elim IntE; rule IntI)
  apply (intro fun_relI)
  apply parametricity
  apply (simp add: pres_eq_iff_svb)
  apply auto
  done

sepref_decl_op map_lookup: "\<lambda>k (m::'k\<rightharpoonup>'v). m k" :: "K \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>V\<rangle>option_rel"
  apply (rule fref_ncI)
  apply parametricity
  unfolding map_rel_def
  apply (intro fun_relI)
  apply (elim IntE)
  apply parametricity
  done
  
sepref_decl_op map_the_lookup: 
  "the oo op_map_lookup" :: "[\<lambda>(k,m). m k \<noteq> None]\<^sub>f K \<times>\<^sub>r \<langle>K,V\<rangle>map_rel \<rightarrow> V"
  subgoal
    apply (intro frefI nres_relI)
    apply (clarsimp simp: map_rel_def)
    apply (drule (1) fun_relD)
    by (auto simp add: option_rel_inv_conv)
  subgoal
    apply (clarsimp simp: map_rel_def)
    apply (drule (1) fun_relD)
    by (auto simp: option_rel_inv_conv)
  done

lemma in_dom_alt: "k\<in>dom m \<longleftrightarrow> \<not>is_None (m k)" by (auto split: option.split)

sepref_decl_op map_contains_key: "\<lambda>k m. k\<in>dom m" :: "K \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> bool_rel"
  unfolding in_dom_alt
  apply (rule fref_ncI)
  apply parametricity
  unfolding map_rel_def
  apply (elim IntE)
  apply parametricity
  done
```
IICF_Map.thy, lines 61 and 75–142. `op_map_the_lookup` is the operation the port's
`amt`/array-map-total layer (§5) actually implements — note its precondition `m k \<noteq> None`,
matching `mop_map_the_lookup` used in `IICF_Array_Map_Total.thy`.

Patterns:
```isabelle
lemma pat_map_empty[pat_rules]: "\<lambda>\<^sub>2_. None \<equiv> op_map_empty" by simp

lemma pat_map_is_empty[pat_rules]: 
  "(=) $m$(\<lambda>\<^sub>2_. None) \<equiv> op_map_is_empty$m" 
  "(=) $(\<lambda>\<^sub>2_. None)$m \<equiv> op_map_is_empty$m" 
  "(=) $(dom$m)${} \<equiv> op_map_is_empty$m"
  "(=) ${}$(dom$m) \<equiv> op_map_is_empty$m"
  unfolding atomize_eq
  by (auto dest: sym)

lemma pat_map_update[pat_rules]: 
  "fun_upd$m$k$(Some$v) \<equiv> op_map_update$'k$'v$'m"
  by simp
lemma pat_map_lookup[pat_rules]: "m$k \<equiv> op_map_lookup$'k$'m"
  by simp

lemma op_map_delete_pat[pat_rules]: 
  "(|`) $ m $ (uminus $ (insert $ k $ {})) \<equiv> op_map_delete$'k$'m"
  "fun_upd$m$k$None \<equiv> op_map_delete$'k$'m"
  by (simp_all add: map_upd_eq_restrict)

lemma op_map_contains_key[pat_rules]: 
  "(\<in>) $ k $ (dom$m) \<equiv> op_map_contains_key$'k$'m"
  "Not$((=) $(m$k)$None) \<equiv> op_map_contains_key$'k$'m"
   by (auto intro!: eq_reflection)
```
IICF_Map.thy, lines 146–170.

`map_custom_empty` locale (same idiom, `i_map`-typed):
```isabelle
locale map_custom_empty = 
  fixes op_custom_empty :: "'k\<rightharpoonup>'v"
  assumes op_custom_empty_def: "op_custom_empty = op_map_empty"
begin
  sepref_register op_custom_empty :: "('kx,'vx) i_map"

  lemma fold_custom_empty:
    "Map.empty = op_custom_empty"
    "op_map_empty = op_custom_empty"
    "mop_map_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all
end
```
IICF_Map.thy, lines 175–186.

---

# 3. Implementation layer pattern (IICF_Array.thy)

## 3.1 The raw assertion

```isabelle
hide_const (open) LLVM_DS_Array.array_assn

abbreviation "raw_array_assn \<equiv> \<upharpoonleft>LLVM_DS_NArray.narray_assn"

definition array_assn where "array_assn A \<equiv> hr_comp raw_array_assn (\<langle>the_pure A\<rangle>list_rel)"
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "array_assn A" for A]

lemma array_assn_comp: "hr_comp (array_assn id_assn) (\<langle>the_pure A\<rangle>list_rel) = array_assn (A)"
  unfolding array_assn_def by simp
```
IICF_Array.thy, lines 73–81. Pattern: the raw assertion (`narray_assn`, defined in
`LLVM_DS_NArray.thy`, not fetched — see Gaps) is composed (`hr_comp`) with the interface's
parametricity relation (`\<langle>the_pure A\<rangle>list_rel`) to get the assertion that sepref actually sees
(`array_assn A`). `the_pure A` extracts the underlying relation from a pure element-assertion `A`.

## 3.2 A worked pre-refactor cost example (in the `experiment` block — shows the intended shape
before FCOMP composition, i.e. what a raw hnr rule looks like *with cost made explicit*):

```isabelle
lemma satminus_lift_acost: "satminus ta (the_acost (lift_acost t) b) = 0 \<longleftrightarrow> ta \<le> the_acost t b"
  unfolding satminus_def lift_acost_def by auto

lemma hnr_SPECT_D:
  fixes \<Phi> :: "_ \<Rightarrow> ((_,enat) acost) option"
  shows
      "do { ASSERT P; consume (RETURNT x) (lift_acost t) } = SPECT \<Phi>
      \<Longrightarrow> P \<and> Some (lift_acost t) \<le> \<Phi> x"
  ...

lemma "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  (array_nth xsi ii)
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  id_assn
  (do { ASSERT (i<length xs); consume (RETURNT (xs!i)) (lift_acost (cost ''load'' (Suc 0)+cost ''ofs_ptr'' (Suc 0))) })" 
  unfolding snat_rel_def snat.assn_is_rel[symmetric] 
  unfolding hn_ctxt_def pure_def
  apply(rule hnr_vcgI)
   apply(drule hnr_SPECT_D, clarify)
  apply(rule exI[where x="xs!i"])
  apply(rule exI[where x="cost ''load'' (Suc 0)+cost ''ofs_ptr'' (Suc 0)"])
  apply (vcg')  
  done
```
IICF_Array.thy, lines 95–139 (inside `experiment ... end`, i.e. NOT part of the checked-in
theory's real proof state — it is a scratch/regression derivation, but it is the ONLY place in
the whole fetched corpus where a concrete named-currency cost multiset for an array op is spelled
out: reading `xs!i` costs `cost ''load'' 1 + cost ''ofs_ptr'' 1` — one pointer-offset unit plus
one load unit). This is strong evidence for what the real (non-experimental) `array_nth` hnr rule
must cost once unfolded — but the real rule (`array_get_hnr_aux` below) does not show the cost
literally; it is hidden inside the abstract `\<rightarrow>\<^sub>a` notation whose expansion (in
`Sepref_Basic.thy`/`Sepref_Rules.thy`, not part of the 7 fetched files) carries the acost bookkeeping.

## 3.3 The real (non-experimental) hnr rules and their `sepref_decl_impl` compositions

```isabelle
context 
  notes [fcomp_norm_unfold] = array_assn_def[symmetric] array_assn_comp
begin  

  lemma array_get_hnr_aux: "(uncurry array_nth,uncurry (RETURNT oo op_list_get)) 
    \<in> [\<lambda>(l,i). i<length l]\<^sub>a raw_array_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> id_assn"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply vcg'
    done
    
  sepref_decl_impl array_get: array_get_hnr_aux .  

  lemma array_set_hnr_aux: "(uncurry2 array_upd,uncurry2 (RETURN ooo op_list_set)) 
    \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a raw_array_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> raw_array_assn"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done
    
  sepref_decl_impl array_set: array_set_hnr_aux .

  sepref_definition array_swap [llvm_code] is "uncurry2 (mop_list_swap)" 
    :: "(array_assn id_assn)\<^sup>d *\<^sub>a (snat_assn)\<^sup>k *\<^sub>a (snat_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn id_assn"
    unfolding gen_mop_list_swap by sepref
    
  sepref_decl_impl (ismop) array_swap.refine .
    
  lemma hn_array_repl_init_raw:
    shows "(narray_new TYPE('c::llvm_rep),RETURN o replicate_init_raw) \<in> snat_assn\<^sup>k \<rightarrow>\<^sub>a raw_array_assn"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply vcg'
    done

  sepref_decl_impl (no_mop) hn_array_repl_init_raw uses array.replicate_init_param . 
  
  lemma hn_array_grow_init_raw:
    shows "(uncurry2 array_grow, uncurry2 (RETURN ooo grow_init_raw)) 
      \<in> [\<lambda>((ns,os),xs). os\<le>length xs \<and> os\<le>ns]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a raw_array_assn\<^sup>d \<rightarrow> raw_array_assn"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    by vcg'
    
  sepref_decl_impl (no_mop) hn_array_grow_init_raw uses grow_init_param .
  
  sepref_decl_op array_custom_replicate: op_list_replicate :: "nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .
  
  lemma hn_array_replicate_new_raw:
    "(uncurry narray_new_init, uncurry (RETURN oo op_array_custom_replicate)) \<in> snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a raw_array_assn"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    by vcg
    
  sepref_decl_impl hn_array_replicate_new_raw .
  
  lemma array_fold_custom_replicate: 
    "replicate = op_array_custom_replicate"
    "op_list_replicate = op_array_custom_replicate"
    "mop_list_replicate = mop_array_custom_replicate"
    by (auto del: ext intro!: ext)
  
  lemma hn_array_free_raw: "(narray_free,RETURN o op_list_free) \<in> raw_array_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
    by sepref_to_hoare vcg
  
  sepref_decl_impl array_free: hn_array_free_raw .
  lemmas array_mk_free[sepref_frame_free_rules] = hn_MK_FREEI[OF array_free_hnr]
  
end  
```
IICF_Array.thy, lines 157–228.

**FCOMP idiom, restated precisely from the source:** an Impl rule is never proved directly
against `array_assn A`; it is proved once against the raw assertion (`raw_array_assn`, no
`hr_comp`) for the *identity* element case (`id_assn`), inside a `context notes
[fcomp_norm_unfold] = array_assn_def[symmetric] array_assn_comp`. The `sepref_decl_impl` command
then performs the `FCOMP` internally: raw-hnr-rule `FCOMP` interface-op's own parametricity fact
(e.g. `op_list_get`'s parametricity, declared back in `IICF_List.thy` as part of
`sepref_decl_op list_get`), normalizing the resulting composed assertion back through
`array_assn_comp` (`hr_comp (array_assn id_assn) (\<langle>the_pure A\<rangle>list_rel) = array_assn A`) so the
final stored fact is stated at the general element-assertion `A`, not just `id_assn`. This is
the textbook instance of "Impl rule = raw hnr rule FCOMP interface param rule" the task asked to
document. The `(ismop)` flag on `sepref_decl_impl` is used when composing a `sepref_definition`'s
own `.refine` fact (itself already an `hn_refine`) rather than a bare hnr lemma — see
`array_swap.refine`. The `(no_mop)` flag is used for ops (`replicate_init`, `grow_init`) that have
no separate abstract `mop_*`, only a raw `RETURN`-wrapped operation, composed directly with the
op's own custom parametricity lemma via `uses <lemma>`.

## 3.4 MK_FREE / free rules

```isabelle
lemma hn_array_free_raw: "(narray_free,RETURN o op_list_free) \<in> raw_array_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  by sepref_to_hoare vcg

sepref_decl_impl array_free: hn_array_free_raw .
lemmas array_mk_free[sepref_frame_free_rules] = hn_MK_FREEI[OF array_free_hnr]
```
IICF_Array.thy, lines 223–227. Pattern: declare `op_list_free` as an `hnr` rule to the
deallocation primitive, then lift it into a `MK_FREE` fact (added to `sepref_frame_free_rules`,
consumed by frame inference when a `\<^sup>d` (destroyed) argument must be freed at scope end) via
the combinator `hn_MK_FREEI`.

## 3.5 The length-tracked variant `larray` (same file, second half)

`IICF_Array.thy` also derives a *length-tracked* array (`larray`, `'l word \<times> 'x ptr` pair) by
refining `array_assn` through a `br` (bijection-relation) `larray1_rel`, giving `get`/`set`/`length`
/`is_empty`/`swap`/`free` all as thin wrappers proved by `FCOMP`ing a `sepref_definition`'s
`.refine` against a plain-HOL-level refinement lemma (`la_get1_refine`, `la_set1_refine`, ...)
rather than against a raw hnr rule directly — a second, purely-functional composition style worth
noting for the port:
```isabelle
definition "larray1_rel = br snd (\<lambda>(n,xs). n = length xs)"
...
definition "la_get1 nxs i \<equiv> case nxs of (n,xs) \<Rightarrow> xs!i"
lemma la_get1_refine: "(la_get1,op_list_get) \<in> larray1_rel \<rightarrow> nat_rel \<rightarrow> Id"
  by (auto simp: larray1_rel_def in_br_conv la_get1_def)
  
sepref_definition la_get_impl [llvm_inline] is "uncurry (RETURN oo la_get1)" :: "[\<lambda>(la,i). i<length (snd la)]\<^sub>a (larray_impl_assn' TYPE('b::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('c::len2))\<^sup>k \<rightarrow> id_assn"
  unfolding la_get1_def la_length1_def
  apply sepref_dbg_keep
  done
  
sepref_decl_impl la_get_impl.refine[FCOMP la_get1_refine] .
```
IICF_Array.thy, lines 235, 320, 347–356 (excerpted; full ladder repeats for `la_set1`,
`la_length1`, `la_is_empty1`, `la_free1`, plus `la_replicate1`/`la_replicate_init1`/`la_grow_init1`
using `uses <param-lemma>` the way §3.3's `array` ops do). Not required for P6's minimal
array/array-list/array-map-total trio but recorded since it is the file's second architectural
idiom (compose against a plain functional-refinement lemma with explicit `FCOMP ... .` syntax,
rather than letting `sepref_decl_impl` do the FCOMP against a `sepref_decl_op`-generated fact).

---

# 4. IICF_Array_List.thy — dynamic array (stack-like)

## 4.1 Assertion

```isabelle
abbreviation (input) "raw_al_assn \<equiv> \<upharpoonleft>arl_assn"

definition "al_assn R \<equiv> hr_comp raw_al_assn (\<langle>the_pure R\<rangle>list_rel)"

abbreviation "al_assn' TYPE('l::len2) R \<equiv> al_assn R :: (_ \<Rightarrow> (_,'l)array_list \<Rightarrow> _)"
```
IICF_Array_List.thy, lines 5–9. Same `hr_comp raw *_assn list_rel` shape as `array_assn`;
`arl_assn` (the raw length+capacity-tracked assertion) is defined in `LLVM_DS_Array_List.thy`
(not fetched — see Gaps).

Free rules:
```isabelle
lemma arl_assn_free[sepref_frame_free_rules]: "MK_FREE (\<upharpoonleft>arl_assn) arl_free"
  apply rule by vcg

lemma al_assn_free[sepref_frame_free_rules]: "MK_FREE (al_assn R) arl_free"
  unfolding al_assn_def by (rule sepref_frame_free_rules)+
```
IICF_Array_List.thy, lines 11–15.

Bound-extraction lemmas (length must fit the index type `'l`):
```isabelle
lemma al_assn_boundD[sepref_bounds_dest]: 
  "rdomp (al_assn' TYPE('l::len2) A) xs \<Longrightarrow> length xs < max_snat LENGTH('l)"
  unfolding al_assn_def arl_assn_def arl_assn'_def
  apply (simp add: rdomp_hrcomp_conv sep_algebra_simps split: prod.splits)
  by (auto 
    simp: rdomp_def snat.assn_def sep_algebra_simps pred_lift_extract_simps
    list_rel_imp_same_length[symmetric]
    )
```
IICF_Array_List.thy, lines 17–24.

## 4.2 Extra abstract ops declared in this file

```isabelle
text \<open>This functions deletes all elements of a resizable array, without resizing it.\<close>
sepref_decl_op emptied_list: "\<lambda>_::'a list. []::'a list" :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .

sepref_decl_op al_custom_replicate: op_list_replicate :: "nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .
```
IICF_Array_List.thy, lines 37–40.

## 4.3 hnr rules — every operation, verbatim, with the `m_ref` proof-method shorthand

```isabelle
private method m_ref =     
    ((unfold snat_rel_def snat.assn_is_rel[symmetric] bool1_rel_def bool.assn_is_rel[symmetric])?,
     sepref_to_hoare, vcg_monadify,
     vcg')

     
lemma al_empty_hnr_aux: 
  "(uncurry0 (arl_new_raw::(_,'l::len2)array_list llM), uncurry0 (RETURN op_list_empty)) 
    \<in> [\<lambda>_. 4 < L]\<^sub>a unit_assn\<^sup>k \<rightarrow> AA"
  by m_ref  
sepref_decl_impl (no_register) al_empty: al_empty_hnr_aux .
     
lemma al_replicate_hnr_aux:
  "(uncurry arl_new_repl, uncurry (RETURN oo op_al_custom_replicate)) 
  \<in> [\<lambda>_. 4 < L]\<^sub>a (snat_assn' TYPE('l))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> AA"
  by m_ref
sepref_decl_impl al_replicate: al_replicate_hnr_aux .


lemma al_nth_hnr_aux: "(uncurry arl_nth, uncurry mop_list_get) 
  \<in> AA\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  by m_ref  
  
sepref_decl_impl (ismop) al_nth: al_nth_hnr_aux .
    
lemma al_upd_hnr_aux: "(uncurry2 arl_upd, uncurry2 mop_list_set) 
  \<in> AA\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a AA"
  by m_ref  
sepref_decl_impl (ismop) al_upd: al_upd_hnr_aux .

lemma al_append_hnr_aux: "(uncurry arl_push_back, uncurry mop_list_append)
  \<in> [\<lambda>(xs,_). length xs + 1 < max_snat L]\<^sub>a AA\<^sup>d *\<^sub>a id_assn\<^sup>k \<rightarrow> AA"
  by m_ref  
sepref_decl_impl (ismop) al_append: al_append_hnr_aux .

lemma al_take_hnr_aux: "(uncurry arl_take, uncurry mop_list_take)
  \<in> snat_assn\<^sup>k *\<^sub>a AA\<^sup>d \<rightarrow>\<^sub>a AA"
  by m_ref  
sepref_decl_impl (ismop) al_take: al_take_hnr_aux .

lemma al_pop_last_hnr_aux: "(arl_pop_back, mop_list_pop_last)
  \<in> AA\<^sup>d \<rightarrow>\<^sub>a id_assn \<times>\<^sub>a AA"
  by m_ref  
sepref_decl_impl (ismop) al_pop_last: al_pop_last_hnr_aux .

lemma al_butlast_hnr_aux: "(arl_butlast, mop_list_butlast) \<in> AA\<^sup>d \<rightarrow>\<^sub>a AA"
  by m_ref
sepref_decl_impl (ismop) al_butlast: al_butlast_hnr_aux .

lemma al_last_hnr_aux: "(arl_last, mop_list_last) \<in> AA\<^sup>k \<rightarrow>\<^sub>a id_assn"
  by m_ref
sepref_decl_impl (ismop) al_last: al_last_hnr_aux .
  
lemma al_len_hnr_aux: "(arl_len, mop_list_length) \<in> AA\<^sup>k \<rightarrow>\<^sub>a snat_assn"
  by m_ref  
sepref_decl_impl (ismop) al_len: al_len_hnr_aux .

lemma al_is_empty_hnr_aux: 
  "(\<lambda>al. doM { l\<leftarrow>arl_len al; ll_icmp_eq l (signed_nat 0) }, mop_list_is_empty) \<in> AA\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  by m_ref
sepref_decl_impl (ismop) al_is_empty: al_is_empty_hnr_aux .

lemma al_emptied_hnr_aux: "(arl_clear,mop_emptied_list)\<in>AA\<^sup>d\<rightarrow>\<^sub>aAA"
  by m_ref
sepref_decl_impl (ismop) al_emptied_hnr_aux .
```
IICF_Array_List.thy, lines 70–136 (`AA` abbreviates `raw_al_assn` at fixed length-type `'l`,
`L` abbreviates `LENGTH('l)`, both fixed in the enclosing `context`, lines 49–54).

**Amortization: NOT visible in the cost sense** — none of these hnr statements carry an explicit
`consume`/`cost` term (same situation as the Intf layer, §2.1); `\<rightarrow>\<^sub>a` again hides whatever cost
the underlying raw operations (`arl_push_back`, `arl_new_repl`, ... from `LLVM_DS_Array_List.thy`,
not fetched) are proved to have. There is textual evidence the array-list is doubling/amortized
— the precondition `length xs + 1 < max_snat L` on `al_append_hnr_aux` is a pure capacity/index-
overflow guard, not a cost bound, and gives no information about whether push is charged O(1)
amortized or a worst-case buffer-growth cost. **This is a Gap**: the port cannot read off
"push is amortized O(1)" from this file; it must be verified in `LLVM_DS_Array_List.thy` directly
(see §7).

Custom-empty wrapper (parallel to `list_custom_empty`, specialized to the length-type-indexed
`al_assn`):
```isabelle
definition [simp]: "op_al_empty TYPE('l::len2) \<equiv> op_list_empty"     
sepref_register "op_al_empty TYPE('l::len2)"
lemma al_custom_empty_hnr[sepref_fr_rules]: 
  "(uncurry0 arl_new_raw, uncurry0 (RETURN (PR_CONST (op_al_empty TYPE('l::len2))))) 
    \<in> [\<lambda>_. 4<LENGTH('l)]\<^sub>a unit_assn\<^sup>k \<rightarrow> al_assn' TYPE('l) A"
  apply simp
  apply (rule al_empty_hnr[simplified])
  done

lemma al_fold_custom_empty:
  "[] = op_al_empty TYPE('l::len2)"
  "op_list_empty = op_al_empty TYPE('l::len2)"
  "mop_list_empty = RETURN (op_al_empty TYPE('l::len2))"
  by auto
```
IICF_Array_List.thy, lines 143–156.

---

# 5. IICF_Array_Map_Total.thy — small total map over an array

Purpose statement, verbatim:
```isabelle
text \<open>
  Map implementation where lookup is only valid for elements 
  already in the map.
\<close>
```
IICF_Array_Map_Total.thy, lines 4–7.

## 5.1 Mid-level (functional) refinement: `amt1` = plain list standing for `nat \<rightharpoonup> 'a`

```isabelle
type_synonym 'a amt1 = "'a list"

definition amt1_rel :: "nat \<Rightarrow> ('a amt1 \<times> (nat\<rightharpoonup>'a)) set"
  where "amt1_rel N \<equiv> {(xs,m). length xs = N \<and> dom m \<subseteq> {0..<N} \<and> (\<forall>k v. m k = Some v \<longrightarrow> v=xs!k)}"

definition amt1_init :: "nat \<Rightarrow> 'a::llvm_rep amt1 nres" where "amt1_init N \<equiv> RETURN (replicate N init)"
definition amt1_lookup :: "nat \<Rightarrow> 'a amt1 \<Rightarrow> 'a nres" 
  where "amt1_lookup k m \<equiv> mop_list_get m k"
  
definition amt1_update :: "nat \<Rightarrow> 'a \<Rightarrow> 'a amt1 \<Rightarrow> 'a amt1 nres"
  where "amt1_update k v m \<equiv> mop_list_set m k v"
```
IICF_Array_Map_Total.thy, lines 9–19. Note: entries not in `dom m` are UNCONSTRAINED garbage in
the backing array (`amt1_rel`'s third conjunct only pins down values that ARE `Some`) — this is
exactly the "lookup only valid for elements already in the map" contract from the file's own doc
comment, and it is why `amt1_lookup`/`amt1_update` are implemented directly via
`mop_list_get`/`mop_list_set` (no membership check) — again inheriting the Intf layer's zero-cost
mop directly with no extra cost term at this level.

Interface op declared specifically for this implementation (a map with a fixed known key range
`{0..<N}`, keyed by `nat`):
```isabelle
sepref_decl_op amt_empty: "\<lambda>(N::nat). Map.empty :: nat \<rightharpoonup> _" :: "nat_rel \<rightarrow> \<langle>nat_rel,V\<rangle> map_rel" .

lemma amt_fold_custom_empty:
  "op_map_empty = op_amt_empty N"
  "Map.empty = op_amt_empty N"
  "mop_map_empty = mop_amt_empty N"
  by auto
```
IICF_Array_Map_Total.thy, lines 21–27.

Functional refinement lemmas (`amt1` vs. the abstract `mop_*`):
```isabelle
lemma amt1_empty_refine: "(amt1_init,mop_amt_empty) 
  \<in> nat_rel \<rightarrow>\<^sub>f\<^sub>d (\<lambda>N. \<langle>amt1_rel N\<rangle>nres_rel)"
  unfolding amt1_init_def
  by (auto intro!: frefI nres_relI simp: amt1_rel_def in_br_conv fun_eq_iff)

lemma amt1_lookup_refine: 
  "(amt1_lookup, mop_map_the_lookup) \<in> nbn_rel N \<rightarrow> amt1_rel N \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (clarsimp simp: amt1_lookup_def)
  apply (refine_vcg)
  apply (auto simp: amt1_rel_def in_br_conv)
  done
  
lemma amt1_update_refine:
  "(amt1_update, mop_map_update) 
    \<in> nbn_rel N \<rightarrow>Id \<rightarrow> amt1_rel N \<rightarrow> \<langle>amt1_rel N\<rangle>nres_rel"
  unfolding amt1_update_def 
  apply (refine_vcg frefI)
  by (auto simp: amt1_rel_def in_br_conv fun_eq_iff)
```
IICF_Array_Map_Total.thy, lines 30–47. (`nbn_rel N` = "nat below N" relation, bounding the key.)

## 5.2 LLVM-level assertion and hnr rules

```isabelle
context
  fixes L :: "'l::len2 itself"  
begin
  
  private abbreviation (input) "amt2_assn \<equiv> array_assn id_assn"

  definition "amt_assn V N \<equiv> hr_comp 
    (hr_comp amt2_assn (amt1_rel N))
    (\<langle>nat_rel, the_pure V\<rangle>map_rel)"
  lemmas [fcomp_norm_unfold] = amt_assn_def[symmetric]

  lemma amt_assn_fold'[fcomp_norm_unfold]: 
    "hrr_comp nat_rel (\<lambda>x _. hr_comp (IICF_Array.array_assn id_assn) (amt1_rel x))
                      (\<lambda>x. \<langle>nat_rel, the_pure V\<rangle>map_rel) = (\<lambda>N _. amt_assn V N)"
    unfolding amt_assn_def 
    by (auto simp: fun_eq_iff hrr_comp_def pred_lift_extract_simps; smt non_dep_def)
  

  lemma amt_assn_intf[intf_of_assn]: "intf_of_assn V TYPE('v) \<Longrightarrow> intf_of_assn (amt_assn V N) (TYPE((nat,'v)i_map))"
    by simp
      
  sepref_definition amt_init_impl [llvm_inline] is "amt1_init"
    :: "(snat_assn' TYPE('l))\<^sup>k \<rightarrow>\<^sub>a amt2_assn"
    unfolding amt1_init_def
    supply [sepref_import_param] = IdI[of init]
    apply (subst array_fold_custom_replicate)
    by sepref
    
   
  sepref_decl_impl (ismop) amt_empty: amt_init_impl.refine[FCOMP amt1_empty_refine] .
  
  sepref_definition amt_lookup_impl [llvm_inline] is "uncurry amt1_lookup" 
    :: "(snat_assn' TYPE('l))\<^sup>k *\<^sub>a amt2_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding amt1_lookup_def
    by sepref
  sepref_decl_impl (ismop) amt_lookup_impl.refine[FCOMP amt1_lookup_refine] 
    uses mop_map_the_lookup.fref[where K=Id] .
                                                          
  sepref_definition amt_update_impl [llvm_inline] is "uncurry2 amt1_update"  
    :: "(snat_assn' TYPE('l))\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a amt2_assn\<^sup>d \<rightarrow>\<^sub>a amt2_assn"
    unfolding amt1_update_def
    by sepref
  sepref_decl_impl (ismop) amt_update_impl.refine[FCOMP amt1_update_refine] 
    uses mop_map_update.fref[where K=Id] .

end    
```
IICF_Array_Map_Total.thy, lines 51–97.

**Two-stage `hr_comp`, the key pattern of this file**: `amt_assn` composes the raw
`array_assn id_assn` (§3.1) FIRST through the plain-HOL `amt1_rel N` (functional
list-represents-partial-map refinement, §5.1), THEN through the interface's `map_rel` (§2.4
IICF_Map.thy). This is a *double* FCOMP — `sepref_definition`s here are proved directly against
`amt2_assn = array_assn id_assn` and manipulate `amt1` (the `'a list` encoding), and the
`sepref_decl_impl (ismop) ... uses <fref-lemma>` step performs both compositions at once by
supplying the map-interface's own parametricity fact (`mop_map_the_lookup.fref`,
`mop_map_update.fref`) as the `uses` argument alongside the `amt1_*_refine` lemma folded into the
`.refine[FCOMP ...]` chain. This is the closest thing in the fetched corpus to a 3-layer
(LLVM-raw / functional-model / interface-abstract) composition and is the direct template for a
port's "small dense map keyed by array index" implementation.

`MK_FREE`, derived automatically by tactic (no manual `narray_free`-style call needed since
`amt_assn` reduces to `array_assn`, which already has its own `MK_FREE` from §3.4):
```isabelle
type_synonym ('v) amt = "'v ptr"

schematic_goal [sepref_frame_free_rules]: "MK_FREE (amt_assn N V) (?fr)"
  unfolding amt_assn_def
  by sepref_dbg_side
```
IICF_Array_Map_Total.thy, lines 99–103.

---

# 6. Mop catalogue

Every `mop_*` (and mop-like operation) declared or implemented across the seven fetched files,
one line each. **Currency column reports what is literally visible in these files** — per §2.1/§4.3
finding, that is "none (abstract, cost enters only via Impl hnr composition)" for essentially
every entry; the one exception is the experimental `array_nth` derivation in §3.2.

| mop (or hnr'd raw op) | file | currency multiset as literally stated in these 7 files |
|---|---|---|
| `mop_list_empty` | IICF_List.thy | none (abstract) |
| `mop_list_is_empty` | IICF_List.thy | none (abstract) |
| `mop_list_replicate` | IICF_List.thy | none (abstract) |
| `mop_list_copy` | IICF_List.thy | none (abstract) |
| `mop_list_prepend` | IICF_List.thy | none (abstract) |
| `mop_list_append` | IICF_List.thy (op); IICF_Array_List.thy (impl, `al_append_hnr_aux`) | none stated; impl precond `length xs+1 < max_snat L` only |
| `mop_list_concat` | IICF_List.thy | none (abstract) |
| `mop_list_take` | IICF_List.thy (op); IICF_Array_List.thy (impl, `al_take_hnr_aux`) | none (abstract) |
| `mop_list_drop` | IICF_List.thy | none (abstract) |
| `mop_list_length` | IICF_List.thy (op); IICF_Array_List.thy (impl, `al_len_hnr_aux`) | none (abstract) |
| `mop_list_get` | IICF_List.thy (op); IICF_Array.thy `array_get_hnr_aux`/`array_nth` (experimental cost, §3.2); IICF_Array_List.thy `al_nth_hnr_aux`; IICF_Array_Map_Total.thy `amt1_lookup` | none in real (non-experiment) rule text; **experimental** derivation gives `cost ''load'' 1 + cost ''ofs_ptr'' 1` for `array_nth` |
| `mop_list_set` | IICF_List.thy (op); IICF_Array.thy `array_set_hnr_aux`/`array_upd`; IICF_Array_List.thy `al_upd_hnr_aux`; IICF_Array_Map_Total.thy `amt1_update` | none stated |
| `mop_list_hd` | IICF_List.thy | none (abstract) |
| `mop_list_tl` | IICF_List.thy | none (abstract) |
| `mop_list_last` | IICF_List.thy (op); IICF_Array_List.thy (impl, `al_last_hnr_aux`) | none (abstract) |
| `mop_list_butlast` | IICF_List.thy (op); IICF_Array_List.thy (impl, `al_butlast_hnr_aux`) | none (abstract) |
| `mop_list_pop_last` | IICF_List.thy (op); IICF_Array_List.thy (impl, `al_pop_last_hnr_aux`) | none (abstract) |
| `mop_list_contains` | IICF_List.thy | none (abstract) |
| `mop_list_swap` | IICF_List.thy (op + `gen_mop_list_swap` unfolding to get/get/set/set); IICF_Array.thy `array_swap`; larray `larray_swap` | none stated (unfolds to 2×get + 2×set, each itself uncosted here) |
| `mop_list_rotate1` | IICF_List.thy | none (abstract) |
| `mop_list_rev` | IICF_List.thy | none (abstract) |
| `mop_list_index` | IICF_List.thy | none (abstract) |
| `mop_list_free` (`op_list_free`, not monadic — unit-returning) | IICF_Array.thy (impl, `hn_array_free_raw`/`narray_free`) | none stated |
| `mop_array_custom_replicate` | IICF_Array.thy | none (abstract) |
| `mop_larray_custom_replicate` | IICF_Array.thy | none (abstract) |
| `mop_al_custom_replicate` | IICF_Array_List.thy | none (abstract) |
| `mop_emptied_list` | IICF_Array_List.thy (op + impl `al_emptied_hnr_aux`/`arl_clear`) | none stated |
| `mop_set_empty` | IICF_Set.thy | none (abstract) |
| `mop_set_is_empty` | IICF_Set.thy | none (abstract) |
| `mop_set_member` | IICF_Set.thy | none (abstract) |
| `mop_set_insert` | IICF_Set.thy | none (abstract) |
| `mop_set_delete` | IICF_Set.thy | none (abstract) |
| `mop_set_union` | IICF_Set.thy | none (abstract) |
| `mop_set_inter` | IICF_Set.thy | none (abstract) |
| `mop_set_diff` | IICF_Set.thy | none (abstract) |
| `mop_set_subseteq` | IICF_Set.thy | none (abstract) |
| `mop_set_subset` | IICF_Set.thy | none (abstract) |
| `mop_set_pick` | IICF_Set.thy | none (abstract); spec is `RES` (nondeterministic) |
| `mop_map_empty` | IICF_Map.thy | none (abstract) |
| `mop_map_is_empty` | IICF_Map.thy | none (abstract) |
| `mop_map_update` | IICF_Map.thy (op); IICF_Array_Map_Total.thy `amt1_update`/`amt_update_impl` | none stated |
| `mop_map_delete` | IICF_Map.thy | none (abstract) |
| `mop_map_lookup` | IICF_Map.thy | none (abstract) |
| `mop_map_the_lookup` | IICF_Map.thy (op); IICF_Array_Map_Total.thy `amt1_lookup`/`amt_lookup_impl` | none stated |
| `mop_map_contains_key` | IICF_Map.thy | none (abstract) |
| `mop_amt_empty` | IICF_Array_Map_Total.thy | none stated |

---

# 7. Gaps

- **The central gap: no cost currencies are visible in the Intf layer at all**, and the Impl
  layer's `hnr` rules (`array_get_hnr_aux`, `al_nth_hnr_aux`, `amt1_lookup`'s `sepref_definition`,
  etc.) state their cost through the notation `\<rightarrow>\<^sub>a`/`\<rightarrow>` whose expansion is defined in
  `Sepref_Basic.thy` / `Sepref_Rules.thy` — NOT among the seven fetched files (though copies of
  both happen to already sit in the tmp dir from a different task; they were not fetched by this
  extraction and are out of scope for verbatim quotation here). The one place cost is spelled
  out literally is the `experiment`-block derivation of `array_nth`'s cost
  (`cost ''load'' 1 + cost ''ofs_ptr'' 1`, IICF_Array.thy lines 125–139) — but that block is
  explicitly an `experiment` (discarded at theory end), not the theory's real, load-bearing hnr
  rule. **The port cannot get named-currency costs for `mop_list_get`/`mop_list_set`/`mop_list_append`/
  etc. straight from these 7 files** — it must additionally consult `Sepref_Basic.thy`'s
  definition of `hn_refine`/`\<rightarrow>\<^sub>a\<close>` (to see how the acost is threaded through), and, for the
  concrete currencies of each primitive, the underlying raw-op theories:
  - `LLVM_DS_NArray.thy` (defines `narray_assn`, `array_nth`, `array_upd`, `narray_new`,
    `narray_new_init`, `array_grow`, `narray_free` — the true source of `array`'s costs)
  - `LLVM_DS_Array_List.thy` (defines `arl_assn`, `arl_nth`, `arl_upd`, `arl_push_back`,
    `arl_pop_back`, `arl_take`, `arl_butlast`, `arl_last`, `arl_len`, `arl_clear`, `arl_new_raw`,
    `arl_new_repl`, `arl_free` — the true source of the array-list's costs, and specifically
    whether `arl_push_back` is a genuine O(1)-amortized doubling array or something simpler)
  None of these were in the fetch list and none were fetched by this task.

- **Amortization claim for `mop_list_append`/`arl_push_back` is unresolved.** §4.3 notes the
  precondition `length xs + 1 < max_snat L` is purely an overflow guard, giving zero information
  about amortized vs. worst-case cost. This must be settled by reading `LLVM_DS_Array_List.thy`
  before the port commits to charging push a constant number of currency units per call (typical
  Isabelilla-LLVM-time array-lists in this codebase family DO use amortized doubling, but that
  fact is not present in any of the 7 fetched files and should not be assumed without the source).

- **`Sepref_Combinator_Setup.thy`** (not fetched; defines the `sepref_decl_op` command itself,
  hence the actual definitional shape of every generated `mop_*` — e.g. whether it is literally
  `do {ASSERT pre; consume (RETURN (op)) 0}` with a zero-cost `consume`, or has no `consume` at
  all) is referenced only implicitly (by every `sepref_decl_op` invocation in the four Intf/Impl
  files) but was not one of the seven files and was not read for verbatim quotation in this
  extract. Its content directly bears on item 2's "cost-carrying fork" framing and should be
  fetched in a follow-up if the port needs the literal generated-mop definition.

- **`Sepref_Id_Op.thy`** (not fetched) defines `sepref_register`/pattern/`def_pat_rules`
  machinery referenced throughout §2; not required for the port's Lean-side translation but
  relevant if the campaign later wants to mirror the pattern-matching monadification step itself.

- **`List-Index.List_Index` (AFP entry)**, imported by `IICF_List.thy` for `index`/`find_index`,
  is an external AFP theory, not part of `isabelle_llvm_time`; not fetched, low relevance to P6
  (only backs `op_list_index`, unlikely to be in P6's minimal scope).

- **`../ds/LLVM_DS_Array_List`, `../../../ds/LLVM_DS_Array_List`** and the various `ds/`-rooted
  imports (`LLVM_DS_NArray`, `LLVM_DS_Array_List`) are ML/definition-level LLVM data-structure
  theories in a sibling directory tree (`thys/ds/`) not touched by this fetch at all — every
  concrete cost number in this whole extract ultimately bottoms out there.

- **`Impl/IICF_Array_Map` and `Impl/IICF_Array_of_Array_List`** (imported by `IICF.thy` at lines
  18 and 29 but not among the seven requested files) sit structurally between `IICF_Array.thy`
  and `IICF_Array_Map_Total.thy` in the import graph; `IICF_Array_Map_Total.thy` imports
  `IICF_Array` directly and does not need `IICF_Array_Map`, so this is likely a genuine sibling
  (partial-map, not total-map, over an array) rather than a hidden dependency — but it was not
  fetched, so its cost/precondition shape relative to `amt` (§5) is unverified.

- **Where the AFP no-cost `isabelle_llvm` (non-`_time`) version would differ structurally**:
  in the no-cost AFP variant, `hn_refine`'s conclusion type has no `acost`/`consume`/`$cost`
  machinery at all — every `\<rightarrow>\<^sub>a` in §3/§4/§5 would be a plain Hoare triple with no cost
  bookkeeping, and the `experiment` block's `hnr_SPECT_D`/`satminus_lift_acost`/`lift_acost`
  lemmas (§3.2) would simply not exist (no acost-typed `SPECT`). Everything else — the
  `sepref_decl_op`/`sepref_decl_impl`/`FCOMP` architecture, the `Intf` vs. `Impl` split, the
  `intf_of_assn`/`is_pure` mechanism, the two-stage `hr_comp` pattern in `amt_assn` — is identical
  in shape between the cost and no-cost variants; the time-costed repo (this pin) simply threads
  an extra `acost` argument through the same skeleton. This matters for the port because it
  confirms the "cost-carrying fork" is a late, almost orthogonal addition to an otherwise
  unchanged refinement architecture — good news for reusing P0–P5's existing cost-indexed
  big-step/wp machinery (per `refinement-tower-campaign.md`) rather than re-deriving IICF's shape
  from scratch.
