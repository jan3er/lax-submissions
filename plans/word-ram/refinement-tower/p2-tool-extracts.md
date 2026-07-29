# P2 source extracts — Autoref `Tool/` pipeline (id-ops, fix-rel, translate, phase driver)

Companion to `p2-autoref-extracts.md` (relators/parametricity/tagging) and
`p2-tutorial-extracts.md` (the acceptance examples this pipeline must drive).
Fetched 2026-07-29, verbatim, from AFP `Automatic_Refinement`, Isabelle2025-2.
Mirror used: **`isabelle-prover/mirror-afp-devel`**, same choice and
justification as both companion files (established working mirror for this
campaign; devel is textually identical to the 2025-2 release for everything
quoted here). Files fetched via raw.githubusercontent.com at commit tip of
`master` on 2026-07-29; every byte count below was cross-checked against the
independent directory listing already recorded in `p2-tutorial-extracts.md`
§1 and matched exactly (no drift, same commit):

- `thys/Automatic_Refinement/Tool/Autoref_Data.thy` (1094 bytes)
- `thys/Automatic_Refinement/Tool/Autoref_Fix_Rel.thy` (31989 bytes)
- `thys/Automatic_Refinement/Tool/Autoref_Gen_Algo.thy` (2491 bytes)
- `thys/Automatic_Refinement/Tool/Autoref_Id_Ops.thy` (21654 bytes)
- `thys/Automatic_Refinement/Tool/Autoref_Phases.thy` (7059 bytes)
- `thys/Automatic_Refinement/Tool/Autoref_Relator_Interface.thy` (3774 bytes)
- `thys/Automatic_Refinement/Tool/Autoref_Tagging.thy` (6452 bytes)
- `thys/Automatic_Refinement/Tool/Autoref_Tool.thy` (6947 bytes)
- `thys/Automatic_Refinement/Tool/Autoref_Translate.thy` (10136 bytes)
- `thys/Automatic_Refinement/Autoref_Bindings_HOL.thy` (32611 bytes) —
  re-fetched only to locate `autoref_struct_expand`'s declaration (see §8);
  not re-extracted for tutorial content, that's `p2-tutorial-extracts.md`'s job.
- `thys/Automatic_Refinement/Parametricity/{Relators,Param_HOL,Param_Tool}.thy`
  — re-fetched and grepped only (for `autoref_struct_expand`, found absent —
  see §8), not re-extracted; full extraction of these three already lives in
  `p2-autoref-extracts.md`.
- `Autoref_Chapter.thy` (102 bytes, `Tool/`) — not fetched: a bare section-title
  stub per its size, confirmed by the listing, no declarations.

**Actual phase registration order** (from `Autoref_Tool.thy`, §7 below) is
`id_op` (priority 10) → `rel_inf` (20) → `fix_rel` (22) → `trans` (30) — one
phase more than the task's suggested "id_ops → fix_rel → translate" framing;
`rel_inf` (relator inference from interfaces) sits between `id_op` and
`fix_rel` and is declared inside `Autoref_Id_Ops.thy` itself. Sections below
follow this actual order.

## 1. `Autoref_Id_Ops.thy` — operation identification (`id_op`, prio 10) and relator inference (`rel_inf`, prio 20)

### 1.1 Interface-application syntax (beyond `p2-autoref-extracts.md` §3)

The companion file already quotes `typedecl interface`, `intfAPP`,
`consts i_fun`/`i_fun_app`, `CONST_INTF`, and `ID_OP` from this theory. Not
quoted there — the concrete-syntax translations that make `⟨i1,i2⟩ᵢi_fun`
write as `i1→ᵢi2` and give interface application its own binder form:

```isabelle
syntax "_intf_APP" :: "args ⇒ 'a ⇒ 'b" ("⟨_⟩⇩i_" [0,900] 900)

syntax_consts "_intf_APP" == intfAPP

translations
  "⟨x,xs⟩⇩iR" == "⟨xs⟩⇩i(CONST intfAPP R x)"
  "⟨x⟩⇩iR" == "CONST intfAPP R x"

consts 
  i_annot :: "interface ⇒ annot"

abbreviation i_ANNOT :: "'a ⇒ interface ⇒ 'a" (infixr ":::⇩i" 10) where
  "t:::⇩iI ≡ ANNOT t (i_annot I)"
```

### 1.2 Interface-inference rules (`ID_OP` calculus)

The full rule set the `id_op` phase resolves against — the companion quoted
only the `CONST_INTF`/`ID_OP` *definitions*; these are the derivation rules
built on top of them:

```isabelle
lemma ID_abs: \<comment> ‹Tag abs first›
  "⟦ ⋀x. ID_OP x x I1 ⟹ ID_OP (f x) (f' x) I2 ⟧ 
  ⟹ ID_OP (λ'x. f x) (λ'x. f' x) (I1→⇩iI2)"
  by simp

lemma ID_app: \<comment> ‹Tag app first›
  "⟦ INDEP I1; ID_OP x x' I1; ID_OP f f' (I1→⇩iI2) ⟧ 
  ⟹ ID_OP (f$x) (f'$x') I2" by simp

lemma ID_const: \<comment> ‹Only if c is constant or free variable›
  "⟦ c ::⇩i I ⟧ ⟹ ID_OP c (OP c :::⇩i I) I"
  by simp

definition [simp]: "ID_TAG x ≡ x"
lemma ID_const_any: \<comment> ‹Only if no typing for constant exists›
  "ID_OP c (OP (ID_TAG c) :::⇩i I) I" 
  by simp

lemma ID_const_check_known: 
  "⟦ c ::⇩i I' ⟧ ⟹ ID_OP c c I" by simp

lemma ID_tagged_OP: \<comment> ‹Try first›
  "ID_OP (OP f :::⇩i I) (OP f :::⇩i I) I"
  by simp

lemma ID_is_tagged_OP: "ID_OP (OP c) t' I ⟹ ID_OP (OP c) t' I" .

lemma ID_tagged_OP_no_annot:
  "c ::⇩i I ⟹ ID_OP (OP c) (OP c :::⇩i I) I" by simp

lemmas ID_tagged = ID_tagged_OP ID_abs ID_app

lemma ID_annotated: \<comment> ‹Try second›
  "ID_OP t t' I ⟹ ID_OP (t :::⇩i I) t' I"
  "ID_OP t t' I ⟹ ID_OP (ANNOT t A) (ANNOT t' A) I"
  by simp_all

lemma ID_init:
  assumes "ID_OP a a' I"
  assumes "(c,a')∈R"
  shows "(c,a)∈R"
  using assms by auto

lemma itypeI: "(c::'t) ::⇩i I" by simp
```

`itypeI` is exactly the lemma the tutorial's `notes [autoref_itype] =
itypeI[where 't="'a::numeral" and I=i_std]` instantiates (§4 below covers
where `i_std` itself does — and doesn't — resolve).

### 1.3 The three `Named_Thms` databases this theory declares

```isabelle
structure intf_types = Named_Thms (
  val name = @{binding autoref_itype}
  val description = "Interface type declaration"
)

structure op_patterns = Named_Thms (
  val name = @{binding autoref_op_pat}
  val description = "Operation patterns"
)

structure op_patterns_def = Named_Thms (
  val name = @{binding autoref_op_pat_def}
  val description = "Definitive operation patterns"
)
```

`autoref_op_pat` is confirmed declared here, exactly where the task
anticipated. `autoref_op_pat_def` ("definitive" patterns) is a second,
separate net for patterns that must fire before anything else is tried
(`def_id_pat` below) — the tutorial extract's `Simple_DFS.thy` example
(`E``{v} ≡ op_succ$E$v`, quoted in `p2-tutorial-extracts.md` §2.1) is an
`autoref_op_pat` entry, not `_def`.

### 1.4 `id_tac` — structural description (ML body elided per task instruction)

`id_tac ctxt` builds one big recursive-descent tactic (`rec_tac`) over the
`ID_OP`-tagged goal. At each node it tries, in order: (1) `assume_tac` (goal
already discharged, e.g. by a caller-supplied `ID_OP` fact); (2) `ID_tagged`
(the term is already `OP _ :::ᵢ _`-tagged — nothing to do); (3) a two-branch
split on whether the head is a *known* constant (`ID_const`/`id_typ`, which
resolves against the `autoref_itype` net built by `get_typ_net`) versus an
*unknown* one, in which case — depending on `cfg_use_id_tags` — it either
fails or falls through to (4) `Indep_Vars.indep_tac`, `ID_annotated`, the
`autoref_op_pat_def` net (`def_id_pat`, tried first and must fully commit),
the `autoref_op_pat` net (`id_pat`), and finally generic
application/constant/abstraction identification (`id_dflt = FIRST'
[id_app,id_const,id_abs]`), each recursing via `ID_app`/`ID_abs` into
sub-`CONSTRAINT`s. This is precisely the mechanism that rewrites `a = None`
to `is_None$a` and `[] = a` to `is_Nil$a` before the relator-level rules in
`p2-tutorial-extracts.md` §3 ever fire — via an `autoref_op_pat` rule not
shown in the extracted tutorial text (see Gaps). The phase itself is thin
wiring around `id_tac`:

```isabelle
val id_phase = {
  init = I,
  tac = (fn ctxt => Seq.INTERVAL (resolve_tac ctxt @{thms ID_init} THEN' id_tac ctxt)),
  analyze = id_analyze,
  pretty_failure = id_pretty_failure
}
```

(`id_analyze`/`id_pretty_failure` just check whether the interval collapsed
to `i = j`, i.e. exactly one leftover `(c,a)∈R` goal and no stray `ID_OP`
subgoals — "no failure" vs. "Interface typing error", full pretty-printing
only under a trace flag.)

### 1.5 `Autoref_Rel_Inf` — the `rel_inf` phase (also declared in this file)

This structure lives in the back half of `Autoref_Id_Ops.thy`, after `setup
Autoref_Id_Ops.setup` — the task's item 6 asked for "the parts beyond §3",
and this is the largest chunk of it: it's the phase that turns the interface
skeleton fixed by `id_op` into an actual schematic relator skeleton for `?R`.

```isabelle
definition IND_FACT :: "rel_name ⇒ ('c × 'a) set ⇒ bool" ("#_=_" 10)
  where [simp]: "#name=R ≡ True"

lemma REL_INDIRECT: "#name=R" by simp

definition CNV_ANNOT :: "'a ⇒ 'a ⇒ (_×'a) set ⇒ bool"
  where [simp]: "CNV_ANNOT t t' R ≡ t=t'"

definition REL_OF_INTF :: "interface ⇒ ('c×'a) set ⇒ bool" 
  where [simp]: "REL_OF_INTF I R ≡ True"

definition 
  [simp]: "REL_OF_INTF_P I R ≡ True" \<comment> ‹Version to resolve relator arguments›

lemma CNV_ANNOT:
  "⋀f f' a a'. ⟦ CNV_ANNOT a a' Ra; CNV_ANNOT f f' (Ra→Rr) ⟧ 
    ⟹ CNV_ANNOT (f$a) (f'$a') (Rr)"
  "⋀f f'. ⟦ ⋀x. CNV_ANNOT x x Ra ⟹ CNV_ANNOT (f x) (f' x) Rr ⟧ 
    ⟹ CNV_ANNOT (λ'x. f x) (λ'x. f' x) (Ra→Rr)"
  "⋀f f I R. ⟦undefined (''Id tag not yet supported'',f)⟧ 
    ⟹ CNV_ANNOT (OP (ID_TAG f) :::⇩i I) f R"
  "⋀f I R. ⟦ INDEP R; REL_OF_INTF I R ⟧ 
    ⟹ CNV_ANNOT (OP f :::⇩i I) (OP f ::: R) R"
  "⋀t t' R. CNV_ANNOT t t' R ⟹ CNV_ANNOT (t ::: R) t' R"
  "⋀t t' name R. ⟦ #name=R; CNV_ANNOT t t' R ⟧ ⟹ CNV_ANNOT (t ::#name) t' R"
  by simp_all

consts i_of_rel :: "'a ⇒ 'b"

lemma ROI_P_app: \<comment> ‹Only if interface is really application›
  "REL_OF_INTF_P I R ⟹ REL_OF_INTF I R"
  by auto

lemma ROI_app: \<comment> ‹Only if interface is really application›
  "⟦ REL_OF_INTF I R; REL_OF_INTF_P J S ⟧ ⟹ REL_OF_INTF_P (⟨I⟩⇩iJ) (⟨R⟩S)"
  by auto

lemma ROI_i_of_rel:
  "REL_OF_INTF_P (i_of_rel S) S"
  "REL_OF_INTF (i_of_rel R) R"
  by auto

lemma ROI_const:
  "REL_OF_INTF_P J S"
  "REL_OF_INTF I R"
  by auto

lemma ROI_init:
  assumes "CNV_ANNOT a a' R"
  assumes "(c,a')∈R"
  shows "(c,a)∈R"
  using assms by simp

lemma REL_OF_INTF_I: "REL_OF_INTF I R" by simp
```

DB it declares:

```isabelle
structure rel_indirect = Named_Thms (
  val name = @{binding autoref_rel_indirect}
  val description = "Indirect relator bindings"
)
```

Structural description of `roi_step_tac`/`roi_tac` (ML body elided): at each
`CNV_ANNOT`/`REL_OF_INTF` goal it tries `assume_tac`, `Indep_Vars.indep_tac`,
the `autoref_rel_indirect` net (named relators registered via `#name=R`
facts — the indirect-annotation route, `t ::# s`, from `Autoref_Tagging.thy`
in the companion file), then falls through to `CNV_ANNOT`'s own recursion
rule or — for a bare `REL_OF_INTF I R` goal with no matching indirect
binding — synthesizes a fresh relator term structurally from the interface
`I` (`rel_of_intf_thm`: `i_fun`-application mirrors `relAPP`, unknown
constants/frees get a fresh `R_<name>` schematic, `i_of_rel R` unwraps back
to the literal `R`). Phase wiring:

```isabelle
val roi_phase = {
  init = I,
  tac = (fn ctxt => Seq.INTERVAL (resolve_tac ctxt @{thms ROI_init} THEN' roi_tac ctxt)),
  analyze = roi_analyze,
  pretty_failure = roi_pretty_failure
}
```

## 2. `Autoref_Fix_Rel.thy` — relator fixing (`fix_rel`, prio 22)

### 2.1 Priority tags

```isabelle
subsubsection ‹Priority tags›
text ‹
  Priority tags are used to influence the ordering of refinement theorems.
  A priority tag defines two numeric priorities, a major and a minor priority.
  The major priority is considered first, the minor priority last, i.e., after
  the homogenity and relator-priority criteria.
  The default value for both priorities is 0.
›
definition PRIO_TAG :: "int ⇒ int ⇒ bool" 
  where [simp]: "PRIO_TAG ma mi ≡ True"
lemma PRIO_TAGI: "PRIO_TAG ma mi" by simp

abbreviation "MAJOR_PRIO_TAG i ≡ PRIO_TAG i 0"
abbreviation "MINOR_PRIO_TAG i ≡ PRIO_TAG 0 i"
abbreviation "DFLT_PRIO_TAG ≡ PRIO_TAG 0 0"

text ‹Some standard tags›
abbreviation "PRIO_TAG_OPTIMIZATION ≡ MINOR_PRIO_TAG 10"
  \<comment> ‹Optimized version of an algorithm, with additional side-conditions›
abbreviation "PRIO_TAG_GEN_ALGO ≡ MINOR_PRIO_TAG (- 10)"
  \<comment> ‹Generic algorithm, considered to be less efficient than default algorithm›
```

This confirms `PRIO_TAG_GEN_ALGO` (the tag the tutorial's generic
order/equality lemmas assume, `p2-tutorial-extracts.md` §3) is *minor*
priority −10 — lower priority than any type-specific rule with default
(0,0) priority, exactly matching that section's "fallback... overridden by
the nat-specific rules" note.

### 2.2 `CONSTRAINT` and the `autoref_rules_raw` database

```isabelle
subsection ‹Solving Relator Constraints›
text ‹
  In this phase, we try to instantiate the annotated relators, using
  the available refinement rules.
›

definition CONSTRAINT :: "'a ⇒ ('c×'a) set ⇒ bool" 
  where [simp]: "CONSTRAINT f R ≡ True"

lemma CONSTRAINTI: "CONSTRAINT f R" by auto

ML ‹
  structure Autoref_Rules = Named_Thms ( 
    val name = @{binding autoref_rules_raw}
    val description = "Refinement Framework: " ^
        "Automatic refinement rules" 
  );
›
setup Autoref_Rules.setup
```

`autoref_rules_raw` is the *only* rule database `Autoref_Fix_Rel.thy`
itself declares — `autoref_rules` (no `_raw`) is a derived attribute
declared one file up the import chain, in `Autoref_Relator_Interface.thy`
(§3 below), not here, despite the task's framing suggesting both live in
this theory (see Gaps).

### 2.3 `PREFER`/`DEFER` tags, `GEN_OP`

```isabelle
text ‹Generic algorithm tags have to be defined here, as we need them for
  relator fixing !›

definition PREFER_tag :: "bool ⇒ bool" 
  where [simp, autoref_tag_defs]: "PREFER_tag x ≡ x"
definition DEFER_tag :: "bool ⇒ bool" 
  where [simp, autoref_tag_defs]: "DEFER_tag x ≡ x"

lemma PREFER_tagI: "P ⟹ PREFER_tag P" by simp
lemma DEFER_tagI: "P ⟹ DEFER_tag P" by simp
lemmas SIDEI = PREFER_tagI DEFER_tagI

definition [simp, autoref_tag_defs]: "GEN_OP_tag P ≡ P"
lemma GEN_OP_tagI: "P ⟹ GEN_OP_tag P" by simp
abbreviation "SIDE_GEN_OP P ≡ PREFER_tag (GEN_OP_tag P)"
text ‹Shortcut for assuming an operation in a generic algorithm lemma›
abbreviation "GEN_OP c a R ≡ SIDE_GEN_OP ((c,OP a ::: R) ∈ R)"
```

Only the raw `_tag` predicates live here. The user-facing `PREFER`/`DEFER`
*abbreviations* (that also strip internal annotations via `REMOVE_INTERNAL`)
and `SIDE_PRECOND` are declared in `Autoref_Translate.thy`, not this theory
— a second location correction relative to the task's item 1 framing (see
Gaps). `GEN_OP c a R` is exactly the shape the tutorial's `autoref_list_eq`
premise (`GEN_OP eq (=) (R→R→Id)`) instantiates.

### 2.4 `TYREL` — type-based relator defaulting

```isabelle
definition TYREL :: "('a×'b) set ⇒ bool" 
  where [simp]: "TYREL R ≡ True"
definition TYREL_DOMAIN :: "'a itself ⇒ bool" 
  where [simp]: "TYREL_DOMAIN i ≡ True"

lemma TYREL_RES: "⟦ TYREL_DOMAIN TYPE('a); TYREL (R::(_×'a) set) ⟧ ⟹ TYREL R"
  .

lemma DOMAIN_OF_TYREL: "TYREL (R::(_×'a) set) 
  ⟹ TYREL_DOMAIN TYPE('a)" by simp

lemma TYRELI: "TYREL (R::(_×'a) set)" by simp

lemma ty_REL: "TYREL (R::(_×'a) set)" by simp
```

`ty_REL` is the lemma the tutorial's `notes [autoref_tyrel] = ty_REL[where
'a="'a set" and R="⟨Id⟩dflt_ahs_rel"]` (§2.5 of `p2-tutorial-extracts.md`,
out-of-scope Collections instance) instantiates — the mechanism itself
(let the user pin a default relator per abstract *type*, via
`TYREL_DOMAIN`) is in-scope P2 spine machinery even though that particular
example isn't.

### 2.5 The two remaining databases: `autoref_hom`, `autoref_tyrel`

```isabelle
structure hom_rules = Named_Sorted_Thms (
  val name = @{binding autoref_hom}
  val description = "Autoref: Homogenity rules"
  val sort = K I
  val transform = K (
    fn thm => case Thm.concl_of thm of 
      @{mpat "Trueprop (CONSTRAINT _ _)"} => [thm]
    | _ => raise THM ("Invalid homogenity rule",~1,[thm])
  )
)
```

```isabelle
structure tyrel_rules = Named_Sorted_Thms (
  val name = @{binding autoref_tyrel}
  val description = "Autoref: Type-based relator fixing rules"
  val sort = K I

  val transform = K (
    fn thm => case Thm.prop_of thm of 
      @{mpat "Trueprop (TYREL _)"} => [thm]
    | _ => raise THM ("Invalid tyrel-rule",~1,[thm])
  )
)
```

### 2.6 The `fix_rel` phase — structural description (job: assign relators to operators)

`Autoref_Fix_Rel.thy` maintains one piece of derived, cached state per
context: `thm_pairsD` — every `autoref_rules_raw` theorem paired with its
*constraint* `(gen_ops, (f, R))` (extracted by `constraint_of_thm`: the
operator's head `f` and the relator `R` it refines under, plus any `GEN_OP`
side-premises), sorted by `(major_prio, hom_count, rel_prio, minor_prio)`
so more specific/higher-priority rules are tried first. The phase's job —
"assigning relators to operators" — is `guess_relators_tac`, run in five
steps per goal interval: (1) `insert_CONSTRAINTS_tac` walks the tagged term
(`constraints_of_term`, recursing through `APP`/`ABS`/`OP ... :::`) and
inserts one `CONSTRAINT f R` subgoal per `OP f ::: R` annotation found; (2)
homogeneity rewriting against the `autoref_hom` net (forces relators like
`R→R` into matching shape before anything else fires); (3) anti-unification
*specialization* (`Anti_Unification.specialize_net_tac`) against a net built
from every `thm_pairsD` constraint — this is the actual "look up the rule
whose LHS operator matches" step; (4) `tyrel_tac` — for every relator
variable still appearing free, insert a `TYREL` subgoal and discharge it via
a user's `autoref_tyrel` rule or the `TYRELI` fallback; (5) full solving —
`SOLVED' (REPEAT_ALL_NEW (resolve against the same constraint-rule net))`,
tried strictly first, falling back to `TRY`-wrapped best-effort if that
fails outright. Failure diagnostics (`analyze`/`pretty_failure`) walk the
leftover `CONSTRAINT` goals, flag "possible problems" (arity mismatches
between a `Type` and its matched relator, `Var`s carrying a `TFree`d
concrete component — signs of a schematic relator wrongly fixed), and offer
to retry each candidate rule from `thm_pairsD` individually under tracing.

## 3. `Autoref_Relator_Interface.thy` — where `autoref_rules` (the non-`_raw` attribute) actually lives

Not named in the task's item 4 list, but this is where the derived,
user-facing `[autoref_rules]` attribute is declared — one file layer above
`Autoref_Fix_Rel.thy`/`Autoref_Id_Ops.thy`, since registering a rule also
needs `Autoref_Relator_Interface.intf_of_rel` (turn a relator into an
interface) and `Autoref_Id_Ops.decl_derived_typing` (both defined in this
theory / consumed from it):

```isabelle
definition [simp]: "REL_INTF R I ≡ True"
lemma REL_INTFI: "REL_INTF R I" by simp
```

```isabelle
structure relator_intf = Named_Thms (
  val name = @{binding autoref_rel_intf}
  val description = "Relator interface declaration"
)
```

`autoref_rel_intf` is the database `lemmas [autoref_rel_intf] =
REL_INTFI[of "succg_rel" i_graph]` (Simple_DFS.thy, `p2-tutorial-extracts.md`
§2.1) populates — "declare this custom relator as the relator for this
conceptual interface type."

The attribute declaration itself (binder line quoted per task instruction,
ML body elided — see structural description immediately after):

```isabelle
attribute_setup autoref_rules = ‹
  Scan.lift (Args.mode "overloaded")
  >> (fn overl => Thm.declaration_attribute (fn thm => fn context => ...))
›
```

Structurally: the attribute first adds the raw theorem to `Autoref_Rules`
(`autoref_rules_raw`, §2.2) exactly as `[autoref_rules_raw]` would; it then
calls `Autoref_Relator_Interface.itype_of_rule` (which reuses
`Autoref_Fix_Rel.constraint_of_thm` to read off `(f,R)` and converts `R` to
an interface via `intf_of_rel`) and, on success, registers that pairing as a
derived `autoref_itype` fact for the operator via
`Autoref_Id_Ops.decl_derived_typing overl`. So a single `[autoref_rules]`
declaration populates *both* the `id_op` phase's typing net and the
`fix_rel` phase's rule net in one step; if no relator can be inferred it
only warns and keeps the raw-rules registration (this is exactly the
"Strange autoref rule" warning path). The `(overloaded)` mode flag
suppresses the warning `decl_derived_typing` would otherwise raise when a
second interface type is derived for an already-typed constant — precisely
what the tutorial's `autoref_rules_raw` vs. `autoref_rules (overloaded)`
contrast (`p2-tutorial-extracts.md` §3/§4, `list_eq`/`hd` examples) hinges
on.

## 4. `Autoref_Translate.thy` — the translate phase (`trans`, prio 30)

### 4.1 `APP`/`ABS` rules and default translation rules

```isabelle
lemma autoref_ABS: 
  "⟦ ⋀x x'. (x,x')∈Ra ⟹ (c x, a x')∈Rr ⟧ ⟹ (c, λ'x. a x)∈Ra→Rr"
  by auto
lemma autoref_APP:
  "⟦ (c,a)∈Ra→Rr; (x,x')∈Ra ⟧ ⟹ (c$x, a $ x')∈Rr"
  by (auto dest: fun_relD)

lemma autoref_beta: 
  assumes "(c,a x)∈R"
  shows "(c,(λ'x. a x)$x)∈R"
  using assms by auto

lemmas dflt_trans_rules = autoref_beta autoref_ABS autoref_APP
```

### 4.2 Side conditions: `PREFER`/`DEFER`, `REMOVE_INTERNAL`, `SIDE_PRECOND`

```isabelle
subsubsection ‹Side Conditions›
text ‹
  Rules can have prefer and defer side-conditions. Prefer conditions must
  be solvable in order for the rule to apply, and defer conditions must
  hold after the rule has been applied and the recursive translations have been
  performed. Thus, prefer-conditions typically restrict on the abstract 
  expression, while defer conditions restrict the translated expression.

  In order to solve the actual side conditions, we use the 
  ‹Tagged_Solver›-infrastructure. The solvers are applied after 
  the ‹PREFER›/‹DEFER› tag has been removed.
›

text ‹
  Tag to remove internal stuff from term.
  Before a prefer/defer side condition is evaluated, all terms inside these 
  tags are purged from autoref-specific annotations, i.e., operator-annotations,
  relator annotations, and tagged applications.
›
definition [simp, autoref_tag_defs]: "REMOVE_INTERNAL x ≡ x" 

text ‹Useful abbreviation to require some property that is not related
  to teh refinement framework›
abbreviation "PREFER nt Φ ≡ PREFER_tag (nt (REMOVE_INTERNAL Φ))"
abbreviation "DEFER nt Φ ≡ DEFER_tag (nt (REMOVE_INTERNAL Φ))"

definition [simp]: "REMOVE_INTERNAL_EQ a b ≡ a=b"
lemma REMOVE_INTERNAL_EQI: "REMOVE_INTERNAL_EQ a a" by simp

lemma autoref_REMOVE_INTERNAL_EQ: 
  assumes "(c,a)∈R"
  assumes "REMOVE_INTERNAL_EQ c c'"
  shows "(c',a)∈R"
  using assms by simp
```

("teh" is a source typo, kept verbatim.) This is where `PREFER`/`DEFER`
*as used by rule authors* (not the raw `_tag` predicates from §2.3) actually
live, together with:

```isabelle
subsubsection ‹Standard side-tactics›

text ‹Preconditions›
definition [simp, autoref_tag_defs]: "PRECOND_tag P ≡ P"
lemma PRECOND_tagI: "P ⟹ PRECOND_tag P" by simp
abbreviation "SIDE_PRECOND P ≡ PREFER PRECOND_tag P"

declaration ‹
  Tagged_Solver.declare_solver @{thms PRECOND_tagI} @{binding PRECOND} 
    "Refinement: Solve preconditions" 
    ( fn ctxt => SOLVED' (
        SELECT_GOAL (auto_tac ctxt)
      )
    )
›

text ‹Optional preconditions›
definition [simp, autoref_tag_defs]: "PRECOND_OPT_tag P ≡ P"
lemma PRECOND_OPT_tagI: "P ⟹ PRECOND_OPT_tag P" by simp
abbreviation "SIDE_PRECOND_OPT P ≡ PREFER PRECOND_OPT_tag P"
declaration ‹
  Tagged_Solver.declare_solver @{thms PRECOND_OPT_tagI} @{binding PRECOND_OPT} 
    "Refinement: Solve optional preconditions" 
    ( fn ctxt => SOLVED' (asm_full_simp_tac ctxt))
›
```

`SIDE_PRECOND` — named in the task's item 1 as if it lived in
`Autoref_Fix_Rel.thy` — is declared here instead, and its solver is a plain
`auto_tac`; `SIDE_PRECOND_OPT`'s is `asm_full_simp_tac`. Both register with
the generic `Tagged_Solver` framework (`Lib/Tagged_Solver.thy`, not
extracted — see Gaps), the same registration idiom `Autoref_Gen_Algo.thy`
(§5) and `Autoref_Bindings_HOL.thy`'s `STRUCT_EQ` (§8) reuse.

### 4.3 `autoref_post_simps` and the `trans` phase — structural description

```isabelle
structure autoref_post_simps = Named_Thms ( 
  val name = @{binding autoref_post_simps}
  val description = "Refinement Framework: " ^
      "Automatic refinement post simplification rules" 
);
```

The phase's rule net (`trans_netD`) is `thm_pairsD` (now with every relator
fixed by `fix_rel`) plus the fixed `dflt_trans_rules`. `trans_step_tac`
handles one goal: if it's a `DEFER_tag` conclusion, solve it now via
`side_tac` (`SIDEI` intro, strip internal tags via `REMOVE_INTERNAL_conv`,
then `Tagged_Solver.solve_tac` — dispatching to whichever solver
(`PRECOND`/`PRECOND_OPT`/`GEN_ALGO`/`GEN_OP`/`STRUCT_EQ`/...) is registered
for that tag); otherwise resolve from the `trans_net` and, if the newly
introduced subgoal is `PREFER_tag`-marked, immediately try to solve it too
(prefer-conditions gate whether the rule was even applicable; defer-conditions
are checked only after recursive translation of the rest of the term
completes). `trans_tac` wraps this in a `REMOVE_INTERNAL_EQ`-based post-pass
that, once all steps succeed, simplifies with `APP_def`/`PROTECT_def`/
`ANNOT_def` and the `autoref_post_simps` set to strip the remaining tagging
machinery from the synthesized concrete term. Phase wiring:

```isabelle
val trans_phase = {
  init = trans_netD.init,
  tac = trans_tac,
  analyze = trans_analyze,
  pretty_failure = trans_pretty_failure
}
```

(`trans_analyze` is just `j < i`, i.e. "the goal interval is now empty";
`trans_pretty_failure` distinguishes an unsolved `DEFER_tag` side-condition
from an unsolved `(_,_)∈_` refinement goal in its error message.)

## 5. `Autoref_Gen_Algo.thy` — where `GEN_OP`'s side-condition is actually discharged

Not on the task's file list, but directly answers how the tutorial's
`autoref_list_eq`'s `GEN_OP eq (=) (R→R→Id)` premise gets solved — it isn't
solved by anything in `Autoref_Fix_Rel.thy`; the *solver* for the `GEN_OP`
tag is registered here, alongside the sibling `GEN_ALGO` side-condition tag
used for arbitrary extra preconditions on generic algorithms:

```isabelle
definition [simp, autoref_tag_defs]: "GEN_ALGO_tag P ≡ P"
lemma GEN_ALGO_tagI: "P ⟹ GEN_ALGO_tag P" by simp
abbreviation "SIDE_GEN_ALGO P ≡ PREFER_tag (GEN_ALGO_tag P)"
```

```isabelle
structure ga_side_thms = Named_Sorted_Thms (
  val name = @{binding autoref_ga_rules}
  val description = "Additional rules for generic algorithm side conditions"
  val sort = K I
  val transform = transform_ga_rule
)
```

```isabelle
fun decl_setup phi = I
#> Tagged_Solver.declare_solver @{thms GEN_ALGO_tagI} @{binding GEN_ALGO} 
    "Autoref: Generic algorithm side condition solver" 
    ( side_ga_tac) phi
#> Autoref_Phases.declare_solver @{thms GEN_OP_tagI} @{binding GEN_OP} 
    "Autoref: Generic algorithm operation instantiation" 
    ( side_ga_op_tac) phi
```

`side_ga_op_tac = SOLVED' (Autoref_Tacticals.REPEAT_ON_SUBGOAL
(Autoref_Translate.trans_step_tac ctxt))` — i.e. the `GEN_OP` solver
re-invokes the *translate* phase's own step tactic to instantiate the
schematic operator (`eq := (=)`) and check it refines under the stated
relator, recursively. `Autoref_Phases.declare_solver` (not
`Tagged_Solver.declare_solver` directly) is used for this one because the
tactic needs the full autoref context (all phase-populated rule nets)
initialized first — it wraps `Tagged_Solver.declare_solver` with the
lazy/guarded `Autoref_Phases.init_data` call shown in §6.

## 6. `Autoref_Phases.thy` — phase-driver architecture

No lemmas, no `attribute_setup`/`method_setup` — entirely ML infrastructure,
per the task's expectation ("Mostly ML"). The one piece of genuine
Isar-adjacent surface is the `phase` record shape and the module signature,
short enough to quote as documentation of the interface every phase must
implement:

```isabelle
signature AUTOREF_PHASES = sig
  type phase = {
    init: Proof.context -> Proof.context,
    tac: Proof.context -> int -> int -> tactic,
    analyze: Proof.context -> int -> int -> thm -> bool,
    pretty_failure: Proof.context -> int -> int -> thm -> Pretty.T
  }

  val register_phase: string -> int -> phase ->
    morphism -> Context.generic -> Context.generic
  val delete_phase: string -> morphism -> Context.generic -> Context.generic
  val get_phases: Proof.context -> (string * int * phase) list

  val get_phase: string -> Proof.context -> (string * int * phase) option

  val init_phase: (string * int * phase) -> Proof.context -> Proof.context
  val init_phases: 
    (string * int * phase) list -> Proof.context -> Proof.context

  val init_data: Proof.context -> Proof.context

  val declare_solver: thm list -> binding -> string
    -> (Proof.context -> tactic') -> morphism
    -> Context.generic -> Context.generic

  val phase_tac: (string * int * phase) -> Proof.context -> tactic'
  val phases_tac: (string * int * phase) list -> Proof.context -> tactic'
  val all_phases_tac: Proof.context -> tactic'

  val phases_tacN: string list -> Proof.context -> tactic'
  val phase_tacN: string -> Proof.context -> tactic'

  val cfg_debug: bool Config.T
  val cfg_trace: bool Config.T
  val cfg_keep_goal: bool Config.T
end
```

Error reporting surface: each phase supplies its own `analyze` (did this
phase's goal interval fully close?) and `pretty_failure` (render the
remaining goals in a phase-specific way) — there is no single shared error
format. Structural description of the driver (ML body elided): phases are
kept in a priority-sorted `Generic_Data` list (`phase_data`,
`register_phase`/`delete_phase`/`get_phases`); `do_phase` runs one phase's
`tac` under `DETERM`, times it if `cfg_trace`, then branches on `analyze`
into either the continuation (`THEN_INTERVAL`, chaining to the next phase)
or `handle_fail_tac`, which prints `pretty_failure`'s output under
`cfg_debug` and then either fails the tactic (default) or, if
`cfg_keep_goal` is set, returns the goal state unchanged (`Seq.single st`) —
this is exactly the mechanism behind `apply (autoref (keep_goal))` leaving
an inspectable unsolved goal instead of failing the `apply`.
`declare_solver` is a thin wrapper around `Tagged_Solver.declare_solver`
that lazily calls `init_data` (running every phase's `init` once, guarded by
a `Proof_Data` flag) if a solver is ever invoked outside a full `autoref`
run, so debugging methods (§7) and cross-phase solvers (`GEN_OP`, §5) can
rely on every phase's rule nets being populated.

## 7. `Autoref_Tool.thy` — the `autoref` method assembly

### 7.1 Standard phase registration (the concrete pipeline order)

```isabelle
declaration ‹fn phi => let open Autoref_Phases in
  I
  #> register_phase "id_op" 10 Autoref_Id_Ops.id_phase phi
  #> register_phase "rel_inf" 20 
       Autoref_Rel_Inf.roi_phase phi
  #> register_phase "fix_rel" 22
       Autoref_Fix_Rel.phase phi
  #> register_phase "trans" 30
       Autoref_Translate.trans_phase phi
end
›
```

(A commented-out alternative registration immediately below it in the
source, using older names `id_ops_phase`/`hm_infer_rel_phase` and giving
`fix_rel` priority 21 instead of 22, is dead code from an earlier iteration
— not extracted further.)

### 7.2 The `autoref` method

```isabelle
text ‹Main method›
method_setup autoref = ‹let
    open Refine_Util
    val autoref_flags = 
          parse_bool_config "trace" Autoref_Phases.cfg_trace
      ||  parse_bool_config "debug" Autoref_Phases.cfg_debug
      ||  parse_bool_config "keep_goal" Autoref_Phases.cfg_keep_goal

    val autoref_phases = 
      Args.$$$ "phases" |-- Args.colon |-- Scan.repeat1 Args.name

  in
    parse_paren_lists autoref_flags 
    |-- Scan.option (Scan.lift (autoref_phases)) >>
    ( fn phases => fn ctxt => SIMPLE_METHOD' (
      (
        case phases of
          NONE => Autoref_Phases.all_phases_tac
        | SOME names => Autoref_Phases.phases_tacN names
      ) (Autoref_Phases.init_data ctxt) 
      (* TODO: If we want more fine-grained initialization here, solvers have
         to depend on phases, or on data that they initialize if necessary *)
    ))

  end

› "Automatic Refinement"
```

This is the literal source of `apply (autoref (trace))`
(`p2-tutorial-extracts.md` §2.4) and `apply (autoref (keep_goal))` (§4):
`trace`/`debug`/`keep_goal` are parenthesized boolean-config flags feeding
`Autoref_Phases.cfg_trace`/`cfg_debug`/`cfg_keep_goal` directly (§6); an
optional `phases: name1 name2 ...` argument restricts the run to a named
subsequence instead of `all_phases_tac`.

### 7.3 `autoref_higher_order_rule` — a derived attribute (structural note)

Declared via `Attrib.setup` inside a `setup ‹...›` ML block (not the
`attribute_setup` Isar keyword):

```isabelle
Attrib.setup @{binding autoref_higher_order_rule} 
  (Scan.succeed higher_order_rl_attr) "Autoref: Convert rule to higher-order form"
```

Structurally: applying `[autoref_higher_order_rule]` to a fully-applied
refinement fact `(c,f a1...an)∈R` re-derives the *un-applied*, higher-order
form `(c',f)∈A1→...→An→R` by re-proving the goal with `fun_relI` resolved
repeatedly and the original theorem discharging the base case — a
convenience for lifting partially-applied facts, not part of the core phase
pipeline and not consulted by any of the tutorial's acceptance examples.

### 7.4 Debugging methods (single-phase-step wrappers)

Each is a one-line `method_setup` wrapping exactly one internal tactic
already described above, for interactive debugging outside a full `autoref`
run:

```isabelle
method_setup autoref_trans_step_keep = ‹...Autoref_Translate.trans_dbg_step_tac...›
  "Single translation step, leaving unsolved side-coditions"
method_setup autoref_trans_step = ‹...Autoref_Translate.trans_step_tac...›
  "Single translation step"
method_setup autoref_trans_step_only = ‹...Autoref_Translate.trans_step_only_tac...›
  "Single translation step, not attempting to solve side-coditions"
method_setup autoref_side = ‹...Autoref_Translate.side_dbg_tac...›
  "Solve side condition, leave unsolved subgoals"
method_setup autoref_try_solve = ‹...Autoref_Fix_Rel.try_solve_tac...›
  "Try to solve constraint and trace debug information"
method_setup autoref_solve_step = ‹...Autoref_Fix_Rel.solve_step_tac...›
  "Single-step of constraint solver"
method_setup autoref_id_op = ‹...Autoref_Id_Ops.id_tac...›
method_setup autoref_solve_id_op = ‹...Autoref_Id_Ops.id_tac (cfg_ss_id_op:=false)...›
```

(ML wiring elided per instruction — each is literally `Scan.succeed (fn ctxt
=> SIMPLE_METHOD' (‹tac› (Autoref_Phases.init_data ctxt)))` in the source,
with the named tactic substituted in each case; docstrings quoted verbatim
where the source gives one.)

### 7.5 `CAST` and the `autoref_syn` locale

```isabelle
text ‹General casting-tag, that allows type-casting on concrete level, while 
  being identity on abstract level.›
definition [simp]: "CAST ≡ id"
lemma [autoref_itype]: "CAST ::⇩i I →⇩i I" by simp
```

(A follow-up comment in the source notes this "does currently not work" as
a general-purpose cast and the actual rule attempt is commented out — dead
end, not pursued further here.)

```isabelle
locale autoref_syn begin
  notation (input) APP (infixl "$" 900)
  notation (input) rel_ANNOT (infix ":::" 10)
  notation (input) ind_ANNOT (infix "::#" 10)
  notation OP ("OP")
  notation (input) ABS (binder "λ''" 10)
end

hide_const (open) PROTECT ANNOT OP APP ABS ID_FAIL rel_annot ind_annot
```

This is exactly what `Simple_DFS.thy`'s `context begin interpretation
autoref_syn . lemma [autoref_op_pat]: "E``{v} ≡ op_succ$E$v" end`
(`p2-tutorial-extracts.md` §2.1) opens locally to get `$`/`:::` infix
notation for one lemma without polluting the ambient namespace — the tags
themselves are otherwise `hide_const (open)`-hidden globally.

## 8. `autoref_struct_expand` — declared in `Autoref_Bindings_HOL.thy`, *not* in `Tool/`

Grepped for across every `Tool/` theory (`Autoref_Fix_Rel.thy`,
`Autoref_Translate.thy`, `Autoref_Id_Ops.thy`, all others) and across
`Parametricity/{Relators,Param_HOL,Param_Tool}.thy` — no match anywhere in
`Automatic_Refinement`'s generic Tool/Parametricity layers. It is declared
locally, consumer-side, in `Autoref_Bindings_HOL.thy` itself (the same file
`p2-tutorial-extracts.md` extracts the tutorial's acceptance examples from),
immediately after the file's `imports "Tool/Autoref_Tool"` line:

```isabelle
subsection "Structural Expansion"
text ‹
  In some situations, autoref imitates the operations on typeclasses and
  the typeclass hierarchy. This may result in structural mismatches, e.g.,
  a hashcode side-condition may look like:
    @{text [display] "is_hashcode (prod_eq (=) (=)) hashcode"}

  This cannot be discharged by the rule
    @{text [display] "is_hashcode (=) hashcode"}
  
  In order to handle such cases, we introduce a set of simplification lemmas
  that expand the structure of an operator as far as possible.
  These lemmas are integrated into a tagged solver, that can prove equality
  between operators modulo structural expansion.
›

definition [simp]: "STRUCT_EQ_tag x y ≡ x = y"
lemma STRUCT_EQ_tagI: "x=y ⟹ STRUCT_EQ_tag x y" by simp

ML ‹
  structure Autoref_Struct_Expand = struct
    structure autoref_struct_expand = Named_Thms (
      val name = @{binding autoref_struct_expand}
      val description = "Autoref: Structural expansion lemmas"
    )

    fun expand_tac ctxt = let
      val ss = ctxt |> put_simpset HOL_basic_ss |> Simplifier.add_simps (autoref_struct_expand.get ctxt)
    in
      SOLVED' (asm_simp_tac ss)
    end

    val setup = autoref_struct_expand.setup
    val decl_setup = fn phi =>
      Tagged_Solver.declare_solver @{thms STRUCT_EQ_tagI} @{binding STRUCT_EQ} 
        "Autoref: Equality modulo structural expansion" 
        (expand_tac) phi
  end
›
```

So `autoref_struct_expand`'s DB, its `expand_tac` (a bare `asm_simp_tac`
against exactly the registered `[autoref_struct_expand]` lemmas), and its
`STRUCT_EQ` `Tagged_Solver` registration are all *HOL-bindings-layer*
infrastructure, not part of the generic `Automatic_Refinement/Tool/` spine
— a scoping question for the port (flagged in Gaps): should the Lean
port's structural-expansion mechanism live alongside the generic phase
machinery, or alongside the concrete HOL/nat/list bindings the way it does
upstream?

## 9. Database registry summary (for the Lean port to register under matching names)

| DB name | Declaring theory | Mechanism |
|---|---|---|
| `autoref_rules_raw` | `Tool/Autoref_Fix_Rel.thy` | `Named_Thms` (`Autoref_Rules`), §2.2 |
| `autoref_rules` | `Tool/Autoref_Relator_Interface.thy` | `attribute_setup`, wraps `autoref_rules_raw` + derived `autoref_itype` registration, §3 |
| `autoref_itype` | `Tool/Autoref_Id_Ops.thy` | `Named_Thms` (`intf_types`), §1.3 |
| `autoref_op_pat` | `Tool/Autoref_Id_Ops.thy` | `Named_Thms` (`op_patterns`), §1.3 |
| `autoref_op_pat_def` | `Tool/Autoref_Id_Ops.thy` | `Named_Thms` (`op_patterns_def`), §1.3 |
| `autoref_struct_expand` | `Autoref_Bindings_HOL.thy` (**not** `Tool/`) | local `Named_Thms`, §8 |
| `autoref_tyrel` | `Tool/Autoref_Fix_Rel.thy` | `Named_Sorted_Thms` (`tyrel_rules`), §2.5 |
| `autoref_tag_defs` | `Tool/Autoref_Tagging.thy` | `Named_Thms` (`Autoref_Tag_Defs`); backs `untag_conv`/`REMOVE_INTERNAL_conv` |
| `autoref_hom` (bonus) | `Tool/Autoref_Fix_Rel.thy` | `Named_Sorted_Thms` (`hom_rules`), §2.5 |
| `autoref_rel_intf` (bonus) | `Tool/Autoref_Relator_Interface.thy` | `Named_Thms` (`relator_intf`), §3 |
| `autoref_rel_indirect` (bonus) | `Tool/Autoref_Id_Ops.thy` (`Autoref_Rel_Inf`) | `Named_Thms` (`rel_indirect`), §1.5 |
| `autoref_post_simps` (bonus) | `Tool/Autoref_Translate.thy` | `Named_Thms`, §4.3 |
| `autoref_ga_rules` (bonus) | `Tool/Autoref_Gen_Algo.thy` | `Named_Sorted_Thms` (`ga_side_thms`), §5 |

## Gaps

- All phase `tac` bodies (`guess_relators_tac`, `id_tac`/`rec_tac`,
  `roi_step_tac`, `trans_step_tac`/`trans_tac`) are pure ML tactics per the
  task's instruction to skip raw ML bodies; only 2-4-sentence structural
  descriptions are given (§1.4, §1.5, §2.6, §4.3), plus the short
  `Named_Thms`/`Named_Sorted_Thms`/phase-record declarations, which are
  configuration data rather than tactic implementations and were judged
  short and load-bearing enough to quote directly.
- `Autoref_Phases.thy` has no `attribute_setup`/`method_setup`/lemma
  surface at all; the `AUTOREF_PHASES` signature (quoted in full, §6) is
  the closest thing to an Isar-visible interface, since it documents the
  `phase` record shape every phase implementation must match.
- The task's item 1 assumed `SIDE_PRECOND` and the priority-tag-adjacent
  `PREFER`/`DEFER` (as opposed to `PREFER_tag`/`DEFER_tag`) live in
  `Autoref_Fix_Rel.thy`; both are actually declared one phase later, in
  `Autoref_Translate.thy` (§4.2) — flagged explicitly rather than silently
  relocated, since the task named the file.
- `i_std`, used in `Autoref_Bindings_HOL.thy`'s `notes [autoref_itype] =
  itypeI[where 't="'a::numeral" and I=i_std]` (twice, in the two "hd"
  examples the task's item 6 also asked about), is **not declared anywhere**
  in `Automatic_Refinement` — grepped the full `Tool/`, `Parametricity/`,
  and `Autoref_Bindings_HOL.thy` itself, no `consts i_std` or equivalent.
  Since `itypeI : (c::'t) ::ᵢ I` leaves `I` fully polymorphic and
  unconstrained, `i_std` here elaborates as a bare schematic/free term
  variable standing in for "the standard/generic interface" (the real
  `i_std` constant, if one exists, would live in Collections/ICF's
  interface hierarchy — out of scope for `Automatic_Refinement` and for
  P2). **Flagging for the supervisor**: if the Lean port's acceptance
  examples reproduce these two `hd`-on-numerals cases from the tutorial
  extract, `i_std` should be treated as a fresh/placeholder interface, not
  looked up against a real definition.
- `autoref_struct_expand` (task item 4) is declared in
  `Autoref_Bindings_HOL.thy`, not in `Tool/` as its grouping in the task
  alongside `autoref_rules`/`autoref_itype`/`autoref_tyrel` might suggest —
  explicitly called out in §8, with the scoping question left open for the
  supervisor (generic-phase-layer port vs. HOL-bindings-layer port).
- `Tagged_Solver` itself (`Lib/Tagged_Solver.thy`, 8981 bytes) — the generic
  solver-registration framework every `declare_solver` call in this file set
  (`PRECOND`, `PRECOND_OPT`, `GEN_ALGO`, `GEN_OP`, `STRUCT_EQ`) ultimately
  calls into — was not fetched or extracted; out of the task's explicit
  file list, and its role (a `Named_Thms`-triggered dispatch table from
  tag-name to solving tactic) is adequately covered by the six call sites
  already quoted/described above.
- `Autoref_Chapter.thy` (102 bytes) was not fetched: per its size and the
  `*_Chapter.thy` naming convention seen consistently elsewhere in this AFP
  entry (`Autoref_Chapter.thy`, `Param_Chapter.thy`, both under 200 bytes),
  it is a bare `chapter`/section-heading stub with no declarations.
- The commented-out alternate phase registration in `Autoref_Tool.thy`
  (older `id_ops_phase`/`hm_infer_rel_phase` names, `fix_rel` at priority 21
  instead of 22) is dead code from a prior iteration of the tool; mentioned
  in §7.1, not further analyzed.
- Did not re-verify the `mirror-afp-2025-1` vs `mirror-afp-devel` path
  question independently; inherited both companion files' finding and used
  `mirror-afp-devel` throughout for consistency across all three P2 extract
  files.
- Isabelle source symbols: as both companion files noted, `Automatic_
  Refinement`'s raw theory bytes mix literal ASCII `\<foo>`-cartouche escapes
  and literal UTF-8 Isabelle symbols line-by-line within the same file (this
  was directly re-confirmed by inspecting the raw fetch: e.g.
  `Autoref_Fix_Rel.thy`'s `GEN_OP_tag`/`GEN_OP` lines mix legacy ASCII `==`/
  `==>` with a literal `≡`/`∈` two lines later). Rendering here was
  normalized to the same fixed Unicode substitution table both companion
  files used (`\<in>`→∈, `\<rightarrow>`→→, `\<langle>`/`\<rangle>`→⟨⟩,
  `\<Longrightarrow>`→⟹, `\<lambda>`→λ, `\<Rightarrow>`→⇒, `\<equiv>`/`==`→≡,
  `\<^sub>i`/`\<^sub>r`→⇩i/⇩r, `\<open>`/`\<close>`→‹› in prose/comment position
  and plain `"..."` in mixfix-template position — matching
  `p2-autoref-extracts.md`'s own rendering of `("⟨_⟩_" ...)`-style syntax
  declarations — `\<comment>` left as the literal keyword), diffed against
  the raw fetched bytes for every quoted block.

## Pipeline summary for the port

The pipeline is four chained phases, registered in `Autoref_Tool.thy` in
this priority order: `id_op` (10) → `rel_inf` (20) → `fix_rel` (22) →
`trans` (30). `id_op` (`Autoref_Id_Ops.id_phase`) takes the raw goal
`(?f,a)∈?R` and rewrites `a` into a fully `OP`/`APP`-tagged, interface-typed
`ID_OP a a' I` term, consulting `autoref_itype` for declared interface types
and `autoref_op_pat`/`autoref_op_pat_def` to rewrite surface operators
before falling back to generic constant/application/abstraction
identification; for the `is_None`/`is_Nil` acceptance examples this is
where `a = None` becomes `is_None$a` and `[] = a` becomes `is_Nil$a`, via an
`autoref_op_pat` rule not present in the extracted tutorial text. `rel_inf`
(`Autoref_Rel_Inf.roi_phase`) turns the interfaces fixed in step 1 into a
schematic relator skeleton for `?R` (`REL_OF_INTF`/`CNV_ANNOT`, consulting
`autoref_rel_indirect`); for all three acceptance examples, which use only
built-in `Id`/`nat_rel`/`list_rel`/`option_rel`, this phase does essentially
no work. `fix_rel` (`Autoref_Fix_Rel.phase`) collects one `CONSTRAINT f R`
subgoal per `OP f ::: R` tag in the term and solves them in sequence:
homogeneity rewriting (`autoref_hom`), anti-unification against the
priority-sorted `autoref_rules_raw`/`autoref_rules` database, `autoref_tyrel`
defaulting for any relator still unfixed, and final resolution against that
same rule set. This is the phase that pins `?R` to `⟨nat_rel⟩list_rel` for
`append`, to `Id` for list-equality (after also discharging that rule's
`GEN_OP eq (=) (R→R→Id)` premise via the `GEN_OP` solver registered in
`Autoref_Gen_Algo.thy`), and to `bool_rel` for `is_None`/`is_Nil`. `trans`
(`Autoref_Translate.trans_phase`) enters with every relator fixed and
rewrites `(?f,a')∈R` by repeatedly resolving against the now-instantiated
rule set plus `dflt_trans_rules` (`autoref_APP`/`autoref_ABS`/
`autoref_beta`), discharging each rule's `PREFER`/`DEFER`-tagged
side-condition through `Tagged_Solver` (`SIDE_PRECOND`, `GEN_ALGO`,
`STRUCT_EQ`) as each subterm is translated, and leaves `?f` fully
instantiated: `append [1,2,3] [4]`, `list_eq (=) [1,2,3] []`, `is_None
ai`/`is_Nil ai`. All four phases share one `Proof.context`, threaded by
`Autoref_Phases.init_phases`/`all_phases_tac` (invoked by the `autoref`
method), each contributing its own named-theorem database into that context
before its `tac` runs. On failure, each phase reports through its own
`analyze`/`pretty_failure` pair rather than a shared error format, and the
`autoref (keep_goal)` option leaves the last unsolved subgoal in the proof
state instead of failing outright — exactly what the `a = None`/`[] = a`
acceptance examples' `apply (autoref (keep_goal))` relies on.
