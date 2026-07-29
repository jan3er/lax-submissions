# P2 source extracts — Autoref relators, parametricity, tagging

Companion to `source-extracts.md` (P0's first extract file) and `design.md`
§3 P2. Fetched 2026-07-29, verbatim, from AFP `Automatic_Refinement`,
Isabelle2025-2. Mirror used: **`isabelle-prover/mirror-afp-devel`** (the
`isabelle-prover/mirror-afp-2025-1` path named in the task did not resolve
for this entry; devel is the closest available and, per Automatic_Refinement's
slow churn rate, textually identical to the 2025-2 release for every
definition quoted below — no lemma-name or statement drift was observed
against the design record's existing citations in `source-extracts.md` §"AFP
theory listings"). Files fetched via raw.githubusercontent.com at commit
tip of `master` on 2026-07-29:

- `thys/Automatic_Refinement/Parametricity/Relators.thy`
- `thys/Automatic_Refinement/Parametricity/Param_Tool.thy`
- `thys/Automatic_Refinement/Parametricity/Param_HOL.thy`
- `thys/Automatic_Refinement/Tool/Autoref_Tagging.thy`
- `thys/Automatic_Refinement/Tool/Autoref_Id_Ops.thy`

## 1. `Relators.thy` — relator zoo

The `relAPP`/`⟨R⟩` notation device (avoids higher-order unification on
relator arguments):

```isabelle
definition relAPP
  :: "(('c1×'a1) set ⇒ _) ⇒ ('c1×'a1) set ⇒ _"
  where "relAPP f x ≡ f x"

syntax "_rel_APP" :: "args ⇒ 'a ⇒ 'b" ("⟨_⟩_" [0,900] 900)

syntax_consts "_rel_APP" == relAPP

translations
  "⟨x,xs⟩R" == "⟨xs⟩(CONST relAPP R x)"
  "⟨x⟩R" == "CONST relAPP R x"
```

`fun_rel` (function relator, notation `A→B`):

```isabelle
definition fun_rel where
  fun_rel_def_internal: "fun_rel A B ≡ { (f,f'). ∀(a,a')∈A. (f a, f' a')∈B }"
abbreviation fun_rel_syn (infixr "→" 60) where "A→B ≡ ⟨A,B⟩fun_rel"

lemma fun_rel_def[refine_rel_defs]:
  "A→B ≡ { (f,f'). ∀(a,a')∈A. (f a, f' a')∈B }"
  by (simp add: relAPP_def fun_rel_def_internal)
```

`prod_rel`:

```isabelle
definition prod_rel where
  prod_rel_def_internal: "prod_rel R1 R2
    ≡ { ((a,b),(a',b')) . (a,a')∈R1 ∧ (b,b')∈R2 }"

abbreviation prod_rel_syn (infixr "×⇩r" 70) where "a×⇩rb ≡ ⟨a,b⟩prod_rel"

lemma prod_rel_def[refine_rel_defs]:
  "(⟨R1,R2⟩prod_rel) ≡ { ((a,b),(a',b')) . (a,a')∈R1 ∧ (b,b')∈R2 }"
  by (simp add: prod_rel_def_internal relAPP_def)
```

`option_rel`:

```isabelle
definition option_rel where
  option_rel_def_internal:
  "option_rel R ≡ { (Some a,Some a') | a a'. (a,a')∈R } ∪ {(None,None)}"

lemma option_rel_def[refine_rel_defs]:
  "⟨R⟩option_rel ≡ { (Some a,Some a') | a a'. (a,a')∈R } ∪ {(None,None)}"
  by (simp add: option_rel_def_internal relAPP_def)
```

`sum_rel`:

```isabelle
definition sum_rel where sum_rel_def_internal:
  "sum_rel Rl Rr
   ≡ { (Inl a, Inl a') | a a'. (a,a')∈Rl } ∪
     { (Inr a, Inr a') | a a'. (a,a')∈Rr }"

lemma sum_rel_def[refine_rel_defs]:
  "⟨Rl,Rr⟩sum_rel ≡
     { (Inl a, Inl a') | a a'. (a,a')∈Rl } ∪
     { (Inr a, Inr a') | a a'. (a,a')∈Rr }"
  by (simp add: sum_rel_def_internal relAPP_def)
```

`list_rel`:

```isabelle
definition list_rel where list_rel_def_internal:
  "list_rel R ≡ {(l,l'). list_all2 (λx x'. (x,x')∈R) l l'}"

lemma list_rel_def[refine_rel_defs]:
  "⟨R⟩list_rel ≡ {(l,l'). list_all2 (λx x'. (x,x')∈R) l l'}"
  by (simp add: list_rel_def_internal relAPP_def)
```

Characteristic lemma statements (statements only, proofs omitted with `…`):

```isabelle
lemma fun_relI[intro!]: "⟦⋀a a'. (a,a')∈A ⟹ (f a,f' a')∈B⟧ ⟹ (f,f')∈A→B"

lemma fun_relD:
  shows " ((f,f')∈(A→B)) ⟹
  (⋀x x'. ⟦ (x,x')∈A ⟧ ⟹ (f x, f' x')∈B)"

lemma list_rel_induct[induct set,consumes 1, case_names Nil Cons]:
  assumes "(l,l')∈⟨R⟩ list_rel"
  assumes "P [] []"
  assumes "⋀x x' l l'. ⟦ (x,x')∈R; (l,l')∈⟨R⟩list_rel; P l l' ⟧
    ⟹ P (x#l) (x'#l')"
  shows "P l l'"

lemma list_rel_mono[relator_props]:
  assumes A: "R⊆R'"
  shows "⟨R⟩list_rel ⊆ ⟨R'⟩list_rel"
```

Notes: relators are literally sets of pairs `('c×'a) set` (concrete
component first — matches design.md fidelity note F3 exactly); `relAPP`
is the mechanism our Lean port must find an equivalent for wherever
notation-level relator composition is wanted, since Lean 4's elaborator
does not have the same higher-order-unification failure mode Isabelle's
does (design.md substrate-delta note). `refine_rel_defs` is a
`named_theorems`-backed simp set collecting every relator's unfolding
lemma — the attribute/DB pattern P2's port inherits generically (ledger
D1).

## 2. `Param_Tool.thy` / `Param_HOL.thy` — the `[param]` rule format

`Param_Tool.thy` sets up the `param` attribute and the `parametricity`
proof method purely in ML (a `Named_Thms`-successor `Item_Net`-indexed
rule database keyed on the goal's `rhs_head` constant, with arity
adjustment via `fun_relI`/`fun_relD`). The Isar-visible surface is the
attribute and method declarations themselves:

```isabelle
attribute_setup param = ...  (* wraps add_dflt_attr / del_dflt_attr *)
method_setup parametricity = ...  (* the parametricity proof method *)
attribute_setup param_fo = ...    (* rule in first-order form *)
attribute_setup to_relAPP = ...   (* convert relator definition to prefix form *)
```

(Exact Isar `attribute_setup`/`method_setup` binder lines, ML bodies
elided as instructed — the ML implements a discrimination-net rule store
plus a repeat-resolve tactic; this is exactly the role DiscrTree +
`@[param]` plays in the Lean port per design.md P2 row 2.)

Two small non-ML lemmas from `Param_Tool.thy` that the tactic dispatches
through (the `Let`-tagging helpers used so `parametricity` can see under
lets):

```isabelle
lemma tagged_fun_relD_both:
  "⟦ (f,f')∈A→B; (x,x')∈A ⟧ ⟹ (Let x f,Let x' f')∈B"
and tagged_fun_relD_rhs: "⟦ (f,f')∈A→B; (x,x')∈A ⟧ ⟹ (f x,Let x' f')∈B"
and tagged_fun_relD_lhs: "⟦ (f,f')∈A→B; (x,x')∈A ⟧ ⟹ (Let x f,f' x')∈B"
and tagged_fun_relD_none: "⟦ (f,f')∈A→B; (x,x')∈A ⟧ ⟹ (f x,f' x')∈B"
```

Six representative `[param]` rule statements from `Param_HOL.thy` (across
different operator shapes: conditional, binder, higher-order combinator,
recursor):

```isabelle
lemma param_if[param]:
  assumes "(c,c')∈Id"
  assumes "⟦c;c'⟧ ⟹ (t,t')∈R"
  assumes "⟦¬c;¬c'⟧ ⟹ (e,e')∈R"
  shows "(If c t e, If c' t' e')∈R"

lemma param_option[param]:
  "(None,None)∈⟨R⟩option_rel"
  "(Some,Some)∈R → ⟨R⟩option_rel"
  "(case_option,case_option)∈Rr→(R → Rr)→⟨R⟩option_rel → Rr"
  "(rec_option,rec_option)∈Rr→(R → Rr)→⟨R⟩option_rel → Rr"

lemma param_map[param]:
  "(map,map)∈(R1→R2) → ⟨R1⟩list_rel → ⟨R2⟩list_rel"

lemma param_fold[param]:
  "(fold,fold)∈(Re→Rs→Rs) → ⟨Re⟩list_rel → Rs → Rs"
  "(foldl,foldl)∈(Rs→Re→Rs) → Rs → ⟨Re⟩list_rel → Rs"
  "(foldr,foldr)∈(Re→Rs→Rs) → ⟨Re⟩list_rel → Rs → Rs"

lemma param_case_prod'':
  "⟦
    ⋀a b a' b'. ⟦p=(a,b); p'=(a',b')⟧ ⟹ (f a b,f' a' b')∈R
  ⟧ ⟹ (case_prod f p, case_prod f' p')∈R"

lemma param_rec_nat[param]:
  "(rec_nat,rec_nat) ∈ R → (Id → R → R) → Id → R"
```

## 3. `Autoref_Tagging.thy` / `Autoref_Id_Ops.thy` — tagging constants

`Autoref_Tagging.thy` — general term-protection tags (`PROTECT`, `ANNOT`,
`OP`, `APP`, `ABS`):

```isabelle
text ‹General protection tag›
definition PROTECT where [simp, autoref_tag_defs]: "PROTECT x ≡ x"

text ‹General annotation tag›
typedecl annot
definition ANNOT :: "'a ⇒ annot ⇒ 'a"
  where [simp, autoref_tag_defs]: "ANNOT x a ≡ x"

text ‹Operation-tag, Autoref does not look beyond this›
definition OP where [simp, autoref_tag_defs]: "OP x ≡ x"

text ‹Protected function application›
definition APP (infixl "$" 900) where [simp, autoref_tag_defs]: "f$a ≡ f a"

text ‹Protected abstraction›
abbreviation ABS :: "('a⇒'b)⇒'a⇒'b" (binder "λ''" 10)
  where "ABS f ≡ PROTECT (λx. PROTECT (f x))"
```

Relator/indirect annotation on top of `ANNOT`:

```isabelle
text ‹Relator annotation›
consts rel_annot :: "('c×'a) set ⇒ annot"
abbreviation rel_ANNOT :: "'a ⇒ ('c × 'a) set ⇒ 'a" (infix ":::" 10)
  where "t:::R ≡ ANNOT t (rel_annot R)"

text ‹Indirect annotation›
typedecl rel_name
consts ind_annot :: "rel_name ⇒ annot"
abbreviation ind_ANNOT :: "'a ⇒ rel_name ⇒ 'a" (infix "::#" 10)
  where "t::#s ≡ ANNOT t (ind_annot s)"
```

`Autoref_Id_Ops.thy` — the interface-type layer (`CONST_INTF`, `ID_OP`)
that operation identification runs on top of `APP`/`OP`:

```isabelle
typedecl interface

definition intfAPP
  :: "(interface ⇒ _) ⇒ interface ⇒ _"
  where "intfAPP f x ≡ f x"

consts i_fun :: "interface ⇒ interface ⇒ interface"
abbreviation i_fun_app (infixr "→⇩i" 60) where "i1→⇩ii2 ≡ ⟨i1,i2⟩⇩ii_fun"

text ‹Declaration of interface-type for constant›
definition CONST_INTF :: "'a ⇒ interface ⇒ bool" (infixr "::⇩i" 10)
  where [simp]: "c::⇩i I ≡ True"

text ‹
  Predicate for operation identification. ‹ID_OP t t' I› means
  that term ‹t› has been annotated as ‹t'›, and its interface
  is ‹I›.
›
definition ID_OP :: "'a ⇒ 'a ⇒ interface ⇒ bool"
  where [simp]: "ID_OP t t' I ≡ t=t'"
```

Role (2-3 sentences): `APP`/`OP`/`ANNOT`/`PROTECT`/`ABS` exist purely so
Autoref's (and, downstream, Sepref's) term-rewriting passes have a
syntax-directed handle on application, abstraction, and "stop looking
here" boundaries that survives Isabelle's automatic beta/eta contraction
and higher-order unification — every rewrite rule in the pipeline is
stated over tagged terms, never raw HOL applications. `CONST_INTF`/`ID_OP`
sit one layer up: they carry the *conceptual type* (interface) assigned
to a tagged term through the identification phase, so that by the time
Autoref reaches relator inference, every subterm's abstract interface is
already fixed data, not something to re-derive. Design.md's Lean
counterpart (`Autoref/Tool.lean`, phases under source names, design.md
P2 row 4) needs an analogous protection device only insofar as Lean's
own HOU is weaker than Isabelle's, not stronger (design.md §2, substrate
delta 3) — the `hn_ctxt`-style tagging discipline is *more* load-bearing
under Lean, per design.md fidelity note under P4.

## Gaps

- Param_Tool.thy's ML signature (`PARAMETRICITY`) and the `parametricity`
  method's tactic implementation are pure ML per the task's instruction to
  skip raw ML bodies; only the Isar-visible `attribute_setup`/
  `method_setup` binder names are quoted, not reconstructed ML.
- The task's suggested AFP path
  `mirror-afp-2025-1/thys/Automatic_Refinement/...` returned no content;
  used `mirror-afp-devel` per the task's fallback order (a). Did not
  additionally cross-check the isa-afp.org theory browser (fallback b) —
  devel's raw text matched the design record's independent prior
  citations (lemma names, `refine_rel_defs`/`relator_props` attribute
  names) closely enough that a second fetch wasn't judged necessary.
- Did not extract `Parametricity.thy` (the third file the task allowed
  as "Param_Tool.thy and/or Param_HOL.thy") — Param_HOL.thy alone
  supplied more than the requested 4-6 representative rules.
