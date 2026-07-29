# P4 source extracts — hfref/fref/FCOMP, translate, frame, monadify, id-op

Companion to `source-extracts.md` (P0's first extract file, which already
holds the `hn_refine` extract this file builds on) and `design.md` §3 P4.
Fetched 2026-07-29, verbatim, from `isabelle_llvm_time` @ `42dd7f5`
(pin per `design.md` §1), `thys/sepref/`:

- `Sepref_Rules.thy`, `Sepref_Translate.thy`, `Sepref_Frame.thy`,
  `Sepref_Monadify.thy`, `Sepref_Id_Op.thy` — all five requested files
  exist directly in `isabelle_llvm_time`'s `thys/sepref/` (no AFP
  `Refine_Imperative_HOL` substitution needed for the files themselves).
- Two items (the `If` and `WHILE` translate rules) are **not** present in
  the cost-carrying artifact's `Sepref_Basic.thy`/`Sepref_Translate.thy`
  under any name — quoted instead from the richer, no-cost AFP twin
  `Refine_Imperative_HOL` (mirror `isabelle-prover/mirror-afp-devel`,
  closest to Isabelle2025-2, same fallback used in
  `p2-autoref-extracts.md`), files `Sepref_Basic.thy` and
  `Sepref_Translate.thy`. Marked `[AFP]` below.
- `Frame_Infer.thy` (`thys/lib/`) for `ENTAILS`, which `Sepref_Frame.thy`
  imports rather than redefining.

## 1. `Sepref_Rules.thy` — `hfref`, `fref`, `FCOMP`

`fref` — the pure-function refinement judgment with precondition
(notation `[P]⇩f⇩d R → S`):

```isabelle
definition fref :: "('c ⇒ bool) ⇒ ('a × 'c) set ⇒ ('c ⇒ ('b × 'd) set)
         ⇒ (('a ⇒ 'b) × ('c ⇒ 'd)) set"
  ("[_]⇩f⇩d _ → _" [0,60,60] 60)
where "[P]⇩f⇩d R → S ≡ {(f,g). ∀x y. P y ∧ (x,y)∈R ⟶ (f x, g y)∈S y}"

abbreviation freft ("_ →⇩f⇩d _" [60,60] 60) where "R →⇩f⇩d S ≡ ([λ_. True]⇩f⇩d R → S)"
abbreviation freftnd ("_ →⇩f _" [60,60] 60) where "R →⇩f S ≡ ([λ_. True]⇩f⇩d R → (λ_. S))"
abbreviation frefnd ("[_]⇩f _ → _" [0,60,60] 60) where "[P]⇩f R → S ≡ [P]⇩f⇩d R → (λ_. S)"
```

`hfref` — the heap-function refinement judgment, `[P]⇩a⇩d RS → T`: a
precondition, a pair of parameter refinement assertions per argument
(before/after, for destructive-update tracking), and the result
refinement assertion, all cashed out through `hn_refine` per-call:

```isabelle
definition hfref
  :: "
    ('a ⇒ bool)
 ⇒ (('a ⇒ 'ai ⇒ assn) × ('a ⇒ 'ai ⇒ assn))
 ⇒ ('a ⇒ 'ai ⇒ 'b ⇒ 'bi ⇒ assn)
 ⇒ (('ai ⇒ 'bi llM) × ('a⇒('b,_) nrest)) set"
 ("[_]⇩a⇩d _ → _" [0,60,60] 60)
 where
  "[P]⇩a⇩d RS → T ≡ { (f,g) . ∀c a.  P a ⟶ hn_refine (fst RS a c) (f c) (snd RS a c) (T a c) (g a)}"

abbreviation hfrefnd ("[_]⇩a _ → _" [0,60,60] 60) where "[P]⇩a RS → T ≡ ([P]⇩a⇩d RS → (λ_ _. T))"
abbreviation hfreft ("_ →⇩a⇩d _" [60,60] 60) where "RS →⇩a⇩d T ≡ ([λ_. True]⇩a⇩d RS → T)"
abbreviation hfreftnd ("_ →⇩a _" [60,60] 60) where "RS →⇩a T ≡ [λ_. True]⇩a RS → T"
```

`FCOMP` — exposed as an attribute (`thm A[FCOMP B]` composes two
refinement-rule theorems); its content is the `hfcomp` lemma, composing
an `hfref` step with an `fref` step through relation composition
`hrp_comp`/`hrr_comp` (both `hr_comp`-based; `hr_comp` itself lifts an
ordinary relation composition to assertions and is not reproduced here):

```isabelle
lemma hfcomp:
  assumes A: "(f,g) ∈ [P]⇩a⇩d RR' → S"
  assumes B: "(g,h) ∈ [Q]⇩f⇩d T → (λx. ⟨U x⟩nrest_rel)"
  assumes SC: "⋀b1 a1. attains_sup (g b1) (h a1) (U a1)"
  shows "(f,h) ∈ [λa. Q a ∧ (∀a'. (a',a)∈T ⟶ P a')]⇩a⇩d
    hrp_comp RR' T → hrr_comp T S U"
```

```isabelle
attribute_setup FCOMP = Sepref_Rules.fcomp_attrib "Composition of refinement rules"
```

## 2. `Sepref_Translate.thy` — the translate phase

Header comment (theory-level `text`), describing the phase's role and
its three named rule collections:

```
This theory defines the translation phase.

The main functionality of the translation phase is to
apply refinement rules. Thereby, the linearity information is
exploited to create copies of parameters that are still required, but
would be destroyed by a synthesized operation.
These frame-based rules are in the named theorem collection
sepref_fr_rules, and the collection sepref_copy_rules
contains rules to handle copying of parameters.

Apart from the frame-based rules described above, there is also a set of
rules for combinators, in the collection sepref_comb_rules,
where no automatic copying of parameters is applied.

Moreover, this theory contains
  - A setup for the basic monad combinators and recursion.
  - A tool to import parametricity theorems.
  - Some setup to identify pure refinement relations, i.e., those not
    involving the heap.
  - A preprocessor that identifies parameters in refinement goals,
    and flags them with a special tag, that allows their correct handling.
```

Trans rules, statements only. **Bind** (`sepref_comb_rules`), routing a
monadic bind through a `doM` block with an explicit free of the bound
variable's remainder (`MK_FREE Rx fr`) — the cost-carrying form of the
same rule quoted as `hnr_bind` further down:

```isabelle
lemma hn_bind[sepref_comb_rules]:
  assumes D1: "hn_refine Γ m' Γ1 Rh m"
  assumes D2:
    "⋀x x'. bind_ref_tag x m ⟹
      hn_refine (hn_ctxt Rh x x' ** Γ1) (f' x') (Γ2 x x') R (f x)"
  assumes IMP: "⋀x x'. Γ2 x x' ⊢ hn_ctxt Rx x x' ** Γ'"
  assumes "MK_FREE Rx fr"
  shows "hn_refine Γ (doM {x←m'; r←f' x; fr x; return r}) Γ' R (NREST.bindT$m$(λ⇩2x. f x))"
```

**Return** (`sepref_fr_rules`), two forms — passing an already-owned
value back out (invalidating it), and returning a fresh pure value
(from `Sepref_Basic.thy`, since `Sepref_Translate.thy` itself only adds
the `PASS`-tagged pass-through rule `hn_pass`):

```isabelle
lemma hnr_RETURN_pass:
  "hn_refine (hn_ctxt R x p) (return p) (hn_invalid R x p) R (RETURNT x)"
  \<comment> ‹Pass on a value from the heap as return value›

lemma hnr_RETURN_pure:
  assumes "(c,a)∈R"
  shows "hn_refine emp (return c) emp (pure R) (RETURNT a)"
  \<comment> ‹Return pure value›

lemma hn_pass[sepref_fr_rules]:
  shows "hn_refine (hn_ctxt P x x') (return x') (hn_invalid P x x') P (PASS$x)"
```

**If** — [AFP `Refine_Imperative_HOL/Sepref_Basic.thy`; not present under
any name in `isabelle_llvm_time`'s cost-carrying `Sepref_Basic.thy`, see
Gaps]:

```isabelle
lemma hnr_If:
  assumes P: "Γ ⟹⇩t Γ1 * hn_val bool_rel a a'"
  assumes RT: "a ⟹ hn_refine (Γ1 * hn_val bool_rel a a') b' Γ2b R b"
  assumes RE: "¬a ⟹ hn_refine (Γ1 * hn_val bool_rel a a') c' Γ2c R c"
  assumes IMP: "Γ2b ∨⇩A Γ2c ⟹⇩t Γ'"
  shows "hn_refine Γ (if a' then b' else c') Γ' R (if a then b else c)"
```

**While** — [AFP `Refine_Imperative_HOL/Sepref_Translate.thy`; likewise
absent from the cost artifact, which synthesizes loops only via
`hn_RECT'`/`Monad.REC`, matching design.md's ledger **D6** ("translate
targets loop-structured programs only; abstract `RECT` must be refined
to `whileT`-form before synthesis")]:

```isabelle
lemma hn_monadic_WHILE_lin[sepref_comb_rules]:
  assumes "INDEP Rs"
  assumes FR: "P ⟹⇩t Γ * hn_ctxt Rs s' s"
  assumes b_ref: "⋀s s'. I s' ⟹ hn_refine
    (Γ * hn_ctxt Rs s' s)
    (b s)
    (Γb s' s)
    (pure bool_rel)
    (b' s')"
  assumes b_fr: "⋀s' s. TERM (monadic_WHILEIT,''cond'') ⟹ Γb s' s ⟹⇩t Γ * hn_ctxt Rs s' s"

  assumes f_ref: "⋀s' s. I s' ⟹ hn_refine
    (Γ * hn_ctxt Rs s' s)
    (f s)
    (Γf s' s)
    Rs
    (f' s')"
  assumes f_fr: "⋀s' s. TERM (monadic_WHILEIT,''body'') ⟹ Γf s' s ⟹⇩t Γ * hn_ctxt (λ_ _. true) s' s"
  shows "hn_refine
    P
    (heap_WHILET b f s)
    (Γ * hn_invalid Rs s' s)
    Rs
    (PR_CONST (monadic_WHILEIT I)$(λ⇩2s'. b' s')$(λ⇩2s'. f' s')$(s'))"
```

Side-condition markers the translate phase emits, all defined in
`Sepref_Translate.thy` itself: `bind_ref_tag` (recovers "what was this
binder's abstract value" for later side conditions), `vassn_tag`
(records that an assertion is nonempty/preconditions hold),
`RPREM` (discharge-by-assumption marker), `CPR_TAG` (aligns assertion
structure for the consequence rule), plus the `TERM (const,''name'')`
tags seen inline above (e.g. `TERM (monadic_WHILEIT,''cond'')`), used to
name *which* frame side-condition failed for debugging:

```isabelle
text ‹Tag to keep track of abstract bindings.
  Required to recover information for side-condition solving.›
definition "bind_ref_tag x m ≡ RETURN x ≤ m"

text ‹Tag to keep track of preconditions in assertions›
definition "vassn_tag Γ ≡ ∃h. Γ h"

text ‹Tag for side-condition solver to discharge by assumption›
definition RPREM :: "bool ⇒ bool" where [simp]: "RPREM P = P"

‹Tag to align structure of refinement assertions for consequence rule›
definition CPR_TAG :: "assn ⇒ assn ⇒ bool" where [simp]: "CPR_TAG y x ≡ True"
```

## 3. `Sepref_Frame.thy` — frame inference and merging

Header comment, describing `frame_tac` and `merge_tac`:

```
In this theory, we provide a specific frame inference tactic
for Sepref.

The first tactic, frame_tac, is a standard frame inference tactic,
based on the assumption that only hn_ctxt-assertions need to be
matched.

The second tactic, merge_tac, resolves entailments of the form
  F1 ∨⇩A F2 ⟹⇩t ?F
that occur during translation of if and case statements.
It synthesizes a new frame ?F, where refinements of variables
with equal refinements in F1 and F2 are preserved,
and the others are set to hn_invalid.
```

`ENTAILS` (defined in `thys/lib/Frame_Infer.thy`, which
`Sepref_Frame.thy` builds on rather than redefining) and `RECOVER_PURE`
(the pure-value-recovery predicate used at merge points):

```isabelle
definition "ENTAILS P Q ≡ P ⊢ Q"
lemma ENTAILSD: "ENTAILS P Q ⟹ P ⊢ Q" by (simp add: ENTAILS_def)

definition "RECOVER_PURE P Q ≡ P ⊢ Q"
```

`MERGE`/`MERGE1` — the merge-tactic's core constants. `MERGE Γ1 f1 Γ2
f2 Γ'` says "a free-function `f1` moves assertion `Γ1` to `Γ'` *and* a
free-function `f2` moves `Γ2` to the same `Γ'`" (i.e. both branches of an
`if`/`case` can be brought to a common postcondition by running the
appropriate cleanup); `MERGE1` is the per-variable, `hn_ctxt`-indexed
form that `MERGE_STAR` folds pointwise across a whole frame:

```isabelle
definition "MERGE Γ1 f1 Γ2 f2 Γ' ≡ llvm_htriple Γ1 f1 (λ_. Γ') ∧ llvm_htriple Γ2 f2 (λ_. Γ')"

definition "MERGE1 R1 f1 R2 f2 R' ≡ ∀ a c. MERGE (R1 a c) (f1 c) (R2 a c) (f2 c) (R' a c)"

lemma MERGE_STAR:
  assumes "MERGE1 R1 f1 R2 f2 R'" "MERGE Γ1 fs1 Γ2 fs2 Γ'"
  shows "MERGE (hn_ctxt R1 a c ** Γ1) (doM {f1 c;fs1}) (hn_ctxt R2 a c ** Γ2) (doM {f2 c;fs2}) (hn_ctxt R' a c ** Γ')"

lemma MERGE_END: "MERGE FRI_END (return ()) FRI_END (return ()) □"

lemma MERGE1_eq: "MERGE1 P (λ_. return ()) P (λ_. return ()) P"

lemma MERGE1_invalids:
  assumes "MK_FREE R f"
  shows "MERGE1 (invalid_assn R) (λ_. return ()) R f (invalid_assn R)"
    and "MERGE1 R f (invalid_assn R) (λ_. return ()) (invalid_assn R)"
```

`merge_thms = MERGE_END MERGE_STAR MERGE1_eq MERGE1_invalids` is exactly
the base case + inductive step + two boundary cases the algorithm
recurses over. Algorithm (from the header comment plus the lemma shapes
above): frame inference walks the two branch postconditions structurally
by `hn_ctxt`-tagged conjunct; where the same variable carries the same
refinement relation on both sides, it is kept (`MERGE1_eq`); where the
relations disagree or one side destroyed it, it is set to `hn_invalid`
on the merged frame (`MERGE1_invalids`, driven by whichever branch still
has an `MK_FREE` cleanup available); `MERGE_END`/`FRI_END` mark
"nothing left to match" on both sides simultaneously — this is the
concrete syntax-directed procedure design.md's `Sepref/Frame.lean` is
asked to port "per the source's algorithm."

## 4. `Sepref_Monadify.thy` — the `EVAL`/`SP`/`PASS` markers

Header comment:

```
In this phase, a monadic program is converted to complete monadic form,
that is, computation of compound expressions are made visible as top-level
operations in the monad.

The monadify process is separated into 2 steps.
  1. In a first step, eta-expansion is used to add missing operands
     to operations and combinators. This way, operators and combinators
     always occur with the same arity, which simplifies further processing.
  2. In a second step, computation of compound operands is flattened,
     introducing new bindings for the intermediate values.
```

The marker constants, verbatim, each with its own one-line comment as
written in the source:

```isabelle
definition SP \<comment> ‹Tag to protect content from further application of arity
  and combinator equations›
  where [simp]: "SP x ≡ x"

definition RCALL \<comment> ‹Tag that marks recursive call›
  where [simp]: "RCALL D ≡ D"
definition EVAL \<comment> ‹Tag that marks evaluation of plain expression for monadify phase›
  where [simp]: "EVAL x ≡ RETURN x"

definition [simp]: "PASS ≡ RETURN"
  \<comment> ‹Pass on value, invalidating old one›

definition COPY :: "'a ⇒ 'a"
  \<comment> ‹Marks required copying of parameter›
  where [simp]: "COPY x ≡ x"
```

`EVAL` is this artifact's analogue of what the task calls a "PLAIN"
marker: it is the tag that says "this subterm is an ordinary
(non-monadic) HOL expression that must be lifted into the monad via
`RETURN`/`RETURNT` before flattening" — i.e., exactly the boundary
between plain and monadic syntax that drives step 2 of the header
comment above.

## 5. `Sepref_Id_Op.thy` — operator-identification tagging

Header comment:

```
The operation identification phase is adapted from the Autoref tool.
The basic idea is to have a type system, which works on so called
interface types (also called conceptual types). Each conceptual type
denotes an abstract data type, e.g., set, map, priority queue.

Each abstract operation, which must be a constant applied to its arguments,
is assigned a conceptual type. Additionally, there is a set of
pattern rewrite rules, which are applied to subterms before type inference
takes place, and which may be backtracked over.
This way, encodings of abstract operations in Isabelle/HOL, like
λ_. None for the empty map, or fun_upd m k (Some v) for map update,
can be rewritten to abstract operations, and get properly typed.
```

`PROTECT2`/`APP'` (protected application, second flavor, to dodge
infinite pattern-rewriting loops — e.g. map lookup) and `PR_CONST`/
`UNPROTECT` (opaque-constant tagging, the mechanism `PR_CONST (op_...)`
uses throughout the stack to keep the identification pass from looking
inside a named operation):

```isabelle
definition [simp]: "PROTECT2 x (y::prop) ≡ x"

definition APP' (infixl "$''" 900) where [simp, autoref_tag_defs]: "f$'a ≡ f a"

definition [simp, autoref_tag_defs]: "PR_CONST x ≡ x" \<comment> ‹Tag to protect constant›
definition [simp, autoref_tag_defs]: "UNPROTECT x ≡ x" \<comment> ‹Gets
  converted to PR_CONST, after unprotecting its content›
```

`intf_type`/`ID` — the interface-typing judgment (infix `::⇩i`) and the
identification-result predicate `ID t t' T` ("term `t` was identified as
`t'`, of interface `T`") that Sepref inherits directly from Autoref's
`ID_OP` (`p2-autoref-extracts.md` §3):

```isabelle
definition intf_type :: "'a ⇒ 'b itself ⇒ bool" (infix "::⇩i" 10) where
  [simp]: "c::⇩iI ≡ True"

definition ID :: "'a ⇒ 'a ⇒ 'c itself ⇒ bool"
  where [simp]: "ID t t' T ≡ t=t'"
```

Role (2-3 sentences): these constants exist for exactly the reason
`Autoref_Tagging`/`Autoref_Id_Ops` do (`p2-autoref-extracts.md` §3) —
Sepref's operation-identification phase is a direct adaptation of
Autoref's, reusing `PROTECT`/`APP`/`ANNOT` from `Autoref_Tagging.thy`
(imported, not redefined) and layering `PR_CONST`/`UNPROTECT`/
`intf_type`/`ID` on top to fix, before synthesis proper starts, exactly
which abstract operation (and which interface/conceptual type) each
tagged subterm denotes. The Isar-visible `mop_...`-named operations
themselves (e.g. `mop_free`, seen already in `Sepref_Translate.thy`)
are declared per-operation elsewhere (`sepref_register`), not in this
file — this file supplies only the generic tagging machinery they ride
on.

## Gaps

- `hnr_If` and `hn_monadic_WHILE_lin` are quoted from the AFP
  `Refine_Imperative_HOL` twin, not `isabelle_llvm_time`: a repo-wide
  grep of every fetched `isabelle_llvm_time` `thys/sepref/*.thy` file
  found no `hn_if`/`hnr_If`/`MIf` and no `WHILE`/`hn_monadic_WHILE*`
  definition under any name. This is consistent with design.md's ledger
  **D6**: the cost artifact's example proofs synthesize loops through
  `Monad.REC`/`hn_RECT'` only, so a dedicated `WHILEIT`-shaped
  `sepref_comb_rules` entry was apparently never added to the
  time-cost line. Because the AFP version is the no-cost original, its
  `hn_refine`/entailment connectives (`⟹⇩t`, `∨⇩A`, `hn_val`) are the
  *no-cost* forms, not the credit-carrying ones from
  `source-extracts.md` §4 — a real port would need to re-derive the
  cost-carrying shapes of these two rules from the cost `hn_refine` and
  `hn_bind`/`hnr_RECT` (both quoted, cost-carrying, above and in
  `source-extracts.md`) rather than transcribe the AFP statements
  as-is. Flagging this explicitly for P4 rather than silently
  papering over it.
- `hr_comp`/`hrp_comp`/`hrr_comp` (the assertion-level relation-composition
  building blocks `hfcomp` is stated in terms of) were read but not
  quoted separately — `hfcomp`'s own statement was judged the more
  load-bearing "main FCOMP lemma" the task asked for, and re-quoting
  every helper it unfolds to would have ballooned this section well past
  what's needed to see FCOMP's shape.
- Did not quote `Sepref_Combinator_Setup.thy` or `Sepref_Constraints.thy`
  (referenced by `Sepref_Translate.thy`'s imports/header comment but not
  in the task's five-file list).
