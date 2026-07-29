# P4 deep extracts — the `Sepref_Basic.thy` lemma suite, hr_comp, MK_FREE/MERGE, constraints

Companion to `p4-sepref-extracts.md` (which holds `fref`/`hfref`/`hfcomp`,
the translate/frame/monadify/id-op surface, and the If/While gap note) and
to `source-extracts.md` §4 (the `hn_refine` definition itself). Fetched
2026-07-29 by direct `curl` of the raw files at the pin: `isabelle_llvm_time`
@ `42dd7f5` (full SHA `42dd7f59998d76047bb4b6bce76d8f67b53a08b6`),
`thys/sepref/`. All ten `Sepref_*.thy` files were fetched whole (7,574
lines); this record quotes the load-bearing parts wave A–C consume.
Line numbers refer to the fetched files.

A fact this fetch corrected against `p4-sepref-extracts.md` §3: the
**cost-carrying `MERGE`/`MERGE1`/`MERGE_STAR` block lives in
`Sepref_Basic.thy` (lines ~800–870), not only in `Sepref_Frame.thy`** —
the artifact has the full merge calculus in credit-carrying form, so the
merge rules need porting, not deriving. (The If/While *translate* rules
remain absent from the cost artifact — that gap stands.)

## 1. `Sepref_Basic.thy` — tags and the assertion zoo

```isabelle
definition hn_ctxt :: "('a⇒'c⇒assn) ⇒ 'a ⇒ 'c ⇒ assn"
  — ‹Tag for refinement assertion›
  where "hn_ctxt P a c ≡ P a c"

definition pure :: "('b × 'a) set ⇒ 'a ⇒ 'b ⇒ assn"
  — ‹Pure binding, not involving the heap›
  where "pure R ≡ (λa c. ↑((c,a)∈R))"

definition is_pure :: "(_ ⇒ _ ⇒ assn) ⇒ bool"
  where "is_pure P ≡ ∃P'. ∀x x'. P x x'=↑(P' x x')"

definition the_pure :: "('b ⇒ 'a ⇒ assn) ⇒ ('a × 'b) set"
  where "the_pure P ≡ THE P'. ∀x x'. P x x'=↑((x',x)∈P')"

abbreviation "hn_val R ≡ hn_ctxt (pure R)"
lemma hn_val_unfold: "hn_val R a b = ↑((b,a)∈R)"

definition "invalid_assn R x y ≡ ↑(pure_part (R x y))"
abbreviation "hn_invalid R ≡ hn_ctxt (invalid_assn R)"

lemma invalidate_clone: "R x y = (invalid_assn R x y ** R x y)"
lemma invalidate_clone': "hn_ctxt R x y = (hn_invalid R x y ** hn_ctxt R x y)"
lemma invalid_pure_recover: "invalid_assn (pure R) x y = pure R x y"
lemma hn_invalidI: "hn_ctxt P x y s ⟹ hn_invalid P x y = □"

definition rdomp :: "('a ⇒ 'c ⇒ assn) ⇒ 'a ⇒ bool" where
  "rdomp R a ≡ ∃h c. R a c h"

definition prod_assn :: "('a1⇒'c1⇒assn) ⇒ ('a2⇒'c2⇒assn)
  ⇒ 'a1*'a2 ⇒ 'c1*'c2 ⇒ assn" where
  "prod_assn P1 P2 a c ≡ case (a,c) of ((a1,a2),(c1,c2)) ⇒
  P1 a1 c1 ** P2 a2 c2"   (* notation: A ×ₐ B *)

lemma prod_assn_pure_conv[simp]:
  "prod_assn (pure R1) (pure R2) = pure (R1 ×ᵣ R2)"
```

Key structural facts: `invalid_assn` is **pure** (ownership dropped — the
heap substrate frees the memory separately, via `MK_FREE` programs);
`invalidate_clone` (duplicating an assertion into its invalid shadow plus
itself) is the device behind `hnr_RETURN_pass` and the merge rules. Both
lean on the heap substrate; the port must re-derive their roles under
named-cell ownership (no dealloc → junk-weakening; see wave-A brief).

## 2. `Sepref_Basic.thy` — the `hn_refine` lemma suite

Intro/elim forms (statements; proofs are `wp`/`sep_algebra` plumbing):

```isabelle
lemma hn_refineI[intro]:
  assumes "⋀F s cr M. ⟦ m = REST M; (Γ**F) (ll_α(s,cr)) ⟧
          ⟹ (∃ra Ca. M ra ≥ Some Ca ∧
                     (wp c (λr s. (Γ' ** R ra r ** F ** GC) (ll_α s)) (s,cr+Ca)))"
  shows "hn_refine Γ c Γ' R m"

lemma hn_refineD:
  assumes "hn_refine Γ c Γ' R m"
  assumes "m = REST M" "(Γ ∧* F) (ll_α (s,cr))"
  shows  "(∃ra Ca. M ra ≥ Some Ca
        ∧ wp c (λr s. (Γ' ∧* R ra r ∧* F ∧* GC) (ll_α s)) (s, cr+Ca))"

lemma hn_refineI_SPECT:
  assumes "llvm_htriple ($t ** Γ) c (λr. Γ' ** R x r)"
  shows "hn_refine Γ c Γ' R (SPECT [x↦t])"

lemma hn_refineI':
  assumes "llvm_htriple Γ c (λr. Γ' ** R x r)"
  shows "hn_refine Γ c Γ' R (RETURNT x)"

lemma hn_refine_consume_return:   (* alternative characterization *)
  "hn_refine Γ c Γ' R m =
  nofailT m ⟶ (∀F s cr. llSTATE (Γ ∧* F) (s,cr) ⟶
      (∃ra Ca. consume (RETURNT ra) Ca ≤ m
        ∧ wp c (λr. llSTATE (Γ' ∧* R ra r ∧* F ∧* GC)) (s, cr+Ca)))"
```

Structural rules:

```isabelle
lemma hn_refine_preI:
  assumes "⋀h. Γ h ⟹ hn_refine Γ c Γ' R a"
  shows "hn_refine Γ c Γ' R a"
lemma hn_refine_nofailI:
  assumes "nofailT a ⟹ hn_refine Γ c Γ' R a"
  shows "hn_refine Γ c Γ' R a"
lemma hn_refine_false[simp]: "hn_refine sep_false c Γ' R m"
lemma hnr_FAIL[simp, intro!]: "hn_refine Γ c Γ' R FAILT"

lemma hn_refine_cons_complete:
  assumes R: "hn_refine P' c Q R m"
  assumes I: "P⊢P'"  and I': "Q⊢Q'"
  assumes R': "⋀x y. R x y ⊢ R' x y"
  assumes LE: "m≤m'"
  shows "hn_refine P c Q' R' m'"
lemmas hn_refine_cons      = …[OF _ _ _ _ order_refl]
lemmas hn_refine_cons_pre  = …[OF _ _ entails_refl entails_refl order_refl]
lemmas hn_refine_cons_post = …[OF _ entails_refl _ entails_refl order_refl]
lemmas hn_refine_cons_res  = …[OF _ entails_refl entails_refl _ order_refl]
lemmas hn_refine_ref       = …[OF _ entails_refl entails_refl entails_refl]

lemma hn_refine_frame:
  assumes hnr: "hn_refine P' c Q' R m"
  assumes ent: "P ⊢ P' ** F"
  shows "hn_refine P c (Q' ** F) R m"
lemma hn_refine_frame':  "hn_refine Γ c Γ' R m ⟹ hn_refine (Γ**F) c (Γ'**F) R m"
lemma hn_refine_frame'': "hn_refine Γ c Γ' R m ⟹ hn_refine (F**Γ) c (F**Γ') R m"

lemma hn_refine_augment_res:
  assumes A: "hn_refine Γ f Γ' R g"
  assumes B: "g ≤ₙ SPEC Φ t"
  shows "hn_refine Γ f Γ' (λa c. R a c ** ↑(Φ a)) g"

lemma hnr_pre_ex_conv:
  "hn_refine (EXS x. Γ x) c Γ' R a ⟷ (∀x. hn_refine (Γ x) c Γ' R a)"
lemma hnr_pre_pure_conv:
  "hn_refine (↑P ** Γ) c Γ' R a ⟷ (P ⟶ hn_refine Γ c Γ' R a)"
lemma hn_refine_extract_pre_val:
  "hn_refine (hn_val S xa xc ** Γ) c Γ' R m ⟷ ((xc,xa)∈S ⟶ hn_refine Γ c Γ' R m)"

lemma hn_refine_split_post: "hn_refine Γ c Γ' R a ⟹ hn_refine Γ c (Γ' or Γ'') R a"
lemma hn_refine_post_other: "hn_refine Γ c Γ'' R a ⟹ hn_refine Γ c (Γ' or Γ'') R a"
```

Return / assert:

```isabelle
lemma hnr_RETURN_pass:
  "hn_refine (hn_ctxt R x p) (return p) (hn_invalid R x p) R (RETURNT x)"
  (* proof: subst invalidate_clone', then vcg — the heap-substrate device *)
lemma hnr_RETURN_pure:
  "(c,a)∈R ⟹ hn_refine emp (return c) emp (pure R) (RETURNT a)"
lemma hnr_ASSERT:
  "(Φ ⟹ hn_refine Γ c Γ' R c') ⟹ hn_refine Γ c Γ' R (do { ASSERT Φ; c'})"
```

Bind — the artifact's cost-carrying rule, in full (`Sepref_Basic.thy`
~l. 628; the proof threads `minus_ecost_cost` through three `wp`
unfoldings and closes cost by `acost_plus_assoc`/
`cost_ecost_add_increasing2`):

```isabelle
lemma hnr_bind:
  assumes D1: "hn_refine Γ m' Γ1 Rh m"
  assumes D2:
    "⋀x x'. RETURNT x ≤ m ⟹ hn_refine (hn_ctxt Rh x x' ** Γ1) (f' x') (Γ2 x x') R (f x)"
  assumes IMP: "⋀x x'. Γ2 x x' ⊢ hn_ctxt Rx x x' ** Γ'"
  assumes MKF: "MK_FREE Rx fr"
  shows "hn_refine Γ (doM {x←m'; r ← f' x; fr x; return r}) Γ' R (m⤜f)"

text ‹Version for manual synthesis, if freeing of bound variable has been
  inserted manually›
lemma hnr_bind_manual_free:
  assumes D1: "hn_refine Γ m' Γ1 Rh m"
  assumes D2:
    "⋀x x'. RETURN x ≤ m ⟹ hn_refine (hn_ctxt Rh x x' ** Γ1) (f' x') (Γ') R (f x)"
  shows "hn_refine Γ (m'⤜f') Γ' R (m⤜f)"
```

Recursion (present for the record; out of translate scope per ledger D6):

```isabelle
lemma hnr_RECT:
  assumes S: "⋀cf af ax px. ⟦⋀ax px. hn_refine (hn_ctxt Rx ax px ** F) (cf px) (F' ax px) Ry (af ax)⟧
    ⟹ hn_refine (hn_ctxt Rx ax px ** F) (cB cf px) (F' ax px) Ry (aB af ax)"
  assumes M: "(⋀x. M.mono_body (λf. cB f x))"
  shows "hn_refine (hn_ctxt Rx ax px ** F) (Monad.REC cB px) (F' ax px) Ry (RECT aB ax)"
```

Cashing seed (P5 will need this shape; quoted for the record):

```isabelle
lemma ht_from_hnr:
  assumes "hn_refine Γ c Γ' R (timerefine E (do {_ ← ASSERT Φ; SPECT (emb Q T) }))"
  and "Φ"
  shows "llvm_htriple ($(timerefineA E T) ** Γ) c (λr. (EXS ra. ↑(Q ra) ** R ra r) ** Γ')"
```

## 3. `Sepref_Basic.thy` — `MK_FREE` and the cost-carrying `MERGE` calculus

```isabelle
definition "MK_FREE R f ≡ ∀a c. llvm_htriple (R a c) (f c) (λ_::unit. □)"
lemma mk_free_pure:    "MK_FREE (pure R) (λ_. return ())"
lemma mk_free_is_pure: "is_pure A ⟹ MK_FREE A (λ_. return ())"
lemma mk_free_invalid: "MK_FREE (invalid_assn R) (λ_. return ())"
lemma mk_free_pair:
  "MK_FREE R₁ f₁ ⟹ MK_FREE R₂ f₂ ⟹ MK_FREE (R₁×ₐR₂) (λ(c₁,c₂). doM {f₁ c₁; f₂ c₂})"
```

```isabelle
definition "MERGE Γ1 f1 Γ2 f2 Γ' ≡ llvm_htriple Γ1 f1 (λ_. Γ') ∧ llvm_htriple Γ2 f2 (λ_. Γ')"
definition "MERGE1 R1 f1 R2 f2 R' ≡ ∀ a c. MERGE (R1 a c) (f1 c) (R2 a c) (f2 c) (R' a c)"

lemma MERGE_STAR:
  "⟦MERGE1 R1 f1 R2 f2 R'; MERGE Γ1 fs1 Γ2 fs2 Γ'⟧ ⟹
   MERGE (hn_ctxt R1 a c ** Γ1) (doM {f1 c;fs1}) (hn_ctxt R2 a c ** Γ2)
         (doM {f2 c;fs2}) (hn_ctxt R' a c ** Γ')"
lemma MERGE_triv: "MERGE Γ (return ()) Γ (return ()) Γ"
lemma MERGE_END:  "MERGE FRI_END (return ()) FRI_END (return ()) □"
lemma MERGE1_eq:  "MERGE1 P (λ_. return ()) P (λ_. return ()) P"
lemma MERGE1_invalids: "MK_FREE R f ⟹
    MERGE1 (invalid_assn R) (λ_. return ()) R f (invalid_assn R)
  ∧ MERGE1 R f (invalid_assn R) (λ_. return ()) (invalid_assn R)"
```

The free-functions `f1`/`f2` exist because the heap substrate must run
deallocation code at merge points. See the wave-A brief: under named-cell
ownership with no dealloc op, freeing degenerates to assertion weakening
(entailment), so `MERGE`'s program arguments degenerate to nothing and
the calculus becomes two entailments — same shape, same rule names.

## 4. `Sepref_Rules.thy` — assertion-relation composition

```isabelle
definition hr_comp :: "('b ⇒ 'c ⇒ assn) ⇒ ('b × 'a) set ⇒ 'a ⇒ 'c ⇒ assn"
  — ‹Compose refinement assertion with refinement relation›
  where "hr_comp R1 R2 a c ≡ EXS b. R1 b c ** ↑((b,a)∈R2)"

definition hrp_comp
  :: "('d ⇒ 'b ⇒ assn) × ('d ⇒ 'c ⇒ assn) ⇒ ('d × 'a) set
      ⇒ ('a ⇒ 'b ⇒ assn) × ('a ⇒ 'c ⇒ assn)"
  where "hrp_comp RR' S ≡ (hr_comp (fst RR') S, hr_comp (snd RR') S)"

definition "hrr_comp R R1 R2 x y a c ≡
    if non_dep2 R1 then hr_comp (R1 undefined undefined) (R2 x) a c
    else EXS b. ↑((b,x)∈R) ** hr_comp (R1 b y) (R2 x) a c"

lemma hr_comp_Id1[simp]: "hr_comp (pure Id) R = pure R"
lemma hrr_comp_nondep: "hrr_comp T (λ_ _. A) R = (λx _. hr_comp A (R x))"

definition "attains_sup m m' RR ≡
  ∀r M' M. m=SPECT M ⟶ m'=SPECT M' ⟶ r∈dom M ⟶ (∃a. (r,a)∈RR) ⟶
    Sup {M' a| a. (r,a)∈RR} ∈ {M' a| a. (r,a)∈RR}"
lemma attains_sup_sv: "single_valued RR ⟹ attains_sup m m' RR"
```

(`hfcomp`, which consumes these, is quoted in `p4-sepref-extracts.md` §1.
`attains_sup`'s discharge route is `single_valued` — our `SingleValued`
from `Autoref/Relators.lean`.)

## 5. `Sepref_Constraints.thy` — deferred constraints

The mechanism: a designated **slot subgoal** collects constraints that
cannot be solved at rule-application time (typically `CONSTRAINT is_pure R`
or `MK_FREE`-style obligations on a yet-unknown relation metavariable);
they are discharged at the end of synthesis.

```isabelle
definition "CONSTRAINT_SLOT (x::prop) ≡ x"
definition CONSTRAINT where [simp]: "CONSTRAINT P x ≡ P x"
definition CN_FALSE :: "('a⇒bool) ⇒ 'a ⇒ bool" where [simp]: "CN_FALSE P x ≡ False"
  (* safe rules introducing CN_FALSE flag unsolvable constraints early *)

lemma insert_slot_rl1/rl2, remove_slot   (* slot plumbing *)
lemma CONSTRAINT_D / CONSTRAINT_I
named_theorems constraint_simps, constraint_abbrevs
(* ML: WITH_SLOT / ON_SLOT / create_slot_tac / ensure_slot_tac,
   solve_constraint_tac — a Tagged_Solver-style dispatch on P *)
```

## 6. `Sepref_Combinator_Setup.thy` — arity equations for monadify

The generated "mcomb" equations, obsolete-manual forms quoted (the ML
`mk_mcomb` generates the n-ary version on demand); these are the
eta/arity step (step 1) of monadify:

```isabelle
mk_mcomb1: "⋀c. c$x1 ≡ (⤜)$(EVAL$x1)$(λ₂x1. SP (c$x1))"
mk_mcomb2: "⋀c. c$x1$x2 ≡ (⤜)$(EVAL$x1)$(λ₂x1. (⤜)$(EVAL$x2)$(λ₂x2. SP (c$x1$x2)))"
mk_mcomb3: "⋀c. c$x1$x2$x3 ≡ (⤜)$(EVAL$x1)$(λ₂x1. (⤜)$(EVAL$x2)$(λ₂x2. (⤜)$(EVAL$x3)$(λ₂x3. SP (c$x1$x2$x3))))"
```

plus interface-type tagging (`map_type_eq`) used by `sepref_register`.

## Gaps / notes

- The If/While translate-rule gap of `p4-sepref-extracts.md` stands:
  nothing in the fetched cost artifact provides them; the cost-carrying
  **merge calculus does exist** (§3 above) and is what the derived
  `hnr_If` should consume.
- `Sepref_Id_Op.thy`, `Sepref_Monadify.thy`, `Sepref_Translate.thy`,
  `Sepref_Frame.thy`, `Sepref_Tool.thy`, `Sepref_Definition.thy` were
  fetched whole; their constant-level content is already recorded in
  `p4-sepref-extracts.md` §§2–5, and their ML drives search control that
  the port re-expresses in `TacticM` (same discipline as P3's
  `SepSolver`).
