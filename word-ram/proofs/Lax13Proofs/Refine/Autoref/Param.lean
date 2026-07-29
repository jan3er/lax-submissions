import Lax13Proofs.Refine.Autoref.Relators

/-!
Parametricity rules, the `@[param]` database, and the `parametricity`
tactic.

Port of `thys/Automatic_Refinement/Parametricity/Param_Tool.thy` and
`…/Param_HOL.thy` of AFP `Automatic_Refinement` (Lammich) at the pin
recorded in `plans/word-ram/refinement-tower/design.md` §1 — AFP for
Isabelle2025-2, release 2026-02-06 — together with the pure-HOL operator
bindings of `Autoref_Bindings_HOL.thy` that the P2 acceptance example
consumes. The verbatim source text this file is checked against is
`plans/word-ram/refinement-tower/p2-autoref-extracts.md` §2 (the
`Let`-tagging helpers and the six representative `[param]` rules) and
`plans/word-ram/refinement-tower/p2-tutorial-extracts.md` §3 (the
`nat`/`list`/`option` bindings, `list_eq`, `is_None`, `is_Nil`);
everything below quotes them in its doc-comments.

Layer discipline, as in `Autoref/Relators.lean`: parametricity is pure
relation material, one layer below the monad. This file imports
`Relators.lean` and nothing else — no `NREST` module appears in its
import closure.

## The source, verbatim

```isabelle
(* Param_Tool.thy — the Let-tagging helpers *)
lemma tagged_fun_relD_both:
  "⟦ (f,f')∈A→B; (x,x')∈A ⟧ ⟹ (Let x f,Let x' f')∈B"
and tagged_fun_relD_rhs: "⟦ (f,f')∈A→B; (x,x')∈A ⟧ ⟹ (f x,Let x' f')∈B"
and tagged_fun_relD_lhs: "⟦ (f,f')∈A→B; (x,x')∈A ⟧ ⟹ (Let x f,f' x')∈B"
and tagged_fun_relD_none: "⟦ (f,f')∈A→B; (x,x')∈A ⟧ ⟹ (f x,f' x')∈B"

(* Param_HOL.thy — six representative rules *)
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

lemma param_map[param]: "(map,map)∈(R1→R2) → ⟨R1⟩list_rel → ⟨R2⟩list_rel"

lemma param_fold[param]:
  "(fold,fold)∈(Re→Rs→Rs) → ⟨Re⟩list_rel → Rs → Rs"
  "(foldl,foldl)∈(Rs→Re→Rs) → Rs → ⟨Re⟩list_rel → Rs"
  "(foldr,foldr)∈(Re→Rs→Rs) → ⟨Re⟩list_rel → Rs → Rs"

lemma param_case_prod'':
  "⟦ ⋀a b a' b'. ⟦p=(a,b); p'=(a',b')⟧ ⟹ (f a b,f' a' b')∈R ⟧
   ⟹ (case_prod f p, case_prod f' p')∈R"

lemma param_rec_nat[param]: "(rec_nat,rec_nat) ∈ R → (Id → R → R) → Id → R"

(* Autoref_Bindings_HOL.thy — the pure-HOL bindings of the acceptance
   example (tagged [autoref_rules] there; see delta PM11) *)
lemma autoref_nat[autoref_rules]:
  "(0, 0::nat) ∈ nat_rel"  "(Suc, Suc) ∈ nat_rel → nat_rel"
  "(1, 1::nat) ∈ nat_rel"  "(numeral n::nat,numeral n::nat) ∈ nat_rel"
  "((<), (<) ::nat ⇒ _) ∈ nat_rel → nat_rel → bool_rel"
  "((≤), (≤) ::nat ⇒ _) ∈ nat_rel → nat_rel → bool_rel"
  "((=), (=) ::nat ⇒ _) ∈ nat_rel → nat_rel → bool_rel"
  "((+) ::nat⇒_,(+))∈nat_rel→nat_rel→nat_rel"
  "((-) ::nat⇒_,(-))∈nat_rel→nat_rel→nat_rel"
  "((div) ::nat⇒_,(div))∈nat_rel→nat_rel→nat_rel"
  "((*), (*))∈nat_rel→nat_rel→nat_rel"
  "((mod), (mod))∈nat_rel→nat_rel→nat_rel"

lemma autoref_append[autoref_rules]:
  "(append, append)∈⟨R⟩list_rel → ⟨R⟩list_rel → ⟨R⟩list_rel"

lemma refine_list[autoref_rules]:
  "(Nil,Nil)∈⟨R⟩list_rel"
  "(Cons,Cons)∈R → ⟨R⟩list_rel → ⟨R⟩list_rel"
  "(case_list,case_list)∈Rr→(R→⟨R⟩list_rel→Rr)→⟨R⟩list_rel→Rr"

lemma autoref_opt[autoref_rules]:
  "(None,None)∈⟨R⟩option_rel"  "(Some,Some)∈R → ⟨R⟩option_rel"
  "(case_option,case_option)∈Rr→(R → Rr)→⟨R⟩option_rel → Rr"
  "(rec_option,rec_option)∈Rr→(R → Rr)→⟨R⟩option_rel → Rr"

definition [simp]: "is_None a ≡ case a of None ⇒ True | _ ⇒ False"
lemma autoref_is_None[param,autoref_rules]:
  "(is_None,is_None)∈⟨R⟩option_rel → Id"

definition [simp]: "is_Nil a ≡ case a of [] ⇒ True | _ ⇒ False"
lemma autoref_is_Nil[param,autoref_rules]:
  "(is_Nil,is_Nil)∈⟨R⟩list_rel → bool_rel"

fun list_eq :: "('a ⇒ 'a ⇒ bool) ⇒ 'a list ⇒ 'a list ⇒ bool" where
  "list_eq eq [] [] ⟷ True"
| "list_eq eq (a#l) (a'#l') ⟷ (if eq a a' then list_eq eq l l' else False)"
| "list_eq _ _ _ ⟷ False"

lemma autoref_list_eq_aux:
  "(list_eq,list_eq) ∈ (R → R → Id) → ⟨R⟩list_rel → ⟨R⟩list_rel → Id"

lemma list_eq_expand[autoref_struct_expand]: "(=) = (list_eq (=))"
```

## Substrate deltas and departures, each flagged

**PM1 — `Id` reads `Set.diagonal`, and `nat_rel`/`bool_rel` are
abbreviations for it.** Isabelle's `Id :: ('a×'a) set` is mathlib's
`Set.diagonal α`, which is the spelling wave A already committed to
(`br_id : br id (fun _ => True) = Set.diagonal α`). The source's
`nat_rel`/`bool_rel` are `Id` at `nat`/`bool` — here `natRel`/`boolRel`,
declared `abbrev` (not `def`) so that they are transparent to
unification exactly as a HOL abbreviation is, and so the tactic below
sees through them without an unfolding step.

**PM2 — `If` is ported at `cond`, with `ite` as a second form.** HOL's
`If :: bool ⇒ 'a ⇒ 'a ⇒ 'a` takes a *Bool*, and its exact Lean 4
counterpart is `cond` (`bif c then t else e`); this is also P1's
convention C1, "loop and branch conditions are `Bool`". `param_ite` is
the same rule at Lean's `ite`, whose condition is a `Prop` with a
`Decidable` instance; it is given because Lean code writes `if` far more
often than `cond`, and it costs three lines. Both carry the source's
premise shape (the condition pair related by `Id`, each branch related
under the corresponding truth of *both* conditions).

**PM3 — multi-statement source lemmas are split, one Lean theorem per
statement.** Isabelle's `lemma name: "stmt₁" "stmt₂" …` binds a *list*
of theorems under one name; Lean has no analogue. `param_option`
becomes `param_option_none` / `_some` / `_cases` / `_rec`, `param_fold`
becomes `param_fold_foldr` / `_foldl`, `refine_list` becomes
`refine_list_nil` / `_cons` / `_cases`, and `autoref_nat` becomes one
theorem per operator. The source's own numbering (`param_option(1)`, …)
is what the suffixes track.

**PM4 — eliminator argument order follows Lean's eliminators.**
`rec_option`, `rec_nat` have exactly Lean's `Option.rec` / `Nat.rec`
argument order (minor premises, then the major premise), so those two
rules are shape-for-shape. `case_option` / `case_list` do *not*:
`Option.casesOn` / `List.casesOn` take the scrutinee *first*. The rules
are stated at the Lean eliminators with the relator chain permuted
accordingly (`optionRel R →ᵣ Rr →ᵣ (R →ᵣ Rr) →ᵣ Rr` where the source
has `Rr→(R → Rr)→⟨R⟩option_rel → Rr`). Nothing about the rules' content
changes; a reader comparing against the source must permute.

**PM5 — of the source's `fold`/`foldl`/`foldr` triple, two are ported.**
Lean has `List.foldl` (argument order identical to HOL's `foldl`) and
`List.foldr` (HOL's `foldr` takes the list *before* the initial value;
Lean's takes it after, so the last two relators of that rule are
swapped). HOL's `fold` — `fold f xs s = foldl (flip f) s xs`, a
left fold with the element in the first argument — has no Lean 4
counterpart constant, so its rule is dropped rather than invented: there
is no term for it to fire on.

**PM6 — `param_case_prod''` is untagged, as in the source.** The
extract shows `lemma param_case_prod'':` with no `[param]` attribute,
unlike its five neighbours; that is preserved. (Its premise carries
equations `p=(a,b)`, `p'=(a',b')`, which is what makes it a rule to
apply by hand rather than one for a repeat-resolve loop.) It is stated
at `Prod.rec`, whose argument order matches HOL's `case_prod f p`.

**PM7 — numerals.** Lean has no `numeral` constant: `(4 : ℕ)` is
`@OfNat.ofNat ℕ 4 _`. The source's `(0,0)`, `(1,1)`, `(numeral n,
numeral n)` trio therefore collapses into one rule
`autoref_nat_lit : ∀ n : ℕ, (n, n) ∈ natRel`, which covers all three
and every other literal. `autoref_nat_zero` and `autoref_nat_one` are
kept as the source's own citable instances.

**PM8 — comparisons are `Bool`-valued through `decide`.** HOL's `bool`
*is* its `Prop`, so `((<), (<)) ∈ nat_rel → nat_rel → bool_rel` is a
statement about a two-valued function. Lean's `(· < ·) : ℕ → ℕ → Prop`
is not that function; `fun a b => decide (a < b)` is. The three
comparison rules are stated at the `decide` forms (P1 convention C1
again), and `param_prop_eq` records the `Prop`-valued twin at
`Set.diagonal Prop` for the one place it is cheap to state.

**PM9 — `is_None`/`is_Nil` map to Lean core constants.** The source
*defines* `is_None`/`is_Nil` because HOL has no such constant; Lean has
`Option.isNone` and `List.isEmpty` with exactly those two clauses, so
the rules are ported at the existing constants and no definition is
introduced. (`List.isEmpty`, not `List.isNil`: the latter does not
exist.)

**PM10 — `list_eq_expand` is stated but not tagged.** The source tags it
`[autoref_struct_expand]`, an attribute belonging to the structural
expansion pass of the translate phase — wave C machinery that does not
exist yet. The statement is ported verbatim modulo PM8 (`(=)` at
`List α` becomes the `decide`-form Bool equality); the tag is deferred
and marked at the declaration.

**PM11 — the `autoref_rules` database does not exist in this wave, so
its pure parametricity facts are tagged `@[param]`.** The bindings of
tutorial-extract §3 (`autoref_nat`, `autoref_append`, `refine_list`,
`autoref_opt`) carry `[autoref_rules]` in the source — the *translate*
phase's database, which is the sibling tagging/solver wave's and wave
C's to build. Their statements are pure parametricity facts of exactly
the `[param]` format, and `Param_HOL.thy` (26 KB, of which the extract
quotes six representative rules) is where the source's own `[param]`
twins live. Rather than invent an `autoref_rules` attribute this wave
does not own, or leave the rules invisible to every tactic, they are
tagged `@[param]` here under the extract's own names — the names are
what can be cited verbatim. When wave C lands `autoref_rules`, these
declarations get that tag too; nothing about their statements changes.
`autoref_is_None`/`autoref_is_Nil` are unaffected: the source already
tags them `[param,autoref_rules]`.

**PM12 — the `Let`-tagging helpers are ported at `letFun`.** HOL's `Let`
is an ordinary constant, so `parametricity` cannot see under it without
the four `tagged_fun_relD_*` rules. Lean 4 has two devices where HOL has
one: a `let` binder, which is zeta-reducible and which the elaborator
sees through without help (no rule can even be stated about it — there
is no head constant), and `letFun`, the constant behind `have x := v;
…`, which behaves exactly like HOL's `Let`. All four helpers are ported
at `letFun`, at the source's own names; the `let`-binder half of the
substrate needs no rule and gets none.

**PM13 — what is deliberately not ported.** `autoref_hd` (its statement
is phrased over `SIDE_PRECOND`, `OP`, `:::` and `$`) and
`autoref_list_eq` (phrased over `GEN_OP`) mention the tagging constants
of `Autoref_Tagging.thy`/`Autoref_Id_Ops.thy`, which belong to the
sibling wave and to wave C. The generic `PRIO_TAG_GEN_ALGO` layer of
extract §3 is the same story. Everything ported here is a bare
relatedness statement.

**PM14 — the tactic is a seed.** Stated in full below, at the tactic.

Inherited unchanged from wave A: **F3** (relators are
`Set (concrete × abstract)`, membership written `(c, a) ∈ R`), **R1**
(no `relAPP`: `⟨R⟩list_rel` reads `listRel R`), **R2** (definitions
camelCase, rule names the source's), **R3** (unfolding lemmas are
`mem_…_iff`).

## The refutation pass (ledger D4, repo practice)

Every statement in this file that is *not* quoted verbatim from an
extract — the `cond`/`ite` split of `param_if`, the permuted eliminator
chains of PM4, the `decide` forms of PM8, `autoref_nat_lit`,
`list_eq_decide`, and the two executable bridges of the gate — was
`#guard`-checked at concrete instances *before* it was proved, in the
gate at the bottom of this file. The gate's working relation is
`Sanity.halfRel = br (·/2) (· % 2 = 0)`: a genuinely non-identity,
non-total relation, so that a check about a rule's conclusion has
content and a mismatched premise is visibly rejected.
-/

namespace Lax13Proofs.Refine

variable {α β γ δ ε ζ : Type}

/-! ### `Id`, and its two named instances

Isabelle's `Id` is mathlib's `Set.diagonal` (delta PM1); the source's
`nat_rel` and `bool_rel` are `Id` at `nat` and `bool`. -/

/-- The source's `nat_rel`: `Id` at `nat`. -/
abbrev natRel : Set (ℕ × ℕ) := Set.diagonal ℕ

/-- The source's `bool_rel`: `Id` at `bool`. -/
abbrev boolRel : Set (Bool × Bool) := Set.diagonal Bool

/-- HOL's `IdI`, the identity relation's introduction rule, cited by the
tutorial's examples (`notes [autoref_rules] = IdI[of src]`). Untagged:
its conclusion `(?a, ?a) ∈ Set.diagonal ?α` unifies with any goal whose
relation is still a metavariable, which is precisely the mis-firing the
source's head-constant rule indexing avoids and this wave's linear scan
does not. -/
theorem IdI (a : α) : (a, a) ∈ Set.diagonal α := rfl

/-- Every function is parametric in the identity relation. The workhorse
behind the source's `by auto` proofs of the generic and `nat` layers of
extract §3. -/
theorem funRel_diagonal_self (f : α → β) :
    (f, f) ∈ Set.diagonal α →ᵣ Set.diagonal β := by
  rintro a a' h
  exact congrArg f h

/-- Binary form of `funRel_diagonal_self`. -/
theorem funRel_diagonal_self₂ (f : α → β → γ) :
    (f, f) ∈ Set.diagonal α →ᵣ Set.diagonal β →ᵣ Set.diagonal γ := by
  rintro a a' ha b b' hb
  exact congrArg₂ f ha hb

/-! ### The conditional (`Param_HOL.thy`) -/

/-- The source's `param_if`, at `cond` — HOL's `If` takes a `bool`, and
`cond` is its Lean 4 counterpart (delta PM2). -/
@[param] theorem param_if {R : Set (α × β)} {c c' : Bool} {t e : α} {t' e' : β}
    (hc : (c, c') ∈ boolRel)
    (ht : c = true → c' = true → (t, t') ∈ R)
    (he : c = false → c' = false → (e, e') ∈ R) :
    (cond c t e, cond c' t' e') ∈ R := by
  have hcc : c = c' := hc
  subst hcc
  cases c
  · exact he rfl rfl
  · exact ht rfl rfl

/-- The source's `param_if` at Lean's `ite`, whose condition is a
`Prop` with a `Decidable` instance (delta PM2). -/
@[param] theorem param_ite {R : Set (α × β)} {c c' : Prop} [Decidable c] [Decidable c']
    {t e : α} {t' e' : β}
    (hc : (c, c') ∈ Set.diagonal Prop)
    (ht : c → c' → (t, t') ∈ R)
    (he : ¬c → ¬c' → (e, e') ∈ R) :
    (if c then t else e, if c' then t' else e') ∈ R := by
  have hcc : c = c' := hc
  subst hcc
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ht h h
  · rw [if_neg h, if_neg h]; exact he h h

/-! ### The option type (`param_option`, `autoref_opt`)

Split one theorem per source statement (delta PM3); the two eliminators
are Lean's, whose argument order differs for `casesOn` (delta PM4).
Extract §3's `autoref_opt` states these same four facts for the
translate phase's database; they are not restated here. -/

/-- The source's `param_option`(1). -/
@[param] theorem param_option_none {R : Set (α × β)} :
    ((none : Option α), (none : Option β)) ∈ optionRel R :=
  mem_optionRel_none_none

/-- The source's `param_option`(2). -/
@[param] theorem param_option_some {R : Set (α × β)} :
    ((some : α → Option α), (some : β → Option β)) ∈ R →ᵣ optionRel R :=
  fun _ _ h => mem_optionRel_some_some.mpr h

/-- The source's `param_option`(3), `case_option`, at Lean's
`Option.casesOn` — scrutinee first (delta PM4). -/
@[param] theorem param_option_cases {R : Set (α × β)} {Rr : Set (γ × δ)} :
    ((@Option.casesOn α (fun _ => γ)), (@Option.casesOn β (fun _ => δ))) ∈
      optionRel R →ᵣ Rr →ᵣ (R →ᵣ Rr) →ᵣ Rr := by
  rintro x x' hx n n' hn s s' hs
  cases x with
  | none =>
    cases x' with
    | none => exact hn
    | some a' => exact absurd hx mem_optionRel_none_some
  | some a =>
    cases x' with
    | none => exact absurd hx mem_optionRel_some_none
    | some a' => exact hs a a' (mem_optionRel_some_some.mp hx)

/-- The source's `param_option`(4), `rec_option`, at Lean's
`Option.rec` — same argument order as the source (delta PM4). -/
@[param] theorem param_option_rec {R : Set (α × β)} {Rr : Set (γ × δ)} :
    ((@Option.rec α (fun _ => γ)), (@Option.rec β (fun _ => δ))) ∈
      Rr →ᵣ (R →ᵣ Rr) →ᵣ optionRel R →ᵣ Rr := by
  rintro n n' hn s s' hs x x' hx
  cases x with
  | none =>
    cases x' with
    | none => exact hn
    | some a' => exact absurd hx mem_optionRel_none_some
  | some a =>
    cases x' with
    | none => exact absurd hx mem_optionRel_some_none
    | some a' => exact hs a a' (mem_optionRel_some_some.mp hx)

/-- The source's `autoref_is_None`, at `Option.isNone` (delta PM9). The
source tags it `[param,autoref_rules]`. -/
@[param] theorem autoref_is_None {R : Set (α × β)} :
    ((Option.isNone : Option α → Bool), (Option.isNone : Option β → Bool)) ∈
      optionRel R →ᵣ boolRel := by
  rintro x x' hx
  cases x with
  | none =>
    cases x' with
    | none => rfl
    | some a' => exact absurd hx mem_optionRel_none_some
  | some a =>
    cases x' with
    | none => exact absurd hx mem_optionRel_some_none
    | some a' => rfl

/-! ### Lists (`param_map`, `param_fold`, `autoref_append`,
`refine_list`, `autoref_is_Nil`) -/

/-- The source's `param_map`. -/
@[param] theorem param_map {R₁ : Set (α × β)} {R₂ : Set (γ × δ)} :
    ((List.map : (α → γ) → List α → List γ),
      (List.map : (β → δ) → List β → List δ)) ∈
      (R₁ →ᵣ R₂) →ᵣ listRel R₁ →ᵣ listRel R₂ := by
  rintro f f' hf l l' hl
  rw [mem_listRel_iff] at hl ⊢
  induction hl with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih => exact List.Forall₂.cons (hf _ _ hx) ih

/-- The source's `param_fold`(3), `foldr`. Lean's `List.foldr` takes the
initial value before the list, so the last two relators are swapped
against the source (delta PM5). -/
@[param] theorem param_fold_foldr {Re : Set (α × β)} {Rs : Set (γ × δ)} :
    ((List.foldr : (α → γ → γ) → γ → List α → γ),
      (List.foldr : (β → δ → δ) → δ → List β → δ)) ∈
      (Re →ᵣ Rs →ᵣ Rs) →ᵣ Rs →ᵣ listRel Re →ᵣ Rs := by
  rintro f f' hf s s' hs l l' hl
  rw [mem_listRel_iff] at hl
  induction hl with
  | nil => exact hs
  | cons hx _ ih => exact hf _ _ hx _ _ ih

/-- The source's `param_fold`(2), `foldl` — argument order identical to
the source's. -/
@[param] theorem param_fold_foldl {Re : Set (α × β)} {Rs : Set (γ × δ)} :
    ((List.foldl : (γ → α → γ) → γ → List α → γ),
      (List.foldl : (δ → β → δ) → δ → List β → δ)) ∈
      (Rs →ᵣ Re →ᵣ Rs) →ᵣ Rs →ᵣ listRel Re →ᵣ Rs := by
  rintro f f' hf
  suffices H : ∀ (l : List α) (l' : List β), (l, l') ∈ listRel Re →
      ∀ s s', (s, s') ∈ Rs → (List.foldl f s l, List.foldl f' s' l') ∈ Rs by
    exact fun s s' hs l l' hl => H l l' hl s s' hs
  intro l l' hl
  rw [mem_listRel_iff] at hl
  induction hl with
  | nil => exact fun s s' hs => hs
  | cons hx _ ih => exact fun s s' hs => ih _ _ (hf _ _ hs _ _ hx)

/-- The source's `autoref_append` (delta PM11 for the tag). -/
@[param] theorem autoref_append {R : Set (α × β)} :
    ((List.append : List α → List α → List α),
      (List.append : List β → List β → List β)) ∈
      listRel R →ᵣ listRel R →ᵣ listRel R := by
  rintro l l' hl m m' hm
  rw [mem_listRel_iff] at hl hm ⊢
  exact List.rel_append hl hm

/-- The source's `refine_list`(1) (delta PM11 for the tag). -/
@[param] theorem refine_list_nil {R : Set (α × β)} :
    (([] : List α), ([] : List β)) ∈ listRel R :=
  mem_listRel_nil

/-- The source's `refine_list`(2). -/
@[param] theorem refine_list_cons {R : Set (α × β)} :
    ((List.cons : α → List α → List α), (List.cons : β → List β → List β)) ∈
      R →ᵣ listRel R →ᵣ listRel R := by
  rintro x x' hx l l' hl
  exact mem_listRel_cons.mpr ⟨hx, hl⟩

/-- The source's `refine_list`(3), `case_list`, at Lean's
`List.casesOn` — scrutinee first (delta PM4). -/
@[param] theorem refine_list_cases {R : Set (α × β)} {Rr : Set (γ × δ)} :
    ((@List.casesOn α (fun _ => γ)), (@List.casesOn β (fun _ => δ))) ∈
      listRel R →ᵣ Rr →ᵣ (R →ᵣ listRel R →ᵣ Rr) →ᵣ Rr := by
  rintro l l' hl n n' hn c c' hc
  rw [mem_listRel_iff] at hl
  cases hl with
  | nil => exact hn
  | cons hx ht => exact hc _ _ hx _ _ ht

/-- The source's `autoref_is_Nil`, at `List.isEmpty` (delta PM9). The
source tags it `[param,autoref_rules]`. -/
@[param] theorem autoref_is_Nil {R : Set (α × β)} :
    ((List.isEmpty : List α → Bool), (List.isEmpty : List β → Bool)) ∈
      listRel R →ᵣ boolRel := by
  rintro l l' hl
  rw [mem_listRel_iff] at hl
  cases hl with
  | nil => rfl
  | cons _ _ => rfl

/-! ### Products and the natural-number recursor -/

/-- The source's `param_case_prod''`, at `Prod.rec` (same argument order
as HOL's `case_prod`). Untagged, as in the source (delta PM6). -/
theorem param_case_prod'' {R : Set (ε × ζ)} {f : α → γ → ε} {f' : β → δ → ζ}
    {p : α × γ} {p' : β × δ}
    (h : ∀ a b a' b', p = (a, b) → p' = (a', b') → (f a b, f' a' b') ∈ R) :
    (@Prod.rec α γ (fun _ => ε) f p, @Prod.rec β δ (fun _ => ζ) f' p') ∈ R := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  exact h a b a' b' rfl rfl

/-- The source's `param_rec_nat`, at `Nat.rec` — same argument order as
the source's `rec_nat`. -/
@[param] theorem param_rec_nat {R : Set (α × β)} :
    ((@Nat.rec (fun _ => α)), (@Nat.rec (fun _ => β))) ∈
      R →ᵣ (natRel →ᵣ R →ᵣ R) →ᵣ natRel →ᵣ R := by
  rintro z z' hz s s' hs n n' hn
  have hnn : n = n' := hn
  subst hnn
  clear hn
  show (@Nat.rec (fun _ => α) z s n, @Nat.rec (fun _ => β) z' s' n) ∈ R
  induction n with
  | zero => exact hz
  | succ k ih => exact hs k k rfl _ _ ih

/-! ### The `nat` bindings of extract §3

The source's `autoref_nat`, split one theorem per statement (PM3), with
numerals collapsed (PM7) and comparisons `decide`d (PM8). Every one is
an instance of `funRel_diagonal_self`, which is what the source's `by
auto` amounts to. -/

/-- The source's `autoref_nat`(4) — and, by PM7, also its (1) `(0,0)`
and (3) `(1,1)`: Lean has no `numeral` constant, so one rule covers
every literal. -/
@[param] theorem autoref_nat_lit (n : ℕ) : (n, n) ∈ natRel := rfl

/-- The source's `autoref_nat`(1). -/
theorem autoref_nat_zero : ((0 : ℕ), (0 : ℕ)) ∈ natRel := rfl

/-- The source's `autoref_nat`(3). -/
theorem autoref_nat_one : ((1 : ℕ), (1 : ℕ)) ∈ natRel := rfl

/-- The source's `autoref_nat`(2). -/
@[param] theorem autoref_nat_succ : (Nat.succ, Nat.succ) ∈ natRel →ᵣ natRel :=
  funRel_diagonal_self _

/-- The source's `autoref_nat`(5), `decide`d (delta PM8). -/
@[param] theorem autoref_nat_lt :
    ((fun a b : ℕ => decide (a < b)), (fun a b : ℕ => decide (a < b))) ∈
      natRel →ᵣ natRel →ᵣ boolRel :=
  funRel_diagonal_self₂ _

/-- The source's `autoref_nat`(6), `decide`d (delta PM8). -/
@[param] theorem autoref_nat_le :
    ((fun a b : ℕ => decide (a ≤ b)), (fun a b : ℕ => decide (a ≤ b))) ∈
      natRel →ᵣ natRel →ᵣ boolRel :=
  funRel_diagonal_self₂ _

/-- The source's `autoref_nat`(7), `decide`d (delta PM8). -/
@[param] theorem autoref_nat_eq :
    ((fun a b : ℕ => decide (a = b)), (fun a b : ℕ => decide (a = b))) ∈
      natRel →ᵣ natRel →ᵣ boolRel :=
  funRel_diagonal_self₂ _

/-- The source's `autoref_nat`(8). -/
@[param] theorem autoref_nat_add :
    ((fun a b : ℕ => a + b), (fun a b : ℕ => a + b)) ∈ natRel →ᵣ natRel →ᵣ natRel :=
  funRel_diagonal_self₂ _

/-- The source's `autoref_nat`(9). -/
@[param] theorem autoref_nat_sub :
    ((fun a b : ℕ => a - b), (fun a b : ℕ => a - b)) ∈ natRel →ᵣ natRel →ᵣ natRel :=
  funRel_diagonal_self₂ _

/-- The source's `autoref_nat`(10). -/
@[param] theorem autoref_nat_div :
    ((fun a b : ℕ => a / b), (fun a b : ℕ => a / b)) ∈ natRel →ᵣ natRel →ᵣ natRel :=
  funRel_diagonal_self₂ _

/-- The source's `autoref_nat`(11). -/
@[param] theorem autoref_nat_mul :
    ((fun a b : ℕ => a * b), (fun a b : ℕ => a * b)) ∈ natRel →ᵣ natRel →ᵣ natRel :=
  funRel_diagonal_self₂ _

/-- The source's `autoref_nat`(12). -/
@[param] theorem autoref_nat_mod :
    ((fun a b : ℕ => a % b), (fun a b : ℕ => a % b)) ∈ natRel →ᵣ natRel →ᵣ natRel :=
  funRel_diagonal_self₂ _

/-- The `Prop`-valued twin of the generic layer's equality rule, kept
because delta PM8's `decide` form is not the only equality a Lean goal
can present. -/
theorem param_prop_eq :
    ((fun a b : α => a = b), (fun a b : α => a = b)) ∈
      Set.diagonal α →ᵣ Set.diagonal α →ᵣ Set.diagonal Prop :=
  funRel_diagonal_self₂ _

/-! ### The `Let`-tagging helpers (`Param_Tool.thy`)

Ported at `letFun`, the constant behind `have x := v; …`; Lean's `let`
binder is zeta-reducible and needs no rule (delta PM12). -/

/-- The source's `tagged_fun_relD_both`. -/
theorem tagged_fun_relD_both {A : Set (α × β)} {B : Set (γ × δ)}
    {f : α → γ} {f' : β → δ} (hf : (f, f') ∈ A →ᵣ B)
    {x : α} {x' : β} (hx : (x, x') ∈ A) :
    (letFun x f, letFun x' f') ∈ B := hf x x' hx

/-- The source's `tagged_fun_relD_rhs`. -/
theorem tagged_fun_relD_rhs {A : Set (α × β)} {B : Set (γ × δ)}
    {f : α → γ} {f' : β → δ} (hf : (f, f') ∈ A →ᵣ B)
    {x : α} {x' : β} (hx : (x, x') ∈ A) :
    (f x, letFun x' f') ∈ B := hf x x' hx

/-- The source's `tagged_fun_relD_lhs`. -/
theorem tagged_fun_relD_lhs {A : Set (α × β)} {B : Set (γ × δ)}
    {f : α → γ} {f' : β → δ} (hf : (f, f') ∈ A →ᵣ B)
    {x : α} {x' : β} (hx : (x, x') ∈ A) :
    (letFun x f, f' x') ∈ B := hf x x' hx

/-- The source's `tagged_fun_relD_none` — `fun_relD` itself, under the
name the source's `Let`-tagging dispatch uses. -/
theorem tagged_fun_relD_none {A : Set (α × β)} {B : Set (γ × δ)}
    {f : α → γ} {f' : β → δ} (hf : (f, f') ∈ A →ᵣ B)
    {x : α} {x' : β} (hx : (x, x') ∈ A) :
    (f x, f' x') ∈ B := hf x x' hx

/-! ### `list_eq` and the structural-expansion route

Extract §3's showcase of the tagging/solver discipline: `(=)` on lists
is *proved equal to* `list_eq (=)`, and `list_eq` is what carries the
parametricity rule — so list equality refines without any equality
requirement on the element type. -/

/-- The source's `list_eq`, clause for clause. -/
def list_eq (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: l, a' :: l' => if eq a a' then list_eq eq l l' else false
  | _, _ => false

@[simp] theorem list_eq_nil_nil (eq : α → α → Bool) :
    list_eq eq [] [] = true := rfl

@[simp] theorem list_eq_cons_cons (eq : α → α → Bool) (a a' : α) (l l' : List α) :
    list_eq eq (a :: l) (a' :: l') = (if eq a a' then list_eq eq l l' else false) := rfl

@[simp] theorem list_eq_nil_cons (eq : α → α → Bool) (a' : α) (l' : List α) :
    list_eq eq [] (a' :: l') = false := rfl

@[simp] theorem list_eq_cons_nil (eq : α → α → Bool) (a : α) (l : List α) :
    list_eq eq (a :: l) [] = false := rfl

/-- The source's `autoref_list_eq_aux`: `list_eq` is parametric in `R`,
with its equality argument related pointwise. Note that the conclusion
is `Id`-relatedness of two `Bool`s — the two runs agree. -/
theorem autoref_list_eq_aux {R : Set (α × β)} :
    ((list_eq : (α → α → Bool) → List α → List α → Bool),
      (list_eq : (β → β → Bool) → List β → List β → Bool)) ∈
      (R →ᵣ R →ᵣ boolRel) →ᵣ listRel R →ᵣ listRel R →ᵣ boolRel := by
  rintro eq eq' heq l₁ l₁' h₁
  rw [mem_listRel_iff] at h₁
  induction h₁ with
  | nil =>
    rintro l₂ l₂' h₂
    rw [mem_listRel_iff] at h₂
    cases h₂ with
    | nil => exact rfl
    | cons _ _ => exact rfl
  | cons hx _ ih =>
    rintro l₂ l₂' h₂
    rw [mem_listRel_iff] at h₂
    cases h₂ with
    | nil => exact rfl
    | cons hy h' =>
      have hb : eq _ _ = eq' _ _ := heq _ _ hx _ _ hy
      show (if eq _ _ then _ else _) = (if eq' _ _ then _ else _)
      rw [hb]
      split
      · exact ih _ _ (mem_listRel_iff.mpr h')
      · rfl

/-- `list_eq` at decidable equality computes decidable equality; the
pointwise form of `list_eq_expand`. -/
theorem list_eq_decide [DecidableEq α] : ∀ l l' : List α,
    list_eq (fun a a' => decide (a = a')) l l' = decide (l = l')
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | a :: l, a' :: l' => by
    rw [list_eq_cons_cons, list_eq_decide l l']
    by_cases h : a = a'
    · subst h; simp
    · simp [h]

/-- The source's `list_eq_expand`, at the `decide` form of list equality
(delta PM8). **The source tags this `[autoref_struct_expand]`**; that
attribute is the translate phase's structural-expansion database, which
is wave C's — the tag is deferred, and this comment is its marker
(delta PM10). -/
theorem list_eq_expand [DecidableEq α] :
    (fun l l' : List α => decide (l = l')) = list_eq (fun a a' : α => decide (a = a')) := by
  funext l l'
  exact (list_eq_decide l l').symm

/-! ### The `parametricity` tactic

Design record §3 (`named_theorems → persistent attribute + DiscrTree`)
and §10 default 3. The `@[param]` attribute itself is declared in
`Autoref/Attrs.lean` — a Lean attribute is unavailable to its own
defining module, which is why wave A put it there and why this file can
both tag its rules and read the database back.

**PM14 — the tactic is a seed, not the source's method.** What it does,
per step, on the first goal: try `assumption`; then, for each
*arity adjustment* `k = 0, 1, …, 4` in turn, try every rule — the ones
named at the call site first, then the `@[param]` database — applied as
`fun_relD (fun_relD … rule)` `k` times, which is exactly the source's
"arity adjustment via `fun_relI`/`fun_relD`"; then, at a goal whose
relation is a `funRel`, try `fun_relI`. `parametricity` repeats that,
interleaved with a binder-peeling step, over all goals.

What it does *not* do, all of which the source's `parametricity` does:
no `Item_Net`/DiscrTree indexing — rules are scanned linearly and the
first match wins, so a rule whose conclusion unifies with a goal whose
relation is still a metavariable can commit the wrong relation (this is
what keying on the goal's `rhs_head` constant prevents, and it is why
`IdI` above is deliberately untagged); no `param_fo` (the source's
first-order rule conversion, `attribute_setup param_fo`); no
`to_relAPP` (there is no `relAPP` — wave A delta R1); no `del` half of
the attribute (`del_dflt_attr`); no `Let`-tag dispatch — the four
`tagged_fun_relD_*` helpers are ported but the tactic does not choose
between them, so a `letFun` goal needs the right one named at the call
site (demonstrated in the gate); and no failure message naming the
unsolved subgoal's head constant. Like `refine_vcg` (P1's precedent), it
is a `repeat'` and therefore *leaves* what it cannot do as goals rather
than failing, where the source's method fails. Rules are tried at
arities 0–4, which covers every rule in this file; a longer rule would
need the bound raised. -/

namespace Param

open Lean Elab Tactic Meta in
/-- Run a tactic, restoring the state and reporting `false` if it
fails. -/
private def try? (stx : TSyntax `tactic) : TacticM Bool := do
  let st ← saveState
  try
    evalTactic stx
    pure true
  catch _ =>
    restoreState st
    pure false

/-- The highest arity adjustment `parametricity_step` tries; every rule
in this file is within it. -/
def maxArity : Nat := 4

open Lean Elab Tactic Meta in
/-- One step of `parametricity`: `assumption`, then the rules (call-site
rules first, then the `@[param]` database) at increasing arity
adjustment, then `fun_relI`. -/
def stepCore (extra : Array Lean.Name) : TacticM Unit := do
  if ← try? (← `(tactic| assumption)) then return
  let names := extra ++ (← labelled `param)
  for k in [0:maxArity + 1] do
    for n in names do
      let mut t : Term := mkIdent n
      for _ in [0:k] do
        t ← `($(mkIdent ``fun_relD) $t)
      if ← try? (← `(tactic| apply $t)) then return
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  if ty.getAppArgs.any fun a => a.getAppFn.isConstOf ``funRel then
    if ← try? (← `(tactic| apply $(mkIdent ``fun_relI))) then return
  throwError "parametricity: no rule applies to this goal"

end Param

/-- One step of the `parametricity` tactic; `parametricity_step [r₁, r₂]`
tries the named rules before the `@[param]` database, which is the
source's `parametricity (add: …)`. -/
syntax (name := parametricityStep) "parametricity_step" (" [" ident,+ "]")? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| parametricity_step) => Param.stepCore #[]
  | `(tactic| parametricity_step [$rs,*]) => do
    Param.stepCore (← rs.getElems.mapM fun i => realizeGlobalConstNoOverload i)

open Lean Elab Tactic Meta in
/-- Peel one binder, but only when the goal is *syntactically* a
quantifier — the guard `refine_vcg_intro` uses, for the same reason
(membership in a relator is a `∀` under its own name, and unfolding it
by accident loses the rule format). -/
elab "parametricity_intro" : tactic => do
  let goal ← getMainGoal
  match ← instantiateMVars (← goal.getType) with
  | .forallE .. => let (_, g) ← goal.intro1; replaceMainGoal [g]
  | _ => throwError "parametricity: the goal is not a quantifier"

/-- The source's `parametricity` proof method, seed version: apply
parametricity rules until nothing matches, leaving the rest as goals.
`parametricity [r₁, r₂]` is the source's `parametricity (add: r₁ r₂)`. -/
syntax (name := parametricityTac) "parametricity" (" [" ident,+ "]")? : tactic

macro_rules
  | `(tactic| parametricity) =>
    `(tactic| repeat' (first | parametricity_step | parametricity_intro))
  | `(tactic| parametricity [$rs,*]) =>
    `(tactic| repeat' (first | parametricity_step [$rs,*] | parametricity_intro))

/-! ### The executable gate (design record ledger D4)

Every rule above is a statement about *values*, so at concrete data it
runs. The working relation is `halfRel = br (·/2) (· % 2 = 0)` —
a concrete `n` stands for the abstract `n / 2`, and odd concrete values
are related to nothing. It is deliberately neither the identity nor
total: a check about a rule's conclusion then has content, and a check
that violates a rule's premise is visibly rejected. Each rule gets at
least one positive check and the section as a whole runs well over two
negative controls.

`listRel`/`optionRel` at `halfRel` carry no decidability instance
(`List.Forall₂` has none), so they go through executable twins with
*proved* agreement — the wave A pattern — which is what makes a `#guard`
here a `#guard` about `listRel`/`optionRel` themselves.

Naming note: this gate shares the namespace `Lax13Proofs.Refine.Sanity`
with the gates of `Relators.lean`, `DataRefinement.lean` and the NREST
files, none of which may be edited; every name below is fresh. -/

namespace Sanity

open Plausible

/-- Membership in `Set.diagonal` is decidable at a decidable carrier —
this is what makes the `natRel`/`boolRel` checks below checks about the
relators themselves. -/
instance instDecidableMemDiagonal [DecidableEq α] (p : α × α) :
    Decidable (p ∈ Set.diagonal α) :=
  inferInstanceAs (Decidable (p.1 = p.2))

/-- The gate's working relation: `br` at halving, with evenness as the
concrete-side invariant. -/
def halfRel : Set (ℕ × ℕ) := br (fun n => n / 2) (fun n => n % 2 = 0)

/-- Executable `halfRel`. -/
def halfB (c a : ℕ) : Bool := c % 2 == 0 && a == c / 2

/-- **The bridge for `halfRel`.** -/
theorem halfB_eq (c a : ℕ) : halfB c a = true ↔ (c, a) ∈ halfRel := by
  simp only [halfB, halfRel, mem_br_iff, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Executable `listRel` at a decidable relation on `ℕ`. -/
def listRelN (R : ℕ → ℕ → Bool) : List ℕ → List ℕ → Bool
  | [], [] => true
  | c :: cs, a :: as => R c a && listRelN R cs as
  | _, _ => false

@[simp] theorem listRelN_nil_nil (R : ℕ → ℕ → Bool) : listRelN R [] [] = true := rfl

@[simp] theorem listRelN_cons_cons (R : ℕ → ℕ → Bool) (c a : ℕ) (cs as : List ℕ) :
    listRelN R (c :: cs) (a :: as) = (R c a && listRelN R cs as) := rfl

@[simp] theorem listRelN_nil_cons (R : ℕ → ℕ → Bool) (a : ℕ) (as : List ℕ) :
    listRelN R [] (a :: as) = false := rfl

@[simp] theorem listRelN_cons_nil (R : ℕ → ℕ → Bool) (c : ℕ) (cs : List ℕ) :
    listRelN R (c :: cs) [] = false := rfl

/-- **The bridge for `listRel`.** -/
theorem listRelN_eq {R : ℕ → ℕ → Bool} {S : Set (ℕ × ℕ)}
    (h : ∀ c a, R c a = true ↔ (c, a) ∈ S) : ∀ l l' : List ℕ,
    listRelN R l l' = true ↔ (l, l') ∈ listRel S
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, a :: as => by
    simp only [listRelN_cons_cons, Bool.and_eq_true, mem_listRel_cons, h,
      listRelN_eq h cs as]

/-- Executable `optionRel` at a decidable relation on `ℕ`. -/
def optionRelN (R : ℕ → ℕ → Bool) : Option ℕ → Option ℕ → Bool
  | none, none => true
  | some c, some a => R c a
  | _, _ => false

/-- **The bridge for `optionRel`.** -/
theorem optionRelN_eq {R : ℕ → ℕ → Bool} {S : Set (ℕ × ℕ)}
    (h : ∀ c a, R c a = true ↔ (c, a) ∈ S) : ∀ x x' : Option ℕ,
    optionRelN R x x' = true ↔ (x, x') ∈ optionRel S
  | none, none => by simp [optionRelN]
  | none, some _ => by simp [optionRelN]
  | some _, none => by simp [optionRelN]
  | some c, some a => by simp only [optionRelN, h, mem_optionRel_some_some]

/-- `listRel halfRel`, executably. -/
abbrev listHalf : List ℕ → List ℕ → Bool := listRelN halfB

/-- **The bridge actually used below**: a `#guard` about `listHalf` is a
`#guard` about `listRel halfRel`. -/
theorem listHalf_eq (l l' : List ℕ) : listHalf l l' = true ↔ (l, l') ∈ listRel halfRel :=
  listRelN_eq halfB_eq l l'

/-- `optionRel halfRel`, executably. -/
abbrev optionHalf : Option ℕ → Option ℕ → Bool := optionRelN halfB

/-- **The bridge actually used below**: a `#guard` about `optionHalf` is
a `#guard` about `optionRel halfRel`. -/
theorem optionHalf_eq (x x' : Option ℕ) :
    optionHalf x x' = true ↔ (x, x') ∈ optionRel halfRel :=
  optionRelN_eq halfB_eq x x'

/-! #### `param_if` / `param_ite` -/

-- related conditions and related branches give related results …
#guard halfB (cond true 4 6) (cond true 2 3)
#guard halfB (cond false 4 6) (cond false 2 3)
#guard halfB (if 2 < 3 then 4 else 6) (if 2 < 3 then 2 else 3)
-- … and unrelated conditions do not (the `(c,c') ∈ Id` premise)
#guard ! halfB (cond true 4 6) (cond false 2 3)
-- … nor does an unrelated branch (the branch premises)
#guard ! halfB (cond true 5 6) (cond true 2 3)

/-! #### `param_option`, `autoref_is_None` -/

#guard optionHalf (some 4) (some 2)
#guard optionHalf none none
#guard ! optionHalf (some 5) (some 2)          -- invariant fails
#guard ! optionHalf (some 4) (some 3)          -- abstraction fails
#guard ! optionHalf none (some 2)              -- constructors disagree

-- `param_option_cases` / `param_option_rec`: relatedness travels
-- through both eliminators.
#guard halfB (Option.casesOn (some 4) 0 fun c => c + 2)
  (Option.casesOn (some 2) 0 fun a => a + 1)
#guard halfB (Option.rec 0 (fun c => c + 2) (some 4))
  (Option.rec 0 (fun a => a + 1) (some 2))
#guard halfB (Option.rec 0 (fun c => c + 2) none) (Option.rec 0 (fun a => a + 1) none)
#guard ! halfB (Option.rec 0 (fun c => c + 3) (some 4))
  (Option.rec 0 (fun a => a + 1) (some 2))     -- unrelated `some` branch

-- `autoref_is_None`: related options agree on `isNone`, unrelated ones
-- need not.
#guard Option.isNone (some 4) == Option.isNone (some 2)
#guard Option.isNone (none : Option ℕ) == Option.isNone (none : Option ℕ)
#guard ! (Option.isNone (none : Option ℕ) == Option.isNone (some 2))

/-! #### `param_map`, `param_fold`, `autoref_append`, `refine_list`,
`autoref_is_Nil` -/

#guard listHalf [0, 2, 4] [0, 1, 2]
#guard ! listHalf [0, 3, 4] [0, 1, 2]          -- odd concrete element
#guard ! listHalf [0, 2] [0, 1, 2]             -- lengths disagree

-- `param_map` at the related pair `(· + 2, · + 1)`
#guard listHalf (List.map (fun c => c + 2) [0, 2, 4]) (List.map (fun a => a + 1) [0, 1, 2])
#guard ! listHalf (List.map (fun c => c + 1) [0, 2, 4]) (List.map (fun a => a + 1) [0, 1, 2])

-- `param_fold_foldr` / `param_fold_foldl`: `(+)` is related to itself,
-- and so are the initial values
#guard halfB (List.foldr (fun c s => c + s) 0 [2, 4, 6])
  (List.foldr (fun a s => a + s) 0 [1, 2, 3])
#guard halfB (List.foldl (fun s c => s + c) 0 [2, 4, 6])
  (List.foldl (fun s a => s + a) 0 [1, 2, 3])
#guard ! halfB (List.foldr (fun c s => c + s) 1 [2, 4, 6])
  (List.foldr (fun a s => a + s) 0 [1, 2, 3])  -- unrelated initial value

-- `autoref_append`, `refine_list_cons`, `refine_list_nil`
#guard listHalf ([2, 4] ++ [6]) ([1, 2] ++ [3])
#guard listHalf (2 :: [4, 6]) (1 :: [2, 3])
#guard listHalf [] []
#guard ! listHalf ([2, 4] ++ [6]) ([1, 2] ++ [4])

-- `refine_list_cases`
#guard halfB (List.casesOn [2, 4] 0 fun c _ => c + 2)
  (List.casesOn [1, 2] 0 fun a _ => a + 1)
#guard halfB (List.casesOn ([] : List ℕ) 0 fun c _ => c + 2)
  (List.casesOn ([] : List ℕ) 0 fun a _ => a + 1)

-- `autoref_is_Nil`
#guard List.isEmpty [2, 4] == List.isEmpty [1, 2]
#guard List.isEmpty ([] : List ℕ) == List.isEmpty ([] : List ℕ)
#guard ! (List.isEmpty ([] : List ℕ) == List.isEmpty [1])

/-! #### `param_case_prod''`, `param_rec_nat`, the `nat` bindings -/

#guard halfB (Prod.rec (motive := fun _ => ℕ) (fun a b => a + b) (2, 4))
  (Prod.rec (motive := fun _ => ℕ) (fun a b => a + b) (1, 2))
#guard ! halfB (Prod.rec (motive := fun _ => ℕ) (fun a b => a + b) (2, 5))
  (Prod.rec (motive := fun _ => ℕ) (fun a b => a + b) (1, 2))

-- `param_rec_nat`: related zero cases, related step functions, equal
-- indices
#guard halfB (Nat.rec 4 (fun _ ih => ih + 2) 3) (Nat.rec 2 (fun _ ih => ih + 1) 3)
#guard ! halfB (Nat.rec 4 (fun _ ih => ih + 3) 3) (Nat.rec 2 (fun _ ih => ih + 1) 3)
#guard ! halfB (Nat.rec 5 (fun _ ih => ih + 2) 3) (Nat.rec 2 (fun _ ih => ih + 1) 3)

-- the `nat` layer is `Id`: related means equal
#guard ((4 : ℕ), (4 : ℕ)) ∈ natRel
#guard ! (((4 : ℕ), (5 : ℕ)) ∈ natRel)
#guard (decide ((2 : ℕ) < 3), decide ((2 : ℕ) < 3)) ∈ boolRel
#guard ((2 : ℕ) + 3, (2 : ℕ) + 3) ∈ natRel

/-! #### The `Let`-tagging helpers -/

#guard halfB (letFun 4 fun x => x + 2) (letFun 2 fun x => x + 1)
#guard halfB (letFun 4 fun x => x + 2) ((fun x => x + 1) 2)
#guard ! halfB (letFun 5 fun x => x + 2) (letFun 2 fun x => x + 1)

/-! #### `list_eq` -/

#guard list_eq (fun a b : ℕ => decide (a = b)) [1, 2, 3] [1, 2, 3]
#guard ! list_eq (fun a b : ℕ => decide (a = b)) [1, 2] [2, 1]
#guard ! list_eq (fun a b : ℕ => decide (a = b)) [1] [1, 1]
-- the equality argument really is a parameter
#guard list_eq (fun _ _ : ℕ => true) [1, 2] [3, 4]
#guard ! list_eq (fun _ _ : ℕ => false) [1] [1]

-- `list_eq_expand`
#guard list_eq (fun a b : ℕ => decide (a = b)) [1, 2, 3] [1, 2, 3] = decide ([1, 2, 3] = [1, 2, 3])
#guard list_eq (fun a b : ℕ => decide (a = b)) [1, 2] [2, 3] = decide ([1, 2] = [2, 3])

-- `autoref_list_eq_aux` at `halfRel`: the concrete run with the
-- concrete equality agrees with the abstract run with the abstract one
#guard list_eq (fun c c' : ℕ => decide (c / 2 = c' / 2)) [0, 2, 4] [0, 2, 4]
  == list_eq (fun a a' : ℕ => decide (a = a')) [0, 1, 2] [0, 1, 2]
#guard list_eq (fun c c' : ℕ => decide (c / 2 = c' / 2)) [0, 2] [2, 0]
  == list_eq (fun a a' : ℕ => decide (a = a')) [0, 1] [1, 0]
-- an *unrelated* equality argument breaks the conclusion
#guard ! (list_eq (fun _ _ : ℕ => false) [0, 2] [0, 2]
  == list_eq (fun a a' : ℕ => decide (a = a')) [0, 1] [0, 1])

/-! #### Property checks

The rules at sampled data, run through the bridges above. -/

-- `param_map`
#test ∀ l : List ℕ, listHalf (List.map (fun c => c + 2) (List.map (fun a => 2 * a) l))
  (List.map (fun a => a + 1) l) = true

-- `param_fold_foldr` and `param_fold_foldl`
#test ∀ l : List ℕ, halfB (List.foldr (fun c s => c + s) 0 (List.map (fun a => 2 * a) l))
  (List.foldr (fun a s => a + s) 0 l) = true

#test ∀ l : List ℕ, halfB (List.foldl (fun s c => s + c) 0 (List.map (fun a => 2 * a) l))
  (List.foldl (fun s a => s + a) 0 l) = true

-- `autoref_append` with `refine_list_nil`/`_cons`
#test ∀ l l' : List ℕ, listHalf (List.map (fun a => 2 * a) l ++ List.map (fun a => 2 * a) l')
  (l ++ l') = true

-- `param_rec_nat`
#test ∀ n : ℕ, halfB (Nat.rec 4 (fun _ ih => ih + 2) n) (Nat.rec 2 (fun _ ih => ih + 1) n) = true

-- `param_option_rec` and `autoref_is_None`
#test ∀ o : Option ℕ, halfB (Option.rec 0 (fun c => c + 2) (Option.map (fun a => 2 * a) o))
  (Option.rec 0 (fun a => a + 1) o) = true

#test ∀ o : Option ℕ,
  (Option.isNone (Option.map (fun a => 2 * a) o) == Option.isNone o) = true

-- `autoref_is_Nil`
#test ∀ l : List ℕ, (List.isEmpty (List.map (fun a => 2 * a) l) == List.isEmpty l) = true

-- `autoref_list_eq_aux`: the two runs agree on related inputs
#test ∀ l l' : List ℕ,
  (list_eq (fun c c' => decide (c / 2 = c' / 2)) (List.map (fun a => 2 * a) l)
      (List.map (fun a => 2 * a) l')
    == list_eq (fun a a' : ℕ => decide (a = a')) l l') = true

-- `list_eq_expand`
#test ∀ l l' : List ℕ, list_eq (fun a a' : ℕ => decide (a = a')) l l' = decide (l = l')

/-! #### The tactic, end to end

`parametricity` alone — no manual rule application, no `intro`, no
`simp` — on goals of the shapes the acceptance example is built from. -/

-- (a) a composite `List.map` goal, with the element relation abstract
example {R : Set (α × β)} {S : Set (γ × δ)} (f : α → γ) (f' : β → δ)
    (hf : (f, f') ∈ R →ᵣ S) :
    (List.map f, List.map f') ∈ listRel R →ᵣ listRel S := by
  parametricity

-- (a′) the same shape at concrete relators, with the mapped function
-- itself needing the rule database (`append`, `cons`, `nil`, literals)
example :
    ((List.map fun l => l ++ [1]), (List.map fun l => l ++ [1])) ∈
      listRel (listRel natRel) →ᵣ listRel (listRel natRel) := by
  parametricity

-- (b) the P2 acceptance example's parametric core: the source's
-- `schematic_goal "(?f::?'c,[1,2,3]@[4::nat])∈?R" by autoref`, with the
-- relator given rather than synthesised (synthesis is wave C's phase
-- pipeline; the parametricity half is this wave's)
example : (([1, 2, 3] ++ [4] : List ℕ), ([1, 2, 3] ++ [4] : List ℕ)) ∈ listRel natRel := by
  parametricity

-- the option half of the same example list
example {R : Set (α × β)} (x : α) (x' : β) (hx : (x, x') ∈ R) :
    ((some x, some x') ∈ optionRel R) := by
  parametricity

example {R : Set (α × β)} (o : Option α) (o' : Option β) (ho : (o, o') ∈ optionRel R) :
    ((Option.isNone o, Option.isNone o') ∈ boolRel) := by
  parametricity

-- an eliminator goal: `param_option_cases` at arity 3
example {R : Set (α × β)} {Rr : Set (γ × δ)} (x : Option α) (x' : Option β)
    (hx : (x, x') ∈ optionRel R) (n : γ) (n' : δ) (hn : (n, n') ∈ Rr)
    (s : α → γ) (s' : β → δ) (hs : (s, s') ∈ R →ᵣ Rr) :
    (Option.casesOn x n s, Option.casesOn x' n' s') ∈ Rr := by
  parametricity

-- a nested goal that needs `fun_relI` and the binder-peeling step
example : ((fun n : ℕ => n + 1), (fun n : ℕ => n + 1)) ∈ natRel →ᵣ natRel := by
  parametricity

-- the `Let`-tagging helpers, which the tactic does not dispatch on its
-- own (PM14): named at the call site, they close a `letFun` goal
example {A : Set (α × β)} {B : Set (γ × δ)} (f : α → γ) (f' : β → δ)
    (hf : (f, f') ∈ A →ᵣ B) (x : α) (x' : β) (hx : (x, x') ∈ A) :
    (letFun x f, letFun x' f') ∈ B := by
  parametricity [tagged_fun_relD_both]

-- the call-site rule list, the source's `parametricity (add: …)`: this
-- is `autoref_list_eq`'s own proof, minus its `GEN_OP` premise (PM13)
example {R : Set (α × β)} (eq : α → α → Bool) (eq' : β → β → Bool)
    (heq : (eq, eq') ∈ R →ᵣ R →ᵣ boolRel) :
    (list_eq eq, list_eq eq') ∈ listRel R →ᵣ listRel R →ᵣ boolRel := by
  parametricity [autoref_list_eq_aux]

end Sanity

end Lax13Proofs.Refine
