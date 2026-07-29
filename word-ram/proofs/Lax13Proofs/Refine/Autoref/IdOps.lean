import Lax13Proofs.Refine.Autoref.Phases
import Lax13Proofs.Refine.Autoref.Relators

/-!
Phases one and two: operation identification (`id_op`, priority 10) and
relator inference (`rel_inf`, priority 20).

Port of `thys/Automatic_Refinement/Tool/Autoref_Id_Ops.thy` of AFP
`Automatic_Refinement` (Lammich) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 — AFP for Isabelle2025-2,
release 2026-02-06. The verbatim source text this file is checked
against is `plans/word-ram/refinement-tower/p2-tool-extracts.md` §1
(§1.1 the interface-application syntax, §1.2 the `ID_OP` calculus, §1.3
the three databases, §1.4 `id_tac` and `id_phase`, §1.5 the whole
`Autoref_Rel_Inf` structure and `roi_phase`). The interface *layer*
itself (`Interface`, `intfAPP`, `i_fun`, `CONST_INTF`, `ID_OP`) landed
in wave B2's `Autoref/Tagging.lean`; this file is everything the extract
records beyond it.

What the two phases do, in the extract's own summary:

> `id_op` (`Autoref_Id_Ops.id_phase`) takes the raw goal `(?f,a)∈?R` and
> rewrites `a` into a fully `OP`/`APP`-tagged, interface-typed
> `ID_OP a a' I` term, consulting `autoref_itype` for declared interface
> types and `autoref_op_pat`/`autoref_op_pat_def` to rewrite surface
> operators before falling back to generic constant/application/
> abstraction identification. […] `rel_inf` (`Autoref_Rel_Inf.roi_phase`)
> turns the interfaces fixed in step 1 into a schematic relator skeleton
> for `?R` (`REL_OF_INTF`/`CNV_ANNOT`, consulting
> `autoref_rel_indirect`); for all three acceptance examples, which use
> only built-in `Id`/`nat_rel`/`list_rel`/`option_rel`, this phase does
> essentially no work.

## The source, verbatim

§1.1, the interface-annotation surface:

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

§1.2, the `ID_OP` calculus:

```isabelle
lemma ID_abs: ‹Tag abs first›
  "⟦ ⋀x. ID_OP x x I1 ⟹ ID_OP (f x) (f' x) I2 ⟧
  ⟹ ID_OP (λ'x. f x) (λ'x. f' x) (I1→⇩iI2)"

lemma ID_app: ‹Tag app first›
  "⟦ INDEP I1; ID_OP x x' I1; ID_OP f f' (I1→⇩iI2) ⟧
  ⟹ ID_OP (f$x) (f'$x') I2"

lemma ID_const: ‹Only if c is constant or free variable›
  "⟦ c ::⇩i I ⟧ ⟹ ID_OP c (OP c :::⇩i I) I"

definition [simp]: "ID_TAG x ≡ x"
lemma ID_const_any: ‹Only if no typing for constant exists›
  "ID_OP c (OP (ID_TAG c) :::⇩i I) I"

lemma ID_const_check_known: "⟦ c ::⇩i I' ⟧ ⟹ ID_OP c c I"

lemma ID_tagged_OP: ‹Try first›  "ID_OP (OP f :::⇩i I) (OP f :::⇩i I) I"
lemma ID_is_tagged_OP: "ID_OP (OP c) t' I ⟹ ID_OP (OP c) t' I"
lemma ID_tagged_OP_no_annot: "c ::⇩i I ⟹ ID_OP (OP c) (OP c :::⇩i I) I"
lemmas ID_tagged = ID_tagged_OP ID_abs ID_app

lemma ID_annotated: ‹Try second›
  "ID_OP t t' I ⟹ ID_OP (t :::⇩i I) t' I"
  "ID_OP t t' I ⟹ ID_OP (ANNOT t A) (ANNOT t' A) I"

lemma ID_init:
  assumes "ID_OP a a' I"  assumes "(c,a')∈R"  shows "(c,a)∈R"

lemma itypeI: "(c::'t) ::⇩i I"
```

§1.5, `Autoref_Rel_Inf`:

```isabelle
definition IND_FACT :: "rel_name ⇒ ('c × 'a) set ⇒ bool" ("#_=_" 10)
  where [simp]: "#name=R ≡ True"
lemma REL_INDIRECT: "#name=R" by simp

definition CNV_ANNOT :: "'a ⇒ 'a ⇒ (_×'a) set ⇒ bool"
  where [simp]: "CNV_ANNOT t t' R ≡ t=t'"

definition REL_OF_INTF :: "interface ⇒ ('c×'a) set ⇒ bool"
  where [simp]: "REL_OF_INTF I R ≡ True"
definition [simp]: "REL_OF_INTF_P I R ≡ True" ‹Version to resolve relator arguments›

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

consts i_of_rel :: "'a ⇒ 'b"

lemma ROI_P_app: ‹Only if interface is really application›
  "REL_OF_INTF_P I R ⟹ REL_OF_INTF I R"
lemma ROI_app: ‹Only if interface is really application›
  "⟦ REL_OF_INTF I R; REL_OF_INTF_P J S ⟧ ⟹ REL_OF_INTF_P (⟨I⟩⇩iJ) (⟨R⟩S)"
lemma ROI_i_of_rel:
  "REL_OF_INTF_P (i_of_rel S) S"   "REL_OF_INTF (i_of_rel R) R"
lemma ROI_const:  "REL_OF_INTF_P J S"   "REL_OF_INTF I R"
lemma ROI_init:
  assumes "CNV_ANNOT a a' R"  assumes "(c,a')∈R"  shows "(c,a)∈R"
lemma REL_OF_INTF_I: "REL_OF_INTF I R"
```

and the two phase records:

```isabelle
val id_phase = {
  init = I,
  tac = (fn ctxt => Seq.INTERVAL (resolve_tac ctxt @{thms ID_init} THEN' id_tac ctxt)),
  analyze = id_analyze,
  pretty_failure = id_pretty_failure }

val roi_phase = {
  init = I,
  tac = (fn ctxt => Seq.INTERVAL (resolve_tac ctxt @{thms ROI_init} THEN' roi_tac ctxt)),
  analyze = roi_analyze,
  pretty_failure = roi_pretty_failure }
```

## Substrate deltas and departures, each flagged

**I1 — `INDEP` is absent.** Both `ID_app` and `CNV_ANNOT`(4) carry an
`INDEP` premise, discharged by `Indep_Vars.indep_tac` of
`Lib/Indep_Vars.thy` — a check that a schematic variable does not occur
in the parameters of its subgoal, i.e. pure Isabelle unification
hygiene. `Lib/Indep_Vars.thy` is not covered by any extract, the device
has no Lean counterpart (ledger class D1), and the two rules are ported
without it. Nothing downstream mentions `INDEP`.

**I2 — identification is a `MetaM` walk justified by one `rfl`, not a
resolution loop.** The source's `id_tac` is a recursive-descent
*tactic*: at each node it resolves against `ID_tagged` / `ID_const` /
`ID_app` / `ID_abs`, so the tagged term is built by the unifier and the
`ID_OP` fact by resolution. Here `idTerm` walks the term in `MetaM` and
the whole `ID_OP a a' I` fact is discharged at once — by the op-pat
rewrite's own equation composed with `rfl`, because in Lean `ID_OP t t' I`
*is* `t = t'` and the tags are `def`s the kernel unfolds. Two reasons,
both substrate: resolving `ID_app` backwards would ask Lean's unifier to
solve `?f $ᵃ ?x =?= f x`, which is exactly the flex-flex shape the tags
exist to avoid; and the source's own `ID_OP` facts are proved `by simp`
from the same definitional identity, so nothing is lost. The rules above
are ported anyway, in full: they are the specification `idTerm` walks
against, and a reader checking this port checks `idTerm`'s cases against
them one for one (`ID_app` ↦ the `APP` case, `ID_const` ↦ the leaf case,
`ID_annotated` ↦ the already-tagged case, `ID_abs` ↦ delta I6).

**I3 — the operator/argument split is by binder info.** HOL applies
everything uniformly, so the source's `ID_app`/`ID_const` split is
simply "is the head a constant". Lean's applications carry implicit,
instance and strict-implicit arguments, which are *part of the
operator*, not arguments to translate: `@List.append ℕ` is the operator
and `[1,2,3]`, `[4]` are its arguments. So `idTerm` splits an
application at the last non-explicit argument — everything up to and
including it belongs to the operator, the trailing explicit arguments
become the `$ᵃ` spine. This reproduces the source's own treatment of
numerals for free: `(4 : ℕ)` is `@OfNat.ofNat ℕ 4 inst`, whose explicit
argument is followed by an instance, so the split leaves no spine and
the literal is a leaf operator — which is exactly the status
`(numeral n::nat, numeral n::nat) ∈ nat_rel` gives it in the source.

**I4 — `decide (a = b)` is an operator occurrence.** HOL's `(=)` is a
constant of type `'a ⇒ 'a ⇒ bool`; Lean's `Bool`-valued equality is
`@decide (a = b) inst`, in which the operator does not appear as a
subterm at all. Wave B1 settled the spelling (delta PM8: comparisons are
`Bool`-valued through `decide`) and states its rules at
`fun a b : τ => decide (a = b)`; `idTerm` therefore recognises
`@decide (@Eq τ a b) inst` and re-forms it as that operator applied to
`a` and `b`, re-synthesising the instance and checking the result is
definitionally the term it started from. This is *identification*, which
is the phase's job, and it is why the operator position here may hold a
closed lambda where the source's holds a constant — the source's own
`OP` documentation ("Autoref does not look beyond this") is what makes
that harmless.

**I5 — interfaces are synthesized from the Lean type; `autoref_itype`
is consulted but empty.** The source's `id_typ` resolves the head
constant against the `autoref_itype` net and only falls back to
`ID_const_any` when no typing exists. Nothing in the acceptance scope
declares an interface type — the tutorial's own two uses are
`itypeI[where 't="'a::numeral" and I=i_std]`, and the extraction's Gaps
section establishes that `i_std` there "is **not declared anywhere** in
`Automatic_Refinement`… a bare schematic/free term variable standing in
for 'the standard/generic interface'". So `intfOfType` walks the Lean
type instead: a function type gives `→ᵢ`, a constant type `C a₁ … aₙ`
gives `⟨i_a₁⟩…⟨i_aₙ⟩i_c`, and anything the walk cannot decompose —
a type variable, a metavariable — gives exactly `i_std`, in the
placeholder sense the extraction found. The `autoref_itype` database is
still read first, so a declaration would win; none exists.

**I6 — `ID_abs` / abstraction is not implemented.** `idTerm` has no
`ABS` case: none of the eight tutorial entries contains a lambda, the
`GEN_OP` route instantiates operators rather than abstracting them, and
an untested `ABS` case would be a claim this wave has not earned. The
rule is ported, the walk stops at a lambda and reports it as an
unidentifiable operator naming the offending subterm, and the honest
gap is here. (`Autoref/Translate.lean` ports `autoref_ABS` for the same
reason and with the same status.)

**I7 — `autoref_op_pat_def` and `autoref_rel_indirect` are absent.**
Neither database is registered in wave B2's `Autoref/Attrs.lean`, which
is frozen for this wave; both are "bonus" rows of the extract's §9
registry table. `autoref_op_pat_def` (the "definitive" patterns that
must fire before anything else) has no consumer in the acceptance scope,
and `autoref_rel_indirect` is the `t ::# name` indirect-annotation route,
which nothing in the tutorial uses. Their absence is why `relSkeleton`
below has no lookup step (delta I8) and why `id_op` runs one op-pat net
rather than two.

**I8 — `rel_inf` synthesizes relator skeletons structurally, from the
type.** The source's `rel_of_intf_thm` builds a relator from an
interface: `i_fun`-application mirrors `relAPP`, an interface with a
registered `autoref_rel_intf`/`autoref_rel_indirect` binding becomes
that relator, and an unknown constant becomes a fresh `R_<name>`
schematic. With neither database registered (I7), every non-function
interface here is "unknown", so `relSkeleton` produces `→ᵣ` for a
function type and a fresh metavariable for everything else. This is the
source's own fallback path, not a weaker one — but it does mean
`rel_inf` cannot *choose* `⟨R⟩list_rel` for a list, and `fix_rel` fixes
that shape from the rule instead. The extract's summary already says
this phase "does essentially no work" for the acceptance examples; what
it does do is give every operator its own relator variable, which is
what `fix_rel` then solves for.

**I9 — `IND_FACT`'s `#_=_` notation is not ported**, for the reason
wave B2 gave for `⟨_⟩⇩i` (delta T5): the mixfix is not Lean-legal and
the constant is what the phases match on. `i_of_rel` is rendered like
`rel_annot` (delta T2): its argument lives in the application term, not
in the value.
-/

open Lean Meta Elab

universe u v w

namespace Lax13Proofs.Refine

/-! ### The interface annotation (`Autoref_Id_Ops.thy` §1.1) -/

/-- The source's `consts i_annot :: interface ⇒ annot`. Rendered like
wave B2's `rel_annot` (delta T2): the annotation value carries no
information, because the interface is present in the *application term*
`i_annot I`, which is where the phases read it. -/
def i_annot (_I : Interface) : Annot := .rel

/-- The source's
`abbreviation i_ANNOT :: 'a ⇒ interface ⇒ 'a (infixr ":::⇩i" 10)`,
`t:::⇩iI ≡ ANNOT t (i_annot I)`: "the term `t` has interface `I`". -/
abbrev i_ANNOT {α : Sort u} (t : α) (I : Interface) : α := ANNOT t (i_annot I)

@[inherit_doc] infixr:10 " :::ᵢ " => i_ANNOT

/-! ### The `ID_OP` calculus (`Autoref_Id_Ops.thy` §1.2)

Every rule below is the source's, statement for statement; every proof
is the source's `by simp` on a definitional identity. Delta I2 records
why the implementation walks against them rather than resolving them. -/

/-- The source's `definition [simp]: "ID_TAG x ≡ x"`: the marker
`ID_const_any` puts on an operator for which no interface type is
known. -/
def ID_TAG {α : Sort u} (x : α) : α := x

/-- The source's `ID_TAG` definition, with the source's own `[simp]`. -/
@[simp] theorem ID_TAG_def {α : Sort u} (x : α) : ID_TAG x = x := rfl

/-- The source's `ID_abs` ("Tag abs first"). -/
theorem ID_abs {α : Sort u} {β : Sort v} {I₁ I₂ : Interface} {f f' : α → β}
    (h : ∀ x, ID_OP x x I₁ → ID_OP (f x) (f' x) I₂) :
    ID_OP (ABS f) (ABS f') (I₁ →ᵢ I₂) := by
  have hf : f = f' := funext fun x => h x rfl
  show ABS f = ABS f'
  rw [hf]

/-- The source's `ID_app` ("Tag app first"), without its `INDEP`
premise (delta I1). -/
theorem ID_app {α : Sort u} {β : Sort v} {I₁ I₂ : Interface} {x x' : α} {f f' : α → β}
    (hx : ID_OP x x' I₁) (hf : ID_OP f f' (I₁ →ᵢ I₂)) :
    ID_OP (f $ᵃ x) (f' $ᵃ x') I₂ := by
  have hx' : x = x' := hx
  have hf' : f = f' := hf
  show f x = f' x'
  rw [hx', hf']

/-- The source's `ID_const` ("Only if c is constant or free
variable"). -/
theorem ID_const {α : Sort u} {c : α} {I : Interface} (_h : c ::ᵢ I) :
    ID_OP c (OP c :::ᵢ I) I := rfl

/-- The source's `ID_const_any` ("Only if no typing for constant
exists"). -/
theorem ID_const_any {α : Sort u} (c : α) (I : Interface) :
    ID_OP c (OP (ID_TAG c) :::ᵢ I) I := rfl

/-- The source's `ID_const_check_known`. -/
theorem ID_const_check_known {α : Sort u} {c : α} {I I' : Interface} (_h : c ::ᵢ I') :
    ID_OP c c I := rfl

/-- The source's `ID_tagged_OP` ("Try first"). -/
theorem ID_tagged_OP {α : Sort u} (f : α) (I : Interface) :
    ID_OP (OP f :::ᵢ I) (OP f :::ᵢ I) I := rfl

/-- The source's `ID_is_tagged_OP`. -/
theorem ID_is_tagged_OP {α : Sort u} {c t' : α} {I : Interface}
    (h : ID_OP (OP c) t' I) : ID_OP (OP c) t' I := h

/-- The source's `ID_tagged_OP_no_annot`. -/
theorem ID_tagged_OP_no_annot {α : Sort u} {c : α} {I : Interface} (_h : c ::ᵢ I) :
    ID_OP (OP c) (OP c :::ᵢ I) I := rfl

/-- The source's `ID_annotated`(1) ("Try second"). -/
theorem ID_annotated_intf {α : Sort u} {t t' : α} {I : Interface}
    (h : ID_OP t t' I) : ID_OP (t :::ᵢ I) t' I := h

/-- The source's `ID_annotated`(2). -/
theorem ID_annotated_any {α : Sort u} {t t' : α} {I : Interface} {A : Annot}
    (h : ID_OP t t' I) : ID_OP (ANNOT t A) (ANNOT t' A) I := h

/-- The source's `ID_init`: the rule the `id_op` phase resolves the goal
against, replacing the abstract term by its tagged form. -/
theorem ID_init {γ α : Type} {a a' : α} {I : Interface} {c : γ} {R : Set (γ × α)}
    (h₁ : ID_OP a a' I) (h₂ : (c, a') ∈ R) : (c, a) ∈ R := by
  have : a = a' := h₁
  rw [this]; exact h₂

/-- The source's `itypeI`, the lemma the tutorial's
`notes [autoref_itype] = itypeI[where 't="…" and I=i_std]`
instantiates. -/
theorem itypeI {α : Sort u} (c : α) (I : Interface) : c ::ᵢ I := trivial

/-! ### `Autoref_Rel_Inf` — the `rel_inf` phase's calculus
(`Autoref_Id_Ops.thy` §1.5) -/

/-- The source's `IND_FACT :: rel_name ⇒ ('c × 'a) set ⇒ bool`,
notation `#name=R` (not ported — delta I9): "the relator named `name`
is `R`", the fact the `autoref_rel_indirect` database holds. -/
def IND_FACT {γ α : Type} (_name : RelName) (_R : Set (γ × α)) : Prop := True

/-- The source's `IND_FACT` definition, with the source's own `[simp]`. -/
@[simp] theorem IND_FACT_def {γ α : Type} (name : RelName) (R : Set (γ × α)) :
    IND_FACT name R ↔ True := Iff.rfl

/-- The source's `REL_INDIRECT`. -/
theorem REL_INDIRECT {γ α : Type} (name : RelName) (R : Set (γ × α)) :
    IND_FACT name R := trivial

/-- The source's `CNV_ANNOT :: 'a ⇒ 'a ⇒ (_×'a) set ⇒ bool`,
`CNV_ANNOT t t' R ≡ t=t'`: "`t` has been re-annotated as `t'`, at
relator `R`" — the `rel_inf` phase's counterpart of `ID_OP`. -/
def CNV_ANNOT {γ α : Type} (t t' : α) (_R : Set (γ × α)) : Prop := t = t'

/-- The source's `CNV_ANNOT` definition, with the source's own `[simp]`. -/
@[simp] theorem CNV_ANNOT_def {γ α : Type} (t t' : α) (R : Set (γ × α)) :
    CNV_ANNOT t t' R ↔ t = t' := Iff.rfl

/-- The source's `REL_OF_INTF :: interface ⇒ ('c×'a) set ⇒ bool`: "the
relator for interface `I` is `R`", a declaration carrying no
information, as `CONST_INTF` is. -/
def REL_OF_INTF {γ α : Type} (_I : Interface) (_R : Set (γ × α)) : Prop := True

/-- The source's `REL_OF_INTF` definition, with the source's own
`[simp]`. -/
@[simp] theorem REL_OF_INTF_def {γ α : Type} (I : Interface) (R : Set (γ × α)) :
    REL_OF_INTF I R ↔ True := Iff.rfl

/-- The source's `REL_OF_INTF_P` ("Version to resolve relator
arguments"). Its second argument is a *partially applied* relator, so
where the source relies on HOL's schematic types this one is
polymorphic over `Sort v`. -/
def REL_OF_INTF_P {ι : Sort w} {β : Sort v} (_I : ι) (_R : β) : Prop := True

/-- The source's `REL_OF_INTF_P` definition, with the source's own
`[simp]`. -/
@[simp] theorem REL_OF_INTF_P_def {ι : Sort w} {β : Sort v} (I : ι) (R : β) :
    REL_OF_INTF_P I R ↔ True := Iff.rfl

/-- The source's `CNV_ANNOT`(1), the application rule. -/
theorem CNV_ANNOT_app {γ γ' α β : Type} {Ra : Set (γ × α)} {Rr : Set (γ' × β)}
    {a a' : α} {f f' : α → β}
    (ha : CNV_ANNOT a a' Ra) (hf : CNV_ANNOT f f' (Ra →ᵣ Rr)) :
    CNV_ANNOT (f $ᵃ a) (f' $ᵃ a') Rr := by
  have ha' : a = a' := ha
  have hf' : f = f' := hf
  show f a = f' a'
  rw [ha', hf']

/-- The source's `CNV_ANNOT`(2), the abstraction rule. -/
theorem CNV_ANNOT_abs {γ γ' α β : Type} {Ra : Set (γ × α)} {Rr : Set (γ' × β)}
    {f f' : α → β} (h : ∀ x, CNV_ANNOT x x Ra → CNV_ANNOT (f x) (f' x) Rr) :
    CNV_ANNOT (ABS f) (ABS f') (Ra →ᵣ Rr) := by
  have hf : f = f' := funext fun x => h x rfl
  show ABS f = ABS f'
  rw [hf]

/-- The source's `CNV_ANNOT`(4), the operator rule — the one the phase
actually runs, and the reason `REL_OF_INTF` exists. Ported without the
`INDEP R` premise (delta I1). -/
theorem CNV_ANNOT_op {γ α : Type} {f : α} {I : Interface} {R : Set (γ × α)}
    (_h : REL_OF_INTF I R) : CNV_ANNOT (OP f :::ᵢ I) (OP f ::: R) R := rfl

/-- The source's `CNV_ANNOT`(5), the direct-annotation rule. -/
theorem CNV_ANNOT_rel {γ α : Type} {t t' : α} {R : Set (γ × α)}
    (h : CNV_ANNOT t t' R) : CNV_ANNOT (t ::: R) t' R := h

/-- The source's `CNV_ANNOT`(6), the indirect-annotation rule. -/
theorem CNV_ANNOT_ind {γ α : Type} {t t' : α} {name : RelName} {R : Set (γ × α)}
    (_hn : IND_FACT name R) (h : CNV_ANNOT t t' R) : CNV_ANNOT (t ::# name) t' R := h

/-- The source's `consts i_of_rel :: 'a ⇒ 'b`, the interface *of* a
relator. Rendered like `rel_annot` (deltas T2, I9): the relator lives in
the application term. -/
def i_of_rel {γ α : Type} (_R : Set (γ × α)) : Interface := .const "i_of_rel"

/-- The source's `ROI_P_app` ("Only if interface is really
application"). -/
theorem ROI_P_app {γ α : Type} {I : Interface} {R : Set (γ × α)}
    (_h : REL_OF_INTF_P I R) : REL_OF_INTF I R := trivial

/-- The source's `ROI_app` ("Only if interface is really application"),
with `⟨R⟩S` written as the ordinary application `S R` (wave A's delta
R1: there is no `relAPP`). -/
theorem ROI_app {γ α : Type} {β : Sort v} {I : Interface} {J : Interface → Interface}
    {R : Set (γ × α)} {S : Set (γ × α) → β}
    (_hI : REL_OF_INTF I R) (_hJ : REL_OF_INTF_P J S) :
    REL_OF_INTF_P (intfAPP J I) (S R) := trivial

/-- The source's `ROI_i_of_rel`(1). -/
theorem ROI_i_of_rel_P {γ α : Type} {β : Sort v} (S : β) (R : Set (γ × α)) :
    REL_OF_INTF_P (i_of_rel R) S := trivial

/-- The source's `ROI_i_of_rel`(2). -/
theorem ROI_i_of_rel {γ α : Type} (R : Set (γ × α)) : REL_OF_INTF (i_of_rel R) R := trivial

/-- The source's `ROI_const`(1). -/
theorem ROI_const_P {ι : Sort w} {β : Sort v} (J : ι) (S : β) : REL_OF_INTF_P J S := trivial

/-- The source's `ROI_const`(2) — and its `REL_OF_INTF_I`, which is the
same statement under a second name. -/
theorem ROI_const {γ α : Type} (I : Interface) (R : Set (γ × α)) : REL_OF_INTF I R := trivial

/-- The source's `REL_OF_INTF_I`. -/
theorem REL_OF_INTF_I {γ α : Type} (I : Interface) (R : Set (γ × α)) : REL_OF_INTF I R := trivial

/-- The source's `ROI_init`: the rule the `rel_inf` phase resolves the
goal against, replacing interface annotations by relator annotations. -/
theorem ROI_init {γ α : Type} {a a' : α} {c : γ} {R : Set (γ × α)}
    (h₁ : CNV_ANNOT a a' R) (h₂ : (c, a') ∈ R) : (c, a) ∈ R := by
  have : a = a' := h₁
  rw [this]; exact h₂

namespace Autoref

/-! ### Interfaces from types (delta I5) -/

/-- The interface-level rendering of a Lean type. `i_fun` for a function
type, `⟨i_a₁⟩…⟨i_aₙ⟩i_c` for a constant type applied to type arguments,
and `i_std` — the tutorial's own placeholder — for anything else. -/
partial def intfOfType (τ : Expr) : MetaM Interface := do
  match ← whnfR τ with
  | .forallE _ d b _ =>
    if b.hasLooseBVars then return .const "i_std"
    else return .app (.app (.const "i_fun") (← intfOfType d)) (← intfOfType b)
  | τ =>
    match τ.getAppFn with
    | .const n _ =>
      let mut r : Interface := .const ("i_" ++ n.getString!.toLower)
      for a in τ.getAppArgs do
        if (← isType a) then r := .app r (← intfOfType a)
      return r
    | _ => return .const "i_std"

/-- An `Interface` value as a Lean term. -/
def intfToExpr : Interface → Expr
  | .const n => mkApp (mkConst ``Interface.const) (mkStrLit n)
  | .app f x => mkApp2 (mkConst ``Interface.app) (intfToExpr f) (intfToExpr x)

/-- An `Interface` value read back out of a Lean term. -/
partial def intfOfExpr? (e : Expr) : Option Interface :=
  match e.getAppFnArgs with
  | (``Interface.const, #[n]) =>
    match n with
    | .lit (.strVal s) => some (.const s)
    | _ => none
  | (``Interface.app, #[f, x]) => do
    return .app (← intfOfExpr? f) (← intfOfExpr? x)
  | _ => none

/-- An interface, as it prints in a trace or a failure message. -/
partial def intfToString : Interface → String
  | .const n => n
  | .app f x => s!"⟨{intfToString x}⟩{intfToString f}"

/-! ### The `autoref_op_pat` net -/

/-- The simp set of the source's `autoref_op_pat` database: the
"operation patterns" that rewrite surface syntax into tagged operator
form before identification proper (`E``{v} ≡ op_succ$E$v` in the
source's own example). The source's second net, `autoref_op_pat_def`,
is absent — delta I7. -/
def opPatContext : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for n in ← Lean.labelled `autoref_op_pat do
    thms ← thms.addConst n
  Simp.mkContext { decide := false } (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)

/-- Run the `autoref_op_pat` net over a term, returning the rewritten
term and a proof that it equals the original (`none` when nothing
fired). -/
def opPatRewrite (e : Expr) : MetaM (Expr × Option Expr) := do
  let (r, _) ← Meta.simp e (← opPatContext)
  return (r.expr, r.proof?)

/-! ### `id_tac` — the identification walk (delta I2) -/

/-- Is this term an operator leaf rather than something to decompose?
An application splits at its last non-explicit argument (delta I3);
`k` below is the number of arguments belonging to the operator. -/
def opSplit (e : Expr) : MetaM Nat := do
  let args := e.getAppArgs
  if args.isEmpty then return 0
  let info ← getFunInfoNArgs e.getAppFn args.size
  let mut k := args.size
  for i in [0:args.size] do
    let j := args.size - 1 - i
    if h : j < info.paramInfo.size then
      if info.paramInfo[j].binderInfo.isExplicit then k := j else break
    else break
  return k

/-- Tag a term as an operator leaf: the source's `ID_const`, whose
conclusion is `ID_OP c (OP c :::ᵢ I) I`. -/
def tagOp (e : Expr) : MetaM (Expr × Interface) := do
  let I ← intfOfType (← inferType e)
  let t ← mkAppM ``ANNOT #[← mkAppM ``OP #[e], ← mkAppM ``i_annot #[intfToExpr I]]
  return (t, I)

/-- The codomain interface of an application, i.e. the `I₂` of
`ID_app`'s `I₁ →ᵢ I₂`. -/
def intfCodomain : Interface → Interface
  | .app (.app (.const "i_fun") _) i₂ => i₂
  | _ => .const "i_std"

/-- The source's `id_tac`: rewrite a term into `OP`/`APP`-tagged,
interface-typed form. The cases are `ID_annotated` (already tagged),
`ID_app` (the `$ᵃ` spine, and the Lean application split of delta I3),
delta I4's `decide` case, and `ID_const` (the leaf). -/
partial def idTerm (e : Expr) : MetaM (Expr × Interface) := do
  -- `ID_tagged_OP` / `ID_annotated`: an already-tagged operator is left alone.
  if let some (t, a) := isANNOT? e then
    if let (``i_annot, #[I]) := a.getAppFnArgs then
      if let some I := intfOfExpr? I then
        return (e, I)
      else
        return (e, ← intfOfType (← inferType t))
  -- `ID_app`, on a spine the op-pat net (or a rule) already tagged.
  if let some (f, x) := isAPP? e then
    let (f', If) ← idTerm f
    let (x', _) ← idTerm x
    return (← mkAppM ``APP #[f', x'], intfCodomain If)
  -- Delta I4: `@decide (@Eq τ a b) inst` is the operator `fun x y => decide (x = y)`
  -- applied to `a` and `b`.
  if let (``Decidable.decide, #[p, _]) := e.getAppFnArgs then
    if let (``Eq, #[τ, a, b]) := p.getAppFnArgs then
      let op ← withLocalDeclD `x τ fun x => withLocalDeclD `y τ fun y => do
        let eq ← mkEq x y
        let inst ← synthInstance (← mkAppM ``Decidable #[eq])
        mkLambdaFVars #[x, y] (← mkAppOptM ``Decidable.decide #[some eq, some inst])
      if ← isDefEq (mkApp2 op a b) e then
        let (op', Iop) ← tagOp op
        let (a', _) ← idTerm a
        let (b', _) ← idTerm b
        let fa ← mkAppM ``APP #[op', a']
        return (← mkAppM ``APP #[fa, b'], intfCodomain (intfCodomain Iop))
  -- `ID_app` on an ordinary Lean application (delta I3).
  let k ← opSplit e
  let args := e.getAppArgs
  if k < args.size then
    let head := mkAppN e.getAppFn (args.extract 0 k)
    let (cur₀, I₀) ← tagOp head
    let mut cur := cur₀
    let mut I := I₀
    for a in args.extract k args.size do
      let (a', _) ← idTerm a
      cur ← mkAppM ``APP #[cur, a']
      I := intfCodomain I
    return (cur, I)
  -- `ID_abs` is not implemented (delta I6): report, naming the subterm.
  if e.isLambda then
    throwError "operation identification: no rule for the abstraction{indentExpr e}\n\
      (`ID_abs` is ported but the identification walk has no abstraction case — \
      see delta I6 of `Autoref/IdOps.lean`)"
  -- `ID_const`: a leaf.
  tagOp e

/-! ### The `id_op` phase -/

/-- The source's `id_phase`, whose `tac` is
`resolve_tac @{thms ID_init} THEN' id_tac`. -/
def idPhase : Phase where
  name := "id_op"
  run := fun st => do
    let goal := st.goal
    let ty ← instantiateMVars (← goal.getType)
    let some (c, a, R) := parseRefine? ty
      | throwError "the goal is not of the form `(?c, a) ∈ ?R`:{indentExpr ty}"
    let (a₁, pat?) ← opPatRewrite a
    let (a', I) ← idTerm a₁
    unless ← isDefEq a₁ a' do
      throwError "the tagged term is not definitionally the term it came from.\n\
        before:{indentExpr a₁}\nafter:{indentExpr a'}"
    let newGoal ← mkFreshExprSyntheticOpaqueMVar (← mkRefine c a' R)
    let idOpTy ← mkAppM ``ID_OP #[a, a', intfToExpr I]
    let base := pat?.getD (← mkEqRefl a)
    let idPf ← mkExpectedTypeHint base idOpTy
    goal.assign (← mkAppM ``ID_init #[idPf, newGoal])
    let st := st.note m!"id_op: {a} ⤳ {a'} : {intfToString I}"
    return { st with goal := newGoal.mvarId!, intf := I }
  analyze := fun st => do
    if (← instantiateMVars (← st.goal.getType)).hasSorry then
      return some m!"the identified goal is not well-formed"
    return none
  prettyFailure := fun st m => do
    return m!"{m}\nabstract term:{indentExpr st.abs}"

/-! ### `roi_tac` — the relator-skeleton walk (delta I8) -/

/-- The source's `rel_of_intf_thm`, on the type side (delta I8): a
function type gives the function relator, everything else a fresh
relator variable for `fix_rel` to solve. -/
partial def relSkeleton (τ : Expr) : MetaM Expr := do
  match ← whnfR τ with
  | .forallE _ d b _ =>
    if b.hasLooseBVars then freshRel τ
    else return ← mkAppM ``funRel #[← relSkeleton d, ← relSkeleton b]
  | τ => freshRel τ
where
  /-- A fresh `?R : Set (?γ × τ)`. -/
  freshRel (τ : Expr) : MetaM Expr := do
    let lvl ← getLevel τ
    let γ ← mkFreshExprMVar (mkSort lvl)
    mkFreshExprMVar (← mkAppM ``Set #[← mkAppM ``Prod #[γ, τ]])

/-- The source's `roi_tac`: replace every interface annotation
`OP f :::ᵢ I` by a relator annotation `OP f ::: R`, threading the
relator through the application structure exactly as the source's
`CNV_ANNOT` rules do — `Rr` is the relator of `e`'s *result*, an
argument gets a fresh relator `Ra` (`relSkeleton`), and the function
gets `Ra →ᵣ Rr` (`CNV_ANNOT`(1)); an operator gets whatever relator
reached it (`CNV_ANNOT`(4), its `REL_OF_INTF I R` premise discharged by
`ROI_const`).

Threading is what makes the phase do real work: it is why the relator
of `cons`'s first argument *is* the relator the literal `1` is
translated at, so that fixing one fixes the other. Annotating each
operator independently would leave every argument relator unconstrained
and the synthesized proof full of metavariables. -/
partial def cnvAnnot (e : Expr) (Rr : Expr) : MetaM Expr := do
  if let some (f, x) := isAPP? e then
    let Ra ← relSkeleton (← inferType x)
    let f' ← cnvAnnot f (← mkAppM ``funRel #[Ra, Rr])
    let x' ← cnvAnnot x Ra
    return ← mkAppM ``APP #[f', x']
  if let some (t, a) := isANNOT? e then
    if let (``i_annot, #[_]) := a.getAppFnArgs then
      return ← mkAppM ``ANNOT #[t, ← mkAppM ``rel_annot #[Rr]]
  return e

/-- The source's `roi_phase`, whose `tac` is
`resolve_tac @{thms ROI_init} THEN' roi_tac`. -/
def roiPhase : Phase where
  name := "rel_inf"
  run := fun st => do
    let goal := st.goal
    let ty ← instantiateMVars (← goal.getType)
    let some (c, a, R) := parseRefine? ty
      | throwError "the goal is not of the form `(?c, a) ∈ ?R`:{indentExpr ty}"
    let a' ← cnvAnnot a R
    unless ← isDefEq a a' do
      throwError "the re-annotated term is not definitionally the term it came from.\n\
        before:{indentExpr a}\nafter:{indentExpr a'}"
    let newGoal ← mkFreshExprSyntheticOpaqueMVar (← mkRefine c a' R)
    let cnvTy ← mkAppM ``CNV_ANNOT #[a, a', R]
    let cnvPf ← mkExpectedTypeHint (← mkEqRefl a) cnvTy
    goal.assign (← mkAppM ``ROI_init #[cnvPf, newGoal])
    let st := st.note m!"rel_inf: {a'}"
    return { st with goal := newGoal.mvarId! }
  prettyFailure := fun st m => do
    return m!"{m}\ninterface assigned by id_op: {intfToString st.intf}"

end Autoref

end Lax13Proofs.Refine
