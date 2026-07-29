import Lax13Proofs.Refine.Autoref.Attrs
import Mathlib.Data.List.Forall2

/-!
The relator zoo: relations between concrete and abstract types, built
structurally.

Port of `thys/Automatic_Refinement/Parametricity/Relators.thy` of AFP
`Automatic_Refinement` (Lammich) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 — AFP for Isabelle2025-2,
release 2026-02-06. The verbatim source text this file is checked
against is `plans/word-ram/refinement-tower/p2-autoref-extracts.md` §1;
everything below quotes it in its doc-comments.

A relator is a *set of pairs*, concrete component first (design record
fidelity note F3), so `⟨R⟩fun_rel`, `⟨R⟩list_rel` and friends are
ordinary `Set (concrete × abstract)` values and their composition is
ordinary `Set`-relation composition (`relComp`, below). Nothing in this
file mentions `NRest`: `Relators.thy` is pure HOL, one layer below the
monad, and the port keeps that property — the import list is Mathlib
plus `Autoref/Attrs.lean` and nothing else.

## The source, verbatim

```isabelle
definition fun_rel where
  fun_rel_def_internal: "fun_rel A B ≡ { (f,f'). ∀(a,a')∈A. (f a, f' a')∈B }"
abbreviation fun_rel_syn (infixr "→" 60) where "A→B ≡ ⟨A,B⟩fun_rel"

definition prod_rel where
  prod_rel_def_internal: "prod_rel R1 R2 ≡ { ((a,b),(a',b')) . (a,a')∈R1 ∧ (b,b')∈R2 }"
abbreviation prod_rel_syn (infixr "×⇩r" 70) where "a×⇩rb ≡ ⟨a,b⟩prod_rel"

definition option_rel where option_rel_def_internal:
  "option_rel R ≡ { (Some a,Some a') | a a'. (a,a')∈R } ∪ {(None,None)}"

definition sum_rel where sum_rel_def_internal:
  "sum_rel Rl Rr ≡ { (Inl a, Inl a') | a a'. (a,a')∈Rl } ∪
                   { (Inr a, Inr a') | a a'. (a,a')∈Rr }"

definition list_rel where list_rel_def_internal:
  "list_rel R ≡ {(l,l'). list_all2 (λx x'. (x,x')∈R) l l'}"

lemma fun_relI[intro!]: "⟦⋀a a'. (a,a')∈A ⟹ (f a,f' a')∈B⟧ ⟹ (f,f')∈A→B"
lemma fun_relD: "((f,f')∈(A→B)) ⟹ (⋀x x'. ⟦ (x,x')∈A ⟧ ⟹ (f x, f' x')∈B)"
lemma list_rel_induct[induct set,consumes 1, case_names Nil Cons]:
  assumes "(l,l')∈⟨R⟩ list_rel"  assumes "P [] []"
  assumes "⋀x x' l l'. ⟦ (x,x')∈R; (l,l')∈⟨R⟩list_rel; P l l' ⟧ ⟹ P (x#l) (x'#l')"
  shows "P l l'"
lemma list_rel_mono[relator_props]: assumes A: "R⊆R'" shows "⟨R⟩list_rel ⊆ ⟨R'⟩list_rel"

definition build_rel where "build_rel α I ≡ {(c,a) . a=α c ∧ I c}"
abbreviation "br≡build_rel"
lemma in_br_conv: "(c,a)∈br α I ⟷ a=α c ∧ I c"
lemma br_id[simp]: "br id (λ_. True) = Id"
lemma br_chain: "(build_rel β J) O (build_rel α I) = build_rel (α∘β) (λs. J s ∧ I (β s))"
lemma br_sv[simp, intro!,relator_props]: "single_valued (br α I)"
```

together with the two `Relation.thy` operations the whole file is
phrased over: `r O s = {(x,z). ∃y. (x,y)∈r ∧ (y,z)∈s}` and
`single_valued r = (∀x y. (x,y)∈r ⟶ (∀z. (x,z)∈r ⟶ y=z))`.

## Substrate deltas and departures, each flagged

**R1 — `relAPP`/`⟨R⟩` is not ported.** The source's `relAPP f x ≡ f x`
plus its `⟨_⟩_` syntax translation exists to keep relator *arguments*
out of higher-order unification: Isabelle's unifier cannot reliably
solve `?R ?x =?= ⟨A⟩list_rel` with the relator applied directly, so
every relator is written in a tagged prefix form. That is a property of
Isabelle's unifier, not of the calculus — ledger class D1 (Isabelle/ML
device → Lean 4 substrate) — and Lean 4's elaborator, which indexes on
head symbols with DiscrTree, has no such failure mode. Relators here are
therefore ordinary functions applied ordinarily, and `⟨R⟩list_rel` reads
`listRel R`. If a later phase turns out to need the tag after all, it is
one `def relAPP f x := f x` plus notation away, and nothing stated in
this file changes.

**R2 — definition names are camelCase, rule names are the source's.**
`fun_rel`/`prod_rel`/… become `funRel`/`prodRel`/…, following P1's
`conc_fun ↦ concFun`, `nrest_rel ↦ nrestRel`. The *rule* names are kept
in the source's own spelling — `fun_relI`, `fun_relD`,
`list_rel_induct`, `list_rel_mono`, `prod_rel_mono`, … — because those
are the names the Autoref and Sepref layers cite, and the campaign's
debugging methodology (design record §4) is "the source's manuals stay
usable".

**R3 — the unfolding lemmas are `mem_…_iff`.** The source's
`fun_rel_def`, `prod_rel_def`, … are equations between sets, tagged
`[refine_rel_defs]`; here the same content is stated as membership
equivalences, following P1's `in_br_conv ↦ mem_br_iff` and
`mem_relComp`, and tagged `@[refine_rel_defs]` (the simp set declared in
`Autoref/Attrs.lean`) plus `@[simp]` where the right-hand side is an
unconditional improvement, again following P1's precedent for
`mem_br_iff`/`mem_relComp`.

**R4 — `fun_rel_mono` is not in the extract.** The extract quotes only
`list_rel_mono` from the `[relator_props]` mono family. `prodRel`,
`optionRel`, `sumRel` and `funRel` get the same lemma here, in the only
shape a set-of-pairs relator admits: covariant in every argument except
the *domain* of `funRel`, which is contravariant. All four are
`#guard`-refuted at `Bool` tables in the gate at the bottom of this file
before being proved (repo practice: refute before prove).

**R5 — no relator-composition distribution lemmas are authored.** The
design record promises that "composition is `Set`-relation composition",
and that is discharged by `relComp` living here and by `br_chain`, which
*is* in the extract. The extract quotes no `⟨R⟩list_rel O ⟨S⟩list_rel`
style distribution law, so none is invented: the scope of P2 wave A is
the spine (design record §3, scope note), and a composition law whose
source statement has not been read is exactly the kind of thing the
fidelity charter forbids guessing at.

**R6 — relocations from P1.** `relComp`, `SingleValued`, `br` and their
pure-relation lemma suite were defined in `NREST/DataRefinement.lean`
during P1, under that file's delta S2 ("relation composition and
single-valuedness are P2 material, pulled forward … P2 should move them
rather than restate them"). This wave is that move. Every fully
qualified name is unchanged, which is why one lemma —
`NRest.singleValued_relComp` — sits inside a `namespace NRest` block
below despite this file knowing nothing about `NRest`: it was declared
inside `DataRefinement.lean`'s `namespace NRest`, and the name is what
downstream cites. Every moved statement and proof is byte-identical to
P1's; the only edits are two *attribute* additions the source itself
asks for and P1 could not make because the attributes did not exist
yet — `@[relator_props]` on `br_singleValued` (the source's
`br_sv[simp, intro!, relator_props]`) and `refine_rel_defs` on
`mem_br_iff` (the source's `in_br_conv`, in the family the source tags
`[refine_rel_defs]`).
-/

namespace Lax13Proofs.Refine

variable {α β δ γ ε ζ : Type}

/-! ### Relation composition and single-valuedness

Isabelle's `Relation.thy` operations the whole relator algebra is
phrased over. Relocated from `NREST/DataRefinement.lean` (delta R6). -/

/-- Isabelle's relation composition `R O S`, at the concrete-first
convention of design record F3: `(c, a) ∈ relComp R S` when some
intermediate `b` has `(c, b) ∈ R` and `(b, a) ∈ S`. -/
def relComp (R : Set (β × δ)) (S : Set (δ × α)) : Set (β × α) :=
  {p | ∃ b, (p.1, b) ∈ R ∧ (b, p.2) ∈ S}

@[simp] theorem mem_relComp {R : Set (β × δ)} {S : Set (δ × α)} {c : β} {a : α} :
    (c, a) ∈ relComp R S ↔ ∃ b, (c, b) ∈ R ∧ (b, a) ∈ S := Iff.rfl

/-- Isabelle's `single_valued`: every concrete value is related to at
most one abstract value. -/
def SingleValued (R : Set (β × α)) : Prop :=
  ∀ c a a', (c, a) ∈ R → (c, a') ∈ R → a = a'

/-! ### `br` — abstraction function plus invariant -/

/-- The source's `build_rel α I`, abbreviated `br`: the relation of an
abstraction function `f` together with a concrete-side invariant `I`. -/
def br (f : β → α) (I : β → Prop) : Set (β × α) := {p | p.2 = f p.1 ∧ I p.1}

/-- The source's `in_br_conv`. -/
@[simp, refine_rel_defs] theorem mem_br_iff {f : β → α} {I : β → Prop} {c : β} {a : α} :
    (c, a) ∈ br f I ↔ a = f c ∧ I c := Iff.rfl

/-- The source's `brI`. -/
theorem mem_br {f : β → α} {I : β → Prop} {c : β} {a : α} (ha : a = f c) (hI : I c) :
    (c, a) ∈ br f I := ⟨ha, hI⟩

/-- The source's `br_id`, with `Id` read as `Set.diagonal` (delta S3). -/
@[simp] theorem br_id : br (id : α → α) (fun _ => True) = Set.diagonal α := by
  ext p; simp [br, Set.diagonal, eq_comm]

/-- The source's `br_chain`. -/
theorem br_chain (g : β → δ) (J : β → Prop) (f : δ → α) (I : δ → Prop) :
    relComp (br g J) (br f I) = br (f ∘ g) (fun s => J s ∧ I (g s)) := by
  ext p
  obtain ⟨c, a⟩ := p
  simp only [mem_relComp, mem_br_iff, Function.comp_apply]
  constructor
  · rintro ⟨b, ⟨rfl, hJ⟩, ⟨rfl, hI⟩⟩
    exact ⟨rfl, hJ, hI⟩
  · rintro ⟨rfl, hJ, hI⟩
    exact ⟨g c, ⟨rfl, hJ⟩, ⟨rfl, hI⟩⟩

/-- The source's `br_sv`, with the source's own `[relator_props]` tag
(delta R6). -/
@[relator_props] theorem br_singleValued (f : β → α) (I : β → Prop) : SingleValued (br f I) := by
  rintro c a a' ⟨ha, -⟩ ⟨ha', -⟩
  exact ha.trans ha'.symm

/-- `Id` is single-valued, in the `Set.diagonal` spelling. -/
theorem singleValued_diagonal : SingleValued (Set.diagonal α) := by
  rintro c a a' ha ha'
  exact ha.symm.trans ha'

namespace NRest

/-- Single-valuedness is preserved by composition (the source's
`single_valued_relcomp`, used in `Data_Refinement.thy`).

Its fully qualified name is `…Refine.NRest.singleValued_relComp`
because `DataRefinement.lean` declared it inside its `namespace NRest`;
the name is preserved across the relocation, which is why this one
`namespace NRest` block appears in a file that is otherwise innocent of
the monad (delta R6). -/
theorem singleValued_relComp {R : Set (β × δ)} {S : Set (δ × α)}
    (hR : SingleValued R) (hS : SingleValued S) : SingleValued (relComp R S) := by
  rintro c a a' ⟨b, hb, hba⟩ ⟨b', hb', hb'a⟩
  rw [hR c b b' hb hb'] at hba
  exact hS b' a a' hba hb'a

end NRest

/-! ### The function relator `A →ᵣ B`

The source's `fun_rel`, notation `A → B` at `infixr 60`. Lean's `→` is
the function arrow, so the relator gets the subscripted spelling `→ᵣ`
at the source's precedence and associativity — the same device P1 used
for `-ᵣ`. -/

/-- The source's
`fun_rel A B ≡ { (f,f'). ∀(a,a')∈A. (f a, f' a')∈B }`: two functions are
related when they take `A`-related arguments to `B`-related results. -/
def funRel (A : Set (α × β)) (B : Set (γ × δ)) : Set ((α → γ) × (β → δ)) :=
  {p | ∀ a a', (a, a') ∈ A → (p.1 a, p.2 a') ∈ B}

@[inherit_doc] infixr:60 " →ᵣ " => funRel

/-- The source's `fun_rel_def`. -/
@[simp, refine_rel_defs] theorem mem_funRel_iff {A : Set (α × β)} {B : Set (γ × δ)}
    {f : α → γ} {f' : β → δ} :
    (f, f') ∈ A →ᵣ B ↔ ∀ a a', (a, a') ∈ A → (f a, f' a') ∈ B := Iff.rfl

/-- The source's `fun_relI[intro!]`. -/
theorem fun_relI {A : Set (α × β)} {B : Set (γ × δ)} {f : α → γ} {f' : β → δ}
    (h : ∀ a a', (a, a') ∈ A → (f a, f' a') ∈ B) : (f, f') ∈ A →ᵣ B := h

/-- The source's `fun_relD`. -/
theorem fun_relD {A : Set (α × β)} {B : Set (γ × δ)} {f : α → γ} {f' : β → δ}
    (h : (f, f') ∈ A →ᵣ B) {x : α} {x' : β} (hx : (x, x') ∈ A) : (f x, f' x') ∈ B :=
  h x x' hx

/-! ### The product relator `R₁ ×ᵣ R₂` -/

/-- The source's
`prod_rel R1 R2 ≡ { ((a,b),(a',b')) . (a,a')∈R1 ∧ (b,b')∈R2 }`. -/
def prodRel (R₁ : Set (α × β)) (R₂ : Set (γ × δ)) : Set ((α × γ) × (β × δ)) :=
  {p | (p.1.1, p.2.1) ∈ R₁ ∧ (p.1.2, p.2.2) ∈ R₂}

@[inherit_doc] infixr:70 " ×ᵣ " => prodRel

/-- The source's `prod_rel_def`. -/
@[simp, refine_rel_defs] theorem mem_prodRel_iff {R₁ : Set (α × β)} {R₂ : Set (γ × δ)}
    {a : α} {b : γ} {a' : β} {b' : δ} :
    ((a, b), (a', b')) ∈ R₁ ×ᵣ R₂ ↔ (a, a') ∈ R₁ ∧ (b, b') ∈ R₂ := Iff.rfl

/-! ### The option relator -/

/-- The source's
`option_rel R ≡ { (Some a,Some a') | a a'. (a,a')∈R } ∪ {(None,None)}`,
union and all. -/
def optionRel (R : Set (α × β)) : Set (Option α × Option β) :=
  {p | ∃ a a', (a, a') ∈ R ∧ p = (some a, some a')} ∪ {(none, none)}

/-- The source's `option_rel_def`. -/
@[refine_rel_defs] theorem mem_optionRel_iff {R : Set (α × β)} {p : Option α × Option β} :
    p ∈ optionRel R ↔ (∃ a a', (a, a') ∈ R ∧ p = (some a, some a')) ∨ p = (none, none) :=
  Iff.rfl

@[simp] theorem mem_optionRel_some_some {R : Set (α × β)} {a : α} {a' : β} :
    ((some a, some a') ∈ optionRel R) ↔ (a, a') ∈ R := by
  simp only [mem_optionRel_iff, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, and_false,
    or_false]
  exact ⟨fun ⟨_, _, hb, rfl, rfl⟩ => hb, fun h => ⟨a, a', h, rfl, rfl⟩⟩

@[simp] theorem mem_optionRel_none_none {R : Set (α × β)} :
    ((none : Option α), (none : Option β)) ∈ optionRel R := Or.inr rfl

@[simp] theorem mem_optionRel_some_none {R : Set (α × β)} {a : α} :
    ((some a, (none : Option β)) ∉ optionRel R) := by
  simp only [mem_optionRel_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_and, exists_false,
    or_self, not_false_eq_true]

@[simp] theorem mem_optionRel_none_some {R : Set (α × β)} {a' : β} :
    (((none : Option α), some a') ∉ optionRel R) := by
  simp only [mem_optionRel_iff, Prod.mk.injEq, reduceCtorEq, false_and, and_false, exists_false,
    or_self, not_false_eq_true]

/-! ### The sum relator -/

/-- The source's
`sum_rel Rl Rr ≡ { (Inl a, Inl a') | a a'. (a,a')∈Rl } ∪
                 { (Inr a, Inr a') | a a'. (a,a')∈Rr }`. -/
def sumRel (Rl : Set (α × β)) (Rr : Set (γ × δ)) : Set ((α ⊕ γ) × (β ⊕ δ)) :=
  {p | ∃ a a', (a, a') ∈ Rl ∧ p = (Sum.inl a, Sum.inl a')} ∪
  {p | ∃ a a', (a, a') ∈ Rr ∧ p = (Sum.inr a, Sum.inr a')}

/-- The source's `sum_rel_def`. -/
@[refine_rel_defs] theorem mem_sumRel_iff {Rl : Set (α × β)} {Rr : Set (γ × δ)}
    {p : (α ⊕ γ) × (β ⊕ δ)} :
    p ∈ sumRel Rl Rr ↔
      (∃ a a', (a, a') ∈ Rl ∧ p = (Sum.inl a, Sum.inl a')) ∨
        (∃ a a', (a, a') ∈ Rr ∧ p = (Sum.inr a, Sum.inr a')) := Iff.rfl

@[simp] theorem mem_sumRel_inl_inl {Rl : Set (α × β)} {Rr : Set (γ × δ)} {a : α} {a' : β} :
    (((Sum.inl a : α ⊕ γ), (Sum.inl a' : β ⊕ δ)) ∈ sumRel Rl Rr) ↔ (a, a') ∈ Rl := by
  simp only [mem_sumRel_iff, Prod.mk.injEq, Sum.inl.injEq, reduceCtorEq, and_false,
    exists_false, or_false]
  exact ⟨fun ⟨_, _, hb, rfl, rfl⟩ => hb, fun h => ⟨a, a', h, rfl, rfl⟩⟩

@[simp] theorem mem_sumRel_inr_inr {Rl : Set (α × β)} {Rr : Set (γ × δ)} {b : γ} {b' : δ} :
    (((Sum.inr b : α ⊕ γ), (Sum.inr b' : β ⊕ δ)) ∈ sumRel Rl Rr) ↔ (b, b') ∈ Rr := by
  simp only [mem_sumRel_iff, Prod.mk.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
    exists_false, false_or]
  exact ⟨fun ⟨_, _, hb, rfl, rfl⟩ => hb, fun h => ⟨b, b', h, rfl, rfl⟩⟩

@[simp] theorem mem_sumRel_inl_inr {Rl : Set (α × β)} {Rr : Set (γ × δ)} {a : α} {b' : δ} :
    (((Sum.inl a : α ⊕ γ), (Sum.inr b' : β ⊕ δ)) ∉ sumRel Rl Rr) := by
  simp only [mem_sumRel_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_and, exists_false,
    or_self, not_false_eq_true]

@[simp] theorem mem_sumRel_inr_inl {Rl : Set (α × β)} {Rr : Set (γ × δ)} {b : γ} {a' : β} :
    (((Sum.inr b : α ⊕ γ), (Sum.inl a' : β ⊕ δ)) ∉ sumRel Rl Rr) := by
  simp only [mem_sumRel_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_and, exists_false,
    or_self, not_false_eq_true]

/-! ### The list relator -/

/-- The source's `list_rel R ≡ {(l,l'). list_all2 (λx x'. (x,x')∈R) l l'}`;
HOL's `list_all2` is mathlib's `List.Forall₂`. -/
def listRel (R : Set (α × β)) : Set (List α × List β) :=
  {p | List.Forall₂ (fun x x' => (x, x') ∈ R) p.1 p.2}

/-- The source's `list_rel_def`. -/
@[simp, refine_rel_defs] theorem mem_listRel_iff {R : Set (α × β)} {l : List α} {l' : List β} :
    (l, l') ∈ listRel R ↔ List.Forall₂ (fun x x' => (x, x') ∈ R) l l' := Iff.rfl

@[simp] theorem mem_listRel_nil {R : Set (α × β)} :
    (([] : List α), ([] : List β)) ∈ listRel R := List.Forall₂.nil

@[simp] theorem mem_listRel_cons {R : Set (α × β)} {x : α} {x' : β} {l : List α} {l' : List β} :
    ((x :: l, x' :: l') ∈ listRel R) ↔ (x, x') ∈ R ∧ (l, l') ∈ listRel R := by
  simp only [mem_listRel_iff, List.forall₂_cons]

/-- The source's
`list_rel_induct[induct set, consumes 1, case_names Nil Cons]`: induction
along the relatedness hypothesis, which it consumes. -/
theorem list_rel_induct {R : Set (α × β)} {P : List α → List β → Prop} {l : List α} {l' : List β}
    (h : (l, l') ∈ listRel R) (Nil : P [] [])
    (Cons : ∀ x x' l l', (x, x') ∈ R → (l, l') ∈ listRel R → P l l' → P (x :: l) (x' :: l')) :
    P l l' := by
  have h' : List.Forall₂ (fun x x' => (x, x') ∈ R) l l' := h
  clear h
  induction h' with
  | nil => exact Nil
  | cons hx hl ih => exact Cons _ _ _ _ hx hl ih

/-! ### Monotonicity — the `[relator_props]` family

The source tags each relator's monotonicity lemma `[relator_props]`; the
extract quotes `list_rel_mono` and the pattern (delta R4). All four are
`#guard`-checked at `Bool` tables in the gate below. -/

/-- The source's `fun_rel_mono`: contravariant in the domain relation,
covariant in the codomain relation (delta R4). -/
@[relator_props] theorem fun_rel_mono {A A' : Set (α × β)} {B B' : Set (γ × δ)}
    (hA : A' ⊆ A) (hB : B ⊆ B') : (A →ᵣ B) ⊆ (A' →ᵣ B') := by
  rintro ⟨f, f'⟩ hf a a' ha
  exact hB (hf a a' (hA ha))

/-- The source's `prod_rel_mono` (delta R4). -/
@[relator_props] theorem prod_rel_mono {R₁ R₁' : Set (α × β)} {R₂ R₂' : Set (γ × δ)}
    (h₁ : R₁ ⊆ R₁') (h₂ : R₂ ⊆ R₂') : (R₁ ×ᵣ R₂) ⊆ (R₁' ×ᵣ R₂') := by
  rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ ⟨ha, hb⟩
  exact ⟨h₁ ha, h₂ hb⟩

/-- The source's `option_rel_mono` (delta R4). -/
@[relator_props] theorem option_rel_mono {R R' : Set (α × β)} (h : R ⊆ R') :
    optionRel R ⊆ optionRel R' := by
  rintro p (⟨a, a', ha, rfl⟩ | rfl)
  · exact Or.inl ⟨a, a', h ha, rfl⟩
  · exact Or.inr rfl

/-- The source's `sum_rel_mono` (delta R4). -/
@[relator_props] theorem sum_rel_mono {Rl Rl' : Set (α × β)} {Rr Rr' : Set (γ × δ)}
    (hl : Rl ⊆ Rl') (hr : Rr ⊆ Rr') : sumRel Rl Rr ⊆ sumRel Rl' Rr' := by
  rintro p (⟨a, a', ha, rfl⟩ | ⟨b, b', hb, rfl⟩)
  · exact Or.inl ⟨a, a', hl ha, rfl⟩
  · exact Or.inr ⟨b, b', hr hb, rfl⟩

/-- The source's `list_rel_mono`. -/
@[relator_props] theorem list_rel_mono {R R' : Set (α × β)} (h : R ⊆ R') :
    listRel R ⊆ listRel R' := by
  rintro ⟨l, l'⟩ hl
  exact List.Forall₂.imp (fun _ _ hab => h hab) hl

/-! ### The executable gate (design record ledger D4)

Relators are sets of pairs, so at a finite carrier they are decidable
and every statement above can be *run*. The carrier is `Bool`, with
relations given as tables `BRel = Bool → Bool → Bool`; `ofBRel` turns a
table into the `Set (Bool × Bool)` it describes, and the `Decidable`
instances below are the plain unfoldings, so a `#guard` here is a
`#guard` about `funRel`/`prodRel`/`optionRel`/`sumRel` themselves.
`listRel` goes through an executable twin `listRelE` with a proved
agreement theorem, because `List.Forall₂` carries no decidability
instance.

The checks include negative controls throughout: a non-related pair
must be *rejected*, or the harness is proving nothing.

Naming note: `ofBRel`, not `ofRel`. The gates all share the namespace
`Lax13Proofs.Refine.Sanity`, and `NREST/DataRefinement.lean`'s gate —
which is *downstream* of this file and must not be edited — already owns
`Sanity.ofRel` for its `Fin 3` tables. -/

namespace Sanity

open Plausible

/-- A relation on `Bool`, as a decidable table. -/
abbrev BRel := Bool → Bool → Bool

/-- The set of pairs a table describes. -/
def ofBRel (R : BRel) : Set (Bool × Bool) := {p | R p.1 p.2 = true}

@[simp] theorem mem_ofBRel {R : BRel} {c a : Bool} : (c, a) ∈ ofBRel R ↔ R c a = true := Iff.rfl

instance instDecidableMemOfBRel (R : BRel) (p : Bool × Bool) : Decidable (p ∈ ofBRel R) :=
  inferInstanceAs (Decidable (R p.1 p.2 = true))

/-- `br` membership is decidable whenever the invariant is and the
abstract type has decidable equality — it is a conjunction of the two.
This is what makes the `br` checks below checks about `br` itself. -/
instance instDecidableMemBr [DecidableEq α] (f : β → α) (I : β → Prop) [DecidablePred I]
    (p : β × α) : Decidable (p ∈ br f I) :=
  inferInstanceAs (Decidable (p.2 = f p.1 ∧ I p.1))

instance instDecidableMemRelComp (R S : BRel) (p : Bool × Bool) :
    Decidable (p ∈ relComp (ofBRel R) (ofBRel S)) :=
  inferInstanceAs (Decidable (∃ b, (p.1, b) ∈ ofBRel R ∧ (b, p.2) ∈ ofBRel S))

instance instDecidableMemFunRel (A B : BRel) (p : (Bool → Bool) × (Bool → Bool)) :
    Decidable (p ∈ ofBRel A →ᵣ ofBRel B) :=
  inferInstanceAs (Decidable (∀ a a', (a, a') ∈ ofBRel A → (p.1 a, p.2 a') ∈ ofBRel B))

instance instDecidableMemProdRel (R₁ R₂ : BRel) (p : (Bool × Bool) × (Bool × Bool)) :
    Decidable (p ∈ ofBRel R₁ ×ᵣ ofBRel R₂) :=
  inferInstanceAs (Decidable ((p.1.1, p.2.1) ∈ ofBRel R₁ ∧ (p.1.2, p.2.2) ∈ ofBRel R₂))

instance instDecidableMemOptionRel (R : BRel) : ∀ p : Option Bool × Option Bool,
    Decidable (p ∈ optionRel (ofBRel R))
  | (some a, some a') => decidable_of_iff ((a, a') ∈ ofBRel R) mem_optionRel_some_some.symm
  | (some _, none) => isFalse mem_optionRel_some_none
  | (none, some _) => isFalse mem_optionRel_none_some
  | (none, none) => isTrue mem_optionRel_none_none

instance instDecidableMemSumRel (Rl Rr : BRel) : ∀ p : (Bool ⊕ Bool) × (Bool ⊕ Bool),
    Decidable (p ∈ sumRel (ofBRel Rl) (ofBRel Rr))
  | (Sum.inl a, Sum.inl a') => decidable_of_iff ((a, a') ∈ ofBRel Rl) mem_sumRel_inl_inl.symm
  | (Sum.inr b, Sum.inr b') => decidable_of_iff ((b, b') ∈ ofBRel Rr) mem_sumRel_inr_inr.symm
  | (Sum.inl _, Sum.inr _) => isFalse mem_sumRel_inl_inr
  | (Sum.inr _, Sum.inl _) => isFalse mem_sumRel_inr_inl

/-- Executable `listRel` at the gate carrier. -/
def listRelE (R : BRel) : List Bool → List Bool → Bool
  | [], [] => true
  | x :: l, x' :: l' => R x x' && listRelE R l l'
  | _, _ => false

@[simp] theorem listRelE_nil_nil (R : BRel) : listRelE R [] [] = true := rfl

@[simp] theorem listRelE_cons_cons (R : BRel) (x x' : Bool) (l l' : List Bool) :
    listRelE R (x :: l) (x' :: l') = (R x x' && listRelE R l l') := rfl

@[simp] theorem listRelE_nil_cons (R : BRel) (x' : Bool) (l' : List Bool) :
    listRelE R [] (x' :: l') = false := rfl

@[simp] theorem listRelE_cons_nil (R : BRel) (x : Bool) (l : List Bool) :
    listRelE R (x :: l) [] = false := rfl

/-- **The bridge.** Everything checked about `listRelE` below is checked
about `listRel`. -/
theorem listRelE_eq (R : BRel) : ∀ l l' : List Bool,
    listRelE R l l' = true ↔ (l, l') ∈ listRel (ofBRel R)
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | x :: l, x' :: l' => by
    simp only [listRelE_cons_cons, Bool.and_eq_true, mem_listRel_cons, mem_ofBRel,
      listRelE_eq R l l']

/-- The identity table — Isabelle's `Id` at the gate carrier. -/
def idB : BRel := fun c a => c == a

/-- The full table. -/
def topB : BRel := fun _ _ => true

/-- The empty table. -/
def botB : BRel := fun _ _ => false

/-- The table relating `false` to `true` and nothing else. -/
def flipB : BRel := fun c a => !c && a

/-- Decidable containment of tables: the executable `R ⊆ R'` the mono
lemmas are stated over. -/
def subB (R S : BRel) : Bool := decide (∀ c a : Bool, R c a = true → S c a = true)

/-- The executable containment agrees with `⊆`. -/
theorem subB_eq (R S : BRel) : subB R S = true ↔ ofBRel R ⊆ ofBRel S := by
  simp only [subB, decide_eq_true_eq]
  constructor
  · rintro h ⟨c, a⟩ hp; exact h c a hp
  · intro h c a hca; exact h (show (c, a) ∈ ofBRel R from hca)

/-! #### Spot checks: `br`, `relComp` -/

-- `br`: the invariant really is a side condition, and `br_id` is `Id`.
#guard ((4, 2) ∈ br (fun n : ℕ => n / 2) (fun n => n % 2 = 0))
#guard ¬ ((5, 2) ∈ br (fun n : ℕ => n / 2) (fun n => n % 2 = 0))   -- invariant fails
#guard ¬ ((4, 3) ∈ br (fun n : ℕ => n / 2) (fun n => n % 2 = 0))   -- abstraction fails
#guard ((3, 3) ∈ br (id : ℕ → ℕ) (fun _ => True))

-- `br_chain`, right-hand side: composing two `br`s composes the
-- abstractions and conjoins the invariants along the first one.
#guard ((8, 2) ∈ br ((fun n : ℕ => n / 2) ∘ (fun n : ℕ => n / 2))
  (fun s => s % 2 = 0 ∧ (s / 2) % 2 = 0))
#guard ¬ ((8, 3) ∈ br ((fun n : ℕ => n / 2) ∘ (fun n : ℕ => n / 2))
  (fun s => s % 2 = 0 ∧ (s / 2) % 2 = 0))
#guard ¬ ((6, 1) ∈ br ((fun n : ℕ => n / 2) ∘ (fun n : ℕ => n / 2))
  (fun s => s % 2 = 0 ∧ (s / 2) % 2 = 0))                          -- inner invariant fails

-- `relComp` (`mem_relComp`) at tables: composition really quantifies
-- over the intermediate value.
#guard ((true, true) ∈ relComp (ofBRel idB) (ofBRel idB))
#guard ¬ ((true, false) ∈ relComp (ofBRel idB) (ofBRel idB))
#guard ((false, true) ∈ relComp (ofBRel flipB) (ofBRel idB))
#guard ¬ ((false, true) ∈ relComp (ofBRel flipB) (ofBRel flipB))
#guard ¬ ((true, true) ∈ relComp (ofBRel idB) (ofBRel botB))

/-! #### Spot checks: `funRel` -/

-- `fun_relI`/`fun_relD` at `Id → Id`: `id` is related to itself, `not`
-- is not related to `id`.
#guard (((id : Bool → Bool), (id : Bool → Bool)) ∈ ofBRel idB →ᵣ ofBRel idB)
#guard ¬ (((not : Bool → Bool), (id : Bool → Bool)) ∈ ofBRel idB →ᵣ ofBRel idB)
#guard (((not : Bool → Bool), (not : Bool → Bool)) ∈ ofBRel idB →ᵣ ofBRel idB)

-- an empty domain relation relates everything (`fun_rel_mono`'s
-- contravariance, at its extreme)
#guard (((not : Bool → Bool), (id : Bool → Bool)) ∈ ofBRel botB →ᵣ ofBRel idB)
-- and a full codomain relation does too
#guard (((not : Bool → Bool), (id : Bool → Bool)) ∈ ofBRel idB →ᵣ ofBRel topB)
-- `flipB → flipB`: `not` sends `false ↦ true`, so `(not, not) ∉ flipB →ᵣ flipB`
#guard ¬ (((not : Bool → Bool), (not : Bool → Bool)) ∈ ofBRel flipB →ᵣ ofBRel flipB)

/-! #### Spot checks: `prodRel`, `optionRel`, `sumRel` -/

#guard (((true, false), (true, false)) ∈ ofBRel idB ×ᵣ ofBRel idB)
#guard ¬ (((true, false), (true, true)) ∈ ofBRel idB ×ᵣ ofBRel idB)
#guard (((true, false), (true, true)) ∈ ofBRel idB ×ᵣ ofBRel topB)

#guard ((some true, some true) ∈ optionRel (ofBRel idB))
#guard ¬ ((some true, some false) ∈ optionRel (ofBRel idB))
#guard ((none, none) ∈ optionRel (ofBRel idB))
#guard ¬ ((some true, none) ∈ optionRel (ofBRel idB))
#guard ¬ ((none, some true) ∈ optionRel (ofBRel botB))

#guard ((Sum.inl true, Sum.inl true) ∈ sumRel (ofBRel idB) (ofBRel idB))
#guard ((Sum.inr false, Sum.inr false) ∈ sumRel (ofBRel idB) (ofBRel idB))
#guard ¬ ((Sum.inl true, Sum.inr true) ∈ sumRel (ofBRel idB) (ofBRel idB))
#guard ¬ ((Sum.inl true, Sum.inl false) ∈ sumRel (ofBRel idB) (ofBRel topB))

/-! #### Spot checks: `listRel` -/

#guard listRelE idB [true, false, true] [true, false, true] = true
#guard listRelE idB [true, false] [true, true] = false        -- a mismatch is rejected
#guard listRelE idB [true] [true, true] = false               -- lengths must agree
#guard listRelE topB [true, false] [false, true] = true
#guard listRelE botB [] [] = true                             -- the empty lists are always related
#guard listRelE botB [true] [true] = false

/-! #### Property checks

The characteristic lemmas at sampled tables. Plausible's `Testable`
resolution wants `Bool`-valued statements, so each relator gets a
one-line executable twin — `decide` at the `Decidable` instance above —
with the agreement theorem that makes a counterexample to the twin a
counterexample to the relator itself. -/

/-- Executable `funRel` at the gate carrier. -/
def funRelE (A B : BRel) (f f' : Bool → Bool) : Bool := decide ((f, f') ∈ ofBRel A →ᵣ ofBRel B)

theorem funRelE_eq (A B : BRel) (f f' : Bool → Bool) :
    funRelE A B f f' = true ↔ (f, f') ∈ ofBRel A →ᵣ ofBRel B := by
  simp only [funRelE, decide_eq_true_eq]

/-- Executable `prodRel` at the gate carrier. -/
def prodRelE (R₁ R₂ : BRel) (p : (Bool × Bool) × (Bool × Bool)) : Bool :=
  decide (p ∈ ofBRel R₁ ×ᵣ ofBRel R₂)

theorem prodRelE_eq (R₁ R₂ : BRel) (p : (Bool × Bool) × (Bool × Bool)) :
    prodRelE R₁ R₂ p = true ↔ p ∈ ofBRel R₁ ×ᵣ ofBRel R₂ := by
  simp only [prodRelE, decide_eq_true_eq]

/-- Executable `optionRel` at the gate carrier. -/
def optionRelE (R : BRel) (p : Option Bool × Option Bool) : Bool :=
  decide (p ∈ optionRel (ofBRel R))

theorem optionRelE_eq (R : BRel) (p : Option Bool × Option Bool) :
    optionRelE R p = true ↔ p ∈ optionRel (ofBRel R) := by
  simp only [optionRelE, decide_eq_true_eq]

/-- Executable `sumRel` at the gate carrier. -/
def sumRelE (Rl Rr : BRel) (p : (Bool ⊕ Bool) × (Bool ⊕ Bool)) : Bool :=
  decide (p ∈ sumRel (ofBRel Rl) (ofBRel Rr))

theorem sumRelE_eq (Rl Rr : BRel) (p : (Bool ⊕ Bool) × (Bool ⊕ Bool)) :
    sumRelE Rl Rr p = true ↔ p ∈ sumRel (ofBRel Rl) (ofBRel Rr) := by
  simp only [sumRelE, decide_eq_true_eq]

-- Four sampled tables plus three implications is more instance search
-- than the default budget allows; `Testable` synthesis is structural in
-- the statement, so the ceiling is raised rather than the statements
-- being weakened.
set_option synthInstance.maxSize 800

/-- Sampling proxy for tables: the four entries. -/
instance instSampleableExtBRel : SampleableExt BRel where
  proxy := Bool × Bool × Bool × Bool
  sample := inferInstance
  interp := fun q c a => if c then (if a then q.2.2.2 else q.2.2.1) else
    (if a then q.2.1 else q.1)

/-- A `Bool → Bool` function, sampled as its two values. -/
def ofPair (q : Bool × Bool) : Bool → Bool := fun b => if b then q.2 else q.1

-- `list_rel_mono`: a bigger relation relates more lists.
#test ∀ (R S : BRel) (l l' : List Bool),
  subB R S = true → listRelE R l l' = true → listRelE S l l' = true

-- `list_rel_induct`, in its computational shape: relatedness is
-- head-and-tail relatedness.
#test ∀ (R : BRel) (x x' : Bool) (l l' : List Bool),
  listRelE R (x :: l) (x' :: l') = (R x x' && listRelE R l l')

-- `fun_relI`/`fun_relD`: two related functions take related arguments
-- to related results, and that property is what membership *is*.
#test ∀ (A B : BRel) (p p' : Bool × Bool) (a a' : Bool),
  funRelE A B (ofPair p) (ofPair p') = true → A a a' = true →
    B (ofPair p a) (ofPair p' a') = true

-- `fun_rel_mono`: contravariant in the domain, covariant in the codomain.
#test ∀ (A A' B B' : BRel) (p p' : Bool × Bool),
  subB A' A = true → subB B B' = true →
    funRelE A B (ofPair p) (ofPair p') = true → funRelE A' B' (ofPair p) (ofPair p') = true

-- `prod_rel_mono`.
#test ∀ (R₁ R₁' R₂ R₂' : BRel) (a b a' b' : Bool),
  subB R₁ R₁' = true → subB R₂ R₂' = true →
    prodRelE R₁ R₂ ((a, b), (a', b')) = true → prodRelE R₁' R₂' ((a, b), (a', b')) = true

-- `prod_rel_def`: membership is componentwise.
#test ∀ (R₁ R₂ : BRel) (a b a' b' : Bool),
  prodRelE R₁ R₂ ((a, b), (a', b')) = (R₁ a a' && R₂ b b')

-- `option_rel_mono`, and `option_rel_def`'s `None` clause.
#test ∀ (R R' : BRel) (a a' : Bool),
  subB R R' = true → optionRelE R (some a, some a') = true →
    optionRelE R' (some a, some a') = true

#test ∀ R : BRel, optionRelE R (none, none) = true

-- `sum_rel_mono`, on both injections.
#test ∀ (Rl Rl' Rr Rr' : BRel) (a a' : Bool),
  subB Rl Rl' = true → subB Rr Rr' = true →
    sumRelE Rl Rr (Sum.inl a, Sum.inl a') = true →
      sumRelE Rl' Rr' (Sum.inl a, Sum.inl a') = true

#test ∀ (Rl Rl' Rr Rr' : BRel) (b b' : Bool),
  subB Rl Rl' = true → subB Rr Rr' = true →
    sumRelE Rl Rr (Sum.inr b, Sum.inr b') = true →
      sumRelE Rl' Rr' (Sum.inr b, Sum.inr b') = true

-- `br_singleValued`: `br` never relates one concrete value to two
-- abstract ones.
#test ∀ (m n n' : ℕ), decide ((m, n) ∈ br (fun k : ℕ => k / 2) (fun k => k % 2 = 0)) = true →
  decide ((m, n') ∈ br (fun k : ℕ => k / 2) (fun k => k % 2 = 0)) = true → n = n'

end Sanity

end Lax13Proofs.Refine
