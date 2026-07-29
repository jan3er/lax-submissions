import Lax13Proofs.Refine.NREST.Sanity
import Lax13Proofs.Refine.Autoref.Relators

/-!
Data refinement for `NRest`: the concretisation operator `⇓R`.

Port of `thys/nrest/Data_Refinement.thy` of `isabelle_llvm_time`
(Haslbeck–Lammich, ESOP'21 artifact) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1,
github.com/lammich/isabelle_llvm_time @ 42dd7f5. The definitions and the
lemma statements ported here, verbatim from that file:

```isabelle
definition conc_fun  ("⇓") where
  "conc_fun R m ≡ case m of FAILi ⇒ FAILT | REST X ⇒ REST (λc. Sup {X a| a. (c,a)∈R})"

definition abs_fun ("⇑") where
  "abs_fun R m ≡ case m of FAILi ⇒ FAILT
    | REST X ⇒ if dom X⊆Domain R then REST (λa. Sup {X c| c. (c,a)∈R}) else FAILT"

lemma conc_fun_FAIL[simp]: "⇓R FAILT = FAILT" and
      conc_fun_RES: "⇓R (REST X) = REST (λc. Sup {X a| a. (c,a)∈R})"
lemma abs_fun_simps[simp]:
  "⇑R FAILT = FAILT"
  "dom X⊆Domain R ⟹ ⇑R (REST X) = REST (λa. Sup {X c| c. (c,a)∈R})"
  "¬(dom X⊆Domain R) ⟹ ⇑R (REST X) = FAILT"
lemma conc_fun_spec_ne_FAIL[simp]: "⇓R (SPECT M) ≠ FAILT"
lemma nrest_Rel_mono:
  fixes A :: "('a,'b::{complete_lattice,monoid_add}) nrest"
  shows "A ≤ B ⟹ ⇓ R A ≤ ⇓ R B"
lemma conc_fun_mono[simp, intro!]:
  shows "mono ((⇓R)::('b, enat) nrest ⇒ ('a, enat) nrest)"
lemma conc_fun_R_mono: fixes M :: "(_,enat) nrest"
  assumes "R ⊆ R'" shows "⇓R M ≤ ⇓R' M"
lemma pw_conc_nofail[refine_pw_simps]: "nofailT (⇓R S) = nofailT S"
lemma conc_fun_fail_iff[simp]: fixes S :: "(_,enat) nrest"
  shows "⇓R S = FAILT ⟷ S=FAILT"  "FAILT = ⇓R S ⟷ S=FAILT"
lemma conc_Id[simp]: "⇓Id = id"
lemma conc_fun_complete_lattice_chain:
  fixes M :: "(_,'b::{complete_lattice,monoid_add}) nrest"
  shows "⇓R (⇓S M) = ⇓(R O S) M"
lemma conc_trans[trans]:
  fixes B :: "(_,'a::{complete_lattice,monoid_add}) nrest"
  assumes A: "C ≤ ⇓R B" and B: "B ≤ ⇓R' A"
  shows "C ≤ ⇓R (⇓R' A)"
lemma RETURNT_refine: assumes "(x,x')∈R" shows "RETURNT x ≤ ⇓R (RETURNT x')"
lemma conc_fun_consume:
  fixes M :: "('c, (_,enat) acost ) nrest"
  shows "⇓R (consume M t) = consume (⇓R M) t"
lemma consume_refine_easy:
  fixes M :: "('e, ('b, enat) acost) nrest"
  shows "⟦t ≤ t'; M ≤ ⇓ R M'⟧ ⟹ consume M t ≤ ⇓R (consume M' t')"
lemma bindT_refine:
  fixes R' :: "('a×'b) set" and R::"('c×'d) set" and M :: "(_,enat) nrest"
  assumes R1: "M ≤ ⇓ R' M'"
  assumes R2: "⋀x x'. ⟦ (x,x')∈R' ⟧ ⟹ f x ≤ ⇓ R (f' x')"
  shows "bindT M (λx. f x) ≤ ⇓ R (bind M' (λx'. f' x'))"
lemma bindT_conc_acost_refine:
  fixes M :: "(_,(_,enat)acost) nrest" and R' :: "('a×'b) set" and R::"('c×'d) set"
  assumes R1: "M ≤ ⇓ R' M'"
  assumes R2: "⋀x x' t . ⟦ (x,x')∈R'; nofailT M; nofailT M' ⟧ ⟹ f x ≤ ⇓ R (f' x')"
  shows "bindT M (λx. f x) ≤ ⇓ R (bindT M' (λx'. f' x'))"
lemma SPECT_refines_conc_fun':
  assumes a: "⋀m c.  M = SPECT m ⟹ c ∈ dom n ⟹ (∃a. (c,a)∈R ∧ n c ≤ m a)"
  shows "SPECT n ≤ ⇓ R M"
lemma SPECT_refines_conc_fun:
  assumes a: "⋀m c. (∃a. (c,a)∈R ∧ n c ≤ m a)"
  shows "SPECT n ≤ ⇓ R (SPECT m)"
lemma Sup_sv: fixes m :: "'b ⇒ enat option"
  shows "(c, a') ∈ R ⟹  Sup {m a| a. (c,a) ∈ R} = m a'"       (in a single_valued context)
lemma build_rel_SPEC_conv: fixes T :: "_ ⇒ ((_,enat)acost)"
  assumes "⋀x. T (α x) = T' x"
  shows "⇓(br α I) (SPEC Φ T) = SPEC (λx. I x ∧ Φ (α x)) T'"
lemma conc_fun_br: "⇓ (br α I1) (SPECT (emb I2 t)) = (SPECT (emb (λx. I1 x ∧ I2 (α x)) t))"
definition nrest_rel where "⟨R⟩nrest_rel ≡ {(c,a). c ≤ ⇓R a}"
lemma nrest_relD / nrest_relI / nrest_rel_comp:
  "⟨A⟩nrest_rel O ⟨B⟩nrest_rel = ⟨A O B⟩nrest_rel"
lemma param_RETURNT[param]: "(RETURNT,RETURNT) ∈ R → ⟨R⟩nrest_rel"
```

The relation constructor `br` is *used* by `Data_Refinement.thy` but
defined one layer down, in AFP `Automatic_Refinement`
(`Parametricity/Relators.thy`, Isabelle2025-2 — design record §1):

```isabelle
definition build_rel where "build_rel α I ≡ {(c,a) . a=α c ∧ I c}"
abbreviation "br≡build_rel"
lemma in_br_conv: "(c,a)∈br α I ⟷ a=α c ∧ I c"
lemma br_id[simp]: "br id (λ_. True) = Id"
lemma br_chain: "(build_rel β J) O (build_rel α I) = build_rel (α∘β) (λs. J s ∧ I (β s))"
lemma br_sv[simp, intro!,relator_props]: "single_valued (br α I)"
```

## Substrate deltas, each flagged

**S1 — relations.** `R : Set (β × α)`, concrete component first, with
membership statements `(c, a) ∈ R`: the source's own spelling
(design record F3). `⇓R : NRest α γ → NRest β γ` therefore takes an
*abstract* program to a *concrete* one.

**S2 — relation composition, single-valuedness and `br` live in
`Autoref/Relators.lean`.** `relComp` (Isabelle's `R O S`),
`SingleValued` (Isabelle's `single_valued`), `br` and the pure-relation
lemmas about them (`mem_relComp`, `mem_br_iff`, `mem_br`, `br_id`,
`br_chain`, `br_singleValued`, `singleValued_diagonal`,
`NRest.singleValued_relComp`) belong to `Autoref/Relators.lean` by the
design record's module map (§7), but `conc_fun_chain`, `nrest_rel_comp`
and the `_sv` lemmas of *this* source file cannot be stated without
them. P1 therefore defined them here and recorded that P2 should move
them rather than restate them; **P2 wave A did the move**, with every
fully qualified name unchanged, and this file now reaches them through
`import Lax13Proofs.Refine.Autoref.Relators`. Nothing stated below
changed.

**S3 — `Id` is `Set.diagonal`.** Isabelle's `Id = {(a,a)|a}` is
mathlib's `Set.diagonal`; `conc_Id` is stated with that name.

**S4 — `dom X ⊆ Domain R` is spelled out.** In `abs_fun`'s side
condition, `dom X` is `{c | X c ≠ ⊥}` and `Domain R` is `{c | ∃a. (c,a) ∈ R}`,
so the condition reads `∀ c, X c ≠ ⊥ → ∃ a, (c, a) ∈ R`. No `Domain`
operator is introduced for one use.

**S5 — carriers of the `enat`-only statements.** Several lemmas the
source states `fixes M :: "(_,enat) nrest"` are stated here at every
`[CompleteLattice γ]`, because their pointwise-free proofs need nothing
more; the source's `enat` there is an artefact of proving them through
its `pw_le_iff`/`refine_pw_simps` route. This is visible *inside the
source itself*: it proves `conc_fun_chain` at `enat` and then
`conc_fun_complete_lattice_chain`, the same statement, generally. The
lemmas affected: `concFun_monotone`, `concFun_R_mono`,
`concFun_eq_fail_iff`, `buildRel_spec_conv`, `concFun_br`. Lemmas whose
proofs really do need adding a cost to commute with suprema
(`concFun_consume`, `consume_refine_easy`, the two `bindT` rules) are
stated at the source's own carriers, `ℕ∞` and `ACost κ ℕ∞`, following
`Pw.lean`'s `AddSupContinuousB` pattern (design record F7).

**S6 — `pw_conc_inres` is NOT ported, and the same-carrier reading of it
is false.** The source's `pw_conc_inres` reads
`inresT (⇓R S') s t = (nofailT S' ⟶ (∃s'. (s,s')∈R ∧ inresT S' s' t))`,
where `inresT`'s cost argument crosses carriers through the source's
`lift` (`inresT S x t ≡ REST [x ↦ lift t] ≤ S`, `lift : nat ⇒ enat` at
this use); the finiteness of `t` is exactly what the source's proof
consumes (`Sup_enat_less2`, `Sup_finite_enat`). `Pw.lean` ports the
*same-carrier* instance of `inresT` (`lift = id`, module header there),
and at that reading the left-to-right direction is refutable: take
`α := ℕ`, `β := Unit`, `γ := ℕ∞`, `R := Set.univ`, `X n := (n : ℕ∞)`
and `t := ⊤`; then `⇓R (rest X) ()` is `sSup {(n : ℕ∞) | n : ℕ} = ⊤`, so
`inresT (⇓R (rest X)) () ⊤` holds, while no `n` has `⊤ ≤ (n : ℕ∞)`. The
always-true direction is ported below as `inresT_concFun_of_mem`; the
full equivalence waits for the nat-indexed `inresT` seam. This is a
substrate mismatch, not a defect of the source.

**S7 — not ported from this file.** `RECT_refine` and `WHILET_refine`
(they need `RECT`/`whileT`, which land with `Rec.lean`/`Combinators.lean`);
`project_acost_conc_fun_commute` and `pw_acost_nrest_rel_iff` (they need
`project_acost`, not in the frozen `Basic.lean`/`Pw.lean` API);
`param_bind` and `param_ASSERT_bind` (they need `fun_rel`/`bool_rel`,
i.e. P2's relator zoo); `conc_fun_RES_sv` and `conc_fun_chain_sv` — the
first is restated below without Hilbert's `THE`
(`concFun_rest_apply_of_singleValued`), the second is the special case
of the general `concFun_chain`. Everything the source states inside
`notepad`, `experiment` or comment blocks is *not* part of its API and
is not ported.
-/

namespace Lax13Proofs.Refine

variable {α β δ γ κ : Type}

namespace NRest

/-! ### The concretisation operator `⇓R`

`conc_fun`, its equation lemmas, and the supremum form every proof below
reasons through. -/

/-- The source's `conc_fun R m`, written `⇓R m`: the concrete program
that, at each concrete result `c`, offers the best cost any `R`-related
abstract result was offered at. `R`'s first component is the concrete
one (design record F3). -/
noncomputable def concFun [CompleteLattice γ] (R : Set (β × α)) (m : NRest α γ) : NRest β γ :=
  match m with
  | .fail => .fail
  | .rest X => .rest (fun c => sSup {u | ∃ a, (c, a) ∈ R ∧ u = X a})

@[simp] theorem concFun_fail [CompleteLattice γ] (R : Set (β × α)) :
    concFun R (fail : NRest α γ) = fail := rfl

@[simp] theorem concFun_rest [CompleteLattice γ] (R : Set (β × α)) (X : α → WithBot γ) :
    concFun R (rest X) = rest (fun c => sSup {u | ∃ a, (c, a) ∈ R ∧ u = X a}) := rfl

/-- The result map of `⇓R (rest X)`. Not a definition of the source —
it has no name for it — but every lattice argument below is about this
function, so it gets one here. -/
noncomputable def concMap [CompleteLattice γ] (R : Set (β × α)) (X : α → WithBot γ) :
    β → WithBot γ :=
  fun c => ⨆ a, ⨆ _ : (c, a) ∈ R, X a

theorem concMap_apply [CompleteLattice γ] (R : Set (β × α)) (X : α → WithBot γ) (c : β) :
    concMap R X c = ⨆ a, ⨆ _ : (c, a) ∈ R, X a := rfl

/-- The source's set comprehension `{X a | a. (c,a) ∈ R}`, as an
indexed supremum. -/
theorem sSup_relImage [CompleteLattice γ] (R : Set (β × α)) (X : α → WithBot γ) (c : β) :
    sSup {u | ∃ a, (c, a) ∈ R ∧ u = X a} = concMap R X c := by
  refine le_antisymm (sSup_le ?_) (iSup_le fun a => iSup_le fun ha => le_sSup ⟨a, ha, rfl⟩)
  rintro u ⟨a, ha, rfl⟩
  exact le_iSup_of_le a (le_iSup_of_le ha le_rfl)

/-- `⇓R` on a `rest`, through its result map. -/
theorem concFun_rest_eq [CompleteLattice γ] (R : Set (β × α)) (X : α → WithBot γ) :
    concFun R (rest X) = rest (concMap R X) := by
  rw [concFun_rest]
  congr 1
  funext c
  exact sSup_relImage R X c

/-- `concMap` is monotone in the map. -/
theorem concMap_mono [CompleteLattice γ] {R : Set (β × α)} {X Y : α → WithBot γ} (h : X ≤ Y) :
    concMap R X ≤ concMap R Y :=
  fun _ => iSup_mono fun a => iSup_mono fun _ => h a

/-- `concMap` is monotone in the relation. -/
theorem concMap_R_mono [CompleteLattice γ] {R R' : Set (β × α)} (h : R ⊆ R')
    (X : α → WithBot γ) : concMap R X ≤ concMap R' X :=
  fun _ => iSup_mono fun _ => iSup_le fun ha => le_iSup_of_le (h ha) le_rfl

/-- `concMap` distributes over suprema: it is a supremum, and suprema
commute. -/
theorem concMap_iSup [CompleteLattice γ] (R : Set (β × α)) {ι : Sort*}
    (X : ι → α → WithBot γ) : concMap R (⨆ i, X i) = ⨆ i, concMap R (X i) := by
  funext c
  rw [concMap_apply, iSup_apply]
  simp only [concMap_apply, iSup_apply]
  rw [iSup_comm]
  exact iSup_congr fun a => iSup_comm

/-- The source's `conc_fun_spec_ne_FAIL`. -/
@[simp] theorem concFun_ne_fail [CompleteLattice γ] (R : Set (β × α)) (X : α → WithBot γ) :
    concFun R (rest X) ≠ fail := rest_ne_fail _

/-- The source's `conc_fun_spec_ne_FAIL`, at a `spec`. -/
@[simp] theorem concFun_spec_ne_fail [CompleteLattice γ] (R : Set (β × α)) (P : α → Prop)
    (t : α → γ) : concFun R (spec P t) ≠ fail := rest_ne_fail _

/-- The source's `pw_conc_nofail`. -/
@[simp] theorem nofailT_concFun [CompleteLattice γ] (R : Set (β × α)) (S : NRest α γ) :
    nofailT (concFun R S) ↔ nofailT S := by
  cases S <;> simp [nofailT_iff]

/-- The source's `conc_fun_fail_iff` (delta S5). -/
@[simp] theorem concFun_eq_fail_iff [CompleteLattice γ] {R : Set (β × α)} {S : NRest α γ} :
    concFun R S = fail ↔ S = fail := by
  cases S <;> simp

/-! ### The abstraction operator `⇑R` -/

open Classical in
/-- The source's `abs_fun R m`, written `⇑R m`: the abstract program a
concrete one witnesses — failing outright if the concrete program can
produce a result no abstract result is related to (delta S4). -/
noncomputable def absFun [CompleteLattice γ] (R : Set (β × α)) (m : NRest β γ) : NRest α γ :=
  match m with
  | .fail => .fail
  | .rest X =>
    if (∀ c, X c ≠ ⊥ → ∃ a, (c, a) ∈ R) then
      .rest (fun a => sSup {u | ∃ c, (c, a) ∈ R ∧ u = X c})
    else .fail

@[simp] theorem absFun_fail [CompleteLattice γ] (R : Set (β × α)) :
    absFun R (fail : NRest β γ) = fail := rfl

@[simp] theorem absFun_rest_of_dom [CompleteLattice γ] {R : Set (β × α)} {X : β → WithBot γ}
    (h : ∀ c, X c ≠ ⊥ → ∃ a, (c, a) ∈ R) :
    absFun R (rest X) = rest (fun a => sSup {u | ∃ c, (c, a) ∈ R ∧ u = X c}) := by
  simp only [absFun, if_pos h]

@[simp] theorem absFun_rest_of_not_dom [CompleteLattice γ] {R : Set (β × α)} {X : β → WithBot γ}
    (h : ¬ (∀ c, X c ≠ ⊥ → ∃ a, (c, a) ∈ R)) : absFun R (rest X) = fail := by
  simp only [absFun, if_neg h]

/-! ### Monotonicity -/

/-- The source's `nrest_Rel_mono`: `⇓R` is monotone in the program. -/
theorem concFun_mono [CompleteLattice γ] {R : Set (β × α)} {A B : NRest α γ} (h : A ≤ B) :
    concFun R A ≤ concFun R B := by
  cases B with
  | fail => simp
  | rest Y =>
    cases A with
    | fail => simp at h
    | rest X =>
      rw [concFun_rest_eq, concFun_rest_eq, rest_le_rest_iff]
      exact concMap_mono h

/-- The source's `conc_fun_mono`, bundled (delta S5). -/
theorem concFun_monotone [CompleteLattice γ] (R : Set (β × α)) :
    Monotone (concFun R : NRest α γ → NRest β γ) := fun _ _ h => concFun_mono h

/-- The source's `conc_fun_R_mono`: `⇓R` is monotone in the relation
(delta S5). -/
theorem concFun_R_mono [CompleteLattice γ] {R R' : Set (β × α)} (h : R ⊆ R')
    (M : NRest α γ) : concFun R M ≤ concFun R' M := by
  cases M with
  | fail => simp
  | rest X =>
    rw [concFun_rest_eq, concFun_rest_eq, rest_le_rest_iff]
    exact concMap_R_mono h X

/-! ### `⇓R` commutes with suprema

Not a lemma of the source (it proves the consequences through its
pointwise machinery instead), but it is the one fact every composite
rule below rests on, and it is immediate here: `⇓R` is a supremum, and
suprema commute. -/

/-- `⇓R` distributes over arbitrary suprema. -/
theorem concFun_iSup [CompleteLattice γ] (R : Set (β × α)) {ι : Sort*} (m : ι → NRest α γ) :
    concFun R (⨆ i, m i) = ⨆ i, concFun R (m i) := by
  by_cases hf : ∃ i, m i = fail
  · obtain ⟨i, hi⟩ := hf
    rw [iSup_eq_fail_iff.mpr ⟨i, hi⟩, iSup_eq_fail_iff.mpr ⟨i, by rw [hi]; rfl⟩, concFun_fail]
  · simp only [not_exists] at hf
    have hrest : ∀ i, m i = rest (resultsOf (m i)) := fun i => eq_rest_resultsOf (hf i)
    rw [show (⨆ i, m i) = ⨆ i, rest (resultsOf (m i)) from iSup_congr hrest, iSup_rest,
      concFun_rest_eq,
      show (⨆ i, concFun R (m i)) = ⨆ i, rest (concMap R (resultsOf (m i))) from
        iSup_congr fun i => by rw [hrest i, concFun_rest_eq, resultsOf_rest],
      iSup_rest, concMap_iSup]

/-! ### Identity and chaining -/

/-- The source's `conc_Id`, at `Id = Set.diagonal` (delta S3). -/
@[simp] theorem concFun_diagonal [CompleteLattice γ] (m : NRest α γ) :
    concFun (Set.diagonal α) m = m := by
  cases m with
  | fail => rfl
  | rest X =>
    rw [concFun_rest_eq, rest_inj_iff]
    funext c
    rw [concMap_apply]
    refine le_antisymm (iSup_le fun a => iSup_le fun ha => ?_) ?_
    · rw [show a = c from (ha : c = a).symm]
    · exact le_iSup_of_le c (le_iSup_of_le (rfl : c = c) le_rfl)

/-- The source's `conc_Id`, as the function equation it states. -/
theorem concFun_id [CompleteLattice γ] :
    (concFun (Set.diagonal α) : NRest α γ → NRest α γ) = id := by
  funext m; exact concFun_diagonal m

/-- The source's `conc_fun_complete_lattice_chain` (and, at `enat`, its
`conc_fun_chain`): chaining two concretisations is concretising along
the composed relation. Note the composition order: `⇓R (⇓S m)` first
undoes `S`, so the composite relates the *outer* concrete side to the
abstract one as `R O S` does. -/
theorem concFun_chain [CompleteLattice γ] (R : Set (β × δ)) (S : Set (δ × α))
    (M : NRest α γ) : concFun R (concFun S M) = concFun (relComp R S) M := by
  cases M with
  | fail => rfl
  | rest X =>
    rw [concFun_rest_eq, concFun_rest_eq, concFun_rest_eq, rest_inj_iff]
    funext c
    simp only [concMap_apply]
    refine le_antisymm (iSup_le fun b => iSup_le fun hb => iSup_le fun a => iSup_le fun ha => ?_)
      (iSup_le fun a => iSup_le fun h => ?_)
    · exact le_iSup_of_le a (le_iSup_of_le ⟨b, hb, ha⟩ le_rfl)
    · obtain ⟨b, hb, ha⟩ := h
      exact le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le a (le_iSup_of_le ha le_rfl)))

/-- The source's `conc_trans`. -/
theorem concFun_trans [CompleteLattice γ] {R : Set (β × δ)} {R' : Set (δ × α)}
    {C : NRest β γ} {B : NRest δ γ} {A : NRest α γ}
    (hA : C ≤ concFun R B) (hB : B ≤ concFun R' A) : C ≤ concFun R (concFun R' A) :=
  hA.trans (concFun_mono hB)

/-! ### Single-valued relations -/

/-- The source's `Sup_sv`: along a single-valued relation the supremum
of the source's set comprehension is the single value it contains. -/
theorem sSup_relImage_of_singleValued [CompleteLattice γ] {R : Set (β × α)}
    (hR : SingleValued R) (X : α → WithBot γ) {c : β} {a : α} (ha : (c, a) ∈ R) :
    sSup {u | ∃ a, (c, a) ∈ R ∧ u = X a} = X a := by
  refine le_antisymm (sSup_le ?_) (le_sSup ⟨a, ha, rfl⟩)
  rintro u ⟨a', ha', rfl⟩
  rw [hR c a' a ha' ha]

/-- The source's `conc_fun_RES_sv`, restated without Hilbert's `THE`
(delta S7): along a single-valued relation, `⇓R` reads off the cost of
the unique related abstract result. -/
theorem concFun_rest_apply_of_singleValued [CompleteLattice γ] {R : Set (β × α)}
    (hR : SingleValued R) (X : α → WithBot γ) {c : β} {a : α} (ha : (c, a) ∈ R) :
    resultsOf (concFun R (rest X)) c = X a := by
  rw [concFun_rest, resultsOf_rest, sSup_relImage_of_singleValued hR X ha]

/-- Off the domain of `R`, `⇓R` offers nothing. -/
theorem concFun_rest_apply_of_notMem_domain [CompleteLattice γ] {R : Set (β × α)}
    (X : α → WithBot γ) {c : β} (hc : ∀ a, (c, a) ∉ R) :
    resultsOf (concFun R (rest X)) c = ⊥ := by
  rw [concFun_rest, resultsOf_rest]
  refine le_antisymm (sSup_le ?_) bot_le
  rintro u ⟨a, ha, rfl⟩
  exact absurd ha (hc a)

/-! ### Refinement of `returnT`, `rest` and `spec` -/

/-- The source's `RETURNT_refine`. -/
theorem returnT_refine [CompleteLattice γ] [Zero γ] {R : Set (β × α)} {x : β} {x' : α}
    (h : (x, x') ∈ R) : (returnT x : NRest β γ) ≤ concFun R (returnT x') := by
  show rest (single x (0 : WithBot γ)) ≤ concFun R (rest (single x' (0 : WithBot γ)))
  rw [concFun_rest_eq, rest_le_rest_iff]
  intro c
  by_cases hc : c = x
  · subst hc
    exact le_iSup_of_le x' (le_iSup_of_le h (by simp))
  · simp [hc]

/-- The source's `SPECT_refines_conc_fun'`. `dom n` is `{c | n c ≠ ⊥}`
(delta S4). -/
theorem rest_refines_concFun' [CompleteLattice γ] {R : Set (β × α)} {n : β → WithBot γ}
    {M : NRest α γ}
    (h : ∀ X, M = rest X → ∀ c, n c ≠ ⊥ → ∃ a, (c, a) ∈ R ∧ n c ≤ X a) :
    rest n ≤ concFun R M := by
  cases M with
  | fail => simp
  | rest X =>
    rw [concFun_rest_eq, rest_le_rest_iff]
    intro c
    by_cases hc : n c = ⊥
    · simp [hc]
    · obtain ⟨a, ha, hle⟩ := h X rfl c hc
      exact hle.trans (le_iSup_of_le a (le_iSup_of_le ha le_rfl))

/-- The source's `SPECT_refines_conc_fun`. -/
theorem rest_refines_concFun [CompleteLattice γ] {R : Set (β × α)} {n : β → WithBot γ}
    {m : α → WithBot γ} (h : ∀ c, ∃ a, (c, a) ∈ R ∧ n c ≤ m a) :
    rest n ≤ concFun R (rest m) :=
  rest_refines_concFun' fun X hX c _ => by cases rest_inj_iff.mp hX; exact h c

/-- The direction of the source's `pw_conc_inres` that survives the
same-carrier reading of `inresT` (delta S6). -/
theorem inresT_concFun_of_mem [CompleteLattice γ] {R : Set (β × α)} {S : NRest α γ}
    {c : β} {a : α} {t : γ} (ha : (c, a) ∈ R) (h : inresT S a t) : inresT (concFun R S) c t := by
  cases S with
  | fail => simp
  | rest X =>
    rw [inresT_rest] at h
    rw [concFun_rest_eq, inresT_rest, concMap_apply]
    exact h.trans (le_iSup_of_le a (le_iSup_of_le ha le_rfl))

/-! ### Interaction with `consume` and `bindT`

These are the rules whose proofs really need adding a cost to commute
with suprema, so they follow `Pw.lean`'s pattern exactly: a
hypothesis-carrying auxiliary, then the source's statements at the
source's own carriers (design record F7). -/

/-- The result-map half of the source's `conc_fun_consume`: charging a
cost commutes with `concMap`, which is exactly the continuity of left
addition over suprema. -/
theorem concMap_add_of [CompleteLattice γ] [AddCommMonoid γ] (hc : AddSupContinuousB γ)
    (R : Set (β × α)) (X : α → WithBot γ) (t : γ) :
    concMap R (fun x => (t : WithBot γ) + X x) = fun c => (t : WithBot γ) + concMap R X c := by
  funext c
  simp only [concMap_apply]
  rw [hc.add_iSup]
  exact iSup_congr fun a => (hc.add_iSup (t : WithBot γ) (fun _ : (c, a) ∈ R => X a)).symm

/-- The source's `conc_fun_consume`, with the continuity hypothesis
explicit. -/
theorem concFun_consume_of [CompleteLattice γ] [AddCommMonoid γ] (hc : AddSupContinuousB γ)
    (R : Set (β × α)) (M : NRest α γ) (t : γ) :
    concFun R (consume M t) = consume (concFun R M) t := by
  cases M with
  | fail => rfl
  | rest X =>
    rw [consume_rest', concFun_rest_eq, concFun_rest_eq, consume_rest', concMap_add_of hc]

/-- `⇓R` and `consumeB`, the `WithBot`-costed form of
`concFun_consume_of`. -/
theorem concFun_consumeB_of [CompleteLattice γ] [AddCommMonoid γ] (hc : AddSupContinuousB γ)
    (R : Set (β × α)) (M : NRest α γ) (u : WithBot γ) :
    concFun R (consumeB M u) = consumeB (concFun R M) u := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · rw [consumeB_bot, consumeB_bot, bot_eq_rest_bot, concFun_rest_eq, bot_eq_rest_bot,
      rest_inj_iff]
    funext c
    refine le_antisymm (iSup_le fun a => iSup_le fun _ => le_rfl) bot_le
  · rw [consumeB_coe, consumeB_coe, concFun_consume_of hc]

/-- The source's `conc_fun_consume`, at the source's carrier
`(_, enat) acost`. -/
theorem concFun_consume_acost (R : Set (β × α)) (M : NRest α (ACost κ ℕ∞)) (t : ACost κ ℕ∞) :
    concFun R (consume M t) = consume (concFun R M) t :=
  concFun_consume_of addSupContinuousB_acost R M t

/-- The source's `conc_fun_consume`, at `enat`. -/
theorem concFun_consume (R : Set (β × α)) (M : NRest α ℕ∞) (t : ℕ∞) :
    concFun R (consume M t) = consume (concFun R M) t :=
  concFun_consume_of addSupContinuousB_enat R M t

/-- The source's `consume_refine_easy`, with the continuity hypothesis
explicit. -/
theorem consume_refine_easy_of [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    (hc : AddSupContinuousB γ) {R : Set (β × α)} {M : NRest β γ} {M' : NRest α γ} {t t' : γ}
    (ht : t ≤ t') (hM : M ≤ concFun R M') : consume M t ≤ concFun R (consume M' t') := by
  rw [concFun_consume_of hc]
  exact consume_mono hM ht

/-- The source's `consume_refine_easy`, at its carrier. -/
theorem consume_refine_easy {R : Set (β × α)} {M : NRest β (ACost κ ℕ∞)}
    {M' : NRest α (ACost κ ℕ∞)} {t t' : ACost κ ℕ∞} (ht : t ≤ t') (hM : M ≤ concFun R M') :
    consume M t ≤ concFun R (consume M' t') :=
  consume_refine_easy_of addSupContinuousB_acost ht hM

/-- The source's `bindT_refine`/`bindT_conc_acost_refine`, with the
continuity hypothesis explicit. Note the side conditions the source
asks for and the ones it does *not*: `R` and `R'` are arbitrary
relations, **not** required to be single-valued. -/
theorem bindT_refine_of {α' β' : Type} [CompleteLattice γ] [AddCommMonoid γ]
    [IsOrderedAddMonoid γ] (hc : AddSupContinuousB γ)
    {R' : Set (β × α)} {R : Set (β' × α')} {M : NRest β γ} {M' : NRest α γ}
    {f : β → NRest β' γ} {f' : α → NRest α' γ}
    (hM : M ≤ concFun R' M') (hf : ∀ x x', (x, x') ∈ R' → f x ≤ concFun R (f' x')) :
    bindT M f ≤ concFun R (bindT M' f') := by
  cases M' with
  | fail => simp
  | rest X' =>
    cases M with
    | fail => simp at hM
    | rest X =>
      rw [bindT_rest_eq_iSup, bindT_rest_eq_iSup, concFun_iSup]
      refine iSup_le fun c => ?_
      have hXc : X c ≤ ⨆ a, ⨆ _ : (c, a) ∈ R', X' a :=
        rest_le_rest_iff.mp (hM.trans_eq (concFun_rest_eq R' X')) c
      calc consumeB (f c) (X c) ≤ consumeB (f c) (⨆ a, ⨆ _ : (c, a) ∈ R', X' a) :=
            consumeB_mono le_rfl hXc
        _ = ⨆ a, ⨆ _ : (c, a) ∈ R', consumeB (f c) (X' a) := by
            rw [consumeB_iSup_cost hc]
            exact iSup_congr fun a => consumeB_iSup_cost hc _ _
        _ ≤ ⨆ a, concFun R (consumeB (f' a) (X' a)) := by
            refine iSup_mono fun a => iSup_le fun ha => ?_
            rw [concFun_consumeB_of hc]
            exact consumeB_mono (hf c a ha) le_rfl

/-- The source's `bindT_refine`, at its carrier `enat`. -/
theorem bindT_refine {α' β' : Type} {R' : Set (β × α)} {R : Set (β' × α')}
    {M : NRest β ℕ∞} {M' : NRest α ℕ∞} {f : β → NRest β' ℕ∞} {f' : α → NRest α' ℕ∞}
    (hM : M ≤ concFun R' M') (hf : ∀ x x', (x, x') ∈ R' → f x ≤ concFun R (f' x')) :
    bindT M f ≤ concFun R (bindT M' f') :=
  bindT_refine_of addSupContinuousB_enat hM hf

/-- The source's `bindT_conc_acost_refine`, at its carrier
`(_, enat) acost`. The source's extra `nofailT M`, `nofailT M'`
hypotheses are available to the caller and are simply unused: they are
consequences of `hM` in the only case where the goal has content. -/
theorem bindT_conc_acost_refine {α' β' : Type} {R' : Set (β × α)} {R : Set (β' × α')}
    {M : NRest β (ACost κ ℕ∞)} {M' : NRest α (ACost κ ℕ∞)}
    {f : β → NRest β' (ACost κ ℕ∞)} {f' : α → NRest α' (ACost κ ℕ∞)}
    (hM : M ≤ concFun R' M')
    (hf : ∀ x x', (x, x') ∈ R' → nofailT M → nofailT M' → f x ≤ concFun R (f' x')) :
    bindT M f ≤ concFun R (bindT M' f') := by
  cases M' with
  | fail => simp
  | rest X' =>
    cases M with
    | fail => simp at hM
    | rest X =>
      exact bindT_refine_of addSupContinuousB_acost hM
        fun x x' hx => hf x x' hx (nofailT_rest X) (nofailT_rest X')

/-! ### `br` and specifications -/

/-- The source's `build_rel_SPEC_conv` (delta S5). -/
theorem buildRel_spec_conv [CompleteLattice γ] {f : β → α} {I : β → Prop} {Φ : α → Prop}
    {T : α → γ} {T' : β → γ} (h : ∀ x, T (f x) = T' x) :
    concFun (br f I) (spec Φ T) = spec (fun x => I x ∧ Φ (f x)) T' := by
  classical
  rw [spec, concFun_rest, spec, rest_inj_iff]
  funext c
  by_cases hI : I c
  · have hset : {u : WithBot γ | ∃ a, (c, a) ∈ br f I ∧ u = if Φ a then ((T a : γ) : WithBot γ)
        else ⊥} = {if Φ (f c) then ((T (f c) : γ) : WithBot γ) else ⊥} := by
      ext u
      constructor
      · rintro ⟨a, ha, rfl⟩
        have : a = f c := (mem_br_iff.mp ha).1
        subst this
        rfl
      · rintro rfl; exact ⟨f c, mem_br rfl hI, rfl⟩
    rw [hset, sSup_singleton, h c]
    by_cases hΦ : Φ (f c) <;> simp [hΦ, hI]
  · have hset : {u : WithBot γ | ∃ a, (c, a) ∈ br f I ∧ u = if Φ a then ((T a : γ) : WithBot γ)
        else ⊥} = ∅ := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      rintro a ha
      exact hI (mem_br_iff.mp ha.1).2
    rw [hset, sSup_empty]
    simp [hI]

/-- The source's `conc_fun_br`. The source writes its right-hand side
with `emb`; `SPECT (emb' Q T) = SPEC Q T` is the source's own
`SPEC_REST_emb'_conv`, so the statement is spelled with `spec`, whose
cost function is constant here. -/
theorem concFun_br [CompleteLattice γ] (f : β → α) (I₁ : β → Prop) (I₂ : α → Prop) (t : γ) :
    concFun (br f I₁) (spec I₂ (fun _ => t)) = spec (fun x => I₁ x ∧ I₂ (f x)) (fun _ => t) :=
  buildRel_spec_conv fun _ => rfl

/-! ### The refinement relator `nrest_rel` -/

/-- The source's `nrest_rel`: the relation between programs that `⇓R`
induces. -/
def nrestRel [CompleteLattice γ] (R : Set (β × α)) : Set (NRest β γ × NRest α γ) :=
  {p | p.1 ≤ concFun R p.2}

/-- The source's `nrest_rel_def`. -/
@[simp] theorem mem_nrestRel_iff [CompleteLattice γ] {R : Set (β × α)} {c : NRest β γ}
    {a : NRest α γ} : (c, a) ∈ nrestRel R ↔ c ≤ concFun R a := Iff.rfl

/-- The source's `nrest_relD`. -/
theorem nrestRel_le [CompleteLattice γ] {R : Set (β × α)} {c : NRest β γ} {a : NRest α γ}
    (h : (c, a) ∈ nrestRel R) : c ≤ concFun R a := h

/-- The source's `nrest_relI`. -/
theorem nrestRel_of_le [CompleteLattice γ] {R : Set (β × α)} {c : NRest β γ} {a : NRest α γ}
    (h : c ≤ concFun R a) : (c, a) ∈ nrestRel R := h

/-- The source's `nrest_rel_comp`. -/
theorem nrestRel_comp [CompleteLattice γ] (A : Set (β × δ)) (B : Set (δ × α)) :
    relComp (nrestRel A : Set (NRest β γ × NRest δ γ)) (nrestRel B) = nrestRel (relComp A B) := by
  ext p
  constructor
  · rintro ⟨b, hb, hb'⟩
    exact (concFun_trans hb hb').trans_eq (concFun_chain A B p.2)
  · intro h
    exact ⟨concFun B p.2, nrestRel_of_le (h.trans_eq (concFun_chain A B p.2).symm),
      nrestRel_of_le le_rfl⟩

/-- The source's `param_RETURNT`. -/
theorem param_returnT [CompleteLattice γ] [Zero γ] {R : Set (β × α)} {x : β} {x' : α}
    (h : (x, x') ∈ R) : ((returnT x : NRest β γ), (returnT x' : NRest α γ)) ∈ nrestRel R :=
  nrestRel_of_le (returnT_refine h)

end NRest

/-! ### The executable gate (design record ledger D4)

`concFun` is a supremum over a relation, and at the sanity carrier of
`Sanity.lean` — three results, costs in `ℕ∞` — that supremum is a join
of three `WithBot ℕ∞`s, so it has an executable twin with a proved
agreement theorem. Everything checked below is therefore checked about
`concFun` itself. -/

namespace Sanity

open NRest

/-- The join of `WithBot ℕ∞`, decided by the (computable) order; the
executable form of `⊔`. -/
def supE (u v : WithBot ℕ∞) : WithBot ℕ∞ := if u ≤ v then v else u

/-- The executable join agrees with `⊔`. -/
theorem supE_eq (u v : WithBot ℕ∞) : supE u v = u ⊔ v := by
  rw [supE]
  split
  · exact (sup_eq_right.mpr ‹_›).symm
  · exact (sup_eq_left.mpr (le_of_not_ge ‹_›)).symm

/-- A relation on the sanity carrier, as a decidable table. -/
abbrev SRel := Fin 3 → Fin 3 → Bool

/-- The set of pairs a table describes. -/
def ofRel (R : SRel) : Set (Fin 3 × Fin 3) := {p | R p.1 p.2 = true}

@[simp] theorem mem_ofRel {R : SRel} {c a : Fin 3} : (c, a) ∈ ofRel R ↔ R c a = true := Iff.rfl

/-- Executable `concFun`. -/
def concFunE (R : SRel) (m : SRest) : SRest :=
  match m with
  | .fail => .fail
  | .rest X =>
    .rest (fun c => supE (supE (if R c 0 then X 0 else ⊥) (if R c 1 then X 1 else ⊥))
      (if R c 2 then X 2 else ⊥))

@[simp] theorem concFunE_fail (R : SRel) : concFunE R .fail = .fail := rfl

@[simp] theorem concFunE_rest (R : SRel) (X : Fin 3 → WithBot ℕ∞) :
    concFunE R (.rest X) =
      .rest (fun c => supE (supE (if R c 0 then X 0 else ⊥) (if R c 1 then X 1 else ⊥))
        (if R c 2 then X 2 else ⊥)) := rfl

/-- **The bridge.** Everything checked below is checked about
`concFun`. -/
theorem concFunE_eq (R : SRel) (m : SRest) : concFunE R m = concFun (ofRel R) m := by
  cases m with
  | fail => rfl
  | rest X =>
    rw [concFunE_rest, concFun_rest_eq, NRest.rest_inj_iff]
    funext c
    have key : ∀ a : Fin 3,
        (⨆ _ : (c, a) ∈ ofRel R, X a) = (if R c a then X a else (⊥ : WithBot ℕ∞)) := by
      intro a
      by_cases h : R c a = true
      · simp [ofRel, h]
      · simp [ofRel, h]
    rw [concMap_apply, iSup_fin3 (fun a => ⨆ _ : (c, a) ∈ ofRel R, X a), key 0, key 1, key 2,
      supE_eq, supE_eq]

/-- Executable relation composition, matching `relComp`. -/
def relCompE (R S : SRel) : SRel := fun c a => (R c 0 && S 0 a) || (R c 1 && S 1 a) ||
  (R c 2 && S 2 a)

/-- The executable composition agrees with `relComp`. -/
theorem relCompE_eq (R S : SRel) : ofRel (relCompE R S) = relComp (ofRel R) (ofRel S) := by
  ext p
  obtain ⟨c, a⟩ := p
  show (relCompE R S c a = true) ↔ _
  rw [mem_relComp]
  simp only [relCompE, Bool.or_eq_true, Bool.and_eq_true, mem_ofRel]
  constructor
  · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    exacts [⟨0, h1, h2⟩, ⟨1, h1, h2⟩, ⟨2, h1, h2⟩]
  · rintro ⟨b, hb, hb'⟩
    fin_cases b
    · exact Or.inl (Or.inl ⟨hb, hb'⟩)
    · exact Or.inl (Or.inr ⟨hb, hb'⟩)
    · exact Or.inr ⟨hb, hb'⟩

/-- The identity table. -/
def idE : SRel := fun c a => c == a

/-- The identity table is `Id`. -/
theorem idE_eq : ofRel idE = Set.diagonal (Fin 3) := by
  ext p
  obtain ⟨c, a⟩ := p
  show (idE c a = true) ↔ _
  rw [show ((c, a) ∈ Set.diagonal (Fin 3)) = (c = a) from rfl]
  simp only [idE, beq_iff_eq]

/-- A decidable "`R` is contained in `S`" for tables. -/
def subrelE (R S : SRel) : Bool := decide (∀ c a : Fin 3, R c a = true → S c a = true)

/-- The executable containment agrees with `⊆`. -/
theorem subrelE_eq (R S : SRel) : subrelE R S = true ↔ ofRel R ⊆ ofRel S := by
  simp only [subrelE, decide_eq_true_eq]
  constructor
  · rintro h ⟨c, a⟩ hp; exact h c a hp
  · intro h c a hca; exact h (show (c, a) ∈ ofRel R from hca)

/-! #### Spot checks -/

-- `⇓Id = id`, on samples.
#guard concFunE idE (.rest sampleX) = (.rest sampleX : SRest)
#guard concFunE idE (NRest.fail : SRest) = (NRest.fail : SRest)

-- the empty relation concretises everything to "no results at all"
#guard concFunE (fun _ _ => false) (.rest sampleX) = (.rest (fun _ => ⊥) : SRest)

-- a relation that merges results `0` and `2` into the concrete result
-- `0`: the concrete cost is the *best* (largest) of the two, since the
-- source's `Sup` is the join of the offers.
#guard concFunE (fun c a => c == 0 && (a == 0 || a == 2)) (.rest sampleX)
  = (.rest ![((5 : ℕ∞) : WithBot ℕ∞), ⊥, ⊥] : SRest)

-- chaining, on samples
#guard concFunE (fun c a => c == 0 && a == 1) (concFunE (fun c a => c == 1 && a == 2)
    (.rest sampleX))
  = concFunE (relCompE (fun c a => c == 0 && a == 1) (fun c a => c == 1 && a == 2))
      (.rest sampleX)

-- `⇓R` never turns a `rest` into a failure
#guard concFunE (fun _ _ => true) (.rest sampleX) ≠ (NRest.fail : SRest)
#guard concFunE (fun _ _ => true) (NRest.fail : SRest) = (NRest.fail : SRest)

/-! #### Property checks -/

open Plausible

/-- Sampling proxy for relation tables. -/
instance instSampleableExtSRel : SampleableExt SRel where
  proxy := List (ℕ × ℕ)
  sample := inferInstance
  interp := fun l c a => l.any (fun p => mk3 p.1 == c && mk3 p.2 == a)

-- `conc_fun_complete_lattice_chain`: `⇓R (⇓S M) = ⇓(R O S) M`.
#test ∀ (R S : SRel) (M : SRest), concFunE R (concFunE S M) = concFunE (relCompE R S) M

-- `conc_Id`: `⇓Id = id`.
#test ∀ M : SRest, concFunE idE M = M

-- `nrest_Rel_mono`: `⇓R` is monotone in the program.
#test ∀ (R : SRel) (M M' : SRest), M ≤ M' → concFunE R M ≤ concFunE R M'

-- `conc_fun_R_mono`: `⇓R` is monotone in the relation.
#test ∀ (R S : SRel) (M : SRest), subrelE R S = true → concFunE R M ≤ concFunE S M

-- `pw_conc_nofail` / `conc_fun_fail_iff`.
#test ∀ (R : SRel) (M : SRest), (concFunE R M = NRest.fail) = (M = NRest.fail)

-- `RETURNT_refine`: `(x,x') ∈ R → RETURNT x ≤ ⇓R (RETURNT x')`.
#test ∀ (R : SRel) (m n : ℕ), R (mk3 m) (mk3 n) = true →
  returnE (mk3 m) ≤ concFunE R (returnE (mk3 n))

-- `conc_fun_consume`: `⇓R (consume M t) = consume (⇓R M) t`.
#test ∀ (R : SRel) (M : SRest) (t : ℕ),
  concFunE R (NRest.consume M (t : ℕ∞)) = NRest.consume (concFunE R M) (t : ℕ∞)

-- `bindT_refine`, in the form whose premises are always satisfiable:
-- refine along the identity and the rule is `bindT_mono`.
#test ∀ (M f₀ f₁ f₂ : SRest),
  bindE M ![f₀, f₁, f₂] ≤ concFunE idE (bindE M ![f₀, f₁, f₂])

end Sanity

end Lax13Proofs.Refine
