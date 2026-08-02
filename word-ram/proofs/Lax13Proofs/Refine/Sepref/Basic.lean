import Lax13Proofs.Refine.Ir.Triples
import Lax13Proofs.Refine.NREST.Pw
import Lax13Proofs.Refine.Autoref.Relators

/-!
The Sepref refinement judgment `hnRefine` on the word-RAM IR: the port of
`thys/sepref/Sepref_Basic.thy` at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 (`isabelle_llvm_time`
@ `42dd7f5`, full SHA `42dd7f59998d76047bb4b6bce76d8f67b53a08b6`).

Extracts: `plans/word-ram/refinement-tower/source-extracts.md` §4 (the
`hn_refine` definition), `p4-sepref-extracts.md` §1, and above all
`p4-sepref-deep-extracts.md` §§1–3, which is this file's specification.
Where an extract was ambiguous the fetched `Sepref_Basic.thy` was the
authority (in particular for `hnr_bind`'s cost threading, source
~l. 629–735, and for `hn_refine_cons_complete`, ~l. 380).

## Supervisor decisions (P4/D-a … P4/D-g, owner-fixed, quoted)

**P4/D-a — concrete values are destination descriptors; the judgment is
generic in them.** The source's `hn_refine Γ c Γ' R m` has
`R : 'a ⇒ 'c ⇒ assn` with `'c` the concrete result type. Our IR is a
statement language: results are read from named cells, and the
destination is statically known (three-address code). So the port keeps
the source's `'c` as a type parameter `κ` and passes the statically-known
destination `d : κ` explicitly. `design.md` §5's `∃ᵃ r, x ↦ᵥ r ∗ R ra r`
draft is superseded: that shape is the scalar instance, recovered by
P4/D-b. Base instances defined here: `natAssn`, `arrayAssn`.

**P4/D-b — `pure`, `is_pure`, `the_pure` are ported verbatim and
generically** (`pureAssn (R : Set (κ × α)) : α → κ → Assn := fun a c =>
⌜(c, a) ∈ R⌝` — named `pureAssn` because `pure` collides with core Lean;
name-only deviation). At `κ := Ir.Val` this is the source's `pure`
exactly; whether translate consumes it for literals is wave C's affair.
`hnVal R := hnCtxt (pureAssn R)`.

**P4/D-c — `invalid_assn` splits in two.** The source's
`invalid_assn R x y ≡ ↑(pure_part (R x y))` is an ownership-free marker;
the heap substrate separately FREES the memory via `MK_FREE` programs.
Our substrate has no dealloc: a cell owned at the start of a run is owned
at its end (assertions describe the state exactly; `GC` absorbs credits
only, never cells). So:
* `invalidAssn R a c := ⌜purePart (R a c)⌝` — verbatim port, the pure
  bookkeeping marker; used where the source uses it for *structure
  alignment* (pass rule, merge bookkeeping of pure values).
* `deadAssn R a c := ∃ᵃ a', R a' c` — ours (flagged): junk-of-the-same-shape,
  the ownership sink for dead temporaries. `R a c ⊢ deadAssn R a c`
  (`entails_dead`, the invalidation weakening). `invalidate_clone` (the
  source's ownership-duplication trick) is FALSE for ownership-carrying
  `R` here and is NOT ported; proved instead:
  `hnCtxt R a c ⊢ hnCtxt (deadAssn R) a c`.

**P4/D-d — `MK_FREE` degenerates to entailment; the bind rule is the
manual-free shape.** Free programs would execute IR ops and cost
currencies the abstract side never paid. The port of `hnr_bind` is the
source's own `hnr_bind_manual_free`, with `doM`-sequencing replaced by
`Com.seq` (`hnr_seq` below). Its proof threads the two cost payments
through `wp_seq` exactly as the source's `hnr_bind` proof threads
`minus_ecost_cost`. D2's guard is kept in the source's form
`NRest.returnT a ≤ m`; `returnT_le_rest_iff` below records that at
`m = rest M` this is exactly `M a ≠ ⊥`, i.e. `∃ t, M a = some t`, so no
vocabulary delta was needed.

**P4/D-e — the MERGE calculus is entailment-form.** `MERGE`/`MERGE1`/
`MERGE_STAR`/`MERGE_triv`/`MERGE_END`/`MERGE1_eq`/`MERGE1_invalids`
(deep-extracts §3) with the free-program arguments dropped:
`MERGE Γ₁ Γ₂ Γ' := (Γ₁ ⊢ Γ') ∧ (Γ₂ ⊢ Γ')`,
`MERGE1 R1 R2 R' := ∀ a c, MERGE (R1 a c) (R2 a c) (R' a c)`,
`MERGE_STAR` congruence over `hnCtxt`-tagged conjuncts,
`MERGE1_invalids` stated with `deadAssn` (both directions). Source names
kept, camelCased where needed. These are wave C's merge-tactic rule base;
no tactic consumes them yet.

**P4/D-f — the pass rule pays for `skip`.** The source's
`hnr_RETURN_pass` uses the zero-cost monad `return`; our only do-nothing
program is `Com.skip`, which charges `¤¤Currency.skip 1` (P3 ledger D-c).
Ported as `hnr_return_pass`, plus the pure-return analogue `hnr_const`
and `hnr_assert` per the source's `hnr_ASSERT`.

**P4/D-g — GC stays P3's credits-only GC.** Dead cells are handled by
`deadAssn` conjuncts (P4/D-c), never by GC.

## This file's own judgment calls

**P4/D-h — assertion disjunction is new here, and is called `sepOr`.**
`Assn.lean` has `sepTrue`/`sepFalse` but no disjunction, so the source's
`Γ' or Γ''` (used only by `hn_refine_split_post`/`hn_refine_post_other`)
is defined here as `sepOr P Q := fun h => P h ∨ Q h`, notation `∨ᵃ`.
*Not* named `sepDisj`: that name is taken by `Ir`'s separation-disjointness
class `SepDisj`, and the two would read as variants of one another.
Rationale: a three-line definition local to its two consumers beats
touching the frozen `Assn.lean`. Fallback if wave C wants it in the
substrate: move the definition down and delete it here; nothing else
depends on its location.

**P4/D-i — `the_pure` is ported as `purePart`-collection, not as HOL's
`THE`.** The source's `the_pure P ≡ THE P'. ∀x x'. P x x' = ↑((x',x)∈P')`
is a definite description; a Lean port would need `Classical.choose` plus
an injectivity lemma to say anything at all. Instead
`thePure P := {p | purePart (P p.2 p.1)}` — total, choice-free, and
*equal* to the source's value wherever the source's is defined:
`thePure_pureAssn : thePure (pureAssn R) = R` and
`pureAssn_thePure : isPure R → pureAssn (thePure R) = R` are both proved
below, which is the entire contract the source's `the_pure` lemmas state
(`the_pure_pure`, `pure_the_pure`). Fallback: none needed — the two
lemmas pin the value on the whole `isPure` domain, and off that domain
the source's `THE` is junk too.

**P4/D-j — `hnRefineI_spect` is stated at `(returnT x).consume t`.** P1's
`NRest` has no `SPECT [x ↦ t]` singleton constructor; the source's
`SPECT [x↦t]` is `consume (RETURNT x) t` (its own `consume_RETURNT`), so
that is the shape used. Vocabulary delta only.

**P4/D-k — `hnRefine_augment_res` takes the unfolded premise.** The
source's `g ≤ₙ SPEC Φ t` needs the `le_or_fail` order, which P1 did not
port (and porting a `leof` theory for one lemma is not worth it). The
premise is stated as its unfolded content:
`∀ M, g = .rest M → ∀ a t, M a = (t : WithBot ECost) → Φ a`. Fallback: if
P5 ports `≤ₙ`, restate and derive this form.

**P4/D-l — `rdomp` quantifies over `AState`, not over "heaps".** The
source's `rdomp R a ≡ ∃h c. R a c h` reads `h` in the LLVM assertion
carrier; ours is `AState` (`Assn = AState → Prop`), i.e. `purePart` of
`∃ᵃ c, R a c`. Recorded as `rdomp_iff_purePart`.

## Deliberate absences

* `hnr_RECT` — ledger D6, out of translate scope. Not ported.
* `ht_from_hnr` — P5's cashing seam. Deferred, quoted in the extract.
* `imp_correctI` — `oops`'d in the source; nothing to port.
* `invalidate_clone` / `invalidate_clone'` — FALSE here (P4/D-c).
* `MK_FREE` and its four `mk_free_*` lemmas — degenerate to entailments
  under P4/D-d; the merge calculus of §5 is what survives of them.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. Tags and the assertion zoo (deep-extracts §1) -/

/-- The source's `hn_ctxt`: a tag marking a refinement assertion for the
frame inferencer. Definitionally transparent, as there. -/
def hnCtxt {α κ : Type} (P : α → κ → Assn) (a : α) (c : κ) : Assn := P a c

@[simp] theorem hnCtxt_def {α κ : Type} (P : α → κ → Assn) (a : α) (c : κ) :
    hnCtxt P a c = P a c := rfl

/-- The source's `pure R ≡ (λa c. ↑((c,a)∈R))` (P4/D-b; renamed to avoid
the collision with core Lean's `pure`). -/
def pureAssn {α κ : Type} (R : Set (κ × α)) : α → κ → Assn :=
  fun a c => ⌜(c, a) ∈ R⌝

@[simp] theorem pureAssn_def {α κ : Type} (R : Set (κ × α)) (a : α) (c : κ) :
    pureAssn R a c = ⌜(c, a) ∈ R⌝ := rfl

/-- The source's `is_pure P ≡ ∃P'. ∀x x'. P x x' = ↑(P' x x')`. -/
def isPure {α κ : Type} (P : α → κ → Assn) : Prop :=
  ∃ P' : α → κ → Prop, ∀ a c, P a c = ⌜P' a c⌝

/-- The source's `the_pure`, as a `purePart`-collection (P4/D-i). -/
def thePure {α κ : Type} (P : α → κ → Assn) : Set (κ × α) :=
  {p | purePart (P p.2 p.1)}

/-- The source's `hn_val R ≡ hn_ctxt (pure R)`. -/
abbrev hnVal {α κ : Type} (R : Set (κ × α)) : α → κ → Assn := hnCtxt (pureAssn R)

/-- The source's `invalid_assn R x y ≡ ↑(pure_part (R x y))` (P4/D-c,
first half: the pure bookkeeping marker). -/
def invalidAssn {α κ : Type} (R : α → κ → Assn) : α → κ → Assn :=
  fun a c => ⌜purePart (R a c)⌝

/-- The source's `hn_invalid R ≡ hn_ctxt (invalid_assn R)`. -/
abbrev hnInvalid {α κ : Type} (R : α → κ → Assn) : α → κ → Assn := hnCtxt (invalidAssn R)

/-- Ours (P4/D-c, second half): junk of the same shape — the ownership
sink for a dead temporary under named-cell ownership with no dealloc. -/
def deadAssn {α κ : Type} (R : α → κ → Assn) : α → κ → Assn :=
  fun _ c => ∃ᵃ a', R a' c

/-- The scalar special case of `deadAssn` that does not need an abstract
witness: the cell `x` exists and holds *something* (P4/D-f's junk cell). -/
def junkCell (x : String) : Assn := ∃ᵃ v, x ↦ᵥ v

/-- The source's `rdomp R a ≡ ∃h c. R a c h` (P4/D-l). -/
def rdomp {α κ : Type} (R : α → κ → Assn) (a : α) : Prop := ∃ (h : AState) (c : κ), R a c h

/-- The source's `prod_assn`, `A ×ₐ B`. -/
def prodAssn {α₁ α₂ κ₁ κ₂ : Type} (P₁ : α₁ → κ₁ → Assn) (P₂ : α₂ → κ₂ → Assn) :
    α₁ × α₂ → κ₁ × κ₂ → Assn :=
  fun a c => P₁ a.1 c.1 ∗ P₂ a.2 c.2

@[inherit_doc] infixr:70 " ×ₐ " => prodAssn

/-- Base instance of P4/D-a: a natural number lives in a named scalar cell. -/
def natAssn : ℕ → String → Assn := fun a c => c ↦ᵥ a

/-- Base instance of P4/D-a: a list of naturals lives in a named array. -/
def arrayAssn : List ℕ → String → Assn := fun xs a => a ↦ₐ xs

/-- Assertion disjunction, the source's `Γ' or Γ''` (P4/D-h). -/
def sepOr (P Q : Assn) : Assn := fun h => P h ∨ Q h

@[inherit_doc] infixr:65 " ∨ᵃ " => sepOr

/-! ### The zoo's lemmas -/

@[simp] theorem invalidAssn_def {α κ : Type} (R : α → κ → Assn) (a : α) (c : κ) :
    invalidAssn R a c = ⌜purePart (R a c)⌝ := rfl

@[simp] theorem deadAssn_def {α κ : Type} (R : α → κ → Assn) (a : α) (c : κ) :
    deadAssn R a c = ∃ᵃ a', R a' c := rfl

@[simp] theorem junkCell_def (x : String) : junkCell x = ∃ᵃ v, x ↦ᵥ v := rfl

@[simp] theorem natAssn_def (a : ℕ) (c : String) : natAssn a c = c ↦ᵥ a := rfl

@[simp] theorem arrayAssn_def (xs : List ℕ) (a : String) : arrayAssn xs a = a ↦ₐ xs := rfl

@[simp] theorem sepOr_apply (P Q : Assn) (h : AState) : (P ∨ᵃ Q) h = (P h ∨ Q h) := rfl

/-- `⌜·⌝` is injective — the fact HOL gets for free from `pred_lift`'s
extraction simps, and the engine of every `is_pure`/`the_pure` lemma. -/
theorem predLift_inj {Φ Ψ : Prop} (h : (⌜Φ⌝ : Assn) = ⌜Ψ⌝) : Φ ↔ Ψ := by
  constructor
  · intro hΦ
    have : (⌜Ψ⌝ : Assn) 0 := by rw [← h]; exact ⟨hΦ, rfl⟩
    exact this.1
  · intro hΨ
    have : (⌜Φ⌝ : Assn) 0 := by rw [h]; exact ⟨hΨ, rfl⟩
    exact this.1

@[simp] theorem purePart_predLift {Φ : Prop} : purePart (⌜Φ⌝ : Assn) ↔ Φ := by
  constructor
  · rintro ⟨h, hΦ, -⟩; exact hΦ
  · intro hΦ; exact ⟨0, hΦ, rfl⟩

/-- The source's `hn_val_unfold`. -/
@[simp] theorem hn_val_unfold {α κ : Type} (R : Set (κ × α)) (a : α) (c : κ) :
    hnVal R a c = ⌜(c, a) ∈ R⌝ := rfl

/-- The source's `pure_pure`: `pure R` is pure. -/
@[simp] theorem pure_pure {α κ : Type} (R : Set (κ × α)) : isPure (pureAssn R) :=
  ⟨fun a c => (c, a) ∈ R, fun _ _ => rfl⟩

/-- The source's `pure_hn_ctxt`. -/
theorem pure_hn_ctxt {α κ : Type} {P : α → κ → Assn} (h : isPure P) : isPure (hnCtxt P) := h

/-- The source's `the_pure_pure`. -/
@[simp] theorem thePure_pureAssn {α κ : Type} (R : Set (κ × α)) : thePure (pureAssn R) = R := by
  ext p
  simp [thePure]

/-- The source's `pure_the_pure`. -/
theorem pureAssn_thePure {α κ : Type} {R : α → κ → Assn} (h : isPure R) :
    pureAssn (thePure R) = R := by
  obtain ⟨P', hP⟩ := h
  funext a c
  rw [pureAssn_def]
  have : ((c, a) ∈ thePure R) = P' a c := by
    simp only [thePure, Set.mem_setOf_eq, hP a c]
    exact propext purePart_predLift
  rw [this, hP a c]

/-- The source's `is_pure_conv`. -/
theorem isPure_conv {α κ : Type} {R : α → κ → Assn} :
    isPure R ↔ ∃ R' : Set (κ × α), R = pureAssn R' := by
  constructor
  · intro h; exact ⟨thePure R, (pureAssn_thePure h).symm⟩
  · rintro ⟨R', rfl⟩; exact pure_pure R'

/-- The source's `invalid_pure_recover`. -/
@[simp] theorem invalid_pure_recover {α κ : Type} (R : Set (κ × α)) (a : α) (c : κ) :
    invalidAssn (pureAssn R) a c = pureAssn R a c := by
  simp [invalidAssn]

/-- The source's `hn_invalidI`: once the real assertion has a model, its
invalid marker is `□`. -/
theorem hn_invalidI {α κ : Type} {P : α → κ → Assn} {a : α} {c : κ} {h : AState}
    (hp : hnCtxt P a c h) : hnInvalid P a c = (□ : Assn) := by
  have : purePart (P a c) := ⟨h, hp⟩
  simp [invalidAssn, this]

/-- P4/D-c's invalidation weakening: ownership is not dropped, it is
downgraded to junk of the same shape. -/
theorem entails_dead {α κ : Type} (R : α → κ → Assn) (a : α) (c : κ) :
    R a c ⊢ deadAssn R a c :=
  fun _ h => ⟨a, h⟩

/-- P4/D-c's replacement for the source's `invalidate_clone'`. -/
theorem hnCtxt_entails_dead {α κ : Type} (R : α → κ → Assn) (a : α) (c : κ) :
    hnCtxt R a c ⊢ hnCtxt (deadAssn R) a c :=
  entails_dead R a c

/-- The junk-cell instance of `entails_dead` at `natAssn`. -/
theorem natAssn_entails_junkCell (a : ℕ) (x : String) : natAssn a x ⊢ junkCell x :=
  fun _ h => ⟨a, h⟩

theorem deadAssn_natAssn_eq_junkCell (a : ℕ) (x : String) : deadAssn natAssn a x = junkCell x :=
  rfl

/-- P4/D-l: `rdomp` is `purePart` of an existential. -/
theorem rdomp_iff_purePart {α κ : Type} (R : α → κ → Assn) (a : α) :
    rdomp R a ↔ purePart (∃ᵃ c, R a c) := by
  constructor
  · rintro ⟨h, c, hc⟩; exact ⟨h, c, hc⟩
  · rintro ⟨h, c, hc⟩; exact ⟨h, c, hc⟩

/-- The source's `rdomp_ctxt`. -/
@[simp] theorem rdomp_ctxt {α κ : Type} (R : α → κ → Assn) : rdomp (hnCtxt R) = rdomp R := rfl

/-- The source's `rdomp_pure`: `a ∈ Range R`. -/
@[simp] theorem rdomp_pure {α κ : Type} (R : Set (κ × α)) (a : α) :
    rdomp (pureAssn R) a ↔ ∃ c, (c, a) ∈ R := by
  constructor
  · rintro ⟨h, c, hc, -⟩; exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩; exact ⟨0, c, hc, rfl⟩

/-- The source's `rdomp_invalid_simp`. -/
@[simp] theorem rdomp_invalid_simp {α κ : Type} (P : α → κ → Assn) (a : α) :
    rdomp (invalidAssn P) a ↔ rdomp P a := by
  constructor
  · rintro ⟨h, c, hc, -⟩
    obtain ⟨h', hh'⟩ := hc
    exact ⟨h', c, hh'⟩
  · rintro ⟨h, c, hc⟩
    exact ⟨0, c, ⟨h, hc⟩, rfl⟩

/-- The source's `prod_assn_pair_conv`. -/
@[simp] theorem prod_assn_pair_conv {α₁ α₂ κ₁ κ₂ : Type} (A : α₁ → κ₁ → Assn)
    (B : α₂ → κ₂ → Assn) (a₁ : α₁) (b₁ : α₂) (a₂ : κ₁) (b₂ : κ₂) :
    (A ×ₐ B) (a₁, b₁) (a₂, b₂) = (A a₁ a₂ ∗ B b₁ b₂) := rfl

/-- The source's `prod_assn_pure_conv`. -/
@[simp] theorem prod_assn_pure_conv {α₁ α₂ κ₁ κ₂ : Type} (R₁ : Set (κ₁ × α₁))
    (R₂ : Set (κ₂ × α₂)) :
    (pureAssn R₁ ×ₐ pureAssn R₂) = pureAssn (R₁ ×ᵣ R₂) := by
  funext a c
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨c₁, c₂⟩ := c
  rw [prod_assn_pair_conv, pureAssn_def, pureAssn_def, pureAssn_def]
  funext h
  refine propext ?_
  simp only [predLift_sepConj_iff, predLift]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, h₂⟩, h₃⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, h₂, h₃⟩

/-- The source's `prod_assn_true`. -/
@[simp] theorem prod_assn_true {α₁ α₂ κ₁ κ₂ : Type} :
    ((fun (_ : α₁) (_ : κ₁) => (sepTrue : Assn)) ×ₐ
      (fun (_ : α₂) (_ : κ₂) => (sepTrue : Assn))) = fun _ _ => (sepTrue : Assn) := by
  funext a c h
  refine propext ⟨fun _ => trivial, fun _ => ?_⟩
  exact ⟨0, h, sep_zero_disj h, (sep_zero_add h).symm, trivial, trivial⟩

/-! ## 2. Two cost facts and two assertion facts

Everything below is stated so that these four are the only "arithmetic"
it uses. The two cost facts are the source's `cost_ecost_add_increasing2`
and `cost_ecost_minus_add_assoc2` — the pair that `hnr_bind`'s `**` step
is made of (source ~l. 623 and ~l. 719). -/

/-- ℕ∞ with a finite subtrahend: adding to an affordable balance keeps
the deduction and the addition commuting. -/
theorem enat_resSub_add {n : ℕ} {x b : ℕ∞} (h : (n : ℕ∞) ≤ x) :
    (x -ᵣ (n : ℕ∞)) + b = (x + b) -ᵣ (n : ℕ∞) := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  rcases eq_or_ne b ⊤ with rfl | hb
  · rw [enat_resSub_coe]
    simp
  lift x to ℕ using hx
  lift b to ℕ using hb
  rw [Nat.cast_le] at h
  rw [enat_resSub_coe, enat_resSub_coe, ← Nat.cast_add, ← ENat.coe_sub, ← ENat.coe_sub,
    ← Nat.cast_add, Nat.cast_inj]
  omega

/-- The source's `cost_ecost_add_increasing2`: an affordable cost stays
affordable when the balance grows. -/
theorem leCostECost_add_right {κ : Cost} {c : ECost} (h : leCostECost κ c) (d : ECost) :
    leCostECost κ (c + d) := fun x => le_trans (h x) (by simp)

/-- The source's `cost_ecost_minus_add_assoc2`, the `**` step of
`hnr_bind`: credits handed over *after* a payment can equivalently be
handed over before it. -/
theorem minusECost_add_of_le {κ : Cost} {c : ECost} (h : leCostECost κ c) (d : ECost) :
    minusECost c κ + d = minusECost (c + d) κ := by
  ext k
  rw [ACost.toFun_add, toFun_minusECost, toFun_minusECost, ACost.toFun_add]
  exact enat_resSub_add (h k)

/-- Adding a `GC` conjunct on the right is always allowed (`□ ⊢ GC`). -/
theorem entails_gc_right (P : Assn) : P ⊢ P ∗ GC := by
  intro h hh
  have hh' : (P ∗ □) h := by rwa [sepConj_emp]
  exact conj_entails_mono (entails_refl P) empty_ent_GC h hh'

/-- `predLift_sepConj_iff` with the pure conjunct on the right — the shape
`hrComp` (and the source's `hr_comp`) puts it in. -/
theorem sepConj_predLift_iff {P : Assn} {Φ : Prop} {h : AState} :
    (P ∗ ⌜Φ⌝) h ↔ Φ ∧ P h := by
  rw [sepConj_comm]
  exact predLift_sepConj_iff

/-- A satisfied pure conjunct is `□`, hence absorbable. -/
theorem predLift_of_true {Φ : Prop} (h : Φ) : (⌜Φ⌝ : Assn) = □ := by
  rw [eq_true h, predLift_true]

/-! ## 3. The judgment (source-extracts.md §4, P4/D-a) -/

/-- Port of `hn_refine` (source-extracts.md §4), clause for clause; `d : κ`
is the statically-known concrete result (a cell name, a pair of cell
names, …) that the shallow source returns from `c` dynamically. -/
def hnRefine {α κ : Type} (Γ : Assn) (c : Com) (Γ' : Assn) (d : κ)
    (R : α → κ → Assn) (m : NRest α ECost) : Prop :=
  m.nofailT →
    ∀ (M : α → WithBot ECost) (F : Assn) (s : State) (cr : ECost),
      m = .rest M →
      irSTATE (Γ ∗ F) (s, cr) →
      ∃ (ra : α) (Ca : ECost), (Ca : WithBot ECost) ≤ M ra ∧
        wp c (fun _ => irSTATE (Γ' ∗ R ra d ∗ F ∗ GC)) (s, cr + Ca)

section Suite

variable {α β κ κ' : Type}

/-! ### Intro / elim -/

/-- The source's `hn_refineI`. -/
theorem hnRefineI {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn} {m : NRest α ECost}
    (h : ∀ (M : α → WithBot ECost) (F : Assn) (s : State) (cr : ECost), m = .rest M →
      irSTATE (Γ ∗ F) (s, cr) →
      ∃ (ra : α) (Ca : ECost), (Ca : WithBot ECost) ≤ M ra ∧
        wp c (fun _ => irSTATE (Γ' ∗ R ra d ∗ F ∗ GC)) (s, cr + Ca)) :
    hnRefine Γ c Γ' d R m := fun _ => h

/-- The source's `hn_refineD`. -/
theorem hnRefineD {Γ Γ' F : Assn} {c : Com} {d : κ} {R : α → κ → Assn} {m : NRest α ECost}
    {M : α → WithBot ECost} {s : State} {cr : ECost}
    (h : hnRefine Γ c Γ' d R m) (hm : m = .rest M) (hs : irSTATE (Γ ∗ F) (s, cr)) :
    ∃ (ra : α) (Ca : ECost), (Ca : WithBot ECost) ≤ M ra ∧
      wp c (fun _ => irSTATE (Γ' ∗ R ra d ∗ F ∗ GC)) (s, cr + Ca) :=
  h (hm ▸ NRest.nofailT_rest M) M F s cr hm hs

/-- The `∗`-permutation the `GC`-carrying postconditions are up to. -/
private theorem gc_perm (A B F : Assn) : ((A ∗ B) ∗ GC) ∗ F = A ∗ B ∗ F ∗ GC := by
  rw [sepConj_assoc, sepConj_assoc, sepConj_comm GC F]

/-- The source's `hn_refineI'`: an exact `irHtriple` with a known result
is a refinement of `returnT`. -/
theorem hnRefineI_htriple {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn} {x : α}
    (h : irHtriple Γ c (Γ' ∗ R x d)) : hnRefine Γ c Γ' d R (NRest.returnT x) := by
  refine hnRefineI fun M F s cr hm hs => ⟨x, 0, ?_, ?_⟩
  · rw [NRest.returnT, NRest.rest_inj_iff] at hm
    simp [← hm]
  · rw [add_zero]
    refine wp_mono_ir (fun _ p hp => ?_) (h F (s, cr) hs)
    show irSTATE (Γ' ∗ R x d ∗ F ∗ GC) p
    rw [← gc_perm]
    exact hp

/-- The source's `hn_refineI_SPECT`, at P4/D-j's shape for the
`SPECT [x ↦ t]` singleton. -/
theorem hnRefineI_spect {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn} {x : α} {t : ECost}
    (h : irHtriple (¤t ∗ Γ) c (Γ' ∗ R x d)) :
    hnRefine Γ c Γ' d R ((NRest.returnT x).consume t) := by
  refine hnRefineI fun M F s cr hm hs => ⟨x, t, ?_, ?_⟩
  · rw [NRest.consume_returnT, NRest.rest_inj_iff] at hm
    rw [← hm, NRest.single_self]
  · have hs' : irSTATE ((¤t ∗ Γ) ∗ F) (s, cr + t) := by
      rw [sepConj_assoc, add_comm cr t]
      exact credits_merge hs
    refine wp_mono_ir (fun _ p hp => ?_) (h F (s, cr + t) hs')
    show irSTATE (Γ' ∗ R x d ∗ F ∗ GC) p
    rw [← gc_perm]
    exact hp

/-- `returnT a ≤ rest M` is exactly "`M` has a result at `a`" — the fact
that makes P4/D-d's D2 guard need no vocabulary delta. -/
theorem returnT_le_rest_iff {M : α → WithBot ECost} {a : α} :
    (NRest.returnT a : NRest α ECost) ≤ NRest.rest M ↔ (0 : WithBot ECost) ≤ M a := by
  rw [NRest.returnT, NRest.rest_le_rest_iff, NRest.single_le_iff]

/-- Any paid-for result is a result. -/
theorem returnT_le_rest_of_coe_le {M : α → WithBot ECost} {a : α} {Ca : ECost}
    (h : (Ca : WithBot ECost) ≤ M a) : (NRest.returnT a : NRest α ECost) ≤ NRest.rest M := by
  refine returnT_le_rest_iff.2 (le_trans ?_ h)
  rw [← WithBot.coe_zero, WithBot.coe_le_coe]
  exact ACost.le_def.2 fun _ => by simp

/-- The source's `hn_refine_consume_return`: the alternative
characterization, with the cost bound stated as a program inequality. -/
theorem hn_refine_consume_return {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} :
    hnRefine Γ c Γ' d R m ↔
      (m.nofailT → ∀ (F : Assn) (s : State) (cr : ECost), irSTATE (Γ ∗ F) (s, cr) →
        ∃ (ra : α) (Ca : ECost), (NRest.returnT ra).consume Ca ≤ m ∧
          wp c (fun _ => irSTATE (Γ' ∗ R ra d ∗ F ∗ GC)) (s, cr + Ca)) := by
  constructor
  · intro h hnf F s cr hs
    cases hm : m with
    | fail => exact absurd hm hnf
    | rest M =>
      obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD h hm hs
      refine ⟨ra, Ca, ?_, w⟩
      rw [NRest.consume_returnT, NRest.rest_le_rest_iff, NRest.single_le_iff]
      exact hCa
  · intro h hnf M F s cr hm hs
    obtain ⟨ra, Ca, hle, w⟩ := h hnf F s cr hs
    refine ⟨ra, Ca, ?_, w⟩
    rw [hm, NRest.consume_returnT, NRest.rest_le_rest_iff, NRest.single_le_iff] at hle
    exact hle

/-! ### Structural rules -/

/-- The source's `hn_refine_preI`. -/
theorem hnRefine_preI {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn} {m : NRest α ECost}
    (h : ∀ hh : AState, Γ hh → hnRefine Γ c Γ' d R m) : hnRefine Γ c Γ' d R m := by
  intro hnf M F s cr hm hs
  obtain ⟨x, -, -, -, hx, -⟩ := id hs
  exact h x hx hnf M F s cr hm hs

/-- The source's `hn_refine_nofailI`. -/
theorem hnRefine_nofailI {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn} {m : NRest α ECost}
    (h : m.nofailT → hnRefine Γ c Γ' d R m) : hnRefine Γ c Γ' d R m := fun hnf => h hnf hnf

/-- The source's `hn_refine_false`. -/
@[simp] theorem hnRefine_false {Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} : hnRefine sepFalse c Γ' d R m := by
  intro _ _ _ _ _ _ hs
  rcases hs with ⟨x, y, h1, h2, hf, h4⟩
  exact False.elim hf

/-- The source's `hnr_FAIL`. -/
@[simp] theorem hnr_fail {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn} :
    hnRefine Γ c Γ' d R (failT : NRest α ECost) := fun hnf => absurd rfl hnf

/-- The source's `hn_refine_cons_complete`. -/
theorem hnRefine_cons_complete {P P' Q Q' : Assn} {c : Com} {d : κ} {R R' : α → κ → Assn}
    {m m' : NRest α ECost} (hR : hnRefine P' c Q d R m) (hI : P ⊢ P') (hI' : Q ⊢ Q')
    (hR' : ∀ (a : α) (e : κ), R a e ⊢ R' a e) (hLE : m ≤ m') :
    hnRefine P c Q' d R' m' := by
  intro _ M F s cr hm hs
  cases hmm : m with
  | fail =>
    exact absurd (hmm ▸ hm ▸ hLE) (NRest.not_fail_le_rest M)
  | rest Mm =>
    have hMle : Mm ≤ M := NRest.rest_le_rest_iff.1 (hmm ▸ hm ▸ hLE)
    have hs' : irSTATE (P' ∗ F) (s, cr) := start_entailsE hs (sepConj_mono_left hI)
    obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD hR hmm hs'
    refine ⟨ra, Ca, le_trans hCa (hMle ra), wp_mono_ir (fun _ p hp => ?_) w⟩
    exact start_entailsE hp
      (conj_entails_mono hI' (conj_entails_mono (hR' ra d) (entails_refl (F ∗ GC))))

/-- The source's `hn_refine_cons`. -/
theorem hnRefine_cons {P P' Q Q' : Assn} {c : Com} {d : κ} {R R' : α → κ → Assn}
    {m : NRest α ECost} (hR : hnRefine P' c Q d R m) (hI : P ⊢ P') (hI' : Q ⊢ Q')
    (hR' : ∀ (a : α) (e : κ), R a e ⊢ R' a e) : hnRefine P c Q' d R' m :=
  hnRefine_cons_complete hR hI hI' hR' le_rfl

/-- The source's `hn_refine_cons_pre`. -/
theorem hnRefine_cons_pre {P P' Q : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} (hR : hnRefine P' c Q d R m) (hI : P ⊢ P') : hnRefine P c Q d R m :=
  hnRefine_cons_complete hR hI (entails_refl Q) (fun a e => entails_refl (R a e)) le_rfl

/-- The source's `hn_refine_cons_post`. -/
theorem hnRefine_cons_post {P Q Q' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} (hR : hnRefine P c Q d R m) (hI' : Q ⊢ Q') : hnRefine P c Q' d R m :=
  hnRefine_cons_complete hR (entails_refl P) hI' (fun a e => entails_refl (R a e)) le_rfl

/-- The source's `hn_refine_cons_res`. -/
theorem hnRefine_cons_res {P Q : Assn} {c : Com} {d : κ} {R R' : α → κ → Assn}
    {m : NRest α ECost} (hR : hnRefine P c Q d R m)
    (hR' : ∀ (a : α) (e : κ), R a e ⊢ R' a e) : hnRefine P c Q d R' m :=
  hnRefine_cons_complete hR (entails_refl P) (entails_refl Q) hR' le_rfl

/-- The source's `hn_refine_ref`. -/
theorem hnRefine_ref {P Q : Assn} {c : Com} {d : κ} {R : α → κ → Assn} {m m' : NRest α ECost}
    (hR : hnRefine P c Q d R m) (hLE : m ≤ m') : hnRefine P c Q d R m' :=
  hnRefine_cons_complete hR (entails_refl P) (entails_refl Q)
    (fun a e => entails_refl (R a e)) hLE

/-- The source's `hn_refine_frame`. -/
theorem hnRefine_frame {P P' Q' F : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} (hnr : hnRefine P' c Q' d R m) (ent : P ⊢ P' ∗ F) :
    hnRefine P c (Q' ∗ F) d R m := by
  intro hnf M Fa s cr hm hs
  have hs' : irSTATE (P' ∗ F ∗ Fa) (s, cr) := by
    have := start_entailsE hs (sepConj_mono_left ent)
    rwa [sepConj_assoc] at this
  obtain ⟨ra, Ca, hCa, w⟩ := hnr hnf M (F ∗ Fa) s cr hm hs'
  refine ⟨ra, Ca, hCa, wp_mono_ir (fun _ p hp => ?_) w⟩
  show irSTATE ((Q' ∗ F) ∗ R ra d ∗ Fa ∗ GC) p
  have he : (Q' ∗ F) ∗ R ra d ∗ Fa ∗ GC = Q' ∗ R ra d ∗ (F ∗ Fa) ∗ GC := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_left_comm F (R ra d)]
  rw [he]
  exact hp

/-- The source's `hn_refine_frame'`. -/
theorem hnRefine_frame' {Γ Γ' F : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} (h : hnRefine Γ c Γ' d R m) : hnRefine (Γ ∗ F) c (Γ' ∗ F) d R m :=
  hnRefine_frame h (entails_refl (Γ ∗ F))

/-- The source's `hn_refine_frame''`. -/
theorem hnRefine_frame'' {Γ Γ' F : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} (h : hnRefine Γ c Γ' d R m) : hnRefine (F ∗ Γ) c (F ∗ Γ') d R m := by
  have h' := hnRefine_frame' (F := F) h
  rw [sepConj_comm Γ F, sepConj_comm Γ' F] at h'
  exact h'

/-- The source's `hnr_pre_ex_conv`. -/
theorem hnr_pre_ex_conv {Γ : β → Assn} {Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} :
    hnRefine (∃ᵃ y, Γ y) c Γ' d R m ↔ ∀ y, hnRefine (Γ y) c Γ' d R m := by
  constructor
  · intro h y hnf M F s cr hm hs
    exact h hnf M F s cr hm (start_entailsE hs (sepConj_mono_left (fun _ hh => ⟨y, hh⟩)))
  · intro h hnf M F s cr hm hs
    rw [sepEx_sepConj] at hs
    obtain ⟨y, hy⟩ := hs
    exact h y hnf M F s cr hm hy

/-- The source's `hnr_pre_pure_conv`. -/
theorem hnr_pre_pure_conv {Φ : Prop} {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} :
    hnRefine (⌜Φ⌝ ∗ Γ) c Γ' d R m ↔ (Φ → hnRefine Γ c Γ' d R m) := by
  constructor
  · intro h hΦ hnf M F s cr hm hs
    refine h hnf M F s cr hm ?_
    show ((⌜Φ⌝ ∗ Γ) ∗ F) (irα (s, cr))
    rw [sepConj_assoc]
    exact (predLift_sepConj_iff).2 ⟨hΦ, hs⟩
  · intro h hnf M F s cr hm hs
    have hs' : (⌜Φ⌝ ∗ (Γ ∗ F)) (irα (s, cr)) := by rwa [← sepConj_assoc]
    obtain ⟨hΦ, hs''⟩ := (predLift_sepConj_iff).1 hs'
    exact h hΦ hnf M F s cr hm hs''

/-- The source's `hn_refine_extract_pre_val`, at `hnVal`. -/
theorem hnRefine_extract_pre_val {S : Set (κ' × β)} {xa : β} {xc : κ'} {Γ Γ' : Assn} {c : Com}
    {d : κ} {R : α → κ → Assn} {m : NRest α ECost} :
    hnRefine (hnVal S xa xc ∗ Γ) c Γ' d R m ↔
      ((xc, xa) ∈ S → hnRefine Γ c Γ' d R m) :=
  hnr_pre_pure_conv

/-- The source's `hn_refine_split_post`. -/
theorem hnRefine_split_post {Γ Γ' Γ'' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} (h : hnRefine Γ c Γ' d R m) : hnRefine Γ c (Γ' ∨ᵃ Γ'') d R m :=
  hnRefine_cons_post h fun _ hh => Or.inl hh

/-- The source's `hn_refine_post_other`. -/
theorem hnRefine_post_other {Γ Γ' Γ'' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} (h : hnRefine Γ c Γ'' d R m) : hnRefine Γ c (Γ' ∨ᵃ Γ'') d R m :=
  hnRefine_cons_post h fun _ hh => Or.inr hh

/-- The source's `hn_refine_augment_res`, with P4/D-k's unfolded premise. -/
theorem hnRefine_augment_res {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {g : NRest α ECost} {Φ : α → Prop} (A : hnRefine Γ c Γ' d R g)
    (B : ∀ M, g = .rest M → ∀ (a : α) (t : ECost), M a = (t : WithBot ECost) → Φ a) :
    hnRefine Γ c Γ' d (fun a e => R a e ∗ ⌜Φ a⌝) g := by
  intro hnf M F s cr hm hs
  obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD A hm hs
  have hne : M ra ≠ ⊥ := by
    intro hbot
    rw [hbot, le_bot_iff] at hCa
    exact absurd hCa (WithBot.coe_ne_bot)
  obtain ⟨t, ht⟩ := WithBot.ne_bot_iff_exists.1 hne
  have hΦ : Φ ra := B M hm ra t ht.symm
  refine ⟨ra, Ca, hCa, wp_mono_ir (fun _ p hp => ?_) w⟩
  show irSTATE (Γ' ∗ (R ra d ∗ ⌜Φ ra⌝) ∗ F ∗ GC) p
  rw [predLift_of_true hΦ, sepConj_emp]
  exact hp

/-! ### The bind rule (P4/D-d)

The port of `hnr_bind_manual_free`. Its proof is the source's `hnr_bind`
proof (`Sepref_Basic.thy` ~l. 629) with the three `wp` unfoldings replaced
by one `wp_seq`, and the free-program run dropped: `Ca` is paid before
`c₁`, `Cb` before `c₂`, and `**` — here `minusECost_add_of_le` — is what
lets the second payment be moved in front of the first program's own
deduction. -/

/-- Port of the source's `hnr_bind_manual_free` at `Com.seq` (P4/D-d). -/
theorem hnr_seq {Γ Γ₁ Γ' : Assn} {c₁ c₂ : Com} {x : κ'} {d : κ} {Rh : α → κ' → Assn}
    {R : β → κ → Assn} {m : NRest α ECost} {f : α → NRest β ECost}
    (D1 : hnRefine Γ c₁ Γ₁ x Rh m)
    (D2 : ∀ a : α, (NRest.returnT a : NRest α ECost) ≤ m →
      hnRefine (hnCtxt Rh a x ∗ Γ₁) c₂ Γ' d R (f a)) :
    hnRefine Γ (.seq c₁ c₂) Γ' d R (m.bindT f) := by
  intro _ M F s cr hm hs
  cases hmm : m with
  | fail =>
    rw [hmm, NRest.bindT_fail] at hm
    exact absurd hm (NRest.fail_ne_rest M)
  | rest Mm =>
    -- (1) `D1` at the incoming state.
    obtain ⟨ra, Ca, hCa, w1⟩ := hnRefineD D1 hmm hs
    -- (2) `Mm ra` is a real cost, so `returnT ra ≤ m` — `D2`'s guard.
    have hne : Mm ra ≠ ⊥ := by
      intro hbot
      rw [hbot, le_bot_iff] at hCa
      exact WithBot.coe_ne_bot hCa
    obtain ⟨Car, hCar⟩ := WithBot.ne_bot_iff_exists.1 hne
    have hCaCar : Ca ≤ Car := by
      rw [← hCar, WithBot.coe_le_coe] at hCa
      exact hCa
    have hret : (NRest.returnT ra : NRest α ECost) ≤ m := by
      rw [hmm]; exact returnT_le_rest_of_coe_le hCa
    -- (3) the bind's `sSup` dominates the `ra` branch, so `f ra` cannot fail.
    have hmemle : (f ra).consume Car ≤ NRest.rest M := by
      rw [← hm, hmm, NRest.bindT_rest]
      exact le_sSup ⟨ra, Car, hCar.symm, rfl⟩
    cases hfra : f ra with
    | fail =>
      rw [hfra, NRest.consume_fail] at hmemle
      exact absurd hmemle (NRest.not_fail_le_rest M)
    | rest Mf =>
      -- (4) open the first run, and hand its state to `D2`.
      obtain ⟨s₁, κa, hbs1, hq1, hi1⟩ := w1
      have hperm : (Γ₁ ∗ Rh ra x ∗ F ∗ GC) = ((hnCtxt Rh ra x ∗ Γ₁) ∗ (F ∗ GC)) := by
        simp only [hnCtxt_def]
        ac_rfl
      have hq1' : irSTATE ((hnCtxt Rh ra x ∗ Γ₁) ∗ (F ∗ GC))
          (s₁, minusECost (cr + Ca) κa) := by
        rw [← hperm]; exact hq1
      obtain ⟨rb, Cb, hCb, w2⟩ := hnRefineD (D2 ra hret) hfra hq1'
      -- (5) the same argument for the second payment.
      have hnb : Mf rb ≠ ⊥ := by
        intro hbot
        rw [hbot, le_bot_iff] at hCb
        exact WithBot.coe_ne_bot hCb
      obtain ⟨Cbr, hCbr⟩ := WithBot.ne_bot_iff_exists.1 hnb
      have hCbCbr : Cb ≤ Cbr := by
        rw [← hCbr, WithBot.coe_le_coe] at hCb
        exact hCb
      -- (6) the composed cost really is bounded by the bind's cost function.
      have hmid : ((Car + Cbr : ECost) : WithBot ECost) ≤ M rb := by
        rw [hfra, NRest.consume_rest, NRest.rest_le_rest_iff] at hmemle
        have h : WithBot.map (fun z => Car + z) (Mf rb) ≤ M rb := hmemle rb
        rw [← hCbr] at h
        simpa using h
      have hMrb : ((Ca + Cb : ECost) : WithBot ECost) ≤ M rb := by
        refine le_trans ?_ hmid
        rw [WithBot.coe_le_coe]
        exact add_le_add hCaCar hCbCbr
      -- (7) the `**` step, and the two runs glued by `wp_seq`.
      have hbal : minusECost (cr + Ca) κa + Cb = minusECost (cr + (Ca + Cb)) κa := by
        rw [minusECost_add_of_le hi1, add_assoc]
      have hi1' : leCostECost κa (cr + (Ca + Cb)) := by
        rw [← add_assoc]; exact leCostECost_add_right hi1 Cb
      refine ⟨rb, Ca + Cb, hMrb, ?_⟩
      rw [wp_seq]
      refine ⟨s₁, κa, hbs1, ?_, hi1'⟩
      rw [← hbal]
      refine wp_mono_ir (fun _ q hq => ?_) w2
      show irSTATE (Γ' ∗ R rb d ∗ F ∗ GC) q
      have hgc : (Γ' ∗ R rb d ∗ (F ∗ GC) ∗ GC) = (Γ' ∗ R rb d ∗ F ∗ GC) := by
        rw [sepConj_assoc F GC GC, GC_absorb]
      rw [← hgc]
      exact hq

/-! ### Return, const, assert -/

/-- The source's `hnr_RETURN_pass`, paying for `skip` (P4/D-f). Ownership
of `p` moves from `Γ` to the result slot; the `hnInvalid` marker records
the structure. -/
theorem hnr_return_pass (R : α → κ → Assn) (a : α) (p : κ) :
    hnRefine (¤¤Currency.skip 1 ∗ hnCtxt R a p) .skip (hnInvalid R a p) p R
      (NRest.returnT a) := by
  refine hnRefineI fun M F s cr hm hs => ⟨a, 0, ?_, ?_⟩
  · rw [NRest.returnT, NRest.rest_inj_iff] at hm
    simp [← hm]
  · rw [add_zero]
    have hs' : irSTATE (¤¤Currency.skip 1 ∗ (R a p ∗ F)) (s, cr) := by
      rw [← sepConj_assoc]; exact hs
    obtain ⟨hafford, hrest⟩ := costCredits_split hs'
    have hpp : purePart (R a p) := by
      rcases id hrest with ⟨u, v, h1, h2, hu, hv⟩
      exact ⟨u, hu⟩
    rw [wp_skip]
    refine ⟨hafford, ?_⟩
    have h2 : irSTATE ((R a p ∗ F) ∗ GC)
        (s, minusECost cr (ACost.cost Currency.skip 1)) :=
      start_entailsE hrest (entails_gc_right _)
    rw [sepConj_assoc] at h2
    have hinv : hnInvalid R a p = (□ : Assn) := by
      rw [show hnInvalid R a p = ⌜purePart (R a p)⌝ from rfl, predLift_of_true hpp]
    show irSTATE (hnInvalid R a p ∗ R a p ∗ F ∗ GC) _
    rw [hinv, emp_sepConj]
    exact h2

/-- The `irHtriple` behind `hnr_const`: overwrite a junk cell with a
literal. -/
theorem const_junk_rule (x : String) (n : Val) :
    irHtriple (¤¤Currency.const 1 ∗ junkCell x) (.const x n) ((□ : Assn) ∗ natAssn n x) := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  have hp1 : irSTATE (junkCell x ∗ (¤¤Currency.const 1 ∗ F)) (s, cr) := by
    have he : ((¤¤Currency.const 1 ∗ junkCell x) ∗ F)
        = junkCell x ∗ (¤¤Currency.const 1 ∗ F) := by ac_rfl
    rw [← he]; exact hp
  rw [junkCell_def, sepEx_sepConj] at hp1
  obtain ⟨v, hv⟩ := hp1
  have hv' : irSTATE ((¤¤Currency.const 1 ∗ (x ↦ᵥ v)) ∗ F) (s, cr) := by
    have he : ((¤¤Currency.const 1 ∗ (x ↦ᵥ v)) ∗ F)
        = (x ↦ᵥ v) ∗ (¤¤Currency.const 1 ∗ F) := by ac_rfl
    rw [he]; exact hv
  refine wp_mono_ir (fun _ q hq => ?_) (const_triple x n v F (s, cr) hv')
  show ((((□ : Assn) ∗ natAssn n x) ∗ GC) ∗ F) (irα q)
  rw [emp_sepConj, natAssn_def]
  exact conj_entails_mono (entails_gc_right (x ↦ᵥ n)) (entails_refl F) _ hq

/-- The source's `hnr_RETURN_pure` at the IR: an abstract `returnT n` is
realized by writing the literal into an owned junk cell (P4/D-f). -/
theorem hnr_const (x : String) (n : Val) :
    hnRefine (¤¤Currency.const 1 ∗ junkCell x) (.const x n) (□ : Assn) x natAssn
      (NRest.returnT n) :=
  hnRefineI_htriple (const_junk_rule x n)

/-- The source's `hnr_ASSERT`. -/
theorem hnr_assert {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn} {Φ : Prop}
    {m : NRest α ECost} (h : Φ → hnRefine Γ c Γ' d R m) :
    hnRefine Γ c Γ' d R (NRest.bindT (NRest.assert Φ) fun _ => m) := by
  by_cases hΦ : Φ
  · rw [NRest.assert_pos hΦ, NRest.returnT_bindT]
    exact h hΦ
  · rw [NRest.assert_neg hΦ, NRest.bindT_fail]
    exact hnr_fail

end Suite

/-! ## 5. The MERGE calculus (P4/D-e)

Entailment-form, with the source's free-program arguments dropped. Wave C's
merge tactic is what will consume these; nothing does yet. `MERGE_END` is
stated at `□` because `FRI_END ≡ □` in the source (`Frame_Infer.thy`) and
the Lean `SepSolver` has no separate marker constant. -/

/-- The source's `MERGE Γ1 f1 Γ2 f2 Γ'`, minus the free programs. -/
def MERGE (Γ₁ Γ₂ Γ' : Assn) : Prop := (Γ₁ ⊢ Γ') ∧ (Γ₂ ⊢ Γ')

/-- The source's `MERGE1`. -/
def MERGE1 {α κ : Type} (R1 R2 R' : α → κ → Assn) : Prop :=
  ∀ (a : α) (c : κ), MERGE (R1 a c) (R2 a c) (R' a c)

/-- The source's `MERGE_STAR`. -/
theorem MERGE_STAR {α κ : Type} {R1 R2 R' : α → κ → Assn} {Γ₁ Γ₂ Γ' : Assn} (a : α) (c : κ)
    (h1 : MERGE1 R1 R2 R') (h2 : MERGE Γ₁ Γ₂ Γ') :
    MERGE (hnCtxt R1 a c ∗ Γ₁) (hnCtxt R2 a c ∗ Γ₂) (hnCtxt R' a c ∗ Γ') :=
  ⟨conj_entails_mono (h1 a c).1 h2.1, conj_entails_mono (h1 a c).2 h2.2⟩

/-- The source's `MERGE_triv`. -/
theorem MERGE_triv (Γ : Assn) : MERGE Γ Γ Γ := ⟨entails_refl Γ, entails_refl Γ⟩

/-- The source's `MERGE_END`, at `FRI_END = □`. -/
theorem MERGE_END : MERGE (□ : Assn) □ □ := MERGE_triv □

/-- The source's `MERGE1_eq`. -/
theorem MERGE1_eq {α κ : Type} (P : α → κ → Assn) : MERGE1 P P P :=
  fun a c => MERGE_triv (P a c)

/-- The source's `MERGE1_invalids`, left half, at `deadAssn` (P4/D-c/e). -/
theorem MERGE1_invalids_left {α κ : Type} (R : α → κ → Assn) :
    MERGE1 (deadAssn R) R (deadAssn R) :=
  fun a c => ⟨entails_refl _, entails_dead R a c⟩

/-- The source's `MERGE1_invalids`, right half. -/
theorem MERGE1_invalids_right {α κ : Type} (R : α → κ → Assn) :
    MERGE1 R (deadAssn R) (deadAssn R) :=
  fun a c => ⟨entails_dead R a c, entails_refl _⟩

/-! ## 6. Gate (refute-before-prove)

Every rule above was first instantiated at the concrete programs below and
its statement checked against the IR's cost ledger; the two negative
controls are the checks that failed by design. -/

namespace Gate

/-- The ledger fact the wrong-currency control turns into a refutation. -/
example : Currency.const ≠ Currency.skip := by decide

/-- Positive control: `hnr_const` at a concrete cell and literal. -/
example : hnRefine (¤¤Currency.const 1 ∗ junkCell "x") (.const "x" 7) (□ : Assn) "x" natAssn
    (NRest.returnT 7) := hnr_const "x" 7

/-- Positive control: the pass rule at a concrete cell. -/
example : hnRefine (¤¤Currency.skip 1 ∗ hnCtxt natAssn 7 "x") .skip
    (hnInvalid natAssn 7 "x") "x" natAssn (NRest.returnT 7) :=
  hnr_return_pass natAssn 7 "x"

/-- Positive control: `hnr_seq` composes two `const`s, threading the frame
through `hnRefine_frame'` / `hnRefine_frame''` and dropping the first
result's ownership to junk through `hnRefine_cons_res`. -/
example :
    hnRefine ((¤¤Currency.const 1 ∗ junkCell "x") ∗ (¤¤Currency.const 1 ∗ junkCell "y"))
      (.seq (.const "x" 3) (.const "y" 4)) (junkCell "x" ∗ (□ : Assn)) "y" natAssn
      (NRest.bindT (NRest.returnT 3) fun _ => NRest.returnT 4) :=
  hnr_seq (x := "x") (Rh := fun _ (c : String) => junkCell c)
    (hnRefine_cons_res (hnRefine_frame' (hnr_const "x" 3)) natAssn_entails_junkCell)
    (fun _ _ => hnRefine_cons_pre (hnRefine_frame'' (hnr_const "y" 4))
      (by rw [emp_sepConj]; exact entails_refl _))

/-- Positive control: `hnr_assert` at a true and at a false assertion. -/
example : hnRefine (¤¤Currency.const 1 ∗ junkCell "x") (.const "x" 7) (□ : Assn) "x" natAssn
    (NRest.bindT (NRest.assert (0 < 1)) fun _ => NRest.returnT 7) :=
  hnr_assert fun _ => hnr_const "x" 7

example : hnRefine (¤¤Currency.const 1 ∗ junkCell "x") (.const "x" 7) (□ : Assn) "x" natAssn
    (NRest.bindT (NRest.assert (1 < 0)) fun _ => NRest.returnT 7) :=
  hnr_assert fun h => absurd h (by decide)

/-- A one-cell state and the frame owning the rest of it. -/
def nzState : State := State.ofPairs [("x", 0)] []

/-- **Negative control 1 — wrong cost vector.** A rule that pays one
`ir.skip` credit cannot run a `const` op: the balance affords nothing in
the `ir.const` currency, and `M = single 7 0` caps the extra credits the
abstract side may hand over at zero. -/
theorem hnr_const_wrong_currency :
    ¬ hnRefine (¤¤Currency.skip 1 ∗ junkCell "x") (.const "x" 7) (□ : Assn) "x" natAssn
      (NRest.returnT 7) := by
  intro h
  have hpre : irSTATE ((¤¤Currency.skip 1 ∗ junkCell "x") ∗
      EXACT (((vcells nzState).erase "x", acells nzState, hcells nzState), 0))
      (nzState, ACost.cost Currency.skip (1 : ℕ∞)) := by
    show ((¤¤Currency.skip 1 ∗ junkCell "x") ∗
      EXACT (((vcells nzState).erase "x", acells nzState, hcells nzState), 0))
      ((vcells nzState, acells nzState, hcells nzState), ACost.cost Currency.skip (1 : ℕ∞))
    rw [sepConj_assoc, costCredits_def]
    refine credits_sepConj_iff.2 ⟨0, (add_zero _).symm, ?_⟩
    rw [junkCell_def, sepEx_sepConj]
    exact ⟨0, ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩⟩
  obtain ⟨ra, Ca, hCa, w⟩ :=
    hnRefineD (F := EXACT (((vcells nzState).erase "x", acells nzState, hcells nzState), 0))
      h rfl hpre
  have hra : ra = 7 := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff] at hCa
    exact WithBot.coe_ne_bot hCa
  subst hra
  rw [NRest.single_self, ← WithBot.coe_zero, WithBot.coe_le_coe] at hCa
  have hCa0 : Ca = 0 := le_antisymm hCa (ACost.le_def.2 fun _ => by simp)
  rw [hCa0, add_zero, wp_const] at w
  have hcur : Currency.const ≠ Currency.skip := by decide
  have := w.2.1 Currency.const
  simp [hcur] at this

/-- **Negative control 2 — cells are never absorbed.** `MERGE` cannot
merge an owned cell into `□`: `GC` absorbs credits only (P4/D-g), so a
junk cell is not entailed away. -/
theorem merge_junk_not_emp : ¬ MERGE (□ : Assn) (junkCell "x") □ := by
  intro h
  have h0 : junkCell "x" ((Cells.single "x" (0 : Val), 0), (0 : ECost)) :=
    ⟨0, ⟨rfl, rfl⟩, rfl⟩
  have h1 := h.2 _ h0
  have h2 : Cells.single "x" (0 : Val) = 0 := congrArg (fun p => p.1.1) h1
  have h3 := congrFun h2 "x"
  simp [Cells.single] at h3

end Gate

end Lax13Proofs.Refine.Sepref
