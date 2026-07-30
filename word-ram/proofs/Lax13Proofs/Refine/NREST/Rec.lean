import Lax13Proofs.Refine.NREST.Sanity

/-!
General recursion for `NREST`: the `RECT` fixed point.

Port of the `RECT` section of `thys/nrest/NREST.thy` of
`isabelle_llvm_time` (Haslbeck–Lammich, ESOP'21 artifact) at the pin
recorded in `plans/word-ram/refinement-tower/design.md` §1,
github.com/lammich/isabelle_llvm_time @ 42dd7f5, together with the
pieces of AFP `Refine_Monadic` (Isabelle2025-2) that `mono2` is stated
over — `Generic/RefineG_Domain.thy` and `Refine_Mono_Prover.thy` — and
the two definitions of HOL's own `Partial_Function.thy` those rest on.
Fetched 2026-07-29 from the pins.

## The source, verbatim

`NREST.thy`, section `RECT`:

```isabelle
definition "mono2 B ≡ flatf_mono_ge B ∧ mono B"
lemma trimonoD_flatf_ge: "mono2 B ⟹ flatf_mono_ge B"
lemma trimonoD_mono:     "mono2 B ⟹ mono B"
lemma trimonoI[refine_mono]: "⟦flatf_mono_ge B; mono B⟧ ⟹ mono2 B"

definition "RECT B x = (if mono2 B then (gfp B x) else (top::'a::complete_lattice))"
definition "RECT' F x =
  consume (RECT (λD x. F (λx. consume (D x) (cost ''call'' 1)) x) x) (cost ''call'' 1)"

lemma RECT_unfold: "⟦mono2 B⟧ ⟹ RECT B = B (RECT B)"
  unfolding RECT_def [abs_def] by (auto dest: trimonoD_mono simp: gfp_unfold[symmetric])

lemma RECT_mono[refine_mono]:
  assumes [simp]: "mono2 B'"  assumes LE: "⋀F x. (B' F x) ≤ (B F x)"
  shows "(RECT B' x) ≤ (RECT B x)"

lemma flat_ge_RECT_aux:
  assumes "mono2 B'" and "⋀x. flat_ge (f x) (g x)"
  shows "flat_ge (B' (λx. consume (f x) c) x) (B' (λx. consume (g x) c) x)"
lemma flat_ge_RECT_aux2:
  assumes "mono2 B'" and "⋀x. f x ≤ g x"
  shows "(B' (λx. consume (f x) c) x) ≤ (B' (λx. consume (g x) c) x)"
lemma RECT'_unfold_aux:
  shows "mono2 B ⟹ mono2 (λD. B (λx. consume (D x) (cost ''call'' 1)))"
lemma RECT'_unfold:
  assumes "mono2 B" shows "RECT' B x = consume (B (λx. RECT' B x) x) (cost ''call'' 1)"
lemma RECT'_mono[refine_mono]:
  assumes m2[simp]: "mono2 B'"  assumes LE: "⋀F x. (B' F x) ≤ (B F x)"
  shows "(RECT' B' x) ≤ (RECT' B x)"
```

The `refine_mono` seed lemmas of the same file:

```isabelle
lemma bindT_mono'[refine_mono]:       fixes m :: "('a,enat) nrest"
  shows "m ≤ m' ⟹ (⋀x. f x ≤ f' x) ⟹ bindT m f ≤ bindT m' f'"
lemma bindT_acost_mono'[refine_mono]: fixes m :: "('a,(_,enat)acost) nrest"  (same statement)
lemma bindT_flat_mono[refine_mono]:   fixes M :: "('a,enat) nrest"
  shows "⟦ flat_ge M M'; ⋀x. flat_ge (f x) (f' x) ⟧ ⟹ flat_ge (bindT M f) (bindT M' f')"
lemma g_bindT_flat_mono[refine_mono]: fixes M :: "('a,(_,enat)acost) nrest"  (same statement)
lemma flat_ge_consume[refine_mono]:   "flat_ge f f' ⟹ flat_ge (consume f T) (consume f' T)"
lemma consume_mono'[refine_mono]:     "f ≤ f' ⟹ (consume f T) ≤ (consume f' T)"
lemma [refine_mono]: "(⋀f g x. (⋀x. f x ≤ g x) ⟹ B f x ≤ B g x) ⟹ mono B"
```

and, from `Refine_Mono_Prover.thy` (locale `mono_setup_loc`, parametric
in an ordering `le` with `refl: le x x`):

```isabelle
lemma monoI: "(⋀f g x. (⋀x. le (f x) (g x)) ⟹ le (B f x) (B g x))
  ⟹ monotone (fun_ord le) (fun_ord le) B"
lemma mono_if:  "⟦le t t'; le e e'⟧ ⟹ le (If b t e) (If b t' e')"
lemma mono_let: "(⋀x. le (f x) (f' x)) ⟹ le (Let x f) (Let x f')"
lemmas mono_thms[refine_mono] = monoI mono_if mono_let refl
```

The orders those are stated over, from `RefineG_Domain.thy` and HOL's
`Partial_Function.thy`:

```isabelle
definition "flat_ord b x y ⟷ x = b ∨ x = y"
definition "fun_ord ord f g ⟷ (∀x. ord (f x) (g x))"
definition "monotone orda ordb f ⟷ (∀x y. orda x y ⟶ ordb (f x) (f y))"
abbreviation "flat_ge ≡ flat_ord top"          abbreviation "flatf_ord b ≡ fun_ord (flat_ord b)"
abbreviation "flatf_ge ≡ flatf_ord top"        abbreviation "flatf_mono b ≡ monotone (flatf_ord b) (flatf_ord b)"
abbreviation "flatf_mono_ge ≡ flatf_mono top"
lemma flat_ord_simps[simp]: "flat_ord b b x"
lemma flat_ord_compat: "flat_ge x y ⟹ x ≥ y"
```

## Substrate decisions and deviations, individually

**S1 (naming).** The all-caps combinator names `RECT`, `RECT'` are kept
verbatim rather than lower-cased the way `Basic.lean` lower-cased
`RETURNT ↦ returnT`: `RECT` is the name the *design record* cites (§3
P1 table, §8 ledger D6 "abstract `RECT` must be refined to `whileT`-form
before synthesis"), and the source's rule names (`RECT_unfold`,
`RECT_mono`, `RECT_rule_arb`) read it as a proper noun. The
lower-casing convention still governs the monad primitives.
HOL's `monotone` is renamed `monotoneRel` because mathlib's `Monotone`
already means the order-to-order special case; `flat_ord`/`fun_ord`
become `flatOrd`/`funOrd` by the usual casing.

**S2 (the fixpoint form).** `RECT` is the source's own definition —
`gfp` in the *lattice* order of the result type, guarded by `mono2`,
with `⊤` (`FAILT`) outside the guard — not a nicer or better-behaved
fixed point. `gfp` here is HOL's `gfp f = Sup {u. u ≤ f u}`; mathlib's
`OrderHom.gfp` is *the same formula* on a bundled monotone map, so
`Lax13Proofs.Refine.gfp` below is the unbundled spelling of it and
`gfp_unfold` is `OrderHom.map_gfp`. This is the mathlib gap filled
locally: mathlib has no unbundled `gfp` taking the monotonicity as a
separate hypothesis, and `RECT`'s definition needs one because the
hypothesis sits inside a classical `if`.

**S3 (what is *not* ported).** `RECT_flat_gfp_def`
(`RECT B x = if mono2 B then flatf_gfp B x else ⊤`) and the
`flatf_gfp`/`ccpo`-`fixp` infrastructure of `RefineG_Domain.thy` are
*not* ported. The source proves `RECT_unfold`, `RECT_mono`, `RECT'` and
the whole `whileT` layer from the `gfp` form and `trimonoD_mono` alone;
`flatf_mono_ge` is consumed only as the *predicate* half of `mono2`,
which is why the predicate is ported and the `ccpo` fixed point behind
it is not. `RECT_rule_arb` / `RECT_wf_induct` / `RECT'_wf_induct_arb`
(well-founded induction over a `RECT`) are deferred to the
backwards-reasoning file, where they are used.

**S4 (the mono prover).** These are plain lemmas. The source's
`refine_mono` *attribute* and its ML prover (`Refine_Mono_Prover`) are
P2/P4 infrastructure (design record §8 ledger D1, §10.3: one shared
attribute implementation parameterized by DB name); until it lands, the
seed set is applied by hand. `mono_setup_loc` is a locale parametric in
the ordering, so its `monoI`/`mono_if`/`mono_let` are ported once,
relationally, and instantiate at both `≤` and `flatGe`.

**S5 (capital, not re-proved).** The source's `bindT_mono'` /
`bindT_acost_mono'` are `NRest.bindT_mono` of `Pw.lean` (same
statement — hypothesis `∀x. f x ≤ f' x`, not the reachability-guarded
one of the unprimed `bindT_mono`), and `consume_mono'` is
`NRest.consume_mono … le_rfl`. Neither is restated here; the two
`flat_ge`-side seeds, which have no `Pw.lean` counterpart, are proved
below. Both are proved once generically rather than twice
monomorphically: the source's monomorphism at `enat`/`acost` there comes
from its pointwise-reasoning lemmas being stated at those carriers, not
from any missing mathematical content — no continuity of `+` over `Sup`
is involved, unlike the monad laws (fidelity note F7).

**S6 (the D4 gate).** `RECT` is noncomputable twice over (the classical
`if` on `mono2`, and `sSup`), so the gate is the fuel route the campaign
brief sanctions, in its exact form: `fuelIter B n = B^[n] ⊤`, with
`RECT_le_fuelIter` (always) and `RECT_eq_of_fuelIter_stable` (as soon as
the iteration stabilises, by `le_gfp`). Both are *theorems*, so a
`#guard` about the executable twin `Sanity.fuelIterE` is a `#guard`
about `RECT` itself. This is why the file imports the gate module
`Sanity.lean`: the finite carrier, its `DecidableEq`, and the executable
`bindE`/`returnE` twins already live there.

**S7 (ND-MC rebase P0.3 — the termination export, and the shape it
cannot have; ledger R0/D-a).** `Sepref/Translate.lean`'s P4/D-cv and
`Sepref/CombRules.lean`'s P4/D-ai both name one missing P1 lemma as the
blocker that keeps the Sepref loop rule *measured*:

> `nofailT (RECT B s) → ∃ n, fuelIter B n s = RECT B s`.

**That statement is false**, and `NoFuelBound` below refutes it with a
`mono2` body over `ℕ∞`: state `0` chooses a natural nondeterministically
(`⨆`), each `n + 1` counts down to a `⊥` at `1`. Every approximant is
`⊤` at `0` — for each fuel there is a branch that has not finished —
while `RECT` itself is `⊥` there. Unbounded nondeterminism is exactly
what ℕ-indexed fuel cannot see, and it is not exotic: a `whileT` whose
body is a `spec` has it. What survives of the fuel route is its *other*
half, strengthened from stability-everywhere to non-failure-here:
`RECT_eq_fuelIter_of_ne_top` — as soon as one approximant is not `⊤` at
a state, it *is* `RECT` there. The witness is `fuelResolved`, the
approximant with its still-unresolved states sent to `⊥` instead of `⊤`,
which flat-monotonicity makes a post-fixed point.

The export the loop rule actually needs is therefore not about fuel at
all: it is `le_RECT_of_postfixed` / `RECT_eq_top_of_postfixed` — "a
post-fixed point is below `RECT`, so a state where one is `⊤` is a state
where `RECT` is `⊤`". Termination then comes out as an *accessibility*
predicate rather than a natural number (`Sepref/CombRules.lean`'s
`LoopTerm`, ledger R0/D-b), which is well-founded without being finitely
branching — the exact gap the counterexample marks. `⊤` on the
non-accessible states is the post-fixed point that pushes divergence
into `FAILT`, and that is what retires `LOOP_VARIANT`.
-/

namespace Lax13Proofs.Refine

/-! ### The flat orderings

HOL's `flat_ord`, `fun_ord` and `monotone`, and the `flat_ge` /
`flatf_ge` / `flatf_mono_ge` abbreviations built from them. The flat
order reads "either it diverges (`⊤ = FAILT`) or it is literally the
same computation"; it is the order recursion is a fixed point in, and
`mono2` asks for monotonicity in it *and* in the refinement order. -/

/-- HOL's `flat_ord b x y ⟷ x = b ∨ x = y` (`Partial_Function.thy`). -/
def flatOrd {β : Type} (b x y : β) : Prop := x = b ∨ x = y

/-- The `refl` of `mono_setup_loc`: the flat order is reflexive, which
is what discharges every recursion-free branch of a `mono2` obligation
(the `RETURNT` branch of `whileT`'s body, for instance). -/
@[simp] theorem flatOrd_refl {β : Type} (b x : β) : flatOrd b x x := Or.inr rfl

/-- The source's `flat_ord_simps`: the distinguished element is below
everything. -/
@[simp] theorem flatOrd_base {β : Type} (b y : β) : flatOrd b b y := Or.inl rfl

/-- HOL's `fun_ord`: an ordering on a function space, pointwise. -/
def funOrd {α β : Type} (ord : β → β → Prop) (f g : α → β) : Prop := ∀ x, ord (f x) (g x)

/-- HOL's `monotone orda ordb f`, the two-relation notion of
monotonicity. Renamed from `monotone` because mathlib's `Monotone` is
already the `≤`-to-`≤` special case. -/
def monotoneRel {σ τ : Type} (orda : σ → σ → Prop) (ordb : τ → τ → Prop) (f : σ → τ) : Prop :=
  ∀ x y, orda x y → ordb (f x) (f y)

/-- The source's `flat_ge ≡ flat_ord top`. -/
abbrev flatGe {β : Type} [Top β] : β → β → Prop := flatOrd ⊤

/-- The source's `flatf_ge ≡ fun_ord (flat_ord top)`. -/
abbrev flatfGe {α β : Type} [Top β] : (α → β) → (α → β) → Prop := funOrd flatGe

/-- The source's `flatf_mono_ge ≡ monotone flatf_ge flatf_ge`. -/
abbrev flatfMonoGe {α β : Type} [Top β] (B : (α → β) → α → β) : Prop :=
  monotoneRel flatfGe flatfGe B

/-- The source's `flat_ord_compat`, second clause: the flat order
implies the lattice order, reversed. -/
theorem flatGe_le {β : Type} [CompleteLattice β] {x y : β} (h : flatGe x y) : y ≤ x := by
  rcases h with rfl | rfl
  · exact le_top
  · exact le_rfl

/-- The source's `flatf_ord_compat`, second clause. -/
theorem flatfGe_le {α β : Type} [CompleteLattice β] {f g : α → β} (h : flatfGe f g) : g ≤ f :=
  fun x => flatGe_le (h x)

/-! ### The seed rules of the mono prover

`mono_setup_loc`'s `monoI`, `mono_if`, `mono_let` and `refl`, ported
once at the locale's generality (parametric in the ordering), plus the
source's anonymous `[refine_mono]` rule that produces mathlib's
`Monotone` from a pointwise statement. -/

/-- The source's `mono_setup_loc.monoI`. -/
theorem monotoneRel_funOrd {α β : Type} {ord : β → β → Prop} {B : (α → β) → α → β}
    (h : ∀ f g x, (∀ y, ord (f y) (g y)) → ord (B f x) (B g x)) :
    monotoneRel (funOrd ord) (funOrd ord) B :=
  fun f g hfg x => h f g x hfg

/-- The source's anonymous `[refine_mono]` rule
`(⋀f g x. (⋀x. f x ≤ g x) ⟹ B f x ≤ B g x) ⟹ mono B`. -/
theorem monotone_of_apply {α β : Type} [Preorder β] {B : (α → β) → α → β}
    (h : ∀ f g x, (∀ y, f y ≤ g y) → B f x ≤ B g x) : Monotone B :=
  fun f g hfg x => h f g x fun y => hfg y

/-- The source's `mono_setup_loc.mono_if`. -/
theorem monotoneRel_ite {β : Type} {ord : β → β → Prop} {t t' e e' : β}
    (b : Prop) [Decidable b] (ht : ord t t') (he : ord e e') :
    ord (if b then t else e) (if b then t' else e') := by
  split
  · exact ht
  · exact he

/-- The source's `mono_setup_loc.mono_let`. -/
theorem monotoneRel_let {α β : Type} {ord : β → β → Prop} {f f' : α → β} (x : α)
    (h : ∀ y, ord (f y) (f' y)) : ord (f x) (f' x) := h x

/-! ### `gfp`

HOL's `gfp f = Sup {u. u ≤ f u}`, unbundled. mathlib's `OrderHom.gfp`
is that formula on a bundled monotone map, so everything here is a
one-line transport (substrate decision S2). -/

/-- HOL's `gfp`, taking monotonicity as a separate hypothesis rather
than bundling it, because `RECT`'s definition guards on `mono2 B`
classically and so cannot carry a bundled map. -/
noncomputable def gfp {β : Type} [CompleteLattice β] (B : β → β) : β := sSup {u | u ≤ B u}

/-- HOL's `gfp_upperbound`. -/
theorem le_gfp {β : Type} [CompleteLattice β] {B : β → β} {u : β} (h : u ≤ B u) : u ≤ gfp B :=
  le_sSup h

/-- HOL's `gfp_least`. -/
theorem gfp_le {β : Type} [CompleteLattice β] {B : β → β} {a : β}
    (h : ∀ u, u ≤ B u → u ≤ a) : gfp B ≤ a := sSup_le h

/-- HOL's `gfp_mono`; no monotonicity of either map is needed. -/
theorem gfp_mono {β : Type} [CompleteLattice β] {B B' : β → β} (h : ∀ u, B' u ≤ B u) :
    gfp B' ≤ gfp B := sSup_le_sSup fun u hu => hu.trans (h u)

/-- The unbundled `gfp` *is* mathlib's `OrderHom.gfp`, by definition. -/
theorem gfp_eq_orderHom_gfp {β : Type} [CompleteLattice β] (B : β →o β) :
    gfp (⇑B) = OrderHom.gfp B := rfl

/-- HOL's `gfp_unfold`. -/
theorem gfp_unfold {β : Type} [CompleteLattice β] {B : β → β} (h : Monotone B) :
    gfp B = B (gfp B) := (OrderHom.map_gfp ⟨B, h⟩).symm

/-! ### `mono2` and `RECT` -/

/-- The source's `mono2 B ≡ flatf_mono_ge B ∧ mono B`, the "trimono"
side condition every `RECT` carries. -/
def mono2 {α β : Type} [CompleteLattice β] (B : (α → β) → α → β) : Prop :=
  flatfMonoGe B ∧ Monotone B

/-- The source's `trimonoD_flatf_ge`. -/
theorem mono2.flatfMonoGe {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) : flatfMonoGe B := h.1

/-- The source's `trimonoD_mono`. -/
theorem mono2.monotone {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) : Monotone B := h.2

/-- The source's `trimonoI`. -/
theorem mono2_intro {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (hf : flatfMonoGe B) (hm : Monotone B) : mono2 B := ⟨hf, hm⟩

open Classical in
/-- The source's `RECT B x = (if mono2 B then gfp B x else top)`: the
greatest fixed point of `B` in the refinement order when `B` is
trimonotone, and the failing computation otherwise. Total correctness:
the *greatest* fixed point is the one that returns `FAILT` where the
recursion may not terminate. -/
noncomputable def RECT {α β : Type} [CompleteLattice β] (B : (α → β) → α → β) (x : α) : β :=
  if mono2 B then gfp B x else ⊤

/-- Under the side condition, `RECT B` is exactly `gfp B`. -/
theorem RECT_eq_gfp {α β : Type} [CompleteLattice β] {B : (α → β) → α → β} (h : mono2 B) :
    RECT B = gfp B := by
  funext x
  simp only [RECT, if_pos h]

/-- Without the side condition, `RECT B` is the failing computation. -/
theorem RECT_of_not_mono2 {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : ¬ mono2 B) (x : α) : RECT B x = ⊤ := by
  simp only [RECT, if_neg h]

/-- **The source's `RECT_unfold`.** -/
theorem RECT_unfold {α β : Type} [CompleteLattice β] {B : (α → β) → α → β} (h : mono2 B) :
    RECT B = B (RECT B) := by
  rw [RECT_eq_gfp h]
  exact gfp_unfold h.monotone

/-- `RECT_unfold`, applied. -/
theorem RECT_unfold_apply {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) (x : α) : RECT B x = B (RECT B) x := by
  conv_lhs => rw [RECT_unfold h]

/-- The source's `RECT_mono`. Only the *smaller* body needs the side
condition: without it the larger `RECT` is `⊤`. -/
theorem RECT_mono {α β : Type} [CompleteLattice β] {B B' : (α → β) → α → β}
    (h : mono2 B') (hle : ∀ F x, B' F x ≤ B F x) (x : α) : RECT B' x ≤ RECT B x := by
  rw [RECT_eq_gfp h]
  by_cases hB : mono2 B
  · rw [RECT_eq_gfp hB]
    exact gfp_mono (fun F y => hle F y) x
  · rw [RECT_of_not_mono2 hB]
    exact le_top

namespace NRest

variable {α β γ κ : Type}

/-! ### The `flat_ge` half of the `refine_mono` seed set

The `≤` half is `Pw.lean`'s `bindT_mono` and `consume_mono` (substrate
decision S5); these two have no counterpart there. -/

/-- The source's `flat_ge_consume`. -/
theorem flatGe_consume [CompleteLattice γ] [Add γ] {m m' : NRest α γ}
    (h : flatGe m m') (t : γ) : flatGe (consume m t) (consume m' t) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The source's `bindT_flat_mono` / `g_bindT_flat_mono`, proved once
for every carrier (substrate decision S5). A bind is flat-below another
one when either the bound computation already diverges, or every
reachable continuation does, or nothing differs at all. -/
theorem bindT_flatGe [CompleteLattice γ] [AddMonoid γ] {M M' : NRest α γ}
    {f f' : α → NRest β γ} (hM : flatGe M M') (hf : ∀ x, flatGe (f x) (f' x)) :
    flatGe (bindT M f) (bindT M' f') := by
  rcases hM with rfl | rfl
  · exact Or.inl rfl
  · cases M with
    | fail => exact Or.inl rfl
    | rest X =>
      by_cases hex : ∃ x, X x ≠ ⊥ ∧ f x = fail
      · obtain ⟨x, hx, hfx⟩ := hex
        refine Or.inl ?_
        rw [top_eq_fail, bindT_rest_eq_iSup]
        exact iSup_eq_fail_iff.mpr ⟨x, by rw [hfx]; exact consumeB_fail_of_ne_bot hx⟩
      · refine Or.inr ?_
        have hex' : ∀ x, X x ≠ ⊥ → f x ≠ fail := fun x hx hfx => hex ⟨x, hx, hfx⟩
        rw [bindT_rest_eq_iSup, bindT_rest_eq_iSup]
        refine iSup_congr fun x => ?_
        rcases withBot_eq_bot_or_coe (X x) with h | ⟨t, h⟩
        · rw [h, consumeB_bot, consumeB_bot]
        · have hne : X x ≠ ⊥ := by rw [h]; exact WithBot.coe_ne_bot
          rcases hf x with hfx | hfx
          · exact absurd (by rw [hfx, top_eq_fail] : f x = fail) (hex' x hne)
          · rw [hfx]

end NRest

/-! ### `RECT'`

The source's cost-carrying variant: one `''call''` unit is paid on entry
and one on every recursive call. Stated, as the source states it, over
the currency-indexed cost carrier — `cost ''call'' 1` is what forces the
currency type to be `String` and the value type to carry a `1`. -/

open Classical in
/-- The source's
`RECT' F x = consume (RECT (λD x. F (λx. consume (D x) (cost ''call'' 1)) x) x) (cost ''call'' 1)`. -/
noncomputable def RECT' {α β γ : Type} [CompleteLattice γ] [AddMonoid γ] [One γ]
    (B : (α → NRest β (ACost String γ)) → α → NRest β (ACost String γ)) (x : α) :
    NRest β (ACost String γ) :=
  NRest.consume
    (RECT (fun D x => B (fun y => NRest.consume (D y) (ACost.cost "call" 1)) x) x)
    (ACost.cost "call" 1)

/-- The source's `flat_ge_RECT_aux`. -/
theorem flatGe_RECT_aux {α β γ : Type} [CompleteLattice γ] [AddMonoid γ]
    {B : (α → NRest β (ACost String γ)) → α → NRest β (ACost String γ)} (hB : mono2 B)
    {f g : α → NRest β (ACost String γ)} (h : ∀ x, flatGe (f x) (g x))
    (c : ACost String γ) (x : α) :
    flatGe (B (fun y => NRest.consume (f y) c) x) (B (fun y => NRest.consume (g y) c) x) :=
  hB.flatfMonoGe _ _ (fun y => NRest.flatGe_consume (h y) c) x

/-- The source's `flat_ge_RECT_aux2`. -/
theorem le_RECT_aux2 {α β γ : Type} [CompleteLattice γ] [AddCommMonoid γ]
    [IsOrderedAddMonoid γ] {B : (α → NRest β (ACost String γ)) → α → NRest β (ACost String γ)}
    (hB : mono2 B) {f g : α → NRest β (ACost String γ)} (h : ∀ x, f x ≤ g x)
    (c : ACost String γ) (x : α) :
    B (fun y => NRest.consume (f y) c) x ≤ B (fun y => NRest.consume (g y) c) x :=
  hB.monotone
    (show (fun y => NRest.consume (f y) c) ≤ (fun y => NRest.consume (g y) c) from
      fun y => NRest.consume_mono (h y) le_rfl) x

/-- The source's `RECT'_unfold_aux`: wrapping every recursive call in a
`consume` preserves the side condition. -/
theorem mono2_consume_call {α β γ : Type} [CompleteLattice γ] [AddCommMonoid γ]
    [IsOrderedAddMonoid γ] {B : (α → NRest β (ACost String γ)) → α → NRest β (ACost String γ)}
    (hB : mono2 B) (c : ACost String γ) :
    mono2 (fun D x => B (fun y => NRest.consume (D y) c) x) :=
  ⟨fun _ _ hfg x => flatGe_RECT_aux hB hfg c x, fun _ _ hfg x => le_RECT_aux2 hB hfg c x⟩

/-- **The source's `RECT'_unfold`.** -/
theorem RECT'_unfold {α β γ : Type} [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    [One γ] {B : (α → NRest β (ACost String γ)) → α → NRest β (ACost String γ)}
    (hB : mono2 B) (x : α) :
    RECT' B x = NRest.consume (B (fun y => RECT' B y) x) (ACost.cost "call" 1) := by
  have h2 := mono2_consume_call hB (ACost.cost "call" 1)
  simp only [RECT']
  conv_lhs => rw [RECT_unfold_apply h2]

/-- The source's `RECT'_mono`. -/
theorem RECT'_mono {α β γ : Type} [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    [One γ] {B B' : (α → NRest β (ACost String γ)) → α → NRest β (ACost String γ)}
    (h : mono2 B') (hle : ∀ F x, B' F x ≤ B F x) (x : α) : RECT' B' x ≤ RECT' B x :=
  NRest.consume_mono
    (RECT_mono (mono2_consume_call h (ACost.cost "call" 1)) (fun _ y => hle _ y) x) le_rfl

/-! ### Finite approximation of `RECT`, and the exactness criterion

The fuel route of substrate decision S6. `fuelIter B n` is `B` applied
`n` times to `⊤`; `RECT B` is below every approximant, and equals the
approximant as soon as the iteration stops moving — because `RECT` is
the *greatest* fixed point and a stable approximant is a post-fixed
point. Both directions are theorems, which is what makes the executable
checks at the bottom of the file checks about `RECT`. -/

/-- The `n`-th approximant of `RECT B`: `B` applied `n` times to `⊤`. -/
noncomputable def fuelIter {α β : Type} [CompleteLattice β] (B : (α → β) → α → β) :
    ℕ → (α → β)
  | 0 => ⊤
  | n + 1 => B (fuelIter B n)

@[simp] theorem fuelIter_zero {α β : Type} [CompleteLattice β] (B : (α → β) → α → β) :
    fuelIter B 0 = ⊤ := rfl

@[simp] theorem fuelIter_succ {α β : Type} [CompleteLattice β] (B : (α → β) → α → β) (n : ℕ) :
    fuelIter B (n + 1) = B (fuelIter B n) := rfl

/-- `RECT` is below every approximant. -/
theorem RECT_le_fuelIter {α β : Type} [CompleteLattice β] {B : (α → β) → α → β} (h : mono2 B)
    (n : ℕ) (x : α) : RECT B x ≤ fuelIter B n x := by
  induction n generalizing x with
  | zero => exact le_top
  | succ n ih =>
    rw [RECT_unfold_apply h, fuelIter_succ]
    exact h.monotone (show RECT B ≤ fuelIter B n from fun y => ih y) x

/-- **The exactness criterion.** Once one more step of the iteration
changes nothing, the approximant *is* `RECT B`. -/
theorem RECT_eq_of_fuelIter_stable {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) {n : ℕ} (hstab : ∀ x, B (fuelIter B n) x = fuelIter B n x) (x : α) :
    RECT B x = fuelIter B n x := by
  refine le_antisymm (RECT_le_fuelIter h n x) ?_
  rw [RECT_eq_gfp h]
  exact le_gfp (B := B) (u := fuelIter B n) (fun y => (hstab y).ge) x

/-! ### From non-failure to termination (S7, ledger R0/D-a)

Three lemmas and one refutation.

`le_RECT_of_postfixed` is the whole *positive* content: `RECT` is a
greatest fixed point, so every post-fixed point is below it, and a state
where a post-fixed point is `⊤` is a state where `RECT` is `⊤`
(`RECT_eq_top_of_postfixed`). Read contrapositively — "`RECT` does not
fail here, so this state is not in the stuck set" — that is the
termination export, and it is what `Sepref/CombRules.lean` builds
`LoopTerm` on.

`RECT_eq_fuelIter_of_ne_top` is what survives of the fuel route: not
`∃ n` (refuted below), but the pointwise strengthening of
`RECT_eq_of_fuelIter_stable`. -/

/-- **A post-fixed point is below `RECT`.** `le_gfp` at `RECT`'s own
side condition. -/
theorem le_RECT_of_postfixed {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) {w : α → β} (hw : ∀ x, w x ≤ B w x) (x : α) : w x ≤ RECT B x := by
  rw [RECT_eq_gfp h]
  exact le_gfp (B := B) (u := w) (fun y => hw y) x

/-- **The divergence criterion.** A post-fixed point that is `⊤` at a
state pins `RECT` to `⊤` there: this is how "the recursion cannot get
out of this set of states" becomes "the recursion fails on it". -/
theorem RECT_eq_top_of_postfixed {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) {w : α → β} (hw : ∀ x, w x ≤ B w x) {x : α} (hx : w x = ⊤) :
    RECT B x = ⊤ :=
  top_le_iff.mp (hx ▸ le_RECT_of_postfixed h hw x)

/-- The approximants descend in the *flat* order: one more step either
resolves a state or leaves it at `⊤`. -/
theorem flatfGe_fuelIter_succ {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) (n : ℕ) : flatfGe (fuelIter B n) (fuelIter B (n + 1)) := by
  induction n with
  | zero => intro x; rw [fuelIter_zero, Pi.top_apply]; exact flatOrd_base _ _
  | succ n ih => exact fun x => h.flatfMonoGe _ _ ih x

/-- Once an approximant is not `⊤` at a state, no later one moves. -/
theorem fuelIter_succ_of_ne_top {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) {n : ℕ} {x : α} (hx : fuelIter B n x ≠ ⊤) :
    fuelIter B (n + 1) x = fuelIter B n x :=
  ((flatfGe_fuelIter_succ h n x).resolve_left hx).symm

theorem fuelIter_eq_of_le_of_ne_top {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) {n m : ℕ} {x : α} (hnm : n ≤ m) (hx : fuelIter B n x ≠ ⊤) :
    fuelIter B m x = fuelIter B n x := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [fuelIter_succ_of_ne_top h (by rw [ih]; exact hx), ih]

open Classical in
/-- The *resolved part* of an approximant: the same function, with the
states it has not resolved yet sent to `⊥` instead of `⊤`. Flat
monotonicity is exactly the statement that `B` cannot tell the two
apart where it matters, which makes this a post-fixed point. -/
noncomputable def fuelResolved {α β : Type} [CompleteLattice β] (B : (α → β) → α → β) (n : ℕ)
    (x : α) : β :=
  if fuelIter B n x = ⊤ then ⊥ else fuelIter B n x

theorem fuelResolved_of_ne_top {α β : Type} [CompleteLattice β] {B : (α → β) → α → β} {n : ℕ}
    {x : α} (hx : fuelIter B n x ≠ ⊤) : fuelResolved B n x = fuelIter B n x := by
  rw [fuelResolved, if_neg hx]

theorem fuelResolved_of_top {α β : Type} [CompleteLattice β] {B : (α → β) → α → β} {n : ℕ}
    {x : α} (hx : fuelIter B n x = ⊤) : fuelResolved B n x = ⊥ := by
  rw [fuelResolved, if_pos hx]

theorem flatfGe_fuelResolved {α β : Type} [CompleteLattice β] {B : (α → β) → α → β} (n : ℕ) :
    flatfGe (fuelIter B n) (fuelResolved B n) := by
  intro y
  by_cases hy : fuelIter B n y = ⊤
  · exact Or.inl hy
  · exact Or.inr (fuelResolved_of_ne_top hy).symm

theorem fuelResolved_postfixed {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) (n : ℕ) (y : α) : fuelResolved B n y ≤ B (fuelResolved B n) y := by
  by_cases hy : fuelIter B n y = ⊤
  · rw [fuelResolved_of_top hy]; exact bot_le
  · have h1 : B (fuelIter B n) y ≠ ⊤ := by
      show fuelIter B (n + 1) y ≠ ⊤
      rw [fuelIter_succ_of_ne_top h hy]; exact hy
    have h2 := (h.flatfMonoGe _ _ (flatfGe_fuelResolved n) y).resolve_left h1
    rw [fuelResolved_of_ne_top hy, ← h2]
    show fuelIter B n y ≤ fuelIter B (n + 1) y
    rw [fuelIter_succ_of_ne_top h hy]

/-- **The exactness criterion, pointwise.** `RECT_eq_of_fuelIter_stable`
asks the whole iteration to stop moving; this asks only that *this*
state be resolved, which is the form a loop rule can use. -/
theorem RECT_eq_fuelIter_of_ne_top {α β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    (h : mono2 B) {n : ℕ} {x : α} (hx : fuelIter B n x ≠ ⊤) : RECT B x = fuelIter B n x := by
  refine le_antisymm (RECT_le_fuelIter h n x) ?_
  have hle := le_RECT_of_postfixed h (fuelResolved_postfixed h n) x
  rwa [fuelResolved_of_ne_top hx] at hle

/-! ### The converse is false (S7, refute-before-prove)

The statement `Sepref/Translate.lean` (P4/D-cv) and
`Sepref/CombRules.lean` (P4/D-ai) both name as the missing export —
"`nofailT (RECT B s) → ∃ n, fuelIter B n s = RECT B s`" — does not hold.

The body below is `mono2`, its `RECT` is `⊥` (not `⊤`, so it does not
fail) at `0`, and *every* approximant is `⊤` there. The reason is
unbounded nondeterminism: `B f 0 = ⨆ m, f (m + 1)` offers infinitely
many branches, branch `m` needs `m` steps, and no single fuel covers
them all — while the fixed point, which is a supremum and not a limit of
approximants, sees all of them at once. Two edges worth naming: at fuel
`0` every approximant is `⊤` by definition, so the statement is not
merely unproved but has no true instance to lean on there; and the
no-failure hypothesis is not the culprit — `Sanity.RECT_bodyLoop`
already shows a diverging body's `RECT` *is* `FAILT`, so dropping the
hypothesis breaks the statement in the other direction too. -/

namespace NoFuelBound

/-- The refuting body. `0` chooses a natural nondeterministically, `1`
returns, `m + 2` counts down. -/
noncomputable def B (f : ℕ → ℕ∞) : ℕ → ℕ∞
  | 0 => ⨆ m, f (m + 1)
  | 1 => ⊥
  | (m + 2) => f (m + 1)

/-- The body satisfies `RECT`'s side condition. The flat half is the
interesting one: an infinite supremum is flat-monotone because a single
`⊤` argument already sends it to `⊤`. -/
theorem mono2_B : mono2 B := by
  constructor
  · refine monotoneRel_funOrd fun f g x hfg => ?_
    match x with
    | 0 =>
      by_cases hex : ∃ m, f (m + 1) = ⊤
      · obtain ⟨m, hm⟩ := hex
        exact Or.inl (top_le_iff.mp (hm ▸ le_iSup (fun k => f (k + 1)) m))
      · exact Or.inr (iSup_congr fun m => (hfg (m + 1)).resolve_left fun hm => hex ⟨m, hm⟩)
    | 1 => exact Or.inr rfl
    | (m + 2) => exact hfg (m + 1)
  · refine monotone_of_apply fun f g x hfg => ?_
    match x with
    | 0 => exact iSup_mono fun m => hfg (m + 1)
    | 1 => exact le_rfl
    | (m + 2) => exact hfg (m + 1)

/-- Fuel `k` has not reached the branches beyond `k`. -/
theorem fuelIter_succ_top : ∀ k n : ℕ, k ≤ n → fuelIter B k (n + 1) = ⊤ := by
  intro k
  induction k with
  | zero => intro n _; rw [fuelIter_zero, Pi.top_apply]
  | succ k ih =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show B (fuelIter B k) (m + 2) = ⊤
    exact ih m (by omega)

/-- …so at the choosing state every approximant fails. -/
theorem fuelIter_zero_top (k : ℕ) : fuelIter B k 0 = ⊤ := by
  cases k with
  | zero => rw [fuelIter_zero, Pi.top_apply]
  | succ k =>
    show (⨆ m, fuelIter B k (m + 1)) = ⊤
    exact top_le_iff.mp ((fuelIter_succ_top k k le_rfl) ▸ le_iSup (fun m => fuelIter B k (m + 1)) k)

/-- The fixed point itself is `⊥` everywhere: every branch terminates,
so every post-fixed point is forced down to `⊥` by the countdown. -/
theorem RECT_B_eq_bot : RECT B = ⊥ := by
  rw [RECT_eq_gfp mono2_B]
  refine le_antisymm (gfp_le fun u hu => ?_) bot_le
  have h1 : ∀ n, u (n + 1) = ⊥ := by
    intro n
    induction n with
    | zero => exact le_bot_iff.mp (hu 1)
    | succ n ih =>
      have h2 := hu (n + 2)
      rw [show B u (n + 2) = u (n + 1) from rfl, ih, le_bot_iff] at h2
      exact h2
  intro x
  match x with
  | 0 =>
    refine le_trans (hu 0) ?_
    show (⨆ m, u (m + 1)) ≤ ⊥
    exact iSup_le fun m => (h1 m).le
  | (n + 1) => exact (h1 n).le

/-- **The refutation.** A `mono2` body whose `RECT` does not fail at `0`
and which no fuel ever reaches there. -/
theorem no_fuel_bound :
    mono2 B ∧ RECT B 0 ≠ ⊤ ∧ ∀ n, fuelIter B n 0 ≠ RECT B 0 := by
  refine ⟨mono2_B, ?_, fun n => ?_⟩
  · rw [RECT_B_eq_bot, Pi.bot_apply]
    exact bot_ne_top
  · rw [fuelIter_zero_top n, RECT_B_eq_bot, Pi.bot_apply]
    exact top_ne_bot

end NoFuelBound

/-! ### The D4 gate

Campaign rule D4 (design record §7, ledger D4): every layer gets
executable instances and checks the day it lands. The carrier, its
`DecidableEq`, and the executable `returnE` twin are `Sanity.lean`'s.

The recursion checked is a countdown that pays one time unit per step:
`bodyC D s = if s = 0 then returnT 0 else consume (D (dec s)) 1`. It is
computable (`consume` is a plain match and `returnE` is the executable
twin of `returnT`), so the *whole* fixed point is pinned down by the two
theorems above from a kernel-checked stability test. -/

namespace Sanity

/-- The countdown step of the sample recursion. -/
def dec (s : Fin 3) : Fin 3 := if s = 2 then 1 else 0

/-- The sample body: count down to `0`, paying one time unit per step.
`returnE` is `Sanity.lean`'s executable `returnT` (`returnE_eq`), so
this is a genuine `NRest` recursion, written computably. -/
def bodyC (D : Fin 3 → SRest) (s : Fin 3) : SRest :=
  if s = 0 then returnE 0 else NRest.consume (D (dec s)) 1

@[simp] theorem bodyC_zero (D : Fin 3 → SRest) : bodyC D 0 = returnE 0 := by
  simp [bodyC]

@[simp] theorem bodyC_of_ne {s : Fin 3} (h : s ≠ 0) (D : Fin 3 → SRest) :
    bodyC D s = NRest.consume (D (dec s)) 1 := by
  simp [bodyC, h]

/-- The sample body satisfies the `RECT` side condition. This is the
seed set of `Rec.lean` doing its job: `monotoneRel_ite` for the branch,
`flatGe_consume` / `consume_mono` for the recursive call. -/
theorem mono2_bodyC : mono2 bodyC := by
  refine ⟨monotoneRel_funOrd fun _ _ s hfg => ?_, monotone_of_apply fun _ _ s hfg => ?_⟩
  · exact monotoneRel_ite (s = 0) (flatOrd_refl _ _) (NRest.flatGe_consume (hfg _) 1)
  · exact monotoneRel_ite (s = 0) le_rfl (NRest.consume_mono (hfg _) le_rfl)

/-- The executable twin of `fuelIter`: `⊤` is `NRest.fail`, which is a
constructor and therefore computes, while `⊤` goes through the
noncomputable complete-lattice instance. -/
def fuelIterE (B : (Fin 3 → SRest) → Fin 3 → SRest) : ℕ → (Fin 3 → SRest)
  | 0 => fun _ => NRest.fail
  | n + 1 => B (fuelIterE B n)

@[simp] theorem fuelIterE_zero (B : (Fin 3 → SRest) → Fin 3 → SRest) :
    fuelIterE B 0 = fun _ => NRest.fail := rfl

@[simp] theorem fuelIterE_succ (B : (Fin 3 → SRest) → Fin 3 → SRest) (n : ℕ) :
    fuelIterE B (n + 1) = B (fuelIterE B n) := rfl

/-- **The bridge.** Everything `#guard`ed below is `#guard`ed about
`fuelIter`, hence — through `RECT_eq_of_fuelIter_stable` — about
`RECT`. -/
theorem fuelIterE_eq (B : (Fin 3 → SRest) → Fin 3 → SRest) (n : ℕ) :
    fuelIterE B n = fuelIter B n := by
  induction n with
  | zero => funext x; rw [fuelIterE_zero, fuelIter_zero, Pi.top_apply, NRest.top_eq_fail]
  | succ n ih => rw [fuelIterE_succ, fuelIter_succ, ih]

/-- The sample recursion, solved: three iterations stabilise it, so
`RECT bodyC` *is* the executable `fuelIterE bodyC 3`. The stability
premise is discharged by kernel computation. -/
theorem RECT_bodyC : RECT bodyC = fuelIterE bodyC 3 := by
  have hstab : ∀ x, bodyC (fuelIterE bodyC 3) x = fuelIterE bodyC 3 x := by decide
  rw [fuelIterE_eq] at hstab ⊢
  exact funext fun x => RECT_eq_of_fuelIter_stable mono2_bodyC hstab x

-- The countdown from each starting point, at the cost it should carry.
#guard fuelIterE bodyC 3 0 = returnE 0
#guard fuelIterE bodyC 3 1 = NRest.rest ![((1 : ℕ∞) : WithBot ℕ∞), ⊥, ⊥]
#guard fuelIterE bodyC 3 2 = NRest.rest ![((2 : ℕ∞) : WithBot ℕ∞), ⊥, ⊥]

-- Two iterations are *not* enough from `2`: the approximant still fails
-- there, which is exactly what `RECT_le_fuelIter` predicts and what
-- makes the stability test at `3` non-vacuous.
#guard fuelIterE bodyC 2 2 = (NRest.fail : SRest)
#guard fuelIterE bodyC 4 = fuelIterE bodyC 3

/-- The value of the fixed point at `2`, as a statement about `RECT`. -/
theorem RECT_bodyC_two : RECT bodyC 2 = NRest.rest ![((2 : ℕ∞) : WithBot ℕ∞), ⊥, ⊥] := by
  rw [RECT_bodyC]
  decide

/-- A body that never terminates: `RECT` of it is the failing
computation, which is the content of taking the *greatest* fixed
point. -/
def bodyLoop (D : Fin 3 → SRest) (s : Fin 3) : SRest := NRest.consume (D s) 1

/-- The looping body satisfies the side condition too — divergence is
not a failure of `mono2`. -/
theorem mono2_bodyLoop : mono2 bodyLoop :=
  ⟨monotoneRel_funOrd fun _ _ s hfg => NRest.flatGe_consume (hfg s) 1,
    monotone_of_apply fun _ _ s hfg => NRest.consume_mono (hfg s) le_rfl⟩

/-- Its fixed point is `FAILT`: the iteration is already stable at fuel
`0`, so the greatest fixed point is `⊤`. This is the total-correctness
reading of `RECT` in one line. -/
theorem RECT_bodyLoop (s : Fin 3) : RECT bodyLoop s = NRest.fail := by
  have hstab : ∀ x, bodyLoop (fuelIterE bodyLoop 0) x = fuelIterE bodyLoop 0 x := by decide
  rw [fuelIterE_eq] at hstab
  rw [RECT_eq_of_fuelIter_stable mono2_bodyLoop hstab s, fuelIter_zero, Pi.top_apply,
    NRest.top_eq_fail]

end Sanity

end Lax13Proofs.Refine
