import Lax13Proofs.Refine.Ir.Assn
import Lax13Proofs.Refine.NREST.BackwardsReasoning

/-!
The generic weakest-precondition layer, the cost framework, and the IR's
own `wp`.

Port of `thys/vcg/Sep_Generic_Wp.thy` at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 (`isabelle_llvm_time` @
`42dd7f5`), quoted verbatim in
`plans/word-ram/refinement-tower/p3-ir-sl-extracts.md` §1 and
`p3-sl-deep-extracts.md` §1:

* the locale pair `generic_wp_defs` / `generic_wp` — `htripleF`,
  `htriple` with the `∀F` framing baked into the *definition*,
  `htriple_as_F_eq`, and, under `wp_comm_inf`, `frame_rule`, `cons_rule`,
  `htriple_gc` / `htriple_to_gc`;
* the locale `cost_framework` — parameters `I` (affordability) and
  `minus` (deduction), its four named assumption groups
  (`minus_0`, `I_0`, `minus_minus_add`, `I1`–`I3`), and the
  `(cost, ecost)` interpretation `le_cost_ecost` / `minus_ecost_cost`;
* the wp equations the source proves inside `cost_framework`
  (`wp_return`, `wp_bind`, `wp_consume`) and the control-flow rules
  `llc_if_simp` / `llc_while_unfold` of `LLVM_Shallow_RS.thy`.

## Judgment calls

**D-o — a locale becomes a section with a parameter, plus a `Prop` class
for its assumptions.** `generic_wp_defs` fixes `wp` and defines two
constants over it: that is a Lean `section` with `wp` an ordinary
argument. `generic_wp` adds one assumption and derives four facts from
it: that is a `Prop` class `WpCommInf wp`, whose *instance* is the
source's `interpretation`. The correspondence is exact — the source
inherits `frame_rule`/`cons_rule` "by interpretation rather than
re-proof" (the extract's own words), and so does `Ir.wp`, by
`instance : WpCommInf wp`. Nothing here is a typeclass for elegance's
sake: `WpCommInf` has one field and one instance in the whole tower.

**D-p — `Ir.wp` is defined at the concrete `(Cost, ECost)` instance, not
generically over a `CostFramework`.** The source's own interpretation of
`cost_framework` at `le_cost_ecost` / `minus_ecost_cost` is *unnamed*,
which deposits `wp`, `wp_bind`, `wp_consume`, … as top-level facts at
that one instance; there is no second instantiation anywhere in the
artifact. Ours is the same: the class is declared and proved (so the six
laws are on the record, under the source's names, as *theorems* rather
than assumptions — the locale's axioms are our obligations), and `wp` is
monomorphic, which is what the design record's watch item asks for.

**D-q — the IR has no result value, so the generic layer is
instantiated at `R = Unit`.** `htriple`'s postcondition is `R → A → Prop`
because the source's programs are `'a llM`. `Ir.Com` is a *statement*
language (design record §6: three-address, results land in cells), so
`Ir.wp`'s postcondition is `Unit → …`. Design record §5's `hn_refine`
draft writes `Ir.wp c (fun r => llState (Γ' ∗ R ra r ∗ F ∗ GC))` with
`r : Ir.Val`; at `R = Unit` that clause becomes
`Ir.wp c (fun _ => irSTATE (Γ' ∗ (∃ᵃ r, x ↦ᵥ r ∗ R ra r) ∗ F ∗ GC))` —
the result is *read out of the destination cell*, and P4's hnr rules
name that cell. The vocabulary of §5 is otherwise untouched (`Assn`,
`irSTATE`, `GC`, `Ir.wp` all resolve).

**D-r — the source's `bind` is our `seq`, and its `consume` is the
per-op cost line of `BigStep`.** There is no monad (ledger D2), so
`wp_bind : wp (m ⤳ f) Q s = wp m (λx. wp (f x) Q) s` ports as
`wp_seq : wp (.seq c d) Q p ↔ wp c (fun _ => wp d Q) p`, and its proof
consumes exactly the same four locale assumptions in exactly the same
places (`minus_minus_add` for the balance, `I2`/`I1` to split
affordability of a sum, `I3` to re-assemble it — `afford_add_iff` below
isolates them). `wp_consume : wp (consume c) Q (s,cr) ⟷ I c cr ∧ Q ()
(s, minus cr c)` has no standalone counterpart because no IR op is a
bare `consume`; instead *every* primitive equation below has the shape
`I κ cr ∧ Q () (effect s, minus cr κ)`, which is `wp_consume` glued to
the op's effect — the artifact's `consume (cost ''load'' 1) ≫ do the
thing`, one op at a time. `wp_return` is `wp_skip`, our unit of `seq`
(judgment call D-c of `Syntax.lean`), except that `skip` is *not* free:
it charges `ir.skip`, so `wp_skip` is `wp_return` composed with one
`wp_consume`.

**D-s — the while rule lives in `Triples.lean`, not here.** The source
puts `llc_while_annot_rule` in `LLVM_Shallow_RS.thy` next to
`ll_load_rule`, not in `Sep_Generic_Wp.thy`; this file therefore carries
only `wp_while_unfold` (its `llc_while_unfold`) and the well-founded
wp-level rule `wp_while_wf` the separation-logic rule is built from.
-/

namespace Lax13Proofs.Refine.Ir

/-! ## 1. `generic_wp_defs` and `generic_wp`

`wp` is a parameter throughout (that is what "generic" means): the same
`htriple` / frame / consequence machinery serves the cost-carrying `wp`
below and would serve any other. -/

section GenericWp

variable {C R S A : Type} [Zero A] [Add A] [SepDisj A] [SepAlgebra A]

/-- The source's `htripleF`: a Hoare triple at *one* frame. -/
def htripleF (wp : C → (R → S → Prop) → S → Prop) (α : S → A) (F P : A → Prop) (c : C)
    (Q : R → A → Prop) : Prop :=
  ∀ s, (P ∗ F) (α s) → wp c (fun r s' => (Q r ∗ F) (α s')) s

/-- The source's `htriple`: the frame is quantified *inside* the
definition, which is what makes framing definitional rather than a
separate law. -/
def htriple (wp : C → (R → S → Prop) → S → Prop) (α : S → A) (P : A → Prop) (c : C)
    (Q : R → A → Prop) : Prop :=
  ∀ F s, (P ∗ F) (α s) → wp c (fun r s' => (Q r ∗ F) (α s')) s

/-- The source's `htriple_as_F_eq`. -/
theorem htriple_as_F_eq {wp : C → (R → S → Prop) → S → Prop} {α : S → A} {P : A → Prop} {c : C}
    {Q : R → A → Prop} : htriple wp α P c Q ↔ ∀ F, htripleF wp α F P c Q := Iff.rfl

/-- The source's `generic_wp` locale: the one assumption from which
`frame_rule`, `cons_rule` and `htriple_to_gc` follow (judgment call
D-o). An instance is the source's `interpretation`. -/
class WpCommInf (wp : C → (R → S → Prop) → S → Prop) : Prop where
  /-- The source's `wp_comm_inf`. -/
  wp_comm_inf (c : C) (Q Q' : R → S → Prop) : wp c Q ⊓ wp c Q' = wp c (Q ⊓ Q')

export WpCommInf (wp_comm_inf)

/-- Monotonicity of `wp`, the one consequence of `wp_comm_inf` the rules
below actually use. -/
theorem wp_mono {wp : C → (R → S → Prop) → S → Prop} [WpCommInf wp] {c : C}
    {Q Q' : R → S → Prop} (hQ : ∀ r s, Q r s → Q' r s) {s : S} (h : wp c Q s) : wp c Q' s := by
  have hQQ : (Q ⊓ Q') = Q := by
    funext r s'
    exact propext ⟨fun h' => h'.1, fun h' => ⟨h', hQ r s' h'⟩⟩
  have hc := wp_comm_inf (wp := wp) c Q Q'
  rw [hQQ] at hc
  have h2 : (wp c Q ⊓ wp c Q') s := by rw [hc]; exact h
  exact (show wp c Q s ∧ wp c Q' s from h2).2

variable {wp : C → (R → S → Prop) → S → Prop} {α : S → A}

/-- The source's `frame_rule`. Framing is definitional: the proof is the
associativity of `∗` and nothing else, which is why the source's own
proof is one `fastforce` and why no `wp` assumption is consumed. -/
theorem frame_rule {P : A → Prop} {c : C} {Q : R → A → Prop} (F : A → Prop)
    (h : htriple wp α P c Q) : htriple wp α (P ∗ F) c (fun r => Q r ∗ F) := by
  intro F' s hs
  rw [sepConj_assoc] at hs
  have := h (F ∗ F') s hs
  simpa [sepConj_assoc] using this

/-- The source's `cons_rule`. -/
theorem cons_rule [WpCommInf wp] {P P' : A → Prop} {c : C} {Q Q' : R → A → Prop}
    (h : htriple wp α P c Q) (hP : ∀ s, P' s → P s) (hQ : ∀ r s, Q r s → Q' r s) :
    htriple wp α P' c Q' := by
  intro F s hs
  have hs' : (P ∗ F) (α s) :=
    conj_entails_mono (fun h' hh => hP h' hh) (entails_refl F) _ hs
  refine wp_mono (fun r s' hs'' => ?_) (h F s hs')
  exact conj_entails_mono (fun h' hh => hQ r h' hh) (entails_refl F) _ hs''

/-- The source's `htriple_gc`: the garbage-collecting variant, with a
postcondition that absorbs whatever the program did not need. -/
def htripleGc (wp : C → (R → S → Prop) → S → Prop) (GC : A → Prop) (α : S → A) (P : A → Prop)
    (c : C) (Q : R → A → Prop) : Prop :=
  htriple wp α P c (fun r => Q r ∗ GC)

/-- The source's `htriple_to_gc`. -/
theorem htriple_to_gc [WpCommInf wp] {GC : A → Prop} {P : A → Prop} {c : C} {Q : R → A → Prop}
    (hGC : (□ : A → Prop) ⊢ GC) (h : htriple wp α P c Q) : htripleGc wp GC α P c Q := by
  refine cons_rule h (fun _ h' => h') (fun r s hs => ?_)
  have hs' : (Q r ∗ □) s := by rwa [sepConj_emp]
  exact conj_entails_mono (entails_refl (Q r)) hGC _ hs'

end GenericWp

/-! ## 2. The `cost_framework` locale

`I c cr` is "the concrete cost `c` is affordable against the balance
`cr`" and `minus cr c` is "the balance after spending `c`". The four
assumption groups are what makes the sequential composition rule go
through, and nothing else about the two carriers is assumed. -/

/-- The source's `cost_framework` locale, as a `Prop` class over its two
parameters (judgment call D-o). Its assumptions are our obligations:
`instCostFrameworkIr` below discharges every one of them at the IR's
instance. -/
class CostFramework {CC CA : Type} [AddMonoid CC] (I : CC → CA → Prop)
    (minus : CA → CC → CA) : Prop where
  /-- The source's `minus_0`. -/
  minus_0 (y : CA) : minus y 0 = y
  /-- The source's `I_0`. -/
  I_0 (cr : CA) : I 0 cr
  /-- The source's `minus_minus_add`. -/
  minus_minus_add (a : CA) (b c : CC) : minus (minus a b) c = minus a (b + c)
  /-- The source's `I1`. -/
  I1 {a b : CC} {c : CA} : I (a + b) c → I b (minus c a)
  /-- The source's `I2`. -/
  I2 {a b : CC} {c : CA} : I (a + b) c → I a c
  /-- The source's `I3`. -/
  I3 {a b : CC} {c : CA} : I a (minus c b) → I b c → I (b + a) c

/-! ### The IR's interpretation: `(Cost, ECost)`

The source's `le_cost_ecost` / `minus_ecost_cost`, at our two carriers —
run costs are finite (`Cost = ACost String ℕ`, judgment call D-e of
`Semantics.lean`) and the balance is `ECost = ACost String ℕ∞` (design
record §10.1). The lift `ℕ → ℕ∞` is one-sided, so no `∞ - ∞` can
arise. -/

/-- The source's `lift_acost`, already ported as `liftACost`
(`NREST/BackwardsReasoning.lean`, from `Enat_Cost.thy`); design record
§5 calls this seam `cash`. No new definition is introduced — the seam
and the source's own lift are the same function. -/
abbrev cash : Cost → ECost := liftACost

/-- The source's `le_cost_ecost`: `∀x. enat (the_acost cc x) ≤ the_acost ca x`. -/
def leCostECost (cc : Cost) (ca : ECost) : Prop := ∀ x, (cc.toFun x : ℕ∞) ≤ ca.toFun x

/-- The source's `minus_ecost_cost`, through the resource subtraction
`-ᵣ` of `Cost/ACost.lean` (which is HOL's `minus` on `enat`, delta B1
there). Since the subtrahend is a lifted *finite* cost, `-ᵣ` and
mathlib's truncated `-` agree here — `minusECost_eq_sub` records it. -/
def minusECost (ca : ECost) (cc : Cost) : ECost := ca -ᵣ cash cc

@[simp] theorem toFun_leCostECost {cc : Cost} {ca : ECost} :
    leCostECost cc ca ↔ ∀ x, (cc.toFun x : ℕ∞) ≤ ca.toFun x := Iff.rfl

@[simp] theorem toFun_minusECost (ca : ECost) (cc : Cost) (k : String) :
    (minusECost ca cc).toFun k = ca.toFun k -ᵣ (cc.toFun k : ℕ∞) := rfl

/-! ### ℕ∞ arithmetic with a finite subtrahend

The five pointwise facts the obligations below are made of. Each is the
same two-case argument — the balance is `⊤`, or it is a natural number
and `omega` finishes — and each is stated at the *one* shape that can
occur here: the subtrahend is always a lifted *run* cost, hence finite,
so `∞ - ∞` never arises (design record §10.1, and the reason delta B1's
`-ᵣ` and mathlib's `-` cannot come apart at this seam). -/

theorem enat_resSub_coe (c : ℕ∞) (m : ℕ) : c -ᵣ (m : ℕ∞) = c - (m : ℕ∞) := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  · rw [enat_resSub_of_ne_top hc]

theorem enat_coe_le_resSub {m n : ℕ} {c : ℕ∞} (h : ((m + n : ℕ) : ℕ∞) ≤ c) :
    (n : ℕ∞) ≤ c -ᵣ (m : ℕ∞) := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  · lift c to ℕ using hc
    rw [Nat.cast_le] at h
    rw [enat_resSub_coe, ← ENat.coe_sub, Nat.cast_le]
    omega

theorem enat_add_le_of_le_resSub {m n : ℕ} {c : ℕ∞} (h₁ : (n : ℕ∞) ≤ c -ᵣ (m : ℕ∞))
    (h₂ : (m : ℕ∞) ≤ c) : ((m + n : ℕ) : ℕ∞) ≤ c := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · exact le_top
  · lift c to ℕ using hc
    rw [enat_resSub_coe, ← ENat.coe_sub, Nat.cast_le] at h₁
    rw [Nat.cast_le] at h₂ ⊢
    omega

theorem enat_resSub_resSub (c : ℕ∞) (m n : ℕ) :
    (c -ᵣ (m : ℕ∞)) -ᵣ (n : ℕ∞) = c -ᵣ ((m + n : ℕ) : ℕ∞) := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  · lift c to ℕ using hc
    simp only [enat_resSub_coe, ← ENat.coe_sub]
    congr 1
    omega

theorem enat_coe_add_resSub (m : ℕ) (b : ℕ∞) : ((m : ℕ∞) + b) -ᵣ (m : ℕ∞) = b := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  · lift b to ℕ using hb
    simp only [enat_resSub_coe, ← Nat.cast_add, ← ENat.coe_sub]
    congr 1
    omega

/-- The source's definition verbatim:
`minus_ecost_cost ca cc ≡ acostC (λx. the_acost ca x - enat (the_acost cc x))`. -/
theorem minusECost_eq_sub (ca : ECost) (cc : Cost) :
    minusECost ca cc = ⟨fun x => ca.toFun x - (cc.toFun x : ℕ∞)⟩ := by
  ext k
  rw [toFun_minusECost]
  exact enat_resSub_coe _ _

/-! ### The six obligations

The source's locale assumptions, proved here under the source's names.
Everything below — `wp_seq` in particular — is stated so that these are
the only cost facts it uses. -/

/-- The source's `minus_0`. -/
@[simp] theorem minus_0 (y : ECost) : minusECost y 0 = y := by
  ext k
  rw [toFun_minusECost]
  simp

/-- The source's `I_0`. -/
@[simp] theorem I_0 (cr : ECost) : leCostECost 0 cr := by intro x; simp

/-- The source's `minus_minus_add`: sequential consumption is
additive — the associativity that `wp_seq`'s balance threading needs. -/
theorem minus_minus_add (a : ECost) (b c : Cost) :
    minusECost (minusECost a b) c = minusECost a (b + c) := by
  ext k
  rw [toFun_minusECost, toFun_minusECost, toFun_minusECost, ACost.toFun_add]
  exact enat_resSub_resSub _ _ _

/-- The source's `I1`: affordability of a sum gives affordability of the
second summand against the reduced balance. -/
theorem I1 {a b : Cost} {c : ECost} (h : leCostECost (a + b) c) :
    leCostECost b (minusECost c a) := by
  intro x
  rw [toFun_minusECost]
  have hx := h x
  rw [ACost.toFun_add] at hx
  exact enat_coe_le_resSub hx

/-- The source's `I2`: …and of the first. -/
theorem I2 {a b : Cost} {c : ECost} (h : leCostECost (a + b) c) : leCostECost a c := by
  intro x
  refine le_trans ?_ (h x)
  rw [ACost.toFun_add, Nat.cast_add]
  exact le_self_add

/-- The source's `I3`: and the two re-assemble. -/
theorem I3 {a b : Cost} {c : ECost} (h1 : leCostECost a (minusECost c b))
    (h2 : leCostECost b c) : leCostECost (b + a) c := by
  intro x
  rw [ACost.toFun_add]
  have h1x := h1 x
  rw [toFun_minusECost] at h1x
  exact enat_add_le_of_le_resSub h1x (h2 x)

/-- The IR's interpretation of `cost_framework`: the source's
`interpretation cost_framework le_cost_ecost minus_ecost_cost`. -/
instance instCostFrameworkIr : CostFramework leCostECost minusECost where
  minus_0 := minus_0
  I_0 := I_0
  minus_minus_add := minus_minus_add
  I1 := I1
  I2 := I2
  I3 := I3

/-- The three obligations that carry sequential composition, packaged as
the one iff `wp_seq` needs: paying `κ₁` and then `κ₂` is paying
`κ₁ + κ₂`. -/
theorem afford_add_iff {κ₁ κ₂ : Cost} {cr : ECost} :
    leCostECost (κ₁ + κ₂) cr ↔
      leCostECost κ₁ cr ∧ leCostECost κ₂ (minusECost cr κ₁) :=
  ⟨fun h => ⟨I2 h, I1 h⟩, fun h => I3 h.2 h.1⟩

/-! ### Paying an op's price out of a credit assertion

The bridge from `Assn.lean`'s `¤¤` to affordability: `costCredits_split`
is what every triple in `Triples.lean` opens with. -/

@[simp] theorem leCostECost_cash_add (κ : Cost) (c : ECost) : leCostECost κ (cash κ + c) := by
  intro x
  rw [ACost.toFun_add, toFun_liftACost]
  exact le_self_add

@[simp] theorem minusECost_cash_add (κ : Cost) (c : ECost) : minusECost (cash κ + c) κ = c := by
  ext k
  rw [toFun_minusECost, ACost.toFun_add, toFun_liftACost]
  exact enat_coe_add_resSub _ _

/-- One unit of one currency, as the source's `$$` writes it. -/
@[simp] theorem cash_cost (n : String) (k : ℕ) : cash (ACost.cost n k) = ACost.cost n (k : ℕ∞) :=
  liftACost_cost n k

/-- Opening a triple: an assertion that owns `¤¤n k` pays for an op
priced at `ACost.cost n k`, and what is left is the frame at the reduced
balance. -/
theorem costCredits_split {n : String} {k : ℕ} {F : Assn} {s : State} {cr : ECost}
    (h : irSTATE (¤¤n k ∗ F) (s, cr)) :
    leCostECost (ACost.cost n k) cr ∧ irSTATE F (s, minusECost cr (ACost.cost n k)) := by
  rw [costCredits_def, ← cash_cost] at h
  obtain ⟨cr₂, rfl, hF⟩ := credits_split h
  exact ⟨leCostECost_cash_add _ _, by rw [minusECost_cash_add]; exact hF⟩

/-! ## 3. `Ir.wp`

The source's `wp` at the IR: its `wp_alt` reading
("the program succeeds with result `r`, concrete cost `c`, new state
`s'`; `c` must be affordable against the balance `cr`; the postcondition
holds of the new state paired with the balance after deduction") with
`run m s = SUCC r c s'` replaced by `BigStep c s s' κ` — the deep
semantics of `Semantics.lean` in place of the shallow monad's `run`
(ledger D2). -/

/-- The IR's weakest precondition, over the `(state, balance)` pair. -/
def wp (c : Com) (Q : Unit → State × ECost → Prop) : State × ECost → Prop :=
  fun p => ∃ s' κ, BigStep c p.1 s' κ ∧ Q () (s', minusECost p.2 κ) ∧ leCostECost κ p.2

theorem wp_def (c : Com) (Q : Unit → State × ECost → Prop) (s : State) (cr : ECost) :
    wp c Q (s, cr) ↔
      ∃ s' κ, BigStep c s s' κ ∧ Q () (s', minusECost cr κ) ∧ leCostECost κ cr := Iff.rfl

/-- The source's `wp_comm_inf`, from `BigStep.unique`: the IR is
deterministic, so a `wp` fact is about *the* run, and two postconditions
of the same run intersect. This one lemma is what `frame_rule`,
`cons_rule` and `htriple_to_gc` cost the IR. -/
theorem wp_comm_inf_ir (c : Com) (Q Q' : Unit → State × ECost → Prop) :
    wp c Q ⊓ wp c Q' = wp c (Q ⊓ Q') := by
  funext p
  refine propext ⟨?_, ?_⟩
  · rintro ⟨⟨s₁, κ₁, h₁, hq₁, hi₁⟩, ⟨s₂, κ₂, h₂, hq₂, hi₂⟩⟩
    obtain ⟨rfl, rfl⟩ := h₁.unique h₂
    exact ⟨s₁, κ₁, h₁, ⟨hq₁, hq₂⟩, hi₁⟩
  · rintro ⟨s', κ, h, hq, hi⟩
    exact ⟨⟨s', κ, h, hq.1, hi⟩, ⟨s', κ, h, hq.2, hi⟩⟩

instance instWpCommInfIr : WpCommInf wp := ⟨wp_comm_inf_ir⟩

/-- Monotonicity of the IR's `wp`, inherited from the generic layer. -/
theorem wp_mono_ir {c : Com} {Q Q' : Unit → State × ECost → Prop}
    (hQ : ∀ r p, Q r p → Q' r p) {p : State × ECost} (h : wp c Q p) : wp c Q' p :=
  wp_mono hQ h

/-! ### The wp equation suite

One equation per constructor. Each primitive reads
`I κ cr ∧ Q () (effect, minus cr κ)` — the source's `wp_consume` glued
to the op's effect (judgment call D-r). -/

@[simp] theorem wp_skip (Q : Unit → State × ECost → Prop) (s : State) (cr : ECost) :
    wp .skip Q (s, cr) ↔
      leCostECost (ACost.cost Currency.skip 1) cr ∧
        Q () (s, minusECost cr (ACost.cost Currency.skip 1)) := by
  rw [wp_def]
  constructor
  · rintro ⟨s', κ, h, hq, hi⟩
    rw [bigStep_skip_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, hq⟩
  · rintro ⟨hi, hq⟩
    exact ⟨s, _, .skip, hq, hi⟩

@[simp] theorem wp_const (x : String) (n : Val) (Q : Unit → State × ECost → Prop) (s : State)
    (cr : ECost) :
    wp (.const x n) Q (s, cr) ↔
      s.vars x ≠ none ∧ leCostECost (ACost.cost Currency.const 1) cr ∧
        Q () (s.setVar x n, minusECost cr (ACost.cost Currency.const 1)) := by
  rw [wp_def]
  constructor
  · rintro ⟨s', κ, h, hq, hi⟩
    rw [bigStep_const_iff] at h
    obtain ⟨hx, rfl, rfl⟩ := h
    exact ⟨hx, hi, hq⟩
  · rintro ⟨hx, hi, hq⟩
    exact ⟨_, _, .const hx, hq, hi⟩

@[simp] theorem wp_copy (x y : String) (Q : Unit → State × ECost → Prop) (s : State)
    (cr : ECost) :
    wp (.copy x y) Q (s, cr) ↔
      s.vars x ≠ none ∧ ∃ v, s.vars y = some v ∧
        leCostECost (ACost.cost Currency.copy 1) cr ∧
        Q () (s.setVar x v, minusECost cr (ACost.cost Currency.copy 1)) := by
  rw [wp_def]
  constructor
  · rintro ⟨s', κ, h, hq, hi⟩
    rw [bigStep_copy_iff] at h
    obtain ⟨hx, v, hy, rfl, rfl⟩ := h
    exact ⟨hx, v, hy, hi, hq⟩
  · rintro ⟨hx, v, hy, hi, hq⟩
    exact ⟨_, _, .copy hx hy, hq, hi⟩

@[simp] theorem wp_binop (op : Imp.Bop) (x y z : String) (Q : Unit → State × ECost → Prop)
    (s : State) (cr : ECost) :
    wp (.binop op x y z) Q (s, cr) ↔
      s.vars x ≠ none ∧ ∃ m n, s.vars y = some m ∧ s.vars z = some n ∧
        leCostECost (ACost.cost (binopCurrency op) 1) cr ∧
        Q () (s.setVar x (op.apply m n), minusECost cr (ACost.cost (binopCurrency op) 1)) := by
  rw [wp_def]
  constructor
  · rintro ⟨s', κ, h, hq, hi⟩
    rw [bigStep_binop_iff] at h
    obtain ⟨hx, m, n, hy, hz, rfl, rfl⟩ := h
    exact ⟨hx, m, n, hy, hz, hi, hq⟩
  · rintro ⟨hx, m, n, hy, hz, hi, hq⟩
    exact ⟨_, _, .binop hx hy hz, hq, hi⟩

@[simp] theorem wp_aget (x a i : String) (Q : Unit → State × ECost → Prop) (s : State)
    (cr : ECost) :
    wp (.aget x a i) Q (s, cr) ↔
      s.vars x ≠ none ∧ ∃ k xs v, s.vars i = some k ∧ s.arrs a = some xs ∧ xs[k]? = some v ∧
        leCostECost (ACost.cost Currency.aget 1) cr ∧
        Q () (s.setVar x v, minusECost cr (ACost.cost Currency.aget 1)) := by
  rw [wp_def]
  constructor
  · rintro ⟨s', κ, h, hq, hi⟩
    rw [bigStep_aget_iff] at h
    obtain ⟨hx, k, xs, v, hi', ha, hv, rfl, rfl⟩ := h
    exact ⟨hx, k, xs, v, hi', ha, hv, hi, hq⟩
  · rintro ⟨hx, k, xs, v, hi', ha, hv, hi, hq⟩
    exact ⟨_, _, .aget hx hi' ha hv, hq, hi⟩

@[simp] theorem wp_aset (a i v : String) (Q : Unit → State × ECost → Prop) (s : State)
    (cr : ECost) :
    wp (.aset a i v) Q (s, cr) ↔
      (∃ k n xs, s.vars i = some k ∧ s.vars v = some n ∧ s.arrs a = some xs ∧ k < xs.length ∧
        leCostECost (ACost.cost Currency.aset 1) cr ∧
        Q () (s.setArr a (xs.set k n), minusECost cr (ACost.cost Currency.aset 1))) := by
  rw [wp_def]
  constructor
  · rintro ⟨s', κ, h, hq, hi⟩
    rw [bigStep_aset_iff] at h
    obtain ⟨k, n, xs, hi', hv, ha, hk, rfl, rfl⟩ := h
    exact ⟨k, n, xs, hi', hv, ha, hk, hi, hq⟩
  · rintro ⟨k, n, xs, hi', hv, ha, hk, hi, hq⟩
    exact ⟨_, _, .aset hi' hv ha hk, hq, hi⟩

/-- The source's `wp_bind`, at `seq` (judgment call D-r). Its proof is
the four `cost_framework` obligations and nothing else. -/
theorem wp_seq (c d : Com) (Q : Unit → State × ECost → Prop) (p : State × ECost) :
    wp (.seq c d) Q p ↔ wp c (fun _ => wp d Q) p := by
  obtain ⟨s, cr⟩ := p
  rw [wp_def]
  constructor
  · rintro ⟨s'', κ, h, hq, hi⟩
    rw [bigStep_seq_iff] at h
    obtain ⟨s', κ₁, κ₂, hc, hd, rfl⟩ := h
    obtain ⟨hi₁, hi₂⟩ := afford_add_iff.1 hi
    refine ⟨s', κ₁, hc, ⟨s'', κ₂, hd, ?_, hi₂⟩, hi₁⟩
    rwa [minus_minus_add]
  · rintro ⟨s', κ₁, hc, ⟨s'', κ₂, hd, hq, hi₂⟩, hi₁⟩
    refine ⟨s'', κ₁ + κ₂, .seq hc hd, ?_, afford_add_iff.2 ⟨hi₁, hi₂⟩⟩
    rwa [← minus_minus_add]

/-- The source's `llc_if_simp`: charge the test, then run the branch. -/
theorem wp_ite (b : Cond) (c d : Com) (Q : Unit → State × ECost → Prop) (s : State)
    (cr : ECost) :
    wp (.ite b c d) Q (s, cr) ↔
      ∃ t, b.eval s = some t ∧ leCostECost (ACost.cost Currency.ite 1) cr ∧
        wp (if t then c else d) Q (s, minusECost cr (ACost.cost Currency.ite 1)) := by
  rw [wp_def]
  constructor
  · rintro ⟨s', κ, h, hq, hi⟩
    rw [bigStep_ite_iff] at h
    obtain ⟨t, κ', hb, hbr, rfl⟩ := h
    obtain ⟨hi₁, hi₂⟩ := afford_add_iff.1 hi
    refine ⟨t, hb, hi₁, s', κ', hbr, ?_, hi₂⟩
    rwa [minus_minus_add]
  · rintro ⟨t, hb, hi₁, s', κ', hbr, hq, hi₂⟩
    refine ⟨s', ACost.cost Currency.ite 1 + κ', bigStep_ite_iff.2 ⟨t, κ', hb, hbr, rfl⟩, ?_,
      afford_add_iff.2 ⟨hi₁, hi₂⟩⟩
    rwa [← minus_minus_add]

/-- The source's `llc_while_unfold`: one guard credit per test, then
either body-and-again or stop (judgment call D-h of `Semantics.lean`).
Not a `simp` lemma — its right-hand side mentions the same loop. -/
theorem wp_while_unfold (b : Cond) (c : Com) (Q : Unit → State × ECost → Prop) (s : State)
    (cr : ECost) :
    wp (.while b c) Q (s, cr) ↔
      ∃ t, b.eval s = some t ∧ leCostECost (ACost.cost Currency.«while» 1) cr ∧
        (if t then wp c (fun _ => wp (.while b c) Q)
              (s, minusECost cr (ACost.cost Currency.«while» 1))
         else Q () (s, minusECost cr (ACost.cost Currency.«while» 1))) := by
  rw [wp_def]
  constructor
  · rintro ⟨s'', κ, h, hq, hi⟩
    rw [bigStep_while_iff] at h
    rcases h with ⟨hb, s', κ₁, κ₂, hc, hw, rfl⟩ | ⟨hb, rfl, rfl⟩
    · have hi' : leCostECost (ACost.cost Currency.«while» 1 + (κ₁ + κ₂)) cr := by
        rwa [add_assoc] at hi
      obtain ⟨hiw, hirest⟩ := afford_add_iff.1 hi'
      obtain ⟨hi₁, hi₂⟩ := afford_add_iff.1 hirest
      refine ⟨true, hb, hiw, ?_⟩
      simp only [if_true]
      refine ⟨s', κ₁, hc, ⟨s'', κ₂, hw, ?_, ?_⟩, hi₁⟩
      · rw [minus_minus_add, minus_minus_add, ← add_assoc]
        exact hq
      · simpa only [minus_minus_add] using hi₂
    · exact ⟨false, hb, hi, by simpa using hq⟩
  · rintro ⟨t, hb, hiw, hrest⟩
    cases t
    · simp only [Bool.false_eq_true, if_false] at hrest
      exact ⟨s, _, .while_false hb, hrest, hiw⟩
    · simp only [if_true] at hrest
      obtain ⟨s', κ₁, hc, ⟨s'', κ₂, hw, hq, hi₂⟩, hi₁⟩ := hrest
      refine ⟨s'', ACost.cost Currency.«while» 1 + κ₁ + κ₂, .while_true hb hc hw, ?_, ?_⟩
      · rw [add_assoc, ← minus_minus_add, ← minus_minus_add]
        exact hq
      · rw [add_assoc]
        exact afford_add_iff.2 ⟨hiw, afford_add_iff.2 ⟨hi₁, hi₂⟩⟩

/-! ### The well-founded loop rule, at `wp`

The reasoning principle `llc_while_annot_rule` is built from: an
invariant indexed by a measure, a well-founded relation on the measure,
one guard credit per test, and a body that re-establishes the invariant
at a smaller measure. The separation-logic form lives in `Triples.lean`
(judgment call D-s). -/

theorem wp_while_wf {τ : Type} {r : τ → τ → Prop} (hwf : WellFounded r)
    {J : τ → State × ECost → Prop} {Q : Unit → State × ECost → Prop} {b : Cond} {c : Com}
    (hstep : ∀ (t : τ) (s : State) (cr : ECost), J t (s, cr) →
      leCostECost (ACost.cost Currency.«while» 1) cr ∧
      ∃ tv, b.eval s = some tv ∧
        (tv = true → wp c (fun _ q => ∃ t', r t' t ∧ J t' q)
            (s, minusECost cr (ACost.cost Currency.«while» 1))) ∧
        (tv = false → Q () (s, minusECost cr (ACost.cost Currency.«while» 1))))
    {t₀ : τ} {p : State × ECost} (hJ : J t₀ p) : wp (.while b c) Q p := by
  induction t₀ using hwf.induction generalizing p with
  | _ t ih =>
    obtain ⟨s, cr⟩ := p
    obtain ⟨hiw, tv, hb, htrue, hfalse⟩ := hstep t s cr hJ
    rw [wp_while_unfold]
    refine ⟨tv, hb, hiw, ?_⟩
    cases tv
    · simpa using hfalse rfl
    · simp only [if_true]
      refine wp_mono_ir (fun _ q hq => ?_) (htrue rfl)
      obtain ⟨t', hrt, hJ'⟩ := hq
      exact ih t' hrt hJ'

end Lax13Proofs.Refine.Ir
