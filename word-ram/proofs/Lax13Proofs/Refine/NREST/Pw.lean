import Lax13Proofs.Refine.NREST.Basic

/-!
Pointwise reasoning about `NRest`, and the monad laws.

Port of the pointwise-reasoning part of `thys/nrest/NREST.thy` and
`NREST_Misc.thy` of `isabelle_llvm_time` @ 42dd7f5 (pin: design record
§1), together with the four monad-law statements of `NREST.thy`. The
source shapes:

```isabelle
definition "nofailT S ≡ S ≠ FAILT"
definition "inresT S x t ≡ REST [x ↦ lift t] ≤ S"
lemma nres_bind_left_identity:
  fixes f :: "'a ⇒ ('b,'c::{complete_lattice,zero,monoid_add}) nrest"
  shows "bindT (RETURNT x) f = f x"
lemma nres_bind_right_identity:  fixes M :: "('b,enat) nrest"
  shows "bindT M RETURNT = M"
lemma nres_bind_assoc:           fixes M :: "('a,enat) nrest"
  shows "bindT (bindT M (λx. f x)) g = bindT M (λx. bindT (f x) g)"
lemma nres_acost_bind_assoc:     fixes M :: "('a,(_,enat) acost) nrest"  (same statement)
```

## What is stated where, and why

The *granularity is the source's*, deliberately. The left identity is
generic (it only needs `0 + t = t`); the right identity and
associativity are stated by the source monomorphically at `enat` and at
`(_, enat) acost`, because their proofs need adding a fixed cost to
commute with suprema — a property a bare `complete_lattice` +
`monoid_add` does not have. So the public theorems below are exactly the
source's four statements at exactly the source's carriers, and the
shared machinery sits underneath them in auxiliary lemmas that take that
continuity as an explicit hypothesis (`AddSupContinuousB`), discharged
once for `ℕ∞` and once for `ACost κ ℕ∞`. Nothing is generalised past the
source at the level of the public API; the hypothesis-carrying auxiliary
is how the two carriers avoid duplicating the whole proof.

`inresT` is here the *same-carrier* instance of the source's definition:
the source writes `REST [x ↦ lift t] ≤ S`, where `lift : enat ⇒ 'c`
crosses currencies. The currency-crossing version arrives with
`TimeRefinement.lean` (design record §3, `Time_Refinement.thy` row);
until then `lift` is the identity and the definition below is the
source's, read at one carrier.

Local fills for gaps in mathlib (candidates for upstreaming, all proved
here): `withBot_map_add` (`WithBot.map (t + ·) = (↑t + ·)`),
`withBot_eq_bot_or_coe`, and the `WithBot`-level continuity transfer
`addSupContinuousB_of`. `ENat.add_sSup` exists upstream and is what the
`ℕ∞` discharge rests on.
-/

namespace Lax13Proofs.Refine

variable {α β δ γ κ : Type}

/-! ### Two `WithBot` facts mathlib does not have -/

/-- Every element of `WithBot γ` is `⊥` or a cost. -/
theorem withBot_eq_bot_or_coe (u : WithBot γ) : u = ⊥ ∨ ∃ t : γ, u = (t : WithBot γ) := by
  induction u using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe t => exact Or.inr ⟨t, rfl⟩

/-- The source charges a cost by `map_option ((+) t)`; on `WithBot` that
is left addition by the coercion, which is the form every lattice
argument below wants. -/
@[simp] theorem withBot_map_add [AddMonoid γ] (t : γ) (u : WithBot γ) :
    WithBot.map (t + ·) u = (t : WithBot γ) + u := by
  induction u using WithBot.recBotCoe with
  | bot => simp
  | coe a => simp [← WithBot.coe_add]

namespace NRest

/-! ### `nofailT` and `inresT` -/

/-- The source's `nofailT S ≡ S ≠ FAILT`. -/
def nofailT [CompleteLattice γ] (S : NRest α γ) : Prop := S ≠ ⊤

theorem nofailT_iff [CompleteLattice γ] {S : NRest α γ} : nofailT S ↔ S ≠ fail := Iff.rfl

@[simp] theorem not_nofailT_fail [CompleteLattice γ] : ¬ nofailT (fail : NRest α γ) :=
  fun h => h rfl

@[simp] theorem nofailT_rest [CompleteLattice γ] (X : α → WithBot γ) : nofailT (rest X) :=
  rest_ne_fail X

@[simp] theorem nofailT_returnT [CompleteLattice γ] [Zero γ] (x : α) :
    nofailT (returnT x : NRest α γ) := rest_ne_fail _

@[simp] theorem nofailT_spec [CompleteLattice γ] (P : α → Prop) (t : α → γ) :
    nofailT (spec P t) := rest_ne_fail _

/-- The source's `inresT S x t ≡ REST [x ↦ lift t] ≤ S`, read at one
carrier (`lift = id`); see the module header. -/
def inresT [CompleteLattice γ] (S : NRest α γ) (x : α) (t : γ) : Prop :=
  rest (single x (t : WithBot γ)) ≤ S

@[simp] theorem inresT_fail [CompleteLattice γ] (x : α) (t : γ) :
    inresT (fail : NRest α γ) x t := le_fail _

@[simp] theorem inresT_rest [CompleteLattice γ] (X : α → WithBot γ) (x : α) (t : γ) :
    inresT (rest X) x t ↔ (t : WithBot γ) ≤ X x := by
  rw [inresT, rest_le_rest_iff, single_le_iff]

/-! ### The pointwise principles

`pw_le_iff` and `pw_eq_iff` of the source. They hold at every complete
lattice: `≤` between result maps is decided by which `single`s sit below
them, because `WithBot` has no elements other than `⊥` and coercions. -/

/-- The source's `pw_le_iff`. -/
theorem pw_le_iff [CompleteLattice γ] {S S' : NRest α γ} :
    S ≤ S' ↔ (nofailT S' → nofailT S ∧ ∀ x t, inresT S x t → inresT S' x t) := by
  constructor
  · intro h hS'
    refine ⟨fun hfail => hS' (le_antisymm (le_fail _) (hfail ▸ h)), fun x t hx => hx.trans h⟩
  · intro h
    cases S' with
    | fail => exact le_fail _
    | rest X' =>
      have ⟨hS, hin⟩ := h (nofailT_rest X')
      cases S with
      | fail => exact absurd rfl hS
      | rest X =>
        refine rest_le_rest_iff.mpr fun x => ?_
        rcases withBot_eq_bot_or_coe (X x) with hx | ⟨t, hx⟩
        · simp [hx]
        · have := (inresT_rest X' x t).mp (hin x t ((inresT_rest X x t).mpr (by rw [hx])))
          rwa [hx]

/-- The source's `pw_eq_iff`. -/
theorem pw_eq_iff [CompleteLattice γ] {S S' : NRest α γ} :
    S = S' ↔ ((nofailT S ↔ nofailT S') ∧ ∀ x t, inresT S x t ↔ inresT S' x t) := by
  constructor
  · rintro rfl; exact ⟨Iff.rfl, fun _ _ => Iff.rfl⟩
  · rintro ⟨hn, hi⟩
    exact le_antisymm (pw_le_iff.mpr fun h => ⟨hn.mpr h, fun x t => (hi x t).mp⟩)
      (pw_le_iff.mpr fun h => ⟨hn.mp h, fun x t => (hi x t).mpr⟩)

/-! ### The result map of a non-failing computation -/

/-- The result map of `m`, with the unused value `⊥` at `fail`. It lets
"all of these are `rest`s" be used without choice. -/
def resultsOf : NRest α γ → α → WithBot γ
  | .fail => ⊥
  | .rest X => X

@[simp] theorem resultsOf_fail : resultsOf (fail : NRest α γ) = ⊥ := rfl

@[simp] theorem resultsOf_rest (X : α → WithBot γ) : resultsOf (rest X) = X := rfl

theorem eq_rest_resultsOf {m : NRest α γ} (h : m ≠ fail) : m = rest (resultsOf m) := by
  cases m with
  | fail => exact absurd rfl h
  | rest X => rfl

/-! ### `consume`, and `consume` at a possibly-absent cost -/

/-- The source's `consume` in the form every lattice argument below
wants: left addition of the charged cost. -/
theorem consume_rest' [AddMonoid γ] (Y : α → WithBot γ) (t : γ) :
    consume (rest Y) t = rest (fun x => (t : WithBot γ) + Y x) := by
  simp [consume, withBot_map_add]

/-- `consume` at a cost that may be absent: charging `⊥` offers nothing
at all. This is the shape the results of a `bindT` take, one per
possible result of the bound computation. -/
noncomputable def consumeB [CompleteLattice γ] [Add γ] (m : NRest α γ) (u : WithBot γ) :
    NRest α γ :=
  u.recBotCoe ⊥ (fun t => consume m t)

@[simp] theorem consumeB_bot [CompleteLattice γ] [Add γ] (m : NRest α γ) :
    consumeB m ⊥ = ⊥ := rfl

@[simp] theorem consumeB_coe [CompleteLattice γ] [Add γ] (m : NRest α γ) (t : γ) :
    consumeB m (t : WithBot γ) = consume m t := rfl

@[simp] theorem consumeB_zero [CompleteLattice γ] [AddMonoid γ] (m : NRest α γ) :
    consumeB m (0 : WithBot γ) = consume m 0 := rfl

/-- `consumeB` on a `rest` is uniform in the charged cost: `⊥` propagates
through the addition on its own. -/
theorem consumeB_rest [CompleteLattice γ] [AddMonoid γ] (Y : α → WithBot γ) (u : WithBot γ) :
    consumeB (rest Y) u = rest (fun x => u + Y x) := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · rw [consumeB_bot, bot_eq_rest_bot, rest_inj_iff]
    funext x
    simp
  · rw [consumeB_coe, consume_rest']

theorem consumeB_fail_of_ne_bot [CompleteLattice γ] [Add γ] {u : WithBot γ} (h : u ≠ ⊥) :
    consumeB (fail : NRest α γ) u = fail := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · exact absurd rfl h
  · simp

@[simp] theorem consume_bot [CompleteLattice γ] [AddMonoid γ] (t : γ) :
    consume (⊥ : NRest α γ) t = ⊥ := by
  rw [bot_eq_rest_bot, consume_rest', rest_inj_iff]
  funext x
  simp

/-- The source's `consume M 0 = M`. -/
@[simp] theorem consume_zero [CompleteLattice γ] [AddMonoid γ] (m : NRest α γ) :
    consume m 0 = m := by
  cases m with
  | fail => rfl
  | rest X => rw [consume_rest']; simp

/-- Charging twice is charging once, and the source's left-addition
convention is what makes the costs associate in this order. -/
theorem consume_consume [CompleteLattice γ] [AddMonoid γ] (m : NRest α γ) (t t' : γ) :
    consume (consume m t') t = consume m (t + t') := by
  cases m with
  | fail => rfl
  | rest X =>
    simp only [consume_rest']
    congr 1
    funext x
    rw [← add_assoc, ← WithBot.coe_add]

/-- The source's `consume_RETURNT`. -/
theorem consume_returnT [CompleteLattice γ] [AddMonoid γ] (x : α) (T : γ) :
    consume (returnT x) T = rest (single x (T : WithBot γ)) := by
  rw [returnT, consume_rest']
  congr 1
  funext v
  by_cases h : v = x
  · subst h; simp
  · simp [h]

theorem consumeB_returnT [CompleteLattice γ] [AddMonoid γ] (x : α) (u : WithBot γ) :
    consumeB (returnT x) u = rest (single x u) := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · simp [Pi.bot_def]
  · simp [consume_returnT]

/-! ### Monotonicity -/

/-- The source's `consume_mono`, in both arguments. -/
theorem consume_mono [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    {m m' : NRest α γ} {t t' : γ} (hm : m ≤ m') (ht : t ≤ t') :
    consume m t ≤ consume m' t' := by
  cases m' with
  | fail => simp
  | rest Y' =>
    cases m with
    | fail => simp at hm
    | rest Y =>
      rw [consume_rest', consume_rest', rest_le_rest_iff]
      exact fun x => add_le_add (WithBot.coe_le_coe.mpr ht) (hm x)

theorem consumeB_mono [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    {m m' : NRest α γ} {u u' : WithBot γ} (hm : m ≤ m') (hu : u ≤ u') :
    consumeB m u ≤ consumeB m' u' := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · rw [consumeB_bot]; exact bot_le
  · rcases withBot_eq_bot_or_coe u' with rfl | ⟨t', rfl⟩
    · simp at hu
    · exact consume_mono hm (WithBot.coe_le_coe.mp hu)

/-! ### `bindT` as a supremum over the results of the bound computation

The set comprehension of the source is a supremum indexed by the results
themselves, with `⊥` contributed by results the bound computation cannot
produce. Everything below reasons through this form. -/

theorem bindT_rest_eq_iSup [CompleteLattice γ] [AddMonoid γ] (X : α → WithBot γ)
    (f : α → NRest β γ) :
    bindT (rest X) f = ⨆ x, consumeB (f x) (X x) := by
  rw [bindT_rest]
  refine le_antisymm (sSup_le ?_) (iSup_le fun x => ?_)
  · rintro n ⟨x, t, hx, rfl⟩
    exact le_iSup_of_le x (by rw [hx, consumeB_coe])
  · rcases withBot_eq_bot_or_coe (X x) with hx | ⟨t, hx⟩
    · rw [hx, consumeB_bot]; exact bot_le
    · exact le_sSup ⟨x, t, hx, by rw [hx, consumeB_coe]⟩

@[simp] theorem bindT_bot [CompleteLattice γ] [AddMonoid γ] (f : α → NRest β γ) :
    bindT (⊥ : NRest α γ) f = ⊥ := by
  rw [bot_eq_rest_bot, bindT_rest_eq_iSup,
    iSup_congr (fun x : α => by rw [Pi.bot_apply, consumeB_bot] :
      ∀ x : α, consumeB (f x) ((⊥ : α → WithBot γ) x) = ⊥)]
  exact iSup_eq_bot.mpr fun _ => rfl

/-- A `consumeB` fails exactly when a real cost is charged to a failing
computation. -/
theorem consumeB_eq_fail_iff [CompleteLattice γ] [AddMonoid γ] {m : NRest α γ}
    {u : WithBot γ} : consumeB m u = fail ↔ u ≠ ⊥ ∧ m = fail := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · simp [rest_ne_fail]
  · cases m with
    | fail => simp
    | rest Y => simp [rest_ne_fail]

/-- The source's `pw_bindT_nofailT`: a bind fails exactly when the bound
computation fails, or some reachable result leads to a failure. -/
theorem pw_bindT_nofailT [CompleteLattice γ] [AddMonoid γ] {M : NRest α γ}
    {f : α → NRest β γ} :
    nofailT (bindT M f) ↔ (nofailT M ∧ ∀ x t, inresT M x t → nofailT (f x)) := by
  cases M with
  | fail => simp [nofailT_iff, bindT_fail]
  | rest X =>
    rw [nofailT_iff, bindT_rest_eq_iSup, ne_eq, iSup_eq_fail_iff]
    simp only [not_exists, consumeB_eq_fail_iff]
    constructor
    · refine fun h => ⟨nofailT_rest X, fun x t ht hfx => ?_⟩
      have hle := (inresT_rest X x t).mp ht
      refine h x ⟨fun hb => ?_, hfx⟩
      rw [hb] at hle
      simp at hle
    · rintro h x ⟨hne, hfail⟩
      rcases withBot_eq_bot_or_coe (X x) with hb | ⟨c, hc⟩
      · exact hne hb
      · exact nofailT_iff.mp (h.2 x c ((inresT_rest X x c).mpr (by rw [hc]))) hfail

/-- The source's `bindT_mono`. -/
theorem bindT_mono [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    {M M' : NRest α γ} {f f' : α → NRest β γ} (hM : M ≤ M') (hf : ∀ x, f x ≤ f' x) :
    bindT M f ≤ bindT M' f' := by
  cases M' with
  | fail => simp
  | rest X' =>
    cases M with
    | fail => simp at hM
    | rest X =>
      rw [bindT_rest_eq_iSup, bindT_rest_eq_iSup]
      exact iSup_mono fun x => consumeB_mono (hf x) (hM x)

/-! ### Continuity of addition, and what it buys

`bindT` is a supremum, so the monad laws need adding a cost to commute
with suprema. That is the property the source's monomorphic statements
of the right identity and of associativity are really about; it is
isolated here so that both carriers can discharge it once. -/

/-- Left addition on `WithBot γ` distributes over arbitrary suprema.
`⊥` makes this hold for the empty supremum too, which is why the
predicate is stated on `WithBot γ` rather than on `γ`. -/
def AddSupContinuousB (γ : Type) [CompleteLattice γ] [Add γ] : Prop :=
  ∀ (v : WithBot γ) (U : Set (WithBot γ)), v + sSup U = ⨆ u ∈ U, (v + u)

theorem AddSupContinuousB.add_iSup [CompleteLattice γ] [Add γ] (hc : AddSupContinuousB γ)
    {ι : Sort*} (v : WithBot γ) (g : ι → WithBot γ) : v + (⨆ i, g i) = ⨆ i, (v + g i) := by
  rw [iSup, hc v (Set.range g), iSup_range]

theorem AddSupContinuousB.iSup_add [CompleteLattice γ] [AddCommMonoid γ]
    (hc : AddSupContinuousB γ) {ι : Sort*} (g : ι → WithBot γ) (v : WithBot γ) :
    (⨆ i, g i) + v = ⨆ i, (g i + v) := by
  simp only [add_comm _ v]
  exact hc.add_iSup v g

/-- Transfer of continuity from `γ` to `WithBot γ`. The `γ`-level
statement only has to hold for *nonempty* sets — the empty case is
exactly where `WithBot`'s new bottom is needed, and it holds there for
free. -/
theorem addSupContinuousB_of (γ : Type) [CompleteLattice γ] [AddCommMonoid γ]
    [IsOrderedAddMonoid γ]
    (h : ∀ (t : γ) (S : Set γ), S.Nonempty → t + sSup S = ⨆ s ∈ S, (t + s)) :
    AddSupContinuousB γ := by
  rintro v U
  rcases withBot_eq_bot_or_coe v with rfl | ⟨t, rfl⟩
  · simp
  by_cases hU : ∃ a : γ, ((a : WithBot γ)) ∈ U
  · obtain ⟨a₀, ha₀⟩ := hU
    set V : Set γ := {a : γ | ((a : WithBot γ)) ∈ U} with hV
    have hVne : V.Nonempty := ⟨a₀, ha₀⟩
    refine le_antisymm ?_ (iSup₂_le fun u hu => add_le_add le_rfl (le_sSup hu))
    -- the supremum on the right is a coercion, because it dominates one
    set R : WithBot γ := ⨆ u ∈ U, ((t : WithBot γ) + u) with hR
    have hle : ((t + a₀ : γ) : WithBot γ) ≤ R := by
      refine le_iSup₂_of_le ((a₀ : WithBot γ)) ha₀ ?_
      rw [WithBot.coe_add]
    obtain hb | ⟨r, hr⟩ := withBot_eq_bot_or_coe R
    · rw [hb] at hle; simp at hle
    have hsup : sSup U ≤ ((sSup V : γ) : WithBot γ) := by
      refine sSup_le fun u hu => ?_
      rcases withBot_eq_bot_or_coe u with rfl | ⟨a, rfl⟩
      · exact bot_le
      · exact WithBot.coe_le_coe.mpr (le_sSup hu)
    calc (t : WithBot γ) + sSup U ≤ (t : WithBot γ) + ((sSup V : γ) : WithBot γ) :=
          add_le_add le_rfl hsup
      _ = ((t + sSup V : γ) : WithBot γ) := by rw [WithBot.coe_add]
      _ = ((⨆ a ∈ V, (t + a) : γ) : WithBot γ) := by rw [h t V hVne]
      _ ≤ R := by
          rw [hr, WithBot.coe_le_coe]
          refine iSup₂_le fun a ha => ?_
          have : ((t + a : γ) : WithBot γ) ≤ R := by
            refine le_iSup₂_of_le ((a : WithBot γ)) ha ?_
            rw [WithBot.coe_add]
          rw [hr] at this
          exact WithBot.coe_le_coe.mp this
  · simp only [not_exists] at hU
    have hbot : sSup U = ⊥ := by
      refine le_antisymm (sSup_le fun u hu => ?_) bot_le
      rcases withBot_eq_bot_or_coe u with rfl | ⟨a, rfl⟩
      · exact le_rfl
      · exact absurd hu (hU a)
    rw [hbot, WithBot.add_bot]
    refine le_antisymm bot_le (iSup₂_le fun u hu => ?_)
    rcases withBot_eq_bot_or_coe u with rfl | ⟨a, rfl⟩
    · simp
    · exact absurd hu (hU a)

/-- The carrier the source states the right identity and associativity
at: `ℕ∞`, the source's `enat`. -/
theorem addSupContinuousB_enat : AddSupContinuousB ℕ∞ :=
  addSupContinuousB_of ℕ∞ fun _ _ hS => ENat.add_sSup hS

/-- The second carrier the source states associativity at: costs over
`ℕ∞`. Everything is currency-by-currency, so this reduces to `ℕ∞`. -/
theorem addSupContinuousB_acost : AddSupContinuousB (ACost κ ℕ∞) := by
  refine addSupContinuousB_of _ fun t S hS => ?_
  ext k
  rw [ACost.toFun_add, ACost.toFun_sSup,
    show (⨆ a ∈ S, a.toFun k) = sSup ((fun a : ACost κ ℕ∞ => a.toFun k) '' S) from sSup_image.symm,
    ENat.add_sSup (hS.image _), iSup_image]
  simp

/-! ### Distribution laws for `consume` and `bindT` -/

theorem consume_iSup [CompleteLattice γ] [AddCommMonoid γ] (hc : AddSupContinuousB γ)
    {ι : Sort*} (m : ι → NRest α γ) (t : γ) :
    consume (⨆ i, m i) t = ⨆ i, consume (m i) t := by
  by_cases hf : ∃ i, m i = fail
  · obtain ⟨i, hi⟩ := hf
    have h1 : (⨆ i, m i) = fail := iSup_eq_fail_iff.mpr ⟨i, hi⟩
    have h2 : (⨆ i, consume (m i) t) = fail := iSup_eq_fail_iff.mpr ⟨i, by rw [hi]; rfl⟩
    rw [h1, h2]; rfl
  · simp only [not_exists] at hf
    have hrest : ∀ i, m i = rest (resultsOf (m i)) := fun i => eq_rest_resultsOf (hf i)
    have h1 : (⨆ i, m i) = rest (⨆ i, resultsOf (m i)) := by
      rw [show (⨆ i, m i) = ⨆ i, rest (resultsOf (m i)) from iSup_congr hrest, iSup_rest]
    rw [h1, consume_rest', show (⨆ i, consume (m i) t)
      = ⨆ i, rest (fun x => (t : WithBot γ) + resultsOf (m i) x) from
        iSup_congr fun i => by rw [hrest i, consume_rest', resultsOf_rest], iSup_rest]
    congr 1
    funext x
    rw [iSup_apply, hc.add_iSup, iSup_apply]

theorem consumeB_iSup_cost [CompleteLattice γ] [AddCommMonoid γ] (hc : AddSupContinuousB γ)
    {ι : Sort*} (m : NRest α γ) (u : ι → WithBot γ) :
    consumeB m (⨆ i, u i) = ⨆ i, consumeB m (u i) := by
  cases m with
  | rest Y =>
    rw [consumeB_rest, show (⨆ i, consumeB (rest Y) (u i))
      = ⨆ i, rest (fun x => u i + Y x) from iSup_congr fun i => consumeB_rest Y (u i), iSup_rest]
    congr 1
    funext x
    rw [hc.iSup_add, iSup_apply]
  | fail =>
    by_cases hb : ∀ i, u i = ⊥
    · have h1 : (⨆ i, u i) = ⊥ := iSup_eq_bot.mpr hb
      have h2 : ∀ i, consumeB (fail : NRest α γ) (u i) = ⊥ := fun i => by rw [hb i, consumeB_bot]
      rw [h1, consumeB_bot]
      exact ((iSup_congr h2).trans (iSup_eq_bot.mpr fun _ => rfl)).symm
    · simp only [not_forall] at hb
      obtain ⟨i, hi⟩ := hb
      have h1 : (⨆ i, u i) ≠ ⊥ := fun h => hi (le_bot_iff.mp (h ▸ le_iSup u i))
      rw [consumeB_fail_of_ne_bot h1]
      exact (iSup_eq_fail_iff.mpr ⟨i, consumeB_fail_of_ne_bot hi⟩).symm

theorem bindT_iSup [CompleteLattice γ] [AddCommMonoid γ] (hc : AddSupContinuousB γ)
    {ι : Sort*} (m : ι → NRest α γ) (f : α → NRest β γ) :
    bindT (⨆ i, m i) f = ⨆ i, bindT (m i) f := by
  by_cases hf : ∃ i, m i = fail
  · obtain ⟨i, hi⟩ := hf
    have h1 : (⨆ i, m i) = fail := iSup_eq_fail_iff.mpr ⟨i, hi⟩
    have h2 : (⨆ i, bindT (m i) f) = fail := iSup_eq_fail_iff.mpr ⟨i, by rw [hi]; rfl⟩
    rw [h1, h2]; rfl
  · simp only [not_exists] at hf
    have hrest : ∀ i, m i = rest (resultsOf (m i)) := fun i => eq_rest_resultsOf (hf i)
    have h1 : (⨆ i, m i) = rest (⨆ i, resultsOf (m i)) := by
      rw [show (⨆ i, m i) = ⨆ i, rest (resultsOf (m i)) from iSup_congr hrest, iSup_rest]
    rw [h1, bindT_rest_eq_iSup,
      show (⨆ i, bindT (m i) f) = ⨆ i, ⨆ x, consumeB (f x) (resultsOf (m i) x) from
        iSup_congr fun i => by rw [hrest i, bindT_rest_eq_iSup, resultsOf_rest],
      iSup_comm]
    exact iSup_congr fun x => by rw [iSup_apply, consumeB_iSup_cost hc]

/-- Charging a cost commutes with binding: the source's left-addition
convention is what makes the two sides charge in the same order. -/
theorem bindT_consume [CompleteLattice γ] [AddCommMonoid γ] (hc : AddSupContinuousB γ)
    (m : NRest α γ) (t : γ) (g : α → NRest β γ) :
    bindT (consume m t) g = consume (bindT m g) t := by
  cases m with
  | fail => rfl
  | rest Y =>
    rw [consume_rest', bindT_rest_eq_iSup, bindT_rest_eq_iSup, consume_iSup hc]
    refine iSup_congr fun x => ?_
    rcases withBot_eq_bot_or_coe (Y x) with h | ⟨s, h⟩
    · rw [h, WithBot.add_bot, consumeB_bot]
      exact (consume_bot t).symm
    · rw [h]
      rw [show ((t : WithBot γ) + (s : WithBot γ)) = ((t + s : γ) : WithBot γ) by
        rw [WithBot.coe_add]]
      rw [consumeB_coe, consumeB_coe, consume_consume]

theorem bindT_consumeB [CompleteLattice γ] [AddCommMonoid γ] (hc : AddSupContinuousB γ)
    (m : NRest α γ) (u : WithBot γ) (g : α → NRest β γ) :
    bindT (consumeB m u) g = consumeB (bindT m g) u := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · simp
  · rw [consumeB_coe, consumeB_coe, bindT_consume hc]

/-! ### The monad laws

The four statements of `NREST.thy`, at the source's own carriers. -/

/-- **Left identity**, the source's `nres_bind_left_identity`:
`bindT (RETURNT x) f = f x`, at any complete lattice with a monoid
addition — `0 + t = t` is all it needs. -/
@[simp] theorem returnT_bindT [CompleteLattice γ] [AddMonoid γ] (x : α) (f : α → NRest β γ) :
    bindT (returnT x) f = f x := by
  rw [returnT, bindT_rest_eq_iSup]
  refine le_antisymm (iSup_le fun e => ?_) (le_iSup_of_le x ?_)
  · by_cases h : e = x
    · subst h; simp
    · rw [single_of_ne h, consumeB_bot]; exact bot_le
  · simp

/-- **Right identity**, the source's `nres_bind_right_identity`, stated
where the source states it: `fixes M :: "('b,enat) nrest"`. -/
@[simp] theorem bindT_returnT (M : NRest α ℕ∞) : bindT M returnT = M := by
  cases M with
  | fail => rfl
  | rest X =>
    rw [bindT_rest_eq_iSup,
      show (⨆ x, consumeB (returnT x : NRest α ℕ∞) (X x)) = ⨆ x, rest (single x (X x)) from
        iSup_congr fun x => consumeB_returnT x (X x), iSup_rest]
    congr 1
    funext v
    rw [iSup_apply]
    refine le_antisymm (iSup_le fun x => ?_) (le_iSup_of_le v ?_)
    · by_cases h : v = x
      · subst h; simp
      · simp [h]
    · simp

/-- **Associativity**, the source's `nres_bind_assoc`, stated where the
source states it: `fixes M :: "('a,enat) nrest"`. -/
theorem bindT_assoc (M : NRest α ℕ∞) (f : α → NRest β ℕ∞)
    (g : β → NRest δ ℕ∞) :
    bindT (bindT M f) g = bindT M (fun x => bindT (f x) g) := by
  cases M with
  | fail => rfl
  | rest X =>
    rw [bindT_rest_eq_iSup, bindT_iSup addSupContinuousB_enat, bindT_rest_eq_iSup]
    exact iSup_congr fun x => bindT_consumeB addSupContinuousB_enat _ _ _

/-- **Associativity at the cost carrier**, the source's
`nres_acost_bind_assoc`, stated where the source states it:
`fixes M :: "('a,(_,enat) acost) nrest"`. -/
theorem bindT_assoc_acost (M : NRest α (ACost κ ℕ∞))
    (f : α → NRest β (ACost κ ℕ∞)) (g : β → NRest δ (ACost κ ℕ∞)) :
    bindT (bindT M f) g = bindT M (fun x => bindT (f x) g) := by
  cases M with
  | fail => rfl
  | rest X =>
    rw [bindT_rest_eq_iSup, bindT_iSup addSupContinuousB_acost, bindT_rest_eq_iSup]
    exact iSup_congr fun x => bindT_consumeB addSupContinuousB_acost _ _ _

end NRest

end Lax13Proofs.Refine
