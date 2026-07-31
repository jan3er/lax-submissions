import Lax13Proofs.Refine.NREST.TimeRefinement
import Lax13Proofs.Refine.Codegen.Cash

/-!
Currency flattening at the cash boundary.

The first half is a source-shaped port of Sepreftime's
`moreCurr/Flatten_Currencies.thy` at
`c1c987b45ec886d289ba215768182ac87b82f20d`: a computation costed in
`ACost Unit ℕ∞` is mapped structurally to a computation costed in `ℕ∞`.
Unlike a projection from a genuine multi-currency account, evaluation at
the sole `Unit` currency is an order isomorphism.  Consequently flattening
preserves arbitrary nondeterministic suprema and commutes with `bindT` on
the nose.

The second half fixes the one exchange rate used at code generation.  It
prices every IR currency in the sole unit currency, using exactly
`Codegen.weight`, and then flattens.  The resulting scalar is proved equal
to the existing `Codegen.ecash`; this is the single intended collapse of a
currency vector.
-/

namespace Lax13Proofs.Refine

namespace NRest

variable {α β γ : Type}

/-! ## Unit-currency costs -/

/-- Read the sole component of a unit-currency account. -/
def flatCost (c : ACost Unit ℕ∞) : ℕ∞ := c.toFun ()

@[simp] theorem flatCost_mk (f : Unit → ℕ∞) : flatCost ⟨f⟩ = f () := rfl
@[simp] theorem flatCost_zero : flatCost 0 = 0 := rfl
@[simp] theorem flatCost_add (a b : ACost Unit ℕ∞) :
    flatCost (a + b) = flatCost a + flatCost b := rfl
@[simp] theorem flatCost_cost (t : ℕ∞) : flatCost (ACost.cost () t) = t := by
  simp [flatCost]

/-- Evaluation at `()` is an order isomorphism: a `Unit`-indexed account
contains exactly one balance. -/
def flatCostIso : ACost Unit ℕ∞ ≃o ℕ∞ where
  toFun := flatCost
  invFun := fun t => ⟨fun _ => t⟩
  left_inv c := by
    ext u
    cases u
    rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro a b
    constructor
    · intro h u
      cases u
      exact h
    · intro h
      exact ACost.le_def.mp h ()

/-- The corresponding isomorphism on optional costs (`⊥` means that a
result is absent). -/
noncomputable def flatWithBotIso : WithBot (ACost Unit ℕ∞) ≃o WithBot ℕ∞ :=
  flatCostIso.withBotCongr

@[simp] theorem flatWithBotIso_apply (u : WithBot (ACost Unit ℕ∞)) :
    flatWithBotIso u = WithBot.map flatCost u := rfl

/-! ## Structural flattening -/

/-- Sepreftime's `flatCurrs`, specialized to the repository's cost
carrier. -/
def flatCurrs (m : NRest α (ACost Unit ℕ∞)) : NRest α ℕ∞ :=
  match m with
  | .fail => .fail
  | .rest M => .rest (fun x => WithBot.map flatCost (M x))

@[simp] theorem flatCurrs_fail :
    flatCurrs (fail : NRest α (ACost Unit ℕ∞)) = fail := rfl

@[simp] theorem flatCurrs_rest (M : α → WithBot (ACost Unit ℕ∞)) :
    flatCurrs (rest M) = rest (fun x => WithBot.map flatCost (M x)) := rfl

@[simp] theorem flatCurrs_eq_fail_iff {m : NRest α (ACost Unit ℕ∞)} :
    flatCurrs m = fail ↔ m = fail := by
  cases m <;> simp [flatCurrs, rest_ne_fail]

@[simp] theorem flatCurrs_returnT (x : α) :
    flatCurrs (returnT x : NRest α (ACost Unit ℕ∞)) = returnT x := by
  rw [returnT, flatCurrs_rest, returnT, rest_inj_iff]
  funext y
  by_cases h : y = x
  · subst h
    simp
  · simp [single_of_ne h]

@[simp] theorem flatCurrs_spec (P : α → Prop) (t : α → ACost Unit ℕ∞) :
    flatCurrs (spec P t) = spec P (fun x => flatCost (t x)) := by
  classical
  simp only [spec, flatCurrs_rest, rest_inj_iff]
  funext x
  by_cases hx : P x <;> simp [hx]

theorem flatCurrs_ite (p : Prop) [Decidable p]
    (m n : NRest α (ACost Unit ℕ∞)) :
    flatCurrs (if p then m else n) = if p then flatCurrs m else flatCurrs n := by
  split <;> rfl

theorem flatCurrs_ite_le (p : Prop) [Decidable p]
    {m n : NRest α (ACost Unit ℕ∞)} {m' n' : NRest α ℕ∞}
    (hm : p → flatCurrs m ≤ m') (hn : ¬ p → flatCurrs n ≤ n') :
    flatCurrs (if p then m else n) ≤ if p then m' else n' := by
  split
  · exact hm (by assumption)
  · exact hn (by assumption)

theorem flatCurrs_ite_ge (p : Prop) [Decidable p]
    {m n : NRest α (ACost Unit ℕ∞)} {m' n' : NRest α ℕ∞}
    (hm : p → m' ≤ flatCurrs m) (hn : ¬ p → n' ≤ flatCurrs n) :
    (if p then m' else n') ≤ flatCurrs (if p then m else n) := by
  split
  · exact hm (by assumption)
  · exact hn (by assumption)

/-- Flattening commutes with destructing a product. -/
@[simp] theorem flatCurrs_caseProd (c : α → β → NRest γ (ACost Unit ℕ∞))
    (p : α × β) :
    flatCurrs (Prod.rec c p) = Prod.rec (fun a b => flatCurrs (c a b)) p := by
  cases p
  rfl

/-- The source's `flatCurrs_prod`, allowing the mapped product branches
to be named independently. -/
theorem flatCurrs_prod {c : α → β → NRest γ (ACost Unit ℕ∞)}
    {c' : α → β → NRest γ ℕ∞} (p : α × β)
    (h : ∀ a b, flatCurrs (c a b) = c' a b) :
    flatCurrs (Prod.rec c p) = Prod.rec c' p := by
  cases p with
  | mk a b => exact h a b

@[simp] theorem flatCurrs_assert (P : Prop) :
    flatCurrs (assert P : NRest Unit (ACost Unit ℕ∞)) =
      (assert P : NRest Unit ℕ∞) := by
  classical
  by_cases h : P <;> simp [h]

@[simp] theorem flatCurrs_consume (m : NRest α (ACost Unit ℕ∞))
    (t : ACost Unit ℕ∞) :
    flatCurrs (consume m t) = consume (flatCurrs m) (flatCost t) := by
  cases m with
  | fail => rfl
  | rest M =>
      rw [consume_rest', flatCurrs_rest, flatCurrs_rest, consume_rest', rest_inj_iff]
      funext x
      rcases withBot_eq_bot_or_coe (M x) with h | ⟨u, h⟩
      · simp [h]
      · simp only [h, ← WithBot.coe_add, WithBot.map_coe, flatCost_add]

@[simp] theorem flatCurrs_consumeB (m : NRest α (ACost Unit ℕ∞))
    (u : WithBot (ACost Unit ℕ∞)) :
    flatCurrs (consumeB m u) = consumeB (flatCurrs m) (WithBot.map flatCost u) := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · rw [WithBot.map_bot]
    change flatCurrs (⊥ : NRest α (ACost Unit ℕ∞)) = (⊥ : NRest α ℕ∞)
    rw [bot_eq_rest_bot, flatCurrs_rest, bot_eq_rest_bot, rest_inj_iff]
    funext x
    rfl
  · rw [consumeB_coe, WithBot.map_coe, consumeB_coe, flatCurrs_consume]

/-- `flatCurrs` preserves arbitrary nondeterministic suprema.  This is
the source's continuity theorem, obtained here from the unit-currency
order isomorphism. -/
theorem flatCurrs_iSup {I : Sort*} (m : I → NRest α (ACost Unit ℕ∞)) :
    flatCurrs (⨆ i, m i) = ⨆ i, flatCurrs (m i) := by
  by_cases hf : ∃ i, m i = fail
  · obtain ⟨i, hi⟩ := hf
    have hleft : (⨆ i, m i) = fail := iSup_eq_fail_iff.mpr ⟨i, hi⟩
    have hright : (⨆ i, flatCurrs (m i)) = fail :=
      iSup_eq_fail_iff.mpr ⟨i, by rw [hi]; rfl⟩
    rw [hleft, hright]
    rfl
  · simp only [not_exists] at hf
    have hr : ∀ i, m i = rest (resultsOf (m i)) := fun i => eq_rest_resultsOf (hf i)
    rw [show (⨆ i, m i) = ⨆ i, rest (resultsOf (m i)) from iSup_congr hr,
      iSup_rest, flatCurrs_rest,
      show (⨆ i, flatCurrs (m i)) =
          ⨆ i, rest (fun x => WithBot.map flatCost (resultsOf (m i) x)) from
        iSup_congr fun i =>
          (congrArg flatCurrs (hr i)).trans (flatCurrs_rest (resultsOf (m i))),
      iSup_rest, rest_inj_iff]
    funext x
    rw [iSup_apply, iSup_apply]
    exact flatWithBotIso.map_iSup (fun i => resultsOf (m i) x)

/-- Sepreftime's central flattening law. -/
theorem flatCurrs_bindT (m : NRest α (ACost Unit ℕ∞))
    (f : α → NRest β (ACost Unit ℕ∞)) :
    flatCurrs (bindT m f) = bindT (flatCurrs m) (fun x => flatCurrs (f x)) := by
  cases m with
  | fail => rfl
  | rest X =>
      rw [bindT_rest_eq_iSup, flatCurrs_iSup, flatCurrs_rest, bindT_rest_eq_iSup]
      exact iSup_congr fun x => flatCurrs_consumeB (f x) (X x)

theorem flatCurrs_bindTI {m : NRest α (ACost Unit ℕ∞)} {m' : NRest α ℕ∞}
    {f : α → NRest β (ACost Unit ℕ∞)} {f' : α → NRest β ℕ∞}
    (hm : flatCurrs m = m') (hf : ∀ x, flatCurrs (f x) = f' x) :
    flatCurrs (bindT m f) = bindT m' f' := by
  rw [flatCurrs_bindT, hm]
  exact congrArg (bindT m') (funext hf)

/-- The source's monotonicity rule. -/
theorem flatCurrs_mono {m m' : NRest α (ACost Unit ℕ∞)} (h : m ≤ m') :
    flatCurrs m ≤ flatCurrs m' := by
  cases m' with
  | fail => exact le_top
  | rest Y =>
      cases m with
      | fail => simp at h
      | rest X =>
          exact rest_le_rest_iff.mpr fun x => flatWithBotIso.monotone (h x)

theorem flatCurrs_bindT_le {m : NRest α (ACost Unit ℕ∞)} {m' : NRest α ℕ∞}
    {f : α → NRest β (ACost Unit ℕ∞)} {f' : α → NRest β ℕ∞}
    (hm : flatCurrs m ≤ m') (hf : ∀ x, flatCurrs (f x) ≤ f' x) :
    flatCurrs (bindT m f) ≤ bindT m' f' := by
  rw [flatCurrs_bindT]
  exact bindT_mono hm hf

theorem flatCurrs_bindT_ge {m : NRest α (ACost Unit ℕ∞)} {m' : NRest α ℕ∞}
    {f : α → NRest β (ACost Unit ℕ∞)} {f' : α → NRest β ℕ∞}
    (hm : m' ≤ flatCurrs m) (hf : ∀ x, f' x ≤ flatCurrs (f x)) :
    bindT m' f' ≤ flatCurrs (bindT m f) := by
  rw [flatCurrs_bindT]
  exact bindT_mono hm hf

/-! ### Nondeterministic acceptance gate -/

/-- A two-result computation used to ensure the bind theorem is exercised
over a genuine supremum, rather than only through `returnT`. -/
noncomputable def flatNondet : NRest Bool (ACost Unit ℕ∞) :=
  spec (fun _ => True) (fun b => ACost.cost () (if b then 2 else 3))

theorem flatCurrs_nondet_bind_gate :
    flatCurrs (bindT flatNondet (fun b =>
      spec (fun n : ℕ => n = if b then 7 else 11) (fun _ => ACost.cost () 5))) =
      bindT (flatCurrs flatNondet) (fun b =>
        flatCurrs (spec (fun n : ℕ => n = if b then 7 else 11)
          (fun _ => ACost.cost () 5))) :=
  flatCurrs_bindT _ _

/-! ## The code-generation cash exchange -/

open Ir

/-- Buy one abstract IR currency in the sole cash currency.  The explicit
membership guard makes the finite support required by `timerefine`
visible; `Codegen.weight` is already zero outside this list. -/
def cashExchangeRate (k : String) : ACost Unit ℕ∞ :=
  if k ∈ Currency.all then ACost.cost () (Codegen.weight k : ℕ∞) else 0

theorem cashExchangeRate_wf : wfR'' cashExchangeRate := by
  intro u
  cases u
  refine Currency.all.toFinset.finite_toSet.subset fun k hk => ?_
  simp only [Finset.mem_coe, List.mem_toFinset]
  by_contra hmem
  simp [cashExchangeRate, hmem] at hk

@[simp] theorem flatCost_cashExchangeRate (k : String) :
    flatCost (cashExchangeRate k) =
      if k ∈ Currency.all then (Codegen.weight k : ℕ∞) else 0 := by
  by_cases h : k ∈ Currency.all <;> simp [cashExchangeRate, h]

/-- Reprice a currency vector into the one cash currency. -/
noncomputable def exchangeToCash (m : NRest α ECost) :
    NRest α (ACost Unit ℕ∞) :=
  timerefine cashExchangeRate m

/-- Exchange and then erase the now-trivial currency index. -/
noncomputable def collapseCash (m : NRest α ECost) : NRest α ℕ∞ :=
  flatCurrs (exchangeToCash m)

/-- The scalar obtained by the exchange is exactly the pre-existing
code-generation price of the account. -/
theorem flatCost_timerefineA_cashExchangeRate (c : ECost) :
    flatCost (timerefineA cashExchangeRate c) = Codegen.ecash c := by
  simp only [flatCost, toFun_timerefineA]
  have hsupp : Function.support
      (fun k => c.toFun k * (cashExchangeRate k).toFun ()) ⊆
      (Currency.all.toFinset : Set String) := by
    intro k hk
    simp only [Function.mem_support] at hk
    by_contra hmem
    have hmem' : k ∉ Currency.all := by simpa using hmem
    apply hk
    simp [cashExchangeRate, hmem']
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Codegen.ecash, List.sum_toFinset _ Currency.all_nodup]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  simp [cashExchangeRate, hk, mul_comm]

/-- **Collapse once, at cash.**  Exchanging `String → Unit` and then
flattening is exactly structural mapping by `Codegen.ecash`; no earlier
phase has discarded the currency vector. -/
theorem collapseCash_eq (m : NRest α ECost) :
    collapseCash m =
      match m with
      | .fail => .fail
      | .rest M => .rest (fun x => WithBot.map Codegen.ecash (M x)) := by
  cases m with
  | fail => rfl
  | rest M =>
      simp only [collapseCash, exchangeToCash, timerefine_rest, flatCurrs_rest,
        timerefineF_apply, rest.injEq]
      funext x
      rcases withBot_eq_bot_or_coe (M x) with h | ⟨c, h⟩
      · simp [h]
      · simp [h, flatCost_timerefineA_cashExchangeRate]

/-! ## Axiom guards -/

/-- info: 'Lax13Proofs.Refine.NRest.flatCurrs_bindT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatCurrs_bindT

/-- info: 'Lax13Proofs.Refine.NRest.flatCost_timerefineA_cashExchangeRate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms flatCost_timerefineA_cashExchangeRate

/-- info: 'Lax13Proofs.Refine.NRest.collapseCash_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms collapseCash_eq

end NRest

end Lax13Proofs.Refine
