import Lax13Proofs.Refine.Sepref.Signature

/-!
The source's signature-normalization and uniform-time side conditions from
`Sepref_Rules.thy` (pinned local copy `/tmp/src/ILT_Sepref_Rules.thy`).

`hr_comp_precise` is deliberately not a missing port: in the source it is
inside a nested comment immediately before `hr_comp_assoc` (lines 452--472)
and therefore declares no theorem or constraint rule.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## `hr_comp` normal forms -/

/-- Source `hr_comp_pure`, used by `hr_comp_the_pure`. -/
@[simp] theorem hr_comp_pure {α β κ : Type} (R : Set (κ × β)) (S : Set (β × α)) :
    hrComp (pureAssn R) S = pureAssn (relComp R S) := by
  funext a c hp
  apply propext
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hS, hR⟩ := sepConj_predLift_iff.1 hb
    exact ⟨⟨b, hR.1, hS⟩, hR.2⟩
  · rintro ⟨⟨b, hR, hS⟩, h0⟩
    exact ⟨b, sepConj_predLift_iff.2 ⟨hS, hR, h0⟩⟩

/-- Source `hr_comp_the_pure`. -/
theorem hr_comp_the_pure {α β κ : Type} {A : β → κ → Assn}
    (B : Set (β × α)) (hA : isPure A) :
    thePure (hrComp A B) = relComp (thePure A) B := by
  calc
    thePure (hrComp A B) = thePure (hrComp (pureAssn (thePure A)) B) :=
      congrArg (fun P => thePure (hrComp P B)) (pureAssn_thePure hA).symm
    _ = relComp (thePure A) B := by rw [hr_comp_pure, thePure_pureAssn]

/-- Source `hr_comp_assoc`. -/
theorem hr_comp_assoc {α β δ κ : Type} (R : β → κ → Assn)
    (S : Set (β × δ)) (T : Set (δ × α)) :
    hrComp (hrComp R S) T = hrComp R (relComp S T) := by
  funext a c hp
  apply propext
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨hT, hd⟩ := sepConj_predLift_iff.1 hd
    obtain ⟨b, hb⟩ := hd
    obtain ⟨hS, hR⟩ := sepConj_predLift_iff.1 hb
    exact ⟨b, sepConj_predLift_iff.2 ⟨⟨d, hS, hT⟩, hR⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨⟨d, hS, hT⟩, hR⟩ := sepConj_predLift_iff.1 hb
    exact ⟨d, sepConj_predLift_iff.2 ⟨hT,
      ⟨b, sepConj_predLift_iff.2 ⟨hS, hR⟩⟩⟩⟩

/-- Source `hr_comp_prod_conv`: composition distributes through the product
assertion and product relation. -/
@[simp] theorem hr_comp_prod_conv
    {α₁ α₂ β₁ β₂ κ₁ κ₂ : Type}
    (Ra : β₁ → κ₁ → Assn) (Rb : β₂ → κ₂ → Assn)
    (Ra' : Set (β₁ × α₁)) (Rb' : Set (β₂ × α₂)) :
    hrComp (Ra ×ₐ Rb) (Ra' ×ᵣ Rb') = hrComp Ra Ra' ×ₐ hrComp Rb Rb' := by
  funext a c hp
  apply propext
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hrel, hab⟩ := sepConj_predLift_iff.1 hb
    rcases hab with ⟨h₁, h₂, hd, rfl, hRa, hRb⟩
    exact ⟨h₁, h₂, hd, rfl, hr_compI hrel.1 h₁ hRa, hr_compI hrel.2 h₂ hRb⟩
  · rintro ⟨h₁, h₂, hd, rfl, hRa, hRb⟩
    obtain ⟨ba, hRa⟩ := hRa
    obtain ⟨hra, hRa⟩ := sepConj_predLift_iff.1 hRa
    obtain ⟨bb, hRb⟩ := hRb
    obtain ⟨hrb, hRb⟩ := sepConj_predLift_iff.1 hRb
    exact ⟨(ba, bb), sepConj_predLift_iff.2 ⟨⟨hra, hrb⟩,
      ⟨h₁, h₂, hd, rfl, hRa, hRb⟩⟩⟩

/-! ## Uniform result time -/

/-- Source `one_time`: every result actually offered by a computation has
the same (non-bottom) cost. -/
def oneTime {α : Type} (m : NRest α ECost) : Prop :=
  ∀ M, m = NRest.rest M → ∀ x y (s t : ECost),
    M x = (s : WithBot ECost) → M y = (t : WithBot ECost) → s = t

/-- Source `one_time_attains_sup`.  Unlike `attains_sup_sv`, this permits a
genuinely multi-valued result relation: uniform result cost, rather than
relation functionality, makes the supremum attained. -/
theorem one_time_attains_sup {β β' : Type} {m : NRest β ECost}
    {m' : NRest β' ECost} {RR : Set (β × β')} (hot : oneTime m') :
    attainsSup m m' RR := by
  intro r M' M _ hm' _ hex
  obtain ⟨a₀, ha₀⟩ := hex
  let V : Set (WithBot ECost) :=
    {u | ∃ a, (r, a) ∈ RR ∧ u = M' a}
  by_cases hreal : ∃ (a : β') (c : ECost), (r, a) ∈ RR ∧ M' a = (c : WithBot ECost)
  · obtain ⟨a, c, ha, hMc⟩ := hreal
    have hmax : sSup V = (c : WithBot ECost) := le_antisymm (sSup_le fun u hu => by
        obtain ⟨a', ha', rfl⟩ := hu
        rcases withBot_eq_bot_or_coe (M' a') with hbot | ⟨t, ht⟩
        · rw [hbot]; exact bot_le
        · rw [ht, hot M' hm' a' a t c ht hMc])
      (le_sSup (show (c : WithBot ECost) ∈ V from ⟨a, ha, hMc.symm⟩))
    change sSup V ∈ V
    rw [hmax]
    exact ⟨a, ha, hMc.symm⟩
  · have hall : ∀ a, (r, a) ∈ RR → M' a = ⊥ := by
      intro a ha
      rcases withBot_eq_bot_or_coe (M' a) with hbot | ⟨c, hc⟩
      · exact hbot
      · exact (hreal ⟨a, c, ha, hc⟩).elim
    have hset : V = {⊥} := by
      ext u
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact Set.mem_singleton_iff.mpr (hall a ha)
      · rintro rfl
        exact ⟨a₀, ha₀, (hall a₀ ha₀).symm⟩
    change sSup V ∈ V
    rw [hset, sSup_singleton]
    rfl

theorem oneTime_return {α : Type} (z : α) :
    oneTime (NRest.returnT z : NRest α ECost) := by
  intro M hm x y s t hx hy
  rw [NRest.returnT, NRest.rest_inj_iff] at hm
  rw [← hm] at hx hy
  have hz : ∀ q (u : ECost), NRest.single z (0 : WithBot ECost) q = (u : WithBot ECost) → u = 0 := by
    intro q u hq
    rcases eq_or_ne q z with rfl | hne
    · rw [NRest.single_self, ← WithBot.coe_zero, WithBot.coe_inj] at hq
      exact hq.symm
    · rw [NRest.single_of_ne hne] at hq
      exact absurd hq.symm WithBot.coe_ne_bot
  exact (hz x s hx).trans (hz y t hy).symm

theorem oneTime_consume {α : Type} {m : NRest α ECost} (hot : oneTime m) (c : ECost) :
    oneTime (NRest.consume m c) := by
  cases m with
  | fail =>
      intro M hm
      exact (NRest.rest_ne_fail M hm.symm).elim
  | rest X =>
      intro M hm x y s t hx hy
      rw [NRest.consume_rest', NRest.rest_inj_iff] at hm
      rw [← hm] at hx hy
      change (c : WithBot ECost) + X x = (s : WithBot ECost) at hx
      change (c : WithBot ECost) + X y = (t : WithBot ECost) at hy
      rcases withBot_eq_bot_or_coe (X x) with hxb | ⟨sx, hsx⟩
      · rw [hxb, WithBot.add_bot] at hx
        exact absurd hx.symm WithBot.coe_ne_bot
      · rcases withBot_eq_bot_or_coe (X y) with hyb | ⟨sy, hsy⟩
        · rw [hyb, WithBot.add_bot] at hy
          exact absurd hy.symm WithBot.coe_ne_bot
        · have hsame : sx = sy := hot X rfl x y sx sy hsx hsy
          rw [hsx, ← WithBot.coe_add, WithBot.coe_inj] at hx
          rw [hsy, ← WithBot.coe_add, WithBot.coe_inj] at hy
          have hxs : c + sx = s := hx
          have hyt : c + sy = t := hy
          exact hxs.symm.trans ((congrArg (c + ·) hsame).trans hyt)

theorem oneTime_assert (Φ : Prop) : oneTime (NRest.assert Φ : NRest Unit ECost) := by
  by_cases hΦ : Φ
  · rw [NRest.assert_pos hΦ]; exact oneTime_return ()
  · intro M hm
    rw [NRest.assert_neg hΦ] at hm
    exact (NRest.rest_ne_fail M hm.symm).elim

theorem oneTime_fail {α : Type} : oneTime (NRest.fail : NRest α ECost) := by
  intro M hm
  exact (NRest.rest_ne_fail M hm.symm).elim

theorem oneTime_spec {α : Type} (P : α → Prop) (c : ECost) :
    oneTime (NRest.spec P (fun _ => c)) := by
  classical
  intro M hm x y s t hx hy
  rw [NRest.spec, NRest.rest_inj_iff] at hm
  rw [← hm] at hx hy
  change (if P x then (c : WithBot ECost) else ⊥) = (s : WithBot ECost) at hx
  change (if P y then (c : WithBot ECost) else ⊥) = (t : WithBot ECost) at hy
  by_cases hPx : P x
  · rw [if_pos hPx, WithBot.coe_inj] at hx
    by_cases hPy : P y
    · rw [if_pos hPy, WithBot.coe_inj] at hy
      exact hx.symm.trans hy
    · rw [if_neg hPy] at hy
      exact absurd hy.symm WithBot.coe_ne_bot
  · rw [if_neg hPx] at hx
    exact absurd hx.symm WithBot.coe_ne_bot

/-- Source `attains_sup_mop_return`, in the current explicit `bindT` spelling. -/
theorem attains_sup_mop_return {β α : Type} (m : NRest β ECost) (Φ : Prop)
    (x : α) (c : ECost) (R : Set (β × α)) :
    attainsSup m (NRest.bindT (NRest.assert Φ) fun _ =>
      NRest.consume (NRest.returnT x) c) R := by
  apply one_time_attains_sup
  by_cases hΦ : Φ
  · rw [NRest.assert_pos hΦ, NRest.returnT_bindT]
    exact oneTime_consume (oneTime_return x) c
  · rw [NRest.assert_neg hΦ, NRest.bindT_fail]
    exact oneTime_fail

/-- Source `attains_sup_mop_spec`; the current `NRest.spec` has exactly the
source carrier, including its constant-cost function. -/
theorem attains_sup_mop_spec {β α : Type} (m : NRest β ECost) (Φ : Prop)
    (P : α → Prop) (c : ECost) (R : Set (β × α)) :
    attainsSup m (NRest.bindT (NRest.assert Φ) fun _ =>
      NRest.spec P (fun _ => c)) R := by
  apply one_time_attains_sup
  by_cases hΦ : Φ
  · rw [NRest.assert_pos hΦ, NRest.returnT_bindT]
    exact oneTime_spec P c
  · rw [NRest.assert_neg hΦ, NRest.bindT_fail]
    exact oneTime_fail

/-- Nontrivial gate: the relation is not single-valued, but a two-result
constant-time specification still attains its supremum. -/
theorem oneTime_multivalued_gate :
    ¬ SingleValued (Set.univ : Set (Unit × Bool)) ∧
      attainsSup (NRest.returnT () : NRest Unit ECost)
        (NRest.spec (fun _ : Bool => True) (fun _ => (0 : ECost))) Set.univ := by
  constructor
  · intro hsv
    exact Bool.false_ne_true (hsv () false true trivial trivial)
  · exact one_time_attains_sup (oneTime_spec (fun _ : Bool => True) 0)

end Lax13Proofs.Refine.Sepref
