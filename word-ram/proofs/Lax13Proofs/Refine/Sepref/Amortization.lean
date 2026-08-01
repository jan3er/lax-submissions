import Lax13Proofs.Refine.Sepref.Basic
import Lax13Proofs.Refine.NREST.BackwardsReasoning
import Lax13Proofs.Refine.NREST.TimeRefinement

/-!
# Generic vector amortization

Source-accounting table:

| source | range | disposition |
|---|---:|---|
| `SLTC.thy` | 53--302 | existing generic assertion/credit algebra in `Ir/Assn.lean` |
| `SLTC.thy` | 304--350 | existing entailment/GC credit weakening; source-shaped support only below |
| `SLTC.thy` | 352--484 | existing `Wp`/frame/consequence capital |
| `SLTC.thy` | 486--573 | existing primitive triples in `Ir/Triples.lean` |
| `SLTC_More.thy` | 7--161, 186--260, 262--345, 610--631 | existing normalization, GC-entailment, `sepOr`, and consequence |
| `SLTC_More.thy` | 165--184 | excluded: D2/X13 address heap relation is superseded by named cells |
| `SLTC_More.thy` | 347--606 | excluded: conjunction/precision/auto2 classifier lies outside the selected credit slice |
| `Dynamic_Array.thy` | 6--200 | existing cost/time-refinement capital; private direct support below where required |
| `Dynamic_Array.thy` | 202--291 | landed here: `reclaim` family and time-refinement bridge |
| `Dynamic_Array.thy` | 293--305 | landed here: potential-augmented assertion family |
| `Dynamic_Array.thy` | 308--333 | landed here: finite-cost/extraction family |
| `Dynamic_Array.thy` | 336--458 | landed here: `Wp`/`hnRefine` amortization family |

The primary source is `Dynamic_Array.thy` at
`lammich/isabelle_llvm_time@42dd7f59998d76047bb4b6bce76d8f67b53a08b6`.
Resource subtraction is always the source operation `-ᵣ`; in particular,
`⊤ -ᵣ ⊤ = ⊤`.
-/

namespace Lax13Proofs.Refine

open Classical

/-! ## Authored two-currency seam checks -/

private abbrev TwoCurrency := Fin 2

private def reclaimMirror (available required : TwoCurrency → ℕ∞) :
    Option (TwoCurrency → ℕ∞) :=
  if ∀ i, required i ≤ available i then
    some (fun i => available i -ᵣ required i)
  else none

private theorem reclaimMirror_eq_pointwise {available required residual : TwoCurrency → ℕ∞}
    (h : reclaimMirror available required = some residual) :
    ∀ i, residual i = available i -ᵣ required i := by
  simp only [reclaimMirror] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst residual
    intro i
    rfl
  · contradiction

private abbrev firstCurrency : String := "reclaim-first"

private abbrev secondCurrency : String := "reclaim-second"

private def twoCost (v : TwoCurrency → ℕ∞) : ECost :=
  ⟨fun k => if k = firstCurrency then v 0 else if k = secondCurrency then v 1 else 0⟩

private theorem twoCost_le_iff {a b : TwoCurrency → ℕ∞} :
    twoCost a ≤ twoCost b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i
    fin_cases i
    · simpa [twoCost] using ACost.le_def.mp h firstCurrency
    · simpa [twoCost] using ACost.le_def.mp h secondCurrency
  · intro h
    apply ACost.le_def.mpr
    intro k
    by_cases hk₀ : k = firstCurrency
    · subst k
      simpa [twoCost] using h 0
    · by_cases hk₁ : k = secondCurrency
      · subst k
        simpa [twoCost, hk₀] using h 1
      · simp [twoCost, hk₀, hk₁]

private theorem twoCost_resSub (a b : TwoCurrency → ℕ∞) :
    twoCost a -ᵣ twoCost b = twoCost (fun i => a i -ᵣ b i) := by
  ext k
  by_cases hk₀ : k = firstCurrency
  · subst k
    simp [twoCost, ACost.toFun_resSub]
  · by_cases hk₁ : k = secondCurrency
    · subst k
      simp [twoCost, ACost.toFun_resSub, hk₀]
    · simp [twoCost, ACost.toFun_resSub, hk₀, hk₁]

#guard reclaimMirror ![5, 7] ![2, 3] = some ![3, 4]
#guard reclaimMirror ![2, 2] ![2, 3] = none
#guard reclaimMirror ![8, 2] ![2, 3] = none
#guard reclaimMirror ![⊤, 7] ![⊤, 3] = some ![⊤, 4]

namespace NRest

/-! ## Reclaiming potential -/

/-- Source `reclaim` (`Dynamic_Array.thy:205`), rendered pointwise over
vector-valued `ECost`. Any available result that cannot pay its requested
potential makes the whole computation fail. -/
noncomputable def reclaim {α : Type} (m : NRest α ECost) (t : α → ECost) :
    NRest α ECost :=
  match m with
  | .fail => .fail
  | .rest M =>
      if ∀ x (c : ECost), M x = (c : WithBot ECost) → t x ≤ c then
        .rest fun x => (M x).recBotCoe ⊥ fun c => ((c -ᵣ t x : ECost) : WithBot ECost)
      else .fail

private def twoResult (available : TwoCurrency → ℕ∞) : NRest Unit ECost :=
  .rest fun _ => ((twoCost available : ECost) : WithBot ECost)

private def twoPotential (required : TwoCurrency → ℕ∞) : Unit → ECost :=
  fun _ => twoCost required

private theorem reclaim_twoCurrency_eq (available required : TwoCurrency → ℕ∞) :
    reclaim (twoResult available) (twoPotential required) =
      match reclaimMirror available required with
      | none => .fail
      | some residual =>
          .rest fun _ => ((twoCost residual : ECost) : WithBot ECost) := by
  simp only [reclaim, twoResult, twoPotential, reclaimMirror]
  by_cases hpay : ∀ i, required i ≤ available i
  · have hglobal : ∀ (_ : Unit) (c : ECost),
        (twoCost available : WithBot ECost) = (c : WithBot ECost) →
          twoCost required ≤ c := by
      intro _ c hc
      have hc' : c = twoCost available := by
        exact WithBot.coe_injective hc.symm
      subst c
      exact twoCost_le_iff.mpr hpay
    rw [if_pos hglobal, if_pos hpay]
    congr 1
    funext x
    cases x
    simp only [WithBot.recBotCoe_coe]
    rw [twoCost_resSub]
  · have hglobal : ¬ ∀ (_ : Unit) (c : ECost),
        (twoCost available : WithBot ECost) = (c : WithBot ECost) →
          twoCost required ≤ c := by
      intro h
      apply hpay
      exact twoCost_le_iff.mp (h () (twoCost available) rfl)
    rw [if_neg hglobal, if_neg hpay]

private theorem reclaim_exactResidual_gate :
    reclaim (twoResult ![5, 7]) (twoPotential ![2, 3]) =
      .rest (fun _ => ((twoCost ![3, 4] : ECost) : WithBot ECost)) := by
  rw [reclaim_twoCurrency_eq]
  norm_num [reclaimMirror]
  congr

private theorem reclaim_insufficientPotential_gate :
    reclaim (twoResult ![2, 2]) (twoPotential ![2, 3]) = .fail := by
  rw [reclaim_twoCurrency_eq]
  norm_num [reclaimMirror]

private theorem reclaim_currencyIsolation_gate :
    reclaim (twoResult ![8, 2]) (twoPotential ![2, 3]) = .fail := by
  rw [reclaim_twoCurrency_eq]
  norm_num [reclaimMirror]

private theorem reclaim_topBehavior_gate :
    reclaim (twoResult ![⊤, 7]) (twoPotential ![⊤, 3]) =
      .rest (fun _ => ((twoCost ![⊤, 4] : ECost) : WithBot ECost)) := by
  rw [reclaim_twoCurrency_eq]
  norm_num [reclaimMirror]
  congr

/-- Source `reclaim_nofailT` / requested public stem `reclaim_fail`. -/
@[simp] theorem reclaim_fail {α : Type} (t : α → ECost) :
    reclaim (.fail : NRest α ECost) t = .fail := rfl

/-- Source `nofailT_reclaim` (`Dynamic_Array.thy:238`). -/
theorem nofailT_reclaim {α : Type} {m : NRest α ECost} {t : α → ECost} :
    (reclaim m t).nofailT ↔
      m.nofailT ∧ ∀ M, m = .rest M → ∀ x (c : ECost),
        M x = (c : WithBot ECost) → t x ≤ c := by
  cases m with
  | fail => simp [reclaim]
  | rest M =>
      simp only [reclaim, nofailT_rest, true_and]
      split
      · simp_all
      · simp_all

/-- Source `reclaim_SPEC` (`Dynamic_Array.thy:247`). -/
theorem reclaim_spec {α : Type} {Q : α → Prop} {T Φ : α → ECost}
    (h : ∀ x, Q x → Φ x ≤ T x) :
    reclaim (spec Q T) Φ = spec Q (fun x => T x -ᵣ Φ x) := by
  simp only [spec, reclaim]
  split
  · congr 1
    funext x
    by_cases hx : Q x <;> simp [hx]
  · rename_i hn
    exfalso
    apply hn
    intro x c hxc
    by_cases hx : Q x
    · simp [hx] at hxc
      subst c
      exact h x hx
    · simp [hx] at hxc

/-- Source `reclaim_SPEC_le` (`Dynamic_Array.thy:255`). -/
theorem reclaim_spec_le {α : Type} {Q : α → Prop} {T Φ : α → ECost} :
    spec Q (fun x => T x -ᵣ Φ x) ≤ reclaim (spec Q T) Φ := by
  simp only [spec, reclaim]
  split
  · apply rest_le_rest_iff.mpr
    intro x
    by_cases hx : Q x <;> simp [hx]
  · exact le_fail _

private theorem consume_spec_eq {α : Type} (Q : α → Prop) (T : α → ECost) (c : ECost) :
    consume (spec Q T) c = spec Q (fun x => c + T x) := by
  rw [spec, consume_rest, spec, rest_inj_iff]
  funext x
  by_cases hx : Q x <;> simp [hx]

private theorem enat_resSub_add_cancel_of_le {a b : ℕ∞} (h : b ≤ a) :
    a -ᵣ b + b = a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp
  · rw [enat_resSub_of_ne_top ha, tsub_add_cancel_of_le h]

private theorem acost_resSub_add_cancel_of_le {κ : Type} {a b : ACost κ ℕ∞}
    (h : b ≤ a) : a -ᵣ b + b = a := by
  ext k
  exact enat_resSub_add_cancel_of_le (ACost.le_def.mp h k)

private theorem timerefineA_resSub_le {κ κ' : Type} {E : κ → ACost κ' ℕ∞}
    (hE : wfR'' E) {a b : ACost κ ℕ∞} (hba : b ≤ a) :
    timerefineA E (a -ᵣ b) ≤ timerefineA E a -ᵣ timerefineA E b := by
  apply Needname.le_diff_if_add_le
  · rw [← timerefineA_add hE, acost_resSub_add_cancel_of_le hba]
  · exact timerefineA_mono hE hba

/-- Source `pull_timerefine_through_reclaim` (`Dynamic_Array.thy:263`),
requested as `timerefine_reclaim`. -/
theorem timerefine_reclaim {α : Type} {E : String → ECost}
    (hE : wfR'' E) {Q : α → Prop} {T : α → ECost}
    {Φ : ECost} {Φ' : α → ECost}
    (hΦ : ∀ x, Q x → Φ' x ≤ T x + Φ) :
    timerefine E (reclaim (consume (spec Q T) Φ) Φ') ≤
      reclaim
        (consume (spec Q (fun x => timerefineA E (T x))) (timerefineA E Φ))
        (fun x => timerefineA E (Φ' x)) := by
  rw [consume_spec_eq]
  rw [reclaim_spec (fun x hx => by simpa [add_comm] using hΦ x hx)]
  rw [timerefine_spec]
  rw [consume_spec_eq]
  rw [reclaim_spec]
  · rw [spec, spec, rest_le_rest_iff]
    intro x
    by_cases hx : Q x
    · simp only [if_pos hx, WithBot.coe_le_coe]
      rw [← timerefineA_add hE]
      exact timerefineA_resSub_le hE (by simpa [add_comm] using hΦ x hx)
    · simp [hx]
  · intro x hx
    rw [← timerefineA_add hE]
    exact timerefineA_mono hE (by simpa [add_comm] using hΦ x hx)

end NRest

namespace ACost

/-! ## Pointwise finite costs -/

/-- Source `finite_cost` (`Dynamic_Array.thy:310`). Since `ACost` is a total
function, this is pointwise non-topness, not finite support. -/
def FiniteCost {κ : Type} (t : ACost κ ℕ∞) : Prop := ∀ k, t.toFun k < ⊤

/-- Source `finite_costD` (`Dynamic_Array.thy:312`). -/
theorem finiteCost_apply {κ : Type} {t : ACost κ ℕ∞} (h : FiniteCost t) (k : κ) :
    t.toFun k < ⊤ := h k

/-- Source `finite_cost_lift_acost` (`Dynamic_Array.thy:319`). -/
theorem finiteCost_liftACost {κ : Type} (t : ACost κ ℕ) : FiniteCost (liftACost t) := by
  intro k
  simp

/-- Source `extract_lift_acost_if_less_infinity` (`Dynamic_Array.thy:322`). -/
theorem exists_liftACost_eq {κ : Type} {t : ACost κ ℕ∞} (h : FiniteCost t) :
    ∃ t' : ACost κ ℕ, liftACost t' = t := by
  let t' : ACost κ ℕ := ⟨fun k => ENat.toNat (t.toFun k)⟩
  refine ⟨t', ?_⟩
  ext k
  exact ENat.coe_toNat (ne_of_lt (h k))

end ACost

namespace Sepref

open Ir

/-! ## Potential-augmented assertions -/

/-- Source `augment_amor_assn` (`Dynamic_Array.thy:295`). -/
def augmentAmorAssn {α κ : Type} (Φ : α → ECost) (A : α → κ → Assn) :
    α → κ → Assn := fun a c => ¤(Φ a) ∗ A a c

/-- Source `invalid_assn_augment_amor_assn` (`Dynamic_Array.thy:297`). -/
@[simp] theorem invalidAssn_augmentAmorAssn {α κ : Type} (Φ : α → ECost)
    (A : α → κ → Assn) :
    invalidAssn (augmentAmorAssn Φ A) = invalidAssn A := by
  funext a c
  apply congrArg predLift
  apply propext
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨cr, -, hA⟩ := credits_sepConj_iff.mp hh
    exact ⟨((h.1.1, h.1.2), cr), hA⟩
  · rintro ⟨hs, hA⟩
    rcases hs with ⟨⟨V, Ar⟩, cr⟩
    exact ⟨((V, Ar), Φ a + cr), credits_sepConj_iff.2 ⟨cr, rfl, hA⟩⟩

/-! ## Framing time through `wp` -/

/-- Source `wp_time_frame` (`Dynamic_Array.thy:343`). -/
theorem wpTimeFrame {c : Ir.Com} {Q : Unit → Ir.Assn} {s : Ir.State}
    {cr t : ECost}
    (h : Ir.wp c (fun r => Ir.irSTATE (Q r)) (s, cr)) :
    Ir.wp c (fun r => Ir.irSTATE (¤t ∗ Q r)) (s, cr + t) := by
  rcases h with ⟨s', κ, hstep, hQ, hle⟩
  refine ⟨s', κ, hstep, ?_, leCostECost_add_right hle t⟩
  rw [← minusECost_add_of_le hle t, add_comm]
  exact Ir.credits_merge hQ

private theorem credits_gc_absorb (q : ECost) (A B F : Ir.Assn) :
    ¤q ∗ (A ∗ (B ∗ (F ∗ Ir.GC))) ⊢ A ∗ (B ∗ (F ∗ Ir.GC)) := by
  rw [Ir.sepConj_left_comm]
  apply Ir.conj_entails_mono (Ir.entails_refl A)
  rw [Ir.sepConj_left_comm]
  apply Ir.conj_entails_mono (Ir.entails_refl B)
  rw [Ir.sepConj_left_comm]
  apply Ir.conj_entails_mono (Ir.entails_refl F)
  intro h hh
  have hh' := Ir.conj_entails_mono (Ir.entails_GC q) (Ir.entails_refl Ir.GC) h hh
  rwa [Ir.GC_absorb] at hh'

private theorem acost_add_resSub_cancel_of_le {a b : ECost} (h : b ≤ a) :
    b + (a -ᵣ b) = a := by
  rw [add_comm]
  exact NRest.acost_resSub_add_cancel_of_le h

/-! ## Refinement rules -/

/-- Source `hn_refineI2` (`Dynamic_Array.thy:364`). -/
theorem hnRefineI2 {α κ : Type} {Γ Γ' : Ir.Assn} {c : Ir.Com} {d : κ}
    {R : α → κ → Ir.Assn} {m : NRest α ECost}
    (h : ∀ (F : Ir.Assn) (s : Ir.State) (cr : ECost)
      (M : α → WithBot ECost), m.nofailT → m = .rest M →
      Ir.irSTATE (Γ ∗ F) (s, cr) →
      ∃ (ra : α) (Ca : ECost), (Ca : WithBot ECost) ≤ M ra ∧
        Ir.wp c (fun _ => Ir.irSTATE (Γ' ∗ R ra d ∗ F ∗ Ir.GC)) (s, cr + Ca)) :
    hnRefine Γ c Γ' d R m := by
  intro hnf M F s cr hm hs
  exact h F s cr M hnf hm hs

/-- Source `hn_refine_payday_reverse_alt` (`Dynamic_Array.thy:372`),
requested as `hnRefine_paydayReverse`. The finite-cost premise is preserved
even though the vector-credit proof itself works directly at `ECost`. -/
theorem hnRefine_paydayReverse {α κ : Type} {Γ Γ' : Ir.Assn} {c : Ir.Com}
    {d : κ} {R : α → κ → Ir.Assn} {m : NRest α ECost} {t : ECost}
    (_ht : ACost.FiniteCost t)
    (h : hnRefine Γ c Γ' d R (NRest.consume m t)) :
    hnRefine (¤t ∗ Γ) c Γ' d R m := by
  apply hnRefineI2
  intro F s cr M _hnf hm hs
  rw [Ir.sepConj_assoc] at hs
  obtain ⟨cr₀, hcr, hs₀⟩ := Ir.credits_split hs
  have hmcons : NRest.consume m t =
      .rest (fun x => WithBot.map (t + ·) (M x)) := by
    rw [hm]
    rfl
  obtain ⟨ra, Ca, hCa, hwp⟩ := hnRefineD h hmcons hs₀
  rcases withBot_eq_bot_or_coe (M ra) with hbot | ⟨D, hD⟩
  · simp [hbot] at hCa
  · have hCa' : Ca ≤ t + D := by
      simpa [hD, ← WithBot.coe_add] using hCa
    let q : ECost := (t + D) -ᵣ Ca
    have hcancel : Ca + q = t + D := acost_add_resSub_cancel_of_le hCa'
    refine ⟨ra, D, ?_, ?_⟩
    · rw [hD]
    · have hframed := wpTimeFrame (t := q) hwp
      have hstart : cr₀ + Ca + q = cr + D := by
        calc
          cr₀ + Ca + q = cr₀ + (Ca + q) := by ac_rfl
          _ = cr₀ + (t + D) := by rw [hcancel]
          _ = (t + cr₀) + D := by ac_rfl
          _ = cr + D := by rw [hcr]
      rw [hstart] at hframed
      exact Ir.wp_mono_ir (fun _ p hp => by
        exact credits_gc_absorb q Γ' (R ra d) F (Ir.irα p) hp) hframed

private theorem credits_move_to_result (q : ECost) (A B F : Ir.Assn) :
    ¤q ∗ (A ∗ (B ∗ (F ∗ Ir.GC))) = A ∗ ((¤q ∗ B) ∗ (F ∗ Ir.GC)) := by
  calc
    ¤q ∗ (A ∗ (B ∗ (F ∗ Ir.GC))) = A ∗ (¤q ∗ (B ∗ (F ∗ Ir.GC))) :=
      Ir.sepConj_left_comm _ _ _
    _ = A ∗ ((¤q ∗ B) ∗ (F ∗ Ir.GC)) := by
      rw [Ir.sepConj_assoc]

/-- Source `hn_refine_reclaimday` (`Dynamic_Array.thy:392`), requested as
`hnRefine_reclaim`. -/
theorem hnRefine_reclaim {α κ : Type} {Γ Γ' : Ir.Assn} {c : Ir.Com}
    {d : κ} {G : α → κ → Ir.Assn} {m : NRest α ECost} {Φ : α → ECost}
    (hnf : m.nofailT → (NRest.reclaim m Φ).nofailT)
    (h : hnRefine Γ c Γ' d G (NRest.reclaim m Φ)) :
    hnRefine Γ c Γ' d (augmentAmorAssn Φ G) m := by
  apply hnRefineI2
  intro F s cr M hm_nf hm hs
  have hr_nf : (NRest.reclaim m Φ).nofailT := hnf hm_nf
  have hglobal : ∀ x (D : ECost), M x = (D : WithBot ECost) → Φ x ≤ D := by
    exact (NRest.nofailT_reclaim.mp hr_nf).2 M hm
  have hr : NRest.reclaim m Φ = .rest (fun x =>
      (M x).recBotCoe ⊥ fun D => ((D -ᵣ Φ x : ECost) : WithBot ECost)) := by
    rw [hm]
    simp only [NRest.reclaim]
    rw [if_pos hglobal]
  obtain ⟨ra, Ca, hCa, hwp⟩ := hnRefineD h hr hs
  rcases withBot_eq_bot_or_coe (M ra) with hbot | ⟨D, hD⟩
  · simp [hbot] at hCa
  · have hpot : Φ ra ≤ D := hglobal ra D hD
    have hCa' : Ca ≤ D -ᵣ Φ ra := by
      simpa [hD] using hCa
    have htotal : Ca + Φ ra ≤ D := by
      calc
        Ca + Φ ra ≤ (D -ᵣ Φ ra) + Φ ra := by gcongr
        _ = D := NRest.acost_resSub_add_cancel_of_le hpot
    refine ⟨ra, Ca + Φ ra, ?_, ?_⟩
    · rw [hD, WithBot.coe_le_coe]
      exact htotal
    · have hframed := wpTimeFrame (t := Φ ra) hwp
      rw [show cr + Ca + Φ ra = cr + (Ca + Φ ra) by ac_rfl] at hframed
      exact Ir.wp_mono_ir (fun _ p hp => by
        change Ir.irSTATE (Γ' ∗ ((¤(Φ ra) ∗ G ra d) ∗ (F ∗ Ir.GC))) p
        rw [← credits_move_to_result (Φ ra) Γ' (G ra d) F]
        exact hp) hframed

private theorem nofailT_consume_iff {α : Type} {m : NRest α ECost} {t : ECost} :
    (NRest.consume m t).nofailT ↔ m.nofailT := by
  cases m <;> simp [NRest.consume]

/-- Source `hn_refine_amortization` (`Dynamic_Array.thy:443`). -/
theorem hnRefine_amortization {α κ ρ ρ' : Type}
    {G : α → κ → Ir.Assn} {F' : ρ → ρ' → Ir.Assn}
    {m : α → ρ → NRest α ECost} {Φ : α → ECost}
    {x : α} {x' : κ} {r : ρ} {r' : ρ'} {c : Ir.Com} {d : κ}
    (hnf : ∀ a z, (m a z).nofailT →
      (NRest.reclaim (NRest.consume (m a z) (Φ a)) Φ).nofailT)
    (hfinite : ∀ a, ACost.FiniteCost (Φ a))
    (h : hnRefine (G x x' ∗ F' r r') c
      (invalidAssn G x x' ∗ F' r r') d G
      (NRest.reclaim (NRest.consume (m x r) (Φ x)) Φ)) :
    hnRefine (augmentAmorAssn Φ G x x' ∗ F' r r') c
      (invalidAssn (augmentAmorAssn Φ G) x x' ∗ F' r r') d
      (augmentAmorAssn Φ G) (m x r) := by
  have hr : hnRefine (G x x' ∗ F' r r') c
      (invalidAssn G x x' ∗ F' r r') d (augmentAmorAssn Φ G)
      (NRest.consume (m x r) (Φ x)) := by
    apply hnRefine_reclaim
    · intro hc
      exact hnf x r (nofailT_consume_iff.mp hc)
    · exact h
  have hp := hnRefine_paydayReverse (hfinite x) hr
  simpa only [augmentAmorAssn, invalidAssn_augmentAmorAssn, Ir.sepConj_assoc] using hp

end Sepref

/-! ## Kernel-three axiom guards -/

/-- info: 'Lax13Proofs.Refine.NRest.nofailT_reclaim' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms NRest.nofailT_reclaim

/-- info: 'Lax13Proofs.Refine.NRest.reclaim_spec' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms NRest.reclaim_spec

/-- info: 'Lax13Proofs.Refine.NRest.reclaim_spec_le' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms NRest.reclaim_spec_le

/-- info: 'Lax13Proofs.Refine.NRest.timerefine_reclaim' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms NRest.timerefine_reclaim

/-- info: 'Lax13Proofs.Refine.ACost.exists_liftACost_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ACost.exists_liftACost_eq

/-- info: 'Lax13Proofs.Refine.Sepref.invalidAssn_augmentAmorAssn' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms Sepref.invalidAssn_augmentAmorAssn

/-- info: 'Lax13Proofs.Refine.Sepref.wpTimeFrame' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms Sepref.wpTimeFrame

/-- info: 'Lax13Proofs.Refine.Sepref.hnRefineI2' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms Sepref.hnRefineI2

/-- info: 'Lax13Proofs.Refine.Sepref.hnRefine_paydayReverse' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms Sepref.hnRefine_paydayReverse

/-- info: 'Lax13Proofs.Refine.Sepref.hnRefine_reclaim' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms Sepref.hnRefine_reclaim

/-- info: 'Lax13Proofs.Refine.Sepref.hnRefine_amortization' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms Sepref.hnRefine_amortization

end Lax13Proofs.Refine
