import Lax13Proofs.Refine.NREST.Foreach
import Lax13Proofs.Refine.Autoref.Param
import Lax13Proofs.Refine.Autoref.Tool

/-!
# Autoref rules for member-list iteration

Tower-expansion P2.B port of the automatic-refinement half of AFP
`Refine_Foreach.thy`.  Lists represent finite sets only when their abstract
counterpart is distinct; `nfoldli` itself is exposed through the normal
`autoref_rules` database at the full currency-vector NREST relation.
-/

namespace Lax13Proofs.Refine

open NRest

variable {α β σ τ : Type}

/-- The source's `list_set_rel R = ⟨R⟩list_rel O br set distinct`, expanded
into its witness form. -/
def listSetRel (R : Set (α × β)) : Set (List α × Set β) :=
  {p | ∃ l' : List β, (p.1, l') ∈ listRel R ∧ l'.Nodup ∧ p.2 = {x | x ∈ l'}}

@[simp, refine_rel_defs] theorem mem_listSetRel_iff {R : Set (α × β)}
    {l : List α} {S : Set β} :
    (l, S) ∈ listSetRel R ↔
      ∃ l' : List β, (l, l') ∈ listRel R ∧ l'.Nodup ∧ S = {x | x ∈ l'} := Iff.rfl

private theorem listRel_diagonal_iff {l l' : List α} :
    (l, l') ∈ listRel (Set.diagonal α) ↔ l = l' := by
  change List.Forall₂ (fun x x' => x = x') l l' ↔ l = l'
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons h _ ih =>
        cases h
        exact congrArg _ ih
  · rintro rfl
    induction l with
    | nil => exact List.Forall₂.nil
    | cons x xs ih => exact List.Forall₂.cons rfl ih

/-- At identity, a list represents exactly its element set and carries the
source's distinctness invariant. -/
theorem mem_listSetRel_diagonal_iff {l : List α} {S : Set α} :
    (l, S) ∈ listSetRel (Set.diagonal α) ↔ l.Nodup ∧ S = {x | x ∈ l} := by
  change (∃ l' : List α,
    (l, l') ∈ listRel (Set.diagonal α) ∧ l'.Nodup ∧ S = {x | x ∈ l'}) ↔ _
  constructor
  · rintro ⟨l', hl, hnd, rfl⟩
    have heq := listRel_diagonal_iff.mp hl
    subst l'
    exact ⟨hnd, rfl⟩
  · rintro ⟨hnd, rfl⟩
    exact ⟨l, listRel_diagonal_iff.mpr rfl, hnd, rfl⟩

/-- Every observable result of `itToSortedListE` represents exactly its
input set through `listSetRel`; the ordering witness is retained. -/
theorem itToSortedListE_result_listSetRel (R : α → α → Prop) (S : Set α)
    (κ t : ECost) (xs : List α)
    (h : NRest.inresT (NRest.itToSortedListE R S κ) xs t) :
    (xs, S) ∈ listSetRel (Set.diagonal α) ∧ xs.Pairwise R := by
  rw [NRest.inresT_itToSortedListE_iff] at h
  exact ⟨mem_listSetRel_diagonal_iff.mpr ⟨h.1.1, h.1.2.1⟩, h.1.2.2⟩

/-- Source `LIST_FOREACH'`: obtain a member list, then fold it directly. -/
noncomputable def LIST_FOREACHPrimeE (toList : NRest (List α) ECost)
    (c : σ → Bool) (f : α → σ → NRest σ ECost) (s : σ) : NRest σ ECost :=
  NRest.bindT toList fun xs => NRest.nfoldli c f xs s

/-- The source's `LIST_FOREACH'_param`, at the currency-vector carrier. -/
@[param] theorem LIST_FOREACHPrimeE_param (Ra : Set (α × β))
    (Rs : Set (σ × τ)) :
    (LIST_FOREACHPrimeE (α := α) (σ := σ),
      LIST_FOREACHPrimeE (α := β) (σ := τ)) ∈
      NRest.nrestRel (listRel Ra) →ᵣ (Rs →ᵣ boolRel) →ᵣ
        (Ra →ᵣ Rs →ᵣ NRest.nrestRel Rs) →ᵣ Rs →ᵣ NRest.nrestRel Rs := by
  intro tsi ts hts ci c hc fi f hf si s hs
  exact NRest.nrestRel_of_le <| NRest.bindT_refine_of NRest.addSupContinuousB_acost
    (NRest.nrestRel_le hts) fun li l hl =>
      NRest.nfoldli_refine Ra Rs hl hs
        (fun si s hs => hc si s hs)
        (fun xi x si s hxi hs _ => NRest.nrestRel_le (hf xi x hxi si s hs))

/-- The source's `autoref_nfoldli`, generalized from scalar NRES to the
repository's currency-vector NREST. -/
@[autoref_rules] theorem autoref_nfoldli (Ra : Set (α × β)) (Rs : Set (σ × τ)) :
    (NRest.nfoldli (γ := ECost) (α := α) (σ := σ),
      NRest.nfoldli (γ := ECost) (α := β) (σ := τ)) ∈
      (Rs →ᵣ boolRel) →ᵣ (Ra →ᵣ Rs →ᵣ NRest.nrestRel Rs) →ᵣ
        listRel Ra →ᵣ Rs →ᵣ NRest.nrestRel Rs := by
  intro ci c hc fi f hf li l hl si s hs
  exact NRest.nrestRel_of_le <| NRest.nfoldli_refine Ra Rs hl hs
    (fun si s hs => hc si s hs)
    (fun xi x si s hxi hs _ => NRest.nrestRel_le (hf xi x hxi si s hs))

/-! ## Gates -/

theorem two_members_listSetRel :
    (([7, 91] : List ℕ), {x | x = 7 ∨ x = 91}) ∈ listSetRel natRel := by
  rw [mem_listSetRel_diagonal_iff]
  constructor
  · decide
  · ext x
    simp

theorem sorted_list_result_gate :
    (([7, 91] : List ℕ), {x | x = 7 ∨ x = 91}) ∈ listSetRel natRel ∧
      ([7, 91] : List ℕ).Pairwise (· < ·) := by
  constructor
  · exact two_members_listSetRel
  · simp

/-- info: 'Lax13Proofs.Refine.autoref_nfoldli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms autoref_nfoldli

/-- info: 'Lax13Proofs.Refine.LIST_FOREACHPrimeE_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LIST_FOREACHPrimeE_param

/-- info: 'Lax13Proofs.Refine.two_members_listSetRel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_members_listSetRel

/-- info: 'Lax13Proofs.Refine.sorted_list_result_gate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sorted_list_result_gate

end Lax13Proofs.Refine
