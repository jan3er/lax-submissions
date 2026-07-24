import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Set-system layer of the Appendix-A machinery (DMMPT26): `v`-pairs and
the positive/negative merge structure, the Sauer–Shelah-style VC-drop
(Lemma 7), the Haussler–Littlestone–Warmuth packing bound (Lemma 8)
with its non-isolated-vertex corollary (Corollary 9), and the
dense-Hamming-restriction lemma (Lemma 19).

Design notes. A Hamming edge `{F, F.erase v}` of a set family is
recorded as the pair `(v, F)` with `F` `v`-positive, so `posPairs` is
literally the edge set of the Hamming graph and no graph structure is
ever needed. The merge graphs of the paper are the relations
`VPos`/`VNeg`: the neighborhood of `v` in the positive merge graph is
`𝓕.filter (VPos 𝓕 v)`, so the paper's Lemma 10 *is* Lemma 7 in this
encoding. Lemma 19 is stated for an indexed family of set systems (the
part systems of a sparsification, indexed by their label tuples)
instead of a partition of a bipartite graph; restriction to `X` is
`Finset.image (· ∩ X)`.
-/

namespace Lax5Proofs.SetSystems

open Finset

variable {α : Type*} [DecidableEq α] {𝓕 : Finset (Finset α)} {v : α}
  {F : Finset α}

/-- `F` is `v`-positive in `𝓕`: `v ∈ F` and removing `v` gives another
member, so that `{F, F.erase v}` is a Hamming edge ("`v`-pair"). -/
def VPos (𝓕 : Finset (Finset α)) (v : α) (F : Finset α) : Prop :=
  F ∈ 𝓕 ∧ v ∈ F ∧ F.erase v ∈ 𝓕

/-- `F` is `v`-negative in `𝓕`: `v ∉ F` and adding `v` gives another
member, so that `{insert v F, F}` is a Hamming edge ("`v`-pair"). -/
def VNeg (𝓕 : Finset (Finset α)) (v : α) (F : Finset α) : Prop :=
  F ∈ 𝓕 ∧ v ∉ F ∧ insert v F ∈ 𝓕

instance : Decidable (VPos 𝓕 v F) :=
  inferInstanceAs (Decidable (F ∈ 𝓕 ∧ v ∈ F ∧ F.erase v ∈ 𝓕))

instance : Decidable (VNeg 𝓕 v F) :=
  inferInstanceAs (Decidable (F ∈ 𝓕 ∧ v ∉ F ∧ insert v F ∈ 𝓕))

/-- The edges of the Hamming graph of `𝓕`, recorded as the pairs
`(v, F)` with `F` `v`-positive: the edge `{F, F.erase v}` joins the two
members differing exactly at `v`. -/
def posPairs (𝓕 : Finset (Finset α)) : Finset (α × Finset α) :=
  (𝓕.sup id ×ˢ 𝓕).filter fun p => VPos 𝓕 p.1 p.2

/-- The number of edges of the Hamming graph of `𝓕`. -/
def hammingEdgeCount (𝓕 : Finset (Finset α)) : ℕ := (posPairs 𝓕).card

/-- The members of `𝓕` that are non-isolated in the Hamming graph:
those lying in a `v`-pair for some `v` (necessarily from `𝓕.sup id`). -/
def nonIsolated (𝓕 : Finset (Finset α)) : Finset (Finset α) :=
  𝓕.filter fun F => ∃ v ∈ 𝓕.sup id, VPos 𝓕 v F ∨ VNeg 𝓕 v F

theorem mem_posPairs {p : α × Finset α} :
    p ∈ posPairs 𝓕 ↔ VPos 𝓕 p.1 p.2 := by
  unfold posPairs
  simp only [mem_filter, mem_product, and_iff_right_iff_imp]
  rintro ⟨hF, hv, -⟩
  exact ⟨mem_sup.2 ⟨p.2, hF, hv⟩, hF⟩

/-- Lemma 7 of DMMPT26 (positive half): the `v`-positive members form a
family of strictly smaller VC dimension. -/
theorem vcDim_filter_vPos_lt (h : (𝓕.filter (VPos 𝓕 v)).Nonempty) :
    (𝓕.filter (VPos 𝓕 v)).vcDim < 𝓕.vcDim := by
  set 𝓟 := 𝓕.filter (VPos 𝓕 v) with h𝓟
  obtain ⟨s, hs, hcard⟩ :=
    Finset.exists_mem_eq_sup 𝓟.shatterer
      ⟨∅, mem_shatterer.2 (shatters_empty.2 h)⟩ card
  rw [mem_shatterer] at hs
  have hv : v ∉ s := by
    intro hvs
    obtain ⟨u, hu, hsu⟩ := hs (erase_subset v s)
    have hvu : v ∈ u := ((mem_filter.1 hu).2).2.1
    exact notMem_erase v s (hsu ▸ mem_inter.2 ⟨hvs, hvu⟩)
  have hshat : 𝓕.Shatters (insert v s) := by
    intro t ht
    have ht' : t.erase v ⊆ s := fun x hx => by
      obtain ⟨hxv, hxt⟩ := mem_erase.1 hx
      exact (mem_insert.1 (ht hxt)).resolve_left hxv
    obtain ⟨u, hu, hsu⟩ := hs ht'
    obtain ⟨hu𝓕, hvu, heu⟩ := (mem_filter.1 hu).2
    by_cases hvt : v ∈ t
    · exact ⟨u, hu𝓕, by rw [insert_inter_of_mem hvu, hsu, insert_erase hvt]⟩
    · refine ⟨u.erase v, heu, ?_⟩
      have h1 : s ∩ u.erase v = s ∩ u := by
        ext x
        simp only [mem_inter, mem_erase]
        exact ⟨fun ⟨hx, _, hxu⟩ => ⟨hx, hxu⟩,
          fun ⟨hx, hxu⟩ => ⟨hx, fun hxv => hv (hxv ▸ hx), hxu⟩⟩
      rw [insert_inter_of_notMem (notMem_erase v u), h1, hsu,
        erase_eq_of_notMem hvt]
  have hd : 𝓟.vcDim = #s := hcard
  have := hshat.card_le_vcDim
  rw [card_insert_of_notMem hv] at this
  omega

/-- Lemma 7 of DMMPT26 (negative half): the `v`-negative members form a
family of strictly smaller VC dimension. -/
theorem vcDim_filter_vNeg_lt (h : (𝓕.filter (VNeg 𝓕 v)).Nonempty) :
    (𝓕.filter (VNeg 𝓕 v)).vcDim < 𝓕.vcDim := by
  set 𝓝 := 𝓕.filter (VNeg 𝓕 v) with h𝓝
  obtain ⟨s, hs, hcard⟩ :=
    Finset.exists_mem_eq_sup 𝓝.shatterer
      ⟨∅, mem_shatterer.2 (shatters_empty.2 h)⟩ card
  rw [mem_shatterer] at hs
  have hv : v ∉ s := by
    intro hvs
    obtain ⟨u, hu, hsu⟩ := hs Subset.rfl
    exact ((mem_filter.1 hu).2).2.1 (inter_eq_left.1 hsu hvs)
  have hshat : 𝓕.Shatters (insert v s) := by
    intro t ht
    have ht' : t.erase v ⊆ s := fun x hx => by
      obtain ⟨hxv, hxt⟩ := mem_erase.1 hx
      exact (mem_insert.1 (ht hxt)).resolve_left hxv
    obtain ⟨u, hu, hsu⟩ := hs ht'
    obtain ⟨hu𝓕, hvu, hiu⟩ := (mem_filter.1 hu).2
    by_cases hvt : v ∈ t
    · refine ⟨insert v u, hiu, ?_⟩
      have h1 : s ∩ insert v u = s ∩ u := by
        ext x
        simp only [mem_inter, mem_insert]
        exact ⟨fun ⟨hx, hxu⟩ => ⟨hx, hxu.resolve_left fun hxv => hv (hxv ▸ hx)⟩,
          fun ⟨hx, hxu⟩ => ⟨hx, Or.inr hxu⟩⟩
      rw [insert_inter_of_mem (mem_insert_self v u), h1, hsu, insert_erase hvt]
    · exact ⟨u, hu𝓕, by
        rw [insert_inter_of_notMem hvu, hsu, erase_eq_of_notMem hvt]⟩
  have hd : 𝓝.vcDim = #s := hcard
  have := hshat.card_le_vcDim
  rw [card_insert_of_notMem hv] at this
  omega

/-- Lemma 8 of DMMPT26 (Haussler–Littlestone–Warmuth packing): the
Hamming graph of a family of VC dimension `d` has at most `d` times as
many edges as the family has members. -/
theorem hammingEdgeCount_le_vcDim_mul_card (𝓕 : Finset (Finset α)) :
    hammingEdgeCount 𝓕 ≤ 𝓕.vcDim * 𝓕.card := by
  sorry

/-- Corollary 9 of DMMPT26: the Hamming edges of `𝓕` are supported on
the non-isolated members, so a family of VC dimension `d` with `m`
Hamming edges has at least `m / d` non-isolated members. -/
theorem hammingEdgeCount_le_vcDim_mul_card_nonIsolated
    (𝓕 : Finset (Finset α)) :
    hammingEdgeCount 𝓕 ≤ 𝓕.vcDim * (nonIsolated 𝓕).card := by
  have hsub : nonIsolated 𝓕 ⊆ 𝓕 := filter_subset _ _
  have hpairs : posPairs 𝓕 = posPairs (nonIsolated 𝓕) := by
    ext ⟨v, F⟩
    simp only [mem_posPairs]
    constructor
    · rintro ⟨hF, hvF, hFe⟩
      have hvsup : v ∈ 𝓕.sup id := mem_sup.2 ⟨F, hF, hvF⟩
      have hFni : F ∈ nonIsolated 𝓕 :=
        mem_filter.2 ⟨hF, v, hvsup, Or.inl ⟨hF, hvF, hFe⟩⟩
      have hFeni : F.erase v ∈ nonIsolated 𝓕 :=
        mem_filter.2 ⟨hFe, v, hvsup,
          Or.inr ⟨hFe, notMem_erase v F, by rwa [insert_erase hvF]⟩⟩
      exact ⟨hFni, hvF, hFeni⟩
    · rintro ⟨hF, hvF, hFe⟩
      exact ⟨hsub hF, hvF, hsub hFe⟩
  calc hammingEdgeCount 𝓕 = hammingEdgeCount (nonIsolated 𝓕) :=
        congrArg card hpairs
    _ ≤ (nonIsolated 𝓕).vcDim * (nonIsolated 𝓕).card :=
        hammingEdgeCount_le_vcDim_mul_card _
    _ ≤ 𝓕.vcDim * (nonIsolated 𝓕).card :=
        Nat.mul_le_mul_right _ (vcDim_mono hsub)

/-- Restricting a family to a subset of the ground set cannot increase
its VC dimension. -/
theorem vcDim_image_inter_le (𝓕 : Finset (Finset α)) (X : Finset α) :
    (𝓕.image (· ∩ X)).vcDim ≤ 𝓕.vcDim := by
  show (𝓕.image (· ∩ X)).shatterer.sup card ≤ _
  apply Finset.sup_le
  intro s hs
  rw [mem_shatterer] at hs
  obtain ⟨u, hu, hsu⟩ := hs.exists_superset
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hu
  have hsX : s ⊆ X := hsu.trans inter_subset_right
  have hshat : 𝓕.Shatters s := by
    intro t ht
    obtain ⟨u', hu', hsu'⟩ := hs ht
    obtain ⟨w', hw', rfl⟩ := mem_image.1 hu'
    refine ⟨w', hw', ?_⟩
    rw [show s ∩ w' = s ∩ (w' ∩ X) by
      rw [inter_comm w' X, ← inter_assoc, inter_eq_left.2 hsX], hsu']
  exact hshat.card_le_vcDim

/-- A family of VC dimension `0` has at most one member. -/
theorem card_le_one_of_vcDim_eq_zero (h : 𝓕.vcDim = 0) : 𝓕.card ≤ 1 := by
  by_contra hcard
  push Not at hcard
  obtain ⟨F, hF, F', hF', hne⟩ := Finset.one_lt_card.1 hcard
  have hns : ¬(F ⊆ F' ∧ F' ⊆ F) := fun ⟨h1, h2⟩ => hne (Subset.antisymm h1 h2)
  rw [not_and_or] at hns
  obtain ⟨w, W, hW, W', hW', hwW, hwW'⟩ :
      ∃ w, ∃ W ∈ 𝓕, ∃ W' ∈ 𝓕, w ∈ W ∧ w ∉ W' := by
    rcases hns with h' | h'
    · obtain ⟨w, hwF, hwF'⟩ := Finset.not_subset.1 h'
      exact ⟨w, F, hF, F', hF', hwF, hwF'⟩
    · obtain ⟨w, hwF', hwF⟩ := Finset.not_subset.1 h'
      exact ⟨w, F', hF', F, hF, hwF', hwF⟩
  have hshat : 𝓕.Shatters {w} := by
    intro t ht
    rcases Finset.subset_singleton_iff.1 ht with rfl | rfl
    · exact ⟨W', hW', by rw [singleton_inter_of_notMem hwW']⟩
    · exact ⟨W, hW, by rw [singleton_inter_of_mem hwW]⟩
  have := hshat.card_le_vcDim
  rw [card_singleton, h] at this
  omega

/-- Lemma 19 of DMMPT26: an indexed family of set systems on `A` with
total size exceeding twice the number of indices admits a restriction
`X ⊆ A` on which the total number of Hamming edges is at least the
total size divided by `2 ln |A| + 2`. Deletion process driven by a
harmonic-number potential. -/
theorem exists_subset_hamming_dense {ι : Type*} (I : Finset ι)
    (𝓕 : ι → Finset (Finset α)) (A : Finset α)
    (hground : ∀ i ∈ I, ∀ F ∈ 𝓕 i, F ⊆ A) (hA : 1 < A.card)
    (hm : 2 * I.card < ∑ i ∈ I, (𝓕 i).card) :
    ∃ X ⊆ A,
      (∑ i ∈ I, ((𝓕 i).card : ℝ)) ≤ (2 * Real.log A.card + 2) *
        ∑ i ∈ I, (hammingEdgeCount ((𝓕 i).image (· ∩ X)) : ℝ) := by
  sorry

end Lax5Proofs.SetSystems
