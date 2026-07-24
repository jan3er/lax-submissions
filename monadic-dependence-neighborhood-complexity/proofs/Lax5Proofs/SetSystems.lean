import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

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

/-- Removing the element `v` from the ground set merges exactly the
`v`-pairs: the size of the erase-`v` image plus the number of
`v`-positive members recovers the size of the family. -/
theorem card_image_erase_add_card_vPos (𝓖 : Finset (Finset α)) (v : α) :
    (𝓖.image (·.erase v)).card + (𝓖.filter (VPos 𝓖 v)).card =
      𝓖.card := by
  classical
  set Q := 𝓖.filter (fun F => ¬ VPos 𝓖 v F) with hQ
  have himg : 𝓖.image (·.erase v) = Q.image (·.erase v) := by
    apply Finset.Subset.antisymm
    · intro E hE
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hE
      by_cases hFP : VPos 𝓖 v F
      · refine Finset.mem_image.2 ⟨F.erase v,
          Finset.mem_filter.2 ⟨hFP.2.2, ?_⟩, erase_idem⟩
        rintro ⟨-, hv, -⟩
        exact notMem_erase v F hv
      · exact Finset.mem_image.2 ⟨F, Finset.mem_filter.2 ⟨hF, hFP⟩, rfl⟩
    · exact Finset.image_subset_image (Finset.filter_subset _ _)
  have hinj : Set.InjOn (fun F : Finset α => F.erase v)
      (Q : Set (Finset α)) := by
    intro F hF F' hF' h
    replace h : F.erase v = F'.erase v := h
    obtain ⟨hF𝓖, hFnp⟩ := Finset.mem_filter.1 hF
    obtain ⟨hF'𝓖, hF'np⟩ := Finset.mem_filter.1 hF'
    by_cases hvF : v ∈ F <;> by_cases hvF' : v ∈ F'
    · rw [← Finset.insert_erase hvF, h, Finset.insert_erase hvF']
    · exact absurd ⟨hF𝓖, hvF,
        by rw [h, Finset.erase_eq_of_notMem hvF']; exact hF'𝓖⟩ hFnp
    · exact absurd ⟨hF'𝓖, hvF',
        by rw [← h, Finset.erase_eq_of_notMem hvF]; exact hF𝓖⟩ hF'np
    · rw [← Finset.erase_eq_of_notMem hvF, h, Finset.erase_eq_of_notMem hvF']
  rw [himg, Finset.card_image_of_injOn hinj, add_comm]
  exact Finset.card_filter_add_card_filter_not (s := 𝓖) _

/-- The Hamming edges of a family with ground set inside `X`, counted
coordinatewise over `X`. -/
theorem sum_card_vPos_filter_eq (𝓖 : Finset (Finset α)) (X : Finset α)
    (h : ∀ F ∈ 𝓖, F ⊆ X) :
    ∑ v ∈ X, (𝓖.filter (VPos 𝓖 v)).card = hammingEdgeCount 𝓖 := by
  classical
  have hpp : posPairs 𝓖 =
      X.biUnion fun v => (𝓖.filter (VPos 𝓖 v)).image (Prod.mk v) := by
    ext ⟨w, F⟩
    simp only [mem_posPairs, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter, Prod.mk.injEq]
    constructor
    · intro hvp
      exact ⟨w, h F hvp.1 hvp.2.1, F, ⟨hvp.1, hvp⟩, rfl, rfl⟩
    · rintro ⟨v, hvX, F', ⟨hF', hvp⟩, rfl, rfl⟩
      exact hvp
  rw [hammingEdgeCount, hpp, Finset.card_biUnion]
  · exact (Finset.sum_congr rfl fun v _ =>
      Finset.card_image_of_injective _ fun a b hab =>
        congrArg Prod.snd hab).symm
  · intro v _ w _ hvw
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨a, F⟩ ha hb
    obtain ⟨F₁, -, h₁⟩ := Finset.mem_image.1 ha
    obtain ⟨F₂, -, h₂⟩ := Finset.mem_image.1 hb
    exact hvw ((congrArg Prod.fst h₁).trans (congrArg Prod.fst h₂).symm)

/-- Lemma 8 of DMMPT26 (Haussler–Littlestone–Warmuth packing): the
Hamming graph of a family of VC dimension `d` has at most `d` times as
many edges as the family has members.

Induction on the ground set. Fixing `v`, the `v`-edges are counted by
the `v`-negative members `Nn` (one per `v`-pair); the remaining edges
inject into the edges of the erase-`v` projection `𝓖₀` plus those of
`Nn` (an edge of the projection is hit twice exactly when both lifts
are edges, and then it is an edge of `Nn`). Lemma 7 drops the VC
dimension of `Nn`, so induction gives
`E ≤ |Nn| + d·|𝓖₀| + (d−1)·|Nn| = d·|𝓖|`. -/
theorem hammingEdgeCount_le_vcDim_mul_card (𝓕 : Finset (Finset α)) :
    hammingEdgeCount 𝓕 ≤ 𝓕.vcDim * 𝓕.card := by
  classical
  suffices h : ∀ (N : ℕ) (𝓖 : Finset (Finset α)), (𝓖.sup id).card ≤ N →
      hammingEdgeCount 𝓖 ≤ 𝓖.vcDim * 𝓖.card from h _ 𝓕 le_rfl
  intro N
  induction N with
  | zero =>
    intro 𝓖 h0
    have hsup : 𝓖.sup id = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 h0)
    have hpp : posPairs 𝓖 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨w, F⟩ hp
      have hm := mem_posPairs.1 hp
      have hw : w ∈ 𝓖.sup id := Finset.mem_sup.2 ⟨F, hm.1, hm.2.1⟩
      simp [hsup] at hw
    simp [hammingEdgeCount, hpp]
  | succ N ih =>
    intro 𝓖 hcard
    rcases (𝓖.sup id).eq_empty_or_nonempty with hsup | ⟨v, hv⟩
    · have hpp : posPairs 𝓖 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        rintro ⟨w, F⟩ hp
        have hm := mem_posPairs.1 hp
        have hw : w ∈ 𝓖.sup id := Finset.mem_sup.2 ⟨F, hm.1, hm.2.1⟩
        simp [hsup] at hw
      simp [hammingEdgeCount, hpp]
    set d := 𝓖.vcDim with hd
    set P := 𝓖.filter (VPos 𝓖 v) with hP
    set Nn := 𝓖.filter (VNeg 𝓖 v) with hNn
    set 𝓖₀ := 𝓖.image (·.erase v) with h𝓖₀
    have hsub𝓖 : ∀ F ∈ 𝓖, F ⊆ 𝓖.sup id := fun F hF =>
      Finset.le_sup (f := id) hF
    -- ground sets shrink, so the induction hypothesis applies
    have hsup₀ : 𝓖₀.sup id ≤ (𝓖.sup id).erase v := by
      refine Finset.sup_le fun G hG => ?_
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hG
      exact Finset.erase_subset_erase v (hsub𝓖 F hF)
    have hsupN : Nn.sup id ≤ (𝓖.sup id).erase v := by
      refine Finset.sup_le fun G hG => ?_
      obtain ⟨hG𝓖, hGneg⟩ := Finset.mem_filter.1 hG
      exact Finset.subset_erase.2 ⟨hsub𝓖 G hG𝓖, hGneg.2.1⟩
    have hle : ((𝓖.sup id).erase v).card ≤ N := by
      rw [Finset.card_erase_of_mem hv]
      have : 1 ≤ (𝓖.sup id).card := Finset.card_pos.2 ⟨v, hv⟩
      omega
    have ih₀ := ih 𝓖₀ (le_trans (Finset.card_le_card hsup₀) hle)
    have ihN := ih Nn (le_trans (Finset.card_le_card hsupN) hle)
    -- projection does not raise the VC dimension
    have hvc₀ : 𝓖₀.vcDim ≤ d := by
      have himg : 𝓖₀ = 𝓖.image (· ∩ (𝓖.sup id).erase v) := by
        rw [h𝓖₀]
        refine Finset.image_congr fun F hF => ?_
        rw [Finset.inter_erase,
          Finset.inter_eq_left.2 (hsub𝓖 F (Finset.mem_coe.1 hF))]
      calc 𝓖₀.vcDim = (𝓖.image (· ∩ (𝓖.sup id).erase v)).vcDim := by
            rw [← himg]
        _ ≤ 𝓖.vcDim := vcDim_image_inter_le _ _
    -- the `v`-pairs, counted from either side
    have hPN : P.card = Nn.card := by
      refine Finset.card_bij' (fun F _ => F.erase v) (fun G _ => insert v G)
        ?_ ?_ ?_ ?_
      · intro F hF
        obtain ⟨hF𝓖, hFpos⟩ := Finset.mem_filter.1 hF
        refine Finset.mem_filter.2 ⟨hFpos.2.2, hFpos.2.2,
          notMem_erase v F, ?_⟩
        rw [Finset.insert_erase hFpos.2.1]
        exact hF𝓖
      · intro G hG
        obtain ⟨hG𝓖, hGneg⟩ := Finset.mem_filter.1 hG
        refine Finset.mem_filter.2 ⟨hGneg.2.2, hGneg.2.2,
          Finset.mem_insert_self v G, ?_⟩
        rw [Finset.erase_insert hGneg.2.1]
        exact hG𝓖
      · intro F hF
        exact Finset.insert_erase ((Finset.mem_filter.1 hF).2.2.1)
      · intro G hG
        exact Finset.erase_insert ((Finset.mem_filter.1 hG).2.2.1)
    -- edges at coordinate `v`
    have hedgev : ((posPairs 𝓖).filter fun p => p.1 = v).card = P.card := by
      refine Finset.card_bij' (fun p _ => p.2) (fun F _ => (v, F))
        ?_ ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpp, hpv⟩ := Finset.mem_filter.1 hp
        have hm := mem_posPairs.1 hpp
        rw [hpv] at hm
        exact Finset.mem_filter.2 ⟨hm.1, hm⟩
      · intro F hF
        exact Finset.mem_filter.2
          ⟨mem_posPairs.2 (Finset.mem_filter.1 hF).2, rfl⟩
      · intro p hp
        obtain ⟨-, hpv⟩ := Finset.mem_filter.1 hp
        exact Prod.ext hpv.symm rfl
      · intro F _
        rfl
    -- the remaining edges inject into edges of `𝓖₀` plus edges of `Nn`
    have hrest : ((posPairs 𝓖).filter fun p => ¬ p.1 = v).card ≤
        hammingEdgeCount 𝓖₀ + hammingEdgeCount Nn := by
      rw [hammingEdgeCount, hammingEdgeCount, ← Finset.card_disjSum]
      refine Finset.card_le_card_of_injOn
        (fun p => if v ∈ p.2 ∧ p.2.erase v ∈ 𝓖 ∧ (p.2.erase p.1).erase v ∈ 𝓖
          then Sum.inr (p.1, p.2.erase v) else Sum.inl (p.1, p.2.erase v))
        ?_ ?_
      · intro p hp
        obtain ⟨hpp, hpv⟩ := Finset.mem_filter.1 hp
        obtain ⟨hF𝓖, hwF, hFw⟩ := mem_posPairs.1 hpp
        dsimp only
        by_cases hC : v ∈ p.2 ∧ p.2.erase v ∈ 𝓖 ∧
            (p.2.erase p.1).erase v ∈ 𝓖
        · rw [if_pos hC]
          apply Finset.inr_mem_disjSum.2
          rw [mem_posPairs]
          refine ⟨?_, Finset.mem_erase.2 ⟨hpv, hwF⟩, ?_⟩
          · refine Finset.mem_filter.2 ⟨hC.2.1, hC.2.1,
              notMem_erase v p.2, ?_⟩
            rw [Finset.insert_erase hC.1]
            exact hF𝓖
          · rw [Finset.erase_right_comm]
            refine Finset.mem_filter.2 ⟨hC.2.2, hC.2.2,
              notMem_erase v _, ?_⟩
            rw [Finset.insert_erase
              (Finset.mem_erase.2 ⟨fun h => hpv h.symm, hC.1⟩)]
            exact hFw
        · rw [if_neg hC]
          apply Finset.inl_mem_disjSum.2
          rw [mem_posPairs]
          refine ⟨Finset.mem_image_of_mem _ hF𝓖,
            Finset.mem_erase.2 ⟨hpv, hwF⟩, ?_⟩
          rw [Finset.erase_right_comm]
          exact Finset.mem_image_of_mem _ hFw
      · intro p hp q hq hpq
        simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
        obtain ⟨hpp, hpv⟩ := hp
        obtain ⟨hqp, hqv⟩ := hq
        obtain ⟨hpF, hpw, hpFw⟩ := mem_posPairs.1 hpp
        obtain ⟨hqF, hqw, hqFw⟩ := mem_posPairs.1 hqp
        dsimp only at hpq
        by_cases hCp : v ∈ p.2 ∧ p.2.erase v ∈ 𝓖 ∧
            (p.2.erase p.1).erase v ∈ 𝓖 <;>
          by_cases hCq : v ∈ q.2 ∧ q.2.erase v ∈ 𝓖 ∧
              (q.2.erase q.1).erase v ∈ 𝓖
        · rw [if_pos hCp, if_pos hCq] at hpq
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hpq
          obtain ⟨h1, h2⟩ := hpq
          have h3 : p.2 = q.2 := by
            rw [← Finset.insert_erase hCp.1, h2, Finset.insert_erase hCq.1]
          exact Prod.ext h1 h3
        · rw [if_pos hCp, if_neg hCq] at hpq
          exact absurd hpq (by simp)
        · rw [if_neg hCp, if_pos hCq] at hpq
          exact absurd hpq (by simp)
        · rw [if_neg hCp, if_neg hCq] at hpq
          simp only [Sum.inl.injEq, Prod.mk.injEq] at hpq
          obtain ⟨h1, h2⟩ := hpq
          by_cases hvp : v ∈ p.2 <;> by_cases hvq : v ∈ q.2
          · exact Prod.ext h1 (by
              rw [← Finset.insert_erase hvp, h2, Finset.insert_erase hvq])
          · refine absurd ⟨hvp, ?_, ?_⟩ hCp
            · rw [h2, Finset.erase_eq_of_notMem hvq]
              exact hqF
            · rw [Finset.erase_right_comm, h2, Finset.erase_eq_of_notMem hvq, h1]
              exact hqFw
          · refine absurd ⟨hvq, ?_, ?_⟩ hCq
            · rw [← h2, Finset.erase_eq_of_notMem hvp]
              exact hpF
            · rw [Finset.erase_right_comm, ← h2,
                Finset.erase_eq_of_notMem hvp, ← h1]
              exact hpFw
          · exact Prod.ext h1 (by
              rw [← Finset.erase_eq_of_notMem hvp, h2,
                Finset.erase_eq_of_notMem hvq])
    -- assemble
    have hsplit_edges := Finset.card_filter_add_card_filter_not
      (s := posPairs 𝓖) fun p => p.1 = v
    have hsplit𝓖 := card_image_erase_add_card_vPos 𝓖 v
    rw [← h𝓖₀, ← hP] at hsplit𝓖
    have ih₀le : hammingEdgeCount 𝓖₀ ≤ d * 𝓖₀.card :=
      le_trans ih₀ (Nat.mul_le_mul_right _ hvc₀)
    rcases Nn.eq_empty_or_nonempty with hNe | hNne
    · have hP0 : P.card = 0 := by rw [hPN, hNe, Finset.card_empty]
      have hhNn : hammingEdgeCount Nn = 0 := by
        have hppN : posPairs Nn = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          rintro ⟨w, F⟩ hp
          have hm := mem_posPairs.1 hp
          rw [hNe] at hm
          exact absurd hm.1 (Finset.notMem_empty F)
        rw [hammingEdgeCount, hppN, Finset.card_empty]
      have hcards : 𝓖₀.card = 𝓖.card := by omega
      calc hammingEdgeCount 𝓖
          = ((posPairs 𝓖).filter fun p => p.1 = v).card +
            ((posPairs 𝓖).filter fun p => ¬ p.1 = v).card :=
            hsplit_edges.symm
        _ ≤ P.card + (hammingEdgeCount 𝓖₀ + hammingEdgeCount Nn) := by
            rw [hedgev]
            exact Nat.add_le_add_left hrest _
        _ = hammingEdgeCount 𝓖₀ := by omega
        _ ≤ d * 𝓖₀.card := ih₀le
        _ = d * 𝓖.card := by rw [hcards]
    · have hvclt := vcDim_filter_vNeg_lt (𝓕 := 𝓖) (v := v) hNne
      rw [← hNn, ← hd] at hvclt
      obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      have ihNle : hammingEdgeCount Nn ≤ d' * Nn.card :=
        le_trans ihN (Nat.mul_le_mul_right _ (by omega))
      calc hammingEdgeCount 𝓖
          = ((posPairs 𝓖).filter fun p => p.1 = v).card +
            ((posPairs 𝓖).filter fun p => ¬ p.1 = v).card :=
            hsplit_edges.symm
        _ ≤ P.card + (hammingEdgeCount 𝓖₀ + hammingEdgeCount Nn) := by
            rw [hedgev]
            exact Nat.add_le_add_left hrest _
        _ ≤ Nn.card + (d * 𝓖₀.card + d' * Nn.card) := by
            rw [hPN]
            exact Nat.add_le_add_left (Nat.add_le_add ih₀le ihNle) _
        _ = d * 𝓖₀.card + d * Nn.card := by
            rw [hd']
            ring
        _ = d * (𝓖₀.card + P.card) := by
            rw [hPN]
            ring
        _ = d * 𝓖.card := by rw [hsplit𝓖]

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
  classical
  set m : ℕ := ∑ i ∈ I, (𝓕 i).card with hm_def
  set H : ℝ := (harmonic A.card : ℝ) with hH
  have hHpos : 0 < H := by
    rw [hH]
    have hq : (0 : ℚ) < harmonic A.card := by
      unfold harmonic
      refine Finset.sum_pos (fun i _ => by positivity)
        (Finset.nonempty_range_iff.2 (by omega))
    exact_mod_cast hq
  set μ : Finset α → ℕ := fun X => ∑ i ∈ I, ((𝓕 i).image (· ∩ X)).card
    with hμ
  -- one deletion step: `μ` drops by exactly the `v`-positive count
  have hdropId : ∀ (X : Finset α) (v : α),
      μ (X.erase v) + (∑ i ∈ I, (((𝓕 i).image (· ∩ X)).filter
        (VPos ((𝓕 i).image (· ∩ X)) v)).card) = μ X := by
    intro X v
    rw [hμ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have himg : (𝓕 i).image (· ∩ X.erase v) =
        ((𝓕 i).image (· ∩ X)).image (·.erase v) := by
      rw [Finset.image_image]
      exact Finset.image_congr fun F _ => by
        simp only [Function.comp_apply]
        exact Finset.inter_erase v F X
    rw [himg]
    exact card_image_erase_add_card_vPos _ v
  -- empty restriction: at most one trace per index
  have hμempty : (μ ∅ : ℝ) ≤ I.card := by
    rw [hμ]
    push_cast
    calc ∑ i ∈ I, (((𝓕 i).image (· ∩ ∅)).card : ℝ)
        ≤ ∑ _i ∈ I, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have : (𝓕 i).image (· ∩ ∅) ⊆ {∅} := fun E hE => by
            obtain ⟨F, _, rfl⟩ := Finset.mem_image.1 hE
            simp
          exact_mod_cast Finset.card_le_card this |>.trans (by simp)
      _ = I.card := by simp
  -- the deletion process, as downward induction on `|X|`
  have main : ∀ (N : ℕ) (X : Finset α), X.card ≤ N → X ⊆ A →
      (m : ℝ) / 2 + m / (2 * H) * (harmonic X.card : ℝ) ≤ (μ X : ℝ) →
      ∃ X' ⊆ A, (m : ℝ) ≤ (2 * Real.log A.card + 2) *
        ∑ i ∈ I, (hammingEdgeCount ((𝓕 i).image (· ∩ X')) : ℝ) := by
    intro N
    induction N with
    | zero =>
      intro X hcard hXA hinv
      exfalso
      obtain rfl : X = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
      simp only [Finset.card_empty, harmonic_zero, Rat.cast_zero,
        mul_zero, add_zero] at hinv
      have h2m : (I.card : ℝ) < (m : ℝ) / 2 := by
        have : (2 * I.card : ℝ) < m := by exact_mod_cast hm
        linarith
      linarith [hμempty.trans h2m.le, hinv]
    | succ N ih =>
      intro X hcard hXA hinv
      rcases Finset.eq_empty_or_nonempty X with rfl | hXne
      · exfalso
        simp only [Finset.card_empty, harmonic_zero, Rat.cast_zero,
          mul_zero, add_zero] at hinv
        have h2m : (I.card : ℝ) < (m : ℝ) / 2 := by
          have : (2 * I.card : ℝ) < m := by exact_mod_cast hm
          linarith
        linarith [hμempty.trans h2m.le, hinv]
      have hcpos : 0 < X.card := hXne.card_pos
      have hcR : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hcpos
      by_cases hrem : ∃ v ∈ X,
          ((∑ i ∈ I, (((𝓕 i).image (· ∩ X)).filter
            (VPos ((𝓕 i).image (· ∩ X)) v)).card : ℕ) : ℝ) ≤
            m / (2 * H * X.card)
      · obtain ⟨v, hvX, hdrop⟩ := hrem
        refine ih (X.erase v) ?_ ((Finset.erase_subset _ _).trans hXA) ?_
        · rw [Finset.card_erase_of_mem hvX]
          omega
        · obtain ⟨c', hc'⟩ : ∃ c', X.card = c' + 1 :=
            ⟨X.card - 1, by omega⟩
          have hharm : (harmonic X.card : ℝ) =
              (harmonic (X.erase v).card : ℝ) + 1 / (X.card : ℝ) := by
            rw [Finset.card_erase_of_mem hvX, hc']
            push_cast [harmonic_succ]
            ring
          have hμX : (μ (X.erase v) : ℝ) = (μ X : ℝ) -
              ((∑ i ∈ I, (((𝓕 i).image (· ∩ X)).filter
                (VPos ((𝓕 i).image (· ∩ X)) v)).card : ℕ) : ℝ) := by
            have h := hdropId X v
            have hcast : ((μ (X.erase v) : ℕ) : ℝ) +
                ((∑ i ∈ I, (((𝓕 i).image (· ∩ X)).filter
                  (VPos ((𝓕 i).image (· ∩ X)) v)).card : ℕ) : ℝ) =
                ((μ X : ℕ) : ℝ) := by exact_mod_cast h
            linarith
          have hdiv : (m : ℝ) / (2 * H) * (1 / (X.card : ℝ)) =
              m / (2 * H * X.card) := by
            field_simp
          rw [hharm, mul_add, hdiv] at hinv
          rw [hμX]
          linarith [hdrop]
      · push Not at hrem
        refine ⟨X, hXA, ?_⟩
        have hedge : ∀ i ∈ I, ∀ F ∈ (𝓕 i).image (· ∩ X), F ⊆ X := by
          intro i _ F hF
          obtain ⟨F', _, rfl⟩ := Finset.mem_image.1 hF
          exact Finset.inter_subset_right
        have hnat : ∑ i ∈ I, hammingEdgeCount ((𝓕 i).image (· ∩ X)) =
            ∑ v ∈ X, ∑ i ∈ I, (((𝓕 i).image (· ∩ X)).filter
              (VPos ((𝓕 i).image (· ∩ X)) v)).card := by
          calc ∑ i ∈ I, hammingEdgeCount ((𝓕 i).image (· ∩ X))
              = ∑ i ∈ I, ∑ v ∈ X, (((𝓕 i).image (· ∩ X)).filter
                  (VPos ((𝓕 i).image (· ∩ X)) v)).card :=
                Finset.sum_congr rfl fun i hi =>
                  (sum_card_vPos_filter_eq _ X (hedge i hi)).symm
            _ = _ := Finset.sum_comm
        have hswap : (∑ i ∈ I,
            (hammingEdgeCount ((𝓕 i).image (· ∩ X)) : ℝ)) =
            ∑ v ∈ X, ((∑ i ∈ I, (((𝓕 i).image (· ∩ X)).filter
              (VPos ((𝓕 i).image (· ∩ X)) v)).card : ℕ) : ℝ) := by
          exact_mod_cast hnat
        have hlower : (m : ℝ) / (2 * H) <
            ∑ i ∈ I, (hammingEdgeCount ((𝓕 i).image (· ∩ X)) : ℝ) := by
          rw [hswap]
          calc (m : ℝ) / (2 * H)
              = ∑ _v ∈ X, (m : ℝ) / (2 * H * X.card) := by
                rw [Finset.sum_const, nsmul_eq_mul]
                field_simp
            _ < _ := Finset.sum_lt_sum_of_nonempty hXne
                fun v hv => hrem v hv
        have hHle : 2 * H ≤ 2 * Real.log A.card + 2 := by
          have := harmonic_le_one_add_log A.card
          rw [hH]
          linarith
        have hEnn : (0 : ℝ) ≤
            ∑ i ∈ I, (hammingEdgeCount ((𝓕 i).image (· ∩ X)) : ℝ) :=
          Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
        have h2H : (m : ℝ) ≤ 2 * H *
            ∑ i ∈ I, (hammingEdgeCount ((𝓕 i).image (· ∩ X)) : ℝ) := by
          rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * H)] at hlower
          nlinarith
        calc (m : ℝ)
            ≤ 2 * H * ∑ i ∈ I,
              (hammingEdgeCount ((𝓕 i).image (· ∩ X)) : ℝ) := h2H
          _ ≤ (2 * Real.log A.card + 2) * ∑ i ∈ I,
              (hammingEdgeCount ((𝓕 i).image (· ∩ X)) : ℝ) :=
            mul_le_mul_of_nonneg_right hHle hEnn
  -- kick off at `X = A`
  have hμA : μ A = m := by
    rw [hm_def]
    show ∑ i ∈ I, ((𝓕 i).image (· ∩ A)).card = _
    refine Finset.sum_congr rfl fun i hi => ?_
    have himg : (𝓕 i).image (· ∩ A) = 𝓕 i := by
      calc (𝓕 i).image (· ∩ A) = (𝓕 i).image id :=
          Finset.image_congr fun F hF =>
            Finset.inter_eq_left.2 (hground i hi F hF)
        _ = 𝓕 i := Finset.image_id
    rw [himg]
  have hstart : (m : ℝ) / 2 + m / (2 * H) * (harmonic A.card : ℝ) ≤
      (μ A : ℝ) := by
    have hcast : (μ A : ℝ) = m := by exact_mod_cast congrArg Nat.cast hμA
    rw [hcast, ← hH]
    have hfe : (m : ℝ) / (2 * H) * H = m / 2 := by
      field_simp
    linarith [hfe.le]
  obtain ⟨X', hX'A, hX'⟩ := main A.card A le_rfl (Finset.Subset.refl A) hstart
  refine ⟨X', hX'A, ?_⟩
  have hmS : (∑ i ∈ I, ((𝓕 i).card : ℝ)) = (m : ℝ) := by
    rw [hm_def]
    norm_cast
  rw [hmS]
  exact hX'

end Lax5Proofs.SetSystems
