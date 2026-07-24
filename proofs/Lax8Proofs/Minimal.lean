import Lax8Proofs.MergeWidthBasic

/-!
# Minimal merge sequences and Lemma 2.1

A merge sequence is **minimal** if its resolved sets cannot be shrunk (keeping the
same partitions) while remaining a valid merge sequence.  Every merge sequence
can be shrunk to a minimal one without increasing its width.  Minimal sequences
satisfy the key transfer property (Lemma 2.1): two unresolved pairs between the
same two parts are resolved at exactly the same later steps.
-/

namespace Lax8Proofs

open Lax8.MergeWidth

open scoped Classical

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- $S$ is **minimal** if any monotone, uniform family of resolved graphs $R'$
below $S.resolved$ (for the same partitions) is in fact equal to $S.resolved$. -/
def Minimal (S : MergeSeq G) : Prop :=
  ∀ (R' : ℕ → SimpleGraph V),
    (∀ i, R' i ≤ S.resolved i) →
    (∀ ⦃i j⦄, 1 ≤ i → i ≤ j → j ≤ S.length → R' i ≤ R' j) →
    (∀ ⦃i⦄, 1 ≤ i → i ≤ S.length → ∀ ⦃x x' y y' : V⦄,
      (S.part i).r x x' → (S.part i).r y y' → x ≠ y → x' ≠ y' →
      ¬ (R' i).Adj x y → ¬ (R' i).Adj x' y' → (G.Adj x y ↔ G.Adj x' y')) →
    ∀ i, 1 ≤ i → i ≤ S.length → S.resolved i ≤ R' i

/-! ### Deleting a single edge on a window of steps (for Lemma 2.1) -/

open Classical in
/-- Delete the single unordered edge $x₁y₁$ from $S$ when $keep$ holds. -/
noncomputable def delEdge (S : SimpleGraph V) (x₁ y₁ : V) (keep : Prop) : SimpleGraph V :=
  if keep then S.deleteEdges {s(x₁, y₁)} else S

omit [Fintype V] in
@[simp] theorem delEdge_adj (S : SimpleGraph V) (x₁ y₁ : V) (keep : Prop) (a b : V) :
    (delEdge S x₁ y₁ keep).Adj a b ↔ S.Adj a b ∧ ¬ (keep ∧ s(a, b) = s(x₁, y₁)) := by
  classical
  unfold delEdge
  by_cases h : keep
  · simp [h, SimpleGraph.deleteEdges_adj]
  · simp [h]

/-- The resolved family of $S$ with the single edge $x₁y₁$ deleted on the window
$i < ℓ ≤ j$. -/
noncomputable def delRes (S : MergeSeq G) (x₁ y₁ : V) (i j ℓ : ℕ) : SimpleGraph V :=
  delEdge (S.resolved ℓ) x₁ y₁ (i < ℓ ∧ ℓ ≤ j)

omit [Fintype V] in
theorem delRes_adj (S : MergeSeq G) (x₁ y₁ : V) (i j ℓ : ℕ) (a b : V) :
    (delRes S x₁ y₁ i j ℓ).Adj a b ↔
      (S.resolved ℓ).Adj a b ∧ ¬ ((i < ℓ ∧ ℓ ≤ j) ∧ s(a, b) = s(x₁, y₁)) := by
  rw [delRes, delEdge_adj]

omit [Fintype V] in
theorem delRes_le (S : MergeSeq G) (x₁ y₁ : V) (i j ℓ : ℕ) :
    delRes S x₁ y₁ i j ℓ ≤ S.resolved ℓ := by
  intro a b h; rw [delRes_adj] at h; exact h.1

omit [Fintype V] in
/-- The deleted family is still monotone. -/
theorem delRes_mono (S : MergeSeq G) {i j : ℕ} {x₁ y₁ : V}
    (hilen : i ≤ S.length) (hnr₁ : ¬ (S.resolved i).Adj x₁ y₁) :
    ∀ ⦃a b⦄, 1 ≤ a → a ≤ b → b ≤ S.length →
      delRes S x₁ y₁ i j a ≤ delRes S x₁ y₁ i j b := by
  intro a b ha hab hblen u v h
  rw [delRes_adj] at h ⊢
  refine ⟨S.resolved_mono ha hab hblen h.1, ?_⟩
  rintro ⟨hwinb, hs⟩
  by_cases hia : i < a
  · -- window at $a$ holds too, contradicting $h.2$.
    exact h.2 ⟨⟨hia, le_trans hab hwinb.2⟩, hs⟩
  · -- $a ≤ i$: then $s(u,v) = s(x₁,y₁)$ gives a resolved pair at $i$.
    push_neg at hia
    have hri : (S.resolved i).Adj u v := S.resolved_mono ha hia hilen h.1
    rw [Sym2.eq_iff] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hnr₁ hri
    · exact hnr₁ hri.symm

omit [Fintype V] in
/-- **Cross claim** for Lemma 2.1: at a window step $ℓ$, any cross pair $ab$
(with $a$ in the part of $x₁$ and $b$ in the part of $y₁$) that is unresolved in
the deleted family agrees in $G$-adjacency with $x₁y₁$. -/
theorem delRes_crossClaim (S : MergeSeq G) {i j ℓ : ℕ} (hi : 1 ≤ i) (hiℓ : i ≤ ℓ)
    (hℓj : ℓ ≤ j) (hjlen : j ≤ S.length) {x₁ x₂ y₁ y₂ : V}
    (hx : (S.part i).r x₁ x₂) (hy : (S.part i).r y₁ y₂) (hne₂ : x₂ ≠ y₂)
    (hnr₂j : ¬ (S.resolved j).Adj x₂ y₂) (hGeq : G.Adj x₁ y₁ ↔ G.Adj x₂ y₂)
    {a b : V} (hab : a ≠ b) (harel : (S.part ℓ).r x₁ a) (hbrel : (S.part ℓ).r y₁ b)
    (hunres : ¬ (S.resolved ℓ).Adj a b ∨ s(a, b) = s(x₁, y₁)) :
    (G.Adj a b ↔ G.Adj x₁ y₁) := by
  have hℓlen : ℓ ≤ S.length := le_trans hℓj hjlen
  have h1ℓ : 1 ≤ ℓ := le_trans hi hiℓ
  rcases hunres with hnres | heq
  · have hx2a : (S.part ℓ).r x₂ a :=
      Setoid.trans' _ (Setoid.symm' _ (S.part_mono hi hiℓ hℓlen hx)) harel
    have hy2b : (S.part ℓ).r y₂ b :=
      Setoid.trans' _ (Setoid.symm' _ (S.part_mono hi hiℓ hℓlen hy)) hbrel
    have hnr₂ℓ : ¬ (S.resolved ℓ).Adj x₂ y₂ :=
      fun h => hnr₂j (S.resolved_mono h1ℓ hℓj hjlen h)
    have huni := S.uniform h1ℓ hℓlen hx2a hy2b hne₂ hab hnr₂ℓ hnres
    rw [hGeq]; exact huni.symm
  · rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Iff.rfl
    · exact ⟨fun h => h.symm, fun h => h.symm⟩

omit [Fintype V] in
/-- The deleted family is uniform for $G$ (this is the crux of Lemma 2.1). -/
theorem delRes_uniform (S : MergeSeq G) {i j : ℕ} (hi : 1 ≤ i)
    (hjlen : j ≤ S.length) {x₁ x₂ y₁ y₂ : V}
    (hx : (S.part i).r x₁ x₂) (hy : (S.part i).r y₁ y₂)
    (hne₂ : x₂ ≠ y₂) (hGeq : G.Adj x₁ y₁ ↔ G.Adj x₂ y₂)
    (hnr₂j : ¬ (S.resolved j).Adj x₂ y₂) :
    ∀ ⦃ℓ⦄, 1 ≤ ℓ → ℓ ≤ S.length → ∀ ⦃x x' y y' : V⦄,
      (S.part ℓ).r x x' → (S.part ℓ).r y y' → x ≠ y → x' ≠ y' →
      ¬ (delRes S x₁ y₁ i j ℓ).Adj x y → ¬ (delRes S x₁ y₁ i j ℓ).Adj x' y' →
      (G.Adj x y ↔ G.Adj x' y') := by
  intro ℓ h1ℓ hℓlen x x' y y' hxx' hyy' hxy hx'y' hnxy hnx'y'
  -- Extract "unresolved in $R$" or "deleted edge in window" from $¬ delRes.Adj$.
  have key : ∀ {p q : V}, ¬ (delRes S x₁ y₁ i j ℓ).Adj p q →
      ¬ (S.resolved ℓ).Adj p q ∨ ((i < ℓ ∧ ℓ ≤ j) ∧ s(p, q) = s(x₁, y₁)) := by
    intro p q h
    rw [delRes_adj] at h
    by_cases hr : (S.resolved ℓ).Adj p q
    · exact Or.inr (by by_contra hc; exact h ⟨hr, hc⟩)
    · exact Or.inl hr
  -- A pair equal to $x₁y₁$ agrees with $x₁y₁$ in $G$ (symmetry of $G$).
  have edgeIff : ∀ {p q : V}, s(p, q) = s(x₁, y₁) → (G.Adj p q ↔ G.Adj x₁ y₁) := by
    intro p q h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Iff.rfl
    · exact ⟨fun h => h.symm, fun h => h.symm⟩
  -- A cross pair (either orientation) unresolved-or-deleted agrees with $x₁y₁$.
  have crossPair : ∀ {a b : V}, (i < ℓ ∧ ℓ ≤ j) → a ≠ b →
      (((S.part ℓ).r x₁ a ∧ (S.part ℓ).r y₁ b) ∨
        ((S.part ℓ).r x₁ b ∧ (S.part ℓ).r y₁ a)) →
      (¬ (S.resolved ℓ).Adj a b ∨ s(a, b) = s(x₁, y₁)) →
      (G.Adj a b ↔ G.Adj x₁ y₁) := by
    intro a b hwin hab hor hun
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact delRes_crossClaim S hi (le_of_lt hwin.1) hwin.2 hjlen hx hy hne₂ hnr₂j
        hGeq hab h1 h2 hun
    · have hun' : ¬ (S.resolved ℓ).Adj b a ∨ s(b, a) = s(x₁, y₁) := by
        rcases hun with h | h
        · exact Or.inl (fun hh => h hh.symm)
        · exact Or.inr (by rw [Sym2.eq_swap]; exact h)
      have hres := delRes_crossClaim S hi (le_of_lt hwin.1) hwin.2 hjlen hx hy hne₂
        hnr₂j hGeq (Ne.symm hab) h1 h2 hun'
      exact (Iff.intro (fun h => h.symm) (fun h => h.symm)).trans hres
  rcases key hnxy with hnr_xy | ⟨hwin1, hexy⟩ <;>
    rcases key hnx'y' with hnr_x'y' | ⟨hwin2, hex'y'⟩
  · -- Both unresolved: original uniformity.
    exact S.uniform h1ℓ hℓlen hxx' hyy' hxy hx'y' hnr_xy hnr_x'y'
  · -- $xy$ unresolved, $x'y'$ is the deleted edge.
    have hor_xy : ((S.part ℓ).r x₁ x ∧ (S.part ℓ).r y₁ y) ∨
        ((S.part ℓ).r x₁ y ∧ (S.part ℓ).r y₁ x) := by
      rw [Sym2.eq_iff] at hex'y'
      rcases hex'y' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨Setoid.symm' _ hxx', Setoid.symm' _ hyy'⟩
      · exact Or.inr ⟨Setoid.symm' _ hyy', Setoid.symm' _ hxx'⟩
    exact (crossPair hwin2 hxy hor_xy (Or.inl hnr_xy)).trans (edgeIff hex'y').symm
  · -- $xy$ is the deleted edge, $x'y'$ unresolved.
    have hor_x'y' : ((S.part ℓ).r x₁ x' ∧ (S.part ℓ).r y₁ y') ∨
        ((S.part ℓ).r x₁ y' ∧ (S.part ℓ).r y₁ x') := by
      rw [Sym2.eq_iff] at hexy
      rcases hexy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hxx', hyy'⟩
      · exact Or.inr ⟨hyy', hxx'⟩
    exact (edgeIff hexy).trans (crossPair hwin1 hx'y' hor_x'y' (Or.inl hnr_x'y')).symm
  · -- Both are the deleted edge.
    exact (edgeIff hexy).trans (edgeIff hex'y').symm

omit [Fintype V] in
/-- **Lemma 2.1.** In a minimal merge sequence, if $x₁y₁$ and $x₂y₂$ are two
unresolved pairs between the same two parts $A, B ∈ Pᵢ$ (with $x₂ ≠ y₂$), then
they are resolved at the same later steps: $x₁y₁ ∈ Rⱼ → x₂y₂ ∈ Rⱼ$. -/
theorem lemma21 (S : MergeSeq G) (hmin : Minimal S) {i : ℕ} (hi : 1 ≤ i)
    (hilen : i ≤ S.length) {x₁ x₂ y₁ y₂ : V}
    (hx : (S.part i).r x₁ x₂) (hy : (S.part i).r y₁ y₂) (hne₂ : x₂ ≠ y₂)
    (hnr₁ : ¬ (S.resolved i).Adj x₁ y₁) (hnr₂ : ¬ (S.resolved i).Adj x₂ y₂)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ S.length) (hres₁ : (S.resolved j).Adj x₁ y₁) :
    (S.resolved j).Adj x₂ y₂ := by
  by_contra hcon
  have hne₁ : x₁ ≠ y₁ := hres₁.ne
  -- $j > i$, else $resolved j ≤ resolved i$ contradicts $hnr₁$.
  have hji : i < j := by
    by_contra hle
    push_neg at hle
    exact hnr₁ (S.resolved_mono hj1 hle hilen hres₁)
  have hGeq : G.Adj x₁ y₁ ↔ G.Adj x₂ y₂ :=
    S.uniform hi hilen hx hy hne₁ hne₂ hnr₁ hnr₂
  have hkey := hmin (delRes S x₁ y₁ i j) (delRes_le S x₁ y₁ i j)
    (delRes_mono S hilen hnr₁)
    (delRes_uniform S hi hj hx hy hne₂ hGeq hcon) j (by omega) hj
  have hcontra : (delRes S x₁ y₁ i j j).Adj x₁ y₁ := hkey hres₁
  rw [delRes_adj] at hcontra
  exact hcontra.2 ⟨⟨hji, le_refl j⟩, rfl⟩

/-- Every merge sequence can be replaced by a minimal one with the same
partitions and no larger width. -/
theorem exists_minimal_mergeSeq (S : MergeSeq G) (r : ℕ) :
    ∃ S' : MergeSeq G, Minimal S' ∧ S'.part = S.part ∧ S'.width r ≤ S.width r := by
  suffices H : ∀ N (S : MergeSeq G),
      (∑ i ∈ Finset.Icc 1 S.length, (S.resolved i).edgeFinset.card) = N →
      ∃ S' : MergeSeq G, Minimal S' ∧ S'.part = S.part ∧ S'.width r ≤ S.width r by
    exact H _ S rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro S hN
    by_cases hmin : Minimal S
    · exact ⟨S, hmin, rfl, le_refl _⟩
    · rw [Minimal] at hmin
      push_neg at hmin
      obtain ⟨R', hle, hmono, huniform, i0, hi0, hi0len, hnotle⟩ := hmin
      set S' := Lax8Proofs.MergeSeq.copyResolved S R' hmono huniform with hS'def
      have hne : (R' i0).edgeFinset ≠ (S.resolved i0).edgeFinset := by
        intro heq
        apply hnotle
        intro a b hab
        have hmem : s(a, b) ∈ (S.resolved i0).edgeFinset := by
          rw [SimpleGraph.mem_edgeFinset]; exact hab
        rw [← heq, SimpleGraph.mem_edgeFinset] at hmem
        exact hmem
      have htot : (∑ i ∈ Finset.Icc 1 S'.length, (S'.resolved i).edgeFinset.card) < N := by
        rw [← hN, hS'def]
        simp only [copyResolved_resolved, copyResolved_length]
        apply Finset.sum_lt_sum
        · intro i _
          exact Finset.card_le_card (SimpleGraph.edgeFinset_subset_edgeFinset.2 (hle i))
        · refine ⟨i0, Finset.mem_Icc.mpr ⟨hi0, hi0len⟩, ?_⟩
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeFinset_subset_edgeFinset.2 (hle i0), hne⟩)
      obtain ⟨S0, hmin0, hpart0, hw0⟩ := IH _ htot S' rfl
      refine ⟨S0, hmin0, ?_, le_trans hw0 ?_⟩
      · rw [hpart0, hS'def, copyResolved_part]
      · exact width_copyResolved_le S R' hmono huniform hle r

end Lax8Proofs
