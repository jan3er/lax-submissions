import Lax8Proofs.MergeWidthMono

/-!
# Freezing on maximally `Kt`-free parts (for Lemma 4.3)

The second freezing construction of Bonamy–Geniet: freeze on the inclusion-wise
maximal parts of the merge sequence that are `Kt`-free.  This produces a
partition `Q` of the vertices whose blocks are `Kt`-free.  The within-block
restriction `GI = restrictGraph G Q` therefore has clique number `< t`, and by
`exists_restrict_mergeSeq` still has radius-2 merge-width `≤ k`.
-/

namespace Lax8Proofs

open Lax8.MergeWidth

open scoped Classical
open Finset

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The part of `Pᵢ` containing `v` contains a clique of size `≥ t`. -/
def partHasClique (S : MergeSeq G) (t i : ℕ) (v : V) : Prop :=
  ∃ X : Finset V, t ≤ X.card ∧ G.IsClique (X : Set V) ∧ ∀ x ∈ X, (S.part i).r v x

/-- The **`Kt`-index** of `v`: the largest step at which the part of `v` is
`Kt`-free (no clique of size `≥ t`). -/
noncomputable def idxKt (S : MergeSeq G) (t : ℕ) (v : V) : ℕ :=
  ((Finset.Icc 1 S.length).filter (fun i => ¬ partHasClique S t i v)).sup id

/-- `partHasClique` depends only on the part of `v`. -/
theorem partHasClique_congr (S : MergeSeq G) (t : ℕ) {i : ℕ} {v w : V}
    (h : (S.part i).r v w) : partHasClique S t i v → partHasClique S t i w := by
  rintro ⟨X, hcard, hclique, hmem⟩
  exact ⟨X, hcard, hclique, fun x hx => Setoid.trans' _ (Setoid.symm' _ h) (hmem x hx)⟩

omit [Fintype V] in
/-- A singleton part contains no clique of size `≥ t` when `t ≥ 2`. -/
theorem not_partHasClique_one (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (v : V) :
    ¬ partHasClique S t 1 v := by
  rintro ⟨X, hcard, _, hmem⟩
  have hle : X.card ≤ 1 := by
    have : X ⊆ {v} := fun x hx => by
      have hvx := hmem x hx
      rw [S.part_one] at hvx
      rw [Finset.mem_singleton]
      exact hvx.symm
    exact Finset.card_le_card this
  linarith

/-- For `t ≥ 2`, the `Kt`-index is at least `1`. -/
theorem one_le_idxKt (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (v : V) :
    1 ≤ idxKt S t v := by
  unfold idxKt
  have h1mem : 1 ∈ (Finset.Icc 1 S.length).filter (fun i => ¬ partHasClique S t i v) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_refl 1, S.one_le_length⟩, not_partHasClique_one S ht v⟩
  exact Finset.le_sup (f := id) h1mem

omit [Fintype V] in
/-- The `Kt`-index is at most the length. -/
theorem idxKt_le_length (S : MergeSeq G) (t : ℕ) (v : V) : idxKt S t v ≤ S.length := by
  simp [idxKt]
  tauto

/-- At the `Kt`-index (positive), the part of `v` is `Kt`-free. -/
theorem not_partHasClique_idxKt (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (v : V) :
    ¬ partHasClique S t (idxKt S t v) v := by
  have h : 1 ≤ idxKt S t v := one_le_idxKt S ht v
  unfold idxKt at h ⊢
  have hne : ((Finset.Icc 1 S.length).filter fun i => ¬ partHasClique S t i v) ≠ ∅ := by
    contrapose! h
    simp [h]
  obtain ⟨a, ha, ha'⟩ := Finset.exists_max_image
    ((Finset.Icc 1 S.length).filter fun i => ¬ partHasClique S t i v) id
    (Finset.nonempty_iff_ne_empty.mpr hne)
  have hsup_eq : ((Finset.Icc 1 S.length).filter fun i => ¬ partHasClique S t i v).sup id = a := by
    apply le_antisymm
    · exact Finset.sup_le fun x hx => ha' x hx
    · exact Finset.le_sup (f := id) ha
  rw [hsup_eq]
  exact Finset.mem_filter.mp ha |>.2

omit [Fintype V] in
/-- Beyond the `Kt`-index, the part of `v` has a clique of size `≥ t`. -/
theorem partHasClique_of_gt (S : MergeSeq G) (t : ℕ) {v : V} {j : ℕ}
    (h : idxKt S t v < j) (hj : j ≤ S.length) : partHasClique S t j v := by
  by_contra hcon
  have hj1 : 1 ≤ j := by omega
  have hjmem : j ∈ (Finset.Icc 1 S.length).filter (fun i => ¬ partHasClique S t i v) := by
    simp [hj1, hj, hcon]
  have : idxKt S t v ≥ j := Finset.le_sup (f := id) hjmem
  omega

/-- If `u, v` share a part at step `i = idxKt u`, then `idxKt v = i`. -/
theorem idxKt_eq_of_part_rel (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) {u v : V} {i : ℕ}
    (hi : idxKt S t u = i) (hr : (S.part i).r u v) : idxKt S t v = i := by
  have h1 : 1 ≤ i := hi ▸ one_le_idxKt S ht u
  have hfree_u : ¬ partHasClique S t i u := by rw [← hi]; exact not_partHasClique_idxKt S ht u
  have hfree_v : ¬ partHasClique S t i v :=
    fun hc => hfree_u (partHasClique_congr S t (Setoid.symm' _ hr) hc)
  have hilen : i ≤ S.length := hi ▸ idxKt_le_length S t u
  have hi_mem : i ∈ (Finset.Icc 1 S.length).filter (fun j => ¬ partHasClique S t j v) := by
    simp [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨h1, hilen⟩, hfree_v⟩
  have h_upper : ∀ j ∈ (Finset.Icc 1 S.length).filter (fun j => ¬ partHasClique S t j v), j ≤ i := by
    intro j hj_mem
    by_contra hj_gt
    push_neg at hj_gt
    simp [Finset.mem_filter] at hj_mem
    have hjlen : j ≤ S.length := hj_mem.1.2
    have hrij : (S.part j).r u v := S.part_mono (by omega) (le_of_lt hj_gt) hjlen hr
    have hclq_u : partHasClique S t j u :=
      partHasClique_of_gt S t (by omega) hjlen
    exact hj_mem.2 (partHasClique_congr S t hrij hclq_u)
  apply le_antisymm
  · simp only [idxKt]
    apply Finset.sup_le
    intro j hj
    exact h_upper j hj
  · apply Finset.le_sup (f := id) hi_mem

/-- The **`Kt`-frozen relation**: equal, or sharing a part at the common
`Kt`-index. -/
def ktRel (S : MergeSeq G) (t : ℕ) (u v : V) : Prop :=
  u = v ∨ (idxKt S t u = idxKt S t v ∧ (S.part (idxKt S t u)).r u v)

/-- The **`Kt`-frozen partition** as a setoid. -/
noncomputable def ktSetoid (S : MergeSeq G) (t : ℕ) : Setoid V where
  r := ktRel S t
  iseqv := by
    constructor
    · intro x; left; rfl
    · rintro x y (rfl | ⟨h2, h3⟩)
      · left; rfl
      · right; exact ⟨h2.symm, h2 ▸ Setoid.symm' _ h3⟩
    · rintro x y z (rfl | ⟨hx2, hx3⟩) hyz
      · exact hyz
      · rcases hyz with rfl | ⟨hy2, hy3⟩
        · exact Or.inr ⟨hx2, hx3⟩
        · exact Or.inr ⟨hx2.trans hy2, Setoid.trans' _ hx3 (by rw [hx2]; exact hy3)⟩

/-- For any `u`, its `Kt`-frozen part equals its part at the `Kt`-index. -/
theorem ktSetoid_rel_iff (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (u v : V) :
    (ktSetoid S t).r u v ↔ (S.part (idxKt S t u)).r u v := by
  constructor
  · rintro (rfl | ⟨_, h3⟩)
    · exact (S.part (idxKt S t u)).iseqv.refl u
    · exact h3
  · intro h
    right
    exact ⟨(idxKt_eq_of_part_rel S ht rfl h).symm, h⟩

/-- The blocks of the `Kt`-frozen partition are `Kt`-free: any clique of `G`
inside a block has size `< t`. -/
theorem ktSetoid_block_KtFree (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t)
    {X : Finset V} (hclique : G.IsClique (X : Set V))
    (hsame : ∀ x ∈ X, ∀ y ∈ X, (ktSetoid S t).r x y) : X.card < t := by
  by_contra h
  push_neg at h
  have hne : X.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, hu⟩ := hne
  have hrel : ∀ v ∈ X, (ktSetoid S t).r u v := fun v hv => hsame u hu v hv
  have hpart : ∀ v ∈ X, (S.part (idxKt S t u)).r u v := by
    intro v hv
    exact (ktSetoid_rel_iff S ht u v).mp (hrel v hv)
  apply not_partHasClique_idxKt S ht u
  exact ⟨X, h, hclique, hpart⟩

/-- When `ω(G) = t`, no block is `Kt`-free at the last step, so every `Kt`-index
is `< length`. -/
theorem idxKt_lt_length (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t)
    (homega : G.cliqueNum = t) (v : V) : idxKt S t v < S.length := by
  have hlast : partHasClique S t S.length v := by
    obtain ⟨X, hX⟩ := G.exists_isNClique_cliqueNum
    refine ⟨X, ?_, hX.isClique, ?_⟩
    · rw [hX.card_eq, homega]
    · intro x _
      have : S.part S.length = ⊤ := S.part_length
      rw [this]; trivial
  have hne : idxKt S t v ≠ S.length := by
    intro h
    exact not_partHasClique_idxKt S ht v (h ▸ hlast)
  exact lt_of_le_of_ne (idxKt_le_length S t v) hne

/-- The block's successor part (`P_{idxKt+1}`) contains a `t`-clique. -/
theorem partHasClique_succ (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t)
    (homega : G.cliqueNum = t) (v : V) :
    partHasClique S t (idxKt S t v + 1) v := by
  have hlt := idxKt_lt_length S ht homega v
  exact partHasClique_of_gt S t (Nat.lt_succ_self _) (by omega)

/-- The within-block clique number of `GI = restrictGraph G Q` is `< t`. -/
theorem restrictGraph_cliqueNum_lt (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) :
    (restrictGraph G (ktSetoid S t)).cliqueNum + 1 ≤ t := by
  obtain ⟨s, hs⟩ := (restrictGraph G (ktSetoid S t)).exists_isNClique_cliqueNum
  have hcard : s.card = (restrictGraph G (ktSetoid S t)).cliqueNum := hs.card_eq
  have hclique_r : (restrictGraph G (ktSetoid S t)).IsClique (s : Set V) := hs.isClique
  have hGclique : G.IsClique (s : Set V) := by
    intro x hx y hy hxy
    have hadj := hclique_r hx hy hxy
    rw [restrictGraph_adj] at hadj
    exact hadj.1
  have hsame : ∀ x ∈ s, ∀ y ∈ s, (ktSetoid S t).r x y := by
    intro x hx y hy
    by_cases hxy : x = y
    · exact hxy ▸ (ktSetoid S t).iseqv.refl x
    · have hadj := hclique_r (by simpa using hx) (by simpa using hy) hxy
      rw [restrictGraph_adj] at hadj
      exact hadj.2
  have hlt := ktSetoid_block_KtFree S ht hGclique hsame
  omega

end Lax8Proofs
