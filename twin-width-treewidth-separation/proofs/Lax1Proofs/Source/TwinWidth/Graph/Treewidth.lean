import Lax1Proofs.Source.TwinWidth.Graph.TreewidthContract

/-!
# Treewidth proof infrastructure

This file proves reusable lemmas about the treewidth definitions in
`TreewidthContract.lean`.  The first construction lifts a tree decomposition of
an induced subgraph to a tree decomposition of the original graph by adding a
fixed finite set of deleted vertices to every bag.
-/

namespace Lax1Proofs.TwinWidth
namespace SimpleGraph

namespace TreeDecomposition

/-- Relabel a tree decomposition along a graph isomorphism. -/
noncomputable def mapIso
    {V V' : Type} [DecidableEq V] [DecidableEq V']
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'}
    (D : TreeDecomposition G) (e : G ≃g G') : TreeDecomposition G' where
  Node := D.Node
  nodeFintype := D.nodeFintype
  nodeDecidableEq := D.nodeDecidableEq
  tree := D.tree
  isTree := D.isTree
  bag := fun i => (D.bag i).map e.toEquiv.toEmbedding
  vertex_mem_bag := by
    intro v
    rcases D.vertex_mem_bag (e.symm v) with ⟨i, hi⟩
    exact ⟨i, Finset.mem_map.mpr ⟨e.symm v, hi, by simp⟩⟩
  edge_mem_bag := by
    intro u v huv
    have hpre : G.Adj (e.symm u) (e.symm v) := by
      exact (_root_.SimpleGraph.Iso.map_adj_iff e).mp (by simpa using huv)
    rcases D.edge_mem_bag hpre with ⟨i, hui, hvi⟩
    exact ⟨i, Finset.mem_map.mpr ⟨e.symm u, hui, by simp⟩,
      Finset.mem_map.mpr ⟨e.symm v, hvi, by simp⟩⟩
  bag_indices_connected := by
    intro v
    have hset :
        {i : D.Node | v ∈ (D.bag i).map e.toEquiv.toEmbedding} =
          {i : D.Node | e.symm v ∈ D.bag i} := by
      ext i
      constructor
      · intro hi
        rcases Finset.mem_map.mp hi with ⟨x, hx, hxv⟩
        have hx_eq : x = e.symm v := by
          rw [← hxv]
          simp
        simpa [← hx_eq] using hx
      · intro hi
        exact Finset.mem_map.mpr ⟨e.symm v, hi, by simp⟩
    rw [hset]
    exact D.bag_indices_connected (e.symm v)

@[simp] theorem mapIso_width
    {V V' : Type} [DecidableEq V] [DecidableEq V']
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'}
    (D : TreeDecomposition G) (e : G ≃g G') :
    (D.mapIso e).width = D.width := by
  classical
  dsimp [TreeDecomposition.width, mapIso]
  congr 1
  apply Finset.sup_congr rfl
  intro i _hi
  simp

/-- Add a fixed finite set `X` to every bag of a tree decomposition of
`G.induce S`, obtaining a decomposition of `G`, provided every vertex outside
`S` lies in `X`.

This is the structural bridge needed for the standard proof that a feedback
vertex set of size `s` gives treewidth at most `s + 1`.
-/
noncomputable def augmentDeletedSet
    {V : Type} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {S : Set V}
    (X : Finset V) (hcover : ∀ v : V, v ∈ X ∨ v ∈ S)
    (D : TreeDecomposition (G.induce S)) : TreeDecomposition G where
  Node := D.Node
  nodeFintype := D.nodeFintype
  nodeDecidableEq := D.nodeDecidableEq
  tree := D.tree
  isTree := D.isTree
  bag := fun i => X ∪ (D.bag i).image Subtype.val
  vertex_mem_bag := by
    intro v
    rcases hcover v with hvX | hvS
    · haveI : Nonempty D.Node := D.isTree.connected.nonempty
      exact ⟨Classical.arbitrary D.Node, by simp [hvX]⟩
    · rcases D.vertex_mem_bag ⟨v, hvS⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      exact Finset.mem_union_right X
        (Finset.mem_image.mpr ⟨⟨v, hvS⟩, hi, rfl⟩)
  edge_mem_bag := by
    intro u v huv
    rcases hcover u with huX | huS
    · rcases hcover v with hvX | hvS
      · haveI : Nonempty D.Node := D.isTree.connected.nonempty
        exact ⟨Classical.arbitrary D.Node, by simp [huX, hvX]⟩
      · rcases D.vertex_mem_bag ⟨v, hvS⟩ with ⟨i, hvi⟩
        refine ⟨i, ?_⟩
        exact ⟨Finset.mem_union_left _ huX,
          Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨v, hvS⟩, hvi, rfl⟩)⟩
    · rcases hcover v with hvX | hvS
      · rcases D.vertex_mem_bag ⟨u, huS⟩ with ⟨i, hui⟩
        refine ⟨i, ?_⟩
        exact ⟨Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨u, huS⟩, hui, rfl⟩),
          Finset.mem_union_left _ hvX⟩
      · have huv' : (G.induce S).Adj ⟨u, huS⟩ ⟨v, hvS⟩ := huv
        rcases D.edge_mem_bag huv' with ⟨i, hui, hvi⟩
        refine ⟨i, ?_⟩
        exact ⟨Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨u, huS⟩, hui, rfl⟩),
          Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨v, hvS⟩, hvi, rfl⟩)⟩
  bag_indices_connected := by
    intro v
    by_cases hvX : v ∈ X
    · have hconn :
          (D.tree.induce (Set.univ : Set D.Node)).Connected := by
        exact (_root_.SimpleGraph.induceUnivIso D.tree).connected_iff.mpr
          D.isTree.connected
      have hset :
          {i : D.Node | v ∈ X ∪ Finset.image Subtype.val (D.bag i)} =
            Set.univ := by
        ext i
        simp [hvX]
      rw [hset]
      exact hconn
    · have hvS : v ∈ S := by
        rcases hcover v with h | h
        · exact (hvX h).elim
        · exact h
      have hset :
          {i : D.Node | v ∈ X ∪ Finset.image Subtype.val (D.bag i)} =
            {i : D.Node | (⟨v, hvS⟩ : S) ∈ D.bag i} := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_union.mp hi with hiX | hiImage
          · exact (hvX hiX).elim
          · rcases Finset.mem_image.mp hiImage with ⟨w, hw, hwv⟩
            have hw_eq : w = ⟨v, hvS⟩ := Subtype.ext hwv
            simpa [hw_eq] using hw
        · intro hi
          exact Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨v, hvS⟩, hi, rfl⟩)
      rw [hset]
      exact D.bag_indices_connected ⟨v, hvS⟩

/-- Adding `X` to every bag increases width by at most `|X|`. -/
theorem augmentDeletedSet_width_le
    {V : Type} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {S : Set V}
    (X : Finset V) (hcover : ∀ v : V, v ∈ X ∨ v ∈ S)
    (D : TreeDecomposition (G.induce S)) {d : ℕ}
    (hD : D.width ≤ d) :
    (D.augmentDeletedSet X hcover).width ≤ X.card + d := by
  classical
  letI : Fintype D.Node := D.nodeFintype
  letI : DecidableEq D.Node := D.nodeDecidableEq
  let M : ℕ := Finset.univ.sup fun i : D.Node => (D.bag i).card
  let M' : ℕ :=
    Finset.univ.sup fun i : D.Node =>
      (X ∪ (D.bag i).image Subtype.val).card
  have hMle : M ≤ d + 1 := by
    dsimp [TreeDecomposition.width, M] at hD
    omega
  have hM'le : M' ≤ X.card + d + 1 := by
    dsimp [M']
    refine Finset.sup_le ?_
    intro i _hi
    have hbag_le_M : (D.bag i).card ≤ M := by
      dsimp [M]
      exact Finset.le_sup (f := fun i : D.Node => (D.bag i).card) (by simp)
    have hbag_le : (D.bag i).card ≤ d + 1 := hbag_le_M.trans hMle
    calc
      (X ∪ (D.bag i).image Subtype.val).card
          ≤ X.card + ((D.bag i).image Subtype.val).card :=
            Finset.card_union_le _ _
      _ ≤ X.card + (D.bag i).card := by
            exact Nat.add_le_add_left Finset.card_image_le X.card
      _ ≤ X.card + (d + 1) := by
            exact Nat.add_le_add_left hbag_le X.card
      _ = X.card + d + 1 := by omega
  dsimp [TreeDecomposition.width, augmentDeletedSet, M'] at hM'le ⊢
  omega

end TreeDecomposition

namespace HasTreewidthAtMost

/-- The predicate `HasTreewidthAtMost` is preserved by graph isomorphism. -/
theorem of_iso
    {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'} {k : ℕ}
    (h : HasTreewidthAtMost G k) (e : G ≃g G') :
    HasTreewidthAtMost G' k := by
  rcases h with ⟨D, hD⟩
  exact ⟨D.mapIso e, by simpa using hD⟩

end HasTreewidthAtMost

/-- Treewidth is invariant under graph isomorphism. -/
theorem treewidth_eq_of_iso
    {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'}
    (e : G ≃g G') :
    treewidth G = treewidth G' := by
  apply le_antisymm
  · exact treewidth_le_of_hasTreewidthAtMost
      ((hasTreewidthAtMost_treewidth G').of_iso e.symm)
  · exact treewidth_le_of_hasTreewidthAtMost
      ((hasTreewidthAtMost_treewidth G).of_iso e)

/-- If every finite acyclic graph has treewidth at most `1`, then a feedback
vertex set of size `s` gives treewidth at most `s + 1`.

The proof deletes the feedback vertex set, takes a width-one decomposition of
the remaining forest, and adds the feedback vertex set to every bag.
-/
theorem treewidth_le_card_add_one_of_feedback_vertex_set_of_acyclic_treewidth_le_one
    (hAcyclic :
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : _root_.SimpleGraph W),
        H.IsAcyclic → treewidth H ≤ 1)
    {V : Type} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {X : Finset V}
    (hX : IsFeedbackVertexSet G X) :
    treewidth G ≤ X.card + 1 := by
  classical
  let S : Set V := {v : V | v ∉ X}
  let H : _root_.SimpleGraph S := G.induce S
  have htwH : treewidth H ≤ 1 := hAcyclic H hX
  rcases hasTreewidthAtMost_treewidth H with ⟨D, hD⟩
  have hD_one : D.width ≤ 1 := hD.trans htwH
  have hcover : ∀ v : V, v ∈ X ∨ v ∈ S := by
    intro v
    by_cases hv : v ∈ X
    · exact Or.inl hv
    · exact Or.inr hv
  let D' : TreeDecomposition G := D.augmentDeletedSet X hcover
  have hwidth : D'.width ≤ X.card + 1 := by
    exact D.augmentDeletedSet_width_le X hcover hD_one
  exact treewidth_le_of_hasTreewidthAtMost ⟨D', hwidth⟩

end SimpleGraph
end Lax1Proofs.TwinWidth
