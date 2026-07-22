import Lax1Proofs.Source.TwinWidth.Graph.Treewidth
import Mathlib.Data.Nat.Bitwise

/-!
# The Bonnet--Déprés graph family

This file defines the finite graph family used in the proof that twin-width can
be exponential in treewidth.  For the first formal pass we specialize the paper
to an integer-friendly setting: `t = 2 * k + 3`, apex set `Fin t`, and a full
`2^t`-ary tree of an explicit large depth.  Child labels encode all
neighborhoods in the apex set by binary bits.
-/

namespace Lax1Proofs.TwinWidth
namespace SimpleGraph

/-- Nodes of the full `branch`-ary rooted tree of depth `depth`.

A node is a level `ℓ ≤ depth` together with the sequence of child labels on the
path from the root to that node.
-/
abbrev FullTreeNode (branch depth : ℕ) : Type :=
  Σ level : Fin (depth + 1), Fin level.val → Fin branch

namespace FullTreeNode

/-- `parent` is the immediate parent of `child` in the full rooted tree. -/
def IsParent {branch depth : ℕ}
    (parent child : FullTreeNode branch depth) : Prop :=
  ∃ hlevel : child.1.val = parent.1.val + 1,
    ∀ i : Fin parent.1.val,
      child.2 ⟨i.val, by omega⟩ = parent.2 i

theorem not_isParent_self {branch depth : ℕ}
    (u : FullTreeNode branch depth) :
    ¬ IsParent u u := by
  intro h
  rcases h with ⟨hlevel, _⟩
  omega

/-- The full rooted tree as a simple graph. -/
def graph (branch depth : ℕ) : _root_.SimpleGraph (FullTreeNode branch depth) where
  Adj u v := IsParent u v ∨ IsParent v u
  symm := by
    intro u v h
    exact h.symm
  loopless := by
    constructor
    intro u h
    rcases h with h | h
    · exact not_isParent_self u h
    · exact not_isParent_self u h

/-- The child label used to determine a non-root node's neighborhood in the
apex set. -/
def lastLabel {branch depth : ℕ}
    (u : FullTreeNode branch depth) (hlevel : 0 < u.1.val) : Fin branch :=
  u.2 ⟨u.1.val - 1, by omega⟩

/-- The child of `parent` with incoming label `label`. -/
def child {branch depth : ℕ}
    (parent : FullTreeNode branch depth) (hlevel : parent.1.val < depth)
    (label : Fin branch) : FullTreeNode branch depth :=
  ⟨⟨parent.1.val + 1, by omega⟩,
    fun i =>
      if h : i.val < parent.1.val then
        parent.2 ⟨i.val, h⟩
      else
        label⟩

theorem isParent_child {branch depth : ℕ}
    (parent : FullTreeNode branch depth) (hlevel : parent.1.val < depth)
    (label : Fin branch) :
    IsParent parent (child parent hlevel label) := by
  refine ⟨rfl, ?_⟩
  intro i
  simp [child, i.isLt]

theorem lastLabel_child {branch depth : ℕ}
    (parent : FullTreeNode branch depth) (hlevel : parent.1.val < depth)
    (label : Fin branch)
    (hchild : 0 < (child parent hlevel label).1.val) :
    lastLabel (child parent hlevel label) hchild = label := by
  ext
  simp [lastLabel, child]

/-- The root of the full rooted tree. -/
def root (branch depth : ℕ) : FullTreeNode branch depth :=
  ⟨⟨0, by omega⟩, fun i => Fin.elim0 i⟩

theorem eq_root_of_level_zero {branch depth : ℕ}
    {u : FullTreeNode branch depth} (h : u.1.val = 0) :
    u = root branch depth := by
  cases u with
  | mk level path =>
    cases level with
    | mk n hn =>
      simp only at h
      subst n
      simp [root]
      funext i
      exact Fin.elim0 i

/-- The immediate parent of a non-root full-tree node. -/
def parent {branch depth : ℕ}
    (u : FullTreeNode branch depth) (hlevel : 0 < u.1.val) :
    FullTreeNode branch depth :=
  ⟨⟨u.1.val - 1, by omega⟩,
    fun i =>
      u.2 ⟨i.val, by
        have hi : i.val < u.1.val - 1 := i.isLt
        omega⟩⟩

theorem parent_isParent {branch depth : ℕ}
    (u : FullTreeNode branch depth) (hlevel : 0 < u.1.val) :
    IsParent (parent u hlevel) u := by
  refine ⟨by simp [parent]; omega, ?_⟩
  intro i
  rfl

theorem isParent_level {branch depth : ℕ}
    {parent child : FullTreeNode branch depth}
    (h : IsParent parent child) :
    child.1.val = parent.1.val + 1 := by
  rcases h with ⟨hlevel, _⟩
  exact hlevel

theorem isParent_parent_lt_child_level {branch depth : ℕ}
    {parent child : FullTreeNode branch depth}
    (h : IsParent parent child) :
    parent.1.val < child.1.val := by
  rw [isParent_level h]
  omega

theorem isParent_unique {branch depth : ℕ}
    {parent₁ parent₂ child : FullTreeNode branch depth}
    (h₁ : IsParent parent₁ child) (h₂ : IsParent parent₂ child) :
    parent₁ = parent₂ := by
  rcases h₁ with ⟨hlevel₁, hpath₁⟩
  rcases h₂ with ⟨hlevel₂, hpath₂⟩
  cases parent₁ with
  | mk level₁ path₁ =>
  cases parent₂ with
  | mk level₂ path₂ =>
    simp only at hlevel₁ hlevel₂ hpath₁ hpath₂ ⊢
    have hval : level₁.val = level₂.val := by omega
    have hlevel : level₁ = level₂ := Fin.ext hval
    subst level₂
    congr
    funext i
    have h₁i := hpath₁ i
    have h₂i := hpath₂ i
    exact h₁i.symm.trans h₂i

theorem adj_level_eq_succ_or_succ_eq {branch depth : ℕ}
    {u v : FullTreeNode branch depth}
    (h : (graph branch depth).Adj u v) :
    v.1.val = u.1.val + 1 ∨ u.1.val = v.1.val + 1 := by
  rcases h with h | h
  · exact Or.inl (isParent_level h)
  · exact Or.inr (isParent_level h)

theorem isParent_of_adj_of_level_le {branch depth : ℕ}
    {u v : FullTreeNode branch depth}
    (h : (graph branch depth).Adj u v) (hlevel : v.1.val ≤ u.1.val) :
    IsParent v u := by
  rcases h with h | h
  · have : u.1.val < v.1.val := isParent_parent_lt_child_level h
    omega
  · exact h

/-- The full rooted tree graph is acyclic.

If a cycle existed, rotate it so that it starts at a vertex of maximum level
among the cycle vertices.  Both neighbours of this maximum-level vertex on the
cycle must be its unique parent, contradicting the fact that the second and
penultimate vertices of a cycle are distinct.
-/
theorem graph_isAcyclic (branch depth : ℕ) :
    (graph branch depth).IsAcyclic := by
  classical
  intro v c hc
  let s : Finset (FullTreeNode branch depth) := c.support.toFinset
  have hs : s.Nonempty := by
    refine ⟨v, ?_⟩
    simp [s]
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_max_image s (fun u : FullTreeNode branch depth => u.1.val) hs
  have hm_support : m ∈ c.support := by
    simpa [s] using hm
  let r : (graph branch depth).Walk m m := c.rotate m hm_support
  have hr_cycle : r.IsCycle := by
    simpa [r] using hc.rotate hm_support
  have hr_not_nil : ¬ r.Nil := hr_cycle.not_nil
  have hsnd_support : r.snd ∈ c.support := by
    have : r.snd ∈ r.support := r.getVert_mem_support 1
    simpa [r] using (c.mem_support_rotate_iff m hm_support).mp this
  have hpen_support : r.penultimate ∈ c.support := by
    have : r.penultimate ∈ r.support := r.getVert_mem_support (r.length - 1)
    simpa [r] using (c.mem_support_rotate_iff m hm_support).mp this
  have hsnd_level : r.snd.1.val ≤ m.1.val := by
    exact hmax r.snd (by simpa [s] using hsnd_support)
  have hpen_level : r.penultimate.1.val ≤ m.1.val := by
    exact hmax r.penultimate (by simpa [s] using hpen_support)
  have hsnd_parent : IsParent r.snd m := by
    exact isParent_of_adj_of_level_le (r.adj_snd hr_not_nil) hsnd_level
  have hpen_parent : IsParent r.penultimate m := by
    exact isParent_of_adj_of_level_le (r.adj_penultimate hr_not_nil).symm hpen_level
  exact hr_cycle.snd_ne_penultimate (isParent_unique hsnd_parent hpen_parent)

theorem root_reachable (branch depth : ℕ)
    (u : FullTreeNode branch depth) :
    (graph branch depth).Reachable (root branch depth) u := by
  classical
  have hmain :
      ∀ n : ℕ, ∀ u : FullTreeNode branch depth, u.1.val = n →
        (graph branch depth).Reachable (root branch depth) u := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro u hu
        by_cases hn : n = 0
        · subst n
          have hroot : u = root branch depth := eq_root_of_level_zero (by omega)
          rw [hroot]
        · have hu_pos : 0 < u.1.val := by omega
          let p : FullTreeNode branch depth := parent u hu_pos
          have hp_lt : p.1.val < n := by
            simp [p, parent]
            omega
          have hreach_p : (graph branch depth).Reachable (root branch depth) p :=
            ih p.1.val hp_lt p rfl
          have hadj : (graph branch depth).Adj p u := Or.inl (parent_isParent u hu_pos)
          exact hreach_p.trans hadj.reachable
  exact hmain u.1.val u rfl

theorem graph_connected (branch depth : ℕ) :
    (graph branch depth).Connected := by
  rw [_root_.SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨root branch depth, root_reachable branch depth⟩

theorem graph_isTree (branch depth : ℕ) :
    (graph branch depth).IsTree where
  connected := graph_connected branch depth
  isAcyclic := graph_isAcyclic branch depth

end FullTreeNode

/-- The apex-set size in the integer-specialized Bonnet--Déprés construction. -/
def bonnetDepresApexCount (k : ℕ) : ℕ :=
  2 * k + 3

/-- The branching factor: one child for each subset of the apex set. -/
def bonnetDepresBranch (k : ℕ) : ℕ :=
  2 ^ bonnetDepresApexCount k

/-- A large explicit depth sufficient for the paper's counting argument after
specializing to `ε = 1/2`.

The exact constants are intentionally generous; later lower-bound lemmas should
refer to this named definition rather than unfold the expression.
-/
def bonnetDepresDepth (k : ℕ) : ℕ :=
  2 + 2 ^ (k + 2) *
    2 ^ ((k + 1) * (2 + 2 ^ (k + 2) * (2 ^ (k + 1) + 1)))

/-- Vertices of the Bonnet--Déprés graph: apex vertices plus the full tree. -/
abbrev BonnetDepresVertex (k : ℕ) : Type :=
  Fin (bonnetDepresApexCount k) ⊕
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)

/-- A tree node is adjacent to an apex vertex according to the bit of its
incoming child label.  The root has no apex neighbors. -/
def bonnetDepresApexAdj {k : ℕ}
    (x : Fin (bonnetDepresApexCount k))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : Prop :=
  ∃ hlevel : 0 < u.1.val,
    (FullTreeNode.lastLabel u hlevel).val.testBit x.val = true

theorem bonnetDepresApexAdj_child {k : ℕ}
    (x : Fin (bonnetDepresApexCount k))
    (parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : parent.1.val < bonnetDepresDepth k)
    (label : Fin (bonnetDepresBranch k)) :
    bonnetDepresApexAdj x (FullTreeNode.child parent hlevel label) ↔
      label.val.testBit x.val = true := by
  constructor
  · rintro ⟨hchild, hbit⟩
    simpa [FullTreeNode.lastLabel_child parent hlevel label hchild] using hbit
  · intro hbit
    refine ⟨by simp [FullTreeNode.child], ?_⟩
    simpa [FullTreeNode.lastLabel_child parent hlevel label (by simp [FullTreeNode.child])]
      using hbit

/-- The Bonnet--Déprés graph specialized to exponent parameter `k`.

The apex set is independent, the tree part is the full rooted tree, and every
non-root tree node uses its incoming child label as the binary code of its
neighborhood in the apex set.
-/
def bonnetDepresGraph (k : ℕ) : _root_.SimpleGraph (BonnetDepresVertex k) where
  Adj a b :=
    match a, b with
    | Sum.inl _, Sum.inl _ => False
    | Sum.inl x, Sum.inr u => bonnetDepresApexAdj x u
    | Sum.inr u, Sum.inl x => bonnetDepresApexAdj x u
    | Sum.inr u, Sum.inr v =>
        (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj u v
  symm := by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).symm h
  loopless := by
    constructor
    intro a h
    cases a with
    | inl x => exact h
    | inr u =>
        exact (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).irrefl h

/-- The apex set of the Bonnet--Déprés graph. -/
def bonnetDepresApexSet (k : ℕ) : Finset (BonnetDepresVertex k) :=
  Finset.univ.image Sum.inl

@[simp] theorem card_bonnetDepresApexSet (k : ℕ) :
    (bonnetDepresApexSet k).card = bonnetDepresApexCount k := by
  classical
  rw [bonnetDepresApexSet, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Sum.inl.inj h

theorem inr_notMem_bonnetDepresApexSet (k : ℕ)
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    (Sum.inr u : BonnetDepresVertex k) ∉ bonnetDepresApexSet k := by
  classical
  intro h
  rcases Finset.mem_image.mp h with ⟨x, _hx, hx⟩
  cases hx

theorem inl_mem_bonnetDepresApexSet (k : ℕ)
    (x : Fin (bonnetDepresApexCount k)) :
    (Sum.inl x : BonnetDepresVertex k) ∈ bonnetDepresApexSet k := by
  classical
  exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩

/-- Deleting the apex set leaves exactly the tree-node side. -/
noncomputable def bonnetDepresTreeComplementEquiv (k : ℕ) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) ≃
      {v : BonnetDepresVertex k // v ∉ bonnetDepresApexSet k} where
  toFun u := ⟨Sum.inr u, inr_notMem_bonnetDepresApexSet k u⟩
  invFun v :=
    match v with
    | ⟨Sum.inl x, hv⟩ => False.elim (hv (inl_mem_bonnetDepresApexSet k x))
    | ⟨Sum.inr u, _hv⟩ => u
  left_inv := by
    intro u
    rfl
  right_inv := by
    intro v
    cases v with
    | mk val hval =>
    cases val with
    | inl x =>
        exact False.elim (hval (inl_mem_bonnetDepresApexSet k x))
    | inr u =>
        rfl

/-- The graph induced after deleting the apex set is isomorphic to the full
tree graph. -/
noncomputable def bonnetDepresTreeComplementIso (k : ℕ) :
    FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k) ≃g
      (bonnetDepresGraph k).induce {v : BonnetDepresVertex k | v ∉ bonnetDepresApexSet k} :=
  { bonnetDepresTreeComplementEquiv k with
    map_rel_iff' := by
      intro u v
      rfl }

/-- The apex set is a feedback vertex set once the full tree graph is known to
be acyclic. -/
theorem bonnetDepresApexSet_isFeedbackVertexSet_of_fullTree_acyclic
    (k : ℕ)
    (hTree :
      (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).IsAcyclic) :
    IsFeedbackVertexSet (bonnetDepresGraph k) (bonnetDepresApexSet k) := by
  simpa [IsFeedbackVertexSet] using
    (bonnetDepresTreeComplementIso k).isAcyclic_iff.mp hTree

/-- The bag at a tree node in the direct tree decomposition of the
Bonnet--Déprés graph.

Every bag contains the whole apex set, the current tree node, and, away from the
root, the parent of the current tree node.  Thus tree edges are covered by the
child bag, while apex-tree edges are covered by the tree endpoint's bag.
-/
def bonnetDepresTreeDecompositionBag (k : ℕ)
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    Finset (BonnetDepresVertex k) :=
  bonnetDepresApexSet k ∪ {Sum.inr u} ∪
    if h : 0 < u.1.val then {Sum.inr (FullTreeNode.parent u h)} else ∅

theorem apex_mem_bonnetDepresTreeDecompositionBag (k : ℕ)
    (x : Fin (bonnetDepresApexCount k))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    (Sum.inl x : BonnetDepresVertex k) ∈
      bonnetDepresTreeDecompositionBag k u := by
  simp [bonnetDepresTreeDecompositionBag, inl_mem_bonnetDepresApexSet]

theorem self_mem_bonnetDepresTreeDecompositionBag (k : ℕ)
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    (Sum.inr u : BonnetDepresVertex k) ∈
      bonnetDepresTreeDecompositionBag k u := by
  simp [bonnetDepresTreeDecompositionBag]

theorem parent_mem_bonnetDepresTreeDecompositionBag (k : ℕ)
    {parent child :
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hparent : FullTreeNode.IsParent parent child) :
    (Sum.inr parent : BonnetDepresVertex k) ∈
      bonnetDepresTreeDecompositionBag k child := by
  have hpos : 0 < child.1.val :=
    Nat.succ_le_iff.mp (by
      rw [FullTreeNode.isParent_level hparent]
      exact Nat.le_add_left 1 parent.1.val)
  have hparent_eq :
      FullTreeNode.parent child hpos = parent :=
    FullTreeNode.isParent_unique (FullTreeNode.parent_isParent child hpos) hparent
  simp [bonnetDepresTreeDecompositionBag, hpos, hparent_eq]

theorem inr_mem_bonnetDepresTreeDecompositionBag_iff (k : ℕ)
    (v u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    (Sum.inr v : BonnetDepresVertex k) ∈
      bonnetDepresTreeDecompositionBag k u ↔
      v = u ∨ ∃ h : 0 < u.1.val, FullTreeNode.parent u h = v := by
  classical
  by_cases h : 0 < u.1.val
  · simp [bonnetDepresTreeDecompositionBag, inr_notMem_bonnetDepresApexSet, h,
      eq_comm]
  · simp [bonnetDepresTreeDecompositionBag, inr_notMem_bonnetDepresApexSet, h,
      eq_comm]

theorem bonnetDepresTreeDecompositionBag_card_le (k : ℕ)
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    (bonnetDepresTreeDecompositionBag k u).card ≤ bonnetDepresApexCount k + 2 := by
  classical
  let tail : Finset (BonnetDepresVertex k) :=
    {Sum.inr u} ∪
      if h : 0 < u.1.val then {Sum.inr (FullTreeNode.parent u h)} else ∅
  have htail : tail.card ≤ 2 := by
    by_cases h : 0 < u.1.val
    · simp [tail, h, Finset.card_le_two]
    · simp [tail, h]
  have hcard :
      (bonnetDepresTreeDecompositionBag k u).card ≤
        (bonnetDepresApexSet k).card + tail.card := by
    simpa [bonnetDepresTreeDecompositionBag, tail, Finset.union_assoc] using
      Finset.card_union_le (bonnetDepresApexSet k) tail
  calc
    (bonnetDepresTreeDecompositionBag k u).card ≤
        (bonnetDepresApexSet k).card + tail.card := hcard
    _ ≤ bonnetDepresApexCount k + 2 := by
      simp
      omega

theorem bonnetDepresTreeDecomposition_bag_indices_connected (k : ℕ)
    (z : BonnetDepresVertex k) :
    ((FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).induce
      {u :
        FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) |
        z ∈ bonnetDepresTreeDecompositionBag k u}).Connected := by
  classical
  cases z with
  | inl x =>
      rw [_root_.SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k),
        apex_mem_bonnetDepresTreeDecompositionBag k x
          (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))⟩, ?_⟩
      intro y
      rcases y with ⟨u, hu⟩
      rcases FullTreeNode.root_reachable (bonnetDepresBranch k) (bonnetDepresDepth k) u with ⟨w⟩
      refine ⟨(w.induce _ ?_).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩
      intro a _ha
      exact apex_mem_bonnetDepresTreeDecompositionBag k x a
  | inr v =>
      rw [_root_.SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨v, self_mem_bonnetDepresTreeDecompositionBag k v⟩, ?_⟩
      intro y
      rcases y with ⟨u, hu⟩
      rcases (inr_mem_bonnetDepresTreeDecompositionBag_iff k v u).mp hu with hself | hparent
      · subst u
        exact _root_.SimpleGraph.Reachable.rfl
      · rcases hparent with ⟨hpos, hparent_eq⟩
        have hparent_isParent : FullTreeNode.IsParent v u := by
          simpa [hparent_eq] using FullTreeNode.parent_isParent u hpos
        have hadj :
            (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj v u :=
          Or.inl hparent_isParent
        exact ⟨_root_.SimpleGraph.Walk.cons (_root_.SimpleGraph.induce_adj.2 hadj)
          _root_.SimpleGraph.Walk.nil⟩

/-- The direct width-`|apex| + 1` tree decomposition of the
Bonnet--Déprés graph. -/
noncomputable def bonnetDepresTreeDecomposition (k : ℕ) :
    TreeDecomposition (bonnetDepresGraph k) where
  Node := FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)
  tree := FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)
  isTree := FullTreeNode.graph_isTree (bonnetDepresBranch k) (bonnetDepresDepth k)
  bag := bonnetDepresTreeDecompositionBag k
  vertex_mem_bag := by
    intro z
    cases z with
    | inl x =>
        exact ⟨FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k),
          apex_mem_bonnetDepresTreeDecompositionBag k x
            (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))⟩
    | inr u =>
        exact ⟨u, self_mem_bonnetDepresTreeDecompositionBag k u⟩
  edge_mem_bag := by
    intro a b hab
    cases a with
    | inl x =>
        cases b with
        | inl y => cases hab
        | inr u =>
            exact ⟨u, apex_mem_bonnetDepresTreeDecompositionBag k x u,
              self_mem_bonnetDepresTreeDecompositionBag k u⟩
    | inr u =>
        cases b with
        | inl x =>
            exact ⟨u, self_mem_bonnetDepresTreeDecompositionBag k u,
              apex_mem_bonnetDepresTreeDecompositionBag k x u⟩
        | inr v =>
            rcases hab with hparent | hparent
            · exact ⟨v, parent_mem_bonnetDepresTreeDecompositionBag k hparent,
                self_mem_bonnetDepresTreeDecompositionBag k v⟩
            · exact ⟨u, self_mem_bonnetDepresTreeDecompositionBag k u,
                parent_mem_bonnetDepresTreeDecompositionBag k hparent⟩
  bag_indices_connected := by
    intro z
    exact bonnetDepresTreeDecomposition_bag_indices_connected k z

theorem bonnetDepresTreeDecomposition_width_le (k : ℕ) :
    (bonnetDepresTreeDecomposition k).width ≤ bonnetDepresApexCount k + 1 := by
  classical
  have hsup :
      (Finset.univ.sup fun u :
        FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) =>
        (bonnetDepresTreeDecompositionBag k u).card) ≤
        bonnetDepresApexCount k + 2 := by
    rw [Finset.sup_le_iff]
    intro u _hu
    exact bonnetDepresTreeDecompositionBag_card_le k u
  dsimp [TreeDecomposition.width, bonnetDepresTreeDecomposition]
  have hsub := Nat.sub_le_sub_right hsup 1
  omega

theorem bonnetDepres_treewidth_le (k : ℕ) :
    treewidth (bonnetDepresGraph k) ≤ 2 * k + 4 := by
  refine treewidth_le_of_hasTreewidthAtMost ?_
  refine ⟨bonnetDepresTreeDecomposition k, ?_⟩
  calc
    (bonnetDepresTreeDecomposition k).width ≤ bonnetDepresApexCount k + 1 :=
      bonnetDepresTreeDecomposition_width_le k
    _ = 2 * k + 4 := by
      simp [bonnetDepresApexCount]

end SimpleGraph
end Lax1Proofs.TwinWidth
