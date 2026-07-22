import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Lax1Proofs.Source.TwinWidth.Contraction.TwinWidth

/-!
# Treewidth contract

This file gives the treewidth interface needed for the Bonnet--Déprés
twin-width/treewidth separation.  It deliberately contains only definitions and
axiom-free basic API; proof-heavy bounds such as the feedback-vertex-set bound
belong in full proof modules.
-/

namespace Lax1Proofs.TwinWidth
namespace SimpleGraph

/-- A tree decomposition of a finite simple graph.

The decomposition has a finite tree of nodes, assigns a finite bag of graph
vertices to each node, covers every graph vertex, covers every graph edge in
some bag, and requires the nodes whose bags contain a fixed graph vertex to
induce a connected subgraph of the decomposition tree.
-/
structure TreeDecomposition {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) where
  /-- The finite node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree has finitely many nodes. -/
  [nodeFintype : Fintype Node]
  /-- Decomposition nodes have decidable equality. -/
  [nodeDecidableEq : DecidableEq Node]
  /-- The tree on decomposition nodes. -/
  tree : _root_.SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex appears in at least one bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- Every graph edge has both endpoints together in at least one bag. -/
  edge_mem_bag : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Node, u ∈ bag i ∧ v ∈ bag i
  /-- For each graph vertex, the bags containing it form a connected subtree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected

namespace TreeDecomposition

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- The width of a tree decomposition is the maximum bag size minus one.

The subtraction is natural-number subtraction, so a decomposition whose largest
bag is empty has width `0`; this convention handles the empty graph without a
separate integer-valued parameter.
-/
noncomputable def width (D : TreeDecomposition G) : ℕ :=
  letI : Fintype D.Node := D.nodeFintype
  (Finset.univ.sup fun i : D.Node => (D.bag i).card) - 1

end TreeDecomposition

/-- The one-bag tree decomposition of a finite graph.

This decomposition witnesses the coarse bound `treewidth G ≤ |V| - 1` and, more
importantly, proves that the minimization defining `treewidth` is never empty
for finite graphs.
-/
noncomputable def oneBagTreeDecomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : TreeDecomposition G where
  Node := Unit
  tree := ⊥
  isTree := _root_.SimpleGraph.IsTree.of_subsingleton
  bag := fun _ => Finset.univ
  vertex_mem_bag := by
    intro v
    exact ⟨(), by simp⟩
  edge_mem_bag := by
    intro u v _huv
    exact ⟨(), by simp⟩
  bag_indices_connected := by
    intro v
    haveI : Nonempty {i : Unit | v ∈ (Finset.univ : Finset V)} := ⟨⟨(), by simp⟩⟩
    haveI : Subsingleton {i : Unit | v ∈ (Finset.univ : Finset V)} := inferInstance
    exact _root_.SimpleGraph.Connected.of_subsingleton

@[simp] theorem oneBagTreeDecomposition_width
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    (oneBagTreeDecomposition G).width = Fintype.card V - 1 := by
  classical
  simp [oneBagTreeDecomposition, TreeDecomposition.width]

/-- A graph has treewidth at most `k` when it has a tree decomposition of width
at most `k`. -/
def HasTreewidthAtMost {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, D.width ≤ k

/-- Every finite graph has treewidth at most `|V| - 1`, witnessed by the
one-bag decomposition. -/
theorem hasTreewidthAtMost_card_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    HasTreewidthAtMost G (Fintype.card V - 1) := by
  exact ⟨oneBagTreeDecomposition G, by simp⟩

/-- The set of possible treewidth bounds is nonempty for every finite graph. -/
theorem exists_hasTreewidthAtMost
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    ∃ k, HasTreewidthAtMost G k :=
  ⟨Fintype.card V - 1, hasTreewidthAtMost_card_sub_one G⟩

/-- The treewidth of a finite simple graph is the least width of a tree
decomposition.

The fallback branch makes the definition total; the usual existence theorem for
finite graphs will make it unreachable in completed proof files.
-/
noncomputable def treewidth {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℕ :=
  by
    classical
    exact if h : ∃ k, HasTreewidthAtMost G k then Nat.find h else 0

theorem treewidth_le_of_hasTreewidthAtMost
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {k : ℕ}
    (h : HasTreewidthAtMost G k) :
    treewidth G ≤ k := by
  classical
  have hex : ∃ e, HasTreewidthAtMost G e := ⟨k, h⟩
  rw [treewidth, dif_pos hex]
  exact Nat.find_min' hex h

/-- Every finite graph has treewidth at most one less than its number of
vertices. -/
theorem treewidth_le_card_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    treewidth G ≤ Fintype.card V - 1 :=
  treewidth_le_of_hasTreewidthAtMost (hasTreewidthAtMost_card_sub_one G)

/-- The minimum in the definition of `treewidth` is attained. -/
theorem hasTreewidthAtMost_treewidth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    HasTreewidthAtMost G (treewidth G) := by
  classical
  rw [treewidth, dif_pos (exists_hasTreewidthAtMost G)]
  exact Nat.find_spec (exists_hasTreewidthAtMost G)

/-- A feedback vertex set is a finite set of vertices whose deletion leaves an
acyclic induced subgraph. -/
def IsFeedbackVertexSet {V : Type*} (G : _root_.SimpleGraph V)
    (X : Finset V) : Prop :=
  (G.induce {v : V | v ∉ X}).IsAcyclic

end SimpleGraph
end Lax1Proofs.TwinWidth
