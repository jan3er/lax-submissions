import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Find

/-!
---
title: Treewidth
---
A tree decomposition of a finite simple graph $G$ consists of a finite tree
$T$ and a bag $X_t \subseteq V(G)$ at each node $t$ such that every graph
vertex occurs in a bag, the endpoints of every graph edge occur together in a
bag, and the nodes whose bags contain any fixed vertex induce a connected
subgraph of $T$.

The width of a tree decomposition is $\max_t |X_t|-1$. The treewidth
$\operatorname{tw}(G)$ is the least width of a tree decomposition of $G$.
The Lean minimum uses the value $0$ as a harmless fallback if the defining
set is empty.
-/

namespace Lax1.Treewidth

/-- A tree decomposition of a simple graph: a finite tree of nodes, a bag of
graph vertices at each node, such that bags cover every vertex and every
edge, and the nodes whose bags contain any fixed vertex induce a connected
subgraph of the tree. -/
structure TreeDecomposition {V : Type} [DecidableEq V] (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree has finitely many nodes. -/
  [nodeFintype : Fintype Node]
  /-- Decomposition nodes have decidable equality. -/
  [nodeDecidableEq : DecidableEq Node]
  /-- The graph on the decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex appears in at least one bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- Every graph edge has both endpoints together in at least one bag. -/
  edge_mem_bag : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Node, u ∈ bag i ∧ v ∈ bag i
  /-- For each graph vertex, the nodes whose bags contain it induce a
  connected subgraph of the tree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected

/-- The width of a tree decomposition: its largest bag size minus one. -/
noncomputable def TreeDecomposition.width
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TreeDecomposition G) : ℕ :=
  letI : Fintype D.Node := D.nodeFintype
  (Finset.univ.sup fun i : D.Node => (D.bag i).card) - 1

/-- The least natural satisfying `P`, or zero if no natural satisfies it.
This packages the minimization convention used in the definition of
treewidth. -/
noncomputable def leastNat (P : ℕ → Prop) : ℕ :=
  letI : Decidable (∃ n, P n) := Classical.propDecidable _
  letI : DecidablePred P := Classical.decPred P
  if h : ∃ n, P n then Nat.find h else 0

/-- The treewidth of a finite simple graph. -/
noncomputable def treewidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  leastNat fun width => ∃ D : TreeDecomposition G, D.width ≤ width

end Lax1.Treewidth
