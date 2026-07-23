import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice

/-!
---
title: Treewidth
type: definition
---
A tree decomposition of a finite simple graph *G* consists of a finite tree
*T* and a bag of graph vertices at each node such that every graph
vertex occurs in a bag, the endpoints of every graph edge occur together in a
bag, and the nodes whose bags contain any fixed vertex induce a connected
subgraph of *T*.

The treewidth of *G* is the least *w* such that *G* has a tree
decomposition with every bag of size at most *w* + 1.

# Formalization notes

A tree decomposition always exists (a single node whose bag is all of the
vertices), so the infimum in `treewidth` ranges over a nonempty set. The
`Fintype` and `DecidableEq` hypotheses of `treewidth` are the uniform
signature shared by all graph parameters in this archive.
-/

namespace Lax1.Treewidth

/-- A tree decomposition of a simple graph: a finite tree of nodes with a bag
of graph vertices at each node, such that the bags cover every vertex and
every edge, and the nodes whose bags contain any fixed vertex induce a
connected subgraph of the tree. -/
structure TreeDecomposition {V : Type} (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree is finite. -/
  [nodeFintype : Fintype Node]
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

/-- `G` has a tree decomposition all of whose bags have at most `w + 1`
vertices. -/
def HasTreewidthAtMost {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ w + 1

/-- The treewidth of a finite simple graph: the least `w` such that the
graph has a tree decomposition with bags of at most `w + 1` vertices. -/
noncomputable def treewidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {w | HasTreewidthAtMost G w}

end Lax1.Treewidth
