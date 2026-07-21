import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
---
title: Tree decomposition and its width
---
$\mathrm{TreeDecomposition}(G)$ is the type of tree decompositions of
the graph $G$. An element consists of a finite node type, a tree $T$ on
that node type, and bags $X_t\subseteq V(G)$ for its nodes, such that every
vertex of $G$ appears in some bag, every edge of $G$ has both endpoints in
some bag, and the set of tree nodes whose bags contain any fixed vertex is
connected in $T$. For such a decomposition $D$,
$\mathrm{treeDecompositionWidth}(D)$ is
$$\max_t |X_t|-1 .$$
The auxiliary definitions $\mathrm{nodeType}(D)$,
$\mathrm{nodeFintype}(D)$, $\mathrm{nodeDecidableEq}(D)$,
$\mathrm{tree}(D)$, and $\mathrm{bag}(D)$ return the displayed
components of $D$.
-/


namespace Lax1.TreeDecompositionWidth

/-- The type of tree decompositions of a graph.  The data are a finite node
type, a tree on that node type, and a bag at each node, together with vertex
coverage, edge coverage, and connectedness of the nodes whose bags contain a
fixed graph vertex. -/
def TreeDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) : Type 1 :=
  Σ Node : Type,
  Σ _nodeFintype : Fintype Node,
  Σ _nodeDecidableEq : DecidableEq Node,
  Σ tree : SimpleGraph Node,
  Σ bag : Node → Finset V,
    PLift (
    tree.IsTree ∧
    (∀ v : V, ∃ i : Node, v ∈ bag i) ∧
    (∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Node, u ∈ bag i ∧ v ∈ bag i) ∧
    (∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected))

/-- The node type of a tree decomposition. -/
def nodeType {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TreeDecomposition G) : Type :=
  Sigma.fst D

/-- The finiteness witness for the node type of a tree decomposition. -/
@[reducible]
def nodeFintype {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TreeDecomposition G) : Fintype (nodeType D) :=
  Sigma.fst (Sigma.snd D)

/-- The decidable-equality witness for the node type of a tree decomposition. -/
@[reducible]
def nodeDecidableEq {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TreeDecomposition G) : DecidableEq (nodeType D) :=
  Sigma.fst (Sigma.snd (Sigma.snd D))

/-- The decomposition tree. -/
def tree {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TreeDecomposition G) : SimpleGraph (nodeType D) :=
  Sigma.fst (Sigma.snd (Sigma.snd (Sigma.snd D)))

/-- The bag assigned to each decomposition node. -/
def bag {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TreeDecomposition G) : nodeType D → Finset V :=
  Sigma.fst (Sigma.snd (Sigma.snd (Sigma.snd (Sigma.snd D))))

/-- The width of a tree decomposition: maximum bag size minus one. -/
noncomputable def treeDecompositionWidth
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TreeDecomposition G) : ℕ :=
  letI : Fintype (nodeType D) := nodeFintype D
  (Finset.univ.sup fun i : nodeType D => (bag D i).card) - 1

end Lax1.TreeDecompositionWidth
