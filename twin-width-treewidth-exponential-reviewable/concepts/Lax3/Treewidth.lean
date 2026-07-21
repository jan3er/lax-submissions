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
The Lean definition uses the value $0$ as a harmless fallback if the defining
set is empty.
-/

namespace Lax3.Treewidth

/-- A tree decomposition of a simple graph. -/
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

/-- The width of a tree decomposition: its largest bag size minus one. -/
noncomputable def treeDecompositionWidth
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TreeDecomposition G) : ℕ :=
  letI : Fintype (nodeType D) := nodeFintype D
  (Finset.univ.sup fun i : nodeType D => (bag D i).card) - 1

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
  leastNat fun width => ∃ D : TreeDecomposition G,
    treeDecompositionWidth D ≤ width

end Lax3.Treewidth
