import Mathlib.Combinatorics.SimpleGraph.Basic
import Lax1.SingletonBags
import Lax1.TrigraphState

/-!
---
title: Initial trigraph state of a graph
---
$\mathrm{InitialState}(G)$ is the subtype of trigraph states whose bags
are the singleton bags
$$\{\{v\}:v\in V(G)\},$$
whose black adjacency between two bags means that there is an edge of $G$
between a vertex in the first bag and a vertex in the second bag, and whose red
adjacency relation is empty.

For $I:\mathrm{InitialState}(G)$, $\mathrm{state}(I)$ is its
underlying trigraph state.
-/


namespace Lax1.InitialTrigraphState

open Lax1.SingletonBags
open Lax1.TrigraphState

/-- The type of initial trigraph states associated with a graph.  Such a state
has singleton bags, black adjacency exactly when the graph has an edge between
the two bags, and no red adjacency. -/
def InitialState {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Type :=
  Σ state : State V,
    PLift (
    bags state = singletonBags V ∧
    (∀ ⦃A B⦄, A ∈ bags state → B ∈ bags state →
      (blackAdj state A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b)) ∧
    (∀ ⦃A B⦄, A ∈ bags state → B ∈ bags state →
      ¬ redAdj state A B))

/-- The underlying trigraph state of an initial state. -/
def state {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (I : InitialState G) : State V :=
  Sigma.fst I

end Lax1.InitialTrigraphState
