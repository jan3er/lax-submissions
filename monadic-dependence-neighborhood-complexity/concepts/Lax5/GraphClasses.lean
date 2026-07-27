import Lax12.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
---
title: Weakly sparse graph classes
type: definition
---
A graph class is a set of finite simple graphs: for each number of
vertices *n*, some of the simple graphs on the canonical *n*-element
vertex type. A graph class is weakly sparse if some complete bipartite
graph K_{t,t} occurs in no member as a subgraph.

# Formalization notes

The notion of a graph class is not restated here. `GraphClass` is the
abbreviation of the *Sparsity Lectures* submission (Lax12), imported and
used as is, so that the statements of this submission and the statements
assumed from that one speak about literally the same objects. This
concept adds the two class-level notions this submission needs on top of
it: the class of all graphs, which the definition of monadic dependence
names as the transduction target, and weak sparseness.

Subgraph containment is mathlib's `⊑` (an injective homomorphism of
`completeBipartiteGraph (Fin t) (Fin t)` into the member). The value
`t = 0` does not trivialize weak sparseness: the empty graph is
contained in every graph, so `¬ K_{0,0} ⊑ G` never holds and no side
condition on `t` is needed.
-/

namespace Lax5.GraphClasses

open scoped SimpleGraph
open Lax12.GraphClasses

/-- The class of all finite simple graphs. -/
def allGraphs : GraphClass := fun _ _ => True

/-- A graph class is weakly sparse if some complete bipartite graph
`K_{t,t}` occurs in no member as a subgraph. -/
def WeaklySparse (C : GraphClass) : Prop :=
  ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ completeBipartiteGraph (Fin t) (Fin t) ⊑ G

end Lax5.GraphClasses
