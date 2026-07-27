import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
---
title: Graph classes
type: definition
---
A graph class is a set of finite simple graphs. A class contains, for
each number of vertices *n*, some of the simple graphs on the canonical
*n*-element vertex type. A graph class is weakly sparse if some complete
bipartite graph K_{t,t} occurs in no member as a subgraph.

# Formalization notes

Every finite simple graph is isomorphic to a graph on some `Fin n`, so
ranging over the canonical carriers loses no generality. Closure under
isomorphism is deliberately not required: no statement of this
submission needs it, and all hypotheses range over concrete members.
`GraphClass` is an abbreviation, so class membership is plain
application `C n G` throughout the submission.

Subgraph containment is mathlib's `⊑` (an injective homomorphism of
`completeBipartiteGraph (Fin t) (Fin t)` into the member). The value
`t = 0` does not trivialize weak sparseness: the empty graph is
contained in every graph, so `¬ K_{0,0} ⊑ G` never holds and no side
condition on `t` is needed.
-/

namespace Lax5.GraphClasses

open scoped SimpleGraph

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

/-- The class of all finite simple graphs. -/
def allGraphs : GraphClass := fun _ _ => True

/-- A graph class is weakly sparse if some complete bipartite graph
`K_{t,t}` occurs in no member as a subgraph. -/
def WeaklySparse (C : GraphClass) : Prop :=
  ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ completeBipartiteGraph (Fin t) (Fin t) ⊑ G

end Lax5.GraphClasses
