import Lax5.MonadicDependence
import Lax5.NowhereDenseClasses
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
---
title: Weakly sparse monadically dependent classes are nowhere dense
type: theorem
---
A graph class is weakly sparse if some complete bipartite graph
K_{t,t} occurs in no member as a subgraph. Every weakly sparse
monadically dependent graph class is nowhere dense.

# Formalization notes

Subgraph containment is mathlib's `⊑` (an injective homomorphism of
`completeBipartiteGraph (Fin t) (Fin t)` into the member). The value
`t = 0` does not trivialize weak sparseness: the empty graph is
contained in every graph, so `¬ K_{0,0} ⊑ G` never holds and no side
condition on `t` is needed. `WeaklySparse` is defined here rather than
in the graph classes concept because this statement is its only use.
-/

namespace Lax5.WeaklySparseDependent

open scoped SimpleGraph
open Lax5.GraphClasses Lax5.MonadicDependence Lax5.NowhereDenseClasses

/-- A graph class is weakly sparse if some complete bipartite graph
`K_{t,t}` occurs in no member as a subgraph. -/
def WeaklySparse (C : GraphClass) : Prop :=
  ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ completeBipartiteGraph (Fin t) (Fin t) ⊑ G

/-- Every weakly sparse monadically dependent graph class is nowhere
dense. -/
axiom nowhereDense_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    NowhereDense C

end Lax5.WeaklySparseDependent
