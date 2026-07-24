import Lax5.MonadicDependence
import Lax5.NeighborhoodComplexity

/-!
---
title: Monadically dependent classes have almost linear neighborhood complexity
type: theorem
---
Every monadically dependent graph class has almost linear neighborhood
complexity: for every ε > 0 there is a constant *c* such that every
member *G* and every nonempty vertex subset *A* satisfy
|{N(v) ∩ A : v ∈ V(G)}| ≤ *c* · |A|^(1+ε).

This is Theorem 2 of Dreier, Mählmann, McCarty, Pilipczuk, Toruńczyk,
*Neighborhood Complexity and Radius-1 Merge-Width in Monadically
Dependent Graph Classes* (2026).

# Formalization notes

The hypothesis is the transduction-based definition of monadic
dependence; the conclusion is the shared predicate `HasAlmostLinearNC`
of the neighborhood complexity concept, so this statement and the
nowhere dense counting statement read uniformly.
-/

namespace Lax5.AlmostLinearNC

open Lax5.GraphClasses Lax5.MonadicDependence Lax5.NeighborhoodComplexity

/-- Monadically dependent graph classes have almost linear neighborhood
complexity. -/
axiom hasAlmostLinearNC_of_monadicallyDependent
    (C : GraphClass) (h : MonadicallyDependent C) :
    HasAlmostLinearNC C

end Lax5.AlmostLinearNC
