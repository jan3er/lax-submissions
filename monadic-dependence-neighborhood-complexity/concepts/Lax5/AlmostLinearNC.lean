import Lax5.MonadicDependence
import Lax12.NeighborhoodComplexity

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
dependence, the subject of this submission; the conclusion is the
predicate `HasAlmostLinearNC` of the *Sparsity Lectures* submission
(Lax12), where neighborhood complexity is defined and endorsed. Stating
the theorem over that predicate is what makes it directly comparable to
the nowhere dense counting statement there: the same bound, under a
strictly weaker hypothesis.
-/

namespace Lax5.AlmostLinearNC

open Lax12.GraphClasses Lax12.NeighborhoodComplexity Lax5.MonadicDependence

/-- Monadically dependent graph classes have almost linear neighborhood
complexity. -/
axiom hasAlmostLinearNC_of_monadicallyDependent
    (C : GraphClass) (h : MonadicallyDependent C) :
    HasAlmostLinearNC C

end Lax5.AlmostLinearNC
