import Lax12.NeighborhoodComplexity
import Lax12.NowhereDenseClasses

/-!
---
title: Nowhere dense classes have almost linear neighborhood complexity
type: theorem
---
Every nowhere dense graph class has almost linear neighborhood
complexity: for every ε > 0 there is a constant *c* such that every
member *G* and every nonempty vertex subset *A* satisfy
|{N(v) ∩ A : v ∈ V(G)}| ≤ *c* · |A|^(1+ε).

This is the radius-1 case of the theorem of Eickmeyer, Giannopoulou,
Kreutzer, Kwon, Pilipczuk, Rabinovich and Siebertz, who prove the
corresponding bound for the traces of *r*-balls for every radius *r*.
The source lecture notes discuss neighborhood complexity but cite the
almost-linear bound as a result of the literature rather than proving
it; the proof accompanying this submission derives the radius-1 case
from the subpolynomial weak-coloring-number theorem stated here.

# Formalization notes

The conclusion is the shared predicate `HasAlmostLinearNC` of the
neighborhood complexity concept; the hypothesis is the shallow-minor
definition of the nowhere dense concept, so the statement adds nothing
of its own. Only radius 1 — traces of neighborhoods rather than of
*r*-balls — is claimed: the general radius is a separate statement with
a separate proof and is not stated here.
-/

namespace Lax12.NowhereDenseNC

open Lax12.GraphClasses Lax12.NeighborhoodComplexity Lax12.NowhereDenseClasses

/-- Nowhere dense graph classes have almost linear neighborhood
complexity. -/
axiom hasAlmostLinearNC_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    HasAlmostLinearNC C

end Lax12.NowhereDenseNC
