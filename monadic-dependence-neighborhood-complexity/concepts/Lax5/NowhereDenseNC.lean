import Lax5.NeighborhoodComplexity
import Lax5.NowhereDenseClasses

/-!
---
title: Nowhere dense classes have almost linear neighborhood complexity
type: theorem
---
Every nowhere dense graph class has almost linear neighborhood
complexity: for every ε > 0 there is a constant *c* such that every
member *G* and every nonempty vertex subset *A* satisfy
|{N(v) ∩ A : v ∈ V(G)}| ≤ *c* · |A|^(1+ε).

# Formalization notes

The conclusion is the shared predicate `HasAlmostLinearNC` of the
neighborhood complexity concept; the hypothesis is the shallow-minor
definition of the nowhere dense concept. This is the radius-1 case of a
classical result on nowhere dense classes (Eickmeyer, Giannopoulou,
Kreutzer, Kwon, Pilipczuk, Rabinovich, Siebertz).
-/

namespace Lax5.NowhereDenseNC

open Lax5.GraphClasses Lax5.NeighborhoodComplexity Lax5.NowhereDenseClasses

/-- Nowhere dense graph classes have almost linear neighborhood
complexity. -/
axiom hasAlmostLinearNC_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    HasAlmostLinearNC C

end Lax5.NowhereDenseNC
