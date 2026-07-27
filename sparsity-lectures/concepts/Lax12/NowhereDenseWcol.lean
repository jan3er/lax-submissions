import Lax12.NowhereDenseClasses
import Lax12.ColoringNumbers

/-!
---
title: Nowhere dense classes have subpolynomial weak coloring numbers
type: theorem
---
Every nowhere dense graph class has subpolynomial weak coloring
numbers: for every radius *r* and every ε > 0 there is a constant *c*
such that every subgraph *H* of a member, on *m* vertices, satisfies
wcol_r(*H*) ≤ *c* · *m*^ε.

# Formalization notes

The hypothesis is the shallow-minor definition of the nowhere dense
concept; the conclusion is the shared predicate `HasSubpolynomialWcol`
of the coloring-number concept. Since nowhere denseness survives taking
subgraphs, the uniformity of that predicate over subgraph copies of
members loses nothing here. This is the headline of the submission and
is the composition of the four preceding theorem concepts: subpolynomial
shallow-minor density, the admissibility bound, and the two links of the
coloring-number chain.
-/

namespace Lax12.NowhereDenseWcol

open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ColoringNumbers

/-- Nowhere dense graph classes have subpolynomial weak coloring
numbers. -/
axiom hasSubpolynomialWcol_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    HasSubpolynomialWcol C

end Lax12.NowhereDenseWcol
