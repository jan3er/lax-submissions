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

This is Theorem 3.4 of Chapter 2 of the source lecture notes (2019/20
edition).

# Formalization notes

The hypothesis is the shallow-minor definition of the nowhere dense
concept; the conclusion is the shared predicate `HasSubpolynomialWcol`
of the coloring-number concept. The notes state the bound for the
members of the class only, whereas the predicate used here demands it
uniformly for all subgraphs of members; the two are equivalent, because
the subgraphs of the members of a nowhere dense class again form a
nowhere dense class, and the subgraph-uniform form is what downstream
localization arguments consume. It is also the form of the identically
named predicate in the neighborhood-complexity submission, so the
statement transports there definitionally. This is the headline of the
submission and
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
