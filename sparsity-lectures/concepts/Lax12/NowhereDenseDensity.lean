import Lax12.NowhereDenseClasses
import Lax12.ShallowMinorDensity

/-!
---
title: Nowhere dense classes have subpolynomial shallow-minor density
type: theorem
---
Every nowhere dense graph class has subpolynomial density: for every
depth *r* and every ε > 0 there is a constant *c* such that every
depth-*r* minor of a member, on *m* vertices, has at most
*c* · *m*^(1+ε) edges. Together with the reverse implication — which is
immediate, since a large clique as a shallow minor forces quadratically
many edges — this is the density characterization of nowhere denseness.

The source lecture notes state the implication as Theorem 3.1 of
Chapter 1 (2019/20 edition), in the threshold form "*G* has fewer than
*n*^(1+ε) edges once *n* ≥ *N*(*r*, ε)", and credit the proof they
present to Zdeněk Dvořák.

# Formalization notes

Both hypothesis and conclusion are the shared predicates of the imported
definition concepts. The bound is uniform over all members of the class
and all their depth-*r* minors, with the constant depending only on the
depth and on ε; that uniformity is what the coloring-number chain
downstream consumes. The multiplicative form used here is the one the
notes themselves record as equivalent to their threshold form,
immediately after the theorem: a graph on *m* vertices has at most *m*²
edges, so the finitely many sizes below the threshold are absorbed into
the constant. Only the stated direction is claimed: the easy converse is
a separate statement and is not conjoined here.
-/

namespace Lax12.NowhereDenseDensity

open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ShallowMinorDensity

/-- Nowhere dense graph classes have subpolynomial shallow-minor
density. -/
axiom hasSubpolynomialDensity_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    HasSubpolynomialDensity C

end Lax12.NowhereDenseDensity
