import Lax5.NowhereDenseClasses
import Lax5.WeakColoring

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
of the weak coloring concept. Since nowhere denseness survives taking
subgraphs, the uniformity of that predicate over subgraph copies of
members loses nothing here. The theorem combines Zhu's bounds relating
weak coloring numbers to densities of shallow minors with the
subpolynomial density bounds for nowhere dense classes (Nešetřil,
Ossona de Mendez); see chapters 2 and 5 of the sparsity lecture notes
of Pilipczuk, Pilipczuk, Siebertz.
-/

namespace Lax5.NowhereDenseWcol

open Lax5.GraphClasses Lax5.NowhereDenseClasses Lax5.WeakColoring

/-- Nowhere dense graph classes have subpolynomial weak coloring
numbers. -/
axiom hasSubpolynomialWcol_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    HasSubpolynomialWcol C

end Lax5.NowhereDenseWcol
