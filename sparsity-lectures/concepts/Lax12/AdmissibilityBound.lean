import Lax12.Admissibility
import Lax12.ShallowMinorDensity

/-!
---
title: Admissibility is bounded by shallow-minor density
type: theorem
---
If every depth-*r* minor of a graph *G* has at most *d* · |V| edges,
then the *r*-admissibility of *G* is at most 1 + 6 · *r* · *d*³. This is
the workhorse behind every bound of a generalized coloring number by an
edge-density bound: sparse shallow minors force an ordering in which no
vertex reaches many predecessors along disjoint short paths.

# Formalization notes

Hypothesis and conclusion are the predicates of the two imported
definition concepts, at the same depth `r`. The literature proof
establishes the sharper statement in which the hypothesis constrains
only the depth-(*r*−1) *topological* minors of *G*; the form stated here
follows, because every shallow topological minor is a shallow minor and
every depth-(*r*−1) minor is a depth-*r* minor, so the hypothesis here
is the stronger one. Stating it this way keeps shallow topological
minors — an edge-indexed family of routed paths — out of the endorsement
surface and avoids truncated natural subtraction in a hypothesis, at the
cost of the sharper depth index.

The constant is stated exactly as in the source: `1 + 6 · r · d ^ 3`,
with the leading `1` the vertex `v` itself that admissibility counts.
-/

namespace Lax12.AdmissibilityBound

open Lax12.Admissibility Lax12.ShallowMinorDensity

/-- A depth-`r` edge-density bound `d` for `G` bounds the
`r`-admissibility of `G` by `1 + 6 · r · d ^ 3`. -/
axiom adm_le_of_hasDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n))
    (r d : ℕ) (h : HasDensityAtMost G r d) :
    adm G r ≤ 1 + 6 * r * d ^ 3

end Lax12.AdmissibilityBound
