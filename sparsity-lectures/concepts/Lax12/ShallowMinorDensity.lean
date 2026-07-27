import Lax12.NowhereDenseClasses
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Edge density of shallow minors
type: definition
---
A graph *G* has depth-*r* density at most *d* if every depth-*r* minor
*H* of *G* has at most *d* · |V(H)| edges — the standard "grad" bound on
how dense the shallow minors of a sparse graph can be. A graph class has
subpolynomial density if for every depth *r* and every ε > 0 there is a
constant *c* such that every depth-*r* minor *H* of a member, on *m*
vertices, has at most *c* · *m*^(1+ε) edges: shallow-minor edge counts
*m*^(1+o(1)).

# Formalization notes

Both predicates are stated over the shallow-minor relation of the
nowhere dense concept, so one notion of depth-*r* minor serves the whole
submission. Minors range over the canonical carriers `Fin m`: every
finite graph is isomorphic to one of those and the shallow-minor
relation is invariant under isomorphism, so nothing is lost.

Edges are counted as the natural cardinality (`Set.ncard`) of
`edgeSet`, which needs no decidability instance and is the exact count
on the finite carriers used here. `HasDensityAtMost` counts edges rather
than twice the edges, matching the usual `|E(H)| ≤ d · |V(H)|` form (the
greatest reduced average density is then at most `2 · d`).

No numeric density parameter is introduced. Every statement of this
submission either supplies a concrete bound `d` or concludes the
class-level predicate, so a `sInf`-defined grad would be review surface
that no claim consumes. The class-level bound carries a multiplicative
constant instead of the size threshold used in the literature proof; the
two agree because a graph on *m* vertices has at most *m*² edges, and
the constant form matches the subpolynomial bound of the coloring-number
concept.
-/

namespace Lax12.ShallowMinorDensity

open Lax12.GraphClasses Lax12.NowhereDenseClasses

/-- Every depth-`r` minor of `G`, on `m` vertices, has at most `d · m`
edges. -/
def HasDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (r d : ℕ) : Prop :=
  ∀ (m : ℕ) (H : SimpleGraph (Fin m)), HasShallowMinor G r H →
    H.edgeSet.ncard ≤ d * m

/-- Every depth-`r` minor of every member of the class, on `m` vertices,
has at most `c · m^(1+ε)` edges, where `c` depends only on the depth `r`
and on `ε > 0`: shallow-minor edge counts `m^(1+o(1))`. -/
def HasSubpolynomialDensity (C : GraphClass) : Prop :=
  ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), HasShallowMinor G r H →
        (H.edgeSet.ncard : ℝ) ≤ c * (m : ℝ) ^ (1 + ε)

end Lax12.ShallowMinorDensity
