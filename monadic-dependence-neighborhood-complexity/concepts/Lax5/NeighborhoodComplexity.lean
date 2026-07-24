import Lax5.GraphClasses
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Neighborhood complexity
type: definition
---
The neighborhood complexity of a graph *G* on a vertex set *A* counts
the distinct traces of vertex neighborhoods on *A*, that is, the sets
*N(v) ∩ A* for *v* ranging over all vertices of *G*. A graph class has
almost linear neighborhood complexity if for every ε > 0 there is a
constant *c* such that every member *G* and every nonempty vertex subset
*A* leave at most *c* · |A|^(1+ε) traces — neighborhood complexity
|A|^(1+o(1)).

# Formalization notes

The trace count is the natural cardinality (`Set.ncard`) of the set of
traces; on the finite carriers where it is used this is the exact count.
(Over an infinite vertex type with infinitely many traces `ncard` takes
the junk value 0; every use in this submission is on `Fin n`.) Working
with `Set` rather than `Finset` keeps the trace literally `N(v) ∩ A`
and needs no decidability instances.

The bound is stated for nonempty `A` only: the empty set always has
exactly one trace (the empty trace), while `c · 0^(1+ε) = 0`, so the
literal inequality must exclude `A = ∅` — and nothing is lost by doing
so. The exponent is a real power of the cast cardinality, and the
constant `c` is real.
-/

namespace Lax5.NeighborhoodComplexity

open Lax5.GraphClasses

/-- The number of distinct neighborhood traces `N(v) ∩ A` that the
vertices of `G` leave on the vertex set `A`. -/
noncomputable def traceCount {V : Type*} (G : SimpleGraph V)
    (A : Set V) : ℕ :=
  {S : Set V | ∃ v : V, S = G.neighborSet v ∩ A}.ncard

/-- Every graph in the class leaves at most `c · |A|^(1+ε)` neighborhood
traces on every nonempty vertex subset `A`, where `c` depends only on
`ε > 0`: neighborhood complexity `|A|^(1+o(1))`. -/
def HasAlmostLinearNC (C : GraphClass) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Set (Fin n), A.Nonempty →
        (traceCount G A : ℝ) ≤ c * (A.ncard : ℝ) ^ (1 + ε)

end Lax5.NeighborhoodComplexity
