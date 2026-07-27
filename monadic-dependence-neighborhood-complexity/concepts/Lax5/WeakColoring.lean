import Lax5.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Weak coloring numbers
type: definition
---
Fix a linear ordering of the vertices of a graph *G*. A vertex *u* is
weakly *r*-reachable from *v* if some path from *v* to *u* of length
at most *r* has *u* as its smallest vertex. The weak *r*-coloring
number wcol_r(*G*) is the minimum over all orderings of the maximum
number of vertices weakly *r*-reachable from a single vertex. A graph
class has subpolynomial weak coloring numbers if for every radius *r*
and every ε > 0 there is a constant *c* such that every subgraph *H* of
a member, on *m* vertices, satisfies wcol_r(*H*) ≤ *c* · *m*^ε.

# Formalization notes

An ordering of the vertices is a permutation `π` of `Fin m` assigning
each vertex its position. Weak reachability is stated with walks, as
in the nowhere dense concept: shortcutting a walk to a path only
shrinks its support, so walks of length at most `r` with `π`-minimal
endpoint reach exactly the vertices that such paths do. `wcol` is the
least achievable bound `k`, a `Nat.sInf` (attained: `k = m` works for
any ordering); the count is `Set.ncard` as in the neighborhood
complexity concept.

The class-level bound is uniform over subgraph copies (`⊑`, as in the
graph classes concept) of members, each measured by its own vertex
count `m`; this is the literature form for subgraph-closed classes, and
the uniformity is what localization arguments downstream consume. At
`m = 0` both sides vanish, so no nonemptiness hypothesis is needed.
-/

namespace Lax5.WeakColoring

open scoped SimpleGraph
open Lax5.GraphClasses

/-- The set of vertices weakly `r`-reachable from `v` in `G` under the
vertex ordering `π` (vertex `u` sits at position `π u`): the endpoints
`u` of walks from `v` of length at most `r` on whose support `u` is
`π`-minimal. Contains `v` itself. -/
def wreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | ∃ w : G.Walk v u, w.length ≤ r ∧ ∀ y ∈ w.support, π u ≤ π y}

/-- The weak `r`-coloring number of `G`: the least `k` such that under
some vertex ordering every vertex weakly `r`-reaches at most `k`
vertices. -/
noncomputable def wcol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | ∃ π : Equiv.Perm (Fin n), ∀ v, (wreach G π r v).ncard ≤ k}

/-- Every subgraph of every member of the class, on `m` vertices, has
weak `r`-coloring number at most `c · m^ε`, where `c` depends only on
the radius `r` and on `ε > 0`: weak coloring numbers `m^{o(1)}`. -/
def HasSubpolynomialWcol (C : GraphClass) : Prop :=
  ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
        (wcol H r : ℝ) ≤ c * (m : ℝ) ^ ε

end Lax5.WeakColoring
