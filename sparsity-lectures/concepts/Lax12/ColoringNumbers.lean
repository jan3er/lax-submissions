import Lax12.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Generalized coloring numbers
type: definition
---
Fix a linear ordering of the vertices of a graph *G*. A vertex *u* is
weakly *r*-reachable from *v* if some path from *v* to *u* of length at
most *r* has *u* as its smallest vertex, and strongly *r*-reachable from
*v* if some path from *v* to *u* of length at most *r* has *v* as its
smallest vertex apart from *u* itself. The weak *r*-coloring number
wcol_r(*G*) and the strong *r*-coloring number scol_r(*G*) are the
minima, over all orderings, of the largest number of vertices weakly
respectively strongly *r*-reachable from a single vertex. A graph class
has subpolynomial weak coloring numbers if for every radius *r* and
every ε > 0 there is a constant *c* such that every subgraph *H* of a
member, on *m* vertices, satisfies wcol_r(*H*) ≤ *c* · *m*^ε.

Weak and strong reachability are Definition 2.1, and the two coloring
numbers Definition 2.3, of Chapter 2 of the source lecture notes
(2019/20 edition), which write scol_*r* where the earlier 2017/18
edition writes col_*r*. The subpolynomial bound is the conclusion of
Theorem 3.4 of that chapter.

# Formalization notes

An ordering of the vertices is a permutation `π` of `Fin m` assigning
each vertex its position. Both reachability sets are stated with walks,
as in the nowhere dense concept: shortcutting a walk to a path only
shrinks its support, so walks of length at most `r` reach exactly the
vertices that such paths do. In `wreach` the `π`-minimality of `u` on
the whole support already forces `π u ≤ π v`; in `sreach` only the
interior of the walk is constrained, so `π u ≤ π v` is a separate
conjunct. Both sets contain `v`.

`wcol` and `scol` are the least achievable bounds `k`, `Nat.sInf`s over
nonempty sets — `k = m` works for any ordering — so the convention
`Nat.sInf ∅ = 0` is never exercised; the counts are `Set.ncard`. Weak
and strong coloring numbers are one review unit because they are the
same construction differing in a single clause, and every relation
between them is read off that contrast.

The class-level bound is uniform over subgraph copies (`⊑`) of members,
each measured by its own vertex count `m`; this is the literature form
for subgraph-closed classes, and the uniformity is what localization
arguments downstream consume. At `m = 0` both sides vanish, so no
nonemptiness hypothesis is needed.
-/

namespace Lax12.ColoringNumbers

open scoped SimpleGraph
open Lax12.GraphClasses

/-- The set of vertices weakly `r`-reachable from `v` in `G` under the
vertex ordering `π` (vertex `u` sits at position `π u`): the endpoints
`u` of walks from `v` of length at most `r` on whose support `u` is
`π`-minimal. Contains `v` itself. -/
def wreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | ∃ w : G.Walk v u, w.length ≤ r ∧ ∀ y ∈ w.support, π u ≤ π y}

/-- The set of vertices strongly `r`-reachable from `v` in `G` under the
vertex ordering `π`: the vertices `u` at or before `v` that are the
endpoint of a walk from `v` of length at most `r` all of whose other
vertices come strictly after `v`. Contains `v` itself. -/
def sreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | π u ≤ π v ∧ ∃ w : G.Walk v u, w.length ≤ r ∧
    ∀ y ∈ w.support, y ≠ v → y ≠ u → π v < π y}

/-- The weak `r`-coloring number of `G`: the least `k` such that under
some vertex ordering every vertex weakly `r`-reaches at most `k`
vertices. -/
noncomputable def wcol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | ∃ π : Equiv.Perm (Fin n), ∀ v, (wreach G π r v).ncard ≤ k}

/-- The strong `r`-coloring number of `G`: the least `k` such that under
some vertex ordering every vertex strongly `r`-reaches at most `k`
vertices. -/
noncomputable def scol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | ∃ π : Equiv.Perm (Fin n), ∀ v, (sreach G π r v).ncard ≤ k}

/-- Every subgraph of every member of the class, on `m` vertices, has
weak `r`-coloring number at most `c · m^ε`, where `c` depends only on
the radius `r` and on `ε > 0`: weak coloring numbers `m^{o(1)}`. -/
def HasSubpolynomialWcol (C : GraphClass) : Prop :=
  ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
        (wcol H r : ℝ) ≤ c * (m : ℝ) ^ ε

end Lax12.ColoringNumbers
