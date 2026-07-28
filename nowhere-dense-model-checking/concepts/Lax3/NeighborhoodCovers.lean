import Lax3.ColoredGraphs
import Mathlib.Data.Set.Card

/-!
---
title: Sparse neighborhood covers
type: definition
---
An *r*-neighborhood cover of a graph is a family of vertex sets, the
clusters, such that the *r*-ball of every vertex is contained in some
cluster. Its radius is the largest radius of a cluster, and its degree
is the largest number of clusters any one vertex belongs to. A cover
is useful when its radius is not much larger than *r* and its degree
is small: local computations can then be done inside single clusters,
and the degree bounds how often each vertex pays for them.

This is the notion of Grohe–Kreutzer–Siebertz §6 (radius 2*r* there,
as here). It is the load distributor of the model-checking algorithm:
the truth of a local formula at a vertex is decided inside a cluster
containing the vertex's ball, and a degree of *n*^ε caps the total
size of all clusters at *n*^(1+ε).

# Formalization notes

Clusters are indexed by vertices — `X : Fin n → Set (Fin n)`, cluster
`X u` centered at `u` — rather than given as a bare family of sets.
The ordering-based construction that discharges the existence theorem
produces exactly this shape (one cluster per vertex, some possibly
empty, `X u` inside the 2`r`-ball of `u`), the algorithm's
cover-assignment map "read the truth of a formula at `v` inside the
cluster of `f(v)`" needs the index to point at a center, and a bare
family is recovered as the image of the indexing if ever needed.
Centering also makes the radius condition self-witnessing: `X u` lies
in the ball *of its own index*, no existential center.

The three fields quantify over all of `Fin n`, including vertices
outside every cluster of interest; an empty cluster satisfies both the
radius and the degree conditions vacuously, so this costs nothing.
Degree is stated with `Set.ncard`, the cardinality idiom of the Lax12
concepts this submission composes with.
-/

namespace Lax3.NeighborhoodCovers

open Lax3.ColoredGraphs

/-- `X` is an `r`-neighborhood cover of `G` of radius `2r` and degree
`d`: every `r`-ball is inside some cluster, the cluster of `u` lies in
the `2r`-ball of `u`, and no vertex is in more than `d` clusters. -/
structure IsNeighborhoodCover {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ)
    (X : Fin n → Set (Fin n)) (d : ℕ) : Prop where
  /-- Every `r`-ball is contained in some cluster. -/
  ball_subset : ∀ v : Fin n, ∃ u : Fin n, ball G r v ⊆ X u
  /-- Each cluster lies in the `2r`-ball of its center. -/
  subset_ball : ∀ u : Fin n, X u ⊆ ball G (2 * r) u
  /-- No vertex belongs to more than `d` clusters. -/
  degree_le : ∀ v : Fin n, {u : Fin n | v ∈ X u}.ncard ≤ d

end Lax3.NeighborhoodCovers
