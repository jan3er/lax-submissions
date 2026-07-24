import Lax5.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
---
title: Nowhere dense graph classes
type: definition
---
A graph *H* is a depth-*r* minor of a graph *G* if *H* can be obtained
from *G* by deleting vertices and edges and contracting pairwise
disjoint connected subgraphs of radius at most *r*. A graph class is
nowhere dense if for every depth *r* there is a *t* such that no member
has the complete graph on *t* vertices as a depth-*r* minor.

# Formalization notes

A depth-`r` minor is witnessed by a `ShallowMinorModel`: pairwise
disjoint branch sets, one per vertex of `H`, and an edge of `G` between
the branch sets of any two adjacent vertices of `H`. The radius
condition — every element of a branch set is reached from its center by
a walk of length at most `r` staying inside the branch set — subsumes
connectivity of the branch sets, so no separate connectivity field is
carried. `center_mem` is not derivable: it also rules out empty branch
sets, as the standard definition requires. `⊤ : SimpleGraph (Fin t)` is
mathlib's complete graph.
-/

namespace Lax5.NowhereDenseClasses

open Lax5.GraphClasses

/-- A model of `H` as a depth-`r` minor of `G`: pairwise disjoint branch
sets, each spanned by walks of length at most `r` from a center vertex
(hence connected of radius at most `r`), with an edge of `G` between the
branch sets of any two adjacent vertices of `H`. -/
structure ShallowMinorModel {V W : Type*} (r : ℕ) (H : SimpleGraph W)
    (G : SimpleGraph V) where
  /-- The branch set of each vertex of `H`. -/
  branch : W → Set V
  /-- The center of each branch set. -/
  center : W → V
  /-- Centers lie in their branch sets (so branch sets are nonempty). -/
  center_mem : ∀ u, center u ∈ branch u
  /-- Distinct branch sets are disjoint. -/
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  /-- Every vertex of a branch set is reached from the center by a walk
  of length at most `r` inside the branch set. -/
  radius_le : ∀ u, ∀ x ∈ branch u, ∃ w : G.Walk (center u) x,
    w.length ≤ r ∧ ∀ y ∈ w.support, y ∈ branch u
  /-- Adjacent vertices of `H` have adjacent branch sets. -/
  adj : ∀ u v, H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

/-- `H` is a minor of `G` at depth `r`. -/
def HasShallowMinor {V W : Type*} (G : SimpleGraph V) (r : ℕ)
    (H : SimpleGraph W) : Prop :=
  Nonempty (ShallowMinorModel r H G)

/-- A graph class is nowhere dense if for every depth `r` some complete
graph is not a depth-`r` minor of any member. -/
def NowhereDense (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ HasShallowMinor G r (⊤ : SimpleGraph (Fin t))

end Lax5.NowhereDenseClasses
