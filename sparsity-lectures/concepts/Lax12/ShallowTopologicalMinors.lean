import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

/-!
---
title: Shallow topological minors
type: definition
---
A graph *H* is a depth-*r* topological minor of a graph *G* if the graph
obtained from *H* by subdividing every edge at most 2*r* times is a
subgraph of *G*: the vertices of *H* are realized by distinct principal
vertices of *G*, and every edge of *H* by a path of length at most
2*r*+1 between the principal vertices of its endpoints, these paths
being internally disjoint from each other and from all principal
vertices. A graph *G* has depth-*r* topological density at most *d* if
every depth-*r* topological minor *H* of *G* has at most *d* · |V(H)|
edges.

In the source lecture notes these are Definitions 2.15 and 2.16 of
Chapter 1 (2019/20 edition): the topological minor relation is written
*H* ⪯^top_*r* *G*, and the topological grad ∇̃_*r*(*G*) is the supremum
of |E(H)|/|V(H)| over the depth-*r* topological minors *H* of *G*, so
the density predicate here says ∇̃_*r*(*G*) ≤ *d*. The length bound
2*r*+1 is the notes' own convention, chosen so that a depth-*r*
topological minor is in particular a depth-*r* minor.

# Formalization notes

The subdivision reading and the model stated here are the same notion:
subdividing an edge *k* times replaces it by a path of length *k*+1, so
a subdivision of *H* with at most 2*r* subdivisions per edge embeds into
*G* exactly when the vertices of *H* can be sent injectively to
principal vertices of *G* and the edges to connecting paths of length at
most 2*r*+1 that are pairwise internally disjoint and avoid all
principal vertices internally. The model carries that data directly.

Connecting walks are indexed by *adjacent pairs* of vertices of `H`
rather than by the edge set, which keeps `Sym2` and its membership
plumbing off the surface. The two orientations of one edge therefore
each carry a walk, and the two are deliberately not required to be
reverses of each other: the `disjoint` field concludes that the two
edges agree, so it never fires on the two orientations of a single edge
and forces nothing between them. Either orientation's walk witnesses
that edge of the subdivision, and a model in the usual edge-indexed form
gives one here by sending the reversed orientation to the reversed walk.

Walks rather than paths, as everywhere in this submission: bypassing a
walk to a path shortens it and shrinks its support, so it preserves both
the length bound and the disjointness conditions, and the two readings
define the same relation. `principal_inj` is not derivable from the
other fields — nothing constrains vertices of `H` that share no edge —
and it is exactly the notes' requirement that principal vertices be
distinct.

No numeric topological grad is introduced, for the reason the
ordinary-minor density concept gives: every statement of this submission
supplies a concrete bound *d* rather than consuming a number, so a
`sInf`-defined ∇̃ would be review surface that no claim uses. Edges are
counted as the natural cardinality (`Set.ncard`) of `edgeSet`, and
minors range over the canonical carriers `Fin m`, as in the
ordinary-minor concepts.
-/

namespace Lax12.ShallowTopologicalMinors

/-- A model of `H` as a depth-`r` topological minor of `G`: an injective
choice of a principal vertex of `G` for each vertex of `H`, together
with a connecting walk of length at most `2 * r + 1` for each edge of
`H`, where the walks pass through no principal vertex other than those
of their own two endpoints and meet each other only in principal
vertices. -/
structure ShallowTopologicalMinorModel {V W : Type*} (r : ℕ) (H : SimpleGraph W)
    (G : SimpleGraph V) where
  /-- The principal vertex of `G` realizing each vertex of `H`. -/
  principal : W → V
  /-- Distinct vertices of `H` have distinct principal vertices. -/
  principal_inj : Function.Injective principal
  /-- The walk of `G` connecting the principal vertices of an edge of
  `H`. -/
  walk : ∀ (u v : W), H.Adj u v → G.Walk (principal u) (principal v)
  /-- Connecting walks have length at most `2 * r + 1`: they subdivide
  the edge at most `2 * r` times. -/
  length_le : ∀ (u v : W) (h : H.Adj u v), (walk u v h).length ≤ 2 * r + 1
  /-- A principal vertex lying on a connecting walk is one of the two
  endpoints of that edge. -/
  principal_eq : ∀ (u v : W) (h : H.Adj u v) (w : W),
    principal w ∈ (walk u v h).support → w = u ∨ w = v
  /-- Connecting walks meet only in principal vertices: a vertex lying
  on two connecting walks and on none of the principal vertices forces
  the two edges to agree. -/
  disjoint : ∀ (u v : W) (h : H.Adj u v) (u' v' : W) (h' : H.Adj u' v') (x : V),
    x ∈ (walk u v h).support → x ∈ (walk u' v' h').support →
      x ∉ Set.range principal → (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')

/-- `H` is a topological minor of `G` at depth `r`. -/
def HasShallowTopologicalMinor {V W : Type*} (G : SimpleGraph V) (r : ℕ)
    (H : SimpleGraph W) : Prop :=
  Nonempty (ShallowTopologicalMinorModel r H G)

/-- Every depth-`r` topological minor of `G`, on `m` vertices, has at
most `d · m` edges. -/
def HasTopologicalDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (r d : ℕ) :
    Prop :=
  ∀ (m : ℕ) (H : SimpleGraph (Fin m)), HasShallowTopologicalMinor G r H →
    H.edgeSet.ncard ≤ d * m

end Lax12.ShallowTopologicalMinors
