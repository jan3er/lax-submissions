import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
---
title: Colored graphs and walk distance
type: definition
---
An *L*-colored graph on *n* vertices is a graph on the vertex set
{0, …, *n* − 1} together with *L* distinguished sets of vertices, its
color classes. The two halves are passed side by side rather than
bundled into a single object: a statement about colored graphs takes a
`SimpleGraph (Fin n)` and a `Coloring n L` as separate arguments.

Two vertices are within distance *d* of each other if some walk between
them has length at most *d*, and the ball of radius *r* around a vertex
is the set of vertices within distance *r* of it. This is the metric the
logic of this submission measures with: its distance atoms and its local
quantifiers are all radius bounds in this sense.

Colored graphs are the structures the first-order logic of this
submission is interpreted in. The source theorem (arXiv:2606.23180)
states its locality theorem over arbitrary finite relational signatures;
fixing the signature to one binary symmetric relation plus finitely many
unary predicates is a genuine specialization, and it is stated here as
one. It is also the full strength that model checking on a class of
*graphs* consumes: the Gaifman graph of a colored graph is the graph
itself, every structure the algorithm builds along the way is the input
graph with edges deleted and colors added, and no step ever leaves this
signature. The same move is made by the MSO concept of submission Lax11,
which pins its logic to MSO₁ rather than claiming a version of
second-order quantification it does not formalize.

# Formalization notes

A colored graph is a pair of arguments, not a structure. Bundling would
force a coercion at every one of the many places where the graph changes
and the coloring does not (deleting the edges incident to a vertex set)
or the coloring changes and the graph does not (recording distance
profiles as new colors), and the concepts of the submissions this one
builds on already pass their data unbundled — the set environments of
Lax11's MSO satisfaction, the graph classes of Lax12. Colors are `Set`s
of vertices rather than a predicate `Fin L → Fin n → Prop` for the same
reason Lax12 states its vertex sets as `Set`s: the two are definitionally
interchangeable and the `Set` form composes with the existing library of
`Set.ncard` cardinality lemmas.

Only finite structures are considered: the vertex type is `Fin n` and
the color index type is `Fin L` throughout. The source's scatter values
may in principle be infinite; over finite structures that case
degenerates and is not carried.

Distance is a predicate on walks, `WithinDist`, and not mathlib's
`SimpleGraph.dist` or `SimpleGraph.edist`. Two vertices are within
distance `d` exactly when some walk between them has length at most `d`,
which needs no connectivity hypothesis, no `ℕ∞` arithmetic and no
decidability instance, and — the deciding reason — it is verbatim the
vocabulary of the sparsity concepts this submission consumes: Lax12's
`DistIndependent` says that every walk between two distinct members of a
set is longer than `r`, so its negation and `WithinDist` are the same
statement. A translation layer between two notions of distance at that
interface would be pure friction.

For the same reason, neither `DistIndependent` nor `deleteVerts` is
restated here. Both are Lax12 concepts, already endorsed, and this
submission uses them as they stand: `deleteVerts G S` — the graph with
every edge incident to `S` removed and the vertex type unchanged — is
exactly the isolation move this submission's splitter game and its
rewriting step perform.

`WithinDist` and `ball` are stated for an arbitrary vertex type, as
Lax12 states `DistIndependent` and `deleteVerts`, since both are
pointwise notions and the proofs consuming them pass through
intermediate carriers. Only `Coloring`, which fixes the two index
ranges, is tied to `Fin`.
-/

namespace Lax3.ColoredGraphs

/-- A coloring of the vertices `Fin n` by `L` colors: one set of
vertices per color. Colors need be neither disjoint nor covering, so a
vertex may carry any set of colors. -/
abbrev Coloring (n L : ℕ) : Type := Fin L → Set (Fin n)

/-- The vertices `u` and `v` are within distance `d` in `G`: some walk
from `u` to `v` has length at most `d`. -/
def WithinDist {V : Type*} (G : SimpleGraph V) (d : ℕ) (u v : V) : Prop :=
  ∃ w : G.Walk u v, w.length ≤ d

/-- The ball of radius `r` around `v` in `G`: the vertices within
distance `r` of `v`. -/
def ball {V : Type*} (G : SimpleGraph V) (r : ℕ) (v : V) : Set V :=
  {u | WithinDist G r v u}

end Lax3.ColoredGraphs
