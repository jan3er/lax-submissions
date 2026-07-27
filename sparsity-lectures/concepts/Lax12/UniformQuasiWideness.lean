import Lax12.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

/-!
---
title: Uniform quasi-wideness
type: definition
---
A set *A* of vertices is distance-*r* independent in *G* if any two
distinct vertices of *A* are at distance more than *r*. A graph class is
uniformly quasi-wide if for every radius *r* there are a threshold
function *N* and a separator bound *s* such that in every member *G*,
every vertex set *A* of size at least *N*(*m*) contains a distance-*r*
independent subset of size at least *m* of *G* − *S*, for some set *S*
of at most *s* vertices.

# Formalization notes

Distance is stated with walks: two vertices are at distance more than
`r` exactly when every walk between them is longer than `r`, which needs
no metric, connectivity or decidability instance. Deleting a vertex set
is modelled by isolating it — `deleteVerts G S` keeps the carrier and
drops every edge incident to `S` — so every set in the statement lives
in the same vertex type and no subtype plumbing enters the surface.
Since the witness satisfies `B ⊆ A \ S`, the isolated vertices are not
in `B` and distance-`r` independence in the isolated graph is the same
as in the induced subgraph on the complement of `S`.

Sets and `Set.ncard` are used throughout, as in the other concepts of
this submission. The threshold `N` may depend on the requested size `m`,
while the separator bound `s` may not: that uniformity in `s` is the
"uniform" of uniform quasi-wideness and is the whole strength of the
notion. `DistIndependent` and `deleteVerts` are stated for an arbitrary
vertex type, since both are pointwise notions and the proofs consuming
them work over intermediate carriers.
-/

namespace Lax12.UniformQuasiWideness

open Lax12.GraphClasses

/-- A set of vertices is distance-`r` independent in `G` when every walk
between two distinct members is longer than `r`. -/
def DistIndependent {V : Type*} (G : SimpleGraph V) (r : ℕ) (A : Set V) : Prop :=
  A.Pairwise fun u v => ∀ p : G.Walk u v, r < p.length

/-- `G` with the vertices of `S` isolated: every edge incident to `S` is
removed and the vertex type is unchanged. This models `G − S`. -/
def deleteVerts {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

/-- A graph class is uniformly quasi-wide if for every radius `r` there
are a threshold function `N` and a separator bound `s` such that in
every member, every vertex set of size at least `N m` contains a
distance-`r` independent subset of size at least `m` after deleting at
most `s` vertices. -/
def UniformlyQuasiWide (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ (N : ℕ → ℕ) (s : ℕ),
    ∀ (m n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Set (Fin n), N m ≤ A.ncard →
        ∃ S B : Set (Fin n),
          S.ncard ≤ s ∧ B ⊆ A \ S ∧ m ≤ B.ncard ∧
          DistIndependent (deleteVerts G S) r B

end Lax12.UniformQuasiWideness
