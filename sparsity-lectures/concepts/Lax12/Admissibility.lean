import Lax12.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Nat.Lattice

/-!
---
title: Admissibility
type: definition
---
Fix a linear ordering of the vertices of a graph *G*. An admissible
family of size *k* at a vertex *v* consists of *k* paths of length at
most *r* that start at *v*, end at vertices smaller than *v*, and are
pairwise disjoint apart from *v*. The *r*-admissibility adm_r(*G*) is
the minimum over all orderings of the largest *k* + 1 for which some
vertex of *G* carries an admissible family of size *k*. Counting *v*
itself is the usual convention: it makes admissibility at least 1 and at
most the strong *r*-coloring number.

# Formalization notes

The ordering is a permutation `π` of `Fin n`, as in the coloring-number
concept, and the family is indexed by `Fin k`, so its size is the
parameter of the structure rather than a derived cardinality. Paths are
stated as walks, as everywhere in this submission: bypassing a walk to a
path shrinks its support, so a family of walks meeting only in `v`
yields a family of paths meeting only in `v` of the same size, and the
two readings define the same largest `k`.

The endpoints of a family are automatically pairwise distinct — a shared
endpoint would lie on two paths and differ from `v` — so no injectivity
field is carried. `HasAdmAtMost G r k` says that some ordering admits no
family of `k` paths anywhere, and `adm` is the least such `k`. The set
is nonempty (`k = n + 1` always qualifies, since a family's endpoints
are `k` distinct vertices other than `v`), so `Nat.sInf ∅ = 0` is never
exercised; on the empty graph every bound holds vacuously and `adm`,
`wcol`, `scol` are all `0`.
-/

namespace Lax12.Admissibility

open Lax12.GraphClasses

/-- An admissible family of `k` paths at `v` under the ordering `π`:
`k` walks of length at most `r` out of `v`, each ending strictly before
`v` in the ordering, pairwise meeting only in `v`. -/
structure AdmFamily {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (r k : ℕ) (v : Fin n) where
  /-- The endpoint of each path. -/
  target : Fin k → Fin n
  /-- The path from `v` to each endpoint. -/
  path : ∀ i, G.Walk v (target i)
  /-- Every endpoint comes strictly before `v` in the ordering. -/
  target_lt : ∀ i, π (target i) < π v
  /-- Every path has length at most `r`. -/
  length_le : ∀ i, (path i).length ≤ r
  /-- Distinct paths meet only in `v`. -/
  meet_eq : ∀ i j, i ≠ j → ∀ y ∈ (path i).support,
    y ∈ (path j).support → y = v

/-- Some vertex ordering admits no admissible family of `k` paths at any
vertex: the `r`-admissibility is at most `k`. -/
def HasAdmAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ) : Prop :=
  ∃ π : Equiv.Perm (Fin n), ∀ (v : Fin n) (j : ℕ),
    Nonempty (AdmFamily G π r j v) → j + 1 ≤ k

/-- The `r`-admissibility of `G`: the least bound achieved by some
vertex ordering. -/
noncomputable def adm {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | HasAdmAtMost G r k}

end Lax12.Admissibility
