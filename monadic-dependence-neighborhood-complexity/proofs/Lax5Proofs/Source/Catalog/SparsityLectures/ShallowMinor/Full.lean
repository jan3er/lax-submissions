import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor

/-- A depth-`d` minor model of `H` in `G`.

For each vertex of `H` we choose a branch set in `G` together with a fixed
center. Every vertex of the branch set is connected to the center by a path of
length at most `d` that stays inside the branch set; distinct branch sets are
disjoint; and every edge of `H` is witnessed by an edge of `G` between the
corresponding branch sets. (Defs 1.10, 2.2-2.4) -/
structure ShallowMinorModel {V W : Type} (H : SimpleGraph W) (G : SimpleGraph V)
    (d : ℕ) where
  branchSet : W → Set V
  center : W → V
  center_mem : ∀ v, center v ∈ branchSet v
  branchDisjoint : ∀ u v, u ≠ v → Disjoint (branchSet u) (branchSet v)
  branchRadius : ∀ v x, x ∈ branchSet v →
    ∃ p : G.Walk (center v) x, p.IsPath ∧ p.length ≤ d ∧
      ∀ w ∈ p.support, w ∈ branchSet v
  branchEdge : ∀ u v, H.Adj u v →
    ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y

/-- `H` is a depth-`d` minor of `G`. -/
def IsShallowMinor {V W : Type} (H : SimpleGraph W) (G : SimpleGraph V)
    (d : ℕ) : Prop :=
  Nonempty (ShallowMinorModel H G d)

end Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor
