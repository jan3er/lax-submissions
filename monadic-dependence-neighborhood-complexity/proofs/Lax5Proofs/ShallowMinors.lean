import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
Shallow minors in the idiom of the ported sparsity development: graph
classes over varying finite vertex types, minor models carrying paths,
and nowhere denseness by an excluded-clique bound.  Re-homed verbatim
from the catalog modules `Preliminaries`, `ShallowMinor` and
`NowhereDense`, whose own development now lives in the
`sparsity-lectures` submission; what remains here is the vocabulary the
polymorphic bridge files `Lax5Proofs.NowhereDenseBridge` and
`Lax5Proofs.Corollary6a` are stated in.
-/

namespace Lax5Proofs.ShallowMinors

/-- A graph class is a predicate on finite simple graphs, where the vertex type
    may vary. -/
abbrev GraphClass :=
  ∀ {V : Type}, [DecidableEq V] → [Fintype V] → SimpleGraph V → Prop

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

/-- A uniform excluded-clique bound on depth-`d` minors of graphs in `C`.
    The parameter `t` is the allowed clique size, so the excluded graph is
    `K_{t+1}`. -/
def HasShallowCliqueBound (C : GraphClass) (d t : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V),
    C G → ¬IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G d

/-- A class `C` of graphs is nowhere dense if for every depth `d` there is a
    bound `t` such that no graph in `C` contains `K_{t+1}` as a depth-`d`
    minor. (Def 2.6) -/
def IsNowhereDense (C : GraphClass) : Prop :=
  ∀ d : ℕ, ∃ t : ℕ, HasShallowCliqueBound C d t

end Lax5Proofs.ShallowMinors
