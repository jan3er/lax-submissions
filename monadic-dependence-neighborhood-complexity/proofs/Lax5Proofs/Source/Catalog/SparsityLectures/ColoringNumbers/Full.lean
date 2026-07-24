import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card

namespace Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers

variable {V : Type*} [DecidableEq V] [Fintype V] [LinearOrder V]

/-- The set of vertices strongly r-reachable from `v` with respect to the
    linear order on `V`. A vertex `u ≤ v` is in `SReach G r v` when there
    exists a path of length ≤ r from `v` to `u` whose internal vertices
    are all strictly greater than `v`. (Def 2.1) -/
def SReach (G : SimpleGraph V) (r : ℕ) (v : V) : Set V :=
  {u | u ≤ v ∧ ∃ p : G.Walk v u, p.IsPath ∧ p.length ≤ r ∧
    ∀ i : ℕ, 0 < i → i < p.length → v < p.getVert i}

/-- The set of vertices weakly r-reachable from `v` with respect to the
    linear order on `V`. A vertex `u ≤ v` is in `WReach G r v` when there
    exists a path of length ≤ r from `v` to `u` whose internal vertices
    are all strictly greater than `u`. (Def 2.1) -/
def WReach (G : SimpleGraph V) (r : ℕ) (v : V) : Set V :=
  {u | u ≤ v ∧ ∃ p : G.Walk v u, p.IsPath ∧ p.length ≤ r ∧
    ∀ i : ℕ, 0 < i → i < p.length → u < p.getVert i}

open Classical in
/-- The weak r-coloring number of `G` (per ordering). (Def 2.3) -/
noncomputable def wcol (G : SimpleGraph V) (r : ℕ) : ℕ :=
  Finset.sup Finset.univ (fun v => (WReach G r v).ncard)

open Classical in
/-- The strong r-coloring number of `G` (per ordering). (Def 2.3) -/
noncomputable def scol (G : SimpleGraph V) (r : ℕ) : ℕ :=
  Finset.sup Finset.univ (fun v => (SReach G r v).ncard)

end Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers
