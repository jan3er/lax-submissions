import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card

/-!
The generalized coloring numbers and the admissibility of a graph
equipped with a fixed linear order, in the idiom of the ported sparsity
development (`Finset.sup` over the vertices rather than an infimum over
orderings).  This is the merge of the catalog modules `ColoringNumbers`
and `Admissibility`.
-/

namespace Lax12Proofs.OrderedParameters

section

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

end

section

open Classical


noncomputable section

variable {V : Type*} [DecidableEq V] [Fintype V] [LinearOrder V]

/-- An admissible family of paths at vertex `v`. (Def 2.2) -/
structure IsAdmFamily (G : SimpleGraph V) (r : ℕ) (v : V)
    {ι : Type*} (paths : ι → (u : V) × G.Walk v u) : Prop where
  target_lt : ∀ i, (paths i).1 < v
  isPath : ∀ i, (paths i).2.IsPath
  length_le : ∀ i, (paths i).2.length ≤ r
  disjoint : ∀ i j, i ≠ j →
    ∀ w, w ∈ (paths i).2.support → w ∈ (paths j).2.support → w = v

/-- The r-admissibility of a vertex `v`. (Def 2.2) -/
def admVertex (G : SimpleGraph V) (r : ℕ) (v : V) : ℕ :=
  1 + Finset.sup (Finset.range (Fintype.card V)) (fun k =>
    if ∃ (paths : Fin k → (u : V) × G.Walk v u), IsAdmFamily G r v paths
    then k else 0)

/-- The r-admissibility of `G` (per ordering). (Def 2.3) -/
def adm (G : SimpleGraph V) (r : ℕ) : ℕ :=
  Finset.sup Finset.univ (fun v => admVertex G r v)

end

end

end Lax12Proofs.OrderedParameters
