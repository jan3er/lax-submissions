import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths

open Classical

namespace Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility

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

end Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility
