import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries.Full

open Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries

namespace Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness

/-- A set `A` of vertices is distance-`r` independent in `G` when every two
    distinct vertices in `A` have no walk of length ≤ `r` between them. -/
def DistIndependent {V : Type} (G : SimpleGraph V) (r : ℕ) (A : Set V) : Prop :=
  A.Pairwise (fun u v => ∀ (p : G.Walk u v), r < p.length)

/-- `deleteVerts G S` removes all edges incident to vertices in `S`, keeping
    the vertex type `V` unchanged. This models `G - S`. -/
def deleteVerts {V : Type} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

/-- A class `C` of graphs is uniformly quasi-wide if for every radius `r`
    there exist a threshold function `N` and a separator size bound `s` such
    that in every graph `G ∈ C`, every vertex set `A` of size at least `N(m)`
    contains a subset `B` of size at least `m` that is distance-`r` independent
    after removing at most `s` vertices. (Def 3.1) -/
def UniformlyQuasiWide (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ (N : ℕ → ℕ) (s : ℕ),
    ∀ (m : ℕ) {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V),
      C G → ∀ (A : Finset V), N m ≤ A.card →
        ∃ (S : Finset V) (B : Finset V),
          S.card ≤ s ∧
          ↑B ⊆ ↑A \ ↑S ∧
          m ≤ B.card ∧
          DistIndependent (deleteVerts G ↑S) r ↑B

end Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness
