import Lax2Proofs.Source.TwinWidth.Matrix.OrderedAdjacency

/-!
# Mixed minor number of finite simple graphs

The mixed minor number of a finite graph is the minimum, over all vertex
orderings, of the mixed number of the ordered adjacency matrix.
-/

namespace Lax2Proofs.TwinWidth
namespace SimpleGraph

/-- There is always at least one vertex order of length `Fintype.card V`. -/
theorem exists_vertexOrder_card (V : Type*) [Fintype V] :
    Nonempty (VertexOrder V (Fintype.card V)) := by
  classical
  exact ⟨⟨(Fintype.equivFin V).symm⟩⟩

/-- There is always an ordered-adjacency mixed number realized by some order. -/
theorem exists_orderedAdjacencyMixedNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    ∃ k, ∃ σ : VertexOrder V (Fintype.card V),
      Matrix.orderedAdjacencyMixedNumber G σ = k := by
  classical
  let σ : VertexOrder V (Fintype.card V) := ⟨(Fintype.equivFin V).symm⟩
  exact ⟨Matrix.orderedAdjacencyMixedNumber G σ, σ, rfl⟩

/-- The mixed minor number graph parameter: the minimum mixed number of an
ordered adjacency matrix over all vertex orderings. -/
noncomputable def mixedMinorNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℕ :=
  by
    classical
    exact Nat.find (exists_orderedAdjacencyMixedNumber G)

/-- Some vertex ordering realizes the graph mixed minor number. -/
theorem exists_order_mixedNumber_eq_mixedMinorNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    ∃ σ : VertexOrder V (Fintype.card V),
      Matrix.orderedAdjacencyMixedNumber G σ = mixedMinorNumber G := by
  classical
  simpa [mixedMinorNumber] using Nat.find_spec (exists_orderedAdjacencyMixedNumber G)

/-- The graph mixed minor number is at most the mixed number of every ordered
adjacency matrix with the canonical cardinality-sized index type. -/
theorem mixedMinorNumber_le_orderedAdjacencyMixedNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (σ : VertexOrder V (Fintype.card V)) :
    mixedMinorNumber G ≤ Matrix.orderedAdjacencyMixedNumber G σ := by
  classical
  exact Nat.find_min' (exists_orderedAdjacencyMixedNumber G)
    ⟨σ, rfl⟩

theorem mixedMinorNumber_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    mixedMinorNumber G ≤ Fintype.card V := by
  classical
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  rw [← hσ]
  simpa [Matrix.orderedAdjacencyMixedNumber] using
    (Matrix.matrixMixedNumber_le_min_card (Matrix.orderedAdjacency G σ))

end SimpleGraph
end Lax2Proofs.TwinWidth
