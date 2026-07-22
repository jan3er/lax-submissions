import Lax2Proofs.Source.TwinWidth.Matrix.MixedNumber
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Ordered adjacency matrices

This file turns a finite graph together with an order equivalence into a Boolean
adjacency matrix indexed by `Fin n`.
-/

namespace Lax2Proofs.TwinWidth

/-- An ordering of a finite vertex type by `Fin n`. -/
structure VertexOrder (V : Type*) (n : ℕ) where
  /-- The equivalence listing vertices by positions `0, ..., n - 1`. -/
  equiv : Fin n ≃ V

namespace Matrix

/-- The Boolean adjacency matrix of a graph in a chosen vertex order. -/
noncomputable def orderedAdjacency {V : Type*} {n : ℕ} (G : SimpleGraph V) (σ : VertexOrder V n) :
    _root_.Matrix (Fin n) (Fin n) Bool :=
  by
    classical
    exact fun i j => decide (G.Adj (σ.equiv i) (σ.equiv j))

/-- The mixed number of the ordered adjacency matrix of `G`. -/
noncomputable def orderedAdjacencyMixedNumber {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (σ : VertexOrder V n) : ℕ :=
  matrixMixedNumber (orderedAdjacency G σ)

end Matrix
end Lax2Proofs.TwinWidth
