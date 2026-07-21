import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Ordered adjacency matrix of a graph
---
Listing the vertices of a finite graph $G$ in some order — given as a
bijection $e : \mathrm{Fin}(n) \simeq V$ — yields the Boolean *ordered
adjacency matrix* with entry $(i,j)$ true exactly when $e(i)$ and $e(j)$ are
adjacent in $G$.
-/

namespace Lax2.OrderedAdjacency

noncomputable section

/-- The Boolean adjacency matrix of a graph in a chosen vertex order. -/
def orderedAdjacency {V : Type} {n : ℕ}
    (G : SimpleGraph V) (e : Fin n ≃ V) : Fin n → Fin n → Bool :=
  fun i j =>
    letI : Decidable (G.Adj (e i) (e j)) := Classical.propDecidable _
    decide (G.Adj (e i) (e j))

end

end Lax2.OrderedAdjacency
