import Lax2Proofs.Source.TwinWidth.Equivalence.FunctionalEquivalence
import Lax2Proofs.Source.TwinWidth.Graph.MixedMinorNumber

/-!
# Twin-width to mixed minor number

This module records the directional bound needed for functional equivalence.
The Section 5 proof of the first twin-width paper provides a linear witness;
with the formal diagonal and mirrored-fusion conventions used for simple graph
adjacency matrices the graph-facing witness is `fun d => 2 * (d + 3) + 2`.
-/

namespace Lax2Proofs.TwinWidth
namespace SimpleGraph

/-- The proposition that mixed minor number is bounded by a numerical function
of twin-width. -/
def MixedMinorNumberBoundedByTwinWidth : Prop :=
  ∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
    mixedMinorNumber G ≤ f (twinWidth G)

/-- The linear bound predicted by the first item of the grid-minor theorem for
twin-width: a `d`-twin-ordered matrix is `(2*d+2)`-mixed-free. -/
def mixedMinorNumberBoundOfTwinWidth (d : ℕ) : ℕ :=
  2 * (d + 3) + 2

/-- Matrix-level ordered-adjacency form of the twin-width-to-mixed direction.

This is the exact interface supplied by Section 5's first item: for every graph,
there is a vertex order whose adjacency matrix has mixed number bounded by a
function of the graph twin-width.  Since `mixedMinorNumber` is the minimum over
orders, this immediately gives the graph-parameter direction below. -/
def OrderedAdjacencyMixedNumberBoundedByTwinWidth (f : ℕ → ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
    ∃ σ : VertexOrder V (Fintype.card V),
      Matrix.orderedAdjacencyMixedNumber G σ ≤ f (twinWidth G)

/-- Passing from a bounded ordered adjacency matrix to the graph mixed minor
number. -/
theorem mixedMinorNumber_le_of_orderedAdjacencyMixedNumber_le
    {V : Type} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {f : ℕ → ℕ}
    {σ : VertexOrder V (Fintype.card V)}
    (hσ : Matrix.orderedAdjacencyMixedNumber G σ ≤ f (twinWidth G)) :
    mixedMinorNumber G ≤ f (twinWidth G) :=
  le_trans (mixedMinorNumber_le_orderedAdjacencyMixedNumber G σ) hσ

/-- The graph-parameter direction follows from the ordered-adjacency matrix
bound. -/
theorem mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyBound
    {f : ℕ → ℕ}
    (h : OrderedAdjacencyMixedNumberBoundedByTwinWidth f) :
    MixedMinorNumberBoundedByTwinWidth := by
  refine ⟨f, ?_⟩
  intro V _ _ G
  rcases h G with ⟨σ, hσ⟩
  exact mixedMinorNumber_le_of_orderedAdjacencyMixedNumber_le (G := G) hσ

/-- The concrete one-direction statement with the project's graph-facing
conventions.  The `+3` accounts for the diagonal/self-zone convention and the
two one-sided child zones introduced by mirroring a graph contraction as row
then column fusions. -/
def OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth : Prop :=
  OrderedAdjacencyMixedNumberBoundedByTwinWidth mixedMinorNumberBoundOfTwinWidth

/-- One functional-equivalence direction with the explicit linear witness,
assuming the Section 5 ordered-adjacency bound. -/
theorem mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyLinearBound
    (h : OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth) :
    MixedMinorNumberBoundedByTwinWidth :=
  mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyBound h

/-- Legacy ordered-adjacency reduction: an ordered-adjacency linear bound
immediately gives the same graph-level bound, because `mixedMinorNumber` is the
minimum over vertex orders. -/
theorem mixed_minor_number_le_twice_twin_width_plus_four_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        ∃ σ : VertexOrder V (Fintype.card V),
          Matrix.orderedAdjacencyMixedNumber G σ ≤ 2 * (twinWidth G + 1) + 2) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      mixedMinorNumber G ≤ 2 * (twinWidth G + 1) + 2 := by
  intro V _ _ G
  rcases h G with ⟨σ, hσ⟩
  exact mixedMinorNumber_le_of_orderedAdjacencyMixedNumber_le
    (G := G) (f := fun d => 2 * (d + 1) + 2) hσ

end SimpleGraph
end Lax2Proofs.TwinWidth
