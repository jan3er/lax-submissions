import Lax2Proofs.Source.TwinWidth.Equivalence.MixedToTwinWidth
import Lax2Proofs.Source.TwinWidth.Graph.TwinDecomposition

/-!
# Main equivalence statement from directional bounds

This file contains the theorem-combiner layer.  The two hard mathematical
ingredients are the directional bounds recorded in the imported modules.
-/

namespace Lax2Proofs.TwinWidth

open SimpleGraph

/-- The two directional bounds imply functional equivalence of twin-width and
mixed minor number. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds
    (h₁ : TwinWidthBoundedByMixedMinorNumber)
    (h₂ : MixedMinorNumberBoundedByTwinWidth) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  exact ⟨h₁, h₂⟩

/-- Functional equivalence from the hard mixed-to-twin-width bound and the
Section 5 ordered-adjacency form of the twin-width-to-mixed direction. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_mixedToTwinWidth_and_orderedAdjacency
    (h₁ : TwinWidthBoundedByMixedMinorNumber)
    (h₂ : OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  exact twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds h₁
    (mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyLinearBound h₂)

/-- Functional equivalence from the two ordered-adjacency matrix bounds supplied
by the grid-minor theorem for twin-width. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_orderedAdjacencyBounds
    (h₁ : TwinWidthBoundedByOrderedAdjacencyMixedNumberExplicit)
    (h₂ : OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  exact twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds
    (twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyExplicitBound h₁)
    (mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyLinearBound h₂)

/-- Contract theorem for
`MainContract.twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds`.

The two explicit directional inequalities imply functional equivalence. -/
theorem twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds
    (h₁ :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G))
    (h₂ :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        mixedMinorNumber G ≤ 2 * (twinWidth G + 3) + 2) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  constructor
  · refine ⟨twinWidthBoundOfMixedMinorNumber, ?_⟩
    intro V _ _ G
    exact h₁ G
  · refine ⟨fun d => 2 * (d + 3) + 2, ?_⟩
    intro V _ _ G
    exact h₂ G

/-- Functional equivalence from the two graph/matrix bridge constructions:

* the left-to-right leaf order of a width-`twinWidth G` twin-decomposition
  makes the ordered adjacency matrix twin-ordered, and
* the symmetric version of the matrix Theorem 10 construction turns every
  mixed-free ordered adjacency matrix into a graph partition sequence.

These are precisely the two graph-facing constructions described around
Theorem 14. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_graph_matrix_bridges
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G))
    (hconstruct :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
        (σ : VertexOrder V (Fintype.card V)) (t : ℕ),
          Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
            Nonempty (GraphPartitionSequence G (theorem14MixedFreeTwinWidthBound t))) :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds
    (fun G => theorem14_twinWidth_le_mixedMinorNumber G (hconstruct G))
    (mixed_minor_number_le_twice_twin_width_plus_eight_of_twinDecomposition hdecomp)

/-- Functional equivalence from the two remaining natural-language
constructions:

* the left-to-right leaf order of a width-`twinWidth G` twin-decomposition
  makes the ordered adjacency matrix twin-ordered, and
* the mirrored matrix Theorem 10 construction gives symmetric matrix
  contraction sequences for mixed-free square Boolean matrices.

The graph interpretation of the symmetric matrix sequence is proved in
`Graph.Theorem14`. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition_and_symmetricMatrix
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G))
    (hmatrix : Matrix.SymmetricMatrixTwinWidthBoundedByMixedFree) :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds
    (fun G =>
      theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixConstruction G
        (fun σ t hfree => by
          simpa [theorem14MixedFreeTwinWidthBound] using
            hmatrix (Matrix.orderedAdjacency G σ)
              (orderedAdjacency_isSymmetricMatrix G σ) hfree))
    (mixed_minor_number_le_twice_twin_width_plus_eight_of_twinDecomposition hdecomp)

/-- Functional equivalence from the leaf-order twin-decomposition and the
remaining symmetric refinement constructor.  The expansion of that symmetric
refinement sequence into paired row/column matrix contractions is proved in
`Matrix.Symmetric`. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition_and_symmetricErrorRefinement
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G))
    (hrefine : Matrix.SymmetricMatrixErrorRefinementBoundedByMixedFree) :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition_and_symmetricMatrix
    hdecomp
    (Matrix.symmetricMatrixTwinWidthBoundedByMixedFree_of_symmetricErrorRefinement hrefine)

/-- Functional equivalence with the mirrored matrix/Theorem 14 side fully
discharged.  The only remaining graph-facing construction is the leaf-order
twin-decomposition for the twin-width-to-mixed direction. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G)) :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds
    SimpleGraph.twinWidthBoundedByMixedMinorNumber
    ⟨mixedMinorNumberBoundOfTwinWidth,
      mixed_minor_number_le_twice_twin_width_plus_eight_of_twinDecomposition hdecomp⟩

/-- The completed functional equivalence between graph twin-width and graph
mixed minor number. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition
    SimpleGraph.twinDecomposition_twinWidth

end Lax2Proofs.TwinWidth
