import Lax2Proofs.Source.TwinWidth.Equivalence.TwinWidthToMixed
import Lax2Proofs.Source.TwinWidth.Graph.Theorem14

/-!
# Mixed minor number to twin-width

This module records the opposite directional bound needed for functional
equivalence.  Section 5 gives an explicit elementary bound via the
Marcus-Tardos theorem, Lemma 13, and the finite-alphabet profile refinement.
-/

namespace Lax2Proofs.TwinWidth
namespace SimpleGraph

/-- The proposition that twin-width is bounded by a numerical function of mixed
minor number. -/
def TwinWidthBoundedByMixedMinorNumber : Prop :=
  ∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
    twinWidth G ≤ f (mixedMinorNumber G)

/-- The concrete elementary bound supplied by the mirrored Boolean
Theorem 14 construction.  If an ordered adjacency matrix has mixed number `k`,
then it is `(k+1)`-mixed-free, so the graph-facing witness is the symmetric
mixed-free bound at `k+1`. -/
def twinWidthBoundOfMixedMinorNumber (k : ℕ) : ℕ :=
  theorem14MixedFreeTwinWidthBound (k + 1)

/-- Matrix-level ordered-adjacency form of the mixed-to-twin-width direction.

This is the graph-facing bridge required after the matrix theorem: the
twin-width of the graph represented by an ordered adjacency matrix is bounded
by a function of that matrix's mixed number. -/
def TwinWidthBoundedByOrderedAdjacencyMixedNumber (f : ℕ → ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
    (σ : VertexOrder V (Fintype.card V)),
      twinWidth G ≤ f (Matrix.orderedAdjacencyMixedNumber G σ)

/-- Passing from a bound for every ordered adjacency matrix to the graph mixed
minor number, using an order that realizes the minimum in `mixedMinorNumber`. -/
theorem twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyBound
    {f : ℕ → ℕ}
    (h : TwinWidthBoundedByOrderedAdjacencyMixedNumber f) :
    TwinWidthBoundedByMixedMinorNumber := by
  refine ⟨f, ?_⟩
  intro V _ _ G
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤ f (Matrix.orderedAdjacencyMixedNumber G σ) := h G σ
    _ = f (mixedMinorNumber G) := by rw [hσ]

/-- The concrete mixed-minor-to-twin-width direction, assuming the Section 5
ordered-adjacency matrix bound with the chosen elementary witness. -/
def TwinWidthBoundedByOrderedAdjacencyMixedNumberExplicit : Prop :=
  TwinWidthBoundedByOrderedAdjacencyMixedNumber twinWidthBoundOfMixedMinorNumber

/-- One functional-equivalence direction with the explicit mixed-minor witness,
obtained from the ordered-adjacency matrix bound. -/
theorem twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyExplicitBound
    (h : TwinWidthBoundedByOrderedAdjacencyMixedNumberExplicit) :
    TwinWidthBoundedByMixedMinorNumber :=
  twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyBound h

/-- The completed mixed-minor-to-twin-width direction, obtained from the
formalized mirrored Theorem 14 construction. -/
theorem twinWidth_le_twinWidthBoundOfMixedMinorNumber
    {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G) := by
  simpa [twinWidthBoundOfMixedMinorNumber] using
    theorem14_twinWidth_le_mixedMinorNumber_explicit G

/-- The completed graph-parameter direction from mixed minor number to
twin-width. -/
theorem twinWidthBoundedByMixedMinorNumber :
    TwinWidthBoundedByMixedMinorNumber := by
  refine ⟨twinWidthBoundOfMixedMinorNumber, ?_⟩
  intro V _ _ G
  exact twinWidth_le_twinWidthBoundOfMixedMinorNumber G

/-- Legacy ordered-adjacency Theorem 14 reduction: a bound for every ordered
adjacency matrix gives the graph-level bound by choosing an order that realizes
`mixedMinorNumber`. -/
theorem twin_width_le_theorem14_bound_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
        (σ : VertexOrder V (Fintype.card V)),
          twinWidth G ≤
            theorem14MixedFreeTwinWidthBound
              (Matrix.orderedAdjacencyMixedNumber G σ + 1)) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G) := by
  intro V _ _ G
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound
        (Matrix.orderedAdjacencyMixedNumber G σ + 1) := h G σ
    _ = twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G) := by
        rw [hσ]
        rfl

/-- Legacy double-exponential reduction retained as a plain consequence of any
ordered-adjacency bound with that numerical witness.  The main contract uses
the explicit Theorem 10 bound above. -/
theorem twin_width_le_double_exponential_mixed_minor_number_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
        (σ : VertexOrder V (Fintype.card V)),
          twinWidth G ≤ 2 ^ (2 ^ (Matrix.orderedAdjacencyMixedNumber G σ + 1))) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      twinWidth G ≤ 2 ^ (2 ^ (mixedMinorNumber G + 1)) := by
  intro V _ _ G
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤ 2 ^ (2 ^ (Matrix.orderedAdjacencyMixedNumber G σ + 1)) := h G σ
    _ = 2 ^ (2 ^ (mixedMinorNumber G + 1)) := by rw [hσ]

end SimpleGraph
end Lax2Proofs.TwinWidth
