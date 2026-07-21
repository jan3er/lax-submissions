import Lax2Proofs.Source.TwinWidth.Graph.Partition
import Lax2Proofs.Source.TwinWidth.Graph.MixedMinorNumber
import Lax2Proofs.Source.TwinWidth.Matrix.Symmetric

/-!
# Theorem 14: from mixed-free ordered adjacency matrices to graph twin-width

Theorem 14 of the first twin-width paper is the graph-facing consequence of
the symmetric version of the matrix Theorem 10 construction.  This file proves
the graph side of that bridge: once the symmetric construction supplies a
bounded graph partition sequence from a mixed-free ordered adjacency matrix,
the existing graph `twinWidth` definition obtains the advertised bound.
-/

namespace Lax2Proofs.TwinWidth
namespace SimpleGraph

/-- Ordered adjacency matrices of undirected graphs are symmetric. -/
theorem orderedAdjacency_isSymmetricMatrix
    {V : Type*} {n : ℕ} [DecidableEq V]
    (G : _root_.SimpleGraph V) (σ : VertexOrder V n) :
    Matrix.IsSymmetricMatrix (Matrix.orderedAdjacency G σ) := by
  classical
  intro i j
  by_cases hij : G.Adj (σ.equiv i) (σ.equiv j)
  · have hji : G.Adj (σ.equiv j) (σ.equiv i) := G.symm hij
    simp [Matrix.orderedAdjacency, hij, hji]
  · have hji : ¬ G.Adj (σ.equiv j) (σ.equiv i) := fun h => hij (G.symm h)
    simp [Matrix.orderedAdjacency, hij, hji]

/-- Push a block of ordered matrix indices through a vertex order. -/
noncomputable def orderedImageBag {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (R : Finset (Fin n)) : Finset V :=
  by
    classical
    exact R.image σ.equiv

theorem orderedImageBag_injective {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) :
    Function.Injective (orderedImageBag σ) := by
  classical
  intro R S h
  ext r
  constructor
  · intro hr
    have hv : σ.equiv r ∈ orderedImageBag σ R := by
      simp [orderedImageBag, hr]
    rw [h] at hv
    rcases Finset.mem_image.mp hv with ⟨s, hs, hsv⟩
    have hsr : s = r := σ.equiv.injective hsv
    simpa [hsr] using hs
  · intro hs
    have hv : σ.equiv r ∈ orderedImageBag σ S := by
      simp [orderedImageBag, hs]
    rw [← h] at hv
    rcases Finset.mem_image.mp hv with ⟨s, hR, hsv⟩
    have hsr : s = r := σ.equiv.injective hsv
    simpa [hsr] using hR

theorem orderedImageBag_union {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (R S : Finset (Fin n)) :
    orderedImageBag σ (R ∪ S) = orderedImageBag σ R ∪ orderedImageBag σ S := by
  classical
  simp [orderedImageBag, Finset.image_union]

/-- The graph bag family induced by the row parts of a square matrix
partition in the chosen vertex order.  For symmetric matrix partitions the row
and column parts are the same family, so these are the graph bags used by the
mirrored Theorem 14 construction. -/
noncomputable def graphBagsOfMatrixPartition {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (P : Matrix.MatrixPartition n n) : Finset (Finset V) :=
  by
    classical
    exact P.rowParts.image (orderedImageBag σ)

theorem isBagPartition_graphBagsOfMatrixPartition {V : Type*} {n : ℕ}
    [DecidableEq V] (σ : VertexOrder V n) (P : Matrix.MatrixPartition n n) :
    IsBagPartition (graphBagsOfMatrixPartition σ P) := by
  classical
  constructor
  · intro A hA
    rcases Finset.mem_image.mp hA with ⟨R, hR, rfl⟩
    rcases P.row_nonempty hR with ⟨r, hr⟩
    exact ⟨σ.equiv r, by
      simp [orderedImageBag, hr]⟩
  constructor
  · intro A B hA hB hAB
    rcases Finset.mem_image.mp hA with ⟨R, hR, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨S, hS, rfl⟩
    have hRS : R ≠ S := by
      intro h
      apply hAB
      subst S
      rfl
    have hdis : Disjoint R S := P.row_disjoint hR hS hRS
    rw [Finset.disjoint_left]
    intro v hvR hvS
    rcases Finset.mem_image.mp hvR with ⟨r, hr, hrv⟩
    rcases Finset.mem_image.mp hvS with ⟨s, hs, hsv⟩
    have hrs : r = s := σ.equiv.injective (by
      rw [hrv, hsv])
    subst s
    exact (Finset.disjoint_left.mp hdis) hr hs
  · intro v
    rcases P.row_cover (σ.equiv.symm v) with ⟨R, hR, hr⟩
    refine ⟨orderedImageBag σ R, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    · exact Finset.mem_image.mpr ⟨σ.equiv.symm v, hr, by simp⟩

theorem graphBagsOfMatrixPartition_card_le_of_row_card_le_one {V : Type*}
    {n : ℕ} [DecidableEq V] (σ : VertexOrder V n)
    {P : Matrix.MatrixPartition n n} (hP : P.rowParts.card ≤ 1) :
    (graphBagsOfMatrixPartition σ P).card ≤ 1 := by
  classical
  calc
    (graphBagsOfMatrixPartition σ P).card ≤ P.rowParts.card := by
      simp [graphBagsOfMatrixPartition]
      exact Finset.card_image_le
    _ ≤ 1 := hP

theorem graphBagsOfMatrixPartition_eq_singletonBags_of_isFinest {V : Type*}
    {n : ℕ} [Fintype V] [DecidableEq V]
    (σ : VertexOrder V n) {P : Matrix.MatrixPartition n n}
    (hP : Matrix.MatrixPartition.IsFinest P) :
    graphBagsOfMatrixPartition σ P = TrigraphState.singletonBags V := by
  classical
  ext A
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨R, hR, rfl⟩
    rcases hP.1 hR with ⟨r, rfl⟩
    exact Finset.mem_image.mpr ⟨σ.equiv r, by simp, by
      simp [orderedImageBag]⟩
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨v, _hv, rfl⟩
    let r : Fin n := σ.equiv.symm v
    refine Finset.mem_image.mpr ⟨({r} : Finset (Fin n)), hP.2.1 r, ?_⟩
    simp [orderedImageBag, r]

theorem isBagContraction_graphBagsOfMatrixPartition_of_isSymmetricContraction
    {V : Type*} {n : ℕ} [DecidableEq V] (σ : VertexOrder V n)
    {P Q : Matrix.MatrixPartition n n}
    (hPQ : Matrix.MatrixPartition.IsSymmetricContraction P Q) :
    IsBagContraction (graphBagsOfMatrixPartition σ P)
      (graphBagsOfMatrixPartition σ Q) := by
  classical
  rcases hPQ with ⟨R, hR, S, hS, hRS, hrow, _hcol⟩
  refine ⟨orderedImageBag σ R, ?_, orderedImageBag σ S, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
  · exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
  · intro h
    exact hRS ((orderedImageBag_injective σ) h)
  · rw [graphBagsOfMatrixPartition, graphBagsOfMatrixPartition, hrow]
    rw [Finset.image_insert]
    rw [Finset.image_erase (orderedImageBag_injective σ)]
    rw [Finset.image_erase (orderedImageBag_injective σ)]
    simp [orderedImageBag_union]

theorem homogeneousBetween_orderedImageBag_of_zoneConstant
    {V : Type*} {n : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {R C : Finset (Fin n)}
    (hR : R.Nonempty) (hC : C.Nonempty)
    (hconst :
      Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C) :
    HomogeneousBetween G (orderedImageBag σ R) (orderedImageBag σ C) := by
  classical
  rcases hR with ⟨r₀, hr₀⟩
  rcases hC with ⟨c₀, hc₀⟩
  by_cases hbase : G.Adj (σ.equiv r₀) (σ.equiv c₀)
  · refine Or.inl ?_
    intro a b ha hb
    rcases Finset.mem_image.mp ha with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨c, hc, rfl⟩
    have hEq := hconst hr₀ hr hc₀ hc
    have hdec : decide (G.Adj (σ.equiv r) (σ.equiv c)) = true := by
      simpa [Matrix.orderedAdjacency, hbase] using hEq.symm
    exact of_decide_eq_true hdec
  · refine Or.inr ?_
    intro a b ha hb hab
    rcases Finset.mem_image.mp ha with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨c, hc, rfl⟩
    have hEq := hconst hr₀ hr hc₀ hc
    have hdec : decide (G.Adj (σ.equiv r) (σ.equiv c)) = false := by
      simpa [Matrix.orderedAdjacency, hbase] using hEq.symm
    exact (of_decide_eq_false hdec) hab

theorem not_zoneConstant_of_partitionRedAdj_orderedImageBag
    {V : Type*} {n : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {R C : Finset (Fin n)}
    (hR : R.Nonempty) (hC : C.Nonempty)
    (hred : partitionRedAdj G (orderedImageBag σ R) (orderedImageBag σ C)) :
    ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C := by
  intro hconst
  exact hred.2 (homogeneousBetween_orderedImageBag_of_zoneConstant
    (G := G) σ hR hC hconst)

theorem partitionRedDegreeAtMost_graphBagsOfMatrixPartition
    {V : Type*} {n d : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {P : Matrix.MatrixPartition n n}
    (hsym : P.rowParts = P.colParts)
    (herror : Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G σ) P d) :
    PartitionRedDegreeAtMost G (graphBagsOfMatrixPartition σ P) d := by
  classical
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨R, hR, rfl⟩
  let graphErrors : Finset (Finset V) :=
    (P.rowParts.filter fun C =>
      ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C).image
        (orderedImageBag σ)
  have hsubset :
      (graphBagsOfMatrixPartition σ P).filter
          (fun B => partitionRedAdj G (orderedImageBag σ R) B) ⊆ graphErrors := by
    intro B hB
    rcases Finset.mem_filter.mp hB with ⟨hBbags, hred⟩
    rcases Finset.mem_image.mp hBbags with ⟨C, hC, rfl⟩
    have hnconst :
        ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C :=
      not_zoneConstant_of_partitionRedAdj_orderedImageBag
        (G := G) σ (P.row_nonempty hR) (P.row_nonempty hC) hred
    exact Finset.mem_image.mpr ⟨C, by simp [hnconst, hC], rfl⟩
  calc
    ((graphBagsOfMatrixPartition σ P).filter
        (fun B => partitionRedAdj G (orderedImageBag σ R) B)).card
        ≤ graphErrors.card := Finset.card_le_card hsubset
    _ ≤ (P.rowParts.filter fun C =>
          ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C).card := by
        exact Finset.card_image_le
    _ = (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ) P R).card := by
        simp [Matrix.rowErrorSet, hsym]
    _ ≤ d := herror.1 hR

/-- A symmetric matrix contraction sequence induces the graph partition
sequence used by Theorem 14.

Rows and columns are the same family at every step.  Pushing each row block
through the chosen vertex order gives graph bags; each symmetric matrix
contraction is exactly the corresponding graph bag contraction, and the
complete/empty/non-homogeneous trigraph semantics agree with the contracted
matrix zones. -/
theorem graphPartitionSequence_of_symmetricMatrixContractionSequence
    {V : Type*} {n d : ℕ} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    (S : Matrix.SymmetricMatrixContractionSequence
      (Matrix.orderedAdjacency G σ) d) :
    Nonempty (GraphPartitionSequence G d) := by
  classical
  refine ⟨?_⟩
  refine
    { stepCount := S.stepCount
      bags := fun i => graphBagsOfMatrixPartition σ (S.partition i)
      isPartition := fun i _hi =>
        isBagPartition_graphBagsOfMatrixPartition σ (S.partition i)
      starts := ?_
      starts_state := ?_
      ends := ?_
      step_contracts := ?_
      redDegree_le := ?_ } <;> try intro i hi
  · exact graphBagsOfMatrixPartition_eq_singletonBags_of_isFinest σ S.starts
  · simpa [graphBagsOfMatrixPartition_eq_singletonBags_of_isFinest σ S.starts] using
      trigraphStateOfPartition_singletonBags_initial G
  · exact graphBagsOfMatrixPartition_card_le_of_row_card_le_one σ S.ends.1
  · exact isContractionStep_trigraphStateOfPartition_of_isBagContraction
      (isBagPartition_graphBagsOfMatrixPartition σ (S.partition i))
      (isBagPartition_graphBagsOfMatrixPartition σ (S.partition (i + 1)))
      (isBagContraction_graphBagsOfMatrixPartition_of_isSymmetricContraction
        σ (S.step_contracts i hi))
  · exact partitionRedDegreeAtMost_graphBagsOfMatrixPartition
      (G := G) σ (S.symmetric i hi) (S.errorValue_le i hi)

theorem graphPartitionSequence_of_symmetricMatrixTwinWidthAtMost
    {V : Type*} {n d : ℕ} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    (h :
      Matrix.SymmetricMatrixTwinWidthAtMost
        (Matrix.orderedAdjacency G σ) d) :
    Nonempty (GraphPartitionSequence G d) := by
  rcases h with ⟨S⟩
  exact graphPartitionSequence_of_symmetricMatrixContractionSequence σ S

/-- The explicit graph-facing bound obtained by applying the formalized
mirrored Theorem 10 refinement to a Boolean `t`-mixed-free ordered adjacency
matrix. -/
def theorem14MixedFreeTwinWidthBound (t : ℕ) : ℕ :=
  Matrix.symmetricMatrixTwinWidthBoundOfMixedFree t

@[simp] theorem theorem14MixedFreeTwinWidthBound_eq (t : ℕ) :
    theorem14MixedFreeTwinWidthBound t =
      Matrix.symmetricMatrixTwinWidthBoundOfMixedFree t := by
  rfl

/-- Theorem 14 in sequence-constructor form.

If the symmetric matrix construction turns a `t`-mixed-free ordered adjacency
matrix into a graph partition sequence of the Theorem 14 width, then the graph
has twin-width at most that width. -/
theorem theorem14_twinWidth_le_of_mixedFree_order_of_partitionSequence
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {n t : ℕ} {σ : VertexOrder V n}
    (hconstruct :
      Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
        Nonempty (GraphPartitionSequence G (theorem14MixedFreeTwinWidthBound t)))
    (hfree : Matrix.MixedFree (Matrix.orderedAdjacency G σ) t) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound t := by
  rcases hconstruct hfree with ⟨S⟩
  exact twinWidth_le_of_hasTwinWidthAtMost
    (GraphPartitionSequence.hasTwinWidthAtMost_of_graphPartitionSequence S)

/-- Ordered-adjacency mixed-number form of Theorem 14.

It suffices to build the symmetric graph partition sequence for the first
mixed-minor order that the ordered adjacency matrix avoids. -/
theorem theorem14_twinWidth_le_orderedAdjacencyMixedNumber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (σ : VertexOrder V (Fintype.card V))
    (hconstruct :
      ∀ t : ℕ,
        Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
          Nonempty (GraphPartitionSequence G (theorem14MixedFreeTwinWidthBound t))) :
    twinWidth G ≤
      theorem14MixedFreeTwinWidthBound
        (Matrix.orderedAdjacencyMixedNumber G σ + 1) := by
  let k := Matrix.orderedAdjacencyMixedNumber G σ
  have hfree : Matrix.MixedFree (Matrix.orderedAdjacency G σ) (k + 1) := by
    simpa [k, Matrix.orderedAdjacencyMixedNumber] using
      Matrix.not_hasMixedMinor_succ_matrixMixedNumber (Matrix.orderedAdjacency G σ)
  simpa [k] using
    theorem14_twinWidth_le_of_mixedFree_order_of_partitionSequence
      (G := G) (σ := σ) (t := k + 1) (hconstruct (k + 1)) hfree

/-- Graph mixed-minor-number form of Theorem 14.

Choose an order realizing `mixedMinorNumber`; the avoided order is then one
more than that minimum, which matches `theorem10MatrixTwinWidthBound`. -/
theorem theorem14_twinWidth_le_mixedMinorNumber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    (hconstruct :
      ∀ σ : VertexOrder V (Fintype.card V), ∀ t : ℕ,
        Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
          Nonempty (GraphPartitionSequence G (theorem14MixedFreeTwinWidthBound t))) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤
        theorem14MixedFreeTwinWidthBound
          (Matrix.orderedAdjacencyMixedNumber G σ + 1) :=
      theorem14_twinWidth_le_orderedAdjacencyMixedNumber G σ (hconstruct σ)
    _ = theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by rw [hσ]

/-- Theorem 14 from the mirrored matrix construction.

The first hypothesis is the symmetric matrix version of Theorem 10: mirror each
row contraction by its column contraction, and mirror each column contraction by
its row contraction.  The second hypothesis translates the resulting symmetric
matrix partition sequence for an ordered adjacency matrix into the graph
partition sequence used by `twinWidth`. -/
theorem theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixBridge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    (hmatrix :
      ∀ σ : VertexOrder V (Fintype.card V), ∀ t : ℕ,
        Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
          Matrix.SymmetricMatrixTwinWidthAtMost (Matrix.orderedAdjacency G σ)
            (theorem14MixedFreeTwinWidthBound t))
    (hbridge :
      ∀ σ : VertexOrder V (Fintype.card V), ∀ d : ℕ,
        Matrix.SymmetricMatrixTwinWidthAtMost (Matrix.orderedAdjacency G σ) d →
          Nonempty (GraphPartitionSequence G d)) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by
  apply theorem14_twinWidth_le_mixedMinorNumber
  intro σ t hfree
  exact hbridge σ (theorem14MixedFreeTwinWidthBound t) (hmatrix σ t hfree)

/-- Theorem 14 from the mirrored symmetric matrix construction.

The graph interpretation of symmetric matrix contractions is proved in this
file, so the only external mathematical input here is the symmetric matrix
construction itself: every mixed-free ordered adjacency matrix has a bounded
symmetric matrix contraction sequence. -/
theorem theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixConstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    (hmatrix :
      ∀ σ : VertexOrder V (Fintype.card V), ∀ t : ℕ,
        Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
          Matrix.SymmetricMatrixTwinWidthAtMost (Matrix.orderedAdjacency G σ)
            (theorem14MixedFreeTwinWidthBound t)) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by
  exact theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixBridge
    G hmatrix (fun σ _d h => graphPartitionSequence_of_symmetricMatrixTwinWidthAtMost σ h)

/-- Theorem 14 with the mirrored matrix construction discharged by
`Matrix.Symmetric`: graph twin-width is bounded by the explicit mixed-free
bound at one more than the graph mixed minor number. -/
theorem theorem14_twinWidth_le_mixedMinorNumber_explicit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by
  exact theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixConstruction G
    (fun σ t hfree => by
      simpa [theorem14MixedFreeTwinWidthBound] using
        Matrix.symmetricMatrixTwinWidthBoundedByMixedFree
          (Matrix.orderedAdjacency G σ)
          (orderedAdjacency_isSymmetricMatrix G σ) hfree)

end SimpleGraph
end Lax2Proofs.TwinWidth
