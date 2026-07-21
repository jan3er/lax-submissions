import Lax4Proofs.Source.TwinWidth.Graph.Theorem14
import Mathlib.Data.List.NodupEquivFin

/-!
# Twin-decomposition orders

The left-to-right order on the leaves of a contraction tree is the order used
to turn a graph `d`-sequence into a `d`-twin-ordered adjacency matrix.  This
file isolates the exact graph/matrix interface supplied by that construction:
a `TwinDecomposition` records the leaf order together with the matrix
twin-orderedness proof for the ordered adjacency matrix.
-/

namespace Lax4Proofs.TwinWidth
namespace SimpleGraph

/-- Reindexing a division twice is the same as reindexing by the composed
cardinality equality. -/
theorem Division.castIndex_castIndex
    {n k l q : ℕ} (hkl : k = l) (hlq : l = q) (D : Division n k) :
    Division.castIndex hlq (Division.castIndex hkl D) =
      Division.castIndex (hkl.trans hlq) D := by
  subst l
  subst q
  rfl

@[simp] theorem Division.castIndex_proof_irrel
    {n k l : ℕ} (h h' : k = l) (D : Division n k) :
    Division.castIndex h D = Division.castIndex h' D := by
  subst l
  rfl

/-- Heterogeneous proof irrelevance for reindexing a fixed division. -/
theorem Division.castIndex_heq
    {n k l l' : ℕ} (h : k = l) (h' : k = l') (D : Division n k) :
    Division.castIndex h D ≍ Division.castIndex h' D := by
  subst l
  subst l'
  rfl

/-- Extensionality for matrix divisions with dependent division fields. -/
theorem matrixDivision_ext_heq {n m : ℕ}
    {D E : Matrix.MatrixDivision n m}
    (hrowCuts : D.rowCuts = E.rowCuts)
    (hcolCuts : D.colCuts = E.colCuts)
    (hrowDiv : D.rowDiv ≍ E.rowDiv)
    (hcolDiv : D.colDiv ≍ E.colDiv) :
    D = E := by
  cases D
  cases E
  simp at hrowCuts hcolCuts
  subst hrowCuts
  subst hcolCuts
  cases hrowDiv
  cases hcolDiv
  rfl

/-- Fin indices with the same value are heterogeneously equal after identifying
their ambient bounds. -/
theorem fin_heq_of_val_eq {n n' : ℕ} (hn : n = n')
    {i : Fin n} {j : Fin n'} (hval : i.1 = j.1) :
    i ≍ j := by
  subst n'
  exact heq_of_eq (Fin.ext hval)

/-- Pull a graph bag back to row/column indices in a vertex order. -/
noncomputable def orderedPreimageBag {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (A : Finset V) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun i => σ.equiv i ∈ A

@[simp] theorem mem_orderedPreimageBag {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (A : Finset V) (i : Fin n) :
    i ∈ orderedPreimageBag σ A ↔ σ.equiv i ∈ A := by
  classical
  simp [orderedPreimageBag]

theorem orderedImageBag_orderedPreimageBag {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (A : Finset V) :
    orderedImageBag σ (orderedPreimageBag σ A) = A := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    simpa using hi
  · intro hv
    refine Finset.mem_image.mpr ⟨σ.equiv.symm v, ?_, by simp⟩
    simp [orderedPreimageBag, hv]

theorem orderedPreimageBag_injective {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) :
    Function.Injective (orderedPreimageBag σ) := by
  intro A B h
  have hA := orderedImageBag_orderedPreimageBag σ A
  have hB := orderedImageBag_orderedPreimageBag σ B
  rw [← hA, h, hB]

theorem orderedPreimageBag_nonempty {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) {A : Finset V} :
    A.Nonempty → (orderedPreimageBag σ A).Nonempty := by
  classical
  rintro ⟨v, hv⟩
  exact ⟨σ.equiv.symm v, by simp [orderedPreimageBag, hv]⟩

theorem orderedPreimageBag_disjoint {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) {A B : Finset V} :
    Disjoint A B → Disjoint (orderedPreimageBag σ A) (orderedPreimageBag σ B) := by
  classical
  intro hAB
  rw [Finset.disjoint_left]
  intro i hiA hiB
  exact (Finset.disjoint_left.mp hAB) (by simpa using hiA) (by simpa using hiB)

@[simp] theorem orderedPreimageBag_union {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (A B : Finset V) :
    orderedPreimageBag σ (A ∪ B) =
      orderedPreimageBag σ A ∪ orderedPreimageBag σ B := by
  classical
  ext i
  simp [orderedPreimageBag]

@[simp] theorem orderedPreimageBag_singleton {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (i : Fin n) :
    orderedPreimageBag σ ({σ.equiv i} : Finset V) = {i} := by
  classical
  ext j
  simp [orderedPreimageBag]

theorem zoneConstant_orderedAdjacency_of_homogeneousBetween_preimage
    {V : Type*} {n : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {A B : Finset V}
    (hhom : HomogeneousBetween G A B) :
    Matrix.ZoneConstant (Matrix.orderedAdjacency G σ)
      (orderedPreimageBag σ A) (orderedPreimageBag σ B) := by
  classical
  intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
  rcases hhom with hcomp | hemp
  · have h₁ : G.Adj (σ.equiv r₁) (σ.equiv c₁) := hcomp (by simpa using hr₁) (by simpa using hc₁)
    have h₂ : G.Adj (σ.equiv r₂) (σ.equiv c₂) := hcomp (by simpa using hr₂) (by simpa using hc₂)
    simp [Matrix.orderedAdjacency, h₁, h₂]
  · have h₁ : ¬ G.Adj (σ.equiv r₁) (σ.equiv c₁) :=
      hemp (by simpa using hr₁) (by simpa using hc₁)
    have h₂ : ¬ G.Adj (σ.equiv r₂) (σ.equiv c₂) :=
      hemp (by simpa using hr₂) (by simpa using hc₂)
    simp [Matrix.orderedAdjacency, h₁, h₂]

theorem nonconstant_preimage_imp_red_or_same
    {V : Type*} {n : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {T : TrigraphState V} (hsem : IsSemanticState G T)
    {A B : Finset V} (hA : A ∈ T.bags) (hB : B ∈ T.bags)
    (hnon :
      ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ)
        (orderedPreimageBag σ A) (orderedPreimageBag σ B)) :
    T.redAdj A B ∨ B = A := by
  classical
  by_cases hBA : B = A
  · exact Or.inr hBA
  · left
    have hred : partitionRedAdj G A B := by
      refine ⟨?_, ?_⟩
      · exact fun hAB => hBA hAB.symm
      · intro hhom
        exact hnon (zoneConstant_orderedAdjacency_of_homogeneousBetween_preimage σ hhom)
    exact (hsem.1 hA hB).2 hred

namespace ContractionSequence

/-- The symmetric matrix partition obtained from a trigraph state by pulling
each graph bag back through the leaf order. -/
noncomputable def matrixPartitionOfState
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) (i : ℕ) : Matrix.MatrixPartition
      (Fintype.card V) (Fintype.card V) where
  rowParts := (S.state i).bags.image (orderedPreimageBag σ)
  row_nonempty := by
    classical
    intro R hR
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    exact orderedPreimageBag_nonempty σ ((S.state i).bag_nonempty hA)
  row_disjoint := by
    classical
    intro R Q hR hQ hRQ
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hQ with ⟨B, hB, rfl⟩
    have hAB : A ≠ B := by
      intro h
      subst B
      exact hRQ rfl
    exact orderedPreimageBag_disjoint σ ((S.state i).bag_disjoint hA hB hAB)
  row_cover := by
    classical
    intro r
    rcases (S.state i).bag_cover (σ.equiv r) with ⟨A, hA, hrA⟩
    refine ⟨orderedPreimageBag σ A, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    · simp [orderedPreimageBag, hrA]
  colParts := (S.state i).bags.image (orderedPreimageBag σ)
  col_nonempty := by
    classical
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    exact orderedPreimageBag_nonempty σ ((S.state i).bag_nonempty hA)
  col_disjoint := by
    classical
    intro C D hC hD hCD
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨B, hB, rfl⟩
    have hAB : A ≠ B := by
      intro h
      subst B
      exact hCD rfl
    exact orderedPreimageBag_disjoint σ ((S.state i).bag_disjoint hA hB hAB)
  col_cover := by
    classical
    intro c
    rcases (S.state i).bag_cover (σ.equiv c) with ⟨A, hA, hcA⟩
    refine ⟨orderedPreimageBag σ A, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    · simp [orderedPreimageBag, hcA]

@[simp] theorem rowParts_matrixPartitionOfState
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) (i : ℕ) :
    (S.matrixPartitionOfState σ i).rowParts =
      (S.state i).bags.image (orderedPreimageBag σ) := rfl

@[simp] theorem colParts_matrixPartitionOfState
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) (i : ℕ) :
    (S.matrixPartitionOfState σ i).colParts =
      (S.state i).bags.image (orderedPreimageBag σ) := rfl

/-- The rectangular matrix partition obtained by taking row bags from one
trigraph state and column bags from another.  This is used for the intermediate
matrix division after a row fusion has been mirrored but before the matching
column fusion has been performed. -/
noncomputable def matrixPartitionOfTwoStates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V))
    (rowTime colTime : ℕ) : Matrix.MatrixPartition
      (Fintype.card V) (Fintype.card V) where
  rowParts := (S.state rowTime).bags.image (orderedPreimageBag σ)
  row_nonempty := by
    classical
    intro R hR
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    exact orderedPreimageBag_nonempty σ ((S.state rowTime).bag_nonempty hA)
  row_disjoint := by
    classical
    intro R Q hR hQ hRQ
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hQ with ⟨B, hB, rfl⟩
    have hAB : A ≠ B := by
      intro h
      subst B
      exact hRQ rfl
    exact orderedPreimageBag_disjoint σ ((S.state rowTime).bag_disjoint hA hB hAB)
  row_cover := by
    classical
    intro r
    rcases (S.state rowTime).bag_cover (σ.equiv r) with ⟨A, hA, hrA⟩
    refine ⟨orderedPreimageBag σ A, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    · simp [orderedPreimageBag, hrA]
  colParts := (S.state colTime).bags.image (orderedPreimageBag σ)
  col_nonempty := by
    classical
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    exact orderedPreimageBag_nonempty σ ((S.state colTime).bag_nonempty hA)
  col_disjoint := by
    classical
    intro C D hC hD hCD
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨B, hB, rfl⟩
    have hAB : A ≠ B := by
      intro h
      subst B
      exact hCD rfl
    exact orderedPreimageBag_disjoint σ ((S.state colTime).bag_disjoint hA hB hAB)
  col_cover := by
    classical
    intro c
    rcases (S.state colTime).bag_cover (σ.equiv c) with ⟨A, hA, hcA⟩
    refine ⟨orderedPreimageBag σ A, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    · simp [orderedPreimageBag, hcA]

@[simp] theorem rowParts_matrixPartitionOfTwoStates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V))
    (rowTime colTime : ℕ) :
    (S.matrixPartitionOfTwoStates σ rowTime colTime).rowParts =
      (S.state rowTime).bags.image (orderedPreimageBag σ) := rfl

@[simp] theorem colParts_matrixPartitionOfTwoStates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V))
    (rowTime colTime : ℕ) :
    (S.matrixPartitionOfTwoStates σ rowTime colTime).colParts =
      (S.state colTime).bags.image (orderedPreimageBag σ) := rfl

/-- Taking the same state on both axes gives the symmetric state partition. -/
theorem matrixPartitionOfTwoStates_self_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) (i : ℕ) :
    S.matrixPartitionOfTwoStates σ i i = S.matrixPartitionOfState σ i := by
  apply Matrix.MatrixPartition.ext_parts <;> rfl

theorem matrixPartitionOfState_errorValueAtMost
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) {i : ℕ} (hi : i ≤ S.stepCount) :
    Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G σ)
      (S.matrixPartitionOfState σ i) (d + 1) := by
  classical
  have hsem := S.isSemanticState i hi
  constructor
  · intro R hR
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    let target : Finset (Finset V) :=
      ((S.state i).bags.filter fun B => (S.state i).redAdj A B) ∪ {A}
    have hsubset :
        (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ) ⊆ target := by
      intro B hB
      rcases Finset.mem_image.mp hB with ⟨C, hCerr, rfl⟩
      rcases Finset.mem_filter.mp hCerr with ⟨hCpart, hnon⟩
      rcases Finset.mem_image.mp hCpart with ⟨B₀, hB₀, rfl⟩
      have hred_or :=
        nonconstant_preimage_imp_red_or_same σ hsem hA hB₀ hnon
      rw [orderedImageBag_orderedPreimageBag]
      rcases hred_or with hred | hs
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hB₀, hred⟩)
      · subst B₀
        exact Finset.mem_union_right _ (by simp)
    have himage_card :
        ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ)).card =
          (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).card := by
      rw [Finset.card_image_of_injective]
      exact orderedImageBag_injective σ
    calc
      (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
          (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).card
          = ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ)).card := himage_card.symm
      _ ≤ target.card := Finset.card_le_card hsubset
      _ ≤ ((S.state i).bags.filter fun B => (S.state i).redAdj A B).card + 1 := by
        have h :=
          Finset.card_union_le
            ((S.state i).bags.filter fun B => (S.state i).redAdj A B)
            ({A} : Finset (Finset V))
        simpa [target] using h
      _ ≤ d + 1 := by
        have hred := S.redDegree_le i hi hA
        simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 1
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    let target : Finset (Finset V) :=
      ((S.state i).bags.filter fun B => (S.state i).redAdj A B) ∪ {A}
    have hsubset :
        (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ) ⊆ target := by
      intro B hB
      rcases Finset.mem_image.mp hB with ⟨R, hRerr, rfl⟩
      rcases Finset.mem_filter.mp hRerr with ⟨hRpart, hnon⟩
      rcases Finset.mem_image.mp hRpart with ⟨B₀, hB₀, rfl⟩
      have hred_or_BA :=
        nonconstant_preimage_imp_red_or_same σ hsem hB₀ hA hnon
      rw [orderedImageBag_orderedPreimageBag]
      rcases hred_or_BA with hredBA | hsame
      · have hredAB := (S.state i).red_symm hB₀ hA hredBA
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hB₀, hredAB⟩)
      · subst B₀
        exact Finset.mem_union_right _ (by simp)
    have himage_card :
        ((Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ)).card =
          (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).card := by
      rw [Finset.card_image_of_injective]
      exact orderedImageBag_injective σ
    calc
      (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
          (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).card
          = ((Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ)).card := himage_card.symm
      _ ≤ target.card := Finset.card_le_card hsubset
      _ ≤ ((S.state i).bags.filter fun B => (S.state i).redAdj A B).card + 1 := by
        have h :=
          Finset.card_union_le
            ((S.state i).bags.filter fun B => (S.state i).redAdj A B)
            ({A} : Finset (Finset V))
        simpa [target] using h
      _ ≤ d + 1 := by
        have hred := S.redDegree_le i hi hA
        simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 1

end ContractionSequence

namespace ContractionSequence

/-- The two bags contracted at a specified step, packaged with the bag-family
part of the contraction-step certificate. -/
noncomputable def stepPair
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    {p : Finset V × Finset V //
      p.1 ∈ (S.state i).bags ∧
      p.2 ∈ (S.state i).bags ∧
      p.1 ≠ p.2 ∧
      (S.state (i + 1)).bags =
        insert (p.1 ∪ p.2) (((S.state i).bags.erase p.1).erase p.2)} :=
  Classical.choice <| by
  classical
  rcases S.step_contracts i hi with ⟨A, hA, B, hB, hAB, hbags, _hred, _hblack⟩
  exact ⟨⟨(A, B), hA, hB, hAB, hbags⟩⟩

/-- The contracted pair at time `i`, with a harmless default outside the
declared time interval.  This proof-independent selector avoids carrying
irrelevant proof terms through the leaf-order recursion. -/
noncomputable def stepPairAt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (i : ℕ) : Finset V × Finset V :=
  if hi : i < S.stepCount then (S.stepPair hi).1 else (∅, ∅)

theorem stepPairAt_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    (S.stepPairAt i).1 ∈ (S.state i).bags ∧
      (S.stepPairAt i).2 ∈ (S.state i).bags ∧
      (S.stepPairAt i).1 ≠ (S.stepPairAt i).2 ∧
      (S.state (i + 1)).bags =
        insert ((S.stepPairAt i).1 ∪ (S.stepPairAt i).2)
          (((S.state i).bags.erase (S.stepPairAt i).1).erase (S.stepPairAt i).2) := by
  classical
  have hif : S.stepPairAt i = (S.stepPair hi).1 := by
    simp [stepPairAt, hi]
  simpa [hif] using (S.stepPair hi).2

/-- The merged bag produced by a step belongs to the next state. -/
theorem stepPairAt_union_mem_next
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    (S.stepPairAt i).1 ∪ (S.stepPairAt i).2 ∈ (S.state (i + 1)).bags := by
  classical
  have hspec := S.stepPairAt_spec hi
  rw [hspec.2.2.2]
  simp

/-- A current bag not among the two contracted bags survives into the next
state. -/
theorem stepPairAt_current_mem_next_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount)
    {X : Finset V} (hX : X ∈ (S.state i).bags)
    (hXA : X ≠ (S.stepPairAt i).1) (hXB : X ≠ (S.stepPairAt i).2) :
    X ∈ (S.state (i + 1)).bags := by
  classical
  have hspec := S.stepPairAt_spec hi
  rw [hspec.2.2.2]
  exact Finset.mem_insert.mpr (Or.inr (by simp [hX, hXA, hXB]))

/-- Every next-state bag is either the newly merged bag or an old bag distinct
from both contracted bags. -/
theorem stepPairAt_next_mem_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount)
    {X : Finset V} (hX : X ∈ (S.state (i + 1)).bags) :
    X = (S.stepPairAt i).1 ∪ (S.stepPairAt i).2 ∨
      X ∈ (S.state i).bags ∧
        X ≠ (S.stepPairAt i).1 ∧ X ≠ (S.stepPairAt i).2 := by
  classical
  have hspec := S.stepPairAt_spec hi
  rw [hspec.2.2.2] at hX
  rcases Finset.mem_insert.mp hX with hXU | hXold
  · exact Or.inl hXU
  ·
    rcases Finset.mem_erase.mp hXold with ⟨hXB, hXold'⟩
    rcases Finset.mem_erase.mp hXold' with ⟨hXA, hXold_current⟩
    exact Or.inr ⟨hXold_current, hXA, hXB⟩

/-- After one side of a graph contraction has been mirrored in the ordered
adjacency matrix, the intermediate rectangular partition still has bounded
nonconstant error.  The extra `+3` accounts for the two children of the merged
bag and the diagonal/self zone convention. -/
theorem matrixPartitionOfAdjacentStates_errorValueAtMost
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V))
    {i : ℕ} (hi : i < S.stepCount) :
    Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G σ)
      (S.matrixPartitionOfTwoStates σ (i + 1) i) (d + 3) := by
  classical
  let A : Finset V := (S.stepPairAt i).1
  let B : Finset V := (S.stepPairAt i).2
  let U : Finset V := A ∪ B
  have hspec := S.stepPairAt_spec hi
  have hA : A ∈ (S.state i).bags := by simpa [A] using hspec.1
  have hB : B ∈ (S.state i).bags := by simpa [B] using hspec.2.1
  have hAB : A ≠ B := by simpa [A, B] using hspec.2.2.1
  have hU : U ∈ (S.state (i + 1)).bags := by
    simpa [A, B, U] using S.stepPairAt_union_mem_next hi
  have hsemCur := S.isSemanticState i (by omega : i ≤ S.stepCount)
  have hsemNext := S.isSemanticState (i + 1) (by omega : i + 1 ≤ S.stepCount)
  constructor
  · intro R hR
    rcases Finset.mem_image.mp hR with ⟨X, hXnext, rfl⟩
    by_cases hXU : X = U
    · subst X
      let target : Finset (Finset V) :=
        ((S.state (i + 1)).bags.filter fun Y => (S.state (i + 1)).redAdj U Y) ∪
          ({A, B, U} : Finset (Finset V))
      have hsubset :
          (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i) (orderedPreimageBag σ U)).image
              (orderedImageBag σ) ⊆ target := by
        intro Y hY
        rcases Finset.mem_image.mp hY with ⟨C, hCerr, rfl⟩
        rcases Finset.mem_filter.mp hCerr with ⟨hCpart, hnon⟩
        rcases Finset.mem_image.mp hCpart with ⟨Y₀, hY₀old, rfl⟩
        rw [orderedImageBag_orderedPreimageBag]
        by_cases hYA : Y₀ = A
        · subst Y₀
          exact Finset.mem_union_right _ (by simp)
        by_cases hYB : Y₀ = B
        · subst Y₀
          exact Finset.mem_union_right _ (by simp)
        have hY₀next :
            Y₀ ∈ (S.state (i + 1)).bags := by
          simpa [A, B] using
            S.stepPairAt_current_mem_next_of_ne hi hY₀old hYA hYB
        have hred_or :=
          nonconstant_preimage_imp_red_or_same σ hsemNext hU hY₀next hnon
        rcases hred_or with hred | hsame
        · exact Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hY₀next, hred⟩)
        · subst Y₀
          exact Finset.mem_union_right _ (by simp)
      have himage_card :
          ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i)
                (orderedPreimageBag σ U)).image
              (orderedImageBag σ)).card =
            (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i)
                (orderedPreimageBag σ U)).card := by
        rw [Finset.card_image_of_injective]
        exact orderedImageBag_injective σ
      calc
        (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfTwoStates σ (i + 1) i)
              (orderedPreimageBag σ U)).card
            = ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                (S.matrixPartitionOfTwoStates σ (i + 1) i)
                  (orderedPreimageBag σ U)).image
                (orderedImageBag σ)).card := himage_card.symm
        _ ≤ target.card := Finset.card_le_card hsubset
        _ ≤ ((S.state (i + 1)).bags.filter fun Y =>
              (S.state (i + 1)).redAdj U Y).card + 3 := by
            have hcard :=
              Finset.card_union_le
                ((S.state (i + 1)).bags.filter fun Y => (S.state (i + 1)).redAdj U Y)
                ({A, B, U} : Finset (Finset V))
            have hspecial : ({A, B, U} : Finset (Finset V)).card ≤ 3 := by
              calc
                ({A, B, U} : Finset (Finset V)).card ≤
                    ({B, U} : Finset (Finset V)).card + 1 :=
                  Finset.card_insert_le _ _
                _ ≤ ({U} : Finset (Finset V)).card + 2 := by
                  have h := Finset.card_insert_le B ({U} : Finset (Finset V))
                  omega
                _ ≤ 3 := by simp
            have htarget_card :
                target.card ≤
                  ((S.state (i + 1)).bags.filter fun Y =>
                    (S.state (i + 1)).redAdj U Y).card +
                    ({A, B, U} : Finset (Finset V)).card := by
              simpa [target] using hcard
            omega
        _ ≤ d + 3 := by
            have hred := S.redDegree_le (i + 1) (by omega : i + 1 ≤ S.stepCount) hU
            simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 3
    · rcases S.stepPairAt_next_mem_cases hi hXnext with hmerged | hXold_data
      · exact (hXU (by simpa [A, B, U] using hmerged)).elim
      · rcases hXold_data with ⟨hXold, _hXA, _hXB⟩
        let target : Finset (Finset V) :=
          ((S.state i).bags.filter fun Y => (S.state i).redAdj X Y) ∪
            ({X} : Finset (Finset V))
        have hsubset :
            (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                (S.matrixPartitionOfTwoStates σ (i + 1) i)
                  (orderedPreimageBag σ X)).image
                (orderedImageBag σ) ⊆ target := by
          intro Y hY
          rcases Finset.mem_image.mp hY with ⟨C, hCerr, rfl⟩
          rcases Finset.mem_filter.mp hCerr with ⟨hCpart, hnon⟩
          rcases Finset.mem_image.mp hCpart with ⟨Y₀, hY₀old, rfl⟩
          rw [orderedImageBag_orderedPreimageBag]
          have hred_or :=
            nonconstant_preimage_imp_red_or_same σ hsemCur hXold hY₀old hnon
          rcases hred_or with hred | hsame
          · exact Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hY₀old, hred⟩)
          · subst Y₀
            exact Finset.mem_union_right _ (by simp)
        have himage_card :
            ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                (S.matrixPartitionOfTwoStates σ (i + 1) i)
                  (orderedPreimageBag σ X)).image
                (orderedImageBag σ)).card =
              (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                (S.matrixPartitionOfTwoStates σ (i + 1) i)
                  (orderedPreimageBag σ X)).card := by
          rw [Finset.card_image_of_injective]
          exact orderedImageBag_injective σ
        calc
          (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i)
                (orderedPreimageBag σ X)).card
              = ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                  (S.matrixPartitionOfTwoStates σ (i + 1) i)
                    (orderedPreimageBag σ X)).image
                  (orderedImageBag σ)).card := himage_card.symm
          _ ≤ target.card := Finset.card_le_card hsubset
          _ ≤ ((S.state i).bags.filter fun Y => (S.state i).redAdj X Y).card + 1 := by
              have hcard :=
                Finset.card_union_le
                  ((S.state i).bags.filter fun Y => (S.state i).redAdj X Y)
                  ({X} : Finset (Finset V))
              simpa [target] using hcard
          _ ≤ d + 3 := by
              have hred := S.redDegree_le i (by omega : i ≤ S.stepCount) hXold
              have hle : ((S.state i).bags.filter fun Y => (S.state i).redAdj X Y).card + 1
                  ≤ d + 1 := by
                simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 1
              omega
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨Y, hYold, rfl⟩
    let target : Finset (Finset V) :=
      ((S.state i).bags.filter fun X => (S.state i).redAdj Y X) ∪
        ({Y, U} : Finset (Finset V))
    have hsubset :
        (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfTwoStates σ (i + 1) i) (orderedPreimageBag σ Y)).image
            (orderedImageBag σ) ⊆ target := by
      intro X hX
      rcases Finset.mem_image.mp hX with ⟨R, hRerr, rfl⟩
      rcases Finset.mem_filter.mp hRerr with ⟨hRpart, hnon⟩
      rcases Finset.mem_image.mp hRpart with ⟨X₀, hX₀next, rfl⟩
      rw [orderedImageBag_orderedPreimageBag]
      rcases S.stepPairAt_next_mem_cases hi hX₀next with hmerged | hXold_data
      · have hXU : X₀ = U := by
          simpa [A, B, U] using hmerged
        rw [hXU]
        exact Finset.mem_union_right _ (by simp)
      · rcases hXold_data with ⟨hX₀old, _hXA, _hXB⟩
        have hred_or :=
          nonconstant_preimage_imp_red_or_same σ hsemCur hX₀old hYold hnon
        rcases hred_or with hred | hsame
        · have hredYX := (S.state i).red_symm hX₀old hYold hred
          exact Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hX₀old, hredYX⟩)
        · subst X₀
          exact Finset.mem_union_right _ (by simp)
    have himage_card :
        ((Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfTwoStates σ (i + 1) i)
              (orderedPreimageBag σ Y)).image
            (orderedImageBag σ)).card =
          (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfTwoStates σ (i + 1) i)
              (orderedPreimageBag σ Y)).card := by
      rw [Finset.card_image_of_injective]
      exact orderedImageBag_injective σ
    calc
      (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
          (S.matrixPartitionOfTwoStates σ (i + 1) i)
            (orderedPreimageBag σ Y)).card
          = ((Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i)
                (orderedPreimageBag σ Y)).image
              (orderedImageBag σ)).card := himage_card.symm
      _ ≤ target.card := Finset.card_le_card hsubset
      _ ≤ ((S.state i).bags.filter fun X => (S.state i).redAdj Y X).card + 2 := by
          have hcard :=
            Finset.card_union_le
              ((S.state i).bags.filter fun X => (S.state i).redAdj Y X)
              ({Y, U} : Finset (Finset V))
          have hspecial : ({Y, U} : Finset (Finset V)).card ≤ 2 := by
            calc
              ({Y, U} : Finset (Finset V)).card ≤
                  ({U} : Finset (Finset V)).card + 1 :=
                Finset.card_insert_le _ _
              _ ≤ 2 := by simp
          have htarget_card :
              target.card ≤
                ((S.state i).bags.filter fun X => (S.state i).redAdj Y X).card +
                  ({Y, U} : Finset (Finset V)).card := by
            simpa [target] using hcard
          omega
      _ ≤ d + 3 := by
          have hred := S.redDegree_le i (by omega : i ≤ S.stepCount) hYold
          have hle : ((S.state i).bags.filter fun X => (S.state i).redAdj Y X).card + 2
              ≤ d + 2 := by
            simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 2
          omega

/-- Walk a contraction sequence backward for `r` steps, starting from the final
bag list and splitting each merged bag into its left and right children. -/
noncomputable def reverseBagList
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) : ℕ → List (Finset V)
  | 0 => (S.state S.stepCount).bags.toList
  | r + 1 =>
      let L := reverseBagList S r
      let i := S.stepCount - (r + 1)
      if i < S.stepCount then
        let p := S.stepPairAt i
        splitMergedBag p.1 p.2 L
      else
        L

/-- The ordered bag list at forward time `i`, read from left to right in the
eventual leaf order.  Outside the declared time interval it is pinned to the
initial list; all mathematical uses pass `i ≤ stepCount`. -/
noncomputable def bagListAt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (i : ℕ) : List (Finset V) :=
  S.reverseBagList (S.stepCount - i)

theorem reverseBagList_toFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ r, r ≤ S.stepCount →
      (S.reverseBagList r).toFinset = (S.state (S.stepCount - r)).bags := by
  classical
  intro r hr
  induction r with
  | zero =>
      simp [reverseBagList]
  | succ r ih =>
      have hrle : r ≤ S.stepCount := by omega
      have hrlt : r < S.stepCount := by omega
      let i := S.stepCount - (r + 1)
      have hi : i < S.stepCount := by dsimp [i]; omega
      have hnext : S.stepCount - r = i + 1 := by dsimp [i]; omega
      have hcur : S.stepCount - (r + 1) = i := by rfl
      let p := S.stepPairAt i
      have hpspec := S.stepPairAt_spec hi
      have hpA : p.1 ∈ (S.state i).bags := hpspec.1
      have hpB : p.2 ∈ (S.state i).bags := hpspec.2.1
      have hpAB : p.1 ≠ p.2 := hpspec.2.2.1
      have hmerge :
          (S.state (i + 1)).bags =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := hpspec.2.2.2
      have hL :
          (S.reverseBagList r).toFinset =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := by
        calc
          (S.reverseBagList r).toFinset = (S.state (S.stepCount - r)).bags := ih hrle
          _ = (S.state (i + 1)).bags := by rw [hnext]
          _ = insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := hmerge
      have hpart : IsBagPartition (S.state i).bags :=
        ⟨(S.state i).bag_nonempty, (S.state i).bag_disjoint, (S.state i).bag_cover⟩
      simp [reverseBagList, i, hi, p, hcur,
        splitMergedBag_toFinset_of_merge hpart hpA hpB hpAB hL]

theorem reverseBagList_nodup
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ r, r ≤ S.stepCount → (S.reverseBagList r).Nodup := by
  classical
  intro r hr
  induction r with
  | zero =>
      simp [reverseBagList, Finset.nodup_toList]
  | succ r ih =>
      have hrle : r ≤ S.stepCount := by omega
      have hrlt : r < S.stepCount := by omega
      let i := S.stepCount - (r + 1)
      have hi : i < S.stepCount := by dsimp [i]; omega
      have hnext : S.stepCount - r = i + 1 := by dsimp [i]; omega
      let p := S.stepPairAt i
      have hpspec := S.stepPairAt_spec hi
      have hpA : p.1 ∈ (S.state i).bags := hpspec.1
      have hpB : p.2 ∈ (S.state i).bags := hpspec.2.1
      have hpAB : p.1 ≠ p.2 := hpspec.2.2.1
      have hmerge :
          (S.state (i + 1)).bags =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := hpspec.2.2.2
      have hL :
          (S.reverseBagList r).toFinset =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := by
        calc
          (S.reverseBagList r).toFinset = (S.state (S.stepCount - r)).bags :=
            S.reverseBagList_toFinset r hrle
          _ = (S.state (i + 1)).bags := by rw [hnext]
          _ = insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := hmerge
      have hpart : IsBagPartition (S.state i).bags :=
        ⟨(S.state i).bag_nonempty, (S.state i).bag_disjoint, (S.state i).bag_cover⟩
      simp [reverseBagList, i, hi, p,
        splitMergedBag_nodup_of_merge hpart hpA hpB hpAB (ih hrle) hL]

theorem bagListAt_toFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    (S.bagListAt i).toFinset = (S.state i).bags := by
  have hsub : S.stepCount - (S.stepCount - i) = i := by omega
  simpa [bagListAt, hsub] using
    S.reverseBagList_toFinset (S.stepCount - i) (by omega : S.stepCount - i ≤ S.stepCount)

theorem bagListAt_nodup
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    (S.bagListAt i).Nodup := by
  simpa [bagListAt] using
    S.reverseBagList_nodup (S.stepCount - i) (by omega : S.stepCount - i ≤ S.stepCount)

/-- The ordered bag list at time `i` has exactly one entry per current bag. -/
theorem bagListAt_length
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    (S.bagListAt i).length = (S.state i).bags.card := by
  rw [← List.toFinset_card_of_nodup (S.bagListAt_nodup hi),
    S.bagListAt_toFinset hi]

/-- One graph contraction shortens the left-to-right bag list by one. -/
theorem bagListAt_length_succ_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    (S.bagListAt (i + 1)).length + 1 = (S.bagListAt i).length := by
  rw [S.bagListAt_length (by omega : i + 1 ≤ S.stepCount),
    S.bagListAt_length (by omega : i ≤ S.stepCount)]
  exact S.bags_card_add_one hi

/-- In a nonempty graph, the bag list at time `i` has `stepCount - i + 1`
entries. -/
theorem bagListAt_length_eq_stepCount_sub_add_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    (S.bagListAt i).length = S.stepCount - i + 1 := by
  have hlen := S.bagListAt_length hi
  have hcount := S.bags_card_add_index (i := i) hi
  have hsteps := S.stepCount_add_one_eq_card
  omega

theorem bagListAt_step_eq_split
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    S.bagListAt i =
      let p := S.stepPairAt i
      splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) := by
  classical
  let r := S.stepCount - (i + 1)
  have hstep : S.stepCount - i = r + 1 := by dsimp [r]; omega
  have hr_index : S.stepCount - (r + 1) = i := by dsimp [r]; omega
  by_cases h : i < S.stepCount
  · simp [bagListAt, hstep, reverseBagList, r, hr_index, h]
  · exact (h hi).elim

/-- The ordered list of singleton bags obtained by reading the leaves of the
contraction tree from left to right. -/
noncomputable def leafBagList
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) : List (Finset V) :=
  S.reverseBagList S.stepCount

theorem leafBagList_toFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.leafBagList.toFinset = TrigraphState.singletonBags V := by
  simpa [leafBagList, S.starts.1] using
    S.reverseBagList_toFinset S.stepCount le_rfl

theorem leafBagList_nodup
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.leafBagList.Nodup := by
  simpa [leafBagList] using S.reverseBagList_nodup S.stepCount le_rfl

theorem leafBagList_length
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.leafBagList.length = Fintype.card V := by
  classical
  rw [← List.toFinset_card_of_nodup S.leafBagList_nodup,
    S.leafBagList_toFinset, TrigraphState.card_singletonBags]

noncomputable def leafBagVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    (A : {A : Finset V // A ∈ S.leafBagList}) : V :=
  Classical.choose <| TrigraphState.mem_singletonBags.mp <| by
    have hA : A.1 ∈ S.leafBagList.toFinset := List.mem_toFinset.mpr A.2
    simpa [S.leafBagList_toFinset] using hA

theorem leafBagVertex_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    (A : {A : Finset V // A ∈ S.leafBagList}) :
    A.1 = {S.leafBagVertex A} := by
  unfold leafBagVertex
  exact Classical.choose_spec <| TrigraphState.mem_singletonBags.mp <| by
    have hA : A.1 ∈ S.leafBagList.toFinset := List.mem_toFinset.mpr A.2
    simpa [S.leafBagList_toFinset] using hA

/-- The equivalence from leaf singleton bags to vertices. -/
noncomputable def leafBagEquivVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    {A : Finset V // A ∈ S.leafBagList} ≃ V where
  toFun := S.leafBagVertex
  invFun v := ⟨{v}, by
    have h : ({v} : Finset V) ∈ S.leafBagList.toFinset := by
      rw [S.leafBagList_toFinset]
      exact TrigraphState.mem_singletonBags.mpr ⟨v, rfl⟩
    exact List.mem_toFinset.mp h⟩
  left_inv A := by
    apply Subtype.ext
    exact (S.leafBagVertex_spec A).symm
  right_inv v := by
    have h :=
      S.leafBagVertex_spec
        (⟨{v}, by
          have h : ({v} : Finset V) ∈ S.leafBagList.toFinset := by
            rw [S.leafBagList_toFinset]
            exact TrigraphState.mem_singletonBags.mpr ⟨v, rfl⟩
          exact List.mem_toFinset.mp h⟩ :
          {A : Finset V // A ∈ S.leafBagList})
    exact (Finset.singleton_inj.mp h).symm

/-- The left-to-right order on leaves of the contraction tree. -/
noncomputable def leafOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) : VertexOrder V (Fintype.card V) where
  equiv :=
    (finCongr S.leafBagList_length.symm).trans
      ((List.Nodup.getEquiv S.leafBagList S.leafBagList_nodup).trans
        S.leafBagEquivVertex)

theorem leafOrder_singleton_eq_get
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (i : Fin (Fintype.card V)) :
    ({S.leafOrder.equiv i} : Finset V) =
      S.leafBagList.get ((finCongr S.leafBagList_length.symm) i) := by
  classical
  let j : Fin S.leafBagList.length := (finCongr S.leafBagList_length.symm) i
  have hspec :=
    S.leafBagVertex_spec
      ((List.Nodup.getEquiv S.leafBagList S.leafBagList_nodup) j)
  change ({S.leafBagVertex
      ((List.Nodup.getEquiv S.leafBagList S.leafBagList_nodup) j)} : Finset V) =
      S.leafBagList.get j
  exact hspec.symm

/-- A certificate that an ordered bag list is represented by consecutive
interval parts in the leaf order. -/
structure BagListDivision
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (L : List (Finset V)) where
  /-- The interval division whose parts are the ordered preimages of `L`. -/
  div : Division (Fintype.card V) L.length
  /-- The `i`-th interval is exactly the preimage of the `i`-th bag. -/
  part_eq :
    ∀ i : Fin L.length,
      div.part i = orderedPreimageBag S.leafOrder (L.get i)

/-- The leaf bag list is represented by the finest interval division. -/
noncomputable def leafBagListDivision
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.BagListDivision S.leafBagList where
  div :=
    Division.castIndex S.leafBagList_length.symm
      (Division.singleton (Fintype.card V))
  part_eq := by
    classical
    intro i
    let r : Fin (Fintype.card V) := (finCongr S.leafBagList_length.symm).symm i
    have hget : ({S.leafOrder.equiv r} : Finset V) = S.leafBagList.get i := by
      simpa [r] using S.leafOrder_singleton_eq_get r
    ext x
    constructor
    · intro hx
      have hxrow : x = r := by
        simpa [Division.castIndex, Division.singleton, r] using hx
      subst x
      rw [← hget]
      simp [orderedPreimageBag]
    · intro hx
      have hxrow : x = r := by
        have hxmem_get : S.leafOrder.equiv x ∈ S.leafBagList.get i := by
          simpa [orderedPreimageBag] using hx
        have hxmem : S.leafOrder.equiv x ∈ ({S.leafOrder.equiv r} : Finset V) := by
          simpa [hget] using hxmem_get
        have heq : S.leafOrder.equiv x = S.leafOrder.equiv r := by
          simpa using hxmem
        exact S.leafOrder.equiv.injective heq
      simp [Division.castIndex, Division.singleton, r, hxrow]

namespace BagListDivision

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {d : ℕ}
variable (S : ContractionSequence G d)

/-- Reindex a bag-list division along an equality of its underlying list. -/
noncomputable def castList {L L' : List (Finset V)}
    (D : S.BagListDivision L) (h : L = L') :
    S.BagListDivision L' where
  div := Division.castIndex (congrArg List.length h) D.div
  part_eq := by
    subst L'
    intro i
    simpa [Division.castIndex] using D.part_eq i

omit [Fintype V] [DecidableEq V] in
private theorem get_pair_left
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    (P ++ [A, B] ++ Q).get ((finCongr hcur).symm idx.castSucc) = A := by
  classical
  dsimp
  simp

omit [Fintype V] [DecidableEq V] in
private theorem get_pair_right
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    (P ++ [A, B] ++ Q).get ((finCongr hcur).symm idx.succ) = B := by
  classical
  dsimp
  simp

omit [Fintype V] in
private theorem get_merged
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm idx) = A ∪ B := by
  classical
  dsimp
  simp

omit [Fintype V] in
private theorem get_before_fused_pair
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    ∀ (j : Fin (P ++ [A ∪ B] ++ Q).length),
      ((finCongr hnext) j).1 < P.length →
        (P ++ [A, B] ++ Q).get
            ((finCongr hcur).symm ((finCongr hnext) j).castSucc) =
          (P ++ [A ∪ B] ++ Q).get j := by
  classical
  dsimp
  intro j hj
  simp [List.getElem_append_left, hj]

omit [Fintype V] in
private theorem get_after_fused_pair
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    ∀ (j : Fin (P ++ [A ∪ B] ++ Q).length),
      P.length < ((finCongr hnext) j).1 →
        (P ++ [A, B] ++ Q).get
            ((finCongr hcur).symm ((finCongr hnext) j).succ) =
          (P ++ [A ∪ B] ++ Q).get j := by
  classical
  dsimp
  intro j hj
  obtain ⟨t, ht⟩ : ∃ t, j.1 = P.length + 1 + t :=
    ⟨j.1 - P.length - 1, by omega⟩
  have hnot1 : ¬ P.length + 1 + t + 1 < P.length := by omega
  have hnot2 : ¬ P.length + 1 + t < P.length := by omega
  have hsub1 : P.length + 1 + t + 1 - P.length = t + 2 := by omega
  have hsub2 : P.length + 1 + t - P.length = t + 1 := by omega
  simp [List.getElem_append, ht, hnot1, hnot2, hsub1, hsub2]

/-- Fuse the two adjacent list entries `A` and `B` into `A ∪ B`, carrying the
associated interval division along by the corresponding division fusion. -/
noncomputable def mergeAdjacent
    {P Q : List (Finset V)} {A B : Finset V}
    (D : S.BagListDivision (P ++ [A, B] ++ Q)) :
    S.BagListDivision (P ++ [A ∪ B] ++ Q) :=
  let k := P.length + Q.length
  let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
  let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
  let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
  let Dcur : Division (Fintype.card V) (k + 2) := Division.castIndex hcur D.div
  let Dnext : Division (Fintype.card V) (k + 1) := Dcur.fuse idx
  { div := Division.castIndex hnext.symm Dnext
    part_eq := by
      classical
      intro j
      let j' : Fin (k + 1) := (finCongr hnext) j
      have hpart_cur :
          ∀ a : Fin (k + 2),
            Dcur.part a =
              orderedPreimageBag S.leafOrder
                ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm a)) := by
        intro a
        simpa [Dcur, Division.castIndex] using D.part_eq ((finCongr hcur).symm a)
      have htarget :
          (P ++ [A ∪ B] ++ Q).get j =
            (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j') := by
        simp [j']
      by_cases hji : j' = idx
      ·
        have hleft :
            Dcur.part idx.castSucc =
              orderedPreimageBag S.leafOrder A := by
          rw [hpart_cur idx.castSucc]
          rw [get_pair_left (V := V) P Q A B]
        have hright :
            Dcur.part idx.succ =
              orderedPreimageBag S.leafOrder B := by
          rw [hpart_cur idx.succ]
          rw [get_pair_right (V := V) P Q A B]
        have hget :
            (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm idx) = A ∪ B :=
          get_merged (V := V) P Q A B
        have hgetj :
            (P ++ [A ∪ B] ++ Q).get j = A ∪ B := by
          calc
            (P ++ [A ∪ B] ++ Q).get j
                = (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j') := htarget
            _ = (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm idx) := by
                rw [hji]
            _ = A ∪ B := hget
        calc
          (Division.castIndex hnext.symm Dnext).part j
              = Dnext.part j' := by
                  simp [Dnext, Division.castIndex, j']
          _ = Dnext.part idx := by
                  rw [hji]
          _ = Dcur.part idx.castSucc ∪ Dcur.part idx.succ := by
                  simp [Dnext, Division.fuse_part_self]
          _ = orderedPreimageBag S.leafOrder A ∪ orderedPreimageBag S.leafOrder B := by
                  rw [hleft, hright]
          _ = orderedPreimageBag S.leafOrder (A ∪ B) := by
                  rw [orderedPreimageBag_union]
          _ = orderedPreimageBag S.leafOrder
                ((P ++ [A ∪ B] ++ Q).get j) := by
                  rw [hgetj]
      · rcases lt_or_gt_of_ne hji with hlt | hgt
        · have hcur_get :
              (P ++ [A, B] ++ Q).get ((finCongr hcur).symm j'.castSucc) =
                (P ++ [A ∪ B] ++ Q).get j :=
            get_before_fused_pair (V := V) P Q A B j hlt
          calc
            (Division.castIndex hnext.symm Dnext).part j
                = Dnext.part j' := by simp [Dnext, Division.castIndex, j']
            _ = Dcur.part j'.castSucc := by
                exact Division.fuse_part_of_lt Dcur hlt
            _ = orderedPreimageBag S.leafOrder
                  ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm j'.castSucc)) := by
                rw [hpart_cur j'.castSucc]
            _ = orderedPreimageBag S.leafOrder ((P ++ [A ∪ B] ++ Q).get j) := by
                rw [hcur_get]
        · have hcur_get :
              (P ++ [A, B] ++ Q).get ((finCongr hcur).symm j'.succ) =
                (P ++ [A ∪ B] ++ Q).get j :=
            get_after_fused_pair (V := V) P Q A B j hgt
          calc
            (Division.castIndex hnext.symm Dnext).part j
                = Dnext.part j' := by simp [Dnext, Division.castIndex, j']
            _ = Dcur.part j'.succ := by
                exact Division.fuse_part_of_gt Dcur hgt
            _ = orderedPreimageBag S.leafOrder
                  ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm j'.succ)) := by
                rw [hpart_cur j'.succ]
            _ = orderedPreimageBag S.leafOrder ((P ++ [A ∪ B] ++ Q).get j) := by
                rw [hcur_get] }

/-- The division inside `mergeAdjacent` is exactly the fusion of the two
adjacent old parts corresponding to `A` and `B`. -/
theorem mergeAdjacent_isFusionAt
    {P Q : List (Finset V)} {A B : Finset V}
    (D : S.BagListDivision (P ++ [A, B] ++ Q)) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    let Dcur : Division (Fintype.card V) (k + 2) := Division.castIndex hcur D.div
    Division.IsFusionAt Dcur
      (Division.castIndex hnext (BagListDivision.mergeAdjacent (S := S) D).div)
      idx := by
  classical
  dsimp [mergeAdjacent]
  intro j
  exact Division.isFusionAt_fuse _ _ j

/-- Any interval certificates for two adjacent bag lists related by merging
`A` and `B` are related by the corresponding division fusion.  This removes
any dependence on which proof object was chosen for either list. -/
theorem isFusionAt_of_adjacent_merge
    {P Q : List (Finset V)} {A B : Finset V}
    (Dcur : S.BagListDivision (P ++ [A, B] ++ Q))
    (Dnext : S.BagListDivision (P ++ [A ∪ B] ++ Q)) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    Division.IsFusionAt
      (Division.castIndex hcur Dcur.div)
      (Division.castIndex hnext Dnext.div)
      idx := by
  classical
  dsimp
  intro j
  let k := P.length + Q.length
  let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
  let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
  let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
  let DcurCast : Division (Fintype.card V) (k + 2) :=
    Division.castIndex hcur Dcur.div
  have hcur_part :
      ∀ a : Fin (k + 2),
        DcurCast.part a =
          orderedPreimageBag S.leafOrder
            ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm a)) := by
    intro a
    simpa [DcurCast, Division.castIndex] using Dcur.part_eq ((finCongr hcur).symm a)
  have hnext_part :
      ∀ a : Fin (k + 1),
        (Division.castIndex hnext Dnext.div).part a =
          orderedPreimageBag S.leafOrder
            ((P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm a)) := by
    intro a
    simpa [Division.castIndex] using Dnext.part_eq ((finCongr hnext).symm a)
  by_cases hji : j = idx
  · subst j
    have hleft :
        DcurCast.part idx.castSucc = orderedPreimageBag S.leafOrder A := by
      rw [hcur_part idx.castSucc]
      rw [get_pair_left (V := V) P Q A B]
    have hright :
        DcurCast.part idx.succ = orderedPreimageBag S.leafOrder B := by
      rw [hcur_part idx.succ]
      rw [get_pair_right (V := V) P Q A B]
    have hget :
        (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm idx) = A ∪ B :=
      get_merged (V := V) P Q A B
    calc
      (Division.castIndex hnext Dnext.div).part idx
          = orderedPreimageBag S.leafOrder (A ∪ B) := by
              rw [hnext_part idx, hget]
      _ = orderedPreimageBag S.leafOrder A ∪ orderedPreimageBag S.leafOrder B := by
              rw [orderedPreimageBag_union]
      _ = DcurCast.part idx.castSucc ∪ DcurCast.part idx.succ := by
              rw [hleft, hright]
      _ = DcurCast.fusePart idx idx := by
              simp [Division.fusePart]
  · rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hcur_get :
          (P ++ [A, B] ++ Q).get ((finCongr hcur).symm j.castSucc) =
            (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j) := by
        simpa using
          get_before_fused_pair (V := V) P Q A B ((finCongr hnext).symm j) hlt
      calc
        (Division.castIndex hnext Dnext.div).part j
            = orderedPreimageBag S.leafOrder
                ((P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j)) := hnext_part j
        _ = orderedPreimageBag S.leafOrder
                ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm j.castSucc)) := by
            rw [hcur_get]
        _ = DcurCast.part j.castSucc := by
            rw [hcur_part j.castSucc]
        _ = DcurCast.fusePart idx j := by
            simp [Division.fusePart, ne_of_lt hlt, hlt]
    · have hcur_get :
          (P ++ [A, B] ++ Q).get ((finCongr hcur).symm j.succ) =
            (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j) := by
        simpa using
          get_after_fused_pair (V := V) P Q A B ((finCongr hnext).symm j) hgt
      have hnlt : ¬ j < idx := not_lt_of_ge (le_of_lt hgt)
      calc
        (Division.castIndex hnext Dnext.div).part j
            = orderedPreimageBag S.leafOrder
                ((P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j)) := hnext_part j
        _ = orderedPreimageBag S.leafOrder
                ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm j.succ)) := by
            rw [hcur_get]
        _ = DcurCast.part j.succ := by
            rw [hcur_part j.succ]
        _ = DcurCast.fusePart idx j := by
            simp [Division.fusePart, ne_of_gt hgt, hnlt]

end BagListDivision

/-- The matrix division obtained from row and column bag-list interval
certificates.  The positivity hypotheses are exactly the nonempty-graph
zerology needed to write the number of parts as `cuts + 1`. -/
noncomputable def matrixDivisionOfBagLists
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    {LR LC : List (Finset V)}
    (R : S.BagListDivision LR) (C : S.BagListDivision LC)
    (hR : 0 < LR.length) (hC : 0 < LC.length) :
    Matrix.MatrixDivision (Fintype.card V) (Fintype.card V) where
  rowCuts := LR.length - 1
  colCuts := LC.length - 1
  rowDiv := Division.castIndex (by omega : LR.length = (LR.length - 1) + 1) R.div
  colDiv := Division.castIndex (by omega : LC.length = (LC.length - 1) + 1) C.div

/-- Matrix division from bag-list certificates with explicit numbers of row
and column cuts.  This version is used in fusion proofs because the equations
`length = cuts + 1` avoid the casts introduced by `length - 1`. -/
noncomputable def matrixDivisionOfBagListsWithCuts
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    {LR LC : List (Finset V)}
    (R : S.BagListDivision LR) (C : S.BagListDivision LC)
    (r c : ℕ) (hR : LR.length = r + 1) (hC : LC.length = c + 1) :
    Matrix.MatrixDivision (Fintype.card V) (Fintype.card V) where
  rowCuts := r
  colCuts := c
  rowDiv := Division.castIndex hR R.div
  colDiv := Division.castIndex hC C.div

/-- The unordered partition underlying the explicit matrix division from
bag-list certificates is exactly the partition whose rows and columns are the
corresponding trigraph states. -/
theorem toPartition_matrixDivisionOfBagListsWithCuts_eq_matrixPartitionOfTwoStates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    {rowTime colTime r c : ℕ}
    (hrowTime : rowTime ≤ S.stepCount) (hcolTime : colTime ≤ S.stepCount)
    (R : S.BagListDivision (S.bagListAt rowTime))
    (C : S.BagListDivision (S.bagListAt colTime))
    (hR : (S.bagListAt rowTime).length = r + 1)
    (hC : (S.bagListAt colTime).length = c + 1) :
    (S.matrixDivisionOfBagListsWithCuts R C r c hR hC).toPartition =
      S.matrixPartitionOfTwoStates S.leafOrder rowTime colTime := by
  classical
  let D := S.matrixDivisionOfBagListsWithCuts R C r c hR hC
  apply Matrix.MatrixPartition.ext_parts
  · ext X
    constructor
    · intro hX
      rcases Finset.mem_map.mp hX with ⟨a, _ha, haX⟩
      change D.rowDiv.part a = X at haX
      let a' : Fin (S.bagListAt rowTime).length := (finCongr hR).symm a
      have hpart :
          D.rowDiv.part a =
            orderedPreimageBag S.leafOrder ((S.bagListAt rowTime).get a') := by
        simpa [D, matrixDivisionOfBagListsWithCuts, Division.castIndex, a'] using
          R.part_eq a'
      have hbag_state :
          (S.bagListAt rowTime).get a' ∈ (S.state rowTime).bags := by
        have hmem_list : (S.bagListAt rowTime).get a' ∈ S.bagListAt rowTime :=
          List.get_mem _ _
        have hmem_finset :
            (S.bagListAt rowTime).get a' ∈ (S.bagListAt rowTime).toFinset :=
          List.mem_toFinset.mpr hmem_list
        simpa [S.bagListAt_toFinset hrowTime] using hmem_finset
      refine Finset.mem_image.mpr
        ⟨(S.bagListAt rowTime).get a', hbag_state, ?_⟩
      rw [← hpart, haX]
    · intro hX
      rcases Finset.mem_image.mp hX with ⟨A, hAstate, rfl⟩
      have hA_finset : A ∈ (S.bagListAt rowTime).toFinset := by
        simpa [S.bagListAt_toFinset hrowTime] using hAstate
      have hA_list : A ∈ S.bagListAt rowTime := List.mem_toFinset.mp hA_finset
      rcases List.mem_iff_get.mp hA_list with ⟨a, ha⟩
      refine Finset.mem_map.mpr ⟨finCongr hR a, Finset.mem_univ _, ?_⟩
      change D.rowDiv.part (finCongr hR a) = orderedPreimageBag S.leafOrder A
      calc
        D.rowDiv.part (finCongr hR a) = R.div.part a := by
          simp [D, matrixDivisionOfBagListsWithCuts, Division.castIndex]
        _ = orderedPreimageBag S.leafOrder ((S.bagListAt rowTime).get a) := R.part_eq a
        _ = orderedPreimageBag S.leafOrder A := by rw [ha]
  · ext X
    constructor
    · intro hX
      rcases Finset.mem_map.mp hX with ⟨a, _ha, haX⟩
      change D.colDiv.part a = X at haX
      let a' : Fin (S.bagListAt colTime).length := (finCongr hC).symm a
      have hpart :
          D.colDiv.part a =
            orderedPreimageBag S.leafOrder ((S.bagListAt colTime).get a') := by
        simpa [D, matrixDivisionOfBagListsWithCuts, Division.castIndex, a'] using
          C.part_eq a'
      have hbag_state :
          (S.bagListAt colTime).get a' ∈ (S.state colTime).bags := by
        have hmem_list : (S.bagListAt colTime).get a' ∈ S.bagListAt colTime :=
          List.get_mem _ _
        have hmem_finset :
            (S.bagListAt colTime).get a' ∈ (S.bagListAt colTime).toFinset :=
          List.mem_toFinset.mpr hmem_list
        simpa [S.bagListAt_toFinset hcolTime] using hmem_finset
      refine Finset.mem_image.mpr
        ⟨(S.bagListAt colTime).get a', hbag_state, ?_⟩
      rw [← hpart, haX]
    · intro hX
      rcases Finset.mem_image.mp hX with ⟨A, hAstate, rfl⟩
      have hA_finset : A ∈ (S.bagListAt colTime).toFinset := by
        simpa [S.bagListAt_toFinset hcolTime] using hAstate
      have hA_list : A ∈ S.bagListAt colTime := List.mem_toFinset.mp hA_finset
      rcases List.mem_iff_get.mp hA_list with ⟨a, ha⟩
      refine Finset.mem_map.mpr ⟨finCongr hC a, Finset.mem_univ _, ?_⟩
      change D.colDiv.part (finCongr hC a) = orderedPreimageBag S.leafOrder A
      calc
        D.colDiv.part (finCongr hC a) = C.div.part a := by
          simp [D, matrixDivisionOfBagListsWithCuts, Division.castIndex]
        _ = orderedPreimageBag S.leafOrder ((S.bagListAt colTime).get a) := C.part_eq a
        _ = orderedPreimageBag S.leafOrder A := by rw [ha]

/-- Transfer an error-value bound on the row/column state partition to the
corresponding interval matrix division. -/
theorem nonconstantErrorValueAtMost_matrixDivisionOfBagListsWithCuts
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d t : ℕ}
    (S : ContractionSequence G d)
    {rowTime colTime r c : ℕ}
    (hrowTime : rowTime ≤ S.stepCount) (hcolTime : colTime ≤ S.stepCount)
    (R : S.BagListDivision (S.bagListAt rowTime))
    (C : S.BagListDivision (S.bagListAt colTime))
    (hR : (S.bagListAt rowTime).length = r + 1)
    (hC : (S.bagListAt colTime).length = c + 1)
    (herr :
      Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
        (S.matrixPartitionOfTwoStates S.leafOrder rowTime colTime) t) :
    Matrix.MatrixDivision.NonconstantErrorValueAtMost
      (Matrix.orderedAdjacency G S.leafOrder)
      (S.matrixDivisionOfBagListsWithCuts R C r c hR hC) t := by
  classical
  apply Matrix.MatrixDivision.nonconstantErrorValueAtMost_of_errorValueAtMost_toPartition
  have hpart :=
    S.toPartition_matrixDivisionOfBagListsWithCuts_eq_matrixPartitionOfTwoStates
      hrowTime hcolTime R C hR hC
  simpa [hpart] using herr

namespace BagListDivision

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {d : ℕ}
variable (S : ContractionSequence G d)

theorem hasRowFusion_matrixDivisionOfBagListsWithCuts_adjacent_merge
    {P Q L : List (Finset V)} {A B : Finset V} {c : ℕ}
    (Rcur : S.BagListDivision (P ++ [A, B] ++ Q))
    (Rnext : S.BagListDivision (P ++ [A ∪ B] ++ Q))
    (C : S.BagListDivision L)
    (hC : L.length = c + 1) :
    Matrix.MatrixDivision.HasRowFusion
      (S.matrixDivisionOfBagListsWithCuts Rcur C (P.length + Q.length + 1) c
        (by simp; omega) hC)
      (S.matrixDivisionOfBagListsWithCuts Rnext C (P.length + Q.length) c
        (by simp; omega) hC) := by
  classical
  refine ⟨rfl, rfl, ⟨P.length, by simp [matrixDivisionOfBagListsWithCuts]; omega⟩, ?_, ?_⟩
  · simpa [matrixDivisionOfBagListsWithCuts] using
      isFusionAt_of_adjacent_merge (S := S) Rcur Rnext
  · intro j
    apply congrArg C.div.part
    ext
    rfl

theorem hasColFusion_matrixDivisionOfBagListsWithCuts_adjacent_merge
    {P Q L : List (Finset V)} {A B : Finset V} {r : ℕ}
    (R : S.BagListDivision L)
    (Ccur : S.BagListDivision (P ++ [A, B] ++ Q))
    (Cnext : S.BagListDivision (P ++ [A ∪ B] ++ Q))
    (hR : L.length = r + 1) :
    Matrix.MatrixDivision.HasColFusion
      (S.matrixDivisionOfBagListsWithCuts R Ccur r (P.length + Q.length + 1)
        hR (by simp; omega))
      (S.matrixDivisionOfBagListsWithCuts R Cnext r (P.length + Q.length)
        hR (by simp; omega)) := by
  classical
  refine ⟨rfl, rfl, ⟨P.length, by simp [matrixDivisionOfBagListsWithCuts]; omega⟩, ?_, ?_⟩
  · intro i
    apply congrArg R.div.part
    ext
    rfl
  · simpa [matrixDivisionOfBagListsWithCuts] using
      isFusionAt_of_adjacent_merge (S := S) Ccur Cnext

end BagListDivision

namespace BagListDivision

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {d : ℕ}
variable (S : ContractionSequence G d)

end BagListDivision

/-- Every left-to-right bag list along the contraction sequence is represented
by consecutive intervals in the leaf order. -/
theorem exists_bagListDivisionAt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ i : ℕ, i ≤ S.stepCount → Nonempty (S.BagListDivision (S.bagListAt i))
  | 0, _ => by
      have h0 : S.bagListAt 0 = S.leafBagList := by
        simp [bagListAt, leafBagList]
      exact ⟨by simpa [h0] using S.leafBagListDivision⟩
  | i + 1, hi => by
      classical
      have hlt : i < S.stepCount := by omega
      let p := S.stepPairAt i
      rcases S.exists_bagListDivisionAt i (by omega) with ⟨Dcur⟩
      have hsplit_step :
          S.bagListAt i = splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) := by
        simpa [p] using S.bagListAt_step_eq_split hlt
      have hpspec := S.stepPairAt_spec hlt
      have hmerge :
          (S.state (i + 1)).bags =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := by
        simpa [p] using hpspec.2.2.2
      have hmerged_state : p.1 ∪ p.2 ∈ (S.state (i + 1)).bags := by
        rw [hmerge]
        simp
      have hmerged_list : p.1 ∪ p.2 ∈ S.bagListAt (i + 1) := by
        have hmem_finset : p.1 ∪ p.2 ∈ (S.bagListAt (i + 1)).toFinset := by
          rw [S.bagListAt_toFinset (by omega : i + 1 ≤ S.stepCount)]
          exact hmerged_state
        exact List.mem_toFinset.mp hmem_finset
      rcases exists_splitMergedBag_eq_append_of_mem_nodup
          (S.bagListAt_nodup (by omega : i + 1 ≤ S.stepCount)) hmerged_list with
        ⟨P, Q, hnext, _hnotP, _hnotQ, hsplit⟩
      have hcur : S.bagListAt i = P ++ [p.1, p.2] ++ Q := by
        rw [hsplit_step, hsplit]
      let Dcur' : S.BagListDivision (P ++ [p.1, p.2] ++ Q) := by
        simpa [hcur] using Dcur
      have Dnext : S.BagListDivision (P ++ [p.1 ∪ p.2] ++ Q) :=
        BagListDivision.mergeAdjacent (S := S) Dcur'
      exact ⟨by simpa [hnext] using Dnext⟩

/-- A chosen interval division certificate for the bag list at time `i`. -/
noncomputable def bagListDivisionAt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ i : ℕ, i ≤ S.stepCount → S.BagListDivision (S.bagListAt i)
  | 0, _ => by
      have h0 : S.bagListAt 0 = S.leafBagList := by
        simp [bagListAt, leafBagList]
      simpa [h0] using S.leafBagListDivision
  | i + 1, hi => by
      classical
      have hlt : i < S.stepCount := by omega
      let p := S.stepPairAt i
      have Dcur : S.BagListDivision (S.bagListAt i) :=
        S.bagListDivisionAt i (by omega)
      have hsplit_step :
          S.bagListAt i = splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) := by
        simpa [p] using S.bagListAt_step_eq_split hlt
      have hpspec := S.stepPairAt_spec hlt
      have hmerge :
          (S.state (i + 1)).bags =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := by
        simpa [p] using hpspec.2.2.2
      have hmerged_state : p.1 ∪ p.2 ∈ (S.state (i + 1)).bags := by
        rw [hmerge]
        simp
      have hmerged_list : p.1 ∪ p.2 ∈ S.bagListAt (i + 1) := by
        have hmem_finset : p.1 ∪ p.2 ∈ (S.bagListAt (i + 1)).toFinset := by
          rw [S.bagListAt_toFinset (by omega : i + 1 ≤ S.stepCount)]
          exact hmerged_state
        exact List.mem_toFinset.mp hmem_finset
      let hex :=
        exists_splitMergedBag_eq_append_of_mem_nodup
          (S.bagListAt_nodup (by omega : i + 1 ≤ S.stepCount)) hmerged_list
      let P : List (Finset V) := Classical.choose hex
      let hexQ := Classical.choose_spec hex
      let Q : List (Finset V) := Classical.choose hexQ
      have hdata :
          S.bagListAt (i + 1) = P ++ [p.1 ∪ p.2] ++ Q ∧
            p.1 ∪ p.2 ∉ P ∧ p.1 ∪ p.2 ∉ Q ∧
              splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) =
                P ++ [p.1, p.2] ++ Q := by
        simpa [P, Q, hexQ] using Classical.choose_spec hexQ
      have hnext : S.bagListAt (i + 1) = P ++ [p.1 ∪ p.2] ++ Q := hdata.1
      have hsplit :
          splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) =
            P ++ [p.1, p.2] ++ Q := hdata.2.2.2
      have hcur : S.bagListAt i = P ++ [p.1, p.2] ++ Q := by
        rw [hsplit_step, hsplit]
      let Dcur' : S.BagListDivision (P ++ [p.1, p.2] ++ Q) := by
        simpa [hcur] using Dcur
      have Dnext : S.BagListDivision (P ++ [p.1 ∪ p.2] ++ Q) :=
        BagListDivision.mergeAdjacent (S := S) Dcur'
      simpa [hnext] using Dnext

@[simp] theorem bagListDivisionAt_proof_irrel
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi hi' : i ≤ S.stepCount) :
    S.bagListDivisionAt i hi = S.bagListDivisionAt i hi' := by
  have h : hi = hi' := proof_irrel _ _
  subst h
  rfl

/-- Reindexing the interval certificate at a fixed time is independent of the
chosen proof that the time is in range. -/
theorem bagListDivisionAt_castIndex_div_heq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i l l' : ℕ}
    (hi hi' : i ≤ S.stepCount)
    (h : (S.bagListAt i).length = l)
    (h' : (S.bagListAt i).length = l') :
    Division.castIndex h (S.bagListDivisionAt i hi).div ≍
      Division.castIndex h' (S.bagListDivisionAt i hi').div := by
  have hD : S.bagListDivisionAt i hi = S.bagListDivisionAt i hi' :=
    S.bagListDivisionAt_proof_irrel hi hi'
  cases hD
  exact Division.castIndex_heq h h' _

/-- Adjacent bag lists around one graph contraction, in the leaf order. -/
theorem exists_bagListAt_succ_eq_append_merge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    ∃ P Q : List (Finset V),
      S.bagListAt (i + 1) =
        P ++ [(S.stepPairAt i).1 ∪ (S.stepPairAt i).2] ++ Q ∧
      S.bagListAt i =
        P ++ [(S.stepPairAt i).1, (S.stepPairAt i).2] ++ Q := by
  classical
  let p := S.stepPairAt i
  have hsplit_step :
      S.bagListAt i = splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) := by
    simpa [p] using S.bagListAt_step_eq_split hi
  have hpspec := S.stepPairAt_spec hi
  have hmerge :
      (S.state (i + 1)).bags =
        insert (p.1 ∪ p.2)
          (((S.state i).bags.erase p.1).erase p.2) := by
    simpa [p] using hpspec.2.2.2
  have hmerged_state : p.1 ∪ p.2 ∈ (S.state (i + 1)).bags := by
    rw [hmerge]
    simp
  have hmerged_list : p.1 ∪ p.2 ∈ S.bagListAt (i + 1) := by
    have hmem_finset : p.1 ∪ p.2 ∈ (S.bagListAt (i + 1)).toFinset := by
      rw [S.bagListAt_toFinset (by omega : i + 1 ≤ S.stepCount)]
      exact hmerged_state
    exact List.mem_toFinset.mp hmem_finset
  rcases exists_splitMergedBag_eq_append_of_mem_nodup
      (S.bagListAt_nodup (by omega : i + 1 ≤ S.stepCount)) hmerged_list with
    ⟨P, Q, hnext, _hnotP, _hnotQ, hsplit⟩
  refine ⟨P, Q, ?_, ?_⟩
  · simpa [p] using hnext
  · rw [hsplit_step, hsplit]

/-- The matrix division whose row and column parts are the leaf-order interval
certificates for two times of the graph contraction sequence. -/
noncomputable def matrixDivisionAtTimes
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    (rowTime colTime : ℕ)
    (hrowTime : rowTime ≤ S.stepCount) (hcolTime : colTime ≤ S.stepCount) :
    Matrix.MatrixDivision (Fintype.card V) (Fintype.card V) :=
  S.matrixDivisionOfBagListsWithCuts
    (S.bagListDivisionAt rowTime hrowTime)
    (S.bagListDivisionAt colTime hcolTime)
    (S.stepCount - rowTime) (S.stepCount - colTime)
    (S.bagListAt_length_eq_stepCount_sub_add_one hrowTime)
    (S.bagListAt_length_eq_stepCount_sub_add_one hcolTime)

/-- Error transfer for the time-indexed matrix division used in the interleaved
row/column sequence. -/
theorem matrixDivisionAtTimes_nonconstantErrorValueAtMost
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d t : ℕ}
    (S : ContractionSequence G d)
    {rowTime colTime : ℕ}
    (hrowTime : rowTime ≤ S.stepCount) (hcolTime : colTime ≤ S.stepCount)
    (herr :
      Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
        (S.matrixPartitionOfTwoStates S.leafOrder rowTime colTime) t) :
    Matrix.MatrixDivision.NonconstantErrorValueAtMost
      (Matrix.orderedAdjacency G S.leafOrder)
      (S.matrixDivisionAtTimes rowTime colTime hrowTime hcolTime) t := by
  simpa [matrixDivisionAtTimes] using
    S.nonconstantErrorValueAtMost_matrixDivisionOfBagListsWithCuts
      hrowTime hcolTime
      (S.bagListDivisionAt rowTime hrowTime)
      (S.bagListDivisionAt colTime hcolTime)
      (S.bagListAt_length_eq_stepCount_sub_add_one hrowTime)
      (S.bagListAt_length_eq_stepCount_sub_add_one hcolTime) herr

/-- The interleaved matrix division sequence associated with a graph
contraction sequence: at even times both axes use the same graph state; at odd
times the row axis has performed the next contraction and the column axis is
its mirror awaiting the matching column fusion. -/
noncomputable def matrixSequenceDivision
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (s : ℕ) :
    Matrix.MatrixDivision (Fintype.card V) (Fintype.card V) :=
  if hs : s ≤ 2 * S.stepCount then
    S.matrixDivisionAtTimes ((s + 1) / 2) (s / 2)
      (by
        rw [Nat.div_le_iff_le_mul (by decide : 0 < 2)]
        omega)
      (Nat.div_le_of_le_mul (by omega : s ≤ 2 * S.stepCount))
  else
    S.matrixDivisionAtTimes S.stepCount S.stepCount le_rfl le_rfl

theorem matrixSequenceDivision_even
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    S.matrixSequenceDivision (2 * i) =
      S.matrixDivisionAtTimes i i hi hi := by
  classical
  unfold matrixSequenceDivision
  have hs : 2 * i ≤ 2 * S.stepCount := by omega
  have hrow : (2 * i + 1) / 2 = i := by
    simpa using Nat.mul_add_div (m := 2) (by decide : 0 < 2) i 1
  have hcol : (2 * i) / 2 = i := Nat.mul_div_right _ (by decide : 0 < 2)
  simp [hs, hrow, hcol]

theorem matrixSequenceDivision_odd
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    S.matrixSequenceDivision (2 * i + 1) =
      S.matrixDivisionAtTimes (i + 1) i (by omega) (by omega) := by
  classical
  unfold matrixSequenceDivision
  have hs : 2 * i + 1 ≤ 2 * S.stepCount := by omega
  have hrow : (2 * i + 1 + 1) / 2 = i + 1 := by
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega]
    exact Nat.mul_div_right _ (by decide : 0 < 2)
  have hcol : (2 * i + 1) / 2 = i := by
    simpa using Nat.mul_add_div (m := 2) (by decide : 0 < 2) i 1
  simp [hs, hrow, hcol]

/-- The even matrix step corresponding to graph step `i` fuses the two row
intervals for the contracted bags. -/
theorem hasRowFusion_matrixDivisionAtTimes_step
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    Matrix.MatrixDivision.HasRowFusion
      (S.matrixDivisionAtTimes i i (by omega) (by omega))
      (S.matrixDivisionAtTimes (i + 1) i (by omega) (by omega)) := by
  classical
  let A : Finset V := (S.stepPairAt i).1
  let B : Finset V := (S.stepPairAt i).2
  rcases S.exists_bagListAt_succ_eq_append_merge hi with ⟨P, Q, hnext, hcur⟩
  let Rcur : S.BagListDivision (P ++ [A, B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt i (by omega : i ≤ S.stepCount)) (by simpa [A, B] using hcur)
  let Rnext : S.BagListDivision (P ++ [A ∪ B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt (i + 1) (by omega : i + 1 ≤ S.stepCount))
        (by simpa [A, B] using hnext)
  let C : S.BagListDivision (P ++ [A, B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt i (by omega : i ≤ S.stepCount)) (by simpa [A, B] using hcur)
  have hC : (P ++ [A, B] ++ Q).length = (P.length + Q.length + 1) + 1 := by
    simp
    omega
  have hcurCuts : S.stepCount - i = P.length + Q.length + 1 := by
    have hlen := S.bagListAt_length_eq_stepCount_sub_add_one
      (i := i) (by omega : i ≤ S.stepCount)
    have hcurLen : (S.bagListAt i).length = P.length + Q.length + 2 := by
      rw [hcur]
      simp
      omega
    omega
  have hnextCuts : S.stepCount - (i + 1) = P.length + Q.length := by
    have hlen := S.bagListAt_length_eq_stepCount_sub_add_one
      (i := i + 1) (by omega : i + 1 ≤ S.stepCount)
    have hnextLen : (S.bagListAt (i + 1)).length = P.length + Q.length + 1 := by
      rw [hnext]
      simp
      omega
    omega
  refine ⟨?_, ?_, ⟨P.length, ?_⟩, ?_, ?_⟩
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hcurCuts, hnextCuts]
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hcurCuts]
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hnextCuts]
    omega
  · convert (BagListDivision.isFusionAt_of_adjacent_merge (S := S) Rcur Rnext) using 1
    · simp only [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, Rcur,
        BagListDivision.castList, Division.castIndex_castIndex]
      exact S.bagListDivisionAt_castIndex_div_heq
        (by omega : i ≤ S.stepCount) (by omega : i ≤ S.stepCount) _ _
    · simp only [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, Rnext,
        BagListDivision.castList, Division.castIndex_castIndex]
      exact S.bagListDivisionAt_castIndex_div_heq
        (by omega : i + 1 ≤ S.stepCount) (by omega : i + 1 ≤ S.stepCount) _ _
    · apply fin_heq_of_val_eq
      · omega
      · rfl
  · intro j
    simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hcurCuts,
      Division.castIndex_castIndex]

/-- The odd matrix step corresponding to graph step `i` mirrors the same
contraction as a column fusion. -/
theorem hasColFusion_matrixDivisionAtTimes_step
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    Matrix.MatrixDivision.HasColFusion
      (S.matrixDivisionAtTimes (i + 1) i (by omega) (by omega))
      (S.matrixDivisionAtTimes (i + 1) (i + 1) (by omega) (by omega)) := by
  classical
  let A : Finset V := (S.stepPairAt i).1
  let B : Finset V := (S.stepPairAt i).2
  rcases S.exists_bagListAt_succ_eq_append_merge hi with ⟨P, Q, hnext, hcur⟩
  let R : S.BagListDivision (P ++ [A ∪ B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt (i + 1) (by omega : i + 1 ≤ S.stepCount))
        (by simpa [A, B] using hnext)
  let Ccur : S.BagListDivision (P ++ [A, B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt i (by omega : i ≤ S.stepCount)) (by simpa [A, B] using hcur)
  let Cnext : S.BagListDivision (P ++ [A ∪ B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt (i + 1) (by omega : i + 1 ≤ S.stepCount))
        (by simpa [A, B] using hnext)
  have hR : (P ++ [A ∪ B] ++ Q).length = (P.length + Q.length) + 1 := by
    simp
    omega
  have hcurCuts : S.stepCount - i = P.length + Q.length + 1 := by
    have hlen := S.bagListAt_length_eq_stepCount_sub_add_one
      (i := i) (by omega : i ≤ S.stepCount)
    have hcurLen : (S.bagListAt i).length = P.length + Q.length + 2 := by
      rw [hcur]
      simp
      omega
    omega
  have hnextCuts : S.stepCount - (i + 1) = P.length + Q.length := by
    have hlen := S.bagListAt_length_eq_stepCount_sub_add_one
      (i := i + 1) (by omega : i + 1 ≤ S.stepCount)
    have hnextLen : (S.bagListAt (i + 1)).length = P.length + Q.length + 1 := by
      rw [hnext]
      simp
      omega
    omega
  refine ⟨?_, ?_, ⟨P.length, ?_⟩, ?_, ?_⟩
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hnextCuts]
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hcurCuts, hnextCuts]
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hnextCuts]
    omega
  · intro j
    simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hnextCuts,
      Division.castIndex_castIndex]
  · convert (BagListDivision.isFusionAt_of_adjacent_merge (S := S) Ccur Cnext) using 1
    · simp only [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, Ccur,
        BagListDivision.castList, Division.castIndex_castIndex]
      exact S.bagListDivisionAt_castIndex_div_heq
        (by omega : i ≤ S.stepCount) (by omega : i ≤ S.stepCount) _ _
    · simp only [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, Cnext,
        BagListDivision.castList, Division.castIndex_castIndex]
      exact S.bagListDivisionAt_castIndex_div_heq
        (by omega : i + 1 ≤ S.stepCount) (by omega : i + 1 ≤ S.stepCount) _ _
    · apply fin_heq_of_val_eq
      · omega
      · rfl

/-- The interleaved sequence starts from the finest division: the leaf bag list
is the singleton division in the leaf order. -/
theorem matrixDivisionAtTimes_zero_isFinest
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    Matrix.MatrixDivision.IsFinest
      (S.matrixDivisionAtTimes 0 0 (by omega) (by omega)) := by
  classical
  constructor
  · intro i
    let r : Fin (Fintype.card V) :=
      Fin.cast (by
        simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts]
        exact S.stepCount_add_one_eq_card) i
    refine ⟨r, ?_⟩
    ext x
    simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts,
      bagListDivisionAt, leafBagListDivision, bagListAt, leafBagList,
      Division.castIndex, Division.singleton, r]
  · intro j
    let c : Fin (Fintype.card V) :=
      Fin.cast (by
        simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts]
        exact S.stepCount_add_one_eq_card) j
    refine ⟨c, ?_⟩
    ext x
    simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts,
      bagListDivisionAt, leafBagListDivision, bagListAt, leafBagList,
      Division.castIndex, Division.singleton, c]

/-- The interleaved sequence ends at the coarsest one-by-one division. -/
theorem matrixDivisionAtTimes_final_isCoarsest
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    Matrix.MatrixDivision.IsCoarsest
      (S.matrixDivisionAtTimes S.stepCount S.stepCount le_rfl le_rfl) := by
  constructor <;> simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts]

/-- Every adjacent pair in the interleaved sequence is one exact row or column
fusion.  Even steps contract rows; odd steps mirror the same graph contraction
as a column fusion. -/
theorem matrixSequenceDivision_step_fuses
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {s : ℕ} (hs : s < 2 * S.stepCount) :
    Matrix.MatrixDivision.HasExactFusion
      (S.matrixSequenceDivision s) (S.matrixSequenceDivision (s + 1)) := by
  classical
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · let i := s / 2
    have hs_eq : s = 2 * i := by
      have h := Nat.div_add_mod s 2
      omega
    have hi : i < S.stepCount := by omega
    rw [hs_eq]
    rw [S.matrixSequenceDivision_even (i := i) (by omega : i ≤ S.stepCount)]
    rw [S.matrixSequenceDivision_odd (i := i) hi]
    exact Or.inl (S.hasRowFusion_matrixDivisionAtTimes_step hi)
  · let i := s / 2
    have hs_eq : s = 2 * i + 1 := by
      have h := Nat.div_add_mod s 2
      omega
    have hi : i < S.stepCount := by omega
    have hi_next : i + 1 ≤ S.stepCount := by omega
    rw [hs_eq]
    rw [S.matrixSequenceDivision_odd (i := i) hi]
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega]
    rw [S.matrixSequenceDivision_even (i := i + 1) hi_next]
    exact Or.inr (S.hasColFusion_matrixDivisionAtTimes_step hi)

/-- Every division in the interleaved sequence has nonconstant error at most
`d + 3`.  At even times this is the symmetric trigraph-state partition; at odd
times it is the one-sided partition before the mirrored column fusion. -/
theorem matrixSequenceDivision_errorValueAtMost
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {s : ℕ} (hs : s ≤ 2 * S.stepCount) :
    Matrix.MatrixDivision.NonconstantErrorValueAtMost
      (Matrix.orderedAdjacency G S.leafOrder)
      (S.matrixSequenceDivision s) (d + 3) := by
  classical
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · let i := s / 2
    have hs_eq : s = 2 * i := by
      have h := Nat.div_add_mod s 2
      omega
    have hi : i ≤ S.stepCount := by omega
    rw [hs_eq]
    rw [S.matrixSequenceDivision_even (i := i) hi]
    have herr_state :
        Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
          (S.matrixPartitionOfState S.leafOrder i) (d + 1) :=
      S.matrixPartitionOfState_errorValueAtMost S.leafOrder hi
    have herr_two :
        Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
          (S.matrixPartitionOfTwoStates S.leafOrder i i) (d + 1) := by
      rw [S.matrixPartitionOfTwoStates_self_eq S.leafOrder i]
      exact herr_state
    have herr_wide :
        Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
          (S.matrixPartitionOfTwoStates S.leafOrder i i) (d + 3) :=
      Matrix.MatrixPartition.errorValueAtMost_mono (by omega : d + 1 ≤ d + 3) herr_two
    exact S.matrixDivisionAtTimes_nonconstantErrorValueAtMost hi hi herr_wide
  · let i := s / 2
    have hs_eq : s = 2 * i + 1 := by
      have h := Nat.div_add_mod s 2
      omega
    have hi : i < S.stepCount := by omega
    rw [hs_eq]
    rw [S.matrixSequenceDivision_odd (i := i) hi]
    have herr :
        Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
          (S.matrixPartitionOfTwoStates S.leafOrder (i + 1) i) (d + 3) :=
      S.matrixPartitionOfAdjacentStates_errorValueAtMost S.leafOrder hi
    exact S.matrixDivisionAtTimes_nonconstantErrorValueAtMost
      (by omega : i + 1 ≤ S.stepCount) (by omega : i ≤ S.stepCount) herr

/-- The division sequence extracted from a graph contraction sequence by using
the left-to-right leaf order and mirroring every graph contraction as a row
fusion followed by the matching column fusion. -/
noncomputable def matrixSequenceOfContractionSequence
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    Matrix.BoundedErrorValueDivisionSequence
      (Matrix.orderedAdjacency G S.leafOrder) (d + 3) where
  stepCount := 2 * S.stepCount
  division := S.matrixSequenceDivision
  starts := by
    rw [S.matrixSequenceDivision_even (i := 0) (by omega : 0 ≤ S.stepCount)]
    exact S.matrixDivisionAtTimes_zero_isFinest
  ends := by
    rw [S.matrixSequenceDivision_even (i := S.stepCount) le_rfl]
    exact S.matrixDivisionAtTimes_final_isCoarsest
  step_fuses := by
    intro s hs
    exact S.matrixSequenceDivision_step_fuses hs
  errorValue_le := by
    intro s hs
    exact S.matrixSequenceDivision_errorValueAtMost hs

end ContractionSequence

/-- A graph twin-decomposition at width `d`, represented only by the data
needed for the mixed-minor direction: the left-to-right leaf order of the
contraction tree and the proof that the ordered adjacency matrix is
`d`-twin-ordered.

The empty graph is a harmless zerology case: the division-sequence definition
of `MatrixTwinOrderedAtMost` has at least one row and column part, so a
`0 × 0` matrix is handled by the explicit `isEmpty` alternative. -/
structure TwinDecomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) where
  /-- The left-to-right order on leaves of the contraction tree. -/
  order : VertexOrder V (Fintype.card V)
  /-- Either the graph has no vertices, or in the leaf order the ordered
  adjacency matrix is `(d+3)`-twin-ordered.  The additive constant records the
  formal diagonal/self-zone convention and the two one-sided child zones that
  appear while a graph contraction is mirrored as one row fusion followed by
  one column fusion. -/
  empty_or_orderedAdjacency_twinOrdered :
    Fintype.card V = 0 ∨
      Matrix.MatrixTwinOrderedAtMost (Matrix.orderedAdjacency G order) (d + 3)

/-- The empty graph has the degenerate twin-decomposition certificate. -/
noncomputable def twinDecompositionOfCardEqZero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {d : ℕ} (hV : Fintype.card V = 0) :
    TwinDecomposition G d where
  order := ⟨(Fintype.equivFin V).symm⟩
  empty_or_orderedAdjacency_twinOrdered := Or.inl hV

/-- A contraction sequence gives a twin-decomposition: the vertex order is the
left-to-right order on the leaves of the contraction tree, and every graph
contraction is mirrored by a row fusion followed by a column fusion. -/
noncomputable def twinDecompositionOfContractionSequence
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    TwinDecomposition G d := by
  classical
  by_cases hV : Fintype.card V = 0
  · exact twinDecompositionOfCardEqZero G hV
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    exact
      { order := S.leafOrder
        empty_or_orderedAdjacency_twinOrdered :=
          Or.inr ⟨S.matrixSequenceOfContractionSequence⟩ }

/-- Every finite graph has the leaf-order twin-decomposition at its twin-width. -/
noncomputable def twinDecomposition_twinWidth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    TwinDecomposition G (twinWidth G) := by
  let S : ContractionSequence G (twinWidth G) :=
    Classical.choice (hasTwinWidthAtMost_twinWidth' G)
  exact twinDecompositionOfContractionSequence S

/-- The leaf order of a width-`d` twin-decomposition gives the first item of
Theorem 10 for graphs. -/
theorem mixedMinorNumber_le_of_twinDecomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (D : TwinDecomposition G d) :
    mixedMinorNumber G ≤ 2 * (d + 3) + 2 := by
  rcases D.empty_or_orderedAdjacency_twinOrdered with hcard | htwin
  · have hmix : mixedMinorNumber G = 0 := by
      exact Nat.eq_zero_of_le_zero (by simpa [hcard] using mixedMinorNumber_le_card G)
    rw [hmix]
    omega
  · have hmatrix :
        Matrix.orderedAdjacencyMixedNumber G D.order ≤ 2 * (d + 3) + 2 := by
      simpa [Matrix.orderedAdjacencyMixedNumber] using
        Matrix.theorem10_ordered_matrix_mixed_number_le_of_twin_ordered_at_most
          (Matrix.orderedAdjacency G D.order) htwin
    exact le_trans (mixedMinorNumber_le_orderedAdjacencyMixedNumber G D.order) hmatrix

/-- If every graph admits the leaf-order twin-decomposition at its own
`twinWidth`, then mixed minor number is linearly bounded by twin-width. -/
theorem mixed_minor_number_le_twice_twin_width_plus_eight_of_twinDecomposition
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G)) :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      mixedMinorNumber G ≤ 2 * (twinWidth G + 3) + 2 := by
  intro V _ _ G
  exact mixedMinorNumber_le_of_twinDecomposition (hdecomp G)

/-- The completed twin-width-to-mixed-minor bound from the leaf order of a
contraction sequence. -/
theorem mixed_minor_number_le_twice_twin_width_plus_eight
    {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    mixedMinorNumber G ≤ 2 * (twinWidth G + 3) + 2 :=
  mixedMinorNumber_le_of_twinDecomposition (twinDecomposition_twinWidth G)

end SimpleGraph
end Lax4Proofs.TwinWidth
