import Lax2.MixedMinorNumber
import Lax2Proofs.Source.TwinWidth.Graph.MixedMinorNumber

/-!
# Bridge from source mixed-minor definitions

The source proof uses structures with named fields.  The public concepts use
small transparent sigma types.  The conversions below preserve division parts
literally, so cells, mixed minors, mixed numbers, ordered adjacency matrices,
and finally the graph mixed minor number agree.
-/

namespace Lax2Proofs.MixedBridge

noncomputable section

def submittedDivisionOfSource {n k : ℕ}
    (D : Lax2Proofs.TwinWidth.Division n k) : Lax2.IntervalDivision.Division n k :=
  ⟨D.part, ⟨D.part_nonempty, D.part_disjoint, D.part_cover,
    D.part_convex, D.part_ordered⟩⟩

def sourceDivisionOfSubmitted {n k : ℕ}
    (D : Lax2.IntervalDivision.Division n k) : Lax2Proofs.TwinWidth.Division n k where
  part := Lax2.IntervalDivision.part D
  part_nonempty := D.2.down.1
  part_disjoint := D.2.down.2.1
  part_cover := D.2.down.2.2.1
  part_convex := D.2.down.2.2.2.1
  part_ordered := D.2.down.2.2.2.2

theorem sourceCellMixed_iff_submitted
    {n m k : ℕ} (M : Fin n → Fin m → Bool)
    (R : Lax2Proofs.TwinWidth.Division n k)
    (C : Lax2Proofs.TwinWidth.Division m k) (i j : Fin k) :
    Lax2Proofs.TwinWidth.Matrix.CellMixed M R C i j ↔
      Lax2.MixedCell.cellMixed M
        (submittedDivisionOfSource R) (submittedDivisionOfSource C) i j := by
  rfl

theorem sourceHasMixedMinor_iff_submitted
    {n m : ℕ} (M : Fin n → Fin m → Bool) (k : ℕ) :
    Lax2Proofs.TwinWidth.Matrix.HasMixedMinor M k ↔
      Lax2.MixedMinor.HasMixedMinor M k := by
  constructor
  · rintro (rfl | ⟨R, C, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨submittedDivisionOfSource R, submittedDivisionOfSource C,
        fun i j => (sourceCellMixed_iff_submitted M R C i j).mp (h i j)⟩
  · rintro (rfl | ⟨R, C, h⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨sourceDivisionOfSubmitted R, sourceDivisionOfSubmitted C, ?_⟩
      intro i j
      simpa [sourceDivisionOfSubmitted, submittedDivisionOfSource,
        Lax2.IntervalDivision.part] using h i j

theorem sourceMatrixMixedNumber_eq_submitted
    {n m : ℕ} (M : Fin n → Fin m → Bool) :
    Lax2Proofs.TwinWidth.Matrix.matrixMixedNumber M =
      Lax2.MixedNumber.matrixMixedNumber M := by
  classical
  have hpred :
      Lax2Proofs.TwinWidth.Matrix.HasMixedMinor M =
        Lax2.MixedMinor.HasMixedMinor M := by
    funext k
    exact propext (sourceHasMixedMinor_iff_submitted M k)
  rw [Lax2Proofs.TwinWidth.Matrix.matrixMixedNumber,
    Lax2.MixedNumber.matrixMixedNumber, hpred]

theorem sourceOrderedAdjacency_eq_submitted
    {V : Type} {n : ℕ} (G : SimpleGraph V) (e : Fin n ≃ V) :
    Lax2Proofs.TwinWidth.Matrix.orderedAdjacency G ⟨e⟩ =
      Lax2.OrderedAdjacency.orderedAdjacency G e := by
  rfl

theorem sourceOrderedAdjacencyMixedNumber_eq_submitted
    {V : Type} {n : ℕ} (G : SimpleGraph V) (e : Fin n ≃ V) :
    Lax2Proofs.TwinWidth.Matrix.orderedAdjacencyMixedNumber G ⟨e⟩ =
      Lax2.MixedNumber.matrixMixedNumber
        (Lax2.OrderedAdjacency.orderedAdjacency G e) := by
  rw [Lax2Proofs.TwinWidth.Matrix.orderedAdjacencyMixedNumber,
    sourceMatrixMixedNumber_eq_submitted, sourceOrderedAdjacency_eq_submitted]

theorem sourceMixedMinorNumber_eq_submitted
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Lax2Proofs.TwinWidth.SimpleGraph.mixedMinorNumber G =
      Lax2.MixedMinorNumber.mixedMinorNumber G := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ σ : Lax2Proofs.TwinWidth.VertexOrder V (Fintype.card V),
      Lax2Proofs.TwinWidth.Matrix.orderedAdjacencyMixedNumber G σ = k
  let Q : ℕ → Prop := fun k =>
    ∃ e : Fin (Fintype.card V) ≃ V,
      Lax2.MixedNumber.matrixMixedNumber
        (Lax2.OrderedAdjacency.orderedAdjacency G e) = k
  have hpred : P = Q := by
    funext k
    apply propext
    constructor
    · rintro ⟨⟨e⟩, h⟩
      exact ⟨e, by simpa [sourceOrderedAdjacencyMixedNumber_eq_submitted] using h⟩
    · rintro ⟨e, h⟩
      exact ⟨⟨e⟩, by simpa [sourceOrderedAdjacencyMixedNumber_eq_submitted] using h⟩
  have hP : ∃ k, P k := by
    simpa [P] using
      Lax2Proofs.TwinWidth.SimpleGraph.exists_orderedAdjacencyMixedNumber G
  have hQ : ∃ k, Q k := by simpa [hpred] using hP
  rw [Lax2Proofs.TwinWidth.SimpleGraph.mixedMinorNumber,
    Lax2.MixedMinorNumber.mixedMinorNumber, Lax1.LeastNatural.leastNat]
  change Nat.find hP = if h : ∃ k, Q k then Nat.find h else 0
  rw [dif_pos hQ]
  have hiff (k : ℕ) : P k ↔ Q k := by rw [hpred]
  apply Nat.le_antisymm
  · exact Nat.find_min' hP ((hiff (Nat.find hQ)).mpr (Nat.find_spec hQ))
  · exact Nat.find_min' hQ ((hiff (Nat.find hP)).mp (Nat.find_spec hP))

end

end Lax2Proofs.MixedBridge
