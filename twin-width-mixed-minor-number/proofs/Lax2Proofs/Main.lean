import Lax2Proofs.Source.TwinWidth.Equivalence.MainContract
import Lax2Proofs.Source.TwinWidth.Graph.MixedMinorNumber
import Lax2Proofs.Source.TwinWidth.Graph.Partition
import Lax1.TwinWidth
import Lax2.MixedMinorNumber
import Lax2.FunctionalEquivalence

/-!
# Bridge to the submitted concepts

The source development and the submitted concepts present the same
mathematics with structures of identical fields.  The conversions below are
therefore field-by-field; the lemmas show that the submitted twin-width
parameter (from submission Lax1) and the submitted mixed minor number agree
with the source parameters, so the source equivalence theorem transports
directly.
-/

namespace Lax2Proofs.Main

noncomputable section

/-! ## Twin-width

The submitted twin-width parameter is `Lax1.TwinWidth.twinWidth` from
submission Lax1.  Its trigraph states and contraction sequences share their
fields with the source structures, so states translate verbatim in both
directions and the two parameters are equal.
-/

/-- A source trigraph state is verbatim a submitted one. -/
def submittedStateOfSource {V : Type}
    (T : TwinWidth.TrigraphState V) :
    Lax1.TwinWidth.TrigraphState V where
  bags := T.bags
  bag_nonempty := T.bag_nonempty
  bag_disjoint := T.bag_disjoint
  bag_cover := T.bag_cover
  blackAdj := T.blackAdj
  redAdj := T.redAdj
  black_symm := T.black_symm
  red_symm := T.red_symm
  black_irrefl := T.black_irrefl
  red_irrefl := T.red_irrefl
  black_red_disjoint := T.black_red_disjoint

/-- A submitted trigraph state is verbatim a source one. -/
def sourceStateOfSubmitted {V : Type}
    (T : Lax1.TwinWidth.TrigraphState V) :
    TwinWidth.TrigraphState V where
  bags := T.bags
  bag_nonempty := T.bag_nonempty
  bag_disjoint := T.bag_disjoint
  bag_cover := T.bag_cover
  blackAdj := T.blackAdj
  redAdj := T.redAdj
  black_symm := T.black_symm
  red_symm := T.red_symm
  black_irrefl := T.black_irrefl
  red_irrefl := T.red_irrefl
  black_red_disjoint := T.black_red_disjoint

theorem singletonBags_eq (V : Type) [Fintype V] [DecidableEq V] :
    Lax1.TwinWidth.TrigraphState.singletonBags V =
      TwinWidth.TrigraphState.singletonBags V := by
  rfl

theorem submitted_isInitialState
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {T : TwinWidth.TrigraphState V}
    (h : TwinWidth.SimpleGraph.IsInitialState G T) :
    Lax1.TwinWidth.IsInitialState G (submittedStateOfSource T) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [submittedStateOfSource, singletonBags_eq] using h.1
  · intro A B hA hB
    simpa [submittedStateOfSource] using h.2.1 hA hB
  · intro A B hA hB
    simpa [submittedStateOfSource] using h.2.2 hA hB

theorem source_isInitialState
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {T : Lax1.TwinWidth.TrigraphState V}
    (h : Lax1.TwinWidth.IsInitialState G T) :
    TwinWidth.SimpleGraph.IsInitialState G (sourceStateOfSubmitted T) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [sourceStateOfSubmitted, singletonBags_eq] using h.1
  · intro A B hA hB
    simpa [sourceStateOfSubmitted] using h.2.1 hA hB
  · intro A B hA hB
    simpa [sourceStateOfSubmitted] using h.2.2 hA hB

theorem submitted_isContractionStep
    {V : Type} [DecidableEq V] {T U : TwinWidth.TrigraphState V}
    (h : TwinWidth.SimpleGraph.IsContractionStep T U) :
    Lax1.TwinWidth.IsContractionStep
      (submittedStateOfSource T) (submittedStateOfSource U) := by
  obtain ⟨A, hA, B, hB, hAB, hbags, hred, hblack⟩ := h
  refine ⟨A, ?_, B, ?_, hAB, ?_, ?_, ?_⟩
  · simpa [submittedStateOfSource] using hA
  · simpa [submittedStateOfSource] using hB
  · simpa [submittedStateOfSource] using hbags
  · intro X Y hX hY
    simpa [submittedStateOfSource, Lax1.TwinWidth.contractedRed,
      TwinWidth.SimpleGraph.contractedRed] using hred hX hY
  · intro X Y hX hY
    simpa [submittedStateOfSource, Lax1.TwinWidth.contractedRed,
      Lax1.TwinWidth.contractedBlack, TwinWidth.SimpleGraph.contractedRed,
      TwinWidth.SimpleGraph.contractedBlack] using hblack hX hY

theorem source_isContractionStep
    {V : Type} [DecidableEq V] {T U : Lax1.TwinWidth.TrigraphState V}
    (h : Lax1.TwinWidth.IsContractionStep T U) :
    TwinWidth.SimpleGraph.IsContractionStep
      (sourceStateOfSubmitted T) (sourceStateOfSubmitted U) := by
  obtain ⟨A, hA, B, hB, hAB, hbags, hred, hblack⟩ := h
  refine ⟨A, ?_, B, ?_, hAB, ?_, ?_, ?_⟩
  · simpa [sourceStateOfSubmitted] using hA
  · simpa [sourceStateOfSubmitted] using hB
  · simpa [sourceStateOfSubmitted] using hbags
  · intro X Y hX hY
    simpa [sourceStateOfSubmitted, Lax1.TwinWidth.contractedRed,
      TwinWidth.SimpleGraph.contractedRed] using hred hX hY
  · intro X Y hX hY
    simpa [sourceStateOfSubmitted, Lax1.TwinWidth.contractedRed,
      Lax1.TwinWidth.contractedBlack, TwinWidth.SimpleGraph.contractedRed,
      TwinWidth.SimpleGraph.contractedBlack] using hblack hX hY

theorem submitted_redDegree {V : Type} [DecidableEq V]
    (T : TwinWidth.TrigraphState V) (A : Finset V) :
    (submittedStateOfSource T).redDegree A = T.redDegree A := by
  unfold Lax1.TwinWidth.TrigraphState.redDegree
    TwinWidth.TrigraphState.redDegree
  simp only [submittedStateOfSource]
  congr!

theorem source_redDegree {V : Type} [DecidableEq V]
    (T : Lax1.TwinWidth.TrigraphState V) (A : Finset V) :
    (sourceStateOfSubmitted T).redDegree A = T.redDegree A := by
  unfold Lax1.TwinWidth.TrigraphState.redDegree
    TwinWidth.TrigraphState.redDegree
  simp only [sourceStateOfSubmitted]
  congr!

/-- Transport a source contraction sequence to the submitted structure. -/
def submittedContractionSequenceOfSource
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (S : TwinWidth.SimpleGraph.ContractionSequence G d) :
    Lax1.TwinWidth.ContractionSequence G d where
  stepCount := S.stepCount
  state i := submittedStateOfSource (S.state i)
  starts := submitted_isInitialState S.starts
  ends := by
    simpa [Lax1.TwinWidth.IsFinalState, submittedStateOfSource,
      TwinWidth.SimpleGraph.IsFinalState] using S.ends
  step_contracts i hi := submitted_isContractionStep (S.step_contracts i hi)
  redDegree_le i hi A hA := by
    rw [submitted_redDegree]
    have hA' : A ∈ (S.state i).bags := by
      simpa [submittedStateOfSource] using hA
    simpa [TwinWidth.SimpleGraph.redDegree] using S.redDegree_le i hi hA'

theorem source_hasTwinWidthAtMost_of_submitted
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (h : Lax1.TwinWidth.HasTwinWidthAtMost G d) :
    TwinWidth.SimpleGraph.HasTwinWidthAtMost G d := by
  obtain ⟨S⟩ := h
  refine ⟨{
    stepCount := S.stepCount
    state := fun i => sourceStateOfSubmitted (S.state i)
    starts := source_isInitialState S.starts
    ends := by
      simpa [Lax1.TwinWidth.IsFinalState, sourceStateOfSubmitted,
        TwinWidth.SimpleGraph.IsFinalState] using S.ends
    step_contracts := fun i hi =>
      source_isContractionStep (S.step_contracts i hi)
    redDegree_le := ?_ }⟩
  intro i hi A hA
  have hA' : A ∈ (S.state i).bags := by
    simpa [sourceStateOfSubmitted] using hA
  have := S.redDegree_le i hi hA'
  simpa [TwinWidth.SimpleGraph.redDegree, source_redDegree] using this

/-- The submitted and source `HasTwinWidthAtMost` predicates agree. -/
theorem submitted_hasTwinWidthAtMost_iff
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ} :
    Lax1.TwinWidth.HasTwinWidthAtMost G d ↔
      TwinWidth.SimpleGraph.HasTwinWidthAtMost G d :=
  ⟨source_hasTwinWidthAtMost_of_submitted,
    fun h => ⟨submittedContractionSequenceOfSource (Classical.choice h)⟩⟩

theorem submitted_twinWidth_le
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (h : Lax1.TwinWidth.HasTwinWidthAtMost G d) :
    Lax1.TwinWidth.twinWidth G ≤ d := by
  classical
  have hex : ∃ e, Lax1.TwinWidth.HasTwinWidthAtMost G e := ⟨d, h⟩
  rw [Lax1.TwinWidth.twinWidth, Lax1.TwinWidth.leastNat, dif_pos hex]
  exact Nat.find_min' hex h

theorem submitted_hasTwinWidthAtMost_twinWidth
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hex : ∃ d, Lax1.TwinWidth.HasTwinWidthAtMost G d) :
    Lax1.TwinWidth.HasTwinWidthAtMost G (Lax1.TwinWidth.twinWidth G) := by
  classical
  rw [Lax1.TwinWidth.twinWidth, Lax1.TwinWidth.leastNat, dif_pos hex]
  exact Nat.find_spec hex

/-- The submitted twin-width parameter equals the source parameter. -/
theorem submitted_twinWidth_eq_source
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Lax1.TwinWidth.twinWidth G = TwinWidth.SimpleGraph.twinWidth G := by
  apply le_antisymm
  · exact submitted_twinWidth_le
      (submitted_hasTwinWidthAtMost_iff.mpr
        (TwinWidth.SimpleGraph.hasTwinWidthAtMost_twinWidth' G))
  · exact TwinWidth.SimpleGraph.twinWidth_le_of_hasTwinWidthAtMost
      (submitted_hasTwinWidthAtMost_iff.mp
        (submitted_hasTwinWidthAtMost_twinWidth G
          ⟨Fintype.card V, submitted_hasTwinWidthAtMost_iff.mpr
            (TwinWidth.SimpleGraph.hasTwinWidthAtMost_card G)⟩))

/-! ## Mixed minor number

The submitted divisions, cells, mixed minors, and ordered adjacency matrices
share their fields and shapes with the source development, so the two graph
parameters are equal.
-/

/-- A source division is verbatim a submitted one. -/
def submittedDivisionOfSource {n k : ℕ} (D : TwinWidth.Division n k) :
    Lax2.MixedMinorNumber.Division n k where
  part := D.part
  part_nonempty := D.part_nonempty
  part_disjoint := D.part_disjoint
  part_cover := D.part_cover
  part_convex := D.part_convex
  part_ordered := D.part_ordered

/-- A submitted division is verbatim a source one. -/
def sourceDivisionOfSubmitted {n k : ℕ}
    (D : Lax2.MixedMinorNumber.Division n k) :
    TwinWidth.Division n k where
  part := D.part
  part_nonempty := D.part_nonempty
  part_disjoint := D.part_disjoint
  part_cover := D.part_cover
  part_convex := D.part_convex
  part_ordered := D.part_ordered

/-- The submitted and source mixed-minor predicates agree. -/
theorem submitted_hasMixedMinor_iff {n m k : ℕ} (M : Fin n → Fin m → Bool) :
    Lax2.MixedMinorNumber.HasMixedMinor M k ↔
      TwinWidth.Matrix.HasMixedMinor M k := by
  constructor
  · rintro (h0 | ⟨R, C, h⟩)
    · exact Or.inl h0
    · exact Or.inr
        ⟨sourceDivisionOfSubmitted R, sourceDivisionOfSubmitted C,
          fun i j => h i j⟩
  · rintro (h0 | ⟨R, C, h⟩)
    · exact Or.inl h0
    · exact Or.inr
        ⟨submittedDivisionOfSource R, submittedDivisionOfSource C,
          fun i j => h i j⟩

theorem findGreatest_congr {P Q : ℕ → Prop}
    [DecidablePred P] [DecidablePred Q] (h : ∀ k, P k ↔ Q k) :
    ∀ n, Nat.findGreatest P n = Nat.findGreatest Q n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.findGreatest_succ, Nat.findGreatest_succ, ih]
      by_cases hP : P (n + 1)
      · rw [if_pos hP, if_pos ((h _).mp hP)]
      · rw [if_neg hP, if_neg fun hq => hP ((h _).mpr hq)]

/-- The submitted and source matrix mixed numbers agree. -/
theorem submitted_matrixMixedNumber_eq {n m : ℕ} (M : Fin n → Fin m → Bool) :
    Lax2.MixedMinorNumber.matrixMixedNumber M =
      TwinWidth.Matrix.matrixMixedNumber M := by
  classical
  unfold Lax2.MixedMinorNumber.matrixMixedNumber TwinWidth.Matrix.matrixMixedNumber
  exact findGreatest_congr (fun k => submitted_hasMixedMinor_iff (k := k) M) (min n m)

/-- The submitted and source ordered adjacency matrices agree. -/
theorem submitted_orderedAdjacency_eq {V : Type} {n : ℕ}
    (G : SimpleGraph V) (e : Fin n ≃ V) :
    Lax2.MixedMinorNumber.orderedAdjacency G e =
      TwinWidth.Matrix.orderedAdjacency G ⟨e⟩ := by
  funext i j
  unfold Lax2.MixedMinorNumber.orderedAdjacency TwinWidth.Matrix.orderedAdjacency
  exact decide_eq_decide.mpr Iff.rfl

/-- The submitted mixed number of an ordered adjacency matrix is the source
one. -/
theorem submitted_orderedMixedNumber_eq {V : Type} {n : ℕ}
    (G : SimpleGraph V) (e : Fin n ≃ V) :
    Lax2.MixedMinorNumber.matrixMixedNumber
        (Lax2.MixedMinorNumber.orderedAdjacency G e) =
      TwinWidth.Matrix.orderedAdjacencyMixedNumber G ⟨e⟩ := by
  rw [TwinWidth.Matrix.orderedAdjacencyMixedNumber,
    submitted_matrixMixedNumber_eq, submitted_orderedAdjacency_eq]

/-- The submitted mixed minor number parameter equals the source parameter. -/
theorem submitted_mixedMinorNumber_eq
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Lax2.MixedMinorNumber.mixedMinorNumber G =
      TwinWidth.SimpleGraph.mixedMinorNumber G := by
  classical
  have hiff : ∀ k,
      (∃ e : Fin (Fintype.card V) ≃ V,
        Lax2.MixedMinorNumber.matrixMixedNumber
          (Lax2.MixedMinorNumber.orderedAdjacency G e) = k) ↔
      (∃ σ : TwinWidth.VertexOrder V (Fintype.card V),
        TwinWidth.Matrix.orderedAdjacencyMixedNumber G σ = k) := by
    intro k
    constructor
    · rintro ⟨e, he⟩
      exact ⟨⟨e⟩, by rw [← submitted_orderedMixedNumber_eq]; exact he⟩
    · rintro ⟨σ, hσ⟩
      exact ⟨σ.equiv, by rw [submitted_orderedMixedNumber_eq]; exact hσ⟩
  have hexP : ∃ k, ∃ e : Fin (Fintype.card V) ≃ V,
      Lax2.MixedMinorNumber.matrixMixedNumber
        (Lax2.MixedMinorNumber.orderedAdjacency G e) = k := by
    obtain ⟨σ, hσ⟩ :=
      TwinWidth.SimpleGraph.exists_order_mixedNumber_eq_mixedMinorNumber G
    exact ⟨TwinWidth.SimpleGraph.mixedMinorNumber G, (hiff _).mpr ⟨σ, hσ⟩⟩
  rw [Lax2.MixedMinorNumber.mixedMinorNumber, Lax2.MixedMinorNumber.leastNat,
    dif_pos hexP]
  apply le_antisymm
  · apply Nat.find_min' hexP
    obtain ⟨σ, hσ⟩ :=
      TwinWidth.SimpleGraph.exists_order_mixedNumber_eq_mixedMinorNumber G
    exact (hiff _).mpr ⟨σ, hσ⟩
  · obtain ⟨σ, hσ⟩ := (hiff _).mp (Nat.find_spec hexP)
    rw [← hσ]
    exact TwinWidth.SimpleGraph.mixedMinorNumber_le_orderedAdjacencyMixedNumber G σ

/-! ## The equivalence theorem -/

/--
---
conclusion: Lax2.FunctionalEquivalence.twin_width_functionally_equivalent_mixed_minor_number
---
Self-contained proof that the submitted twin-width parameter (from submission
Lax1) and the submitted mixed minor number are functionally equivalent.  The
submitted structures share their fields with the source development, so both
graph parameters are pointwise equal to their source counterparts and the
source equivalence theorem — Marcus–Tardos, the matrix grid-minor theorem,
and the twin-decomposition bridge — transports directly.
-/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    Lax2.FunctionalEquivalence.FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V] =>
        Lax1.TwinWidth.twinWidth)
      (fun {V : Type} [Fintype V] [DecidableEq V] =>
        Lax2.MixedMinorNumber.mixedMinorNumber) := by
  obtain ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ :=
    TwinWidth.MainContract.twin_width_functionally_equivalent_mixed_minor_number
  constructor
  · refine ⟨f, ?_⟩
    intro V _ _ G
    show Lax1.TwinWidth.twinWidth G ≤
      f (Lax2.MixedMinorNumber.mixedMinorNumber G)
    rw [submitted_twinWidth_eq_source, submitted_mixedMinorNumber_eq]
    exact hf G
  · refine ⟨g, ?_⟩
    intro V _ _ G
    show Lax2.MixedMinorNumber.mixedMinorNumber G ≤
      g (Lax1.TwinWidth.twinWidth G)
    rw [submitted_twinWidth_eq_source, submitted_mixedMinorNumber_eq]
    exact hg G

end

end Lax2Proofs.Main
