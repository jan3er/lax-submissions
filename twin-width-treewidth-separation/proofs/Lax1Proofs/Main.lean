import Lax1Proofs.Source.TwinWidth.Graph.BonnetDepresLower
import Lax1.ExponentialSeparation

/-!
# Bridge to the submitted concepts

The source development and the submitted concepts present the same
mathematics with structures of identical fields.  The conversions below are
therefore field-by-field; the lemmas transport the treewidth upper bound and
the twin-width lower bound to the submitted parameters.
-/

namespace Lax1Proofs.Main

noncomputable section

/-! ## Treewidth -/

/-- A source tree decomposition is verbatim a submitted one. -/
def submittedTreeDecompositionOfSource
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TwinWidth.SimpleGraph.TreeDecomposition G) :
    Lax1.Treewidth.TreeDecomposition G where
  Node := D.Node
  nodeFintype := D.nodeFintype
  nodeDecidableEq := D.nodeDecidableEq
  tree := D.tree
  isTree := D.isTree
  bag := D.bag
  vertex_mem_bag := D.vertex_mem_bag
  edge_mem_bag := D.edge_mem_bag
  bag_indices_connected := D.bag_indices_connected

theorem submittedTreeDecompositionWidth_eq_source
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TwinWidth.SimpleGraph.TreeDecomposition G) :
    (submittedTreeDecompositionOfSource D).width = D.width := by
  rfl

theorem treewidth_le_of_treeDecomposition
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {width : ℕ}
    (D : Lax1.Treewidth.TreeDecomposition G)
    (hwidth : D.width ≤ width) :
    Lax1.Treewidth.treewidth G ≤ width := by
  classical
  let P : ℕ → Prop := fun e =>
    ∃ D : Lax1.Treewidth.TreeDecomposition G, D.width ≤ e
  have hex : ∃ e, P e := ⟨width, D, hwidth⟩
  change Lax1.Treewidth.leastNat P ≤ width
  rw [Lax1.Treewidth.leastNat, dif_pos hex]
  exact Nat.find_min' hex ⟨D, hwidth⟩

theorem treewidth_le_of_source
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {width : ℕ}
    (D : TwinWidth.SimpleGraph.TreeDecomposition G)
    (hwidth : D.width ≤ width) :
    Lax1.Treewidth.treewidth G ≤ width :=
  treewidth_le_of_treeDecomposition
    (submittedTreeDecompositionOfSource D)
    (by simpa [submittedTreeDecompositionWidth_eq_source D] using hwidth)

/-! ## Twin-width -/

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

theorem submitted_hasTwinWidthAtMost_mono
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d e : ℕ}
    (h : Lax1.TwinWidth.HasTwinWidthAtMost G d) (hde : d ≤ e) :
    Lax1.TwinWidth.HasTwinWidthAtMost G e := by
  obtain ⟨S⟩ := h
  exact ⟨{ S with
    redDegree_le := fun i hi A hA => le_trans (S.redDegree_le i hi hA) hde }⟩

theorem submitted_hasTwinWidthAtMost_twinWidth
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hex : ∃ d, Lax1.TwinWidth.HasTwinWidthAtMost G d) :
    Lax1.TwinWidth.HasTwinWidthAtMost G (Lax1.TwinWidth.twinWidth G) := by
  classical
  rw [Lax1.TwinWidth.twinWidth, Lax1.TwinWidth.leastNat, dif_pos hex]
  exact Nat.find_spec hex

theorem lt_twinWidth_of_not_hasTwinWidthAtMost
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (hnot : ¬ Lax1.TwinWidth.HasTwinWidthAtMost G d)
    (hex : ∃ e, Lax1.TwinWidth.HasTwinWidthAtMost G e) :
    d < Lax1.TwinWidth.twinWidth G := by
  by_contra hle
  exact hnot
    (submitted_hasTwinWidthAtMost_mono
      (submitted_hasTwinWidthAtMost_twinWidth G hex) (Nat.le_of_not_gt hle))

/-! ## The separation theorem -/

/--
---
conclusion: Lax1.ExponentialSeparation.twin_width_can_be_exponential_in_treewidth
---
Self-contained proof of the Bonnet–Déprés exponential gap: for every `k`, the
Bonnet–Déprés graph `BD_k` has treewidth at most `2*k + 4` while its
twin-width exceeds `2^k`. The submitted structures share their fields with
the source development, so the proof transports the source tree decomposition
directly and translates submitted bounded contraction sequences back into the
source structure, where the lower bound is proved.
-/
theorem twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      Lax1.Treewidth.treewidth G ≤ 2 * k + 4 ∧
        2 ^ k < Lax1.TwinWidth.twinWidth G := by
  refine
    ⟨TwinWidth.SimpleGraph.BonnetDepresVertex k, inferInstance, inferInstance,
      TwinWidth.SimpleGraph.bonnetDepresGraph k, ?_, ?_⟩
  · simpa [
      TwinWidth.SimpleGraph.bonnetDepresApexCount
    ] using treewidth_le_of_source
      (TwinWidth.SimpleGraph.bonnetDepresTreeDecomposition k)
      (TwinWidth.SimpleGraph.bonnetDepresTreeDecomposition_width_le k)
  · have hsource :
        ¬ TwinWidth.SimpleGraph.HasTwinWidthAtMost
          (TwinWidth.SimpleGraph.bonnetDepresGraph k) (2 ^ k) :=
      TwinWidth.SimpleGraph.BonnetDepres.bonnetDepres_not_hasTwinWidthAtMost_two_pow k
    have hsubmitted :
        ¬ Lax1.TwinWidth.HasTwinWidthAtMost
          (TwinWidth.SimpleGraph.bonnetDepresGraph k) (2 ^ k) := by
      intro h
      exact hsource (source_hasTwinWidthAtMost_of_submitted h)
    have hex :
        ∃ e, Lax1.TwinWidth.HasTwinWidthAtMost
          (TwinWidth.SimpleGraph.bonnetDepresGraph k) e := by
      refine ⟨Fintype.card (TwinWidth.SimpleGraph.BonnetDepresVertex k), ?_⟩
      exact ⟨submittedContractionSequenceOfSource
        (Classical.choice
          (TwinWidth.SimpleGraph.hasTwinWidthAtMost_card
            (TwinWidth.SimpleGraph.bonnetDepresGraph k)))⟩
    exact lt_twinWidth_of_not_hasTwinWidthAtMost hsubmitted hex

end

end Lax1Proofs.Main
