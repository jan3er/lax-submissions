import Lax1Proofs.Source.TwinWidth.Graph.BonnetDepresLower
import Lax1.ExponentialSeparation

namespace Lax1Proofs.Main

open Lax1

noncomputable section

def submittedTreeDecompositionOfSource
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TwinWidth.SimpleGraph.TreeDecomposition G) :
    Treewidth.TreeDecomposition G :=
  ⟨D.Node, D.nodeFintype, D.nodeDecidableEq, D.tree, D.bag,
    ⟨D.isTree, D.vertex_mem_bag, D.edge_mem_bag, D.bag_indices_connected⟩⟩

theorem submittedTreeDecompositionWidth_eq_source
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TwinWidth.SimpleGraph.TreeDecomposition G) :
    Treewidth.treeDecompositionWidth
        (submittedTreeDecompositionOfSource D) = D.width := by
  rfl

theorem treewidth_le_of_treeDecomposition
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {width : ℕ}
    (D : Treewidth.TreeDecomposition G)
    (hwidth : Treewidth.treeDecompositionWidth D ≤ width) :
    Treewidth.treewidth G ≤ width := by
  classical
  let P : ℕ → Prop := fun e =>
    ∃ D : Treewidth.TreeDecomposition G,
      Treewidth.treeDecompositionWidth D ≤ e
  have hex : ∃ e, P e := ⟨width, D, hwidth⟩
  change Treewidth.leastNat P ≤ width
  rw [Treewidth.leastNat, dif_pos hex]
  exact Nat.find_min' hex ⟨D, hwidth⟩

theorem treewidth_le_of_source
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {width : ℕ}
    (D : TwinWidth.SimpleGraph.TreeDecomposition G)
    (hwidth : D.width ≤ width) :
    Treewidth.treewidth G ≤ width := by
  exact treewidth_le_of_treeDecomposition
    (submittedTreeDecompositionOfSource D)
    (by simpa [submittedTreeDecompositionWidth_eq_source D] using hwidth)

def submittedStateOfSource {V : Type} [DecidableEq V]
    (T : TwinWidth.TrigraphState V) :
    TwinWidth.State V :=
  ⟨T.bags, T.blackAdj, T.redAdj,
    ⟨T.bag_nonempty, T.bag_disjoint, T.bag_cover, T.black_symm, T.red_symm,
      T.black_irrefl, T.red_irrefl, T.black_red_disjoint⟩⟩

def sourceStateOfSubmitted {V : Type} [DecidableEq V]
    (T : TwinWidth.State V) :
    TwinWidth.TrigraphState V where
  bags := TwinWidth.bags T
  blackAdj := TwinWidth.blackAdj T
  redAdj := TwinWidth.redAdj T
  bag_nonempty := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.1
  bag_disjoint := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.1
  bag_cover := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.1
  black_symm := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.1
  red_symm := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.2.1
  black_irrefl := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.2.2.1
  red_irrefl := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.2.2.2.1
  black_red_disjoint := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.2.2.2.2

def submittedInitialStateOfSource
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (T : TwinWidth.TrigraphState V)
    (h : TwinWidth.SimpleGraph.IsInitialState G T) :
    TwinWidth.InitialState G :=
  ⟨submittedStateOfSource T, ⟨by
    refine ⟨?_, ?_, ?_⟩
    ·
      simpa [submittedStateOfSource, TwinWidth.singletonBags,
        TwinWidth.TrigraphState.singletonBags] using h.1
    ·
      intro A B hA hB
      simpa [submittedStateOfSource] using h.2.1 hA hB
    ·
      intro A B hA hB
      simpa [submittedStateOfSource] using h.2.2 hA hB⟩⟩

def submittedFinalStateOfSource {V : Type} [DecidableEq V]
    (T : TwinWidth.TrigraphState V)
    (h : TwinWidth.SimpleGraph.IsFinalState T) :
    TwinWidth.FinalState V :=
  ⟨submittedStateOfSource T, ⟨by
    simpa [submittedStateOfSource] using h⟩⟩

def submittedStepOfSource {V : Type} [DecidableEq V]
    {T U : TwinWidth.TrigraphState V}
    (h : TwinWidth.SimpleGraph.IsContractionStep T U) :
    TwinWidth.Step (submittedStateOfSource T) (submittedStateOfSource U) := by
  classical
  let A : Finset V := Classical.choose h
  have hApack := Classical.choose_spec h
  let B : Finset V := Classical.choose hApack.2
  have hBpack := Classical.choose_spec hApack.2
  have hA : A ∈ T.bags := hApack.1
  have hB : B ∈ T.bags := hBpack.1
  have hAB : A ≠ B := hBpack.2.1
  have hbags : U.bags = insert (A ∪ B) ((T.bags.erase A).erase B) := hBpack.2.2.1
  have hred :
      ∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
        (U.redAdj X Y ↔ TwinWidth.SimpleGraph.contractedRed T A B X Y) :=
    hBpack.2.2.2.1
  have hblack :
      ∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
        (U.blackAdj X Y ↔ TwinWidth.SimpleGraph.contractedBlack T A B X Y) :=
    hBpack.2.2.2.2
  refine ⟨A, B, ⟨?_, ?_, hAB, ?_, ?_, ?_⟩⟩
  · simpa [submittedStateOfSource] using hA
  · simpa [submittedStateOfSource] using hB
  · simpa [submittedStateOfSource] using hbags
  · intro X Y hX hY
    simpa [submittedStateOfSource, TwinWidth.contractedRed,
      TwinWidth.SimpleGraph.contractedRed] using hred hX hY
  · intro X Y hX hY
    simpa [submittedStateOfSource, TwinWidth.contractedRed,
      TwinWidth.contractedBlack, TwinWidth.SimpleGraph.contractedRed,
      TwinWidth.SimpleGraph.contractedBlack] using hblack hX hY

def submittedContractionSequenceOfSource
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (S : TwinWidth.SimpleGraph.ContractionSequence G d) :
    TwinWidth.ContractionSequence G d :=
  ⟨S.stepCount, fun i => submittedStateOfSource (S.state i),
    submittedInitialStateOfSource (S.state 0) S.starts,
    submittedFinalStateOfSource (S.state S.stepCount) S.ends,
    ⟨rfl⟩, ⟨rfl⟩,
    (fun i hi => submittedStepOfSource (S.step_contracts i hi)),
    ⟨by
      intro i hi A hA
      simpa [submittedStateOfSource, TwinWidth.redDegree,
        TwinWidth.SimpleGraph.redDegree, TwinWidth.TrigraphState.redDegree]
        using S.redDegree_le i hi hA⟩⟩

theorem source_contractionSequence_of_submitted
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (h : Nonempty (TwinWidth.ContractionSequence G d)) :
    TwinWidth.SimpleGraph.HasTwinWidthAtMost G d := by
  rcases h with ⟨S⟩
  rcases S with ⟨stepCount, state, start, final, hstart, hfinal, hsteps, hred⟩
  let sourceState : ℕ → TwinWidth.TrigraphState V :=
    fun i => sourceStateOfSubmitted (state i)
  refine ⟨?_⟩
  refine
    { stepCount := stepCount
      state := sourceState
      starts := ?_
      ends := ?_
      step_contracts := ?_
      redDegree_le := ?_ }
  · change TwinWidth.SimpleGraph.IsInitialState G
      (sourceStateOfSubmitted (state 0))
    rw [hstart.down]
    have hstartProp := start.2.down
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceState, sourceStateOfSubmitted,
        TwinWidth.singletonBags, TwinWidth.TrigraphState.singletonBags]
        using hstartProp.1
    · intro A B hA hB
      simpa [sourceState, sourceStateOfSubmitted]
        using hstartProp.2.1 hA hB
    · intro A B hA hB
      simpa [sourceState, sourceStateOfSubmitted]
        using hstartProp.2.2 hA hB
  · change TwinWidth.SimpleGraph.IsFinalState
      (sourceStateOfSubmitted (state stepCount))
    rw [hfinal.down]
    simpa [sourceState, sourceStateOfSubmitted] using final.2.down
  · intro i hi
    rcases hsteps i hi with ⟨A, B, hstepLift⟩
    rcases hstepLift.down with ⟨hA, hB, hAB, hbags, hredStep, hblackStep⟩
    refine ⟨A, ?_, B, ?_, hAB, ?_, ?_, ?_⟩
    · simpa [sourceState, sourceStateOfSubmitted] using hA
    · simpa [sourceState, sourceStateOfSubmitted] using hB
    · simpa [sourceState, sourceStateOfSubmitted] using hbags
    · intro X Y hX hY
      simpa [sourceState, sourceStateOfSubmitted, TwinWidth.contractedRed,
        TwinWidth.SimpleGraph.contractedRed] using hredStep hX hY
    · intro X Y hX hY
      simpa [sourceState, sourceStateOfSubmitted, TwinWidth.contractedRed,
        TwinWidth.contractedBlack, TwinWidth.SimpleGraph.contractedRed,
        TwinWidth.SimpleGraph.contractedBlack] using hblackStep hX hY
  · intro i hi A hA
    simpa [sourceState, sourceStateOfSubmitted, TwinWidth.redDegree,
      TwinWidth.SimpleGraph.redDegree, TwinWidth.TrigraphState.redDegree]
      using hred.down i hi hA

theorem contractionSequence_mono
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d e : ℕ}
    (h : Nonempty (TwinWidth.ContractionSequence G d)) (hde : d ≤ e) :
    Nonempty (TwinWidth.ContractionSequence G e) := by
  rcases h with ⟨S⟩
  rcases S with ⟨stepCount, state, start, final, hstart, hfinal, hsteps, hred⟩
  refine ⟨⟨stepCount, state, start, final, hstart, hfinal, hsteps, ?_⟩⟩
  refine ⟨?_⟩
  intro i hi A hA
  exact le_trans (hred.down i hi hA) hde

theorem contractionSequence_twinWidth
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hex : ∃ d, Nonempty (TwinWidth.ContractionSequence G d)) :
    Nonempty (TwinWidth.ContractionSequence G (TwinWidth.twinWidth G)) := by
  classical
  rw [TwinWidth.twinWidth, TwinWidth.leastNat, dif_pos hex]
  exact Nat.find_spec hex

theorem lt_twinWidth_of_not_contractionSequence
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (hnot : ¬ Nonempty (TwinWidth.ContractionSequence G d))
    (hex : ∃ e, Nonempty (TwinWidth.ContractionSequence G e)) :
    d < TwinWidth.twinWidth G := by
  by_contra hle
  exact hnot
    (contractionSequence_mono
      (contractionSequence_twinWidth G hex) (Nat.le_of_not_gt hle))

/--
---
conclusion: Lax1.ExponentialSeparation.twin_width_can_be_exponential_in_treewidth
---
Self-contained proof of the Bonnet–Depres exponential gap: for every `k`, the
Bonnet–Depres graph `BD_k` has treewidth at most `2*k + 4` while its twin-width
exceeds `2^k`. The proof translates the source tree decomposition into the
submitted tree-decomposition predicate and translates submitted bounded
contraction sequences back into the source structure, where the lower bound is
proved.
-/
theorem twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      Treewidth.treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < TwinWidth.twinWidth G := by
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
        ¬ Nonempty (TwinWidth.ContractionSequence
          (TwinWidth.SimpleGraph.bonnetDepresGraph k) (2 ^ k)) := by
      intro h
      exact hsource (source_contractionSequence_of_submitted h)
    have hex :
        ∃ e, Nonempty (TwinWidth.ContractionSequence
          (TwinWidth.SimpleGraph.bonnetDepresGraph k) e) := by
      refine ⟨Fintype.card (TwinWidth.SimpleGraph.BonnetDepresVertex k), ?_⟩
      exact ⟨submittedContractionSequenceOfSource
        (Classical.choice
          (TwinWidth.SimpleGraph.hasTwinWidthAtMost_card
            (TwinWidth.SimpleGraph.bonnetDepresGraph k)))⟩
    exact lt_twinWidth_of_not_contractionSequence hsubmitted hex

end

end Lax1Proofs.Main
