import Lax1.TwinWidth
import Lax2Proofs.Source.TwinWidth.Contraction.TwinWidth

/-!
# Bridge from the source twin-width development

The proof development uses its original structure-based presentation of
trigraphs and contraction sequences.  The public submission exposes the same
mathematics as small transparent sigma types in `Lax1`.  This file proves that
the two presentations define the same graph parameter.
-/

namespace Lax2Proofs.Bridge

open Lax1

noncomputable section

def submittedStateOfSource {V : Type} [DecidableEq V]
    (T : Lax2Proofs.TwinWidth.TrigraphState V) :
    Lax1.TwinWidth.State V :=
  ⟨T.bags, T.blackAdj, T.redAdj,
    ⟨T.bag_nonempty, T.bag_disjoint, T.bag_cover, T.black_symm, T.red_symm,
      T.black_irrefl, T.red_irrefl, T.black_red_disjoint⟩⟩

def sourceStateOfSubmitted {V : Type} [DecidableEq V]
    (T : Lax1.TwinWidth.State V) :
    Lax2Proofs.TwinWidth.TrigraphState V where
  bags := Lax1.TwinWidth.bags T
  blackAdj := Lax1.TwinWidth.blackAdj T
  redAdj := Lax1.TwinWidth.redAdj T
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
    (T : Lax2Proofs.TwinWidth.TrigraphState V)
    (h : Lax2Proofs.TwinWidth.SimpleGraph.IsInitialState G T) :
    Lax1.TwinWidth.InitialState G :=
  ⟨submittedStateOfSource T, ⟨by
    refine ⟨?_, ?_, ?_⟩
    · simpa [submittedStateOfSource, Lax1.TwinWidth.singletonBags,
        Lax2Proofs.TwinWidth.TrigraphState.singletonBags] using h.1
    · intro A B hA hB
      simpa [submittedStateOfSource] using h.2.1 hA hB
    · intro A B hA hB
      simpa [submittedStateOfSource] using h.2.2 hA hB⟩⟩

def submittedFinalStateOfSource {V : Type} [DecidableEq V]
    (T : Lax2Proofs.TwinWidth.TrigraphState V)
    (h : Lax2Proofs.TwinWidth.SimpleGraph.IsFinalState T) :
    Lax1.TwinWidth.FinalState V :=
  ⟨submittedStateOfSource T, ⟨by
    simpa [submittedStateOfSource] using h⟩⟩

def submittedStepOfSource {V : Type} [DecidableEq V]
    {T U : Lax2Proofs.TwinWidth.TrigraphState V}
    (h : Lax2Proofs.TwinWidth.SimpleGraph.IsContractionStep T U) :
    Lax1.TwinWidth.Step (submittedStateOfSource T) (submittedStateOfSource U) := by
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
        (U.redAdj X Y ↔
          Lax2Proofs.TwinWidth.SimpleGraph.contractedRed T A B X Y) :=
    hBpack.2.2.2.1
  have hblack :
      ∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
        (U.blackAdj X Y ↔
          Lax2Proofs.TwinWidth.SimpleGraph.contractedBlack T A B X Y) :=
    hBpack.2.2.2.2
  refine ⟨A, B, ⟨?_, ?_, hAB, ?_, ?_, ?_⟩⟩
  · simpa [submittedStateOfSource] using hA
  · simpa [submittedStateOfSource] using hB
  · simpa [submittedStateOfSource] using hbags
  · intro X Y hX hY
    simpa [submittedStateOfSource, Lax1.TwinWidth.contractedRed,
      Lax2Proofs.TwinWidth.SimpleGraph.contractedRed] using hred hX hY
  · intro X Y hX hY
    simpa [submittedStateOfSource, Lax1.TwinWidth.contractedRed,
      Lax1.TwinWidth.contractedBlack,
      Lax2Proofs.TwinWidth.SimpleGraph.contractedRed,
      Lax2Proofs.TwinWidth.SimpleGraph.contractedBlack] using hblack hX hY

def submittedContractionSequenceOfSource
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (S : Lax2Proofs.TwinWidth.SimpleGraph.ContractionSequence G d) :
    Lax1.TwinWidth.ContractionSequence G d :=
  ⟨S.stepCount, fun i => submittedStateOfSource (S.state i),
    submittedInitialStateOfSource (S.state 0) S.starts,
    submittedFinalStateOfSource (S.state S.stepCount) S.ends,
    ⟨rfl⟩, ⟨rfl⟩,
    (fun i hi => submittedStepOfSource (S.step_contracts i hi)),
    ⟨by
      intro i hi A hA
      simpa [submittedStateOfSource, Lax1.TwinWidth.redDegree,
        Lax2Proofs.TwinWidth.SimpleGraph.redDegree,
        Lax2Proofs.TwinWidth.TrigraphState.redDegree]
        using S.redDegree_le i hi hA⟩⟩

theorem sourceContractionSequenceOfSubmitted
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (h : Nonempty (Lax1.TwinWidth.ContractionSequence G d)) :
    Lax2Proofs.TwinWidth.SimpleGraph.HasTwinWidthAtMost G d := by
  rcases h with ⟨S⟩
  rcases S with ⟨stepCount, state, start, final, hstart, hfinal, hsteps, hred⟩
  let sourceState : ℕ → Lax2Proofs.TwinWidth.TrigraphState V :=
    fun i => sourceStateOfSubmitted (state i)
  refine ⟨{
    stepCount := stepCount
    state := sourceState
    starts := ?_
    ends := ?_
    step_contracts := ?_
    redDegree_le := ?_ }⟩
  · change Lax2Proofs.TwinWidth.SimpleGraph.IsInitialState G
      (sourceStateOfSubmitted (state 0))
    rw [hstart.down]
    have hstartProp := start.2.down
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceState, sourceStateOfSubmitted,
        Lax1.TwinWidth.singletonBags,
        Lax2Proofs.TwinWidth.TrigraphState.singletonBags] using hstartProp.1
    · intro A B hA hB
      simpa [sourceState, sourceStateOfSubmitted] using hstartProp.2.1 hA hB
    · intro A B hA hB
      simpa [sourceState, sourceStateOfSubmitted] using hstartProp.2.2 hA hB
  · change Lax2Proofs.TwinWidth.SimpleGraph.IsFinalState
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
      simpa [sourceState, sourceStateOfSubmitted, Lax1.TwinWidth.contractedRed,
        Lax2Proofs.TwinWidth.SimpleGraph.contractedRed] using hredStep hX hY
    · intro X Y hX hY
      simpa [sourceState, sourceStateOfSubmitted, Lax1.TwinWidth.contractedRed,
        Lax1.TwinWidth.contractedBlack,
        Lax2Proofs.TwinWidth.SimpleGraph.contractedRed,
        Lax2Proofs.TwinWidth.SimpleGraph.contractedBlack] using hblackStep hX hY
  · intro i hi A hA
    simpa [sourceState, sourceStateOfSubmitted, Lax1.TwinWidth.redDegree,
      Lax2Proofs.TwinWidth.SimpleGraph.redDegree,
      Lax2Proofs.TwinWidth.TrigraphState.redDegree] using hred.down i hi hA

theorem hasTwinWidthAtMost_iff_submitted
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (d : ℕ) :
    Lax2Proofs.TwinWidth.SimpleGraph.HasTwinWidthAtMost G d ↔
      Nonempty (Lax1.TwinWidth.ContractionSequence G d) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨submittedContractionSequenceOfSource S⟩
  · exact sourceContractionSequenceOfSubmitted

theorem sourceTwinWidth_eq_submitted
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Lax2Proofs.TwinWidth.SimpleGraph.twinWidth G = Lax1.TwinWidth.twinWidth G := by
  classical
  by_cases hs : ∃ d, Lax2Proofs.TwinWidth.SimpleGraph.HasTwinWidthAtMost G d
  · have hp : ∃ d, Nonempty (Lax1.TwinWidth.ContractionSequence G d) := by
      rcases hs with ⟨d, hd⟩
      exact ⟨d, (hasTwinWidthAtMost_iff_submitted G d).mp hd⟩
    rw [Lax2Proofs.TwinWidth.SimpleGraph.twinWidth, dif_pos hs,
      Lax1.TwinWidth.twinWidth, Lax1.TwinWidth.leastNat, dif_pos hp]
    apply Nat.le_antisymm
    · exact Nat.find_min' hs
        ((hasTwinWidthAtMost_iff_submitted G (Nat.find hp)).mpr (Nat.find_spec hp))
    · exact Nat.find_min' hp
        ((hasTwinWidthAtMost_iff_submitted G (Nat.find hs)).mp (Nat.find_spec hs))
  · have hp : ¬ ∃ d, Nonempty (Lax1.TwinWidth.ContractionSequence G d) := by
      rintro ⟨d, hd⟩
      exact hs ⟨d, (hasTwinWidthAtMost_iff_submitted G d).mpr hd⟩
    rw [Lax2Proofs.TwinWidth.SimpleGraph.twinWidth, dif_neg hs,
      Lax1.TwinWidth.twinWidth, Lax1.TwinWidth.leastNat, dif_neg hp]

end

end Lax2Proofs.Bridge
