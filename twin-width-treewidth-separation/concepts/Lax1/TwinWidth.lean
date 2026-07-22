import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Find

/-!
---
title: Twin-width
---
A trigraph contraction sequence starts from the singleton partition of a
finite simple graph. At every step it merges two current bags. Adjacencies
that remain uniformly present are black; adjacencies that were already red or
become nonuniform after a merge are red. The sequence ends with at most one
bag, and its width is the largest red degree occurring at any stage.

The twin-width $\operatorname{tww}(G)$ is the least $d$ for which $G$ has a
contraction sequence of width at most $d$. The declarations below give the
complete definition: trigraph states, their contraction rule, bounded
contraction sequences, and the resulting graph parameter. The Lean minimum
uses the value $0$ as a harmless fallback if the defining set is empty.
-/

namespace Lax1.TwinWidth

/-- A trigraph state on the original vertex type `V`: a partition of the
vertices into current bags together with disjoint black and red adjacency
relations between bags. -/
structure TrigraphState (V : Type) where
  /-- Current bags, represented as finite subsets of the original vertex
  set. -/
  bags : Finset (Finset V)
  /-- Every current bag is nonempty. -/
  bag_nonempty : ∀ ⦃A⦄, A ∈ bags → A.Nonempty
  /-- Distinct current bags are disjoint. -/
  bag_disjoint : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → A ≠ B → Disjoint A B
  /-- The current bags cover the original vertex set. -/
  bag_cover : ∀ v : V, ∃ A ∈ bags, v ∈ A
  /-- Black, uniform adjacencies between current bags. -/
  blackAdj : Finset V → Finset V → Prop
  /-- Red, error adjacencies between current bags. -/
  redAdj : Finset V → Finset V → Prop
  /-- Black adjacency is symmetric on bags. -/
  black_symm : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → blackAdj B A
  /-- Red adjacency is symmetric on bags. -/
  red_symm : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → redAdj A B → redAdj B A
  /-- No bag has a black loop. -/
  black_irrefl : ∀ ⦃A⦄, A ∈ bags → ¬ blackAdj A A
  /-- No bag has a red loop. -/
  red_irrefl : ∀ ⦃A⦄, A ∈ bags → ¬ redAdj A A
  /-- A pair of bags is never simultaneously black- and red-adjacent. -/
  black_red_disjoint :
    ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → ¬ redAdj A B

/-- The family of singleton bags on a finite vertex type: the bags of the
finest partition. -/
noncomputable def TrigraphState.singletonBags
    (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.image fun v : V => ({v} : Finset V)

/-- The red degree of a current bag. -/
noncomputable def TrigraphState.redDegree {V : Type}
    (T : TrigraphState V) (A : Finset V) : ℕ :=
  letI : DecidablePred fun B => T.redAdj A B := Classical.decPred _
  (T.bags.filter fun B => T.redAdj A B).card

/-- The initial trigraph state of a graph: singleton bags, the graph's edges
as black adjacencies, and no red adjacencies. -/
def IsInitialState {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : TrigraphState V) : Prop :=
  T.bags = TrigraphState.singletonBags V ∧
    (∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags →
      (T.blackAdj A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b)) ∧
    (∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags → ¬ T.redAdj A B)

/-- A final trigraph state has at most one current bag. -/
def IsFinalState {V : Type} (T : TrigraphState V) : Prop :=
  T.bags.card ≤ 1

/-- Red adjacency after merging the bags `A` and `B`: the merged bag is
red-adjacent to a bag that was red-adjacent to either part or whose black
adjacencies to the two parts disagree; other pairs are unchanged. -/
def contractedRed {V : Type} [DecidableEq V]
    (T : TrigraphState V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    T.redAdj A Y ∨ T.redAdj B Y ∨ T.blackAdj A Y ≠ T.blackAdj B Y
  else if Y = A ∪ B then
    T.redAdj X A ∨ T.redAdj X B ∨ T.blackAdj X A ≠ T.blackAdj X B
  else
    T.redAdj X Y

/-- Black adjacency after merging the bags `A` and `B`: the merged bag keeps
a black edge only where both parts had one and no red edge is created; other
pairs are unchanged. -/
def contractedBlack {V : Type} [DecidableEq V]
    (T : TrigraphState V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    T.blackAdj A Y ∧ T.blackAdj B Y ∧ ¬ contractedRed T A B X Y
  else if Y = A ∪ B then
    T.blackAdj X A ∧ T.blackAdj X B ∧ ¬ contractedRed T A B X Y
  else
    T.blackAdj X Y

/-- `U` is obtained from `T` by merging two distinct current bags. -/
def IsContractionStep {V : Type} [DecidableEq V]
    (T U : TrigraphState V) : Prop :=
  ∃ A ∈ T.bags, ∃ B ∈ T.bags, A ≠ B ∧
    U.bags = insert (A ∪ B) ((T.bags.erase A).erase B) ∧
    (∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
      (U.redAdj X Y ↔ contractedRed T A B X Y)) ∧
    (∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
      (U.blackAdj X Y ↔ contractedBlack T A B X Y))

/-- A contraction sequence for `G` all of whose red degrees are at most
`d`. -/
structure ContractionSequence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) where
  /-- The number of contraction steps. -/
  stepCount : ℕ
  /-- The trigraph state after each number of steps. -/
  state : ℕ → TrigraphState V
  /-- The sequence starts at the initial state of `G`. -/
  starts : IsInitialState G (state 0)
  /-- The sequence ends fully contracted. -/
  ends : IsFinalState (state stepCount)
  /-- Consecutive states are related by one bag contraction. -/
  step_contracts :
    ∀ i, i < stepCount → IsContractionStep (state i) (state (i + 1))
  /-- Every bag of every state has red degree at most `d`. -/
  redDegree_le :
    ∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ (state i).bags →
      (state i).redDegree A ≤ d

/-- `G` admits a contraction sequence of width at most `d`. -/
def HasTwinWidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (ContractionSequence G d)

/-- The least natural satisfying `P`, or zero if no natural satisfies it.
This packages the minimization convention used in the definition of
twin-width. -/
noncomputable def leastNat (P : ℕ → Prop) : ℕ :=
  letI : Decidable (∃ n, P n) := Classical.propDecidable _
  letI : DecidablePred P := Classical.decPred P
  if h : ∃ n, P n then Nat.find h else 0

/-- The twin-width of a finite simple graph. -/
noncomputable def twinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  leastNat fun d => HasTwinWidthAtMost G d

end Lax1.TwinWidth
