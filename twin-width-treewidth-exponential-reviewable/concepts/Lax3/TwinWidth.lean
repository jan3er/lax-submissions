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
contraction sequences, and the resulting graph parameter. The Lean definition
uses the value $0$ as a harmless fallback if the defining set is empty.
-/

namespace Lax3.TwinWidth

/-- A trigraph state on the original vertex type `V`: a partition into current
bags with disjoint black and red adjacency relations. -/
def State (V : Type) [DecidableEq V] : Type :=
  Σ bags : Finset (Finset V),
  Σ blackAdj : Finset V → Finset V → Prop,
  Σ redAdj : Finset V → Finset V → Prop,
    PLift (
      (∀ ⦃A⦄, A ∈ bags → A.Nonempty) ∧
      (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → A ≠ B → Disjoint A B) ∧
      (∀ v : V, ∃ A ∈ bags, v ∈ A) ∧
      (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → blackAdj B A) ∧
      (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → redAdj A B → redAdj B A) ∧
      (∀ ⦃A⦄, A ∈ bags → ¬ blackAdj A A) ∧
      (∀ ⦃A⦄, A ∈ bags → ¬ redAdj A A) ∧
      (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → ¬ redAdj A B))

/-- The current bags of a trigraph state. -/
def bags {V : Type} [DecidableEq V] (T : State V) : Finset (Finset V) :=
  Sigma.fst T

/-- The black adjacency relation of a trigraph state. -/
def blackAdj {V : Type} [DecidableEq V] (T : State V) :
    Finset V → Finset V → Prop :=
  Sigma.fst (Sigma.snd T)

/-- The red adjacency relation of a trigraph state. -/
def redAdj {V : Type} [DecidableEq V] (T : State V) :
    Finset V → Finset V → Prop :=
  Sigma.fst (Sigma.snd (Sigma.snd T))

/-- The family of singleton bags on a finite vertex type. -/
noncomputable def singletonBags
    (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.image (fun v : V => ({v} : Finset V))

/-- The red degree of a current bag. -/
noncomputable def redDegree {V : Type} [DecidableEq V]
    (T : State V) (A : Finset V) : ℕ :=
  letI : DecidablePred (fun B => redAdj T A B) := Classical.decPred _
  ((bags T).filter fun B => redAdj T A B).card

/-- Red adjacency after merging the bags `A` and `B`. -/
def contractedRed {V : Type} [DecidableEq V]
    (T : State V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    redAdj T A Y ∨ redAdj T B Y ∨ blackAdj T A Y ≠ blackAdj T B Y
  else if Y = A ∪ B then
    redAdj T X A ∨ redAdj T X B ∨ blackAdj T X A ≠ blackAdj T X B
  else
    redAdj T X Y

/-- Black adjacency after merging the bags `A` and `B`. -/
def contractedBlack {V : Type} [DecidableEq V]
    (T : State V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    blackAdj T A Y ∧ blackAdj T B Y ∧ ¬ contractedRed T A B X Y
  else if Y = A ∪ B then
    blackAdj T X A ∧ blackAdj T X B ∧ ¬ contractedRed T A B X Y
  else
    blackAdj T X Y

/-- A witness that `U` is obtained from `T` by one bag contraction. -/
def Step {V : Type} [DecidableEq V] (T U : State V) : Type :=
  Σ left : Finset V,
  Σ right : Finset V,
    PLift (
      left ∈ bags T ∧
      right ∈ bags T ∧
      left ≠ right ∧
      bags U = insert (left ∪ right) (((bags T).erase left).erase right) ∧
      (∀ ⦃X Y⦄, X ∈ bags U → Y ∈ bags U →
        (redAdj U X Y ↔ contractedRed T left right X Y)) ∧
      (∀ ⦃X Y⦄, X ∈ bags U → Y ∈ bags U →
        (blackAdj U X Y ↔ contractedBlack T left right X Y)))

/-- A trigraph state encoding the starting graph: singleton bags, the graph's
edges as black adjacencies, and no red adjacencies. -/
def InitialState {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Type :=
  Σ state : State V,
    PLift (
      bags state = singletonBags V ∧
      (∀ ⦃A B⦄, A ∈ bags state → B ∈ bags state →
        (blackAdj state A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b)) ∧
      (∀ ⦃A B⦄, A ∈ bags state → B ∈ bags state → ¬ redAdj state A B))

/-- The trigraph state underlying an initial-state witness. -/
def initialState {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (I : InitialState G) : State V :=
  Sigma.fst I

/-- A final trigraph state has at most one current bag. -/
def FinalState (V : Type) [DecidableEq V] : Type :=
  Σ state : State V, PLift ((bags state).card ≤ 1)

/-- The trigraph state underlying a final-state witness. -/
def finalState {V : Type} [DecidableEq V] (F : FinalState V) : State V :=
  Sigma.fst F

/-- A contraction sequence all of whose red degrees are at most `d`. -/
def ContractionSequence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Type :=
  Σ stepCount : ℕ,
  Σ state : ℕ → State V,
  Σ start : InitialState G,
  Σ final : FinalState V,
    PLift (state 0 = initialState start) ×
    PLift (state stepCount = finalState final) ×
    (∀ i, i < stepCount → Step (state i) (state (i + 1))) ×
    PLift (∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ bags (state i) →
      redDegree (state i) A ≤ d)

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
  leastNat fun d => Nonempty (ContractionSequence G d)

end Lax3.TwinWidth
