import Mathlib.Data.Finset.Basic
import Lax1.TrigraphState

/-!
---
title: Red adjacency after contraction
---
$\mathrm{contractedRed}(T,A,B,X,Y)$ is the red adjacency relation
defined from a trigraph state $T$ after contracting the two bags $A$ and
$B$. Loops are not red. For the merged bag $A\cup B$, red adjacency to
another bag $Y$ is inherited from either old red adjacency
$R_T(A,Y)$ or $R_T(B,Y)$, or is created when the old black adjacencies
$K_T(A,Y)$ and $K_T(B,Y)$ disagree. Pairs not involving the merged bag
keep their old red adjacency in $T$.
-/


namespace Lax1.ContractedRed

open Lax1.TrigraphState

/-- Red adjacency after contracting two bags `A` and `B` in a trigraph state. -/
def contractedRed {V : Type} [DecidableEq V]
    (T : State V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    redAdj T A Y ∨ redAdj T B Y ∨
      blackAdj T A Y ≠ blackAdj T B Y
  else if Y = A ∪ B then
    redAdj T X A ∨ redAdj T X B ∨
      blackAdj T X A ≠ blackAdj T X B
  else
    redAdj T X Y

end Lax1.ContractedRed
