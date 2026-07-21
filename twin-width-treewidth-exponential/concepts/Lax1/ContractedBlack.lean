import Lax1.ContractedRed

/-!
---
title: Black adjacency after contraction
---
$\mathrm{contractedBlack}(T,A,B,X,Y)$ is the black adjacency relation
defined from a trigraph state $T$ after contracting the two bags $A$ and
$B$. Loops are not black. For the merged bag $A\cup B$, black adjacency
to $Y$ requires both old black adjacencies to $Y$ and requires that
$\mathrm{contractedRed}(T,A,B,X,Y)$ is false. Pairs not involving the
merged bag keep their old black adjacency in $T$.
-/


namespace Lax1.ContractedBlack

open Lax1.ContractedRed
open Lax1.TrigraphState

/-- Black adjacency after contracting two bags `A` and `B` in a trigraph
state. -/
def contractedBlack {V : Type} [DecidableEq V]
    (T : State V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    blackAdj T A Y ∧ blackAdj T B Y ∧
      ¬ contractedRed T A B X Y
  else if Y = A ∪ B then
    blackAdj T X A ∧ blackAdj T X B ∧
      ¬ contractedRed T A B X Y
  else
    blackAdj T X Y

end Lax1.ContractedBlack
