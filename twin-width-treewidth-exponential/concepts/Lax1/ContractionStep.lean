import Lax1.ContractedBlack
import Lax1.ContractedRed

/-!
---
title: One contraction step
---
$\mathrm{Step}(T,U)$ is the type of witnesses that the trigraph state
$U$ is obtained from the trigraph state $T$ by one contraction. Such a
witness chooses two distinct current bags $A,B$ of $T$ and states that they
are replaced by $A\cup B$:
$$\mathrm{bags}(U)=\{A\cup B\}\cup
    (\mathrm{bags}(T)\setminus\{A,B\}),$$
and that the red and black adjacencies of $U$ are exactly the relations
defined by $\mathrm{contractedRed}(T,A,B,-,-)$ and
$\mathrm{contractedBlack}(T,A,B,-,-)$.
-/


namespace Lax1.ContractionStep

open Lax1.ContractedBlack
open Lax1.ContractedRed
open Lax1.TrigraphState

/-- The type of witnesses that one trigraph state is obtained from another by
contracting two distinct current bags. -/
def Step {V : Type} [DecidableEq V]
    (T U : State V) : Type :=
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

end Lax1.ContractionStep
