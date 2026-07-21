import Mathlib.Data.Finset.Card
import Lax1.TrigraphState

/-!
---
title: Red degree in a trigraph state
---
For a trigraph state $T$ and a current bag $A$,
$\mathrm{redDegree}(T,A)$ is
$$|\{C\in\mathrm{bags}(T) : \mathrm{redAdj}(T,A,C)\}|.$$
-/


namespace Lax1.RedDegree

open Lax1.TrigraphState

noncomputable section

/-- The red degree of a bag, counted among the current bags of a trigraph
state. -/
def redDegree {V : Type} [DecidableEq V]
    (T : State V) (A : Finset V) : ℕ :=
  letI : DecidablePred (fun B => redAdj T A B) :=
    Classical.decPred (fun B => redAdj T A B)
  ((bags T).filter fun B => redAdj T A B).card

end

end Lax1.RedDegree
