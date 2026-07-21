import Mathlib.Data.Finset.Card
import Lax1.TrigraphState

/-!
---
title: Final trigraph state
---
$\mathrm{FinalState}(V)$ is the subtype of trigraph states on $V$
whose current family of bags has cardinality at most one:
$$|\mathrm{bags}(T)|\le 1.$$

For $F:\mathrm{FinalState}(V)$, $\mathrm{state}(F)$ is its
underlying trigraph state.
-/


namespace Lax1.FinalTrigraphState

open Lax1.TrigraphState

/-- The type of final trigraph states, namely states with at most one current
bag. -/
def FinalState (V : Type) [DecidableEq V] : Type :=
  Σ state : State V, PLift ((bags state).card ≤ 1)

/-- The underlying trigraph state of a final state. -/
def state {V : Type} [DecidableEq V] (F : FinalState V) : State V :=
  Sigma.fst F

end Lax1.FinalTrigraphState
