import Mathlib.Combinatorics.SimpleGraph.Basic
import Lax1.ContractionStep
import Lax1.FinalTrigraphState
import Lax1.InitialTrigraphState
import Lax1.RedDegree

/-!
---
title: Bounded-width contraction sequence
---
$\mathrm{ContractionSequence}(G,d)$ is the type of bounded contraction
sequences of the graph $G$. An element consists of a finite time horizon,
a trigraph state at each time, a witness that time $0$ is the initial
singleton-bag state of $G$, a witness that the final time has at most one bag,
a contraction-step witness between every successive pair of states, and the
bound
$$\mathrm{redDegree}(T_i,A)\le d$$
for every time $i$ up to the final time and every current bag $A$.
-/


namespace Lax1.ContractionSequenceWidth

open Lax1.ContractionStep
open Lax1.FinalTrigraphState
open Lax1.InitialTrigraphState
open Lax1.RedDegree
open Lax1.TrigraphState

/-- The type of contraction sequences whose red degree is everywhere at most
`d`.  The data are a finite time horizon, a trigraph state at each time, an
initial-state witness, a final-state witness, a contraction witness for each
successive pair of states, and the red-degree bound. -/
def ContractionSequence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Type :=
  Σ stepCount : ℕ,
  Σ state : ℕ → State V,
  Σ start : InitialState G,
  Σ final : FinalState V,
    PLift (state 0 = InitialTrigraphState.state start) ×
    PLift (state stepCount = FinalTrigraphState.state final) ×
    (∀ i, i < stepCount → Step (state i) (state (i + 1))) ×
    PLift (∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ bags (state i) →
      redDegree (state i) A ≤ d)

end Lax1.ContractionSequenceWidth
