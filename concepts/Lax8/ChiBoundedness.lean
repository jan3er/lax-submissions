import Lax8.MergeWidth

/-!
---
title: χ-Boundedness
type: definition
---
A class of finite simple graphs is χ-bounded if the chromatic number of each
graph in the class is bounded by a function of its clique number.
-/

namespace Lax8.ChiBoundedness

open Lax8.MergeWidth

/-- A graph class $C$ is χ-bounded if there is a function $f$ such that every
$G ∈ C$ is $f(ω(G))$-colourable. -/
def ChiBounded (C : GraphClass) : Prop :=
  ∃ f : ℕ → ℕ, ∀ ⦃V : Type⦄ [Fintype V] (G : SimpleGraph V), C G →
    G.Colorable (f G.cliqueNum)

end Lax8.ChiBoundedness
