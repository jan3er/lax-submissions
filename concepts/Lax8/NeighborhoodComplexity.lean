import Lax8.MergeWidth

/-!
---
title: Linear Neighbourhood Complexity
type: definition
---
For a finite simple graph $G$ and a natural number $p$, the neighbourhood
complexity $π_G(p)$ is the maximum, over sets $X$ of $p$ vertices, of the number
of distinct traces on $X$ of the neighbourhoods of vertices outside $X$. A
graph class has linear neighbourhood complexity if $π_G(p)$ is bounded by a
constant multiple of $p$ for every positive $p$.
-/

namespace Lax8.NeighborhoodComplexity

open Lax8.MergeWidth
open scoped Classical

universe u

variable {V : Type u} [Fintype V]

/-- The neighbourhood complexity $π_G(p)$ of a finite simple graph $G$. -/
noncomputable def neighborhoodComplexity (G : SimpleGraph V) (p : ℕ) : ℕ :=
  (Finset.univ.powersetCard p).sup fun X =>
    ((Finset.univ \ X).image fun v => X.filter fun u => G.Adj v u).card

/-- A graph class has linear neighbourhood complexity if $π_G(p) ≤ c p$ for
some constant $c$ and every positive $p$. -/
def LinearNeighborhoodComplexity (C : GraphClass) : Prop :=
  ∃ c : ℕ, ∀ ⦃V : Type⦄ [Fintype V] (G : SimpleGraph V), C G → ∀ p, 1 ≤ p →
    neighborhoodComplexity G p ≤ c * p

end Lax8.NeighborhoodComplexity
