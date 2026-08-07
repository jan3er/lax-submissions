import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Graph parameters and functional equivalence
type: definition
---
A *graph parameter* assigns a natural number to every finite simple graph.
Two graph parameters *p* and *q* are *functionally equivalent* when each is
bounded by a numerical function of the other: there are functions
*f*, *g* : ℕ → ℕ such that every finite simple graph *G* satisfies both
*p*(*G*) ≤ *f*(*q*(*G*)) and *q*(*G*) ≤ *g*(*p*(*G*)). Functionally
equivalent parameters are bounded on exactly the same classes of graphs.

# Formalization notes

`GraphParam` is the uniform signature shared by all graph parameters in this
archive: a natural-valued function of finite simple graphs over `Fintype` and
`DecidableEq` instances. It is an abbreviation, so a statement about concrete
parameters mentions them by name — `Lax48.TwinWidth.twinWidth`,
`Lax49.MixedMinorNumber.mixedMinorNumber` — with no eta-expanded wrapper
lambdas a reader would have to unfold.

The two directions of `FunctionallyEquivalent` are separate existential
claims rather than one function pair, so each can be established on its own.
-/

namespace Lax49.GraphParameters

/-- A natural-valued parameter of finite simple graphs, in the uniform
signature shared by all graph parameters in this archive. -/
abbrev GraphParam :=
  ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → ℕ

/-- Each of two graph parameters is bounded by a numerical function of the
other. -/
def FunctionallyEquivalent (p q : GraphParam) : Prop :=
  (∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V), p G ≤ f (q G)) ∧
  (∃ g : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V), q G ≤ g (p G))

end Lax49.GraphParameters
