import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Functional equivalence of graph parameters
---
A graph parameter assigns a natural number to every finite simple graph
(uniformly in the vertex type). Two parameters $p$ and $q$ are *functionally
equivalent* when each is bounded by a numerical function of the other: there
are $f, g : \mathbb{N} \to \mathbb{N}$ with $p(G) \le f(q(G))$ and
$q(G) \le g(p(G))$ for every finite simple graph $G$.
-/

namespace Lax2.FunctionalEquivalence

/-- A finite simple-graph parameter. -/
def GraphParam :=
  ∀ {V : Type}, [Fintype V] → [DecidableEq V] → SimpleGraph V → ℕ

/-- Two graph parameters are functionally equivalent when each is bounded by
some numerical function of the other. -/
def FunctionallyEquivalent (p q : GraphParam) : Prop :=
  (∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    p (V := V) G ≤ f (q (V := V) G)) ∧
  (∃ g : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    q (V := V) G ≤ g (p (V := V) G))

end Lax2.FunctionalEquivalence
