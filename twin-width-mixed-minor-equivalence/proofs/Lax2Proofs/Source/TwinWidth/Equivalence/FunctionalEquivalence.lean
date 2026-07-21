import Lax2Proofs.Source.TwinWidth.Contraction.TwinWidth

/-!
# Functional equivalence of graph parameters

This file defines the abstract relation used by the main theorem: each graph
parameter is bounded by a numerical function of the other.
-/

namespace Lax2Proofs.TwinWidth

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

end Lax2Proofs.TwinWidth
