import Lax1.TwinWidth
import Lax2.MixedMinorNumber

/-!
---
title: Twin-width and mixed minor number are functionally equivalent
---
Two finite-graph parameters are *functionally equivalent* when each is bounded
by a numerical function of the other. Twin-width and mixed minor number are
functionally equivalent: there are functions $f,g:\mathbb N\to\mathbb N$ such
that every finite simple graph $G$ satisfies
$$
  \operatorname{tww}(G) \le f(\operatorname{mmn}(G))
  \quad\text{and}\quad
  \operatorname{mmn}(G) \le g(\operatorname{tww}(G)).
$$
-/

namespace Lax2.FunctionalEquivalence

/-- A natural-valued parameter of finite simple graphs. -/
def GraphParam :=
  ∀ {V : Type}, [Fintype V] → [DecidableEq V] → SimpleGraph V → ℕ

/-- Each of two graph parameters is bounded by a numerical function of the
other. -/
def FunctionallyEquivalent (p q : GraphParam) : Prop :=
  (∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    p (V := V) G ≤ f (q (V := V) G)) ∧
  (∃ g : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    q (V := V) G ≤ g (p (V := V) G))

/-- Twin-width and mixed minor number are functionally equivalent graph
parameters. -/
axiom twin_width_functionally_equivalent_mixed_minor_number :
    FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V] =>
        Lax1.TwinWidth.twinWidth)
      (fun {V : Type} [Fintype V] [DecidableEq V] =>
        Lax2.MixedMinorNumber.mixedMinorNumber)

end Lax2.FunctionalEquivalence
