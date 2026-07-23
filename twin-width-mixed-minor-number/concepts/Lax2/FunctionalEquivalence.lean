import Lax1.TwinWidth
import Lax2.MixedMinorNumber

/-!
---
title: Twin-width and mixed minor number are functionally equivalent
type: theorem
---
Two finite-graph parameters are *functionally equivalent* when each is
bounded by a numerical function of the other. Twin-width and mixed minor
number are functionally equivalent: there are functions
$f,g:\mathbb N\to\mathbb N$ such that every finite simple graph $G$ satisfies
$$
  \operatorname{tww}(G) \le f(\operatorname{mmn}(G))
  \quad\text{and}\quad
  \operatorname{mmn}(G) \le g(\operatorname{tww}(G)).
$$

# Formalization notes

`GraphParam` is the uniform signature shared by all graph parameters in this
archive: a natural-valued function of finite simple graphs over `Fintype`
and `DecidableEq` instances. It is an abbreviation, so the statement applies
to `Lax1.TwinWidth.twinWidth` and `Lax2.MixedMinorNumber.mixedMinorNumber`
directly, without wrapper lambdas.
-/

namespace Lax2.FunctionalEquivalence

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

/-- Twin-width and mixed minor number are functionally equivalent graph
parameters. -/
axiom twin_width_functionally_equivalent_mixed_minor_number :
    FunctionallyEquivalent
      Lax1.TwinWidth.twinWidth
      Lax2.MixedMinorNumber.mixedMinorNumber

end Lax2.FunctionalEquivalence
