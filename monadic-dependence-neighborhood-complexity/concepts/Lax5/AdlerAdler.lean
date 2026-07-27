import Lax5.MonadicDependence
import Lax12.NowhereDenseClasses

/-!
---
title: Nowhere dense classes are monadically dependent
type: theorem
---
Every nowhere dense graph class is monadically dependent. Together with
the statement that weakly sparse monadically dependent classes are
nowhere dense, this carries the classical equivalence: on weakly sparse
classes, monadic dependence and nowhere denseness coincide.

# Formalization notes

Adler and Adler proved that nowhere dense classes are monadically
*stable*; monadic dependence is the weakening stated here, which is how
the equivalence is used in the literature. The hypothesis is
`NowhereDense`, the shallow-minor definition of the *Sparsity Lectures*
submission (Lax12), where nowhere denseness is defined and endorsed.
-/

namespace Lax5.AdlerAdler

open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax5.MonadicDependence

/-- Nowhere dense graph classes are monadically dependent. -/
axiom monadicallyDependent_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    MonadicallyDependent C

end Lax5.AdlerAdler
