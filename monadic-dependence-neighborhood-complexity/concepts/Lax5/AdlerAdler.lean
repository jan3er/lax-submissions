import Lax5.MonadicDependence
import Lax5.NowhereDenseClasses

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
the equivalence is used in the literature.
-/

namespace Lax5.AdlerAdler

open Lax5.GraphClasses Lax5.MonadicDependence Lax5.NowhereDenseClasses

/-- Nowhere dense graph classes are monadically dependent. -/
axiom monadicallyDependent_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    MonadicallyDependent C

end Lax5.AdlerAdler
