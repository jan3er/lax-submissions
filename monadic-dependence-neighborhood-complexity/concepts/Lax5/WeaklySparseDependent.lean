import Lax5.GraphClasses
import Lax5.MonadicDependence
import Lax5.NowhereDenseClasses

/-!
---
title: Weakly sparse monadically dependent classes are nowhere dense
type: theorem
---
Every weakly sparse monadically dependent graph class is nowhere dense.
Together with the statement that nowhere dense classes are monadically
dependent, this carries the classical equivalence: on weakly sparse
classes, monadic dependence and nowhere denseness coincide.

# Formalization notes

The hypotheses are the weak sparseness predicate of the graph classes
concept and the transduction-based definition of monadic dependence;
the conclusion is the shallow-minor definition of the nowhere dense
concept.
-/

namespace Lax5.WeaklySparseDependent

open Lax5.GraphClasses Lax5.MonadicDependence Lax5.NowhereDenseClasses

/-- Every weakly sparse monadically dependent graph class is nowhere
dense. -/
axiom nowhereDense_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    NowhereDense C

end Lax5.WeaklySparseDependent
