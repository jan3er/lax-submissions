import Lax5.GraphClasses
import Lax5.MonadicDependence
import Lax12.NowhereDenseClasses

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
concept of this submission and the transduction-based definition of
monadic dependence; the conclusion is `NowhereDense`, the shallow-minor
definition of the *Sparsity Lectures* submission (Lax12), where nowhere
denseness is defined and endorsed. Stating the conclusion over that
definition is what lets this statement compose directly with the
sparsity theory built on it.
-/

namespace Lax5.WeaklySparseDependent

open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax5.GraphClasses Lax5.MonadicDependence

/-- Every weakly sparse monadically dependent graph class is nowhere
dense. -/
axiom nowhereDense_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    NowhereDense C

end Lax5.WeaklySparseDependent
