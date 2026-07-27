import Lax14.OrderTypes
import Mathlib.Data.Set.Card

/-!
---
title: Ramsey's theorem for tuples
type: theorem
---
For every number of colours *k*, every arity ℓ and every size *s* there is
an *N* such that for every colouring of the ℓ-tuples over a linearly
ordered *N*-element set with *k* colours there is a subset *I* of size *s*
on which the colour of a tuple depends only on its order type: any two
tuples with entries in *I* that are arranged in the same way receive the
same colour. This is the finite Ramsey theorem for hypergraphs of
Erdős and Rado, in the order-type form used in model theory.

# Formalization notes

Tuples are arbitrary functions `Fin ℓ → Fin n`, so repeated entries and
every ordering of the entries are allowed. This is stronger than colouring
the ℓ-element *subsets* of the ground set — that classical form is the
special case where the colouring only depends on the increasing
enumeration — and it is the form that applications consume, since the
tuples they colour arise from arbitrary indexed families.

Homogeneity is stated as "tuples with entries in *I* and equal order types
receive equal colours", rather than as the existence of a function from
order types to colours through which the colouring factors. The two are
equivalent — such a function is obtained by choice — and the stated form
carries no choice and needs no default colour for the order types that no
tuple over *I* realizes.

The ground set is `Fin n` with its standard linear order, the canonical
carrier of this submission; sizes are `Set.ncard`, stated as "at least".
As in the other statements, no hypothesis is placed on the number of
colours: with `k = 0` there is no colouring at all.
-/

namespace Lax14.TupleRamsey

open Lax14.OrderTypes

/-- Ramsey's theorem for tuples: every `k`-colouring of the `ℓ`-tuples
over a large enough linearly ordered finite set has a subset of size `s`
on which the colour of a tuple depends only on its order type. -/
axiom exists_orderType_homogeneous (k ℓ s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : (Fin ℓ → Fin n) → Fin k), N ≤ n →
      ∃ I : Set (Fin n), s ≤ I.ncard ∧
        ∀ a b : Fin ℓ → Fin n, (∀ i, a i ∈ I) → (∀ i, b i ∈ I) →
          orderType a = orderType b → c a = c b

end Lax14.TupleRamsey
