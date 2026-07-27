import Lax11.Ram

/-!
---
title: Computing a function within a time bound
type: definition
---
A random access machine program computes a function of words within a
time bound *T* on a set *D* of admissible inputs if, started on any
input *x* in *D*, it halts after at most *T(x)* steps having written
the value of the function at *x* to its output tape. The bound is a
function of the input, so that bounds like "linear in the length of the
input" are stated by instantiating *T*.

# Formalization notes

The number of steps is the machine's own step count, so a time bound is
a statement about the *program*: nothing is annotated onto the program
and then trusted. Only inputs in `D` are constrained; a program is free
to do anything at all on malformed input, which is what a statement
about an algorithm on encoded objects should say.

The bound is stated elementarily — an explicit `T` that the step count
does not exceed — rather than through asymptotic notation. Asymptotics
would require a filter on inputs and would obscure, rather than
clarify, a statement that quantifies over encodings of every graph; a
linear bound is spelled out at the point of use as `c * (x.length + 1)`
with an explicit constant, a fixed-parameter bound as
`c * 2 ^ k * (x.length + 1)` with the parameter dependence written in,
the `+ 1` making both meaningful for the empty input as well.

Only the timed notion is defined: every statement of this submission
carries a bound, and plain computability is the special case in which
`T` is unconstrained.
-/

namespace Lax11.RamComputes

open Lax11.Ram

/-- On every admissible input `x`, the program halts within `T x` steps
with output `f x`. -/
def ComputesInTime (p : Program) (D : Set (List ℕ))
    (f : List ℕ → List ℕ) (T : List ℕ → ℕ) : Prop :=
  ∀ x ∈ D, ∃ t ≤ T x, RunsTo p x (f x) t

end Lax11.RamComputes
