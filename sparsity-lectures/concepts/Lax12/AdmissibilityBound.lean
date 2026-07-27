import Lax12.Admissibility
import Lax12.ShallowTopologicalMinors

/-!
---
title: Admissibility is bounded by topological shallow-minor density
type: theorem
---
If every depth-*r* topological minor of a graph *G* has at most
*d* · |V| edges, then the (*r*+1)-admissibility of *G* is at most
1 + 6 · (*r*+1) · *d*³. This is the workhorse behind every bound of a
generalized coloring number by an edge-density bound: sparse shallow
topological minors force an ordering in which no vertex reaches many
predecessors along disjoint short paths.

The source lecture notes state this as Lemma 3.2 of Chapter 2 (2019/20
edition): for every *r* and every graph *G*,
adm_*r*(*G*) ≤ 1 + 6*r*⌈∇̃_{*r*−1}(*G*)⌉³, where ∇̃ is the topological
grad.

# Formalization notes

Hypothesis and conclusion are the predicates of the two imported
definition concepts. The statement is the notes' Lemma 3.2 with its
radius index shifted by one: the notes pair a conclusion at radius *r*
with a hypothesis at depth *r*−1, and writing the conclusion at *r*+1
against a hypothesis at depth *r* keeps truncated natural subtraction
out of a concept statement. This is presentation only — the shifted form
ranges over exactly the instances *r* ≥ 1 of the notes' form, which are
all of its instances with a defined hypothesis, and the constant is the
notes' constant with *r* read as *r*+1.

The natural number *d* plays the notes' ⌈∇̃_{*r*−1}(*G*)⌉: the
hypothesis `HasTopologicalDensityAtMost G r d` says exactly that the
topological grad of *G* at depth *r* is at most *d*, and the notes
instantiate their lemma at the ceiling of that grad, the least natural
number with this property. The leading 1 of the bound is the vertex *v*
itself, which admissibility counts.
-/

namespace Lax12.AdmissibilityBound

open Lax12.Admissibility Lax12.ShallowTopologicalMinors

/-- A depth-`r` topological edge-density bound `d` for `G` bounds the
`(r+1)`-admissibility of `G` by `1 + 6 · (r+1) · d ^ 3`. -/
axiom adm_le_of_hasTopologicalDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n))
    (r d : ℕ) (h : HasTopologicalDensityAtMost G r d) :
    adm G (r + 1) ≤ 1 + 6 * (r + 1) * d ^ 3

end Lax12.AdmissibilityBound
