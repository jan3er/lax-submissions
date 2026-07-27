import Lax11.RamComputes
import Lax11.GraphEncoding
import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
---
title: Vertex cover in explicit fixed-parameter time
type: theorem
---
Whether a graph has a vertex cover of at most *k* vertices — a set
touching every edge — can be decided in time 2^*k* times linear: there
are one random access machine program and one constant *c* such that,
given any graph in compressed sparse row form followed by the single
entry *k*, the program halts within *c*·2^*k*·(|x|+1) steps and writes
`1` if the graph has a vertex cover of at most *k* vertices and `0` if
it does not.

This is the opening result of parameterized complexity, by the
bounded search tree: every edge forces one of its two endpoints into
any cover, so trying both, to depth *k*, decides the question in 2^*k*
branches of linear work each.

# Formalization notes

The parameter dependence is written into the bound. The usual
definition of fixed-parameter tractability hides it behind an
existential — "some computable *f* with running time *f*(*k*)·poly" —
and stating the theorem that way would quantify away exactly the
number the algorithm is famous for. In the elementary style of this
submission the bound is the explicit term `c * 2 ^ k * (x.length + 1)`:
the 2^*k* is the size of the search tree, and the claim is falsifiable
at every single *k* rather than eventually. Nothing asserts the base 2
is best — covers within 1.3^*k* are known — and nothing here competes
with them; the statement asks for the textbook bound and no more.

The program and the constant are quantified ahead of the parameter.
The parameter is part of the input, so a single program with a single
constant serves every graph *and every k* — the uniform notion of
fixed-parameter tractability, which is a stronger statement than one
program per *k*. This is the opposite ordering from Courcelle's
theorem in this submission, where the sentence and the width bound
precede the program and must: there the constant provably cannot be
uniform in them. Here it can be, so the statement says so.

The instance word is the graph block with one entry appended. The
compressed sparse row block is self-delimiting — its own header
determines its length — so nothing needs to separate it from the
parameter, and the split of the word into the two parts is determined
by the word itself, not chosen. The parameter comes last so that the
graph block sits at the same offsets as in every other statement of
this submission.

The answer is stated through mathlib's vertex cover number, the
infimum of the sizes of all covers, so the output is a *function* of
the graph and the parameter and the concept surface adds no definition
of its own: `vertexCoverNum G ≤ k` and "some set of at most *k*
vertices covers every edge" agree by `vertexCoverNum_exists` and
`IsVertexCover.vertexCoverNum_le`. The decision problem is the honest
scope of the claim — a program producing a cover, or a smallest one,
is a different theorem with a different bound.

Only encodings are admitted as inputs; the program may behave
arbitrarily on words that encode nothing.
-/

namespace Lax11.VertexCover

open Lax11.Ram Lax11.RamComputes Lax11.GraphEncoding

/-- The word `x` presents the graph `G` on `n` vertices together with
the parameter `k`: a compressed sparse row block encoding `G`, followed
by the single entry `k`. -/
def EncodesInstance (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ g, x = g ++ [k] ∧ EncodesGraph g n G

open Classical in
/-- **Vertex cover is fixed-parameter tractable**, with the parameter
dependence explicit: there are one program and one constant such that,
on every graph given in compressed sparse row form followed by the
parameter `k`, the program halts within `c * 2 ^ k` times the length
of the input, having written `1` if the graph has a vertex cover of at
most `k` vertices and `0` otherwise. -/
axiom exists_fptTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ),
      ComputesInTime p {x | EncodesInstance x n G k}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * 2 ^ k * (x.length + 1))

end Lax11.VertexCover
