import Lax13.RamComputes
import Lax11.GraphEncoding
import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
---
title: Vertex cover in explicit fixed-parameter time
type: theorem
---
Whether a graph has a vertex cover of at most *k* vertices — a set
touching every edge — can be decided in time 2^*k* times linear: there
are one word RAM program and one constant *c* such that, at every word
length, given any graph in compressed sparse row form followed by the
single entry *k* as a word *x* for which *c*(|x|+*k*+1) is at most
`2 ^ w`, the program halts within *c*·2^*k*·(|x|+1) steps and writes
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

The program and the constant are quantified ahead of the parameter and
ahead of the word length. The parameter is part of the input, so a
single program with a single constant serves every graph *and every k* —
the uniform notion of fixed-parameter tractability, which is a stronger
statement than one program per *k*. Quantifying the program before the
word length says the same thing about `w`: one program that works at
every word length that admits its input, rather than a family of
programs, one of which could hide an arbitrary amount of information in
its literals. This is the opposite ordering from Courcelle's theorem in
this submission, where the sentence and the width bound precede the
program and must: there the constant provably cannot be uniform in
them. Here it can be, so the statement says so.

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

One constant does both jobs. An instance is admissible at word length
`w` when `c * (|x| + k + 1) ≤ 2 ^ w`, written out as an explicit
inequality against `2 ^ w` rather than through a logarithm. What that
condition has to cover is every number the machine holds: the entries
of the graph block, which are vertex numbers, offsets and the two
header numbers, all smaller than the block is long; the parameter,
which is an entry of the word and so must be a word, since a machine at
word length `w` sees its input reduced modulo `2 ^ w` and a parameter
that is not a word is not the parameter it was handed; and the depth of
the search stack, which never exceeds the parameter. So `|x| + k`
bounds every value the run produces, and a constant multiple of it is
what has to fit.

The condition is deliberately *not* coupled to the running time.
`c * 2 ^ k * (|x| + 1)` bounds the number of steps, not any number the
machine holds: the search tree has 2^*k* branches, but each of them
keeps a stack of at most *k* frames and vertex numbers below |x|.
Requiring `2 ^ k` to fit into a word would be requiring the word length
to be at least the parameter, and would exclude every instance with a
large parameter on a small machine — instances this algorithm decides
perfectly well, only slowly. The admissible set is therefore as large
as the algorithm warrants, and the claim on it is correspondingly
stronger; a fitting condition chosen for the convenience of the proof
rather than for what the machine needs would be a weaker theorem
wearing the same bound.

The fitting condition is a condition on the admissible inputs and not a
hypothesis of the claim, because as a hypothesis it would be empty. A
graph with an edge has encodings of every length, since a block may
list a neighbour repeatedly, so no word length accommodates all
encodings of a fixed graph at once and "if every instance for `G` and
`k` fits into a word" would never be satisfied. Restricting the inputs
instead says what is meant: at every word length, every instance that
fits is decided within the bound.

Only encodings are admitted as inputs; the program may behave
arbitrarily on words that encode nothing, and on words too long for its
word length.
-/

namespace Lax11.VertexCover

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding

/-- The word `x` presents the graph `G` on `n` vertices together with
the parameter `k`: a compressed sparse row block encoding `G`, followed
by the single entry `k`. -/
def EncodesParamInstance (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ g, x = g ++ [k] ∧ EncodesGraph g n G

open Classical in
/-- **Vertex cover is fixed-parameter tractable**, with the parameter
dependence explicit: there are one program and one constant such that,
at every word length `w`, on every graph given in compressed sparse row
form followed by the parameter `k` as a word `x` for which
`c * (x.length + k + 1)` is at most `2 ^ w`, the program halts within
`c * 2 ^ k * (x.length + 1)` steps, having written `1` if the graph has
a vertex cover of at most `k` vertices and `0` otherwise. -/
axiom exists_fptTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ),
      ComputesInTime w p
        {x | EncodesParamInstance x n G k ∧ c * (x.length + k + 1) ≤ 2 ^ w}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * 2 ^ k * (x.length + 1))

end Lax11.VertexCover
