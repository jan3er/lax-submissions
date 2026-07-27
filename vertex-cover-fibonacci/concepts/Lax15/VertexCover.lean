import Lax13.RamComputes
import Lax11.GraphEncoding
import Lax11.VertexCover
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Data.Nat.Fib.Basic

/-!
---
title: Vertex cover in Fibonacci-of-k time
type: theorem
---
Whether a graph has a vertex cover of at most *k* vertices — a set
touching every edge — can be decided in Fibonacci-of-*k* times linear
time: there are one word RAM program and one constant *c* such that, at
every word length, given any graph in compressed sparse row form
followed by the single entry *k* as a word *x* for which *c*(|x|+*k*+1)
is at most `2 ^ w`, the program halts within *c*·`fib`(*k*+2)·(|x|+1)
steps and writes `1` if the graph has a vertex cover of at most *k*
vertices and `0` if it does not.

The bounded search tree of parameterized complexity branches on an
edge: one of its two endpoints lies in every cover, so trying both to
depth *k* gives 2^*k* branches. Branching on a *vertex* instead does
better. Take a vertex *v* that still has two or more uncovered edges on
it. Either *v* is in the cover, which costs one unit of budget, or it
is not, and then every one of its at least two remaining neighbours is,
which costs at least two. The search tree therefore obeys
*T*(*k*) ≤ *T*(*k*−1) + *T*(*k*−2), the Fibonacci recurrence, and its
size is `fib`(*k*+2) rather than 2^*k*. The case the branching rule
does not cover is the case that needs no search: if no vertex has two
uncovered edges on it, the uncovered edges form a matching, and the
answer is whether there are at most *k* of them.

This is the same problem, the same machine, the same input format and
the same shape of statement as *Vertex cover in explicit fixed-parameter
time* in *Algorithmic Experiments on a Random Access Machine*, with the
base of the exponential lowered: `fib`(*k*+2) is a fixed multiple of
φ^*k* with φ = (1+√5)/2 ≈ 1.618. That statement is not withdrawn or
weakened by this one — it is the textbook bound, proved, and it remains
true; this is the next rung of the same ladder, and 1.618 is not the
end of it either.

# Formalization notes

The parameter dependence is written into the bound. The usual
definition of fixed-parameter tractability hides it behind an
existential — "some computable *f* with running time *f*(*k*)·poly" —
and stating the theorem that way would quantify away exactly the number
this submission is about. The bound is the explicit term
`c * Nat.fib (k + 2) * (x.length + 1)`, so that the claim is falsifiable
at every single *k* rather than eventually, and improving the base is a
change of statement rather than a change of commentary.

The base is stated through mathlib's `Nat.fib` and not through a real
number. A bound of the form `c * φ ^ k * (x.length + 1)` would have to
round the irrational power somewhere, and every rounding is a small
statement about growth that the algorithm does not make; the search
tree really does have `fib`(*k*+2) leaves, and that count is what the
proof produces. It also keeps the surface free of any definition of its
own: `Nat.fib` is mathlib's, as is the vertex cover number, and the
encoding of the instance is imported from the earlier submission rather
than restated, so that the two bounds are claims about literally the
same inputs. Nothing here asserts that the golden ratio is the best
base — bases below 1.3 are known — and nothing here competes with those
analyses; the statement asks for what this branching rule gives and no
more.

The program and the constant are quantified ahead of the parameter and
ahead of the word length. The parameter is part of the input, so a
single program with a single constant serves every graph *and every k* —
the uniform notion of fixed-parameter tractability, which is a stronger
statement than one program per *k*. Quantifying the program before the
word length says the same thing about `w`: one program that works at
every word length that admits its input, rather than a family of
programs, one of which could hide an arbitrary amount of information in
its literals.

The instance word is the graph block with one entry appended. The
compressed sparse row block is self-delimiting — its own header
determines its length — so nothing needs to separate it from the
parameter, and the split of the word into the two parts is determined by
the word itself, not chosen. The parameter comes last so that the graph
block sits at the same offsets as in every other statement built on this
encoding.

The answer is stated through mathlib's vertex cover number, the infimum
of the sizes of all covers, so the output is a *function* of the graph
and the parameter and the concept surface adds no definition of its own:
`vertexCoverNum G ≤ k` and "some set of at most *k* vertices covers
every edge" agree by `vertexCoverNum_exists` and
`IsVertexCover.vertexCoverNum_le`. The decision problem is the honest
scope of the claim — a program producing a cover, or a smallest one, is
a different theorem with a different bound.

One constant does both jobs. An instance is admissible at word length
`w` when `c * (|x| + k + 1) ≤ 2 ^ w`, written out as an explicit
inequality against `2 ^ w` rather than through a logarithm. What that
condition has to cover is every number the machine holds: the entries of
the graph block, which are vertex numbers, offsets and the two header
numbers, all smaller than the block is long; the parameter, which is an
entry of the word and so must be a word, since a machine at word length
`w` sees its input reduced modulo `2 ^ w` and a parameter that is not the
parameter it was handed is not the parameter; and the bookkeeping of the
search, which is a stack of frames and a trail of marked vertices. The
frames each spend at least one unit of budget, so there are at most *k*
of them, and the trail lists distinct vertices, so it is shorter than the
block. So `|x| + k` bounds every value the run produces, and a constant
multiple of it is what has to fit.

The condition is deliberately *not* coupled to the running time.
`c * fib (k + 2) * (|x| + 1)` bounds the number of steps, not any number
the machine holds. Requiring `fib (k + 2)` to fit into a word would be
requiring the word length to be a constant multiple of the parameter,
and would exclude every instance with a large parameter on a small
machine — instances this algorithm decides perfectly well, only slowly.
The admissible set is therefore as large as the algorithm warrants, and
the claim on it is correspondingly stronger; a fitting condition chosen
for the convenience of the proof rather than for what the machine needs
would be a weaker theorem wearing the same bound. Note that this is one
place where lowering the base changes nothing: the admissible set is
character for character the one of the 2^*k* statement, so the improved
bound is claimed on exactly the same instances and not on a smaller
class.

The fitting condition is a condition on the admissible inputs and not a
hypothesis of the claim, because as a hypothesis it would be empty. A
graph with an edge has encodings of every length, since a block may list
a neighbour repeatedly, so no word length accommodates all encodings of
a fixed graph at once and "if every instance for `G` and `k` fits into a
word" would never be satisfied. Restricting the inputs instead says what
is meant: at every word length, every instance that fits is decided
within the bound.

Only encodings are admitted as inputs; the program may behave
arbitrarily on words that encode nothing, and on words too long for its
word length.
-/

namespace Lax15.VertexCover

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding Lax11.VertexCover

open Classical in
/-- **Vertex cover is decided in Fibonacci-of-`k` time**: there are one
program and one constant such that, at every word length `w`, on every
graph given in compressed sparse row form followed by the parameter `k`
as a word `x` for which `c * (x.length + k + 1)` is at most `2 ^ w`, the
program halts within `c * Nat.fib (k + 2) * (x.length + 1)` steps,
having written `1` if the graph has a vertex cover of at most `k`
vertices and `0` otherwise. The instance format is the one of
`Lax11.VertexCover.EncodesParamInstance`, so this is the same claim as
that submission's with the base of the exponential lowered from `2` to
the golden ratio. -/
axiom exists_fibTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ),
      ComputesInTime w p
        {x | EncodesParamInstance x n G k ∧ c * (x.length + k + 1) ≤ 2 ^ w}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * Nat.fib (k + 2) * (x.length + 1))

end Lax15.VertexCover
