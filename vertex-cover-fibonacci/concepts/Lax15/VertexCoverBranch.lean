import Lax13.RamComputes
import Lax11.GraphEncoding
import Lax11.VertexCover
import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
---
title: Vertex cover below the golden ratio
type: theorem
---
Whether a graph has a vertex cover of at most *k* vertices — a set
touching every edge — can be decided in `branchCount`(*k*) times linear
time, where `branchCount` is the leaf count of the search tree that
branches a budget *b* into *b*−1 and *b*−3: there are one word RAM
program and one constant *c* such that, at every word length, given any
graph in compressed sparse row form followed by the single entry *k* as
a word *x* for which *c*(|x|+*k*+1) is at most `2 ^ w`, the program
halts within *c*·`branchCount`(*k*)·(|x|+1) steps and writes `1` if the
graph has a vertex cover of at most *k* vertices and `0` if it does not.
`branchCount` grows as β^*k* for the real root β ≈ 1.4656 of
*x*³ = *x*² + 1.

The bound comes from a sharper branching rule. Branching on an *edge*
gives 2^*k*; branching on a *vertex* with two or more uncovered edges on
it gives the Fibonacci recurrence, and that is the statement *Vertex
cover in Fibonacci-of-k time* of this same submission, with base
φ ≈ 1.618. Branch on a vertex *v* with **three** distinct uncovered
neighbours instead. Either *v* is in the cover, which costs one unit of
budget, or it is not, and then all three or more of its remaining
neighbours are, which costs at least three. So the leaf count obeys
*T*(*b*) ≤ *T*(*b*−1) + *T*(*b*−3), and its base is the real root of
*x*³ = *x*² + 1.

The price of the sharper rule is a harder leaf. When no unmarked vertex
has three distinct uncovered neighbours, every one of them has at most
two, so the uncovered edges form a disjoint union of paths and cycles —
and a path or a cycle with *e* edges is covered by ⌈*e*/2⌉ vertices and
by no fewer. The leaf is therefore not a count of edges, as it is one
rung down, but a sum of ⌈*e*/2⌉ over the connected components of what is
left, computed by one breadth-first sweep. That the sum is exactly the
cover number of a graph of maximum degree two is the one new theorem
under this statement.

This sharpens *Vertex cover in Fibonacci-of-k time*, which sharpens the
2^*k* statement of *Algorithmic Experiments on a Random Access Machine*.
The three are the same problem, the same machine, the same input format
and the same shape of statement, with the base of the exponential
lowered twice: `branchCount`(*k*) ≤ `Nat.fib`(*k*+2) for every *k*, with
equality exactly at *k* ≤ 2 and strict inequality from *k* = 3 on
(1, 2, 3, 4, 6, 9, 13, 19, 28 against 1, 2, 3, 5, 8, 13, 21, 34, 55).
Neither earlier statement is withdrawn or weakened: both are proved and
both remain true. And 1.4656 is not the end of the ladder either —
bases below 1.3 are known, from branching rules with reduction rules in
front of them, and nothing here competes with those analyses.

# Formalization notes

The count is stated by its defining recurrence and not by a power. The
base β is the real root of *x*³ = *x*² + 1, an irrational number a
little above 1.4656, and a bound of the form `c * β ^ k * (x.length + 1)`
would have to round it somewhere. Every rounding is a small claim about
growth that the algorithm does not make: the search tree really does
have `branchCount`(*k*) leaves, exactly, and that count is what the
proof produces. The same reasoning put `Nat.fib` rather than φ^*k* into
the statement one rung down, and it is the same reasoning that writes
the parameter dependence into the bound at all rather than quantifying
it away behind "some computable *f*" — the claim is meant to be
falsifiable at every single *k*, and improving the base is then a change
of statement rather than a change of commentary. Here it forces one
definition onto the surface, since mathlib has no name for this
sequence; `Nat.fib` was mathlib's, and this is the one place where this
ladder has had to define something of its own.

The three initial values are the exact leaf counts, not a convention.
The algorithm branches whenever it finds a branching vertex and has any
budget at all, and the second child's budget is the remaining budget
less the residual degree, truncated at zero. So a budget of 0 admits no
branch and the tree is one leaf; a budget of 1 branches into two
children both measured at budget 0, giving 2; a budget of 2 branches
into a child at budget 1 and a child at budget 0, giving 3. Those are
`branchCount 0 = 1`, `branchCount 1 = 2`, `branchCount 2 = 3`, and the
recurrence `branchCount (b+3) = branchCount (b+2) + branchCount b` above
them. Rounding the initials up to a clean power would have been a
weaker theorem wearing a smaller-looking bound.

The admissible set is unchanged, character for character. An instance is
admissible at word length `w` when `c * (|x| + k + 1) ≤ 2 ^ w`, the same
inequality against `2 ^ w`, with the same reading: what has to fit into
a word is every number the machine holds — the entries of the graph
block, which are vertex numbers, offsets and the two header numbers, all
smaller than the block is long; the parameter, which is an entry of the
word, since a machine at word length `w` sees its input reduced modulo
`2 ^ w` and a parameter that is not the parameter it was handed is not
the parameter; and the bookkeeping of the search, a stack of frames and
a trail of marked vertices, both bounded by the block. The constant `c`
differs from the earlier statements' — it is bigger, and the driver has
two more arrays — but the *form* of the condition does not, so the
improved bound is claimed on exactly the same instances and not on a
smaller class. The condition is deliberately not coupled to the running
time: `branchCount k` counts leaves and is never a number the machine
holds, and requiring it to be a word would exclude every instance with a
large parameter on a small machine, which is exactly where the improved
base is interesting.

The fitting condition is a condition on the admissible inputs and not a
hypothesis of the claim, because as a hypothesis it would be empty: a
graph with an edge has encodings of every length, since a block may list
a neighbour repeatedly, so no word length accommodates all encodings of
a fixed graph at once.

The program and the constant are quantified ahead of the parameter and
ahead of the word length, so a single program with a single constant
serves every graph, every *k* and every *w* — the uniform notion of
fixed-parameter tractability, and a stronger statement than one program
per parameter or one program per word length.

The answer is stated through mathlib's vertex cover number, so the
output is a function of the graph and the parameter and the surface adds
no definition beyond the count. The decision problem is the honest scope
of the claim; a program producing a cover, or a smallest one, is a
different theorem with a different bound. Only encodings are admitted as
inputs; the program may behave arbitrarily on words that encode nothing,
and on words too long for its word length.
-/

namespace Lax15.VertexCoverBranch

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding Lax11.VertexCover

/-- Leaf count of the search tree that branches, at budget `b ≥ 3`,
into budgets `b − 1` and `b − 3`: the take-the-vertex child and the
take-its-three-plus-neighbours child. Grows as `β^k` for the real root
`β ≈ 1.4656` of `x³ = x² + 1`. The three initial values are the exact
leaf counts at budgets `0`, `1` and `2`, where the second child's budget
truncates at zero: `1`, `2`, `3`, and then `4, 6, 9, 13, 19, 28, …`. -/
def branchCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | (b + 3) => branchCount (b + 2) + branchCount b

open Classical in
/-- **Vertex cover is decided in `branchCount k` time**: there are one
program and one constant such that, at every word length `w`, on every
graph given in compressed sparse row form followed by the parameter `k`
as a word `x` for which `c * (x.length + k + 1)` is at most `2 ^ w`, the
program halts within `c * branchCount k * (x.length + 1)` steps, having
written `1` if the graph has a vertex cover of at most `k` vertices and
`0` otherwise. The instance format is the one of
`Lax11.VertexCover.EncodesParamInstance`, so this is the same claim as
that submission's, and as this submission's Fibonacci one, with the base
of the exponential lowered to the real root `β ≈ 1.4656` of
`x³ = x² + 1`. -/
axiom exists_branchTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ),
      ComputesInTime w p
        {x | EncodesParamInstance x n G k ∧ c * (x.length + k + 1) ≤ 2 ^ w}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * branchCount k * (x.length + 1))

end Lax15.VertexCoverBranch
