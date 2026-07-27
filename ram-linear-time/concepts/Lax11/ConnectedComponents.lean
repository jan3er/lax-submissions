import Lax13.RamComputes
import Lax11.GraphEncoding
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Lattice

/-!
---
title: Connected components in linear time
type: theorem
---
The connected components of a graph can be computed in linear time.
Label every vertex by the least vertex of its connected component; then
there is one word RAM program and one constant *c* such that, at every
word length, given any graph in compressed sparse row form as a word
*x* for which *c*(|x|+1) is at most `2 ^ w`, the program halts within
*c*(|x|+1) steps with the labels of all vertices, in vertex order, as
its output.

# Formalization notes

Labelling a vertex by the least vertex reachable from it makes the
output a *function* of the graph, so the statement is about computing a
function and needs no convention for choosing representatives. Any
other canonical choice would do; what matters is that the answer is
determined, since a program that may return any of several correct
answers would be a weaker claim dressed up as this one.

The least vertex is the infimum of the set of numbers of vertices
reachable from `v`. That set contains `v` itself, so the value is a
genuine minimum and the convention `sInf ∅ = 0` for natural numbers is
never exercised. The labelling of the whole graph is the list of these
values in vertex order, so its length is the number of vertices.

The order of quantifiers is the content of the theorem: the program and
the constant come first, the graph next and the word length last, so
one program with one constant serves every graph at every word length.
Quantifying the program before the word length is what makes it an
algorithm rather than a family of them — a program chosen after `w`
could hide an arbitrary amount of information in its literals — and it
is the strong form of uniformity the model supports, since a program
can measure `w` for itself.

The bound is linear in the length of the input word — the number of
entries actually handed to the machine, namely `3 + n + 2m` — which is
the input size in the sense the model charges for. Reading the input
alone takes that many steps, so the bound is tight up to the constant.
The `+ 1` only keeps the bound from being vacuous on inputs of length
0, of which there are none valid.

One constant does both jobs. An encoding is admissible at word length
`w` when `c * (|x| + 1) ≤ 2 ^ w`, that is, when `2 ^ w` is at least
the very number of steps the claim allows; this is the "the word is
wide enough for the input" hypothesis of the word-RAM literature, written
out as an explicit inequality against `2 ^ w` rather than through a
logarithm. Nothing further need be asked of the entries: an encoding's
entries are vertex numbers, offsets and the two header numbers, all
smaller than its own length, so a word length that admits an encoding
also holds every number in it.

The fitting condition is a condition on the admissible inputs and not a
hypothesis of the claim, because as a hypothesis it would be empty. A
graph with an edge has encodings of every length, since a block may
list a neighbour repeatedly, so no word length accommodates all
encodings of a fixed graph at once and "if every encoding of `G` fits
into a word" would never be satisfied. Restricting the inputs instead
says what is meant: at every word length, every encoding that fits is
computed within the bound.

Only encodings of `G` are admitted as inputs; the program may behave
arbitrarily on words that encode nothing, and on words too long for its
word length.
-/

namespace Lax11.ConnectedComponents

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding

/-- The label of a vertex: the least vertex of its connected
component. -/
noncomputable def label {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  sInf (Fin.val '' {u : Fin n | G.Reachable u v})

/-- The component labelling of a graph: the labels of all vertices, in
vertex order. -/
noncomputable def ccLabels {n : ℕ} (G : SimpleGraph (Fin n)) : List ℕ :=
  List.ofFn (label G)

/-- Connected components can be computed in linear time on a word
random access machine: one program labels the vertices of every graph
given in compressed sparse row form by the least vertex of their
component, within a constant multiple of the length of the input, at
every word length `w` with that constant multiple at most `2 ^ w`. -/
axiom exists_linearTime_program_ccLabels :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ),
      ComputesInTime w p {x | EncodesGraph x n G ∧ c * (x.length + 1) ≤ 2 ^ w}
        (fun _ => ccLabels G) (fun x => c * (x.length + 1))

end Lax11.ConnectedComponents
