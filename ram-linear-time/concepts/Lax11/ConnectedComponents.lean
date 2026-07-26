import Lax11.RamComputes
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
there is one random access machine program and one constant *c* such
that, given any graph in compressed sparse row form as a word *x*, the
program halts within *c*(|x|+1) steps with the labels of all vertices,
in vertex order, as its output.

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
the constant come first and the graph afterwards, so one program serves
all graphs with one constant. The bound is linear in the length of the
input word — the number of entries actually handed to the machine,
namely `3 + n + 2m` — which is the input size in the sense the model
charges for. Reading the input alone takes that many steps, so the
bound is tight up to the constant. The `+ 1` only keeps the bound from
being vacuous on inputs of length 0, of which there are none valid.

Only encodings of `G` are admitted as inputs; the program may behave
arbitrarily on words that encode nothing.
-/

namespace Lax11.ConnectedComponents

open Lax11.Ram Lax11.RamComputes Lax11.GraphEncoding

/-- The label of a vertex: the least vertex of its connected
component. -/
noncomputable def label {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  sInf (Fin.val '' {u : Fin n | G.Reachable u v})

/-- The component labelling of a graph: the labels of all vertices, in
vertex order. -/
noncomputable def ccLabels {n : ℕ} (G : SimpleGraph (Fin n)) : List ℕ :=
  List.ofFn (label G)

/-- Connected components can be computed in linear time on a random
access machine: one program labels the vertices of every graph given in
compressed sparse row form by the least vertex of their component,
within a constant multiple of the length of the input. -/
axiom exists_linearTime_program_ccLabels :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ComputesInTime p {x | EncodesGraph x n G} (fun _ => ccLabels G)
        (fun x => c * (x.length + 1))

end Lax11.ConnectedComponents
