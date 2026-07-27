import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Compressed sparse row encoding of a graph
type: definition
---
A graph is handed to a word random access machine as a word of numbers
in compressed sparse row form, the adjacency-array format every
textbook assumes: the number *n* of vertices, the number *m* of edges, then
*n+1* offsets, then the target array. The target array lists, for each
vertex in turn, the neighbors of that vertex; the offsets say where
each vertex's block of neighbors begins, the first offset being 0 and
the last one the length of the target array. So the neighbors of vertex
*u* are the entries of the target array at the positions from the *u*-th
offset up to, but excluding, the *(u+1)*-st.

# Formalization notes

The encoding is deliberately dumb: it is exactly the input format,
with nothing precomputed that an algorithm would otherwise have to
compute. The word is required to have the right length, the offsets to
be nondecreasing with the right two endpoints, and every target entry
to be a vertex; beyond that the only condition is that each vertex's
block lists exactly its neighbors. In particular the blocks are not
required to be sorted and repetitions are not forbidden — the fewer
conditions the encoding imposes, the more inputs a claim about
programs reading it has to handle, so leaving them out strengthens
every such claim rather than weakening it. For the same reason `m` is
only the declared length of the target array (which is `2m`): it is at
least the number of edges, and equals it exactly when no block repeats
a neighbor. Nothing forces each edge to be listed from both of its
endpoints either — that is automatic, since adjacency in a simple
graph is symmetric.

Cells are read with `List.getD`, which returns `0` outside the word;
the length condition pins down the word completely, so this default
value is never reached at any position the other conditions constrain.
The conditions are bundled as a structure so that each one is a named
obligation a reader can check off separately.

Nothing here mentions the word length of the machine the encoding is
handed to. It does not have to: every entry of an encoding is a vertex
number, an offset into the target array, or one of the two header
numbers, and each of those is smaller than the length of the word
itself, so an encoding that a machine can address at all is one whose
entries fit into that machine's words. The condition that it does fit
belongs to the claims made about programs reading the encoding, and is
stated there, once, as an explicit inequality against `2 ^ w`.
-/

namespace Lax11.GraphEncoding

/-- The number of vertices declared by a word: its first entry. -/
def vertexCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of edges declared by a word: its second entry. -/
def edgeCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The `i`-th offset of a word: the `n+1` offsets follow the two
header entries. -/
def offset (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- The `j`-th entry of the target array of a word, which follows the
header and the offsets. -/
def target (x : List ℕ) (j : ℕ) : ℕ := x.getD (3 + vertexCount x + j) 0

/-- The word `x` is a compressed sparse row encoding of the graph `G`
on `n` vertices. -/
structure EncodesGraph (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) :
    Prop where
  /-- The word declares `n` vertices. -/
  vertexCount_eq : vertexCount x = n
  /-- The word consists of the two header entries, the `n+1` offsets,
  and a target array of length twice the declared number of edges. -/
  length_eq : x.length = 3 + n + 2 * edgeCount x
  /-- The block of the first vertex begins at the start of the target
  array. -/
  offset_zero : offset x 0 = 0
  /-- The block of the last vertex ends at the end of the target
  array. -/
  offset_last : offset x n = 2 * edgeCount x
  /-- The offsets are nondecreasing, so they cut the target array into
  one block per vertex. -/
  offset_mono : ∀ i < n, offset x i ≤ offset x (i + 1)
  /-- Every entry of the target array is a vertex. -/
  target_lt : ∀ j < 2 * edgeCount x, target x j < n
  /-- The block of a vertex lists exactly its neighbors. -/
  adj_iff : ∀ u v : Fin n, G.Adj u v ↔
    ∃ j, offset x u ≤ j ∧ j < offset x (u + 1) ∧ target x j = v

end Lax11.GraphEncoding
