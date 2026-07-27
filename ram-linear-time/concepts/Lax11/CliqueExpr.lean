import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: k-expressions, and the graphs of cliquewidth at most k
type: definition
---
A *k-expression* builds a graph from single vertices, each created with
one of *k* labels, by three operations: disjoint union of two
expressions; adding every edge between the vertices of one label class
and those of another; and relabelling, which moves one label class into
another. Evaluating an expression gives a vertex set, a graph on it,
and the *k* label classes it has arrived at. A graph has cliquewidth at
most *k* when some *k*-expression evaluates to it — that is the width
measure the theorem below is stated for, and an expression for the
graph is what the theorem takes as input.

An expression is *valid* when its leaves create pairwise distinct
vertices and every edge-adding operation joins two *different* classes;
it is an expression *for* a graph `G` when in addition its leaves
create all of `G`'s vertices and it evaluates to exactly `G`'s edges.

The operations of an expression are also numbered here, since the
numbers are what a machine reading an expression is handed: the
disjoint union is `0`, creating a vertex with label `l` is `1 + l`, and
the two binary operations occupy two further blocks of `k²` numbers
each, in which a pair of labels is read in base `k`.

# Formalization notes

Vertices are named globally, by the leaves: a leaf carries a vertex
name and the vertex set of a subexpression is the set of names of its
leaves. So no node of an expression builds a fresh structure that would
then have to be glued along an isomorphism — every subexpression
evaluates to a subset of the same fixed vertex set, and disjoint union
is literally union. That the two sides of a union really are disjoint
is then a consequence of the leaf names being distinct, which is what
validity requires; it is not built into the definition of the
evaluation, so the evaluation stays a plain structural recursion. What
does change from a node to its parent is the graph, since adding edges
adds them.

The label classes are sets of vertices rather than a colouring
function. That they are pairwise disjoint and cover the vertex set is a
theorem about valid expressions, not a clause of the definition — the
fewer conditions the definition imposes, the less there is to check
against a paper.

Everything computes: vertex sets and label classes are finite sets, the
well-formedness test is a Boolean, and the evaluated graph has a
decidable adjacency relation given by the same recursion, so a
hand-written expression can be evaluated and its edges compared with a
graph by computation rather than by hand.

The requirement that edge addition joins two different classes is part
of validity rather than of the constructor, so that an expression is
plain data with no proof carried inside it. Nothing in the mathematics
needs it; it is there because it is part of the standard definition of
cliquewidth, and leaving it out would silently claim the theorem for a
larger class of graphs than the name denotes. Relabelling tests for the
target class before the source class, so that relabelling a class into
itself is the identity rather than an operation that empties it.

The decoding of an operation number is total: numbers that name no
operation decode to the disjoint union. This is only so that decoding
is a function; the encoding of an instance requires every number in an
expression block to be the number of an operation, so no such number is
ever decoded.
-/

namespace Lax11.CliqueExpr

variable {n k : ℕ}

/-- A `k`-expression over the vertex names `Fin n`: a single labelled
vertex, disjoint union, edge addition between two label classes, or
relabelling one class into another. -/
inductive Expr (n k : ℕ) : Type
  /-- The vertex `v`, carrying label `l`. -/
  | leaf (v : Fin n) (l : Fin k)
  /-- Disjoint union `⊕`. -/
  | union (e₁ e₂ : Expr n k)
  /-- `η i j`: join every vertex of class `i` to every vertex of class `j`. -/
  | addEdges (i j : Fin k) (e : Expr n k)
  /-- `ρ i j`: move class `i` into class `j`. -/
  | relabel (i j : Fin k) (e : Expr n k)

/-- The vertex names created by the leaves, in order. -/
def leafIds : Expr n k → List (Fin n)
  | .leaf v _ => [v]
  | .union e₁ e₂ => leafIds e₁ ++ leafIds e₂
  | .addEdges _ _ e => leafIds e
  | .relabel _ _ e => leafIds e

/-- The vertex set of an expression. -/
def verts : Expr n k → Finset (Fin n)
  | .leaf v _ => {v}
  | .union e₁ e₂ => verts e₁ ∪ verts e₂
  | .addEdges _ _ e => verts e
  | .relabel _ _ e => verts e

/-- The label classes of an expression: `cls e i` is the set of vertices
of `e` currently carrying label `i`. -/
def cls : Expr n k → Fin k → Finset (Fin n)
  | .leaf v l, i => if i = l then {v} else ∅
  | .union e₁ e₂, i => cls e₁ i ∪ cls e₂ i
  | .addEdges _ _ e, i => cls e i
  | .relabel i j e, t => if t = j then cls e i ∪ cls e j else if t = i then ∅ else cls e t

/-- The graph an expression evaluates to. -/
def graph : Expr n k → SimpleGraph (Fin n)
  | .leaf _ _ => ⊥
  | .union e₁ e₂ => graph e₁ ⊔ graph e₂
  | .addEdges i j e => graph e ⊔ SimpleGraph.fromRel fun u v => u ∈ cls e i ∧ v ∈ cls e j
  | .relabel _ _ e => graph e

/-- The evaluated graph has a decidable adjacency relation, by the same
structural recursion. -/
instance decidableAdj : ∀ e : Expr n k, DecidableRel (graph e).Adj
  | .leaf _ _ => fun u v => show Decidable ((⊥ : SimpleGraph (Fin n)).Adj u v) from
      inferInstance
  | .union e₁ e₂ => fun u v => by
      letI := decidableAdj e₁
      letI := decidableAdj e₂
      exact show Decidable ((graph e₁ ⊔ graph e₂).Adj u v) from inferInstance
  | .addEdges i j e => fun u v => by
      letI := decidableAdj e
      exact show Decidable
        ((graph e ⊔ SimpleGraph.fromRel fun u v => u ∈ cls e i ∧ v ∈ cls e j).Adj u v) from
        inferInstance
  | .relabel _ _ e => fun u v => by
      letI := decidableAdj e
      exact show Decidable ((graph e).Adj u v) from inferInstance

/-- Well-formedness of the operations: `addEdges` joins two *different*
classes, the standard restriction on `η`. -/
def opsOk : Expr n k → Bool
  | .leaf _ _ => true
  | .union e₁ e₂ => opsOk e₁ && opsOk e₂
  | .addEdges i j e => (i != j) && opsOk e
  | .relabel _ _ e => opsOk e

/-- A valid expression: the leaves create pairwise distinct vertices —
which is what makes the two sides of every `⊕` disjoint — and the
operations are well formed. -/
structure Valid (e : Expr n k) : Prop where
  /-- No vertex name is created twice. -/
  nodup : (leafIds e).Nodup
  /-- Every `addEdges` joins two different classes. -/
  ops : opsOk e = true

/-- A `k`-expression *for* `G`: valid, and at the root it has created
every vertex and exactly the edges of `G`. -/
structure ValidFor (e : Expr n k) (G : SimpleGraph (Fin n)) : Prop extends Valid e where
  /-- The root creates every vertex. -/
  verts_eq : verts e = Finset.univ
  /-- The root evaluates to `G`. -/
  graph_eq : graph e = G

/-- The operation performed at a node of a `k`-expression. -/
inductive Op (k : ℕ) where
  /-- Disjoint union. -/
  | union
  /-- Create a vertex with label `l`. -/
  | leaf (l : Fin k)
  /-- `η i j`: join class `i` to class `j`. -/
  | eta (i j : Fin k)
  /-- `ρ i j`: move class `i` into class `j`. -/
  | rho (i j : Fin k)
  deriving DecidableEq

/-- The number naming an operation. The blocks are `union` (one code),
the leaves (`k` codes), the joins and the relabels (`k²` codes each,
the pair `(i, j)` read in base `k`). -/
def Op.code : Op k → ℕ
  | .union => 0
  | .leaf l => 1 + (l : ℕ)
  | .eta i j => 1 + k + ((i : ℕ) * k + (j : ℕ))
  | .rho i j => 1 + k + k * k + ((i : ℕ) * k + (j : ℕ))

/-- The size of the operation alphabet. -/
def opCard (k : ℕ) : ℕ := 1 + k + 2 * (k * k)

private theorem div_lt_sq {c k : ℕ} (h : c < k * k) : c / k < k :=
  Nat.div_lt_of_lt_mul h

private theorem pos_of_lt_sq {c k : ℕ} (h : c < k * k) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd h (by simp)
  · exact hk

private theorem mod_lt_sq {c k : ℕ} (h : c < k * k) : c % k < k :=
  Nat.mod_lt _ (pos_of_lt_sq h)

/-- The inverse of `Op.code`, total by sending every number that names
no operation to `union`. -/
def Op.decode (k c : ℕ) : Op k :=
  if c = 0 then .union
  else if h : c - 1 < k then .leaf ⟨c - 1, h⟩
  else if h : c - 1 - k < k * k then
    .eta ⟨(c - 1 - k) / k, div_lt_sq h⟩ ⟨(c - 1 - k) % k, mod_lt_sq h⟩
  else if h : c - 1 - k - k * k < k * k then
    .rho ⟨(c - 1 - k - k * k) / k, div_lt_sq h⟩ ⟨(c - 1 - k - k * k) % k, mod_lt_sq h⟩
  else .union

end Lax11.CliqueExpr
