import Lax11.RamComputes
import Lax11.GraphEncoding
import Lax11.Mso
import Lax11.CliqueExpr

/-!
---
title: Courcelle's theorem on a random access machine
type: theorem
---
Every property of graphs expressible in monadic second-order logic can
be decided in linear time on graphs of bounded cliquewidth, given a
*k*-expression for the graph. Fix a sentence and a width bound *k*;
then there is one random access machine program and one constant *c*
such that, given any graph in compressed sparse row form followed by a
*k*-expression that evaluates to it, the program halts within
*c*(|x|+1) steps and writes `1` if the sentence holds in the graph and
`0` if it does not.

This is the Courcelle–Makowsky–Rotics form of Courcelle's theorem: the
width measure is cliquewidth and the logic is monadic second-order
logic with quantification over vertices and vertex sets, which is the
pairing the two notions are matched to.

The input word has two blocks. The first is the graph itself, in the
compressed sparse row form used everywhere in this submission. The
second is the *k*-expression, as a tree: the number of nodes, then one
number per node giving that node's parent, then one per node giving the
operation performed there, then one per node giving the vertex name it
creates. Children are numbered before their parents and the root is the
last node.

# Formalization notes

The expression is *input*, not something the program computes. Deciding
cliquewidth, or approximating it, is a different theorem with a
different proof, and folding it in here would silently claim it; the
statement is the honest one, "given a graph together with a
*k*-expression for it". This is the same choice a treewidth-based
statement makes when it takes a tree decomposition as input.

The expression block is a certificate, and it is required to be a
correct one: the encoding says that the arrays describe some valid
expression that evaluates to exactly the graph in the first block.
Since the two blocks describe the same graph, the statement is not
weakened by carrying both — the first block is what makes the sentence
`Sat G φ` refer to a graph, and the second is what makes the input
admissible. The arrays determine the expression completely, the vertex
names included, so the existential quantifier over expressions ranges
over at most one thing: the certificate is data in the word, not a
choice made about it.

The vertex-name array is part of the input even though the program
never reads it. Without it the second block would not be a
*k*-expression, only the shape of one, and a reader could not check
against the first block what the certificate claims. Its presence costs
nothing: it is one number per node, so it only lengthens the input, and
the bound is linear in that length.

The order of the quantifiers is the content of the theorem: the
sentence and the width bound come first, then the program and the
constant, then the graph. So one program serves all graphs of
cliquewidth at most *k*, with one constant, but both may depend — and
in every known proof do depend, in a way that grows faster than any
tower of exponentials in the sentence — on the sentence and the width.
Nothing here estimates the constant.

Only encodings of `G` are admitted as inputs; the program may behave
arbitrarily on words that encode nothing.
-/

namespace Lax11.Courcelle

open Lax11.Ram Lax11.RamComputes Lax11.GraphEncoding Lax11.Mso Lax11.CliqueExpr

/-- The number of nodes declared by an expression block: its first
entry. -/
def nodeCount (t : List ℕ) : ℕ := t.getD 0 0

/-- The parent of node `i`: the parents follow the header entry. -/
def parent (t : List ℕ) (i : ℕ) : ℕ := t.getD (1 + i) 0

/-- The operation performed at node `i`, as a number: the operations
follow the parents. -/
def opCode (t : List ℕ) (i : ℕ) : ℕ := t.getD (1 + nodeCount t + i) 0

/-- The vertex name created at node `i`, meaningful when the operation
there creates a vertex: the names follow the operations. -/
def vertexName (t : List ℕ) (i : ℕ) : ℕ := t.getD (1 + 2 * nodeCount t + i) 0

/-- The children of node `i`: the earlier nodes whose parent is `i`,
in increasing order. -/
def children (par : ℕ → ℕ) (i : ℕ) : List ℕ :=
  (List.range i).filter (fun c => par c == i)

/-- The word `t` is an expression block for a tree whose operations are
operations of `k`-expressions. The number of nodes is the block's own
first entry, so it is read off `t` rather than quantified over. -/
structure EncodesExprTree (t : List ℕ) (k : ℕ) : Prop where
  /-- There is at least one node: an expression has a root. -/
  pos : 1 ≤ nodeCount t
  /-- The block consists of the header entry and three arrays of one
  number per node. -/
  length_eq : t.length = 1 + 3 * nodeCount t
  /-- Every node but the last has a parent, which is a later node — so
  children are numbered before their parents and the root is the last
  node. -/
  parent_gt : ∀ i, i + 1 < nodeCount t → i < parent t i ∧ parent t i < nodeCount t
  /-- Every operation entry is the number of an operation. -/
  opCode_lt : ∀ i < nodeCount t, opCode t i < opCard k

/-- The node `i` of the tree given by the three arrays is the
expression `e`: the operation number at `i` is the one of `e`'s
outermost operation, the vertex name at `i` is the one `e` creates if
`e` is a leaf, and the children of `i` — which are listed in increasing
order — are the nodes of `e`'s immediate subexpressions, the left one
first. -/
def EncodesExpr {n k : ℕ} (par lab ids : ℕ → ℕ) : ℕ → Expr n k → Prop
  | i, .leaf v l => children par i = [] ∧ lab i = (Op.leaf l).code ∧ ids i = (v : ℕ)
  | i, .union e₁ e₂ => ∃ c₁ c₂, children par i = [c₁, c₂] ∧
      lab i = (Op.union : Op k).code ∧
      EncodesExpr par lab ids c₁ e₁ ∧ EncodesExpr par lab ids c₂ e₂
  | i, .addEdges a b e => ∃ c, children par i = [c] ∧
      lab i = (Op.eta a b).code ∧ EncodesExpr par lab ids c e
  | i, .relabel a b e => ∃ c, children par i = [c] ∧
      lab i = (Op.rho a b).code ∧ EncodesExpr par lab ids c e

/-- The word `x` presents the graph `G` on `n` vertices together with a
`k`-expression for it: a compressed sparse row block encoding `G`,
followed by an expression block whose arrays describe a valid
`k`-expression, rooted at its last node, that evaluates to `G`. -/
def EncodesInstance (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ (g t : List ℕ) (e : Expr n k),
    x = g ++ t ∧ EncodesGraph g n G ∧ EncodesExprTree t k ∧
      EncodesExpr (parent t) (opCode t) (vertexName t) (nodeCount t - 1) e ∧ ValidFor e G

open Classical in
/-- **Courcelle's theorem** (Courcelle–Makowsky–Rotics form): model
checking monadic second-order logic is linear time on a random access
machine, for graphs presented together with a `k`-expression. For every
sentence and every width bound there are one program and one constant
such that, on every graph given in compressed sparse row form followed
by a `k`-expression for it, the program halts within a constant
multiple of the length of the input, having written `1` if the sentence
holds in the graph and `0` otherwise. -/
axiom exists_linearTime_program_modelChecking :
    ∀ (φ : MSO 0 0) (k : ℕ),
      ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        ComputesInTime p {x | EncodesInstance x n G k}
          (fun _ => if Sat G Fin.elim0 Fin.elim0 φ then [1] else [0])
          (fun x => c * (x.length + 1))

end Lax11.Courcelle
