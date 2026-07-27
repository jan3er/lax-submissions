import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
---
title: Monadic second-order logic on graphs
type: definition
---
A formula of monadic second-order logic over graphs is built from three
atoms — two vertices are adjacent, two vertices are equal, a vertex
belongs to a set — by negation, conjunction, and quantification over
vertices and over sets of vertices. A formula holds in a graph under an
assignment of vertices to its free vertex variables and of sets of
vertices to its free set variables, by the usual reading of the
connectives and the quantifiers. The quantifier rank of a formula is
the nesting depth of its quantifiers, counting both kinds.

# Formalization notes

Free variables are counted rather than named: `MSO r s` is the type of
formulas with `r` free vertex variables and `s` free set variables, and
a quantifier turns a formula with one more free variable of its kind
into a formula with one fewer. Satisfaction is therefore a total
function of a formula and two environments, `Fin r → Fin n` and
`Fin s → Set (Fin n)`, one entry per free variable: there is no partial
valuation, no default value for an unassigned variable, and no
well-formedness side condition. A sentence is a formula of `MSO 0 0`,
so being closed is a property of the type rather than a predicate to
check. The price is that variables are de Bruijn positions rather than
names; the alternative, named variables, needs capture-avoiding
substitution *inside the trusted definition*, which is a considerably
worse object to audit than an index.

Variables are levels, not indices: a quantifier extends the environment
at its *last* position (`Fin.snoc`), so the outermost bound variable of
a formula is `0` and the innermost is the last. Nothing in the
definition shifts an index.

Only negation, conjunction and existential quantification are
constructors. Disjunction, implication and universal quantification are
the usual abbreviations, written out where they are used: each of them
as a constructor would add a case to the definition of satisfaction and
buy nothing that is not already there.

The logic is monadic second-order logic in its MSO₁ form —
quantification over vertices and over *sets of vertices*, with
adjacency, equality and membership as the atoms. Sets of edges are not
quantified over. This is not a step on the way to a fuller version that
was left unfinished: MSO₁ and MSO₂, the logic that also quantifies over
edges and sets of edges, are matched to different width measures. MSO₂
model checking is tractable on classes of bounded treewidth and is *not*
tractable on classes of bounded cliquewidth unless the standard
complexity assumptions fail, so a development that proved the MSO₁
statement for cliquewidth and then claimed MSO₂ "by the same argument"
would be claiming something false. MSO₂ needs its own encoding — the
incidence graph, or edge-set variables in the type algebra — and is
deferred as one unit, logic and width measure together.
-/

namespace Lax11.Mso

/-- Formulas of monadic second-order logic over the adjacency
signature, with `r` free vertex variables and `s` free set variables.
Vertex variables are `Fin r`, set variables are `Fin s`, and a
quantifier binds the *new last* index. -/
inductive MSO : ℕ → ℕ → Type
  /-- The vertices `i` and `j` are adjacent. -/
  | adj {r s : ℕ} (i j : Fin r) : MSO r s
  /-- The vertices `i` and `j` are equal. -/
  | eq {r s : ℕ} (i j : Fin r) : MSO r s
  /-- The vertex `i` belongs to the set `X`. -/
  | mem {r s : ℕ} (i : Fin r) (X : Fin s) : MSO r s
  /-- Negation. -/
  | not {r s : ℕ} (φ : MSO r s) : MSO r s
  /-- Conjunction. -/
  | and {r s : ℕ} (φ ψ : MSO r s) : MSO r s
  /-- There is a vertex satisfying `φ`, bound at the last index. -/
  | exV {r s : ℕ} (φ : MSO (r + 1) s) : MSO r s
  /-- There is a set of vertices satisfying `φ`, bound at the last
  index. -/
  | exS {r s : ℕ} (φ : MSO r (s + 1)) : MSO r s

/-- The quantifier rank: the nesting depth of quantifiers, counting
both kinds. -/
def rank : {r s : ℕ} → MSO r s → ℕ
  | _, _, .adj _ _ => 0
  | _, _, .eq _ _ => 0
  | _, _, .mem _ _ => 0
  | _, _, .not φ => rank φ
  | _, _, .and φ ψ => max (rank φ) (rank ψ)
  | _, _, .exV φ => rank φ + 1
  | _, _, .exS φ => rank φ + 1

variable {n : ℕ}

/-- Satisfaction of a formula in the graph `G`, under a vertex
environment `m` and a set environment `A`. -/
def Sat (G : SimpleGraph (Fin n)) :
    {r s : ℕ} → (Fin r → Fin n) → (Fin s → Set (Fin n)) → MSO r s → Prop
  | _, _, m, _, .adj i j => G.Adj (m i) (m j)
  | _, _, m, _, .eq i j => m i = m j
  | _, _, m, A, .mem i X => m i ∈ A X
  | _, _, m, A, .not φ => ¬ Sat G m A φ
  | _, _, m, A, .and φ ψ => Sat G m A φ ∧ Sat G m A ψ
  | _, _, m, A, .exV φ => ∃ v : Fin n, Sat G (Fin.snoc m v) A φ
  | _, _, m, A, .exS φ => ∃ S : Set (Fin n), Sat G m (Fin.snoc A S) φ

end Lax11.Mso
