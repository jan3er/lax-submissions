import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
---
title: First-order logic on graphs
type: definition
---
A first-order formula over graphs is built from two atoms — two
vertices are adjacent, two vertices are equal — by negation,
conjunction, and quantification over vertices. A formula holds in a
graph under an assignment of vertices to its free variables, by the
usual reading of the connectives and the quantifier. The quantifier
rank of a formula is the nesting depth of its quantifiers.

This is the input logic of the model-checking problem this submission
is about: a statement of that problem is allowed to mention first-order
sentences and graphs, and nothing else. The distance logic of
`Lax3.DistFO` — first-order logic with distance atoms and local
quantification — is the logic the algorithm manipulates internally; it
is a different syntax with the same expressive power, introduced there
because it admits a finer rank measure. Keeping the two apart is the
point: a theorem stated for `FO` cannot be weakened by any convenience
built into `DistFO`.

# Formalization notes

Free variables are counted rather than named: `FO k` is the type of
formulas with `k` free variables, and the quantifier turns a formula
with one more free variable into a formula with one fewer. Satisfaction
is therefore a total function of a formula and an environment
`Fin k → Fin n`, one entry per free variable: there is no partial
valuation, no default value for an unassigned variable and no
well-formedness side condition. A sentence is a formula of `FO 0`, so
being closed is a property of the type rather than a predicate to
check. The price is that variables are de Bruijn positions rather than
names; the alternative, named variables, needs capture-avoiding
substitution *inside the trusted definition*, which is a considerably
worse object to audit than an index. This is the pattern of submission
Lax11's MSO concept, minus the set variables.

Variables are levels, not indices: the quantifier extends the
environment at its *last* position (`Fin.snoc`), so the outermost bound
variable of a formula is `0` and the innermost is the last. Nothing in
the definition shifts an index.

Only negation, conjunction and existential quantification are
constructors. Disjunction, implication and universal quantification are
the usual abbreviations, written out where they are used: each of them
as a constructor would add a case to the definition of satisfaction and
buy nothing that is not already there.

Graphs here are uncolored — the signature is one binary symmetric
relation. Colors are a device of the algorithm, not of the problem
statement: they record intermediate information (which vertices were
isolated, which distance profile a vertex has) that the input never
carries. The logic that has them is `Lax3.DistFO`, over the colored
graphs of `Lax3.ColoredGraphs`.
-/

namespace Lax3.FirstOrder

/-- Formulas of first-order logic over the adjacency signature, with
`k` free variables. Variables are `Fin k`, and the quantifier binds the
*new last* index. -/
inductive FO : ℕ → Type
  /-- The vertices `i` and `j` are adjacent. -/
  | adj {k : ℕ} (i j : Fin k) : FO k
  /-- The vertices `i` and `j` are equal. -/
  | eq {k : ℕ} (i j : Fin k) : FO k
  /-- Negation. -/
  | not {k : ℕ} (φ : FO k) : FO k
  /-- Conjunction. -/
  | and {k : ℕ} (φ ψ : FO k) : FO k
  /-- There is a vertex satisfying `φ`, bound at the last index. -/
  | ex {k : ℕ} (φ : FO (k + 1)) : FO k

/-- The quantifier rank: the nesting depth of quantifiers. -/
def rank : {k : ℕ} → FO k → ℕ
  | _, .adj _ _ => 0
  | _, .eq _ _ => 0
  | _, .not φ => rank φ
  | _, .and φ ψ => max (rank φ) (rank ψ)
  | _, .ex φ => rank φ + 1

variable {n : ℕ}

/-- Satisfaction of a formula in the graph `G` under the environment
`m`, which assigns a vertex to each free variable. -/
def Sat (G : SimpleGraph (Fin n)) : {k : ℕ} → (Fin k → Fin n) → FO k → Prop
  | _, m, .adj i j => G.Adj (m i) (m j)
  | _, m, .eq i j => m i = m j
  | _, m, .not φ => ¬ Sat G m φ
  | _, m, .and φ ψ => Sat G m φ ∧ Sat G m ψ
  | _, m, .ex φ => ∃ v : Fin n, Sat G (Fin.snoc m v) φ

end Lax3.FirstOrder
