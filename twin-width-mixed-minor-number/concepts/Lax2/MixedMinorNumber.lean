import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

/-!
---
title: Mixed minor number
type: definition
---
A $k$-division of $\operatorname{Fin} n$ partitions it into $k$ nonempty
consecutive intervals in increasing order. A row division and a column
division split a matrix into a grid of $k^2$ cells. A cell is vertical if
each of its columns is constant, horizontal if each of its rows is constant,
and mixed if it is neither. The matrix has a $k$-mixed minor if some pair of
row and column $k$-divisions makes all $k^2$ cells mixed, and its mixed
number is the largest such $k$.

An ordering of a finite simple graph's vertices turns its adjacency relation
into such a matrix. The mixed minor number of the graph is the least mixed
number of this matrix over all vertex orderings.

# Formalization notes

Disjointness and convexity of the parts of a `Division` follow from the
ordering and covering fields, so the structure does not carry them. Matrix
entries are truth values, so constancy of a cell's rows or columns is
propositional equivalence. A $k$-division of $\operatorname{Fin} n$ forces
$k \le n$, so the supremum in `matrixMixedNumber` ranges over a bounded set;
it takes the value $0$ if the matrix has no mixed minor at all. Vertex
orderings always exist, so the infimum in `mixedMinorNumber` ranges over a
nonempty set.
-/

namespace Lax2.MixedMinorNumber

/-- A division of `Fin n` into `k` nonempty consecutive intervals in
increasing order. Disjointness and convexity of the parts follow from
`part_ordered` and `part_cover`. -/
structure Division (n k : ℕ) where
  /-- The `i`-th part of the division. -/
  part : Fin k → Finset (Fin n)
  /-- Every part is nonempty. -/
  part_nonempty : ∀ i, (part i).Nonempty
  /-- The parts cover the whole interval. -/
  part_cover : ∀ x : Fin n, ∃ i, x ∈ part i
  /-- Earlier-indexed parts lie strictly before later-indexed parts. -/
  part_ordered :
    ∀ ⦃i j : Fin k⦄, i < j →
      ∀ ⦃a b : Fin n⦄, a ∈ part i → b ∈ part j → a < b

/-- A matrix cell is vertical when each column is constant within the row
part. -/
def cellVertical {n m k : ℕ} (M : Fin n → Fin m → Prop)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R.part i → r₂ ∈ R.part i →
    ∀ ⦃c : Fin m⦄, c ∈ C.part j → (M r₁ c ↔ M r₂ c)

/-- A matrix cell is horizontal when each row is constant within the column
part. -/
def cellHorizontal {n m k : ℕ} (M : Fin n → Fin m → Prop)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R.part i →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C.part j → c₂ ∈ C.part j →
      (M r c₁ ↔ M r c₂)

/-- A matrix cell is mixed when it is neither vertical nor horizontal. -/
def cellMixed {n m k : ℕ} (M : Fin n → Fin m → Prop)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ¬ cellVertical M R C i j ∧ ¬ cellHorizontal M R C i j

/-- A matrix has a `k`-mixed minor if suitable row and column `k`-divisions
make every induced cell mixed. -/
def HasMixedMinor {n m : ℕ} (M : Fin n → Fin m → Prop) (k : ℕ) : Prop :=
  ∃ R : Division n k, ∃ C : Division m k, ∀ i j : Fin k, cellMixed M R C i j

/-- The largest order of a mixed minor of a matrix. -/
noncomputable def matrixMixedNumber {n m : ℕ}
    (M : Fin n → Fin m → Prop) : ℕ :=
  sSup {k | HasMixedMinor M k}

/-- The adjacency matrix of a graph in a chosen vertex order. -/
def orderedAdjacency {V : Type} {n : ℕ}
    (G : SimpleGraph V) (e : Fin n ≃ V) : Fin n → Fin n → Prop :=
  fun i j => G.Adj (e i) (e j)

/-- The mixed minor number of a finite simple graph: the least mixed number
of its adjacency matrix over all vertex orderings. -/
noncomputable def mixedMinorNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf (Set.range fun e : Fin (Fintype.card V) ≃ V =>
    matrixMixedNumber (orderedAdjacency G e))

end Lax2.MixedMinorNumber
