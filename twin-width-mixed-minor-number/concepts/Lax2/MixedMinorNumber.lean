import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Find

/-!
---
title: Mixed minor number
---
A $k$-division of a finite linearly ordered set partitions it into $k$
nonempty consecutive intervals. A row division and a column division split a
Boolean matrix into a grid of cells. A cell is *mixed* if it is neither
constant in every column nor constant in every row, and the matrix has a
$k$-mixed minor if some row and column $k$-divisions make all $k^2$ cells
mixed. Its mixed number is the largest such $k$.

An ordering of a finite simple graph's vertices turns its adjacency relation
into a Boolean matrix. The graph's mixed minor number is the minimum mixed
number of this matrix over all vertex orderings. The declarations below give
this complete chain of definitions. The Lean minimum uses the value $0$ as a
harmless fallback if the defining set is empty.
-/

namespace Lax2.MixedMinorNumber

/-- A division of `Fin n` into `k` nonempty, disjoint, covering, convex
parts in increasing order. -/
structure Division (n k : ℕ) where
  /-- The `i`-th part of the division. -/
  part : Fin k → Finset (Fin n)
  /-- Every part is nonempty. -/
  part_nonempty : ∀ i, (part i).Nonempty
  /-- Distinct parts are disjoint. -/
  part_disjoint : ∀ ⦃i j : Fin k⦄, i ≠ j → Disjoint (part i) (part j)
  /-- The parts cover the whole interval. -/
  part_cover : ∀ x : Fin n, ∃ i, x ∈ part i
  /-- Each part is convex in the natural order on `Fin n`. -/
  part_convex :
    ∀ (i : Fin k) ⦃a b c : Fin n⦄,
      a ∈ part i → c ∈ part i → a ≤ b → b ≤ c → b ∈ part i
  /-- Earlier-indexed parts lie strictly before later-indexed parts. -/
  part_ordered :
    ∀ ⦃i j : Fin k⦄, i < j →
      ∀ ⦃a b : Fin n⦄, a ∈ part i → b ∈ part j → a < b

/-- A matrix cell is vertical when each column is constant within the row
part. -/
def cellVertical {n m k : ℕ} (M : Fin n → Fin m → Bool)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R.part i → r₂ ∈ R.part i →
    ∀ ⦃c : Fin m⦄, c ∈ C.part j → M r₁ c = M r₂ c

/-- A matrix cell is horizontal when each row is constant within the column
part. -/
def cellHorizontal {n m k : ℕ} (M : Fin n → Fin m → Bool)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R.part i →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C.part j → c₂ ∈ C.part j →
      M r c₁ = M r c₂

/-- A matrix cell is mixed when it is neither vertical nor horizontal. -/
def cellMixed {n m k : ℕ} (M : Fin n → Fin m → Bool)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ¬ cellVertical M R C i j ∧ ¬ cellHorizontal M R C i j

/-- A matrix has a `k`-mixed minor if suitable row and column `k`-divisions
make every induced cell mixed. -/
def HasMixedMinor {n m : ℕ} (M : Fin n → Fin m → Bool) (k : ℕ) : Prop :=
  k = 0 ∨
    ∃ R : Division n k, ∃ C : Division m k,
      ∀ i j : Fin k, cellMixed M R C i j

/-- The largest order of a mixed minor of a Boolean matrix. -/
noncomputable def matrixMixedNumber {n m : ℕ}
    (M : Fin n → Fin m → Bool) : ℕ :=
  letI : DecidablePred (HasMixedMinor M) := Classical.decPred _
  Nat.findGreatest (HasMixedMinor M) (min n m)

/-- The Boolean adjacency matrix of a graph in a chosen vertex order. -/
noncomputable def orderedAdjacency {V : Type} {n : ℕ}
    (G : SimpleGraph V) (e : Fin n ≃ V) : Fin n → Fin n → Bool :=
  fun i j =>
    letI : Decidable (G.Adj (e i) (e j)) := Classical.propDecidable _
    decide (G.Adj (e i) (e j))

/-- The least natural satisfying `P`, or zero if no natural satisfies it.
This packages the minimization convention used for graph mixed minor
number. -/
noncomputable def leastNat (P : ℕ → Prop) : ℕ :=
  letI : Decidable (∃ n, P n) := Classical.propDecidable _
  letI : DecidablePred P := Classical.decPred P
  if h : ∃ n, P n then Nat.find h else 0

/-- The mixed minor number of a finite simple graph. -/
noncomputable def mixedMinorNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  leastNat fun k =>
    ∃ e : Fin (Fintype.card V) ≃ V,
      matrixMixedNumber (orderedAdjacency G e) = k

end Lax2.MixedMinorNumber
