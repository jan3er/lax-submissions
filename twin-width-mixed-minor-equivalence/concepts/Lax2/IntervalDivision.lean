import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
---
title: Division of a finite interval
---
A *$k$-division* of $\mathrm{Fin}(n)$ partitions the linearly ordered index
set $\{0,\dots,n-1\}$ into $k$ consecutive nonempty intervals. An element of
$\mathrm{Division}(n,k)$ stores the $k$ parts as finite sets together with the
invariants: every part is nonempty, distinct parts are disjoint, the parts
cover all of $\mathrm{Fin}(n)$, each part is convex in the order, and parts
with smaller index lie strictly before parts with larger index.

$\mathrm{part}(D)$ returns the indexed family of parts of a division $D$.
-/

namespace Lax2.IntervalDivision

/-- A `k`-division of `Fin n`: `k` nonempty, disjoint, covering, convex parts
in increasing order. -/
def Division (n k : ℕ) : Type :=
  Σ part : Fin k → Finset (Fin n),
    PLift (
    (∀ i, (part i).Nonempty) ∧
    (∀ ⦃i j : Fin k⦄, i ≠ j → Disjoint (part i) (part j)) ∧
    (∀ x : Fin n, ∃ i, x ∈ part i) ∧
    (∀ (i : Fin k) ⦃a b c : Fin n⦄,
      a ∈ part i → c ∈ part i → a ≤ b → b ≤ c → b ∈ part i) ∧
    (∀ ⦃i j : Fin k⦄, i < j →
      ∀ ⦃a b : Fin n⦄, a ∈ part i → b ∈ part j → a < b))

/-- The parts of a division. -/
def part {n k : ℕ} (D : Division n k) : Fin k → Finset (Fin n) :=
  Sigma.fst D

end Lax2.IntervalDivision
