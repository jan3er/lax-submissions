import Lax2.IntervalDivision

/-!
---
title: Mixed cells of a divided Boolean matrix
---
For a Boolean matrix $M$ with rows $\mathrm{Fin}(n)$ and columns
$\mathrm{Fin}(m)$, a row division $R$ and a column division $C$ (both into $k$
parts) induce a $k \times k$ grid of cells: cell $(i,j)$ is the submatrix on
rows $\mathrm{part}(R,i)$ and columns $\mathrm{part}(C,j)$.

A cell is *vertical* when each of its columns is constant, *horizontal* when
each of its rows is constant, and *mixed* when it is neither vertical nor
horizontal.
-/

namespace Lax2.MixedCell

open Lax2.IntervalDivision

/-- A cell is vertical when each of its columns is constant on the row part. -/
def cellVertical {n m k : ℕ} (M : Fin n → Fin m → Bool)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ part R i → r₂ ∈ part R i →
    ∀ ⦃c : Fin m⦄, c ∈ part C j → M r₁ c = M r₂ c

/-- A cell is horizontal when each of its rows is constant on the column
part. -/
def cellHorizontal {n m k : ℕ} (M : Fin n → Fin m → Bool)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ part R i →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ part C j → c₂ ∈ part C j →
      M r c₁ = M r c₂

/-- A cell is mixed when it is neither vertical nor horizontal. -/
def cellMixed {n m k : ℕ} (M : Fin n → Fin m → Bool)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ¬ cellVertical M R C i j ∧ ¬ cellHorizontal M R C i j

end Lax2.MixedCell
