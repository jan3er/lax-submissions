import Lax2.MixedCell

/-!
---
title: Mixed minor of a Boolean matrix
---
A Boolean matrix $M$ *has a $k$-mixed minor* when it admits a row
$k$-division $R$ and a column $k$-division $C$ such that every one of the
$k \times k$ induced cells is mixed. The convention for $k = 0$ is that every
matrix has a $0$-mixed minor (witnessed by the empty family of cells).
-/

namespace Lax2.MixedMinor

open Lax2.IntervalDivision
open Lax2.MixedCell

/-- A matrix has a `k`-mixed minor if it admits row and column `k`-divisions
whose every cell is mixed. -/
def HasMixedMinor {n m : ℕ} (M : Fin n → Fin m → Bool) (k : ℕ) : Prop :=
  k = 0 ∨
    ∃ R : Division n k, ∃ C : Division m k,
      ∀ i j : Fin k, cellMixed M R C i j

end Lax2.MixedMinor
