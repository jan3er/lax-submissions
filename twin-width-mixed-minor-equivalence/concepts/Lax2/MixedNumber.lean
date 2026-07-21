import Mathlib.Data.Nat.Find
import Lax2.MixedMinor

/-!
---
title: Mixed number of a Boolean matrix
---
The *mixed number* of a Boolean matrix $M$ is the largest $k$ (at most
$\min(n,m)$) for which $M$ has a $k$-mixed minor:
$$\mathrm{matrixMixedNumber}(M) =
  \max\,\{\,k \le \min(n,m) : M \text{ has a } k\text{-mixed minor}\,\}.$$
The maximum is well defined because every matrix has a $0$-mixed minor;
it is expressed with `Nat.findGreatest`, which returns the largest number up
to the given bound satisfying the predicate, and $0$ if none does.
-/

namespace Lax2.MixedNumber

open Lax2.MixedMinor

noncomputable section

/-- The mixed number of a matrix: the largest order of a mixed minor, searched
up to the smaller matrix dimension. -/
def matrixMixedNumber {n m : ℕ} (M : Fin n → Fin m → Bool) : ℕ :=
  letI : DecidablePred (HasMixedMinor M) := Classical.decPred _
  Nat.findGreatest (HasMixedMinor M) (min n m)

end

end Lax2.MixedNumber
