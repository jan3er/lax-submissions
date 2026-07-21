import Mathlib.Data.Nat.Find

/-!
---
title: Least natural number satisfying a predicate
---
$\mathrm{leastNat}(P)$ is the least natural number satisfying the
predicate $P$, when such a number exists. If no natural number satisfies
$P$, it is defined to be $0$.
-/


namespace Lax1.LeastNatural

noncomputable section

/-- The least natural number satisfying a predicate, with fallback value `0`
when the predicate is never satisfied. -/
def leastNat (P : ℕ → Prop) : ℕ :=
  letI : Decidable (∃ n, P n) := Classical.propDecidable _
  letI : DecidablePred P := Classical.decPred P
  if h : ∃ n, P n then Nat.find h else 0

end

end Lax1.LeastNatural
