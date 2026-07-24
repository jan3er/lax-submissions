import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The one asymptotic fact the machinery consumes: polylogarithmic
factors are absorbed by an arbitrarily small polynomial gap, uniformly
on `[1, ∞)`. Combines `Real.log`-vs-`rpow` growth with continuity on a
compact initial segment.
-/

namespace Lax5Proofs.Asymptotics

/-- Polylog absorption: for every coefficient `K`, degree `p`, and
`δ > 0` there is `c ≥ 0` with `K (log x + 2)^p ≤ c x^δ` on `[1, ∞)`. -/
theorem exists_polylog_le_rpow (K : ℝ) (p : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, 1 ≤ x →
      K * (Real.log x + 2) ^ p ≤ c * x ^ δ := by
  sorry

end Lax5Proofs.Asymptotics
