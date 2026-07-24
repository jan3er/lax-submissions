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
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · refine ⟨max K 0, le_max_right K 0, fun x hx => ?_⟩
    have hx1 : (1 : ℝ) ≤ x ^ δ := Real.one_le_rpow hx hδ.le
    calc K * (Real.log x + 2) ^ 0 = K := by ring
      _ ≤ max K 0 := le_max_left _ _
      _ ≤ max K 0 * x ^ δ :=
          le_mul_of_one_le_right (le_max_right _ _) hx1
  · set t : ℝ := δ / p with ht
    have htpos : 0 < t := by positivity
    set M : ℝ := 1 / t + 2 with hM
    have hM0 : 0 ≤ M := by positivity
    refine ⟨max K 0 * M ^ p, by positivity, fun x hx => ?_⟩
    have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
    have hxt1 : (1 : ℝ) ≤ x ^ t := Real.one_le_rpow hx htpos.le
    have hlog : Real.log x + 2 ≤ M * x ^ t := by
      have h1 : Real.log x ≤ x ^ t / t := Real.log_le_rpow_div hx0 htpos
      have heq : M * x ^ t = x ^ t / t + 2 * x ^ t := by rw [hM]; ring
      rw [heq]
      linarith
    have hbase0 : (0 : ℝ) ≤ Real.log x + 2 := by
      have := Real.log_nonneg hx
      linarith
    have hpow : (Real.log x + 2) ^ p ≤ (M * x ^ t) ^ p :=
      pow_le_pow_left₀ hbase0 hlog p
    have hxtp : (x ^ t) ^ p = x ^ δ := by
      rw [← Real.rpow_natCast (x ^ t) p, ← Real.rpow_mul hx0]
      congr 1
      rw [ht]
      field_simp
    calc K * (Real.log x + 2) ^ p
        ≤ max K 0 * (Real.log x + 2) ^ p :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max K 0 * (M * x ^ t) ^ p :=
          mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
      _ = max K 0 * M ^ p * (x ^ t) ^ p := by rw [mul_pow]; ring
      _ = max K 0 * M ^ p * x ^ δ := by rw [hxtp]

end Lax5Proofs.Asymptotics
