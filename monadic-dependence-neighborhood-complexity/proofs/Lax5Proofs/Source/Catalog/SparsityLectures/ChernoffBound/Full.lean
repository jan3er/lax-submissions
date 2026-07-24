import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Lax5Proofs.Source.Catalog.SparsityLectures.ChernoffBound

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

/-! ## Bernoulli MGF bound

For X ∈ {0,1} a.s. with E[X] = p, the MGF satisfies
  mgf X μ t ≤ exp(p·(eᵗ − 1)).

Proof idea: mgf X μ t = E[eᵗˣ] = (1−p)·1 + p·eᵗ = 1 + p·(eᵗ−1) ≤ exp(p·(eᵗ−1))
using `Real.add_one_le_exp`. -/

lemma bernoulli_mgf_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℝ} (t : ℝ)
    (_hp : p ∈ Set.Icc 0 1)
    (hX_meas : Measurable X)
    (hX_bern : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1)
    (hX_mean : ∫ ω, X ω ∂μ = p) :
    mgf X μ t ≤ exp (p * (exp t - 1)) := by
  simp only [mgf]
  -- Rewrite exp(t*X ω) = 1 + X ω * (exp t - 1) a.e. using Bernoulli property
  have h_ae : (fun x => rexp (t * X x)) =ᵐ[μ] (fun ω => 1 + X ω * (rexp t - 1)) := by
    filter_upwards [hX_bern] with ω hω
    rcases hω with h | h <;> simp [h]
  rw [integral_congr_ae h_ae]
  -- X is integrable (bounded in {0,1} a.e., hence dominated by constant 1)
  have hX_int : Integrable X μ := by
    apply Integrable.mono (integrable_const (1 : ℝ)) hX_meas.aestronglyMeasurable
    filter_upwards [hX_bern] with ω hω
    rcases hω with h | h <;> simp [h]
  -- Split: ∫(1 + X*(exp t − 1)) = 1 + p*(exp t − 1)
  rw [integral_add (integrable_const _) (hX_int.mul_const _)]
  simp [integral_mul_const, hX_mean]
  -- Apply 1 + x ≤ exp x
  linarith [Real.add_one_le_exp (p * (rexp t - 1))]

/-! ## Real-analysis inequalities for tail optimization -/

/-- Upper tail inequality: (1+δ)·log(1+δ) − δ ≥ δ²/3 for δ ∈ (0,1).

Proof: Use 2δ/(δ+2) ≤ log(1+δ) from `le_log_one_add_of_nonneg`, multiply by (1+δ),
compute (1+δ)·2δ/(δ+2) − δ = δ²/(δ+2) ≥ δ²/3 since δ+2 ≤ 3. -/
lemma upper_log_inequality {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    δ ^ 2 / 3 ≤ (1 + δ) * log (1 + δ) - δ := by
  have hδ1 : 0 ≤ δ := hδ.1.le
  have h_denom : (0 : ℝ) < δ + 2 := by linarith
  have h_log : 2 * δ / (δ + 2) ≤ log (1 + δ) := Real.le_log_one_add_of_nonneg hδ1
  have h_mul : (1 + δ) * (2 * δ / (δ + 2)) ≤ (1 + δ) * log (1 + δ) :=
    mul_le_mul_of_nonneg_left h_log (by linarith)
  have h_simp : (1 + δ) * (2 * δ / (δ + 2)) - δ = δ ^ 2 / (δ + 2) := by
    field_simp; ring
  -- δ²/(δ+2) ≥ δ²/3 since δ+2 ≤ 3
  have h_bound : δ ^ 2 / 3 ≤ δ ^ 2 / (δ + 2) :=
    div_le_div_of_nonneg_left (sq_nonneg δ) h_denom (by linarith [hδ.2])
  linarith

/-- Lower tail inequality: δ + (1−δ)·log(1−δ) ≥ δ²/3 for δ ∈ (0,1).

Proof: Let f(x) = x + (1−x)·log(1−x) − x²/3. Show f(0) = 0 and f' ≥ 0 on (0,1)
via −log(1−x) ≥ 2x/(2−x) ≥ 2x/3 (using `le_log_one_add_of_nonneg`), so f is
monotone increasing, hence f(δ) ≥ f(0) = 0. -/
lemma lower_log_inequality {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    δ ^ 2 / 3 ≤ δ + (1 - δ) * log (1 - δ) := by
  suffices h : 0 ≤ δ + (1 - δ) * log (1 - δ) - δ ^ 2 / 3 by linarith
  -- Define f and show it is monotone increasing from f(0) = 0
  let f : ℝ → ℝ := fun x => x + (1 - x) * Real.log (1 - x) - x ^ 2 / 3
  -- HasDerivAt for f on (0,1): derivative = −log(1−x) − 2x/3
  have hd_at : ∀ x : ℝ, x ∈ Set.Ioo (0:ℝ) 1 →
      HasDerivAt f (-Real.log (1 - x) - 2 * x / 3) x := by
    intro x hx
    have h1mx_ne : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have hd_1mx : HasDerivAt (fun x => 1 - x) (-1) x := by
      simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    -- (1−x)·log(1−x) = −negMulLog(1−x), derivative = −log(1−x) − 1
    have hd_nml : HasDerivAt (fun x => (1 - x) * Real.log (1 - x))
        (-Real.log (1 - x) - 1) x := by
      have key : (fun x : ℝ => (1 - x) * Real.log (1 - x)) =
                 fun x => -Real.negMulLog (1 - x) := by
        ext y; simp [Real.negMulLog_def]
      rw [key]
      have h := ((Real.hasDerivAt_negMulLog h1mx_ne).comp x hd_1mx).neg
      convert h using 1; ring
    have hd_sq : HasDerivAt (fun x => x ^ 2 / 3) (2 * x / 3) x := by
      convert (hasDerivAt_pow 2 x).div_const (3 : ℝ) using 1
      push_cast; ring
    have hd_sum : HasDerivAt (fun x => x + (1 - x) * Real.log (1 - x))
        (1 + (-Real.log (1 - x) - 1)) x := (hasDerivAt_id x).add hd_nml
    have hd_f : HasDerivAt f (1 + (-Real.log (1 - x) - 1) - 2 * x / 3) x :=
      hd_sum.sub hd_sq
    convert hd_f using 1; ring
  -- f is monotone on [0,1]
  have hf_mono : MonotoneOn f (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · -- Continuity: f = x − negMulLog(1−x) − x²/3, all terms continuous
      have : f = fun x => x - Real.negMulLog (1 - x) - x ^ 2 / 3 := by
        ext x; simp [f, Real.negMulLog_def]
      rw [this]; fun_prop
    · -- Differentiability on interior (0,1)
      rw [interior_Icc]
      exact fun x hx => (hd_at x hx).differentiableAt.differentiableWithinAt
    · -- Derivative ≥ 0: −log(1−x) − 2x/3 ≥ 0
      rw [interior_Icc]
      intro x hx
      have h1mx_pos : 0 < 1 - x := by linarith [hx.2]
      have h2mx_pos : 0 < 2 - x := by linarith [hx.2]
      rw [(hd_at x hx).deriv]
      -- −log(1−x) > x ≥ 2x/3, using log(y) < y − 1 for y ≠ 1
      have h_log_strict : Real.log (1 - x) < -x := by
        have h1mx_ne1 : (1 : ℝ) - x ≠ 1 := by linarith [hx.1]
        linarith [Real.log_lt_sub_one_of_pos h1mx_pos h1mx_ne1]
      linarith [hx.1.le]
  -- f(0) = 0, so f(δ) ≥ 0
  have hf0 : f 0 = 0 := by simp [f, Real.log_one]
  have hfδ : f 0 ≤ f δ :=
    hf_mono (Set.left_mem_Icc.mpr (by linarith [hδ.2])) ⟨hδ.1.le, hδ.2.le⟩ hδ.1.le
  exact hf0 ▸ hfδ

/-! ## Tail bounds -/

/-- Upper tail: P(S ≥ (1+δ)μ) ≤ exp(−δ²μ/3).

Proof outline:
1. Apply `measure_ge_le_exp_mul_mgf` with t = log(1+δ) > 0
2. Factor mgf via `iIndepFun.mgf_sum`
3. Bound each factor via `bernoulli_mgf_le`
4. Simplify with t = log(1+δ) so exp(t)−1 = δ
5. Apply `upper_log_inequality` -/
lemma chernoff_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {p : ℝ}
    (hp : p ∈ Set.Icc 0 1)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_bern : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = p)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    μ.real {ω | (1 + δ) * (↑n * p) ≤ ∑ i : Fin n, X i ω} ≤
      exp (-(δ ^ 2 * (↑n * p) / 3)) := by
  have hδ1_pos : (0 : ℝ) < 1 + δ := by linarith [hδ.1]
  set t := Real.log (1 + δ) with ht_def
  have ht_pos : 0 < t := Real.log_pos (by linarith [hδ.1])
  have hexp_t : Real.exp t = 1 + δ := Real.exp_log hδ1_pos
  have hnp_nn : (0 : ℝ) ≤ ↑n * p := mul_nonneg (Nat.cast_nonneg _) hp.1
  -- Combine a.e. Bernoulli conditions into one
  have h_bern_ae : ∀ᵐ ω ∂μ, ∀ i : Fin n, X i ω = 0 ∨ X i ω = 1 :=
    Filter.eventually_all.mpr hX_bern
  -- Measurability of the sum S ω = ∑ Xi ω
  have h_meas_S : Measurable (fun ω => ∑ i : Fin n, X i ω) :=
    Finset.measurable_sum Finset.univ (fun i _ => hX_meas i)
  -- Integrability: S ω ≤ n a.e., so exp(t*S) ≤ exp(t*n)
  have h_int : Integrable (fun ω => Real.exp (t * ∑ i : Fin n, X i ω)) μ := by
    apply Integrable.mono' (integrable_const (Real.exp (t * ↑n)))
    · exact (measurable_const.mul h_meas_S).exp.aestronglyMeasurable
    · filter_upwards [h_bern_ae] with ω hω
      simp only [Real.norm_of_nonneg (Real.exp_nonneg _)]
      apply Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left _ ht_pos.le)
      calc ∑ i : Fin n, X i ω
          ≤ ∑ _i : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum (fun i _ => by rcases hω i with h | h <;> simp [h])
        _ = ↑n := by simp
  -- Chernoff-Markov step: μ.real {S ≥ ε} ≤ exp(-t·ε) · mgf(S)
  -- h_chernoff uses mgf (fun ω => ∑ Xi ω) μ t; bridge to mgf (∑ Xi) μ t via Finset.sum_apply
  have h_chernoff := ProbabilityTheory.measure_ge_le_exp_mul_mgf
      ((1 + δ) * (↑n * p)) ht_pos.le h_int
  have h_sum_fun_eq : (fun ω : Ω => ∑ i : Fin n, X i ω) = ∑ i : Fin n, X i := by
    ext ω; simp [Finset.sum_apply]
  rw [h_sum_fun_eq] at h_chernoff
  -- Factor: mgf(∑ Xi) = ∏ mgf(Xi)
  have h_mgf : mgf (∑ i : Fin n, X i) μ t = ∏ i : Fin n, mgf (X i) μ t :=
    hX_indep.mgf_sum (fun i => hX_meas i) Finset.univ
  -- Each factor ≤ exp(p * δ)  [since exp(t) - 1 = δ]
  have h_fac : ∀ i : Fin n, mgf (X i) μ t ≤ Real.exp (p * δ) := fun i =>
    calc mgf (X i) μ t
        ≤ Real.exp (p * (Real.exp t - 1)) :=
            bernoulli_mgf_le t hp (hX_meas i) (hX_bern i) (hX_mean i)
      _ = Real.exp (p * δ) := by rw [hexp_t]; congr 1; ring
  -- Product bound: ∏ mgf(Xi) ≤ exp(n*p*δ)
  have h_prod : ∏ i : Fin n, mgf (X i) μ t ≤ Real.exp (↑n * p * δ) :=
    calc ∏ i : Fin n, mgf (X i) μ t
        ≤ ∏ _i : Fin n, Real.exp (p * δ) :=
            Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => h_fac i)
      _ = Real.exp (↑n * p * δ) := by
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            rw [← Real.exp_nat_mul]; congr 1; ring
  -- Final estimate: combine and apply upper_log_inequality
  calc μ.real {ω | (1 + δ) * (↑n * p) ≤ ∑ i : Fin n, X i ω}
      ≤ Real.exp (-t * ((1 + δ) * (↑n * p))) * mgf (∑ i : Fin n, X i) μ t :=
          h_chernoff
    _ = Real.exp (-t * ((1 + δ) * (↑n * p))) * (∏ i : Fin n, mgf (X i) μ t) := by
          rw [h_mgf]
    _ ≤ Real.exp (-t * ((1 + δ) * (↑n * p))) * Real.exp (↑n * p * δ) :=
          mul_le_mul_of_nonneg_left h_prod (Real.exp_nonneg _)
    _ ≤ Real.exp (-(δ ^ 2 * (↑n * p) / 3)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h_ineq : δ ^ 2 / 3 ≤ (1 + δ) * t - δ := upper_log_inequality hδ
          nlinarith [mul_nonneg hnp_nn (by linarith : (0 : ℝ) ≤ (1 + δ) * t - δ - δ ^ 2 / 3)]

/-- Lower tail: P(S ≤ (1−δ)μ) ≤ exp(−δ²μ/3).

Proof outline:
1. Apply `measure_le_le_exp_mul_mgf` with t = log(1−δ) < 0
2. Factor mgf via `iIndepFun.mgf_sum`
3. Bound each factor via `bernoulli_mgf_le`
4. Simplify with t = log(1−δ) so exp(t)−1 = −δ
5. Apply `lower_log_inequality` -/
lemma chernoff_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {p : ℝ}
    (hp : p ∈ Set.Icc 0 1)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_bern : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = p)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    μ.real {ω | ∑ i : Fin n, X i ω ≤ (1 - δ) * (↑n * p)} ≤
      exp (-(δ ^ 2 * (↑n * p) / 3)) := by
  have h1mδ_pos : (0 : ℝ) < 1 - δ := by linarith [hδ.2]
  set t := Real.log (1 - δ) with ht_def
  have ht_neg : t < 0 := Real.log_neg h1mδ_pos (by linarith [hδ.1])
  have hexp_t : Real.exp t = 1 - δ := Real.exp_log h1mδ_pos
  have hnp_nn : (0 : ℝ) ≤ ↑n * p := mul_nonneg (Nat.cast_nonneg _) hp.1
  have h_bern_ae : ∀ᵐ ω ∂μ, ∀ i : Fin n, X i ω = 0 ∨ X i ω = 1 :=
    Filter.eventually_all.mpr hX_bern
  have h_meas_S : Measurable (fun ω => ∑ i : Fin n, X i ω) :=
    Finset.measurable_sum Finset.univ (fun i _ => hX_meas i)
  -- Integrability: t < 0 and S ≥ 0 a.e., so t*S ≤ 0, exp(t*S) ≤ 1
  have h_int : Integrable (fun ω => Real.exp (t * ∑ i : Fin n, X i ω)) μ := by
    apply Integrable.mono' (integrable_const 1)
    · exact (measurable_const.mul h_meas_S).exp.aestronglyMeasurable
    · filter_upwards [h_bern_ae] with ω hω
      simp only [Real.norm_of_nonneg (Real.exp_nonneg _)]
      rw [Real.exp_le_one_iff]
      apply mul_nonpos_of_nonpos_of_nonneg ht_neg.le
      exact Finset.sum_nonneg (fun i _ => by rcases hω i with h | h <;> simp [h])
  have h_chernoff := ProbabilityTheory.measure_le_le_exp_mul_mgf
      ((1 - δ) * (↑n * p)) ht_neg.le h_int
  have h_sum_fun_eq : (fun ω : Ω => ∑ i : Fin n, X i ω) = ∑ i : Fin n, X i := by
    ext ω; simp [Finset.sum_apply]
  rw [h_sum_fun_eq] at h_chernoff
  have h_mgf : mgf (∑ i : Fin n, X i) μ t = ∏ i : Fin n, mgf (X i) μ t :=
    hX_indep.mgf_sum (fun i => hX_meas i) Finset.univ
  -- Each factor ≤ exp(-p*δ)  [since exp(t) - 1 = -δ]
  have h_fac : ∀ i : Fin n, mgf (X i) μ t ≤ Real.exp (-(p * δ)) := fun i =>
    calc mgf (X i) μ t
        ≤ Real.exp (p * (Real.exp t - 1)) :=
            bernoulli_mgf_le t hp (hX_meas i) (hX_bern i) (hX_mean i)
      _ = Real.exp (-(p * δ)) := by rw [hexp_t]; congr 1; ring
  have h_prod : ∏ i : Fin n, mgf (X i) μ t ≤ Real.exp (-(↑n * p * δ)) :=
    calc ∏ i : Fin n, mgf (X i) μ t
        ≤ ∏ _i : Fin n, Real.exp (-(p * δ)) :=
            Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => h_fac i)
      _ = Real.exp (-(↑n * p * δ)) := by
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            rw [← Real.exp_nat_mul]; congr 1; ring
  calc μ.real {ω | ∑ i : Fin n, X i ω ≤ (1 - δ) * (↑n * p)}
      ≤ Real.exp (-t * ((1 - δ) * (↑n * p))) * mgf (∑ i : Fin n, X i) μ t :=
          h_chernoff
    _ = Real.exp (-t * ((1 - δ) * (↑n * p))) * (∏ i : Fin n, mgf (X i) μ t) := by
          rw [h_mgf]
    _ ≤ Real.exp (-t * ((1 - δ) * (↑n * p))) * Real.exp (-(↑n * p * δ)) :=
          mul_le_mul_of_nonneg_left h_prod (Real.exp_nonneg _)
    _ ≤ Real.exp (-(δ ^ 2 * (↑n * p) / 3)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h_ineq : δ ^ 2 / 3 ≤ δ + (1 - δ) * t := lower_log_inequality hδ
          nlinarith [mul_nonneg hnp_nn (by linarith : (0 : ℝ) ≤ δ + (1 - δ) * t - δ ^ 2 / 3)]

/-! ## Main theorem -/

/-- Theorem 3.3 (Chernoff's bound). For i.i.d. Bernoulli(p) random variables
X₁, ..., Xₙ with sum S and mean μ = np, for every δ ∈ (0, 1):
  P(|S - μ| ≥ δμ) ≤ 2 exp(-δ²μ/3).

Proof: split absolute value into upper/lower tails, union bound, apply
`chernoff_upper_tail` and `chernoff_lower_tail`. -/
theorem chernoffBound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {p : ℝ}
    (hp : p ∈ Set.Icc 0 1)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_bern : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = p)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    μ.real {ω | δ * (↑n * p) ≤ |(∑ i : Fin n, X i ω) - ↑n * p|} ≤
      2 * Real.exp (-(δ ^ 2 * (↑n * p) / 3)) := by
  -- Shorthand sets
  let A := {ω : Ω | (1 + δ) * (↑n * p) ≤ ∑ i : Fin n, X i ω}
  let B := {ω : Ω | ∑ i : Fin n, X i ω ≤ (1 - δ) * (↑n * p)}
  -- {|S − np| ≥ δnp} ⊆ A ∪ B
  have h_subset : {ω : Ω | δ * (↑n * p) ≤ |(∑ i : Fin n, X i ω) - ↑n * p|} ⊆ A ∪ B := by
    intro ω hω
    simp only [A, B, Set.mem_union, Set.mem_setOf_eq]
    rcases lt_or_ge ((∑ i : Fin n, X i ω) - ↑n * p) 0 with h | h
    · right
      have : δ * (↑n * p) ≤ -((∑ i : Fin n, X i ω) - ↑n * p) :=
        (abs_of_neg h) ▸ hω
      linarith
    · left
      have : δ * (↑n * p) ≤ (∑ i : Fin n, X i ω) - ↑n * p :=
        (abs_of_nonneg h) ▸ hω
      linarith
  -- Tail bounds
  have h_upper : μ.real A ≤ Real.exp (-(δ ^ 2 * (↑n * p) / 3)) :=
    chernoff_upper_tail hp hX_meas hX_indep hX_bern hX_mean hδ
  have h_lower : μ.real B ≤ Real.exp (-(δ ^ 2 * (↑n * p) / 3)) :=
    chernoff_lower_tail hp hX_meas hX_indep hX_bern hX_mean hδ
  -- Combine via union bound
  calc μ.real {ω | δ * (↑n * p) ≤ |(∑ i : Fin n, X i ω) - ↑n * p|}
      ≤ μ.real (A ∪ B) := measureReal_mono h_subset (measure_ne_top μ _)
    _ ≤ μ.real A + μ.real B := measureReal_union_le A B
    _ ≤ Real.exp (-(δ ^ 2 * (↑n * p) / 3)) + Real.exp (-(δ ^ 2 * (↑n * p) / 3)) :=
          add_le_add h_upper h_lower
    _ = 2 * Real.exp (-(δ ^ 2 * (↑n * p) / 3)) := by ring

end Lax5Proofs.Source.Catalog.SparsityLectures.ChernoffBound
