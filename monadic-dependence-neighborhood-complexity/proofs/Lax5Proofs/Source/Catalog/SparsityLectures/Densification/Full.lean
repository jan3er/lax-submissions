import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ChernoffBound.Full
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor Real Filter Finset MeasureTheory ProbabilityTheory PMF NNReal

namespace Lax5Proofs.Source.Catalog.SparsityLectures.Densification

/-!
## Proof structure

The proof of `densification` follows Lemma 3.4 of the source, broken into:

1. `exists_good_pair` (probabilistic core): For large n, any graph with
   min degree ≥ n^ε has disjoint A, B ⊆ V with |A| ∈ [n^{1-ε}, 3n^{1-ε} log n],
   |B| ≥ n/2, and every b ∈ B having ≥ log n neighbors in A.
   Proof uses Chernoff bounds on Bernoulli sums (not yet in Mathlib).

2. `greedy_densify` (graph construction): Given (A, B) as above, the
   greedy process either finds K_{t+1} ≼₁ G for t ≥ log n, or builds a
   depth-1 minor G' on vertex set A with ≥ |B| edges.
   Each step: if N(b) ∩ A is a clique, use b to extend to a clique of size
   |N(b) ∩ A| + 1 ≥ log n + 1; else contract b onto some a ∈ N(b) ∩ A,
   adding an edge to G'[A]. Branch sets: {a} ∪ {contracted b's}, depth 1.

3. `edge_density_bound` (arithmetic): From n' = |A| ≤ 3n^{1-ε} log n
   and n/2 ≤ edges, deduce (n')^{1+ε+ε²} ≤ edges for large n.
   Proof: (n')^{1+ε+ε²} ≤ C · n^{1-ε³} · (log n)^{1+ε+ε²} ≤ n/2,
   where the last step uses n^{ε³} dominates (log n)^{1+ε+ε²}
   (from `isLittleO_log_rpow_rpow_atTop` with exponent ε³ > 0).
-/

/-- Under the product Bernoulli(p) measure on V → Bool,
the indicator 𝟙[ω v = true] has mean p. -/
private lemma pi_bernoulli_indicator_mean {V : Type} [DecidableEq V] [Fintype V]
    {p : ℝ≥0} (hp : p ≤ 1) (v : V) :
    ∫ (ω : V → Bool), (if ω v then (1 : ℝ) else 0)
      ∂(Measure.pi (fun _ : V => (bernoulli p hp).toMeasure)) = p.toReal := by
  -- Reduce to the single-factor Bernoulli integral via measure pushforward.
  have step1 : ∫ (ω : V → Bool), (if ω v then (1 : ℝ) else 0)
        ∂(Measure.pi (fun _ : V => (bernoulli p hp).toMeasure)) =
      ∫ (b : Bool), (if b then (1 : ℝ) else 0) ∂(bernoulli p hp).toMeasure := by
    conv_rhs => rw [← (measurePreserving_eval (μ := fun _ : V => (bernoulli p hp).toMeasure) v).map_eq]
    exact (integral_map_of_stronglyMeasurable
        (measurable_pi_apply (X := fun _ : V => Bool) v)
        (measurable_of_countable (fun b : Bool => if b then (1:ℝ) else 0)).stronglyMeasurable).symm
  rw [step1]
  simp_rw [show (fun b : Bool => if b then (1 : ℝ) else 0) = fun b => cond b 1 0 from
        funext fun b => by cases b <;> rfl]
  exact bernoulli_expectation hp

/-- Under the product Bernoulli(p) measure on V → Bool, the indicators 𝟙[ω v = true]
for v : V are independent random variables (V → Bool) → ℝ. -/
private lemma pi_bernoulli_iIndepFun {V : Type} [DecidableEq V] [Fintype V]
    {p : ℝ≥0} (hp : p ≤ 1) :
    iIndepFun (fun (v : V) (ω : V → Bool) => if ω v then (1 : ℝ) else 0)
      (Measure.pi (fun _ : V => (bernoulli p hp).toMeasure)) :=
  iIndepFun_pi (fun _ => (measurable_of_countable
      (fun b : Bool => if b then (1 : ℝ) else 0)).aemeasurable)

/-- **Step 1 (probabilistic core)**: For large n, a min-degree-n^ε graph has
a "good pair" (A, B): disjoint vertex subsets with |A| in [n^{1-ε}, 3n^{1-ε} log n],
|B| ≥ n/2, and every b ∈ B having ≥ log n neighbors in A.

Source proof: sample each vertex with probability p = 2 log n / n^ε independently.
For large n, p ∈ (0,1). Let A = sampled set, B = {v ∉ A | |N(v) ∩ A| ≥ log n}.
- Chernoff (upper + lower tail) on |A| = ∑_v Bernoulli(p): since μ = np = 2n^{1-ε} log n,
  P(|A| ∉ [n^{1-ε} log n, 3n^{1-ε} log n]) ≤ 2 exp(-n^{1-ε} log n / 6) → 0.
- For each v with deg v ≥ n^ε: μ_v = deg(v) · p ≥ 2 log n, so by Chernoff lower tail,
  P(|N(v) ∩ A| < log n) ≤ exp(-log n / 6) = n^{-1/6}.
- Since p = 2 log n / n^ε → 0, P(v ∈ A) = p → 0 too.
  So P(v ∉ B) ≤ p + n^{-1/6} → 0. For large n, P(v ∉ B) ≤ 1/6.
- By linearity of expectation: E[|V \ B|] ≤ n/6.
- By Markov: P(|B| ≥ n/2) ≥ 1 - P(|V \ B| ≥ n/2) ≥ 1 - 1/3 = 2/3.
- Both events (good A size, |B| ≥ n/2) hold simultaneously with probability ≥ 2/3 + 3/4 - 1 > 0.
- By the probabilistic method, a good (A, B) pair exists.

Uses `Lax5Proofs.Source.Catalog.SparsityLectures.ChernoffBound.chernoffBound` applied twice (once for |A|, once per vertex
for the neighbor count). The indicator variables X_v = 𝟙[ω v = true] are i.i.d. Bernoulli(p)
under `Measure.pi (fun _ : V => (PMF.bernoulli p_nnr hp_nnr).toMeasure)`, with independence
from `iIndepFun_pi` and mean from `bernoulli_expectation` + `measurePreserving_eval`. -/
private lemma exists_good_pair (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 2 / 3) :
    ∃ M : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      M ≤ Fintype.card V →
      (∀ v : V, (Fintype.card V : ℝ) ^ ε ≤ ↑(G.degree v)) →
      ∃ (A B : Finset V), Disjoint A B ∧
        (Fintype.card V : ℝ) ^ (1 - ε) ≤ ↑A.card ∧
        (↑A.card : ℝ) ≤ 3 * (Fintype.card V : ℝ) ^ (1 - ε) * log ↑(Fintype.card V) ∧
        (Fintype.card V : ℝ) / 2 ≤ ↑B.card ∧
        ∀ b ∈ B, log ↑(Fintype.card V) ≤ ↑(G.neighborFinset b ∩ A).card := by
  -- ======================== THRESHOLD SELECTION ========================
  -- We need n large enough that:
  -- (A) p_n := 2 * log n / n^ε is a valid probability in (0,1)
  -- (B) The Chernoff bound gives < 1/4 error for |A|
  -- (C) Bad-vertex probability p_n + n^{-1/6} ≤ 1/6
  --
  -- Asymptotic: log x = o(x^ε) from isLittleO_log_rpow_atTop
  -- -------
  -- (A) p_n ∈ (0,1) eventually:
  have hp_pos_ev : ∀ᶠ n : ℕ in Filter.atTop,
      0 < 2 * Real.log n / (n : ℝ) ^ ε := by
    rw [Filter.eventually_atTop]
    -- log n > 0 for n ≥ 3, and n^ε > 0 for n ≥ 1
    exact ⟨3, fun n hn => div_pos (by
      apply mul_pos two_pos
      apply Real.log_pos
      exact_mod_cast show 1 < n by omega) (Real.rpow_pos_of_pos (by exact_mod_cast show 0 < n by omega) ε)⟩
  have hp_lt1_ev : ∀ᶠ n : ℕ in Filter.atTop,
      2 * Real.log (n : ℝ) / (n : ℝ) ^ ε < 1 := by
    have h := (isLittleO_log_rpow_atTop hε_pos).tendsto_div_nhds_zero
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * Real.log (n : ℝ) / (n : ℝ) ^ ε)
        Filter.atTop (nhds 0) := by
      have := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      simp only [] at this
      have hcov : Filter.Tendsto (fun n : ℕ => 2 * (Real.log (n : ℝ) / (n : ℝ) ^ ε))
          Filter.atTop (nhds 0) := by
        simpa [mul_comm] using this.const_mul 2
      simpa [mul_div_assoc] using hcov
    exact h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  -- (B) Chernoff error < 1/4 eventually: 2·exp(−n^{1−ε}·log n/6) < 1/4
  have hchernoff_ev : ∀ᶠ n : ℕ in Filter.atTop,
      2 * Real.exp (-(((n : ℝ) ^ (1 - ε) * Real.log (n : ℝ)) / 6)) < 1 / 4 := by
    have h1e : 0 < 1 - ε := by linarith
    have h_rpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - ε)) Filter.atTop Filter.atTop :=
      (_root_.tendsto_rpow_atTop h1e).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h_logn_ev : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log (n : ℝ) :=
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
    filter_upwards [h_rpow.eventually_ge_atTop (18 * Real.log 2 + 1), h_logn_ev]
      with n h_large h_logn
    have h_nn : (0 : ℝ) ≤ (n : ℝ) ^ (1 - ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h_log8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    have h_lb : Real.log 8 < (n : ℝ) ^ (1 - ε) * Real.log n / 6 := by
      have h1 : (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε) * Real.log n :=
        le_mul_of_one_le_right h_nn h_logn
      linarith
    calc 2 * Real.exp (-((n : ℝ) ^ (1 - ε) * Real.log n / 6))
        < 2 * Real.exp (-Real.log 8) := by
          apply mul_lt_mul_of_pos_left _ two_pos
          exact Real.exp_lt_exp.mpr (by linarith)
      _ = 1 / 4 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8)]; norm_num
  -- (C) Bad vertex probability p + 2·n^{-1/6} < 1/6 eventually
  -- (Factor 2 accounts for the two-sided Chernoff bound applied per vertex)
  have hbad_ev : ∀ᶠ n : ℕ in Filter.atTop,
      2 * Real.log (n : ℝ) / (n : ℝ) ^ ε + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ)) < 1 / 6 := by
    have h_log_zero : Filter.Tendsto (fun n : ℕ => 2 * Real.log (n : ℝ) / (n : ℝ) ^ ε)
        Filter.atTop (nhds 0) := by
      have h := (isLittleO_log_rpow_atTop hε_pos).tendsto_div_nhds_zero
      have h2 := (h.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
      simp only [mul_zero] at h2; simpa [mul_div_assoc] using h2
    have h_pow_zero : Filter.Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (-(1 / 6 : ℝ)))
        Filter.atTop (nhds 0) := by
      have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa using this.const_mul 2
    have h_sum : Filter.Tendsto
        (fun n : ℕ => 2 * Real.log (n : ℝ) / (n : ℝ) ^ ε + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ)))
        Filter.atTop (nhds 0) := by simpa using h_log_zero.add h_pow_zero
    filter_upwards [h_sum.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))]
      with n hn; exact hn
  -- (D) log n ≥ 1 eventually (needed to relate n^{1-ε} lower bound to n·p/2)
  have h_logn_ev : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  -- Extract concrete M
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (hp_pos_ev.and (hp_lt1_ev.and (hchernoff_ev.and (hbad_ev.and h_logn_ev))))
  refine ⟨M, ?_⟩
  -- ======================== MAIN ARGUMENT ========================
  intro V inst_deq inst_fin G inst_adj hn hG_deg
  -- Set up notation
  set n := Fintype.card V with hn_def
  -- Unpack threshold conditions for this n
  obtain ⟨hp_pos, hp_lt1, hchernoff, hbad, h_logn⟩ := hM n hn
  -- Lift p to NNReal
  have hp_nn_pos : (0 : ℝ) ≤ 2 * Real.log n / (n : ℝ) ^ ε := hp_pos.le
  let p_nnr : ℝ≥0 := ⟨2 * Real.log n / (n : ℝ) ^ ε, hp_nn_pos⟩
  have hp_nnr : p_nnr ≤ 1 := by
    have : (p_nnr : ℝ) ≤ 1 := hp_lt1.le
    exact_mod_cast this
  -- ======================== PROBABILITY SPACE ========================
  -- Product Bernoulli(p) measure on V → Bool
  let μ := Measure.pi (fun _ : V => (bernoulli p_nnr hp_nnr).toMeasure)
  haveI : IsProbabilityMeasure μ := inferInstance
  -- Indicator variables: X_v ω = 𝟙[ω v = true]
  let X : V → (V → Bool) → ℝ := fun v ω => if ω v then 1 else 0
  -- Properties of X needed for Chernoff:
  have hX_meas : ∀ v : V, Measurable (X v) :=
    fun v => measurable_of_countable (X v)
  have hX_bern : ∀ v : V, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1 :=
    fun v => Filter.Eventually.of_forall (fun ω => by simp [X])
  have hX_mean : ∀ v : V, ∫ ω, X v ω ∂μ = p_nnr.toReal :=
    fun v => pi_bernoulli_indicator_mean hp_nnr v
  have hX_indep : iIndepFun X μ := pi_bernoulli_iIndepFun hp_nnr
  -- ======================== CHERNOFF BOUND FOR |A| ========================
  -- Use Fintype.equivFin to reindex V as Fin n
  let e : V ≃ Fin n := Fintype.equivFin V
  -- Reindexed variables: Y_i ω = X_{e.symm i} ω
  let Y : Fin n → (V → Bool) → ℝ := fun i => X (e.symm i)
  have hY_meas : ∀ i : Fin n, Measurable (Y i) := fun i => hX_meas (e.symm i)
  have hY_bern : ∀ i : Fin n, ∀ᵐ ω ∂μ, Y i ω = 0 ∨ Y i ω = 1 :=
    fun i => hX_bern (e.symm i)
  have hY_mean : ∀ i : Fin n, ∫ ω, Y i ω ∂μ = p_nnr.toReal := fun i => hX_mean (e.symm i)
  have hY_indep : iIndepFun Y μ :=
    hX_indep.precomp e.symm.injective
  -- p_nnr.toReal ∈ [0,1]
  have hp_icc : p_nnr.toReal ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨NNReal.coe_nonneg _, NNReal.coe_le_one.mpr hp_nnr⟩
  -- Chernoff bound: δ = 1/2
  have hδ : (1/2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  have h_chernoff_A :=
    Lax5Proofs.Source.Catalog.SparsityLectures.ChernoffBound.chernoffBound hp_icc hY_meas hY_indep hY_bern hY_mean hδ
  -- h_chernoff_A : μ.real {ω | 1/2 * (n * p) ≤ |∑_i Y i ω - n * p|} ≤ 2*exp(−(1/4*n*p/3))
  -- Note: ∑_i Y_i ω = ∑_v X_v ω = |{v | ω v}|
  -- Good event for |A|: |∑_i Y_i ω - n*p| < n*p/2, i.e., ∑_i Y_i ∈ [n*p/2, 3*n*p/2]
  -- ======================== GOOD PAIR HAS POSITIVE MEASURE ========================
  -- A good ω: A = {v | ω v}, B = {v | !ω v ∧ |N(v) ∩ A| ≥ log n}, with A and B in right range.
  let good_event : Set (V → Bool) := {ω |
    -- A is in the right size range
    (n : ℝ) ^ (1 - ε) ≤ (Finset.univ.filter (fun v => ω v)).card ∧
    ((Finset.univ.filter (fun v => ω v)).card : ℝ) ≤
        3 * (n : ℝ) ^ (1 - ε) * Real.log n ∧
    -- B (vertices not in A with enough neighbors in A) has size ≥ n/2
    (n : ℝ) / 2 ≤ (Finset.univ.filter (fun v =>
        !ω v ∧ Real.log n ≤
          (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card)).card}
  -- The good event has positive measure (the hard probabilistic argument)
  have h_good_pos : 0 < μ.real good_event := by
    -- ∑_i Y_i ω = |(Finset.univ.filter (fun v => ω v))| as reals
    have h_sum_card : ∀ ω : V → Bool,
        (∑ i : Fin n, Y i ω : ℝ) =
          (Finset.univ.filter (fun v : V => ω v)).card := fun ω => by
      simp only [Y, X]
      rw [show (∑ i : Fin n, if ω (e.symm i) = true then (1:ℝ) else 0) =
            ∑ v : V, if ω v = true then (1:ℝ) else 0 from
            Equiv.sum_comp e.symm (fun v => if ω v = true then (1:ℝ) else 0)]
      simp
    -- P(|∑_i Y_i - n*p| ≥ n*p/2) ≤ 2*exp(-n*p/12) < 1/4 (from h_chernoff_A + hchernoff)
    -- n*p = 2 * n^{1-ε} * log n, n*p/12 = n^{1-ε} * log n / 6
    -- h_chernoff_A gives: μ.real {ω | 1/2*(n*p) ≤ |∑_i Y_i ω - n*p|} ≤ 2*exp(-1/4*n*p/3)
    -- and 1/4 * n*p / 3 = n*p/12 = n^{1-ε}*log n/6
    -- Relate: {ω | good A size} ⊇ {ω | |∑_i Y_i ω - n*p| < n*p/2}
    -- So P(bad A) ≤ P(|∑_i Y_i - n*p| ≥ n*p/2) ≤ 2*exp(-n*p/12) < 1/4
    have h_bad_A : μ.real {ω | ¬(
        (n : ℝ) ^ (1 - ε) ≤ (Finset.univ.filter (fun v => ω v)).card ∧
        ((Finset.univ.filter (fun v => ω v)).card : ℝ) ≤
          3 * (n : ℝ) ^ (1 - ε) * Real.log n)} < 1 / 4 := by
      -- n > 0 (otherwise hp_pos : 0 < 0, contradiction)
      have hn_pos : (0 : ℝ) < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · simp only [h, Nat.cast_zero, Real.log_zero, mul_zero, zero_div] at hp_pos
          exact absurd hp_pos (lt_irrefl _)
        · exact Nat.cast_pos.mpr h
      have h_npe : 0 < (n : ℝ)^(1 - ε) := Real.rpow_pos_of_pos hn_pos _
      -- n * p = 2 * n^{1-ε} * log n  (since p = 2*log n / n^ε and n/n^ε = n^{1-ε})
      have hn_p : (n : ℝ) * (p_nnr : ℝ) = 2 * (n : ℝ)^(1-ε) * Real.log n := by
        show (n : ℝ) * (2 * Real.log n / (n : ℝ)^ε) = 2 * (n : ℝ)^(1-ε) * Real.log n
        have hdiv : (n : ℝ) / (n : ℝ)^ε = (n : ℝ)^(1-ε) := by
          rw [Real.rpow_sub hn_pos, Real.rpow_one]
        rw [show (n : ℝ) * (2 * Real.log n / (n : ℝ)^ε) =
              2 * ((n : ℝ) / (n : ℝ)^ε) * Real.log n from by ring, hdiv]
      -- {bad_A} ⊆ {Chernoff set}: if |A| ∉ [n^{1-ε}, 3n^{1-ε}logn] then |∑Yi - np| ≥ np/2
      have h_sub_A : {ω | ¬((n : ℝ)^(1-ε) ≤ ↑(Finset.univ.filter (fun v => ω v)).card ∧
              ↑(Finset.univ.filter (fun v => ω v)).card ≤ 3*(n:ℝ)^(1-ε)*Real.log n)} ⊆
          {ω | 1/2 * ((n:ℝ) * ↑p_nnr) ≤ |∑ i, Y i ω - (n:ℝ) * ↑p_nnr|} := by
        intro ω hω
        simp only [Set.mem_setOf_eq, not_and_or, not_le] at hω
        rw [← h_sum_card ω] at hω
        simp only [Set.mem_setOf_eq, hn_p]
        rcases hω with hlo | hhi
        · -- lower tail: ∑Yi < n^{1-ε} ≤ n^{1-ε}·logn = np/2
          have h_lt : ∑ i, Y i ω < (n:ℝ)^(1-ε) * Real.log n :=
            hlo.trans_le (le_mul_of_one_le_right h_npe.le h_logn)
          rw [abs_of_nonpos (by
            have := mul_nonneg h_npe.le (by linarith : (0:ℝ) ≤ Real.log n)
            linarith)]
          linarith
        · -- upper tail: ∑Yi > 3n^{1-ε}·logn = np/2 + np
          have h_prod : 0 < (n:ℝ)^(1-ε) * Real.log n := mul_pos h_npe (by linarith)
          rw [abs_of_pos (by linarith)]
          linarith
      -- Chain: μ(bad_A) ≤ μ(Chernoff) ≤ 2·exp(−np/12) = 2·exp(−n^{1-ε}·logn/6) < 1/4
      have h_exp_simp : (1/2:ℝ)^2 * ((n:ℝ) * ↑p_nnr) / 3 = (n:ℝ)^(1-ε) * Real.log n / 6 := by
        rw [hn_p]; ring
      calc μ.real {ω | ¬((n:ℝ)^(1-ε) ≤ ↑(Finset.univ.filter (fun v => ω v)).card ∧
              ↑(Finset.univ.filter (fun v => ω v)).card ≤ 3*(n:ℝ)^(1-ε)*Real.log n)}
          ≤ μ.real {ω | 1/2 * ((n:ℝ) * ↑p_nnr) ≤ |∑ i, Y i ω - (n:ℝ) * ↑p_nnr|} :=
              measureReal_mono h_sub_A
        _ ≤ 2 * Real.exp (-((1/2:ℝ)^2 * ((n:ℝ) * ↑p_nnr) / 3)) := h_chernoff_A
        _ = 2 * Real.exp (-((n:ℝ)^(1-ε) * Real.log n / 6)) := by
              rw [show (1/2:ℝ)^2 * ((n:ℝ) * ↑p_nnr) / 3 = (n:ℝ)^(1-ε) * Real.log n / 6 from
                    h_exp_simp]
        _ < 1/4 := hchernoff
    -- P(|B| < n/2) < 1/3 (Markov on |V\B| with E[|V\B|] ≤ n*(p + 2*n^{-1/6}) and hbad)
    have h_bad_B : μ.real {ω | ¬ ((n : ℝ) / 2 ≤
        (Finset.univ.filter (fun v =>
          !ω v ∧ Real.log n ≤
            (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card)).card)} < 1 / 3 := by
      -- n > 0 (from hp_pos)
      have hn_pos : (0 : ℝ) < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · simp only [h, Nat.cast_zero, Real.log_zero, mul_zero, zero_div] at hp_pos
          exact absurd hp_pos (lt_irrefl _)
        · exact Nat.cast_pos.mpr h
      have h_npe : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hn_pos _
      have h_npi : 0 < (n : ℝ) ^ (-(1 / 6 : ℝ)) := Real.rpow_pos_of_pos hn_pos _
      -- deg(v) * p ≥ 2 * log n for each v (from hG_deg and p = 2*log n/n^ε)
      have h_dp_lower : ∀ v : V, 2 * Real.log n ≤ (G.degree v : ℝ) * (p_nnr : ℝ) := fun v => by
        have hdeg := hG_deg v
        calc 2 * Real.log n
            = (n : ℝ) ^ ε * (p_nnr : ℝ) := by
              show 2 * Real.log n = (n : ℝ) ^ ε * (2 * Real.log n / (n : ℝ) ^ ε)
              field_simp
          _ ≤ (G.degree v : ℝ) * (p_nnr : ℝ) :=
              mul_le_mul_of_nonneg_right hdeg hp_pos.le
      -- Per-vertex Chernoff: P(|N(v) ∩ A| < log n) ≤ 2 * n^{-1/6}
      have h_chernoff_vtx : ∀ v : V,
          μ.real {ω | (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card <
              Real.log n} ≤ 2 * (n : ℝ) ^ (-(1 / 6 : ℝ)) := fun v => by
        -- Sum identity: ∑_j X(nbr_j(v)) ω = |N(v) ∩ A(ω)|
        have h_sum_v : ∀ ω : V → Bool,
            (∑ j : Fin (G.degree v),
              X ((Finset.equivFin (G.neighborFinset v)).symm j).val ω : ℝ) =
            (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card := fun ω => by
          simp only [X]
          rw [show G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u) =
              (G.neighborFinset v).filter (fun u => ω u) by ext; simp]
          rw [show (((G.neighborFinset v).filter (fun u => ω u)).card : ℝ) =
              ∑ u ∈ G.neighborFinset v, if ω u then (1 : ℝ) else 0 by
            push_cast [Finset.card_filter]
            apply Finset.sum_congr rfl; intro x _; simp]
          rw [← Finset.sum_coe_sort (G.neighborFinset v)]
          apply Fintype.sum_equiv (Finset.equivFin (G.neighborFinset v)).symm
          intro j; simp
        -- Independence of neighbor indicators via precomp
        have hg_inj : Function.Injective
            (fun j : Fin (G.degree v) =>
              ((Finset.equivFin (G.neighborFinset v)).symm j).val) := fun a b hab => by
          have h1 := Subtype.val_injective hab
          exact (Finset.equivFin (G.neighborFinset v)).symm.injective h1
        -- Apply Chernoff with δ = 1/2
        have h_chernoff_Z :=
          Lax5Proofs.Source.Catalog.SparsityLectures.ChernoffBound.chernoffBound hp_icc
            (fun j => hX_meas ((Finset.equivFin (G.neighborFinset v)).symm j).val)
            (hX_indep.precomp hg_inj)
            (fun j => hX_bern ((Finset.equivFin (G.neighborFinset v)).symm j).val)
            (fun j => hX_mean ((Finset.equivFin (G.neighborFinset v)).symm j).val)
            hδ
        -- Subset: {|N(v)∩A| < log n} ⊆ {Chernoff condition}
        have h_dp := h_dp_lower v
        have h_sub_v : {ω | (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card <
                Real.log n} ⊆
            {ω | 1 / 2 * ((G.degree v : ℝ) * ↑p_nnr) ≤
                |∑ j : Fin (G.degree v),
                  X ((Finset.equivFin (G.neighborFinset v)).symm j).val ω -
                  (G.degree v : ℝ) * ↑p_nnr|} := fun ω hω => by
          simp only [Set.mem_setOf_eq] at hω ⊢
          rw [h_sum_v]
          have h_neg : ((G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card : ℝ) -
              (G.degree v : ℝ) * ↑p_nnr < 0 := by linarith
          rw [abs_of_nonpos (le_of_lt h_neg)]
          linarith
        -- Bound: 2*exp(−deg*p/12) ≤ 2*n^{−1/6}  (since deg*p ≥ 2*log n)
        have h_exp_bound : 2 * Real.exp (-((1 / 2 : ℝ) ^ 2 * ((G.degree v : ℝ) * ↑p_nnr) / 3)) ≤
            2 * (n : ℝ) ^ (-(1 / 6 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          have h1 : (n : ℝ) ^ (-(1 / 6 : ℝ)) = Real.exp (-(Real.log n / 6)) := by
            rw [Real.rpow_neg (le_of_lt hn_pos), Real.rpow_def_of_pos hn_pos, ← Real.exp_neg]
            congr 1; ring
          rw [h1]
          apply Real.exp_le_exp_of_le
          linarith
        calc μ.real {ω | (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card <
                Real.log n}
            ≤ μ.real {ω | 1 / 2 * ((G.degree v : ℝ) * ↑p_nnr) ≤
                |∑ j : Fin (G.degree v),
                  X ((Finset.equivFin (G.neighborFinset v)).symm j).val ω -
                  (G.degree v : ℝ) * ↑p_nnr|} := measureReal_mono h_sub_v
          _ ≤ 2 * Real.exp (-((1 / 2 : ℝ) ^ 2 * ((G.degree v : ℝ) * ↑p_nnr) / 3)) :=
              h_chernoff_Z
          _ ≤ 2 * (n : ℝ) ^ (-(1 / 6 : ℝ)) := h_exp_bound
      -- P(v ∉ B) ≤ p + 2*n^{-1/6} via union bound
      have h_bad_v : ∀ v : V,
          μ.real {ω | ¬(!ω v ∧ Real.log n ≤
            (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card)} ≤
          (p_nnr : ℝ) + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ)) := fun v => by
        -- {v ∉ B} ⊆ {ω v = true} ∪ {|N(v)∩A| < log n}
        have h_sub : {ω | ¬(!ω v ∧ Real.log n ≤
              (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card)} ⊆
            {ω : V → Bool | ω v = true} ∪
            {ω | (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card <
              Real.log n} := fun ω hω => by
          simp only [Set.mem_setOf_eq, not_and_or, Bool.not_eq_true, not_le,
            Set.mem_union] at *
          rcases hω with h | h
          · left; cases hv : ω v
            · simp [hv] at h
            · rfl
          · right; exact h
        -- P(ω v = true) = p
        have h_p_v : μ.real {ω : V → Bool | ω v = true} = (p_nnr : ℝ) := by
          rw [← hX_mean v, ← integral_indicator_one MeasurableSet.of_discrete]
          congr 1; ext ω; simp [X, Set.indicator]
        linarith [(measureReal_mono h_sub (measure_ne_top μ _)).trans (measureReal_union_le _ _),
                  h_chernoff_vtx v, h_p_v.symm.le]
      -- Markov on f = |V\B| (count of bad vertices)
      let notB_pred : V → (V → Bool) → Prop := fun v ω =>
        ¬(!ω v ∧ Real.log n ≤
          (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card)
      let f : (V → Bool) → ℝ :=
        fun ω => (Finset.univ.filter (fun v => notB_pred v ω)).card
      -- {bad_B} ⊆ {f ≥ n/2}
      have h_sub_f : {ω | ¬ ((n : ℝ) / 2 ≤
            (Finset.univ.filter (fun v =>
              !ω v ∧ Real.log n ≤
                (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card)).card)} ⊆
          {ω | (n : ℝ) / 2 ≤ f ω} := fun ω hω => by
        simp only [Set.mem_setOf_eq, f, notB_pred] at *
        have h_sum : ((Finset.univ.filter (fun v => !ω v ∧ Real.log n ≤
              (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card)).card : ℝ) +
            ((Finset.univ.filter (fun v => ¬(!ω v ∧ Real.log n ≤
                (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card))).card : ℝ) =
            n := by
          have key := @Finset.card_filter_add_card_filter_not V Finset.univ
              (fun v => !ω v ∧ Real.log n ≤
                (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card) _ _
          rw [Finset.card_univ] at key
          exact_mod_cast key.trans hn_def.symm
        linarith
      -- Markov inequality
      have hf_nonneg : 0 ≤ᵐ[μ] f :=
        Filter.Eventually.of_forall (fun ω => by positivity)
      have h_markov :=
        mul_meas_ge_le_integral_of_nonneg hf_nonneg Integrable.of_finite ((n : ℝ) / 2)
      -- ∫ f ∂μ = ∑_v P(v ∉ B)
      have h_int : ∫ ω, f ω ∂μ = ∑ v : V, μ.real {ω | notB_pred v ω} := by
        conv_lhs =>
          arg 2; ext ω
          rw [show (f ω : ℝ) = ∑ v : V,
              ({ω | notB_pred v ω} : Set _).indicator (fun _ => (1 : ℝ)) ω from by
            simp [f, notB_pred, Set.indicator]]
        rw [integral_finset_sum Finset.univ (fun v _ => Integrable.of_finite)]
        congr 1; ext v
        exact MeasureTheory.integral_indicator_one MeasurableSet.of_discrete
      -- ∫ f ∂μ ≤ n * (p + 2*n^{-1/6})
      have h_int_bound : ∫ ω, f ω ∂μ ≤ n * ((p_nnr : ℝ) + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ))) := by
        rw [h_int]
        calc ∑ v : V, μ.real {ω | notB_pred v ω}
            ≤ ∑ v : V, ((p_nnr : ℝ) + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ))) :=
                Finset.sum_le_sum (fun v _ => h_bad_v v)
          _ = n * ((p_nnr : ℝ) + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ))) := by
                simp [Finset.sum_const, Finset.card_univ, hn_def]; ring
      -- Chain: P(bad_B) ≤ P(f ≥ n/2) ≤ E[f]/(n/2) ≤ 2*(p+2*n^{-1/6}) < 1/3
      have hn_half : 0 < (n : ℝ) / 2 := by linarith
      have h_Pf : μ.real {ω | (n : ℝ) / 2 ≤ f ω} ≤
          2 * ((p_nnr : ℝ) + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ))) := by
        have h_final : (n : ℝ) / 2 * μ.real {ω | (n : ℝ) / 2 ≤ f ω} ≤
            n * ((p_nnr : ℝ) + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ))) :=
          h_markov.trans h_int_bound
        rw [show (n : ℝ) * ((p_nnr : ℝ) + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ))) =
            (n : ℝ) / 2 * (2 * ((p_nnr : ℝ) + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ)))) from by ring]
            at h_final
        exact le_of_mul_le_mul_left h_final hn_half
      have h_p_val : (p_nnr : ℝ) = 2 * Real.log n / (n : ℝ) ^ ε := rfl
      have h_bound : 2 * ((p_nnr : ℝ) + 2 * (n : ℝ) ^ (-(1 / 6 : ℝ))) < 1 / 3 := by
        linarith
      linarith [measureReal_mono h_sub_f (measure_ne_top μ _)]
    -- Combine: P(good_event^c) ≤ P(bad_A) + P(bad_B) < 1/4 + 1/3 = 7/12 < 1
    -- So P(good_event) ≥ 5/12 > 0
    have h_bad_total : μ.real good_eventᶜ < 1 := by
      have h_sub : good_eventᶜ ⊆
          {ω | ¬((n : ℝ) ^ (1 - ε) ≤ (Finset.univ.filter (fun v => ω v)).card ∧
              (Finset.univ.filter (fun v => ω v)).card ≤
                3 * (n : ℝ) ^ (1 - ε) * Real.log n)} ∪
          {ω | ¬((n : ℝ) / 2 ≤ (Finset.univ.filter (fun v =>
              !ω v ∧ Real.log n ≤
                (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card)).card)} := by
        intro ω hω
        simp only [good_event, Set.mem_compl_iff, Set.mem_setOf_eq, not_and] at hω
        simp only [Set.mem_union, Set.mem_setOf_eq]
        by_cases hA : (n : ℝ) ^ (1 - ε) ≤ (Finset.univ.filter (fun v => ω v)).card ∧
            ((Finset.univ.filter (fun v => ω v)).card : ℝ) ≤ 3 * (n : ℝ) ^ (1 - ε) * Real.log n
        · exact Or.inr (hω hA.1 hA.2)
        · exact Or.inl hA
      have h_union : μ.real (good_eventᶜ) ≤
          μ.real {ω | ¬((n : ℝ) ^ (1 - ε) ≤ (Finset.univ.filter (fun v => ω v)).card ∧
              ((Finset.univ.filter (fun v => ω v)).card : ℝ) ≤
                3 * (n : ℝ) ^ (1 - ε) * Real.log n)} +
          μ.real {ω | ¬((n : ℝ) / 2 ≤ (Finset.univ.filter (fun v =>
              !ω v ∧ Real.log n ≤
                (G.neighborFinset v ∩ Finset.univ.filter (fun u => ω u)).card)).card)} :=
        (measureReal_mono h_sub).trans (measureReal_union_le _ _)
      linarith
    have h_meas : MeasurableSet good_event := MeasurableSet.of_discrete
    rw [probReal_compl_eq_one_sub h_meas] at h_bad_total
    linarith
  -- ======================== EXTRACT WITNESS ========================
  obtain ⟨ω, hω⟩ := nonempty_of_measureReal_ne_zero (ne_of_gt h_good_pos)
  obtain ⟨hA_lo, hA_hi, hB_lo⟩ := hω
  -- Define A = sampled vertices, B = non-sampled vertices with enough sampled neighbors
  let A : Finset V := Finset.univ.filter (fun v => ω v)
  let B : Finset V := Finset.univ.filter
    (fun v => !ω v ∧ Real.log n ≤ (G.neighborFinset v ∩ A).card)
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_⟩
  · -- Disjoint A B: A ⊆ {ω v = true}, B ⊆ {ω v = false}
    simp only [A, B, Finset.disjoint_filter]
    intro v _ hv_A hv_B
    simp [hv_A] at hv_B
  · -- |A| ≥ n^{1-ε}
    exact_mod_cast hA_lo
  · -- |A| ≤ 3 n^{1-ε} log n
    exact_mod_cast hA_hi
  · -- |B| ≥ n/2
    exact_mod_cast hB_lo
  · -- Every b ∈ B has ≥ log n neighbors in A (by definition of B)
    intro b hb
    exact_mod_cast ((Finset.mem_filter.mp hb).2).2

/-- **Auxiliary (minor model from assignment)**: Given an edge set `E` on `A` and an
assignment `f` from the processed subset `B'` of `B` to `A` — with each `b` adjacent to
`f b` in `G` — and a witness for every edge in `E` (some processed `b` whose assignment is
one endpoint and is adjacent to the other), this constructs a depth-1 `ShallowMinorModel`
of `fromEdgeSet E` in `G`.

Branch set of `a ∈ A`: `{a.val} ∪ {b.val | b ∈ B', f b = a}`.
Depth 1: each `b` is adjacent to its assigned vertex `f b = a` in `G`. -/
private noncomputable def minorModelFromAssignment
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B' : Finset V) (hAB' : Disjoint A B')
    (E : Finset (Sym2 {a : V // a ∈ A}))
    (f : {b : V // b ∈ B'} → {a : V // a ∈ A})
    (hf_adj : ∀ b : {b : V // b ∈ B'}, G.Adj (f b).val b.val)
    (hE_witness : ∀ (a a' : {a : V // a ∈ A}),
        (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 {a : V // a ∈ A}))).Adj a a' →
        ∃ b : {b : V // b ∈ B'},
          (f b = a ∧ G.Adj b.val a'.val) ∨ (f b = a' ∧ G.Adj b.val a.val)) :
    ShallowMinorModel
        (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 {a : V // a ∈ A}))) G 1 where
  branchSet a := {v : V | v = a.val ∨ ∃ b : {b : V // b ∈ B'}, f b = a ∧ v = b.val}
  center a := a.val
  center_mem a := Set.mem_setOf.mpr (Or.inl rfl)
  branchDisjoint := by
    intro a₁ a₂ ha
    apply Set.disjoint_left.mpr
    intro v hv₁ hv₂
    simp only [Set.mem_setOf_eq] at hv₁ hv₂
    have hd := Finset.disjoint_left.mp hAB'
    rcases hv₁ with rfl | ⟨b, hfb, rfl⟩ <;> rcases hv₂ with h | ⟨b', hfb', h'⟩
    · exact ha (Subtype.ext h)
    · exact hd a₁.property (h' ▸ b'.property)
    · exact hd a₂.property (by rw [← h]; exact b.property)
    · have hbb' : b = b' := Subtype.ext h'
      have hfb_eq : f b = a₂ := by rw [hbb']; exact hfb'
      exact ha (hfb.symm.trans hfb_eq)
  branchRadius := by
    intro a v hv
    simp only [Set.mem_setOf_eq] at hv
    rcases hv with rfl | ⟨b, hfb, rfl⟩
    · exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp,
        fun w hw => by
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          exact hw ▸ Set.mem_setOf.mpr (Or.inl rfl)⟩
    · have hadj : G.Adj a.val b.val := hfb ▸ hf_adj b
      refine ⟨hadj.toWalk, SimpleGraph.Walk.IsPath.of_adj hadj,
        by simp [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.length_cons],
        fun w hw => ?_⟩
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
                 SimpleGraph.Walk.support_nil, List.mem_cons,
                 List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl
      · exact Set.mem_setOf.mpr (Or.inl rfl)
      · exact Set.mem_setOf.mpr (Or.inr ⟨b, hfb, rfl⟩)
  branchEdge := by
    intro a₁ a₂ hadj
    obtain ⟨b, hb | hb⟩ := hE_witness a₁ a₂ hadj
    · exact ⟨b.val, Set.mem_setOf.mpr (Or.inr ⟨b, hb.1, rfl⟩),
             a₂.val, Set.mem_setOf.mpr (Or.inl rfl), hb.2⟩
    · exact ⟨a₁.val, Set.mem_setOf.mpr (Or.inl rfl),
             b.val, Set.mem_setOf.mpr (Or.inr ⟨b, hb.1, rfl⟩), hb.2.symm⟩

/-- Given a depth-1 minor model, a clique `S` in the source graph, and a vertex `b₀`
adjacent in `G` to the center of every element of `S` and not in any branch set,
we get `K_{|S|+1} ≼₁ G`. -/
private noncomputable def clique_extension_minor
    {V W : Type} [DecidableEq V] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : ShallowMinorModel H G 1)
    (S : Finset W)
    (hS_clique : ∀ a₁ ∈ S, ∀ a₂ ∈ S, a₁ ≠ a₂ → H.Adj a₁ a₂)
    (b₀ : V)
    (hb₀_adj : ∀ a ∈ S, G.Adj b₀ (M.center a))
    (hb₀_not_branch : ∀ w : W, b₀ ∉ M.branchSet w) :
    ShallowMinorModel (SimpleGraph.completeGraph (Fin (S.card + 1))) G 1 :=
  let φ := S.equivFin
  let toW : Fin S.card → W := fun i => (φ.symm i).val
  have htoW_inj : Function.Injective toW := fun i j h =>
    φ.symm.injective (Subtype.val_injective h)
  have htoW_mem : ∀ i, toW i ∈ S := fun i => (φ.symm i).property
  { branchSet := fun i =>
      if h : (i : ℕ) < S.card then M.branchSet (toW ⟨i, h⟩) else {b₀}
    center := fun i =>
      if h : (i : ℕ) < S.card then M.center (toW ⟨i, h⟩) else b₀
    center_mem := by
      intro i; split
      · exact M.center_mem _
      · exact rfl
    branchDisjoint := by
      intro i j hij
      by_cases hi : (i : ℕ) < S.card <;> by_cases hj : (j : ℕ) < S.card
      · rw [dif_pos hi, dif_pos hj]
        exact M.branchDisjoint _ _ (fun heq => hij (Fin.ext (by
          exact_mod_cast congrArg Fin.val (htoW_inj heq))))
      · rw [dif_pos hi, dif_neg hj]
        exact Set.disjoint_singleton_right.mpr (hb₀_not_branch _)
      · rw [dif_neg hi, dif_pos hj]
        exact Set.disjoint_singleton_left.mpr (hb₀_not_branch _)
      · exact absurd (Fin.ext (by omega)) hij
    branchRadius := by
      intro i x hx
      by_cases h : (i : ℕ) < S.card
      · rw [dif_pos h] at hx; rw [dif_pos h]; rw [dif_pos h]
        exact M.branchRadius _ x hx
      · rw [dif_neg h] at hx; rw [dif_neg h]; rw [dif_neg h]
        rw [Set.mem_singleton_iff.mp hx]
        exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by norm_num,
          fun w hw => by
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
            exact hw⟩
    branchEdge := by
      intro i j hij
      simp only [SimpleGraph.top_adj] at hij
      by_cases hi : (i : ℕ) < S.card <;> by_cases hj : (j : ℕ) < S.card
      · rw [dif_pos hi, dif_pos hj]
        exact M.branchEdge _ _ (hS_clique _ (htoW_mem _) _ (htoW_mem _)
          (fun heq => hij (Fin.ext (by exact_mod_cast congrArg Fin.val (htoW_inj heq)))))
      · rw [dif_pos hi, dif_neg hj]
        exact ⟨M.center _, M.center_mem _, b₀, rfl, (hb₀_adj _ (htoW_mem _)).symm⟩
      · rw [dif_neg hi, dif_pos hj]
        exact ⟨b₀, rfl, M.center _, M.center_mem _, hb₀_adj _ (htoW_mem _)⟩
      · exact absurd (Fin.ext (by omega)) hij }

/-- **Step 2 (greedy edges or clique)**: Core induction — either find `K_{t+1} ≼₁ G`
for `t ≥ log n`, or find an edge set `E` with `|B| ≤ |E|`, an assignment `f : B → A`
with `G.Adj (f b) b`, and witnesses for the minor-model construction. -/
private lemma greedy_edges_or_clique
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hAB : Disjoint A B)
    (hB_nbrs : ∀ b ∈ B, log ↑(Fintype.card V) ≤ ↑(G.neighborFinset b ∩ A).card) :
    (∃ t : ℕ, log ↑(Fintype.card V) ≤ ↑t ∧
        IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G 1) ∨
    (∃ (E : Finset (Sym2 {a : V // a ∈ A}))
       (f : {b : V // b ∈ B} → {a : V // a ∈ A}),
       B.card ≤ E.card ∧
       (∀ e ∈ E, ¬e.IsDiag) ∧
       (∀ b : {b : V // b ∈ B}, G.Adj (f b).val b.val) ∧
       ∀ (a a' : {a : V // a ∈ A}),
         (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 {a : V // a ∈ A}))).Adj a a' →
         ∃ b : {b : V // b ∈ B},
           (f b = a ∧ G.Adj b.val a'.val) ∨ (f b = a' ∧ G.Adj b.val a.val)) := by
  classical
  refine Finset.induction_on B ?_ ?_ hAB hB_nbrs
  · intro hAB_empty hB_empty
    refine Or.inr ?_
    refine ⟨∅, (fun b => nomatch b.property), ?_⟩
    simp
  · intro b₀ B₀ hb₀ ih hAB_ins hB_ins
    have hAB₀ : Disjoint A B₀ := by
      rw [Finset.disjoint_left] at hAB_ins ⊢
      intro a haA haB₀
      exact hAB_ins haA (Finset.mem_insert_of_mem haB₀)
    have hB₀_nbrs : ∀ b ∈ B₀, log ↑(Fintype.card V) ≤ ↑(G.neighborFinset b ∩ A).card := by
      intro b hb
      exact hB_ins b (Finset.mem_insert_of_mem hb)
    rcases ih hAB₀ hB₀_nbrs with
      hclique | ⟨E₀, f₀, hcard₀, hnd₀, hf₀_adj, hwitness₀⟩
    · exact Or.inl hclique
    · let S : Finset {a : V // a ∈ A} :=
        (G.neighborFinset b₀ ∩ A).subtype (fun a => a ∈ A)
      have hS_ge : log ↑(Fintype.card V) ≤ ↑S.card := by
        have hS_card : S.card = (G.neighborFinset b₀ ∩ A).card := by
          unfold S
          rw [Finset.card_subtype]
          apply congrArg Finset.card
          ext a
          simp [Finset.mem_inter]
        rw [hS_card]
        exact hB_ins b₀ (Finset.mem_insert_self b₀ B₀)
      by_cases hnew :
          ∃ a₁ ∈ S, ∃ a₂ ∈ S, a₁ ≠ a₂ ∧ s(a₁, a₂) ∉ E₀
      · rcases hnew with ⟨a₁, ha₁S, a₂, ha₂S, ha12, hnotE₀⟩
        let E : Finset (Sym2 {a : V // a ∈ A}) := insert (s(a₁, a₂)) E₀
        let f : {b : V // b ∈ insert b₀ B₀} → {a : V // a ∈ A} := fun b =>
          if h : b.val = b₀ then a₁ else f₀ ⟨b.val, (Finset.mem_insert.mp b.property).resolve_left h⟩
        refine Or.inr ⟨E, f, ?_, ?_, ?_, ?_⟩
        · calc
            (insert b₀ B₀).card = B₀.card + 1 := by simp [hb₀]
            _ ≤ E₀.card + 1 := Nat.succ_le_succ hcard₀
            _ = E.card := by simp [E, hnotE₀]
        · intro e he
          rcases Finset.mem_insert.mp he with rfl | he₀
          · simpa [Sym2.mk_isDiag_iff] using ha12
          · exact hnd₀ e he₀
        · intro b
          by_cases hb : b.val = b₀
          · rw [show f b = a₁ by simp [f, hb]]
            have ha₁_mem : a₁.val ∈ G.neighborFinset b₀ ∩ A := by
              simpa [S] using ha₁S
            simpa [hb] using ((G.mem_neighborFinset b₀ a₁.val).mp (Finset.mem_inter.mp ha₁_mem).1).symm
          · rw [show f b = f₀ ⟨b.val, (Finset.mem_insert.mp b.property).resolve_left hb⟩ by
                simp [f, hb]]
            exact hf₀_adj ⟨b.val, (Finset.mem_insert.mp b.property).resolve_left hb⟩
        · intro a a' hadj
          rw [SimpleGraph.fromEdgeSet_adj] at hadj
          rcases Finset.mem_insert.mp hadj.1 with hE | hE
          · have hs : s(a, a') = s(a₁, a₂) := hE
            let b : {b : V // b ∈ insert b₀ B₀} := ⟨b₀, Finset.mem_insert_self b₀ B₀⟩
            have ha₁_mem : a₁.val ∈ G.neighborFinset b₀ ∩ A := by
              simpa [S] using ha₁S
            have ha₂_mem : a₂.val ∈ G.neighborFinset b₀ ∩ A := by
              simpa [S] using ha₂S
            have ha₁_adj : G.Adj b₀ a₁.val :=
              (G.mem_neighborFinset b₀ a₁.val).mp (Finset.mem_inter.mp ha₁_mem).1
            have ha₂_adj : G.Adj b₀ a₂.val :=
              (G.mem_neighborFinset b₀ a₂.val).mp (Finset.mem_inter.mp ha₂_mem).1
            rcases Sym2.eq_iff.mp hs with h | h
            · refine ⟨b, Or.inl ?_⟩
              rcases h with ⟨rfl, rfl⟩
              exact ⟨by simp [b, f], ha₂_adj⟩
            · refine ⟨b, Or.inr ?_⟩
              rcases h with ⟨rfl, rfl⟩
              exact ⟨by simp [b, f], ha₂_adj⟩
          · obtain ⟨b, hb | hb⟩ := hwitness₀ a a' ((SimpleGraph.fromEdgeSet_adj _).2 ⟨hE, hadj.2⟩)
            · refine ⟨⟨b.val, Finset.mem_insert_of_mem b.property⟩, Or.inl ?_⟩
              refine ⟨?_, hb.2⟩
              have hbne : b.val ≠ b₀ := by
                intro hEq
                exact hb₀ (hEq ▸ b.property)
              simp [f, hbne, hb.1]
            · refine ⟨⟨b.val, Finset.mem_insert_of_mem b.property⟩, Or.inr ?_⟩
              refine ⟨?_, hb.2⟩
              have hbne : b.val ≠ b₀ := by
                intro hEq
                exact hb₀ (hEq ▸ b.property)
              simp [f, hbne, hb.1]
      · have hall :
            ∀ a₁ ∈ S, ∀ a₂ ∈ S, a₁ ≠ a₂ → s(a₁, a₂) ∈ E₀ := by
          intro a₁ ha₁S a₂ ha₂S ha12
          by_contra hnotmem
          exact hnew ⟨a₁, ha₁S, a₂, ha₂S, ha12, hnotmem⟩
        let M₀ := minorModelFromAssignment G A B₀ hAB₀ E₀ f₀ hf₀_adj hwitness₀
        have hS_clique :
            ∀ a₁ ∈ S, ∀ a₂ ∈ S, a₁ ≠ a₂ →
              (SimpleGraph.fromEdgeSet (↑E₀ : Set (Sym2 {a : V // a ∈ A}))).Adj a₁ a₂ := by
          intro a₁ ha₁S a₂ ha₂S ha12
          rw [SimpleGraph.fromEdgeSet_adj]
          exact ⟨hall a₁ ha₁S a₂ ha₂S ha12, ha12⟩
        have hb₀_adj :
            ∀ a ∈ S, G.Adj b₀ (M₀.center a) := by
          intro a haS
          change G.Adj b₀ a.val
          have ha_mem : a.val ∈ G.neighborFinset b₀ ∩ A := by
            simpa [S] using haS
          exact (G.mem_neighborFinset b₀ a.val).mp (Finset.mem_inter.mp ha_mem).1
        have hb₀_not_branch :
            ∀ w : {a : V // a ∈ A}, b₀ ∉ M₀.branchSet w := by
          intro w
          change b₀ ∉ {v : V | v = w.val ∨ ∃ b : {b : V // b ∈ B₀}, f₀ b = w ∧ v = b.val}
          intro hb
          rcases hb with hEq | ⟨b, -, hbval⟩
          · rw [Finset.disjoint_left] at hAB_ins
            exact (hAB_ins w.property) (hEq ▸ Finset.mem_insert_self b₀ B₀)
          · exact hb₀ (hbval ▸ b.property)
        exact Or.inl ⟨S.card, hS_ge, ⟨clique_extension_minor M₀ S hS_clique b₀ hb₀_adj hb₀_not_branch⟩⟩

/-- **Step 2 (greedy construction)**: Given a "good pair" (A, B) in G, the greedy
process either finds a clique minor K_{t+1} for t ≥ log n, or builds a depth-1
minor G' on vertex set {a : V // a ∈ A} with ≥ |B| edges.

Uses `greedy_edges_or_clique` for the inductive construction and
`minorModelFromAssignment` to build the minor model from the assignment. -/
private lemma greedy_densify
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hAB : Disjoint A B)
    (hB_nbrs : ∀ b ∈ B, log ↑(Fintype.card V) ≤ ↑(G.neighborFinset b ∩ A).card) :
    (∃ t : ℕ, log ↑(Fintype.card V) ≤ ↑t ∧
      IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G 1) ∨
    (∃ (G' : SimpleGraph {a : V // a ∈ A}) (_ : DecidableRel G'.Adj),
      IsShallowMinor G' G 1 ∧
      (↑B.card : ℝ) ≤ ↑G'.edgeFinset.card) := by
  rcases greedy_edges_or_clique G A B hAB hB_nbrs with
    clique | ⟨E, f, hcard, hnd, hf_adj, hwitness⟩
  · exact Or.inl clique
  · right
    letI : DecidableRel (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 {a : V // a ∈ A})) :
        SimpleGraph {a : V // a ∈ A}).Adj :=
      fun a a' => by rw [SimpleGraph.fromEdgeSet_adj]; exact inferInstance
    refine ⟨SimpleGraph.fromEdgeSet (↑E : Set _), ‹_›,
            ⟨minorModelFromAssignment G A B hAB E f hf_adj hwitness⟩, ?_⟩
    simp only [Nat.cast_le]
    apply hcard.trans
    apply Finset.card_le_card
    intro e he
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet,
               Set.mem_diff, Finset.mem_coe, Sym2.mem_diagSet]
    exact ⟨he, hnd e he⟩

/-- **Step 3 (arithmetic)**: For large n, if n' ≤ 3n^{1-ε} log n then
(n')^{1+ε+ε²} ≤ n/2.

Proof:
  (n')^{1+ε+ε²} ≤ (3n^{1-ε} log n)^{1+ε+ε²}
    = 3^{1+ε+ε²} · n^{(1-ε)(1+ε+ε²)} · (log n)^{1+ε+ε²}
    = 3^{1+ε+ε²} · n^{1-ε³} · (log n)^{1+ε+ε²}  [since (1-ε)(1+ε+ε²) = 1-ε³]
  By isLittleO_log_rpow_rpow_atTop (ε³ > 0): eventually
    (log n)^{1+ε+ε²} ≤ n^{ε³} / (2 · 3^{1+ε+ε²})
  So the bound is ≤ 3^{1+ε+ε²} · n^{1-ε³} · n^{ε³} / (2·3^{1+ε+ε²}) = n/2. -/
private lemma edge_density_bound (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ M : ℕ, ∀ (n n' : ℕ), M ≤ n →
      (↑n' : ℝ) ≤ 3 * (↑n : ℝ) ^ (1 - ε) * Real.log ↑n →
      (↑n' : ℝ) ^ (1 + ε + ε ^ 2) ≤ (↑n : ℝ) / 2 := by
  have hε3 : (0 : ℝ) < ε ^ 3 := by positivity
  -- (log x)^(1+ε+ε²) =o[atTop] x^(ε³) since ε³ > 0
  have hiso := isLittleO_log_rpow_rpow_atTop (1 + ε + ε ^ 2) hε3
  -- Extract: eventually |log x|^(...) ≤ (2·3^{...})⁻¹ · x^(ε³)
  have hc_pos : (0 : ℝ) < (2 * (3 : ℝ) ^ (1 + ε + ε ^ 2))⁻¹ := by positivity
  have hbnd_nat : ∀ᶠ m : ℕ in atTop,
      ‖Real.log (↑m : ℝ) ^ (1 + ε + ε ^ 2)‖ ≤
      (2 * (3 : ℝ) ^ (1 + ε + ε ^ 2))⁻¹ * ‖(↑m : ℝ) ^ ε ^ 3‖ :=
    tendsto_natCast_atTop_atTop.eventually (hiso.bound hc_pos)
  rw [Filter.eventually_atTop] at hbnd_nat
  obtain ⟨M₀, hM₀⟩ := hbnd_nat
  -- M = max M₀ 3 ensures n ≥ 3 so log n ≥ 0
  refine ⟨max M₀ 3, ?_⟩
  intro n n' hn_ge hn'_le
  have hM₀n : M₀ ≤ n := (Nat.le_max_left M₀ 3).trans hn_ge
  have hn_ge3 : (3 : ℕ) ≤ n := (Nat.le_max_right M₀ 3).trans hn_ge
  have hn_pos : (0 : ℝ) < (↑n : ℝ) := by exact_mod_cast show 0 < n by omega
  have hnn : (0 : ℝ) ≤ (↑n : ℝ) := le_of_lt hn_pos
  have hlog_nn : (0 : ℝ) ≤ Real.log (↑n : ℝ) :=
    Real.log_nonneg (by norm_cast; linarith)
  -- Trivial when n' = 0: (0:ℝ)^(1+ε+ε²) = 0 ≤ n/2
  rcases Nat.eq_zero_or_pos n' with rfl | hn'_pos
  · simp only [Nat.cast_zero,
               Real.zero_rpow (show (1 + ε + ε ^ 2 : ℝ) ≠ 0 by positivity)]
    positivity
  -- Main case: n' > 0
  have hn'_pos_r : (0 : ℝ) < (↑n' : ℝ) := Nat.cast_pos.mpr hn'_pos
  -- Step 1: (n')^{1+ε+ε²} ≤ (3·n^{1-ε}·log n)^{1+ε+ε²}
  have hstep1 : (↑n' : ℝ) ^ (1 + ε + ε ^ 2) ≤
      (3 * (↑n : ℝ) ^ (1 - ε) * Real.log (↑n : ℝ)) ^ (1 + ε + ε ^ 2) :=
    Real.rpow_le_rpow (by positivity) hn'_le (by positivity)
  -- Step 2: expand (3·n^{1-ε}·log n)^{1+ε+ε²} = 3^{...}·n^{1-ε³}·(log n)^{...}
  have hstep2 : (3 * (↑n : ℝ) ^ (1 - ε) * Real.log (↑n : ℝ)) ^ (1 + ε + ε ^ 2) =
      (3 : ℝ) ^ (1 + ε + ε ^ 2) * (↑n : ℝ) ^ (1 - ε ^ 3) *
      Real.log (↑n : ℝ) ^ (1 + ε + ε ^ 2) := by
    rw [Real.mul_rpow (by positivity) hlog_nn,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Real.rpow_nonneg hnn _),
        ← Real.rpow_mul hnn, show (1 - ε) * (1 + ε + ε ^ 2) = 1 - ε ^ 3 from by ring]
  -- Step 3: log bound from hM₀: (log n)^{...} ≤ (2·3^{...})⁻¹ · n^{ε³}
  have hlog_bnd : Real.log (↑n : ℝ) ^ (1 + ε + ε ^ 2) ≤
      (2 * (3 : ℝ) ^ (1 + ε + ε ^ 2))⁻¹ * (↑n : ℝ) ^ ε ^ 3 := by
    have h := hM₀ n hM₀n
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg hlog_nn _),
         Real.norm_of_nonneg (Real.rpow_nonneg hnn _)] at h
  -- Step 4: algebraic simplification 3^r · n^{1-ε³} · (2·3^r)⁻¹ · n^{ε³} = n/2
  have hstep4 : (3 : ℝ) ^ (1 + ε + ε ^ 2) * (↑n : ℝ) ^ (1 - ε ^ 3) *
      ((2 * (3 : ℝ) ^ (1 + ε + ε ^ 2))⁻¹ * (↑n : ℝ) ^ ε ^ 3) = (↑n : ℝ) / 2 := by
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ (1 + ε + ε ^ 2) := by positivity
    rw [show (3 : ℝ) ^ (1 + ε + ε ^ 2) * (↑n : ℝ) ^ (1 - ε ^ 3) *
        ((2 * (3 : ℝ) ^ (1 + ε + ε ^ 2))⁻¹ * (↑n : ℝ) ^ ε ^ 3) =
        (3 : ℝ) ^ (1 + ε + ε ^ 2) * (2 * (3 : ℝ) ^ (1 + ε + ε ^ 2))⁻¹ *
        ((↑n : ℝ) ^ (1 - ε ^ 3) * (↑n : ℝ) ^ ε ^ 3) from by ring]
    rw [← Real.rpow_add hn_pos, show (1 - ε ^ 3) + ε ^ 3 = 1 from by ring, Real.rpow_one]
    have h_half : (3 : ℝ) ^ (1 + ε + ε ^ 2) * (2 * (3 : ℝ) ^ (1 + ε + ε ^ 2))⁻¹ = 1 / 2 := by
      rw [mul_inv, mul_comm (2 : ℝ)⁻¹, ← mul_assoc,
          mul_inv_cancel₀ h3pos.ne', one_mul, inv_eq_one_div]
    rw [h_half]; ring
  -- Chain the steps
  calc (↑n' : ℝ) ^ (1 + ε + ε ^ 2)
      ≤ (3 * (↑n : ℝ) ^ (1 - ε) * Real.log (↑n : ℝ)) ^ (1 + ε + ε ^ 2) := hstep1
    _ = (3 : ℝ) ^ (1 + ε + ε ^ 2) * (↑n : ℝ) ^ (1 - ε ^ 3) *
        Real.log (↑n : ℝ) ^ (1 + ε + ε ^ 2) := hstep2
    _ ≤ (3 : ℝ) ^ (1 + ε + ε ^ 2) * (↑n : ℝ) ^ (1 - ε ^ 3) *
        ((2 * (3 : ℝ) ^ (1 + ε + ε ^ 2))⁻¹ * (↑n : ℝ) ^ ε ^ 3) := by
          gcongr
    _ = (↑n : ℝ) / 2 := hstep4

/-- Lemma 3.4/ch1: Densification lemma. -/
theorem densification (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 2 / 3) :
    ∃ M : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      M ≤ Fintype.card V →
      (∀ v : V, (Fintype.card V : ℝ) ^ ε ≤ ↑(G.degree v)) →
      (∃ t : ℕ, Real.log ↑(Fintype.card V) ≤ ↑t ∧
        IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G 1) ∨
      (∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
        (G' : SimpleGraph W) (_ : DecidableRel G'.Adj),
        IsShallowMinor G' G 1 ∧
        (Fintype.card V : ℝ) ^ (1 - ε) ≤ ↑(Fintype.card W) ∧
        (Fintype.card W : ℝ) ^ (1 + ε + ε ^ 2) ≤ ↑(G'.edgeFinset.card)) := by
  obtain ⟨M₁, hM₁⟩ := exists_good_pair ε hε_pos hε_le
  obtain ⟨M₂, hM₂⟩ := edge_density_bound ε hε_pos
  refine ⟨max M₁ M₂, ?_⟩
  intro V _ _ G _ hn_ge hmin
  have hM₁n : M₁ ≤ Fintype.card V := (Nat.le_max_left M₁ M₂).trans hn_ge
  have hM₂n : M₂ ≤ Fintype.card V := (Nat.le_max_right M₁ M₂).trans hn_ge
  obtain ⟨A, B, hAB, hA_lower, hA_upper, hB_lower, hB_nbrs⟩ := hM₁ G hM₁n hmin
  rcases greedy_densify G A B hAB hB_nbrs with
    ⟨t, ht_log, ht_minor⟩ | ⟨G', hG'_dec, hG'_minor, hG'_edges⟩
  · exact Or.inl ⟨t, ht_log, ht_minor⟩
  · right
    refine ⟨{a : V // a ∈ A}, inferInstance, inferInstance, G', hG'_dec,
            hG'_minor, ?_, ?_⟩
    · -- (Fintype.card V)^{1-ε} ≤ Fintype.card W = A.card
      simp only [Fintype.card_coe]
      exact_mod_cast hA_lower
    · -- (Fintype.card W)^{1+ε+ε²} ≤ G'.edgeFinset.card
      simp only [Fintype.card_coe]
      have h_arith : (↑A.card : ℝ) ^ (1 + ε + ε ^ 2) ≤ (↑(Fintype.card V) : ℝ) / 2 :=
        hM₂ (Fintype.card V) A.card hM₂n (by exact_mod_cast hA_upper)
      calc (↑A.card : ℝ) ^ (1 + ε + ε ^ 2)
          ≤ (↑(Fintype.card V) : ℝ) / 2 := h_arith
        _ ≤ ↑B.card := hB_lower
        _ ≤ ↑G'.edgeFinset.card := hG'_edges

end Lax5Proofs.Source.Catalog.SparsityLectures.Densification
