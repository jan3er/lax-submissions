import Lax13Proofs.Refine.Asymptotics.TwoDimensional

/-!
# Two-dimensional composition and normalization

This file ports the live public declarations from `Asymptotics_2D.thy` at
`bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`,
lines 272--463, 563--636, and 671--672.

Source-to-Lean table (12 live declarations and one substrate exclusion):

* 272 `bigO2_compose_both` -> `bigO2ComposeBoth`
* 342 `bigOmega2_compose_both` -> `bigOmega2ComposeBoth`
* 412 `bigTheta2_compose_both` -> `bigTheta2ComposeBoth`
* 432 `bigTheta2_compose_both_linear` -> `bigTheta2ComposeBothLinear`
* 453 `bigTheta2_compose_both_linear'` -> `bigTheta2ComposeBothPolylogLinear`
* 563 `cas1` -> `Polylog2StrictlyBelow`
* 566 `polylog2_compare` -> `polylog2Compare`
* 602 `polylog2_compare'` -> `polylog2CompareFstStrict`
* 612 `polylog2_compare2'` -> `polylog2CompareSndStrict`
* 624 `landau_norms2` -> `landauNorms2` (a conjunction-valued theorem bundle)
* 634 `landau_norms2'` -> `landauNorms2Mul`
* 671 `polylog_omega1` -> `polylogLittleOmegaOne`
* 674 `ML_file "landau_util_2d.ML"` -> substrate exclusion: the named rules
  above and representative checks replace the source's partial head-keyed ML
  reducer; no total normalizer is claimed.
-/

open Filter
open scoped Topology

namespace Lax13Proofs.Refine.Asymptotics2D

open Asymptotics
open Lax13Proofs.Refine.Asymptotics1D

private theorem eventuallyProductAtTopIff {P : ℕ × ℕ → Prop} :
    (∀ᶠ p in productAtTop, P p) ↔
      ∃ N, ∀ n m, N ≤ n → N ≤ m → P (n, m) := by
  change (∀ᶠ p in atTop ×ˢ atTop, P p) ↔ _
  rw [prod_atTop_atTop_eq, eventually_atTop_prod_self]

/-! ## Composition in both coordinates -/

/-- Source `bigO2_compose_both` (line 272). -/
theorem bigO2ComposeBoth {f₁ : ℕ × ℕ → ℕ} {g₁ : ℕ × ℕ → ℝ}
    {f₂a g₂a f₂b g₂b : ℕ → ℕ}
    (hstable : StableBigO2 g₁)
    (houter : (fun p => (f₁ p : ℝ)) =O[productAtTop] g₁)
    (hinnera : (fun n => (f₂a n : ℝ)) =O[atTop] fun n => (g₂a n : ℝ))
    (hf₂a : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (f₂a n : ℝ))
    (hg₂a : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (g₂a n : ℝ))
    (hinnerb : (fun n => (f₂b n : ℝ)) =O[atTop] fun n => (g₂b n : ℝ))
    (hf₂b : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (f₂b n : ℝ))
    (hg₂b : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (g₂b n : ℝ))
    (hmono : EventuallyMonoNorm2 g₁) :
    (fun p => (f₁ (f₂a p.1, f₂b p.2) : ℝ)) =O[productAtTop]
      fun p => g₁ (g₂a p.1, g₂b p.2) := by
  obtain ⟨c₁, hc₁, n₁, h₁⟩ := bigO2E houter
  obtain ⟨c₂a, hc₂a, n₂a, h₂a⟩ := bigOENat hinnera
  obtain ⟨c₂b, hc₂b, n₂b, h₂b⟩ := bigOENat hinnerb
  obtain ⟨c₃, hc₃, h₃⟩ := stableBigO2Extract hstable hc₂a hc₂b
  rw [eventuallyProductAtTopIff] at h₃
  unfold EventuallyMonoNorm2 at hmono
  rw [eventuallyProductAtTopIff] at hmono
  obtain ⟨n₃, h₃⟩ := h₃
  obtain ⟨nM, hM⟩ := hmono
  apply IsBigO.of_bound (c₁ * c₃)
  filter_upwards [
    (fsmallEventually (c := max n₁ nM) hf₂a).prod_mk
      (fsmallEventually (c := max n₁ nM) hf₂b),
    (fsmallEventually (c := n₃) hg₂a).prod_mk
      (fsmallEventually (c := n₃) hg₂b),
    (eventually_ge_atTop n₂a).prod_mk (eventually_ge_atTop n₂b)]
      with p hfp hgp hnp
  have hn₁a : n₁ ≤ f₂a p.1 := (le_max_left _ _).trans hfp.1
  have hn₁b : n₁ ≤ f₂b p.2 := (le_max_left _ _).trans hfp.2
  have hnMa : nM ≤ f₂a p.1 := (le_max_right _ _).trans hfp.1
  have hnMb : nM ≤ f₂b p.2 := (le_max_right _ _).trans hfp.2
  have hia : f₂a p.1 ≤ c₂a * g₂a p.1 := h₂a p.1 hnp.1
  have hib : f₂b p.2 ≤ c₂b * g₂b p.2 := h₂b p.2 hnp.2
  have hmonox :
      ‖g₁ (f₂a p.1, f₂b p.2)‖ ≤
        ‖g₁ (c₂a * g₂a p.1, c₂b * g₂b p.2)‖ :=
    hM _ _ hnMa hnMb _ hia _ hib
  calc
    ‖(f₁ (f₂a p.1, f₂b p.2) : ℝ)‖ ≤
        c₁ * ‖g₁ (f₂a p.1, f₂b p.2)‖ := h₁ _ hn₁a hn₁b
    _ ≤ c₁ * ‖g₁ (c₂a * g₂a p.1, c₂b * g₂b p.2)‖ :=
      mul_le_mul_of_nonneg_left hmonox hc₁.le
    _ ≤ c₁ * (c₃ * ‖g₁ (g₂a p.1, g₂b p.2)‖) :=
      mul_le_mul_of_nonneg_left (h₃ _ _ hgp.1 hgp.2) hc₁.le
    _ = (c₁ * c₃) * ‖g₁ (g₂a p.1, g₂b p.2)‖ := by ring

/-- Source `bigOmega2_compose_both` (line 342), preserving reverse-big-O orientation. -/
theorem bigOmega2ComposeBoth {f₁ : ℕ × ℕ → ℕ} {g₁ : ℕ × ℕ → ℝ}
    {f₂a g₂a f₂b g₂b : ℕ → ℕ}
    (hstable : StableBigO2 g₁)
    (houter : IsBigOmega2 (fun p => (f₁ p : ℝ)) g₁)
    (hinnera : IsBigOmega atTop (fun n => (f₂a n : ℝ)) (fun n => (g₂a n : ℝ)))
    (hf₂a : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (f₂a n : ℝ))
    (hg₂a : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (g₂a n : ℝ))
    (hinnerb : IsBigOmega atTop (fun n => (f₂b n : ℝ)) (fun n => (g₂b n : ℝ)))
    (hf₂b : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (f₂b n : ℝ))
    (hg₂b : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (g₂b n : ℝ))
    (hmono : EventuallyMonoNorm2 g₁) :
    IsBigOmega2 (fun p => (f₁ (f₂a p.1, f₂b p.2) : ℝ))
      (fun p => g₁ (g₂a p.1, g₂b p.2)) := by
  obtain ⟨c₁, hc₁, n₁, h₁⟩ := bigOmega2E houter
  obtain ⟨c₂a, hc₂a, n₂a, h₂a⟩ := bigOmegaENat hinnera
  obtain ⟨c₂b, hc₂b, n₂b, h₂b⟩ := bigOmegaENat hinnerb
  obtain ⟨c₃, hc₃, h₃⟩ := stableBigO2Extract hstable hc₂a hc₂b
  rw [eventuallyProductAtTopIff] at h₃
  unfold EventuallyMonoNorm2 at hmono
  rw [eventuallyProductAtTopIff] at hmono
  obtain ⟨n₃, h₃⟩ := h₃
  obtain ⟨nM, hM⟩ := hmono
  apply IsBigO.of_bound (c₃ / c₁)
  filter_upwards [
    (fsmallEventually (c := max n₁ n₃) hf₂a).prod_mk
      (fsmallEventually (c := max n₁ n₃) hf₂b),
    (fsmallEventually (c := nM) hg₂a).prod_mk
      (fsmallEventually (c := nM) hg₂b),
    (eventually_ge_atTop n₂a).prod_mk (eventually_ge_atTop n₂b)]
      with p hfp hgp hnp
  have hn₁a : n₁ ≤ f₂a p.1 := (le_max_left _ _).trans hfp.1
  have hn₁b : n₁ ≤ f₂b p.2 := (le_max_left _ _).trans hfp.2
  have hn₃a : n₃ ≤ f₂a p.1 := (le_max_right _ _).trans hfp.1
  have hn₃b : n₃ ≤ f₂b p.2 := (le_max_right _ _).trans hfp.2
  have hia : g₂a p.1 ≤ c₂a * f₂a p.1 := h₂a p.1 hnp.1
  have hib : g₂b p.2 ≤ c₂b * f₂b p.2 := h₂b p.2 hnp.2
  have hmonox :
      ‖g₁ (g₂a p.1, g₂b p.2)‖ ≤
        ‖g₁ (c₂a * f₂a p.1, c₂b * f₂b p.2)‖ :=
    hM _ _ hgp.1 hgp.2 _ hia _ hib
  have houterx :
      ‖g₁ (f₂a p.1, f₂b p.2)‖ ≤
        ‖(f₁ (f₂a p.1, f₂b p.2) : ℝ)‖ / c₁ :=
    (le_div_iff₀ hc₁).2 (by simpa [mul_comm] using h₁ _ hn₁a hn₁b)
  calc
    ‖g₁ (g₂a p.1, g₂b p.2)‖ ≤
        ‖g₁ (c₂a * f₂a p.1, c₂b * f₂b p.2)‖ := hmonox
    _ ≤ c₃ * ‖g₁ (f₂a p.1, f₂b p.2)‖ :=
      h₃ _ _ hn₃a hn₃b
    _ ≤ c₃ * (‖(f₁ (f₂a p.1, f₂b p.2) : ℝ)‖ / c₁) :=
      mul_le_mul_of_nonneg_left houterx hc₃.le
    _ = (c₃ / c₁) * ‖(f₁ (f₂a p.1, f₂b p.2) : ℝ)‖ := by ring

/-- Source `bigTheta2_compose_both` (line 412). -/
theorem bigTheta2ComposeBoth {f₁ : ℕ × ℕ → ℕ} {g₁ : ℕ × ℕ → ℝ}
    {f₂a g₂a f₂b g₂b : ℕ → ℕ}
    (hstable : StableBigO2 g₁)
    (houter : (fun p => (f₁ p : ℝ)) =Θ[productAtTop] g₁)
    (hinnera : (fun n => (f₂a n : ℝ)) =Θ[atTop] fun n => (g₂a n : ℝ))
    (hf₂a : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (f₂a n : ℝ))
    (hinnerb : (fun n => (f₂b n : ℝ)) =Θ[atTop] fun n => (g₂b n : ℝ))
    (hf₂b : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (f₂b n : ℝ))
    (hmono : EventuallyMonoNorm2 g₁) :
    (fun p => (f₁ (f₂a p.1, f₂b p.2) : ℝ)) =Θ[productAtTop]
      fun p => g₁ (g₂a p.1, g₂b p.2) := by
  have hg₂a : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (g₂a n : ℝ) := by
    apply (isLittleO_one_left_iff ℝ).mpr
    exact hinnera.tendsto_norm_atTop_iff.mp ((isLittleO_one_left_iff ℝ).mp hf₂a)
  have hg₂b : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (g₂b n : ℝ) := by
    apply (isLittleO_one_left_iff ℝ).mpr
    exact hinnerb.tendsto_norm_atTop_iff.mp ((isLittleO_one_left_iff ℝ).mp hf₂b)
  exact ⟨
    bigO2ComposeBoth hstable houter.1 hinnera.1 hf₂a hg₂a
      hinnerb.1 hf₂b hg₂b hmono,
    bigOmega2ComposeBoth hstable houter.2 hinnera.2 hf₂a hg₂a
      hinnerb.2 hf₂b hg₂b hmono⟩

/-- Source `bigTheta2_compose_both_linear` (line 432). -/
theorem bigTheta2ComposeBothLinear {f₁ : ℕ × ℕ → ℕ} {g₁ : ℕ × ℕ → ℝ}
    {f₂a f₂b : ℕ → ℕ}
    (hstable : StableBigO2 g₁) (hmono : EventuallyMonoNorm2 g₁)
    (houter : (fun p => (f₁ p : ℝ)) =Θ[productAtTop] g₁)
    (hinnera : (fun n => (f₂a n : ℝ)) =Θ[atTop] fun n => (n : ℝ))
    (hinnerb : (fun n => (f₂b n : ℝ)) =Θ[atTop] fun n => (n : ℝ)) :
    (fun p => (f₁ (f₂a p.1, f₂b p.2) : ℝ)) =Θ[productAtTop] g₁ := by
  have hid : Tendsto (norm ∘ fun n : ℕ => (n : ℝ)) atTop atTop := by
    simpa [Function.comp_def] using tendsto_natCast_atTop_atTop
  have hga : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (f₂a n : ℝ) :=
    (isLittleO_one_left_iff ℝ).mpr (hinnera.tendsto_norm_atTop_iff.mpr hid)
  have hgb : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (f₂b n : ℝ) :=
    (isLittleO_one_left_iff ℝ).mpr (hinnerb.tendsto_norm_atTop_iff.mpr hid)
  simpa using bigTheta2ComposeBoth hstable houter hinnera hga hinnerb hgb hmono

/-- Source `bigTheta2_compose_both_linear'` (line 453). -/
theorem bigTheta2ComposeBothPolylogLinear
    {f₁ : ℕ × ℕ → ℕ} {g₁ : ℕ × ℕ → ℝ} {f₂a f₂b : ℕ → ℕ}
    (hstable : StableBigO2 g₁) (hmono : EventuallyMonoNorm2 g₁)
    (houter : (fun p => (f₁ p : ℝ)) =Θ[productAtTop] g₁)
    (hinnera : (fun n => (f₂a n : ℝ)) =Θ[atTop] fun n => polylog 1 0 n)
    (hinnerb : (fun n => (f₂b n : ℝ)) =Θ[atTop] fun n => polylog 1 0 n) :
    (fun p => (f₁ (f₂a p.1, f₂b p.2) : ℝ)) =Θ[productAtTop] g₁ := by
  apply bigTheta2ComposeBothLinear hstable hmono houter
  · simpa [polylog] using hinnera
  · simpa [polylog] using hinnerb

/-! ## Partial comparison of two-dimensional polylogarithms -/

/-- Source `cas1` (line 563): at least one coordinate is strict and neither decreases. -/
def Polylog2StrictlyBelow (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ) : Prop :=
  ((a₁ < a₂ ∨ a₁ = a₂ ∧ b₁ < b₂) ∧
      (c₁ < c₂ ∨ c₁ = c₂ ∧ d₁ ≤ d₂)) ∨
    ((a₁ < a₂ ∨ a₁ = a₂ ∧ b₁ ≤ b₂) ∧
      (c₁ < c₂ ∨ c₁ = c₂ ∧ d₁ < d₂))

/-- Source `polylog2_compare` (line 566). -/
theorem polylog2Compare {f₁ f₂ : ℕ × ℕ → ℝ} {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (hf₁ : f₁ =Θ[productAtTop] polylog2 a₁ b₁ c₁ d₁)
    (hf₂ : f₂ =Θ[productAtTop] polylog2 a₂ b₂ c₂ d₂)
    (hcmp : Polylog2StrictlyBelow a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) :
    f₁ =o[productAtTop] f₂ := by
  rcases hcmp with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · have hoa := polylogCompare ha
    have hOc : (fun n => polylog c₁ d₁ n) =O[atTop] fun n => polylog c₂ d₂ n := by
      rcases hc with hc | ⟨rfl, hd⟩
      · exact (polylogCompare (Or.inl hc)).isBigO
      · rcases hd.eq_or_lt with rfl | hd
        · exact isBigO_refl _ _
        · exact (polylogCompare (Or.inr ⟨rfl, hd⟩)).isBigO
    have hpoly : polylog2 a₁ b₁ c₁ d₁ =o[productAtTop]
        polylog2 a₂ b₂ c₂ d₂ := by
      simpa [polylog2] using oO_o hoa hOc
    exact hf₁.trans_isLittleO (hpoly.trans_isTheta hf₂.symm)
  · have hOa : (fun n => polylog a₁ b₁ n) =O[atTop] fun n => polylog a₂ b₂ n := by
      rcases ha with ha | ⟨rfl, hb⟩
      · exact (polylogCompare (Or.inl ha)).isBigO
      · rcases hb.eq_or_lt with rfl | hb
        · exact isBigO_refl _ _
        · exact (polylogCompare (Or.inr ⟨rfl, hb⟩)).isBigO
    have hoc := polylogCompare hc
    have hpoly : polylog2 a₁ b₁ c₁ d₁ =o[productAtTop]
        polylog2 a₂ b₂ c₂ d₂ := by
      simpa [polylog2] using Oo_o hOa hoc
    exact hf₁.trans_isLittleO (hpoly.trans_isTheta hf₂.symm)

/-- Source first-coordinate-strict wrapper `polylog2_compare'` (line 602). -/
theorem polylog2CompareFstStrict {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (hcmp : (a₁ < a₂ ∨ a₁ = a₂ ∧ b₁ < b₂) ∧
      (c₁ < c₂ ∨ c₁ = c₂ ∧ d₁ ≤ d₂)) :
    polylog2 a₁ b₁ c₁ d₁ =o[productAtTop] polylog2 a₂ b₂ c₂ d₂ := by
  exact polylog2Compare (isTheta_refl _ _) (isTheta_refl _ _) (Or.inl hcmp)

/-- Source second-coordinate-strict wrapper `polylog2_compare2'` (line 612). -/
theorem polylog2CompareSndStrict {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (hcmp : (a₁ < a₂ ∨ a₁ = a₂ ∧ b₁ ≤ b₂) ∧
      (c₁ < c₂ ∨ c₁ = c₂ ∧ d₁ < d₂)) :
    polylog2 a₁ b₁ c₁ d₁ =o[productAtTop] polylog2 a₂ b₂ c₂ d₂ := by
  exact polylog2Compare (isTheta_refl _ _) (isTheta_refl _ _) (Or.inr hcmp)

/-! ## Named normalization rules -/

/-- Source theorem bundle `landau_norms2` (line 624). -/
theorem landauNorms2 (a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℕ) (p : ℕ × ℕ) :
    (polylog a₁ b₁ p.1 = polylog2 a₁ b₁ 0 0 p) ∧
    (polylog a₂ b₂ p.2 = polylog2 0 0 a₂ b₂ p) ∧
    (polylog2 a₁ b₁ a₂ b₂ p * polylog2 a₃ b₃ a₄ b₄ p =
      polylog2 (a₁ + a₃) (b₁ + b₃) (a₂ + a₄) (b₂ + b₄) p) := by
  constructor
  · simp [polylog2, polylog]
  constructor
  · simp [polylog2, polylog]
  · simp only [polylog2]
    rw [← landauNormsMul a₁ b₁ a₃ b₃ p.1,
      ← landauNormsMul a₂ b₂ a₄ b₄ p.2]
    ring

/-- Source function-level multiplication wrapper `landau_norms2'` (line 634). -/
theorem landauNorms2Mul (a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℕ) :
    (fun p => polylog2 a₁ b₁ a₂ b₂ p * polylog2 a₃ b₃ a₄ b₄ p) =
      polylog2 (a₁ + a₃) (b₁ + b₃) (a₂ + a₄) (b₂ + b₄) := by
  funext p
  exact (landauNorms2 a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ p).2.2

/-- Source `polylog_omega1` (line 671). -/
theorem polylogLittleOmegaOne {a b : ℕ} (h : a ≠ 0 ∨ b ≠ 0) :
    (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => polylog a b n := by
  have hlex : 0 < a ∨ (0 = a ∧ 0 < b) := by omega
  simpa [polylog] using (polylogCompare (a₁ := 0) (b₁ := 0) hlex)

/-! ## Representative positive checks -/

private theorem thetaCompositionGate {f₁ : ℕ × ℕ → ℕ} {g₁ : ℕ × ℕ → ℝ}
    {f₂a f₂b : ℕ → ℕ}
    (hs : StableBigO2 g₁) (hm : EventuallyMonoNorm2 g₁)
    (ho : (fun p => (f₁ p : ℝ)) =Θ[productAtTop] g₁)
    (ha : (fun n => (f₂a n : ℝ)) =Θ[atTop] fun n => (n : ℝ))
    (hb : (fun n => (f₂b n : ℝ)) =Θ[atTop] fun n => (n : ℝ)) :
    (fun p => (f₁ (f₂a p.1, f₂b p.2) : ℝ)) =Θ[productAtTop] g₁ :=
  bigTheta2ComposeBothLinear hs hm ho ha hb

private theorem fstStrictComparisonGate :
    polylog2 0 0 0 0 =o[productAtTop] polylog2 1 0 0 0 := by
  exact polylog2CompareFstStrict ⟨Or.inl (by omega), Or.inr ⟨rfl, le_rfl⟩⟩

private theorem sndStrictComparisonGate :
    polylog2 0 0 0 0 =o[productAtTop] polylog2 0 0 0 1 := by
  exact polylog2CompareSndStrict ⟨Or.inr ⟨rfl, le_rfl⟩, Or.inr ⟨rfl, by omega⟩⟩

private theorem polylogMultiplicationGate (p : ℕ × ℕ) :
    polylog2 1 2 3 4 p * polylog2 5 6 7 8 p = polylog2 6 8 10 12 p := by
  simpa using (landauNorms2 1 2 3 4 5 6 7 8 p).2.2

/-! ## Kernel-three axiom guards -/

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.bigO2ComposeBoth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigO2ComposeBoth

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.bigOmega2ComposeBoth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigOmega2ComposeBoth

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.bigTheta2ComposeBoth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigTheta2ComposeBoth

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.polylog2Compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polylog2Compare

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.landauNorms2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms landauNorms2

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.polylogLittleOmegaOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polylogLittleOmegaOne

end Lax13Proofs.Refine.Asymptotics2D
