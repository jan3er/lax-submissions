import Lax13Proofs.Refine.Asymptotics.OneDimensional

/-!
# One-dimensional asymptotic operations and normalization

This file ports the live public family from `Asymptotics_1D.thy` at
`bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`,
lines 386--854. Natural-valued functions are cast explicitly to `ℝ` at every
Landau boundary, and Isabelle omega is represented by reverse mathlib big-O.

Source-to-Lean table (32 live declarations and four exclusions):

* 386 `bigOmega_compose` -> `bigOmegaCompose`
* 430 `bigO_compose` -> `bigOCompose`
* 474 `bigTheta_compose` -> `bigThetaCompose`
* 489 `polylog_power_compose` -> excluded: proof ends in source `oops`
* 500 `bigTheta_compose_linear` -> `bigThetaComposeLinear`
* 515 `bigTheta_compose_linear'` -> `bigThetaComposePolylogLinear`
* 527 `asym_bound_div` -> `asymBoundDiv`
* 589 `asym_bound_div_linear` -> `asymBoundDivLinear`
* 594 `asym_bound_diff` -> `asymBoundDiff`
* 642--643 `ceiling_Theta` -> `ceilingTheta`
* 689 `eventually_nonneg_logplus` -> `eventNonnegLogPlus`
* 693 `log_2_asym'` -> `log2AsymHelper`
* 699 `log_2_asym` -> `log2Asym`
* 703 `abcd_lnx` -> `abcdLog`
* 725 `log2_gt_zero` -> `log2Nonnegative`
* 730 `Theta_plus` -> `thetaAdd`
* 781 `Theta_plus'` -> `thetaAddFn`
* 796 `landau_norms(1)` -> `landauNormsOne`
* 796 `landau_norms(2)` -> `landauNormsLinear`
* 796 `landau_norms(3)` -> `landauNormsLog`
* 796 `landau_norms(4)` -> `landauNormsPow`
* 796 `landau_norms(5)` -> `landauNormsLogPow`
* 796 `landau_norms(6)` -> `landauNormsMul`
* 805 `plus_absorb1'` -> `plusAbsorbLeft`
* 808 `plus_absorb2'` -> `plusAbsorbRight`
* 811 `plus_absorb_same'` -> `plusAbsorbSame`
* 814 `bigtheta_add` -> `bigThetaAdd`
* 830 `landau_norm_linear` -> `landauNormLinear`
* 833 `landau_norm_const` -> `landauNormConst`
* 836 `landau_norm_times` -> `landauNormTimes`
* 840 `bigtheta_const` -> `bigThetaConst`
* 844 `bigtheta_linear` -> `bigThetaLinear`
* 848 `bigtheta_mult` -> `bigThetaMul`
* 855 `ML_file landau_util.ML` -> excluded substrate; rendered by the named rules above
* 857 `attribute_setup asym_bound` -> excluded substrate; no total simplifier is claimed
* 859--862 master-theorem ML/method surface -> excluded substrate; mathlib Akra--Bazzi is reused later
-/

open Filter
open scoped Topology

namespace Lax13Proofs.Refine.Asymptotics1D

open Asymptotics

/-! ## Falsification controls -/

/-- A zero divisor cannot satisfy the authored premise of `asymBoundDiv`. -/
private theorem divisorZeroRejected : ¬(0 < (0 : ℕ)) := by omega

/-- A big-O upper bound alone does not imply a theta bound. -/
private theorem bigOOnlyCannotProduceTheta :
    ((fun _ : ℕ => (0 : ℝ)) =O[atTop] fun _ => (1 : ℝ)) ∧
      ¬((fun _ : ℕ => (0 : ℝ)) =Θ[atTop] fun _ => (1 : ℝ)) := by
  constructor
  · exact isBigO_zero _ _
  · intro h
    have heq : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] 0 := isTheta_zero_left.mp h
    obtain ⟨N, hN⟩ := eventually_atTop.mp heq
    have := hN N le_rfl
    norm_num at this

/-- Removing nonnegativity permits cancellation and invalidates theta addition. -/
private theorem thetaAdditionCancellationControl :
    ((fun _ : ℕ => (1 : ℝ)) =Θ[atTop] fun _ => (1 : ℝ)) ∧
      ((fun _ : ℕ => (-1 : ℝ)) =Θ[atTop] fun _ => (1 : ℝ)) ∧
      ¬((fun _ : ℕ => (1 : ℝ) + (-1 : ℝ)) =Θ[atTop]
        fun _ => (1 : ℝ) + 1) := by
  constructor
  · exact isTheta_refl _ _
  constructor
  · exact isTheta_const_const (by norm_num) (by norm_num)
  · intro h
    have hz : (fun _ : ℕ => (0 : ℝ)) =Θ[atTop] fun _ => (1 : ℝ) + 1 := by
      simpa using h
    have heq : (fun _ : ℕ => (1 : ℝ) + 1) =ᶠ[atTop] 0 := isTheta_zero_left.mp hz
    obtain ⟨N, hN⟩ := eventually_atTop.mp heq
    have := hN N le_rfl
    norm_num at this

private inductive SourceDisposition
  | deadSource

/-- The source proof of `polylog_power_compose` ends in `oops`; it is metadata, not an obligation. -/
private def polylogPowerComposeDisposition : SourceDisposition := .deadSource

/-! ## Composition in one variable -/

/-- Source `bigOmega_compose` (line 386), with natural inner functions cast at Landau boundaries. -/
theorem bigOmegaCompose {f₁ g₁ : ℕ → ℝ} {f₂ g₂ : ℕ → ℕ}
    (hstable : StableBigO g₁)
    (houter : IsBigOmega atTop f₁ g₁)
    (hinner : IsBigOmega atTop (fun x => (f₂ x : ℝ)) (fun x => (g₂ x : ℝ)))
    (hf₂ : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun x => (f₂ x : ℝ))
    (hg₂ : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun x => (g₂ x : ℝ))
    (hmono : EventuallyMonoNorm g₁) :
    IsBigOmega atTop (fun x => f₁ (f₂ x)) (fun x => g₁ (g₂ x)) := by
  obtain ⟨c₁, hc₁, n₁, h₁⟩ := bigOmegaE houter
  obtain ⟨c₂, hc₂, n₂, h₂⟩ := bigOmegaENat hinner
  obtain ⟨c₃, hc₃, h₃⟩ := stableBigOD hstable hc₂
  obtain ⟨n₃, h₃⟩ := eventually_atTop.mp h₃
  obtain ⟨nM, hM⟩ := eventually_atTop.mp hmono
  apply IsBigO.of_bound (c₃ / c₁)
  filter_upwards [fsmallEventually (c := max n₁ n₃) hf₂,
    fsmallEventually (c := nM) hg₂, eventually_ge_atTop n₂]
      with x hfx hgx hx
  have hn₁ : n₁ ≤ f₂ x := (le_max_left _ _).trans hfx
  have hn₃ : n₃ ≤ f₂ x := (le_max_right _ _).trans hfx
  have hmonox : ‖g₁ (g₂ x)‖ ≤ ‖g₁ (c₂ * f₂ x)‖ :=
    hM (g₂ x) hgx (c₂ * f₂ x) (h₂ x hx)
  have houterx : ‖g₁ (f₂ x)‖ ≤ ‖f₁ (f₂ x)‖ / c₁ :=
    (le_div_iff₀ hc₁).2 (by simpa [mul_comm] using h₁ (f₂ x) hn₁)
  calc
    ‖g₁ (g₂ x)‖ ≤ ‖g₁ (c₂ * f₂ x)‖ := hmonox
    _ ≤ c₃ * ‖g₁ (f₂ x)‖ := h₃ (f₂ x) hn₃
    _ ≤ c₃ * (‖f₁ (f₂ x)‖ / c₁) :=
      mul_le_mul_of_nonneg_left houterx hc₃.le
    _ = (c₃ / c₁) * ‖f₁ (f₂ x)‖ := by ring

/-- Source `bigO_compose` (line 430), preserving its stability and growth premises. -/
theorem bigOCompose {f₁ g₁ : ℕ → ℝ} {f₂ g₂ : ℕ → ℕ}
    (hstable : StableBigO g₁)
    (houter : f₁ =O[atTop] g₁)
    (hinner : (fun x => (f₂ x : ℝ)) =O[atTop] fun x => (g₂ x : ℝ))
    (hf₂ : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun x => (f₂ x : ℝ))
    (hg₂ : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun x => (g₂ x : ℝ))
    (hmono : EventuallyMonoNorm g₁) :
    (fun x => f₁ (f₂ x)) =O[atTop] fun x => g₁ (g₂ x) := by
  obtain ⟨c₁, hc₁, n₁, h₁⟩ := bigOE houter
  obtain ⟨c₂, hc₂, n₂, h₂⟩ := bigOENat hinner
  obtain ⟨c₃, hc₃, h₃⟩ := stableBigOD hstable hc₂
  obtain ⟨n₃, h₃⟩ := eventually_atTop.mp h₃
  obtain ⟨nM, hM⟩ := eventually_atTop.mp hmono
  apply IsBigO.of_bound (c₁ * c₃)
  filter_upwards [fsmallEventually (c := max n₁ nM) hf₂,
    fsmallEventually (c := n₃) hg₂, eventually_ge_atTop n₂]
      with x hfx hgx hx
  have hn₁ : n₁ ≤ f₂ x := (le_max_left _ _).trans hfx
  have hnM : nM ≤ f₂ x := (le_max_right _ _).trans hfx
  have hmonox : ‖g₁ (f₂ x)‖ ≤ ‖g₁ (c₂ * g₂ x)‖ :=
    hM (f₂ x) hnM (c₂ * g₂ x) (h₂ x hx)
  calc
    ‖f₁ (f₂ x)‖ ≤ c₁ * ‖g₁ (f₂ x)‖ := h₁ (f₂ x) hn₁
    _ ≤ c₁ * ‖g₁ (c₂ * g₂ x)‖ :=
      mul_le_mul_of_nonneg_left hmonox hc₁.le
    _ ≤ c₁ * (c₃ * ‖g₁ (g₂ x)‖) :=
      mul_le_mul_of_nonneg_left (h₃ (g₂ x) hgx) hc₁.le
    _ = (c₁ * c₃) * ‖g₁ (g₂ x)‖ := by ring

/-- Source `bigTheta_compose` (line 474). -/
theorem bigThetaCompose {f₁ g₁ : ℕ → ℝ} {f₂ g₂ : ℕ → ℕ}
    (hstable : StableBigO g₁)
    (houter : f₁ =Θ[atTop] g₁)
    (hinner : (fun x => (f₂ x : ℝ)) =Θ[atTop] fun x => (g₂ x : ℝ))
    (hf₂ : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun x => (f₂ x : ℝ))
    (hmono : EventuallyMonoNorm g₁) :
    (fun x => f₁ (f₂ x)) =Θ[atTop] fun x => g₁ (g₂ x) := by
  have htendf : Tendsto (norm ∘ fun x => (f₂ x : ℝ)) atTop atTop :=
    (isLittleO_one_left_iff ℝ).mp hf₂
  have htendg : Tendsto (norm ∘ fun x => (g₂ x : ℝ)) atTop atTop :=
    hinner.tendsto_norm_atTop_iff.mp htendf
  have hg₂ : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun x => (g₂ x : ℝ) :=
    (isLittleO_one_left_iff ℝ).mpr htendg
  exact ⟨bigOCompose hstable houter.1 hinner.1 hf₂ hg₂ hmono,
    bigOmegaCompose hstable houter.2 hinner.2 hf₂ hg₂ hmono⟩

/-- Source `bigTheta_compose_linear` (line 500). -/
theorem bigThetaComposeLinear {f₁ g₁ : ℕ → ℝ} {f₂ : ℕ → ℕ}
    (hstable : StableBigO g₁) (hmono : EventuallyMonoNorm g₁)
    (houter : f₁ =Θ[atTop] g₁)
    (hinner : (fun x => (f₂ x : ℝ)) =Θ[atTop] fun x => (x : ℝ)) :
    (fun x => f₁ (f₂ x)) =Θ[atTop] g₁ := by
  have hid : Tendsto (norm ∘ fun x : ℕ => (x : ℝ)) atTop atTop := by
    simpa [Function.comp_def] using tendsto_natCast_atTop_atTop
  have hf₂t : Tendsto (norm ∘ fun x => (f₂ x : ℝ)) atTop atTop :=
    hinner.tendsto_norm_atTop_iff.mpr hid
  have hf₂ : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun x => (f₂ x : ℝ) :=
    (isLittleO_one_left_iff ℝ).mpr hf₂t
  simpa using bigThetaCompose hstable houter hinner hf₂ hmono

/-- Source polylog-linear wrapper `bigTheta_compose_linear'` (line 515). -/
theorem bigThetaComposePolylogLinear {f₁ g₁ : ℕ → ℝ} {f₂ : ℕ → ℕ}
    (hstable : StableBigO g₁) (hmono : EventuallyMonoNorm g₁)
    (houter : f₁ =Θ[atTop] g₁)
    (hinner : (fun x => (f₂ x : ℝ)) =Θ[atTop] fun x => polylog 1 0 x) :
    (fun x => f₁ (f₂ x)) =Θ[atTop] g₁ := by
  apply bigThetaComposeLinear hstable hmono houter
  simpa [polylog] using hinner

/-! ## Arithmetic operations -/

private theorem natLeTwiceMulDiv {c x : ℕ} (hc : 0 < c) (hx : c < x) :
    x ≤ 2 * c * (x / c) := by
  have hmod : x % c < c := Nat.mod_lt x hc
  have hdiv : 0 < x / c := Nat.div_pos (by omega) hc
  calc
    x = x % c + c * (x / c) := (Nat.mod_add_div x c).symm
    _ ≤ c + c * (x / c) := by omega
    _ ≤ c * (x / c) + c * (x / c) := by
      gcongr
      exact Nat.le_mul_of_pos_right c hdiv
    _ = 2 * c * (x / c) := by ring

/-- Source `asym_bound_div` (line 527), preserving natural division before casting. -/
theorem asymBoundDiv {c : ℕ} {f : ℕ → ℕ} {g : ℕ → ℝ}
    (hc : 0 < c)
    (hlinear : IsBigOmega atTop (fun x => (f x : ℝ)) (fun x => (x : ℝ)))
    (hfg : (fun x => (f x : ℝ)) =Θ[atTop] g) :
    (fun x => ((f x / c : ℕ) : ℝ)) =Θ[atTop] g := by
  have hupper : (fun x => ((f x / c : ℕ) : ℝ)) =O[atTop]
      fun x => (f x : ℝ) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall fun x => by
      simpa only [norm_natCast, one_mul, Nat.cast_le] using Nat.div_le_self (f x) c
  obtain ⟨N, hN⟩ := fbig (c := c + 1) hlinear
  have hlower : (fun x => (f x : ℝ)) =O[atTop]
      fun x => ((f x / c : ℕ) : ℝ) := by
    apply IsBigO.of_bound (2 * c)
    filter_upwards [eventually_ge_atTop N] with x hx
    have hcx : c < f x := by
      have := hN x hx
      omega
    have hnat := natLeTwiceMulDiv hc hcx
    simp only [norm_natCast]
    exact_mod_cast hnat
  exact ⟨hupper.trans hfg.1, hfg.2.trans hlower⟩

/-- Source `asym_bound_div_linear` (line 589). -/
theorem asymBoundDivLinear {c : ℕ} {f : ℕ → ℕ} (hc : 0 < c)
    (hf : (fun x => (f x : ℝ)) =Θ[atTop] fun x => (x : ℝ)) :
    (fun x => ((f x / c : ℕ) : ℝ)) =Θ[atTop] fun x => (x : ℝ) :=
  asymBoundDiv hc hf.2 hf

/-- Source `asym_bound_diff` (line 594), preserving truncated natural subtraction. -/
theorem asymBoundDiff {f g : ℕ → ℕ}
    (hf : (fun x => (f x : ℝ)) =Θ[atTop] fun x => (x : ℝ))
    (hg : (fun x => (g x : ℝ)) =Θ[atTop] fun _ => (1 : ℝ)) :
    (fun x => ((f x - g x : ℕ) : ℝ)) =Θ[atTop] fun x => (x : ℝ) := by
  have hupper : (fun x => ((f x - g x : ℕ) : ℝ)) =O[atTop]
      fun x => (f x : ℝ) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall fun x => by
      simpa only [norm_natCast, one_mul, Nat.cast_le] using Nat.sub_le (f x) (g x)
  obtain ⟨cg, hcg, ng, hgBound⟩ := bigOE hg.1
  obtain ⟨cf, hcf, nf, hfBound⟩ := bigOmegaE hf.2
  let N := max (max nf ng) ⌈2 * cg / cf⌉₊
  have hlower : (fun x : ℕ => (x : ℝ)) =O[atTop]
      fun x => ((f x - g x : ℕ) : ℝ) := by
    apply IsBigO.of_bound (2 / cf)
    filter_upwards [eventually_ge_atTop N] with x hx
    have hxnf : nf ≤ x := (le_max_left nf ng).trans (le_max_left _ _ |>.trans hx)
    have hxng : ng ≤ x := (le_max_right nf ng).trans (le_max_left _ _ |>.trans hx)
    have hxceil : ⌈2 * cg / cf⌉₊ ≤ x := (le_max_right (max nf ng) _).trans hx
    have hgx : (g x : ℝ) ≤ cg := by
      have := hgBound x hxng
      simpa only [norm_natCast, norm_one, mul_one] using this
    have hfx : cf * (x : ℝ) ≤ (f x : ℝ) := by
      have := hfBound x hxnf
      simpa only [norm_natCast] using this
    have hlarge : 2 * cg / cf ≤ (x : ℝ) :=
      (Nat.le_ceil (2 * cg / cf)).trans (by exact_mod_cast hxceil)
    have hgf : g x ≤ f x := by
      have htwocg : 2 * cg ≤ cf * (x : ℝ) := by
        simpa [mul_comm] using (div_le_iff₀ hcf).mp hlarge
      have hreal : (g x : ℝ) ≤ (f x : ℝ) := by linarith
      exact_mod_cast hreal
    rw [norm_natCast, Nat.cast_sub hgf]
    have htwog : 2 * (g x : ℝ) ≤ (f x : ℝ) := by
      have : 2 * cg ≤ cf * (x : ℝ) := by
        simpa [mul_comm] using (div_le_iff₀ hcf).mp hlarge
      linarith
    have hdiff : 0 ≤ (f x : ℝ) - g x := sub_nonneg.mpr (by exact_mod_cast hgf)
    rw [Real.norm_of_nonneg hdiff]
    rw [show 2 / cf * ((f x : ℝ) - g x) =
      (2 * ((f x : ℝ) - g x)) / cf by ring]
    exact (le_div_iff₀ hcf).2 (by nlinarith)
  exact ⟨hupper.trans hf.1, hlower⟩

/-! ## Ceiling and logarithms -/

/-- Source `ceiling_Theta` (lines 642--643), using mathlib's ceiling equivalence. -/
theorem ceilingTheta {f g : ℕ → ℝ}
    (hfNonneg : EventuallyNonnegative atTop f)
    (hgrowth : (fun _ : ℕ => (1 : ℝ)) =o[atTop] g)
    (hfg : f =Θ[atTop] g) :
    (fun n => ((⌈f n⌉₊ : ℕ) : ℝ)) =Θ[atTop] g := by
  have hgTop : Tendsto (norm ∘ g) atTop atTop := (isLittleO_one_left_iff ℝ).mp hgrowth
  have hfNormTop : Tendsto (norm ∘ f) atTop atTop :=
    hfg.tendsto_norm_atTop_iff.mpr hgTop
  have hfTop : Tendsto f atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hfNormTop.eventually_ge_atTop (max b 0), hfNonneg] with x hx hfx
    rw [Function.comp_apply, Real.norm_of_nonneg hfx] at hx
    exact (le_max_left b 0).trans hx
  have hceil : (fun n => ((⌈f n⌉₊ : ℕ) : ℝ)) =Θ[atTop] f := by
    simpa [Function.comp_def] using
      (Asymptotics.isEquivalent_nat_ceil.comp_tendsto hfTop).isTheta
  exact hceil.trans hfg

/-- Source `eventually_nonneg_logplus` (line 689). -/
theorem eventNonnegLogPlus {c : ℝ} {d : ℕ} (hc : 0 ≤ c) :
    EventuallyNonnegative atTop (fun n => c * Real.logb 2 (d + n : ℕ)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply mul_nonneg hc
  apply Real.logb_nonneg (by norm_num)
  exact_mod_cast (show 1 ≤ d + n by omega)

private theorem logbTwoThetaLog :
    (fun n : ℕ => Real.logb 2 (n : ℝ)) =Θ[atTop]
      fun n => Real.log (n : ℝ) := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simpa [Real.logb, div_eq_mul_inv, mul_comm] using
    (isTheta_refl (fun n : ℕ => Real.log (n : ℝ)) atTop).const_mul_left
      (inv_ne_zero hlog2)

/-- Source helper `log_2_asym'` (line 693). -/
theorem log2AsymHelper {f : ℕ → ℕ}
    (hf : (fun x => (f x : ℝ)) =Θ[atTop] fun x => (x : ℝ)) :
    (fun n => Real.logb 2 (f n : ℕ)) =Θ[atTop]
      fun n => Real.log (n : ℝ) := by
  exact bigThetaComposeLinear stableBigOLog eventMonoLog logbTwoThetaLog hf

private theorem natShiftThetaLinear (d : ℕ) :
    (fun n => ((d + n : ℕ) : ℝ)) =Θ[atTop] fun n => (n : ℝ) := by
  constructor
  · apply IsBigO.of_bound (d + 1)
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [norm_natCast, Nat.cast_add]
    have hnat : d + n ≤ (d + 1) * n := by nlinarith
    exact_mod_cast hnat
  · apply IsBigO.of_bound 1
    exact Eventually.of_forall fun n => by
      simpa only [norm_natCast, one_mul, Nat.cast_le] using Nat.le_add_left n d

/-- Source `log_2_asym` (line 699). -/
theorem log2Asym (d : ℕ) :
    (fun n => Real.logb 2 (d + n : ℕ)) =Θ[atTop]
      fun n => Real.log (n : ℝ) :=
  log2AsymHelper (natShiftThetaLinear d)

/-- Source `abcd_lnx` (line 703). -/
theorem abcdLog {a b c : ℝ} {d : ℕ}
    (_ha : 0 ≤ a) (hb : 1 ≤ b) (hc : 0 < c) (_hd : 0 ≤ d) :
    (fun n => a + b * ((⌈c * Real.logb 2 (d + n : ℕ)⌉₊ : ℕ) : ℝ)) =Θ[atTop]
      fun n => Real.log (n : ℝ) := by
  have hlog := log2Asym d
  have hscaled : (fun n => c * Real.logb 2 (d + n : ℕ)) =Θ[atTop]
      (fun n => Real.log (n : ℝ)) := hlog.const_mul_left hc.ne'
  have hlogGrowth : (fun _ : ℕ => (1 : ℝ)) =o[atTop]
      fun n => Real.log (n : ℝ) := by
    simpa using (Real.isLittleO_const_log_atTop (c := (1 : ℝ))).natCast_atTop
  have hceil : (fun n => ((⌈c * Real.logb 2 (d + n : ℕ)⌉₊ : ℕ) : ℝ)) =Θ[atTop]
      (fun n => Real.log (n : ℝ)) :=
    ceilingTheta (eventNonnegLogPlus hc.le) hlogGrowth hscaled
  have hmain : (fun n => b * ((⌈c * Real.logb 2 (d + n : ℕ)⌉₊ : ℕ) : ℝ)) =Θ[atTop]
      (fun n => Real.log (n : ℝ)) := hceil.const_mul_left (by linarith)
  have hconst : (fun _ : ℕ => a) =o[atTop] fun n => Real.log (n : ℝ) := by
    simpa using (Real.isLittleO_const_log_atTop (c := a)).natCast_atTop
  simpa only [Pi.add_apply] using hconst.add_isTheta hmain

/-- Source `log2_gt_zero` (line 725). -/
theorem log2Nonnegative {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Real.logb 2 x :=
  Real.logb_nonneg (by norm_num) hx

/-! ## Theta addition for any filter -/

/-- Source `Theta_plus` (line 730), rendered as preservation of theta relations. -/
theorem thetaAdd {α : Type*} {l : Filter α} {f₁ f₂ g₁ g₂ : α → ℝ}
    (hf₁ : EventuallyNonnegative l f₁) (hf₂ : EventuallyNonnegative l f₂)
    (hg₁ : EventuallyNonnegative l g₁) (hg₂ : EventuallyNonnegative l g₂)
    (hf : f₁ =Θ[l] f₂) (hg : g₁ =Θ[l] g₂) :
    (fun x => f₁ x + g₁ x) =Θ[l] fun x => f₂ x + g₂ x := by
  constructor
  · have h := hf.1.add_add hg.1
    refine h.congr' EventuallyEq.rfl ?_
    filter_upwards [hf₂, hg₂] with x hfx hgx
    simp [Real.norm_of_nonneg hfx, Real.norm_of_nonneg hgx]
  · have h := hf.2.add_add hg.2
    refine h.congr' EventuallyEq.rfl ?_
    filter_upwards [hf₁, hg₁] with x hfx hgx
    simp [Real.norm_of_nonneg hfx, Real.norm_of_nonneg hgx]

/-- Source function-addition wrapper `Theta_plus'` (line 781). -/
theorem thetaAddFn {α : Type*} {l : Filter α} {f₁ f₂ g₁ g₂ : α → ℝ}
    (hf₁ : EventuallyNonnegative l f₁) (hf₂ : EventuallyNonnegative l f₂)
    (hg₁ : EventuallyNonnegative l g₁) (hg₂ : EventuallyNonnegative l g₂)
    (hf : f₁ =Θ[l] f₂) (hg : g₁ =Θ[l] g₂) :
    (f₁ + g₁) =Θ[l] (f₂ + g₂) := by
  simpa only [Pi.add_apply] using thetaAdd hf₁ hf₂ hg₁ hg₂ hf hg

/-! ## Named normalization rules -/

/-- Source `landau_norms(1)` (line 796). -/
theorem landauNormsOne (x : ℕ) : (1 : ℝ) = polylog 0 0 x := by
  simp [polylog]

/-- Source `landau_norms(2)` (line 796). -/
theorem landauNormsLinear (x : ℕ) : (x : ℝ) = polylog 1 0 x := by
  simp [polylog]

/-- Source `landau_norms(3)` (line 796). -/
theorem landauNormsLog (x : ℕ) : Real.log (x : ℝ) = polylog 0 1 x := by
  simp [polylog]

/-- Source `landau_norms(4)` (line 796). -/
theorem landauNormsPow (a x : ℕ) : ((x ^ a : ℕ) : ℝ) = polylog a 0 x := by
  simp [polylog]

/-- Source `landau_norms(5)` (line 796). -/
theorem landauNormsLogPow (b x : ℕ) :
    Real.log (x : ℝ) ^ b = polylog 0 b x := by
  simp [polylog]

/-- Source `landau_norms(6)` (line 796). -/
theorem landauNormsMul (a₁ b₁ a₂ b₂ x : ℕ) :
    polylog a₁ b₁ x * polylog a₂ b₂ x = polylog (a₁ + a₂) (b₁ + b₂) x := by
  simp only [polylog, pow_add]
  ring

/-- Source `plus_absorb1'` (line 805). -/
theorem plusAbsorbLeft {α : Type*} {l : Filter α} {f g : α → ℝ}
    (h : f =o[l] g) : (f + g) =Θ[l] g :=
  h.add_isTheta isTheta_rfl

/-- Source `plus_absorb2'` (line 808). -/
theorem plusAbsorbRight {α : Type*} {l : Filter α} {f g : α → ℝ}
    (h : g =o[l] f) : (f + g) =Θ[l] f :=
  isTheta_rfl.add_isLittleO h

/-- Source `plus_absorb_same'` (line 811). -/
theorem plusAbsorbSame {α : Type*} {l : Filter α} {f : α → ℝ} :
    (f + f) =Θ[l] f := by
  simpa [two_mul] using
    (isTheta_refl f l).const_mul_left (show (2 : ℝ) ≠ 0 by norm_num)

/-- Source `bigtheta_add` (line 814), with casts after natural addition. -/
theorem bigThetaAdd {α : Type*} {l : Filter α} {f₁ f₂ : α → ℕ} {g₁ g₂ : α → ℝ}
    (hg₁ : EventuallyNonnegative l g₁) (hg₂ : EventuallyNonnegative l g₂)
    (hf₁ : (fun x => (f₁ x : ℝ)) =Θ[l] g₁)
    (hf₂ : (fun x => (f₂ x : ℝ)) =Θ[l] g₂) :
    (fun x => ((f₁ x + f₂ x : ℕ) : ℝ)) =Θ[l] fun x => g₁ x + g₂ x := by
  have hn₁ : EventuallyNonnegative l (fun x => (f₁ x : ℝ)) :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _
  have hn₂ : EventuallyNonnegative l (fun x => (f₂ x : ℝ)) :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _
  simpa only [Nat.cast_add] using thetaAdd hn₁ hg₁ hn₂ hg₂ hf₁ hf₂

/-- Source `landau_norm_linear` (line 830). -/
theorem landauNormLinear : polylog 1 0 = fun x : ℕ => (x : ℝ) := by
  funext x
  simp [polylog]

/-- Source `landau_norm_const` (line 833). -/
theorem landauNormConst : polylog 0 0 = fun _ : ℕ => (1 : ℝ) := by
  funext x
  simp [polylog]

/-- Source `landau_norm_times` (line 836). -/
theorem landauNormTimes (a₁ b₁ a₂ b₂ : ℕ) :
    (fun x => polylog a₁ b₁ x * polylog a₂ b₂ x) =
      polylog (a₁ + a₂) (b₁ + b₂) := by
  funext x
  exact landauNormsMul a₁ b₁ a₂ b₂ x

/-- Source `bigtheta_const` (line 840). -/
theorem bigThetaConst {c : ℕ} (hc : 0 < c) :
    (fun _ : ℕ => (c : ℝ)) =Θ[atTop] polylog 0 0 := by
  rw [landauNormConst]
  exact
    (isTheta_const_const (l := atTop) (show (c : ℝ) ≠ 0 by positivity)
      (show (1 : ℝ) ≠ 0 by norm_num))

/-- Source `bigtheta_linear` (line 844). -/
theorem bigThetaLinear :
    (fun x : ℕ => (x : ℝ)) =Θ[atTop] polylog 1 0 := by
  rw [landauNormLinear]

/-- Source `bigtheta_mult` (line 848). -/
theorem bigThetaMul {α : Type*} {l : Filter α} {f₁ f₂ : α → ℕ} {g₁ g₂ : α → ℝ}
    (hf₁ : (fun x => (f₁ x : ℝ)) =Θ[l] g₁)
    (hf₂ : (fun x => (f₂ x : ℝ)) =Θ[l] g₂) :
    (fun x => ((f₁ x * f₂ x : ℕ) : ℝ)) =Θ[l] fun x => g₁ x * g₂ x := by
  simpa only [Nat.cast_mul] using hf₁.mul hf₂

/-! ## Positive acceptance gates -/

private theorem natScaleThetaLinear {k : ℕ} (hk : 0 < k) :
    (fun n => ((k * n : ℕ) : ℝ)) =Θ[atTop] fun n => (n : ℝ) := by
  constructor
  · apply IsBigO.of_bound k
    exact Eventually.of_forall fun n => by simp [Nat.cast_mul]
  · apply IsBigO.of_bound 1
    exact Eventually.of_forall fun n => by
      simp only [norm_natCast, one_mul, Nat.cast_le]
      exact Nat.le_mul_of_pos_left n hk

private theorem thetaLinearCompositionGate :
    (fun n : ℕ => ((2 * n : ℕ) : ℝ)) =Θ[atTop] fun n => (n : ℝ) := by
  exact bigThetaComposeLinear stableBigOLinear eventMonoLinear
    (isTheta_refl (fun n : ℕ => (n : ℝ)) atTop) (natScaleThetaLinear (by omega))

private theorem natDivisionAndDifferenceGate :
    ((fun n : ℕ => ((((6 * n : ℕ) / 3 : ℕ)) : ℝ)) =Θ[atTop]
      fun n => (n : ℝ)) ∧
    ((fun n : ℕ => (((2 * n : ℕ) - 3 : ℕ) : ℝ)) =Θ[atTop]
      fun n => (n : ℝ)) := by
  constructor
  · exact asymBoundDivLinear (by omega) (natScaleThetaLinear (by omega))
  · apply asymBoundDiff (natScaleThetaLinear (by omega))
    exact isTheta_const_const (by norm_num) (by norm_num)

private theorem ceilingLogThetaGate :
    (fun n : ℕ => ((⌈Real.logb 2 (1 + n : ℕ)⌉₊ : ℕ) : ℝ)) =Θ[atTop]
      fun n => Real.log (n : ℝ) := by
  simpa using abcdLog (a := 0) (b := 1) (c := 1) (d := 1)
    (by norm_num) (by norm_num) (by norm_num) (by omega)

private theorem thetaAdditionGate :
    (fun n : ℕ => (n : ℝ) + (n : ℝ) ^ 2) =Θ[atTop]
      fun n => (n : ℝ) + (n : ℝ) ^ 2 := by
  have hlin : EventuallyNonnegative atTop (fun n : ℕ => (n : ℝ)) :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _
  have hsq : EventuallyNonnegative atTop (fun n : ℕ => (n : ℝ) ^ 2) :=
    Eventually.of_forall fun _ => sq_nonneg _
  exact thetaAdd hlin hlin hsq hsq isTheta_rfl isTheta_rfl

private theorem concreteNormalizationGate :
    (fun n : ℕ => ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 3) *
      ((n : ℝ) * Real.log (n : ℝ) ^ 4)) = polylog 3 7 := by
  simpa [polylog] using landauNormTimes 2 3 1 4

/-! ## Kernel-three axiom guards -/

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigOmegaCompose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigOmegaCompose

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigOCompose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigOCompose

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigThetaCompose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigThetaCompose

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigThetaComposeLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigThetaComposeLinear

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.asymBoundDiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymBoundDiv

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.asymBoundDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymBoundDiff

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.ceilingTheta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ceilingTheta

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.log2Asym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log2Asym

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.abcdLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abcdLog

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.thetaAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thetaAdd

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigThetaAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigThetaAdd

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigThetaMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigThetaMul

end Lax13Proofs.Refine.Asymptotics1D
