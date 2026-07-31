import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# One-dimensional asymptotic foundations

This file ports the scheduled public family from
`Asymptotics/Asymptotics_1D.thy` at
`bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`,
lines 7--384.  Isabelle's `f \<in> \<Omega>[F](g)` is represented faithfully by
the reverse mathlib big-O judgment `g =O[F] f`.

Source-to-Lean table (38 declarations: 5 definitions and 33 theorems):

* source substrate `eventually_nonneg` -> `EventuallyNonnegative` (local source-shaped surface)
* 7 `event_nonneg_real` -> `eventNonnegReal`
* 10 `event_nonneg_ln` -> `eventNonnegLog`
* 14 `event_nonneg_ln_pow` -> `eventNonnegLogPow`
* 17 `event_nonneg_add'` -> `eventNonnegAdd`
* 21 `event_nonneg_mult'` -> `eventNonnegMul`
* 27 `polylog` -> `polylog`
* 30 `event_nonneg_polylog` -> `eventNonnegPolylog`
* 37 `poly_log_compare` -> `polylogCompare`
* 43 `stablebigO` -> `StableBigO`
* 46 `stablebiOI` -> `stableBigOI`
* 50 `stablebigOD` -> `stableBigOD`
* 59 `stablebigO_linear` -> `stableBigOLinear`
* 62 `stablebigO_poly` -> `stableBigOPoly`
* 65 `stablebigO_ln` -> `stableBigOLog`
* 68 `stablebigO_lnpower` -> `stableBigOLogPow`
* 71 `stablebigO_mult` -> `stableBigOMul`
* 107 `stablebigO_mult'` -> `stableBigOMul'`
* 117 `stable_polylog` -> `stablePolylog`
* 127 `stablebigO_plus` -> `stableBigOAdd`
* 164 `event_mono` -> `EventuallyMonoNorm`
* 167 `event_mono_linear` -> `eventMonoLinear`
* 170 `event_mono_poly` -> `eventMonoPoly`
* 174 `event_mono_ln` -> `eventMonoLog`
* 178 `event_mono_lnpower` -> `eventMonoLogPow`
* 182--185 `event_mono_plus` -> `eventMonoAdd`
* 211--212 `event_mono_mult` -> `eventMonoMul`
* 229 `event_mono_polylog` -> `eventMonoPolylog`
* source notation `\<Omega>[F]` -> `IsBigOmega` (reverse-big-O rendering)
* 239 `bigomegaI` -> `bigOmegaI`
* 253 `bigOmegaE` -> `bigOmegaE`
* 265 `bigOE` -> `bigOE`
* 277 `bigOE_nat` -> `bigOENat`
* 295 `bigOmegaE_nat` -> `bigOmegaENat`
* 320 `fsmall'` -> `fsmallReal`
* 334 `fsmall_ev` -> `fsmallEventually`
* 350 `fsmall` -> `fsmall`
* 363 `fbig` -> `fbig`
-/

open Filter
open scoped Topology

namespace Lax13Proofs.Refine.Asymptotics1D

open Asymptotics

/-- Source-shaped eventual nonnegativity surface. -/
def EventuallyNonnegative {α : Type*} (l : Filter α) (f : α → ℝ) : Prop :=
  ∀ᶠ x in l, 0 ≤ f x

/-- Polynomial-logarithmic normal form `x^a (log x)^b`. -/
noncomputable def polylog (a b x : ℕ) : ℝ :=
  (x : ℝ) ^ a * Real.log (x : ℝ) ^ b

/-- Stability under every strictly positive natural rescaling. -/
def StableBigO (f : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → (fun x => f (d * x)) =O[atTop] f

/-- Eventual monotonicity of the norm along `atTop`. -/
def EventuallyMonoNorm (f : ℕ → ℝ) : Prop :=
  ∀ᶠ x₁ in atTop, ∀ x₂ ≥ x₁, ‖f x₁‖ ≤ ‖f x₂‖

/-- Isabelle's big-Omega surface, rendered as reverse mathlib big-O. -/
def IsBigOmega {α E F : Type*} [Norm E] [Norm F]
    (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  g =O[l] f

/-! ## Falsification controls

These private controls pin the three side conditions that the source uses.
They are deliberately proved before any authored source adaptation below.
-/

/-- Reversing the strict lexicographic comparison would claim that linear growth is little-o(1). -/
private theorem reversedPolylogComparisonFails :
    ¬((fun n : ℕ => polylog 1 0 n) =o[atTop] fun n => polylog 0 0 n) := by
  intro h
  have hb := h.bound (c := 1) zero_lt_one
  rw [eventually_atTop] at hb
  obtain ⟨N, hN⟩ := hb
  have bad := hN (max N 2) (le_max_left _ _)
  simp only [polylog, pow_one, pow_zero, mul_one, norm_natCast, norm_one] at bad
  norm_num at bad

private def zeroSpike (n : ℕ) : ℝ :=
  if n = 0 then 1 else 0

private theorem zeroSpikeStable : StableBigO zeroSpike := by
  intro d hd
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : n ≠ 0 := by omega
  have hdn0 : d * n ≠ 0 := Nat.mul_ne_zero (by omega) hn0
  simp [zeroSpike, hn0, hdn0]

/-- Positive scaling is essential: the zero rescaling of a stable spike is not big-O of it. -/
private theorem zeroScalingFails :
    ¬((fun n : ℕ => zeroSpike (0 * n)) =O[atTop] zeroSpike) := by
  intro h
  have hz := h.eq_zero_imp
  rw [eventually_atTop] at hz
  obtain ⟨N, hN⟩ := hz
  have bad := hN (max N 1) (le_max_left _ _)
  have hm0 : max N 1 ≠ 0 := by omega
  simp [zeroSpike, hm0] at bad

private theorem alternatingNormMono :
    EventuallyMonoNorm (fun n : ℕ => (-1 : ℝ) ^ n) := by
  simp [EventuallyMonoNorm]

/-- Norm-monotone summands need not have a norm-monotone sum without nonnegativity. -/
private theorem sumWithoutNonnegativityFails :
    EventuallyMonoNorm (fun _n : ℕ => (1 : ℝ)) ∧
      EventuallyMonoNorm (fun n : ℕ => (-1 : ℝ) ^ n) ∧
      ¬EventuallyMonoNorm (fun n : ℕ => (1 : ℝ) + (-1 : ℝ) ^ n) := by
  refine ⟨by simp [EventuallyMonoNorm], alternatingNormMono, ?_⟩
  intro h
  rw [EventuallyMonoNorm, eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  have bad := hN (2 * N) (by omega) (2 * N + 1) (by omega)
  norm_num [pow_succ, pow_mul] at bad

/-! ## Eventually nonnegative and polynomial-logarithmic normal forms -/

/-- Source `event_nonneg_real` (line 7). -/
theorem eventNonnegReal {α : Type*} {l : Filter α} {f : α → ℕ} :
    EventuallyNonnegative l (fun x => (f x : ℝ)) := by
  exact Eventually.of_forall fun _ => Nat.cast_nonneg _

/-- Source `event_nonneg_ln` (line 10). -/
theorem eventNonnegLog :
    EventuallyNonnegative atTop (fun x : ℕ => Real.log (x : ℝ)) := by
  exact Eventually.of_forall Real.log_natCast_nonneg

/-- Source `event_nonneg_ln_pow` (line 14). -/
theorem eventNonnegLogPow (m : ℕ) :
    EventuallyNonnegative atTop (fun x : ℕ => Real.log (x : ℝ) ^ m) := by
  exact eventNonnegLog.mono fun _ hx => pow_nonneg hx _

/-- Source `event_nonneg_add'` (line 17). -/
theorem eventNonnegAdd {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : EventuallyNonnegative l f) (hg : EventuallyNonnegative l g) :
    EventuallyNonnegative l (fun x => f x + g x) := by
  exact hf.and hg |>.mono fun _ h => add_nonneg h.1 h.2

/-- Source `event_nonneg_mult'` (line 21). -/
theorem eventNonnegMul {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : EventuallyNonnegative l f) (hg : EventuallyNonnegative l g) :
    EventuallyNonnegative l (fun x => f x * g x) := by
  exact hf.and hg |>.mono fun _ h => mul_nonneg h.1 h.2

/-- Source `event_nonneg_polylog` (line 30). -/
theorem eventNonnegPolylog (a b : ℕ) :
    EventuallyNonnegative atTop (fun x => polylog a b x) := by
  exact (eventNonnegReal (f := fun x : ℕ => x ^ a)).and (eventNonnegLogPow b) |>.mono
    fun _ h => by simpa [polylog] using mul_nonneg h.1 h.2

/-- Source `poly_log_compare` (line 37): strict lexicographic growth of `polylog`. -/
theorem polylogCompare {a₁ a₂ b₁ b₂ : ℕ}
    (hlex : a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂)) :
    (fun x => polylog a₁ b₁ x) =o[atTop] fun x => polylog a₂ b₂ x := by
  rcases hlex with ha | ⟨rfl, hb⟩
  · have hd : 0 < a₂ - a₁ := Nat.sub_pos_of_lt ha
    have hlogId :
        (fun n : ℕ => Real.log (n : ℝ) ^ b₁) =o[atTop] fun n => (n : ℝ) :=
      Real.isLittleO_pow_log_id_atTop.natCast_atTop
    have hidPow :
        (fun n : ℕ => (n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ (a₂ - a₁) := by
      apply IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop 1] with n hn
      simp only [norm_natCast, norm_pow, one_mul]
      exact le_self_pow₀ (mod_cast hn) hd.ne'
    have hlogPow :
        (fun n : ℕ => Real.log (n : ℝ) ^ b₁) =o[atTop]
          fun n => (n : ℝ) ^ (a₂ - a₁) :=
      hlogId.trans_isBigO hidPow
    have hpoly :
        (fun n : ℕ => (n : ℝ) ^ a₁ * Real.log (n : ℝ) ^ b₁) =o[atTop]
          fun n => (n : ℝ) ^ a₂ := by
      refine ((isBigO_refl (fun n : ℕ => (n : ℝ) ^ a₁) atTop).mul_isLittleO hlogPow).congr_right ?_
      intro n
      rw [← pow_add]
      congr
      omega
    have honeLog :
        (fun n : ℕ => (1 : ℝ)) =O[atTop] fun n => Real.log (n : ℝ) ^ b₂ := by
      simpa using
        ((Real.isLittleO_const_log_atTop (c := (1 : ℝ))).isBigO.natCast_atTop.pow b₂)
    have htarget :
        (fun n : ℕ => (n : ℝ) ^ a₂) =O[atTop]
          fun n => (n : ℝ) ^ a₂ * Real.log (n : ℝ) ^ b₂ := by
      simpa using (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a₂) atTop).mul honeLog
    simpa [polylog] using hpoly.trans_isBigO htarget
  · have hlog :
        (fun n : ℕ => Real.log (n : ℝ) ^ b₁) =o[atTop]
          fun n => Real.log (n : ℝ) ^ b₂ :=
      (isLittleO_pow_pow_atTop_of_lt hb).comp_tendsto
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa [polylog] using
      (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a₁) atTop).mul_isLittleO hlog

/-! ## Stability in one variable -/

/-- Source `stablebiOI` (line 46). -/
theorem stableBigOI {f : ℕ → ℝ}
    (h : ∀ d : ℕ, 0 < d → (fun x => f (d * x)) =O[atTop] f) :
    StableBigO f :=
  h

/-- Source `stablebigOD` (line 50), exposing a positive eventual-bound constant. -/
theorem stableBigOD {f : ℕ → ℝ} (hf : StableBigO f) {d : ℕ} (hd : 0 < d) :
    ∃ c > 0, ∀ᶠ x in atTop, ‖f (d * x)‖ ≤ c * ‖f x‖ := by
  exact isBigO_iff'.mp (hf d hd)

/-- Source `stablebigO_linear` (line 59). -/
theorem stableBigOLinear : StableBigO (fun n : ℕ => (n : ℝ)) := by
  intro d _hd
  apply IsBigO.of_bound (d : ℝ)
  exact Eventually.of_forall fun n => by simp [Nat.cast_mul]

/-- Source `stablebigO_poly` (line 62). -/
theorem stableBigOPoly (m : ℕ) : StableBigO (fun n : ℕ => (n : ℝ) ^ m) := by
  intro d _hd
  apply IsBigO.of_bound ((d : ℝ) ^ m)
  exact Eventually.of_forall fun n => by simp [Nat.cast_mul, mul_pow]

/-- Source `stablebigO_ln` (line 65). -/
theorem stableBigOLog : StableBigO (fun n : ℕ => Real.log (n : ℝ)) := by
  intro d _hd
  simpa [Nat.cast_mul] using
    (Real.isBigO_log_const_mul_log_atTop (d : ℝ)).natCast_atTop

/-- Source `stablebigO_lnpower` (line 68). -/
theorem stableBigOLogPow (m : ℕ) :
    StableBigO (fun n : ℕ => Real.log (n : ℝ) ^ m) := by
  intro d hd
  simpa using (stableBigOLog d hd).pow m

/-- Source `stablebigO_mult` (line 71). -/
theorem stableBigOMul {f g : ℕ → ℝ}
    (hf : StableBigO f) (hg : StableBigO g)
    (_evf : EventuallyNonnegative atTop f) (_evg : EventuallyNonnegative atTop g) :
    StableBigO (fun x => f x * g x) := by
  intro d hd
  exact (hf d hd).mul (hg d hd)

/-- Source lambda-shaped wrapper `stablebigO_mult'` (line 107). -/
theorem stableBigOMul' {f g : ℕ → ℝ}
    (hf : StableBigO f) (hg : StableBigO g)
    (evf : EventuallyNonnegative atTop f) (evg : EventuallyNonnegative atTop g) :
    StableBigO (fun x => f x * g x) :=
  stableBigOMul hf hg evf evg

/-- Source `stable_polylog` (line 117). -/
theorem stablePolylog (a b : ℕ) : StableBigO (fun x => polylog a b x) := by
  have hp : EventuallyNonnegative atTop (fun x : ℕ => (x : ℝ) ^ a) := by
    simpa using (eventNonnegReal (l := atTop) (f := fun x : ℕ => x ^ a))
  simpa [polylog] using stableBigOMul'
    (stableBigOPoly a) (stableBigOLogPow b)
    hp (eventNonnegLogPow b)

/-- Source `stablebigO_plus` (line 127). -/
theorem stableBigOAdd {f g : ℕ → ℝ}
    (hf : StableBigO f) (hg : StableBigO g)
    (evf : EventuallyNonnegative atTop f) (evg : EventuallyNonnegative atTop g) :
    StableBigO (fun x => f x + g x) := by
  intro d hd
  have hsum := (hf d hd).add_add (hg d hd)
  refine hsum.congr' EventuallyEq.rfl ?_
  filter_upwards [evf, evg] with x hfx hgx
  simp [Real.norm_of_nonneg hfx, Real.norm_of_nonneg hgx]

/-! ## Eventual norm-monotonicity in one variable -/

/-- Source `event_mono_linear` (line 167). -/
theorem eventMonoLinear : EventuallyMonoNorm (fun n : ℕ => (n : ℝ)) := by
  exact Eventually.of_forall fun n₁ n₂ h₁₂ => by simpa using h₁₂

/-- Source `event_mono_poly` (line 170). -/
theorem eventMonoPoly (m : ℕ) : EventuallyMonoNorm (fun n : ℕ => (n : ℝ) ^ m) := by
  exact Eventually.of_forall fun n₁ n₂ h₁₂ => by
    simp only [norm_pow, norm_natCast]
    exact pow_le_pow_left₀ (show 0 ≤ (n₁ : ℝ) by positivity)
      (show (n₁ : ℝ) ≤ (n₂ : ℝ) by exact_mod_cast h₁₂) m

/-- Source `event_mono_ln` (line 174). -/
theorem eventMonoLog : EventuallyMonoNorm (fun n : ℕ => Real.log (n : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1] with n₁ hn₁
  intro n₂ h₁₂
  rw [Real.norm_of_nonneg (Real.log_natCast_nonneg n₁),
    Real.norm_of_nonneg (Real.log_natCast_nonneg n₂)]
  exact Real.log_le_log (by exact_mod_cast hn₁) (by exact_mod_cast h₁₂)

/-- Source `event_mono_lnpower` (line 178). -/
theorem eventMonoLogPow (m : ℕ) :
    EventuallyMonoNorm (fun n : ℕ => Real.log (n : ℝ) ^ m) := by
  filter_upwards [eventMonoLog] with n₁ hn₁
  intro n₂ h₁₂
  simp only [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hn₁ n₂ h₁₂) m

/-- Source `event_mono_plus` (lines 182--185). -/
theorem eventMonoAdd {f g : ℕ → ℝ}
    (hf : EventuallyMonoNorm f) (hg : EventuallyMonoNorm g)
    (evf : EventuallyNonnegative atTop f) (evg : EventuallyNonnegative atTop g) :
    EventuallyMonoNorm (fun x => f x + g x) := by
  obtain ⟨Nf, hNf⟩ := eventually_atTop.mp evf
  obtain ⟨Ng, hNg⟩ := eventually_atTop.mp evg
  filter_upwards [hf, hg, eventually_ge_atTop Nf, eventually_ge_atTop Ng]
    with n₁ hfm hgm hn₁f hn₁g
  intro n₂ h₁₂
  have hf₁ : 0 ≤ f n₁ := hNf n₁ hn₁f
  have hg₁ : 0 ≤ g n₁ := hNg n₁ hn₁g
  have hf₂ : 0 ≤ f n₂ := hNf n₂ (hn₁f.trans h₁₂)
  have hg₂ : 0 ≤ g n₂ := hNg n₂ (hn₁g.trans h₁₂)
  simpa [Real.norm_of_nonneg hf₁, Real.norm_of_nonneg hg₁,
    Real.norm_of_nonneg hf₂, Real.norm_of_nonneg hg₂,
    Real.norm_of_nonneg (add_nonneg hf₁ hg₁),
    Real.norm_of_nonneg (add_nonneg hf₂ hg₂)] using
      add_le_add (hfm n₂ h₁₂) (hgm n₂ h₁₂)

/-- Source `event_mono_mult` (lines 211--212). -/
theorem eventMonoMul {f g : ℕ → ℝ}
    (hf : EventuallyMonoNorm f) (hg : EventuallyMonoNorm g) :
    EventuallyMonoNorm (fun x => f x * g x) := by
  filter_upwards [hf, hg] with n₁ hfm hgm
  intro n₂ h₁₂
  simp only [norm_mul]
  exact mul_le_mul (hfm n₂ h₁₂) (hgm n₂ h₁₂) (norm_nonneg _) (norm_nonneg _)

/-- Source `event_mono_polylog` (line 229). -/
theorem eventMonoPolylog (a b : ℕ) :
    EventuallyMonoNorm (fun x => polylog a b x) := by
  simpa [polylog] using eventMonoMul (eventMonoPoly a) (eventMonoLogPow b)

/-! ## Source-facing Landau introduction and extraction -/

/-- Source `bigomegaI` (line 239). -/
theorem bigOmegaI {α E F : Type*} [Norm E] [Norm F]
    {l : Filter α} {f : α → E} {g : α → F} {c : ℝ}
    (h : ∀ᶠ x in l, ‖g x‖ ≤ c * ‖f x‖) :
    IsBigOmega l f g := by
  exact IsBigO.of_bound c h

/-- Source `bigOmegaE` (line 253). -/
theorem bigOmegaE {f g : ℕ → ℝ} (h : IsBigOmega atTop f g) :
    ∃ c > 0, ∃ n, ∀ x ≥ n, c * ‖g x‖ ≤ ‖f x‖ := by
  obtain ⟨c, hc, hev⟩ := isBigO_iff''.mp h
  obtain ⟨n, hn⟩ := eventually_atTop.mp hev
  exact ⟨c, hc, n, hn⟩

/-- Source `bigOE` (line 265). -/
theorem bigOE {f g : ℕ → ℝ} (h : f =O[atTop] g) :
    ∃ c > 0, ∃ n, ∀ x ≥ n, ‖f x‖ ≤ c * ‖g x‖ := by
  obtain ⟨c, hc, hev⟩ := isBigO_iff'.mp h
  obtain ⟨n, hn⟩ := eventually_atTop.mp hev
  exact ⟨c, hc, n, hn⟩

/-- Source `bigOE_nat` (line 277), with the natural-valued functions cast explicitly. -/
theorem bigOENat {f g : ℕ → ℕ}
    (h : (fun x => (f x : ℝ)) =O[atTop] fun x => (g x : ℝ)) :
    ∃ c > 0, ∃ n, ∀ x ≥ n, f x ≤ c * g x := by
  obtain ⟨C, hC, hev⟩ := isBigO_iff'.mp h
  obtain ⟨n, hn⟩ := eventually_atTop.mp hev
  let c : ℕ := ⌈C⌉₊
  have hc : 0 < c := Nat.ceil_pos.mpr hC
  refine ⟨c, hc, n, fun x hx => ?_⟩
  have hbound := hn x hx
  simp only [norm_natCast] at hbound
  have hceil : C ≤ (c : ℝ) := Nat.le_ceil C
  have hreal : (f x : ℝ) ≤ (c : ℝ) * (g x : ℝ) :=
    hbound.trans (mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg _))
  exact_mod_cast hreal

/-- Source `bigOmegaE_nat` (line 295), with explicit natural casts at the Ω boundary. -/
theorem bigOmegaENat {f g : ℕ → ℕ}
    (h : IsBigOmega atTop (fun x => (f x : ℝ)) (fun x => (g x : ℝ))) :
    ∃ c > 0, ∃ n, ∀ x ≥ n, g x ≤ c * f x := by
  exact bigOENat h

/-! ## Eventual-growth consequences -/

/-- Source `fsmall'` (line 320), renamed `fsmallReal` to expose its codomain. -/
theorem fsmallReal {f : ℕ → ℝ} {c : ℝ}
    (h : (fun _ : ℕ => (1 : ℝ)) =o[atTop] f) (_hc : 0 ≤ c) :
    ∃ n, ∀ x ≥ n, c ≤ ‖f x‖ := by
  have ht : Tendsto (fun x => ‖f x‖) atTop atTop :=
    (isLittleO_one_left_iff ℝ).mp h
  obtain ⟨n, hn⟩ := eventually_atTop.mp (ht.eventually_ge_atTop c)
  exact ⟨n, hn⟩

/-- Source `fsmall_ev` (line 334), renamed `fsmallEventually`. -/
theorem fsmallEventually {f : ℕ → ℕ} {c : ℕ}
    (h : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun x => (f x : ℝ)) :
    ∀ᶠ x in atTop, c ≤ f x := by
  have ht : Tendsto (fun x => ‖(f x : ℝ)‖) atTop atTop :=
    (isLittleO_one_left_iff ℝ).mp h
  have hev := ht.eventually_ge_atTop (c : ℝ)
  filter_upwards [hev] with x hx
  simpa only [norm_natCast, Nat.cast_le] using hx

/-- Source `fsmall` (line 350). -/
theorem fsmall {f : ℕ → ℕ} {c : ℕ}
    (h : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun x => (f x : ℝ)) :
    ∃ n, ∀ x ≥ n, c ≤ f x := by
  exact eventually_atTop.mp (fsmallEventually h)

/-- Source `fbig` (line 363). -/
theorem fbig {f : ℕ → ℕ} {c : ℕ}
    (h : IsBigOmega atTop (fun x => (f x : ℝ)) (fun x => (x : ℝ))) :
    ∃ n, ∀ x ≥ n, c ≤ f x := by
  obtain ⟨k, hk, N, hN⟩ := bigOmegaENat (f := f) (g := fun x => x) h
  refine ⟨max N (k * c), fun x hx => ?_⟩
  have hNx : N ≤ x := (le_max_left N (k * c)).trans hx
  have hkcx : k * c ≤ x := (le_max_right N (k * c)).trans hx
  have hchain : k * c ≤ k * f x := hkcx.trans (hN x hNx)
  exact le_of_mul_le_mul_left hchain hk

/-! ## Positive acceptance gates -/

private theorem polylogOneZeroLinearGate :
    (fun n : ℕ => polylog 1 0 n) =Θ[atTop] fun n => (n : ℝ) := by
  constructor <;>
    simpa [polylog] using (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)

private theorem strictPolylogGate :
    (fun n : ℕ => polylog 1 5 n) =o[atTop] fun n => polylog 2 0 n :=
  polylogCompare (Or.inl (by omega))

private theorem stableSumProductGate :
    StableBigO (fun n : ℕ => (n : ℝ) + (n : ℝ)) ∧
      StableBigO (fun n : ℕ => (n : ℝ) * (n : ℝ)) := by
  have hnonneg : EventuallyNonnegative atTop (fun n : ℕ => (n : ℝ)) :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _
  exact ⟨stableBigOAdd stableBigOLinear stableBigOLinear hnonneg hnonneg,
    stableBigOMul stableBigOLinear stableBigOLinear hnonneg hnonneg⟩

private theorem eventMonoSumProductGate :
    EventuallyMonoNorm (fun n : ℕ => (n : ℝ) + (n : ℝ)) ∧
      EventuallyMonoNorm (fun n : ℕ => (n : ℝ) * (n : ℝ)) := by
  have hnonneg : EventuallyNonnegative atTop (fun n : ℕ => (n : ℝ)) :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _
  exact ⟨eventMonoAdd eventMonoLinear eventMonoLinear hnonneg hnonneg,
    eventMonoMul eventMonoLinear eventMonoLinear⟩

private theorem bigOAndOmegaExtractorGate :
    (∃ c > 0, ∃ n : ℕ, ∀ x ≥ n,
      ‖(x : ℝ)‖ ≤ c * ‖(x : ℝ)‖) ∧
    (∃ c > 0, ∃ n : ℕ, ∀ x ≥ n,
      c * ‖(x : ℝ)‖ ≤ ‖(x : ℝ)‖) := by
  constructor
  · exact bigOE (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  · exact bigOmegaE (show IsBigOmega atTop (fun n : ℕ => (n : ℝ))
      (fun n : ℕ => (n : ℝ)) from isBigO_refl _ _)

/-! ## Kernel-three axiom guards -/

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.polylogCompare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polylogCompare

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.stablePolylog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stablePolylog

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.stableBigOAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stableBigOAdd

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.eventMonoPolylog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventMonoPolylog

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.eventMonoAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventMonoAdd

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigOmegaI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigOmegaI

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigOmegaE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigOmegaE

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigOENat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigOENat

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.bigOmegaENat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigOmegaENat

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.fsmallReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fsmallReal

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.fsmallEventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fsmallEventually

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.fsmall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fsmall

/-- info: 'Lax13Proofs.Refine.Asymptotics1D.fbig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fbig

end Lax13Proofs.Refine.Asymptotics1D
