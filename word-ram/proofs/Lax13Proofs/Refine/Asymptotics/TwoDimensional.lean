import Lax13Proofs.Refine.Asymptotics.OneDimensionalOperations
import Mathlib.Order.Filter.AtTopBot.Prod

/-!
# Two-dimensional asymptotic foundations and lifting

This file ports the live public declarations from `Asymptotics_2D.thy` at
`bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`,
lines 5--270, 467--559, and 638--669.  The carrier is the genuine product
filter `atTop ×ˢ atTop`; it is not a diagonal limit.

Source-to-Lean table (26 declarations: four aliases, three definitions, and
nineteen theorems):

* 5 `O₂` -> `IsBigO2`
* 6 `o₂` -> `IsLittleO2`
* 7 `Θ₂` -> `IsTheta2`
* 8 `Ω₂` -> `IsBigOmega2` (reverse-big-O rendering)
* 12 `polylog2` -> `polylog2`
* 15 `event_nonneg_polylog2` -> `eventNonnegPolylog2`
* 23 `stablebigO2` -> `StableBigO2`
* 26 `stablebigO2I` -> `stableBigO2I`
* 34 `stablebigO2_mult` -> `stableBigO2Mul`
* 71 `stablebigO2D'` -> `stableBigO2Extract`
* 84 `stablebigO2D` -> `stableBigO2ExtractPair`
* 97 `stablebigO2_plus` -> `stableBigO2Add`
* 133 `stable_polylog2` -> `stablePolylog2`
* 142 `event_mono2` -> `EventuallyMonoNorm2`
* 145 `event_mono2_mult` -> `eventMono2Mul`
* 173 `event_mono2_polylog2` -> `eventMono2Polylog2`
* 180 `event_mono2_plus` -> `eventMono2Add`
* 214 `bigO2E` -> `bigO2E`
* 226 `bigOmega2E` -> `bigOmega2E`
* 240 `mult_bivariate_I` -> `multBivariateI`
* 467 `oO_o` -> `oO_o`
* 490 `Oo_o` -> `Oo_o`
* 515 `mult_Theta_bivariate` -> `multThetaBivariate`
* 638 `mult_Theta_bivariate'` -> `multThetaBivariatePolylog`
* 649 `mult_Theta_bivariate1` -> `multThetaBivariateFst`
* 660 `mult_Theta_bivariate2` -> `multThetaBivariateSnd`
-/

open Filter
open scoped Topology

namespace Lax13Proofs.Refine.Asymptotics2D

open Asymptotics
open Lax13Proofs.Refine.Asymptotics1D

/-! ## Product-filter faces -/

/-- The genuine independent two-coordinate limit. -/
abbrev productAtTop : Filter (ℕ × ℕ) := atTop ×ˢ atTop

/-- Source abbreviation `O₂` (line 5). -/
abbrev IsBigO2 (f g : ℕ × ℕ → ℝ) : Prop := f =O[productAtTop] g

/-- Source abbreviation `o₂` (line 6). -/
abbrev IsLittleO2 (f g : ℕ × ℕ → ℝ) : Prop := f =o[productAtTop] g

/-- Source abbreviation `Θ₂` (line 7). -/
abbrev IsTheta2 (f g : ℕ × ℕ → ℝ) : Prop := f =Θ[productAtTop] g

/-- Source abbreviation `Ω₂` (line 8), represented as reverse big-O. -/
abbrev IsBigOmega2 (f g : ℕ × ℕ → ℝ) : Prop := IsBigOmega productAtTop f g

private theorem eventuallyProductAtTopIff {P : ℕ × ℕ → Prop} :
    (∀ᶠ p in productAtTop, P p) ↔
      ∃ N, ∀ n m, N ≤ n → N ≤ m → P (n, m) := by
  change (∀ᶠ p in atTop ×ˢ atTop, P p) ↔ _
  rw [prod_atTop_atTop_eq, eventually_atTop_prod_self]

/-! ## Polynomial-logarithmic normal form -/

/-- Source `polylog2` (line 12). -/
noncomputable def polylog2 (a b c d : ℕ) (p : ℕ × ℕ) : ℝ :=
  polylog a b p.1 * polylog c d p.2

/-- Source `event_nonneg_polylog2` (line 15). -/
theorem eventNonnegPolylog2 (a b c d : ℕ) :
    EventuallyNonnegative productAtTop (polylog2 a b c d) := by
  exact (eventNonnegPolylog a b).prod_mk (eventNonnegPolylog c d) |>.mono
    fun p h => by simpa [polylog2] using mul_nonneg h.1 h.2

/-! ## Stability under independent rescaling -/

/-- Source `stablebigO2` (line 23). -/
def StableBigO2 (f : ℕ × ℕ → ℝ) : Prop :=
  ∀ c d : ℕ, 0 < c → 0 < d →
    (fun p => f (c * p.1, d * p.2)) =O[productAtTop] f

/-- Source `stablebigO2I` (line 26). -/
theorem stableBigO2I {f : ℕ × ℕ → ℝ}
    (h : ∀ c d : ℕ, 0 < c → 0 < d →
      (fun p => f (c * p.1, d * p.2)) =O[productAtTop] f) :
    StableBigO2 f :=
  h

/-- Source `stablebigO2_mult` (line 34). -/
theorem stableBigO2Mul {f g : ℕ → ℝ}
    (hf : StableBigO f) (hg : StableBigO g) :
    StableBigO2 (fun p => f p.1 * g p.2) := by
  intro c d hc hd
  have hf' : (fun p : ℕ × ℕ => f (c * p.1)) =O[productAtTop] fun p => f p.1 := by
    simpa [productAtTop, Function.comp_def] using
      (hf c hc).comp_fst (atTop : Filter ℕ)
  have hg' : (fun p : ℕ × ℕ => g (d * p.2)) =O[productAtTop] fun p => g p.2 := by
    simpa [productAtTop, Function.comp_def] using
      (hg d hd).comp_snd (atTop : Filter ℕ)
  simpa [Function.comp_def] using hf'.mul hg'

/-- Source `stablebigO2D'` (line 71), in projection form. -/
theorem stableBigO2Extract {f : ℕ × ℕ → ℝ}
    (hf : StableBigO2 f) {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ∃ c > 0, ∀ᶠ p in productAtTop,
      ‖f (d₁ * p.1, d₂ * p.2)‖ ≤ c * ‖f p‖ := by
  exact isBigO_iff'.mp (hf d₁ d₂ hd₁ hd₂)

/-- Source `stablebigO2D` (line 84), with an explicit pair lambda. -/
theorem stableBigO2ExtractPair {f : ℕ × ℕ → ℝ}
    (hf : StableBigO2 f) {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ∃ c > 0, ∀ᶠ p in productAtTop,
      ‖f (d₁ * p.1, d₂ * p.2)‖ ≤ c * ‖f (p.1, p.2)‖ := by
  simpa using stableBigO2Extract hf hd₁ hd₂

/-- Source `stablebigO2_plus` (line 97). -/
theorem stableBigO2Add {f g : ℕ × ℕ → ℝ}
    (hf : StableBigO2 f) (hg : StableBigO2 g)
    (evf : EventuallyNonnegative productAtTop f)
    (evg : EventuallyNonnegative productAtTop g) :
    StableBigO2 (fun p => f p + g p) := by
  intro d₁ d₂ hd₁ hd₂
  have hsum := (hf d₁ d₂ hd₁ hd₂).add_add (hg d₁ d₂ hd₁ hd₂)
  refine hsum.congr' EventuallyEq.rfl ?_
  filter_upwards [evf, evg] with p hfp hgp
  simp [Real.norm_of_nonneg hfp, Real.norm_of_nonneg hgp]

/-- Source `stable_polylog2` (line 133). -/
theorem stablePolylog2 (a b c d : ℕ) : StableBigO2 (polylog2 a b c d) := by
  simpa [polylog2] using stableBigO2Mul (stablePolylog a b) (stablePolylog c d)

/-! ## Eventual norm-monotonicity in the product order -/

/-- Source `event_mono2` (line 142). -/
def EventuallyMonoNorm2 (f : ℕ × ℕ → ℝ) : Prop :=
  ∀ᶠ p in productAtTop, ∀ n ≥ p.1, ∀ m ≥ p.2, ‖f p‖ ≤ ‖f (n, m)‖

/-- Source `event_mono2_mult` (line 145). -/
theorem eventMono2Mul {f g : ℕ → ℝ}
    (hf : EventuallyMonoNorm f) (hg : EventuallyMonoNorm g) :
    EventuallyMonoNorm2 (fun p => f p.1 * g p.2) := by
  filter_upwards [hf.prod_mk hg] with p hp
  intro n hn m hm
  simp only [norm_mul]
  exact mul_le_mul (hp.1 n hn) (hp.2 m hm) (norm_nonneg _) (norm_nonneg _)

/-- Source `event_mono2_polylog2` (line 173). -/
theorem eventMono2Polylog2 (a b c d : ℕ) :
    EventuallyMonoNorm2 (polylog2 a b c d) := by
  simpa [polylog2] using eventMono2Mul (eventMonoPolylog a b) (eventMonoPolylog c d)

private theorem eventuallyFutureNonnegative2 {f : ℕ × ℕ → ℝ}
    (hf : EventuallyNonnegative productAtTop f) :
    ∀ᶠ p in productAtTop, ∀ n ≥ p.1, ∀ m ≥ p.2, 0 ≤ f (n, m) := by
  rw [EventuallyNonnegative, eventuallyProductAtTopIff] at hf
  obtain ⟨N, hN⟩ := hf
  rw [eventuallyProductAtTopIff]
  exact ⟨N, fun n m hn hm n' hn' m' hm' => hN n' m' (hn.trans hn') (hm.trans hm')⟩

/-- Source `event_mono2_plus` (line 180). -/
theorem eventMono2Add {f g : ℕ × ℕ → ℝ}
    (hf : EventuallyMonoNorm2 f) (hg : EventuallyMonoNorm2 g)
    (evf : EventuallyNonnegative productAtTop f)
    (evg : EventuallyNonnegative productAtTop g) :
    EventuallyMonoNorm2 (fun p => f p + g p) := by
  filter_upwards [hf, hg, evf, evg, eventuallyFutureNonnegative2 evf,
    eventuallyFutureNonnegative2 evg] with p hfm hgm hfp hgp hff hgf
  intro n hn m hm
  have hfn : 0 ≤ f (n, m) := hff n hn m hm
  have hgn : 0 ≤ g (n, m) := hgf n hn m hm
  simpa [Real.norm_of_nonneg hfp, Real.norm_of_nonneg hgp,
    Real.norm_of_nonneg hfn, Real.norm_of_nonneg hgn,
    Real.norm_of_nonneg (add_nonneg hfp hgp),
    Real.norm_of_nonneg (add_nonneg hfn hgn)] using
      add_le_add (hfm n hn m hm) (hgm n hn m hm)

/-! ## Two-dimensional bound extraction -/

/-- Source `bigO2E` (line 214). -/
theorem bigO2E {f g : ℕ × ℕ → ℝ} (h : IsBigO2 f g) :
    ∃ c > 0, ∃ N, ∀ p, N ≤ p.1 → N ≤ p.2 → ‖f p‖ ≤ c * ‖g p‖ := by
  obtain ⟨c, hc, hev⟩ := isBigO_iff'.mp h
  rw [eventuallyProductAtTopIff] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨c, hc, N, fun p hp₁ hp₂ => hN p.1 p.2 hp₁ hp₂⟩

/-- Source `bigOmega2E` (line 226). -/
theorem bigOmega2E {f g : ℕ × ℕ → ℝ} (h : IsBigOmega2 f g) :
    ∃ c > 0, ∃ N, ∀ p, N ≤ p.1 → N ≤ p.2 → c * ‖g p‖ ≤ ‖f p‖ := by
  obtain ⟨c, hc, hev⟩ := isBigO_iff''.mp h
  rw [eventuallyProductAtTopIff] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨c, hc, N, fun p hp₁ hp₂ => hN p.1 p.2 hp₁ hp₂⟩

private theorem tendstoNatMulProductAtTop :
    Tendsto (fun p : ℕ × ℕ => p.1 * p.2) productAtTop atTop := by
  rw [tendsto_atTop]
  intro N
  rw [eventuallyProductAtTopIff]
  refine ⟨max N 1, fun n m hn hm => ?_⟩
  have hNn : N ≤ n := (le_max_left N 1).trans hn
  have hmpos : 0 < m := by omega
  exact hNn.trans (Nat.le_mul_of_pos_right n hmpos)

/-- Source `mult_bivariate_I` (line 240), preserving multiplication before casting. -/
theorem multBivariateI {f : ℕ → ℕ}
    (hf : (fun n => (f n : ℝ)) =Θ[atTop] fun n => (n : ℝ)) :
    (fun p : ℕ × ℕ => (f (p.1 * p.2) : ℝ)) =Θ[productAtTop]
      fun p => ((p.1 * p.2 : ℕ) : ℝ) := by
  exact ⟨hf.1.comp_tendsto tendstoNatMulProductAtTop,
    hf.2.comp_tendsto tendstoNatMulProductAtTop⟩

/-! ## Coordinate lifting and multiplication -/

/-- Source `oO_o` (line 467). -/
theorem oO_o {f₁ f₂ g₁ g₂ : ℕ → ℝ}
    (h₁ : f₁ =o[atTop] g₁) (h₂ : f₂ =O[atTop] g₂) :
    (fun p : ℕ × ℕ => f₁ p.1 * f₂ p.2) =o[productAtTop]
      fun p => g₁ p.1 * g₂ p.2 := by
  simpa [Function.comp_def] using
    (h₁.comp_fst atTop).mul_isBigO (h₂.comp_snd atTop)

/-- Source `Oo_o` (line 490). -/
theorem Oo_o {f₁ f₂ g₁ g₂ : ℕ → ℝ}
    (h₁ : f₁ =O[atTop] g₁) (h₂ : f₂ =o[atTop] g₂) :
    (fun p : ℕ × ℕ => f₁ p.1 * f₂ p.2) =o[productAtTop]
      fun p => g₁ p.1 * g₂ p.2 := by
  simpa [Function.comp_def] using
    (h₁.comp_fst atTop).mul_isLittleO (h₂.comp_snd atTop)

/-- Source `mult_Theta_bivariate` (line 515). -/
theorem multThetaBivariate {f₁ f₂ : ℕ → ℕ} {g₁ g₂ : ℕ → ℝ}
    (h₁ : (fun n => (f₁ n : ℝ)) =Θ[atTop] g₁)
    (h₂ : (fun n => (f₂ n : ℝ)) =Θ[atTop] g₂) :
    (fun p : ℕ × ℕ => ((f₁ p.1 * f₂ p.2 : ℕ) : ℝ)) =Θ[productAtTop]
      fun p => g₁ p.1 * g₂ p.2 := by
  simpa [Function.comp_def, Nat.cast_mul] using
    (h₁.comp_fst atTop).mul (h₂.comp_snd atTop)

/-- Source polylog wrapper `mult_Theta_bivariate'` (line 638). -/
theorem multThetaBivariatePolylog {f₁ f₂ : ℕ → ℕ} {a b c d : ℕ}
    (h₁ : (fun n => (f₁ n : ℝ)) =Θ[atTop] fun n => polylog a b n)
    (h₂ : (fun n => (f₂ n : ℝ)) =Θ[atTop] fun n => polylog c d n) :
    (fun p : ℕ × ℕ => ((f₁ p.1 * f₂ p.2 : ℕ) : ℝ)) =Θ[productAtTop]
      polylog2 a b c d := by
  simpa [polylog2] using multThetaBivariate h₁ h₂

/-- Source `mult_Theta_bivariate1` (line 649). -/
theorem multThetaBivariateFst {f : ℕ → ℕ} {a b : ℕ}
    (hf : (fun n => (f n : ℝ)) =Θ[atTop] fun n => polylog a b n) :
    (fun p : ℕ × ℕ => (f p.1 : ℝ)) =Θ[productAtTop] polylog2 a b 0 0 := by
  have hone : (fun _ : ℕ => ((1 : ℕ) : ℝ)) =Θ[atTop] fun n => polylog 0 0 n :=
    bigThetaConst (by omega)
  simpa [polylog2] using multThetaBivariatePolylog hf hone

/-- Source `mult_Theta_bivariate2` (line 660). -/
theorem multThetaBivariateSnd {f : ℕ → ℕ} {a b : ℕ}
    (hf : (fun n => (f n : ℝ)) =Θ[atTop] fun n => polylog a b n) :
    (fun p : ℕ × ℕ => (f p.2 : ℝ)) =Θ[productAtTop] polylog2 0 0 a b := by
  have hone : (fun _ : ℕ => ((1 : ℕ) : ℝ)) =Θ[atTop] fun n => polylog 0 0 n :=
    bigThetaConst (by omega)
  simpa [polylog2] using multThetaBivariatePolylog hone hf

/-! ## Positive acceptance gates -/

private theorem independentThresholdGate (a b : ℕ) :
    ∀ᶠ p : ℕ × ℕ in productAtTop, a ≤ p.1 ∧ b ≤ p.2 := by
  rw [eventuallyProductAtTopIff]
  exact ⟨max a b, fun n m hn hm =>
    ⟨le_max_left a b |>.trans hn, le_max_right a b |>.trans hm⟩⟩

private theorem coordinateLiftGate :
    ((fun p : ℕ × ℕ => (p.1 : ℝ)) =Θ[productAtTop] fun p => (p.1 : ℝ)) ∧
      ((fun p : ℕ × ℕ => (p.2 : ℝ)) =Θ[productAtTop] fun p => (p.2 : ℝ)) := by
  exact ⟨(isTheta_refl _ atTop).comp_fst atTop, (isTheta_refl _ atTop).comp_snd atTop⟩

private theorem extractionGate :
    (∃ c > 0, ∃ N, ∀ p : ℕ × ℕ, N ≤ p.1 → N ≤ p.2 →
      ‖(p.1 : ℝ)‖ ≤ c * ‖(p.1 : ℝ)‖) ∧
    (∃ c > 0, ∃ N, ∀ p : ℕ × ℕ, N ≤ p.1 → N ≤ p.2 →
      c * ‖(p.2 : ℝ)‖ ≤ ‖(p.2 : ℝ)‖) := by
  exact ⟨bigO2E (isBigO_refl _ _), bigOmega2E (isBigO_refl _ _)⟩

private theorem littleOLiftingGate :
    ((fun p : ℕ × ℕ => (1 : ℝ) * p.2) =o[productAtTop]
      fun p => (p.1 : ℝ) * p.2) ∧
    ((fun p : ℕ × ℕ => p.1 * (1 : ℝ)) =o[productAtTop]
      fun p => p.1 * (p.2 : ℝ)) := by
  have hsmall : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (n : ℝ) := by
    have ht : Tendsto (norm ∘ fun n : ℕ => (n : ℝ)) atTop atTop := by
      simpa [Function.comp_def] using tendsto_natCast_atTop_atTop
    exact (isLittleO_one_left_iff ℝ).mpr ht
  exact ⟨oO_o hsmall (isBigO_refl _ _), Oo_o (isBigO_refl _ _) hsmall⟩

private theorem thetaMultiplicationGate :
    (fun p : ℕ × ℕ => (((2 * p.1) * (3 * p.2) : ℕ) : ℝ)) =Θ[productAtTop]
      fun p => (p.1 : ℝ) * (p.2 : ℝ) := by
  have htwo : (fun n : ℕ => ((2 * n : ℕ) : ℝ)) =Θ[atTop] fun n => (n : ℝ) := by
    constructor
    · apply IsBigO.of_bound 2
      simp [Nat.cast_mul]
    · apply IsBigO.of_bound 1
      filter_upwards [] with n
      simp only [norm_natCast, one_mul, Nat.cast_le]
      omega
  have hthree : (fun n : ℕ => ((3 * n : ℕ) : ℝ)) =Θ[atTop] fun n => (n : ℝ) := by
    constructor
    · apply IsBigO.of_bound 3
      simp [Nat.cast_mul]
    · apply IsBigO.of_bound 1
      filter_upwards [] with n
      simp only [norm_natCast, one_mul, Nat.cast_le]
      omega
  exact multThetaBivariate htwo hthree

/-! ## Kernel-three axiom guards -/

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.eventNonnegPolylog2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventNonnegPolylog2

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.stableBigO2Mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stableBigO2Mul

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.stableBigO2Add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stableBigO2Add

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.stablePolylog2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stablePolylog2

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.eventMono2Mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventMono2Mul

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.eventMono2Add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventMono2Add

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.bigO2E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigO2E

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.bigOmega2E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bigOmega2E

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.multBivariateI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multBivariateI

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.oO_o' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oO_o

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.Oo_o' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oo_o

/-- info: 'Lax13Proofs.Refine.Asymptotics2D.multThetaBivariate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multThetaBivariate

end Lax13Proofs.Refine.Asymptotics2D
