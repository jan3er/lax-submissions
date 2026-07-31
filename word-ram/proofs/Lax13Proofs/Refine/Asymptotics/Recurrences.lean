import Lax13Proofs.Refine.Asymptotics.TwoDimensionalComposition
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Computability.AkraBazzi.AkraBazzi

/-!
# Linear successor recurrences

This file ports all scheduled declarations from `Asymptotics_Recurrences.thy` at
`bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`,
through line 585.  These are successor recurrences with argument `n - 1`; their
asymptotic ratio is one, so they deliberately use tail induction rather than
mathlib's fixed-shrink Akra--Bazzi interface.

Source-to-Lean table (18 rows: twelve generic declarations and six example rows):

* 7 `K` -> `selfLeMulMul`
* 11 `bigO_linear_recurrence` -> `bigOLinearRecurrence`
* 60 `bigO_linear_recurrence'` -> `bigOLinearRecurrenceGeneral`
* 139 `bigOmega_linear_recurrence` -> `bigOmegaLinearRecurrence`
* 220 `bigOmega_linear_recurrence'` -> `bigOmegaLinearRecurrenceGeneral`
* 313 `chara_ln` -> `succMulLogLe`
* 353 `bigTheta_linear_recurrence_const` -> `bigThetaLinearRecurrenceConst`
* 371 `bigTheta_linear_recurrence_log` -> `bigThetaLinearRecurrenceLog`
* 387 `bigTheta_linear_recurrence` -> `bigThetaLinearRecurrence`
* 403 `bla_time` -> `Examples.blaTime`
* 407 `bla_time_nneg` -> `Examples.blaTimeNonnegative`
* 410 unnamed validation lemma -> private `blaTimeThetaQuadraticGate`
* 416 `bivariate` -> `bivariateBigO`
* 496 `bivariateOmega` -> `bivariateBigOmega`
* 559 `bivariateTheta` -> `bivariateTheta`
* 579 `ex` -> `Examples.bivariateTime`
* 583 `ex_pos` -> `Examples.bivariateTimeNonnegative`
* 585 unnamed validation lemma -> private `bivariateTimeThetaProductGate`

The generated equation and induction declarations for the two recursive
definitions are compiler artifacts, not additional source rows.
-/

open Filter
open scoped Topology

namespace Lax13Proofs.Refine.AsymptoticsRecurrences

open Asymptotics
open Lax13Proofs.Refine.Asymptotics1D
open Lax13Proofs.Refine.Asymptotics2D

/-! Mathlib endpoints relevant to fixed-shrink recurrences, documented rather
than duplicated here. -/
#check AkraBazziRecurrence.asympBound
#check AkraBazziRecurrence.isBigO_asympBound
#check AkraBazziRecurrence.isBigO_symm_asympBound
#check AkraBazziRecurrence.isTheta_asympBound

/-- Source `K` (line 7). -/
theorem selfLeMulMul {a b c : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a ≤ a * b * c := by
  calc
    a = a * 1 * 1 := by ring
    _ ≤ a * b * c := by gcongr

/-- Source generalized `bigO_linear_recurrence'` (line 60). -/
theorem bigOLinearRecurrenceGeneral {f g G : ℕ → ℝ} {N : ℕ}
    (hrec : ∀ i ≥ N, f (i + 1) = f i + g i)
    (hg : g =O[atTop] G)
    (hmono : ∀ x y, N ≤ x → x ≤ y → G x ≤ G y)
    (hpos : ∀ x ≥ N, 0 < G x) :
    f =O[atTop] fun n => (n : ℝ) * G n := by
  obtain ⟨c, hc, Ng, hg⟩ := bigOE hg
  let M := max Ng (N + 1)
  let A : ℝ := max c (‖f M‖ / ((M : ℝ) * G M))
  have hM_N : N ≤ M := by simp [M]
  have hM_pos : 0 < (M : ℝ) * G M := by
    apply mul_pos
    · exact_mod_cast (show 0 < M by simp [M])
    · exact hpos M hM_N
  have hA_nonneg : 0 ≤ A := le_trans hc.le (le_max_left _ _)
  have hcA : c ≤ A := le_max_left _ _
  apply IsBigO.of_bound A
  filter_upwards [eventually_ge_atTop M] with n hn
  have hnN : N ≤ n := hM_N.trans hn
  have hGn : 0 ≤ G n := (hpos n hnN).le
  have hbound : ∀ k ≥ M, ‖f k‖ ≤ A * ((k : ℝ) * G k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        have hratio : ‖f M‖ / ((M : ℝ) * G M) ≤ A := le_max_right _ _
        calc
          ‖f M‖ = (‖f M‖ / ((M : ℝ) * G M)) * ((M : ℝ) * G M) := by
            exact (div_mul_cancel₀ _ hM_pos.ne').symm
          _ ≤ A * ((M : ℝ) * G M) :=
            mul_le_mul_of_nonneg_right hratio hM_pos.le
    | succ k hk ih =>
        have hkN : N ≤ k := hM_N.trans hk
        have hkNg : Ng ≤ k := (le_max_left Ng (N + 1)).trans hk
        have hGk : 0 ≤ G k := (hpos k hkN).le
        have hGmono : G k ≤ G (k + 1) := hmono k (k + 1) hkN (by omega)
        calc
          ‖f (k + 1)‖ = ‖f k + g k‖ := by rw [hrec k hkN]
          _ ≤ ‖f k‖ + ‖g k‖ := norm_add_le _ _
          _ ≤ A * ((k : ℝ) * G k) + c * ‖G k‖ := add_le_add ih (hg k hkNg)
          _ = A * ((k : ℝ) * G k) + c * G k := by rw [Real.norm_of_nonneg hGk]
          _ ≤ A * ((k : ℝ) * G k) + A * G k := by gcongr
          _ = A * (((k + 1 : ℕ) : ℝ) * G k) := by push_cast; ring
          _ ≤ A * (((k + 1 : ℕ) : ℝ) * G (k + 1)) := by gcongr
  simpa [Real.norm_of_nonneg hGn] using hbound n hn

/-- Source `bigO_linear_recurrence` (line 11). -/
theorem bigOLinearRecurrence {f g : ℕ → ℝ} {N : ℕ}
    (hrec : ∀ i ≥ N, f (i + 1) = f i + g i)
    (hg : g =O[atTop] fun n => (n : ℝ)) :
    f =O[atTop] fun n => (n : ℝ) * (n : ℝ) := by
  apply bigOLinearRecurrenceGeneral (N := max N 1)
    (fun i hi => hrec i ((le_max_left N 1).trans hi)) hg
  · intro x y _ hxy
    exact_mod_cast hxy
  · intro x hx
    exact_mod_cast (show 0 < x by omega)

/-- Source generalized `bigOmega_linear_recurrence'` (line 220). -/
theorem bigOmegaLinearRecurrenceGeneral {f g G : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hrec : ∀ i ≥ N, f (i + 1) = f i + g i)
    (hg : IsBigOmega atTop g G)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hg_nonneg : ∀ n, 0 ≤ g n)
    (hGpos : ∀ x ≥ N, 0 < G x)
    (hinc : ∀ n ≥ N,
      (((n + 1 : ℕ) : ℝ) * G (n + 1)) ≤ (n : ℝ) * G n + C * G n)
    (hC : 0 ≤ C) :
    IsBigOmega atTop f (fun n => (n : ℝ) * G n) := by
  obtain ⟨c, hc, Ng, hg⟩ := bigOmegaE hg
  let B := max Ng N
  let M := B + 1
  have hBN : N ≤ B := by simp [B]
  have hBNg : Ng ≤ B := by simp [B]
  have hGN : 0 < G B := hGpos B hBN
  have hgB : c * G B ≤ g B := by
    simpa [Real.norm_of_nonneg hGN.le, Real.norm_of_nonneg (hg_nonneg B)] using hg B hBNg
  have hgBpos : 0 < g B := lt_of_lt_of_le (mul_pos hc hGN) hgB
  have hfMpos : 0 < f M := by
    rw [show M = B + 1 by rfl, hrec B hBN]
    exact add_pos_of_nonneg_of_pos (hf_nonneg B) hgBpos
  have hMN : N ≤ M := hBN.trans (by simp [M])
  have hGMpos : 0 < G M := hGpos M hMN
  let A : ℝ := max (((M : ℝ) * G M) / f M) (C / c)
  have hA_nonneg : 0 ≤ A := by
    apply le_trans (div_nonneg hC hc.le)
    exact le_max_right _ _
  have hApos : 0 < A := by
    have hMreal : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by simp [M])
    apply lt_of_lt_of_le (div_pos (mul_pos hMreal hGMpos) hfMpos)
    exact le_max_left _ _
  apply IsBigO.of_bound A
  filter_upwards [eventually_ge_atTop M] with n hn
  have hnN : N ≤ n := hMN.trans hn
  have hGn : 0 ≤ G n := (hGpos n hnN).le
  have hbound : ∀ k ≥ M, (k : ℝ) * G k ≤ A * f k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        have hratio : ((M : ℝ) * G M) / f M ≤ A := le_max_left _ _
        calc
          (M : ℝ) * G M = (((M : ℝ) * G M) / f M) * f M := by
            exact (div_mul_cancel₀ _ hfMpos.ne').symm
          _ ≤ A * f M := mul_le_mul_of_nonneg_right hratio hfMpos.le
    | succ k hk ih =>
        have hkN : N ≤ k := hMN.trans hk
        have hkNg : Ng ≤ k := hBNg.trans (show B ≤ k by
          exact (show B < M by simp [M]).le.trans hk)
        have hGk : 0 ≤ G k := (hGpos k hkN).le
        have hgk : c * G k ≤ g k := by
          simpa [Real.norm_of_nonneg hGk, Real.norm_of_nonneg (hg_nonneg k)] using hg k hkNg
        have hcoef : C * G k ≤ A * g k := by
          have hCA : C / c ≤ A := le_max_right _ _
          calc
            C * G k = (C / c) * (c * G k) := by field_simp
            _ ≤ (C / c) * g k := mul_le_mul_of_nonneg_left hgk (div_nonneg hC hc.le)
            _ ≤ A * g k := mul_le_mul_of_nonneg_right hCA (hg_nonneg k)
        calc
          (((k + 1 : ℕ) : ℝ) * G (k + 1)) ≤ (k : ℝ) * G k + C * G k := hinc k hkN
          _ ≤ A * f k + A * g k := add_le_add ih hcoef
          _ = A * f (k + 1) := by rw [hrec k hkN]; ring
  have hraw := hbound n hn
  simpa [Real.norm_of_nonneg hGn, Real.norm_of_nonneg (hf_nonneg n),
    mul_nonneg (Nat.cast_nonneg _) hGn] using hraw

/-- Source `bigOmega_linear_recurrence` (line 139). -/
theorem bigOmegaLinearRecurrence {f g : ℕ → ℝ} {N : ℕ}
    (hrec : ∀ i ≥ N, f (i + 1) = f i + g i)
    (hg : IsBigOmega atTop g (fun n => (n : ℝ)))
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hg_nonneg : ∀ n, 0 ≤ g n) :
    IsBigOmega atTop f (fun n => (n : ℝ) * (n : ℝ)) := by
  apply bigOmegaLinearRecurrenceGeneral (N := max N 1) (C := 3)
    (fun i hi => hrec i ((le_max_left N 1).trans hi)) hg hf_nonneg hg_nonneg
  · intro x hx
    exact_mod_cast (show 0 < x by omega)
  · intro n hn
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    push_cast
    nlinarith
  · norm_num

/-- Source `chara_ln` (line 313). -/
theorem succMulLogLe {x : ℝ} (hx : 3 ≤ x) :
    (x + 1) * Real.log (x + 1) ≤ x * Real.log x + 3 * Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hex : Real.exp 1 ≤ x := (Real.exp_one_lt_three.le).trans hx
  have hlog1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hex
  have hinner : 0 < 1 + 1 / x := by positivity
  have hfactor : x + 1 = x * (1 + 1 / x) := by field_simp
  have hlogextra : Real.log (1 + 1 / x) ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos hinner
    linarith
  have hlogsucc : Real.log (x + 1) ≤ Real.log x + 1 / x := by
    rw [hfactor, Real.log_mul hx0.ne' hinner.ne']
    linarith
  have hxlog : x * Real.log (x + 1) ≤ x * Real.log x + 1 := by
    have h := mul_le_mul_of_nonneg_left hlogsucc hx0.le
    field_simp at h ⊢
    nlinarith
  have hinv : 1 / x ≤ Real.log x := by
    have hx1 : 1 ≤ x := by linarith
    have hi : 1 / x ≤ 1 := (div_le_one hx0).2 hx1
    linarith
  have hlogsucc' : Real.log (x + 1) ≤ 2 * Real.log x := by linarith
  nlinarith

/-- Source `bigTheta_linear_recurrence_const` (line 353). -/
theorem bigThetaLinearRecurrenceConst {f g : ℕ → ℝ} {N : ℕ}
    (hrec : ∀ i ≥ N, f (i + 1) = f i + g i)
    (hg : g =Θ[atTop] fun _ => (1 : ℝ))
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hg_nonneg : ∀ n, 0 ≤ g n) :
    f =Θ[atTop] fun n => (n : ℝ) := by
  have hrec' : ∀ i ≥ max N 1, f (i + 1) = f i + g i :=
    fun i hi => hrec i ((le_max_left N 1).trans hi)
  constructor
  · simpa using (bigOLinearRecurrenceGeneral (N := max N 1) hrec' hg.1
      (fun _ _ _ _ => le_rfl) (fun _ _ => zero_lt_one))
  · simpa using (bigOmegaLinearRecurrenceGeneral (N := max N 1) (C := 1)
      hrec' hg.2 hf_nonneg hg_nonneg (fun _ _ => zero_lt_one)
      (fun n _ => by push_cast; ring_nf; norm_num) (by norm_num))

/-- Source `bigTheta_linear_recurrence_log` (line 371). -/
theorem bigThetaLinearRecurrenceLog {f g : ℕ → ℝ} {N : ℕ}
    (hrec : ∀ i ≥ N, f (i + 1) = f i + g i)
    (hg : g =Θ[atTop] fun n => Real.log (n : ℝ))
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hg_nonneg : ∀ n, 0 ≤ g n) :
    f =Θ[atTop] fun n => (n : ℝ) * Real.log (n : ℝ) := by
  let N' := max N 3
  have hrec' : ∀ i ≥ N', f (i + 1) = f i + g i :=
    fun i hi => hrec i ((le_max_left N 3).trans hi)
  have hlogpos : ∀ n ≥ N', 0 < Real.log (n : ℝ) := by
    intro n hn
    apply Real.log_pos
    exact_mod_cast (show 1 < n by simp [N'] at hn ⊢; omega)
  have hlogmono : ∀ x y, N' ≤ x → x ≤ y →
      Real.log (x : ℝ) ≤ Real.log (y : ℝ) := by
    intro x y hx hxy
    have hxpos : 0 < x := by simp [N'] at hx; omega
    exact Real.log_le_log (by exact_mod_cast hxpos) (by exact_mod_cast hxy)
  constructor
  · exact bigOLinearRecurrenceGeneral hrec' hg.1 hlogmono hlogpos
  · apply bigOmegaLinearRecurrenceGeneral (C := 3) hrec' hg.2 hf_nonneg hg_nonneg hlogpos
    · intro n hn
      simpa [Nat.cast_add, Nat.cast_one] using
        (succMulLogLe (x := (n : ℝ)) (by exact_mod_cast (show 3 ≤ n by
          exact (le_max_right N 3).trans hn)))
    · norm_num

/-- Source `bigTheta_linear_recurrence` (line 387). -/
theorem bigThetaLinearRecurrence {f g : ℕ → ℝ} {N : ℕ}
    (hrec : ∀ i ≥ N, f (i + 1) = f i + g i)
    (hg : g =Θ[atTop] fun n => (n : ℝ))
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hg_nonneg : ∀ n, 0 ≤ g n) :
    f =Θ[atTop] fun n => (n : ℝ) * (n : ℝ) :=
  ⟨bigOLinearRecurrence hrec hg.1,
    bigOmegaLinearRecurrence hrec hg.2 hf_nonneg hg_nonneg⟩

namespace Examples

/-- Source `bla_time` (line 403). -/
def blaTime : ℕ → ℝ
  | 0 => 1
  | n + 1 => blaTime n + n

/-- Source `bla_time_nneg` (line 407). -/
theorem blaTimeNonnegative (n : ℕ) : 0 ≤ blaTime n := by
  induction n with
  | zero => simp [blaTime]
  | succ n ih => simp only [blaTime]; positivity

end Examples

/-- Source unnamed validation theorem (line 410). -/
private theorem blaTimeThetaQuadraticGate :
    Examples.blaTime =Θ[atTop] fun n => (n : ℝ) * (n : ℝ) := by
  apply bigThetaLinearRecurrence (N := 0) (g := fun n => (n : ℝ))
  · intro i _
    simp [Examples.blaTime]
  · exact isTheta_refl _ _
  · exact Examples.blaTimeNonnegative
  · exact fun _ => Nat.cast_nonneg _

private theorem eventuallyProductAtTopIff {P : ℕ × ℕ → Prop} :
    (∀ᶠ p in productAtTop, P p) ↔
      ∃ K, ∀ n m, K ≤ n → K ≤ m → P (n, m) := by
  change (∀ᶠ p in atTop ×ˢ atTop, P p) ↔ _
  rw [prod_atTop_atTop_eq, eventually_atTop_prod_self]

/-- Source `bivariate` (line 416). The recurrence advances only the first
coordinate, while the conclusion uses the literal product filter. -/
theorem bivariateBigO {f : ℕ × ℕ → ℝ} {g : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hrec : ∀ n m, N ≤ n → f (n + 1, m) = f (n, m) + g m)
    (hbase : ∀ n m, n ≤ N → f (n, m) ≤ C)
    (hg : g =O[atTop] fun m => (m : ℝ))
    (hf_nonneg : EventuallyNonnegative productAtTop f)
    (hC : 0 ≤ C) :
    f =O[productAtTop] fun p => ((p.1 * p.2 : ℕ) : ℝ) := by
  obtain ⟨c, hc, Ng, hg⟩ := bigOE hg
  rw [EventuallyNonnegative, eventuallyProductAtTopIff] at hf_nonneg
  obtain ⟨Npos, hf_nonneg⟩ := hf_nonneg
  have hshift : ∀ k m, f (N + k, m) ≤ C + (k : ℝ) * g m := by
    intro k m
    induction k with
    | zero => simpa using hbase N m le_rfl
    | succ k ih =>
        rw [show N + (k + 1) = (N + k) + 1 by omega, hrec (N + k) m (by omega)]
        push_cast
        linarith
  have hupper : ∀ n m, N ≤ n → f (n, m) ≤ C + ((n - N : ℕ) : ℝ) * g m := by
    intro n m hn
    simpa [Nat.add_sub_of_le hn] using hshift (n - N) m
  let T := max (max Ng Npos) (N + 1)
  apply IsBigO.of_bound (C + c)
  rw [eventuallyProductAtTopIff]
  refine ⟨T, fun n m hn hm => ?_⟩
  have hnN : N ≤ n := (le_max_right (max Ng Npos) (N + 1)).trans hn |>.trans' (by omega)
  have hmNg : Ng ≤ m := (le_max_left Ng Npos).trans
    ((le_max_left (max Ng Npos) (N + 1)).trans hm)
  have hnpos : Npos ≤ n := (le_max_right Ng Npos).trans
    ((le_max_left (max Ng Npos) (N + 1)).trans hn)
  have hmpos : Npos ≤ m := (le_max_right Ng Npos).trans
    ((le_max_left (max Ng Npos) (N + 1)).trans hm)
  have hfn : 0 ≤ f (n, m) := hf_nonneg n m hnpos hmpos
  have hn1 : 1 ≤ n := by simp [T] at hn; omega
  have hm1 : 1 ≤ m := by simp [T] at hm; omega
  have hgm := hg m hmNg
  simp only [norm_natCast] at hgm
  calc
    ‖f (n, m)‖ = f (n, m) := Real.norm_of_nonneg hfn
    _ ≤ C + ((n - N : ℕ) : ℝ) * g m := hupper n m hnN
    _ ≤ C + ((n - N : ℕ) : ℝ) * ‖g m‖ := by
      gcongr
      simpa only [Real.norm_eq_abs] using le_abs_self (g m)
    _ ≤ C + (n : ℝ) * ‖g m‖ := by gcongr; exact_mod_cast Nat.sub_le n N
    _ ≤ C + (n : ℝ) * (c * (m : ℝ)) := by gcongr
    _ ≤ C * ((n : ℝ) * (m : ℝ)) + c * ((n : ℝ) * (m : ℝ)) := by
      have hnm : (1 : ℝ) ≤ (n : ℝ) * (m : ℝ) := by
        exact_mod_cast (show 1 ≤ n * m by exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
      nlinarith [mul_le_mul_of_nonneg_left hnm hC]
    _ = (C + c) * ‖((n * m : ℕ) : ℝ)‖ := by
      rw [Real.norm_of_nonneg (show 0 ≤ (((n * m : ℕ) : ℝ)) by positivity)]
      push_cast
      ring

/-- Source `bivariateOmega` (line 496). The source's base premise is retained,
as is the deliberately redundant second binder of `gpos`. -/
theorem bivariateBigOmega {f : ℕ × ℕ → ℝ} {g : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hrec : ∀ n m, N ≤ n → f (n + 1, m) = f (n, m) + g m)
    (_hbase : ∀ n m, n ≤ N → f (n, m) ≤ C)
    (hg : IsBigOmega atTop g (fun m => (m : ℝ)))
    (hf_nonneg : EventuallyNonnegative productAtTop f)
    (gpos : ∀ n _m : ℕ, 0 ≤ g n)
    (_hC : 0 ≤ C) :
    IsBigOmega2 f (fun p => ((p.1 * p.2 : ℕ) : ℝ)) := by
  obtain ⟨c, hc, Ng, hg⟩ := bigOmegaE hg
  rw [EventuallyNonnegative, eventuallyProductAtTopIff] at hf_nonneg
  obtain ⟨Npos, hf_nonneg⟩ := hf_nonneg
  let B := max N Npos
  have hshift : ∀ m ≥ Npos, ∀ k : ℕ,
      (k : ℝ) * g m ≤ f (B + k, m) := by
    intro m hm k
    induction k with
    | zero =>
        simp only [Nat.cast_zero, zero_mul]
        exact hf_nonneg B m (le_max_right N Npos) hm
    | succ k ih =>
        rw [show B + (k + 1) = (B + k) + 1 by omega,
          hrec (B + k) m ((le_max_left N Npos).trans (Nat.le_add_right B k))]
        push_cast
        linarith
  have hlower : ∀ n m, B ≤ n → Npos ≤ m →
      (((n - B : ℕ) : ℝ) * g m) ≤ f (n, m) := by
    intro n m hn hm
    simpa [Nat.add_sub_of_le hn] using hshift m hm (n - B)
  let T := max (max Ng Npos) (2 * B)
  apply IsBigO.of_bound (2 / c)
  rw [eventuallyProductAtTopIff]
  refine ⟨T, fun n m hn hm => ?_⟩
  have hmNg : Ng ≤ m := (le_max_left Ng Npos).trans
    ((le_max_left (max Ng Npos) (2 * B)).trans hm)
  have hmpos : Npos ≤ m := (le_max_right Ng Npos).trans
    ((le_max_left (max Ng Npos) (2 * B)).trans hm)
  have hn2B : 2 * B ≤ n := (le_max_right (max Ng Npos) (2 * B)).trans hn
  have hnB : B ≤ n := by omega
  have hnpos : Npos ≤ n := (le_max_right N Npos).trans hnB
  have hfn : 0 ≤ f (n, m) := hf_nonneg n m hnpos hmpos
  have hgm : c * (m : ℝ) ≤ g m := by
    simpa [Real.norm_of_nonneg (gpos m 0), norm_natCast] using hg m hmNg
  have hm_le : (m : ℝ) ≤ (1 / c) * g m := by
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hgm)
  have hn_le : (n : ℝ) ≤ 2 * ((n - B : ℕ) : ℝ) := by exact_mod_cast (show n ≤ 2 * (n - B) by omega)
  have hk_nonneg : 0 ≤ ((n - B : ℕ) : ℝ) := Nat.cast_nonneg _
  calc
    ‖((n * m : ℕ) : ℝ)‖ = (n : ℝ) * (m : ℝ) := by simp [Nat.cast_mul]
    _ ≤ (2 * ((n - B : ℕ) : ℝ)) * (m : ℝ) := by gcongr
    _ ≤ (2 * ((n - B : ℕ) : ℝ)) * ((1 / c) * g m) := by gcongr
    _ = (2 / c) * (((n - B : ℕ) : ℝ) * g m) := by ring
    _ ≤ (2 / c) * f (n, m) := by
      exact mul_le_mul_of_nonneg_left (hlower n m hnB hmpos)
        (div_nonneg (by norm_num) hc.le)
    _ = (2 / c) * ‖f (n, m)‖ := by rw [Real.norm_of_nonneg hfn]

/-- Source `bivariateTheta` (line 559). -/
theorem bivariateTheta {f : ℕ × ℕ → ℝ} {g : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hrec : ∀ n m, N ≤ n → f (n + 1, m) = f (n, m) + g m)
    (hbase : ∀ n m, n ≤ N → f (n, m) ≤ C)
    (hg : g =Θ[atTop] fun m => (m : ℝ))
    (hf_nonneg : EventuallyNonnegative productAtTop f)
    (gpos : ∀ n _m : ℕ, 0 ≤ g n)
    (hC : 0 ≤ C) :
    f =Θ[productAtTop] fun p => ((p.1 * p.2 : ℕ) : ℝ) :=
  ⟨bivariateBigO hrec hbase hg.1 hf_nonneg hC,
    bivariateBigOmega hrec hbase hg.2 hf_nonneg gpos hC⟩

namespace Examples

/-- Source `ex` (line 579). -/
def bivariateTime : ℕ × ℕ → ℝ
  | (0, _m) => 1
  | (n + 1, m) => bivariateTime (n, m) + m

/-- Source `ex_pos` (line 583). -/
@[simp] theorem bivariateTimeNonnegative (n m : ℕ) :
    0 ≤ bivariateTime (n, m) := by
  induction n with
  | zero => simp [bivariateTime]
  | succ n ih => simp only [bivariateTime]; positivity

end Examples

/-- Source unnamed validation theorem (line 585). -/
private theorem bivariateTimeThetaProductGate :
    Examples.bivariateTime =Θ[productAtTop]
      fun p => ((p.1 * p.2 : ℕ) : ℝ) := by
  apply bivariateTheta (N := 0) (C := 1) (g := fun m => (m : ℝ))
  · intro n m _
    simp [Examples.bivariateTime]
  · intro n m hn
    have : n = 0 := by omega
    subst n
    simp [Examples.bivariateTime]
  · exact isTheta_refl _ _
  · exact Eventually.of_forall fun p => Examples.bivariateTimeNonnegative p.1 p.2
  · exact fun n _ => Nat.cast_nonneg n
  · norm_num

/-! ## Lightweight source-orientation checks -/

private theorem reverseOmegaOrientationGate {f g : ℕ → ℝ} {N : ℕ}
    (hrec : ∀ i ≥ N, f (i + 1) = f i + g i)
    (hg : (fun n : ℕ => (n : ℝ)) =O[atTop] g)
    (hf : ∀ n, 0 ≤ f n) (hgn : ∀ n, 0 ≤ g n) :
    (fun n : ℕ => (n : ℝ) * (n : ℝ)) =O[atTop] f :=
  bigOmegaLinearRecurrence hrec hg hf hgn

private theorem generalizedPairGate {f g G : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hrec : ∀ i ≥ N, f (i + 1) = f i + g i)
    (hg : g =Θ[atTop] G)
    (hf : ∀ n, 0 ≤ f n) (hgn : ∀ n, 0 ≤ g n)
    (hmono : ∀ x y, N ≤ x → x ≤ y → G x ≤ G y)
    (hpos : ∀ x ≥ N, 0 < G x)
    (hinc : ∀ n ≥ N,
      (((n + 1 : ℕ) : ℝ) * G (n + 1)) ≤ (n : ℝ) * G n + C * G n)
    (hC : 0 ≤ C) :
    f =Θ[atTop] fun n => (n : ℝ) * G n :=
  ⟨bigOLinearRecurrenceGeneral hrec hg.1 hmono hpos,
    bigOmegaLinearRecurrenceGeneral hrec hg.2 hf hgn hpos hinc hC⟩

/-! ## Kernel-three axiom guards -/

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bigOLinearRecurrenceGeneral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bigOLinearRecurrenceGeneral

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bigOLinearRecurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bigOLinearRecurrence

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bigOmegaLinearRecurrenceGeneral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bigOmegaLinearRecurrenceGeneral

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bigOmegaLinearRecurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bigOmegaLinearRecurrence

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bigThetaLinearRecurrenceConst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bigThetaLinearRecurrenceConst

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bigThetaLinearRecurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bigThetaLinearRecurrence

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bigThetaLinearRecurrenceLog' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bigThetaLinearRecurrenceLog

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bivariateBigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bivariateBigO

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bivariateBigOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bivariateBigOmega

/-- info: 'Lax13Proofs.Refine.AsymptoticsRecurrences.bivariateTheta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bivariateTheta

end Lax13Proofs.Refine.AsymptoticsRecurrences
