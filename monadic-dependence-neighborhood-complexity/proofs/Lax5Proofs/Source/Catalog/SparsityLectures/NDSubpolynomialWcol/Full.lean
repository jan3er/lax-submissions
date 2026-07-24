import Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.NDSubpolynomialDensity.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.AdmBoundByTopGrad.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumberEquivalence.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinorComposition.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor.Full
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers
open Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility
open Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense
open Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinorComposition
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor

namespace Lax5Proofs.Source.Catalog.SparsityLectures.NDSubpolynomialWcol

/-! ## Helper lemmas -/

/-- Edge count of a simple graph is at most |V|². -/
private lemma edgeFinset_card_le_card_mul_card {W : Type} [DecidableEq W] [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    H.edgeFinset.card ≤ Fintype.card W * Fintype.card W := by
  calc H.edgeFinset.card
      ≤ (Fintype.card W).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
    _ = Fintype.card W * (Fintype.card W - 1) / 2 := Nat.choose_two_right _
    _ ≤ Fintype.card W * (Fintype.card W - 1) := Nat.div_le_self _ 2
    _ ≤ Fintype.card W * Fintype.card W :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ 1)

/-- Topological minors have at most as many vertices as the host. -/
private lemma card_le_of_isShallowTopologicalMinor {V W : Type}
    [DecidableEq W] [Fintype W] [Fintype V]
    {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (h : IsShallowTopologicalMinor H G d) :
    Fintype.card W ≤ Fintype.card V := by
  obtain ⟨m⟩ := h
  exact Fintype.card_le_of_injective m.branchVertex m.branchVertex.injective

/-- Theorem 3.4/ch2: Nowhere dense classes have subpolynomial wcol. -/
theorem nd_subpolynomial_wcol (C : GraphClass) (hC : IsNowhereDense C)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℝ, 0 < f ∧ ∀ {V : Type} [DecidableEq V] [Fintype V]
      (G : SimpleGraph V),
      C G → ∃ (ord : LinearOrder V),
        letI := ord; (↑(wcol G r) : ℝ) ≤ f * (Fintype.card V : ℝ) ^ ε := by
  -- Choose ε₁ for the density bound, ensuring 3·r²·ε₁ < ε
  set ε₁ := ε / (3 * ↑(r ^ 2) + 1) with hε₁_def
  have hε₁_pos : 0 < ε₁ := div_pos hε (by positivity)
  -- Get N from subpolynomial density (for depth r-1 shallow reducts)
  obtain ⟨N, hN⟩ := Lax5Proofs.Source.Catalog.SparsityLectures.NDSubpolynomialDensity.nd_subpolynomial_density
    C hC (r - 1) ε₁ hε₁_pos
  -- Define constant K = r · (6r)^{r²} · (N+2)^{3r²} and set f = K + 1
  set K : ℕ := r * (6 * r) ^ (r ^ 2) * (N + 2) ^ (3 * r ^ 2) with hK_def
  refine ⟨↑K + 1, by positivity, ?_⟩
  -- For each graph G in C
  intro V _ _ G hCG
  set n := Fintype.card V with hn_def
  -- Define d = ⌈n^{ε₁}⌉₊ + N
  set d := ⌈(↑n : ℝ) ^ ε₁⌉₊ + N with hd_def
  -- Prove edge bound hypothesis for adm_le_of_topGrad_bound
  have hd_bound : ∀ {W : Type} [DecidableEq W] [Fintype W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      IsShallowTopologicalMinor H G (r - 1) →
      H.edgeFinset.card ≤ d * Fintype.card W := by
    intro W _ _ H _ hMinor
    set m := Fintype.card W with hm_def
    -- Case split on whether m ≥ N (large) or m < N (small)
    by_cases hm_large : N ≤ m
    · -- Large case: use density bound
      -- H is a topological minor → shallow minor → in ShallowReduct C (r-1)
      have hSM : IsShallowMinor H G (r - 1) :=
        shallowTopologicalMinor_toShallowMinor hMinor
      have hReduct : ShallowReduct C (r - 1) H :=
        ⟨V, inferInstance, inferInstance, G, hCG, hSM⟩
      have hDensity := hN H hReduct hm_large
      -- hDensity : (↑(H.edgeFinset.card) : ℝ) < (↑m : ℝ) ^ (1 + ε₁)
      -- |V(H)| ≤ |V(G)| = n
      have hm_le_n : m ≤ n := card_le_of_isShallowTopologicalMinor hMinor
      -- Chain: edge_count < m^{1+ε₁} = m · m^{ε₁} ≤ m · n^{ε₁} ≤ m · ⌈n^{ε₁}⌉ ≤ m · d
      by_cases hm0 : m = 0
      · have h := edgeFinset_card_le_card_mul_card H
        simp only [← hm_def, hm0, Nat.mul_zero, Nat.le_zero] at h ⊢
        exact h
      · have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
        have h1 : (↑m : ℝ) ^ (1 + ε₁) = ↑m * (↑m : ℝ) ^ ε₁ := by
          rw [Real.rpow_add hm_pos, Real.rpow_one]
        have h2 : (↑m : ℝ) ^ ε₁ ≤ (↑n : ℝ) ^ ε₁ :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hm_le_n) hε₁_pos.le
        have h3 : (↑n : ℝ) ^ ε₁ ≤ ↑d := by
          calc (↑n : ℝ) ^ ε₁ ≤ ↑⌈(↑n : ℝ) ^ ε₁⌉₊ := Nat.le_ceil _
            _ ≤ ↑d := by exact_mod_cast Nat.le_add_right _ N
        have key : (↑(H.edgeFinset.card) : ℝ) < ↑d * ↑m := calc
          (↑(H.edgeFinset.card) : ℝ) < (↑m : ℝ) ^ (1 + ε₁) := hDensity
          _ = ↑m * (↑m : ℝ) ^ ε₁ := h1
          _ ≤ ↑m * ↑d := mul_le_mul_of_nonneg_left (h2.trans h3) hm_pos.le
          _ = ↑d * ↑m := mul_comm _ _
        exact_mod_cast key.le
    · -- Small case: m < N, so edge_count ≤ m² ≤ m · N ≤ m · d
      push_neg at hm_large
      calc H.edgeFinset.card
          ≤ m * m := edgeFinset_card_le_card_mul_card H
        _ ≤ m * N := Nat.mul_le_mul_left m (Nat.le_of_lt hm_large)
        _ ≤ m * d := Nat.mul_le_mul_left m (Nat.le_add_left N _)
        _ = d * m := Nat.mul_comm m d
  -- Get ordering from admissibility bound
  obtain ⟨ord, hadm⟩ :=
    Lax5Proofs.Source.Catalog.SparsityLectures.AdmBoundByTopGrad.adm_le_of_topGrad_bound G r d hd_bound
  refine ⟨ord, ?_⟩
  letI := ord
  -- Chain: wcol ≤ 1 + r·(adm-1)^{r²} ≤ 1 + r·(6r·d³)^{r²}
  have hwcol := Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumberEquivalence.wcol_le_of_adm G r
  have hadm_sub : adm G r - 1 ≤ 6 * r * d ^ 3 := by omega
  have hnat_bound : wcol G r ≤ 1 + r * (6 * r * d ^ 3) ^ (r ^ 2) := by
    calc wcol G r
        ≤ 1 + r * (adm G r - 1) ^ (r ^ 2) := hwcol
      _ ≤ 1 + r * (6 * r * d ^ 3) ^ (r ^ 2) := by
          apply Nat.add_le_add_left
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left hadm_sub _
  -- Convert to real: ↑(wcol G r) ≤ (↑K + 1) · (↑n)^ε
  by_cases hn0 : n = 0
  · -- V is empty, wcol = 0
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    simp only [show wcol G r = 0 from by simp [wcol, Finset.univ_eq_empty],
      Nat.cast_zero, show (↑n : ℝ) = 0 from by exact_mod_cast hn0,
      Real.zero_rpow (ne_of_gt hε), mul_zero, le_refl]
  · -- n ≥ 1
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hn1 : (1 : ℝ) ≤ ↑n := Nat.one_le_cast.mpr hn_pos
    have hne1 : (1 : ℝ) ≤ (↑n : ℝ) ^ ε₁ := Real.one_le_rpow hn1 hε₁_pos.le
    have hnε : (1 : ℝ) ≤ (↑n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
    -- d ≤ (N+2) · n^{ε₁}
    have hd_le : (↑d : ℝ) ≤ (↑N + 2) * (↑n : ℝ) ^ ε₁ := by
      have hceil := le_of_lt (Nat.ceil_lt_add_one
        (Real.rpow_nonneg (Nat.cast_nonneg n) ε₁))
      have h1 : (↑d : ℝ) ≤ (↑n : ℝ) ^ ε₁ + ((↑N : ℝ) + 1) := by
        push_cast [hd_def]; linarith
      have h2 : (↑N : ℝ) + 1 ≤ ((↑N : ℝ) + 1) * (↑n : ℝ) ^ ε₁ :=
        le_mul_of_one_le_right (by positivity) hne1
      nlinarith
    -- 3r²ε₁ ≤ ε
    have hexp : ε₁ * (3 * (↑r : ℝ) ^ 2) ≤ ε := by
      have h : (0 : ℝ) < 3 * ↑(r ^ 2) + 1 := by positivity
      have h2 : (3 : ℝ) * (↑r : ℝ) ^ 2 ≤ 3 * ↑(r ^ 2) + 1 := by push_cast; linarith
      calc ε₁ * (3 * (↑r : ℝ) ^ 2)
          ≤ ε₁ * (3 * ↑(r ^ 2) + 1) := mul_le_mul_of_nonneg_left h2 hε₁_pos.le
        _ = ε := by rw [hε₁_def, div_mul_cancel₀ _ (ne_of_gt h)]
    -- d^{3r²} ≤ (N+2)^{3r²} · (n^{ε₁})^{3r²}
    have hd_pow : (↑d : ℝ) ^ (3 * r ^ 2) ≤
        ((↑N : ℝ) + 2) ^ (3 * r ^ 2) * ((↑n : ℝ) ^ ε₁) ^ (3 * r ^ 2) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _)
        (by linarith) _
    -- (n^{ε₁})^{3r²} ≤ n^ε
    have hrpow_le : ((↑n : ℝ) ^ ε₁) ^ (3 * r ^ 2) ≤ (↑n : ℝ) ^ ε := by
      rw [← Real.rpow_natCast ((↑n : ℝ) ^ ε₁) (3 * r ^ 2),
          ← Real.rpow_mul (Nat.cast_nonneg n)]
      apply Real.rpow_le_rpow_of_exponent_le hn1
      convert hexp using 1; push_cast; ring
    -- Main chain
    have hstep1 : (↑(wcol G r) : ℝ) ≤
        1 + (↑r : ℝ) * (6 * (↑r : ℝ)) ^ (r ^ 2) * (↑d : ℝ) ^ (3 * r ^ 2) := by
      have h := Nat.cast_le (α := ℝ).mpr hnat_bound
      push_cast at h; rw [mul_pow, ← pow_mul] at h; linarith
    calc (↑(wcol G r) : ℝ)
        ≤ 1 + (↑r : ℝ) * (6 * ↑r) ^ (r ^ 2) * (↑d : ℝ) ^ (3 * r ^ 2) := hstep1
      _ ≤ 1 + (↑r : ℝ) * (6 * ↑r) ^ (r ^ 2) *
          (((↑N : ℝ) + 2) ^ (3 * r ^ 2) * ((↑n : ℝ) ^ ε₁) ^ (3 * r ^ 2)) := by
          gcongr
      _ = 1 + (↑K : ℝ) * ((↑n : ℝ) ^ ε₁) ^ (3 * r ^ 2) := by
          simp only [hK_def]; push_cast; ring
      _ ≤ 1 + (↑K : ℝ) * (↑n : ℝ) ^ ε := by gcongr
      _ ≤ (↑n : ℝ) ^ ε + (↑K : ℝ) * (↑n : ℝ) ^ ε := by linarith
      _ = (↑K + 1) * (↑n : ℝ) ^ ε := by ring

end Lax5Proofs.Source.Catalog.SparsityLectures.NDSubpolynomialWcol
