import Lax12.NowhereDenseWcol
import Lax12.NowhereDenseDensity
import Lax12.AdmissibilityBound
import Lax12.StrongColoringBound
import Lax12.WeakColoringBound
import Lax12Proofs.MinorBridge
import Lax12Proofs.OrderBridge

/-!
Theorem 3.4 of Chapter 2 of the notes, as the composition of the four
preceding theorem concepts: this file contains no mathematics of its own
beyond the arithmetic that chains them.
-/

namespace Lax12Proofs.NowhereDenseWcol

open scoped SimpleGraph
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ColoringNumbers
open Lax12.Admissibility Lax12.ShallowMinorDensity
open Lax12Proofs.MinorBridge Lax12Proofs.OrderBridge

/--
---
conclusion: Lax12.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense
assumptions:
  - Lax12.NowhereDenseDensity.hasSubpolynomialDensity_of_nowhereDense
  - Lax12.AdmissibilityBound.adm_le_of_hasTopologicalDensityAtMost
  - Lax12.StrongColoringBound.scol_le_of_adm
  - Lax12.WeakColoringBound.wcol_le_of_scol
---
Every nowhere dense graph class has subpolynomial weak coloring numbers:
for every radius `r` and every `ε > 0` there is a constant `c` such that
every subgraph `H` of a member, on `m` vertices, satisfies
`wcol_r(H) ≤ c * m^ε`.

# Proof strategy

This is a glue proof: it assumes the four preceding statements of the
submission and does nothing but compose them, so the proof network is
visible on the archive rather than buried inside a single derivation.

Fix `r` and `ε`, and set `ε₁ = ε / (3r² + 1)`.  Subpolynomial density,
applied to the closure of the class under subgraph copies — which is
nowhere dense whenever the class is — gives a constant `c` bounding the
edges of every depth-`r` minor of a subgraph `H` of a member by
`c · k^(1+ε₁)` in its own vertex count `k`.  Since a shallow minor has no
more vertices than its host, `k ≤ m`, so that bound rewrites as the
per-graph density bound `d = ⌈c · m^ε₁⌉` for `H`: `k^(1+ε₁) = k · k^ε₁ ≤
k · m^ε₁`.  A depth-`r` topological minor is in particular a depth-`r`
minor, so `d` bounds the topological density as well, and the
admissibility bound yields `adm_{r+1}(H) ≤ 1 + 6(r+1)d³`; admissibility
is monotone in the radius, so the same bound holds at radius `r`.  The
two coloring-number links then give
`wcol_r(H) ≤ 1 + r·(scol_r(H) - 1)^r ≤ 1 + r·(adm_r(H) - 1)^(r²) ≤
1 + r·(6(r+1)d³)^(r²)` — the arithmetic of Corollary 2.7 of the notes,
which has no concept of its own.

What remains is real arithmetic.  From `d ≤ (c+1)·m^ε₁` and
`ε₁ · 3r² ≤ ε` one gets `d^(3r²) ≤ (c+1)^(3r²) · m^ε`, so
`wcol_r(H) ≤ 1 + K·m^ε ≤ (K+1)·m^ε` with
`K = r·(6(r+1))^(r²)·(c+1)^(3r²)`, using `m^ε ≥ 1`.  The degenerate case
`m = 0` is separate: there `wcol_r(H) = 0` and `m^ε = 0`.

# Attribution

The statement is Theorem 3.4 of Chapter 2 of the sparsity lecture notes
of Pilipczuk and Siebertz (numbering of the 2019/20 edition).  The
composition reproduces, at the level of the submitted concepts, the
corresponding derivation of the formalization accompanying those notes.
-/
theorem hasSubpolynomialWcol_of_nowhereDense (C : GraphClass)
    (hC : NowhereDense C) : HasSubpolynomialWcol C := by
  intro r ε hε
  have hden : (0 : ℝ) < 3 * ((r : ℝ) ^ 2) + 1 := by positivity
  set ε₁ : ℝ := ε / (3 * ((r : ℝ) ^ 2) + 1) with hε₁def
  have hε₁pos : 0 < ε₁ := div_pos hε hden
  obtain ⟨c₁, hc₁⟩ := Lax12.NowhereDenseDensity.hasSubpolynomialDensity_of_nowhereDense
    (closure C) (nowhereDense_closure hC) r ε₁ hε₁pos
  set c : ℝ := max c₁ 0 with hcdef
  have hc0 : (0 : ℝ) ≤ c := le_max_right _ _
  have hc1c : c₁ ≤ c := le_max_left _ _
  set K : ℝ := (r : ℝ) * (6 * ((r : ℝ) + 1)) ^ (r ^ 2) * (c + 1) ^ (3 * r ^ 2) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  refine ⟨K + 1, ?_⟩
  intro n G hG m H hHG
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · have hw : wcol H r = 0 := Nat.le_zero.1 (Nat.sInf_le ⟨1, fun v => v.elim0⟩)
    rw [hw]
    simp [Real.zero_rpow (ne_of_gt hε)]
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hmε₁ : (1 : ℝ) ≤ (m : ℝ) ^ ε₁ := Real.one_le_rpow hm1 hε₁pos.le
    have hmε : (1 : ℝ) ≤ (m : ℝ) ^ ε := Real.one_le_rpow hm1 hε.le
    set d : ℕ := ⌈c * (m : ℝ) ^ ε₁⌉₊ with hddef
    have hdge : c * (m : ℝ) ^ ε₁ ≤ (d : ℝ) := Nat.le_ceil _
    -- the per-graph density bound
    have hdens : HasDensityAtMost H r d := by
      intro k K' hK'
      have hkm : k ≤ m := by
        have h := card_le_of_hasShallowMinor hK'
        simpa using h
      have hbound := hc₁ m H ⟨n, G, hG, hHG⟩ k K' hK'
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · have hempty : K'.edgeSet = ∅ := by
          ext e
          simp only [Set.mem_empty_iff_false, iff_false]
          refine e.ind fun a _ _ => a.elim0
        simp [hempty]
      · have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
        have hkpow : (0 : ℝ) ≤ (k : ℝ) ^ (1 + ε₁) := Real.rpow_nonneg (by positivity) _
        have hsplit : (k : ℝ) ^ (1 + ε₁) = (k : ℝ) * (k : ℝ) ^ ε₁ := by
          rw [Real.rpow_add (by linarith), Real.rpow_one]
        have hkm' : (k : ℝ) ^ ε₁ ≤ (m : ℝ) ^ ε₁ :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkm) hε₁pos.le
        have hkε₁ : (0 : ℝ) ≤ (k : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
        have hreal : (K'.edgeSet.ncard : ℝ) ≤ (d : ℝ) * (k : ℝ) := by
          calc (K'.edgeSet.ncard : ℝ) ≤ c₁ * (k : ℝ) ^ (1 + ε₁) := hbound
            _ ≤ c * (k : ℝ) ^ (1 + ε₁) := mul_le_mul_of_nonneg_right hc1c hkpow
            _ = c * (k : ℝ) * (k : ℝ) ^ ε₁ := by rw [hsplit]; ring
            _ ≤ c * (k : ℝ) * (m : ℝ) ^ ε₁ :=
                mul_le_mul_of_nonneg_left hkm' (mul_nonneg hc0 (by positivity))
            _ = (c * (m : ℝ) ^ ε₁) * (k : ℝ) := by ring
            _ ≤ (d : ℝ) * (k : ℝ) :=
                mul_le_mul_of_nonneg_right hdge (by positivity)
        exact_mod_cast hreal
    -- the chain of the four assumed statements
    have hadm : adm H r ≤ 1 + 6 * (r + 1) * d ^ 3 :=
      le_trans (adm_le_adm_succ H r)
        (Lax12.AdmissibilityBound.adm_le_of_hasTopologicalDensityAtMost H r d
          (hasTopologicalDensityAtMost_of_hasDensityAtMost hdens))
    have hscol := Lax12.StrongColoringBound.scol_le_of_adm H r
    have hwcolstep := Lax12.WeakColoringBound.wcol_le_of_scol H r
    have hsub : scol H r - 1 ≤ (adm H r - 1) ^ r := by omega
    have hnat : wcol H r ≤ 1 + r * (6 * (r + 1) * d ^ 3) ^ (r ^ 2) := by
      calc wcol H r ≤ 1 + r * (scol H r - 1) ^ r := hwcolstep
        _ ≤ 1 + r * ((adm H r - 1) ^ r) ^ r :=
            Nat.add_le_add_left (Nat.mul_le_mul_left r (Nat.pow_le_pow_left hsub r)) 1
        _ = 1 + r * (adm H r - 1) ^ (r ^ 2) := by rw [pow_two, ← pow_mul]
        _ ≤ 1 + r * (6 * (r + 1) * d ^ 3) ^ (r ^ 2) :=
            Nat.add_le_add_left
              (Nat.mul_le_mul_left r (Nat.pow_le_pow_left (by omega) _)) 1
    -- real arithmetic
    have hd_le : (d : ℝ) ≤ (c + 1) * (m : ℝ) ^ ε₁ := by
      have hceil : (d : ℝ) < c * (m : ℝ) ^ ε₁ + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      nlinarith
    have hexp : ε₁ * (3 * (r : ℝ) ^ 2) ≤ ε := by
      have h1 : ε₁ * (3 * (r : ℝ) ^ 2) ≤ ε₁ * (3 * (r : ℝ) ^ 2 + 1) := by
        nlinarith [hε₁pos.le]
      have h2 : ε₁ * (3 * (r : ℝ) ^ 2 + 1) = ε := by
        rw [hε₁def]; field_simp
      linarith
    have hrpow : ((m : ℝ) ^ ε₁) ^ (3 * r ^ 2) ≤ (m : ℝ) ^ ε := by
      rw [← Real.rpow_natCast ((m : ℝ) ^ ε₁) (3 * r ^ 2),
        ← Real.rpow_mul (by positivity)]
      refine Real.rpow_le_rpow_of_exponent_le hm1 ?_
      push_cast
      linarith [hexp]
    have hdpow : (d : ℝ) ^ (3 * r ^ 2) ≤
        (c + 1) ^ (3 * r ^ 2) * ((m : ℝ) ^ ε₁) ^ (3 * r ^ 2) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hd_le _
    have hcast : (wcol H r : ℝ) ≤
        1 + (r : ℝ) * (6 * ((r : ℝ) + 1)) ^ (r ^ 2) * (d : ℝ) ^ (3 * r ^ 2) := by
      have h := (Nat.cast_le (α := ℝ)).2 hnat
      push_cast at h
      rw [mul_pow, ← pow_mul] at h
      linarith
    have hpos1 : (0 : ℝ) ≤ (r : ℝ) * (6 * ((r : ℝ) + 1)) ^ (r ^ 2) := by positivity
    calc (wcol H r : ℝ)
        ≤ 1 + (r : ℝ) * (6 * ((r : ℝ) + 1)) ^ (r ^ 2) * (d : ℝ) ^ (3 * r ^ 2) := hcast
      _ ≤ 1 + (r : ℝ) * (6 * ((r : ℝ) + 1)) ^ (r ^ 2) *
            ((c + 1) ^ (3 * r ^ 2) * ((m : ℝ) ^ ε₁) ^ (3 * r ^ 2)) := by
          nlinarith
      _ = 1 + K * ((m : ℝ) ^ ε₁) ^ (3 * r ^ 2) := by rw [hKdef]; ring
      _ ≤ 1 + K * (m : ℝ) ^ ε := by nlinarith
      _ ≤ (m : ℝ) ^ ε + K * (m : ℝ) ^ ε := by linarith
      _ = (K + 1) * (m : ℝ) ^ ε := by ring

end Lax12Proofs.NowhereDenseWcol
