import Lax5.NowhereDenseNC
import Lax5Proofs.NowhereDenseWcol
import Lax5Proofs.NowhereDenseNeighborhoods

/-!
Corollary 6b at radius 1: nowhere dense classes have almost linear
neighborhood complexity. Top of the sparsity chain surveyed in
`pipeline.md` §3a.

The proof imports the completed subpolynomial weak-coloring-number chain,
then carries out the radius-one trace counting, polynomial witness
localization, and final exponent rescaling explicitly.
-/

namespace Lax5Proofs.Corollary6b

open Lax5.GraphClasses Lax5.NeighborhoodComplexity Lax5.NowhereDenseClasses
open Lax5.NowhereDenseWcol
open Lax5Proofs.NowhereDenseNeighborhoods

/-- The set-valued definition of `traceCount` agrees with the finite trace
family used by the counting argument. -/
private theorem traceCount_coe_finset {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) :
    traceCount G (A : Set (Fin n)) =
      (Finset.univ.image (neighborTrace G A)).card := by
  classical
  let F := Finset.univ.image (neighborTrace G A)
  let T : Set (Set (Fin n)) :=
    {S | ∃ v : Fin n, S = G.neighborSet v ∩ (A : Set (Fin n))}
  have hcoe : ((fun Q : Finset (Fin n) => (Q : Set (Fin n))) '' (F : Set _)) = T := by
    ext S
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hQ)
      refine ⟨v, Set.ext fun x => ?_⟩
      simp [neighborTrace, SimpleGraph.mem_neighborSet, and_comm]
    · rintro ⟨v, rfl⟩
      refine ⟨neighborTrace G A v, ?_, ?_⟩
      · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨v, Finset.mem_univ _, rfl⟩)
      · ext x
        simp [neighborTrace, SimpleGraph.mem_neighborSet, and_comm]
  have hinj : Function.Injective (fun Q : Finset (Fin n) => (Q : Set (Fin n))) := by
    intro Q R hQR
    exact Finset.coe_injective hQR
  calc
    traceCount G (A : Set (Fin n)) = T.ncard := rfl
    _ = ((fun Q : Finset (Fin n) => (Q : Set (Fin n))) '' (F : Set _)).ncard := by
      rw [hcoe]
    _ = (F : Set (Finset (Fin n))).ncard := Set.ncard_image_of_injective _ hinj
    _ = F.card := Set.ncard_coe_finset F

/--
---
conclusion: Lax5.NowhereDenseNC.hasAlmostLinearNC_of_nowhereDense
---
Nowhere dense graph classes have almost linear neighborhood complexity:
the radius-1 case of the theorem of Eickmeyer, Giannopoulou, Kreutzer,
Kwon, Pilipczuk, Rabinovich, Siebertz.

# Proof strategy

Radius-1 specialization of the generalized-coloring-number route: a
nowhere dense class is K_{t,t}-free, so its neighborhood set systems
have VC dimension O(t + log t); Dvořák's densification bounds the
depth-1 grad by f(ε)·n^ε, which bounds the weak 2-coloring number;
counting neighborhood traces along a weak coloring order then yields
|A| · n^ε traces, and localization to a polynomially small witness set
rescales this to c · |A|^(1+ε).

# Attribution

Sparsity lecture notes of Pilipczuk, Pilipczuk, Siebertz (chapters 1,
2, 5), specialized to radius 1; densification following Dvořák.
-/
theorem hasAlmostLinearNC_of_nowhereDense (C : GraphClass)
    (h : NowhereDense C) : HasAlmostLinearNC C := by
  classical
  intro ε hε
  obtain ⟨t, hKt⟩ := exists_forall_not_hasBiclique C h
  let s : ℕ := 3 * t + 1
  let q : ℕ := 6 * t + 1
  have hspos : 0 < s := by simp [s]
  have hqpos : 0 < q := by simp [q]
  let δ : ℝ := ε / ((s : ℝ) * q)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨cw, hcw⟩ :=
    Lax5Proofs.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense C h 2 δ hδ
  let cw' : ℝ := max cw 0
  let K : ℕ := 3 * t + 1
  let L : ℕ := 1 + K + K ^ 2
  let M : ℝ := (K + 1 : ℕ) * (2 : ℝ) ^ s
  have hM0 : 0 ≤ M := by positivity
  refine ⟨(L : ℝ) * (cw' + 1) ^ q * M ^ (δ * q), ?_⟩
  intro n G hG A hA
  let Af : Finset (Fin n) := A.toFinite.toFinset
  have hAfcoe : (Af : Set (Fin n)) = A := by
    ext x
    simp [Af]
  have hAfpos : 0 < Af.card := by
    rw [← Set.ncard_coe_finset Af, hAfcoe]
    exact (Set.ncard_pos A.toFinite).mpr hA
  have hGKt : ¬ HasBiclique G t := hKt n G hG
  obtain ⟨m, H, B, hHG, hHKt, hBcard, htraces, hm⟩ :=
    exists_localized_copy G Af hGKt
  have hBne : B.Nonempty := Finset.card_pos.mp (hBcard.trans_gt hAfpos)
  have hmpos : 0 < m := by
    have hBm : B.card ≤ m := by simpa using Finset.card_le_univ B
    omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  let d := wcol H 2
  obtain ⟨π, hπ⟩ := exists_ordering_wreach_le_wcol H 2
  have hfixed :
      (Finset.univ.image (neighborTrace H B)).card ≤
        B.card * orderCountingPolynomial t d :=
    card_neighborTraceFamily_le_mul_of_wreach H π B hBne hHKt hπ
  have hdw : (d : ℝ) ≤ cw' * (m : ℝ) ^ δ := by
    calc
      (d : ℝ) ≤ cw * (m : ℝ) ^ δ := hcw n G hG m H hHG
      _ ≤ cw' * (m : ℝ) ^ δ := by
        gcongr
        exact le_max_left cw 0
  have hmpow1 : (1 : ℝ) ≤ (m : ℝ) ^ δ := Real.one_le_rpow hm1 hδ.le
  have hdone : (d + 1 : ℕ) ≤ (cw' + 1) * (m : ℝ) ^ δ := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    calc
      (d : ℝ) + 1 ≤ cw' * (m : ℝ) ^ δ + (m : ℝ) ^ δ := by linarith
      _ = (cw' + 1) * (m : ℝ) ^ δ := by ring
  have horder : (orderCountingPolynomial t d : ℝ) ≤
      (L : ℝ) * ((d + 1 : ℕ) : ℝ) ^ q := by
    exact_mod_cast orderCountingPolynomial_le t d
  have h3s : 3 * t ≤ s := by
    change 3 * t ≤ 3 * t + 1
    omega
  have hmNat : m ≤ (K + 1) * (Af.card + 1) ^ s := by
    calc
      m ≤ Af.card + K * (Af.card + 1) ^ (3 * t) := by
        simpa [K] using hm
      _ ≤ (Af.card + 1) ^ s + K * (Af.card + 1) ^ s := by
        apply Nat.add_le_add
        · calc Af.card ≤ Af.card + 1 := Nat.le_succ _
            _ ≤ (Af.card + 1) ^ s := by
              simpa only [pow_one] using
                (pow_le_pow_right₀ (by omega : 1 ≤ Af.card + 1)
                  (show 1 ≤ s by omega) :
                    (Af.card + 1) ^ 1 ≤ (Af.card + 1) ^ s)
        · exact Nat.mul_le_mul_left K
            (pow_le_pow_right₀ (by omega : 1 ≤ Af.card + 1) h3s)
      _ = (K + 1) * (Af.card + 1) ^ s := by ring
  have hmM : (m : ℝ) ≤ M * (Af.card : ℝ) ^ s := by
    have hadd : (Af.card + 1 : ℕ) ≤ (2 : ℝ) * Af.card := by
      norm_cast
      omega
    calc
      (m : ℝ) ≤ (K + 1 : ℕ) * ((Af.card + 1 : ℕ) : ℝ) ^ s := by
        exact_mod_cast hmNat
      _ ≤ (K + 1 : ℕ) * ((2 : ℝ) * Af.card) ^ s := by gcongr
      _ = M * (Af.card : ℝ) ^ s := by
        simp only [M, mul_pow]
        ring
  have hmq : (m : ℝ) ^ (δ * q) ≤
      M ^ (δ * q) * (Af.card : ℝ) ^ ε := by
    have hβ : 0 ≤ δ * (q : ℝ) := by positivity
    calc
      (m : ℝ) ^ (δ * q) ≤ (M * (Af.card : ℝ) ^ s) ^ (δ * q) :=
        Real.rpow_le_rpow (by positivity) hmM hβ
      _ = M ^ (δ * q) * ((Af.card : ℝ) ^ s) ^ (δ * q) := by
        rw [Real.mul_rpow hM0 (by positivity)]
      _ = M ^ (δ * q) * (Af.card : ℝ) ^ ((s : ℝ) * (δ * q)) := by
        congr 1
        have hbase : (Af.card : ℝ) ^ s = (Af.card : ℝ) ^ (s : ℝ) := by
          rw [Real.rpow_natCast]
        rw [hbase, ← Real.rpow_mul (by positivity)]
      _ = M ^ (δ * q) * (Af.card : ℝ) ^ ε := by
        congr 2
        dsimp [δ]
        field_simp
  have hdpow : (((d + 1 : ℕ) : ℝ) ^ q) ≤
      (cw' + 1) ^ q * (m : ℝ) ^ (δ * q) := by
    calc
      (((d + 1 : ℕ) : ℝ) ^ q) ≤
          ((cw' + 1) * (m : ℝ) ^ δ) ^ q := by gcongr
      _ = (cw' + 1) ^ q * ((m : ℝ) ^ δ) ^ q := by rw [mul_pow]
      _ = (cw' + 1) ^ q * (m : ℝ) ^ (δ * q) := by
        congr 1
        rw [← Real.rpow_natCast]
        rw [Real.rpow_mul (by positivity)]
  rw [← hAfcoe, traceCount_coe_finset]
  calc
    ((Finset.univ.image (neighborTrace G Af)).card : ℝ)
        ≤ (Finset.univ.image (neighborTrace H B)).card := by exact_mod_cast htraces
    _ ≤ B.card * orderCountingPolynomial t d := by exact_mod_cast hfixed
    _ = Af.card * orderCountingPolynomial t d := by rw [hBcard]
    _ ≤ (Af.card : ℝ) * ((L : ℝ) * ((d + 1 : ℕ) : ℝ) ^ q) := by gcongr
    _ ≤ (Af.card : ℝ) *
          ((L : ℝ) * ((cw' + 1) ^ q * (m : ℝ) ^ (δ * q))) := by gcongr
    _ ≤ (Af.card : ℝ) *
          ((L : ℝ) * ((cw' + 1) ^ q *
            (M ^ (δ * q) * (Af.card : ℝ) ^ ε))) := by gcongr
    _ = ((L : ℝ) * (cw' + 1) ^ q * M ^ (δ * q)) *
          (Af.card : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add (by positivity), Real.rpow_one]
      ring
    _ = ((L : ℝ) * (cw' + 1) ^ q * M ^ (δ * q)) *
          ((Af : Set (Fin n)).ncard : ℝ) ^ (1 + ε) := by
      rw [Set.ncard_coe_finset]

end Lax5Proofs.Corollary6b
