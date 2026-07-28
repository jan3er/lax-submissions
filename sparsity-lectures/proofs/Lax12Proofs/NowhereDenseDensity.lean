import Lax12.NowhereDenseDensity
import Lax12Proofs.MinorBridge
import Lax12Proofs.DensityOfShallowMinors

/-!
Theorem 3.1 of Chapter 1 of the notes, transported to the submitted
concepts: nowhere dense classes have subpolynomial shallow-minor density.
-/

namespace Lax12Proofs.NowhereDenseDensity

open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ShallowMinorDensity
open Lax12Proofs.MinorBridge

/--
---
conclusion: Lax12.NowhereDenseDensity.hasSubpolynomialDensity_of_nowhereDense
---
Every nowhere dense graph class has subpolynomial density: for every
depth `r` and every `ε > 0` there is a constant `c` such that every
depth-`r` minor of a member, on `m` vertices, has at most `c * m^(1+ε)`
edges.

# Proof strategy

The ported development proves the threshold form of the theorem — fewer
than `m^(1+ε)` edges once `m` is at least a bound `N` depending on the
depth and on `ε` — for classes indexed by arbitrary finite vertex types.
The submitted class is therefore closed under subgraph copies, whose
ported nowhere denseness follows from the submitted one, and the ported
theorem is instantiated at a submitted member, which lies in that
closure.  A submitted minor model becomes a ported one by bypassing its
walks to paths, and the edge counts are matched by
`Set.ncard_coe_finset`.

Threshold form to constant form: take `c = max 1 (N^2)`.  Above the
threshold the ported bound already gives `< m^(1+ε) ≤ c * m^(1+ε)`; below
it, a graph on `m` vertices has at most `m^2 ≤ N^2 ≤ c` edges while
`m^(1+ε) ≥ 1`; and at `m = 0` both sides vanish.  This is the equivalence
the notes themselves record immediately after the theorem.

# Attribution

The statement is Theorem 3.1 of Chapter 1 of the sparsity lecture notes
of Pilipczuk and Siebertz (numbering of the 2019/20 edition), whose
presented proof is credited there to Zdeněk Dvořák.  The proof is a port
of the formalization accompanying those notes, whose threshold version is
`Lax12Proofs.DensityOfShallowMinors.nd_subpolynomial_density`.
-/
theorem hasSubpolynomialDensity_of_nowhereDense (C : GraphClass)
    (h : NowhereDense C) : HasSubpolynomialDensity C := by
  classical
  intro r ε hε
  obtain ⟨N, hN⟩ := Lax12Proofs.DensityOfShallowMinors.nd_subpolynomial_density
    (subgraphClosure C) (isNowhereDense_subgraphClosure h) r ε hε
  refine ⟨max 1 ((N : ℝ) ^ 2), ?_⟩
  intro n G hG m H hHminor
  have hc0 : (0 : ℝ) ≤ max 1 ((N : ℝ) ^ 2) := le_trans zero_le_one (le_max_left _ _)
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · have hzero : H.edgeSet.ncard = 0 := by
      rw [ncard_edgeSet]
      have hsq := edgeFinset_card_le_sq H
      simpa using hsq
    rw [hzero]
    simp [Real.zero_rpow (by positivity : (1 : ℝ) + ε ≠ 0)]
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hpow : (1 : ℝ) ≤ (m : ℝ) ^ (1 + ε) :=
      Real.one_le_rpow hm1 (by positivity)
    rw [ncard_edgeSet]
    by_cases hmN : N ≤ m
    · have hlt := hN H
        ⟨Fin n, inferInstance, inferInstance, G, subgraphClosure_self hG,
          isShallowMinor_of_hasShallowMinor hHminor⟩ (by simpa using hmN)
      have hlt' : (H.edgeFinset.card : ℝ) < (m : ℝ) ^ (1 + ε) := by simpa using hlt
      calc (H.edgeFinset.card : ℝ) ≤ (m : ℝ) ^ (1 + ε) := hlt'.le
        _ ≤ max 1 ((N : ℝ) ^ 2) * (m : ℝ) ^ (1 + ε) :=
            le_mul_of_one_le_left (by positivity) (le_max_left _ _)
    · push_neg at hmN
      have hsq : (H.edgeFinset.card : ℝ) ≤ (m : ℝ) * (m : ℝ) := by
        have := edgeFinset_card_le_sq H
        simp only [Fintype.card_fin] at this
        exact_mod_cast this
      have hmN' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN.le
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      calc (H.edgeFinset.card : ℝ) ≤ (m : ℝ) * (m : ℝ) := hsq
        _ ≤ (N : ℝ) ^ 2 := by nlinarith
        _ ≤ max 1 ((N : ℝ) ^ 2) := le_max_right _ _
        _ ≤ max 1 ((N : ℝ) ^ 2) * (m : ℝ) ^ (1 + ε) :=
            le_mul_of_one_le_right hc0 hpow

end Lax12Proofs.NowhereDenseDensity
