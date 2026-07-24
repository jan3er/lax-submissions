import Lax5.MonadicDependence
import Lax5.NeighborhoodComplexity
import Lax5Proofs.SparsGraphs
import Lax5Proofs.Asymptotics
import Mathlib.Combinatorics.SetFamily.Shatter

/-!
Top of the Appendix-A machinery (DMMPT26). This module states the
interface the headline theorem consumes: Lemma 21 in *semi-induced*
form — in a monadically dependent class, any vertex set `B` whose
members leave pairwise distinct neighborhood traces on a nonempty
vertex set `A` has size at most `c · |A|^(1+ε)` — together with the
ingredient [VC] (neighborhood set systems of a monadically dependent
class have uniformly bounded VC dimension).

Stating Lemma 21 on the class itself, rather than for a class of
bipartite graphs as the paper does, pushes the bipartite-encoding
choices below this interface: the reduction of the paper's Theorem 2
becomes a choice of trace representatives (see `Theorem2`), and the
transduction onto the semi-induced bipartite class happens inside the
proof of this lemma.

The proof of Lemma 21 wires together the Appendix-A pipeline: [VC]
bounds the VC dimension of the trace system of `B \ A` on `A`;
Lemma 26 (`exists_terminal_sparsification`) produces a definable
terminal sparsification whose size loss is a `stepLoss^d` polylog
factor; Lemma 24 (`size_le_of_terminal`, at exponent `ε/2`) bounds the
terminal sparsification; polylog absorption
(`exists_polylog_le_rpow`, at exponent `ε/2`) recovers the exponent
`1 + ε`. The part `B ∩ A` and the case `|A| = 1` (excluded by
Lemma 26) are absorbed into the constant: `|B ∩ A| ≤ |A|`, and on a
singleton `A` a twin-free family has at most `2^1` traces.
-/

namespace Lax5Proofs.Lemma21

open Lax5.GraphClasses Lax5.MonadicDependence Lax5.NeighborhoodComplexity

/-- The neighborhood traces of `G` on the finite vertex set `A`, as a
finite set family: `Finset` counterpart of the trace set underlying
`traceCount`, in the shape mathlib's `Finset.vcDim` consumes. -/
noncomputable def traceFamily {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.image (trace G A)

/-- Ingredient [VC]: the neighborhood set systems of a monadically
dependent class have uniformly bounded VC dimension. Contrapositive
route: unbounded shattering lets the class transduce all graphs. -/
theorem exists_vcDim_traceFamily_le (C : GraphClass)
    (hC : MonadicallyDependent C) :
    ∃ d : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Finset (Fin n), (traceFamily G A).vcDim ≤ d := by
  sorry

/-- Lemma 21 (semi-induced form): in a monadically dependent class,
vertices with pairwise distinct neighborhood traces on a nonempty set
`A` number at most `c · |A|^(1+ε)`. -/
theorem ncard_le_rpow_of_injOn_traces (C : GraphClass)
    (hC : MonadicallyDependent C) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A B : Set (Fin n), A.Nonempty →
        Set.InjOn (fun v => G.neighborSet v ∩ A) B →
        (B.ncard : ℝ) ≤ c * (A.ncard : ℝ) ^ (1 + ε) := by
  classical
  obtain ⟨d, hd⟩ := exists_vcDim_traceFamily_le C hC
  have hε2 : 0 < ε / 2 := by positivity
  -- Lemma 24 at exponent `ε/2`, its constant uniformized over the
  -- possible step counts `i ≤ d` by summing
  choose c24 hc24₀ hc24 using fun k : ℕ => size_le_of_terminal C hC k hε2
  set cUni : ℝ := ∑ k ∈ Finset.range (d + 1), c24 k with hcUni
  have hcUni₀ : 0 ≤ cUni := Finset.sum_nonneg fun k _ => hc24₀ k
  -- polylog absorption for `stepLoss^d`, at exponent `ε/2`
  obtain ⟨cAbs, hcAbs₀, hcAbs⟩ :=
    Asymptotics.exists_polylog_le_rpow ((600 * ((d : ℝ) + 1)) ^ d) (2 * d) hε2
  refine ⟨4 + cAbs * cUni, fun n G hG A B hA hinj => ?_⟩
  have hAfin : A.Finite := A.toFinite
  have hBfin : B.Finite := B.toFinite
  set A' : Finset (Fin n) := hAfin.toFinset with hA'
  set B' : Finset (Fin n) := hBfin.toFinset with hB'
  have hAcard : A.ncard = A'.card := Set.ncard_eq_toFinset_card A hAfin
  have hBcard : B.ncard = B'.card := Set.ncard_eq_toFinset_card B hBfin
  have hA'ne : A'.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨a, hAfin.mem_toFinset.2 ha⟩
  have hx1 : (1 : ℝ) ≤ (A'.card : ℝ) := by exact_mod_cast hA'ne.card_pos
  have mem_trace : ∀ (X : Finset (Fin n)) (b x : Fin n),
      x ∈ trace G X b ↔ x ∈ X ∧ G.Adj b x := by
    intro X b x
    simp [trace]
  set B₁ : Finset (Fin n) := B' \ A' with hB₁
  -- `B₁` is twin-free for finset traces on `A'`
  have htf : ∀ b ∈ B₁, ∀ b' ∈ B₁, trace G A' b = trace G A' b' → b = b' := by
    intro b hb b' hb' htr
    refine hinj (hBfin.mem_toFinset.1 (Finset.mem_sdiff.1 hb).1)
      (hBfin.mem_toFinset.1 (Finset.mem_sdiff.1 hb').1) ?_
    ext x
    have hx := Finset.ext_iff.1 htr x
    rw [mem_trace, mem_trace, hAfin.mem_toFinset] at hx
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
    exact ⟨fun ⟨had, hxA⟩ => ⟨(hx.1 ⟨hxA, had⟩).2, hxA⟩,
      fun ⟨had, hxA⟩ => ⟨(hx.2 ⟨hxA, had⟩).2, hxA⟩⟩
  have hsplit : (B'.card : ℝ) = ((B' ∩ A').card : ℝ) + (B₁.card : ℝ) := by
    rw [← Finset.card_inter_add_card_sdiff B' A']
    push_cast
    ring
  have hBA : ((B' ∩ A').card : ℝ) ≤ (A'.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  rcases lt_or_ge 1 A'.card with h1 | h1
  · -- main case: `1 < |A|`, the Appendix-A machinery applies
    have hxpos : (0 : ℝ) < (A'.card : ℝ) := lt_of_lt_of_le one_pos hx1
    have hsub : B₁.image (trace G A') ⊆ traceFamily G A' := by
      unfold traceFamily
      exact Finset.image_subset_image (Finset.subset_univ B₁)
    have hvc : (B₁.image (trace G A')).vcDim ≤ d :=
      le_trans (Finset.vcDim_mono hsub) (hd n G hG A')
    obtain ⟨i, hi, S, hSdef, hSterm, hSsize⟩ :=
      exists_terminal_sparsification htf hvc h1
    have hS24 : (S.size : ℝ) ≤ c24 i * (A'.card : ℝ) ^ (1 + ε / 2) :=
      hc24 i n G hG A' B₁ Finset.disjoint_sdiff hA'ne S hSdef hSterm
    have hstep : stepLoss d (A'.card : ℝ) ^ d =
        (600 * ((d : ℝ) + 1)) ^ d *
          (Real.log (A'.card : ℝ) + 2) ^ (2 * d) := by
      simp only [stepLoss]
      rw [mul_pow, ← pow_mul]
    have habs : stepLoss d (A'.card : ℝ) ^ d ≤
        cAbs * (A'.card : ℝ) ^ (ε / 2) := by
      rw [hstep]
      exact hcAbs _ hx1
    have hc24le : c24 i ≤ cUni :=
      Finset.single_le_sum (fun k _ => hc24₀ k)
        (Finset.mem_range.2 (by omega))
    have hB₁bound : (B₁.card : ℝ) ≤
        cAbs * cUni * (A'.card : ℝ) ^ (1 + ε) := by
      have hS' : (S.size : ℝ) ≤ cUni * (A'.card : ℝ) ^ (1 + ε / 2) :=
        le_trans hS24 (mul_le_mul_of_nonneg_right hc24le
          (Real.rpow_nonneg hxpos.le _))
      calc (B₁.card : ℝ)
          ≤ stepLoss d (A'.card : ℝ) ^ d * S.size := hSsize
        _ ≤ (cAbs * (A'.card : ℝ) ^ (ε / 2)) *
              (cUni * (A'.card : ℝ) ^ (1 + ε / 2)) := by
            apply mul_le_mul habs hS' (Nat.cast_nonneg _) (by positivity)
        _ = cAbs * cUni *
              ((A'.card : ℝ) ^ (ε / 2) * (A'.card : ℝ) ^ (1 + ε / 2)) := by
            ring
        _ = cAbs * cUni * (A'.card : ℝ) ^ (1 + ε) := by
            rw [← Real.rpow_add hxpos,
              show ε / 2 + (1 + ε / 2) = 1 + ε from by ring]
    have hAle : (A'.card : ℝ) ≤ (A'.card : ℝ) ^ (1 + ε) := by
      calc (A'.card : ℝ) = (A'.card : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (A'.card : ℝ) ^ (1 + ε) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hrp : (0 : ℝ) ≤ (A'.card : ℝ) ^ (1 + ε) :=
      Real.rpow_nonneg hxpos.le _
    rw [hBcard, hAcard, hsplit]
    nlinarith [mul_nonneg (mul_nonneg hcAbs₀ hcUni₀) hrp]
  · -- degenerate case `|A| = 1`: at most `2` twin-free traces off `A`
    have hA1 : A'.card = 1 := le_antisymm h1 hA'ne.card_pos
    have hB₁inj : Set.InjOn (trace G A') B₁ := fun b hb b' hb' =>
      htf b hb b' hb'
    have hB₁le : (B₁.card : ℝ) ≤ 2 := by
      have himg : B₁.image (trace G A') ⊆ A'.powerset := by
        intro F hF
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hF
        exact Finset.mem_powerset.2 fun x hx => ((mem_trace A' b x).1 hx).1
      have : B₁.card ≤ 2 := by
        calc B₁.card = (B₁.image (trace G A')).card :=
              (Finset.card_image_of_injOn hB₁inj).symm
          _ ≤ A'.powerset.card := Finset.card_le_card himg
          _ = 2 := by rw [Finset.card_powerset, hA1]; norm_num
      exact_mod_cast this
    have hrhs : (A.ncard : ℝ) ^ (1 + ε) = 1 := by
      rw [hAcard, hA1]
      simp [Real.one_rpow]
    rw [hrhs, hBcard, hsplit]
    have hBA1 : ((B' ∩ A').card : ℝ) ≤ 1 := by
      rw [hA1] at hBA
      exact_mod_cast hBA
    nlinarith [mul_nonneg hcAbs₀ hcUni₀]

end Lax5Proofs.Lemma21
