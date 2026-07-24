import Lax9Proofs.EdgeDecomp
import Lax9.BoundedMergeWidthChiBounded

/-!
# χ-boundedness of bounded merge-width classes

Formalisation of Theorem 1.2 of Bonamy–Geniet: any graph $G$ with radius-2
merge-width at most $k$ and clique number at most $t$ satisfies
$χ(G) ≤ (t+1)! · k^(2t-2)$.  Consequently every class of bounded merge-width is
χ-bounded.
-/

namespace Lax9Proofs

open Lax9.MergeWidth
open Lax9.ChiBoundedness

open scoped Classical
open Finset

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 4.3 (edge decomposition).**
A graph $G$ with radius-2 merge-width $≤ k$ and clique number $≤ t$ decomposes as
an edge-union $G = GR ⊔ GU ⊔ GI$ where $GR$ is $k$-colourable, $GU$ is
$(kt+1)$-colourable, and $GI$ (a disjoint union of induced $Kt$-free subgraphs)
has clique number $< t$ and radius-2 merge-width $≤ k$. -/
theorem exists_edge_decomposition (k t : ℕ) (hk : 1 ≤ k) (ht : 2 ≤ t) (S : MergeSeq G)
    (hS : S.width 2 ≤ k) (homega : G.cliqueNum ≤ t) :
    ∃ GR GU GI : SimpleGraph V, G = GR ⊔ GU ⊔ GI ∧
      GR.Colorable k ∧ GU.Colorable (k * t + 1) ∧
      GI.cliqueNum + 1 ≤ t ∧ ∃ S' : MergeSeq GI, S'.width 2 ≤ k := by
  rcases lt_or_eq_of_le homega with hlt | heq
  · -- $ω(G) < t$: trivial decomposition $G = ⊥ ⊔ ⊥ ⊔ G$.
    refine ⟨⊥, ⊥, G, by simp, ?_, ?_, by omega, S, hS⟩
    · exact (colorable_one_of_edgeless (⊥ : SimpleGraph V) (fun u v => by simp)).mono hk
    · exact (colorable_one_of_edgeless (⊥ : SimpleGraph V) (fun u v => by simp)).mono (by omega)
  · -- $ω(G) = t$: freeze a minimal merge sequence on maximally $Kt$-free parts.
    obtain ⟨S0, hmin, _, hwidth0⟩ := exists_minimal_mergeSeq S 2
    have hW0 : S0.width 2 ≤ k := le_trans hwidth0 hS
    refine ⟨edgeR S0 t, edgeU S0 t, restrictGraph G (ktSetoid S0 t),
      edge_decomp_eq S0 t, edgeR_colorable S0 ht k hk hW0 hmin heq,
      edgeU_colorable S0 ht k hW0 heq, restrictGraph_cliqueNum_lt S0 ht,
      exists_restrict_mergeSeq S0 (ktSetoid S0 t) 2 k hk hW0⟩

/-- Auxiliary: if $cliqueNum H ≤ 1$ then $H$ has no edges. -/
theorem edgeless_of_cliqueNum_le_one {W : Type u} [Fintype W] (H : SimpleGraph W)
    (h : H.cliqueNum ≤ 1) : ∀ u v, ¬ H.Adj u v := by
  intro u v hadj
  have hne : u ≠ v := hadj.ne
  have hclique : H.IsNClique 2 ({u, v} : Finset W) := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        first | exact absurd rfl hab | exact hadj | exact hadj.symm
    · rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hle : ({u, v} : Finset W).card ≤ H.cliqueNum :=
    @SimpleGraph.IsClique.card_le_cliqueNum _ H _ ({u, v} : Finset W) hclique.isClique
  rw [hclique.card_eq] at hle
  omega

/-- **Theorem 1.2 (per graph).**
A graph $H$ with radius-2 merge-width $≤ k$ (with $k ≥ 1$) and clique number
$≤ t$ satisfies $χ(H) ≤ (t+1)! · k^(2t-2)$. -/
theorem chromatic_le_of_width (k : ℕ) (hk : 1 ≤ k) :
    ∀ (t : ℕ) {W : Type u} [Fintype W] (H : SimpleGraph W),
      (∃ S : MergeSeq H, S.width 2 ≤ k) → H.cliqueNum ≤ t →
      H.Colorable ((t + 1).factorial * k ^ (2 * t - 2)) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro W _ H hwit homega
    rcases Nat.lt_or_ge t 2 with htlt | htge
    · -- $t ≤ 1$: $H$ is edgeless.
      have hno := edgeless_of_cliqueNum_le_one H (by omega)
      refine (colorable_one_of_edgeless H hno).mono ?_
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (by omega)))
    · -- $t ≥ 2$: use the edge decomposition and the induction hypothesis on $GI$.
      obtain ⟨GR, GU, GI, hEq, hGR, hGU, hGIomega, S', hS'⟩ :=
        exists_edge_decomposition (G := H) k t hk htge hwit.choose hwit.choose_spec homega
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
      have hGIcolor : GI.Colorable ((s + 2).factorial * k ^ (2 * s)) := by
        have hIH := IH (s + 1) (by omega) GI ⟨S', hS'⟩ (by omega)
        have e : 2 * (s + 1) - 2 = 2 * s := by omega
        rw [e] at hIH
        exact hIH
      rw [hEq]
      have hall :
          ((GR ⊔ GU) ⊔ GI).Colorable
            (k * (k * (s + 2) + 1) * ((s + 2).factorial * k ^ (2 * s))) :=
        colorable_sup (colorable_sup hGR hGU) hGIcolor
      refine hall.mono ?_
      have hexp : 2 * (s + 2) - 2 = 2 * s + 2 := by omega
      rw [hexp, pow_add]
      have hcore : k * (k * (s + 2) + 1) ≤ (s + 3) * k ^ 2 := by nlinarith [hk]
      have hfact : (s + 2 + 1).factorial = (s + 3) * (s + 2).factorial := by
        rw [Nat.factorial_succ]
      rw [hfact]
      calc k * (k * (s + 2) + 1) * ((s + 2).factorial * k ^ (2 * s))
          = (k * (k * (s + 2) + 1)) * (s + 2).factorial * k ^ (2 * s) := by ring
        _ ≤ ((s + 3) * k ^ 2) * (s + 2).factorial * k ^ (2 * s) := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcore)
        _ = (s + 3) * (s + 2).factorial * (k ^ (2 * s) * k ^ 2) := by ring

/--
---
conclusion: Lax9.BoundedMergeWidthChiBounded.bounded_mergeWidth_chiBounded
---
Theorem 1.2 of Bonamy–Geniet: every graph class of bounded merge-width is
χ-bounded.
-/
theorem chiBounded_of_boundedMergeWidth
    (C : GraphClass) (h : BoundedMergeWidth C) : ChiBounded C := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun t => (t + 1).factorial * (max (f 2) 1) ^ (2 * t - 2), ?_⟩
  intro W _ H hH
  have hwit : ∃ S : MergeSeq H, S.width 2 ≤ max (f 2) 1 := by
    obtain ⟨S, hS⟩ := (mergeWidth_le_iff 2 (f 2)).1 (hf H hH 2)
    exact ⟨S, le_trans hS (le_max_left _ _)⟩
  exact chromatic_le_of_width (max (f 2) 1) (le_max_right _ _) H.cliqueNum H hwit (le_refl _)

end Lax9Proofs
