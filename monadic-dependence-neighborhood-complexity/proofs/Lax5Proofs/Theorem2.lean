import Lax5.AlmostLinearNC
import Lax5Proofs.Lemma21

/-!
The headline theorem, derived from the semi-induced form of Lemma 21 by
choosing one representative vertex per realized neighborhood trace.
-/

namespace Lax5Proofs.Theorem2

open Lax5.GraphClasses Lax5.MonadicDependence Lax5.NeighborhoodComplexity

/--
---
conclusion: Lax5.AlmostLinearNC.hasAlmostLinearNC_of_monadicallyDependent
---
Monadically dependent graph classes have almost linear neighborhood
complexity: Theorem 2 of DMMPT26.

# Proof strategy

Choose one representative vertex per realized neighborhood trace on
`A`; the representatives leave pairwise distinct traces, so the
semi-induced form of Lemma 21 bounds their number — which is exactly
`traceCount G A` — by c · |A|^(1+ε). The paper's reduction to a
monadically dependent class of twin-free bipartite graphs lives inside
the proof of Lemma 21.

# Attribution

Theorem 2 of DMMPT26 (Appendix A).
-/
theorem hasAlmostLinearNC_of_monadicallyDependent (C : GraphClass)
    (h : MonadicallyDependent C) : HasAlmostLinearNC C := by
  intro ε hε
  obtain ⟨c, hc⟩ := Lemma21.ncard_le_rpow_of_injOn_traces C h hε
  refine ⟨c, fun n G hG A hA => ?_⟩
  classical
  set T : Set (Set (Fin n)) :=
    {S : Set (Fin n) | ∃ v : Fin n, S = G.neighborSet v ∩ A} with hT
  choose rep hrep using fun S : T => S.2
  set B : Set (Fin n) := Set.range rep with hB
  have hinj : Set.InjOn (fun v => G.neighborSet v ∩ A) B := by
    rintro _ ⟨S₁, rfl⟩ _ ⟨S₂, rfl⟩ h12
    have : S₁ = S₂ := Subtype.ext ((hrep S₁).trans (h12.trans (hrep S₂).symm))
    exact congrArg rep this
  have himage : T = (fun v => G.neighborSet v ∩ A) '' B := by
    apply Set.eq_of_subset_of_subset
    · rintro S hS
      exact ⟨rep ⟨S, hS⟩, ⟨⟨S, hS⟩, rfl⟩, (hrep ⟨S, hS⟩).symm⟩
    · rintro _ ⟨v, ⟨S, rfl⟩, rfl⟩
      exact ⟨rep S, rfl⟩
  have hcount : traceCount G A ≤ B.ncard := by
    calc traceCount G A = T.ncard := rfl
      _ ≤ B.ncard := himage ▸ Set.ncard_image_le B.toFinite
  calc (traceCount G A : ℝ) ≤ (B.ncard : ℝ) := Nat.cast_le.mpr hcount
    _ ≤ c * (A.ncard : ℝ) ^ (1 + ε) := hc n G hG A B hA hinj

end Lax5Proofs.Theorem2
