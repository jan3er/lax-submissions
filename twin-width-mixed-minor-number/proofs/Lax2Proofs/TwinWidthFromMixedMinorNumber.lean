import Lax2Proofs.Bridge
import Lax2Proofs.Source.TwinWidth.Equivalence.MixedToTwinWidth
import Lax2.TwinWidthFromMixedMinorNumber

/-!
# The mixed-minor-to-twin-width direction

The source development bounds source twin-width by a function of the source
mixed minor number; `Lax2Proofs.Bridge` proves both submitted parameters
pointwise equal to their source counterparts, so the bound transports
verbatim.
-/

namespace Lax2Proofs.TwinWidthFromMixedMinorNumber

noncomputable section

/--
---
conclusion: Lax2.TwinWidthFromMixedMinorNumber.exists_twinWidth_bound_of_mixedMinorNumber
---
Twin-width (the parameter of submission Lax1) is bounded by a numerical
function of the submitted mixed minor number.

# Proof strategy

The source direction `twinWidthBoundedByMixedMinorNumber` is the mirrored
Boolean Theorem 14 construction: an ordered adjacency matrix of mixed number
`k` is `(k+1)`-mixed-free, and the Marcus–Tardos-based Theorem 10 machinery
turns a mixed-free matrix into a contraction sequence of bounded red degree.
Rewriting with the two parameter equalities of `Lax2Proofs.Bridge` moves the
bound onto the submitted parameters, with the same witness function.

# Attribution

Ported from Édouard Bonnet's formalization of Bonnet–Kim–Thomassé–Watrigant,
*Twin-width I: Tractable FO Model Checking* (J. ACM 2022).
-/
theorem exists_twinWidth_bound_of_mixedMinorNumber :
    ∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V),
      Lax1.TwinWidth.twinWidth G ≤
        f (Lax2.MixedMinorNumber.mixedMinorNumber G) := by
  obtain ⟨f, hf⟩ := TwinWidth.SimpleGraph.twinWidthBoundedByMixedMinorNumber
  refine ⟨f, ?_⟩
  intro V _ _ G
  rw [Bridge.submitted_twinWidth_eq_source, Bridge.submitted_mixedMinorNumber_eq]
  exact hf G

end

end Lax2Proofs.TwinWidthFromMixedMinorNumber
