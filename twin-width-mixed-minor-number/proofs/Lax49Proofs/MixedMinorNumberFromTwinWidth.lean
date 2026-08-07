import Lax49Proofs.Bridge
import Lax49Proofs.Source.TwinWidth.Graph.TwinDecomposition
import Lax49.MixedMinorNumberFromTwinWidth

/-!
# The twin-width-to-mixed direction

The source development bounds the source mixed minor number linearly in
source twin-width; `Lax49Proofs.Bridge` proves both submitted parameters
pointwise equal to their source counterparts, so the bound transports
verbatim.
-/

namespace Lax49Proofs.MixedMinorNumberFromTwinWidth

noncomputable section

/--
---
conclusion: Lax49.MixedMinorNumberFromTwinWidth.exists_mixedMinorNumber_bound_of_twinWidth
---
The submitted mixed minor number is bounded by a numerical function of
twin-width (the parameter of submission Lax48); the witness is the linear
function `d ↦ 2 * (d + 3) + 2`.

# Proof strategy

The left-to-right leaf order of a twin-decomposition of width `twinWidth G`
makes the ordered adjacency matrix twin-ordered, and the first item of the
grid-minor theorem for twin-width bounds the mixed number of a twin-ordered
matrix linearly; the `+3` absorbs the diagonal convention and the two
one-sided child zones created by mirroring a graph contraction as a row and
a column fusion. Rewriting with the two parameter equalities of
`Lax49Proofs.Bridge` moves the bound onto the submitted parameters.

# Attribution

Ported from Édouard Bonnet's formalization of Bonnet–Kim–Thomassé–Watrigant,
*Twin-width I: Tractable FO Model Checking* (J. ACM 2022).
-/
theorem exists_mixedMinorNumber_bound_of_twinWidth :
    ∃ g : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V),
      Lax49.MixedMinorNumber.mixedMinorNumber G ≤
        g (Lax48.TwinWidth.twinWidth G) := by
  refine ⟨fun d => 2 * (d + 3) + 2, ?_⟩
  intro V _ _ G
  rw [Bridge.submitted_twinWidth_eq_source, Bridge.submitted_mixedMinorNumber_eq]
  exact TwinWidth.SimpleGraph.mixed_minor_number_le_twice_twin_width_plus_eight G

end

end Lax49Proofs.MixedMinorNumberFromTwinWidth
