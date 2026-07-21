import Lax4.FunctionalEquivalence
import Lax4Proofs.Bridge
import Lax4Proofs.MixedBridge
import Lax4Proofs.Source.TwinWidth.Equivalence.MainContract

namespace Lax4Proofs.Main

/--
---
conclusion: Lax4.FunctionalEquivalence.twin_width_functionally_equivalent_mixed_minor_number
---
The source proof establishes both directional bounds through Marcus–Tardos,
matrix Theorem 10, Theorem 14, and the graph twin-decomposition bridge.
`Bridge` and `MixedBridge` identify the source graph parameters with the small,
transparent concept definitions exposed by Lax3 and Lax4.
-/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    Lax4.FunctionalEquivalence.FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V] => Lax3.TwinWidth.twinWidth)
      (fun {V : Type} [Fintype V] [DecidableEq V] =>
        Lax4.MixedMinorNumber.mixedMinorNumber) := by
  have h :=
    Lax4Proofs.TwinWidth.MainContract.twin_width_functionally_equivalent_mixed_minor_number
  rw [Lax4Proofs.TwinWidth.FunctionallyEquivalent] at h
  rw [Lax4.FunctionalEquivalence.FunctionallyEquivalent]
  rcases h with ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  constructor
  · refine ⟨f, ?_⟩
    intro V _ _ G
    rw [← Lax4Proofs.Bridge.sourceTwinWidth_eq_submitted,
      ← Lax4Proofs.MixedBridge.sourceMixedMinorNumber_eq_submitted]
    exact hf G
  · refine ⟨g, ?_⟩
    intro V _ _ G
    rw [← Lax4Proofs.Bridge.sourceTwinWidth_eq_submitted,
      ← Lax4Proofs.MixedBridge.sourceMixedMinorNumber_eq_submitted]
    exact hg G

end Lax4Proofs.Main
