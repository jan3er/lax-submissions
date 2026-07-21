import Lax2.Main
import Lax2Proofs.Bridge
import Lax2Proofs.MixedBridge
import Lax2Proofs.Source.TwinWidth.Equivalence.MainContract

namespace Lax2Proofs.Main

/--
---
conclusion: Lax2.Main.twin_width_functionally_equivalent_mixed_minor_number
---
The source proof establishes both directional bounds through Marcus–Tardos,
matrix Theorem 10, Theorem 14, and the graph twin-decomposition bridge.
`Bridge` and `MixedBridge` identify the source graph parameters with the small,
transparent concept definitions exposed by Lax1 and Lax2.
-/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    Lax2.FunctionalEquivalence.FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V] => Lax1.TwinWidth.twinWidth)
      (fun {V : Type} [Fintype V] [DecidableEq V] =>
        Lax2.MixedMinorNumber.mixedMinorNumber) := by
  have h :=
    Lax2Proofs.TwinWidth.MainContract.twin_width_functionally_equivalent_mixed_minor_number
  rw [Lax2Proofs.TwinWidth.FunctionallyEquivalent] at h
  rw [Lax2.FunctionalEquivalence.FunctionallyEquivalent]
  rcases h with ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  constructor
  · refine ⟨f, ?_⟩
    intro V _ _ G
    rw [← Lax2Proofs.Bridge.sourceTwinWidth_eq_submitted,
      ← Lax2Proofs.MixedBridge.sourceMixedMinorNumber_eq_submitted]
    exact hf G
  · refine ⟨g, ?_⟩
    intro V _ _ G
    rw [← Lax2Proofs.Bridge.sourceTwinWidth_eq_submitted,
      ← Lax2Proofs.MixedBridge.sourceMixedMinorNumber_eq_submitted]
    exact hg G

end Lax2Proofs.Main
