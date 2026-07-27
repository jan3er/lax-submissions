import Lax2.FunctionalEquivalence
import Lax2.MixedMinorNumberFromTwinWidth
import Lax2.TwinWidthFromMixedMinorNumber

/-!
# The headline equivalence, assembled from the two directions

Functional equivalence is by definition the conjunction of the two
directional bounds, each of which is a statement of this submission in its
own right.  This module derives the headline claim from those two statements
alone: it consumes no source material, so the proof network records the
equivalence as exactly "direction one and direction two".
-/

namespace Lax2Proofs.Main

/--
---
conclusion: Lax2.FunctionalEquivalence.twin_width_functionally_equivalent_mixed_minor_number
assumptions:
  - Lax2.TwinWidthFromMixedMinorNumber.exists_twinWidth_bound_of_mixedMinorNumber
  - Lax2.MixedMinorNumberFromTwinWidth.exists_mixedMinorNumber_bound_of_twinWidth
---
Twin-width and mixed minor number are functionally equivalent, from the two
sibling statements bounding each parameter by a function of the other.

# Proof strategy

`FunctionallyEquivalent` unfolds to the conjunction of the two directional
existentials, so pairing the two assumed statements is the whole proof.  The
mathematical content lives in the proofs of those two statements
(`Lax2Proofs.TwinWidthFromMixedMinorNumber` and
`Lax2Proofs.MixedMinorNumberFromTwinWidth`).

# Attribution

Bonnet–Kim–Thomassé–Watrigant, *Twin-width I: Tractable FO Model Checking*
(J. ACM 2022), state the equivalence as the conjunction of these two bounds.
-/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    Lax2.GraphParameters.FunctionallyEquivalent
      Lax1.TwinWidth.twinWidth
      Lax2.MixedMinorNumber.mixedMinorNumber :=
  ⟨Lax2.TwinWidthFromMixedMinorNumber.exists_twinWidth_bound_of_mixedMinorNumber,
    Lax2.MixedMinorNumberFromTwinWidth.exists_mixedMinorNumber_bound_of_twinWidth⟩

end Lax2Proofs.Main
