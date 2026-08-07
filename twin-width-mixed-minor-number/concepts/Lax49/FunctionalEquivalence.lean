import Lax48.TwinWidth
import Lax49.GraphParameters
import Lax49.MixedMinorNumber

/-!
---
title: Twin-width and mixed minor number are functionally equivalent
type: theorem
---
Two finite-graph parameters are *functionally equivalent* when each is
bounded by a numerical function of the other. Twin-width and mixed minor
number are functionally equivalent: there are functions *f*, *g* : ℕ → ℕ
such that every finite simple graph *G* satisfies both:

- tww(*G*) ≤ *f*(mmn(*G*)); and
- mmn(*G*) ≤ *g*(tww(*G*)).

# Formalization notes

`FunctionallyEquivalent` and the uniform parameter signature it is stated
over come from the graph parameters concept; the equivalence applies the
relation to `Lax48.TwinWidth.twinWidth` and
`Lax49.MixedMinorNumber.mixedMinorNumber` directly, without wrapper lambdas.

The two directions are also stated on their own, as the sibling concepts
`TwinWidthFromMixedMinorNumber` and `MixedMinorNumberFromTwinWidth`: each has
its own literature proof and is usable on its own. This concept is the
headline claim that both hold at once.
-/

namespace Lax49.FunctionalEquivalence

open Lax49.GraphParameters

/-- Twin-width and mixed minor number are functionally equivalent graph
parameters. -/
axiom twin_width_functionally_equivalent_mixed_minor_number :
    FunctionallyEquivalent
      Lax48.TwinWidth.twinWidth
      Lax49.MixedMinorNumber.mixedMinorNumber

end Lax49.FunctionalEquivalence
