import Lax1.TwinWidth
import Lax2.GraphParameters
import Lax2.MixedMinorNumber

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
relation to `Lax1.TwinWidth.twinWidth` and
`Lax2.MixedMinorNumber.mixedMinorNumber` directly, without wrapper lambdas.

The two directions are also stated on their own, as the sibling concepts
`TwinWidthFromMixedMinorNumber` and `MixedMinorNumberFromTwinWidth`: each has
its own literature proof and is usable on its own. This concept is the
headline claim that both hold at once.
-/

namespace Lax2.FunctionalEquivalence

open Lax2.GraphParameters

/-- Twin-width and mixed minor number are functionally equivalent graph
parameters. -/
axiom twin_width_functionally_equivalent_mixed_minor_number :
    FunctionallyEquivalent
      Lax1.TwinWidth.twinWidth
      Lax2.MixedMinorNumber.mixedMinorNumber

end Lax2.FunctionalEquivalence
