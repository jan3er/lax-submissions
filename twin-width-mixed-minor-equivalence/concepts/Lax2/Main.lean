import Lax1.TwinWidth
import Lax2.FunctionalEquivalence
import Lax2.MixedMinorNumber

/-!
---
title: Twin-width and mixed minor number are functionally equivalent
---
For finite simple graphs, twin-width and mixed minor number are functionally
equivalent graph parameters: each is bounded by a numerical function of the
other. Twin-width is the transparent definition of submission [Lax1] (least
red-degree bound admitting a full contraction sequence); the mixed minor
number is the minimum over vertex orderings of the largest mixed minor of the
ordered adjacency matrix, as defined in this submission's concept modules.
-/

namespace Lax2.Main

open Lax2.FunctionalEquivalence

/-- Twin-width and mixed minor number are functionally equivalent parameters
of finite simple graphs. -/
axiom twin_width_functionally_equivalent_mixed_minor_number :
    FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V] => Lax1.TwinWidth.twinWidth)
      (fun {V : Type} [Fintype V] [DecidableEq V] =>
        Lax2.MixedMinorNumber.mixedMinorNumber)

end Lax2.Main
