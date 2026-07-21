import Lax2.Source

/-!
---
title: Twin-width and mixed minor number are functionally equivalent
---
For finite simple graphs, twin-width and mixed minor number are functionally
equivalent graph parameters: each is bounded by a numerical function of the
other. The statement is phrased directly with the source definitions of
twin-width (via bounded-red-degree contraction sequences) and mixed minor
number (the minimum over vertex orderings of the largest mixed minor of the
ordered adjacency matrix).
-/

namespace Lax2.Main

open Lax2.Source

axiom twin_width_functionally_equivalent_mixed_minor_number :
    TwinWidth.FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V] => TwinWidth.SimpleGraph.twinWidth)
      (fun {V : Type} [Fintype V] [DecidableEq V] => TwinWidth.SimpleGraph.mixedMinorNumber)

end Lax2.Main
