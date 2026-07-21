import Lax2.Source
import Lax2.Main

namespace Lax2Proofs.Main

open Lax2.Source

/--
---
conclusion: Lax2.Main.twin_width_functionally_equivalent_mixed_minor_number
---
Self-contained source proof of functional equivalence, via the theorem chain
through Marcus–Tardos, matrix Theorem 10, Theorem 14, and the graph
twin-decomposition bridge.
-/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    TwinWidth.FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V] => TwinWidth.SimpleGraph.twinWidth)
      (fun {V : Type} [Fintype V] [DecidableEq V] => TwinWidth.SimpleGraph.mixedMinorNumber) :=
  TwinWidth.MainContract.twin_width_functionally_equivalent_mixed_minor_number

end Lax2Proofs.Main
