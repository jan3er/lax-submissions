import Lax1.LeastNatural
import Lax1.ContractionSequenceWidth

/-!
---
title: Twin-width
---
$\mathrm{twinWidth}(G)$ is the least natural number $d$ such that
$\mathrm{ContractionSequence}(G,d)$ is nonempty:
$$\mathrm{leastNat}\bigl(d\mapsto
    \mathrm{Nonempty}(\mathrm{ContractionSequence}(G,d))\bigr).$$
-/


namespace Lax1.TwinWidth

open Lax1.ContractionSequenceWidth
open Lax1.LeastNatural

noncomputable section

/-- The twin-width of a finite graph is the least red-degree bound admitting a
contraction sequence.  The fallback value is `0` if the search type is empty. -/
def twinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  leastNat fun d => Nonempty (ContractionSequence G d)

end

end Lax1.TwinWidth
