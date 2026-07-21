import Lax1.LeastNatural
import Lax2.MixedNumber
import Lax2.OrderedAdjacency

/-!
---
title: Mixed minor number of a graph
---
The *mixed minor number* of a finite simple graph $G$ is the minimum, over
all orderings $e$ of its vertex set, of the mixed number of the ordered
adjacency matrix of $G$ under $e$:
$$\mathrm{mixedMinorNumber}(G) =
  \min_{e : \mathrm{Fin}(|V|) \simeq V}
    \mathrm{matrixMixedNumber}(\mathrm{orderedAdjacency}(G, e)).$$
It is expressed as the least value attained by some ordering, via the least
natural number satisfying a predicate ([Lax1] `leastNat`).
-/

namespace Lax2.MixedMinorNumber

open Lax1.LeastNatural
open Lax2.MixedNumber
open Lax2.OrderedAdjacency

noncomputable section

/-- The mixed minor number of a finite graph: the minimum mixed number of an
ordered adjacency matrix over all vertex orderings. -/
def mixedMinorNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  leastNat fun k =>
    ∃ e : Fin (Fintype.card V) ≃ V,
      matrixMixedNumber (orderedAdjacency G e) = k

end

end Lax2.MixedMinorNumber
