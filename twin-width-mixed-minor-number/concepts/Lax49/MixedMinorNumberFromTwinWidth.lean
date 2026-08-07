import Lax48.TwinWidth
import Lax49.MixedMinorNumber

/-!
---
title: Mixed minor number is bounded by a function of twin-width
type: theorem
---
There is a function *g* : ℕ → ℕ such that every finite simple graph *G*
satisfies mmn(*G*) ≤ *g*(tww(*G*)): a graph of bounded twin-width admits a
vertex ordering whose adjacency matrix has no large mixed minor. Twin-width
is the parameter of submission Lax48, mixed minor number the parameter of the
prerequisite concept.

# Formalization notes

The bound is stated over the two parameters themselves, on arbitrary finite
vertex types carrying `Fintype` and `DecidableEq` instances — the signature
both parameters have. Only the existence of a bounding function is claimed;
the known witness for this direction is linear.
-/

namespace Lax49.MixedMinorNumberFromTwinWidth

/-- Mixed minor number is bounded by a numerical function of twin-width. -/
axiom exists_mixedMinorNumber_bound_of_twinWidth :
    ∃ g : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V),
      Lax49.MixedMinorNumber.mixedMinorNumber G ≤ g (Lax48.TwinWidth.twinWidth G)

end Lax49.MixedMinorNumberFromTwinWidth
