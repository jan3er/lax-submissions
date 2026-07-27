import Lax1.TwinWidth
import Lax2.MixedMinorNumber

/-!
---
title: Twin-width is bounded by a function of mixed minor number
type: theorem
---
There is a function *f* : ℕ → ℕ such that every finite simple graph *G*
satisfies tww(*G*) ≤ *f*(mmn(*G*)): a graph whose adjacency matrix admits no
large mixed minor in any vertex ordering has bounded twin-width. Twin-width
is the parameter of submission Lax1, mixed minor number the parameter of the
prerequisite concept.

# Formalization notes

The bound is stated over the two parameters themselves, on arbitrary finite
vertex types carrying `Fintype` and `DecidableEq` instances — the signature
both parameters have. Only the existence of a bounding function is claimed:
the known witness is doubly exponential, and its shape is not part of the
result.
-/

namespace Lax2.TwinWidthFromMixedMinorNumber

/-- Twin-width is bounded by a numerical function of mixed minor number. -/
axiom exists_twinWidth_bound_of_mixedMinorNumber :
    ∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V),
      Lax1.TwinWidth.twinWidth G ≤ f (Lax2.MixedMinorNumber.mixedMinorNumber G)

end Lax2.TwinWidthFromMixedMinorNumber
