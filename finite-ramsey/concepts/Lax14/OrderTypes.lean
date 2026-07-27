import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic

/-!
---
title: Order type of a tuple
type: definition
---
Fix a linearly ordered set and a tuple *a* = (*a*₁, …, *a*_ℓ) of its
elements. The order type of *a* records which coordinates carry strictly
smaller entries than which: it is the relation that holds of *i* and *j*
when *a*ᵢ < *a*ⱼ. Two tuples have the same order type when they are
arranged in the same way — in particular they then agree on which
coordinates carry equal entries, since a linear order is total.

# Formalization notes

The order type is a `Prop`-valued relation on coordinates rather than a
three-valued code: in a linear order the strict-order pattern determines
the equality pattern (`a i = a j` exactly when neither `a i < a j` nor
`a j < a i`), so recording `<` alone loses nothing and keeps
decidability, `compare` and `Ordering` off the endorsement surface.

The definition is stated for an arbitrary linearly ordered vertex type,
not only for `Fin n`: it is a pointwise notion, and proofs that consume it
work over intermediate carriers. Statements of this submission still
instantiate it at the canonical carriers.
-/

namespace Lax14.OrderTypes

/-- The order type of a tuple: the relation holding of coordinates `i` and
`j` when the `i`-th entry is strictly smaller than the `j`-th. Two tuples
have the same order type when this relation is the same. -/
def orderType {V : Type*} [LinearOrder V] {ℓ : ℕ} (a : Fin ℓ → V) :
    Fin ℓ → Fin ℓ → Prop :=
  fun i j => a i < a j

end Lax14.OrderTypes
