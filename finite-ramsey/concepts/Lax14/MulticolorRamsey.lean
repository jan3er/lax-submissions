import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.Card

/-!
---
title: Ramsey's theorem for colourings of pairs
type: theorem
---
For every number of colours *k* and every size *s* there is an *N* such
that for every colouring of the unordered pairs of an *N*-element set with
*k* colours there is a monochromatic subset of size *s*: a set of *s*
elements all of whose pairs receive one and the same colour. This is
Ramsey's theorem for pairs in its multicolour form; the number of colours
and the requested size are arbitrary and the bound *N* depends only on
them.

# Formalization notes

The colouring is a plain function on `Sym2 (Fin n)`, mathlib's type of
unordered pairs; no notion of colouring is introduced. Colourings assign a
colour to the degenerate pairs `s(u, u)` as well, and the conclusion
ignores them — `Set.Pairwise` constrains distinct elements only — so
colourings of the edges of the complete graph are exactly the functions
considered here, restricted along an inclusion that changes nothing.

Sizes are stated as "at least": a monochromatic set of size at least *s*
contains one of size exactly *s*, and the stated form is what every
application uses. All statements of this submission range over the
canonical carriers `Fin n` and over all `n` beyond the bound, so the
theorem applies to a set of any size by transport along a bijection.

The Ramsey number itself is deliberately not defined. The archive's
convention for a numeric parameter would be `sInf {N | …}`, but no
statement of this submission consumes a numeric bound, so such a
definition would be endorsement surface that nothing uses; the existential
carries the whole content.

No hypothesis is placed on the number of colours: for `k = 0` there is no
colouring of the pairs of a nonempty set at all, so the statement holds
vacuously with `N = 1`.
-/

namespace Lax14.MulticolorRamsey

/-- Ramsey's theorem for pairs: every `k`-colouring of the unordered pairs
of a large enough finite set has a monochromatic subset of size `s`. -/
axiom exists_monochromatic_set (k s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : Sym2 (Fin n) → Fin k), N ≤ n →
      ∃ (i : Fin k) (S : Set (Fin n)), s ≤ S.ncard ∧
        S.Pairwise fun u v => c s(u, v) = i

end Lax14.MulticolorRamsey
