import Lax5.NowhereDenseWcol
import Lax12.NowhereDenseWcol
import Lax5Proofs.QuasiWideness

/-!
Subpolynomial weak coloring numbers of nowhere dense classes, assumed from
the `sparsity-lectures` submission rather than reproved.  The two
submissions state the result over nominally distinct but textually
identical definitions, so the transport is the shallow-minor repacking of
`Lax5Proofs.QuasiWideness` on the hypothesis side and definitional
unfolding on the conclusion side: `wreach`, `wcol` and
`HasSubpolynomialWcol` have literally the same bodies in
`Lax5.WeakColoring` and `Lax12.ColoringNumbers`.
-/

namespace Lax5Proofs.NowhereDenseWcol

/--
---
conclusion: Lax5.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense
assumptions:
  - Lax12.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense
---
Nowhere dense classes have subpolynomial weak coloring numbers, uniformly
over graph copies contained in their members.

# Proof strategy

Assume the statement of the `sparsity-lectures` submission, which is the
same claim over that submission's own copies of the shallow-minor and
weak-coloring definitions.  Nowhere denseness transports by repacking the
shallow-minor model field for field, and the conclusion transports by
unfolding: the two `HasSubpolynomialWcol` predicates, and the `wcol` and
`wreach` definitions they are built from, are byte-identical, and
`GraphClass` is the same abbreviation on both sides.

# Attribution

Theorem 3.4 of the sparsity lecture notes of Pilipczuk, Pilipczuk, and
Siebertz, formalized in the `sparsity-lectures` submission.
-/
theorem hasSubpolynomialWcol_of_nowhereDense
    (C : Lax5.GraphClasses.GraphClass)
    (hC : Lax5.NowhereDenseClasses.NowhereDense C) :
    Lax5.WeakColoring.HasSubpolynomialWcol C :=
  Lax12.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense C
    (Lax5Proofs.QuasiWideness.nowhereDense_lax12_of_lax5 C hC)

end Lax5Proofs.NowhereDenseWcol
