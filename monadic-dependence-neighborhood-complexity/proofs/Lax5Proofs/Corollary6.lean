import Lax5.WeaklySparseDependent
import Lax5.NowhereDenseNC

/-!
Corollary 6 of DMMPT26, composed from the *statements* of the two proved
halves: 6a (weakly sparse + monadically dependent ⇒ nowhere dense,
`Lax5.WeaklySparseDependent`) and 6b (nowhere dense ⇒ almost linear
neighborhood complexity, `Lax5.NowhereDenseNC`), each discharged by its own
proof elsewhere in this package.  Consumed by the terminal-sparsification
step (Lemma 24) of the Appendix-A machinery; composing the statements
rather than importing the two proofs is what makes the dependency visible
in the archive's proof network.
-/

namespace Lax5Proofs.Corollary6

open Lax5 Lax5.GraphClasses Lax5.MonadicDependence
  Lax5.NeighborhoodComplexity

/-- Corollary 6: weakly sparse monadically dependent classes have
almost linear neighborhood complexity. -/
theorem hasAlmostLinearNC_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    HasAlmostLinearNC C :=
  Lax5.NowhereDenseNC.hasAlmostLinearNC_of_nowhereDense C
    (Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent C hs hd)

end Lax5Proofs.Corollary6
