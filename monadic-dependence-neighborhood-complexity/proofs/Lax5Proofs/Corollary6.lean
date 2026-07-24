import Lax5.WeaklySparseDependent
import Lax5.NowhereDenseNC

/-!
Corollary 6 of DMMPT26, composed from the two concept statements: 6a
(weakly sparse + monadically dependent ⇒ nowhere dense, an *open*
obligation of this submission) and 6b (nowhere dense ⇒ almost linear
neighborhood complexity, discharged in `Corollary6b`). Consumed by the
terminal-sparsification step (Lemma 24) of the Appendix-A machinery.
-/

namespace Lax5Proofs.Corollary6

open Lax5 Lax5.GraphClasses Lax5.MonadicDependence
  Lax5.NeighborhoodComplexity Lax5.WeaklySparseDependent

/-- Corollary 6: weakly sparse monadically dependent classes have
almost linear neighborhood complexity. -/
theorem hasAlmostLinearNC_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    HasAlmostLinearNC C :=
  NowhereDenseNC.hasAlmostLinearNC_of_nowhereDense C
    (nowhereDense_of_weaklySparse_of_monadicallyDependent C hs hd)

end Lax5Proofs.Corollary6
