import Lax9.MergeWidth
import Lax9.NeighborhoodComplexity

/-!
---
title: Linear Neighbourhood Complexity of Bounded Merge-Width Classes
type: theorem
---
Every class of finite simple graphs with bounded merge-width has linear
neighbourhood complexity.
-/

namespace Lax9.BoundedMergeWidthLinearNeighborhoodComplexity

open Lax9.MergeWidth
open Lax9.NeighborhoodComplexity

/-- Every graph class of bounded merge-width has linear neighbourhood
complexity. -/
axiom bounded_mergeWidth_linearNeighborhoodComplexity
    (C : GraphClass) (h : BoundedMergeWidth C) : LinearNeighborhoodComplexity C

end Lax9.BoundedMergeWidthLinearNeighborhoodComplexity
