import Lax8.MergeWidth
import Lax8.NeighborhoodComplexity

/-!
---
title: Linear Neighbourhood Complexity of Bounded Merge-Width Classes
type: theorem
---
Every class of finite simple graphs with bounded merge-width has linear
neighbourhood complexity.
-/

namespace Lax8.BoundedMergeWidthLinearNeighborhoodComplexity

open Lax8.MergeWidth
open Lax8.NeighborhoodComplexity

/-- Every graph class of bounded merge-width has linear neighbourhood
complexity. -/
axiom bounded_mergeWidth_linearNeighborhoodComplexity
    (C : GraphClass) (h : BoundedMergeWidth C) : LinearNeighborhoodComplexity C

end Lax8.BoundedMergeWidthLinearNeighborhoodComplexity
