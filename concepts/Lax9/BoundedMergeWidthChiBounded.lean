import Lax9.ChiBoundedness
import Lax9.MergeWidth

/-!
---
title: χ-Boundedness of Bounded Merge-Width Classes
type: theorem
---
Every class of finite simple graphs with bounded merge-width is χ-bounded.
-/

namespace Lax9.BoundedMergeWidthChiBounded

open Lax9.ChiBoundedness
open Lax9.MergeWidth

/-- Every graph class of bounded merge-width is χ-bounded. -/
axiom bounded_mergeWidth_chiBounded
    (C : GraphClass) (h : BoundedMergeWidth C) : ChiBounded C

end Lax9.BoundedMergeWidthChiBounded
