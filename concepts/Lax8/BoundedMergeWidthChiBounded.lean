import Lax8.ChiBoundedness
import Lax8.MergeWidth

/-!
---
title: χ-Boundedness of Bounded Merge-Width Classes
type: theorem
---
Every class of finite simple graphs with bounded merge-width is χ-bounded.
-/

namespace Lax8.BoundedMergeWidthChiBounded

open Lax8.ChiBoundedness
open Lax8.MergeWidth

/-- Every graph class of bounded merge-width is χ-bounded. -/
axiom bounded_mergeWidth_chiBounded
    (C : GraphClass) (h : BoundedMergeWidth C) : ChiBounded C

end Lax8.BoundedMergeWidthChiBounded
