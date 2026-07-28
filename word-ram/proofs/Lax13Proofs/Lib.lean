import Lax13Proofs.Lib.Basic
import Lax13Proofs.Lib.Ind
import Lax13Proofs.Lib.Stack
import Lax13Proofs.Lib.Trail
import Lax13Proofs.Lib.Queue

/-!
The data-structure library: one module per structure, each an
abstraction relation and its operations exported as `Spec`s with cost.

`Lib/Basic.lean` holds what they share — the pointwise cell update, and
the driver their worked examples are checked with. `Lib/Ind.lean` is the
indicator array, and its header states the shape the remaining modules
follow. `Lib/Stack.lean` is the search stack of both drivers, and
`Lib/Trail.lean` the undo trail of Lax15's two rungs, whose `unwind`
loop is the first loop the kit exports as a `Spec`. `Lib/Queue.lean` is
the breadth-first queue of the two search drivers; its `drain` is the
first loop the kit exports with the *body* left to the caller, since in
both consumers the body is the algorithm.
-/
