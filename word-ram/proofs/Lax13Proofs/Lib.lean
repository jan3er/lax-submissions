import Lax13Proofs.Lib.Basic
import Lax13Proofs.Lib.Ind

/-!
The data-structure library: one module per structure, each an
abstraction relation and its operations exported as `Spec`s with cost.

`Lib/Basic.lean` holds what they share — the pointwise cell update, and
the driver their worked examples are checked with. `Lib/Ind.lean` is the
indicator array, and its header states the shape the remaining modules
follow.
-/
