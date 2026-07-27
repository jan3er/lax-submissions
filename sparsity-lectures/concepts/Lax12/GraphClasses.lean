import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
---
title: Graph classes
type: definition
---
A graph class is a set of finite simple graphs. A class contains, for
each number of vertices *n*, some of the simple graphs on the canonical
*n*-element vertex type.

# Formalization notes

Every finite simple graph is isomorphic to a graph on some `Fin n`, so
ranging over the canonical carriers loses no generality. Closure under
isomorphism is deliberately not required: no statement of this
submission needs it, and all hypotheses range over concrete members.
`GraphClass` is an abbreviation, so class membership is plain
application `C n G` throughout the submission, and any identically
shaped abbreviation elsewhere denotes literally the same function type.
-/

namespace Lax12.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax12.GraphClasses
