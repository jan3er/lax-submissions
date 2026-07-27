import Lax12.NowhereDenseClasses
import Lax12.UniformQuasiWideness

/-!
---
title: Nowhere dense classes are uniformly quasi-wide
type: theorem
---
Every nowhere dense graph class is uniformly quasi-wide: for every
radius *r* there are a threshold function *N* and a separator bound *s*
such that in every member, every vertex set of size at least *N*(*m*)
contains a distance-*r* independent subset of size at least *m* after
deleting at most *s* vertices.

# Formalization notes

Hypothesis and conclusion are the shared predicates of the two imported
definition concepts, so the statement adds nothing of its own. The
strength of the theorem is entirely in the quantifier order already
carried by `UniformlyQuasiWide`: the separator bound depends on the
class and the radius alone, not on the requested size or on the member.
The converse implication holds on subgraph-closed classes but is a
separate claim with a separate proof and is not stated here.
-/

namespace Lax12.NowhereDenseUQW

open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.UniformQuasiWideness

/-- Nowhere dense graph classes are uniformly quasi-wide. -/
axiom uniformlyQuasiWide_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    UniformlyQuasiWide C

end Lax12.NowhereDenseUQW
