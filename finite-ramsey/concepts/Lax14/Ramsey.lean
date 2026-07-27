import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

/-!
---
title: Ramsey's theorem
type: theorem
---
For all *a* and *b* there is an *N* such that every graph on at least *N*
vertices contains a clique on *a* vertices or an independent set on *b*
vertices. Equivalently: colouring the edges of a large enough complete
graph with two colours always leaves a monochromatic clique.

# Formalization notes

A clique is a set of pairwise adjacent vertices and an independent set a
set of pairwise non-adjacent vertices, both in mathlib's `Set`-valued,
`Prop`-valued form (`IsIndepSet` is by definition pairwise
non-adjacency, so no complement graph and no decidability appear in the
statement). Sizes are counted with `Set.ncard` and stated as "at least",
as everywhere in this submission.

Graphs range over the canonical carriers `Fin n` for all `n` beyond the
bound, so the statement applies to a graph on any finite vertex set by
transport along a bijection.

This is the two-colour case of the multicolour concept of this
submission — colour a pair by whether it is an edge — and it is proved
that way, by a glue proof assuming that statement. It gets its own
statement because it is the form the literature cites and the form
graph-theoretic applications consume, and because a submission's headline
should not be reachable only through a strengthening.
-/

namespace Lax14.Ramsey

/-- Ramsey's theorem: a large enough graph contains a clique on `a`
vertices or an independent set on `b` vertices. -/
axiom exists_clique_or_indepSet (a b : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n →
      (∃ S : Set (Fin n), G.IsClique S ∧ a ≤ S.ncard) ∨
      (∃ S : Set (Fin n), G.IsIndepSet S ∧ b ≤ S.ncard)

end Lax14.Ramsey
