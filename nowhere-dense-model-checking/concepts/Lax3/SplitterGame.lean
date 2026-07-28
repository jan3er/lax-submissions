import Lax3.ColoredGraphs
import Lax12.UniformQuasiWideness

/-!
---
title: The isolation splitter game
type: definition
---
The (*ℓ*, *m*, *r*)-splitter game is played on a graph by two players,
Connector and Splitter. In each round, Connector picks a vertex *v* of
the current arena; the arena is restricted to the ball of radius *r*
around *v*; then Splitter picks a batch *W* of at most *m* vertices
inside that ball and isolates it — every edge incident to *W* is
deleted. Splitter wins when the arena becomes edgeless; if that has not
happened after *ℓ* rounds, Connector wins.

The game is Definition 4.1 of Chapter 4 of the source lecture notes
(2019/20 edition), in an *isolation* variant: where the notes delete
Splitter's vertices from the arena, here the batch keeps its vertices
and loses its incident edges, and the winning condition "the arena is
empty" becomes "the arena is edgeless". Vertices never disappear, so
every arena of a play lives on the vertex set of the original graph.
The model-checking algorithm of this submission descends the game tree
of this variant: keeping the vertices is what lets its rewriting step
translate formulas through an isolation uniformly, with no case split
on whether a variable lands on the batch.

# Formalization notes

Both moves of a round are the same operation: restricting to the ball
around Connector's vertex is `deleteVerts` of the ball's complement,
and isolating Splitter's batch is `deleteVerts` of the batch —
Lax12's `deleteVerts`, which removes the edges incident to a set and
keeps the vertex type, is used for both, and is not restated here.
Arenas therefore only ever lose edges, which is the invariant the win
proof and the evaluator downstream both ride on (a vertex isolated
once is isolated in every later arena).

`SplitterWins m r ℓ G` is defined by recursion on the remaining round
budget: with budget `0` Splitter has won exactly if the arena is
edgeless; with positive budget, if the arena is edgeless or for every
Connector move there is a batch after which he wins with the rest of
the budget. This says exactly "Splitter has a winning strategy within
`ℓ` rounds" without carrying strategy functions on the surface; the
explicit strategy — the object the algorithm executes — appears
proofs-side with the win theorem's discharge. (An inductive
winning-position predicate would say the same thing, but its step
constructor nests the ∀/∃ alternation of a round through `Exists`,
which Lean's kernel rejects as a nested inductive; the recursion on
the budget is the same mathematics and unfolds one round at a time.)
Allowing the edgeless win at any budget, rather than only after a
move, only enlarges Splitter's winning positions by games he has
already won and matches the algorithm's base case, which stops at an
edgeless arena before playing a round.

The batch is a `Set` with an `ncard` bound, the idiom of Lax12's
quasi-wideness statements. The edgeless condition is `G = ⊥`,
mathlib's empty graph.
-/

namespace Lax3.SplitterGame

open Lax3.ColoredGraphs
open Lax12.UniformQuasiWideness

/-- Winning positions of Splitter in the (`ℓ`, `m`, `r`)-isolation
splitter game, by recursion on the remaining budget `ℓ`: the arena `G`
is already edgeless, or a round is left and for every vertex Connector
plays there is a batch of at most `m` vertices of its `r`-ball whose
isolation, after restricting the arena to that ball, is a winning
position with one round fewer. -/
def SplitterWins {n : ℕ} (m r : ℕ) : ℕ → SimpleGraph (Fin n) → Prop
  | 0, G => G = ⊥
  | ℓ + 1, G => G = ⊥ ∨
      ∀ v : Fin n, ∃ W : Set (Fin n), W ⊆ ball G r v ∧ W.ncard ≤ m ∧
        SplitterWins m r ℓ (deleteVerts (deleteVerts G (ball G r v)ᶜ) W)

end Lax3.SplitterGame
