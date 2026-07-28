import Lax3.SplitterGame
import Lax12.NowhereDenseClasses

/-!
---
title: Splitter wins on nowhere dense classes
type: theorem
---
On a nowhere dense class, Splitter wins the isolation splitter game:
for every radius *r* there are a round bound *ℓ* and a batch bound *m*,
depending only on the class and *r*, such that Splitter wins the
(*ℓ*, *m*, *r*)-game on every member.

This is Lemma 4.2 of Chapter 4 of the source lecture notes (2019/20
edition) — Theorem 4.2 of Grohe–Kreutzer–Siebertz in the batch form —
transposed to the isolation variant of the game. The bound is the
qualitative heart of the model-checking algorithm: the game tree has
bounded depth, so the recursion that descends it does bounded work per
vertex.

# Formalization notes

The hypothesis is `Lax12.NowhereDense` verbatim, and the proof to come
derives the strategy from Lax12's `uniformlyQuasiWide_of_nowhereDense`,
following the notes' path-maintenance strategy: Splitter maintains
BFS paths to the connector vertices of earlier rounds and isolates the
still-active vertices of those paths, with `ℓ = N_r(2·s_r + 2)` and
`m = ℓ · (r + 1)` for the quasi-wideness margins `N_r, s_r`. Two
remarks recorded for the discharge. First, the notes state
`ℓ = N_r(2·s_r + 1)`, but their proof extracts `s_r + 1` pairwise
disjoint paths so that one avoids the deleted separator, which needs
the `+ 2` form; the formalization takes the `+ 2` form and fixes the
slip silently. Second, the isolation variant needs no new argument
over the notes' deletion variant: arenas only lose edges, so a vertex
isolated in some round has no incident edge in any later arena — the
paths the strategy cuts stay cut, and the distance-independent set the
contradiction extracts is independent in exactly Lax12's
`deleteVerts` sense, which is the conclusion shape of the endorsed
quasi-wideness theorem.

The statement quantifies the strategy away: it asserts winning
positions, not a strategy function. The explicit strategy — the object
the model-checking program executes — is constructed proofs-side with
this axiom's discharge and consumed there by the program-correctness
proofs; surfacing it would freeze implementation detail into the
concept.
-/

namespace Lax3.NowhereDenseSplitter

open Lax3.SplitterGame
open Lax12.GraphClasses Lax12.NowhereDenseClasses

/-- On a nowhere dense class, for every radius there are round and
batch bounds with which Splitter wins the isolation splitter game on
every member. -/
axiom splitterWins_of_nowhereDense (C : GraphClass) (h : NowhereDense C)
    (r : ℕ) :
    ∃ ℓ m : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      SplitterWins m r ℓ G

end Lax3.NowhereDenseSplitter
