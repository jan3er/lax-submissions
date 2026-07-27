import Lax12.ColoringNumbers

/-!
---
title: Weak coloring numbers are bounded by strong coloring numbers
type: theorem
---
The weak *r*-coloring number of a graph is at most
1 + *r* · (scol_r − 1)^*r*, where scol_r is its strong *r*-coloring
number. With the trivial bound scol_r ≤ wcol_r this says that the two
generalized coloring numbers are functionally equivalent parameters.

This is Lemma 2.6 of Chapter 2 of the source lecture notes (2019/20
edition), which state it for a fixed vertex ordering; composed with
their Lemma 2.5 it gives their Corollary 2.7,
wcol_r ≤ 1 + *r*(adm_r − 1)^(*r*²).

# Formalization notes

Both parameters are the minima over vertex orderings defined in the
imported concept, and the statement is the minimized form: the
literature proves it for each ordering separately, and the minimized
form follows because the right-hand side is monotone in scol_r, so an
ordering optimal for the strong coloring number witnesses the bound. The
proof idea is that a weakly reachable vertex is found by a bounded
search tree of strongly reachable vertices, of depth *r* and branching
scol_r − 1. Natural subtraction is harmless: strong coloring numbers
count the vertex itself, so they are at least 1 on every nonempty graph.
-/

namespace Lax12.WeakColoringBound

open Lax12.ColoringNumbers

/-- The weak `r`-coloring number is at most `1 + r · (scol_r - 1) ^ r`. -/
axiom wcol_le_of_scol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    wcol G r ≤ 1 + r * (scol G r - 1) ^ r

end Lax12.WeakColoringBound
