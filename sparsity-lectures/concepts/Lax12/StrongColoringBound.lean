import Lax12.Admissibility
import Lax12.ColoringNumbers

/-!
---
title: Strong coloring numbers are bounded by admissibility
type: theorem
---
The strong *r*-coloring number of a graph is at most
1 + (adm_r − 1)^*r*, where adm_r is its *r*-admissibility. Together with
the trivial bound adm_r ≤ scol_r this says that admissibility and the
strong coloring number are functionally equivalent parameters.

# Formalization notes

Both parameters are the minima over vertex orderings defined in the
imported concepts, and the statement is the minimized form: the
literature proves it for each ordering separately, and the minimized
form follows because the right-hand side is monotone in adm_r, so an
ordering optimal for admissibility witnesses the bound. Natural
subtraction `adm_r − 1` is harmless: admissibility counts the vertex
itself, so it is at least 1 on every nonempty graph, and on the empty
graph both sides degenerate to a true inequality.
-/

namespace Lax12.StrongColoringBound

open Lax12.Admissibility Lax12.ColoringNumbers

/-- The strong `r`-coloring number is at most `1 + (adm_r - 1) ^ r`. -/
axiom scol_le_of_adm {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    scol G r ≤ 1 + (adm G r - 1) ^ r

end Lax12.StrongColoringBound
