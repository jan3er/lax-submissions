import Lax1.LeastNatural
import Lax1.TreeDecompositionWidth

/-!
---
title: Treewidth
---
$\mathrm{treewidth}(G)$ is the least natural number $w$ such that
there exists $D:\mathrm{TreeDecomposition}(G)$ with
$$\mathrm{treeDecompositionWidth}(D)\le w.$$
Equivalently, it is
$$\mathrm{leastNat}\bigl(w\mapsto
    \exists D:\mathrm{TreeDecomposition}(G),\,
      \mathrm{treeDecompositionWidth}(D)\le w\bigr).$$
-/


namespace Lax1.Treewidth

open Lax1.LeastNatural
open Lax1.TreeDecompositionWidth

noncomputable section

/-- The treewidth of a finite graph is the least width of a tree decomposition.
The fallback value is `0` if the search type is empty. -/
def treewidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  leastNat fun width => ∃ D : TreeDecomposition G,
    treeDecompositionWidth D ≤ width

end

end Lax1.Treewidth
