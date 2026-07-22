import Lax1.Treewidth
import Lax1.TwinWidth

/-!
---
title: Twin-width can be exponential in treewidth
---
For every $k\in\mathbb{N}$, there is a finite simple graph $G$ such that
$$
  \operatorname{tw}(G) \le 2k+4
  \quad\text{and}\quad
  2^k < \operatorname{tww}(G).
$$
Here $\operatorname{tw}$ and $\operatorname{tww}$ are the treewidth and
twin-width parameters defined in the two prerequisite concepts. The graph is
quantified over the canonical finite vertex types $\operatorname{Fin} n$,
which loses no generality: every finite simple graph is isomorphic to a
graph on some $\operatorname{Fin} n$.
-/

namespace Lax1.ExponentialSeparation

/-- For every `k`, some finite graph has treewidth at most `2 * k + 4` and
twin-width greater than `2 ^ k`. -/
axiom twin_width_can_be_exponential_in_treewidth (k : ℕ) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      Lax1.Treewidth.treewidth G ≤ 2 * k + 4 ∧
        2 ^ k < Lax1.TwinWidth.twinWidth G

end Lax1.ExponentialSeparation
