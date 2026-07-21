import Lax3.Treewidth
import Lax3.TwinWidth

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
twin-width parameters defined in the two prerequisite concepts.
-/

namespace Lax3.ExponentialSeparation

/-- For every `k`, some finite graph has treewidth at most `2*k+4` and
twin-width greater than `2^k`. -/
axiom twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      Lax3.Treewidth.treewidth G ≤ 2 * k + 4 ∧
        2 ^ k < Lax3.TwinWidth.twinWidth G

end Lax3.ExponentialSeparation
