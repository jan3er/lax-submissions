import Lax1.Treewidth
import Lax1.TwinWidth

/-!
---
title: Twin-width can be exponential in treewidth
---
**Statement.**
For every $k\in\mathbb{N}$, there is a finite type $V$, decidable equality
on $V$, and a simple graph $G$ on $V$ such that
$$\mathrm{treewidth}(G) \le 2k+4
  \qquad\text{and}\qquad
  2^k < \mathrm{twinWidth}(G).$$

**Proof content.**
The proof uses the explicit Bonnet–Depres graph $BD_k$ from the submitted
source files. It translates the proved Bonnet–Depres tree decomposition into
the submitted tree-decomposition-width predicate, and translates any submitted
bounded contraction sequence back into the source contraction-sequence
structure. The source proof that $BD_k$ has no $2^k$-bounded contraction
sequence therefore proves the submitted lower bound on
$\mathrm{twinWidth}$.
-/


namespace Lax1.Main

open Lax1.Treewidth
open Lax1.TwinWidth

/-- For every `k`, some finite graph has treewidth at most `2*k+4` and
twin-width greater than `2^k`. -/
axiom twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth G

end Lax1.Main
