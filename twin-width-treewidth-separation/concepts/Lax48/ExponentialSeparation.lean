import Lax48.Treewidth
import Lax48.TwinWidth

/-!
---
title: Twin-width can be exponential in treewidth
type: theorem
---
For every natural number *k*, there is a finite simple graph *G* with
treewidth at most 2*k* + 4 and twin-width greater than 2ᵏ. Treewidth and
twin-width are the parameters defined in the two prerequisite concepts.

# Formalization notes

The graph is quantified over the canonical finite vertex types `Fin n`,
which loses no generality: every finite simple graph is isomorphic to a
graph on some `Fin n`.
-/

namespace Lax48.ExponentialSeparation

/-- For every `k`, some finite graph has treewidth at most `2 * k + 4` and
twin-width greater than `2 ^ k`. -/
axiom exists_treewidth_le_and_two_pow_lt_twinWidth (k : ℕ) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      Lax48.Treewidth.treewidth G ≤ 2 * k + 4 ∧
        2 ^ k < Lax48.TwinWidth.twinWidth G

end Lax48.ExponentialSeparation
