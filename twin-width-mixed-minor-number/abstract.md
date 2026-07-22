This submission gives a full Lean proof that finite-graph twin-width and
mixed minor number are functionally equivalent: each parameter is bounded by
a numerical function of the other.

The concept surface has two review units. The first gives the complete
definition of mixed minor number — interval divisions, mixed matrix cells,
mixed minors, and vertex-ordered adjacency matrices — phrased with plain
structures and Prop-valued predicates, so a reviewer checks named fields
rather than decoding an encoding. The second states the functional
equivalence with the twin-width parameter of submission Lax1. The proof runs
through the Marcus–Tardos theorem, the matrix grid-minor theorem, and the
graph twin-decomposition bridge; its internal development uses structures
with the same fields as the submitted ones, so the translation between the
two is field-by-field.

Ported from the original formalization by Édouard Bonnet
(github.com/EdouardBonnet/leaning, `twin-width`, MIT-licensed).
