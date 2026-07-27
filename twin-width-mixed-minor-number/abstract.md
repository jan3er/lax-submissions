This submission gives a full Lean proof that finite-graph twin-width and
mixed minor number are functionally equivalent: each parameter is bounded by
a numerical function of the other.

The concept surface has five review units. Two are definitions: the complete
definition of mixed minor number — interval divisions, mixed matrix cells,
mixed minors, and vertex-ordered adjacency matrices — phrased with plain
structures and Prop-valued predicates and with the parameter an infimum of
an explicit set of naturals; and the uniform signature of a graph parameter
together with the functional equivalence relation over it. Three are claims:
the two directional bounds, each stated on its own over the twin-width
parameter of submission Lax1 and the mixed minor number, and the headline
equivalence, which applies the equivalence relation to the two parameters
directly. Each direction has its own literature proof and is independently
usable; the equivalence follows from the two by definition.

The proof runs through the Marcus–Tardos theorem, the matrix grid-minor
theorem, and the graph twin-decomposition bridge; both submitted parameters
are proved pointwise equal to their source counterparts, via the
black-is-complete / red-is-non-homogeneous invariant for contraction
sequences and a pointwise division-and-cell translation for mixed minors.
The mixed-minor-to-twin-width direction is transported from the mirrored
Theorem 14 construction, the twin-width-to-mixed direction from the
leaf-order twin-decomposition, and the headline equivalence is assembled
from the two directional statements alone.

Ported from [Édouard Bonnet's original formalization][leaning] of twin-width,
which is MIT-licensed.

[leaning]: https://github.com/EdouardBonnet/leaning
