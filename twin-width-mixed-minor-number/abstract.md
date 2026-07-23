This submission gives a full Lean proof that finite-graph twin-width and
mixed minor number are functionally equivalent: each parameter is bounded by
a numerical function of the other.

The concept surface has two review units. The first gives the complete
definition of mixed minor number — interval divisions, mixed matrix cells,
mixed minors, and vertex-ordered adjacency matrices — phrased with plain
structures and Prop-valued predicates, and with the parameter an infimum of
an explicit set of naturals. The second states the functional equivalence
with the twin-width parameter of submission Lax1, applied directly to the
two parameters through a shared uniform signature. The proof runs through
the Marcus–Tardos theorem, the matrix grid-minor theorem, and the graph
twin-decomposition bridge; both submitted parameters are proved pointwise
equal to their source counterparts, via the black-is-complete /
red-is-non-homogeneous invariant for contraction sequences and a pointwise
division-and-cell translation for mixed minors.

Ported from [Édouard Bonnet's original formalization][leaning] of twin-width,
which is MIT-licensed.

[leaning]: https://github.com/EdouardBonnet/leaning
