This submission proves the Bonnet–Déprés separation in the form: for every
natural number $k$, there is a finite simple graph $G$ with
$\mathrm{treewidth}(G) \le 2k+4$ and $2^k < \mathrm{twinWidth}(G)$.

The concept surface has three review units: the complete definition of
treewidth, the complete definition of twin-width, and the separation theorem.
Treewidth is phrased through tree decompositions with a bag-size bound;
twin-width through contraction sequences of vertex partitions whose red
degrees are derived from homogeneity in the graph, so no auxiliary state is
carried alongside the partitions. Both parameters are infima of explicit sets
of naturals, and the separation is stated over the canonical finite vertex
types $\mathrm{Fin}\ n$. The proof constructs the explicit Bonnet–Déprés
graph $BD_k$ in a trigraph-based source development and bridges it to the
submitted concepts through the invariant that, along any contraction
sequence, black pairs are exactly the complete pairs and red pairs exactly
the non-homogeneous pairs.

Ported from the original formalization by Édouard Bonnet
(github.com/EdouardBonnet/leaning, `twin-width`, MIT-licensed).
