This submission proves the Bonnet–Déprés separation in the form: for every
natural number $k$, there is a finite simple graph $G$ with
$\mathrm{treewidth}(G) \le 2k+4$ and $2^k < \mathrm{twinWidth}(G)$.

The concept surface has three review units: the complete definition of
treewidth, the complete definition of twin-width, and the separation theorem.
Tree decompositions live with treewidth; trigraph states, contractions, and
bounded contraction sequences live with twin-width. Thus each parameter can be
reviewed as one coherent mathematical definition rather than as a collection
of implementation-sized helper concepts. The proof constructs the explicit
Bonnet–Déprés graph $BD_k$ and translates between the submitted definitions and
the internal source development.

Ported from the original formalization by Édouard Bonnet
(github.com/EdouardBonnet/leaning, `twin-width`, MIT-licensed).
