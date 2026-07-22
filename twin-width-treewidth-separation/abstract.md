This submission proves the Bonnet–Déprés separation in the form: for every
natural number $k$, there is a finite simple graph $G$ with
$\mathrm{treewidth}(G) \le 2k+4$ and $2^k < \mathrm{twinWidth}(G)$.

The concept surface has three review units: the complete definition of
treewidth, the complete definition of twin-width, and the separation theorem.
Tree decompositions live with treewidth; trigraph states, contractions, and
bounded contraction sequences live with twin-width. Each parameter reads as
one coherent mathematical definition, phrased with plain structures and
Prop-valued predicates, so a reviewer checks named fields rather than
decoding an encoding. The proof constructs the explicit Bonnet–Déprés graph
$BD_k$; its internal development uses structures with the same fields as the
submitted ones, so the translation between the two is field-by-field.

Ported from the original formalization by Édouard Bonnet
(github.com/EdouardBonnet/leaning, `twin-width`, MIT-licensed).
