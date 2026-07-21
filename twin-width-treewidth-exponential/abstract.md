This submission proves the Bonnet–Déprés separation in the form: for every
natural number $k$, there is a finite simple graph $G$ with
$\mathrm{treewidth}(G) \le 2k+4$ and $2^k < \mathrm{twinWidth}(G)$.

The submitted statement is transparent: it includes self-contained definitions
of treewidth, twin-width, tree decompositions, trigraph states, contraction
steps, and bounded-width contraction sequences, so trusting the statement
requires reading only the small concept modules. The proof constructs the
explicit Bonnet–Déprés graph $BD_k$ and translates between the submitted
definitions and the internal source development.

Ported from the original formalization by Édouard Bonnet
(github.com/EdouardBonnet/leaning, `twin-width`, MIT-licensed).
