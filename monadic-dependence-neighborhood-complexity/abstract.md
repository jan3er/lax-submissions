This submission states Theorem 2 of Dreier, Mählmann, McCarty, Pilipczuk,
Toruńczyk, *Neighborhood Complexity and Radius-1 Merge-Width in Monadically
Dependent Graph Classes* (2026): every monadically dependent class of finite
graphs has almost linear neighborhood complexity — for every $\varepsilon >
0$ there is a $c$ such that every member $G$ and every nonempty vertex
subset $A$ satisfy $|\{N(v) \cap A : v \in V(G)\}| \le c\,|A|^{1+\varepsilon}$.

The concept surface has twelve review units. Seven definitions: graph classes
on the canonical vertex types, together with weak sparseness; non-copying
first-order transductions between
classes of arbitrary relational structures (a domain formula and one
formula per target relation symbol, over a monadic color expansion); graph
transductions as the special case over the language of graphs; monadic
dependence (the class does not transduce all graphs); neighborhood
complexity, with the shared bound predicate $|A|^{1+o(1)}$; nowhere
denseness via shallow-minor models; and weak coloring numbers, with the
shared subpolynomial bound predicate. Five theorems: weakly sparse
monadically dependent classes are nowhere dense; nowhere dense classes have
subpolynomial weak coloring numbers, uniformly over subgraphs of members;
nowhere dense classes have almost linear neighborhood complexity; the
headline theorem; and nowhere dense classes are monadically dependent
(Adler–Adler).

The proof package discharges the headline theorem via the paper's
VC-dimension sparsification argument; the nowhere dense counting
statement from the coloring-number theorem, via radius-1 trace counting
along a weak coloring order and localization; the weakly sparse
theorem via Mählmann's Ramsey-theoretic extraction of induced subdivided
bicliques (thesis, Lemma 13.8) together with a star-crossing transduction
of all graphs; and the Adler–Adler direction via uniform quasi-wideness
and a semantic locality argument — the deletion specialization of the
flip-breakability route, with hereditarily finite rank-bounded local
types of decorated balls and a ball-swap back-and-forth system in place
of Gaifman's theorem. A transduction of all graphs would shatter
arbitrarily large sets; quasi-wide scattering, a local-type pigeonhole,
and the swap lemma refute this. With that, all five theorem concepts are
proved, and every one reports only Lean's standard logical axioms — the
surface carries the full classical equivalence that on weakly sparse
classes, monadic dependence and nowhere denseness coincide.
