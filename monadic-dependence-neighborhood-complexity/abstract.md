This submission states Theorem 2 of Dreier, Mählmann, McCarty, Pilipczuk,
Toruńczyk, *Neighborhood Complexity and Radius-1 Merge-Width in Monadically
Dependent Graph Classes* (2026): every monadically dependent class of finite
graphs has almost linear neighborhood complexity — for every $\varepsilon >
0$ there is a $c$ such that every member $G$ and every nonempty vertex
subset $A$ satisfy $|\{N(v) \cap A : v \in V(G)\}| \le c\,|A|^{1+\varepsilon}$.
Neighborhood complexity is a notion of sparsity theory, and the theorem
extends a classical bound for nowhere dense classes to a much larger,
model-theoretically defined family. The submission is organized to say
exactly that: it builds on the *Sparsity Lectures* submission (Lax12), whose
concepts of graph classes, nowhere denseness and neighborhood complexity it
imports and states its own theorems over, and it contributes the
model-theoretic side — transductions, monadic dependence, weak sparseness —
together with three theorems relating the two.

The concept surface has seven review units. Four definitions: weakly sparse
graph classes — the class of all graphs and weak sparseness, the exclusion
of some complete bipartite graph $K_{t,t}$ as a subgraph, on top of the
imported notion of a graph class; non-copying first-order transductions
between classes of arbitrary relational structures (a domain formula and one
formula per target relation symbol, over a monadic color expansion); graph
transductions as the special case over the language of graphs; and monadic
dependence (the class does not transduce all graphs). Three theorems: weakly
sparse monadically dependent classes are nowhere dense; the headline
theorem; and nowhere dense classes are monadically dependent (Adler–Adler).
The nowhere-denseness hypotheses and conclusions, and the almost-linear
bound predicate $|A|^{1+o(1)}$, are the imported and separately endorsed
definitions of Lax12, so these three statements compose directly with the
sparsity theory stated there — no restatement, and no second copy of a
notion that already has a home.

The proof package discharges the headline theorem via the paper's
VC-dimension sparsification argument; the weakly sparse theorem via
Mählmann's Ramsey-theoretic extraction of induced subdivided bicliques
(thesis, Lemma 13.8) together with a star-crossing transduction of all
graphs; and the Adler–Adler direction via uniform quasi-wideness and a
semantic locality argument — the deletion specialization of the
flip-breakability route, with hereditarily finite rank-bounded local types
of decorated balls and a ball-swap back-and-forth system in place of
Gaifman's theorem. A transduction of all graphs would shatter arbitrarily
large sets; quasi-wide scattering, a local-type pigeonhole, and the swap
lemma refute this. With that, all three theorem concepts are proved — the
surface carries the full classical equivalence that on weakly sparse
classes, monadic dependence and nowhere denseness coincide.

The proofs do not contain the classical sparsity and Ramsey material they
rest on; they *assume* it, from two upstream submissions, so that the
dependency is visible in the archive's proof network. Uniform quasi-wideness
of nowhere dense classes, and their almost linear neighborhood complexity,
are assumed from the *Sparsity Lectures* submission (Lax12), which
formalizes the lecture notes of Pilipczuk, Pilipczuk and Siebertz; Ramsey's
theorem for colourings of pairs and its order-type form for tuples are
assumed from the *Finite Ramsey* submission (Lax14). Inside this submission
the same discipline applies: the terminal step of the headline proof
composes the *statements* of the two halves of the paper's Corollary 6 — the
weakly sparse theorem stated here and the nowhere dense counting theorem
stated in Lax12 — instead of importing their proofs. What each proof reports
beyond Lean's standard logical axioms is exactly the list in its
`assumptions` block.
