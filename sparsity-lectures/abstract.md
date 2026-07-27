This submission states the core sparsity theory of nowhere dense graph
classes as it is developed in the lecture notes *Sparsity* of Pilipczuk,
Pilipczuk and Siebertz: nowhere dense classes are uniformly quasi-wide,
the shallow minors of their members have subpolynomial edge density, an
edge-density bound on shallow topological minors bounds admissibility,
admissibility bounds the strong coloring number, the strong coloring number
bounds the weak coloring number, and — as the composition of the last four
— nowhere dense classes have subpolynomial weak coloring numbers.

The concept surface has thirteen review units. Seven definitions: graph
classes on the canonical vertex types; depth-$r$ minors via shallow-minor
models, together with nowhere denseness; the edge density of shallow
minors, both as the per-graph bound $|E(H)| \le d\,|V(H)|$ and as the
class-level predicate $|E(H)| \le c\,m^{1+\varepsilon}$; depth-$r$
topological minors — an injective choice of principal vertices together
with internally disjoint connecting walks of length at most $2r+1$ — with
their per-graph density bound; the generalized coloring numbers
$\mathrm{wcol}_r$ and $\mathrm{scol}_r$, the minima over vertex orderings
of the largest weak respectively strong $r$-reachability count, with the
shared subpolynomial bound predicate $m^{o(1)}$; $r$-admissibility, via
families of short paths from a vertex to smaller vertices that are
disjoint apart from their common start; and uniform quasi-wideness, the
existence — for each radius, uniformly in the requested size — of a
bounded separator after whose deletion a large vertex set contains a large
distance-$r$ independent subset. Six theorems: nowhere dense classes are
uniformly quasi-wide (Lemma 3.4 of Chapter 4 of the notes); nowhere dense
classes have subpolynomial shallow-minor density (Theorem 3.1 of
Chapter 1); a depth-$r$ topological edge-density bound $d$ forces
$\mathrm{adm}_{r+1} \le 1 + 6(r+1)d^3$ (Lemma 3.2 of Chapter 2);
$\mathrm{scol}_r \le 1 + (\mathrm{adm}_r - 1)^r$ (Lemma 2.5);
$\mathrm{wcol}_r \le 1 + r\,(\mathrm{scol}_r - 1)^r$ (Lemma 2.6); and the
headline, that nowhere dense classes have subpolynomial weak coloring
numbers, uniformly over subgraphs of members (Theorem 3.4 of Chapter 2).

The two links of the coloring-number chain are stated separately rather
than as the combined Corollary 2.7 of the notes: they have disjoint proofs,
and each is citable and usable on its own. All parameters are infima of
explicit sets of naturals, and all statements are phrased over the
canonical finite vertex types $\mathrm{Fin}\ n$. The admissibility bound is
stated in the topological form the notes prove, over the topological grad
$\tilde\nabla_r$ rather than over the ordinary grad, with the radius index
shifted by one so that the hypothesis sits at depth $r$ and the conclusion
at radius $r+1$ — the notes' pairing of depth $r-1$ with radius $r$,
without truncated natural subtraction.

The headline theorem is not proved from scratch. It is discharged by a glue
proof that assumes the four preceding theorem concepts — subpolynomial
shallow-minor density, the admissibility bound, and the two coloring-number
links — and performs only the arithmetic composing them, so the internal
proof network of the submission is visible on the archive instead of being
buried inside a single derivation. The other theorem concepts are
discharged by a port of the development accompanying the lecture notes:
a Ramsey-theoretic extraction of distance-independent sets for
quasi-wideness, a Chernoff-based densification argument for the density
theorem, and the tree-counting and path-routing arguments for the
coloring-number chain, each bridged to the submitted concepts. Ramsey's
theorem itself is not reproved here: the quasi-wideness proof assumes the
two Ramsey statements of the submission *Finite Ramsey Theorems for Pairs
and Tuples*, so that dependency is visible on the archive as well.

All material is from the lecture notes *Sparsity* taught at the University
of Warsaw; the numbering above follows the 2019/20 edition of Marcin
Pilipczuk and Michał Pilipczuk, whose 2017/18 predecessor by Michał
Pilipczuk and Sebastian Siebertz carries the same statements under
sequential numbering.
