First-order model checking is fixed-parameter tractable on nowhere
dense graph classes (Grohe–Kreutzer–Siebertz, JACM 2017), realized as
a verified program on the word RAM of Lax13: for every nowhere dense
class C and every ε > 0, deciding a first-order sentence φ on n-vertex
members of C takes time f(φ, ε, C) · n^(1+ε).

The route is not the original proof. The logic engine is the
rank-preserving locality theorem of Dreier–Toruńczyk
(arXiv 2606.23180), a purely syntactic rewriting; around it the
algorithm is rebuilt from an isolation-form splitter game and sparse
neighborhood covers obtained from weak coloring orderings. The
combinatorial hypotheses — nowhere denseness, uniform quasi-wideness,
subpolynomial weak coloring numbers — are consumed from Lax12; the
machine model and timed computation from Lax13; graph encodings from
Lax11.

(Draft abstract — to be rewritten at P8.)
