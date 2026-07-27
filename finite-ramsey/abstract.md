This submission puts the finite Ramsey theorems for pairs and for tuples on
the archive as citable, dependency-free statements: a colouring of the pairs
or of the ordered tuples of a large enough finite set always admits a large
homogeneous subset. Nothing in mathlib states a finite Ramsey theorem at the
pinned revision, and the material formalized here was until now buried inside
the proof package of another submission, where nothing could cite it.

The concept surface has four review units. One definition: the order type of
a tuple over a linearly ordered set — the relation recording which
coordinates carry strictly smaller entries than which — kept Prop-valued,
since in a linear order the strict-order pattern already determines the
equality pattern. Three claims: the multicolour Ramsey theorem for pairs,
that every colouring of the unordered pairs of a large enough finite set with
*k* colours has a monochromatic subset of any requested size; Ramsey's
theorem in the graph form the literature cites, that every large enough graph
has a clique on *a* vertices or an independent set on *b* vertices; and the
Erdős–Rado theorem for tuples, that every colouring of the *l*-tuples over a
large enough linearly ordered finite set has a large subset on which the
colour of a tuple depends only on its order type. All three are existential
bounds over the canonical carriers `Fin n`, with sizes counted by `Set.ncard`
and stated as "at least"; no positivity hypothesis is placed on the number of
colours, and no Ramsey number is defined, since no statement here consumes a
numeric bound.

The graph form is the two-colour case of the multicolour form, and it is
discharged inside this submission by a glue proof assuming that statement and
nothing else: a pair is coloured by whether it is an edge, and the two colour
classes are read as a clique and as an independent set. The archive therefore
records the derivation rather than hiding it. The multicolour statement
itself is proved by induction on the list of colours from the two-colour
case, which is the Erdős–Szekeres neighbourhood-splitting induction; the
tuple statement by Erdős–Rado chain building for strict-monotone tuples,
followed by factoring an arbitrary tuple through its rank pattern and
iterating over the finitely many patterns.

The proofs are ported from the proof package of the submission *Almost linear
neighborhood complexity of monadically dependent graph classes*, where the
same theorems were proved as internal lemmas. This submission requires
nothing but mathlib and is intended as an assumption target: Ramsey's theorem
is the archetypal statement other submissions want to cite rather than
reprove.
