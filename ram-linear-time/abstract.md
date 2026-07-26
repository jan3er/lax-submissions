This submission states, on a textbook random access machine, that the
connected components of a graph can be computed in linear time: there
are one program and one constant $c$ such that, given any graph in
compressed sparse row form as a word $x$ of natural numbers, the machine
halts within $c(|x|+1)$ steps having labelled every vertex by the least
vertex of its connected component.

Its purpose is to put running-time claims about concrete algorithms
within reach of the archive, so the machine model carries the whole
weight of the statement. The concept surface has four review units.
Three definitions: the machine itself — an accumulator, an unbounded
memory of natural-number cells, direct and indirect addressing, input
and output tapes, and the instruction set of Aho, Hopcroft and Ullman
without multiplication and division, so that the unit-cost measure is
the honest one; what it means
for a program to compute a function of words within a time bound, the
running time being the machine's own step count rather than an
annotation carried alongside the program; and the compressed sparse row
encoding of a graph, in the dumb form in which an algorithm actually
receives it, with nothing precomputed, no sortedness assumed and
repetitions permitted. One theorem: the linear-time statement itself,
with the program and the constant quantified ahead of the graph.

The proof obligation is presently open. It is to be discharged through a
tower built in the proof package: a structured while-language with named
arrays and a compiler to machine programs whose step count is
bounded by the number of statements executed; a Hoare-style calculus
carrying a time bound; and a first-order program combinator language
with an executable denotation, in which an algorithm is written once and
verified against a Lean function by invariants and variants, never
against compiled code. Breadth-first search then supplies the labelling.
