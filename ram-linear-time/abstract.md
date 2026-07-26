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

The obligation is discharged in the proof package, through a tower built
for the purpose. At the bottom is a structured while-language with named
scalars and arrays which does its own reading and writing and whose
semantics carries the number of statements executed as a cost; a
compiler lays its variables out in the machine's memory, lowers control
flow to jumps and array indexing to indirect addressing, and a
simulation theorem bounds the machine's step count by a constant
multiple of that cost, the constant depending on the layout alone. Above
it sits a reasoning layer in which an algorithm is verified without
compiled code ever appearing: a judgment "this command takes this state
to that one within this cost", one rule per construct, and a loop rule
taking an invariant together with a cost potential, so that termination
and the running-time bound are a single obligation and amortized
arguments are direct.

The algorithm is the textbook sweep of breadth-first searches, written
in that language and verified against a pure model of the search state,
so that the graph reasoning — a set closed under adjacency contains the
whole component of any vertex it contains — is done on the graph and
never on the machine. Its entire cost is one potential: adjacency slots
not yet scanned, queue capacity not yet used, queue entries not yet
expanded, vertices not yet swept. Because the potential is global the
searches are counted together rather than one at a time, which is what
the amortization needs. The constant that comes out is 2604, where the
compiled program, run on the small graphs it was tested on, takes about
a hundred steps per input number. The factor of twenty-five between them
is deliberate, and so is the slack at every level below: nothing in the
tower argues for a tight constant, and the statement asks only for some
constant.
