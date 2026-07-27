This submission is a catch-all home for algorithmic experiments in
Lean: running-time claims about concrete algorithms, stated on a
textbook random access machine and measured by the machine's own step
count. The machine is fixed once, the input encodings are fixed once,
and the submission grows by theorems. Every statement has the same
elementary shape — there are a program and a constant such that, on
every admissible input, the machine halts within an explicit bound,
having written the answer — and nothing in it is asymptotic: a
linear-time claim is the bound $c(|x|+1)$, a fixed-parameter claim is
the bound $c\,2^k(|x|+1)$, and every uniformity claim is carried by
the order of the quantifiers.

Three theorems are stated. The first is that the connected components
of a graph can be computed in linear time: there are one program and
one constant $c$ such that, given any graph in compressed sparse row
form as a word $x$ of natural numbers, the machine halts within
$c(|x|+1)$ steps having labelled every vertex by the least vertex of
its connected component. The second is Courcelle's theorem in the
Courcelle–Makowsky–Rotics form: for every sentence of monadic
second-order logic and every width bound $k$ there are one program and
one constant $c$ such that, given any graph in compressed sparse row
form followed by a $k$-expression that evaluates to it, the machine
halts within $c(|x|+1)$ steps having written $1$ if the sentence holds
in the graph and $0$ if it does not. The third is that vertex cover is
fixed-parameter tractable, with the parameter dependence written into
the bound rather than hidden behind an existential: there are one
program and one constant $c$ such that, given any graph in compressed
sparse row form followed by the single entry $k$, the machine halts
within $c\,2^k(|x|+1)$ steps having written $1$ if the graph has a
vertex cover of at most $k$ vertices and $0$ if it does not — the
program and the constant quantified ahead of the graph *and* the
parameter, which is the uniform notion of fixed-parameter
tractability.

The machine model carries the whole weight of such statements, so the
concept surface is organized to be reused. It has eight review units,
of which the machine, the notion of timed computation and the graph
encoding are the substrate every experiment imports. Five definitions:
the machine itself — an accumulator, an unbounded memory of
natural-number cells, direct and indirect addressing, input and output
tapes, and the instruction set of Aho, Hopcroft and Ullman without
multiplication and division, so that the unit-cost measure is the
honest one; what it means for a program to compute a function of words
within a time bound, the running time being the machine's own step
count rather than an annotation carried alongside the program; the
compressed sparse row encoding of a graph, in the dumb form in which
an algorithm actually receives it, with nothing precomputed, no
sortedness assumed and repetitions permitted; monadic second-order
logic on graphs, with quantification over vertices and over sets of
vertices, its variables counted rather than named so that satisfaction
needs no substitution; and $k$-expressions, which build a graph from
labelled single vertices by disjoint union, edge addition between two
label classes, and relabelling, together with the numbering of those
operations that a machine reading an expression is handed. Three
theorems: the three statements above.

The first two obligations are discharged in the proof package, through
a tower built for the purpose and meant to be built on. At the bottom
is a structured while-language with named scalars and arrays which
does its own reading and writing and whose semantics carries the
number of statements executed as a cost; a compiler lays its variables
out in the machine's memory, lowers control flow to jumps and array
indexing to indirect addressing, and a simulation theorem bounds the
machine's step count by a constant multiple of that cost, the constant
depending on the layout alone. Above it sits a reasoning layer in
which an algorithm is verified without compiled code ever appearing: a
judgment "this command takes this state to that one within this cost",
one rule per construct, and a loop rule taking an invariant together
with a cost potential, so that termination and the running-time bound
are a single obligation and amortized arguments are direct.

The components algorithm is the textbook sweep of breadth-first
searches, written in that language and verified against a pure model of
the search state, so that the graph reasoning — a set closed under
adjacency contains the whole component of any vertex it contains — is
done on the graph and never on the machine. Its entire cost is one
potential: adjacency slots not yet scanned, queue capacity not yet used,
queue entries not yet expanded, vertices not yet swept. Because the
potential is global the searches are counted together rather than one at
a time, which is what the amortization needs. The constant that comes
out is 2604, where the compiled program, run on the small graphs it was
tested on, takes about a hundred steps per input number. The factor of
twenty-five between them is deliberate, and so is the slack at every
level below: nothing in the tower argues for a tight constant, and the
statement asks only for some constant.

Courcelle's theorem is proved the way it is proved on paper, with the
machine kept out of the mathematics until the mathematics is finished.
That mathematics is an Ehrenfeucht–Fraïssé type algebra: a finite space
of types for each quantifier rank, the type of a subset of an ambient
graph under an assignment of marked vertices and sets, adequacy — equal
types satisfy the same sentences of that rank — and a composition lemma
saying that types are preserved when two regions of one graph are glued
along an overlap that is marked on both sides and crossed by no edge
outside it. That lemma is proved at every rank and across two different
ambient graphs at once, which is what lets the four operations of a
$k$-expression be handled uniformly: disjoint union is the composition
lemma at the empty overlap, and edge addition, relabelling and vertex
creation are three inductions of the same shape. From these the value
table of the fold is extracted by finiteness and choice — nothing
computes it, and the theorem does not ask anything to.

The program is a generic bottom-up fold, verified once against a table
it knows nothing about: it reads a tree given by a parent array whose
children are numbered before their parents, materializes the table into
memory in a prologue, and makes one left-to-right pass in which each
node costs a fixed number of array accesses, independent of the size of
the table — and, since the machine has no multiplication, the row bases
of the table are themselves an array, so that indexing it is two reads
and an addition. Instantiating the fold with the type table and adding
an epilogue that turns the root's value into $1$ or $0$ gives the
driver. Its constant is a tower in the sentence and the width, because
the table is, and it is never estimated; but the tower is paid once,
before the input is read, and the input-dependent part of the cost is a
fixed number of steps per entry. The $k$-expression is input rather than
something the program computes; the formalization notes on the theorem
say plainly what that leaves open, as they do for everything else the
statement decides rather than proves.

The vertex cover statement is open. The archive decouples concepts
from proofs — a submission may leave its own obligations open — and a
catch-all submission uses that deliberately: a statement joins the
surface when its form is settled, and its discharge, here a bounded
search tree written in the same while-language and costed by the same
loop rule, can arrive in a later record without the surface moving
under its reviewers. What is proved and what is merely stated is said
plainly, here and in the formalization notes, because the submission's
value is exactly that distinction.
