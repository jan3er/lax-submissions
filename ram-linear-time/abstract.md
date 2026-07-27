This submission is a catch-all home for algorithmic experiments in
Lean: running-time claims about concrete algorithms, stated on the
word RAM — the machine of the archive's model submission *The Word
RAM*, which this one requires — and measured by the machine's own step
count. The input encodings are fixed once, and the submission grows by
theorems. Every statement has the same elementary shape — there are a
program and a constant such that, at every word length $w$, on every
admissible input, admissibility including an explicit fitting
inequality against $2^w$, the machine halts within an explicit bound,
having written the answer — and nothing in it is asymptotic: a
linear-time claim is the bound $c(|x|+1)$, a fixed-parameter claim is
the bound $c\,2^k(|x|+1)$, and every uniformity claim — over the
graph, over the parameter, over the word length — is carried by the
order of the quantifiers.

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

The machine model carries the whole weight of such statements, and it
is deliberately not this submission's: the word RAM and the notion of
computing a function within a time bound are the two concepts of *The
Word RAM*, argued there once for every submission that states running
times. The concept surface here has seven review units. Four
definitions: the compressed sparse row encoding of a graph, in the
dumb form in which an algorithm actually receives it, with nothing
precomputed, no sortedness assumed and repetitions permitted; monadic
second-order logic on graphs, with quantification over vertices and
over sets of vertices, its variables counted rather than named so that
satisfaction needs no substitution; $k$-expressions, which build a
graph from labelled single vertices by disjoint union, edge addition
between two label classes, and relabelling; and the instance encoding
that hands a graph together with a $k$-expression for it to the
machine, the numbering of the operations included. Three theorems: the
three statements above.

All three obligations are discharged in the proof package, and the
tower they are discharged through is not this submission's either. The
structured while-language with named scalars and arrays whose
semantics carries the number of statements executed as a cost, the
compiler laying its variables out in the machine's memory, the
simulation theorem bounding the machine's step count by a constant
multiple of that cost with the constant depending on the layout alone,
and the reasoning layer in which an algorithm is verified without
compiled code ever appearing — one rule per construct, and a loop rule
taking an invariant together with a cost potential, so that
termination and the running-time bound are a single obligation and
amortized arguments are direct — all live in the proof package of *The
Word RAM* and are reused here by requiring it, a dependency on proved
theorems that the kernel checks like any others and that adds nothing
to the axioms, which remain the background ones alone. The word RAM
adds one obligation to that discipline: alongside its cost, every
algorithm accounts for the values it holds, so that the same
derivation that yields the running time also shows no intermediate
value outgrows a word — which is where the fitting conditions in the
statements come from, each chosen for what the machine holds rather
than for what a proof would find convenient.

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
the table — and the row bases of the table are themselves an array, so
that indexing it is two reads and an addition: the compiled driver is
checked, mechanically, to contain no multiplication, division or shift,
so the theorem leans on none of the word RAM's stronger instructions. Instantiating the fold with the type table and adding
an epilogue that turns the root's value into $1$ or $0$ gives the
driver. Its constant is a tower in the sentence and the width, because
the table is, and it is never estimated; but the tower is paid once,
before the input is read, and the input-dependent part of the cost is a
fixed number of steps per entry. The $k$-expression is input rather than
something the program computes; the formalization notes on the theorem
say plainly what that leaves open, as they do for everything else the
statement decides rather than proves.

The vertex cover statement is discharged as well, and by the same
apparatus: the textbook bounded search tree of Downey and Fellows,
written in the same while-language and costed by the same loop rule.
The driver marks vertices in an array and keeps the alternatives it
still owes on a stack, branching on an edge with neither endpoint
marked, and correctness is a single invariant splitting the answer
between the marking it has committed to and the frames it has yet to
try. The cost is again one potential — $4\cdot 2^b-3$ for the subtree
still to be searched at remaining budget $b$, plus slack for the
frames — so the whole tree is paid for by one application of the loop
rule rather than by a recursion, and the factor $2^k$ enters exactly
once, as the potential of the initial configuration. The constant that comes out is
33300: thirty-seven machine steps per statement of the compiled
program, times $900\,2^k(|x|+1)$ statements. No reduction rules are
applied, and nothing here competes with the refined analyses that beat
the base 2. The statement joined the surface before it had a proof,
which is what the archive's decoupling of concepts from proofs is for;
what is proved and what is merely stated is said plainly, here and in
the formalization notes, because the submission's value is exactly
that distinction.
