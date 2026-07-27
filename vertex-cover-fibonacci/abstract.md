This submission states one theorem and proves it: vertex cover is
decided on the word RAM within $c\,\mathrm{fib}(k+2)\,(|x|+1)$ steps.
There are one program and one constant $c$ such that, at every word
length $w$, given any graph in compressed sparse row form followed by
the single entry $k$ as a word $x$ for which $c(|x|+k+1)$ is at most
$2^w$, the machine halts within that many steps, having written $1$ if
the graph has a vertex cover of at most $k$ vertices and $0$ if it does
not. Nothing in the statement is asymptotic — the bound is that
explicit term, at every $k$ rather than eventually — and every
uniformity claim, over the graph, over the parameter and over the word
length, is carried by the order of the quantifiers, with the program
and the constant standing ahead of all three.

The machine, the notion of computing a function within a time bound and
the input format are not this submission's. The first two are the two
concepts of *The Word RAM*; the third is the instance encoding of
*Algorithmic Experiments on a Random Access Machine*, whose vertex cover
theorem is the same statement with $2^k$ in place of
$\mathrm{fib}(k+2)$. Both are required, and the admissible set here is
character for character that one's, so the two bounds are claims about
literally the same inputs on literally the same machine. This one
sharpens that one; it does not unsay it. The $2^k$ bound is the textbook
analysis, it is proved, and it stays true — what is new is that the same
problem admits a smaller explicit bound. That is the point of writing
the parameter dependence into the statement instead of hiding it behind
an existential over computable functions: improving the base is then a
change of statement rather than a change of commentary. The golden ratio
is not the end of the ladder either, and nothing here competes with the
refined analyses that go below it.

What changes is the branching rule. The textbook bounded search tree
branches on an *edge*: one of its two endpoints lies in every cover, so
trying both to depth $k$ costs a factor of two per unit of budget.
Branching on a *vertex* of residual degree at least two costs less —
either the vertex is in the cover, at one unit of budget, or it is not
and then all of its at least two remaining neighbours are, at two units
or more — so the leaf count obeys $T(k)\le T(k-1)+T(k-2)$ and is
$\mathrm{fib}(k+2)$, which is
$(\varphi^{2}/\sqrt5)\,\varphi^{k}\,(1+o(1))\approx 1.17\,\varphi^{k}$
with $\varphi\approx1.618$. Where the rule does not apply, no search is
needed: if no unmarked vertex has two uncovered edges on it then the
uncovered edges form a matching, and the answer is whether there are at
most $k$ of them. The bound is stated through mathlib's `Nat.fib` and
not through a power of a real number, so that no rounding enters — the
search tree really does have $\mathrm{fib}(k+2)$ leaves, and that count
is what the proof produces.

The concept surface is a single review unit, and it defines nothing.
mathlib's vertex cover number is the answer, mathlib's `Nat.fib` is the
bound, the compressed sparse row encoding and the instance format that
appends the parameter to it are the earlier submission's, and the
machine together with the predicate "this program computes this function
within this bound at this word length" are the word RAM's. A reviewer is
asked about one sentence and nothing else. The formalization notes on it
say what the statement decides rather than proves: why the fitting
condition is an admissibility condition on inputs rather than a
hypothesis — a graph with an edge has encodings of every length, so as a
hypothesis it would be empty — and why that condition is deliberately
not coupled to the running time, since asking $\mathrm{fib}(k+2)$ to fit
into a word would exclude exactly the instances the theorem is about.

The obligation is discharged in the same submission: statement and proof
ship together, unlike the $2^k$ statement, which joined the surface
before it had a proof. The apparatus is the earlier one, reused rather
than rebuilt — the structured while-language of *The Word RAM*, its
compiler and simulation theorem, and its loop rule taking an invariant
together with a cost potential — required as proved theorems that the
kernel checks like any others, so the axioms remain the three background
ones. The mathematics is done with the machine out of sight: the
residual graph at a node of the search, three lemmas disposing of a node
(at most $b$ residual edges admit a cover within $b$; a residual
matching of more than $b$ edges admits none; branching on a vertex is
exhaustive), and a pure configuration — a stack of frames, each carrying
the budget it was pushed at, since the two children of a branch no
longer cost the same, and each recording the height of a trail of marked
vertices, since a frame on its second branch marks a whole neighbourhood
and cannot undo it by name. Correctness is one invariant splitting the
answer between the marking committed to and the alternatives the frames
still owe. The cost is one potential, $4\,\mathrm{fib}(b+2)-3$ for the
subtree still to be searched at remaining budget $b$ plus slack per
frame, which every one of the eight transitions strictly decreases, so
the whole tree is paid for by a single application of the loop rule
rather than by a recursion, and $\mathrm{fib}(k+2)$ enters exactly once,
as the potential of the initial configuration.

One subtlety is specific to the improved bound. The encoding is allowed
to name a neighbour of a vertex several times, so the number of slots in
a block is not the degree of the vertex. A branching test that counts
unmarked slots would branch at a vertex with a single residual
neighbour, where the second branch buys one unit of budget instead of
two and the Fibonacci recurrence fails — and on $k$ disjoint edges with
every slot doubled it would search a $2^k$ tree on an instance the
correct program answers without a single branch. So the driver's test
compares the *targets* of unmarked slots rather than counting them, and
the residual edge count is capped at one per block; the smallest witness,
a nine-number word encoding one edge, is kept in the proof package as a
machine-checked standing warning. The constant that comes out is 90300:
forty-three machine steps per statement of the compiled program — the
layout has eight arrays, so one index computation is ten instructions —
times $2100\,\mathrm{fib}(k+2)(|x|+1)$ statements. Nothing at any level
was fought for, and the $2^k$ driver's constant, 33300, is the smaller
of the two; on small shared instances that driver is also the faster
program. Where the base bites, the order reverses: on five disjoint
edges with every slot doubled it takes 52554 steps and this one takes
4572. The claim is about the exponent, not about the constant.
