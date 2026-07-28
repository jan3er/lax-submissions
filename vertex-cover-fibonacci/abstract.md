This submission states two theorems and proves both: vertex cover is
decided on the word RAM within $c\,\mathrm{fib}(k+2)\,(|x|+1)$ steps,
and — with a second program and a second constant — within
$c\,\mathrm{branchCount}(k)\,(|x|+1)$ steps, where $\mathrm{branchCount}$
is the leaf count of a search tree that splits a budget $b$ into $b-1$
and $b-3$. Each statement has the same shape: there are one program and
one constant $c$ such that, at every word length $w$, given any graph in
compressed sparse row form followed by the single entry $k$ as a word
$x$ for which $c(|x|+k+1)$ is at most $2^w$, the machine halts within
that many steps, having written $1$ if the graph has a vertex cover of at
most $k$ vertices and $0$ if it does not. Nothing in either statement is
asymptotic — the bound is that explicit term, at every $k$ rather than
eventually — and every uniformity claim, over the graph, over the
parameter and over the word length, is carried by the order of the
quantifiers, with the program and the constant standing ahead of all
three.

The machine, the notion of computing a function within a time bound and
the input format are not this submission's. The first two are the two
concepts of *The Word RAM*; the third is the instance encoding of
*Algorithmic Experiments on a Random Access Machine*, whose vertex cover
theorem is the same statement with $2^k$ in place of the two bounds
here. Both are required, and the admissible set here is character for
character that one's, so all three bounds are claims about literally the
same inputs on literally the same machine. They are three rungs of one
ladder, and each sharpens the one below without unsaying it: the $2^k$
bound is the textbook analysis, it is proved, and it stays true — what is
new is that the same problem admits smaller explicit bounds. That is the
point of writing the parameter dependence into the statement instead of
hiding it behind an existential over computable functions: improving the
base is then a change of statement rather than a change of commentary.
The real root of $x^3=x^2+1$ is not the end of the ladder either, and
nothing here competes with the refined analyses that go below it.

What changes from rung to rung is the branching rule. The textbook
bounded search tree branches on an *edge*: one of its two endpoints lies
in every cover, so trying both to depth $k$ costs a factor of two per
unit of budget. Branching on a *vertex* of residual degree at least two
costs less — either the vertex is in the cover, at one unit of budget, or
it is not and then all of its at least two remaining neighbours are, at
two units or more — so the leaf count obeys $T(k)\le T(k-1)+T(k-2)$ and
is $\mathrm{fib}(k+2)$, which is
$(\varphi^{2}/\sqrt5)\,\varphi^{k}\,(1+o(1))\approx 1.17\,\varphi^{k}$
with $\varphi\approx1.618$. Where that rule does not apply, no search is
needed: if no unmarked vertex has two uncovered edges on it then the
uncovered edges form a matching, and the answer is whether there are at
most $k$ of them.

The second rung demands more of the branching vertex and pays for it at
the leaf. Branch only on a vertex with *three* distinct uncovered
neighbours: the second child then costs at least three units of budget,
the leaf count obeys $T(k)\le T(k-1)+T(k-3)$, and its base is the real
root $\beta\approx1.4656$ of $x^3=x^2+1$. But the leaf is now a graph in
which every unmarked vertex has at most two uncovered neighbours — a
disjoint union of paths and cycles — and there counting edges is no
longer the answer: a path or a cycle with $e$ edges is covered by
$\lceil e/2\rceil$ vertices and by no fewer. So the leaf is an exact
solver, one breadth-first sweep summing $\lceil e/2\rceil$ over the
connected components of what is left, and the theorem that this sum is
the cover number of a graph of maximum degree two is the one genuinely
new piece of mathematics under the second statement. Both bounds are
stated through a recurrence — mathlib's `Nat.fib`, and the surface's own
`branchCount` — and not through a power of a real number, so that no
rounding enters: the search trees really do have $\mathrm{fib}(k+2)$ and
$\mathrm{branchCount}(k)$ leaves, and those counts are what the proofs
produce. The second is at most the first at every $k$, and strictly
smaller from $k=3$ on: $1,2,3,4,6,9,13,19,28$ against
$1,2,3,5,8,13,21,34,55$.

The concept surface is two review units and one definition. mathlib's
vertex cover number is the answer in both statements, mathlib's
`Nat.fib` is the first bound, the compressed sparse row encoding and the
instance format that appends the parameter to it are the earlier
submission's, and the machine together with the predicate "this program
computes this function within this bound at this word length" are the
word RAM's. The one thing that had to be defined is `branchCount`:
mathlib names the sequence nowhere, and rounding it up to a clean power
would have been a weaker theorem wearing a smaller-looking bound. A
reviewer is asked about two sentences and one four-line recurrence,
and nothing else. The formalization notes say what the statements decide
rather than prove: why the fitting condition is an admissibility
condition on inputs rather than a hypothesis — a graph with an edge has
encodings of every length, so as a hypothesis it would be empty — why
that condition is deliberately not coupled to the running time, since
asking $\mathrm{fib}(k+2)$ to fit into a word would exclude exactly the
instances the theorems are about, and why `branchCount`'s three initial
values are the exact leaf counts at budgets $0$, $1$ and $2$ rather than
a convention.

Both obligations are discharged in the same submission: statement and
proof ship together, unlike the $2^k$ statement, which joined the surface
before it had a proof. The apparatus is the earlier one, reused rather
than rebuilt — the structured while-language of *The Word RAM*, its
compiler and simulation theorem, and its loop rule taking an invariant
together with a cost potential — required as proved theorems that the
kernel checks like any others, so the axioms remain the three background
ones. The mathematics is done with the machine out of sight: the
residual graph at a node of the search, the lemmas disposing of a node
(at most $b$ residual edges admit a cover within $b$; a residual matching
of more than $b$ edges admits none; branching on a vertex is exhaustive;
and, for the second rung, that the component sum $\sum\lceil e_C/2\rceil$
decides coverability exactly when every residual degree is at most two),
and a pure configuration — a stack of frames, each carrying the budget it
was pushed at, since the two children of a branch no longer cost the
same, and each recording the height of a trail of marked vertices, since
a frame on its second branch marks a whole neighbourhood and cannot undo
it by name. Correctness is one invariant splitting the answer between the
marking committed to and the alternatives the frames still owe. The cost
is one potential — $4\,\mathrm{fib}(b+2)-3$ on the first rung,
$4\,\mathrm{branchCount}(b)-3$ on the second, plus slack per frame —
which every one of the eight transitions strictly decreases, so the whole
tree is paid for by a single application of the loop rule rather than by
a recursion, and the leaf count enters exactly once, as the potential of
the initial configuration.

One subtlety is specific to the improved bounds and cost a full rewrite
of the branching test: the encoding is allowed to name a neighbour of a
vertex several times, so the number of unmarked slots in a block is not
the residual degree, and a test that counts slots rather than comparing
*targets* would branch where the recurrence does not hold — on $k$
disjoint edges with every slot doubled it would search a $2^k$ tree on an
instance the correct program answers without a single branch. The
smallest witness, a nine-number word encoding one edge, is kept in the
proof package as a machine-checked standing warning, and both drivers
compare targets. The constants that come out are 90300 for the Fibonacci
program ($43$ machine steps per statement of the compiled program, times
$2100$ statements per $\mathrm{fib}(k+2)$ per input letter) and 318500
for the branching program ($49\times 6500$; ten arrays rather than eight,
so one index computation is twelve instructions). Against the $2^k$
driver's 33300 that is a ladder in both directions: each rung buys a
smaller base by paying a larger constant, and nothing at any level was
fought for. On small shared instances the cheaper constant wins — the
$2^k$ driver beats both on a triangle — and where the base bites the
order reverses: on the seven-cycle at $k=3$ the Fibonacci program takes
17937 steps and the branching program 7016, and on five disjoint edges
with every slot doubled the $2^k$ driver takes 52554 steps where the
Fibonacci one takes 4572. The claim is about the exponent, not about the
constant.
