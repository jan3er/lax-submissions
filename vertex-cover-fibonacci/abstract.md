This submission states one theorem: vertex cover is decided on the word
RAM within $c\,\mathrm{fib}(k+2)\,(|x|+1)$ steps. There are one program
and one constant $c$ such that, at every word length $w$, given any
graph in compressed sparse row form followed by the single entry $k$ as
a word $x$ for which $c(|x|+k+1)$ is at most $2^w$, the machine halts
within that many steps having written $1$ if the graph has a vertex
cover of at most $k$ vertices and $0$ if it does not. The machine, the
notion of computing a function within a time bound, and the input
format are not this submission's: the first two are the concepts of
*The Word RAM* and the third is the instance encoding of *Algorithmic
Experiments on a Random Access Machine*, both of which this submission
requires, so that the statement below and that submission's $c\,2^k$
statement are claims about literally the same inputs.

What changes is the base of the exponential. The textbook bounded
search tree branches on an edge — one of its two endpoints is in every
cover — and pays a factor of two per unit of budget. Branching on a
vertex of residual degree at least two pays less: either the vertex is
in the cover, at one unit, or all of its at least two remaining
neighbours are, at two or more, so the search tree obeys
$T(k) \le T(k-1)+T(k-2)$ and has $\mathrm{fib}(k+2)$ leaves. The base
drops from $2$ to the golden ratio $\varphi \approx 1.618$. When no
vertex has two uncovered edges on it the branching rule does not apply
and none is needed: the uncovered edges then form a matching, and the
answer is whether there are at most $k$ of them. The bound is stated
through mathlib's `Nat.fib` rather than through a power of a real
number, so that no rounding enters the statement and the surface adds
no definition of its own.

The proof is being written on the same kit as the $2^k$ result: the
structured while-language of *The Word RAM*, its compiler and
simulation theorem, and its loop rule taking an invariant together with
a cost potential, so that the whole search tree is paid for by one
application of that rule rather than by a recursion. The pure model —
the residual graph, the search configuration, the invariant and the
potential $4\,\mathrm{fib}(b+2)-3$ — is developed without the machine
in sight, and the earlier submission's search predicate and its bridge
to mathlib's vertex cover number are imported rather than restated.

*Status: the statement is on the surface and the proof is in progress;
this abstract will be rewritten when the development is complete, with
the achieved constant spelled out.*
