# Formalization notes

These notes are the honesty ledger of the submission. The concept files
carry their own `# Formalization notes` sections, and those are the ones
a reviewer of a single definition needs; what follows is the part that
belongs to no single concept — the scope the statement claims, the
places where a standard textbook proof and this development part
company, and the things the reader is entitled to know were decided
rather than proved. Each is argued rather than listed, because a
one-line disclaimer is exactly the form in which an unexamined claim
survives review.

## The logic is MSO₁, and MSO₂ is not deferred by accident

The formulas of `Lax11.Mso` quantify over vertices and over sets of
vertices, and their only atoms are adjacency, equality and membership.
Quantification over edges and over sets of edges — monadic second-order
logic of the second kind, MSO₂ — is absent. This is not a step on the
way to a fuller version that was left unfinished. MSO₂ and MSO₁ are
matched to different width measures: MSO₂ model checking is tractable on
classes of bounded treewidth and is *not* tractable on classes of
bounded cliquewidth unless the standard complexity assumptions fail, so
a submission that proved the MSO₁ statement for cliquewidth and then
claimed MSO₂ "by the same argument" would be claiming something false.
The honest description of what is here is the Courcelle–Makowsky–Rotics
theorem, and the other canonical pairing — MSO₂ with treewidth — is a
separate theorem with a separate encoding (the incidence graph, or edge
set variables in the type algebra) and is deferred as one unit, logic
and width measure together.

## The syntax is a well-scoped de Bruijn family

`MSO r s` is the type of formulas with `r` free vertex variables and `s`
free set variables; a quantifier maps `MSO (r+1) s` to `MSO r s`, and a
sentence is an element of `MSO 0 0`. Variables are therefore positions,
not names, and being closed is a property of the type rather than a
predicate that has to be stated and checked.

The alternative — variables as names, or as bare natural numbers, with a
separate well-formedness predicate — is what a paper writes, and it is
worse *here* for a specific reason. Satisfaction is on the trust surface:
it is a definition in the concept package, and the entire claim of the
submission is that this definition means what the phrase "the sentence
holds in the graph" means. With names, satisfaction of a quantified
formula is stated by substituting a value for a variable, and
substitution must avoid capture; capture-avoiding substitution is
fifteen to forty lines of definition with a renaming pass inside it, and
every one of those lines would sit on the trust surface, where nothing
proves it correct and a reviewer must read it. With positions,
satisfaction extends an environment by one entry and recurses, and there
is no substitution in the development at all — not in the concept
package, not in the proof package. What the reader pays for this is that
the atoms of a formula name positions: `MSO.adj 0 1` is "the two
outermost bound vertex variables are adjacent". That is a real cost and
it is the subject of the last note below.

## The type table is noncomputable, and that is the theorem's shape

The fold that the machine runs is driven by a table: a finite value
alphabet, an initial value per operation symbol, and a binary
combination. For this development the values are the quantifier-rank-`q`
types of `k`-labelled regions, and the table is extracted from the
composition congruences by `Fintype` together with the axiom of choice —
for each pair of types the entry is *a* type realized by some gluing of
two regions with those types, and the congruence lemmas say that the
choice does not matter. Nothing in the development computes this table,
and nothing could: the statement being proved is an existential over
programs, and the truth of an MSO sentence in an arbitrary graph is not
something the meta level decides on the way to constructing one. A
reader who wants the machine to *print* the table is asking for a
different theorem — an effective bound on the type space, which is
exactly the tower this development declines to estimate.

What the noncomputability does not touch is the program. `table q k` is
a noncomputable value of a perfectly ordinary structure type, and the
program generator consumes it as data: the same generator applied to a
computable table produces a program that runs, which is how the machine
runs are checked (below). The table's *content* is carried by proof; the
program text around it is carried by evaluation.

## The width measure is cliquewidth, and the conversion from treewidth is not formalized

The development originally aimed at treewidth, and the pure set theory
of tree decompositions was built before the aim changed. The theorem as
it stands is the Courcelle–Makowsky–Rotics form: MSO₁ model checking in
linear time on graphs presented with a `k`-expression. Bounded treewidth
implies bounded cliquewidth, so the class of graphs covered here
contains every class of bounded treewidth; but obtaining the treewidth
form of the statement from this one requires converting a tree
decomposition of width `w` into a `k`-expression with `k` bounded in
terms of `w`, and that conversion is not formalized. Anyone who wants
the treewidth statement should treat it as unproved here.

The same applies one level up, to the input. The theorem takes the
`k`-expression as part of its input; it does not compute one. Deciding
cliquewidth is NP-hard, approximating it is the theorem of Oum and
Seymour, and neither is in this submission. This is precisely the status
that Bodlaender's linear-time treewidth algorithm would have had under
the earlier plan: a separate theorem, with its own proof, which composes
with this one to give an algorithm that takes only the graph. Until it
exists, the honest reading of the statement is "given a graph together
with a `k`-expression for it", which is what the concept says.

## The expression is a certificate, and the program reads only two of its arrays

The input word has two blocks: the graph in compressed sparse row form,
then the expression as four arrays — node count, parent, operation code,
vertex name. The graph block is what makes `Sat G φ` refer to a graph;
the expression block is a certificate that determines the same graph
completely, and the encoding predicate requires that it evaluates to
exactly `G`, so the existential over expressions in the encoding ranges
over at most one expression.

The program reads the whole word, because it must get past the graph
block to reach the expression block and because a random access machine
reads its input tape in order; but it *uses* only the parent array and
the operation-code array. The graph block and the vertex-name array go
into arrays that no later expression of the program mentions. This is
not laziness dressed up: the decision procedure genuinely needs only the
tree shape and the operation at each node, because the type of a
subexpression is a function of the types of its children and its own
operation, and nothing else. The vertex names are in the input because
without them the block would be the shape of a `k`-expression rather
than one, and a reviewer could not check the certificate against the
graph block. Reading past them costs a constant per entry and the bound
is linear in the number of entries, so the two unread blocks cost the
statement nothing.

## Children are numbered before their parents, and this costs no generality

The expression block requires that the parent of node `i` is a node with
a larger number, so the root is the last node. This is what makes the
fold a single left-to-right sweep with no recursion, no stack and no
second pass, and it is where the linear bound comes from.

It restricts the *encoding*, not the class of graphs. Every rooted tree
admits such a numbering — any postorder is one — and a numbering can be
produced from an arbitrary one in linear time by a sort that this
submission does not contain and does not need to: the statement
quantifies over words that encode the instance, and the instance is
presented in this format by definition. A submission that accepted
arbitrary parent arrays would be proving a theorem about a different
input format, at the price of a renumbering pass inside the program,
and would say exactly the same thing about graphs.

## The machine has addition and subtraction only

The machine of `Lax11.Ram` has the instruction set of Aho, Hopcroft and
Ullman without multiplication and division. Under a unit-cost measure
this matters: a machine that multiplies in one step can do things in
linear time that a real computer cannot, and unit-cost multiplication is
the standard way a linear-time claim on a random access machine becomes
an artifact of the model.

The fold indexes a two-dimensional table, which is where a
multiplication would naturally appear: the entry for values `a` and `b`
sits at position `a·V + b`. Instead the row bases `a·V` are themselves
materialized as an array `row`, once, in the prologue, and a table
lookup is `tab[row[a] + b]` — two array reads and an addition. The
prologue that fills `row` is a sequence of stores whose length is the
table's size, which is a constant fixed before the input is read. So no
multiplication occurs anywhere in the compiled program, and the
linear-time claim survives a strict word-RAM reading of the model rather
than depending on a generous one.

## The machine-versus-model check runs a stand-in table

House discipline in this submission is that every program is run — by
`#eval` inside the build, against the pure model it is proved to
implement — before anything about it is proved. The Courcelle driver is
run that way, but it cannot be run with the type table, which is
noncomputable by construction. The check therefore instantiates the
*generic* driver with `edgeTable`: a hand-written table over the same
operation alphabet, decoded by the same `Op.decode`, whose values are
three bits — label class 0 is nonempty, label class 1 is nonempty, there
is an edge — together with the partial states the sequential fold needs.
That is a genuine cliquewidth dynamic program, and the two sentences it
decides on the path 0—1—2 are "some two vertices are adjacent" and its
negation; the machine writes `1` and `0` respectively, and the
`#guard`s check that against the pure fold.

What this establishes and what it does not is worth being exact about.
Every line of program text is exercised: the same reads, the same
prologue, the same seed and push loops, the same accept-bit epilogue,
the same decoder. What is not exercised is the content of the real
table, and that is the part the proof carries — `val_eq_typeOf` says the
fold's value at a node is the number of that node's type, for the real
table, by structural induction on the expression. The division of labour
is deliberate: plumbing is machine-checked, mathematics is proof-carried,
and neither is asked to vouch for the other.

## The constant is a tower, and is never estimated

The bound proved is `46 · (100 + driverCost (table q k))` machine steps
per entry of the input word. The `46` is the compiler's layout constant
— nine arrays, so one array access lowers to eleven instructions — and
the `100` is the driver's own per-entry cost with every loop bounded
loosely. The remaining term is the price of materializing the tables,
three units per entry, and it is where the tower lives: the type table
has one row and one column per quantifier-rank-`q` type of a
`k`-labelled region, a quantity that grows faster than any tower of
exponentials in the rank of the sentence.

This is not a defect of the proof; it is the theorem. The quantifiers
run sentence and width first, then program and constant, then the graph,
so the constant is permitted to depend on the sentence and the width in
any way whatsoever, and every known proof of Courcelle's theorem makes
it non-elementary. What the submission does claim is that the dependence
is on the sentence and the width *alone* — the table is materialized
before the input is read, and the per-node work in the fold is a fixed
number of array accesses independent of the alphabet size. What it does
not claim is any bound on the constant, and no bound is computed
anywhere. A reader looking for one will not find it, and should not read
the absence as an oversight.

## `TreeDecomp.lean` is kept, as theory that no longer feeds the theorem

The pivot to cliquewidth stranded 574 lines of tree-decomposition set
theory: descendants as parent-map iteration, validity and width, the
tree order, the highest node containing a vertex, subtrees as unions of
bags, the separation lemma and the edge-placement lemmas. Nothing in the
proof of the theorem imports it. It is kept anyway, and the argument is
that it is not scaffolding but a self-contained piece of mathematics
that happens to be stated in the shape this machine wants: nodes are
numbers, the parent map is the same `ℕ → ℕ` the fold sweeps, and every
lemma is proved and green. Deleting it would cost a future MSO₂ or
treewidth submission the whole of its combinatorial layer for no gain
beyond a smaller build, and keeping it costs one file that imports only
mathlib and is imported by nothing. It is flagged here rather than
silently retained so that no reviewer spends time looking for the place
where it is used.

## The one thing on the trust surface that is not textbook

Everything the reader has to check by eye — the machine, what it means
to compute within a time bound, the graph encoding, the syntax and
satisfaction of the logic, `k`-expressions and their evaluation, the
input format, and the statement itself — is written to be the object a
paper would write, with one exception, and it should be named plainly.
The exception is that variables in formulas are de Bruijn positions.
`Sat` is otherwise the usual clause-by-clause recursion, the graph
encoding is the dumb one, the expression evaluation is the standard
structural recursion, and the theorem is the standard quantifier order;
but a reader checking `Lax11.Mso` against a textbook must translate
between `∃x. ∃y. adj(x,y)` and `MSO.exV (MSO.exV (MSO.adj 0 1))`, and
must hold in mind that a quantifier binds at the *last* position, so
that the outermost variable is `0` and no index is ever shifted. Every
other deviation in this development is inside the proof package, where
the kernel is the reviewer. This one is not, and it is the price paid
for keeping substitution off the surface entirely.
