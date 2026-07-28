# The map of this directory

The honesty ledger of this submission is written where the archive
renders it, next to the object each item is about, and not here. This
file is for anyone reading the directory rather than the submission
page: where the two statements live, where their proofs live, and what is
borrowed from elsewhere.

## The statements

- `concepts/Lax15/VertexCover.lean` is the first review unit: one theorem
  concept, `exists_fibTime_program_vertexCover`, and no definitions. Its
  `# Formalization notes` carry the statement's items — the parameter
  dependence written into the bound rather than quantified away,
  `Nat.fib` in place of a power of a real number, the program and the
  constant standing ahead of the parameter *and* the word length, what
  the fitting condition has to cover, why it is a condition on the
  admissible inputs rather than a hypothesis, and why it is deliberately
  not coupled to the running time.
- `concepts/Lax15/VertexCoverBranch.lean` is the second: one theorem
  concept, `exists_branchTime_program_vertexCover`, with the same shape,
  the same admissible set and the same output, and the bound
  `c * branchCount k * (x.length + 1)`. Its notes carry the items above
  in their sharper form plus two of its own — why the three initial
  values of `branchCount` are the exact leaf counts at budgets 0, 1 and 2
  and not a convention, and that the admissible set is unchanged
  character for character even though the constant is larger.
- **`branchCount` lives in that second concept**, next to the statement
  that is the only thing it is for. It is the ladder's first
  self-defined object: mathlib has a name for the Fibonacci numbers and
  none for the leaf count of a `b ↦ (b−1, b−3)` split, so the recurrence
  had to go on the surface. It stays inside the theorem concept rather
  than becoming a definition-concept of its own because it is the
  claim-local object the statement is about — the same placement rule
  that keeps `ccLabels` inside Lax11's `ConnectedComponents`. Stating it
  by its recurrence rather than as `⌈β^k⌉` for the real root
  β ≈ 1.4656 of `x³ = x² + 1` is what keeps every rounding out of the
  claim.
- Everything else the statements mention is imported. The machine and the
  timed-computation predicate are `Lax13`'s, the compressed sparse row
  encoding and the instance format that appends the parameter are
  `Lax11`'s, and the vertex cover number and `Nat.fib` are mathlib's. In
  particular the admissible set is `Lax11`'s, character for character, so
  all three bounds compare directly; the notes on every statement say so.

## The Fibonacci rung, layer by layer

Six modules, bottom-up. Each carries a module docstring saying what it is
for; the items that belong to the *proof* rather than to the statement
are in the conclusion annotation of `proofs/Lax15Proofs/Main.lean`, under
`# Where the word length is paid for`, `# What the program is allowed to
help itself to` and `# Attribution`.

- `Residual.lean` — the graph side of the pure model. The residual
  neighbourhood, residual degree and residual edge set at a marking, the
  three lemmas that dispose of a node of the search (early exit, matching
  lower bound, vertex branch), and the transport of those quantities to
  the compressed sparse row encoding, where the machine meets them as
  counts over slots.
- `Repeats.lean` — one nine-number word, kept as a standing warning: an
  encoding may name a neighbour twice, so a block with two unmarked slots
  need not be a vertex with two residual neighbours. This is why the
  branch test compares targets and the residual edge count is capped at
  one per block; the file is the machine-checked refutation of the naive
  variant. It governs both rungs.
- `Config.lean` — the configuration side of the pure model. Frames,
  trail, marking, frame health, the invariant `J`, the potential, and the
  eight transitions, each proved to preserve `J` and to drop the
  potential.
- `Program.lean` — the driver `vcfCom` as an IMP+ program, its
  well-formedness, and the smoke tests: eighteen instances `#eval`ed
  through the compiled machine and `#guard`ed against the expected
  answers, the repeat encodings and the doubled-slot matching family
  among them.
- `Phases.lean` — `Rep`, which says what the arrays and scalars hold when
  the pure configuration is `C`, and the three inner loops run against
  it: the descend scan, the flip's row scan, the pop's unwind loop.
- `Loop.lean` — one turn of the outer loop, run: the dispatch on the mode
  and, under it, the eight transitions, each case reassembling `Rep`,
  invoking exactly one `step_*` lemma, and paying a loose numeral times
  the length of the input.
- `Main.lean` — the loop as one application of the loop rule, the read
  phase and the `write`, the compiler, and the theorem, with an identity
  check against the concept's proposition. Achieved constant 90300.

## The branching rung, layer by layer

Seven modules, namespace `Lax15Proofs.VC3`, on top of the rung above:
the read phase, the push, flip and pop blocks and their run lemmas are
imported from it by name and none of its files was touched. The
conclusion annotation is in `proofs/Lax15Proofs/Main3.lean`.

- `Solver.lean` — the one genuinely new theorem: for a marking under
  which every unmarked vertex has residual degree at most two, a cover
  within budget `b` exists exactly when `∑ ⌈e_C/2⌉ ≤ b`, the sum over the
  connected components of the residual graph. The lower bound is a
  counting argument per component; the upper bound is an induction that
  isolates the neighbour of a degree-one vertex when there is one and any
  endpoint of an edge otherwise, the second case resting on the handshake
  lemma per component. Also the scan transport at threshold three.
- `Config3.lean` — the branch recurrence as `branchCount` (the concept's
  four equations, proofs-side), the potential `4·branchCount b − 3`, the
  invariant `J3 = J ∧ Sharp` — `Sharp` being the extra clause that every
  pushed frame branched at residual degree three or more, which is what
  pays for the flip — and the eight transition wrappers, seven of whose
  `J`-halves are projected straight from the rung above.
- `Program3.lean` — the driver `vcf3Com`: the same read phase and the
  same backtrack blocks, a descend scan that dedups targets into
  `seen/t1/t2` and reports three distinct ones, and the solver block. Ten
  arrays, thirty scalars. Smoke: twenty-eight `#guard`ed runs, every
  expected answer hand-derived in a comment first, including the odd
  cycle, two disjoint cycles and the bull that exercise the leaf solver.
- `Phases3.lean` — the inner loops of the new blocks, run: the shared
  dedup step, `descendScan3_run` (the verdict at threshold three), the
  queue structure and its push, the row scan of one dequeued vertex with
  the toggle's closed form, and the clearing pass.
- `Sweep3.lean` — the solver assembled: the pure identity summing
  up-degrees over a component, the queue-reading potential, the drain,
  the root sweep that meets every component exactly once, and
  `solve_run`, which reports `s = compCost` and the verdict.
- `Loop3.lean` — one turn of the outer loop, as `Loop.lean` but with the
  solver at the leaf and `SideInv` carrying the three interface facts
  (`"n"`, and the extents of `vis` and `q`) that `Rep` is silent about.
- `Main3.lean` — the loop rule, the assembly on the reused read phase,
  the theorem, and the identity check. Achieved constant 318500.

## The one-line story of the potential

The pending work of a configuration is `4·g(b) − 3` for the subtree still
to be searched at remaining budget `b`, plus slack for each frame whose
second branch is still owed, where `g` is `Nat.fib (· + 2)` on the first
rung and `branchCount` on the second; `fPot (b+2) = fPot (b+1) + fPot b
+ 3` and `fPot3 (b+3) = fPot3 (b+2) + fPot3 b + 3` hold exactly, which is
what pays for a push, and every transition drops the total by at least
one — so the entire search tree costs one application of the loop rule,
and the leaf count enters exactly once, as the potential of the initial
configuration.

## What is borrowed

- From `Lax13Proofs` (*The Word RAM*): the IMP+ language and its cost
  semantics, the compiler and the simulation theorem, and the reasoning
  layer — one rule per construct plus the loop rule taking an invariant
  together with a cost potential. No machine-level code appears in this
  package.
- From `Lax11Proofs` (*Algorithmic Experiments on a Random Access
  Machine*): the search predicate `Ok`, its bridge to mathlib's vertex
  cover number, and the read phase of the components driver, which reads
  the encoding into the offset and target arrays. `Residual.lean` adds a
  layer on top of `VCSpec` and restates none of it.
- Both are proof-package dependencies pinned at the exact commits of
  those submissions' records. They are proved theorems, checked by the
  kernel like any others, and they add nothing to the axiom set, which is
  the three background axioms alone.
