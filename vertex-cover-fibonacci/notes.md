# The map of this directory

The honesty ledger of this submission is written where the archive
renders it, next to the object each item is about, and not here. This
file is for anyone reading the directory rather than the submission
page: where the one statement lives, where its proof lives, and what is
borrowed from elsewhere.

## The statement

- `concepts/Lax15/VertexCover.lean` is the whole concept surface: one
  theorem concept, `exists_fibTime_program_vertexCover`, and no
  definitions. Its `# Formalization notes` carry the statement's items —
  the parameter dependence written into the bound rather than quantified
  away, `Nat.fib` in place of a power of a real number, the program and
  the constant standing ahead of the parameter *and* the word length,
  what the fitting condition has to cover, why it is a condition on the
  admissible inputs rather than a hypothesis, and why it is deliberately
  not coupled to the running time.
- Everything the statement mentions is imported. The machine and the
  timed-computation predicate are `Lax13`'s, the compressed sparse row
  encoding and the instance format that appends the parameter are
  `Lax11`'s, and the vertex cover number and `Nat.fib` are mathlib's. In
  particular the admissible set is `Lax11`'s, character for character, so
  the two bounds compare directly; the notes on both statements say so.

## The proof, layer by layer

The proof package is six modules, bottom-up. Each carries a module
docstring saying what it is for; the items that belong to the *proof*
rather than to the statement are in the conclusion annotation of
`proofs/Lax15Proofs/Main.lean`, under `# Where the word length is paid
for`, `# What the program is allowed to help itself to` and
`# Attribution`.

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
  variant.
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
  check against the concept's proposition.

## The one-line story of the potential

The pending work of a configuration is `4·fib(b+2) − 3` for the subtree
still to be searched at remaining budget `b`, plus slack for each frame
whose second branch is still owed; `fPot (b+2) = fPot (b+1) + fPot b + 3`
holds exactly, which is what pays for a push, and every transition drops
the total by at least one — so the entire search tree costs one
application of the loop rule, and `fib (k+2)` enters exactly once, as the
potential of the initial configuration.

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
