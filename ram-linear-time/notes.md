# Formalization notes — where they live

The honesty ledger of this submission is written where the archive
renders it, next to the object each item is about, and not here. This
file is a map for anyone reading the directory rather than the
submission page.

- **The theorem's own items** — the cliquewidth pivot and the
  unformalized conversion from treewidth; the expression as a
  certificate, with the whole word read but only two of its arrays
  used; the noncomputable type table and the existential-over-programs
  shape of the statement; the strength-reduced table indexing, which
  keeps multiplication out of the compiled program altogether; the
  `#eval` stand-in table and what it does and does not establish; the
  constant as a tower that is never estimated; the three things the
  word length has to hold, the size of the table among them;
  `TreeDecomp.lean` kept as theory that no longer feeds the theorem;
  and the one device on the trust surface that is not textbook — are in
  the conclusion annotation of
  `proofs/Lax11Proofs/CourcelleMain.lean`, under
  `# Where the constant comes from`, `# Where the word length is paid
  for` and `# Formalization notes`.
- **The definitions' items** are in the `# Formalization notes` section
  of each concept file: the MSO₁ scope and the de Bruijn family in
  `concepts/Lax11/Mso.lean`; global vertex names, label classes as
  sets, and the totality of the operation decoding in
  `concepts/Lax11/CliqueExpr.lean`; the certificate clause, the unread
  vertex-name array and the children-before-parents numbering in
  `concepts/Lax11/InstanceEncoding.lean`. The statement's own items —
  the expression as input rather than something the program computes,
  the order of the quantifiers, and why the fitting condition
  quantifies over the entries of the word rather than over its length
  alone — are in the `# Formalization notes` of
  `concepts/Lax11/Courcelle.lean`.
- **The connected-components theorem's** items are in the conclusion
  annotation of `proofs/Lax11Proofs/CCMain.lean`, and the graph
  encoding carries its own notes in `concepts/Lax11/`. The machine
  itself and the timed-computation predicate are not this submission's
  concepts at all: they are the word RAM of `Lax13`, and their notes
  are there.
- **The vertex cover theorem's** items are in two places. The
  statement's — the parameter dependence written into the bound rather
  than quantified away, the program and constant uniform in the
  parameter, the parameter as a single entry after the self-delimiting
  graph block, and the decision problem as the honest scope — are in
  the `# Formalization notes` of `concepts/Lax11/VertexCover.lean`.
  The proof's — the budget carried as a scalar rather than a field of
  the frames, the mark array left uninitialized because fresh memory
  is zero, and the plain base 2 of a search tree that applies no
  reduction rules — are in the conclusion annotation of
  `proofs/Lax11Proofs/VCMain.lean`, under `# What the program is
  allowed to help itself to` and `# Attribution`.
