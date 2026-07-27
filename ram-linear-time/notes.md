# Formalization notes — where they live

The honesty ledger of this submission is written where the archive
renders it, next to the object each item is about, and not here. This
file is a map for anyone reading the directory rather than the
submission page.

- **The theorem's own items** — the cliquewidth pivot and the
  unformalized conversion from treewidth; the expression as a
  certificate, with the whole word read but only two of its arrays
  used; the noncomputable type table and the existential-over-programs
  shape of the statement; the machine's add-and-subtract-only
  instruction set and the strength-reduced table indexing; the `#eval`
  stand-in table and what it does and does not establish; the constant
  as a tower that is never estimated; `TreeDecomp.lean` kept as theory
  that no longer feeds the theorem; and the one device on the trust
  surface that is not textbook — are in the conclusion annotation of
  `proofs/Lax11Proofs/CourcelleMain.lean`, under
  `# Where the constant comes from` and `# Formalization notes`.
- **The definitions' items** are in the `# Formalization notes` section
  of each concept file: the MSO₁ scope and the de Bruijn family in
  `concepts/Lax11/Mso.lean`; global vertex names, label classes as
  sets, and the totality of the operation decoding in
  `concepts/Lax11/CliqueExpr.lean`; the expression as input, the
  certificate clause, the unread vertex-name array and the
  children-before-parents numbering in `concepts/Lax11/Courcelle.lean`.
- **The connected-components theorem's** items are in the conclusion
  annotation of `proofs/Lax11Proofs/CCMain.lean`, and the machine,
  the cost model and the graph encoding carry their own notes in
  `concepts/Lax11/`.
