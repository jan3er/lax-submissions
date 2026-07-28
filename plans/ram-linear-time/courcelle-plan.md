# Courcelle plan (rev 6 — closed; all steps done, 2026-07-28)

Rev 6 (wrap-up, session 17): **the plan is complete.** Every step is
done and the theorem
`Lax11.Courcelle.exists_linearTime_program_modelChecking` is proved and
discharged at the concept surface. Nothing below is rewritten — the
step list is marked with ✅ and a pointer to the `NIGHTLOG.md` block
that executed it, and a "Final state" section is appended at the end.
The rev-5 text that follows is the plan as it stood while it was being
executed, and it is left as the record of what was decided when.

Rev 5 (Jan, in session): **the width parameter is cliquewidth, not
treewidth** — the theorem becomes Courcelle–Makowsky–Rotics (MSO₁
model checking is linear-time on graphs given with a k-expression).
Jan's observation, confirmed by the orchestrator against the code as
built: the entire shared-boundary FV machinery — marks-as-bags,
overlap patterns, canonical bag ordering, forgets in the fold, and the
C7a four-phase label pass — existed to serve gluing along a shared
boundary, and disjoint union eliminates all of it. Decisions C11–C14
below record the pivot; C4, C6, C7/C7a are superseded. C1–C3, C5,
C8–C10 stand. Rev 2's frame (everything in Lax11, single submission)
is unchanged.

Rev history: rev 2 single-submission; rev 3 added C7a (now moot); rev
4 refined C2 (well-scoped `MSO r s`, axiom over `MSO 0 0`) and C3.3
(cross-ambient congruence, table by choice) — both refinements stand
and are load-bearing below.

Goal: **Courcelle's theorem (Courcelle–Makowsky–Rotics form) on the
Lax11 RAM** — for every MSO₁ sentence and every width bound k, model
checking on graphs given with a k-expression is linear time. Lax11
supplies the machine, the compiler, the reasoning kit, and — after the
pivot — the *already verified* generic tree-fold program.

## The statement (C0 target, rev 5 form)

```lean
/-- Courcelle's theorem (Courcelle–Makowsky–Rotics): MSO model checking
is linear-time on the RAM, for graphs presented with a k-expression
(cliquewidth ≤ k). -/
axiom courcelle :
    ∀ (φ : MSO 0 0) (k : ℕ),
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ComputesInTime p {x | EncodesInstance x n G k}
        (fun _ => if Sat G φ then [1] else [0])
        (fun x => c * (x.length + 1))
```

- Quantifier order unchanged: `p` and `c` after `φ` and `k`, before
  the graph — non-uniform in sentence and width, constant may be a
  tower, never estimated.
- `EncodesInstance x n G k`: `x` encodes `G` (CSR, `EncodesGraph`
  reused) **followed by a k-expression that evaluates to `G`** (C14).
  The expression is *input*, exactly as the decomposition was:
  computing a k-expression (cliquewidth approximation à la
  Oum–Seymour) is a separate future submission — ledger item, same
  status Bodlaender had.
- Output `[1]`/`[0]` on the output tape (C9).
- Honesty item the pivot adds: MSO₁ + cliquewidth *covers* MSO₁ +
  treewidth (bounded tw ⟹ bounded cw), but deriving the treewidth
  form needs a decomposition→expression conversion we do not
  formalize. The ledger says so plainly. In exchange the pairing is
  now the canonical one — MSO₁ is *the* logic of cliquewidth, and the
  C1 scope decision and the width parameter finally agree; MSO₂ +
  treewidth is the other canonical pair and is deferred as one unit.

## Decision record

- **C1 (scope)** MSO₁ — unchanged, and strengthened by the pivot:
  MSO₁ is exactly the logic preserved by cliquewidth operations. MSO₂
  remains a later submission (incidence encoding, treewidth pairing).
- **C2 (logic representation; rev 4)** Unchanged. Well-scoped de
  Bruijn family `MSO r s`, atoms `adj`/`eq`/`mem`, connectives
  `not`/`and`, quantifiers `exV`/`exS`; `Sat` a ~15-line recursion
  over two environments; axiom over `MSO 0 0`; no substitution
  machinery. As built in `Mso.lean` (M4/M5) — the surface copy at the
  freeze remains verbatim.
- **C3 (proof route)** Unchanged and already executed: the abstract
  type algebra `T q r s` / `typ` (M4), adequacy (M5), and the
  cross-ambient congruence `typ_union_congr` (M6, general q, gate
  green). The pivot does not touch this engine; it changes which
  *instances* of it downstream consumes. The mark lemmas (M5) and the
  concatenated form `typ_append_congr` become internal artifacts —
  they underpin the proofs as built and stay, but no new work
  consumes them.
- **C4 (superseded by C12/C13)** No bag gluing, no sequential
  glue-and-forget over children. The composition structure of the
  proof is now the k-expression's own tree: binary disjoint union,
  unary edge-addition and relabel.
- **C5 (noncomputable table)** Unchanged, and cheaper: the table is
  extracted by `Fintype` + choice from the C13 congruences exactly as
  before; there are now four small tables (one per op family) instead
  of one glue table indexed by overlap patterns.
- **C6 (superseded by C14)** — the instance encoding now carries a
  k-expression tree, in M1's `EncodesTree` format.
- **C7/C7a (superseded, deleted with relief)** No label pass, no
  top-node computation, no edge discovery, no top-down propagation,
  no overlap-pattern scanning. The per-node symbol of the fold is the
  op code, present verbatim in the input. This deletes the single
  hairiest remaining program component of rev 4.
- **C8 (single submission)** Unchanged — everything in Lax11,
  existing concept files frozen, Courcelle surface added at the
  freeze step.
- **C9** Unchanged — `[1]`/`[0]` by membership of the root value in
  the accepting set.
- **C10** Moot as before (same package, direct imports).

- **C11 (rev 5: the pivot itself)** Width parameter = cliquewidth;
  theorem = Courcelle–Makowsky–Rotics. What it buys, measured against
  the code as built (session-10/11 logs):
  (a) the outer statements have **no marks at all** — `r = 0`
  everywhere; labels are set parameters (C12), so the mark pool,
  overlap patterns and canonical bag order never appear;
  (b) binary composition is `typ_union_congr` **at the empty pool**
  (`c = 0`): empty overlap, no-cross-edges = disjointness — already
  proved, eleven hypotheses collapse to two;
  (c) the fold program is the *already verified* Q3 schema with no
  label pass (C14) — Q6 shrinks from the biggest remaining milestone
  to an instantiation;
  (d) no forgets in the induction — the expression tree is the proof
  tree.
  What it costs: `TreeDecomp.lean` (M7, 574 lines) idles — it stays
  in the build untouched, disposition (keep as bonus theory for the
  future treewidth submission, or prune) is a wrap-up decision; the
  C0 statement changes as above; three new unary-op congruences must
  be proved (C13), each strictly easier than the proved
  `typ_union_congr`.
- **C12 (k-expressions, the object)** One inductive type `Expr n k`:
  `leaf (v : Fin n) (ℓ : Fin k)` — vertex `v` created with label `ℓ`;
  `union e₁ e₂` (⊕); `addEdges (i j : Fin k) e` (η, `i ≠ j`);
  `relabel (i j : Fin k) e` (ρ, i→j). **Vertices are globally named
  by leaves** — the ambient-subset trick survives the pivot: the
  vertex set of a node is a `Set (Fin n)` (its leaves' ids), no
  quotients, no isomorphisms. What *does* vary along the tree is the
  graph (η adds edges), so statements are cross-graph — which is
  already the house style (`typ_union_congr` is cross-ambient).
  Evaluator by structural recursion: `eval e = (X, H, lab)` — vertex
  set, graph (edges within `X`), label classes `Fin k → Set (Fin n)`
  partitioning `X`. Validity: leaf ids distinct (this yields
  disjointness at every ⊕ node); at the root `X = univ` and `H = G`.
  **Labels are set parameters**: a k-labeled graph is an ambient
  subset plus a set assignment `Fin s = Fin k` — `typ q` with
  `r = 0, s = k`, the *existing* `T`/`typ` unchanged. `T q 0 k` is
  the type space; marks exist only inside the recursion.
- **C13 (the op congruences — the new FV inventory)** Four lemmas,
  all q-inductions with identity vertex sets (no re-indexing, no
  Glue), each bounded above in difficulty by the proved union
  congruence:
  1. *Disjoint union*: instance of `typ_union_congr` at `c = 0`.
     Already proved; write the instance and move on.
  2. *`typ_addEdges`* (η): cross-graph, same `X`, same sets; `G'`
     adjacency = `G` adjacency ∨ (endpoints in classes i,j resp.),
     restricted to distinct vertices. Rank 0: the new atomic diagram
     is a function of the old, because `mem` atoms of the label
     parameters are *in* the diagram. Moves: identical. This is the
     only new lemma with meat, and it is a same-set induction.
  3. *`typ_setRemap`*: new set assignment where each new parameter is
     the union of a chosen subfamily of the old ones
     (`f : Fin s' → Finset (Fin s)`, `A' j = ⋃ i ∈ f j, A i`).
     Rank 0: `mem` of a union of parameters is determined by the
     `mem` atoms. Instances: relabel ρ (merge two classes, empty one)
     and the root's forget-all (`s' = 0`), which is what lets
     adequacy consume the root type at `s = 0` for the sentence.
  4. *Singleton*: the typ of a one-vertex subset with a given
     label-membership pattern is independent of the ambient graph and
     of which vertex it is. Base of the main induction; small.
  Possibly needed as plumbing: `typ` depends only on edges within `X`
  (to move between a node's evaluated graph and its parent's). Check
  whether M4's development already gives it; if not it is the same
  cheap induction.
- **C14 (table, encoding, program)** Fold alphabet: op codes for
  fixed k — `1 + k + 2·k·(k−1)`-ish symbols, canonically numbered;
  this is the `lab` array of M1's `EncodesTree`, **present verbatim
  in the input**. Value alphabet: `T q 0 k` indices (Fintype
  enumeration) ⊎ op-tagged partial states — exactly the
  "carry the label inside the value" device TreeFold.lean was built
  with (its header says so); ⊕ needs one partial state ("left child
  absorbed"), unary ops apply on the second `step`. Table by
  `Fintype` + choice per C5, correct via the C13 congruences.
  Encoding: CSR graph block (unchanged), then the expression tree in
  `EncodesTree` format (parent array with children-before-parent,
  root `N−1`, op-code array), plus a per-node vertex-id array
  (meaningful at leaves — the explicit certificate; the *program
  never reads it*, only `EncodesInstance`'s validity clause does).
  Note for the ledger: the program reads only the expression block —
  the CSR block is consumed by the *statement* (it defines `G`), and
  the expression is a certificate that determines `G`. The remaining
  program work beyond Q3-as-built: the accept-bit epilogue (root
  value ∈ accepting set → write `[1]`/`[0]`, C9) and the
  `EncodesInstance` plumbing of the two blocks.

## Steps (rev 5; marked done at rev 6)

Done and standing: ✅ **Q3** (M1–M3, the generic fold — now consumed
verbatim; sessions 5–7, checkpoint "Q3 checkpoint: the schema as built"),
✅ **Q1** (M4–M6, type algebra + adequacy + the congruence — consumed
through its empty-pool instance; sessions 8–10, checkpoint "Q1a
checkpoint: the composition lemma as built"). Sunk: ✅ **Q2a** (M7,
session 11, TreeDecomp.lean — idled untouched, kept at wrap-up, see
Final state). Remaining, all now done:

4. ✅ **Q4 — the cliquewidth mathematics.** a: session 12 (M8), b:
   session 13 (M9), c: session 14 (M10), checkpoint "Q4c checkpoint:
   the table and the induction as built".
   a. `Expr`, `eval`, validity, the structural lemmas (leaf-set =
      vertex set, label classes partition it, edges within `X`,
      disjointness at ⊕ from leaf-injectivity), smoke `#eval`s on a
      hand k-expression (path 0—1—2 at k = 2).
   b. The C13 congruences.
   c. The table by choice; `typeOf e := typ q (eval e)` with label
      classes as the set parameters; the main induction — structural
      on `Expr`, one case per constructor, each case one C13 lemma;
      corollary at the root: the value determines `Sat G φ`
      (set-forget + adequacy + `X = univ` + `H = G`).
      **Checkpoint** (gates the freeze): lines per case, and whether
      the cross-graph plumbing stayed cheap.
5. ✅ **C0 freeze** (session 15, M11; orchestrator gate "freeze
   verified" at the end of that block): new files in `concepts/Lax11/` — `Mso.lean`
   (verbatim copy from proofs, as rev 4 planned), `CliqueExpr.lean`
   (`Expr`, `eval`, validity — the new trust object; must be
   auditable in one sitting, target ~40 lines of definitions),
   `Courcelle.lean` (`EncodesInstance`, the rev-5 axiom). Existing
   four concept files frozen verbatim. Smoke tests proofs-side (Sat
   on two-vertex graphs; the path k-expression hand-checked).
6. ✅ **Q6 — the driver, shrunk** (session 16, M12, commits 25daa9c +
   20937f6): instantiate `foldProgram` with the
   C14 table, reuse M3's read-phases against the new two-block
   encoding, add the accept epilogue, compose the `Run`, discharge
   the axiom, audit.
7. ✅ **Q7 — wrap-up** (session 17, M13; see Final state below):
   `#print axioms`, `lax build --replay`; ledger
   (C1, C2 de Bruijn, C5, C11 pivot + unformalized tw→cw conversion,
   expression-as-input, program-ignores-CSR, children-before-parent
   ordering, TreeDecomp disposition); abstract + manifest; final
   plan rev.

Order rationale: Q4 is now the only mathematics left and its riskiest
piece (η congruence) is bounded by an already-proved harder lemma;
the freeze stays after the Q4c checkpoint for the same D3-shaped
reason as before (the surface's `Expr`/`eval` must be verbatim what
the induction proved tractable).

## Feasibility judgment (rev 5)

Q4a: definitions + structural recursion, no risk. Q4b: three
q-inductions with identity moves — the session-10 checkpoint measured
the hypothesis-plumbing cost of the *eleven*-hypothesis cross-ambient
congruence at 580 lines with the real cost in restating hypotheses;
these have two or three hypotheses each. Q4c: structural induction,
one lemma per case. Q6: instantiation of verified components; the
only new program text is the epilogue. The research-engineering risk
the rev-2 plan carried (composition) was retired at session 10; the
pivot removes the largest remaining *volume* items (C7a label pass,
bag/overlap scanning, M8's canonical-order bookkeeping). Prior-art
note unchanged: no complete mechanization of Courcelle known to this
plan (in either width parameter); Traytel's MSO-on-words is the
nearest relative, automaton route, cite when confirmed.

## Final state (rev 6, session 17)

The theorem is proved. `Lax11.Courcelle.exists_linearTime_program_modelChecking`
is discharged by `Lax11Proofs.Courcelle.exists_linearTime_program_modelChecking`
with witness `driverProgram (table (rank φ) k) (acpArr (rank φ) k φ)`
and constant `46 * (100 + driverCost (table (rank φ) k))`; both
packages build green (concepts 821 jobs, proofs 2998), `lax build
ram-linear-time` and `lax build ram-linear-time --replay` are OK, and
`build-output.json` records the proof with `assumptions: []`. The axiom
audit is `propext`, `Classical.choice`, `Quot.sound` on the theorem and
on every spot-checked upstream result (`typ_union_congr`, `satIn_congr`,
`val_eq_typeOf`, `acceptVal_val`, `sweep_eq_val`), and the older
`exists_linearTime_program_ccLabels` is unchanged and equally clean.

What the submission contains, by plan step: the machine, the compiler
and the reasoning kit (the RAM stack, `ram-stack-plan.md` rev 7); the
connected-components driver (constant 2604); the generic tree-fold
schema `TreeFold*.lean` with its own theorem
`exists_linearTime_program_treeFold`; the type algebra `MsoTypes.lean`
/ `MsoAdequacy.lean` / `MsoComposition.lean` (composition at every
rank, cross-ambient); `CliqueExpr.lean` and the four op congruences of
`MsoCliqueOps.lean`; the table and main induction of `MsoTable.lean`;
the driver `CourcelleDriver.lean` / `CourcelleMain.lean`; and the three
new concept files `Mso.lean`, `CliqueExpr.lean`, `Courcelle.lean`,
which with the four originals make a surface of seven review units —
five definitions and two theorems.

Two dispositions were open at the wrap-up and are now settled.
`TreeDecomp.lean` (M7, 574 lines) is **kept**: it is self-contained
mathlib-only tree-decomposition theory, green, imported by nothing, and
stated in the shape a future MSO₂-and-treewidth submission would want;
deleting it would cost that submission its combinatorial layer for
nothing but a smaller build. And the honesty ledger, which under rev 5
was to be written into concept docstrings, is instead
`ram-linear-time/notes.md`: the concept surface was fully frozen at
M11, and the eleven items — MSO₁ scope, de Bruijn on the trust surface,
the noncomputable table, the cliquewidth pivot with its unformalized
tw→cw conversion, expression-as-input, the two unread input blocks, the
children-before-parent numbering, the add/sub-only machine with table
indexing strength-reduced to the `row` array, the stand-in table in the
`#eval` checks, the never-estimated tower, and the `TreeDecomp`
retention — belong together in one document rather than scattered
across seven.

What remains is outward-facing and Jan's: `lax submit`. Nothing in the
plan is open.
