# Night log — Lax11 step 6 relay

Read `cc-night-brief.md` first. Append your session block at the end;
never rewrite earlier entries. Next milestone: **M1** (`CCSpec.lean`).

## Session 1 — 2026-07-26 ~21:20 UTC
Milestone: M4 — done
Commits: 1c64ff9 Lax11 driver: the sweep, and the driver end to end
State: M1–M3 were already committed before this relay began (0f4691a,
00b82a6, 6c9ff7c) under the names `CCGraph.lean` (the pure graph
lemmas, not `CCSpec.lean`) and `CCSearch.lean` (scan, expand, drain).
This session turned `sweep-draft.lean.txt` into `CCSweep.lean`:
`outerBody_run`, `sweep_run` (`Run.while_pot` with `SweepPot = Pot +
27·(n−u)`), and `ccCom_run` — for every `x` with `EncodesGraph x n G`,
`Run ccCom (initEnv (ccExt n m) x) σ' K` with `σ'.out = ccLabels G` and
`K ≤ 84 * (x.length + 1)`. Full `lake build` green, no `sorry`;
`#print axioms ccCom_run` = propext, Classical.choice, Quot.sound.
`Reasoning.lean` gained two generic items: `replicate_eq_arrOf` and
`Com.NoWrite` + `Run.out_eq` (the output-tape frame condition).
Next: M5 — `computesInTime_of_run ccCom_ok` with the layout constant
(`layout.const = 31`: 4 arrays, `idxLen = 6`), so `31 * K ≤ 2604 *
(x.length + 1)`; state the endgame theorem with the `conclusion:
Lax11.ConnectedComponents.exists_linearTime_program_ccLabels`
frontmatter, in a new `CCMain.lean` imported from `Lax11Proofs.lean`.
Decisions: (1) `ccCom_run`'s bound is stated as `84 * (x.length + 1)`
rather than `a·n + b·m + d` — same content, and it makes M5 arithmetic
trivial. (2) Deleted `sweep-draft.lean.txt`: superseded by `CCSweep.lean`.
(3) The `lean-lsp` MCP server holds stale imports after a Bash `lake
build` — it reported `sorryAx` and unknown identifiers that the real
build does not; trust `lake build` / `#print axioms`.

## Session 2 — 2026-07-26 ~22:10 UTC
Milestone: M5 — done
Commits: a724004 Lax11 driver: the theorem, cashed in at the concept surface
State: Working tree was clean at start (only the untracked NIGHTLOG.md,
asdf, cc-night-brief.md). New `CCMain.lean` (imported from
`Lax11Proofs.lean`) proves `Lax11Proofs.CCMain.exists_linearTime_program_ccLabels`
with witness `ccProgram` and constant `2604`, carrying the
`conclusion: Lax11.ConnectedComponents.exists_linearTime_program_ccLabels`
frontmatter. `const_eq : layout.const = 31` as predicted, so the proof
is `computesInTime_of_run ccCom_ok` + `ccCom_run` + `omega`. Full
`lake build` in `proofs/` green, no `sorry` anywhere in `Lax11Proofs/`;
`#print axioms` on the theorem = propext, Classical.choice, Quot.sound.
Also checked by `rfl` that the proved statement is *definitionally the
same type* as the concept axiom (no drift).
Next: M6 — plan step 7: formalization notes / honesty ledger (D2, D4,
D5, D7, D16; move the "global queue + `sc` counter, both free" argument
out of `CC.lean`'s docstring into the notes), abstract, build output.
Decisions: (1) No `n ≤ |x|` / `2m ≤ |x|` arithmetic was needed at M5 —
session 1 had already folded it into `ccCom_run`'s `84 * (|x| + 1)`.
(2) Pre-existing `unusedSimpArgs` linter warnings in CCPhases.lean and
CCSweep.lean are untouched (cosmetic, not mine to churn).

## Session 3 — 2026-07-26 ~21:38 UTC (system clock; earlier entries' times look estimated)
Milestone: M6 — done
Commits: 9e1c903 Lax11 driver: the wrap-up — abstract, and the honesty of the program
State: The submission is complete. The honesty ledger asked for by step 7
(D2, D4, D5, D7, D16) turned out to be *already written*, in full, in the
`# Formalization notes` of the four frozen concept docstrings — nothing was
missing, and `concepts/` was not touched. So M6 was: (1) the "global queue +
`sc` counter, both free" argument moved out of `CC.lean`'s module docstring
(which the archive never renders) into a new `# What the program is allowed
to help itself to` section of the theorem annotation in `CCMain.lean`;
(2) `abstract.md`'s last paragraph rewritten — it still said the obligation
was open and still described the superseded D19 combinator DSL — now
describing the tower as built, plus the constant 2604 against the ~100
steps/input-number the `#guard`ed machine runs actually take. `lake build`
green; `lax build ram-linear-time --replay` OK, no violations,
`build-output.json` regenerated (gitignored), the proof's `assumptions: []`.
Next: nothing in the brief remains. Jan's call from here: `lax submit`
(outward-facing, deliberately not done), and revising `ram-stack-plan.md`,
which still reads "step 6 in progress" — steps 6 and 7 are both done.
Decisions: (1) An extra `#` section in a proof annotation beyond `# Proof
strategy` / `# Attribution` is accepted by `lax build` and renders as its
own block — that is where the "both free" argument now lives. (2) The
abstract now names a concrete looseness factor (~25×), computed from the
`#guard`s in `CC.lean` (e.g. `|x| = 14`, 1513 machine steps, bound 39060);
if Jan dislikes advertising it, delete that sentence, nothing depends on it.
(3) Pre-existing `unusedSimpArgs` warnings in CCPhases/CCSweep left alone
for the third session running.

## Session 4 — 2026-07-26 ~23:50 UTC
Milestone: the plan revision (post-M6 housekeeping) — done
Commits: 9feffa2 RAM stack plan rev 7: steps 6 and 7 done, step-6 checkpoint reported
State: No Lean was touched; only `ram-stack-plan.md`, committed alone (Jan's
NIGHTLOG.md / asdf / cc-night-brief.md left unstaged). Rev 7: title and the
opening status paragraph now say all seven steps are done and the submission
is complete except `lax submit`; steps 6 and 7 marked ✅ with what each
actually contained; and a new "Step-6 checkpoint: the driver as built"
section in the step-3/step-5 style, recording the six-module structure
(CC/CCGraph/CCPhases/CCSearch/CCSweep/CCMain, 1478 lines) against the plan's
`ccPure` sketch — the pure model became CCGraph's invariant-level lemmas
because a refinement proof against a second BFS is proved by exactly the
`Base`/`Live` invariant and adds a termination argument for nothing — plus
the numbers (84*(|x|+1), layout.const 31, 2604, ~25× loose at ~100 machine
steps per input number), the four kit additions (arrOf & friends,
replicate_eq_arrOf, Com.NoWrite/Run.out_eq, the while_pot drop
strengthening), and an honest pain paragraph: nothing was in doubt, the cost
was volume (825 of 1478 lines are the two cost files, eleven invariant
fields re-established at six `_run` lemmas).
Next: nothing. The relay is finished; `lax submit` is Jan's.
Decisions: (1) The stale-lean-lsp finding (session 1, decision 3) is
recorded as a **watch item** at the end of the step-6 checkpoint rather than
appended to the existing concept-namespace watch item, which is about a
different subject. (2) "Where the driver stands" and "Driver — connected
components at P3" were left in place as the historical record and merely
marked superseded by the checkpoint's heading, per the instruction not to
touch anything else.

## Session 5 — 2026-07-26 ~23:45 UTC (second relay: Courcelle)
Milestone: M1 (Q3a, tree-fold schema: program + evaluation) — done
Commits: e57055b Courcelle Q3a: the tree-fold schema, program and pure model
State: New `Lax11Proofs/TreeFold.lean` (378 lines), imported from
`Lax11Proofs.lean`; namespace `Lax11Proofs.TreeFold`; nothing else touched,
full `lake build` green, no `sorry`. It contains: `Table` (V, L, `init`,
`step`) with `Table.Wf`; the pure tree recursion `val` (fuel-based, with
`valAux_eq_val` and the usable equation `val_eq_foldl`) plus `val_lt`; the
Env-free accumulator sweep `sweep` with `sweep_eq_foldl` / `sweep_eq_val`
(*the* mathematical content of Q3 — the program's one pass computes the
tree fold, proved with no environment in sight, per the step-6 strategic
instruction); `EncodesTree`; the table's three arrays (`initList`,
`rowList`, `stepList`) and the `storesFrom` prologue generator; the program
`foldCom` (read N, read `par` and `lab` via CC's `readLoop`, materialize the
table, `seedLoop`, `pushLoop`, write `acc[N-1]`), `layout` (4 scalars, 6
arrays, 4 temps) and `foldProgram`; nine `#guard`s of the compiled machine
program against the model.
Next: M2 — the `Run` lemmas. Order: `storesFrom_run` (induction on the
list, `3*|vs|+1`), `seedLoop_run` and `pushLoop_run` by `Run.while_count`
in the `CCPhases` style, invariant "`acc` array = `arrOf N (sweep T par lab
i)`" so `sweep_eq_val` closes it at the end. The global-potential form is
not needed here — every loop is uniform-cost, so `while_count` suffices and
the brief's "nodes left + child-slots left + table-slots left" potential
collapses to three separate counted loops. `Com.Ok layout (foldCom T)` is
already checked to go through except for the three `stores` cases, which
want a `storesFrom_ok` induction lemma (drafted, ~3 lines).
Decisions: (1) **The schema has two tables, not three.** The brief's
"table(label, fold of children values)" suggested a post-map applied to a
node's value on its way to its parent (which C4 needs, for the forget +
overlap re-indexing). It is not a separate table: carrying the node's label
inside the value alphabet makes it part of the parent's `step`, and the
alphabet blow-up is Lean-side and free (C5). So `val i = foldl step (init
(lab i)) (children i)`, seeded by the node's own data — which is the
C4-correct shape, *not* a fold of the children with each other. If the
orchestrator wants the explicit `final` table back, it is one more array
and one more lookup. (2) **Per-node data is one label, not a CSR block.**
The brief said both. The schema reads a `lab` array of one number per node;
Q6's bag scanning (C7, `O(k²)` per node) is a *separate earlier phase* that
computes that label. This keeps the schema exactly generic and keeps
per-node cost in the fold visibly O(1) — two array reads. (3) No
multiplication in the machine language, so the step table is read at
`row[a] + b` with the row bases `a*V` themselves a materialized array.
(4) `1 ≤ N` is part of `EncodesTree`: with `N = 0` the program's final read
of `acc[N-1]` is out of range and stuck. A decomposition always has a node.
(5) The `#eval`-before-proving discipline earned its keep again: the
depth-two test initially used labels `3, 4` against a three-label table, the
machine read past the seed array into another array's interleaved cells,
and the mismatch is exactly the `lab i < L` clause of `EncodesTree`. The
test now sits in the file with that story in its comment. (6) `readLoop` is
reused from `CC.lean` (with `CCPhases.readLoop_run` waiting for M2) rather
than duplicated; it is generic and should move to `Reasoning.lean` when
TreeFold migrates to its own submission — it cannot move now without
editing `CC.lean`, which the brief forbids. `runOut` *is* duplicated (three
lines) so the file's only CC dependency is the read loop.

**Orchestrator note (after night-2 session 1 / M1):** both design
calls approved — two tables with the label carried in the value
alphabet (the child's overlap pattern is per-node data seen from the
child, so this is exactly what Q6 needs), and per-node single label
with the bag scanning in a separate earlier phase. That phase has a
nonobvious linearity trap, now pinned as C7a in courcelle-plan.md
(rev 3, committed) together with the two coherence lemmas Q2 owes.
Proceed with M2.

## Session 6 — 2026-07-27 ~01:20 UTC
Milestone: M2 (Q3b, the fold-loop `Run` lemmas) — done
Commits: cbb7ef4 Courcelle Q3b: the tree-fold schema, run
State: New `Lax11Proofs/TreeFoldRun.lean` (268 lines), imported from
`Lax11Proofs.lean`; `TreeFold.lean` gained three pure lemmas (`sweep_zero`,
`sweep_succ`, `sweep_lt`) and `Reasoning.lean` two generic kit items
(`arrOf_congr`, `getD_arrOf`). Nothing else touched; full `lake build`
green, no `sorry`, `#print axioms` on all five new `_run`/`_ok` theorems =
propext, Classical.choice, Quot.sound. Proved: `storesFrom_ok`,
`storesFrom_run` (`3*|vs|+1`, induction on the list), `stores_arrOf_run`
(the usable corollary: the array ends up holding the generating function
itself), `seedLoop_run` (`13*N+6`), `pushLoop_run` (`22*N+8`, conclusion
`acc = arrOf N (val T par lab)`), `foldCom_ok`.
Next: M3 — Q3c, end to end. Compose `.read "N"` + two `readLoop_run`s +
three `stores_arrOf_run`s + `seedLoop_run` + `pushLoop_run` + the final
`.write`, choosing `ext`: `par,lab,acc ↦ N`, `ini ↦ T.L`, `row ↦ T.V`,
`tab ↦ T.V*T.V`. The three table extents do not depend on the input, which
is fine (`ext` is chosen per input, D17). Then `computesInTime_of_run
foldCom_ok`; `layout.const = 3*(6-1+3)+13 = 37`. Note the bound is linear
in `N` plus a table-sized constant `3*(L+V+V²)+3` — with the table fixed
before the graph, per C5's quantifier order, that constant is legitimate;
say so in the theorem's prose. Then the step-1-style checkpoint block.
Decisions: (1) The phase lemmas are stated with the *function* named
(`arrOf N (val T par lab)`, `arrOf T.L T.init`) rather than with an
existential + pointwise agreement, which is what CCPhases does. That is
what `arrOf_congr` buys, and it makes M3's plumbing between phases
syntactic instead of another layer of `∃ g, ∀ i < n`. Recommend the CC
files adopt it if they are ever touched again — not touching them now.
(2) `pushLoop_run` takes `1 ≤ N` and `∀ i, i+1 < N → i < par i ∧ par i < N`
directly rather than `EncodesTree`, so the schema's loop lemmas are
independent of the encoding; `EncodesTree` is unpacked once, at M3.
(3) `sweep_lt`'s hypotheses are bounded by `N` (`∀ i < N, lab i < T.L`),
unlike the M1 `val_lt`, whose global `∀ i, lab i < T.L` is not obtainable
from a read array. `val_lt` is so far unused; if M3/Q6 needs it, it wants
the same bounded restatement — flagging rather than churning M1's file.

## Session 7 — 2026-07-27 ~03:05 UTC
Milestone: M3 (Q3c, the schema end to end + the Q3 checkpoint) — done
Commits: 4244c41 Courcelle Q3c: the tree-fold schema, end to end
State: New `Lax11Proofs/TreeFoldMain.lean` (196 lines), imported from
`Lax11Proofs.lean`; nothing else touched (TreeFold.lean and TreeFoldRun.lean
unchanged — the M2 phase lemmas composed without a single restatement).
Full `lake build` green, no `sorry`; `#print axioms` on both new theorems =
propext, Classical.choice, Quot.sound. Contains: `foldExt` (the per-input
extents: three tree arrays at `N`, three table arrays at `L`, `V`, `V²`),
`tableCost T = 3*(L+V+V²)+35`, `foldCom_run` (for every `x` with
`EncodesTree x N par lab T.L`: `Run (foldCom T) (initEnv (foldExt T N) x) σ' K`
with `σ'.out = [val T par lab (N-1)]` and `K ≤ 60*(|x|+1) + tableCost T`),
`const_eq : layout.const = 37`, and `exists_linearTime_program_treeFold` —
for every `T.Wf` a program and a constant `37*(60 + tableCost T)` that folds
the table over every encoded tree in linear time. Plus a `#guard` joining the
`#eval` harness's `encTree` to the shape `EncodesTree` asserts.
Next: M4 — Q1a-1, the type algebra's definitions (`T q r s`, `typ`,
`Fintype`/`DecidableEq` through the recursion), in a new
`Lax11Proofs/MsoTypes.lean`, namespace `Lax11Proofs.MsoTypes`, zero imports
from the TreeFold files. Q3 is closed.

### Q3 checkpoint: the schema as built

*Is "table := the type table" a plug-in?* Yes for the fold, with one
missing piece and one thing that is not what it looks like.
- The interface is four fields and two closure facts: `V`, `L`,
  `init : ℕ → ℕ`, `step : ℕ → ℕ → ℕ`, `Wf`. It is ℕ-valued, so Q1 owes a
  *numbering* of the types (`Fintype.equivFin` on `T q r s`, noncomputable
  by C5, fine) and `init`/`step` transported along it. Nothing else: no
  computability, no decidability, no bound on `V`.
- **Missing piece (C9).** The schema writes the root's *value* — a type
  number — not `[1]`/`[0]`. The accepting set is a fourth table: one more
  `arrOf V` materialized by `stores_arrOf_run`, and the final `.write`
  reads `acc[N-1]` through it instead of directly. Three lines of program,
  one more `stores_arrOf_run` in the composition; costed at `3V+1`.
- **Not what it looks like: `foldCom` is not Q6's program.** Its read phase
  reads a bare `N, par, lab` word, and C6's instance is CSR graph + bags.
  What Q6 reuses is the *phase lemmas* — `stores_arrOf_run`, `seedLoop_run`,
  `pushLoop_run` — which are stated on arrays (`σ.arrs "lab" = arrOf N lab`),
  never on the input word (M2 decision 2, and it pays off here exactly as
  intended). In Q6 the `lab` array is *computed* by the C7a label pass rather
  than read, and the lemmas do not care. `foldCom`/`foldCom_run`/
  `exists_linearTime_program_treeFold` remain as the schema's own theorem and
  as the tested harness — worth keeping, not on Q6's critical path.

*Is per-node cost visibly O(bag work)?* The fold's per-node cost is
**constant, and independent of `V`, `L` and `k`**: 13 IMP+ units seeding
(two array reads and a store) plus 22 pushing (a parent read, two
accumulator reads, two table reads for the `row`/`tab` indexing, a store).
No loop in the schema scales with the alphabet. All the `k`-dependence of
Courcelle therefore lives in the C7a label pass, where the plan puts it,
and none of it can hide in the fold. The table's own `3*(L+V+V²)` is paid
once, before the tree is touched.

*Looseness, measured.* On the depth-two test (`|x| = 13`, `sumTable`,
`V = L = 3`): 1188 machine steps against a bound of 72520, ~61×. The
prologue dominates at six nodes; the ratio is the usual CC-style slack
(31 vs 37 machine steps per IMP+ unit, loose phase bounds) and nothing was
fought over.

*What Q6 still needs, beyond Q1/Q2:* (a) the accept table and the 0/1
write; (b) the C6 readers for the CSR block and the bag arrays; (c) the
C7a label pass — `top v`, the top-node scan, the top-down propagation,
the overlap patterns — which is the real driver work and is where the
`O(k²)` per node sits; (d) the numbering bridge from `Fintype` to ℕ.

*One thing for the step-7 ledger.* `stepList` has `V²` entries, so for the
type table the *program itself* is a tower in `|φ|` and `k`, not just the
constant. The statement allows it (`p` is quantified after `φ` and `k`) and
every textbook Courcelle has the same property, but the notes should say it
in one sentence rather than let a reader discover it.

Decisions: (1) `foldCom_run`'s bound is left in the two-term shape
`60*(|x|+1) + tableCost T` rather than collapsed to one constant, so that
the input-linear part and the table's fixed price stay separately visible;
the collapse to `37*(60 + tableCost T)*(|x|+1)` happens once, at
`exists_linearTime_program_treeFold`. (2) `val_lt` (M1) is still unused —
`sweep_lt` did all the work at M2 and M3 needed no new bound. Leave it;
if Q6 never wants it, delete it then rather than churn now. (3) Kit
unchanged: `Reasoning.lean` gained nothing this session, `arrOf_congr` and
`getD_arrOf` from M2 were exactly what the composition needed. (4) The
`#guard` on `encTree` vs `EncodesTree` is new house practice worth keeping:
the `#eval` harness and the proved statement are otherwise joined by
nothing but the reader's eye.

## Session 8 — 2026-07-27 ~00:18 UTC (system clock; sessions 5–7 stamps run ahead of it)
Milestone: M4 (Q1a-1, the type algebra: definitions) — done
Commits: 4a7944d Courcelle Q1a: the type algebra, definitions
State: New `Lax11Proofs/MsoTypes.lean` (329 lines), imported from
`Lax11Proofs.lean`; namespace `Lax11Proofs.MsoTypes`; zero imports from the
TreeFold files (mathlib only), nothing else touched. Full `lake build` green,
no `sorry`; `#print axioms` on `typ`, `instFintypeT`, `vMoves_typ`,
`typ_congr_inter` = propext, Classical.choice, Quot.sound. Contains:
`Atomic r s` (adj/eq/mem, `deriving DecidableEq, Fintype`); `T q r s` by
recursion on the rank with move sets as characteristic functions into `Bool`;
`finDec` (one recursion carrying `Fintype` *and* `DecidableEq`, computable) and
the two instances; `T.mk`/`T.diagram`/`T.vMoves`/`T.sMoves` + `T.ext` + `_mk`
simp lemmas; six `#guard`ed cardinalities (`card (T 1 0 0) = 32`); `Atomic.of`
and `typ G X q m A` (noncomputable, `open Classical in`), with `diagram_typ`,
`vMoves_typ`/`sMoves_typ` (iff form, no `decide` in any statement) and their
witness halves `vMoves_typ_snoc`/`sMoves_typ_snoc`; a two-vertex smoke test
that ambient adjacency reaches the diagram; and the first q-induction,
`typ_congr_inter` — assignments agreeing on `X` give `X` the same type.
Cost: the whole file was green on the first compile, no approach was
abandoned. Instance plumbing took two tries (`inferInstance` will not unfold
`T`; a type ascription to the spelled-out layer fixes it).
Next: M5 — adequacy and the mark lemmas. First item is the MSO syntax, which
I deliberately did **not** define (see decision 3).
Decisions: (1) **Move sets are `α → Bool`, not `Finset`/`Set`.** A `Finset`
needs `DecidableEq` for the type the same recursion is still defining, and
`Set` costs `Fintype Prop` and noncomputable instances (killing the `#guard`s).
Bool characteristic functions carry the same data and need nothing;
`FinDec` (the brief's permitted bundle) is a 6-line structure and both
instances are ~8 lines total. This is the "instance plumbing" the brief flagged
and it is a non-issue. (2) `typ`'s `r`/`s` are **implicit** (inferred from `m`
and `A`), only `q` explicit — use sites in M5/M6 will have many `typ`s and
`typ G X q m A` reads far better than `typ G X q r s m A`; the equation
compiler recurses through implicit arguments without complaint. New marks and
sets are appended with `Fin.snoc` (last position), per the brief's
concatenated-marks guidance. (3) **No MSO syntax yet** — the brief puts it at
M5 and I left it there rather than pin it blind, which is the D3 mistake at
10× cost. Recommendation for M5, from how `typ` came out: use the well-scoped
indexed family `MSO r s` (atoms `adj i j`/`eq i j` with `i j : Fin r`,
`mem i X` with `X : Fin s`; `exV : MSO (r+1) s → MSO r s`,
`exS : MSO r (s+1) → MSO r s`), whose indices then line up with `typ`'s `r`/`s`
argument-for-argument, and `Closed φ := ` the family at `0 0`. Orchestrator
note: plan C0's `(φ : MSO) (hφ : φ.Closed)` would become `(φ : MSO 0 0)` at
step 5 — same theorem, one less predicate on the surface, but it *is* a
surface change and is yours to approve. (4) **Recommendation for M6, worth
deciding before the session starts:** state composition as a *congruence*, not
as a function — "if `typ q X … = typ q X' …` and `typ q Y … = typ q Y' …` and
the overlap patterns agree, then `typ q (X ∪ Y) … = typ q (X' ∪ Y') …`" —
and likewise adequacy as "equal types ⟹ same truth". Then `F` is never
defined: it is extracted at the end from `Fintype` + choice, which C5 already
licenses, and the q-induction never has to build the right function on types.
Every downstream use (the table's existence, C5) is served by the congruence
form. The module docstring records this idiom as what the definitions are
shaped for. (5) `typ_congr_inter` was proved now rather than at M5 because the
set-splitting step of composition (`S ↦ (S ∩ X, S ∩ Y)`) cannot even be stated
without it, and it doubled as the measurement of whether the recursion is
workable: 18 lines, `Bool.eq_iff_iff` + `exists_congr` + `Fin.lastCases`, no
re-indexing pain. (6) `T` is a `def`, so `Prod.fst` is never used directly —
the constructor/projection/ext API is there so that M5/M6 never depend on the
tuple encoding, and `Layer q r s` exists only to make the ascriptions that
teach instance search to unfold `T` readable.

**Orchestrator note (after session 8 / M4):** both recommendations
approved and folded into courcelle-plan.md rev 4 (committed): MSO as
a well-scoped family `MSO r s` (M5 builds it that way; step 5's
surface copies it verbatim, axiom over `MSO 0 0`), and M6's
composition stated as a cross-ambient congruence with no `F` — the
table comes later by Fintype + choice. M6's acceptance changes
accordingly: the checkpoint measures the congruence at q ≤ 1.
Proceed with M5.

## Session 9 — 2026-07-27 ~00:28 UTC
Milestone: M5 (Q1a-2, adequacy and the mark lemmas) — done
Commits: 040b950 Courcelle Q1a: MSO, adequacy, and the mark lemmas
State: Two new files, both imported from `Lax11Proofs.lean`, both in namespace
`Lax11Proofs.MsoTypes`, zero imports from the TreeFold files. `Mso.lean` (211
lines): the well-scoped family `MSO r s` per C2 rev 4 (seven constructors),
`rank` with its seven simp lemmas, the trusted `Sat` (fifteen lines, two
environments, no `Closed`, no substitution), the relativized `SatIn` with its
simp lemmas, the bridge `satIn_univ`, and four hand-checked smoke sentences on
the two-vertex graphs. `MsoAdequacy.lean` (292 lines): `liftLast` +
`snoc_comp_liftLast` (the only re-indexing bookkeeping in the file);
`Atomic.remap`/`Atomic.of_comp`; **the mark lemma** `typ_comp_congr` — for
arbitrary `σ : Fin r' → Fin r` and `τ : Fin s' → Fin s` simultaneously,
remapping is a congruence for `typ` — with `typ_forgetV_congr` /
`typ_forgetS_congr` as `Fin.castSucc` instances and an `example` doing
permutation-and-duplication in one line; three diagram-transfer lemmas; and
**adequacy** `satIn_congr` (rank ≤ q + equal `q`-types ⟹ same truth, across two
ambient graphs), with `sat_congr` and `sat_congr_sentence` at `X = univ`.
Full `lake build` green (2987 jobs), no `sorry`; `#print axioms` on all six
theorems = propext, Classical.choice, Quot.sound.
Cost: both files were green within two compile rounds; no approach was
abandoned. The mark lemma is 57 lines, adequacy 47.
Next: M6 — Q1a-3, composition at q ≤ 1 in the cross-ambient congruence form of
C3.3, then THE checkpoint. Everything M6 needs is now in place: `typ_comp_congr`
supplies the concatenated-mark re-indexing (`σ = Fin.castAdd`/`Fin.natAdd`),
`typ_congr_inter` (M4) the set-splitting step.
Decisions: (1) **`Sat` and `SatIn` are two definitions, not one.** The trust
surface should carry the plain recursion with quantifiers over the whole graph
(that is what a reader checks against a paper); the type algebra needs
satisfaction relativized to a region. Defining `Sat := SatIn univ` would put a
region in the surface for nothing, so both exist and `satIn_univ` joins them —
ten lines, and step 5 copies out `MSO`/`rank`/`Sat` verbatim with `SatIn` left
behind in the proofs package. (2) **One mark lemma, not three.** Forget,
permute and duplicate are `typ_comp_congr` at three `σ`s, and so is the
`Fin.append` re-indexing M6 needs; the brief's "prove them through one general
remap lemma if that works" — it works, and the general statement is *easier*
than forget alone, because the induction step needs the lifted remap
`liftLast σ` and specializing that to `Fin.castSucc` mid-induction would not
close. (3) **De Bruijn levels, not indices**: `Fin.snoc` binds at the *last*
position, so the outermost bound variable is `0`. This matches `typ`'s moves
(M4) and is why adequacy needs no shifting whatsoever; it is stated in the
module docstring because a reader will otherwise assume indices. (4) Adequacy
and the mark lemma are both stated cross-ambient (two graphs on different
vertex counts) from the start, since C3.3 rev 4 is cross-ambient and it costs
nothing — `T q r s` mentions no graph. (5) `induction φ` leaves the family's
indices `r s` inaccessible in the quantifier cases; `rename_i r s` recovers
them. Recorded because it is the kind of thing that eats twenty minutes twice.

## Session 10 — 2026-07-27 ~00:43 UTC
Milestone: M6 (Q1a-3, composition + THE checkpoint) — done, **at general `q`**
Commits: 5695678 Courcelle Q1a: composition, the cross-ambient congruence
State: New `Lax11Proofs/MsoComposition.lean` (580 lines), imported from
`Lax11Proofs.lean`, namespace `Lax11Proofs.MsoTypes`; nothing else touched
(MsoTypes/Mso/MsoAdequacy unchanged — M4 and M5 composed with no
restatement). Full `lake build` green (2988 jobs), no `sorry`; `#print
axioms` on `typ_union_congr`, `typ_append_congr`, `typ_succ_congr`,
`atomic_union_congr` = propext, Classical.choice, Quot.sound. Contains:
`Glue` (the six gluing hypotheses) with `symm`/`mem_union`/`snocX`/`append`;
`adj_of_cross` and `atomic_union_congr` (the rank-0 layer);
`typ_succ_congr` (rank `q+1` determines rank `q`); the pool bookkeeping
(`snoc_liftLast_apply`, `snoc_castSucc_apply`), `pat_snoc`, `pat_symm`,
`set_witness_agree`; **`typ_union_congr`** — the cross-ambient congruence
at *every* `q`; `typ_append_congr` — the same with C3.3's concatenated
marks; the `q = 0` and `q = 1` instances the brief asks for as `example`s;
and a non-vacuity check (the path `0—1—2` glued at its middle vertex).
Next: the orchestrator's call. Q1b's "general composition by induction on
q" is **done**; what remains of step 3 is only the realizable-at-width-k
finite restriction of the table (and the `Fintype`+choice extraction of the
table itself, which is where C5 gets cashed in). Q2 is the natural next
line.

### Q1a checkpoint: the composition lemma as built

*Verdict: **grind, and a short one**. No redesign. The general-`q`
induction is not a harder object than `q ≤ 1` — it is the same object, and
it fell out of the same induction on the first compile.* The measured
reason: `T q r s` mentions no graph, so the cross-ambient statement costs
nothing; and the ambient-subset formulation (plan C3, the decision the
plan called "the trick that makes Q1 formalizable") means gluing is `X ∪ Y`
and the induction never manipulates a structure.

*Lines per obligation* (580 total, of which ~120 are docstrings):
- the gluing hypotheses `Glue` + `symm`/`mem_union`: 33
- the rank-0 layer: `adj_of_cross` 23, `atomic_union_congr` 40 — **63, the
  largest single obligation**, and the only place the no-edge hypothesis
  is used
- `typ_succ_congr` (rank drop): 56
- pool bookkeeping (`snoc_liftLast_apply`, `snoc_castSucc_apply`,
  `Glue.snocX`): 36
- `pat_snoc` (the new mark's overlap pattern): 24
- `set_witness_agree` (the two set witnesses agree on the overlap): 15
- `typ_union_congr` itself: 154, split as statement 11, `q = 0` case **3**,
  vertex move 26 (`vkey` 17 + `vstep` 9), set move 58, assembly 13 — plus
  **37 lines of pure hypothesis-package restatement** in the three inner
  `have` signatures, which is a third of the theorem's body and is Lean
  tax, not mathematics
- `Glue.append` + `typ_append_congr` (C3.3's concatenated form): 38
- acceptance instances + non-vacuity: 35

*Where the pain is — and where it is not.*
- **Not re-indexing.** This is the headline. The plan named re-indexing
  inside the q-induction as the known pain point and built the M5 mark
  lemmas to keep it out; in the event the induction uses **no mark lemma at
  all**. The shared-mark-pool formulation (see below) makes the vertex
  move's re-indexing two `simp`-level facts, and `typ_comp_congr` is never
  invoked. The mark lemmas remain right for C4's forgets; they were not
  what composition needed.
- **Not set splitting either**, mathematically: `S ↦ (S ∩ X, S ∩ Y)` is
  exactly as clean as the plan said. But it is the *longest* case (58
  lines) because each of the two sides needs four steps — transfer the
  half through the side's `sMoves`, read the marks' membership off the
  diagram, prove the two witnesses agree on the overlap, then two
  `typ_congr_inter` rewrites to swap `S ∩ X` for `S` and `SX` for
  `SX ∪ SY`. `typ_congr_inter` (proved at M4 precisely for this) is the
  load-bearing lemma; without it the statement could not even be formed.
- **Not instance friction**: zero. `Fintype`/`DecidableEq` never appear in
  this file — the congruence form (M4 decision 4) means no table is built,
  so no enumeration is ever touched.
- **The real cost is hypothesis plumbing.** Six `Glue` fields × two sides +
  the overlap pattern + two type equalities = eleven hypotheses that must
  be restated verbatim at every inner `have` (they cannot be `variable`s,
  because the inner steps need them re-quantified for the X↔Y and 1↔2
  swaps). That is the 37 lines above, and it is the only thing that would
  get worse in a bigger induction.
- **One genuine mathematical step beyond the plan's sketch**: the vertex
  move needs the *other* side's hypothesis one rank down, which the plan's
  sketch does not mention. Hence `typ_succ_congr` (56 lines, its own
  q-induction). It is a fact worth having anyway.

*Deviation from the plan's guidance, argued (C3.3's "concatenated marks").*
The workhorse `typ_union_congr` gives the union **one mark pool**
`m : Fin c → Fin n` and lets each side read its marks through an index map
(`σ : Fin a → Fin c`, `τ : Fin b → Fin c`); C3.3's concatenated form is the
instance `c = a+b`, `σ = Fin.castAdd`, `τ = Fin.natAdd`, and is proved as
`typ_append_congr` in 18 lines, so the plan's interface exists verbatim.
Two reasons the pool is the right workhorse: (1) the vertex move appends
to the pool with `Fin.snoc`, and both sides' maps then re-index by
`snoc_comp_liftLast` (already proved at M5) and `Fin.snoc_comp_castSucc` —
with concatenated marks the same step needs a hand-built permutation
`Fin (a+b+1) → Fin ((a+1)+b)` and a `typ_comp_congr` application in every
case; (2) C4's sequential fold absorbs children one at a time into a
growing boundary, which is *one pool growing*, not iterated `Fin.append`
with an associativity/re-indexing argument at each child. Recommend C4 be
written against the pool form directly.

*Two things the checkpoint should record for later.*
- `Glue.sep` is stated as "an edge from `X` to `Y` has an endpoint in the
  overlap" rather than "no edges between `X ∖ Y` and `Y ∖ X`" — the same
  condition, in the form every use site wants. Q2's separation lemma should
  produce it in this shape.
- The non-vacuity `example` (path glued at its middle vertex) is house
  practice worth keeping: a congruence with eleven hypotheses can be
  vacuously true, and nothing else in the file would notice.

Decisions: (1) The general-`q` theorem is what is committed; `q = 0` and
`q = 1` are `example`s that instantiate it, so the brief's acceptance
criterion is met literally and the milestone is not left half-open. (2)
`typ_succ_congr` lives in this file rather than in `MsoTypes.lean`, to keep
the three committed M4/M5 files untouched; it is a general `typ` fact and
should move up if those files are ever revised. (3) The `Glue` hypotheses
are a `structure` in `Prop`, not eleven loose arguments — otherwise the
inner `have`s of the induction would be unreadable. Its `cover` field
(every pool mark belongs to a side) is the one hypothesis the concatenated
form gets for free and the pool form must state. (4) Kit unchanged:
`Reasoning.lean` untouched, no new mathlib-shaped lemmas needed.

**Orchestrator note (after session 10 / M6): THE GATE IS GREEN.**
General-q composition on the first compile settles it — no redesign,
Q1 core complete. The mark-pool deviation is approved (the derived
concatenated form is what downstream uses). Continuation milestones
M7–M11 are appended to courcelle-night-brief.md (rev 3); proceed
with M7.

## Session 11 — 2026-07-27 ~00:59 UTC
Milestone: M7 (Q2a, decomposition set theory) — done
Commits: 736bbe0 Courcelle Q2a: tree decompositions, the set theory
State: New `Lax11Proofs/TreeDecomp.lean` (574 lines), imported from
`Lax11Proofs.lean`, namespace `Lax11Proofs.TreeDecomp`; nothing else touched
(the four Mso files and the three TreeFold files unchanged). Mathlib-only
imports — no `Run`, no MSO. Full `lake build` green (2989 jobs), no `sorry`,
no new warnings; `#print axioms` on the eleven main theorems = propext,
Classical.choice, Quot.sound (two of them need no choice at all). Contains:
`Desc par s t` (descendant, as parent-map iteration) with refl/trans/step/
`par_of_ne`; `Valid` (seven fields: `pos`, `par_gt`, `par_mem`, `par_root`,
`vertex_cover`, `edge_cover`, `coherent`) and `Width`; the parent-map
arithmetic (`le_par`, `par_lt`, `iterate_lt/le_iterate/iterate_mono`); the
tree order (`desc_le`, `desc_lt`, `desc_antisymm`, `desc_of_desc_of_le` =
**two ancestors of a node are comparable**, `desc_total`, `desc_root`,
`exists_child`); `top` by `Nat.findGreatest` with `top_lt`, `le_top`,
`mem_top`, `top_eq` (uniqueness), `mem_par_of_lt_top` (the climb), `desc_top`
(every occurrence descends from the top — the connectivity, in usable form)
and `mem_of_desc` (occurrences are upward closed to the top); `subtree` as a
`Set (Fin n)` with `mem_subtree_iff` (**bag ∪ children's subtrees** — the
fold's induction step) and `subtree_root = univ`; `mem_bags_of_out` (the exit
lemma) with `separation`, `no_edge_interior`, `sep_glue`,
`bags_inter_subtree`, `sibling`, `sibling_interior_disjoint`,
`child_not_desc`; and C7a's two lemmas, `desc_min_top` + `mem_bags_min_top`
(an edge is present at the lower of its endpoints' top nodes, and at no node
above it) and `mem_bags_par_of_edge` (an edge of `B_c` whose top node is not
`c` is in `B_{par c}` — the soundness of the top-down propagation). Closing
smoke test: the path `0—1—2` with bags `{0,1}—{1,2}`, `Valid` and `Width … 1`
proved, three `#guard`s on `top`, and `subtree = univ` at the root.
Cost: green within three compile rounds; no approach was abandoned. The
longest proof is `mem_bags_of_out` at 14 lines; everything else is under 10.
Next: M8 — Q2b + step 3, the table and the main induction. The pieces are in
place and the interfaces line up: `mem_subtree_iff` gives the induction step
over `children par t` (same `par : ℕ → ℕ` the schema folds, no translation),
`sep_glue` produces `Glue.sep` verbatim for `X ⊇ ↑(bags (par c))`,
`bags_inter_subtree` + `sibling` give `Glue.interX`/`interY` (the overlap of
the accumulator with a child's subtree is inside `B_c ∩ B_t`, hence marked
once the marks are the bag), and `subtree_root` + adequacy close the
corollary at the root.
Decisions: (1) **Coherence is one clause, not a path predicate**: "`v` occurs
at `i` and again higher up ⟹ `v` occurs at `par i`". For a *rooted*
decomposition this is equivalent to connectivity of the occurrence set, it is
first-order and needs no auxiliary path type, and every lemma in the file is
a climb along it. The equivalence is not proved (nothing needs it); the
docstring states which form is meant. (2) **The root is its own parent**
(`par_root : par (N-1) = N-1`), a new convention this file introduces. It is
what makes `Desc` never escape the tree — without it `par (N-1)` is
unconstrained and could point anywhere, which breaks every `Desc` lemma.
It costs nothing: `children par i` looks at `c < i` only, so a self-parenting
root has no extra child, and M1's `EncodesTree` is *compatible* but does not
require it — **M8/Q6 must add `par (N-1) = N-1` to `EncodesInstance`**, i.e.
the encoded parent array holds `N-1` at the root. Flagging it as the one
encoding change M7 forces. (3) Nodes are ℕ and bags are `ℕ → Finset (Fin n)`,
not `Fin N → …`: the fold's `par : ℕ → ℕ` is ℕ-indexed, `Fin N` would put a
cast at every use site, and out-of-range nodes are simply never mentioned
(every lemma carries `_ < N` where it matters). (4) `top` is
`Nat.findGreatest`, so it *computes* — the `#guard`s exercise it, and the
driver's phase (a) computes the same function. (5) Several lemmas turned out
not to need `c < N` (the bound comes along the `Desc` chain from an
occurrence): `mem_bags_of_out`, `separation`, `sep_glue`, `sibling` are
stated without it. (6) `sibling` is stated for *incomparable* nodes, with
`child_not_desc` deriving incomparability for distinct children; that is the
form the fold wants, since the accumulator holds several already-absorbed
children at once. (7) Kit unchanged: `Reasoning.lean` untouched, no
mathlib-shaped lemma was missing.

## Orchestrator — 2026-07-27 (day): plan rev 5, the cliquewidth pivot

Jan's call in session, confirmed against the code as built: the width
parameter becomes **cliquewidth**; the theorem is
Courcelle–Makowsky–Rotics (MSO₁ model checking linear-time given a
k-expression). The accounting that decided it:
- **Consumed as-is**: M4–M6 in full — `typ_union_congr` at the
  *empty pool* (`c = 0`) is exactly disjoint-union composition, so
  the make-or-break lemma is already proved and its eleven
  hypotheses collapse to two at every use site; M1–M3's fold schema
  becomes a *verbatim* plug-in (op codes are the `lab` array; the
  "label inside the value" device its header advertises handles ⊕'s
  two-step absorption).
- **Deleted from the plan**: all shared-boundary machinery — marks
  in outer statements (`r = 0` everywhere now; labels are the `s = k`
  set parameters), overlap patterns, canonical bag order, forgets in
  the fold, and C7a's entire four-phase label pass. The program
  reads only the expression block; CSR is consumed by the statement.
- **Sunk**: M7's `TreeDecomp.lean` (574 lines) idles — stays in the
  build untouched, disposition at wrap-up.
- **New debt**: C13's op congruences (`typ_addEdges`, `typ_setRemap`,
  `typ_singleton` + the disjoint-union instance) — q-inductions with
  identity vertex sets, each bounded above by the proved union
  congruence; and the honesty item that the treewidth form now needs
  an unformalized tw→cw conversion (ledger, same status as
  Bodlaender/cliquewidth-approximation).
Plan bumped to rev 5 (C11–C14 added; C4/C6/C7/C7a superseded); brief
milestones rewritten (rev 4): M8 Q4a expressions, M9 Q4b congruences,
M10 Q4c table + main induction + gate, M11 freeze, M12 driver, M13
wrap-up. Relay resumes at M8.

## Session 12 — 2026-07-27 ~22:40 UTC
Milestone: M8 — Q4a (k-expressions, the object) — done
Commits: 5a99b35 "Courcelle Q4a: k-expressions, the object"
State: `ram-linear-time/proofs/Lax11Proofs/CliqueExpr.lean` (413 lines,
namespace `Lax11Proofs.CliqueExpr`, imported from `Lax11Proofs.lean`; imports
Mathlib only — zero coupling to MsoTypes or TreeFold). Contains: `Expr n k`
(`leaf v l` / `union` / `addEdges i j` / `relabel i j`); the evaluator split
into four independent structural recursions — `leafIds : List (Fin n)`,
`verts : Finset (Fin n)`, `cls : Fin k → Finset (Fin n)`,
`graph : SimpleGraph (Fin n)` (`⊥` / `⊔` / `⊔ SimpleGraph.fromRel …`) — plus
`opsOk : Bool`; a `DecidableRel (graph e).Adj` instance by the same recursion;
20 one-line `rfl` equation lemmas (`@[simp]`), so no proof simps with a
pattern-matching definition; `Valid` (leaf ids `Nodup` + `opsOk`) and
`ValidFor e G` (adds `verts e = univ`, `graph e = G`). Structural facts, all
proved: `mem_verts_iff` / `verts_eq_toFinset` (vertex set = leaf-id set),
`cls_subset_verts`, `exists_mem_cls`, `verts_eq_biUnion_cls` (classes cover),
`cls_unique` + `cls_disjoint` (classes partition, from leaf-distinctness),
`verts_disjoint` / `Valid.disjoint` (**⊕-side disjointness**),
`mem_verts_of_adj` (edges stay inside `verts`), `sep_union` (the `Glue.sep`
shape verbatim, over `Set` coercions), and the sub-validity lemmas
`Valid.left/right/of_addEdges/of_relabel/ne`. Smoke test first, per house
discipline: `pathExpr : Expr 3 2` for the path 0—1—2, with `#guard`s on
`leafIds`, `verts = univ`, both label classes, `opsOk`, the **decided edge
set** `{(0,1),(1,0),(1,2),(2,1)}`, and that `relabel 1 0` merges the classes
and changes no edge. `lake build` green (2990 jobs), no `sorry`, no new
warnings; `#print axioms` on five main lemmas = propext, Classical.choice,
Quot.sound.
Cost: the smoke test passed on the first elaboration (the `decide`d edge set
caught nothing — the `relabel` if-order below was fixed while writing);
everything green in three diagnostic rounds; longest proof is `cls_unique`'s
relabel case at ~25 lines, everything else under 10.
Next: M9 — Q4b, the op congruences (C13), starting with `typ_disjUnion` as the
`c = 0` instance of `typ_union_congr`: feed it `Valid.disjoint` (for `interX`/
`interY`, vacuous at the empty overlap) and `sep_union` (for `Glue.sep`), with
`X := ↑(verts e₁)`, `Y := ↑(verts e₂)`, `A i := ↑(cls _ i)`.
Decisions: (1) **`Finset`, not `Set`, in the evaluator.** `verts`/`cls` are
`Finset (Fin n)`, which is what makes `graph e` decidable and the whole smoke
test `#guard`able (a genuine edge-set check, not a hand-simp). M9/M10 consume
them through `↑` coercions — `typ` wants `Set (Fin n)`; `sep_union` is already
stated in coerced form to show the friction is nil. If M9 finds the coercions
annoying, the fix is Set-level restatements *added* here, not a change of
definition — computability of the surface object is worth more.
(2) **The evaluator is four recursions, not one tuple-valued `eval`.** Plan
C12 writes `eval e = (X, H, lab)`; splitting it gives one clean equation lemma
per function and no projection noise, and the concept-surface copy at M11 is
just as auditable (~45 lines of definitions). Flagging it as a deviation in
presentation only.
(3) **`i ≠ j` for `addEdges` lives in validity (`opsOk`), not in the
constructor.** A proof field in the inductive would infect every `Expr`
literal and the encoding at M12. Nothing in the mathematics needs `i ≠ j`
(the η congruence will hold for `i = j` too); it is there for fidelity to the
standard definition of clique-width, so that the surface does not silently
claim a larger class of graphs. `Valid.ne` extracts it.
(4) **`relabel i j` tests `t = j` before `t = i`**, so that `relabel i i` is
the identity rather than the class-erasing operation the other order would
give. Cheap and worth keeping in any surface copy.
(5) `sep_union` needs **no** validity hypothesis — a `⊕` adds no edges, so the
separation is unconditional; only the disjointness clause of `Glue` uses
leaf-distinctness. Slightly fewer hypotheses to carry at M9 than expected.

**Orchestrator gate (after session 12): approved, all five.** The
as-built shape (Finset evaluator, four recursions + `opsOk`, `i ≠ j`
in validity, `relabel i i` = identity) *is* the C12 object now —
presentation amendments, no rev bump; M11's surface copy is verbatim
the as-built `CliqueExpr` definitions, ~45 lines. If M9 wants
Set-level restatements they are added lemmas, never definition
changes. Proceed to M9.

## Session 13 — 2026-07-27 ~23:55 UTC
Milestone: M9 — Q4b (the op congruences, C13) — done
Commits: fc4080a "Courcelle Q4b: the op congruences"
State: `ram-linear-time/proofs/Lax11Proofs/MsoCliqueOps.lean` (582 lines, imported
from `Lax11Proofs.lean`; imports `MsoComposition` + `CliqueExpr`). Frozen files
untouched — `CliqueExpr.lean` did not need even the permitted added lemmas, the
two `Set`-level restatements went in the new file. Namespace
`Lax11Proofs.MsoTypes` for everything general about `typ` (it would belong in
`MsoTypes.lean` if that were not frozen; the docstring says so, as session 10 did
with `typ_succ_congr`), and a closing `Lax11Proofs.CliqueExpr` block for the four
bridging lemmas. Contents, in the brief's order:
(1) `typ_disjUnion` — the `c = a = b = 0` instance of `typ_union_congr`, exactly
as session 12 spelled it out: the two `Glue`s are built inline from
`Set.disjoint_left` (the two overlap clauses) and `Fin.elim0` (the four mark
clauses and the overlap pattern), `sep` is passed through verbatim. **17 lines,
statement included**; the pivot's core claim is confirmed.
(2) `typ_setRemap` for `f : Fin s' → Finset (Fin s)`, `A' j = ⋃ i ∈ f j, A i`,
via `setRemap`/`liftLastF`/`setRemap_snoc` (the set-side counterpart of
`snoc_comp_liftLast`); instances `typ_relabel` (through `relabelSets`/`relabelF`,
the exact shape of `cls (.relabel i j e)`) and `typ_forgetAll` (`s' = 0`).
(3) `typ_addEdges`, over `addEdgesG G A i j := G ⊔ SimpleGraph.fromRel (· ∈ A i ∧ · ∈ A j)`
— **no hypothesis beyond equality of the types**, in particular no `i ≠ j` and
no marks-in-`X`. All the work is `Atomic.of_addEdges` (10 lines): the new
adjacency is `adj ∨ (¬eq ∧ (mem i ∧ mem j ∨ …))`, three atoms the diagram
already carries.
(4) `typ_singleton` — general mark tuple all of whose entries are the vertex
(that is what the vertex move produces); the set move maps `S ⊆ {v₁}` to
`if v₁ ∈ S then {v₂} else ∅`.
Plus `typ_congr_edges` and the bridge: `Valid.disjoint_coe`, `graph_addEdges_eq`
(`rfl`), `cls_relabel_eq`, `typ_graph_union_left`/`_right`. Non-vacuity anchor:
the outer `⊕` of `pathExpr` satisfies the disjointness hypothesis, by
`Valid.of_addEdges … |>.disjoint_coe` with `Valid pathExpr` by `decide`.
`lake build` green (2991 jobs), no `sorry`, no new warnings; `#print axioms` on
all seven main results = propext, Classical.choice, Quot.sound.
Cost: three compile rounds, no approach abandoned. Every one of the four is the
same q-induction skeleton as `typ_comp_congr` (diagram + `vstep` + `sstep`), so
the proofs are transcription, not invention; the longest is `typ_setRemap` at 60
lines including its restated hypothesis block, the shortest `typ_disjUnion` at
17. Set-move hypothesis restatement is again where the volume is (session 10's
measurement holds), but the identity vertex sets mean there is no re-indexing
anywhere.
Next: M10 — Q4c, the table and the main induction. The interfaces line up:
`typeOf e := typ q ↑(verts e) (Fin.elim0) (fun i => ↑(cls e i))`; the `⊕` case is
`typ_graph_union_left`/`_right` to move the children into the parent's graph,
`typ_congr_inter` to move the children's set parameters from `cls e₁`/`cls e₂` to
`cls (union e₁ e₂)` (they agree inside each child's vertex set, which is exactly
that lemma's hypothesis), then `typ_disjUnion` fed `Valid.disjoint_coe` +
`sep_union`; the `η` case is `graph_addEdges_eq` + `typ_addEdges`; the `ρ` case is
`cls_relabel_eq` + `typ_relabel`; the leaf is `typ_singleton`; the root corollary
is `typ_forgetAll` + `satIn_congr`.
Decisions: (1) **"typ depends only on edges within X" is NOT implicit in M4** —
the plan's open question, answered. `Atomic.of` reads `G.Adj (m i) (m j)` for a
mark tuple that `typ` never requires to lie in `X`, so the statement is simply
false without `∀ i, m i ∈ X`. With that hypothesis it is the same cheap
induction: `typ_congr_edges` (16 lines) plus the instance `typ_sup_of_avoids`.
Both are general facts about `typ`, so they are M11-surface-irrelevant but
MsoTypes-shaped; flagged in the file's docstring for whoever un-freezes.
(2) **`typ_addEdges` needs no `i ≠ j`**, confirming session 12's decision (3)
from the other side: validity carries it for fidelity to the standard definition
of clique-width, and nothing in the mathematics wants it. Also no marks-in-`X`
hypothesis — the congruence is unconditional.
(3) **`typ_setRemap` is stated with `Finset (Fin s)`, not a `Set` or a
predicate.** The union `⋃ i ∈ f j, A i` needs no decidability and `liftLastF`
uses `Finset.image`; a `Set (Fin s)` index would work equally but `Finset` is
what `relabelF` writes down by `if`-cascade and what a future table-side
enumeration would want.
(4) **The `⊕` case will need `typ_congr_inter` as well as `typ_disjUnion`** —
flagging it now because it is the one plumbing step M10 cannot get from C13: the
children's types are taken with the *children's* label classes as set parameters,
the union's with the union's, and `cls (union e₁ e₂) i ∩ verts e₁ = cls e₁ i`
(from `cls_subset_verts` + `Valid.disjoint`). It is one line per side, but it is
a real step and the plan's C13 list does not mention it.
(5) `Reasoning.lean` untouched; no mathlib-shaped lemma was missing.

**Orchestrator gate (after session 13): clean, proceed to M10.** The
`typ_congr_inter` step in the ⊕ case (decision 4) is accepted as part
of the case plan — it is an existing M4 lemma, not new machinery.
Reminder to session 14: M10 ends at its checkpoint block; the freeze
(M11) is orchestrator-gated, do not start it.

## Session 14 — 2026-07-28 ~01:10 UTC
Milestone: M10 — Q4c (the table, the main induction) — done, in one session
Commits: a410ef3 "Courcelle Q4c: the type table, and the main induction"
State: `ram-linear-time/proofs/Lax11Proofs/MsoTable.lean` (618 lines: 330 code,
207 docstring, 81 blank), namespace `Lax11Proofs.MsoTable`, imported from
`Lax11Proofs.lean`; imports `MsoCliqueOps` + `TreeFold` — **this is the first
file that imports both workstreams**, which is what C14 is. No committed file
was edited except the import line. Full `lake build` green (2992 jobs), no
`sorry`, **no new warnings**; `#print axioms` on all eleven main results =
propext, Classical.choice, Quot.sound. Contents, in order:
(1) `Op k` (`union`/`leaf l`/`eta i j`/`rho i j`), the **computable** code
`Op.code` (blocks `0` | `1+l` | `1+k+(i·k+j)` | `1+k+k²+(i·k+j)`), its
computable inverse `Op.decode`, `Op.decode_code`, `Op.code_lt`,
`opCard k = 1+k+2k²` (= the fold's `Table.L`).
(2) `Val q k` = `done (t : T q 0 k)` | `unionEmpty` | `unionLeft t` |
`etaWait i j` | `rhoWait i j`, `deriving DecidableEq, Fintype` (it just works,
`instFintypeT` is found); `enc`/`dec` by `Fintype.equivFin` with `dec_enc`.
(3) `Inst`/`UInst` (a region, resp. two disjoint mutually non-adjacent regions
of one ambient graph, label classes as set parameters) and the three table
entries `etaVal`/`rhoVal`/`unionVal` by `dif` on "∃ a realization of this
type", with `etaVal_ty`/`rhoVal_ty`/`unionVal_ty` — **6, 6 and 9 lines**, each
one `congrArg Val.done` applied to `typ_addEdges`/`typ_relabel`/
`typ_disjUnion` at `h.choose_spec`. `leafType` needs no choice at all.
(4) `initV`, `stepV` (four meaningful cases, all four equations `rfl`),
`table q k : Table`, `table_wf` (**2 lines** — the partial states are
inhabitants of `Val`, so `V` counts them and closure is `enc_lt`).
(5) `typeOf q e := typ (graph e) ↑(verts e) q Fin.elim0 (fun i => ↑(cls e i))`
and the four case lemmas.
(6) `EncExpr par lab i e` (10 lines) and **`val_eq_typeOf`**: for `Valid e`
and `EncExpr par lab i e`, `val (table q k) par lab i = enc (.done (typeOf q e))`.
(7) The root: `sat_congr_typeOf` (equal root types ⟹ same rank-≤q sentences,
via `typ_forgetAll` + `sat_congr_sentence` + `verts = univ` + `graph = G`),
the accepting set `Accepts` with `accepts_typeOf`, and `acceptVal_val` — the
C9 statement the driver cashes in: `acceptVal q k φ (val (table q k) par lab i)
= true ↔ Sat G Fin.elim0 Fin.elim0 φ`.
(8) Smoke test: `pathPar`/`pathLab`, the seven-node parent-pointer tree of
`pathExpr`, with `EncExpr pathPar pathLab 6 pathExpr` proved by `decide`s.
Cost: **two diagnostic rounds**. The first compile had six errors, all trivial
(two `omega`-shaped arithmetic leftovers in `decode_code`, one over-eager
`omega`, one missing explicit `q`); nothing was redesigned and no approach was
abandoned.

### Q4c checkpoint: the table and the induction as built

*Verdict: **green, freeze recommended**. The pivot's promise held exactly.
The main induction is 38 lines — ~8 per constructor — and every case is one
C13 congruence plus `simp only` bookkeeping. Cross-graph plumbing stayed
cheap: it cost two `rw`s, in one case, once.*

*Lines per case* (proof bodies of `val_eq_typeOf`, and the semantic lemma
each consumes):
- **leaf**: induction case **4**, `typeOf_leaf` 6. One `typ_singleton`, with
  the canonical one-vertex graph `(⊥ : SimpleGraph (Fin 1))` as the
  representative. This is the lemma that makes the vertex-id array unread.
- **⊕**: induction case **6**, `typeOf_union` 35 + two `cls_union_inter_*`
  helpers 15 each = **65 — the only case with any volume**, and the whole of
  it is the plumbing session 13 flagged in its decision (4). Breakdown: the
  `UInst` literal 8, `tyL`/`tyR` 6+6 (each = one `typ_congr_inter` + one
  `typ_graph_union_left/right`), `tyU` 4 (`Finset.coe_union`), assembly 1;
  the two helpers are the set identity
  `↑(cls e₁ j ∪ cls e₂ j) ∩ ↑(verts e₁) = ↑(cls e₁ j) ∩ ↑(verts e₁)`, i.e.
  `cls_subset_verts` + `Valid.disjoint`.
- **η**: induction case **6**, `typeOf_addEdges` **4** — and three of those
  four lines are naming the `Inst`; the actual content is `rfl`, because
  `graph (.addEdges i j e)` *is* `addEdgesG (graph e) ↑(cls e) i j` on the
  nose (session 13's `graph_addEdges_eq`).
- **ρ**: induction case **6**, `typeOf_relabel` **5** (`cls_relabel_eq`,
  then `rfl`).
- **root**: `sat_congr_typeOf` 23, `accepts_typeOf` 11, `acceptVal_val` 7.

*Did cross-graph plumbing stay cheap?* **Yes, and cheaper than expected.**
The plan's worry was that a child's type is computed in the child's evaluated
graph while the parent's type lives in the parent's, so every case would owe
a transfer. In the event only `⊕` owes one — `typ_graph_union_left/right`,
already proved at M9, applied with the vacuous `∀ i, m i ∈ X` of the empty
mark pool (`fun i => i.elim0`) — and `η`/`ρ` owe none, because their
evaluated graph/classes are *definitionally* the operation applied to the
child's. Two `rw`s in one case is the entire cost of "the graph varies along
the tree".

*The table by choice: measured.* The C5 device cost **21 lines of proof**
(three correctness lemmas) plus two structures. The dependent ambient size
`n` lives *inside* `Inst`/`UInst`, so the existential quantified over is over
a single structure and `Exists.choose` needs no bundling gymnastics; the
cross-ambient statements of M5/M6/M9 are what make this work — a same-ambient
congruence could not have been lifted this way at all. `Table.Wf` is 2 lines
because the partial states are constructors of `Val`, not a separate alphabet
glued on: the brief's requirement that they count toward `Table.V` is
satisfied by construction rather than by an argument.

*The `Expr`↔encoding correspondence: shape and cost.* A relation, 10 lines:
`EncExpr par lab i e`, by structural recursion on `e`, saying "the op code at
`i` is `e`'s and `children par i` (the schema's own increasing-index list) is
the list of the subexpressions' nodes, left before right". It is stated
against `TreeFold.children`, which is exactly what `val_eq_foldl` unfolds to,
so the induction consumes it with a single `rw [val_eq_foldl, hc]` per case
and *no* fuel, index or ordering reasoning appears anywhere. The literal
`par`/`lab`-array form is **not** deferred in spirit: the op codes are pinned
here as explicit arithmetic with a proved inverse (`Op.decode_code`) and a
proved bound (`Op.code_lt`, i.e. `lab i < Table.L`), and the smoke test
exhibits real arrays satisfying `EncExpr`. What M12 still owes is only the
bridge from an input word to `(par, lab)` — `EncodesTree`'s job, which it
already does — plus the two facts `EncExpr` deliberately does not carry:
`par c > c` and `root = N-1` (needed by `sweep_eq_val`, not by `val`).
Recommend M12 state `EncodesInstance` as `EncodesTree` ∧ `EncExpr par lab (N-1) e`
∧ `ValidFor e G`; nothing else is missing.

*Readiness for the surface freeze: ready.* The three objects the freeze
copies out are untouched by this milestone and were consumed exactly as they
stand: `MSO`/`rank`/`Sat` appear only in the root corollary, in the sentence
form `Sat G Fin.elim0 Fin.elim0 φ`; `Expr`/`verts`/`cls`/`graph`/`Valid`/
`ValidFor` appear only through `Valid.left/right/of_addEdges/of_relabel`,
`Valid.disjoint`, `ValidFor.verts_eq/graph_eq` and the 20 `rfl` equation
lemmas. **`CliqueExpr.lean` needed no added lemma this session either** — M9
and M10 both got through on what M8 shipped, which is the strongest evidence
the surface shape is right. The one surface-visible number the freeze must
carry is `opCard k = 1 + k + 2k²` and the code layout, since they are the
input format; `Op`/`Op.code`/`Op.decode` are ~20 lines and are the natural
fourth block of `concepts/Lax11/CliqueExpr.lean` (or of `Courcelle.lean`,
where `EncodesInstance` will read them) — **orchestrator's call at M11**.

Next: M11 — the surface freeze, **on the orchestrator's green only** (not
started, `concepts/` untouched). Then M12 with the plumbing above.
Decisions: (1) **The op codes are computable arithmetic, the value numbering
is not.** `Fintype.equivFin` would have given a uniform two-line numbering for
both alphabets, but the label alphabet is *in the input word*: a reader of
`EncodesInstance` must be able to say that `η 0 1` at `k = 2` is the number
`4`. So `Op.code`/`Op.decode`/`Op.decode_code` (≈45 lines with the four
arithmetic helpers) buy an auditable input format; the values, which nobody
writes down, stay noncomputable per C5.
(2) **`EncExpr` is a relation, not an `Expr`-indexed `val`.** The brief
allowed either. The relation is 10 lines, is stated in `children` (so it is
literally what `val_eq_foldl` needs), and — unlike an `Expr`-level `val` —
it is *also* what M12 must produce anyway, so nothing is proved twice.
(3) **The accepting set is an existential, not a choice.** `Accepts q φ t :=
∃ a valid expression of type t whose graph satisfies φ`; `accepts_typeOf` is
11 lines and its forward direction is exactly `sat_congr_typeOf`. This keeps
C9 free of a second choice and gives M12 a membership test rather than a
function to invert.
(4) **`stepV`'s junk cases answer `unionEmpty`, not a `default`.** A
`default : T q 0 k` would need an `Inhabited` instance for the type algebra
(provable, but a noncomputable instance on a frozen-file-shaped object);
routing junk to a partial state costs nothing and keeps `MsoTypes.lean`'s
API untouched.
(5) `Reasoning.lean` untouched; no mathlib-shaped lemma was missing; the four
`Fin`/`Nat` arithmetic helpers (`div_lt_sq`, `pos_of_lt_sq`, `mod_lt_sq`,
`pair_lt`, `div_pair`) are private and local to the code arithmetic.

**Orchestrator gate (after session 14): M10 checkpoint GREEN — the
freeze is authorized. M11 decisions:**
(1) `Op`/`Op.code`/`Op.decode`/`opCard` go in
`concepts/Lax11/CliqueExpr.lean` as the fourth block — the code
layout is part of the expression object's serialization, and
`Courcelle.lean` stays statement-only.
(2) `EncodesInstance` keeps C14's explicit leaf vertex-id array: the
input literally is a k-expression (deterministic decode), the honest
"given a k-expression" form; the program never reads it — ledger
line, and the surface relation ties ids at leaves. The surface
predicate must be self-contained in `concepts/` (no proofs imports):
restate the tree layout in `EncodesGraph`'s style and a surface-level
expression↔arrays relation (EncExpr's shape plus the id clause).
(3) After copying, the proofs drafts (`Lax11Proofs` Mso + CliqueExpr
definitions) switch to aliases/re-exports of the surface definitions
— verbatim identity makes this mechanical — so M12's discharge is
about the *surface* statement with M8–M10 compiling unchanged.
Session-14 decisions (1)–(5) all approved as-is.

## Session 15 — 2026-07-28 ~02:40 UTC
Milestone: M11 — step 5, the surface freeze — done
Commits: 93740a2 "Courcelle step 5: the surface freeze"
State: Three new files in `concepts/Lax11/`, imported from `Lax11.lean`
(which gained three import lines — the library root, not one of the four
frozen files, which are untouched):
- `Mso.lean` (100 lines, 45 of definition): `MSO r s` (seven
  constructors), `rank`, `Sat` — **verbatim** from the proofs draft, in
  namespace `Lax11.Mso`, docstring rewritten in the surface voice.
- `CliqueExpr.lean` (206 lines, ~110 of definition): `Expr`, `leafIds`,
  `verts`, `cls`, `graph` + the `DecidableRel` instance, `opsOk`,
  `Valid`, `ValidFor` verbatim, then per gate decision 1 the fourth
  block `Op` / `Op.code` / `opCard` / `Op.decode` (with the three
  `private` arithmetic side conditions `Op.decode` needs to typecheck).
  Definitions only, no theorems.
- `Courcelle.lean` (154 lines): `nodeCount`/`parent`/`opCode`/
  `vertexName` in `EncodesGraph`'s `List.getD` style, `children`,
  `EncodesExprTree` (six fields: node count, `1 ≤ N`, `length = 1+3N`,
  children-before-parent, op codes `< opCard k`), the surface relation
  `EncodesExpr par lab ids i e` (`EncExpr`'s shape plus `ids i = ↑v` at
  leaves), `EncodesInstance x n G k := ∃ g t N e, x = g ++ t ∧
  EncodesGraph g n G ∧ EncodesExprTree t N k ∧ EncodesExpr … (N-1) e ∧
  ValidFor e G`, and the axiom
  `Lax11.Courcelle.exists_linearTime_program_modelChecking` in exactly
  the plan's C0 rev-5 form (`MSO 0 0`, `ComputesInTime`,
  `c * (x.length + 1)`, `[1]`/`[0]`; `open Classical in` for the `if`).
Both packages green (`concepts` 821 jobs, `proofs` 2996), no `sorry`,
**no new warnings** (the nine `unusedSimpArgs` in Reasoning/CCPhases/
CCSweep are the pre-existing ones), `lax build ram-linear-time` **OK**.
`#print axioms` on `val_eq_typeOf`, `acceptVal_val`, `Op.decode_code`
and the new `encodesInstance_instanceWord` = propext, Classical.choice,
Quot.sound.

*The sanctioned proofs-side switch, exactly* (four committed files):
- `Lax11Proofs/Mso.lean` (−75/+34): `import Lax11.Mso` added; the
  `inductive MSO`, `def rank`, `def Sat` blocks deleted and replaced by
  one `export Lax11.Mso (MSO MSO.adj MSO.eq MSO.mem MSO.not MSO.and
  MSO.exV MSO.exS rank Sat)`; module docstring updated. Everything else
  (the seven `rank_*` simp lemmas, `SatIn` + its simp lemmas,
  `satIn_univ`, the four smoke `example`s) unchanged.
- `Lax11Proofs/CliqueExpr.lean` (−134/+50): `import Lax11.CliqueExpr`;
  the nine definitions deleted, replaced by two `export`s (the object,
  and the op-code block); five new `rfl` equation lemmas
  (`Op.code_union/leaf/eta/rho`, `opCard_eq`) added to the equations
  section; docstring updated. The 20 old equation lemmas, all structural
  facts, all `Valid.*` lemmas and the `pathExpr` smoke test unchanged.
- `Lax11Proofs/MsoTable.lean` (−85/+21): the `Op` block deleted
  (`inductive Op`, `Op.code`, `opCard`, `Op.decode`, and the three
  private helpers `div_lt_sq`/`pos_of_lt_sq`/`mod_lt_sq` that moved to
  the surface with `decode`); `pair_lt`, `div_pair`, `Op.decode_code`,
  `Op.code_lt` stay, with `simp only [Op.code, opCard]` → the new `rfl`
  lemmas; six dot-notation call sites de-sugared (below); two docstring
  paragraphs updated.
- `Lax11Proofs/MsoCliqueOps.lean` (4 lines): four dot-notation call
  sites de-sugared. Nothing else; `Valid.disjoint_coe` and the four
  bridging lemmas are unchanged in content.
New: `Lax11Proofs/CourcelleSmoke.lean` (136 lines), imported from
`Lax11Proofs.lean`.
Cost: the concepts package was green on the first compile; the proofs
side took four rounds, all of them the two mechanical issues below.
Next: M12 — Q6, the driver. The bridge it owes is now visible: from
`EncodesInstance x n G k` produce `TreeFold.EncodesTree` for the
expression block (the surface block has *three* arrays where
`EncodesTree` has two, and the word is `csr ++ t` rather than `t`, so
M12 either generalizes `EncodesTree` or reads the block directly) plus
`MsoTable.EncExpr` from `Courcelle.EncodesExpr` — the two relations are
the *same* recursion up to the extra `ids` clause and the two `children`
definitions are syntactically identical, so the forgetful direction
should be a structural induction of ~10 lines. Then the accept-bit
epilogue and `acceptVal_val`.
Decisions: (1) **`export` does not carry dot notation, and that is what
the switch actually cost.** `export Lax11.CliqueExpr (Valid)` makes
`Valid` resolve, but `h.left` for `h : Valid …` looks up
`Lax11.CliqueExpr.Valid.left`, which does not exist — Lean's
`findMethod?` never consults aliases. Likewise `MSO.adj` as an explicit
name fails unless the *constructors* are exported too (they now are, for
both `MSO` and `Expr` and `Op`). The two ways out were (a) exporting the
helper lemmas back into `Lax11.CliqueExpr` from the proof package, which
puts proof-package names in the concept namespace — the standing watch
item — or (b) writing the ten affected call sites as `Valid.left hv`
instead of `hv.left`. I took (b): `h.disjoint` ×3, `h.disjoint_coe` ×4,
`hv.left`/`hv.right`/`hv.of_addEdges`/`hv.of_relabel` ×1 each, across
`MsoCliqueOps.lean` (4) and `MsoTable.lean` (6). So M9/M10 did *not*
compile literally unchanged — ten lines, no content, listed above. Field
and parent projections (`h.nodup`, `h.ops`, `h₁.verts_eq`, `hv.toValid`)
and anonymous constructors are unaffected.
(2) **The splitter leakage the guardrails warn about is real, and `lax`
catches it.** `simp only [Op.code, …]` in `Op.decode_code` generated
`Lax11.CliqueExpr.Op.code.match_1.splitter` inside the proof package and
`lax build` rejected it by the namespace rule. Fixed the house way:
`Op.code_union/leaf/eta/rho` and `opCard_eq` as `rfl` lemmas in
`Lax11Proofs.CliqueExpr`, and the note is now in that file's docstring
so the next person does not rediscover it. Nothing else in the two
packages unfolds a concept definition by `simp`.
(3) **At most one module docstring per concept file.** `lax` rejects
`/-! ### … -/` section headers in `concepts/` (five in `CliqueExpr`,
three in `Courcelle` on the first attempt). The new files therefore have
one front docstring and no section headers, which is also what the four
frozen files look like.
(4) **`EncodesInstance` splits the word as `x = g ++ t`** rather than
indexing one word by absolute offsets. `EncodesGraph` already pins its
own length from its header, so the split is unique and the CSR block is
reused verbatim instead of being restated with a base offset. The
expression block's own accessors are then offsets into `t`, which is
what makes the file readable; the driver pays for it by computing the
block boundary as `3 + n + 2m` from the first two entries, which it must
read anyway.
(5) **No `parent (N-1) = N-1` clause.** Session 11's decision 2 demanded
it for `TreeDecomp`, which the pivot sunk; nothing in the fold reads the
root's parent entry (`children` only looks below `i`), so requiring it
would only shrink the admissible input set. The root is pinned instead
by *rooting the expression relation at `N-1`*, which is where the plan's
"root `N−1`" belongs. The smoke test's array happens to be self-parented
at the root, so a driver may still produce that shape.
(6) The surface relation is named `EncodesExpr` (not `EncExpr`) and the
axiom `exists_linearTime_program_modelChecking` (in the style of
`exists_linearTime_program_ccLabels`); the plan's `courcelle` was a
sketch name, and the concept namespace `Lax11.Courcelle` already carries
the attribution.
(7) `Reasoning.lean` untouched; the four originally frozen concept files
untouched (verified by `git diff`); `TreeDecomp.lean` still idles.

**Orchestrator gate (after session 15): freeze verified, proceed to
M12.** Commit 93740a2 audited: the four original concept files are
absent from the diff; the proofs-side switch matches the sanctioned
list exactly. The dot-notation de-sugaring (decision 1, option b) is
the right call — proof-package names never enter the concept
namespace. The splitter leakage on `Op.code` (decision 2) confirms
the house rule extends to the new surface: proofs-side `rfl` equation
lemmas are now the standing pattern for all three new concept files.
From here `concepts/` is FULLY frozen — all seven files; M12/M13 are
proofs-only.

## Session 16 — 2026-07-28 ~07:10 UTC (system clock reads 2026-07-27)
Milestone: M12 — Q6, the driver — **done, in one session, not split**
Commits: 25daa9c "Courcelle Q6: the driver, the program and the bridges";
20937f6 "Courcelle Q6: the theorem, cashed in at the concept surface"
State: Two new files, both imported from `Lax11Proofs.lean` (the only
committed file touched — two import lines), namespace `Lax11Proofs.Courcelle`.
`concepts/` untouched (verified: absent from both diffs).
- `CourcelleDriver.lean` (309 lines): `driverCom T acp` — the schema's program
  with the instance word's front end (`.read "n"`, `.read "m"`, `len := n+1+2m`,
  `readLoop "csr" "len"`, `.read "N"`, `readLoop` × 3 for `par`/`lab`/`ids`,
  the four `stores` prologues, `seedLoop`, `pushLoop`) and the C9 epilogue
  `.write (.get "acp" (.get "acc" (.sub (.var "N") (.lit 1))))`; `layout`
  (7 scalars, 9 arrays, 4 temps), `driverProgram`, `driverCom_ok`,
  `driverExt`; the two bridges — `encExpr_of_encodesExpr` (**7 lines**, the
  `children`s are `rfl`-equal, `children_eq` says so) and `instance_tape`
  (the word decomposed into `n :: m :: (gr ++ N :: tr)` with all the fold's
  hypotheses, ~45 lines) plus `getD_take`/`getD_drop`; and the smoke test.
- `CourcelleMain.lean` (343 lines): `driverCost T = 3*(L+V+V²+V)+60`,
  `driverCom_run` (the fifteen phases in a row, `K ≤ 100*(|x|+1) + driverCost T`),
  `const_eq : layout.const = 46`, `acpArr`, and
  **`exists_linearTime_program_modelChecking`** with the conclusion
  frontmatter, witness `driverProgram (table (rank φ) k) (acpArr (rank φ) k φ)`
  and constant `46 * (100 + driverCost (table (rank φ) k))`.
Full `lake build` green (2998 jobs), no `sorry`, **no new warnings** (the nine
`unusedSimpArgs` are the pre-existing ones); `lax build ram-linear-time` **OK**,
`build-output.json` records the proof of
`Lax11.Courcelle.exists_linearTime_program_modelChecking` with `assumptions: []`.
`#print axioms` on the theorem, on `driverCom_run` and on `instance_tape` =
propext, Classical.choice, Quot.sound (`encExpr_of_encodesExpr` needs none).
No-drift check (run in scratch, not committed, so that the proof package does
not reference the axiom): `example : Lax11.Courcelle.exists_… = Lax11Proofs.Courcelle.exists_… := rfl`
elaborates — `Eq` forces the two types to be defeq, proof irrelevance closes it.
Cost: three diagnostic rounds for the driver file, two for the main file; no
approach was abandoned and no lemma of M1–M11 was restated or amended.
Next: M13 — discharge + wrap-up (Q7). Nothing is owed to it by this milestone
beyond the ledger lines listed in the brief; two new ones are below (decisions
2 and 3).
Decisions: (1) **The block is read directly; `EncodesTree` is not generalized.**
The surface expression block has three arrays where `EncodesTree` has two, and
the word is `csr ++ t`, so a generalized `EncodesTree` would have had to grow a
base offset and a third array and would then be used exactly once. Instead
`instance_tape` produces the tape segments (`gr`, `tr.take N`,
`(tr.drop N).take N`, `tr.drop (N+N)`) and the two functions `par := tr.getD ·`,
`lab := tr.getD (N + ·)` directly, and the phase lemmas of M2 — which speak
about *arrays*, never about the word — consume them unchanged. `EncodesTree`
and `foldCom_run` stay as the schema's own theorem, untouched.
(2) **Read-and-discard is a `readLoop` into a junk array**, not a new
skip-loop command: `csr` (extent `n+1+2m`) and `ids` (extent `N`) are read
into arrays that no expression in the program ever mentions again. This
reuses `readLoop_run` verbatim — zero new `Run` lemmas — at the price of two
array names in the layout, i.e. of `layout.const` being 46 rather than 40.
Loose constants everywhere, as instructed. *Ledger line for M13*: the program
reads the whole input word (it must, to find the expression block) but uses
only the expression block's parent and op-code arrays.
(3) **The `#eval` check runs a computable stand-in table, and it cannot run
the real one.** `table q k` is noncomputable by construction (C5: choice), and
so is `acceptVal`; the machine-vs-model check therefore instantiates the
*generic* `driverCom T acp` with `edgeTable`, a hand table over the **same**
op alphabet, decoded by the **same** `Op.decode`, whose values are the three
bits "class 0 nonempty", "class 1 nonempty", "there is an edge", plus the
partial states the sequential fold needs — a genuine clique-width dynamic
program. The two sentences are therefore "some two vertices are adjacent"
(true on the path, machine writes `[1]`) and its negation (`[0]`), rather
than the brief's edge-existence/triangle pair: a triangle is not decidable
from three bits, and a state big enough for it would put `V²` table entries
into every `#eval` of the build. The run is 4.3 s of build time; a table with
`V = 89` would have been ~10× that.
(4) The smoke test is joined to the mathematics by a `#guard` that the
`parent`/`opCode` accessors on `CourcelleSmoke.exprBlock` agree with
`MsoTable.pathPar`/`pathLab` on all seven nodes — session 7's decision 4 as
standing practice; without it the machine run and the model run are joined
by nothing but the reader's eye.
(5) `Reasoning.lean` untouched; no mathlib-shaped lemma was missing. The only
new generic-looking items are `getD_take` and `getD_drop`, which are two
`simp only`s each and are kept local to the driver file.
(6) The theorem takes `q := rank φ`, so the table is as small as the statement
allows; `acceptVal_val`'s `rank φ ≤ q` is `le_rfl`.

**Orchestrator gate (after session 16): M12 accepted, all six
decisions approved.** The stand-in-table `#eval` (decision 3) is the
correct reading of the house discipline under C5 — the machine run
exercises the entire program text through the same `Op.decode`; the
real table's content is exactly what the proof carries. Ledger lines
for M13 confirmed: reads-whole-word-uses-two-arrays, the stand-in
rationale, and (from the day's Q&A) that the machine has add/sub
only — no multiplication anywhere, table indexing strength-reduced
to the `row` lookup array, so the theorem is honest even under a
strict word-RAM reading. TreeDecomp disposition: orchestrator
recommends KEEP as bonus theory (self-contained, green, feeds a
future treewidth submission) — final argument to be written at M13.
Proceed to M13.

## Session 17 — 2026-07-28 ~09:30 UTC
Milestone: M13 — discharge + wrap-up (Q7) — done. **The relay is finished.**
Commits: 12e83e7 "Courcelle Q7: the wrap-up — the honesty of the theorem"
State: No Lean was touched. Four files committed: new
`ram-linear-time/notes.md` (250 lines), `abstract.md`, `manifest.yaml`,
`courcelle-plan.md` (rev 6). `NIGHTLOG.md`, `asdf`, `cc-night-brief.md` left
unstaged; `concepts/` and every committed proofs file untouched (verified by
`git status` before staging).

*Audit — all green, nothing papered over.*
- `lake build`: concepts 821 jobs, proofs 2998 jobs, both successful, no
  `sorry`, no new warnings (the nine `unusedSimpArgs` in Reasoning/CCPhases/
  CCSweep are the pre-existing ones). Caches were not deleted, per instruction.
- `lax build ram-linear-time` **OK**; `lax build ram-linear-time --replay`
  **OK** (the replay is supported and was run; kernel-replays both packages).
  `build-output.json` records **two** proofs — `exists_linearTime_program_ccLabels`
  and `exists_linearTime_program_modelChecking` — each with `assumptions: []`,
  and seven concepts.
- `#print axioms` (via `lake env lean` on a scratch file, not committed) =
  propext, Classical.choice, Quot.sound on
  `Lax11Proofs.Courcelle.exists_linearTime_program_modelChecking` and on six
  further results: the three spot-checks asked for —
  `MsoTypes.typ_union_congr` (composition), `MsoTypes.satIn_congr` (adequacy),
  `MsoTable.val_eq_typeOf` (the main induction) — plus
  `MsoTable.acceptVal_val`, `TreeFold.sweep_eq_val` and
  `CCMain.exists_linearTime_program_ccLabels`. The no-drift `example`
  (`Lax11.Courcelle.exists_… = Lax11Proofs.Courcelle.exists_… := rfl`) still
  elaborates, re-run in the same scratch file.
- Post-edit re-run of `lax build ram-linear-time` after the abstract/manifest
  changes: OK (the manifest's new keys are only `title` text and `bibEntries`).

*The formalization notes.* All eleven ledger items are written, each as an
argued paragraph or two, in `ram-linear-time/notes.md`: MSO₁ scope with
MSO₂+treewidth deferred as one unit (and *why* "by the same argument" would be
a false claim); the well-scoped de Bruijn family and what capture-avoiding
substitution would cost *on the trust surface*; the noncomputable table and the
∃-program shape of the statement; the cliquewidth pivot, the unformalized
tw→cw conversion and Oum–Seymour out of scope, at the status Bodlaender had;
expression-as-certificate with the whole word read but only `par`/`lab` used;
children-before-parent as an encoding restriction and not a class restriction;
add/sub only with table indexing strength-reduced to the materialized `row`
array; the `#eval` stand-in table (`edgeTable`) with an exact statement of what
it does and does not establish; the tower, paid once and never estimated;
`TreeDecomp.lean` KEEP with the argument; and a closing item naming de Bruijn
positions as *the* single non-textbook device a reviewer must translate.
I checked every session block for anything else flagged "ledger" — sessions 7,
12, 15, 16 and the two orchestrator gates — and found no twelfth item; the
`stepList`-is-`V²` point from session 7 is folded into the tower paragraph, and
the splitter-leakage rule from session 15 is a house build convention, not an
honesty item, so it stayed in the file docstrings where it is actionable.

*Abstract and manifest.* Abstract rewritten to the grown submission in its own
voice: two theorems in the opening, seven review units (five definitions, two
theorems) in the surface paragraph, the RAM/compiler/reasoning-kit tower and
the CC paragraph unchanged in substance, then two new paragraphs — the
Ehrenfeucht–Fraïssé engine (composition at every rank, cross-ambient, the four
ops uniform, table by finiteness and choice) and the generic fold with its
`row`-array indexing, the epilogue, and the tower paid before the input is
read. Manifest title is now "Connected Components and Courcelle's Theorem in
Linear Time on a Random Access Machine"; four bib entries added (Courcelle
1990, Courcelle–Olariu 2000, Courcelle–Makowsky–Rotics 2000, Oum–Seymour 2006).
Next: nothing in the plan. Outward-facing and Jan's: `lax submit`.
Decisions: (1) **The notes are a new root-level `notes.md`, not a docstring.**
The brief said "extend Lax11's existing notes document"; there is none — the
house pattern puts `# Formalization notes` in concept module docstrings and
extra `#` sections in proof annotations (session 3 did exactly that for CC),
and *both* were closed to me: `concepts/` is fully frozen since M11 and
committed proofs files are off limits at M13. The archive spec allows files
beyond the layout and ignores them, so `notes.md` is admissible but **not
rendered on the submission page**. That is the one cost, and it is Jan's call
to fix in a minute if he wants it rendered: the natural home is a
`# Formalization notes` section appended to the theorem annotation in
`CourcelleMain.lean`, which is exactly the shape session 3 used for CC, and the
text is written to drop in unchanged. I did not do it myself because it is an
edit to a committed proofs file.
(2) **The abstract does not absorb the ledger.** Eleven argued items would have
tripled it and broken the length discipline the existing abstract keeps; the
abstract states the two theorems and the route, names the two honesty points a
reader cannot do without (the tower is never estimated; the expression is
input), and points at the notes for the rest.
(3) **`TreeDecomp.lean` kept**, per the orchestrator's recommendation, with the
argument written out: mathlib-only, green, imported by nothing, and stated in
the machine's own `par : ℕ → ℕ` shape, so a future MSO₂/treewidth submission
inherits its whole combinatorial layer. The note exists so no reviewer hunts
for the place it is used.
(4) The plan is rev 6: header paragraph, ✅ + session/checkpoint pointer on each
step (Q3 → sessions 5–7, Q1 → 8–10, Q2a → 11, Q4 → 12–14, freeze → 15, driver →
16, wrap-up → 17), and an appended "Final state" section. Rev 5's text is
untouched — no history was rewritten. The night briefs were not edited.
(5) Constants for the record: the Courcelle theorem's is
`46 * (100 + driverCost (table (rank φ) k))` with
`driverCost T = 3*(L+V+V²+V)+60`, `layout.const = 46`; CC's is 2604. Neither is
estimated further, and the notes say why the first cannot be.

**Orchestrator close-out — 2026-07-28.** The relay is finished:
sessions 12–17, six milestones, six green single-session landings, no
split, no stuck report, no abandoned approach.
`Lax11.Courcelle.exists_linearTime_program_modelChecking` is proved
(assumptions: [], standard three axioms, replay clean). The rev-5
pivot's ledger, plan rev 6, abstract and manifest are committed
(12e83e7). Open for Jan: (1) `lax submit` — outward-facing, his call,
covers the grown single submission per C8; (2) the notes.md placement
question (session 17 decision 1): the ledger text is written to drop
verbatim into `CourcelleMain.lean`'s conclusion annotation if he
wants it rendered, which would touch a committed proofs file — his
call; (3) TreeDecomp.lean kept as bonus theory per the M12 gate note,
argued in notes.md item 10.

**Orchestrator — 2026-07-28: cleanup pass (Jan's request, in
session).** Scope: improve the submission as reviewers see it.
Targets, in priority order: (1) surface code polish in the three
Courcelle concept files (decidableAdj boilerplate, Op.decode's three
private lemmas, optionally the redundant ∃ N in EncodesInstance) —
semantic-preserving, ripple proof work sanctioned; (2) the ledger
moves to where it renders — theorem-adjacent items into
CourcelleMain.lean's conclusion annotation, definition-adjacent items
reconciled with the concept docstrings, notes.md deduplicated or
dissolved; (3) warning-free build (the nine unusedSimpArgs); (4)
abstract/manifest editorial pass. The four ORIGINAL concept files
stay frozen (already polished at the RAM-stack wrap-up) — defects
are logged, not fixed. Invariants: the theorem statement must not
change semantically; both packages + `lax build` + `--replay` green
and the no-drift check intact after every commit.

## Session 18 — 2026-07-28 ~12:40 UTC
Milestone: the cleanup pass (Jan's request) — all four priorities done
Commits: 4908f3f "Courcelle cleanup: the surface, tightened";
a7d362a "Courcelle cleanup: the node count is read, not quantified";
6cf4f10 "Courcelle cleanup: the ledger moves to where it renders";
27f1a04 "Lax11: the build is warning-free";
8b78af1 "Lax11: the abstract, corrected"
State: Both packages green after every commit, **zero warnings anywhere**
(the nine pre-existing `unusedSimpArgs` are gone), `lax build
ram-linear-time` OK, `--replay` OK, `#print axioms` on the theorem still
propext/Classical.choice/Quot.sound, and session 16's no-drift `example`
(`Lax11.Courcelle.exists_… = Lax11Proofs.Courcelle.exists_… := rfl`,
run in scratch, not committed) still elaborates. `EncodesGraph`,
`Ram.lean`, `RamComputes.lean`, `ConnectedComponents.lean` untouched;
no defect found in them to log.

*(1a) `decidableAdj`, 15 lines → 11.* The four `letI` + `show … from
inferInstance` cases become `inferInstanceAs` applied to the unfolded
graph, with `have := decidableAdj eᵢ` supplying the recursive instances
— term-mode `have` of a class type does register as a local instance,
so the tactic block was pure ceremony. The `relabel` case is now just
`decidableAdj e`: `graph (.relabel _ _ e)` is `graph e` by definition,
so no coercion is needed at all. Still an instance, still structural
recursion, still no `Classical.dec`.

*(1b) `Op.decode`, three private theorems → zero.* `div_lt_sq` was
`Nat.div_lt_of_lt_mul` verbatim and is inlined; `pos_of_lt_sq` and
`mod_lt_sq` collapse into `Nat.mod_lt _ hk` with
`hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at h)` as a
`have` inside the two `k²` branches — the block condition `c < k * k`
already refutes `k = 0`. Two extra lines in the body, no private name on
the surface, and a docstring sentence naming the two arithmetic facts so
a reader is not left to reconstruct them. **`CliqueExpr.lean` 206 → 197
lines. Zero proofs-side ripple**: `Op.decode_code` and `Op.code_lt` in
`MsoTable.lean` compiled untouched, the `have` beta-reduces under the
`simp only [… , dif_pos hp]` they already used.

*(1c) The `∃ N` is gone — done, the ripple was 12 lines.*
`EncodesExprTree t k` (was `t N k`) drops the `nodeCount_eq` field and
states its four clauses about `nodeCount t` directly; `EncodesInstance`
loses one existential and roots the expression at `nodeCount t - 1`.
`Courcelle.lean` 154 → 164 lines (the growth is the new ledger
paragraph, see (2); the definitions shrank by 4). Proofs side:
`instance_tape` now names `N` by casing the block (`cases t with | cons
c tr => exact ⟨c, tr, rfl⟩`) instead of by hypothesis, with one
`have hN : nodeCount (N :: tr) = N := rfl` doing the work the
`nodeCount_eq` field used to; every other line of the ~45-line proof is
unchanged, because `nodeCount (N :: tr)` is `N` by `rfl` and the field
projections typecheck by defeq. `CourcelleSmoke.lean` drops the field
and the `7`, and two `interval_cases` needed their bound restated
(`have hi' : i < 7 := hi`) since `omega` will not unfold `nodeCount`.
The theorem's statement is semantically unchanged: the same words are
admitted, since the old `N` was pinned to `nodeCount t` by the field
that is now gone.

*(2) The ledger renders.* `CourcelleMain.lean`'s conclusion annotation
343 → 466 lines: the old `# What the program does not read` section is
absorbed into a new `# Formalization notes` section carrying seven
argued items in the house's italic-lead-in shape — the cliquewidth pivot
with the unformalized tw→cw conversion and Oum–Seymour, the certificate
and the two arrays the program actually uses, the noncomputable table
and the ∃-program shape, the add-and-subtract-only machine with the
strength-reduced `row` indexing, the `#eval` stand-in table and exactly
what it does and does not establish, `TreeDecomp.lean` kept with the
argument, and the one non-textbook device on the trust surface. The
tower item stayed in `# Where the constant comes from`, which already
said most of it, and gained the closing paragraph on what is and is not
claimed — one home per item, no duplication. Definition-shaped items
went to the concept files per the rule that the concept wins: the MSO₁
scope with the "MSO₂ by the same argument would be false" argument joins
the de Bruijn note in `Mso.lean` (100 → 108), children-before-parents
joins the input-format notes in `Courcelle.lean`. Verified in
`build-output.json`: the theorem's `sections` now list `Proof strategy`,
`Where the constant comes from`, `Formalization notes`, `Attribution`.
`notes.md` 250 → 30 lines, kept as a **map** rather than deleted: it is
not rendered, but anyone reading the directory or the tarball can find
each item from it in one hop, and that costs thirty lines.

*(3) Warning-free.* Nine `unusedSimpArgs`: two `List` lemmas in
`Reasoning.getElem?_arrOf`, four in `CCPhases.readLoop_run` (a whole
`[hi, ht, hl]` on the second component, and an `hy1` passed twice), one
in `CCPhases.initLab_run`, two `hm`s in `CCSweep.outerBody_run`. Only
simp argument lists changed; no proof changed shape and both packages
now build with no output at all.

*(4) Abstract and manifest.* The manifest is accurate against the final
state — title, both bib blocks, seven concepts and two theorems all
check out — and is unchanged. The abstract got two substantive fixes:
the second theorem's bound is now stated as `c(|x|+1)` like the first
instead of "a constant multiple of the length of the input", and the
closing sentence points at the formalization notes *on the theorem*
rather than at a file beside the submission, which no longer holds them.
Nothing else was touched: at 1045 words it is three times the longest
sibling abstract, but the submission is a tower, two theorems and seven
concepts, and every paragraph is carrying a distinct load — trimming it
would have been style churn against Jan's own text.
Next: nothing in the plan. Outward-facing and Jan's: `lax submit`.
Decisions: (1) **`notes.md` survives as a pointer, not a deletion.** The
brief left it to me. The ledger is now where the archive renders it, so
the file has no reviewer-facing job; but the repository is also read
directly, and a thirty-line map is cheaper than a reader grepping seven
files for where the honesty items went. Delete it if you disagree —
nothing imports it and `lax build` ignores it.
(2) **The MSO₁/MSO₂ item went to `Mso.lean`, not to the theorem.** It
reads as a scope claim about the theorem, but the argument it makes is
about which logic `Lax11.Mso` *is* and why the missing constructors are
missing, which is a question a reviewer asks while reading that
definition. The theorem's notes name MSO₁ in the cliquewidth item and do
not re-argue it.
(3) **Editing three concept files was sanctioned and used in full** —
`CliqueExpr.lean` (code + docstring), `Courcelle.lean` (code +
docstring), `Mso.lean` (docstring only; its code has no defect). The
four original concept files were not opened.
(4) The `have`-inside-a-`def` idiom in `Op.decode` is new to this
surface. It survives `simp only [Op.decode, …, dif_pos h]` unharmed, but
it is worth knowing that a future `decide`-heavy proof about `decode`
would see a beta-redex where it used to see a `Fin.mk`.
