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

## VC session 1 — 2026-07-27 (Jan-supervised session, full-authority)
Milestone: V1 + V2 + V3 done; V4 partial (scaffolding green)
Commits: ea32152 pure model (VCSpec) · 46c1897 program + smoke (VC) ·
2316dc1 scan lemma (VCScan) · 3bf9dbd outer-loop scaffolding (VCLoop)
State: Plan rev 1 re-verified by hand before executing — VC4 arithmetic
and the J transitions all check; one gap found and closed: reading
`off[u+1]` needs `u < n`, derived from the invariant `off[u] ≤ j < 2m`.
VCSpec: Ok/bridge/branch/cover-on-exhaustion, cons-form config (top at
head, `Alt`/`stackPot` recurse with bud as accumulator — push/flip/pop
near-rfl), six `inv_*` preservation + six `pot_*` drop lemmas. VC:
vcCom, layout (18 scalars, 6 arrays, L.const = 37), vcCom_ok, nine
#guard smoke tests all correct (triangle/star/P4/edgeless/empty/
malformed; step counts 121–2376). VCScan: flat scan (no inner loop —
design decision, same algorithm) under while_pot, pot 50(2m−j)+50(n−u),
cost 100m+50n+10, dichotomy conclusion. VCLoop so far: Rep (stack
arrays bottom-up = frames.reverse), indicator lemmas, stackPotB/potN
numeric potential + phasesOf decode, potN_eq agreement. All green,
warning-free, mark array needs no init loop (zeroed arrays, marker 0).
Next: VCLoop `outerBody_run` — six-case body transition lemma (descend
cases contain scan_run; K ≤ 100m+50n+100), then `searchLoop_run` via
while_pot with Φ = (100m+50n+104)·potN; then V5 assembly (read phase =
CC pattern + one read into "bud", write ans, computesInTime_of_run,
endgame constant ~37·(4·104+slack)) and V6 wrap-up.
Decisions: (1) scan flattened to a single loop (if j < off[u+1] then
slot else u+1) — proof restructure, not an algorithm change; (2) config
stack cons-form with top at head, Rep does the reversal; (3) Inv's done
clause strengthened to also pin ans ≤ 1 so the answer is determined;
(4) k read directly into "bud", no "k" scalar.

## VC session 2 — 2026-07-27 13:21 UTC
Milestone: V4a — done
Commits: b33656d Lax11 vc: the outer-loop body — six transitions, one lemma
State: `VCLoop.lean` now carries `descendBody_run`, `backtrackBody_run`
and `outerBody_run` with the contract's signatures verbatim; all six
cases (found / stuck / push; fail / flip / pop) discharged, `lake build`
green across `proofs/`, warning-free, zero `sorry`,
`lean_verify Lax11Proofs.VC.outerBody_run` → propext, Classical.choice,
Quot.sound only. K-bounds achieved are exactly the contract's, on the
nose as numerals (`le_rfl` closes each): descend `100*m + 50*n + 96`,
backtrack `96`, outer `100*m + 50*n + 100`. So V4b's loop potential
factor `100*m + 50*n + 104` stands unchanged. Actual costs are much
smaller (descend ≤ scan + 38, backtrack ≤ 34); the slack is deliberate.
Next: V4b — `searchLoop_run` via `Run.while_pot` with
`Φ = (100*m + 50*n + 104) * potN (τ.vars "mode") (τ.vars "bud")
(phasesOf τ)`, using `potN_eq` to cross to `pot` and `outerBody_run` as
the step; then V5 assembly.
Decisions: (1) No deviation from the contract — signatures, case
analysis and bounds are as written; the milestone really was assembly.
(2) Two Lean-level notes for whoever writes V4b. `rw [hfrs] at hstk`
fails with a motive error on Rep's stack clause (the binder
`hi : i < C.frames.length` occurs in the `getElem` proof); `simp only
[hfrs] at hstk` goes through. And `rw [mem_marked_flip …]` fails the
same way inside an `if` (the `Decidable` instance depends on the
proposition) — `dsimp only` to reduce the projection of the
configuration literal, then `simp only [mem_marked_flip …]`, works.
(3) The failure-exit case keeps `C.frames` rather than `[]` in the new
configuration (they are equal by the case hypothesis); this matches
`inv_fail`'s statement and saves a rewrite.

## VC session 3 — 2026-07-27 14:12 UTC
Milestone: V4b — done
Commits: 2bf1ba8 Lax11 vc: the outer loop — while_pot over the tree potential
State: `VCLoop.lean` closes with `searchLoop_run`, the contract's
signature verbatim: one `Run.while_pot` on invariant `I τ := ∃ C, Rep …
∧ Inv … ∧ τ.inp = σ.inp ∧ τ.out = σ.out` and potential `Φ τ =
(100*m + 50*n + 104) * potN (τ.vars "mode") (τ.vars "bud") (phasesOf
τ)`, with `outerBody_run` as the step and `potN_eq` crossing to `pot` at
both ends. Final bound as contracted: `K ≤ (100*m + 50*n + 104) *
pot C₀ + 4`. `lake build` green across `proofs/`, warning-free, zero
`sorry`, `lean_verify Lax11Proofs.VC.searchLoop_run` → propext,
Classical.choice, Quot.sound only.
Next: V5 assembly — read phase (CC pattern + one read into "bud"),
`searchLoop_run`, write `ans`, `computesInTime_of_run`; the constant
arithmetic starts from `(100*m + 50*n + 104) * pot C₀ + 4` with
`pot C₀ = fPot k + 1 ≤ 4 * 2^k`.
Decisions: (1) No deviation from the contract — signature, proof shape
and bounds are as written; the factor `104` needed no raising, since
V4a shipped `outerBody_run` at exactly `100*m + 50*n + 100` and the test
costs `1 + Cond.size = 4`. (2) One Lean-level note for later sessions:
passing the `hstep` argument of `Run.while_pot` inline as `(fun τ hτ hc
=> ?_)` inside an `obtain … := …` silently drops the hole (the second
bullet then reports "no goals"); state `hstep` as a standalone `have`
with the loop rule's payment inequality spelled out — including the
literal `1 + (Cond.lt (Expr.var "mode") (Expr.lit 2)).size` — and pass
it by name. (3) The payment arithmetic is kept away from `omega`'s
nonlinear blind spot by pre-deriving `Nat.mul_le_mul_left _ hpot` and
`rw [Nat.mul_succ]`, then rewriting both `potN`s to `pot`; `omega` sees
only atoms after that.

## VC session 4 — 2026-07-27 15:04 UTC
Milestone: V5 — done. **The vertex cover statement is discharged.**
Commits: 7be9bba Lax11 vc: the 2^k discharge — assembly, endgame, constant 33300
State: `VCMain.lean` carries `vcExt`, `const_eq : layout.const = 37`,
`vcCom_run` and the proof-package theorem
`Lax11Proofs.VCMain.exists_fptTime_program_vertexCover`, statement
verbatim from the concept — checked by `example : … = Lax11.VertexCover
.exists_fptTime_program_vertexCover := rfl`, which typechecks, so the
two types are definitionally equal. The five VC modules are appended to
the root `Lax11Proofs.lean` in order (`VCSpec`, `VC`, `VCScan`,
`VCLoop`, `VCMain`), `lake build` green across `proofs/`, zero `sorry`,
`lean_diagnostic_messages` on `VCMain.lean` returns an empty list — no
warnings. `lean_verify Lax11Proofs.VCMain.exists_fptTime_program_vertexCover`
→ `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}`.
**Achieved constant: c = 33300** (= 37 · 900), the literal numeral in
the witness `⟨vcProgram, 33300, …⟩`; `vcCom_run`'s IMP+ bound is
`900 * 2^k * (|x| + 1)`.
Next: V6 wrap-up (Jan-visible): `abstract.md` final paragraph, `notes.md`,
`lax submit`. No Lean work remains on this ladder.
Decisions: (1) One deviation from the contract, sanctioned by its own
text: `VCMain.lean` imports `Lax11Proofs.CCSweep` in addition to
`Lax11Proofs.VCLoop`, because `getD_take` / `getD_drop` /
`getD_cons_cons` live there and `VCLoop`'s chain does not reach it.
Everything else — `vcExt`, `const_eq = 37`, the `900` in `vcCom_run`,
the `⟨vcProgram, 37 * 900⟩` witness — is exactly as contracted; the
whole file compiled on the first build with no failed attempts.
(2) The arithmetic recipe that avoids `omega`'s nonlinear blind spot:
mono the loop run to `816 * (2^k * (5 + n + 2*m)) + 4` (from
`Nat.mul_le_mul` of `100m + 50n + 104 ≤ 204*(5 + n + 2*m)` and
`pot_init_le`), then in the cost goal `rw [hlen2, Nat.mul_assoc]`,
supply `hQ : 5 + n + 2*m ≤ 2^k * (5 + n + 2*m)` from
`Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)`, and
`generalize 2 ^ k * (5 + n + 2*m) = Q at hQ ⊢` — after which `omega`
sees a purely linear goal. Read phase is `12n + 24m + 39` and the write
is `2`, so the slack from `816` to `900` is roughly ten times what is
needed; nothing was fought for.
(3) `EncodesInstance` destructures as `⟨g, rfl, hg⟩` and then `subst`s
`g = n :: m :: rest`, so the whole proof works on the literal tape
`n :: m :: rest ++ [k]`; `edgeCount (g ++ [k]) = edgeCount g` comes from
`List.getElem?_append_left (show 1 < g.length …)` off `length_eq`.
(4) The concept's `open Classical in` is inert here: `ℕ∞` has a real
`DecidableLE`, so `VCSpec.ans_eq`'s `if` and the concept's `if` pick the
same instance, and `VCMain` needs no `open Classical`.

## VC session 5 — 2026-07-27 13:39 UTC (= 15:39 local; the "UTC" stamps on the earlier VC entries were local time)
Milestone: V6 — done. **>>> FOR JAN'S MORNING REVIEW <<<**
Commits: 142da71 Lax11 vc: wrap-up — abstract and notes record the discharge
State: The Lax11 vertex cover statement is discharged end to end and the
submission's outward-facing record now says so.
**Achieved constant: c = 33300 = 37 · 900** — `layout.const = 37` machine
steps per IMP+ statement, times the IMP+ bound `900 * 2^k * (|x| + 1)`.
`lean_verify Lax11Proofs.VCMain.exists_fptTime_program_vertexCover` →
propext, Classical.choice, Quot.sound only.
The campaign, seven commits: b369ffa (plan rev 1), ea32152 (pure model),
46c1897 (program + smoke), 2316dc1 (scan lemma), 3bf9dbd (outer-loop
scaffolding), b33656d (outer-loop body), 7be9bba (assembly + endgame),
plus tonight's 142da71 (wrap-up). Four of them landed tonight (b33656d,
2bf1ba8 = the `while_pot` outer loop, 7be9bba, 142da71).
Three edits: (1) `abstract.md` final paragraph rewritten — the statement
is discharged, not open; search tree in the same while-language, same
loop rule, the potential and where `2^k` enters, constant 33300 spelled
out as 37 × 900. (2) `notes.md` vertex-cover bullet rewritten in the
style of the CC bullet: statement items still in the concept's
`# Formalization notes`, proof items now in `VCMain.lean`'s conclusion
annotation under `# What the program is allowed to help itself to` and
`# Attribution`; the "open obligation" sentence is gone. (3) `lax build`
in `ram-linear-time/` — both packages green (988 + 3008 jobs), and
`build-output.json` records `Lax11Proofs.VCMain.exists_fptTime_program_
vertexCover` with `conclusion: Lax11.VertexCover.exists_fptTime_program_
vertexCover`, `assumptions: []`, and sections `Proof strategy` / `What
the program is allowed to help itself to` / `Attribution`. The file is
gitignored, so nothing of it was staged. No `.lean` and no `concepts/`
file was touched.
Next: **`lax submit` is Jan's call — deliberately not run.** No Lean work
remains on this ladder; phase 2 (φ^k) is sketched in `vc-ladder-plan.md`
and needs Jan's gate on VC6.
Decisions (things Jan may want to undo):
(1) The abstract's closing paragraph is my prose in Jan's register — the
wording most open to revision is the last sentence, where I kept Jan's
original "what is proved and what is merely stated is said plainly …"
and added "the statement joined the surface before it had a proof, which
is what the archive's decoupling of concepts from proofs is for", so the
paragraph's old point survives now that no obligation is open. Cut it if
it reads as self-congratulation.
(2) I quoted the constant in the abstract as "33300: thirty-seven machine
steps per statement of the compiled program, times `900·2^k(|x|+1)`
statements", matching the CC paragraph's habit of quoting 2604 with its
per-input-number gloss. If the factorization is too much detail for an
abstract, the first clause stands alone.
(3) I did not mention the achieved constant in `notes.md` — it lives in
the abstract and in the `VCMain` docstring, and `notes.md` is a map, not
a ledger.

## VCF session 1 — 20:41 UTC
Milestone: S0 — done
Commits: aa8359a `Lax15 vcfib: scaffold — concept surface, pins, packages build green`
State: `lax init vertex-cover-fibonacci` reached the archive server and
allocated **Lax15** (not provisional). Scaffold gave LICENSE (Apache 2.0,
byte-identical to `ram-linear-time/LICENSE`), a `.gitignore` covering
`build-output.json`, `lake-manifest.json` and `.lake/`, and mathlib
pre-provisioned in both packages. Written: lakefile pins per VF1 (concepts:
mathlib c5ea003, Lax13 @ 2087642 word-ram/concepts, Lax11 @ 0bbcfec
ram-linear-time/concepts; proofs: those plus `../concepts`, Lax13Proofs @
2087642, Lax11Proofs @ 0bbcfec), manifest (title *Vertex Cover in Fibonacci
Time*, Jan + Fable, CyganEtAl2015 + DowneyFellows1999), abstract draft,
`concepts/Lax15/VertexCover.lean` with the plan's statement verbatim plus
frontmatter/prose/`# Formalization notes`, root modules, and a placeholder
`proofs/Lax15Proofs/Basic.lean`. Both packages `lake build` green, zero
sorry: concepts 24 s (1032 jobs), proofs 62 s (2987 jobs) — the dep build
was fast because only the transitive closure of `Lax13Proofs.Reasoning` and
`Lax11Proofs.VCSpec` is needed, nowhere near the feared 20–60 min.
Next: S1 — the pure graph lemmas (`ResNbhd`, `resDeg`, `ResEdges`, lemmas
1–3) in a new `Lax15Proofs` module.
Decisions:
(1) `lax init` writes a `lake-manifest.json` listing mathlib only, and lake
then refuses to build with `dependency 'Lax11' not in manifest; use lake
update`. I did **not** run `lake update`: I deleted the (gitignored)
`lake-manifest.json` in each package and let `lake build` re-resolve from
the lakefile, which pins every Lax rev exactly. The regenerated manifests
record exactly the six intended revs. Flagging it because the brief forbids
`lake update` and this is the adjacent move; a future session that adds a
dependency should do the same rather than reach for `lake update`.
(2) The plan's prose says `fib (k+2) ≈ 1.9·φ^k`; the true factor is
`φ²/√5 ≈ 1.17`. I did not put a number in the concept — the notes say
"a fixed multiple of φ^k". Worth fixing in `vc-fib-plan.md` if the figure
is reused in the S7 abstract.
(3) The concept's Formalization notes say the admissible set is character
for character Lax11's, so the improved bound is claimed on exactly the same
instances. That is a promise the S6 assembly must keep: the fitting
condition stays `c * (x.length + k + 1) ≤ 2 ^ w`, with the *same* `c` as
the time bound.

## VCF session 2 — 21:05 UTC
Milestone: S1 — done (items 1–5 all landed), with a **plan-level finding
the orchestrator must resolve before S3/S4**.
Commits: 80adfd3 `Lax15 vcfib: residual graph side — early exit, matching
bound, vertex branch`
State: `Lax15Proofs/Residual.lean` (green, zero sorry, only the three
background axioms), root module now imports it plus `Repeats.lean`; the
scaffold stub `Basic.lean` is gone. Contents: `ResNbhd`/`resDeg`/
`ResEdges` with membership API, disjointness and antitonicity;
`ok_of_card_resEdges_le` (plan lemma 1, witness `M ∪ image Sym2.inf` —
`Sym2.inf` from `Mathlib.Data.Sym.Sym2.Order` is a cleaner endpoint pick
than `Quot.out`, and `Sym2.inf_eq_inf_and_sup_eq_sup` gives injectivity
for free); `not_ok_of_lt_card_resEdges` (lemma 2, hypothesis
`∀ v ∉ M, resDeg ≤ 1`); `ok_branch_resNbhd` (lemma 3, exactly the plan's
statement, `2 ≤ resDeg` indeed not needed — the ← direction goes through
a new `ok_of_ok_union : Ok (M ∪ N) b → Ok M (b + N.card)`); and the CSR
transport: `ResSlots` (slot count, parameterized by a bound `J` so the
scan's invariant can use it directly), `ResOwners` (the same count capped
at one slot per block), `ThinBlocks`/`ThinSlots`, `thinBlocks_iff`,
`exists_two_slots_iff`, and the four card comparisons.

**The finding (VF3 is not implementable as written).** The Lax11 concept
surface deliberately admits encodings that list a neighbour of a vertex
several times ("A graph with an edge has encodings of every length"), and
the plan's descend scan is not repeat-proof:

  * `Repeats.lean` proves, machine-checked, that
    `g = [2,2,0,2,4,1,1,0,0]` encodes the one-edge graph on `Fin 2` with
    the block of vertex 0 naming vertex 1 *twice*. Every vertex has
    residual degree 1, yet vertex 0 has two slots with unmarked targets.
  * So the plan's found-test (per-owner *count* of unmarked slots reaches
    2) fires at a vertex of residual degree 1. T4 then pushes, and at the
    flip T6 needs `2 ≤ d` for the drop `(f (b−2) + 2) − f (b−d) − 1 ≥ 1`;
    with `d = 1` the potential *rises*. This is not only a proof gap: on
    the family "k disjoint edges, every block listing its neighbour
    twice" (|x| = 6k+3) the planned program branches binary to depth k,
    i.e. 2^k steps against a claimed `c·fib(k+2)·(|x|+1)` — the bound is
    violated for large k. The algorithm is *correct*, just not Fibonacci.
  * Fixing the found-test to "two unmarked slots with **different**
    targets" (O(1) per slot: keep the block's first unmarked target in a
    register) makes it exactly `∃ v ∉ M, 2 ≤ resDeg M v` —
    `exists_two_slots_iff` — but then T2 breaks instead: the slot count
    `re` still overcounts (2k for a k-matching), so `re > bud` no longer
    implies `¬ Ok`. That direction needs the *capped* count: one
    increment per block, at its first unmarked slot with `u < tgt` — that
    is `ResOwners`, which is `≤ card ResEdges` always and `=` on a
    matching (`card_resOwners_le_card_resEdges`,
    `card_resEdges_le_card_resOwners`).
  * Recommended repair, cheapest that keeps every transition sound and
    the potential intact (orchestrator's call, it changes VF3): one
    counter `re` = the capped count, one flag `found` = distinct-target
    test, and the descend rules become: `found` → branch (or, at
    `bud = 0`, backtrack — a branching vertex gives an uncovered edge);
    `¬found` → `re ≤ bud` yes, else no. The early-YES test on the
    *uncapped* slot count may be kept as a fast path (it stays sound:
    `card_resEdges_le_card_resSlots`), but it is not needed.
Next: orchestrator decides the VF3 repair (recommendation above), then
S2 — the config side — proceeds unchanged: it needs `ok_branch_resNbhd`,
`not_ok_of_lt_card_resEdges`, `ok_of_card_resEdges_le` and nothing from
the transport section. S2 is independent of the repair and can start now.
Decisions:
(1) All residual definitions are `noncomputable` under `open Classical
in`; no `DecidableRel G.Adj` variable anywhere. This keeps S2/S4
statements instance-free, at the cost of the defs never `#eval`-ing —
the S3 smoke tests run the *program*, not these, so nothing is lost.
(2) `Repeats.lean` was added to the package rather than left in a
scratch file: it is a fact about the encoding, true whatever S3 does with
it, and it is the evidence for the finding above. Delete it if the
orchestrator considers the surface too wide.
(3) `ResSlots` is a `Finset (Fin n × ℕ)` of (owner, slot) pairs and not a
`Finset ℕ` of slots: no owner function has to be defined, and the scan's
partial count over `j < J` is the same definition with a smaller `J`. If
S4 would rather count over `Finset.range J` with an owner read off the
offsets, that transport is not proved here.

## VCF session 3 — 21:23 UTC
Milestone: S2 — done (all four deliverables, flip included)
Commits: 135259b `Lax15 vcfib: config side — frames, invariant, potential,
eight transitions`
State: `Lax15Proofs/Config.lean` (green, zero sorry, three background
axioms only; whole package builds in ~6 s on top of the warm dep build).
Contents: `Frame` (`v, b, phase, S`) and `Config` (`frames, mode, bud,
ans`), `trail`/`marked` (the plan's `P_i` is `marked` of the frames below
a frame, `M` is `marked` of all — the list is top-first, so no index
arithmetic ever appears), `Healthy G k` with its consequences
(`head_disjoint`, `head_ne_nil`, `trail_nodup`, `card_marked`,
`trail_length_le : (trail fs).length ≤ n`, `length_le : fs.length ≤ n`)
and the two pointwise mark-update lemmas `mem_marked_flip` /
`mem_marked_pop` that S5 will need for the mark-array writes; `Alt`, `J`,
`j_init`, `ans_eq`; `fPot b = 4 * Nat.fib (b+2) - 3` with `fPot_zero`,
`fPot_one`, `fPot_succ_succ`, `one_le_fPot`, `fPot_mono`, `fPot_push`,
`stackPot`, `pot`, `pot_init`, `pot_init_le ≤ 4 * fib (k+2)`, and the
machine-side mirror `stackPotN`/`potN` with `pot_eq_potN` (the crossing
equation is *not* deferred: the stack arrays hold `(b_i, phase_i)` and
that is all the potential reads). Eight transitions `step_yes`,
`step_no`, `step_stuck`, `step_push`, `step_exhausted`, `step_flip`,
`step_flip_infeasible`, `step_pop`, each concluding
`J G k C' ∧ pot C' + 1 ≤ pot C`.
Next: S3 — the program `vcfCom` + `#eval` smoke tests (VF3 rev 2 rules).
Decisions:
(1) Because a phase-one frame marks a whole neighbourhood, stack depth is
no longer budget spent, so each frame stores its own `b` and neither
`Alt` nor `stackPot` threads a budget through the recursion (unlike
Lax11's). That is also what makes `potN` cheap: `stkB` and `stkP` are
exactly its arguments.
(2) The descend budget equation `bud + (trail frames).length = k` is in
`J` **only in descend mode**. In backtrack mode `bud` is dead — the flip
and the pop both overwrite it from the frame's stored `b` — and after an
infeasible flip (T7) the relation is genuinely false (the trail grew by
`d` while `bud` stayed `b`). `step_flip_infeasible` and `step_pop`
therefore quantify over an arbitrary new `bud'`.
(3) The flip lemmas take any `l` with `l.Nodup` and
`l.toFinset = ResNbhd G (P_i) v_i`: order and the CSR's freedom to name
neighbours in any order never reach the pure side. T6 came out near-`rfl`
as the plan predicted — one `Finset.union_comm` and an `Or` shuffle.
(4) The plan's arithmetic checks out with **no deviation**. Exact drops:
T4 push (`fPot (b-1) + fPot (b-2) + 3 ≤ fPot b`, equality at every `b ≥ 1`
including the truncated `b = 1` case `1 + 1 + 3 = 5`), T5, T8, and T6 when
`d = 2`. Slack: T1 (`fPot bud + 1`), T2 (`fPot bud`), T3 (exactly
`fPot 0 = 1`, so exact too), T6 with `d > 2`, T7 (two units). Numerically
sanity-checked: `fPot` = 1, 5, 9, 17, 29, 49 and a push/push/backtrack/
flip/pop trace drops 18 → 17 → 16 → 11 → 10 → … as designed.

## VCF session 4 — 21:46 UTC
Milestone: S3 — done (program, `vcfCom_ok`, and the full smoke list green)
Commits: 0bcb6f3 `Lax15 vcfib: the program and its smoke tests`
State: `Lax15Proofs/Program.lean` (green, zero sorry, three background
axioms), added to the root module. `vcfCom` is the plan's VF3 rev 2
algorithm verbatim: read phase copied from Lax11's `vcCom`; outer
`while mode < 2`; `descendScan` = one pass `j ∈ [0, 2m)` with the inner
`ownerAdvance` loop (`off[u+1] < j+1`) resetting `seen`/`t1`/`cnted`,
`slotStep` counting the owner into `ro` once (guarded by `cnted` and
`u < w`) and raising `found`/`v` on an unmarked target different from
`t1`; then the four-way case; `backtrackBody` = exhausted / `flipFrame`
(unmark, restore `bud` from `stkB`, row scan marking onto the trail,
`stkP[sp] := 1`, feasibility `d < bud+1`) / `popFrame` (unwind loop,
restore `bud`, `top := top-1`); `write ans`. Layout: 26 scalars, arrays
`off tgt mark trail stkV stkB stkT stkP`, 4 temps. Every name and the
statement shape are documented in the file's header comment (lines
4–140; the scalar table is lines 51–91, the statement layout 93–139) —
S4/S5 should read that as the ground truth.
All eighteen smoke instances answer as the plan predicts, asserted with
`#guard` (a wrong answer was checked to break the build). Step counts:
triangle 3030 / 2415 (k=1/2), P4 3120 / 2505, K1,3 2357 (k=1), C4 3862 /
4294, C5 7990 / 5483 (k=2/3), 2K2 1142 / 1107, K4 7512 / 6127 (k=2/3),
edgeless 200, empty 144, malformed 129 (halts on the exhausted tape).
Repeat encodings: `[2,2,0,2,4,1,1,0,0]` + k gives 0 at 1028 steps and 1
at 993. The doubled-slot matching family (e disjoint edges, every slot
listed twice, budgets e-1 / e) is linear: e = 3 → 2800 / 2765
(|x| = 22), e = 5 → 4572 / 4537 (|x| = 34), e = 8 → 7230 / 7195
(|x| = 53), i.e. 127, 134, 136 steps per input letter and no push ever.
Lax11's `vcCom` on the same two: 6934 and 52554 steps (it branches).
On shared instances Lax11 is a constant factor cheaper (triangle k=2:
1662 vs 2415; C5 k=3: 3898 vs 5483) — eight arrays cost more per array
access and the descend scan has no early exit.
Next: S4 — the inner-loop Run lemmas (descend scan, flip row scan, pop
unmark loop) against `Program.lean`'s three `while`s.
Decisions:
(1) Two deviations from the plan's prose, both documented in the header.
`flipFrame` unmarks `mark[pv]` rather than `mark[trail[tb]]` (equal under
frame health, and it saves S5 an appeal to `trail[tb] = v`). And the
branch witness is kept *first* by guarding the assignment with
`found = 0`, as the plan says, even though S4's invariant would accept
an arbitrary witness.
(2) `ownerAdvance` is a genuine inner `while`, per the plan, so the
descend scan is two nested `while_pot`s and not one: outer potential in
`2m − j`, inner in `n − u`. Note the inner loop has no `u < n` guard — on
a valid encoding `off` is nondecreasing with `off[n] = 2m > j`, so `u`
stops below `n`; on a malformed word that got past the read phase it
would spin (the machine wraps addresses, it never traps). Every malformed
word I could construct halts in the read phase, and the smoke word does.
If S4/S5 would rather not carry that, the guard is a one-line change —
but it turns the loop's exit condition into a disjunction.
(3) Fuel and word length of the smoke runner: `runOut 16 3000000`. The
`#eval`s are cheap (the largest is 7230 steps) but the machine's memory
is a closure chain, so long runs get quadratic — that is why Lax11's
`vcCom` was not run on the eight-edge instance.

## VCF session 5 — 01:12 UTC
Milestone: S4 — done (all three inner-loop Run lemmas plus the Rep layer)
Commits: 6cd8e6e `Lax15 vcfib: inner-loop run lemmas — Rep, descend scan,
row scan, unwind`
State: `Lax15Proofs/Phases.lean` (1607 lines, green, zero sorry, three
background axioms), added to the root module. Signatures S5 consumes
verbatim:
- `Rep (n m : ℕ) (O T : ℕ → ℕ) (C : Config n) (τ : Env) : Prop` with
  projections `Rep.m2/off/tgt/mode/bud/ans/top/tt/mark/trail/stk` and
  `Rep.of_vars_eq` (arrays + the six scalars fixed ⇒ Rep transports).
- `descendScan_run (hg) (hm : edgeCount g = m) (hO) (hT) (h1B : 1 < B)
  (hnB : n < B) (hmB : 2*m < B) (hRep : Rep n m O T C τ) : ∃ τ' K,
  Run B descendScan τ τ' K ∧ Rep n m O T C τ' ∧ arrs/inp/out fixed ∧
  τ'.vars "ro" = (ResOwners g (marked C.frames) (2*edgeCount g)).card ∧
  ((found = 0 ∧ ThinBlocks g (marked C.frames)) ∨ (found = 1 ∧ ∃ v : Fin n,
  (v:ℕ) = τ'.vars "v" ∧ v ∉ marked C.frames ∧ 2 ≤ resDeg G _ v)) ∧
  K ≤ 250 * (n + 2*m + 1)`.
- `rowLoop_run (hg) (hm) (hT) (h1B) (hnB) (hmB) {v MK TR tb τ}
  (hcard : M.card = tb) (hmark) (hMK : Indicator M MK) (htrail) (htgt)
  (hj : j = offset g v) (hjend : jend = offset g (v+1)) (htt : tt = tb) :
  ∃ τ' l MK' TR' K, Run B rowLoop τ τ' K ∧ l.Nodup ∧
  l.toFinset = ResNbhd G M v ∧ tt' = tb + l.length ∧ mark = Indicator
  (M ∪ l.toFinset) ∧ trail below tb fixed ∧ TR' (tb+i) = l[i] ∧ frames ∧
  K ≤ 50 * (n + 2*m + 1)`  (`rowLoop`/`unwindLoop` are the `while`s of
  `flipFrame`/`popFrame`, tied to them by `flipFrame_eq`/`popFrame_eq`).
- `unwind_run (h1B) (hnB) {S MK TR tb τ} (hnd : S.Nodup)
  (hdisj : Disjoint S.toFinset M) (hmark) (hMK : Indicator (S.toFinset ∪ M)
  MK) (htrail) (hTR : TR (tb+i) = S[i]) (htb) (htt : tt = tb + S.length)
  (hbnd : tb + S.length ≤ n) : ∃ τ' MK' K, Run B unwindLoop τ τ' K ∧
  tt' = tb ∧ Indicator M MK' ∧ frames ∧ K ≤ 50 * (n + 1)`.
Cost numerals shipped: descend scan `250·(n+2m+1)` (potential
`200·(2m−j) + 100·(n−u)`), row scan `50·(n+2m+1)` (potential
`40·(off(v+1)−j)`), unwind `50·(n+1)` (potential `30·(tt−tb)`).
Next: S5 — the outer body (`outerBody_run`), case split on mode/branch
against these three.
Decisions:
(1) **Trail orientation** (S5 must mirror): the array is `trailArr fs =
trail fs.reverse` — bottom frame first, each frame's marks in the order
it made them — so a push appends at the end and a pop truncates. The
`Rep` clause is stated against `trailVals` (the same list as `ℕ`) and
only over `[0, (trail C.frames).length)`; nothing above the height is
constrained. Stack arrays bottom-up (`C.frames.reverse[i]`), extents
`n+1` for `trail`/`stkV`/`stkB`/`stkT`/`stkP`, `n` for `mark`, per
Program.lean's header. Frame `i`'s stored base is `base fs i =
(trail (fs.drop (fs.length − i))).length`, with `base_top` and
`base_cons` the two lemmas a push/pop needs.
(2) The descend scan is `Rep`-level; the flip's row scan and the pop's
unwind loop are **array-level**, like Lax11's `scan_run` — mid-body they
represent no configuration (marks already those of the frames below
while the frame is still on the stack). S5 reassembles `Rep` from the
`Indicator`/trail conclusions; `indicator_set_one`/`indicator_set_zero`
are there for the flip's single unmark of `pv`, which I left to S5 (it
is one `Run.store`).
(3) Two lemmas S1 did not have, proved in Phases.lean and worth a look:
`two_le_resDeg_of_slots` — the per-vertex form of `exists_two_slots_iff`
(the ∃-form cannot name the witness the scan found, which `step_push`
needs), and `resOwners_succ_of_residual`/`_of_not`, one slot's effect on
`ResOwners`. If a later session wants them upstream they belong next to
`exists_two_slots_iff`.
(4) The guard-free owner advance (S3's note 2) needed no guard: the
invariant clause `j ≤ offset (u+1)` both stops the loop and makes the
reset of `seen`/`t1`/`cnted` sound (the advance can only step onto a
block that starts exactly at `j`). No change to the program.

## VCF session 6 — 04:12 UTC
Milestone: S5 — done (the whole outer body, all eight transitions)
Commits: 179742a `Lax15 vcfib: outer body — the eight transitions, run`
State: `Lax15Proofs/Loop.lean` (776 lines, green, zero sorry, three
background axioms), added to the root module; whole package builds in
~25 s on the warm dep build. Three theorems S6 consumes:
- `descendBody_run (hg) (hm) (hO) (hT) (h2B : 2 < B) (hnB : n + 1 < B)
  (hmB : 2*m < B) (hkB : k + 1 < B) {C τ} (hRep : Rep n m O T C τ)
  (hJ : J G k C) (hmode : C.mode = 0) : ∃ C' τ' K, Run B descendBody τ τ' K
  ∧ Rep n m O T C' τ' ∧ J G k C' ∧ pot C' + 1 ≤ pot C ∧ τ'.inp = τ.inp ∧
  τ'.out = τ.out ∧ K ≤ 500 * (n + 2*m + 1)`
- `backtrackBody_run` — same hypotheses with `C.mode = 1`, same
  conclusion for `backtrackBody`, same numeral.
- `outerBody_run` — same hypotheses with `C.mode < 2`, conclusion for
  `outerBody`, `K ≤ 510 * (n + 2*m + 1)`.
Plus three reusable helpers in the same file: `getElem_reverse_top` /
`getElem_reverse_lt` (the bottom-up stack order past a push, Lax11's
lemmas re-proved here since `VCLoop` is not imported), `Rep.of_frames_eq`
(a transition that leaves the stack alone transports `Rep`; the shape is
`Rep … ⟨C.frames, mode, bud, ans⟩ τ'`, which is exactly what T1/T2/T3/T5
produce), and `card_resOwners_le`.
Next: S6 — `Run.while_pot` with `Φ = U·(x.length+1)·potN`, the read
phase, `write ans`, `computesInTime_of_run`, the endgame theorem.
Decisions:
(1) **The value bound moved.** S4's lemmas take `n < B`; the body needs
`n + 1 < B` (the push writes `top + 1` and `tt + 1`) and `k + 1 < B` (the
two comparisons `ro < bud + 1` and `d < bud + 1` evaluate `bud + 1`, and
`bud ≤ k`). Both are free from the admissibility condition
`c * (x.length + k + 1) ≤ 2^w`. The four hypotheses of the body are
therefore `2 < B`, `n + 1 < B`, `2m < B`, `k + 1 < B` — S6 must supply
these, not Lax11's `k < B`.
(2) The plan's T-table needed no repair: every semantic guard discharged
from the scan verdict plus S1. T1/T2 go through
`card_resOwners_le_card_resEdges` and `card_resEdges_le_card_resOwners`
(the second needs `thinBlocks_iff` first), which pin `ro` to
`(ResEdges).card` exactly in the ¬found case; T3 takes the uncovered edge
out of `2 ≤ resDeg` by `Finset.card_pos`. Nothing in `Config.lean` or
`Phases.lean` had to change.
(3) Two Lean-level traps worth carrying forward. Deeply nested
`Run.seq`/`Run.ite` terms over `set`-bound environments blow the whnf
heartbeat limit: build each phase as its own `have` (`rflip`, `rpop`,
`rback`) with an explicit `K₁ + numeral` cost and the elaborations stay
small. And `if_neg (by decide)` / `if_pos rfl` inside `simp only`/`rw`
lists either leaves a metavariable or silently fails to fire — use a
named hypothesis (`if_neg h`), a `show`-typed proof, or plain `simp`.
(4) `unwind_run` needs `(B := B)` passed explicitly: `B` occurs in none
of its hypotheses except `1 < B`/`n < B`, so an `obtain` without an
expected type leaves it a metavariable and the `by omega`s fail. Also,
the `Rep` binder `i < (trail C'.frames).length` does not reduce to
`i < (trail fs).length` for `omega` — restate it with a `have`.

## VCF session 7 — 23:24 UTC (clock reading; the box is behind sessions 5–6)
Milestone: S6 — done (loop, assembly, endgame theorem, all four deliverables)
Commits: 12fddcc `Lax15 vcfib: assembly and endgame — the loop, the read
phase, the theorem`
State: `Lax15Proofs/Main.lean` (green, zero sorry, `lean_verify` on the
endgame gives propext / Classical.choice / Quot.sound only,
`lean_diagnostic_messages` empty), added to the root module. The whole
`proofs/` package builds in ~6 s on the warm dep build; `concepts/`
untouched and still green (1032 jobs). Contents, in order:
- `framesOf` (the stack's `(b, phase)` list read totally off `stkB`/`stkP`
  below `top`), `framesOf_eq`, `potN_eq` — the decode, one
  `List.ext_getElem`, exactly the `VCLoop` shape.
- `searchLoop_run` — `Run.while_pot` at scale `514 * (n + 2m + 1)`
  (`510` for the body, `4` for the test), conclusion
  `K ≤ 514 * (n + 2m + 1) * pot C₀ + 4`.
- `vcfExt` (`tgt ↦ 2m`, `mark ↦ n`, everything else `↦ n+1`), `const_eq :
  vcfLayout.const = 43`, `mem_lt_length_add`, `vcfCom_run` (end-to-end
  `Run` on every encoded instance, `K ≤ 2100 * fib (k+2) * (|x|+1)`),
  `vcfCom_solves`, and `exists_fibTime_program_vertexCover` with the
  conclusion frontmatter and the `@thm = @axiom := rfl` identity check
  against `Lax15.VertexCover.exists_fibTime_program_vertexCover`.
**Achieved constant: `c = 90300 = 43 · 2100`.** `43 = vcfLayout.const =
3 · (8 − 1 + 3) + 13` — eight arrays, so one index computation is ten
instructions and the machine pays 43 steps per unit of IMP+ cost.
`2100` is the IMP+ cost per `fib (k+2)` per input letter: `2056 =
514 · 4` from the loop (`514 · (n+2m+1)` per turn against
`pot C₀ ≤ 4 · fib (k+2)`, and `n+2m+1 ≤ |x|+1`), plus `44` of slack
absorbing the read phase (`12n + 24m + 35`), the `write`, and the loop
rule's `+4`. Same fitting condition and same admissible set as Lax11's,
whose constant was `33300 = 37 · 900`; ours is 2.7× larger, all of it in
the two extra arrays and the flat descend scan, none of it in `k`.
Next: S7 — wrap-up (abstract.md final, notes.md, `lax build`, Jan
summary). No `lax submit` (VF8).
Decisions:
(1) The endgame landed on the first serious elaboration: three fixable
errors (two missing `open Lax11Proofs` / `import Lax15.VertexCover`, one
`omega` that needed `4 + n + 2m + k ≤ B` hoisted out of `hB` before the
value bounds instead of `simp at hB` inside each). S5's whnf trap never
fired — the read phase's eight `Run.seq`s over `set` environments
elaborate fine, as they do in Lax11's `VCMain`; the trap is specific to
nesting `Run.ite` inside them.
(2) The identity check is written `example : @exists_fibTime_program_
vertexCover = @Lax15.VertexCover.exists_fibTime_program_vertexCover :=
rfl`. `Eq` forces the two types to be defeq, so this typechecks only if
the proved statement *is* the concept's proposition; `rfl` then closes it
by proof irrelevance. Cheaper and stronger than restating the type, and
it also certifies that the `Decidable` instance in the concept's
`if G.vertexCoverNum ≤ (k : ℕ∞)` (under `open Classical in`) is the same
one the proof side infers.
(3) Nothing in the kit assumed a power-of-two potential, as the plan
hoped: `while_pot` and the `omega` recipe took `Nat.fib (k+2)` with
`Nat.fib_pos.2` in place of `Nat.two_pow_pos` and no other change.
(4) For S7's abstract: the honest headline numbers are `fib (k+2)`
leaves, `c = 90300`, and the measured step counts of S3 — Lax11 is a
constant factor *cheaper* on small shared instances (triangle k=2: 1662
vs 2415) and catastrophically worse where the base bites (the doubled
five-edge matching: 52554 vs 4572). Worth one sentence; the claim is
about the exponent, not about the constant.

## VCF session 8 — 23:33 UTC
Milestone: S7 — done (all five deliverables; the Fibonacci rung is
finished and staged for Jan)
Commits: 72fffb8 `Lax15 vcfib: wrap-up — abstract, notes, README entry`

### For Jan, in the morning

**Lax15 `vertex-cover-fibonacci/` is complete: statement *and* proof.**
Vertex cover is decided on the word RAM within
`c · fib(k+2) · (|x|+1)` steps — the base of the exponential lowered
from 2 to the golden ratio (`fib(k+2) ≈ 1.17 · φ^k`, φ ≈ 1.618) by
branching on a vertex of residual degree ≥ 2 instead of on an edge.
Same machine, same encoding, same admissible set as Lax11's `2^k`
statement, character for character, so the two bounds are claims about
literally the same inputs: this sharpens that rung, it does not unsay
it. Achieved constant **`c = 90300 = 43 · 2100`** (43 machine steps per
IMP+ statement from the eight-array layout; 2100 IMP+ statements per
`fib(k+2)` per input letter). `lax build vertex-cover-fibonacci` green
(concepts 1032 jobs, proofs 2998), `build-output.json` records the
conclusion `Lax15.VertexCover.exists_fibTime_program_vertexCover` with
**empty assumptions**; `lean_verify` on the endgame theorem gives the
three background axioms only; zero `sorry` anywhere.

The whole campaign, in order:
- aa8359a S0 scaffold — concept surface, pins, both packages green
- 80adfd3 S1 residual graph side (early exit / matching bound / vertex
  branch) — *and* the repeat-encoding finding that repaired VF3
- 135259b S2 config side — frames, invariant `J`, potential, the eight
  transitions
- 0bcb6f3 S3 the program `vcfCom` and eighteen `#guard`ed smoke tests
- 6cd8e6e S4 inner-loop run lemmas — `Rep`, descend scan, row scan,
  unwind
- 179742a S5 the outer body — all eight transitions, run
- 12fddcc S6 assembly and endgame — the loop, the read phase, the
  theorem
- 72fffb8 S7 wrap-up — `abstract.md`, `notes.md`, README entry

Deliberately left for you, none of it blocking:
- **`lax submit vertex-cover-fibonacci`** — not run tonight (VF8). The
  draft is ready; submitting is your call, and registering it will need
  Lax11 and Lax13 registered first (the build warns about both).
- **Title and register review.** Manifest title is *Vertex Cover in
  Fibonacci Time*; authors Jan Dreier + Claude Fable 5. `abstract.md` is
  rewritten from the S0 draft (it now says the proof ships) and
  `notes.md` is new — both in the register of `ram-linear-time`'s.
- **Nothing is provisional.** `lax init` reached the server, so the id
  **Lax15 was server-allocated**, not guessed; no id fix-up is pending.
- README's `ram-linear-time` entry still describes Lax11 as carrying "a
  word-RAM surface", which the Lax13 extraction moved out. Left alone —
  not this task's file to rewrite, but worth a line when you next touch
  it.

State: three files changed this session (`vertex-cover-fibonacci/
abstract.md`, `vertex-cover-fibonacci/notes.md`, `README.md`); no Lean
edits, no concept edits, no generated files staged. `build-output.json`
refreshed and left untracked as intended.
Next: nothing on rung A. The orchestrator proceeds to a **rung B**
attempt (1.4656^k, branch on degree ≥ 3 with a path/cycle solver) as a
*second* campaign inside this same submission — a second theorem concept
with its own named recurrence. Rung A's files are finished and will not
be touched by it.
Decisions:
(1) The abstract carries three numbers a reader could check and one
comparison: `fib(k+2) ≈ 1.17·φ^k` (the plan's "1.9" was wrong and is not
used), `c = 90300` against Lax11's `33300`, and the honest admission
that the `2^k` driver is the *cheaper* program on small instances —
followed by the doubled five-edge matching, where Lax11's `vcCom` takes
52554 steps and this one 4572. The sentence that carries the whole
framing is "This one sharpens that one; it does not unsay it."
(2) `notes.md` is a map, not a ledger, exactly as `ram-linear-time`'s:
it points at the module docstrings and at the `Main.lean` conclusion
annotation rather than repeating them, and the achieved constant appears
only in the abstract and in that annotation.
(3) The README entry spends most of its length on the relationship to
Lax11 (same admissible set, sharpening not replacing), because that is
the one thing a reader scanning the list could get wrong.

## VCF session 9 — 00:06 UTC
Milestone: B1 — done (all five deliverables; the abort valve is cleared
in one session, no second session needed)
Commits: d185064 `Lax15 vcfib: rung B solver, pure side — the
maximum-degree-two cost` (`Lax15Proofs/Solver.lean`, 966 lines, plus the
root-module import)
State: `lake build` green in `vertex-cover-fibonacci/proofs/` (3003
jobs), zero sorry, `lean_verify` on `ok_iff_compCost_le` and
`thinBlocks3_iff` gives the three background axioms only. Namespace
`Lax15Proofs.VC3`; rung A files untouched. What B2–B5 consume:
- `R G M : SimpleGraph (Fin n)` (`Adj a c ↔ G.Adj a c ∧ a ∉ M ∧ c ∉ M`),
  ties `edgeFinset_R : (R G M).edgeFinset = ResEdges G M`,
  `degree_R (hv : v ∉ M) : (R G M).degree v = resDeg G M v`,
  `degree_R_of_mem`, `degree_R_le_two`.
- `compEdges H C` (`{e ∈ H.edgeFinset | H.connectedComponentMk e.inf = C}`)
  with `mem_compEdges`, `sum_card_compEdges`, `sum_card_compEdges_R`;
  `compCost' H = ∑ C, ((compEdges H C).card + 1) / 2`,
  `compCost G M = compCost' (R G M)`, `compCost_eq_zero_iff`.
- `not_ok_of_lt_compCost (hdeg : ∀ v ∉ M, resDeg G M v ≤ 2)
  (hb : b < compCost G M) : ¬ Ok G M b`;
  `ok_of_compCost_le (hdeg) (hb : compCost G M ≤ b) : Ok G M b`;
  `ok_iff_compCost_le (hdeg) : Ok G M b ↔ compCost G M ≤ b`.
- transport: `three_le_resDeg_of_slots` (six slot bounds, three unmarked
  targets, three disequalities ⇒ `3 ≤ resDeg G M o`), `ThinBlocks3`,
  `thinBlocks3_iff : ThinBlocks3 g M ↔ ∀ v ∉ M, resDeg G M v ≤ 2`,
  `resDeg_le_two_of_thinBlocks3`.
Next: B2 — potential and transitions (`Lax15Proofs/Config3.lean`), per
the plan. Nothing from B1 is deferred.
Decisions:
(1) **The plan's upper-bound induction rule is wrong as written and was
replaced.** `vc-rung-b-plan.md` says to delete a degree-two vertex of an
edge-bearing component and cites `⌈e₁/2⌉ + ⌈e₂/2⌉ + 1 ≤ ⌈e_C/2⌉` for
`e₁ + e₂ = e_C − 2`; that inequality is false at `e₁ = e₂ = 1`
(`1+1+1 > 2`), and the five-vertex path realizes it — deleting the
middle vertex of `a−b−v−c−d` leaves two single edges, cost 2 either
way, so the step buys nothing. The two rules that do work: (i) if some
vertex has degree one, isolate its *neighbour* — the degree-one vertex
becomes isolated, so at most one piece keeps edges; (ii) otherwise every
degree is 0 or 2, isolate any endpoint of an edge — its two neighbours
stay in one piece, because otherwise the piece of one of them would be a
component with exactly one odd degree, which the handshake lemma forbids.
Case (ii) is the only place any real graph theory enters, and it needs
the handshake lemma *per component*: `sum_degree_comp`, proved by
restricting `H` to one component (`restrictComp`) and calling mathlib's
`sum_degrees_eq_twice_card_edges` on the restriction.
(2) Deletion is `isolate H v` (drop the edges at `v`, keep the vertex),
as the brief suggested: the vertex type never changes, so `H` and
`isolate H v` have components in the same family and `liftComp`/`fiber`
can compare them. The component bookkeeping is one lemma
(`compCost'_isolate_succ_le`): away from `v` the fibre is a singleton
with the same edges, so the whole comparison reduces to `v`'s own
component, which `split_bound` handles.
(3) Decidability: two file-local instances (`DecidableRel H.Adj`,
`DecidableEq H.ConnectedComponent`) fix one derivation of every
finiteness instance, so mathlib's `edgeFinset`/`degree`/`Fintype
ConnectedComponent` lemmas apply syntactically. They are `local`, so
nothing leaks; every exported statement is instance-free except the
`edgeFinset`/`degree` ties, and `sum_card_compEdges_R` /
`compCost_eq_zero_iff` are stated in `ResEdges` so B4 can count without
them.
(4) The two bounds pin `compCost` to the exact vertex cover number of a
maximum-degree-two graph (they are only jointly satisfiable if it is),
which is the internal consistency check the pure side gets in place of
`#guard`s — every definition here is noncomputable.

## VCF session 10 — 00:13 UTC
Milestone: B2 — done (all five deliverables, first-build green)
Commits: 8dce72b `Lax15 vcfib: rung B potential and transitions — the
branch recurrence` (`Lax15Proofs/Config3.lean`, 380 lines, plus the root
module import)
State: `lake build` green in `vertex-cover-fibonacci/proofs/` (3004
jobs), zero sorry, `#print axioms` on `step3_push`/`step3_flip`/
`pot3_init_le` gives the three background axioms only. Namespace
`Lax15Proofs.VC3`; rung A files untouched. What B3–B5 consume:
- `branchCount : ℕ → ℕ` with the concept's equation shapes verbatim
  (`| 0 => 1 | 1 => 2 | 2 => 3 | (b+3) => branchCount (b+2) +
  branchCount b`), `branchCount_zero/one/two` and `branchCount_add_three`
  all `@[simp]`, `branchCount_pos`, `branchCount_le_succ`,
  `branchCount_mono`. Values 1,2,3,4,6,9,13,19,28 (checked by `#eval`).
- `fPot3 b = 4 * branchCount b - 3` (values 1,5,9,13,21,33,49,73,109):
  `fPot3_zero/one/two`, `fPot3_add_three` (exact), `one_le_fPot3`,
  `fPot3_mono`, `fPot3_le_of_le`, `fPot3_push (1 ≤ b) : fPot3 (b-1) +
  fPot3 (b-3) + 3 ≤ fPot3 b`, and the two truncation identities
  `fPot3_push_one`, `fPot3_push_two`.
- `stackPot3`, `pot3`, `stackPotN3`, `potN3 (mode bud) (frs)`,
  `pot3_eq_potN3`, `pot3_init : pot3 ⟨[],0,k,a⟩ = fPot3 k + 1`,
  `pot3_init_le : … ≤ 4 * branchCount k`.
- `Sharp G : List (Frame n) → Prop` (`| [] => True | f :: fs =>
  (f.phase = false → 3 ≤ resDeg G (marked fs) f.v) ∧ Sharp G fs`) with
  `sharp_cons`, `Sharp.head`, `Sharp.tail`; `J3 G k C := J G k C ∧
  Sharp G C.frames`, `J3.j`, `J3.sharp`, `j3_init`, `ans3_eq`.
- the eight wrappers `step3_yes/no/stuck/push/exhausted/flip/
  flip_infeasible/pop`, each concluding `J3 G k C' ∧ pot3 C' + 1 ≤
  pot3 C`, with rung A's argument lists except: `step3_no` takes a plain
  `¬ Ok G (marked C.frames) C.bud`, and `step3_push` takes
  `3 ≤ resDeg G (marked C.frames) v`.
Next: B3 — the program `vcf3Com` and its smoke tests
(`Lax15Proofs/Program3.lean`), per the plan.
Decisions:
(1) **Seven of the eight `J`-halves are projected from S2 with `.1`, as
the plan hoped.** Only `step3_no` is restated (three lines from `J`'s
definition): S2's `step_no` bakes the counting guards `hdeg`/`hlt` into
its hypotheses and derives `¬ Ok` internally, so it does not factor
through a plain-`¬Ok` core. The solver's NO verdict now feeds `step3_no`
directly, which is what B1's `not_ok_of_lt_compCost` produces.
(2) **Every drop the plan calls exact is exact.** `fPot3_push` is an
equality at every `b ≥ 1` — `5 = 1 + (1+2) + 1` at `b = 1` and
`9 = 5 + (1+2) + 1` at `b = 2`, the recurrence above that — so the push
drop is exactly one; so are stuck, exhausted, pop, and the flip at
`d = 3`. The `−3` and the `+2` are load-bearing at exactly the places
rung A's were. Nothing needed loosening.
(3) The extra invariant clause is `Sharp`, quantified over frames the
way `Healthy` is (structural recursion with the below-frame marking
`marked fs`), not as a list-index quantifier — so it projects and
reassembles with `.1`/`.2` in every wrapper, and its preservation is one
term per transition. The feasible flip is the only consumer:
`Sharp.head` supplies `3 ≤ d`, which is what makes `fPot3 (b − d) ≤
fPot3 (b − 3)` and thus the drop.

## VCF session 11 — 00:50 UTC
Milestone: B3 — done (all four deliverables; every guard green on the
first run, no disagreement with the hand-derivations, nothing blocking)
Commits: 522d846 `Lax15 vcfib: rung B program and smoke — branch at
three, solve the rest` (`Lax15Proofs/Program3.lean`, 493 lines, plus the
root module import)
State: `lake build` green in `vertex-cover-fibonacci/proofs/` (3005
jobs), zero sorry, no warnings; rung A files untouched. Namespace
`Lax15Proofs.VC3`. What B4/B5 consume — the header comment of
`Program3.lean` is the ground truth, with the full name/layout table and
a pseudocode transcript of every block marked (A) where it is rung A's:
- reused **by name**: `readLoop`, `VC.pushFrame`, `VC.backtrackBody`
  (hence `VC.flipFrame`/`VC.popFrame`/`VC.rowStep`), `VC.recordFound`.
- re-typed: `ownerAdvance3`, `slotStep3`, `descendScan3` — the scan's
  per-owner register set changed (`t2` replaces `cnted`, `ro` is gone),
  so rung A's `ownerAdvance` would leave `t2` stale across owners.
- new: `neTest`, `dedupStep first second third` (the one dedup, used by
  both scans), `clearVis`, `countPush`, `solveSlot`, `expandBody3`,
  `drain3`, `rootStep`, `solveBlock`, `descendBody3`, `outerBody3`,
  `vcf3Com`, `vcf3Layout`, `vcf3Program`, `vcf3Com_ok`, `test`.
- layout: rung A's 26 scalars less `ro`/`cnted`, plus `t2`, `head`,
  `tl`, `s`, `tog`, `r` (30); arrays plus `vis`, `q` (10); temps 4.
Next: B4 — the two scan Run lemmas (`Lax15Proofs/Phases3.lean`):
`descendScan3_run` and `solve_run`. Split B4a/B4b if `solve_run` needs
its own session, as the plan allows.
Decisions:
(1) **No early exit in `descendScan3`** — the scan runs the full pass,
as rung A's does. The counter-forcing idiom was available and is
rejected on three grounds: the cost bound is identical (one pass over
`2m` slots, which the potential already pays for), the loop invariant
stays the plain "`found` says whether some owner below `j` has three
distinct unmarked targets" instead of carrying a disjunction for the
forced state, and the scan stays syntactically parallel to rung A's
`descendScan`, whose Run lemma B4 can then imitate line for line.
(2) The `seen/t1/t2` dedup is **one parameterized definition**,
`dedupStep first second third`, used by both scans; they differ only in
the commands hung on the first, second and third distinct target
(`skip, skip, recordFound` in the descend scan; `countPush, countPush,
skip` in the solver). B4's two Run lemmas cannot be single-sourced —
the actions differ — but the shape they walk is literally the same
term, which is the most the watch item can buy. A third distinct target
in the solver is **skipped, not counted**, so `s` never exceeds the
residual edge count even off the invariant; B4 shows the branch
unreachable.
(3) The queue is not reset between components (the CC idiom): `head`
and `tl` are set once per solver call and are monotone across its
components, with `vis` set before every enqueue, so `tl ≤ n` and `q`
has extent `n`. The toggle `tog`, by contrast, **is** reset at each
root — that is what makes `s` a sum of ceilings rather than one
ceiling, and `C₄ + C₆` is the guard that would catch a lapse (it would
answer `4` instead of `5`).
(4) Step counts, all first-run and all agreeing with hand-derivation.
Rung B: K₅ 14649 (`no`, k=3) / 12846 (`yes`, k=4); C₇ 7016 / 6981;
C₄+C₆ 9944 / 9909; K₄ 7442 / 6628; triangle+P₃+C₄ 9236 / 9201; bull
6618 / 5804; K₁,₄ 4511; P₄ 3358 / 3323; doubled 2K₂ 3780 / 3745;
repeat word 1974 / 1939; edgeless 712; empty 172; malformed halts at
137. Against rung A on the same words: **C₇ 17937 / 9776 (A) against
7016 / 6981 (B)** — the clean win, rung A branching through a Fibonacci
tree where rung B answers at the first leaf. `K₅` is 14782 / 12437 (A)
against 14649 / 12846 (B): a near tie, rung B ahead on the `no` and
behind on the `yes`, because both push three times on `K₅` at `k = 4`
and rung B additionally pays for a solver pass at the leaf. Rung A wins
the small constants: `K₄` 7512 / 6127 vs 7442 / 6628, `P₄` 3120 / 2505
vs 3358 / 3323, repeat word 1028 / 993 vs 1974 / 1939, doubled `2K₂`
1914 / 1879 vs 3780 / 3745. Two structural reasons, both expected and
both recorded in the file: rung A fuses its matching leaf into the
branching scan while rung B needs a second pass, and the layout has ten
arrays rather than eight, so every array access costs more machine
steps. Nothing here touches the asymptotics; the abstract's honest
comparison against Lax11 will want the same treatment at B7.

## VCF session 12 — 01:10 UTC
Milestone: B4 — partial (deliverable 1 done; `solve_run` split off, see Next)
Commits: ec4ac2f `Lax15 vcfib: rung B descend scan — the branching test at
three` (`Lax15Proofs/Phases3.lean`, new file + root import), ee322e5 `Lax15
vcfib: the solver's queue, its count and its dedup`, 2c558be `Lax15 vcfib:
the row scan's set of recorded targets`
State: `lake build` green in `vertex-cover-fibonacci/proofs/` (3006 jobs),
zero sorry, `#print axioms` on `descendScan3_run`/`countPush_run`/
`dedupCount_run` gives the three background axioms only; rung A untouched.
`Lax15Proofs/Phases3.lean` (1290 lines) holds, in order:
- `neTest_ne`/`neTest_eq`, `dedupFound_run` (the shared dedup with the
  descend scan's actions: five outcomes, only the five registers move).
- `SeenInv`/`thin_of_seenInv`/`pigeon3`, `ThinBelow`/`thinBelow_succ`/
  `thinBlocks3_of_thinBelow`, `Scanned3`, `ScanInv3`, and
  **`descendScan3_run`** — signature and numeral verbatim below.
- `Queue` (structure: card, hd, mem, all, inj) with `tl_le`, `tl_lt`,
  `push`; `countPush_run` (≤ 60); `dedupCount_run` (≤ 200).
- `resTgts` + `mem_resTgts`, `resTgts_start`, `resTgts_succ_of_marked`,
  `resTgts_succ_of_unmarked`, `resTgts_end`, `resTgts_mono`; `RowInv3`.
Next: B4b — `rowScan3_run` (its exact conclusion, cost shape and proof plan
are written out in `Phases3.lean` under "What is left of the row scan"),
then `drain3`/`rootStep`/`clearVis` and `solve_run`.
Decisions:
(1) **`descendScan3_run` is done and B5 can consume it now.** Statement:
`(hg : EncodesGraph g n G) (hm : edgeCount g = m) (hO : ∀ i ≤ n, O i =
offset g i) (hT : ∀ p < 2*m, T p = target g p) (h1B : 1 < B) (hnB : n < B)
(hmB : 2*m < B) {C : Config n} {τ : Env} (hRep : Rep n m O T C τ) : ∃ τ' K,
Run B descendScan3 τ τ' K ∧ Rep n m O T C τ' ∧ τ'.arrs = τ.arrs ∧ τ'.inp =
τ.inp ∧ τ'.out = τ.out ∧ ((τ'.vars "found" = 0 ∧ ThinBlocks3 g (marked
C.frames)) ∨ (τ'.vars "found" = 1 ∧ ∃ v : Fin n, (v:ℕ) = τ'.vars "v" ∧ v ∉
marked C.frames ∧ 3 ≤ resDeg G (marked C.frames) v)) ∧ **K ≤ 800 * (n + 2*m
+ 1)**`. Rung A's `Rep` was reused with no change at all: the scan moves
only `Scanned3` names (j, u, w, found, v, seen, t1, t2) and no array, so
`Rep.of_vars_eq` transports it exactly as on rung A. No rung-A file needed
touching, and none was.
(2) The scan's invariant carries `SeenInv` — "the registers describe the
current block exactly" — **only while the flag is down**. It cannot survive
the slot that raises the flag (that slot's target is by construction outside
`{t1, t2}`), and it is not wanted afterwards: once `found = 1` the verdict is
the witness already recorded, and `recordFound` keeps the first one. Guarding
the clause by `found = 0` is what makes the four dedup outcomes uniform.
Rung A's `ro`/`cnted` half of the invariant simply disappears.
(3) The solver's lower blocks are green and their statements are final:
`countPush_run` yields `Indicator (insert w V) VIS'` and `Queue (insert w V)
Q' head tl'` *in both branches* (an already-visited target makes `insert w V
= V`), which is what keeps the row scan's bookkeeping to one shape;
`dedupCount_run` reports the third-distinct branch (`ρ' = ρ ∧ seen = 2 ∧ w ≠
t1 ∧ w ≠ t2`) rather than refuting it, because the refutation needs the
block-level `resTgts ⊆ ResNbhd` and belongs to the row scan.
(4) **The toggle in closed form** (this is the arithmetic B4b needs, checked
on paper): with `e` edges counted since the toggle's reset, `s` has grown by
`⌈e/2⌉` and `tog = e % 2`; counting `c` more takes `s` to `s + (c + 1 −
tog)/2` and `tog` to `(c + tog) % 2`. Both are `omega`-provable per step
(`omega` handles `/2` and `%2`), and the per-row `c` is
`((ResNbhd G M u).filter (fun x => (u:ℕ) < (x:ℕ))).card`.
(5) **The cost of the solver must be amortized against `2m` by hand**: the
rung-B program has no slot counter (`sc`) where the CC campaign put one, so
the drain's `while_pot` potential has to read the queue array —
`60 * (2m − Σ_{i < head} blockLen (q i)) + 60 * (n − head)` — and the fact
that the sum stays `≤ 2m` is exactly `Queue.inj` plus the blocks being
disjoint intervals of `[0, 2m)`. `rowScan3_run`'s cost is therefore stated
per block (`≤ 300 * (offset (u+1) − offset u) + 10`) and not as a constant.
This is the one place where B4b's shape differs from `CCSearch.lean`'s.
(6) `rowScan3_run` was written in full and reverted rather than left
half-proved: the mathematics went through (all three case analyses close),
what did not converge in the time left was rewrite plumbing around
`Env.setVar` under `set` — the goals came back delta-expanded and the
`rw [e_j]`-style steps missed. B4b should build that lemma's clauses with
`simp only [vars_setVar]` normalisation (rung A's idiom) instead of naming
the updated environment with `set`, and should prove `hcardnew`/`hsnew`/
`htognew` as `have`s *before* the `refine` — that part was already working.

## VCF session 13 — 01:45 UTC
Milestone: B4b — partial (three of five lemmas; `solve_run` did **not**
land, see Decisions (1) for the continue/abort call)
Commits: 6323e0e `Lax15 vcfib: the solver's row scan — one block of one
dequeued vertex`, 016d681 `Lax15 vcfib: the clearing pass and one turn of
the drain`, c4051f3 `Lax15 vcfib: the drain and the sweep, written out`
State: `lake build` green in `vertex-cover-fibonacci/proofs/` (3006 jobs),
zero sorry, no warnings; rung A untouched. `Lax15Proofs/Phases3.lean` is
now 1900 lines and holds, past session 12's material:
- `eq_singleton_of_card_one` / `eq_pair_of_card_two`;
- **`rowScan3_run`** — `while j < jend do solveSlot` over one block, cost
  `≤ 300 * (offset g (u+1) - offset g u) + 10`, concluding
  `Indicator (V ∪ ResNbhd G M u) VIS'`,
  `Queue (V ∪ ResNbhd G M u) Q' head (τ'.vars "tl")`,
  `s' = s + (c + 1 - tog) / 2`, `tog' = (c + tog) % 2` with
  `c = ((ResNbhd G M u).filter (fun x => (u:ℕ) < (x:ℕ))).card`;
- **`clearVis_run`** (cost `≤ 20*n + 10`, needs `σ.vars "n" = n`);
- `Queue.advance`; **`expandBody3_run`** (one turn of the drain: dequeue,
  set the block up, scan it, `head := head + 1`; cost
  `≤ 300 * (offset g (u+1) - offset g u) + 60`);
- a doc section **"What is left of the solver"** with the full design of
  the three remaining lemmas — invariants, potentials, the pure-side
  identity — so the next session executes instead of re-deriving.
Next: B4c — `drain3_run` (the queue-reading potential, and the identity
`∑_{v ∈ C} c v = (compEdges C).card`), then B4d — the root sweep and
`solve_run`. Both are specified verbatim in that doc section.
Decisions:
(1) **Recommendation: `continue`, with a hard checkpoint.** The remaining
solver work is ~2 sessions (B4c drain, B4d sweep + `solve_run`), then B5
~1, B6 ~1–2, B7 ~0.5 — call it 4.5–5.5 sessions against the ~5 that fit
before the 06:00 local cutoff at the observed ~25 min cadence. That is a
coin flip, and it is a *free* coin flip: rung B is invisible to the
endorsement surface until B6 lands the concept, so a campaign that stops
half-way costs nothing but the sessions, and everything committed is
green. The honest checkpoint: **if `solve_run` is not green by ~02:40
UTC, stop and go to B7-style wrap-up**, because B5 and B6 together cannot
be done in under three sessions and B6 is the only milestone that changes
what is endorsed.
(2) `solve_run`'s shape is **changed** from the brief's, deliberately, and
the change is recorded in the file. It must conclude a run of the *whole*
`solveBlock`, final `ite` included — not of a `solveCore` prefix. Reason:
`solveBlock` is right-nested as `seq clearVis (seq … (seq rootLoop ite))`,
so a lemma about the prefix `seq clearVis (seq … rootLoop)` cannot be
composed with a run of the `ite` without a `Run` re-association, which
would need `BigStepB` inversion. Consuming it is *easier* this way: B5
does `Run.seq hscan (Run.ite_true … hsolve)` exactly as rung A's
`descendBody_run` does, and gets `Rep` of the new configuration directly.
The same trap bit `expandBody3_run`: its six set-up assignments are
packaged as a **continuation** lemma (`∀ c ρ'' Kc, Run B c ρ ρ'' Kc →
Run B (a₁; a₂; …; a₆; c) σ ρ'' (25 + Kc)`), not as a block, which is the
idiom to reuse wherever a program block is right-nested.
(3) `solve_run` needs `τ.vars "n" = n`, a hypothesis rung A never wanted:
`Rep` is silent about `"n"`, and both `clearVis` and the root sweep
compare against it. B5/B6 must thread it from the read phase. It is the
one interface surprise found this session.
(4) Session 12's repair advice (decision (6) of its entry) was right and
was followed: no `set` for the updated environments, `simp only
[vars_setVar]` normalisation, and `hcardnew`/`hsnew`/`htognew` proved as
`have`s before the `refine`. `rowScan3_run` then went through in four
build rounds. The one arithmetic trap worth recording: the invariant
clause `s ≤ s₀ + 1` is **not** provable from the old closed form plus the
`countPush` disjunct — it needs the *new* closed form together with
`card ≤ 2`, so `hsnew` has to be proved before the clause that uses it.

## VCF session 14 — 02:20 UTC
Milestone: B4c — **done**. `solve_run` is green; B4 is closed.
Commits: 5e89f59 `Lax15 vcfib: the drain, and what one component
contributes`, cb43771 `Lax15 vcfib: the root sweep — every component met
exactly once`, 60d71dc `Lax15 vcfib: the solver block, run whole`,
f911e3f `Lax15 vcfib: point the solver's design note at the file that
executes it`
State: `lake build` green in `vertex-cover-fibonacci/proofs/` (3007
jobs), zero sorry, no warnings; `#print axioms solve_run` gives the three
background axioms only; rung A untouched. The new file
`Lax15Proofs/Sweep3.lean` (≈960 lines, imported from the root module)
holds, in order:
- `upDeg`, `compVerts`, `eq_mk_inf_sup`, `notMem_of_mem_compVerts`,
  `card_fiber_compEdges`, **`sum_upDeg_compVerts`** (the pure identity),
  `mem_of_reachable_closed`, `sum_upDeg_le_comp`;
- `blockLen`, `sum_blockLen_range`, `sum_blockLen_le`, `sum_range_queue`,
  `qsum`/`qsum_eq` (the queue-reading potential's vocabulary);
- **`drain3_run`**, **`visComps`**/`sum_comp_le`/
  `resNbhd_subset_compVerts`/**`rootSweep_run`**, `rep_of_solver`,
  **`solve_run`**.
Next: B5 — `outerBody3_run` in `Lax15Proofs/Loop3.lean`. `solve_run` is
consumed exactly as rung A's `descendBody_run` consumes its leaf lemmas:
`Run.seq hscan (Run.ite_true hfound hsolve)`.
Decisions:
(1) **`solve_run`'s signature, verbatim, for B5**:
`(hg : EncodesGraph g n G) (hm : edgeCount g = m) (hO : ∀ i ≤ n, O i =
offset g i) (hT : ∀ p < 2*m, T p = target g p) (h1B : 1 < B) (h2B : 2 < B)
(hnB : n + 2 < B) (hmB : 2*m < B) {C : Config n} {τ : Env}
(hRep : Rep n m O T C τ) (hbudB : C.bud + 1 < B) (hn : τ.vars "n" = n)
(hthin : ThinBlocks3 g (marked C.frames))
(hvisE : ∃ VIS, τ.arrs "vis" = arrOf n VIS)
(hqE : ∃ Q, τ.arrs "q" = arrOf n Q) : ∃ τ' K, Run B solveBlock τ τ' K ∧
τ'.inp = τ.inp ∧ τ'.out = τ.out ∧ τ'.vars "n" = n ∧
(∃ VIS' Q', τ'.arrs "vis" = arrOf n VIS' ∧ τ'.arrs "q" = arrOf n Q') ∧
τ'.vars "s" = compCost G (marked C.frames) ∧
((compCost G (marked C.frames) ≤ C.bud ∧ Rep n m O T ⟨C.frames,2,C.bud,1⟩ τ') ∨
 (¬ compCost G (marked C.frames) ≤ C.bud ∧ Rep n m O T ⟨C.frames,1,C.bud,C.ans⟩ τ'))
∧ **K ≤ 700 * (n + 2*m + 1)**`.
(2) **Three interface facts B5/B6 must thread**, none of them in rung A's
`Rep`: `τ.vars "n" = n`, and the two array extents `vis`/`q`. All three
are set by the read phase and preserved by every block (stores use
`List.set`, which preserves length), and `solve_run` hands all three back,
so the outer loop can carry them as a side invariant next to `Rep`. The
`n + 2 < B` is one tighter than rung A's `n + 1 < B` — it pays for
`s ≤ n` at the last comparison; the endgame constant swallows it.
(3) The plan put these lemmas in `Phases3.lean`; they are in a **new
file** `Sweep3.lean` instead, purely for iteration speed (editing
`Phases3.lean` recompiles 1900 lines on every round). `Phases3.lean`'s
design note now points at it. B5's `Loop3.lean` imports `Sweep3.lean`.
(4) The design in session 13's note went through **unchanged** in
substance; two shape choices are worth recording. The drain's invariant
carries *two* queues over the same array — `Queue V Q head tl` for the
visited set and `Queue W Q head head` for the expanded prefix — which
makes the toggle's closed form a sum over a `Finset` rather than over
queue indices, and makes `W = V` at the exit a cardinality argument. The
sweep indexes its cost by `visComps V := V.image (connectedComponentMk ·)`
rather than by the brief's `P r`; an unmarked unvisited root inserts
exactly one new component, and at `r = n` the unmet components carry no
unmarked vertex hence no edge, so `Finset.sum_subset` finishes.
(5) Lean traps met, for whoever writes B5. `Run.assign`/`Run.ite_*`
inside a `refine`'s anonymous constructor leave the command as a
metavariable and `.mono (by simp; omega)` then fails on `Cond.size`
atoms: build the whole run as a **`have` with the target type
`Run B <block> τ τ' K` spelled out**, then `.mono`. `set x := e with h`
is a trap in `simp only` rewrites (the `have`s built from it do not fire);
prefer explicit `have e1 : ρ.vars "head" = … := by simp` and `rw`.
`Rep.of_frames_eq` does **not** apply here — it wants `τ'.arrs = τ.arrs`
and the solver writes `vis`/`q` — hence `rep_of_solver`, which takes the
per-array frame; B5 wants the same for anything that touches an array.

## VCF session 15 — 02:30 UTC
Milestone: B5 — **done**. `outerBody3_run` is green; B5 is closed.
Commits: 1cda358 `Lax15 vcfib: rung B outer body — one turn of the search,
eight transitions`
State: `lake build` green in `vertex-cover-fibonacci/proofs/` (3008 jobs),
zero sorry, no warnings; `#print axioms outerBody3_run` gives the three
background axioms only; rung A untouched. New file
`Lax15Proofs/Loop3.lean` (≈610 lines, imported from the root module,
namespace `Lax15Proofs.VC3`) holds `SideInv` with `n_eq`/`vis`/`q`/
`transport`, `descendBody3_run`, `backtrackBody3_run`, `outerBody3_run`.
One numeral for all eight cases: `1600 * (n + 2*m + 1)` for the two
bodies, `1610 * (n + 2*m + 1)` for `outerBody3_run`.
Next: B6 — the concept `concepts/Lax15/VertexCoverBranch.lean`, the
`while_pot` loop over `pot3` with `Rep ∧ SideInv ∧ J3` as invariant, the
assembly (rung A's read phase, which must additionally deliver
`SideInv`), and the endgame.
Decisions:
(1) **`outerBody3_run`'s signature, verbatim, for B6**:
`(hg : EncodesGraph g n G) (hm : edgeCount g = m) (hO : ∀ i ≤ n, O i =
offset g i) (hT : ∀ p < 2*m, T p = target g p) (h2B : 2 < B)
(hnB : n + 2 < B) (hmB : 2*m < B) (hkB : k + 1 < B) {C : Config n}
{τ : Env} (hRep : Rep n m O T C τ) (hside : SideInv n τ) (hJ : J3 G k C)
(hmode : C.mode < 2) : ∃ (C' : Config n) (τ' : Env) (K : ℕ),
Run B outerBody3 τ τ' K ∧ Rep n m O T C' τ' ∧ SideInv n τ' ∧ J3 G k C' ∧
pot3 C' + 1 ≤ pot3 C ∧ τ'.inp = τ.inp ∧ τ'.out = τ.out ∧
K ≤ 1610 * (n + 2*m + 1)`.
`SideInv n τ := τ.vars "n" = n ∧ (∃ VIS, τ.arrs "vis" = arrOf n VIS) ∧
(∃ Q, τ.arrs "q" = arrOf n Q)` — the packaging of session 14's three
interface facts, with `SideInv.transport` (`"n"`, `vis`, `q` unchanged ⇒
carried) for the read phase and anything else that has to move it.
(2) **`descendScan3_run` gained a conclusion clause**: `∀ y, ¬ Scanned3 y
→ τ'.vars y = τ.vars y`, inserted after `τ'.out = τ.out` and before the
verdict disjunction. It was already in the invariant (`hfr'`), just not
exported; without it `"n"` cannot cross the scan. Anyone destructuring
that lemma must add the extra binder.
(3) The value bound is rung A's with `hnB : n + 1 < B` raised to
`n + 2 < B` (session 14's note); nothing else changed, and every rung-A
`by omega` side condition went through unchanged.
(4) The backtrack half could **not** reuse rung A's `backtrackBody_run`:
that lemma existentially quantifies the new configuration, so which of
T5–T8 fired is not recoverable, and `J3`/`pot3` need to know. The proof
is therefore rung A's, copied and re-bookkept — the `Com`, the row scan,
the unwind loop and every `Run` step are identical, only `step_*` became
`step3_*` and `hJ.x` became `hJ.j.x`. If a third rung ever happens, the
right move is to factor rung A's backtrack into four per-case lemmas.
(5) No Lean traps this session: rung A's `refine (Run.seq …).mono ?_`
idiom worked as written, session 14's metavariable trap did not bite
because the command is fixed by the goal in every case here. The whole
file compiled on the second attempt (the first missed
`import Lax15Proofs.Config3` — nothing else imports it).

## VCF session 16 — 02:39 UTC
Milestone: B6 — **done**. The rung-B concept is on the surface and
discharged in the same commit; rung B is complete but for B7's wrap-up.
Commits: efe81a6 `Lax15 vcfib: rung B concept and endgame — the branch
count, discharged`
State: `lake build` green in `vertex-cover-fibonacci/concepts/` (1033
jobs) and `proofs/` (3010 jobs), zero sorry, no warnings, diagnostics
clean on both new files; rung A untouched.
- **Concept** `concepts/Lax15/VertexCoverBranch.lean`, namespace
  `Lax15.VertexCoverBranch`, imported from the concepts root. One def,
  `branchCount` (the plan's four equations verbatim), and one axiom,
  `exists_branchTime_program_vertexCover`, statement verbatim from
  `vc-rung-b-plan.md`. Imports are rung A's less `Mathlib.Data.Nat.Fib.
  Basic`, which nothing in the file uses. Prose in the rung-A register:
  the deg-3 branching rule, why the count is stated by its defining
  recurrence rather than a rounded power of β ≈ 1.4656, the
  max-degree-two leaf and its `⌈e/2⌉` per component, and
  `branchCount k ≤ fib (k+2)` with the two value lists. `# Formalization
  notes` carry the initials-are-the-exact-leaf-counts item and the
  admissible-set-unchanged item.
- **Endgame** `proofs/Lax15Proofs/Main3.lean` (≈470 lines, namespaces
  `Lax15Proofs.VC3` and `Lax15Proofs.VC3Main`, in the proofs root):
  `potN3_eq`, `searchLoop3_run`, `vcf3Ext`, `const3_eq`,
  `branchCount_eq`, `vcf3Com_run`, `vcf3Com_solves`,
  `exists_branchTime_program_vertexCover` with the house conclusion
  frontmatter, and the `example := rfl` identity check.
- `#print axioms` on the endgame: `propext`, `Classical.choice`,
  `Quot.sound` — the three background axioms only.
**Achieved constant: 318500**, factored `49 · 6500`. `49` is
`vcf3Layout.const` (ten arrays, so one index computation is twelve
instructions); `6500` is the IMP+ cost per entry of the word, itself
`1614 · 4 + 44`: `1610` for a turn of `outerBody3_run`, `4` for the
loop test, times the four units of `pot3 ⟨[], 0, k, 0⟩ ≤ 4·branchCount k`,
plus `44` of slack that swallows the read phase (`12n + 24m + 37`) and
the loop rule's `+4`. Rung A's constant was `90300 = 43 · 2100`.
Next: B7 — abstract, notes, README second-rung updates, `lax build`,
morning block. No submit (VF8 stands).
Decisions:
(1) **`branchCount` did NOT bridge by `rfl`.** `example (b : ℕ) :
VC3.branchCount b = Lax15.VertexCoverBranch.branchCount b := rfl` fails
with a type mismatch even though the two definitions have identical
equations — the structural-recursion elaborations do not unify at a
variable argument. `branchCount_eq` proves it by
`induction b using branchCount.induct` (three `rfl` base cases, then
`rw [branchCount_add_three, ih1, ih2]; rfl`, the final `rfl` being the
concept side's equation at `b + 3`, which *does* reduce because the
constructors are exposed). The endgame states the theorem against the
concept's `branchCount` and rewrites with `branchCount_eq` in the single
`hT` obligation of `computesInTime_of_solves`. The plan's watch item
"the two must be definitionally identical so the endgame's `rfl`
identity check survives" was over-cautious: the identity check compares
*statements*, and the statement uses the concept's def, so it passes
regardless.
(2) The whole file compiled on the **first** attempt. Rung A's
`Main.lean` is a complete template: the only edits were `vcfExt →
vcf3Ext` with `vis`/`q` at extent `n` (so `hrest₇` grew two more
hypotheses and `hvis₇`/`hq₇` were split out), one extra `hn₇` for
`SideInv`'s `"n"` clause, `SideInv` threaded through the loop invariant
and the `hstep` obligation, `hJ'.x → hJ'.j.x` throughout, and the
numerals. Session 15's `descendScan3_run` extra binder never surfaced —
nothing here destructures it.
(3) Nothing is open on the mathematics. The surface is now two theorem
concepts and one definition; `notes.md` and `abstract.md` still describe
one, which is exactly B7's job.

## VCF session 17 — 02:44 UTC
Milestone: B7 — done (all six deliverables; the night is closed)
Commits: 205723b `Lax15 vcfib: night wrap-up — two rungs, abstract, notes,
retitle` (`vertex-cover-fibonacci/abstract.md`, `notes.md`,
`manifest.yaml`, root `README.md`; no Lean edits, no generated files
staged, no `lax submit`)

### For Jan, in the morning

**Lax15 `vertex-cover-fibonacci/` carries two theorem concepts and
discharges both.** Vertex cover on the word RAM, same machine, same
encoding, same admissible set as Lax11's `2^k` statement — character for
character, so all three bounds are claims about literally the same
inputs — with the base of the exponential lowered twice:

- `Lax15.VertexCover.exists_fibTime_program_vertexCover` —
  `c · fib(k+2) · (|x|+1)`, base φ ≈ 1.618 (`fib(k+2) ≈ 1.17·φ^k`),
  **c = 90300 = 43 · 2100**. Branch on a vertex of residual degree ≥ 2;
  the leaf is a matching, answered by counting.
- `Lax15.VertexCoverBranch.exists_branchTime_program_vertexCover` —
  `c · branchCount k · (|x|+1)`, base the real root β ≈ 1.4656 of
  `x³ = x² + 1`, **c = 318500 = 49 · 6500**. Branch only at residual
  degree ≥ 3; the leaf has maximum residual degree 2, i.e. paths and
  cycles, and is solved exactly by one BFS sweep summing `⌈e/2⌉` over
  components. `branchCount k ≤ fib (k+2)` everywhere, strict from k = 3
  (1,2,3,4,6,9,13,19,28 against 1,2,3,5,8,13,21,34,55).

`lax build vertex-cover-fibonacci` green (concepts 1033 jobs, proofs
3010); `build-output.json` records **both** conclusions with **empty
assumptions**; `#print axioms` on both endgames gives `propext`,
`Classical.choice`, `Quot.sound` only; zero `sorry` anywhere; every
rung-A file untouched by the rung-B campaign.

The night, in order:
- Rung A (fib), sessions 1–8: aa8359a scaffold · 80adfd3 residual graph
  side · 135259b config side · 0bcb6f3 program + smoke · 6cd8e6e
  inner-loop run lemmas · 179742a outer body · 12fddcc assembly and
  endgame · 72fffb8 wrap-up.
- Rung B (branchCount), sessions 9–16: d185064 solver pure side ·
  8dce72b potential and transitions · 522d846 program + smoke · ec4ac2f
  descend scan · ee322e5, 2c558be, 6323e0e, 016d681, c4051f3, 5e89f59,
  cb43771, 60d71dc, f911e3f the solver, block by block · 1cda358 outer
  body · efe81a6 concept + endgame.
- This session: 205723b wrap-up.

**Two plan-level corrections were found and machine-checked on the way.**
Both were errors in the plans, not in the formalization, and both are
recorded where they were found:
1. *(session 2, rung A)* VF3's descend test was **unsound for the claimed
   bound**. The Lax11 encoding may name a neighbour of a vertex several
   times, so counting unmarked *slots* branches at a vertex of residual
   degree 1, where the Fibonacci recurrence fails: on `k` disjoint edges
   with every slot doubled the planned program searches a `2^k` tree
   against a claimed `c·fib(k+2)·(|x|+1)`. The algorithm was correct, just
   not Fibonacci. Repair (VF3 rev 2, implemented): the test compares
   *targets*, and the residual edge count is capped at one per block. The
   smallest witness, a nine-number word, is `Repeats.lean` in the proof
   package — a permanent machine-checked warning.
2. *(session 9, rung B)* B1's upper-bound induction rule — "delete a
   degree-two vertex" — is **false**: `⌈e₁/2⌉ + ⌈e₂/2⌉ + 1 ≤ ⌈e_C/2⌉`
   fails at `e₁ = e₂ = 1`, and the five-vertex path realizes it. The
   corrected rule, proved: isolate the *neighbour* of a degree-one vertex
   if one exists, else every degree in an edge-bearing component is 2 (by
   the handshake lemma per component) and any endpoint of an edge works.

Deliberately left for you, none of it blocking:
- **`lax submit vertex-cover-fibonacci`** — not run, per VF8. The draft
  is ready; submitting is your call, and registering will need Lax11 and
  Lax13 registered first (the build warns about both).
- **The retitle is the orchestrator's call and you should veto it
  freely.** `manifest.yaml` now says **"Vertex Cover Below Two to the k"**
  instead of *"Vertex Cover in Fibonacci Time"*, under your "push the
  base as far as possible" mandate: with two rungs on the surface the old
  title names only the weaker one. It is one line in `manifest.yaml`,
  trivially revertible, and nothing depends on it. The directory name
  stays `vertex-cover-fibonacci/`.
- **Two abstract wording flags carried from session 8**, both still live:
  (a) the asymptotic gloss is `fib(k+2) ≈ 1.17·φ^k` — the figure `1.9`
  that appears in `vc-fib-plan.md`'s prose is simply wrong (the constant
  is `φ²/√5`) and is used nowhere; (b) the abstract admits in its own
  voice that the `2^k` driver is the *cheaper program* on small shared
  instances and that each rung buys its smaller base by paying a larger
  constant (33300 → 90300 → 318500). Both are honesty calls, not facts in
  dispute — say the word and either can be softened or cut.
- **One concrete measured pair now in the abstract**, so a reader can
  check the claim is about the exponent and not the constant: the
  seven-cycle at k = 3 takes 17937 steps under the fib program and 7016
  under the branch program.
- README's `ram-linear-time` entry still describes Lax11 as carrying "a
  word-RAM surface", which the Lax13 extraction moved out. Flagged in
  session 8, still true, still left alone — not this campaign's file to
  rewrite.

**The machine model was never touched.** VF5 held all night: no
multiplication and no division in either program, `fib` and `branchCount`
are never computed at run time, and nothing outside
`vertex-cover-fibonacci/` was edited by any of the seventeen sessions.

State: four files changed this session, committed; `NIGHTLOG.md` appended
and left unstaged as the protocol requires; `build-output.json` refreshed
and untracked.
Next: nothing. The night's plan is complete — `vc-fib-plan.md` and
`vc-rung-b-plan.md` are both closed. The next action is Jan's:
`lax submit vertex-cover-fibonacci`, or the retitle veto.
Decisions:
(1) The abstract was **extended, not rewritten**: the rung-A framing
sentences that carry the whole story ("This one sharpens that one; it
does not unsay it", the quantifier-order paragraph, the
falsifiable-at-every-k argument) are kept verbatim or lightly
generalized to three rungs, and two paragraphs were added — the deg-3
rule with its `⌈e/2⌉` leaf, and the constants ladder with the measured
pair. The repeat-encoding subtlety survives as one sentence inside the
constants paragraph rather than as its own.
(2) `notes.md` splits the module map into two per-rung sections and adds
a bullet on **where `branchCount` lives and why**: inside the theorem
concept as the claim-local object (the `ccLabels` placement rule), and on
the surface at all only because mathlib names the sequence nowhere — the
first self-defined object this ladder has needed.
(3) The README entry keeps its emphasis on the relationship to Lax11 (the
one thing a list-scanner could get wrong) and adds the second rung in the
style of the multi-concept entries, naming the count and its base.

## VCF orchestrator coda — 2026-07-28 04:47 CEST
The relay is closed: 17 Opus sessions, 24 commits (aa8359a..205723b),
zero sorry anywhere, both rungs discharged and wrapped 74 minutes
before the 06:00 cutoff. Planning artifacts left untracked for Jan,
house-style: `vc-fib-plan.md`, `vc-rung-b-plan.md`,
`vc-fib-night-brief.md`.
Decisions I own (not the sessions): opening the concept-surface gate
under Jan's evening mandate; VF3 rev 2 after session 2's finding; the
rung-B go at 03:00 and the go-on at session 13's checkpoint; the
retitle to "Vertex Cover Below Two to the k". All flagged inline where
they bind; all trivially revertible.
Memory updated (`vc-ladder-lax15`). Nothing was submitted; the machine
model was never touched; rung C (folding/struction) remains sketched
only.

## Housekeeping — 2026-07-28
All root-level plan artifacts moved to `plans/<submission-name>/`; the
until-then-untracked night artifacts (`vc-fib-plan.md`, `vc-rung-b-plan.md`,
the three `*-night-brief.md`, `vc-contracts/`) are now tracked there too.
Two renames: `todo.md` → `implementation-log.md`,
`cc-night-brief.md` → `ram-stack-night-brief.md`. Earlier entries in this
log cite the old root paths; `plans/README.md` has the old→new map.

## IMP+ toolkit P1 — the frame rule — 2026-07-28
`Lax13Proofs/Frame.lean` lands: `Com.wvars` / `Com.warrs` / `Com.reads`
with decision procedures, and `Run.frame_var` / `frame_arr` /
`frame_inp` proved by the induction `BigStep.out_eq` already did for the
output tape. A `Decidable` instance for the pre-existing `Com.NoWrite`
joins it, so all four `Env` fields are framed by one `by decide` each.
Retrofit: `readLoop_run` (`Lax11Proofs/CCPhases.lean`) dropped three of
its four frame conjuncts and `ReadInv` dropped its `σ` parameter with
them; all twelve call sites across Lax11 and Lax15 rewritten and green,
zero `sorry`. The second half of P1's acceptance — `Scanned` /
`not_scanned_ne` in Lax15's `Phases.lean` — is surveyed but not done,
and is the next session's first task; the survey, the two shape
decisions taken, and the timings are in
`plans/word-ram/imp-toolkit-plan.md`.
Working model from here, Jan's call mid-session: Fable supervises and
Opus subagents write the proofs.

## IMP+ toolkit P3 — the `run_vcg` tactic — 2026-07-28
(P2, the `Spec` triples, landed earlier today; its record is in the
plan.) `Lax13Proofs/Tactic.lean` lands: `run_vcg` symbolically
executes a concrete straight-line `Com` against a `Spec` or legacy
existential goal — walks skip/assign/store/seq/ite, splits each `ite`
on its arithmetic test, discharges or defers the `< B` obligations,
checks the cost, and leaves one postcondition goal per path.
`run_vcg [spec]` steps over a named sub-program (or loop) by its
specification instead of into it. Written by an Opus subagent per the
working model; both VCF-session-6 hard requirements (have-chain
construction, no `if_neg (by decide)` in rewrite lists) honored.
Acceptance passed: `countBlock_spec` 21 proof lines → 2,
`seenBlock_spec` 51 → 3, statements byte-for-byte unchanged,
elaboration of `Phases.lean` neutral (≈21 s wall before and after),
all three proofs packages green, zero `sorry`. Deviations (renamed
from `run_step`; bracket-argument specs instead of an attribute set;
`< B` goals deferred individually) recorded in the plan's P3 as-built
notes, with the P4 handoff: `Lib` postconditions as `abbrev`,
operations as `Spec`s consumed through `run_vcg [·]`.

## IMP+ toolkit P4 — the data-structure library — 2026-07-28
`Lax13Proofs/Lib/` lands in four reviewed commits (P4a–P4d): `Basic`
(shared cell update + the machine-run demo driver), `Ind`, `Stack`,
`Trail`, `Queue`, `Csr` — ~2,850 lines, each module an `arrOf`-cheap
abstraction relation, name-parameterized `Com` operations with one
`Spec` apiece, and a worked example `#guard`-checked through the
compiler and the machine. Four Opus subagents wrote them against the
shape note fixed in `Ind`'s header; the supervisor re-read every line
at the end (one rename: `Csr.step` → `Csr.off_le_succ`). Consumer
evidence drove three plan deviations, all recorded: Queue's `advance`
split into `front`+`advance`, `drain` a body-open combinator over
`while_potential`, Trail logging bare indices with undo-to-zero. The
kit's loops: `Trail.unwind` (`while_count`, one `Spec` with the loop
inside), `Queue.drain_spec` and `Csr.rowScan_spec`/`ownerScan_spec` —
the last hiding the two-term amortized potential from the caller
entirely. P4 acceptance passed for real: `rowLoop_run` re-proved
through `rowScan_spec` with its statement byte-for-byte unchanged,
elaboration neutral; five of the repo's seven scan-shaped loops are
direct combinator instances. All three packages green, zero `sorry`.
Next: P5, the Lax11 CC pilot retrofit behind the 40% gate; three
pre-P5 flags (tryClose state-restore, run_vcg first-match spec
selection, Phases3's local `Queue` name) in the plan's P4 as-built.

## Nowhere dense MC — campaign plan rev 1 — 2026-07-28
The campaign for "FO model checking is FPT on nowhere dense classes"
is planned: `plans/nowhere-dense-model-checking/nd-mc-plan.md`. Route:
the Dreier–Toruńczyk rank-preserving locality theorem (arXiv
2606.23180, syntactic rewriting) replaces the ugly-and-broken GKS
rank-preserving Gaifman machinery, and its greedy scatter sentences
delete the distance-r independent set subroutine (GKS §5) outright;
the assembly is the splitter game in the notes-ch. 4 UQW form on top
of Lax12's endorsed theorems (UQW, subpolynomial wcol, density),
sparse neighborhood covers from wcol orderings, and a Lax13/Lax11 RAM
realization consuming the IMP+ toolkit. Headline C0 mirrors the
Courcelle house form with an n^(1+ε) side-condition bound and
`Lax12.NowhereDense` verbatim as hypothesis. Nine phases P0–P8 with
gates after P0 (design note checked against the to-be-fetched GKS
§6/§8 sources), P1 (surface freeze), and P4 (math core done, RAM
half re-forecast). Five open questions for Jan: id slot (Lax3/Lax4),
bound form, colored-graph-level locality surface, citable-concept
set, batch-form splitter game. Nothing built; no submission folder
yet; the references fetch (gks, mw, rploc) is P0's first task.

## Nowhere dense MC — plan rev 2: isolation, not removal — 2026-07-28
Jan's call, same session: the splitter isolates its batch — incident
edges deleted, vertices kept, win = edgeless arena — instead of
removing it. Vertices never disappear, so rev 1's substitution
readout (virtual vertices) and the avoid-W side conditions of the
removal translation are gone; the per-level translation is one exact
quantifier-free atom rewrite through W-membership, old-neighbor and
capped-distance-profile colors, with the capped W-distance matrix
selecting among finitely many precomputed formula variants; the base
case is "edgeless arena: evaluate by lookup"; on the RAM the graph is
materialized once and every arena is a vertex mask + isolation bits +
profile arrays, wound back by Trail. Locality still applies at every
arena — profile disjuncts are not new-metric guards — so the mutual
typeTables/sentenceEval shape stays. D1, D8–D11, L2–L4, budgets and
R2 rewritten in the plan; Q5 resolved (isolation game is the surfaced
concept); estimate down to 30–48 sessions.

## Nowhere dense MC — plan rev 3: accepted, wrapped for launch — 2026-07-28
Jan's wrap-up, same session: the plan is accepted; execution starts
next session at P0 (fetch gks 1311.3899, mw 2502.18065, rploc
2606.23180 into references/, write the design note, gate with Jan
before any Lean). Two rev-3 changes: the RAM half P5–P7 is gated on
the IMP+ toolkit campaign closing — the math core P0–P4 is ungated
and the two campaigns meet at the D12 gate — and Q1–Q4 are closed by
their recommended defaults (Lax3 init slot, folder
nowhere-dense-model-checking, Lax4 left free for a future merge-width
submission; real-ε side-condition bound; colored-graph locality
surface; four citable theorems), all revisable until the P1
statement freeze.

## ND-MC P0 — 2026-07-28
Sources fetched with license READMEs: `references/rploc` (2606.23180,
CC-BY), `references/gks` (1311.3899, arXiv nonexclusive),
`references/mw` (2502.18065 v1+v2, CC-BY, both kept for the
error-fix diff). Design note written:
`plans/nowhere-dense-model-checking/nd-mc-design.md`, settling
(a)–(e). Headlines: the isolation rewrite needs no matrix-indexed
variant family (profile colors at batch vertices carry the matrix —
D8 tightens, R2 shrinks); radius schedule flat at ρ* = ρ⁻(0,q); R1
reduced to one named kernel (augmentation density theorem, NO05, not
in the notes, not in Lax12 — budgeted 3–5 sessions inside P6);
notes' Lem 4.2 constant slip (2s+1 vs 2s+2) recorded; isolation-form
win proof checked against Lax12's walk-based `deleteVerts` UQW —
zero impedance. Gate open: Jan reads the design note; P1 does not
start before that.

## ND-MC P1 session 1 — 2026-07-28
Gate cleared: Jan approved the design note; plan rev 4 folds its
three deltas (D8 variant family dropped for profile colors, D4 sharp
ρ* = ρ⁻(0,q) schedule, R1 = augmentation density theorem in P6).
Lax3 claimed (`lax init --id Lax3`, the reserved slot), packages
scaffolded, path-requires on Lax12/Lax13/Lax11, manifest + draft
abstract. Full L0 concept surface written and green: ColoredGraphs
(Coloring, WithinDist, ball), FirstOrder (FO/rank/Sat), DistFO
(rhoMinus/rhoPlus, syntax incl. exL with syntactic guard radius,
Sat, rename, DRank predicate with ≤-relaxed guard — source Obs 4
forces it, recorded in notes — IsLocal, WithinDistIn, SatWithin,
SemanticallyLocal), ScatterSentences (ScatterChoice per (G,r,X),
maxChoice + greedyChoice both with real spec proofs, ScatterSentence
+ Sat + DRank), Locality (BC reification + `locality` axiom),
NormalForm (verum/conj/exUs/scatterFml + `normalForm` axiom; split
from Locality for the one-statement rule), SplitterGame
(SplitterWins by recursion on the round budget — kernel rejects the
∀/∃ nested inductive; both moves are Lax12 deleteVerts),
NowhereDenseSplitter (`splitterWins_of_nowhereDense`),
NeighborhoodCovers (IsNeighborhoodCover, center-indexed),
NeighborhoodCoverBound (`exists_neighborhoodCover_degree_wcol`,
class-free wcol-degree form), ModelChecking (C0 verbatim from the
plan, Courcelle idiom + real-ε T bound). Proofs-side: WalkDistance
API incl. the metric-kernel decomposition
`withinDist_deleteVerts_or_through`. Opus wrote units A and B; the
supervisor wrote C and D and reviewed everything against the
sources. `lax build` green end to end; axiom audit: exactly the five
declared axioms (locality, normalForm, splitter win, cover bound,
C0) + propext/choice/Quot.sound. Next: Jan endorse-reviews the
surface — the P1 statement freeze — then P2 (locality engine, three
Opus tracks).

## ND-MC P2 session 1 — 2026-07-28
Gate cleared in-session: Jan endorsed the full Lax3 surface on the
orchestrator's review package; statements frozen at 514cc4c. P2
(locality engine) ran as three parallel Opus tracks over a
supervisor-written Horizon prelude (eq. (1), exact ρ⁺ = 9^k·ρ⁻,
monotonicity both ways and antidiagonal, strict chain). Landed,
sorry-free, kernel axioms propext/choice/Quot.sound only:
(a) SemLocal — Lem 5 as a strengthened agreement (Sat ↔ SatWithin D
for every D containing the ρ⁻-balls), arity-independent primed forms,
the source's k ≥ 1 dropped (sound under the frozen exL semantics,
argued in the module docstring); (b) Clusters + ScatterCore — Vitali/
Cor 10 packaged as a ClusterSystem structure with the exact scale
R = r·9^t, t < k (the finite radius range farQuant's case split
needs), and Lem 11 verbatim with the Maximal hypothesis in
ScatterChoice.spec's shape; the source's last-paragraph counting gap
closed via proper subset + ncard_lt_ncard, recorded in the module;
(c) SyntaxLemmas — Sat ↔ SatWithin univ, DRank mono_left/mono_right/
antidiagonal (Obs 4), scatter Obs 6, UsesOnly + congruence, rename
soundness. Headline finding of (c): unconditional rename and
environment-congruence are FALSE — the frozen exL guard reads the
whole context — proved as in-module counterexample theorems; the
repaired lemmas carry range-of-environment / guard-agreement
hypotheses. This is the source's silent guarded↔unrestricted
rewriting made explicit; the separation-lemma session must write out
the guards it means (exU + binary atoms), not lean on rename.
Process learnings: the lax namespace audit rejects proofs-side
declarations in concept namespaces AND concept definition names
passed to simp/rw (match splitters get recorded in the proofs
module); lake build alone does not catch either — always gate on lax
build. SyntaxLemmas' Unfolding section (rfl clause lemmas, local
simp) is the sanctioned way to take Sat/SatWithin/rename/IsLocal
apart. EnterWorktree based the worktree on a stale ref — reset to
main before seeding. Remaining P2: separate (Lem 8), farQuant
(Lem 12), locality + normalForm assembly, then the locality axiom
discharge.

## ND-MC P2 session 2 — exL-guard finding, surface decision escalated — 2026-07-28
Supervisor pre-flight for separate/farQuant found the P2 blocker
before any track launched: the frozen `exL` guard reads the whole
typed context, but the source's local quantifier (tex 495–548) guards
over an explicitly chosen variable set recorded at formula formation.
Session 1's counterexamples were the symptom; Lem 12 is where it
binds — condition (2a) and the cluster-intersection tests (tex 1067,
1097) embed a one-variable capsule β into the k+1 context, which is
exactly the unsound operation, and the "write the guards out as
atoms" repair is arithmetically impossible: guard radii run to
ρ⁺ = 9^k·ρ⁻ while the atom budget at the same rank is ρ⁻, with no
slack anywhere in the schedule (concrete inexpressible instance at
rank (1,2) in the decision note). The frozen locality AND normalForm
axioms are judged most likely false as stated — scatterFml's rename
placement has the same disease. Escalation:
`plans/nowhere-dense-model-checking/exl-guard-decision.md` asks Jan
to endorse `exL (r : ℕ) (g : Finset (Fin k))` — the source-faithful
guard-set reading; whole-context is the g = univ special case; the
≤-relaxed radius deviation stays. Prospective build on branch
`nd-mc-exl-guard` (NOT merged to main): supervisor-written DistFO.lean
revision (concepts green; ScatterSentences/Locality/NormalForm compile
with zero text changes), two Opus tracks reworked the only affected
proof modules — SemLocal (pattern-widening only, public statements
verbatim) and SyntaxLemmas (sat_rename/satWithin_rename/
sat_congr_of_usesOnly now UNCONDITIONAL, UsesOnly counts guard sets
via ↑g ⊆ s, counterexample section deleted, 725 → 578 lines). Both
first-build green; `lax build` gate OK; kernel axioms
propext/choice/Quot.sound only. Design record for the remaining P2
(`p2-remaining-design.md`): separate in reindexed per-side contexts
(no substitution, no UsesOnly in the statement — supersedes the
session-1 sketch), farQuant source-verbatim with the sound capsule
rename, assembly plan incl. BC-algebra and sat_scatterFml; session
split (a) separate (b) farQuant (c) BC-algebra + scatterFml, then
serialized assembly. P2 is PAUSED on Jan's endorsement of the
revised surface; if endorsed, the rework is already done and the
campaign resumes at zero extra cost.

## IMP+ toolkit — P5 pilot done, gate missed, campaign paused for Jan — 2026-07-28
Supervised session (Fable orchestrating, five Opus units): pre-P5
tactic flags fixed (tryClose swallowed partially-failed dischargers —
root cause in Lean's Tactic.run resetting recover; handed specs now
consumed in order), then the Lax11 CC driver retrofitted end to end
in five commits (P5a–P5e) with two mid-pilot kit units filling
consumer-driven gaps: tape rules + Lib/Fill + forRangeZero, then
seq-prefix spec matching + relational Queue.drain_run (+ costTac and
mdata bug fixes). Jan re-cut the gate mid-flight onto the glue split:
four glue files ≤ 505 (40% of 1,263). They landed at 1,152 — missed
2.3×, so P6 is not started, per plan. The pilot's real product is the
category split: symbolic-execution glue shrinks 33–42% (run_vcg),
composition shrinks when phases are GROUPED into one prefix-matched
spec (ccCom_run −39%), but invariant hand-off across opaque spec
states can cost more than the reads the kit removes (expandBody +11,
recorded in-file), and ~330 lines of the four files are mathematics
no machine kit touches. Elaboration got faster at every site, no
exceptions. Exported statements byte-identical throughout. Verdict,
six open kit gaps, and three options (recommend: close the retrofit
arm, go to P7, un-gate ND-MC RAM — the kit's economics favor new
code written in Spec form) are in the plan's P5 as-built section.

## ND-MC P2 session 3 — locality + normalForm discharged, P2 complete — 2026-07-28
Jan: "continue with the nowhere dense plan" — read as the endorsement
the session-2 escalation asked for. `nd-mc-exl-guard` merged
(400b811); the guard-set `DistFO.lean` is now the surface (flag for
re-endorsement at the next surface review). Three parallel Opus
tracks on pre-wired stub modules, then one serialized assembly track:
Separation.lean (3b4d2d0) — Lem 8 in reindexed per-side contexts,
with two supervisor deviations: added `1 ≤ a`, `1 ≤ b` (no local
rank-(·,0) formula exists at arity 0) and a 2-way guard-side split in
the exL case (the guard set makes the witness's side syntactic; the
design record's 3-way r⁻ split and its annulus atoms were a leftover
of the whole-context surface). FarQuant.lean (2f53d33) — Lem 12:
capsule via unconditional sat_rename, candidate (t : Fin k, I, sel)
recognition by distance atoms (radii ≤ 8·9^(k−1)·r, under
ρ⁻(k,q'+1)), scatterCore at H = ρ⁺(k+1,q'), counting by subset
patterns of ≤ k cluster tests `exL r (sel-fiber) β↑` against scatter
sentences ⟨4R, β, |T|+1⟩. BCAlgebra.lean + ScatterFml.lean (5ef8eef)
— BC clause lemmas, collapse/patternBC/assignments/
exists_eval_sum_iff/pullOut (scatter atoms out of a quantifier),
interp with rank transport; sat_scatterFml with NO rank/locality
hypotheses, plus the five normalForm side-condition bridges.
Assembly.lean (1d96817) — structural induction: exL via pullOut
(interp truth constant = Separation.alwaysTrue, NOT verum which
spends an exU); exU at arity 0 → scatter ⟨4ρ⁻(1,q), ψ_τ, 1⟩; exU at
arity ≥ 1 → near/far split at ρ⁻(k+1,q), far via separate
(e₁ = castSucc, e₂ = const last) then farQuant per capsule.
`Lax3Proofs.Assembly.locality`/`normalForm` carry `conclusion:`
frontmatter; build-output.json registers both with assumptions: [].
Gates: full `lax build` green (concepts 2016 + proofs 1079 jobs);
lean_verify on both = propext/Classical.choice/Quot.sound; zero
diagnostics all five new modules; supervisor audits found no
splitter-rule or namespace violations. P2 acceptance met: both
concept axioms discharged, zero sorry, no statement drift. Note for
polish (non-blocking): FarQuant carries private copies of a few BC
helpers; could later import BCAlgebra instead. Next: P3 splitter +
covers (plan L2 items 7–9), on the now-live locality interface.

## IMP+ toolkit — P7 done, campaign closed — 2026-07-28
Jan chose option (a): P6 out of scope, close via P7. Sibling path
requires kept (Jan, mid-P7) — the wave submit orders folders along
them and the pin is the submitted repo rev. The full pipeline caught
one violation package builds miss (root module must import the Lib
submodules individually; fixed). Wave Lax13 -> Lax11 -> Lax15
submitted as drafts at rev 5733671, all three confirmed in the draft
state; registration untouched per the JAN-FLAG. The campaign closes
with the kit consumer-tested and faster everywhere, and the ND-MC
RAM phases (P5-P7) are now un-gated. Operating guidance for them,
from the pilot: write machine code in Spec form from the start —
group consecutive phases into one handed spec, state invariants once
— and the hand-off tax that killed the retrofit gate never arises.

## ND-MC P3 — splitter game + covers discharged, P3 complete in one session — 2026-07-28
Jan: "continue with the nowhere dense plan … full authority"; session
branch fast-forwarded onto main (5733671) first. Supervised session,
three parallel Opus tracks on a supervisor-written design that
expands the design note's isolation-form recipe into a full formal
decomposition (checked against Lax12's exact UQW statement before
briefing). SplitterBasics.lean (supervisor) — Iff.rfl clause lemmas
for SplitterWins/deleteVerts so no tactic ever touches a concept
name. SplitterMono.lean — win antitone under ≤-subarenas via the
round_le edge comparison (batch cut to the smaller ball), plus
budget/batch monotonicity; L2 item 7. SplitterWin.lean (692 lines) —
splitterWins_of_nowhereDense discharged with ℓ = N(2s+2),
m = ℓ(r+1): strategy as functions (pathSet choice-walks, genSet,
batch = genSet ∩ ball, nextArena), Reached histories newest-first
with suffix-based invariants (isolation permanent, live picks in
every earlier ball, picks nodup), extraction by chronological
orderEmbOfFin pairing → s+1 disjoint pair-paths → one avoids S →
DistIndependent contradiction; notes' 2s+1 → 2s+2 slip fixed as the
concept notes record; assumptions exactly
[Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense]. L2
item 8. CoverConstruction.lean — exists_neighborhoodCover_degree_wcol
discharged kernel-only: clusters are wreach-fibers of a
Nat.sInf_mem-attained ordering; degree is the wreach bound read
backwards, covering via the π-minimal ball vertex and a two-sided
support-in-ball cut; L2 item 9. Gates: full lax build green
(concepts 2016 + proofs 2029 jobs), audit clean, lean_verify on both
discharges as registered, build-output.json carries all four
conclusions. P3 acceptance met in 1 session of the budgeted 2–4.
Commit 064c51e. Next: P4 abstract evaluator (L3 items 10–12,
isolation rewrite first — R2), D12 gate with Jan after.


## ND-MC P4 — math core complete, checkpoint proved, D12 passed as-built — 2026-07-28
Jan (before bed): "keep on going until ndmc is complete" — full
authority, D12 to be passed as a record, not a pause. Four Opus
tracks (three parallel, evaluator serialized on the rewrite).
Supervisor design work before briefing found and fixed a rank gap in
design §(a): translating a local guard into distance atoms inside the
body violates drank (ρ⁺(k+1,q) > ρ⁻(k+1,q)); the shipped iso keeps
the surviving guard as a genuine exL and adds a color-guarded exU
case for near-batch witnesses — colors are rank-free, so drank is
preserved exactly. Second supervisor delta: iso is total on DistFO
(cumulative profile + per-color distance families; the unary atom
becomes one color lookup), deleting the binary-fragment closure
obligation. Isolate.lean (896) — sat_iso against recorded cumulative
colors on the isolated arena, riding WalkDistance's
withinDist_deleteVerts_or_through as built for it in P1; drank_iso
exact; radiiLe_of_drank in the sharp two-hypothesis form (supervisor
mid-flight correction; the naive bound is false at the antidiagonal
boundary). Relativize.lean (336) — β↾cluster with marker color and
pre-intersected coloring, sat_rel unconditional in the tuple.
Reduction.lean (147) — toDistFO, satisfaction + qr→drank(k',q).
Evaluator.lean (760) — tablesLocal/tablesNonlocal by (budget, phase),
rank-free bodies choosing cover (CoverConstruction), batch
(splitterWins_succ_iff right disjunct), slot packings
(castAdd/natAdd/finProdFinEquiv); correctness chain semLocal sandwich
→ sat_rel → sat_iso → splitterWins_anti into budget−1, under the
antidiagonal invariant k'+q' ≤ q_top (all radii ≤ ρ⁻(0,q_top); the
agent's one-step antidiagonal normalization is needed — H2 is tight
at k'=q_top=1); sentence phase collapsed to inline Fin-order greedy
scatter over local tables. Checkpoint evaluator_decides: kernel three
+ Lax12 UQW only, both lean_verify'd. Full lax build green (2016 +
2034 jobs), audit clean, zero sorry. P4 done in 1 session of 4–7
budgeted; commits 5d2d9a8 + d9b3d47. D12 as-built record in the plan
(statements frozen since P2's exL revision; no elaboration hotspots;
RAM half proceeds). Deferred to P7: edgeless-arena unary evaluation
lemma. Next: P5 RAM primitives on the closed IMP+ toolkit (Spec form
from the start), then P6 (R1 risk peak), P7 (driver + cost + C0), P8.

## Refinement tower P0 — sources pinned, design record written — 2026-07-29
Milestone: P0 (sources + design record) — done, one session.
Commits: (this one) — plans/word-ram/refinement-tower/{design.md,source-extracts.md}.
State: no Lean written (per plan). Sources pinned: the four AFP entries
(Refine_Monadic, Automatic_Refinement, Refine_Imperative_HOL, NREST) at
AFP Isabelle2025-2 (2026-02-06); isabelle_llvm_time @ 42dd7f5 (ESOP'21
artifact — canonical for everything cost-carrying: acost currencies,
nrest, timerefine, cost hn_refine, SL with credits); isabelle_llvm
branch 2023 @ b44b639 (basic-layer shape); Haslbeck thesis mediaTUM
1596032; Std.Do+mvcgen confirmed in the pinned v4.30.0 toolchain
(evidence, not dependency). Verbatim extracts of the load-bearing
definitions are in source-extracts.md with provenance. design.md has
the P1–P6 component maps with substrate deltas, the hnRefine Lean
draft, IR op set v0.1 (three-address, tape-free, no alloc, currencies
per op), module skeleton under Lax13Proofs/Refine/, and the completed
deviation ledger — two new entries: D6 (no general recursion at the
concrete layer; RECT must be loop-refined before translate — IMP+ has
no procedures) and N3 (tower is tape-free; one kit-proved boundary
wrapper at P5; bfs_spec's export shape is already tape-free, checked
against 570a49e).
Decisions: currencies stay String-named (F1); plain functions + wfR,
not Finsupp (F2); relations as Set (concrete × abstract) (F3);
currencies survive to the IR, cashed once at P5 beside L.const (F4);
Std.Do not wrapped (F5). Defaults handed to P1 in design.md §10.
Next: P1 — Refine/Cost/ACost.lean + Refine/NREST/* (Basic, Pw, Rec,
Combinators, DataRefinement, TimeRefinement, BackwardsReasoning),
acceptance = abstract masked depth-capped BFS in bfs_spec's
vocabulary. Design record awaits Jan's post-hoc comments (no gate).

## ND-MC P5+P6 complete, P7 deep in flight — 2026-07-29 (overnight continuation)
Jan (before bed): "keep on going until ndmc is complete." Sixteen Opus
tracks since the P4 landing, supervised per the standing model. The
mathematics of the algorithmic half is DONE and kernel-verified:
Augmentation (chains, path invariant, fraternity densification; the
design-note transfer route is invalid — star square — and in-degree
structure is essential), AugmentedDensity (R1 RETIRED unconditionally:
the awarding route — one-sided witness claims cap collisions at d+1;
roundTransfer depth a→4a+4; joint in-degree/density recursion),
OrderedCovers (GKS 6.5/6.6 via meet_of_walk, 3 rounds per doubling;
route-(ii) reorientation provably fails), CoverDegree (closed budgets
— the density half needs exponent 2·16^i(a+1) — six-hypothesis
end-to-end cover degree ≤ ⌈c·m^δ⌉, cluster mass), BotEval (edgeless
base case: k + 2^L candidates), SplitterWinOracle (the win at any
path oracle; driver maintenance recipe), FormulaTables (per-depth
tables with PROVED choice-sharing with the Evaluator). Programs, all
Spec-form, all compiled with #guard demos: RamBfs, RamBfsPaths
(PathOracle recipe), RamElim (correctness fix: Elim.deg was false at
eliminated vertices; Reach layer + the full elimination turn walked;
frontier: while wrapper + fillPass + assembly, finisher in flight),
RamAugment (NewArc rule unconditional; GreedyFratRound found too
strong for inherited arcs — counterexample recorded, narrowing
queued), RamCover (wreach fibre = predecessor-ball bridge; f = first
catch at r, not 2r), RamScatter (fully walked; GreedyMem equation
lemmas reused audit-clean). RamDriver (1610 lines): driver_correct
PROVED from nine named obligations; ALL semantic glue discharged —
the descent needs no splitter win (only the base does); two masks per
depth keep ReachedO an equality; mb = ℓ(2cap+1). Discharge tracks:
RamDriverCluster (cluster+level mathematics proved; five phase-walk
Props open; found vertex-blind ReadbackImplements — repaired as
ReadbackStep — missing frames, unused Sized, PlayOk threading gap,
descendCom in-place aliasing), RamDriverIO (Decode/Sentence REFUTABLE
as stated — memory clauses + value bounds missing from all eight
obligations; repaired forms proved with the exact patch; name kit +
run_length_arrs/run_mem_arrs_lt infrastructure; orderCom destroys
LevelPre's block structure), RamDriverBase in flight. LOAD-BEARING
COST FINDING: per-arena full-array inits × n arenas = n² — the final
time bound REQUIRES touched-only (Trail-backed) cost forms per design
D8; correctness layers unaffected; queued as the cost wave. Assembly
wave next (single owner of RamDriver/RamElim/Augmentation): the
obligation-surface repairs, GreedyFratRound narrowing, ElimPre
relaxation, PlayOk threading, ball-chain fix, OrderImplements. Then
cost wave, recurrence, C0, P8. Branch at fd6048b, sixteen commits
ahead of main (main @ 1541d6f = P4).

## ND-MC wrap-up — P5+P6 done, P7 driver walks landed, session closed — 2026-07-29
Jan (morning): "good job! please wrap up when wave is done", plus two
process directives folded into memory: refutation-before-proof
(Plausible + #guard falsification of every authored obligation before
any proof attempt — eight refutable obligations were found mid-proof
this session) and folding in own insights (obligation-Props
discipline, touched-only costs). Wave B closed: RamDriverFrames
(scatter walk + both frames; HEADLINE: the frame proof caught a real
driver bug — the nested driver clobbers the caller's shared cover
arrays and centre cursor, so a level would process one centre and
exit; program-text repair specced), RamDriverOrder (cover single-turn
walked + coverPass_spec needing no availability hypothesis; ordering
kit; CoverState/CoverImplements gaps found; RamAugment.Implements
honestly declined with route recorded), RamDriverDescend (padding +
expansion/chain core; five surface gaps), RamDriverBot (repr/bot/base
specs complete; the generated exU branch is unsound-but-unreachable
with counterexample; BaseMem gap). Final full lax build GREEN: 3440
jobs, zero violations, zero sorry, kernel-three footprints on every
landed theorem (the only endorsed-axiom dependencies anywhere are the
intended Lax12 ones). Plan updated: P5 [x], P6 [x] (R1 retired), P7
in-progress with the complete A3 → wave C → cost wave → C0 resumption
spec. The campaign stands at: all four citable theorem concepts
discharged, the math core checkpoint proved, every engine program
fully verified, the driver correct modulo a converging set of walk
obligations whose every defect is now a precise, falsification-gated
repair item. Landed on main at session close.


## Refinement tower P1 slice 1 — NREST core landed green — 2026-07-29
Milestone: P1 slice 1 (ACost + NRest + Pw + Sanity) — done.
Files: word-ram/proofs/Lax13Proofs/Refine/{Cost/ACost,NREST/Basic,
NREST/Pw,NREST/Sanity}.lean + Refine.lean aggregator (~1,520 lines).
State: build green (2970 jobs), lax audit passes, zero sorry, #print
axioms on all four monad laws = propext/Classical.choice/Quot.sound.
bindT is the source's Sup-of-consume formula verbatim; laws at the
source's own generality (left id generic; right id + assoc at ℕ∞ and
ACost κ ℕ∞ — F7). D4 gate ran: 13 #guards + 6 Plausible #tests over
executable twins with proved agreement theorems (noncomputable sSup
can't #eval; twins are the sanctioned fallback and kernel-honest);
negative controls found planted bugs in 5 and 13 shrinks, so the
harness discriminates. No source divergence found. Elaboration 31.7 s
for the five modules. Opus-agent deviations D-a…D-i reviewed, all
accepted (biggest: no CompleteLattice (WithTop β) in mathlib, so the
lattice is built the source's way — completeLatticeOfSup over the
source's sSup formula; ⊤ = fail and ⊥ = rest ⊥ are rfl). Upstream
candidates: withBot_map_add, withBot_eq_bot_or_coe, the WithBot
add-Sup-continuity transfer.
Parallel: P2–P4 source deep-read done by a second agent (byte-exact
extract files p2/p3/p4-*.md, committed d0a1ac7); finding: the cost
artifact has NO control-flow hnr rules — P4 must derive cost-carrying
if/while rules against the no-cost twin's shapes (noted in design.md).
Next: wave 2 satellites in parallel worktrees — Rec+Combinators,
DataRefinement+TimeRefinement — then BackwardsReasoning, then the
abstract masked-BFS P1 acceptance.

## Refinement tower P1 wave 2 — Rec/Combinators + Data/TimeRefinement — 2026-07-29
Milestone: P1 wave 2 (four satellite files, two parallel Opus agents in
seeded worktrees) — done, merged, green.
Files: Refine/NREST/{Rec,Combinators,DataRefinement,TimeRefinement}
(.lean, 581+617+873+1081 lines). Build 2974 jobs, lax audit OK (from
archive root — running lax from inside a package dir false-fails with
submission-scaffolding violations; audit only from root), axioms clean
everywhere, elaboration 13.4+21.6 s.
Fidelity events worth Jan's eye: (1) DataRefinement — the source's
pw_conc_inres is REFUTABLE under our same-carrier inresT reading;
witness in the module header; true direction ported, hypothesis-free
bindT_refine shape used. (2) FOREACH absent from the cost artifact;
ported pre-currency from AFP Refine_Foreach at ℕ∞. (3) ⇓R/⇓C
commutation is an inequality only. (4) One agent-authored D4 gate
assertion Plausible-falsified and corrected (SUCCEEDT loop wrinkle) —
refute-before-prove catching authored-obligation bugs again.
Integration protocol worked: satellites branch from frozen-API main,
one commit each, import-block union merges, verify, ff. Backlog: br/
relComp/SingleValued move to P2 Relators; consumea to Basic on thaw;
upstream candidates finsum_comm_of_support, unbundled gfp, WithBot
trio. Next: BackwardsReasoning (gwp + needname/drm), then the abstract
masked-BFS P1 acceptance program.

## Refinement tower P1 — BackwardsReasoning (gwp + vcg seed) landed — 2026-07-29
Milestone: last major P1 file — done, merged, green (2975 jobs, root
lax audit OK, zero sorry, axioms clean, 17.7 s elaboration).
BackwardsReasoning.lean (1964 l): needname/nonneg/drm/needname_zero
class port, gwp = ⨅ minusPM per source, full gwp rule suite
(returnT/SPEC/bindT/consume/If/MIf/ASSERT + conseq), progress
predicates, RECT_wf_induct, gwp_whileT_rule_wf + While, seed
@[refine_vcg] attribute + tactic; in-file demo: counted countdown
discharged BY the tactic to ⊑ SPEC with explicit cost.
FIDELITY EVENT (B1, Jan's eye): mathlib's Sub ℕ∞ is truncated
(⊤ - ⊤ = 0); Isabelle's enat has ∞ - ∞ = ∞, and needname's top_absorb
is that point — the ported minus_p_m_bindT is FALSE under mathlib's
minus (counterexample #guarded). Resolution: ResSub class (-ᵣ) as the
source's own minus-as-class; mathlib Sub untouched. Deviations B1–B7
reviewed and accepted (B5: several statements need [Nonempty] — false
at empty types, HOL types are nonempty; B7: attribute can't be used in
its declaring module — coreRules list + attribute extension point).
D4: twins with proved agreement (gwpE), 10 #guards incl. the B1
counterexamples, 5 Plausible #tests incl. gwp_bindT end-to-end.
Tactic maturity honestly limited: no DiscrTree, no progress-method, no
sc_solve — P2-era hardening. Backlog: ResSub/instances → ACost.lean on
thaw; inres section → Pw.lean; monadic_WHILEIET chain deferred to its
consumer.
Next: P1 acceptance — abstract masked depth-capped BFS via refine_vcg,
in Examples/Bfs.lean (mathlib SimpleGraph vocabulary inside Lax13Proofs;
the Lax3 WithinDist bridge belongs to the P7 consumer side — recorded
adjustment of design.md §10.4).

## Refinement tower P1 COMPLETE — acceptance passed, 481 vs 1,201 — 2026-07-29
Milestone: P1 acceptance (Examples/Bfs.lean) — done; P1 closed in one
session against a 2–3-session budget (same session as P0).
State: build green 2,987 jobs, root lax audit OK, zero sorry,
bfsAlg_correct axioms clean, 35 s module elaboration.
The number that matters: the abstract masked depth-capped BFS —
RamBfs's content, d+1 sentinel, threshold-iff postcondition, currency
budget — is 30 lines of algorithm + 30 of spec/invariant + 421 of
proof = 481 authored lines, 0 manual gwp-rule applications, 0 hand
frame clauses; refine_vcg drove the whole surface to 12 one-line
goals. Baseline RamBfs.lean is 1,201 lines with hand-authored
invariants and frames. This is abstract-level-only telemetry (the
tower below is P3–P5), but it is the shape of the P7 gate and it
points the right way.
D4: the gate checks Post itself (decidable WD twin proved equivalent),
5 positive configs + 3 negative controls + 2 Plausible differential
tests; no authored statement refuted (stated explicitly).
Honest limitation: ⊑ admits result-free programs; non-vacuity
evidenced, not proved (nofailT/inresT through the fixed point — later).
vcg-hardening backlog (6 items) recorded in the plan progress log.
Review queue for Jan before P2 leans on this: P0 design record;
pw_conc_inres refutation; B1 ResSub (mathlib ⊤−⊤=0 vs enat ∞−∞=∞);
FOREACH provenance; §10.4 vocabulary adjustment.
Next session: P2 — relators + rule DBs (first move br/relComp/
SingleValued out of DataRefinement into Autoref/Relators.lean).

## Refinement tower P2 COMPLETE — Autoref spine, acceptance passed — 2026-07-29
Milestone: P2 (relators + rule DBs) done in one session against a
1–2-session budget; four waves (A single-owner, B1/B2 parallel Opus
satellites in seeded worktrees, C single-owner), three extraction
passes (tutorial target, tool phases; both committed with provenance).
State: build green 2,999 jobs, root lax audit OK, zero sorry, axioms
{propext, Quot.sound} or none on every spot check.
Landed under Refine/Autoref/: Attrs (all ten DB attributes, one shared
module), Relators (zoo + characteristic suite, source snake_case rule
names; br/relComp/SingleValued relocated in from DataRefinement with
byte-identical statements), Param (33 @[param] rules incl. the list_eq
route, parametricity seed tactic), Tagging (OP/APP/ANNOT/PROTECT/ABS +
Interface/CONST_INTF/ID_OP, axiom-free), Solver (TaggedSolver priority
registry, declare_solver command, legible dispatch failures), then
wave C: Phases/IdOps/FixRel/Translate/Tool/BindingsHOL — the real
four-phase pipeline id_op(10)→rel_inf(20)→fix_rel(22)→trans(30)
(extraction corrected the design record's three-phase framing),
autoref tactic + autoref_synth command, autoref_rules DB at 26 rules.
Thaw relocations: consumea→Basic, ResSub+B2-backlog→ACost; inres was
a NO-OP (P1 never ported it — still open, needs a source fetch).
Acceptance: the source's own Autoref_Bindings_HOL §Examples — 7 of 8
entries reproduced mechanically (0 manual rule applications;
synthesized terms #guard-checked in value; hd's SIDE_PRECOND
discharged through the solver registry; the [1,2]=[2,3] entry runs
the full GEN_OP + struct_expand list_eq route), 1 adapted (Isabelle
sort-annotation pitfall, no Lean analogue). Failure legibility proven
by #guard_msgs negative controls naming phase + unmet side condition.
D4 gates everywhere; B2's gate caught a real dispatch bug (goal-list
mutation before a late throw), C's audit run caught an autoref_synth
namespace bug.
Review queue for Jan (adds to the standing P0/P1 queue): extra-rules
vehicle (local hypotheses swept + autoref [rules] — no notes-attribute
analogue in Lean); entry-4 adaptation; the #guard_msgs "26 rules" DB-
size canary; autoref_nat_lit catch-all (leaf-only, but P4-relevant).
Backlog → P4: ID_abs/ABS ported but unexercised until monadify brings
lambdas; STRUCT_EQ registered, unexercised (Collections material);
trans rule choices untraced; six bonus DBs (hom/post_simps/ga_rules/…)
need one Attrs-unfreeze wave; DiscrTree indexing still absent
(linear scans, flagged honestly at every site).
Ergonomics: lean-lsp MCP pinned itself to a removed worktree path —
satellites fell back to lake env lean, which worked fine.
Next session: P3 — the IR and its separation logic with credits
(Ir/{Syntax,Semantics,Assn,Wp,Triples,SepSolver}; p3-ir-sl-extracts.md
already in the repo; first decision = balance carrier default ℕ∞ per
design §10.1).

## PCP campaign proposed — plan rev 1, unscheduled — 2026-07-29

Jan asked what I'd be most excited to build and then said "think
bolder"; the answer was formalized hardness, summit first: Dinur's
gap-amplification proof of the PCP theorem. Plan drafted at
plans/pcp-theorem/pcp-plan.md, status PROPOSAL — nothing scheduled,
JAN-FLAGs 1–4 open (charter scope P7-vs-P8, sequencing against the
two live campaigns, NP-over-word-RAM endorsement surface, 5-vs-3
submission split). Shape: machine-free Amplification Theorem at P7
(constraint graphs, explicit gap-doubling transformation, no machine
model) + PCP proper at P8 (NP over word RAM, Cook–Levin via
RAM→circuit→CSP, verifier form, reduction cost through the tower).
Ladder: constraint-graphs / spectral-expanders / linearity-testing /
gap-amplification / pcp-theorem, each first-in-ecosystem. Budget
20–32 sessions, long pole the P5 powering analysis
(Radhakrishnan–Sudan governing text); riskiest prerequisite is
exact-size explicit expanders (P0 spike, GG default, h→λ fallback).
Ledger seeded L1–L7 (finite counting, symbolic constants until P7,
Hadamard-only composition, word-RAM NP). No Lean was written; no
existing campaign touched.

## Refinement tower P3 — 2026-07-29 (same day as P2; one session vs 2–3 budget)
Milestone: P3 COMPLETE, acceptance passed.
Commits: 600d985 (deep SL extracts), bb7ff84 (wave A), 0c19fee (wave
B), 888efde (wave C); governance 88fb046 earlier the same evening (full
authority delegated — this and later phases run without interim review
flags; ledger/D-flag discipline unchanged, now serving the final
evaluation).
State: the IR and its credit-carrying separation logic exist end to
end under Refine/Ir/{Syntax,Semantics,Assn,Wp,Triples,Attrs,SepSolver}
+ Examples/ArrayFill. Wave A: Val=ℕ, binops ARE Imp.Bop (reused),
16 "ir.*" currencies, deterministic BigStep charging one currency per
op, evalFuel twin equivalent both directions, out-of-range stuck.
Wave B: AFP sep-algebra class stack with Tsa/Pi/Prod/ACost instances;
carrier (scalar cells × array cells) × ECost — §10.1 default taken,
runs consume finite Cost, balances ℕ∞; ¤/¤¤ for the source's $/$$
($ is Lean-illegal); generic_wp as a one-field class (frame/cons by
instance = the source's interpretation); ALL SIX cost_framework locale
axioms proved at (leCostECost, minusECost) — assumptions became
theorems; wp over BigStep, wp_seq = wp_bind; per-op credit triples in
ll_load_rule's mould, exact + GC forms; while_triple =
llc_while_annot_rule, invariant carries the credits (ESOP'21). R=Unit:
IR statements return nothing, results are read from destination cells
(design §5 updated accordingly this session — the P4 target now names
the destination cell). Arrays are ONE indivisible cell (no sep_set_img
— no IR op splits an array). Wave C: Frame_Infer.thy whole — tags +
four structural rules 1:1, the ML search loop as a TacticM solver
(start/extract/round/end kept; rotations_tac as O(k) index selection;
credits by numeral arithmetic; GC absorbs greedily at the back;
entails_refl first at end instantiates the frame metavariable from the
residue; no HOU anywhere); five rule DBs as attributes incl. vcg_rules
populated with the op rules; failure messages name the unmatched
conjunct, #guard_msgs-pinned.
Acceptance (plan criterion met): hand-proved credit triples for array
get/set/fill as concrete IR programs — get pays exactly 1·ir.aget, set
1·ir.aset, fill (n+1)·ir.while + n·ir.aset + n·ir.add — with ALL frame
reasoning through the fri solver (zero manual sepConj/ac_rfl/rotation
steps in the acceptance file); the n=3 fill run derived from the exact
triple down to BigStep, full 16-currency vector #guard-pinned;
Plausible cost-as-function-of-n on the executable twin;
fill_no_wrong_cost: a wrong vector admits no derivation, by
determinism.
Verification: lake build 3,007 jobs green; lax audit OK from archive
root (the inside-proofs false-fail bit once again — ROOT ONLY); axioms
⊆ {propext, Classical.choice, Quot.sound} on 49 spot-checks; zero
sorries anywhere.
Supervisor review events: one wave-B header defect caught and fixed
pre-commit (D-l claimed $c Lean-legal while the code correctly uses
¤c); wave C untouched-clean on review. Spend-limit interruption mid
wave B; resumed agent finished from transcript with no loss.
Backlog → P4: goal-side ∃ᵃ not solver-handled (port fri_exI if
needed); fri_red_rules declared + populated but the round loop doesn't
enumerate it yet (~20 lines); sepImp has no consumer; no PRECOND/PRIO
side-condition registry (Autoref's declare_solver is the wiring
point); solver is first-match-wins, no cross-round backtracking
(complete while fri_rules={refl}); x:=y⊕y needs monadify's
duplicate-arg split; inres still unported (P2 carry-over).
Next session: P4 — hn_refine + the Sepref phase pipeline under the
source's own phase names (design §3 map, §5's updated hnRefine as the
target; budget 3–5 sessions; extraction of Sepref/Basic + monadify +
translate first).

## ND-MC P7 correctness half CLOSED — end-to-end checkpoint proved — 2026-07-29 (session 2)
Jan: "continue with the ndmc plan, all changes from last session are
approved"; later "credit reset, continue but wrap up at a convenient
point." Ten supervised Opus waves (A3, C1–C3, D1–D4, E1–E1c, E2), all
committed individually (dc1ca67…9d28d4b). Result: EVERY obligation of
the driver stack is discharged and
`RamDriverRoot.driverRoot_decides_sentence` is proved — the RAM
driver's output bit equals Sat G φ at R = 0, costs parametric,
hypotheses only input-word data (+ CsrSimple as root datum), parameter
equations, hQ (UQW over Lax12 definitions; endorsed axioms enter when
C0 derives hQ), and cost side conditions. Kernel three exactly.
Eleven falsification-caught defects this session, every one with a
recorded counterexample (two landed as theorems in RamDriverWrites):
the standouts are the orderCom PROGRAM BUG (second elimination on
un-re-zeroed elm/bh — no run existed; repaired by elimRezeroCom,
review-marked in the docstring) and the DescendStep SPEC mismatch
(machine path buffers are existential, oracle-function batches
underivable — C₄ witness), which forced the session's one design
pivot: the path-oracle layer was deleted wholesale and replaced by
SplitterWinRec's recorded-batch game (faithfulness absorbed into
splitterWins_of_reachedR). The augment walk closed hypothesis-free
over three continuations (RamDriverAugment, 5277 lines;
slotCnt_out_eq is the load-bearing cost exchange). Supervisor review
caught one interface defect the gates missed (playRec_succ's
∀-over-unrecorded-rounds hstep). For Jan's review: the two program
repairs (per-depth cover/ord/cursor names in A3; elimRezeroCom in
D4), the SplitterWinRec pivot, OrderMem gaining B, CsrSimple as root
input data. Cost wave next (frontier in plan P7): solve the Kl/Ks
recursion, touched-only retrofit (LOAD-BEARING — recursion as stated
is n^ℓ), R > 0 tgt widenings for the cover degree, derive hQ, ElimMem
cleanup, ComputesInTime bridge, C0. Full lax gate green at every
commit; 3444 jobs, zero sorry throughout.

## Session 19 — 2026-07-30 ~21:00 UTC → 07-31 (overnight)
Milestone: refinement tower P4–P8 — CAMPAIGN COMPLETE
Commits: ab58c34…32f8cdf on worktree-refine-p0 (P4: extracts, waves
A/B1/B2/C, acceptance; P5: design + codegen waves A1/A2/B; P6: IICF
waves A/B; P7: gate waves A/B + final; phase-close commits each), plus
p8-verdict.md.
State: the full Sepref/NREST tower is live — sepref_synth writes deep
IR programs from NREST specs (P4 acceptance: reverse + filter-count,
323 authored lines, 0 frame clauses); verified codegen cashes them to
computesInTime at factor exactly 4 (P5); IICF collections all
synthesized-impl (P6); the P7 gate re-derived RamBfs end to end —
whole-program synthesis in 49 s, export bfsQ_spec at computed cost
56n+40ns+33 vs the baseline's hand-tuned 51n+44ns+30. GATE VERDICT:
frame-clause criterion PASS (0), line criterion MISS (≈2.5× raw; the
queue invariant is intrinsic and the 560-line bounds pass is D-a's
price — full decomposition + adoption options in
plans/word-ram/refinement-tower/p8-verdict.md). Build 3,041 jobs
green, root lax audit green, all headline theorems axiom-pinned.
Five flagged tower repairs during P7, all output-preserving (pinned
syntheses byte-identical). Opus outage mid-P7 final leg: completed on
Fable per Jan's live instruction; Opus draft survived ~100% under
audit.
Next: Jan's evaluation of p8-verdict.md (recommendation: adopt (a) +
the wordAssn spike (b)); thaw-queue wave when convenient; land is a
clean merge (main gained only ND-MC files since branch point).

## Session 20 — 2026-07-30 (daytime, cross-cutting)
Milestone: subagent retrospective + workflow integration — done
Commits: d47bc76 (retro report + worker brief template), this session's
integration commit (CLAUDE.md, nd-mc-rebase-plan.md, this entry).
State: all 72 July worker transcripts reviewed (12 sessions, 07-24→29,
4,644 tool calls) plus the wave-level git repair signal (11/316
commits). Findings ranked in plans/subagent-retro-2026-07.md:
orientation tax (median 35% of worker messages pre-first-edit; two
3-agent chains on single obligations), refutable supervisor-authored
surfaces as the largest rework class (A3's 397-message repair agent),
compile-loop vs LSP iteration (1,040 builds vs ~220 LSP calls),
shell-idiom file handling, ownership-clause archaeology (clause set is
load-bearing; zero contamination once complete). Worker report quality
high throughout; S4's revert-don't-half-prove canonized. Nulls: no
rate-limit incidents, no retry loops, no clause violations, no
dishonest success claims.
Integration: plans/worker-brief-template.md is LIVE — CLAUDE.md now
binds proof-worker briefs to it; nd-mc-rebase-plan.md gained a "Worker
process" section (split at brief time, named falsification gate,
budget check before long waves); memory indexed.
Next: ND-MC rebase P0 (hfcomp first) with briefs from the template.

## Session 21 — 2026-07-30 → 07-31 (ND-MC tower rebase, single supervised session)

Milestone: the ND-MC rebase campaign executed P0 through the C0 gate in
one continuous supervised session (~35 waves: Opus workhorses, Fable on
the tool/design/last-obligation waves per Jan's mid-session authority).
Commits: f8cfa36 → 2bab5b8 on worktree-ndmc-rebase-p0, landed on main.
State: P0/P1/P2/P3 complete — all engines tower-derived with computed
costs (headlines: clusterLoad 16n²→12n+15m, expandCom's n·ns dies,
coverCost's n² → Σ|X_c|, carrier-free BFS turn), the R1 compacted
skeleton, the Σ/size interface, dead-vertex path, tgt widening
end-to-end, symCom + orderImplementsR (Fable's R=1 probe refuted the
designed fold body before proof — re-zeroing was missing). All 30
hypotheses of driverRoot_decides_sentence have named producers. C0
itself: B7 stopped at the gate with two compiled findings (C0Probe.lean
— EncodesGraph permits repeats ⇒ CsrSimple underivable; Ω(n·W) floor
from the carrier-width phase constants with W ≥ n²+1 on the C0 path).
Repair legs G1 (dedup guard) + G2 (phase-cost re-thread) specced; both
launched and stopped at Jan's wrap order. Next session: resume G1 ∥
G2-design (briefs in the session log / plan wrap section), G2
execution, B7 re-run, P5. Process notes: refute-before-prove caught
eleven+ wave-level defects including three refuted cost constants and
two refuted design assumptions; the worker-brief template held; two
structural floors were found only by compiled probes after prose
verdicts passed — compiled accounting is now the standing requirement
for any "the recurrence closes" claim.

## Session 22 — 2026-07-31 (G-road: G1 + G2 engines through the compiled residue)
Milestone: ND-MC rebase G-road — G1 complete, G2 engine layer complete,
residue compiled; wrapped at Jan's order with E-mem cancelled pre-edit.
Commits: e5e0f91 → 10e6dc4 on worktree-ndmc-rebase-p0, landed on main
(13 waves: plan rev 3, G1a/G1b Opus, G2-design Fable, E5/E1 Opus,
E2/E2b Fable, E3a/E4a/E4b Opus, E6/E-order Fable; model allocation per
Jan mid-session: Fable on the integration/assembly waves).
State: dedup guard end-to-end (CsrSimple derivable at the C0 boundary,
cost 31n+50ns+29); arena-weight cost interface designed compiled-both-
directions and its spine landed (root cost Kl 0 (n+ns)); W-free uniform
program text (C0's ∃p-before-∀n closed by signature); chainWidthE
degree-aware width (n·n term dead, floor route compiled dead);
live-prefix copies with the saving proven on a cost-carrying
interpreter (execC); block-driven cover leaves, touched-only BFS
(queue-is-the-trail, measured carrier-free), active-set scatter.
Verdicts that end the guessing: E6's g2_plug consumes the Σ/weight
slots verbatim but compiles six per-slot gaps (phase compositions
missing); E-order's no-escape theorem — ANY empty-arena carrier
charge, even 1·n, breaks the closed form (decide +kernel at n=10¹¹) —
and the root finding that NO member list exists in the driver state
(R1.6 unbuilt). Residue enumerated in G2CostProbe §7 +
OrderBlockProbe: E-mem → member-driven interiors per family → E-order
re-run → E3b → E4c → R1.8 → B7 re-run (slot sweep first) → P5;
estimate 1–2 sessions. Three design-doc errors caught by compilation
mid-session (capacity prose, capital-table BFS row, §3(a) coupling);
zero sorry, kernel-three, lax OK at every commit.
Next: Jan decisions — bridge/prologue seam probe first (last unprobed
seam), optional provisional P5 draft (citable core discharged, C0 as
open obligation); then resume at E-mem (brief re-issue from wrap
section pointers).

## Session 23 — 2026-07-31 (tower expansion P0, Codex)

Milestone: tower-expansion P0 complete; Codex-only governance recorded.
Commit: this session's P0 record commit on `worktree-tower-expansion-p0`.
State: the existing 69-file / 47,054-line `Lax13Proofs/Refine/` tree was
diffed against the pinned source graphs and every unported component was
assigned to P1–P8 or given an explicit rule-4 exclusion. Deliverables:
`plans/word-ram/tower-expansion/{port-map,ledger,debt-register}.md`.
Pins for the two LLVM artifacts, Sepreftime, and Imperative_HOL_Time
were reverified upstream. P0 corrected four planning assumptions: there
is no source currency-vector FOREACH (P2 is an authored, source-shaped
adaptation); the primary artifact's IICF is dead/no-cost (P5 is cost
adaptation); introsort is the primary currency exemplar while timed
Kruskal/union-find live in Sepreftime; hash maps are excluded until the
cost calculus has an honest randomized story. The 52-row debt register
distinguishes actual opens from ND-MC readiness work already landed
(dependent hfcomp, unfueled loops, recursive trail acceptance, scaling
telemetry). Jan's instruction "we only use codex, not claude" supersedes
the plan's non-Codex fallback: Codex supervises and GPT-5.6-Sol via
`codex exec` is the only worker path. Documentation-only phase; no Lean
or build changes.
Next: P1.A half-size Sol calibration — `to_hnr`/`to_hfref`, `comp_PRE`,
FCOMP, and dependent-composition flattening.

## Session 24 — 2026-07-31 (tower expansion P1.A, Codex)

Milestone: tower-expansion P1.A complete; signature composition frontend
root-green. Commit: this session's P1.A commit on
`worktree-tower-expansion-p0`. State: four new `Lax13Proofs/Refine/Sepref`
modules provide the exact `compPRE` surface, transparent safe
`to_hnr`/`to_hfref`, dependent and non-dependent heap FCOMP, pure
`fref ∘ fref`, a goal-directed general/checked frontend with explicit
`attainsSup` residues, correlated flattening for nested `hrrCompDep`, the
active source `hr_comp` normal forms, and the `oneTime`/attained-supremum
family. Two review findings became permanent compiled negative controls:
one fixed `hnRefine` instance does not make a universally name-parametric
signature, and separately composing the input/result relations of dependent
layers is unsound because it permits different intermediate witnesses.
SIG-2–SIG-5 are closed; ledger E10 records the Lean theorem/tactic rendering
of Isabelle attributes. Root imports all four modules. Concepts: 505 jobs;
proofs: 3,053 jobs in 135 s; root `lax build` OK; key exports kernel-three;
zero sorry/admit and no new warnings. The first
Codex-subagent calibration is folded into the retro/template; Jan authorized
normal collaboration subagents instead of nested `codex exec`. Operational
finding: a redundant fresh seed hit ENOSPC before any edit; its empty
worktree was removed and the already-seeded campaign worktree reused.
Next: P1.B — signature-to-synthesis goal preparation, `sepref_register`, and
interface-type discipline.

## Session 25 — 2026-07-31 (tower expansion P1.B, Codex)

Milestone: tower-expansion P1.B complete; signatures now drive synthesis
instead of merely describing already-written refinement judgments. State:
`sepref_synth` accepts `hfref`, introduces its generic concrete/abstract/
precondition binders, sends the exposed `hnRefine` through the unchanged
pipeline, and exports the synthesized concrete descriptor. The small chain
and an eight-array ownership phase compile from signatures only. The decisive
gate, `bfsQFromSignature`, regenerates the full nested-loop queue BFS from one
argument record plus input/output assertions; its result-cell tuple and
`Ir.Com` are definitionally equal to `bfsQSynth_impl`, with no handwritten
`hnRefine` text. `intfOfAssn` plus `sepref_register` now infer conceptual
interfaces from assertion relations, fall back to the abstract carrier,
install `id_rules`, and admit explicit TYPE overrides. An eight-argument
operator identifies at eight deliberately distinct `ArrayI` inputs. Ledger
E11 records why Lean's arbitrary-spine monadifier replaces the source's
generated per-arity/mcomb equations. SIG-6/SIG-7 closed. Concepts: 505 jobs;
proofs: 3,056 jobs in 117 s; `lax build --only proofs word-ram` OK; new BFS
gate kernel-three; zero sorry/admit and no new warnings. Work was performed
in main under Jan's explicit authorization for this and future tasks.
Next: P1.C — port `sepref_decl_op`, `sepref_decl_intf`, and
`sepref_decl_impl` so P5 can declare container interfaces without bespoke
metaprogramming.

## Session 26 — 2026-07-31 (tower expansion P1.C, Codex)

Milestone: tower-expansion P1 complete; the declaration layer is root-green.
State: `Sepref/IntfUtil.lean` adds parameterized nominal interfaces,
interface-type normalization/checking, configured and structural
`INTF_OF_REL` inference with the abstract-carrier fallback, and the three
commands `sepref_decl_intf`, `sepref_decl_op`, and `sepref_decl_impl`.
The compiled gate declares fresh `CounterI`/`PairI` interfaces, preserves the
nominal counter interface through list/product relators, defines and
registers `op_counterRead` plus its `fref`, composes the existing raw heap
signature through checked FCOMP, and verifies the generated implementation
is in `sepref_fr_rules`. `Iicf/Basic.lean` imports the declaration surface for
P5. Ledger E12 records the explicit-statement/proof Lean frontend delta;
SIG-8 is closed. Concepts: 505 jobs; proofs: 3,057 jobs in 80 s after an
initial 120 s replay timeout at 3,046/3,057; zero sorry/admit and no new
warnings. Work stayed in main under Jan's standing authorization.
Next: P2.A — currency-vector `nfoldli`/FOREACH and its hnr/sepref rules.

## Session 27 — 2026-07-31 (tower expansion P2.A, Codex)

Milestone: tower-expansion P2.A complete; vector FOREACH and its compiled
masked-walk acceptance are green. State: `NREST/Foreach.lean` adds the
source-shaped `nfoldli` equations, monotonicity, append/assert and relational
refinement rules, inert IE annotations with an exact vector invariant/cost
rule, the `FOREACHociE`/`FOREACHciE` family, and the
`itToSortedListE`/`LIST_FOREACHE` decomposition. `Sepref/Foreach.lean` adds
the hnr lowering bridge, synthesizes the concrete member-index loop, and
pins its generated `Com`. The acceptance arena has members `[7,91]` in a
100-cell carrier; the kernel proof equates the compiled loop to the abstract
member-list fold plus three guard evaluations. Its vector is exactly four
reads, four additions, two skips, and three while checks, independent of
carrier length. The generated judgment is lifted to the abstract fold and
both axiom probes are kernel-three. NR-9 closed. Concepts: 505 jobs; full
proofs: 3,059 jobs; `lax build --only proofs word-ram` OK; zero sorry/admit
and no new warnings (only the root replay's recorded warnings). Work stayed in main under Jan's
standing authorization.
Next: P2.B — `list_set_rel`/sorted-list iteration refinement, the Autoref
iteration rule set, and RECT-based nested for-loop combinators.

## Session 28 — 2026-07-31 (tower expansion P2.B, Codex)

Milestone: tower-expansion P2 complete; iteration-list refinement, Autoref
rules, and nested for combinators are root-green. State:
`Autoref/Foreach.lean` ports the distinct-list/set relation,
`autoref_nfoldli`, source `LIST_FOREACH'`, and its currency-vector
parametricity theorem. `itToSortedListE` now has an exact observable-result
theorem: every result is a distinct enumeration of precisely the input set,
is pairwise ordered by the requested relation, and respects its declared
cost vector. A two-member sorted-list gate pins the relation discipline.
`NREST/For.lean` provides the inclusive one-index recursion and the source's
closed two-/three-index forms, proving them equal to nested `nfoldli` walks
over `List.range (n + 1)`; a full 2×2×2 cube is the compiled shape gate.
Ledger E13 records the closed-form rendering of the source's public
lexicographic recursion. Root imports both modules. Concepts: 505 jobs; full
proofs: 3,061 jobs; `lax build --only proofs word-ram` OK; zero sorry/admit
and no new warnings (only recorded root replay diagnostics). Work stayed in
main under Jan's standing authorization.
Next: P3.A — currency normalization and cost-side-condition automation.

## Session 29 — 2026-08-01 (tower expansion supervision reset, Codex)

Jan corrected a supervision failure mode before the next P4 worker launch:
do not multiply worktrees, seeds, briefs, or planning ceremony around this
campaign. The authoritative execution rhythm is now sequential work on the
already-warm clean `main`: one proof worker, one concrete outcome, then
supervisor review and commit before the next worker. Fresh worktrees and
seeding are specifically excluded for tower expansion. Two empty attempted P4
worktrees were removed after their parallel seeds hit ENOSPC; no proof edits
were lost. Inherited briefs remain useful technical reference only and must
not drive process overengineering. Next: one B1 successor finishes the
height/rank/logarithmic union-find slice; A2 waits.

Jan reaffirmed this after the instruction was nevertheless misread: the warm
`main` checkout is not a fallback but the required execution environment.
Proceed sequentially there. Do not treat apparently mandatory parts of a
worker brief as authorization for worktrees, seeding, parallelism, or process
ceremony; the warm-main rule takes precedence unless Jan explicitly changes
it.

The reset immediately produced a clean boundary: the single B1 successor
finished the remaining height/rank/logarithmic slice in
`Iicf/UnionFindAbstract.lean`. Supervisor replay passed the 1,992-job leaf,
3,250-job proofs root, and `lax build --only proofs word-ram`; kernel guards
remain within `propext`, `Classical.choice`, and `Quot.sound`, with zero
placeholders. P4.B1 is complete. Next: P4.A2, still sequentially on warm main.

P4.A2 then reached a deliberately partial green boundary in one new leaf:
source-shaped vector amortization plus a caller-owned bounded adapter whose
logical capacity grows only inside existing storage and fails cleanly when
full. The 2,984-job leaf build and compiled functional/cost probes pass. A2 is
not marked complete: `boundedPushSpec` still lacks its concrete
`Ir.Com`/`hnRefine` implementation and the leaf is not root-wired. Next is that
single seam, not a redesign of the landed foundation.

That seam now has green concrete leaves: exact loop-free success and
non-mutating failure `Ir.Com` programs synthesize with an explicit physical
capacity operand. Whole-dispatcher synthesis repeatedly timed out inside
`isDefEq` even at 800k heartbeats, so the worker removed the unfinished theorem
and stopped. Next: manual `hnRefine` composition from the two landed leaves;
do not repeat the whole-tree synthesis experiment.

Manual composition closed that final seam without touching the tower:
`boundedExec_hnr` assembles the two green leaves under `hnr_If`/`hnr_bind` and
connects the explicit loop-free command to the observable bounded push at its
exact branch-sensitive vector cost. Compiled no-resize, in-buffer growth, and
full-failure gates pin complete state and cost vectors; failure preserves the
array and metadata. The leaf is root-imported. Full proofs: 3,251 jobs; concepts:
505; proofs-only lax green; kernel-three and zero placeholders. P4.A2 is
complete. Next: P4.B2 timed loop-form union-find, sequentially on warm main.

P4.B2's first green boundary is now landed in an unrooted leaf: the MOP and
two-array assertion surface, an exact-vector-cost parent-range loop, and
no-allocation initialization from two caller-owned buffers. The resulting
parents/sizes pair satisfies the accepted pure `ufaInvar` and `rankInvar`.
Focused Lake build: 2,997 jobs; kernel-three and zero placeholders. Next:
bounded root search and path compression in the same leaf.

The root-search half is green. A first length-bounded loop was rejected because
its Theta(n) cost could not support B2's logarithmic contract. The accepted
implementation manually composes a measured loop whose exact vector cost is
indexed by `heightOf`; `hnr_ufFind` preserves the two-array assertion and returns
`repOf`. Singleton, compressed, and two-edge-chain gates pin both semantics and
strictly different costs. Focused replay: 2,998 jobs; kernel-three and zero
placeholders. Next: path compression, sequentially in the same warm-main leaf.

Path compression is now green in that leaf. The measured IR loop rewrites each
visited parent to the representative, preserves the abstract forest, both
union-find invariants, and the untouched size array, and charges an exact vector
cost for the executed rewrites with a starting-height upper bound. Its public
HNR bridge consumes the representative left by find. Compressed and two-edge
chain gates pin both the final arrays and distinct costs. Supervisor replay:
2,998 jobs; kernel-three and zero placeholders. Next: comparison.

Comparison is green. Valid inputs sequentially find and compress both paths,
then compare the representatives; invalid inputs return false without mutating
the structure. `hnr_ufCompare` preserves the abstract relation, rank invariant,
and caller-owned arrays. Exact branch-sensitive vector costs are exposed with
both measured phases, and their heights and rewrite counts are bounded by
`heightUb`. True/false forest gates and supervisor replay pass at 2,998 jobs;
kernel-three and zero placeholders. Next: union-by-size.

Union-by-size is green. The concrete operation performs two measured finds,
then links the smaller root below the larger and updates the winning size. Both
orientations preserve `UfArrays.Wf` and `rankInvar`, and refine exactly to
`perUnion`; equal roots take a non-mutating no-op branch. Exact branch costs,
`heightUb` bounds, orientation/no-op gates, and `hnr_ufUnion` pass the 2,998-job
supervisor replay with kernel-three and zero placeholders. Next: the final B2
interface and root wiring.

P4.B2 and P4 are complete. The final timed implementation certificate packages
init, compare, and union HNR rules with exact `ECost` vectors bounded pointwise
by `heightUb`; the certificate carries `heightUb = Θ(log n)` and makes no
inverse-Ackermann claim. The leaf is root-imported. The proofs-only archive
audit found one undeclared direct Batteries import; replacing it with the
mathlib-owned bitwise module preserved the proof and cleared the audit. Final
gates: focused leaf 3,000 jobs, concepts 505, root proofs and proofs-only lax
3,255, kernel-three, zero placeholders. Next: P5 IICF breadth, sequentially on
warm main.

P5.A has started with the smallest complete source family. New unrooted
`Iicf/Intf/Set.lean` defines the bidirectional set relator, `SetI`, inference,
and all eleven cost-silent interface operations; pick retains its nonempty
precondition and zero-cost nondeterminism. Source single-valued/converse
conditions, operation registrations, and diagonal frefs are gated. Supervisor
replay: 2,983 jobs; kernel-three and zero placeholders. Next: Map, still one
worker at a time on warm main.

P5.A Map is green as the second interface leaf. New unrooted
`Iicf/Intf/Map.lean` ports the active key-supported `map_rel`, `MapI`, and all
seven cost-silent operations. Update/delete keep both single-valued key
conditions; checked lookup keeps the paired-input nonempty precondition and a
zero-cost unique specification. Registrations, diagonal frefs, source
pattern/locale accounting, and kernel guards all pass. Supervisor replay:
2,984 jobs; zero placeholders. Next: List, sequentially on warm main.

P5.A List is green as the third interface leaf. New unrooted
`Iicf/Intf/List.lean` ports the list-relational support and all twenty-two
cost-silent operations, preserving the exact bound, nonempty, and nested-tuple
preconditions. Index/contains keep their single-valued relation requirements,
and the generic swap expansion is proved from the get/set sequence.
Registrations, diagonal frefs, source automation dispositions, and kernel
guards pass. Supervisor replay: 2,984 jobs; zero placeholders. Next: List_List,
sequentially on warm main.

P5.A List_List is green as the fourth interface leaf. New unrooted
`Iicf/Intf/ListList.lean` ports all eight nested-list operations and six fold
equalities with their original bounds and tuple shapes. The nominal
`ListListI` exists only because nested `ListI` does not normalize to
`List (List α)`; it adds no representation or operations. Registrations,
diagonal frefs, custom-empty accounting, and kernel guards pass. Supervisor
replay: 2,985 jobs; zero placeholders. Next: Matrix, sequentially on warm main.

P5.A Matrix is green as the fifth interface leaf. New unrooted
`Iicf/Intf/Matrix.lean` includes the relator and five operations plus the full
portable pointwise theory from the same source file: div/mod fold conversions,
nonzero support, unary/binary refinements, and the finite interruptible
comparison proof. The Isabelle heap code-generation locales are explicitly
disposed of while their semantic NRest refinements are retained; no fake API
was introduced. Supervisor replay: 2,985 jobs; kernel-three and zero
placeholders. Next: Multiset, sequentially on warm main.

P5.A Multiset is green as the sixth interface leaf. New unrooted
`Iicf/Intf/Multiset.lean` ports the complete multiset-relational algebra and
all nine operations. Delete/subtract/count/membership retain both uniqueness
directions, while nonempty pick proves a related element-and-remainder
decomposition at zero cost. Registrations, pattern/custom-empty accounting,
and kernel guards pass. Supervisor replay: 2,984 jobs; zero placeholders.
Next: Prio_Bag, sequentially on warm main.

P5.A Prio_Bag is green as the seventh interface leaf. New unrooted
`Iicf/Intf/PrioBag.lean` keeps the general cross-priority relational theorems
and the source's below-identity registration boundary for pop-min and
peek-min. Their outer frefs are unrestricted; empty bags fail through the
internal assertion, and pop returns the exact related erase remainder.
Generic, diagonal, registration, and kernel gates pass. Supervisor replay:
2,985 jobs; zero placeholders. Next: Prio_Map, sequentially on warm main.

All eight P5.A leaves are individually green. The final unrooted leaf,
`Iicf/Intf/PrioMap.lean`, ports the conversion helpers and all seven priority-
map operations with the exact presence, monotonicity, nonempty, uniqueness,
and below-identity requirements. Peek/pop transport global minima, and pop
returns the exact related delete remainder. Proper-below-id, diagonal,
registration, and kernel gates pass. Supervisor replay: 2,987 jobs; zero
placeholders. Next: root wiring and the package/archive boundary on warm main.

P5.A is complete. `Lax13Proofs.lean` explicitly imports all eight interface
families, and the aggregate boundary preserves their registration and kernel
gates. Final checks: concepts 505 jobs, rooted proofs 3,263 jobs, and
`lax build --only proofs word-ram` green with no dependency leak; zero
placeholders. Next: P5.B concrete bounded sequence/map families, sequentially
on warm main.

P5.B has begun with `Array_List`. The new unrooted implementation leaf adapts
the source to caller-owned `BoundedArray`: bounded/fallible append reuses P4,
and length, is-empty, last, butlast, get, set, and swap have synthesized
command rules with exact vector costs. Conditional shrink updates logical
capacity without reallocating the physical buffer; fresh empty, sized empty,
and copy remain honest non-executable allocation boundaries. Supervisor replay:
2,990 jobs; registration, command-shape, currency, kernel-three, and zero-
placeholder gates pass. Next: `DArray_List`, sequentially on warm main.

`DArray_List` is green as the second P5.B implementation family. The new
unrooted leaf keeps the source surface narrow: pure-element assertion
composition, the actual `dyn_da` identity cast, combined/empty assertion facts,
and empty/push. Empty is caller-owned and nonallocating; push reuses P4's
fallible command and exact branch-sensitive vector cost. The source's scalar
12/23 pair is recorded only as provenance, never passed off as an `ECost`.
Supervisor replay: 2,987 jobs; relation, registration, branch/currency,
kernel-three, and zero-placeholder gates pass. Next: `MS_Array_List`,
sequentially on warm main.

`MS_Array_List` is green as the third P5.B implementation family. Its fixed
maximum `N` is tied to both the owned buffer length and capacity. Empty-size
stays a caller-owned nonallocation boundary; append is exactly set/increment,
butlast exactly decrements length, and all seven executable operations expose
command-derived vector costs. Custom-empty folds and both source synthesis
examples survive at this honest boundary. Supervisor replay: 2,991 jobs;
relation/precision, registration, command/currency, kernel-three, and zero-
placeholder gates pass. Next: `Indexed_Array_List`, sequentially on warm main.

`Indexed_Array_List` is green as the fourth P5.B implementation family. The
new coupled representation proves its distinct bounded-list/inverse-position
invariant through swap, append, and butlast. All seven source operations have
synthesized exact-cost commands; contains is branch-sensitive. The registered
generic rules use `ialRel N A`, with append enforcing the source below-identity
condition and index/contains retaining two-way uniqueness. Empty remains a
caller-owned two-buffer boundary. Supervisor replay: 2,992 jobs; invariant,
generic-registration, command/currency, kernel-three, and zero-placeholder
gates pass. Next: `Array_of_Array_List`, sequentially on warm main.

`Array_of_Array_List` is green as the fifth P5.B implementation family and
closes the bounded-sequence group. The new unrooted leaf carries the generic
nested-list relation and the source empty/push/pop/index/update/length/take
semantic rules. Exact vector-cost commands begin at the selected-row boundary,
where the caller supplies the row buffer and metadata; the IR has no allocator,
deallocator, or runtime array-of-pointers selection, and the leaf says so
instead of inventing those capabilities. Strict spare-cell push bounds,
registration, command/currency, kernel-three, and zero-placeholder gates pass.
Supervisor replay: 2,993 jobs. Next: `Array_Map`, sequentially on warm main.

`Array_Map` is green as the sixth P5.B implementation family and the first
bounded-key map. Because the IR cannot store `Option Nat` in a natural array
without reserving a value, the new unrooted leaf uses caller-owned presence
and value arrays and proves the presence entries canonical 0/1. Generic
empty/update/delete/lookup/contains refinements and exact two-array executable
rules are linked by whole-state bridges; caller-owned empty is a linear fill,
and allocation/free/export stay explicit unsupported boundaries. Supervisor
replay: 2,987 jobs; registration, command/currency, kernel-three, and zero-
placeholder gates pass. Next: `Array_Map_Total`, sequentially on warm main.
