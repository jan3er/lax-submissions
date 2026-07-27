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
