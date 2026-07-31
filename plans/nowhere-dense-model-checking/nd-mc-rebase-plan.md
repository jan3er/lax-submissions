# ND-MC rebase plan — the driver stack re-derived through the refinement tower

Rev 2, 2026-07-30. **Status: OPEN — direction approved by Jan
2026-07-30 (conversation): fastest path to the tower-based ND-MC;
the old-style cost wave is frozen, not executed.** JAN-FLAGs 1–3
resolved 2026-07-30 under Jan's delegated supervisor authority
("full authority, may resolve the jan-flags"): all three at their
documented defaults — (1) superseded layer deleted in P5 after G4,
(2) per-engine retention at supervisor discretion with ledger
entries, (3) `wordAssn` thaw pre-authorized on a green spike. This
document is the contract: implementing sessions follow it,
deviations need an owner decision first.

Rev 2 delta (from a parallel supervisor instance's pre-rebase
review, folded in): P0 gains item 5, a **synthesis-scaling probe**
— the only tower cost that compounds over the campaign; BFS
synthesized in 49 s with linear-scan rule matching, and P2 grows
both the rule DBs and the program sizes. One oversized synthetic
program (~3–5× BFS op count) with the full DB loaded, wall-clock
measured; roughly-linear → done, superlinear → DiscrTree-index
`sepref_fr_rules` (and the frame-match conjunct scan if profiled)
**before** the engine waves. `packN` beyond 4 joins the trailing
list, demand-driven. Sequencing nuance made explicit: item 2's
outcome binds P2 brief style, so **P0 must fully land before any
P2 brief is frozen**; P1 may interleave.

**Working model** (unchanged): Fable supervises — plan, sequencing,
review, acceptance calls, commits — and Opus subagents write the Lean.
Refute-before-prove is standing practice for every authored
obligation. Scope is **proofs-only**: no concept surface changes
anywhere (the C0 statement and all Lax3 concepts are untouched), no
`lean-toolchain` or mathlib pin moves. The tower's fidelity charter
(`word-ram/refinement-tower-plan.md`) governs any change made inside
`Lax13Proofs/Refine/`; new deviations there are ledger entries in that
file's style.

## Charter

**Objective: the rebased ND-MC, fastest.** Replace the hand-walked
RAM program layer of `nowhere-dense-model-checking/proofs/Lax3Proofs`
with tower-synthesized programs, discharge C0 on tower-computed costs,
and draft-submit. This is *not* an evaluation campaign: no line gates,
no baseline measurement, no P7-gate-style verdict (Jan, 2026-07-30 —
"I don't care about eval metrics"). Acceptances are green-or-blocked,
nothing else.

**What is frozen and reused (the capital):**

- The math core P0–P4 (`evaluator_decides` and everything under it) —
  untouched.
- The P7 correctness half: `RamDriverRoot.driverRoot_decides_sentence`,
  `driver_correct`, and the named walk-obligation Props are the
  **frozen spec surface**. Tower-synthesized engines discharge the
  *same* obligation Props; the driver assembly proofs are retained,
  not re-derived. (Full-abstract re-derivation of the driver itself is
  out of scope; see JAN-FLAG 2.)
- P6 math (Augmentation/OrderedCovers/AugmentedDensity) — untouched.

**What is superseded:** the old-style cost wave (nd-mc-plan P7 items
(1)–(6)) is not executed. Its items map here as: Kl/Ks recursion → P3
(parametric, survives); touched-only retrofit → free from trail-array
synthesis in P2; tgt couplings → math in P3, walks die with the old
engines; hQ derivation → P3 unchanged; ElimMem repair + bridge
deletion → dies with the old engines; ComputesInTime bridge + C0 →
P4. The old wave spec stays in nd-mc-plan P7 **as the documented
fallback** (see below).

**Where new code lives:** `Lax3Proofs/Refine/` (tower-consumer
layout), namespace `Lax3Proofs.*` throughout per the root lax audit;
the lakefile already requires `Lax13Proofs` + `Lax12Proofs`. Old
`Ram*` files stay in-tree and green until the P4 gate passes — no
engine is deleted before C0 is discharged in tower form.

**Fallback (the hard checkpoint):** if P0 or P1 surfaces a structural
blocker — dependent `hfcomp` is the named candidate — the campaign
stops, the blocker is written up, and the decision to resume the
old-style cost wave goes to Jan. Nothing in P0–P2 makes that fallback
more expensive than it is today.

## Phases

- [x] **P0 — tower readiness (1–2 sessions).** **GATE G0 GREEN
  2026-07-30**, all five items (see progress log). All items live in
  `Lax13Proofs/Refine/` (tower campaign is closed; these are its
  handoff/thaw items executed here because this campaign needs them):
  1. **Dependent `hfcomp`** — port it (P2 carry-over, never needed
     until now; ND-MC composition is parameter-dependent everywhere).
     Blocker candidate #1; do it first.
  2. **`wordAssn` spike** (p8-verdict option (b), one session, capped):
     move `<B` into the arithmetic hnr rules; measure on one real
     engine-sized program whether the 560-line bounds class actually
     retires. Outcome binds P2 style: adopt (rule-layer thaw) or
     reject with the telemetry recorded. See JAN-FLAG 3.
  3. **`RECT` fuel-stability export** — retire `LOOP_VARIANT`
     wholesale (verdict: best single ergonomic win; every P2 loop
     pays it otherwise).
  4. **Recursive-arena trail acceptance** — first real touched-only
     consumer: a per-arena pass of `clusterLoad` shape charging
     active-set only, via `treset_cost_touched_only`. This is D5's
     missing exercise and the mechanism C0's time bound stands on.
  5. **Synthesis-scaling probe** (Rev 2): one synthetic program at
     ~3–5× BFS's op count, full rule DB loaded, synthesis wall-clock
     measured against BFS's 49 s. Roughly linear → record and move
     on; superlinear → DiscrTree-index `sepref_fr_rules` (and the
     frame-match conjunct scan if the profile names it) before P2.
  6. (trailing, only if slack) cheap thaw-queue placement/dedupe
     items; `packN` beyond 4 (demand-driven, else first P2 brief
     that hits a wider loop state picks it up).

  **Gate G0:** items 1–5 green → proceed. Any structural blocker →
  fallback checkpoint with Jan.

- [ ] **P1 — spec-surface alignment acceptance (½–1 session, may
  interleave with P0).** The tower already re-derived ND-MC's own BFS
  (P7 gate baseline *was* `Lax3Proofs/RamBfs.lean`; export
  `bfsQ_spec`, cost 56n+40ns+33). Swap it in: the driver's BFS-side
  obligations discharged from `bfsQ_spec` instead of the hand-walked
  specs, costs flowing through the parametric slots. **Gate G1:** the
  driver stack builds green with tower BFS underneath, with at most
  thin recorded bridges at the obligation boundary. This validates
  the engines-first architecture end-to-end before any mass work; if
  the bridges come out ugly, that is a shape report and a pause, not
  a push-through.

- [ ] **P2 — engine waves (2–4 sessions).** Re-derive engines
  smallest-first in dependency order: RamScatter + FormulaTables +
  BotEval; RamElim (the tower version supersedes `elimRezeroCom`'s
  bridge pair and the ElimMem conjunct debt outright); RamCover;
  RamAugment (`slotCnt_out_eq` becomes an abstract-level cost fact);
  the ordering phase; the descend/game layer (SplitterWinOracle,
  recorded-batch discipline — NREST's native nondeterminism replaces
  the machine-level existential contortions; the C₄ counterexample
  class dies at this layer). Per engine: abstract NREST program,
  correctness against the frozen obligation Prop, refutation pass
  before proof, synthesis, touched-only cost via trail arrays where
  the pass is per-arena. Satellite discharge files for parallelism;
  single-owner repair waves folding all defect reports at once.
  Per-engine retention escape hatch: see JAN-FLAG 2.

- [ ] **P3 — math survivors, parallel track (1 session; zero program
  contact, runs alongside P0–P2 as a satellite).** (i) Kl/Ks
  recurrence solved **parametrically** in per-engine cost constants —
  never bake in numbers; (ii) `hQ` derived from Lax12's UQW theorem
  (the endorsed axioms enter here, as designed); (iii) the R > 0 tgt
  coupling mathematics (fratSlots/K₁,₄, W vs in-degrees) at the
  abstract level, feeding the cover-degree bound.

- [ ] **P4 — cost assembly + C0 (1 session).** Instantiate the P3
  recurrence with P2's synthesized costs; Spec→`computesInTime`
  bridge; **C0 discharged**, kernel-three, lean_verify'd, root lax
  audit green. **Gate G4:** C0 green → the superseded hand-walked
  engines may be removed per JAN-FLAG 1.

- [ ] **P5 — polish + draft submission (1 session).** abstract.md,
  manifest, plan/NIGHTLOG records, old-layer disposal per FLAG 1,
  draft `lax submit` — **never `--register`** (freeze-consent rule).

Budget: 6–10 sessions end to end; P3 inside the envelope, not added
to it.

## Worker process (every brief, every phase)

Briefs are instantiated from `plans/worker-brief-template.md` (LIVE
2026-07-30; retro evidence in `plans/subagent-retro-2026-07.md`). The
three retro rules that bind hardest here: (1) split at brief time —
any obligation whose honest estimate exceeds one agent-session is
split *before* spawning (the July E1→E1c and B4→B4c chains each burned
three agents on one obligation, ~35% of every spawn re-orienting);
(2) the refutation pass of the P2 recipe is the template's named
falsification-gate section, so it cannot drop out of a brief; (3)
budget check before launching a long wave (a spawn died on the spend
limit 07-29 and cost the wave three hours).

## Traps carried from the tower campaign (into every P2 brief)

From p8-verdict §5: `omega` is blind through the `Ir.Val` abbrev —
bind indices at ℕ; `decide` times out on string-chain arithmetic —
use `decide +kernel`; `split at` on library matches leaks splitters
that only the root `lax` audit catches; scratch cells are consumed
from the precondition in written order; the operator phase never
backtracks across rule choice — order junk cells so junk-destination
rules cannot misfire. Plus ND-MC's own: touched-only charging from
the **first** brief of any per-arena pass (n² kills the headline);
per-depth register names, never save/restore (cost-fatal, A3 finding).

**R = 0 scope ruling (2026-07-30, supervisor, FLAG 2 discretion).**
Wave 2E established that at R = 0 the driver's augmentation fold is
`Com.skip`: the augment round and all counting sorts are dead code
on the C0 path. Consequently **RamAugment is retained old-style**
(its `RamDriverAugment.implements` is consumed by the frozen driver
assembly and stays green); the tower augment passes landed by 2C
(alvSet/prefix/count, plus whatever 2C′ banks) are R>0 capital, not
C0 critical path. The R>0 completion (tgt widening per TgtCoupling,
the round assembly, the sorts) is a future campaign's wave.

**Integration-A findings (2026-07-30, Fable wave — SUPERSEDES the
two ruling blocks below in part; full record in
`integration-design.md`).** (F1) The frozen driver *program* is
Ω(n^ℓ) in its text (n centre turns per level unconditional, inner
recursion unconditional — compiled floor theorem
`uniform_interface_floor_zero` in `Refine/CostShapeProbe.lean`);
the Σ-revision therefore includes the R1 program-skeleton change
(compacted centre loop, block-driven zeroing) — supervisor
decision D-1 APPROVED. (F2) At R = 0 there is no cover-degree mass
bound (`exists_cover_degree` needs 3t ≤ R; cap ≥ 9), so C0's cost
path runs at `R* = 3⌈log₂(2·cap)⌉` — the augment rounds, counting
sorts, and the tgt widening are LOAD-BEARING after all (the R=0
ruling below stands for correctness only; the 2C/2C′ augment
capital returns to the critical path); supervisor decision D-2
option (a) APPROVED. Positive: the size-indexed interface + R1
lands the recurrence in `CostRecurrence.solve` at coefficient D+1
→ n^{1+ε} confirmed (paper + compiled star probe). Road: briefs
B1–B7 in integration-design.md §8.

**Σ-shape cost threading (2026-07-30, supervisor analysis — binds
the integration wave and P4).** The frozen driver cost interface is
uniform-per-turn: `hKl`'s `(Ks j + 8) * n` charges the max cluster
cost times n turns, which loses exactly the `Σ|X_c|` saving the
touched-only engines produce (star-like instance: uniform×n = n²,
true sum linear — C0's almost-linear bound is underivable through
the uniform shape). This is the old plan's "touched-only retrofit
is LOAD-BEARING; the recursion as stated is n^ℓ" item surfacing at
the driver layer: the rebase's engine costs are touched-only for
free, but the DRIVER's cluster-loop threading must be revised to
per-turn costs summed (Σ-shape) — a proofs-side hypothesis revision
of `levelImplements`/`driver_correct`/`driverRoot_decides_sentence`
(the C0 concept statement is untouched; P3's CostRecurrence solver
is parametric and absorbs either shape). Scheduled into the
integration wave; ledger entry required there.

## JAN-FLAGs

1. **Disposal of the superseded layer.** After G4, the hand-walked
   engine/walk files (~15k lines, incl. `RamDriverAugment`) are dead
   weight in the build. Default: delete in P5 — git history keeps
   them, the draft archive shrinks, the build gets faster. Flag
   because it removes landed proofs; alternative is freezing them
   out of the build tree.
2. **Per-engine retention.** Both stacks export the same `Spec`
   interface, so any engine whose re-derivation turns out
   disproportionate can keep its old-style export (verdict option
   (c)). Default: supervisor discretion with a ledger entry +
   review at the next boundary. Flag if Jan wants totality forced
   (north-star purity) or wants specific engines pre-designated.
3. **`wordAssn` thaw pre-authorization.** The spike, if green,
   implies a rule-layer thaw inside the closed tower campaign's P4
   layer. Default: pre-authorized on a green spike, recorded as a
   tower ledger entry. Flag if Jan wants sign-off between spike and
   thaw instead.

## Records

Progress log appended below per session, tower-plan style; NIGHTLOG
entries per overnight session; memory updated at boundaries. The
old-style cost wave remains specced verbatim in nd-mc-plan P7 —
that text is the fallback contract and is not edited beyond a
supersession pointer.

## Progress log

- 2026-07-30 — Rev 1 written; direction approved in conversation
  (rebase-now over ship-then-rederive; no eval gates). No code yet.
- 2026-07-30 — Rev 2: FLAGs 1–3 resolved at defaults under
  delegated authority; scaling probe added as P0 item 5, `packN`
  to trailing, P0-before-P2-briefs sequencing pinned. P0 session
  opens (worktree `ndmc-rebase-p0`, both packages seeded green).
- 2026-07-30 — **P0.1 GREEN** (f8cfa36): dependent `hfcomp` +
  frame-carrying `hnr_comp_dep` + bind-shape consumer test; blocker
  candidate #1 cleared, no structural obstruction. Queued debt: the
  `hrrCompDep` flattening lemma (only bites loop-composition).
- 2026-07-30 — **P3 GREEN, early** (4fb7da2): CostRecurrence
  (parametric solve, closed form, minimality), UqwInstantiation
  (`hQ_of_nowhereDense`, exactly one endorsed Lax12 axiom),
  TgtCoupling (coupling (a) settled negatively — K₁,₄ refutes
  ns-reuse; (b) as single chain-budget width).
- 2026-07-30 — **P0.3 GREEN** (e31be80): the D-cv fuel export
  refuted (compiled counterexample, unbounded nondeterminism);
  correct export is postfixed-point + `LoopTerm` accessibility;
  unfueled `hnr_while` has no termination premise; LOOP_VARIANT
  retired at all 14 loop sites.
- 2026-07-30 — **P0.4 GREEN** (c26318a): recursive-arena trail
  acceptance; nested loop-with-trail synthesized first-try; cost
  signature n-free by construction; compiled proof the naive shape
  admits no touched-only bound. D5 exercised.
- 2026-07-30 — **P0.2 PARTIAL — binds P2 style** (98f26bc):
  `wordAssn` rejected as formally vacuous; **`BRefine`** adopted
  (second judgment component transporting creation-site `<B`
  against the abstract correctness invariant). −28% measured on
  the bounds class, −61% projected with tool support; fully
  additive, FLAG 3 thaw unused. P2 briefs say BRefine.
- 2026-07-30 — **P1 GATE G1 GREEN** (7e0bd9c): tower BFS under the
  driver via Refine/BfsBridge.lean; zero diff at CoverImplements
  and above; six thin bridges P1/B-a..B-g; worked example
  cell-identical. The P2 swap pattern is validated and templated
  (see the P1 report's 7 points, folded into P2 briefs).
- 2026-07-30 — **P0.5 GREEN — probe closes, G0 CLOSED** (probe
  artifact deleted after recording; telemetry here is the record).
  Synthesis scaling on a 16→100-op family, full DB, load-normalized:
  exponent 1.28–1.35 (local ~1.4 in the upper half); 4× ops ≈ 6.2×
  time; 3–5× BFS extrapolates to 45–135 s — minutes, not hours.
  **DiscrTree indexing is the wrong target**: appending 20 rules
  costs ≤2.6%, pre-match scan is a flat ~2 ms/goal (<0.5% at 100
  ops); the growth is the frame/entailment layer (matchLoop/
  proveConjEq walk the conjunct list; one `fri` call = 28% at 100
  ops). Follow-ups if ever needed, payoff order: (1) release dead
  scratch cells mid-block at `hnr_bind` (flattens exponent to ~1);
  (2) cheapen `fri`/`proveConjEq` on long conjunct lists; (3)
  DiscrTree for failure-path latency only. None block P2.
- 2026-07-30 — **P2 satellite 2A GREEN** (fca93bf, ScatterSynth) +
  three supervisor decisions under FLAG 2 discretion: (i)
  **FormulaTables/BotEval retained as-is** — no machine content,
  they are already the abstract layer; (ii) **the base case
  (baseCom = reprCom + botCom fold) retained old-style** — botCom
  recurses on formula syntax and generates cell names, outside
  fixed-program synthesis; re-deriving reprCom alone buys nothing
  while botCom stays; (iii) **the tower/hand boundary is pinned**:
  tower synthesizes leaf engines; the name-generating recursion
  (botCom, per-depth driver assembly) is retained capital. Scatter
  phase 2 (greedy scan) + Cover + order phase all queue behind
  **tool wave T1** (word-ram, single-owner, after ElimSynth lands):
  (a) `fri` bound-tuple split — the blocking gap; (b) BRefine junk
  rule; (c) `sepref_brefine_rules` DB + driver emission of
  perm/frame; (d) promote mopSucc/mopAddIn to a shared module;
  (e) frameMatch named-assertion diagnostic. Probe capital: a
  synthesized engine registers as a leaf `sepref_fr_rules` op and
  fires (engine-in-engine composition works; precondition must be
  spelled as conjuncts, R2A/D-f).
- 2026-07-30 (continued) — **P2 SYNTHESIS COMPLETE** in nine further
  waves + one tool wave: 2B′ (all Elim phases synthesized; mopPair
  skip-tax finding F-a), 2A′ (Scatter whole-engine, Progress into
  the abstract state), 2E (**the R=0 reduction**: augment fold is
  skip — RamAugment retained, no counting sorts; ordering phase
  fully derived + BRefine-covered), 2C′ (outPass complete, round
  cancelled per R=0 ruling), 2B″/2B‴ (Elim engine export
  elimEngine_le with the rank bound restored; 2B″'s cost prediction
  corrected by 2B‴ — dropped A₂·ls term; honest 296n+127ns+41),
  2D+2F (Cover turn loop + the cluster reduction map + all mask/
  load leaves; clusterLoad 16n²→12n+15m — first touched-only proof
  of the load half), 2G (expandCom — the LAST leaf; the n·ns
  product dies: 47n+30ns+4 vs (24ns+44)n+6). **T2 tool wave
  (Fable, db-branch merged)**: BRefine nested-while + junk rules +
  brefine driver (−52%/−77% measured), bpre→BRefine run adapter,
  bind_ref_tag normalization, Bounds.lean promotion zero-breakage.
  Endgame launched: F1 mop-up (five-phase Elim export + ReachedList,
  Opus) ∥ Integration-A (Σ-shape driver revision + swap design,
  Fable) → Integration-B waves → P4.
- 2026-07-30 — **P2 satellites 2B (afde8b3) + 2C (c0e08f5) GREEN**:
  ElimSynth (five-phase twin, 12 golden #guards first-build; degree
  pass 36n+23ns+4 vs old 48n+44ns+10; rezero/ElimMem debt dies by
  the layer argument) and AugmentSynth (5/10 passes; slotCnt_out_eq
  becomes cntPass_spec, a pass postcondition; K₁,₄ coupling bites
  the file's own program). Gap narrowing across satellites fed T1.
- 2026-07-30 — **T1 TOOL WAVE LANDED (db68602, Fable)**: the D-a
  stall was whole-vs-split tuple spelling in `mergeSolve` pairing
  (both prior hypotheses pass in isolation) — fixed via
  conjunctsSplit normalization (T1/D-a); bound-tuple split in three
  organs (fri simps T1/D-b, componentwise junkConjunct T1/D-d,
  lazy matchLoop splitting T1/D-f) + a live-caught junk/absAgree
  soundness guard (T1/D-e); shared mops (IrOpsExtra); wide-state
  packN dissolved by measurement (11-deep state ≈18 s — crawls,
  doesn't break). degPass: 3-min timeout → seconds; bfsThenSweep
  and cntThenPref both green kernel-three. BRefine tooling memo'd
  (junk rule, nested-while rule, brefine DB, Bounds.lean
  promotion) — bounded tax ~50 lines/loop until then. Loop states
  are resources: assemble with mopPair/pack, never literal tuples
  (P4/D-m linearity — put in every P2 brief).
- 2026-07-31 — **F-c PARTIAL — the symmetrization landed, the
  `orderCom` rewiring is NOT** (this session). Delivered green,
  zero consumer breakage: (i) **`RamDriver.symCom`** — the pass
  B5 approved, `RamAugment.outPass` + one `fillUpto` over the
  offsets (a vertex's degree in `D.toGraph` is its in-degree plus
  its out-degree, so the union's offsets are the *sums* of the two
  structures' offsets — no second counting sort) + `symRow`, two
  `blockScan`s per vertex; (ii) its walk **`symPass_run`**
  (`RamDriverAugment`, §Symmetrize, ~600 lines) leaving
  `RamElim.CsrSimple D.toGraph (m+m)` in `off`/`tgt`, with
  `symCopy_run` / `csrSimple_of_rowsDone` /
  `slotCnt_eq_card_outSet` / `card_symNbrs` / `two_mul_arcs_le` as
  reusable capital; (iii) the **§5.4 `P` slot** in
  `RamDriver.OrderImplements`, instantiated `fun _ _ => True` at
  every existing call site (`orderImplements₀`,
  `levelImplements`'s `horder`, `OrderBridge`'s three
  statements) — `driverRoot_decides_sentence` byte-identical;
  (iv) the **K₁,₄ symmetrization gate** in `TgtWidenProbe`:
  differential refutation of the old text (its final elimination
  reports the *star's* bound `kmax = 1`, the symmetrized run the
  *augmented* graph's `kmax = 4` — `(D₁).toGraph = K₅` seen cell
  by cell), plus `symCom` stuck at the level's 8 slots and
  completing at `R = 0`.
  **NOT landed, and what B7 inherits**: the `orderCom` text
  rewiring (`symCom` inserted after the fold, `restoreCsr` moved
  after the final elimination) with the `R = 0` re-discharge of
  `orderImplements₀` at the new text, and the `R*` fold. Both are
  unblocked, not merely unstarted — see the F-c report.
- 2026-07-31 — **F-c-3 PARTIAL — the widened cover chain landed, both
  bare slots addressed, the `LevelPre` flip BLOCKED ON DATA** (this
  session; full `lake build` + root `lax build --only proofs` green,
  kernel-three, no `sorry`, zero consumer breakage,
  `driverRoot_decides_sentence` byte-identical). Three items.

  **(A) Cover widening — steps 2–4 landed, step 5 blocked.** Additive
  and green: `Refine.BfsBridge.csr_of_csrGraphW` + `bfsQCom_specW`;
  `RamCover.CoverPreW`/`CoverStateW`/`ImplementsW`/`cover_specW`
  (accessors restated once on `CoverStateW`; every pinned form is the
  `nt = ns` instance on the nose, RamElim's precedent);
  `RamDriverOrder.centreStep_specW`/`coverTurnImplementsW`/
  `coverPass_specW`. Differential `#guard`s in `RamCover.Demo`: the
  padded run `demoRunPad` — two slots written past the structure's six
  — agrees with the exact run cell for cell at all four settings of the
  worked example, and the two clocks differ, so the check has teeth;
  plus a refutation that the padding hypothesis is not implied by
  `CsrGraph`.
  **L-8, the flip's blocker.** The widened relation needs `T j < n` at
  the *padding* slots — F-a's documented residual, since `BfsQ.Shape`
  keeps its range clause over the whole physical array (`Ir.StateBound`
  is state-global, and four ND-MC passes read the same clause at full
  width). That clause cannot be added to `LevelPre`: `n = 0` is
  reachable (`WordBound` permits it) and makes `∀ j < W, T j < n` false
  for every `W > 0`, so `LevelPre` would be unsatisfiable and
  `RamDriverIO.decodeImplements` could not establish it. The
  satisfiable form is a **zero-padded tail** — `∀ j, ns ≤ j → j < W →
  T j = 0`, which yields the clause wherever a centre turn runs, since
  a turn carries `c < n` — and its price is a reshape the F-c-2 map did
  not have: `DecodeMem` becomes `length = W` with the tail zeroed, and
  the decode's walk must show its `ns` stores leave the tail alone. The
  tail then survives a level, because `saveCsr`/`restoreCsr` copy all
  `W` slots. Full record at `RamDriver.LevelPre`'s docstring.

  **(B) `orderImplementsR` — the interface landed, the walk not.**
  `RamDriverCompose.OrderP` (the slot value: `∃ D d₀ k,
  CoverDegree.AugChainData (masked G M) D π R d₀ k`), `relinkCost`,
  `orderPhaseCostR n ns W R = orderPhaseCost n ns W + R · (augCost n W +
  relinkCost n W)` with its `R = 0` and monotonicity readings, and
  `OrderImplementsR` as a named `def`. The residual is itemized in that
  section: the fold's chain-carrying induction (the family `D` is built
  round by round out of `AugPost`'s existential, `isAugChain_succ` /
  `greedyFratRound_succ` growing the two clauses), one `W` for every
  round via `TgtCoupling.chainWidth_dominates`, the two `ElimPost`s
  that steps (3) and (10) of `orderImplements₀` already produce and
  discard, the syntax section at general `R`, and
  `AugmentedDepthOneDensity` as an inherited hypothesis.
  **L-9, and its repair.** The `P` slot F-c anchored was *dropped*:
  `RamDriverCluster.levelImplements` destructured the phase's witness
  away one line after it arrived, and its `hmass` slot had no place for
  it — which left the root's `hdeg` asking for the cover degree at
  **every** permutation, a hypothesis nothing can discharge, since
  `CoverDegree.exists_cover_degree` is about the ordering of a chain's
  last elimination. Repaired: `hmass` takes `P π ord` beside
  `RamCover.OrdersBy`, `levelAt` supplies it with `_` at `R = 0` (no
  statement above this moved), and `RamDriverRoot.wreachDeg_of_orderP`
  / `exists_wreachDeg_of_orderP` are the proved step from the slot to
  the coefficient.

  **(C) `hbinj` closed.** `Refine.MassMath.blockInj_of_coverOut` is
  `RamCover.CoverOut.block_inj`: B3's clause and B6's `BlockInj` came
  out identical clause for clause, so the projection B6 designed is one
  field access. `RamDriverRoot.blockInj_slot` states it at the slot's
  own type and `driverRoot_decides_sentence_binj` is the plug check
  (B8's discipline at a slot with no arithmetic in it). B6's stale
  header and falsification prose corrected; the hypothesis is *kept* on
  the mass lemmas — they are about block data, not about a pass — and
  the `badXoff` control still shows it is load-bearing.

  **B7's hypothesis table.** Of the 29 slots, 27 are input-word data,
  parameter equations or cost side conditions and always had honest
  producers; `hbinj` (#24) now has one; `hdeg` (#25) has a *named*
  producer waiting on `OrderImplementsR` and nothing else. Probe family
  (`TgtWidenProbe`, K₁,₄ / `sym5*`) re-run green.

- 2026-07-31 — **rebase F-c-4: the `tgt` flip landed; `relinkCost`
  walked and found wrong.** Worktree `ndmc-rebase-p0`, on `c41f3f7`.
  Full `lake build` green (3523 jobs), `lax build --only proofs
  nowhere-dense-model-checking` OK, no `sorry`, kernel-three.

  **(A) The flip.** `RamDriver.LevelPre`'s `tgt` clause is now `arrOf W
  T` — the allocation width, not the block structure's `ns` — with two
  conjuncts appended: the **zero-padded tail** `∀ z, ns ≤ z → z < W → T
  z = 0` and the word clause `∀ z < W, T z < B`. Appending rather than
  inserting is what kept the ~20 destructuring walks to two extra
  binders apiece. `OrderMem`'s `("gtg", ns)` became `("gtg", W)`;
  `RamDriver.saveCsr`/`restoreCsr` took a `W` parameter and copy `.lit
  W` (program text), with `RamDriverOrder.csrCopy_spec`/`saveCsr_spec`/
  `restoreCsr_spec` and `RamDriverCompose.warrs_saveCsr`/
  `warrs_restoreCsr`/`alvName_notMem_saveCsr` following.

  **Why zero and not "a vertex".** L-8's blocker was real and the
  refutation is now in `TgtWidenProbe`'s flip gate: the range form `∀
  j, ns ≤ j → j < W → T j < n` is unsatisfiable at `n = 0`, which
  `WordBound` permits and the empty input word reaches, so `LevelPre`
  carrying it could never be established. Zero padding is satisfiable
  at every `n` and *yields* the range form wherever a turn runs
  (`RamDriver.pad_lt_of_zero`, from `c < n`). Consequence for the
  landed F-c-3 chain: `RamCover.ImplementsW`/`cover_specW` and
  `RamDriverOrder.centreStep_specW`/`coverPass_specW` now take `hpad`
  **guarded by `0 < n`**. That is the one reshape inside F-c-3's
  widened chain; it is consumed at exactly one place (the search inside
  the turn), where `σ.vars "c" < n` is in scope.

  **The decode.** `RamDriver.DecodeMem` gained `W`: `tgt` is `W` cells
  with the tail above `ns` zeroed. `RamDriverIO.readLoop_specW` is the
  new widened read loop — the invariant carries `Fill.Below` at the
  *physical* width plus `i ≤ k` and the tail clause, and the body shows
  the store index stays below `k`; `readLoop_spec` is now its `W = k`
  instance and is not re-walked. `decodeImplements` threads it and
  gains `hpad0` as a hypothesis, `T` being the caller's function.
  `TgtWidenProbe.decodeTail` is the differential: the decode run on the
  demo `K₁,₄` tape into a `20`-cell `tgt` with a sentinel tail leaves
  all twelve padding slots holding `7`.

  **Reach.** F-c-3's map said "the widened chain is fully landed"; that
  was true of `RamElim`/`RamAugment`/`RamCover`/`RamScatter`/
  `BfsBridge`/`RamBfsPaths`, and *not* of `RamDriverDescend`'s own
  passes, which were all pinned at `ns` through the reasoning kit's
  `Csr`. Those are now stated at a width parameter over
  `CsrWide.CsrW`/`CsrWide.loadRow_spec` — `RamDriverCluster.ExpandInv`/
  `ScanHit`, `expandStep_spec`, `expandCom_spec`, `chainCom_spec`,
  `chainCom_stages`, `ColPre`, `pdBody`/`pdCom`/`puBody`/`puCom`/
  `colourCom_spec`, `ballCom_spec`, `ancestorStep_spec`, `BatchEnv`,
  `batchFold_spec`, `batchCom_spec`, and the parent search through
  `RamBfsPaths.bfsPar_specW`. Fifteen surfaces, no new mathematics.
  Likewise `RamDriverIO`'s `RootPre` is read at `Ws` and the root
  scatter enters through `RamScatter.scatter_specW`, and
  `RamDriverFrames`'s cluster scatter through the same, with
  `ScatPre.nsW` the new accessor.

  **Cost.** `orderPhaseCost`'s `W` coefficient rose `20 → 60`: the two
  block-structure copies are charged at `W` now, not at `ns`
  (`28·W` of it). `Refine.OrderBridge`'s `#guard` moved `22350 →
  22750`; `OrderSynth`'s comparison prose was stale from F-c-2 and is
  corrected to the current def.

  **Hypothesis reshapes (ledgered).** `driverRoot_decides_sentence` and
  `driverRoot_decides_sentence_binj`: precondition `DecodeMem n ns σ →
  DecodeMem n ns W σ`, one new hypothesis `hpad0` (#7 of now **30**
  slots — F-c-3's count of 29 plus this one; `hbinj` is #25 and `hdeg`
  #26). `driver_correct` gained `hWB : W < B` and `hpad0`.
  `DecodeImplements` gained `W < B`, `ns ≤ W` and `hpad0`.
  **The conclusions are byte-identical**: the program `driverRoot q_top
  cap mb 0 ℓ W φ`, the postcondition `σ'.out = [if Sat G Fin.elim0 φ
  then 1 else 0]` and the cost `Kdec + (Kl 0 n + Ksent)` are unmoved,
  and `RamDriverCluster.levelImplements` is untouched. Plug discipline
  re-run: `levelAt_of_sigma` and `driverRoot_decides_sentence_binj`
  both still type-check.

  **(B) `OrderImplementsR` — not landed; one item of it is.**
  `relinkCost` was F-c-3's "generous, not yet walked" constant and the
  walk **refutes it**: the nine passes of `augRelinkCom W` come to
  `97·n + 12·W + 115` (`RamDriverCompose.relinkCostSum`,
  `relinkCostSum_eq`), and `100·n + 20·W + 100` is below that on every
  carrier under five vertices — `relinkCost_old_refuted` at `n = W = 0`
  (`115 > 100`), with `#guard`s at `n = 4` (fails) and `n = 5` (holds).
  The constant is repaired to `120`, so `orderPhaseCostR` is now a
  budget the fold can actually be proved at. The `n` and `W`
  coefficients were indeed generous; the constant was not.

  The fold walk itself is **open**, and the flip removed work from it
  rather than adding any: every surface the fold has to thread is now
  stated at `W`, so items 1–3 and 5 of the `Rstar` residual stand as
  written, item 4 (the syntax section at general `R`) is unchanged, and
  item 6 (the cost) is closed. Probe family re-run green:
  `TgtWidenProbe` (K₁,₄ / `sym5*` / the new flip gate), `RamCover.Demo`,
  `RamAugment.Demo`, the padded-run differentials.

- 2026-07-31 — **rebase F-c-5: `orderImplementsR` LANDED — the last
  obligation before the headline theorem; the fold body was refuted and
  repaired on the way.** Worktree `ndmc-rebase-p0`, on `03df23e`. Full
  `lake build` green, `lax build --only proofs
  nowhere-dense-model-checking` OK, no `sorry`, kernel-three, zero
  consumer breakage (`driverRoot_decides_sentence`,
  `driverRoot_decides_sentence_binj`, `levelAt_of_sigma`,
  `orderImplements₀` and everything above byte-identical in statement).

  **(A) The defect, compiled before any proof (refute-before-prove).**
  The R = 1 probe the brief mandated — `orderCom 1 64 0` run end to end
  on a `K₁,₄` level state — found the landed fold body **stuck**:
  `RamAugment.AugPre` asks for `off`, `elm` and `bh` zeroed at every
  round's entry, the phase's *first* elimination leaves `elm` all-ones
  and `bh` dirty, `off` holds the level's structure until the first
  relink, and `augRelinkCom` re-zeroes `off` but never `elm`/`bh` (the
  round's inner elimination re-dirties them). Wave D4's defect A one
  pass earlier: at `R ≥ 1`, `n ≥ 1` the obligation was refuted, not
  unproved. `TgtWidenProbe`'s new R = 1 gate is the record: the old text
  (written out as `orderComOld1`) sticks, the fold-entry state shows
  `elm = [1,1,1,1,1]`, and the repaired text completes.
  **The repair** (session repair, D4's precedent): `RamDriver.augPrepCom`
  — `fillUpto "off"` + `elimRezeroCom`, the minimal three fills — inside
  the new fold body `RamDriver.augRoundCom W`, so `foldRange _ 0 = skip`
  keeps the `R = 0` text **byte-identical** and `orderImplements₀`
  re-checks untouched. Two cost constants fell with it. `relinkCost`
  repaired a second time, `100n+20W+120 → 140n+20W+170`, now the budget
  for twelve passes (`prepCostSum + relinkCostSum = 134n+12W+163`;
  `prep_relink_le`, with `#guard`s recording that F-c-4's constant
  cannot pay for the prep). And **`orderPhaseCostR`'s round coefficient
  was refuted as landed**: at `R ≥ 1` the symmetrization and the final
  elimination charge at up to `W` slots (`2m ≤ ns` is an `R = 0` fact),
  up to `650·W` beyond the fixed part's `60·W`, while the fold's own
  component budgets consume the whole round term. Repaired with a
  `650·W` surcharge on the coefficient (`… + R·(augCost + relinkCost +
  650·W)`; same `R`-linear shape P3 consumes, `R = 0` reading
  unchanged); the accounting `#guard` at the smallest widened shape
  (`n=0, W=2, 2m=W, R=1`: components `26194` vs old budget `24980`) is
  the record.

  **(B) The theorem.** `RamDriverCompose.orderImplementsR {…} (hd :
  LowDegreeVertices (masked G M) d) (hdens : ∀ D i, i ≤ R → IsAugChain →
  Greedy → AugmentedDepthOneDensity D i D₁) (hWc : chainWidth n d D₁ R ≤
  W) : OrderImplementsR B n R W cap mb ns j G O T M Gm C` — the
  thirteen-step walk at general `R`. The fold is `fold_run_aux` over
  `fold_step` with invariant `FoldInv`: machine side (Sized scratch,
  re-zeroed accumulators/stamps, `ntg` word clause, `doff`/`dtg` =
  the chain's last orientation) ∧ chain side (`IsAugChain` + greedy
  clauses to `i`, `(D 0).InDegLE d₀`, `InCsr (D i) m' DO DT`, `m' ≤ W`,
  and `i = 0 → m'+m' ≤ ns` — the clause that keeps the R = 0 cost at
  `ns`). Per round: `augPrep_spec` (new), `RamAugment.augment_specW` off
  `RamDriverAugment.implementsW`, `augRelink_spec` (new — the nine
  passes walked as a Spec, F-c-4 only summed their costs); the chain
  grows by the `if l = i+1` update, `AugPost`'s `AugStep` +
  `GreedyFratRound`. Width thread: `greedy_chain_inDegLE` +
  `budget_mono` + `augWidth_mono` + `chainWidth_eq_augWidth` (rfl); the
  symmetrization fits by `arcs_le` + `2b ≤ (b+1)²`. Both `ElimPost`s are
  now *kept*: the first is the chain's foot (`d₀ = ka`, minimality
  against the arena, `ka ≤ d` via `hd`), the second — on the
  symmetrized `(D R).toGraph` — its head (`k`, minimality), with
  `masked_of_all_alive` collapsing the all-ones mask.
  **L-10, and its repair.** `ordCom_spec`'s postcondition quantifies the
  permutation away, and nothing ties the exported `π` to the final
  elimination's rank — information-theoretically unrecoverable from its
  statement (the ∃ hides the inversion). `ordCom_specData` is the landed
  proof with the final weakening removed (the loop invariant already
  carries `g (R v) = v`); `π := RamCover.rankPerm` at the kept data, so
  `(π v : ℕ) = R₂ v` definitionally and the exported `OrderP` bundle's
  `BackDegLE` is the final elimination's, transported across the two
  rank reads by `arrOf` agreement.
  Syntax at general `R`: `mem_wvars/warrs_orderCom` decompose into the
  landed R = 0 sets ∨ the round's (`mem_*_foldRange_const`, write sets
  W-independent by `rfl`), `noWrite_orderCom` by per-component `decide`.

  **(C) The probes.** `TgtWidenProbe` R = 1 gate: old text stuck; new
  text ok at R = 0/1/2 with the differential `kmax = 1 / 2 / 2` — the
  machine's own chain augments `K₁,₄` to the double star (one leaf into
  the centre, centre into three ⇒ three transitive links, no fraternal
  edge; smaller than the hand-fed `sym5Final` K₅ and the honest
  instance, being the phase's own run); order arrays `[1,0,2,3,4]` /
  `[0,2,1,3,4]`; exit state = entry state (structure + zero tail
  restored, `elm`/`bh` re-zeroed). All landed guards re-run green.

  **B7's `hdeg` discharge, end to end.** `horder :=
  orderImplementsR hd hdens hWc` replaces `orderImplements₀` at
  `P := OrderP R G M`, cost `orderPhaseCostR n ns W R`; then with
  `⟨c, hc⟩ := RamDriverRoot.exists_wreachDeg_of_orderP C hC cap R t ht
  hrt δ hδ` and `Kmass := ⌈c·n^δ⌉₊`, the slot value discharges `hdeg`
  via `RamDriverRoot.wreachDeg_of_orderP` — the conditional (per-`π`)
  form `levelImplements`'s repaired `hmass` consumes. Slot #26 now has
  a landed producer; all 30 slots do.

- 2026-07-31 — **B7 STOPPED AT THE GATE: C0 is not dischargeable from
  the landed capital — two compiled findings, no forced assembly**
  (this session; worktree `ndmc-rebase-p0` on `f70d993`). New file
  `Lax3Proofs/C0Probe.lean` + root import; full `lake build` green
  (3524 jobs), `lax build --only proofs` OK, all three headline
  theorems kernel-three; nothing frozen touched, zero consumer
  breakage; no C0.lean.

  **(G1, the brief's designated suspect, confirmed) `EncodesGraph` ⇏
  `CsrSimple` — slot #6 is underivable at the C0 boundary.**
  `Lax11.GraphEncoding.EncodesGraph` deliberately permits a row to
  name a neighbour twice (its own notes; `adj_iff` is an existential),
  and `driverRoot_decides_sentence`'s `hcsr` forbids it. Compiled:
  `C0Probe.dupWord = [2,2,0,2,4,1,1,0,0]` is a genuine `EncodesGraph`
  word for `K₂` whose row 0 is `[1,1]`; `encodesGraph_not_csrSimple`
  exhibits it at the root theorem's own instantiation (`offset x` /
  `target x` / `2·edgeCount x`). D4's "root input DATA" ruling is
  thereby wrong at the C0 boundary, where the input predicate is
  `EncodesGraph` alone. Repair: a dedup guard between decode and the
  first level — `driverRoot = decodeCom ; driverAt 0 ; sentenceCom`
  and `driver_correct`'s decode slot is already a hypothesis, so the
  splice is a new root text + a composed `DecodeImplements` (mark/
  collect/unmark per row, trail-pattern cost `O(n + ns)`, the P0.4
  acceptance covers the shape) + a `CsrSimple`-of-dedup lemma; one
  satellite wave.

  **(G2, found on the way, outranks G1) the landed cost interface has
  a compiled `Ω(n·W)` floor, and the C0 path pins `W ≥ n² + 1`.**
  `C0Probe.level_interface_floor`: from `driverRoot_decides_sentence`'s
  `hKs` (#20), `hKo` (#22), `hKl` (#27) **verbatim**, every admissible
  `Kl` at `ℓ ≥ 2` pays `n·(60·W + 1600·n) ≤ Kl 0 n` — `hKo` charges
  `orderPhaseCost n ns W` at every arena including the empty one (the
  R1.6 touched-only debt, named open in `levelCost_of_sigma`'s own
  docstring), `turnCost` carries `Kin` additively, and `hKl` runs up
  to `n` turns. So even at `W = ns` the floor is `1600·n²` — already
  over C0's budget for every `ε < 1` on sparse members. And the C0
  path cannot run at `W = ns`: the mass bound needs `R = R* > 0`
  (integration-design §2.3, compiled), `orderImplementsR`'s `hWc` pins
  `chainWidth n d D₁ R ≤ W`, and `chainWidth` carries an `n·n` term
  for the level's own graph ⇒ `60·n³ ≤ Kl 0 n`
  (`level_interface_floor_cubic`). Teeth: two `#guard`s beat the
  `ε = 1` and `ε = 1/2` budgets at generous constants on sparse
  instances; the quantifier order (c before n) finishes. The floor is
  also a *program* floor (paper half, F1's precedent): `orderCom R W j`
  opens with `saveCsr` copying `.lit W` cells at every level entry,
  up to `n` entries per depth. §2.4's "yes" verdict assumed R1.6's
  block-driven nested phases, which never landed in the cost surface.
  Repairs (owner decisions, in order of the money): (i) R1.6/R1.8
  honestly — nested order/cover/base phases charged at the arena
  (tower re-derivations + interface re-thread of `hKo`/`hKc`/`hKd`/
  `hKbase` to size-read forms); (ii) live-width save/restore + a
  degree-aware `chainWidth` (drop the `n·n` term against the chain's
  budget; the symmetrized round is degree-bounded by `arcs_le`) so `W`
  enters at `O(n·budget²)` and is copied only at its live prefix;
  (iii) fallback checkpoint per the plan's hard clause — noting the
  frozen old-style wave inherits the same floors.

  **Not done, deliberately**: `levelAtR`/`driverRoot_decides_sentenceR`
  (the general-`R` restatement) and the `Solves`/`computesInTime_of_solves`
  bridge scaffolding — both reshape under (i)/(ii), so landing them now
  is certain rework; the F-c-5 `hdeg` composition note stands unchanged
  for whoever re-runs B7 after the repair waves. C0's concept axiom
  stays an axiom; P5 is blocked behind the two repairs + a re-run B7.
