# ND-MC rebase plan — the driver stack re-derived through the refinement tower

Rev 1, 2026-07-30. **Status: OPEN — direction approved by Jan
2026-07-30 (conversation): fastest path to the tower-based ND-MC;
the old-style cost wave is frozen, not executed.** JAN-FLAGs 1–3
below are open; none block P0. This document is the contract:
implementing sessions follow it, deviations need an owner decision
first.

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

- [ ] **P0 — tower readiness (1–2 sessions).** All items live in
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
  5. (trailing, only if slack) cheap thaw-queue placement/dedupe items.

  **Gate G0:** items 1–4 green → proceed. Any structural blocker →
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
