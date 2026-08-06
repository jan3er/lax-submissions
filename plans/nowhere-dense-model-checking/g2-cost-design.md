# G2 cost design — the arena-charged phase interface, the width repair, and text uniformity

Rev 1, 2026-07-31. Author: G2-design (Fable). Status: **DESIGN COMPLETE,
COMPILED IN BOTH DIRECTIONS** — the existence probe and the floor-death
refutations are green in `proofs/Lax3Proofs/Refine/G2CostProbe.lean`
(zero sorry, kernel-three; `orderCom_reads_W` needs `propext` alone).
No frozen surface touched; every proposed form lives in the probe as a
local `def` and moves to the real declarations only in the execution
waves of §6.

Standing rule honoured (plan rev 3): unlike `integration-design.md`
§2.4 — whose prose verdict "`n^{1+ε}` comes out" was wrong because the
phase slots had not moved — every claim here is gated by a compiled
statement, cited by name.

## Table of contents

- §1 The design in one paragraph, and the one new idea
- §2 The old → new statement deltas (integration-design §5 style)
- §3 The width repair (item ii)
- §4 Text uniformity (item iii — a correctness constraint)
- §5 The per-phase capital table
- §6 The wave decomposition for G2 execution
- §7 Slot audit: findings and corrections
- §8 What the probe compiles (the record)

---

## §1 The design in one paragraph, and the one new idea

**One size variable threads the whole interface: the arena weight.**

```
arenaWeight n G M := ∑_{v ∈ markSet n M} (1 + deg_G v)      (root: n + ns)
blockWeight c     := ∑_{v ∈ block c}   (1 + deg_G v)
```

Every phase side condition `phaseCost(n, ns, W) ≤ K j m` becomes
`coeff · (w + 1) ≤ K j w` read at the weight; turn budgets read block
weights; the level condition `hKl` keeps its landed Σ-shape **byte for
byte** (`Kmass · (m + 1)` mass bound, `Σ (Ks j (bs c) + 11) + 6`
sum) — only the reading of `m`/`bs` changes from vertex counts to
weights. Why weights and not two variables (vertices, edges): the same
per-vertex cover-degree bound `hdeg ≤ D` that today gives
`Σ_c |X_c| ≤ D·(m+1)` gives `Σ_c blockWeight c ≤ D·(w+1)` — each vertex
lies in ≤ D blocks, so its `(1 + deg v)` contribution is counted ≤ D
times — and the recurrence `u j = a j + (D+1)·u (j+1)` is therefore
**unchanged**, absorbed by the landed parametric solver
(`CostRecurrence.exists_driverCostsSigma`, which already takes the
phase hypotheses in the form `K j m ≤ k · (m+1)`). The weight is
machine-computable: the compaction scan that today counts alive
vertices adds `1 + (off[v+1] − off[v])` per alive vertex instead — one
extra `aget` pair per member, no new pass.

The ordering phase's coefficient carries `bsq := (budget d D₁ R + 1)²`:
ONE save/restore of the live prefix `liveWidth = m·bsq + e + 1` per
level entry, plus the `R` augment/relink rounds at that width, all
charged at the arena (`G2CostProbe.orderCostA`, honesty:
`orderPhaseCostR_le_orderCostA` — constants `2310`/`16840` read off the
landed `orderPhaseCost`/`augCost`/`relinkCost`, not chosen). `bsq` is
constant in `n` (a function of `d, D₁, R`); at the C0 path
`d = ⌈c·n^δ⌉` makes it subpolynomial, handled by the landed
real-exponent lemma exactly as `(D+1)^ℓ` is.

## §2 The old → new statement deltas

Everything below is a **statement delta only**; no postcondition's
semantic content moves. "Probe name" = the local def in
`Refine/G2CostProbe.lean` that the form is stated as today.

1. **`hKo`** (`driverRoot_decides_sentence`, `RamDriverRoot.lean:659`)

   old  `∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m`
   new  `∀ j w, orderCostA (bsq d D₁ R) R w ≤ Ko j w`
   probe `orderCostA b R w := (2310 + 16840·R)·b·(w+1)`; the general-`R`
   slot and the `R = 0` slot unify (at `R = 0` the round term is zero —
   mirror of `orderPhaseCostR_zero`).

2. **`hKc`** (`:660`)

   old  `∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m`
   new  `∀ j w, kcov · (w + 1) ≤ Kc j w`, `kcov` supplied by the
   block-driven cover phase (E3 below). NOTE the landed
   `coverPhaseCost n ns = RamCover.coverCost n ns + 12·n² + 81·n + 56`
   carries **its own `12·n²`** (the coverSave member copy, "charged at
   the whole cluster arena" per its docstring) *and* `coverCost`'s
   `100·n² + 50·n·ns` — compiled as unfittable in the probe's §5
   negative findings. This slot is a **program** delta (E3), not
   re-threading.

3. **`hKd`** (`:661`)

   old  `∀ j m, Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j m`
   new  `∀ j w, sweepCoeffA q_top cap mb j φ · (w + 1) ≤ Kd j w`
   probe `sweepCoeffA = RamDriverBot.turnCost … + 10` (the landed
   per-vertex turn cost, member-list-driven; honesty
   `sweepCost_le_weight` is generic in `φ`). Program delta: NOT a
   header change — compiled refutation (`DeadSweep.lean` §4b,
   `no_memCoeff_pays_deadRows`, landed 2026-08-06): `DeadRows`
   quantifies over the dead set, the complement of the member list.
   The write moves to the turn that killed the vertex (its block
   contains it) — the R1.8-design leaf, a program change in the turn.

4. **`hKbase`** (`:658`)

   old  `∀ m, RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m`
   new  `∀ w, baseCoeffA q_top cap mb ℓ φ · (w + 1) ≤ Kl ℓ w`
   probe `baseCoeffA = reprBodyCost + turnCost + 22`; honesty
   `baseCost_le_weight`. Program delta: NOT a header change — blocked
   twice (compiled 2026-08-06): `BaseImplements` asks `TableInv` over
   all `Fin n`, and `BotEval.sat_exU_bot_of_repr`'s `hW` ranges the
   bottom formula's unrestricted quantifier over the carrier, so
   `reprCom` owes a representative for every vertex, dead ones
   included. Needs the R1.8-design leaf (a representative story for
   dead vertices), independent of the dead-row question.

5. **`hKs` / `turnCostSize`** (`RamDriverRoot.lean:192`) — the size
   slot is today **discarded** (`turnCostSize_eq` is `rfl` to the
   carrier-width `turnCost`, whose `descendCost` alone carries `16·n²`
   — compiled unfittable in the probe). New:

   `turnCostSizeA ct ksc s Kin := (ct + ksc)·(s + 1) + Kin`

   with `s` the block **weight**, `ct` the block-driven leaf
   coefficient (BlockLeaves: honesty `blockLeaves_le_weight` shows
   `ct = 200` covers clear+load, and/sub, expansion at the block), and
   `ksc` the per-member scatter-chain coefficient (see §2.7).

6. **`hKl`** — **unchanged byte for byte** (the probe's existence
   theorem satisfies the landed shape verbatim, `Kmass := D` now
   bounding block-weight sums). `hKmono` unchanged. `hbinj`/`hdeg`
   unchanged (same producers). The mass derivation
   `Refine.ArenaBlock.mass_of_alive_compaction` gains a weighted twin
   (§6 E5): `Σ_c blockWeight c ≤ D·(arenaWeight + 1)` from the same
   `hdeg`, plus the weighted §5.3 descend clause
   `arenaWeight(sub) ≤ blockWeight(cur)` (monotone: sub-arena ⊆ block,
   same graph `G`).

7. **The `hbnd → hcostI → hKsc` chain** (slots #12–14): today
   `Kb ≥ RamDriverIO.atomCost n ns t = 24·n + … + scatterCost n ns t`
   feeds `Ksc j` which enters `turnCost` **additively per turn** — a
   carrier read per turn (n·per-depth = n² — part of the same floor,
   found in this wave's audit; §7.2). New: the scatter pass at the
   block, `Kb` becomes a per-member coefficient
   (`kb·(s+1)`-form), `hKsc` becomes
   `∀ j < ℓ, ∀ s, Ki j s · tables + 1 ≤ Ksc j s` with
   `Ksc j s = ksc j · (s+1)`. Engine: the scatter engine's block-driven
   variant (E4; `scatK` is `Θ(n·t)` today).

8. **`hWc`** (`orderImplementsR`, `RamDriverCompose.lean:2724`)

   old  `TgtCoupling.chainWidth n d D₁ R ≤ W`
   new  `chainWidthE n ns d D₁ R ≤ W`  (§3).

9. **Root statement** (`driverRoot_decides_sentence`): cost
   `Kdec + (Kl 0 (n + ns) + Ksent)` (weight at the all-alive root mask;
   `arenaSize_of_all_alive` gains the weighted twin
   `arenaWeight_of_all_alive = n + ns`), plus the B7-side prologue
   charge `Kpro ≤ kpro·bsq·(w+1)` for allocation at `W = chainWidthE`
   and the dedup pass (G1's `O(n + ns)`). Close: probe
   `g2_root_close` then `g2_c0_shape` (composes with the landed
   `sigma_root_almostLinear` — the real-ε massage B7 consumes).

Compatibility note: there is **no** constant-instantiation
compatibility this time (unlike rebase B2's `uniform_recovers_level`) —
the point of G2 is exactly that the old carrier-width dischargers may
NOT discharge the new phase slots. The probe's honesty controls are the
replacement compatibility story: the landed *engine* exports fit the new
budgets at the root arena.

## §3 The width repair (item ii)

(a) **Degree-aware width.**
`chainWidthE n ns d D₁ r := n·(budget d D₁ r + 1)² + ns + 1` — the
`n·n` of `TgtCoupling.chainWidth` (there to hold the level's own graph
at the generic `csrSlots_le_sq`) dies against the actual slot count
`ns`. Probe: both "fits" lemmas re-proved
(`csrSlots_lt_chainWidthE` at the hypothesis `csrSlots F ≤ ns` — true
of the level's graph exactly and of every masked sub-arena by subgraph
monotonicity; `csrSlots_fratGraph_lt_chainWidthE` verbatim), the
arena-linearity `chainWidthE ≤ bsq·(n+ns+1)` (the load-bearing cost
fact), domination `chainWidthE ≤ chainWidth` on real inputs, and the
floor-death `width_step_dead` + `#guard` (new width `227·10⁶ + 1` vs
`n² = 10¹²` at a sparse instance).

Consumers to re-thread, by name (from `lean_references`/grep):
`TgtCoupling.chainWidth` def + its two fits lemmas;
`RamDriverCompose.chainWidth_eq_augWidth` (:2261 — becomes
`chainWidthE = augWidthE n ns (budget …)` with
`augWidthE n ns d := n·(d+1)² + ns + 1` replacing
`RamAugment.augWidth`'s `n·n`); `fold_step` (:2474, uses
`augWidth_mono` + the eq — mechanical); the `n·(2b) ≤ chainWidth` step
at :2923 (lives in the `(b+1)²` term — unaffected);
`orderImplementsR`'s `hWc` (:2724); `RamAugment`'s `augWidth ≤ W`
consumers (`:815/:830/:843/:851` — the `m' ≤ n²` capacity steps flagged
at `RamDriverAugment:5988/6061` must re-discharge from `m' ≤ ns` /
`m' ≤ n·budget` via `arcs_le`; this is the one place the walk content
changes, not just the statement); `TgtWidenProbe` (probe file, gets a
new instance); `C0Probe` (frozen record — untouched, its floor is
*about* the old width).

(b) **Live-width save/restore and relink copies.** The four `.lit W`
sites (`RamDriver.lean:1559/1589/1594/1767`) copy a runtime-computed
live prefix instead:

- **the scalar**: `"lw"` (live width), written by the phase prologue as
  `lw := (n)·bsq-part + m` — concretely, the produced value is
  `liveWidth` = the compacted arena's `m·bsq + e + 1` (probe:
  `liveWidth b m e`, weight-linear by `liveWidth_le`). Its *producer*
  is the same compaction scan that produces `arenaWeight` (§1): the
  member scan accumulates `1 + deg v`; the `bsq` part is the per-vertex
  chain-row budget, a parameter-computed scalar the prologue derives
  from `R` by the budget recursion **in program text** (a
  `foldRange`-of-squarings over `R` — `R` is a parameter, so this is a
  constant-length straight-line block, uniform in the input).
- **walk deltas**: `saveCsr`/`restoreCsr` copy `lw` cells
  (`copyUpto … (.var "lw")`); their specs
  (`RamDriverOrder.saveCsr_spec` etc.) re-state at
  `σ.vars "lw" = liveWidth …` with the padding argument (F-c-4's flip)
  replaced by a *live-prefix* invariant: cells ≥ `lw` are 0 on both
  sides (the zero-tail clause the phase already maintains between
  rounds), so restoring the prefix restores the array. `augRelinkCom`'s
  two copies identical. The offset copies (`n+1` cells) become
  member-driven only in the compacted-CSR variant (E2) — at the root
  they are already within `O(w)`.

(c) **The compacted arena CSR** (the deeper program delta, E2): at
nested depths the phase must not walk `off[0..n+1]` at all — the arena
hands down its member list (R1.6, threaded like the masks are today)
and the engines read the level graph through it. This is where
`saveCsr`'s `n+1`-cell offset copy, the `fillCom … "n"`-bounded fills
inside `orderCom`/`augRelinkCom`, and the elimination/BFS carrier scans
all get their arena-driven form. Without E2 the order phase still pays
`Θ(n)` per level entry — `n²` at depth 1; the interface form of §2.1
is only dischargeable after E2.

## §4 Text uniformity (item iii — a correctness constraint)

C0 (`concepts/Lax3/ModelChecking.lean:77`) fixes ONE program before
`∀ n G w`. Sweep result (grep over `.lit` with non-numeral arguments in
`RamDriver.lean`): the only input-scaling literal in the text is `W`,
at exactly the four sites above; `mb`, the fold literals and the table
indices are formula/parameter constants; every loop bound is
`.var`-driven (`fillCom` reads `"n"`; decode leaves `"n"`/`"m"`).
Compiled finding: `G2CostProbe.saveCsr_reads_W` / `orderCom_reads_W` —
two widths give two programs.

**Target text parameter list: `driverRoot q_top cap mb R ℓ φ`** — all
formula/class parameters, no `W`. The allocation width lives in the
precondition Props only (`DecodeMem`/`OrderMem`/`LevelPre` keep their
`W` as a *proof-side* parameter about the store, exactly as `n`/`ns`
already are); the program reads the runtime scalar `"lw"` (§3b). The
`ComputesInTime` bridge's memory prologue allocates by writing zeros up
to the runtime-computed width — `O(W) = O(bsq·(w+1))` once, at the
root, accounted in the probe's `g2_root_close` as `Kpro`.

## §5 The per-phase capital table

Phase → landed export (+cost) → target form → gap (∅ = re-thread only).

| phase / slot | landed export, cost | target form | gap to close in execution |
|---|---|---|---|
| order: eliminations | `ElimSynth6.elimEngine5_le`, `engineK5 = 333n+168ns+45` | `≤ 333·(w+1)` at root (probe `engineK5_le_weight`) | block-driven variant for nested arenas (E2); at root: ∅ |
| order: BFS under it | `BfsBridge.bfsQCom_spec(W)`, `56n+40ns+65` | `≤ 65·(w+1)` (probe `bfsQCost_le_weight`) | block-driven variant (E2) |
| order: augment rounds | `RamDriverAugment.implements(W)` walks; `augCost = 8000(n+W+1)`, `relinkCost = 140n+20W+170` | `≤ 16840·bsq·(w+1)`/round (probe `orderPhaseCostR_le_orderCostA`) | live-width copies (E1) + arena-driven fills (E2); walks exist |
| order: save/restore | `saveCsr_spec` at `.lit W` | one `liveWidth` copy per entry, `≤ 60·bsq·(w+1)` | E1 (scalar + spec re-state) |
| order: symmetrization | `symCom` walk (F-c) | inside `2310·bsq` | in-list copy at `lw` (E1) |
| cover: emission | `CoverSynth.emitLoopCost` — **carrier-free**, `2·touches` asets, `towerEmitAgets = 3·touches` | per-centre `O(ball weight)` | compose emit with block-driven BFS per centre (E3) |
| cover: per-centre | `RamCover.centreCost = 100n+50ns+100` | `≤ 150·(w+1)` per centre (probe `centreCost_le_weight`); mass-charged over centres | E3: centre loop over member list; ball-weight reads |
| cover: wrapper | `coverPhaseCost` carries `12n²` (member copy) + `coverCost`'s `100n²` | mass-driven copy `O(mm)` | **program delta E3** (probe compiles unfittability) |
| turn: descend leaves | `BlockLeaves`: `blockLoadK 15m₁+15m+30`, `bandK 25m+4`, `bsubK 29m+4`, `bexpK 50m+30·degSum+4` — **no `n` anywhere** | `ct = 200` at block weight (probe `blockLeaves_le_weight`) | swap into `descendCom` (E4); B4c/N-1 composed clear+load; `m₁` cross-turn charge — see §7.4 |
| turn: scatter chain | `ScatterSynth.scatterTowerCom_spec`, `scatK = (94n+40ns+50)t+33n+4` — `Θ(n·t)` | `ksc·(s+1)` per turn | block-driven scatter engine (E4) — the one engine with no touched-only variant yet |
| turn: readback | `rbCost = (…)·n + 6` | coeff·(s+1), member-list header | R1.5 header delta (E4) |
| dead sweep | `DeadSweep.sweepImplements`, `(tc+4)n+6` | `sweepCoeffA·(w+1)` (probe `sweepCost_le_weight`) | member-list header (E5-adjacent, small) |
| base | `baseImplements`, `reprCost + (tc+4)n+6` | `baseCoeffA·(w+1)` (probe `baseCost_le_weight`) | member-list headers (R1.8) |
| mass | `MassAlive.aliveMass_le ≤ d·(arena+1)`; `ArenaBlock.mass_of_alive_compaction`; `MassMath.BlockInj` | weighted twins at `D·(w+1)` | E5 (math only, zero machine) |
| solver | `CostRecurrence.exists_driverCostsSigma` + `solve_sigma_le` + `sigma_root_almostLinear` | consumed as-is | ∅ (probe `g2_exists` demonstrates) |
| decode | `decodeImplements`, `decodeCost = 34n+12ns+46` | `≤ 46·(w+1)` (probe `decodeCost_le_weight`) | ∅ root-only; dedup (G1) adds `O(n+ns)` |
| sentence | `sentenceImplements`, atom costs `O(n+ns)` × formula-many | `ksent·(w+1)` | ∅ root-only |
| cluster load (old) | `ClusterSynth.clusterLoad0_le 12n+15m+19` | superseded | the `12n` fill is per-turn carrier → replaced by `blockLoadK` (BlockLeaves), do not wire |

## §6 The wave decomposition for G2 execution

Order matters; E1+E5 are parallel-safe from the start.

- **E1 — live width + uniform text** (one wave, single owner —
  `RamDriver.lean` text + `RamDriverOrder`/`RamDriverAugment` copy
  specs). The `"lw"` scalar, the four `.lit W` → `.var "lw"` swaps, the
  budget-recursion prologue block, `driverAux/driverAt/driverRoot`
  parameter list drops `W`, zero-tail live-prefix invariants replace
  the F-c-4 padding argument. Gate: the probe's `orderCom_reads_W`
  becomes *undischargeable* against the new text (state its analogue
  `orderCom R j` with no `W` argument — uniformity by signature);
  differential `#guard` on a two-width store pair.
- **E2 — compacted arena CSR + block-driven order phase** (the critical
  path; one wave per engine family, `levelImplements`-style single
  owner for the thread). Member-list threading into
  elim/BFS/augment/sym; `chainWidthE`/`augWidthE` swap with the
  `m' ≤ ns` capacity re-discharges (§3a consumer list); the arena
  save/restore at `liveWidth`. Lands §2.1 + §2.8.
- **E3 — block-driven cover phase** (one wave): centre loop over the
  member list, per-centre ball-weight BFS + the landed carrier-free
  emit, mass-driven member copy in `coverSave`. Lands §2.2.
- **E4 — turn re-thread** (one wave): `turnCostSizeA` into
  `turnCostSize` (the slot finally read), BlockLeaves swap into
  `descendCom` (incl. B4c/N-1 composed clear+load), block-driven
  scatter engine, readback header. Lands §2.5 + §2.7.
- **E5 — weighted mass mathematics** (parallel, zero machine):
  `arenaWeight`/`blockWeight` defs, weighted
  `mass_of_alive_compaction`, weighted descend clause, weighted
  `aliveMass_le`, `arenaWeight_of_all_alive`, and B4c/N-2
  (`degSum ≤ ns` — subsumed by `degSum(block) ≤ blockWeight`).
- **E6 — interface re-thread + re-discharge** (after E1–E5; one owner):
  `levelImplements` induction at weights, `levelAt` slots at the §2
  forms, `orderImplementsR` at `orderCostA`-shape cost, root restated
  (`Kl 0 (n+ns)`), plug checks re-run (`levelAt_of_sigma` twin at the
  new forms — the probe's `g2_exists` is its arithmetic skeleton).

Then the B7 re-run per plan (slot sweep first, general-`R` root on
`driverRootD`, `Spec`→`ComputesInTime` incl. prologue, C0). Fallback
clause unchanged: any structural blocker goes to Jan; the frozen
old-style wave is dominated (inherits both floors).

## §7 Slot audit: findings and corrections

1. **`hKdec`/`hKsent`/`hatoms` are clean** — root-only reads,
   `O(n + ns)` each, weight-linear (probe `decodeCost_le_weight`).
   No C0-boundary derivability issue found in them.
2. **The `hbnd → hcostI → hKsc` chain carrier-reads per turn** (§2.7)
   — `atomCost`'s `24·n + scatterCost n ns t` enters every turn via
   `Ksc`. Not previously named in the floor record (C0Probe's floor
   works off `hKo` alone); it is the same `Θ(n)`-per-turn class and
   dies with E4. No *derivability* problem — only cost.
3. **`coverPhaseCost` carries its own `12·n²`** on top of `coverCost`'s
   `100·n²` — the floor is thus not only in `hKo`; a `hKc`-only
   analogue of `level_interface_floor` would compile the same way.
   Recorded compiled (probe §5 negative findings).
4. **BlockLeaves' `blockLoadK m₁ m` reads the PREVIOUS turn's block**
   (the clear half). The Σ interface absorbs it with coefficient-2
   slack (`Σ_c (bs(c−1) + bs c) ≤ 2·Σ bs`); E4 must either charge the
   clear to the turn that wrote (trail-free, the B4c design) or widen
   the turn slot to `bs(c−1) + bs c`. The probe's `ct = 200` control
   uses `blockLoadK s s` — the equal-block reading; the doc notes the
   factor-2 headroom lives inside `driverASigma`'s `(D+1)` slack.
5. **Corrections to the session-wrap capital list**: `BfsQTrail` does
   **not exist** in the package (the touched-only-BFS role is filled by
   `BlockLeaves` + `CoverSynth.emitLoopCost`, both citing
   `TrailRecursion` §6.4 as their acceptance bar);
   `treset_cost_touched_only` lives in the word-ram package
   (`Lax13Proofs/Refine/Iicf/IicfTrailArray.lean:591`) and BlockLeaves
   deliberately declines it (`BlockLeaves.lean:46` — the write set is
   exactly known). `clusterLoad0_le`'s `12·n` is per-turn carrier: do
   not wire it; it is superseded by `blockLoadK`.
6. **No new C0-boundary underivability found.** The two known gates
   (CsrSimple/dedup = G1; the cost floor = this design) remain the
   complete list as far as this wave's sweep reaches: `hWB : n+W+1 < B`
   survives the width repair (`W` stays `poly(n)`); `hdeg` at nested
   masks needs only subgraph closure (hereditary, B7's existing plan);
   `hpad0`'s zero-tail moves into the live-prefix invariant (E1).

## §8 What the probe compiles (the record)

`proofs/Lax3Proofs/Refine/G2CostProbe.lean`, all green, kernel-three:

- **Existence** (`g2_exists`): a `CostRecurrence.solve` witness family
  satisfies — verbatim — the four proposed phase forms, the landed
  `hKmono`/`hKl` shapes, and the proposed size-reading turn form, and
  closes to `(ℓ·g2A + Cb)·(D+1)^ℓ·(w+1)`. Root close `g2_root_close`
  (decode + dedup + sentence + `O(bsq·(w+1))` prologue), C0 shape
  `g2_c0_shape` (composes the landed real-ε massage). Star numerics:
  the ε = 1 and ε = 1/2 budgets **clear** at the very instances where
  `C0Probe`'s guards showed the floor exceeding them (8 orders of
  magnitude of slack at ε = 1).
- **Floor-death**: `emptyArena_charge_const` + guard (the
  `orderPhaseCost ≤ Ko 1 0` step cannot start — the empty-arena charge
  is `n`-free); `level_interface_floor_analogue_refuted` (the full
  C0Probe derivation re-stated over the proposed forms is **false** —
  witnessed below the floor at the C0 width); `width_step_dead` + guard
  (the `n·n ≤ W` step dies against `chainWidthE`).
- **Honesty**: order (`orderPhaseCostR_le_orderCostA`, constants read
  off the landed defs; `orderPhaseCostR_honest_at_chainWidthE`), cover
  engines (`centreCost_le_weight`, `bfsQCost_le_weight`,
  `engineK5_le_weight`), turn leaves (`blockLeaves_le_weight` — the
  landed B4c exports), sweep/base/decode (generic in `φ`). Negative
  findings: `coverPhaseCost` and `descendCost` fit NO weight-linear
  budget (program deltas E3/E4, compiled). Negative controls: dropping
  the `bsq` factor, undersizing the turn coefficient to 30, and
  undersizing the order constant to 1600 each FAIL.
- **Uniformity**: `saveCsr_reads_W`/`orderCom_reads_W` — the current
  text is not one program across widths (needs `propext` alone).

Ledger: two additive files (this doc + the probe); imports wired and
committed by the supervisor; no frozen statement touched; the proposed
forms exist nowhere outside the probe's namespace.
