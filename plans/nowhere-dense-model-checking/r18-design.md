# R1.8 design — dead vertices' obligations without the carrier

Rev 1, 2026-08-06. Author: R1.8-design (Fable). Status: **DESIGN
COMPLETE, COMPILED IN BOTH DIRECTIONS** — the verdict on the recorded
intent ("a vertex's death-row write charges to the turn that killed it —
its block contains it") is **holds for exactly half the dead set, and
the other half needs no writes at all**. The dead set of a child depth
splits along the turn's cluster: the **kill set** (in the cluster, dead
in the child mask) is block-contained and turn-charged, compiled
carrier-blind at `(3·t + 20)·kills + 6`; the **outside class** (out of
the cluster) is colour-uniform — every slot of the child palette lives
inside the cluster — so one representative and one bit per formula
carry it, and every per-vertex payment for it is a compiled carrier
walk. All compiled counterparts live in
`proofs/Lax3Proofs/Refine/DeadRowProbe.lean` (zero sorry, kernel-three
or less on every principal). No landed statement touched.

Standing rule honoured: every claim with a compiled counterpart cites
it by name; prose closures are not closures.

## Table of contents

- §1 The design in one paragraph, and the one new idea
- §2 The old → new statement deltas
- §3 The producer table, with charging slots
- §4 The consumer table, per reader of dead rows
- §5 Interactions with the in-flight roads (E-mem thread, E4)
- §6 The wave decomposition
- §7 Unresolved design questions (flagged, not silently resolved)
- §8 What the probe compiles (the record)

---

## §1 The design in one paragraph, and the one new idea

A vertex dead at depth `j + 1` is dead for one of two reasons, and the
two cost differently. Either it is **in the turn's cluster** — then it
is alive at depth `j` (clusters of alive centres are alive-homogeneous,
`MassAlive.inCluster_alive_iff`) and was killed by THIS turn's batch:
its row is written **at kill time**, by a new guarded pass over the
turn's own padded batch buffer `wa` (`≤ mb` entries), running inside
`clusterCom` right after `colourCom` (the row is the edgeless reading
at the child palette, `Refine.DeadRow.sat_bot_of_dead`, so the palette
must exist first), charged inside the turn's `turnCostSizeA` slot at a
formula-sized constant per turn. Or it is **outside the cluster** —
then no per-vertex anything is affordable (`n - bs` members,
`DeadRowProbe.no_coeff_pays_outsideRows`) and none is needed: every
colour class of the child palette lives inside the cluster
(`stepColoringP_subset`), so the whole class shares the EMPTY colour
row, its table bit is ONE value per formula (`sat_outside_uniform`),
and its role in every consumer reduces to a count (`n − mm − kills`, off
the member clause) plus a default-bit register. The sweep
(`RamDriver.sweepCom`) leaves the driver; `DeadRows`/`TableInv` weaken
their domains to `alive ∪ kills`; the base drops `reprCom` (dead code —
`tabled_isLocal`) and walks its member list.

**The one new idea: the outside class is colour-uniform.** The child
palette `stepColoringP` = `isoColoring` over `relColoring` has three
slot families, and all three vanish outside the cluster `X`: the
relativized slots by construction (`∩ X`, marker `X`), the two profile
families because their distances are measured in `deleteVerts A Xᶜ`,
where an out-of-cluster vertex is isolated and a walk out of it is nil.
Compiled: `DeadRowProbe.stepColoringP_subset`, and its two consequences
`sat_outside_uniform` (one bit per formula for the whole class) and
`sat_exU_bot_via_cluster` (the representative system is the cluster
plus ONE vertex — `cluster_repr_ncard` at `bs + 1`, found in `bs + 1`
probes by pigeonhole, `exists_outside_in_prefix`). This is what lets
the design pay the outside class with **zero writes** — the only escape
from `no_memCoeff_pays_deadRows` (`DeadSweep.lean` §4b), which killed
every charging scheme that still visits the class.

**No resurrection, at the landed interface.** Finding B8/1
(`Refine.DeadRow.descent_mask_not_pointwise_monotone`) proved
`BatchData`'s graph equation cannot give `M v = 0 → Alv' v = 0`, and
concluded the dead-vertex path must run at every level. The G2/E6
restatement has since given `DescendStep` a pointwise clause —
`∀ v, Alv' v ≠ 0 → v ∈ clusterAt …` (`RamDriverCluster.lean:637-638`)
— and from it plus the alive-centre guard the monotonicity IS derivable:
`DeadRowProbe.dead_stays_dead`. B8/1's consequence is superseded; the
kill-time row, once written, stays valid down the whole subtree (masks:
no nested pass writes `alvName (j+1)`; tables: a dead vertex's centre
is dead, so no turn writes its row —
`ArenaBlock.dead_vertex_has_no_alive_turn` — and the sweep, the only
other writer, is gone).

## §2 The old → new statement deltas

Everything verified against the worktree @ d2d7245 (post-R1.8-stop).

### 2.1 `DeadRows` (`RamDriver.lean:3109`) and `SweepImplements` (`:3121`)

`DeadRows` quantifies over `M v = 0` — the whole dead set. New: the
obligation becomes its **kill half** only, `DeadRowProbe.KillRows` —
the same row content, quantified `Xa v ≠ 0 → Alv' v = 0` at the turn's
cluster indicator. The split is exact and generic
(`deadRows_split`: `DeadRows ↔ KillRows ∧ OutsideRows`, a partition of
the quantifier domain), the kill half is inhabited wherever the landed
sweep ran (`killRows_of_deadRows`), and the dropped half is the exact
carrier forcer (`outsideRows_forced_by_deadRows`: the junk state
satisfies `KillRows` and refutes `DeadRows`, generic in `φ`).
`SweepImplements` and `sweepCom` (`:1595`) leave `driverAux`
(`:2100-2119`); the kill pass (§2.3) and the base's member sweep (§2.5)
are the residue. `hKd` (`RamDriverRoot.lean:374`, root slot `:661`)
becomes a constant-class slot — the probe's interface closure
instantiates it at `phaseMR 0 12` (`deadRow_interface_closes`).

### 2.2 `TableInv` (`RamDriver.lean:2245`) in `LevelPost` (`:2503`)

`TableInv`'s domain is the whole carrier ("the turns of the loop
partition the carrier"). New: `LevelPost` carries
`DeadRowProbe.TableInvOn` at the domain `{Alv ≠ 0} ∪ kills` — the
turns write the alive rows, the PARENT's kill pass wrote the kill rows
before the nested call, and the outside class is carried by the
count-plus-default-bit convention (§4). `tableInv_iff_on_split`
compiles that the carrier-wide form is exactly its two mask halves
(re-assembly by `eq_of_arrOf_eq` alone), so `levelImplements`'
partition step (`RamDriverCluster.lean:1240`, `LevelInv` `:1128`)
re-derives with the dead half supplied by the precondition instead of
the sweep. NOTE the inversion of supply direction: kill rows at depth
`j + 1` are a **precondition** of the nested call (written by the
enclosing turn), not a postcondition of the level — they survive
`inner` because nothing below writes them (§1, no-resurrection).

### 2.3 `clusterCom` (`RamDriver.lean:2006`) — the kill pass (program delta)

`clusterCom` gains one pass between `colourCom` and `inner`:

```
killCom j := walk "wa" (mb entries); at each entry alive-and-in-cluster,
  envName 0 := entry; foldIdx (botCom (j+1) β) over tablesAt (j+1);
  store the bits into tabName (j+1)
```

— the sweep's own per-vertex turn (`RamDriverBot.base_turn_spec`'s
body), run `≤ mb` times instead of `n`. Placement is forced from both
sides: after `colourCom` because the row content is the edgeless
reading at the CHILD palette (`sat_bot_of_dead` needs
`colName (j+1)`), before `inner` because `wa` does not survive the
nested call (`BatchData`'s docstring — the `ClusterWa` seam; the
guard's idempotence makes the padding's repeated first entry harmless).
Cost: `(turnCost (j+1) + c)·mb + c'` — a formula-sized constant per
turn, absorbed into the turn's `ct` (probe: stand-in compiled at
`(3·t + 20)·kills + 6`, carrier-blind, linear in kills, `t` the row's
own size class; `#guard 200 + 84 ≤ 284·(0+1)` pins the absorption at
the empty block).

### 2.4 `DescendStep` (`RamDriverCluster.lean:625`) / `BatchData` (`:532`)

The kill pass's spec needs the kill set **pointwise**: `BatchData`
gains the clause

```
∀ v : Fin n, Alv' (v : ℕ) ≠ 0 ↔ (M (v : ℕ) ≠ 0 ∧ v ∈ X ∧ v ∉ W)
```

— the strengthening finding B8/1 predicted would be the price, and the
descend walk already proves it: the stored mask is literally the cell
function of `RamDriver.masked_step` (`:358-380`), whose proof derives
exactly this equivalence on the way to the graph equation. Monotonicity
alone is already derivable without it (`dead_stays_dead` off the E6
inclusion clause), but the kill-write's postcondition ("every vertex of
`X ∩ alive ∩ W` has its row") needs the set, not the graph.

### 2.5 `baseCom` (`RamDriver.lean:1606`) and `hKbase`

Two deltas. (a) **`reprCom` (`:1491`) is dropped**: its product `"rep"`
is read only by `botCom`'s `exU` case, which is unreachable — every
tabled formula is local (`DeadRowProbe.tabled_isLocal`, off
`FormulaTables.tableRank_of_mem_tablesAt`; `RamDriverBot`'s own header
records that the case "is not walked, and cannot be", discharged by
`isLocal_exU` at `RamDriverBot.lean:715/792`). The landed
`reprCost` carrier scan (`RamDriverBot.lean:175`, the floor
`G2CostProbe.hKbase_gap` compiled) guards dead code. (b) the sweep
half's header moves to the member list — legitimate NOW because the
base's obligation domain is `alive ∪ kills` (§2.2), the kill rows
arriving from the depth-`(ℓ-1)` turn's kill pass. `baseCost`
(`RamDriverBot.lean:1641`) goes from `reprCost + (tc+4)·n + 6` to
`(tc + c)·mm + c'`; `hKbase` (`RamDriverRoot.lean:371`, root slot
`:658`) discharges at `G2CostProbe.baseCoeffA` **minus its
`reprBodyCost` term**, read at the weight. The `hW` carrier story
(`BotEval.lean:306`) is thereby moot for the landed surface; the probe
compiles the contingency anyway (`sat_exU_bot_via_cluster` +
`cluster_repr_ncard` + `exists_outside_in_prefix`: cluster-plus-one
representatives, found in `bs + 1` probes) — it is also the uniformity
germ E4's scatter fold consumes (§4).

## §3 The producer table

| producer | program | cost, compiled | charging slot |
|---|---|---|---|
| **kill pass** (per turn, depth `j` writing depth `j+1` rows) | `killCom j` between `colourCom` and `inner` (§2.3): guarded walk of `wa`, `botCom (j+1)` fold per kill | probe `killTurnCom`: `(3·t + 20)·kills + 6`, **carrier-blind** (equal at 100/200 at kills ∈ {0,2,3}), linear in kills, `t` = the row's size class (table count), guard-dead run writes nothing | inside the turn's `turnCostSizeA` slot: `ct = 200 + 84 → 284` at the probe's instance (`deadRow_interface_closes`, `#guard` at `s = 0`); the real constant is `turnCost (j+1)·mb`-class — formula-sized, not carrier-sized |
| **outside class** (per level) | NO program — a count (`n − mm_{j+1} − kills`, all landed scalars/clause 16) and, where a consumer needs the bit, one `botCom (j+1)` eval at the empty row | `O(1)` per level; the class's bit is well-defined by `sat_outside_uniform` | the vestigial `Kd` slot at a constant (`phaseMR 0 12` in the closure) |
| **base member sweep** (depth `ℓ`) | `sweepCom`'s loop at the member-list header (the R1.8/1 refutation no longer applies: the domain shrank to `alive ∪ kills`, and the kill rows arrive from the parent turn) | `(tc + 4)·mm + 6`-class — `sweepCoeffA·(w+1)` by the landed honesty `G2CostProbe.sweepCost_le_weight` read at `mm ≤ w` | `Kl ℓ` (`Cb·(w+1)`), `hKbase` |
| **the dead route** (negative) | any per-level/per-entry dead-set pass (`deadScanCom`, the landed sweep's loop shape) | **`Ω(n)` compiled**: `+15/carrier vertex` between 100 and 200 at a fixed 3-kill arena (`84` vs `3006`); and per-vertex outside materialization dies by arithmetic (`no_coeff_pays_outsideRows`) | none — this is R1.8/1 (`no_memCoeff_pays_deadRows`) re-read at the program |

## §4 The consumer table, per reader of dead rows

| consumer | landed read | what changes |
|---|---|---|
| readback local atoms (`readbackCom`, `RamDriver.lean:1990`; `atomExpr .inl`) | `tabName (j+1)` at `asg v = cur` vertices | NOTHING — its whole dead-read domain IS the kill set (`readback_dead_read_is_kill`: an `asg`-visited vertex is alive at `j` and in the turn's cluster, so dead-at-`(j+1)` means killed-by-this-turn), and those rows are written at kill time |
| scatter pass (`scatterCom` `:1957`; `ScatVal`, `RamDriverCluster.lean:502`) | `tabName (j+1)` over the carrier — the greedy set `{a ∣ Sat …}` genuinely contains dead vertices (isolated, hence all mutually scattered) | the ONE consumer that reads the outside class per-vertex today. E4's block-driven scatter folds it arithmetically: dead contribution = individual kill bits + (default bit × outside count) — `sat_outside_uniform` is the compiled germ; the greedy-count split is flag F-3 |
| base evaluator `exU` (`botCom`, `reprCom`'s only reader) | `"rep"` | unreachable (`tabled_isLocal`); pass dropped; contingency compiled (`sat_exU_bot_via_cluster`) |
| sentence readback / root (`RamDriverIO`, `SentenceImplements` `RamDriver.lean:3297`) | `TableInv` at depth 0 | unaffected — the root is all-alive (`∀ v < n, M v ≠ 0` hypothesis), no dead rows exist |

## §5 Interactions with the in-flight roads

**E-mem thread (landed).** The kill pass does NOT ride `descendCom`'s
filter chain, though that is where the kills happen: at
`subCom (resName j) (batName j) (alvName (j+1))` the child PALETTE does
not exist yet, and the row content is the edgeless reading at that
palette. The pass rides `clusterCom`, after `colourCom`, reading the
same `wa` buffer the colouring just consumed — the `ClusterWa` seam
(`RamDriverCluster.lean:562`) closes over `enumBatch`,
`colourCom` AND the kill pass, still strictly before `inner`, so no
clause about `wa` crosses the recursion (the constraint `BatchData`'s
docstring records). The member clause (LevelPre 16, `MemEnum`,
`RamDriver.lean:2478-2495`) supplies the base sweep's header and the
outside COUNT (`n − mm − kills`); `memFilterCom` stays at
`descendCom`'s tail untouched.

**E4 turn re-thread (block leaves + scatter).** The kill pass's charge
sits in the same `turnCostSizeA` slot BlockLeaves' `ct = 200` occupies
— the closure runs at `ct = 284` and the interface is indifferent
(`deadRow_interface_closes`). The scatter engine — already "the one
engine with no touched-only variant" (g2-cost-design §5) — acquires the
dead-fold obligation of §4 as part of its E4 re-derivation, not as a
separate wave: its input contract shrinks from carrier-wide `TableInv`
to `alive ∪ kills` rows + outside count + default bit.

**E5/mass.** Kill count ≤ `mb` per turn needs no mass lemma; the
outside count is `n − mm − kills` off landed scalars. No interaction.

## §6 The wave decomposition

- **R1.8-T1 — masks pointwise (descend owner).**
  `RamDriverCluster.BatchData` + `DescendStep` gain the pointwise mask
  clause (§2.4); `RamDriverDescend`'s walk exports it off
  `masked_step`'s cell function. Small, self-contained, unblocks T2.
- **R1.8-T2 — the kill pass (turn owner).** `killCom` into
  `clusterCom` (§2.3), its spec (`KillRows`-shaped post at the
  pointwise kill set), `clusterStepImplements`
  (`RamDriverCluster.lean:871`) re-derived with the new pass and the
  readback's dead reads discharged from it
  (`readback_dead_read_is_kill` is the template); `Ks`/`ct`
  re-derivation at the absorbed constant.
- **R1.8-T3/E4 semantic layer — LANDED (`3af24e7`).**
  `Refine/ScatterDeadFold.lean`: the F-3 greedy-count split
  refuted-then-proved (`ncard_greedySet_fold`), the outside-class bit
  (`outside_ncard_of_probe`/`outside_ncard_of_empty` — one probe vertex
  found in ≤ bs+1 steps collapses the outside term to
  `if bit then count else 0`), `sum_bit_eq_ncard_inter` (a
  repetition-free kill list's bits sum to the kill term), and survival
  (`row_survives_turn`/`row_survives_chain` off
  `dead_vertex_has_no_alive_turn` + `Compacted.alive` +
  `ClusterFrames`). `Refine/ScatterDeadEngine.lean`:
  `scatBlockCnt_specW` — the active-set engine re-derived with its
  counter exported in the `∀ e` decision form (the naive `cnt = count`
  is compiled-refuted at the threshold cap), same charge `scatBlockK`;
  `scatVal_of_cnt` — `ScatVal` decided by counter + kill scalar +
  outside scalar, no read outside `alive ∪ kills`. F-2 audit: empty
  (game mask feeds only ball/path machinery; no table indexed by it).
- **R1.8-T3-flip — the statement flip (successor wave, ONE boundary).**
  (a) `killListCom j` in `clusterCom` between `killCom` and `inner`
  (ClusterWa seam extends over it): repetition-free kill list
  `klName j` + count `kkName j`, dedupe by O(mb²) prefix membership
  scan — avoids strengthening the landed `EnumStep` post (ClusterWa
  pins only the range of `wa`). T2's `KillStep`/`KillPass` untouched.
  (b) New atom program replacing `scatterCom`: filtered child member
  list (tab-bit test → `MemList` for satSet ∩ alive), `alv` copy +
  `dist` fill (carrier-charge parity with the landed engine this
  boundary), `scatBlockCom σs.r σs.t`, kill walk
  (`sum_bit_eq_ncard_inter`), outside probe (first `z` with
  `alv'[z] = 0 ∧ clu[z] = 0`; `botCom (j+1) σs.β` at it = the class
  bit), `flag := (σs.t ≤ cnt + kc + obit·oc)`. (c) The flip:
  `LevelImplements`/`LevelPost` gain a pre-written-domain parameter
  `D ⊆ dead` (pre `TableInvOn … D`, post `TableInvOn … ({alive} ∪ D)`);
  turn instantiates `D' :=` its kill set off `KillRowsAt`; `sweepCom`
  leaves `driverAux`/`driverAt_succ`; `LevelInv` table clause
  `v ∈ D ∨ earlier-turn`; `levelImplements` partition re-derived (the
  landed `hdeadne` block is already the survival argument);
  `ScatterStep`/`ReadbackStep` preconditions to `TableInvOn`. Edits
  beyond the T3 files: `RamDriverFrames.lean` (`scatterStep` discharge
  — the large one), `RamDriverBase.lean` (`readbackStep` precondition
  weakening), `RamDriverWrites.lean` (frames for `klName`/`kkName`),
  `RamDriverRoot.lean` (`hKd` vestigial at `phaseMR 0 12` per
  `deadRow_interface_closes`).
- **R1.8-T4 — the base (base owner).** T4a: drop `reprCom` (§2.5(a)).
  T4b: member-list header on the base sweep, `baseCost`/`hKbase` at
  the shed constant (§2.5(b)). Parallel to T3 after T2.

T1 → T2 → semantic layer → (T3-flip ∥ T4), flip after T4a lands (file
overlap in the driver files).

## §7 Unresolved design questions (flagged)

Supervisor dispositions, 2026-08-06 (r18 thread waves dispatched on
these): F-1 no bridging shim — T3 lands in ONE boundary with E4's
block-driven scatter re-derivation, single owner; T1/T2/T4 proceed
independently. F-2 T3 owner's audit obligation during the 17-file
`LevelPre` radius sweep, expected empty; if a `Gm`-side dead-row
consumer surfaces, the same kill/outside dichotomy applies (the ball is
block-contained). F-3 the greedy-count split is the T3+E4 wave's FIRST
obligation, refute-before-prove; the per-atom outside-bit fallback
(same `O(1)`-per-level) is pre-authorized without a fresh supervisor
round-trip. F-4 absorb the kill charge into `ct` (the probe's
`ct = 284` closure), depth-indexing through `tablesAt (j+1)` accepted;
it moves to its own `Ksc`-style slot only if the B7 root re-run demands
a depth-free `ct` — the closure is indifferent, so no pre-emptive slot.

- **F-1, the T3/E4 ordering.** The scatter pass is the one landed
  consumer of outside-class rows (§4). Weakening `TableInv` before the
  E4 scatter fold lands would strand `scatterCom`'s discharge. Options:
  land T3 and E4-scatter in one boundary, or bridge with a temporary
  outside-fill only where a scatter atom exists (`tablesAt`-dependent).
  Owner: the E4 brief. This road's T1/T2/T4 are unaffected.
- **F-2, `Gm`-side kills.** The game mask `gamName (j+1)` also kills
  vertices (`subCom … (batName j) (gamName (j+1))`), but no table is
  indexed by the game mask — the obligation audit found no `Gm`-side
  dead-row consumer. Confirm during T3's sweep of the 17-file
  `LevelPre` radius; if one surfaces, the same dichotomy applies (the
  ball is block-contained).
- **F-3, the greedy-count split.** The E4 fold needs
  `|greedySet A r S| = |greedy over alive part| + |S ∩ dead|` (isolated
  vertices are mutually scattered and scattered from everything) — a
  semantic lemma about `ScatterCore.greedySet`, plausible and not
  compiled here. `sat_outside_uniform` supplies the membership-side
  uniformity; the count-side identity is E4's first obligation. If it
  fails as stated, the fallback is per-atom outside-bit precomputation
  at the SAME `O(1)`-per-level cost, so the budget shape is not at
  risk — only the lemma inventory.
- **F-4, `mb` in `ct`.** The kill charge absorbed into `ct` makes the
  turn coefficient `turnCost`-dependent (formula-sized, constant in
  `n`) — same class as `ct = 200`'s BlockLeaves provenance, but now
  depth-indexed through `tablesAt (j+1)`. If the root re-derivation
  wants `ct` depth-free, the kill charge moves to its own
  `Ksc`-style per-turn slot; the closure is indifferent (both are
  `turnCostSizeA`-shaped).

## §8 What the probe compiles (the record)

`proofs/Lax3Proofs/Refine/DeadRowProbe.lean`, all green, zero sorry,
kernel-three or less on every principal (`#guard_msgs`-pinned §7 of the
file):

- **No-resurrection**: `dead_stays_dead` (B8/1 superseded at
  `DescendStep`'s E6 clause), `readback_vertex_in_cluster`,
  `readback_dead_read_is_kill` (the readback's dead-read domain is the
  kill set — "its block contains it", compiled).
- **Uniformity**: `relColoring_subset`, `isoColoring_notMem_of_isolated`,
  `stepColoringP_subset` (the child palette lives in the cluster);
  `sat_bot_swap₁`, `sat_dead_uniform`, `sat_outside_uniform` (one bit
  per formula for the whole outside class).
- **Base story**: `hW_of_outside_uniform`, `sat_exU_bot_via_cluster`
  (+ concrete four-vertex instance `hW4` and the `n = 0` gate
  `hW_zero_carrier`), `cluster_repr_ncard` (`≤ bs + 1`),
  `exists_outside_in_prefix` (found in `bs + 1` probes),
  `tabled_isLocal` (`reprCom` is dead code).
- **The split**: `KillRows`/`OutsideRows`/`deadRows_split` (exact
  partition), `killRows_of_deadRows` (satisfiability inherited from the
  landed sweep), `killRows_zero_carrier` (flip gate),
  `TableInvOn`/`tableInv_iff_on_split`, and the separation
  `outsideRows_forced_by_deadRows` (junk state: kill half holds, landed
  `DeadRows` refuted — generic in `φ`).
- **Cost, positive**: `killTurnCom` pinned `(3·t + 20)·kills + 6` —
  carrier-blind at 100/200, linear at kills ∈ {0, 2, 3}, per-row at the
  row's size class `t` ∈ {0, 2}, touched-only (killed cells written,
  neighbours and guard-dead runs untouched).
- **Cost, negative**: `deadScanCom` at `+15/carrier vertex` (the
  `Ω(n)` of `no_memCoeff_pays_deadRows` at the program; `84` vs `3006`
  on the same three dead rows), `no_coeff_pays_outsideRows` (the
  outside class beats every block-read coefficient).
- **Interface closure**: `deadRow_interface_closes` —
  `G2ExistsRevalidation.g2m_exists` at `ℓ = 3`, `D = 8`, `R = 0`,
  order/cover at the measured `68/12`, the dead slot at the constant
  `phaseMR 0 12`, `ct = 284 = 200 + 84` (BlockLeaves + the measured
  kill write, absorption `#guard`ed at `s = 0`), `ksc = 10⁴`, base
  clause generic.

Ledger: two additive files (this doc + the probe) plus one root-import
line in `Lax3Proofs.lean`; no landed statement touched; every proposed
delta exists nowhere outside the probe's namespace.
