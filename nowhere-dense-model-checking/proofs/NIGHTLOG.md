
**Supervisor finding at this session's close — E-order's gate has
moved.** `Refine/OrderEngineProbe.lean`'s verdict refused the E-order
re-run on two premises: that `OrderBlockProbe`'s successor (2)
"member-driven engines, one wave per family" did not exist ("no
member-driven elimination, augmentation or symmetrization `Com` exists
in the package"), and that the first elimination's own share
`elimShare n W = 159·n + 276` — carrier-linear — already exceeded the
whole §2.1 budget at carrier 800. **Both premises are now stale.** The
E2 family landed the corrected form of (2) — compacted-arena engines,
the arena renumbered to `mm` and the engine run at carrier `mm` (in-place
member passes were themselves refuted) — for all three families:
`ElimCompact`, `SymCompact`, `AugCompact`, with the preps and the scatter
obligation discharged this session. And the charges are carrier-free:
`elimCompactCost mm w = 900·mm + 900·w + 400`, `augCompactCost mm kd W`,
no `n` in either.

This does **not** yet say the twelve interior shapes' refuting couplings
close — that is what the re-run must determine, and it is a wave, not an
inference. What it says is that E-order is no longer blocked on *missing
engines*, and the carrier-linear floor that made the budget unreachable
is gone. Road unchanged in order: E3b block cover + the `OrdersBy`
contract restated at members (the contract seam is what couples E2 to
E3) → E-order text + walk → B7 re-run → C0 → P5 draft.

**R1.8-T3-flip (b) (merge `ba84606`, 3585 jobs).** The dead-aware atom
program, additive — `clusterCom` byte-identical, the whole diff is
`+150` in `RamDriver.lean`, `+114` in `RamDriverWrites.lean`, the new
`Refine/ScatterDeadPass.lean` (1259 lines) and one import.

**The composition CLOSED; it did not stop at (c).**
`atomTerms_iff_scatVal` decides a scatter atom from three registers —
the engine's counter, the kill-bit sum, the probe bit times the outside
count — through `ScatterDeadEngine.scatVal_of_cnt`, **reading no table
row outside `alive ∪ kills`**. That is the whole content of the R1.8
flip, and it landed with **nothing of `TableInv`/`LevelPost` moved**.
The alignment that was the wave's declared stop-risk closes in
`turnKills_eq_dead_inter`: `KillListAt`'s set is stated at the parent
mask + cluster + batch and the dead fold needs `deadSet n Alv' ∩ X` at
the child mask, and the two are identified by T1's pointwise `BatchData`
clause in one direction and cluster alive-homogeneity in the other. The
hypothesis that costs, `hXalive`, is not a gap: it is
`MassAlive.clusterAt_subset_alive` at an alive centre, and
`RamDriverCluster.lean:1574` already runs that argument.

Five passes walked (`atomMemCom_spec` at `23·mm1+8` charged at the
*child's* member count, `killSumCom_spec` at `14·kq+8` carrier-blind,
`outProbeCom_spec`, `atomBitCom_spec_found/_empty`, `atomFlagCom_spec`);
the sixth is the landed engine at an untouched `scatBlockK`.

**Refute-before-prove earned its keep against a supervisor instruction.**
The brief told the worker to model the filter on `RamDriver.memFilterCom`.
That would have been **wrong**, and `inplace_filter_refuted` compiles
why: a turn decides every atom of every tabled formula against the same
child member list, so in-place compaction lets the first atom shorten
the list and the second atom then reports the empty list where the truth
is one member. `atomMemCom` is out-of-place for exactly that reason.
Also compiled: `empty_class_probe_refuted` (with the class empty the
probe register still holds an *in-cluster* vertex, so the found flag is
load-bearing) and `atomTerms_compose` (all four new driver passes run in
program order on a ten-vertex turn, no scratch-name collision).

**Second structural finding of this road, and it shapes (c).**
`scatBlockCom` is strictly downstream of `RamDriver.lean`
(`ScatterBlockProg → ScatterBlockCost → MassWeight → ArenaBlock →
RamDriver`), so the composite cannot be defined in `RamDriver.lean` and
`clusterCom` cannot call it as written — the same class of defect as
a1's walk sitting downstream of the driver. (c) must either parameterise
`clusterCom` by the atom family (precedented: `inner` is already such a
parameter) or lift the engine's program text above the driver.

Honest residue, flagged not papered over: the end-to-end sequential
`Spec` for the nine-pass composite is not threaded (the two seam facts
that make its order sound — `warrs_scatBlockCom`,
`notMem_wvars_scatBlockCom` — *are* proved, and the composition is
compiled at a concrete arena), because (c) restates that precondition at
`TurnPre` when it re-derives `ScatterStep`. And `outProbeCost n = 20n+10`
is a carrier-width *bound* on an early-exiting scan — same parity as the
mask copy and distance fill, E4c's to narrow. No `turnCost` edit, so
`ctKL` is untouched.

**Dispatched next: (c1), the swap only** — `scatDeadCom` into the turn,
`ScatterStep` re-derived against it, `TableInv`/`LevelPost`/
`LevelImplements`/`LevelInv` frozen. The statement flip is (c2). The
split is deliberate: the new program is sound under the current
carrier-wide `TableInv` a fortiori, so the large `RamDriverFrames`
scatter discharge happens once against a stable invariant and (c2) then
weakens a precondition on an already-re-derived proof.
