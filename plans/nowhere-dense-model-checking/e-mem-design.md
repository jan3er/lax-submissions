# E-mem design — member-list threading into `LevelPre`

Rev 1, 2026-08-06. Author: E-mem-design (Fable). Status: **DESIGN
COMPLETE, COMPILED IN BOTH DIRECTIONS** — the clause is inhabited by
driver-shaped machines (root AND descend-updated child), the producer
is compiled at `≤ c·(block size)` with the mask-only route compiled
`Ω(n)`, the consumer wiring runs carrier-blind on landed capital, and
the order-floor escape is compiled against `OrderBlockProbe`'s own
instance — all in `proofs/Lax3Proofs/Refine/MemThreadProbe.lean` (zero
sorry, kernel-three axioms on every principal). No frozen surface
touched; the proposed clause lives in the probe as `LevelPreM` and
moves into `RamDriver.LevelPre` only in the thread wave of §6.

Standing rule honoured: every claim with a compiled counterpart cites
it by name; prose closures are not closures.

## Table of contents

- §1 The design in one paragraph, and the one new idea
- §2 The old → new statement deltas (`LevelPre`, `DepthMem`,
  `levelPre_run`, `DescendStep`)
- §3 The producer table, with charging slots
- §4 The consumer table, per engine family
- §5 The `ElimSynth7` `arrOf` pin, and the E29 allocation story
- §6 The wave decomposition for the thread
- §7 Unresolved design questions (flagged, not silently resolved)
- §8 What the probe compiles (the record)

---

## §1 The design in one paragraph, and the one new idea

Each depth `j` gains a **member list**: an array `memName j`
(`"mem" ++ j`, fixed physical length `n`, live prefix) and a count
scalar `mnumName j` (`"mm" ++ j`), tied to the depth's own mask by
`Refine.ScatterBlock.MemList (markSet n M)` — sound, complete,
strictly increasing. The names follow the `cpsName`/`cnumName`
precedent (`RamDriver.lean:807/811`) at the `alvName → "alv"` copy
pattern: per-depth name = fixed engine name + depth numeral
(freshness compiled in the probe §1).

**The one new idea: the clause is existential.** `LevelPre` keeps its
signature — no new `M`-style parameters thread through the 113
occurrences and every phase-`Implements` `Prop` — because a strictly
increasing sound-and-complete enumeration of a determined set is
unique: `MemThreadProbe.memList_unique` compiles that two witnesses
agree in count and, cell for cell, on the live prefix. So the clause
rides as one appended `∃`-conjunct (the `DepthMem` `∃ g` idiom), and
the blast radius is exactly: one added component at each positional
destructuring, two added frame side conditions at `levelPre_run`, and
the producer/consumer program deltas of §3/§4. Consumers extract the
same list at every program point; exact-array frame (junk tail
included) continues to come from `∉ warrs`, as it does for every
other name.

The clause carries **no tail-content conjunct**. Two reasons, one per
direction: satisfiability (`memClause_zero_carrier` — the F-c-4
flip-gate lesson re-checked at `n = 0`; a range-style tail clause is
the exact shape that killed the first `tgt` padding form), and cost
(a zero-tail obligation would force producers to clear junk tails —
a carrier walk, i.e. a touched-only violation; the E25–E29 space
substrate wants the tail dead, not zeroed).

## §2 The old → new statement deltas

Everything here is verified against warm `main` @ 36dd877.

### 2.1 `LevelPre` (`RamDriver.lean:2345-2354`)

**15 clauses today** — the docstring "thirteen clauses" at
`RamDriverCompose.lean:262` is stale (it predates the F-c-4 tail and
word clauses) and should be corrected to the new count when the thread
wave touches the file. Old → new, with positions so the destructuring
repairs are mechanical:

| # | clause | new |
|---|---|---|
| 1 | `σ.vars "n" = n` | unchanged |
| 2 | `σ.arrs "off" = arrOf (n+1) O` | unchanged |
| 3 | `σ.arrs "tgt" = arrOf W T` | unchanged |
| 4 | `σ.arrs (alvName j) = arrOf n M` | unchanged |
| 5 | `σ.arrs (gamName j) = arrOf n Gm` | unchanged |
| 6 | colours `= arrOf n (C c)` | unchanged |
| 7–9 | value bounds `M`/`Gm`/`C` | unchanged |
| 10 | `LevelMem` | unchanged |
| 11 | `DepthMem` | unchanged (its own delta below) |
| 12 | `σ.vars "m" + σ.vars "m" = ns` | unchanged |
| 13 | `OrderMem` | unchanged |
| 14 | zero tail of `tgt` | unchanged |
| 15 | word bound on `tgt` | unchanged |
| **16** | — | **`∃ Mem mmj, σ.arrs (memName j) = arrOf n Mem ∧ σ.vars (mnumName j) = mmj ∧ MemEnum n mmj Mem M ∧ ∀ z < mmj, Mem z < B`** |

Two spellings in clause 16 are deliberate. `MemEnum` is the driver-side
twin of `ScatterBlock.MemList … (markSet n M)` — `Refine.ScatterBlockProg`
depends on `RamDriver`, so the clause cannot cite `MemList` directly; the
equivalence (`memList_of_memEnum`) is compiled in the gate satellite so
the twin cannot drift. And the word bound covers the LIVE PREFIX only
(`z < mmj`, not `z < n`): the junk tail above the emitted prefix has no
provenance — bounding it would demand exactly the carrier walk this
design forbids, the same reason the clause carries no tail-zero conjunct —
and consumers only ever read `z < mm` through the live-prefix copy.

Probe name: `MemThreadProbe.MemClause` (the conjunct),
`MemThreadProbe.LevelPreM` (the assembled shape). Appending at the END
means a positional `⟨h1, …, h15⟩` destructuring repairs by one added
component; sites whose last pattern is `-` or a pass-through name
still need the check that the pass-through is rebuilt at the same
depth (see the repair list in §6).

### 2.2 `DepthMem` (`RamDriver.lean:2175-2180`)

The `Sized` list gains a 13th entry `(memName j, n)`. Every clause of
`DepthMem` is a length, so `DepthMem.get/setArr/setVar/run` extend by
one list element with no new argument — the probe's
`depthMem_childEnv` uses the landed transports unchanged. The count
scalar needs no allocation clause (scalars are total).

### 2.3 `levelPre_run` (`RamDriverCompose.lean:295-313`)

Gains `hmemA : memName j ∉ c.warrs` and `hmm : mnumName j ∉ c.wvars`;
the walk transports clause 16 by `hr.frame_arr`/`hr.frame_var` and
repackages the `∃`. **Every caller gains two discharges**, in the
`alvName_notMem_*` style (`RamDriverCompose.lean:317-323`): one
`simp [memName/mnumName, …, String.ext_iff]` lemma per phase `warrs`
/`wvars` list. Frame-section radius: ~16 files / ~167 `alvName`-name
sites (incl. `RamDriverWrites`/`RamDriverDedup`, which carry names but
no `LevelPre`); `LevelPre` radius: 17 files / 113 occurrences.

### 2.4 `DescendStep` (`RamDriverCluster.lean:623`) and `descendCom`

Program delta (§3 P-child): `clusterLoad` gains the emission add-on
and `descendCom` gains the filter pass after its last `subCom`.
Statement delta: the postcondition's `∃ (X W : Set _) (Alv' Gam' : _)`
block gains the child list export —

```
∃ Mem' mm', σ'.arrs (memName (j+1)) = arrOf n Mem' ∧
  σ'.vars (mnumName (j+1)) = mm' ∧ MemList n mm' Mem' (markSet n Alv')
```

— most naturally as a new conjunct of `BatchData` (the "state of the
next depth" packet the `hlevin` sites already read their mask content
from). The two `hlevin` constructions
(`RamDriverCluster.lean:921-926`, `RamDriverFrames.lean:1035-1039`)
then extend by one component from `hdat₃`, exactly as `halv₃`/`hgam₃`
do today; the clause must survive `henum`/`colourStep` to `σ₃`, which
is the standard frame discharge (neither writes `memName (j+1)` nor
`mnumName (j+1)`).

## §3 The producer table

Sortedness is a supply chain, and the compiled probe pins each link:
`MemList.smono` at the child comes from the block row's order; the
block row's order comes from the cover's emission scan.

| producer | program | cost, compiled | charging slot |
|---|---|---|---|
| **P-root** (depth 0) | after decode/dedup: `mem0[i] := i` for `i < n`, `mm0 := n` — the identity enumeration of the all-ones root mask | `O(n)`, at the root only — the root arena IS the carrier (`w = n + ns`), so this is weight-linear where it runs | `Kdec`-side (the G1 dedup pass is already `O(n + ns)` there); witness shape `MemThreadProbe.levelPreM_root` |
| **P-child, emission** (raw block list) | one store + one counter bump inside `clusterLoad`'s existing block scan (`RamDriver.lean:1826-1831`): `mem_{j+1}[bq] := xmm[p]; bq := bq + 1` | delta = `8·bs + 2`, **carrier-blind** — `MemThreadProbe` §4 guards pin the delta equal at carriers 100/200 and linear at `bs ∈ {0,2,3}`; emission order = row order, compiled `[7,13,91]` | inside `DescendStep`'s `Kd` (the turn's descend slot, `clusterStepImplements`'s `hK`); spec extends `clusterLoad_spec` (`RamDriverDescend.lean:2245`) / `CluScan` (`:2230`) with the prefix-emitted clause |
| **P-child, filter** (child list) | after `descendCom`'s last `subCom` (child mask now written): walk the raw block list, keep `alv_{j+1}[v] ≠ 0`, compact in place, count into `mnumName (j+1)` — `MemThreadProbe.memFilterCom` | `21·bs + 8`, **carrier-blind** (equal at 100/200; empty block = 8); stable, so sortedness inherits — output `[7,91]` compiled | same `Kd`; the pass is `O(bs)` because child ⊆ block (`Alv' ≠ 0 → InCluster`, `DescendStep`'s own clause) |
| **the dead route** (negative) | build the list from the mask alone (`memFromMaskCom`) | **`Ω(n)` compiled**: +`14`/carrier vertex between 100 and 200 at a fixed 2-member arena — `OrderBlockProbe`'s prose reason, now a guard | none — this is why the list must be *threaded*, not recomputed per level |

**Relationship to the cover CSR.** The per-depth list is NOT the
cover's per-cluster member CSR (`xofName j`/`xmmName j`, CoverBlock
F-1): the CSR is the *turn-indexed* structure the cover phase owns and
`coverSave` copies at `memCopyK mm = 12·mm + 6`; the depth list is the
*arena-indexed* structure handed DOWN by the parent's descend. The
child list is the turn's block row filtered by the child mask — so its
`smono` is inherited from the row, and the row's from `emitLoop`
(`RamCover.lean:790-806`), which scans `z = 0..n` in index order.
`CoverOut` does not currently RECORD that order (`block` is a fibre,
`block_inj` repetition-freeness, no monotonicity), so the thread wave
adds a `block_mono` clause to `CoverOut`/`CoverInv` — a walk extension
of the landed emission invariant, not a program change. The compiled
negative `unsorted_emission_refuted` (a BFS-ordered two-member block
kills `MemList`) pins what is at stake — see flag F-1 in §7 for the
E3 interaction.

## §4 The consumer table, per engine family

The read convention, uniformly: count into `"mm"`, then the LIVE
PREFIX into `"mem"` by `copyUpto (memName j) "mem" (.var "mm")` — the
`CoverBlock.memCopy_spec` leaf shape at `memCopyK mm = 12·mm + 6` —
then the engine. **Not** `copyCom`: the fixed-`n` copy convention that
serves the masks (`copyCom (alvName j) "alv"`) is itself a carrier
walk, exactly the class G2 is killing; the probe's consumer composite
(`consumeCom`, §5 guards) compiles the live-prefix path carrier-blind
(clock 66 at both carriers, inside `memCopyK 2 + clearMemK 2 + 4`).

| engine family | landed capital reused | what the member list changes |
|---|---|---|
| order-phase fills/copies/inversion | `OrderSigProbeM` — the twelve member-driven passes, synthesized both modes, measured `phaseClockK m = 68·m + 12` carrier-blind; clock kit (`clk`/`probeSt`, `:311-410`) | the driver-side list is what `ms` abstracted; the phase reads it through `"mem"`/`"mm"`; E-order re-run discharges `hKo` at `orderCostA` (probe §6) |
| scatter/clear/mark (E4b block engines) | `ScatterBlock` `ArenaA` (`:87-93`), `clearMem`/`clearMemK`, active scan + `memPos` gap kit (`ScatterBlockProg`) | their `hml : MemList …` hypotheses get their FIRST driver-side discharge (nothing constructs `MemList` in the package today — grep verified); note the length seam, flag F-2 |
| BFS under order/cover | `BfsBlock`/`BfsBridge` block variants (design §2 E2/E3 of g2-cost-design) | ball-driven already; the member list feeds the *enclosing* loops, not the BFS itself |
| cover phase | `CoverBlock` (`coverLoopK`, `memCopyK`, `centreK`) | the centre loop walks the compacted list (`cpsName` — already landed); `coverSave`'s member copy is already mass-driven; E3's block-driven emit is where flag F-1 lands |
| dead sweep / base tables | `DeadSweep.sweepImplements`, `RamDriverBot.baseImplements` | loop headers walk `memName j` instead of the carrier (g2-cost-design §2.3/2.4, R1.8-style header change); dead rows are the sweep's business exactly as today — the member list lists the ALIVE set |
| eliminations | `ElimSynth7` (assembled leaf) | pin carried, not moved — §5 |

## §5 The `ElimSynth7` `arrOf` pin, and the E29 allocation story

**The pin stays.** `ElimSynth7`'s engine entry pins its context at
`arrOf (n+1) O` / `arrOf ns T` / `arrOf n M` for `"off"`/`"tgt"`/
`"alv"` (`:350-352` etc.) — a carrier-shaped, carrier-charged engine
that is *sound* at that charge. The member wave does not touch it:
threading the list changes what the level state CARRIES, not what this
engine READS. The wave's obligations against the pin are exactly two,
both frame-side: the new names must stay out of the elim engine's
write set (they do — the engine writes its own scratch; one
`memName j ∉ warrs` discharge like every other pass), and the
level-entry copies that establish the pin (`copyCom (alvName j)
"alv"`, …) are unchanged. The pin's *replacement* — a member-driven
elim variant reading the arena through the list — is E2's business
(g2-cost-design §3(c)), after this thread lands; `ElimSynth7` remains
the engine of record until then, and the carried item transfers to E2
unchanged.

**E29: why fixed-`n` + count inherits the allocation story.** The
member array joins `DepthMem`'s `Sized` list (§2.2), i.e. it is
allocated exactly as `alvName j`/`cpsName j` are: once, by the
`ComputesInTime` prologue, at a size known before the run
(`n` per depth), bump-pointer style — P4.5's O(1) allocation with the
LIFO unwind (`SpaceBudget.nested_fits_iff`, consumed at the driver
shape by `G2ExistsRevalidation.mclass_driver_fits`). One extra
`n`-cell array per level changes the per-level arena weight `aw` by a
constant factor, so the E41 law `setup + levels·aw` is unmoved. A
per-level VARYING length (`mm_j` cells) would instead be a fresh
allocation per turn — the exact "per-turn fresh allocation is
budget-fatal" pattern E25–E29 killed — and the live-prefix discipline
(count scalar, junk tail, **no tail-zero clause**) is what makes the
fixed-size array behave touched-only: producers write `bs` cells,
consumers read `mm` cells, nobody clears `n` cells. The compiled
`memClause_zero_carrier` and the cost guards of probe §4/§5 are the
two directions of that choice.

## §6 The wave decomposition for the thread

One coherent spine, satellites per obligation file — the
single-owner/satellite discipline, sized to the compiled radii
(113 `LevelPre` / 17 files; ~167 name sites / ~16 files).

- **T1 — names + clause + frame (the spine owner).**
  `RamDriver.lean`: `memName`/`mnumName` defs next to `cpsName`,
  clause 16 into `LevelPre`, `(memName j, n)` into `DepthMem` (+ its
  three transport lemmas' lists), the `descendCom` text delta
  (emission + filter, §3). `RamDriverCompose.lean`: `levelPre_run`
  +2 side conditions; the per-phase `notMem` lemmas; the stale
  "thirteen clauses" docstring fixed to sixteen. Gate: the probe's
  `LevelPreM` becomes derivable from the real `LevelPre` by `And.intro`
  reshuffling (state it as a satellite `example`), and `lax build`
  from the repo root replays green.
- **T2 — the producer walks.** `RamDriverDescend.lean`:
  `clusterLoad_spec`/`CluScan` extended with the emitted-prefix
  clause; the filter pass's spec (`Spec` at `21·bs + 8`-class cost,
  the probe's compiled constants as the honesty control);
  `DescendStep` post + `BatchData` delta (§2.4); `Kd` re-derived.
  `RamCover.lean`: `CoverOut.block_mono` walk extension (§3).
  Root side: the identity-list emission after decode/dedup, charged
  `Kdec`-side.
- **T3 — the destructuring repair sweep (satellites, mechanical).**
  The compiled list of positional `⟨h1,…⟩` sites:
  `RamDriverCompose.lean:305` (`levelPre_run` itself, done in T1),
  `RamDriverIO.lean:817` (`rootMem_of_levelPre` — last pattern `-`,
  absorbs silently: must be *checked*, not edited blindly),
  `RamDriverCluster.lean:922-923` and `RamDriverFrames.lean:1036-1037`
  (the `hlevin` sites — need T2's `BatchData` component, the one place
  content is NEW), plus every `obtain ⟨…⟩ := hlev`-shaped site the
  build breaks in the 17-file radius. Rule for the sweep: a site that
  rebuilds `LevelPre` at depth `j+1` may NOT pass the depth-`j` member
  conjunct through — the clause is depth-indexed through `memName j`,
  exactly like clauses 4/5.
- **T4 — frame discharges.** The ~16-file `warrs`/`wvars` sweep:
  `memName`/`mnumName` disequalities per phase, `RamDriverWrites`/
  `RamDriverDedup` included. All `simp [_, String.ext_iff]`-class.
- **T5 — consumer re-wire gate (NOT this thread).** The engine-side
  re-statements (flag F-2's length seam, the R1.8 headers, E-order's
  `hKo` discharge) consume the threaded clause; they are the
  order/cover re-synthesis waves' openings and stay out of the thread
  wave — the thread is done when the state carries the list and the
  producers fill it, with every landed walk replayed.

T1 → T2 → (T3 ∥ T4); T3/T4 satellites are single-file-owned and
mergeable in any order once T2's exports exist.

## §7 Unresolved design questions (flagged)

Supervisor dispositions, 2026-08-06 (thread wave dispatched on these):
F-1 defer to E3's brief, thread rides the landed `emitLoop` order with
`CoverOut.block_mono`; F-2 defer to T5's engine waves, thread must not
touch `ScatterBlock` arena `Prop`s; F-3 accept P-root after
decode+dedup, re-confirm at the B7 re-run if dedup ever kills carrier
vertices; F-4 T2 owner's call, preference `BatchData` extension,
parallel conjunct pre-authorized if the `setArr` transports fight it.

- **F-1, sortedness under E3.** The mainline supply chain (§3) rides
  the landed `emitLoop`'s index-order scan, recorded as
  `CoverOut.block_mono`. E3's block-driven cover (g2-cost-design §6
  E3) replaces the emission with a touched-set emit whose order is
  discovery order — `unsorted_emission_refuted` compiles that this
  breaks `MemList` as stated. When E3 lands it must either emit in
  index order at the block (unknown whether its `2·touches` budget
  survives that) or the member contract weakens to a nodup form
  (`lt`/`inj`/`sound`/`complete`), which loses the `memPos` gap kit's
  sorted reading. Decision belongs to E3's brief; the thread wave is
  correct under the landed cover either way.
- **F-2, the `ArenaA` length seam.** `ScatterBlock.ArenaA` pins
  `σ.arrs "mem" = arrOf mm Mem` — physical length `mm` — while the
  threaded convention pre-allocates `"mem"` at `n` and fills a live
  prefix. The engines' arena `Prop`s need the live-prefix re-statement
  (`arrOf n Mem` + `MemList` reading only `k < mm` — the same `Mem`
  function works, so this is a length-clause edit, not a semantic
  one). Owned by T5's engine waves, not the thread; the probe's
  `consumeCom` guards show the fixed-`n` layout already runs the
  landed `clearMem` correctly.
- **F-3, root-list placement.** P-root emits after decode+dedup; if
  G1's dedup story ever kills carrier vertices (it currently dedups
  edges), the root list becomes the mask enumeration — still `O(n)`,
  still root-only. Confirm at the B7 re-run.
- **F-4, `BatchData` vs bare `∃`.** §2.4 recommends extending
  `BatchData`; if its `setArr`-transport lemmas make the extension
  awkward (the member clause is content, not length), a parallel
  conjunct in `DescendStep`'s post is equivalent. T2 owner's call;
  either way the `hlevin` sites read one more component.

## §8 What the probe compiles (the record)

`proofs/Lax3Proofs/Refine/MemThreadProbe.lean`, all green, zero
sorry, kernel-three (`#print axioms` §7 of the file; `memList_unique`
and `memPhase_escapes_floor` need less):

- **Existence**: `levelPreM_root` — a root-shaped `Env` (every array
  of `LevelMem`/`OrderMem`/`DepthMem` present at its declared length,
  all-alive mask, identity list) satisfies the full 15 landed clauses
  PLUS the member clause at depth 0; `levelPreM_child` — the SAME
  `Env` after a literal `setArr`/`setVar` descend-like update
  satisfies it at depth 1 with the filtered child list.
  `memClause_zero_carrier` — satisfiable at `n = 0` (the flip-gate
  control; no tail conjunct to refute). `memList_unique` — the
  `∃`-form is lossless.
- **Producer, both directions**: emission delta `8·bs + 2` and filter
  `21·bs + 8`, each pinned carrier-blind at carriers 100/200 and
  linear at `bs ∈ {0, 2, 3}`, with the emitted/filtered contents
  checked cell for cell (`[7,13,91]` → `[7,91]`, sorted, counted);
  negative controls `memFromMaskCom` (`+14·n`, the `Ω(n)` mask-only
  route — `OrderBlockProbe`'s prose claim made compiled) and
  `unsorted_emission_refuted` (BFS-order emission kills `smono`,
  generically in the mask).
- **Consumer**: `consumeCom` — count + live-prefix copy
  (`memCopy_spec` shape) + landed `clearMem` — clock 66 at BOTH
  carriers, inside `memCopyK 2 + clearMemK 2 + 4`, exactly the member
  cells moved.
- **Floor-death**: `memPhase_escapes_floor` — the measured
  member-driven phase clock fits `orderCostA (bsq 2 2 0) 0` read at
  arena weight 4, where `OrderBlockProbe`'s guard refutes the landed
  text's clock at the same reading; empty-arena charge 12 fits the
  weight-0 budget; the `10¹¹` guard defuses the
  `nested_emptyCharge_floor` route at the measured constant; and
  `memPhase_interface_closes` instantiates
  `G2ExistsRevalidation.g2m_exists` at `68/12`, `ℓ = 3`, `D = 8`,
  `ct = 200`, `ksc = 10⁴` — the Σ interface closes at exactly the
  constants the threaded engines were measured at.

Ledger: two additive files (this doc + the probe) plus one root-import
line; no landed statement touched; the proposed clause exists nowhere
outside the probe's namespace.
