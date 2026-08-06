import Lax3Proofs.Refine.OrderSynth
import Lax13Proofs.Refine.Sepref.Register

/-!
# P4.6 / wave M — a member-driven order-phase text, synthesized, with
compiled carrier-blindness

The phase's landing criterion, tested. `OrderBlockProbe` §1/§2 prove
the landed carrier-walking order text can never synthesize to a
carrier-blind cost — the member-list interior is the only route. This
file walks that route at probe scale: an order-phase-shaped abstract
program whose twelve passes are all driven by an explicit member array
`ms`, synthesized whole through the tower (direct written-goal mode
AND `hfref` signature mode), with the carrier-blindness of the
*synthesized machine program* compiled — clock equal at two members
inside a 100- and a 200-cell carrier, `O(1)` at zero members, and a
carrier-walking negative control at the same slot that grows.

## 0. TELEMETRY

Warm `main` checkout, module target at 3 070 jobs, staged builds of
this file (each row's figure is its stage's module wall clock minus the
previous stage's); single runs, ±10 %.

| stage | ops | module wall clock | delta |
|---|---|---|---|
| twins + 3 parametric leaf syntheses | 10 / 8 / 10 | 13 s | 13 s |
| + `orderPhaseMSynth` (direct, 12 passes) | 123 | 213 s | ≈ 200 s |
| + carrier-blindness artifacts (§4) | — | 228 s | ≈ 15 s |
| + `orderPhaseMFromSignature` (`hfref`) | — | 457 s | ≈ 229 s |

**Heartbeats**: the three leaves at `1000000`; direct mode passes at
`8000000` (wave S's `pre18` figure); signature mode was granted
`16000000` and passed (whether S's `8000000` suffices was not probed).

**Against wave S.** S's `pre18Synth` — the same tool, the same
15-array-scale context, carrier-walking passes — is 141 ops at 132 s
direct and ≈ 181 s from a signature. This file's 123 ops cost ≈ 200 s
direct and ≈ 229 s from a signature: about 1.7× S's curve read at the
same op count. The member-driven leaves are wider than S's — every
rule carries the member array as an extra framed conjunct, one to two
junk cells, and (for the copy and the inversion) two framed source
arrays — so every one of the twelve rule applications pays a larger
frame-match. Same tool, same exponent family, a bigger constant; no
new wall.

**The signature verdict wave M routes on**: member-driven whole-phase
synthesis lands, in both modes, with no new obstruction — the
frameMatch merge wall (S §4, E43 obstruction 1) is avoided by the
probe's own discipline (every destination is a pre-owned context
product, no pass writes into an array-value an earlier pass produced),
and the engine (E43 obstruction 2) is out of scope below.

## 1. WHAT THIS FILE DOES *NOT* CLAIM

This is a **standalone probe**. `orderPhaseM` is a new definition of
this namespace: `orderPhase0`'s pass *shapes* at `orderPhase0`'s array
names, but driven by a member list that the landed driver state does
not carry (R1.6 member lists are unbuilt). **No theorem here claims
`orderPhaseM` equals `orderPhase0`, refines `RamDriver.orderCom`, or
discharges any `OrderImplements` obligation.** Threading member lists
into `LevelPre` and the driver state is the later E-mem wave. Nothing
in `LevelPre`, `RamDriver*`, `OrderSynth`, `OrderBridge` is touched,
and no attribute is added to any landed declaration.

**What is parameterized OUT, and why that is honest.** The real
phase's genuinely setup-scale work — the full-width `saveCsr` block
copies, the two elimination-engine calls, and the carrier-width
scratch zeroing — is not smuggled in as member-driven passes and not
silently included: the engine outputs enter as ordinary array
arguments (`e2rnk`; 2E/D-a — the phase does not own the engine, and
the engine has no single `Com`, E43 obstruction 2), and no pass of
this file reads or writes carrier-many cells. The touched-only law —
write only cells named by `ms` (for the inversion: their rank-side
images), restore only cells named by `ms` — is checked on data in §1's
twins and on the synthesized machine in §4.

**Import note.** This file deliberately imports `OrderSynth` directly
rather than the S module (`OrderSigProbe`), whose working-tree copy was
under a concurrent worker's WIP when this wave ran; `comSize` is
restated verbatim below. The negative control uses
`OrderSynth.fillSynth_impl`, which S's `mopFill_landed` proves is
exactly wave S's parametric `mopFill` read at the landed cell names —
so the control is S's carrier-walking fill, at the same slot.

## 2. THE COMPILED CARRIER-BLINDNESS (§4)

The instrument is the tower's own executable semantics
`Ir.evalFuel` — state and *exact cost vector*, currency by currency
(the Ir-layer sibling of `TgtWidenProbe.execC`, which lives at the
Imp layer and cannot run an Ir `Com`). `clk` sums the sixteen
currencies. All compiled, none prose:

* **the clock law** — `phaseClockK m = 68·m + 12`, `n` absent: pinned
  by `#guard` at `m ∈ {0, 2, 3}`, each at BOTH `n = 100` and
  `n = 200` (`probeClock_carrier_blind`, kernel-checked by `decide`);
* **the empty-member charge is O(1)** — `probeClock n [] = 12` at both
  carrier widths: the twelve failing guard tests and nothing else
  (`probeClock_empty_const`);
* **the negative control bites** — the landed carrier-walking fill at
  the same slot clocks `4·n + 1`: `401` at `n = 100`, `801` at
  `n = 200`, strictly growing on the same instrument
  (`fillClock_carrier_bound`);
* **the touched-only law on the machine** — sentinel arrays come out
  with exactly the member-indexed cells moved, and the two restores
  are cell-for-cell identities on `off`/`tgt`.

## 3. HOUSE TRAP OBSERVED (S §3, reproduced at this scale)

The fills' value cell is the matcher's choice, consumed in written
order: the synthesized fills read their `0` from the NEXT fill's index
cell — `aset "e1elm" "u1" "i11"`, `aset "e1bh" "u1" "i13"`,
`aset "e2elm" "u1" "i15"` — and only the last fill uses `"zero"`.
Sound (each such cell still holds `0` when read, since its own pass
has not yet run), deterministic, and now also *executed*: the §4
probes run those very programs and the touched-only guards pass.
-/

namespace Lax3Proofs.Refine.OrderSigProbeM

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax3Proofs.Refine.OrderSynth

/-- The number of `Com` nodes in a program (wave S's measure, restated
here so this file does not import the S module while it is under a
concurrent worker's WIP). -/
def comSize : Com → ℕ
  | .skip => 1
  | .const _ _ => 1
  | .copy _ _ => 1
  | .binop _ _ _ _ => 1
  | .aget _ _ _ => 1
  | .aset _ _ _ => 1
  | .seq c d => 1 + comSize c + comSize d
  | .ite _ c d => 1 + comSize c + comSize d
  | .while _ c => 1 + comSize c

/-! ## 1. The three member-driven passes

Same state shape as the phase's carrier passes (`OrderSynth.FS`: the
array being written and the counter), but the counter now walks the
member list `ms`, never the carrier: every read of the written array's
index space goes through `ms[k]`. -/

/-- The guard: the counter against the member count. The carrier length
is not an argument anywhere in this file's programs. -/
def memBf (mm : ℕ) : FS → Bool := fun s => decide (s.2 < mm)

/-- One member of a member-driven copy: `u := ms[k]; w := src[u];
A[u] := w; k := k + 1`. -/
noncomputable def mcopyF (ms src : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget ms s.2) fun u =>
    bindT (mopAget src u) fun w =>
      bindT (mopAset s.1 u w) fun A =>
        bindT (mopSucc s.2) fun i => mopPair A i

/-- **The member-driven copy.** -/
noncomputable def mcopyPass (mm : ℕ) (ms src : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun _ => True) (memBf mm) (mcopyF ms src) s₀

/-- One member of a member-driven (touched-only) fill: `u := ms[k];
A[u] := v; k := k + 1`. -/
noncomputable def mfillF (ms : List ℕ) (v : ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget ms s.2) fun u =>
    bindT (mopAset s.1 u v) fun A =>
      bindT (mopSucc s.2) fun i => mopPair A i

/-- **The member-driven fill.** -/
noncomputable def mfillPass (mm : ℕ) (ms : List ℕ) (v : ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun _ => True) (memBf mm) (mfillF ms v) s₀

/-- One member of the member-driven rank inversion: `u := ms[k];
r := rnk[u]; A[r] := u; k := k + 1`. -/
noncomputable def mordF (ms rnk : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget ms s.2) fun u =>
    bindT (mopAget rnk u) fun r =>
      bindT (mopAset s.1 r u) fun A =>
        bindT (mopSucc s.2) fun i => mopPair A i

/-- **The member-driven rank inversion.** -/
noncomputable def mordPass (mm : ℕ) (ms rnk : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun _ => True) (memBf mm) (mordF ms rnk) s₀

/-! ### Refute before prove: the twins, and the touched-only law -/

/-- One member of the copy, as a pure step. -/
def mcopyTw (ms src : List ℕ) : FS → FS := fun s =>
  (s.1.set ms[s.2]! src[ms[s.2]!]!, s.2 + 1)

/-- One member of the fill. -/
def mfillTw (ms : List ℕ) (v : ℕ) : FS → FS := fun s =>
  (s.1.set ms[s.2]! v, s.2 + 1)

/-- One member of the inversion. -/
def mordTw (ms rnk : List ℕ) : FS → FS := fun s =>
  (s.1.set rnk[ms[s.2]!]! ms[s.2]!, s.2 + 1)

-- **The touched-only law, on data**: two members inside a five-cell
-- array — exactly the listed cells move, every other cell is the
-- caller's.
#guard (runTw (mcopyTw [1, 3] [10, 11, 12, 13, 14]) 2 3 ([9, 9, 9, 9, 9], 0)).1
  = [9, 11, 9, 13, 9]
#guard (runTw (mfillTw [1, 3] 0) 2 3 ([9, 9, 9, 9, 9], 0)).1 = [9, 0, 9, 0, 9]
-- the inversion writes at `rnk[u]`, the rank-side image of the member
-- list: member `1` lands at `rnk[1] = 4`, member `3` at `rnk[3] = 0`
#guard (runTw (mordTw [1, 3] [2, 4, 3, 0, 1]) 2 3 ([9, 9, 9, 9, 9], 0)).1
  = [3, 9, 9, 9, 1]
-- the member count, not the carrier, bounds the walk: at `mm = 0`
-- nothing moves
#guard (runTw (mfillTw [1, 3] 0) 0 3 ([9, 9, 9, 9, 9], 0)).1 = [9, 9, 9, 9, 9]

/-! ## 2. The passes as leaf operations, at symbolic cell names -/

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth mopCopyM (d i s t cnt one u w : String) (mm : ℕ) (ms src A₀ : List ℕ)
    (k₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, k₀) (d, i) ∗
      hnCtxt arrayAssn ms s ∗ hnCtxt arrayAssn src t ∗
      hnCtxt natAssn mm cnt ∗ hnCtxt natAssn 1 one ∗
      junkCell u ∗ junkCell w)
    _ _ (d, i) (arrayAssn ×ₐ natAssn)
    (mcopyPass mm ms src (A₀, k₀))

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth mopFillM (a i s v cnt one u : String) (mm vv : ℕ) (ms A₀ : List ℕ)
    (k₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, k₀) (a, i) ∗
      hnCtxt arrayAssn ms s ∗ hnCtxt natAssn vv v ∗
      hnCtxt natAssn mm cnt ∗ hnCtxt natAssn 1 one ∗
      junkCell u)
    _ _ (a, i) (arrayAssn ×ₐ natAssn)
    (mfillPass mm ms vv (A₀, k₀))

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth mopOrdM (a i s r cnt one u w : String) (mm : ℕ) (ms rnk A₀ : List ℕ)
    (k₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, k₀) (a, i) ∗
      hnCtxt arrayAssn ms s ∗ hnCtxt arrayAssn rnk r ∗
      hnCtxt natAssn mm cnt ∗ hnCtxt natAssn 1 one ∗
      junkCell u ∗ junkCell w)
    _ _ (a, i) (arrayAssn ×ₐ natAssn)
    (mordPass mm ms rnk (A₀, k₀))

attribute [sepref_fr_rules] mopCopyM mopFillM mopOrdM

/-! ## 3. The member-driven phase -/

/-- **The member-driven order-phase text.** Twelve passes in the R = 0
phase's own order and at its own array names: five saves, two restores
(reading the saved copies back), the two first-elimination scratch
resets, the rank inversion, and the two second-elimination scratch
resets. Every pass is driven by `ms`; the setup-scale work of the real
phase (full-width `saveCsr`, the engines, carrier-width zeroing) is
parameterized OUT — the engine outputs enter as ordinary array
arguments (`e2rnk`), not as passes. -/
noncomputable def orderPhaseM (mm : ℕ)
    (ms off tgt alvj alv d1off doff d1tg dtg e2rnk : List ℕ)
    (gof gtg e1elm e1bh e2elm e2bh ord : List ℕ) : NRest FS ECost :=
  bindT (mcopyPass mm ms off (gof, 0)) fun sv1 =>
  bindT (mcopyPass mm ms tgt (gtg, 0)) fun sv2 =>
  bindT (mcopyPass mm ms alvj (alv, 0)) fun _ =>
  bindT (mcopyPass mm ms d1off (doff, 0)) fun _ =>
  bindT (mcopyPass mm ms d1tg (dtg, 0)) fun _ =>
  bindT (mcopyPass mm ms sv1.1 (off, 0)) fun _ =>
  bindT (mcopyPass mm ms sv2.1 (tgt, 0)) fun _ =>
  bindT (mfillPass mm ms 0 (e1elm, 0)) fun _ =>
  bindT (mfillPass mm ms 0 (e1bh, 0)) fun _ =>
  bindT (mordPass mm ms e2rnk (ord, 0)) fun _ =>
  bindT (mfillPass mm ms 0 (e2elm, 0)) fun _ =>
  mfillPass mm ms 0 (e2bh, 0)

set_option maxHeartbeats 8000000 in
set_option linter.unusedVariables false in
sepref_synth orderPhaseMSynth (mm : ℕ)
    (ms off tgt alvj alv d1off doff d1tg dtg e2rnk : List ℕ)
    (gof gtg e1elm e1bh e2elm e2bh ord : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (gof, 0) ("gof", "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (off, 0) ("off", "i7") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (gtg, 0) ("gtg", "i2") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (tgt, 0) ("tgt", "i8") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (alv, 0) ("alv", "i3") ∗
      hnCtxt arrayAssn alvj "alvj" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (doff, 0) ("doff", "i5") ∗
      hnCtxt arrayAssn d1off "d1off" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (dtg, 0) ("dtg", "i6") ∗
      hnCtxt arrayAssn d1tg "d1tg" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e1elm, 0) ("e1elm", "i10") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e1bh, 0) ("e1bh", "i11") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (ord, 0) ("ord", "i13") ∗
      hnCtxt arrayAssn e2rnk "e2rnk" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e2elm, 0) ("e2elm", "i14") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e2bh, 0) ("e2bh", "i15") ∗
      hnCtxt arrayAssn ms "ms" ∗
      hnCtxt natAssn mm "mc" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "u1" ∗ junkCell "u2")
    _ _ ("e2bh", "i15") (arrayAssn ×ₐ natAssn)
    (orderPhaseM mm ms off tgt alvj alv d1off doff d1tg dtg e2rnk
      gof gtg e1elm e1bh e2elm e2bh ord)

#guard comSize orderPhaseMSynth_impl = 123

/-! ## 4. Compiled carrier-blindness (instrument: `Ir.evalFuel`) -/

/-- The total clock of a cost vector: the sum over the IR's sixteen
currencies. -/
def clk (κ : Ir.Cost) : ℕ := (Currency.all.map κ.toFun).sum

/-- The probe memory: the member list, six read-side arrays with
recognizable contents, and eleven write-side arrays full of the
sentinel `9` — all carrier arrays at length `n`. -/
def probeSt (n : ℕ) (ms : List ℕ) : Ir.State :=
  Ir.State.ofPairs
    [("i1", 0), ("i2", 0), ("i3", 0), ("i5", 0), ("i6", 0), ("i7", 0), ("i8", 0),
     ("i10", 0), ("i11", 0), ("i13", 0), ("i14", 0), ("i15", 0),
     ("mc", ms.length), ("one", 1), ("zero", 0), ("u1", 0), ("u2", 0)]
    [("ms", ms),
     ("off", List.range n), ("tgt", List.replicate n 2),
     ("alvj", List.replicate n 1),
     ("d1off", List.range n), ("d1tg", List.replicate n 3),
     ("e2rnk", ((List.replicate n 0).set 7 5).set 91 9),
     ("gof", List.replicate n 9), ("gtg", List.replicate n 9),
     ("alv", List.replicate n 9),
     ("doff", List.replicate n 9), ("dtg", List.replicate n 9),
     ("e1elm", List.replicate n 9), ("e1bh", List.replicate n 9),
     ("e2elm", List.replicate n 9), ("e2bh", List.replicate n 9),
     ("ord", List.replicate n 9)]

/-- The synthesized phase, run. -/
def probeOut (n : ℕ) (ms : List ℕ) : Option (Ir.State × Ir.Cost) :=
  Ir.evalFuel 20000 orderPhaseMSynth_impl (probeSt n ms)

/-- Its clock. -/
def probeClock (n : ℕ) (ms : List ℕ) : Option ℕ := (probeOut n ms).map fun p => clk p.2

/-- The two-member arena of the P2 gate. -/
def mem2 : List ℕ := [7, 91]

/-- The phase's clock law: `68·m + 12` — six units per member for each
of the eight aget-carrying passes (seven copies, one inversion), five
per member for each of the four fills, and the twelve final guard
tests. The carrier length `n` does not appear. -/
def phaseClockK (m : ℕ) : ℕ := 68 * m + 12

-- the law, pinned at three member counts and both carrier widths
#guard probeClock 100 mem2 = some (phaseClockK 2)
#guard probeClock 200 mem2 = some (phaseClockK 2)
#guard probeClock 100 [] = some (phaseClockK 0)
#guard probeClock 200 [] = some (phaseClockK 0)
#guard probeClock 100 [7, 8, 91] = some (phaseClockK 3)
#guard probeClock 200 [7, 8, 91] = some (phaseClockK 3)

set_option maxRecDepth 40000 in
/-- **Carrier-blindness, compiled**: the synthesized phase's clock at
two members inside a 100-cell carrier EQUALS its clock at two members
inside a 200-cell carrier — and is the closed form's `68·2 + 12`. -/
theorem probeClock_carrier_blind :
    probeClock 100 mem2 = probeClock 200 mem2 ∧
      probeClock 100 mem2 = some (phaseClockK 2) := by decide

set_option maxRecDepth 40000 in
/-- **The empty-member charge is O(1), compiled**: at `m = 0` the clock
is the constant `12` — the twelve failing guard tests — at both carrier
widths. -/
theorem probeClock_empty_const :
    probeClock 100 [] = some (phaseClockK 0) ∧
      probeClock 200 [] = some (phaseClockK 0) ∧ phaseClockK 0 = 12 := by decide

/-! ### The touched-only law, on the synthesized machine

Two members inside a 100-cell carrier: the phase moves exactly the
member-indexed cells (and, for the inversion, their rank-side images)
and every sentinel cell outside them survives. The restores really
restore: `off` and `tgt` come out cell-for-cell as they went in. -/

#guard (probeOut 100 mem2).map (fun p => p.1.arrs "gof") =
  some (some (((List.replicate 100 9).set 7 7).set 91 91))
#guard (probeOut 100 mem2).map (fun p => p.1.arrs "gtg") =
  some (some (((List.replicate 100 9).set 7 2).set 91 2))
#guard (probeOut 100 mem2).map (fun p => p.1.arrs "off") = some (some (List.range 100))
#guard (probeOut 100 mem2).map (fun p => p.1.arrs "tgt") =
  some (some (List.replicate 100 2))
#guard (probeOut 100 mem2).map (fun p => p.1.arrs "ord") =
  some (some (((List.replicate 100 9).set 5 7).set 9 91))
#guard (probeOut 100 mem2).map (fun p => p.1.arrs "e1elm") =
  some (some (((List.replicate 100 9).set 7 0).set 91 0))
-- at `m = 0` nothing moves at all
#guard (probeOut 100 []).map (fun p => p.1.arrs "gof") =
  some (some (List.replicate 100 9))

/-- The negative control's memory: the landed carrier-walking fill
(`OrderSynth.fillSynth_impl`) at bound `n`, at the same slot. -/
def fillSt (n : ℕ) : Ir.State :=
  Ir.State.ofPairs [("fli", 0), ("fln", n), ("flv", 0), ("one", 1)]
    [("fla", List.replicate n 9)]

/-- The carrier-walking fill's clock. -/
def fillClock (n : ℕ) : Option ℕ :=
  (Ir.evalFuel 20000 fillSynth_impl (fillSt n)).map fun p => clk p.2

set_option maxRecDepth 40000 in
/-- **The negative control BITES, compiled**: the landed carrier-walking
fill at the same slot clocks `4·n + 1` — it GROWS between the 100- and
the 200-cell carrier, on the same instrument that just measured the
member-driven phase flat. -/
theorem fillClock_carrier_bound :
    fillClock 100 = some 401 ∧ fillClock 200 = some 801 ∧ (401 : ℕ) < 801 := by decide

-- the differential, side by side: flat where member-driven, growing
-- where carrier-walking
#guard probeClock 100 mem2 = probeClock 200 mem2
#guard fillClock 100 ≠ fillClock 200

/-! ## 5. Signature mode

The same phase from an `hfref` signature: one abstract-argument record,
the ownership boundary as data, no hand-written `hnRefine` goal
(`BfsQSignature`'s idiom at this file's own scale). The `#guard` pins
the synthesized implementation record against the direct-mode
synthesis. -/

structure OrderPhaseMArgs where
  mm : ℕ
  ms : List ℕ
  off : List ℕ
  tgt : List ℕ
  alvj : List ℕ
  alv : List ℕ
  d1off : List ℕ
  doff : List ℕ
  d1tg : List ℕ
  dtg : List ℕ
  e2rnk : List ℕ
  gof : List ℕ
  gtg : List ℕ
  e1elm : List ℕ
  e1bh : List ℕ
  e2elm : List ℕ
  e2bh : List ℕ
  ord : List ℕ

/-- Reducible, so signature preparation exposes precisely the ownership
boundary `orderPhaseMSynth`'s written goal has; the post side is the
frame the direct synthesis computed. -/
abbrev orderPhaseMRS :
    (OrderPhaseMArgs → Unit → Assn) × (OrderPhaseMArgs → Unit → Assn) :=
  ((fun x _ =>
      hnCtxt (arrayAssn ×ₐ natAssn) (x.gof, 0) ("gof", "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.off, 0) ("off", "i7") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.gtg, 0) ("gtg", "i2") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.tgt, 0) ("tgt", "i8") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.alv, 0) ("alv", "i3") ∗
      hnCtxt arrayAssn x.alvj "alvj" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.doff, 0) ("doff", "i5") ∗
      hnCtxt arrayAssn x.d1off "d1off" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.dtg, 0) ("dtg", "i6") ∗
      hnCtxt arrayAssn x.d1tg "d1tg" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.e1elm, 0) ("e1elm", "i10") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.e1bh, 0) ("e1bh", "i11") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.ord, 0) ("ord", "i13") ∗
      hnCtxt arrayAssn x.e2rnk "e2rnk" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.e2elm, 0) ("e2elm", "i14") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.e2bh, 0) ("e2bh", "i15") ∗
      hnCtxt arrayAssn x.ms "ms" ∗
      hnCtxt natAssn x.mm "mc" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "u1" ∗ junkCell "u2"),
    (fun x _ =>
      junkArray "e2elm" ∗ junkCell "i14" ∗ junkArray "ord" ∗ junkCell "i13" ∗
      junkArray "e1bh" ∗ junkCell "i11" ∗ junkArray "e1elm" ∗ junkCell "i10" ∗
      junkArray "tgt" ∗ junkCell "i8" ∗ junkArray "off" ∗ junkCell "i7" ∗
      junkArray "dtg" ∗ junkCell "i6" ∗ junkArray "doff" ∗ junkCell "i5" ∗
      junkArray "alv" ∗ junkCell "i3" ∗ junkArray "gtg" ∗ junkCell "i2" ∗
      (junkArray "gof" ∗ junkCell "i1") ∗
      hnCtxt arrayAssn x.alvj "alvj" ∗ hnCtxt arrayAssn x.d1off "d1off" ∗
      hnCtxt arrayAssn x.d1tg "d1tg" ∗ hnCtxt arrayAssn x.e2rnk "e2rnk" ∗
      hnCtxt arrayAssn x.ms "ms" ∗
      hnCtxt natAssn x.mm "mc" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "u1" ∗ junkCell "u2"))

set_option maxHeartbeats 16000000 in
set_option linter.unusedVariables false in
sepref_synth orderPhaseMFromSignature :
    ((fun _ : Unit => (_, _)),
      fun x : OrderPhaseMArgs =>
        orderPhaseM x.mm x.ms x.off x.tgt x.alvj x.alv x.d1off x.doff x.d1tg x.dtg
          x.e2rnk x.gof x.gtg x.e1elm x.e1bh x.e2elm x.e2bh x.ord) ∈
      hfref (fun _ : OrderPhaseMArgs => True) orderPhaseMRS
        (fun _ _ => arrayAssn ×ₐ natAssn)

#guard orderPhaseMFromSignature_impl () = (("e2bh", "i15"), orderPhaseMSynth_impl)

/-! ## 6. Axioms

Every principal declaration, at the kernel three. -/

#print axioms mopCopyM
#print axioms mopFillM
#print axioms mopOrdM
#print axioms orderPhaseMSynth
#print axioms orderPhaseMFromSignature
#print axioms probeClock_carrier_blind
#print axioms probeClock_empty_const
#print axioms fillClock_carrier_bound

end Lax3Proofs.Refine.OrderSigProbeM
