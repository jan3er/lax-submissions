import Lax3Proofs.Refine.OrderBlockProbe

/-!
# ND-MC G2/E-order re-run — the twelve member shapes at the real slots,
refuted at the engine seam

The re-run was tasked with rebuilding `RamDriver.orderCom`'s interior
member-driven (the twelve `Refine.OrderSigProbeM` shapes, read off the
E-mem member list `LevelPre` now carries), re-discharging
`OrderImplements`/`OrderImplementsR` at the arena-charged
`G2CostProbe.orderCostA`, restating the root's `hKo` at the g2 §2.1
form, and re-closing `g2_plug`'s order gap. **This file is the re-run's
honest compiled verdict: none of the four is reachable from the landed
package, because every one of the twelve member-driven shapes, moved
from the probe to its real slot in the phase, is refuted by a coupling
to the landed carrier engines — and the first elimination's own share
of the phase clock already exceeds the whole §2.1 budget at a light
arena.** `OrderSigProbeM` §1 records what the probe deliberately did
not claim (the engines were parameterized out, the touched-only law
assumed of them); this file closes that recorded gap in the *negative*
direction, shape by shape, against the engines of record.

`OrderBlockProbe` — the first E-order verdict — gated the re-run on
three successor surfaces, **in order**: (1) member-list threading;
(2) member-driven engines, *one wave per family*; (3) the phase text +
walk. Since then (1) landed (E-mem: `LevelPre` clause 16, the descend
producers, `MemThreadGate`, `ArenaSeam`) — but (2) did not: no
member-driven elimination, augmentation or symmetrization `Com` exists
in the package (the only `MemList` consumers are E4b's
scatter/clear/mark block engines and the cover copies; `ElimSynth7`'s
own header records "costs stay carrier-class this wave; the
member-driven interior is the next wave"). The re-run was dispatched at
(3) with (2) missing. The findings below compile that (3) cannot
execute first — **the twelve interior shapes and the engines are one
coupled seam, not two separable halves** — so the wave order of
`OrderBlockProbe`'s brief is forced, not preferential.

## The coupling table: each probe shape at its real slot

`OrderSigProbeM.orderPhaseM`'s twelve passes, and what refutes each of
them the moment it replaces its landed counterpart while
`RamElim.elimCom` / `RamAugment.augCom` / `RamDriver.symCom` stand:

| probe shape | real slot | refuting coupling | compiled at |
|---|---|---|---|
| `mcopyPass … off/tgt` (saves 1–2) | `saveCsr` | restore-seam: `symCom` writes `off[0..n]`/`tgt` carrier-wide, so the saved prefix must be the carrier's or the restore restores junk | §3 |
| `mcopyPass … alvj` (save 3) | `copyCom (alvName j) "alv"` | read-seam: the engine's degree pass reads `alv` at EVERY carrier vertex; a member copy leaves stale non-member cells and `RamElim.ElimPre`'s mask clause is false on data | §4 |
| `mcopyPass … d1off/d1tg` (saves 4–5) | `copyUpto "ioff"/"itg" → "doff"/"dtg"` | read-seam: `symCom`'s offset fill and `forVerts` read `doff` at every carrier vertex (same class as §4) | §4 (class) |
| `mcopyPass` restores (6–7) | `restoreCsr` | restore-seam: after `symCom` the non-member cells of `off` hold the arena structure's offsets, not the level's — the member restore leaves them and `LevelPre`'s `off` clause is refuted on data | §3 |
| `mfillPass e1elm/e1bh` (8–9) | `elimRezeroCom` | zero-seam: the first elimination extracts EVERY carrier vertex (`elm ≡ 1` on the carrier, compiled §1), so a member re-zero leaves dead vertices flagged and the second `elimCom` has **no run** — the D4 stuck replay, now at the member text | §2 |
| `mordPass` (10) | `ordCom` | contract-seam: the postcondition is `RamCover.OrdersBy n π` — a carrier permutation's inverse, consumed carrier-wide by the cover — and the member inversion leaves junk at every dead position | §5 |
| `mfillPass e2elm/e2bh` (11–12) | `orderZeroCom`'s `elm`/`bh` fills | zero-seam: `OrderMem`'s zeroed-scratch clauses are carrier-wide (`∀ v ∈ arrs "elm", v = 0`) and a level must hand them back; the member re-zero leaves `elm ≡ 1` off the members, compiled §2 | §2 |

And §1 compiles the floor that survives even a FREE interior: the first
`elimCom` alone, at a fixed two-member arena, clocks `159·n + 276` — affine in the
carrier — and exceeds `orderCostA (bsq 2 2 0) 0 4` — the §2.1 budget at
the arena's weight — at carrier 800. So no interior rebuild flips
`OrderBlockProbe`'s refutation gate while the engines stand.

## What the re-run therefore did NOT touch

`orderCom`'s text, `orderImplements₀`/`orderImplementsR`, and the four
`hKo` slots (`RamDriverRoot.levelAt`, `levelAt_of_sigma`,
`driverRoot_decides_sentence`, `driverRoot_decides_sentence_binj`) all
stand at the landed carrier form — restating `hKo` at the §2.1 form
with the landed phase walk would make `levelAt`'s order slot
undischargeable (`G2CostProbe.hKo_gap`; `OrderBlockProbe` §2 pins that
no intermediate form exists either). A statement delta without its
program delta is exactly the "checklist-complete but semantically
weakened" failure the campaign forbids.

## The residual work list (OrderBlockProbe item 2, sharpened)

The couplings say more than "engines next": they pin the *shape* of the
engine waves.

* **In-place member passes cannot be the engine repair.** The
  elimination's contract is carrier-shaped on BOTH sides: it ranks
  every carrier vertex (`while cnt < n`; §1's `elm ≡ 1` pin) and its
  entry asks for carrier-zeroed scratch and the carrier-length mask. A
  member-driven elimination is therefore the **compacted-arena** engine
  of g2-cost-design §3(c): the member list renumbers the arena
  (`mm` vertices, member-row slots), the engine runs at carrier `mm`,
  and the outputs scatter back through the list.
* **E2 is coupled to E3 through the ordering contract.** §5 compiles
  that the phase's postcondition (`OrdersBy n π`, a total carrier
  ordering, consumed by `RamCover.cover_spec` and
  `CoverOut.asg_lt` at every carrier vertex) cannot be produced without
  a carrier write. A compacted engine yields a member ordering; the
  contract must be re-stated at the members — which moves the cover
  phase (its consumer), i.e. E3's block-driven cover and R1.8's
  dead-vertex story are upstream of the §2.1 `hKo`, exactly as
  g2-cost-design §6 sequences them (E1–E5 before E6).
* Only then the E-order text + walk, with `OrderBlockProbe` §1's clocks
  re-run arena-affine as the gate.
-/

namespace Lax3Proofs.Refine.OrderEngineProbe

open Lax13Proofs.Imp
open Lax3Proofs.TgtWidenProbe
open Lax3Proofs.Refine.OrderBlockProbe
open Lax3Proofs.Refine.G2CostProbe (orderCostA bsq)

/-! ### §0 The member passes, at the real slots

The three `Com` transliterations of `OrderSigProbeM`'s member-driven
shapes this file moves into the phase, at the E-mem read convention
(`"mem"`/`"mm"`, the post-`ArenaSeam.memEntry` state). They are the
passes the re-run was asked to install; each is refuted below at its
slot. -/

/-- The member-driven scratch re-zero — `OrderSigProbeM.mfillPass` at
the real `elm`/`bh` slots (probe passes 8–9 and 11–12). -/
def memRezeroCom : Com :=
  .seq (.assign "mk" (.lit 0))
    (.while (.lt (.var "mk") (.var "mm"))
      (.seq (.assign "mu" (.get "mem" (.var "mk")))
        (.seq (.store "elm" (.var "mu") (.lit 0))
          (.seq (.store "bh" (.var "mu") (.lit 0))
            (.assign "mk" (.add (.var "mk") (.lit 1)))))))

/-- The member-driven restore — `OrderSigProbeM.mcopyPass` at the real
`off`/`tgt` slots (probe passes 6–7). -/
def memRestoreCom : Com :=
  .seq (.assign "mk" (.lit 0))
    (.while (.lt (.var "mk") (.var "mm"))
      (.seq (.assign "mu" (.get "mem" (.var "mk")))
        (.seq (.store "off" (.var "mu") (.get "gof" (.var "mu")))
          (.seq (.store "tgt" (.var "mu") (.get "gtg" (.var "mu")))
            (.assign "mk" (.add (.var "mk") (.lit 1)))))))

/-- The member-driven mask copy — `OrderSigProbeM.mcopyPass` at the real
`alv` slot (probe pass 3). -/
def memMaskCopyCom (j : ℕ) : Com :=
  .seq (.assign "mk" (.lit 0))
    (.while (.lt (.var "mk") (.var "mm"))
      (.seq (.assign "mu" (.get "mem" (.var "mk")))
        (.seq (.store "alv" (.var "mu")
            (.get (Lax3Proofs.RamDriver.alvName j) (.var "mu")))
          (.assign "mk" (.add (.var "mk") (.lit 1))))))

open Lax3Proofs.RamDriver in
/-- The `R = 0` phase text with its ninth and eleventh passes as slots —
the two places the member shapes below are installed. At the landed
passes this **is** `orderCom 0 j`, definitionally (`orderComAt_landed`),
so each variant below is a one-slot delta of the real text and nothing
else. -/
def orderComAt (rez restore : Com) (j : ℕ) : Com :=
  .seq saveCsr
    (.seq (copyCom (alvName j) "alv")
      (.seq Lax3Proofs.RamElim.elimCom
        (.seq (copyUpto "ioff" "doff" (.add (.var "n") (.lit 1)))
          (.seq (copyUpto "itg" "dtg" (.var "lw"))
            (.seq (foldRange (fun _ => augRoundCom) 0)
              (.seq symCom
                (.seq (fillCom "alv" (.lit 1))
                  (.seq rez
                    (.seq Lax3Proofs.RamElim.elimCom
                      (.seq restore
                        (.seq (ordCom (ordName j)) orderZeroCom)))))))))))

/-- **Text fidelity**: the slotted text at the landed passes is the
landed phase, by `rfl` — the variants differ from `orderCom 0 j` in
exactly the one installed pass. -/
theorem orderComAt_landed (j : ℕ) :
    orderComAt Lax3Proofs.RamDriver.elimRezeroCom Lax3Proofs.RamDriver.restoreCsr j =
      Lax3Proofs.RamDriver.orderCom 0 j := rfl

/-- Pass 8–9 installed: the member re-zero between the two engine
calls. -/
def orderComMZ (j : ℕ) : Com :=
  orderComAt memRezeroCom Lax3Proofs.RamDriver.restoreCsr j

/-- Passes 6–7 installed: the member restore after the second engine
call. -/
def orderComMR (j : ℕ) : Com :=
  orderComAt Lax3Proofs.RamDriver.elimRezeroCom memRestoreCom j

/-! ### The instances

`OrderBlockProbe`'s two-member arena, extended by the E-mem read
convention's `"mem"`/`"mm"` (the state `ArenaSeam.memEntry` leaves:
member array at the CARRIER's physical length, live prefix `[0, 1]`,
junk `9` above it); a wedge instance whose level CSR differs at a dead
row from the arena's own structure; and the all-alive control. -/

/-- The two-member arena in an `n`-carrier, with the member list
present. -/
def edgeArenaStM (n W : ℕ) : PSt :=
  { edgeArenaSt n W with
    vars := [("n", n), ("m", 1), ("lw", W), ("mm", 2)]
    arrs := ("mem", [0, 1] ++ List.replicate (n - 2) 9) :: (edgeArenaSt n W).arrs }

/-- The wedge: edges `0–1` and `0–2` in the LEVEL's graph (`ns = 4`),
mask alive `{0, 1}` — so the masked arena is the single edge `0–1` and
the level's dead row `off[2] = 3` differs from anything the
symmetrization of the arena's orientation writes there. -/
def wedgeArenaStM (n W : ℕ) : PSt :=
  { augSt n W W (List.replicate (n + 1) 0) [] with
    vars := [("n", n), ("m", 2), ("lw", W), ("mm", 2)]
    arrs :=
      ("mem", [0, 1] ++ List.replicate (n - 2) 9) ::
      ("off", 0 :: 2 :: 3 :: List.replicate (n - 2) 4) ::
      ("tgt", [1, 2, 0, 0] ++ List.replicate (W - 4) 0) ::
      ("gof", List.replicate (n + 1) 0) :: ("gtg", List.replicate W 0) ::
      (Lax3Proofs.RamDriver.alvName 0, [1, 1] ++ List.replicate (n - 2) 0) ::
      (Lax3Proofs.RamDriver.gamName 0, List.replicate n 1) ::
      (Lax3Proofs.RamDriver.ordName 0, List.replicate n 0) ::
      (augSt n W W (List.replicate (n + 1) 0) []).arrs }

/-- The all-alive control: members = carrier (`mem` the identity,
`mm = n`), the one reading on which a member pass and its carrier
counterpart coincide. -/
def allAliveStM (n W : ℕ) : PSt :=
  { augSt n W W (List.replicate (n + 1) 0) [] with
    vars := [("n", n), ("m", 1), ("lw", W), ("mm", n)]
    arrs :=
      ("mem", List.range n) ::
      ("off", 0 :: 1 :: List.replicate (n - 1) 2) ::
      ("tgt", [1, 0] ++ List.replicate (W - 2) 0) ::
      ("gof", List.replicate (n + 1) 0) :: ("gtg", List.replicate W 0) ::
      (Lax3Proofs.RamDriver.alvName 0, List.replicate n 1) ::
      (Lax3Proofs.RamDriver.gamName 0, List.replicate n 1) ::
      (Lax3Proofs.RamDriver.ordName 0, List.replicate n 0) ::
      (augSt n W W (List.replicate (n + 1) 0) []).arrs }

/-! ### §1 The engine floor: the first elimination's own share

The phase's opening three passes, instrumented as prefixes so the
engine's share is a difference of clocks on the SAME state — no
modelling, the landed text's own numbers. The engine is run exactly as
the phase runs it (after `saveCsr` and the mask copy). -/

/-- The phase's first two passes. -/
def orderPre2 : Com :=
  .seq Lax3Proofs.RamDriver.saveCsr
    (Lax3Proofs.RamDriver.copyCom (Lax3Proofs.RamDriver.alvName 0) "alv")

/-- …and the first engine call on top of them. -/
def orderPre3 : Com := .seq orderPre2 Lax3Proofs.RamElim.elimCom

/-- The clock of a prefix on the two-member arena at carrier `n`. -/
def preClock (c : Com) (n W : ℕ) : ℕ := (execC pB pF c (edgeArenaSt n W)).2

-- the runs complete
#guard (execC pB pF orderPre3 (edgeArenaSt 100 8)).1.isOk
#guard (execC pB pF orderPre3 (edgeArenaSt 800 8)).1.isOk

-- **the pinned prefix clocks** at the fixed two-member arena
#guard preClock orderPre2 100 8 = 2730
#guard preClock orderPre3 100 8 = 18906
#guard preClock orderPre2 200 8 = 5330
#guard preClock orderPre3 200 8 = 37406

/-- **The engine's own share of the phase clock**: the first
`elimCom`, in context, at a fixed two-member arena. -/
def elimShare (n W : ℕ) : ℕ := preClock orderPre3 n W - preClock orderPre2 n W

-- the share is affine in the CARRIER at the fixed arena: `159·n + 276`,
-- at four carriers spanning a factor of eight
#guard elimShare 100 8 = 159 * 100 + 276
#guard elimShare 200 8 = 159 * 200 + 276
#guard elimShare 400 8 = 159 * 400 + 276
#guard elimShare 800 8 = 159 * 800 + 276

-- **the floor**: the engine call ALONE exceeds the whole §2.1 phase
-- budget at the arena's weight — even a FREE interior cannot flip
-- `OrderBlockProbe`'s gate while this call stands
#guard orderCostA (bsq 2 2 0) 0 4 = 103950
#guard ¬ (elimShare 800 8 ≤ orderCostA (bsq 2 2 0) 0 4)
-- (both directions: the same share fits the same budget read at the
-- ROOT weight, so the defect is the reading point, not the constant)
#guard elimShare 800 8 ≤ orderCostA (bsq 2 2 0) 0 (800 + 2)

/-! #### The engine's write set is the carrier (the K1 pin)

The first elimination extracts EVERY carrier vertex — the loop is
`cnt < n`, the mask only reorders — so its `elm` flags and its ranks
cover the carrier, dead vertices included. This is the fact both
zero-seam refutations below stand on, pinned on data. -/

#guard (List.range 100).all fun v =>
  (execC pB pF orderPre3 (edgeArenaSt 100 8)).1.cell "elm" v == 1
#guard (List.range 100).all fun v =>
  decide ((execC pB pF orderPre3 (edgeArenaSt 100 8)).1.cell "rnk" v < 100)

/-! ### §2 The zero-seam: the member re-zero has no run

Probe passes 8–9 (`mfillPass e1elm`/`e1bh`) installed at
`elimRezeroCom`'s slot. The first engine flagged the whole carrier
(§1); the member re-zero clears the two member cells and nothing else;
the second `elimCom` pops flagged slots, drops every one, its counter
stalls below `n`, and the bucket read walks out of range — **stuck**,
the exact D4 mechanism (`RamDriver.orderCom`'s docstring), replayed at
the member text. The obligation is not "hard to walk": the program has
no run, so ANY Spec for it at the `LevelPre` precondition is refuted.
-/

-- the member text sticks on the two-member arena …
#guard ¬ (execC pB pF (orderComMZ 0) (edgeArenaStM 100 8)).1.isOk
#guard (execC pB pF (orderComMZ 0) (edgeArenaStM 100 8)).1.isStuck
-- … where the LANDED text completes on the SAME state …
#guard (execC pB pF (Lax3Proofs.RamDriver.orderCom 0 0) (edgeArenaStM 100 8)).1.isOk
-- … and the member text completes on the all-alive control (members =
-- carrier), so the refutation is the seam, not the pass
#guard (execC pB pF (orderComMZ 0) (allAliveStM 4 8)).1.isOk

-- the same seam refutes probe passes 11–12 (the exit re-zero,
-- `OrderMem`'s carrier-wide zeroed-scratch clause): after the engine,
-- a member re-zero leaves a dead vertex flagged
#guard (execC pB pF (.seq orderPre3 memRezeroCom) (edgeArenaStM 100 8)).1.cell "elm" 50 = 1

/-! ### §3 The restore-seam: the member restore does not restore

Probe passes 6–7 (`mcopyPass` back into `off`/`tgt`) installed at
`restoreCsr`'s slot, on the wedge. `symCom` wrote the arena structure's
offsets over the WHOLE of `off` (its offset pass is a carrier
`fillUpto`); the member restore puts back the two member cells and
leaves the dead rows holding the arena's offsets — `LevelPre`'s
`σ.arrs "off" = arrOf (n+1) O` clause is false of the exit state on
data, at exactly the dead rows. The five member SAVES (probe passes
1–5) are the same seam from the other side: a member-prefix `gof`/`gtg`
gives even a full restore nothing to restore the dead rows from. -/

-- both texts complete on the wedge
#guard (execC pB pF (orderComMR 0) (wedgeArenaStM 100 8)).1.isOk
#guard (execC pB pF (Lax3Proofs.RamDriver.orderCom 0 0) (wedgeArenaStM 100 8)).1.isOk

-- the LANDED restore hands the level's own dead rows back …
#guard (execC pB pF (Lax3Proofs.RamDriver.orderCom 0 0) (wedgeArenaStM 100 8)).1.cell "off" 2 = 3
#guard (execC pB pF (Lax3Proofs.RamDriver.orderCom 0 0) (wedgeArenaStM 100 8)).1.cell "off" 3 = 4
-- … the member restore leaves the arena structure's offsets there
#guard (execC pB pF (orderComMR 0) (wedgeArenaStM 100 8)).1.cell "off" 2 = 2
#guard (execC pB pF (orderComMR 0) (wedgeArenaStM 100 8)).1.cell "off" 3 = 2

/-! ### §4 The read-seam: the engine reads the mask at the carrier

Probe pass 3 (`mcopyPass alvj → alv`) at the mask-copy slot. The
engine's degree pass reads `alv` at every carrier vertex, and `"alv"`
is shared scratch — the phase's own pass 8 (`fillCom "alv" 1`) leaves
it all-ones for whoever runs next, so at the next level entry the
member copy inherits stale ones at every dead vertex and
`RamElim.ElimPre`'s mask clause (`σ.arrs "alv" = arrOf n M`) is false
on data. Probe passes 4–5 (`d1off`/`d1tg`) are the same seam at
`symCom`'s carrier-wide `doff` reads. -/

/-- The stale-scratch state: `"alv"` as the previous phase leaves it. -/
def staleAlvSt (n W : ℕ) : PSt :=
  { edgeArenaStM n W with
    arrs := ("alv", List.replicate n 1) :: (edgeArenaStM n W).arrs }

#guard (execC pB pF (memMaskCopyCom 0) (staleAlvSt 100 8)).1.isOk
-- the member cells come out right …
#guard (execC pB pF (memMaskCopyCom 0) (staleAlvSt 100 8)).1.cell "alv" 0 = 1
#guard (execC pB pF (memMaskCopyCom 0) (staleAlvSt 100 8)).1.cell "alv" 1 = 1
-- … and a dead vertex stays STALE-ALIVE where the mask says dead: the
-- engine would eliminate the wrong arena
#guard (execC pB pF (memMaskCopyCom 0) (staleAlvSt 100 8)).1.cell "alv" 50 = 1
#guard (execC pB pF (Lax3Proofs.RamDriver.copyCom (Lax3Proofs.RamDriver.alvName 0) "alv")
  (staleAlvSt 100 8)).1.cell "alv" 50 = 0

/-! ### §5 The contract-seam: the ordering is a carrier permutation

Probe pass 10 (`mordPass`) at `ordCom`'s slot, as pure data (the
inversion is straight-line, so the machine adds nothing here). The
phase's postcondition is `RamCover.OrdersBy n π ord` — `ord` inverts a
permutation of the WHOLE carrier, and `RamCover.cover_spec` /
`CoverOut.asg_lt` consume it at every carrier vertex. The member
inversion writes the members' positions and leaves junk everywhere
else, so the contract is false of its output *whatever the engines do*:
this seam is not repaired by member-driven engines alone — the
contract itself must move to the members, which moves its consumer
(the cover phase, E3). -/

/-- The member inversion, as `OrderSigProbeM.mordTw` folded over the
list. -/
def mordRun (ms rnk ord : List ℕ) : List ℕ :=
  (List.range ms.length).foldl (fun A k => A.set rnk[ms[k]!]! ms[k]!) ord

/-- `OrdersBy`'s clause at a concrete size (the `OrderBridge` §5
control, restated): the array sends the position a vertex occupies back
to the vertex. -/
def ordersByAt (n : ℕ) (rnk ordA : List ℕ) : Bool :=
  (List.range n).all fun v => ordA[rnk[v]!]! == v

-- the full inversion of a carrier rank array meets the contract …
#guard ordersByAt 4 [2, 0, 3, 1]
  (Lax3Proofs.Refine.OrderSynth.ordRun 4 [2, 0, 3, 1] [9, 9, 9, 9])
-- … the member inversion is right ON the members …
#guard (mordRun [0, 1] [2, 0, 3, 1] [9, 9, 9, 9])[2]! = 0
#guard (mordRun [0, 1] [2, 0, 3, 1] [9, 9, 9, 9])[0]! = 1
-- … and refuted at the contract: a dead position holds junk that is
-- not even a vertex
#guard ¬ ordersByAt 4 [2, 0, 3, 1] (mordRun [0, 1] [2, 0, 3, 1] [9, 9, 9, 9])
#guard ¬ ((mordRun [0, 1] [2, 0, 3, 1] [9, 9, 9, 9])[1]! < 4)

/-! ### §6 The verdict, cross-referenced

* The interface half is landed and unchanged: `G2CostProbe.hKo_gap`
  (no §2.1 budget dominates the carrier walk),
  `OrderBlockProbe.nested_emptyCharge_floor` /
  `emptyCharge_route_dead` (no intermediate form exists), and §1 here
  (the engine share alone out-runs the §2.1 budget at a light arena).
* The program half cannot start at the phase: §§2–4 compile that each
  member shape installed against the landed engines either has no run,
  breaks `LevelPre`'s frame clauses, or feeds the engine a wrong arena;
  §5 compiles that the phase contract itself is carrier-sized.
* Therefore the four `hKo` slots keep the landed form this wave, and
  the §2.1 restatement stays parked at g2-cost-design §6's own order:
  E2 (compacted-arena engines) and E3 (member cover contract) before
  E6 (interface re-thread). -/

end Lax3Proofs.Refine.OrderEngineProbe
