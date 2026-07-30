import Lax3Proofs.RamAugment
import Lax3Proofs.TgtCoupling

/-!
# ND-MC rebase P2 / satellite 2C — the augmentation round's twins

The computable half of `Lax3Proofs.Refine.AugmentSynth`: ordinary `List`
functions that do what the round's block-structure passes do, and the
differential tests that refute them *before* anything is proved (ledger
D4, "refute before prove"). No `NRest`, no `Ir`, no tower — this file
imports the baseline and `TgtCoupling` and nothing else, so the tests
below are tests against numbers this campaign already owns:
`RamAugment.Demo`'s reported fraternity slot count and
`TgtCoupling`'s K₁,₄ witness.

Split out of `AugmentSynth.lean` for length; every declaration here is
used there.
-/

namespace Lax3Proofs.Refine.AugmentTwins

/-! ## 1. Refute before prove (ledger D4)

Computable twins of the round's block-structure passes, differential
tested *before* any of them is proved, and tested against numbers this
file does not own: `RamAugment.Demo`'s reported fraternity slot count
`mf = 2` and the block structure its `#guard` pins, and
`TgtCoupling`'s K₁,₄ witness.

The twins are ordinary `List` functions — no `NRest`, no `Ir` — written
so that each is the *same fold* as the abstract program of §2–§5 below
(the out-count twin is `cntRow` slot by slot, the prefix twin is
`prefStep` vertex by vertex). Where a pass is not synthesized in this
file, the twin is still here, and it is what §7's pricing is priced
against. -/


/-- The slots of a block: the indices `[a, b)`, in order. -/
def slotsIn (a b : ℕ) : List ℕ := (List.range (b - a)).map fun t => a + t

/-- **The counting pass**, twinned: every slot of every in-block bumps
the out-degree of the vertex it names, one place up. -/
def outCountTw (n : ℕ) (doff dtg : List ℕ) : List ℕ :=
  (List.range n).foldl
    (fun O i => (slotsIn doff[i]! doff[i + 1]!).foldl
      (fun O p => O.set (dtg[p]! + 1) (O[dtg[p]! + 1]! + 1)) O)
    (List.replicate (n + 1) 0)

/-- **The prefix pass**, twinned: the running sum, and the fill pointer
opened at each block's start. -/
def prefixTw (n : ℕ) (O₀ : List ℕ) : List ℕ × List ℕ :=
  (List.range n).foldl
    (fun s i => (s.1.set (i + 1) (s.1[i + 1]! + s.1[i]!), s.2.set i s.1[i]!))
    (O₀, List.replicate n 0)

/-- **The fill pass**, twinned: the arc `u → i` becomes a slot of `u`'s
out-block, at `u`'s fill pointer. -/
def outFillTw (n m : ℕ) (doff dtg ofl₀ : List ℕ) : List ℕ × List ℕ :=
  (List.range n).foldl
    (fun s i => (slotsIn doff[i]! doff[i + 1]!).foldl
      (fun s p => (s.1.set s.2[dtg[p]!]! i, s.2.set dtg[p]! (s.2[dtg[p]!]! + 1))) s)
    (List.replicate m 0, ofl₀)

/-- The whole out-list build, twinned. -/
def outPassTw (n m : ℕ) (doff dtg : List ℕ) : List ℕ × List ℕ :=
  let O := prefixTw n (outCountTw n doff dtg)
  (O.1, (outFillTw n m doff dtg O.2).1)

/-! ### 1.2 The fraternity build, twinned (not synthesized — §7)

The stamped walk: the partners of `i` are the in-neighbours of the
vertices `i` points at, `i` itself stamped first so that the loop is
excluded without a test, and every partner counted once because its
stamp is set when it is counted. The clearing walk is run too, so that
the twin tests the *pair* of walks the pass actually runs. -/

/-- One vertex's stamped count, and the stamp array it leaves. -/
def fratRowTw (doff dtg ooff otg : List ℕ) (stf : List ℕ) (i : ℕ) : ℕ × List ℕ :=
  let s₁ := stf.set i 1
  let r := (slotsIn ooff[i]! ooff[i + 1]!).foldl
    (fun s k => (slotsIn doff[otg[k]!]! doff[otg[k]! + 1]!).foldl
      (fun s q => if s.2[dtg[q]!]! = 0 then (s.1 + 1, s.2.set dtg[q]! 1) else s) s)
    ((0 : ℕ), s₁)
  let cl := (slotsIn ooff[i]! ooff[i + 1]!).foldl
    (fun S k => (slotsIn doff[otg[k]!]! doff[otg[k]! + 1]!).foldl
      (fun S q => S.set dtg[q]! 0) S)
    r.2
  (r.1, cl.set i 0)

/-- The fraternal degrees, one place up — `RamAugment.fratCount`. -/
def fratCountTw (n : ℕ) (doff dtg ooff otg : List ℕ) : List ℕ :=
  ((List.range n).foldl
    (fun s i => let r := fratRowTw doff dtg ooff otg s.2 i; (s.1.set (i + 1) r.1, r.2))
    (List.replicate (n + 1) 0, List.replicate n 0)).1

/-- The number of slots the fraternity graph occupies, as the program
computes it: the round's own reported `mf`. -/
def fratSlotsTw (n : ℕ) (doff dtg ooff otg : List ℕ) : ℕ :=
  ((List.range n).map fun i => (fratCountTw n doff dtg ooff otg)[i + 1]!).sum

/-- **The negative control**: the same walk with the stamp removed. A
pair carried by two witnesses is then counted twice, which is exactly
the defect `RamAugment`'s docstring says the stamp exists to kill. -/
def fratRowTwNoStamp (doff dtg ooff otg : List ℕ) (i : ℕ) : ℕ :=
  (slotsIn ooff[i]! ooff[i + 1]!).foldl
    (fun c k => (slotsIn doff[otg[k]!]! doff[otg[k]! + 1]!).foldl
      (fun c q => if dtg[q]! = i then c else c + 1) c)
    0

/-! ### 1.3 `RamAugment.Demo`'s own four-vertex orientation

In-lists `∅ | 0 | 0 1 | 2` — the arcs `0 → 1`, `0 → 2`, `1 → 2`,
`2 → 3`. The demo's `#guard` reports `mf = 2`: the fraternity graph is
the single edge `{0,1}`, two slots symmetrized. -/

/-- The demo's in-block structure, read off `RamAugment.Demo.demoDoff`
and `demoDtg`. -/
def dOff : List ℕ := [0, 0, 1, 3, 4]
def dTgt : List ℕ := [0, 0, 1, 2]

-- the out-degrees, one place up: `0` points at two vertices, `1` and
-- `2` at one each, `3` at none
#guard outCountTw 4 dOff dTgt = [0, 2, 1, 1, 0]
-- the running sum, and the fill pointers it opens
#guard prefixTw 4 (outCountTw 4 dOff dTgt) = ([0, 2, 3, 4, 4], [0, 2, 3, 4])
-- the out-lists themselves: `1 2 | 2 | 3 |`
#guard outPassTw 4 4 dOff dTgt = ([0, 2, 3, 4, 4], [1, 2, 2, 3])

-- …and the fraternity build on top of them: `1 | 0 | |`, two slots —
-- which is the `mf = 2` `RamAugment.Demo`'s own run reports
#guard fratCountTw 4 dOff dTgt [0, 2, 3, 4, 4] [1, 2, 2, 3] = [0, 1, 1, 0, 0]
#guard fratSlotsTw 4 dOff dTgt [0, 2, 3, 4, 4] [1, 2, 2, 3] = 2

/-- **The demo's slot count is the baseline's.** `RamAugment.Demo`'s run
reports `mf = 2` as the sixth entry of its output list; the twin agrees
with it, and so the fraternity build of §7's pricing is a build of the
same graph. -/
theorem fratSlotsTw_demo : fratSlotsTw 4 dOff dTgt [0, 2, 3, 4, 4] [1, 2, 2, 3] = 2 := by
  decide +kernel

-- **The negative controls.**
-- The out-count is not the *in*-degrees: on this orientation the two
-- differ, so a pass that counted the wrong end would be caught.
/--
error: Expression
  decide (outCountTw 4 dOff dTgt = [0, 0, 1, 2, 1])
did not evaluate to `true`
-/
#guard_msgs in
#guard outCountTw 4 dOff dTgt = [0, 0, 1, 2, 1]

-- The prefix pass really accumulates: the unsummed array is refuted.
/--
error: Expression
  decide ((prefixTw 4 (outCountTw 4 dOff dTgt)).1 = [0, 2, 1, 1, 0])
did not evaluate to `true`
-/
#guard_msgs in
#guard (prefixTw 4 (outCountTw 4 dOff dTgt)).1 = [0, 2, 1, 1, 0]

/-! ### 1.4 The two hazards the brief names, exercised

**Repeated targets.** A vertex with several in-neighbours has each of
them counted, and a vertex pointing at several vertices has its
out-degree counted once per arc — the double-counting hazard is a
*multiplicity* question and the twin answers it on data where the two
readings differ.

**Inherited-vs-new fraternal arcs, and the stamp.** Two vertices sharing
*two* common out-neighbours are one fraternal pair carried by two
witnesses. The stamped walk counts it once; the unstamped one counts it
twice. -/

/-- Two vertices, `0` and `1`, both pointing at `2` and at `3`: the pair
`{0,1}` is fraternal twice over. -/
def wOff : List ℕ := [0, 0, 0, 2, 4]
def wTgt : List ℕ := [0, 1, 0, 1]

#guard outCountTw 4 wOff wTgt = [0, 2, 2, 0, 0]
#guard outPassTw 4 4 wOff wTgt = ([0, 2, 4, 4, 4], [2, 3, 2, 3])

-- the stamped walk counts the doubly-witnessed pair **once**
#guard fratCountTw 4 wOff wTgt [0, 2, 4, 4, 4] [2, 3, 2, 3] = [0, 1, 1, 0, 0]
#guard fratSlotsTw 4 wOff wTgt [0, 2, 4, 4, 4] [2, 3, 2, 3] = 2
-- …and the unstamped one counts it **twice**, at both vertices
#guard fratRowTwNoStamp wOff wTgt [0, 2, 4, 4, 4] [2, 3, 2, 3] 0 = 2
#guard fratRowTwNoStamp wOff wTgt [0, 2, 4, 4, 4] [2, 3, 2, 3] 1 = 2

/-- **The stamp is load-bearing.** On a pair carried by two witnesses the
stamped and unstamped walks disagree — so the dedup is not decoration,
and a `CsrSimple` built by the unstamped walk would name a row twice and
report the wrong degree. -/
theorem stamp_matters :
    fratRowTwNoStamp wOff wTgt [0, 2, 4, 4, 4] [2, 3, 2, 3] 0
      ≠ (fratRowTw wOff wTgt [0, 2, 4, 4, 4] [2, 3, 2, 3] (List.replicate 4 0) 0).1 := by
  decide +kernel

/-! ### 1.5 K₁,₄: the level's slot count is not the round's

`TgtCoupling.not_csrSlots_fratGraph_le_csrSlots` refutes, at the Finset
layer, the reading in which the driver's `tgt` at the level's `ns` could
serve the round. Here the same refutation is *run*: the twin builds the
fraternity graph of the star oriented into its centre and reports twelve
slots against the star's eight. -/

/-- `K₁,₄` oriented into its centre, in block form: the centre `0` has
the four leaves as in-neighbours. This is `TgtCoupling.starOr`. -/
def starOff : List ℕ := [0, 4, 4, 4, 4, 4]
def starTgt : List ℕ := [1, 2, 3, 4]

#guard outPassTw 5 4 starOff starTgt = ([0, 0, 1, 2, 3, 4], [0, 0, 0, 0])
#guard fratSlotsTw 5 starOff starTgt [0, 0, 1, 2, 3, 4] [0, 0, 0, 0] = 12

/-- **The twin computes `TgtCoupling.csrSlots`.** The number of slots
this file's fraternity build would materialize on the star is the
abstract slot count of its fraternity graph — so
`TgtCoupling.not_csrSlots_fratGraph_le_csrSlots` is a refutation *of
this program's width requirement*, not only of a Finset shadow. -/
theorem fratSlotsTw_star :
    fratSlotsTw 5 starOff starTgt [0, 0, 1, 2, 3, 4] [0, 0, 0, 0]
      = TgtCoupling.csrSlots (Lax3Proofs.Augmentation.fratGraph TgtCoupling.starOr) := by
  rw [TgtCoupling.csrSlots_fratGraph_starOr]
  decide +kernel

/-- …and it exceeds the level's own slot count, which is `8`. -/
theorem fratSlotsTw_star_gt :
    ¬ fratSlotsTw 5 starOff starTgt [0, 0, 1, 2, 3, 4] [0, 0, 0, 0]
        ≤ TgtCoupling.csrSlots TgtCoupling.starOr.toGraph := by
  rw [fratSlotsTw_star]
  exact TgtCoupling.not_csrSlots_fratGraph_le_csrSlots


end Lax3Proofs.Refine.AugmentTwins
