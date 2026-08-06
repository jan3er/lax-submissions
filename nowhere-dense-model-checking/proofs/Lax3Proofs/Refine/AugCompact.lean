import Lax3Proofs.Refine.SymCompact

/-!
# ND-MC G2/E2-aug — the compacted-arena augmentation round

The second engine family of `g2-cost-design` §6, on the template
`Refine/ElimCompact.lean` §9 wrote for it, and with the carrier install
shared with `Refine/SymCompact.lean` (`symSetCarrier`, one program for
all three families).

`RamAugment.augCom` is the round the ordering phase folds `R` times. It
reads the current orientation's in-lists out of `doff`/`dtg`, materializes
the fraternity graph in `off`/`tgt`, hands *that* to
`RamElim.elimCom`, and assembles the next orientation into `noff`/`ntg`.
`Refine/OrderEngineProbe.lean`'s coupling-table row 3 refuted the member
form of the two copies that feed it (`d1off`/`d1tg`: "the read-seam:
`symCom`'s offset fill and `forVerts` read `doff` at every carrier
vertex"), and its row 2 the member form of the mask copy. Both are
`augCom`'s seams too, and both die here for the same reason: at carrier
`mm` the copies are *prefix* copies of the compact view and the reads are
at carrier `mm`, so there is no non-member cell to read and no stale cell
to leave behind.

## What the wave had to discover, and did not have to do

`RamAugment.augCom` is **carrier-parametric**, exactly as
`RamElim.elimCom` and `RamDriver.symCom` were. Every one of its ten
passes is a `RamAugment.forVerts`, whose loop is
`.lt (.var "i") (.var "n")`; the sub-call is `elimCom`, itself
`"n"`-bounded (`ElimCompact`'s finding); and its landed Hoare triple
`RamAugment.ImplementsW` is **discharged** by
`RamDriverAugment.implementsW`, a theorem, which quantifies over that
carrier. So "augment at carrier `mm`" needs no re-synthesis whatever: set
`"n" := mm` and apply `RamAugment.augment_specW` at `n := mm`. Neither
the `AugmentSynth` nor the `ElimSynth` heartbeat ceilings were spent in
this file.

The obstruction is again the *length seam*, closed generically in
`ElimCompact` §3 (`bigStepB_padArrs`, `run_of_run_cutArrs`,
`tail_preserved`). This file imports those verbatim and supplies only its
own three pieces: a length schedule (`augClen`, twenty-six arrays), a
live-prefix entry surface (`AugPreC`, twenty-seven clauses), and one
`elimPreW_cutArrs`-shaped lemma (`augPreC_cutArrs`).

## The two hazards the brief named, and what happened to them

**GreedyFratRound's narrowing.** `RamAugment`'s docstring records the
counterexample: asked of *every* arc of `D'` on a fraternity edge the
greedy clause is **false** of this round, and it holds only of the arcs
added on fraternal grounds alone — one `D` did not carry and no
transitive link forced. `AugMemPost` (§6) carries
`GreedyFratRound D D'` as the landed `AugPost` states it, verbatim, and
carries the in-degree budget in the same guarded form
(`∀ d k', D.InDegLE d → LowDegreeVertices (fratGraph D) k' →
D'.InDegLE (d + d*d + k')`). Nothing is re-scoped; §8's bridge proves the
restatement is an equivalence at `mm = n`.

**The width.** This is the one place where the family hits a residue, and
§5 compiles it in both directions.

* The *carrier* has left the width and the cost: the round's demand moves
  from `RamAugment.augWidth n d ≤ W` to `augWidth mm d ≤ W`, which is
  strictly weaker (`augWidth_mono_left`), and its cost from
  `augCost n W` to `augCost mm W`.
* What is left inside `augWidth mm d = mm·(d+1)² + mm·mm + 1` is the
  `mm·mm` term, and it is **arena-quadratic**. `g2-cost-design` §3(a)'s
  repair is `augWidthE nv ks d := nv·(d+1)² + ks + 1`, which §5 defines,
  fits the fraternity graph into (`fratSlots_lt_augWidthE`), proves
  arena-affine (`augWidthE_le_weight`: `≤ (d+1)²·(w+1)`), and separates
  from `augWidth` on data by three orders of magnitude at a sparse arena.
  The capacity step the design flags — `m' ≤ ns` rather than `m' ≤ n²` —
  is re-discharged here at the compact numbering from `arcs_le`
  (`arcs_le_compact`, `arcs_lt_augWidthE`), and `AugMemPost` carries that
  reading as a clause.
* **The obstruction, precisely.** Substituting `augWidthE` for
  `augWidth` inside the round's own precondition is an edit to
  `RamAugment.augWidth` (a read-only definition of this wave) plus the
  four consumer sites `g2-cost-design` §3(a) lists and the `m' ≤ n·n`
  capacity step inside `RamDriverAugment.implementsW`. A satellite cannot
  do it, and no restatement here can hide it: this wave therefore
  delivers the arena-affine width and its fit lemmas, and stops at the
  substitution. See §5.3.

## What is *not* here

One walk is a named obligation (§9): `AugPreps`, that the eleven
preparation passes move the compact in-lists into the round's input arrays
and zero the nine arrays `RamAugment.AugPreW` asks zeroed, over the
compact prefix. It is refuted-before-proved on data in §2.3.

The scatter-back is **not** a new obligation: the round's per-vertex
answer is a rank array, so `ElimCompact.scatterCom` and
`ElimCompact.ScatterBacks` are reused unchanged — one obligation for two
families, exactly as the template's item 3 predicted, and the satellite
discharging it discharges this one's too. The carrier install is
`SymCompact.symSetCarrier` and is **walked**, not assumed.

Nothing here is `sorry`, and no theorem assumes `AugPreps` or
`ScatterBacks` except `augCompact_spec`, which names them as hypotheses.
-/

namespace Lax3Proofs.Refine.AugCompact

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriver (copyUpto fillUpto)
open Lax3Proofs.RamElim (CsrSimple InCsr)
open Lax3Proofs.Augmentation (Orientation AugStep GreedyFratRound LowDegreeVertices
  IsAugChain fratGraph)
open Lax3Proofs.RamAugment (augCom augOr fratSlots augWidth augCost AugPreW AugPost)
open Lax3Proofs.RamDriverCluster (markSet)
open Lax3Proofs.TgtWidenProbe (PSt PRes exec execC pB pF augSt star5doff star5dtg
  aug5doff aug5dtg)
open Lax3Proofs.Refine.ScatterBlock (MemList)
open Lax3Proofs.Refine.ElimCompact (padArrs cutArrs tailOf padArrs_arrs cutArrs_arrs
  run_of_run_cutArrs tail_preserved take_arrOf memGraph getD_padArrs scatterCom scatterCost
  ScatterBacks)
open Lax3Proofs.Refine.SymCompact (symSetCarrier symSetCarrier_run)

/-! ## §1 The program

Thirteen passes and one `Com`. Every bound is `"mm"` or the compact
in-list slot counter `"kd"`; the carrier scalar `"n"` occurs in exactly
two places, both inside the shared carrier install — and the second of
them is what makes the round's ten loops and its sub-call's five
arena-bounded. -/

/-- **The compact orientation into the round's input arrays.** The
phase's own relink (`copyUpto "ioff" "doff" (.add (.var "n") (.lit 1))`,
`copyUpto "itg" "dtg" (.var "lw")`) with both bounds moved to the arena.
This is `OrderEngineProbe`'s coupling row 3, in the form that survives:
a prefix copy, read back at carrier `mm`. -/
def augRelink : Com :=
  .seq (copyUpto "ioff" "doff" (.add (.var "mm") (.lit 1)))
    (copyUpto "itg" "dtg" (.var "kd"))

/-- **The nine arrays `RamAugment.AugPreW` asks zeroed, over the compact
prefix.** Three counting-sort accumulators (`ooff`, `off`, `noff`), the
sub-elimination's two (`bh`, `elm`), and the four stamps. The landed
phase zeroes all nine carrier-wide (`RamDriver.orderZeroCom`,
`augRelinkCom`, `augPrepCom`); here every fill is `mm`- or
`mm+1`-bounded. This is `OrderEngineProbe` §2's zero-seam with nothing to
catch — the re-zero is arena-class *and* a prefix fill, so no cell above
the prefix is left stale, which is exactly what the member re-zero could
not achieve. -/
def augZero : Com :=
  .seq (fillUpto "ooff" (.add (.var "mm") (.lit 1)) (.lit 0))
    (.seq (fillUpto "off" (.add (.var "mm") (.lit 1)) (.lit 0))
      (.seq (fillUpto "noff" (.add (.var "mm") (.lit 1)) (.lit 0))
        (.seq (fillUpto "bh" (.add (.var "mm") (.lit 1)) (.lit 0))
          (.seq (fillUpto "elm" (.var "mm") (.lit 0))
            (.seq (fillUpto "stf" (.var "mm") (.lit 0))
              (.seq (fillUpto "sta" (.var "mm") (.lit 0))
                (.seq (fillUpto "std" (.var "mm") (.lit 0))
                  (fillUpto "ste" (.var "mm") (.lit 0)))))))))

/-- The eleven preparation passes. -/
def augPrepCom : Com := .seq augRelink augZero

/-- **The compacted round, core**: install the carrier, prepare, run the
landed round, scatter the ranks back through the member list. The
carrier install comes *first*, so that the preparation's own bounds and
the round's are read in the same arena.

`off`/`tgt` come out holding the round's fraternity graph and not the
level's block structure — as they do in the landed phase, which restores
them afterwards. In the compacted design that restore is an
arena-class *prefix* copy (`ElimCompact`'s `savePre`/`restorePre`), which
is the finding this family inherits rather than re-derives. -/
def augCompactCore : Com :=
  .seq symSetCarrier (.seq augPrepCom (.seq augCom scatterCom))

/-- …and with the carrier scalar put back. -/
def augCompactCom : Com := .seq augCompactCore (.assign "n" (.var "kn"))

/-! ### §1.1 Frames -/

theorem notMem_augRelink_warrs {a : String} (h₁ : a ≠ "doff") (h₂ : a ≠ "dtg") :
    a ∉ augRelink.warrs := by
  simp [augRelink, copyUpto, fillUpto, Fill.put, Com.warrs, h₁, h₂]

theorem notMem_augZero_warrs {a : String} (h₁ : a ≠ "ooff") (h₂ : a ≠ "off")
    (h₃ : a ≠ "noff") (h₄ : a ≠ "bh") (h₅ : a ≠ "elm") (h₆ : a ≠ "stf") (h₇ : a ≠ "sta")
    (h₈ : a ≠ "std") (h₉ : a ≠ "ste") : a ∉ augZero.warrs := by
  simp [augZero, fillUpto, Fill.put, Com.warrs, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]

theorem notMem_augPrepCom_warrs {a : String} (h₀ : a ≠ "doff") (h₁ : a ≠ "dtg")
    (h₂ : a ≠ "ooff") (h₃ : a ≠ "off") (h₄ : a ≠ "noff") (h₅ : a ≠ "bh") (h₆ : a ≠ "elm")
    (h₇ : a ≠ "stf") (h₈ : a ≠ "sta") (h₉ : a ≠ "std") (h₁₀ : a ≠ "ste") :
    a ∉ augPrepCom.warrs := by
  simp [augPrepCom, augRelink, augZero, copyUpto, fillUpto, Fill.put, Com.warrs,
    h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀]

theorem notMem_augPrepCom_wvars {y : String} (h : y ≠ "i") : y ∉ augPrepCom.wvars := by
  simp [augPrepCom, augRelink, augZero, copyUpto, fillUpto, Fill.put, Com.wvars, h]

/-! ## §2 The compiled data

Refute-before-prove, on `TgtWidenProbe`'s witness instance: the star
`K₁,₄` oriented into its centre (`star5doff`/`star5dtg`, in-degree four),
carried as the **compact** in-lists of a five-member arena at the *odd*
vertices `1, 3, 5, 7, 9` of a carrier of any size, with a **sentinel**
above every compact prefix. `TgtWidenProbe.star5Wide` records the landed
round's answers on that orientation at carrier `5`: fraternity slots
`12`, greedy bound `3`, ten new arcs, and the block structure
`aug5doff`/`aug5dtg`. The compacted composite must produce exactly those,
scattered. -/

/-- The compact in-list offsets at the carrier's physical length. -/
def augIoffL (n : ℕ) : List ℕ := star5doff ++ List.replicate (n + 1 - 6) 4

/-- …and its targets at the width. -/
def augItgL (W : ℕ) : List ℕ := star5dtg ++ List.replicate (W - 4) 0

/-- The store the composite runs in: `augSt`'s twenty-six arrays with the
compact in-lists installed, the member list at the odd placement (junk
above the live prefix, the `ArenaSeam` convention), the arena-numbered
rank destination `"ork"`, and the **sentinel** `7` in every array the
round writes. -/
def aSt (n W mm kd : ℕ) : PSt :=
  { augSt n W W (List.replicate (n + 1) 0) [] with
    vars := [("n", n), ("m", 0), ("lw", W), ("mm", mm), ("kd", kd)]
    arrs :=
      ("ioff", augIoffL n) :: ("itg", augItgL W) ::
      ("mem", [1, 3, 5, 7, 9] ++ List.replicate (n - 5) 999) ::
      ("ork", List.replicate n 7) ::
      ("doff", List.replicate (n + 1) 7) :: ("dtg", List.replicate W 7) ::
      ("ooff", List.replicate (n + 1) 7) :: ("otg", List.replicate W 7) ::
      ("ofl", List.replicate n 7) ::
      ("off", List.replicate (n + 1) 7) :: ("tgt", List.replicate W 7) ::
      ("ffl", List.replicate n 7) :: ("alv", List.replicate n 7) ::
      ("deg", List.replicate n 7) :: ("elm", List.replicate n 7) ::
      ("rnk", List.replicate n 7) :: ("idg", List.replicate n 7) ::
      ("bh", List.replicate (n + 1) 7) :: ("ifl", List.replicate n 7) ::
      ("noff", List.replicate (n + 1) 7) :: ("nfl", List.replicate n 7) ::
      ("ntg", List.replicate W 7) ::
      ("stf", List.replicate n 7) :: ("sta", List.replicate n 7) ::
      ("std", List.replicate n 7) :: ("ste", List.replicate n 7) ::
      (augSt n W W (List.replicate (n + 1) 0) []).arrs }

/-- The composite on the five-member arena at carrier `n`. -/
def augRun (n W : ℕ) : PRes := exec pB pF augCompactCom (aSt n W 5 4)

#guard (augRun 100 200).isOk
#guard (augRun 800 200).isOk

/-! ### §2.1 The answers are the landed round's, at the compact carrier -/

-- the fraternity graph of the star is `K₄` on the leaves: twelve slots,
-- `TgtCoupling.csrSlots_fratGraph_starOr`'s number, measured by the run
#guard (augRun 100 200).scalar "mf" = 12
-- the greedy bound of `K₄` is its degeneracy
#guard (augRun 100 200).scalar "kmax" = 3
-- ten new arcs, and the block structure `TgtWidenProbe.aug5doff/aug5dtg`
#guard (augRun 100 200).scalar "mn" = 10
#guard (List.range 6).map ((augRun 100 200).cell "noff") = aug5doff
#guard (List.range 10).map ((augRun 100 200).cell "ntg") = aug5dtg

-- carrier-blind, answer for answer, at a carrier eight times larger
#guard (augRun 800 200).scalar "mf" = 12
#guard (augRun 800 200).scalar "kmax" = 3
#guard (augRun 800 200).scalar "mn" = 10
#guard (List.range 6).map ((augRun 800 200).cell "noff") = aug5doff
#guard (List.range 10).map ((augRun 800 200).cell "ntg") = aug5dtg

-- the carrier scalar comes back
#guard (augRun 100 200).scalar "n" = 100
#guard (augRun 800 200).scalar "n" = 800

-- **the ranks**: the elimination of `K₄` on the leaves peels the centre
-- first (it is isolated in the fraternity graph) and then the clique, so
-- the centre ranks `4` and the leaves `0 1 2 3`
#guard (List.range 5).map ((augRun 100 200).cell "rnk") = [4, 0, 1, 2, 3]
-- **…scattered back to the arena's numbering** through the member list
-- `1 3 5 7 9`: this is `ElimCompact.scatterCom` reused verbatim
#guard (List.range 5).map (fun k => (augRun 100 200).cell "ork" (2 * k + 1)) = [4, 0, 1, 2, 3]
#guard (List.range 5).map (fun k => (augRun 800 200).cell "ork" (2 * k + 1)) = [4, 0, 1, 2, 3]

/-! ### §2.2 The engine touches no carrier cell

The sentinel `7` sits above every compact prefix, and the composite must
hand every one of those cells back. Two of them are the coupling table's
own refutations:

* `alv` — the read-seam (row 2). The round's `alvSet` fills the mask at
  every vertex of *its* carrier; at carrier `mm` that is the compact
  prefix, and the level's own mask at its dead vertices is still there
  when the round is done.
* `off` — the restore-seam (rows 1 and 4). The fraternity build writes
  `off[0..mm]` and `tgt[0..mf)` and nothing above either. -/

#guard (List.range 95).all fun k => (augRun 100 200).cell "alv" (5 + k) == 7
#guard (List.range 95).all fun k => (augRun 100 200).cell "off" (6 + k) == 7
#guard (List.range 95).all fun k => (augRun 100 200).cell "noff" (6 + k) == 7
#guard (List.range 95).all fun k => (augRun 100 200).cell "elm" (5 + k) == 7
#guard (List.range 95).all fun k => (augRun 100 200).cell "rnk" (5 + k) == 7
#guard (List.range 95).all fun k => (augRun 100 200).cell "stf" (5 + k) == 7
#guard (List.range 95).all fun k => (augRun 100 200).cell "sta" (5 + k) == 7
#guard (List.range 95).all fun k => (augRun 100 200).cell "std" (5 + k) == 7
#guard (List.range 95).all fun k => (augRun 100 200).cell "ste" (5 + k) == 7
#guard (List.range 188).all fun k => (augRun 100 200).cell "tgt" (12 + k) == 7
-- and the same at the larger carrier, on the two seam arrays
#guard (List.range 795).all fun k => (augRun 800 200).cell "alv" (5 + k) == 7
#guard (List.range 794).all fun k => (augRun 800 200).cell "off" (6 + k) == 7

-- **the scatter really is member-driven**: nothing is written at a
-- non-member cell of `"ork"`, so the arena numbering's own junk survives
#guard (List.range 45).all fun k => (augRun 100 200).cell "ork" (2 * k) == 7

/-- The negative control's store: the same orientation padded to the
carrier in `doff`/`dtg`, and the nine zeroed arrays zeroed carrier-wide,
so the landed round runs on the same arena at the **carrier**. -/
def augCarrierSt (n W : ℕ) : PSt :=
  { aSt n W 5 4 with
    arrs := ("doff", augIoffL n) :: ("dtg", augItgL W) ::
      ("ooff", List.replicate (n + 1) 0) :: ("off", List.replicate (n + 1) 0) ::
      ("noff", List.replicate (n + 1) 0) :: ("bh", List.replicate (n + 1) 0) ::
      ("elm", List.replicate n 0) :: ("stf", List.replicate n 0) ::
      ("sta", List.replicate n 0) :: ("std", List.replicate n 0) ::
      ("ste", List.replicate n 0) :: (aSt n W 5 4).arrs }

def augCarrierRun (n W : ℕ) : PRes := exec pB pF augCom (augCarrierSt n W)

#guard (augCarrierRun 100 200).isOk
-- the same answers …
#guard (augCarrierRun 100 200).scalar "mf" = 12
#guard (augCarrierRun 100 200).scalar "kmax" = 3
#guard (augCarrierRun 100 200).scalar "mn" = 10
-- … and the level's mask gone: the round's `alvSet` ran to the carrier,
-- which is `OrderEngineProbe` §4's read-seam from the other side
#guard ¬ ((List.range 95).all fun k => (augCarrierRun 100 200).cell "alv" (5 + k) == 7)
#guard (augCarrierRun 100 200).cell "alv" 50 = 1
-- … and the level's offset rows with it
#guard ¬ ((List.range 95).all fun k => (augCarrierRun 100 200).cell "off" (6 + k) == 7)

-- **the honesty direction on the compact prefix**: the wave does not get
-- its frame by writing nothing — the arena's own cells really did change
#guard ¬ ((List.range 5).all fun k => (augRun 100 200).cell "alv" k == 7)
#guard ¬ ((List.range 6).all fun k => (augRun 100 200).cell "noff" k == 7)

/-! ### §2.3 The preparation passes are load-bearing

Refute-before-prove on `AugPreps` (§9). Without the relink the round
augments the sentinel; without the nine zeroing fills it has **no run at
all** — the sub-elimination's `elimLoop` pops flagged slots, drops every
one and reads `bh` out of range, which in IMP+ is stuck, not defaulted.
That is the D4 mechanism (`RamDriver.augPrepCom`'s docstring), and it is
what makes the zeroing half of the obligation refutable rather than
decorative. -/

-- without the preparation, the round is STUCK on the same store
#guard ¬ (exec pB pF (.seq symSetCarrier augCom) (aSt 100 200 5 4)).isOk
#guard (exec pB pF (.seq symSetCarrier augCom) (aSt 100 200 5 4)).isStuck
-- with the relink but no re-zero, still stuck
#guard (exec pB pF (.seq symSetCarrier (.seq augRelink augCom)) (aSt 100 200 5 4)).isStuck
-- with both, it runs — the obligation's content, separated on data
#guard (exec pB pF (.seq symSetCarrier (.seq augPrepCom augCom)) (aSt 100 200 5 4)).isOk

-- and the carrier install is load-bearing: without it the round runs at
-- the carrier on a store prepared only over the compact prefix, and
-- sticks (the nine arrays are zeroed only up to `mm`)
#guard ¬ (exec pB pF (.seq augPrepCom augCom) (aSt 100 200 5 4)).isOk

/-! ## §3 The length schedule and the live-prefix entry -/

/-- **The length schedule of a compacted round.** Which prefix of each of
the round's twenty-six arrays is the compact call's own array. The four
width-class arrays (`dtg`, `otg`, `itg`, `ntg`), the target array `tgt`
and the bucket arena `bv`/`bn` are cut at the caller's own widths, so
those cuts are the identity or nearly so — the widths were never
carrier-*indexed*, only carrier-*sized*, which is §5's story. -/
def augClen (mm nt W : ℕ) : String → ℕ := fun a =>
  if a = "doff" ∨ a = "ooff" ∨ a = "off" ∨ a = "bh" ∨ a = "ioff" ∨ a = "noff" then mm + 1
  else if a = "ofl" ∨ a = "ffl" ∨ a = "alv" ∨ a = "deg" ∨ a = "elm" ∨ a = "rnk" ∨
      a = "idg" ∨ a = "ifl" ∨ a = "nfl" ∨ a = "stf" ∨ a = "sta" ∨ a = "std" ∨ a = "ste"
    then mm
  else if a = "dtg" ∨ a = "otg" ∨ a = "itg" ∨ a = "ntg" then W
  else if a = "tgt" then nt
  else if a = "bv" ∨ a = "bn" then mm + W + 1
  else 0

@[simp] theorem augClen_doff (mm nt W : ℕ) : augClen mm nt W "doff" = mm + 1 := by simp [augClen]
@[simp] theorem augClen_ooff (mm nt W : ℕ) : augClen mm nt W "ooff" = mm + 1 := by simp [augClen]
@[simp] theorem augClen_off (mm nt W : ℕ) : augClen mm nt W "off" = mm + 1 := by simp [augClen]
@[simp] theorem augClen_bh (mm nt W : ℕ) : augClen mm nt W "bh" = mm + 1 := by simp [augClen]
@[simp] theorem augClen_ioff (mm nt W : ℕ) : augClen mm nt W "ioff" = mm + 1 := by simp [augClen]
@[simp] theorem augClen_noff (mm nt W : ℕ) : augClen mm nt W "noff" = mm + 1 := by simp [augClen]
@[simp] theorem augClen_ofl (mm nt W : ℕ) : augClen mm nt W "ofl" = mm := by simp [augClen]
@[simp] theorem augClen_ffl (mm nt W : ℕ) : augClen mm nt W "ffl" = mm := by simp [augClen]
@[simp] theorem augClen_alv (mm nt W : ℕ) : augClen mm nt W "alv" = mm := by simp [augClen]
@[simp] theorem augClen_deg (mm nt W : ℕ) : augClen mm nt W "deg" = mm := by simp [augClen]
@[simp] theorem augClen_elm (mm nt W : ℕ) : augClen mm nt W "elm" = mm := by simp [augClen]
@[simp] theorem augClen_rnk (mm nt W : ℕ) : augClen mm nt W "rnk" = mm := by simp [augClen]
@[simp] theorem augClen_idg (mm nt W : ℕ) : augClen mm nt W "idg" = mm := by simp [augClen]
@[simp] theorem augClen_ifl (mm nt W : ℕ) : augClen mm nt W "ifl" = mm := by simp [augClen]
@[simp] theorem augClen_nfl (mm nt W : ℕ) : augClen mm nt W "nfl" = mm := by simp [augClen]
@[simp] theorem augClen_stf (mm nt W : ℕ) : augClen mm nt W "stf" = mm := by simp [augClen]
@[simp] theorem augClen_sta (mm nt W : ℕ) : augClen mm nt W "sta" = mm := by simp [augClen]
@[simp] theorem augClen_std (mm nt W : ℕ) : augClen mm nt W "std" = mm := by simp [augClen]
@[simp] theorem augClen_ste (mm nt W : ℕ) : augClen mm nt W "ste" = mm := by simp [augClen]
@[simp] theorem augClen_dtg (mm nt W : ℕ) : augClen mm nt W "dtg" = W := by simp [augClen]
@[simp] theorem augClen_otg (mm nt W : ℕ) : augClen mm nt W "otg" = W := by simp [augClen]
@[simp] theorem augClen_itg (mm nt W : ℕ) : augClen mm nt W "itg" = W := by simp [augClen]
@[simp] theorem augClen_ntg (mm nt W : ℕ) : augClen mm nt W "ntg" = W := by simp [augClen]
@[simp] theorem augClen_tgt (mm nt W : ℕ) : augClen mm nt W "tgt" = nt := by simp [augClen]
@[simp] theorem augClen_bv (mm nt W : ℕ) : augClen mm nt W "bv" = mm + W + 1 := by simp [augClen]
@[simp] theorem augClen_bn (mm nt W : ℕ) : augClen mm nt W "bn" = mm + W + 1 := by simp [augClen]

/-- **The round's entry surface at a live prefix.** Clause for clause
`RamAugment.AugPreW`, with every physical length at the carrier `n` and
every *contract* at the compact carrier `mm`. Note what is not here: no
clause ranges over the carrier. Nine arrays are asked zeroed over the
compact prefix and not over the carrier, which is the zero-seam with
nothing to catch. -/
def AugPreC (mm n nt W : ℕ) (DO DT : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = mm ∧ mm ≤ n ∧
  (∃ g, σ.arrs "doff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = DO i) ∧
  σ.arrs "dtg" = arrOf W DT ∧
  (∃ g, σ.arrs "ooff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = 0) ∧
  (∃ g, σ.arrs "otg" = arrOf W g) ∧ (∃ g, σ.arrs "ofl" = arrOf n g) ∧
  (∃ g, σ.arrs "off" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = 0) ∧
  (∃ g, σ.arrs "tgt" = arrOf nt g) ∧ (∃ g, σ.arrs "ffl" = arrOf n g) ∧
  (∃ g, σ.arrs "alv" = arrOf n g) ∧ (∃ g, σ.arrs "deg" = arrOf n g) ∧
  (∃ g, σ.arrs "elm" = arrOf n g ∧ ∀ i < mm, g i = 0) ∧
  (∃ g, σ.arrs "rnk" = arrOf n g) ∧ (∃ g, σ.arrs "idg" = arrOf n g) ∧
  (∃ g, σ.arrs "bh" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = 0) ∧
  (∃ g, σ.arrs "bv" = arrOf (n + W + 1) g) ∧ (∃ g, σ.arrs "bn" = arrOf (n + W + 1) g) ∧
  (∃ g, σ.arrs "ioff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "ifl" = arrOf n g) ∧
  (∃ g, σ.arrs "itg" = arrOf W g) ∧
  (∃ g, σ.arrs "noff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = 0) ∧
  (∃ g, σ.arrs "nfl" = arrOf n g) ∧ (∃ g, σ.arrs "ntg" = arrOf W g) ∧
  (∃ g, σ.arrs "stf" = arrOf n g ∧ ∀ i < mm, g i = 0) ∧
  (∃ g, σ.arrs "sta" = arrOf n g ∧ ∀ i < mm, g i = 0) ∧
  (∃ g, σ.arrs "std" = arrOf n g ∧ ∀ i < mm, g i = 0) ∧
  (∃ g, σ.arrs "ste" = arrOf n g ∧ ∀ i < mm, g i = 0)

/-- **The seam, closed at the augmentation.** The live-prefix surface at
the carrier's physical lengths *is* the landed round's surface at the
compact carrier, read in the view. Every clause is one `take_arrOf` and
one `arrOf_congr`; `RamAugment` is not touched. -/
theorem augPreC_cutArrs {mm n nt W : ℕ} {DO DT : ℕ → ℕ} {σ : Env}
    (h : AugPreC mm n nt W DO DT σ) :
    AugPreW mm nt W DO DT (cutArrs σ (augClen mm nt W)) := by
  obtain ⟨hn, hmn, ⟨d, hd, hdP⟩, hdtg, ⟨o, ho, hoP⟩, ⟨t, ht⟩, ⟨fl, hfl⟩,
    ⟨e, he, heP⟩, ⟨g, hg⟩, ⟨ff, hff⟩, ⟨al, hal⟩, ⟨dg, hdg⟩, ⟨em, hem, hemP⟩,
    ⟨rk, hrk⟩, ⟨ig, hig⟩, ⟨bh, hbh, hbhP⟩, ⟨bv, hbv⟩, ⟨bn, hbn⟩, ⟨io, hio⟩,
    ⟨il, hil⟩, ⟨it, hit⟩, ⟨no, hno, hnoP⟩, ⟨nl, hnl⟩, ⟨nt', hnt'⟩,
    ⟨sf, hsf, hsfP⟩, ⟨sa, hsa, hsaP⟩, ⟨sd, hsd, hsdP⟩, ⟨se, hse, hseP⟩⟩ := h
  refine ⟨hn, ?_, ?_, ⟨o, ?_, hoP⟩, ⟨t, ?_⟩, ⟨fl, ?_⟩, ⟨e, ?_, heP⟩, ⟨g, ?_⟩, ⟨ff, ?_⟩,
    ⟨al, ?_⟩, ⟨dg, ?_⟩, ⟨em, ?_, hemP⟩, ⟨rk, ?_⟩, ⟨ig, ?_⟩, ⟨bh, ?_, hbhP⟩, ⟨bv, ?_⟩,
    ⟨bn, ?_⟩, ⟨io, ?_⟩, ⟨il, ?_⟩, ⟨it, ?_⟩, ⟨no, ?_, hnoP⟩, ⟨nl, ?_⟩, ⟨nt', ?_⟩,
    ⟨sf, ?_, hsfP⟩, ⟨sa, ?_, hsaP⟩, ⟨sd, ?_, hsdP⟩, ⟨se, ?_, hseP⟩⟩
  · rw [cutArrs_arrs, augClen_doff, hd, take_arrOf (by omega)]
    exact ElimCompact.arrOf_congr fun i hi => hdP i (by omega)
  · rw [cutArrs_arrs, augClen_dtg, hdtg, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augClen_ooff, ho, take_arrOf (by omega)]
  · rw [cutArrs_arrs, augClen_otg, ht, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augClen_ofl, hfl, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_off, he, take_arrOf (by omega)]
  · rw [cutArrs_arrs, augClen_tgt, hg, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augClen_ffl, hff, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_alv, hal, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_deg, hdg, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_elm, hem, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_rnk, hrk, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_idg, hig, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_bh, hbh, take_arrOf (by omega)]
  · rw [cutArrs_arrs, augClen_bv, hbv, take_arrOf (by omega)]
  · rw [cutArrs_arrs, augClen_bn, hbn, take_arrOf (by omega)]
  · rw [cutArrs_arrs, augClen_ioff, hio, take_arrOf (by omega)]
  · rw [cutArrs_arrs, augClen_ifl, hil, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_itg, hit, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augClen_noff, hno, take_arrOf (by omega)]
  · rw [cutArrs_arrs, augClen_nfl, hnl, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_ntg, hnt', take_arrOf le_rfl]
  · rw [cutArrs_arrs, augClen_stf, hsf, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_sta, hsa, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_std, hsd, take_arrOf hmn]
  · rw [cutArrs_arrs, augClen_ste, hse, take_arrOf hmn]

/-! ### §3.1 Two accessors

The clauses the composite reads back off the entry surface. -/

theorem AugPreC.alv {mm n nt W : ℕ} {DO DT : ℕ → ℕ} {σ : Env}
    (h : AugPreC mm n nt W DO DT σ) : ∃ g, σ.arrs "alv" = arrOf n g :=
  h.2.2.2.2.2.2.2.2.2.2.1

theorem AugPreC.ntg {mm n nt W : ℕ} {DO DT : ℕ → ℕ} {σ : Env}
    (h : AugPreC mm n nt W DO DT σ) : ∃ g, σ.arrs "ntg" = arrOf W g :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! ## §4 The round at the arena's carrier

The landed walk, transported. `RamAugment.augment_specW` is applied at
`n := mm` with `RamDriverAugment.implementsW` — a theorem — supplying the
Hoare triple. Nothing is restated and nothing is re-synthesized. -/

/-- **The compacted round.** `RamAugment.augCom`, unchanged, at the
compact carrier `mm`, on a store whose arrays are the carrier's: it runs
at `RamAugment.augCost mm W` — a cost in which **the carrier does not
occur** — and leaves `RamAugment.AugPost`, the landed contract, verbatim,
of the compact view. The exit store is the view's answer over the tail the
call entered with, so the level's own mask and offsets above the compact
prefix come back untouched. -/
theorem augCompact_engine {B mm n nt W d m : ℕ} {D : Orientation mm} {DO DT : ℕ → ℕ}
    {σ : Env} (hin : InCsr D m DO DT) (hd : D.InDegLE d) (hnt : fratSlots D ≤ nt)
    (hm : m ≤ W) (hW : augWidth mm d ≤ W) (hB : mm + W + 1 < B)
    (hpre : AugPreC mm n nt W DO DT σ) :
    ∃ τ, Run B augCom σ (padArrs τ (tailOf σ (augClen mm nt W))) (augCost mm W) ∧
        AugPost mm W D (cutArrs σ (augClen mm nt W)) τ ∧
        (∀ a, augClen mm nt W a ≤ (σ.arrs a).length →
          ((padArrs τ (tailOf σ (augClen mm nt W))).arrs a).drop (augClen mm nt W a) =
            (σ.arrs a).drop (augClen mm nt W a)) := by
  obtain ⟨τ, hrun, hpost⟩ :=
    (Lax3Proofs.RamAugment.augment_specW (n := mm) Lax3Proofs.RamDriverAugment.implementsW
      hin hd hnt hm hW hB).run (augPreC_cutArrs hpre)
  exact ⟨τ, run_of_run_cutArrs _ hrun, hpost, fun a ha => tail_preserved hrun ha⟩

/-! ## §5 The width, and the one residue

`g2-cost-design` §3(a) is the design this section executes and the one
place it stops. -/

/-- **The degree-aware width** of `g2-cost-design` §3(a): the room the
fraternity graph needs, plus the arena's own slot count, and *not* the
square of the vertex count. `RamAugment.augWidth`'s `nv·nv` term is there
to hold the round's output block structure at the generic `m' ≤ n²`; the
sharp bound is `m' ≤ nv · d'` by `arcs_le`, which is what `ks` stands
for. -/
def augWidthE (nv ks d : ℕ) : ℕ := nv * (d + 1) ^ 2 + ks + 1

/-- **The fraternity graph fits the arena-affine width.** The `ks` term
is not needed for this half: `fratSlots D ≤ nv · d²` and
`d² ≤ (d+1)²`. -/
theorem fratSlots_lt_augWidthE {mm ks d : ℕ} {D : Orientation mm} (hd : D.InDegLE d) :
    fratSlots D < augWidthE mm ks d := by
  have h₁ := Lax3Proofs.RamAugment.fratSlots_le hd
  have h₂ : mm * (d * d) ≤ mm * (d + 1) ^ 2 := Nat.mul_le_mul_left mm (by nlinarith)
  simp only [augWidthE]
  omega

/-- **The arena-affine reading**: the width is `(d+1)²` times the arena's
own weight, which is `g2-cost-design` §1's `coeff · (w + 1)` shape with
the coefficient depending on the degree budget alone. This is the whole
point of the repair — `augWidth`'s `mm·mm` has no such reading. -/
theorem augWidthE_le_weight {mm ks d w : ℕ} (h : mm + ks ≤ w) :
    augWidthE mm ks d ≤ (d + 1) ^ 2 * (w + 1) := by
  have h₃ : ks + 1 ≤ (d + 1) ^ 2 * (ks + 1) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have key : augWidthE mm ks d ≤ (d + 1) ^ 2 * (mm + ks + 1) := by
    calc augWidthE mm ks d = mm * (d + 1) ^ 2 + (ks + 1) := by simp only [augWidthE]; ring
      _ ≤ mm * (d + 1) ^ 2 + (d + 1) ^ 2 * (ks + 1) := Nat.add_le_add_left h₃ _
      _ = (d + 1) ^ 2 * (mm + ks + 1) := by ring
  exact key.trans (Nat.mul_le_mul_left _ (by omega))

/-- The sharper width is below the landed one exactly when the arena's
slot capacity is below the arena's square — which is the generic bound the
`nv·nv` term stands for. -/
theorem augWidthE_le_augWidth {mm ks d : ℕ} (h : ks ≤ mm * mm) :
    augWidthE mm ks d ≤ augWidth mm d := by
  simp only [augWidthE, augWidth]
  omega

/-- **The carrier really has left the round's width demand.** The
compacted round asks `augWidth mm d ≤ W` where the carrier round asked
`augWidth n d ≤ W`, and the first is implied by the second. So the
compacted engine strictly weakens what the allocation has to supply,
whatever happens to the `mm·mm` term. -/
theorem augWidth_mono_left {mm n d : ℕ} (h : mm ≤ n) : augWidth mm d ≤ augWidth n d := by
  simp only [augWidth]
  have h₁ : mm * (d + 1) ^ 2 ≤ n * (d + 1) ^ 2 := Nat.mul_le_mul_right _ h
  have h₂ : mm * mm ≤ n * n := Nat.mul_le_mul h h
  omega

/-! ### §5.1 The capacity step, at the compact numbering

`g2-cost-design` §3(a): "the `m' ≤ n²` capacity steps flagged at
`RamDriverAugment:5988/6061` must re-discharge from `m' ≤ ns` /
`m' ≤ n·budget` via `arcs_le`; this is the one place the walk content
changes, not just the statement". Here is that reading, at the compact
numbering. -/

/-- **The round's output capacity, read off the compact arena.** The
number of arcs of an orientation of `Fin mm` of in-degree at most `d'` is
at most `mm · d'` — never `mm · mm`. This is `RamDriverAugment.arcs_le` at
the compact carrier, and it is the clause `AugMemPost` carries. -/
theorem arcs_le_compact {mm m' d' : ℕ} {D' : Orientation mm} {NO NT : ℕ → ℕ}
    (h : InCsr D' m' NO NT) (hd : D'.InDegLE d') : m' ≤ mm * d' :=
  Lax3Proofs.RamDriverAugment.arcs_le h hd

/-- …and it fits the arena-affine width whenever the arena's slot
capacity does. -/
theorem arcs_lt_augWidthE {mm m' d' ks d : ℕ} {D' : Orientation mm} {NO NT : ℕ → ℕ}
    (h : InCsr D' m' NO NT) (hd : D'.InDegLE d') (hks : mm * d' ≤ ks) :
    m' < augWidthE mm ks d := by
  have := arcs_le_compact h hd
  simp only [augWidthE]
  omega

/-! ### §5.2 The separation, compiled

The two widths at a sparse arena of a thousand members: the landed one is
arena-*quadratic* and the repaired one arena-*affine*, three orders of
magnitude apart. This is `g2-cost-design` §3(a)'s `width_step_dead` at the
compacted arena. -/

#guard augWidthE 1000 4000 4 = 1000 * 25 + 4000 + 1
#guard augWidthE 1000 4000 4 = 29001
#guard augWidth 1000 4 = 1000 * 25 + 1000 * 1000 + 1
#guard augWidth 1000 4 = 1025001
-- the repaired width is inside `(d+1)²·(w+1)` at the arena's weight …
#guard augWidthE 1000 4000 4 ≤ 25 * (5000 + 1)
-- … and the landed one is NOT: no arena-affine reading exists for it
#guard ¬ (augWidth 1000 4 ≤ 25 * (5000 + 1))
-- the gap grows: at ten thousand members it is two more orders
#guard augWidthE 10000 40000 4 = 290001
#guard ¬ (augWidth 10000 4 ≤ 100 * augWidthE 10000 40000 4)
-- and the demo's own width fits the round's demand, where the level's
-- narrower allocation does not (`TgtWidenProbe`'s `12 > 8` coupling, at
-- the width parameter)
#guard augWidth 5 4 ≤ 200
#guard ¬ (augWidth 5 4 ≤ 64)

/-! ### §5.3 The residue, stated

What §5.1 delivers is a *reading*; substituting it is not this wave's
edit. `RamAugment.ImplementsW` — the landed Hoare triple, discharged by
`RamDriverAugment.implementsW` — asks its caller for
`augWidth n d ≤ W` and derives its four internal capacity facts from the
`n·n` room ("the `n · n` room pays the assembly's capacity via
`sum_augDeg_le`", that theorem's own docstring). At `n := mm` that is
`mm·mm`, and no restatement on this side can remove it: the term lives in
a read-only definition and in the walk that consumes it.

So the compacted round's width demand is `augWidth mm d ≤ W` and this
wave states it as such — `augCompact_engine`'s `hW`. The substitution of
`augWidthE` for `augWidth` is a `RamAugment`/`RamDriverAugment` edit,
listed by `g2-cost-design` §3(a) with its four consumer sites, and it is
E-width's, not E2-aug's. Everything E-width needs from this side is
above: the width, its fit, its arena-affine reading, and the compact
capacity step. -/

/-! ## §6 The contract at the compacted arena

The round's contract, restated so that nothing in it ranges over the
carrier. The subject is an `Orientation mm` — the compacted arena's own
orientation, or an augmentation of it — the ranks are read at the
members' *arena* cells `ork[Mem j]` (which is what `scatterCom` writes),
and the block structure is read on the compact prefix. There is no
`∀ v < n`.

The two clauses that are *not* moved are the ones the brief warned about:
`GreedyFratRound D D'` and the in-degree budget keep the landed guards
exactly — the round's rule is for **new-fraternal arcs only**, and
widening either clause would be false of this round on
`RamAugment`'s own three-vertex counterexample. -/

/-- **The augmentation round's contract, at the compacted arena.** -/
def AugMemPost (mm W : ℕ) (Mem : ℕ → ℕ) (D : Orientation mm) (σ' : Env) : Prop :=
  ∃ (R NO NT : ℕ → ℕ) (k m' : ℕ) (D' : Orientation mm),
    (∀ j, j < mm → (σ'.arrs "ork").getD (Mem j) 0 = R j) ∧
    σ'.vars "kmax" = k ∧
    (∀ i, i ≤ mm → (σ'.arrs "noff").getD i 0 = NO i) ∧
    σ'.arrs "ntg" = arrOf W NT ∧
    σ'.vars "mn" = m' ∧ m' ≤ W ∧
    AugStep D D' ∧ InCsr D' m' NO NT ∧
    (∀ k', LowDegreeVertices (fratGraph D) k' → k ≤ k') ∧
    GreedyFratRound D D' ∧
    (∀ d k', D.InDegLE d → LowDegreeVertices (fratGraph D) k' →
      D'.InDegLE (d + d * d + k')) ∧
    (∀ d', D'.InDegLE d' → m' ≤ mm * d')

/-- **The arena reading.** If the round's input orients the compacted
arena — which is what `ElimCompact.ElimMemPost`'s
`E.toGraph = memGraph G M hml` clause delivers at `R = 0` — then the
round's output *contains* the compacted arena: `AugStep.mono` keeps every
old arc, so every edge of `memGraph G M hml` is an edge of `D'.toGraph`.

This is the fact the phase's final elimination stands on
(`CoverDegree.exists_wreach_degree` reads `BackDegLE (D R).toGraph … k`
of the augmented graph, and the ordering it consumes has to cover the
level's own arena), now at the compacted arena and with no carrier
quantifier anywhere in it. -/
theorem augMemPost_memGraph {n mm W : ℕ} {G : SimpleGraph (Fin n)} {M Mem : ℕ → ℕ}
    {X : Set (Fin n)} {hml : MemList n mm Mem X} {D : Orientation mm} {σ' : Env}
    (h : AugMemPost mm W Mem D σ') (hD : D.toGraph = memGraph G M hml) :
    ∃ D' : Orientation mm, AugStep D D' ∧ GreedyFratRound D D' ∧
      ∀ u v : Fin mm, (memGraph G M hml).Adj u v → D'.toGraph.Adj u v := by
  obtain ⟨R, NO, NT, k, m', D', -, -, -, -, -, -, hstep, -, -, hgr, -, -⟩ := h
  refine ⟨D', hstep, hgr, fun u v huv => ?_⟩
  rcases (Orientation.toGraph_adj.1 (hD ▸ huv : D.toGraph.Adj u v)) with hin | hin
  · exact Orientation.toGraph_adj.2 (Or.inl (hstep.mono u v hin))
  · exact Orientation.toGraph_adj.2 (Or.inr (hstep.mono v u hin))

/-- **The chain, one round longer, at the compacted arena.** The driver
folds the round `R` times and collects an augmentation chain of the
*compacted* arena. `RamAugment.isAugChain_succ` is the landed step; this
is it driven by `AugMemPost`, with the extended chain named explicitly, so
that nothing about the fold's own indexing has to be assumed. -/
theorem augMemPost_chain {n mm W r : ℕ} {G : SimpleGraph (Fin n)} {M Mem : ℕ → ℕ}
    {X : Set (Fin n)} {hml : MemList n mm Mem X} {Dc : ℕ → Orientation mm} {σ' : Env}
    (hchain : IsAugChain (memGraph G M hml) Dc r)
    (hprev : ∀ i < r, GreedyFratRound (Dc i) (Dc (i + 1)))
    (h : AugMemPost mm W Mem (Dc r) σ') :
    ∃ Dc' : ℕ → Orientation mm, (∀ i, i ≤ r → Dc' i = Dc i) ∧
      IsAugChain (memGraph G M hml) Dc' (r + 1) ∧
      (∀ i < r + 1, GreedyFratRound (Dc' i) (Dc' (i + 1))) := by
  obtain ⟨R, NO, NT, k, m', D', -, -, -, -, -, -, hstep, -, -, hgr, -, -⟩ := h
  refine ⟨fun i => if i = r + 1 then D' else Dc i, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    have h1 : i ≠ r + 1 := by omega
    simp [h1]
  · have h0 : (0 : ℕ) ≠ r + 1 := by omega
    simpa [h0] using hchain.1
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · have h1 : i ≠ r + 1 := by omega
      have h2 : i ≠ r := by omega
      simpa [h1, h2] using hchain.2 i hlt
    · have h3 : i ≠ i + 1 := by omega
      simpa [h3] using hstep
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · have h1 : i ≠ r + 1 := by omega
      have h2 : i ≠ r := by omega
      simpa [h1, h2] using hprev i hlt
    · have h3 : i ≠ i + 1 := by omega
      simpa [h3] using hgr

/-! ## §7 The cost: the carrier gone, the width residual named -/

/-- The preparation budget: arena-affine, carrier-free — eleven passes,
nine of them `mm`-bounded fills and two `mm`/`kd`-bounded copies. -/
def augPrepCost (mm kd : ℕ) : ℕ := 1000 * mm + 100 * kd + 1000

/-- **The composite's cost**: the landed round's own `augCost` at the
compact carrier, plus the preparation, the carrier install and the member
scatter at a generous constant. The carrier `n` does not appear; what
does appear beside the arena's two numbers is `W`, the *allocation
width*, and §7.1 is the reading that makes that arena-affine too. -/
def augCompactCost (mm kd W : ℕ) : ℕ :=
  augCost mm W + augPrepCost mm kd + scatterCost mm + 100

/-- The cost, expanded. -/
theorem augCompactCost_eq (mm kd W : ℕ) :
    augCompactCost mm kd W = 8000 * W + 9100 * mm + 100 * kd + 9200 := by
  simp only [augCompactCost, augPrepCost, scatterCost, augCost]; ring

#guard augCompactCost 5 4 200 = 8000 * 200 + 9100 * 5 + 100 * 4 + 9200
#guard augCompactCost 5 4 200 = 1655100
-- two-sided: the constants are not slack
#guard ¬ (augCompactCost 5 4 200 = 8001 * 200 + 9100 * 5 + 100 * 4 + 9200)

/-! ### §7.1 The arena-affine reading

The composite's clock is affine in the arena's weight with a coefficient
that depends on the width parameter alone — which is
`g2-cost-design` §1's shape — **provided the allocation width itself is
arena-affine**. That proviso is `chainWidthE ≤ bsq·(n+ns+1)`, the
design's own load-bearing width fact, and §5.3 records that supplying it
is E-width's edit and not this wave's. -/
theorem augCompactCost_le_weight {mm kd W bsq w : ℕ} (hW : W ≤ bsq * (mm + kd + 1))
    (hw : mm + kd ≤ w) : augCompactCost mm kd W ≤ (8000 * bsq + 9200) * (w + 1) := by
  have h1 : W ≤ bsq * (w + 1) := le_trans hW (Nat.mul_le_mul_left bsq (by omega))
  obtain ⟨p, hp⟩ : ∃ p, bsq * (w + 1) = p := ⟨_, rfl⟩
  rw [hp] at h1
  have h2 : (8000 * bsq + 9200) * (w + 1) = 8000 * (bsq * (w + 1)) + 9200 * (w + 1) := by ring
  rw [augCompactCost_eq, h2, hp]
  omega

/-- **…and at the repaired width the proviso is discharged.** With the
allocation at `augWidthE`, the composite's clock is
`8000·(d+1)²·(w+1) + 8300·(w+1)` — affine in the compacted arena's own
weight, with the degree budget in the coefficient and the carrier
nowhere. This is the statement E-width's substitution buys, stated here
so that the substitution has a target. -/
theorem augCompactCost_le_weight_augWidthE {mm kd d w : ℕ} (hw : mm + kd ≤ w) :
    augCompactCost mm kd (augWidthE mm kd d) ≤ (8000 * (d + 1) ^ 2 + 9200) * (w + 1) :=
  augCompactCost_le_weight (augWidthE_le_weight (le_refl (mm + kd))) hw

/-! ### §7.2 The clocks, compiled

The same arena inside carriers spanning a factor of eight, and one
clock — against the landed round on the same arena, whose clock is affine
in the carrier. -/

/-- The composite's clock on the five-member arena at carrier `n`. -/
def augClock (n W : ℕ) : ℕ := (execC pB pF augCompactCom (aSt n W 5 4)).2

/-- The landed round's clock on the same arena, padded to the carrier. -/
def augCarrierClock (n W : ℕ) : ℕ := (execC pB pF augCom (augCarrierSt n W)).2

-- **carrier-blindness**: one arena, four carriers, one clock
#guard augClock 100 200 = 10126
#guard augClock 200 200 = 10126
#guard augClock 400 200 = 10126
#guard augClock 800 200 = 10126
-- and it fits the cost function at the arena's own numbers
#guard augClock 800 200 ≤ augCompactCost 5 4 200

-- **the honesty direction, on the clock**: the pin is exact
#guard ¬ (augClock 800 200 ≤ 10125)

-- **the class the wave kills**: the landed round's clock is affine in the
-- CARRIER at the fixed arena — `671·n + 5889` at three carriers spanning
-- a factor of four
#guard augCarrierClock 100 200 = 671 * 100 + 5889
#guard augCarrierClock 200 200 = 671 * 200 + 5889
#guard augCarrierClock 400 200 = 671 * 400 + 5889
-- the carrier term, measured as a difference of clocks on the same arena
#guard augCarrierClock 400 200 - augCarrierClock 200 200 = 671 * 200
-- twenty-seven times the compacted clock at carrier 400, and growing …
#guard augClock 400 200 * 27 ≤ augCarrierClock 400 200
-- … while the honesty direction says the landed clock does not fit where
-- the compacted one does
#guard ¬ (augCarrierClock 400 200 ≤ augClock 400 200 * 27)
-- the compacted clock is strictly below the landed one at every measured
-- carrier, and the gap is the whole carrier term
#guard augClock 100 200 < augCarrierClock 100 200
#guard augClock 800 200 < augCarrierClock 100 200

/-! ## §8 The bridge to the landed reading

At `mm = n` — the all-alive arena at the identity numbering, `Mem` the
identity, `"ork"` reading `"rnk"` (which is what `scatterCom` degenerates
to) — `AugMemPost` holds of exactly the states `RamAugment.AugPost` holds
of. So §6 weakens nothing; in particular the greedy clause and the
in-degree budget are the landed ones, guards included. -/

/-- **The bridge.** -/
theorem augMemPost_of_augPost {n W : ℕ} {D : Orientation n} {σ σ' : Env}
    (hpost : AugPost n W D σ σ') (hork : σ'.arrs "ork" = σ'.arrs "rnk") :
    AugMemPost n W id D σ' := by
  obtain ⟨R, NO, NT, k, m', D', hrnk, hk, hnoff, hntg, hmn, hmW, hstep, hcsr, hlow,
    hgr, hbud⟩ := hpost
  refine ⟨R, NO, NT, k, m', D', ?_, hk, ?_, hntg, hmn, hmW, hstep, hcsr, hlow, hgr, hbud,
    fun d' hd' => arcs_le_compact hcsr hd'⟩
  · intro j hj
    rw [hork, hrnk]
    simp only [id_eq]
    exact getD_arrOf R hj
  · intro i hi
    rw [hnoff, getD_arrOf _ (by omega)]

/-- The converse reading, so the bridge is an equivalence and not a
weakening in disguise: at the identity numbering the member clauses give
back everything the phase consumes of the landed contract — the next
orientation, its step, its block structure, the greedy clause and the
in-degree budget. -/
theorem augPost_answers_of_augMemPost {n W : ℕ} {D : Orientation n} {σ' : Env}
    (h : AugMemPost n W id D σ') :
    ∃ (NO NT : ℕ → ℕ) (k m' : ℕ) (D' : Orientation n),
      σ'.vars "kmax" = k ∧ σ'.vars "mn" = m' ∧ m' ≤ W ∧
      σ'.arrs "ntg" = arrOf W NT ∧
      (∀ i, i ≤ n → (σ'.arrs "noff").getD i 0 = NO i) ∧
      AugStep D D' ∧ InCsr D' m' NO NT ∧
      (∀ k', LowDegreeVertices (fratGraph D) k' → k ≤ k') ∧
      GreedyFratRound D D' ∧
      (∀ d k', D.InDegLE d → LowDegreeVertices (fratGraph D) k' →
        D'.InDegLE (d + d * d + k')) := by
  obtain ⟨R, NO, NT, k, m', D', -, hk, hnoff, hntg, hmn, hmW, hstep, hcsr, hlow, hgr,
    hbud, -⟩ := h
  exact ⟨NO, NT, k, m', D', hk, hmn, hmW, hntg, hnoff, hstep, hcsr, hlow, hgr, hbud⟩

/-! ## §9 The composite

One named obligation of this family (`AugPreps`), one obligation shared
with E2-elim (`ElimCompact.ScatterBacks` — the same program and the same
walk), one walked pass (the carrier install), and §4's transported
round. -/

/-! ### §9.0 What a discharger of `AugPreps` needs

As for `SymCompact.SymPreps`, and by the same kit: eleven applications of
`RamDriverOrder.copyKeep_spec`/`fillKeep_spec` at
`(N, Nd) = (mm+1, n+1)` (four times), `(kd, W)`, `(mm, n)` (five times)
and `(mm+1, n+1)`, with the invariant carrying the three scalars and the
two source arrays. The eleven costs sum to `121·mm + 12·kd + 142`, inside
`augPrepCost mm kd = 1000·mm + 100·kd + 1000` with room. -/

/-- The twenty-nine array clauses of the composite's entry, split off the
scalars so that the carrier install can be walked between them. -/
def AugArrsC (n mm nt W kd : ℕ) (IO IT : ℕ → ℕ) (σ : Env) : Prop :=
  (∃ g, σ.arrs "ioff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = IO i) ∧
  (∃ g, σ.arrs "itg" = arrOf W g ∧ ∀ j < kd, g j = IT j) ∧
  (∃ g, σ.arrs "doff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "dtg" = arrOf W g) ∧
  (∃ g, σ.arrs "ooff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "otg" = arrOf W g) ∧
  (∃ g, σ.arrs "ofl" = arrOf n g) ∧ (∃ g, σ.arrs "off" = arrOf (n + 1) g) ∧
  (∃ g, σ.arrs "tgt" = arrOf nt g) ∧ (∃ g, σ.arrs "ffl" = arrOf n g) ∧
  (∃ g, σ.arrs "alv" = arrOf n g) ∧ (∃ g, σ.arrs "deg" = arrOf n g) ∧
  (∃ g, σ.arrs "elm" = arrOf n g) ∧ (∃ g, σ.arrs "rnk" = arrOf n g) ∧
  (∃ g, σ.arrs "idg" = arrOf n g) ∧ (∃ g, σ.arrs "bh" = arrOf (n + 1) g) ∧
  (∃ g, σ.arrs "bv" = arrOf (n + W + 1) g) ∧ (∃ g, σ.arrs "bn" = arrOf (n + W + 1) g) ∧
  (∃ g, σ.arrs "ifl" = arrOf n g) ∧
  (∃ g, σ.arrs "noff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "nfl" = arrOf n g) ∧
  (∃ g, σ.arrs "ntg" = arrOf W g) ∧
  (∃ g, σ.arrs "stf" = arrOf n g) ∧ (∃ g, σ.arrs "sta" = arrOf n g) ∧
  (∃ g, σ.arrs "std" = arrOf n g) ∧ (∃ g, σ.arrs "ste" = arrOf n g) ∧
  (∃ g, σ.arrs "ork" = arrOf n g)

/-- **The composite's entry.** -/
def AugEntryC (n mm nt W kd : ℕ) (IO IT : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "mm" = mm ∧ σ.vars "kd" = kd ∧ mm ≤ n ∧ kd ≤ W ∧
  AugArrsC n mm nt W kd IO IT σ

/-- **Obligation E2-a/1 — the preparation walk.** `augPrepCom` moves the
compact in-lists into the round's input arrays and zeroes the nine arrays
`RamAugment.AugPreW` asks zeroed, over the compact prefix, at
`augPrepCost`, leaving the round's live-prefix entry surface and touching
no cell above the compact prefixes.

Refutable, and refuted-before-proved on data in §2.3: without the relink
the round augments the sentinel, and without the nine fills it has **no
run at all** (the D4 stuck mechanism at the sub-elimination's bucket
read).

The four word-bound antecedents are the ones a *copy* needs:
`Expr.evalB` refuses a value reaching `B`, so a copy of an over-bound cell
has no derivation and the obligation without them would be false rather
than hard. `SymCompact.prep_bounds_of_inCsr` supplies the last two from
the block structure itself, at `kd = m`. -/
def AugPreps (B n mm nt W kd : ℕ) : Prop :=
  ∀ (IO IT : ℕ → ℕ) (σ : Env), mm + 1 < B → kd < B →
    (∀ i ≤ mm, IO i < B) → (∀ j < kd, IT j < B) →
    σ.vars "n" = mm → σ.vars "mm" = mm → σ.vars "kd" = kd → mm ≤ n → kd ≤ W →
    AugArrsC n mm nt W kd IO IT σ →
    ∃ (σ' : Env) (DT : ℕ → ℕ),
      Run B augPrepCom σ σ' (augPrepCost mm kd) ∧
      σ'.vars "mm" = mm ∧ (∀ j < kd, DT j = IT j) ∧
      AugPreC mm n nt W IO DT σ' ∧
      σ'.arrs "mem" = σ.arrs "mem" ∧ (∃ g, σ'.arrs "ork" = arrOf n g)

/-- **The compacted round implements the arena contract.** The two
obligations, the walked carrier install, §4's transported round, and
nothing else. Read the cost: `augCompactCost mm kd W` — the arena's live
vertex count, its compact slot count and the allocation width, and **no
carrier term**. Read the last clause: the level's own mask above the
compact prefix comes back exactly, which is `OrderEngineProbe` §4's
read-seam dead. -/
theorem augCompact_spec {B n mm nt W kd d m : ℕ} {D : Orientation mm} {Mem IO IT : ℕ → ℕ}
    {σ : Env} (h1 : AugPreps B n mm nt W kd) (h2 : ScatterBacks B n mm Mem)
    (hin : InCsr D m IO IT) (hd : D.InDegLE d) (hmkd : m ≤ kd) (hkdW : kd ≤ W)
    (hnt : fratSlots D ≤ nt) (hW : augWidth mm d ≤ W) (hB : mm + W + 1 < B) (hnB : n < B)
    (hmn : mm ≤ n) (hIOB : ∀ i ≤ mm, IO i < B) (hITB : ∀ j < kd, IT j < B)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hmlt : ∀ j, j < mm → Mem j < n)
    (hent : AugEntryC n mm nt W kd IO IT σ) :
    ∃ σ'', Run B augCompactCore σ σ'' (augCompactCost mm kd W) ∧
      AugMemPost mm W Mem D σ'' ∧
      (σ''.arrs "alv").drop mm = (σ.arrs "alv").drop mm := by
  classical
  obtain ⟨hn0, hmm0, hkd0, -, -, harrs0⟩ := hent
  -- the carrier install
  have r1 : Run B symSetCarrier σ ((σ.setVar "kn" n).setVar "n" mm) 4 :=
    symSetCarrier_run hnB (by omega) hn0 hmm0
  set σ1 : Env := (σ.setVar "kn" n).setVar "n" mm with hσ1
  have harrs1 : AugArrsC n mm nt W kd IO IT σ1 := by simpa [hσ1] using harrs0
  have harr1 : ∀ a, σ1.arrs a = σ.arrs a := fun a => rfl
  -- the preparation
  obtain ⟨σ2, DT, r2, hmm2, hDT, hpre2, hmem2, hork2⟩ :=
    h1 IO IT σ1 (by omega) (by omega) hIOB hITB
      (by simp [hσ1]) (by simp [hσ1, hmm0]) (by simp [hσ1, hkd0]) hmn hkdW harrs1
  have hin' : InCsr D m IO DT :=
    Lax3Proofs.RamDriverAugment.inCsr_congr_prefix hin fun j hj => hDT j (by omega)
  -- the round, at the arena's carrier
  obtain ⟨τ, r3, hpost, htl⟩ :=
    augCompact_engine (d := d) hin' hd hnt (hmkd.trans hkdW) hW hB hpre2
  set σ3 : Env := padArrs τ (tailOf σ2 (augClen mm nt W)) with hσ3
  obtain ⟨R, NO, NT, k, m', D', hrnk, hk, hnoff, hntg, hmn', hmW, hstep, hcsr, hlow,
    hgr, hbud⟩ := hpost
  -- the round's answers, read on the padded store
  have hrnkP : ∀ j, j < mm → (σ3.arrs "rnk").getD j 0 = R j := by
    intro j hj
    rw [hσ3, getD_padArrs (by rw [hrnk]; simpa [arrOf] using hj), hrnk, getD_arrOf _ hj]
  have hnoffP : ∀ i, i ≤ mm → (σ3.arrs "noff").getD i 0 = NO i := by
    intro i hi
    rw [hσ3, getD_padArrs (by rw [hnoff]; simpa [arrOf] using Nat.lt_succ_of_le hi),
      hnoff, getD_arrOf _ (Nat.lt_succ_of_le hi)]
  have hntgP : σ3.arrs "ntg" = arrOf W NT := by
    obtain ⟨g, hg⟩ := hpre2.ntg
    have htz : (σ2.arrs "ntg").drop (augClen mm nt W "ntg") = [] := by
      rw [augClen_ntg, hg]
      exact List.drop_eq_nil_of_le (by simp [arrOf])
    rw [hσ3, padArrs_arrs, tailOf, htz, List.append_nil, hntg]
  -- the member data survives the round (frame, read off the syntax)
  have hmm3 : σ3.vars "mm" = mm := by rw [← hmm2]; exact r3.frame_var "mm" (by decide)
  have hmem3 : σ3.arrs "mem" = arrOf n Mem := by
    rw [← hmem, ← harr1 "mem", ← hmem2]; exact r3.frame_arr "mem" (by decide)
  have hork3 : ∃ g, σ3.arrs "ork" = arrOf n g := by
    obtain ⟨g, hg⟩ := hork2
    exact ⟨g, by rw [← hg]; exact r3.frame_arr "ork" (by decide)⟩
  -- the scatter
  obtain ⟨σ4, r4, horkS, -, -, -⟩ := h2 R σ3 hmm3 hmem3 hmlt hrnkP hork3
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono ?_,
    ⟨R, NO, NT, k, m', D', horkS, ?_, ?_, ?_, ?_, hmW, hstep, hcsr, hlow, hgr, hbud,
      fun d' hd' => arcs_le_compact hcsr hd'⟩, ?_⟩
  · rw [augCompactCost, augPrepCost, scatterCost]; omega
  · rw [← hk]; exact r4.frame_var "kmax" (by decide)
  · intro i hi; rw [r4.frame_arr "noff" (by decide)]; exact hnoffP i hi
  · rw [r4.frame_arr "ntg" (by decide)]; exact hntgP
  · rw [← hmn']; exact r4.frame_var "mn" (by decide)
  · -- the level's mask above the compact prefix, handed back
    have halvLen : augClen mm nt W "alv" ≤ (σ2.arrs "alv").length := by
      obtain ⟨g, hg⟩ := hpre2.alv
      rw [augClen_alv, hg, length_arrOf]
      omega
    have h := htl "alv" halvLen
    rw [augClen_alv] at h
    have halv2 : σ2.arrs "alv" = σ.arrs "alv" := by
      rw [r2.frame_arr "alv" (notMem_augPrepCom_warrs (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)), harr1 "alv"]
    rw [r4.frame_arr "alv" (by decide), h, halv2]

end Lax3Proofs.Refine.AugCompact
