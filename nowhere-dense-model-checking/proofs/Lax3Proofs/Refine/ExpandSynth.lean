import Lax3Proofs.Refine.ClusterSynth
import Lax3Proofs.RamDriverDescend

/-!
# ND-MC rebase P2 / satellite 2G — `expandCom`, the nested expansion,
re-derived through the refinement tower

`RamDriver.expandCom msk src dst` is one step of neighbourhood expansion
of a vertex set inside the arena a mask cuts out: a flat pass over the
carrier whose body, at a **live** vertex, loads the vertex's block and
scans it for a live marked neighbour. It is the pass both chains of a
cluster are built from — the ball of the descent (D6, `2·cap`
instances), the padded batch profiles (C2, `mb·cap`) and the colour-class
profiles (C3, `(sigL+1)·cap`) — and after satellite 2F it was the **last
underived program shape on the `C0` path** (2F/N-1).

It is derived here: abstract program, twin, bound, synthesis, and the
bridge into `RamDriverCluster.expandVal`'s vocabulary.

## 0. The reduction — what `expandCom` runs, and against what

| # | machine | shape | here |
|---|---|---|---|
| E1 | `.assign "z" (.lit 0)`; `.while (z < n)` | the carrier pass | §3 `expPass` |
| E2 | `.assign "hit" (.get src (.var "z"))` | one `aget` | §3 |
| E3 | `.ite (0 < msk[z]) (…) .skip` | the branch **containing a loop** | §3 |
| E3a | `Csr.loadRow "off" "z" "j" "jend"` | **three** IR ops (2F/D-b) | §3 |
| E3b | `Csr.scan "j" "jend" (expandSlot msk src)` | the block scan | §2 `expScan` |
| E4 | `.store dst (.var "z") (.var "hit")` | one `aset`, in **both** arms | §3 |
| E5 | `.assign "z" (.add (.var "z") (.lit 1))` | the bump | §3 |

and one slot `RamDriver.expandSlot msk src` of E3b is `w := tgt[j]`,
`if 0 < msk[w] then (if 0 < src[w] then hit := 1)`, `j := j + 1`.

The shape is `ElimSynth.degPass`'s — an outer carrier pass with an inner
row scan and an `aset` branch — with one difference that matters: **the
scan sits inside the branch**, because a dead vertex must *not* be
expanded into (`RamDriverDescend.expandVal_of_dead`), where the degree
pass scans unconditionally and only the write is guarded. That is
`ElimSynth2.fillRowF`'s shape, which tool wave T1 made translatable
(`fillSynth`), so nothing here is a matcher gap.

## 2G/D-a — the hit flag is a **count**

The machine's inner loop sets `hit := 1` and leaves it. At this layer a
scalar carried by a loop lives in one cell and the only rules that write
it are the *in-place* ones (`mopSucc`, `mopAddIn`, `mopKeep`,
`mopPred`) — there is no rule that overwrites an owned cell with the
contents of another, by design (the `mopKeep` finding: a copy moves the
accumulator out of its cell and the branch merge junks it). So
`hit := 1` is not expressible, and the two arms of the slot's branch
would have to deliver two different cells.

The pass therefore **counts** the live marked neighbours instead of
flagging them: the slot's branch is `ElimSynth.degF`'s exactly —
`mopSucc` against `mopKeep` — and the row's *own* branch turns the count
into the machine's value, `1` when the count is positive and `src[z]`
when it is not. `0 < count ↔ ∃ slot naming a live marked vertex`, which
is §4's `hitUpto_pos`, so the value written is `RamDriverCluster.expandVal`
on the nose and only the scratch cell's contents differ from the
machine's. Same deviation class as 2B′/D-a (`ls` dropped) and 2B′/D-b
(`max` without a branch): the *values the pass reports* are identical,
and §1's differential guards are what check it.

## 2G/D-b — the cost goes from quadratic to linear in `ns`

`RamDriverDescend.expandCom_spec` charges `(24·ns + 44)·n + 6`: its walk
bounds *every* vertex's block scan by the whole target array, because
`Csr.rowScan_spec` is applied at the constant `24·ns + 4`. The tower's
bound is the two-currency energy `ElimSynth`'s degree pass runs on —
`E2 (iter expRowC) (iter expC) (n − z) (off[n] − off[z])` — so the scan
turns are the **blocks, which tile the target array**, and the closed
cost is `47·n + 30·ns + 4`. Linear where the baseline is quadratic; §10
puts the two numbers side by side. This is the same touched-only
harvest 2F took on `clusterLoad` (2F/D-a), at the pass 2F left behind.

## 2G/D-c — a dead vertex still pays for its branch

`expRowC` is charged at every vertex, live or dead, and the `r • iter expC`
term is charged at the block length whether the block was scanned or
not. Both are `≤`-bounds and the dead vertex pays strictly less than
its account, so nothing is lost; it is recorded because the *shape* of
the account (one `expRowC` per carrier cell) is what makes the chain of
`2·cap` expansions `Θ(cap·(n + ns))` per cluster, and no mask can make
it sublinear. The touched-only repair for the ball chain — expanding a
*frontier* rather than the whole carrier — is a change to the machine
program and is named in §11.

## What is consumed rather than re-proved

`ElimSynth2.while_pot_le`/`step_spec` carry both loops; `ElimSynth`'s
`Shape`, `getElem!_arrOf` and the `liveUpto` idiom are the model for
§4's `hitUpto`; `RamDriverCluster.expandVal`, `expandVal_of_dead` and
**`hit_eq_expandVal`** — the whole graph mathematics of the pass — are
consumed by §9 and not restated. `RamDriverDescend`'s walk is not
touched.

## House traps observed

`omega` is blind through `Ir.Val` and through tuple projections (`show`
first); `decide +kernel` for the numerals; never `simp [Codegen.embed]`;
junk cells are digit-free and consumed in written order; loop states are
assembled with `mopPair` and never as literal tuples.
-/

namespace Lax3Proofs.Refine.ExpandSynth

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (Shape cu iter irWhile_exit get!_set res_of_le liftACost_cu)
open Lax3Proofs.Refine.ElimSynth (getElem!_arrOf)
open Lax3Proofs.Refine.ElimSynth2 (while_pot_le step_spec)
open Lax3Proofs.RamBfs (CsrGraph MAdj)
open Lax3Proofs.RamDriverCluster (expandVal)

/-! ## 1. Refute before prove

The pass as a computable function, run on an arena where the answer is
independently known, and the readings pinned. The hot spots:

* **the mask cuts the arena at *both* ends of an edge** — a dead vertex
  is not expanded into (`expandVal_of_dead`) *and* a dead neighbour does
  not expand anything. Both halves are checked, and both negative
  controls are exhibited.
* **one step is a step, not a closure** — radius `2` differs from radius
  `1` on a path, which is what makes `chainCom`'s fold observable.
* **the destination is a union, not a frontier** — a marked vertex stays
  marked (`hit := src[z]` first). The frontier reading is exhibited and
  refuted.
* **the source's value rides through** — at an unexpanded vertex the
  cell is `src[z]` and not `0`, so a source above `1` survives. This is
  what `expandVal_eq_or` needs and a "write the indicator" reading would
  break.
-/

section Twin

/-- The block scan's state: the count, the slot pointer. -/
abbrev SS : Type := ℕ × ℕ

/-- The carrier pass's state: the destination, the vertex. -/
abbrev PS : Type := List ℕ × ℕ

/-- **One slot of the block**, as a function: a live neighbour that the
source marks bumps the count (2G/D-a — the machine raises a flag). -/
def expSlotTw (tgt msk src : List ℕ) : SS → SS := fun s =>
  if 0 < msk[tgt[s.2]!]! then
    (if 0 < src[tgt[s.2]!]! then s.1 + 1 else s.1, s.2 + 1)
  else (s.1, s.2 + 1)

/-- The block scan, run. -/
def expScanTw (tgt msk src : List ℕ) (jend : ℕ) : ℕ → SS → SS
  | 0, s => s
  | fuel + 1, s =>
    if s.2 < jend then expScanTw tgt msk src jend fuel (expSlotTw tgt msk src s) else s

/-- **One vertex of the pass**: a live vertex scans its block, and the
count decides between `1` and the source's own cell. -/
def expRowTw (off tgt msk src : List ℕ) : PS → PS := fun s =>
  let c := if 0 < msk[s.2]! then
      (expScanTw tgt msk src off[s.2 + 1]! (off[s.2 + 1]! - off[s.2]!) (0, off[s.2]!)).1
    else 0
  (s.1.set s.2 (if 0 < c then 1 else src[s.2]!), s.2 + 1)

/-- The pass, run. -/
def expRunTw (n : ℕ) (off tgt msk src : List ℕ) : ℕ → PS → PS
  | 0, s => s
  | fuel + 1, s =>
    if s.2 < n then expRunTw n off tgt msk src fuel (expRowTw off tgt msk src s) else s

/-- One expansion step of a mask, from a zeroed destination. -/
def expOnce (n : ℕ) (off tgt msk src : List ℕ) : List ℕ :=
  (expRunTw n off tgt msk src (n + 1) (List.replicate n 0, 0)).1

/-! ### The arena

Six vertices in a path `0—1—2—3—4—5`, in the compressed-row form
`RamDriver.expandCom` reads. The path is what makes radius `2` differ
from radius `1`; vertex `5` is the one the masks switch off. -/

def demoOff : List ℕ := [0, 1, 3, 5, 7, 9, 10]

def demoTgt : List ℕ := [1, 0, 2, 1, 3, 2, 4, 3, 5, 4]

/-- The path's edges, written out — the reference the CSR arrays are
differentially tested against. -/
def demoEdges : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]

/-- A vertex's neighbours, read off the edge list and not off the
arena. -/
def refNbrs (v : ℕ) : List ℕ :=
  demoEdges.filterMap fun e =>
    if e.1 = v then some e.2 else if e.2 = v then some e.1 else none

-- the two readings of the arena agree, block by block
#guard (List.range 6).map (fun v =>
    ((List.range 10).filter (fun p => demoOff[v]! ≤ p ∧ p < demoOff[v + 1]!)).map
      (fun p => demoTgt[p]!))
  = (List.range 6).map refNbrs

/-- **The reference expansion**, from the edge list: a live vertex whose
live neighbour is marked becomes marked, everything else keeps its
cell. This is `RamDriverCluster.expandVal` written out. -/
def refExpand (msk src : List ℕ) : List ℕ :=
  (List.range 6).map fun z =>
    if 0 < msk[z]! ∧ (refNbrs z).any (fun y => 0 < msk[y]! ∧ 0 < src[y]!) then 1 else src[z]!

/-- The mask with every vertex alive. -/
def demoAll : List ℕ := List.replicate 6 1

/-- The mask with the path's last vertex switched off. -/
def demoMsk : List ℕ := [1, 1, 1, 1, 1, 0]

/-- The mask with the path's middle cut. -/
def demoCut : List ℕ := [1, 1, 0, 1, 1, 1]

/-- `{0}`. -/
def demoSrc : List ℕ := [1, 0, 0, 0, 0, 0]

-- **The pass is the reference**, on five mask/source pairs.
#guard expOnce 6 demoOff demoTgt demoAll demoSrc = refExpand demoAll demoSrc
#guard expOnce 6 demoOff demoTgt demoCut demoSrc = refExpand demoCut demoSrc
#guard expOnce 6 demoOff demoTgt demoCut [0, 1, 0, 0, 0, 0]
  = refExpand demoCut [0, 1, 0, 0, 0, 0]
#guard expOnce 6 demoOff demoTgt demoMsk [0, 0, 0, 0, 0, 1]
  = refExpand demoMsk [0, 0, 0, 0, 0, 1]
#guard expOnce 6 demoOff demoTgt demoMsk [0, 0, 0, 0, 1, 0]
  = refExpand demoMsk [0, 0, 0, 0, 1, 0]

-- …and the readings, written out, so the checks are not circular
#guard expOnce 6 demoOff demoTgt demoAll demoSrc = [1, 1, 0, 0, 0, 0]
#guard expOnce 6 demoOff demoTgt demoCut demoSrc = [1, 1, 0, 0, 0, 0]

/-- The chain: `r` steps, each from the last. -/
def expChain (n : ℕ) (off tgt msk : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, src => src
  | r + 1, src => expChain n off tgt msk r (expOnce n off tgt msk src)

-- **A step is a step.** On the path, radius `1`, `2` and `3` from `{0}`
-- are three different sets, so the fold of `chainCom` is observable.
#guard expChain 6 demoOff demoTgt demoAll 1 demoSrc = [1, 1, 0, 0, 0, 0]
#guard expChain 6 demoOff demoTgt demoAll 2 demoSrc = [1, 1, 1, 0, 0, 0]
#guard expChain 6 demoOff demoTgt demoAll 3 demoSrc = [1, 1, 1, 1, 0, 0]
#guard expChain 6 demoOff demoTgt demoAll 1 demoSrc
  ≠ expChain 6 demoOff demoTgt demoAll 2 demoSrc

-- **The mask is visible in *one* step**, from a source next to the cut:
-- `{1}` reaches `2` in the graph and does not in the arena.
#guard expOnce 6 demoOff demoTgt demoAll [0, 1, 0, 0, 0, 0] = [1, 1, 1, 0, 0, 0]
#guard expOnce 6 demoOff demoTgt demoCut [0, 1, 0, 0, 0, 0] = [1, 1, 0, 0, 0, 0]

-- **The mask stops the expansion.** With the path cut at `2`, radius
-- `5` is still `{0, 1}` — the ball is taken in the arena the mask cuts
-- out and not in `G`.
#guard expChain 6 demoOff demoTgt demoCut 5 demoSrc = [1, 1, 0, 0, 0, 0]
#guard expChain 6 demoOff demoTgt demoAll 5 demoSrc = [1, 1, 1, 1, 1, 1]

/-! ### Negative controls -/

-- **A dead vertex is not expanded into.** With `5` off and `4` marked,
-- the cell at `5` stays `0`; a pass that scanned dead vertices would
-- mark it.
#guard (expOnce 6 demoOff demoTgt demoMsk [0, 0, 0, 0, 1, 0])[5]! = 0
#guard (expOnce 6 demoOff demoTgt demoAll [0, 0, 0, 0, 1, 0])[5]! = 1

-- **A dead neighbour expands nothing.** With `5` off and *only* `5`
-- marked, `4` stays `0`; without the mask it would be `1`.
#guard (expOnce 6 demoOff demoTgt demoMsk [0, 0, 0, 0, 0, 1])[4]! = 0
#guard (expOnce 6 demoOff demoTgt demoAll [0, 0, 0, 0, 0, 1])[4]! = 1

-- **A dead vertex keeps its own cell.** `expandVal_of_dead`: the source
-- rides through, so a marked dead vertex stays marked.
#guard (expOnce 6 demoOff demoTgt demoMsk [0, 0, 0, 0, 0, 1])[5]! = 1

-- **The destination is a union and not a frontier.** The reading that
-- writes only the newly reached vertices differs at `0`.
#guard (List.range 6).map (fun z =>
    if 0 < demoAll[z]! ∧ demoSrc[z]! = 0 ∧
        (refNbrs z).any (fun y => 0 < demoAll[y]! ∧ 0 < demoSrc[y]!) then 1 else 0)
  ≠ expOnce 6 demoOff demoTgt demoAll demoSrc

-- **The source's value rides through.** At an unexpanded vertex the
-- cell is `src[z]` and not the indicator of `src[z] ≠ 0`, which is what
-- `expandVal_eq_or` says and a chain of expansions needs.
#guard expOnce 6 demoOff demoTgt demoAll [0, 0, 0, 0, 0, 7] = [0, 0, 0, 0, 1, 7]

-- **The scan is a prefix of a prefix.** Vertex `0`'s block is the single
-- slot `0`; a scan that ran to the array's end would see every vertex.
#guard (expScanTw demoTgt demoAll [1, 1, 1, 1, 1, 1] demoOff[1]! 10 (0, demoOff[0]!)).1 = 1
#guard (expScanTw demoTgt demoAll [1, 1, 1, 1, 1, 1] 10 10 (0, demoOff[0]!)).1 = 10

-- **An empty block counts nothing.** Vertex `5`'s block under a shorter
-- arena is empty, and the scan's `.skip` is visible.
#guard (expScanTw demoTgt demoAll demoAll 3 3 (0, 3)).1 = 0

end Twin

/-! ## 2. The block scan

`Csr.scan "j" "jend" (expandSlot msk src)` at the two components it
touches. Its body is `ElimSynth.degF`'s with the second read behind the
first's branch: the degree pass counts *live* slots, this one counts
live slots the source marks (2G/D-a). -/

section Scan

/-- The scan's guard — the block's own end, a runtime number. -/
def expBf (jend : ℕ) : SS → Bool := fun s => decide (s.2 < jend)

/-- What one slot needs in range: the pointer names a target, and the
target it names is a vertex both mask arrays cover. -/
def expSlotP (tgt msk src : List ℕ) : SS → Prop := fun s =>
  s.2 < tgt.length ∧ tgt[s.2]! < msk.length ∧ tgt[s.2]! < src.length

/-- **One slot of the block.** The nested branch is the IR's `Cond`:
`msk[w]` is read and tested, and only then is `src[w]` read at all. -/
noncomputable def expF (tgt msk src : List ℕ) : SS → NRest SS ECost := fun s =>
  bindT (mopAget tgt s.2) fun w =>
    bindT (mopAget msk w) fun mw =>
      bindT (irIf (decide (0 < mw))
          (bindT (mopAget src w) fun sw =>
            irIf (decide (0 < sw)) (mopSucc s.1) (mopKeep s.1))
          (mopKeep s.1)) fun c =>
        bindT (mopSucc s.2) fun j => mopPair c j

/-- **The block scan.** -/
noncomputable def expScan (tgt msk src : List ℕ) (jend : ℕ) (s₀ : SS) : NRest SS ECost :=
  irWhileIT (fun s => expBf jend s = true → expSlotP tgt msk src s) (expBf jend)
    (expF tgt msk src) s₀

/-- What a slot whose target is dead pays: two reads, the branch, the
kept count, the pointer, the tuple. -/
def expC0 : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.ite
  + cu Currency.add + cu Currency.add + cu Currency.skip

/-- …and a slot whose target is alive pays the source read and the
second branch on top. Both live arms cost the same — `mopKeep` is what
makes the empty `else` an `add` and not a lost cell. -/
def expC : ACost String ℕ := expC0 + (cu Currency.aget + cu Currency.ite)

theorem expF_le (tgt msk src : List ℕ) (s : SS) (h : expSlotP tgt msk src s) :
    expF tgt msk src s
      ≤ NRest.consume (NRest.returnT (expSlotTw tgt msk src s)) (liftACost expC) := by
  obtain ⟨h1, h2, h3⟩ := h
  have base : liftACost expC0 ≤ liftACost expC := by
    rw [expC, liftACost_add]; exact cost_le_add _ _
  by_cases hb : 0 < msk[tgt[s.2]!]!
  · by_cases hs : 0 < src[tgt[s.2]!]!
    · refine le_of_eq ?_
      simp only [expF, expSlotTw, mopAget_def, mopSucc_eq, mopKeep_eq, mopBinop_def,
        mopPair_def, irIf_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
        NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
        NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
        decide_eq_true_eq, if_pos hb, if_pos hs, expC, expC0, liftACost_add, liftACost_cu]
      congr 1
      ac_rfl
    · refine le_of_eq ?_
      simp only [expF, expSlotTw, mopAget_def, mopSucc_eq, mopKeep_eq, mopBinop_def,
        mopPair_def, irIf_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
        NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
        NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
        decide_eq_true_eq, if_pos hb, if_neg hs, expC, expC0, liftACost_add, liftACost_cu]
      congr 1
      ac_rfl
  · simp only [expF, expSlotTw, mopAget_def, mopSucc_eq, mopKeep_eq, mopBinop_def,
      mopPair_def, irIf_def, NRest.assert_pos h1, NRest.assert_pos h2,
      NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
      NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
      decide_eq_true_eq, if_neg hb]
    refine NRest.consume_mono le_rfl (le_trans (le_of_eq ?_) base)
    simp only [expC0, liftACost_add, liftACost_cu]
    ac_rfl

end Scan

/-! ## 3. One vertex of the carrier pass

The branch that contains the loop: a live vertex loads its block (three
IR operations, 2F/D-b) and scans it, a dead one does not, and the count
the branch delivers decides what the `aset` writes. Both arms of *both*
branches deliver the same cell — the count's for the first, the
destination array's for the second — which is what makes the merge go
through (2F/D-c's rule at a scalar and at an array). -/

section Row

/-- The carrier pass's guard. -/
def expRowBf (n : ℕ) : PS → Bool := fun s => decide (s.2 < n)

/-- What one vertex needs in range: the block structure, the
destination at its length, the counter a vertex, and the source array
as wide as the carrier. -/
def expRowP (n : ℕ) (off tgt msk src : List ℕ) : PS → Prop := fun s =>
  Shape n off tgt msk ∧ src.length = n ∧ s.1.length = n ∧ s.2 < n

/-- **One vertex of the expansion.** -/
noncomputable def expRowF (off tgt msk src : List ℕ) : PS → NRest PS ECost := fun s =>
  bindT (mopAget src s.2) fun hz =>
    bindT (mopAget msk s.2) fun mz =>
      bindT (mopConstN 0) fun c₀ =>
        bindT (irIf (decide (0 < mz))
            (bindT (mopAget off s.2) fun j0 =>
              bindT (mopBinop .add s.2 1) fun zp =>
                bindT (mopAget off zp) fun jend =>
                  bindT (mopPair c₀ j0) fun z0 =>
                    bindT (expScan tgt msk src jend z0) fun r => mopKeep r.1)
            (mopKeep c₀)) fun c =>
          bindT (irIf (decide (0 < c)) (mopAset s.1 s.2 1) (mopAset s.1 s.2 hz)) fun D =>
            bindT (mopSucc s.2) fun z => mopPair D z

/-- **The expansion pass.** -/
noncomputable def expPass (n : ℕ) (off tgt msk src : List ℕ) (s₀ : PS) : NRest PS ECost :=
  irWhileIT (fun s => expRowBf n s = true → expRowP n off tgt msk src s) (expRowBf n)
    (expRowF off tgt msk src) s₀

/-- One vertex of the pass, everything outside the block scan —
including the scan loop's own entry test, and the row load's three
operations (2F/D-b). -/
def expRowC : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.const
  + cu Currency.ite + cu Currency.aget + cu Currency.add + cu Currency.aget
  + cu Currency.skip + cu Currency.«while» + cu Currency.add + cu Currency.ite
  + cu Currency.aset + cu Currency.add + cu Currency.skip

/-- The three reads in front of the branch. -/
def expPreC : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.const

/-- **What the branch that contains the loop pays**, at a block of `m`
slots. The dead arm pays the first two summands and nothing else, which
is why the account is written with them in front. -/
def expMidC (m : ℕ) : ACost String ℕ :=
  cu Currency.ite + cu Currency.add +
    (cu Currency.aget + cu Currency.add + cu Currency.aget + cu Currency.skip +
      (m • iter expC + cu Currency.«while»))

/-- The branch that writes the cell, and the bump. -/
def expTailC : ACost String ℕ :=
  cu Currency.ite + cu Currency.aset + cu Currency.add + cu Currency.skip

theorem expRowC_split (m : ℕ) :
    expPreC + (expMidC m + expTailC) = expRowC + m • iter expC := by
  simp only [expPreC, expMidC, expTailC, expRowC]
  ac_rfl

end Row

/-! ## 4. What a block scan counts

`hitUpto` is the tower's reading of `RamDriverCluster.ScanHit`'s
existential: the slots already passed that name a live marked vertex,
counted rather than flagged (2G/D-a). `hitUpto_pos` is the equivalence
that makes the count and the flag the same test, and it is the only
place the deviation has to be argued. -/

section Count

/-- The slots of a block between two indices that name a live marked
vertex. -/
def hitUpto (tgt msk src : List ℕ) (a b : ℕ) : ℕ :=
  ((Finset.Ico a b).filter (fun p => 0 < msk[tgt[p]!]! ∧ 0 < src[tgt[p]!]!)).card

theorem hitUpto_self (tgt msk src : List ℕ) (a : ℕ) : hitUpto tgt msk src a a = 0 := by
  simp [hitUpto]

theorem hitUpto_succ (tgt msk src : List ℕ) {a b : ℕ} (h : a ≤ b) :
    hitUpto tgt msk src a (b + 1) =
      if 0 < msk[tgt[b]!]! ∧ 0 < src[tgt[b]!]! then hitUpto tgt msk src a b + 1
      else hitUpto tgt msk src a b := by
  rw [hitUpto, hitUpto, Nat.Ico_succ_right_eq_insert_Ico h, Finset.filter_insert]
  by_cases hb : 0 < msk[tgt[b]!]! ∧ 0 < src[tgt[b]!]!
  · rw [if_pos hb, if_pos hb, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg hb, if_neg hb]

/-- **The count is the flag.** -/
theorem hitUpto_pos {tgt msk src : List ℕ} {a b : ℕ} :
    0 < hitUpto tgt msk src a b ↔
      ∃ p, a ≤ p ∧ p < b ∧ 0 < msk[tgt[p]!]! ∧ 0 < src[tgt[p]!]! := by
  rw [hitUpto, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨p, hp, h₁, h₂⟩
    exact ⟨p, (Finset.mem_Ico.1 hp).1, (Finset.mem_Ico.1 hp).2, h₁, h₂⟩
  · rintro ⟨p, h₁, h₂, h₃, h₄⟩
    exact ⟨p, Finset.mem_Ico.2 ⟨h₁, h₂⟩, h₃, h₄⟩

/-- **What the branch delivers**: the block's count at a live vertex,
and nothing at a dead one — the pass does not scan a dead vertex, which
is `RamDriverDescend.expandVal_of_dead`'s content at this layer. -/
def expCnt (off tgt msk src : List ℕ) (z : ℕ) : ℕ :=
  if 0 < msk[z]! then hitUpto tgt msk src off[z]! off[z + 1]! else 0

/-- **The cell one vertex of the pass writes.** -/
def expOf (off tgt msk src : List ℕ) (z : ℕ) : ℕ :=
  if 0 < expCnt off tgt msk src z then 1 else src[z]!

/-! ### 4.1 The scan, run to the end -/

/-- The scan's invariant: the pointer inside the block, and the count
the live marked slots passed. -/
def expScanI (tgt msk src : List ℕ) (a jend : ℕ) : SS → Prop := fun s =>
  a ≤ s.2 ∧ s.2 ≤ jend ∧ s.1 = hitUpto tgt msk src a s.2

theorem expScanI_range {n : ℕ} {off tgt msk src : List ℕ} (hsh : Shape n off tgt msk)
    (hsrc : src.length = n) {a jend : ℕ} (hje : jend ≤ tgt.length) {s : SS}
    (_hI : expScanI tgt msk src a jend s) (hb : expBf jend s = true) :
    expSlotP tgt msk src s := by
  have hlt : s.2 < jend := by simpa [expBf] using hb
  have h1 : s.2 < tgt.length := by omega
  have h2 : tgt[s.2]! < n := hsh.2.2.2.2 _ h1
  exact ⟨h1, by rw [hsh.2.1]; exact h2, by rw [hsrc]; exact h2⟩

/-- The slot's nested branch, as the single test `hitUpto` counts. -/
theorem expSlotTw_eq (tgt msk src : List ℕ) (s : SS) :
    expSlotTw tgt msk src s =
      (if 0 < msk[tgt[s.2]!]! ∧ 0 < src[tgt[s.2]!]! then s.1 + 1 else s.1, s.2 + 1) := by
  simp only [expSlotTw]
  by_cases hm : 0 < msk[tgt[s.2]!]!
  · by_cases hs : 0 < src[tgt[s.2]!]!
    · rw [if_pos hm, if_pos hs, if_pos ⟨hm, hs⟩]
    · rw [if_pos hm, if_neg hs, if_neg (fun h : _ ∧ _ => hs h.2)]
  · rw [if_neg hm, if_neg (fun h : _ ∧ _ => hm h.1)]

theorem expScanI_step {tgt msk src : List ℕ} {a jend : ℕ} {s : SS}
    (hI : expScanI tgt msk src a jend s) (hb : expBf jend s = true) :
    expScanI tgt msk src a jend (expSlotTw tgt msk src s) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hlt : s.2 < jend := by simpa [expBf] using hb
  rw [expScanI, expSlotTw_eq]
  refine ⟨by omega, by omega, ?_⟩
  show (if 0 < msk[tgt[s.2]!]! ∧ 0 < src[tgt[s.2]!]! then s.1 + 1 else s.1)
    = hitUpto tgt msk src a (s.2 + 1)
  rw [hitUpto_succ tgt msk src h1, h3]

/-- **The block scan, bounded.** The turns are the block's own slots. -/
theorem expScan_le {n : ℕ} {off tgt msk src : List ℕ} (hsh : Shape n off tgt msk)
    (hsrc : src.length = n) {a jend : ℕ} (hje : jend ≤ tgt.length) :
    ∀ (fuel : ℕ) (s : SS), expScanI tgt msk src a jend s → jend - s.2 < fuel →
      expScan tgt msk src jend s
        ≤ NRest.spec (fun t => expScanI tgt msk src a jend t ∧ expBf jend t = false)
            (fun _ => liftACost ((jend - s.2) • iter expC + cu Currency.«while»)) :=
  while_pot_le (P := expSlotP tgt msk src) (V := fun s => jend - s.2)
    (Φ := fun s => (jend - s.2) • iter expC) (Φ' := fun s => (jend - (s.2 + 1)) • iter expC)
    (C := fun _ => expC) (fun _ h hb => expScanI_range hsh hsrc hje h hb)
    (fun s h hb => by
      have hlt : s.2 < jend := by simpa [expBf] using hb
      exact step_spec (s := s) (x := expSlotTw tgt msk src s) (C := fun _ => expC)
        (Φ := fun s => (jend - s.2) • iter expC)
        (Φ' := fun s => (jend - (s.2 + 1)) • iter expC)
        (V := fun s => jend - s.2)
        (expF_le tgt msk src s (expScanI_range hsh hsrc hje h hb)) (expScanI_step h hb)
        (by rw [expSlotTw_eq]; show jend - (s.2 + 1) < jend - s.2; omega)
        (le_of_eq (by rw [expSlotTw_eq])))
    (fun s _ hb => by
      have hlt : s.2 < jend := by simpa [expBf] using hb
      show iter expC + (jend - (s.2 + 1)) • iter expC ≤ (jend - s.2) • iter expC
      rw [show jend - s.2 = (jend - (s.2 + 1)) + 1 by omega, succ_nsmul]
      exact le_of_eq (by ac_rfl))

end Count

/-! ## 5. One vertex, walked

The branch that contains the loop, bounded in its two arms, and the
branch that writes the cell after it. Both are `≤`-bounds at the *live*
vertex's account: a dead vertex pays neither the row load nor the scan
(2G/D-c). -/

section RowWalk

open Lax3Proofs.Refine.ClusterSynth (mopAget_le)

/-- A literal into a junk cell, bounded. -/
theorem mopConstN_le (m : ℕ) :
    mopConstN m ≤ NRest.spec (fun u => u = m) (fun _ => liftACost (cu Currency.const)) := by
  rw [mopConstN_def, liftACost_cu]
  exact consume_returnT_le_spec rfl le_rfl

/-- The row's account, in the nesting the composition produces it in. -/
def expRowCn (m : ℕ) : ACost String ℕ :=
  cu Currency.aget + (cu Currency.aget + (cu Currency.const + (expMidC m + expTailC)))

theorem expRowCn_eq (m : ℕ) : expRowCn m = expRowC + m • iter expC := by
  simp only [expRowCn, expMidC, expTailC, expRowC]
  ac_rfl

theorem expRowF_le {n : ℕ} {off tgt msk src : List ℕ} (hsh : Shape n off tgt msk)
    (hsrc : src.length = n) (s : PS) (hlen : s.1.length = n) (hi : s.2 < n) :
    expRowF off tgt msk src s
      ≤ NRest.spec
          (fun t : PS => t.1.length = n ∧ t.2 = s.2 + 1 ∧
            (∀ v, v ≠ s.2 → t.1[v]! = s.1[v]!) ∧ t.1[s.2]! = expOf off tgt msk src s.2)
          (fun _ => liftACost (expRowC + (off[s.2 + 1]! - off[s.2]!) • iter expC)) := by
  have holen : off.length = n + 1 := hsh.1
  have hmlen : msk.length = n := hsh.2.1
  have h0 : s.2 < off.length := by omega
  have h1 : s.2 + 1 < off.length := by omega
  have hmono : off[s.2]! ≤ off[s.2 + 1]! := hsh.2.2.1 _ hi
  have hrow : off[s.2 + 1]! ≤ tgt.length := hsh.row_le hi
  have hsz : s.2 < src.length := by omega
  have hmz : s.2 < msk.length := by omega
  have hdz : s.2 < s.1.length := by omega
  -- the branch that contains the loop
  have hmid : irIf (decide (0 < msk[s.2]!))
        (bindT (mopAget off s.2) fun j0 =>
          bindT (mopBinop .add s.2 1) fun zp =>
            bindT (mopAget off zp) fun jend =>
              bindT (mopPair (0 : ℕ) j0) fun z0 =>
                bindT (expScan tgt msk src jend z0) fun r => mopKeep r.1)
        (mopKeep (0 : ℕ))
      ≤ NRest.spec (fun c : ℕ => c = expCnt off tgt msk src s.2)
          (fun _ => liftACost (expMidC (off[s.2 + 1]! - off[s.2]!))) := by
    by_cases hm : 0 < msk[s.2]!
    · have hstart : expScanI tgt msk src off[s.2]! off[s.2 + 1]! (0, off[s.2]!) :=
        ⟨le_rfl, hmono, (hitUpto_self tgt msk src _).symm⟩
      have hscan := expScan_le hsh hsrc hrow (off[s.2 + 1]! - off[s.2]! + 1) _ hstart (by omega)
      have hkeep : ∀ r : SS,
          (expScanI tgt msk src off[s.2]! off[s.2 + 1]! r ∧ expBf off[s.2 + 1]! r = false) →
            mopKeep r.1 ≤ NRest.spec (fun c : ℕ => c = expCnt off tgt msk src s.2)
              (fun _ => liftACost (cu Currency.add)) := by
        rintro r ⟨⟨hr1, hr2, hr3⟩, hbf⟩
        have hend : r.2 = off[s.2 + 1]! := by
          have : ¬ r.2 < off[s.2 + 1]! := by simpa [expBf] using hbf
          omega
        rw [mopKeep_eq, mopBinop_def, liftACost_cu]
        refine consume_returnT_le_spec ?_ le_rfl
        show Lax13Proofs.Imp.Bop.apply .add r.1 0 = _
        rw [Lax13Proofs.Imp.Bop.apply_add, expCnt, if_pos hm, hr3, hend, Nat.add_zero]
      simp only [irIf_def, decide_eq_true_eq, if_pos hm, mopAget_def, mopBinop_def,
        mopPair_def, NRest.assert_pos h0, Lax13Proofs.Imp.Bop.apply_add, NRest.assert_pos h1,
        NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
        NRest.consume_consume, binopCurrency_add, NRest.bindT_assoc_acost]
      refine le_trans (NRest.consume_mono
        (le_trans (NRest.bindT_mono hscan fun _ => le_rfl)
          (bindT_spec_le _ _ _ _ _ hkeep)) le_rfl) (le_of_eq ?_)
      rw [Sepref.consume_spec]
      refine congrArg (NRest.spec _) (funext fun _ => ?_)
      simp only [expMidC, iter, liftACost_add, liftACost_nsmul, liftACost_cu]
      ac_rfl
    · simp only [irIf_def, decide_eq_true_eq, if_neg hm, mopKeep_eq, mopBinop_def,
        NRest.consume_consume]
      refine consume_returnT_le_spec ?_ ?_
      · show Lax13Proofs.Imp.Bop.apply .add 0 0 = _
        rw [Lax13Proofs.Imp.Bop.apply_add, expCnt, if_neg hm]
      · rw [expMidC, liftACost_add, liftACost_add]
        refine le_trans (le_of_eq ?_) (cost_le_add _ _)
        simp only [binopCurrency_add, liftACost_cu]
  -- the branch that writes the cell, and the bump
  have htail :
      NRest.bindT (irIf (decide (0 < expCnt off tgt msk src s.2))
            (mopAset s.1 s.2 1) (mopAset s.1 s.2 src[s.2]!))
          (fun D => NRest.bindT (mopSucc s.2) fun z => mopPair D z)
        ≤ NRest.spec
            (fun t : PS => t.1.length = n ∧ t.2 = s.2 + 1 ∧
              (∀ v, v ≠ s.2 → t.1[v]! = s.1[v]!) ∧ t.1[s.2]! = expOf off tgt msk src s.2)
            (fun _ => liftACost expTailC) := by
    by_cases hc : 0 < expCnt off tgt msk src s.2
    · simp only [irIf_def, decide_eq_true_eq, if_pos hc]
      simp only [mopAset_def, mopSucc_eq, mopBinop_def, mopPair_def,
        NRest.assert_pos hdz, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
        Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add]
      refine consume_returnT_le_spec ⟨by simp [hlen], rfl, ?_, ?_⟩ ?_
      · intro v hv
        show (s.1.set s.2 1)[v]! = _
        rw [get!_set _ _ _ _ hdz, if_neg hv]
      · show (s.1.set s.2 1)[s.2]! = _
        rw [get!_set _ _ _ _ hdz, if_pos rfl, expOf, if_pos hc]
      · simp only [expTailC, liftACost_add, liftACost_cu]
        exact le_of_eq (by ac_rfl)
    · simp only [irIf_def, decide_eq_true_eq, if_neg hc]
      simp only [mopAset_def, mopSucc_eq, mopBinop_def, mopPair_def,
        NRest.assert_pos hdz, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
        Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add]
      refine consume_returnT_le_spec ⟨by simp [hlen], rfl, ?_, ?_⟩ ?_
      · intro v hv
        show (s.1.set s.2 src[s.2]!)[v]! = _
        rw [get!_set _ _ _ _ hdz, if_neg hv]
      · show (s.1.set s.2 src[s.2]!)[s.2]! = _
        rw [get!_set _ _ _ _ hdz, if_pos rfl, expOf, if_neg hc]
      · simp only [expTailC, liftACost_add, liftACost_cu]
        exact le_of_eq (by ac_rfl)
  -- assemble
  rw [← expRowCn_eq (off[s.2 + 1]! - off[s.2]!), expRowCn, expRowF]
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopAget_le hsz) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro hz rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopAget_le hmz) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro mz rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopConstN_le 0) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro c₀ rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono hmid (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro c rfl
  exact htail

end RowWalk

/-! ## 6. The pass

The outer loop's energy is two-currency, as the degree pass's is: one
`expRowC` per vertex still to visit, one `expC` per slot still to scan.
The second is bounded because the blocks **tile** the target array, and
that is the whole of 2G/D-b. -/

section PassWalk

/-- The pass's invariant: the destination at its length, the counter a
carrier index, and every cell below it written. -/
def expI (n : ℕ) (off tgt msk src : List ℕ) : PS → Prop := fun s =>
  s.1.length = n ∧ s.2 ≤ n ∧ ∀ v, v < s.2 → s.1[v]! = expOf off tgt msk src v

theorem expPass_le {n : ℕ} {off tgt msk src : List ℕ} (hsh : Shape n off tgt msk)
    (hsrc : src.length = n) :
    ∀ (fuel : ℕ) (s : PS), expI n off tgt msk src s → n - s.2 < fuel →
      expPass n off tgt msk src s
        ≤ NRest.spec (fun t => expI n off tgt msk src t ∧ expRowBf n t = false)
            (fun _ => liftACost (E2 (iter expRowC) (iter expC) (n - s.2)
              (off[n]! - off[s.2]!) + cu Currency.«while»)) :=
  while_pot_le (P := expRowP n off tgt msk src) (V := fun s => n - s.2)
    (Φ := fun s => E2 (iter expRowC) (iter expC) (n - s.2) (off[n]! - off[s.2]!))
    (Φ' := fun s => E2 (iter expRowC) (iter expC) (n - (s.2 + 1)) (off[n]! - off[s.2 + 1]!))
    (C := fun s => expRowC + (off[s.2 + 1]! - off[s.2]!) • iter expC)
    (fun s h hb => ⟨hsh, hsrc, h.1, by simpa [expRowBf] using hb⟩)
    (fun s h hb => by
      have hi : s.2 < n := by simpa [expRowBf] using hb
      refine le_trans (expRowF_le hsh hsrc s h.1 hi) (spec_mono ?_ (fun _ _ => le_rfl))
      rintro t ⟨htlen, hti, htkeep, htnew⟩
      refine ⟨⟨htlen, by omega, fun v hv => ?_⟩, ?_, ?_⟩
      · rw [hti] at hv
        rcases eq_or_ne v s.2 with rfl | hne
        · exact htnew
        · rw [htkeep v hne]; exact h.2.2 v (by omega)
      · show n - t.2 < n - s.2
        rw [hti]; omega
      · show E2 (iter expRowC) (iter expC) (n - t.2) (off[n]! - off[t.2]!) ≤ _
        rw [hti])
    (fun s h hb => by
      have hi : s.2 < n := by simpa [expRowBf] using hb
      have hmono : off[s.2]! ≤ off[s.2 + 1]! := hsh.2.2.1 _ hi
      have htop : off[s.2 + 1]! ≤ off[n]! := hsh.mono' (by omega) le_rfl
      show iter (expRowC + (off[s.2 + 1]! - off[s.2]!) • iter expC)
        + E2 (iter expRowC) (iter expC) (n - (s.2 + 1)) (off[n]! - off[s.2 + 1]!)
        ≤ E2 (iter expRowC) (iter expC) (n - s.2) (off[n]! - off[s.2]!)
      rw [show n - s.2 = (n - (s.2 + 1)) + 1 by omega,
        show off[n]! - off[s.2]!
          = (off[n]! - off[s.2 + 1]!) + (off[s.2 + 1]! - off[s.2]!) by omega,
        E2_split]
      exact le_of_eq (by simp only [iter]; ac_rfl))

/-- **One expansion pass, discharged.** Every cell of the carrier holds
`expOf`, and the cost is the carrier's cells and the target array's
slots — never their product (2G/D-b). -/
theorem expPass_spec {n : ℕ} {off tgt msk src A₀ : List ℕ} (hsh : Shape n off tgt msk)
    (hsrc : src.length = n) (hA : A₀.length = n) :
    expPass n off tgt msk src (A₀, 0)
      ≤ NRest.spec
          (fun t : PS => t.1.length = n ∧ ∀ v, v < n → t.1[v]! = expOf off tgt msk src v)
          (fun _ => liftACost (E2 (iter expRowC) (iter expC) n (off[n]! - off[0]!)
            + cu Currency.«while»)) := by
  refine le_trans (expPass_le hsh hsrc (n + 1) (A₀, 0)
    ⟨hA, Nat.zero_le n, fun v hv => absurd hv (by omega)⟩ (by omega))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, t2, t3⟩, hbf⟩
  have hti : t.2 = n := by
    have : ¬ t.2 < n := by simpa [expRowBf] using hbf
    omega
  exact ⟨t1, fun v hv => t3 v (by omega)⟩

end PassWalk

/-! ## 7. The syntheses -/

section Synth

set_option maxHeartbeats 1000000 in
sepref_synth expScanSynth (tgt msk src : List ℕ) (jend c₀ j₀ : ℕ) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn) (c₀, j₀) ("hct", "j") ∗
      hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn msk "msk" ∗
      hnCtxt arrayAssn src "src" ∗ hnCtxt natAssn jend "jend" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "w" ∗ junkCell "mw" ∗ junkCell "sw")
    _ _ ("hct", "j") (natAssn ×ₐ natAssn)
    (expScan tgt msk src jend (c₀, j₀))

set_option maxHeartbeats 1000000 in
sepref_synth expSynth (n : ℕ) (off tgt msk src : List ℕ) (dst₀ : List ℕ) (z₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (dst₀, z₀) ("dst", "z") ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn msk "msk" ∗ hnCtxt arrayAssn src "src" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "hz" ∗ junkCell "mz" ∗ junkCell "hct" ∗ junkCell "j" ∗ junkCell "zp" ∗
      junkCell "jend" ∗ junkCell "w" ∗ junkCell "mw" ∗ junkCell "sw")
    _ _ ("dst", "z") (arrayAssn ×ₐ natAssn)
    (expPass n off tgt msk src (dst₀, z₀))

-- **The block scan, pinned**: `RamDriver.expandSlot` instruction for
-- instruction, save 2G/D-a — the flag `hit := 1` is the count
-- `hct := hct + one`, and the empty `else` is the in-place
-- `hct := hct + zero` that `mopKeep` forces (`ElimSynth`'s degree scan
-- at the same two arms).
#guard expScanSynth_impl =
  Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
    ((Com.aget "w" "tgt" "j").seq
      ((Com.aget "mw" "msk" "w").seq
        ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "mw"))
              ((Com.aget "sw" "src" "w").seq
                (Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "sw"))
                  (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "one")
                  (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")))
              (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")).seq
          ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq Com.skip))))

-- **`RamDriver.expandCom`, pinned** — the carrier pass, the branch
-- containing the row load and the block scan, and the two-armed store.
-- The row load is three instructions (2F/D-b: `aget`, `add`, `aget`),
-- the count is reset per vertex by `Com.const` where the machine's
-- `hit := src[z]` is an `aget`, and the store's two arms write `one`
-- and the vertex's own `src` cell.
#guard expSynth_impl =
  Com.while (Cond.lt (Operand.cell "z") (Operand.cell "n"))
    ((Com.aget "hz" "src" "z").seq
      ((Com.aget "mz" "msk" "z").seq
        ((Com.const "hct" 0).seq
          ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "mz"))
                ((Com.aget "j" "off" "z").seq
                  ((Com.binop Lax13Proofs.Imp.Bop.add "zp" "z" "one").seq
                    ((Com.aget "jend" "off" "zp").seq
                      (Com.skip.seq
                        ((Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
                              ((Com.aget "w" "tgt" "j").seq
                                ((Com.aget "mw" "msk" "w").seq
                                  ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "mw"))
                                        ((Com.aget "sw" "src" "w").seq
                                          (Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "sw"))
                                            (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "one")
                                            (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")))
                                        (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")).seq
                                    ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq
                                      Com.skip))))).seq
                          (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero"))))))
                (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")).seq
            ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "hct"))
                  (Com.aset "dst" "z" "one") (Com.aset "dst" "z" "hz")).seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "z" "z" "one").seq Com.skip))))))

/-! ### Negative controls on the pins -/

-- **The scan is inside the branch.** A program that scanned the block
-- of a dead vertex too — the degree pass's shape — is a different one,
-- and §1's guard on the dead vertex's cell is what refutes it.
#guard expSynth_impl ≠
  Com.while (Cond.lt (Operand.cell "z") (Operand.cell "n"))
    ((Com.aget "hz" "src" "z").seq
      ((Com.aget "mz" "msk" "z").seq
        ((Com.const "hct" 0).seq
          (((Com.aget "j" "off" "z").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "zp" "z" "one").seq
                  ((Com.aget "jend" "off" "zp").seq
                    (Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
                      ((Com.aget "w" "tgt" "j").seq
                        ((Com.aget "mw" "msk" "w").seq
                          ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "mw"))
                                ((Com.aget "sw" "src" "w").seq
                                  (Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "sw"))
                                    (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "one")
                                    (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")))
                                (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")).seq
                            ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq
                              Com.skip)))))))).seq
            ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "hct"))
                  (Com.aset "dst" "z" "one") (Com.aset "dst" "z" "hz")).seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "z" "z" "one").seq Com.skip))))))

-- **The neighbour's mask is read.** The scan that tested only the
-- source — the reading that expands in `G` and not in the arena the
-- mask cuts out — drops one `aget` and one branch.
#guard expScanSynth_impl ≠
  Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
    ((Com.aget "w" "tgt" "j").seq
      ((Com.aget "sw" "src" "w").seq
        ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "sw"))
              (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "one")
              (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")).seq
          ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq Com.skip))))

-- **The unexpanded cell is the source's and not zero.** The `else` arm
-- of the store writes `hz`, and a program writing `zero` there is the
-- frontier reading §1 refutes.
#guard expSynth_impl ≠
  Com.while (Cond.lt (Operand.cell "z") (Operand.cell "n"))
    ((Com.aget "hz" "src" "z").seq
      ((Com.aget "mz" "msk" "z").seq
        ((Com.const "hct" 0).seq
          ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "mz"))
                ((Com.aget "j" "off" "z").seq
                  ((Com.binop Lax13Proofs.Imp.Bop.add "zp" "z" "one").seq
                    ((Com.aget "jend" "off" "zp").seq
                      (Com.skip.seq
                        ((Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
                              ((Com.aget "w" "tgt" "j").seq
                                ((Com.aget "mw" "msk" "w").seq
                                  ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "mw"))
                                        ((Com.aget "sw" "src" "w").seq
                                          (Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "sw"))
                                            (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "one")
                                            (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")))
                                        (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")).seq
                                    ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq
                                      Com.skip))))).seq
                          (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero"))))))
                (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")).seq
            ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "hct"))
                  (Com.aset "dst" "z" "one") (Com.aset "dst" "z" "zero")).seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "z" "z" "one").seq Com.skip))))))

/-- The block scan's synthesis with the frame the tool computed left
existential — the form a consumer composes with. -/
theorem expScanSynth' (tgt msk src : List ℕ) (jend c₀ j₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (natAssn ×ₐ natAssn) (c₀, j₀) ("hct", "j") ∗
        hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn msk "msk" ∗
        hnCtxt arrayAssn src "src" ∗ hnCtxt natAssn jend "jend" ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "w" ∗ junkCell "mw" ∗ junkCell "sw")
      expScanSynth_impl Γ' ("hct", "j") (natAssn ×ₐ natAssn)
      (expScan tgt msk src jend (c₀, j₀)) :=
  ⟨_, expScanSynth tgt msk src jend c₀ j₀⟩

/-- **The expansion pass's synthesis**, with the tool's frame left
existential. -/
theorem expSynth' (n : ℕ) (off tgt msk src dst₀ : List ℕ) (z₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (dst₀, z₀) ("dst", "z") ∗
        hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt arrayAssn msk "msk" ∗ hnCtxt arrayAssn src "src" ∗
        hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "hz" ∗ junkCell "mz" ∗ junkCell "hct" ∗ junkCell "j" ∗ junkCell "zp" ∗
        junkCell "jend" ∗ junkCell "w" ∗ junkCell "mw" ∗ junkCell "sw")
      expSynth_impl Γ' ("dst", "z") (arrayAssn ×ₐ natAssn)
      (expPass n off tgt msk src (dst₀, z₀)) :=
  ⟨_, expSynth n off tgt msk src dst₀ z₀⟩

end Synth

/-! ## 8. Gate — the *synthesized* program, run

`Ir/Semantics.lean`'s evaluator on §7's `Com`, at §1's arena. Every
answer is the twin's answer, and the twins' answers are the edge list's. -/

section Gate

/-- The pass's entry store. The count cell enters at the caller's junk —
the program's own `Com.const` is what zeroes it, once per vertex, and
the readings below are what says so. -/
def pState (msk src A : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("z", 0), ("n", 6), ("one", 1), ("zero", 0), ("hz", 0), ("mz", 0),
      ("hct", 5), ("j", 0), ("zp", 0), ("jend", 0), ("w", 0), ("mw", 0), ("sw", 0)]
    [("dst", A), ("off", demoOff), ("tgt", demoTgt), ("msk", msk), ("src", src)]

/-- What the synthesized pass leaves in the destination. -/
def pRun (msk src A : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 expSynth_impl (pState msk src A)).bind fun p => p.1.arrs "dst"

-- **The program is the reference**, on the four mask/source pairs of §1
-- and out of a destination holding the caller's junk.
#guard pRun demoAll demoSrc (List.replicate 6 9) = some (refExpand demoAll demoSrc)
#guard pRun demoCut demoSrc (List.replicate 6 9) = some (refExpand demoCut demoSrc)
#guard pRun demoMsk [0, 0, 0, 0, 0, 1] (List.replicate 6 9)
  = some (refExpand demoMsk [0, 0, 0, 0, 0, 1])
#guard pRun demoMsk [0, 0, 0, 0, 1, 0] (List.replicate 6 9)
  = some (refExpand demoMsk [0, 0, 0, 0, 1, 0])

-- **The program is the twin**, cell for cell, at the same entry array.
#guard pRun demoAll demoSrc (List.replicate 6 9)
  = some (expRunTw 6 demoOff demoTgt demoAll demoSrc 7 (List.replicate 6 9, 0)).1
#guard pRun demoMsk [0, 0, 0, 0, 0, 7] (List.replicate 6 9)
  = some (expRunTw 6 demoOff demoTgt demoMsk [0, 0, 0, 0, 0, 7] 7 (List.replicate 6 9, 0)).1

-- **The count is reset per vertex.** The entry store pins `"hct"` at
-- `5`; if the `Com.const` were not there every cell would come out `1`.
#guard pRun demoAll demoSrc (List.replicate 6 9) = some [1, 1, 0, 0, 0, 0]
#guard pRun demoAll demoSrc (List.replicate 6 9) ≠ some (List.replicate 6 1)

/-! ### Negative controls -/

-- **The mask is load-bearing in the evaluator too.** From `{1}` one
-- step reaches `2` in the graph and does not in the arena the cut mask
-- leaves.
/--
error: Expression
  decide (pRun demoCut [0, 1, 0, 0, 0, 0] (List.replicate 6 9) = pRun demoAll [0, 1, 0, 0, 0, 0] (List.replicate 6 9))
did not evaluate to `true`
-/
#guard_msgs in
#guard pRun demoCut [0, 1, 0, 0, 0, 0] (List.replicate 6 9)
  = pRun demoAll [0, 1, 0, 0, 0, 0] (List.replicate 6 9)

-- **One step is not two.** The synthesized program run once is the
-- radius-`1` set, and the radius-`2` set is a different answer.
/--
error: Expression
  decide (pRun demoAll demoSrc (List.replicate 6 9) = some (expChain 6 demoOff demoTgt demoAll 2 demoSrc))
did not evaluate to `true`
-/
#guard_msgs in
#guard pRun demoAll demoSrc (List.replicate 6 9)
  = some (expChain 6 demoOff demoTgt demoAll 2 demoSrc)

end Gate

/-! ## 9. The bridge into `RamDriverCluster`'s vocabulary

What the tower's pass leaves is `expOf`, a count over lists; what the
driver stack speaks about is `RamDriverCluster.expandVal`, a condition on
the arena `MAdj`. They are the same number, and the bridge is proved once
here — `hit_eq_expandVal` is the graph half and is *consumed*, exactly as
`ElimSynth` §5 consumes `card_liveSlots`. -/

section Bridge

open Lax13Proofs.Reasoning (arrOf)
open Lax3Proofs.RamDriverDescend (expandVal_of_dead)
open Lax3Proofs.RamDriverCluster (hit_eq_expandVal)

/-- The block structure, as the tower reads it. -/
theorem shape_of_csrGraph {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T Msk : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) :
    Shape n (arrOf (n + 1) O) (arrOf ns T) (arrOf n Msk) := by
  refine ⟨by simp [arrOf], by simp [arrOf], fun i hi => ?_, ?_, fun j hj => ?_⟩
  · rw [getElem!_arrOf O (by omega), getElem!_arrOf O (by omega)]
    exact hcsr.mono i hi
  · rw [getElem!_arrOf O (by omega), hcsr.last]
    simp [arrOf]
  · have hjs : j < ns := by simpa [arrOf] using hj
    rw [getElem!_arrOf T hjs]
    exact hcsr.target_lt j hjs

/-- **The tower's cell is the driver's.** -/
theorem expOf_eq_expandVal {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T Msk Src : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) {z : ℕ} (hz : z < n) :
    expOf (arrOf (n + 1) O) (arrOf ns T) (arrOf n Msk) (arrOf n Src) z
      = expandVal G Msk Src z := by
  have hMz : (arrOf n Msk)[z]! = Msk z := getElem!_arrOf Msk hz
  have hSz : (arrOf n Src)[z]! = Src z := getElem!_arrOf Src hz
  by_cases hm : Msk z = 0
  · have hcnt : expCnt (arrOf (n + 1) O) (arrOf ns T) (arrOf n Msk) (arrOf n Src) z = 0 := by
      rw [expCnt, if_neg (show ¬ 0 < (arrOf n Msk)[z]! by rw [hMz, hm]; omega)]
    rw [expOf, hcnt, if_neg (by omega), hSz, expandVal_of_dead hm]
  · have hOz : (arrOf (n + 1) O)[z]! = O z := getElem!_arrOf O (by omega)
    have hOz1 : (arrOf (n + 1) O)[z + 1]! = O (z + 1) := getElem!_arrOf O (by omega)
    have hrow : O (z + 1) ≤ ns := hcsr.le_ns (by omega)
    have hcnt : expCnt (arrOf (n + 1) O) (arrOf ns T) (arrOf n Msk) (arrOf n Src) z
        = hitUpto (arrOf ns T) (arrOf n Msk) (arrOf n Src) (O z) (O (z + 1)) := by
      rw [expCnt, if_pos (show 0 < (arrOf n Msk)[z]! by rw [hMz]; omega), hOz, hOz1]
    rw [expOf, hcnt, hSz, ← hit_eq_expandVal hcsr hz hm]
    congr 1
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨p, h₁, h₂, h₃, h₄⟩ := hitUpto_pos.1 h
      have hps : p < ns := by omega
      have hTp : T p < n := hcsr.target_lt p hps
      rw [getElem!_arrOf T hps, getElem!_arrOf Msk hTp] at h₃
      rw [getElem!_arrOf T hps, getElem!_arrOf Src hTp] at h₄
      exact ⟨p, h₁, h₂, by omega, by omega⟩
    · obtain ⟨p, h₁, h₂, h₃, h₄⟩ := h
      have hps : p < ns := by omega
      have hTp : T p < n := hcsr.target_lt p hps
      refine hitUpto_pos.2 ⟨p, h₁, h₂, ?_, ?_⟩
      · rw [getElem!_arrOf T hps, getElem!_arrOf Msk hTp]; omega
      · rw [getElem!_arrOf T hps, getElem!_arrOf Src hTp]; omega

/-- **The pass, in `RamDriverDescend.expandCom_spec`'s vocabulary.** The
destination holds `RamDriverCluster.expandVal` at every vertex of the
carrier — so, by `markSet_expandVal`, it marks one neighbourhood step of
what the source marks — and the cost is `n` carrier cells and `ns`
slots, never their product. -/
theorem expPass_expandVal {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T Msk Src : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) {A₀ : List ℕ} (hA : A₀.length = n) :
    expPass n (arrOf (n + 1) O) (arrOf ns T) (arrOf n Msk) (arrOf n Src) (A₀, 0)
      ≤ NRest.spec
          (fun t : PS => t.1.length = n ∧ ∀ v, v < n → t.1[v]! = expandVal G Msk Src v)
          (fun _ => liftACost (E2 (iter expRowC) (iter expC) n ns + cu Currency.«while»)) := by
  have h := expPass_spec (off := arrOf (n + 1) O) (tgt := arrOf ns T) (msk := arrOf n Msk)
    (src := arrOf n Src) (shape_of_csrGraph hcsr) (by simp [arrOf]) hA
  rw [getElem!_arrOf O (show n < n + 1 by omega), getElem!_arrOf O (show 0 < n + 1 by omega),
    hcsr.last, hcsr.zero, Nat.sub_zero] at h
  refine le_trans h (spec_mono ?_ (fun _ _ => le_rfl))
  rintro t ⟨t1, t2⟩
  exact ⟨t1, fun v hv => by rw [t2 v hv]; exact expOf_eq_expandVal hcsr hv⟩

end Bridge

/-! ## 10. The cost, against the hand-walked pass

`RamDriverDescend.expandCom_spec` proves the machine program at
`(24·ns + 44)·n + 6`. The tower's is `47·n + 30·ns + 4`.

| | hand-walked | tower |
|---|---|---|
| per carrier cell | `24·ns + 44` | `47` |
| per block slot | — (charged `ns` per cell) | `30` |
| whole pass | `(24·ns + 44)·n + 6` | `47·n + 30·ns + 4` |

The per-cell and per-slot excesses are 2E/D-b's standing deviation (a
cell expression of `k` reads is `k` `aget`s plus one operation per
connective, and a loop state of `k` components pays `k − 1` `skip`s per
turn, 2B′/F-a). **The `n·ns` is not**: the baseline's walk bounds every
vertex's block by the whole target array, and the tower's energy charges
the block's own length, so what was quadratic per pass is linear
(2G/D-b). Over a chain of `2·cap` expansions the difference is
`Θ(cap·n·ns)` against `Θ(cap·(n + ns))`. -/

section Cash

theorem cash_expC : Codegen.cash (iter expC) = 30 := by decide +kernel

theorem cash_expRowC : Codegen.cash (iter expRowC) = 47 := by decide +kernel

theorem cash_while : Codegen.cash (cu Currency.«while») = 4 := by decide +kernel

/-- The pass's cost in IMP+ time units. -/
def expK (n ns : ℕ) : ℕ := 47 * n + 30 * ns + 4

theorem cash_expBudget (n ns : ℕ) :
    Codegen.cash (E2 (iter expRowC) (iter expC) n ns + cu Currency.«while») = expK n ns := by
  rw [E2, Codegen.cash_add, Codegen.cash_add, BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul,
    cash_expRowC, cash_expC, cash_while, expK]
  ring

-- the two figures side by side at §1's arena — six vertices, ten slots
#guard expK 6 10 = 586
#guard (24 * 10 + 44) * 6 + 6 = 1710

-- …and at ten times the arena, where the shape of the difference shows
#guard expK 60 100 = 5824
#guard (24 * 100 + 44) * 60 + 6 = 146646

end Cash

/-! ## 11. Debts, named

**2G/N-1 — the chain is not composed.** `RamDriver.chainCom` is
`foldRange (expandCom msk (nm a) (nm (a+1))) r`, and what is derived
here is one turn of that fold. Composing `r` of them at this layer is a
*name* problem and not a program problem: consecutive stages must be
distinct cells (`RamDriver.ballStage` alternates two, the colour chains
run through `cap + 1`), and the tower's cell names are literals, so a
chain of length `r` is `r` instantiations of `expSynth` at `r + 1`
names — which is the pinned boundary's name generation and belongs to
the integration wave, exactly as `ClusterSynth` §6 states for the
per-depth names. The mathematics of the fold (`chainCom_succ`,
`ballOf_nbhd`, `chainCom_stages`) is `RamDriverDescend`'s and is
consumed, not re-proved.

**2G/N-2 — no `BRefine` coverage** (2F/N-5 at this pass). Every bound
(`n`, `jend`) is a runtime cell entering as an `ℕ`, and the count `hct`
is a *new* quantity the machine does not carry: it is bounded by the
block's length and so by `ns`, which is below the word bound in every
caller, but nothing here proves it. `ScatterSynth` §15's `ScanBounded`
is the pattern; the nested loop needs the rule `ElimSynth3`'s debt E3
names as missing (`BRefine.while_guard` takes a body, not a body
containing a loop).

**2G/N-3 — the carrier pass is not touched-only, and cannot be made so
here.** 2G/D-c: `expRowC` is paid at every vertex whether or not the
mask keeps it, so a chain of `2·cap` expansions costs `Θ(cap·n)` per
cluster even when the ball is a constant-size set. The repair is a
*frontier* representation — expand a list of marked vertices rather than
the carrier — which is a change to the machine program (`RamDriver`),
not to this file, and it is the same shape of repair 2F/D-a names for
`clusterLoad`'s fill. Recorded together with it.

## 12. Axioms -/

section Axioms

/-- info: 'Lax3Proofs.Refine.ExpandSynth.expScanSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms expScanSynth

/-- info: 'Lax3Proofs.Refine.ExpandSynth.expSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms expSynth

/-- info: 'Lax3Proofs.Refine.ExpandSynth.expPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms expPass_spec

/-- info: 'Lax3Proofs.Refine.ExpandSynth.expPass_expandVal' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms expPass_expandVal

/-- info: 'Lax3Proofs.Refine.ExpandSynth.expOf_eq_expandVal' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms expOf_eq_expandVal

end Axioms

/-! ## 13. Telemetry (the wave's acceptance numbers)

| item | number |
|---|---|
| passes derived here | 2 (the block scan, and the whole pass containing it) |
| syntheses | 2, both at 1 000 000 heartbeats |
| `expScanSynth` (inner loop alone) | ≈ 0.7 s |
| `expSynth` (outer + inner, branch containing the loop) | ≈ 2.6 s |
| file wall clock, cold | ≈ 26 s |
| widest state | 2 components (both loops) |
| `#guard`s | 45 |
| `#guard_msgs` blocks (negative controls + axiom checks) | 8 |
| refuted authored statements | 0 |
| sorries | 0 |
| axioms | `propext`, `Classical.choice`, `Quot.sound` only |

**2G/M-a — the branch containing a loop is cheap when the state is
narrow.** `ElimSynth2.fillSynth` — the same shape at a three-component
state — needed 4 000 000 heartbeats when it first landed; this one, at
two components, translates in 1 000 000 and under three seconds. Taken
with 2B′/M-a's ≈ 90 s at eleven components, the tool's cost is governed
by the *state width* and not by the nesting depth, which is the
datapoint the rebase plan wanted before committing the remaining
per-depth shapes to the tower. -/

end Lax3Proofs.Refine.ExpandSynth
