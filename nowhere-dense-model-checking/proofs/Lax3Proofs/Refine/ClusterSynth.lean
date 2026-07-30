import Lax3Proofs.Refine.OrderSynth
import Lax13Proofs.Refine.Sepref.IrOpsExtra

/-!
# ND-MC rebase P2 / satellite 2F — the DESCEND/CLUSTER leaves at `R = 0`,
re-derived through the refinement tower

`RamDriver.clusterCom q_top cap mb φ j inner` is one turn of the driver's
loop over the centres of a level's cover: the descent into a cluster, the
padded enumeration of the round's batch, the colouring of the next depth,
the nested driver, the scatter atoms, and the readback. This file maps it
pass by pass and re-derives its **leaf passes** through the tower.

## 0. THE REDUCTION — what `clusterCom q_top cap mb φ j inner` actually
runs

Two facts govern the map, and neither is the one the ordering phase's
map turned on.

**`clusterCom` does not mention `R`.** Unlike `RamDriver.orderCom`,
whose augmentation fold collapses to `Com.skip` at `R = 0` and takes
three counting sorts with it (`OrderSynth` §0), the cluster step is
*`R`-independent*: every pass below is live at `R = 0` exactly as it is
at `R > 0`. So there is no degeneracy to harvest here, and the map is
the full program.

**What does degenerate is the depth.** The recorded-batch fold
`foldRange (fun a => ancestorStep cap j a) j` of `RamDriver.batchCom`
runs `j` turns, so **at the top depth `j = 0` it is `Com.skip`** — no
`RamBfsPaths.bfsParCom`, no `extractPathCom`, no `markPath`, and the
batch of the round is the connector alone cut down to the ball. The
whole game side of the descent — the only place a search is called from
inside a cluster — first appears at `j = 1`. That is this map's
counterpart of 2E's `Com.skip` finding, and it is why the leaves below
are ordered as they are: `scatPass` (§3) is reached at every depth,
`markPath` only from `j = 1`.

### The six phases

| # | phase | shape |
|---|---|---|
| 1 | `descendCom cap j` | **D1–D10 below** |
| 2 | `enumBatch (batName j) mb` | two flat loops (compaction + padding) |
| 3 | `colourCom cap mb j` | **C1–C3 below** |
| 4 | `inner` | the nested driver — **RETAINED** (pinned boundary) |
| 5 | `foldIdx (scatterCom …) 0 (tablesAt …)` | per atom: two prefix copies + the scatter **engine** |
| 6 | `readbackCom q_top cap mb φ j` | one flat loop, straight-line body |

### The descent, pass by pass

| # | command | shape | this file |
|---|---|---|---|
| D1 | `.assign (ctrName j) (.get (ordName j) (.var (curName j)))` | one `aget` | — |
| D2a | `fillCom (cluName j) (.lit 0)` | prefix fill at `n` | `OrderSynth.fillPass` |
| D2b | `Csr.loadRow (xofName j) (curName j) "p" "pend"` | two machine ops, **three** IR ops (2F/D-b) | §6 |
| D2c | `Csr.scan "p" "pend" (…)` | **the touched-only scatter loop** | **§3 `scatPass`** |
| D3 | `andCom (alvName j) (cluName j) (resName j)` | prefix mask pass | **§4 `andPass`** |
| D4 | `fillCom (balName j) (.lit 0)` | prefix fill at `n` | `OrderSynth.fillPass` |
| D5 | `.store (balName j) (.var (ctrName j)) (.lit 1)` | one `aset` | — |
| D6 | `chainCom (gamName j) (ballStage j) (2 * cap)` | `2·cap` × **`expandCom`** — a *nested* loop | **not derived (§9 debt 1)** |
| D7a | `fillCom (batName j) (.lit 0)` | prefix fill at `n` | `OrderSynth.fillPass` |
| D7b | `.store (batName j) (.var (ctrName j)) (.lit 1)` | one `aset` | — |
| D7c | `foldRange (ancestorStep cap j ·) j` | `j` turns; **`Com.skip` at `j = 0`** | see below |
| D7d | `andCom (batName j) (balName j) (batName j)` | **self-reading** mask pass | **§5 `andSelfPass`** |
| D8 | `subCom (resName j) (batName j) (alvName (j+1))` | prefix mask pass | **§4 `subPass`** |
| D9 | `andCom (gamName j) (balName j) (gamName (j+1))` | prefix mask pass | **§4 `andPass`** |
| D10 | `subCom (gamName (j+1)) (batName j) (gamName (j+1))` | **self-reading** mask pass | **§5 `subSelfPass`** |

and one turn `ancestorStep cap j a` of D7c is

| # | command | shape | this file |
|---|---|---|---|
| A1 | `.assign "src" (.var (ctrName a))`, `.assign "tv" (.var (ctrName j))` | two copies | — |
| A2 | `copyCom (gamName a) "alv"` | prefix copy at `n` | `OrderSynth.copyPass` |
| A3 | `RamBfsPaths.bfsParCom (2 * cap)` | the **search engine** (leaf) | consumed, §9 debt 2 |
| A4 | `.ite (dist[tv] < 2·cap+1) (extractPathCom; markPath (batName j)) .skip` | guarded walk-back + **the path marker** | **§3 `scatPass` again** |

### The colouring, pass by pass

| # | command | shape | this file |
|---|---|---|---|
| C1 | `oldCom cap mb j` | `sigL` × `andCom` + one `copyCom` | **§4 `andPass`**, `OrderSynth.copyPass` |
| C2 | `pdCom cap mb j` | `mb` × (prefix fill + one `aset` + `chainCom … cap`) | fill derived; chain = debt 1 |
| C3 | `puCom cap mb j` | `(sigL+1)` × (prefix copy + `chainCom … cap`) | copy derived; chain = debt 1 |

### So what is a leaf here, and what is not

Counting instances at depth `j` with `s := sigL cap mb j`:

* **prefix passes over the carrier** — `4 + j` copies (D2a…, A2, C1, C3) and
  `3 + mb` fills, plus `2 + s` and-passes, `1` sub-pass, `1` self-and,
  `1` self-sub. Every one of them is `RamDriver.fillUpto` with a cell
  expression, and §§3–5 derive the three cell expressions the phase uses
  that `OrderSynth` did not: the **indirect store** (D2c/A4), the
  **product of two masks** (D3/D9/C1), and the **product with a
  complement** (D8).
* **touched-only passes** — exactly one: D2c, the `Csr.scan` of the
  cluster load, whose turns are the *members of the block* and not the
  carrier. §8 is what that is worth and what it is not worth.
* **nested loops** — `expandCom` only, at `2·cap + mb·cap + (s+1)·cap`
  instances per cluster. This is the single largest underived object on
  the `C0` path and §9 debt 1 states it precisely.
* **engines called as leaves** — the search (A3) and the scatter
  (phase 5). Both are already through the tower (`BfsBridge`,
  `ScatterSynth.scatterTowerCom_spec`); nothing here re-derives them.
* **retained** — `inner`, and every per-depth name (`curName j`,
  `cluName j`, …). The leaves below take their cells at *one* depth, as
  literals; the driver's name generation is the pinned boundary and
  stays out of this file.

## 2F/D-a — the cluster load's two halves are charged differently

`clusterLoad j` is `fillCom (cluName j) 0` *then* the block scan. The
scan is touched-only — its cost is `15·|block(c)| + 4`, the block's own
size — but the fill that precedes it is `12·n + 4` **per cluster**, so
the pass as a whole is `Θ(n)` per cluster and `Θ(n · #clusters)` per
level. §8 states both halves separately and §8's `clusterLoadK` is the
sum; this is `[[touched-only-costs]]` at its named site, and the
touched-only *shape* is visible in `scatPass_spec`'s bound (`e - p₀`,
never `n`) while the `Θ(n)` is visible in `clusterLoadK`. Recording it
here rather than repairing it: the repair is a change to the *machine*
program (a trail array over the previous block, `Examples/TrailRecursion`'s
carrier-free idiom), which this satellite does not own.

## 2F/D-b — the row load is three IR operations, not two

`Csr.loadRow o v j jend` is `j := o[v]; jend := o[v+1]`, two machine
instructions with an addition nested inside the second's index. The IR
has no nested operand (2E/D-b at a second site), so the tower's load is
`aget p o cur; add t cur one; aget pend o t` — one extra cell and one
extra time unit per *row*, which is once per cluster and not once per
member. §6 pins it.

## 2F/D-c — the self-reading mask passes are different programs

`andCom (batName j) (balName j) (batName j)` and
`subCom (gamName (j+1)) (batName j) (gamName (j+1))` read their own
destination. At the machine layer that is invisible — array names are
strings and `RamDriverDescend.andSelfCom_spec` is a separate lemma for
exactly this reason. At the tower it is *not* invisible: the destination
array is the loop state's own component and the source is a frame
conjunct, and one cell name cannot be both. So §5 derives them as their
own abstract programs, reading `s.1` where §4 reads the frame — the
values agree because each cell reads only its own index, which is
`binI`'s last conjunct and is the content of §5's two `_le` lemmas.

## 2F/D-d — the stored constant rides in a cell

`Csr.scan`'s body stores `.lit 1` and `subCom`'s expression contains
`.lit 1`. The IR's `aset` takes three cells and its `binop` takes two,
so both literals are cells: `"sv"` for the scatter pass's value and the
entry store's pinned `"one"` for the complement. This is
`OrderSynth.fillPass`'s `"flv"` at two more sites, and it is why §3's
pass is stated at a *general* `v` and instantiated at `1`.

## What is consumed rather than re-proved

`OrderSynth.copyPass`/`fillPass` are this campaign's own capital and are
used, not restated: D2a, D4, D7a, A2, C1's copy and C3's copy are them.
`ElimSynth2`'s two devices (`while_pot_le`, `larr`) carry every loop
below. `SplitterWinRec` is not touched at all — the game mathematics of
the batch is `RamDriverDescend`'s and this file owes it nothing.

## House traps observed

`omega` is blind through `Ir.Val`, so every arithmetic obligation is
bound at `ℕ` first; `decide +kernel` for the cost numerals; never
`simp [Codegen.embed]`; junk cells are consumed in written order across
leaf boundaries (2E/D-d), so composed programs are pinned from the
tool's own report and never by hand-seq; loop states are assembled with
`mopPair` and never as literal tuples (P4/D-m).
-/

namespace Lax3Proofs.Refine.ClusterSynth

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Sepref.WordSpike
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (cu iter irWhile_exit get!_set liftACost_cu)
open Lax3Proofs.Refine.ElimSynth2 (while_pot_le step_spec)

/-! ## 1. Refute before prove

The three cell expressions of §§3–5 as computable functions, run to
their ends, and their answers pinned — first against hand-computed
readings on a small arena, then (in §7) against `Ir.evalFuel`'s reading
of the *synthesized* programs.

The hot spots, and where each is checked:

* **the block scan is indirect** — it writes at `xmem[p]`, not at `p`.
  A pass that wrote at `p` would agree with this one exactly when the
  block is an identity segment, and the arena below's second block is
  not. The negative control exhibits it.
* **the block scan is a prefix of a prefix** — it starts at `xoff[c]`
  and stops at `xoff[c+1]`, so it touches neither the earlier blocks'
  members nor the later ones'. Both ends are checked.
* **the cluster load aliases its own fill** — `clusterLoad` is the fill
  of the *whole carrier* followed by the scan of *one block*, so the
  cells the scan does not reach are the fill's zeroes and not the
  caller's. The composed twin is checked against a carrier longer than
  the block.
* **`andCom` and `subCom` are not each other**, and the self-reading
  versions are not the frame-reading ones on a source that has already
  been overwritten. Both are checked.
* **`subCom` needs its second argument to be a mask.** `a * (1 - b)` on
  a `b` above `1` is truncated to `a * 0 = 0`, which is the complement's
  answer, but on a `b` of `2` a reading that expected `a - b` would
  differ. The negative control fixes which one the program is.
-/

section Twin

/-- The state of every pass here: the array being written and the
counter. `OrderSynth.FS` under its own name, so that the twins compose
with `OrderSynth`'s. -/
abbrev FS : Type := List ℕ × ℕ

/-- One slot of an indirect scatter-write: read the index array at the
pointer, write the value there, bump the pointer. -/
def scatTw (idx : List ℕ) (v : ℕ) : FS → FS := fun s => (s.1.set idx[s.2]! v, s.2 + 1)

/-- One cell of a two-source mask pass. -/
def binTw (g : ℕ → ℕ → ℕ) (a b : List ℕ) : FS → FS :=
  fun s => (s.1.set s.2 (g a[s.2]! b[s.2]!), s.2 + 1)

/-- One cell of a *self-reading* two-source mask pass. -/
def binSelfTw (g : ℕ → ℕ → ℕ) (b : List ℕ) : FS → FS :=
  fun s => (s.1.set s.2 (g s.1[s.2]! b[s.2]!), s.2 + 1)

/-- `andCom`'s cell function. -/
def andG (x y : ℕ) : ℕ := x * y

/-- `subCom`'s cell function: the first mask with the second's marks
killed, in truncated arithmetic. -/
def subG (x y : ℕ) : ℕ := x * (1 - y)

/-- A pass, run from a start to a bound. -/
def runTw (step : FS → FS) (N : ℕ) : ℕ → FS → FS
  | 0, s => s
  | fuel + 1, s => if s.2 < N then runTw step N fuel (step s) else s

/-- The block scan, run from `p₀` to `e`. -/
def scatRun (p₀ e v : ℕ) (idx A : List ℕ) : List ℕ :=
  (runTw (scatTw idx v) e (e + 1) (A, p₀)).1

/-- A mask pass, run. -/
def binRun (N : ℕ) (g : ℕ → ℕ → ℕ) (a b A : List ℕ) : List ℕ :=
  (runTw (binTw g a b) N (N + 1) (A, 0)).1

/-- A self-reading mask pass, run. -/
def binSelfRun (N : ℕ) (g : ℕ → ℕ → ℕ) (b A : List ℕ) : List ℕ :=
  (runTw (binSelfTw g b) N (N + 1) (A, 0)).1

/-- **The cluster load, whole**: the fill of the carrier and then the
scan of one block. `OrderSynth.fillRun` is the first half. -/
def loadRun (n p₀ e : ℕ) (idx A : List ℕ) : List ℕ :=
  scatRun p₀ e 1 idx (OrderSynth.fillRun n 0 A)

/-! ### The arena

Six carrier vertices in three blocks, in the compressed-row form
`RamCover.coverCom` leaves and `clusterLoad` reads: `xoff` is the block
offsets and `xmem` the members. Block `0` is `{0, 3}`, block `1` is
`{5, 1, 4}` — deliberately *not* an identity segment, which is what the
indirection is checked against — and block `2` is `{2}`. -/

def demoXoff : List ℕ := [0, 2, 5, 6]

def demoXmem : List ℕ := [0, 3, 5, 1, 4, 2]

/-- The block of centre `c`, read straight off the arena — the
independent reference the scan is differentially tested against. -/
def demoBlock (c : ℕ) : List ℕ :=
  ((List.range 6).filter (fun p => demoXoff[c]! ≤ p ∧ p < demoXoff[c + 1]!)).map
    (fun p => demoXmem[p]!)

#guard demoBlock 0 = [0, 3]
#guard demoBlock 1 = [5, 1, 4]
#guard demoBlock 2 = [2]

/-- The cluster indicator the load should leave for centre `c`: the
block's members and nothing else. -/
def demoClu (c : ℕ) : List ℕ :=
  (List.range 6).map (fun w => if w ∈ demoBlock c then 1 else 0)

-- **The scan is the block, differentially.** Three centres, and each
-- time the load's answer is the reference's indicator, cell for cell.
#guard loadRun 6 demoXoff[0]! demoXoff[1]! demoXmem (List.replicate 6 9) = demoClu 0
#guard loadRun 6 demoXoff[1]! demoXoff[2]! demoXmem (List.replicate 6 9) = demoClu 1
#guard loadRun 6 demoXoff[2]! demoXoff[3]! demoXmem (List.replicate 6 9) = demoClu 2

-- and the readings, written out, so the check is not circular
#guard loadRun 6 0 2 demoXmem (List.replicate 6 9) = [1, 0, 0, 1, 0, 0]
#guard loadRun 6 2 5 demoXmem (List.replicate 6 9) = [0, 1, 0, 0, 1, 1]
#guard loadRun 6 5 6 demoXmem (List.replicate 6 9) = [0, 0, 1, 0, 0, 0]

-- **The fill is what the caller's cells become.** The scan alone leaves
-- the untouched cells at `9`; the load zeroes them. This is the
-- aliasing hot spot, and the two runs differ.
#guard scatRun 0 2 1 demoXmem (List.replicate 6 9) = [1, 9, 9, 1, 9, 9]
#guard scatRun 0 2 1 demoXmem (List.replicate 6 9) ≠ loadRun 6 0 2 demoXmem (List.replicate 6 9)

/-! ### Negative controls -/

-- **The write is indirect.** A pass storing at the pointer rather than
-- at `xmem[p]` would mark `{2, 3, 4}` for the middle block; the scan
-- marks `{1, 4, 5}`.
#guard loadRun 6 2 5 demoXmem (List.replicate 6 9)
  ≠ (List.range 6).map (fun w => if 2 ≤ w ∧ w < 5 then 1 else 0)

-- **The scan is a prefix of a prefix.** It touches neither block `0`'s
-- members (`0`, `3`) nor block `2`'s (`2`) when it runs on block `1`.
#guard (loadRun 6 2 5 demoXmem (List.replicate 6 9))[0]! = 0
#guard (loadRun 6 2 5 demoXmem (List.replicate 6 9))[3]! = 0
#guard (loadRun 6 2 5 demoXmem (List.replicate 6 9))[2]! = 0

-- **An empty block writes nothing.** `p₀ = e` is the `.skip` of the
-- pass, and a scan that ran one turn anyway would be caught.
#guard scatRun 3 3 1 demoXmem (List.replicate 6 9) = List.replicate 6 9

/-! ### The mask passes -/

def demoAlv : List ℕ := [1, 1, 0, 1, 1, 1]

def demoCluL : List ℕ := [0, 1, 0, 0, 1, 1]

def demoBat : List ℕ := [0, 1, 0, 0, 0, 1]

-- **`andCom`**: the arena cut down to the cluster.
#guard binRun 6 andG demoAlv demoCluL (List.replicate 6 7) = [0, 1, 0, 0, 1, 1]

-- **`subCom`**: the cluster-restricted arena with the batch killed.
#guard binRun 6 subG [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7) = [0, 0, 0, 0, 1, 0]

-- **The two are not each other** on this data.
#guard binRun 6 andG [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7)
  ≠ binRun 6 subG [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7)

-- **The self-reading versions agree with the frame-reading ones at the
-- entry array** — D7d's `andCom bat bal bat` is `binSelfTw` at `b :=
-- bal`, and its answer is `binTw` at `a := bat`.
#guard binSelfRun 6 andG [1, 1, 1, 0, 0, 1] demoBat
  = binRun 6 andG demoBat [1, 1, 1, 0, 0, 1] (List.replicate 6 0)
#guard binSelfRun 6 subG demoBat [0, 1, 0, 0, 1, 1]
  = binRun 6 subG [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 0)

-- **A self-reading pass is not the frame-reading pass at the *source***
-- when the two arrays differ: the point of D7d is that the destination
-- *is* the source, and swapping them is a different answer.
#guard binSelfRun 6 subG [1, 1, 1, 1, 1, 1] [0, 1, 0, 0, 1, 1]
  ≠ binRun 6 subG [1, 1, 1, 1, 1, 1] [0, 1, 0, 0, 1, 1] (List.replicate 6 0)

-- **`subG` is a complement and not a subtraction.** On a second
-- argument of `2` the truncation makes it `0`; a pass computing `a - b`
-- would say `0` as well at `a = 1`, but at `a = 3` it would say `1`.
#guard subG 3 2 = 0
#guard 3 - 2 = 1

-- **The passes really write.** A pass that stopped at zero would leave
-- the entry array, and the check can tell.
#guard binRun 6 andG demoAlv demoCluL (List.replicate 6 7) ≠ List.replicate 6 7

-- **The bound is a prefix bound**, here too: three cells of six.
#guard binRun 3 andG demoAlv demoCluL (List.replicate 6 7) = [0, 1, 0, 7, 7, 7]

end Twin

/-! ## 2. The block scan — the one touched-only pass of the descent

`Csr.scan "p" "pend"` over `.store (cluName j) (.get (xmmName j) (.var
"p")) (.lit 1)`: read the member at the slot pointer, mark it, bump the
pointer. Its turns are the **members of the block** — the loop starts at
`xoff[c]` and stops at `xoff[c+1]` — so its cost is the block's size and
not the carrier's, which is the whole of D2c's claim and what §8 cashes.

The specification is stated *positively and negatively*: every slot of
the block is marked, and every cell no slot of the block names is the
entry array's. The second half is what the fill in front of it turns
into "and everything else is zero" (§6), and it is what
`RamDriverCluster.BatchData`'s `markSet n Xa = X` needs. -/

section Scat

/-- What one slot needs in range: the pointer names a member, and the
member is a vertex. -/
def scatP (idx : List ℕ) : FS → Prop := fun s => s.2 < idx.length ∧ idx[s.2]! < s.1.length

/-- The scan's guard — the block's own end, a *runtime* number. -/
def scatBf (e : ℕ) : FS → Bool := fun s => decide (s.2 < e)

/-- **One slot.** The machine's nested `.get` inside `.store` is two IR
operations (2E/D-b), and the stored `.lit 1` rides in a cell (2F/D-d). -/
noncomputable def scatF (idx : List ℕ) (v : ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget idx s.2) fun u =>
    bindT (mopAset s.1 u v) fun A =>
      bindT (mopSucc s.2) fun p => mopPair A p

/-- **The block scan.** -/
noncomputable def scatPass (e v : ℕ) (idx : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => scatBf e s = true → scatP idx s) (scatBf e) (scatF idx v) s₀

/-- One slot's price: a read, a write, a bump, the pair — a copy's cell
exactly, since the indirection changes which cell is read and not how
many. -/
def scatC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aset + cu Currency.add + cu Currency.skip

theorem scatF_le (idx : List ℕ) (v : ℕ) (s : FS) (h : scatP idx s) :
    scatF idx v s ≤ NRest.consume (NRest.returnT (scatTw idx v s)) (liftACost scatC) := by
  refine le_of_eq ?_
  obtain ⟨h1, h2⟩ := h
  simp only [scatF, scatTw, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, scatC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- The scan's invariant: the length, the pointer inside the block, and
the array read **two ways** — every slot already passed is marked, and
every cell no passed slot names is the caller's. -/
def scatI (p₀ e L v : ℕ) (idx A₀ : List ℕ) : FS → Prop := fun s =>
  s.1.length = L ∧ p₀ ≤ s.2 ∧ s.2 ≤ e ∧ e ≤ idx.length ∧ (∀ q, q < e → idx[q]! < L) ∧
    (∀ q, p₀ ≤ q → q < s.2 → s.1[idx[q]!]! = v) ∧
    (∀ w, (∀ q, p₀ ≤ q → q < s.2 → idx[q]! ≠ w) → s.1[w]! = A₀[w]!)

theorem scatI_range {p₀ e L v : ℕ} {idx A₀ : List ℕ} {s : FS} (hI : scatI p₀ e L v idx A₀ s)
    (hb : scatBf e s = true) : scatP idx s := by
  obtain ⟨h1, -, -, h4, h5, -, -⟩ := hI
  have hi : s.2 < e := by simpa [scatBf] using hb
  exact ⟨by omega, by rw [h1]; exact h5 _ hi⟩

theorem scatI_step {p₀ e L v : ℕ} {idx A₀ : List ℕ} {s : FS} (hI : scatI p₀ e L v idx A₀ s)
    (hb : scatBf e s = true) : scatI p₀ e L v idx A₀ (scatTw idx v s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  have hi : s.2 < e := by simpa [scatBf] using hb
  have hd : idx[s.2]! < s.1.length := by rw [h1]; exact h5 _ hi
  simp only [scatI, scatTw]
  refine ⟨by simpa using h1, by omega, by omega, h4, h5, ?_, ?_⟩
  · intro q hq hq'
    rw [get!_set _ _ _ _ hd]
    by_cases hh : idx[q]! = idx[s.2]!
    · rw [if_pos hh]
    · rw [if_neg hh]
      have hlt : q < s.2 := by
        by_contra hc
        have : q = s.2 := by omega
        subst this; exact hh rfl
      exact h6 q hq hlt
  · intro w hw
    rw [get!_set _ _ _ _ hd, if_neg (fun hc => hw s.2 (by omega) (by omega) hc.symm)]
    exact h7 w fun q hq hq' => hw q hq (by omega)

theorem scatPass_le {p₀ e L v : ℕ} {idx A₀ : List ℕ} :
    ∀ (fuel : ℕ) (s : FS), scatI p₀ e L v idx A₀ s → e - s.2 < fuel →
      scatPass e v idx s
        ≤ NRest.spec (fun t => scatI p₀ e L v idx A₀ t ∧ scatBf e t = false)
            (fun _ => liftACost ((e - s.2) • iter scatC + cu Currency.«while»)) :=
  while_pot_le (P := scatP idx) (V := fun s => e - s.2)
    (Φ := fun s => (e - s.2) • iter scatC) (Φ' := fun s => (e - (s.2 + 1)) • iter scatC)
    (C := fun _ => scatC) (fun _ h hb => scatI_range h hb)
    (fun s h hb => by
      have hi : s.2 < e := by simpa [scatBf] using hb
      exact step_spec (s := s) (x := scatTw idx v s) (C := fun _ => scatC)
        (Φ := fun s => (e - s.2) • iter scatC) (Φ' := fun s => (e - (s.2 + 1)) • iter scatC)
        (V := fun s => e - s.2) (scatF_le idx v s (scatI_range h hb)) (scatI_step h hb)
        (by show e - (s.2 + 1) < e - s.2; omega) le_rfl)
    (fun s _ hb => by
      have hi : s.2 < e := by simpa [scatBf] using hb
      show iter scatC + (e - (s.2 + 1)) • iter scatC ≤ (e - s.2) • iter scatC
      rw [show e - s.2 = (e - (s.2 + 1)) + 1 by omega, succ_nsmul]
      exact le_of_eq (by ac_rfl))

/-- **The block scan's export.** Everything the block names holds `v`;
everything it does not is the caller's. The bound is `e - p₀`, the
block's own size — the touched-only shape, visible in the signature. -/
theorem scatPass_spec {p₀ e L v : ℕ} {idx A₀ : List ℕ} (hA : A₀.length = L) (hp : p₀ ≤ e)
    (he : e ≤ idx.length) (hlt : ∀ q, q < e → idx[q]! < L) :
    scatPass e v idx (A₀, p₀)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            (∀ q, p₀ ≤ q → q < e → t.1[idx[q]!]! = v) ∧
            (∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → t.1[w]! = A₀[w]!))
          (fun _ => liftACost ((e - p₀) • iter scatC + cu Currency.«while»)) := by
  refine le_trans (scatPass_le (p₀ := p₀) (e := e) (L := L) (v := v) (idx := idx) (A₀ := A₀)
    (e + 1) (A₀, p₀)
      ⟨hA, le_rfl, hp, he, hlt, fun q hq hq' => absurd hq' (by omega), fun w _ => rfl⟩ (by omega))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, -, t3, -, -, t6, t7⟩, hbf⟩
  have hte : t.2 = e := by
    have : ¬ t.2 < e := by simpa [scatBf] using hbf
    omega
  subst hte
  exact ⟨t1, t6, t7⟩

end Scat

/-! ## 3. The mask passes, generically

`RamDriver.andCom a b dst` and `subCom a b dst` are both
`fillUpto dst (.var "n") e` with a two-array cell expression, and so is
`oldCom`'s pass. What differs between them is the expression and the
price; what does not is the loop. So the loop is proved once here, at an
abstract body and an abstract cell function, and §§4–5 supply four
bodies.

The invariant is `OrderSynth.copyI`'s with the source read through the
cell function — deliberately, because the frame conditions
`RamDriverCluster.BatchData` and `TurnPre` need the destination cell by
cell below the bound *and* above it. -/

section Bin

/-- What one cell of a frame-reading mask pass needs in range. -/
def binP (a b : List ℕ) : FS → Prop :=
  fun s => s.2 < a.length ∧ s.2 < b.length ∧ s.2 < s.1.length

/-- What one cell of a self-reading one needs (2F/D-c): the destination
is the first source, so there are two bounds and not three. -/
def binSelfP (b : List ℕ) : FS → Prop := fun s => s.2 < b.length ∧ s.2 < s.1.length

/-- The passes' guard. -/
def binBf (N : ℕ) : FS → Bool := fun s => decide (s.2 < N)

/-- The mask passes' invariant. -/
def binI (N L : ℕ) (g : ℕ → ℕ → ℕ) (a b A₀ : List ℕ) : FS → Prop := fun s =>
  s.1.length = L ∧ N ≤ L ∧ N ≤ a.length ∧ N ≤ b.length ∧ s.2 ≤ N ∧
    ∀ j, s.1[j]! = if j < s.2 then g a[j]! b[j]! else A₀[j]!

theorem binI_range {N L : ℕ} {g : ℕ → ℕ → ℕ} {a b A₀ : List ℕ} {s : FS}
    (hI : binI N L g a b A₀ s) (hb : binBf N s = true) : binP a b s := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hI
  have hi : s.2 < N := by simpa [binBf] using hb
  exact ⟨by omega, by omega, by omega⟩

theorem binI_selfRange {N L : ℕ} {g : ℕ → ℕ → ℕ} {a b A₀ : List ℕ} {s : FS}
    (hI : binI N L g a b A₀ s) (hb : binBf N s = true) : binSelfP b s := by
  obtain ⟨h1, h2, -, h4, -, -⟩ := hI
  have hi : s.2 < N := by simpa [binBf] using hb
  exact ⟨by omega, by omega⟩

/-- **The self-reading step is the frame-reading step at the entry
array** (2F/D-c). Below the counter the destination has already been
overwritten, but the cell the step is about is *at* the counter, which
no earlier turn touched. -/
theorem binSelfTw_eq {N L : ℕ} {g : ℕ → ℕ → ℕ} {b A₀ : List ℕ} {s : FS}
    (hI : binI N L g A₀ b A₀ s) : binSelfTw g b s = binTw g A₀ b s := by
  obtain ⟨-, -, -, -, -, h6⟩ := hI
  rw [binSelfTw, binTw, h6 s.2, if_neg (lt_irrefl _)]

theorem binI_step {N L : ℕ} {g : ℕ → ℕ → ℕ} {a b A₀ : List ℕ} {s : FS}
    (hI : binI N L g a b A₀ s) (hb : binBf N s = true) : binI N L g a b A₀ (binTw g a b s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  have hi : s.2 < N := by simpa [binBf] using hb
  simp only [binI, binTw]
  refine ⟨by simpa using h1, h2, h3, h4, by omega, fun j => ?_⟩
  rw [get!_set _ _ _ _ (show s.2 < s.1.length by omega)]
  by_cases hj : j = s.2
  · subst hj; rw [if_pos rfl, if_pos (by omega)]
  · rw [if_neg hj, h6 j]
    by_cases hlt : j < s.2
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

/-- **The mask passes' loop, once.** The body enters as a hypothesis
bounded by the cell function's step at a fixed price, which is the only
thing the four instances of §§4–5 differ in. -/
theorem binLoop_le {N L : ℕ} {g : ℕ → ℕ → ℕ} {a b A₀ : List ℕ} {P : FS → Prop}
    {f : FS → NRest FS ECost} {C : ACost String ℕ}
    (hP : ∀ s, binI N L g a b A₀ s → binBf N s = true → P s)
    (hf : ∀ s, binI N L g a b A₀ s → binBf N s = true →
      f s ≤ NRest.consume (NRest.returnT (binTw g a b s)) (liftACost C)) :
    ∀ (fuel : ℕ) (s : FS), binI N L g a b A₀ s → N - s.2 < fuel →
      irWhileIT (fun t => binBf N t = true → P t) (binBf N) f s
        ≤ NRest.spec (fun t => binI N L g a b A₀ t ∧ binBf N t = false)
            (fun _ => liftACost ((N - s.2) • iter C + cu Currency.«while»)) :=
  while_pot_le (P := P) (V := fun s => N - s.2)
    (Φ := fun s => (N - s.2) • iter C) (Φ' := fun s => (N - (s.2 + 1)) • iter C)
    (C := fun _ => C) hP
    (fun s h hb => by
      have hi : s.2 < N := by simpa [binBf] using hb
      exact step_spec (s := s) (x := binTw g a b s) (C := fun _ => C)
        (Φ := fun s => (N - s.2) • iter C) (Φ' := fun s => (N - (s.2 + 1)) • iter C)
        (V := fun s => N - s.2) (hf s h hb) (binI_step h hb)
        (by show N - (s.2 + 1) < N - s.2; omega) le_rfl)
    (fun s _ hb => by
      have hi : s.2 < N := by simpa [binBf] using hb
      show iter C + (N - (s.2 + 1)) • iter C ≤ (N - s.2) • iter C
      rw [show N - s.2 = (N - (s.2 + 1)) + 1 by omega, succ_nsmul]
      exact le_of_eq (by ac_rfl))

end Bin

/-! ## 4. The two frame-reading mask passes

D3, D9 and C1's `andCom a b dst`, and D8's `subCom a b dst`. Both write
a destination distinct from both sources; §5 is the case where it is
not. -/

section MaskFrame

/-- **One cell of `andCom`.** The machine's single `.store dst i (.mul
(.get a i) (.get b i))` is four IR operations: two reads, the product,
the write. -/
noncomputable def andF (a b : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget a s.2) fun x =>
    bindT (mopAget b s.2) fun y =>
      bindT (mopBinop .mul x y) fun w =>
        bindT (mopAset s.1 s.2 w) fun A =>
          bindT (mopSucc s.2) fun i => mopPair A i

/-- **One cell of `subCom`.** One operation more: the complement
`1 - b[i]`, whose `1` rides in the entry store's pinned cell
(2F/D-d). -/
noncomputable def subF (a b : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget a s.2) fun x =>
    bindT (mopAget b s.2) fun y =>
      bindT (mopBinop .sub 1 y) fun c =>
        bindT (mopBinop .mul x c) fun w =>
          bindT (mopAset s.1 s.2 w) fun A =>
            bindT (mopSucc s.2) fun i => mopPair A i

/-- One cell of `andCom`'s price. -/
def andC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aget + cu Currency.mul + cu Currency.aset +
    cu Currency.add + cu Currency.skip

/-- One cell of `subCom`'s: the complement's subtraction more. -/
def subC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aget + cu Currency.sub + cu Currency.mul +
    cu Currency.aset + cu Currency.add + cu Currency.skip

theorem andF_le (a b : List ℕ) (s : FS) (h : binP a b s) :
    andF a b s ≤ NRest.consume (NRest.returnT (binTw andG a b s)) (liftACost andC) := by
  refine le_of_eq ?_
  obtain ⟨h1, h2, h3⟩ := h
  simp only [andF, binTw, andG, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
    NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_mul,
    binopCurrency_add, binopCurrency_mul, andC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

theorem subF_le (a b : List ℕ) (s : FS) (h : binP a b s) :
    subF a b s ≤ NRest.consume (NRest.returnT (binTw subG a b s)) (liftACost subC) := by
  refine le_of_eq ?_
  obtain ⟨h1, h2, h3⟩ := h
  simp only [subF, binTw, subG, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
    NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_mul,
    Lax13Proofs.Imp.Bop.apply_sub, binopCurrency_add, binopCurrency_mul, binopCurrency_sub,
    subC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- **The and-pass.** -/
noncomputable def andPass (N : ℕ) (a b : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => binBf N s = true → binP a b s) (binBf N) (andF a b) s₀

/-- **The sub-pass.** -/
noncomputable def subPass (N : ℕ) (a b : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => binBf N s = true → binP a b s) (binBf N) (subF a b) s₀

/-- **The and-pass's export.** -/
theorem andPass_spec {N L : ℕ} {a b A₀ : List ℕ} (hA : A₀.length = L) (hNL : N ≤ L)
    (hNa : N ≤ a.length) (hNb : N ≤ b.length) :
    andPass N a b (A₀, 0)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            ∀ j, t.1[j]! = if j < N then a[j]! * b[j]! else A₀[j]!)
          (fun _ => liftACost (N • iter andC + cu Currency.«while»)) := by
  refine le_trans (binLoop_le (N := N) (L := L) (g := andG) (a := a) (b := b) (A₀ := A₀)
      (P := binP a b) (C := andC) (fun _ h hb => binI_range h hb)
      (fun s h hb => andF_le a b s (binI_range h hb))
      (N + 1) (A₀, 0) ⟨hA, hNL, hNa, hNb, Nat.zero_le _, fun j => by simp⟩ (by simp))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, -, -, -, t5, t6⟩, hbf⟩
  have hti : t.2 = N := by
    have : ¬ t.2 < N := by simpa [binBf] using hbf
    omega
  exact ⟨t1, by rw [← hti]; exact t6⟩

/-- **The sub-pass's export.** The complement is truncated: on a mask
the cell is `a[j]` when `b[j] = 0` and `0` otherwise. -/
theorem subPass_spec {N L : ℕ} {a b A₀ : List ℕ} (hA : A₀.length = L) (hNL : N ≤ L)
    (hNa : N ≤ a.length) (hNb : N ≤ b.length) :
    subPass N a b (A₀, 0)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            ∀ j, t.1[j]! = if j < N then a[j]! * (1 - b[j]!) else A₀[j]!)
          (fun _ => liftACost (N • iter subC + cu Currency.«while»)) := by
  refine le_trans (binLoop_le (N := N) (L := L) (g := subG) (a := a) (b := b) (A₀ := A₀)
      (P := binP a b) (C := subC) (fun _ h hb => binI_range h hb)
      (fun s h hb => subF_le a b s (binI_range h hb))
      (N + 1) (A₀, 0) ⟨hA, hNL, hNa, hNb, Nat.zero_le _, fun j => by simp⟩ (by simp))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, -, -, -, t5, t6⟩, hbf⟩
  have hti : t.2 = N := by
    have : ¬ t.2 < N := by simpa [binBf] using hbf
    omega
  exact ⟨t1, by rw [← hti]; exact t6⟩

end MaskFrame

/-! ## 5. The two self-reading mask passes (2F/D-c)

D7d's `andCom (batName j) (balName j) (batName j)` and D10's
`subCom (gamName (j+1)) (batName j) (gamName (j+1))`. The first source
*is* the destination, so at this layer the read comes off the loop
state's own array component and not off a frame conjunct — a different
abstract program, with the same value and the same price. -/

section MaskSelf

/-- **One cell of the self-reading and-pass.** -/
noncomputable def andSelfF (b : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget s.1 s.2) fun x =>
    bindT (mopAget b s.2) fun y =>
      bindT (mopBinop .mul x y) fun w =>
        bindT (mopAset s.1 s.2 w) fun A =>
          bindT (mopSucc s.2) fun i => mopPair A i

/-- **One cell of the self-reading sub-pass.** -/
noncomputable def subSelfF (b : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget s.1 s.2) fun x =>
    bindT (mopAget b s.2) fun y =>
      bindT (mopBinop .sub 1 y) fun c =>
        bindT (mopBinop .mul x c) fun w =>
          bindT (mopAset s.1 s.2 w) fun A =>
            bindT (mopSucc s.2) fun i => mopPair A i

theorem andSelfF_le (b : List ℕ) (s : FS) (h : binSelfP b s) :
    andSelfF b s ≤ NRest.consume (NRest.returnT (binSelfTw andG b s)) (liftACost andC) := by
  refine le_of_eq ?_
  obtain ⟨h2, h3⟩ := h
  simp only [andSelfF, binSelfTw, andG, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h2, NRest.assert_pos h3,
    NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_mul,
    binopCurrency_add, binopCurrency_mul, andC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

theorem subSelfF_le (b : List ℕ) (s : FS) (h : binSelfP b s) :
    subSelfF b s ≤ NRest.consume (NRest.returnT (binSelfTw subG b s)) (liftACost subC) := by
  refine le_of_eq ?_
  obtain ⟨h2, h3⟩ := h
  simp only [subSelfF, binSelfTw, subG, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h2, NRest.assert_pos h3,
    NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_mul,
    Lax13Proofs.Imp.Bop.apply_sub, binopCurrency_add, binopCurrency_mul, binopCurrency_sub,
    subC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- **The self-reading and-pass.** -/
noncomputable def andSelfPass (N : ℕ) (b : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => binBf N s = true → binSelfP b s) (binBf N) (andSelfF b) s₀

/-- **The self-reading sub-pass.** -/
noncomputable def subSelfPass (N : ℕ) (b : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => binBf N s = true → binSelfP b s) (binBf N) (subSelfF b) s₀

/-- **The self-reading and-pass's export.** Its answer is the
frame-reading pass's at `a := A₀` — which is the whole content of
2F/D-c and the reason the two can be composed by the integration wave
without a second mathematics. -/
theorem andSelfPass_spec {N L : ℕ} {b A₀ : List ℕ} (hA : A₀.length = L) (hNL : N ≤ L)
    (hNb : N ≤ b.length) :
    andSelfPass N b (A₀, 0)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            ∀ j, t.1[j]! = if j < N then A₀[j]! * b[j]! else A₀[j]!)
          (fun _ => liftACost (N • iter andC + cu Currency.«while»)) := by
  refine le_trans (binLoop_le (N := N) (L := L) (g := andG) (a := A₀) (b := b) (A₀ := A₀)
      (P := binSelfP b) (C := andC) (fun _ h hb => binI_selfRange h hb)
      (fun s h hb => by
        rw [← binSelfTw_eq h]; exact andSelfF_le b s (binI_selfRange h hb))
      (N + 1) (A₀, 0) ⟨hA, hNL, by omega, hNb, Nat.zero_le _, fun j => by simp⟩ (by simp))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, -, -, -, t5, t6⟩, hbf⟩
  have hti : t.2 = N := by
    have : ¬ t.2 < N := by simpa [binBf] using hbf
    omega
  exact ⟨t1, by rw [← hti]; exact t6⟩

/-- **The self-reading sub-pass's export.** -/
theorem subSelfPass_spec {N L : ℕ} {b A₀ : List ℕ} (hA : A₀.length = L) (hNL : N ≤ L)
    (hNb : N ≤ b.length) :
    subSelfPass N b (A₀, 0)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            ∀ j, t.1[j]! = if j < N then A₀[j]! * (1 - b[j]!) else A₀[j]!)
          (fun _ => liftACost (N • iter subC + cu Currency.«while»)) := by
  refine le_trans (binLoop_le (N := N) (L := L) (g := subG) (a := A₀) (b := b) (A₀ := A₀)
      (P := binSelfP b) (C := subC) (fun _ h hb => binI_selfRange h hb)
      (fun s h hb => by
        rw [← binSelfTw_eq h]; exact subSelfF_le b s (binI_selfRange h hb))
      (N + 1) (A₀, 0) ⟨hA, hNL, by omega, hNb, Nat.zero_le _, fun j => by simp⟩ (by simp))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, -, -, -, t5, t6⟩, hbf⟩
  have hti : t.2 = N := by
    have : ¬ t.2 < N := by simpa [binBf] using hbf
    omega
  exact ⟨t1, by rw [← hti]; exact t6⟩

end MaskSelf

/-! ## 6. The five passes, synthesized

Cell names are literals here, as the tool requires, and they are *not*
the driver's per-depth names: at depth `j` the scan's `"clu"` is
`RamDriver.cluName j` and its `"xmm"` is `xmmName j`, and at A4 the same
program runs at `"bat"`/`"path"`. The renaming is the integration wave's
(§10), and the leaves are stated at one depth exactly as the pinned
boundary decision says. -/

section Synth

set_option maxHeartbeats 1000000 in
sepref_synth scatSynth (e v : ℕ) (idx A₀ : List ℕ) (p₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, p₀) ("clu", "p") ∗
      hnCtxt arrayAssn idx "xmm" ∗ hnCtxt natAssn v "sv" ∗ hnCtxt natAssn e "pend" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "cw")
    _ _ ("clu", "p") (arrayAssn ×ₐ natAssn)
    (scatPass e v idx (A₀, p₀))

set_option maxHeartbeats 1000000 in
sepref_synth andSynth (N : ℕ) (a b A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cld", "cli") ∗
      hnCtxt arrayAssn a "cla" ∗ hnCtxt arrayAssn b "clb" ∗ hnCtxt natAssn N "cln" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clw")
    _ _ ("cld", "cli") (arrayAssn ×ₐ natAssn)
    (andPass N a b (A₀, i₀))

set_option maxHeartbeats 1000000 in
sepref_synth subSynth (N : ℕ) (a b A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cld", "cli") ∗
      hnCtxt arrayAssn a "cla" ∗ hnCtxt arrayAssn b "clb" ∗ hnCtxt natAssn N "cln" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clc" ∗
      junkCell "clw")
    _ _ ("cld", "cli") (arrayAssn ×ₐ natAssn)
    (subPass N a b (A₀, i₀))

set_option maxHeartbeats 1000000 in
sepref_synth andSelfSynth (N : ℕ) (b A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cld", "cli") ∗
      hnCtxt arrayAssn b "clb" ∗ hnCtxt natAssn N "cln" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clw")
    _ _ ("cld", "cli") (arrayAssn ×ₐ natAssn)
    (andSelfPass N b (A₀, i₀))

set_option maxHeartbeats 1000000 in
sepref_synth subSelfSynth (N : ℕ) (b A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cld", "cli") ∗
      hnCtxt arrayAssn b "clb" ∗ hnCtxt natAssn N "cln" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clc" ∗
      junkCell "clw")
    _ _ ("cld", "cli") (arrayAssn ×ₐ natAssn)
    (subSelfPass N b (A₀, i₀))

-- **The block scan, pinned**: `Csr.scan`'s body — the member read, the
-- mark, the pointer bump — instruction for instruction, the machine's
-- nested `.get` inside `.store` split into `aget` + `aset` and the
-- stored `.lit 1` in the cell `"sv"` (2F/D-d).
#guard scatSynth_impl =
  Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
    ((Com.aget "cw" "xmm" "p").seq
      ((Com.aset "clu" "cw" "sv").seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq Com.skip)))

-- **`andCom`, pinned.**
#guard andSynth_impl =
  Com.while (Cond.lt (Operand.cell "cli") (Operand.cell "cln"))
    ((Com.aget "clx" "cla" "cli").seq
      ((Com.aget "cly" "clb" "cli").seq
        ((Com.binop Lax13Proofs.Imp.Bop.mul "clw" "clx" "cly").seq
          ((Com.aset "cld" "cli" "clw").seq
            ((Com.binop Lax13Proofs.Imp.Bop.add "cli" "cli" "one").seq Com.skip)))))

-- **`subCom`, pinned**: the complement is `1 - b[i]` out of the entry
-- store's `"one"`, and the product follows.
#guard subSynth_impl =
  Com.while (Cond.lt (Operand.cell "cli") (Operand.cell "cln"))
    ((Com.aget "clx" "cla" "cli").seq
      ((Com.aget "cly" "clb" "cli").seq
        ((Com.binop Lax13Proofs.Imp.Bop.sub "clc" "one" "cly").seq
          ((Com.binop Lax13Proofs.Imp.Bop.mul "clw" "clx" "clc").seq
            ((Com.aset "cld" "cli" "clw").seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "cli" "cli" "one").seq Com.skip))))))

-- **The self-reading pair, pinned.** The *only* difference from the two
-- above is the array the first `aget` reads — `"cld"`, the destination
-- itself, in place of `"cla"`. That is 2F/D-c made visible: one cell
-- name, one program, and no aliasing anywhere in the tower's account.
#guard andSelfSynth_impl =
  Com.while (Cond.lt (Operand.cell "cli") (Operand.cell "cln"))
    ((Com.aget "clx" "cld" "cli").seq
      ((Com.aget "cly" "clb" "cli").seq
        ((Com.binop Lax13Proofs.Imp.Bop.mul "clw" "clx" "cly").seq
          ((Com.aset "cld" "cli" "clw").seq
            ((Com.binop Lax13Proofs.Imp.Bop.add "cli" "cli" "one").seq Com.skip)))))

#guard subSelfSynth_impl =
  Com.while (Cond.lt (Operand.cell "cli") (Operand.cell "cln"))
    ((Com.aget "clx" "cld" "cli").seq
      ((Com.aget "cly" "clb" "cli").seq
        ((Com.binop Lax13Proofs.Imp.Bop.sub "clc" "one" "cly").seq
          ((Com.binop Lax13Proofs.Imp.Bop.mul "clw" "clx" "clc").seq
            ((Com.aset "cld" "cli" "clw").seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "cli" "cli" "one").seq Com.skip))))))

/-! ### Negative controls on the pins -/

-- **The block scan writes at the member, not at the pointer.** The
-- transposition — `clu[p] := 1` — is a different program, and it is the
-- one the twin's negative control of §1 refutes on the arena.
#guard scatSynth_impl ≠
  Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
    ((Com.aget "cw" "xmm" "p").seq
      ((Com.aset "clu" "p" "sv").seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq Com.skip)))

-- **The sub-pass is not the and-pass.** They differ in one instruction,
-- and the tool produced both.
#guard subSynth_impl ≠ andSynth_impl

-- **The self-reading pass is not the frame-reading one.**
#guard andSelfSynth_impl ≠ andSynth_impl
#guard subSelfSynth_impl ≠ subSynth_impl

/-- info: 'Lax3Proofs.Refine.ClusterSynth.scatSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms scatSynth

/-- info: 'Lax3Proofs.Refine.ClusterSynth.andSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms andSynth

/-- info: 'Lax3Proofs.Refine.ClusterSynth.subSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms subSynth

/-- info: 'Lax3Proofs.Refine.ClusterSynth.andSelfSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms andSelfSynth

/-- info: 'Lax3Proofs.Refine.ClusterSynth.subSelfSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms subSelfSynth

/-- The block scan's synthesis with the frame the tool computed left
existential — the form a consumer composes with. -/
theorem scatSynth' (e v : ℕ) (idx A₀ : List ℕ) (p₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, p₀) ("clu", "p") ∗
        hnCtxt arrayAssn idx "xmm" ∗ hnCtxt natAssn v "sv" ∗ hnCtxt natAssn e "pend" ∗
        hnCtxt natAssn 1 "one" ∗ junkCell "cw")
      scatSynth_impl Γ' ("clu", "p") (arrayAssn ×ₐ natAssn) (scatPass e v idx (A₀, p₀)) :=
  ⟨_, scatSynth e v idx A₀ p₀⟩

/-- The and-pass's. -/
theorem andSynth' (N : ℕ) (a b A₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cld", "cli") ∗
        hnCtxt arrayAssn a "cla" ∗ hnCtxt arrayAssn b "clb" ∗ hnCtxt natAssn N "cln" ∗
        hnCtxt natAssn 1 "one" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clw")
      andSynth_impl Γ' ("cld", "cli") (arrayAssn ×ₐ natAssn) (andPass N a b (A₀, i₀)) :=
  ⟨_, andSynth N a b A₀ i₀⟩

/-- The sub-pass's. -/
theorem subSynth' (N : ℕ) (a b A₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cld", "cli") ∗
        hnCtxt arrayAssn a "cla" ∗ hnCtxt arrayAssn b "clb" ∗ hnCtxt natAssn N "cln" ∗
        hnCtxt natAssn 1 "one" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clc" ∗
        junkCell "clw")
      subSynth_impl Γ' ("cld", "cli") (arrayAssn ×ₐ natAssn) (subPass N a b (A₀, i₀)) :=
  ⟨_, subSynth N a b A₀ i₀⟩

/-- The self-reading and-pass's. -/
theorem andSelfSynth' (N : ℕ) (b A₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cld", "cli") ∗
        hnCtxt arrayAssn b "clb" ∗ hnCtxt natAssn N "cln" ∗
        hnCtxt natAssn 1 "one" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clw")
      andSelfSynth_impl Γ' ("cld", "cli") (arrayAssn ×ₐ natAssn) (andSelfPass N b (A₀, i₀)) :=
  ⟨_, andSelfSynth N b A₀ i₀⟩

/-- The self-reading sub-pass's. -/
theorem subSelfSynth' (N : ℕ) (b A₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cld", "cli") ∗
        hnCtxt arrayAssn b "clb" ∗ hnCtxt natAssn N "cln" ∗
        hnCtxt natAssn 1 "one" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clc" ∗
        junkCell "clw")
      subSelfSynth_impl Γ' ("cld", "cli") (arrayAssn ×ₐ natAssn) (subSelfPass N b (A₀, i₀)) :=
  ⟨_, subSelfSynth N b A₀ i₀⟩

end Synth

/-! ## 7. Gate — the *synthesized* programs, run

`Ir/Semantics.lean`'s evaluator on the five programs of §6, at §1's
arena. Every answer is the twin's answer, and the twins' answers are the
reference's. -/

section Gate

/-- The block scan's entry store, at centre `c` of §1's arena: the
pointer at the block's start, the bound at its end, the stored value at
`1`. The cluster indicator enters holding the caller's junk — which is
what makes the *load*'s fill visible in the readings below. -/
def sState (c : ℕ) (A : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("p", demoXoff[c]!), ("pend", demoXoff[c + 1]!), ("sv", 1), ("one", 1),
      ("cw", 0)]
    [("clu", A), ("xmm", demoXmem)]

/-- What the synthesized scan leaves in the cluster indicator. -/
def sRun (c : ℕ) (A : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 scatSynth_impl (sState c A)).bind fun p => p.1.arrs "clu"

-- **The load, in the synthesized program**: the fill's zeroes and then
-- the block's marks. Three centres, three blocks, and each answer is
-- the reference indicator of §1.
#guard sRun 0 (List.replicate 6 0) = some (demoClu 0)
#guard sRun 1 (List.replicate 6 0) = some (demoClu 1)
#guard sRun 2 (List.replicate 6 0) = some (demoClu 2)

-- **The twin is the program**, cell for cell, including the aliasing
-- case where the entry array is the caller's junk and not the fill's.
#guard sRun 1 (List.replicate 6 9) = some (scatRun demoXoff[1]! demoXoff[2]! 1 demoXmem
  (List.replicate 6 9))
#guard sRun 1 (List.replicate 6 9) = some [9, 1, 9, 9, 1, 1]

/-- The mask passes' entry store. -/
def mState (a b A : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("cli", 0), ("cln", 6), ("one", 1), ("clx", 0), ("cly", 0), ("clc", 0),
      ("clw", 0)]
    [("cld", A), ("cla", a), ("clb", b)]

def aRun (a b A : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 andSynth_impl (mState a b A)).bind fun p => p.1.arrs "cld"

def bRun (a b A : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 subSynth_impl (mState a b A)).bind fun p => p.1.arrs "cld"

def aSelfRun (b A : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 andSelfSynth_impl (mState [] b A)).bind fun p => p.1.arrs "cld"

def bSelfRun (b A : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 subSelfSynth_impl (mState [] b A)).bind fun p => p.1.arrs "cld"

-- D3: the arena cut down to the cluster.
#guard aRun demoAlv demoCluL (List.replicate 6 7) = some [0, 1, 0, 0, 1, 1]
-- D8: the cluster-restricted arena with the batch killed.
#guard bRun [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7) = some [0, 0, 0, 0, 1, 0]
-- D7d and D10, self-reading, at the destination's own entry contents.
#guard aSelfRun demoBat [1, 1, 1, 0, 0, 1] = some [0, 1, 0, 0, 0, 1]
#guard bSelfRun demoBat [0, 1, 0, 0, 1, 1] = some [0, 0, 0, 0, 1, 0]

-- **The twins are the programs.**
#guard aRun demoAlv demoCluL (List.replicate 6 7)
  = some (binRun 6 andG demoAlv demoCluL (List.replicate 6 7))
#guard bRun [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7)
  = some (binRun 6 subG [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7))
#guard aSelfRun demoBat [1, 1, 1, 0, 0, 1] = some (binSelfRun 6 andG demoBat [1, 1, 1, 0, 0, 1])
#guard bSelfRun demoBat [0, 1, 0, 0, 1, 1] = some (binSelfRun 6 subG demoBat [0, 1, 0, 0, 1, 1])

/-! ### Negative controls -/

-- **The scan does not run past its block.** Centre `2`'s block is the
-- single member `2`; a scan to the array's end would mark more.
/--
error: Expression
  decide (sRun 2 (List.replicate 6 0) = some [1, 1, 1, 1, 1, 1])
did not evaluate to `true`
-/
#guard_msgs in
#guard sRun 2 (List.replicate 6 0) = some [1, 1, 1, 1, 1, 1]

-- **The two mask passes are not each other**, in the evaluator too.
/--
error: Expression
  decide (bRun [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7) = aRun [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7))
did not evaluate to `true`
-/
#guard_msgs in
#guard bRun [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7)
  = aRun [0, 1, 0, 0, 1, 1] demoBat (List.replicate 6 7)

end Gate

/-! ## 8. `clusterLoad`, composed — the pass the touched-only question is
about

D2a, D2b and D2c in one program: the fill of the carrier, the two offset
reads that bound the block, and the scan of the block. This is
`RamDriver.clusterLoad j` entire, and it is the composition the wave was
for, because it is where the `Θ(n)` half and the touched-only half meet.

Two tool facts it exercises, neither of which the ordering phase needed:
a loop whose **bound and start counter are both computed by preceding
operations** (R2D/D-b's shape, at a loop the tool synthesizes itself
rather than at a registered leaf), and a **bound-tuple split followed by
a re-pair** — the fill delivers `(array, counter)`, the scan wants
`(array, pointer)`, and the counter is dropped. -/

section Load

/-- **The cluster load, abstractly.** `mopBinop .add c 1` and not
`mopSucc c`: the machine's `Csr.loadRow` reads `o[v+1]` without
destroying `v`, and the in-place successor would (2F/D-b). -/
noncomputable def clusterLoad0 (n c : ℕ) (xoff idx A₀ : List ℕ) (i₀ : ℕ) :
    NRest FS ECost :=
  bindT (OrderSynth.fillPass n 0 (A₀, i₀)) fun s =>
    bindT (mopAget xoff c) fun p₀ =>
      bindT (mopBinop .add c 1) fun c₁ =>
        bindT (mopAget xoff c₁) fun e =>
          bindT (mopPair s.1 p₀) fun st => scatPass e 1 idx st

set_option maxHeartbeats 1000000 in
sepref_synth loadSynth (n c : ℕ) (xoff idx A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("clu", "cli") ∗
      hnCtxt natAssn 0 "zero" ∗ hnCtxt natAssn n "cln" ∗
      hnCtxt arrayAssn xoff "xof" ∗ hnCtxt natAssn c "cur" ∗
      hnCtxt arrayAssn idx "xmm" ∗ hnCtxt natAssn 1 "sv" ∗
      hnCtxt natAssn 1 "one" ∗
      junkCell "p" ∗ junkCell "ct" ∗ junkCell "pend" ∗ junkCell "cw")
    _ _ ("clu", "p") (arrayAssn ×ₐ natAssn)
    (clusterLoad0 n c xoff idx A₀ i₀)

-- **`RamDriver.clusterLoad j`, pinned** — the fill, the two offset
-- reads, and the block scan, in the machine's own order.
--
-- **2F/D-e: the increment cell is `"sv"` and not `"one"`.** Two cells
-- of the entry store hold `1` — the scan's stored value and the
-- successor's operand — and the frame inferencer takes the *first*
-- conjunct that matches, which is `"sv"`. So the composed program never
-- mentions `"one"` at all. It is sound (the cell holds `1`), it is
-- invisible in the abstract layer, and it is a fact the integration
-- wave has to know: an entry store that pins only `"one"` to `1` and
-- leaves `"sv"` at the caller's junk runs a *different* program. Junk
-- destinations are consumed in written order (2E/D-d); **owned cells of
-- equal value are consumed in context order**, which is its analogue
-- and this wave's own finding.
#guard loadSynth_impl =
  (Com.while (Cond.lt (Operand.cell "cli") (Operand.cell "cln"))
      ((Com.aset "clu" "cli" "zero").seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "cli" "cli" "sv").seq Com.skip))).seq
    ((Com.aget "p" "xof" "cur").seq
      ((Com.binop Lax13Proofs.Imp.Bop.add "ct" "cur" "sv").seq
        ((Com.aget "pend" "xof" "ct").seq
          (Com.skip.seq
            (Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
              ((Com.aget "cw" "xmm" "p").seq
                ((Com.aset "clu" "cw" "sv").seq
                  ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "sv").seq Com.skip))))))))

-- **The row load is three instructions.** 2F/D-b, in the tool's own
-- output: `aget`, `add`, `aget`, where the machine writes two `.assign`s.
#guard loadSynth_impl ≠
  (Com.while (Cond.lt (Operand.cell "cli") (Operand.cell "cln"))
      ((Com.aset "clu" "cli" "zero").seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "cli" "cli" "sv").seq Com.skip))).seq
    ((Com.aget "p" "xof" "cur").seq
      ((Com.aget "pend" "xof" "cur").seq
        (Com.skip.seq
          (Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
            ((Com.aget "cw" "xmm" "p").seq
              ((Com.aset "clu" "cw" "sv").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "sv").seq Com.skip)))))))

/-- info: 'Lax3Proofs.Refine.ClusterSynth.loadSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms loadSynth

/-- The composed load's synthesis with the frame left existential. -/
theorem loadSynth' (n c : ℕ) (xoff idx A₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("clu", "cli") ∗
        hnCtxt natAssn 0 "zero" ∗ hnCtxt natAssn n "cln" ∗
        hnCtxt arrayAssn xoff "xof" ∗ hnCtxt natAssn c "cur" ∗
        hnCtxt arrayAssn idx "xmm" ∗ hnCtxt natAssn 1 "sv" ∗
        hnCtxt natAssn 1 "one" ∗
        junkCell "p" ∗ junkCell "ct" ∗ junkCell "pend" ∗ junkCell "cw")
      loadSynth_impl Γ' ("clu", "p") (arrayAssn ×ₐ natAssn)
      (clusterLoad0 n c xoff idx A₀ i₀) :=
  ⟨_, loadSynth n c xoff idx A₀ i₀⟩

/-! ### The composed load, run

The entry store the pin above demands — `"sv"` at `1`, `"zero"` at `0` —
and §1's arena. What comes out is the reference indicator of the block,
with the carrier zeroed underneath it. -/

def lState (c : ℕ) (A : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("cli", 0), ("cln", 6), ("zero", 0), ("sv", 1), ("one", 1), ("cur", c),
      ("p", 0), ("ct", 0), ("pend", 0), ("cw", 0)]
    [("clu", A), ("xof", demoXoff), ("xmm", demoXmem)]

def lRun (c : ℕ) (A : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 loadSynth_impl (lState c A)).bind fun p => p.1.arrs "clu"

-- the three blocks, out of the caller's junk, through the fill
#guard lRun 0 (List.replicate 6 9) = some (demoClu 0)
#guard lRun 1 (List.replicate 6 9) = some (demoClu 1)
#guard lRun 2 (List.replicate 6 9) = some (demoClu 2)

-- **the twin is the composed program**, fill and scan together
#guard lRun 1 (List.replicate 6 9) = some (loadRun 6 demoXoff[1]! demoXoff[2]! demoXmem
  (List.replicate 6 9))

-- **negative control: the fill is load-bearing.** Without it the
-- caller's junk survives outside the block, and the two answers differ.
/--
error: Expression
  decide (lRun 1 (List.replicate 6 9) = some (scatRun demoXoff[1]! demoXoff[2]! 1 demoXmem (List.replicate 6 9)))
did not evaluate to `true`
-/
#guard_msgs in
#guard lRun 1 (List.replicate 6 9)
  = some (scatRun demoXoff[1]! demoXoff[2]! 1 demoXmem (List.replicate 6 9))

end Load

/-! ## 9. The composed load's bound — the touched-only statement

The three operations of §8's straight line, bounded, and then the two
loops' exports chained through them. What comes out is the pass's cost
as `12·n + 15·m + 19` with `m` the **block's** size, and its
postcondition in the two halves `RamDriverCluster.BatchData` needs. -/

section LoadSpec

theorem mopAget_le {xs : List ℕ} {i : ℕ} (h : i < xs.length) :
    mopAget xs i ≤ NRest.spec (fun u => u = xs[i]!) (fun _ => liftACost (cu Currency.aget)) := by
  rw [mopAget_def, NRest.assert_pos h, NRest.returnT_bindT, liftACost_cu]
  exact consume_returnT_le_spec rfl le_rfl

theorem mopAdd_le (m k : ℕ) :
    mopBinop .add m k ≤ NRest.spec (fun u => u = m + k) (fun _ => liftACost (cu Currency.add)) := by
  rw [mopBinop_def, liftACost_cu]
  simp only [Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add]
  exact consume_returnT_le_spec rfl le_rfl

theorem mopPair_le {α β : Type} (a : α) (b : β) :
    mopPair a b ≤ NRest.spec (fun u => u = (a, b)) (fun _ => liftACost (cu Currency.skip)) := by
  rw [mopPair_def, liftACost_cu]
  exact consume_returnT_le_spec rfl le_rfl

/-- **The load's price**, in the nesting the chain produces it in: the
fill over the carrier, the three straight-line operations, and the scan
over the block. -/
def clusterLoadC (n m : ℕ) : ACost String ℕ :=
  (n • iter OrderSynth.fillC + cu Currency.«while») +
    (cu Currency.aget +
      (cu Currency.add +
        (cu Currency.aget +
          (cu Currency.skip + (m • iter scatC + cu Currency.«while»)))))

/-- **The cluster load, bounded.** `m` — the second argument of the cost
— is `xoff[c+1] - xoff[c]`, the size of *this cluster's block*, and it
is the only place the cost grows with anything the pass touched. The
`12·n` in front of it is the fill, and 2F/D-a is that it is there. -/
theorem clusterLoad0_le {n c L : ℕ} {xoff idx A₀ : List ℕ} (hA : A₀.length = L) (hnL : n ≤ L)
    (hc : c + 1 < xoff.length) (hpe : xoff[c]! ≤ xoff[c + 1]!)
    (he : xoff[c + 1]! ≤ idx.length) (hlt : ∀ q, q < xoff[c + 1]! → idx[q]! < L) :
    clusterLoad0 n c xoff idx A₀ 0
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            (∀ q, xoff[c]! ≤ q → q < xoff[c + 1]! → t.1[idx[q]!]! = 1) ∧
            (∀ w, w < n → (∀ q, xoff[c]! ≤ q → q < xoff[c + 1]! → idx[q]! ≠ w) → t.1[w]! = 0))
          (fun _ => liftACost (clusterLoadC n (xoff[c + 1]! - xoff[c]!))) := by
  have hcl : c < xoff.length := by omega
  rw [clusterLoadC, liftACost_add]
  refine le_trans (NRest.bindT_mono (OrderSynth.fillPass_spec hA hnL) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro s ⟨hs1, hs2⟩
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopAget_le hcl) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro p₀ rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopAdd_le c 1) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro c₁ rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopAget_le hc) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro e rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopPair_le s.1 xoff[c]!) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro st rfl
  refine le_trans (scatPass_spec (A₀ := s.1) hs1 hpe he hlt)
    (spec_mono ?_ (fun _ _ => le_rfl))
  rintro t ⟨t1, t2, t3⟩
  refine ⟨t1, t2, fun w hw hnw => ?_⟩
  rw [t3 w hnw, hs2 w, if_pos hw]

/-! ### The load's cost, cashed -/

theorem cash_scatC : Codegen.cash (iter scatC) = 15 := by decide +kernel

theorem cash_andC : Codegen.cash (iter andC) = 22 := by decide +kernel

theorem cash_subC : Codegen.cash (iter subC) = 26 := by decide +kernel

theorem cash_aget : Codegen.cash (cu Currency.aget) = 3 := by decide +kernel

theorem cash_add : Codegen.cash (cu Currency.add) = 4 := by decide +kernel

theorem cash_skip : Codegen.cash (cu Currency.skip) = 1 := by decide +kernel

/-- The load's cost in IMP+ time units. -/
def clusterLoadK (n m : ℕ) : ℕ := 12 * n + 15 * m + 19

theorem cash_clusterLoadC (n m : ℕ) :
    Codegen.cash (clusterLoadC n m) = clusterLoadK n m := by
  rw [clusterLoadC, clusterLoadK]
  simp only [Codegen.cash_add, BfsQSynth.cash_nsmul, OrderSynth.cash_fillC, cash_scatC,
    OrderSynth.cash_while, cash_aget, cash_add, cash_skip]
  ring

end LoadSpec

/-! ## 10. The costs, against the hand-walked passes

Unlike the ordering phase's, the descent's baseline numbers are not a
budget: `Lax3Proofs.RamDriverCluster` proves each flat pass at an exact
cost, and `RamDriverDescend.clusterLoad_spec` proves the load at one. So
the comparison is exact on both sides.

| pass | hand-walked | tower | per cell |
|---|---|---|---|
| `fillCom_spec` | `11·N + 6` | `12·N + 4` | `+1` |
| `copyCom_spec` | `12·N + 6` | `15·N + 4` | `+3` |
| `andCom_spec` | `15·N + 6` | `22·N + 4` | `+7` |
| `subCom_spec` | `17·N + 6` | `26·N + 4` | `+9` |
| `andSelfCom_spec` | `15·N + 6` | `22·N + 4` | `+7` |
| `clusterLoad_spec` | `16·n² + 11·n + 24` | `12·n + 15·m + 19` | **see below** |

The per-cell excess is the same deviation everywhere and it is not a
regression in the algorithm: the machine's cell expression is *one*
instruction priced by its syntactic size, and the IR has no nested
operand, so a cell expression of `k` reads becomes `k` `aget`s plus one
operation per connective. `andCom`'s `+7` is exactly one `aget` (`3`)
and one `mul` (`4`); `subCom`'s `+9` is those and the `sub`'s
truncation minus the two units the machine's constant folding of `.lit
1` saves. Every one of the six is accounted for by 2E/D-b's rule, and
none by a change of algorithm.

**The load is the other direction, and it is the wave's headline.** The
hand-walked budget is *quadratic per cluster* — `16·n²` — because the
walk bounds the block by the whole cluster arena `Xmem`, whose length is
`n·n`; the tower's is `12·n + 15·m` with `m` the block's own size, and
the block sizes of a level sum to the cover's write pointer. Summed over
the centres of one level, that is

    hand-walked   Θ(n³)      (16·n² per centre)
    tower         Θ(n·k) + Θ(xp)   with k the number of centres

so the touched-only half of the pass is *proved* touched-only here for
the first time, and what is left of the `n²` is the fill, one `12·n` per
centre (2F/D-a). -/

section Cash

-- the two figures side by side at §1's arena — six vertices, and the
-- middle block's three members
#guard clusterLoadK 6 3 = 136
#guard 16 * (6 * 6) + 11 * 6 + 24 = 666

-- and the shape of the difference, at a carrier ten times as wide with
-- the same block: the tower's number grows linearly, the baseline's
-- quadratically
#guard clusterLoadK 60 3 = 784
#guard 16 * (60 * 60) + 11 * 60 + 24 = 58284

end Cash

/-! ## 11. What `ClusterStepImplements` asks for, and what is here

`RamDriverCluster.DescendStep` is the obligation D1–D10 discharge
together. This file does **not** discharge it: it derives six of its
passes and leaves `expandCom`, the search leaf and the padding to the
integration wave. What a consumer can take from here today is

* `scatPass_spec` — D2c and A4, at a bound that is the block's size;
* `andPass_spec`, `subPass_spec` — D3, D8, D9, C1;
* `andSelfPass_spec`, `subSelfPass_spec` — D7d, D10 (2F/D-c);
* `clusterLoad0_le` + `loadSynth` — D2a+D2b+D2c as one program, with
  its cost and both halves of `BatchData`'s indicator condition;
* the five synthesized programs, pinned instruction for instruction.

The postconditions are stated in `List`/`[·]!` terms and not in
`arrOf`/`markSet` terms. Turning `∀ q, xoff[c]! ≤ q → q < xoff[c+1]! →
t.1[idx[q]!]! = 1` into `markSet n Xa = {v | InCluster …}` is
`RamDriverDescend.clusterLoad_spec`'s second half and is *mathematics
already landed* — it is consumed by the integration wave, not re-proved
here (the same discipline `OrderSynth` §11 states for `OrdersBy`).

## 12. Debts, named

**2F/N-1 — `expandCom`, the nested expansion, is not derived.** It is
the only underived *shape* left on the `C0` path after this wave: an
outer loop over the carrier whose body branches on the mask and, in the
true arm, loads a CSR row and runs an inner scan with a hit flag. Per
cluster the descent runs it `2·cap` times (D6) and the colouring
`mb·cap + (sigL+1)·cap` times (C2, C3). This is **not** a matcher gap:
`ElimSynth3.elimLoop` is the same shape at a wider state and it
translates, so what stands between here and there is budget, estimated
at 400–600 lines and one wide-state synthesis (≈ 90 s at eleven
components; this one has six).

**2F/N-2 — `enumBatch` needs a deviation, and the deviation needs a
refutation first.** The compaction loop writes `wa` *and* bumps `bc`
under a branch, and both arms of an `irIf` must deliver the same
destination (2B′/D-b). `CoverSynth.emitF`'s idiom — write
unconditionally, let the branch decide only the value — does not apply
unchanged, because here it is the *index* that is conditional. The
shape that does work is `wa[bc] := z` unconditionally together with
`bc := bc + bat[z]`: a non-hit writes a cell that the next hit, or the
padding loop, overwrites. Its answer is the machine's **provided the
batch indicator is `0`/`1`** — §1's negative control on `subG` is the
same hypothesis at a different site — and the padding loop's first
write is at `bc`, which is what closes the argument. Nothing of this is
proved here; it is a proposal with its refutation obligation attached.

**2F/N-3 — the readback may not be a tower leaf at all.** `readbackCom`'s
body is a straight line of `|tablesAt …|` stores whose values are
`bcExpr` of a *formula-indexed* boolean combination — program text
generated by recursion on a construction-time object, exactly like
`botCom`. The pinned boundary decision retains name-generating
recursion; the readback is the first pass on the `C0` path where it is
not obvious which side of that line it falls on. The integration wave
should decide it before anyone budgets for it.

**2F/N-4 — the guarded engine call (A4) is untried.** `ancestorStep`
wraps `extractPathCom; markPath` in an `.ite` on a scalar. An `irIf`
whose arm *contains a registered leaf* is a shape the tower has not been
asked for; `markPath` itself is derived here (it is `scatPass`), so what
is untried is only the guard around it.

**2F/N-5 — no `BRefine` coverage.** None of the five passes carries a
bounded-word refinement: every bound (`n`, `pend`, `mb`) is a runtime
cell and enters as an `ℕ`. `ScatterSynth` §15's `ScanBounded` pattern
applies to the two-level passes, and the flat ones would pay the
≈ 50-line tax each. Deferred, deliberately: the wave's budget went to
the reduction map and to the load.

## 13. Axioms -/

section Axioms

/-- info: 'Lax3Proofs.Refine.ClusterSynth.scatPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms scatPass_spec

/-- info: 'Lax3Proofs.Refine.ClusterSynth.andPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms andPass_spec

/-- info: 'Lax3Proofs.Refine.ClusterSynth.subPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms subPass_spec

/-- info: 'Lax3Proofs.Refine.ClusterSynth.andSelfPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms andSelfPass_spec

/-- info: 'Lax3Proofs.Refine.ClusterSynth.subSelfPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms subSelfPass_spec

/-- info: 'Lax3Proofs.Refine.ClusterSynth.clusterLoad0_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms clusterLoad0_le

end Axioms

/-! ## 14. Telemetry (the wave's acceptance numbers)

| item | number |
|---|---|
| passes mapped (D1–D10, A1–A4, C1–C3, phases 1–6) | 23 |
| passes derived here | 5 + 1 composed |
| syntheses | 6, all at 1 000 000 heartbeats |
| file wall clock, cold | ≈ 21 s (twins alone ≈ 3 s; the five flat syntheses and their walks ≈ 13 s; §8's composition ≈ 1 s) |
| widest state | 2 components (every pass is `(array, counter)`) |
| deepest composition | 6 operations, two loops (§8) |
| `#guard`s | 61 |
| `#guard_msgs` blocks (negative controls + axiom checks) | 15 |
| refuted authored statements | 0 |
| sorries | 0 |
| axioms | `propext`, `Classical.choice`, `Quot.sound` only |

The measurement 2F was asked to take: **a composed program whose second
loop's start counter and bound are both computed by preceding
operations translates** (§8), at a cost of no extra tool wave — the
T1 bound-tuple split carries it, including the drop of the fill's
counter on the way into the scan's state. -/

end Lax3Proofs.Refine.ClusterSynth
