import Lax3Proofs.RamElim
import Lax13Proofs.Refine.Examples.BfsQSynth

/-!
# P2 satellite 2B — the elimination engine, re-derived through the tower

`Lax3Proofs.RamElim` is the campaign's one *ordering* engine: greedy
minimum-degree (Matula–Beck) elimination over a masked block structure,
hand-walked against IMP+ in 3,712 lines. This file re-derives the same
program at the refinement tower's layers — an abstract `NRest` program
over `List ℕ`, its cost, and the synthesized `Ir.Com` — in the export
vocabulary the driver stack already consumes.

## How the re-zeroing defect class dies (the plan's charter for 2B)

The frozen stack carries two repairs that exist **only** because the
machine program mutates cells it did not create:

* `RamDriver.elimRezeroCom` and its bridge pair
  (`RamDriverCompose.elimRank_spec` / `elimCert_spec`). `orderCom` runs
  `RamElim.elimCom` twice. The first call leaves `elm[w] = 1` at every
  extracted vertex and `bh` holding its own bucket heads; the second
  call therefore pops every slot, finds it flagged, drops it, never
  moves `cnt`, climbs `mind` past `n + 1`, and *gets stuck* — the
  obligation was refuted, not merely unproved, and the repair was two
  extra flat fills between the calls.
* The `ElimMem` conjunct debt. `RamElim.ElimMem` drops the rank bound
  `∀ v < n, R v < n` that `RamElim.AfterLoop` and `AfterOff` both carry
  and `elimLoop_spec` proves; `RamDriverCompose` had to re-run all five
  phase walks (`elimRank_spec`, ≈120 lines) to get it back for the rank
  inversion.

**Both die at the abstract level, and neither is repaired here — there
is nothing to repair.**

*The first* dies because a program at this layer takes **values**, not
dirty machine cells. `elimTw` (§1.2) — and the `NRest` program it is
the step function of — is a function of `n`, `ns`, `W`, `off`, `tgt`
and `alv`, and **nothing else**: every scratch array it works in is
built inside it, `elm`, `bh`, `bv`, `bn`, `deg`, `idg` and `ifl` all
entering their loops as `List.replicate _ 0` that the engine itself
produced. Calling it twice is calling a function twice, and the second
call cannot see the first call's `elm`. `ElimPre`'s two *value* clauses
— `elm` zeroed, `bh` zeroed — therefore have no counterpart in an
abstract precondition at all: they are not weakened, they are absent.
`elimRezeroCom` has nothing to re-zero and the `n = 1` counterexample
is not expressible. What a caller still owns is *length*, which is the
one thing an IMP+ run cannot change anyway, and that is what `W` is.

This is a property of the *layer*, and it therefore holds for the
phases this satellite does not carry as well as for the one it does;
it is not contingent on any particular phase having been synthesized.
§3's `degPass` is the worked instance: its precondition is
`deg₀.length = n` and the block structure's `Shape`, and there is no
clause anywhere about what `deg₀` *contains*.

*The second* dies because the rank bound belongs in the export's
postcondition from the start. `RamElim.Elim.rank_lt` — a clause of the
loop invariant the old walk already carries, and which
`RamElim.AfterLoop`/`AfterOff` both propagate — is available at the
exit of the elimination loop; the only reason the old `ElimMem` lost it
is that `ElimMem` was written before the rank inversion existed, so a
tower export has no reason to repeat the omission. Since this
satellite retains the elimination loop (§8), the conjunct is *named*
here rather than proved here, and it is named where the next wave must
put it: in the postcondition of the elimination loop's own `≤ spec`,
beside the certificate.

The one clause the abstract program still cannot delete is the *width*
`W`: the caller allocates the bucket arena and the in-list targets once
and reuses them, so their length is data of the caller. That is a
length, not a value, and it is `ElimPre`'s own design (`ns ≤ W`).

## What is in this file, and what is not (FLAG 2, §8)

* **§1 — the falsification gate.** A computable twin of the *whole*
  engine, all five phases slot for slot, differential-tested against
  `RamElim.Demo`'s two published runs of the compiled machine program —
  the ranks, the bound `kmax`, the in-list offsets and the in-list
  targets, mask on and mask off, plus the block readings — with four
  negative controls.
* **§2 — two operations restated locally**: the in-place `+1`
  (P7/D-bb) and its companion `mopKeep`, which is what an empty `else`
  needs at this layer.
* **§3 — the degree pass at the `NRest` layer**: the abstract program,
  the per-slot and per-row prices, both loop bounds (the outer one
  amortized on a two-currency energy, the rows tiling the target
  array), and the two `LOOP_VARIANT`s.
* **§4 — the synthesis.** The row scan reaches a deep `Ir.Com` and is
  pinned; §4.1 records, with measurements, the translate-driver stall
  that keeps the *outer* pass from doing the same.
* **§5 — the bridge** into `RamElim`'s own vocabulary: what the pass
  leaves is `RamElim.adeg`, which is where `CsrSimple`'s `nodup` clause
  is spent.
* **§6 — the cost, cashed**: `36·n + 23·ns + 4`, computed by
  `decide +kernel`, against the baseline's hand-tuned `48·n + 44·ns +
  10` for the same phase.
* **§7 — axioms**, **§8 — FLAG 2**: what is retained and why.

## House traps observed

`omega` is blind through `Ir.Val`, so every arithmetic obligation is
bound at `ℕ` first; `decide +kernel` for the cost numerals; never
`simp [Codegen.embed]`; the junk cells are consumed in written order.
-/

namespace Lax3Proofs.Refine.ElimSynth

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen

/-! ## 1. Refute before prove

The whole engine as a computable function over `List ℕ`, written slot
for slot against `RamElim`'s five phases, and checked against the two
runs `RamElim.Demo` publishes — which are runs of the *compiled machine
program*, not of any abstraction of it.

Every step function here is the step the abstract program of §2 is
proved equal to, so what is checked is the abstract program.

The engine's known hot spots, and where each is checked:

* **the rank bound** — the rank counts *down*, so the first vertex
  extracted gets `n - 1`; a run that counts up would report the same
  `kmax` and the *reversed* orientation. The `rnk` readings and the
  in-list blocks both discriminate.
* **degree counting under repeated targets** — `CsrSimple`'s `nodup`
  clause exists because a row naming a neighbour twice double-counts
  into `deg`. §1.3 exhibits the double count on a repeat row.
* **in-place aliasing** — the bucket push reads `bh[d]` *before*
  writing it, and the row scan decrements `deg[u]` *before* reading it
  back for the new bucket. §1.3 checks both orders against their
  transpositions.
-/

section Twin

/-! ### 1.1 The five phases, as functions -/

/-- One slot of the counting scan: `(c, j)`. -/
def degSlotTw (tgt alv : List ℕ) : ℕ × ℕ → ℕ × ℕ :=
  fun s => (if 0 < alv[tgt[s.2]!]! then s.1 + 1 else s.1, s.2 + 1)

/-- The counting scan of one row, run to its end. -/
def degScanTw (tgt alv : List ℕ) (jend : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | fuel + 1, s =>
    if s.2 < jend then degScanTw tgt alv jend fuel (degSlotTw tgt alv s) else s

/-- One vertex's degree in the arena: `(deg, i)`. A dead vertex is
isolated, so its degree is zero whatever its row says. -/
def degRowTw (off tgt alv : List ℕ) : List ℕ × ℕ → List ℕ × ℕ :=
  fun s =>
    let c := (degScanTw tgt alv off[s.2 + 1]! (off[s.2 + 1]! - off[s.2]!) (0, off[s.2]!)).1
    (if 0 < alv[s.2]! then s.1.set s.2 c else s.1.set s.2 0, s.2 + 1)

/-- Every vertex's degree. -/
def initDegTw (n : ℕ) (off tgt alv : List ℕ) : ℕ → List ℕ × ℕ → List ℕ × ℕ
  | 0, s => s
  | fuel + 1, s =>
    if s.2 < n then initDegTw n off tgt alv fuel (degRowTw off tgt alv s) else s

/-- The bucket arena's state: heads, slot vertices, slot links, and the
next free slot. Slot `0` is the sentinel, so an empty bucket reads `0`
and no bucket has to be initialised. -/
abbrev BSt : Type := List ℕ × List ℕ × List ℕ × ℕ

/-- Push the vertex `x` onto the bucket `d`: one fresh slot, linked in
front of the head. The head is **read before it is written** — the
aliasing this file's §1.3 checks. -/
def pushTw (b : BSt) (d x : ℕ) : BSt :=
  (b.1.set d b.2.2.2, b.2.1.set b.2.2.2 x, b.2.2.1.set b.2.2.2 b.1[d]!, b.2.2.2 + 1)

/-- One vertex, put in the bucket of its degree: `(b, i)`. -/
def initBuckRowTw (deg : List ℕ) : BSt × ℕ → BSt × ℕ :=
  fun s => (pushTw s.1 deg[s.2]! s.2, s.2 + 1)

/-- Every vertex, bucketed. -/
def initBuckTw (n : ℕ) (deg : List ℕ) : ℕ → BSt × ℕ → BSt × ℕ
  | 0, s => s
  | fuel + 1, s => if s.2 < n then initBuckTw n deg fuel (initBuckRowTw deg s) else s

/-- The elimination loop's state: the degrees, the elimination flags,
the ranks, the recorded extraction degrees, the bucket arena, and the
three scalars `cnt`, `mind`, `kmax`. -/
structure ESt where
  /-- Current degrees in the arena. -/
  deg : List ℕ
  /-- Elimination flags. -/
  elm : List ℕ
  /-- The ranks handed out so far. -/
  rnk : List ℕ
  /-- The extraction degrees recorded so far. -/
  idg : List ℕ
  /-- The lazily deleted bucket stacks. -/
  bk : BSt
  /-- How many vertices have been eliminated. -/
  cnt : ℕ
  /-- The pointer at the smallest bucket that can still be nonempty. -/
  mind : ℕ
  /-- The largest extraction degree so far. -/
  kmax : ℕ
  deriving Repr, DecidableEq

/-- One slot of the row of the vertex being eliminated: a neighbour
still in the arena loses one from its degree and is pushed into its new
bucket. The degree is **decremented before it is read back** for the
new bucket — the second aliasing §1.3 checks. -/
def decSlotTw (tgt alv : List ℕ) (s : ESt × ℕ) : ESt × ℕ :=
  let u := tgt[s.2]!
  let e := s.1
  if 0 < alv[u]! ∧ e.elm[u]! < 1 then
    let deg' := e.deg.set u (e.deg[u]! - 1)
    ({ e with deg := deg', bk := pushTw e.bk deg'[u]! u }, s.2 + 1)
  else (e, s.2 + 1)

/-- The row scan of an extraction, run to the end of the row. -/
def decScanTw (tgt alv : List ℕ) (jend : ℕ) : ℕ → ESt × ℕ → ESt × ℕ
  | 0, s => s
  | fuel + 1, s =>
    if s.2 < jend then decScanTw tgt alv jend fuel (decSlotTw tgt alv s) else s

/-- Eliminate the vertex `w`: stamp it with the next rank *down*,
record its extraction degree, scan its row (a dead vertex has none),
and drop the pointer by one. -/
def elimVertexTw (n : ℕ) (off tgt alv : List ℕ) (e : ESt) (w : ℕ) : ESt :=
  let e1 : ESt :=
    { e with elm := e.elm.set w 1, rnk := e.rnk.set w (n - 1 - e.cnt),
             idg := e.idg.set w e.mind, cnt := e.cnt + 1,
             kmax := if e.kmax < e.mind then e.mind else e.kmax }
  let e2 : ESt :=
    if 0 < alv[w]! then
      (decScanTw tgt alv off[w + 1]! (off[w + 1]! - off[w]!) (e1, off[w]!)).1
    else e1
  { e2 with mind := e2.mind - 1 }

/-- One turn: bump the pointer over an empty bucket, or pop the head
slot of the bucket it names — and eliminate its vertex unless the slot
is stale. -/
def elimTurnTw (n : ℕ) (off tgt alv : List ℕ) (e : ESt) : ESt :=
  if e.bk.1[e.mind]! = 0 then { e with mind := e.mind + 1 }
  else
    let p := e.bk.1[e.mind]!
    let w := e.bk.2.1[p]!
    let e' : ESt := { e with bk := (e.bk.1.set e.mind e.bk.2.2.1[p]!, e.bk.2.1, e.bk.2.2.1,
                                     e.bk.2.2.2) }
    if e'.elm[w]! < 1 ∧ e'.deg[w]! = e'.mind then elimVertexTw n off tgt alv e' w else e'

/-- The elimination, turn after turn until every vertex has a rank. -/
def elimLoopTw (n : ℕ) (off tgt alv : List ℕ) : ℕ → ESt → ESt
  | 0, e => e
  | fuel + 1, e =>
    if e.cnt < n then elimLoopTw n off tgt alv fuel (elimTurnTw n off tgt alv e) else e

/-- One vertex's block, opened: `(ioff, ifl, s, i)`. -/
def offRowTw (idg : List ℕ) : List ℕ × List ℕ × ℕ × ℕ → List ℕ × List ℕ × ℕ × ℕ :=
  fun t =>
    let s' := t.2.2.1 + idg[t.2.2.2]!
    (t.1.set (t.2.2.2 + 1) s', t.2.1.set t.2.2.2 t.2.2.1, s', t.2.2.2 + 1)

/-- The offsets of the in-neighbour lists: a running sum. -/
def offPassTw (n : ℕ) (idg : List ℕ) :
    ℕ → List ℕ × List ℕ × ℕ × ℕ → List ℕ × List ℕ × ℕ × ℕ
  | 0, t => t
  | fuel + 1, t => if t.2.2.2 < n then offPassTw n idg fuel (offRowTw idg t) else t

/-- One slot of the fill: an arc of the arena is written into the block
of its endpoint of larger rank — the one eliminated first. -/
def fillSlotTw (tgt alv rnk : List ℕ) (i : ℕ) :
    List ℕ × List ℕ × ℕ → List ℕ × List ℕ × ℕ :=
  fun t =>
    let u := tgt[t.2.2]!
    if 0 < alv[u]! ∧ rnk[u]! < rnk[i]! then
      (t.1.set t.2.1[i]! u, t.2.1.set i (t.2.1[i]! + 1), t.2.2 + 1)
    else (t.1, t.2.1, t.2.2 + 1)

/-- The fill's row scan. -/
def fillScanTw (tgt alv rnk : List ℕ) (i jend : ℕ) :
    ℕ → List ℕ × List ℕ × ℕ → List ℕ × List ℕ × ℕ
  | 0, t => t
  | fuel + 1, t =>
    if t.2.2 < jend then fillScanTw tgt alv rnk i jend fuel (fillSlotTw tgt alv rnk i t) else t

/-- One vertex's in-neighbours, written out: `(itg, ifl, i)`. -/
def fillRowTw (off tgt alv rnk : List ℕ) :
    List ℕ × List ℕ × ℕ → List ℕ × List ℕ × ℕ :=
  fun t =>
    let i := t.2.2
    let r :=
      if 0 < alv[i]! then
        fillScanTw tgt alv rnk i off[i + 1]! (off[i + 1]! - off[i]!) (t.1, t.2.1, off[i]!)
      else (t.1, t.2.1, off[i]!)
    (r.1, r.2.1, i + 1)

/-- Every vertex's block, written out. -/
def fillPassTw (n : ℕ) (off tgt alv rnk : List ℕ) :
    ℕ → List ℕ × List ℕ × ℕ → List ℕ × List ℕ × ℕ
  | 0, t => t
  | fuel + 1, t =>
    if t.2.2 < n then fillPassTw n off tgt alv rnk fuel (fillRowTw off tgt alv rnk t) else t

/-! ### 1.2 The whole engine

The five phases in sequence, each handed the fresh scratch it needs.
Nothing here is a caller's array: every scratch list is built by
`elimTw` itself, which is the whole of §0's first argument. -/

/-- The engine's four answers: the ranks, the bound, the in-list
offsets, the in-list targets. -/
structure ETw where
  /-- The elimination ranking. -/
  rnk : List ℕ
  /-- The degeneracy bound the run achieved. -/
  kmax : ℕ
  /-- The offsets of the in-neighbour lists. -/
  ioff : List ℕ
  /-- The in-neighbour lists themselves. -/
  itg : List ℕ
  deriving Repr, DecidableEq

/-- Fuel enough for every loop of the engine: the elimination makes at
most one bump per bucket, one pop per slot ever pushed, and a slot is
pushed once per vertex and once per scanned slot. -/
def elimFuel (n ns : ℕ) : ℕ := 2 * n + 2 * ns + 4

/-- **The engine, as a function.** -/
def elimTw (n ns W : ℕ) (off tgt alv : List ℕ) : ETw :=
  let deg := (initDegTw n off tgt alv (elimFuel n ns) (List.replicate n 0, 0)).1
  let b0 : BSt := (List.replicate (n + 1) 0, List.replicate (n + W + 1) 0,
    List.replicate (n + W + 1) 0, 1)
  let b := (initBuckTw n deg (elimFuel n ns) (b0, 0)).1
  let e0 : ESt := ⟨deg, List.replicate n 0, List.replicate n 0, List.replicate n 0, b, 0, 0, 0⟩
  let e := elimLoopTw n off tgt alv (elimFuel n ns) e0
  let o := offPassTw n e.idg (elimFuel n ns)
    (List.replicate (n + 1) 0, List.replicate n 0, 0, 0)
  let f := fillPassTw n off tgt alv e.rnk (elimFuel n ns) (List.replicate W 0, o.2.1, 0)
  ⟨e.rnk, e.kmax, o.1, f.1⟩

/-! ### 1.3 The differential test

`RamElim.Demo`'s arena — the triangle `0—1—2` with the path `2—3—4`,
five vertices, ten slots — with the mask bit of vertex `2` as the
parameter, and the published readings of the *compiled machine
program*. -/

/-- The offsets, as the demo stores them. -/
def demoOff : List ℕ := [0, 2, 4, 7, 9, 10]

/-- The targets: `1 2 | 0 2 | 0 1 3 | 2 4 | 3`. -/
def demoTgt : List ℕ := [1, 2, 0, 2, 0, 1, 3, 2, 4, 3]

/-- The mask, with the bit of vertex `2` left open. -/
def demoAlv (a2 : ℕ) : List ℕ := [1, 1, a2, 1, 1]

/-- The engine on the demo arena, at the demo's own width. -/
def demoTw (a2 : ℕ) : ETw := elimTw 5 10 10 demoOff demoTgt (demoAlv a2)

-- **Mask on.** `RamElim.Demo`'s first `#guard`: the ranks `0 … 4` in
-- reverse peeling order, the bound `2` the triangle forces, the
-- offsets `0 0 1 3 4 5` and the arcs `0 0 1 2 3`.
#guard (demoTw 1).rnk = [0, 1, 2, 3, 4]
#guard (demoTw 1).kmax = 2
#guard (demoTw 1).ioff = [0, 0, 1, 3, 4, 5]
#guard (demoTw 1).itg.take 5 = [0, 0, 1, 2, 3]

-- **Mask off at vertex `2`.** `RamElim.Demo`'s second `#guard`: the
-- arena falls apart into `0—1` and `3—4`, the bound drops to `1`,
-- vertex `2` is ranked and carries nothing.
#guard (demoTw 0).rnk = [0, 1, 4, 2, 3]
#guard (demoTw 0).kmax = 1
#guard (demoTw 0).ioff = [0, 0, 1, 1, 1, 2]
#guard (demoTw 0).itg.take 5 = [0, 3, 0, 0, 0]

-- …and the blocks the two arrays cut out, against `RamElim.Demo`'s own
-- reading of them.
#guard RamElim.Demo.demoBlock (demoTw 1).ioff ((demoTw 1).itg.take 5) 2 = [0, 1]
#guard RamElim.Demo.demoBlock (demoTw 1).ioff ((demoTw 1).itg.take 5) 3 = [2]
#guard RamElim.Demo.demoBlock (demoTw 0).ioff ((demoTw 0).itg.take 5) 2 = []
#guard RamElim.Demo.demoBlock (demoTw 0).ioff ((demoTw 0).itg.take 5) 4 = [3]

/-! #### Negative controls

Four, one per hot spot the mission names. -/

-- **The mask really bites**: the two runs differ, and the check can
-- tell. (A twin that ignored `alv` would pass every reading above at
-- `a2 = 1` and fail here.)
#guard demoTw 1 ≠ demoTw 0

-- **The rank counts down.** The first vertex extracted is `4` (degree
-- one) and it gets the *largest* rank; reversing the convention gives
-- the complementary reading, which is not what the machine reports.
#guard (demoTw 1).rnk ≠ [4, 3, 2, 1, 0]

/-- The degree pass, isolated, on a row that names a neighbour twice —
`0` adjacent to `1` listed twice — which is a `CsrGraph` and is not a
`CsrSimple`. -/
def repOff : List ℕ := [0, 2, 3]
/-- Its targets: `1 1 | 0`. -/
def repTgt : List ℕ := [1, 1, 0]
/-- Both vertices alive. -/
def repAlv : List ℕ := [1, 1]

-- **The double count is real**, which is why the input surface is
-- `CsrSimple`: the row of `0` names one neighbour and the pass counts
-- two.
#guard (initDegTw 2 repOff repTgt repAlv 10 (List.replicate 2 0, 0)).1 = [2, 1]
#guard (initDegTw 2 repOff repTgt repAlv 10 (List.replicate 2 0, 0)).1 ≠ [1, 1]

/-- The push, with the head **written before it is read** — the
transposition of `pushTw`'s two array writes. -/
def pushTwWrong (b : BSt) (d x : ℕ) : BSt :=
  let bh' := b.1.set d b.2.2.2
  (bh', b.2.1.set b.2.2.2 x, b.2.2.1.set b.2.2.2 bh'[d]!, b.2.2.2 + 1)

-- **In-place aliasing, checked.** Two pushes into the same bucket: the
-- right order links the second slot to the first, the wrong order links
-- it to itself.
#guard (pushTw (pushTw (List.replicate 3 0, List.replicate 5 0, List.replicate 5 0, 1) 0 7)
    0 8).2.2.1 = [0, 0, 1, 0, 0]
#guard (pushTwWrong (pushTwWrong
    (List.replicate 3 0, List.replicate 5 0, List.replicate 5 0, 1) 0 7) 0 8).2.2.1
  = [0, 1, 2, 0, 0]

/-- The row scan of an extraction, with the new bucket read from the
degree **before** the decrement — the transposition of `decSlotTw`'s
two steps. -/
def decSlotTwWrong (tgt alv : List ℕ) (s : ESt × ℕ) : ESt × ℕ :=
  let u := tgt[s.2]!
  let e := s.1
  if 0 < alv[u]! ∧ e.elm[u]! < 1 then
    ({ e with deg := e.deg.set u (e.deg[u]! - 1), bk := pushTw e.bk e.deg[u]! u }, s.2 + 1)
  else (e, s.2 + 1)

-- **The stale-bucket aliasing, checked**: the two orders put the
-- neighbour in different buckets, so a transposition is visible.
#guard
  (let e : ESt := ⟨[3, 3], [0, 0], [0, 0], [0, 0],
      (List.replicate 4 0, List.replicate 6 0, List.replicate 6 0, 1), 0, 0, 0⟩
   ((decSlotTw [1] [1, 1] (e, 0)).1.bk.1, (decSlotTwWrong [1] [1, 1] (e, 0)).1.bk.1))
  = ([0, 0, 1, 0], [0, 0, 0, 1])

end Twin

/-! ## 2. Two operations restated locally

`mopSucc` is P7/D-bb: an in-place `+1` as an operation of its own, so
that the operator phase cannot route a loop counter through a scratch
cell. `mopKeep` is its companion, and it is what a branch with an empty
`else` needs at this layer: both arms of an `irIf` must deliver the
*same destination*, and `mopCopy`'s only rule has a **junk**
destination, so an `else` written with it would move the accumulator
into a scratch cell and the branch merge would junk it. `x := x + zero`
keeps the cell; it costs one `add` where the machine program pays a
`skip`, and that is the whole of the difference.

Both are restated here rather than imported, per the campaign's
shared-file rule (`Examples/TrailRecursion.lean` restates the same
way): no file outside this one changes. -/

section Ops

/-- `x := x + 1`, in place. -/
noncomputable def mopSucc (m : ℕ) : NRest ℕ ECost := mopBinop .add m 1

theorem mopSucc_eq (m : ℕ) : mopSucc m = mopBinop .add m 1 := rfl

@[sepref_fr_rules]
theorem hnr_mop_succ (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 1 z) (.binop .add x x z)
      (hnCtxt natAssn 1 z) x natAssn (mopSucc m) := by
  rw [mopSucc_eq]; exact hnr_mop_binop_self .add x z m 1

attribute [irreducible] mopSucc

/-- `x := x + 0`, in place: the identity, at a cell that does not
move. -/
noncomputable def mopKeep (m : ℕ) : NRest ℕ ECost := mopBinop .add m 0

theorem mopKeep_eq (m : ℕ) : mopKeep m = mopBinop .add m 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_keep (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 0 z) (.binop .add x x z)
      (hnCtxt natAssn 0 z) x natAssn (mopKeep m) := by
  rw [mopKeep_eq]; exact hnr_mop_binop_self .add x z m 0

attribute [irreducible] mopKeep

/-- Any outcome of a body bounded by a specification satisfies it —
`BfsQ.res_of_le` at a `spec` right-hand side, which is what a loop body
containing an inner loop needs for its variant. -/
theorem res_spec_of_le {α : Type} {m : NRest α ECost} {s' : α} {P : α → Prop} {T : α → ECost}
    (hm : m ≤ NRest.spec P T) (hle : (NRest.returnT s' : NRest α ECost) ≤ m) : P s' := by
  by_contra hne
  have h := le_trans hle hm
  rw [NRest.spec, returnT_le_rest_iff, if_neg hne, le_bot_iff, ← WithBot.coe_zero] at h
  exact WithBot.coe_ne_bot h

end Ops

/-! ## 3. The degree pass, at the `NRest` layer

One pass over the block structure, its inner loop the row scan. What
the scan counts is the number of *live* slots of the row; what
`RamElim.card_liveSlots` says is that for a live vertex that count is
the arena degree, and `RamElim.adeg_of_dead` is the other branch.

The state of the inner loop is `(c, j)`, of the outer `(deg, i)` —
which are exactly `degSlotTw`'s and `degRowTw`'s, so §1's differential
test is a test of this program. -/

section DegreePass

open Lax13Proofs.Refine.BfsQ (Shape)

/-- The row scan's guard. -/
def degBf (jend : ℕ) : ℕ × ℕ → Bool := fun s => decide (s.2 < jend)

/-- What one slot of the row scan needs: the slot is in the target
array and the target it names is a vertex the mask array covers. -/
def degSlotP (tgt alv : List ℕ) : ℕ × ℕ → Prop := fun s =>
  s.2 < tgt.length ∧ tgt[s.2]! < alv.length

/-- One slot of the counting scan. -/
noncomputable def degF (tgt alv : List ℕ) : ℕ × ℕ → NRest (ℕ × ℕ) ECost := fun s =>
  bindT (mopAget tgt s.2) fun u =>
    bindT (mopAget alv u) fun au =>
      bindT (irIf (decide (0 < au)) (mopSucc s.1) (mopKeep s.1)) fun c =>
        bindT (mopSucc s.2) fun j => mopPair c j

/-- The counting scan of one row. -/
noncomputable def degScan (tgt alv : List ℕ) (jend : ℕ) (s₀ : ℕ × ℕ) : NRest (ℕ × ℕ) ECost :=
  irWhileIT (fun s => degBf jend s = true → degSlotP tgt alv s) (degBf jend) (degF tgt alv) s₀

/-- The outer pass's guard. -/
def degRowBf (n : ℕ) : List ℕ × ℕ → Bool := fun s => decide (s.2 < n)

/-- What one row of the degree pass needs: the block structure's shape,
the counter a vertex, and the degree array at its length. -/
def degRowP (n : ℕ) (off tgt alv : List ℕ) : List ℕ × ℕ → Prop := fun s =>
  Shape n off tgt alv ∧ s.1.length = n ∧ s.2 < n

/-- One vertex's degree in the arena. -/
noncomputable def degRowF (off tgt alv : List ℕ) :
    List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  bindT (mopAget off s.2) fun j0 =>
    bindT (mopBinop .add s.2 1) fun i1 =>
      bindT (mopAget off i1) fun jend =>
        bindT (mopConstN 0) fun c0 =>
          bindT (mopPair c0 j0) fun z0 =>
            bindT (degScan tgt alv jend z0) fun r =>
              bindT (mopAget alv s.2) fun ai =>
                bindT (irIf (decide (0 < ai)) (mopAset s.1 s.2 r.1) (mopAset s.1 s.2 0))
                  fun D => bindT (mopSucc s.2) fun i => mopPair D i

/-- **The degree pass.** -/
noncomputable def degPass (n : ℕ) (off tgt alv : List ℕ) (s₀ : List ℕ × ℕ) :
    NRest (List ℕ × ℕ) ECost :=
  irWhileIT (fun s => degRowBf n s = true → degRowP n off tgt alv s) (degRowBf n)
    (degRowF off tgt alv) s₀

/-! ### 3.1 What a row counts

`liveUpto` is `RamElim.liveUpto` at the list layer: the live slots of a
row the scan has already passed. `degOf` is what the pass leaves in
`deg`, and §7 identifies it with `RamElim.adeg`. -/

/-- The live slots of a block between two indices. -/
def liveUpto (tgt alv : List ℕ) (a b : ℕ) : ℕ :=
  ((Finset.Ico a b).filter (fun j => 0 < alv[tgt[j]!]!)).card

theorem liveUpto_self (tgt alv : List ℕ) (a : ℕ) : liveUpto tgt alv a a = 0 := by
  simp [liveUpto]

theorem liveUpto_succ (tgt alv : List ℕ) {a b : ℕ} (h : a ≤ b) :
    liveUpto tgt alv a (b + 1) =
      if 0 < alv[tgt[b]!]! then liveUpto tgt alv a b + 1 else liveUpto tgt alv a b := by
  rw [liveUpto, liveUpto, Nat.Ico_succ_right_eq_insert_Ico h, Finset.filter_insert]
  by_cases hb : 0 < alv[tgt[b]!]!
  · rw [if_pos hb, if_pos hb, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg hb, if_neg hb]

/-- What the pass leaves at a vertex: a dead vertex is isolated in the
arena, so its degree is zero whatever its row says. -/
def degOf (off tgt alv : List ℕ) (v : ℕ) : ℕ :=
  if 0 < alv[v]! then liveUpto tgt alv off[v]! off[v + 1]! else 0

/-! ### 3.2 The prices -/

open Lax13Proofs.Refine.BfsQ (cu iter)

/-- One slot of the counting scan: two reads, the branch, the count, the
index, the tuple. -/
def degC : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.ite
  + cu Currency.add + cu Currency.add + cu Currency.skip

/-- One row of the degree pass, everything outside the scan — including
the scan loop's own entry test. -/
def degRowC : ACost String ℕ := cu Currency.aget + cu Currency.add + cu Currency.aget
  + cu Currency.const + cu Currency.skip + cu Currency.«while» + cu Currency.aget
  + cu Currency.ite + cu Currency.aset + cu Currency.add + cu Currency.skip

/-- One slot of the counting scan, priced. Both branches pay the same —
`mopKeep` is what makes the empty `else` cost an `add` and not a lost
cell. -/
theorem degF_le (tgt alv : List ℕ) (s : ℕ × ℕ) (h1 : s.2 < tgt.length)
    (h2 : tgt[s.2]! < alv.length) :
    degF tgt alv s ≤ NRest.consume (NRest.returnT (degSlotTw tgt alv s)) (liftACost degC) := by
  refine le_of_eq ?_
  by_cases hb : 0 < alv[tgt[s.2]!]!
  · simp only [degF, degSlotTw, mopAget_def, mopBinop_def, mopPair_def, mopSucc_eq, mopKeep_eq,
      irIf_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
      Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, decide_eq_true_eq, if_pos hb, degC,
      liftACost_add, BfsQ.liftACost_cu]
    congr 1
    ac_rfl
  · simp only [degF, degSlotTw, mopAget_def, mopBinop_def, mopPair_def, mopSucc_eq, mopKeep_eq,
      irIf_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
      Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, decide_eq_true_eq, if_neg hb, degC,
      liftACost_add, BfsQ.liftACost_cu]
    congr 1
    ac_rfl

/-! ### 3.3 The row scan, run to the end -/

theorem degScan_le {Inv : ℕ × ℕ → Prop} (tgt alv : List ℕ) (jend : ℕ)
    (hs : ∀ t : ℕ × ℕ, Inv t → degBf jend t = true →
      degSlotP tgt alv t ∧ Inv (degSlotTw tgt alv t)) :
    ∀ (fuel : ℕ) (s : ℕ × ℕ), Inv s → jend - s.2 ≤ fuel →
      degScan tgt alv jend s
        ≤ NRest.spec (fun t : ℕ × ℕ => Inv t ∧ jend ≤ t.2)
            (fun _ => liftACost ((jend - s.2) • iter degC + cu Currency.«while»)) := by
  have exit : ∀ s : ℕ × ℕ, Inv s → jend ≤ s.2 →
      degScan tgt alv jend s
        ≤ NRest.spec (fun t : ℕ × ℕ => Inv t ∧ jend ≤ t.2)
            (fun _ => liftACost ((jend - s.2) • iter degC + cu Currency.«while»)) := by
    intro s hI hk
    have hb : degBf jend s = false := by simp only [degBf, decide_eq_false_iff_not]; omega
    simp only [degScan, BfsQ.irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hI, hk⟩ ?_
    rw [show jend - s.2 = 0 by omega]
    simp
  intro fuel
  induction fuel with
  | zero => intro s hI hf; exact exit s hI (by omega)
  | succ fuel ih =>
    intro s hI hf
    by_cases hb : s.2 < jend
    · have hbt : degBf jend s = true := by simp [degBf, hb]
      obtain ⟨hPs, hInv'⟩ := hs s hI hbt
      have hIs : degBf jend s = true → degSlotP tgt alv s := fun _ => hPs
      have hk' : (degSlotTw tgt alv s).2 = s.2 + 1 := rfl
      have hih := ih (degSlotTw tgt alv s) hInv' (by rw [hk']; omega)
      rw [hk'] at hih
      have hcost : irUnit Currency.«while»
          + (liftACost degC + liftACost ((jend - (s.2 + 1)) • iter degC + cu Currency.«while»))
          = liftACost ((jend - s.2) • iter degC + cu Currency.«while») := by
        rw [show jend - s.2 = (jend - (s.2 + 1)) + 1 by omega, succ_nsmul]
        simp only [iter, liftACost_add, liftACost_nsmul, BfsQ.liftACost_cu]
        ac_rfl
      calc degScan tgt alv jend s
          = NRest.consume (NRest.bindT (degF tgt alv s)
              fun s' => degScan tgt alv jend s') (irUnit Currency.«while») := by
            simp only [degScan]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.bindT
              (NRest.consume (NRest.returnT (degSlotTw tgt alv s)) (liftACost degC))
              fun s' => degScan tgt alv jend s') (irUnit Currency.«while») :=
            NRest.consume_mono
              (NRest.bindT_mono (degF_le tgt alv s hPs.1 hPs.2) fun _ => le_rfl) le_rfl
        _ = NRest.consume (NRest.consume (degScan tgt alv jend (degSlotTw tgt alv s))
              (liftACost degC)) (irUnit Currency.«while») := by rw [bindT_unitT]
        _ ≤ _ := by
            rw [← hcost]
            exact NRest.consume_mono (NRest.consume_mono hih le_rfl) le_rfl |>.trans
              (le_of_eq (by rw [Sepref.consume_spec, Sepref.consume_spec]))
    · exact exit s hI (by omega)

/-! ### 3.4 One row

The row scan's invariant is the count it has accumulated; what the row
leaves in `deg` is `degOf`, and every other entry is untouched. -/

/-- The row scan's invariant: the index inside the row, the count the
live slots passed. -/
def degRowInv (off tgt alv : List ℕ) (i : ℕ) : ℕ × ℕ → Prop := fun z =>
  off[i]! ≤ z.2 ∧ z.2 ≤ off[i + 1]! ∧ z.1 = liveUpto tgt alv off[i]! z.2

theorem degRowF_le {n : ℕ} {off tgt alv : List ℕ} (hsh : Shape n off tgt alv)
    (s : List ℕ × ℕ) (hlen : s.1.length = n) (hi : s.2 < n) :
    degRowF off tgt alv s
      ≤ NRest.spec
          (fun t : List ℕ × ℕ => t.1.length = n ∧ t.2 = s.2 + 1 ∧
            (∀ v, v ≠ s.2 → t.1[v]! = s.1[v]!) ∧ t.1[s.2]! = degOf off tgt alv s.2)
          (fun _ => liftACost (degRowC + (off[s.2 + 1]! - off[s.2]!) • iter degC)) := by
  have holen : off.length = n + 1 := hsh.1
  have halen : alv.length = n := hsh.2.1
  have h0 : s.2 < off.length := by omega
  have h1 : s.2 + 1 < off.length := by omega
  have hmono : off[s.2]! ≤ off[s.2 + 1]! := hsh.2.2.1 _ hi
  have hrow : off[s.2 + 1]! ≤ tgt.length := hsh.row_le hi
  have hai : s.2 < alv.length := by omega
  have hdi : s.2 < s.1.length := by omega
  -- the scan's step preserves the count and stays in range
  have hs : ∀ z : ℕ × ℕ, degRowInv off tgt alv s.2 z → degBf off[s.2 + 1]! z = true →
      degSlotP tgt alv z ∧ degRowInv off tgt alv s.2 (degSlotTw tgt alv z) := by
    intro z ⟨hz1, hz2, hz3⟩ hzb
    have hzlt : z.2 < off[s.2 + 1]! := by simpa [degBf] using hzb
    have hzt : z.2 < tgt.length := by omega
    have hun : tgt[z.2]! < n := hsh.2.2.2.2 _ hzt
    refine ⟨⟨hzt, by omega⟩, ?_, ?_, ?_⟩
    · show off[s.2]! ≤ z.2 + 1
      omega
    · show z.2 + 1 ≤ off[s.2 + 1]!
      omega
    · show (if 0 < alv[tgt[z.2]!]! then z.1 + 1 else z.1)
        = liveUpto tgt alv off[s.2]! (z.2 + 1)
      rw [liveUpto_succ tgt alv hz1, hz3]
  have hstart : degRowInv off tgt alv s.2 (0, off[s.2]!) :=
    ⟨le_rfl, hmono, (liveUpto_self tgt alv _).symm⟩
  have hscan := degScan_le (Inv := degRowInv off tgt alv s.2) tgt alv off[s.2 + 1]! hs
    (off[s.2 + 1]! - off[s.2]!) _ hstart (by simp)
  -- the tail: the branch that writes the degree, and the counter bump
  have hK : ∀ z : ℕ × ℕ, (degRowInv off tgt alv s.2 z ∧ off[s.2 + 1]! ≤ z.2) →
      NRest.bindT (NRest.assert (s.2 < alv.length)) (fun _ =>
          NRest.consume
            (NRest.bindT
              (irIf (decide (0 < alv[s.2]!)) (mopAset s.1 s.2 z.1) (mopAset s.1 s.2 0))
              fun D => NRest.bindT (mopSucc s.2) fun i =>
                NRest.consume (NRest.returnT (D, i)) (irUnit Currency.skip))
            (irUnit Currency.aget))
        ≤ NRest.spec
            (fun t : List ℕ × ℕ => t.1.length = n ∧ t.2 = s.2 + 1 ∧
              (∀ v, v ≠ s.2 → t.1[v]! = s.1[v]!) ∧ t.1[s.2]! = degOf off tgt alv s.2)
            (fun _ => irUnit Currency.aget + irUnit Currency.ite + irUnit Currency.aset
              + irUnit Currency.add + irUnit Currency.skip) := by
    rintro z ⟨⟨hz1, hz2, hz3⟩, hdone⟩
    have hzend : z.2 = off[s.2 + 1]! := by omega
    have hcount : z.1 = liveUpto tgt alv off[s.2]! off[s.2 + 1]! := by rw [hz3, hzend]
    simp only [mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def, mopPair_def, irIf_def,
      NRest.assert_pos hai, NRest.assert_pos hdi, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
      Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add]
    by_cases hb : 0 < alv[s.2]!
    · rw [if_pos (by simpa using hb)]
      simp only [NRest.assert_pos hdi, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume]
      refine consume_returnT_le_spec ⟨by simp [hlen], rfl, ?_, ?_⟩ (le_of_eq (by ac_rfl))
      · intro v hv; rw [BfsQ.get!_set _ _ _ _ hdi, if_neg hv]
      · rw [BfsQ.get!_set _ _ _ _ hdi, if_pos rfl, degOf, if_pos hb, hcount]
    · rw [if_neg (by simpa using hb)]
      simp only [NRest.assert_pos hdi, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume]
      refine consume_returnT_le_spec ⟨by simp [hlen], rfl, ?_, ?_⟩ (le_of_eq (by ac_rfl))
      · intro v hv; rw [BfsQ.get!_set _ _ _ _ hdi, if_neg hv]
      · rw [BfsQ.get!_set _ _ _ _ hdi, if_pos rfl, degOf, if_neg hb]
  -- assemble
  simp only [degRowF, mopAget_def, mopBinop_def, mopConstN_def, mopPair_def,
    NRest.assert_pos h0, NRest.assert_pos h1, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, NRest.bindT_assoc_acost]
  refine le_trans (NRest.consume_mono
    (le_trans (NRest.bindT_mono hscan fun _ => le_rfl) (bindT_spec_le _ _ _ _ _ hK)) le_rfl)
    (le_of_eq ?_)
  rw [Sepref.consume_spec]
  refine congrArg (NRest.spec _) (funext fun _ => ?_)
  simp only [degRowC, iter, liftACost_add, liftACost_nsmul, BfsQ.liftACost_cu]
  ac_rfl

/-! ### 3.5 The pass

The outer loop's energy is two-currency, as the drain's is: one
`degRowC` per vertex still to visit, one `degC` per adjacency slot still
to scan. The second is bounded because the rows **tile** the target
array — no injectivity argument is needed here, unlike the queue's,
since the pass visits every vertex exactly once in order. -/

theorem degPass_le {n : ℕ} {off tgt alv : List ℕ} (hsh : Shape n off tgt alv) :
    ∀ (fuel : ℕ) (s : List ℕ × ℕ), s.1.length = n → s.2 ≤ n → n - s.2 ≤ fuel →
      (∀ v, v < s.2 → s.1[v]! = degOf off tgt alv v) →
      degPass n off tgt alv s
        ≤ NRest.spec
            (fun t : List ℕ × ℕ => t.1.length = n ∧
              ∀ v, v < n → t.1[v]! = degOf off tgt alv v)
            (fun _ => liftACost (E2 (iter degRowC) (iter degC) (n - s.2)
              (off[n]! - off[s.2]!) + cu Currency.«while»)) := by
  have exit : ∀ s : List ℕ × ℕ, s.1.length = n → n ≤ s.2 →
      (∀ v, v < s.2 → s.1[v]! = degOf off tgt alv v) →
      degPass n off tgt alv s
        ≤ NRest.spec
            (fun t : List ℕ × ℕ => t.1.length = n ∧
              ∀ v, v < n → t.1[v]! = degOf off tgt alv v)
            (fun _ => liftACost (E2 (iter degRowC) (iter degC) (n - s.2)
              (off[n]! - off[s.2]!) + cu Currency.«while»)) := by
    intro s hlen hge hall
    have hb : degRowBf n s = false := by simp only [degRowBf, decide_eq_false_iff_not]; omega
    simp only [degPass, BfsQ.irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hlen, fun v hv => hall v (by omega)⟩ ?_
    rw [liftACost_add, BfsQ.liftACost_cu, add_comm]
    exact cost_le_add _ _
  intro fuel
  induction fuel with
  | zero => intro s hlen hle hf hall; exact exit s hlen (by omega) hall
  | succ fuel ih =>
    intro s hlen hle hf hall
    by_cases hb : s.2 < n
    · have hbt : degRowBf n s = true := by simp [degRowBf, hb]
      have hIs : degRowBf n s = true → degRowP n off tgt alv s := fun _ => ⟨hsh, hlen, hb⟩
      have hmono : off[s.2]! ≤ off[s.2 + 1]! := hsh.2.2.1 _ hb
      have htop : off[s.2 + 1]! ≤ off[n]! := hsh.mono' (by omega) le_rfl
      have hcont : ∀ t : List ℕ × ℕ, (t.1.length = n ∧ t.2 = s.2 + 1 ∧
            (∀ v, v ≠ s.2 → t.1[v]! = s.1[v]!) ∧ t.1[s.2]! = degOf off tgt alv s.2) →
          degPass n off tgt alv t
            ≤ NRest.spec
                (fun t' : List ℕ × ℕ => t'.1.length = n ∧
                  ∀ v, v < n → t'.1[v]! = degOf off tgt alv v)
                (fun _ => liftACost (E2 (iter degRowC) (iter degC) (n - (s.2 + 1))
                  (off[n]! - off[s.2 + 1]!) + cu Currency.«while»)) := by
        rintro t ⟨htlen, hti, htkeep, htnew⟩
        refine le_trans (ih t htlen (by omega) (by omega) ?_) (le_of_eq ?_)
        · intro v hv
          rw [hti] at hv
          rcases eq_or_ne v s.2 with rfl | hne
          · exact htnew
          · rw [htkeep v hne]; exact hall v (by omega)
        · rw [hti]
      have hcost : irUnit Currency.«while»
          + (liftACost (degRowC + (off[s.2 + 1]! - off[s.2]!) • iter degC)
            + liftACost (E2 (iter degRowC) (iter degC) (n - (s.2 + 1))
                (off[n]! - off[s.2 + 1]!) + cu Currency.«while»))
          = liftACost (E2 (iter degRowC) (iter degC) (n - s.2)
              (off[n]! - off[s.2]!) + cu Currency.«while») := by
        rw [show n - s.2 = (n - (s.2 + 1)) + 1 by omega,
          show off[n]! - off[s.2]!
            = (off[n]! - off[s.2 + 1]!) + (off[s.2 + 1]! - off[s.2]!) by omega,
          E2_split]
        simp only [iter, liftACost_add, liftACost_nsmul, BfsQ.liftACost_cu]
        ac_rfl
      calc degPass n off tgt alv s
            = NRest.consume (NRest.bindT (degRowF off tgt alv s)
                fun t => degPass n off tgt alv t) (irUnit Currency.«while») := by
              simp only [degPass]; rw [irWhileIT_of_true hIs hbt]
          _ ≤ NRest.consume (NRest.spec _ (fun _ =>
                liftACost (degRowC + (off[s.2 + 1]! - off[s.2]!) • iter degC)
                + liftACost (E2 (iter degRowC) (iter degC) (n - (s.2 + 1))
                    (off[n]! - off[s.2 + 1]!) + cu Currency.«while»)))
                (irUnit Currency.«while») :=
              NRest.consume_mono
                (le_trans (NRest.bindT_mono (degRowF_le hsh s hlen hb) fun _ => le_rfl)
                  (bindT_spec_le _ _ _ _ _ hcont)) le_rfl
          _ = _ := by rw [Sepref.consume_spec, ← hcost]
    · exact exit s hlen (by omega) hall

/-! ### 3.6 The variants the synthesis takes as annotations

Each is the measure the fuel induction above already runs on, and each
rests on the body's *value*: a one-result upper bound makes every
possible outcome that one result (`BfsQ.res_of_le`). -/

theorem deg_variant (tgt alv : List ℕ) (jend : ℕ) :
    LOOP_VARIANT (fun s => degBf jend s = true → degSlotP tgt alv s) (degBf jend)
      (degF tgt alv) (fun s => jend - s.2) := by
  intro s s' hI hb hle
  obtain ⟨h1, h2⟩ := hI hb
  rw [BfsQ.res_of_le (degF_le tgt alv s h1 h2) hle]
  have hk : s.2 < jend := by simpa [degBf] using hb
  show jend - (degSlotTw tgt alv s).2 < jend - s.2
  show jend - (s.2 + 1) < jend - s.2
  omega

theorem degRow_variant (n : ℕ) (off tgt alv : List ℕ) :
    LOOP_VARIANT (fun s => degRowBf n s = true → degRowP n off tgt alv s) (degRowBf n)
      (degRowF off tgt alv) (fun s => n - s.2) := by
  intro s s' hI hb hle
  obtain ⟨hsh, hlen, hi⟩ := hI hb
  have hcon : (NRest.returnT s' : NRest (List ℕ × ℕ) ECost)
      ≤ NRest.spec (fun t : List ℕ × ℕ => t.1.length = n ∧ t.2 = s.2 + 1 ∧
          (∀ v, v ≠ s.2 → t.1[v]! = s.1[v]!) ∧ t.1[s.2]! = degOf off tgt alv s.2)
        (fun _ => liftACost (degRowC + (off[s.2 + 1]! - off[s.2]!) • iter degC)) :=
    le_trans hle (degRowF_le hsh s hlen hi)
  have hs' : s'.2 = s.2 + 1 := (res_spec_of_le hcon le_rfl).2.1
  show n - s'.2 < n - s.2
  rw [hs']
  omega

end DegreePass

/-! ## 4. The degree pass, synthesized

The two loops go through `sepref_synth` with no bespoke tactic work and
no hand-written frame clause: two `LOOP_VARIANT` annotations, the two
the abstract proof already had. -/

section DegreeSynth

open Lax13Proofs.Refine.BfsQ (Shape)

set_option maxHeartbeats 1000000 in
sepref_synth degScanSynth (tgt alv : List ℕ) (jend c₀ j₀ : ℕ)
    (hv : LOOP_VARIANT (fun s => degBf jend s = true → degSlotP tgt alv s) (degBf jend)
      (degF tgt alv) (fun s => jend - s.2)) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn) (c₀, j₀) ("c", "j") ∗
      hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn alv "alv" ∗
      hnCtxt natAssn jend "jend" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "u" ∗ junkCell "au")
    _ _ ("c", "j") (natAssn ×ₐ natAssn)
    (degScan tgt alv jend (c₀, j₀))

-- The synthesized row scan, pinned. It is `RamElim.degSlot` on the
-- nose, one instruction for one instruction, with the empty `else`
-- realized as the in-place `c := c + zero` that `mopKeep` forces.
#guard degScanSynth_impl =
  Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
    ((Com.aget "u" "tgt" "j").seq
      ((Com.aget "au" "alv" "u").seq
        ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "au"))
              (Com.binop Lax13Proofs.Imp.Bop.add "c" "c" "one")
              (Com.binop Lax13Proofs.Imp.Bop.add "c" "c" "zero")).seq
          ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq Com.skip))))

-- **The negative control on the pin**: the `else` really is an
-- in-place add and not a `skip`, so a `Com` that dropped it is a
-- different program and the check can tell.
#guard degScanSynth_impl ≠
  Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
    ((Com.aget "u" "tgt" "j").seq
      ((Com.aget "au" "alv" "u").seq
        ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "au"))
              (Com.binop Lax13Proofs.Imp.Bop.add "c" "c" "one") Com.skip).seq
          ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq Com.skip))))

/-- The row scan's synthesis with its variant discharged. The frame the
tool computed is existential here only because naming it costs a page
and buys nothing: `degScanSynth` itself is the named statement. -/
theorem degScanSynth' (tgt alv : List ℕ) (jend c₀ j₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (natAssn ×ₐ natAssn) (c₀, j₀) ("c", "j") ∗
        hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn alv "alv" ∗
        hnCtxt natAssn jend "jend" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "u" ∗ junkCell "au")
      degScanSynth_impl Γ' ("c", "j") (natAssn ×ₐ natAssn)
      (degScan tgt alv jend (c₀, j₀)) :=
  ⟨_, degScanSynth tgt alv jend c₀ j₀ (deg_variant tgt alv jend)⟩

/-- info: 'Lax3Proofs.Refine.ElimSynth.degScanSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms degScanSynth

/-! ### 4.1 P2/2B/D-a — the *outer* pass does not translate, measured

`degPassSynth`, the two-loop degree pass, was written and run and is
**not** in this file, because `sepref_synth` does not finish on it:

| goal | budget | wall clock | result |
|---|---|---|---|
| `degScan` (inner loop alone) | 1 000 000 hb | ≈ 4 s | `Com`, pinned above |
| `degPass` (outer + inner) | 1 000 000 hb | ≈ 130 s | `(deterministic) timeout at whnf` |
| `degPass` (outer + inner) | 4 000 000 hb | ≈ 8 min | `(deterministic) timeout at whnf` |

The goal was `hnRefine (… ∗ hnCtxt (arrayAssn ×ₐ natAssn) (deg₀, 0) ("deg","i") ∗
…) _ _ ("deg","i") (arrayAssn ×ₐ natAssn) (degPass n off tgt alv (deg₀, 0))`
with the two `LOOP_VARIANT`s of §3.6 supplied as hypotheses — the same
shape `BfsQSynth.bfsQSynth` uses, and that one has *three* nested loops
and two nested branches and finishes in ≈ 49 s.

What is different here, and what the next tower wave should look at:

* **The outer loop’s state carries the array the branch writes.** In
  `bfsQS` every `aset` destination (`dist`, `q`) is an array the
  *inner* loop owns and the branches inside the row scan are balanced by
  `pack3`. Here the outer body’s branch has `mopAset` in **both** arms,
  each moving `deg`’s ownership into the `irIf`’s result slot, and that
  slot is a component of the enclosing loop’s state. So the branch merge
  and the loop rule’s state matching interact, which they never do in
  the gate program.
* **The inner loop sits in the middle of the outer body, not at its
  end.** `popF'` ends with the row scan (modulo one `pack4`); `degRowF`
  runs the scan and then does four more operations *using its result*
  (`r.1` feeds the `aset`). Every one of those needs the loop’s result
  tuple split back into cells, which is P7/D-ba’s `conjunctsSplit`
  path, re-entered under the outer loop’s own translation.

Both are cheap to test in the tower package itself: the minimal
reproducer is *one* outer loop whose body contains one inner loop
followed by a two-armed `aset` branch on a state array — about forty
lines. It is not testable from here, since the fix is in
`Sepref/Translate.lean` and `Sepref/Frame.lean`, which this satellite
may not edit.

**What survives the stall.** `degPass_le` (§3.5) is the abstract pass’s
cost and correctness and does not mention the tool; `degScanSynth` is
the inner loop’s `Com`. When the translate driver is repaired the
outer synthesis is one `sepref_synth` invocation away — the
annotations, the variants and the bound are all here. -/

end DegreeSynth

/-! ## 5. The bridge into `RamElim`'s own vocabulary

What the tower's degree pass leaves is `degOf`, a count over lists;
what the driver stack's phase predicates speak about is
`RamElim.adeg`, a `Finset` cardinality in the *arena*. They are the
same number, and this is the thin future bridge the P1 pattern asks
for: it is proved once, here, and every phase above it is stated in the
old vocabulary and needs no further translation.

The bridge is exactly where `RamElim.CsrSimple`'s `nodup` clause is
spent: `card_liveSlots` is the bijection between a row's live slots and
the arena neighbours, and a row that named a neighbour twice would make
this equation false — which is what §1.3's repeat-row `#guard`
exhibits at the list layer. -/

section Bridge

open Lax13Proofs.Reasoning (arrOf)
open Lax13Proofs.Refine.BfsQ (Shape cu iter)

/-- In range, the `getElem!` of a function array is the function. -/
theorem getElem!_arrOf {m i : ℕ} (f : ℕ → ℕ) (h : i < m) : (arrOf m f)[i]! = f i := by
  rw [getElem!_pos (arrOf m f) i (by simpa [arrOf] using h)]
  simp [arrOf]

/-- **The tower's degree is the arena degree.** -/
theorem degOf_eq_adeg {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : RamElim.CsrSimple G ns O T) {v : ℕ} (hv : v < n) :
    degOf (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) v = RamElim.adeg G M v := by
  classical
  have hMv : (arrOf n M)[v]! = M v := getElem!_arrOf M hv
  by_cases hd : M v = 0
  · rw [degOf, if_neg (by rw [hMv, hd]; omega), RamElim.adeg_of_dead hv hd]
  · have hOv : (arrOf (n + 1) O)[v]! = O v := getElem!_arrOf O (by omega)
    have hOv1 : (arrOf (n + 1) O)[v + 1]! = O (v + 1) := getElem!_arrOf O (by omega)
    have hrow : O (v + 1) ≤ ns := by
      have := hcsr.csr.mono' (show v + 1 ≤ n from hv) (le_refl n)
      rwa [hcsr.csr.last] at this
    rw [degOf, if_pos (by rw [hMv]; omega), hOv, hOv1,
      RamElim.adeg_of_alive hcsr hv hd, RamElim.liveSlots, liveUpto]
    refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
    have hjs : j < ns := lt_of_lt_of_le (Finset.mem_Ico.1 hj).2 hrow
    have hTj : (arrOf ns T)[j]! = T j := getElem!_arrOf T hjs
    have hTn : T j < n := hcsr.csr.target_lt j hjs
    rw [hTj, getElem!_arrOf M hTn]
    exact ⟨fun h => by omega, fun h => by omega⟩

/-- The block structure, as the tower reads it: `BfsQ.Shape`'s five
clauses on the lists the arrays hold. -/
theorem shape_of_csrSimple {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : RamElim.CsrSimple G ns O T) :
    Shape n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) := by
  refine ⟨by simp [arrOf], by simp [arrOf], fun i hi => ?_, ?_, fun j hj => ?_⟩
  · rw [getElem!_arrOf O (by omega), getElem!_arrOf O (by omega)]
    exact hcsr.csr.mono i hi
  · rw [getElem!_arrOf O (by omega), hcsr.csr.last]
    simp [arrOf]
  · have hj' : j < ns := by simpa [arrOf] using hj
    rw [getElem!_arrOf T hj']
    exact hcsr.csr.target_lt j hj'

/-- **The degree pass, in the old export's terms.** The pass leaves in
`deg` exactly `RamElim.AfterDeg`'s conjunct `deg = arrOf n (adeg G M)`
— read at the list layer. -/
theorem degPass_adeg {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : RamElim.CsrSimple G ns O T) (deg₀ : List ℕ) (hlen : deg₀.length = n) :
    degPass n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) (deg₀, 0)
      ≤ NRest.spec
          (fun t : List ℕ × ℕ => t.1.length = n ∧ ∀ v, v < n → t.1[v]! = RamElim.adeg G M v)
          (fun _ => liftACost (E2 (iter degRowC) (iter degC) n ns + cu Currency.«while»)) := by
  have hsh : Shape n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) := shape_of_csrSimple hcsr
  refine le_trans (degPass_le hsh n (deg₀, 0) hlen (Nat.zero_le n) le_rfl
    (fun v hv => absurd hv (Nat.not_lt_zero v))) (spec_mono ?_ ?_)
  · rintro t ⟨h1, h2⟩
    exact ⟨h1, fun v hv => by rw [h2 v hv]; exact degOf_eq_adeg hcsr hv⟩
  · intro _ _
    have h0 : (arrOf (n + 1) O)[0]! = O 0 := getElem!_arrOf O (by omega)
    have hn : (arrOf (n + 1) O)[n]! = O n := getElem!_arrOf O (by omega)
    show liftACost (E2 (iter degRowC) (iter degC) (n - (0 : ℕ)) _ + _)
      ≤ liftACost (E2 (iter degRowC) (iter degC) n ns + cu Currency.«while»)
    rw [h0, hn, hcsr.csr.zero, hcsr.csr.last, Nat.sub_zero, Nat.sub_zero]

end Bridge

/-! ## 6. The degree pass's cost, cashed

The abstract budget priced in IMP+ time units. The constants are
**computed** from the per-iteration accounts by `decide +kernel`, not
tuned — which is the point of the tower's cost layer and the reason
this number may be compared with the baseline's at all. -/

section Cash

open Lax13Proofs.Refine.BfsQ (cu iter)

/-- **The degree pass's cost**: `36·n + 23·ns + 4` IMP+ time units. The
hand-walked baseline charges `48·n + 44·ns + 10` for the same phase
(`RamElim.implements`'s `w1`); the tower is cheaper on both
coefficients, and its number is derived rather than chosen. -/
def degK (n ns : ℕ) : ℕ := 36 * n + 23 * ns + 4

theorem cash_degBudget (n ns : ℕ) :
    Codegen.cash (E2 (iter degRowC) (iter degC) n ns + cu Currency.«while») = degK n ns := by
  rw [E2, Codegen.cash_add, Codegen.cash_add, BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter degRowC) = 36 from by decide +kernel,
    show Codegen.cash (iter degC) = 23 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, degK]
  ring

-- The baseline's own figure for the same phase, for the record — and
-- the check can tell that the tower's is the smaller one.
#guard degK 5 10 = 414
#guard 48 * 5 + 44 * 10 + 10 = 690
#guard degK 5 10 < 48 * 5 + 44 * 10 + 10

end Cash

/-! ## 7. Axioms -/

/-- info: 'Lax3Proofs.Refine.ElimSynth.degPass_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms degPass_le

/-- info: 'Lax3Proofs.Refine.ElimSynth.degPass_adeg' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms degPass_adeg

/-- info: 'Lax3Proofs.Refine.ElimSynth.degOf_eq_adeg' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms degOf_eq_adeg

/-- info: 'Lax3Proofs.Refine.ElimSynth.degScanSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms degScanSynth

/-- info: 'Lax3Proofs.Refine.ElimSynth.cash_degBudget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cash_degBudget

/-! ## 8. FLAG 2 — what is retained, and the argument for it

This satellite delivers the engine's **falsification gate** (§1) and
**one phase end to end** (§3–§6): abstract program, amortized cost,
inner-loop synthesis, the bridge into `RamElim`'s own `adeg`
vocabulary, and a computed constant. The other four phases are retained
in their hand-walked form for this wave. The argument, concretely:

**What the gate already buys, whatever happens to the rest.** §1 is a
computable twin of the *whole* engine — all five phases, slot for slot
— checked against `RamElim.Demo`'s two published runs of the compiled
machine program: the ranks, `kmax`, the in-list offsets and the in-list
targets, mask on and mask off, plus the block readings. It passed on
the first build with no adjustment, which is independent evidence that
the hand-walked engine and a from-scratch re-reading of its five phases
compute the same function. Four negative controls back it: the mask
(the two runs differ), the rank direction (down, not up), the
`CsrSimple` double count on a repeat row, and the two in-place
aliasings (the bucket head read-before-write, the degree
decrement-before-read) each against its transposition.

**Why the elimination loop is the disproportionate one.** Its state is
seven arrays and four scalars — `deg`, `elm`, `rnk`, `idg`, the three
bucket arrays, `sp`, `cnt`, `mind`, `kmax` — against the gate
program's four components. `hnr_while_var` takes the loop state as a
*single* `hnCtxt` conjunct at one relator, so that state is an
eleven-deep `prodAssn` chain, every component of which the branch
merger and the frame matcher walk on every rule attempt. §4.1 measures
what a **two**-component outer state with one inner loop already costs:
the translate driver does not finish it in 4 000 000 heartbeats. The
elimination loop is strictly harder than the goal that stalls, so
attempting it before §4.1's defect is fixed would buy a second
timeout, not a program.

**What retention costs the campaign.** Nothing at the obligation
boundary. `RamElim.Implements`/`elim_spec` are unchanged and the driver
stack keeps consuming them exactly as now; the debt this satellite was
chartered to settle — `elimRezeroCom`'s bridge pair and the `ElimMem`
conjunct — is settled *by the design argument in this file's header*,
which is about how an abstract program takes values rather than cells,
and which does not depend on the elimination loop having been
synthesized. When §4.1's translate defect is repaired, the remaining
four phases are each a copy of §3's shape (a flat or two-level pass
with a `mopSucc` counter and one branch), and the elimination loop is
the one that needs a design decision about the state relator — that
decision belongs with the tower's owner, not with this satellite.
-/

end Lax3Proofs.Refine.ElimSynth

