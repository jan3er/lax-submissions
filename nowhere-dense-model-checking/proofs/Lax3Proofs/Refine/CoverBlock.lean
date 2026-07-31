import Lax3Proofs.RamDriverCompose
import Lax3Proofs.Refine.SigmaLoop
import Lax3Proofs.Refine.MassWeight

/-!
# ND-MC rebase G2 / wave E3a — the **block-driven cover-phase leaf
engines**

Design: `plans/nowhere-dense-model-checking/g2-cost-design.md` §2.2,
§5 (the three cover rows), §6-E3, §7.3. The slot this wave serves is
`hKc`:

    old   ∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m
    new   ∀ j w, kcov · (w + 1) ≤ Kc j w

and the reason the old one cannot be discharged is compiled twice over
in `Refine.G2CostProbe` §5: the landed wrapper carries **two**
carrier-quadratic terms,

    coverPhaseCost n ns = RamCover.coverCost n ns + 12·n² + 81·n + 56
                          ⌊ 100·n² + 50·n·ns ⌋   ⌊ the member copy ⌋

This file is the *leaf* side of killing both. It owns no driver text —
the phase composition is E6's — and it edits nothing: every declaration
below is new, and the landed walks (`RamDriverCompose.copyPrefix_spec`,
`Refine.SigmaLoop.forRangeZeroSum`, `RamCover.centreCost`) are threaded,
not re-run.

## What the wave found before it proved anything (§7 of this file)

**F-1 — the `12·n²` half is an *accounting* loss, not a program
defect.** The landed member copy is
`RamDriver.copyUpto "xmem" (xmmName j) (.var "xp")`: its bound is the
cover's own runtime write pointer, and the landed walk
(`RamDriverCompose.coverImplements`) already derives the leaf cost at
that pointer — `12·m + 6` — and only then inflates it, in one
`Nat.mul_le_mul_left` step against `hmle : m ≤ n*n`, to match the
declared `coverPhaseCost`. So the design doc's "this slot is a
**program** delta (E3), not re-threading" is right about `coverCost`'s
`100·n²` and **wrong about the `12·n²`**: that half needs the arena
pointer threaded into `CoverImplements`' cost parameter and nothing
else. §2 states the leaf at the pointer (`memCopy_spec`, cost
`memCopyK mm = 12·mm + 6`), which is the export E6 wires.

**F-2 — but `mm` is not bounded by the arena's mass, and the gap is
exactly the dead centres.** The cover pass walks *every* centre `c < n`;
a dead centre reaches nothing, yet the pass still writes the centre into
its own block (`Refine.CoverSynth`'s own §1 note: `max tl 1` slots, and
`Refine.MassAlive.block_nonempty` says no block of a cover output is
ever empty). So the arena the copy runs over is
`alive mass + #dead`, and the landed weighted mass mathematics
(`Refine.MassWeight.mass_of_alive_compaction_weight`) bounds only the
**alive** sum, `Σ_k blockWeight (cps k) ≤ d·(w+1)`. At a nested level
whose arena is small inside a large carrier that difference *is* a
carrier charge — the very thing the weight was introduced to remove.
§3's `memCopy_dead_charge_refuted` compiles the refutation.

**And it is a floor, not a slack.** `block_nonempty` carries no
aliveness hypothesis — a centre is always in its own cluster — so the
offsets increase strictly across the whole carrier and
`carrier_le_arena_of_coverOut` (§3) proves `n ≤ m` outright: the member
copy costs at least `12·n + 6` at **every** level, whatever the level's
arena weighs. So F-1 has a sting in its tail. The `12·n²` is an
accounting loss at the *root*; at depth ≥ 1 the copy genuinely reads the
carrier, and no coefficient makes `12·m + 6` fit `k·(w + 1)`. The repair
is therefore forced, and it is E3-b/E6's choice of two: run the copy to
the *alive* prefix (the compaction scan already lists exactly it), or
give `MassWeight` a full-range weighted twin.
`memCopy_alive_prefix_le_weight` (§6) costs the first option — it is
discharged by the same `mass_of_alive_compaction_weight` that supplies
`hball`, with no new mathematics at all.

**F-3 — there is no carrier-free BFS to compose with, anywhere in the
package.** §7.5 of the design doc already corrected the session-wrap
capital list on `BfsQTrail` (it does not exist); this wave confirms the
stronger statement that *nothing* fills the role: the only landed search
export is `Refine.BfsBridge.bfsQCom_spec` at
`bfsQCost n ns = 32 + bfsQK n ns`, a carrier cost, and
`RamCover.centreCost n ns = 100·n + 50·ns + 100` is carrier-charged
through it. §5 compiles what that means for E3 —
`carrierCentre_no_ball_bound`, in `CoverSynth.flat_no_touched_only_bound`'s
shape: the Σ-shaped centre loop of §4 buys **nothing** until the search
under it is block-driven, which is E2's engine and not this wave's. The
per-centre obligation is therefore stated here as a named Prop
(`CentreImplementsB`) with its root discharge compiled
(`centreObligation_of_carrierCost`), which is the honest interface: E3
delivers the loop and the budget shape, E2 delivers the body.

## What is here

* §1 the three numbers a block-driven cover phase is a function of, and
  the cost vocabulary over them — `memCopyK`, `centreK`, `coverLoopK`,
  `coverPhaseCostB`, `kcov`;
* §2 the member copy at the emitted count — a real `Spec`, from
  `copyPrefix_spec`;
* §3 the falsification gates for §2 (F-1's differential and F-2's
  refutation);
* §4 the centre loop at the arena's member list, Σ-charged — a real
  `Spec`, from `forRangeZeroSum`;
* §5 the per-centre obligation, its root discharge, and F-3's
  refutation;
* §6 the export lemmas in the arena-charged interface's shape, with the
  bridge to `MassWeight.mass_of_alive_compaction_weight`;
* §7 the two-block differential instance, `#guard`ed.

## Method note (falsification first)

Every authored budget below was checked against data before it was
proved, and three of the checks are refutations rather than
confirmations (F-2, F-3, and the size-only per-centre budget of
`centre_size_refuted` — the cover's twin of
`MassWeight.turn_size_refuted`). The two-block instance of §7 is built
to *disagree* with a carrier-charged reading, and §7 exhibits the cell
the two member copies disagree at.
-/

namespace Lax3Proofs.Refine.CoverBlock

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover (CoverOut OrdersBy)
open Lax3Proofs.RamDriver (Compacted)
open Lax3Proofs.Refine.MassMath (BlockInj)
open Finset

/-! ## §1 The cost vocabulary

A block-driven cover phase is a function of three numbers and of no
other:

* `mlen` — the number of centres the phase actually turns on, i.e. the
  length of the arena's member list (the compaction scan's `cnum`);
* `bw k` — the weight of the `k`-th centre's ball, `|ball| + edges(ball)`
  in the `Refine.MassWeight` reading (`blockWeight = blockSize + degSum`
  exactly, `MassWeight.blockWeight_eq_add_degSum`);
* `mm` — the number of members the pass emitted, i.e. the cover's own
  write pointer `xp`.

The carrier `n` occurs in none of them. That is the whole content of the
E3 delta, and §6 is the arithmetic that turns it into `hKc`.
-/

/-- **The member copy's cost**, at the emitted member count. This is
`RamDriverCompose.copyPrefix_spec`'s exported cost at the bound
`.var "xp"` (whose `Expr.size` is `1`), read off and named: the landed
walk already pays exactly this, see §2. -/
def memCopyK (mm : ℕ) : ℕ := 12 * mm + 6

/-- **The per-centre budget at the centre's ball weight.** `kc` is the
coefficient the search-plus-emission engine must fit; §5 shows
`kc = 150` is admissible against `G2CostProbe.centreCost_le_weight`'s
constant, i.e. it is read off the landed engine and not chosen. -/
def centreK (kc bw : ℕ) : ℕ := kc * (bw + 1)

/-- **The centre loop's cost**: `Refine.SigmaLoop.forRangeZeroSum`'s
export at the per-centre budget — the sum of the turns, not `mlen` times
the worst one, and not `n` times anything. -/
def coverLoopK (kc mlen : ℕ) (bw : ℕ → ℕ) : ℕ :=
  (∑ k ∈ range mlen, (centreK kc (bw k) + 4)) + 6

/-- **The block-driven cover phase's cost.** Three summands: the centre
loop at the arena's member list, the member copy at the emitted count,
and the arena-driven residue `ka·(mlen + 1)` — the block-offset copy,
the assignment copy and the compaction scan, which are member-driven
only after E2 (design §3c: "the offset copies become member-driven only
in the compacted-CSR variant"). E3 owns the first two; `ka` is carried
as a parameter precisely so that the export of §6 says what it depends
on. -/
def coverPhaseCostB (kc ka mlen : ℕ) (bw : ℕ → ℕ) (mm : ℕ) : ℕ :=
  coverLoopK kc mlen bw + memCopyK mm + ka * (mlen + 1)

/-- **The `hKc` coefficient**: what §6 proves `coverPhaseCostB` fits
into at the arena weight, given the cover-degree bound `D`. -/
def kcov (kc ka D : ℕ) : ℕ := kc * D + kc + 12 * D + ka + 16

/-- The Σ of the per-centre budgets, closed. -/
theorem sum_centreK (kc mlen : ℕ) (bw : ℕ → ℕ) :
    (∑ k ∈ range mlen, (centreK kc (bw k) + 4))
      = kc * (∑ k ∈ range mlen, bw k) + (kc + 4) * mlen := by
  induction mlen with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, centreK]
      ring

/-- The centre loop, closed at the Σ of the ball weights. -/
theorem coverLoopK_eq (kc mlen : ℕ) (bw : ℕ → ℕ) :
    coverLoopK kc mlen bw = kc * (∑ k ∈ range mlen, bw k) + (kc + 4) * mlen + 6 := by
  rw [coverLoopK, sum_centreK]

/-! ## §2 The member copy at the emitted count

The `12·n²` half of the wrapper, at the number the program is actually
driven by.

The program is unchanged and untouched: `RamDriver.coverSave`'s second
copy is already `copyUpto "xmem" (xmmName j) (.var "xp")`, a *runtime*
bound. What moves is the statement — the cost is the pointer, not the
cluster arena's capacity — and §3 exhibits the difference. -/

/-- **The context the member copy runs in**: the cover's write pointer
in `"xp"`, and the source array at its physical length `na` (`n·n` in
the driver, but nothing below needs to know that). -/
def MemCtx (na mm : ℕ) (g : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "xp" = mm ∧ σ.arrs "xmem" = arrOf na g

/-- **The member copy, at the emitted member count.** The one leaf of
the cover phase E3 can state at its honest cost with no new walk: the
copy runs to the cover's write pointer and costs `12·mm + 6`, whatever
the physical capacity `na` of the two arrays is.

`RamDriverCompose.coverImplements` derives exactly this inequality
internally (its `hr₅` step) and then discards it against
`hmle : m ≤ n*n`; here it is, kept. -/
theorem memCopy_spec {B : ℕ} {j mm na : ℕ} {g : ℕ → ℕ}
    (hB : 0 < B) (hmmB : mm < B) (hna : mm ≤ na) (hgB : ∀ k < mm, g k < B) :
    Spec B
      (fun σ => (∃ h, σ.arrs (RamDriver.xmmName j) = arrOf na h) ∧ MemCtx na mm g σ)
      (RamDriver.copyUpto "xmem" (RamDriver.xmmName j) (.var "xp"))
      (fun _ σ' => (∃ h, σ'.arrs (RamDriver.xmmName j) = arrOf na h ∧ ∀ k < mm, h k = g k) ∧
        σ'.vars "i" = mm ∧ MemCtx na mm g σ')
      (memCopyK mm) :=
  (RamDriverCompose.copyPrefix_spec (B := B) mm na na "xmem" (RamDriver.xmmName j)
    (.var "xp") g (MemCtx na mm g) hB hmmB hna hna
    (fun _ _ hQ hv ha => ⟨by rw [hv "xp" (by decide)]; exact hQ.1,
      by rw [ha "xmem" (RamDriverCompose.xmem_ne_xmmName j)]; exact hQ.2⟩)
    (fun _ hQ => by rw [← hQ.1]; exact evalB_var (by rw [hQ.1]; omega))
    (fun _ hQ => hQ.2) hgB).mono (le_of_eq (by simp [memCopyK]))

/-- **F-1, compiled**: the leaf cost is below the wrapper's declared
member-copy term for every arena the driver can produce
(`hmle : mm ≤ n·n`) — so re-stating `CoverImplements` at `memCopyK mm`
is a strengthening with no walk to redo, and the old statement is
recovered by one `Nat.mul_le_mul_left`. -/
theorem memCopyK_le_carrier {mm n : ℕ} (h : mm ≤ n * n) :
    memCopyK mm ≤ 12 * (n * n) + 6 := by
  have : 12 * mm ≤ 12 * (n * n) := Nat.mul_le_mul_left 12 h
  simp only [memCopyK]
  omega

/-- …and it is weight-linear in the emitted count. -/
theorem memCopyK_le_weight {mm D w : ℕ} (h : mm ≤ D * (w + 1)) :
    memCopyK mm ≤ (12 * D + 6) * (w + 1) := by
  have h₁ : 12 * mm ≤ 12 * (D * (w + 1)) := Nat.mul_le_mul_left 12 h
  have h₂ : (12 * D + 6) * (w + 1) = 12 * (D * (w + 1)) + 6 * (w + 1) := by ring
  have h₃ : 6 ≤ 6 * (w + 1) := by nlinarith
  simp only [memCopyK]
  omega

/-! ## §3 The falsification gates for §2

Two probes and one refutation. The first two are the *difference* the
statement delta makes on data; the third is F-2, the finding that the
copy's own bound is not the arena's mass. -/

-- F-1's differential, in one line: a level with a thousand vertices
-- whose cover emits three thousand members pays `36006`, where the
-- landed accounting charges twelve million.
#guard memCopyK 3000 = 36006
#guard 12 * (1000 * 1000) + 6 = 12000006
#guard ¬ (12 * (1000 * 1000) + 6 ≤ 300 * memCopyK 3000)

-- …and the two agree at the degenerate instance the old bound is tight
-- at (a complete cover of a complete graph), so the delta is a real
-- refinement and not a different quantity.
#guard memCopyK (10 * 10) = 12 * (10 * 10) + 6

/-- **F-2 — the arena the member copy runs over is not the arena's
mass.** The cover pass turns on every centre `c < n`, and a *dead*
centre — one the level's mask has cleared — still gets a block of its
own (its search reaches nothing, but `RamCover`'s emission writes the
source; `Refine.MassAlive.block_nonempty`). So the write pointer is

    mm = (alive mass) + #dead

and the landed weighted mass mathematics bounds only the alive half
(`MassWeight.mass_of_alive_compaction_weight` sums over the *compacted*
centres `cps k`, which B8's `alive` clause restricts to living ones).

This is the model of that arithmetic, and the theorem says no
coefficient in `D` and the arena weight covers it: at a level with one
alive member inside a carrier of any size, the dead singletons alone
drive the copy. -/
def deadSingletonArena (mass dead : ℕ) : ℕ := mass + dead

/-- **The refutation.** For every proposed coefficient `K`, there is a
level — one alive member, weight `1`, and enough dead carrier — at which
the member copy exceeds `K·(w+1)`. The repair is not a bigger constant:
it is running the copy to the *alive* prefix (E3-b / E6), or a
full-range weighted mass bound in `MassWeight` (E5). -/
theorem memCopy_dead_charge_refuted (K D : ℕ) :
    ∃ mass dead w : ℕ, mass ≤ D * (w + 1) ∧ 0 < w ∧
      ¬ (memCopyK (deadSingletonArena mass dead) ≤ K * (w + 1)) := by
  refine ⟨0, K + 1, 1, by omega, by omega, ?_⟩
  simp only [memCopyK, deadSingletonArena]
  omega

/-- **F-2, sharpened into a floor: the cover's arena is never smaller
than the carrier.** `Refine.MassAlive.block_nonempty` holds at *every*
position `c < n`, with no aliveness hypothesis — a centre is always in
its own cluster — so the block offsets strictly increase across the
whole carrier, and `CoverOut.last` reads the write pointer off the top:

    n ≤ m.

Consequence for `hKc`: `RamDriver.coverSave`'s member copy costs at
least `12·n + 6` at **every** level of the recursion, whatever the
level's arena weighs. So the `12·n²` of `coverPhaseCost` is not merely
an accounting artefact of F-1 at nested depths — at depth ≥ 1 the copy
really does read the carrier, and no constant `k` makes `12·m + 6`
fit `k·(w + 1)`. The repair is not a bigger coefficient; it is the
alive prefix (`memCopy_alive_prefix_le_weight`), and this theorem is
the proof that nothing else will do. -/
theorem carrier_le_arena_of_coverOut {n : ℕ} {G : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {r m : ℕ}
    (hord : OrdersBy n π ord) (hout : CoverOut G A₀ π ord r m Xoff Xmem asg) :
    n ≤ m := by
  have key : ∀ k, k ≤ n → k ≤ Xoff k := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ i ih =>
        intro hi
        have h₁ : Xoff i < Xoff (i + 1) := MassAlive.block_nonempty hord hout (by omega)
        have h₂ := ih (by omega)
        omega
  have h := key n le_rfl
  rw [hout.last] at h
  exact h

/-- **The carrier floor on the member copy**, read off the last
theorem. -/
theorem memCopyK_carrier_floor {n : ℕ} {G : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {r m : ℕ}
    (hord : OrdersBy n π ord) (hout : CoverOut G A₀ π ord r m Xoff Xmem asg) :
    12 * n + 6 ≤ memCopyK m := by
  have := carrier_le_arena_of_coverOut hord hout
  simp only [memCopyK]
  omega

-- the same on data: a level whose arena weighs `1`, inside a carrier of
-- a million dead vertices, at the generous coefficient `10⁵` — the copy
-- pays `12·n`, which is the carrier charge the weight was introduced to
-- remove
#guard ¬ (memCopyK (deadSingletonArena 1 (10 ^ 6)) ≤ 10 ^ 5 * (1 + 1))
-- …and it is exactly the dead half that does it: the alive half alone
-- clears the same budget with four orders of magnitude to spare
#guard memCopyK (deadSingletonArena 1 0) ≤ 10 ^ 5 * (1 + 1)

/-! ## §4 The centre loop at the arena's member list

The loop-header delta of design §6-E3, stated once and for all. The
landed cover pass's centre loop is `while c < n` over the *carrier*
(`RamCover.coverBf n`); the block-driven one walks the compaction scan's
member list, `while x < mlen`, and — crucially — is charged with
`Refine.SigmaLoop.forRangeZeroSum`, one budget per turn, so the loop
pays `Σ_k centreK kc (bw k)` and not `mlen · max`.

Nothing here is a new loop rule: `forRangeZeroSum` is landed capital and
this is its instantiation at the cover's counter. What is new is the
*shape of the per-turn budget* — the centre's ball weight — and the
export of §6 that it feeds. -/

/-- **The block-driven centre loop's text**: the counter, the member
count as the bound, the turn. -/
def centreLoopCom (x mlenName : String) (body : Com) : Com :=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var mlenName)) body)

/-- **The per-centre obligation** a block-driven cover turn owes: the
turn at counter value `k` runs at the budget of *its own* centre's ball
weight. `bw` is the ball-weight reading of `Refine.MassWeight`
(`blockWeight = blockSize + degSum`), so `centreK kc (bw k)` is
`O(block + edges(block))` and mentions no carrier. -/
def CentreImplementsB (B : ℕ) (x : String) (body : Com) (I : Env → Prop)
    (mlen kc : ℕ) (bw : ℕ → ℕ) : Prop :=
  ∀ k, k < mlen → Spec B (fun σ => I σ ∧ σ.vars x = k) body
    (fun _ σ' => I σ' ∧ σ'.vars x = k + 1) (centreK kc (bw k))

/-- **The centre loop, discharged at the Σ of the ball weights.** The
carrier does not occur in the cost, and `mlen` is the arena's member
count, not `n`. -/
theorem centreLoop_spec {B : ℕ} {body : Com} {I : Env → Prop} (x mlenName : String)
    (mlen kc : ℕ) (bw : ℕ → ℕ) (hNB : mlen < B)
    (hxN : ∀ σ, I σ → σ.vars x ≤ mlen) (hm : ∀ σ, I σ → σ.vars mlenName = mlen)
    (hbody : CentreImplementsB B x body I mlen kc bw) :
    Spec B (fun σ => I (σ.setVar x 0)) (centreLoopCom x mlenName body)
      (fun _ σ' => I σ' ∧ σ'.vars x = mlen) (coverLoopK kc mlen bw) :=
  SigmaLoop.forRangeZeroSum x mlenName I mlen (fun k => centreK kc (bw k)) hNB hxN hm hbody

/-- **The Σ-shape is a strict refinement of the uniform one.** With
every centre's ball the same weight, the loop's cost is exactly the
uniform rule's `(centreK kc bw + 4)·mlen + 6` — so re-threading a
consumer to `centreLoop_spec` never costs slack
(`SigmaLoop.sum_const_eq_uniform`, at this budget). -/
theorem coverLoopK_const (kc mlen bw : ℕ) :
    coverLoopK kc mlen (fun _ => bw) = (centreK kc bw + 4) * mlen + 6 :=
  SigmaLoop.sum_const_eq_uniform mlen (centreK kc bw)

/-- **The cover's twin of `MassWeight.turn_size_refuted`**: a per-centre
budget read at the block's *size* bounds no block-driven cover turn. At
a star's centre — one member, many slots — the ball weight is the degree
and the size is `1`, so every size-read coefficient is exceeded. This is
why §1's budget reads the weight. -/
theorem centre_size_refuted (ct : ℕ) :
    ∃ mlen bw : ℕ, 0 < mlen ∧ ¬ (coverLoopK 1 mlen (fun _ => bw) ≤ ct * (mlen + 1)) := by
  refine ⟨1, 2 * ct + 1, by omega, ?_⟩
  rw [coverLoopK_const, centreK]
  omega

-- on data: a single star centre of degree 10⁴ — one member, ten
-- thousand slots — budgeted at its block's SIZE with the turn
-- coefficient `200` of `G2CostProbe.blockLeaves_le_weight`
#guard ¬ (coverLoopK 1 1 (fun _ => 10001) ≤ 200 * (1 + 1))
-- …and the same turn, budgeted at its block's WEIGHT, clears
#guard coverLoopK 1 1 (fun _ => 10001) ≤ 200 * (10001 + 1)

/-! ## §5 The per-centre body — what E3 can discharge, and what it
cannot

F-3, compiled. The obligation of §4 is the shape; the *body* that
discharges it is a search plus an emission. The emission half is landed
and carrier-free (`Refine.CoverSynth.emitLoopCost`, whose
`emitCost_touched_only` reads it as `touches • emitUnit + one`, and
whose `towerEmitAgets = 3·touches` mentions no `n`). The search half is
**not**: the package's only search export is
`Refine.BfsBridge.bfsQCom_spec` at a carrier cost, and the design doc's
§7.5 correction already recorded that the touched-only BFS named in the
session-wrap capital list (`BfsQTrail`) does not exist.

So E3 can state the obligation and discharge it at the *root*, where a
centre's ball is the whole carrier and the landed per-centre cost is
weight-linear by `G2CostProbe.centreCost_le_weight`'s own constant. At
nested arenas it stays open until E2's block-driven search lands, and
the theorem below says that in the negative. -/

/-- **`kc = 150` is admissible, and it is read off the landed engine.**
The constant is `G2CostProbe.centreCost_le_weight`'s: the landed
per-centre cost of `RamCover` fits the proposed budget at the root
arena's weight. -/
theorem centreK_root_admissible (n ns : ℕ) :
    RamCover.centreCost n ns ≤ centreK 150 (n + ns) := by
  simp only [RamCover.centreCost, centreK]
  omega

/-- **The root discharge of the obligation.** Any per-centre walk that
runs at the landed carrier cost discharges the block-driven obligation
as soon as every centre's ball weight has reached the root arena's — the
root instance, where the two readings coincide. This is the honest
composition surface for E6: the loop of §4 is available *today* at the
root, and E2's block-driven body replaces `RamCover.centreCost` by a
ball-weight cost at nested depths without touching anything here. -/
theorem centreObligation_of_carrierCost {B : ℕ} {body : Com} {I : Env → Prop} {x : String}
    {mlen n ns : ℕ} {bw : ℕ → ℕ} (hbw : ∀ k < mlen, n + ns ≤ bw k)
    (h : ∀ k, k < mlen → Spec B (fun σ => I σ ∧ σ.vars x = k) body
      (fun _ σ' => I σ' ∧ σ'.vars x = k + 1) (RamCover.centreCost n ns)) :
    CentreImplementsB B x body I mlen 150 bw := by
  intro k hk
  refine (h k hk).mono (le_trans (centreK_root_admissible n ns) ?_)
  exact Nat.mul_le_mul_left 150 (by have := hbw k hk; omega)

/-- **F-3 — the loop alone buys nothing.** In the shape of
`CoverSynth.flat_no_touched_only_bound`: a per-centre cost that is a
function of the carrier has **no** bound of the ball-weight shape
`c₁ · Σ balls + c₂`, for any constants fixed before the input. The
family is the honest one — constant-size balls, so the block-driven
reading is `Θ(mlen)` — and the carrier is free to grow under it.

Read together with §4 this is the wave's scoping statement: E3 delivers
the Σ-shaped loop, the ball-weight budget and the member copy; the
`100·n²` of `coverCost` dies only when E2's search does. -/
theorem carrierCentre_no_ball_bound (c₁ c₂ : ℕ) :
    ∃ n ns mlen bw : ℕ, 0 < mlen ∧ 0 < n ∧
      ¬ (mlen * RamCover.centreCost n ns ≤ c₁ * (mlen * bw) + c₂) := by
  refine ⟨c₁ + c₂ + 1, 0, 1, 1, by omega, by omega, ?_⟩
  simp only [RamCover.centreCost]
  omega

/-! ## §6 The exports, in the arena-charged interface's shape

`hKc`'s new form is `∀ j w, kcov · (w + 1) ≤ Kc j w`; what a producer
owes is that the phase's cost is below `kcov · (w + 1)`. That is the
theorem below, from three hypotheses which are exactly the landed
weighted mass mathematics:

* `hmlen : mlen ≤ w` — `mass_of_alive_compaction_weight`'s first
  conjunct (`cnum ≤ arenaWeight`);
* `hball : Σ_k bw k ≤ D·(w+1)` — its second
  (`Σ blockWeight (cps k) ≤ d·(arenaWeight + 1)`);
* `hmm : mm ≤ D·(w+1)` — **not** landed, and F-2 says why. It is
  carried as a hypothesis so that the export is honest about its one
  open producer.
-/

/-- **The cover phase at the arena weight.** -/
theorem coverPhaseCostB_le_weight {kc ka mlen mm D w : ℕ} {bw : ℕ → ℕ}
    (hmlen : mlen ≤ w) (hball : (∑ k ∈ range mlen, bw k) ≤ D * (w + 1))
    (hmm : mm ≤ D * (w + 1)) :
    coverPhaseCostB kc ka mlen bw mm ≤ kcov kc ka D * (w + 1) := by
  have h₁ : kc * (∑ k ∈ range mlen, bw k) ≤ kc * (D * (w + 1)) :=
    Nat.mul_le_mul_left kc hball
  have h₂ : (kc + 4) * mlen ≤ (kc + 4) * (w + 1) :=
    Nat.mul_le_mul_left (kc + 4) (by omega)
  have h₃ : 12 * mm ≤ 12 * (D * (w + 1)) := Nat.mul_le_mul_left 12 hmm
  have h₄ : ka * (mlen + 1) ≤ ka * (w + 1) := Nat.mul_le_mul_left ka (by omega)
  have h₅ : (12 : ℕ) ≤ 12 * (w + 1) := by nlinarith
  have hexp : kcov kc ka D * (w + 1)
      = kc * (D * (w + 1)) + (kc + 4) * (w + 1) + 12 * (D * (w + 1))
        + ka * (w + 1) + 12 * (w + 1) := by
    simp only [kcov]; ring
  rw [coverPhaseCostB, coverLoopK_eq, memCopyK, hexp]
  omega

/-- **The bridge to the landed weighted mass mathematics.** The two
hypotheses `coverPhaseCostB_le_weight` needs about the *arena* are
exactly `MassWeight.mass_of_alive_compaction_weight`'s two conjuncts, at
`bw k = blockWeight (cps k)` and `w = arenaWeight`. Only `hmm` is left,
and F-2 names its producer. -/
theorem coverPhaseCostB_le_weight_of_compaction {n : ℕ} {G H : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg cps : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {r m cnum d mm kc ka : ℕ}
    (hord : OrdersBy n π ord) (hout : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hinj : BlockInj n Xoff Xmem)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hcomp : Compacted n cnum m A₀ ord Xoff cps)
    (hmm : mm ≤ d * (MassWeight.arenaWeight n H A₀ + 1)) :
    coverPhaseCostB kc ka cnum
        (fun k => MassWeight.blockWeight n H Xoff Xmem (cps k)) mm
      ≤ kcov kc ka d * (MassWeight.arenaWeight n H A₀ + 1) := by
  obtain ⟨hcnum, hsum⟩ :=
    MassWeight.mass_of_alive_compaction_weight (H := H) hord hout hinj hk hcomp
  exact coverPhaseCostB_le_weight hcnum hsum hmm

/-- **The F-2 repair, costed.** The finding is that the member copy's
bound is the cover's write pointer, which counts the dead centres'
singleton blocks as well as the arena's mass. The repair is to run the
copy to the *alive* prefix — the compaction scan already lists exactly
those centres (`RamDriver.compactCom`, whose inner `ite` reads
`alv[ord[i]]`, and B8's `Compacted.alive` clause) — and this is what it
buys: the copy's cost is then weight-linear, discharged by the **same**
`mass_of_alive_compaction_weight` that supplies `hball`, with no new
mathematics at all.

So E6's choice is a one-line one: either thread this hypothesis, or
accept a `12·#dead` carrier term in `hKc`. -/
theorem memCopy_alive_prefix_le_weight {n : ℕ} {G H : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg cps : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {r m cnum d mm : ℕ}
    (hord : OrdersBy n π ord) (hout : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hinj : BlockInj n Xoff Xmem)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hcomp : Compacted n cnum m A₀ ord Xoff cps)
    (halive : mm ≤ ∑ k ∈ range cnum, MassWeight.blockWeight n H Xoff Xmem (cps k)) :
    memCopyK mm ≤ (12 * d + 6) * (MassWeight.arenaWeight n H A₀ + 1) :=
  memCopyK_le_weight (le_trans halive
    (MassWeight.mass_of_alive_compaction_weight (H := H) hord hout hinj hk hcomp).2)

/-- **The whole phase at the root, with the constants the probe
admits.** `kc = 150` (`centreK_root_admissible`), and the arena residue
at `ka` — so the `hKc` coefficient the E6 wave threads is
`kcov 150 ka D = 150·D + 12·D + ka + 166`. Compare the landed
wrapper, which fits **no** weight-linear budget at all
(`G2CostProbe`'s §5 negative finding). -/
theorem kcov_root (ka D : ℕ) : kcov 150 ka D = 162 * D + ka + 166 := by
  simp only [kcov]; ring

-- the coefficient is in the probe's family: the honest engine constants
-- of `G2CostProbe` are `150` (centre), `200` (turn leaves), `333`
-- (elimination) — `kcov` adds `12·D` for the member copy and `ka` for
-- the arena residue, and nothing else.
#guard kcov 150 0 0 = 166

/-! ## §7 The two-block differential instance

The instance is built to disagree with a carrier-charged reading: a
carrier of a thousand vertices, of which the level's arena holds four,
in two blocks of two. Every carrier-charged reading pays for the
thousand; every block-driven one pays for the four.

The member arrays are the driver's: `dXoff` is the block-offset array
(`n + 1` cells, of which only the first three are nonzero here), `dXmem`
the cluster arena at its physical capacity, and `dMm = 4` the cover's
write pointer. -/

section Demo

/-- Two blocks, `{0,1}` and `{3,5}`, at offsets `0,2,4`. -/
def dXoff : List ℕ := [0, 2, 4, 4, 4, 4, 4]

/-- The arena: four emitted members, then the capacity the driver
allocated (`n·n` in the real thing, `12` here). -/
def dXmem : List ℕ := [0, 1, 3, 5] ++ List.replicate 8 0

/-- The cover's write pointer. -/
def dMm : ℕ := 4

/-- The carrier the level sits in. -/
def dN : ℕ := 1000

/-- The two blocks' ball weights: two members and three slots each. -/
def dBw : ℕ → ℕ := fun _ => 5

/-- The block at position `c`, read off the two arrays — the only
reading of the arena any consumer below the cover performs. -/
def blockAt (xoff xmem : List ℕ) (c : ℕ) : List ℕ :=
  (List.range (xoff[c + 1]! - xoff[c]!)).map (fun i => xmem[xoff[c]! + i]!)

/-- The member copy at the pointer, with arbitrary junk above it — the
"copy `mm` cells" reading. -/
def copiedAt (mm : ℕ) (junk : ℕ) : List ℕ :=
  (List.take mm dXmem) ++ List.replicate (dXmem.length - mm) junk

-- **Semantic agreement**: everything a level reads off the arena is
-- determined by the prefix below the write pointer, so the copy at `mm`
-- and the copy at the full capacity give the same blocks, whatever the
-- junk above the pointer is.
#guard blockAt dXoff dXmem 0 = [0, 1]
#guard blockAt dXoff dXmem 1 = [3, 5]
#guard blockAt dXoff (copiedAt dMm 0) 0 = blockAt dXoff dXmem 0
#guard blockAt dXoff (copiedAt dMm 0) 1 = blockAt dXoff dXmem 1
#guard blockAt dXoff (copiedAt dMm 77) 0 = blockAt dXoff dXmem 0
#guard blockAt dXoff (copiedAt dMm 77) 1 = blockAt dXoff dXmem 1

-- …and the two copies **do** differ, at the first cell above the
-- pointer: the delta is a real difference in the program's write set,
-- not a no-op.
#guard (copiedAt dMm 77)[dMm]! ≠ dXmem[dMm]!
#guard (copiedAt dMm 77)[dMm]! = 77
#guard dXmem[dMm]! = 0

-- **Cost disagreement**, the point of the wave. The block-driven
-- phase's three summands at this instance, against the landed
-- wrapper's.
#guard memCopyK dMm = 54

/-- The centre loop pays for the two blocks and nothing else. -/
theorem coverLoopK_demo : coverLoopK 150 2 dBw = 1814 := by
  simp [coverLoopK, centreK, dBw]

/-- The whole block-driven phase, at this instance. -/
theorem coverPhaseCostB_demo : coverPhaseCostB 150 20 2 dBw dMm = 1928 := by
  rw [coverPhaseCostB, coverLoopK_demo, memCopyK, dMm]

/-- The landed wrapper, at the same instance. -/
theorem coverPhaseCost_demo :
    RamDriverCompose.coverPhaseCost dN (2 * dN) = 212281156 := by
  simp only [RamDriverCompose.coverPhaseCost, RamCover.coverCost, dN]

/-- The landed wrapper overpays this instance by five orders of
magnitude, and the gap is the carrier: it is `Θ(n²)` in a level whose
arena has four members. -/
theorem demo_gap :
    ¬ (RamDriverCompose.coverPhaseCost dN (2 * dN)
        ≤ 10 ^ 4 * coverPhaseCostB 150 20 2 dBw dMm) := by
  rw [coverPhaseCost_demo, coverPhaseCostB_demo]
  norm_num

/-- The block-driven cost, in contrast, is inside the `hKc` budget at
the instance's own arena weight (`w = 10`: four members and six slots)
with the admissible coefficients. -/
theorem demo_fits : coverPhaseCostB 150 20 2 dBw dMm ≤ kcov 150 20 4 * (10 + 1) := by
  rw [coverPhaseCostB_demo, kcov]
  norm_num

end Demo

end Lax3Proofs.Refine.CoverBlock
