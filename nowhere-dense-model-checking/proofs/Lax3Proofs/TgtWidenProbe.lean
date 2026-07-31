import Lax3Proofs.RamAugment
import Lax3Proofs.RamDriver
import Lax3Proofs.TgtCoupling

/-!
**The `tgt`-widening probe (rebase B5): the K₁,₄ coupling, run.**

`Lax3Proofs.TgtCoupling` refutes the `ns`-reuse reading of the two `tgt`
couplings at the abstract level: on `K₁,₄` the fraternity graph occupies
`12` slots against the star's `8`, so the level's target array cannot
hold a round's. This file is the *machine* half of that falsification
gate, both ways:

* **the un-widened phase remains refuted** — `RamAugment.augCom` run on
  the in-lists of `K₁,₄` with `"tgt"` allocated at the level's own slot
  count `8` goes *stuck*: the fraternity fill's ninth store has no
  in-range derivation, which in IMP+ is stuck, not defaulted (the same
  store discipline as `Lax13Proofs.Imp.BigStep.store`);
* **the widened phase passes on that instance** — the same round with
  `"tgt"` at a width covering `TgtCoupling.chainWidth`'s budget runs to
  completion and reports the machine's own fraternity slot count
  `mf = 12`, matching `TgtCoupling.csrSlots_fratGraph_starOr` exactly,
  and the augmented in-lists `∅ | ⋯` of ten arcs.

Two controls pin the instrument.

* **`K₁,₃` is one leaf below the witness** (`TgtCoupling`'s own
  refutation of "a smaller star refutes"): there `fratSlots = ns = 6`
  and the *un-widened* round completes — so the `K₁,₄` stuck really is
  the `12 > 8` coupling and not some unrelated width.
* **The worked example of `RamAugment.Demo` replays**: the four-vertex
  orientation whose compiled RAM run is `#guard`ed there produces,
  under this file's interpreter, cell for cell the same ranks, bound,
  slot counts and augmented block structure. That anchors the
  interpreter against the landed golden run.

### The instrument

IMP+ has no executable interpreter in the repo — the demos run the
*compiled* RAM programs, whose flat memory cannot detect an
out-of-range store (the compiler lays arrays out contiguously). The
probe therefore carries a small fuelled interpreter over the `Com`
syntax that *mirrors* the bounded big-step semantics
(`Lax13Proofs.Bounds.BigStepB`): expression evaluation refuses values
reaching `B` at every subterm (`fit`), a store requires its index below
the array's length, and a violation is `stuck`. The state is an
association list rather than `Env`'s function fields so that the
interpreter runs in the elaborator at probe scale. The mirror is by
construction (each equation is `BigStepB`'s rule read as a program) and
anchored by the golden-run control; a formal `exec = ok → Run` bridge
is deliberately *not* claimed here — the load-bearing refutation stays
the compiled one in `TgtCoupling`, and this file is the differential
evidence the falsification gate asks for.
-/

namespace Lax3Proofs.TgtWidenProbe

open Lax13Proofs.Imp

/-! ### The probe state: association lists, so the interpreter runs -/

/-- Scalars as an association list. Reads default to `0`, as a machine's
fresh memory does. -/
def getV (ρ : List (String × ℕ)) (x : String) : ℕ :=
  ((ρ.find? (·.1 == x)).map (·.2)).getD 0

/-- Update a scalar in place. -/
def setV : List (String × ℕ) → String → ℕ → List (String × ℕ)
  | [], x, v => [(x, v)]
  | (y, w) :: t, x, v => if y == x then (x, v) :: t else (y, w) :: setV t x v

/-- Arrays as an association list. A name that was never allocated is
the empty array, so every access to it is out of range — exactly the
refutation-by-absent-array discipline of the driver's memory clauses. -/
def getA (ρ : List (String × List ℕ)) (a : String) : List ℕ :=
  ((ρ.find? (·.1 == a)).map (·.2)).getD []

/-- Update one cell of an array in place (the caller has checked the
range, as `BigStepB.store` does). -/
def setA : List (String × List ℕ) → String → ℕ → ℕ → List (String × List ℕ)
  | [], a, i, v => [(a, [].set i v)]
  | (b, l) :: t, a, i, v => if b == a then (a, l.set i v) :: t else (b, l) :: setA t a i v

/-- The probe state: scalars and arrays. -/
structure PSt where
  vars : List (String × ℕ)
  arrs : List (String × List ℕ)

/-! ### Bounded evaluation, mirrored from `Lax13Proofs.Bounds` -/

/-- `Bounds.fit`, mirrored. -/
def fitP (B v : ℕ) : Option ℕ := if v < B then some v else none

/-- `Expr.evalB`, mirrored equation by equation. -/
def evalE (B : ℕ) : Expr → PSt → Option ℕ
  | .lit n, _ => fitP B n
  | .var x, σ => fitP B (getV σ.vars x)
  | .get a i, σ => (evalE B i σ).bind fun k => ((getA σ.arrs a)[k]?).bind (fitP B)
  | .bin op e f, σ =>
      (evalE B e σ).bind fun m => (evalE B f σ).bind fun n => fitP B (op.apply m n)

/-- `Cond.evalB`, mirrored. -/
def evalC (B : ℕ) : Cond → PSt → Option Bool
  | .eq e f, σ => (evalE B e σ).bind fun m => (evalE B f σ).map fun n => m == n
  | .lt e f, σ => (evalE B e σ).bind fun m => (evalE B f σ).map fun n => decide (m < n)

/-- The interpreter's verdict: a final state, a stuck step, or fuel out.
`stuck` is what an out-of-range access or an over-bound value is in the
bounded semantics; `fuel` never occurs in the probes below (their fuel
covers the derivation). -/
inductive PRes
  | ok (σ : PSt)
  | stuck
  | fuel

/-- `BigStepB`, read as a fuelled program: each equation is one rule.
The fuel bounds the derivation's depth; the two tape rules are not
modelled (`augCom` has neither `read` nor `write`) and are conservative:
`read` is stuck, `write` evaluates and drops. -/
def exec (B : ℕ) : ℕ → Com → PSt → PRes
  | 0, _, _ => .fuel
  | _ + 1, .skip, σ => .ok σ
  | _ + 1, .assign x e, σ =>
      match evalE B e σ with
      | some v => .ok ⟨setV σ.vars x v, σ.arrs⟩
      | none => .stuck
  | _ + 1, .store a i e, σ =>
      match evalE B i σ, evalE B e σ with
      | some k, some v =>
          if k < (getA σ.arrs a).length then .ok ⟨σ.vars, setA σ.arrs a k v⟩ else .stuck
      | _, _ => .stuck
  | f + 1, .seq c d, σ =>
      match exec B f c σ with
      | .ok σ' => exec B f d σ'
      | r => r
  | f + 1, .ite b c d, σ =>
      match evalC B b σ with
      | some true => exec B f c σ
      | some false => exec B f d σ
      | none => .stuck
  | f + 1, .while b c, σ =>
      match evalC B b σ with
      | some true =>
          match exec B f c σ with
          | .ok σ' => exec B f (.while b c) σ'
          | r => r
      | some false => .ok σ
      | none => .stuck
  | _ + 1, .read _, _ => .stuck
  | _ + 1, .write e, σ =>
      match evalE B e σ with
      | some _ => .ok σ
      | none => .stuck

/-! ### Projections of a verdict, for the `#guard`s -/

def PRes.isOk : PRes → Bool
  | .ok _ => true
  | _ => false

def PRes.isStuck : PRes → Bool
  | .stuck => true
  | _ => false

/-- A scalar of the final state (zero when the run did not finish). -/
def PRes.scalar (r : PRes) (x : String) : ℕ :=
  match r with
  | .ok σ => getV σ.vars x
  | _ => 0

/-- A cell of the final state (zero when the run did not finish). -/
def PRes.cell (r : PRes) (a : String) (i : ℕ) : ℕ :=
  match r with
  | .ok σ => (getA σ.arrs a).getD i 0
  | _ => 0

/-! ### The round's memory

`RamAugment.AugPre`'s twenty-six arrays at their lengths, with the
accumulators and stamps zeroed (a fresh machine memory), the in-lists of
the probed orientation in `doff`/`dtg`, and — the probe's one dial —
`"tgt"` at a chosen length `tl`. Everything else is at the width `W`. -/

def augSt (n W tl : ℕ) (doff dtg : List ℕ) : PSt where
  vars := [("n", n)]
  arrs :=
    [("doff", doff), ("dtg", dtg ++ List.replicate (W - dtg.length) 0),
     ("ooff", List.replicate (n + 1) 0), ("otg", List.replicate W 0),
     ("ofl", List.replicate n 0),
     ("off", List.replicate (n + 1) 0), ("tgt", List.replicate tl 0),
     ("ffl", List.replicate n 0),
     ("alv", List.replicate n 0), ("deg", List.replicate n 0),
     ("elm", List.replicate n 0), ("rnk", List.replicate n 0),
     ("idg", List.replicate n 0), ("bh", List.replicate (n + 1) 0),
     ("bv", List.replicate (n + W + 1) 0), ("bn", List.replicate (n + W + 1) 0),
     ("ioff", List.replicate (n + 1) 0), ("ifl", List.replicate n 0),
     ("itg", List.replicate W 0),
     ("noff", List.replicate (n + 1) 0), ("nfl", List.replicate n 0),
     ("ntg", List.replicate W 0),
     ("stf", List.replicate n 0), ("sta", List.replicate n 0),
     ("std", List.replicate n 0), ("ste", List.replicate n 0)]

/-- The word bound of the probes: far above every value and address a
five-vertex round forms. -/
def pB : ℕ := 100000

/-- Fuel covering the derivations below with room. -/
def pF : ℕ := 2000000

/-! ### The anchor: `RamAugment.Demo`, replayed

The four-vertex orientation `∅ | 0 | 0 1 | 2` whose compiled run is
`#guard`ed in `RamAugment.Demo`: ranks `0 1 2 3`, bound `1`, fraternity
slots `2`, offsets `0 0 1 3 6`, slots `| 0 | 0 1 | 2 0 1`, ten cells in
all. The interpreter must reproduce every one of them. -/

def demoRun : PRes :=
  exec pB pF RamAugment.augCom (augSt 4 16 16 [0, 0, 1, 3, 4] [0, 0, 1, 2])

#guard demoRun.isOk
#guard (List.range 4).map (demoRun.cell "rnk") = [0, 1, 2, 3]
#guard demoRun.scalar "kmax" = 1
#guard demoRun.scalar "mf" = 2
#guard (List.range 5).map (demoRun.cell "noff") = [0, 0, 1, 3, 6]
#guard (List.range 6).map (demoRun.cell "ntg") = [0, 0, 1, 2, 0, 1]
#guard demoRun.scalar "mn" = 6

/-! ### The gate, negative half: `K₁,₄` at the level's own width

The star on four leaves oriented into its centre — `TgtCoupling.starOr`,
in-lists `{1,2,3,4} | ∅ | ∅ | ∅ | ∅` — with `"tgt"` at the *level's*
slot count `csrSlots starOr.toGraph = 8`. The fraternity graph is `K₄`
on the leaves at `12` slots, so the fraternity fill's ninth store is out
of range and the round is **stuck**: the machine form of
`TgtCoupling.not_csrSlots_fratGraph_le_csrSlots`. -/

def star5doff : List ℕ := [0, 4, 4, 4, 4, 4]
def star5dtg : List ℕ := [1, 2, 3, 4]

/-- The un-widened round. -/
def star5Narrow : PRes := exec pB pF RamAugment.augCom (augSt 5 64 8 star5doff star5dtg)

-- **the un-widened phase remains refuted**
#guard star5Narrow.isStuck

-- and the stall is the fraternity pass's, not a later one: the first
-- two passes alone already stick at the same width
#guard (exec pB pF (.seq RamAugment.outPass RamAugment.fratPass)
  (augSt 5 64 8 star5doff star5dtg)).isStuck

/-! ### The gate, positive half: the same round, widened

The same instance with `"tgt"` at the width `W = 64` — above the `12`
slots the round needs, and inside every `chainWidth` budget that
dominates this instance (`TgtCoupling`'s `#guard`s check
`csrSlots (fratGraph starOr) < chainWidth 5 1 1 2`). The round runs to
completion; the machine's own fraternity slot count is the abstract
`12`; and the augmented in-lists are the hand computation: the four old
arcs into the centre kept, the six edges of `K₄` oriented by the
elimination's ranking, no transitive arcs — ten in all. -/

def star5Wide : PRes := exec pB pF RamAugment.augCom (augSt 5 64 64 star5doff star5dtg)

-- **the widened phase passes on the witness instance**
#guard star5Wide.isOk

-- the machine's fraternity slot count is `TgtCoupling`'s `12`, above
-- the level's `8` — the coupling, measured by the run itself
#guard star5Wide.scalar "mf" = 12
#guard ¬ (star5Wide.scalar "mf" ≤ 8)

-- the augmented block structure: the centre keeps its four arcs, the
-- six fraternal edges are oriented somewhere among the leaves, nothing
-- else appears
#guard star5Wide.scalar "mn" = 10
#guard star5Wide.cell "noff" 0 = 0
#guard star5Wide.cell "noff" 1 = 4
#guard star5Wide.cell "noff" 5 = 10
#guard (List.range 4).map (star5Wide.cell "ntg") = [1, 2, 3, 4]

-- the greedy bound of `K₄` is its degeneracy
#guard star5Wide.scalar "kmax" = 3

/-! ### The control: no smaller star refutes

`K₁,₃`, one leaf below the witness: `fratSlots = 6 = ns`, so the
*un-widened* round completes — the `K₁,₄` stuck is the `12 > 8`
coupling and nothing else. This is the machine form of `TgtCoupling`'s
`#guard csrSlots (fratGraph star3Or) = 6 = csrSlots star3Or.toGraph`. -/

def star4Narrow : PRes :=
  exec pB pF RamAugment.augCom (augSt 4 64 6 [0, 3, 3, 3, 3] [1, 2, 3])

#guard star4Narrow.isOk
#guard star4Narrow.scalar "mf" = 6
#guard star4Narrow.scalar "mn" = 6


/-! ### The symmetrization gate (rebase F-c)

The same `K₁,₄` instance, one pass further on. After the round the
augmented orientation `D₁` is in `noff`/`ntg`; the ordering phase relinks
it into `doff`/`dtg` and — in the **new** text — symmetrizes it into
`off`/`tgt` before the final elimination. What is measured here is
*why* the symmetrization is there, and it is measured as a
**differential**: the two texts' final eliminations report different
bounds, so the old one cannot be producing the augmented graph's data.

The instance is the sharpest small one. `D₁` has ten arcs on five
vertices, so `(D₁).toGraph` is `K₅` — degeneracy `4` — while the level's
own graph is the star `K₁,₄`, degeneracy `1`. -/

/-- The augmented orientation the round left, read off `star5Wide`: the
centre keeps its four arcs and the six fraternal edges of `K₄` are
oriented among the leaves. -/
def aug5doff : List ℕ := [0, 4, 4, 5, 7, 10]

/-- Its targets. -/
def aug5dtg : List ℕ := [1, 2, 3, 4, 1, 1, 2, 1, 2, 3]

-- the round really did leave these two, so the probe below is the
-- *next* pass of the same run and not a fresh hand computation
#guard (List.range 6).map (star5Wide.cell "noff") = aug5doff
#guard (List.range 10).map (star5Wide.cell "ntg") = aug5dtg

/-- The ordering phase's state at the symmetrization: the chain's last
orientation in `doff`/`dtg`, the counting sort's arrays zeroed, and
`"tgt"` at the `2 · 10 = 20` slots the union occupies. -/
def sym5St : PSt := augSt 5 64 20 aug5doff aug5dtg

/-- The symmetrization, run. -/
def sym5Run : PRes := exec pB pF RamDriver.symCom sym5St

#guard sym5Run.isOk

-- the offsets are the sums of the in- and out-offsets, so every row is
-- four long: the union is `K₅`
#guard (List.range 6).map (sym5Run.cell "off") = [0, 4, 8, 12, 16, 20]

-- and every row names the other four vertices — its in-block first,
-- then its out-block: this is `RamElim.CsrSimple ((D₁).toGraph) 20` seen
#guard (List.range 20).map (sym5Run.cell "tgt")
  = [1, 2, 3, 4,  0, 2, 3, 4,  1, 0, 3, 4,  1, 2, 0, 4,  1, 2, 3, 0]

-- no row names a vertex twice, and no row names its own vertex
#guard ((List.range 5).map (fun v =>
  ((List.range 4).map (fun k => sym5Run.cell "tgt" (4 * v + k))).eraseDups.length)) =
    [4, 4, 4, 4, 4]
#guard ((List.range 5).map (fun v =>
  ((List.range 4).map (fun k => sym5Run.cell "tgt" (4 * v + k))).contains v)) =
    [false, false, false, false, false]

/-- **The new text's final elimination**: symmetrize, revive every
vertex, eliminate. -/
def sym5Final : PRes :=
  exec pB pF (.seq RamDriver.symCom
    (.seq (RamDriver.fillCom "alv" (.lit 1)) RamElim.elimCom)) sym5St

#guard sym5Final.isOk

-- the greedy bound of `K₅` — which is the number
-- `CoverDegree.exists_wreach_degree` reads as `BackDegLE (D R).toGraph π k`
#guard sym5Final.scalar "kmax" = 4

/-- The level's own block structure — the star `K₁,₄` at its eight
slots — which is what `restoreCsr` puts back and what the **old** text's
final elimination therefore ran on. -/
def level5St : PSt :=
  { augSt 5 64 8 star5doff star5dtg with
    arrs := ("off", [0, 4, 5, 6, 7, 8]) :: ("tgt", [1, 2, 3, 4, 0, 0, 0, 0]) ::
      (augSt 5 64 8 star5doff star5dtg).arrs }

/-- **The old text's final elimination**: the same two passes on the
level's own graph. -/
def old5Final : PRes :=
  exec pB pF (.seq (RamDriver.fillCom "alv" (.lit 1)) RamElim.elimCom) level5St

#guard old5Final.isOk

-- the greedy bound of the star
#guard old5Final.scalar "kmax" = 1

-- **the refutation.** The old text's final elimination cannot be
-- producing `BackDegLE (D₁).toGraph π k` with `k` least: the two runs
-- report different bounds on the same instance, and `4` is the one the
-- augmented graph has. So a phase that restores the level's structure
-- before eliminating has no route to the degree data
-- `CoverDegree.exists_wreach_degree` consumes — which is the whole
-- reason `RamDriver.symCom` exists.
#guard old5Final.scalar "kmax" ≠ sym5Final.scalar "kmax"
#guard ¬ (old5Final.scalar "kmax" = 4)

/-! ### The new text's tail, at `R = 0` (rebase F-c-2)

`RamDriver.orderCom` now reads `… fold … ; symCom ; alv := 1 ;
elimRezeroCom ; elimCom ; restoreCsr ; …`. The differential above is
the *reason*; what has to hold beside it is that the swap costs the
`R = 0` phase nothing — and it does not, because at `R = 0` the
orientation symmetrized is one of the level's **own** arena, so the
union it writes is the level's own graph in the level's own array.
That is `RamDriverAugment.two_mul_arcs_le` proved, and this is it run:
the tail on the star's elimination orientation reports the star's own
degeneracy, the same number the old text's tail reported. -/
def sym5ZeroFinal : PRes :=
  exec pB pF
    (.seq RamDriver.symCom
      (.seq (RamDriver.fillCom "alv" (.lit 1))
        (.seq RamDriver.elimRezeroCom RamElim.elimCom)))
    (augSt 5 64 8 star5doff star5dtg)

#guard sym5ZeroFinal.isOk
#guard sym5ZeroFinal.scalar "kmax" = 1
#guard sym5ZeroFinal.scalar "kmax" = old5Final.scalar "kmax"

-- and the graph it eliminated is the star, cell for cell: the `R = 0`
-- fit, seen
#guard (List.range 6).map (sym5ZeroFinal.cell "off") = [0, 4, 5, 6, 7, 8]
#guard (List.range 8).map (sym5ZeroFinal.cell "tgt") = [1, 2, 3, 4, 0, 0, 0, 0]

-- **the R = 1 fold instance.** The same tail one round on is
-- `sym5Final` above: `kmax = 4`, the augmented graph's degeneracy —
-- so the new order really does hand the *augmented* datum on, and the
-- two instances of one tail separate exactly where the fold does.
#guard sym5ZeroFinal.scalar "kmax" ≠ sym5Final.scalar "kmax"

/-! ### The symmetrization's own width

The union of the two blocks is twice the arc count, and at `R > 0` that
is above the level's slot count: the same coupling the round's
fraternity fill has, one pass later. The star's level has `8` slots and
the symmetrized augmented graph needs `20`, so the pass is **stuck** in
the level's own array — the machine half of "`LevelPre`'s `tgt` clause
has to widen before the `R*` phase is statable". -/

def sym5Narrow : PRes := exec pB pF RamDriver.symCom (augSt 5 64 8 aug5doff aug5dtg)

#guard sym5Narrow.isStuck

-- the control: at `R = 0` the graph symmetrized is the level's own, so
-- the same pass in the same `8`-cell array completes. The orientation
-- is the star's own elimination orientation — four arcs, eight slots.
def sym5Zero : PRes := exec pB pF RamDriver.symCom (augSt 5 64 8 star5doff star5dtg)

#guard sym5Zero.isOk
#guard (List.range 6).map (sym5Zero.cell "off") = [0, 4, 5, 6, 7, 8]
#guard (List.range 8).map (sym5Zero.cell "tgt") = [1, 2, 3, 4, 0, 0, 0, 0]

end Lax3Proofs.TgtWidenProbe
