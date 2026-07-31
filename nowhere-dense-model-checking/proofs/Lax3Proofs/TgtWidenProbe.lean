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

/-- The probe state: scalars, arrays, and the input tape.

**The tape** (rebase F-c-4). The interpreter's `read` used to be stuck,
because `RamAugment.augCom` has no tape rule and a conservative verdict
was all the round's probes needed. The decode does, and the flip's
second gate is a *decode* differential, so the field is here and
`BigStepB.read`'s rule is mirrored with it: a `read` pops the head of
the tape into a scalar, and an empty tape is stuck. `write` still
evaluates and drops — no probe below reads the output. -/
structure PSt where
  vars : List (String × ℕ)
  arrs : List (String × List ℕ)
  inp : List ℕ := []

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
      | some v => .ok ⟨setV σ.vars x v, σ.arrs, σ.inp⟩
      | none => .stuck
  | _ + 1, .store a i e, σ =>
      match evalE B i σ, evalE B e σ with
      | some k, some v =>
          if k < (getA σ.arrs a).length then .ok ⟨σ.vars, setA σ.arrs a k v, σ.inp⟩ else .stuck
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
  | _ + 1, .read x, σ =>
      match σ.inp with
      | v :: rest => if v < B then .ok ⟨setV σ.vars x v, σ.arrs, rest⟩ else .stuck
      | [] => .stuck
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

/-! ### The flip's falsification gate (rebase F-c-4)

`RamDriver.LevelPre`'s `tgt` clause is now `arrOf W T` with a
**zero-padded** tail, and `RamDriver.DecodeMem` is length-`W` with the
tail zeroed. Both halves of that shape are refutable, and this section
is the two refutations run before the walks were touched.

**The first is the shape of the tail clause itself.** The tower's
`BfsQ.Shape` keeps its range clause over the whole physical array, so
the obvious padding clause to carry is `∀ j, ns ≤ j → j < W → T j < n`
— and that clause is *unsatisfiable at `n = 0`*, which
`RamDriver.WordBound` permits and the empty input word reaches. The
three `example`s below are the failure, the repair, and the reason the
repair is enough: zero padding is satisfiable at every `n`, and it
*yields* the range clause wherever the cover pass runs, because a centre
turn carries `c < n` and so `0 < n`.

**The second is the decode.** `DecodeMem` now hands in a `W`-cell `tgt`
with the tail zeroed, and the decode's postcondition hands it back — but
the decode's read loop stores `ns` cells, and nothing in its statement
said the other `W - ns` were left alone. `decodeTail` is that claim run
on the demo tape, with a *sentinel* tail rather than a zeroed one so
that a stray store would show. -/

section FlipGate

/-- **The failure L-8 names.** The range form of the padding clause has
no witness at `n = 0`: it is `∀ j, ns ≤ j → j < W → T j < 0`, and the
padding slots are nonempty as soon as `ns < W`. So `LevelPre` carrying
it would be unsatisfiable on the empty input word, and
`RamDriverIO.decodeImplements` could not establish it. -/
example : ¬ ∃ T : ℕ → ℕ, ∀ j, 8 ≤ j → j < 20 → T j < 0 := by
  rintro ⟨T, h⟩
  exact absurd (h 8 le_rfl (by omega)) (by omega)

/-- **The repair.** Zero padding is satisfiable at every `n`, `ns` and
`W` — the clause is about `T` alone and the constant-zero tail is a
witness — so `LevelPre` stays satisfiable where the range form was not.
-/
example (ns W : ℕ) : ∃ T : ℕ → ℕ, ∀ j, ns ≤ j → j < W → T j = 0 :=
  ⟨fun _ => 0, fun _ _ _ => rfl⟩

/-- **And the repair is enough.** Wherever the cover pass runs it is at a
centre turn, which carries `c < n`; so `n` is positive there, and the
zero tail *is* `RamCover.cover_specW`'s `hpad`. This is the one line the
flip trades the range clause for. -/
example {ns W n c : ℕ} {T : ℕ → ℕ} (hpad0 : ∀ j, ns ≤ j → j < W → T j = 0) (hc : c < n) :
    ∀ j, ns ≤ j → j < W → T j < n :=
  fun j h₁ h₂ => by rw [hpad0 j h₁ h₂]; omega

/-! The demo tape: `K₁,₄` in `Lax11.GraphEncoding`'s format — the vertex
count, the edge count, the `n + 1` offsets, the `2·m` targets. It is the
same block structure `level5St` carries, so the decode's answer can be
read against a landed probe. -/

/-- The encoding of the star on four leaves. -/
def starTape : List ℕ := [5, 4, 0, 4, 5, 6, 7, 8, 1, 2, 3, 4, 0, 0, 0, 0]

/-- A fresh machine for the decode: the four arrays `RamDriver.DecodeMem`
sizes, with `tgt` at the star's own eight slots followed by a chosen
padding tail. -/
def decSt (tail : List ℕ) : PSt where
  vars := []
  arrs :=
    [("off", List.replicate 6 0), ("tgt", List.replicate 8 0 ++ tail),
     (RamDriver.alvName 0, List.replicate 5 0),
     (RamDriver.gamName 0, List.replicate 5 0)]
  inp := starTape

/-- **The decode, into a `tgt` twelve cells wider than the encoding**,
with a sentinel tail: every padding slot holds `7` going in. -/
def decodeTail : PRes := exec pB pF RamDriver.decodeCom (decSt (List.replicate 12 7))

#guard decodeTail.isOk

-- the block structure the encoding names, in the first `ns = 8` slots
#guard (List.range 6).map (decodeTail.cell "off") = [0, 4, 5, 6, 7, 8]
#guard (List.range 8).map (decodeTail.cell "tgt") = [1, 2, 3, 4, 0, 0, 0, 0]

-- **the claim.** The twelve padding slots are untouched: the decode's
-- `ns` stores leave the tail alone, which is what the walk of
-- `RamDriverIO.decodeImplements` now has to show.
#guard (List.range 12).map (fun k => decodeTail.cell "tgt" (8 + k)) = List.replicate 12 7

-- and the same run with the tail *zeroed* hands the zeroed tail back,
-- which is `DecodeMem`'s clause surviving the phase
#guard (exec pB pF RamDriver.decodeCom (decSt (List.replicate 12 0))).isOk
#guard (List.range 20).map ((exec pB pF RamDriver.decodeCom
  (decSt (List.replicate 12 0))).cell "tgt") =
    [1, 2, 3, 4, 0, 0, 0, 0] ++ List.replicate 12 0

-- the two controls. At the exact width the decode is the landed one …
#guard (exec pB pF RamDriver.decodeCom (decSt [])).isOk
#guard (List.range 8).map ((exec pB pF RamDriver.decodeCom (decSt [])).cell "tgt") =
    [1, 2, 3, 4, 0, 0, 0, 0]

-- … and below it the read loop's eighth store has no in-range
-- derivation, so the phase is stuck: the length clause of `DecodeMem` is
-- load-bearing at `W` exactly as it was at `ns`.
def decodeNarrow : PRes :=
  exec pB pF RamDriver.decodeCom
    { decSt [] with arrs := ("tgt", List.replicate 7 0) :: (decSt []).arrs }

#guard decodeNarrow.isStuck

end FlipGate

/-! ### The `R = 1` fold gate (rebase F-c-5)

The whole ordering phase, run end to end on a `K₁,₄` level state at
`R = 0`, `1` and `2` — the honest instance of the `R*` fold, and the
compiled record of the defect its walk found.

**The defect.** `RamAugment.AugPre` asks for `off`, `elm` and `bh`
zeroed at every round's entry, and the landed text had no pass that
re-zeroes them: the phase's *first* elimination leaves `elm[w] = 1` at
every extracted vertex and `bh` holding bucket heads, and `off` holds
the level's own block structure until the first relink. So the fold body
`augCom ; augRelinkCom` had **no run** at `R ≥ 1` — wave D4's defect A,
one pass earlier — and `orderComOld1` below, which is the pre-F-c-5 text
written out, is stuck on this state. The repair is
`RamDriver.augPrepCom` *inside* the fold body (`augRoundCom`), so the
`R = 0` text is byte-identical (`foldRange` of anything at `0` is
`skip`).

**The differential.** At `R = 0` the final elimination reports the
star's bound `kmax = 1`; at `R = 1` it reports `2` — the machine's own
augmented graph is the double star (`D 0` here is the *machine's* first
elimination orientation, which orients one leaf into the centre and the
centre into the other three, so one transitive round attaches that
leaf's three links and no fraternal edge — a smaller instance than the
hand-fed `sym5Final` `K₅`, and the honest one, being the phase's own
chain). At `R = 2` the chain has saturated and the bound stays `2`. In
every case the level's structure comes back restored and the scratch
re-zeroed: a level's exit state is a level's entry state. -/

/-- A `K₁,₄` level state: the star's block structure in `off`/`tgt`
(`tgt` at the allocation width `64` with the zero tail), the reserved
pair, the depth-`0` masks alive, the order array, and the engines'
scratch fresh at width `64`. -/
def ordStAt (W : ℕ) : PSt :=
  { augSt 5 W W [0, 0, 0, 0, 0, 0] [] with
    vars := [("n", 5), ("m", 4), ("lw", W)]
    arrs :=
      ("off", [0, 4, 5, 6, 7, 8]) ::
      ("tgt", [1, 2, 3, 4] ++ List.replicate (W - 4) 0) ::
      ("gof", List.replicate 6 0) :: ("gtg", List.replicate W 0) ::
      (RamDriver.alvName 0, List.replicate 5 1) ::
      (RamDriver.gamName 0, List.replicate 5 1) ::
      (RamDriver.ordName 0, List.replicate 5 0) ::
      (augSt 5 W W [0, 0, 0, 0, 0, 0] []).arrs }

/-- The state at the allocation width `64`. The scalar `"lw"` carries
that width, which is `RamDriver.OrderMem`'s clause read as data. -/
def ordSt : PSt := ordStAt 64

/-- **The pre-F-c-5 ordering phase at `R = 1`**, written out: the fold
body is `augCom ; augRelinkCom` with no prep. -/
def orderComOld1 : Com :=
  .seq RamDriver.saveCsr
    (.seq (RamDriver.copyCom (RamDriver.alvName 0) "alv")
      (.seq RamElim.elimCom
        (.seq (RamDriver.copyUpto "ioff" "doff" (.add (.var "n") (.lit 1)))
          (.seq (RamDriver.copyUpto "itg" "dtg" (.var "lw"))
            (.seq (RamDriver.foldRange (fun _ =>
                .seq RamAugment.augCom RamDriver.augRelinkCom) 1)
              (.seq RamDriver.symCom
                (.seq (RamDriver.fillCom "alv" (.lit 1))
                  (.seq RamDriver.elimRezeroCom
                    (.seq RamElim.elimCom
                      (.seq RamDriver.restoreCsr
                        (.seq (RamDriver.ordCom (RamDriver.ordName 0))
                          RamDriver.orderZeroCom)))))))))))

-- **the defect, compiled**: the old text's round is entered with `elm`,
-- `bh` and `off` dirty, and the phase has no run
#guard (exec pB pF orderComOld1 ordSt).isStuck

-- and the dirt is the first elimination's: at the fold's entry every
-- vertex is flagged eliminated
def ord1Pre : PRes :=
  exec pB pF
    (.seq RamDriver.saveCsr
      (.seq (RamDriver.copyCom (RamDriver.alvName 0) "alv")
        (.seq RamElim.elimCom
          (.seq (RamDriver.copyUpto "ioff" "doff" (.add (.var "n") (.lit 1)))
            (RamDriver.copyUpto "itg" "dtg" (.var "lw")))))) ordSt

#guard ord1Pre.isOk
#guard (List.range 5).map (ord1Pre.cell "elm") = [1, 1, 1, 1, 1]

/-- The repaired phase at `R = 0`. -/
def ord0Run : PRes := exec pB pF (RamDriver.orderCom 0 0) ordSt

/-- At `R = 1`. -/
def ord1Run : PRes := exec pB pF (RamDriver.orderCom 1 0) ordSt

/-- At `R = 2`. -/
def ord2Run : PRes := exec pB pF (RamDriver.orderCom 2 0) ordSt

-- **the repaired phase runs at all three round counts**
#guard ord0Run.isOk
#guard ord1Run.isOk
#guard ord2Run.isOk

-- the differential: the star's bound at `R = 0`, the augmented graph's
-- from `R = 1` on — the fold really hands the chain's datum to the
-- final elimination
#guard ord0Run.scalar "kmax" = 1
#guard ord1Run.scalar "kmax" = 2
#guard ord2Run.scalar "kmax" = 2
#guard ord0Run.scalar "kmax" ≠ ord1Run.scalar "kmax"

-- the exported order arrays: an inversion of the final elimination's
-- ranking in each case
#guard (List.range 5).map (ord0Run.cell (RamDriver.ordName 0)) = [1, 0, 2, 3, 4]
#guard (List.range 5).map (ord1Run.cell (RamDriver.ordName 0)) = [0, 2, 1, 3, 4]

-- a level's exit state is a level's entry state: the block structure
-- restored — zero tail included — and the scratch re-zeroed
#guard (List.range 6).map (ord1Run.cell "off") = [0, 4, 5, 6, 7, 8]
#guard (List.range 8).map (ord1Run.cell "tgt") = [1, 2, 3, 4, 0, 0, 0, 0]
#guard (List.range 12).map (fun k => ord1Run.cell "tgt" (8 + k)) = List.replicate 12 0
#guard (List.range 5).map (ord1Run.cell "elm") = List.replicate 5 0
#guard (List.range 6).map (ord1Run.cell "bh") = List.replicate 6 0

/-! ### The uniformity gate (rebase G2/E1)

`Refine.G2CostProbe`'s `saveCsr_reads_W`/`orderCom_reads_W` compiled the
defect this wave repairs: the phase's four block copies read the
allocation width as a *literal of the program text*, so two widths gave
two programs and `Lax3.ModelChecking`'s one-program-before-all-inputs
quantifier could not be met. The repair is the runtime scalar `"lw"`,
pinned to the width by `RamDriver.OrderMem`, and the tombstones in that
file record the positive form: `RamDriver.orderCom R j` is W-free *by
signature*.

What follows is the executed control the signature argument cannot give
on its own — that the one text, run at two different allocation widths
on states that differ in nothing else, agrees on the live prefix. The
same `orderCom 1 0` runs at `W = 64` (`ord1Run`) and at `W = 96`
(`ord1Wide`); at the second the arrays are half again as long and `"lw"`
says so, and the phase copies half again as many cells. Its answers —
the elimination bound, the exported order, and the restored block
structure — are identical. -/

/-- The same `K₁,₄` level state, allocated at width `96`. -/
def ordStWide : PSt := ordStAt 96

/-- The SAME program text, at the wider allocation. -/
def ord1Wide : PRes := exec pB pF (RamDriver.orderCom 1 0) ordStWide

#guard ord1Wide.isOk

-- the differential: one text, two widths, one answer on the live prefix
#guard ord1Wide.scalar "kmax" = ord1Run.scalar "kmax"
#guard (List.range 5).map (ord1Wide.cell (RamDriver.ordName 0)) =
  (List.range 5).map (ord1Run.cell (RamDriver.ordName 0))
#guard (List.range 6).map (ord1Wide.cell "off") = (List.range 6).map (ord1Run.cell "off")
#guard (List.range 8).map (ord1Wide.cell "tgt") = (List.range 8).map (ord1Run.cell "tgt")

-- and the wider allocation's own tail is restored to zero too, which is
-- the clause `RamDriver.LevelPre` carries and `restoreCsr` now re-copies
-- through the scalar rather than through a literal
#guard (List.range 92).map (fun k => ord1Wide.cell "tgt" (4 + k)) = List.replicate 92 0

-- the scalar is not written by the phase: it comes out as it went in,
-- at both widths (`RamDriverCompose.lw_notMem_orderCom`, executed)
#guard ord1Run.scalar "lw" = 64
#guard ord1Wide.scalar "lw" = 96

/-- **The empty-word check** (refute-before-prove; the instance that
killed F-c-3's range form, `RamDriver.LevelPre`'s `hpad` at `n = 0`).
The clause this wave adds is a scalar equation and carries no range, so
it is satisfiable where the range form was not: at `n = 0`, `ns = 0`,
`W = 0` the whole of `RamDriver.OrderMem`'s new conjunct is
`σ.vars "lw" = 0`, which the empty state meets. -/
example : ((⟨fun _ => 0, fun _ => [], [], []⟩ : Env).vars "lw") = 0 := rfl

end Lax3Proofs.TgtWidenProbe
