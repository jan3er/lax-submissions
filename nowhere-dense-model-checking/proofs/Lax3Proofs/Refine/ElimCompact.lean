import Lax3Proofs.Refine.OrderEngineProbe
import Lax3Proofs.Refine.ArenaSeam
import Lax3Proofs.Refine.MassWeight

/-!
# ND-MC G2/E2-elim — the compacted-arena elimination engine

`Refine/OrderEngineProbe.lean` is this file's warrant. Its coupling
table refuted every IN-PLACE member pass at every slot of the landed
order phase, and its residual list named the repair:

> **In-place member passes cannot be the engine repair.** … A
> member-driven elimination is therefore the **compacted-arena** engine
> of g2-cost-design §3(c): the member list renumbers the arena
> (`mm` vertices, member-row slots), the engine runs at carrier `mm`,
> and the outputs scatter back through the list.

This file is that engine. §1 is the program; §2 the compiled data; §3
the *length seam* — the one real obstruction and its generic repair;
§4 the engine transported to the arena; §5 the contract at the arena's
members; §6 the costs; §7 the bridge to the landed reading.

## The one thing the wave had to discover

`RamElim.elimCom` is already **carrier-parametric**: every one of its
five passes is bounded by the runtime scalar `"n"` (`initDeg`,
`initBuck`, `elimLoop`, `offPass`, `fillPass` all loop on `.var "n"`),
and its landed specification `RamElim.implementsW` quantifies over that
carrier. So "run the engine at carrier `mm`" needs **no
re-synthesis at all**: set `"n" := mm`, hand it the compacted CSR, and
`RamElim.elim_specW` applies verbatim at `n := mm`. The heartbeat
ceilings of `ElimSynth7` are not spent here; the engine is reused as
capital, exactly as the campaign asks.

What *does* stand in the way is a length seam, and it is worth naming
precisely because it is the same seam in every engine family:

> `RamElim.ElimPreW` pins the **physical** length of eleven arrays to
> the carrier scalar (`σ.arrs "alv" = arrOf n M`, `arrOf (n+1)` for the
> offsets, `arrOf (n+W+1)` for the bucket arena, …). At carrier `mm` it
> therefore asks for `mm`-cell arrays — and an IMP+ run cannot
> re-allocate, so what the driver holds is `n`-cell arrays with an
> `mm`-cell live prefix.

§3 closes it *generically*, in the semantics rather than in any engine:
appending a tail to every array of an environment changes no run
(`bigStepB_padArrs`), because the only length-sensitive rule is the
store's in-range side condition and appending only widens it, and no
expression of IMP+ reads a length. So a run on the `mm`-cell **view** of
the store is a run on the store itself, and the landed contract holds of
the view. Two consequences, both load-bearing:

* the landed engine's specification is reusable at any carrier below the
  physical one, with **no restatement of `RamElim`** (which stays
  read-only capital);
* the exit state is literally `⟨engine's compact prefix⟩ ++ ⟨the tail it
  entered with⟩`, per array — i.e. **the engine touches no carrier
  cell**, which is the statement `OrderEngineProbe`'s read-seam (§4) and
  zero-seam (§2) died for the want of. The re-zero between two calls is
  `fillUpto … (.var "mm")`, not a carrier fill.

## What is *not* here, and where it goes

The compaction pass's own walk — that `compactPass` leaves a
`CsrSimple` block structure of the member pullback — is isolated as the
named obligation `CompactBuilds` (§5), in the campaign's
obligation-Props discipline: refuted-before-proved on data (§2), stated
once, and discharged in its own satellite. Nothing here is `sorry`, and
no theorem below assumes it except the composite of §5, which names it
as a hypothesis.

The driver and phase text are untouched: this is a satellite. The
level-CSR save/restore that the composite carries (§1) is nonetheless a
*finding* for the phase text — see §6's note.
-/

namespace Lax3Proofs.Refine.ElimCompact

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver (copyUpto fillUpto)
open Lax3Proofs.TgtWidenProbe (PSt PRes exec execC pB pF augSt)
open Lax3Proofs.Refine.ScatterBlock (MemList MemOf)

/-! ## §1 The program

Six blocks, one `Com`. All six loop on `"mm"` or on the compact slot
counter `"ks"`; the carrier scalar `"n"` occurs in exactly one place —
`installCom`'s `n := mm`, which is what makes the engine's own five
loops arena-bounded — and is restored at the end.

The cell discipline is a fresh `k`-prefix (`"km"` the member index,
`"ku"`/`"kw"` the arena vertices, `"kj"`/`"ke"` the row bounds, `"ks"`
the compact slot counter, `"kn"` the saved carrier), so no landed pass's
scalar is disturbed; the arrays are `"kof"`/`"ktg"` (the compact CSR),
`"kix"` (the inverse numbering), `"ork"` (the arena-numbered ranks) and
`"qof"`/`"qtg"`/`"qav"` (the prefix save). Frame lemmas in §1.4. -/

/-! ### §1.1 Renumbering -/

/-- **The inverse numbering.** Member `k` of the list becomes compact
vertex `k`; this pass writes that map into `"kix"` at the members'
arena positions. `O(mm)` — the array is carrier-length, the walk is
not, and the non-member cells are never written and never read. -/
def cixPass : Com :=
  .seq (.assign "km" (.lit 0))
    (.while (.lt (.var "km") (.var "mm"))
      (.seq (.assign "ku" (.get "mem" (.var "km")))
        (.seq (.store "kix" (.var "ku") (.var "km"))
          (.assign "km" (.add (.var "km") (.lit 1))))))

/-- One member's compact row: the arena row of `mem[km]`, its live
targets renumbered through `"kix"` and appended to `"ktg"`, and the
member's block closed in `"kof"`. The row is read at the *arena*
vertex, so no non-member row is ever walked — this is g2-cost-design
§3(c)'s "the engines read the level graph through the member list". -/
def cRow : Com :=
  .seq (.assign "ku" (.get "mem" (.var "km")))
    (.seq (.assign "kj" (.get "off" (.var "ku")))
      (.seq (.assign "ke" (.get "off" (.add (.var "ku") (.lit 1))))
        (.seq (.while (.lt (.var "kj") (.var "ke"))
                (.seq (.assign "kw" (.get "tgt" (.var "kj")))
                  (.seq (.ite (.lt (.lit 0) (.get "alv" (.var "kw")))
                          (.seq (.store "ktg" (.var "ks") (.get "kix" (.var "kw")))
                            (.assign "ks" (.add (.var "ks") (.lit 1))))
                          .skip)
                    (.assign "kj" (.add (.var "kj") (.lit 1))))))
          (.seq (.assign "km" (.add (.var "km") (.lit 1)))
            (.store "kof" (.var "km") (.var "ks"))))))

/-- **The compacted CSR**, built in one member-driven pass: offsets in
`"kof"` over `mm+1` cells, targets in `"ktg"` over the arena's live
degree sum, which the pass leaves in `"ks"`. -/
def compactCsr : Com :=
  .seq (.store "kof" (.lit 0) (.lit 0))
    (.seq (.assign "ks" (.lit 0))
      (.seq (.assign "km" (.lit 0))
        (.while (.lt (.var "km") (.var "mm")) cRow)))

/-- **The renumbering**, both passes. -/
def compactPass : Com := .seq cixPass compactCsr

/-! ### §1.2 The prefix save, and the install

The compaction writes only *prefixes* of `off`/`tgt`/`alv` — cells
`[0, mm]`, `[0, ks)` and `[0, mm)`. That is the point of the compacted
design and it is what makes the save a **prefix copy of arena-class
length**, where `OrderEngineProbe` §3 refuted a member scatter. -/

/-- Save the three prefixes the install overwrites, and the carrier. -/
def savePre : Com :=
  .seq (.assign "kn" (.var "n"))
    (.seq (copyUpto "off" "qof" (.add (.var "mm") (.lit 1)))
      (.seq (copyUpto "tgt" "qtg" (.var "ks"))
        (copyUpto "alv" "qav" (.var "mm"))))

/-- Put them back, and the carrier with them. -/
def restorePre : Com :=
  .seq (.assign "n" (.var "kn"))
    (.seq (copyUpto "qof" "off" (.add (.var "mm") (.lit 1)))
      (.seq (copyUpto "qtg" "tgt" (.var "ks"))
        (copyUpto "qav" "alv" (.var "mm"))))

/-- **The engine's entry, compacted.** The compact CSR into the
engine's own array names, the all-alive mask over the compact carrier
(compaction made the dead vertices *nonexistent*, so the mask is a
constant — `OrderEngineProbe` §4's read-seam has nothing to read), the
two zeroed-scratch prefixes `RamElim.ElimPre` asks for, and the carrier
scalar moved to `mm`. **Every fill is `mm`-bounded**: this is the
zero-seam (§2 of the probe) dead, since the re-zero between two engine
calls is now arena-class and not carrier-class. -/
def installCom : Com :=
  .seq (copyUpto "kof" "off" (.add (.var "mm") (.lit 1)))
    (.seq (copyUpto "ktg" "tgt" (.var "ks"))
      (.seq (fillUpto "alv" (.var "mm") (.lit 1))
        (.seq (fillUpto "elm" (.var "mm") (.lit 0))
          (.seq (fillUpto "bh" (.add (.var "mm") (.lit 1)) (.lit 0))
            (.assign "n" (.var "mm"))))))

/-! ### §1.3 Scatter-back, and the whole engine -/

/-- **Scatter-back.** The engine ranked the compact vertices; this walk
sends rank `rnk[k]` to the arena vertex `mem[k]`. Member-driven,
`O(mm)`, and it writes nothing at a non-member cell. -/
def scatterCom : Com :=
  .seq (.assign "km" (.lit 0))
    (.while (.lt (.var "km") (.var "mm"))
      (.seq (.assign "ku" (.get "mem" (.var "km")))
        (.seq (.store "ork" (.var "ku") (.get "rnk" (.var "km")))
          (.assign "km" (.add (.var "km") (.lit 1))))))

/-- **The compacted engine, core**: renumber, install, run the landed
engine, scatter back. The level CSR is left compacted — a caller that
needs it back wraps this in the prefix save/restore (`elimCompactCom`).
-/
def elimCompactCore : Com :=
  .seq compactPass (.seq installCom (.seq Lax3Proofs.RamElim.elimCom scatterCom))

/-- **The compacted engine, frame-clean**: the core between the prefix
save and the prefix restore, so that `off`/`tgt`/`alv` and the carrier
scalar come out exactly as they went in. -/
def elimCompactCom : Com :=
  .seq compactPass
    (.seq savePre
      (.seq installCom
        (.seq Lax3Proofs.RamElim.elimCom (.seq scatterCom restorePre))))

/-! ### §1.4 Frames

What the wave owns writes only its own cells and the engine's. Read off
the syntax, one `simp` apiece — the discipline `OrderSigProbeM` runs on
(pre-owned destinations only; no pass writes an array an earlier pass
produced except through the named install). -/

theorem notMem_compactPass_warrs {a : String} (h₁ : a ≠ "kix") (h₂ : a ≠ "kof")
    (h₃ : a ≠ "ktg") : a ∉ compactPass.warrs := by
  simp [compactPass, cixPass, compactCsr, cRow, Com.warrs, h₁, h₂, h₃]

theorem notMem_compactPass_wvars {y : String} (h₁ : y ≠ "km") (h₂ : y ≠ "ku")
    (h₃ : y ≠ "kj") (h₄ : y ≠ "ke") (h₅ : y ≠ "kw") (h₆ : y ≠ "ks") :
    y ∉ compactPass.wvars := by
  simp [compactPass, cixPass, compactCsr, cRow, Com.wvars, h₁, h₂, h₃, h₄, h₅, h₆]

theorem notMem_scatterCom_warrs {a : String} (h : a ≠ "ork") : a ∉ scatterCom.warrs := by
  simp [scatterCom, Com.warrs, h]

theorem notMem_savePre_warrs {a : String} (h₁ : a ≠ "qof") (h₂ : a ≠ "qtg")
    (h₃ : a ≠ "qav") : a ∉ savePre.warrs := by
  simp [savePre, copyUpto, fillUpto, Fill.put, Com.warrs, h₁, h₂, h₃]

theorem notMem_installCom_warrs {a : String} (h₁ : a ≠ "off") (h₂ : a ≠ "tgt")
    (h₃ : a ≠ "alv") (h₄ : a ≠ "elm") (h₅ : a ≠ "bh") : a ∉ installCom.warrs := by
  simp [installCom, copyUpto, fillUpto, Fill.put, Com.warrs, h₁, h₂, h₃, h₄, h₅]

/-! ## §2 The compiled data

The wave's instances, run on the probe interpreter of
`TgtWidenProbe` (`execC pB pF`, the clock-carrying twin of
`Lax13Proofs.BigStepB`). The arena is `RamElim.Demo`'s graph — the
triangle `0—1—2` with the path `2—3—4`, five vertices, degeneracy two —
placed at the **odd** vertices `1, 3, 5, 7, 9` of a carrier of any size,
every other row of the level CSR empty and every other mask cell dead.
So the composite's answer must be `Demo`'s answer, scattered. -/

/-- The store the composite runs in: `augSt`'s twenty-six arrays at
their lengths, plus the wave's own seven, with the level CSR, the mask
and the member list as parameters. -/
def cSt (n W mm : ℕ) (offL tgtL alvL memL : List ℕ) : PSt :=
  { augSt n W W (List.replicate (n + 1) 0) [] with
    vars := [("n", n), ("m", 0), ("lw", W), ("mm", mm)]
    arrs :=
      ("off", offL) :: ("tgt", tgtL) :: ("alv", alvL) :: ("mem", memL) ::
      ("kof", List.replicate (n + 1) 0) :: ("ktg", List.replicate W 0) ::
      ("kix", List.replicate n 0) :: ("ork", List.replicate n 0) ::
      ("qof", List.replicate (n + 1) 0) :: ("qtg", List.replicate W 0) ::
      ("qav", List.replicate n 0) ::
      (augSt n W W (List.replicate (n + 1) 0) []).arrs }

/-- The offsets of the odd-placed `Demo` arena in a carrier of `n`
vertices: rows `1 ↦ {3,5}`, `3 ↦ {1,5}`, `5 ↦ {1,3,7}`, `7 ↦ {5,9}`,
`9 ↦ {7}`, everything else empty. -/
def demoOffL (n : ℕ) : List ℕ :=
  [0, 0, 2, 2, 4, 4, 7, 7, 9, 9] ++ List.replicate (n + 1 - 10) 10

/-- …and its targets. -/
def demoTgtL (W : ℕ) : List ℕ := [3, 5, 1, 5, 1, 3, 7, 5, 9, 7] ++ List.replicate (W - 10) 0

/-- …its mask: the five odd vertices alive. -/
def demoAlvL (n : ℕ) : List ℕ :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ List.replicate (n - 10) 0

/-- …and its member list, at the carrier's physical length with junk
above the live prefix (the `ArenaSeam` convention). -/
def demoMemL (n : ℕ) : List ℕ := [1, 3, 5, 7, 9] ++ List.replicate (n - 5) 999

/-- The `Demo` arena at carrier `n`. -/
def demoSt (n W : ℕ) : PSt := cSt n W 5 (demoOffL n) (demoTgtL W) (demoAlvL n) (demoMemL n)

/-! ### §2.1 The renumbering is the arena's CSR

Refute-before-prove on `CompactBuilds` (§5): the pass's claim is that
`kof`/`ktg` is a block structure of the *member pullback*, at slot count
`ks`. On data, at two carriers. -/

/-- The renumbering alone. -/
def cmpRun (n W : ℕ) : PRes := exec pB pF compactPass (demoSt n W)

#guard (cmpRun 100 64).isOk
#guard (cmpRun 800 64).isOk

-- the inverse numbering, at the members
#guard (List.range 5).map (fun k => (cmpRun 100 64).cell "kix" (2 * k + 1)) = [0, 1, 2, 3, 4]

-- **the compacted CSR is `RamElim.Demo`'s, on the nose**
#guard (List.range 6).map ((cmpRun 100 64).cell "kof") = [0, 2, 4, 7, 9, 10]
#guard (List.range 10).map ((cmpRun 100 64).cell "ktg") = [1, 2, 0, 2, 0, 1, 3, 2, 4, 3]
#guard (cmpRun 100 64).scalar "ks" = 10
-- … and it does not move with the carrier
#guard (List.range 6).map ((cmpRun 800 64).cell "kof") = [0, 2, 4, 7, 9, 10]
#guard (List.range 10).map ((cmpRun 800 64).cell "ktg") = [1, 2, 0, 2, 0, 1, 3, 2, 4, 3]

-- **the honesty direction on the slot count**: the compact slot count is
-- the *live* degree sum, not the arena's raw row length sum — a claim
-- that the pass emits every slot of every member row is refuted, since
-- the odd-placed arena's rows are already live-only here, so the
-- separating instance is the wedge below (§2.4).

/-! ### §2.2 The whole composite reproduces the landed engine's answers

`RamElim.Demo` (that file's worked example) records: ranks `0 1 2 3 4`,
`kmax = 2`, in-lists `∅, {0}, {0,1}, {2}, {3}` — offsets `0 0 1 3 4 5`
and targets `0 0 1 2 3`. The composite must produce exactly those, in
the compact numbering for the in-lists and *scattered* for the ranks. -/

/-- The composite. -/
def compRun (n W : ℕ) : PRes := exec pB pF elimCompactCom (demoSt n W)

#guard (compRun 100 64).isOk
#guard (compRun 800 64).isOk

-- **the ranks, scattered back to the arena's numbering**
#guard (List.range 5).map (fun k => (compRun 100 64).cell "ork" (2 * k + 1)) = [0, 1, 2, 3, 4]
-- **the degeneracy bound**: the triangle's two
#guard (compRun 100 64).scalar "kmax" = 2
-- **the in-lists**, in the compact numbering (the consumer — E2-aug —
-- is compacted too, which is why this is the right output)
#guard (List.range 6).map ((compRun 100 64).cell "ioff") = [0, 0, 1, 3, 4, 5]
#guard (List.range 5).map ((compRun 100 64).cell "itg") = [0, 0, 1, 2, 3]

-- carrier-blind, answer for answer
#guard (List.range 5).map (fun k => (compRun 800 64).cell "ork" (2 * k + 1)) = [0, 1, 2, 3, 4]
#guard (compRun 800 64).scalar "kmax" = 2
#guard (List.range 6).map ((compRun 800 64).cell "ioff") = [0, 0, 1, 3, 4, 5]

/-! ### §2.3 The engine touches no carrier cell

The wave's central operational claim (§3 proves it). The store enters
with a **sentinel tail**: every cell of the eleven engine arrays above
the compact prefix holds `7`, and the composite must hand every one of
them back. A carrier-class pass — the landed `elimCom` at carrier `n`,
or any of the landed phase's `fillCom`s — would erase them. -/

/-- The `Demo` store with a sentinel above the compact prefixes. -/
def demoStTaint (n W : ℕ) : PSt :=
  { demoSt n W with
    arrs :=
      ("deg", List.replicate 5 0 ++ List.replicate (n - 5) 7) ::
      ("elm", List.replicate 5 0 ++ List.replicate (n - 5) 7) ::
      ("rnk", List.replicate 5 0 ++ List.replicate (n - 5) 7) ::
      ("idg", List.replicate 5 0 ++ List.replicate (n - 5) 7) ::
      ("ifl", List.replicate 5 0 ++ List.replicate (n - 5) 7) ::
      ("bh", List.replicate 6 0 ++ List.replicate (n - 5) 7) ::
      ("ioff", List.replicate 6 0 ++ List.replicate (n - 5) 7) ::
      (demoSt n W).arrs }

def taintRun (n W : ℕ) : PRes := exec pB pF elimCompactCom (demoStTaint n W)

#guard (taintRun 100 64).isOk

-- **the sentinel survives, array by array** — the run wrote no cell at
-- or above the compact prefix of any of the seven
#guard (List.range 95).all fun k => (taintRun 100 64).cell "deg" (5 + k) == 7
#guard (List.range 95).all fun k => (taintRun 100 64).cell "elm" (5 + k) == 7
#guard (List.range 95).all fun k => (taintRun 100 64).cell "rnk" (5 + k) == 7
#guard (List.range 95).all fun k => (taintRun 100 64).cell "idg" (5 + k) == 7
#guard (List.range 95).all fun k => (taintRun 100 64).cell "ifl" (5 + k) == 7
#guard (List.range 94).all fun k => (taintRun 100 64).cell "bh" (6 + k) == 7
#guard (List.range 94).all fun k => (taintRun 100 64).cell "ioff" (6 + k) == 7
-- the answers are unchanged by the taint
#guard (List.range 5).map (fun k => (taintRun 100 64).cell "ork" (2 * k + 1)) = [0, 1, 2, 3, 4]
#guard (taintRun 100 64).scalar "kmax" = 2

-- **the negative control**: the landed engine at the carrier, run on
-- the same taint, erases it — this is the class the wave kills
#guard ¬ ((List.range 95).all fun k =>
  (exec pB pF Lax3Proofs.RamElim.elimCom (demoStTaint 100 64)).cell "elm" (5 + k) == 7)

/-! ### §2.4 The frame: the level CSR comes back

`elimCompactCom` overwrites only prefixes, so the prefix save restores
the level's own block structure — the exact repair
`OrderEngineProbe` §3 refuted for a member scatter. Instance: a level
CSR whose **dead** rows differ from anything the compaction writes (the
probe's wedge, at the odd placement), plus a dead target inside a live
row, which is what separates the live degree sum from the raw one. -/

/-- The wedge: vertex `1`'s row also lists the DEAD vertex `2`, so the
live degree sum (`10`) is strictly below the raw row-length sum (`11`),
and the dead rows of `off` carry values no compaction produces. -/
def wedgeSt (n W : ℕ) : PSt :=
  cSt n W 5
    ([0, 0, 3, 3, 5, 5, 8, 8, 10, 10] ++ List.replicate (n + 1 - 10) 11)
    ([3, 5, 2, 1, 5, 1, 3, 7, 5, 9, 7] ++ List.replicate (W - 11) 0)
    (demoAlvL n) (demoMemL n)

def wedgeRun (n W : ℕ) : PRes := exec pB pF elimCompactCom (wedgeSt n W)

#guard (wedgeRun 100 64).isOk
-- the dead target is dropped: the compact CSR is `Demo`'s again …
#guard (wedgeRun 100 64).scalar "ks" = 10
-- … so the *live* degree sum is the slot count, and the raw sum is not
#guard ¬ ((wedgeRun 100 64).scalar "ks" = 11)
-- the answers are `Demo`'s
#guard (List.range 5).map (fun k => (wedgeRun 100 64).cell "ork" (2 * k + 1)) = [0, 1, 2, 3, 4]
#guard (wedgeRun 100 64).scalar "kmax" = 2

-- **the level CSR is restored, dead rows included** — where
-- `OrderEngineProbe` §3 compiled the member restore leaving the arena's
-- offsets at the dead rows, the prefix restore hands back the level's
#guard (List.range 11).map ((wedgeRun 100 64).cell "off") =
  [0, 0, 3, 3, 5, 5, 8, 8, 10, 10, 11]
#guard (List.range 11).map ((wedgeRun 100 64).cell "tgt") =
  [3, 5, 2, 1, 5, 1, 3, 7, 5, 9, 7]
-- … the mask too, and the carrier scalar
#guard (List.range 10).map ((wedgeRun 100 64).cell "alv") = [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
#guard (wedgeRun 100 64).scalar "n" = 100

-- **the honesty direction on the frame**: the CORE (no save/restore)
-- does *not* restore — the save is load-bearing, not decoration
#guard ¬ ((List.range 11).map
  ((exec pB pF elimCompactCore (wedgeSt 100 64)).cell "off") =
  [0, 0, 3, 3, 5, 5, 8, 8, 10, 10, 11])

/-! ## §3 The length seam, closed in the semantics

The obstruction the header names, and its repair. Nothing in this
section is about the elimination: it is a fact about IMP+, and E2-aug
and E2-sym consume it unchanged.

The two observations that make it work:

* **no expression of IMP+ reads a length.** `Expr.evalB`'s only
  array clause is `((σ.arrs a)[k]?).bind (fit B)`, which is `some` only
  when `k` is in range and then depends on the cell alone;
* **the only length-sensitive rule is the store's** `hk : k <
  (σ.arrs a).length`, and appending a tail only widens it.

So appending tails to every array changes no derivation and no clock. -/

/-- **Every array widened by a tail.** -/
def padArrs (σ : Env) (tl : String → List ℕ) : Env :=
  { σ with arrs := fun a => σ.arrs a ++ tl a }

/-- **Every array cut to a schedule** — the *view* an engine at a
smaller carrier runs in. -/
def cutArrs (σ : Env) (len : String → ℕ) : Env :=
  { σ with arrs := fun a => (σ.arrs a).take (len a) }

/-- The tail a schedule leaves behind. -/
def tailOf (σ : Env) (len : String → ℕ) : String → List ℕ :=
  fun a => (σ.arrs a).drop (len a)

/-- The view and its tail are the store. -/
theorem padArrs_cutArrs (σ : Env) (len : String → ℕ) :
    padArrs (cutArrs σ len) (tailOf σ len) = σ := by
  have h : (fun a => (σ.arrs a).take (len a) ++ (σ.arrs a).drop (len a)) = σ.arrs := by
    funext a; exact List.take_append_drop _ _
  simp only [padArrs, cutArrs, tailOf, h]

@[simp] theorem padArrs_vars (σ : Env) (tl : String → List ℕ) :
    (padArrs σ tl).vars = σ.vars := rfl

@[simp] theorem padArrs_inp (σ : Env) (tl : String → List ℕ) :
    (padArrs σ tl).inp = σ.inp := rfl

@[simp] theorem padArrs_arrs (σ : Env) (tl : String → List ℕ) (a : String) :
    (padArrs σ tl).arrs a = σ.arrs a ++ tl a := rfl

/-- **Widening preserves every expression's value.** -/
theorem evalB_padArrs {B : ℕ} {tl : String → List ℕ} :
    ∀ {e : Expr} {σ : Env} {v : ℕ}, e.evalB B σ = some v →
      e.evalB B (padArrs σ tl) = some v := by
  intro e
  induction e with
  | lit m => intro σ v h; exact h
  | var x => intro σ v h; exact h
  | get a i ih =>
      intro σ v h
      rw [Expr.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨k, hk, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨u, hu, hfit⟩ := h
      have hlt : k < (σ.arrs a).length := by
        rcases List.getElem?_eq_some_iff.mp hu with ⟨hlt, -⟩; exact hlt
      have hu' : ((padArrs σ tl).arrs a)[k]? = some u := by
        rw [padArrs_arrs, List.getElem?_append_left hlt]; exact hu
      rw [Expr.evalB, Option.bind_eq_some_iff]
      exact ⟨k, ih hk, by rw [Option.bind_eq_some_iff]; exact ⟨u, hu', hfit⟩⟩
  | bin op e f ihe ihf =>
      intro σ v h
      rw [Expr.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨q, hq, hfit⟩ := h
      rw [Expr.evalB, Option.bind_eq_some_iff]
      exact ⟨m, ihe hm, by rw [Option.bind_eq_some_iff]; exact ⟨q, ihf hq, hfit⟩⟩

/-- …and every condition's. -/
theorem evalC_padArrs {B : ℕ} {tl : String → List ℕ} {b : Cond} {σ : Env} {r : Bool}
    (h : b.evalB B σ = some r) : b.evalB B (padArrs σ tl) = some r := by
  cases b with
  | eq e f =>
      rw [Cond.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      rw [Cond.evalB, Option.bind_eq_some_iff]
      exact ⟨m, evalB_padArrs hm, by rw [Option.map_eq_some_iff]; exact ⟨q, evalB_padArrs hq, rfl⟩⟩
  | lt e f =>
      rw [Cond.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      rw [Cond.evalB, Option.bind_eq_some_iff]
      exact ⟨m, evalB_padArrs hm, by rw [Option.map_eq_some_iff]; exact ⟨q, evalB_padArrs hq, rfl⟩⟩

theorem padArrs_setVar (σ : Env) (tl : String → List ℕ) (x : String) (v : ℕ) :
    padArrs (σ.setVar x v) tl = (padArrs σ tl).setVar x v := rfl

theorem padArrs_setArr {σ : Env} {tl : String → List ℕ} {a : String} {k v : ℕ}
    (hk : k < (σ.arrs a).length) :
    padArrs (σ.setArr a k v) tl = (padArrs σ tl).setArr a k v := by
  have h : (fun b => (if b = a then (σ.arrs a).set k v else σ.arrs b) ++ tl b) =
      fun b => if b = a then (σ.arrs a ++ tl a).set k v else σ.arrs b ++ tl b := by
    funext b
    by_cases hb : b = a
    · subst hb; simp only [if_pos rfl]; exact (List.set_append_left k v hk).symm
    · simp [hb]
  simpa [padArrs, Env.setArr, padArrs_arrs] using congrArg
    (fun f => ({ σ with arrs := f } : Env)) h

/-- **The wave's key lemma: widening every array changes no run.**
Induction on the derivation; the store's side condition is the only
place a length is looked at, and `Nat.lt_of_lt_of_le` against
`List.length_append` closes it. The clock is untouched, rule for
rule — so a cost claim proved at the view is a cost claim at the
store. -/
theorem bigStepB_padArrs {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (tl : String → List ℕ)
    (h : BigStepB B c σ σ' k) : BigStepB B c (padArrs σ tl) (padArrs σ' tl) k := by
  induction h with
  | skip => exact .skip
  | @assign σ x e v he => rw [padArrs_setVar]; exact .assign (evalB_padArrs he)
  | @store σ a i e k v hi he hk =>
      rw [padArrs_setArr hk]
      refine .store (evalB_padArrs hi) (evalB_padArrs he) ?_
      rw [padArrs_arrs, List.length_append]
      exact Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite_true hb _ ih => exact .ite_true (evalC_padArrs hb) ih
  | ite_false hb _ ih => exact .ite_false (evalC_padArrs hb) ih
  | while_true hb _ _ ih₁ ih₂ => exact .while_true (evalC_padArrs hb) ih₁ ih₂
  | while_false hb => exact .while_false (evalC_padArrs hb)
  | @read σ x v rest hi =>
      have : padArrs { σ.setVar x v with inp := rest } tl =
          { (padArrs σ tl).setVar x v with inp := rest } := rfl
      rw [this]; exact .read hi
  | @write σ e v he =>
      have : padArrs { σ with out := σ.out ++ [v] } tl =
          { padArrs σ tl with out := (padArrs σ tl).out ++ [v] } := rfl
      rw [this]; exact .write (evalB_padArrs he)

/-- **The seam, in the form a caller uses it.** A run in the view is a
run in the store, and the store it ends in is the view's answer over the
tail it entered with — *per array*. That second half is the compiled
statement of "the engine touches no carrier cell". -/
theorem run_of_run_cutArrs {B : ℕ} {c : Com} {σ τ : Env} {K : ℕ} (len : String → ℕ)
    (h : Run B c (cutArrs σ len) τ K) : Run B c σ (padArrs τ (tailOf σ len)) K := by
  obtain ⟨k, hk, hbs⟩ := h
  have hpad := bigStepB_padArrs (tailOf σ len) hbs
  rw [padArrs_cutArrs σ len] at hpad
  exact ⟨k, hk, hpad⟩

/-- The cut of a `arrOf` is an `arrOf`, which is how the eleven length
clauses of `RamElim.ElimPreW` are read off a live prefix. -/
theorem take_arrOf {m k : ℕ} {f : ℕ → ℕ} (h : k ≤ m) : (arrOf m f).take k = arrOf k f := by
  rw [arrOf, arrOf, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- `arrOf` reads only the prefix it is asked for. -/
theorem arrOf_congr {k : ℕ} {f g : ℕ → ℕ} (h : ∀ i < k, f i = g i) : arrOf k f = arrOf k g := by
  rw [arrOf, arrOf]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- **Lengths are invariant along a run.** No rule of IMP+ changes the
length of an array — the store's `List.set` does not — which is what
lets the exit state be read as "the view's answer over the entry
tail". -/
theorem bigStepB_length {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) (a : String) : (σ'.arrs a).length = (σ.arrs a).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | @store σ b i e k v _ _ _ =>
      by_cases hb : a = b
      · subst hb; simp [Env.setArr]
      · simp [Env.setArr, hb]
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_length {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨_, _, hbs⟩ := h
  exact bigStepB_length hbs a

@[simp] theorem cutArrs_arrs (σ : Env) (len : String → ℕ) (a : String) :
    (cutArrs σ len).arrs a = (σ.arrs a).take (len a) := rfl

@[simp] theorem cutArrs_vars (σ : Env) (len : String → ℕ) : (cutArrs σ len).vars = σ.vars := rfl

/-- **The tail comes out as it went in**, array by array: a run in the
view writes nothing at or above the schedule. This is the compiled §2.3
claim, as a theorem. -/
theorem tail_preserved {B : ℕ} {c : Com} {σ τ : Env} {K : ℕ} {len : String → ℕ}
    (h : Run B c (cutArrs σ len) τ K) {a : String} (hle : len a ≤ (σ.arrs a).length) :
    ((padArrs τ (tailOf σ len)).arrs a).drop (len a) = (σ.arrs a).drop (len a) := by
  have hlen : (τ.arrs a).length = len a := by
    rw [run_length h a, cutArrs_arrs, List.length_take, Nat.min_eq_left hle]
  rw [padArrs_arrs, tailOf, ← hlen, List.drop_left]

/-! ## §4 The engine at the arena's carrier

The landed engine, its landed specification, and nothing new: the entry
surface is `RamElim.ElimPreW`'s thirteen clauses with the **physical**
lengths at the carrier `n` and the **contract** at the compact carrier
`mm`, and §3 turns the one into the other. -/

/-- **The length schedule of a compacted call.** Which prefix of each of
the engine's arrays is the compact call's own array. Everything the
engine never touches is cut to nothing and restored by the tail. -/
def clen (mm nt W : ℕ) : String → ℕ := fun a =>
  if a = "off" ∨ a = "bh" ∨ a = "ioff" then mm + 1
  else if a = "alv" ∨ a = "deg" ∨ a = "elm" ∨ a = "rnk" ∨ a = "idg" ∨ a = "ifl" then mm
  else if a = "bv" ∨ a = "bn" then mm + W + 1
  else if a = "tgt" then nt
  else if a = "itg" then W
  else 0

@[simp] theorem clen_off (mm nt W : ℕ) : clen mm nt W "off" = mm + 1 := by simp [clen]
@[simp] theorem clen_bh (mm nt W : ℕ) : clen mm nt W "bh" = mm + 1 := by simp [clen]
@[simp] theorem clen_ioff (mm nt W : ℕ) : clen mm nt W "ioff" = mm + 1 := by simp [clen]
@[simp] theorem clen_alv (mm nt W : ℕ) : clen mm nt W "alv" = mm := by simp [clen]
@[simp] theorem clen_deg (mm nt W : ℕ) : clen mm nt W "deg" = mm := by simp [clen]
@[simp] theorem clen_elm (mm nt W : ℕ) : clen mm nt W "elm" = mm := by simp [clen]
@[simp] theorem clen_rnk (mm nt W : ℕ) : clen mm nt W "rnk" = mm := by simp [clen]
@[simp] theorem clen_idg (mm nt W : ℕ) : clen mm nt W "idg" = mm := by simp [clen]
@[simp] theorem clen_ifl (mm nt W : ℕ) : clen mm nt W "ifl" = mm := by simp [clen]
@[simp] theorem clen_bv (mm nt W : ℕ) : clen mm nt W "bv" = mm + W + 1 := by simp [clen]
@[simp] theorem clen_bn (mm nt W : ℕ) : clen mm nt W "bn" = mm + W + 1 := by simp [clen]
@[simp] theorem clen_tgt (mm nt W : ℕ) : clen mm nt W "tgt" = nt := by simp [clen]
@[simp] theorem clen_itg (mm nt W : ℕ) : clen mm nt W "itg" = W := by simp [clen]

/-- **The engine's entry surface at a live prefix.** Clause for clause
`RamElim.ElimPreW`, with every physical length at the carrier `n` and
every *contract* at the compact carrier `mm`. Note what is **not**
here: no clause ranges over the carrier. The zeroed-scratch clauses ask
for `mm` cells of `elm` and `mm + 1` of `bh` — which is why the
re-zero between two calls is `fillUpto … (.var "mm")` and the
`OrderEngineProbe` §2 zero-seam has nothing to catch. -/
def ElimPreC (mm n nt W : ℕ) (O T M : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = mm ∧ mm ≤ n ∧
  (∃ g, σ.arrs "off" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = O i) ∧
  σ.arrs "tgt" = arrOf nt T ∧
  (∃ g, σ.arrs "alv" = arrOf n g ∧ ∀ v < mm, g v = M v) ∧
  (∃ g, σ.arrs "deg" = arrOf n g) ∧
  (∃ g, σ.arrs "elm" = arrOf n g ∧ ∀ v < mm, g v = 0) ∧
  (∃ g, σ.arrs "rnk" = arrOf n g) ∧ (∃ g, σ.arrs "idg" = arrOf n g) ∧
  (∃ g, σ.arrs "bh" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = 0) ∧
  (∃ g, σ.arrs "bv" = arrOf (n + W + 1) g) ∧ (∃ g, σ.arrs "bn" = arrOf (n + W + 1) g) ∧
  (∃ g, σ.arrs "ioff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "ifl" = arrOf n g) ∧
  (∃ g, σ.arrs "itg" = arrOf W g)

/-- **The seam, closed at the elimination.** The live-prefix surface at
the carrier's physical lengths *is* the landed surface at the compact
carrier, read in the view. Every clause is one `take_arrOf` and one
`arrOf_congr`; `RamElim` is not touched. -/
theorem elimPreW_cutArrs {mm n nt W ns : ℕ} {O T M : ℕ → ℕ} {σ : Env}
    (h : ElimPreC mm n nt W O T M σ) :
    RamElim.ElimPreW mm ns nt W O T M (cutArrs σ (clen mm nt W)) := by
  obtain ⟨hn, hmn, ⟨o, ho, hoP⟩, htgt, ⟨m, hm, hmP⟩, ⟨d, hd⟩, ⟨e, he, heP⟩, ⟨r, hr⟩,
    ⟨g, hg⟩, ⟨bh, hbh, hbhP⟩, ⟨bv, hbv⟩, ⟨bn, hbn⟩, ⟨io, hio⟩, ⟨fl, hfl⟩, ⟨it, hit⟩⟩ := h
  refine ⟨hn, ?_, ?_, ?_, ⟨d, ?_⟩, ⟨e, ?_, ?_⟩, ⟨r, ?_⟩, ⟨g, ?_⟩, ⟨bh, ?_, ?_⟩,
    ⟨bv, ?_⟩, ⟨bn, ?_⟩, ⟨io, ?_⟩, ⟨fl, ?_⟩, ⟨it, ?_⟩⟩
  · rw [cutArrs_arrs, clen_off, ho, take_arrOf (by omega)]
    exact arrOf_congr fun i hi => hoP i (by omega)
  · rw [cutArrs_arrs, clen_tgt, htgt, take_arrOf le_rfl]
  · rw [cutArrs_arrs, clen_alv, hm, take_arrOf hmn]
    exact arrOf_congr hmP
  · rw [cutArrs_arrs, clen_deg, hd, take_arrOf hmn]
  · rw [cutArrs_arrs, clen_elm, he, take_arrOf hmn]
  · exact heP
  · rw [cutArrs_arrs, clen_rnk, hr, take_arrOf hmn]
  · rw [cutArrs_arrs, clen_idg, hg, take_arrOf hmn]
  · rw [cutArrs_arrs, clen_bh, hbh, take_arrOf (by omega)]
  · exact hbhP
  · rw [cutArrs_arrs, clen_bv, hbv, take_arrOf (by omega)]
  · rw [cutArrs_arrs, clen_bn, hbn, take_arrOf (by omega)]
  · rw [cutArrs_arrs, clen_ioff, hio, take_arrOf (by omega)]
  · rw [cutArrs_arrs, clen_ifl, hfl, take_arrOf hmn]
  · rw [cutArrs_arrs, clen_itg, hit, take_arrOf le_rfl]

/-- **The compacted engine call.** `RamElim.elimCom`, unchanged, at the
compact carrier `mm`, on a store whose arrays are the carrier's: it
runs, at `RamElim.elimCost mm ns` — a cost in which **the carrier does
not occur** — and leaves `RamElim.ElimPost`, the landed contract,
verbatim, of the compact view. The exit store is the view's answer over
the tail the call entered with.

No re-synthesis and no restatement of `RamElim`: `elim_specW` is
applied at `n := mm`, which is all "the engine runs at carrier `mm`"
ever needed. -/
theorem elimCompact_engine {B mm n ns nt W : ℕ} {H : SimpleGraph (Fin mm)} {O T M : ℕ → ℕ}
    {σ : Env} (hcsr : RamElim.CsrSimple H ns O T) (hB : mm + ns + 1 < B)
    (hMB : ∀ z < mm, M z < B) (hW : ns ≤ W) (hnt : ns ≤ nt)
    (hpre : ElimPreC mm n nt W O T M σ) :
    ∃ τ, Run B RamElim.elimCom σ (padArrs τ (tailOf σ (clen mm nt W)))
          (RamElim.elimCost mm ns) ∧
        RamElim.ElimPost H M ns W (cutArrs σ (clen mm nt W)) τ := by
  obtain ⟨τ, hrun, hpost⟩ :=
    RamElim.elim_specW RamElim.implementsW hcsr hB hMB hW hnt _ (elimPreW_cutArrs hpre)
  exact ⟨τ, run_of_run_cutArrs _ hrun, hpost⟩

/-! ## §5 The contract at the arena's live vertices

`OrderEngineProbe` §5 compiled that the *phase*'s postcondition is
carrier-sized and that no engine repair can change that — the consumer
has to move. This section is the engine's own half of that move: the
elimination's contract, restated so that **nothing in it ranges over the
carrier**. Its subject is the compacted arena, and the compacted arena
is a graph on `Fin mm`: the level's masked graph pulled back along the
member list. -/

open Lax3Proofs.Augmentation (Orientation BackDegLE DegeneracyLE LowDegreeVertices)
open Lax3Proofs.RamElim (InCsr CsrSimple)
open Lax3Proofs.RamDriverCluster (markSet)

/-- **The member embedding**: compact vertex `k` is the arena vertex
`mem[k]`. -/
def memEmb {n mm : ℕ} {Mem : ℕ → ℕ} {X : Set (Fin n)} (hml : MemList n mm Mem X)
    (i : Fin mm) : Fin n := ⟨Mem (i : ℕ), hml.lt i i.isLt⟩

theorem memEmb_injective {n mm : ℕ} {Mem : ℕ → ℕ} {X : Set (Fin n)}
    (hml : MemList n mm Mem X) : Function.Injective (memEmb hml) := by
  intro i j hij
  have h : Mem (i : ℕ) = Mem (j : ℕ) := congrArg Fin.val hij
  by_contra hne
  rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with hlt | hge
  · exact absurd h (Nat.ne_of_lt (hml.smono _ _ hlt j.isLt))
  · have hlt : (j : ℕ) < (i : ℕ) :=
      Nat.lt_of_le_of_ne hge fun he => hne (Fin.ext he.symm)
    exact absurd h.symm (Nat.ne_of_lt (hml.smono _ _ hlt i.isLt))

/-- **The compacted arena**: the level's arena, renumbered by the member
list. Adjacency is the arena's, read at the members' arena numbers —
which is exactly what `cRow` walks. -/
def memGraph {n mm : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) {Mem : ℕ → ℕ}
    {X : Set (Fin n)} (hml : MemList n mm Mem X) : SimpleGraph (Fin mm) :=
  SimpleGraph.comap (memEmb hml) (masked G M)

theorem memGraph_adj {n mm : ℕ} {G : SimpleGraph (Fin n)} {M Mem : ℕ → ℕ}
    {X : Set (Fin n)} {hml : MemList n mm Mem X} {i j : Fin mm} :
    (memGraph G M hml).Adj i j ↔ (masked G M).Adj (memEmb hml i) (memEmb hml j) := Iff.rfl

/-- **Compaction makes the mask a constant.** The dead vertices are not
renumbered, so the compacted arena has no dead vertex and its mask is
all ones — `RamElim`'s `masked` of it is itself. This is why
`OrderEngineProbe` §4's read-seam has nothing to read: the engine's
mask pass reads `alv` at every vertex of *its* carrier, and every one of
them is alive by construction. -/
theorem masked_of_all_alive {mm : ℕ} (H : SimpleGraph (Fin mm)) {M' : ℕ → ℕ}
    (h : ∀ v < mm, M' v ≠ 0) : masked H M' = H := by
  ext u v
  rw [Lax3Proofs.RamBfs.masked_adj]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', h _ u.isLt, h _ v.isLt⟩⟩

/-- **The elimination's contract, at the arena's live vertices.**

Clause for clause `RamElim.ElimPost`, with three deliberate moves:

* the graph is `memGraph` — the arena renumbered — so every
  quantifier ranges over `Fin mm` and **no clause mentions the
  carrier**;
* the ranks are read at the members' *arena* cells, `ork[mem j]`, which
  is what `scatterCom` writes: a member reading, not a carrier array;
* the in-lists stay in the **compact** numbering (`ioff` over `mm + 1`
  cells, `itg`), because their consumer — the augmentation engine, wave
  E2-aug — is compacted too. Re-numbering them back would be a second
  scatter nobody reads.

Nothing here is a `∀ v < n`. That is the whole point: the hazard the
wave was warned about is that the carrier walks back in through the
statement. -/
def ElimMemPost {n mm : ℕ} (G : SimpleGraph (Fin n)) (M Mem : ℕ → ℕ)
    {X : Set (Fin n)} (hml : MemList n mm Mem X) (ns W : ℕ) (σ' : Env) : Prop :=
  ∃ (R IO IT : ℕ → ℕ) (k m : ℕ) (E : Orientation mm),
    (∀ j, j < mm → (σ'.arrs "ork").getD (Mem j) 0 = R j) ∧
    σ'.vars "kmax" = k ∧
    (∀ i, i ≤ mm → (σ'.arrs "ioff").getD i 0 = IO i) ∧
    σ'.arrs "itg" = arrOf W IT ∧ m ≤ ns ∧
    Function.Injective (fun i : Fin mm => R (i : ℕ)) ∧
    E.Orients (memGraph G M hml) ∧ E.InDegLE k ∧
    (∀ u w : Fin mm, u ∈ E.inN w ↔ (memGraph G M hml).Adj u w ∧ R (u : ℕ) < R (w : ℕ)) ∧
    E.toGraph = memGraph G M hml ∧
    BackDegLE (memGraph G M hml) (fun i : Fin mm => R (i : ℕ)) k ∧
    BackDegLE E.toGraph (fun i : Fin mm => R (i : ℕ)) k ∧
    DegeneracyLE (memGraph G M hml) k ∧
    (∀ k', LowDegreeVertices (memGraph G M hml) k' → k ≤ k') ∧
    InCsr E m IO IT

/-! ## §6 The cost: arena-affine, carrier-blind

The composite's clock, and the two things that make it the wave's
deliverable: the carrier does not occur in it, and the arena's own two
numbers do. -/

/-- **The composite's cost**: the landed engine's own `elimCost` at the
compact carrier, plus the six member-driven passes (renumber, prefix
save, install, scatter, prefix restore) at a generous constant. `mm` is
the arena's live vertex count and `cs` its live slot count — **the
carrier `n` does not appear**, which is the whole claim of the wave. -/
def elimCompactCost (mm cs : ℕ) : ℕ := Lax3Proofs.RamElim.elimCost mm cs + 200 * mm + 200 * cs + 200

/-- The cost, expanded: `800·mm + 800·cs + 300`. Affine in the arena's
two numbers, and in nothing else. -/
theorem elimCompactCost_eq (mm cs : ℕ) : elimCompactCost mm cs = 800 * mm + 800 * cs + 300 := by
  simp only [elimCompactCost, Lax3Proofs.RamElim.elimCost]; ring

#guard elimCompactCost 5 10 = 800 * 5 + 800 * 10 + 300
#guard elimCompactCost 5 10 = 12300
-- two-sided: the constant `800` is not slack for `801`, and the run
-- below (`3407`) is inside `12300` while `mm`-only budgets are not
#guard ¬ (elimCompactCost 5 10 = 801 * 5 + 801 * 10 + 300)

/-- **The single weight**: the composite's cost is affine in the arena's
weight and in nothing else. -/
theorem elimCompactCost_le_weight {mm cs w : ℕ} (h : mm + cs ≤ w) :
    elimCompactCost mm cs ≤ 800 * w + 300 := by
  rw [elimCompactCost_eq]
  have : 800 * mm + 800 * cs = 800 * (mm + cs) := by ring
  omega

/-- **…and the weight is the compacted arena's own.** `MassWeight`'s
root reading at the compact graph: a `CsrSimple` of a graph all of whose
vertices are alive has weight `mm + cs`, the vertex count plus the slot
count. So the composite's clock is `800 · arenaWeight + 300` at the
arena the engine actually ran on, with the carrier nowhere in sight. -/
theorem elimCompactCost_le_arenaWeight {mm cs : ℕ} {H : SimpleGraph (Fin mm)} {O' T' : ℕ → ℕ}
    (hcsr : CsrSimple H cs O' T') {M' : ℕ → ℕ} (halive : ∀ v < mm, M' v ≠ 0) :
    elimCompactCost mm cs ≤ 800 * MassWeight.arenaWeight mm H M' + 300 :=
  elimCompactCost_le_weight (le_of_eq (MassWeight.arenaWeight_root hcsr halive).symm)

/-! ### §6.1 The clocks, compiled

The control pattern of `OrderSigProbeM`/`killTurnCom`: the SAME arena
inside two carriers differing by a factor of eight, and one clock. -/

/-- The composite's clock on the `Demo` arena at carrier `n`. -/
def compClock (n W : ℕ) : ℕ := (execC pB pF elimCompactCom (demoSt n W)).2

-- **carrier-blindness**: one arena, four carriers, one clock
#guard compClock 100 64 = 3407
#guard compClock 200 64 = 3407
#guard compClock 400 64 = 3407
#guard compClock 800 64 = 3407
-- and it fits the cost function at the arena's own two numbers
#guard compClock 800 64 ≤ elimCompactCost 5 10

-- **the honesty direction, on the clock**: the pin is exact — one tick
-- less does not hold
#guard ¬ (compClock 800 64 ≤ 3406)

-- **the honesty direction, on the shape**: a slot-blind budget is
-- refuted. The same five members, now pairwise adjacent (`K₅`, twenty
-- slots instead of ten), clock strictly higher — so no `c·mm + c'`
-- bound is uniform, and the `cs` term of `elimCompactCost` is
-- load-bearing.
def k5St (n W : ℕ) : PSt :=
  cSt n W 5
    ([0, 0, 4, 4, 8, 8, 12, 12, 16, 16] ++ List.replicate (n + 1 - 10) 20)
    ([3, 5, 7, 9, 1, 5, 7, 9, 1, 3, 7, 9, 1, 3, 5, 9, 1, 3, 5, 7] ++
      List.replicate (W - 20) 0)
    (demoAlvL n) (demoMemL n)

def k5Clock (n W : ℕ) : ℕ := (execC pB pF elimCompactCom (k5St n W)).2

#guard (exec pB pF elimCompactCom (k5St 100 64)).isOk
-- the denser arena's slot count is twice the sparse one's …
#guard (exec pB pF compactPass (k5St 100 64)).scalar "ks" = 20
-- … its clock is strictly higher …
#guard compClock 100 64 < k5Clock 100 64
-- … so the sparse arena's clock is NOT a bound for it: a budget read at
-- `mm` alone is refuted on data
#guard ¬ (k5Clock 100 64 ≤ compClock 100 64)
-- … and it too is carrier-blind, and inside the cost at its own numbers
#guard k5Clock 100 64 = k5Clock 800 64
#guard k5Clock 800 64 ≤ elimCompactCost 5 20
-- `K₅` has degeneracy four
#guard (exec pB pF elimCompactCom (k5St 100 64)).scalar "kmax" = 4

/-! ### §6.2 The floor of `OrderEngineProbe` §1, cleared

The probe's §1 compiled the landed engine's own share of the order
phase's clock at a fixed two-member arena: `elimShare n = 159·n + 276`,
affine in the **carrier**, and at carrier `800` it exceeds
`orderCostA (bsq 2 2 0) 0 4 = 103950` — the §2.1 budget read at the
arena's weight. That is the floor the whole G2 interface stood behind.

The same two-member arena, at the same carrier `800`, through this
engine. -/

/-- The probe's two-member arena — one edge `0—1`, everything else dead
— with the member list, in a carrier of `n`. -/
def twoSt (n W : ℕ) : PSt :=
  cSt n W 2 ([0, 1, 2] ++ List.replicate (n + 1 - 3) 2)
    ([1, 0] ++ List.replicate (W - 2) 0)
    ([1, 1] ++ List.replicate (n - 2) 0) ([0, 1] ++ List.replicate (n - 2) 999)

def twoClock (n W : ℕ) : ℕ := (execC pB pF elimCompactCom (twoSt n W)).2

#guard (exec pB pF elimCompactCom (twoSt 800 8)).isOk
-- the answers: two vertices, one edge, degeneracy one
#guard (exec pB pF elimCompactCom (twoSt 800 8)).scalar "kmax" = 1
#guard [(exec pB pF elimCompactCom (twoSt 800 8)).cell "ork" 0,
        (exec pB pF elimCompactCom (twoSt 800 8)).cell "ork" 1] = [0, 1]

-- **carrier-blind at the probe's own instance**
#guard twoClock 100 8 = 1184
#guard twoClock 800 8 = 1184

-- **the floor is cleared.** The landed engine's share at carrier `800`
-- overshoots the §2.1 budget; this engine's whole clock — compaction,
-- save, install, engine, scatter, restore — fits inside it, at the same
-- arena and the same carrier.
#guard ¬ (OrderEngineProbe.elimShare 800 8 ≤
  G2CostProbe.orderCostA (G2CostProbe.bsq 2 2 0) 0 4)
#guard twoClock 800 8 ≤ G2CostProbe.orderCostA (G2CostProbe.bsq 2 2 0) 0 4
-- by two orders of magnitude, and the gap grows with the carrier while
-- this clock does not
#guard OrderEngineProbe.elimShare 800 8 = 127476
#guard twoClock 800 8 * 100 ≤ OrderEngineProbe.elimShare 800 8
-- the honesty direction on the comparison: the landed share does NOT
-- fit where this one does
#guard ¬ (OrderEngineProbe.elimShare 800 8 ≤ twoClock 800 8 * 100)

/-! ## §7 The bridge to the landed reading

The wave's contract is a restatement, so it owes the statement that it
*is* one: on the all-alive arena at the identity numbering — `mm = n`,
`mem` the identity, every vertex live — `ElimMemPost` is
`RamElim.ElimPost`, clause for clause. This is the compiled
non-weakening check the campaign asks of every restated theorem. -/

/-- The identity member list of an all-alive arena: every vertex is a
member, in order. -/
def idMemList {n : ℕ} {M : ℕ → ℕ} (h : ∀ v < n, M v ≠ 0) :
    MemList n n id (markSet n M) where
  lt := fun _ hj => hj
  smono := fun _ _ hij _ => hij
  sound := fun j hj => ⟨hj, h j hj⟩
  complete := fun a ha => ⟨a, ha.lt, rfl⟩

/-- At the identity numbering the compacted arena is the arena. -/
theorem memGraph_id {n : ℕ} (G : SimpleGraph (Fin n)) {M : ℕ → ℕ}
    (h : ∀ v < n, M v ≠ 0) : memGraph G M (idMemList h) = masked G M := by
  ext u v
  rw [memGraph_adj]
  exact Iff.of_eq (by rw [show memEmb (idMemList h) u = u from Fin.ext rfl,
    show memEmb (idMemList h) v = v from Fin.ext rfl])

/-- **The bridge.** On the all-alive arena at the identity numbering,
the wave's member contract holds of exactly the states the landed
contract holds of — with `"ork"` reading `"rnk"`, which is what
`scatterCom` degenerates to when `mem` is the identity. So the
restatement of §5 weakens nothing: it is the landed `ElimPost` with the
carrier replaced by the member list, and at `mm = n` the two coincide.
-/
theorem elimMemPost_of_elimPost {n ns W : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    (halive : ∀ v < n, M v ≠ 0) {σ σ' : Env}
    (hpost : Lax3Proofs.RamElim.ElimPost G M ns W σ σ')
    (hork : σ'.arrs "ork" = σ'.arrs "rnk") :
    ElimMemPost G M id (idMemList halive) ns W σ' := by
  obtain ⟨R, IO, IT, k, m, E, hrnk, hk, hioff, hitg, hm, hinj, horients, hindeg, hinN,
    htoG, hbd, hbdE, hdeg, hlow, hcsr⟩ := hpost
  rw [← memGraph_id G halive] at horients hinN htoG hbd hdeg hlow
  refine ⟨R, IO, IT, k, m, E, ?_, hk, ?_, hitg, hm, hinj, horients, hindeg, hinN, htoG,
    hbd, hbdE, hdeg, hlow, hcsr⟩
  · intro j hj
    rw [hork, hrnk]
    simp only [id_eq]
    exact getD_arrOf R hj
  · intro i hi
    rw [hioff, getD_arrOf _ (by omega)]

/-- The converse reading, so the bridge is an equivalence and not a
weakening in disguise: at the identity numbering the member clauses give
the landed ones back for the three answers the phase consumes (the rank
array's contract is `"ork"`'s, the bound is `kmax`, the in-lists are
`ioff`/`itg`). -/
theorem elimPost_answers_of_elimMemPost {n ns W : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    (halive : ∀ v < n, M v ≠ 0) {σ' : Env}
    (h : ElimMemPost G M id (idMemList halive) ns W σ') :
    ∃ (R : ℕ → ℕ) (k : ℕ), σ'.vars "kmax" = k ∧
      (∀ v, v < n → (σ'.arrs "ork").getD v 0 = R v) ∧
      DegeneracyLE (masked G M) k ∧
      BackDegLE (masked G M) (fun v : Fin n => R (v : ℕ)) k := by
  obtain ⟨R, IO, IT, k, m, E, hork, hk, -, -, -, -, -, -, -, -, hbd, -, hdeg, -, -⟩ := h
  rw [memGraph_id G halive] at hbd hdeg
  exact ⟨R, k, hk, fun v hv => hork v hv, hdeg, hbd⟩

end Lax3Proofs.Refine.ElimCompact
