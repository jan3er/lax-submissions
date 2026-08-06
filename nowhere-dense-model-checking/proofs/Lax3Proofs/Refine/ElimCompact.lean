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

end Lax3Proofs.Refine.ElimCompact
