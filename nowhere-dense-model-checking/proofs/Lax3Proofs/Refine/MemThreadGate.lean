import Lax3Proofs.Refine.MemThreadProbe
import Lax3Proofs.RamDriverDescend

/-!
# The E-mem thread's gate — the twin, and the probe's shape

The member thread of `plans/nowhere-dense-model-checking/e-mem-design.md`
landed in two spellings, and this file is what keeps them one thing.

* **The twin.** `RamDriver.LevelPre`'s clause 16 reads its member list
  through `RamDriver.MemEnum`, which is
  `Refine.ScatterBlock.MemList n mm Mem (RamDriverCluster.markSet n M)`
  written out at the driver's arrays. It has to be written out:
  `Refine/ScatterBlockProg.lean` is *downstream* of `RamDriver.lean`, so
  the clause cannot name `MemList`. `memList_of_memEnum` and
  `memEnum_of_memList` are the identification, in both directions, so the
  twin cannot drift — the engine family that consumes the clause
  (`ScatterBlock`'s block engines, `CoverBlock`'s copies) states its
  hypotheses in `MemList` and the driver produces `MemEnum`.

* **The probe's shape.** `Refine.MemThreadProbe.LevelPreM` is the design's
  proposed `LevelPre`, compiled before the thread was cut. The gate below
  is that the landed `LevelPre` *is* it, by `And.intro` reshuffling and
  the twin — with the one deviation the design records at §2.1 made
  explicit rather than papered over.

**The deviation, stated once.** The probe's `MemClause` carries the word
bound on the WHOLE physical array (`∀ z < n, Mem z < B`); the landed
clause 16 carries it on the LIVE PREFIX only (`∀ z < mmj`). The junk
tail above the emitted prefix has no provenance — bounding it would
demand exactly the carrier walk the design forbids (the same reason the
clause carries no tail-zero conjunct), and consumers only ever read
`z < mm`. So `levelPreMLive_of_levelPre` is the unconditional gate, and
the probe's own `LevelPreM` follows from it the moment a tail bound is
supplied (`levelPreM_of_levelPre`), which is where the difference is
isolated to one hypothesis.
-/

namespace Lax3Proofs.Refine.MemThreadGate

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriver (memName mnumName alvName MemEnum LevelPre DepthMem memFilterCom)
open Lax3Proofs.RamDriverCluster (markSet)
open Lax3Proofs.Refine.ScatterBlock (MemList MemOf)
open Lax3Proofs.TgtWidenProbe (execC pB pF PSt)

variable {n mm : ℕ} {Mem M : ℕ → ℕ}

/-! ### §1 The twin, both ways -/

/-- **The driver's clause is the engines' contract.** `MemEnum` at the
depth's mask is `MemList` at the set that mask marks. -/
theorem memList_of_memEnum (h : MemEnum n mm Mem M) : MemList n mm Mem (markSet n M) :=
  ⟨h.1, h.2.1, fun k hk => ⟨h.1 k hk, h.2.2.1 k hk⟩,
    fun a ha => h.2.2.2 a ha.1 ha.2⟩

/-- And back, so neither spelling can drift from the other. -/
theorem memEnum_of_memList (h : MemList n mm Mem (markSet n M)) : MemEnum n mm Mem M :=
  ⟨h.lt, h.smono, fun k hk => (h.sound k hk).2,
    fun a ha hMa => h.complete a ⟨ha, hMa⟩⟩

theorem memEnum_iff_memList : MemEnum n mm Mem M ↔ MemList n mm Mem (markSet n M) :=
  ⟨memList_of_memEnum, memEnum_of_memList⟩

/-! ### §2 The T1 gate

The probe's names are its own copies of the driver's (`"mem" ++ j`,
`"mm" ++ j`), so the two agree definitionally; nothing below rewrites a
name. -/

theorem memName_eq (j : ℕ) : MemThreadProbe.memName j = memName j := rfl

theorem mnumName_eq (j : ℕ) : MemThreadProbe.mnumName j = mnumName j := rfl

/-- **The probe's shape at the landed word clause.** `MemThreadProbe.LevelPreM`
with its fourth conjunct read at the live prefix — the shape the thread
actually carries. -/
def LevelPreMLive (B n cap mb ns W : ℕ) (O T : ℕ → ℕ) (j : ℕ) (M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  LevelPre B n cap mb ns W O T j M Gm C σ ∧ MemThreadProbe.DepthMemM n σ ∧
    ∃ (Mem : ℕ → ℕ) (mmj : ℕ), σ.arrs (memName j) = arrOf n Mem ∧
      σ.vars (mnumName j) = mmj ∧ MemList n mmj Mem (markSet n M) ∧
      ∀ z, z < mmj → Mem z < B

/-- **The gate.** The landed `LevelPre` carries the design's proposed
shape: the array allocation is `DepthMem`'s thirteenth entry, the clause
is the sixteenth conjunct, and the contract is the twin. Nothing here is
a proof — it is `And.intro` and one destructuring, which is the point
(the design's blast-radius claim, compiled). -/
theorem levelPreMLive_of_levelPre {B n cap mb ns W j : ℕ} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ : Env} (h : LevelPre B n cap mb ns W O T j M Gm C σ) :
    LevelPreMLive B n cap mb ns W O T j M Gm C σ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hdep, -, -, -, -, Mem, mmj, hA, hV, hE, hB⟩ := id h
  exact ⟨h, fun k => hdep.get (p := (memName k, n)) k (by simp),
    Mem, mmj, hA, hV, memList_of_memEnum hE, hB⟩

/-- **And the probe's own `Prop`, at one extra hypothesis** — the junk
tail's word bound, the one conjunct the landed clause deliberately drops
(§2.1 of the design; `MemThreadProbe.memClause_zero_carrier` is why the
clause may not grow a tail obligation, and the touched-only rule is why
no producer may pay for one). -/
theorem levelPreM_of_levelPre {B n cap mb ns W j : ℕ} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ : Env} (h : LevelPre B n cap mb ns W O T j M Gm C σ)
    (htail : ∀ g : ℕ → ℕ, σ.arrs (memName j) = arrOf n g → ∀ z, z < n → g z < B) :
    MemThreadProbe.LevelPreM B n cap mb ns W O T j M Gm C σ := by
  obtain ⟨hlev, hdepM, Mem, mmj, hA, hV, hL, -⟩ := levelPreMLive_of_levelPre h
  exact ⟨hlev, hdepM, Mem, mmj, hA, hV, hL, htail Mem hA⟩

/-- The design states the gate as an `example`; here it is, at the shape
the thread carries. -/
example {B n cap mb ns W j : ℕ} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {σ : Env}
    (h : LevelPre B n cap mb ns W O T j M Gm C σ) :
    MemThreadProbe.DepthMemM n σ ∧
      ∃ (Mem : ℕ → ℕ) (mmj : ℕ), σ.arrs (memName j) = arrOf n Mem ∧
        σ.vars (mnumName j) = mmj ∧ MemList n mmj Mem (markSet n M) ∧
        ∀ z, z < mmj → Mem z < B :=
  (levelPreMLive_of_levelPre h).2

/-! ### §3 The filter's constant, measured

`RamDriverDescend.memFilter_spec` charges `23·bs + 8`: the two-counter
head's `4 + 4`, and `19 + 4` per block cell — the taken branch's read,
store and two bumps, plus the scan's own test. The probe's compiled
`21·bs + 8` (`MemThreadProbe.filterClock 100 3 = 71`) is the clock of
one particular block, two of whose three members survive; the walk's
constant is the uniform bound, and the two meet on the all-alive block.
Both are measured here on the LANDED `RamDriver.memFilterCom`. -/

/-- The filter context with every block member alive: nothing is
dropped, so every turn takes the store-and-bump branch. -/
def filterStAll (n bq : ℕ) : PSt :=
  { vars := [("bq", bq)]
    arrs := [(memName 1, [7, 13, 91] ++ List.replicate (n - 3) 9),
             (alvName 1, (((List.replicate n 0).set 7 1).set 13 1).set 91 1)] }

def filterAllClock (n bq : ℕ) : ℕ := (execC pB pF (memFilterCom 1) (filterStAll n bq)).2

#guard (execC pB pF (memFilterCom 1) (filterStAll 100 3)).1.isOk

-- the empty block is the head alone, and the all-alive block is `23` a cell
#guard filterAllClock 100 0 = 23 * 0 + 8
#guard filterAllClock 100 2 = 23 * 2 + 8
#guard filterAllClock 100 3 = 23 * 3 + 8

-- **carrier-blind**: the same clock at carriers 100 and 200
#guard filterAllClock 100 3 = filterAllClock 200 3

-- and the answer is the whole block, in the row's order
#guard (List.range 3).map
  ((execC pB pF (memFilterCom 1) (filterStAll 100 3)).1.cell (memName 1)) = [7, 13, 91]
#guard (execC pB pF (memFilterCom 1) (filterStAll 100 3)).1.scalar (mnumName 1) = 3

-- the mixed block the probe measured, on the landed program: `21 * 3 + 8`,
-- inside the walk's uniform `23 * 3 + 8`
#guard (execC pB pF (memFilterCom 1) (MemThreadProbe.filterSt 100 3)).2 = 21 * 3 + 8
#guard (execC pB pF (memFilterCom 1) (MemThreadProbe.filterSt 100 3)).2 ≤ 23 * 3 + 8

/-! ### §4 Axioms -/

end Lax3Proofs.Refine.MemThreadGate
