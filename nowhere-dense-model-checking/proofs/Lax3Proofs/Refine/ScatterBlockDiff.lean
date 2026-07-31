import Lax3Proofs.Refine.ScatterBlockProg

/-!
# The active-set scatter engine, differentially

The engine's specification says it computes the landed answer at a new
charge. This file *runs* both engines on the same arena and compares the
answers, machine to machine, so that the claim is seen and not only
proved.

The arena is `RamScatter.Demo`'s: the path `0—1—2—3—4`, every vertex
alive, radius one, and the table bit of vertex `2` left open. Its
programs are reused verbatim — `demoOff`, `demoTgt`, `demoAlv` are
imported, not retyped, so the two engines are demonstrably reading the
same graph. What differs is the fourth array: the landed engine gets
`tab`, a bitmask over the carrier, and the active engine gets `mem`, the
same set listed.

With the bit set, `X = {0,1,2,3,4}` and the greedy process at radius one
takes `0`, `2`, `4` — three. With it clear, `X = {0,1,3,4}`, and the
process takes `0` and then `3`, vertex `1` being excluded by `0` and
vertex `3` being two steps away — two. The engines must agree on both,
at every threshold either side of the answer.
-/

namespace Lax3Proofs.Refine.ScatterBlock.Diff

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamScatter Lax3Proofs.RamBfs

/-! ### The arena

Three of the four setup blocks are the landed demo's own. -/

/-- The member list of `X`, listed in increasing order. With the bit of
vertex `2` set the list is `0 1 2 3 4`; with it clear, `0 1 3 4`. -/
def demoMem (b2 : ℕ) : Com :=
  if b2 = 0 then
    .seq (.store "mem" (.lit 0) (.lit 0))
      (.seq (.store "mem" (.lit 1) (.lit 1))
        (.seq (.store "mem" (.lit 2) (.lit 3)) (.store "mem" (.lit 3) (.lit 4))))
  else
    .seq (.store "mem" (.lit 0) (.lit 0))
      (.seq (.store "mem" (.lit 1) (.lit 1))
        (.seq (.store "mem" (.lit 2) (.lit 2))
          (.seq (.store "mem" (.lit 3) (.lit 3)) (.store "mem" (.lit 4) (.lit 4)))))

/-- The member count that goes with it. -/
def demoMm (b2 : ℕ) : ℕ := if b2 = 0 then 4 else 5

/-- **The clean distance array.** `BfsBlock`'s contract is clean-in,
clean-out at the sentinel: the pass is handed a `dist` already holding
`r + 1` everywhere and hands it back the same. The landed engine needs
no such block because it fills the array itself — which is exactly the
`O(n)` per centre the block engine exists to delete, paid here **once**,
before the pass, instead of once per pick. -/
def demoDist (r : ℕ) : Com :=
  .seq (.store "dist" (.lit 0) (.lit (r + 1)))
    (.seq (.store "dist" (.lit 1) (.lit (r + 1)))
      (.seq (.store "dist" (.lit 2) (.lit (r + 1)))
        (.seq (.store "dist" (.lit 3) (.lit (r + 1))) (.store "dist" (.lit 4) (.lit (r + 1))))))

/-- Five vertices, eight slots, the member list, a clean distance array. -/
def demoSetup (b2 r : ℕ) : Com :=
  .seq (.assign "n" (.lit 5))
    (.seq (.assign "mm" (.lit (demoMm b2)))
      (.seq RamScatter.Demo.demoOff
        (.seq RamScatter.Demo.demoTgt (.seq RamScatter.Demo.demoAlv (.seq (demoMem b2) (demoDist r))))))

/-- Build the arena, run the active pass, report the flag. -/
def demoWatched (b2 r t : ℕ) : Com :=
  .seq (demoSetup b2 r) (.seq (scatBlockCom r t) (.write (.var "flag")))

/-- The scalars of the active engine: the landed demo's, plus the block
search's own (`u`, `du`, `ri`), plus the member scan's (`sj`, `mj`,
`mv`, `mw`, `mm`). The arrays gain `qd` and `mem` and lose `tab`. -/
def demoLayout : Lax13Proofs.Compile.Layout :=
  ⟨["n", "src", "i", "head", "tail", "sc", "v", "w", "dv", "dn", "j", "jend",
    "u", "du", "ri", "sj", "mj", "mv", "mw", "cnt", "flag", "mm"],
   ["off", "tgt", "alv", "dist", "q", "qd", "mem", "exc"], 4⟩

/-- The machine program. -/
def demoProg (b2 r t : ℕ) : Lax13.Ram.Program :=
  Lax13Proofs.Compile.compileProgram demoLayout (demoWatched b2 r t)

/-- Run it at a word length that holds every number this arena
produces. -/
def demoRun (b2 r t : ℕ) : Option (List ℕ × ℕ) :=
  runOut 16 40000 (demoProg b2 r t) (Lax13.Ram.initState []) 0

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok (b2 r t : ℕ) :
    Lax13Proofs.Compile.Com.Ok demoLayout (demoWatched b2 r t) := by
  by_cases h : b2 = 0 <;>
    simp [h, demoWatched, demoSetup, demoMem, demoMm, demoDist,
      RamScatter.Demo.demoOff, RamScatter.Demo.demoTgt, RamScatter.Demo.demoAlv, scatBlockCom, clearMem, clearSlot,
      scatBlockLoop, scatBlockStep, scatBlockBody, pickBlock, markBall, markSlot,
      Refine.BfsBlock.bfsBlockCom, Refine.BfsBlock.unwind, Refine.BfsBlock.unwindSlot,
      seedSrc, bfsDrain, expandRow, scanSlot, Fill.put, Csr.loadRow, Csr.scan, Queue.drain,
      demoLayout, Lax13Proofs.Compile.Com.Ok, Lax13Proofs.Compile.Cond.Ok,
      Lax13Proofs.Compile.condExpr, Lax13Proofs.Compile.Expr.Ok]

/-! ### §1 The semantic differential

The landed engine's answers, from `RamScatter.Demo`, are the ground
truth. The active engine must produce the same first component — the
flag — at every setting, and it does: five settings, spanning both
tables, thresholds either side of both answers, and the degenerate
threshold zero. -/

#guard demoRun 1 1 3 = some ([1], 3657)
#guard demoRun 1 1 4 = some ([0], 3656)
#guard demoRun 1 1 0 = some ([1], 799)
#guard demoRun 0 1 2 = some ([1], 2680)
#guard demoRun 0 1 3 = some ([0], 2712)

/-! The landed engine on the same arena, for comparison. These five are
`RamScatter.Demo`'s own compiled gates, restated. -/

#guard RamScatter.Demo.demoRun 1 1 3 = some ([1], 3859)
#guard RamScatter.Demo.demoRun 1 1 4 = some ([0], 3858)
#guard RamScatter.Demo.demoRun 1 1 0 = some ([1], 573)
#guard RamScatter.Demo.demoRun 0 1 2 = some ([1], 2801)
#guard RamScatter.Demo.demoRun 0 1 3 = some ([0], 2849)

/-! **The differential itself**: the flags agree, engine to engine, at
every setting — stated as the comparison rather than left to the reader
of two tables. -/

/-- The flag the run wrote, or `none` if it did not finish. -/
def flagOf (o : Option (List ℕ × ℕ)) : Option (List ℕ) := o.map Prod.fst

#guard flagOf (demoRun 1 1 3) = flagOf (RamScatter.Demo.demoRun 1 1 3)
#guard flagOf (demoRun 1 1 4) = flagOf (RamScatter.Demo.demoRun 1 1 4)
#guard flagOf (demoRun 1 1 0) = flagOf (RamScatter.Demo.demoRun 1 1 0)
#guard flagOf (demoRun 0 1 2) = flagOf (RamScatter.Demo.demoRun 0 1 2)
#guard flagOf (demoRun 0 1 3) = flagOf (RamScatter.Demo.demoRun 0 1 3)

/-! ### §2 The measured clock

`ScatterBlockCost.lean`'s clock gates compare the two *charges*. These
compare the two *machines*, which is the sharper reading: the charge
carries deliberate slack and the step count does not.

The result is worth stating precisely, because it is better than the
charge predicts. `ScatterBlockCost.clock_crossover_at_full_active`
records that at `mm = n` the active **charge** does not beat the landed
one. The active **machine** does, on this arena, by about five per cent
— the accounting is conservative, not the engine.

The exception is the threshold-zero row, and it is instructive. There
the pass makes no picks at all, so there is no ball work to save, and
the active run still pays to pre-fill `dist` with the sentinel. That
fill is the `O(n)` the block engine deletes from the *inside* of the
pass; a caller who runs one pass pays it once either way, and a caller
who runs a pass per centre — which is what a cover level does — pays it
once instead of once per centre. Charging it to the setup here is the
honest placement, and it is why this row goes the other way. -/

/-- The step counts the two machines actually took. -/
def clockOf (o : Option (List ℕ × ℕ)) : Option ℕ := o.map Prod.snd

#guard clockOf (demoRun 1 1 3) = some 3657
#guard clockOf (RamScatter.Demo.demoRun 1 1 3) = some 3859

/-- **The measured clock gate**: strictly fewer machine steps than the
landed engine, at four of the five settings. -/
def beatsLanded (b2 r t : ℕ) : Bool :=
  match clockOf (demoRun b2 r t), clockOf (RamScatter.Demo.demoRun b2 r t) with
  | some a, some b => decide (a < b)
  | _, _ => false

#guard beatsLanded 1 1 3
#guard beatsLanded 1 1 4
#guard beatsLanded 0 1 2
#guard beatsLanded 0 1 3

/-! And the fifth, recorded rather than hidden: at threshold zero the
active run is dearer, because it pays the sentinel fill and does no ball
work to amortise it against. -/

#guard ¬ beatsLanded 1 1 0

end Lax3Proofs.Refine.ScatterBlock.Diff
