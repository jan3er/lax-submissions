import Lax3Proofs.Refine.BfsBlock

/-!
# The block-driven search, run

House discipline: what the specification says is also *seen*. Four gates,
all of them compiled, and all of them run on the same graph the landed
search's own worked example uses — the path `0—1—2—3` with an isolated
vertex `4` — planted inside a carrier of `nv` vertices, the other
`nv - 5` of which are isolated and alive.

1. **Semantic agreement.** The reached set and the distances the block
   engine hands back in `q`/`qd` are read against the landed
   `RamBfs.Demo`'s distance array, cell for cell, including the masked
   case and the cap boundary.
2. **Carrier-freeness.** The engine's own step count — measured as the
   difference between running the setup with the cleaning and running it
   with the search on top — is *the same number* at `nv = 100` and at
   `nv = 400`. The landed search's is not.
3. **The clock.** That number is strictly below the landed search's at
   the same instance.
4. **Sentinel taint.** A distance cell dirtied outside the ball survives
   byte-identically; one dirtied inside is restored to the sentinel.
-/

namespace Lax3Proofs.Refine.BfsBlock.Diff

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamBfs

/-! ### The instance -/

/-- Fill `a[0 .. hi)` with `v`. The carrier's own cells, which the level
pays for once. -/
def fillTo (a i : String) (hi v : ℕ) : Com :=
  .seq (.assign i (.lit 0))
    (.while (.lt (.var i) (.lit hi))
      (.seq (.store a (.var i) (.lit v))
        (.assign i (.add (.var i) (.lit 1)))))

/-- The path `0—1—2—3` and the isolated vertex `4`, planted in a carrier
of `nv` vertices: every offset starts at `6`, so every vertex from `4` up
has an empty block, and the first six offsets are then overwritten with
the path's. The mask starts all-alive and the bit of vertex `2` is the
parameter, exactly as in the landed example. -/
def setupOnly (nv a2 : ℕ) : Com :=
  .seq (.assign "n" (.lit nv))
    (.seq (.assign "src" (.lit 0))
      (.seq (fillTo "off" "i" (nv + 1) 6)
        (.seq (fillTo "alv" "i" nv 1)
          (.seq Demo.demoOff
            (.seq Demo.demoTgt (.store "alv" (.lit 2) (.lit a2)))))))

/-- The level's one-time cleaning: the sentinel, everywhere. This is the
`O(n)` the block engine pays **once** and the landed search pays once per
centre. -/
def cleanOnly (nv a2 d : ℕ) : Com := .seq (setupOnly nv a2) (initDist d)

/-- Setup, cleaning, and one block-driven search. -/
def blockAll (nv a2 d : ℕ) : Com := .seq (cleanOnly nv a2 d) (bfsBlockCom d)

/-- Setup and one landed search, which cleans for itself. -/
def landedAll (nv a2 d : ℕ) : Com := .seq (setupOnly nv a2) (bfsCom d)

/-! ### Reading the answer out -/

/-- The tail, then the first five queue cells, then their five
distances. Cells the search never wrote read zero, which is what the
machine starts at. -/
def reportBall : Com :=
  .seq (.write (.var "tail"))
    (.seq (.write (.get "q" (.lit 0)))
      (.seq (.write (.get "q" (.lit 1)))
        (.seq (.write (.get "q" (.lit 2)))
          (.seq (.write (.get "q" (.lit 3)))
            (.seq (.write (.get "qd" (.lit 0)))
              (.seq (.write (.get "qd" (.lit 1)))
                (.seq (.write (.get "qd" (.lit 2)))
                  (.write (.get "qd" (.lit 3))))))))))

/-- The five distance cells of the planted graph — after a block search
these must all read the sentinel again. -/
def reportDist : Com :=
  .seq (.write (.get "dist" (.lit 0)))
    (.seq (.write (.get "dist" (.lit 1)))
      (.seq (.write (.get "dist" (.lit 2)))
        (.seq (.write (.get "dist" (.lit 3)))
          (.write (.get "dist" (.lit 4))))))

/-! ### The machine -/

/-- One layout for every program here, so that the step counts are
comparable: the same cells, the same address arithmetic. -/
def layout : Lax13Proofs.Compile.Layout :=
  ⟨["n", "src", "i", "head", "tail", "sc", "v", "w", "dv", "dn", "j", "jend",
    "ri", "u", "du"],
   ["off", "tgt", "alv", "dist", "q", "qd"], 4⟩

/-- Compile and run, reporting the output and the step count. -/
def runIt (c : Com) : Option (List ℕ × ℕ) :=
  runOut 18 4000000 (Lax13Proofs.Compile.compileProgram layout c)
    (Lax13.Ram.initState []) 0

/-- The step count alone. -/
def costOf (c : Com) : ℕ := ((runIt c).map Prod.snd).getD 0

/-! ### Gate 1 — semantic agreement with the landed search

The landed example, for reference:
`Demo.demoRun 1 3 = some ([0, 1, 2, 3, 4], _)` — the path's distances,
the isolated vertex `4` at the sentinel;
`Demo.demoRun 0 3 = some ([0, 1, 4, 4, 4], _)` — vertex `2` dead, the
arena falls apart;
`Demo.demoRun 1 1 = some ([0, 1, 2, 2, 2], _)` — the cap truncates.

The block engine says the same three things in the reached-set reading,
and restores the sentinel in every one of them. -/

/-! Vertex `2` alive, cap `3`: four vertices reached, at distances
`0,1,2,3`; vertex `4` is not reached and is not in the queue. The four
distance cells come back at the sentinel `4`. -/
#guard runIt (.seq (blockAll 5 1 3) (.seq reportBall reportDist))
  = some ([4, 0, 1, 2, 3, 0, 1, 2, 3, 4, 4, 4, 4, 4], 1815)

/-! Vertex `2` dead: only `0` and `1` are reached — the landed run's
`[0, 1, 4, 4, 4]` in the other reading — and the queue cells above the
tail are untouched zeros. -/
#guard runIt (.seq (blockAll 5 0 3) (.seq reportBall reportDist))
  = some ([2, 0, 1, 0, 0, 0, 1, 0, 0, 4, 4, 4, 4, 4], 1285)

/-! **The cap boundary**, the classic defect of this engine family. At
cap `1` the landed search reads `[0, 1, 2, 2, 2]`: vertex `1` sits at
depth exactly `1`, its whole block *is* scanned, and vertex `2` is
rejected because the offer `2` does not beat the sentinel `2`. The block
engine reaches exactly `{0, 1}` and charges vertex `1`'s full block. -/
#guard runIt (.seq (blockAll 5 1 1) (.seq reportBall reportDist))
  = some ([2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 2, 2, 2, 2], 1302)

/-! Cap `0`: the source alone. -/
#guard runIt (.seq (blockAll 5 1 0) (.seq reportBall reportDist))
  = some ([1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1], 1013)

/-! ### Gate 1b — the landed engine, run in this same harness

Gate 1 compares against numbers; this compares against a *run*. The
landed `RamBfs.bfsCom` is compiled here under the same layout, on the
same instance, and its distance array comes out at the values its own
worked example commits — so the two engines are being read side by side
and not against a transcription.

The correspondence is the sentinel's: the landed array reaches `v` iff
`dist v ≤ d`, and its value there is the depth. Read that off each line
below and it is the block engine's `tail`, `q` and `qd` from Gate 1,
term for term.

* `[0,1,2,3,4]` at cap `3`, sentinel `4`: reached `{0,1,2,3}` at depths
  `0,1,2,3` — Gate 1's `tail = 4`, `q = [0,1,2,3]`, `qd = [0,1,2,3]`.
* `[0,1,4,4,4]`, vertex `2` dead: reached `{0,1}` at `0,1` — Gate 1's
  `tail = 2`, `q = [0,1]`, `qd = [0,1]`.
* `[0,1,2,2,2]` at cap `1`, sentinel `2`: reached `{0,1}` at `0,1` —
  the cap boundary, Gate 1's `tail = 2`.
* `[0,1,1,1,1]` at cap `0`: reached `{0}` — Gate 1's `tail = 1`. -/

#guard runIt (.seq (landedAll 5 1 3) reportDist) = some ([0, 1, 2, 3, 4], 1462)
#guard runIt (.seq (landedAll 5 0 3) reportDist) = some ([0, 1, 4, 4, 4], 1048)
#guard runIt (.seq (landedAll 5 1 1) reportDist) = some ([0, 1, 2, 2, 2], 1065)
#guard runIt (.seq (landedAll 5 1 0) reportDist) = some ([0, 1, 1, 1, 1], 834)

/-! ### Gate 2 — the engine's cost does not see the carrier

The search's own step count is the difference between running the
cleaning and running the cleaning with the search on top. That
difference is the same number at a carrier of `100` and a carrier of
`400` — the ball is the same four vertices in both. -/

/-- The block engine's own cost at carrier `nv`. -/
def blockCost (nv a2 d : ℕ) : ℕ := costOf (blockAll nv a2 d) - costOf (cleanOnly nv a2 d)

/-- The landed search's own cost at carrier `nv`. -/
def landedCost (nv a2 d : ℕ) : ℕ := costOf (landedAll nv a2 d) - costOf (setupOnly nv a2)

/-! **Carrier-free.** Four times the carrier, the same cost. -/
#guard blockCost 100 1 3 = blockCost 400 1 3

/-! And the landed search's cost is *not* the same — it carries the fill,
which is the whole difference between the two engines. -/
#guard landedCost 100 1 3 ≠ landedCost 400 1 3

/-! The landed cost grows by very nearly the carrier's own increment. -/
#guard landedCost 400 1 3 - landedCost 100 1 3 = 7500

/-! ### Gate 3 — the clock

At a small ball inside a large carrier the block engine is strictly
cheaper, and by a margin that grows with the carrier: `1076` against
`3333` at a carrier of `100`, and `1076` against `10833` at `400`.

**Two clocks, and they are not the same clock.** The numbers above are
steps of the *compiled machine*, which is what `runOut` counts; the
charge `bfsBlockK` is in units of the *`Com` cost* the `Spec` walk
carries, and compilation multiplies by a constant factor. The gates
below are therefore about the shape of the charge, not about the
measured number — what they and the run agree on is the only thing that
matters here, that neither one moves when `n` does. -/

#guard blockCost 100 1 3 < landedCost 100 1 3
#guard blockCost 400 1 3 < landedCost 400 1 3

/-! The cost function's own shape, evaluated where the carrier is huge
and the ball is not: the ball is `{0,1,2,3}` with slot weight `6`, so
`bfsBlockK 6 4 = 644`, while the landed charge `51 n + 44 ns + 30` at
`n = 400`, `ns = 6` is `20694`. The charge is `n`-free by construction —
these two evaluations differ only in `n`, and the first does not move. -/
#guard bfsBlockK 6 4 = 644
#guard bfsBlockK 6 4 < 51 * 400 + 44 * 6 + 30
#guard bfsBlockK 6 4 < 51 * 100000 + 44 * 6 + 30

/-! ### Gate 4 — sentinel taint

The touched-only claim is a claim about the cells the engine does *not*
write. Dirty one outside the ball and it must come through the run
untouched; dirty one inside and it must come back at the sentinel. -/

/-- Setup, clean, dirty `dist[k]` to `val`, search, report `dist[k]`. -/
def taintRun (nv a2 d k val : ℕ) : Option (List ℕ × ℕ) :=
  runIt (.seq (cleanOnly nv a2 d)
    (.seq (.store "dist" (.lit k) (.lit val))
      (.seq (bfsBlockCom d) (.write (.get "dist" (.lit k))))))

/-! **Outside the ball**: vertex `90` of a `100`-vertex carrier is
isolated and unreached, and the mark planted in its distance cell is
still there, byte-identical, after the search. -/
#guard (taintRun 100 1 3 90 12345).map Prod.fst = some [12345]

/-! **Inside the ball**: vertex `2` is reached, so its cell is written —
and the unwind puts the sentinel `4` back, discarding the mark. -/
#guard (taintRun 100 1 3 2 12345).map Prod.fst = some [4]

/-! **The source's own cell**, which the queue does not name when the
source is dead: with vertex `0` alive it is reached and restored, and the
unwind's final unconditional store is what covers the other case. -/
#guard (taintRun 100 1 3 0 12345).map Prod.fst = some [4]

/-! ### The probe's negative control

`G2CostProbe`'s §5 pairs every admissible coefficient with a refutation
of an undersized one, on data — `blockLeaves_le_weight`'s companion at
`G2CostProbe:555` is the pattern. The block engine's coefficient is
`80`, read off the walk; `30` is refuted on a star, where the ball is
one vertex and its block is a hundred slots. -/

#guard bfsBlockK 100 1 ≤ 80 * (1 + 100 + 1)
#guard ¬ (bfsBlockK 100 1 ≤ 30 * (1 + 100 + 1))

end Lax3Proofs.Refine.BfsBlock.Diff
