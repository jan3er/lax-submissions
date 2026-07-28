import Lax11Proofs.CC

/-!
The driver: the Fibonacci-base bounded search tree for vertex cover, as
an IMP+ program.

The algorithm is the plan's (VF3, rev 2). After the read phase — the CSR
block into `off` and `tgt` exactly as in the components driver, then one
more `read` for the budget — the machine runs one outer loop over a mode
scalar: descend (`0`) scans the whole target array once and either
answers, gives up on the branch, or pushes a frame and marks a
branching vertex; backtrack (`1`) either answers, flips the top frame to
its second branch — marking the *whole residual neighbourhood* of its
vertex — or pops it; done (`2`) exits.

What separates this from the `2^k` driver of Lax11 is the second branch.
There, both children of a frame cost one unit of budget, and the tree has
`2^k` leaves. Here the first child marks the branching vertex `v` (one
unit) and the second marks all `d ≥ 2` of its residual neighbours (`d`
units), so the two children cost `1` and `d ≥ 2`: the leaf count obeys
`T(b) ≤ T(b-1) + T(b-2)` and is a Fibonacci number. Two consequences
shape the program. The budget can no longer be a scalar the frames share
— a frame must remember the budget it was pushed at, so the stack gains
`stkB`. And a frame no longer marks one vertex but a whole set, so the
marks it made cannot be undone by name: they are recorded on a `trail`,
each frame storing the trail height it found (`stkT`), and undone by
truncating the trail back to it.

### The scan

One descend pass walks the target array once, `j` from `0` to `2m`, with
the block owner `u` walking alongside: an inner loop advances `u` past
every block that ends at or before `j`. Its cost is amortized — over the
whole pass the owner advances at most `n` times — which is why it is an
inner loop and not, as in the `2^k` driver, another branch of the same
loop.

The pass computes two things at once. `ro` counts the *owners*, not the
slots, that name a larger unmarked vertex: the register `cnted` keeps a
block from being counted twice, which matters because the concept's
encoding may list a neighbour repeatedly, and an uncapped slot count
would exceed the number of residual edges and break the matching leaf.
And `found` says whether some unmarked vertex has two residual
neighbours: the registers `seen` and `t1` remember the first unmarked
target of the current block, and the flag is raised on an unmarked target
*different* from it — again because repeats make a second unmarked slot
no evidence of a second neighbour. `v` records the first such owner. The
three registers are per-owner and are reset whenever the owner advances.

### The names

Scalars, in the order of the layout:

* `n`, `m` — the vertex and edge counts, off the tape.
* `m2` — `2 * m`, the length of the target array (computed as `m + m`;
  there is no multiplication anywhere in this program).
* `len` — `n + 1`, the length of the offset array.
* `i`, `t` — the read loop's counter and cell (Lax11's `readLoop`).
* `j` — the slot pointer, of the descend scan and of the flip's row scan.
* `u` — the block owner of the descend scan.
* `w` — the target of slot `j`, in both scans.
* `jend` — the end of the flip's row scan, `off[pv + 1]`.
* `seen`, `t1`, `cnted` — the per-owner registers of the descend scan:
  whether an unmarked target has been seen in this block, which one, and
  whether this block has been counted into `ro`. Reset on owner advance.
* `ro` — the residual owner count of the descend scan.
* `found`, `v` — the branching flag and the branching vertex.
* `top` — the number of frames on the stack.
* `tt` — the trail height.
* `bud` — the remaining budget.
* `mode` — `0` descend, `1` backtrack, `2` done.
* `ans` — the answer, written at the end.
* `sp` — `top - 1`, the index of the top frame.
* `pv`, `pb`, `tb` — the top frame's vertex, stored budget and trail
  base, read out of `stkV`, `stkB`, `stkT`.
* `d` — `tt - tb`, the size of the residual neighbourhood a flip marked.

Arrays, in the order of the layout, with the extents the proofs give
them:

* `off` (extent `n + 1`), `tgt` (extent `2m`) — the encoding.
* `mark` (extent `n`) — the indicator of the marked set. Fresh arrays
  are zeroed and the marker for "unmarked" is `0`, so it needs no
  initialization.
* `trail` (extent `n + 1`) — the marked vertices in the order they were
  marked. Frame health makes the marked sets disjoint and nonempty, so
  `tt ≤ n` and `top ≤ n`, and every write below is in bounds.
* `stkV`, `stkB`, `stkT`, `stkP` (extent `n + 1`) — the frames: the
  vertex branched on, the budget at the push, the trail height at the
  push, and the phase (`0` first branch, `1` second).

### The statement layout

The commands below are the ground truth for the Run proofs; this is the
shape they see.

    vcfCom = read n; read m; len := n+1; readLoop off len;
             m2 := m+m; readLoop tgt m2; read bud;
             while mode < 2 do outerBody;
             write ans

    outerBody     = if mode = 0 then descendBody else backtrackBody
    descendBody   = descendScan;
                    if found = 0
                      then if ro < bud+1 then (ans := 1; mode := 2)
                                         else mode := 1
                      else if bud = 0 then mode := 1 else pushFrame
    descendScan   = j := 0; u := 0; ro := 0; found := 0;
                    seen := 0; t1 := 0; cnted := 0;
                    while j < m2 do (ownerAdvance; slotStep)
    ownerAdvance  = while off[u+1] < j+1 do
                      (u := u+1; seen := 0; t1 := 0; cnted := 0)
    slotStep      = (if mark[u] = 0 then … else skip); j := j+1
    backtrackBody = if top = 0 then (ans := 0; mode := 2)
                    else sp := top-1; pv := stkV[sp]; pb := stkB[sp];
                         tb := stkT[sp];
                         if stkP[sp] = 0 then flipFrame else popFrame
    flipFrame     = mark[pv] := 0; tt := tb; bud := pb;
                    j := off[pv]; jend := off[pv+1];
                    while j < jend do rowStep;
                    stkP[sp] := 1; d := tt - tb;
                    if d < bud+1 then (bud := bud - d; mode := 0)
                                 else skip
    popFrame      = while tb < tt do (tt := tt-1; mark[trail[tt]] := 0);
                    bud := pb; top := top-1

Two encodings deserve a word. A condition is a single comparison, so
`x ≤ y` is written `x < y + 1` and `w ≠ t1` is two strict comparisons in
nested `ite`s. Unlike the `2^k` driver, no loop here exits early, so the
"assign the counter its bound" idiom for `break` does not appear: the
descend scan has to run to completion, since `ro` is only correct after
the last slot.

One deviation from the plan's prose, both readings of which are equal
under frame health: the flip unmarks `mark[pv]` rather than
`mark[trail[tb]]`. A phase-`0` frame marked exactly `[v]`, so `trail[tb]`
is `pv`, and reading the vertex out of the frame saves the proofs an
appeal to that fact.
-/

namespace Lax15Proofs.VC

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC

/-! ### The program -/

/-- Advance the block owner past every block ending at or before the
slot pointer, resetting the per-owner registers each time. The condition
is `off[u+1] ≤ j`, written as a single comparison. -/
def ownerAdvance : Com :=
  .while (.lt (.get "off" (.add (.var "u") (.lit 1))) (.add (.var "j") (.lit 1)))
    (.seq (.assign "u" (.add (.var "u") (.lit 1)))
      (.seq (.assign "seen" (.lit 0))
        (.seq (.assign "t1" (.lit 0))
          (.assign "cnted" (.lit 0)))))

/-- Raise the branching flag on the current owner, keeping the first
such owner as the witness. -/
def recordFound : Com :=
  .ite (.eq (.var "found") (.lit 0))
    (.seq (.assign "found" (.lit 1)) (.assign "v" (.var "u")))
    .skip

/-- Look at slot `j`. If both the owner and the target are unmarked, the
slot is residual: it counts its owner into `ro` — once, and only when the
target is the larger endpoint — and it feeds the distinct-target test,
which raises the branching flag on an unmarked target other than the
block's first one. Then the pointer moves on; the scan never exits
early. -/
def slotStep : Com :=
  .seq
    (.ite (.eq (.get "mark" (.var "u")) (.lit 0))
      (.seq (.assign "w" (.get "tgt" (.var "j")))
        (.ite (.eq (.get "mark" (.var "w")) (.lit 0))
          (.seq
            (.ite (.eq (.var "cnted") (.lit 0))
              (.ite (.lt (.var "u") (.var "w"))
                (.seq (.assign "ro" (.add (.var "ro") (.lit 1)))
                  (.assign "cnted" (.lit 1)))
                .skip)
              .skip)
            (.ite (.eq (.var "seen") (.lit 0))
              (.seq (.assign "seen" (.lit 1)) (.assign "t1" (.var "w")))
              (.ite (.lt (.var "w") (.var "t1")) recordFound
                (.ite (.lt (.var "t1") (.var "w")) recordFound .skip))))
          .skip))
      .skip)
    (.assign "j" (.add (.var "j") (.lit 1)))

/-- One pass over the whole target array: the residual owner count and
the branching test. -/
def descendScan : Com :=
  .seq (.assign "j" (.lit 0))
    (.seq (.assign "u" (.lit 0))
      (.seq (.assign "ro" (.lit 0))
        (.seq (.assign "found" (.lit 0))
          (.seq (.assign "seen" (.lit 0))
            (.seq (.assign "t1" (.lit 0))
              (.seq (.assign "cnted" (.lit 0))
                (.while (.lt (.var "j") (.var "m2"))
                  (.seq ownerAdvance slotStep))))))))

/-- Push a frame on the branching vertex, take it into the cover, and
record it on the trail. The frame keeps the budget it was pushed at,
since the second branch will spend a different amount. -/
def pushFrame : Com :=
  .seq (.store "stkV" (.var "top") (.var "v"))
    (.seq (.store "stkB" (.var "top") (.var "bud"))
      (.seq (.store "stkT" (.var "top") (.var "tt"))
        (.seq (.store "stkP" (.var "top") (.lit 0))
          (.seq (.assign "top" (.add (.var "top") (.lit 1)))
            (.seq (.store "mark" (.var "v") (.lit 1))
              (.seq (.store "trail" (.var "tt") (.var "v"))
                (.seq (.assign "tt" (.add (.var "tt") (.lit 1)))
                  (.assign "bud" (.sub (.var "bud") (.lit 1))))))))))

/-- Descend: scan, then answer `1` at a matching within budget, give up
on the branch, or push a frame. -/
def descendBody : Com :=
  .seq descendScan
    (.ite (.eq (.var "found") (.lit 0))
      (.ite (.lt (.var "ro") (.add (.var "bud") (.lit 1)))
        (.seq (.assign "ans" (.lit 1)) (.assign "mode" (.lit 2)))
        (.assign "mode" (.lit 1)))
      (.ite (.eq (.var "bud") (.lit 0))
        (.assign "mode" (.lit 1))
        pushFrame))

/-- One slot of the flip's row scan: an unmarked neighbour joins the
cover and the trail. A neighbour listed twice is marked once, so the
trail grows by the residual degree exactly. -/
def rowStep : Com :=
  .seq (.assign "w" (.get "tgt" (.var "j")))
    (.seq
      (.ite (.eq (.get "mark" (.var "w")) (.lit 0))
        (.seq (.store "mark" (.var "w") (.lit 1))
          (.seq (.store "trail" (.var "tt") (.var "w"))
            (.assign "tt" (.add (.var "tt") (.lit 1)))))
        .skip)
      (.assign "j" (.add (.var "j") (.lit 1))))

/-- Flip the top frame to its second branch: unmark its vertex, restore
the budget it was pushed at, mark the vertex's whole residual
neighbourhood, and go on descending if that fits the budget. If it does
not, the branch is infeasible and the mode stays at backtrack, so the
next turn pops the frame. -/
def flipFrame : Com :=
  .seq (.store "mark" (.var "pv") (.lit 0))
    (.seq (.assign "tt" (.var "tb"))
      (.seq (.assign "bud" (.var "pb"))
        (.seq (.assign "j" (.get "off" (.var "pv")))
          (.seq (.assign "jend" (.get "off" (.add (.var "pv") (.lit 1))))
            (.seq (.while (.lt (.var "j") (.var "jend")) rowStep)
              (.seq (.store "stkP" (.var "sp") (.lit 1))
                (.seq (.assign "d" (.sub (.var "tt") (.var "tb")))
                  (.ite (.lt (.var "d") (.add (.var "bud") (.lit 1)))
                    (.seq (.assign "bud" (.sub (.var "bud") (.var "d")))
                      (.assign "mode" (.lit 0)))
                    .skip))))))))

/-- Pop the top frame: unwind the trail to the height the frame found,
unmarking as it goes, and restore the budget. -/
def popFrame : Com :=
  .seq
    (.while (.lt (.var "tb") (.var "tt"))
      (.seq (.assign "tt" (.sub (.var "tt") (.lit 1)))
        (.store "mark" (.get "trail" (.var "tt")) (.lit 0))))
    (.seq (.assign "bud" (.var "pb"))
      (.assign "top" (.sub (.var "top") (.lit 1))))

/-- Backtrack: answer `0` on an empty stack, flip a phase-`0` top frame
to its second branch, or pop a phase-`1` one. -/
def backtrackBody : Com :=
  .ite (.eq (.var "top") (.lit 0))
    (.seq (.assign "ans" (.lit 0)) (.assign "mode" (.lit 2)))
    (.seq (.assign "sp" (.sub (.var "top") (.lit 1)))
      (.seq (.assign "pv" (.get "stkV" (.var "sp")))
        (.seq (.assign "pb" (.get "stkB" (.var "sp")))
          (.seq (.assign "tb" (.get "stkT" (.var "sp")))
            (.ite (.eq (.get "stkP" (.var "sp")) (.lit 0))
              flipFrame popFrame)))))

/-- One turn of the outer loop, dispatched on the mode. -/
def outerBody : Com :=
  .ite (.eq (.var "mode") (.lit 0)) descendBody backtrackBody

/-- The whole algorithm: read the encoding and the budget, search, write
the answer. -/
def vcfCom : Com :=
  .seq (.read "n")
    (.seq (.read "m")
      (.seq (.assign "len" (.add (.var "n") (.lit 1)))
        (.seq (readLoop "off" "len")
          (.seq (.assign "m2" (.add (.var "m") (.var "m")))
            (.seq (readLoop "tgt" "m2")
              (.seq (.read "bud")
                (.seq (.while (.lt (.var "mode") (.lit 2)) outerBody)
                  (.write (.var "ans")))))))))

/-- Twenty-six scalars, the two arrays of the encoding, the mark and
trail arrays, the four stack arrays, four temporaries (the deepest
expression is a condition of the form `mark[w] = 0`, which the compiler
turns into `(mark[w] - 0) + (0 - mark[w])`). -/
def vcfLayout : Layout :=
  ⟨["n", "m", "m2", "len", "i", "t", "j", "u", "w", "jend", "seen", "t1",
    "cnted", "ro", "found", "v", "top", "tt", "bud", "mode", "ans", "sp",
    "pv", "pb", "tb", "d"],
   ["off", "tgt", "mark", "trail", "stkV", "stkB", "stkT", "stkP"], 4⟩

/-- The machine program. -/
def vcfProgram : Program := compileProgram vcfLayout vcfCom

theorem vcfCom_ok : Com.Ok vcfLayout vcfCom := by
  simp [vcfCom, readLoop, outerBody, descendBody, descendScan, ownerAdvance,
    slotStep, recordFound, pushFrame, backtrackBody, flipFrame, rowStep,
    popFrame, vcfLayout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-! ### The program, run

House discipline: the compiled machine program is run before anything is
proved about it. The instances below cover both answers at the boundary
budgets, the leaves of both kinds (the matching leaf and the exhausted
stack), the feasible and the infeasible flip, the pop, the `k = 0` cases,
the empty graph, one malformed word — which must merely not diverge —
and the encodings that name a neighbour twice, on which an uncapped slot
count would answer wrongly and a slot-counting branch test would search a
`2^k` tree. The word length is fixed at sixteen, which is more than these
instances need; the step counts do not depend on it. -/

/-- Run `vcfProgram` on an encoded instance, at a word length that holds
every number these instances produce. -/
def test (x : List ℕ) : Option (List ℕ × ℕ) := runOut 16 3000000 vcfProgram (initState x) 0

-- the triangle: cover number two, so `no` at budget one, `yes` at two.
-- The `no` pushes vertex `0`, reaches the matching leaf with `ro = 1 > 0`,
-- flips to the neighbourhood `{1, 2}` (infeasible, `d = 2 > 1`), pops and
-- exhausts the stack: T4, T2, T7, T8, T5.
#guard test ([3, 3, 0, 2, 4, 6, 1, 2, 0, 2, 0, 1] ++ [1]) = some ([0], 3030)
#guard test ([3, 3, 0, 2, 4, 6, 1, 2, 0, 2, 0, 1] ++ [2]) = some ([1], 2415)
-- the path on four vertices: cover number two
#guard test ([4, 3, 0, 1, 3, 5, 6, 1, 0, 2, 1, 3, 2] ++ [1]) = some ([0], 3120)
#guard test ([4, 3, 0, 1, 3, 5, 6, 1, 0, 2, 1, 3, 2] ++ [2]) = some ([1], 2505)
-- the star on three leaves: its center is a cover, found on the first push
#guard test ([4, 3, 0, 3, 4, 5, 6, 1, 2, 3, 0, 0, 0] ++ [1]) = some ([1], 2357)
-- the four-cycle: cover number two. At budget one the second descend finds
-- a branching vertex with no budget left, which is the `¬ Ok M 0` leaf (T3)
#guard test ([4, 4, 0, 2, 4, 6, 8, 1, 3, 0, 2, 1, 3, 2, 0] ++ [1]) = some ([0], 3862)
#guard test ([4, 4, 0, 2, 4, 6, 8, 1, 3, 0, 2, 1, 3, 2, 0] ++ [2]) = some ([1], 4294)
-- the five-cycle: cover number three. At budget two the search pushes twice,
-- fails, flips the inner frame infeasibly, pops it, and flips the outer one
-- *feasibly* — the only instance here that exercises T6, the flip that
-- returns to descend with the neighbourhood marked
#guard test ([5, 5, 0, 2, 4, 6, 8, 10, 1, 4, 0, 2, 1, 3, 2, 4, 3, 0] ++ [2]) = some ([0], 7990)
#guard test ([5, 5, 0, 2, 4, 6, 8, 10, 1, 4, 0, 2, 1, 3, 2, 4, 3, 0] ++ [3]) = some ([1], 5483)
-- two disjoint edges: the matching leaf decides both budgets with no push
-- at all, on the residual owner count alone (T2 then T5, and T1)
#guard test ([4, 2, 0, 1, 2, 3, 4, 1, 0, 3, 2] ++ [1]) = some ([0], 1142)
#guard test ([4, 2, 0, 1, 2, 3, 4, 1, 0, 3, 2] ++ [2]) = some ([1], 1107)
-- the complete graph on four vertices: cover number three
#guard test ([4, 6, 0, 3, 6, 9, 12, 1, 2, 3, 0, 2, 3, 0, 1, 3, 0, 1, 2] ++ [2]) = some ([0], 7512)
#guard test ([4, 6, 0, 3, 6, 9, 12, 1, 2, 3, 0, 2, 3, 0, 1, 3, 0, 1, 2] ++ [3]) = some ([1], 6127)
-- no edges: the empty set is a cover, even with no budget
#guard test ([2, 0, 0, 0, 0] ++ [0]) = some ([1], 200)
-- no vertices
#guard test ([0, 0, 0] ++ [0]) = some ([1], 144)
-- a malformed word: the program merely halts (the exhausted tape stops it)
#guard test [5, 2, 0, 1, 9, 3] = some ([], 129)

/-! #### The repeat-encoding regressions

The concept's encoding does not require a block to name each neighbour
once. `Repeats.lean` proves that `[2, 2, 0, 2, 4, 1, 1, 0, 0]` encodes
the single edge on two vertices with both blocks naming their neighbour
twice. A branch test that counted unmarked *slots* would branch here, on
a graph whose every vertex has residual degree one; a leaf test on the
uncapped slot count would see two residual edges where there is one and
answer `no` at budget one. Both counts below are the capped ones, so the
two words answer on the matching leaf without a single push. -/

#guard test ([2, 2, 0, 2, 4, 1, 1, 0, 0] ++ [0]) = some ([0], 1028)
#guard test ([2, 2, 0, 2, 4, 1, 1, 0, 0] ++ [1]) = some ([1], 993)

/-! The same doubling on a matching of `e` disjoint edges, at the two
budgets `e - 1` and `e`, is the family the slot-counting scan would search
a `2^k` tree on. The step counts are linear in the input, and flat per
input letter — 127, 134, 136 steps per letter at `e = 3, 5, 8` — with no
sign of the budget in them: the program never pushes a frame on these
instances. Lax11's `2^k` driver, which branches on an edge and cannot see
that the graph is a matching, takes 6934 steps on the first of them and
52554 on the second, against 2800 and 4572 here. -/

-- three disjoint edges, every slot doubled
#guard test ([6, 6, 0, 2, 4, 6, 8, 10, 12, 1, 1, 0, 0, 3, 3, 2, 2, 5, 5, 4, 4] ++ [2])
  = some ([0], 2800)
#guard test ([6, 6, 0, 2, 4, 6, 8, 10, 12, 1, 1, 0, 0, 3, 3, 2, 2, 5, 5, 4, 4] ++ [3])
  = some ([1], 2765)
-- five disjoint edges, every slot doubled
#guard test ([10, 10, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20,
    1, 1, 0, 0, 3, 3, 2, 2, 5, 5, 4, 4, 7, 7, 6, 6, 9, 9, 8, 8] ++ [4])
  = some ([0], 4572)
#guard test ([10, 10, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20,
    1, 1, 0, 0, 3, 3, 2, 2, 5, 5, 4, 4, 7, 7, 6, 6, 9, 9, 8, 8] ++ [5])
  = some ([1], 4537)
-- eight disjoint edges, every slot doubled
#guard test ([16, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32,
    1, 1, 0, 0, 3, 3, 2, 2, 5, 5, 4, 4, 7, 7, 6, 6, 9, 9, 8, 8,
    11, 11, 10, 10, 13, 13, 12, 12, 15, 15, 14, 14] ++ [7])
  = some ([0], 7230)
#guard test ([16, 16, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32,
    1, 1, 0, 0, 3, 3, 2, 2, 5, 5, 4, 4, 7, 7, 6, 6, 9, 9, 8, 8,
    11, 11, 10, 10, 13, 13, 12, 12, 15, 15, 14, 14] ++ [8])
  = some ([1], 7195)

end Lax15Proofs.VC
