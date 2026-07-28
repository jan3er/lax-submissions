import Lax15Proofs.Program

/-!
The second driver: the branch-and-solve search tree for vertex cover, as
an IMP+ program.

The algorithm is the rung-B plan's. Everything outside the descend phase
is rung A's, reused **by name** — the read phase (`readLoop`), the push
(`pushFrame`), the backtrack dispatch with its flip and its pop
(`backtrackBody`, `flipFrame`, `popFrame`) — so that the Run lemmas
already proved about those blocks (`flipFrame_eq`, `popFrame_eq`,
`rowLoop_run`, `unwind_run`) apply here unchanged. Two things are new.

The **branching test** is raised from two to three. Rung A branches on a
vertex with two residual neighbours, which costs `1` and `2` units of
budget and gives `fib`; here a vertex is a branching vertex only when it
has *three* distinct residual neighbours, so the two children cost `1`
and `3` and the leaf count obeys `T(b) ≤ T(b-1) + T(b-3)`.

The price of the sharper test is that the leaf is no longer a counting
argument. Rung A's leaf was a matching: with every residual degree at
most one the residual graph is a matching and its cover number is its
edge count, which one pass can count. Here the leaf has every residual
degree at most *two*, so the residual graph is a disjoint union of paths
and cycles, and its cover number is `∑_C ⌈e_C / 2⌉` over the connected
components. That sum is what the **solver block** computes: a
breadth-first sweep in the shape of the components driver, one component
at a time, counting each residual edge once and halving the count with a
toggle. The toggle is the halving — the machine has no division, and
`⌈e/2⌉` is exactly what a flag flipped once per edge, and counted only
when it is down, accumulates.

### The scan

One descend pass walks the target array once, `j` from `0` to `2m`, with
the block owner `u` walking alongside; the inner owner loop is rung A's,
amortized over the pass. What the pass computes is only `found`: the
per-owner registers are now `seen ∈ {0, 1, 2}`, `t1` and `t2`, the first
and second *distinct* unmarked target of the current block, and the flag
is raised on a third distinct one. `v` records the first such owner.
`ro` and `cnted` are gone with the matching leaf.

The scan **runs to completion**; there is no early exit. It could have
one — nothing after the first branching vertex is read — and the machine
model's idiom for `break` is to force the loop counter to its bound. The
full pass is chosen instead, for three reasons: the cost bound is the
same either way (one pass over `2m` slots, which is what the potential
already pays for), the loop invariant stays the plain "`found` says
whether some owner below `j` has three distinct unmarked targets" with no
disjunction for the forced state, and — the deciding one — it keeps the
scan syntactically parallel to rung A's `descendScan`, whose Run lemma
B4 imitates line for line.

### The solver

At `¬ found` every unmarked vertex has at most two distinct unmarked
neighbours. The solver clears `vis`, sets `s := 0`, and sweeps the roots
`r = 0, …, n-1`. An unmarked, unvisited root opens a component: it is
visited, enqueued, the toggle is set to `0` — **per component**, which is
what makes the sum a sum of ceilings rather than one ceiling — and the
queue is drained. Draining dequeues `u`, scans its block with the *same*
`seen`/`t1`/`t2` dedup as the descend scan, and for each distinct
unmarked target `w` does two things: it counts the edge `{u, w}` if
`u < w`, so that each residual edge is counted at the one endpoint that
is smaller and hence exactly once; and it visits and enqueues `w` if `w`
is unvisited. The queue is never reset between components, as in the
components driver: `vis` is set before the enqueue, so each vertex is
enqueued at most once per solver call and `tl ≤ n`.

The dedup admits a third distinct target syntactically — the shared
`dedupStep` has a slot for it — and the solver's third slot is `skip`.
Under `¬ found` that branch is unreachable, and the Run proof shows it
so; what matters for the reading of the program is that a third distinct
target would be **skipped, not counted**, so the count never exceeds the
residual edge count even off the invariant.

Then `s ≤ bud` answers `1` and stops, and otherwise the branch is
abandoned: `mode := 1`.

### The dedup, once

The `seen`/`t1`/`t2` dedup is literally one definition, `dedupStep`,
used by both scans; the two differ only in the three commands they hang
on the first, second and third distinct target. In the descend scan
those are `skip`, `skip`, `recordFound` — rung A's `recordFound`, reused;
in the solver they are `countPush`, `countPush`, `skip`.

### The names

Scalars, in the order of the layout:

* `n`, `m` — the vertex and edge counts, off the tape.
* `m2` — `2 * m`, the length of the target array (computed as `m + m`;
  there is no multiplication anywhere in this program).
* `len` — `n + 1`, the length of the offset array.
* `i`, `t` — the read loop's counter and cell (Lax11's `readLoop`); `i`
  is also the counter of the solver's `vis`-clearing pass, which runs
  long after the last read.
* `j` — the slot pointer: of the descend scan, of the solver's row scan,
  and of the flip's row scan.
* `u` — the block owner of the descend scan, and the dequeued vertex of
  the solver's drain.
* `w` — the target of slot `j`, in all three scans.
* `jend` — the end of a row scan, `off[u+1]` or `off[pv+1]`.
* `seen`, `t1`, `t2` — the per-owner registers of the dedup: how many
  distinct unmarked targets this block has shown (`0`, `1`, `2`) and
  which they are. Reset on owner advance in the descend scan, and at the
  start of each row in the solver.
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
* `head`, `tl` — the solver's queue pointers, both reset once per solver
  call and monotone across its components.
* `s` — the solver's accumulated cost, `∑_C ⌈e_C / 2⌉`.
* `tog` — the halving toggle, reset at the root of each component.
* `r` — the solver's root sweep counter.

Rung A's `ro` and `cnted` are gone: there is no owner count here.

Arrays, in the order of the layout, with the extents the proofs give
them:

* `off` (extent `n + 1`), `tgt` (extent `2m`) — the encoding.
* `mark` (extent `n`) — the indicator of the marked set.
* `trail` (extent `n + 1`) — the marked vertices in the order they were
  marked.
* `stkV`, `stkB`, `stkT`, `stkP` (extent `n + 1`) — the frames: the
  vertex branched on, the budget at the push, the trail height at the
  push, and the phase (`0` first branch, `1` second).
* `vis` (extent `n`) — the solver's visited indicator, cleared at the
  start of every solver call. Fresh arrays are zeroed, so the first call
  would not need the pass; every later one does.
* `q` (extent `n`) — the solver's queue. Each unmarked vertex is
  enqueued at most once per call, because `vis` is set before the
  enqueue, so `tl ≤ n`.

### The statement layout

The commands below are the ground truth for the Run proofs; this is the
shape they see. Blocks marked (A) are rung A's, reused by name.

    vcf3Com = read n; read m; len := n+1; readLoop off len;          (A)
              m2 := m+m; readLoop tgt m2; read bud;                  (A)
              while mode < 2 do outerBody3;
              write ans

    outerBody3    = if mode = 0 then descendBody3 else backtrackBody (A)
    descendBody3  = descendScan3;
                    if found = 0 then solveBlock
                    else if bud = 0 then mode := 1 else pushFrame    (A)

    descendScan3  = j := 0; u := 0; found := 0;
                    seen := 0; t1 := 0; t2 := 0;
                    while j < m2 do (ownerAdvance3; slotStep3)
    ownerAdvance3 = while off[u+1] < j+1 do
                      (u := u+1; seen := 0; t1 := 0; t2 := 0)
    slotStep3     = (if mark[u] = 0 then
                       w := tgt[j];
                       if mark[w] = 0
                         then dedupStep skip skip recordFound        (A)
                         else skip
                     else skip);
                    j := j+1

    dedupStep A B C = if seen = 0 then (seen := 1; t1 := w; A)
                      else if w ≠ t1 then
                        (if seen = 1 then (seen := 2; t2 := w; B)
                         else if w ≠ t2 then C else skip)
                      else skip

    solveBlock    = clearVis; s := 0; head := 0; tl := 0; r := 0;
                    while r < n do rootStep;
                    if s < bud+1 then (ans := 1; mode := 2)
                                 else mode := 1
    clearVis      = i := 0; while i < n do (vis[i] := 0; i := i+1)
    rootStep      = (if mark[r] = 0 then
                       (if vis[r] = 0 then
                          (vis[r] := 1; q[tl] := r; tl := tl+1;
                           tog := 0; drain3)
                        else skip)
                     else skip);
                    r := r+1
    drain3        = while head < tl do expandBody3
    expandBody3   = u := q[head]; j := off[u]; jend := off[u+1];
                    seen := 0; t1 := 0; t2 := 0;
                    while j < jend do solveSlot;
                    head := head+1
    solveSlot     = w := tgt[j];
                    (if mark[w] = 0
                       then dedupStep countPush countPush skip
                       else skip);
                    j := j+1
    countPush     = (if u < w then
                       (if tog = 0 then (s := s+1; tog := 1)
                                   else tog := 0)
                     else skip);
                    (if vis[w] = 0 then
                       (vis[w] := 1; q[tl] := w; tl := tl+1)
                     else skip)

    backtrackBody, flipFrame, popFrame, pushFrame, readLoop           (A)

A condition is a single comparison, so `x ≤ y` is written `x < y + 1`
and `w ≠ t` is two strict comparisons in nested `ite`s — the `neTest`
combinator, which is why the third-target command appears four times in
the elaborated tree of `dedupStep` and is therefore always a name.
-/

namespace Lax15Proofs.VC3

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC

/-! ### The shared dedup -/

/-- `w ≠ t` guarding `c`, as two strict comparisons: the machine's
conditions are single comparisons, so a disequality costs a duplicated
branch. -/
def neTest (t : String) (c : Com) : Com :=
  .ite (.lt (.var "w") (.var t)) c (.ite (.lt (.var t) (.var "w")) c .skip)

/-- The per-owner deduplication, shared by the descend scan and the
solver's row scan. `seen` counts the distinct unmarked targets the block
has shown so far, `t1` and `t2` name them; `first`, `second` and `third`
are what the caller does on a first, second and third *distinct* target.
A repeat of `t1` or `t2` does nothing at all, which is the whole point:
the encoding may name a neighbour any number of times. -/
def dedupStep (first second third : Com) : Com :=
  .ite (.eq (.var "seen") (.lit 0))
    (.seq (.assign "seen" (.lit 1)) (.seq (.assign "t1" (.var "w")) first))
    (neTest "t1"
      (.ite (.eq (.var "seen") (.lit 1))
        (.seq (.assign "seen" (.lit 2)) (.seq (.assign "t2" (.var "w")) second))
        (neTest "t2" third)))

/-! ### The descend scan, at threshold three -/

/-- Advance the block owner past every block ending at or before the
slot pointer, resetting the per-owner registers each time. Rung A's
`ownerAdvance` with `t2` in place of `cnted`: the register set of the
scan changed, so this one block of the scan is re-typed rather than
reused. -/
def ownerAdvance3 : Com :=
  .while (.lt (.get "off" (.add (.var "u") (.lit 1))) (.add (.var "j") (.lit 1)))
    (.seq (.assign "u" (.add (.var "u") (.lit 1)))
      (.seq (.assign "seen" (.lit 0))
        (.seq (.assign "t1" (.lit 0))
          (.assign "t2" (.lit 0)))))

/-- Look at slot `j`. If both the owner and the target are unmarked, the
slot names a residual neighbour, and it feeds the distinct-target test:
the flag is raised on the third distinct unmarked target of a block. The
pointer moves on; the scan never exits early. -/
def slotStep3 : Com :=
  .seq
    (.ite (.eq (.get "mark" (.var "u")) (.lit 0))
      (.seq (.assign "w" (.get "tgt" (.var "j")))
        (.ite (.eq (.get "mark" (.var "w")) (.lit 0))
          (dedupStep .skip .skip VC.recordFound)
          .skip))
      .skip)
    (.assign "j" (.add (.var "j") (.lit 1)))

/-- One pass over the whole target array: is there an unmarked vertex
with three distinct unmarked neighbours, and which is the first one. -/
def descendScan3 : Com :=
  .seq (.assign "j" (.lit 0))
    (.seq (.assign "u" (.lit 0))
      (.seq (.assign "found" (.lit 0))
        (.seq (.assign "seen" (.lit 0))
          (.seq (.assign "t1" (.lit 0))
            (.seq (.assign "t2" (.lit 0))
              (.while (.lt (.var "j") (.var "m2"))
                (.seq ownerAdvance3 slotStep3)))))))

/-! ### The solver -/

/-- Zero the visited array. Every solver call starts here; only the
first could skip it, since fresh arrays are zeroed. -/
def clearVis : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "n"))
      (.seq (.store "vis" (.var "i") (.lit 0))
        (.assign "i" (.add (.var "i") (.lit 1)))))

/-- What a distinct unmarked target of a dequeued vertex does: count the
edge, if this is its smaller endpoint, into the halving toggle; and
visit and enqueue the target if the search has not reached it yet. The
`u < w` test is what counts each residual edge exactly once — the other
endpoint is dequeued too, and sees the same edge from above. -/
def countPush : Com :=
  .seq
    (.ite (.lt (.var "u") (.var "w"))
      (.ite (.eq (.var "tog") (.lit 0))
        (.seq (.assign "s" (.add (.var "s") (.lit 1))) (.assign "tog" (.lit 1)))
        (.assign "tog" (.lit 0)))
      .skip)
    (.ite (.eq (.get "vis" (.var "w")) (.lit 0))
      (.seq (.store "vis" (.var "w") (.lit 1))
        (.seq (.store "q" (.var "tl") (.var "w"))
          (.assign "tl" (.add (.var "tl") (.lit 1)))))
      .skip)

/-- One slot of the solver's row scan. A marked target is ignored, a
repeated one is ignored, and a third distinct one is *skipped* — it
cannot happen below the branching threshold, and skipping rather than
counting keeps `s` a lower bound on nothing but the residual edges. -/
def solveSlot : Com :=
  .seq (.assign "w" (.get "tgt" (.var "j")))
    (.seq
      (.ite (.eq (.get "mark" (.var "w")) (.lit 0))
        (dedupStep countPush countPush .skip)
        .skip)
      (.assign "j" (.add (.var "j") (.lit 1))))

/-- Take the next vertex off the queue and scan its whole block, with
the per-row registers reset. The queue pointer moves after the scan, as
in the components driver. -/
def expandBody3 : Com :=
  .seq (.assign "u" (.get "q" (.var "head")))
    (.seq (.assign "j" (.get "off" (.var "u")))
      (.seq (.assign "jend" (.get "off" (.add (.var "u") (.lit 1))))
        (.seq (.assign "seen" (.lit 0))
          (.seq (.assign "t1" (.lit 0))
            (.seq (.assign "t2" (.lit 0))
              (.seq (.while (.lt (.var "j") (.var "jend")) solveSlot)
                (.assign "head" (.add (.var "head") (.lit 1)))))))))

/-- Empty the queue: the breadth-first search of one component. -/
def drain3 : Com := .while (.lt (.var "head") (.var "tl")) expandBody3

/-- One vertex of the solver's root sweep. An unmarked, unvisited vertex
opens a component: the toggle goes down and the search runs. -/
def rootStep : Com :=
  .seq
    (.ite (.eq (.get "mark" (.var "r")) (.lit 0))
      (.ite (.eq (.get "vis" (.var "r")) (.lit 0))
        (.seq (.store "vis" (.var "r") (.lit 1))
          (.seq (.store "q" (.var "tl") (.var "r"))
            (.seq (.assign "tl" (.add (.var "tl") (.lit 1)))
              (.seq (.assign "tog" (.lit 0)) drain3))))
        .skip)
      .skip)
    (.assign "r" (.add (.var "r") (.lit 1)))

/-- The leaf of the search: with every residual degree at most two, the
cover number of the residual graph is `∑_C ⌈e_C / 2⌉`, and this block
computes it. Within budget it answers `1`; otherwise the branch is
abandoned and the machine backtracks. -/
def solveBlock : Com :=
  .seq clearVis
    (.seq (.assign "s" (.lit 0))
      (.seq (.assign "head" (.lit 0))
        (.seq (.assign "tl" (.lit 0))
          (.seq (.assign "r" (.lit 0))
            (.seq (.while (.lt (.var "r") (.var "n")) rootStep)
              (.ite (.lt (.var "s") (.add (.var "bud") (.lit 1)))
                (.seq (.assign "ans" (.lit 1)) (.assign "mode" (.lit 2)))
                (.assign "mode" (.lit 1))))))))

/-! ### The loop -/

/-- Descend: scan, then either solve the residual graph outright or
branch on the vertex the scan found — giving up on the branch when there
is no budget for it. -/
def descendBody3 : Com :=
  .seq descendScan3
    (.ite (.eq (.var "found") (.lit 0))
      solveBlock
      (.ite (.eq (.var "bud") (.lit 0))
        (.assign "mode" (.lit 1))
        VC.pushFrame))

/-- One turn of the outer loop, dispatched on the mode. The backtrack
half is rung A's, unchanged. -/
def outerBody3 : Com :=
  .ite (.eq (.var "mode") (.lit 0)) descendBody3 VC.backtrackBody

/-- The whole algorithm: read the encoding and the budget, search, write
the answer. The read phase is rung A's. -/
def vcf3Com : Com :=
  .seq (.read "n")
    (.seq (.read "m")
      (.seq (.assign "len" (.add (.var "n") (.lit 1)))
        (.seq (readLoop "off" "len")
          (.seq (.assign "m2" (.add (.var "m") (.var "m")))
            (.seq (readLoop "tgt" "m2")
              (.seq (.read "bud")
                (.seq (.while (.lt (.var "mode") (.lit 2)) outerBody3)
                  (.write (.var "ans")))))))))

/-- Thirty scalars — rung A's twenty-six less `ro` and `cnted`, plus the
dedup's `t2` and the solver's `head`, `tl`, `s`, `tog`, `r` — the two
arrays of the encoding, the mark and trail arrays, the four stack
arrays, the solver's two, and four temporaries (the deepest expression
is a condition of the form `mark[w] = 0`, which the compiler turns into
`(mark[w] - 0) + (0 - mark[w])`). -/
def vcf3Layout : Layout :=
  ⟨["n", "m", "m2", "len", "i", "t", "j", "u", "w", "jend", "seen", "t1", "t2",
    "found", "v", "top", "tt", "bud", "mode", "ans", "sp", "pv", "pb", "tb", "d",
    "head", "tl", "s", "tog", "r"],
   ["off", "tgt", "mark", "trail", "stkV", "stkB", "stkT", "stkP", "vis", "q"], 4⟩

/-- The machine program. -/
def vcf3Program : Program := compileProgram vcf3Layout vcf3Com

theorem vcf3Com_ok : Com.Ok vcf3Layout vcf3Com := by
  simp [vcf3Com, readLoop, outerBody3, descendBody3, descendScan3, ownerAdvance3,
    slotStep3, dedupStep, neTest, VC.recordFound, VC.pushFrame, solveBlock, clearVis,
    rootStep, drain3, expandBody3, solveSlot, countPush, VC.backtrackBody,
    VC.flipFrame, VC.rowStep, VC.popFrame, vcf3Layout, Com.Ok, Cond.Ok, condExpr,
    Expr.Ok]

/-! ### The program, run

House discipline: the compiled machine program is run before anything is
proved about it. Every expected answer below was derived by hand first —
a cover witness for a `yes`, a counting argument for a `no` — and the
derivation is the comment above the guard. The instances cover both
branches of the descend dispatch, both verdicts of the solver, the flip
(feasible and infeasible), the pop, the empty budget, the empty graph,
one malformed word which must merely not diverge, and the two dedup
regressions: an encoding that names a neighbour twice, and a disjoint
matching whose every slot is doubled.

The residual-graph facts the derivations use: below the branching
threshold every unmarked vertex has at most two distinct unmarked
neighbours, so the residual graph is a disjoint union of paths and
cycles, and its cover number is `∑_C ⌈e_C / 2⌉` — a path with `e` edges
costs `⌈e/2⌉`, a cycle with `e` edges costs `⌈e/2⌉`, an isolated vertex
costs nothing. The word length is fixed at sixteen, which is more than
these instances need; the step counts do not depend on it. -/

/-- Run `vcf3Program` on an encoded instance, at a word length that
holds every number these instances produce. -/
def test (x : List ℕ) : Option (List ℕ × ℕ) := runOut 16 3000000 vcf3Program (initState x) 0

-- **K₄** — `n = 4`, `m = 6`, every degree three, offsets `0,3,6,9,12`.
-- Cover number `4 - α = 4 - 1 = 3`: any two vertices leave the edge
-- between the other two uncovered, and `{0,1,2}` covers everything. So
-- `no` at `2`, `yes` at `3`. Every vertex has three distinct residual
-- neighbours, so the first descend branches — this is the instance that
-- exercises the new threshold against rung A's.
#guard test ([4, 6, 0, 3, 6, 9, 12, 1, 2, 3, 0, 2, 3, 0, 1, 3, 0, 1, 2] ++ [2])
  = some ([0], 7442)
#guard test ([4, 6, 0, 3, 6, 9, 12, 1, 2, 3, 0, 2, 3, 0, 1, 3, 0, 1, 2] ++ [3])
  = some ([1], 6628)

-- **K₅** — `n = 5`, `m = 10`, every degree four, offsets `0,4,8,12,16,20`.
-- Cover number `5 - 1 = 4`: three vertices leave a `K₂` uncovered.
-- `no` at `3`, `yes` at `4`. The deepest branching here: three pushes
-- before the residual graph thins to a single edge, and `d = 4` on the
-- first flip, so the second branch is infeasible at every budget below
-- four.
#guard test ([5, 10, 0, 4, 8, 12, 16, 20,
    1, 2, 3, 4, 0, 2, 3, 4, 0, 1, 3, 4, 0, 1, 2, 4, 0, 1, 2, 3] ++ [3])
  = some ([0], 14649)
#guard test ([5, 10, 0, 4, 8, 12, 16, 20,
    1, 2, 3, 4, 0, 2, 3, 4, 0, 1, 3, 4, 0, 1, 2, 4, 0, 1, 2, 3] ++ [4])
  = some ([1], 12846)

-- **K₁,₄** — the star, centre `0`, leaves `1,2,3,4`; `n = 5`, `m = 4`,
-- offsets `0,4,5,6,7,8`. `{0}` covers all four edges, so `yes` at `1`.
-- The scan finds the centre (four distinct unmarked targets, three
-- suffice), pushes it, and the residual graph is four isolated
-- vertices: the solver sweeps four singleton components, each of cost
-- zero, and answers at `s = 0 ≤ 0`.
#guard test ([5, 4, 0, 4, 5, 6, 7, 8, 1, 2, 3, 4, 0, 0, 0, 0] ++ [1])
  = some ([1], 4511)

-- **C₇** — the seven-cycle `0-1-…-6-0`; `n = 7`, `m = 7`, every degree
-- two. Cover number `⌈7/2⌉ = 4`: `{0,2,4,6}` meets all seven edges
-- `0-1,1-2,2-3,3-4,4-5,5-6,6-0`, and a cover of size three would leave
-- an independent set of size four, which `C₇` has not — an independent
-- set in an odd cycle on seven vertices has at most three. `no` at `3`,
-- `yes` at `4`. Pure solver: no vertex has three distinct neighbours, so the
-- first descend goes straight to the leaf, one component with seven
-- edges, `s = ⌈7/2⌉ = 4`.
#guard test ([7, 7, 0, 2, 4, 6, 8, 10, 12, 14,
    1, 6, 0, 2, 1, 3, 2, 4, 3, 5, 4, 6, 5, 0] ++ [3])
  = some ([0], 7016)
#guard test ([7, 7, 0, 2, 4, 6, 8, 10, 12, 14,
    1, 6, 0, 2, 1, 3, 2, 4, 3, 5, 4, 6, 5, 0] ++ [4])
  = some ([1], 6981)

-- **C₄ + C₆**, disjoint — `n = 10`, `m = 10`; the four-cycle on
-- `0,1,2,3` and the six-cycle on `4,…,9`. Cover number
-- `2 + 3 = 5` (`{0,2}` and `{4,6,8}`), and four do not suffice since
-- `C₄` needs two and `C₆` needs three. `no` at `4`, `yes` at `5`. Two
-- components, `s = ⌈4/2⌉ + ⌈6/2⌉ = 2 + 3`: the instance that would fail
-- if the toggle were not reset at each root.
#guard test ([10, 10, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20,
    1, 3, 0, 2, 1, 3, 2, 0, 5, 9, 4, 6, 5, 7, 6, 8, 7, 9, 8, 4] ++ [4])
  = some ([0], 9944)
#guard test ([10, 10, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20,
    1, 3, 0, 2, 1, 3, 2, 0, 5, 9, 4, 6, 5, 7, 6, 8, 7, 9, 8, 4] ++ [5])
  = some ([1], 9909)

-- **triangle + P₃ + C₄** — `n = 10`, `m = 9`: the triangle on `0,1,2`,
-- the two-edge path `3-4-5`, the four-cycle on `6,7,8,9`; offsets
-- `0,2,4,6,7,9,10,12,14,16,18`. Cover number `2 + 1 + 2 = 5`
-- (`{0,1}`, `{4}`, `{6,8}`), and each summand is forced. `no` at `4`,
-- `yes` at `5`. Three components of three, two and four edges:
-- `s = ⌈3/2⌉ + ⌈2/2⌉ + ⌈4/2⌉ = 2 + 1 + 2`. The odd component is the one
-- that makes the halving a *ceiling*.
#guard test ([10, 9, 0, 2, 4, 6, 7, 9, 10, 12, 14, 16, 18,
    1, 2, 0, 2, 0, 1, 4, 3, 5, 4, 7, 9, 6, 8, 7, 9, 8, 6] ++ [4])
  = some ([0], 9236)
#guard test ([10, 9, 0, 2, 4, 6, 7, 9, 10, 12, 14, 16, 18,
    1, 2, 0, 2, 0, 1, 4, 3, 5, 4, 7, 9, 6, 8, 7, 9, 8, 6] ++ [5])
  = some ([1], 9201)

-- **P₄** — the path `0-1-2-3`; `n = 4`, `m = 3`. Cover number two:
-- `{1,2}` covers, and one vertex covers at most two of the three edges.
-- `no` at `1`, `yes` at `2`. Pure solver again, one component of three
-- edges, `s = ⌈3/2⌉ = 2`.
#guard test ([4, 3, 0, 1, 3, 5, 6, 1, 0, 2, 1, 3, 2] ++ [1]) = some ([0], 3358)
#guard test ([4, 3, 0, 1, 3, 5, 6, 1, 0, 2, 1, 3, 2] ++ [2]) = some ([1], 3323)

-- **the bull** — the triangle `0,1,2` with a pendant `3` at `0` and a
-- pendant `4` at `1`; `n = 5`, `m = 5`, offsets `0,3,6,8,9,10`. `{0,1}`
-- covers all five edges (`0-1,0-2,1-2,0-3,1-4`), and one vertex covers
-- at most `deg = 3 < 5` of them, so the cover number is two: `no` at
-- `1`, `yes` at `2`. The one instance here that runs the whole
-- machinery in a single sweep: vertex `0` has three distinct
-- neighbours, so the first descend pushes it; the residual graph is
-- then the path `2-1-4` plus the isolated `3`, which the solver costs
-- at `⌈2/2⌉ = 1`. At budget one that leaves `1 > 0`, the flip marks
-- `{1,2,3}` with `d = 3 > 1` — infeasible — and the pop empties the
-- stack for the `no`.
#guard test ([5, 5, 0, 3, 6, 8, 9, 10, 1, 2, 3, 0, 2, 4, 0, 1, 0, 1] ++ [1])
  = some ([0], 6618)
#guard test ([5, 5, 0, 3, 6, 8, 9, 10, 1, 2, 3, 0, 2, 4, 0, 1, 0, 1] ++ [2])
  = some ([1], 5804)

-- **2K₂ with every slot doubled** — `n = 4`, `m = 4`, offsets
-- `0,2,4,6,8`, targets `1,1 | 0,0 | 3,3 | 2,2`: two disjoint edges,
-- each block naming its one neighbour twice. Cover number two, one
-- vertex per edge: `no` at `1`, `yes` at `2`. Two things are being
-- watched. The dedup: a block with two unmarked *slots* but one
-- unmarked *target* must not look like a branching vertex, and does
-- not — the scan never branches here. And the count: the edge `{0,1}`
-- is counted once, at `u = 0 < 1 = w`, and the repeat is skipped
-- before it reaches the toggle, so `s = 1 + 1 = 2` and not four.
#guard test ([4, 4, 0, 2, 4, 6, 8, 1, 1, 0, 0, 3, 3, 2, 2] ++ [1])
  = some ([0], 3780)
#guard test ([4, 4, 0, 2, 4, 6, 8, 1, 1, 0, 0, 3, 3, 2, 2] ++ [2])
  = some ([1], 3745)

-- **the repeating word of `Repeats.lean`** — `[2,2,0,2,4,1,1,0,0]`, the
-- one edge on two vertices with both blocks naming their neighbour
-- twice; `encodesGraph_repeatWord` proves it is a legitimate encoding.
-- Cover number one. `no` at `0`, `yes` at `1`: one component, one edge,
-- `s = ⌈1/2⌉ = 1`.
#guard test ([2, 2, 0, 2, 4, 1, 1, 0, 0] ++ [0]) = some ([0], 1974)
#guard test ([2, 2, 0, 2, 4, 1, 1, 0, 0] ++ [1]) = some ([1], 1939)

-- **no edges** — two vertices, no edges: the empty set is a cover, so
-- `yes` even at budget zero. Two singleton components, `s = 0`.
#guard test ([2, 0, 0, 0, 0] ++ [0]) = some ([1], 712)
-- **no vertices** — the root sweep does not run at all.
#guard test ([0, 0, 0] ++ [0]) = some ([1], 172)
-- **a malformed word**: the program merely halts (the exhausted tape
-- stops it in the read phase).
#guard test [5, 2, 0, 1, 9, 3] = some ([], 137)

/-! #### Against rung A

The same instances on `vcfCom`, where they are not already guarded in
`Program.lean`. The picture is the one the two recurrences predict, with
a constant against rung B: the solver is a second pass over the graph
where rung A's matching leaf was fused into the branching scan, and the
layout has ten arrays rather than eight, so every array access costs
more machine steps.

Rung B wins outright exactly where the branching bites and its leaf is
strictly stronger. On `C₇` — every degree two, so rung A branches to a
depth its Fibonacci tree pays for while rung B answers at the first
leaf — it is `17937` against `7016` at `k = 3` and `9776` against `6981`
at `k = 4`. On the `K`-family the two effects nearly cancel at these
sizes: `K₄` is `7512/6127` (A) against `7442/6628` (B), `K₅` is
`14782/12437` (A) against `14649/12846` (B) — rung B ahead on the `no`,
behind on the `yes`, since both programs push the same three times and
rung B pays for the solver at the leaf. Where there is nothing to branch
on and the leaf is a matching, rung A's fused count is simply cheaper:
`P₄` is `3120/2505` against `3358/3323`, the repeating word `1028/993`
against `1974/1939`, and the doubled `2K₂` `1914/1879` against
`3780/3745`. None of this is the asymptotics; it is the constant, and
the asymptotics is what the concept states. -/

#guard VC.test ([5, 10, 0, 4, 8, 12, 16, 20,
    1, 2, 3, 4, 0, 2, 3, 4, 0, 1, 3, 4, 0, 1, 2, 4, 0, 1, 2, 3] ++ [3])
  = some ([0], 14782)
#guard VC.test ([5, 10, 0, 4, 8, 12, 16, 20,
    1, 2, 3, 4, 0, 2, 3, 4, 0, 1, 3, 4, 0, 1, 2, 4, 0, 1, 2, 3] ++ [4])
  = some ([1], 12437)
#guard VC.test ([7, 7, 0, 2, 4, 6, 8, 10, 12, 14,
    1, 6, 0, 2, 1, 3, 2, 4, 3, 5, 4, 6, 5, 0] ++ [3]) = some ([0], 17937)
#guard VC.test ([7, 7, 0, 2, 4, 6, 8, 10, 12, 14,
    1, 6, 0, 2, 1, 3, 2, 4, 3, 5, 4, 6, 5, 0] ++ [4]) = some ([1], 9776)
#guard VC.test ([4, 4, 0, 2, 4, 6, 8, 1, 1, 0, 0, 3, 3, 2, 2] ++ [1])
  = some ([0], 1914)
#guard VC.test ([4, 4, 0, 2, 4, 6, 8, 1, 1, 0, 0, 3, 3, 2, 2] ++ [2])
  = some ([1], 1879)

end Lax15Proofs.VC3
