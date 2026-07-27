import Lax11.VertexCover
import Lax11Proofs.CCPhases
import Lax11Proofs.VCSpec

/-!
The driver: the bounded search tree for vertex cover, as an IMP+
program.

The algorithm is the plan's. After the read phase — the CSR block into
`off` and `tgt` exactly as in the components driver, then one more
`read` for the budget — the machine runs one outer loop over a mode
scalar: descend (`0`) scans for an uncovered edge and either answers,
gives up on the branch, or pushes a frame and marks an endpoint;
backtrack (`1`) either answers, flips the top frame to its second
branch, or pops it; done (`2`) exits. The stack lives in three arrays
`stkU`, `stkV`, `stkP` with a `top` scalar; the budget is a scalar,
since in the `2^k` tree both children run at one budget less and no
frame needs to store it.

The scan is a single flat loop: one pointer `j` over the target array
and one owner `u`, and each iteration either advances the owner past an
exhausted block or examines one slot — no inner loop, which keeps it
one application of the loop rule. Loops exit early by assigning their
counters to their bounds (`j := m2`), the house idiom for `break`,
since a condition is a single comparison. The mark array needs no
initialization: fresh arrays are zeroed and the marker for "unmarked"
is `0`.
-/

namespace Lax11Proofs.VC

open Lax11.Ram Lax11.RamComputes Lax11.GraphEncoding
open Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning Lax11Proofs.CC

/-! ### The program -/

/-- One turn of the scan: if `j` has left the owner's block, advance
the owner; otherwise examine slot `j`, and on an uncovered edge record
its endpoints, raise the flag and force the exit. -/
def scanBody : Com :=
  .ite (.lt (.var "j") (.get "off" (.add (.var "u") (.lit 1))))
    (.seq (.assign "w" (.get "tgt" (.var "j")))
      (.ite (.eq (.get "mark" (.var "u")) (.lit 0))
        (.ite (.eq (.get "mark" (.var "w")) (.lit 0))
          (.seq (.assign "eu" (.var "u"))
            (.seq (.assign "ev" (.var "w"))
              (.seq (.assign "found" (.lit 1))
                (.assign "j" (.var "m2")))))
          (.assign "j" (.add (.var "j") (.lit 1))))
        (.assign "j" (.add (.var "j") (.lit 1)))))
    (.assign "u" (.add (.var "u") (.lit 1)))

/-- Scan the whole target array for an uncovered edge. -/
def scan : Com :=
  .seq (.assign "j" (.lit 0))
    (.seq (.assign "u" (.lit 0))
      (.seq (.assign "found" (.lit 0))
        (.while (.lt (.var "j") (.var "m2")) scanBody)))

/-- Descend: scan, then answer `1`, give up on the branch, or push a
frame committing `eu`. -/
def descendBody : Com :=
  .seq scan
    (.ite (.eq (.var "found") (.lit 0))
      (.seq (.assign "ans" (.lit 1)) (.assign "mode" (.lit 2)))
      (.ite (.eq (.var "bud") (.lit 0))
        (.assign "mode" (.lit 1))
        (.seq (.store "stkU" (.var "top") (.var "eu"))
          (.seq (.store "stkV" (.var "top") (.var "ev"))
            (.seq (.store "stkP" (.var "top") (.lit 0))
              (.seq (.store "mark" (.var "eu") (.lit 1))
                (.seq (.assign "top" (.add (.var "top") (.lit 1)))
                  (.assign "bud" (.sub (.var "bud") (.lit 1))))))))))

/-- Backtrack: answer `0` on an empty stack, flip a phase-`0` top frame
to its second branch, or pop a phase-`1` one. -/
def backtrackBody : Com :=
  .ite (.eq (.var "top") (.lit 0))
    (.seq (.assign "ans" (.lit 0)) (.assign "mode" (.lit 2)))
    (.seq (.assign "pu" (.get "stkU" (.sub (.var "top") (.lit 1))))
      (.seq (.assign "pv" (.get "stkV" (.sub (.var "top") (.lit 1))))
        (.ite (.eq (.get "stkP" (.sub (.var "top") (.lit 1))) (.lit 0))
          (.seq (.store "mark" (.var "pu") (.lit 0))
            (.seq (.store "mark" (.var "pv") (.lit 1))
              (.seq (.store "stkP" (.sub (.var "top") (.lit 1)) (.lit 1))
                (.assign "mode" (.lit 0)))))
          (.seq (.store "mark" (.var "pv") (.lit 0))
            (.seq (.assign "bud" (.add (.var "bud") (.lit 1)))
              (.assign "top" (.sub (.var "top") (.lit 1))))))))

/-- One turn of the outer loop, dispatched on the mode. -/
def outerBody : Com :=
  .ite (.eq (.var "mode") (.lit 0)) descendBody backtrackBody

/-- The whole algorithm: read the encoding and the budget, search,
write the answer. -/
def vcCom : Com :=
  .seq (.read "n")
    (.seq (.read "m")
      (.seq (.assign "len" (.add (.var "n") (.lit 1)))
        (.seq (readLoop "off" "len")
          (.seq (.assign "m2" (.add (.var "m") (.var "m")))
            (.seq (readLoop "tgt" "m2")
              (.seq (.read "bud")
                (.seq (.while (.lt (.var "mode") (.lit 2)) outerBody)
                  (.write (.var "ans")))))))))

/-- Eighteen scalars, the two arrays of the encoding, the mark array,
the three stack arrays, four temporaries. -/
def layout : Layout :=
  ⟨["n", "m", "m2", "len", "i", "t", "j", "u", "w", "found", "eu", "ev",
    "top", "bud", "mode", "ans", "pu", "pv"],
   ["off", "tgt", "mark", "stkU", "stkV", "stkP"], 4⟩

/-- The machine program. -/
def vcProgram : Program := compileProgram layout vcCom

theorem vcCom_ok : Com.Ok layout vcCom := by
  simp [vcCom, readLoop, outerBody, descendBody, backtrackBody, scan, scanBody,
    layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-! ### The program, run

House discipline: the compiled machine program is run before anything
is proved about it. The instances below cover both answers at the
boundary budgets, the `k = 0` cases, the empty graph, and one malformed
word, which must merely not diverge. -/

/-- Run `vcProgram` on an encoded instance. -/
def test (x : List ℕ) : Option (List ℕ × ℕ) := runOut 1000000 vcProgram (initState x) 0

-- the triangle: cover number two, so `no` at budgets zero and one, `yes` at two
#guard test ([3, 3, 0, 2, 4, 6, 1, 2, 0, 2, 0, 1] ++ [0]) = some ([0], 509)
#guard test ([3, 3, 0, 2, 4, 6, 1, 2, 0, 2, 0, 1] ++ [1]) = some ([0], 1539)
#guard test ([3, 3, 0, 2, 4, 6, 1, 2, 0, 2, 0, 1] ++ [2]) = some ([1], 1662)
-- the star on three leaves: its center is a cover
#guard test ([4, 3, 0, 3, 4, 5, 6, 1, 2, 3, 0, 0, 0] ++ [1]) = some ([1], 1244)
-- the path on four vertices: cover number two
#guard test ([4, 3, 0, 1, 3, 5, 6, 1, 0, 2, 1, 3, 2] ++ [1]) = some ([0], 1814)
#guard test ([4, 3, 0, 1, 3, 5, 6, 1, 0, 2, 1, 3, 2] ++ [2]) = some ([1], 2376)
-- no edges: the empty set is a cover, even with no budget
#guard test ([2, 0, 0, 0, 0] ++ [0]) = some ([1], 175)
-- no vertices
#guard test ([0, 0, 0] ++ [0]) = some ([1], 123)
-- a malformed word: the program merely halts (the exhausted tape stops it)
#guard test [5, 2, 0, 1, 9, 3] = some ([], 121)
