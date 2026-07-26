import Lax11.ConnectedComponents
import Lax11Proofs.Reasoning

/-!
The driver: connected components, as an IMP+ program.

The algorithm is the textbook one. Sweep the vertices in increasing
order; when a vertex is still unlabelled it is the least vertex of its
component, so start a breadth-first search from it and label everything
the search reaches with that vertex. The label array doubles as the
visited array, with `n` — not a vertex — as the marker for "unvisited",
so no second array is needed.

Two details are chosen for the sake of the cost proof rather than the
algorithm, and both are free.

*The queue is global.* It is never reset between searches: a search
leaves `head = tail` behind, and the next one continues from there. So
`tail` only ever increases, and since a vertex is enqueued only in the
step that labels it, `tail` never exceeds `n`. The quantity `n - tail`
is therefore a budget for the whole run, out of which every enqueue is
paid — with a per-search queue it would be a budget per search, and the
searches would have to be counted separately.

*Nothing is precomputed.* The input word is read once into the four
arrays in the order the tape presents it, so the reading phase is a
plain copy and the encoding stays the dumb one the concept fixes.

The cost argument, for the record, is a single potential
`c₁·(2m − scanned) + c₀·(n − tail) + c₀·(tail − head) + c₂·(n − u)`,
where `scanned` is the number of adjacency slots already looked at. One
turn of the search loop dequeues a vertex, scans its block and enqueues
some vertices: the first term pays for the scan, the second for the
enqueues, and the third gives back the one unit the dequeue itself
cost. The potential is global, so the amortization crosses the boundary
between the searches — which is exactly what a per-loop constant cannot
express, and why the while rule takes a potential.
-/

namespace Lax11Proofs.CC

open Lax11.Ram Lax11.RamComputes Lax11.GraphEncoding Lax11.ConnectedComponents
open Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning

/-! ### The program -/

/-- Read `lim` numbers off the input tape into the array `a`, where
`lim` is a scalar the loop does not touch. -/
def readLoop (a lim : String) : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var lim))
      (.seq (.read "t")
        (.seq (.store a (.var "i") (.var "t"))
          (.assign "i" (.add (.var "i") (.lit 1))))))

/-- Mark every vertex unvisited. The marker is `n`, which is not a
vertex, so the label array needs no companion. -/
def initLab : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "n"))
      (.seq (.store "lab" (.var "i") (.var "n"))
        (.assign "i" (.add (.var "i") (.lit 1)))))

/-- Look at the adjacency slot `j`: if the vertex it names is
unvisited, label it and put it on the queue. `sc` counts the slots
looked at; it exists only so that the cost potential is a function of
the scalars, and it costs one unit per slot. -/
def scanBody : Com :=
  .seq (.assign "w" (.get "tgt" (.var "j")))
    (.seq (.ite (.eq (.get "lab" (.var "w")) (.var "n"))
            (.seq (.store "lab" (.var "w") (.var "u"))
              (.seq (.store "q" (.var "tail") (.var "w"))
                (.assign "tail" (.add (.var "tail") (.lit 1)))))
            .skip)
      (.seq (.assign "sc" (.add (.var "sc") (.lit 1)))
        (.assign "j" (.add (.var "j") (.lit 1)))))

/-- Take the next vertex off the queue and scan its whole block. The
queue pointer moves *after* the scan, so that "the vertices before
`head` have been expanded" is an invariant of the scan as well. -/
def expandBody : Com :=
  .seq (.assign "v" (.get "q" (.var "head")))
    (.seq (.assign "j" (.get "off" (.var "v")))
      (.seq (.assign "jend" (.get "off" (.add (.var "v") (.lit 1))))
        (.seq (.while (.lt (.var "j") (.var "jend")) scanBody)
          (.assign "head" (.add (.var "head") (.lit 1))))))

/-- Empty the queue: the breadth-first search itself. -/
def drain : Com := .while (.lt (.var "head") (.var "tail")) expandBody

/-- One vertex of the outer sweep. An unlabelled vertex is the least of
its component, so it is labelled with itself and searched from. -/
def outerBody : Com :=
  .seq (.ite (.eq (.get "lab" (.var "u")) (.var "n"))
        (.seq (.store "lab" (.var "u") (.var "u"))
          (.seq (.store "q" (.var "tail") (.var "u"))
            (.seq (.assign "tail" (.add (.var "tail") (.lit 1)))
              drain)))
        .skip)
    (.assign "u" (.add (.var "u") (.lit 1)))

/-- Write the labels to the output tape in vertex order. -/
def writeLoop : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "n"))
      (.seq (.write (.get "lab" (.var "i")))
        (.assign "i" (.add (.var "i") (.lit 1)))))

/-- The whole algorithm: read the encoding, sweep, write the labels. -/
def ccCom : Com :=
  .seq (.read "n")
    (.seq (.read "m")
      (.seq (.assign "len" (.add (.var "n") (.lit 1)))
        (.seq (readLoop "off" "len")
         (.seq (.assign "len" (.add (.var "m") (.var "m")))
          (.seq (readLoop "tgt" "len")
          (.seq initLab
            (.seq (.assign "u" (.lit 0))
              (.seq (.assign "head" (.lit 0))
                (.seq (.assign "tail" (.lit 0))
                 (.seq (.assign "sc" (.lit 0))
                  (.seq (.while (.lt (.var "u") (.var "n")) outerBody)
                    writeLoop)))))))))))

/-- Thirteen scalars, the four arrays of the encoding, four temporaries
(the deepest expression is the condition `lab[w] = n`, which the
compiler turns into `(lab[w] - n) + (n - lab[w])`). -/
def layout : Layout :=
  ⟨["n", "m", "i", "t", "u", "v", "w", "j", "jend", "head", "tail", "len", "sc"],
   ["off", "tgt", "lab", "q"], 4⟩

/-- The machine program. -/
def ccProgram : Program := compileProgram layout ccCom

theorem ccCom_ok : Com.Ok layout ccCom := by
  simp [ccCom, readLoop, initLab, writeLoop, outerBody, drain, expandBody, scanBody,
    layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-! ### The program, run

The compiler was checked by evaluation before anything was proved,
which is how two bugs were found at P1. `runOut` runs the machine to a
halt and reports the output tape and the number of steps; the graphs
below are given in the concept's encoding, and the outputs are the
least-vertex labels. -/

/-- Run a machine program to a halt within `f` steps, reporting the
output tape and the number of steps taken. -/
def runOut : ℕ → Program → State → ℕ → Option (List ℕ × ℕ)
  | 0, _, _, _ => none
  | f + 1, p, s, k =>
      match step p s with
      | none => some (s.out, k)
      | some s' => runOut f p s' (k + 1)

/-- Run `ccProgram` on an encoded graph. -/
def test (x : List ℕ) : Option (List ℕ × ℕ) := runOut 100000 ccProgram (initState x) 0

-- no vertices
#guard test [0, 0, 0] = some ([], 97)
-- one vertex, no edges
#guard test [1, 0, 0, 0] = some ([0], 292)
-- two vertices, the edge between them
#guard test [2, 1, 0, 1, 2, 1, 0] = some ([0, 0], 634)
-- two vertices, no edge
#guard test [2, 0, 0, 0, 0] = some ([0, 1], 487)
-- three vertices, the edge 1-2
#guard test [3, 1, 0, 0, 1, 2, 2, 1] = some ([0, 1, 1], 829)
-- four vertices, the edges 0-2 and 1-3: two components, interleaved
#guard test [4, 2, 0, 1, 2, 3, 4, 2, 3, 0, 1] = some ([0, 1, 0, 1], 1171)
-- five vertices, the path 0-1-2-3 and an isolated vertex
#guard test [5, 3, 0, 1, 3, 5, 6, 6, 1, 0, 2, 1, 3, 2] = some ([0, 0, 0, 0, 4], 1513)
-- four vertices, a triangle and an isolated vertex
#guard test [4, 3, 0, 2, 4, 6, 6, 1, 2, 0, 2, 0, 1] = some ([0, 0, 0, 3], 1327)

end Lax11Proofs.CC
