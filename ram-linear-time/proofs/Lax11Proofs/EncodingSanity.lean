import Lax11.GraphEncoding
import Mathlib.Tactic

/-!
Sanity check for the graph encoding: a concrete word is exhibited as
the encoding of a concrete graph, so that `EncodesGraph` is known to be
satisfiable and the index arithmetic of the header, the offsets and the
target array is known to line up.

Nothing here is a proof of a submitted statement; this is a smoke test
of the concept surface.
-/

namespace Lax11Proofs.EncodingSanity

open Lax11.GraphEncoding

/-- The compressed sparse row word of the one-edge graph on two
vertices: two vertices, one edge, the offsets `0, 1, 2`, and the target
array listing the edge from both of its endpoints. -/
def edgeWord : List ℕ := [2, 1, 0, 1, 2, 1, 0]

/-- The word encodes the complete graph on two vertices, that is, the
graph with the single edge `0 — 1`. -/
theorem encodesGraph_edgeWord : EncodesGraph edgeWord 2 ⊤ where
  vertexCount_eq := rfl
  length_eq := rfl
  offset_zero := rfl
  offset_last := rfl
  offset_mono := by intro i hi; interval_cases i <;> decide
  target_lt := by
    intro j hj
    have hj : j < 2 := hj
    interval_cases j <;> decide
  adj_iff := by
    intro u v
    fin_cases u <;> fin_cases v <;>
      simp [edgeWord, target, offset, vertexCount] <;>
      first
        | exact ⟨1, by decide⟩
        | (intro j h1 h2; interval_cases j; decide)

end Lax11Proofs.EncodingSanity
