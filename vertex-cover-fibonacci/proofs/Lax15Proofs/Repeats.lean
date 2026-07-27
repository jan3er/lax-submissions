import Lax15Proofs.Residual

/-!
One encoding, kept as a standing warning to the scan.

The encoding of a graph does not have to be repetition-free: a block may
list a neighbour of a vertex several times, and the concept surface of
the earlier submission says so in as many words — that is why a graph
with an edge has encodings of every length. The word below is the
smallest witness: two vertices, one edge, and the block of vertex `0`
naming vertex `1` twice.

On it, every vertex has residual degree one — the residual graph is a
single edge, a matching, the leaf case of the search — and yet the block
of vertex `0` holds *two* slots whose targets are unmarked. So a scan
that decides to branch when a block reaches two unmarked slots branches
here, at a vertex with one residual neighbour, where the second branch
buys one unit of budget rather than two and the Fibonacci recurrence does
not hold. A scan must compare the *targets* of the unmarked slots, which
is what `ThinBlocks` is about and what `exists_two_slots_iff` certifies;
`ThinSlots`, the condition on slots rather than targets, fails here, and
with it any count of slots that is meant to be a count of edges.
-/

namespace Lax15Proofs.VC

open Lax11.GraphEncoding

/-- Two vertices, one edge, and a block that names its one neighbour
twice: `n = 2`, `m = 2`, offsets `0, 2, 4`, targets `1, 1, 0, 0`. -/
def repeatWord : List ℕ := [2, 2, 0, 2, 4, 1, 1, 0, 0]

/-- The repeating word is a legitimate encoding of the one-edge graph. -/
theorem encodesGraph_repeatWord :
    EncodesGraph repeatWord 2 (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> simp [offset, repeatWord]
  · intro j hj
    simp only [edgeCount, repeatWord, List.getD] at hj
    norm_num at hj
    interval_cases j <;> simp [target, vertexCount, repeatWord]
  · intro u v
    fin_cases u <;> fin_cases v <;>
      simp only [offset, target, vertexCount, repeatWord, List.getD] <;> constructor
    · intro h; simp at h
    · rintro ⟨j, hj, h⟩
      rcases j with _ | _ | j
      · norm_num at h
      · norm_num at h
      · norm_num at h
    · intro _; exact ⟨0, by norm_num, by norm_num⟩
    · intro _; simp
    · intro _; exact ⟨2, by norm_num, by norm_num, by norm_num⟩
    · intro _; simp
    · intro h; simp at h
    · rintro ⟨j, hj1, hj2, h⟩
      rcases j with _ | _ | _ | _ | j
      · norm_num at hj1
      · norm_num at hj1
      · norm_num at h
      · norm_num at h
      · exfalso; norm_num at hj2; omega

/-- Its residual graph at the empty marking is a matching: one edge. -/
theorem resDeg_top_le_one (v : Fin 2) : resDeg (⊤ : SimpleGraph (Fin 2)) ∅ v ≤ 1 := by
  rw [resDeg_eq_card, Finset.card_le_one]
  intro a ha b hb
  obtain ⟨ha', -⟩ := mem_resNbhd.1 ha
  obtain ⟨hb', -⟩ := mem_resNbhd.1 hb
  rw [SimpleGraph.top_adj] at ha' hb'
  refine Fin.ext ?_
  have h1 : (v : ℕ) ≠ (a : ℕ) := fun h => ha' (Fin.ext h)
  have h2 : (v : ℕ) ≠ (b : ℕ) := fun h => hb' (Fin.ext h)
  have := a.isLt
  have := b.isLt
  have := v.isLt
  omega

/-- The blocks are thin in the sense that matters — every block's
unmarked targets agree — so nothing here is a branching vertex. -/
theorem thinBlocks_repeatWord : ThinBlocks repeatWord (∅ : Finset (Fin 2)) :=
  (thinBlocks_iff encodesGraph_repeatWord).2 fun v _ => resDeg_top_le_one v

/-- And yet the block of vertex `0` holds two different slots with
unmarked targets. Counting slots is not counting neighbours. -/
theorem not_thinSlots_repeatWord : ¬ ThinSlots repeatWord (∅ : Finset (Fin 2)) := by
  intro h
  have := h 0 (by simp) 0 1 (by simp [offset, repeatWord])
    (by norm_num [offset, repeatWord]) (by simp [offset, repeatWord])
    (by norm_num [offset, repeatWord]) (by simp [markedVals]) (by simp [markedVals])
  omega

end Lax15Proofs.VC
