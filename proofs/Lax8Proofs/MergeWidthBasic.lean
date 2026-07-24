import Lax8.MergeWidth

/-!
# Basic facts about merge sequences and merge-width

This file provides:
* the existence of a merge sequence for every finite simple graph
  (`MergeWidth.MergeSeq.trivial`), so that `mergeWidth` is a genuine minimum;
* the characterisation `mergeWidth r G ≤ k ↔ ∃ S, S.width r ≤ k`.
-/

namespace Lax8Proofs

open Lax8.MergeWidth

open scoped Classical

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The trivial merge sequence: singletons, then everything in one part, with
all pairs resolved.  This shows every finite graph has a merge sequence. -/
def MergeSeq.trivial (G : SimpleGraph V) : MergeSeq G where
  length := 2
  one_le_length := by norm_num
  part i := if i ≤ 1 then ⊥ else ⊤
  resolved _ := ⊤
  part_one := by simp
  part_length := by norm_num
  part_mono := by
    intro i j hi hij hj
    by_cases h1 : i ≤ 1
    · simp only [h1, if_true]
      exact bot_le
    · simp only [h1, if_false]
      have : ¬ j ≤ 1 := by omega
      simp only [this, if_false, le_refl]
  resolved_mono := by intro i j _ _ _; exact le_refl _
  uniform := by
    intro i _ _ x x' y y' _ _ hxy _ hnr _
    exact absurd (by simpa [SimpleGraph.top_adj] using hxy) hnr

instance : Nonempty (MergeSeq G) := ⟨MergeSeq.trivial G⟩

/-- The set of achievable radius-`r` widths is nonempty. -/
theorem widthSet_nonempty (r : ℕ) : {w | ∃ S : MergeSeq G, S.width r = w}.Nonempty :=
  ⟨(MergeSeq.trivial G).width r, MergeSeq.trivial G, rfl⟩

/-- `mergeWidth r G ≤ k` iff there is a merge sequence of radius-`r` width `≤ k`. -/
theorem mergeWidth_le_iff (r k : ℕ) :
    mergeWidth r G ≤ k ↔ ∃ S : MergeSeq G, S.width r ≤ k := by
  constructor
  · intro h
    have hmem : mergeWidth r G ∈ {w | ∃ S : MergeSeq G, S.width r = w} :=
      Nat.sInf_mem (widthSet_nonempty r)
    obtain ⟨S, hS⟩ := hmem
    exact ⟨S, hS ▸ h⟩
  · rintro ⟨S, hS⟩
    exact le_trans (Nat.sInf_le ⟨S, rfl⟩) hS

/-! ### Resolved-ball helpers -/

omit [Fintype V] in
theorem mem_resolvedBall_self (H : SimpleGraph V) (r : ℕ) (v : V) :
    v ∈ resolvedBall H r v :=
  ⟨SimpleGraph.Walk.nil, by simp⟩

omit [Fintype V] in
theorem mem_resolvedBall_of_adj (H : SimpleGraph V) {r : ℕ} (hr : 1 ≤ r) {v u : V}
    (h : H.Adj v u) : u ∈ resolvedBall H r v :=
  ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil, by simpa using hr⟩

omit [Fintype V] in
theorem mem_resolvedBall_two (H : SimpleGraph V) {v c u : V}
    (h1 : H.Adj v c) (h2 : H.Adj c u) : u ∈ resolvedBall H 2 v :=
  ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil), by simp⟩

omit [Fintype V] in
theorem resolvedBall_mono (H : SimpleGraph V) {r r' : ℕ} (h : r ≤ r') (v : V) :
    resolvedBall H r v ⊆ resolvedBall H r' v := by
  rintro u ⟨w, hw⟩; exact ⟨w, hw.trans h⟩

omit [Fintype V] in
/-- Reusability lemma from the uniformity axiom: if `x, y` lie in the same part
of step `i` and `a` is adjacent to exactly one of them, then one of `ax`, `ay`
is a resolved pair. -/
theorem uniform_resolved {G : SimpleGraph V} (S : MergeSeq G) {i : ℕ} (hi1 : 1 ≤ i)
    (hilen : i ≤ S.length) {a x y : V} (hxy : (S.part i).r x y) (hax : a ≠ x)
    (hay : a ≠ y) (hne : G.Adj a x ≠ G.Adj a y) :
    (S.resolved i).Adj a x ∨ (S.resolved i).Adj a y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact hne (propext (S.uniform hi1 hilen (Setoid.refl' _ a) hxy hax hay h1 h2))

/-! ### Copying a merge sequence with different resolved sets -/

/-- Replace the resolved sets of `S` by another monotone, uniform family `R'`
(keeping the same partitions). -/
def MergeSeq.copyResolved (S : MergeSeq G) (R' : ℕ → SimpleGraph V)
    (hmono : ∀ ⦃i j⦄, 1 ≤ i → i ≤ j → j ≤ S.length → R' i ≤ R' j)
    (huniform : ∀ ⦃i⦄, 1 ≤ i → i ≤ S.length → ∀ ⦃x x' y y' : V⦄,
      (S.part i).r x x' → (S.part i).r y y' → x ≠ y → x' ≠ y' →
      ¬ (R' i).Adj x y → ¬ (R' i).Adj x' y' → (G.Adj x y ↔ G.Adj x' y')) :
    MergeSeq G where
  length := S.length
  one_le_length := S.one_le_length
  part := S.part
  resolved := R'
  part_one := S.part_one
  part_length := S.part_length
  part_mono := S.part_mono
  resolved_mono := hmono
  uniform := huniform

@[simp] theorem copyResolved_part (S : MergeSeq G) (R' : ℕ → SimpleGraph V)
    (hmono huniform) :
    (Lax8Proofs.MergeSeq.copyResolved S R' hmono huniform).part = S.part := rfl

@[simp] theorem copyResolved_resolved (S : MergeSeq G) (R' : ℕ → SimpleGraph V)
    (hmono huniform) :
    (Lax8Proofs.MergeSeq.copyResolved S R' hmono huniform).resolved = R' := rfl

@[simp] theorem copyResolved_length (S : MergeSeq G) (R' : ℕ → SimpleGraph V)
    (hmono huniform) :
    (Lax8Proofs.MergeSeq.copyResolved S R' hmono huniform).length = S.length := rfl

/-- Shrinking the resolved sets (same partitions) does not increase the width. -/
theorem width_copyResolved_le (S : MergeSeq G) (R' : ℕ → SimpleGraph V)
    (hmono huniform) (hle : ∀ i, R' i ≤ S.resolved i) (r : ℕ) :
    (Lax8Proofs.MergeSeq.copyResolved S R' hmono huniform).width r ≤ S.width r := by
  unfold MergeSeq.width
  apply Finset.sup_le
  intro i hi
  apply Finset.sup_le
  intro v _
  have hnum :
      (Lax8Proofs.MergeSeq.copyResolved S R' hmono huniform).numAccessible r i v ≤
        S.numAccessible r i v := by
    unfold MergeSeq.numAccessible
    apply Set.ncard_le_ncard
    · apply Set.image_mono
      rintro u ⟨w, hw⟩
      exact ⟨w.mapLe (hle i), by
        change (w.map (SimpleGraph.Hom.ofLE (hle i))).length ≤ r
        simpa only [SimpleGraph.Walk.length_map] using hw⟩
    · exact Set.toFinite _
  refine le_trans hnum ?_
  refine Finset.le_sup_of_le (b := i) ?_ (Finset.le_sup (Finset.mem_univ v))
  simpa using hi

end Lax8Proofs
