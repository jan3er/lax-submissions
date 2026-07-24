import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Lemma 12 of DMMPT26 — Lemma 10 of arXiv:2311.18740 (FOCS'24): in a
bipartite graph with no isolated vertices there are subsets `X' ⊆ X`
and `Y' ⊆ Y` with `|Y'| ≥ |Y| / (150 (ln |X| + 1))` such that every
vertex of `Y'` has exactly one neighbor in `X'`.

Stated for an abstract relation between two finsets — the machinery
applies it to the merge relation `VPos`/`VNeg` between a vertex set and
a family of traces. The paper's denominator `150 ln |X|` is replaced by
`150 (ln |X| + 1)`, which the same proof delivers and which remains
meaningful at `|X| = 1` (there the statement is witnessed by
`X' := X`, `Y' := Y`).

Proof plan (arXiv:2311.18740, Lemma 10): bucket the `Y`-degrees by
powers of `1.1`, keep a bucket `Y₀` carrying a `1 / (25 (ln |X| + 1))`
fraction of `Y`, sample each `x ∈ X` independently with probability
`1/d` for the bucket degree `d`, and combine `(1 - 1/d)^d ≥ 1/6`-type
estimates with Markov's inequality; over the finite cube this is
counting, no measure theory. -/

namespace Lax5Proofs.Sampling

/-- Lemma 12 of DMMPT26: unique-neighbor subsets in bipartite graphs
without isolated vertices. -/
theorem exists_unique_neighbor_subsets {α β : Type*}
    (X : Finset α) (Y : Finset β) (R : α → β → Prop)
    (hX : ∀ x ∈ X, ∃ y ∈ Y, R x y) (hY : ∀ y ∈ Y, ∃ x ∈ X, R x y) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y,
      (Y.card : ℝ) ≤ 150 * (Real.log X.card + 1) * Y'.card ∧
      ∀ y ∈ Y', ∃! x, x ∈ X' ∧ R x y := by
  sorry

end Lax5Proofs.Sampling
