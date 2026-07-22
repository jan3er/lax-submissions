import Lax2Proofs.Source.TwinWidth.Order.Divisions
import Mathlib.Data.Matrix.Basic

/-!
# Grid minors of Boolean matrices

This file defines the grid-minor notion used in the Marcus-Tardos ingredient of
the twin-width grid theorem.  A `t`-grid minor in a Boolean matrix is a pair of
`t`-divisions of rows and columns such that every zone contains a `true` entry.
-/

namespace Lax2Proofs.TwinWidth
namespace Matrix

/-- The set of `true` entries of a Boolean matrix. -/
noncomputable def oneEntries {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    Finset (Fin n × Fin m) :=
  by
    classical
    exact Finset.univ.filter fun p : Fin n × Fin m => M p.1 p.2 = true

/-- A cell of a divided Boolean matrix contains a `true` entry. -/
def CellHasOne {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∃ r ∈ R.part i, ∃ c ∈ C.part j, M r c = true

/-- A Boolean matrix has a `t`-grid minor if there are row and column
`t`-divisions such that every zone contains a `true` entry.

The `t = 0` convention is vacuous, matching the empty family of zones.
-/
def HasGridMinor {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool) (t : ℕ) : Prop :=
  t = 0 ∨
    ∃ R : Division n t, ∃ C : Division m t,
      ∀ i j : Fin t, CellHasOne M R C i j

@[simp] theorem hasGridMinor_zero {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    HasGridMinor M 0 :=
  Or.inl rfl

theorem mem_oneEntries_iff {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (p : Fin n × Fin m) :
    p ∈ oneEntries M ↔ M p.1 p.2 = true := by
  classical
  simp [oneEntries]

/-- The one-part division of a nonempty finite interval. -/
def oneDivision (n : ℕ) (hn : 0 < n) : Division n 1 where
  part := fun _ => Finset.univ
  part_nonempty := by
    intro _
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  part_disjoint := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  part_cover := by
    intro x
    exact ⟨0, Finset.mem_univ x⟩
  part_convex := by
    intro _ _ _ _ _ _ _ _
    exact Finset.mem_univ _
  part_ordered := by
    intro i j hij
    exact (not_lt_of_ge (Subsingleton.elim i j ▸ le_rfl) hij).elim

/-- A nonempty Boolean matrix with at least one true entry has a `1`-grid
minor. -/
theorem hasGridMinor_one_of_true_entry {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    {r : Fin n} {c : Fin m} (h : M r c = true) :
    HasGridMinor M 1 := by
  refine Or.inr ?_
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le r.1) r.2
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le c.1) c.2
  refine ⟨oneDivision n hn, oneDivision m hm, ?_⟩
  intro i j
  exact ⟨r, Finset.mem_univ r, c, Finset.mem_univ c, h⟩

/-- If the set of true entries is nonempty, then the matrix has a `1`-grid
minor. -/
theorem hasGridMinor_one_of_oneEntries_nonempty {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (h : (oneEntries M).Nonempty) :
    HasGridMinor M 1 := by
  rcases h with ⟨p, hp⟩
  exact hasGridMinor_one_of_true_entry M ((mem_oneEntries_iff M p).mp hp)

end Matrix
end Lax2Proofs.TwinWidth
