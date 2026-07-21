import Lax2Proofs.Source.TwinWidth.Matrix.Cell

/-!
# Mixed minors of matrices

This file defines `HasMixedMinor`.  The `k = 0` convention is intentionally
vacuous: every matrix has a `0`-mixed minor, witnessed by the empty family of
cells.  Positive mixed minors require concrete row and column divisions.
-/

namespace Lax2Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

/-- A matrix has a `k`-mixed minor if it admits row and column
`k`-divisions whose every cell is mixed. -/
def HasMixedMinor {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (k : ℕ) : Prop :=
  k = 0 ∨
    ∃ R : Division n k, ∃ C : Division m k,
      ∀ i j : Fin k, CellMixed M R C i j

@[simp] theorem hasMixedMinor_zero {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) : HasMixedMinor M 0 :=
  Or.inl rfl

/-- A mixed minor cannot have order larger than either matrix dimension. -/
theorem hasMixedMinor_le_min_card {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (h : HasMixedMinor M k) : k ≤ min n m := by
  rcases h with rfl | h
  · exact Nat.zero_le _
  · rcases h with ⟨R, C, _⟩
    exact le_min (Division.card_parts_le R) (Division.card_parts_le C)

end Matrix
end Lax2Proofs.TwinWidth
