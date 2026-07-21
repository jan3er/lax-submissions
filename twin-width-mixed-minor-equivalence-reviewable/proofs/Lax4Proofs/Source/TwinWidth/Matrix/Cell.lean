import Lax4Proofs.Source.TwinWidth.Order.Divisions
import Mathlib.Data.Matrix.Basic

/-!
# Cells of divided matrices

Cells are the submatrices induced by a row division and a column division.  The
paper's mixed-minor notion says that a cell is mixed when it is neither vertical
nor horizontal.
-/

namespace Lax4Proofs.TwinWidth
namespace Matrix

open TwinWidth

variable {α : Type*}

/-- A cell is vertical when each of its columns is constant on the row part. -/
def CellVertical {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R.part i → r₂ ∈ R.part i →
    ∀ ⦃c : Fin m⦄, c ∈ C.part j → M r₁ c = M r₂ c

/-- A cell is horizontal when each of its rows is constant on the column part. -/
def CellHorizontal {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R.part i →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C.part j → c₂ ∈ C.part j →
      M r c₁ = M r c₂

/-- A cell is mixed when it is neither vertical nor horizontal, matching
Section 5 of the first twin-width paper. -/
def CellMixed {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ¬ CellVertical M R C i j ∧ ¬ CellHorizontal M R C i j

theorem cellMixed_iff_not_vertical_and_not_horizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    CellMixed M R C i j ↔ ¬ CellVertical M R C i j ∧ ¬ CellHorizontal M R C i j :=
  Iff.rfl

end Matrix
end Lax4Proofs.TwinWidth
