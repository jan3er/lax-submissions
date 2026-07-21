import Lax2Proofs.Source.TwinWidth.Matrix.Cell

/-!
# Witnesses for mixed cells

This file proves the elementary witness form of a mixed cell.  A cell is mixed
iff it has a vertical disagreement and a horizontal disagreement.  The separate
corner file distinguishes paper-style adjacent corners from the weaker
non-contiguous `2 x 2` witnesses used in some algebraic proofs.
-/

namespace Lax2Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

/-- A vertical disagreement inside a divided cell. -/
def CellVerticalDisagreement {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∃ r₁ ∈ R.part i, ∃ r₂ ∈ R.part i, ∃ c ∈ C.part j, M r₁ c ≠ M r₂ c

/-- A horizontal disagreement inside a divided cell. -/
def CellHorizontalDisagreement {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∃ r ∈ R.part i, ∃ c₁ ∈ C.part j, ∃ c₂ ∈ C.part j, M r c₁ ≠ M r c₂

theorem not_cellVertical_iff_verticalDisagreement {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    ¬ CellVertical M R C i j ↔ CellVerticalDisagreement M R C i j := by
  classical
  simp [CellVertical, CellVerticalDisagreement]

theorem not_cellHorizontal_iff_horizontalDisagreement {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    ¬ CellHorizontal M R C i j ↔ CellHorizontalDisagreement M R C i j := by
  classical
  simp [CellHorizontal, CellHorizontalDisagreement]

/-- A mixed cell has exactly the two expected disagreement witnesses. -/
theorem cellMixed_iff_disagreements {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    CellMixed M R C i j ↔
      CellVerticalDisagreement M R C i j ∧ CellHorizontalDisagreement M R C i j := by
  rw [CellMixed, not_cellVertical_iff_verticalDisagreement,
    not_cellHorizontal_iff_horizontalDisagreement]

end Matrix
end Lax2Proofs.TwinWidth
