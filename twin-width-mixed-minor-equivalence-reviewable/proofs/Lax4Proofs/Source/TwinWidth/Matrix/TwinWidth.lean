import Lax4Proofs.Source.TwinWidth.Matrix.MixedValue
import Lax4Proofs.Source.TwinWidth.Matrix.MixedNumber

/-!
# Twin-width of matrices via partition sequences

This file records the Section 5.2 partition-sequence definition of matrix
twin-width.  The definition is intentionally kept in terms of the already
formalized `MatrixPartition` and `ErrorValueAtMost` predicates.
-/

namespace Lax4Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

namespace MatrixPartition

/-- A matrix partition is finest if every row and column part is a singleton
and every singleton occurs. -/
def IsFinest {n m : ℕ} (P : MatrixPartition n m) : Prop :=
  (∀ ⦃R⦄, R ∈ P.rowParts → ∃ r : Fin n, R = {r}) ∧
    (∀ r : Fin n, ({r} : Finset (Fin n)) ∈ P.rowParts) ∧
      (∀ ⦃C⦄, C ∈ P.colParts → ∃ c : Fin m, C = {c}) ∧
        ∀ c : Fin m, ({c} : Finset (Fin m)) ∈ P.colParts

/-- A matrix partition is coarsest if there is at most one row part and at most
one column part.  Empty dimensions are handled by the `≤ 1` convention. -/
def IsCoarsest {n m : ℕ} (P : MatrixPartition n m) : Prop :=
  P.rowParts.card ≤ 1 ∧ P.colParts.card ≤ 1

end MatrixPartition

/-- A concrete matrix contraction sequence of error value at most `d`. -/
structure MatrixContractionSequence {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) where
  /-- Number of partition contractions. -/
  stepCount : ℕ
  /-- Partition at each time. -/
  partition : ℕ → MatrixPartition n m
  /-- The first partition is the singleton partition. -/
  starts : MatrixPartition.IsFinest (partition 0)
  /-- The last partition is the coarsest partition. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Each step contracts one row part or one column part. -/
  step_contracts :
    ∀ i, i < stepCount → MatrixPartition.IsContraction (partition i) (partition (i + 1))
  /-- Every intermediate partition has error value at most `d`. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

/-- A matrix has matrix twin-width at most `d` if it has a partition
contraction sequence whose error value never exceeds `d`. -/
def MatrixTwinWidthAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) : Prop :=
  Nonempty (MatrixContractionSequence M d)

/-- A matrix is `t`-mixed-free if it has no `t`-mixed minor. -/
def MixedFree {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ) : Prop :=
  ¬ HasMixedMinor M t

/-- The matrix-level bound supplied by the second item of Theorem 10. -/
def MatrixTwinWidthBoundedByMixedNumber (f : ℕ → ℕ) : Prop :=
  ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
    MatrixTwinWidthAtMost M (f (matrixMixedNumber M))

end Matrix
end Lax4Proofs.TwinWidth
