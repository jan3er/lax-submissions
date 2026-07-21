import Lax2Proofs.Source.TwinWidth.Matrix.DivisionSequence

/-!
# Definitions for matrix Theorem 10

This file contains only the public predicates and numerical bounds used to
state the matrix form of Theorem 10.  Proofs live in `Theorem10.lean`; contract
wrappers for the public theorem statements live in `Theorem10Contract.lean`.
-/

namespace Lax2Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

/-- The matrix first-item bound predicted by Theorem 10: bounded matrix
twin-width forces bounded matrix mixed number.  The constant follows the
project's current mixed-minor convention. -/
def theorem10MatrixMixedNumberBound (d : ℕ) : ℕ :=
  2 * d + 2

namespace MatrixDivision

/-- Column parts on which a fixed row part is nonconstant in a division.

This is the error notion used in the first item of Theorem 10: an error zone is
any nonconstant zone, not only a mixed zone. -/
noncomputable def nonconstantRowErrorSet {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1)) :
    Finset (Fin (D.colCuts + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j =>
      ¬ ZoneConstant M (D.rowDiv.part i) (D.colDiv.part j)

/-- Row parts on which a fixed column part is nonconstant in a division.

This is the error notion used in the first item of Theorem 10: an error zone is
any nonconstant zone, not only a mixed zone. -/
noncomputable def nonconstantColErrorSet {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1)) :
    Finset (Fin (D.rowCuts + 1)) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      ¬ ZoneConstant M (D.rowDiv.part i) (D.colDiv.part j)

/-- A division has error value at most `t` when each row part and each column
part sees at most `t` nonconstant zones. -/
def NonconstantErrorValueAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (t : ℕ) : Prop :=
  (∀ i, (nonconstantRowErrorSet M D i).card ≤ t) ∧
    ∀ j, (nonconstantColErrorSet M D j).card ≤ t

end MatrixDivision

/-- A concrete division sequence all of whose divisions have nonconstant error
value at most `d`.  This formalizes the `d`-twin-ordered matrix hypothesis used
in the first item of Theorem 10. -/
structure BoundedErrorValueDivisionSequence {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) where
  /-- Number of fusions. -/
  stepCount : ℕ
  /-- Division at each time. -/
  division : ℕ → MatrixDivision n m
  /-- The first division is the finest one. -/
  starts : MatrixDivision.IsFinest (division 0)
  /-- The final division is the coarsest one. -/
  ends : MatrixDivision.IsCoarsest (division stepCount)
  /-- Consecutive divisions are related by one row or column fusion. -/
  step_fuses :
    ∀ s, s < stepCount → MatrixDivision.HasExactFusion (division s) (division (s + 1))
  /-- Every division in the sequence has bounded nonconstant error value. -/
  errorValue_le :
    ∀ s, s ≤ stepCount → MatrixDivision.NonconstantErrorValueAtMost M (division s) d

/-- A matrix is `d`-twin-ordered when its current row and column orders have a
division sequence of nonconstant error value at most `d`. -/
def MatrixTwinOrderedAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) : Prop :=
  Nonempty (BoundedErrorValueDivisionSequence M d)

/-- Matrix-level form of the first item of Theorem 10: a `d`-twin-ordered
matrix has mixed number bounded by a function of `d`. -/
def MatrixMixedNumberBoundedByTwinOrdered (f : ℕ → ℕ) : Prop :=
  ∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
    MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ f d

/-- Public matrix-level first item of Theorem 10: bounded matrix twin-width
forces bounded matrix mixed number. -/
def MatrixMixedNumberBoundedByMatrixTwinWidth (f : ℕ → ℕ) : Prop :=
  ∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
    MatrixTwinWidthAtMost M d → matrixMixedNumber M ≤ f d

/-- A concrete contraction path between two prescribed matrix partitions. -/
structure MatrixContractionPath {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ)
    (P₀ P₁ : MatrixPartition n m) where
  /-- Number of contractions in the path. -/
  stepCount : ℕ
  /-- Partition at each time. -/
  partition : ℕ → MatrixPartition n m
  /-- The path starts at `P₀`. -/
  starts : partition 0 = P₀
  /-- The path ends at `P₁`. -/
  ends : partition stepCount = P₁
  /-- Each step contracts one row part or one column part. -/
  step_contracts :
    ∀ i, i < stepCount → MatrixPartition.IsContraction (partition i) (partition (i + 1))
  /-- Every partition in the path has bounded error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

/-- A sequence of partitions where each term has error at most `t` and
`r`-refines the next one.

This is the hypothesis of Lemma 8 in the matrix language. -/
structure BoundedErrorRefinementPartitionSequence {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (r t : ℕ) where
  /-- Number of coarse-graining steps. -/
  stepCount : ℕ
  /-- Partition at each time. -/
  partition : ℕ → MatrixPartition n m
  /-- The first partition is finest. -/
  starts : MatrixPartition.IsFinest (partition 0)
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Each partition boundedly refines the next one. -/
  step_rrefines :
    ∀ i, i < stepCount → MatrixPartition.RRefines (partition i) (partition (i + 1)) r
  /-- Every partition in the sequence has bounded nonconstant error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) t

/-- The mixed-value bound obtained from Marcus--Tardos constants in the second
item of Theorem 10.  The argument is `matrixMixedNumber M`; the proof applies
Lemma 13 at the next mixed-minor order, which is mixed-free by maximality. -/
def theorem10MixedValueBound (c : ℕ → ℕ) (k : ℕ) : ℕ :=
  lemma13MixedValueBound c (k + 1)

/-- The refinement blow-up in the second item of Theorem 10 for alphabet size
`a`.

If a division sequence has mixed value at most `d`, the paper refines it into
a bounded-refinement partition sequence and obtains a contraction sequence of
nonconstant error value bounded by this expression.  Combined with the
formalized Lemma 13 constant, this has the same elementary finite-alphabet
shape as Theorem 10, with explicit constants from the Lean proof. -/
def theorem10AlphabetErrorRefinementBound (a d : ℕ) : ℕ :=
  2 * d * a ^ (2 * (d + 1))

/-- Boolean-alphabet specialization of `theorem10AlphabetErrorRefinementBound`. -/
def theorem10ErrorRefinementBound (d : ℕ) : ℕ :=
  theorem10AlphabetErrorRefinementBound 2 d

/-- The explicit bound used in the final, unconditional second item of
Theorem 10.  It applies the refinement blow-up to Lemma 13's mixed-value bound
at one more than the matrix mixed number, with the formalized Marcus--Tardos
constants. -/
def theorem10AlphabetMatrixTwinWidthBound (a k : ℕ) : ℕ :=
  theorem10AlphabetErrorRefinementBound a (theorem10MixedValueBound marcusTardosConstant k)

/-- Boolean-alphabet specialization of `theorem10AlphabetMatrixTwinWidthBound`. -/
def theorem10MatrixTwinWidthBound (k : ℕ) : ℕ :=
  theorem10AlphabetMatrixTwinWidthBound 2 k

end Matrix
end Lax2Proofs.TwinWidth
