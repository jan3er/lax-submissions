import Lax4Proofs.Source.TwinWidth.Matrix.Cell

/-!
# Matrix partitions and error value

This file formalizes the partition-and-error language from Section 5.2 of the
first twin-width paper.  A matrix partition is a row partition and a column
partition of the underlying finite intervals.  The error value counts
nonconstant zones.  It is recorded by the predicate `ErrorValueAtMost`,
avoiding a premature commitment to a concrete maximum operator.
-/

namespace Lax4Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

/-- A finite partition of the rows and columns of an `n × m` matrix. -/
structure MatrixPartition (n m : ℕ) where
  /-- Row parts. -/
  rowParts : Finset (Finset (Fin n))
  /-- Every row part is nonempty. -/
  row_nonempty : ∀ ⦃R⦄, R ∈ rowParts → R.Nonempty
  /-- Distinct row parts are disjoint. -/
  row_disjoint : ∀ ⦃R S⦄, R ∈ rowParts → S ∈ rowParts → R ≠ S → Disjoint R S
  /-- Row parts cover all rows. -/
  row_cover : ∀ r : Fin n, ∃ R ∈ rowParts, r ∈ R
  /-- Column parts. -/
  colParts : Finset (Finset (Fin m))
  /-- Every column part is nonempty. -/
  col_nonempty : ∀ ⦃C⦄, C ∈ colParts → C.Nonempty
  /-- Distinct column parts are disjoint. -/
  col_disjoint : ∀ ⦃C D⦄, C ∈ colParts → D ∈ colParts → C ≠ D → Disjoint C D
  /-- Column parts cover all columns. -/
  col_cover : ∀ c : Fin m, ∃ C ∈ colParts, c ∈ C

namespace MatrixPartition

/-- A family of finite sets refines another if every part is contained in a
part of the latter family. -/
def PartsRefine {α : Type*} (P Q : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ P → ∃ B ∈ Q, A ⊆ B

/-- `P` `r`-refines `Q` if it refines `Q` and no part of `Q` contains more
than `r` parts of `P`. -/
def PartsRRefine {α : Type*} [DecidableEq α]
    (P Q : Finset (Finset α)) (r : ℕ) : Prop :=
  PartsRefine P Q ∧ ∀ ⦃B⦄, B ∈ Q → (P.filter fun A => A ⊆ B).card ≤ r

/-- Refinement of matrix partitions, componentwise on rows and columns. -/
def Refines {n m : ℕ} (P Q : MatrixPartition n m) : Prop :=
  PartsRefine P.rowParts Q.rowParts ∧ PartsRefine P.colParts Q.colParts

/-- Bounded refinement of matrix partitions, componentwise on rows and
columns. -/
def RRefines {n m : ℕ} (P Q : MatrixPartition n m) (r : ℕ) : Prop :=
  PartsRRefine P.rowParts Q.rowParts r ∧ PartsRRefine P.colParts Q.colParts r

/-- A row contraction merges two distinct row parts and leaves columns fixed. -/
def IsRowContraction {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]
    (P Q : MatrixPartition n m) : Prop :=
  ∃ R ∈ P.rowParts, ∃ S ∈ P.rowParts, R ≠ S ∧
    Q.rowParts = insert (R ∪ S) ((P.rowParts.erase R).erase S) ∧
    Q.colParts = P.colParts

/-- A column contraction merges two distinct column parts and leaves rows fixed. -/
def IsColContraction {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]
    (P Q : MatrixPartition n m) : Prop :=
  ∃ C ∈ P.colParts, ∃ D ∈ P.colParts, C ≠ D ∧
    Q.colParts = insert (C ∪ D) ((P.colParts.erase C).erase D) ∧
    Q.rowParts = P.rowParts

/-- A matrix partition contraction is either a row contraction or a column
contraction. -/
def IsContraction {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]
    (P Q : MatrixPartition n m) : Prop :=
  IsRowContraction P Q ∨ IsColContraction P Q

end MatrixPartition

/-- A rectangular zone is vertical if each column is constant across the row
set. -/
def ZoneVertical {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R → r₂ ∈ R →
    ∀ ⦃c : Fin m⦄, c ∈ C → M r₁ c = M r₂ c

/-- A rectangular zone is horizontal if each row is constant across the column
set. -/
def ZoneHorizontal {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C → c₂ ∈ C → M r c₁ = M r c₂

/-- A rectangular zone is mixed if it is neither vertical nor horizontal. -/
def ZoneMixed {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ¬ ZoneVertical M R C ∧ ¬ ZoneHorizontal M R C

/-- A zone is constant if all entries in the row part and column part have the
same matrix value. -/
def ZoneConstant {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R → r₂ ∈ R →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C → c₂ ∈ C → M r₁ c₁ = M r₂ c₂

/-- Column parts on which a fixed row part forms a nonconstant zone. -/
noncomputable def rowErrorSet {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (P : MatrixPartition n m) (R : Finset (Fin n)) : Finset (Finset (Fin m)) :=
  by
    classical
    exact P.colParts.filter fun C => ¬ ZoneConstant M R C

/-- Row parts on which a fixed column part forms a nonconstant zone. -/
noncomputable def colErrorSet {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (P : MatrixPartition n m) (C : Finset (Fin m)) : Finset (Finset (Fin n)) :=
  by
    classical
    exact P.rowParts.filter fun R => ¬ ZoneConstant M R C

/-- A matrix partition has error value at most `t` when every row part and
every column part sees at most `t` nonconstant zones. -/
def ErrorValueAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (P : MatrixPartition n m) (t : ℕ) : Prop :=
  (∀ ⦃R⦄, R ∈ P.rowParts → (rowErrorSet M P R).card ≤ t) ∧
    ∀ ⦃C⦄, C ∈ P.colParts → (colErrorSet M P C).card ≤ t

end Matrix
end Lax4Proofs.TwinWidth
