import Lax2Proofs.Source.TwinWidth.Matrix.MixedWitness
import Lax2Proofs.Source.TwinWidth.Matrix.Partition

/-!
# Mixed zones, mixed cuts, and mixed value

This file formalizes the local quantities from Section 5.6.  Mixed values are
defined for one side of a division at a time: a column set measured against a
row division, and dually a row set measured against a column division.
-/

namespace Lax2Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

/-- The mixed zones of a column set on a row division. -/
noncomputable def rowMixedZones {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Finset (Fin m)) : Finset (Fin k) :=
  by
    classical
    exact Finset.univ.filter fun i => ZoneMixed M (R.part i) C

/-- The mixed zones of a row set on a column division. -/
noncomputable def colMixedZones {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m k) : Finset (Fin k) :=
  by
    classical
    exact Finset.univ.filter fun j => ZoneMixed M R (C.part j)

/-- The two-row cut between consecutive row parts is vertical on a column set
if the last row of the lower part and first row of the upper part agree on all
columns of the set. -/
def RowCutVertical {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) : Prop :=
  ∀ ⦃c : Fin m⦄, c ∈ C →
    M (R.last i.castSucc) c = M (R.first i.succ) c

/-- The two-row cut between consecutive row parts is horizontal on a column set
if each of the two boundary rows is constant on that column set. -/
def RowCutHorizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) : Prop :=
  (∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C → c₂ ∈ C →
      M (R.last i.castSucc) c₁ = M (R.last i.castSucc) c₂) ∧
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C → c₂ ∈ C →
      M (R.first i.succ) c₁ = M (R.first i.succ) c₂

/-- A mixed row cut. -/
def RowCutMixed {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) : Prop :=
  ¬ RowCutVertical M R C i ∧ ¬ RowCutHorizontal M R C i

/-- The mixed row cuts of a column set on a row division. -/
noncomputable def rowMixedCuts {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) : Finset (Fin k) :=
  by
    classical
    exact Finset.univ.filter fun i => RowCutMixed M R C i

/-- Column-cut verticality, dual to `RowCutVertical`. -/
def ColCutVertical {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) : Prop :=
  (∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R → r₂ ∈ R →
      M r₁ (C.last j.castSucc) = M r₂ (C.last j.castSucc)) ∧
    ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R → r₂ ∈ R →
      M r₁ (C.first j.succ) = M r₂ (C.first j.succ)

/-- Column-cut horizontality, dual to `RowCutHorizontal`. -/
def ColCutHorizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R →
    M r (C.last j.castSucc) = M r (C.first j.succ)

/-- A mixed column cut. -/
def ColCutMixed {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) : Prop :=
  ¬ ColCutVertical M R C j ∧ ¬ ColCutHorizontal M R C j

/-- The mixed column cuts of a row set on a column division. -/
noncomputable def colMixedCuts {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) : Finset (Fin k) :=
  by
    classical
    exact Finset.univ.filter fun j => ColCutMixed M R C j

/-- Mixed value of a column set on a row division with `k + 1` parts. -/
noncomputable def rowMixedValue {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) : ℕ :=
  (rowMixedZones M R C).card + (rowMixedCuts M R C).card

/-- Mixed value of a row set on a column division with `k + 1` parts. -/
noncomputable def colMixedValue {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) : ℕ :=
  (colMixedZones M R C).card + (colMixedCuts M R C).card

@[simp] theorem rowMixedValue_castIndex {n m k l : ℕ}
    (h : k = l) (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) :
    rowMixedValue M (Division.castIndex (by omega : k + 1 = l + 1) R) C =
      rowMixedValue M R C := by
  subst l
  simp [Division.castIndex]

@[simp] theorem colMixedValue_castIndex {n m k l : ℕ}
    (h : k = l) (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) :
    colMixedValue M R (Division.castIndex (by omega : k + 1 = l + 1) C) =
      colMixedValue M R C := by
  subst l
  simp [Division.castIndex]

/-- Mixed zones and mixed cuts of a column set on a row division, packaged as
one finite set.  This is useful for injection proofs showing that fusions do
not increase mixed value. -/
noncomputable def rowMixedItems {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) :
    Finset (Sum (Fin (k + 1)) (Fin k)) := by
  classical
  exact (rowMixedZones M R C).map ⟨Sum.inl, by intro a b h; simpa using h⟩ ∪
    (rowMixedCuts M R C).map ⟨Sum.inr, by intro a b h; simpa using h⟩

@[simp] theorem mem_rowMixedItems_zone {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin (k + 1)) :
    Sum.inl i ∈ rowMixedItems M R C ↔ ZoneMixed M (R.part i) C := by
  classical
  simp [rowMixedItems, rowMixedZones]

@[simp] theorem mem_rowMixedItems_cut {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) :
    Sum.inr i ∈ rowMixedItems M R C ↔ RowCutMixed M R C i := by
  classical
  simp [rowMixedItems, rowMixedCuts]

theorem rowMixedItems_card {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) :
    (rowMixedItems M R C).card = rowMixedValue M R C := by
  classical
  rw [rowMixedItems, Finset.card_union_of_disjoint]
  · simp [rowMixedValue]
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp at hx hy
    rcases hx with ⟨a, _ha, hxa⟩
    rcases hy with ⟨b, _hb, hyb⟩
    cases hxa.trans hyb.symm

/-- Mixed zones and mixed cuts of a row set on a column division, packaged as
one finite set. -/
noncomputable def colMixedItems {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) :
    Finset (Sum (Fin (k + 1)) (Fin k)) := by
  classical
  exact (colMixedZones M R C).map ⟨Sum.inl, by intro a b h; simpa using h⟩ ∪
    (colMixedCuts M R C).map ⟨Sum.inr, by intro a b h; simpa using h⟩

@[simp] theorem mem_colMixedItems_zone {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin (k + 1)) :
    Sum.inl j ∈ colMixedItems M R C ↔ ZoneMixed M R (C.part j) := by
  classical
  simp [colMixedItems, colMixedZones]

@[simp] theorem mem_colMixedItems_cut {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) :
    Sum.inr j ∈ colMixedItems M R C ↔ ColCutMixed M R C j := by
  classical
  simp [colMixedItems, colMixedCuts]

theorem colMixedItems_card {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) :
    (colMixedItems M R C).card = colMixedValue M R C := by
  classical
  rw [colMixedItems, Finset.card_union_of_disjoint]
  · simp [colMixedValue]
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp at hx hy
    rcases hx with ⟨a, _ha, hxa⟩
    rcases hy with ⟨b, _hb, hyb⟩
    cases hxa.trans hyb.symm

end Matrix
end Lax2Proofs.TwinWidth
