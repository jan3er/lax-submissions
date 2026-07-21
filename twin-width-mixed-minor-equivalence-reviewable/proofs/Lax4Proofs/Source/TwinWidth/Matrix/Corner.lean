import Lax4Proofs.Source.TwinWidth.Matrix.MixedValue

/-!
# Corners

This file separates two related notions.

* A `ZoneCorner` is the paper's notion from Section 5.5: a mixed `2 x 2`
  submatrix on adjacent rows and adjacent columns.
* A `ZoneTwoByTwoSubmatrix` is the weaker algebraic witness that a zone contains
  some mixed `2 x 2` submatrix, without an adjacency requirement.

The second notion is useful for elementary algebraic proofs about mixed zones,
but it is deliberately not called a corner.
-/

namespace Lax4Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

/-- The first index of an adjacent pair in `Fin n`, represented by a cut
position in `Fin (n - 1)`. -/
def adjacentFirst {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le n 1)⟩

/-- The second index of an adjacent pair in `Fin n`, represented by a cut
position in `Fin (n - 1)`. -/
def adjacentSecond {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1 + 1, by
    have hi : i.1 < n - 1 := i.2
    omega⟩

/-- A `2 x 2` submatrix is mixed when it is neither vertical nor horizontal. -/
def TwoByTwoMixed {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (r₁ r₂ : Fin n) (c₁ c₂ : Fin m) : Prop :=
  ((M r₁ c₁ ≠ M r₂ c₁) ∨ (M r₁ c₂ ≠ M r₂ c₂)) ∧
    ((M r₁ c₁ ≠ M r₁ c₂) ∨ (M r₂ c₁ ≠ M r₂ c₂))

/-- A paper-style corner: a mixed `2 x 2` submatrix using adjacent rows and
adjacent columns inside the rectangular zone. -/
def ZoneCorner {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∃ r : Fin (n - 1), adjacentFirst r ∈ R ∧ adjacentSecond r ∈ R ∧
    ∃ c : Fin (m - 1), adjacentFirst c ∈ C ∧ adjacentSecond c ∈ C ∧
      TwoByTwoMixed M (adjacentFirst r) (adjacentSecond r)
        (adjacentFirst c) (adjacentSecond c)

/-- A mixed `2 x 2` submatrix inside a rectangular zone, with no adjacency
requirement.  This is an algebraic witness for mixedness, not a paper corner. -/
def ZoneTwoByTwoSubmatrix {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C,
    TwoByTwoMixed M r₁ r₂ c₁ c₂

theorem not_zoneVertical_iff_exists {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ¬ ZoneVertical M R C ↔
      ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ c ∈ C, M r₁ c ≠ M r₂ c := by
  classical
  simp [ZoneVertical]

theorem not_zoneHorizontal_iff_exists {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ¬ ZoneHorizontal M R C ↔
      ∃ r ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C, M r c₁ ≠ M r c₂ := by
  classical
  simp [ZoneHorizontal]

theorem zoneTwoByTwoSubmatrix_of_zoneMixed {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneMixed M R C) : ZoneTwoByTwoSubmatrix M R C := by
  classical
  rcases (not_zoneVertical_iff_exists M R C).mp h.1 with
    ⟨a, ha, b, hb, x, hx, habx⟩
  rcases (not_zoneHorizontal_iff_exists M R C).mp h.2 with
    ⟨r, hr, y, hy, z, hz, hryz⟩
  by_cases hay : M a x ≠ M a y
  · exact ⟨a, ha, b, hb, x, hx, y, hy, Or.inl habx, Or.inl hay⟩
  · have hay' : M a x = M a y := Classical.not_not.mp hay
    by_cases hby : M b x ≠ M b y
    · exact ⟨a, ha, b, hb, x, hx, y, hy, Or.inl habx, Or.inr hby⟩
    · have hby' : M b x = M b y := Classical.not_not.mp hby
      by_cases haz : M a x ≠ M a z
      · exact ⟨a, ha, b, hb, x, hx, z, hz, Or.inl habx, Or.inl haz⟩
      · have haz' : M a x = M a z := Classical.not_not.mp haz
        by_cases hbz : M b x ≠ M b z
        · exact ⟨a, ha, b, hb, x, hx, z, hz, Or.inl habx, Or.inr hbz⟩
        · have hbz' : M b x = M b z := Classical.not_not.mp hbz
          have hayz : M a y = M a z := hay'.symm.trans haz'
          by_cases hrya : M r y ≠ M a y
          · exact ⟨r, hr, a, ha, y, hy, z, hz, Or.inl hrya, Or.inl hryz⟩
          · have hrya' : M r y = M a y := Classical.not_not.mp hrya
            have hrza : M r z ≠ M a z := by
              intro hrza
              exact hryz (hrya'.trans (hayz.trans hrza.symm))
            exact ⟨r, hr, a, ha, y, hy, z, hz, Or.inr hrza, Or.inl hryz⟩

theorem zoneMixed_of_zoneTwoByTwoSubmatrix {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneTwoByTwoSubmatrix M R C) : ZoneMixed M R C := by
  rcases h with ⟨r₁, hr₁, r₂, hr₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  constructor
  · intro hv
    rcases hvert with h | h
    · exact h (hv hr₁ hr₂ hc₁)
    · exact h (hv hr₁ hr₂ hc₂)
  · intro hh
    rcases hhoriz with h | h
    · exact h (hh hr₁ hc₁ hc₂)
    · exact h (hh hr₂ hc₁ hc₂)

/-- A rectangular zone is mixed iff it contains a mixed `2 x 2` submatrix.
This statement has no adjacency requirement; paper corners are `ZoneCorner`. -/
theorem zoneMixed_iff_zoneTwoByTwoSubmatrix {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ZoneMixed M R C ↔ ZoneTwoByTwoSubmatrix M R C :=
  ⟨zoneTwoByTwoSubmatrix_of_zoneMixed, zoneMixed_of_zoneTwoByTwoSubmatrix⟩

/-- A paper-style adjacent corner is, in particular, a mixed `2 x 2`
submatrix witness. -/
theorem zoneTwoByTwoSubmatrix_of_zoneCorner {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneCorner M R C) : ZoneTwoByTwoSubmatrix M R C := by
  rcases h with ⟨r, hr₁, hr₂, c, hc₁, hc₂, hmix⟩
  exact ⟨adjacentFirst r, hr₁, adjacentSecond r, hr₂,
    adjacentFirst c, hc₁, adjacentSecond c, hc₂, hmix⟩

/-- A paper-style adjacent corner witnesses that the zone is mixed. -/
theorem zoneMixed_of_zoneCorner {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneCorner M R C) : ZoneMixed M R C :=
  zoneMixed_of_zoneTwoByTwoSubmatrix (zoneTwoByTwoSubmatrix_of_zoneCorner h)

end Matrix
end Lax4Proofs.TwinWidth
