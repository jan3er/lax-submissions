import Lax4Proofs.Source.TwinWidth.Matrix.Theorem10

/-!
# Symmetric matrix contraction sequences

For graph adjacency matrices, Theorem 14 uses the symmetric version of the
matrix construction: every row contraction is immediately mirrored by the
corresponding column contraction, and conversely.  This file records the
front-end structure for those paired contractions.
-/

namespace Lax4Proofs.TwinWidth
namespace Matrix

/-- A square Boolean matrix is symmetric when mirroring about the diagonal
preserves every entry.  This is the matrix property used by Theorem 14 for
ordered adjacency matrices of undirected graphs. -/
def IsSymmetricMatrix {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) : Prop :=
  ∀ i j, M i j = M j i

namespace MatrixDivision

/-- The square matrix division obtained by using the same interval division
for rows and columns.  This is the local model for a perfectly mirrored
division. -/
def same {n k : ℕ} (D : Division n (k + 1)) : MatrixDivision n n where
  rowCuts := k
  colCuts := k
  rowDiv := D
  colDiv := D

end MatrixDivision

theorem zoneConstant_swap_iff_of_isSymmetricMatrix {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (R C : Finset (Fin n)) :
    ZoneConstant M R C ↔ ZoneConstant M C R := by
  constructor
  · intro h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂
    calc
      M c₁ r₁ = M r₁ c₁ := hM c₁ r₁
      _ = M r₂ c₂ := h hr₁ hr₂ hc₁ hc₂
      _ = M c₂ r₂ := (hM c₂ r₂).symm
  · intro h r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
    calc
      M r₁ c₁ = M c₁ r₁ := hM r₁ c₁
      _ = M c₂ r₂ := h hc₁ hc₂ hr₁ hr₂
      _ = M r₂ c₂ := (hM r₂ c₂).symm

theorem zoneVertical_swap_iff_zoneHorizontal_of_isSymmetricMatrix {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (R C : Finset (Fin n)) :
    ZoneVertical M R C ↔ ZoneHorizontal M C R := by
  constructor
  · intro h c hc r₁ r₂ hr₁ hr₂
    calc
      M c r₁ = M r₁ c := hM c r₁
      _ = M r₂ c := h (r₁ := r₁) (r₂ := r₂) hr₁ hr₂ (c := c) hc
      _ = M c r₂ := (hM c r₂).symm
  · intro h r₁ r₂ hr₁ hr₂ c hc
    calc
      M r₁ c = M c r₁ := hM r₁ c
      _ = M c r₂ := h (r := c) hc (c₁ := r₁) (c₂ := r₂) hr₁ hr₂
      _ = M r₂ c := (hM r₂ c).symm

theorem zoneHorizontal_swap_iff_zoneVertical_of_isSymmetricMatrix {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (R C : Finset (Fin n)) :
    ZoneHorizontal M R C ↔ ZoneVertical M C R := by
  constructor
  · intro h c₁ c₂ hc₁ hc₂ r hr
    calc
      M c₁ r = M r c₁ := hM c₁ r
      _ = M r c₂ := h (r := r) hr (c₁ := c₁) (c₂ := c₂) hc₁ hc₂
      _ = M c₂ r := (hM c₂ r).symm
  · intro h r hr c₁ c₂ hc₁ hc₂
    calc
      M r c₁ = M c₁ r := hM r c₁
      _ = M c₂ r := h (r₁ := c₁) (r₂ := c₂) hc₁ hc₂ (c := r) hr
      _ = M r c₂ := (hM r c₂).symm

theorem zoneMixed_swap_iff_of_isSymmetricMatrix {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (R C : Finset (Fin n)) :
    ZoneMixed M R C ↔ ZoneMixed M C R := by
  constructor
  · intro h
    exact
      ⟨fun hv => h.2
          ((zoneHorizontal_swap_iff_zoneVertical_of_isSymmetricMatrix hM R C).mpr hv),
        fun hh => h.1
          ((zoneVertical_swap_iff_zoneHorizontal_of_isSymmetricMatrix hM R C).mpr hh)⟩
  · intro h
    exact
      ⟨fun hv => h.2
          ((zoneVertical_swap_iff_zoneHorizontal_of_isSymmetricMatrix hM R C).mp hv),
        fun hh => h.1
          ((zoneHorizontal_swap_iff_zoneVertical_of_isSymmetricMatrix hM R C).mp hh)⟩

theorem rowCutVertical_iff_colCutHorizontal_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) (i : Fin k) :
    RowCutVertical M D C i ↔ ColCutHorizontal M C D i := by
  constructor
  · intro h c hc
    calc
      M c (D.last i.castSucc) = M (D.last i.castSucc) c := hM c (D.last i.castSucc)
      _ = M (D.first i.succ) c := h hc
      _ = M c (D.first i.succ) := (hM c (D.first i.succ)).symm
  · intro h c hc
    calc
      M (D.last i.castSucc) c = M c (D.last i.castSucc) := hM (D.last i.castSucc) c
      _ = M c (D.first i.succ) := h (r := c) hc
      _ = M (D.first i.succ) c := (hM (D.first i.succ) c).symm

theorem rowCutHorizontal_iff_colCutVertical_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) (i : Fin k) :
    RowCutHorizontal M D C i ↔ ColCutVertical M C D i := by
  constructor
  · intro h
    constructor
    · intro c₁ c₂ hc₁ hc₂
      calc
        M c₁ (D.last i.castSucc) = M (D.last i.castSucc) c₁ :=
          hM c₁ (D.last i.castSucc)
        _ = M (D.last i.castSucc) c₂ := h.1 hc₁ hc₂
        _ = M c₂ (D.last i.castSucc) := (hM c₂ (D.last i.castSucc)).symm
    · intro c₁ c₂ hc₁ hc₂
      calc
        M c₁ (D.first i.succ) = M (D.first i.succ) c₁ :=
          hM c₁ (D.first i.succ)
        _ = M (D.first i.succ) c₂ := h.2 hc₁ hc₂
        _ = M c₂ (D.first i.succ) := (hM c₂ (D.first i.succ)).symm
  · intro h
    constructor
    · intro c₁ c₂ hc₁ hc₂
      calc
        M (D.last i.castSucc) c₁ = M c₁ (D.last i.castSucc) :=
          hM (D.last i.castSucc) c₁
        _ = M c₂ (D.last i.castSucc) := h.1 hc₁ hc₂
        _ = M (D.last i.castSucc) c₂ := (hM (D.last i.castSucc) c₂).symm
    · intro c₁ c₂ hc₁ hc₂
      calc
        M (D.first i.succ) c₁ = M c₁ (D.first i.succ) :=
          hM (D.first i.succ) c₁
        _ = M c₂ (D.first i.succ) := h.2 hc₁ hc₂
        _ = M (D.first i.succ) c₂ := (hM (D.first i.succ) c₂).symm

theorem rowCutMixed_iff_colCutMixed_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) (i : Fin k) :
    RowCutMixed M D C i ↔ ColCutMixed M C D i := by
  constructor
  · intro h
    exact
      ⟨fun hv => h.2
          ((rowCutHorizontal_iff_colCutVertical_of_isSymmetricMatrix hM D C i).mpr hv),
        fun hh => h.1
          ((rowCutVertical_iff_colCutHorizontal_of_isSymmetricMatrix hM D C i).mpr hh)⟩
  · intro h
    exact
      ⟨fun hv => h.2
          ((rowCutVertical_iff_colCutHorizontal_of_isSymmetricMatrix hM D C i).mp hv),
        fun hh => h.1
          ((rowCutHorizontal_iff_colCutVertical_of_isSymmetricMatrix hM D C i).mp hh)⟩

theorem rowMixedValue_eq_colMixedValue_swap_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) :
    rowMixedValue M D C = colMixedValue M C D := by
  classical
  have hzones : rowMixedZones M D C = colMixedZones M C D := by
    ext i
    simp [rowMixedZones, colMixedZones,
      (zoneMixed_swap_iff_of_isSymmetricMatrix hM (D.part i) C)]
  have hcuts : rowMixedCuts M D C = colMixedCuts M C D := by
    ext i
    simp [rowMixedCuts, colMixedCuts,
      (rowCutMixed_iff_colCutMixed_of_isSymmetricMatrix hM D C i)]
  simp [rowMixedValue, colMixedValue, hzones, hcuts]

theorem rowMixedItems_eq_colMixedItems_swap_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) :
    rowMixedItems M D C = colMixedItems M C D := by
  classical
  ext item
  cases item with
  | inl i =>
      simp [zoneMixed_swap_iff_of_isSymmetricMatrix hM (D.part i) C]
  | inr i =>
      simp [rowCutMixed_iff_colCutMixed_of_isSymmetricMatrix hM D C i]

/-- A square matrix partition is symmetric when its row and column parts are
the same family. -/
def MatrixPartition.IsSymmetric {n : ℕ} (P : MatrixPartition n n) : Prop :=
  P.rowParts = P.colParts

namespace MatrixPartition

theorem splitPartsByLabel_eq_of_base_eq_of_labels
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    {P Q : Finset (Finset α)}
    {labelP labelQ : Finset α → α → β}
    (hPQ : P = Q)
    (hlabel :
      ∀ ⦃A⦄, A ∈ P → ∀ ⦃x⦄, x ∈ A → labelP A x = labelQ A x) :
    splitPartsByLabel P labelP = splitPartsByLabel Q labelQ := by
  classical
  subst Q
  ext F
  constructor
  · intro hF
    rcases (mem_splitPartsByLabel.mp hF) with ⟨hne, A, hA, b, rfl⟩
    refine mem_splitPartsByLabel.mpr ⟨?_, A, hA, b, ?_⟩
    · rcases hne with ⟨x, hx⟩
      exact ⟨x, by simpa [hlabel hA (Finset.mem_of_mem_filter x hx)] using hx⟩
    · ext x
      by_cases hxA : x ∈ A
      · simp [hxA, hlabel hA hxA]
      · simp [hxA]
  · intro hF
    rcases (mem_splitPartsByLabel.mp hF) with ⟨hne, A, hA, b, rfl⟩
    refine mem_splitPartsByLabel.mpr ⟨?_, A, hA, b, ?_⟩
    · rcases hne with ⟨x, hx⟩
      exact ⟨x, by simpa [hlabel hA (Finset.mem_of_mem_filter x hx)] using hx⟩
    · ext x
      by_cases hxA : x ∈ A
      · simp [hxA, hlabel hA hxA]
      · simp [hxA]

end MatrixPartition

namespace MatrixDivision

/-- A square division is symmetric when row and column cuts agree and matching
row and column parts are the same subsets of `Fin n`. -/
def IsSymmetric {n : ℕ} (D : MatrixDivision n n) : Prop :=
  ∃ hcuts : D.rowCuts = D.colCuts,
    ∀ i : Fin (D.rowCuts + 1),
      D.rowDiv.part i =
        D.colDiv.part
          ((finCongr (by omega : D.rowCuts + 1 = D.colCuts + 1)) i)

@[simp] theorem same_isSymmetric {n k : ℕ} (D : Division n (k + 1)) :
    (same D).IsSymmetric := by
  exact ⟨rfl, by intro i; rfl⟩

theorem finest_isSymmetric {n : ℕ} (hn : 0 < n) :
    (finest hn hn).IsSymmetric := by
  refine ⟨rfl, ?_⟩
  intro i
  simp [finest, Division.castIndex, Division.singleton]
  rfl

theorem toPartition_isSymmetric_of_isSymmetric {n : ℕ}
    {D : MatrixDivision n n} (hD : D.IsSymmetric) :
    D.toPartition.IsSymmetric := by
  classical
  rcases D with ⟨rowCuts, colCuts, rowDiv, colDiv⟩
  rcases hD with ⟨hcuts, hparts⟩
  dsimp at hcuts hparts ⊢
  subst colCuts
  ext A
  constructor
  · intro hA
    rcases Finset.mem_map.mp hA with ⟨i, _hi, rfl⟩
    refine Finset.mem_map.mpr
      ⟨(finCongr (by omega : rowCuts + 1 = rowCuts + 1)) i,
        Finset.mem_univ _, ?_⟩
    exact (hparts i).symm
  · intro hA
    rcases Finset.mem_map.mp hA with ⟨j, _hj, rfl⟩
    let i : Fin (rowCuts + 1) :=
      (finCongr (by omega : rowCuts + 1 = rowCuts + 1)).symm j
    refine Finset.mem_map.mpr ⟨i, Finset.mem_univ _, ?_⟩
    have h := hparts i
    simpa [i] using h

theorem profilePartition_isSymmetric_of_profile_eq {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {D : MatrixDivision n n}
    (hD : D.IsSymmetric)
    (hprofile :
      ∀ ⦃A⦄, A ∈ D.toPartition.rowParts → ∀ ⦃x⦄, x ∈ A →
        rowProfile (d := d) M D (rowIndexOfPartitionPart D A) x =
          colProfile (d := d) M D (colIndexOfPartitionPart D A) x) :
    (profilePartition (d := d) M D).IsSymmetric := by
  classical
  have hparts : D.toPartition.rowParts = D.toPartition.colParts :=
    toPartition_isSymmetric_of_isSymmetric hD
  unfold profilePartition
  exact MatrixPartition.splitPartsByLabel_eq_of_base_eq_of_labels
    hparts hprofile

/-- For a mirrored division, the row and column bad-item counters agree after
swapping the matrix across the diagonal. -/
theorem colBadBefore_same_eq_rowBadBefore_same_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (i j : Fin (k + 1)) :
    colBadBefore M (same D) i j = rowBadBefore M (same D) i j := by
  classical
  simp [colBadBefore, rowBadBefore, same,
    rowMixedItems_eq_colMixedItems_swap_of_isSymmetricMatrix hM D (D.part i),
    colMixedItemPos, rowMixedItemPos]
  rfl

/-- The candidate indices used by row and column profiles are the same for a
symmetric matrix on a mirrored division. -/
theorem rowProfileCandidates_same_eq_colProfileCandidates_same_of_isSymmetricMatrix
    {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (i : Fin (k + 1)) (q : Fin (d + 1)) :
    rowProfileCandidates (d := d) M (same D) i q =
      colProfileCandidates (d := d) M (same D) i q := by
  classical
  ext j
  constructor
  · intro hj
    have hdata :
        ¬ ZoneMixed M (D.part i) (D.part j) ∧
          colBadBefore M (same D) i j = q.1 := by
      change j ∈ ((Finset.univ : Finset (Fin (k + 1))).filter fun j =>
        ¬ ZoneMixed M (D.part i) (D.part j) ∧
          colBadBefore M (same D) i j = q.1) at hj
      exact (Finset.mem_filter.mp hj).2
    have hout :
        ¬ ZoneMixed M (D.part j) (D.part i) ∧
          rowBadBefore M (same D) i j = q.1 := by
      constructor
      · intro hmix
        exact hdata.1
          ((zoneMixed_swap_iff_of_isSymmetricMatrix hM (D.part i) (D.part j)).mpr hmix)
      · simpa [(colBadBefore_same_eq_rowBadBefore_same_of_isSymmetricMatrix
          hM D i j).symm] using hdata.2
    change j ∈ ((Finset.univ : Finset (Fin (k + 1))).filter fun j =>
          ¬ ZoneMixed M (D.part j) (D.part i) ∧
            rowBadBefore M (same D) i j = q.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hout⟩
  · intro hj
    have hdata :
        ¬ ZoneMixed M (D.part j) (D.part i) ∧
          rowBadBefore M (same D) i j = q.1 := by
      change j ∈ ((Finset.univ : Finset (Fin (k + 1))).filter fun j =>
        ¬ ZoneMixed M (D.part j) (D.part i) ∧
          rowBadBefore M (same D) i j = q.1) at hj
      exact (Finset.mem_filter.mp hj).2
    have hout :
        ¬ ZoneMixed M (D.part i) (D.part j) ∧
          colBadBefore M (same D) i j = q.1 := by
      constructor
      · intro hmix
        exact hdata.1
          ((zoneMixed_swap_iff_of_isSymmetricMatrix hM (D.part i) (D.part j)).mp hmix)
      · simpa [colBadBefore_same_eq_rowBadBefore_same_of_isSymmetricMatrix
          hM D i j] using hdata.2
    change j ∈ ((Finset.univ : Finset (Fin (k + 1))).filter fun j =>
          ¬ ZoneMixed M (D.part i) (D.part j) ∧
            colBadBefore M (same D) i j = q.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hout⟩

/-- Row and column profiles agree pointwise on a symmetric matrix when the row
and column divisions are literally mirrored by the same interval division. -/
theorem rowProfile_same_eq_colProfile_same_of_isSymmetricMatrix {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (i : Fin (k + 1)) (x : Fin n) :
    rowProfile (d := d) M (same D) i x =
      colProfile (d := d) M (same D) i x := by
  classical
  funext q
  let Rset := rowProfileCandidates (d := d) M (same D) i q
  let Cset := colProfileCandidates (d := d) M (same D) i q
  have hsets : Rset = Cset := by
    simpa [Rset, Cset] using
      rowProfileCandidates_same_eq_colProfileCandidates_same_of_isSymmetricMatrix
        hM D i q
  by_cases hR : Rset.Nonempty
  · have hC : Cset.Nonempty := by simpa [← hsets] using hR
    have hmin : Rset.min' hR = Cset.min' hC := by
      apply le_antisymm
      · exact Finset.min'_le _ _ (by
          simpa [← hsets] using Finset.min'_mem Cset hC)
      · exact Finset.min'_le _ _ (by
          simpa [hsets] using Finset.min'_mem Rset hR)
    have hRactual :
        (rowProfileCandidates (d := d) M (same D) i q).Nonempty := by
      simpa [Rset] using hR
    have hCactual :
        (colProfileCandidates (d := d) M (same D) i q).Nonempty := by
      simpa [Cset] using hC
    have hminActual :
        (rowProfileCandidates (d := d) M (same D) i q).min' hRactual =
          (colProfileCandidates (d := d) M (same D) i q).min' hCactual := by
      simpa [Rset, Cset] using hmin
    have hRstruct :
        (rowProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).Nonempty := by
      simpa [same] using hRactual
    have hCstruct :
        (colProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).Nonempty := by
      simpa [same] using hCactual
    have hminStruct :
        (rowProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).min' hRstruct =
          (colProfileCandidates (d := d) M
            ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
              MatrixDivision n n) i q).min' hCstruct := by
      simpa [same] using hminActual
    have hentry :=
      hM x (D.first
        ((rowProfileCandidates (d := d) M (same D) i q).min' hRactual))
    simpa [rowProfile, colProfile, same, hRstruct, hCstruct, hminStruct] using hentry
  · have hC : ¬ Cset.Nonempty := by
      intro h
      exact hR (by simpa [hsets] using h)
    have hRactual :
        ¬ (rowProfileCandidates (d := d) M (same D) i q).Nonempty := by
      simpa [Rset] using hR
    have hCactual :
        ¬ (colProfileCandidates (d := d) M (same D) i q).Nonempty := by
      simpa [Cset] using hC
    have hRstruct :
        ¬ (rowProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).Nonempty := by
      simpa [same] using hRactual
    have hCstruct :
        ¬ (colProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).Nonempty := by
      simpa [same] using hCactual
    simp [rowProfile, colProfile, same, hRstruct, hCstruct]

/-- The Section 5.8 profile partition is symmetric for a symmetric matrix when
the underlying division uses the same row and column intervals. -/
theorem profilePartition_same_isSymmetric_of_isSymmetricMatrix {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1)) :
    (profilePartition (d := d) M (same D)).IsSymmetric := by
  classical
  apply profilePartition_isSymmetric_of_profile_eq (same_isSymmetric D)
  intro A hA x hx
  have hAcol : A ∈ (same D).toPartition.colParts := by
    simpa [same] using hA
  have hrowSpec :=
    rowIndexOfPartitionPart_spec (same D) hA
  have hcolSpec :=
    colIndexOfPartitionPart_spec (same D) hAcol
  have hidx :
      rowIndexOfPartitionPart (same D) A =
        colIndexOfPartitionPart (same D) A := by
    apply D.part_injective
    calc
      D.part (rowIndexOfPartitionPart (same D) A) = A := by
        simpa [same] using hrowSpec
      _ = D.part (colIndexOfPartitionPart (same D) A) := by
        simpa [same] using hcolSpec.symm
  simpa [hidx] using
    rowProfile_same_eq_colProfile_same_of_isSymmetricMatrix
      (d := d) hM D (rowIndexOfPartitionPart (same D) A) x

/-- Mirrored fusion preserves bounded mixed value once the newly fused row
block has bounded column mixed value.  The row side follows by symmetry from
the column side. -/
theorem mixedValueAtMost_same_fuse_of_colMixedValue_fused_le {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M)
    (D : Division n (k + 2)) (hD : MixedValueAtMost M (same D) d)
    (i : Fin (k + 1))
    (hnew : colMixedValue M ((D.fuse i).part i) D ≤ d) :
    MixedValueAtMost M (same (D.fuse i)) d := by
  classical
  have hcol :
      ∀ a : Fin (k + 1),
        colMixedValue M ((D.fuse i).part a) (D.fuse i) ≤ d := by
    intro a
    have hmono :
        colMixedValue M ((D.fuse i).part a) (D.fuse i) ≤
          colMixedValue M ((D.fuse i).part a) D :=
      colMixedValue_fuse_le (M := M) ((D.fuse i).part a) D i
    refine le_trans hmono ?_
    by_cases hai : a = i
    · subst a
      exact hnew
    · by_cases hai_lt : a < i
      · have hpart := D.fuse_part_of_lt (i := i) (j := a) hai_lt
        rw [hpart]
        simpa [same] using hD.2 a.castSucc
      · have hia : i < a := lt_of_le_of_ne (le_of_not_gt hai_lt) (Ne.symm hai)
        have hpart := D.fuse_part_of_gt (i := i) (j := a) hia
        rw [hpart]
        simpa [same] using hD.2 a.succ
  constructor
  · intro j
    change rowMixedValue M (D.fuse i) ((D.fuse i).part j) ≤ d
    rw [rowMixedValue_eq_colMixedValue_swap_of_isSymmetricMatrix
      hM (D.fuse i) ((D.fuse i).part j)]
    exact hcol j
  · intro a
    change colMixedValue M ((D.fuse i).part a) (D.fuse i) ≤ d
    exact hcol a

/-- A local good cut for the mixed-value greedy proof.  This is the
non-contracted form of `GreedyFusionStep`, retaining the cut index needed by
the mirrored construction. -/
def HasGoodCut {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool)
    (D : MatrixDivision n n) (d : ℕ) : Prop :=
  (∃ hrow : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
    colMixedValue M
      ((D.rowFuse hrow i).rowDiv.part
        ((finCongr
          (by simp [rowFuse]; omega :
            D.rowCuts = (D.rowFuse hrow i).rowCuts + 1)) i))
      (D.rowFuse hrow i).colDiv ≤ d) ∨
    (∃ hcol : 0 < D.colCuts, ∃ j : Fin D.colCuts,
      rowMixedValue M
        (D.colFuse hcol j).rowDiv
        ((D.colFuse hcol j).colDiv.part
          ((finCongr
            (by simp [colFuse]; omega :
              D.colCuts = (D.colFuse hcol j).colCuts + 1)) j)) ≤ d)

/-- Lemma 13's local Marcus--Tardos step, retaining the good cut rather than
immediately packaging it as a one-sided fusion. -/
theorem hasGoodCut_of_marcusTardos
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n : ℕ} (M : _root_.Matrix (Fin n) (Fin n) Bool) (t : ℕ),
      MixedFree M t → ∀ D : MatrixDivision n n,
        MixedValueAtMost M D (lemma13MixedValueBound c t) →
          ¬ IsCoarsest D →
            HasGoodCut M D (lemma13MixedValueBound c t) := by
  intro n M t hfree D hD hcoarse
  by_cases ht : t = 0
  · subst t
    exact (False.elim (hfree (hasMixedMinor_zero M)))
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    by_cases hrow : 0 < D.rowCuts
    · by_cases hcol : 0 < D.colCuts
      · by_cases hgoodRow :
          ∃ hrow' : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
            colMixedValue M
              ((D.rowFuse hrow' i).rowDiv.part
                ((finCongr
                  (by simp [rowFuse]; omega :
                    D.rowCuts =
                      (D.rowFuse hrow' i).rowCuts + 1)) i))
              (D.rowFuse hrow' i).colDiv ≤
                lemma13MixedValueBound c t
        · exact Or.inl hgoodRow
        · by_cases hgoodCol :
            ∃ hcol' : 0 < D.colCuts, ∃ j : Fin D.colCuts,
              rowMixedValue M
                (D.colFuse hcol' j).rowDiv
                ((D.colFuse hcol' j).colDiv.part
                  ((finCongr
                    (by simp [colFuse]; omega :
                      D.colCuts =
                        (D.colFuse hcol' j).colCuts + 1)) j)) ≤
                lemma13MixedValueBound c t
          · exact Or.inr hgoodCol
          · exact False.elim
              (pairedMarcusTardosCountingStep
                M t (hMT t) hfree D hD hrow hcol hgoodRow hgoodCol)
      · have hcol0 : D.colCuts = 0 := Nat.eq_zero_of_not_pos hcol
        rcases exists_goodRowCut_of_colCuts_eq_zero
          (M := M) (hMT t) htpos D hrow hcol0 with ⟨i, hi⟩
        exact Or.inl ⟨hrow, i, le_trans hi (by
          have hcpos : 0 < c t := IsMarcusTardosConstant.pos (hMT t) htpos
          simp [lemma13MixedValueBound]
          omega)⟩
    · have hrow0 : D.rowCuts = 0 := Nat.eq_zero_of_not_pos hrow
      have hcol : 0 < D.colCuts := by
        by_contra hcolnot
        have hcol0 : D.colCuts = 0 := Nat.eq_zero_of_not_pos hcolnot
        exact hcoarse ⟨hrow0, hcol0⟩
      rcases exists_goodColCut_of_rowCuts_eq_zero
        (M := M) (hMT t) htpos D hcol hrow0 with ⟨j, hj⟩
      exact Or.inr ⟨hcol, j, le_trans hj (by
        have hcpos : 0 < c t := IsMarcusTardosConstant.pos (hMT t) htpos
        simp [lemma13MixedValueBound]
        omega)⟩

/-- The row-good-cut conclusion for `same D` is exactly the fused-row mixed
value bound needed by the mirrored fusion lemma. -/
theorem colMixedValue_fused_le_of_goodRow_same {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (D : Division n (k + 2))
    (hrow : 0 < (same D).rowCuts) (i : Fin (same D).rowCuts)
    (hgood :
      colMixedValue M
        (((same D).rowFuse hrow i).rowDiv.part
          ((finCongr
            (by simp [rowFuse]; omega :
              (same D).rowCuts = ((same D).rowFuse hrow i).rowCuts + 1)) i))
        ((same D).rowFuse hrow i).colDiv ≤ d) :
    colMixedValue M
      ((D.fuse ((finCongr (by rfl : (same D).rowCuts = k + 1)) i)).part
        ((finCongr (by rfl : (same D).rowCuts = k + 1)) i))
      D ≤ d := by
  simpa [same, rowFuse] using hgood

/-- The column-good-cut conclusion for `same D`, mirrored across a symmetric
matrix, gives the same fused-row column mixed value bound. -/
theorem colMixedValue_fused_le_of_goodCol_same {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M)
    (D : Division n (k + 2))
    (hcol : 0 < (same D).colCuts) (j : Fin (same D).colCuts)
    (hgood :
      rowMixedValue M
        ((same D).colFuse hcol j).rowDiv
        (((same D).colFuse hcol j).colDiv.part
          ((finCongr
            (by simp [colFuse]; omega :
              (same D).colCuts = ((same D).colFuse hcol j).colCuts + 1)) j)) ≤ d) :
    colMixedValue M
      ((D.fuse ((finCongr (by rfl : (same D).colCuts = k + 1)) j)).part
        ((finCongr (by rfl : (same D).colCuts = k + 1)) j))
      D ≤ d := by
  have hrow :
      rowMixedValue M D
        ((D.fuse ((finCongr (by rfl : (same D).colCuts = k + 1)) j)).part
          ((finCongr (by rfl : (same D).colCuts = k + 1)) j)) ≤ d := by
    simpa [same, colFuse] using hgood
  rwa [rowMixedValue_eq_colMixedValue_swap_of_isSymmetricMatrix
    hM D
      ((D.fuse ((finCongr (by rfl : (same D).colCuts = k + 1)) j)).part
        ((finCongr (by rfl : (same D).colCuts = k + 1)) j))] at hrow

end MatrixDivision

/-- One symmetric contraction block: either contract two row parts and mirror
the same contraction on columns, or contract two column parts and mirror it on
rows.  Since row and column parts are both subsets of `Fin n`, both cases are
represented by the same merged pair of parts. -/
def MatrixPartition.IsSymmetricContraction {n : ℕ}
    (P Q : MatrixPartition n n) : Prop :=
  ∃ A ∈ P.rowParts, ∃ B ∈ P.rowParts, A ≠ B ∧
    Q.rowParts = insert (A ∪ B) ((P.rowParts.erase A).erase B) ∧
    Q.colParts = insert (A ∪ B) ((P.colParts.erase A).erase B)

namespace MatrixPartition

/-- The unique empty partition used for `0 × 0` matrix zerology. -/
def emptyZero : MatrixPartition 0 0 where
  rowParts := ∅
  row_nonempty := by simp
  row_disjoint := by simp
  row_cover := by intro r; exact Fin.elim0 r
  colParts := ∅
  col_nonempty := by simp
  col_disjoint := by simp
  col_cover := by intro c; exact Fin.elim0 c

theorem emptyZero_isFinest : emptyZero.IsFinest := by
  constructor
  · simp [emptyZero]
  constructor
  · intro r
    exact Fin.elim0 r
  constructor
  · simp [emptyZero]
  · intro c
    exact Fin.elim0 c

theorem emptyZero_isCoarsest : emptyZero.IsCoarsest := by
  simp [emptyZero, IsCoarsest]

theorem emptyZero_isSymmetric : emptyZero.IsSymmetric := by
  rfl

/-- Simultaneously contract the same two parts in the rows and columns of a
symmetric square matrix partition. -/
noncomputable def symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) : MatrixPartition n n :=
  let Prow := P.rowContract hA hB hAB
  Prow.colContract
    (by
      simpa [Prow, IsSymmetric] using hP ▸ hA)
    (by
      simpa [Prow, IsSymmetric] using hP ▸ hB)
    hAB

@[simp] theorem rowParts_symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).rowParts =
      insert (A ∪ B) ((P.rowParts.erase A).erase B) := by
  simp [symContract]

@[simp] theorem colParts_symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).colParts =
      insert (A ∪ B) ((P.colParts.erase A).erase B) := by
  simp [symContract]

theorem isSymmetric_symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).IsSymmetric := by
  simp [IsSymmetric]
  rw [hP]

theorem isSymmetricContraction_symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    P.IsSymmetricContraction (P.symContract hP hA hB hAB) := by
  exact ⟨A, hA, B, hB, hAB, by simp, by simp⟩

theorem rowParts_card_symContract_lt {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).rowParts.card < P.rowParts.card := by
  have hrowlt := MatrixPartition.rowParts_card_rowContract_lt P hA hB hAB
  simpa [symContract] using hrowlt

theorem colParts_card_symContract_lt {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).colParts.card < P.colParts.card := by
  let Prow : MatrixPartition n n := P.rowContract hA hB hAB
  have hAcol : A ∈ Prow.colParts := by
    simpa [Prow] using (hP ▸ hA)
  have hBcol : B ∈ Prow.colParts := by
    simpa [Prow] using (hP ▸ hB)
  have hcollt := MatrixPartition.colParts_card_colContract_lt Prow hAcol hBcol hAB
  simpa [symContract, Prow] using hcollt

end MatrixPartition

/-- A symmetric matrix contraction sequence of error value at most `d`. -/
structure SymmetricMatrixContractionSequence {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (d : ℕ) where
  /-- Number of paired contraction blocks. -/
  stepCount : ℕ
  /-- Symmetric partition at each time. -/
  partition : ℕ → MatrixPartition n n
  /-- Every partition has identical row and column families. -/
  symmetric : ∀ i, i ≤ stepCount → (partition i).IsSymmetric
  /-- The first partition is the singleton partition. -/
  starts : MatrixPartition.IsFinest (partition 0)
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Each step is a contraction together with its mirror about the diagonal. -/
  step_contracts :
    ∀ i, i < stepCount →
      MatrixPartition.IsSymmetricContraction (partition i) (partition (i + 1))
  /-- Every intermediate partition has error value at most `d`. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

/-- A square Boolean matrix has symmetric matrix twin-width at most `d` when it
has a symmetric contraction sequence of width `d`. -/
def SymmetricMatrixTwinWidthAtMost {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (d : ℕ) : Prop :=
  Nonempty (SymmetricMatrixContractionSequence M d)

/-- A symmetric contraction tail from a prescribed symmetric square partition
to a coarsest partition.  This is the tail object used to expand a bounded
refinement step into paired row/column contractions. -/
structure SymmetricMatrixContractionTail {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (d : ℕ)
    (P₀ : MatrixPartition n n) where
  /-- Number of remaining paired contraction blocks. -/
  stepCount : ℕ
  /-- Symmetric partition at each time. -/
  partition : ℕ → MatrixPartition n n
  /-- The first partition is the prescribed one. -/
  starts : partition 0 = P₀
  /-- Every partition in the tail is symmetric. -/
  symmetric : ∀ i, i ≤ stepCount → (partition i).IsSymmetric
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Consecutive partitions are paired symmetric contractions. -/
  step_contracts :
    ∀ i, i < stepCount →
      MatrixPartition.IsSymmetricContraction (partition i) (partition (i + 1))
  /-- Every partition in the tail has bounded error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

/-- A symmetric bounded-refinement partition sequence.  It is the square,
diagonal-mirrored version of the Lemma 8 input: every partition has the same
row and column families, each term boundedly refines the next, and every term
has error value at most `t`. -/
structure SymmetricBoundedErrorRefinementPartitionSequence {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (r t : ℕ) where
  /-- Number of coarse-graining steps. -/
  stepCount : ℕ
  /-- Symmetric partition at each time. -/
  partition : ℕ → MatrixPartition n n
  /-- The first partition is finest. -/
  starts : MatrixPartition.IsFinest (partition 0)
  /-- Every partition has the same row and column families. -/
  symmetric : ∀ i, i ≤ stepCount → (partition i).IsSymmetric
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Each partition boundedly refines the next. -/
  step_rrefines :
    ∀ i, i < stepCount → MatrixPartition.RRefines (partition i) (partition (i + 1)) r
  /-- Every partition in the sequence has bounded error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) t

/-- Upgrade an ordinary bounded-refinement partition sequence to the symmetric
version once symmetry of every partition has been proved. -/
def symmetricBoundedErrorRefinement_of_boundedErrorRefinement
    {n r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (S : BoundedErrorRefinementPartitionSequence M r t)
    (hsym : ∀ i, i ≤ S.stepCount → (S.partition i).IsSymmetric) :
    SymmetricBoundedErrorRefinementPartitionSequence M r t where
  stepCount := S.stepCount
  partition := S.partition
  starts := S.starts
  symmetric := hsym
  ends := S.ends
  step_rrefines := S.step_rrefines
  errorValue_le := S.errorValue_le

/-- Section 5.8 profile refinement preserves symmetry for any bounded
mixed-value division sequence whose divisions are literally mirrored by the
same row/column interval division at every time.  The remaining symmetric
Lemma 13 task is therefore exactly to construct such a mirrored mixed-value
sequence. -/
theorem symmetricBoundedErrorRefinement_of_same_boundedMixedValue
    {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (hd : 0 < d)
    (S : BoundedMixedValueDivisionSequence M d)
    (hsame :
      ∀ i, i ≤ S.stepCount →
        ∃ k : ℕ, ∃ D : Division n (k + 1),
          S.division i = MatrixDivision.same D) :
    Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
      (2 * 2 ^ (d + 1)) (d * 2 ^ (d + 1))) := by
  classical
  let T : BoundedErrorRefinementPartitionSequence M
      (2 * Fintype.card Bool ^ (d + 1))
      (d * Fintype.card Bool ^ (d + 1)) :=
    boundedErrorRefinementPartitionSequence_of_boundedMixedValue
      (α := Bool) hd S
  have hsym : ∀ i, i ≤ T.stepCount → (T.partition i).IsSymmetric := by
    intro i hi
    by_cases hcur : i ≤ S.stepCount
    · rcases hsame i hcur with ⟨k, D, hD⟩
      simpa [T, boundedErrorRefinementPartitionSequence_of_boundedMixedValue,
        hcur, hD] using
        MatrixDivision.profilePartition_same_isSymmetric_of_isSymmetricMatrix
          (d := d) hM D
    · have hi_last : i = S.stepCount + 1 := by
        dsimp [T, boundedErrorRefinementPartitionSequence_of_boundedMixedValue] at hi
        omega
      subst i
      have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
      rcases hsame S.stepCount le_rfl with ⟨k, D, hD⟩
      simpa [T, boundedErrorRefinementPartitionSequence_of_boundedMixedValue,
        hnot, hD] using
        MatrixDivision.toPartition_isSymmetric_of_isSymmetric
          (MatrixDivision.same_isSymmetric D)
  refine ⟨?_⟩
  simpa using symmetricBoundedErrorRefinement_of_boundedErrorRefinement T hsym

/-- The bounded-refinement factor for one mirrored profile-refinement block.
This formalization composes the row-profile and column-profile refinements, so
the factor is the product of the two one-sided factors. -/
def symmetricProfileRefinementBlockBound (d : ℕ) : ℕ :=
  (2 * 2 ^ (d + 1)) * (2 * 2 ^ (d + 1))

/-- The profile-partition error bound over the Boolean alphabet. -/
def symmetricProfileErrorBound (d : ℕ) : ℕ :=
  d * 2 ^ (d + 1)

/-- A tail of mirrored mixed-value divisions.  Consecutive terms are not
ordinary one-sided fusions: each step has already been converted into the
profile-partition bounded-refinement block obtained by mirroring the cut. -/
structure SameMixedValueDivisionTail {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (d : ℕ)
    (D₀ : MatrixDivision n n) where
  /-- Number of remaining mirrored fusion blocks. -/
  stepCount : ℕ
  /-- Division at each time. -/
  division : ℕ → MatrixDivision n n
  /-- The first division is the prescribed one. -/
  starts : division 0 = D₀
  /-- Every division is literally the same row/column interval division. -/
  same :
    ∀ i, i ≤ stepCount →
      ∃ k : ℕ, ∃ D : Division n (k + 1),
        division i = MatrixDivision.same D
  /-- The final division is coarsest. -/
  ends : MatrixDivision.IsCoarsest (division stepCount)
  /-- Consecutive profile partitions satisfy the mirrored block refinement
  bound. -/
  step_rrefines :
    ∀ i, i < stepCount →
      MatrixPartition.RRefines
        (MatrixDivision.profilePartition (d := d) M (division i))
        (MatrixDivision.profilePartition (d := d) M (division (i + 1)))
        (symmetricProfileRefinementBlockBound d)
  /-- Every division has mixed value at most `d`. -/
  mixedValue_le :
    ∀ i, i ≤ stepCount →
      MatrixDivision.MixedValueAtMost M (division i) d

namespace SameMixedValueDivisionTail

/-- Empty mirrored mixed-value tail from a coarsest same division. -/
def nil {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {D₀ : MatrixDivision n n}
    (hsame : ∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D)
    (hcoarse : MatrixDivision.IsCoarsest D₀)
    (hmix : MatrixDivision.MixedValueAtMost M D₀ d) :
    SameMixedValueDivisionTail M d D₀ where
  stepCount := 0
  division := fun _ => D₀
  starts := rfl
  same := by intro i hi; simpa using hsame
  ends := hcoarse
  step_rrefines := by intro i hi; omega
  mixedValue_le := by intro i hi; simpa using hmix

/-- Prepend one mirrored fusion block to a same-division tail. -/
def cons {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {D₀ D₁ : MatrixDivision n n}
    (hsame₀ : ∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D)
    (hmix₀ : MatrixDivision.MixedValueAtMost M D₀ d)
    (hrefine :
      MatrixPartition.RRefines
        (MatrixDivision.profilePartition (d := d) M D₀)
        (MatrixDivision.profilePartition (d := d) M D₁)
        (symmetricProfileRefinementBlockBound d))
    (S : SameMixedValueDivisionTail M d D₁) :
    SameMixedValueDivisionTail M d D₀ where
  stepCount := S.stepCount + 1
  division := fun i =>
    match i with
    | 0 => D₀
    | j + 1 => S.division j
  starts := rfl
  same := by
    intro i hi
    cases i with
    | zero =>
        simpa using hsame₀
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.same j hj
  ends := by
    simpa using S.ends
  step_rrefines := by
    intro i hi
    cases i with
    | zero =>
        simpa [S.starts] using hrefine
    | succ j =>
        have hj : j < S.stepCount := by omega
        simpa using S.step_rrefines j hj
  mixedValue_le := by
    intro i hi
    cases i with
    | zero =>
        simpa using hmix₀
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.mixedValue_le j hj

end SameMixedValueDivisionTail

namespace SymmetricMatrixContractionSequence

/-- Relax the numerical error bound on a symmetric contraction sequence. -/
noncomputable def mono {n d e : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hde : d ≤ e) (S : SymmetricMatrixContractionSequence M d) :
    SymmetricMatrixContractionSequence M e where
  stepCount := S.stepCount
  partition := S.partition
  symmetric := S.symmetric
  starts := S.starts
  ends := S.ends
  step_contracts := S.step_contracts
  errorValue_le := by
    intro i hi
    exact MatrixPartition.errorValueAtMost_mono hde (S.errorValue_le i hi)

end SymmetricMatrixContractionSequence

namespace MatrixPartition

/-- Bounded refinement of finite partition families is transitive, with
multiplied bounds.  The partition hypotheses are the nonemptiness of fine
parts and disjointness of coarse parts, exactly as supplied by
`MatrixPartition`. -/
theorem partsRRefine_trans_of_partition {α : Type*} [DecidableEq α]
    {P Q R : Finset (Finset α)} {r s : ℕ}
    (hPnonempty : ∀ ⦃A⦄, A ∈ P → A.Nonempty)
    (hRdisjoint : ∀ ⦃A B⦄, A ∈ R → B ∈ R → A ≠ B → Disjoint A B)
    (hPQ : PartsRRefine P Q r) (hQR : PartsRRefine Q R s) :
    PartsRRefine P R (r * s) := by
  classical
  constructor
  · intro A hA
    rcases hPQ.1 hA with ⟨B, hB, hAB⟩
    rcases hQR.1 hB with ⟨C, hC, hBC⟩
    exact ⟨C, hC, fun x hx => hBC (hAB hx)⟩
  · intro C hC
    let baseInside : Finset (Finset α) := Q.filter fun B => B ⊆ C
    let candidates : Finset (Finset α) :=
      baseInside.biUnion fun B => P.filter fun A => A ⊆ B
    have hsubset : (P.filter fun A => A ⊆ C) ⊆ candidates := by
      intro A hAfilter
      have hA : A ∈ P := (Finset.mem_filter.mp hAfilter).1
      have hAC : A ⊆ C := (Finset.mem_filter.mp hAfilter).2
      rcases hPQ.1 hA with ⟨B, hB, hAB⟩
      rcases hQR.1 hB with ⟨C', hC', hBC'⟩
      have hC'C : C' = C := by
        rcases hPnonempty hA with ⟨x, hxA⟩
        have hxC' : x ∈ C' := hBC' (hAB hxA)
        have hxC : x ∈ C := hAC hxA
        by_contra hne
        exact Finset.disjoint_left.mp (hRdisjoint hC' hC hne) hxC' hxC
      have hBbase : B ∈ baseInside := by
        have hBC : B ⊆ C := by
          intro x hx
          simpa [hC'C] using hBC' hx
        simp [baseInside, hB, hBC]
      exact Finset.mem_biUnion.mpr
        ⟨B, hBbase, Finset.mem_filter.mpr ⟨hA, hAB⟩⟩
    have hcandidates :
        candidates.card ≤ baseInside.card * r := by
      unfold candidates
      refine Finset.card_biUnion_le_card_mul _ _ _ ?_
      intro B hBbase
      have hB : B ∈ Q := (Finset.mem_filter.mp hBbase).1
      exact hPQ.2 hB
    have hbase : baseInside.card ≤ s := by
      exact hQR.2 hC
    calc
      (P.filter fun A => A ⊆ C).card ≤ candidates.card :=
        Finset.card_le_card hsubset
      _ ≤ baseInside.card * r := hcandidates
      _ ≤ s * r := Nat.mul_le_mul_right r hbase
      _ = r * s := by rw [Nat.mul_comm]

/-- Matrix-partition bounded refinement is transitive, with multiplied
bounds. -/
theorem rrefines_trans {n m r s : ℕ}
    {P Q R : MatrixPartition n m}
    (hPQ : RRefines P Q r) (hQR : RRefines Q R s) :
    RRefines P R (r * s) := by
  constructor
  · exact partsRRefine_trans_of_partition
      P.row_nonempty R.row_disjoint hPQ.1 hQR.1
  · exact partsRRefine_trans_of_partition
      P.col_nonempty R.col_disjoint hPQ.2 hQR.2

theorem rrefines_profilePartition_same_fuse {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {D : Division n (k + 2)}
    (hDmix : MatrixDivision.MixedValueAtMost M (MatrixDivision.same D) d)
    (i : Fin (k + 1))
    (hnew : colMixedValue M ((D.fuse i).part i) D ≤ d) :
    RRefines (MatrixDivision.profilePartition (d := d) M (MatrixDivision.same D))
      (MatrixDivision.profilePartition (d := d) M (MatrixDivision.same (D.fuse i)))
      ((2 * 2 ^ (d + 1)) * (2 * 2 ^ (d + 1))) := by
  classical
  let D₀ : MatrixDivision n n := MatrixDivision.same D
  have hrow : 0 < D₀.rowCuts := by
    dsimp [D₀, MatrixDivision.same]
    exact Nat.succ_pos k
  let i₀ : Fin D₀.rowCuts := i
  have hnewRow :
      colMixedValue M
        ((D₀.rowFuse hrow i₀).rowDiv.part
          ((finCongr
            (by simp [MatrixDivision.rowFuse]; omega :
              D₀.rowCuts = (D₀.rowFuse hrow i₀).rowCuts + 1)) i₀))
        (D₀.rowFuse hrow i₀).colDiv ≤ d := by
    simpa [D₀, i₀, MatrixDivision.same, MatrixDivision.rowFuse] using hnew
  have hDrowmix :
      MatrixDivision.MixedValueAtMost M (D₀.rowFuse hrow i₀) d :=
    MatrixDivision.mixedValueAtMost_rowFuse D₀ hDmix hrow i₀ hnewRow
  have hstep₁ :
      RRefines (MatrixDivision.profilePartition (d := d) M D₀)
        (MatrixDivision.profilePartition (d := d) M (D₀.rowFuse hrow i₀))
        (2 * Fintype.card Bool ^ (d + 1)) :=
    MatrixDivision.rrefines_profilePartition_of_hasExactFusion hDmix
      (Or.inl (MatrixDivision.hasRowFusion_rowFuse D₀ hrow i₀))
  let D₁ : MatrixDivision n n := D₀.rowFuse hrow i₀
  have hcol : 0 < D₁.colCuts := by
    dsimp [D₁, D₀, MatrixDivision.rowFuse, MatrixDivision.same]
    exact Nat.succ_pos k
  let j₀ : Fin D₁.colCuts := i
  have hstep₂ :
      RRefines (MatrixDivision.profilePartition (d := d) M D₁)
        (MatrixDivision.profilePartition (d := d) M (D₁.colFuse hcol j₀))
        (2 * Fintype.card Bool ^ (d + 1)) :=
    MatrixDivision.rrefines_profilePartition_of_hasExactFusion hDrowmix
      (Or.inr (MatrixDivision.hasColFusion_colFuse D₁ hcol j₀))
  have htrans := rrefines_trans hstep₁ hstep₂
  simpa [D₀, D₁, i₀, j₀, MatrixDivision.same, MatrixDivision.rowFuse,
    MatrixDivision.colFuse, Fintype.card_bool] using htrans

theorem rrefines_symContract {n r : ℕ}
    {P Q : MatrixPartition n n}
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPQ : RRefines P Q r)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B)
    (hsame : ∃ C ∈ Q.rowParts, A ⊆ C ∧ B ⊆ C) :
    RRefines (P.symContract hP hA hB hAB) Q r := by
  classical
  let Prow : MatrixPartition n n := P.rowContract hA hB hAB
  have hrow : RRefines Prow Q r :=
    MatrixPartition.rrefines_rowContract hPQ hA hB hAB hsame
  have hAcol : A ∈ Prow.colParts := by
    simpa [Prow] using (hP ▸ hA)
  have hBcol : B ∈ Prow.colParts := by
    simpa [Prow] using (hP ▸ hB)
  have hsame_col : ∃ C ∈ Q.colParts, A ⊆ C ∧ B ⊆ C := by
    rcases hsame with ⟨C, hC, hAC, hBC⟩
    exact ⟨C, by simpa using (hQ ▸ hC), hAC, hBC⟩
  simpa [MatrixPartition.symContract, Prow] using
    MatrixPartition.rrefines_colContract hrow hAcol hBcol hAB hsame_col

end MatrixPartition

/-- Finite descent for mirrored mixed-value divisions, assuming the local good
cut oracle. -/
theorem exists_sameMixedValueDivisionTail_of_goodCut
    {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M)
    (hgood :
      ∀ D : MatrixDivision n n,
        MatrixDivision.MixedValueAtMost M D d →
          ¬ MatrixDivision.IsCoarsest D →
            MatrixDivision.HasGoodCut M D d) :
    ∀ D₀ : MatrixDivision n n,
      (∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D) →
        MatrixDivision.MixedValueAtMost M D₀ d →
          Nonempty (SameMixedValueDivisionTail M d D₀) := by
  classical
  intro D₀
  refine WellFounded.induction
    (C := fun D₀ : MatrixDivision n n =>
      (∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D) →
        MatrixDivision.MixedValueAtMost M D₀ d →
          Nonempty (SameMixedValueDivisionTail M d D₀))
    (InvImage.wf MatrixDivision.cutCount <| (Nat.lt_wfRel).2)
    D₀ ?_
  intro D₀ ih hsame hmix
  by_cases hcoarse : MatrixDivision.IsCoarsest D₀
  · exact ⟨SameMixedValueDivisionTail.nil hsame hcoarse hmix⟩
  · rcases hsame with ⟨k, D, rfl⟩
    cases k with
    | zero =>
        exact False.elim (hcoarse (by simp [MatrixDivision.same, MatrixDivision.IsCoarsest]))
    | succ k =>
        have hcurrent_same :
            ∃ q : ℕ, ∃ E : Division n (q + 1),
              MatrixDivision.same D = MatrixDivision.same E := ⟨k + 1, D, rfl⟩
        have hcut := hgood (MatrixDivision.same D) hmix hcoarse
        rcases hcut with hrowgood | hcolgood
        · rcases hrowgood with ⟨hrow, i, hnewRow⟩
          let iD : Fin (k + 1) :=
            (finCongr (by rfl : (MatrixDivision.same D).rowCuts = k + 1)) i
          have hnew :
              colMixedValue M ((D.fuse iD).part iD) D ≤ d := by
            simpa [iD] using
              MatrixDivision.colMixedValue_fused_le_of_goodRow_same
                (D := D) hrow i hnewRow
          let E : MatrixDivision n n := MatrixDivision.same (D.fuse iD)
          have hEmix : MatrixDivision.MixedValueAtMost M E d := by
            simpa [E] using
              MatrixDivision.mixedValueAtMost_same_fuse_of_colMixedValue_fused_le
                hM D hmix iD hnew
          have hEsame :
              ∃ q : ℕ, ∃ F : Division n (q + 1), E = MatrixDivision.same F :=
            ⟨k, D.fuse iD, rfl⟩
          have hlt :
              MatrixDivision.cutCount E < MatrixDivision.cutCount (MatrixDivision.same D) := by
            simp [E, MatrixDivision.same, MatrixDivision.cutCount]
            omega
          rcases ih E hlt hEsame hEmix with ⟨S⟩
          have hrefine :
              MatrixPartition.RRefines
                (MatrixDivision.profilePartition (d := d) M (MatrixDivision.same D))
                (MatrixDivision.profilePartition (d := d) M E)
                (symmetricProfileRefinementBlockBound d) := by
            simpa [E, symmetricProfileRefinementBlockBound] using
              MatrixPartition.rrefines_profilePartition_same_fuse
                (M := M) hmix iD hnew
          exact ⟨SameMixedValueDivisionTail.cons hcurrent_same hmix hrefine S⟩
        · rcases hcolgood with ⟨hcol, j, hnewCol⟩
          let jD : Fin (k + 1) :=
            (finCongr (by rfl : (MatrixDivision.same D).colCuts = k + 1)) j
          have hnew :
              colMixedValue M ((D.fuse jD).part jD) D ≤ d := by
            simpa [jD] using
              MatrixDivision.colMixedValue_fused_le_of_goodCol_same
                (hM := hM) (D := D) hcol j hnewCol
          let E : MatrixDivision n n := MatrixDivision.same (D.fuse jD)
          have hEmix : MatrixDivision.MixedValueAtMost M E d := by
            simpa [E] using
              MatrixDivision.mixedValueAtMost_same_fuse_of_colMixedValue_fused_le
                hM D hmix jD hnew
          have hEsame :
              ∃ q : ℕ, ∃ F : Division n (q + 1), E = MatrixDivision.same F :=
            ⟨k, D.fuse jD, rfl⟩
          have hlt :
              MatrixDivision.cutCount E < MatrixDivision.cutCount (MatrixDivision.same D) := by
            simp [E, MatrixDivision.same, MatrixDivision.cutCount]
            omega
          rcases ih E hlt hEsame hEmix with ⟨S⟩
          have hrefine :
              MatrixPartition.RRefines
                (MatrixDivision.profilePartition (d := d) M (MatrixDivision.same D))
                (MatrixDivision.profilePartition (d := d) M E)
                (symmetricProfileRefinementBlockBound d) := by
            simpa [E, symmetricProfileRefinementBlockBound] using
              MatrixPartition.rrefines_profilePartition_same_fuse
                (M := M) hmix jD hnew
          exact ⟨SameMixedValueDivisionTail.cons hcurrent_same hmix hrefine S⟩

/-- A mirrored mixed-value tail starting from a finest division gives a
symmetric bounded-error refinement sequence. -/
theorem symmetricBoundedErrorRefinement_of_sameMixedValueTail
    {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (hd : 0 < d)
    {D₀ : MatrixDivision n n}
    (hfinest : MatrixDivision.IsFinest D₀)
    (S : SameMixedValueDivisionTail M d D₀) :
    Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
      (symmetricProfileRefinementBlockBound d)
      (symmetricProfileErrorBound d)) := by
  classical
  refine ⟨?_⟩
  exact
    { stepCount := S.stepCount + 1
      partition := fun i =>
        if h : i ≤ S.stepCount then
          MatrixDivision.profilePartition (d := d) M (S.division i)
        else
          (S.division S.stepCount).toPartition
      starts := by
        have h0finest : MatrixDivision.IsFinest (S.division 0) := by
          simpa [S.starts] using hfinest
        exact MatrixDivision.profilePartition_isFinest_of_isFinest M h0finest
      symmetric := by
        intro i hi
        by_cases hcur : i ≤ S.stepCount
        · rcases S.same i hcur with ⟨k, D, hD⟩
          simp [hcur, hD,
            MatrixDivision.profilePartition_same_isSymmetric_of_isSymmetricMatrix
              (d := d) hM D]
        · have hi_last : i = S.stepCount + 1 := by omega
          subst i
          have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
          rcases S.same S.stepCount le_rfl with ⟨k, D, hD⟩
          simpa [hnot, hD] using
            MatrixDivision.toPartition_isSymmetric_of_isSymmetric
              (MatrixDivision.same_isSymmetric D)
      ends := by
        have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
        simp [hnot, MatrixDivision.toPartition_isCoarsest S.ends]
      step_rrefines := by
        intro i hi
        by_cases hlast : i = S.stepCount
        · subst i
          have hnext : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
          simp [hnext]
          exact MatrixPartition.rrefines_mono
            (by
              have hpow : 0 < 2 ^ (d + 1) :=
                pow_pos (by decide : 0 < 2) _
              have hleft : 2 ^ (d + 1) ≤ 2 * 2 ^ (d + 1) :=
                Nat.le_mul_of_pos_left (2 ^ (d + 1)) (by decide : 0 < 2)
              have hfactor_pos : 0 < 2 * 2 ^ (d + 1) :=
                Nat.mul_pos (by decide : 0 < 2) hpow
              calc
                Fintype.card Bool ^ (d + 1) = 2 ^ (d + 1) := by simp
                _ ≤ 2 * 2 ^ (d + 1) := hleft
                _ ≤ symmetricProfileRefinementBlockBound d := by
                  simpa [symmetricProfileRefinementBlockBound] using
                    Nat.le_mul_of_pos_right (2 * 2 ^ (d + 1)) hfactor_pos)
            (MatrixDivision.profilePartition_rrefines_toPartition
              (d := d) M (S.division S.stepCount))
        · have hiS : i < S.stepCount := by omega
          have hcur : i ≤ S.stepCount := by omega
          have hnext : i + 1 ≤ S.stepCount := by omega
          simpa [hcur, hnext] using S.step_rrefines i hiS
      errorValue_le := by
        intro i hi
        by_cases hcur : i ≤ S.stepCount
        · simp [hcur, symmetricProfileErrorBound]
          exact MatrixDivision.errorValueAtMost_profilePartition
            (S.mixedValue_le i hcur)
        · have hi_last : i = S.stepCount + 1 := by omega
          subst i
          have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
          simp [hnot, symmetricProfileErrorBound]
          have hone :
              ErrorValueAtMost M (S.division S.stepCount).toPartition 1 :=
            errorValueAtMost_one_of_isCoarsest M
              (MatrixDivision.toPartition_isCoarsest S.ends)
          have hle : 1 ≤ d * 2 ^ (d + 1) := by
            have hpow : 0 < 2 ^ (d + 1) := pow_pos (by decide : 0 < 2) _
            exact Nat.succ_le_of_lt (Nat.mul_pos hd hpow)
          exact MatrixPartition.errorValueAtMost_mono hle hone }

namespace SymmetricMatrixContractionTail

/-- The empty symmetric contraction tail at a partition whose error is already
bounded. -/
def nil {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {P : MatrixPartition n n}
    (hP : P.IsSymmetric) (hErr : ErrorValueAtMost M P d)
    (hCoarse : MatrixPartition.IsCoarsest P) :
    SymmetricMatrixContractionTail M d P where
  stepCount := 0
  partition := fun _ => P
  starts := rfl
  symmetric := by intro i hi; simpa using hP
  ends := hCoarse
  step_contracts := by intro i hi; omega
  errorValue_le := by intro i hi; simpa using hErr

/-- Prepend one paired symmetric contraction to a symmetric contraction tail. -/
noncomputable def cons {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {P Q : MatrixPartition n n}
    (hPQ : MatrixPartition.IsSymmetricContraction P Q)
    (hP : P.IsSymmetric)
    (hPerr : ErrorValueAtMost M P d)
    (S : SymmetricMatrixContractionTail M d Q) :
    SymmetricMatrixContractionTail M d P where
  stepCount := S.stepCount + 1
  partition := fun i =>
    match i with
    | 0 => P
    | j + 1 => S.partition j
  starts := rfl
  symmetric := by
    intro i hi
    cases i with
    | zero =>
        simpa using hP
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.symmetric j hj
  ends := by
    simpa using S.ends
  step_contracts := by
    intro i hi
    cases i with
    | zero =>
        simpa [S.starts] using hPQ
    | succ j =>
        have hj : j < S.stepCount := by omega
        simpa using S.step_contracts j hj
  errorValue_le := by
    intro i hi
    cases i with
    | zero =>
        simpa using hPerr
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.errorValue_le j hj

/-- Expand one symmetric bounded-refinement step into paired row/column
contractions before an already constructed symmetric tail from the coarse
partition. -/
theorem exists_of_symmetric_rrefines {n r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool} :
    ∀ (P Q : MatrixPartition n n),
      P.IsSymmetric →
      Q.IsSymmetric →
      MatrixPartition.RRefines P Q r →
      ErrorValueAtMost M Q t →
      SymmetricMatrixContractionTail M (r * t) Q →
      Nonempty (SymmetricMatrixContractionTail M (r * t) P) := by
  classical
  intro P
  refine WellFounded.induction
    (C := fun P : MatrixPartition n n =>
      ∀ Q : MatrixPartition n n,
        P.IsSymmetric →
        Q.IsSymmetric →
        MatrixPartition.RRefines P Q r →
        ErrorValueAtMost M Q t →
        SymmetricMatrixContractionTail M (r * t) Q →
        Nonempty (SymmetricMatrixContractionTail M (r * t) P))
    (InvImage.wf (fun P : MatrixPartition n n => P.rowParts.card)
      <| (Nat.lt_wfRel).2)
    P ?_
  intro P ih Q hP hQ hPQ hQerr T
  have hPerr : ErrorValueAtMost M P (r * t) :=
    MatrixPartition.errorValueAtMost_of_rrefines hPQ hQerr
  by_cases hrow : P.rowParts = Q.rowParts
  · have hcol : P.colParts = Q.colParts := by
      calc
        P.colParts = P.rowParts := hP.symm
        _ = Q.rowParts := hrow
        _ = Q.colParts := hQ
    have hPQeq : P = Q := MatrixPartition.ext_parts hrow hcol
    subst Q
    exact ⟨T⟩
  · rcases MatrixPartition.exists_two_rowParts_subset_of_refines_ne
      hPQ.1.1 hrow with
      ⟨C, hC, A, hA, B, hB, hAB, hAC, hBC⟩
    let P' : MatrixPartition n n := P.symContract hP hA hB hAB
    have hP'sym : P'.IsSymmetric :=
      MatrixPartition.isSymmetric_symContract P hP hA hB hAB
    have hP'Q : MatrixPartition.RRefines P' Q r :=
      MatrixPartition.rrefines_symContract hP hQ hPQ hA hB hAB
        ⟨C, hC, hAC, hBC⟩
    have hlt : P'.rowParts.card < P.rowParts.card := by
      simpa [P'] using
        MatrixPartition.rowParts_card_symContract_lt P hP hA hB hAB
    rcases ih P' hlt Q hP'sym hQ hP'Q hQerr T with ⟨T'⟩
    exact ⟨SymmetricMatrixContractionTail.cons
      (MatrixPartition.isSymmetricContraction_symContract P hP hA hB hAB)
      hP hPerr T'⟩

end SymmetricMatrixContractionTail

/-- Starting from any index in a symmetric bounded-refinement partition
sequence, the remaining suffix expands to paired symmetric contractions with
the multiplicative error bound `r * t`. -/
theorem exists_symmetricMatrixContractionTail_of_symmetricBoundedErrorRefinement
    {n r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hr : 0 < r)
    (S : SymmetricBoundedErrorRefinementPartitionSequence M r t) :
    ∀ i, i ≤ S.stepCount →
      Nonempty (SymmetricMatrixContractionTail M (r * t) (S.partition i)) := by
  classical
  intro i hi
  have ht_le : t ≤ r * t := by
    cases r with
    | zero => omega
    | succ r =>
        rw [Nat.succ_mul]
        exact Nat.le_add_left t (r * t)
  refine WellFounded.induction
    (C := fun a : {i // i ≤ S.stepCount} =>
      Nonempty (SymmetricMatrixContractionTail M (r * t) (S.partition a.1)))
    (InvImage.wf
      (fun a : {i // i ≤ S.stepCount} => S.stepCount - a.1)
      <| (Nat.lt_wfRel).2)
    ⟨i, hi⟩ ?_
  intro a ih
  by_cases hlast : a.1 = S.stepCount
  · have hsym : (S.partition a.1).IsSymmetric := by
      simpa [hlast] using S.symmetric S.stepCount le_rfl
    have herr : ErrorValueAtMost M (S.partition a.1) (r * t) := by
      exact MatrixPartition.errorValueAtMost_mono ht_le
        (by simpa [hlast] using S.errorValue_le S.stepCount le_rfl)
    have hcoarse : MatrixPartition.IsCoarsest (S.partition a.1) := by
      simpa [hlast] using S.ends
    exact ⟨SymmetricMatrixContractionTail.nil hsym herr hcoarse⟩
  · have hlt : a.1 < S.stepCount := lt_of_le_of_ne a.2 hlast
    let b : {i // i ≤ S.stepCount} := ⟨a.1 + 1, by omega⟩
    have hdec : S.stepCount - b.1 < S.stepCount - a.1 := by
      dsimp [b]
      omega
    rcases ih b hdec with ⟨Tnext⟩
    have hstep : MatrixPartition.RRefines
        (S.partition a.1) (S.partition (a.1 + 1)) r :=
      S.step_rrefines a.1 hlt
    have hnext_err : ErrorValueAtMost M (S.partition (a.1 + 1)) t :=
      S.errorValue_le (a.1 + 1) (by omega)
    exact SymmetricMatrixContractionTail.exists_of_symmetric_rrefines
      (S.partition a.1) (S.partition (a.1 + 1))
      (S.symmetric a.1 a.2)
      (S.symmetric (a.1 + 1) (by omega))
      hstep hnext_err Tnext

/-- Symmetric Lemma 8: a symmetric bounded-refinement partition sequence
expands into a symmetric matrix contraction sequence, using one paired
row/column contraction block for each fine merge. -/
theorem symmetricMatrixTwinWidthAtMost_of_symmetricBoundedErrorRefinement
    {n r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hr : 0 < r)
    (S : Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M r t)) :
    SymmetricMatrixTwinWidthAtMost M (r * t) := by
  rcases S with ⟨S⟩
  rcases exists_symmetricMatrixContractionTail_of_symmetricBoundedErrorRefinement
      hr S 0 (Nat.zero_le S.stepCount) with ⟨T⟩
  exact ⟨{
    stepCount := T.stepCount
    partition := T.partition
    symmetric := T.symmetric
    starts := by
      rw [T.starts]
      exact S.starts
    ends := T.ends
    step_contracts := T.step_contracts
    errorValue_le := T.errorValue_le
  }⟩

/-- Symmetric Lemma 8 with the numerical parameters used by Theorem 10 for
Boolean matrices. -/
theorem symmetricMatrixTwinWidthAtMost_of_theorem10SymmetricErrorRefinement
    {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (S : Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
      (2 * 2 ^ (d + 1)) (d * 2 ^ (d + 1)))) :
    SymmetricMatrixTwinWidthAtMost M
      (theorem10AlphabetErrorRefinementBound 2 d) := by
  have hr : 0 < 2 * 2 ^ (d + 1) := by
    exact Nat.mul_pos (by decide : 0 < 2) (pow_pos (by decide : 0 < 2) _)
  have h := symmetricMatrixTwinWidthAtMost_of_symmetricBoundedErrorRefinement
    (M := M) (r := 2 * 2 ^ (d + 1)) (t := d * 2 ^ (d + 1)) hr S
  have hmul :
      (2 * 2 ^ (d + 1)) * (d * 2 ^ (d + 1)) =
        theorem10AlphabetErrorRefinementBound 2 d := by
    unfold theorem10AlphabetErrorRefinementBound
    have hp : 2 ^ (d + 1) * 2 ^ (d + 1) = 2 ^ (2 * (d + 1)) := by
      rw [← pow_add]
      have hexp : d + 1 + (d + 1) = 2 * (d + 1) := by omega
      simp [hexp]
    calc
      (2 * 2 ^ (d + 1)) * (d * 2 ^ (d + 1))
          = 2 * d * (2 ^ (d + 1) * 2 ^ (d + 1)) := by ring
      _ = 2 * d * 2 ^ (2 * (d + 1)) := by rw [hp]
  simpa [hmul] using h

theorem SymmetricMatrixTwinWidthAtMost.mono {n d e : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (h : SymmetricMatrixTwinWidthAtMost M d) (hde : d ≤ e) :
    SymmetricMatrixTwinWidthAtMost M e := by
  rcases h with ⟨S⟩
  exact ⟨S.mono hde⟩

theorem symmetricMatrixTwinWidthAtMost_zero (d : ℕ)
    (M : _root_.Matrix (Fin 0) (Fin 0) Bool) :
    SymmetricMatrixTwinWidthAtMost M d := by
  refine ⟨?_⟩
  exact
    { stepCount := 0
      partition := fun _ => MatrixPartition.emptyZero
      symmetric := by intro i hi; exact MatrixPartition.emptyZero_isSymmetric
      starts := MatrixPartition.emptyZero_isFinest
      ends := MatrixPartition.emptyZero_isCoarsest
      step_contracts := by intro i hi; omega
      errorValue_le := by
        intro i hi
        simp [MatrixPartition.emptyZero, ErrorValueAtMost, rowErrorSet, colErrorSet] }

/-- Empty square matrices have the degenerate symmetric bounded-refinement
sequence for any numerical parameters. -/
theorem symmetricBoundedErrorRefinement_zero (r t : ℕ)
    (M : _root_.Matrix (Fin 0) (Fin 0) Bool) :
    Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M r t) := by
  refine ⟨?_⟩
  exact
    { stepCount := 0
      partition := fun _ => MatrixPartition.emptyZero
      starts := MatrixPartition.emptyZero_isFinest
      symmetric := by intro i hi; exact MatrixPartition.emptyZero_isSymmetric
      ends := MatrixPartition.emptyZero_isCoarsest
      step_rrefines := by intro i hi; omega
      errorValue_le := by
        intro i hi
        simp [MatrixPartition.emptyZero, ErrorValueAtMost, rowErrorSet, colErrorSet] }

/-- The explicit width bound obtained by the mirrored symmetric construction
from a `t`-mixed-free square Boolean matrix.  The profile-refinement factor is
squared because each one-sided fusion is immediately mirrored across the
diagonal before the next mixed-value descent step. -/
def symmetricMatrixTwinWidthBoundOfMixedFree (t : ℕ) : ℕ :=
  let d := lemma13MixedValueBound marcusTardosConstant t
  symmetricProfileRefinementBlockBound d * symmetricProfileErrorBound d

/-- The finest positive square matrix division is a same row/column division. -/
theorem finest_same {n : ℕ} (hn : 0 < n) :
    ∃ k : ℕ, ∃ D : Division n (k + 1),
      MatrixDivision.finest hn hn = MatrixDivision.same D := by
  refine ⟨n - 1,
    Division.castIndex (by omega : n = (n - 1) + 1) (Division.singleton n), ?_⟩
  simp [MatrixDivision.finest, MatrixDivision.same]

/-- A mixed-free symmetric Boolean matrix admits the mirrored bounded-error
profile-refinement sequence.  This is the fully formalized symmetric version
of the Section 5.8 refinement construction: at every descent step the chosen
row cut or column cut is fused together with its mirror. -/
theorem symmetricBoundedErrorRefinement_of_mixedFree
    {n t : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool)
    (hM : IsSymmetricMatrix M)
    (hfree : MixedFree M t) :
    Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
      (symmetricProfileRefinementBlockBound
        (lemma13MixedValueBound marcusTardosConstant t))
      (symmetricProfileErrorBound
        (lemma13MixedValueBound marcusTardosConstant t))) := by
  classical
  by_cases hn0 : n = 0
  · subst n
    exact symmetricBoundedErrorRefinement_zero _ _ M
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let d : ℕ := lemma13MixedValueBound marcusTardosConstant t
    have htpos : 0 < t := by
      cases t with
      | zero =>
          exact False.elim (hfree (hasMixedMinor_zero M))
      | succ t =>
          exact Nat.succ_pos t
    have hd : 0 < d := by
      dsimp [d, lemma13MixedValueBound]
      exact Nat.mul_pos (by decide : 0 < 20)
        (IsMarcusTardosConstant.pos
          (isMarcusTardosConstant_marcusTardosConstant t) htpos)
    let D₀ : MatrixDivision n n := MatrixDivision.finest hn hn
    have hsame :
        ∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D := by
      simpa [D₀] using finest_same hn
    have hfinest : MatrixDivision.IsFinest D₀ := by
      simpa [D₀] using MatrixDivision.finest_isFinest hn hn
    have hmix : MatrixDivision.MixedValueAtMost M D₀ d :=
      MatrixDivision.mixedValueAtMost_of_isFinest hfinest
    have hgood :
        ∀ D : MatrixDivision n n,
          MatrixDivision.MixedValueAtMost M D d →
            ¬ MatrixDivision.IsCoarsest D →
              MatrixDivision.HasGoodCut M D d := by
      simpa [d] using
        MatrixDivision.hasGoodCut_of_marcusTardos
          isMarcusTardosConstant_marcusTardosConstant M t hfree
    rcases exists_sameMixedValueDivisionTail_of_goodCut
        hM hgood D₀ hsame hmix with ⟨S⟩
    simpa [d] using
      symmetricBoundedErrorRefinement_of_sameMixedValueTail
        hM hd hfinest S

/-- The mirrored matrix construction turns a symmetric mixed-free Boolean
matrix into a paired row/column contraction sequence. -/
theorem symmetricMatrixTwinWidthAtMost_of_mixedFree
    {n t : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool)
    (hM : IsSymmetricMatrix M)
    (hfree : MixedFree M t) :
    SymmetricMatrixTwinWidthAtMost M
      (symmetricMatrixTwinWidthBoundOfMixedFree t) := by
  classical
  let d : ℕ := lemma13MixedValueBound marcusTardosConstant t
  have hrefine :
      Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
        (symmetricProfileRefinementBlockBound d)
        (symmetricProfileErrorBound d)) := by
    simpa [d] using symmetricBoundedErrorRefinement_of_mixedFree M hM hfree
  have hr : 0 < symmetricProfileRefinementBlockBound d := by
    have hpow : 0 < 2 ^ (d + 1) := pow_pos (by decide : 0 < 2) _
    have hfactor : 0 < 2 * 2 ^ (d + 1) :=
      Nat.mul_pos (by decide : 0 < 2) hpow
    simp [symmetricProfileRefinementBlockBound, Nat.mul_pos hfactor hfactor]
  simpa [symmetricMatrixTwinWidthBoundOfMixedFree, d] using
    symmetricMatrixTwinWidthAtMost_of_symmetricBoundedErrorRefinement
      (M := M) (r := symmetricProfileRefinementBlockBound d)
      (t := symmetricProfileErrorBound d) hr hrefine

/-- The mirrored version of Theorem 10 needed by Theorem 14.

The symmetry hypothesis is essential: the paper applies this construction to
ordered adjacency matrices of undirected graphs, where every row operation can
be mirrored by the corresponding column operation without increasing the
mixed-value/error bound. -/
def SymmetricMatrixTwinWidthBoundedByMixedFree : Prop :=
  ∀ {n t : ℕ} (M : _root_.Matrix (Fin n) (Fin n) Bool),
    IsSymmetricMatrix M →
    MixedFree M t →
      SymmetricMatrixTwinWidthAtMost M
        (symmetricMatrixTwinWidthBoundOfMixedFree t)

/-- Symmetric refinement constructor needed for the mirrored matrix
construction in Theorem 14.  It states exactly the remaining refinement task:
from a symmetric `t`-mixed-free Boolean matrix, build the symmetric
bounded-refinement sequence with the Section 5.8 parameters. -/
def SymmetricMatrixErrorRefinementBoundedByMixedFree : Prop :=
  ∀ {n t : ℕ} (M : _root_.Matrix (Fin n) (Fin n) Bool),
    IsSymmetricMatrix M →
    MixedFree M t →
      Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
        (symmetricProfileRefinementBlockBound
          (lemma13MixedValueBound marcusTardosConstant t))
        (symmetricProfileErrorBound
          (lemma13MixedValueBound marcusTardosConstant t)))

/-- The mirrored matrix construction follows from the symmetric
bounded-refinement constructor by expanding every refinement step into paired
row/column contractions. -/
theorem symmetricMatrixTwinWidthBoundedByMixedFree_of_symmetricErrorRefinement
    (hrefine : SymmetricMatrixErrorRefinementBoundedByMixedFree) :
    SymmetricMatrixTwinWidthBoundedByMixedFree := by
  intro n t M hsym hfree
  let d : ℕ := lemma13MixedValueBound marcusTardosConstant t
  have hr : 0 < symmetricProfileRefinementBlockBound d := by
    have hpow : 0 < 2 ^ (d + 1) := pow_pos (by decide : 0 < 2) _
    have hfactor : 0 < 2 * 2 ^ (d + 1) :=
      Nat.mul_pos (by decide : 0 < 2) hpow
    simp [symmetricProfileRefinementBlockBound, Nat.mul_pos hfactor hfactor]
  simpa [symmetricMatrixTwinWidthBoundOfMixedFree, d] using
    symmetricMatrixTwinWidthAtMost_of_symmetricBoundedErrorRefinement
      (M := M) (r := symmetricProfileRefinementBlockBound d)
      (t := symmetricProfileErrorBound d) hr
      (by simpa [d] using hrefine M hsym hfree)

/-- Public theorem: the mirrored matrix construction is fully formalized for
finite square Boolean matrices. -/
theorem symmetricMatrixTwinWidthBoundedByMixedFree :
    SymmetricMatrixTwinWidthBoundedByMixedFree := by
  intro n t M hsym hfree
  exact symmetricMatrixTwinWidthAtMost_of_mixedFree M hsym hfree

end Matrix
end Lax4Proofs.TwinWidth
