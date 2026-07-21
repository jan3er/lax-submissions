import Lax4Proofs.Source.TwinWidth.Matrix.Fusion
import Lax4Proofs.Source.TwinWidth.Matrix.MarcusTardos
import Lax4Proofs.Source.TwinWidth.Matrix.TwinWidth

/-!
# Division sequences with bounded mixed value

This file records the formal target of Lemma 13 from Section 5.7.  A matrix
division has a row division and a column division, each with at least one part.
Its mixed value is the maximum of the one-sided mixed values of all row and
column parts.

The proof of Lemma 13 is split into two layers: the local greedy-fusion step,
which uses Marcus--Tardos on the auxiliary matrix of mixed zones, and the
finite descent argument turning that step into a full division sequence.
-/

namespace Lax4Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

/-- The auxiliary matrix whose entries record which zones of a pair of
divisions are mixed. -/
noncomputable def mixedZoneMatrix {n m k l : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m l) :
    _root_.Matrix (Fin k) (Fin l) Bool :=
  by
    classical
    exact fun i j => decide (ZoneMixed M (R.part i) (C.part j))

theorem mixedZoneMatrix_eq_true_iff {n m k l : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m l) (i : Fin k) (j : Fin l) :
    mixedZoneMatrix M R C i j = true ↔ ZoneMixed M (R.part i) (C.part j) := by
  classical
  simp [mixedZoneMatrix]

theorem zoneMixed_of_subset {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R₁ R₂ : Finset (Fin n)} {C₁ C₂ : Finset (Fin m)}
    (hR : R₁ ⊆ R₂) (hC : C₁ ⊆ C₂)
    (hmix : ZoneMixed M R₁ C₁) :
    ZoneMixed M R₂ C₂ := by
  constructor
  · intro hv
    exact hmix.1 (by
      intro r₁ r₂ hr₁ hr₂ c hc
      exact hv (hR hr₁) (hR hr₂) (hC hc))
  · intro hh
    exact hmix.2 (by
      intro r hr c₁ c₂ hc₁ hc₂
      exact hh (hR hr) (hC hc₁) (hC hc₂))

/-- A mixed zone remains mixed after coarsening the column division part that
contains it. -/
theorem zoneMixed_col_coarsen_of_zoneMixed {n m l q : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Division m l} {I : Division l q}
    {a : Fin q} {j : Fin l}
    (hj : j ∈ I.part a)
    (hmix : ZoneMixed M R (C.part j)) :
    ZoneMixed M R ((C.coarsen I).part a) :=
  zoneMixed_of_subset (by intro r hr; exact hr) (C.part_subset_coarsen_part I hj) hmix

/-- A mixed zone remains mixed after coarsening the row division part that
contains it. -/
theorem zoneMixed_row_coarsen_of_zoneMixed {n m k q : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {I : Division k q} {C : Finset (Fin m)}
    {a : Fin q} {i : Fin k}
    (hi : i ∈ I.part a)
    (hmix : ZoneMixed M (R.part i) C) :
    ZoneMixed M ((R.coarsen I).part a) C :=
  zoneMixed_of_subset (R.part_subset_coarsen_part I hi) (by intro c hc; exact hc) hmix

/-- If the two sides of a mixed column cut are grouped into the same coarsened
column part, then the corresponding coarsened zone is mixed. -/
theorem zoneMixed_col_coarsen_of_colCutMixed {n m l q : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Division m (l + 1)} {I : Division (l + 1) q}
    {a : Fin q} {j : Fin l}
    (hj₀ : j.castSucc ∈ I.part a) (hj₁ : j.succ ∈ I.part a)
    (hmix : ColCutMixed M R C j) :
    ZoneMixed M R ((C.coarsen I).part a) := by
  constructor
  · intro hv
    exact hmix.1 ⟨
      (by
        intro r₁ r₂ hr₁ hr₂
        exact hv hr₁ hr₂
          (C.part_subset_coarsen_part I hj₀ (C.last_mem j.castSucc))),
      (by
        intro r₁ r₂ hr₁ hr₂
        exact hv hr₁ hr₂
          (C.part_subset_coarsen_part I hj₁ (C.first_mem j.succ)))⟩
  · intro hh
    exact hmix.2 (by
      intro r hr
      exact hh hr
        (C.part_subset_coarsen_part I hj₀ (C.last_mem j.castSucc))
        (C.part_subset_coarsen_part I hj₁ (C.first_mem j.succ)))

/-- Row-cut version of `zoneMixed_col_coarsen_of_colCutMixed`. -/
theorem zoneMixed_row_coarsen_of_rowCutMixed {n m k q : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n (k + 1)} {I : Division (k + 1) q} {C : Finset (Fin m)}
    {a : Fin q} {i : Fin k}
    (hi₀ : i.castSucc ∈ I.part a) (hi₁ : i.succ ∈ I.part a)
    (hmix : RowCutMixed M R C i) :
    ZoneMixed M ((R.coarsen I).part a) C := by
  constructor
  · intro hv
    exact hmix.1 (by
      intro c hc
      exact hv
        (R.part_subset_coarsen_part I hi₀ (R.last_mem i.castSucc))
        (R.part_subset_coarsen_part I hi₁ (R.first_mem i.succ))
        hc)
  · intro hh
    exact hmix.2 ⟨
      (by
        intro c₁ c₂ hc₁ hc₂
        exact hh
          (R.part_subset_coarsen_part I hi₀ (R.last_mem i.castSucc))
          hc₁ hc₂),
      (by
        intro c₁ c₂ hc₁ hc₂
        exact hh
          (R.part_subset_coarsen_part I hi₁ (R.first_mem i.succ))
          hc₁ hc₂)⟩

/-- A grid minor in the auxiliary mixed-zone matrix induces a mixed minor in
the original matrix by coarsening the row and column divisions. -/
theorem hasMixedMinor_of_mixedZoneMatrix_hasGridMinor {n m k l t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m l}
    (hgrid : HasGridMinor (mixedZoneMatrix M R C) t) :
    HasMixedMinor M t := by
  rcases hgrid with ht | hgrid
  · exact Or.inl ht
  · rcases hgrid with ⟨IR, IC, hcell⟩
    refine Or.inr ⟨R.coarsen IR, C.coarsen IC, ?_⟩
    intro a b
    rcases hcell a b with ⟨i, hi, j, hj, htrue⟩
    have hmix : ZoneMixed M (R.part i) (C.part j) :=
      (mixedZoneMatrix_eq_true_iff M R C i j).mp htrue
    have hR : R.part i ⊆ (R.coarsen IR).part a :=
      R.part_subset_coarsen_part IR hi
    have hC : C.part j ⊆ (C.coarsen IC).part b :=
      C.part_subset_coarsen_part IC hj
    have hbig : ZoneMixed M ((R.coarsen IR).part a) ((C.coarsen IC).part b) :=
      zoneMixed_of_subset hR hC hmix
    simpa [CellMixed, CellVertical, CellHorizontal,
      ZoneMixed, ZoneVertical, ZoneHorizontal] using hbig

/-- Contradiction form used in Lemma 13: a `t`-grid minor in the auxiliary
mixed-zone matrix contradicts `t`-mixed-freeness of the original matrix. -/
theorem mixedFree_not_mixedZoneMatrix_hasGridMinor {n m k l t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m l}
    (hfree : MixedFree M t) :
    ¬ HasGridMinor (mixedZoneMatrix M R C) t := by
  intro hgrid
  exact hfree (hasMixedMinor_of_mixedZoneMatrix_hasGridMinor hgrid)

/-- Marcus--Tardos counting form for the auxiliary mixed-zone matrix: in a
`t`-mixed-free matrix, the auxiliary matrix has fewer than `c * max k l` mixed
zones whenever `c` is a Marcus--Tardos constant for `t`. -/
theorem oneEntries_mixedZoneMatrix_lt_of_mixedFree {n m k l t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m l}
    (hMT : IsMarcusTardosConstant t c)
    (hfree : MixedFree M t)
    (hpos : 0 < max k l) :
    (oneEntries (mixedZoneMatrix M R C)).card < c * max k l := by
  by_contra hnot
  have hden : c * max k l ≤ (oneEntries (mixedZoneMatrix M R C)).card :=
    Nat.le_of_not_gt hnot
  exact mixedFree_not_mixedZoneMatrix_hasGridMinor (R := R) (C := C) hfree
    (hMT (mixedZoneMatrix M R C) hpos hden)

/-- A row/column division of a finite matrix.  The fields `rowCuts` and
`colCuts` are one less than the number of row and column parts; this matches the
`k + 1` indexing used by mixed cuts. -/
structure MatrixDivision (n m : ℕ) where
  /-- One less than the number of row parts. -/
  rowCuts : ℕ
  /-- One less than the number of column parts. -/
  colCuts : ℕ
  /-- Consecutive row parts. -/
  rowDiv : Division n (rowCuts + 1)
  /-- Consecutive column parts. -/
  colDiv : Division m (colCuts + 1)

namespace MatrixDivision

/-- The number of cuts in a matrix division.  A fusion step decreases this
measure by exactly one. -/
def cutCount {n m : ℕ} (D : MatrixDivision n m) : ℕ :=
  D.rowCuts + D.colCuts

/-- The canonical finest matrix division of a positive-size matrix. -/
noncomputable def finest {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    MatrixDivision n m where
  rowCuts := n - 1
  colCuts := m - 1
  rowDiv := Division.castIndex (by omega : n = (n - 1) + 1) (Division.singleton n)
  colDiv := Division.castIndex (by omega : m = (m - 1) + 1) (Division.singleton m)

/-- A matrix division has mixed value at most `d` if every column part has
mixed value at most `d` on the row division, and every row part has mixed value
at most `d` on the column division. -/
def MixedValueAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (d : ℕ) : Prop :=
  (∀ j : Fin (D.colCuts + 1),
      rowMixedValue M D.rowDiv (D.colDiv.part j) ≤ d) ∧
    ∀ i : Fin (D.rowCuts + 1),
      colMixedValue M (D.rowDiv.part i) D.colDiv ≤ d

/-- The finest division: every row part and every column part is a singleton.
The cover field of `Division` then ensures that every row and column appears. -/
def IsFinest {n m : ℕ} (D : MatrixDivision n m) : Prop :=
  (∀ i : Fin (D.rowCuts + 1), ∃ r : Fin n, D.rowDiv.part i = {r}) ∧
    ∀ j : Fin (D.colCuts + 1), ∃ c : Fin m, D.colDiv.part j = {c}

theorem finest_isFinest {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    IsFinest (finest hn hm) := by
  constructor
  · intro i
    simp [finest, Division.castIndex, Division.singleton]
  · intro j
    simp [finest, Division.castIndex, Division.singleton]

/-- The coarsest division: one row part and one column part. -/
def IsCoarsest {n m : ℕ} (D : MatrixDivision n m) : Prop :=
  D.rowCuts = 0 ∧ D.colCuts = 0

/-- A fusion step between divisions.  The first disjunct is a row fusion and
the second is a column fusion; the exact part-identification relation is kept
as the next local API to build on top of Lemma 12. -/
def HasFusionShape {n m : ℕ} (D E : MatrixDivision n m) : Prop :=
  (D.rowCuts = E.rowCuts + 1 ∧ D.colCuts = E.colCuts) ∨
    (D.rowCuts = E.rowCuts ∧ D.colCuts = E.colCuts + 1)

/-- Exact row-fusion data: `E` is obtained from `D` by merging one specified
pair of consecutive row parts and leaving the column division unchanged. -/
def HasRowFusion {n m : ℕ} (D E : MatrixDivision n m) : Prop :=
  ∃ hrow : D.rowCuts = E.rowCuts + 1,
    ∃ hcol : D.colCuts = E.colCuts,
      ∃ i : Fin (E.rowCuts + 1),
        Division.IsFusionAt
          (Division.castIndex (by omega : D.rowCuts + 1 = E.rowCuts + 2) D.rowDiv)
          E.rowDiv i ∧
          ∀ j : Fin (E.colCuts + 1),
            E.colDiv.part j =
              (Division.castIndex (by omega : D.colCuts + 1 = E.colCuts + 1) D.colDiv).part j

/-- Exact column-fusion data, dual to `HasRowFusion`. -/
def HasColFusion {n m : ℕ} (D E : MatrixDivision n m) : Prop :=
  ∃ hrow : D.rowCuts = E.rowCuts,
    ∃ hcol : D.colCuts = E.colCuts + 1,
      ∃ j : Fin (E.colCuts + 1),
        (∀ i : Fin (E.rowCuts + 1),
            E.rowDiv.part i =
              (Division.castIndex (by omega : D.rowCuts + 1 = E.rowCuts + 1) D.rowDiv).part i) ∧
          Division.IsFusionAt
            (Division.castIndex (by omega : D.colCuts + 1 = E.colCuts + 2) D.colDiv)
            E.colDiv j

/-- An exact fusion is either an exact row fusion or an exact column fusion. -/
def HasExactFusion {n m : ℕ} (D E : MatrixDivision n m) : Prop :=
  HasRowFusion D E ∨ HasColFusion D E

/-- Fuse one row cut of a matrix division.  The input index is a boundary
between consecutive row parts. -/
noncomputable def rowFuse {n m : ℕ} (D : MatrixDivision n m)
    (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts) : MatrixDivision n m where
  rowCuts := D.rowCuts - 1
  colCuts := D.colCuts
  rowDiv :=
    (Division.castIndex
      (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv).fuse
        ((finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i)
  colDiv := D.colDiv

/-- Fuse one column cut of a matrix division. -/
noncomputable def colFuse {n m : ℕ} (D : MatrixDivision n m)
    (hcol : 0 < D.colCuts) (j : Fin D.colCuts) : MatrixDivision n m where
  rowCuts := D.rowCuts
  colCuts := D.colCuts - 1
  rowDiv := D.rowDiv
  colDiv :=
    (Division.castIndex
      (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv).fuse
        ((finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j)

/-- Row division obtained by grouping row parts in left pairs
`0,1`, `2,3`, ... with a possible leftover absorbed into the last group. -/
noncomputable def rowPairLeftDiv {n m : ℕ} (D : MatrixDivision n m)
    (hrow : 0 < D.rowCuts) : Division n (Division.pairCount (D.rowCuts + 1)) :=
  D.rowDiv.coarsen
    (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))

/-- Row division obtained by the shifted right pairing. -/
noncomputable def rowPairRightDiv {n m : ℕ} (D : MatrixDivision n m)
    (hrow : 0 < D.rowCuts) : Division n (Division.pairCount (D.rowCuts + 1)) :=
  D.rowDiv.coarsen
    (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega))

/-- Column division obtained by grouping column parts in left pairs. -/
noncomputable def colPairLeftDiv {n m : ℕ} (D : MatrixDivision n m)
    (hcol : 0 < D.colCuts) : Division m (Division.pairCount (D.colCuts + 1)) :=
  D.colDiv.coarsen
    (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))

/-- Column division obtained by grouping column parts in shifted right pairs:
the first part is initially isolated, then `1,2`, `3,4`, ... are grouped,
with a possible tail absorbed into the last group. -/
noncomputable def colPairRightDiv {n m : ℕ} (D : MatrixDivision n m)
    (hcol : 0 < D.colCuts) : Division m (Division.pairCount (D.colCuts + 1)) :=
  D.colDiv.coarsen
    (Division.pairRightIndexDivision (D.colCuts + 1) (by omega))

/-- A mixed column cut is visible as a mixed zone in one of the two paired
column coarsenings. -/
theorem zoneMixed_colPair_of_colCutMixed {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n)) (j : Fin D.colCuts)
    (hmix : ColCutMixed M R D.colDiv j) :
    (∃ a : Fin (Division.pairCount (D.colCuts + 1)),
        ZoneMixed M R ((colPairLeftDiv D hcol).part a)) ∨
      ∃ a : Fin (Division.pairCount (D.colCuts + 1)),
        ZoneMixed M R ((colPairRightDiv D hcol).part a) := by
  let aL : Fin (Division.pairCount (D.colCuts + 1)) :=
    Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j.castSucc
  let aR : Fin (Division.pairCount (D.colCuts + 1)) :=
    Division.pairRightIndex (l := D.colCuts + 1) (by omega) j.castSucc
  rcases Division.pairIndex_adjacent_same_succ hcol j with hleft | hright
  · refine Or.inl ⟨aL, ?_⟩
    have hj₀ :
        j.castSucc ∈
          (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part aL := by
      simp [Division.pairLeftIndexDivision, aL]
    have hj₁ :
        j.succ ∈
          (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part aL := by
      simp [Division.pairLeftIndexDivision, aL, hleft.symm]
    simpa [colPairLeftDiv] using
      zoneMixed_col_coarsen_of_colCutMixed (M := M) (R := R) (C := D.colDiv)
        (I := Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))
        (a := aL) (j := j) hj₀ hj₁ hmix
  · refine Or.inr ⟨aR, ?_⟩
    have hj₀ :
        j.castSucc ∈
          (Division.pairRightIndexDivision (D.colCuts + 1) (by omega)).part aR := by
      simp [Division.pairRightIndexDivision, aR]
    have hj₁ :
        j.succ ∈
          (Division.pairRightIndexDivision (D.colCuts + 1) (by omega)).part aR := by
      simp [Division.pairRightIndexDivision, aR, hright.symm]
    simpa [colPairRightDiv] using
      zoneMixed_col_coarsen_of_colCutMixed (M := M) (R := R) (C := D.colDiv)
        (I := Division.pairRightIndexDivision (D.colCuts + 1) (by omega))
        (a := aR) (j := j) hj₀ hj₁ hmix

/-- A mixed row cut is visible as a mixed zone in one of the two paired row
coarsenings. -/
theorem zoneMixed_rowPair_of_rowCutMixed {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m)) (i : Fin D.rowCuts)
    (hmix : RowCutMixed M D.rowDiv C i) :
    (∃ a : Fin (Division.pairCount (D.rowCuts + 1)),
        ZoneMixed M ((rowPairLeftDiv D hrow).part a) C) ∨
      ∃ a : Fin (Division.pairCount (D.rowCuts + 1)),
        ZoneMixed M ((rowPairRightDiv D hrow).part a) C := by
  let aL : Fin (Division.pairCount (D.rowCuts + 1)) :=
    Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i.castSucc
  let aR : Fin (Division.pairCount (D.rowCuts + 1)) :=
    Division.pairRightIndex (l := D.rowCuts + 1) (by omega) i.castSucc
  rcases Division.pairIndex_adjacent_same_succ hrow i with hleft | hright
  · refine Or.inl ⟨aL, ?_⟩
    have hi₀ :
        i.castSucc ∈
          (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part aL := by
      simp [Division.pairLeftIndexDivision, aL]
    have hi₁ :
        i.succ ∈
          (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part aL := by
      simp [Division.pairLeftIndexDivision, aL, hleft.symm]
    simpa [rowPairLeftDiv] using
      zoneMixed_row_coarsen_of_rowCutMixed (M := M) (R := D.rowDiv)
        (I := Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))
        (C := C) (a := aL) (i := i) hi₀ hi₁ hmix
  · refine Or.inr ⟨aR, ?_⟩
    have hi₀ :
        i.castSucc ∈
          (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega)).part aR := by
      simp [Division.pairRightIndexDivision, aR]
    have hi₁ :
        i.succ ∈
          (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega)).part aR := by
      simp [Division.pairRightIndexDivision, aR, hright.symm]
    simpa [rowPairRightDiv] using
      zoneMixed_row_coarsen_of_rowCutMixed (M := M) (R := D.rowDiv)
        (I := Division.pairRightIndexDivision (D.rowCuts + 1) (by omega))
        (C := C) (a := aR) (i := i) hi₀ hi₁ hmix

/-- Every mixed item of a row set on the column division is visible in one of
the two paired column coarsenings. -/
theorem colMixedItem_visible_pair {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n)) {x : Sum (Fin (D.colCuts + 1)) (Fin D.colCuts)}
    (hx : x ∈ colMixedItems M R D.colDiv) :
    (∃ a : Fin (Division.pairCount (D.colCuts + 1)),
        ZoneMixed M R ((colPairLeftDiv D hcol).part a)) ∨
      ∃ a : Fin (Division.pairCount (D.colCuts + 1)),
        ZoneMixed M R ((colPairRightDiv D hcol).part a) := by
  cases x with
  | inl j =>
      have hmix : ZoneMixed M R (D.colDiv.part j) := by
        simpa using hx
      let a : Fin (Division.pairCount (D.colCuts + 1)) :=
        Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j
      refine Or.inl ⟨a, ?_⟩
      have hj :
          j ∈ (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part a := by
        simp [Division.pairLeftIndexDivision, a]
      simpa [colPairLeftDiv] using
        zoneMixed_col_coarsen_of_zoneMixed (M := M) (R := R) (C := D.colDiv)
          (I := Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))
          (a := a) (j := j) hj hmix
  | inr j =>
      have hmix : ColCutMixed M R D.colDiv j := by
        simpa using hx
      exact zoneMixed_colPair_of_colCutMixed D hcol R j hmix

/-- Row-side version of `colMixedItem_visible_pair`. -/
theorem rowMixedItem_visible_pair {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m)) {x : Sum (Fin (D.rowCuts + 1)) (Fin D.rowCuts)}
    (hx : x ∈ rowMixedItems M D.rowDiv C) :
    (∃ a : Fin (Division.pairCount (D.rowCuts + 1)),
        ZoneMixed M ((rowPairLeftDiv D hrow).part a) C) ∨
      ∃ a : Fin (Division.pairCount (D.rowCuts + 1)),
        ZoneMixed M ((rowPairRightDiv D hrow).part a) C := by
  cases x with
  | inl i =>
      have hmix : ZoneMixed M (D.rowDiv.part i) C := by
        simpa using hx
      let a : Fin (Division.pairCount (D.rowCuts + 1)) :=
        Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i
      refine Or.inl ⟨a, ?_⟩
      have hi :
          i ∈ (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part a := by
        simp [Division.pairLeftIndexDivision, a]
      simpa [rowPairLeftDiv] using
        zoneMixed_row_coarsen_of_zoneMixed (M := M) (R := D.rowDiv)
          (I := Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))
          (C := C) (a := a) (i := i) hi hmix
  | inr i =>
      have hmix : RowCutMixed M D.rowDiv C i := by
        simpa using hx
      exact zoneMixed_rowPair_of_rowCutMixed D hrow C i hmix

/-- The canonical fused part for a left row pair is contained in the
corresponding part of the left paired row coarsening.  The last paired part may
also contain a leftover row part, which is harmless for mixedness because
mixed zones are monotone under enlarging the row set. -/
theorem rowFuse_pairLeft_part_subset {n m : ℕ}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    let i : Fin D.rowCuts := Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
    let fi : Fin ((D.rowCuts - 1) + 1) :=
      (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
    ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) ⊆
      (MatrixDivision.rowPairLeftDiv D hrow).part a := by
  intro i fi x hx
  let Rcast : Division n ((D.rowCuts - 1) + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv
  have hfused :
      (MatrixDivision.rowFuse D hrow i).rowDiv.part fi =
        Rcast.part fi.castSucc ∪ Rcast.part fi.succ := by
    simpa [MatrixDivision.rowFuse, Rcast, fi] using
      Division.fuse_part_self Rcast fi
  rw [hfused] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · refine Finset.mem_biUnion.mpr ⟨(finCongr
        (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm fi.castSucc, ?_, ?_⟩
    · have hidx :
          Division.pairLeftIndex (l := D.rowCuts + 1) (by omega)
              ((finCongr
                (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm fi.castSucc) = a := by
        subst fi
        subst i
        simpa [Division.pairLeftCutIndex] using
          Division.pairLeftIndex_pairLeftCutIndex_castSucc
            (l := D.rowCuts + 1) (by omega) a
      simpa [MatrixDivision.rowPairLeftDiv, Division.pairLeftIndexDivision] using hidx
    · simpa [Rcast, Division.castIndex] using hx
  · refine Finset.mem_biUnion.mpr ⟨(finCongr
        (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm fi.succ, ?_, ?_⟩
    · have hidx :
          Division.pairLeftIndex (l := D.rowCuts + 1) (by omega)
              ((finCongr
                (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm fi.succ) = a := by
        subst fi
        subst i
        simpa [Division.pairLeftCutIndex] using
          Division.pairLeftIndex_pairLeftCutIndex_succ
            (l := D.rowCuts + 1) (by omega) a
      simpa [MatrixDivision.rowPairLeftDiv, Division.pairLeftIndexDivision] using hidx
    · simpa [Rcast, Division.castIndex] using hx

/-- Column-side analogue of `rowFuse_pairLeft_part_subset`. -/
theorem colFuse_pairLeft_part_subset {n m : ℕ}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    let j : Fin D.colCuts := Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) a
    let fj : Fin ((D.colCuts - 1) + 1) :=
      (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
    ((MatrixDivision.colFuse D hcol j).colDiv.part fj) ⊆
      (MatrixDivision.colPairLeftDiv D hcol).part a := by
  intro j fj x hx
  let Ccast : Division m ((D.colCuts - 1) + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv
  have hfused :
      (MatrixDivision.colFuse D hcol j).colDiv.part fj =
        Ccast.part fj.castSucc ∪ Ccast.part fj.succ := by
    simpa [MatrixDivision.colFuse, Ccast, fj] using
      Division.fuse_part_self Ccast fj
  rw [hfused] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · refine Finset.mem_biUnion.mpr ⟨(finCongr
        (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm fj.castSucc, ?_, ?_⟩
    · have hidx :
          Division.pairLeftIndex (l := D.colCuts + 1) (by omega)
              ((finCongr
                (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm fj.castSucc) = a := by
        subst fj
        subst j
        simpa [Division.pairLeftCutIndex] using
          Division.pairLeftIndex_pairLeftCutIndex_castSucc
            (l := D.colCuts + 1) (by omega) a
      simpa [MatrixDivision.colPairLeftDiv, Division.pairLeftIndexDivision] using hidx
    · simpa [Ccast, Division.castIndex] using hx
  · refine Finset.mem_biUnion.mpr ⟨(finCongr
        (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm fj.succ, ?_, ?_⟩
    · have hidx :
          Division.pairLeftIndex (l := D.colCuts + 1) (by omega)
              ((finCongr
                (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm fj.succ) = a := by
        subst fj
        subst j
        simpa [Division.pairLeftCutIndex] using
          Division.pairLeftIndex_pairLeftCutIndex_succ
            (l := D.colCuts + 1) (by omega) a
      simpa [MatrixDivision.colPairLeftDiv, Division.pairLeftIndexDivision] using hidx
    · simpa [Ccast, Division.castIndex] using hx

/-- If no row fusion is good, then every canonical left row-pair fusion has
new row-part mixed value strictly above the bound. -/
theorem colMixedValue_rowPair_gt_of_no_good_row {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (hbad :
      ¬ ∃ hrow' : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
        colMixedValue M
          ((MatrixDivision.rowFuse D hrow' i).rowDiv.part
            ((finCongr
              (by simp [MatrixDivision.rowFuse]; omega :
                D.rowCuts =
                  (MatrixDivision.rowFuse D hrow' i).rowCuts + 1)) i))
          (MatrixDivision.rowFuse D hrow' i).colDiv ≤ d)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    let i : Fin D.rowCuts := Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
    colMixedValue M
      ((MatrixDivision.rowFuse D hrow i).rowDiv.part
        ((finCongr
          (by simp [MatrixDivision.rowFuse]; omega :
            D.rowCuts =
              (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
      (MatrixDivision.rowFuse D hrow i).colDiv > d := by
  intro i
  exact Nat.lt_of_not_ge (by
    intro hle
    exact hbad ⟨hrow, i, hle⟩)

/-- Column-side analogue of `colMixedValue_rowPair_gt_of_no_good_row`. -/
theorem rowMixedValue_colPair_gt_of_no_good_col {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (hbad :
      ¬ ∃ hcol' : 0 < D.colCuts, ∃ j : Fin D.colCuts,
        rowMixedValue M
          (MatrixDivision.colFuse D hcol' j).rowDiv
          ((MatrixDivision.colFuse D hcol' j).colDiv.part
            ((finCongr
              (by simp [MatrixDivision.colFuse]; omega :
                D.colCuts =
                  (MatrixDivision.colFuse D hcol' j).colCuts + 1)) j)) ≤ d)
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    let j : Fin D.colCuts := Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) a
    rowMixedValue M
      (MatrixDivision.colFuse D hcol j).rowDiv
      ((MatrixDivision.colFuse D hcol j).colDiv.part
        ((finCongr
          (by simp [MatrixDivision.colFuse]; omega :
            D.colCuts =
              (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) > d := by
  intro j
  exact Nat.lt_of_not_ge (by
    intro hle
    exact hbad ⟨hcol, j, hle⟩)

/-- Cardinal form of `colMixedValue_rowPair_gt_of_no_good_row`. -/
theorem colMixedItems_rowPair_card_gt_of_no_good_row {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (hbad :
      ¬ ∃ hrow' : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
        colMixedValue M
          ((MatrixDivision.rowFuse D hrow' i).rowDiv.part
            ((finCongr
              (by simp [MatrixDivision.rowFuse]; omega :
                D.rowCuts =
                  (MatrixDivision.rowFuse D hrow' i).rowCuts + 1)) i))
          (MatrixDivision.rowFuse D hrow' i).colDiv ≤ d)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    let i : Fin D.rowCuts := Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
    let fi : Fin ((D.rowCuts - 1) + 1) :=
      (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
    d <
      (colMixedItems M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
        D.colDiv).card := by
  intro i fi
  have hgt := colMixedValue_rowPair_gt_of_no_good_row
    (M := M) D hrow hbad a
  dsimp only at hgt
  have hcard :=
    colMixedItems_card M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) D.colDiv
  rw [hcard]
  simpa [MatrixDivision.rowFuse, i, fi] using hgt

/-- Cardinal form of `rowMixedValue_colPair_gt_of_no_good_col`. -/
theorem rowMixedItems_colPair_card_gt_of_no_good_col {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (hbad :
      ¬ ∃ hcol' : 0 < D.colCuts, ∃ j : Fin D.colCuts,
        rowMixedValue M
          (MatrixDivision.colFuse D hcol' j).rowDiv
          ((MatrixDivision.colFuse D hcol' j).colDiv.part
            ((finCongr
              (by simp [MatrixDivision.colFuse]; omega :
                D.colCuts =
                  (MatrixDivision.colFuse D hcol' j).colCuts + 1)) j)) ≤ d)
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    let j : Fin D.colCuts := Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) a
    let fj : Fin ((D.colCuts - 1) + 1) :=
      (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
    d <
      (rowMixedItems M D.rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part fj)).card := by
  intro j fj
  have hgt := rowMixedValue_colPair_gt_of_no_good_col
    (M := M) D hcol hbad a
  dsimp only at hgt
  have hcard :=
    rowMixedItems_card M D.rowDiv ((MatrixDivision.colFuse D hcol j).colDiv.part fj)
  rw [hcard]
  simpa [MatrixDivision.colFuse, j, fj] using hgt

/-- Mixed targets in the two paired column coarsenings, packaged as one finite
set.  The left summand records mixed zones of the left pairing and the right
summand records mixed zones of the shifted right pairing. -/
noncomputable def colPairedMixedTargets {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n)) :
    Finset (Sum (Fin (Division.pairCount (D.colCuts + 1)))
      (Fin (Division.pairCount (D.colCuts + 1)))) := by
  classical
  exact
    (Finset.univ.filter fun a =>
      ZoneMixed M R ((MatrixDivision.colPairLeftDiv D hcol).part a)).map
        ⟨Sum.inl, by intro a b h; simpa using h⟩ ∪
      (Finset.univ.filter fun a =>
        ZoneMixed M R ((MatrixDivision.colPairRightDiv D hcol).part a)).map
        ⟨Sum.inr, by intro a b h; simpa using h⟩

@[simp] theorem mem_colPairedMixedTargets_left {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n))
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    Sum.inl a ∈ colPairedMixedTargets M D hcol R ↔
      ZoneMixed M R ((MatrixDivision.colPairLeftDiv D hcol).part a) := by
  classical
  simp [colPairedMixedTargets]

@[simp] theorem mem_colPairedMixedTargets_right {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n))
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    Sum.inr a ∈ colPairedMixedTargets M D hcol R ↔
      ZoneMixed M R ((MatrixDivision.colPairRightDiv D hcol).part a) := by
  classical
  simp [colPairedMixedTargets]

/-- Row-side analogue of `colPairedMixedTargets`. -/
noncomputable def rowPairedMixedTargets {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m)) :
    Finset (Sum (Fin (Division.pairCount (D.rowCuts + 1)))
      (Fin (Division.pairCount (D.rowCuts + 1)))) := by
  classical
  exact
    (Finset.univ.filter fun a =>
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a) C).map
        ⟨Sum.inl, by intro a b h; simpa using h⟩ ∪
      (Finset.univ.filter fun a =>
        ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a) C).map
        ⟨Sum.inr, by intro a b h; simpa using h⟩

@[simp] theorem mem_rowPairedMixedTargets_left {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m))
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    Sum.inl a ∈ rowPairedMixedTargets M D hrow C ↔
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a) C := by
  classical
  simp [rowPairedMixedTargets]

@[simp] theorem mem_rowPairedMixedTargets_right {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m))
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    Sum.inr a ∈ rowPairedMixedTargets M D hrow C ↔
      ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a) C := by
  classical
  simp [rowPairedMixedTargets]

/-- Membership form of `colMixedItem_visible_pair`. -/
theorem exists_mem_colPairedMixedTargets_of_colMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n)) {x : Sum (Fin (D.colCuts + 1)) (Fin D.colCuts)}
    (hx : x ∈ colMixedItems M R D.colDiv) :
    ∃ y, y ∈ colPairedMixedTargets M D hcol R := by
  rcases MatrixDivision.colMixedItem_visible_pair D hcol R hx with hleft | hright
  · rcases hleft with ⟨a, ha⟩
    exact ⟨Sum.inl a, by simpa using ha⟩
  · rcases hright with ⟨a, ha⟩
    exact ⟨Sum.inr a, by simpa using ha⟩

/-- Membership form of `rowMixedItem_visible_pair`. -/
theorem exists_mem_rowPairedMixedTargets_of_rowMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m)) {x : Sum (Fin (D.rowCuts + 1)) (Fin D.rowCuts)}
    (hx : x ∈ rowMixedItems M D.rowDiv C) :
    ∃ y, y ∈ rowPairedMixedTargets M D hrow C := by
  rcases MatrixDivision.rowMixedItem_visible_pair D hrow C hx with hleft | hright
  · rcases hleft with ⟨a, ha⟩
    exact ⟨Sum.inl a, by simpa using ha⟩
  · rcases hright with ⟨a, ha⟩
    exact ⟨Sum.inr a, by simpa using ha⟩

/-- A finite-fiber counting lemma for paired item targets.  If every source
zone/cut item is charged to an allowed paired target, then there are at least
one tenth as many allowed targets. -/
theorem pairedItem_card_le_ten_mul_target_card {k : ℕ} (hk : 0 < k)
    (S : Finset (Sum (Fin (k + 1)) (Fin k)))
    (T : Finset
      (Sum (Fin (Division.pairCount (k + 1)))
        (Fin (Division.pairCount (k + 1)))))
    (hmem : ∀ ⦃x⦄, x ∈ S → Division.pairedItemTargetSucc hk x ∈ T) :
    S.card ≤ 10 * T.card := by
  classical
  let f : Sum (Fin (k + 1)) (Fin k) →
      Sum (Fin (Division.pairCount (k + 1)))
          (Fin (Division.pairCount (k + 1))) × Fin 10 :=
    fun x => (Division.pairedItemTargetSucc hk x, Division.pairedItemCodeSucc hk x)
  have hmaps : Set.MapsTo f S (T.product (Finset.univ : Finset (Fin 10))) := by
    intro x hx
    simp [f, hmem hx]
  have hinj : (S : Set (Sum (Fin (k + 1)) (Fin k))).InjOn f := by
    intro x _hx y _hy hxy
    exact Division.pairedItemTargetSucc_code_injective hk hxy
  calc
    S.card ≤ (T.product (Finset.univ : Finset (Fin 10))).card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    _ = T.card * 10 := by simp
    _ = 10 * T.card := by omega

/-- The two auxiliary mixed-zone matrices used when row pairs are the rows:
the left summand is the matrix for the left column pairing and the right
summand is the matrix for the shifted right column pairing. -/
noncomputable def rowPairAuxTargets {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts) :
    Finset (Fin (Division.pairCount (D.rowCuts + 1)) ×
      Sum (Fin (Division.pairCount (D.colCuts + 1)))
        (Fin (Division.pairCount (D.colCuts + 1)))) := by
  classical
  exact
    (oneEntries
      (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
        (MatrixDivision.colPairLeftDiv D hcol))).map
        ⟨fun p => (p.1, Sum.inl p.2), by
          intro a b h
          cases a with
          | mk ar ac =>
              cases b with
              | mk br bc =>
                  simp at h
                  exact Prod.ext h.1 h.2⟩ ∪
      (oneEntries
        (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
          (MatrixDivision.colPairRightDiv D hcol))).map
        ⟨fun p => (p.1, Sum.inr p.2), by
          intro a b h
          cases a with
          | mk ar ac =>
              cases b with
              | mk br bc =>
                  simp at h
                  exact Prod.ext h.1 h.2⟩

@[simp] theorem mem_rowPairAuxTargets_left {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    (a, Sum.inl b) ∈ rowPairAuxTargets M D hrow hcol ↔
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
        ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
  classical
  simp [rowPairAuxTargets, oneEntries, mixedZoneMatrix]

@[simp] theorem mem_rowPairAuxTargets_right {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    (a, Sum.inr b) ∈ rowPairAuxTargets M D hrow hcol ↔
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
        ((MatrixDivision.colPairRightDiv D hcol).part b) := by
  classical
  simp [rowPairAuxTargets, oneEntries, mixedZoneMatrix]

/-- Marcus--Tardos upper bound for the two row-pair auxiliary matrices. -/
theorem rowPairAuxTargets_card_lt {n m t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (hMT : IsMarcusTardosConstant t c) (hfree : MixedFree M t) :
    (rowPairAuxTargets M D hrow hcol).card <
      c * max (Division.pairCount (D.rowCuts + 1))
          (Division.pairCount (D.colCuts + 1)) +
        c * max (Division.pairCount (D.rowCuts + 1))
          (Division.pairCount (D.colCuts + 1)) := by
  classical
  have hpos :
      0 < max (Division.pairCount (D.rowCuts + 1))
        (Division.pairCount (D.colCuts + 1)) := by
    have hp : 0 < Division.pairCount (D.rowCuts + 1) :=
      Division.pairCount_pos (by omega)
    exact lt_of_lt_of_le hp (le_max_left _ _)
  have hleft :=
    oneEntries_mixedZoneMatrix_lt_of_mixedFree
      (M := M) (R := MatrixDivision.rowPairLeftDiv D hrow)
      (C := MatrixDivision.colPairLeftDiv D hcol) hMT hfree hpos
  have hright :=
    oneEntries_mixedZoneMatrix_lt_of_mixedFree
      (M := M) (R := MatrixDivision.rowPairLeftDiv D hrow)
      (C := MatrixDivision.colPairRightDiv D hcol) hMT hfree hpos
  have hcard :
      (rowPairAuxTargets M D hrow hcol).card =
        (oneEntries
          (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
            (MatrixDivision.colPairLeftDiv D hcol))).card +
          (oneEntries
            (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
              (MatrixDivision.colPairRightDiv D hcol))).card := by
    rw [rowPairAuxTargets, Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      intro x hx hy
      simp at hx hy
      rcases hx with ⟨a, _ha, hxa⟩
      rcases hy with ⟨b, _hb, hyb⟩
      cases hxa.2.trans hyb.2.symm
  rw [hcard]
  exact Nat.add_lt_add hleft hright

/-- A mixed item of the fused row pair contributes a mixed entry to one of the
two row-pair auxiliary matrices. -/
theorem exists_mem_rowPairAuxTargets_of_rowPair_colMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    {x : Sum (Fin (D.colCuts + 1)) (Fin D.colCuts)}
    (hx :
      let i : Fin D.rowCuts :=
        Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
      let fi : Fin ((D.rowCuts - 1) + 1) :=
        (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
      x ∈ colMixedItems M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
        D.colDiv) :
    ∃ y,
      (a, y) ∈ rowPairAuxTargets M D hrow hcol := by
  dsimp only at hx
  let i : Fin D.rowCuts :=
    Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hsubset :
      ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) ⊆
        (MatrixDivision.rowPairLeftDiv D hrow).part a := by
    simpa [i, fi] using MatrixDivision.rowFuse_pairLeft_part_subset D hrow a
  rcases MatrixDivision.colMixedItem_visible_pair D hcol
      ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) hx with hleft | hright
  · rcases hleft with ⟨b, hb⟩
    refine ⟨Sum.inl b, ?_⟩
    have hbig :
        ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
          ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
      zoneMixed_of_subset hsubset (by intro c hc; exact hc) hb
    simpa using hbig
  · rcases hright with ⟨b, hb⟩
    refine ⟨Sum.inr b, ?_⟩
    have hbig :
        ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
          ((MatrixDivision.colPairRightDiv D hcol).part b) :=
      zoneMixed_of_subset hsubset (by intro c hc; exact hc) hb
    simpa using hbig

/-- Deterministic version of
`exists_mem_rowPairAuxTargets_of_rowPair_colMixedItem`, using the paired target
map from `Division`. -/
theorem pairedItemTarget_mem_rowPairAuxTargets_of_rowPair_colMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    {x : Sum (Fin (D.colCuts + 1)) (Fin D.colCuts)}
    (hx :
      let i : Fin D.rowCuts :=
        Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
      let fi : Fin ((D.rowCuts - 1) + 1) :=
        (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
      x ∈ colMixedItems M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
        D.colDiv) :
    (a, Division.pairedItemTargetSucc hcol x) ∈ rowPairAuxTargets M D hrow hcol := by
  classical
  dsimp only at hx
  let i : Fin D.rowCuts :=
    Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hsubset :
      ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) ⊆
        (MatrixDivision.rowPairLeftDiv D hrow).part a := by
    simpa [i, fi] using MatrixDivision.rowFuse_pairLeft_part_subset D hrow a
  cases x with
  | inl j =>
      have hmix : ZoneMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
          (D.colDiv.part j) := by
        simpa using hx
      let b : Fin (Division.pairCount (D.colCuts + 1)) :=
        Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j
      have hj :
          j ∈ (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part b := by
        simp [Division.pairLeftIndexDivision, b]
      have hcolmix :
          ZoneMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
            ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
        simpa [MatrixDivision.colPairLeftDiv] using
          zoneMixed_col_coarsen_of_zoneMixed (M := M)
            (R := (MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
            (C := D.colDiv)
            (I := Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))
            (a := b) (j := j) hj hmix
      have hbig :
          ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
            ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
        zoneMixed_of_subset hsubset (by intro c hc; exact hc) hcolmix
      simpa [Division.pairedItemTargetSucc_zone, b] using hbig
  | inr j =>
      have hmix : ColCutMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
          D.colDiv j := by
        simpa using hx
      by_cases hleft :
          Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j.castSucc =
            Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j.succ
      · let b : Fin (Division.pairCount (D.colCuts + 1)) :=
          Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j.succ
        have hj₀ :
            j.castSucc ∈
              (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part b := by
          simp [Division.pairLeftIndexDivision, b, hleft]
        have hj₁ :
            j.succ ∈
              (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part b := by
          simp [Division.pairLeftIndexDivision, b]
        have hcolmix :
            ZoneMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
              ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
          simpa [MatrixDivision.colPairLeftDiv] using
            zoneMixed_col_coarsen_of_colCutMixed (M := M)
              (R := (MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
              (C := D.colDiv)
              (I := Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))
              (a := b) (j := j) hj₀ hj₁ hmix
        have hbig :
            ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
              ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
          zoneMixed_of_subset hsubset (by intro c hc; exact hc) hcolmix
        simpa [Division.pairedItemTargetSucc_cut_left hcol j hleft, b] using hbig
      · have hright :
            Division.pairRightIndex (l := D.colCuts + 1) (by omega) j.castSucc =
              Division.pairRightIndex (l := D.colCuts + 1) (by omega) j.succ := by
          rcases Division.pairIndex_adjacent_same_succ hcol j with h | h
          · exact False.elim (hleft h)
          · exact h
        let b : Fin (Division.pairCount (D.colCuts + 1)) :=
          Division.pairRightIndex (l := D.colCuts + 1) (by omega) j.castSucc
        have hj₀ :
            j.castSucc ∈
              (Division.pairRightIndexDivision (D.colCuts + 1) (by omega)).part b := by
          simp [Division.pairRightIndexDivision, b]
        have hj₁ :
            j.succ ∈
              (Division.pairRightIndexDivision (D.colCuts + 1) (by omega)).part b := by
          simp [Division.pairRightIndexDivision, b, hright.symm]
        have hcolmix :
            ZoneMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
              ((MatrixDivision.colPairRightDiv D hcol).part b) := by
          simpa [MatrixDivision.colPairRightDiv] using
            zoneMixed_col_coarsen_of_colCutMixed (M := M)
              (R := (MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
              (C := D.colDiv)
              (I := Division.pairRightIndexDivision (D.colCuts + 1) (by omega))
              (a := b) (j := j) hj₀ hj₁ hmix
        have hbig :
            ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
              ((MatrixDivision.colPairRightDiv D hcol).part b) :=
          zoneMixed_of_subset hsubset (by intro c hc; exact hc) hcolmix
        simpa [Division.pairedItemTargetSucc_cut_right hcol j hleft, b] using hbig

/-- The row-pair auxiliary entries in a fixed paired row. -/
noncomputable def rowPairAuxFiber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    Finset
      (Sum (Fin (Division.pairCount (D.colCuts + 1)))
        (Fin (Division.pairCount (D.colCuts + 1)))) := by
  classical
  exact Finset.univ.filter fun y => (a, y) ∈ rowPairAuxTargets M D hrow hcol

theorem colMixedItems_rowPair_card_le_ten_mul_rowPairAuxFiber_card {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    let i : Fin D.rowCuts :=
      Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
    let fi : Fin ((D.rowCuts - 1) + 1) :=
      (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
    (colMixedItems M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
        D.colDiv).card ≤
      10 * (rowPairAuxFiber M D hrow hcol a).card := by
  intro i fi
  apply pairedItem_card_le_ten_mul_target_card hcol
  intro x hx
  simp [rowPairAuxFiber]
  exact pairedItemTarget_mem_rowPairAuxTargets_of_rowPair_colMixedItem
    D hrow hcol a (by simpa [i, fi] using hx)

theorem rowPairAuxTargets_card_gt_of_fibers_gt {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (h :
      ∀ a : Fin (Division.pairCount (D.rowCuts + 1)),
        d < (rowPairAuxFiber M D hrow hcol a).card) :
    Division.pairCount (D.rowCuts + 1) * d <
      (rowPairAuxTargets M D hrow hcol).card := by
  classical
  let p := Division.pairCount (D.rowCuts + 1)
  let Y :=
    Sum (Fin (Division.pairCount (D.colCuts + 1)))
      (Fin (Division.pairCount (D.colCuts + 1)))
  let P : Finset (Fin p × Y) := rowPairAuxTargets M D hrow hcol
  let A := Sigma fun a : Fin p => {y : Y // y ∈ rowPairAuxFiber M D hrow hcol a}
  have hcardA :
      Fintype.card A =
        ∑ a : Fin p, (rowPairAuxFiber M D hrow hcol a).card := by
    simp [A]
  have hle : Fintype.card A ≤ P.card := by
    let f : A → {z : Fin p × Y // z ∈ P} := fun z =>
      ⟨(z.1, z.2.1), by
        have hz := z.2.2
        change z.2.1 ∈
          (Finset.univ.filter fun y => (z.1, y) ∈ rowPairAuxTargets M D hrow hcol) at hz
        simpa [P] using (Finset.mem_filter.mp hz).2⟩
    have hinj : Function.Injective f := by
      intro u v huv
      cases u with
      | mk a ya =>
          cases v with
          | mk b yb =>
              have hval := congrArg Subtype.val huv
              simp [f] at hval
              cases hval.1
              cases ya with
              | mk y hy =>
                  cases yb with
                  | mk z hz =>
                      simp at hval
                      subst z
                      rfl
    have hcard := Fintype.card_le_of_injective f hinj
    simpa [P] using hcard
  have hsum_le :
      ∑ _a : Fin p, (d + 1) ≤
        ∑ a : Fin p, (rowPairAuxFiber M D hrow hcol a).card := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin p)))
        (fun a _ha => Nat.succ_le_of_lt (h a)))
  have hp : 0 < p := Division.pairCount_pos (by omega)
  have hmul : p * d < p * (d + 1) :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self d) hp
  have hlt_sum :
      p * d < ∑ a : Fin p, (rowPairAuxFiber M D hrow hcol a).card := by
    refine lt_of_lt_of_le ?_ hsum_le
    simpa [p, Finset.sum_const, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hmul
  have hlt_A : p * d < Fintype.card A := by
    simpa [hcardA] using hlt_sum
  exact lt_of_lt_of_le (by simpa [p, P] using hlt_A) hle

/-- The two auxiliary mixed-zone matrices used when column pairs are the
columns, dual to `rowPairAuxTargets`. -/
noncomputable def colPairAuxTargets {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts) :
    Finset (Sum (Fin (Division.pairCount (D.rowCuts + 1)))
        (Fin (Division.pairCount (D.rowCuts + 1))) ×
      Fin (Division.pairCount (D.colCuts + 1))) := by
  classical
  exact
    (oneEntries
      (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
        (MatrixDivision.colPairLeftDiv D hcol))).map
        ⟨fun p => (Sum.inl p.1, p.2), by
          intro a b h
          cases a with
          | mk ar ac =>
              cases b with
              | mk br bc =>
                  simp at h
                  exact Prod.ext h.1 h.2⟩ ∪
      (oneEntries
        (mixedZoneMatrix M (MatrixDivision.rowPairRightDiv D hrow)
          (MatrixDivision.colPairLeftDiv D hcol))).map
        ⟨fun p => (Sum.inr p.1, p.2), by
          intro a b h
          cases a with
          | mk ar ac =>
              cases b with
              | mk br bc =>
                  simp at h
                  exact Prod.ext h.1 h.2⟩

@[simp] theorem mem_colPairAuxTargets_left {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    (Sum.inl a, b) ∈ colPairAuxTargets M D hrow hcol ↔
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
        ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
  classical
  simp [colPairAuxTargets, oneEntries, mixedZoneMatrix]

@[simp] theorem mem_colPairAuxTargets_right {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    (Sum.inr a, b) ∈ colPairAuxTargets M D hrow hcol ↔
      ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a)
        ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
  classical
  simp [colPairAuxTargets, oneEntries, mixedZoneMatrix]

/-- Marcus--Tardos upper bound for the two column-pair auxiliary matrices. -/
theorem colPairAuxTargets_card_lt {n m t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (hMT : IsMarcusTardosConstant t c) (hfree : MixedFree M t) :
    (colPairAuxTargets M D hrow hcol).card <
      c * max (Division.pairCount (D.rowCuts + 1))
          (Division.pairCount (D.colCuts + 1)) +
        c * max (Division.pairCount (D.rowCuts + 1))
          (Division.pairCount (D.colCuts + 1)) := by
  classical
  have hpos :
      0 < max (Division.pairCount (D.rowCuts + 1))
        (Division.pairCount (D.colCuts + 1)) := by
    have hp : 0 < Division.pairCount (D.colCuts + 1) :=
      Division.pairCount_pos (by omega)
    exact lt_of_lt_of_le hp (le_max_right _ _)
  have hleft :=
    oneEntries_mixedZoneMatrix_lt_of_mixedFree
      (M := M) (R := MatrixDivision.rowPairLeftDiv D hrow)
      (C := MatrixDivision.colPairLeftDiv D hcol) hMT hfree hpos
  have hright :=
    oneEntries_mixedZoneMatrix_lt_of_mixedFree
      (M := M) (R := MatrixDivision.rowPairRightDiv D hrow)
      (C := MatrixDivision.colPairLeftDiv D hcol) hMT hfree hpos
  have hcard :
      (colPairAuxTargets M D hrow hcol).card =
        (oneEntries
          (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
            (MatrixDivision.colPairLeftDiv D hcol))).card +
          (oneEntries
            (mixedZoneMatrix M (MatrixDivision.rowPairRightDiv D hrow)
              (MatrixDivision.colPairLeftDiv D hcol))).card := by
    rw [colPairAuxTargets, Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      intro x hx hy
      simp at hx hy
      rcases hx with ⟨a, _ha, hxa⟩
      rcases hy with ⟨b, _hb, hyb⟩
      cases hxa.2.trans hyb.2.symm
  rw [hcard]
  exact Nat.add_lt_add hleft hright

/-- Column-side analogue of
`exists_mem_rowPairAuxTargets_of_rowPair_colMixedItem`. -/
theorem exists_mem_colPairAuxTargets_of_colPair_rowMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (b : Fin (Division.pairCount (D.colCuts + 1)))
    {x : Sum (Fin (D.rowCuts + 1)) (Fin D.rowCuts)}
    (hx :
      let j : Fin D.colCuts :=
        Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
      let fj : Fin ((D.colCuts - 1) + 1) :=
        (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
      x ∈ rowMixedItems M D.rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part fj)) :
    ∃ y,
      (y, b) ∈ colPairAuxTargets M D hrow hcol := by
  dsimp only at hx
  let j : Fin D.colCuts :=
    Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hsubset :
      ((MatrixDivision.colFuse D hcol j).colDiv.part fj) ⊆
        (MatrixDivision.colPairLeftDiv D hcol).part b := by
    simpa [j, fj] using MatrixDivision.colFuse_pairLeft_part_subset D hcol b
  rcases MatrixDivision.rowMixedItem_visible_pair D hrow
      ((MatrixDivision.colFuse D hcol j).colDiv.part fj) hx with hleft | hright
  · rcases hleft with ⟨a, ha⟩
    refine ⟨Sum.inl a, ?_⟩
    have hbig :
        ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
          ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
      zoneMixed_of_subset (by intro r hr; exact hr) hsubset ha
    simpa using hbig
  · rcases hright with ⟨a, ha⟩
    refine ⟨Sum.inr a, ?_⟩
    have hbig :
        ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a)
          ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
      zoneMixed_of_subset (by intro r hr; exact hr) hsubset ha
    simpa using hbig

/-- Column-side deterministic paired-target membership. -/
theorem pairedItemTarget_mem_colPairAuxTargets_of_colPair_rowMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (b : Fin (Division.pairCount (D.colCuts + 1)))
    {x : Sum (Fin (D.rowCuts + 1)) (Fin D.rowCuts)}
    (hx :
      let j : Fin D.colCuts :=
        Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
      let fj : Fin ((D.colCuts - 1) + 1) :=
        (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
      x ∈ rowMixedItems M D.rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part fj)) :
    (Division.pairedItemTargetSucc hrow x, b) ∈ colPairAuxTargets M D hrow hcol := by
  classical
  dsimp only at hx
  let j : Fin D.colCuts :=
    Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hsubset :
      ((MatrixDivision.colFuse D hcol j).colDiv.part fj) ⊆
        (MatrixDivision.colPairLeftDiv D hcol).part b := by
    simpa [j, fj] using MatrixDivision.colFuse_pairLeft_part_subset D hcol b
  cases x with
  | inl i =>
      have hmix : ZoneMixed M (D.rowDiv.part i)
          ((MatrixDivision.colFuse D hcol j).colDiv.part fj) := by
        simpa using hx
      let a : Fin (Division.pairCount (D.rowCuts + 1)) :=
        Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i
      have hi :
          i ∈ (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part a := by
        simp [Division.pairLeftIndexDivision, a]
      have hrowmix :
          ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
            ((MatrixDivision.colFuse D hcol j).colDiv.part fj) := by
        simpa [MatrixDivision.rowPairLeftDiv] using
          zoneMixed_row_coarsen_of_zoneMixed (M := M)
            (R := D.rowDiv)
            (I := Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))
            (C := (MatrixDivision.colFuse D hcol j).colDiv.part fj)
            (a := a) (i := i) hi hmix
      have hbig :
          ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
            ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
        zoneMixed_of_subset (by intro r hr; exact hr) hsubset hrowmix
      simpa [Division.pairedItemTargetSucc_zone, a] using hbig
  | inr i =>
      have hmix : RowCutMixed M D.rowDiv
          ((MatrixDivision.colFuse D hcol j).colDiv.part fj) i := by
        simpa using hx
      by_cases hleft :
          Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i.castSucc =
            Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i.succ
      · let a : Fin (Division.pairCount (D.rowCuts + 1)) :=
          Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i.succ
        have hi₀ :
            i.castSucc ∈
              (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part a := by
          simp [Division.pairLeftIndexDivision, a, hleft]
        have hi₁ :
            i.succ ∈
              (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part a := by
          simp [Division.pairLeftIndexDivision, a]
        have hrowmix :
            ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
              ((MatrixDivision.colFuse D hcol j).colDiv.part fj) := by
          simpa [MatrixDivision.rowPairLeftDiv] using
            zoneMixed_row_coarsen_of_rowCutMixed (M := M)
              (R := D.rowDiv)
              (I := Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))
              (C := (MatrixDivision.colFuse D hcol j).colDiv.part fj)
              (a := a) (i := i) hi₀ hi₁ hmix
        have hbig :
            ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
              ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
          zoneMixed_of_subset (by intro r hr; exact hr) hsubset hrowmix
        simpa [Division.pairedItemTargetSucc_cut_left hrow i hleft, a] using hbig
      · have hright :
            Division.pairRightIndex (l := D.rowCuts + 1) (by omega) i.castSucc =
              Division.pairRightIndex (l := D.rowCuts + 1) (by omega) i.succ := by
          rcases Division.pairIndex_adjacent_same_succ hrow i with h | h
          · exact False.elim (hleft h)
          · exact h
        let a : Fin (Division.pairCount (D.rowCuts + 1)) :=
          Division.pairRightIndex (l := D.rowCuts + 1) (by omega) i.castSucc
        have hi₀ :
            i.castSucc ∈
              (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega)).part a := by
          simp [Division.pairRightIndexDivision, a]
        have hi₁ :
            i.succ ∈
              (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega)).part a := by
          simp [Division.pairRightIndexDivision, a, hright.symm]
        have hrowmix :
            ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a)
              ((MatrixDivision.colFuse D hcol j).colDiv.part fj) := by
          simpa [MatrixDivision.rowPairRightDiv] using
            zoneMixed_row_coarsen_of_rowCutMixed (M := M)
              (R := D.rowDiv)
              (I := Division.pairRightIndexDivision (D.rowCuts + 1) (by omega))
              (C := (MatrixDivision.colFuse D hcol j).colDiv.part fj)
              (a := a) (i := i) hi₀ hi₁ hmix
        have hbig :
            ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a)
              ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
          zoneMixed_of_subset (by intro r hr; exact hr) hsubset hrowmix
        simpa [Division.pairedItemTargetSucc_cut_right hrow i hleft, a] using hbig

/-- The column-pair auxiliary entries in a fixed paired column. -/
noncomputable def colPairAuxFiber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    Finset
      (Sum (Fin (Division.pairCount (D.rowCuts + 1)))
        (Fin (Division.pairCount (D.rowCuts + 1)))) := by
  classical
  exact Finset.univ.filter fun y => (y, b) ∈ colPairAuxTargets M D hrow hcol

theorem rowMixedItems_colPair_card_le_ten_mul_colPairAuxFiber_card {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    let j : Fin D.colCuts :=
      Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
    let fj : Fin ((D.colCuts - 1) + 1) :=
      (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
    (rowMixedItems M D.rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part fj)).card ≤
      10 * (colPairAuxFiber M D hrow hcol b).card := by
  intro j fj
  apply pairedItem_card_le_ten_mul_target_card hrow
  intro x hx
  simp [colPairAuxFiber]
  exact pairedItemTarget_mem_colPairAuxTargets_of_colPair_rowMixedItem
    D hrow hcol b (by simpa [j, fj] using hx)

theorem colPairAuxTargets_card_gt_of_fibers_gt {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (h :
      ∀ b : Fin (Division.pairCount (D.colCuts + 1)),
        d < (colPairAuxFiber M D hrow hcol b).card) :
    Division.pairCount (D.colCuts + 1) * d <
      (colPairAuxTargets M D hrow hcol).card := by
  classical
  let q := Division.pairCount (D.colCuts + 1)
  let X :=
    Sum (Fin (Division.pairCount (D.rowCuts + 1)))
      (Fin (Division.pairCount (D.rowCuts + 1)))
  let P : Finset (X × Fin q) := colPairAuxTargets M D hrow hcol
  let A := Sigma fun b : Fin q => {x : X // x ∈ colPairAuxFiber M D hrow hcol b}
  have hcardA :
      Fintype.card A =
        ∑ b : Fin q, (colPairAuxFiber M D hrow hcol b).card := by
    simp [A]
  have hle : Fintype.card A ≤ P.card := by
    let f : A → {z : X × Fin q // z ∈ P} := fun z =>
      ⟨(z.2.1, z.1), by
        have hz := z.2.2
        change z.2.1 ∈
          (Finset.univ.filter fun y => (y, z.1) ∈ colPairAuxTargets M D hrow hcol) at hz
        simpa [P] using (Finset.mem_filter.mp hz).2⟩
    have hinj : Function.Injective f := by
      intro u v huv
      cases u with
      | mk a xa =>
          cases v with
          | mk b xb =>
              have hval := congrArg Subtype.val huv
              simp [f] at hval
              cases hval.2
              cases xa with
              | mk x hx =>
                  cases xb with
                  | mk y hy =>
                      simp at hval
                      subst y
                      rfl
    have hcard := Fintype.card_le_of_injective f hinj
    simpa [P] using hcard
  have hsum_le :
      ∑ _b : Fin q, (d + 1) ≤
        ∑ b : Fin q, (colPairAuxFiber M D hrow hcol b).card := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q)))
        (fun b _hb => Nat.succ_le_of_lt (h b)))
  have hq : 0 < q := Division.pairCount_pos (by omega)
  have hmul : q * d < q * (d + 1) :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self d) hq
  have hlt_sum :
      q * d < ∑ b : Fin q, (colPairAuxFiber M D hrow hcol b).card := by
    refine lt_of_lt_of_le ?_ hsum_le
    simpa [q, Finset.sum_const, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hmul
  have hlt_A : q * d < Fintype.card A := by
    simpa [hcardA] using hlt_sum
  exact lt_of_lt_of_le (by simpa [q, P] using hlt_A) hle

theorem hasRowFusion_rowFuse {n m : ℕ} (D : MatrixDivision n m)
    (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts) :
    HasRowFusion D (rowFuse D hrow i) := by
  refine ⟨by simp [rowFuse]; omega, rfl, ?_⟩
  refine ⟨(finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i, ?_, ?_⟩
  · simpa [rowFuse] using
      Division.isFusionAt_fuse
        (Division.castIndex
          (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv)
        ((finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i)
  · intro j
    rfl

theorem hasColFusion_colFuse {n m : ℕ} (D : MatrixDivision n m)
    (hcol : 0 < D.colCuts) (j : Fin D.colCuts) :
    HasColFusion D (colFuse D hcol j) := by
  refine ⟨rfl, by simp [colFuse]; omega, ?_⟩
  refine ⟨(finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j, ?_, ?_⟩
  · intro i
    rfl
  · simpa [colFuse] using
      Division.isFusionAt_fuse
        (Division.castIndex
          (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv)
        ((finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j)

/-- Row fusion does not increase the mixed value of any column part. -/
theorem rowMixedValue_rowFuse_le {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (j : Fin ((rowFuse D hrow i).colCuts + 1)) :
    rowMixedValue M (rowFuse D hrow i).rowDiv
        ((rowFuse D hrow i).colDiv.part j) ≤
      rowMixedValue M D.rowDiv (D.colDiv.part j) := by
  let Rcast : Division n ((D.rowCuts - 1) + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hle := rowMixedValue_fuse_le (M := M) Rcast (D.colDiv.part j) fi
  have hcast :
      rowMixedValue M Rcast (D.colDiv.part j) =
        rowMixedValue M D.rowDiv (D.colDiv.part j) := by
    simpa [Rcast] using
      rowMixedValue_castIndex
        (by omega : D.rowCuts = D.rowCuts - 1 + 1) M D.rowDiv (D.colDiv.part j)
  simpa [rowFuse, Rcast, fi, hcast] using hle

/-- Column fusion does not increase the mixed value of any row part. -/
theorem colMixedValue_colFuse_le {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (i : Fin ((colFuse D hcol j).rowCuts + 1)) :
    colMixedValue M ((colFuse D hcol j).rowDiv.part i)
        (colFuse D hcol j).colDiv ≤
      colMixedValue M (D.rowDiv.part i) D.colDiv := by
  let Ccast : Division m ((D.colCuts - 1) + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hle := colMixedValue_fuse_le (M := M) (D.rowDiv.part i) Ccast fj
  have hcast :
      colMixedValue M (D.rowDiv.part i) Ccast =
        colMixedValue M (D.rowDiv.part i) D.colDiv := by
    simpa [Ccast] using
      colMixedValue_castIndex
        (by omega : D.colCuts = D.colCuts - 1 + 1) M
        (D.rowDiv.part i) D.colDiv
  simpa [colFuse, Ccast, fj, hcast] using hle

/-- A row part strictly before the fused row cut is unchanged. -/
theorem rowFuse_rowPart_eq_of_lt {n m : ℕ}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (a : Fin ((rowFuse D hrow i).rowCuts + 1))
    (ha : a < (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i) :
    (rowFuse D hrow i).rowDiv.part a =
      D.rowDiv.part
        ((finCongr (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm
          a.castSucc) := by
  let Rcast : Division n ((D.rowCuts - 1) + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hpart : (Rcast.fuse fi).part a = Rcast.part a.castSucc :=
    Division.fuse_part_of_lt Rcast ha
  simpa [rowFuse, Rcast, fi, Division.castIndex] using hpart

/-- A row part strictly after the fused row cut is the corresponding shifted
old part. -/
theorem rowFuse_rowPart_eq_of_gt {n m : ℕ}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (a : Fin ((rowFuse D hrow i).rowCuts + 1))
    (ha : (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i < a) :
    (rowFuse D hrow i).rowDiv.part a =
      D.rowDiv.part
        ((finCongr (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm
          a.succ) := by
  let Rcast : Division n ((D.rowCuts - 1) + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hpart : (Rcast.fuse fi).part a = Rcast.part a.succ :=
    Division.fuse_part_of_gt Rcast ha
  simpa [rowFuse, Rcast, fi, Division.castIndex] using hpart

/-- A column part strictly before the fused column cut is unchanged. -/
theorem colFuse_colPart_eq_of_lt {n m : ℕ}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (b : Fin ((colFuse D hcol j).colCuts + 1))
    (hb : b < (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j) :
    (colFuse D hcol j).colDiv.part b =
      D.colDiv.part
        ((finCongr (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm
          b.castSucc) := by
  let Ccast : Division m ((D.colCuts - 1) + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hpart : (Ccast.fuse fj).part b = Ccast.part b.castSucc :=
    Division.fuse_part_of_lt Ccast hb
  simpa [colFuse, Ccast, fj, Division.castIndex] using hpart

/-- A column part strictly after the fused column cut is the corresponding
shifted old part. -/
theorem colFuse_colPart_eq_of_gt {n m : ℕ}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (b : Fin ((colFuse D hcol j).colCuts + 1))
    (hb : (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j < b) :
    (colFuse D hcol j).colDiv.part b =
      D.colDiv.part
        ((finCongr (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm
          b.succ) := by
  let Ccast : Division m ((D.colCuts - 1) + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hpart : (Ccast.fuse fj).part b = Ccast.part b.succ :=
    Division.fuse_part_of_gt Ccast hb
  simpa [colFuse, Ccast, fj, Division.castIndex] using hpart

/-- A row fusion preserves bounded mixed value once the newly fused row part
has bounded mixed value on the column division. -/
theorem mixedValueAtMost_rowFuse {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hD : MixedValueAtMost M D d)
    (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (hnew :
      colMixedValue M
        ((rowFuse D hrow i).rowDiv.part
          ((finCongr
            (by simp [rowFuse]; omega :
              D.rowCuts = (rowFuse D hrow i).rowCuts + 1)) i))
        (rowFuse D hrow i).colDiv ≤ d) :
    MixedValueAtMost M (rowFuse D hrow i) d := by
  constructor
  · intro j
    exact le_trans (rowMixedValue_rowFuse_le D hrow i j) (hD.1 j)
  · intro a
    let fi : Fin ((D.rowCuts - 1) + 1) :=
      (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
    by_cases haeq : a = fi
    · subst a
      simpa [rowFuse, fi] using hnew
    · by_cases halt : a < fi
      · have hpart := rowFuse_rowPart_eq_of_lt D hrow i a halt
        rw [hpart]
        exact hD.2 _
      · have hfilt : fi < a := lt_of_le_of_ne (le_of_not_gt halt) (Ne.symm haeq)
        have hpart := rowFuse_rowPart_eq_of_gt D hrow i a hfilt
        rw [hpart]
        exact hD.2 _

/-- A column fusion preserves bounded mixed value once the newly fused column
part has bounded mixed value on the row division. -/
theorem mixedValueAtMost_colFuse {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hD : MixedValueAtMost M D d)
    (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (hnew :
      rowMixedValue M
        (colFuse D hcol j).rowDiv
        ((colFuse D hcol j).colDiv.part
          ((finCongr
            (by simp [colFuse]; omega :
              D.colCuts = (colFuse D hcol j).colCuts + 1)) j)) ≤ d) :
    MixedValueAtMost M (colFuse D hcol j) d := by
  constructor
  · intro b
    let fj : Fin ((D.colCuts - 1) + 1) :=
      (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
    by_cases hbeq : b = fj
    · subst b
      simpa [colFuse, fj] using hnew
    · by_cases hblt : b < fj
      · have hpart := colFuse_colPart_eq_of_lt D hcol j b hblt
        rw [hpart]
        exact hD.1 _
      · have hfjlt : fj < b := lt_of_le_of_ne (le_of_not_gt hblt) (Ne.symm hbeq)
        have hpart := colFuse_colPart_eq_of_gt D hcol j b hfjlt
        rw [hpart]
        exact hD.1 _
  · intro i
    exact le_trans (colMixedValue_colFuse_le D hcol j i) (hD.2 i)

/-- A good row cut gives a valid greedy fusion step. -/
theorem exists_exactFusion_of_goodRowCut {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hD : MixedValueAtMost M D d)
    (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (hnew :
      colMixedValue M
        ((rowFuse D hrow i).rowDiv.part
          ((finCongr
            (by simp [rowFuse]; omega :
              D.rowCuts = (rowFuse D hrow i).rowCuts + 1)) i))
        (rowFuse D hrow i).colDiv ≤ d) :
    ∃ E : MatrixDivision n m,
      HasExactFusion D E ∧ MixedValueAtMost M E d := by
  refine ⟨rowFuse D hrow i, Or.inl (hasRowFusion_rowFuse D hrow i), ?_⟩
  exact mixedValueAtMost_rowFuse D hD hrow i hnew

/-- A good column cut gives a valid greedy fusion step. -/
theorem exists_exactFusion_of_goodColCut {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hD : MixedValueAtMost M D d)
    (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (hnew :
      rowMixedValue M
        (colFuse D hcol j).rowDiv
        ((colFuse D hcol j).colDiv.part
          ((finCongr
            (by simp [colFuse]; omega :
              D.colCuts = (colFuse D hcol j).colCuts + 1)) j)) ≤ d) :
    ∃ E : MatrixDivision n m,
      HasExactFusion D E ∧ MixedValueAtMost M E d := by
  refine ⟨colFuse D hcol j, Or.inr (hasColFusion_colFuse D hcol j), ?_⟩
  exact mixedValueAtMost_colFuse D hD hcol j hnew

theorem hasFusionShape_of_hasRowFusion {n m : ℕ}
    {D E : MatrixDivision n m} (h : HasRowFusion D E) :
    HasFusionShape D E := by
  rcases h with ⟨hrow, hcol, _⟩
  exact Or.inl ⟨hrow, hcol⟩

theorem hasFusionShape_of_hasColFusion {n m : ℕ}
    {D E : MatrixDivision n m} (h : HasColFusion D E) :
    HasFusionShape D E := by
  rcases h with ⟨hrow, hcol, _⟩
  exact Or.inr ⟨hrow, hcol⟩

theorem hasFusionShape_of_hasExactFusion {n m : ℕ}
    {D E : MatrixDivision n m} (h : HasExactFusion D E) :
    HasFusionShape D E := by
  rcases h with h | h
  · exact hasFusionShape_of_hasRowFusion h
  · exact hasFusionShape_of_hasColFusion h

theorem cutCount_lt_of_hasFusionShape {n m : ℕ}
    {D E : MatrixDivision n m}
    (h : HasFusionShape D E) :
    cutCount E < cutCount D := by
  rcases h with h | h <;> dsimp [cutCount] <;> omega

theorem rowMixedValue_eq_zero_of_col_singleton {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) {j : Fin (D.colCuts + 1)} {c : Fin m}
    (hc : D.colDiv.part j = {c}) :
    rowMixedValue M D.rowDiv (D.colDiv.part j) = 0 := by
  classical
  have hz : rowMixedZones M D.rowDiv (D.colDiv.part j) = ∅ := by
    ext i
    simp [rowMixedZones]
    intro hmix
    exact hmix.2 (by
      intro r _ c₁ c₂ hc₁ hc₂
      have h₁ : c₁ = c := by simpa [hc] using hc₁
      have h₂ : c₂ = c := by simpa [hc] using hc₂
      subst c₁
      subst c₂
      rfl)
  have hcuts : rowMixedCuts M D.rowDiv (D.colDiv.part j) = ∅ := by
    ext i
    simp [rowMixedCuts]
    intro hmix
    exact hmix.2 (by
      constructor
      · intro c₁ c₂ hc₁ hc₂
        have h₁ : c₁ = c := by simpa [hc] using hc₁
        have h₂ : c₂ = c := by simpa [hc] using hc₂
        subst c₁
        subst c₂
        rfl
      · intro c₁ c₂ hc₁ hc₂
        have h₁ : c₁ = c := by simpa [hc] using hc₁
        have h₂ : c₂ = c := by simpa [hc] using hc₂
        subst c₁
        subst c₂
        rfl)
  simp [rowMixedValue, hz, hcuts]

theorem colMixedValue_eq_zero_of_row_singleton {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) {i : Fin (D.rowCuts + 1)} {r : Fin n}
    (hr : D.rowDiv.part i = {r}) :
    colMixedValue M (D.rowDiv.part i) D.colDiv = 0 := by
  classical
  have hz : colMixedZones M (D.rowDiv.part i) D.colDiv = ∅ := by
    ext j
    simp [colMixedZones]
    intro hmix
    exact hmix.1 (by
      intro r₁ r₂ hr₁ hr₂ c hc
      have h₁ : r₁ = r := by simpa [hr] using hr₁
      have h₂ : r₂ = r := by simpa [hr] using hr₂
      subst r₁
      subst r₂
      rfl)
  have hcuts : colMixedCuts M (D.rowDiv.part i) D.colDiv = ∅ := by
    ext j
    simp [colMixedCuts]
    intro hmix
    exact hmix.1 (by
      constructor
      · intro r₁ r₂ hr₁ hr₂
        have h₁ : r₁ = r := by simpa [hr] using hr₁
        have h₂ : r₂ = r := by simpa [hr] using hr₂
        subst r₁
        subst r₂
        rfl
      · intro r₁ r₂ hr₁ hr₂
        have h₁ : r₁ = r := by simpa [hr] using hr₁
        have h₂ : r₂ = r := by simpa [hr] using hr₂
        subst r₁
        subst r₂
        rfl)
  simp [colMixedValue, hz, hcuts]

theorem colMixedValue_le_one_of_colCuts_eq_zero {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : D.colCuts = 0)
    (R : Finset (Fin n)) :
    colMixedValue M R D.colDiv ≤ 1 := by
  rcases D with ⟨rowCuts, colCuts, rowDiv, colDiv⟩
  dsimp at hcol ⊢
  subst colCuts
  have hzones : (colMixedZones M R colDiv).card ≤ 1 := by
    calc
      (colMixedZones M R colDiv).card ≤
          (Finset.univ : Finset (Fin 1)).card := by
        exact Finset.card_le_card (by
          intro x hx
          exact Finset.mem_univ x)
      _ = 1 := by simp
  have hcuts : colMixedCuts M R colDiv = ∅ := by
    ext j
    exact Fin.elim0 j
  simpa [colMixedValue, hcuts] using hzones

theorem rowMixedValue_le_one_of_rowCuts_eq_zero {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : D.rowCuts = 0)
    (C : Finset (Fin m)) :
    rowMixedValue M D.rowDiv C ≤ 1 := by
  rcases D with ⟨rowCuts, colCuts, rowDiv, colDiv⟩
  dsimp at hrow ⊢
  subst rowCuts
  have hzones : (rowMixedZones M rowDiv C).card ≤ 1 := by
    calc
      (rowMixedZones M rowDiv C).card ≤
          (Finset.univ : Finset (Fin 1)).card := by
        exact Finset.card_le_card (by
          intro x hx
          exact Finset.mem_univ x)
      _ = 1 := by simp
  have hcuts : rowMixedCuts M rowDiv C = ∅ := by
    ext i
    exact Fin.elim0 i
  simpa [rowMixedValue, hcuts] using hzones

theorem exists_goodRowCut_of_colCuts_eq_zero {n m t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hMT : IsMarcusTardosConstant t c) (ht : 0 < t)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : D.colCuts = 0) :
    ∃ i : Fin D.rowCuts,
      colMixedValue M
        ((MatrixDivision.rowFuse D hrow i).rowDiv.part
          ((finCongr
            (by simp [MatrixDivision.rowFuse]; omega :
              D.rowCuts =
                (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
        (MatrixDivision.rowFuse D hrow i).colDiv ≤ 2 * c := by
  let i : Fin D.rowCuts := ⟨0, hrow⟩
  refine ⟨i, ?_⟩
  have hle1 :
      colMixedValue M
        ((MatrixDivision.rowFuse D hrow i).rowDiv.part
          ((finCongr
            (by simp [MatrixDivision.rowFuse]; omega :
              D.rowCuts =
                (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
        (MatrixDivision.rowFuse D hrow i).colDiv ≤ 1 :=
    colMixedValue_le_one_of_colCuts_eq_zero
      (MatrixDivision.rowFuse D hrow i) (by simp [MatrixDivision.rowFuse, hcol]) _
  have hcpos : 0 < c := IsMarcusTardosConstant.pos hMT ht
  exact le_trans hle1 (by omega)

theorem exists_goodColCut_of_rowCuts_eq_zero {n m t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hMT : IsMarcusTardosConstant t c) (ht : 0 < t)
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts) (hrow : D.rowCuts = 0) :
    ∃ j : Fin D.colCuts,
      rowMixedValue M
        (MatrixDivision.colFuse D hcol j).rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part
          ((finCongr
            (by simp [MatrixDivision.colFuse]; omega :
              D.colCuts =
                (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) ≤ 2 * c := by
  let j : Fin D.colCuts := ⟨0, hcol⟩
  refine ⟨j, ?_⟩
  have hle1 :
      rowMixedValue M
        (MatrixDivision.colFuse D hcol j).rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part
          ((finCongr
            (by simp [MatrixDivision.colFuse]; omega :
              D.colCuts =
                (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) ≤ 1 :=
    rowMixedValue_le_one_of_rowCuts_eq_zero
      (MatrixDivision.colFuse D hcol j) (by simp [MatrixDivision.colFuse, hrow]) _
  have hcpos : 0 < c := IsMarcusTardosConstant.pos hMT ht
  exact le_trans hle1 (by omega)

theorem mixedValueAtMost_of_isFinest {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : IsFinest D) :
    MixedValueAtMost M D d := by
  constructor
  · intro j
    rcases hD.2 j with ⟨c, hc⟩
    rw [rowMixedValue_eq_zero_of_col_singleton D hc]
    exact Nat.zero_le d
  · intro i
    rcases hD.1 i with ⟨r, hr⟩
    rw [colMixedValue_eq_zero_of_row_singleton D hr]
    exact Nat.zero_le d

end MatrixDivision

/-- A tail of a bounded mixed-value division sequence starting from a prescribed
division. -/
structure BoundedMixedValueDivisionTail {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ)
    (D₀ : MatrixDivision n m) where
  /-- Number of remaining fusions. -/
  stepCount : ℕ
  /-- Division at each time. -/
  division : ℕ → MatrixDivision n m
  /-- The first division is the prescribed one. -/
  starts : division 0 = D₀
  /-- The final division is coarsest. -/
  ends : MatrixDivision.IsCoarsest (division stepCount)
  /-- Consecutive divisions are related by one row or column fusion. -/
  step_fuses :
    ∀ s, s < stepCount → MatrixDivision.HasExactFusion (division s) (division (s + 1))
  /-- Every division in the tail has bounded mixed value. -/
  mixedValue_le :
    ∀ s, s ≤ stepCount → MatrixDivision.MixedValueAtMost M (division s) d

/-- A concrete division sequence all of whose divisions have mixed value at
most `d`. -/
structure BoundedMixedValueDivisionSequence {n m : ℕ}
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
  /-- Every division in the sequence has bounded mixed value. -/
  mixedValue_le :
    ∀ s, s ≤ stepCount → MatrixDivision.MixedValueAtMost M (division s) d

/-- The local greedy step used in Lemma 13: every non-coarsest division whose
mixed value is already bounded admits one fusion preserving the same bound. -/
def GreedyFusionStep {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) : Prop :=
  ∀ D : MatrixDivision n m,
    MatrixDivision.MixedValueAtMost M D d →
      ¬ MatrixDivision.IsCoarsest D →
        ∃ E : MatrixDivision n m,
          MatrixDivision.HasExactFusion D E ∧
            MatrixDivision.MixedValueAtMost M E d

/-- Greedy-step interface left after the Marcus--Tardos counting argument:
every non-coarsest bounded division has either a good row cut or a good column
cut. -/
theorem greedyFusionStep_of_goodCut {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hgood :
      ∀ D : MatrixDivision n m,
        MatrixDivision.MixedValueAtMost M D d →
          ¬ MatrixDivision.IsCoarsest D →
            (∃ hrow : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
              colMixedValue M
                ((MatrixDivision.rowFuse D hrow i).rowDiv.part
                  ((finCongr
                    (by simp [MatrixDivision.rowFuse]; omega :
                      D.rowCuts =
                        (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
                (MatrixDivision.rowFuse D hrow i).colDiv ≤ d) ∨
              (∃ hcol : 0 < D.colCuts, ∃ j : Fin D.colCuts,
                rowMixedValue M
                  (MatrixDivision.colFuse D hcol j).rowDiv
                  ((MatrixDivision.colFuse D hcol j).colDiv.part
                    ((finCongr
                      (by simp [MatrixDivision.colFuse]; omega :
                        D.colCuts =
                          (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) ≤ d)) :
    GreedyFusionStep M d := by
  intro D hD hcoarse
  rcases hgood D hD hcoarse with hrowgood | hcolgood
  · rcases hrowgood with ⟨hrow, i, hnew⟩
    exact MatrixDivision.exists_exactFusion_of_goodRowCut D hD hrow i hnew
  · rcases hcolgood with ⟨hcol, j, hnew⟩
    exact MatrixDivision.exists_exactFusion_of_goodColCut D hD hcol j hnew

namespace BoundedMixedValueDivisionTail

/-- Prepend one fusion to a bounded tail. -/
def cons {n m d : ℕ} {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDE : MatrixDivision.HasExactFusion D E)
    (hD : MatrixDivision.MixedValueAtMost M D d)
    (S : BoundedMixedValueDivisionTail M d E) :
    BoundedMixedValueDivisionTail M d D where
  stepCount := S.stepCount + 1
  division := fun s =>
    match s with
    | 0 => D
    | r + 1 => S.division r
  starts := rfl
  ends := by
    simpa using S.ends
  step_fuses := by
    intro s hs
    cases s with
    | zero =>
        simpa [S.starts] using hDE
    | succ r =>
        have hr : r < S.stepCount := by omega
        simpa using S.step_fuses r hr
  mixedValue_le := by
    intro s hs
    cases s with
    | zero =>
        simpa using hD
    | succ r =>
        have hr : r ≤ S.stepCount := by omega
        simpa using S.mixedValue_le r hr

end BoundedMixedValueDivisionTail

/-- The finite descent part of Lemma 13.  Once the local greedy-fusion step is
available, repeatedly applying it gives a bounded mixed-value division sequence
from any bounded starting division. -/
theorem exists_boundedMixedValueDivisionTail_of_greedyStep {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hstep : GreedyFusionStep M d) :
    ∀ D : MatrixDivision n m,
      MatrixDivision.MixedValueAtMost M D d →
        Nonempty (BoundedMixedValueDivisionTail M d D) := by
  classical
  intro D
  refine WellFounded.induction
    (C := fun D : MatrixDivision n m =>
      MatrixDivision.MixedValueAtMost M D d →
        Nonempty (BoundedMixedValueDivisionTail M d D))
    (InvImage.wf MatrixDivision.cutCount <| (Nat.lt_wfRel).2) D ?_
  intro D ih hD
  by_cases hcoarse : MatrixDivision.IsCoarsest D
  · exact ⟨{
      stepCount := 0
      division := fun _ => D
      starts := rfl
      ends := hcoarse
      step_fuses := by intro s hs; omega
      mixedValue_le := by intro s hs; simpa using hD
    }⟩
  · rcases hstep D hD hcoarse with ⟨E, hDE, hE⟩
    have hElt : MatrixDivision.cutCount E < MatrixDivision.cutCount D :=
      MatrixDivision.cutCount_lt_of_hasFusionShape
        (MatrixDivision.hasFusionShape_of_hasExactFusion hDE)
    rcases ih E hElt hE with ⟨S⟩
    exact ⟨BoundedMixedValueDivisionTail.cons hDE hD S⟩

/-- Convert a bounded tail from a finest division into the public sequence
object. -/
def boundedMixedValueDivisionSequence_of_tail {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D₀ : MatrixDivision n m}
    (hfinest : MatrixDivision.IsFinest D₀)
    (S : BoundedMixedValueDivisionTail M d D₀) :
    BoundedMixedValueDivisionSequence M d where
  stepCount := S.stepCount
  division := S.division
  starts := by
    rw [S.starts]
    exact hfinest
  ends := S.ends
  step_fuses := S.step_fuses
  mixedValue_le := S.mixedValue_le

/-- Lemma 13 reduced to its local greedy-fusion step and a bounded finest
starting division.  The Marcus--Tardos auxiliary-matrix argument supplies the
local greedy step; see
`greedyFusionStep_of_marcusTardos` for the fully proved explicit constant used
in this formalization. -/
theorem boundedMixedValueDivisionSequence_of_greedyStep {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D₀ : MatrixDivision n m}
    (hfinest : MatrixDivision.IsFinest D₀)
    (hD₀ : MatrixDivision.MixedValueAtMost M D₀ d)
    (hstep : GreedyFusionStep M d) :
    Nonempty (BoundedMixedValueDivisionSequence M d) := by
  rcases exists_boundedMixedValueDivisionTail_of_greedyStep hstep D₀ hD₀ with ⟨S⟩
  exact ⟨boundedMixedValueDivisionSequence_of_tail hfinest S⟩

/-- Explicit mixed-value bound used in the formalized Lemma 13.  The paper
states a bound of the form `2 * c_t`; the finite-fiber charging formalized here
uses the harmless constant `20`. -/
def lemma13MixedValueBound (c : ℕ → ℕ) (t : ℕ) : ℕ :=
  20 * c t

/-- Nondegenerate Marcus--Tardos counting step for Lemma 13 with the explicit
finite-fiber constant used in this formalization. -/
theorem pairedMarcusTardosCountingStep
    {c : ℕ → ℕ} :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
      (_hMT : IsMarcusTardosConstant t (c t)) (_hfree : MixedFree M t)
      (D : MatrixDivision n m),
        MatrixDivision.MixedValueAtMost M D (lemma13MixedValueBound c t) →
          0 < D.rowCuts → 0 < D.colCuts →
            ¬ (∃ hrow : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
              colMixedValue M
                ((MatrixDivision.rowFuse D hrow i).rowDiv.part
                  ((finCongr
                    (by simp [MatrixDivision.rowFuse]; omega :
                      D.rowCuts =
                        (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
                (MatrixDivision.rowFuse D hrow i).colDiv ≤
                  lemma13MixedValueBound c t) →
            ¬ (∃ hcol : 0 < D.colCuts, ∃ j : Fin D.colCuts,
              rowMixedValue M
                (MatrixDivision.colFuse D hcol j).rowDiv
                ((MatrixDivision.colFuse D hcol j).colDiv.part
                  ((finCongr
                    (by simp [MatrixDivision.colFuse]; omega :
                      D.colCuts =
                        (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) ≤
                lemma13MixedValueBound c t) →
              False := by
  intro n m M t hMT hfree D _hD hrow hcol hbadRow hbadCol
  classical
  let p := Division.pairCount (D.rowCuts + 1)
  let q := Division.pairCount (D.colCuts + 1)
  have htwice_p : c t * p + c t * p = p * (2 * c t) := by
    ring
  have htwice_q : c t * q + c t * q = q * (2 * c t) := by
    ring
  by_cases hpq : q ≤ p
  · have hfib :
        ∀ a : Fin p, 2 * c t < (MatrixDivision.rowPairAuxFiber M D hrow hcol a).card := by
      intro a
      have hgt := MatrixDivision.colMixedItems_rowPair_card_gt_of_no_good_row
        (M := M) (d := lemma13MixedValueBound c t) D hrow hbadRow a
      have hle := MatrixDivision.colMixedItems_rowPair_card_le_ten_mul_rowPairAuxFiber_card
        (M := M) D hrow hcol a
      dsimp [p, lemma13MixedValueBound] at hgt hle
      omega
    have hlower := MatrixDivision.rowPairAuxTargets_card_gt_of_fibers_gt
      (M := M) (d := 2 * c t) D hrow hcol (by simpa [p] using hfib)
    have hupper := MatrixDivision.rowPairAuxTargets_card_lt
      (M := M) D hrow hcol hMT hfree
    have hmax : max p q = p := max_eq_left hpq
    have hupper' :
        (MatrixDivision.rowPairAuxTargets M D hrow hcol).card < p * (2 * c t) := by
      simpa [p, q, hmax, htwice_p] using hupper
    have hlow' :
        p * (2 * c t) < (MatrixDivision.rowPairAuxTargets M D hrow hcol).card := by
      simpa [p] using hlower
    exact (not_lt_of_ge (le_of_lt hupper')) hlow'
  · have hqp : p ≤ q := le_of_not_ge hpq
    have hfib :
        ∀ b : Fin q, 2 * c t < (MatrixDivision.colPairAuxFiber M D hrow hcol b).card := by
      intro b
      have hgt := MatrixDivision.rowMixedItems_colPair_card_gt_of_no_good_col
        (M := M) (d := lemma13MixedValueBound c t) D hcol hbadCol b
      have hle := MatrixDivision.rowMixedItems_colPair_card_le_ten_mul_colPairAuxFiber_card
        (M := M) D hrow hcol b
      dsimp [q, lemma13MixedValueBound] at hgt hle
      omega
    have hlower := MatrixDivision.colPairAuxTargets_card_gt_of_fibers_gt
      (M := M) (d := 2 * c t) D hrow hcol (by simpa [q] using hfib)
    have hupper := MatrixDivision.colPairAuxTargets_card_lt
      (M := M) D hrow hcol hMT hfree
    have hmax : max p q = q := max_eq_right hqp
    have hupper' :
        (MatrixDivision.colPairAuxTargets M D hrow hcol).card < q * (2 * c t) := by
      simpa [p, q, hmax, htwice_q] using hupper
    have hlow' :
        q * (2 * c t) < (MatrixDivision.colPairAuxTargets M D hrow hcol).card := by
      simpa [q] using hlower
    exact (not_lt_of_ge (le_of_lt hupper')) hlow'

/-- Local greedy-fusion step in the proved form of Lemma 13. -/
theorem greedyFusionStep_of_marcusTardos
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ),
      MixedFree M t → GreedyFusionStep M (lemma13MixedValueBound c t) := by
  intro n m M t hfree
  by_cases ht : t = 0
  · subst t
    exact (False.elim (hfree (hasMixedMinor_zero M)))
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    apply greedyFusionStep_of_goodCut
    intro D hD hcoarse
    by_cases hrow : 0 < D.rowCuts
    · by_cases hcol : 0 < D.colCuts
      · by_cases hgoodRow :
          ∃ hrow' : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
            colMixedValue M
              ((MatrixDivision.rowFuse D hrow' i).rowDiv.part
                ((finCongr
                  (by simp [MatrixDivision.rowFuse]; omega :
                    D.rowCuts =
                      (MatrixDivision.rowFuse D hrow' i).rowCuts + 1)) i))
              (MatrixDivision.rowFuse D hrow' i).colDiv ≤
                lemma13MixedValueBound c t
        · exact Or.inl hgoodRow
        · by_cases hgoodCol :
            ∃ hcol' : 0 < D.colCuts, ∃ j : Fin D.colCuts,
              rowMixedValue M
                (MatrixDivision.colFuse D hcol' j).rowDiv
                ((MatrixDivision.colFuse D hcol' j).colDiv.part
                  ((finCongr
                    (by simp [MatrixDivision.colFuse]; omega :
                      D.colCuts =
                        (MatrixDivision.colFuse D hcol' j).colCuts + 1)) j)) ≤
                lemma13MixedValueBound c t
          · exact Or.inr hgoodCol
          · exact False.elim
              (pairedMarcusTardosCountingStep
                M t (hMT t) hfree D hD hrow hcol hgoodRow hgoodCol)
      · have hcol0 : D.colCuts = 0 := Nat.eq_zero_of_not_pos hcol
        rcases MatrixDivision.exists_goodRowCut_of_colCuts_eq_zero
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
      rcases MatrixDivision.exists_goodColCut_of_rowCuts_eq_zero
        (M := M) (hMT t) htpos D hcol hrow0 with ⟨j, hj⟩
      exact Or.inr ⟨hcol, j, le_trans hj (by
        have hcpos : 0 < c t := IsMarcusTardosConstant.pos (hMT t) htpos
        simp [lemma13MixedValueBound]
        omega)⟩

/-- Positive-size matrix form of Lemma 13 proved from Marcus--Tardos, with the
explicit finite-fiber constant used in this formalization. -/
theorem boundedMixedValueDivisionSequence_positive_of_marcusTardos
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      (M : _root_.Matrix (Fin n) (Fin m) α) → (t : ℕ) →
        MixedFree M t →
          Nonempty (BoundedMixedValueDivisionSequence M (lemma13MixedValueBound c t)) := by
  intro n m hn hm M t hfree
  exact boundedMixedValueDivisionSequence_of_greedyStep
    (MatrixDivision.finest_isFinest hn hm)
    (MatrixDivision.mixedValueAtMost_of_isFinest
      (MatrixDivision.finest_isFinest hn hm))
    (greedyFusionStep_of_marcusTardos hMT M t hfree)

/-- The greedy-step form of Lemma 13 with the explicit `20 * c_t` bound. -/
theorem greedyFusionProducesBoundedMixedValueSequence
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
      (D₀ : MatrixDivision n m),
        MixedFree M t →
          MatrixDivision.IsFinest D₀ →
            GreedyFusionStep M (lemma13MixedValueBound c t) := by
  intro n m M t _D₀ hfree _hfinest
  exact greedyFusionStep_of_marcusTardos hMT M t hfree

/-- Reusable positive-size Lemma 13 with the explicit `20 * c_t` bound.

The positive-size hypotheses are necessary because a `Division 0 1` cannot
have a nonempty part. -/
theorem boundedMixedValueDivisionSequenceTheorem
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      ∀ (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ),
        MixedFree M t →
          Nonempty (BoundedMixedValueDivisionSequence M (lemma13MixedValueBound c t)) := by
  intro n m hn hm M t hfree
  exact boundedMixedValueDivisionSequence_positive_of_marcusTardos
    hMT hn hm M t hfree

/-- Sequence-level form of Lemma 13, once the greedy-fusion argument has been
proved from the grid-form Marcus--Tardos theorem. -/
theorem boundedMixedValueDivisionSequence_of_greedyFusion
    {c : ℕ → ℕ}
    (hgreedy :
      ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
        (D₀ : MatrixDivision n m),
          MixedFree M t →
            MatrixDivision.IsFinest D₀ →
              GreedyFusionStep M (lemma13MixedValueBound c t)) :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
      (D₀ : MatrixDivision n m),
        MixedFree M t →
          MatrixDivision.IsFinest D₀ →
            Nonempty (BoundedMixedValueDivisionSequence M (lemma13MixedValueBound c t)) := by
  intro n m M t D₀ hfree hfinest
  exact boundedMixedValueDivisionSequence_of_greedyStep hfinest
    (MatrixDivision.mixedValueAtMost_of_isFinest hfinest)
    (hgreedy M t D₀ hfree hfinest)

/-- Positive-size matrix form: using the canonical singleton division as the
finest starting point. -/
theorem boundedMixedValueDivisionSequence_of_greedyFusion_positive
    {c : ℕ → ℕ}
    (hgreedy :
      ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
        (D₀ : MatrixDivision n m),
          MixedFree M t →
            MatrixDivision.IsFinest D₀ →
              GreedyFusionStep M (lemma13MixedValueBound c t))
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
    (hfree : MixedFree M t) :
    Nonempty (BoundedMixedValueDivisionSequence M (lemma13MixedValueBound c t)) :=
  boundedMixedValueDivisionSequence_of_greedyFusion hgreedy M t
    (MatrixDivision.finest hn hm) hfree (MatrixDivision.finest_isFinest hn hm)

/-- Contract theorem for
`DivisionSequenceContract.lemma13_bounded_mixed_value_division_sequence`.

If `M` is positive-size and `t`-mixed-free, then it has a full division sequence
whose mixed value is bounded by `20 * c t`, for any Marcus--Tardos constant
family `c`. -/
theorem lemma13_bounded_mixed_value_division_sequence
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      ∀ (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ),
        MixedFree M t →
          Nonempty (BoundedMixedValueDivisionSequence M (20 * c t)) := by
  intro n m hn hm M t hfree
  simpa [lemma13MixedValueBound] using
    boundedMixedValueDivisionSequenceTheorem hMT hn hm M t hfree

end Matrix
end Lax4Proofs.TwinWidth
