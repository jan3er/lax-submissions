import Lax2Proofs.Source.TwinWidth.Matrix.Theorem10Defs

/-!
# Matrix theorem 10

This file proves the matrix Theorem 10 interface.  It contains the ordered
first item, the Lemma 13 mixed-value sequence packaging, the Section 5.8 profile
refinement from bounded mixed value to bounded error value, and the Lemma 8
expansion from bounded-refinement partition sequences to matrix contraction
sequences.
-/

namespace Lax2Proofs.TwinWidth
namespace Matrix

universe u

variable {α : Type u}

/-- Negating verticality produces two rows and one column witnessing different
entries. -/
theorem not_cellVertical_iff_exists {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    ¬ CellVertical M R C i j ↔
      ∃ r₁, r₁ ∈ R.part i ∧
        ∃ r₂, r₂ ∈ R.part i ∧
          ∃ c, c ∈ C.part j ∧ M r₁ c ≠ M r₂ c := by
  classical
  simp [CellVertical]

/-- Negating horizontality produces one row and two columns witnessing
different entries. -/
theorem not_cellHorizontal_iff_exists {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    ¬ CellHorizontal M R C i j ↔
      ∃ r, r ∈ R.part i ∧
        ∃ c₁, c₁ ∈ C.part j ∧
          ∃ c₂, c₂ ∈ C.part j ∧ M r c₁ ≠ M r c₂ := by
  classical
  simp [CellHorizontal]

namespace Division

/-- If two separated parts of a division meet the same convex part of another
division, then every part between them is contained in that convex part. -/
theorem part_subset_of_between_mem_same_part {n k l : ℕ}
    (A : Division n k) (D : Division n l)
    {p mid q : Fin k} {b : Fin l}
    (hpm : p < mid) (hmq : mid < q)
    {x y : Fin n}
    (hxA : x ∈ A.part p) (hxD : x ∈ D.part b)
    (hyA : y ∈ A.part q) (hyD : y ∈ D.part b) :
    A.part mid ⊆ D.part b := by
  intro z hz
  have hxz : x < z := A.part_ordered hpm hxA hz
  have hzy : z < y := A.part_ordered hmq hz hyA
  exact D.part_convex b hxD hyD (le_of_lt hxz) (le_of_lt hzy)

end Division

namespace MatrixDivision

/-- A division has swallowed one row or column block of a proposed mixed minor
when some mixed-minor row part is contained in one row part of the division, or
some mixed-minor column part is contained in one column part of the division. -/
def ContainsMinorBlock {n m k : ℕ}
    (R : Division n k) (C : Division m k) (D : MatrixDivision n m) : Prop :=
  (∃ i : Fin k, ∃ a : Fin (D.rowCuts + 1), R.part i ⊆ D.rowDiv.part a) ∨
    ∃ j : Fin k, ∃ b : Fin (D.colCuts + 1), C.part j ⊆ D.colDiv.part b

/-- A coarsest division contains every mixed-minor block on both sides. -/
theorem containsMinorBlock_of_isCoarsest {n m k : ℕ}
    (R : Division n k) (C : Division m k) {D : MatrixDivision n m}
    (hD : IsCoarsest D) (hk : 0 < k) :
    ContainsMinorBlock R C D := by
  rcases hD with ⟨hrow, _hcol⟩
  left
  let i : Fin k := ⟨0, hk⟩
  let a : Fin (D.rowCuts + 1) := ⟨0, by omega⟩
  refine ⟨i, a, ?_⟩
  intro x hx
  rcases D.rowDiv.part_cover x with ⟨b, hb⟩
  have hba : b = a := by
    apply Fin.ext
    omega
  simpa [hba] using hb

/-- At the finest division, no block of a positive mixed minor has already been
swallowed by a singleton row or column part. -/
theorem not_containsMinorBlock_of_isFinest_of_mixed {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m k} {D : MatrixDivision n m}
    (hk : 0 < k) (hD : IsFinest D)
    (hmix : ∀ i j : Fin k, CellMixed M R C i j) :
    ¬ ContainsMinorBlock R C D := by
  classical
  intro hcontains
  let j₀ : Fin k := ⟨0, hk⟩
  rcases hcontains with ⟨i, a, hsub⟩ | ⟨j, b, hsub⟩
  · rcases hD.1 a with ⟨r, ha⟩
    have hvert : CellVertical M R C i j₀ := by
      intro r₁ r₂ hr₁ hr₂ c hc
      have hr₁_eq : r₁ = r := by
        have : r₁ ∈ ({r} : Finset (Fin n)) := by
          simpa [ha] using hsub hr₁
        simpa using this
      have hr₂_eq : r₂ = r := by
        have : r₂ ∈ ({r} : Finset (Fin n)) := by
          simpa [ha] using hsub hr₂
        simpa using this
      simp [hr₁_eq, hr₂_eq]
    exact (hmix i j₀).1 hvert
  · rcases hD.2 b with ⟨c, hb⟩
    have hhor : CellHorizontal M R C j₀ j := by
      intro r hr c₁ c₂ hc₁ hc₂
      have hc₁_eq : c₁ = c := by
        have : c₁ ∈ ({c} : Finset (Fin m)) := by
          simpa [hb] using hsub hc₁
        simpa using this
      have hc₂_eq : c₂ = c := by
        have : c₂ ∈ ({c} : Finset (Fin m)) := by
          simpa [hb] using hsub hc₂
        simpa using this
      simp [hc₁_eq, hc₂_eq]
    exact (hmix j₀ j).2 hhor

/-- A column fusion leaves the row division unchanged, so any swallowed row
minor block after the fusion was already swallowed before it. -/
theorem rowBlock_subset_prev_of_hasColFusion {n m k : ℕ}
    {R : Division n k} {C : Division m k} {D E : MatrixDivision n m}
    (hDE : HasColFusion D E)
    (hrow :
      ∃ i : Fin k, ∃ a : Fin (E.rowCuts + 1), R.part i ⊆ E.rowDiv.part a) :
    ContainsMinorBlock R C D := by
  rcases hDE with ⟨hrowCuts, _hcolCuts, _j, hrows, _hcols⟩
  rcases hrow with ⟨i, a, hsub⟩
  left
  let aD : Fin (D.rowCuts + 1) :=
    (finCongr (by omega : E.rowCuts + 1 = D.rowCuts + 1)) a
  refine ⟨i, aD, ?_⟩
  intro x hx
  have hxE := hsub hx
  have hpart := hrows a
  rw [hpart] at hxE
  simpa [Division.castIndex, aD] using hxE

/-- A row fusion leaves the column division unchanged, so any swallowed column
minor block after the fusion was already swallowed before it. -/
theorem colBlock_subset_prev_of_hasRowFusion {n m k : ℕ}
    {R : Division n k} {C : Division m k} {D E : MatrixDivision n m}
    (hDE : HasRowFusion D E)
    (hcol :
      ∃ j : Fin k, ∃ b : Fin (E.colCuts + 1), C.part j ⊆ E.colDiv.part b) :
    ContainsMinorBlock R C D := by
  rcases hDE with ⟨_hrowCuts, hcolCuts, _i, _hrows, hcols⟩
  rcases hcol with ⟨j, b, hsub⟩
  right
  let bD : Fin (D.colCuts + 1) :=
    (finCongr (by omega : E.colCuts + 1 = D.colCuts + 1)) b
  refine ⟨j, bD, ?_⟩
  intro x hx
  have hxE := hsub hx
  have hpart := hcols b
  rw [hpart] at hxE
  simpa [Division.castIndex, bD] using hxE

end MatrixDivision

/-- Row-side counting core of the first item of Theorem 10.

If one row block of a `k`-mixed minor is contained in a row part of a division,
while no column block of the mixed minor is contained in any column part, then
the containing row part sees at least one nonconstant error for every other
minor column block.  Taking the even-indexed column blocks gives `d + 2`
distinct errors when `2 * d + 2 < k`, contradicting error value at most `d`. -/
theorem false_of_rowBlock_subset_of_no_colBlock_subset {n m k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m k} {D : MatrixDivision n m}
    (hk : 2 * d + 2 < k)
    (hmix : ∀ i j : Fin k, CellMixed M R C i j)
    (herror : MatrixDivision.NonconstantErrorValueAtMost M D d)
    {i : Fin k} {a : Fin (D.rowCuts + 1)}
    (hrow : R.part i ⊆ D.rowDiv.part a)
    (hnoCol : ¬ ∃ j : Fin k, ∃ b : Fin (D.colCuts + 1),
      C.part j ⊆ D.colDiv.part b) :
    False := by
  classical
  let idx : Fin (d + 2) → Fin k := fun u => ⟨2 * u.1, by omega⟩
  have hwit :
      ∀ u : Fin (d + 2),
        ∃ r₁, r₁ ∈ R.part i ∧
          ∃ r₂, r₂ ∈ R.part i ∧
            ∃ c, c ∈ C.part (idx u) ∧ M r₁ c ≠ M r₂ c := by
    intro u
    exact (not_cellVertical_iff_exists M R C i (idx u)).mp (hmix i (idx u)).1
  choose r₁ hr₁ hrest₁ using hwit
  choose r₂ hr₂ hrest₂ using hrest₁
  choose c hc hneq using hrest₂
  have hcover : ∀ u : Fin (d + 2), ∃ b : Fin (D.colCuts + 1), c u ∈ D.colDiv.part b := by
    intro u
    exact D.colDiv.part_cover (c u)
  choose b hb using hcover
  have hnotconst :
      ∀ u : Fin (d + 2),
        ¬ ZoneConstant M (D.rowDiv.part a) (D.colDiv.part (b u)) := by
    intro u hconst
    exact hneq u (hconst (hrow (hr₁ u)) (hrow (hr₂ u)) (hb u) (hb u))
  have hb_mem :
      ∀ u : Fin (d + 2), b u ∈ MatrixDivision.nonconstantRowErrorSet M D a := by
    intro u
    simp [MatrixDivision.nonconstantRowErrorSet, hnotconst u]
  have hbinj : Function.Injective b := by
    intro u v huv
    by_cases huv' : u = v
    · exact huv'
    · rcases lt_or_gt_of_ne huv' with huvlt | hvult
      · have hmid_lt : 2 * u.1 + 1 < k := by omega
        let mid : Fin k := ⟨2 * u.1 + 1, hmid_lt⟩
        have hidx_mid : idx u < mid := by
          rw [Fin.lt_def]
          simp [idx, mid]
        have hmid_idx : mid < idx v := by
          rw [Fin.lt_def]
          simp [idx, mid]
          omega
        have hsubset : C.part mid ⊆ D.colDiv.part (b u) :=
          Division.part_subset_of_between_mem_same_part C D.colDiv
            hidx_mid hmid_idx
            (hc u) (hb u) (hc v) (by simpa [huv] using hb v)
        exact False.elim (hnoCol ⟨mid, b u, hsubset⟩)
      · have hmid_lt : 2 * v.1 + 1 < k := by omega
        let mid : Fin k := ⟨2 * v.1 + 1, hmid_lt⟩
        have hidx_mid : idx v < mid := by
          rw [Fin.lt_def]
          simp [idx, mid]
        have hmid_idx : mid < idx u := by
          rw [Fin.lt_def]
          simp [idx, mid]
          omega
        have hsubset : C.part mid ⊆ D.colDiv.part (b v) :=
          Division.part_subset_of_between_mem_same_part C D.colDiv
            hidx_mid hmid_idx
            (hc v) (hb v) (hc u) (by simpa [huv] using hb u)
        exact False.elim (hnoCol ⟨mid, b v, hsubset⟩)
  have hsubset_image :
      (Finset.univ.image b : Finset (Fin (D.colCuts + 1))) ⊆
        MatrixDivision.nonconstantRowErrorSet M D a := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨u, _hu, rfl⟩
    exact hb_mem u
  have hcard :
      d + 2 ≤ (MatrixDivision.nonconstantRowErrorSet M D a).card := by
    calc
      d + 2 = (Finset.univ : Finset (Fin (d + 2))).card := by simp
      _ = (Finset.univ.image b : Finset (Fin (D.colCuts + 1))).card := by
        rw [Finset.card_image_of_injective _ hbinj]
      _ ≤ (MatrixDivision.nonconstantRowErrorSet M D a).card :=
        Finset.card_le_card hsubset_image
  have hle := herror.1 a
  omega

/-- Column-side counting core of the first item of Theorem 10, dual to
`false_of_rowBlock_subset_of_no_colBlock_subset`. -/
theorem false_of_colBlock_subset_of_no_rowBlock_subset {n m k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m k} {D : MatrixDivision n m}
    (hk : 2 * d + 2 < k)
    (hmix : ∀ i j : Fin k, CellMixed M R C i j)
    (herror : MatrixDivision.NonconstantErrorValueAtMost M D d)
    {j : Fin k} {b : Fin (D.colCuts + 1)}
    (hcol : C.part j ⊆ D.colDiv.part b)
    (hnoRow : ¬ ∃ i : Fin k, ∃ a : Fin (D.rowCuts + 1),
      R.part i ⊆ D.rowDiv.part a) :
    False := by
  classical
  let idx : Fin (d + 2) → Fin k := fun u => ⟨2 * u.1, by omega⟩
  have hwit :
      ∀ u : Fin (d + 2),
        ∃ r, r ∈ R.part (idx u) ∧
          ∃ c₁, c₁ ∈ C.part j ∧
            ∃ c₂, c₂ ∈ C.part j ∧ M r c₁ ≠ M r c₂ := by
    intro u
    exact (not_cellHorizontal_iff_exists M R C (idx u) j).mp (hmix (idx u) j).2
  choose r hr hrest₁ using hwit
  choose c₁ hc₁ hrest₂ using hrest₁
  choose c₂ hc₂ hneq using hrest₂
  have hcover : ∀ u : Fin (d + 2), ∃ a : Fin (D.rowCuts + 1), r u ∈ D.rowDiv.part a := by
    intro u
    exact D.rowDiv.part_cover (r u)
  choose a ha using hcover
  have hnotconst :
      ∀ u : Fin (d + 2),
        ¬ ZoneConstant M (D.rowDiv.part (a u)) (D.colDiv.part b) := by
    intro u hconst
    exact hneq u (hconst (ha u) (ha u) (hcol (hc₁ u)) (hcol (hc₂ u)))
  have ha_mem :
      ∀ u : Fin (d + 2), a u ∈ MatrixDivision.nonconstantColErrorSet M D b := by
    intro u
    simp [MatrixDivision.nonconstantColErrorSet, hnotconst u]
  have hainj : Function.Injective a := by
    intro u v huv
    by_cases huv' : u = v
    · exact huv'
    · rcases lt_or_gt_of_ne huv' with huvlt | hvult
      · have hmid_lt : 2 * u.1 + 1 < k := by omega
        let mid : Fin k := ⟨2 * u.1 + 1, hmid_lt⟩
        have hidx_mid : idx u < mid := by
          rw [Fin.lt_def]
          simp [idx, mid]
        have hmid_idx : mid < idx v := by
          rw [Fin.lt_def]
          simp [idx, mid]
          omega
        have hsubset : R.part mid ⊆ D.rowDiv.part (a u) :=
          Division.part_subset_of_between_mem_same_part R D.rowDiv
            hidx_mid hmid_idx
            (hr u) (ha u) (hr v) (by simpa [huv] using ha v)
        exact False.elim (hnoRow ⟨mid, a u, hsubset⟩)
      · have hmid_lt : 2 * v.1 + 1 < k := by omega
        let mid : Fin k := ⟨2 * v.1 + 1, hmid_lt⟩
        have hidx_mid : idx v < mid := by
          rw [Fin.lt_def]
          simp [idx, mid]
        have hmid_idx : mid < idx u := by
          rw [Fin.lt_def]
          simp [idx, mid]
          omega
        have hsubset : R.part mid ⊆ D.rowDiv.part (a v) :=
          Division.part_subset_of_between_mem_same_part R D.rowDiv
            hidx_mid hmid_idx
            (hr v) (ha v) (hr u) (by simpa [huv] using ha u)
        exact False.elim (hnoRow ⟨mid, a v, hsubset⟩)
  have hsubset_image :
      (Finset.univ.image a : Finset (Fin (D.rowCuts + 1))) ⊆
        MatrixDivision.nonconstantColErrorSet M D b := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨u, _hu, rfl⟩
    exact ha_mem u
  have hcard :
      d + 2 ≤ (MatrixDivision.nonconstantColErrorSet M D b).card := by
    calc
      d + 2 = (Finset.univ : Finset (Fin (d + 2))).card := by simp
      _ = (Finset.univ.image a : Finset (Fin (D.rowCuts + 1))).card := by
        rw [Finset.card_image_of_injective _ hainj]
      _ ≤ (MatrixDivision.nonconstantColErrorSet M D b).card :=
        Finset.card_le_card hsubset_image
  have hle := herror.2 b
  omega

/-- Ordered first item of matrix Theorem 10: a bounded-error division sequence
for the current row and column orders bounds the matrix mixed number linearly. -/
theorem theorem10_ordered_matrix_mixed_number_le_of_twin_ordered_at_most
    {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) :
    MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ 2 * d + 2 := by
  classical
  rintro ⟨S⟩
  by_contra hle
  have hkgt : 2 * d + 2 < matrixMixedNumber M := Nat.lt_of_not_ge hle
  have hkpos : 0 < matrixMixedNumber M := by omega
  rcases hasMixedMinor_matrixMixedNumber M with hzero | hminor
  · omega
  rcases hminor with ⟨R, C, hmix⟩
  let P : ℕ → Prop := fun s =>
    s ≤ S.stepCount ∧ MatrixDivision.ContainsMinorBlock R C (S.division s)
  have hex : ∃ s, P s := by
    refine ⟨S.stepCount, le_rfl, ?_⟩
    exact MatrixDivision.containsMinorBlock_of_isCoarsest R C S.ends hkpos
  let s : ℕ := Nat.find hex
  have hsP : P s := Nat.find_spec hex
  cases hs : s with
  | zero =>
      have hcontains0 : MatrixDivision.ContainsMinorBlock R C (S.division 0) := by
        simpa [P, s, hs] using hsP.2
      exact (MatrixDivision.not_containsMinorBlock_of_isFinest_of_mixed
        hkpos S.starts hmix) hcontains0
  | succ t =>
      have hcur : MatrixDivision.ContainsMinorBlock R C (S.division (t + 1)) := by
        simpa [P, s, hs] using hsP.2
      have hsle : t + 1 ≤ S.stepCount := by
        simpa [P, s, hs] using hsP.1
      have htstep : t < S.stepCount := by omega
      have hprev_not :
          ¬ MatrixDivision.ContainsMinorBlock R C (S.division t) := by
        intro hprev
        have htP : P t := ⟨by omega, hprev⟩
        have hmin : s ≤ t := Nat.find_min' hex htP
        omega
      have hstep := S.step_fuses t htstep
      rcases hcur with hrowcur | hcolcur
      · rcases hstep with hrowF | hcolF
        · have hnoCol :
              ¬ ∃ j : Fin (matrixMixedNumber M),
                  ∃ b : Fin ((S.division (t + 1)).colCuts + 1),
                    C.part j ⊆ (S.division (t + 1)).colDiv.part b := by
            intro hcol
            exact hprev_not
              (MatrixDivision.colBlock_subset_prev_of_hasRowFusion hrowF hcol)
          rcases hrowcur with ⟨i, a, hrow⟩
          exact false_of_rowBlock_subset_of_no_colBlock_subset
            hkgt hmix (S.errorValue_le (t + 1) hsle) hrow hnoCol
        · exact False.elim
            (hprev_not
              (MatrixDivision.rowBlock_subset_prev_of_hasColFusion hcolF hrowcur))
      · rcases hstep with hrowF | hcolF
        · exact False.elim
            (hprev_not
              (MatrixDivision.colBlock_subset_prev_of_hasRowFusion hrowF hcolcur))
        · have hnoRow :
              ¬ ∃ i : Fin (matrixMixedNumber M),
                  ∃ a : Fin ((S.division (t + 1)).rowCuts + 1),
                    R.part i ⊆ (S.division (t + 1)).rowDiv.part a := by
            intro hrow
            exact hprev_not
              (MatrixDivision.rowBlock_subset_prev_of_hasColFusion hcolF hrow)
          rcases hcolcur with ⟨j, b, hcol⟩
          exact false_of_colBlock_subset_of_no_rowBlock_subset
            hkgt hmix (S.errorValue_le (t + 1) hsle) hcol hnoRow

/-- Predicate-wrapper form of the first item of matrix Theorem 10. -/
theorem theorem10_first_item_ordered :
    MatrixMixedNumberBoundedByTwinOrdered (α := α) theorem10MatrixMixedNumberBound := by
  intro n m d M hM
  exact theorem10_ordered_matrix_mixed_number_le_of_twin_ordered_at_most M hM

namespace MatrixPartition

/-- Split every part of a finite partition according to a label function
attached to that base part.  Empty fibers are discarded. -/
noncomputable def splitPartsByLabel {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    (P : Finset (Finset α)) (label : Finset α → α → β) :
    Finset (Finset α) := by
  classical
  exact
    (P.biUnion fun A =>
      (Finset.univ : Finset β).image fun b =>
        A.filter fun x => label A x = b).filter fun A => A.Nonempty

theorem mem_splitPartsByLabel {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    {F : Finset α} :
    F ∈ splitPartsByLabel P label ↔
      F.Nonempty ∧
        ∃ A ∈ P, ∃ b : β, F = A.filter fun x => label A x = b := by
  classical
  unfold splitPartsByLabel
  rw [Finset.mem_filter, Finset.mem_biUnion]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨A, hA, b, hFb⟩, hF⟩
    exact ⟨hF, A, hA, b, hFb.symm⟩
  · rintro ⟨hF, A, hA, b, rfl⟩
    exact ⟨⟨A, hA, b, rfl⟩, hF⟩

theorem splitPartsByLabel_subset_base {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    {F : Finset α}
    (hF : F ∈ splitPartsByLabel P label) :
    ∃ A ∈ P, F ⊆ A := by
  classical
  rcases (mem_splitPartsByLabel.mp hF).2 with ⟨A, hA, b, rfl⟩
  exact ⟨A, hA, by intro x hx; exact (Finset.mem_filter.mp hx).1⟩

theorem splitPartsByLabel_nonempty {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    {F : Finset α}
    (hF : F ∈ splitPartsByLabel P label) :
    F.Nonempty :=
  (mem_splitPartsByLabel.mp hF).1

theorem splitPartsByLabel_cover {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    (hcover : ∀ x : α, ∃ A ∈ P, x ∈ A) :
    ∀ x : α, ∃ F ∈ splitPartsByLabel P label, x ∈ F := by
  classical
  intro x
  rcases hcover x with ⟨A, hA, hxA⟩
  let F : Finset α := A.filter fun y => label A y = label A x
  have hxF : x ∈ F := by simp [F, hxA]
  have hFnon : F.Nonempty := ⟨x, hxF⟩
  have hFmem : F ∈ splitPartsByLabel P label := by
    rw [mem_splitPartsByLabel]
    exact ⟨hFnon, A, hA, label A x, rfl⟩
  exact ⟨F, hFmem, hxF⟩

theorem splitPartsByLabel_disjoint {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    (hdisj : ∀ ⦃A B⦄, A ∈ P → B ∈ P → A ≠ B → Disjoint A B)
    {F G : Finset α}
    (hF : F ∈ splitPartsByLabel P label)
    (hG : G ∈ splitPartsByLabel P label)
    (hFG : F ≠ G) :
    Disjoint F G := by
  classical
  rw [Finset.disjoint_left]
  intro x hxF hxG
  rcases (mem_splitPartsByLabel.mp hF).2 with ⟨A, hA, b, hFdef⟩
  rcases (mem_splitPartsByLabel.mp hG).2 with ⟨B, hB, c, hGdef⟩
  subst F
  subst G
  have hxA : x ∈ A := (Finset.mem_filter.mp hxF).1
  have hxb : label A x = b := (Finset.mem_filter.mp hxF).2
  have hxB : x ∈ B := (Finset.mem_filter.mp hxG).1
  have hxc : label B x = c := (Finset.mem_filter.mp hxG).2
  by_cases hAB : A = B
  · subst B
    have hbc : b = c := hxb.symm.trans hxc
    apply hFG
    simp [hbc]
  · exact Finset.disjoint_left.mp (hdisj hA hB hAB) hxA hxB

/-- Refining each row part and each column part by bounded labels gives a
matrix partition. -/
noncomputable def refineByLabels {n m : ℕ} {β γ : Type*}
    [DecidableEq β] [Fintype β] [DecidableEq γ] [Fintype γ]
    (P : MatrixPartition n m)
    (rowLabel : Finset (Fin n) → Fin n → β)
    (colLabel : Finset (Fin m) → Fin m → γ) :
    MatrixPartition n m where
  rowParts := splitPartsByLabel P.rowParts rowLabel
  row_nonempty := by
    intro R hR
    exact splitPartsByLabel_nonempty hR
  row_disjoint := by
    intro R S hR hS hRS
    exact splitPartsByLabel_disjoint P.row_disjoint hR hS hRS
  row_cover := by
    exact splitPartsByLabel_cover P.row_cover
  colParts := splitPartsByLabel P.colParts colLabel
  col_nonempty := by
    intro C hC
    exact splitPartsByLabel_nonempty hC
  col_disjoint := by
    intro C D hC hD hCD
    exact splitPartsByLabel_disjoint P.col_disjoint hC hD hCD
  col_cover := by
    exact splitPartsByLabel_cover P.col_cover

@[simp] theorem rowParts_refineByLabels {n m : ℕ} {β γ : Type*}
    [DecidableEq β] [Fintype β] [DecidableEq γ] [Fintype γ]
    (P : MatrixPartition n m)
    (rowLabel : Finset (Fin n) → Fin n → β)
    (colLabel : Finset (Fin m) → Fin m → γ) :
    (P.refineByLabels rowLabel colLabel).rowParts =
      splitPartsByLabel P.rowParts rowLabel :=
  rfl

@[simp] theorem colParts_refineByLabels {n m : ℕ} {β γ : Type*}
    [DecidableEq β] [Fintype β] [DecidableEq γ] [Fintype γ]
    (P : MatrixPartition n m)
    (rowLabel : Finset (Fin n) → Fin n → β)
    (colLabel : Finset (Fin m) → Fin m → γ) :
    (P.refineByLabels rowLabel colLabel).colParts =
      splitPartsByLabel P.colParts colLabel :=
  rfl

theorem partsRRefine_splitPartsByLabel {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {r : ℕ}
    {P : Finset (Finset α)} {label : Finset α → α → β}
    (hdisj : ∀ ⦃A B⦄, A ∈ P → B ∈ P → A ≠ B → Disjoint A B)
    (hr : Fintype.card β ≤ r) :
    PartsRRefine (splitPartsByLabel P label) P r := by
  classical
  constructor
  · intro F hF
    exact splitPartsByLabel_subset_base hF
  · intro A hA
    let fibers : Finset (Finset α) :=
      (Finset.univ : Finset β).image fun b =>
        A.filter fun x => label A x = b
    have hsubset :
        (splitPartsByLabel P label).filter (fun F => F ⊆ A) ⊆ fibers := by
      intro F hF
      have hFmem : F ∈ splitPartsByLabel P label := (Finset.mem_filter.mp hF).1
      have hFsub : F ⊆ A := (Finset.mem_filter.mp hF).2
      rcases mem_splitPartsByLabel.mp hFmem with ⟨hFne, B, hB, b, hFdef⟩
      have hBA : B = A := by
        rcases hFne with ⟨x, hxF⟩
        have hxB : x ∈ B := by
          rw [hFdef] at hxF
          exact (Finset.mem_filter.mp hxF).1
        have hxA : x ∈ A := hFsub hxF
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj hB hA hne) hxB hxA
      subst B
      subst F
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
    have hcard :
        ((splitPartsByLabel P label).filter fun F => F ⊆ A).card ≤ fibers.card :=
      Finset.card_le_card hsubset
    have hfibers : fibers.card ≤ Fintype.card β := by
      calc
        fibers.card ≤ (Finset.univ : Finset β).card := Finset.card_image_le
        _ = Fintype.card β := by simp
    exact le_trans hcard (le_trans hfibers hr)

/-- Bounded refinement is preserved by compatible finite labels.  The factor
is multiplied by the number of labels: over each coarse part there are at most
`rb` old base parts, and each old base part contributes at most one fiber for
each label. -/
theorem partsRRefine_splitPartsByLabel_of_partsRRefine {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {rb : ℕ}
    {P Q : Finset (Finset α)}
    {pLabel qLabel : Finset α → α → β}
    (hQdisj : ∀ ⦃A B⦄, A ∈ Q → B ∈ Q → A ≠ B → Disjoint A B)
    (hPQ : PartsRRefine P Q rb)
    (hcompat :
      ∀ ⦃A B x y⦄, A ∈ P → B ∈ Q → A ⊆ B →
        x ∈ A → y ∈ A → pLabel A x = pLabel A y →
          qLabel B x = qLabel B y) :
    PartsRRefine (splitPartsByLabel P pLabel)
      (splitPartsByLabel Q qLabel) (rb * Fintype.card β) := by
  classical
  constructor
  · intro F hF
    rcases mem_splitPartsByLabel.mp hF with ⟨hFne, A, hA, b, hFdef⟩
    rcases hPQ.1 hA with ⟨B, hB, hAB⟩
    rcases hFne with ⟨x, hxF⟩
    have hxA : x ∈ A := by
      rw [hFdef] at hxF
      exact (Finset.mem_filter.mp hxF).1
    let G : Finset α := B.filter fun y => qLabel B y = qLabel B x
    have hxG : x ∈ G := by simp [G, hAB hxA]
    have hGmem : G ∈ splitPartsByLabel Q qLabel := by
      rw [mem_splitPartsByLabel]
      exact ⟨⟨x, hxG⟩, B, hB, qLabel B x, rfl⟩
    refine ⟨G, hGmem, ?_⟩
    intro y hyF
    rw [hFdef] at hyF
    have hyA : y ∈ A := (Finset.mem_filter.mp hyF).1
    have hyb : pLabel A y = b := (Finset.mem_filter.mp hyF).2
    have hxb : pLabel A x = b := by
      rw [hFdef] at hxF
      exact (Finset.mem_filter.mp hxF).2
    have hqy : qLabel B y = qLabel B x := by
      exact hcompat hA hB hAB hyA hxA (hyb.trans hxb.symm)
    simp [G, hAB hyA, hqy]
  · intro G hG
    rcases mem_splitPartsByLabel.mp hG with ⟨hGne, B, hB, c, hGdef⟩
    let baseInside : Finset (Finset α) := P.filter fun A => A ⊆ B
    let candidates : Finset (Finset α) :=
      baseInside.biUnion fun A =>
        (Finset.univ : Finset β).image fun b =>
          A.filter fun x => pLabel A x = b
    have hsubset :
        (splitPartsByLabel P pLabel).filter (fun F => F ⊆ G) ⊆ candidates := by
      intro F hF
      have hFmem : F ∈ splitPartsByLabel P pLabel := (Finset.mem_filter.mp hF).1
      have hFG : F ⊆ G := (Finset.mem_filter.mp hF).2
      rcases mem_splitPartsByLabel.mp hFmem with ⟨hFne, A, hA, b, hFdef⟩
      have hAsubB : A ⊆ B := by
        rcases hPQ.1 hA with ⟨B', hB', hAB'⟩
        rcases hFne with ⟨x, hxF⟩
        have hxA : x ∈ A := by
          rw [hFdef] at hxF
          exact (Finset.mem_filter.mp hxF).1
        have hxG : x ∈ G := hFG hxF
        have hxB : x ∈ B := by
          rw [hGdef] at hxG
          exact (Finset.mem_filter.mp hxG).1
        have hxB' : x ∈ B' := hAB' hxA
        have hB'eq : B' = B := by
          by_contra hne
          exact Finset.disjoint_left.mp (hQdisj hB' hB hne) hxB' hxB
        simpa [hB'eq] using hAB'
      have hAbase : A ∈ baseInside := by
        simp [baseInside, hA, hAsubB]
      subst F
      exact Finset.mem_biUnion.mpr
        ⟨A, hAbase, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩
    have hcard_candidates : candidates.card ≤ baseInside.card * Fintype.card β := by
      unfold candidates
      refine Finset.card_biUnion_le_card_mul _ _ _ ?_
      intro A hA
      calc
        ((Finset.univ : Finset β).image fun b =>
            A.filter fun x => pLabel A x = b).card
            ≤ (Finset.univ : Finset β).card := Finset.card_image_le
        _ = Fintype.card β := by simp
    have hbase : baseInside.card ≤ rb := by
      exact hPQ.2 hB
    exact le_trans (Finset.card_le_card hsubset)
      (le_trans hcard_candidates (Nat.mul_le_mul_right _ hbase))

/-- A family of disjoint nonempty parts `2`-refines the family obtained by
merging two of its parts. -/
theorem partsRRefine_self_insert_union_erase {α : Type*} [DecidableEq α]
    {P : Finset (Finset α)} {R S : Finset α}
    (hnonempty : ∀ ⦃A⦄, A ∈ P → A.Nonempty)
    (hdisj : ∀ ⦃A B⦄, A ∈ P → B ∈ P → A ≠ B → Disjoint A B)
    (hR : R ∈ P) (hS : S ∈ P) (_hRS : R ≠ S) :
    PartsRRefine P (insert (R ∪ S) ((P.erase R).erase S)) 2 := by
  classical
  constructor
  · intro A hA
    by_cases hAR : A = R
    · subst A
      refine ⟨R ∪ S, Finset.mem_insert_self _ _, ?_⟩
      intro x hx
      exact Finset.mem_union_left S hx
    · by_cases hAS : A = S
      · subst A
        refine ⟨R ∪ S, Finset.mem_insert_self _ _, ?_⟩
        intro x hx
        exact Finset.mem_union_right R hx
      · refine ⟨A, Finset.mem_insert.mpr ?_, by intro x hx; exact hx⟩
        exact Or.inr (Finset.mem_erase.mpr ⟨hAS, Finset.mem_erase.mpr ⟨hAR, hA⟩⟩)
  · intro B hB
    rcases Finset.mem_insert.mp hB with hBunion | hBold
    · subst B
      have hsubset :
          (P.filter fun A => A ⊆ R ∪ S) ⊆ ({R, S} : Finset (Finset α)) := by
        intro A hAfilter
        have hA : A ∈ P := (Finset.mem_filter.mp hAfilter).1
        have hAsub : A ⊆ R ∪ S := (Finset.mem_filter.mp hAfilter).2
        by_cases hAR : A = R
        · simp [hAR]
        · by_cases hAS : A = S
          · simp [hAS]
          · rcases hnonempty hA with ⟨x, hxA⟩
            have hxUnion : x ∈ R ∪ S := hAsub hxA
            rcases Finset.mem_union.mp hxUnion with hxR | hxS
            · exact False.elim
                (Finset.disjoint_left.mp (hdisj hA hR hAR) hxA hxR)
            · exact False.elim
                (Finset.disjoint_left.mp (hdisj hA hS hAS) hxA hxS)
      calc
        (P.filter fun A => A ⊆ R ∪ S).card
            ≤ ({R, S} : Finset (Finset α)).card := Finset.card_le_card hsubset
        _ ≤ 2 := by
          by_cases h : R = S <;> simp [h]
    · have hBmem : B ∈ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2
      have hBneR : B ≠ R :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).1
      have hBneS : B ≠ S := (Finset.mem_erase.mp hBold).1
      have hsubset :
          (P.filter fun A => A ⊆ B) ⊆ ({B} : Finset (Finset α)) := by
        intro A hAfilter
        have hA : A ∈ P := (Finset.mem_filter.mp hAfilter).1
        have hAsub : A ⊆ B := (Finset.mem_filter.mp hAfilter).2
        by_cases hAB : A = B
        · simp [hAB]
        · rcases hnonempty hA with ⟨x, hxA⟩
          have hxB : x ∈ B := hAsub hxA
          exact False.elim
            (Finset.disjoint_left.mp (hdisj hA hBmem hAB) hxA hxB)
      calc
        (P.filter fun A => A ⊆ B).card
            ≤ ({B} : Finset (Finset α)).card := Finset.card_le_card hsubset
        _ ≤ 2 := by simp

/-- A disjoint nonempty family `r`-refines itself for every positive `r`. -/
theorem partsRRefine_refl_of_partition {α : Type*} [DecidableEq α]
    {P : Finset (Finset α)} {r : ℕ}
    (hnonempty : ∀ ⦃A⦄, A ∈ P → A.Nonempty)
    (hdisj : ∀ ⦃A B⦄, A ∈ P → B ∈ P → A ≠ B → Disjoint A B)
    (hr : 1 ≤ r) :
    PartsRRefine P P r := by
  classical
  constructor
  · intro A hA
    exact ⟨A, hA, by intro x hx; exact hx⟩
  · intro B hB
    have hsubset : (P.filter fun A => A ⊆ B) ⊆ ({B} : Finset (Finset α)) := by
      intro A hAfilter
      have hA : A ∈ P := (Finset.mem_filter.mp hAfilter).1
      have hAB : A ⊆ B := (Finset.mem_filter.mp hAfilter).2
      by_cases h : A = B
      · simp [h]
      · rcases hnonempty hA with ⟨x, hxA⟩
        have hxB : x ∈ B := hAB hxA
        exact False.elim (Finset.disjoint_left.mp (hdisj hA hB h) hxA hxB)
    calc
      (P.filter fun A => A ⊆ B).card ≤ ({B} : Finset (Finset α)).card :=
        Finset.card_le_card hsubset
      _ ≤ r := by simpa using hr

theorem partsRRefine_mono {α : Type*} [DecidableEq α]
    {P Q : Finset (Finset α)} {r s : ℕ}
    (hrs : r ≤ s) (h : PartsRRefine P Q r) :
    PartsRRefine P Q s := by
  constructor
  · exact h.1
  · intro B hB
    exact le_trans (h.2 hB) hrs

theorem rrefines_mono {n m r s : ℕ}
    {P Q : MatrixPartition n m}
    (hrs : r ≤ s) (h : RRefines P Q r) :
    RRefines P Q s := by
  exact ⟨partsRRefine_mono hrs h.1, partsRRefine_mono hrs h.2⟩

/-- If a filter predicate is strictly strengthened inside a finite set, the
filtered cardinality strictly increases. -/
theorem card_filter_lt_card_filter_of_exists {α : Type*} [DecidableEq α]
    {S : Finset α} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hsub : ∀ x, p x → q x)
    (hex : ∃ x ∈ S, q x ∧ ¬ p x) :
    (S.filter p).card < (S.filter q).card := by
  classical
  have hsubset : S.filter p ⊆ S.filter q := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, hsub x (Finset.mem_filter.mp hx).2⟩
  rcases hex with ⟨x, hxS, hxq, hxp⟩
  have hxqmem : x ∈ S.filter q := Finset.mem_filter.mpr ⟨hxS, hxq⟩
  have hxnotpmem : x ∉ S.filter p := by
    intro hx
    exact hxp (Finset.mem_filter.mp hx).2
  have hssub : S.filter p ⊂ S.filter q := by
    refine ⟨hsubset, ?_⟩
    intro hrev
    exact hxnotpmem (hrev hxqmem)
  exact Finset.card_lt_card hssub

/-- Merge two distinct row parts of a matrix partition. -/
noncomputable def rowContract {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (_hRS : R ≠ S) : MatrixPartition n m where
  rowParts := insert (R ∪ S) ((P.rowParts.erase R).erase S)
  row_nonempty := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact (P.row_nonempty hR).mono (by intro x hx; exact Finset.mem_union_left _ hx)
    · exact P.row_nonempty ((Finset.mem_erase.mp (Finset.mem_erase.mp hA).2).2)
  row_disjoint := by
    intro A B hA hB hAB
    rw [Finset.disjoint_left]
    rcases Finset.mem_insert.mp hA with rfl | hAold <;>
      rcases Finset.mem_insert.mp hB with rfl | hBold
    · exact (hAB rfl).elim
    · intro x hx hxB
      rcases Finset.mem_union.mp hx with hxR | hxS
      · exact Finset.disjoint_left.mp
          (P.row_disjoint hR ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2)
            (by intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).1 h.symm))
          hxR hxB
      · exact Finset.disjoint_left.mp
          (P.row_disjoint hS ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2)
            (by intro h; exact (Finset.mem_erase.mp hBold).1 h.symm))
          hxS hxB
    · intro x hxA hx
      rcases Finset.mem_union.mp hx with hxR | hxS
      · exact Finset.disjoint_left.mp
          (P.row_disjoint ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2) hR
            (by intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).1 h))
          hxA hxR
      · exact Finset.disjoint_left.mp
          (P.row_disjoint ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2) hS
            (by intro h; exact (Finset.mem_erase.mp hAold).1 h))
          hxA hxS
    · exact Finset.disjoint_left.mp
        (P.row_disjoint
          ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2)
          ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2) hAB)
  row_cover := by
    intro r
    rcases P.row_cover r with ⟨A, hA, hrA⟩
    by_cases hAR : A = R
    · refine ⟨R ∪ S, Finset.mem_insert_self _ _, ?_⟩
      subst A
      exact Finset.mem_union_left _ hrA
    · by_cases hAS : A = S
      · refine ⟨R ∪ S, Finset.mem_insert_self _ _, ?_⟩
        subst A
        exact Finset.mem_union_right _ hrA
      · refine ⟨A, Finset.mem_insert.mpr (Or.inr ?_), hrA⟩
        exact Finset.mem_erase.mpr ⟨hAS, Finset.mem_erase.mpr ⟨hAR, hA⟩⟩
  colParts := P.colParts
  col_nonempty := P.col_nonempty
  col_disjoint := P.col_disjoint
  col_cover := P.col_cover

/-- Merge two distinct column parts of a matrix partition. -/
noncomputable def colContract {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (_hCD : C ≠ D) : MatrixPartition n m where
  rowParts := P.rowParts
  row_nonempty := P.row_nonempty
  row_disjoint := P.row_disjoint
  row_cover := P.row_cover
  colParts := insert (C ∪ D) ((P.colParts.erase C).erase D)
  col_nonempty := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact (P.col_nonempty hC).mono (by intro x hx; exact Finset.mem_union_left _ hx)
    · exact P.col_nonempty ((Finset.mem_erase.mp (Finset.mem_erase.mp hA).2).2)
  col_disjoint := by
    intro A B hA hB hAB
    rw [Finset.disjoint_left]
    rcases Finset.mem_insert.mp hA with rfl | hAold <;>
      rcases Finset.mem_insert.mp hB with rfl | hBold
    · exact (hAB rfl).elim
    · intro x hx hxB
      rcases Finset.mem_union.mp hx with hxC | hxD
      · exact Finset.disjoint_left.mp
          (P.col_disjoint hC ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2)
            (by intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).1 h.symm))
          hxC hxB
      · exact Finset.disjoint_left.mp
          (P.col_disjoint hD ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2)
            (by intro h; exact (Finset.mem_erase.mp hBold).1 h.symm))
          hxD hxB
    · intro x hxA hx
      rcases Finset.mem_union.mp hx with hxC | hxD
      · exact Finset.disjoint_left.mp
          (P.col_disjoint ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2) hC
            (by intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).1 h))
          hxA hxC
      · exact Finset.disjoint_left.mp
          (P.col_disjoint ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2) hD
            (by intro h; exact (Finset.mem_erase.mp hAold).1 h))
          hxA hxD
    · exact Finset.disjoint_left.mp
        (P.col_disjoint
          ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2)
          ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2) hAB)
  col_cover := by
    intro c
    rcases P.col_cover c with ⟨A, hA, hcA⟩
    by_cases hAC : A = C
    · refine ⟨C ∪ D, Finset.mem_insert_self _ _, ?_⟩
      subst A
      exact Finset.mem_union_left _ hcA
    · by_cases hAD : A = D
      · refine ⟨C ∪ D, Finset.mem_insert_self _ _, ?_⟩
        subst A
        exact Finset.mem_union_right _ hcA
      · refine ⟨A, Finset.mem_insert.mpr (Or.inr ?_), hcA⟩
        exact Finset.mem_erase.mpr ⟨hAD, Finset.mem_erase.mpr ⟨hAC, hA⟩⟩

@[simp] theorem rowParts_rowContract {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    (P.rowContract hR hS hRS).rowParts =
      insert (R ∪ S) ((P.rowParts.erase R).erase S) :=
  rfl

@[simp] theorem colParts_colContract {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    (P.colContract hC hD hCD).colParts =
      insert (C ∪ D) ((P.colParts.erase C).erase D) :=
  rfl

@[simp] theorem colParts_rowContract {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    (P.rowContract hR hS hRS).colParts = P.colParts :=
  rfl

@[simp] theorem rowParts_colContract {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    (P.colContract hC hD hCD).rowParts = P.rowParts :=
  rfl

/-- A partition `2`-refines the result of one row contraction. -/
theorem rrefines_rowContract_self {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    RRefines P (P.rowContract hR hS hRS) 2 := by
  constructor
  · simpa [rowParts_rowContract] using
      partsRRefine_self_insert_union_erase
        P.row_nonempty P.row_disjoint hR hS hRS
  · simpa [colParts_rowContract] using
      partsRRefine_refl_of_partition
        P.col_nonempty P.col_disjoint (by decide : 1 ≤ 2)

/-- A partition `2`-refines the result of one column contraction. -/
theorem rrefines_colContract_self {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    RRefines P (P.colContract hC hD hCD) 2 := by
  constructor
  · simpa [rowParts_colContract] using
      partsRRefine_refl_of_partition
        P.row_nonempty P.row_disjoint (by decide : 1 ≤ 2)
  · simpa [colParts_colContract] using
      partsRRefine_self_insert_union_erase
        P.col_nonempty P.col_disjoint hC hD hCD

theorem isRowContraction_rowContract {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    IsRowContraction P (P.rowContract hR hS hRS) := by
  exact ⟨R, hR, S, hS, hRS, rfl, rfl⟩

theorem isColContraction_colContract {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    IsColContraction P (P.colContract hC hD hCD) := by
  exact ⟨C, hC, D, hD, hCD, rfl, rfl⟩

theorem rowParts_card_rowContract_lt {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    (P.rowContract hR hS hRS).rowParts.card < P.rowParts.card := by
  classical
  have hS_erase : S ∈ P.rowParts.erase R := Finset.mem_erase.mpr ⟨hRS.symm, hS⟩
  calc
    (P.rowContract hR hS hRS).rowParts.card
        ≤ ((P.rowParts.erase R).erase S).card + 1 := by
          simp [rowContract, Finset.card_insert_le]
    _ = (P.rowParts.erase R).card := by
          exact Finset.card_erase_add_one hS_erase
    _ < P.rowParts.card := Finset.card_erase_lt_of_mem hR

theorem colParts_card_colContract_lt {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    (P.colContract hC hD hCD).colParts.card < P.colParts.card := by
  classical
  have hD_erase : D ∈ P.colParts.erase C := Finset.mem_erase.mpr ⟨hCD.symm, hD⟩
  calc
    (P.colContract hC hD hCD).colParts.card
        ≤ ((P.colParts.erase C).erase D).card + 1 := by
          simp [colContract, Finset.card_insert_le]
    _ = (P.colParts.erase C).card := by
          exact Finset.card_erase_add_one hD_erase
    _ < P.colParts.card := Finset.card_erase_lt_of_mem hC

/-- The partition into singleton rows and singleton columns. -/
noncomputable def singleton (n m : ℕ) : MatrixPartition n m where
  rowParts := (Finset.univ : Finset (Fin n)).map ⟨fun r => ({r} : Finset (Fin n)), by
    intro a b h
    simpa using h⟩
  row_nonempty := by
    intro R hR
    rcases Finset.mem_map.mp hR with ⟨r, _hr, rfl⟩
    exact ⟨r, by simp⟩
  row_disjoint := by
    intro R S hR hS hRS
    rcases Finset.mem_map.mp hR with ⟨r, _hr, rfl⟩
    rcases Finset.mem_map.mp hS with ⟨s, _hs, rfl⟩
    rw [Finset.disjoint_left]
    intro x hx hy
    simp at hx hy
    subst r
    subst s
    exact hRS rfl
  row_cover := by
    intro r
    exact ⟨{r}, by simp, by simp⟩
  colParts := (Finset.univ : Finset (Fin m)).map ⟨fun c => ({c} : Finset (Fin m)), by
    intro a b h
    simpa using h⟩
  col_nonempty := by
    intro C hC
    rcases Finset.mem_map.mp hC with ⟨c, _hc, rfl⟩
    exact ⟨c, by simp⟩
  col_disjoint := by
    intro C D hC hD hCD
    rcases Finset.mem_map.mp hC with ⟨c, _hc, rfl⟩
    rcases Finset.mem_map.mp hD with ⟨d, _hd, rfl⟩
    rw [Finset.disjoint_left]
    intro x hx hy
    simp at hx hy
    subst c
    subst d
    exact hCD rfl
  col_cover := by
    intro c
    exact ⟨{c}, by simp, by simp⟩

@[simp] theorem rowParts_singleton (n m : ℕ) :
    (singleton n m).rowParts =
      (Finset.univ : Finset (Fin n)).map ⟨fun r => ({r} : Finset (Fin n)), by
        intro a b h
        simpa using h⟩ :=
  rfl

@[simp] theorem colParts_singleton (n m : ℕ) :
    (singleton n m).colParts =
      (Finset.univ : Finset (Fin m)).map ⟨fun c => ({c} : Finset (Fin m)), by
        intro a b h
        simpa using h⟩ :=
  rfl

/-- The singleton partition is finest. -/
theorem singleton_isFinest (n m : ℕ) :
    IsFinest (singleton n m) := by
  constructor
  · intro R hR
    rcases Finset.mem_map.mp hR with ⟨r, _hr, rfl⟩
    exact ⟨r, rfl⟩
  constructor
  · intro r
    simp [singleton]
  constructor
  · intro C hC
    rcases Finset.mem_map.mp hC with ⟨c, _hc, rfl⟩
    exact ⟨c, rfl⟩
  · intro c
    simp [singleton]

/-- A partition of a matrix with no rows has no row parts. -/
theorem rowParts_eq_empty_of_zero_rows {m : ℕ} (P : MatrixPartition 0 m) :
    P.rowParts = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro R hR
  rcases P.row_nonempty hR with ⟨r, _hr⟩
  exact Fin.elim0 r

/-- A partition of a matrix with no columns has no column parts. -/
theorem colParts_eq_empty_of_zero_cols {n : ℕ} (P : MatrixPartition n 0) :
    P.colParts = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  rcases P.col_nonempty hC with ⟨c, _hc⟩
  exact Fin.elim0 c

/-- Every partition of a matrix with no rows has error value zero. -/
theorem errorValueAtMost_zeroRows {m d : ℕ}
    (M : _root_.Matrix (Fin 0) (Fin m) α) (P : MatrixPartition 0 m) :
    ErrorValueAtMost M P d := by
  constructor
  · intro R hR
    rcases P.row_nonempty hR with ⟨r, _hr⟩
    exact Fin.elim0 r
  · intro C hC
    have hrows := rowParts_eq_empty_of_zero_rows P
    simp [colErrorSet, hrows]

/-- Every partition of a matrix with no columns has error value zero. -/
theorem errorValueAtMost_zeroCols {n d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin 0) α) (P : MatrixPartition n 0) :
    ErrorValueAtMost M P d := by
  constructor
  · intro R hR
    have hcols := colParts_eq_empty_of_zero_cols P
    simp [rowErrorSet, hcols]
  · intro C hC
    rcases P.col_nonempty hC with ⟨c, _hc⟩
    exact Fin.elim0 c

/-- Error-value bounds are monotone in the numerical bound. -/
theorem errorValueAtMost_mono {n m d e : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P : MatrixPartition n m}
    (hde : d ≤ e) (hP : ErrorValueAtMost M P d) :
    ErrorValueAtMost M P e := by
  constructor
  · intro R hR
    exact le_trans (hP.1 hR) hde
  · intro C hC
    exact le_trans (hP.2 hC) hde

/-- A nonempty partition refining a finest partition is itself finest. -/
theorem isFinest_of_refines_isFinest {n m : ℕ}
    {P Q : MatrixPartition n m}
    (href : Refines P Q) (hQ : IsFinest Q) :
    IsFinest P := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    rcases href.1 hR with ⟨B, hB, hRB⟩
    rcases hQ.1 hB with ⟨r, rfl⟩
    rcases P.row_nonempty hR with ⟨x, hxR⟩
    have hxr : x = r := by simpa using hRB hxR
    subst x
    refine ⟨r, ?_⟩
    apply Finset.Subset.antisymm hRB
    intro y hy
    simp at hy
    simpa [hy] using hxR
  · intro r
    rcases P.row_cover r with ⟨R, hR, hrR⟩
    rcases href.1 hR with ⟨B, hB, hRB⟩
    rcases hQ.1 hB with ⟨s, hs⟩
    have hrs : r = s := by
      have hrB : r ∈ B := hRB hrR
      simpa [hs] using hrB
    have hRsingle : R = ({r} : Finset (Fin n)) := by
      apply Finset.Subset.antisymm
      · intro y hy
        have hyB : y ∈ B := hRB hy
        simpa [hs, hrs] using hyB
      · intro y hy
        simp at hy
        simpa [hy] using hrR
    simpa [hRsingle] using hR
  · intro C hC
    rcases href.2 hC with ⟨D, hD, hCD⟩
    rcases hQ.2.2.1 hD with ⟨c, rfl⟩
    rcases P.col_nonempty hC with ⟨x, hxC⟩
    have hxc : x = c := by simpa using hCD hxC
    subst x
    refine ⟨c, ?_⟩
    apply Finset.Subset.antisymm hCD
    intro y hy
    simp at hy
    simpa [hy] using hxC
  · intro c
    rcases P.col_cover c with ⟨C, hC, hcC⟩
    rcases href.2 hC with ⟨D, hD, hCD⟩
    rcases hQ.2.2.1 hD with ⟨t, ht⟩
    have hct : c = t := by
      have hcD : c ∈ D := hCD hcC
      simpa [ht] using hcD
    have hCsingle : C = ({c} : Finset (Fin m)) := by
      apply Finset.Subset.antisymm
      · intro y hy
        have hyD : y ∈ D := hCD hy
        simpa [ht, hct] using hyD
      · intro y hy
        simp at hy
        simpa [hy] using hcC
    simpa [hCsingle] using hC

end MatrixPartition

/-- A contraction tail from a prescribed matrix partition to a coarsest
partition. -/
structure MatrixContractionTail {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ)
    (P₀ : MatrixPartition n m) where
  /-- Number of remaining contractions. -/
  stepCount : ℕ
  /-- Partition at each time. -/
  partition : ℕ → MatrixPartition n m
  /-- The first partition is the prescribed one. -/
  starts : partition 0 = P₀
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Consecutive partitions are contractions. -/
  step_contracts :
    ∀ i, i < stepCount → MatrixPartition.IsContraction (partition i) (partition (i + 1))
  /-- Every partition in the tail has bounded error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

namespace MatrixContractionTail

/-- Prepend one matrix-partition contraction to a contraction tail. -/
noncomputable def cons {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P Q : MatrixPartition n m}
    (hPQ : MatrixPartition.IsContraction P Q)
    (hP : ErrorValueAtMost M P d)
    (S : MatrixContractionTail M d Q) :
    MatrixContractionTail M d P where
  stepCount := S.stepCount + 1
  partition := fun i =>
    match i with
    | 0 => P
    | j + 1 => S.partition j
  starts := rfl
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
        simpa using hP
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.errorValue_le j hj

/-- Relax the numerical error bound on a contraction tail. -/
noncomputable def mono {n m d e : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P : MatrixPartition n m}
    (hde : d ≤ e) (S : MatrixContractionTail M d P) :
    MatrixContractionTail M e P where
  stepCount := S.stepCount
  partition := S.partition
  starts := S.starts
  ends := S.ends
  step_contracts := S.step_contracts
  errorValue_le := by
    intro i hi
    exact MatrixPartition.errorValueAtMost_mono hde (S.errorValue_le i hi)

end MatrixContractionTail

/-- From any partition of a matrix with no rows, repeatedly contract column
parts until the partition is coarsest.  All intermediate error values are zero. -/
theorem exists_matrixContractionTail_zeroRows {m d : ℕ}
    (M : _root_.Matrix (Fin 0) (Fin m) α) :
    ∀ P : MatrixPartition 0 m, Nonempty (MatrixContractionTail M d P) := by
  classical
  intro P
  refine WellFounded.induction
    (C := fun P : MatrixPartition 0 m => Nonempty (MatrixContractionTail M d P))
    (InvImage.wf (fun P : MatrixPartition 0 m => P.colParts.card) <| (Nat.lt_wfRel).2)
    P ?_
  intro P ih
  by_cases hcol : P.colParts.card ≤ 1
  · have hrow : P.rowParts.card ≤ 1 := by
      rw [MatrixPartition.rowParts_eq_empty_of_zero_rows P]
      simp
    exact ⟨{
      stepCount := 0
      partition := fun _ => P
      starts := rfl
      ends := ⟨hrow, hcol⟩
      step_contracts := by intro i hi; omega
      errorValue_le := by
        intro i hi
        exact MatrixPartition.errorValueAtMost_zeroRows M P
    }⟩
  · have hgt : 1 < P.colParts.card := Nat.lt_of_not_ge hcol
    rcases Finset.one_lt_card.mp hgt with ⟨C, hC, D, hD, hCD⟩
    let Q : MatrixPartition 0 m := P.colContract hC hD hCD
    have hlt : Q.colParts.card < P.colParts.card :=
      MatrixPartition.colParts_card_colContract_lt P hC hD hCD
    rcases ih Q hlt with ⟨S⟩
    exact ⟨MatrixContractionTail.cons
      (Or.inr (MatrixPartition.isColContraction_colContract P hC hD hCD))
      (MatrixPartition.errorValueAtMost_zeroRows M P) S⟩

/-- From any partition of a matrix with no columns, repeatedly contract row
parts until the partition is coarsest.  All intermediate error values are zero. -/
theorem exists_matrixContractionTail_zeroCols {n d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin 0) α) :
    ∀ P : MatrixPartition n 0, Nonempty (MatrixContractionTail M d P) := by
  classical
  intro P
  refine WellFounded.induction
    (C := fun P : MatrixPartition n 0 => Nonempty (MatrixContractionTail M d P))
    (InvImage.wf (fun P : MatrixPartition n 0 => P.rowParts.card) <| (Nat.lt_wfRel).2)
    P ?_
  intro P ih
  by_cases hrow : P.rowParts.card ≤ 1
  · have hcol : P.colParts.card ≤ 1 := by
      rw [MatrixPartition.colParts_eq_empty_of_zero_cols P]
      simp
    exact ⟨{
      stepCount := 0
      partition := fun _ => P
      starts := rfl
      ends := ⟨hrow, hcol⟩
      step_contracts := by intro i hi; omega
      errorValue_le := by
        intro i hi
        exact MatrixPartition.errorValueAtMost_zeroCols M P
    }⟩
  · have hgt : 1 < P.rowParts.card := Nat.lt_of_not_ge hrow
    rcases Finset.one_lt_card.mp hgt with ⟨R, hR, S, hS, hRS⟩
    let Q : MatrixPartition n 0 := P.rowContract hR hS hRS
    have hlt : Q.rowParts.card < P.rowParts.card :=
      MatrixPartition.rowParts_card_rowContract_lt P hR hS hRS
    rcases ih Q hlt with ⟨T⟩
    exact ⟨MatrixContractionTail.cons
      (Or.inl (MatrixPartition.isRowContraction_rowContract P hR hS hRS))
      (MatrixPartition.errorValueAtMost_zeroCols M P) T⟩

/-- Matrices with no rows have matrix twin-width at most every bound. -/
theorem matrixTwinWidthAtMost_zeroRows {m d : ℕ}
    (M : _root_.Matrix (Fin 0) (Fin m) α) :
    MatrixTwinWidthAtMost M d := by
  rcases exists_matrixContractionTail_zeroRows (d := d) M
      (MatrixPartition.singleton 0 m) with ⟨S⟩
  exact ⟨{
    stepCount := S.stepCount
    partition := S.partition
    starts := by
      rw [S.starts]
      exact MatrixPartition.singleton_isFinest 0 m
    ends := S.ends
    step_contracts := S.step_contracts
    errorValue_le := S.errorValue_le
  }⟩

/-- Matrices with no columns have matrix twin-width at most every bound. -/
theorem matrixTwinWidthAtMost_zeroCols {n d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin 0) α) :
    MatrixTwinWidthAtMost M d := by
  rcases exists_matrixContractionTail_zeroCols (d := d) M
      (MatrixPartition.singleton n 0) with ⟨S⟩
  exact ⟨{
    stepCount := S.stepCount
    partition := S.partition
    starts := by
      rw [S.starts]
      exact MatrixPartition.singleton_isFinest n 0
    ends := S.ends
    step_contracts := S.step_contracts
    errorValue_le := S.errorValue_le
  }⟩

namespace MatrixPartition

/-- Matrix partitions are equal when their row and column part families are
equal.  The remaining fields are propositions. -/
theorem ext_parts {n m : ℕ} {P Q : MatrixPartition n m}
    (hrow : P.rowParts = Q.rowParts) (hcol : P.colParts = Q.colParts) :
    P = Q := by
  cases P
  cases Q
  simp at hrow hcol
  subst hrow
  subst hcol
  rfl

/-- If a row partition properly refines another row partition, two fine row
parts lie in one coarse row part. -/
theorem exists_two_rowParts_subset_of_refines_ne {n m : ℕ}
    {P Q : MatrixPartition n m}
    (href : PartsRefine P.rowParts Q.rowParts)
    (hne : P.rowParts ≠ Q.rowParts) :
    ∃ B ∈ Q.rowParts, ∃ R ∈ P.rowParts, ∃ S ∈ P.rowParts,
      R ≠ S ∧ R ⊆ B ∧ S ⊆ B := by
  classical
  by_contra hno
  have huniq :
      ∀ ⦃B R S⦄, B ∈ Q.rowParts → R ∈ P.rowParts → S ∈ P.rowParts →
        R ⊆ B → S ⊆ B → R = S := by
    intro B R S hB hR hS hRB hSB
    by_contra hRS
    exact hno ⟨B, hB, R, hR, S, hS, hRS, hRB, hSB⟩
  have hcoarse_subset :
      ∀ ⦃A B⦄, A ∈ P.rowParts → B ∈ Q.rowParts → A ⊆ B → B ⊆ A := by
    intro A B hA hB hAB x hxB
    rcases P.row_cover x with ⟨A', hA', hxA'⟩
    rcases href hA' with ⟨B', hB', hA'B'⟩
    have hxB' : x ∈ B' := hA'B' hxA'
    have hB'eq : B' = B := by
      by_contra hneB
      exact Finset.disjoint_left.mp (Q.row_disjoint hB' hB hneB) hxB' hxB
    have hA'eq : A' = A :=
      huniq hB hA' hA (by simpa [hB'eq] using hA'B') hAB
    simpa [hA'eq] using hxA'
  have hPsubsetQ : P.rowParts ⊆ Q.rowParts := by
    intro A hA
    rcases href hA with ⟨B, hB, hAB⟩
    have hBA : B ⊆ A := hcoarse_subset hA hB hAB
    have hAeqB : A = B := Finset.Subset.antisymm hAB hBA
    simpa [hAeqB] using hB
  have hQsubsetP : Q.rowParts ⊆ P.rowParts := by
    intro B hB
    rcases Q.row_nonempty hB with ⟨x, hxB⟩
    rcases P.row_cover x with ⟨A, hA, hxA⟩
    rcases href hA with ⟨B', hB', hAB'⟩
    have hxB' : x ∈ B' := hAB' hxA
    have hB'eq : B' = B := by
      by_contra hneB
      exact Finset.disjoint_left.mp (Q.row_disjoint hB' hB hneB) hxB' hxB
    have hAB : A ⊆ B := by simpa [hB'eq] using hAB'
    have hBA : B ⊆ A := hcoarse_subset hA hB hAB
    have hBeqA : B = A := Finset.Subset.antisymm hBA hAB
    simpa [hBeqA] using hA
  exact hne (Finset.Subset.antisymm hPsubsetQ hQsubsetP)

/-- Column-side analogue of
`exists_two_rowParts_subset_of_refines_ne`. -/
theorem exists_two_colParts_subset_of_refines_ne {n m : ℕ}
    {P Q : MatrixPartition n m}
    (href : PartsRefine P.colParts Q.colParts)
    (hne : P.colParts ≠ Q.colParts) :
    ∃ B ∈ Q.colParts, ∃ C ∈ P.colParts, ∃ D ∈ P.colParts,
      C ≠ D ∧ C ⊆ B ∧ D ⊆ B := by
  classical
  by_contra hno
  have huniq :
      ∀ ⦃B C D⦄, B ∈ Q.colParts → C ∈ P.colParts → D ∈ P.colParts →
        C ⊆ B → D ⊆ B → C = D := by
    intro B C D hB hC hD hCB hDB
    by_contra hCD
    exact hno ⟨B, hB, C, hC, D, hD, hCD, hCB, hDB⟩
  have hcoarse_subset :
      ∀ ⦃A B⦄, A ∈ P.colParts → B ∈ Q.colParts → A ⊆ B → B ⊆ A := by
    intro A B hA hB hAB x hxB
    rcases P.col_cover x with ⟨A', hA', hxA'⟩
    rcases href hA' with ⟨B', hB', hA'B'⟩
    have hxB' : x ∈ B' := hA'B' hxA'
    have hB'eq : B' = B := by
      by_contra hneB
      exact Finset.disjoint_left.mp (Q.col_disjoint hB' hB hneB) hxB' hxB
    have hA'eq : A' = A :=
      huniq hB hA' hA (by simpa [hB'eq] using hA'B') hAB
    simpa [hA'eq] using hxA'
  have hPsubsetQ : P.colParts ⊆ Q.colParts := by
    intro A hA
    rcases href hA with ⟨B, hB, hAB⟩
    have hBA : B ⊆ A := hcoarse_subset hA hB hAB
    have hAeqB : A = B := Finset.Subset.antisymm hAB hBA
    simpa [hAeqB] using hB
  have hQsubsetP : Q.colParts ⊆ P.colParts := by
    intro B hB
    rcases Q.col_nonempty hB with ⟨x, hxB⟩
    rcases P.col_cover x with ⟨A, hA, hxA⟩
    rcases href hA with ⟨B', hB', hAB'⟩
    have hxB' : x ∈ B' := hAB' hxA
    have hB'eq : B' = B := by
      by_contra hneB
      exact Finset.disjoint_left.mp (Q.col_disjoint hB' hB hneB) hxB' hxB
    have hAB : A ⊆ B := by simpa [hB'eq] using hAB'
    have hBA : B ⊆ A := hcoarse_subset hA hB hAB
    have hBeqA : B = A := Finset.Subset.antisymm hBA hAB
    simpa [hBeqA] using hA
  exact hne (Finset.Subset.antisymm hPsubsetQ hQsubsetP)

/-- Merging two parts that lie in one coarse part preserves bounded
refinement of a finite family of parts. -/
theorem partsRRefine_contract {α : Type*} [DecidableEq α]
    {P Q : Finset (Finset α)} {R S : Finset α} {r : ℕ}
    (hPQ : PartsRRefine P Q r)
    (hR : R ∈ P) (_hS : S ∈ P) (_hRS : R ≠ S)
    (hsame : ∃ B ∈ Q, R ⊆ B ∧ S ⊆ B) :
    PartsRRefine (insert (R ∪ S) ((P.erase R).erase S)) Q r := by
  classical
  constructor
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hAold
    · rcases hsame with ⟨B, hB, hRB, hSB⟩
      exact ⟨B, hB, by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hRB hx
        · exact hSB hx⟩
    · have hAP : A ∈ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2
      exact hPQ.1 hAP
  · intro B hB
    let Pnew : Finset (Finset α) := insert (R ∪ S) ((P.erase R).erase S)
    let f : Finset α → Finset α := fun A => if A = R ∪ S then R else A
    have hmap :
        ∀ A ∈ Pnew.filter fun A => A ⊆ B, f A ∈ P.filter fun A => A ⊆ B := by
      intro A hA
      have hAdata : A ∈ Pnew ∧ A ⊆ B := by
        simpa [Pnew] using hA
      by_cases hAunion : A = R ∪ S
      · subst A
        have hRsub : R ⊆ B := by
          intro x hx
          exact hAdata.2 (Finset.mem_union_left S hx)
        simp [f, hR, hRsub]
      · have hAold : A ∈ (P.erase R).erase S := by
          rcases Finset.mem_insert.mp hAdata.1 with h | h
          · exact False.elim (hAunion h)
          · exact h
        have hAP : A ∈ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2
        simp [f, hAunion, hAP, hAdata.2]
    have hinj :
        Set.InjOn f (Pnew.filter fun A => A ⊆ B) := by
      intro A hA C hC hAC
      have hAdata : A ∈ Pnew ∧ A ⊆ B := by
        simpa [Pnew] using hA
      have hCdata : C ∈ Pnew ∧ C ⊆ B := by
        simpa [Pnew] using hC
      by_cases hAunion : A = R ∪ S
      · by_cases hCunion : C = R ∪ S
        · exact hAunion.trans hCunion.symm
        · have hCold : C ∈ (P.erase R).erase S := by
            rcases Finset.mem_insert.mp hCdata.1 with h | h
            · exact False.elim (hCunion h)
            · exact h
          have hCneR : C ≠ R :=
            (Finset.mem_erase.mp (Finset.mem_erase.mp hCold).2).1
          have hCR : C = R := by
            simpa [f, hAunion, hCunion] using hAC.symm
          exact False.elim (hCneR hCR)
      · by_cases hCunion : C = R ∪ S
        · have hAold : A ∈ (P.erase R).erase S := by
            rcases Finset.mem_insert.mp hAdata.1 with h | h
            · exact False.elim (hAunion h)
            · exact h
          have hAneR : A ≠ R :=
            (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).1
          have hAR : A = R := by
            simpa [f, hAunion, hCunion] using hAC
          exact False.elim (hAneR hAR)
        · simpa [f, hAunion, hCunion] using hAC
    exact le_trans
      (Finset.card_le_card_of_injOn f hmap hinj)
      (hPQ.2 hB)

/-- Row contractions inside one coarse row part preserve bounded refinement. -/
theorem rrefines_rowContract {n m r : ℕ}
    {P Q : MatrixPartition n m}
    {R S : Finset (Fin n)}
    (hPQ : RRefines P Q r)
    (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts) (hRS : R ≠ S)
    (hsame : ∃ B ∈ Q.rowParts, R ⊆ B ∧ S ⊆ B) :
    RRefines (P.rowContract hR hS hRS) Q r := by
  constructor
  · simpa [rowParts_rowContract] using
      partsRRefine_contract hPQ.1 hR hS hRS hsame
  · simpa [colParts_rowContract] using hPQ.2

/-- Column contractions inside one coarse column part preserve bounded
refinement. -/
theorem rrefines_colContract {n m r : ℕ}
    {P Q : MatrixPartition n m}
    {C D : Finset (Fin m)}
    (hPQ : RRefines P Q r)
    (hC : C ∈ P.colParts) (hD : D ∈ P.colParts) (hCD : C ≠ D)
    (hsame : ∃ B ∈ Q.colParts, C ⊆ B ∧ D ⊆ B) :
    RRefines (P.colContract hC hD hCD) Q r := by
  constructor
  · simpa [rowParts_colContract] using hPQ.1
  · simpa [colParts_colContract] using
      partsRRefine_contract hPQ.2 hC hD hCD hsame

/-- Error values pull back across bounded refinements, with the expected
multiplicative loss. -/
theorem errorValueAtMost_of_rrefines {n m r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P Q : MatrixPartition n m}
    (hPQ : MatrixPartition.RRefines P Q r)
    (hQ : ErrorValueAtMost M Q t) :
    ErrorValueAtMost M P (r * t) := by
  classical
  constructor
  · intro R hR
    rcases hPQ.1.1 hR with ⟨RQ, hRQ, hRsub⟩
    let badQ : Finset (Finset (Fin m)) := rowErrorSet M Q RQ
    let overBad : Finset (Finset (Fin m)) :=
      badQ.biUnion fun CQ => P.colParts.filter fun C => C ⊆ CQ
    have hsubset :
        rowErrorSet M P R ⊆ overBad := by
      intro C hC
      have hCdata : C ∈ P.colParts ∧ ¬ ZoneConstant M R C := by
        simpa [rowErrorSet] using hC
      have hCparts : C ∈ P.colParts := by
        exact hCdata.1
      have hCnon : ¬ ZoneConstant M R C := by
        exact hCdata.2
      rcases hPQ.2.1 hCparts with ⟨CQ, hCQ, hCsub⟩
      have hCQbad : CQ ∈ badQ := by
        simp [badQ, rowErrorSet, hCQ]
        intro hconst
        exact hCnon (by
          intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
          exact hconst (hRsub hr₁) (hRsub hr₂) (hCsub hc₁) (hCsub hc₂))
      exact Finset.mem_biUnion.mpr ⟨CQ, hCQbad, by simp [hCparts, hCsub]⟩
    have hcard_over :
        overBad.card ≤ badQ.card * r := by
      unfold overBad
      exact Finset.card_biUnion_le_card_mul _ _ _ (by
        intro CQ hCQ
        have hCQdata : CQ ∈ Q.colParts ∧ ¬ ZoneConstant M RQ CQ := by
          simpa [badQ, rowErrorSet] using hCQ
        have hCQparts : CQ ∈ Q.colParts := by
          exact hCQdata.1
        exact hPQ.2.2 hCQparts)
    calc
      (rowErrorSet M P R).card ≤ overBad.card := Finset.card_le_card hsubset
      _ ≤ badQ.card * r := hcard_over
      _ ≤ t * r := Nat.mul_le_mul_right r (hQ.1 hRQ)
      _ = r * t := Nat.mul_comm t r
  · intro C hC
    rcases hPQ.2.1 hC with ⟨CQ, hCQ, hCsub⟩
    let badQ : Finset (Finset (Fin n)) := colErrorSet M Q CQ
    let overBad : Finset (Finset (Fin n)) :=
      badQ.biUnion fun RQ => P.rowParts.filter fun R => R ⊆ RQ
    have hsubset :
        colErrorSet M P C ⊆ overBad := by
      intro R hR
      have hRdata : R ∈ P.rowParts ∧ ¬ ZoneConstant M R C := by
        simpa [colErrorSet] using hR
      have hRparts : R ∈ P.rowParts := by
        exact hRdata.1
      have hRnon : ¬ ZoneConstant M R C := by
        exact hRdata.2
      rcases hPQ.1.1 hRparts with ⟨RQ, hRQ, hRsub⟩
      have hRQbad : RQ ∈ badQ := by
        simp [badQ, colErrorSet, hRQ]
        intro hconst
        exact hRnon (by
          intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
          exact hconst (hRsub hr₁) (hRsub hr₂) (hCsub hc₁) (hCsub hc₂))
      exact Finset.mem_biUnion.mpr ⟨RQ, hRQbad, by simp [hRparts, hRsub]⟩
    have hcard_over :
        overBad.card ≤ badQ.card * r := by
      unfold overBad
      exact Finset.card_biUnion_le_card_mul _ _ _ (by
        intro RQ hRQ
        have hRQdata : RQ ∈ Q.rowParts ∧ ¬ ZoneConstant M RQ CQ := by
          simpa [badQ, colErrorSet] using hRQ
        have hRQparts : RQ ∈ Q.rowParts := by
          exact hRQdata.1
        exact hPQ.1.2 hRQparts)
    calc
      (colErrorSet M P C).card ≤ overBad.card := Finset.card_le_card hsubset
      _ ≤ badQ.card * r := hcard_over
      _ ≤ t * r := Nat.mul_le_mul_right r (hQ.2 hCQ)
      _ = r * t := Nat.mul_comm t r

end MatrixPartition

namespace MatrixContractionPath

/-- The empty contraction path at a partition whose error is already bounded. -/
def nil {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P : MatrixPartition n m}
    (hP : ErrorValueAtMost M P d) :
    MatrixContractionPath M d P P where
  stepCount := 0
  partition := fun _ => P
  starts := rfl
  ends := rfl
  step_contracts := by intro i hi; omega
  errorValue_le := by intro i hi; simpa using hP

/-- Prepend one contraction to a contraction path. -/
noncomputable def cons {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P Q R : MatrixPartition n m}
    (hPQ : MatrixPartition.IsContraction P Q)
    (hP : ErrorValueAtMost M P d)
    (S : MatrixContractionPath M d Q R) :
    MatrixContractionPath M d P R where
  stepCount := S.stepCount + 1
  partition := fun i =>
    match i with
    | 0 => P
    | j + 1 => S.partition j
  starts := rfl
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
        simpa using hP
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.errorValue_le j hj

end MatrixContractionPath

namespace MatrixContractionTail

/-- Expand one bounded-refinement step into ordinary contractions before an
already constructed contraction tail from the coarse partition.

The proof repeatedly merges two fine row or column parts lying in the same
coarse part.  Bounded refinement is preserved at every merge, so the pulled
back error bound remains `r * t`. -/
theorem exists_of_rrefines {n m r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α} :
    ∀ (P Q : MatrixPartition n m),
      MatrixPartition.RRefines P Q r →
      ErrorValueAtMost M Q t →
      MatrixContractionTail M (r * t) Q →
      Nonempty (MatrixContractionTail M (r * t) P) := by
  classical
  intro P
  refine WellFounded.induction
    (C := fun P : MatrixPartition n m =>
      ∀ Q : MatrixPartition n m,
        MatrixPartition.RRefines P Q r →
        ErrorValueAtMost M Q t →
        MatrixContractionTail M (r * t) Q →
        Nonempty (MatrixContractionTail M (r * t) P))
    (InvImage.wf
      (fun P : MatrixPartition n m => P.rowParts.card + P.colParts.card)
      <| (Nat.lt_wfRel).2)
    P ?_
  intro P ih Q hPQ hQ T
  have hPerr : ErrorValueAtMost M P (r * t) :=
    MatrixPartition.errorValueAtMost_of_rrefines hPQ hQ
  by_cases hrow : P.rowParts = Q.rowParts
  · by_cases hcol : P.colParts = Q.colParts
    · have hPQeq : P = Q := MatrixPartition.ext_parts hrow hcol
      subst Q
      exact ⟨T⟩
    · rcases MatrixPartition.exists_two_colParts_subset_of_refines_ne
        hPQ.2.1 hcol with
        ⟨B, hB, C, hC, D, hD, hCD, hCB, hDB⟩
      let P' : MatrixPartition n m := P.colContract hC hD hCD
      have hP'Q : MatrixPartition.RRefines P' Q r :=
        MatrixPartition.rrefines_colContract hPQ hC hD hCD ⟨B, hB, hCB, hDB⟩
      have hlt :
          P'.rowParts.card + P'.colParts.card <
            P.rowParts.card + P.colParts.card := by
        have hcollt := MatrixPartition.colParts_card_colContract_lt P hC hD hCD
        have hroweq : P'.rowParts.card = P.rowParts.card := by
          simp [P']
        have hcoleq : P'.colParts.card = (P.colContract hC hD hCD).colParts.card := rfl
        rw [hroweq, hcoleq]
        omega
      rcases ih P' hlt Q hP'Q hQ T with ⟨T'⟩
      exact ⟨MatrixContractionTail.cons
        (Or.inr (MatrixPartition.isColContraction_colContract P hC hD hCD))
        hPerr T'⟩
  · rcases MatrixPartition.exists_two_rowParts_subset_of_refines_ne
      hPQ.1.1 hrow with
      ⟨B, hB, R, hR, S, hS, hRS, hRB, hSB⟩
    let P' : MatrixPartition n m := P.rowContract hR hS hRS
    have hP'Q : MatrixPartition.RRefines P' Q r :=
      MatrixPartition.rrefines_rowContract hPQ hR hS hRS ⟨B, hB, hRB, hSB⟩
    have hlt :
        P'.rowParts.card + P'.colParts.card <
          P.rowParts.card + P.colParts.card := by
      have hrowlt := MatrixPartition.rowParts_card_rowContract_lt P hR hS hRS
      have hroweq : P'.rowParts.card = (P.rowContract hR hS hRS).rowParts.card := rfl
      have hcoleq : P'.colParts.card = P.colParts.card := by
        simp [P']
      rw [hroweq, hcoleq]
      omega
    rcases ih P' hlt Q hP'Q hQ T with ⟨T'⟩
    exact ⟨MatrixContractionTail.cons
      (Or.inl (MatrixPartition.isRowContraction_rowContract P hR hS hRS))
      hPerr T'⟩

end MatrixContractionTail

/-- Starting from any index in a bounded-refinement partition sequence, the
remaining suffix expands to an ordinary contraction tail of error at most
`r * t`. -/
theorem exists_matrixContractionTail_of_boundedErrorRefinementPartitionSequence
    {n m r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hr : 0 < r)
    (S : BoundedErrorRefinementPartitionSequence M r t) :
    ∀ i, i ≤ S.stepCount →
      Nonempty (MatrixContractionTail M (r * t) (S.partition i)) := by
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
      Nonempty (MatrixContractionTail M (r * t) (S.partition a.1)))
    (InvImage.wf
      (fun a : {i // i ≤ S.stepCount} => S.stepCount - a.1)
      <| (Nat.lt_wfRel).2)
    ⟨i, hi⟩ ?_
  intro a ih
  by_cases hlast : a.1 = S.stepCount
  · refine ⟨{
      stepCount := 0
      partition := fun _ => S.partition a.1
      starts := rfl
      ends := by simpa [hlast] using S.ends
      step_contracts := by intro j hj; omega
      errorValue_le := by
        intro j hj
        exact MatrixPartition.errorValueAtMost_mono ht_le
          (by simpa [hlast] using S.errorValue_le S.stepCount le_rfl)
    }⟩
  · have hlt : a.1 < S.stepCount := lt_of_le_of_ne a.2 hlast
    let b : {i // i ≤ S.stepCount} := ⟨a.1 + 1, by omega⟩
    have hdec : S.stepCount - b.1 < S.stepCount - a.1 := by
      dsimp [b]
      omega
    rcases ih b hdec with ⟨Tnext⟩
    have hstep : MatrixPartition.RRefines
        (S.partition a.1) (S.partition (a.1 + 1)) r :=
      S.step_rrefines a.1 hlt
    have hnext : ErrorValueAtMost M (S.partition (a.1 + 1)) t :=
      S.errorValue_le (a.1 + 1) (by omega)
    exact MatrixContractionTail.exists_of_rrefines
      (S.partition a.1) (S.partition (a.1 + 1)) hstep hnext Tnext

/-- Lemma 8 in matrix-partition form: a bounded-refinement partition sequence
expands to a matrix contraction sequence, with the multiplicative error
bound `r * t`. -/
theorem matrixTwinWidthAtMost_of_boundedErrorRefinementPartitionSequence
    {n m r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hr : 0 < r)
    (S : Nonempty (BoundedErrorRefinementPartitionSequence M r t)) :
    MatrixTwinWidthAtMost M (r * t) := by
  rcases S with ⟨S⟩
  rcases exists_matrixContractionTail_of_boundedErrorRefinementPartitionSequence
      hr S 0 (Nat.zero_le S.stepCount) with ⟨T⟩
  exact ⟨{
    stepCount := T.stepCount
    partition := T.partition
    starts := by
      rw [T.starts]
      exact S.starts
    ends := T.ends
    step_contracts := T.step_contracts
    errorValue_le := T.errorValue_le
  }⟩

/-- Lemma 8 with the numerical parameters used by Theorem 10 for alphabet size
`a`. -/
theorem matrixTwinWidthAtMost_of_theorem10ErrorRefinementSequence
    {n m a d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (ha : 0 < a)
    (S : Nonempty (BoundedErrorRefinementPartitionSequence M
      (2 * a ^ (d + 1)) (d * a ^ (d + 1)))) :
    MatrixTwinWidthAtMost M (theorem10AlphabetErrorRefinementBound a d) := by
  have hr : 0 < 2 * a ^ (d + 1) := by
    exact Nat.mul_pos (by decide : 0 < 2) (pow_pos ha _)
  have h := matrixTwinWidthAtMost_of_boundedErrorRefinementPartitionSequence
    (M := M) (r := 2 * a ^ (d + 1)) (t := d * a ^ (d + 1)) hr S
  have hmul :
      (2 * a ^ (d + 1)) * (d * a ^ (d + 1)) =
        theorem10AlphabetErrorRefinementBound a d := by
    unfold theorem10AlphabetErrorRefinementBound
    have hp : a ^ (d + 1) * a ^ (d + 1) = a ^ (2 * (d + 1)) := by
      rw [← pow_add]
      have hexp : d + 1 + (d + 1) = 2 * (d + 1) := by omega
      simp [hexp]
    calc
      (2 * a ^ (d + 1)) * (d * a ^ (d + 1))
          = 2 * d * (a ^ (d + 1) * a ^ (d + 1)) := by ring
      _ = 2 * d * a ^ (2 * (d + 1)) := by rw [hp]
  simpa [hmul] using h

namespace MatrixDivision

/-- The unordered matrix partition underlying a consecutive matrix division. -/
noncomputable def toPartition {n m : ℕ} (D : MatrixDivision n m) :
    MatrixPartition n m where
  rowParts :=
    (Finset.univ : Finset (Fin (D.rowCuts + 1))).map
      ⟨D.rowDiv.part, D.rowDiv.part_injective⟩
  row_nonempty := by
    intro R hR
    rcases Finset.mem_map.mp hR with ⟨i, _hi, rfl⟩
    exact D.rowDiv.part_nonempty i
  row_disjoint := by
    intro R S hR hS hRS
    rcases Finset.mem_map.mp hR with ⟨i, _hi, rfl⟩
    rcases Finset.mem_map.mp hS with ⟨j, _hj, rfl⟩
    exact D.rowDiv.part_disjoint (by
      intro hij
      subst j
      exact hRS rfl)
  row_cover := by
    intro r
    rcases D.rowDiv.part_cover r with ⟨i, hi⟩
    exact ⟨D.rowDiv.part i, by simp, hi⟩
  colParts :=
    (Finset.univ : Finset (Fin (D.colCuts + 1))).map
      ⟨D.colDiv.part, D.colDiv.part_injective⟩
  col_nonempty := by
    intro C hC
    rcases Finset.mem_map.mp hC with ⟨j, _hj, rfl⟩
    exact D.colDiv.part_nonempty j
  col_disjoint := by
    intro C E hC hE hCE
    rcases Finset.mem_map.mp hC with ⟨i, _hi, rfl⟩
    rcases Finset.mem_map.mp hE with ⟨j, _hj, rfl⟩
    exact D.colDiv.part_disjoint (by
      intro hij
      subst j
      exact hCE rfl)
  col_cover := by
    intro c
    rcases D.colDiv.part_cover c with ⟨j, hj⟩
    exact ⟨D.colDiv.part j, by simp, hj⟩

@[simp] theorem rowParts_toPartition {n m : ℕ} (D : MatrixDivision n m) :
    (D.toPartition).rowParts =
      (Finset.univ : Finset (Fin (D.rowCuts + 1))).map
        ⟨D.rowDiv.part, D.rowDiv.part_injective⟩ :=
  rfl

@[simp] theorem colParts_toPartition {n m : ℕ} (D : MatrixDivision n m) :
    (D.toPartition).colParts =
      (Finset.univ : Finset (Fin (D.colCuts + 1))).map
        ⟨D.colDiv.part, D.colDiv.part_injective⟩ :=
  rfl

/-- Alphabet profiles used in the Section 5.8 refinement.  A row or column
part of mixed value at most `d` has at most `d + 1` non-mixed intervals, so an
alphabet value on `Fin (d + 1)` is enough to encode its profile. -/
abbrev AlphabetProfile (α : Type u) (d : ℕ) : Type u :=
  Fin (d + 1) → α

@[simp] theorem fintype_card_alphabetProfile [Fintype α] (d : ℕ) :
    Fintype.card (AlphabetProfile α d) = Fintype.card α ^ (d + 1) := by
  simp [AlphabetProfile]

/-- Linear position of a column mixed-value item: zones have even positions
and cuts have odd positions. -/
def colMixedItemPos {k : ℕ} : Sum (Fin (k + 1)) (Fin k) → ℕ
  | Sum.inl j => 2 * j.1
  | Sum.inr j => 2 * j.1 + 1

/-- Linear position of a row mixed-value item: zones have even positions and
cuts have odd positions. -/
def rowMixedItemPos {k : ℕ} : Sum (Fin (k + 1)) (Fin k) → ℕ
  | Sum.inl i => 2 * i.1
  | Sum.inr i => 2 * i.1 + 1

/-- Number of mixed zones/cuts strictly before a column zone. -/
noncomputable def colBadBefore {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (j : Fin (D.colCuts + 1)) : ℕ :=
  ((colMixedItems M (D.rowDiv.part i) D.colDiv).filter
    fun item => colMixedItemPos item < 2 * j.1).card

/-- Number of mixed zones/cuts strictly before a row zone. -/
noncomputable def rowBadBefore {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (i : Fin (D.rowCuts + 1)) : ℕ :=
  ((rowMixedItems M D.rowDiv (D.colDiv.part j)).filter
    fun item => rowMixedItemPos item < 2 * i.1).card

theorem colBadBefore_le_colMixedValue {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (j : Fin (D.colCuts + 1)) :
    colBadBefore M D i j ≤ colMixedValue M (D.rowDiv.part i) D.colDiv := by
  unfold colBadBefore
  calc
    ((colMixedItems M (D.rowDiv.part i) D.colDiv).filter
        fun item => colMixedItemPos item < 2 * j.1).card
        ≤ (colMixedItems M (D.rowDiv.part i) D.colDiv).card :=
          Finset.card_filter_le _ _
    _ = colMixedValue M (D.rowDiv.part i) D.colDiv :=
          colMixedItems_card M (D.rowDiv.part i) D.colDiv

theorem rowBadBefore_le_rowMixedValue {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (i : Fin (D.rowCuts + 1)) :
    rowBadBefore M D j i ≤ rowMixedValue M D.rowDiv (D.colDiv.part j) := by
  unfold rowBadBefore
  calc
    ((rowMixedItems M D.rowDiv (D.colDiv.part j)).filter
        fun item => rowMixedItemPos item < 2 * i.1).card
        ≤ (rowMixedItems M D.rowDiv (D.colDiv.part j)).card :=
          Finset.card_filter_le _ _
    _ = rowMixedValue M D.rowDiv (D.colDiv.part j) :=
          rowMixedItems_card M D.rowDiv (D.colDiv.part j)

theorem colBadBefore_lt_succ_of_mixedValueAtMost {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1)) :
    colBadBefore M D i j < d + 1 := by
  exact Nat.lt_succ_of_le
    (le_trans (colBadBefore_le_colMixedValue M D i j) (hD.2 i))

theorem rowBadBefore_lt_succ_of_mixedValueAtMost {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (j : Fin (D.colCuts + 1)) (i : Fin (D.rowCuts + 1)) :
    rowBadBefore M D j i < d + 1 := by
  exact Nat.lt_succ_of_le
    (le_trans (rowBadBefore_le_rowMixedValue M D j i) (hD.1 j))

/-- Candidate representative column zones for a row-profile coordinate. -/
noncomputable def rowProfileCandidates {n m d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (q : Fin (d + 1)) : Finset (Fin (D.colCuts + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j =>
      ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) ∧
        colBadBefore M D i j = q.1

/-- Candidate representative row zones for a column-profile coordinate. -/
noncomputable def colProfileCandidates {n m d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (q : Fin (d + 1)) : Finset (Fin (D.rowCuts + 1)) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) ∧
        rowBadBefore M D j i = q.1

theorem mem_rowProfileCandidates {n m d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (q : Fin (d + 1)) (j : Fin (D.colCuts + 1)) :
    j ∈ rowProfileCandidates (d := d) M D i q ↔
      ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) ∧
        colBadBefore M D i j = q.1 := by
  classical
  simp [rowProfileCandidates]

theorem mem_colProfileCandidates {n m d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (q : Fin (d + 1)) (i : Fin (D.rowCuts + 1)) :
    i ∈ colProfileCandidates (d := d) M D j q ↔
      ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) ∧
        rowBadBefore M D j i = q.1 := by
  classical
  simp [colProfileCandidates]

theorem rowProfileCandidates_nonempty_of_not_zoneMixed {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j)) :
    (rowProfileCandidates (d := d) M D i
      ⟨colBadBefore M D i j,
        colBadBefore_lt_succ_of_mixedValueAtMost hD i j⟩).Nonempty := by
  refine ⟨j, ?_⟩
  rw [mem_rowProfileCandidates]
  exact ⟨hnot, rfl⟩

theorem colProfileCandidates_nonempty_of_not_zoneMixed {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j)) :
    (colProfileCandidates (d := d) M D j
      ⟨rowBadBefore M D j i,
        rowBadBefore_lt_succ_of_mixedValueAtMost hD j i⟩).Nonempty := by
  refine ⟨i, ?_⟩
  rw [mem_colProfileCandidates]
  exact ⟨hnot, rfl⟩

theorem no_colMixedItem_between_profile_min_and_zone {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j)) :
    let q : Fin (d + 1) :=
      ⟨colBadBefore M D i j,
        colBadBefore_lt_succ_of_mixedValueAtMost hD i j⟩
    let candidates := rowProfileCandidates (d := d) M D i q
    let rep := candidates.min'
      (rowProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot)
    ∀ item ∈ colMixedItems M (D.rowDiv.part i) D.colDiv,
      colMixedItemPos item < 2 * j.1 →
        colMixedItemPos item < 2 * rep.1 := by
  classical
  intro q candidates rep item hitem hbefore
  have hjmem : j ∈ candidates := by
    rw [mem_rowProfileCandidates]
    exact ⟨hnot, rfl⟩
  have hrep_mem : rep ∈ candidates := by
    exact Finset.min'_mem candidates
      (rowProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot)
  have hrep_le_j : rep ≤ j :=
    Finset.min'_le candidates j hjmem
  by_contra hnot_before_rep
  have hlt :
      (((colMixedItems M (D.rowDiv.part i) D.colDiv).filter
          fun item => colMixedItemPos item < 2 * rep.1).card) <
        (((colMixedItems M (D.rowDiv.part i) D.colDiv).filter
          fun item => colMixedItemPos item < 2 * j.1).card) := by
    refine MatrixPartition.card_filter_lt_card_filter_of_exists ?_ ?_
    · intro x hx
      have hrepj : rep.1 ≤ j.1 := Fin.le_iff_val_le_val.mp hrep_le_j
      omega
    · exact ⟨item, hitem, hbefore, hnot_before_rep⟩
  have hrep_bad :
      colBadBefore M D i rep = q.1 :=
    (mem_rowProfileCandidates M D i q rep).mp hrep_mem |>.2
  have hj_bad :
      colBadBefore M D i j = q.1 :=
    (mem_rowProfileCandidates M D i q j).mp hjmem |>.2
  unfold colBadBefore at hrep_bad hj_bad
  omega

theorem no_rowMixedItem_between_profile_min_and_zone {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j)) :
    let q : Fin (d + 1) :=
      ⟨rowBadBefore M D j i,
        rowBadBefore_lt_succ_of_mixedValueAtMost hD j i⟩
    let candidates := colProfileCandidates (d := d) M D j q
    let rep := candidates.min'
      (colProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot)
    ∀ item ∈ rowMixedItems M D.rowDiv (D.colDiv.part j),
      rowMixedItemPos item < 2 * i.1 →
        rowMixedItemPos item < 2 * rep.1 := by
  classical
  intro q candidates rep item hitem hbefore
  have himem : i ∈ candidates := by
    rw [mem_colProfileCandidates]
    exact ⟨hnot, rfl⟩
  have hrep_mem : rep ∈ candidates := by
    exact Finset.min'_mem candidates
      (colProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot)
  have hrep_le_i : rep ≤ i :=
    Finset.min'_le candidates i himem
  by_contra hnot_before_rep
  have hlt :
      (((rowMixedItems M D.rowDiv (D.colDiv.part j)).filter
          fun item => rowMixedItemPos item < 2 * rep.1).card) <
        (((rowMixedItems M D.rowDiv (D.colDiv.part j)).filter
          fun item => rowMixedItemPos item < 2 * i.1).card) := by
    refine MatrixPartition.card_filter_lt_card_filter_of_exists ?_ ?_
    · intro x hx
      have hrepj : rep.1 ≤ i.1 := Fin.le_iff_val_le_val.mp hrep_le_i
      omega
    · exact ⟨item, hitem, hbefore, hnot_before_rep⟩
  have hrep_bad :
      rowBadBefore M D j rep = q.1 :=
    (mem_colProfileCandidates M D j q rep).mp hrep_mem |>.2
  have hi_bad :
      rowBadBefore M D j i = q.1 :=
    (mem_colProfileCandidates M D j q i).mp himem |>.2
  unfold rowBadBefore at hrep_bad hi_bad
  omega

theorem row_eq_next_col_zone_of_not_mixed_adjacent {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Division m (k + 1)}
    (u : Fin k)
    (hL : ¬ ZoneMixed M R (C.part u.castSucc))
    (hR : ¬ ZoneMixed M R (C.part u.succ))
    (hcut : ¬ ColCutMixed M R C u)
    {r₁ r₂ : Fin n} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R)
    (hleft : M r₁ (C.first u.castSucc) = M r₂ (C.first u.castSucc)) :
    M r₁ (C.first u.succ) = M r₂ (C.first u.succ) := by
  have hunion :
      ¬ ZoneMixed M R (C.part u.castSucc ∪ C.part u.succ) :=
    not_zoneMixed_union_consecutive_cols_of_not_mixed_cut C u hL hR hcut
  rcases (not_zoneMixed_iff_vertical_or_horizontal M R
      (C.part u.castSucc ∪ C.part u.succ)).mp hunion with hv | hh
  · exact hv hr₁ hr₂ (Finset.mem_union_right _ (C.first_mem u.succ))
  · have h₁ :
        M r₁ (C.first u.castSucc) = M r₁ (C.first u.succ) :=
      hh hr₁ (Finset.mem_union_left _ (C.first_mem u.castSucc))
        (Finset.mem_union_right _ (C.first_mem u.succ))
    have h₂ :
        M r₂ (C.first u.castSucc) = M r₂ (C.first u.succ) :=
      hh hr₂ (Finset.mem_union_left _ (C.first_mem u.castSucc))
        (Finset.mem_union_right _ (C.first_mem u.succ))
    exact h₁.symm.trans (hleft.trans h₂)

theorem col_eq_next_row_zone_of_not_mixed_adjacent {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n (k + 1)} {C : Finset (Fin m)}
    (u : Fin k)
    (hL : ¬ ZoneMixed M (R.part u.castSucc) C)
    (hR : ¬ ZoneMixed M (R.part u.succ) C)
    (hcut : ¬ RowCutMixed M R C u)
    {c₁ c₂ : Fin m} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hleft : M (R.first u.castSucc) c₁ = M (R.first u.castSucc) c₂) :
    M (R.first u.succ) c₁ = M (R.first u.succ) c₂ := by
  have hunion :
      ¬ ZoneMixed M (R.part u.castSucc ∪ R.part u.succ) C :=
    not_zoneMixed_union_consecutive_rows_of_not_mixed_cut R u hL hR hcut
  rcases (not_zoneMixed_iff_vertical_or_horizontal M
      (R.part u.castSucc ∪ R.part u.succ) C).mp hunion with hv | hh
  · have h₁ :
        M (R.first u.castSucc) c₁ = M (R.first u.succ) c₁ :=
      hv (Finset.mem_union_left _ (R.first_mem u.castSucc))
        (Finset.mem_union_right _ (R.first_mem u.succ)) hc₁
    have h₂ :
        M (R.first u.castSucc) c₂ = M (R.first u.succ) c₂ :=
      hv (Finset.mem_union_left _ (R.first_mem u.castSucc))
        (Finset.mem_union_right _ (R.first_mem u.succ)) hc₂
    exact h₁.symm.trans (hleft.trans h₂)
  · exact hh (Finset.mem_union_right _ (R.first_mem u.succ)) hc₁ hc₂

theorem row_eq_col_zone_first_of_no_mixed_between {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Division m (k + 1)}
    {a b : Fin (k + 1)}
    (hab : a ≤ b)
    (hbnot : ¬ ZoneMixed M R (C.part b))
    (hno :
      ∀ item ∈ colMixedItems M R C,
        colMixedItemPos item < 2 * b.1 → colMixedItemPos item < 2 * a.1)
    {r₁ r₂ : Fin n} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R)
    (hstart : M r₁ (C.first a) = M r₂ (C.first a)) :
    M r₁ (C.first b) = M r₂ (C.first b) := by
  classical
  by_cases hEq : a = b
  · subst b
    exact hstart
  · have hablt : a < b := lt_of_le_of_ne hab hEq
    let u : Fin k := ⟨a.1, by
      have hb : b.1 < k + 1 := b.2
      have habv : a.1 < b.1 := Fin.lt_def.mp hablt
      omega⟩
    have hua : u.castSucc = a := by
      ext
      rfl
    let a' : Fin (k + 1) := u.succ
    have ha'val : a'.1 = a.1 + 1 := by
      simp [a', u]
    have ha'le : a' ≤ b := by
      rw [Fin.le_iff_val_le_val]
      have habv : a.1 < b.1 := Fin.lt_def.mp hablt
      simp [a', u]
      omega
    have hL : ¬ ZoneMixed M R (C.part u.castSucc) := by
      rw [hua]
      by_contra hmix
      have hitem : Sum.inl a ∈ colMixedItems M R C := by
        simpa using (mem_colMixedItems_zone M R C a).mpr hmix
      have hbefore : colMixedItemPos (Sum.inl a) < 2 * b.1 := by
        simp [colMixedItemPos]
        have habv : a.1 < b.1 := Fin.lt_def.mp hablt
        omega
      have hbad := hno (Sum.inl a) hitem hbefore
      simp [colMixedItemPos] at hbad
    have hcut : ¬ ColCutMixed M R C u := by
      by_contra hmix
      have hitem : Sum.inr u ∈ colMixedItems M R C := by
        simpa using (mem_colMixedItems_cut M R C u).mpr hmix
      have hbefore : colMixedItemPos (Sum.inr u) < 2 * b.1 := by
        simp [colMixedItemPos, u]
        have habv : a.1 < b.1 := Fin.lt_def.mp hablt
        omega
      have hbad := hno (Sum.inr u) hitem hbefore
      simp [colMixedItemPos, u] at hbad
    have hR : ¬ ZoneMixed M R (C.part u.succ) := by
      by_cases hnext : a' = b
      · simpa [a', hnext] using hbnot
      · have hnextlt : a' < b := lt_of_le_of_ne ha'le hnext
        by_contra hmix
        have hitem : Sum.inl a' ∈ colMixedItems M R C := by
          simpa using (mem_colMixedItems_zone M R C a').mpr hmix
        have hbefore : colMixedItemPos (Sum.inl a') < 2 * b.1 := by
          simp [colMixedItemPos]
          exact hnextlt
        have hbad := hno (Sum.inl a') hitem hbefore
        simp [colMixedItemPos, ha'val] at hbad
    have hstep :
        M r₁ (C.first a') = M r₂ (C.first a') := by
      simpa [a', hua] using
        row_eq_next_col_zone_of_not_mixed_adjacent (M := M) (R := R) (C := C)
          u hL hR hcut hr₁ hr₂ (by simpa [hua] using hstart)
    have hno' :
        ∀ item ∈ colMixedItems M R C,
          colMixedItemPos item < 2 * b.1 → colMixedItemPos item < 2 * a'.1 := by
      intro item hitem hbefore
      by_contra hnot
      have hbad := hno item hitem hbefore
      have ha_lt_a' : a.1 < a'.1 := by omega
      omega
    exact row_eq_col_zone_first_of_no_mixed_between
      (M := M) (R := R) (C := C) ha'le hbnot hno' hr₁ hr₂ hstep
termination_by b.1 - a.1
decreasing_by
  simp_wf
  omega

theorem col_eq_row_zone_first_of_no_mixed_between {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n (k + 1)} {C : Finset (Fin m)}
    {a b : Fin (k + 1)}
    (hab : a ≤ b)
    (hbnot : ¬ ZoneMixed M (R.part b) C)
    (hno :
      ∀ item ∈ rowMixedItems M R C,
        rowMixedItemPos item < 2 * b.1 → rowMixedItemPos item < 2 * a.1)
    {c₁ c₂ : Fin m} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hstart : M (R.first a) c₁ = M (R.first a) c₂) :
    M (R.first b) c₁ = M (R.first b) c₂ := by
  classical
  by_cases hEq : a = b
  · subst b
    exact hstart
  · have hablt : a < b := lt_of_le_of_ne hab hEq
    let u : Fin k := ⟨a.1, by
      have hb : b.1 < k + 1 := b.2
      have habv : a.1 < b.1 := Fin.lt_def.mp hablt
      omega⟩
    have hua : u.castSucc = a := by
      ext
      rfl
    let a' : Fin (k + 1) := u.succ
    have ha'val : a'.1 = a.1 + 1 := by
      simp [a', u]
    have ha'le : a' ≤ b := by
      rw [Fin.le_iff_val_le_val]
      have habv : a.1 < b.1 := Fin.lt_def.mp hablt
      simp [a', u]
      omega
    have hL : ¬ ZoneMixed M (R.part u.castSucc) C := by
      rw [hua]
      by_contra hmix
      have hitem : Sum.inl a ∈ rowMixedItems M R C := by
        simpa using (mem_rowMixedItems_zone M R C a).mpr hmix
      have hbefore : rowMixedItemPos (Sum.inl a) < 2 * b.1 := by
        simp [rowMixedItemPos]
        have habv : a.1 < b.1 := Fin.lt_def.mp hablt
        omega
      have hbad := hno (Sum.inl a) hitem hbefore
      simp [rowMixedItemPos] at hbad
    have hcut : ¬ RowCutMixed M R C u := by
      by_contra hmix
      have hitem : Sum.inr u ∈ rowMixedItems M R C := by
        simpa using (mem_rowMixedItems_cut M R C u).mpr hmix
      have hbefore : rowMixedItemPos (Sum.inr u) < 2 * b.1 := by
        simp [rowMixedItemPos, u]
        have habv : a.1 < b.1 := Fin.lt_def.mp hablt
        omega
      have hbad := hno (Sum.inr u) hitem hbefore
      simp [rowMixedItemPos, u] at hbad
    have hR : ¬ ZoneMixed M (R.part u.succ) C := by
      by_cases hnext : a' = b
      · simpa [a', hnext] using hbnot
      · have hnextlt : a' < b := lt_of_le_of_ne ha'le hnext
        by_contra hmix
        have hitem : Sum.inl a' ∈ rowMixedItems M R C := by
          simpa using (mem_rowMixedItems_zone M R C a').mpr hmix
        have hbefore : rowMixedItemPos (Sum.inl a') < 2 * b.1 := by
          simp [rowMixedItemPos]
          exact hnextlt
        have hbad := hno (Sum.inl a') hitem hbefore
        simp [rowMixedItemPos, ha'val] at hbad
    have hstep :
        M (R.first a') c₁ = M (R.first a') c₂ := by
      simpa [a', hua] using
        col_eq_next_row_zone_of_not_mixed_adjacent (M := M) (R := R) (C := C)
          u hL hR hcut hc₁ hc₂ (by simpa [hua] using hstart)
    have hno' :
        ∀ item ∈ rowMixedItems M R C,
          rowMixedItemPos item < 2 * b.1 → rowMixedItemPos item < 2 * a'.1 := by
      intro item hitem hbefore
      by_contra hnot
      have hbad := hno item hitem hbefore
      have ha_lt_a' : a.1 < a'.1 := by omega
      omega
    exact col_eq_row_zone_first_of_no_mixed_between
      (M := M) (R := R) (C := C) ha'le hbnot hno' hc₁ hc₂ hstep
termination_by b.1 - a.1
decreasing_by
  simp_wf
  omega

/-- Row profile for one row part of a division.  The `q`-th coordinate is read at
the first non-mixed column zone whose preceding-bad-item count is `q`, if such
a zone exists. -/
noncomputable def rowProfile {n m d : ℕ}
    [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (r : Fin n) : AlphabetProfile α d := by
  classical
  exact fun q =>
    if h : (rowProfileCandidates (d := d) M D i q).Nonempty then
      M r (D.colDiv.first ((rowProfileCandidates (d := d) M D i q).min' h))
    else
      default

/-- Column profile dual to `rowProfile`. -/
noncomputable def colProfile {n m d : ℕ}
    [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (c : Fin m) : AlphabetProfile α d := by
  classical
  exact fun q =>
    if h : (colProfileCandidates (d := d) M D j q).Nonempty then
      M (D.rowDiv.first ((colProfileCandidates (d := d) M D j q).min' h)) c
    else
      default

theorem row_eq_on_horizontal_zone_of_profile_eq {n m d : ℕ}
    [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j))
    (hh : ZoneHorizontal M (D.rowDiv.part i) (D.colDiv.part j))
    {r₁ r₂ : Fin n}
    (hr₁ : r₁ ∈ D.rowDiv.part i) (hr₂ : r₂ ∈ D.rowDiv.part i)
    (hprof : rowProfile (d := d) M D i r₁ =
      rowProfile (d := d) M D i r₂) :
    ∀ ⦃c : Fin m⦄, c ∈ D.colDiv.part j → M r₁ c = M r₂ c := by
  classical
  intro c hc
  let q : Fin (d + 1) :=
    ⟨colBadBefore M D i j,
      colBadBefore_lt_succ_of_mixedValueAtMost hD i j⟩
  let candidates := rowProfileCandidates (d := d) M D i q
  let hcan : candidates.Nonempty :=
    rowProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot
  let rep := candidates.min' hcan
  have hjmem : j ∈ candidates := by
    rw [mem_rowProfileCandidates]
    exact ⟨hnot, rfl⟩
  have hrep_le : rep ≤ j := Finset.min'_le candidates j hjmem
  have hno :
      ∀ item ∈ colMixedItems M (D.rowDiv.part i) D.colDiv,
        colMixedItemPos item < 2 * j.1 → colMixedItemPos item < 2 * rep.1 := by
    simpa [q, candidates, rep] using
      no_colMixedItem_between_profile_min_and_zone hD i j hnot
  have hstart :
      M r₁ (D.colDiv.first rep) = M r₂ (D.colDiv.first rep) := by
    have hq := congrFun hprof q
    simpa [rowProfile, q, candidates, hcan, rep] using hq
  have hfirst :
      M r₁ (D.colDiv.first j) = M r₂ (D.colDiv.first j) :=
    row_eq_col_zone_first_of_no_mixed_between
      (M := M) (R := D.rowDiv.part i) (C := D.colDiv)
      hrep_le hnot hno hr₁ hr₂ hstart
  have h₁ : M r₁ (D.colDiv.first j) = M r₁ c :=
    hh hr₁ (D.colDiv.first_mem j) hc
  have h₂ : M r₂ (D.colDiv.first j) = M r₂ c :=
    hh hr₂ (D.colDiv.first_mem j) hc
  exact h₁.symm.trans (hfirst.trans h₂)

theorem col_eq_on_vertical_zone_of_profile_eq {n m d : ℕ}
    [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j))
    (hv : ZoneVertical M (D.rowDiv.part i) (D.colDiv.part j))
    {c₁ c₂ : Fin m}
    (hc₁ : c₁ ∈ D.colDiv.part j) (hc₂ : c₂ ∈ D.colDiv.part j)
    (hprof : colProfile (d := d) M D j c₁ =
      colProfile (d := d) M D j c₂) :
    ∀ ⦃r : Fin n⦄, r ∈ D.rowDiv.part i → M r c₁ = M r c₂ := by
  classical
  intro r hr
  let q : Fin (d + 1) :=
    ⟨rowBadBefore M D j i,
      rowBadBefore_lt_succ_of_mixedValueAtMost hD j i⟩
  let candidates := colProfileCandidates (d := d) M D j q
  let hcan : candidates.Nonempty :=
    colProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot
  let rep := candidates.min' hcan
  have himem : i ∈ candidates := by
    rw [mem_colProfileCandidates]
    exact ⟨hnot, rfl⟩
  have hrep_le : rep ≤ i := Finset.min'_le candidates i himem
  have hno :
      ∀ item ∈ rowMixedItems M D.rowDiv (D.colDiv.part j),
        rowMixedItemPos item < 2 * i.1 → rowMixedItemPos item < 2 * rep.1 := by
    simpa [q, candidates, rep] using
      no_rowMixedItem_between_profile_min_and_zone hD i j hnot
  have hstart :
      M (D.rowDiv.first rep) c₁ = M (D.rowDiv.first rep) c₂ := by
    have hq := congrFun hprof q
    simpa [colProfile, q, candidates, hcan, rep] using hq
  have hfirst :
      M (D.rowDiv.first i) c₁ = M (D.rowDiv.first i) c₂ :=
    col_eq_row_zone_first_of_no_mixed_between
      (M := M) (R := D.rowDiv) (C := D.colDiv.part j)
      hrep_le hnot hno hc₁ hc₂ hstart
  have h₁ : M r c₁ = M (D.rowDiv.first i) c₁ :=
    hv hr (D.rowDiv.first_mem i) hc₁
  have h₂ : M r c₂ = M (D.rowDiv.first i) c₂ :=
    hv hr (D.rowDiv.first_mem i) hc₂
  exact h₁.trans (hfirst.trans h₂.symm)

/-- Recover the row-division index represented by a row part of
`D.toPartition`.  The default branch is never used for actual row parts. -/
noncomputable def rowIndexOfPartitionPart {n m : ℕ}
    (D : MatrixDivision n m) (R : Finset (Fin n)) :
    Fin (D.rowCuts + 1) :=
  if h : R ∈ D.toPartition.rowParts then
    Classical.choose (by
      rcases Finset.mem_map.mp h with ⟨i, _hi, hi⟩
      exact ⟨i, hi⟩)
  else
    0

theorem rowIndexOfPartitionPart_spec {n m : ℕ}
    (D : MatrixDivision n m) {R : Finset (Fin n)}
    (hR : R ∈ D.toPartition.rowParts) :
    D.rowDiv.part (rowIndexOfPartitionPart D R) = R := by
  classical
  unfold rowIndexOfPartitionPart
  simp only [dif_pos hR]
  exact Classical.choose_spec (by
    rcases Finset.mem_map.mp hR with ⟨i, _hi, hi⟩
    exact ⟨i, hi⟩)

/-- Recover the column-division index represented by a column part of
`D.toPartition`.  The default branch is never used for actual column parts. -/
noncomputable def colIndexOfPartitionPart {n m : ℕ}
    (D : MatrixDivision n m) (C : Finset (Fin m)) :
    Fin (D.colCuts + 1) :=
  if h : C ∈ D.toPartition.colParts then
    Classical.choose (by
      rcases Finset.mem_map.mp h with ⟨j, _hj, hj⟩
      exact ⟨j, hj⟩)
  else
    0

theorem colIndexOfPartitionPart_spec {n m : ℕ}
    (D : MatrixDivision n m) {C : Finset (Fin m)}
    (hC : C ∈ D.toPartition.colParts) :
    D.colDiv.part (colIndexOfPartitionPart D C) = C := by
  classical
  unfold colIndexOfPartitionPart
  simp only [dif_pos hC]
  exact Classical.choose_spec (by
    rcases Finset.mem_map.mp hC with ⟨j, _hj, hj⟩
    exact ⟨j, hj⟩)

/-- The profile refinement of a matrix division: each row part is split by
its row profile and each column part by its column profile. -/
noncomputable def profilePartition {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) : MatrixPartition n m :=
  D.toPartition.refineByLabels
    (fun R r => rowProfile (d := d) M D (rowIndexOfPartitionPart D R) r)
    (fun C c => colProfile (d := d) M D (colIndexOfPartitionPart D C) c)

/-- A profile partition refines its underlying division partition with factor
`|α|^(d+1)` on both sides. -/
theorem profilePartition_rrefines_toPartition {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) :
    MatrixPartition.RRefines (profilePartition (d := d) M D) D.toPartition
      (Fintype.card α ^ (d + 1)) := by
  classical
  constructor
  · simpa [profilePartition] using
      MatrixPartition.partsRRefine_splitPartsByLabel
        (P := D.toPartition.rowParts)
        (label := fun R r =>
          rowProfile (d := d) M D (rowIndexOfPartitionPart D R) r)
        D.toPartition.row_disjoint
        (by simp [AlphabetProfile])
  · simpa [profilePartition] using
      MatrixPartition.partsRRefine_splitPartsByLabel
        (P := D.toPartition.colParts)
        (label := fun C c =>
          colProfile (d := d) M D (colIndexOfPartitionPart D C) c)
        D.toPartition.col_disjoint
        (by simp [AlphabetProfile])

theorem rowProfile_eq_of_mem_profilePartition_rowPart_of_subset {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    {R : Finset (Fin n)} {i : Fin (D.rowCuts + 1)}
    (hR : R ∈ (profilePartition (d := d) M D).rowParts)
    (hRi : R ⊆ D.rowDiv.part i)
    {r₁ r₂ : Fin n} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R) :
    rowProfile (d := d) M D i r₁ =
      rowProfile (d := d) M D i r₂ := by
  classical
  rcases MatrixPartition.mem_splitPartsByLabel.mp
      (by simpa [profilePartition] using hR) with ⟨_hne, A, hA, b, hRdef⟩
  have hAeq : A = D.rowDiv.part i := by
    rcases Finset.mem_map.mp hA with ⟨i₀, _hi₀, hi₀A⟩
    change D.rowDiv.part i₀ = A at hi₀A
    rw [← hi₀A]
    by_contra hne
    have hr₁A : r₁ ∈ D.rowDiv.part i₀ := by
      rw [hRdef] at hr₁
      simpa [hi₀A] using (Finset.mem_filter.mp hr₁).1
    have hr₁i : r₁ ∈ D.rowDiv.part i := hRi hr₁
    have hidxne : i₀ ≠ i := by
      intro hij
      exact hne (by rw [hij])
    exact Finset.disjoint_left.mp (D.rowDiv.part_disjoint hidxne) hr₁A hr₁i
  have hidx : rowIndexOfPartitionPart D A = i := by
    apply D.rowDiv.part_injective
    rw [rowIndexOfPartitionPart_spec D hA, hAeq]
  rw [hRdef] at hr₁ hr₂
  have h₁ : rowProfile (d := d) M D (rowIndexOfPartitionPart D A) r₁ = b :=
    (Finset.mem_filter.mp hr₁).2
  have h₂ : rowProfile (d := d) M D (rowIndexOfPartitionPart D A) r₂ = b :=
    (Finset.mem_filter.mp hr₂).2
  simpa [hidx] using h₁.trans h₂.symm

theorem colProfile_eq_of_mem_profilePartition_colPart_of_subset {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    {C : Finset (Fin m)} {j : Fin (D.colCuts + 1)}
    (hC : C ∈ (profilePartition (d := d) M D).colParts)
    (hCj : C ⊆ D.colDiv.part j)
    {c₁ c₂ : Fin m} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) :
    colProfile (d := d) M D j c₁ =
      colProfile (d := d) M D j c₂ := by
  classical
  rcases MatrixPartition.mem_splitPartsByLabel.mp
      (by simpa [profilePartition] using hC) with ⟨_hne, A, hA, b, hCdef⟩
  have hAeq : A = D.colDiv.part j := by
    rcases Finset.mem_map.mp hA with ⟨j₀, _hj₀, hj₀A⟩
    change D.colDiv.part j₀ = A at hj₀A
    rw [← hj₀A]
    by_contra hne
    have hc₁A : c₁ ∈ D.colDiv.part j₀ := by
      rw [hCdef] at hc₁
      simpa [hj₀A] using (Finset.mem_filter.mp hc₁).1
    have hc₁j : c₁ ∈ D.colDiv.part j := hCj hc₁
    have hidxne : j₀ ≠ j := by
      intro hij
      exact hne (by rw [hij])
    exact Finset.disjoint_left.mp (D.colDiv.part_disjoint hidxne) hc₁A hc₁j
  have hidx : colIndexOfPartitionPart D A = j := by
    apply D.colDiv.part_injective
    rw [colIndexOfPartitionPart_spec D hA, hAeq]
  rw [hCdef] at hc₁ hc₂
  have h₁ : colProfile (d := d) M D (colIndexOfPartitionPart D A) c₁ = b :=
    (Finset.mem_filter.mp hc₁).2
  have h₂ : colProfile (d := d) M D (colIndexOfPartitionPart D A) c₂ = b :=
    (Finset.mem_filter.mp hc₂).2
  simpa [hidx] using h₁.trans h₂.symm

/-- The Section 5.8 profile split makes every originally non-mixed zone
constant.  Horizontal zones are handled by the row profile; vertical zones are
handled by the column profile. -/
theorem profilePartition_nonmixed_zones_constant {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d) :
    ∀ ⦃R C⦄,
      R ∈ (profilePartition (d := d) M D).rowParts →
      C ∈ (profilePartition (d := d) M D).colParts →
      ∀ (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1)),
        R ⊆ D.rowDiv.part i → C ⊆ D.colDiv.part j →
          ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) →
            ZoneConstant M R C := by
  classical
  intro R C hR hC i j hRi hCj hnot
  rcases (not_zoneMixed_iff_vertical_or_horizontal M
      (D.rowDiv.part i) (D.colDiv.part j)).mp hnot with hv | hh
  · intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
    have hr₂i : r₂ ∈ D.rowDiv.part i := hRi hr₂
    have hc₁j : c₁ ∈ D.colDiv.part j := hCj hc₁
    have hc₂j : c₂ ∈ D.colDiv.part j := hCj hc₂
    have hcols :
        colProfile (d := d) M D j c₁ =
          colProfile (d := d) M D j c₂ :=
      colProfile_eq_of_mem_profilePartition_colPart_of_subset hC hCj hc₁ hc₂
    have hsame_col :
        M r₂ c₁ = M r₂ c₂ :=
      col_eq_on_vertical_zone_of_profile_eq hD i j hnot hv hc₁j hc₂j hcols hr₂i
    exact (hv (hRi hr₁) hr₂i hc₁j).trans hsame_col
  · intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
    have hr₁i : r₁ ∈ D.rowDiv.part i := hRi hr₁
    have hr₂i : r₂ ∈ D.rowDiv.part i := hRi hr₂
    have hc₁j : c₁ ∈ D.colDiv.part j := hCj hc₁
    have hc₂j : c₂ ∈ D.colDiv.part j := hCj hc₂
    have hrows :
        rowProfile (d := d) M D i r₁ =
          rowProfile (d := d) M D i r₂ :=
      rowProfile_eq_of_mem_profilePartition_rowPart_of_subset hR hRi hr₁ hr₂
    have hsame_row :
        M r₁ c₁ = M r₂ c₁ :=
      row_eq_on_horizontal_zone_of_profile_eq hD i j hnot hh hr₁i hr₂i hrows hc₁j
    exact hsame_row.trans (hh hr₂i hc₁j hc₂j)


/-- Error columns for a division partition are exactly the nonconstant column
indices, transported through the column-part embedding. -/
theorem rowErrorSet_toPartition {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1)) :
    rowErrorSet M D.toPartition (D.rowDiv.part i) =
      (MatrixDivision.nonconstantRowErrorSet M D i).map
        ⟨D.colDiv.part, D.colDiv.part_injective⟩ := by
  classical
  ext C
  simp [rowErrorSet, MatrixDivision.nonconstantRowErrorSet]
  constructor
  · rintro ⟨⟨j, rfl⟩, hnonconst⟩
    exact ⟨j, hnonconst, rfl⟩
  · rintro ⟨j, hnonconst, rfl⟩
    exact ⟨⟨j, rfl⟩, hnonconst⟩

/-- Error rows for a division partition are exactly the nonconstant row
indices, transported through the row-part embedding. -/
theorem colErrorSet_toPartition {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1)) :
    colErrorSet M D.toPartition (D.colDiv.part j) =
      (MatrixDivision.nonconstantColErrorSet M D j).map
        ⟨D.rowDiv.part, D.rowDiv.part_injective⟩ := by
  classical
  ext R
  simp [colErrorSet, MatrixDivision.nonconstantColErrorSet]
  constructor
  · rintro ⟨⟨i, rfl⟩, hnonconst⟩
    exact ⟨i, hnonconst, rfl⟩
  · rintro ⟨i, hnonconst, rfl⟩
    exact ⟨⟨i, rfl⟩, hnonconst⟩

/-- Bounded nonconstant division error gives bounded partition error for the
underlying matrix partition. -/
theorem errorValueAtMost_toPartition_of_nonconstantErrorValueAtMost {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MatrixDivision.NonconstantErrorValueAtMost M D d) :
    ErrorValueAtMost M D.toPartition d := by
  classical
  constructor
  · intro R hR
    rcases Finset.mem_map.mp hR with ⟨i, _hi, rfl⟩
    change (rowErrorSet M D.toPartition (D.rowDiv.part i)).card ≤ d
    rw [rowErrorSet_toPartition]
    simpa using hD.1 i
  · intro C hC
    rcases Finset.mem_map.mp hC with ⟨j, _hj, rfl⟩
    change (colErrorSet M D.toPartition (D.colDiv.part j)).card ≤ d
    rw [colErrorSet_toPartition]
    simpa using hD.2 j

/-- Bounded error for the unordered partition underlying a division is
equivalent to bounded nonconstant error for the division.  This direction is
used when a graph partition gives the same row and column parts as an ordered
matrix division. -/
theorem nonconstantErrorValueAtMost_of_errorValueAtMost_toPartition {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : ErrorValueAtMost M D.toPartition d) :
    MatrixDivision.NonconstantErrorValueAtMost M D d := by
  classical
  constructor
  · intro i
    have hrow :
        (rowErrorSet M D.toPartition (D.rowDiv.part i)).card ≤ d :=
      hD.1 (R := D.rowDiv.part i) (by simp [MatrixDivision.toPartition])
    rw [rowErrorSet_toPartition] at hrow
    simpa using hrow
  · intro j
    have hcol :
        (colErrorSet M D.toPartition (D.colDiv.part j)).card ≤ d :=
      hD.2 (C := D.colDiv.part j) (by simp [MatrixDivision.toPartition])
    rw [colErrorSet_toPartition] at hcol
    simpa using hcol

/-- A finest division induces a finest matrix partition. -/
theorem toPartition_isFinest {n m : ℕ}
    {D : MatrixDivision n m} (hD : IsFinest D) :
    MatrixPartition.IsFinest D.toPartition := by
  classical
  rcases hD with ⟨hrow, hcol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    rcases Finset.mem_map.mp hR with ⟨i, _hi, rfl⟩
    exact hrow i
  · intro r
    rcases D.rowDiv.part_cover r with ⟨i, hi⟩
    rcases hrow i with ⟨r', hr'⟩
    have hrr' : r = r' := by
      simpa [hr'] using hi
    subst r'
    exact by
      rw [← hr']
      simp
  · intro C hC
    rcases Finset.mem_map.mp hC with ⟨j, _hj, rfl⟩
    exact hcol j
  · intro c
    rcases D.colDiv.part_cover c with ⟨j, hj⟩
    rcases hcol j with ⟨c', hc'⟩
    have hcc' : c = c' := by
      simpa [hc'] using hj
    subst c'
    exact by
      rw [← hc']
      simp

/-- The profile refinement of a finest division is a finest matrix partition. -/
theorem profilePartition_isFinest_of_isFinest {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    {D : MatrixDivision n m} (hD : IsFinest D) :
    MatrixPartition.IsFinest (profilePartition (d := d) M D) := by
  have hrefine := profilePartition_rrefines_toPartition (d := d) M D
  exact MatrixPartition.isFinest_of_refines_isFinest
    ⟨hrefine.1.1, hrefine.2.1⟩ (toPartition_isFinest hD)

theorem colMixedZones_card_le_colMixedValue {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) :
    (colMixedZones M R C).card ≤ colMixedValue M R C := by
  unfold colMixedValue
  omega

theorem rowMixedZones_card_le_rowMixedValue {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) :
    (rowMixedZones M R C).card ≤ rowMixedValue M R C := by
  unfold rowMixedValue
  omega

/-- Counting lemma for Section 5.8.  If a refinement of a division makes every
originally non-mixed zone constant, then errors can only occur above originally
mixed zones.  Since each original part is split into at most `a` refined parts,
the error value is bounded by `d * a`. -/
theorem errorValueAtMost_of_rrefines_toPartition_of_nonmixed_zones_constant
    {n m d a : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    {P : MatrixPartition n m}
    (href : MatrixPartition.RRefines P D.toPartition a)
    (hD : MixedValueAtMost M D d)
    (hconst :
      ∀ ⦃R C⦄, R ∈ P.rowParts → C ∈ P.colParts →
        ∀ (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1)),
          R ⊆ D.rowDiv.part i → C ⊆ D.colDiv.part j →
            ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) →
              ZoneConstant M R C) :
    ErrorValueAtMost M P (d * a) := by
  classical
  constructor
  · intro R hR
    rcases href.1.1 hR with ⟨R₀, hR₀, hRR₀⟩
    rcases Finset.mem_map.mp hR₀ with ⟨i, _hi, hiR₀⟩
    change D.rowDiv.part i = R₀ at hiR₀
    subst R₀
    let mixedCols : Finset (Finset (Fin m)) :=
      (colMixedZones M (D.rowDiv.part i) D.colDiv).map
        ⟨D.colDiv.part, D.colDiv.part_injective⟩
    let overMixed : Finset (Finset (Fin m)) :=
      mixedCols.biUnion fun C₀ => P.colParts.filter fun C => C ⊆ C₀
    have hsubset : rowErrorSet M P R ⊆ overMixed := by
      intro C hC
      have hCdata : C ∈ P.colParts ∧ ¬ ZoneConstant M R C := by
        simpa [rowErrorSet] using hC
      rcases href.2.1 hCdata.1 with ⟨C₀, hC₀, hCC₀⟩
      rcases Finset.mem_map.mp hC₀ with ⟨j, _hj, hjC₀⟩
      change D.colDiv.part j = C₀ at hjC₀
      subst C₀
      have hmix : ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) := by
        by_contra hnot
        exact hCdata.2 (hconst hR hCdata.1 i j hRR₀ hCC₀ hnot)
      have hbad : D.colDiv.part j ∈ mixedCols := by
        simp [mixedCols, colMixedZones, hmix]
      exact Finset.mem_biUnion.mpr ⟨D.colDiv.part j, hbad, by
        simp [hCdata.1, hCC₀]⟩
    have hcard_over : overMixed.card ≤ mixedCols.card * a := by
      unfold overMixed
      refine Finset.card_biUnion_le_card_mul _ _ _ ?_
      intro C₀ hC₀
      have hC₀part : C₀ ∈ D.toPartition.colParts := by
        rcases (by
          have := hC₀
          simpa [mixedCols] using this :
            ∃ j ∈ colMixedZones M (D.rowDiv.part i) D.colDiv,
              D.colDiv.part j = C₀) with ⟨j, _hj, rfl⟩
        simp [toPartition]
      exact href.2.2 hC₀part
    have hmixedCols :
        mixedCols.card ≤ d := by
      calc
        mixedCols.card = (colMixedZones M (D.rowDiv.part i) D.colDiv).card := by
          simp [mixedCols]
        _ ≤ colMixedValue M (D.rowDiv.part i) D.colDiv :=
          colMixedZones_card_le_colMixedValue M (D.rowDiv.part i) D.colDiv
        _ ≤ d := hD.2 i
    calc
      (rowErrorSet M P R).card ≤ overMixed.card := Finset.card_le_card hsubset
      _ ≤ mixedCols.card * a := hcard_over
      _ ≤ d * a := Nat.mul_le_mul_right a hmixedCols
  · intro C hC
    rcases href.2.1 hC with ⟨C₀, hC₀, hCC₀⟩
    rcases Finset.mem_map.mp hC₀ with ⟨j, _hj, hjC₀⟩
    change D.colDiv.part j = C₀ at hjC₀
    subst C₀
    let mixedRows : Finset (Finset (Fin n)) :=
      (rowMixedZones M D.rowDiv (D.colDiv.part j)).map
        ⟨D.rowDiv.part, D.rowDiv.part_injective⟩
    let overMixed : Finset (Finset (Fin n)) :=
      mixedRows.biUnion fun R₀ => P.rowParts.filter fun R => R ⊆ R₀
    have hsubset : colErrorSet M P C ⊆ overMixed := by
      intro R hR
      have hRdata : R ∈ P.rowParts ∧ ¬ ZoneConstant M R C := by
        simpa [colErrorSet] using hR
      rcases href.1.1 hRdata.1 with ⟨R₀, hR₀, hRR₀⟩
      rcases Finset.mem_map.mp hR₀ with ⟨i, _hi, hiR₀⟩
      change D.rowDiv.part i = R₀ at hiR₀
      subst R₀
      have hmix : ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) := by
        by_contra hnot
        exact hRdata.2 (hconst hRdata.1 hC i j hRR₀ hCC₀ hnot)
      have hbad : D.rowDiv.part i ∈ mixedRows := by
        simp [mixedRows, rowMixedZones, hmix]
      exact Finset.mem_biUnion.mpr ⟨D.rowDiv.part i, hbad, by
        simp [hRdata.1, hRR₀]⟩
    have hcard_over : overMixed.card ≤ mixedRows.card * a := by
      unfold overMixed
      refine Finset.card_biUnion_le_card_mul _ _ _ ?_
      intro R₀ hR₀
      have hR₀part : R₀ ∈ D.toPartition.rowParts := by
        rcases (by
          have := hR₀
          simpa [mixedRows] using this :
            ∃ i ∈ rowMixedZones M D.rowDiv (D.colDiv.part j),
              D.rowDiv.part i = R₀) with ⟨i, _hi, rfl⟩
        simp [toPartition]
      exact href.1.2 hR₀part
    have hmixedRows :
        mixedRows.card ≤ d := by
      calc
        mixedRows.card = (rowMixedZones M D.rowDiv (D.colDiv.part j)).card := by
          simp [mixedRows]
        _ ≤ rowMixedValue M D.rowDiv (D.colDiv.part j) :=
          rowMixedZones_card_le_rowMixedValue M D.rowDiv (D.colDiv.part j)
        _ ≤ d := hD.1 j
    calc
      (colErrorSet M P C).card ≤ overMixed.card := Finset.card_le_card hsubset
      _ ≤ mixedRows.card * a := hcard_over
      _ ≤ d * a := Nat.mul_le_mul_right a hmixedRows

/-- Profile-partition error bound, reduced to the local profile-correctness
property that every originally non-mixed zone becomes constant after the row
and column profile splits. -/
theorem errorValueAtMost_profilePartition_of_nonmixed_zones_constant
    {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (hconst :
      ∀ ⦃R C⦄,
        R ∈ (profilePartition (d := d) M D).rowParts →
        C ∈ (profilePartition (d := d) M D).colParts →
        ∀ (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1)),
          R ⊆ D.rowDiv.part i → C ⊆ D.colDiv.part j →
            ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) →
              ZoneConstant M R C) :
    ErrorValueAtMost M (profilePartition (d := d) M D)
      (d * Fintype.card α ^ (d + 1)) :=
  errorValueAtMost_of_rrefines_toPartition_of_nonmixed_zones_constant
    (profilePartition_rrefines_toPartition (d := d) M D) hD hconst

/-- The profile partition associated to a division of mixed value at most `d`
has nonconstant error value at most `d * |α|^(d+1)`. -/
theorem errorValueAtMost_profilePartition {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d) :
    ErrorValueAtMost M (profilePartition (d := d) M D)
      (d * Fintype.card α ^ (d + 1)) :=
  errorValueAtMost_profilePartition_of_nonmixed_zones_constant hD
    (profilePartition_nonmixed_zones_constant hD)

/-- A coarsest division induces a coarsest matrix partition. -/
theorem toPartition_isCoarsest {n m : ℕ}
    {D : MatrixDivision n m} (hD : IsCoarsest D) :
    MatrixPartition.IsCoarsest D.toPartition := by
  rcases hD with ⟨hrow, hcol⟩
  constructor <;> simp [hrow, hcol]

/-- Exact row fusion of consecutive divisions is a row contraction of the
underlying matrix partitions. -/
theorem isRowContraction_toPartition_of_hasRowFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasRowFusion D E) :
    MatrixPartition.IsRowContraction D.toPartition E.toPartition := by
  classical
  rcases hDE with ⟨hrow, hcol, i, hfusion, hcols⟩
  let Rcast : Division n (E.rowCuts + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = E.rowCuts + 2) D.rowDiv
  let Ccast : Division m (E.colCuts + 1) :=
    Division.castIndex (by omega : D.colCuts + 1 = E.colCuts + 1) D.colDiv
  let A : Finset (Fin n) := Rcast.part i.castSucc
  let B : Finset (Fin n) := Rcast.part i.succ
  refine ⟨A, ?_, B, ?_, ?_, ?_, ?_⟩
  · simp [A, Rcast, toPartition, Division.castIndex]
  · simp [B, Rcast, toPartition, Division.castIndex]
  · intro hAB
    have hidx := Rcast.part_injective hAB
    have hv := congrArg Fin.val hidx
    simp at hv
  · have hparts := Division.parts_eq_insert_erase_of_isFusionAt hfusion
    have hrow' : D.rowCuts + 1 = E.rowCuts + 2 := by omega
    have hcastParts :
        ((Finset.univ : Finset (Fin (E.rowCuts + 2))).map
            ⟨Rcast.part, Rcast.part_injective⟩) =
          ((Finset.univ : Finset (Fin (D.rowCuts + 1))).map
            ⟨D.rowDiv.part, D.rowDiv.part_injective⟩) := by
      simp [Rcast]
    rw [hcastParts] at hparts
    simpa [A, B, Rcast, toPartition, Division.castIndex] using hparts
  · ext C
    constructor
    · intro hC
      rcases Finset.mem_map.mp hC with ⟨j, _hj, hjC⟩
      change E.colDiv.part j = C at hjC
      rw [← hjC, hcols j]
      simp [toPartition, Division.castIndex]
    · intro hC
      rcases Finset.mem_map.mp hC with ⟨j, _hj, hjC⟩
      change D.colDiv.part j = C at hjC
      rw [← hjC]
      refine Finset.mem_map.mpr ⟨finCongr (by omega : D.colCuts + 1 = E.colCuts + 1) j,
        Finset.mem_univ _, ?_⟩
      change E.colDiv.part (finCongr (by omega : D.colCuts + 1 = E.colCuts + 1) j) =
        D.colDiv.part j
      rw [hcols]
      simp [Division.castIndex]

/-- Exact column fusion of consecutive divisions is a column contraction of the
underlying matrix partitions. -/
theorem isColContraction_toPartition_of_hasColFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasColFusion D E) :
    MatrixPartition.IsColContraction D.toPartition E.toPartition := by
  classical
  rcases hDE with ⟨hrow, hcol, j, hrows, hfusion⟩
  let Rcast : Division n (E.rowCuts + 1) :=
    Division.castIndex (by omega : D.rowCuts + 1 = E.rowCuts + 1) D.rowDiv
  let Ccast : Division m (E.colCuts + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = E.colCuts + 2) D.colDiv
  let A : Finset (Fin m) := Ccast.part j.castSucc
  let B : Finset (Fin m) := Ccast.part j.succ
  refine ⟨A, ?_, B, ?_, ?_, ?_, ?_⟩
  · simp [A, Ccast, toPartition, Division.castIndex]
  · simp [B, Ccast, toPartition, Division.castIndex]
  · intro hAB
    have hidx := Ccast.part_injective hAB
    have hv := congrArg Fin.val hidx
    simp at hv
  · have hparts := Division.parts_eq_insert_erase_of_isFusionAt hfusion
    have hcol' : D.colCuts + 1 = E.colCuts + 2 := by omega
    have hcastParts :
        ((Finset.univ : Finset (Fin (E.colCuts + 2))).map
            ⟨Ccast.part, Ccast.part_injective⟩) =
          ((Finset.univ : Finset (Fin (D.colCuts + 1))).map
            ⟨D.colDiv.part, D.colDiv.part_injective⟩) := by
      simp [Ccast]
    rw [hcastParts] at hparts
    simpa [A, B, Ccast, toPartition, Division.castIndex] using hparts
  · ext R
    constructor
    · intro hR
      rcases Finset.mem_map.mp hR with ⟨i, _hi, hiR⟩
      change E.rowDiv.part i = R at hiR
      rw [← hiR, hrows i]
      simp [toPartition, Division.castIndex]
    · intro hR
      rcases Finset.mem_map.mp hR with ⟨i, _hi, hiR⟩
      change D.rowDiv.part i = R at hiR
      rw [← hiR]
      refine Finset.mem_map.mpr ⟨finCongr (by omega : D.rowCuts + 1 = E.rowCuts + 1) i,
        Finset.mem_univ _, ?_⟩
      change E.rowDiv.part (finCongr (by omega : D.rowCuts + 1 = E.rowCuts + 1) i) =
        D.rowDiv.part i
      rw [hrows]
      simp [Division.castIndex]

/-- Exact fusion of consecutive divisions is a matrix-partition contraction. -/
theorem isContraction_toPartition_of_hasExactFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasExactFusion D E) :
    MatrixPartition.IsContraction D.toPartition E.toPartition := by
  rcases hDE with hrow | hcol
  · exact Or.inl (isRowContraction_toPartition_of_hasRowFusion hrow)
  · exact Or.inr (isColContraction_toPartition_of_hasColFusion hcol)

/-- Exact row fusion gives `2`-bounded refinement of the underlying matrix
partitions. -/
theorem rrefines_toPartition_of_hasRowFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasRowFusion D E) :
    MatrixPartition.RRefines D.toPartition E.toPartition 2 := by
  classical
  rcases isRowContraction_toPartition_of_hasRowFusion hDE with
    ⟨R, hR, S, hS, hRS, hrow, hcol⟩
  have hEq :
      E.toPartition = D.toPartition.rowContract hR hS hRS := by
    apply MatrixPartition.ext_parts
    · simpa [MatrixPartition.rowParts_rowContract] using hrow
    · simpa [MatrixPartition.colParts_rowContract] using hcol
  rw [hEq]
  exact MatrixPartition.rrefines_rowContract_self D.toPartition hR hS hRS

/-- Exact column fusion gives `2`-bounded refinement of the underlying matrix
partitions. -/
theorem rrefines_toPartition_of_hasColFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasColFusion D E) :
    MatrixPartition.RRefines D.toPartition E.toPartition 2 := by
  classical
  rcases isColContraction_toPartition_of_hasColFusion hDE with
    ⟨C, hC, F, hF, hCF, hcol, hrow⟩
  have hEq :
      E.toPartition = D.toPartition.colContract hC hF hCF := by
    apply MatrixPartition.ext_parts
    · simpa [MatrixPartition.rowParts_colContract] using hrow
    · simpa [MatrixPartition.colParts_colContract] using hcol
  rw [hEq]
  exact MatrixPartition.rrefines_colContract_self D.toPartition hC hF hCF

/-- Exact fusion gives `2`-bounded refinement of the underlying matrix
partitions. -/
theorem rrefines_toPartition_of_hasExactFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasExactFusion D E) :
    MatrixPartition.RRefines D.toPartition E.toPartition 2 := by
  rcases hDE with hrow | hcol
  · exact rrefines_toPartition_of_hasRowFusion hrow
  · exact rrefines_toPartition_of_hasColFusion hcol

/-- If profiles are monotone across an exact fusion, the corresponding profile
partitions have the bounded-refinement factor from Section 5.8. -/
theorem rrefines_profilePartition_of_hasExactFusion_of_profile_mono
    {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDE : HasExactFusion D E)
    (hrow :
      ∀ ⦃A B x y⦄, A ∈ D.toPartition.rowParts → B ∈ E.toPartition.rowParts →
        A ⊆ B → x ∈ A → y ∈ A →
          rowProfile (d := d) M D (rowIndexOfPartitionPart D A) x =
            rowProfile (d := d) M D (rowIndexOfPartitionPart D A) y →
          rowProfile (d := d) M E (rowIndexOfPartitionPart E B) x =
            rowProfile (d := d) M E (rowIndexOfPartitionPart E B) y)
    (hcol :
      ∀ ⦃A B x y⦄, A ∈ D.toPartition.colParts → B ∈ E.toPartition.colParts →
        A ⊆ B → x ∈ A → y ∈ A →
          colProfile (d := d) M D (colIndexOfPartitionPart D A) x =
            colProfile (d := d) M D (colIndexOfPartitionPart D A) y →
            colProfile (d := d) M E (colIndexOfPartitionPart E B) x =
            colProfile (d := d) M E (colIndexOfPartitionPart E B) y) :
    MatrixPartition.RRefines (profilePartition (d := d) M D)
      (profilePartition (d := d) M E) (2 * Fintype.card α ^ (d + 1)) := by
  classical
  have hbase := rrefines_toPartition_of_hasExactFusion hDE
  constructor
  · simpa [profilePartition, AlphabetProfile] using
      MatrixPartition.partsRRefine_splitPartsByLabel_of_partsRRefine
        (Q := E.toPartition.rowParts)
        (P := D.toPartition.rowParts)
        (pLabel := fun R r =>
          rowProfile (d := d) M D (rowIndexOfPartitionPart D R) r)
        (qLabel := fun R r =>
          rowProfile (d := d) M E (rowIndexOfPartitionPart E R) r)
        E.toPartition.row_disjoint hbase.1 hrow
  · simpa [profilePartition, AlphabetProfile] using
      MatrixPartition.partsRRefine_splitPartsByLabel_of_partsRRefine
        (Q := E.toPartition.colParts)
        (P := D.toPartition.colParts)
        (pLabel := fun C c =>
          colProfile (d := d) M D (colIndexOfPartitionPart D C) c)
        (qLabel := fun C c =>
          colProfile (d := d) M E (colIndexOfPartitionPart E C) c)
        E.toPartition.col_disjoint hbase.2 hcol

/-- Row profiles are monotone under an exact fusion: two rows in an old row
part that had the same old profile also have the same profile in the coarser
row part containing them. -/
theorem rowProfile_mono_of_hasExactFusion {n m d : ℕ}
    [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDmix : MixedValueAtMost M D d)
    (hDE : HasExactFusion D E) :
    ∀ ⦃A B x y⦄, A ∈ D.toPartition.rowParts → B ∈ E.toPartition.rowParts →
      A ⊆ B → x ∈ A → y ∈ A →
        rowProfile (d := d) M D (rowIndexOfPartitionPart D A) x =
          rowProfile (d := d) M D (rowIndexOfPartitionPart D A) y →
        rowProfile (d := d) M E (rowIndexOfPartitionPart E B) x =
          rowProfile (d := d) M E (rowIndexOfPartitionPart E B) y := by
  classical
  intro A B x y hA hB hAB hxA hyA hxy
  funext q
  by_cases hcan :
      (rowProfileCandidates (d := d) M E (rowIndexOfPartitionPart E B) q).Nonempty
  · simp [rowProfile, hcan]
    let iE := rowIndexOfPartitionPart E B
    let candidates := rowProfileCandidates (d := d) M E iE q
    let rep := candidates.min' hcan
    have hrep_mem : rep ∈ candidates := Finset.min'_mem candidates hcan
    have hrep_data :
        ¬ ZoneMixed M (E.rowDiv.part iE) (E.colDiv.part rep) ∧
          colBadBefore M E iE rep = q.1 := by
      simpa [candidates] using
        (mem_rowProfileCandidates M E iE q rep).mp hrep_mem
    let c : Fin m := E.colDiv.first rep
    have hcE : c ∈ E.colDiv.part rep := E.colDiv.first_mem rep
    rcases D.colDiv.part_cover c with ⟨jD, hcD⟩
    have hDcol : D.colDiv.part jD ∈ D.toPartition.colParts := by
      simp [toPartition]
    have hbase := rrefines_toPartition_of_hasExactFusion hDE
    rcases hbase.2.1 hDcol with ⟨CE, hCE, hsubCE⟩
    have hCEeq : CE = E.colDiv.part rep := by
      have hcCE : c ∈ CE := hsubCE hcD
      rcases Finset.mem_map.mp hCE with ⟨jE, _hjE, hjE⟩
      change E.colDiv.part jE = CE at hjE
      rw [← hjE] at hcCE
      by_contra hne
      have hidxne : jE ≠ rep := by
        intro h
        apply hne
        rw [← hjE, h]
      exact Finset.disjoint_left.mp (E.colDiv.part_disjoint hidxne) hcCE hcE
    have hsubCol : D.colDiv.part jD ⊆ E.colDiv.part rep := by
      simpa [hCEeq] using hsubCE
    let iD := rowIndexOfPartitionPart D A
    have hAeq : D.rowDiv.part iD = A := rowIndexOfPartitionPart_spec D hA
    have hBeq : E.rowDiv.part iE = B := rowIndexOfPartitionPart_spec E hB
    have hnot_old :
        ¬ ZoneMixed M (D.rowDiv.part iD) (D.colDiv.part jD) := by
      intro hmix_old
      have hbig : ZoneMixed M (E.rowDiv.part iE) (E.colDiv.part rep) := by
        apply zoneMixed_of_subset _ _ hmix_old
        · intro r hr
          simpa [hBeq] using hAB (by simpa [hAeq] using hr)
        · exact hsubCol
      exact hrep_data.1 hbig
    have hxD : x ∈ D.rowDiv.part iD := by simpa [hAeq] using hxA
    have hyD : y ∈ D.rowDiv.part iD := by simpa [hAeq] using hyA
    rcases (not_zoneMixed_iff_vertical_or_horizontal M
        (D.rowDiv.part iD) (D.colDiv.part jD)).mp hnot_old with hv | hh
    · exact hv hxD hyD hcD
    · exact row_eq_on_horizontal_zone_of_profile_eq
        hDmix iD jD hnot_old hh hxD hyD hxy hcD
  · simp [rowProfile, hcan]

/-- Column-profile analogue of `rowProfile_mono_of_hasExactFusion`. -/
theorem colProfile_mono_of_hasExactFusion {n m d : ℕ}
    [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDmix : MixedValueAtMost M D d)
    (hDE : HasExactFusion D E) :
    ∀ ⦃A B x y⦄, A ∈ D.toPartition.colParts → B ∈ E.toPartition.colParts →
      A ⊆ B → x ∈ A → y ∈ A →
        colProfile (d := d) M D (colIndexOfPartitionPart D A) x =
          colProfile (d := d) M D (colIndexOfPartitionPart D A) y →
        colProfile (d := d) M E (colIndexOfPartitionPart E B) x =
          colProfile (d := d) M E (colIndexOfPartitionPart E B) y := by
  classical
  intro A B x y hA hB hAB hxA hyA hxy
  funext q
  by_cases hcan :
      (colProfileCandidates (d := d) M E (colIndexOfPartitionPart E B) q).Nonempty
  · simp [colProfile, hcan]
    let jE := colIndexOfPartitionPart E B
    let candidates := colProfileCandidates (d := d) M E jE q
    let rep := candidates.min' hcan
    have hrep_mem : rep ∈ candidates := Finset.min'_mem candidates hcan
    have hrep_data :
        ¬ ZoneMixed M (E.rowDiv.part rep) (E.colDiv.part jE) ∧
          rowBadBefore M E jE rep = q.1 := by
      simpa [candidates] using
        (mem_colProfileCandidates M E jE q rep).mp hrep_mem
    let r : Fin n := E.rowDiv.first rep
    have hrE : r ∈ E.rowDiv.part rep := E.rowDiv.first_mem rep
    rcases D.rowDiv.part_cover r with ⟨iD, hrD⟩
    have hDrow : D.rowDiv.part iD ∈ D.toPartition.rowParts := by
      simp [toPartition]
    have hbase := rrefines_toPartition_of_hasExactFusion hDE
    rcases hbase.1.1 hDrow with ⟨RE, hRE, hsubRE⟩
    have hREeq : RE = E.rowDiv.part rep := by
      have hrRE : r ∈ RE := hsubRE hrD
      rcases Finset.mem_map.mp hRE with ⟨iE, _hiE, hiE⟩
      change E.rowDiv.part iE = RE at hiE
      rw [← hiE] at hrRE
      by_contra hne
      have hidxne : iE ≠ rep := by
        intro h
        apply hne
        rw [← hiE, h]
      exact Finset.disjoint_left.mp (E.rowDiv.part_disjoint hidxne) hrRE hrE
    have hsubRow : D.rowDiv.part iD ⊆ E.rowDiv.part rep := by
      simpa [hREeq] using hsubRE
    let jD := colIndexOfPartitionPart D A
    have hAeq : D.colDiv.part jD = A := colIndexOfPartitionPart_spec D hA
    have hBeq : E.colDiv.part jE = B := colIndexOfPartitionPart_spec E hB
    have hnot_old :
        ¬ ZoneMixed M (D.rowDiv.part iD) (D.colDiv.part jD) := by
      intro hmix_old
      have hbig : ZoneMixed M (E.rowDiv.part rep) (E.colDiv.part jE) := by
        apply zoneMixed_of_subset _ _ hmix_old
        · exact hsubRow
        · intro c hc
          simpa [hBeq] using hAB (by simpa [hAeq] using hc)
      exact hrep_data.1 hbig
    have hxD : x ∈ D.colDiv.part jD := by simpa [hAeq] using hxA
    have hyD : y ∈ D.colDiv.part jD := by simpa [hAeq] using hyA
    rcases (not_zoneMixed_iff_vertical_or_horizontal M
        (D.rowDiv.part iD) (D.colDiv.part jD)).mp hnot_old with hv | hh
    · exact col_eq_on_vertical_zone_of_profile_eq
        hDmix iD jD hnot_old hv hxD hyD hxy hrD
    · exact hh hrD hxD hyD
  · simp [colProfile, hcan]

/-- Consecutive profile partitions in a bounded mixed-value division sequence
have the bounded-refinement factor from Section 5.8. -/
theorem rrefines_profilePartition_of_hasExactFusion {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDmix : MixedValueAtMost M D d)
    (hDE : HasExactFusion D E) :
    MatrixPartition.RRefines (profilePartition (d := d) M D)
      (profilePartition (d := d) M E) (2 * Fintype.card α ^ (d + 1)) :=
  rrefines_profilePartition_of_hasExactFusion_of_profile_mono hDE
    (rowProfile_mono_of_hasExactFusion hDmix hDE)
    (colProfile_mono_of_hasExactFusion hDmix hDE)

end MatrixDivision

/-- A bounded nonconstant-error division sequence induces a matrix contraction
sequence with the same error bound. -/
noncomputable def matrixContractionSequence_of_boundedErrorValueDivisionSequence {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (S : BoundedErrorValueDivisionSequence M d) :
    MatrixContractionSequence M d where
  stepCount := S.stepCount
  partition := fun s => (S.division s).toPartition
  starts := MatrixDivision.toPartition_isFinest S.starts
  ends := MatrixDivision.toPartition_isCoarsest S.ends
  step_contracts := by
    intro s hs
    exact MatrixDivision.isContraction_toPartition_of_hasExactFusion (S.step_fuses s hs)
  errorValue_le := by
    intro s hs
    exact MatrixDivision.errorValueAtMost_toPartition_of_nonconstantErrorValueAtMost
      (S.errorValue_le s hs)

/-- Theorem 10 bridge in predicate form. -/
theorem matrixTwinWidthAtMost_of_boundedErrorValueDivisionSequence {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (S : Nonempty (BoundedErrorValueDivisionSequence M d)) :
    MatrixTwinWidthAtMost M d := by
  rcases S with ⟨S⟩
  exact ⟨matrixContractionSequence_of_boundedErrorValueDivisionSequence S⟩

/-- A coarsest matrix partition has error value at most one. -/
theorem errorValueAtMost_one_of_isCoarsest {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    {P : MatrixPartition n m}
    (hP : MatrixPartition.IsCoarsest P) :
    ErrorValueAtMost M P 1 := by
  classical
  constructor
  · intro R hR
    calc
      (rowErrorSet M P R).card ≤ P.colParts.card := by
        unfold rowErrorSet
        exact Finset.card_filter_le _ _
      _ ≤ 1 := hP.2
  · intro C hC
    calc
      (colErrorSet M P C).card ≤ P.rowParts.card := by
        unfold colErrorSet
        exact Finset.card_filter_le _ _
      _ ≤ 1 := hP.1

/-- Section 5.8 bridge: a positive mixed-value division sequence yields a
bounded-error bounded-refinement partition sequence with finite-alphabet
profile parameters. -/
noncomputable def boundedErrorRefinementPartitionSequence_of_boundedMixedValue
    {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hd : 0 < d)
    (S : BoundedMixedValueDivisionSequence M d) :
    BoundedErrorRefinementPartitionSequence M
      (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1)) where
  stepCount := S.stepCount + 1
  partition := fun s =>
    if h : s ≤ S.stepCount then
      MatrixDivision.profilePartition (d := d) M (S.division s)
    else
      (S.division S.stepCount).toPartition
  starts := by
    simp [MatrixDivision.profilePartition_isFinest_of_isFinest M S.starts]
  ends := by
    have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
    simp [hnot, MatrixDivision.toPartition_isCoarsest S.ends]
  step_rrefines := by
    intro i hi
    by_cases hlast : i = S.stepCount
    · subst i
      have hcur : S.stepCount ≤ S.stepCount := le_rfl
      have hnext : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
      simp [hnext]
      exact MatrixPartition.rrefines_mono
        (by
          calc
            Fintype.card α ^ (d + 1) =
                1 * Fintype.card α ^ (d + 1) := by simp
            _ ≤ 2 * Fintype.card α ^ (d + 1) :=
              Nat.mul_le_mul_right _ (by decide : 1 ≤ 2))
        (MatrixDivision.profilePartition_rrefines_toPartition
          (d := d) M (S.division S.stepCount))
    · have hiS : i < S.stepCount := by omega
      have hcur : i ≤ S.stepCount := by omega
      have hnext : i + 1 ≤ S.stepCount := by omega
      simp [hcur, hnext]
      exact MatrixDivision.rrefines_profilePartition_of_hasExactFusion
        (S.mixedValue_le i hcur) (S.step_fuses i hiS)
  errorValue_le := by
    intro i hi
    by_cases hcur : i ≤ S.stepCount
    · simp [hcur]
      exact MatrixDivision.errorValueAtMost_profilePartition
        (S.mixedValue_le i hcur)
    · have hi_last : i = S.stepCount + 1 := by omega
      subst i
      have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
      simp [hnot]
      have hone :
          ErrorValueAtMost M (S.division S.stepCount).toPartition 1 :=
        errorValueAtMost_one_of_isCoarsest M
          (MatrixDivision.toPartition_isCoarsest S.ends)
      have hle : 1 ≤ d * Fintype.card α ^ (d + 1) := by
        have hαpos : 0 < Fintype.card α := Fintype.card_pos
        have hpos : 0 < d * Fintype.card α ^ (d + 1) :=
          Nat.mul_pos hd (pow_pos hαpos _)
        exact hpos
      exact MatrixPartition.errorValueAtMost_mono hle hone

theorem exists_boundedErrorRefinementPartitionSequence_of_boundedMixedValue
    {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hd : 0 < d)
    (S : Nonempty (BoundedMixedValueDivisionSequence M d)) :
    Nonempty (BoundedErrorRefinementPartitionSequence M
      (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1))) := by
  rcases S with ⟨S⟩
  exact ⟨boundedErrorRefinementPartitionSequence_of_boundedMixedValue hd S⟩

/-- The second item of Theorem 10 in the division-sequence form proved by the
current matrix development: a positive-size matrix has a bounded mixed-value
fusion sequence, with the bound depending only on its mixed number. -/
theorem theorem10_second_item_mixedValue
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      (M : _root_.Matrix (Fin n) (Fin m) α) →
        Nonempty (BoundedMixedValueDivisionSequence M
          (theorem10MixedValueBound c (matrixMixedNumber M))) := by
  intro n m hn hm M
  exact boundedMixedValueDivisionSequenceTheorem hMT hn hm M
    (matrixMixedNumber M + 1)
    (not_hasMixedMinor_succ_matrixMixedNumber M)

/-- A noncomputable choice of Marcus--Tardos constants from the abstract
Marcus--Tardos theorem. -/
noncomputable def marcusTardosConstantOfTheorem
    (hMT : MarcusTardosTheorem) (t : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (hMT t)

/-- The chosen constants satisfy the Marcus--Tardos density property. -/
theorem isMarcusTardosConstant_marcusTardosConstantOfTheorem
    (hMT : MarcusTardosTheorem) :
    ∀ t : ℕ, IsMarcusTardosConstant t (marcusTardosConstantOfTheorem hMT t) := by
  classical
  intro t
  exact Nat.find_spec (hMT t)

/-- Theorem 10's second item using a bundled proof of Marcus--Tardos. -/
theorem theorem10_second_item_mixedValue_of_marcusTardos
    (hMT : MarcusTardosTheorem) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      (M : _root_.Matrix (Fin n) (Fin m) α) →
        Nonempty (BoundedMixedValueDivisionSequence M
          (theorem10MixedValueBound
            (marcusTardosConstantOfTheorem hMT) (matrixMixedNumber M))) :=
  theorem10_second_item_mixedValue
    (isMarcusTardosConstant_marcusTardosConstantOfTheorem hMT)

/-- The final, unconditional division-sequence form of the second item of
Theorem 10 for positive-size matrices. -/
theorem theorem10_mixedValue :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      (M : _root_.Matrix (Fin n) (Fin m) α) →
        Nonempty (BoundedMixedValueDivisionSequence M
          (theorem10MixedValueBound marcusTardosConstant (matrixMixedNumber M))) :=
  theorem10_second_item_mixedValue isMarcusTardosConstant_marcusTardosConstant

theorem theorem10MixedValueBound_pos (k : ℕ) :
    0 < theorem10MixedValueBound marcusTardosConstant k := by
  unfold theorem10MixedValueBound lemma13MixedValueBound
  exact Nat.mul_pos (by decide : 0 < 20)
    (IsMarcusTardosConstant.pos
      (isMarcusTardosConstant_marcusTardosConstant (k + 1))
      (Nat.succ_pos k))

/-- The remaining bridge needed for the full second item of Theorem 10,
expressed as a precise hypothesis.

Once a bounded mixed-value division sequence is refined into a bounded-error
partition sequence with the finite-alphabet profile parameters, the proved
Lemma 13 machinery and the proved Lemma 8 expansion give the advertised matrix
twin-width bound. -/
theorem theorem10_matrixTwinWidthAtMost_of_mixedValue_refinement
    [Fintype α] [DecidableEq α] [Inhabited α]
    (hrefine :
      ∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
        Nonempty (BoundedMixedValueDivisionSequence M d) →
          Nonempty (BoundedErrorRefinementPartitionSequence M
            (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1)))) :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinWidthAtMost M
        (theorem10AlphabetMatrixTwinWidthBound (Fintype.card α) (matrixMixedNumber M)) := by
  intro n m M
  by_cases hn : n = 0
  · subst n
    exact matrixTwinWidthAtMost_zeroRows M
  · by_cases hm : m = 0
    · subst m
      exact matrixTwinWidthAtMost_zeroCols M
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let d : ℕ := theorem10MixedValueBound marcusTardosConstant (matrixMixedNumber M)
      have hmixed : Nonempty (BoundedMixedValueDivisionSequence M d) := by
        simpa [d] using theorem10_mixedValue hnpos hmpos M
      have hrefined : Nonempty (BoundedErrorRefinementPartitionSequence M
          (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1))) :=
        hrefine M hmixed
      have hαpos : 0 < Fintype.card α := Fintype.card_pos
      have htww :
          MatrixTwinWidthAtMost M
            (theorem10AlphabetErrorRefinementBound (Fintype.card α) d) :=
        matrixTwinWidthAtMost_of_theorem10ErrorRefinementSequence
          (a := Fintype.card α) hαpos hrefined
      simpa [theorem10AlphabetMatrixTwinWidthBound, d] using htww

/-- The completed second item of matrix Theorem 10 over a nonempty finite
alphabet: matrix twin-width is bounded by the explicit Theorem 10 function of
the alphabet size and matrix mixed number. -/
theorem theorem10_matrixTwinWidthAtMost
    [Fintype α] [DecidableEq α] [Inhabited α] :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinWidthAtMost M
        (theorem10AlphabetMatrixTwinWidthBound (Fintype.card α) (matrixMixedNumber M)) := by
  intro n m M
  by_cases hn : n = 0
  · subst n
    exact matrixTwinWidthAtMost_zeroRows M
  · by_cases hm : m = 0
    · subst m
      exact matrixTwinWidthAtMost_zeroCols M
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let d : ℕ := theorem10MixedValueBound marcusTardosConstant (matrixMixedNumber M)
      have hmixed : Nonempty (BoundedMixedValueDivisionSequence M d) := by
        simpa [d] using theorem10_mixedValue hnpos hmpos M
      have hrefined : Nonempty (BoundedErrorRefinementPartitionSequence M
          (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1))) :=
        exists_boundedErrorRefinementPartitionSequence_of_boundedMixedValue
          (by simpa [d] using theorem10MixedValueBound_pos (matrixMixedNumber M))
          hmixed
      have hαpos : 0 < Fintype.card α := Fintype.card_pos
      have htww :
          MatrixTwinWidthAtMost M
            (theorem10AlphabetErrorRefinementBound (Fintype.card α) d) :=
        matrixTwinWidthAtMost_of_theorem10ErrorRefinementSequence
          (a := Fintype.card α) hαpos hrefined
      simpa [theorem10AlphabetMatrixTwinWidthBound, d] using htww

/-- Boolean specialization of the completed second item of matrix Theorem 10. -/
theorem theorem10_bool_matrixTwinWidthAtMost :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
      MatrixTwinWidthAtMost M (theorem10MatrixTwinWidthBound (matrixMixedNumber M)) := by
  intro n m M
  simpa [theorem10MatrixTwinWidthBound, theorem10AlphabetMatrixTwinWidthBound]
    using theorem10_matrixTwinWidthAtMost (α := Bool) M

/-- Matrix Theorem 10 in the public contract shape: bounded matrix
twin-orderedness bounds mixed number, and matrix mixed number bounds matrix
twin-width via the explicit Section 5.8 function. -/
theorem theorem10_matrix_mixed_number_and_matrix_twin_width_bound_each_other
    [Fintype α] [DecidableEq α] [Inhabited α] :
    (∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ 2 * d + 2) ∧
    (∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinWidthAtMost M
        (theorem10AlphabetMatrixTwinWidthBound (Fintype.card α) (matrixMixedNumber M))) := by
  constructor
  · intro n m d M hM
    simpa [theorem10MatrixMixedNumberBound] using
      theorem10_first_item_ordered (n := n) (m := m) (d := d) M hM
  · intro n m M
    exact theorem10_matrixTwinWidthAtMost M

/-- Boolean-alphabet specialization of the public contract shape retained for
graph adjacency matrices. -/
theorem theorem10_bool_matrix_mixed_number_and_matrix_twin_width_bound_each_other :
    (∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
      MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ 2 * d + 2) ∧
    (∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
      MatrixTwinWidthAtMost M (theorem10MatrixTwinWidthBound (matrixMixedNumber M))) := by
  constructor
  · intro n m d M hM
    exact (theorem10_matrix_mixed_number_and_matrix_twin_width_bound_each_other
      (α := Bool)).1 M hM
  · exact theorem10_bool_matrixTwinWidthAtMost

end Matrix
end Lax2Proofs.TwinWidth
