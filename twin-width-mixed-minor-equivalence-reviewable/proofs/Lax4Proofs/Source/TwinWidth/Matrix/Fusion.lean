import Lax4Proofs.Source.TwinWidth.Matrix.Corner

/-!
# Fusion lemmas for mixed zones

This file proves the core fusion argument used in Lemma 12.  If two zones are
not mixed and no mixed `2 x 2` submatrix witness crosses between them, then
their union is not mixed.  The paper's corners are adjacent `2 x 2` witnesses;
the crossing predicates below are intentionally named as submatrix witnesses
because they do not impose adjacency.
-/

namespace Lax4Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

private theorem false_of_or_ne_of_eqs {α : Type*} {a b c d : α}
    (h : (a ≠ b) ∨ (c ≠ d)) (hab : a = b) (hcd : c = d) : False := by
  rcases h with h | h
  · exact h hab
  · exact h hcd

/-- A mixed crossing `2 x 2` submatrix witness between two row sets over a
column set.  This is not necessarily a paper corner, since the selected rows
and columns need not be adjacent. -/
def RowCrossingTwoByTwoSubmatrix {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R S : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∃ r ∈ R, ∃ s ∈ S, ∃ c₁ ∈ C, ∃ c₂ ∈ C,
    TwoByTwoMixed M r s c₁ c₂

/-- A mixed crossing `2 x 2` submatrix witness between two column sets over a
row set.  This is not necessarily a paper corner, since the selected rows and
columns need not be adjacent. -/
def ColCrossingTwoByTwoSubmatrix {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C D : Finset (Fin m)) : Prop :=
  ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ c ∈ C, ∃ d ∈ D,
    TwoByTwoMixed M r₁ r₂ c d

/-- A zone is not mixed exactly when it is vertical or horizontal. -/
theorem not_zoneMixed_iff_vertical_or_horizontal {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ¬ ZoneMixed M R C ↔ ZoneVertical M R C ∨ ZoneHorizontal M R C := by
  classical
  constructor
  · intro h
    by_cases hv : ZoneVertical M R C
    · exact Or.inl hv
    · by_cases hh : ZoneHorizontal M R C
      · exact Or.inr hh
      · exact False.elim (h ⟨hv, hh⟩)
  · intro h hmix
    rcases h with hv | hh
    · exact hmix.1 hv
    · exact hmix.2 hh

/-- A row cut is not mixed exactly when it is vertical or horizontal. -/
theorem not_rowCutMixed_iff_cutVertical_or_cutHorizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) :
    ¬ RowCutMixed M R C i ↔
      RowCutVertical M R C i ∨ RowCutHorizontal M R C i := by
  classical
  constructor
  · intro h
    by_cases hv : RowCutVertical M R C i
    · exact Or.inl hv
    · by_cases hh : RowCutHorizontal M R C i
      · exact Or.inr hh
      · exact False.elim (h ⟨hv, hh⟩)
  · intro h hmix
    rcases h with hv | hh
    · exact hmix.1 hv
    · exact hmix.2 hh

/-- A column cut is not mixed exactly when it is vertical or horizontal. -/
theorem not_colCutMixed_iff_cutVertical_or_cutHorizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) :
    ¬ ColCutMixed M R C j ↔
      ColCutVertical M R C j ∨ ColCutHorizontal M R C j := by
  classical
  constructor
  · intro h
    by_cases hv : ColCutVertical M R C j
    · exact Or.inl hv
    · by_cases hh : ColCutHorizontal M R C j
      · exact Or.inr hh
      · exact False.elim (h ⟨hv, hh⟩)
  · intro h hmix
    rcases h with hv | hh
    · exact hmix.1 hv
    · exact hmix.2 hh

theorem not_zoneMixed_union_rows_of_no_crossing {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R S : Finset (Fin n)} {C : Finset (Fin m)}
    (hR : ¬ ZoneMixed M R C)
    (hS : ¬ ZoneMixed M S C)
    (hcross : ¬ RowCrossingTwoByTwoSubmatrix M R S C) :
    ¬ ZoneMixed M (R ∪ S) C := by
  intro hmix
  rcases (zoneMixed_iff_zoneTwoByTwoSubmatrix M (R ∪ S) C).mp hmix with
    ⟨r₁, hr₁, r₂, hr₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  rcases Finset.mem_union.mp hr₁ with hR₁ | hS₁
  · rcases Finset.mem_union.mp hr₂ with hR₂ | hS₂
    · exact hR ((zoneMixed_iff_zoneTwoByTwoSubmatrix M R C).mpr
        ⟨r₁, hR₁, r₂, hR₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩)
    · exact hcross ⟨r₁, hR₁, r₂, hS₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  · rcases Finset.mem_union.mp hr₂ with hR₂ | hS₂
    · have hvert' :
          (M r₂ c₁ ≠ M r₁ c₁) ∨ (M r₂ c₂ ≠ M r₁ c₂) := by
        rcases hvert with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have hhoriz' :
          (M r₂ c₁ ≠ M r₂ c₂) ∨ (M r₁ c₁ ≠ M r₁ c₂) := by
        exact hhoriz.symm
      exact hcross ⟨r₂, hR₂, r₁, hS₁, c₁, hc₁, c₂, hc₂, hvert', hhoriz'⟩
    · exact hS ((zoneMixed_iff_zoneTwoByTwoSubmatrix M S C).mpr
        ⟨r₁, hS₁, r₂, hS₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩)

theorem not_zoneMixed_union_cols_of_no_crossing {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C D : Finset (Fin m)}
    (hC : ¬ ZoneMixed M R C)
    (hD : ¬ ZoneMixed M R D)
    (hcross : ¬ ColCrossingTwoByTwoSubmatrix M R C D) :
    ¬ ZoneMixed M R (C ∪ D) := by
  intro hmix
  rcases (zoneMixed_iff_zoneTwoByTwoSubmatrix M R (C ∪ D)).mp hmix with
    ⟨r₁, hr₁, r₂, hr₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  rcases Finset.mem_union.mp hc₁ with hC₁ | hD₁
  · rcases Finset.mem_union.mp hc₂ with hC₂ | hD₂
    · exact hC ((zoneMixed_iff_zoneTwoByTwoSubmatrix M R C).mpr
        ⟨r₁, hr₁, r₂, hr₂, c₁, hC₁, c₂, hC₂, hvert, hhoriz⟩)
    · exact hcross ⟨r₁, hr₁, r₂, hr₂, c₁, hC₁, c₂, hD₂, hvert, hhoriz⟩
  · rcases Finset.mem_union.mp hc₂ with hC₂ | hD₂
    · have hhoriz' :
          (M r₁ c₂ ≠ M r₁ c₁) ∨ (M r₂ c₂ ≠ M r₂ c₁) := by
        rcases hhoriz with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have hvert' :
          (M r₁ c₂ ≠ M r₂ c₂) ∨ (M r₁ c₁ ≠ M r₂ c₁) := by
        exact hvert.symm
      exact hcross ⟨r₁, hr₁, r₂, hr₂, c₂, hC₂, c₁, hD₁, hvert', hhoriz'⟩
    · exact hD ((zoneMixed_iff_zoneTwoByTwoSubmatrix M R D).mpr
        ⟨r₁, hr₁, r₂, hr₂, c₁, hD₁, c₂, hD₂, hvert, hhoriz⟩)

/-- Boundary localization for consecutive row parts.  If two adjacent zones
are not mixed, then a nonmixed boundary cut prevents any mixed `2 x 2`
submatrix witness from crossing the boundary. -/
theorem not_rowCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (R : Division n (k + 1)) {C : Finset (Fin m)} (i : Fin k)
    (hLzone : ¬ ZoneMixed M (R.part i.castSucc) C)
    (hRzone : ¬ ZoneMixed M (R.part i.succ) C)
    (hcut : ¬ RowCutMixed M R C i) :
    ¬ RowCrossingTwoByTwoSubmatrix M (R.part i.castSucc) (R.part i.succ) C := by
  intro hcross
  rcases hcross with
    ⟨r, hr, s, hs, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  have hLast : R.last i.castSucc ∈ R.part i.castSucc := R.last_mem i.castSucc
  have hFirst : R.first i.succ ∈ R.part i.succ := R.first_mem i.succ
  rcases (not_zoneMixed_iff_vertical_or_horizontal M (R.part i.castSucc) C).mp
      hLzone with hLv | hLh
  · rcases (not_zoneMixed_iff_vertical_or_horizontal M (R.part i.succ) C).mp
      hRzone with hRv | hRh
    · rcases (not_rowCutMixed_iff_cutVertical_or_cutHorizontal M R C i).mp
        hcut with hcutv | hcuth
      · have hcol₁ : M r c₁ = M s c₁ := by
          calc
            M r c₁ = M (R.last i.castSucc) c₁ := hLv hr hLast hc₁
            _ = M (R.first i.succ) c₁ := hcutv hc₁
            _ = M s c₁ := (hRv hs hFirst hc₁).symm
        have hcol₂ : M r c₂ = M s c₂ := by
          calc
            M r c₂ = M (R.last i.castSucc) c₂ := hLv hr hLast hc₂
            _ = M (R.first i.succ) c₂ := hcutv hc₂
            _ = M s c₂ := (hRv hs hFirst hc₂).symm
        exact false_of_or_ne_of_eqs hvert hcol₁ hcol₂
      · have hrconst : M r c₁ = M r c₂ := by
          calc
            M r c₁ = M (R.last i.castSucc) c₁ := hLv hr hLast hc₁
            _ = M (R.last i.castSucc) c₂ := hcuth.1 hc₁ hc₂
            _ = M r c₂ := (hLv hr hLast hc₂).symm
        have hsconst : M s c₁ = M s c₂ := by
          calc
            M s c₁ = M (R.first i.succ) c₁ := hRv hs hFirst hc₁
            _ = M (R.first i.succ) c₂ := hcuth.2 hc₁ hc₂
            _ = M s c₂ := (hRv hs hFirst hc₂).symm
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
    · rcases (not_rowCutMixed_iff_cutVertical_or_cutHorizontal M R C i).mp
        hcut with hcutv | hcuth
      · have hrconst : M r c₁ = M r c₂ := by
          calc
            M r c₁ = M (R.last i.castSucc) c₁ := hLv hr hLast hc₁
            _ = M (R.first i.succ) c₁ := hcutv hc₁
            _ = M (R.first i.succ) c₂ := hRh hFirst hc₁ hc₂
            _ = M (R.last i.castSucc) c₂ := (hcutv hc₂).symm
            _ = M r c₂ := (hLv hr hLast hc₂).symm
        have hsconst : M s c₁ = M s c₂ := hRh hs hc₁ hc₂
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
      · have hrconst : M r c₁ = M r c₂ := by
          calc
            M r c₁ = M (R.last i.castSucc) c₁ := hLv hr hLast hc₁
            _ = M (R.last i.castSucc) c₂ := hcuth.1 hc₁ hc₂
            _ = M r c₂ := (hLv hr hLast hc₂).symm
        have hsconst : M s c₁ = M s c₂ := hRh hs hc₁ hc₂
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
  · rcases (not_zoneMixed_iff_vertical_or_horizontal M (R.part i.succ) C).mp
      hRzone with hRv | hRh
    · rcases (not_rowCutMixed_iff_cutVertical_or_cutHorizontal M R C i).mp
        hcut with hcutv | hcuth
      · have hrconst : M r c₁ = M r c₂ := hLh hr hc₁ hc₂
        have hsconst : M s c₁ = M s c₂ := by
          calc
            M s c₁ = M (R.first i.succ) c₁ := hRv hs hFirst hc₁
            _ = M (R.last i.castSucc) c₁ := (hcutv hc₁).symm
            _ = M (R.last i.castSucc) c₂ := hLh hLast hc₁ hc₂
            _ = M (R.first i.succ) c₂ := hcutv hc₂
            _ = M s c₂ := (hRv hs hFirst hc₂).symm
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
      · have hrconst : M r c₁ = M r c₂ := hLh hr hc₁ hc₂
        have hsconst : M s c₁ = M s c₂ := by
          calc
            M s c₁ = M (R.first i.succ) c₁ := hRv hs hFirst hc₁
            _ = M (R.first i.succ) c₂ := hcuth.2 hc₁ hc₂
            _ = M s c₂ := (hRv hs hFirst hc₂).symm
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
    · have hrconst : M r c₁ = M r c₂ := hLh hr hc₁ hc₂
      have hsconst : M s c₁ = M s c₂ := hRh hs hc₁ hc₂
      exact false_of_or_ne_of_eqs hhoriz hrconst hsconst

/-- Boundary localization for consecutive column parts, dual to
`not_rowCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut`. -/
theorem not_colCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (C : Division m (k + 1)) (j : Fin k)
    (hLzone : ¬ ZoneMixed M R (C.part j.castSucc))
    (hRzone : ¬ ZoneMixed M R (C.part j.succ))
    (hcut : ¬ ColCutMixed M R C j) :
    ¬ ColCrossingTwoByTwoSubmatrix M R (C.part j.castSucc) (C.part j.succ) := by
  intro hcross
  rcases hcross with
    ⟨r₁, hr₁, r₂, hr₂, c, hc, d, hd, hvert, hhoriz⟩
  have hLast : C.last j.castSucc ∈ C.part j.castSucc := C.last_mem j.castSucc
  have hFirst : C.first j.succ ∈ C.part j.succ := C.first_mem j.succ
  rcases (not_zoneMixed_iff_vertical_or_horizontal M R (C.part j.castSucc)).mp
      hLzone with hLv | hLh
  · rcases (not_zoneMixed_iff_vertical_or_horizontal M R (C.part j.succ)).mp
      hRzone with hRv | hRh
    · have hcvert : M r₁ c = M r₂ c := hLv hr₁ hr₂ hc
      have hdvert : M r₁ d = M r₂ d := hRv hr₁ hr₂ hd
      exact false_of_or_ne_of_eqs hvert hcvert hdvert
    · rcases (not_colCutMixed_iff_cutVertical_or_cutHorizontal M R C j).mp
        hcut with hcutv | hcuth
      · have hcvert : M r₁ c = M r₂ c := hLv hr₁ hr₂ hc
        have hdvert : M r₁ d = M r₂ d := by
          calc
            M r₁ d = M r₁ (C.first j.succ) := (hRh hr₁ hFirst hd).symm
            _ = M r₂ (C.first j.succ) := hcutv.2 hr₁ hr₂
            _ = M r₂ d := hRh hr₂ hFirst hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
      · have hcvert : M r₁ c = M r₂ c := hLv hr₁ hr₂ hc
        have hdvert : M r₁ d = M r₂ d := by
          calc
            M r₁ d = M r₁ (C.first j.succ) := (hRh hr₁ hFirst hd).symm
            _ = M r₁ (C.last j.castSucc) := (hcuth hr₁).symm
            _ = M r₂ (C.last j.castSucc) := hLv hr₁ hr₂ hLast
            _ = M r₂ (C.first j.succ) := hcuth hr₂
            _ = M r₂ d := hRh hr₂ hFirst hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
  · rcases (not_zoneMixed_iff_vertical_or_horizontal M R (C.part j.succ)).mp
      hRzone with hRv | hRh
    · rcases (not_colCutMixed_iff_cutVertical_or_cutHorizontal M R C j).mp
        hcut with hcutv | hcuth
      · have hcvert : M r₁ c = M r₂ c := by
          calc
            M r₁ c = M r₁ (C.last j.castSucc) := hLh hr₁ hc hLast
            _ = M r₂ (C.last j.castSucc) := hcutv.1 hr₁ hr₂
            _ = M r₂ c := (hLh hr₂ hc hLast).symm
        have hdvert : M r₁ d = M r₂ d := hRv hr₁ hr₂ hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
      · have hcvert : M r₁ c = M r₂ c := by
          calc
            M r₁ c = M r₁ (C.last j.castSucc) := hLh hr₁ hc hLast
            _ = M r₁ (C.first j.succ) := hcuth hr₁
            _ = M r₂ (C.first j.succ) := hRv hr₁ hr₂ hFirst
            _ = M r₂ (C.last j.castSucc) := (hcuth hr₂).symm
            _ = M r₂ c := (hLh hr₂ hc hLast).symm
        have hdvert : M r₁ d = M r₂ d := hRv hr₁ hr₂ hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
    · rcases (not_colCutMixed_iff_cutVertical_or_cutHorizontal M R C j).mp
        hcut with hcutv | hcuth
      · have hcvert : M r₁ c = M r₂ c := by
          calc
            M r₁ c = M r₁ (C.last j.castSucc) := hLh hr₁ hc hLast
            _ = M r₂ (C.last j.castSucc) := hcutv.1 hr₁ hr₂
            _ = M r₂ c := (hLh hr₂ hc hLast).symm
        have hdvert : M r₁ d = M r₂ d := by
          calc
            M r₁ d = M r₁ (C.first j.succ) := (hRh hr₁ hFirst hd).symm
            _ = M r₂ (C.first j.succ) := hcutv.2 hr₁ hr₂
            _ = M r₂ d := hRh hr₂ hFirst hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
      · have hr₁const : M r₁ c = M r₁ d := by
          calc
            M r₁ c = M r₁ (C.last j.castSucc) := hLh hr₁ hc hLast
            _ = M r₁ (C.first j.succ) := hcuth hr₁
            _ = M r₁ d := hRh hr₁ hFirst hd
        have hr₂const : M r₂ c = M r₂ d := by
          calc
            M r₂ c = M r₂ (C.last j.castSucc) := hLh hr₂ hc hLast
            _ = M r₂ (C.first j.succ) := hcuth hr₂
            _ = M r₂ d := hRh hr₂ hFirst hd
        exact false_of_or_ne_of_eqs hhoriz hr₁const hr₂const

/-- If adjacent row zones are not mixed, a crossing mixed `2 x 2` submatrix
witness forces the boundary row cut to be mixed. -/
theorem rowCutMixed_of_crossingTwoByTwoSubmatrix_of_not_mixed_zones {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (R : Division n (k + 1)) {C : Finset (Fin m)} (i : Fin k)
    (hLzone : ¬ ZoneMixed M (R.part i.castSucc) C)
    (hRzone : ¬ ZoneMixed M (R.part i.succ) C)
    (hcross :
      RowCrossingTwoByTwoSubmatrix M (R.part i.castSucc) (R.part i.succ) C) :
    RowCutMixed M R C i := by
  classical
  by_contra hcut
  exact not_rowCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut
    (M := M) R i hLzone hRzone hcut hcross

/-- If adjacent column zones are not mixed, a crossing mixed `2 x 2` submatrix
witness forces the boundary column cut to be mixed. -/
theorem colCutMixed_of_crossingTwoByTwoSubmatrix_of_not_mixed_zones {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (C : Division m (k + 1)) (j : Fin k)
    (hLzone : ¬ ZoneMixed M R (C.part j.castSucc))
    (hRzone : ¬ ZoneMixed M R (C.part j.succ))
    (hcross :
      ColCrossingTwoByTwoSubmatrix M R (C.part j.castSucc) (C.part j.succ)) :
    ColCutMixed M R C j := by
  classical
  by_contra hcut
  exact not_colCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut
    (M := M) C j hLzone hRzone hcut hcross

/-- Row form of the paper's Lemma 12: fusing two consecutive row zones that
are both nonmixed preserves nonmixedness whenever the boundary cut is also
nonmixed. -/
theorem not_zoneMixed_union_consecutive_rows_of_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (R : Division n (k + 1)) {C : Finset (Fin m)} (i : Fin k)
    (hLzone : ¬ ZoneMixed M (R.part i.castSucc) C)
    (hRzone : ¬ ZoneMixed M (R.part i.succ) C)
    (hcut : ¬ RowCutMixed M R C i) :
    ¬ ZoneMixed M (R.part i.castSucc ∪ R.part i.succ) C :=
  not_zoneMixed_union_rows_of_no_crossing hLzone hRzone
    (not_rowCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut
      (M := M) R i hLzone hRzone hcut)

/-- Column form of the paper's Lemma 12. -/
theorem not_zoneMixed_union_consecutive_cols_of_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (C : Division m (k + 1)) (j : Fin k)
    (hLzone : ¬ ZoneMixed M R (C.part j.castSucc))
    (hRzone : ¬ ZoneMixed M R (C.part j.succ))
    (hcut : ¬ ColCutMixed M R C j) :
    ¬ ZoneMixed M R (C.part j.castSucc ∪ C.part j.succ) :=
  not_zoneMixed_union_cols_of_no_crossing hLzone hRzone
    (not_colCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut
      (M := M) C j hLzone hRzone hcut)

/-- Lemma 12, local exact row-fusion form: the newly merged row part is
nonmixed on `C` whenever the two old adjacent row zones and their boundary cut
are nonmixed. -/
theorem not_zoneMixed_fused_row_part_of_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : Division n (k + 2)} {E : Division n (k + 1)}
    {C : Finset (Fin m)} {i : Fin (k + 1)}
    (hfuse : Division.IsFusionAt D E i)
    (hLzone : ¬ ZoneMixed M (D.part i.castSucc) C)
    (hRzone : ¬ ZoneMixed M (D.part i.succ) C)
    (hcut : ¬ RowCutMixed M D C i) :
    ¬ ZoneMixed M (E.part i) C := by
  rw [hfuse i, Division.fusePart_self]
  exact not_zoneMixed_union_consecutive_rows_of_not_mixed_cut
    (M := M) D i hLzone hRzone hcut

/-- Contrapositive package of the exact row-fusion form of Lemma 12. -/
theorem rowFusion_old_zone_or_cut_mixed_of_fused_row_part_mixed {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : Division n (k + 2)} {E : Division n (k + 1)}
    {C : Finset (Fin m)} {i : Fin (k + 1)}
    (hfuse : Division.IsFusionAt D E i)
    (hmix : ZoneMixed M (E.part i) C) :
    ZoneMixed M (D.part i.castSucc) C ∨
      ZoneMixed M (D.part i.succ) C ∨ RowCutMixed M D C i := by
  classical
  by_cases hL : ZoneMixed M (D.part i.castSucc) C
  · exact Or.inl hL
  · by_cases hR : ZoneMixed M (D.part i.succ) C
    · exact Or.inr (Or.inl hR)
    · by_cases hcut : RowCutMixed M D C i
      · exact Or.inr (Or.inr hcut)
      · exact False.elim
          (not_zoneMixed_fused_row_part_of_not_mixed_cut
            (M := M) hfuse hL hR hcut hmix)

/-- Lemma 12, local exact column-fusion form. -/
theorem not_zoneMixed_fused_col_part_of_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {D : Division m (k + 2)} {E : Division m (k + 1)}
    {j : Fin (k + 1)}
    (hfuse : Division.IsFusionAt D E j)
    (hLzone : ¬ ZoneMixed M R (D.part j.castSucc))
    (hRzone : ¬ ZoneMixed M R (D.part j.succ))
    (hcut : ¬ ColCutMixed M R D j) :
    ¬ ZoneMixed M R (E.part j) := by
  rw [hfuse j, Division.fusePart_self]
  exact not_zoneMixed_union_consecutive_cols_of_not_mixed_cut
    (M := M) D j hLzone hRzone hcut

/-- Contrapositive package of the exact column-fusion form of Lemma 12. -/
theorem colFusion_old_zone_or_cut_mixed_of_fused_col_part_mixed {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {D : Division m (k + 2)} {E : Division m (k + 1)}
    {j : Fin (k + 1)}
    (hfuse : Division.IsFusionAt D E j)
    (hmix : ZoneMixed M R (E.part j)) :
    ZoneMixed M R (D.part j.castSucc) ∨
      ZoneMixed M R (D.part j.succ) ∨ ColCutMixed M R D j := by
  classical
  by_cases hL : ZoneMixed M R (D.part j.castSucc)
  · exact Or.inl hL
  · by_cases hR : ZoneMixed M R (D.part j.succ)
    · exact Or.inr (Or.inl hR)
    · by_cases hcut : ColCutMixed M R D j
      · exact Or.inr (Or.inr hcut)
      · exact False.elim
          (not_zoneMixed_fused_col_part_of_not_mixed_cut
            (M := M) hfuse hL hR hcut hmix)

theorem rowCutMixed_of_fuse_rowCutMixed_of_lt {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : Division n (k + 2)) {C : Finset (Fin m)}
    {i : Fin (k + 1)} {j : Fin k}
    (hji : j.castSucc < i)
    (hmix : RowCutMixed M (D.fuse i) C j) :
    RowCutMixed M D C j.castSucc := by
  have hleftPart :
      (D.fuse i).part j.castSucc = D.part j.castSucc.castSucc :=
    Division.fuse_part_of_lt D hji
  have hleftLast :
      (D.fuse i).last j.castSucc = D.last j.castSucc.castSucc := by
    simp [Division.last, hleftPart]
  have hrightFirst :
      (D.fuse i).first j.succ = D.first j.castSucc.succ := by
    by_cases hs : j.succ = i
    · subst i
      simp [Division.first_fuse_self]
    · have hslt : j.succ < i := by
        apply Fin.mk_lt_mk.mpr
        have hlt : j.1 < i.1 := Fin.mk_lt_mk.mp hji
        have hne : j.1 + 1 ≠ i.1 := by
          intro hval
          exact hs (Fin.ext hval)
        omega
      have hpart : (D.fuse i).part j.succ = D.part j.succ.castSucc :=
        Division.fuse_part_of_lt D hslt
      simp [Division.first, hpart]
  constructor
  · intro hv
    exact hmix.1 (by
      intro c hc
      rw [hleftLast, hrightFirst]
      exact hv hc)
  · intro hh
    exact hmix.2 (by
      constructor
      · intro c₁ c₂ hc₁ hc₂
        rw [hleftLast]
        exact hh.1 hc₁ hc₂
      · intro c₁ c₂ hc₁ hc₂
        rw [hrightFirst]
        exact hh.2 hc₁ hc₂)

theorem rowCutMixed_of_fuse_rowCutMixed_of_ge {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : Division n (k + 2)) {C : Finset (Fin m)}
    {i : Fin (k + 1)} {j : Fin k}
    (hij : i ≤ j.castSucc)
    (hmix : RowCutMixed M (D.fuse i) C j) :
    RowCutMixed M D C j.succ := by
  have hleftLast :
      (D.fuse i).last j.castSucc = D.last j.succ.castSucc := by
    by_cases hs : j.castSucc = i
    · subst i
      simp [Division.last_fuse_self]
    · have hgt : i < j.castSucc := lt_of_le_of_ne hij (Ne.symm hs)
      have hpart : (D.fuse i).part j.castSucc = D.part j.castSucc.succ :=
        Division.fuse_part_of_gt D hgt
      simp [Division.last, hpart]
  have hrightPart :
      (D.fuse i).part j.succ = D.part j.succ.succ := by
    have hgt : i < j.succ := by
      apply lt_of_le_of_lt hij
      exact Fin.castSucc_lt_succ
    exact Division.fuse_part_of_gt D hgt
  have hrightFirst :
      (D.fuse i).first j.succ = D.first j.succ.succ := by
    simp [Division.first, hrightPart]
  constructor
  · intro hv
    exact hmix.1 (by
      intro c hc
      rw [hleftLast, hrightFirst]
      exact hv hc)
  · intro hh
    exact hmix.2 (by
      constructor
      · intro c₁ c₂ hc₁ hc₂
        rw [hleftLast]
        exact hh.1 hc₁ hc₂
      · intro c₁ c₂ hc₁ hc₂
        rw [hrightFirst]
        exact hh.2 hc₁ hc₂)

theorem colCutMixed_of_fuse_colCutMixed_of_lt {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (D : Division m (k + 2))
    {i : Fin (k + 1)} {j : Fin k}
    (hji : j.castSucc < i)
    (hmix : ColCutMixed M R (D.fuse i) j) :
    ColCutMixed M R D j.castSucc := by
  have hleftPart :
      (D.fuse i).part j.castSucc = D.part j.castSucc.castSucc :=
    Division.fuse_part_of_lt D hji
  have hleftLast :
      (D.fuse i).last j.castSucc = D.last j.castSucc.castSucc := by
    simp [Division.last, hleftPart]
  have hrightFirst :
      (D.fuse i).first j.succ = D.first j.castSucc.succ := by
    by_cases hs : j.succ = i
    · subst i
      simp [Division.first_fuse_self]
    · have hslt : j.succ < i := by
        apply Fin.mk_lt_mk.mpr
        have hlt : j.1 < i.1 := Fin.mk_lt_mk.mp hji
        have hne : j.1 + 1 ≠ i.1 := by
          intro hval
          exact hs (Fin.ext hval)
        omega
      have hpart : (D.fuse i).part j.succ = D.part j.succ.castSucc :=
        Division.fuse_part_of_lt D hslt
      simp [Division.first, hpart]
  constructor
  · intro hv
    exact hmix.1 (by
      constructor
      · intro r₁ r₂ hr₁ hr₂
        rw [hleftLast]
        exact hv.1 hr₁ hr₂
      · intro r₁ r₂ hr₁ hr₂
        rw [hrightFirst]
        exact hv.2 hr₁ hr₂)
  · intro hh
    exact hmix.2 (by
      intro r hr
      rw [hleftLast, hrightFirst]
      exact hh hr)

theorem colCutMixed_of_fuse_colCutMixed_of_ge {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (D : Division m (k + 2))
    {i : Fin (k + 1)} {j : Fin k}
    (hij : i ≤ j.castSucc)
    (hmix : ColCutMixed M R (D.fuse i) j) :
    ColCutMixed M R D j.succ := by
  have hleftLast :
      (D.fuse i).last j.castSucc = D.last j.succ.castSucc := by
    by_cases hs : j.castSucc = i
    · subst i
      simp [Division.last_fuse_self]
    · have hgt : i < j.castSucc := lt_of_le_of_ne hij (Ne.symm hs)
      have hpart : (D.fuse i).part j.castSucc = D.part j.castSucc.succ :=
        Division.fuse_part_of_gt D hgt
      simp [Division.last, hpart]
  have hrightPart :
      (D.fuse i).part j.succ = D.part j.succ.succ := by
    have hgt : i < j.succ := by
      apply lt_of_le_of_lt hij
      exact Fin.castSucc_lt_succ
    exact Division.fuse_part_of_gt D hgt
  have hrightFirst :
      (D.fuse i).first j.succ = D.first j.succ.succ := by
    simp [Division.first, hrightPart]
  constructor
  · intro hv
    exact hmix.1 (by
      constructor
      · intro r₁ r₂ hr₁ hr₂
        rw [hleftLast]
        exact hv.1 hr₁ hr₂
      · intro r₁ r₂ hr₁ hr₂
        rw [hrightFirst]
        exact hv.2 hr₁ hr₂)
  · intro hh
    exact hmix.2 (by
      intro r hr
      rw [hleftLast, hrightFirst]
      exact hh hr)

/-- The old mixed item charged by a mixed item after a row fusion.  Zones away
from the fused pair keep their old zone index, cuts away from the fused
boundary keep their old cut index, and the new fused zone is charged to one of
the two old zones or to the disappearing boundary cut. -/
noncomputable def rowFuseItemMap {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : Division n (k + 2)) (C : Finset (Fin m)) (i : Fin (k + 1)) :
    Sum (Fin (k + 1)) (Fin k) → Sum (Fin (k + 2)) (Fin (k + 1)) := by
  classical
  intro x
  rcases x with j | j
  · exact
      if hj : j = i then
        if ZoneMixed M (D.part i.castSucc) C then
          Sum.inl i.castSucc
        else if ZoneMixed M (D.part i.succ) C then
          Sum.inl i.succ
        else
          Sum.inr i
      else if hji : j < i then
        Sum.inl j.castSucc
      else
        Sum.inl j.succ
  · exact
      if hji : j.castSucc < i then
        Sum.inr j.castSucc
      else
        Sum.inr j.succ

/-- A left inverse for `rowFuseItemMap`.  Old zones are projected by the
fusion index map.  The deleted old boundary cut is sent to the new fused zone. -/
def rowFuseItemPreimage {k : ℕ} (i : Fin (k + 1)) :
    Sum (Fin (k + 2)) (Fin (k + 1)) → Sum (Fin (k + 1)) (Fin k)
  | Sum.inl a => Sum.inl (Division.fuseIndex i a)
  | Sum.inr b =>
      if hlt : b < i then
        Sum.inr ⟨b.1, by
          have hb : b.1 < i.1 := Fin.mk_lt_mk.mp hlt
          omega⟩
      else if hb : b = i then
        Sum.inl i
      else
        Sum.inr ⟨b.1 - 1, by
          have hle : i ≤ b := le_of_not_gt hlt
          have hne : i ≠ b := by exact Ne.symm hb
          have hlt' : i < b := lt_of_le_of_ne hle hne
          have hbpos : 0 < b.1 := by
            have hi_lt : i.1 < b.1 := Fin.mk_lt_mk.mp hlt'
            omega
          omega⟩

theorem rowFuseItemPreimage_map {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : Division n (k + 2)) (C : Finset (Fin m)) (i : Fin (k + 1))
    (x : Sum (Fin (k + 1)) (Fin k)) :
    rowFuseItemPreimage i (rowFuseItemMap M D C i x) = x := by
  classical
  cases x with
  | inl j =>
      by_cases hj : j = i
      · subst j
        by_cases hL : ZoneMixed M (D.part i.castSucc) C
        · simp [rowFuseItemMap, rowFuseItemPreimage, hL, Division.fuseIndex_eq_self_iff]
        · by_cases hR : ZoneMixed M (D.part i.succ) C
          · simp [rowFuseItemMap, rowFuseItemPreimage, hL, hR,
              Division.fuseIndex_eq_self_iff]
          · simp [rowFuseItemMap, rowFuseItemPreimage, hL, hR]
      · by_cases hji : j < i
        · have hidx : Division.fuseIndex i j.castSucc = j :=
            (Division.fuseIndex_eq_of_lt_iff hji j.castSucc).mpr rfl
          simp [rowFuseItemMap, rowFuseItemPreimage, hj, hji, hidx]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj)
          have hidx : Division.fuseIndex i j.succ = j :=
            (Division.fuseIndex_eq_of_gt_iff hij j.succ).mpr rfl
          simp [rowFuseItemMap, rowFuseItemPreimage, hj, hji, hidx]
  | inr j =>
      by_cases hji : j.castSucc < i
      · have hlt : j.castSucc < i := hji
        simp [rowFuseItemMap, rowFuseItemPreimage, hji]
      · have hnot : ¬ j.succ < i := by
          intro hlt
          exact hji (lt_trans Fin.castSucc_lt_succ hlt)
        have hne : ¬ j.succ = i := by
          intro h
          subst i
          exact hji Fin.castSucc_lt_succ
        simp [rowFuseItemMap, rowFuseItemPreimage, hji, hnot, hne]

theorem rowFuseItemMap_injective {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : Division n (k + 2)) (C : Finset (Fin m)) (i : Fin (k + 1)) :
    Function.Injective (rowFuseItemMap M D C i) := by
  intro x y hxy
  have h := congrArg (rowFuseItemPreimage i) hxy
  simpa [rowFuseItemPreimage_map M D C i x,
    rowFuseItemPreimage_map M D C i y] using h

theorem rowFuseItemMap_mem {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : Division n (k + 2)) {C : Finset (Fin m)} (i : Fin (k + 1))
    {x : Sum (Fin (k + 1)) (Fin k)}
    (hx : x ∈ rowMixedItems M (D.fuse i) C) :
    rowFuseItemMap M D C i x ∈ rowMixedItems M D C := by
  classical
  cases x with
  | inl j =>
      have hmix : ZoneMixed M ((D.fuse i).part j) C := by
        simpa using hx
      by_cases hj : j = i
      · subst j
        by_cases hL : ZoneMixed M (D.part i.castSucc) C
        · simp [rowFuseItemMap, hL]
        · by_cases hR : ZoneMixed M (D.part i.succ) C
          · simp [rowFuseItemMap, hL, hR]
          · have hcut : RowCutMixed M D C i := by
              rcases rowFusion_old_zone_or_cut_mixed_of_fused_row_part_mixed
                  (M := M) (D := D) (E := D.fuse i)
                  (C := C) (i := i) (Division.isFusionAt_fuse D i) hmix with h | h | h
              · exact False.elim (hL h)
              · exact False.elim (hR h)
              · exact h
            simp [rowFuseItemMap, hL, hR, hcut]
      · by_cases hji : j < i
        · have hpart : (D.fuse i).part j = D.part j.castSucc :=
            Division.fuse_part_of_lt D hji
          have hold : ZoneMixed M (D.part j.castSucc) C := by
            simpa [hpart] using hmix
          simp [rowFuseItemMap, hj, hji, hold]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj)
          have hpart : (D.fuse i).part j = D.part j.succ :=
            Division.fuse_part_of_gt D hij
          have hold : ZoneMixed M (D.part j.succ) C := by
            simpa [hpart] using hmix
          simp [rowFuseItemMap, hj, hji, hold]
  | inr j =>
      have hmix : RowCutMixed M (D.fuse i) C j := by
        simpa using hx
      by_cases hji : j.castSucc < i
      · have hold : RowCutMixed M D C j.castSucc :=
          rowCutMixed_of_fuse_rowCutMixed_of_lt D hji hmix
        simp [rowFuseItemMap, hji, hold]
      · have hij : i ≤ j.castSucc := le_of_not_gt hji
        have hold : RowCutMixed M D C j.succ :=
          rowCutMixed_of_fuse_rowCutMixed_of_ge D hij hmix
        simp [rowFuseItemMap, hji, hold]

/-- Cardinal form of Lemma 12 for row fusions: fusing two consecutive row
parts does not increase the mixed value of any fixed column interval. -/
theorem rowMixedValue_fuse_le {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : Division n (k + 2)) (C : Finset (Fin m)) (i : Fin (k + 1)) :
    rowMixedValue M (D.fuse i) C ≤ rowMixedValue M D C := by
  classical
  rw [← rowMixedItems_card M (D.fuse i) C, ← rowMixedItems_card M D C]
  exact Finset.card_le_card_of_injOn
    (rowFuseItemMap M D C i)
    (fun x hx => rowFuseItemMap_mem D i hx)
    (fun x _hx y _hy hxy => rowFuseItemMap_injective M D C i hxy)

/-- Column-fusion analogue of `rowFuseItemMap`. -/
noncomputable def colFuseItemMap {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (D : Division m (k + 2)) (i : Fin (k + 1)) :
    Sum (Fin (k + 1)) (Fin k) → Sum (Fin (k + 2)) (Fin (k + 1)) := by
  classical
  intro x
  rcases x with j | j
  · exact
      if hj : j = i then
        if ZoneMixed M R (D.part i.castSucc) then
          Sum.inl i.castSucc
        else if ZoneMixed M R (D.part i.succ) then
          Sum.inl i.succ
        else
          Sum.inr i
      else if hji : j < i then
        Sum.inl j.castSucc
      else
        Sum.inl j.succ
  · exact
      if hji : j.castSucc < i then
        Sum.inr j.castSucc
      else
        Sum.inr j.succ

theorem colFuseItemPreimage_map {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (D : Division m (k + 2)) (i : Fin (k + 1))
    (x : Sum (Fin (k + 1)) (Fin k)) :
    rowFuseItemPreimage i (colFuseItemMap M R D i x) = x := by
  classical
  cases x with
  | inl j =>
      by_cases hj : j = i
      · subst j
        by_cases hL : ZoneMixed M R (D.part i.castSucc)
        · simp [colFuseItemMap, rowFuseItemPreimage, hL, Division.fuseIndex_eq_self_iff]
        · by_cases hR : ZoneMixed M R (D.part i.succ)
          · simp [colFuseItemMap, rowFuseItemPreimage, hL, hR,
              Division.fuseIndex_eq_self_iff]
          · simp [colFuseItemMap, rowFuseItemPreimage, hL, hR]
      · by_cases hji : j < i
        · have hidx : Division.fuseIndex i j.castSucc = j :=
            (Division.fuseIndex_eq_of_lt_iff hji j.castSucc).mpr rfl
          simp [colFuseItemMap, rowFuseItemPreimage, hj, hji, hidx]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj)
          have hidx : Division.fuseIndex i j.succ = j :=
            (Division.fuseIndex_eq_of_gt_iff hij j.succ).mpr rfl
          simp [colFuseItemMap, rowFuseItemPreimage, hj, hji, hidx]
  | inr j =>
      by_cases hji : j.castSucc < i
      · have hlt : j.castSucc < i := hji
        simp [colFuseItemMap, rowFuseItemPreimage, hji]
      · have hnot : ¬ j.succ < i := by
          intro hlt
          exact hji (lt_trans Fin.castSucc_lt_succ hlt)
        have hne : ¬ j.succ = i := by
          intro h
          subst i
          exact hji Fin.castSucc_lt_succ
        simp [colFuseItemMap, rowFuseItemPreimage, hji, hnot, hne]

theorem colFuseItemMap_injective {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (D : Division m (k + 2)) (i : Fin (k + 1)) :
    Function.Injective (colFuseItemMap M R D i) := by
  intro x y hxy
  have h := congrArg (rowFuseItemPreimage i) hxy
  simpa [colFuseItemPreimage_map M R D i x,
    colFuseItemPreimage_map M R D i y] using h

theorem colFuseItemMap_mem {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (D : Division m (k + 2)) (i : Fin (k + 1))
    {x : Sum (Fin (k + 1)) (Fin k)}
    (hx : x ∈ colMixedItems M R (D.fuse i)) :
    colFuseItemMap M R D i x ∈ colMixedItems M R D := by
  classical
  cases x with
  | inl j =>
      have hmix : ZoneMixed M R ((D.fuse i).part j) := by
        simpa using hx
      by_cases hj : j = i
      · subst j
        by_cases hL : ZoneMixed M R (D.part i.castSucc)
        · simp [colFuseItemMap, hL]
        · by_cases hR : ZoneMixed M R (D.part i.succ)
          · simp [colFuseItemMap, hL, hR]
          · have hcut : ColCutMixed M R D i := by
              rcases colFusion_old_zone_or_cut_mixed_of_fused_col_part_mixed
                  (M := M) (R := R) (D := D) (E := D.fuse i)
                  (j := i) (Division.isFusionAt_fuse D i) hmix with h | h | h
              · exact False.elim (hL h)
              · exact False.elim (hR h)
              · exact h
            simp [colFuseItemMap, hL, hR, hcut]
      · by_cases hji : j < i
        · have hpart : (D.fuse i).part j = D.part j.castSucc :=
            Division.fuse_part_of_lt D hji
          have hold : ZoneMixed M R (D.part j.castSucc) := by
            simpa [hpart] using hmix
          simp [colFuseItemMap, hj, hji, hold]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj)
          have hpart : (D.fuse i).part j = D.part j.succ :=
            Division.fuse_part_of_gt D hij
          have hold : ZoneMixed M R (D.part j.succ) := by
            simpa [hpart] using hmix
          simp [colFuseItemMap, hj, hji, hold]
  | inr j =>
      have hmix : ColCutMixed M R (D.fuse i) j := by
        simpa using hx
      by_cases hji : j.castSucc < i
      · have hold : ColCutMixed M R D j.castSucc :=
          colCutMixed_of_fuse_colCutMixed_of_lt D hji hmix
        simp [colFuseItemMap, hji, hold]
      · have hij : i ≤ j.castSucc := le_of_not_gt hji
        have hold : ColCutMixed M R D j.succ :=
          colCutMixed_of_fuse_colCutMixed_of_ge D hij hmix
        simp [colFuseItemMap, hji, hold]

/-- Cardinal form of Lemma 12 for column fusions. -/
theorem colMixedValue_fuse_le {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (R : Finset (Fin n)) (D : Division m (k + 2)) (i : Fin (k + 1)) :
    colMixedValue M R (D.fuse i) ≤ colMixedValue M R D := by
  classical
  rw [← colMixedItems_card M R (D.fuse i), ← colMixedItems_card M R D]
  exact Finset.card_le_card_of_injOn
    (colFuseItemMap M R D i)
    (fun x hx => colFuseItemMap_mem D i hx)
    (fun x _hx y _hy hxy => colFuseItemMap_injective M R D i hxy)

end Matrix
end Lax4Proofs.TwinWidth
