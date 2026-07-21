/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TwinWidth contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# Divisions of finite intervals

This file contains the finite interval divisions used by the mixed-minor side of
the twin-width/mixed-minor equivalence.  A `Division n k` is represented by its
parts, together with the properties needed downstream: nonempty parts,
disjointness, covering, and order-convexity.
-/

namespace Lax2Proofs.TwinWidth

/-- A `k`-division of `Fin n` is a partition into `k` nonempty convex parts.

The intended use is a partition of the linearly ordered rows or columns of a
matrix into consecutive intervals.  The fields expose exactly the API used by
mixed cells; the concrete representation is deliberately neutral so that a
cut-point implementation can replace it later without changing downstream
statements.
-/
structure Division (n k : ℕ) where
  /-- The `i`-th part of the division. -/
  part : Fin k → Finset (Fin n)
  /-- Every part is nonempty. -/
  part_nonempty : ∀ i, (part i).Nonempty
  /-- Distinct parts are disjoint. -/
  part_disjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (part i) (part j)
  /-- The parts cover the whole finite interval. -/
  part_cover : ∀ x : Fin n, ∃ i, x ∈ part i
  /-- Parts are convex in the natural order on `Fin n`. -/
  part_convex :
    ∀ i ⦃a b c : Fin n⦄, a ∈ part i → c ∈ part i → a ≤ b → b ≤ c → b ∈ part i
  /-- Earlier-indexed parts are strictly before later-indexed parts. -/
  part_ordered :
    ∀ ⦃i j : Fin k⦄, i < j →
      ∀ ⦃a b : Fin n⦄, a ∈ part i → b ∈ part j → a < b

namespace Division

variable {n k : ℕ} (D : Division n k)

@[simp] theorem part_nonempty' (i : Fin k) : (D.part i).Nonempty :=
  D.part_nonempty i

theorem part_disjoint' ⦃i j : Fin k⦄ (hij : i ≠ j) :
    Disjoint (D.part i) (D.part j) :=
  D.part_disjoint hij

theorem part_cover' (x : Fin n) : ∃ i, x ∈ D.part i :=
  D.part_cover x

theorem part_convex' (i : Fin k) ⦃a b c : Fin n⦄
    (ha : a ∈ D.part i) (hc : c ∈ D.part i) (hab : a ≤ b) (hbc : b ≤ c) :
    b ∈ D.part i :=
  D.part_convex i ha hc hab hbc

theorem part_ordered' ⦃i j : Fin k⦄ (hij : i < j)
    ⦃a b : Fin n⦄ (ha : a ∈ D.part i) (hb : b ∈ D.part j) :
    a < b :=
  D.part_ordered hij ha hb

/-- Distinct indices of a division have distinct parts. -/
theorem part_injective : Function.Injective D.part := by
  intro i j hij_parts
  by_contra hij
  rcases D.part_nonempty i with ⟨x, hx⟩
  have hxj : x ∈ D.part j := by simpa [hij_parts] using hx
  exact Finset.disjoint_left.mp (D.part_disjoint hij) hx hxj

/-- A division of `Fin n` into `k` nonempty parts has at most `n` parts. -/
theorem card_parts_le (D : Division n k) : k ≤ n := by
  classical
  let f : Fin k → Fin n := fun i => Classical.choose (D.part_nonempty i)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hi : f i ∈ D.part i := Classical.choose_spec (D.part_nonempty i)
    have hj : f i ∈ D.part j := by
      have hj' : f j ∈ D.part j := Classical.choose_spec (D.part_nonempty j)
      simpa [hij] using hj'
    exact Finset.disjoint_left.mp (D.part_disjoint hne) hi hj
  simpa using Fintype.card_le_of_injective f hf

/-- Build a division as the fibers of an order-preserving surjection.

This constructor is useful for index coarsenings: if consecutive source
indices are sent to the same target index, the fibers are nonempty consecutive
blocks and therefore form a `Division`. -/
noncomputable def ofMonotoneSurjective {n k : ℕ} (f : Fin n → Fin k)
    (hmono : ∀ ⦃a b : Fin n⦄, a ≤ b → f a ≤ f b)
    (hsurj : ∀ j : Fin k, ∃ a : Fin n, f a = j) :
    Division n k where
  part j := (Finset.univ : Finset (Fin n)).filter fun a => f a = j
  part_nonempty := by
    intro j
    rcases hsurj j with ⟨a, ha⟩
    exact ⟨a, by simp [ha]⟩
  part_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hy
    have hxi : f x = i := by simpa using hx
    have hxj : f x = j := by simpa using hy
    exact hij (hxi.symm.trans hxj)
  part_cover := by
    intro x
    exact ⟨f x, by simp⟩
  part_convex := by
    intro i a b c ha hc hab hbc
    have hai : f a = i := by simpa using ha
    have hci : f c = i := by simpa using hc
    have hab' : f a ≤ f b := hmono hab
    have hbc' : f b ≤ f c := hmono hbc
    have hbi : f b = i := by
      exact le_antisymm (by simpa [hci] using hbc') (by simpa [hai] using hab')
    simp [hbi]
  part_ordered := by
    intro i j hij a b ha hb
    have hai : f a = i := by simpa using ha
    have hbj : f b = j := by simpa using hb
    by_contra hnot
    have hba : b ≤ a := le_of_not_gt hnot
    have hle : f b ≤ f a := hmono hba
    have hji : j ≤ i := by simpa [hai, hbj] using hle
    exact (not_lt_of_ge hji) hij

@[simp] theorem mem_ofMonotoneSurjective_part {n k : ℕ}
    (f : Fin n → Fin k)
    (hmono : ∀ ⦃a b : Fin n⦄, a ≤ b → f a ≤ f b)
    (hsurj : ∀ j : Fin k, ∃ a : Fin n, f a = j)
    (j : Fin k) (a : Fin n) :
    a ∈ (ofMonotoneSurjective f hmono hsurj).part j ↔ f a = j := by
  simp [ofMonotoneSurjective]

/-- The first element of a division part. -/
noncomputable def first (i : Fin k) : Fin n :=
  (D.part i).min' (D.part_nonempty i)

/-- The last element of a division part. -/
noncomputable def last (i : Fin k) : Fin n :=
  (D.part i).max' (D.part_nonempty i)

theorem first_mem (i : Fin k) : D.first i ∈ D.part i :=
  Finset.min'_mem _ _

theorem last_mem (i : Fin k) : D.last i ∈ D.part i :=
  Finset.max'_mem _ _

/-- Equal division parts have the same first element. -/
theorem first_eq_of_part_eq {D E : Division n k} {i j : Fin k}
    (hpart : D.part i = E.part j) :
    D.first i = E.first j := by
  classical
  apply le_antisymm
  · exact Finset.min'_le _ _ (by simpa [hpart] using E.first_mem j)
  · exact Finset.min'_le _ _ (by simpa [hpart] using D.first_mem i)

/-- Reindex the parts of a division along an equality of the number of parts. -/
noncomputable def castIndex {l : ℕ} (h : k = l) (D : Division n k) :
    Division n l where
  part i := D.part ((finCongr h).symm i)
  part_nonempty i := D.part_nonempty ((finCongr h).symm i)
  part_disjoint := by
    intro i j hij
    apply D.part_disjoint
    intro heq
    exact hij (by
      apply (finCongr h).symm.injective
      simpa using heq)
  part_cover := by
    intro x
    rcases D.part_cover x with ⟨i, hi⟩
    exact ⟨finCongr h i, by simpa using hi⟩
  part_convex := by
    intro i a b c ha hc hab hbc
    exact D.part_convex ((finCongr h).symm i) ha hc hab hbc
  part_ordered := by
    intro i j hij a b ha hb
    have hij' : (finCongr h).symm i < (finCongr h).symm j := by
      apply Fin.mk_lt_mk.mpr
      exact Fin.mk_lt_mk.mp hij
    exact D.part_ordered hij' ha hb

/-- Reindexing a division does not change its finite set of parts. -/
@[simp] theorem parts_castIndex {n k l : ℕ} (h : k = l) (D : Division n k) :
    ((Finset.univ : Finset (Fin l)).map ⟨(Division.castIndex h D).part,
      (Division.castIndex h D).part_injective⟩) =
    ((Finset.univ : Finset (Fin k)).map ⟨D.part, D.part_injective⟩) := by
  classical
  ext R
  constructor
  · intro hR
    rcases Finset.mem_map.mp hR with ⟨a, _ha, haR⟩
    change (Division.castIndex h D).part a = R at haR
    refine Finset.mem_map.mpr ⟨(finCongr h).symm a, Finset.mem_univ _, ?_⟩
    simpa [Division.castIndex] using haR
  · intro hR
    rcases Finset.mem_map.mp hR with ⟨a, _ha, haR⟩
    change D.part a = R at haR
    refine Finset.mem_map.mpr ⟨finCongr h a, Finset.mem_univ _, ?_⟩
    simpa [Division.castIndex] using haR

/-- The singleton division of `Fin n` into `n` consecutive singleton parts. -/
def singleton (n : ℕ) : Division n n where
  part i := {i}
  part_nonempty i := ⟨i, by simp⟩
  part_disjoint := by
    intro i j hij
    simp [hij]
  part_cover := by
    intro x
    exact ⟨x, by simp⟩
  part_convex := by
    intro i a b c ha hc hab hbc
    have hai : a = i := by simpa using ha
    have hci : c = i := by simpa using hc
    subst a
    subst c
    have hbi : b = i := le_antisymm hbc hab
    simp [hbi]
  part_ordered := by
    intro i j hij a b ha hb
    have hai : a = i := by simpa using ha
    have hbj : b = j := by simpa using hb
    subst a
    subst b
    exact hij

/-- Number of pairs in a nontrivial finite interval.  For an interval of size
`l ≥ 2`, this is positive and equals `⌊l / 2⌋`. -/
def pairCount (l : ℕ) : ℕ :=
  l / 2

theorem pairCount_pos {l : ℕ} (hl : 2 ≤ l) : 0 < pairCount l := by
  unfold pairCount
  exact Nat.div_pos hl (by decide : 0 < 2)

/-- The left paired coarsening map: `0,1 ↦ 0`, `2,3 ↦ 1`, and so on, with the
last target index absorbing a possible leftover source index. -/
def pairLeftIndex {l : ℕ} (hl : 2 ≤ l) (a : Fin l) : Fin (pairCount l) :=
  ⟨min (a.1 / 2) (pairCount l - 1), by
    have hq : 0 < pairCount l := pairCount_pos hl
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

theorem pairLeftIndex_mono {l : ℕ} (hl : 2 ≤ l)
    {a b : Fin l} (hab : a ≤ b) :
    pairLeftIndex hl a ≤ pairLeftIndex hl b := by
  rw [Fin.le_iff_val_le_val]
  have habv : a.1 ≤ b.1 := Fin.le_iff_val_le_val.mp hab
  exact min_le_min (Nat.div_le_div_right habv) le_rfl

theorem pairLeftIndex_surjective {l : ℕ} (hl : 2 ≤ l) :
    ∀ j : Fin (pairCount l), ∃ a : Fin l, pairLeftIndex hl a = j := by
  intro j
  refine ⟨⟨2 * j.1, ?_⟩, ?_⟩
  · have hj : j.1 < l / 2 := j.2
    have hmul : 2 * j.1 < 2 * (l / 2) :=
      Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
    have hle : 2 * (l / 2) ≤ l := by
      calc
        2 * (l / 2) ≤ 2 * (l / 2) + l % 2 := Nat.le_add_right _ _
        _ = l := by rw [Nat.div_add_mod l 2]
    exact lt_of_lt_of_le hmul hle
  · ext
    have hjle : j.1 ≤ pairCount l - 1 := by omega
    have hjle' : j.1 ≤ l / 2 - 1 := by simpa [pairCount] using hjle
    simp [pairLeftIndex, pairCount, hjle']

/-- The left paired division of the index interval. -/
noncomputable def pairLeftIndexDivision (l : ℕ) (hl : 2 ≤ l) :
    Division l (pairCount l) :=
  ofMonotoneSurjective (pairLeftIndex hl)
    (fun _ _ hab => pairLeftIndex_mono hl hab)
    (pairLeftIndex_surjective hl)

/-- The cut index represented by a part of the left paired division.  The
`j`-th paired part always contains source indices `2*j` and `2*j+1`. -/
def pairLeftCutIndex {l : ℕ} (hl : 2 ≤ l) (j : Fin (pairCount l)) : Fin (l - 1) :=
  ⟨2 * j.1, by
    have hj : j.1 < l / 2 := j.2
    have hmul : 2 * j.1 < 2 * (l / 2) :=
      Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
    have hle : 2 * (l / 2) ≤ l := by
      calc
        2 * (l / 2) ≤ 2 * (l / 2) + l % 2 := Nat.le_add_right _ _
        _ = l := by rw [Nat.div_add_mod l 2]
    have hlt : 2 * j.1 < l := lt_of_lt_of_le hmul hle
    omega⟩

@[simp] theorem pairLeftIndex_pairLeftCutIndex_castSucc {l : ℕ} (hl : 2 ≤ l)
    (j : Fin (pairCount l)) :
    pairLeftIndex hl
        ((finCongr (by omega : l - 1 + 1 = l)) (pairLeftCutIndex hl j).castSucc) = j := by
  ext
  have hjle : j.1 ≤ pairCount l - 1 := by omega
  have hjle' : j.1 ≤ l / 2 - 1 := by simpa [pairCount] using hjle
  simp [pairLeftCutIndex, pairLeftIndex, pairCount, hjle']

@[simp] theorem pairLeftIndex_pairLeftCutIndex_succ {l : ℕ} (hl : 2 ≤ l)
    (j : Fin (pairCount l)) :
    pairLeftIndex hl
        ((finCongr (by omega : l - 1 + 1 = l)) (pairLeftCutIndex hl j).succ) = j := by
  ext
  have hjle : j.1 ≤ pairCount l - 1 := by omega
  have hjle' : j.1 ≤ l / 2 - 1 := by simpa [pairCount] using hjle
  have hdiv : (2 * j.1 + 1) / 2 = j.1 := by
    rw [show 2 * j.1 + 1 = 2 * j.1 + 1 by rfl]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [pairLeftCutIndex, pairLeftIndex, pairCount, hdiv, hjle']

theorem pairLeftIndex_val_bounds {l : ℕ} (hl : 2 ≤ l)
    {a : Fin l} {b : Fin (pairCount l)}
    (h : pairLeftIndex hl a = b) :
    2 * b.1 ≤ a.1 ∧ a.1 ≤ 2 * b.1 + 2 := by
  have hqpos : 0 < pairCount l := pairCount_pos hl
  have hbval : b.1 = min (a.1 / 2) (pairCount l - 1) := by
    simpa [pairLeftIndex] using congrArg Fin.val h.symm
  have hble_div : b.1 ≤ a.1 / 2 := by
    rw [hbval]
    exact Nat.min_le_left _ _
  have hleft : 2 * b.1 ≤ a.1 := by
    calc
      2 * b.1 ≤ 2 * (a.1 / 2) := Nat.mul_le_mul_left 2 hble_div
      _ ≤ a.1 := by
        calc
          2 * (a.1 / 2) ≤ 2 * (a.1 / 2) + a.1 % 2 := Nat.le_add_right _ _
          _ = a.1 := by rw [Nat.div_add_mod a.1 2]
  have hright : a.1 ≤ 2 * b.1 + 2 := by
    by_cases hbtop : b.1 = pairCount l - 1
    · have hlbound : l ≤ 2 * pairCount l + 1 := by
        unfold pairCount
        have h := Nat.div_add_mod l 2
        have hmod : l % 2 < 2 := Nat.mod_lt l (by decide : 0 < 2)
        omega
      have ha : a.1 + 1 ≤ l := Nat.succ_le_of_lt a.2
      omega
    · have hmin_left : min (a.1 / 2) (pairCount l - 1) = a.1 / 2 := by
        by_cases hle : a.1 / 2 ≤ pairCount l - 1
        · exact Nat.min_eq_left hle
        · have hmin : min (a.1 / 2) (pairCount l - 1) = pairCount l - 1 :=
            Nat.min_eq_right (le_of_not_ge hle)
          exact False.elim (hbtop (by omega))
      have hdiv : a.1 / 2 = b.1 := by omega
      have hmod : a.1 % 2 < 2 := Nat.mod_lt a.1 (by decide : 0 < 2)
      have hdecomp := Nat.div_add_mod a.1 2
      omega
  exact ⟨hleft, hright⟩

/-- The right paired coarsening map: the first source index is isolated, then
`1,2 ↦ 1`, `3,4 ↦ 2`, and so on, with the last target index absorbing any
leftover tail. -/
def pairRightIndex {l : ℕ} (hl : 2 ≤ l) (a : Fin l) : Fin (pairCount l) :=
  ⟨min ((a.1 + 1) / 2) (pairCount l - 1), by
    have hq : 0 < pairCount l := pairCount_pos hl
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

theorem pairRightIndex_mono {l : ℕ} (hl : 2 ≤ l)
    {a b : Fin l} (hab : a ≤ b) :
    pairRightIndex hl a ≤ pairRightIndex hl b := by
  rw [Fin.le_iff_val_le_val]
  have habv : a.1 ≤ b.1 := Fin.le_iff_val_le_val.mp hab
  have hplus : a.1 + 1 ≤ b.1 + 1 := Nat.succ_le_succ habv
  exact min_le_min (Nat.div_le_div_right hplus) le_rfl

theorem pairRightIndex_surjective {l : ℕ} (hl : 2 ≤ l) :
    ∀ j : Fin (pairCount l), ∃ a : Fin l, pairRightIndex hl a = j := by
  intro j
  by_cases hj0 : j.1 = 0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    ext
    simp [pairRightIndex, pairCount, hj0]
  · refine ⟨⟨2 * j.1 - 1, ?_⟩, ?_⟩
    · have hj : j.1 < l / 2 := j.2
      have hmul : 2 * j.1 < 2 * (l / 2) :=
        Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
      have hle : 2 * (l / 2) ≤ l := by
        calc
          2 * (l / 2) ≤ 2 * (l / 2) + l % 2 := Nat.le_add_right _ _
          _ = l := by rw [Nat.div_add_mod l 2]
      have hpos : 0 < 2 * j.1 := by omega
      exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le hmul hle)
    · ext
      have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj0
      have hjle : j.1 ≤ pairCount l - 1 := by omega
      have hjle' : j.1 ≤ l / 2 - 1 := by simpa [pairCount] using hjle
      have hval : (2 * j.1 - 1 + 1) / 2 = j.1 := by
        have hsub : 2 * j.1 - 1 + 1 = 2 * j.1 := by omega
        rw [hsub]
        exact Nat.mul_div_right j.1 (by decide : 0 < 2)
      simp [pairRightIndex, pairCount, hval, hjle']

/-- The right paired division of the index interval. -/
noncomputable def pairRightIndexDivision (l : ℕ) (hl : 2 ≤ l) :
    Division l (pairCount l) :=
  ofMonotoneSurjective (pairRightIndex hl)
    (fun _ _ hab => pairRightIndex_mono hl hab)
    (pairRightIndex_surjective hl)

theorem pairRightIndex_val_bounds {l : ℕ} (hl : 2 ≤ l)
    {a : Fin l} {b : Fin (pairCount l)}
    (h : pairRightIndex hl a = b) :
    2 * b.1 ≤ a.1 + 1 ∧ a.1 + 1 ≤ 2 * b.1 + 3 := by
  have hqpos : 0 < pairCount l := pairCount_pos hl
  have hbval : b.1 = min ((a.1 + 1) / 2) (pairCount l - 1) := by
    simpa [pairRightIndex] using congrArg Fin.val h.symm
  have hble_div : b.1 ≤ (a.1 + 1) / 2 := by
    rw [hbval]
    exact Nat.min_le_left _ _
  have hleft : 2 * b.1 ≤ a.1 + 1 := by
    calc
      2 * b.1 ≤ 2 * ((a.1 + 1) / 2) := Nat.mul_le_mul_left 2 hble_div
      _ ≤ a.1 + 1 := by
        calc
          2 * ((a.1 + 1) / 2) ≤
              2 * ((a.1 + 1) / 2) + (a.1 + 1) % 2 := Nat.le_add_right _ _
          _ = a.1 + 1 := by rw [Nat.div_add_mod (a.1 + 1) 2]
  have hright : a.1 + 1 ≤ 2 * b.1 + 3 := by
    by_cases hbtop : b.1 = pairCount l - 1
    · have hlbound : l ≤ 2 * pairCount l + 1 := by
        unfold pairCount
        have h := Nat.div_add_mod l 2
        have hmod : l % 2 < 2 := Nat.mod_lt l (by decide : 0 < 2)
        omega
      have ha : a.1 + 1 ≤ l := Nat.succ_le_of_lt a.2
      omega
    · have hmin_left : min ((a.1 + 1) / 2) (pairCount l - 1) = (a.1 + 1) / 2 := by
        by_cases hle : (a.1 + 1) / 2 ≤ pairCount l - 1
        · exact Nat.min_eq_left hle
        · have hmin :
              min ((a.1 + 1) / 2) (pairCount l - 1) = pairCount l - 1 :=
            Nat.min_eq_right (le_of_not_ge hle)
          exact False.elim (hbtop (by omega))
      have hdiv : (a.1 + 1) / 2 = b.1 := by omega
      have hmod : (a.1 + 1) % 2 < 2 := Nat.mod_lt (a.1 + 1) (by decide : 0 < 2)
      have hdecomp := Nat.div_add_mod (a.1 + 1) 2
      omega
  exact ⟨hleft, hright⟩

/-- Every adjacent pair of source indices is grouped by at least one of the two
paired coarsenings.  Even cuts are grouped by the left pairing and odd cuts by
the shifted right pairing. -/
theorem pairIndex_adjacent_same {l : ℕ} (hl : 2 ≤ l) (i : Fin (l - 1)) :
    pairLeftIndex hl ((finCongr (by omega : l - 1 + 1 = l)) i.castSucc) =
        pairLeftIndex hl ((finCongr (by omega : l - 1 + 1 = l)) i.succ) ∨
      pairRightIndex hl ((finCongr (by omega : l - 1 + 1 = l)) i.castSucc) =
        pairRightIndex hl ((finCongr (by omega : l - 1 + 1 = l)) i.succ) := by
  rcases Nat.mod_two_eq_zero_or_one i.1 with hmod | hmod
  · left
    ext
    have hi : i.1 = 2 * (i.1 / 2) := by
      have h := Nat.div_add_mod i.1 2
      omega
    have hdiv : (i.1 + 1) / 2 = i.1 / 2 := by
      rw [hi]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [pairLeftIndex, hdiv]
  · right
    ext
    have hi : i.1 = 2 * (i.1 / 2) + 1 := by
      have h := Nat.div_add_mod i.1 2
      omega
    have hdiv : (i.1 + 2) / 2 = (i.1 + 1) / 2 := by
      rw [hi]
      have h₁ : (2 * (i.1 / 2) + 1 + 2) / 2 = i.1 / 2 + 1 := by
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      have h₂ : (2 * (i.1 / 2) + 1 + 1) / 2 = i.1 / 2 + 1 := by
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      exact h₁.trans h₂.symm
    change
      min ((i.1 + 1) / 2) (pairCount l - 1) =
        min ((i.1 + 1 + 1) / 2) (pairCount l - 1)
    rw [show i.1 + 1 + 1 = i.1 + 2 by omega, hdiv]

/-- Adjacent-pair coverage in the common `k + 1` source-size form. -/
theorem pairIndex_adjacent_same_succ {k : ℕ} (hk : 0 < k) (i : Fin k) :
    pairLeftIndex (l := k + 1) (by omega) i.castSucc =
        pairLeftIndex (l := k + 1) (by omega) i.succ ∨
      pairRightIndex (l := k + 1) (by omega) i.castSucc =
        pairRightIndex (l := k + 1) (by omega) i.succ := by
  rcases Nat.mod_two_eq_zero_or_one i.1 with hmod | hmod
  · left
    ext
    have hi : i.1 = 2 * (i.1 / 2) := by
      have h := Nat.div_add_mod i.1 2
      omega
    have hdiv : (i.1 + 1) / 2 = i.1 / 2 := by
      rw [hi]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [pairLeftIndex, hdiv]
  · right
    ext
    have hi : i.1 = 2 * (i.1 / 2) + 1 := by
      have h := Nat.div_add_mod i.1 2
      omega
    have hdiv : (i.1 + 2) / 2 = (i.1 + 1) / 2 := by
      rw [hi]
      have h₁ : (2 * (i.1 / 2) + 1 + 2) / 2 = i.1 / 2 + 1 := by
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      have h₂ : (2 * (i.1 / 2) + 1 + 1) / 2 = i.1 / 2 + 1 := by
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      exact h₁.trans h₂.symm
    change
      min ((i.1 + 1) / 2) (pairCount (k + 1) - 1) =
      min ((i.1 + 1 + 1) / 2) (pairCount (k + 1) - 1)
    rw [show i.1 + 1 + 1 = i.1 + 2 by omega, hdiv]

/-- The left endpoint of a cut index, viewed as a source index. -/
def cutLeftIndex {l : ℕ} (j : Fin (l - 1)) : Fin l :=
  ⟨j.1, by omega⟩

/-- The right endpoint of a cut index, viewed as a source index. -/
def cutRightIndex {l : ℕ} (j : Fin (l - 1)) : Fin l :=
  ⟨j.1 + 1, by omega⟩

@[simp] theorem cutLeftIndex_val {l : ℕ} (j : Fin (l - 1)) :
    (cutLeftIndex j : Fin l).1 = j.1 := rfl

@[simp] theorem cutRightIndex_val {l : ℕ} (j : Fin (l - 1)) :
    (cutRightIndex j : Fin l).1 = j.1 + 1 := rfl

/-- The paired target used by the Lemma 13 counting proof for an original
zone/cut item.  Zones are assigned to the left pairing; a cut is assigned to
whichever of the two pairings groups its two adjacent column parts. -/
def pairedItemTarget {l : ℕ} (hl : 2 ≤ l) :
    Sum (Fin l) (Fin (l - 1)) → Sum (Fin (pairCount l)) (Fin (pairCount l))
  | Sum.inl j => Sum.inl (pairLeftIndex hl j)
  | Sum.inr j =>
      if _h :
          pairLeftIndex hl (cutLeftIndex j) =
            pairLeftIndex hl (cutRightIndex j) then
        Sum.inl (pairLeftIndex hl (cutLeftIndex j))
      else
        Sum.inr (pairRightIndex hl (cutLeftIndex j))

/-- A small local offset inside the paired target.  Together with
`pairedItemTarget`, this is injective; the target fiber size is therefore
bounded by `10`. -/
def pairedItemCode {l : ℕ} (hl : 2 ≤ l) :
    Sum (Fin l) (Fin (l - 1)) → Fin 10
  | Sum.inl j =>
      let b := pairLeftIndex hl j
      ⟨j.1 - 2 * b.1, by
        have hb := pairLeftIndex_val_bounds hl (a := j) (b := b) rfl
        omega⟩
  | Sum.inr j =>
      let j₀ : Fin l := cutLeftIndex j
      if h :
          pairLeftIndex hl j₀ =
            pairLeftIndex hl (cutRightIndex j) then
        let b := pairLeftIndex hl j₀
        ⟨3 + (j.1 - 2 * b.1), by
          have hb := pairLeftIndex_val_bounds hl (a := j₀) (b := b) rfl
          simp [j₀] at hb
          omega⟩
      else
        let b := pairRightIndex hl j₀
        ⟨6 + (j.1 + 1 - 2 * b.1), by
          have hb := pairRightIndex_val_bounds hl (a := j₀) (b := b) rfl
          simp [j₀] at hb
          omega⟩

/-- The paired target together with the local code determines the original
zone/cut item.  This finite-fiber estimate is used in the Lemma 13 counting
argument: at most ten original mixed items can be charged to one paired
auxiliary entry. -/
theorem pairedItemTarget_code_injective {l : ℕ} (hl : 2 ≤ l) :
    Function.Injective fun x : Sum (Fin l) (Fin (l - 1)) =>
      (pairedItemTarget hl x, pairedItemCode hl x) := by
  intro x y hxy
  have hcode : (pairedItemCode hl x).1 = (pairedItemCode hl y).1 := by
    simpa using congrArg (fun p => (p.2 : Fin 10).1) hxy
  cases x with
  | inl xz =>
      cases y with
      | inl yz =>
          have ht :
              pairLeftIndex hl xz = pairLeftIndex hl yz := by
            have h := congrArg Prod.fst hxy
            simpa [pairedItemTarget] using h
          have hc :
              xz.1 - 2 * (pairLeftIndex hl xz).1 =
                yz.1 - 2 * (pairLeftIndex hl yz).1 := by
            have h := congrArg (fun p => (p.2 : Fin 10).1) hxy
            simpa [pairedItemCode] using h
          have hx := pairLeftIndex_val_bounds hl (a := xz)
            (b := pairLeftIndex hl xz) rfl
          have hy := pairLeftIndex_val_bounds hl (a := yz)
            (b := pairLeftIndex hl yz) rfl
          have hval : xz.1 = yz.1 := by
            have htv : (pairLeftIndex hl xz).1 = (pairLeftIndex hl yz).1 := by
              exact congrArg Fin.val ht
            omega
          apply congrArg Sum.inl
          exact Fin.ext hval
      | inr yc =>
          by_cases hyleft :
              pairLeftIndex hl (cutLeftIndex yc) =
                pairLeftIndex hl (cutRightIndex yc)
          · have hxcode : (pairedItemCode hl (Sum.inl xz)).1 < 3 := by
              have hb := pairLeftIndex_val_bounds hl (a := xz)
                (b := pairLeftIndex hl xz) rfl
              simp [pairedItemCode]
              omega
            have hycode : 3 ≤ (pairedItemCode hl (Sum.inr yc)).1 := by
              let y₀ : Fin l := cutLeftIndex yc
              have hb := pairLeftIndex_val_bounds hl (a := y₀)
                (b := pairLeftIndex hl y₀) rfl
              simp [pairedItemCode, hyleft, y₀] at hb ⊢
            have hcode' :
                (pairedItemCode hl (Sum.inl xz)).1 =
                  (pairedItemCode hl (Sum.inr yc)).1 := hcode
            omega
          · have hxcode : (pairedItemCode hl (Sum.inl xz)).1 < 3 := by
              have hb := pairLeftIndex_val_bounds hl (a := xz)
                (b := pairLeftIndex hl xz) rfl
              simp [pairedItemCode]
              omega
            have hycode : 3 ≤ (pairedItemCode hl (Sum.inr yc)).1 := by
              let y₀ : Fin l := cutLeftIndex yc
              have hb := pairRightIndex_val_bounds hl (a := y₀)
                (b := pairRightIndex hl y₀) rfl
              simp [pairedItemCode, hyleft, y₀] at hb ⊢
              omega
            have hcode' :
                (pairedItemCode hl (Sum.inl xz)).1 =
                  (pairedItemCode hl (Sum.inr yc)).1 := hcode
            omega
  | inr xc =>
      cases y with
      | inl yz =>
          by_cases hxleft :
              pairLeftIndex hl (cutLeftIndex xc) =
                pairLeftIndex hl (cutRightIndex xc)
          · have hxcode : 3 ≤ (pairedItemCode hl (Sum.inr xc)).1 := by
              let x₀ : Fin l := cutLeftIndex xc
              have hb := pairLeftIndex_val_bounds hl (a := x₀)
                (b := pairLeftIndex hl x₀) rfl
              simp [pairedItemCode, hxleft, x₀] at hb ⊢
            have hycode : (pairedItemCode hl (Sum.inl yz)).1 < 3 := by
              have hb := pairLeftIndex_val_bounds hl (a := yz)
                (b := pairLeftIndex hl yz) rfl
              simp [pairedItemCode]
              omega
            have hcode' :
                (pairedItemCode hl (Sum.inr xc)).1 =
                  (pairedItemCode hl (Sum.inl yz)).1 := hcode
            omega
          · have hxcode : 3 ≤ (pairedItemCode hl (Sum.inr xc)).1 := by
              let x₀ : Fin l := cutLeftIndex xc
              have hb := pairRightIndex_val_bounds hl (a := x₀)
                (b := pairRightIndex hl x₀) rfl
              simp [pairedItemCode, hxleft, x₀] at hb ⊢
              omega
            have hycode : (pairedItemCode hl (Sum.inl yz)).1 < 3 := by
              have hb := pairLeftIndex_val_bounds hl (a := yz)
                (b := pairLeftIndex hl yz) rfl
              simp [pairedItemCode]
              omega
            have hcode' :
                (pairedItemCode hl (Sum.inr xc)).1 =
                  (pairedItemCode hl (Sum.inl yz)).1 := hcode
            omega
      | inr yc =>
          by_cases hxleft :
              pairLeftIndex hl (cutLeftIndex xc) =
                pairLeftIndex hl (cutRightIndex xc)
          · by_cases hyleft :
              pairLeftIndex hl (cutLeftIndex yc) =
                pairLeftIndex hl (cutRightIndex yc)
            · have ht :
                pairLeftIndex hl (cutLeftIndex xc) =
                  pairLeftIndex hl (cutLeftIndex yc) := by
                have h := congrArg Prod.fst hxy
                simpa [pairedItemTarget, hxleft, hyleft] using h
              let x₀ : Fin l := cutLeftIndex xc
              let y₀ : Fin l := cutLeftIndex yc
              have hc :
                  3 + (xc.1 - 2 * (pairLeftIndex hl x₀).1) =
                    3 + (yc.1 - 2 * (pairLeftIndex hl y₀).1) := by
                have h := congrArg (fun p => (p.2 : Fin 10).1) hxy
                simpa [pairedItemTarget, pairedItemCode, x₀, y₀, hxleft, hyleft] using h
              have hx := pairLeftIndex_val_bounds hl (a := x₀)
                (b := pairLeftIndex hl x₀) rfl
              have hy := pairLeftIndex_val_bounds hl (a := y₀)
                (b := pairLeftIndex hl y₀) rfl
              have hval : xc.1 = yc.1 := by
                have htv : (pairLeftIndex hl x₀).1 = (pairLeftIndex hl y₀).1 := by
                  simpa [x₀, y₀] using congrArg Fin.val ht
                have hdiff :
                    xc.1 - 2 * (pairLeftIndex hl x₀).1 =
                      yc.1 - 2 * (pairLeftIndex hl y₀).1 := by
                  omega
                have hxge : 2 * (pairLeftIndex hl x₀).1 ≤ xc.1 := by
                  simpa [x₀] using hx.1
                have hyge : 2 * (pairLeftIndex hl y₀).1 ≤ yc.1 := by
                  simpa [y₀] using hy.1
                simp [x₀] at hx
                simp [y₀] at hy
                omega
              apply congrArg Sum.inr
              exact Fin.ext hval
            · have hxcode : (pairedItemCode hl (Sum.inr xc)).1 < 6 := by
                let x₀ : Fin l := cutLeftIndex xc
                have hb := pairLeftIndex_val_bounds hl (a := x₀)
                  (b := pairLeftIndex hl x₀) rfl
                simp [pairedItemCode, hxleft, x₀] at hb ⊢
                omega
              have hycode : 6 ≤ (pairedItemCode hl (Sum.inr yc)).1 := by
                let y₀ : Fin l := cutLeftIndex yc
                have hb := pairRightIndex_val_bounds hl (a := y₀)
                  (b := pairRightIndex hl y₀) rfl
                simp [pairedItemCode, hyleft, y₀] at hb ⊢
              omega
          · by_cases hyleft :
              pairLeftIndex hl (cutLeftIndex yc) =
                pairLeftIndex hl (cutRightIndex yc)
            · have hxcode : 6 ≤ (pairedItemCode hl (Sum.inr xc)).1 := by
                let x₀ : Fin l := cutLeftIndex xc
                have hb := pairRightIndex_val_bounds hl (a := x₀)
                  (b := pairRightIndex hl x₀) rfl
                simp [pairedItemCode, hxleft, x₀] at hb ⊢
              have hycode : (pairedItemCode hl (Sum.inr yc)).1 < 6 := by
                let y₀ : Fin l := cutLeftIndex yc
                have hb := pairLeftIndex_val_bounds hl (a := y₀)
                  (b := pairLeftIndex hl y₀) rfl
                simp [pairedItemCode, hyleft, y₀] at hb ⊢
                omega
              omega
            · have ht :
                pairRightIndex hl (cutLeftIndex xc) =
                  pairRightIndex hl (cutLeftIndex yc) := by
                have h := congrArg Prod.fst hxy
                simpa [pairedItemTarget, hxleft, hyleft] using h
              let x₀ : Fin l := cutLeftIndex xc
              let y₀ : Fin l := cutLeftIndex yc
              have hc :
                  6 + (xc.1 + 1 - 2 * (pairRightIndex hl x₀).1) =
                    6 + (yc.1 + 1 - 2 * (pairRightIndex hl y₀).1) := by
                have h := congrArg (fun p => (p.2 : Fin 10).1) hxy
                simpa [pairedItemCode, x₀, y₀, hxleft, hyleft] using h
              have hx := pairRightIndex_val_bounds hl (a := x₀)
                (b := pairRightIndex hl x₀) rfl
              have hy := pairRightIndex_val_bounds hl (a := y₀)
                (b := pairRightIndex hl y₀) rfl
              have hval : xc.1 = yc.1 := by
                have htv : (pairRightIndex hl x₀).1 = (pairRightIndex hl y₀).1 := by
                  simpa [x₀, y₀] using congrArg Fin.val ht
                have hdiff :
                    xc.1 + 1 - 2 * (pairRightIndex hl x₀).1 =
                      yc.1 + 1 - 2 * (pairRightIndex hl y₀).1 := by
                  omega
                have hxge : 2 * (pairRightIndex hl x₀).1 ≤ xc.1 + 1 := by
                  simpa [x₀] using hx.1
                have hyge : 2 * (pairRightIndex hl y₀).1 ≤ yc.1 + 1 := by
                  simpa [y₀] using hy.1
                simp [x₀] at hx
                simp [y₀] at hy
                omega
              apply congrArg Sum.inr
              exact Fin.ext hval

/-- Cast the common `k + 1` item type to the generic `l`/`l - 1` item type. -/
def pairedItemCastSucc {k : ℕ} :
    Sum (Fin (k + 1)) (Fin k) → Sum (Fin (k + 1)) (Fin ((k + 1) - 1))
  | Sum.inl j => Sum.inl j
  | Sum.inr j => Sum.inr ((finCongr (by omega : k = (k + 1) - 1)) j)

theorem pairedItemCastSucc_injective {k : ℕ} :
    Function.Injective (pairedItemCastSucc (k := k)) := by
  intro x y hxy
  cases x with
  | inl xz =>
      cases y with
      | inl yz =>
          apply congrArg Sum.inl
          simpa [pairedItemCastSucc] using hxy
      | inr yc =>
          simp [pairedItemCastSucc] at hxy
  | inr xc =>
      cases y with
      | inl yz =>
          simp [pairedItemCastSucc] at hxy
      | inr yc =>
          apply congrArg Sum.inr
          have h :
              (finCongr (by omega : k = (k + 1) - 1)) xc =
                (finCongr (by omega : k = (k + 1) - 1)) yc := by
            simpa [pairedItemCastSucc] using hxy
          exact (finCongr (by omega : k = (k + 1) - 1)).injective h

/-- Paired target in the common `k + 1` source-size form. -/
def pairedItemTargetSucc {k : ℕ} (hk : 0 < k) :
    Sum (Fin (k + 1)) (Fin k) →
      Sum (Fin (pairCount (k + 1))) (Fin (pairCount (k + 1))) :=
  fun x => pairedItemTarget (l := k + 1) (by omega) (pairedItemCastSucc x)

/-- Local code in the common `k + 1` source-size form. -/
def pairedItemCodeSucc {k : ℕ} (hk : 0 < k) :
    Sum (Fin (k + 1)) (Fin k) → Fin 10 :=
  fun x => pairedItemCode (l := k + 1) (by omega) (pairedItemCastSucc x)

@[simp] theorem pairedItemTargetSucc_zone {k : ℕ} (hk : 0 < k)
    (j : Fin (k + 1)) :
    pairedItemTargetSucc hk (Sum.inl j) =
      Sum.inl (pairLeftIndex (l := k + 1) (by omega) j) := by
  simp [pairedItemTargetSucc, pairedItemCastSucc, pairedItemTarget]

theorem pairedItemTargetSucc_cut_left {k : ℕ} (hk : 0 < k)
    (j : Fin k)
    (hleft :
      pairLeftIndex (l := k + 1) (by omega) j.castSucc =
        pairLeftIndex (l := k + 1) (by omega) j.succ) :
    pairedItemTargetSucc hk (Sum.inr j) =
      Sum.inl (pairLeftIndex (l := k + 1) (by omega) j.succ) := by
  unfold pairedItemTargetSucc pairedItemCastSucc pairedItemTarget
  simp only
  rw [dif_pos]
  · simpa [cutLeftIndex, cutRightIndex] using hleft
  · simpa [cutLeftIndex, cutRightIndex] using hleft

theorem pairedItemTargetSucc_cut_right {k : ℕ} (hk : 0 < k)
    (j : Fin k)
    (hleft :
      ¬ pairLeftIndex (l := k + 1) (by omega) j.castSucc =
        pairLeftIndex (l := k + 1) (by omega) j.succ) :
    pairedItemTargetSucc hk (Sum.inr j) =
      Sum.inr (pairRightIndex (l := k + 1) (by omega) j.castSucc) := by
  unfold pairedItemTargetSucc pairedItemCastSucc pairedItemTarget
  simp only
  rw [dif_neg]
  · apply congrArg Sum.inr
    ext
    change
      min ((j.1 + 1) / 2) (pairCount (k + 1) - 1) =
        min ((j.1 + 1) / 2) (pairCount (k + 1) - 1)
    rfl
  · intro h
    exact hleft (by simpa [cutLeftIndex, cutRightIndex] using h)

theorem pairedItemTargetSucc_code_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective fun x : Sum (Fin (k + 1)) (Fin k) =>
      (pairedItemTargetSucc hk x, pairedItemCodeSucc hk x) := by
  intro x y hxy
  have h :
      (pairedItemTarget (l := k + 1) (by omega) (pairedItemCastSucc x),
          pairedItemCode (l := k + 1) (by omega) (pairedItemCastSucc x)) =
        (pairedItemTarget (l := k + 1) (by omega) (pairedItemCastSucc y),
          pairedItemCode (l := k + 1) (by omega) (pairedItemCastSucc y)) := by
    simpa [pairedItemTargetSucc, pairedItemCodeSucc] using hxy
  exact pairedItemCastSucc_injective
    (pairedItemTarget_code_injective (l := k + 1) (by omega) h)

/-- Index map that identifies the two consecutive indices `i` and `i+1`.

It is the order-preserving surjection used to build the index division for a
fusion.  Values up to `i` are kept unchanged; values after `i` are shifted down
by one. -/
def fuseIndex {k : ℕ} (i : Fin (k + 1)) (a : Fin (k + 2)) : Fin (k + 1) :=
  if h : a.1 ≤ i.1 then
    ⟨a.1, lt_of_le_of_lt h i.2⟩
  else
    ⟨a.1 - 1, by omega⟩

theorem fuseIndex_mono {k : ℕ} (i : Fin (k + 1))
    {a b : Fin (k + 2)} (hab : a ≤ b) :
    fuseIndex i a ≤ fuseIndex i b := by
  rw [Fin.le_iff_val_le_val]
  have habv : a.1 ≤ b.1 := Fin.le_iff_val_le_val.mp hab
  by_cases ha : a.1 ≤ i.1 <;> by_cases hb : b.1 ≤ i.1 <;>
    simp [fuseIndex, ha, hb] <;> omega

/-- The division of the index interval which groups exactly the two adjacent
indices `i` and `i+1`, leaving all other indices as singleton parts. -/
noncomputable def fusionIndexDivision {k : ℕ} (i : Fin (k + 1)) :
    Division (k + 2) (k + 1) where
  part j := (Finset.univ : Finset (Fin (k + 2))).filter fun a => fuseIndex i a = j
  part_nonempty := by
    intro j
    by_cases hji : j ≤ i
    · refine ⟨j.castSucc, ?_⟩
      have hval : j.1 ≤ i.1 := Fin.le_iff_val_le_val.mp hji
      have hidx : fuseIndex i j.castSucc = j := by
        ext
        unfold fuseIndex
        simp [hval]
      simp [hidx]
    · refine ⟨j.succ, ?_⟩
      have hij : i < j := lt_of_not_ge hji
      have hlt : i.1 < j.1 := Fin.mk_lt_mk.mp hij
      have hnot : ¬ j.1 + 1 ≤ i.1 := by omega
      have hidx : fuseIndex i j.succ = j := by
        ext
        unfold fuseIndex
        simp [hnot]
      simp [hidx]
  part_disjoint := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro x hx hy
    have hx' : fuseIndex i x = a := by simpa using hx
    have hy' : fuseIndex i x = b := by simpa using hy
    exact hab (hx'.symm.trans hy')
  part_cover := by
    intro x
    exact ⟨fuseIndex i x, by simp⟩
  part_convex := by
    intro j a b c ha hc hab hbc
    have ha' : fuseIndex i a = j := by simpa using ha
    have hc' : fuseIndex i c = j := by simpa using hc
    have hab' : fuseIndex i a ≤ fuseIndex i b := fuseIndex_mono i hab
    have hbc' : fuseIndex i b ≤ fuseIndex i c := fuseIndex_mono i hbc
    have hb' : fuseIndex i b = j := by
      exact le_antisymm (by simpa [hc'] using hbc') (by simpa [ha'] using hab')
    simp [hb']
  part_ordered := by
    intro a b hab x y hx hy
    have hx' : fuseIndex i x = a := by simpa using hx
    have hy' : fuseIndex i y = b := by simpa using hy
    by_contra hnot
    have hyx : y ≤ x := le_of_not_gt hnot
    have hmono : fuseIndex i y ≤ fuseIndex i x := fuseIndex_mono i hyx
    have hba : b ≤ a := by simpa [hx', hy'] using hmono
    exact (not_lt_of_ge hba) hab

@[simp] theorem mem_fusionIndexDivision_part {k : ℕ}
    (i : Fin (k + 1)) (j : Fin (k + 1)) (a : Fin (k + 2)) :
    a ∈ (fusionIndexDivision i).part j ↔ fuseIndex i a = j := by
  simp [fusionIndexDivision]

theorem fuseIndex_eq_self_iff {k : ℕ}
    (i : Fin (k + 1)) (a : Fin (k + 2)) :
    fuseIndex i a = i ↔ a = i.castSucc ∨ a = i.succ := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    by_cases ha : a.1 ≤ i.1
    · left
      ext
      simp [fuseIndex, ha] at hv
      exact hv
    · right
      ext
      simp [fuseIndex, ha] at hv
      change a.1 = i.1 + 1
      omega
  · intro h
    rcases h with rfl | rfl
    · ext
      simp [fuseIndex]
    · ext
      have hnot : ¬ i.1 + 1 ≤ i.1 := by omega
      simp [fuseIndex, hnot]

theorem fuseIndex_eq_of_lt_iff {k : ℕ}
    {i j : Fin (k + 1)} (hji : j < i) (a : Fin (k + 2)) :
    fuseIndex i a = j ↔ a = j.castSucc := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    have hlt : j.1 < i.1 := Fin.mk_lt_mk.mp hji
    by_cases ha : a.1 ≤ i.1
    · ext
      simp [fuseIndex, ha] at hv
      exact hv
    · simp [fuseIndex, ha] at hv
      omega
  · intro h
    subst a
    ext
    have hle : j.1 ≤ i.1 := le_of_lt (Fin.mk_lt_mk.mp hji)
    simp [fuseIndex, hle]

theorem fuseIndex_eq_of_gt_iff {k : ℕ}
    {i j : Fin (k + 1)} (hij : i < j) (a : Fin (k + 2)) :
    fuseIndex i a = j ↔ a = j.succ := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    have hlt : i.1 < j.1 := Fin.mk_lt_mk.mp hij
    by_cases ha : a.1 ≤ i.1
    · simp [fuseIndex, ha] at hv
      omega
    · ext
      simp [fuseIndex, ha] at hv
      change a.1 = j.1 + 1
      omega
  · intro h
    subst a
    ext
    have hnot : ¬ j.1 + 1 ≤ i.1 := by
      have hlt : i.1 < j.1 := Fin.mk_lt_mk.mp hij
      omega
    simp [fuseIndex, hnot]

/-- The part family obtained by merging the consecutive parts `i` and `i+1`
of a division with `k+2` parts. -/
noncomputable def fusePart {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) (j : Fin (k + 1)) : Finset (Fin n) :=
  if j = i then
    D.part i.castSucc ∪ D.part i.succ
  else if j < i then
    D.part j.castSucc
  else
    D.part j.succ

@[simp] theorem fusePart_self {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    D.fusePart i i = D.part i.castSucc ∪ D.part i.succ := by
  simp [fusePart]

/-- `E` is obtained from `D` by merging the consecutive parts `i` and `i+1`. -/
def IsFusionAt {k : ℕ} (D : Division n (k + 2))
    (E : Division n (k + 1)) (i : Fin (k + 1)) : Prop :=
  ∀ j : Fin (k + 1), E.part j = D.fusePart i j

/-- Coarsen a division by grouping consecutive indices according to another
division of the index set. -/
noncomputable def coarsen {t : ℕ} (D : Division n k) (I : Division k t) :
    Division n t where
  part a := (I.part a).biUnion fun i => D.part i
  part_nonempty := by
    intro a
    classical
    rcases I.part_nonempty a with ⟨i, hi⟩
    rcases D.part_nonempty i with ⟨x, hx⟩
    exact ⟨x, Finset.mem_biUnion.mpr ⟨i, hi, hx⟩⟩
  part_disjoint := by
    intro a b hab
    classical
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    rcases Finset.mem_biUnion.mp hy with ⟨j, hj, hxj⟩
    have hij : i ≠ j := by
      intro hij
      subst j
      exact Finset.disjoint_left.mp (I.part_disjoint hab) hi hj
    exact Finset.disjoint_left.mp (D.part_disjoint hij) hxi hxj
  part_cover := by
    intro x
    classical
    rcases D.part_cover x with ⟨i, hi⟩
    rcases I.part_cover i with ⟨a, ha⟩
    exact ⟨a, Finset.mem_biUnion.mpr ⟨i, ha, hi⟩⟩
  part_convex := by
    intro a x y z hx hz hxy hyz
    classical
    rcases Finset.mem_biUnion.mp hx with ⟨ix, hix, hxD⟩
    rcases Finset.mem_biUnion.mp hz with ⟨iz, hiz, hzD⟩
    rcases D.part_cover y with ⟨iy, hyD⟩
    have hix_le_iy : ix ≤ iy := by
      by_contra hnot
      have hlt : iy < ix := lt_of_not_ge hnot
      have hyx : y < x := D.part_ordered hlt hyD hxD
      exact (not_lt_of_ge hxy) hyx
    have hiy_le_iz : iy ≤ iz := by
      by_contra hnot
      have hlt : iz < iy := lt_of_not_ge hnot
      have hzy : z < y := D.part_ordered hlt hzD hyD
      exact (not_lt_of_ge hyz) hzy
    have hiy : iy ∈ I.part a := I.part_convex a hix hiz hix_le_iy hiy_le_iz
    exact Finset.mem_biUnion.mpr ⟨iy, hiy, hyD⟩
  part_ordered := by
    intro a b hab x y hx hy
    classical
    rcases Finset.mem_biUnion.mp hx with ⟨ix, hix, hxD⟩
    rcases Finset.mem_biUnion.mp hy with ⟨iy, hiy, hyD⟩
    exact D.part_ordered (I.part_ordered hab hix hiy) hxD hyD

theorem part_subset_coarsen_part {t : ℕ} (D : Division n k) (I : Division k t)
    {a : Fin t} {i : Fin k} (hi : i ∈ I.part a) :
    D.part i ⊆ (D.coarsen I).part a := by
  classical
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩

/-- Fuse the two consecutive parts `i` and `i+1` of a division. -/
noncomputable def fuse {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) : Division n (k + 1) :=
  D.coarsen (fusionIndexDivision i)

theorem coarsen_fusionIndexDivision_part_eq_fusePart {k : ℕ}
    (D : Division n (k + 2)) (i : Fin (k + 1)) (j : Fin (k + 1)) :
    (D.coarsen (fusionIndexDivision i)).part j = D.fusePart i j := by
  classical
  ext x
  by_cases heq : j = i
  · subst j
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
      have hidx : fuseIndex i a = i := (mem_fusionIndexDivision_part i i a).mp ha
      rcases (fuseIndex_eq_self_iff i a).mp hidx with rfl | rfl
      · simp [fusePart, hxa]
      · simp [fusePart, hxa]
    · intro hx
      rw [fusePart_self] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · refine Finset.mem_biUnion.mpr ⟨i.castSucc, ?_, hx⟩
        exact (mem_fusionIndexDivision_part i i i.castSucc).mpr
          ((fuseIndex_eq_self_iff i i.castSucc).mpr (Or.inl rfl))
      · refine Finset.mem_biUnion.mpr ⟨i.succ, ?_, hx⟩
        exact (mem_fusionIndexDivision_part i i i.succ).mpr
          ((fuseIndex_eq_self_iff i i.succ).mpr (Or.inr rfl))
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · constructor
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
        have hidx : fuseIndex i a = j := (mem_fusionIndexDivision_part i j a).mp ha
        have ha' : a = j.castSucc := (fuseIndex_eq_of_lt_iff hlt a).mp hidx
        subst a
        simpa [fusePart, heq, hlt] using hxa
      · intro hx
        refine Finset.mem_biUnion.mpr ⟨j.castSucc, ?_, ?_⟩
        · exact (mem_fusionIndexDivision_part i j j.castSucc).mpr
            ((fuseIndex_eq_of_lt_iff hlt j.castSucc).mpr rfl)
        · simpa [fusePart, heq, hlt] using hx
    · have hnlt : ¬ j < i := not_lt_of_ge (le_of_lt hgt)
      constructor
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
        have hidx : fuseIndex i a = j := (mem_fusionIndexDivision_part i j a).mp ha
        have ha' : a = j.succ := (fuseIndex_eq_of_gt_iff hgt a).mp hidx
        subst a
        simpa [fusePart, heq, hnlt] using hxa
      · intro hx
        refine Finset.mem_biUnion.mpr ⟨j.succ, ?_, ?_⟩
        · exact (mem_fusionIndexDivision_part i j j.succ).mpr
            ((fuseIndex_eq_of_gt_iff hgt j.succ).mpr rfl)
        · simpa [fusePart, heq, hnlt] using hx

theorem isFusionAt_fuse {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    IsFusionAt D (D.fuse i) i := by
  intro j
  exact coarsen_fusionIndexDivision_part_eq_fusePart D i j

theorem fuse_part_self {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    (D.fuse i).part i = D.part i.castSucc ∪ D.part i.succ :=
  by simpa [fuse] using isFusionAt_fuse D i i

theorem fuse_part_of_lt {k : ℕ} (D : Division n (k + 2))
    {i j : Fin (k + 1)} (hji : j < i) :
    (D.fuse i).part j = D.part j.castSucc := by
  rw [isFusionAt_fuse D i j]
  simp [fusePart, ne_of_lt hji, hji]

theorem fuse_part_of_gt {k : ℕ} (D : Division n (k + 2))
    {i j : Fin (k + 1)} (hij : i < j) :
    (D.fuse i).part j = D.part j.succ := by
  rw [isFusionAt_fuse D i j]
  have hne : j ≠ i := ne_of_gt hij
  have hnlt : ¬ j < i := not_lt_of_ge (le_of_lt hij)
  simp [fusePart, hne, hnlt]

/-- The first element of a fused part is the first element of the left old
part. -/
theorem first_fuse_self {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    (D.fuse i).first i = D.first i.castSucc := by
  classical
  apply
    (Finset.min'_eq_iff ((D.fuse i).part i)
      ((D.fuse i).part_nonempty i) (D.first i.castSucc)).mpr
  constructor
  · rw [fuse_part_self]
    exact Finset.mem_union_left _ (D.first_mem i.castSucc)
  · intro x hx
    rw [fuse_part_self] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.min'_le _ _ hx
    · exact le_of_lt (D.part_ordered (by simp) (D.first_mem i.castSucc) hx)

/-- The last element of a fused part is the last element of the right old
part. -/
theorem last_fuse_self {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    (D.fuse i).last i = D.last i.succ := by
  classical
  apply
    (Finset.max'_eq_iff ((D.fuse i).part i)
      ((D.fuse i).part_nonempty i) (D.last i.succ)).mpr
  constructor
  · rw [fuse_part_self]
    exact Finset.mem_union_right _ (D.last_mem i.succ)
  · intro x hx
    rw [fuse_part_self] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact le_of_lt (D.part_ordered (by simp) hx (D.last_mem i.succ))
    · exact Finset.le_max' _ _ hx

/-- The set of parts of a fused division is obtained by replacing the two
fused source parts by their union. -/
theorem parts_eq_insert_erase_of_isFusionAt {n k : ℕ}
    {D : Division n (k + 2)} {E : Division n (k + 1)} {i : Fin (k + 1)}
    (h : IsFusionAt D E i) :
    ((Finset.univ : Finset (Fin (k + 1))).map ⟨E.part, E.part_injective⟩) =
      insert (D.part i.castSucc ∪ D.part i.succ)
        ((((Finset.univ : Finset (Fin (k + 2))).map ⟨D.part, D.part_injective⟩).erase
          (D.part i.castSucc)).erase (D.part i.succ)) := by
  classical
  ext R
  constructor
  · intro hR
    rcases Finset.mem_map.mp hR with ⟨j, _hj, hjR⟩
    change E.part j = R at hjR
    rw [← hjR]
    by_cases hji : j = i
    · subst j
      exact Finset.mem_insert.mpr (Or.inl (by simp [h i, fusePart]))
    · rcases lt_or_gt_of_ne hji with hlt | hgt
      · have hpart : E.part j = D.part j.castSucc := by
          rw [h j]
          simp [fusePart, hji, hlt]
        rw [hpart]
        refine Finset.mem_insert.mpr (Or.inr ?_)
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro heq
          have hidx := D.part_injective heq
          have hv := congrArg Fin.val hidx
          simp at hv
          omega
        · refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · intro heq
            have hidx := D.part_injective heq
            have hv := congrArg Fin.val hidx
            simp at hv
            omega
          · exact Finset.mem_map.mpr ⟨j.castSucc, Finset.mem_univ _, rfl⟩
      · have hpart : E.part j = D.part j.succ := by
          rw [h j]
          have hnlt : ¬ j < i := not_lt_of_ge (le_of_lt hgt)
          simp [fusePart, hji, hnlt]
        rw [hpart]
        refine Finset.mem_insert.mpr (Or.inr ?_)
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro heq
          have hidx := D.part_injective heq
          have hv := congrArg Fin.val hidx
          simp at hv
          omega
        · refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · intro heq
            have hidx := D.part_injective heq
            have hv := congrArg Fin.val hidx
            simp at hv
            omega
          · exact Finset.mem_map.mpr ⟨j.succ, Finset.mem_univ _, rfl⟩
  · intro hR
    rcases Finset.mem_insert.mp hR with hR | hR
    · refine Finset.mem_map.mpr ⟨i, Finset.mem_univ _, ?_⟩
      change E.part i = R
      rw [h i]
      rw [hR]
      simp [fusePart]
    · rcases Finset.mem_erase.mp hR with ⟨hR_ne_succ, hR_old_erase⟩
      rcases Finset.mem_erase.mp hR_old_erase with ⟨hR_ne_cast, hR_old⟩
      rcases Finset.mem_map.mp hR_old with ⟨a, _ha, haR⟩
      change D.part a = R at haR
      by_cases hai : a.1 ≤ i.1
      · have hlt_ai : a.1 < i.1 := by
          have hne : a ≠ i.castSucc := by
            intro hae
            exact hR_ne_cast (by rw [← haR, hae])
          by_contra hnot
          have hge : i.1 ≤ a.1 := le_of_not_gt hnot
          have hval : a.1 = i.1 := le_antisymm hai hge
          apply hne
          ext
          simpa using hval
        let j : Fin (k + 1) := ⟨a.1, by omega⟩
        refine Finset.mem_map.mpr ⟨j, Finset.mem_univ _, ?_⟩
        change E.part j = R
        rw [h j]
        have hji : j < i := Fin.mk_lt_mk.mpr hlt_ai
        have hneji : j ≠ i := ne_of_lt hji
        simp [fusePart, hneji, hji]
        rw [← haR]
        congr
      · have hgt_i_a : i.1 + 1 < a.1 := by
          have hgt : i.1 < a.1 := lt_of_not_ge hai
          have hne : a ≠ i.succ := by
            intro hae
            exact hR_ne_succ (by rw [← haR, hae])
          by_contra hnot
          have hle : a.1 ≤ i.1 + 1 := le_of_not_gt hnot
          have hval : a.1 = i.1 + 1 := le_antisymm hle hgt
          apply hne
          ext
          simpa using hval
        let j : Fin (k + 1) := ⟨a.1 - 1, by omega⟩
        refine Finset.mem_map.mpr ⟨j, Finset.mem_univ _, ?_⟩
        change E.part j = R
        rw [h j]
        have hij : i < j := Fin.mk_lt_mk.mpr (by omega)
        have hneji : j ≠ i := ne_of_gt hij
        have hnlt : ¬ j < i := not_lt_of_ge (le_of_lt hij)
        simp [fusePart, hneji, hnlt]
        rw [← haR]
        congr
        ext
        dsimp [j]
        omega

end Division

end Lax2Proofs.TwinWidth
