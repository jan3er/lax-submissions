import Lax5.NowhereDenseClasses
import Lax12.NowhereDenseUQW
import Mathlib.Data.Set.Card

/-!
Uniform quasi-wideness in the shape the Adler–Adler argument consumes.
Nothing is proved here: uniform quasi-wideness of a nowhere dense class is
*assumed* from the `sparsity-lectures` submission
(`Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense`), and this file
only transports it across the nominal duplication of the two submissions'
definitions — the shallow-minor models have literally the same fields, so
the transport is a field-for-field repacking, and the `Set`-valued
conclusion is converted to the `Finset` form the caller uses.
-/

namespace Lax5Proofs.QuasiWideness

open Lax5.GraphClasses
open Lax12.UniformQuasiWideness

/-- Repack a shallow-minor model of the `sparsity-lectures` submission as
the identically shaped model of this submission. -/
def shallowMinorModel_lax5 {V W : Type*} {r : ℕ} {H : SimpleGraph W}
    {G : SimpleGraph V} (M : Lax12.NowhereDenseClasses.ShallowMinorModel r H G) :
    Lax5.NowhereDenseClasses.ShallowMinorModel r H G where
  branch := M.branch
  center := M.center
  center_mem := M.center_mem
  disjoint := M.disjoint
  radius_le := M.radius_le
  adj := M.adj

/-- Repack a shallow-minor model of this submission as the identically
shaped model of the `sparsity-lectures` submission. -/
def shallowMinorModel_lax12 {V W : Type*} {r : ℕ} {H : SimpleGraph W}
    {G : SimpleGraph V} (M : Lax5.NowhereDenseClasses.ShallowMinorModel r H G) :
    Lax12.NowhereDenseClasses.ShallowMinorModel r H G where
  branch := M.branch
  center := M.center
  center_mem := M.center_mem
  disjoint := M.disjoint
  radius_le := M.radius_le
  adj := M.adj

/-- Nowhere denseness in this submission's sense implies nowhere denseness
in the sense of the `sparsity-lectures` submission (in fact the two are the
same condition, read off two nominally distinct copies of one structure). -/
theorem nowhereDense_lax12_of_lax5 (C : GraphClass)
    (h : Lax5.NowhereDenseClasses.NowhereDense C) :
    Lax12.NowhereDenseClasses.NowhereDense C := by
  intro r
  obtain ⟨t, ht⟩ := h r
  refine ⟨t, fun n G hG hminor => ?_⟩
  obtain ⟨M⟩ := hminor
  exact ht n G hG ⟨shallowMinorModel_lax5 M⟩

/-- Uniform quasi-wideness of a nowhere dense class, specialized to the
submitted members: for every radius `r` there are a threshold function
`N` and a separator bound `s` such that every `A` of size at least
`N m` in a member contains, after deleting a set `S` of at most `s`
vertices, a subset `B` of size at least `m` that is pairwise more than
`r` apart in `G − S`. -/
theorem uqw_of_nowhereDense (C : Lax5.GraphClasses.GraphClass)
    (h : Lax5.NowhereDenseClasses.NowhereDense C) (r : ℕ) :
    ∃ (N : ℕ → ℕ) (s : ℕ),
      ∀ (m n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ A : Finset (Fin n), N m ≤ A.card →
          ∃ S B : Finset (Fin n),
            S.card ≤ s ∧ ↑B ⊆ ↑A \ ↑S ∧ m ≤ B.card ∧
            DistIndependent (deleteVerts G ↑S) r ↑B := by
  classical
  obtain ⟨N, s, huqw⟩ :=
    Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense C
      (nowhereDense_lax12_of_lax5 C h) r
  refine ⟨N, s, ?_⟩
  intro m n G hG A hA
  obtain ⟨S, B, hScard, hBsub, hBcard, hBind⟩ :=
    huqw m n G hG (↑A : Set (Fin n)) (by rwa [Set.ncard_coe_finset])
  refine ⟨S.toFinset, B.toFinset, ?_, ?_, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card']
    exact hScard
  · intro x hx
    have hxB : x ∈ B := by simpa using hx
    have hxAS := hBsub hxB
    simpa using hxAS
  · rw [← Set.ncard_eq_toFinset_card']
    exact hBcard
  · simpa only [Set.coe_toFinset] using hBind

end Lax5Proofs.QuasiWideness
