import Lax12.NowhereDenseUQW
import Mathlib.Data.Set.Card

/-!
Uniform quasi-wideness in the shape the Adler–Adler argument consumes.
Nothing is proved here: uniform quasi-wideness of a nowhere dense class is
*assumed* from the `sparsity-lectures` submission
(`Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense`), whose
nowhere-denseness definition is the one this submission's concepts are
stated over as well.  All this file does is convert the `Set`-valued
conclusion to the `Finset` form the caller uses.
-/

namespace Lax5Proofs.QuasiWideness

open Lax12.GraphClasses
open Lax12.UniformQuasiWideness

/-- Uniform quasi-wideness of a nowhere dense class, specialized to the
submitted members: for every radius `r` there are a threshold function
`N` and a separator bound `s` such that every `A` of size at least
`N m` in a member contains, after deleting a set `S` of at most `s`
vertices, a subset `B` of size at least `m` that is pairwise more than
`r` apart in `G − S`. -/
theorem uqw_of_nowhereDense (C : GraphClass)
    (h : Lax12.NowhereDenseClasses.NowhereDense C) (r : ℕ) :
    ∃ (N : ℕ → ℕ) (s : ℕ),
      ∀ (m n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ A : Finset (Fin n), N m ≤ A.card →
          ∃ S B : Finset (Fin n),
            S.card ≤ s ∧ ↑B ⊆ ↑A \ ↑S ∧ m ≤ B.card ∧
            DistIndependent (deleteVerts G ↑S) r ↑B := by
  classical
  obtain ⟨N, s, huqw⟩ :=
    Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense C h r
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
