import Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumberOrdering.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.StrongColoringBoundByAdm.Full
import Mathlib.Tactic

open Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers
open Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility

namespace Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumberEquivalence

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Corollary 2.7: wcol_r ≤ 1 + r · (adm_r - 1)^(r²) per ordering. -/
theorem wcol_le_of_adm (G : SimpleGraph V) (r : ℕ) :
    wcol G r ≤ 1 + r * (adm G r - 1) ^ (r ^ 2) := by
  have hscol :
      scol G r ≤ 1 + (adm G r - 1) ^ r :=
    Lax5Proofs.Source.Catalog.SparsityLectures.StrongColoringBoundByAdm.scol_le_one_add_adm_sub_one_pow G r
  have hsub : scol G r - 1 ≤ (adm G r - 1) ^ r := by
    rw [Nat.sub_le_iff_le_add]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hscol
  calc
    wcol G r ≤ 1 + r * (scol G r - 1) ^ r :=
      Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumberOrdering.wcol_le_of_scol G r
    _ ≤ 1 + r * ((adm G r - 1) ^ r) ^ r := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      exact hsub
    _ = 1 + r * (adm G r - 1) ^ (r * r) := by
      rw [← Nat.pow_mul]
    _ = 1 + r * (adm G r - 1) ^ (r ^ 2) := by
      simp [pow_two]

end Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumberEquivalence
