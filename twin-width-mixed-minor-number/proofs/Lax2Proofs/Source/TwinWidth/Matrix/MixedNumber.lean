import Lax2Proofs.Source.TwinWidth.Matrix.MixedMinor

/-!
# Mixed number of a matrix

The mixed number is the largest `k ≤ min n m` for which the matrix has a
`k`-mixed minor.  The `k = 0` convention from `HasMixedMinor` ensures this
maximum is always defined.
-/

namespace Lax2Proofs.TwinWidth
namespace Matrix

variable {α : Type*}

/-- The mixed number of a matrix: the largest order of a mixed minor,
searched up to the smaller matrix dimension. -/
noncomputable def matrixMixedNumber {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) : ℕ :=
  by
    classical
    exact Nat.findGreatest (HasMixedMinor M) (min n m)

theorem matrixMixedNumber_le_min_card {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) :
    matrixMixedNumber M ≤ min n m :=
  by
    classical
    exact Nat.findGreatest_le (P := HasMixedMinor M) (min n m)

theorem hasMixedMinor_matrixMixedNumber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) :
    HasMixedMinor M (matrixMixedNumber M) := by
  classical
  exact Nat.findGreatest_spec (P := HasMixedMinor M) (m := 0) (n := min n m)
    (Nat.zero_le _) (hasMixedMinor_zero M)

@[simp] theorem matrixMixedNumber_zero_rows {m : ℕ}
    (M : _root_.Matrix (Fin 0) (Fin m) α) :
    matrixMixedNumber M = 0 :=
  Nat.eq_zero_of_le_zero (by
    simpa using matrixMixedNumber_le_min_card M)

@[simp] theorem matrixMixedNumber_zero_cols {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin 0) α) :
    matrixMixedNumber M = 0 :=
  Nat.eq_zero_of_le_zero (by
    simpa using matrixMixedNumber_le_min_card M)

/-- The successor of the mixed number is mixed-free. -/
theorem not_hasMixedMinor_succ_matrixMixedNumber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) :
    ¬ HasMixedMinor M (matrixMixedNumber M + 1) := by
  classical
  by_cases hle : matrixMixedNumber M + 1 ≤ min n m
  · exact Nat.findGreatest_is_greatest
      (P := HasMixedMinor M)
      (hk := Nat.lt_succ_self (matrixMixedNumber M)) hle
  · intro h
    exact hle (hasMixedMinor_le_min_card h)

end Matrix
end Lax2Proofs.TwinWidth
