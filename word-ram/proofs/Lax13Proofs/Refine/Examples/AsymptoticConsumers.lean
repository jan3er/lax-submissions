import Lax13Proofs.Refine.Asymptotics.Recurrences
import Lax13Proofs.Refine.Examples.BfsQ
import Lax13Proofs.Refine.Examples.IntrosortBudget

/-!
# Asymptotic consumer demonstrations

This leaf checks that two exact producer accounts can consume the landed
asymptotic API without strengthening their advertised upper bounds.

Consumer provenance (two rows):

* `BfsQ.bfsQTotal` and its seven coordinate theorems -> `bfsQCash`,
  `bfsQCash_eq`, `bfsQCash_isBigO`;
* `IntrosortBudget.introsortBudget_cash` -> `introsortCash`,
  `introsortBudget_cash_eq`, `introsortCash_isBigO`.
-/

open Filter
open scoped Topology

namespace Lax13Proofs.Refine.AsymptoticConsumers

open Asymptotics
open Lax13Proofs.Refine.Asymptotics1D
open Lax13Proofs.Refine.Asymptotics2D

/-! ## The seven-coordinate BFS cash projection -/

/-- Unit cash for the complete support of the source-shaped BFS account. -/
def bfsQCash (n ns : ℕ) : ℕ :=
  (BfsQ.bfsQTotal n ns).toFun Ir.Currency.skip +
  (BfsQ.bfsQTotal n ns).toFun Ir.Currency.const +
  (BfsQ.bfsQTotal n ns).toFun Ir.Currency.aget +
  (BfsQ.bfsQTotal n ns).toFun Ir.Currency.aset +
  (BfsQ.bfsQTotal n ns).toFun Ir.Currency.ite +
  (BfsQ.bfsQTotal n ns).toFun Ir.Currency.«while» +
  (BfsQ.bfsQTotal n ns).toFun Ir.Currency.add

/-- Exact unit-cash polynomial obtained by summing all seven coordinates. -/
theorem bfsQCash_eq (n ns : ℕ) : bfsQCash n ns = 22 * n + 15 * ns + 13 := by
  simp [bfsQCash]
  omega

/-- The exact BFS cash projection is linear at the genuine product limit. -/
theorem bfsQCash_isBigO :
    (fun p : ℕ × ℕ => (bfsQCash p.1 p.2 : ℝ)) =O[productAtTop]
      fun p => (p.1 : ℝ) + (p.2 : ℝ) := by
  apply IsBigO.of_bound 50
  rw [show productAtTop = atTop ×ˢ atTop from rfl, prod_atTop_atTop_eq,
    eventually_atTop_prod_self]
  refine ⟨1, fun n ns hn hns => ?_⟩
  rw [bfsQCash_eq]
  simp only [norm_natCast]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) + (ns : ℝ))]
  push_cast
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsR : (1 : ℝ) ≤ ns := by exact_mod_cast hns
  nlinarith

/-! ## The introsort scalar boundary -/

/-- The scalar polynomial displayed by the exact introsort cash boundary. -/
def introsortCash (n : ℕ) : ℕ :=
  4693 + 5 * IntrosortBudget.ilog n + 231 * n +
    455 * (n * IntrosortBudget.ilog n)

/-- Exact producer wrapper, with the displayed polynomial named by `introsortCash`. -/
theorem introsortBudget_cash_eq (ltCurr : String) (n : ℕ) :
    IntrosortBudget.sourceCollapse ltCurr
        (NRest.spec (fun _ : Unit => True)
          (fun _ => (IntrosortBudget.introsortBudget ltCurr n).operationVector)) =
      NRest.spec (fun _ : Unit => True)
        (fun _ => ((introsortCash n : ℕ) : ℕ∞)) := by
  simpa [introsortCash] using IntrosortBudget.introsortBudget_cash ltCurr n

private theorem ilogIsBigOLog :
    (fun n : ℕ => (IntrosortBudget.ilog n : ℝ)) =O[atTop]
      fun n => Real.log (n : ℝ) := by
  have hlogb :
      (fun n : ℕ => (IntrosortBudget.ilog n : ℝ)) =O[atTop]
        fun n => Real.logb 2 (n : ℝ) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    have hn : 0 ≤ Real.logb 2 (n : ℝ) := by
      cases n with
      | zero => simp
      | succ n =>
          apply Real.logb_nonneg (by norm_num)
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa [IntrosortBudget.ilog, norm_natCast, Real.norm_of_nonneg hn] using
      (Real.natLog_le_logb n 2)
  exact hlogb.trans (by simpa using (log2Asym 0).1)

private theorem oneIsBigONLog :
    (fun _ : ℕ => (1 : ℝ)) =O[atTop]
      fun n => (n : ℝ) * Real.log (n : ℝ) := by
  simpa [polylog] using
    (polylogCompare (a₁ := 0) (b₁ := 0) (a₂ := 1) (b₂ := 1)
      (Or.inl (by omega))).isBigO

private theorem linearIsBigONLog :
    (fun n : ℕ => (n : ℝ)) =O[atTop]
      fun n => (n : ℝ) * Real.log (n : ℝ) := by
  simpa [polylog] using
    (polylogCompare (a₁ := 1) (b₁ := 0) (a₂ := 1) (b₂ := 1)
      (Or.inr ⟨rfl, by omega⟩)).isBigO

private theorem ilogTermIsBigONLog :
    (fun n : ℕ => (IntrosortBudget.ilog n : ℝ)) =O[atTop]
      fun n => (n : ℝ) * Real.log (n : ℝ) :=
  ilogIsBigOLog.trans <| by
    simpa [polylog] using
      (polylogCompare (a₁ := 0) (b₁ := 1) (a₂ := 1) (b₂ := 1)
        (Or.inl (by omega))).isBigO

private theorem nIlogIsBigONLog :
    (fun n : ℕ => ((n * IntrosortBudget.ilog n : ℕ) : ℝ)) =O[atTop]
      fun n => (n : ℝ) * Real.log (n : ℝ) := by
  simpa only [Nat.cast_mul] using
    (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul ilogIsBigOLog

/-- The exact introsort cash polynomial has the advertised O(n log n) bound. -/
theorem introsortCash_isBigO :
    (fun n => (introsortCash n : ℝ)) =O[atTop]
      fun n => (n : ℝ) * Real.log (n : ℝ) := by
  have hconst := oneIsBigONLog.const_mul_left (4693 : ℝ)
  have hilog := ilogTermIsBigONLog.const_mul_left (5 : ℝ)
  have hlinear := linearIsBigONLog.const_mul_left (231 : ℝ)
  have hmain := nIlogIsBigONLog.const_mul_left (455 : ℝ)
  simpa [introsortCash, Nat.cast_add, Nat.cast_mul] using
    ((hconst.add hilog).add hlinear).add hmain

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.AsymptoticConsumers.bfsQCash_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bfsQCash_isBigO

/-- info: 'Lax13Proofs.Refine.AsymptoticConsumers.introsortCash_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms introsortCash_isBigO

end Lax13Proofs.Refine.AsymptoticConsumers
