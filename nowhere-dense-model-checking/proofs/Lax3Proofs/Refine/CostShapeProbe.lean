import Lax3Proofs.RamDriverRoot
import Lax3Proofs.CostRecurrence

/-!
**The cost-shape probes of the integration wave** — the falsification
record of the Σ-shape driver revision (integration-design.md), compiled.

Three things are established here, before any surgery, in the
refute-before-prove discipline:

1. **The star probe.** A cover with one big cluster and `n - 1`
   singletons has total mass `2·(n-1)`, but a *uniform* per-turn budget
   must cover the big cluster on every turn, so the uniform interface
   cannot state a bound below `n·(n-1)`: quadratic where the truth is
   linear. This is the plan's Σ-shape ruling, as arithmetic
   (`star_mass_linear` / `star_uniform_quadratic` /
   `star_uniform_gap`), with the negative control `sum_le_uniform`
   showing the Σ reading never *exceeds* the uniform one — the
   revision is a strict refinement.

2. **The interface floor.** The frozen cost side conditions of
   `RamDriverRoot.driverRoot_decides_sentence` — `hKs` and `hKl`, in
   their current uniform, arena-size-blind shape — force
   `n ^ ℓ · Kl ℓ ≤ Kl 0` for *every* instantiation of the free cost
   parameters (`uniform_interface_floor`). No engine improvement, and
   no choice of `Kb/Ki/Ksc/Ks/Kl`, can carry the tower's touched-only
   costs through the current interface to an almost-linear bound: the
   `n^ℓ` is in the hypotheses' shape, not in the engines. (The
   companion finding — that the *program* `RamDriver.driverAux` has an
   `n^ℓ` run-cost floor of its own, so the revision cannot be
   hypothesis-only — is a six-line paper argument recorded in
   integration-design.md §3; the loop's `n` turns each run the nested
   driver unconditionally.)

3. **The Σ-shaped recurrence stays inside the P3 solver.** The revised
   interface's per-size linear ansatz `Kl j m = u j · m + …` puts the
   coefficient recursion `u j = a j + D · u (j+1)` — `D` the cover
   degree, not `n` — into exactly `CostRecurrence.solve`'s shape;
   `sigma_coefficients_geometric` is `solve_const_le` cited at `D`,
   and the `#guard` pair at the bottom compiles the contrast between
   coefficient `n` and coefficient `D` on small data.
-/

namespace Lax3Proofs.Refine.CostShapeProbe

open Finset

/-! ### 1. The star probe -/

/-- The star cover's block sizes at carrier `n`: block `0` is the big
cluster on `n - 1` vertices, every other block is a singleton. -/
def starSizes (n c : ℕ) : ℕ := if c = 0 then n - 1 else 1

-- the instance at `n = 8`: mass `14`, uniform budget `56`
#guard (∑ c ∈ range 8, starSizes 8 c) = 14
#guard (∑ _c ∈ range 8, (8 - 1)) = 56
-- and the gap grows: at `n = 32`, `62` against `992`
#guard (∑ c ∈ range 32, starSizes 32 c) = 62
#guard (∑ _c ∈ range 32, (32 - 1)) = 992

/-- **The Σ reading of the star level is linear**: the blocks' sizes sum
to twice the carrier, less two. -/
theorem star_mass_linear (n : ℕ) (hn : 1 ≤ n) :
    ∑ c ∈ range n, starSizes n c = 2 * (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ' (starSizes (k + 1)) k]
  have h1 : ∀ c ∈ range k, starSizes (k + 1) (c + 1) = 1 := fun c _ =>
    if_neg (Nat.succ_ne_zero c)
  rw [sum_congr rfl h1, sum_const, card_range, smul_eq_mul, mul_one]
  show k + starSizes (k + 1) 0 = 2 * (k + 1 - 1)
  rw [starSizes, if_pos rfl]
  omega

/-- **The uniform reading of the same level is quadratic**: a per-turn
budget that covers the big cluster, paid on all `n` turns. -/
theorem star_uniform_quadratic (n : ℕ) :
    ∑ _c ∈ range n, (n - 1) = n * (n - 1) := by
  rw [sum_const, card_range, smul_eq_mul]

/-- The gap: from `n = 3` on, the Σ total is strictly below the uniform
one, and the ratio is `n / 2`. -/
theorem star_uniform_gap (n : ℕ) (hn : 3 ≤ n) :
    ∑ c ∈ range n, starSizes n c < ∑ _c ∈ range n, (n - 1) := by
  rw [star_mass_linear n (by omega), star_uniform_quadratic]
  exact mul_lt_mul_of_pos_right (show 2 < n by omega) (show 0 < n - 1 by omega)

/-- **Negative control**: the Σ reading never exceeds the uniform one —
whenever every turn's budget is below `K`, the sum is below `n · K`. So
a Σ-shaped side condition is implied by the uniform one, and the
re-threading is a strict refinement, never a strengthening. -/
theorem sum_le_uniform (n K : ℕ) (f : ℕ → ℕ) (hf : ∀ c < n, f c ≤ K) :
    ∑ c ∈ range n, f c ≤ n * K := by
  calc ∑ c ∈ range n, f c ≤ ∑ _c ∈ range n, K :=
        sum_le_sum fun c hc => hf c (mem_range.mp hc)
    _ = n * K := by rw [sum_const, card_range, smul_eq_mul]

/-! ### 2. The interface floor

The two side conditions, exactly as `driverRoot_decides_sentence` takes
them today, force the geometric blow-up: `turnCost` carries the nested
level's whole budget `Kl (j+1)` additively (`hKs`), and the level pays
`n` turns at the uniform budget (`hKl`). Nothing else about the driver
is used. -/

/-- The nested budget rides inside the turn cost: `turnCost`'s `Kin`
slot is additive. -/
theorem kin_le_turnCost (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (Ksc Kin : ℕ) : Kin ≤ RamDriverRoot.turnCost n ns cap mb q_top j φ Ksc Kin := by
  unfold RamDriverRoot.turnCost
  omega

/-- **The uniform interface forces `n^ℓ`.** Any cost parameters
satisfying the current `hKs` and `hKl` side conditions of
`RamDriverRoot.driverRoot_decides_sentence` satisfy
`n ^ (ℓ - j) · Kl ℓ ≤ Kl j` at every level — at the root,
`n ^ ℓ · Kl ℓ ≤ Kl 0`. The almost-linear C0 bound is not statable
through this interface for `ℓ ≥ 2`: the blow-up is in the hypothesis
shape, independent of every engine cost. -/
theorem uniform_interface_floor {n ns cap mb q_top W ℓ : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {Ksc Ks Kl : ℕ → ℕ}
    (hKs : ∀ j < ℓ,
      RamDriverRoot.turnCost n ns cap mb q_top j φ (Ksc j) (Kl (j + 1)) ≤ Ks j)
    (hKl : ∀ j < ℓ, RamDriverCompose.orderPhaseCost n ns W +
      (RamDriverCompose.coverPhaseCost n ns + ((Ks j + 8) * n + 6)) ≤ Kl j) :
    ∀ j ≤ ℓ, n ^ (ℓ - j) * Kl ℓ ≤ Kl j := by
  have key : ∀ f j, ℓ - j = f → j ≤ ℓ → n ^ f * Kl ℓ ≤ Kl j := by
    intro f
    induction f with
    | zero =>
        intro j hf hj
        have hje : j = ℓ := by omega
        subst hje
        simp
    | succ f ih =>
        intro j hf hj
        have hjl : j < ℓ := by omega
        have hnext : n ^ f * Kl ℓ ≤ Kl (j + 1) := ih (j + 1) (by omega) (by omega)
        have h₁ : Kl (j + 1) ≤ Ks j :=
          le_trans (kin_le_turnCost n ns cap mb q_top j φ (Ksc j) (Kl (j + 1)))
            (hKs j hjl)
        have h₂ : Ks j * n ≤ Kl j := by
          have h := hKl j hjl
          have : Ks j * n ≤ (Ks j + 8) * n := Nat.mul_le_mul_right n (by omega)
          omega
        calc n ^ (f + 1) * Kl ℓ = n ^ f * Kl ℓ * n := by ring
          _ ≤ Kl (j + 1) * n := Nat.mul_le_mul_right n hnext
          _ ≤ Ks j * n := Nat.mul_le_mul_right n h₁
          _ ≤ Kl j := h₂
  exact fun j hj => key (ℓ - j) j rfl hj

/-- The floor at the root. -/
theorem uniform_interface_floor_zero {n ns cap mb q_top W ℓ : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {Ksc Ks Kl : ℕ → ℕ}
    (hKs : ∀ j < ℓ,
      RamDriverRoot.turnCost n ns cap mb q_top j φ (Ksc j) (Kl (j + 1)) ≤ Ks j)
    (hKl : ∀ j < ℓ, RamDriverCompose.orderPhaseCost n ns W +
      (RamDriverCompose.coverPhaseCost n ns + ((Ks j + 8) * n + 6)) ≤ Kl j) :
    n ^ ℓ * Kl ℓ ≤ Kl 0 := by
  simpa using uniform_interface_floor hKs hKl 0 (Nat.zero_le ℓ)

/-! ### 3. The Σ recurrence, inside the P3 solver

The Σ-shape revision's per-size linear ansatz `Kl j m = u j · m + w j`
turns the level recursion into `u j = a j + D · u (j+1)` with `D` the
cover degree — `CostRecurrence.solve` at coefficient `D`. With
`D = ⌈c · n^(ε/ℓ)⌉` from `CoverDegree.exists_cover_degree`, the
geometric bound is `(ℓ·A + Cbase) · D^ℓ = O(n^ε)` per unit of carrier:
the almost-linear headline. -/

/-- The Σ-shaped coefficient recursion is the P3 solver at the cover
degree: geometric in `D`, not in `n`. -/
theorem sigma_coefficients_geometric {a : ℕ → ℕ} {D Cbase ℓ A : ℕ}
    (hA : ∀ j < ℓ, a j ≤ A) (hD : 1 ≤ D) :
    CostRecurrence.solve a (fun _ => D) Cbase ℓ 0 ≤ (ℓ * A + Cbase) * D ^ ℓ :=
  CostRecurrence.solve_const_le hA hD

-- the contrast, compiled: per-level constant 10, base 1, three levels —
-- coefficient `n = 100` (the uniform recursion) against coefficient
-- `D = 2` (the Σ recursion at a degree-2 cover)
#guard CostRecurrence.solve (fun _ => 10) (fun _ => 100) 1 3 0 = 1101010
#guard CostRecurrence.solve (fun _ => 10) (fun _ => 2) 1 3 0 = 78

end Lax3Proofs.Refine.CostShapeProbe
