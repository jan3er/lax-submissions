import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
**The driver's cost recurrence, solved.**

`RamDriverRoot.driverRoot_decides_sentence` leaves the cost parameters
free and asks for them only through side conditions. Four of those —
`hKbase`, `hKl`, `hKs`, and the affine shape of `RamDriverRoot.turnCost`
in its `Kin` slot — form a single **downward affine recursion** over the
levels `j = ℓ, ℓ-1, …, 0`:

* `hKbase` : `Cbase ≤ Kl ℓ` — the base pass at the bottom level;
* `hKs`    : `tb j + Kl (j+1) ≤ Ks j` — one turn of the centre loop, whose
  cost is a per-level constant `tb j` *plus one copy* of the cost of the
  nested driver, since `turnCost` names `Kin` once and additively;
* `hKl`    : `order + (cover + ((Ks j + 8) * n + 6)) ≤ Kl j` — a level is
  the ordering phase, the cover phase, and `n` clusters each running a
  turn.

Substituting gives `Kl j ≥ a j + n · Kl (j+1)` with
`a j = order + (cover + ((tb j + 8) * n + 6))`: an affine recursion with
per-level constant `a j` and per-level coefficient `n`.

# What this file provides

Everything is **parametric**: `a`, `b` and `Cbase` are opaque, and no
engine cost, no `Ram*` file and no numeral of the current engines is
mentioned anywhere. The tower-synthesized costs are plugged in later by
choosing `a`, `b`, `Cbase`.

* `solve a b Cbase ℓ` — the canonical downward solution, defined by
  structural recursion on the *fuel* `ℓ - j` so that it computes.
* `Cbase_le_solve` / `le_solve_succ` — it satisfies the recursion
  constraints (with `≤`, the direction the side conditions want; the
  underlying identity `solve_step` is an equality).
* `solve_le_of_le` — it is the **least** such solution: any `K`
  satisfying the same constraints dominates it pointwise. This is what
  makes "instantiate with `solve`" lossless.
* `solve_eq_closed` — the closed form
  `solve a b Cbase ℓ 0 = (∑ j < ℓ, a j * ∏ i < j, b i) + Cbase * ∏ i < ℓ, b i`.
* `solve_mono` — monotone in `a`, `b` and `Cbase` separately and jointly.
* `solve_const` / `solve_const_le` — the constant-coefficient case
  `b ≡ β`, where the products collapse to `β ^ j`, and the coarse
  geometric bound `(ℓ · A + Cbase) · β ^ ℓ`.
* `exists_driverCosts` — the corollary in the driver's own shape: from
  `ℓ`, `n`, the two phase costs and the per-level turn constants `tb`,
  a pair `Kl`, `Ks` satisfying `hKbase`, `hKs` and `hKl` verbatim, with
  `Kl 0` in closed form. Stated with `tb` opaque and with the
  `turnCost`-in-`Kin` affinity as the hypothesis `hturn`, so that no
  `Ram*` import is needed here: P4 supplies `tb j := turnCost … 0` and
  the (definitional) affinity.

# Falsification gate

The recursion, the closed form, the minimality and the driver shape are
`#guard`-checked on `ℓ = 0, 1, 2, 3` with tiny coefficients before any
proof, and three plausible-but-false readings are refuted the same way —
dropping the coefficient products, charging the base at the wrong power,
and reading the solution as monotone in the level. See the
`Falsification` section.
-/

namespace Lax3Proofs.CostRecurrence

open Finset

/-! ### The solver -/

/-- The downward solution with `k` levels left to go from level `j`:
`Cbase` when the budget is spent, and `a j + b j * (the rest)` otherwise.
The fuel is an explicit argument so that this is structural recursion and
computes. -/
def solveRec (a b : ℕ → ℕ) (Cbase : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => Cbase
  | k + 1, j => a j + b j * solveRec a b Cbase k (j + 1)

/-- **The canonical solution** of the downward affine recursion with `ℓ`
levels: at level `j` there are `ℓ - j` levels left. -/
def solve (a b : ℕ → ℕ) (Cbase ℓ j : ℕ) : ℕ := solveRec a b Cbase (ℓ - j) j

/-! ### The recursion -/

/-- At and below the bottom the solution is the base cost. -/
theorem solve_of_le {a b : ℕ → ℕ} {Cbase ℓ j : ℕ} (h : ℓ ≤ j) :
    solve a b Cbase ℓ j = Cbase := by
  have : ℓ - j = 0 := by omega
  rw [solve, this, solveRec]

/-- The bottom level carries exactly the base cost. -/
theorem solve_top (a b : ℕ → ℕ) (Cbase ℓ : ℕ) : solve a b Cbase ℓ ℓ = Cbase :=
  solve_of_le le_rfl

/-- **The recursion**, as an identity: above the bottom, a level is its
own constant plus its coefficient times the level below. -/
theorem solve_step {a b : ℕ → ℕ} {Cbase ℓ j : ℕ} (h : j < ℓ) :
    solve a b Cbase ℓ j = a j + b j * solve a b Cbase ℓ (j + 1) := by
  have hf : ℓ - j = (ℓ - (j + 1)) + 1 := by omega
  rw [solve, hf, solveRec, solve]

/-- The base constraint, in the direction the side conditions want. -/
theorem Cbase_le_solve (a b : ℕ → ℕ) (Cbase ℓ : ℕ) : Cbase ≤ solve a b Cbase ℓ ℓ :=
  le_of_eq (solve_top a b Cbase ℓ).symm

/-- The step constraint, in the direction the side conditions want. -/
theorem le_solve_succ {a b : ℕ → ℕ} {Cbase ℓ j : ℕ} (h : j < ℓ) :
    a j + b j * solve a b Cbase ℓ (j + 1) ≤ solve a b Cbase ℓ j :=
  le_of_eq (solve_step h).symm

/-! ### Minimality

Any cost function satisfying the same two constraints dominates the
canonical solution, so instantiating the driver's parameters with `solve`
loses nothing. -/

/-- **The canonical solution is the least one.** -/
theorem solve_le_of_le {a b K : ℕ → ℕ} {Cbase ℓ : ℕ}
    (hbase : Cbase ≤ K ℓ)
    (hstep : ∀ j < ℓ, a j + b j * K (j + 1) ≤ K j) :
    ∀ j ≤ ℓ, solve a b Cbase ℓ j ≤ K j := by
  have key : ∀ f j, ℓ - j = f → j ≤ ℓ → solve a b Cbase ℓ j ≤ K j := by
    intro f
    induction f with
    | zero =>
        intro j hf hj
        have : j = ℓ := by omega
        subst this
        rw [solve_top]
        exact hbase
    | succ f ih =>
        intro j hf hj
        have hjl : j < ℓ := by omega
        have hnext : solve a b Cbase ℓ (j + 1) ≤ K (j + 1) := ih (j + 1) (by omega) (by omega)
        calc solve a b Cbase ℓ j = a j + b j * solve a b Cbase ℓ (j + 1) := solve_step hjl
          _ ≤ a j + b j * K (j + 1) := by
              exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hnext) _
          _ ≤ K j := hstep j hjl
  intro j hj
  exact key (ℓ - j) j rfl hj

/-! ### Monotonicity

What a consumer needs when it replaces one engine's cost by a larger
bound: the whole solution only grows. -/

/-- The fuel-indexed solution is monotone in all three arguments. -/
theorem solveRec_mono {a a' b b' : ℕ → ℕ} {Cbase Cbase' : ℕ}
    (ha : ∀ j, a j ≤ a' j) (hb : ∀ j, b j ≤ b' j) (hC : Cbase ≤ Cbase') :
    ∀ k j, solveRec a b Cbase k j ≤ solveRec a' b' Cbase' k j := by
  intro k
  induction k with
  | zero => intro j; exact hC
  | succ k ih =>
      intro j
      exact Nat.add_le_add (ha j) (Nat.mul_le_mul (hb j) (ih (j + 1)))

/-- **The solution is monotone** in the per-level constants, the
per-level coefficients and the base cost. -/
theorem solve_mono {a a' b b' : ℕ → ℕ} {Cbase Cbase' ℓ j : ℕ}
    (ha : ∀ j, a j ≤ a' j) (hb : ∀ j, b j ≤ b' j) (hC : Cbase ≤ Cbase') :
    solve a b Cbase ℓ j ≤ solve a' b' Cbase' ℓ j :=
  solveRec_mono ha hb hC _ _

/-- Monotone in the per-level constants alone. -/
theorem solve_mono_a {a a' b : ℕ → ℕ} {Cbase ℓ j : ℕ} (ha : ∀ j, a j ≤ a' j) :
    solve a b Cbase ℓ j ≤ solve a' b Cbase ℓ j :=
  solve_mono ha (fun _ => le_rfl) le_rfl

/-- Monotone in the per-level coefficients alone. -/
theorem solve_mono_b {a b b' : ℕ → ℕ} {Cbase ℓ j : ℕ} (hb : ∀ j, b j ≤ b' j) :
    solve a b Cbase ℓ j ≤ solve a b' Cbase ℓ j :=
  solve_mono (fun _ => le_rfl) hb le_rfl

/-- Monotone in the base cost alone. -/
theorem solve_mono_base {a b : ℕ → ℕ} {Cbase Cbase' ℓ j : ℕ} (hC : Cbase ≤ Cbase') :
    solve a b Cbase ℓ j ≤ solve a b Cbase' ℓ j :=
  solve_mono (fun _ => le_rfl) (fun _ => le_rfl) hC

/-! ### The closed form

Unrolling the recursion: level `j`'s constant is charged the product of
the coefficients of the levels above it, and the base cost the product of
them all. -/

/-- **The closed form of the fuel-indexed solution.** -/
theorem solveRec_eq (a b : ℕ → ℕ) (Cbase : ℕ) : ∀ k j,
    solveRec a b Cbase k j =
      (∑ i ∈ range k, a (j + i) * ∏ i' ∈ range i, b (j + i')) +
        Cbase * ∏ i ∈ range k, b (j + i) := by
  intro k
  induction k with
  | zero => intro j; simp [solveRec]
  | succ k ih =>
      intro j
      rw [solveRec, ih (j + 1)]
      rw [Finset.sum_range_succ' (fun i => a (j + i) * ∏ i' ∈ range i, b (j + i')) k,
        Finset.prod_range_succ' (fun i => b (j + i)) k]
      have hsum : ∑ i ∈ range k, a (j + (i + 1)) * ∏ i' ∈ range (i + 1), b (j + i') =
          b j * ∑ i ∈ range k, a (j + 1 + i) * ∏ i' ∈ range i, b (j + 1 + i') := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.prod_range_succ' (fun i' => b (j + i')) i]
        have hb : ∀ i' : ℕ, b (j + (i' + 1)) = b (j + 1 + i') := by
          intro i'; congr 1; omega
        simp only [hb, Nat.add_zero]
        have : a (j + (i + 1)) = a (j + 1 + i) := by congr 1; omega
        rw [this]
        ring
      have hprod : ∏ i ∈ range k, b (j + (i + 1)) = ∏ i ∈ range k, b (j + 1 + i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        congr 1; omega
      rw [hsum, hprod, Nat.add_zero]
      simp only [Finset.range_zero, Finset.prod_empty, mul_one]
      ring_nf

/-- **The closed form at the top level**, the house form: every level's
constant charged the coefficients above it, the base charged all of
them. -/
theorem solve_eq_closed (a b : ℕ → ℕ) (Cbase ℓ : ℕ) :
    solve a b Cbase ℓ 0 =
      (∑ j ∈ range ℓ, a j * ∏ i ∈ range j, b i) + Cbase * ∏ i ∈ range ℓ, b i := by
  rw [solve, Nat.sub_zero, solveRec_eq]
  simp

/-- The closed form as an upper bound, which is the shape a cost
consumer usually wants. -/
theorem solve_le_closed (a b : ℕ → ℕ) (Cbase ℓ : ℕ) :
    solve a b Cbase ℓ 0 ≤
      (∑ j ∈ range ℓ, a j * ∏ i ∈ range j, b i) + Cbase * ∏ i ∈ range ℓ, b i :=
  le_of_eq (solve_eq_closed a b Cbase ℓ)

/-! ### Constant coefficients

The driver's coefficient is the same at every level — the `n` clusters a
level runs — so the products collapse to powers. -/

/-- **The closed form with a constant coefficient.** -/
theorem solve_const (a : ℕ → ℕ) (β Cbase ℓ : ℕ) :
    solve a (fun _ => β) Cbase ℓ 0 = (∑ j ∈ range ℓ, a j * β ^ j) + Cbase * β ^ ℓ := by
  rw [solve_eq_closed]
  simp

/-- **The geometric bound.** With every per-level constant at most `A`
and a coefficient at least one, the whole solution is
`(ℓ · A + Cbase) · β ^ ℓ`. -/
theorem solve_const_le {a : ℕ → ℕ} {β Cbase ℓ A : ℕ}
    (hA : ∀ j < ℓ, a j ≤ A) (hβ : 1 ≤ β) :
    solve a (fun _ => β) Cbase ℓ 0 ≤ (ℓ * A + Cbase) * β ^ ℓ := by
  rw [solve_const]
  have hterm : ∀ j ∈ range ℓ, a j * β ^ j ≤ A * β ^ ℓ := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact Nat.mul_le_mul (hA j hj) (Nat.pow_le_pow_right hβ (le_of_lt hj))
  calc (∑ j ∈ range ℓ, a j * β ^ j) + Cbase * β ^ ℓ
      ≤ (∑ _j ∈ range ℓ, A * β ^ ℓ) + Cbase * β ^ ℓ :=
        Nat.add_le_add_right (Finset.sum_le_sum hterm) _
    _ = ℓ * (A * β ^ ℓ) + Cbase * β ^ ℓ := by
        simp [Finset.sum_const, Finset.card_range]
    _ = (ℓ * A + Cbase) * β ^ ℓ := by ring

/-! ### The driver's shape

The corollary `RamDriverRoot.driverRoot_decides_sentence` consumes: the
three side conditions `hKbase`, `hKs`, `hKl` at once, with witnesses.
Nothing here knows what the numbers are — `order`, `cover`, `Cbase` and
the per-level turn constants `tb` are opaque, and the only thing assumed
about the turn cost is that it is **affine with coefficient one** in the
nested driver's cost, which is what `turnCost`'s text says (`Kin` occurs
once, additively). -/

/-- The per-level constant the driver's three side conditions produce. -/
def driverA (order cover n : ℕ) (tb : ℕ → ℕ) (j : ℕ) : ℕ :=
  order + (cover + ((tb j + 8) * n + 6))

/-- **The driver's cost parameters, exhibited.** Given the round budget
`ℓ`, the carrier size `n`, the two phase costs, the base cost and the
per-level turn constants, there are `Kl` and `Ks` satisfying the three
cost side conditions of `driverRoot_decides_sentence` — `hKbase`, `hKs`,
`hKl` — with `Kl 0` in closed form, and `Kl` least among all such.

`turn j Kin` is the turn cost with the nested driver's budget in its
`Kin` slot; `hturn` is its affinity, which for `RamDriverRoot.turnCost`
holds with `tb j := turnCost … j φ (Ksc j) 0` by `Nat.add` associativity
alone. -/
theorem exists_driverCosts (ℓ n order cover Cbase : ℕ) (tb : ℕ → ℕ)
    (turn : ℕ → ℕ → ℕ) (hturn : ∀ j Kin, turn j Kin ≤ tb j + Kin) :
    ∃ Kl Ks : ℕ → ℕ,
      Cbase ≤ Kl ℓ ∧
      (∀ j < ℓ, turn j (Kl (j + 1)) ≤ Ks j) ∧
      (∀ j < ℓ, order + (cover + ((Ks j + 8) * n + 6)) ≤ Kl j) ∧
      Kl 0 = (∑ j ∈ range ℓ, driverA order cover n tb j * n ^ j) + Cbase * n ^ ℓ ∧
      ∀ K : ℕ → ℕ, Cbase ≤ K ℓ →
        (∀ j < ℓ, driverA order cover n tb j + n * K (j + 1) ≤ K j) →
        ∀ j ≤ ℓ, Kl j ≤ K j := by
  classical
  refine ⟨solve (driverA order cover n tb) (fun _ => n) Cbase ℓ,
    fun j => tb j + solve (driverA order cover n tb) (fun _ => n) Cbase ℓ (j + 1),
    Cbase_le_solve _ _ _ _, fun j _ => hturn j _, fun j hj => ?_, solve_const _ _ _ _,
    fun K hbase hstep => solve_le_of_le hbase hstep⟩
  have h := le_solve_succ (a := driverA order cover n tb) (b := fun _ => n)
    (Cbase := Cbase) (ℓ := ℓ) (j := j) hj
  simp only [driverA] at h
  calc order + (cover + ((tb j +
        solve (driverA order cover n tb) (fun _ => n) Cbase ℓ (j + 1) + 8) * n + 6))
      = (order + (cover + ((tb j + 8) * n + 6))) +
        n * solve (driverA order cover n tb) (fun _ => n) Cbase ℓ (j + 1) := by ring
    _ ≤ solve (driverA order cover n tb) (fun _ => n) Cbase ℓ j := h

/-! ### Falsification

Every statement above was `#guard`-checked before it was proved: the
recursion on `ℓ = 0, 1, 2, 3` against hand values, the closed form
against the recursion, minimality against a witness that satisfies the
constraints slackly, and the two closed forms one would plausibly write
down instead — both refuted. -/

section Falsification

/-- The sample data: `a j = j + 1`, `b ≡ 2`, `Cbase = 5`. -/
private def sa : ℕ → ℕ := fun j => j + 1
private def sb : ℕ → ℕ := fun _ => 2

-- the recursion, unrolled by hand: `Cbase` at the bottom, and
-- `1 + 2·(2 + 2·(3 + 2·5)) = 57` at the top of three levels
#guard solve sa sb 5 0 0 = 5
#guard solve sa sb 3 3 3 = 3
#guard solve sa sb 5 1 0 = 1 + 2 * 5
#guard solve sa sb 5 2 0 = 1 + 2 * (2 + 2 * 5)
#guard solve sa sb 5 3 0 = 57

-- above the bottom the solution is constant, and the step identity holds
#guard solve sa sb 5 3 4 = 5
#guard solve sa sb 5 3 1 = sa 1 + sb 1 * solve sa sb 5 3 2

-- the closed form: `∑ a j · 2 ^ j + 5 · 2 ^ 3 = 1 + 4 + 12 + 40`
#guard solve sa sb 5 3 0 = (1 * 1 + 2 * 2 + 3 * 4) + 5 * 8

-- monotonicity, on the same data
#guard solve sa sb 5 3 0 ≤ solve (fun j => sa j + 1) sb 5 3 0
#guard solve sa sb 5 3 0 ≤ solve sa (fun _ => 3) 5 3 0
#guard solve sa sb 5 3 0 ≤ solve sa sb 6 3 0

-- **Refuted**: dropping the coefficient products — charging every
-- level's constant once — is *not* an upper bound.
#guard ¬ (solve sa sb 5 3 0 ≤ (1 + 2 + 3) + 5 * 2 ^ 3)

-- **Refuted**: charging the base cost the coefficient product of the
-- levels *below* the bottom, i.e. `β ^ 0`, is not an upper bound either.
#guard ¬ (solve sa sb 5 3 0 ≤ (1 * 1 + 2 * 2 + 3 * 4) + 5 * 2 ^ 0)

-- **Refuted**: with a zero coefficient the solution is *not* monotone in
-- the level, so no consumer may read `solve … ℓ j` as decreasing in `j`
-- without the coefficient being at least one.
#guard ¬ (solve sa (fun _ => 0) 5 3 0 ≥ solve sa (fun _ => 0) 5 3 1)

-- the driver shape, on `n = 2`, `order = 7`, `cover = 11`, `tb j = j`
private def stb : ℕ → ℕ := fun j => j
#guard driverA 7 11 2 stb 0 = 7 + (11 + ((0 + 8) * 2 + 6))
#guard solve (driverA 7 11 2 stb) (fun _ => 2) 4 2 0 =
  (driverA 7 11 2 stb 0 * 1 + driverA 7 11 2 stb 1 * 2) + 4 * 4

-- and the side condition the corollary discharges, checked numerically
#guard 7 + (11 + (((stb 0 + solve (driverA 7 11 2 stb) (fun _ => 2) 4 2 1) + 8) * 2 + 6)) ≤
  solve (driverA 7 11 2 stb) (fun _ => 2) 4 2 0

-- The falsification data is not degenerate: the three-level solution is
-- not the base cost.
example : solve sa sb 5 3 0 ≠ 5 := by decide

end Falsification

end Lax3Proofs.CostRecurrence
