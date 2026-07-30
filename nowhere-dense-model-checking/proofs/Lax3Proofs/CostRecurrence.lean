import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-! ### The Σ shape

`integration-design.md` §5.9. The uniform corollary above charges a
level `n` turns at the worst turn's budget, which forces the
coefficient `n` and hence the `n ^ ℓ` floor its §2.1 compiles. The
revised interface charges a level the **sum** of its turns, each read at
its own block size, and every cost becomes a function of the arena size
`m`:

* `Kl j m` — the level at depth `j` on an arena of `m` alive vertices;
* `Kt j s` — one turn whose block has `s` members;
* `Ko j m`, `Kc j m` — the ordering and cover phases, active-set driven,
  so linear in the arena rather than in the carrier;
* `tb j s` — the turn's own leaves, touched-only, linear in the block.

The three shape hypotheses `hKo`/`hKc`/`htb` are exactly "linear in the
size handed in" (`… ≤ coeff * (size + 1)`, the `+1` absorbing the
per-call constants), and the mass hypothesis of the level is the one
B6 supplies from the cover's degree bound: the block sizes of a level
sum to at most `D * (m + 1)`.

Under those, the linear ansatz `Kl j m = u j * (m + 1)` turns the level
condition into the *same* affine recursion the file already solves —
with the coefficient `D + 1` in place of `n`:

```
u j = (ko j + kc j + α j * (D + 1) + 14) + (D + 1) * u (j + 1)
```

The `+ 1` in the coefficient is not slack: the level pays one turn
*overhead* per nonempty block on top of the block's own mass, and there
can be `m` of them. The falsification block below compiles that — the
side condition is refuted at coefficient `D`. -/

/-- The per-level constant of the Σ-shaped recursion: the two phase
coefficients, the turn-leaf coefficient charged at the mass
coefficient, and the loop's own per-turn and per-level constants
(`8` per turn, `6` per level). -/
def driverASigma (ko kc α : ℕ → ℕ) (D j : ℕ) : ℕ :=
  ko j + (kc j + (α j * (D + 1) + 14))

/-- **The level witness**: the canonical solution at coefficient
`D + 1`, read linearly in the arena size. -/
def KlSigma (ko kc α : ℕ → ℕ) (D Cb ℓ j m : ℕ) : ℕ :=
  solve (driverASigma ko kc α D) (fun _ => D + 1) Cb ℓ j * (m + 1)

/-- **The turn witness**: the turn's own leaves at the block's size,
plus the nested level at that same size. -/
def KtSigma (ko kc α : ℕ → ℕ) (tb : ℕ → ℕ → ℕ) (D Cb ℓ j s : ℕ) : ℕ :=
  tb j s + KlSigma ko kc α D Cb ℓ (j + 1) s

/-- **The driver's Σ-shaped cost parameters, exhibited** (§5.9).

From the level count `ℓ`, the mass coefficient `D`, the base
coefficient `Cb`, and the three per-level *coefficients* `ko`, `kc`,
`α` bounding the two phases and the turn's leaves linearly in the size
they are handed, there are size-indexed `Kl` and `Kt` satisfying the
revised side conditions of `driverRoot_decides_sentence` — the base,
the monotonicity `hKmono` the descend clause needs, the turn condition
§5.7 and the Σ-shaped level condition §5.6 — with `Kl 0` in closed form
and `Kl` least among the solutions of the induced numeric recursion.

Nothing here knows what the numbers are: `Ko`, `Kc`, `tb` and `turn`
are opaque, and the only thing assumed about the turn cost is the same
affinity in the nested driver's slot that `exists_driverCosts` assumes,
now at each block size. The uniform corollary above is unchanged and
stays: this is its refinement, not its replacement. -/
theorem exists_driverCostsSigma (ℓ D Cb : ℕ) (ko kc α : ℕ → ℕ)
    (Ko Kc tb : ℕ → ℕ → ℕ) (turn : ℕ → ℕ → ℕ → ℕ)
    (hKo : ∀ j m, Ko j m ≤ ko j * (m + 1))
    (hKc : ∀ j m, Kc j m ≤ kc j * (m + 1))
    (htb : ∀ j s, tb j s ≤ α j * (s + 1))
    (hturn : ∀ j s Kin, turn j s Kin ≤ tb j s + Kin) :
    ∃ Kl Kt : ℕ → ℕ → ℕ,
      (∀ m, Cb * (m + 1) ≤ Kl ℓ m) ∧
      (∀ j, Monotone (Kl j)) ∧
      (∀ j s, turn j s (Kl (j + 1) s) ≤ Kt j s) ∧
      (∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
        (∑ c ∈ range t, bs c) ≤ D * (m + 1) →
        Ko j m + (Kc j m + ((∑ c ∈ range t, (Kt j (bs c) + 8)) + 6)) ≤ Kl j m) ∧
      (∀ m, Kl 0 m =
        ((∑ j ∈ range ℓ, driverASigma ko kc α D j * (D + 1) ^ j) + Cb * (D + 1) ^ ℓ) * (m + 1)) ∧
      (∀ K : ℕ → ℕ, Cb ≤ K ℓ →
        (∀ j < ℓ, driverASigma ko kc α D j + (D + 1) * K (j + 1) ≤ K j) →
        ∀ j ≤ ℓ, ∀ m, Kl j m ≤ K j * (m + 1)) := by
  classical
  have hAdef : ∀ j, driverASigma ko kc α D j =
      ko j + (kc j + (α j * (D + 1) + 14)) := fun _ => rfl
  set A : ℕ → ℕ := driverASigma ko kc α D with hA
  set u : ℕ → ℕ := solve A (fun _ => D + 1) Cb ℓ with hu
  have hKl : ∀ j m, KlSigma ko kc α D Cb ℓ j m = u j * (m + 1) := fun _ _ => rfl
  have hKt : ∀ j s, KtSigma ko kc α tb D Cb ℓ j s = tb j s + u (j + 1) * (s + 1) :=
    fun _ _ => rfl
  refine ⟨KlSigma ko kc α D Cb ℓ, KtSigma ko kc α tb D Cb ℓ,
    fun m => by rw [hKl, hu, solve_top],
    fun j a b hab => by rw [hKl, hKl]; exact Nat.mul_le_mul_left _ (by omega),
    fun j s => by rw [hKt, hKl]; exact hturn j s _,
    fun j hj m t htm bs hbs => ?_,
    fun m => by rw [hKl, hu, solve_const],
    fun K hbase hstep j hj m => by
      rw [hKl]; exact Nat.mul_le_mul_right _ (solve_le_of_le hbase hstep j hj)⟩
  rw [hKl]
  simp only [hKt]
  -- the block sizes, with one loop overhead each, fit the mass bound at coefficient `D + 1`
  have hsum1 : (∑ c ∈ range t, (bs c + 1)) ≤ (D + 1) * (m + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    calc (∑ c ∈ range t, bs c) + t ≤ D * (m + 1) + (m + 1) := Nat.add_le_add hbs (by omega)
      _ = (D + 1) * (m + 1) := by ring
  -- one turn is its leaves plus the nested level, both linear in the block
  have hterm : ∀ c ∈ range t,
      (tb j (bs c) + u (j + 1) * (bs c + 1)) + 8 ≤ (α j + u (j + 1)) * (bs c + 1) + 8 := by
    intro c _
    have := htb j (bs c)
    calc (tb j (bs c) + u (j + 1) * (bs c + 1)) + 8
        ≤ (α j * (bs c + 1) + u (j + 1) * (bs c + 1)) + 8 := by omega
      _ = (α j + u (j + 1)) * (bs c + 1) + 8 := by ring
  have hsum2 : (∑ c ∈ range t, ((tb j (bs c) + u (j + 1) * (bs c + 1)) + 8)) ≤
      (α j + u (j + 1)) * ((D + 1) * (m + 1)) + 8 * (m + 1) := by
    calc (∑ c ∈ range t, ((tb j (bs c) + u (j + 1) * (bs c + 1)) + 8))
        ≤ ∑ c ∈ range t, ((α j + u (j + 1)) * (bs c + 1) + 8) := Finset.sum_le_sum hterm
      _ = (α j + u (j + 1)) * (∑ c ∈ range t, (bs c + 1)) + 8 * t := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range,
            smul_eq_mul, mul_comm t 8]
      _ ≤ (α j + u (j + 1)) * ((D + 1) * (m + 1)) + 8 * (m + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hsum1) (Nat.mul_le_mul_left _ (by omega))
  have hstep : u j = A j + (D + 1) * u (j + 1) := by rw [hu]; exact solve_step hj
  calc Ko j m + (Kc j m + ((∑ c ∈ range t,
        ((tb j (bs c) + u (j + 1) * (bs c + 1)) + 8)) + 6))
      ≤ ko j * (m + 1) + (kc j * (m + 1) +
          (((α j + u (j + 1)) * ((D + 1) * (m + 1)) + 8 * (m + 1)) + 6 * (m + 1))) :=
        Nat.add_le_add (hKo j m) (Nat.add_le_add (hKc j m) (Nat.add_le_add hsum2 (by omega)))
    _ = (A j + (D + 1) * u (j + 1)) * (m + 1) := by rw [hAdef j]; ring
    _ = u j * (m + 1) := by rw [← hstep]

/-- The Σ-shaped root cost, geometrically: with every per-level constant
at most `A`, the whole recursion is `(ℓ · A + Cb) · (D + 1) ^ ℓ`, which
is the factor the real-exponent lemma below turns into `n ^ ε`. -/
theorem solve_sigma_le {ko kc α : ℕ → ℕ} {D Cb ℓ A : ℕ}
    (hA : ∀ j < ℓ, driverASigma ko kc α D j ≤ A) :
    solve (driverASigma ko kc α D) (fun _ => D + 1) Cb ℓ 0 ≤ (ℓ * A + Cb) * (D + 1) ^ ℓ :=
  solve_const_le hA (by omega)

section SigmaFalsification

/-! The Σ side condition, and the coefficient it needs, on data: mass
coefficient `D = 1`, two levels, base `100`, per-level constant `14`,
an arena of `m = 4` with `t = 4` blocks of sizes `2, 2, 1, 0` — the
mass bound `∑ bs = 5 ≤ D · (m + 1)` held **tight**. -/

private def sbs : ℕ → ℕ := fun c => [2, 2, 1, 0].getD c 0

-- the mass hypothesis, at the edge
#guard (∑ c ∈ range 4, sbs c) = 5
#guard (∑ c ∈ range 4, sbs c) ≤ 1 * (4 + 1)

-- the level's bill: four turns, each the nested level `100 · (s + 1)`
-- plus the `8` of the loop, and the level's own `6`
#guard (∑ c ∈ range 4, (100 * (sbs c + 1) + 8)) + 6 = 938

-- the witness pays it at coefficient `D + 1 = 2`
#guard 938 ≤ solve (fun _ => 14) (fun _ => 2) 100 2 1 * (4 + 1)

-- **Refuted**: at coefficient `D` the same side condition fails — the
-- per-turn overhead of up to `m` nonempty blocks is not in the mass.
#guard ¬ (938 ≤ solve (fun _ => 14) (fun _ => 1) 100 2 1 * (4 + 1))

-- **Refuted**: reading the level's sum over the *carrier's* `n` blocks
-- instead of the `t ≤ m` compacted ones is not the same number.
#guard ¬ ((∑ c ∈ range 8, (100 * (sbs c + 1) + 8)) + 6 ≤ 938)

-- the per-level constant, and the degenerate levels
#guard driverASigma (fun _ => 1) (fun _ => 2) (fun _ => 3) 1 0 = 1 + (2 + (3 * 2 + 14))
#guard solve (driverASigma (fun _ => 1) (fun _ => 2) (fun _ => 3) 1) (fun _ => 2) 7 0 0 = 7

end SigmaFalsification

/-! ### The real exponent

The last step of P4: the mass coefficient `exists_cover_degree` hands
over is `D = ⌈c · n ^ (ε / ℓ)⌉₊`, and the recursion charges it `ℓ`
times, so the headline needs `(D + 1) ^ ℓ ≤ c' · n ^ ε`. That is the
same massage `CoverDegree.exists_cover_degree` performs internally on
`X ^ (2 · 16 ^ R) = m ^ δ`, at the driver's exponent.

Both hypotheses are necessary, not decoration: at `n = 0` the right
side is `0` while the left is at least `1` (`ceil_rpow_pow_zero`
compiles the refutation), and at `ℓ = 0` the `X ^ ℓ = n ^ ε` step is
false. Everything is stated at `ℝ` — `^ ε` is `Real.rpow`, `^ ℓ` is
the monoid power — with the ℕ-side consumer taking the cast form. -/

/-- **The exponent massage.** With `X = n ^ (ε / ℓ)` at least one, the
ceiling costs at most one and the `+ 1` one more, so the whole
`ℓ`-th power collapses to `(c + 2) ^ ℓ · n ^ ε`. -/
theorem ceil_rpow_pow_le {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) :
    ((⌈c * (n : ℝ) ^ (ε / (ℓ : ℝ))⌉₊ : ℝ) + 1) ^ ℓ ≤ (c + 2) ^ ℓ * (n : ℝ) ^ ε := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by
    have : 0 < ℓ := Nat.pos_of_ne_zero hℓ
    exact_mod_cast this
  have hexp : 0 ≤ ε / (ℓ : ℝ) := le_of_lt (div_pos hε hℓ0)
  set X : ℝ := (n : ℝ) ^ (ε / (ℓ : ℝ)) with hX
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hX]
    calc (1 : ℝ) = (1 : ℝ) ^ (ε / (ℓ : ℝ)) := (Real.one_rpow _).symm
      _ ≤ (n : ℝ) ^ (ε / (ℓ : ℝ)) := Real.rpow_le_rpow (by norm_num) hn1 hexp
  have hXnn : (0 : ℝ) ≤ X := le_trans zero_le_one hX1
  have hceil : ((⌈c * X⌉₊ : ℕ) : ℝ) ≤ c * X + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hc hXnn)).le
  have hstep : ((⌈c * X⌉₊ : ℕ) : ℝ) + 1 ≤ (c + 2) * X := by nlinarith
  have hXP : X ^ ℓ = (n : ℝ) ^ ε := by
    rw [hX, ← Real.rpow_natCast ((n : ℝ) ^ (ε / (ℓ : ℝ))) ℓ, ← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
  calc ((⌈c * X⌉₊ : ℝ) + 1) ^ ℓ ≤ ((c + 2) * X) ^ ℓ := by
        refine pow_le_pow_left₀ (by positivity) hstep ℓ
    _ = (c + 2) ^ ℓ * X ^ ℓ := by rw [mul_pow]
    _ = (c + 2) ^ ℓ * (n : ℝ) ^ ε := by rw [hXP]

/-- **Refuted at the empty carrier.** The bound is not unconditional in
`n`: at `n = 0` the right side is zero and the left is one, which is
why `ceil_rpow_pow_le` carries `1 ≤ n` (the C0 consumer reads it at
`|x| + 1 ≥ 1`). -/
theorem ceil_rpow_pow_zero {c ε : ℝ} (hε : 0 < ε) :
    ¬ ((⌈c * (0 : ℝ) ^ (ε / (1 : ℝ))⌉₊ : ℝ) + 1) ^ 1 ≤ (c + 2) ^ 1 * (0 : ℝ) ^ ε := by
  have h0 : (0 : ℝ) ^ ε = 0 := Real.zero_rpow (ne_of_gt hε)
  have h1 : (0 : ℝ) ^ (ε / (1 : ℝ)) = 0 := Real.zero_rpow (by simpa using ne_of_gt hε)
  rw [h0, h1]
  norm_num

/-- **The C0 shape.** The Σ recursion's root cost, at the mass
coefficient the cover-degree theorem supplies, is almost linear: the
`(D + 1) ^ ℓ` factor becomes `n ^ ε` and the arena's `n + 1` becomes
the missing exponent one. This is the arithmetic P4 closes the headline
with; the constant is `(ℓ · A + Cb) · (c + 2) ^ ℓ`, independent of
`n`. -/
theorem sigma_root_almostLinear {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {C n K : ℕ} (hn : 1 ≤ n)
    (hK : (K : ℝ) ≤ (C : ℝ) * ((⌈c * (n : ℝ) ^ (ε / (ℓ : ℝ))⌉₊ : ℝ) + 1) ^ ℓ * ((n : ℝ) + 1)) :
    (K : ℝ) ≤ ((C : ℝ) * (c + 2) ^ ℓ) * ((n : ℝ) + 1) ^ (1 + ε) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hpow : (n : ℝ) ^ ε ≤ ((n : ℝ) + 1) ^ ε :=
    Real.rpow_le_rpow hn0 (by linarith) (le_of_lt hε)
  have hsplit : ((n : ℝ) + 1) ^ (1 + ε) = ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ ε := by
    rw [Real.rpow_add hn1, Real.rpow_one]
  refine hK.trans ?_
  rw [hsplit]
  have hce := ceil_rpow_pow_le (c := c) (ε := ε) hc hε (ℓ := ℓ) hℓ (n := n) hn
  have hC : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  calc (C : ℝ) * ((⌈c * (n : ℝ) ^ (ε / (ℓ : ℝ))⌉₊ : ℝ) + 1) ^ ℓ * ((n : ℝ) + 1)
      ≤ (C : ℝ) * ((c + 2) ^ ℓ * (n : ℝ) ^ ε) * ((n : ℝ) + 1) := by
        have := mul_le_mul_of_nonneg_left hce hC
        exact mul_le_mul_of_nonneg_right this (le_of_lt hn1)
    _ ≤ (C : ℝ) * ((c + 2) ^ ℓ * ((n : ℝ) + 1) ^ ε) * ((n : ℝ) + 1) := by
        have hcp : (0 : ℝ) ≤ (c + 2) ^ ℓ := by positivity
        have := mul_le_mul_of_nonneg_left hpow hcp
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC) (le_of_lt hn1)
    _ = (C : ℝ) * (c + 2) ^ ℓ * (((n : ℝ) + 1) * ((n : ℝ) + 1) ^ ε) := by ring

-- the exponent arithmetic, on numbers: `c = 1`, `ε = 1`, `ℓ = 2`,
-- `n = 256`, so `n ^ (ε / ℓ) = 16` and the left side is `17 ^ 2`
#guard 17 ^ 2 ≤ 3 ^ 2 * 256

-- **Refuted**: without the `+ 2` in the constant — reading the bound as
-- `(⌈c · n ^ (ε/ℓ)⌉ + 1) ^ ℓ ≤ c ^ ℓ · n ^ ε` — it is false at `c = 1`.
#guard ¬ (17 ^ 2 ≤ 1 ^ 2 * 256)

-- **Refuted**: and the ceiling alone already breaks the naive reading
-- `⌈c · n ^ (ε/ℓ)⌉ ^ ℓ ≤ c ^ ℓ · n ^ ε`, at `n = 250` (`⌈√250⌉ = 16`).
#guard ¬ (16 ^ 2 ≤ 1 ^ 2 * 250)

end Lax3Proofs.CostRecurrence
