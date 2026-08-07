import Lax3Proofs.RamDriverBot

/-!
**The base case's shed, recorded** — R1.8-T4a, the cost half.

`RamDriver.baseCom` used to be `reprCom` followed by the depth's sweep.
The representative scan's only product is the array `"rep"`, and the
only text that reads it is the `exU` case of `RamDriver.botCom` — a case
generated for no formula any table holds, because every tabled formula
is local (`FormulaTables.tableRank_of_mem_tablesAt`, read as
`Refine.DeadRowProbe.tabled_isLocal`) and `botCom` on a local formula
has no `exU` node. So the scan guarded dead code, and the base pass paid
for it: a second carrier walk whose turn is an inner loop over the whole
row space `2 ^ sigL cap mb ℓ`.

`RamDriverBot.baseCost` now sheds exactly that summand. This file is the
ledger of the shed: what the old constant was (`oldBaseCost`), that the
difference is `RamDriverBot.reprCost` on the nose (`shed_eq_reprCost`),
that the new constant is *strictly* smaller (`baseCost_lt_old`), and
that the shed is not a rounding — it is at least `2 ^ sigL cap mb ℓ`
per carrier vertex (`pow_mul_le_shed`).

# What did NOT change

The base pass still walks the **carrier**, so the base's charge is still
carrier-linear and `Refine.G2CostProbe.hKbase_gap` still refutes a
weight-linear budget for it. What changed is the gap's floor: it used to
be the scan's `reprBodyCost · n` — a floor guarding dead code, which is
why the design calls the scan's removal free — and it is now the
sweep's own `(turnCost + 4) · n`, which is real work at every vertex and
which only the member-list header (wave T4b, design §2.5(b)) moves.
`baseCoeffA` sheds its `reprBodyCost` term with the scan; the gap is
re-proved there at the shed coefficient.

Nothing about `RamDriver.reprCom`, `RamDriverBot.repr_spec` or
`RamDriverBot.reprCost` is deleted: they stay compiled as the machine
half of the contingency `Refine.DeadRowProbe.sat_exU_bot_via_cluster`
describes, and `oldBaseCost` below is the only remaining consumer of
`reprCost` in the package.
-/

namespace Lax3Proofs.Refine.BaseShed

open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriverBot

variable {q_top cap mb ℓ n : ℕ} {φ : Lax3.FirstOrder.FO 0}

/-- **The base cost as it stood before R1.8-T4a**: the representative
scan's carrier walk plus the depth's sweep. Kept verbatim so the shed is
a statement and not a memory. -/
noncomputable def oldBaseCost (q_top cap mb ℓ n : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  reprCost ℓ (sigL cap mb ℓ) n + ((turnCost q_top cap mb ℓ φ + 4) * n + 6)

/-- The old cost is the scan's plus the new one — the shed is a summand,
not a re-derivation. -/
theorem oldBaseCost_eq :
    oldBaseCost q_top cap mb ℓ n φ =
      reprCost ℓ (sigL cap mb ℓ) n + baseCost q_top cap mb ℓ n φ := rfl

/-- **What the base pass shed**: the representative scan's cost, exactly. -/
theorem shed_eq_reprCost :
    oldBaseCost q_top cap mb ℓ n φ - baseCost q_top cap mb ℓ n φ =
      reprCost ℓ (sigL cap mb ℓ) n := by
  rw [oldBaseCost_eq]; omega

/-- The scan's cost is positive at every carrier size — it opens and
closes even on the empty carrier. -/
theorem reprCost_pos : 0 < reprCost ℓ (sigL cap mb ℓ) n := by
  rw [reprCost]
  exact Nat.lt_of_lt_of_le (by norm_num) (Nat.le_add_left 8 _)

/-- **The shed is strict**: the base pass costs strictly less than it
did, at every carrier size and every formula. -/
theorem baseCost_lt_old :
    baseCost q_top cap mb ℓ n φ < oldBaseCost q_top cap mb ℓ n φ := by
  have h : 0 < reprCost ℓ (sigL cap mb ℓ) n := reprCost_pos
  rw [oldBaseCost_eq]
  omega

/-- **The shed is not a constant.** It is at least the whole row space
per carrier vertex: the scan's turn ran an inner loop over `2 ^ L`
recorded rows, so the summand removed dominates `2 ^ sigL cap mb ℓ · n`.
This is the sense in which the `exU` case was expensive dead code. -/
theorem pow_mul_le_shed :
    2 ^ sigL cap mb ℓ * n ≤
      oldBaseCost q_top cap mb ℓ n φ - baseCost q_top cap mb ℓ n φ := by
  rw [shed_eq_reprCost, reprCost, reprBodyCost]
  refine le_trans (Nat.mul_le_mul_right n ?_) (Nat.le_add_right _ 8)
  calc 2 ^ sigL cap mb ℓ
      ≤ (scanCost ℓ (sigL cap mb ℓ) + 4) * 2 ^ sigL cap mb ℓ :=
        Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ (scanCost ℓ (sigL cap mb ℓ) + 4) * 2 ^ sigL cap mb ℓ + 23 + 4 := by omega

/-! ### Falsification: the two constants on numbers

The base cost changed, so it is checked on a concrete instance in both
directions before it is used. `turnCost` is noncomputable (`tablesAt`),
so the walk's per-vertex charge is a parameter `K` here and the scan's
half is the **real** `reprCost` — the only half that moved.

The instance is depth `ℓ = 3`, palette width `L = 4` (sixteen rows), a
carrier of `100`, and a per-vertex turn charge `K = 10`. -/

section Falsification

/-- The new base cost at turn charge `K` on a carrier of `n` — the
sweep's shape, `RamDriverBot.baseCost` with `turnCost` opened up. -/
private def nb (K n : ℕ) : ℕ := (K + 4) * n + 6

/-- The old base cost: the scan's real cost at depth `jd`, palette `L`,
plus the same sweep. -/
private def ob (jd L K n : ℕ) : ℕ := reprCost jd L n + nb K n

-- The new constant, both directions.
#guard nb 10 100 = 1406
#guard ¬ (nb 10 100 = 1405)
#guard ¬ (nb 10 100 = 1407)

-- The scan's real cost at the instance: an inner loop over `2 ^ 4 = 16`
-- recorded rows at every one of the `100` vertices.
#guard scanCost 3 4 = 73
#guard reprBodyCost 3 4 = 1255
#guard reprCost 3 4 100 = 125908
#guard ¬ (reprCost 3 4 100 = 125907)
#guard ¬ (reprCost 3 4 100 = 125909)

-- The old constant, both directions, and the shed between them.
#guard ob 3 4 10 100 = 127314
#guard ¬ (ob 3 4 10 100 = 127313)
#guard ¬ (ob 3 4 10 100 = 127315)
#guard ob 3 4 10 100 - nb 10 100 = 125908

-- The shed dominates the row space per vertex: `2 ^ 4 · 100 = 1600`.
#guard 2 ^ 4 * 100 ≤ ob 3 4 10 100 - nb 10 100
#guard ¬ (ob 3 4 10 100 - nb 10 100 ≤ 1599)

-- **The proportion, pinned both ways.** At this instance the dead scan
-- was between eighty and ninety times the whole surviving base pass —
-- the base case did not shave a constant, it stopped paying for a
-- second, wider walk.
#guard 80 * nb 10 100 ≤ ob 3 4 10 100 - nb 10 100
#guard ¬ (90 * nb 10 100 ≤ ob 3 4 10 100 - nb 10 100)

-- **Negative control.** The shed is not the whole cost: the sweep half
-- survives untouched, and it is still carrier-linear — doubling the
-- carrier doubles it exactly, which is why
-- `Refine.G2CostProbe.hKbase_gap` survives the shed (the header is wave
-- T4b's, not this one's).
#guard nb 10 200 - nb 10 100 = nb 10 100 - nb 10 0
#guard ¬ (nb 10 100 ≤ 10 * (0 + 1))

end Falsification

/-- info: 'Lax3Proofs.Refine.BaseShed.shed_eq_reprCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shed_eq_reprCost

/-- info: 'Lax3Proofs.Refine.BaseShed.baseCost_lt_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baseCost_lt_old

/-- info: 'Lax3Proofs.Refine.BaseShed.pow_mul_le_shed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pow_mul_le_shed

end Lax3Proofs.Refine.BaseShed
