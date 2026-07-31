import Lax13Proofs.Refine.NREST.AutomationAttrs
import Lax13Proofs.Refine.NREST.BackwardsReasoning

/-!
Cost-side-condition automation for `NRest`.

This is the source-shaped port of the corresponding section of
Sepreftime's `NREST_Automation.thy`.  The solver does not flatten a cost
vector pointwise and split on every currency name.  Instead it rotates
the two additive expressions, groups syntactically equal singleton
currencies, and leaves one scalar inequality per currency.  Consequently
the debug variant can retain the name of the currency that failed.

The source's `norm_cost` entries involving `costmult` have no Lean
counterpart: the tower represents repeated cost with additive scalar
action (`n • C`).  The two lemmas `ACost.nsmul_add` and
`ACost.nsmul_cost` below are their live analogue.  The source's
`the_acost_propagate` is `ACost.toFun_add`, already part of the bounded
collection.  No dead `costmult` vocabulary is introduced.
-/

namespace Lax13Proofs.Refine

namespace ACost

/-- Scalar action distributes through a cost-vector sum. -/
theorem nsmul_add {κ γ : Type} [AddCommMonoid γ] (n : ℕ) (a b : ACost κ γ) :
    n • (a + b) = n • a + n • b := by
  ext k
  induction n with
  | zero => simp
  | succ n ih => simp only [succ_nsmul, toFun_add] at ih ⊢; rw [ih]; ac_rfl

/-- Repeated payment of one currency is one payment of the repeated amount. -/
theorem nsmul_cost {κ γ : Type} [DecidableEq κ] [AddMonoid γ]
    (n : ℕ) (c : κ) (x : γ) : n • cost c x = cost c (n • x) := by
  ext k
  rw [toFun_nsmul, toFun_cost, toFun_cost]
  split <;> simp

end ACost

attribute [norm_cost]
  ACost.cost_zero ACost.cost_add_cost ACost.nsmul_add ACost.nsmul_cost
  ACost.toFun_zero ACost.toFun_add ACost.toFun_nsmul ACost.toFun_cost
  liftACost_zero liftACost_add liftACost_cost
  NRest.timerefineA_zero NRest.timerefineA_add NRest.timerefineA_cost
  NRest.timerefineA_cost_one
  NRest.TId_apply

attribute [norm_pp]
  NRest.pp_TId_right NRest.pp_TId_left NRest.pp_update

namespace NRest

/-! ## The structural side-condition state and its transitions -/

/-- The source's `leq_sidecon`, fixed to its source carrier `ECost`. -/
def leqSidecon (a as₁ as₂ b bs₁ bs₂ : ECost) (P : Prop) : Prop :=
  a + as₁ + as₂ ≤ b + bs₁ + bs₂ ∧ P

theorem leqScInitAdd {a as bs : ECost} :
    leqSidecon a 0 (as + 0) 0 0 (bs + 0) True → a + as ≤ bs := by
  simp [leqSidecon]

theorem leqScInitSingle {a bs : ECost} :
    leqSidecon a 0 0 0 0 (bs + 0) True → a ≤ bs := by
  simp [leqSidecon]

theorem leqScLSucc {n : String} {x y : ℕ∞} {ar as bs P} :
    leqSidecon (ACost.cost n (x + y)) ar as 0 0 bs P →
      leqSidecon (ACost.cost n x) ar (ACost.cost n y + as) 0 0 bs P := by
  simp only [leqSidecon]
  intro h
  rw [← ACost.cost_add_cost] at h
  simpa only [add_assoc, add_left_comm, add_comm] using h

theorem leqScLFail {n m : String} {x z : ℕ∞} {ar as bs P} :
    leqSidecon (ACost.cost n x) (ACost.cost m z + ar) as 0 0 bs P →
      leqSidecon (ACost.cost n x) ar (ACost.cost m z + as) 0 0 bs P := by
  simp only [leqSidecon]
  intro h
  simpa only [add_assoc, add_left_comm, add_comm] using h

theorem leqScLDone {n : String} {x : ℕ∞} {l bs P} :
    leqSidecon (ACost.cost n x) l 0 (ACost.cost n 0) 0 bs P →
      leqSidecon (ACost.cost n x) l 0 0 0 bs P := by
  intro h
  simpa only [ACost.cost_zero] using h

theorem leqScRSucc {n : String} {x y z : ℕ∞} {l bs₁ bs₂ P} :
    leqSidecon (ACost.cost n x) l 0 (ACost.cost n (y + z)) bs₁ bs₂ P →
      leqSidecon (ACost.cost n x) l 0 (ACost.cost n y) bs₁
        (ACost.cost n z + bs₂) P := by
  simp only [leqSidecon]
  intro h
  rw [← ACost.cost_add_cost] at h
  simpa only [add_assoc, add_left_comm, add_comm] using h

theorem leqScRFail {n m : String} {x y z : ℕ∞} {l bs₁ bs₂ P} :
    leqSidecon (ACost.cost n x) l 0 (ACost.cost n y) (ACost.cost m z + bs₁) bs₂ P →
      leqSidecon (ACost.cost n x) l 0 (ACost.cost n y) bs₁ (ACost.cost m z + bs₂) P := by
  simp only [leqSidecon]
  intro h
  simpa only [add_assoc, add_left_comm, add_comm] using h

theorem costMono {n : String} {x y : ℕ∞} (h : x ≤ y) :
    ACost.cost n x ≤ ACost.cost n y := by
  exact ACost.le_def.mpr fun k => by
    rw [ACost.toFun_cost, ACost.toFun_cost]
    split <;> simp_all

theorem ecostNonneg (r : ECost) : 0 ≤ r :=
  ACost.le_def.mpr fun _ => zero_le

theorem leqScRDoneAll {n : String} {x y : ℕ∞} {r : ECost} {P : Prop}
    (h : P ∧ x ≤ y) :
    leqSidecon (ACost.cost n x) 0 0 (ACost.cost n y) r 0 P := by
  refine ⟨?_, h.1⟩
  simp only [add_zero]
  have hr : ACost.cost n y + 0 ≤ ACost.cost n y + r :=
    add_le_add le_rfl (ecostNonneg r)
  exact le_trans (costMono h.2) (by simpa only [add_zero] using hr)

theorem leqScRDone1 {n : String} {x y : ℕ∞} {l ls r : ECost} {P : Prop} :
    leqSidecon l 0 ls 0 0 r (P ∧ x ≤ y) →
      leqSidecon (ACost.cost n x) (l + ls) 0 (ACost.cost n y) r 0 P := by
  rintro ⟨hcost, hP, hxy⟩
  refine ⟨?_, hP⟩
  simp only [zero_add, add_zero] at hcost ⊢
  exact add_le_add (costMono hxy) hcost

/-- Identity wrapper used only to retain the failing currency in debug goals. -/
def scSolveDebug (_n : String) (P : Prop) : Prop := P

theorem leqScRDoneAllDebug {n : String} {x y : ℕ∞} {r : ECost} {P : Prop}
    (h : P ∧ scSolveDebug n (x ≤ y)) :
    leqSidecon (ACost.cost n x) 0 0 (ACost.cost n y) r 0 P :=
  leqScRDoneAll h

theorem leqScRDone1Debug {n : String} {x y : ℕ∞} {l ls r : ECost} {P : Prop} :
    leqSidecon l 0 ls 0 0 r (P ∧ scSolveDebug n (x ≤ y)) →
      leqSidecon (ACost.cost n x) (l + ls) 0 (ACost.cost n y) r 0 P :=
  leqScRDone1

/-! ## The public solver front ends -/

open Lean Elab Tactic Meta

namespace ScSolve

private def addArgs? (e : Expr) : Option (Expr × Expr) :=
  let (f, args) := e.getAppFnArgs
  if (f == ``HAdd.hAdd ∨ f == ``Add.add) ∧ args.size ≥ 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else none

private def costArgs? (e : Expr) : Option (Expr × Expr) :=
  let (f, args) := e.getAppFnArgs
  if f == ``ACost.cost ∧ args.size ≥ 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else none

private def stateArgs? (e : Expr) : Option (Array Expr) :=
  let (f, args) := e.getAppFnArgs
  if f == ``leqSidecon ∧ args.size == 7 then some args else none

private def applyOne (g : MVarId) (n : Name) : TacticM MVarId := do
  let gs ← g.apply (← mkConstWithFreshMVarLevels n)
  let ps ← gs.filterM fun g' => g'.withContext do isProp (← g'.getType)
  match ps with
  | [g'] => pure g'
  | _ => throwError "sc_solve: internal rule {n} produced {ps.length} proposition goals"

/- Deterministic source transition walk.  The syntactic tests are
load-bearing: unrestricted `apply leqScLSucc` can instantiate an atomic
amount with `?x + ?y`, a non-decreasing transition the source matcher
never performs. -/
mutual
  partial def walk (debug : Bool) (g : MVarId) : TacticM MVarId := g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some a := stateArgs? target | pure g
    let some (ln, _) := costArgs? a[0]! | pure g
    if let some (h, _) := addArgs? a[2]! then
      let some (rn, _) := costArgs? h | pure g
      let same ← isDefEq ln rn
      walk debug (← applyOne g (if same then ``leqScLSucc else ``leqScLFail))
    else
      right debug (← applyOne g ``leqScLDone)

  partial def right (debug : Bool) (g : MVarId) : TacticM MVarId := g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some a := stateArgs? target | pure g
    let some (ln, _) := costArgs? a[0]! | pure g
    if let some (h, _) := addArgs? a[5]! then
      let some (rn, _) := costArgs? h | pure g
      let same ← isDefEq ln rn
      right debug (← applyOne g (if same then ``leqScRSucc else ``leqScRFail))
    else
      let done := if (addArgs? a[1]!).isSome then
        if debug then ``leqScRDone1Debug else ``leqScRDone1
      else if debug then ``leqScRDoneAllDebug else ``leqScRDoneAll
      walk debug (← applyOne g done)
end

end ScSolve

elab "sc_solve_core" : tactic => do
  let g ← getMainGoal
  replaceMainGoal [← ScSolve.walk false g]

elab "sc_solve_core_debug" : tactic => do
  let g ← getMainGoal
  replaceMainGoal [← ScSolve.walk true g]

macro "sc_solve'" : tactic =>
  `(tactic|
    (first | simp only [add_assoc] | skip) <;>
      (first | apply leqScInitAdd | apply leqScInitSingle) <;>
        (first | simp only [add_assoc] | skip) <;> sc_solve_core)

macro "sc_solve" : tactic =>
  `(tactic| first | (simp only [norm_cost] <;> sc_solve') | sc_solve')

macro "sc_solve'_debug" : tactic =>
  `(tactic|
    (first | simp only [add_assoc] | skip) <;>
      (first | apply leqScInitAdd | apply leqScInitSingle) <;>
        (first | simp only [add_assoc] | skip) <;> sc_solve_core_debug)

macro "sc_solve_debug" : tactic =>
  `(tactic| first | (simp only [norm_cost] <;> sc_solve'_debug) | sc_solve'_debug)

/-! ## Canonical upper-bound synthesis -/

theorem leqScLTerminateSpecial {n : String} {x : ℕ∞} {P : Prop} (h : P) :
    leqSidecon (ACost.cost n x) 0 0 0 0 (ACost.cost n x + 0) P := by
  unfold leqSidecon
  exact ⟨by simp, h⟩

theorem leqScLDoneSpecial {n : String} {x : ℕ∞} {l bs : ECost} {P : Prop} :
    leqSidecon 0 l 0 0 0 (bs + 0) P →
      leqSidecon (ACost.cost n x) l 0 0 0 ((ACost.cost n x + bs) + 0) P := by
  rintro ⟨h, hP⟩
  refine ⟨?_, hP⟩
  simpa only [zero_add, add_zero, add_comm] using add_le_add_left h (ACost.cost n x)

theorem leqScLNextRowSpecial {n : String} {x : ℕ∞} {ls bs : ECost} {P : Prop} :
    leqSidecon (ACost.cost n x) 0 ls 0 0 bs P →
      leqSidecon 0 (ACost.cost n x + ls) 0 0 0 bs P := by
  simp [leqSidecon]

namespace ScSolve

partial def upper (g : MVarId) : TacticM MVarId := g.withContext do
  let target ← instantiateMVars (← g.getType)
  let some a := stateArgs? target | pure g
  let some (ln, _) := costArgs? a[0]! | pure g
  if let some (h, _) := addArgs? a[2]! then
    let some (rn, _) := costArgs? h | pure g
    let same ← isDefEq ln rn
    upper (← applyOne g (if same then ``leqScLSucc else ``leqScLFail))
  else if (addArgs? a[1]!).isSome then
    let g ← applyOne g ``leqScLDoneSpecial
    upper (← applyOne g ``leqScLNextRowSpecial)
  else
    applyOne g ``leqScLTerminateSpecial

end ScSolve

elab "sc_solve_upperbound_core" : tactic => do
  let g ← getMainGoal
  replaceMainGoal [← ScSolve.upper g]

macro "sc_solve_upperbound" : tactic =>
  `(tactic|
    (first | simp only [add_assoc] | skip) <;>
      (first | apply leqScInitAdd | apply leqScInitSingle) <;>
        (first | simp only [add_assoc] | skip) <;> sc_solve_upperbound_core)

/-! ## Gates -/

section Gates

theorem mixedCurrencyGate :
    ACost.cost "a" 1 + ACost.cost "b" (1 : ℕ∞) + ACost.cost "b" 1 +
        ACost.cost "b" 1 + ACost.cost "a" 2 ≤
      ACost.cost "a" 3 + ACost.cost "b" 3 := by
  sc_solve'
  norm_num

theorem upperBoundSynthesisGate : ∃ ub : ECost,
    ACost.cost "a" 1 + ACost.cost "b" 2 + ACost.cost "b" 2 + ACost.cost "b" 5 ≤ ub ∧
      ub = ACost.cost "a" 1 + ACost.cost "b" 9 := by
  apply Exists.intro
  constructor
  · sc_solve_upperbound
    trivial
  · rfl

theorem debugCurrencyGate {x y : ℕ∞} (h : x ≤ y) :
    ACost.cost "debug-currency" x ≤ ACost.cost "debug-currency" y := by
  sc_solve'_debug
  exact ⟨trivial, by simpa using h⟩

theorem suppliedBoundGate :
    ACost.cost "a" 1 + ACost.cost "b" (2 : ℕ∞) + ACost.cost "b" 2 + ACost.cost "b" 5 ≤
      ACost.cost "a" 1 + ACost.cost "b" 9 := by
  sc_solve'
  norm_num

example (n : ℕ) :
    liftACost (n • (ACost.cost "a" 2 + ACost.cost "b" 3)) =
      ACost.cost "a" ((n • 2 : ℕ) : ℕ∞) + ACost.cost "b" ((n • 3 : ℕ) : ℕ∞) := by
  simp only [norm_cost]

example {κ : Type} [DecidableEq κ] (R : κ → ACost κ ℕ∞) (a : κ) :
    pp TId (Function.update R a (ACost.cost a 1)) =
      Function.update R a (ACost.cost a 1) := by
  simp only [norm_pp, timerefineA_TId]

example {κ κ' : Type} [DecidableEq κ] (A : κ' → ACost κ ℕ∞)
    (B : κ → ACost κ' ℕ∞) (a : κ) (b : ACost κ' ℕ∞) :
    pp A (Function.update B a b) =
      Function.update (pp A B) a (timerefineA A b) := by
  simp only [norm_pp]

example {κ κ' : Type} [DecidableEq κ] (E : κ → ACost κ' ℕ∞) (hE : wfR'' E)
    (a b : κ) :
    timerefineA E (ACost.cost a 1 + ACost.cost b 1) = E a + E b := by
  simp only [norm_cost, one_mul, hE]

example {κ κ' : Type} [DecidableEq κ] (E : κ → ACost κ' ℕ∞)
    (a : κ) (t : ℕ∞) :
    timerefineA E (ACost.cost a t) = ⟨fun x => t * (E a).toFun x⟩ := by
  simp only [norm_cost]

/-- `solve` confirms that the debug front end leaves its labelled scalar
obligation instead of claiming to decide it. -/
example (n : ℕ) :
    ACost.cost "nonlinear-debug" ((n + n : ℕ) : ℕ∞) ≤
      ACost.cost "nonlinear-debug" ((2 * n : ℕ) : ℕ∞) := by
  fail_if_success (solve | sc_solve_debug)
  sc_solve_debug
  constructor
  · trivial
  · show scSolveDebug "nonlinear-debug"
      (((n + n : ℕ) : ℕ∞) ≤ 0 + ((2 * n : ℕ) : ℕ∞))
    unfold scSolveDebug
    simpa only [zero_add] using
      (show ((n + n : ℕ) : ℕ∞) ≤ ((2 * n : ℕ) : ℕ∞) by
        exact_mod_cast (show n + n ≤ 2 * n by omega))

end Gates

/-- info: 'Lax13Proofs.Refine.NRest.mixedCurrencyGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixedCurrencyGate

/-- info: 'Lax13Proofs.Refine.NRest.upperBoundSynthesisGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperBoundSynthesisGate

/-- info: 'Lax13Proofs.Refine.NRest.debugCurrencyGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms debugCurrencyGate

end NRest
end Lax13Proofs.Refine
