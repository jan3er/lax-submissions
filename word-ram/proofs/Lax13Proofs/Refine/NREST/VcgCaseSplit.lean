import Lax13Proofs.Refine.NREST.Automation
import Lean.Meta.Tactic.Grind.Cases
import Lean.Meta.Tactic.Grind.CasesMatch

/-!
# Shallow VCG case splitting

This is the deliberately small port of `VCG_Case_Splitter` from the corrected
Sepreftime `MoreCurrAutomation.thy:73–131` pin
`c1c987b45ec886d289ba215768182ac87b82f20d`.  It only looks through the two goal
shapes used by that splitter (`_ ≤ gwp prog _` and `progress prog`), and it
only acts when `prog` itself starts with an `Option` or `Sum` match.  It does
not recursively search a program, split arbitrary expressions, or extend the
separate refinement-condition generator.
-/

namespace Lax13Proofs.Refine
namespace NRest

open Lean Elab Tactic Meta

namespace VcgCaseSplit

/-- Extract the program from exactly the supported VCG goal heads. -/
private def program? (target : Expr) : Option Expr := do
  let fn := target.getAppFn.constName?
  if fn == some ``LE.le then
    let args := target.getAppArgs
    guard (args.size ≥ 2)
    let rhs := args.back!
    guard (rhs.getAppFn.constName? == some ``gwp)
    let gwpArgs := rhs.getAppArgs
    guard (gwpArgs.size ≥ 2)
    return gwpArgs[gwpArgs.size - 2]!
  else if fn == some ``progress then
    return target.getAppArgs.back!
  else
    none

/-- Is this matcher discriminating on the intentionally supported shallow
`Option`/`Sum` fragment? -/
private def supportedDiscr (app : MatcherApp) : MetaM Bool := do
  let some discr := app.discrs.back? | return false
  let ty ← whnf (← inferType discr)
  let some n := ty.getAppFn.constName? | return false
  return n == ``Option || n == ``Sum

/-- Split a supported VCG program-head match once.  `casesMatch` supplies the
branch equations, so dependent matches and non-variable discriminants retain
the same safe abstraction behaviour as Lean's compiled matcher splitter. -/
def split (goal : MVarId) : TacticM (List MVarId) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let some prog := program? target
    | throwError "vcg_split_case: expected `_ ≤ gwp prog _` or `progress prog`"
  let some app ← matchMatcherApp? prog (alsoCasesOn := true)
    | throwError "vcg_split_case: the program head is not a datatype match"
  unless ← supportedDiscr app do
    throwError "vcg_split_case: only Option and Sum program-head matches are supported"
  if ← isMatcher app.matcherName then
    Lean.Meta.Grind.casesMatch goal prog
  else
    let some discr := app.discrs.back?
      | throwError "vcg_split_case: malformed casesOn application"
    Lean.Meta.Grind.cases goal discr

end VcgCaseSplit

/-- One shallow source-shaped case split at the program head of a supported
`gwp`/`progress` goal. -/
elab "vcg_split_case" : tactic => do
  let goal ← getMainGoal
  replaceMainGoal (← VcgCaseSplit.split goal)

/-! ## Gates -/

section Gates

private noncomputable def optionProg (o : Option Nat) : NRest Unit ECost :=
  match o with
  | none => NRest.returnT ()
  | some _ => NRest.returnT ()

theorem vcgSplitGwpGate (o : Option Nat) :
    ((0 : ECost) : WithBot ECost) ≤ gwp (optionProg o) (fun _ => 0) := by
  unfold optionProg
  vcg_split_case <;> intros <;> subst_vars <;> apply gwp_RETURNT_I <;> simp

theorem vcgSplitProgressGate (s : Sum Unit Unit) :
    progress
      (match s with
       | Sum.inl _ => NRest.consume (NRest.returnT ()) (ACost.cost "step" (1 : ℕ∞))
       | Sum.inr _ => NRest.consume (NRest.returnT ()) (ACost.cost "step" (1 : ℕ∞))) := by
  vcg_split_case <;> intros <;> subst_vars <;>
    exact progress_consume_returnT Sanity.cost_step_pos ()

/-- Negative head-shape control: the splitter refuses to search beneath a
non-match program head. -/
example : progress
    (NRest.consume (NRest.returnT ()) (ACost.cost "step" (1 : ℕ∞)) : NRest Unit ECost) := by
  fail_if_success vcg_split_case
  exact progress_consume_returnT Sanity.cost_step_pos ()

end Gates

/-- info: 'Lax13Proofs.Refine.NRest.vcgSplitGwpGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vcgSplitGwpGate

/-- info: 'Lax13Proofs.Refine.NRest.vcgSplitProgressGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vcgSplitProgressGate

end NRest
end Lax13Proofs.Refine
