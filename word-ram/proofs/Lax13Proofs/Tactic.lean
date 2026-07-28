import Lax13Proofs.Spec

/-!
`run_vcg`: symbolic execution of a concrete `Com`, as a tactic.

A straight-line block of IMP+ is proved by hand the same way every time.
Apply `Run.assign` or `Run.store`, exhibit the value of the expression
one subexpression at a time, prove each of those values below `B`, chain
the pieces with `Run.seq`, split on every `ite`, and finish with
`Run.mono` against the cost the statement announces. `countBlock_spec`
in Lax15 is five lines of program and was twenty-one lines of proof;
`seenBlock_spec` is seven lines of program and was fifty-one. None of it
is mathematics.

`run_vcg` does the walk. What is left for the reader is exactly the two
things the walk cannot know: what the block *computed* — one goal per
control-flow path, in the environment the path ends in — and, where the
precondition is not literally a hypothesis, why each value stayed below
the bound.

Three implementation decisions are what make it usable.

* **The derivation is a `have` chain, not one term.** Every atomic run
  and every combination is `assert`ed as a named hypothesis and the
  consumed pieces are cleared. A single nested `Run.seq`/`Run.ite`
  application over a chain of `setVar`-bound environments blows the whnf
  heartbeat limit — this was learned the hard way — and the chain also
  keeps the local context of the goals the user sees down to a single
  `Run`.
* **The value bound is discharged where it arises, or deferred.** Each
  `_ < B` obligation is tried with `omega`, then with `simp` followed by
  `omega`, against the precondition as it stands at that point of the
  walk. What neither closes is handed back as a goal, in the branch it
  came from, with that branch's case hypotheses in scope — which is what
  a bound like `ρ.vars "cnted" = 0 → ρ.vars "u" < ρ.vars "w" →
  ρ.vars "ro" + 1 < B` needs.
* **A branch's case hypothesis is inaccessible.** Splitting `ite`s
  generate `ρ.vars "cnted" = 0` and its negation; naming them would
  invent names the user has to guess and that shift when the program
  does. They are in scope for `simp_all`, `omega` and `‹_›`, and that is
  the whole interface.

Loops are deliberately not walked: `Spec.while_potential`,
`Spec.while_count` and `Spec.forRange` want an invariant and a potential,
which is content and not bookkeeping. A loop enters a block the way any
already-proved phase does — `run_vcg [my_loop_spec]` steps over the
command the specification is about, owing its precondition and giving
back its postcondition. Handed nothing, the tactic stops at the loop
with an error naming it, rather than guessing.
-/

namespace Lax13Proofs.Reasoning

open Lax13Proofs.Imp

/-! ### The rules the walk emits

The kit's own rules take their arguments implicitly, which is right for
a human and wrong for a metaprogram: an implicit that the premises do
not determine — the assigned variable of `Run.assign`, the untaken
branch of `Run.ite_true` — comes back as an unassigned metavariable. So
the walk emits these instead. They are the same rules with every
argument explicit and in a fixed order, plus the two conveniences a
symbolic execution wants: an operator's value in normal form (`m + n`,
not `Bop.add.apply m n`) and a condition's truth already decided. -/

namespace RunStep

/-! #### Evaluating an expression -/

theorem eval_lit (B n : ℕ) (σ : Env) (h : n < B) :
    (Expr.lit n).evalB B σ = some n := evalB_lit h

theorem eval_var (B : ℕ) (σ : Env) (x : String) (h : σ.vars x < B) :
    (Expr.var x).evalB B σ = some (σ.vars x) := evalB_var h

/-- An array read, with the value named by `getD` rather than left as an
existential: the walk owes the range condition anyway, and `getD` is the
form every invariant in the repo reads an array in. -/
theorem eval_get (B : ℕ) (σ : Env) (a : String) (i : Expr) (k : ℕ)
    (hi : i.evalB B σ = some k) (hk : k < (σ.arrs a).length)
    (h : (σ.arrs a).getD k 0 < B) :
    (Expr.get a i).evalB B σ = some ((σ.arrs a).getD k 0) := by
  refine evalB_get hi ?_ h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem eval_add (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m + n < B) :
    (Expr.bin .add e f).evalB B σ = some (m + n) := evalB_bin he hf h

theorem eval_sub (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m - n < B) :
    (Expr.bin .sub e f).evalB B σ = some (m - n) := evalB_bin he hf h

theorem eval_mul (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m * n < B) :
    (Expr.bin .mul e f).evalB B σ = some (m * n) := evalB_bin he hf h

theorem eval_div (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m / n < B) :
    (Expr.bin .div e f).evalB B σ = some (m / n) := evalB_bin he hf h

theorem eval_and (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : Nat.land m n < B) :
    (Expr.bin .and e f).evalB B σ = some (Nat.land m n) := evalB_bin he hf h

theorem eval_or (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : Nat.lor m n < B) :
    (Expr.bin .or e f).evalB B σ = some (Nat.lor m n) := evalB_bin he hf h

theorem eval_xor (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : Nat.xor m n < B) :
    (Expr.bin .xor e f).evalB B σ = some (Nat.xor m n) := evalB_bin he hf h

theorem eval_shiftl (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m * 2 ^ n < B) :
    (Expr.bin .shiftl e f).evalB B σ = some (m * 2 ^ n) := evalB_bin he hf h

theorem eval_shiftr (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m / 2 ^ n < B) :
    (Expr.bin .shiftr e f).evalB B σ = some (m / 2 ^ n) := evalB_bin he hf h

/-! #### Deciding a condition

The walk splits on the *arithmetic* proposition, not on the `Bool` the
semantics returns, so that the hypothesis the user is left with is
`ρ.vars "cnted" = 0` and not `(Cond.eq _ _).evalB B ρ = some true`. -/

theorem cond_eq_true (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m = n) :
    (Cond.eq e f).evalB B σ = some true := by
  rw [evalB_condEq he hf, h]; simp

theorem cond_eq_false (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : ¬ m = n) :
    (Cond.eq e f).evalB B σ = some false := by
  rw [evalB_condEq he hf]; simp [h]

theorem cond_lt_true (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m < n) :
    (Cond.lt e f).evalB B σ = some true := by
  rw [evalB_condLt he hf]; simp [h]

theorem cond_lt_false (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : ¬ m < n) :
    (Cond.lt e f).evalB B σ = some false := by
  rw [evalB_condLt he hf]; simp [h]

/-! #### Running a command -/

theorem skip (B : ℕ) (σ : Env) : Run B .skip σ σ 1 := Run.skip

theorem assign (B : ℕ) (σ : Env) (x : String) (e : Expr) (v : ℕ)
    (h : e.evalB B σ = some v) :
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size) := Run.assign h

theorem store (B : ℕ) (σ : Env) (a : String) (i e : Expr) (idx v : ℕ)
    (hi : i.evalB B σ = some idx) (he : e.evalB B σ = some v)
    (hidx : idx < (σ.arrs a).length) :
    Run B (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size) := Run.store hi he hidx

theorem seq (B : ℕ) (c d : Com) (σ σ' σ'' : Env) (K K' : ℕ)
    (h : Run B c σ σ' K) (h' : Run B d σ' σ'' K') :
    Run B (.seq c d) σ σ'' (K + K') := h.seq h'

theorem ite_true (B : ℕ) (b : Cond) (c d : Com) (σ σ' : Env) (K : ℕ)
    (hb : b.evalB B σ = some true) (h : Run B c σ σ' K) :
    Run B (.ite b c d) σ σ' (1 + b.size + K) := Run.ite_true hb h

theorem ite_false (B : ℕ) (b : Cond) (c d : Com) (σ σ' : Env) (K : ℕ)
    (hb : b.evalB B σ = some false) (h : Run B d σ σ' K) :
    Run B (.ite b c d) σ σ' (1 + b.size + K) := Run.ite_false hb h

theorem mono (B : ℕ) (c : Com) (σ σ' : Env) (K K' : ℕ)
    (h : Run B c σ σ' K) (hK : K ≤ K') : Run B c σ σ' K' := h.mono hK

/-- Using a specification the caller handed the walk. `Spec.run` with
its arguments explicit, so that a sub-program the walk must not unfold —
a loop, or a phase already proved — enters as an opaque step. -/
theorem use (B : ℕ) (P : Env → Prop) (c : Com) (Q : Env → Env → Prop) (K : ℕ)
    (h : Spec B P c Q K) (σ : Env) (hσ : P σ) : ∃ σ', Run B c σ σ' K ∧ Q σ σ' := h σ hσ

end RunStep

/-! ### The walk -/

section Meta

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace RunVCG

/-- What the walk carries: the value bound, the specifications it may
step over, and the obligations it could not close on the spot. -/
structure Cfg where
  /-- The value bound `B` of the goal. -/
  B : Lean.Expr
  /-- Deferred `_ < B` (and array-range) obligations, in walk order. -/
  side : IO.Ref (Array MVarId)
  /-- Specifications the caller supplied, tried at every command before
  its syntax is looked at. -/
  specs : Array Lean.Expr := #[]

/-- Close a goal with the standard discharger, reporting whether it
worked and leaving the state untouched when it did not. -/
def tryClose (g : MVarId) (stx : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← Lean.Elab.Tactic.run g (evalTactic stx)
    if gs.isEmpty then return true else s.restore; return false
  catch _ =>
    s.restore
    return false

/-- The discharger for a value-bound obligation: the precondition
verbatim, or the precondition after the environment chain is collapsed. -/
def sideTac : TacticM (TSyntax `tactic) := `(tactic| first | omega | (simp <;> omega))

/-- The discharger for the one arithmetic goal the walk creates itself,
`accumulated cost ≤ announced cost`, on concrete syntax. -/
def costTac : TacticM (TSyntax `tactic) := `(tactic| first | simp | (simp <;> omega) | omega)

/-- A value-bound obligation: tried at once, deferred if it does not go. -/
def mkSide (cfg : Cfg) (mv : MVarId) (ty : Lean.Expr) : TacticM Lean.Expr := mv.withContext do
  let m ← mkFreshExprSyntheticOpaqueMVar ty
  unless ← tryClose m.mvarId! (← sideTac) do
    cfg.side.modify (·.push m.mvarId!)
  return m

/-- One link of the `have` chain: assert `val` under its own type, and
hand back the hypothesis together with the goal that follows it. -/
def mkHave (mv : MVarId) (n : Name) (val : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × MVarId) := mv.withContext do
  let ty ← instantiateMVars (← inferType val)
  let mv₁ ← mv.assert n ty val
  let (f, mv₂) ← mv₁.intro1P
  return (mkFVar f, ty, mv₂)

/-- Drop a run hypothesis that has been folded into a larger one. The
context a user is handed then holds one `Run`, not the twelve the walk
went through. -/
def dropRun (mv : MVarId) (h : Lean.Expr) : MetaM MVarId := do
  if let .fvar f := h then
    try mv.clear f catch _ => return mv
  else return mv

private def natLt (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``LT.lt #[a, b]

/-- The value of a concrete expression, with a proof that it evaluates
to it. Every `_ < B` the evaluation needs becomes a side obligation. -/
partial def evalE (cfg : Cfg) (mv : MVarId) (σ e : Lean.Expr) :
    TacticM (Lean.Expr × Lean.Expr) := mv.withContext do
  let e ← withReducible <| whnf e
  match e.getAppFnArgs with
  | (``Lax13Proofs.Imp.Expr.lit, #[n]) =>
      let h ← mkSide cfg mv (← natLt n cfg.B)
      return (n, mkAppN (mkConst ``RunStep.eval_lit) #[cfg.B, n, σ, h])
  | (``Lax13Proofs.Imp.Expr.var, #[x]) =>
      let v := mkApp2 (mkConst ``Lax13Proofs.Imp.Env.vars) σ x
      let h ← mkSide cfg mv (← natLt v cfg.B)
      return (v, mkAppN (mkConst ``RunStep.eval_var) #[cfg.B, σ, x, h])
  | (``Lax13Proofs.Imp.Expr.get, #[a, i]) =>
      let (k, hi) ← evalE cfg mv σ i
      let arr := mkApp2 (mkConst ``Lax13Proofs.Imp.Env.arrs) σ a
      let len ← mkAppM ``List.length #[arr]
      let hk ← mkSide cfg mv (← natLt k len)
      let v ← mkAppM ``List.getD #[arr, k, mkNatLit 0]
      let h ← mkSide cfg mv (← natLt v cfg.B)
      return (v, mkAppN (mkConst ``RunStep.eval_get) #[cfg.B, σ, a, i, k, hi, hk, h])
  | (``Lax13Proofs.Imp.Expr.bin, #[op, e₁, e₂]) =>
      let (m, h₁) ← evalE cfg mv σ e₁
      let (n, h₂) ← evalE cfg mv σ e₂
      let op ← withReducible <| whnf op
      let (rule, v) ← match op.getAppFnArgs with
        | (``Lax13Proofs.Imp.Bop.add, _) => pure (``RunStep.eval_add, ← mkAppM ``HAdd.hAdd #[m, n])
        | (``Lax13Proofs.Imp.Bop.sub, _) => pure (``RunStep.eval_sub, ← mkAppM ``HSub.hSub #[m, n])
        | (``Lax13Proofs.Imp.Bop.mul, _) => pure (``RunStep.eval_mul, ← mkAppM ``HMul.hMul #[m, n])
        | (``Lax13Proofs.Imp.Bop.div, _) => pure (``RunStep.eval_div, ← mkAppM ``HDiv.hDiv #[m, n])
        | (``Lax13Proofs.Imp.Bop.and, _) => pure (``RunStep.eval_and, ← mkAppM ``Nat.land #[m, n])
        | (``Lax13Proofs.Imp.Bop.or, _) => pure (``RunStep.eval_or, ← mkAppM ``Nat.lor #[m, n])
        | (``Lax13Proofs.Imp.Bop.xor, _) => pure (``RunStep.eval_xor, ← mkAppM ``Nat.xor #[m, n])
        | (``Lax13Proofs.Imp.Bop.shiftl, _) =>
            pure (``RunStep.eval_shiftl, ← mkAppM ``HMul.hMul #[m, ← mkAppM ``HPow.hPow #[mkNatLit 2, n]])
        | (``Lax13Proofs.Imp.Bop.shiftr, _) =>
            pure (``RunStep.eval_shiftr, ← mkAppM ``HDiv.hDiv #[m, ← mkAppM ``HPow.hPow #[mkNatLit 2, n]])
        | _ => throwError "run_vcg: unrecognized operator {op}"
      let h ← mkSide cfg mv (← natLt v cfg.B)
      return (v, mkAppN (mkConst rule) #[cfg.B, σ, e₁, e₂, m, n, h₁, h₂, h])
  | _ => throwError "run_vcg: cannot evaluate the expression {e}"

/-- The final environment and the cost of a `Run B c σ σ' K`. -/
private def runParts (ty : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  match ty.getAppFnArgs with
  | (``Run, #[_, _, _, σ', K]) => return (σ', K)
  | _ => throwError "run_vcg: not a Run judgment: {ty}"

mutual

/-- If one of the supplied specifications is about this command, use it:
its precondition becomes an obligation, its postcondition a hypothesis,
and the walk resumes in the state it left. -/
partial def useSpec (cfg : Cfg) (mv : MVarId) (c σ : Lean.Expr)
    (kont : MVarId → Lean.Expr → Lean.Expr → Lean.Expr → TacticM (List MVarId)) :
    TacticM (Option (List MVarId)) := mv.withContext do
  for h in cfg.specs do
    let ty ← instantiateMVars (← inferType h)
    let (``Spec, #[Bs, P, cs, Q, Ks]) := ty.getAppFnArgs | continue
    unless ← isDefEq Bs cfg.B do continue
    unless ← isDefEq cs c do continue
    let hP ← mkFreshExprSyntheticOpaqueMVar (← whnfR (mkApp P σ))
    cfg.side.modify (·.push hP.mvarId!)
    let use := mkAppN (mkConst ``RunStep.use) #[Bs, P, cs, Q, Ks, h, σ, hP]
    let (hex, _, mv) ← mkHave mv `hspec use
    let .fvar hexF := hex | throwError "run_vcg: internal error"
    let #[s₁] ← mv.cases hexF | throwError "run_vcg: cannot open {ty}"
    let #[σ', .fvar hAnd] := s₁.fields | throwError "run_vcg: cannot open {ty}"
    let #[s₂] ← s₁.mvarId.cases hAnd | throwError "run_vcg: cannot open {ty}"
    let #[hrun, _] := s₂.fields | throwError "run_vcg: cannot open {ty}"
    return some (← kont s₂.mvarId σ' Ks hrun)
  return none

/-- Walk `c` from `σ`, and hand the continuation the goal it is left
with, the environment the command ends in, the cost it accumulated, and
the hypothesis carrying the derivation. An `ite` calls the continuation
once per branch; the goals of all branches are concatenated. -/
partial def exec (cfg : Cfg) (mv : MVarId) (c σ : Lean.Expr)
    (kont : MVarId → Lean.Expr → Lean.Expr → Lean.Expr → TacticM (List MVarId)) :
    TacticM (List MVarId) := do
  -- A supplied specification wins over the syntax: that is how a loop, or
  -- a phase already proved, is stepped over instead of unfolded.
  if let some r ← useSpec cfg mv c σ kont then return r
  let c ← mv.withContext <| whnf c
  match c.getAppFnArgs with
  | (``Lax13Proofs.Imp.Com.skip, _) =>
      let val := mkAppN (mkConst ``RunStep.skip) #[cfg.B, σ]
      let (h, ty, mv) ← mkHave mv `hrun val
      let (σ', K) ← runParts ty
      kont mv σ' K h
  | (``Lax13Proofs.Imp.Com.assign, #[x, e]) =>
      let (v, he) ← evalE cfg mv σ e
      let val := mkAppN (mkConst ``RunStep.assign) #[cfg.B, σ, x, e, v, he]
      let (h, ty, mv) ← mkHave mv `hrun val
      let (σ', K) ← runParts ty
      kont mv σ' K h
  | (``Lax13Proofs.Imp.Com.store, #[a, i, e]) =>
      let (idx, hi) ← evalE cfg mv σ i
      let (v, he) ← evalE cfg mv σ e
      let arr := mkApp2 (mkConst ``Lax13Proofs.Imp.Env.arrs) σ a
      let len ← mv.withContext <| mkAppM ``List.length #[arr]
      let hidx ← mkSide cfg mv (← mv.withContext <| natLt idx len)
      let val := mkAppN (mkConst ``RunStep.store) #[cfg.B, σ, a, i, e, idx, v, hi, he, hidx]
      let (h, ty, mv) ← mkHave mv `hrun val
      let (σ', K) ← runParts ty
      kont mv σ' K h
  | (``Lax13Proofs.Imp.Com.seq, #[c₁, c₂]) =>
      exec cfg mv c₁ σ fun mv₁ σ₁ K₁ h₁ =>
        exec cfg mv₁ c₂ σ₁ fun mv₂ σ₂ K₂ h₂ => do
          let val := mkAppN (mkConst ``RunStep.seq) #[cfg.B, c₁, c₂, σ, σ₁, σ₂, K₁, K₂, h₁, h₂]
          let (h, ty, mv₃) ← mkHave mv₂ `hrun val
          let mv₃ ← dropRun mv₃ h₁
          let mv₃ ← dropRun mv₃ h₂
          let (σ', K) ← runParts ty
          kont mv₃ σ' K h
  | (``Lax13Proofs.Imp.Com.ite, #[b, c₁, c₂]) =>
      let bw ← mv.withContext <| whnf b
      let (e₁, e₂, trueRule, falseRule, isEq) ← match bw.getAppFnArgs with
        | (``Lax13Proofs.Imp.Cond.eq, #[e₁, e₂]) =>
            pure (e₁, e₂, ``RunStep.cond_eq_true, ``RunStep.cond_eq_false, true)
        | (``Lax13Proofs.Imp.Cond.lt, #[e₁, e₂]) =>
            pure (e₁, e₂, ``RunStep.cond_lt_true, ``RunStep.cond_lt_false, false)
        | _ => throwError "run_vcg: cannot evaluate the condition {b}"
      let (m, h₁) ← evalE cfg mv σ e₁
      let (n, h₂) ← evalE cfg mv σ e₂
      let p := if isEq then
          mkAppN (mkConst ``Eq [Level.one]) #[mkConst ``Nat, m, n]
        else
          mkAppN (mkConst ``LT.lt [Level.zero]) #[mkConst ``Nat, mkConst ``instLTNat, m, n]
      let (sT, sF) ← mv.byCases p (← mkFreshUserName `hcase)
      let branch (sB : ByCasesSubgoal) (rule : Name) (body : Lean.Expr) (pos : Bool) := do
        let mvB := sB.mvarId
        let hc := mkFVar sB.fvarId
        let hb := mkAppN (mkConst rule) #[cfg.B, σ, e₁, e₂, m, n, h₁, h₂, hc]
        exec cfg mvB body σ fun mv' σ' K' h' => do
          let rule' := if pos then ``RunStep.ite_true else ``RunStep.ite_false
          let val := mkAppN (mkConst rule') #[cfg.B, b, c₁, c₂, σ, σ', K', hb, h']
          let (h, ty, mv'') ← mkHave mv' `hrun val
          let mv'' ← dropRun mv'' h'
          let (σ'', K) ← runParts ty
          kont mv'' σ'' K h
      let gsT ← branch sT trueRule c₁ true
      let gsF ← branch sF falseRule c₂ false
      return gsT ++ gsF
  | _ =>
      throwError "run_vcg: no rule for {c}\n\
        (a loop or a tape operation is stepped over by handing run_vcg a Spec \
        for it: `run_vcg [my_loop_spec]`)"

end

/-! ### Recognizing the goal

Two shapes are accepted. `Spec B P c Q K` is the interface of `Spec.lean`
and is what a new phase lemma is stated in; the walk introduces the
initial state and takes the precondition apart, so that its conjuncts are
in scope for the value-bound obligations. `∃ σ' K', Run B c σ σ' K' ∧
K' ≤ K ∧ Q σ σ'` is the shape every phase lemma written before `Spec.lean`
has, and is accepted so that the tactic can be pointed at one without
restating it. -/

/-- Take a conjunctive precondition apart, so `omega` can see its parts.
Stops at anything that is not an `And`. -/
partial def splitAnds (mv : MVarId) (f : FVarId) : MetaM MVarId := do
  let old ← mv.withContext f.getType
  let ty ← mv.withContext do whnfR old
  match ty.and? with
  | some _ =>
      -- `cases` reduces the type itself, and it renumbers the hypotheses it
      -- reverts, so the decl must not be rewritten first.
      match ← mv.cases f with
      | #[s] =>
          match s.fields with
          | #[.fvar f₁, .fvar f₂] => splitAnds (← splitAnds s.mvarId f₁) f₂
          | _ => return s.mvarId
      | _ => return mv
  | none =>
      -- A precondition that is not a conjunction is still an application of
      -- the predicate; `omega` wants it beta-reduced.
      if ty == old then return mv else mv.changeLocalDecl f ty

/-- The goal shapes the walk closes. -/
inductive Shape
  /-- `∃ σ', Run B c σ σ' K ∧ Q σ σ'`, what `Spec` unfolds to. -/
  | spec
  /-- `∃ σ' K', Run B c σ σ' K' ∧ K' ≤ K ∧ Q σ σ'`, the legacy shape. -/
  | legacy

end RunVCG

open RunVCG in
/-- **Symbolically execute a concrete block of IMP+.**

The goal is a `Spec B P c Q K` — or the existential shape phase lemmas
had before `Spec` — whose command `c` is built from `skip`, `assign`,
`store`, `seq` and `ite`. `run_vcg` runs it: it introduces the initial
state, takes the precondition apart, applies the rule of every construct
in turn as a `have`, splits every conditional on its test, and discharges
the announced cost bound.

What is left is one goal per control-flow path — the postcondition, in
the environment that path ends in, with the path's case hypotheses in
scope — followed by the value-bound obligations `omega` could not read
straight off the precondition. `simp_all` and `omega` are what close
them; `run_vcg <;> simp_all <;> omega` is the whole proof of a block
whose postcondition is a case analysis.

`run_vcg [h₁, h₂]` walks around the commands `h₁` and `h₂` specify
instead of into them. That is how a `while` — whose invariant and
potential are content, not bookkeeping — and a phase already proved
enter a block: each becomes one step, owing its precondition and giving
back its postcondition. -/
syntax (name := runVcg) "run_vcg" (" [" term,* "]")? : tactic

open RunVCG in
@[tactic runVcg] def evalRunVcg : Tactic := fun stx => do
  let side ← IO.mkRef (#[] : Array MVarId)
  let mv ← getMainGoal
  let specs ← mv.withContext do
    match stx with
    | `(tactic| run_vcg [$ts,*]) => ts.getElems.mapM fun t => elabTerm t none
    | _ => pure #[]
  -- `Spec B P c Q K` is a definition; unfold it and introduce.
  let mv ← mv.withContext do
    let t ← instantiateMVars (← mv.getType)
    if t.isAppOf ``Spec then
      let t' ← withTransparency .default (whnf t)
      let mv ← mv.change t'
      let (_, mv) ← mv.intro1P
      let (f, mv) ← mv.intro1P
      splitAnds mv f
    else pure mv
  let target ← mv.withContext do instantiateMVars (← mv.getType)
  -- Read `B`, `c`, `σ` and the announced cost off the target.
  let some (envTy, p) := target.app2? ``Exists
    | throwError "run_vcg: the goal is not an existential over the final state:\n{target}"
  let (shape, B, c, σ, K) ← lambdaTelescope p fun xs body => do
    unless xs.size == 1 do throwError "run_vcg: unexpected goal shape"
    match body.and? with
    | some (runTy, _) =>
        match runTy.getAppFnArgs with
        | (``Run, #[B, c, σ, _, K]) => pure (Shape.spec, B, c, σ, K)
        | _ => throwError "run_vcg: the goal does not begin with a Run judgment:\n{body}"
    | none =>
        match body.app2? ``Exists with
        | some (_, q) =>
            lambdaTelescope q fun _ body' => do
              match body'.and? with
              | some (runTy, rest) =>
                  match runTy.getAppFnArgs, rest.and? with
                  | (``Run, #[B, c, σ, _, _]), some (le, _) =>
                      match le.getAppFnArgs with
                      | (``LE.le, #[_, _, _, K]) => pure (Shape.legacy, B, c, σ, K)
                      | _ => throwError "run_vcg: no cost bound in\n{body'}"
                  | _, _ => throwError "run_vcg: unexpected goal shape:\n{body'}"
              | none => throwError "run_vcg: unexpected goal shape:\n{body'}"
        | none => throwError "run_vcg: unexpected goal shape:\n{body}"
  let cfg : Cfg := { B := B, side := side, specs := specs }
  let main ← exec cfg mv c σ fun mv' σf Kf hrun => mv'.withContext do
    let leTy ← mkAppM ``LE.le #[Kf, K]
    let leM ← mkFreshExprSyntheticOpaqueMVar leTy
    let runTerm := mkAppN (mkConst ``RunStep.mono) #[B, c, σ, σf, Kf, K, hrun, leM]
    unless ← tryClose leM.mvarId! (← costTac) do
      throwError "run_vcg: cannot prove the cost bound {leTy}"
    match shape with
    | .spec =>
        let pApp ← whnfR (mkApp p σf)
        let some (runGoal, qTy) := pApp.and?
          | throwError "run_vcg: unexpected goal shape:\n{pApp}"
        let qM ← mkFreshExprSyntheticOpaqueMVar (← whnfR qTy)
        let andTerm := mkAppN (mkConst ``And.intro) #[runGoal, qTy, runTerm, qM]
        mv'.assign (mkAppN (mkConst ``Exists.intro [Level.one]) #[envTy, p, σf, andTerm])
        let qG ← dropRun qM.mvarId! hrun
        return [qG]
    | .legacy =>
        let pApp ← whnfR (mkApp p σf)
        let some (_, q) := pApp.app2? ``Exists
          | throwError "run_vcg: unexpected goal shape:\n{pApp}"
        let inner ← whnfR (mkApp q Kf)
        let some (runGoal, rest) := inner.and?
          | throwError "run_vcg: unexpected goal shape:\n{inner}"
        let some (leGoal, qTy) := rest.and?
          | throwError "run_vcg: unexpected goal shape:\n{rest}"
        let leM' ← mkFreshExprSyntheticOpaqueMVar leGoal
        unless ← tryClose leM'.mvarId! (← costTac) do
          throwError "run_vcg: cannot prove the cost bound {leGoal}"
        let qM ← mkFreshExprSyntheticOpaqueMVar (← whnfR qTy)
        let hrun' ← do
          if ← isDefEq (← inferType hrun) runGoal then pure hrun else pure runTerm
        let restTerm := mkAppN (mkConst ``And.intro) #[leGoal, qTy, leM', qM]
        let andTerm := mkAppN (mkConst ``And.intro) #[runGoal, rest, hrun', restTerm]
        mv'.assign (mkAppN (mkConst ``Exists.intro [Level.one]) #[envTy, p, σf,
          mkAppN (mkConst ``Exists.intro [Level.one]) #[mkConst ``Nat, q, Kf, andTerm]])
        let qG ← dropRun qM.mvarId! hrun
        return [qG]
  replaceMainGoal (main ++ (← side.get).toList)

end Meta

/-! ### Worked examples

Small kit-local programs, so that the kit documents its own tactic. Each
is the whole proof: the tactic, and one combinator for what it leaves. -/

namespace Example

open Lax13Proofs.Imp

/-- An assignment: one goal, the postcondition in the updated
environment. -/
example (B : ℕ) : Spec B (fun ρ => ρ.vars "x" + 1 < B) (.assign "y" (.add (.var "x") (.lit 1)))
    (fun ρ ρ' => ρ'.vars "y" = ρ.vars "x" + 1) 4 := by
  run_vcg; simp

/-- A sequence: the walk threads the environment, and the cost of the
block is checked against the announced bound. -/
example (B : ℕ) : Spec B (fun ρ => ρ.vars "x" + 1 < B)
    (.seq (.assign "y" (.add (.var "x") (.lit 1))) (.assign "z" (.var "y")))
    (fun ρ ρ' => ρ'.vars "z" = ρ.vars "x" + 1) 6 := by
  run_vcg; simp

/-- A conditional: two goals, each with its branch's test in scope. -/
example (B : ℕ) (h : 1 < B) :
    Spec B (fun ρ => ρ.vars "x" < B ∧ ρ.vars "y" < B)
      (.ite (.lt (.var "x") (.var "y")) (.assign "m" (.lit 1)) (.assign "m" (.lit 0)))
      (fun ρ ρ' => (ρ'.vars "m" = 1 ↔ ρ.vars "x" < ρ.vars "y")) 7 := by
  run_vcg <;> simp_all

/-- A store: the range condition joins the value bounds as an
obligation. -/
example (B : ℕ) (h : 1 < B) :
    Spec B (fun ρ => ρ.vars "i" < B ∧ ρ.vars "i" < (ρ.arrs "a").length)
      (.store "a" (.var "i") (.lit 1))
      (fun ρ ρ' => ρ'.arrs "a" = (ρ.arrs "a").set (ρ.vars "i") 1) 4 := by
  run_vcg; simp

/-- Nested conditionals over a block that assigns in one leaf only —
the shape of a phase lemma, at kit scale. Four paths, four goals. -/
example (B : ℕ) (h : 1 < B) :
    Spec B (fun ρ => ρ.vars "c" < B ∧ ρ.vars "u" < B ∧ ρ.vars "w" < B ∧ ρ.vars "n" + 1 < B)
      (.ite (.eq (.var "c") (.lit 0))
        (.ite (.lt (.var "u") (.var "w"))
          (.seq (.assign "n" (.add (.var "n") (.lit 1))) (.assign "c" (.lit 1)))
          .skip)
        .skip)
      (fun ρ ρ' => (ρ.vars "c" = 0 ∧ ρ.vars "u" < ρ.vars "w" ∧ ρ'.vars "n" = ρ.vars "n" + 1) ∨
        ρ'.vars "n" = ρ.vars "n") 20 := by
  run_vcg <;> simp_all

/-! A sub-program the walk must not unfold — a loop, or a phase already
proved — enters as one step, by handing `run_vcg` its specification. The
precondition of the specification becomes an obligation and its
postcondition a hypothesis; the walk resumes in the state it leaves. -/

/-- A one-command sub-program, standing in for a phase. -/
def bump : Com := .assign "n" (.add (.var "n") (.lit 1))

/-- Its specification, itself proved by the walk. -/
theorem bump_spec (B : ℕ) :
    Spec B (fun ρ => ρ.vars "n" + 1 < B) bump
      (fun ρ ρ' => ρ'.vars "n" = ρ.vars "n" + 1) 4 := by
  run_vcg; simp

example (B : ℕ) :
    Spec B (fun ρ => ρ.vars "n" + 2 < B) (.seq bump bump)
      (fun ρ ρ' => ρ'.vars "n" = ρ.vars "n" + 2) 8 := by
  run_vcg [bump_spec B] <;> omega

/-- The same mechanism is what a `while` uses: `Spec.while_potential`,
`Spec.while_count` or `Spec.forRange` proves the loop, and the block it
sits in is walked around it. -/
example (B : ℕ) (loop : Com)
    (hloop : Spec B (fun ρ => ρ.vars "n" < B) loop (fun _ ρ' => ρ'.vars "n" = 0) 100) :
    Spec B (fun ρ => ρ.vars "n" < B ∧ 1 < B) (.seq loop (.assign "d" (.lit 1)))
      (fun _ ρ' => ρ'.vars "n" = 0 ∧ ρ'.vars "d" = 1) 102 := by
  run_vcg [hloop] <;> simp_all

end Example

end Lax13Proofs.Reasoning
