import Lax13Proofs.Refine.Autoref.FixRel
import Lax13Proofs.Refine.Autoref.Solver

/-!
Phase four: syntax-directed translation (`trans`, priority 30).

Port of `thys/Automatic_Refinement/Tool/Autoref_Translate.thy` of AFP
`Automatic_Refinement` (Lammich) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 — AFP for Isabelle2025-2,
release 2026-02-06. The verbatim source text this file is checked
against is `plans/word-ram/refinement-tower/p2-tool-extracts.md` §4
(§4.1 the default translation rules, §4.2 the side-condition tags and
their solvers, §4.3 `autoref_post_simps` and the phase).

The phase's job, in the extract's own summary:

> `trans` (`Autoref_Translate.trans_phase`) enters with every relator
> fixed and rewrites `(?f,a')∈R` by repeatedly resolving against the
> now-instantiated rule set plus `dflt_trans_rules`
> (`autoref_APP`/`autoref_ABS`/`autoref_beta`), discharging each rule's
> `PREFER`/`DEFER`-tagged side-condition through `Tagged_Solver`
> (`SIDE_PRECOND`, `GEN_ALGO`, `STRUCT_EQ`) as each subterm is
> translated, and leaves `?f` fully instantiated.

## The source, verbatim

§4.1:

```isabelle
lemma autoref_ABS:
  "⟦ ⋀x x'. (x,x')∈Ra ⟹ (c x, a x')∈Rr ⟧ ⟹ (c, λ'x. a x)∈Ra→Rr"
lemma autoref_APP:
  "⟦ (c,a)∈Ra→Rr; (x,x')∈Ra ⟧ ⟹ (c$x, a $ x')∈Rr"
lemma autoref_beta:
  assumes "(c,a x)∈R"  shows "(c,(λ'x. a x)$x)∈R"

lemmas dflt_trans_rules = autoref_beta autoref_ABS autoref_APP
```

§4.2, with the source's own explanation of the two side-condition
kinds:

> Rules can have prefer and defer side-conditions. Prefer conditions
> must be solvable in order for the rule to apply, and defer conditions
> must hold after the rule has been applied and the recursive
> translations have been performed. Thus, prefer-conditions typically
> restrict on the abstract expression, while defer conditions restrict
> the translated expression. In order to solve the actual side
> conditions, we use the `Tagged_Solver`-infrastructure. The solvers are
> applied after the `PREFER`/`DEFER` tag has been removed.

and

> Tag to remove internal stuff from term. Before a prefer/defer side
> condition is evaluated, all terms inside these tags are purged from
> autoref-specific annotations, i.e., operator-annotations, relator
> annotations, and tagged applications.

```isabelle
definition [simp, autoref_tag_defs]: "REMOVE_INTERNAL x ≡ x"

abbreviation "PREFER nt Φ ≡ PREFER_tag (nt (REMOVE_INTERNAL Φ))"
abbreviation "DEFER nt Φ ≡ DEFER_tag (nt (REMOVE_INTERNAL Φ))"

definition [simp]: "REMOVE_INTERNAL_EQ a b ≡ a=b"
lemma REMOVE_INTERNAL_EQI: "REMOVE_INTERNAL_EQ a a" by simp

lemma autoref_REMOVE_INTERNAL_EQ:
  assumes "(c,a)∈R"  assumes "REMOVE_INTERNAL_EQ c c'"  shows "(c',a)∈R"

definition [simp, autoref_tag_defs]: "PRECOND_tag P ≡ P"
lemma PRECOND_tagI: "P ⟹ PRECOND_tag P" by simp
abbreviation "SIDE_PRECOND P ≡ PREFER PRECOND_tag P"

declaration ‹
  Tagged_Solver.declare_solver @{thms PRECOND_tagI} @{binding PRECOND}
    "Refinement: Solve preconditions"
    ( fn ctxt => SOLVED' ( SELECT_GOAL (auto_tac ctxt) ) )
›

definition [simp, autoref_tag_defs]: "PRECOND_OPT_tag P ≡ P"
lemma PRECOND_OPT_tagI: "P ⟹ PRECOND_OPT_tag P" by simp
abbreviation "SIDE_PRECOND_OPT P ≡ PREFER PRECOND_OPT_tag P"
declaration ‹
  Tagged_Solver.declare_solver @{thms PRECOND_OPT_tagI} @{binding PRECOND_OPT}
    "Refinement: Solve optional preconditions"
    ( fn ctxt => SOLVED' (asm_full_simp_tac ctxt))
›
```

§4.3, the phase (ML elided by the extraction, structural description
quoted):

> The phase's rule net (`trans_netD`) is `thm_pairsD` (now with every
> relator fixed by `fix_rel`) plus the fixed `dflt_trans_rules`.
> `trans_step_tac` handles one goal: if it's a `DEFER_tag` conclusion,
> solve it now via `side_tac` (`SIDEI` intro, strip internal tags via
> `REMOVE_INTERNAL_conv`, then `Tagged_Solver.solve_tac` […]);
> otherwise resolve from the `trans_net` and, if the newly introduced
> subgoal is `PREFER_tag`-marked, immediately try to solve it too
> (prefer-conditions gate whether the rule was even applicable;
> defer-conditions are checked only after recursive translation of the
> rest of the term completes). `trans_tac` wraps this in a
> `REMOVE_INTERNAL_EQ`-based post-pass that, once all steps succeed,
> simplifies with `APP_def`/`PROTECT_def`/`ANNOT_def` and the
> `autoref_post_simps` set to strip the remaining tagging machinery from
> the synthesized concrete term.

```isabelle
val trans_phase = {
  init = trans_netD.init,
  tac = trans_tac,
  analyze = trans_analyze,
  pretty_failure = trans_pretty_failure }
```

## Substrate deltas and departures, each flagged

**T1 — resolution is `MVarId.apply` over the same net, with explicit
backtracking.** The source's `trans_step_tac` resolves against a
`Item_Net` of rules; here `transResolve` walks `fix_rel`'s
priority-sorted rule list and `apply`s each in turn, restoring the
metavariable context on failure. The `PREFER` gate is inside the
backtracking, exactly as the source describes it ("prefer-conditions
gate whether the rule was even applicable"): a rule whose prefer
condition fails is *rejected*, and the next rule is tried. Which rules
were rejected that way, and why, is what the failure message reports —
the plan's supervision-legibility requirement lands here (delta P6 of
`Autoref/Phases.lean`).

**T2 — no rule needs a tagged conclusion.** In Isabelle,
`(append,append)∈…` cannot resolve against a goal whose abstract side is
`ANNOT (OP append) (rel_annot R)` unless the framework normalises one to
the other, because HOL resolution does not unfold definitions. In Lean
the four tags are ordinary `def`s and `isDefEq` unfolds them, so a rule
stated on the bare operator applies to a tagged goal directly, and a
rule stated on the tagged operator (`autoref_hd`'s
`(OP hd ::: ⟨R⟩list_rel → R)$l'`) applies to the same goal just as
directly. Both spellings are therefore supported with no preprocessing
pass; the tags still do their real work, which is telling the *phases'*
structural walks where the operators are.

**T3 — `autoref_post_simps` is absent.** Its attribute is not
registered (wave B2's `Autoref/Attrs.lean` is frozen; the database is a
"bonus" row of the extract's §9 table). The post-pass therefore runs
with `autoref_tag_defs` alone — `PROTECT_def`, `ANNOT_def`, `OP_def`,
`APP_def`, which is what the source names explicitly — and a consumer
wanting to post-simplify a synthesized term does it by hand. The
post-pass itself is the source's, `autoref_REMOVE_INTERNAL_EQ` and all:
the phase resolves the goal against it *before* translating, so that the
clean term lands in the caller's own `?c` metavariable rather than
being reconstructed afterwards.

**T4 — the `PRECOND` solver is `simp`-then-`omega`-then-`decide`, not
`auto`.** The source's is `SOLVED' (SELECT_GOAL (auto_tac))` and
`PRECOND_OPT`'s is `SOLVED' (asm_full_simp_tac)`. Lean has no `auto`;
the closest honest reading of "the classical reasoner plus the
simplifier plus the assumptions" at spine scope is the cascade below,
and `PRECOND_OPT` gets `simp_all`, which *is* `asm_full_simp_tac`. A
side condition the cascade cannot do is reported by name, with the
`tagged_solver` dispatch message wave B2 built for exactly this.

**T5 — `trans_dbg_step_tac` / `trans_step_only_tac` are folded into two
tactics.** The source exposes `autoref_trans_step`,
`autoref_trans_step_keep` and `autoref_trans_step_only` (extract §7.4);
here there are `autoref_trans_step` (one step, side conditions solved)
and `autoref_trans` (to completion), the two the `GEN_OP` solver and
interactive debugging actually need. `autoref_side` is the source's
method of the same name.

**T9 — rule selection dispatches on the goal's abstract shape.** Delta
T2's convenience — Lean unfolds the tags, so an untagged rule resolves
against a tagged goal — has a flip side: it also lets a rule resolve
against a goal it was never meant for. `autoref_APP`'s conclusion
`(c$x, a$x')∈Rr` unfolds to an ordinary application, so it matches the
*operator* goal `(?c, OP (@List.append ℕ) ::: R) ∈ R` by taking
`@List.append ℕ` apart into `List.append` applied to `ℕ`; and wave B1's
`autoref_nat_lit : (n, n) ∈ natRel`, whose abstract side is a bare
variable (its delta PM7 collapsed the source's `numeral n` into it),
matches *any* `ℕ`-valued abstract side, applied or not. Isabelle is
immune to both because its resolution does not unfold `APP`/`OP`/`ANNOT`
at all. The port restores the distinction structurally: a goal whose
abstract side is an `$ᵃ` spine is offered only the rules whose own
conclusion is applied (plus `autoref_APP`, and `autoref_beta` under an
`ABS` head); a goal whose abstract side is a bare operator is offered
only the un-applied ones; `autoref_ABS` is offered only under an `ABS`.
`Rule.applied` (`Autoref/FixRel.lean`) is that classification, computed
once per rule.

**T8 — resolution is at the rule's stated arity, not `MVarId.apply`'s.**
Recorded at `applyRule` below, where it is load-bearing: `apply` unfolds
a rule's conclusion looking for a matching argument count, and a
refinement rule's conclusion unfolds all the way through `Set` membership
into a `∀`, so `apply` would resolve `(cons, cons) ∈ R →ᵣ ⟨R⟩list_rel →ᵣ
⟨R⟩list_rel` directly against `(?c, cons $ᵃ x $ᵃ y) ∈ ?R` — flattening
the spine and leaving `?R` open. `forallMetaTelescope` stops at the
rule's syntactic conclusion, which is the arity Isabelle's `resolve_tac`
uses.

**T7 — a rule's undetermined implicit arguments are skipped.** In
Isabelle a rule's schematic variables are simply left schematic and get
instantiated as the derivation proceeds; in Lean `MVarId.apply` hands
back *every* metavariable it could not determine, including the
non-`Prop` ones — for `autoref_hd`, the concrete list `l`, which is
fixed only when the `(l, l') ∈ ⟨R⟩list_rel` premise is translated.
`classify` sorts those out and the worklist ignores them; that they were
all assigned in the end is checked once, by `autoref_synth`, which
refuses a proof still containing a metavariable.

**T6 — the recursion is a worklist, and it is bounded.** The source
recurses through `Seq.INTERVAL`/`REPEAT_ON_SUBGOAL`; `transWork` below
is an explicit worklist over goals, function-before-argument so that
`autoref_APP`'s shared `?Ra` is fixed by the operator's rule before the
argument is translated. The step budget is a guard against a rule that
resolves against its own conclusion; the source's tacticals have the
same failure mode and no guard.
-/

open Lean Meta Elab

universe u

namespace Lax13Proofs.Refine

/-! ### Default translation rules (`Autoref_Translate.thy` §4.1) -/

/-- The source's `autoref_ABS`. -/
theorem autoref_ABS {γ γ' α β : Type} {Ra : Set (γ × α)} {Rr : Set (γ' × β)}
    {c : γ → γ'} {a : α → β} (h : ∀ x x', (x, x') ∈ Ra → (c x, a x') ∈ Rr) :
    (c, ABS a) ∈ Ra →ᵣ Rr := h

/-- The source's `autoref_APP`. -/
theorem autoref_APP {γ γ' α β : Type} {Ra : Set (γ × α)} {Rr : Set (γ' × β)}
    {c : γ → γ'} {a : α → β} {x : γ} {x' : α}
    (h : (c, a) ∈ Ra →ᵣ Rr) (hx : (x, x') ∈ Ra) : (c $ᵃ x, a $ᵃ x') ∈ Rr :=
  fun_relD h hx

/-- The source's `autoref_beta`. -/
theorem autoref_beta {γ α β : Type} {R : Set (γ × β)} {c : γ} {a : α → β} {x : α}
    (h : (c, a x) ∈ R) : (c, (ABS a) $ᵃ x) ∈ R := h

/-! ### Side conditions (`Autoref_Translate.thy` §4.2) -/

/-- The source's `REMOVE_INTERNAL x ≡ x`, its "Tag to remove internal
stuff from term": everything inside it is purged of autoref annotations
before a side condition is evaluated. -/
def REMOVE_INTERNAL {α : Sort u} (x : α) : α := x

/-- The source's `REMOVE_INTERNAL` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem REMOVE_INTERNAL_def {α : Sort u} (x : α) :
    REMOVE_INTERNAL x = x := rfl

/-- The source's `PREFER nt Φ ≡ PREFER_tag (nt (REMOVE_INTERNAL Φ))`:
the form a rule author writes. -/
abbrev PREFER (nt : Prop → Prop) (Φ : Prop) : Prop := PREFER_tag (nt (REMOVE_INTERNAL Φ))

/-- The source's `DEFER nt Φ ≡ DEFER_tag (nt (REMOVE_INTERNAL Φ))`. -/
abbrev DEFER (nt : Prop → Prop) (Φ : Prop) : Prop := DEFER_tag (nt (REMOVE_INTERNAL Φ))

/-- The source's `REMOVE_INTERNAL_EQ a b ≡ a=b`. -/
def REMOVE_INTERNAL_EQ {α : Sort u} (a b : α) : Prop := a = b

/-- The source's `REMOVE_INTERNAL_EQ` definition, with the source's own
`[simp]`. -/
@[simp] theorem REMOVE_INTERNAL_EQ_def {α : Sort u} (a b : α) :
    REMOVE_INTERNAL_EQ a b ↔ a = b := Iff.rfl

/-- The source's `REMOVE_INTERNAL_EQI`. -/
theorem REMOVE_INTERNAL_EQI {α : Sort u} (a : α) : REMOVE_INTERNAL_EQ a a := rfl

/-- The source's `autoref_REMOVE_INTERNAL_EQ`: the rule the phase's
post-pass runs on, by which the *clean* concrete term reaches the
caller's metavariable. -/
theorem autoref_REMOVE_INTERNAL_EQ {γ α : Type} {c c' : γ} {a : α} {R : Set (γ × α)}
    (h : (c, a) ∈ R) (heq : REMOVE_INTERNAL_EQ c c') : (c', a) ∈ R := by
  have : c = c' := heq
  rw [← this]; exact h

/-- The source's `PRECOND_tag P ≡ P`. -/
def PRECOND_tag (P : Prop) : Prop := P

/-- The source's `PRECOND_tag` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem PRECOND_tag_def (P : Prop) : PRECOND_tag P ↔ P := Iff.rfl

/-- The source's `PRECOND_tagI`. -/
theorem PRECOND_tagI {P : Prop} (h : P) : PRECOND_tag P := h

/-- The source's `SIDE_PRECOND P ≡ PREFER PRECOND_tag P`: the
side-condition form `autoref_hd` and its kin state. -/
abbrev SIDE_PRECOND (P : Prop) : Prop := PREFER PRECOND_tag P

/-- The source's `PRECOND_OPT_tag P ≡ P`. -/
def PRECOND_OPT_tag (P : Prop) : Prop := P

/-- The source's `PRECOND_OPT_tag` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem PRECOND_OPT_tag_def (P : Prop) :
    PRECOND_OPT_tag P ↔ P := Iff.rfl

/-- The source's `PRECOND_OPT_tagI`. -/
theorem PRECOND_OPT_tagI {P : Prop} (h : P) : PRECOND_OPT_tag P := h

/-- The source's `SIDE_PRECOND_OPT P ≡ PREFER PRECOND_OPT_tag P`. -/
abbrev SIDE_PRECOND_OPT (P : Prop) : Prop := PREFER PRECOND_OPT_tag P

section Solvers

-- A `declare_solver` body is stored, not run, so the tactic linters see
-- a block that never executes (wave B2's `Autoref/Solver.lean` gate has
-- the same two lines for the same reason).
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

-- The source's `PRECOND` solver, `Tagged_Solver.declare_solver
-- @{thms PRECOND_tagI} @{binding PRECOND} "Refinement: Solve
-- preconditions" (SOLVED' (SELECT_GOAL (auto_tac ctxt)))` — with the
-- `auto` cascade of delta T4.
declare_solver PRECOND for PRECOND_tag at 0 with "Refinement: Solve preconditions" :=
  simp only [PRECOND_tag_def, REMOVE_INTERNAL_def]
  try (first | assumption | simp | omega | decide)

-- The source's `PRECOND_OPT` solver, whose tactic is
-- `SOLVED' (asm_full_simp_tac ctxt)`.
declare_solver PRECOND_OPT for PRECOND_OPT_tag at 0
    with "Refinement: Solve optional preconditions" :=
  simp only [PRECOND_OPT_tag_def, REMOVE_INTERNAL_def]
  try simp_all

end Solvers

namespace Autoref

/-! ### Resolution at a rule's stated arity (delta T8) -/

/-- Match a rule's conclusion against a goal, component by component —
see `applyRule`. -/
def matchConcl (concl target : Expr) : MetaM Bool := do
  match parseRefine? concl, parseRefine? target with
  | some (c₁, a₁, R₁), some (c₂, a₂, R₂) =>
    -- Component-wise, abstract side first: it is the discriminating one,
    -- and unifying the memberships whole would unfold `Set` membership
    -- into the `∀` of `funRel` on both sides (delta T8).
    if !(← isDefEq a₁ a₂) then return false
    if !(← isDefEq R₁ R₂) then return false
    isDefEq c₁ c₂
  | _, _ => isDefEq concl target

/-- Resolve a goal against a rule, at the rule's *stated* arity.

`MVarId.apply` cannot be used here. A refinement rule's conclusion
`(f, f') ∈ A →ᵣ B` is `Set` membership, which unfolds to
`∀ a a', (a,a') ∈ A → (f a, f' a') ∈ B` — so `apply`, which chooses the
argument count by unfolding the conclusion until it matches, happily
resolves an *un-applied* rule against an *applied* goal, flattening the
`$ᵃ` spine the whole tagging discipline exists to preserve and leaving
the relator variables it should have fixed still open. `forallMetaTelescope`
stops at the rule's syntactic conclusion, which is exactly the arity the
source's `resolve_tac` uses, so this is resolution as the source has it
(delta T8). -/
def applyRule (proof type : Expr) (g : MVarId) : MetaM (List MVarId) := do
  let (mvars, bis, concl) ← forallMetaTelescope type
  let target ← instantiateMVars (← g.getType)
  unless ← matchConcl concl target do
    throwError "the rule's conclusion{indentExpr concl}\ndoes not match the \
      goal{indentExpr target}"
  for (m, bi) in mvars.zip bis do
    if bi.isInstImplicit then
      let mid := m.mvarId!
      unless ← mid.isAssigned do
        match ← trySynthInstance (← instantiateMVars (← mid.getType)) with
        | .some inst => unless ← isDefEq m inst do
            throwError "the rule's instance argument could not be synthesized"
        | _ => pure ()
  g.assign (mkAppN proof mvars)
  let mut gs : Array MVarId := #[]
  for m in mvars do
    let mid := m.mvarId!
    unless ← mid.isAssigned do gs := gs.push mid
  return gs.toList

/-- `applyRule` at a named global rule. -/
def applyConst (n : Name) (g : MVarId) : MetaM (List MVarId) := do
  let e ← mkConstWithFreshMVarLevels n
  applyRule e (← inferType e) g

/-! ### Side-condition solving (the source's `side_tac`) -/

/-- The source's `REMOVE_INTERNAL_conv`: purge autoref annotations from
everything inside a `REMOVE_INTERNAL` tag. The rewrite is definitional
(every tag is a `def` for the identity), so this is a `change`. -/
def removeInternalConv (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let ty' ← Meta.transform ty (post := fun e => do
    match e.getAppFnArgs with
    | (``REMOVE_INTERNAL, #[_, x]) =>
      return .done (← mkAppM ``REMOVE_INTERNAL #[← untag x])
    | _ => return .continue)
  if ty' == ty then return g else g.change ty'

/-- The source's `side_tac`: introduce through the `PREFER`/`DEFER` tag
(`SIDEI`), strip internal tags, then dispatch through
`Tagged_Solver` — wave B2's `tagged_solver`, whose own failure message
names the tag and every solver it considered. -/
def sideSolve (g : MVarId) : TermElabM Unit := do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let g ←
    match ty.getAppFn with
    | .const ``PREFER_tag _ => do
      let gs ← applyConst ``PREFER_tagI g
      match gs with
      | [g'] => pure g'
      | _ => throwError "side condition: PREFER_tagI did not leave one goal"
    | .const ``DEFER_tag _ => do
      let gs ← applyConst ``DEFER_tagI g
      match gs with
      | [g'] => pure g'
      | _ => throwError "side condition: DEFER_tagI did not leave one goal"
    | _ => pure g
  let g ← removeInternalConv g
  let rest ← Tactic.run g (Tactic.evalTactic (← `(tactic| tagged_solver)))
  unless rest.isEmpty do
    throwError "the side condition was not closed:{indentD (← rest.head!.getType)}"

/-! ### The translation step (the source's `trans_step_tac`) -/

/-- How a premise produced by a rule application is discharged. -/
inductive PremKind
  /-- A tag that holds of everything: close it by applying this rule. -/
  | trivial (c : Name)
  /-- The source's prefer condition: solve now, and reject the rule if
  it cannot be solved. -/
  | prefer
  /-- The source's defer condition: solve after the recursive
  translations. -/
  | defer
  /-- A refinement goal `(c, a) ∈ R`: translate it. -/
  | refine
  /-- Not a proposition at all: an implicit argument of the rule that
  the conclusion did not determine — the synthesized concrete term
  itself, most often. It is assigned when the premises are, so there is
  nothing to do (delta T7). -/
  | skip
  /-- Anything else. -/
  | other

/-- Classify a premise. -/
def classify (ty : Expr) : MetaM PremKind := do
  unless ← isProp ty do return .skip
  let ty ← whnfR ty
  match ty.getAppFn with
  | .const ``PREFER_tag _ => return .prefer
  | .const ``DEFER_tag _ => return .defer
  | .const ``PRIO_TAG _ => return .trivial ``PRIO_TAGI
  | .const ``CONSTRAINT _ => return .trivial ``CONSTRAINTI
  | .const ``TYREL _ => return .trivial ``TYRELI
  | .const ``CONST_INTF _ => return .trivial ``itypeI
  | .const ``REL_OF_INTF _ => return .trivial ``REL_OF_INTF_I
  | _ => if (parseRefine? ty).isSome then return .refine else return .other

/-- The outcome of trying one rule on one goal. -/
inductive Attempt
  /-- The rule applied: these goals are to be translated, those to be
  deferred. -/
  | ok (todo defer : List MVarId)
  /-- The rule's conclusion did not match. -/
  | noMatch
  /-- The rule's conclusion matched but a premise could not be
  discharged — the source's prefer gate. Recorded, because this is what
  a failure message must report. -/
  | sideFailed (why : MessageData)

/-- Try one rule on one goal, with the prefer gate inside the
backtracking (delta T1). -/
def attemptRule (r : Rule) (g : MVarId) : TermElabM Attempt := do
  let s ← saveState
  let gs? ← try pure (some (← applyRule r.proof r.type g)) catch _ => pure none
  match gs? with
  | none => s.restore; return .noMatch
  | some gs =>
    try
      let mut todo : Array MVarId := #[]
      let mut defer : Array MVarId := #[]
      for g' in gs do
        if ← g'.isAssigned then continue
        match ← classify (← instantiateMVars (← g'.getType)) with
        | .trivial c =>
          let rest ← applyConst c g'
          unless rest.isEmpty do throwError "the tag premise {c} was not closed"
        | .prefer => sideSolve g'
        | .defer => defer := defer.push g'
        | .refine => todo := todo.push g'
        | .skip => pure ()
        | .other =>
          let ok ← try (do let _ ← g'.assumption; pure true) catch _ => pure false
          unless ok do
            throwError "the premise is not a refinement goal, a tag or an \
              assumption:{indentD (← g'.getType)}"
      return .ok todo.toList defer.toList
    catch e =>
      s.restore
      return .sideFailed m!"{r.name}: {e.toMessageData}"

/-- Match the source's `λ'x. f x` (`ABS f`, i.e. `PROTECT (fun x =>
PROTECT (f x))`). -/
def isABS? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``PROTECT, #[_, f]) => some f
  | _ => none

/-- The source's `dflt_trans_rules = autoref_beta autoref_ABS
autoref_APP`, in the source's order, restricted to the ones whose
conclusion has the shape of the goal's abstract side (delta T9). -/
def dfltTransRules (a : Expr) : MetaM (Array Rule) := do
  let names : Array Name :=
    match isAPP? a with
    | some (f, _) => if (isABS? f).isSome then #[``autoref_beta, ``autoref_APP]
                     else #[``autoref_APP]
    | none => if (isABS? a).isSome then #[``autoref_ABS] else #[]
  names.mapM fun n => do
    let e ← mkConstWithFreshMVarLevels n
    return { name := m!"{n}", proof := e, type := ← inferType e,
             applied := n != ``autoref_ABS }

/-- The source's `trans_step_tac` on a refinement goal: resolve from the
`trans_net`, which is `fix_rel`'s priority-sorted rules followed by
`dflt_trans_rules`. -/
def transResolve (rules : Array Rule) (sideLog : IO.Ref (Array MessageData)) (g : MVarId) :
    TermElabM (MessageData × List MVarId × List MVarId) := do
  let ty ← instantiateMVars (← g.getType)
  let some (_, a, R) := parseRefine? ty
    | throwError "not a refinement goal:{indentExpr ty}"
  let applied := !(peelAPP a).2.isEmpty
  let mut reasons : Array MessageData := #[]
  for r in rules.filter (·.applied == applied) ++ (← dfltTransRules a) do
    match ← attemptRule r g with
    | .ok todo defer => return (r.name, todo, defer)
    | .noMatch => pure ()
    | .sideFailed why =>
      reasons := reasons.push why
      sideLog.modify (·.push why)
  let tail :=
    if reasons.isEmpty then
      m!"no rule's conclusion matched it."
    else
      m!"the following rules matched but their side conditions failed:\n\
        {MessageData.joinSep reasons.toList "\n"}"
  throwError "cannot translate the term{indentExpr a}\nat the relator{indentExpr R}\n{tail}"

/-- The source's `trans_tac`: `trans_step_tac` to exhaustion over a
worklist, function before argument (delta T6), with defer conditions
collected and solved at the end. -/
partial def transWork (rules : Array Rule) (sideLog : IO.Ref (Array MessageData))
    (budget : Nat) (todo defer : List MVarId) (notes : Array MessageData) :
    TermElabM (Array MessageData) := do
  match todo with
  | [] =>
    for g in defer.reverse do
      unless ← g.isAssigned do sideSolve g
    return notes
  | g :: rest =>
    if budget == 0 then
      throwError "the translation did not terminate within the step budget"
    if ← g.isAssigned then
      transWork rules sideLog budget rest defer notes
    else
      let ty ← whnfR (← instantiateMVars (← g.getType))
      match ty.getAppFn with
      | .const ``DEFER_tag _ => transWork rules sideLog (budget - 1) rest (g :: defer) notes
      | _ =>
        let (nm, new, dfr) ← transResolve rules sideLog g
        let a := ((parseRefine? (← instantiateMVars (← g.getType))).map (·.2.1)).getD ty
        transWork rules sideLog (budget - 1) (new ++ rest) (dfr ++ defer)
          (notes.push m!"trans: {a} by {nm}")

/-- Every rule the `trans` phase may use on a goal, when it is invoked
outside a full pipeline run (the `GEN_OP` solver, the debugging
tactics): the local context's refinement hypotheses, then the
databases. -/
def collectExtras (g : MVarId) : MetaM (Array Expr) :=
  g.withContext do
    let mut out : Array Expr := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let isRule ← forallTelescopeReducing (← instantiateMVars d.type) fun _ c =>
        return (parseRefine? c).isSome
      if isRule then out := out.push d.toExpr
    return out

/-! ### The `trans` phase -/

/-- The step budget of delta T6. -/
def transBudget : Nat := 2000

/-- The source's `trans_phase`, post-pass and all: the goal is first
resolved against `autoref_REMOVE_INTERNAL_EQ`, so that the concrete term
the caller's metavariable receives is the *untagged* one. -/
def transPhase : Phase where
  name := "trans"
  run := fun st => do
    let goal := st.goal
    let rules ← allRules st.extras
    -- The source's post-pass, set up first (delta T3).
    let gs ← applyConst ``autoref_REMOVE_INTERNAL_EQ goal
    let mut gMain? : Option MVarId := none
    let mut gEq? : Option MVarId := none
    for g in gs do
      let ty ← whnfR (← instantiateMVars (← g.getType))
      if let (``REMOVE_INTERNAL_EQ, _) := ty.getAppFnArgs then gEq? := some g
      else if (parseRefine? ty).isSome then gMain? := some g
    let (some gMain, some gEq) := (gMain?, gEq?)
      | throwError "autoref_REMOVE_INTERNAL_EQ did not leave a refinement goal \
          and a post-pass equation"
    let sideLog ← IO.mkRef (#[] : Array MessageData)
    let notes ←
      try
        transWork rules sideLog transBudget [gMain] [] #[]
      catch e =>
        -- The plan's supervision-legibility requirement: a translation
        -- that failed *anywhere* must name every side condition that went
        -- unmet on the way, even when the rule carrying it was rejected
        -- several steps above the goal that finally had no rule at all.
        let rej ← sideLog.get
        if rej.isEmpty then throw e
        else throwError "{e.toMessageData}\nSide conditions that went unmet \
          along the way:\n{MessageData.joinSep rej.toList "\n"}"
    -- `REMOVE_INTERNAL_EQ ?cTagged ?c`: clean the synthesized term and
    -- hand it to the caller's metavariable.
    let eqTy ← instantiateMVars (← gEq.getType)
    match (← whnfR eqTy).getAppFnArgs with
    | (``REMOVE_INTERNAL_EQ, #[_, cTagged, cOut]) =>
      let clean ← untag (← instantiateMVars cTagged)
      unless ← isDefEq cOut clean do
        throwError "the cleaned concrete term does not match the goal's:\
          {indentExpr clean}"
      let rest ← applyConst ``REMOVE_INTERNAL_EQI gEq
      unless rest.isEmpty do throwError "the post-pass equation was not closed"
    | _ => throwError "the post-pass goal is not a REMOVE_INTERNAL_EQ:{indentExpr eqTy}"
    return notes.foldl (fun s m => s.note m) st
  analyze := fun st => do
    if ← st.goal.isAssigned then return none
    return some m!"the refinement goal is still open"
  prettyFailure := fun st m => do
    let rules ← allRules st.extras
    return m!"{m}\n({rules.size} rules were available: {st.extras.size} from the call site, \
      {rules.size - st.extras.size} from the autoref_rules databases)"

end Autoref

/-! ### Debugging tactics (the source's `autoref_trans_step` /
`autoref_side`, extract §7.4; delta T5) -/

open Autoref in
/-- The source's `autoref_trans_step`: "Single translation step". -/
elab "autoref_trans_step" : tactic => do
  let g ← Tactic.getMainGoal
  let rules ← allRules (← collectExtras g)
  let (_, todo, defer) ← transResolve rules (← IO.mkRef #[]) g
  Tactic.replaceMainGoal (todo ++ defer)

open Autoref in
/-- Translate one goal to completion — the tactic the `GEN_OP` solver
re-enters the phase through, which is the source's
`side_ga_op_tac = SOLVED' (REPEAT_ON_SUBGOAL (trans_step_tac ctxt))`. -/
elab "autoref_trans" : tactic => do
  let g ← Tactic.getMainGoal
  let rules ← allRules (← collectExtras g)
  let _ ← transWork rules (← IO.mkRef #[]) transBudget [g] [] #[]
  Tactic.replaceMainGoal []

open Autoref in
/-- The source's `autoref_side`: "Solve side condition". -/
elab "autoref_side" : tactic => do
  let g ← Tactic.getMainGoal
  sideSolve g
  Tactic.replaceMainGoal []

end Lax13Proofs.Refine
