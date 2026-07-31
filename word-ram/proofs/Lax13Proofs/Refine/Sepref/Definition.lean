import Lax13Proofs.Refine.Sepref.Tool

/-!
The synthesis command: the port of `thys/sepref/Sepref_Definition.thy`,
and the wave's end-to-end gate.

Source pin as `Sepref/Basic.lean`'s header (`isabelle_llvm_time`
@ `42dd7f5`); the theory was fetched whole (172 lines) and is 40 lines
of `Term_Synth` marker constants plus the three Isar commands
`sepref_definition`, `sepref_def` and `sepref_thm`, all built out of one
ML function `sd_cmd`:

```isabelle
fun sd_cmd ((((name,attribs_def),attribs_ref),t_raw),r_raw) lthy = let
    val t = mk_synth_term lthy t_raw r_raw          (* SYNTH f R *)
    val ((pat,goal),ctxt) = make_hnr_goal t lthy    (* the hnr goal *)
    fun after_qed [[thm]] ctxt = …
      Definition_Utils.define_concrete_fun NONE name attribs_def attribs_ref [] thm [pat] lthy
  in Proof.theorem NONE after_qed [[ (goal,[]) ]] ctxt end
```

## Judgment calls

**P4/D-da (superseded by tower-expansion P1.B) — the original command
accepted a written goal; it now also accepts an `hfref` signature.** The
source's user writes
`sepref_definition foo is bar :: nat_assn⇧k →⇩a nat_assn`: a name, an
abstract program and an `hfref` *signature*, out of which `synth_hnrI`
builds the `hn_refine` goal (which argument is destroyed, which
preserved, what the result assertion is). Two things stand in the way of
copying that. First, the signature machinery is `Sepref/Rules.lean`'s
`hfref` plus `prepare_hfref_synth_tac`, which P4/D-cx did not port.
Second, and decisively, P4/D-a made the destination a *cell name* and
P4/D-cn made the scratch pool part of the precondition: an `hfref`
signature says nothing about cell names, so the user has to write the
precondition anyway. So `sepref_synth` takes the `hnRefine` goal with
holes where the source has schematics —

```
sepref_synth chain (a b c : ℕ) :
  hnRefine (junkCell "t" ∗ junkCell "r" ∗ hnCtxt natAssn a "a" ∗ …) _ _ "r" natAssn
    (do x ← mopBinop .add a b; mopBinop .mul x c)
```

— which is exactly `schematic_goal … by sepref` with `_` for `?c` and
`?Γ'`, and is P2's `autoref_synth` shape (its delta O2, whose argument
applies here verbatim). P1.B supplies the signature form without a
second command: `sepref_synth` unfolds an `hfref` target's generic
concrete-name, abstract-argument, and precondition binders, runs the
same pipeline on the exposed `hnRefine`, and packages the proof back
into the signature. Named scratch ownership remains explicit in the
signature's input assertion rather than hidden in metaprogram state.

**P4/D-db — `sepref_thm` is the `noDef` flag.** The source has three
commands differing only in what they *add*: `sepref_definition` (theorem
+ definition + attributes), `sepref_def` (the same with default
attributes) and `sepref_thm` (theorem only). Here one command with a
`(thm_only)` flag, because the attribute defaults the other two differ in
(`[llvm_code]`, `[sepref_fr_rules]`) have no counterpart — `llvm_code`
is the source's code generator's tag, and adding the synthesized rule to
`sepref_fr_rules` is `attribute [sepref_fr_rules] name` on the next
line.

**P4/D-dc — the `Term_Synth` markers are not ported.** `SYNTH`,
`CP_UNCURRY`, `CP_PAT`, `INTRO_KD`, `SPEC_RES_ASSN`, `hfunspec`,
`UNSPEC` and the `synth_hnrI` rule exist to *derive* the goal from the
signature by resolution inside Isabelle's `Term_Synth` framework. Lean's
P1.B frontend performs that bounded derivation directly by unfolding the
transparent `hfref` judgment; it does not reproduce a general term-synthesis
engine. `SYNTH` remains the marker naming the intent.
-/

open Lean Elab Meta

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. The marker (source line 21) -/

/-- The source's `SYNTH f R ≡ True`: the tag that says "synthesize an
implementation of `f` at the signature `R`" (P4/D-dc). -/
def SYNTH {α : Type} {κ : Type} (_f : NRest α ECost) (_R : α → κ → Assn) : Prop := True

@[simp] theorem SYNTH_def {α κ : Type} (f : NRest α ECost) (R : α → κ → Assn) :
    SYNTH f R ↔ True := Iff.rfl

/-! ## 2. The command -/

namespace Definition

open Tool

/-- Parse `(f, g) ∈ hfref P RS S`, retaining the concrete function `f`.

This deliberately matches the public judgment before reduction. Reducing
`hfref` loses the expression that signature mode exports as `<name>_impl`.
-/
def parseHfref? (e : Expr) : Option Expr :=
  match e.consumeMData.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, coll, elem]) =>
      match coll.consumeMData.getAppFnArgs, elem.consumeMData.getAppFnArgs with
      | (n, #[_, _, _, _, _, _, _]), (``Prod.mk, #[_, _, f, _]) =>
          if n == `Lax13Proofs.Refine.Sepref.hfref then some f else none
      | _, _ => none
  | _ => none

/-- Run the pipeline on a written-out `hnRefine` goal or an `hfref`
signature, and return the statement, proof, and synthesized concrete
program (a `Com` in direct mode, the concrete descriptor function in
signature mode). -/
def synthesize (stmt : Expr) (cfg : Tool.Config) : TermElabM (Expr × Expr × Expr) := do
  for m in (stmt.collectMVars {}).result do m.setKind .natural
  let goal ← mkFreshExprSyntheticOpaqueMVar stmt
  if (Frame.parseHnRefine? stmt).isSome then
    seprefTac cfg goal.mvarId!
  else if (parseHfref? stmt).isSome then
    let outer := goal.mvarId!
    let reduced ← withTransparency .all (whnf (← outer.getType))
    let prepared ← outer.replaceTargetDefEq reduced
    let (xs, inner₀) ← prepared.intros
    unless xs.size == 3 do
      throwError "sepref: signature preparation expected the concrete name, abstract argument, \
        and precondition binders, but introduced {xs.size} binders"
    inner₀.withContext do
      let (inner?, _) ← simpTarget inner₀ (← IdOp.simpOnlyContext #[])
      let some inner := inner?
        | throwError "sepref: signature preparation unexpectedly closed the synthesis goal"
      let innerTy ← instantiateMVars (← inner.getType)
      let some (α, κ, Γ, c, Γfixed, d, Rfixed, m) := Frame.parseHnRefine? innerTy
        | throwError "sepref: signature preparation did not expose an hnRefine goal:{indentExpr innerTy}"
      let Γs ← mkFreshExprMVar (some (mkConst ``Assn)) .natural
      let synthTy ← mkAppOptM ``hnRefine
        #[some α, some κ, some Γ, some c, some Γs, some d, some Rfixed, some m]
      let synthProof ← mkFreshExprSyntheticOpaqueMVar synthTy
      seprefTac cfg synthProof.mvarId!
      let Γs ← instantiateMVars Γs
      let postTy ← mkAppM ``entails #[Γs, Γfixed]
      let postProof ← mkFreshExprSyntheticOpaqueMVar postTy
      let postRest ← postProof.mvarId!.apply (← mkConstWithFreshMVarLevels ``entails_refl)
      unless postRest.isEmpty do
        throwError "sepref: synthesized postcondition does not match the signature:{indentD (← Meta.ppGoal postProof.mvarId!)}"
      let resTy ← withLocalDeclD `x α fun x =>
        withLocalDeclD `y κ fun y => do
          let lhs ← mkAppM ``hnCtxt #[Rfixed, x, y]
          let rhs ← mkAppM ``hnCtxt #[Rfixed, x, y]
          mkForallFVars #[x, y] (← mkAppM ``entails #[lhs, rhs])
      let resProof ← mkFreshExprSyntheticOpaqueMVar resTy
      let (_, resGoal) ← resProof.mvarId!.intros
      let resRest ← resGoal.apply (← mkConstWithFreshMVarLevels ``entails_refl)
      unless resRest.isEmpty do
        throwError "sepref: synthesized result assertion does not match the signature:{indentD (← Meta.ppGoal resGoal)}"
      let wrapped ← mkAppM ``CONS_init
        #[← instantiateMVars synthProof, ← instantiateMVars postProof,
          ← instantiateMVars resProof]
      inner.assign wrapped
  else
    throwError "sepref: expected an hnRefine statement or an hfref signature"
  let stmt ← instantiateMVars stmt
  let proof ← instantiateMVars goal
  let prog ←
    match Frame.parseHnRefine? stmt, parseHfref? stmt with
    | some (_, _, _, c, _, _, _, _), _ => pure c
    | _, some f => pure f
    | _, _ => throwError "sepref: the synthesized statement changed to an unsupported shape"
  if proof.hasExprMVar then
    let mvs := (proof.collectMVars {}).result
    let mut msg := m!""
    for m in mvs do
      msg := msg ++ m!"\n  ?{m.name} : {← instantiateMVars (← m.getType)}"
    throwError "sepref: the synthesized proof still contains metavariables — some \
      side condition was never discharged:{msg}"
  return (stmt, proof, prog)

end Definition

open Definition in
/-- The source's `sepref_definition` / `sepref_def` / `sepref_thm`
(P4/D-da, P4/D-db). Given a name, optional binders and either an `hnRefine`
statement with `_` for the program and postcondition or an `hfref`
signature with a schematic concrete descriptor function, it runs the
`sepref` pipeline, adds the resulting theorem under the given name, and
— when the synthesized program is closed — a definition `<name>_impl`
holding it.

`(thm_only)` suppresses the definition (the source's `sepref_thm`);
`(trace)` reports each phase. -/
syntax (name := seprefSynth) "sepref_synth" ("(" ident,* ")")? ident
  (ppSpace bracketedBinder)* " : " term : command

open Definition Tool in
elab_rules : command
  | `(command| sepref_synth $[($fs,*)]? $nm:ident $bs* : $t:term) => do
    Command.liftTermElabM do
      let flags := (fs.map (·.getElems)).getD #[]
      let mut cfg : Tool.Config := {}
      let mut thmOnly := false
      for f in flags do
        match f.getId.toString with
        | "trace" => cfg := { cfg with tracing := true }
        | "thm_only" => thmOnly := true
        | s => throwError "sepref_synth: unknown flag '{s}'; the flags are \
            trace, thm_only"
      let declName := (← getCurrNamespace) ++ nm.getId
      Term.elabBinders bs fun xs => do
        let stmt ← Term.elabTerm t none
        Term.synthesizeSyntheticMVarsNoPostponing
        let (stmt, proof, prog) ← synthesize (← instantiateMVars stmt) cfg
        let type ← Term.levelMVarToParam (← instantiateMVars (← mkForallFVars xs stmt))
        let value ← Term.levelMVarToParam (← instantiateMVars (← mkLambdaFVars xs proof))
        let us := (collectLevelParams (collectLevelParams {} type) value).params
        addDecl (.thmDecl { name := declName, levelParams := us.toList, type, value })
        logInfo m!"sepref_synth {declName}:{indentExpr prog}"
        unless thmOnly || prog.hasFVar || prog.hasExprMVar do
          let iName := declName.appendAfter "_impl"
          addAndCompile (.defnDecl
            { name := iName, levelParams := [], type := ← inferType prog, value := prog,
              hints := .abbrev, safety := .safe })

open Definition Tool in
/-- Report what the pipeline produces for a written-out `hnRefine`
statement, without adding anything to the environment: the synthesized
program on success, the failure envelope on failure. This is what the
gate pins with `#guard_msgs` — the `Autoref/Solver.lean` precedent
(report instead of throwing, so a negative control leaves no failing
declaration behind). -/
syntax (name := seprefSynthCheck) "#sepref_synth" (ppSpace bracketedBinder)*
  " : " term : command

open Definition Tool in
elab_rules : command
  | `(command| #sepref_synth $bs* : $t:term) => do
    Command.liftTermElabM do
      Term.elabBinders bs fun _ => do
        let stmt ← Term.elabTerm t none
        Term.synthesizeSyntheticMVarsNoPostponing
        try
          let (_, _, prog) ← synthesize (← instantiateMVars stmt) {}
          logInfo m!"{prog}"
        catch e => logInfo (← e.toMessageData.toString)

/-! ## 3. Gate (design record ledger D4, and the wave's acceptance)

The plan's supervision-legibility watch item is the bar here: every
failure below names its phase and the condition it could not meet, and
three of them are pinned verbatim. -/

namespace SynthGate

/-! ### Smoke synthesis 1 — a straight-line program

Two chained binops, `t := a + b; r := t * c`. The abstract program is
written at the mop layer (`Sepref/IrOps.lean`); the precondition owns
the three argument cells and two scratch cells, one of which is the
destination. -/

sepref_synth chain (a b c : ℕ) :
  hnRefine (junkCell "t" ∗ junkCell "r" ∗ hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b" ∗
      hnCtxt natAssn c "c")
    _ _ "r" natAssn
    (NRest.bindT (mopBinop .add a b) fun x => mopBinop .mul x c)

-- The synthesized program, pinned: a `seq` of two `binop`s, with the
-- intermediate in the scratch cell the precondition supplied.
#guard chain_impl =
  Com.seq (Com.binop Imp.Bop.add "t" "a" "b") (Com.binop Imp.Bop.mul "r" "t" "c")

/-! ### Smoke synthesis 2 — a branch

`if m < n then r := 1 else r := 2`. Both branches write the same
destination, so the merge is `MERGE_triv`; the guard is the fused
`CondRefine` of P4/D-af, and the `.lt` condition is *synthesized* from
the abstract `decide (m < n)`. -/

sepref_synth branch (m n : ℕ) :
  hnRefine (junkCell "r" ∗ hnCtxt natAssn m "m" ∗ hnCtxt natAssn n "n")
    _ _ "r" natAssn
    (irIf (decide (m < n)) (mopConstN 1) (mopConstN 2))

#guard branch_impl =
  Com.ite (Cond.lt (Operand.cell "m") (Operand.cell "n"))
    (Com.const "r" 1) (Com.const "r" 2)

/-! ### Smoke synthesis 3 — the array pair

`t := A[i]; A[i] := t`. The linearity showcase: `hnr_mop_aset` moves the
array's ownership into the result slot, and the scratch cell it used is
junk in the postcondition. -/

sepref_synth arrayRoundTrip (xs : List ℕ) (i : ℕ) :
  hnRefine (junkCell "t" ∗ hnCtxt arrayAssn xs "A" ∗ hnCtxt natAssn i "i")
    _ _ "A" arrayAssn
    (NRest.bindT (mopAget xs i) fun v => mopAset xs i v)

#guard arrayRoundTrip_impl =
  Com.seq (Com.aget "t" "A" "i") (Com.aset "A" "i" "t")

/-! ### The `sepref` *tactic*, on a schematic goal

The command is the usual entry point, but the source's is a method, and
so is ours. A Lean goal cannot be schematic in its statement, so the
schematic form is an existential — P2's `Autoref/Tool.lean` delta O2
again — and `sepref` fills both holes. -/

example (a b : ℕ) : ∃ (c : Com) (Γ' : Assn),
    hnRefine (junkCell "t" ∗ hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b") c Γ' "t" natAssn
      (mopBinop .add a b) := by
  exact ⟨_, _, by sepref⟩

/-! ### The axiom check (the brief's requirement) -/

#print axioms chain
#print axioms branch
#print axioms arrayRoundTrip

/-! ### Smoke synthesis 4 — a tuple-state loop (P4/D-cu, P4/D-cv)

The wave's hardest integration test, and it lands: the sum of the first
`n` naturals, as a loop whose state is the pair `(i, acc)` living in the
two cells `"i"` and `"acc"`. Three pieces of wave-C machinery meet here.
The loop rule sees the state as *one* conjunct
(`hnCtxt (natAssn ×ₐ natAssn) s ("i","acc")`); the body's two in-place
`binop`s see it as *two* (`hnCtxt natAssn s.1 "i"` and
`hnCtxt natAssn s.2 "acc"`), which is `frameMatch`'s split retry; and the
body's last step rebuilds the tuple with `mopPair`, which compiles to
`skip`. The variant comes from the caller, as `LOOP_VARIANT`. -/

/-- The loop's invariant: none is needed (the abstract loop asserts it,
so a false one would make the judgment vacuous — `CombRules.lean`'s
negative control 3). -/
def sumI : ℕ × ℕ → Prop := fun _ => True

/-- The guard: `i < n`. -/
def sumBf (n : ℕ) : ℕ × ℕ → Bool := fun s => decide (s.1 < n)

/-- The body: `acc := acc + i` first (it reads the old `i`), then
`i := i + 1`, then the tuple. -/
noncomputable def sumF : ℕ × ℕ → NRest (ℕ × ℕ) ECost := fun s =>
  NRest.bindT (mopBinop .add s.2 s.1) fun acc' =>
    NRest.bindT (mopBinop .add s.1 1) fun i' => mopPair i' acc'

/-- The body's cost: one `ir.skip` for the tuple, two `ir.add`s. -/
noncomputable def sumFCost : ECost :=
  irUnit (binopCurrency Imp.Bop.add) + irUnit (binopCurrency Imp.Bop.add) +
    irUnit Currency.skip

/-- The body's value — all the variant needs. -/
theorem sumF_eq (s : ℕ × ℕ) :
    sumF s = NRest.consume
      (NRest.returnT (Imp.Bop.add.apply s.1 1, Imp.Bop.add.apply s.2 s.1)) sumFCost := by
  show NRest.bindT (mopBinop .add s.2 s.1) _ = _
  rw [mopBinop_def, NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.returnT_bindT,
    mopBinop_def, NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.returnT_bindT,
    mopPair_def, NRest.consume_consume, NRest.consume_consume, sumFCost]

/-- The variant, proved: `n - i` decreases on every iteration. -/
theorem sum_variant (n : ℕ) : LOOP_VARIANT sumI (sumBf n) sumF (fun s => n - s.1) := by
  intro s s' _ hb hle
  rw [sumF_eq s, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = (Imp.Bop.add.apply s.1 1, Imp.Bop.add.apply s.2 s.1) := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  have hlt : s.1 < n := by simpa [sumBf] using hb
  subst hs'
  show n - (s.1 + 1) < n - s.1
  omega

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth sumLoop (n : ℕ)
    (hv : LOOP_VARIANT sumI (sumBf n) sumF (fun s => n - s.1)) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn) (0, 0) ("i", "acc") ∗ hnCtxt natAssn 1 "one" ∗
      hnCtxt natAssn n "n")
    _ _ ("i", "acc") (natAssn ×ₐ natAssn)
    (irWhileIT sumI (sumBf n) sumF (0, 0))

#guard sumLoop_impl =
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    (Com.seq (Com.binop Imp.Bop.add "acc" "acc" "i")
      (Com.seq (Com.binop Imp.Bop.add "i" "i" "one") Com.skip))

/-- The variant discharged: the loop's refinement theorem, with no
hypotheses left. -/
theorem sumLoop' (n : ℕ) :
    hnRefine (hnCtxt (natAssn ×ₐ natAssn) (0, 0) ("i", "acc") ∗ hnCtxt natAssn 1 "one" ∗
        hnCtxt natAssn n "n")
      sumLoop_impl (hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn n "n") ("i", "acc")
      (natAssn ×ₐ natAssn) (irWhileIT sumI (sumBf n) sumF (0, 0)) :=
  sumLoop n (sum_variant n)

#print axioms sumLoop
#print axioms sumLoop'

/-! ### The same loop, with no annotation at all (R0/D-b)

`sumLoop` above takes `hv : LOOP_VARIANT …` because P4/D-cv's loop rule
demanded a variant. It does not any more: `CombRules.lean`'s `hnr_while`
reads termination off the abstract loop's own non-failure
(`loopTerm_of_nofailT`), and it is the `sepref_comb_rules` entry.

So the annotation goes away with nothing put in its place — same goal,
same synthesized program, no hypothesis. `sumLoop` and `sum_variant`
stay compiled above: they are the landed form, and this is the delta. -/

sepref_synth sumLoopFree (n : ℕ) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn) (0, 0) ("i", "acc") ∗ hnCtxt natAssn 1 "one" ∗
      hnCtxt natAssn n "n")
    _ _ ("i", "acc") (natAssn ×ₐ natAssn)
    (irWhileIT sumI (sumBf n) sumF (0, 0))

-- The variant-free synthesis produces the *same* program.
#guard sumLoopFree_impl = sumLoop_impl

/-- …and the same theorem, with no hypothesis to discharge. -/
theorem sumLoopFree' (n : ℕ) :
    hnRefine (hnCtxt (natAssn ×ₐ natAssn) (0, 0) ("i", "acc") ∗ hnCtxt natAssn 1 "one" ∗
        hnCtxt natAssn n "n")
      sumLoopFree_impl (hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn n "n") ("i", "acc")
      (natAssn ×ₐ natAssn) (irWhileIT sumI (sumBf n) sumF (0, 0)) :=
  sumLoopFree n

#print axioms sumLoopFree
#print axioms sumLoopFree'

/-! ### Negative controls

Three ways a synthesis can go wrong, and the envelope each produces. All
three are run through `#sepref_synth`, which *reports* instead of
throwing, so the exact text is `#guard_msgs`-checkable and no failing
declaration is left behind (the `Autoref/Solver.lean` precedent). The
first is additionally run through the `sepref` tactic, to check that the
tactic really refuses. -/

/-- An operation nobody registered a rule for: its own currency, so it is
not accidentally another operation in disguise. -/
noncomputable def mopMystery (n : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT n) (irUnit "ir.mystery")

set_option linter.unusedVariables false in
set_option linter.unreachableTactic false in
/-- The `sepref` tactic refuses an unregistered operation. -/
example (n : ℕ) : True := by
  fail_if_success
    (have : hnRefine (junkCell "r" ∗ hnCtxt natAssn n "n") Com.skip (□ : Assn) "r"
        natAssn (mopMystery n) := by sepref)
  trivial

/-! #### 1 — an unregistered operation

Phase `trans`, the term it could not translate, and the ownership it
had. The rules whose *abstract* side is simply another operation are
counted, not listed; the informative ones — those that matched the
abstract term and failed later — are listed in full, as in control 2. -/

/--
info: sepref: phase 'trans' (priority 80) failed.
sepref: no rule translates
  Lax13Proofs.Refine.Sepref.SynthGate.mopMystery n
under the ownership
  Lax13Proofs.Refine.Sepref.junkCell "r" ∗ Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn n "n"
combinator rules: none is stated at this abstract term (4 tried).
operator rules: none is stated at this abstract term (8 tried).
-/
#guard_msgs in
#sepref_synth (n : ℕ) :
  hnRefine (junkCell "r" ∗ hnCtxt natAssn n "n") _ _ "r" natAssn (mopMystery n)

/-! #### 2 — an unsatisfiable frame

`t := a + b` needs a scratch cell and the precondition owns none: the
envelope names the unmatched conjunct (`junkCell` at the destination),
the conjuncts that were on offer, and — per P4/D-cn — the cell the caller
should add. -/

/--
info: sepref: phase 'trans' (priority 80) failed.
sepref: no rule translates
  Lax13Proofs.Refine.Sepref.mopBinop Lax13Proofs.Imp.Bop.add a b
under the ownership
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn a "a" ∗
    Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn b "b"
The precondition owns no scratch cell; a destination-taking rule needs `junkCell "t1"` in it.
combinator rules: none is stated at this abstract term (4 tried).
operator rules (6 more are stated at other abstract terms):
Lax13Proofs.Refine.Sepref.hnr_mop_binop: the rule's precondition conjuncts
  Lax13Proofs.Refine.Sepref.junkCell "r"
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn a ?y
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn b ?z
could not all be matched against the goal's
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn a "a"
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn b "b"
Lax13Proofs.Refine.Sepref.hnr_mop_binop_self: the rule's precondition conjuncts
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn a "r"
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn b ?z
could not all be matched against the goal's
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn a "a"
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn b "b"
-/
#guard_msgs in
#sepref_synth (a b : ℕ) :
  hnRefine (hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b") _ _ "r" natAssn
    (mopBinop .add a b)

/-! #### 3 — a `check_EVAL` leftover

An `EVAL` tag that survives the combinator step never reaches `trans`:
wave B2's own sub-phase reports it, by name and priority, and the
driver's envelope does not wrap it twice. -/

/--
info: sepref: phase 'check_EVAL' (priority 40) failed.
an `EVAL` tag survived the combinator phase:
  Lax13Proofs.Refine.Sepref.EVAL $ᵃ fun y =>
    Lax13Proofs.Refine.Sepref.PROTECT2 (HAdd.hAdd $ᵃ y $ᵃ Lax13Proofs.Refine.Sepref.PR_CONST 1)
      Lax13Proofs.Refine.Sepref.DUMMY
no `sepref_monadify_comb` equation applies to it.
Either the operation needs a combinator equation, or the tagged
application's head is an abstraction (the source's
`monadify: higher-order`), which this phase cannot flatten.
-/
#guard_msgs in
#sepref_synth :
  hnRefine (junkCell "r") _ _ "r" natAssn
    (NRest.bindT (EVAL (γ := ECost) (fun y : ℕ => y + 1)) fun g => mopConstN (g 1))

/-! ### The phase list, pinned -/

/-- info: "preproc(1) → cons_init(5) → id(10) → monadify(20) → opt_init(75) → trans(80) → opt(85) → cons_solve(90) → constraints(95)" -/
#guard_msgs in
#eval seprefPhaseList

end SynthGate

end Lax13Proofs.Refine.Sepref
