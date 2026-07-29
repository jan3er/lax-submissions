import Lax13Proofs.Refine.Autoref.IdOps

/-!
Phase three: relator fixing (`fix_rel`, priority 22).

Port of `thys/Automatic_Refinement/Tool/Autoref_Fix_Rel.thy` of AFP
`Automatic_Refinement` (Lammich) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 — AFP for Isabelle2025-2,
release 2026-02-06. The verbatim source text this file is checked
against is `plans/word-ram/refinement-tower/p2-tool-extracts.md` §2
(§2.1 the priority tags, §2.2 `CONSTRAINT` and `autoref_rules_raw`,
§2.3 `PREFER`/`DEFER`/`GEN_OP`, §2.4 `TYREL`, §2.5 the `autoref_hom`
and `autoref_tyrel` databases, §2.6 the phase itself).

The phase's job, in the extract's own summary:

> `fix_rel` (`Autoref_Fix_Rel.phase`) collects one `CONSTRAINT f R`
> subgoal per `OP f ::: R` tag in the term and solves them in sequence:
> homogeneity rewriting (`autoref_hom`), anti-unification against the
> priority-sorted `autoref_rules_raw`/`autoref_rules` database,
> `autoref_tyrel` defaulting for any relator still unfixed, and final
> resolution against that same rule set. This is the phase that pins
> `?R` to `⟨nat_rel⟩list_rel` for `append`, to `Id` for list-equality
> […] and to `bool_rel` for `is_None`/`is_Nil`.

## The source, verbatim

§2.1, the priority tags:

```isabelle
definition PRIO_TAG :: "int ⇒ int ⇒ bool"
  where [simp]: "PRIO_TAG ma mi ≡ True"
lemma PRIO_TAGI: "PRIO_TAG ma mi" by simp

abbreviation "MAJOR_PRIO_TAG i ≡ PRIO_TAG i 0"
abbreviation "MINOR_PRIO_TAG i ≡ PRIO_TAG 0 i"
abbreviation "DFLT_PRIO_TAG ≡ PRIO_TAG 0 0"

abbreviation "PRIO_TAG_OPTIMIZATION ≡ MINOR_PRIO_TAG 10"
  ‹Optimized version of an algorithm, with additional side-conditions›
abbreviation "PRIO_TAG_GEN_ALGO ≡ MINOR_PRIO_TAG (- 10)"
  ‹Generic algorithm, considered to be less efficient than default algorithm›
```

with the source's own explanation:

> Priority tags are used to influence the ordering of refinement
> theorems. A priority tag defines two numeric priorities, a major and a
> minor priority. The major priority is considered first, the minor
> priority last, i.e., after the homogenity and relator-priority
> criteria. The default value for both priorities is 0.

§2.2, `CONSTRAINT` and the raw rule database:

```isabelle
definition CONSTRAINT :: "'a ⇒ ('c×'a) set ⇒ bool"
  where [simp]: "CONSTRAINT f R ≡ True"
lemma CONSTRAINTI: "CONSTRAINT f R" by auto

ML ‹
  structure Autoref_Rules = Named_Thms (
    val name = @{binding autoref_rules_raw}
    val description = "Refinement Framework: Automatic refinement rules" );
›
```

§2.3, the side-condition tags and `GEN_OP`:

```isabelle
definition PREFER_tag :: "bool ⇒ bool"
  where [simp, autoref_tag_defs]: "PREFER_tag x ≡ x"
definition DEFER_tag :: "bool ⇒ bool"
  where [simp, autoref_tag_defs]: "DEFER_tag x ≡ x"

lemma PREFER_tagI: "P ⟹ PREFER_tag P" by simp
lemma DEFER_tagI: "P ⟹ DEFER_tag P" by simp
lemmas SIDEI = PREFER_tagI DEFER_tagI

definition [simp, autoref_tag_defs]: "GEN_OP_tag P ≡ P"
lemma GEN_OP_tagI: "P ⟹ GEN_OP_tag P" by simp
abbreviation "SIDE_GEN_OP P ≡ PREFER_tag (GEN_OP_tag P)"
abbreviation "GEN_OP c a R ≡ SIDE_GEN_OP ((c,OP a ::: R) ∈ R)"
```

§2.4, type-based relator defaulting:

```isabelle
definition TYREL :: "('a×'b) set ⇒ bool" where [simp]: "TYREL R ≡ True"
definition TYREL_DOMAIN :: "'a itself ⇒ bool" where [simp]: "TYREL_DOMAIN i ≡ True"

lemma TYREL_RES: "⟦ TYREL_DOMAIN TYPE('a); TYREL (R::(_×'a) set) ⟧ ⟹ TYREL R" .
lemma DOMAIN_OF_TYREL: "TYREL (R::(_×'a) set) ⟹ TYREL_DOMAIN TYPE('a)" by simp
lemma TYRELI: "TYREL (R::(_×'a) set)" by simp
lemma ty_REL: "TYREL (R::(_×'a) set)" by simp
```

§2.6, the phase's five steps (structural description, ML elided by the
extraction):

> (1) `insert_CONSTRAINTS_tac` walks the tagged term
> (`constraints_of_term`, recursing through `APP`/`ABS`/`OP ... :::`)
> and inserts one `CONSTRAINT f R` subgoal per `OP f ::: R` annotation
> found; (2) homogeneity rewriting against the `autoref_hom` net;
> (3) anti-unification *specialization* against a net built from every
> `thm_pairsD` constraint — this is the actual "look up the rule whose
> LHS operator matches" step; (4) `tyrel_tac` […]; (5) full solving.

and the cached rule state it runs against:

> `thm_pairsD` — every `autoref_rules_raw` theorem paired with its
> *constraint* `(gen_ops, (f, R))` (extracted by `constraint_of_thm`:
> the operator's head `f` and the relator `R` it refines under, plus any
> `GEN_OP` side-premises), sorted by
> `(major_prio, hom_count, rel_prio, minor_prio)`.

## Substrate deltas and departures, each flagged

**F1 — `CONSTRAINT` goals are computed, not inserted.** The source's
step (1) *inserts* one subgoal per annotation and steps (2)–(5) discharge
them; since `CONSTRAINT f R ≡ True` the subgoals carry no proof content
whatever — their whole purpose is to give the unifier a place to fix
`R`. `constraintsOfTerm` below collects the same list and
`solveConstraint` fixes the same metavariables, without manufacturing
`True`s. `CONSTRAINT` and `CONSTRAINTI` are ported so that a rule may
still carry a `CONSTRAINT` premise, and so the phase's trace prints in
the source's vocabulary.

**F2 — matching is `isDefEq`, not anti-unification.** The source's step
(3) indexes rules in an `Anti_Unification` net and specialises against
it; design record §3 P2 row 3 already replaced that indexing ("DiscrTree
replaces `Anti_Unification`-based indexing"), and wave B2's delta S2
recorded that at spine scale the honest implementation is a linear scan.
This is that scan: rules in priority order, first whose operator *and*
relator unify with the constraint wins. The DiscrTree upgrade is local
to `candidates` below.

**F3 — the sort key is `(major, minor)`, not
`(major, hom_count, rel_prio, minor)`.** `hom_count` counts matches
against the `autoref_hom` net and `rel_prio` reads a relator-priority
table; neither database is registered (wave B2's `Autoref/Attrs.lean` is
frozen for this wave and carries neither `autoref_hom` nor a relator
priority table — delta I7's list). Both dropped criteria are *tie
breakers between rules of equal major priority*; with them gone, ties
break on the declaration name, so the order is still total and
reproducible. Step (2), homogeneity rewriting, is absent for the same
reason.

**F4 — call-site rules come first, then the database by priority.** The
source has one net: `assumes [autoref_rules]: "(succi,E)∈⟨Id⟩succg_rel"`
enters `thm_pairsD` like any other rule, at default priority. Lean has
no attribute on a local hypothesis, so `Autoref/Tool.lean` collects
relational hypotheses out of the local context (its delta O1) and passes
them here in `State.extras`, and they are tried *before* the database
rather than merged into it at priority (0,0). The difference is visible
only when a database rule of positive major priority would otherwise
beat a local assumption; at spine scope no such rule exists, and putting
the call site first is the reading of "on the fly" the tutorial's own
examples want.

**F5 — `tyrel` defaulting is one step deep.** `tyrel_tac` in the source
inserts a `TYREL` subgoal for every relator variable still free and
solves it through the `autoref_tyrel` net, with `TYREL_RES` /
`DOMAIN_OF_TYREL` letting a user's rule dispatch on the abstract type
*before* the relator is known. Here `tyrelDefault` matches an
unassigned relator variable's abstract type against each `autoref_tyrel`
fact's and assigns on the first match — the same mechanism, without the
`TYREL_DOMAIN` staging, and with no recursion into the assigned
relator's own arguments. The database is empty at spine scope (nothing
in the tutorial's pure-HOL examples pins a type's relator), so this path
is ported but unexercised, and it says so here rather than pretending
otherwise.

**F6 — `autoref_rules` is a plain label attribute.** The source's
`attribute_setup autoref_rules` does two things: register into
`autoref_rules_raw`, and *derive* an `autoref_itype` fact for the
operator via `intf_of_rel` / `decl_derived_typing`. Wave B2 registered
`autoref_rules` as a label attribute (`Autoref/Attrs.lean`, frozen), so
only the first half exists; the second half feeds the `autoref_itype`
net, which delta I5 already records as empty and bypassed. The
`(overloaded)` mode flag — which suppresses the warning when a second
interface type is derived for an already-typed constant — has nothing to
suppress and is likewise absent. Consequence for the port: the two
databases are read *together* here, and a rule tagged either way is
found.
-/

open Lean Meta Elab

namespace Lax13Proofs.Refine

/-! ### Priority tags (`Autoref_Fix_Rel.thy` §2.1) -/

/-- The source's `PRIO_TAG :: int ⇒ int ⇒ bool`, `PRIO_TAG ma mi ≡ True`:
a rule's major and minor priority, carried as a premise. -/
def PRIO_TAG (_ma _mi : ℤ) : Prop := True

/-- The source's `PRIO_TAG` definition, with the source's own `[simp]`. -/
@[simp] theorem PRIO_TAG_def (ma mi : ℤ) : PRIO_TAG ma mi ↔ True := Iff.rfl

/-- The source's `PRIO_TAGI`. -/
theorem PRIO_TAGI (ma mi : ℤ) : PRIO_TAG ma mi := trivial

/-- The source's `MAJOR_PRIO_TAG i ≡ PRIO_TAG i 0`. -/
abbrev MAJOR_PRIO_TAG (i : ℤ) : Prop := PRIO_TAG i 0

/-- The source's `MINOR_PRIO_TAG i ≡ PRIO_TAG 0 i`. -/
abbrev MINOR_PRIO_TAG (i : ℤ) : Prop := PRIO_TAG 0 i

/-- The source's `DFLT_PRIO_TAG ≡ PRIO_TAG 0 0`. -/
abbrev DFLT_PRIO_TAG : Prop := PRIO_TAG 0 0

/-- The source's `PRIO_TAG_OPTIMIZATION ≡ MINOR_PRIO_TAG 10`:
"Optimized version of an algorithm, with additional side-conditions". -/
abbrev PRIO_TAG_OPTIMIZATION : Prop := MINOR_PRIO_TAG 10

/-- The source's `PRIO_TAG_GEN_ALGO ≡ MINOR_PRIO_TAG (- 10)`: "Generic
algorithm, considered to be less efficient than default algorithm" —
minor priority −10, so *below* any type-specific rule at the default
(0,0). -/
abbrev PRIO_TAG_GEN_ALGO : Prop := MINOR_PRIO_TAG (-10)

/-! ### The relator constraint (`Autoref_Fix_Rel.thy` §2.2) -/

/-- The source's `CONSTRAINT :: 'a ⇒ ('c×'a) set ⇒ bool`,
`CONSTRAINT f R ≡ True`: "the operator `f` is to be translated at
relator `R`". Carries no information — its job is to give the phase a
place to fix `R` (delta F1). -/
def CONSTRAINT {γ α : Type} (_f : α) (_R : Set (γ × α)) : Prop := True

/-- The source's `CONSTRAINT` definition, with the source's own
`[simp]`. -/
@[simp] theorem CONSTRAINT_def {γ α : Type} (f : α) (R : Set (γ × α)) :
    CONSTRAINT f R ↔ True := Iff.rfl

/-- The source's `CONSTRAINTI`. -/
theorem CONSTRAINTI {γ α : Type} (f : α) (R : Set (γ × α)) : CONSTRAINT f R := trivial

/-! ### Side-condition tags and `GEN_OP` (`Autoref_Fix_Rel.thy` §2.3)

The source's own comment: "Generic algorithm tags have to be defined
here, as we need them for relator fixing !" — the user-facing
`PREFER`/`DEFER` abbreviations and `SIDE_PRECOND` live one phase later,
in `Autoref/Translate.lean`, exactly as the extract's Gaps section
records. -/

/-- The source's `PREFER_tag :: bool ⇒ bool`, `PREFER_tag x ≡ x`: a side
condition that must be solvable *before* the rule applies, so it
restricts the abstract expression. -/
def PREFER_tag (x : Prop) : Prop := x

/-- The source's `PREFER_tag` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem PREFER_tag_def (x : Prop) : PREFER_tag x ↔ x := Iff.rfl

/-- The source's `DEFER_tag :: bool ⇒ bool`, `DEFER_tag x ≡ x`: a side
condition checked *after* the rule applied and the recursive
translations ran, so it restricts the translated expression. -/
def DEFER_tag (x : Prop) : Prop := x

/-- The source's `DEFER_tag` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem DEFER_tag_def (x : Prop) : DEFER_tag x ↔ x := Iff.rfl

/-- The source's `PREFER_tagI`. -/
theorem PREFER_tagI {P : Prop} (h : P) : PREFER_tag P := h

/-- The source's `DEFER_tagI`. -/
theorem DEFER_tagI {P : Prop} (h : P) : DEFER_tag P := h

/-- The source's `GEN_OP_tag P ≡ P`. -/
def GEN_OP_tag (P : Prop) : Prop := P

/-- The source's `GEN_OP_tag` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem GEN_OP_tag_def (P : Prop) : GEN_OP_tag P ↔ P := Iff.rfl

/-- The source's `GEN_OP_tagI`. -/
theorem GEN_OP_tagI {P : Prop} (h : P) : GEN_OP_tag P := h

/-- The source's `SIDE_GEN_OP P ≡ PREFER_tag (GEN_OP_tag P)`. -/
abbrev SIDE_GEN_OP (P : Prop) : Prop := PREFER_tag (GEN_OP_tag P)

/-- The source's
`GEN_OP c a R ≡ SIDE_GEN_OP ((c,OP a ::: R) ∈ R)`, its "Shortcut for
assuming an operation in a generic algorithm lemma": the premise a
generic algorithm states to get its operator instantiated by the
`GEN_OP` solver. -/
abbrev GEN_OP {γ α : Type} (c : γ) (a : α) (R : Set (γ × α)) : Prop :=
  SIDE_GEN_OP ((c, OP a ::: R) ∈ R)

/-! ### Type-based relator defaulting (`Autoref_Fix_Rel.thy` §2.4) -/

/-- The source's `TYREL :: ('a×'b) set ⇒ bool`, `TYREL R ≡ True`: the
`autoref_tyrel` database's fact shape — "use `R` for its abstract
type". -/
def TYREL {γ α : Type} (_R : Set (γ × α)) : Prop := True

/-- The source's `TYREL` definition, with the source's own `[simp]`. -/
@[simp] theorem TYREL_def {γ α : Type} (R : Set (γ × α)) : TYREL R ↔ True := Iff.rfl

/-- The source's `TYREL_DOMAIN :: 'a itself ⇒ bool`. Isabelle's
`TYPE('a)` is Lean's `(α : Type)` itself, so the argument is the type. -/
def TYREL_DOMAIN (_α : Type) : Prop := True

/-- The source's `TYREL_DOMAIN` definition, with the source's own
`[simp]`. -/
@[simp] theorem TYREL_DOMAIN_def (α : Type) : TYREL_DOMAIN α ↔ True := Iff.rfl

/-- The source's `TYREL_RES`. -/
theorem TYREL_RES {γ α : Type} {R : Set (γ × α)}
    (_h₁ : TYREL_DOMAIN α) (h₂ : TYREL R) : TYREL R := h₂

/-- The source's `DOMAIN_OF_TYREL`. -/
theorem DOMAIN_OF_TYREL {γ α : Type} {R : Set (γ × α)} (_h : TYREL R) :
    TYREL_DOMAIN α := trivial

/-- The source's `TYRELI`, the fallback the phase uses when no
`autoref_tyrel` rule applies. -/
theorem TYRELI {γ α : Type} (R : Set (γ × α)) : TYREL R := trivial

/-- The source's `ty_REL`, the lemma a user instantiates to pin the
default relator of an abstract type:
`notes [autoref_tyrel] = ty_REL[where 'a="'a set" and R="⟨Id⟩dflt_ahs_rel"]`. -/
theorem ty_REL {γ α : Type} (R : Set (γ × α)) : TYREL R := trivial

namespace Autoref

/-! ### The rule database -/

/-- One entry of the source's `thm_pairsD`: a rule together with the
priorities read off its `PRIO_TAG` premises. -/
structure Rule where
  /-- How the rule prints in a trace or a failure message. -/
  name : MessageData
  /-- The rule as a term. -/
  proof : Expr
  /-- Its type. -/
  type : Expr
  /-- The source's `major_prio`. -/
  major : Int := 0
  /-- The source's `minor_prio`. -/
  minor : Int := 0
  /-- A total tie-break, so the order does not depend on the database's
  insertion order (delta F3). -/
  tie : String := ""
  /-- Whether the rule's conclusion's abstract side is an *applied*
  `$ᵃ` spine (`autoref_hd`) rather than a bare operator
  (`autoref_append`). `Autoref/Translate.lean`'s delta T9 explains why
  the translate phase dispatches on it. -/
  applied : Bool := false

/-- Read a rule's `PRIO_TAG ma mi` premise, defaulting to `(0, 0)` as
the source does. -/
def prioOfType (ty : Expr) : MetaM (Int × Int) := do
  forallTelescopeReducing ty fun xs _ => do
    let mut ma : Int := 0
    let mut mi : Int := 0
    for x in xs do
      let t ← whnfR (← inferType x)
      if let (``PRIO_TAG, #[a, b]) := t.getAppFnArgs then
        ma := (a.int?).getD 0
        mi := (b.int?).getD 0
    return (ma, mi)

/-- The source's `constraint_of_thm`: read `(f, R)` off a rule's
conclusion — "the operator's head `f` and the relator `R` it refines
under". A conclusion whose abstract side is *applied* must annotate its
operator (`(hd l, (OP hd ::: ⟨R⟩list_rel → R)$l') ∈ R`), because that
annotation is the only place the operator's own relator appears. -/
def constraintOfConcl (concl : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_, a, R) := parseRefine? concl | return none
  let (h, args) := peelAPP a
  let h ← whnfR h
  match isOpRel? h with
  | some (f, R') => return some (f, R')
  | none =>
    if !args.isEmpty then return none
    match isOP? h with
    | some f => return some (f, R)
    | none => return some (h, R)

/-- Whether a rule's conclusion translates an *applied* term. -/
def concluAppliedOfType (ty : Expr) : MetaM Bool :=
  withNewMCtxDepth do
    let (_, _, concl) ← forallMetaTelescope ty
    match parseRefine? concl with
    | some (_, a, _) => return !(peelAPP a).2.isEmpty
    | none => return false

/-- Build a `Rule` from a global declaration name. -/
def ruleOfConst (n : Name) : MetaM Rule := do
  let e ← mkConstWithFreshMVarLevels n
  let ty ← inferType e
  let (ma, mi) ← prioOfType ty
  return { name := m!"{n}", proof := e, type := ty, major := ma, minor := mi,
           tie := n.toString, applied := ← concluAppliedOfType ty }

/-- Build a `Rule` from a call-site term (a local hypothesis, or a rule
named at the call site — delta F4). -/
def ruleOfExpr (i : Nat) (e : Expr) : MetaM Rule := do
  let ty ← inferType e
  let (ma, mi) ← prioOfType ty
  return { name := m!"{e}", proof := e, type := ty, major := ma, minor := mi,
           tie := s!"{i}", applied := ← concluAppliedOfType ty }

/-- The source's `thm_pairsD`, sorted: the `autoref_rules` and
`autoref_rules_raw` databases (delta F6 reads them together), highest
major priority first, then highest minor priority, then the declaration
name (delta F3). -/
def dbRules : MetaM (Array Rule) := do
  let mut names : Array Name := #[]
  for n in (← Lean.labelled `autoref_rules) ++ (← Lean.labelled `autoref_rules_raw) do
    unless names.contains n do names := names.push n
  let rs ← names.mapM ruleOfConst
  return rs.qsort fun a b =>
    a.major > b.major ||
      (a.major == b.major &&
        (a.minor > b.minor || (a.minor == b.minor && a.tie < b.tie)))

/-- Every rule the phase may use: the call site's first, then the
database (delta F4). -/
def allRules (extras : Array Expr) : MetaM (Array Rule) := do
  let ex ← extras.mapIdxM fun i e => ruleOfExpr i e
  return ex ++ (← dbRules)

/-- A fresh instance of a rule: its premises as metavariables, its
conclusion's constraint `(f, R)`. -/
def ruleConstraint (r : Rule) : MetaM (Option (Expr × Expr)) := do
  let (_, _, concl) ← forallMetaTelescope r.type
  constraintOfConcl concl

/-- The source's step (3): the first rule, in priority order, whose
operator *and* relator unify with the constraint (delta F2). The
assignment is kept only on success. -/
def solveConstraint (rules : Array Rule) (f R : Expr) : MetaM (Option Rule) := do
  for r in rules do
    let ok ← commitWhen do
      match ← ruleConstraint r with
      | none => return false
      | some (f', R') => return (← isDefEq f' f) && (← isDefEq R' R)
    if ok then return some r
  return none

/-- Rules whose operator alone matches — what a failure message offers
when no rule matched operator *and* relator. -/
def candidates (rules : Array Rule) (f : Expr) : MetaM (Array Rule) := do
  let mut out := #[]
  for r in rules do
    let ok ← withNewMCtxDepth do
      match ← ruleConstraint r with
      | none => return false
      | some (f', _) => isDefEq f' f
    if ok then out := out.push r
  return out

/-! ### Constraints of a tagged term (the source's `constraints_of_term`) -/

/-- The source's `constraints_of_term`, "recursing through `APP`/`ABS`/
`OP ... :::`": one `CONSTRAINT f R` per operator annotation, head
first. -/
partial def constraintsOfTerm (e : Expr) : Array (Expr × Expr) :=
  if let some (f, x) := isAPP? e then
    constraintsOfTerm f ++ constraintsOfTerm x
  else if let some (f, R) := isOpRel? e then
    #[(f, R)]
  else
    #[]

/-! ### `tyrel` defaulting (delta F5) -/

/-- The `autoref_tyrel` database's facts, as `TYREL R` relators. -/
def tyrelRules : MetaM (Array (Name × Expr)) := do
  (← Lean.labelled `autoref_tyrel).mapM fun n => do
    return (n, ← mkConstWithFreshMVarLevels n)

/-- The source's `tyrel_tac`, one step deep (delta F5): a relator still
unassigned after rule matching is given the `autoref_tyrel` relator
whose abstract type matches, if there is one. -/
def tyrelDefault (R : Expr) : MetaM (Option Name) := do
  unless (← instantiateMVars R).hasExprMVar do return none
  for (n, e) in ← tyrelRules do
    let ok ← commitWhen do
      let (_, _, concl) ← forallMetaTelescope (← inferType e)
      match concl.getAppFnArgs with
      | (``TYREL, #[_, _, R']) => isDefEq R' R
      | _ => return false
    if ok then return some n
  return none

/-! ### The `fix_rel` phase -/

/-- The source's `Autoref_Fix_Rel.phase`. -/
def fixRelPhase : Phase where
  name := "fix_rel"
  run := fun st => do
    let ty ← instantiateMVars (← st.goal.getType)
    let some (_, a, _) := parseRefine? ty
      | throwError "the goal is not of the form `(?c, a) ∈ ?R`:{indentExpr ty}"
    let rules ← allRules st.extras
    let mut st := st
    for (f₀, R₀) in constraintsOfTerm a do
      let f ← instantiateMVars f₀
      let R ← instantiateMVars R₀
      match ← solveConstraint rules f R with
      | some r =>
        st := st.note m!"fix_rel: CONSTRAINT {f} {R} solved by {r.name}"
      | none =>
        let cands ← candidates rules f
        let names :=
          if cands.isEmpty then m!"(none)"
          else MessageData.joinSep (cands.map (·.name)).toList ", "
        let nDb := (← Lean.labelled `autoref_rules).size
        throwError "no rule fixes the relator of the operator{indentExpr f}\n\
          at the relator{indentExpr R}\n\
          {rules.size} rules were considered ({nDb} of them in the autoref_rules \
          database, {st.extras.size} supplied at the call site); \
          {cands.size} match the operator but not the relator: {names}"
      match ← tyrelDefault (← instantiateMVars R₀) with
      | some n => st := st.note m!"fix_rel: tyrel default {n} applied"
      | none => pure ()
    return st
  prettyFailure := fun st m => do
    let ty ← instantiateMVars (← st.goal.getType)
    return m!"{m}\ngoal at this phase:{indentExpr ty}"

end Autoref

end Lax13Proofs.Refine
