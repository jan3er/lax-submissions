import Lax13Proofs.Refine.Autoref.Tool
import Lax13Proofs.Refine.Autoref.Param

/-!
The pure-HOL operator bindings: the `autoref_rules` database, the
operation patterns, and structural expansion.

Port of `thys/Automatic_Refinement/Autoref_Bindings_HOL.thy` of AFP
`Automatic_Refinement` (Lammich) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 — AFP for Isabelle2025-2,
release 2026-02-06. The verbatim source text this file is checked
against is `plans/word-ram/refinement-tower/p2-tutorial-extracts.md` §3
(the bindings) and `plans/word-ram/refinement-tower/p2-tool-extracts.md`
§8 (structural expansion, `STRUCT_EQ`).

Wave B1 (`Autoref/Param.lean`) already *proved* the pure parametricity
half of these bindings, under the source's own names, and tagged them
`@[param]` because the `autoref_rules` database did not exist yet
(its delta PM11). Wave B2 registered the database. This file is where
the two meet: it applies `[autoref_rules]` to wave B1's declarations
across the module boundary — which is why almost nothing here is a new
theorem — and adds the four bindings B1 deliberately deferred
(its delta PM13: `autoref_hd` needs `SIDE_PRECOND`, `autoref_list_eq`
needs `GEN_OP`, the generic layer needs `PRIO_TAG_GEN_ALGO`) plus the
operation patterns the tutorial's `is_None`/`is_Nil` route runs on.

## The source, verbatim

The bindings, from tutorial extract §3 (`autoref_nat`,
`autoref_append`, `refine_list`, `autoref_opt`, `autoref_is_None`,
`autoref_is_Nil` are quoted in `Autoref/Param.lean`'s own header and are
not repeated):

```isabelle
  lemma [autoref_rules]:
    assumes "PRIO_TAG_GEN_ALGO"
    shows "((<), (<)) ∈ Id→Id→bool_rel"
    and "((≤), (≤)) ∈ Id→Id→bool_rel"
    and "((=), (=)) ∈ Id→Id→bool_rel"
    and "(numeral x,OP (numeral x) ::: Id) ∈ Id"
    and "(uminus,uminus) ∈ Id → Id"
    and "(0,0) ∈ Id"
    and "(1,1) ∈ Id"
    by auto

  lemma autoref_hd[autoref_rules]:
    "⟦ SIDE_PRECOND (l'≠[]); (l,l') ∈ ⟨R⟩list_rel ⟧ ⟹
      (hd l,(OP hd ::: ⟨R⟩list_rel → R)$l') ∈ R"

  lemma list_eq_expand[autoref_struct_expand]: "(=) = (list_eq (=))"

  lemma autoref_list_eq[autoref_rules (overloaded)]:
    "GEN_OP eq (=) (R→R→Id) ⟹ (list_eq eq, (=))
    ∈ ⟨R⟩list_rel → ⟨R⟩list_rel → Id"
    unfolding autoref_tag_defs
    apply (subst list_eq_expand)
    apply (parametricity add: autoref_list_eq_aux)
    done
```

and, from tool extract §8, the structural-expansion layer this file also
owns (the extraction's own finding: `autoref_struct_expand` "is declared
locally, consumer-side, in `Autoref_Bindings_HOL.thy` itself", *not* in
the generic `Tool/` layer):

```isabelle
definition [simp]: "STRUCT_EQ_tag x y ≡ x = y"
lemma STRUCT_EQ_tagI: "x=y ⟹ STRUCT_EQ_tag x y" by simp

ML ‹
  structure Autoref_Struct_Expand = struct
    structure autoref_struct_expand = Named_Thms (
      val name = @{binding autoref_struct_expand}
      val description = "Autoref: Structural expansion lemmas" )

    fun expand_tac ctxt = let
      val ss = ctxt |> put_simpset HOL_basic_ss
                    |> Simplifier.add_simps (autoref_struct_expand.get ctxt)
    in SOLVED' (asm_simp_tac ss) end

    val setup = autoref_struct_expand.setup
    val decl_setup = fn phi =>
      Tagged_Solver.declare_solver @{thms STRUCT_EQ_tagI} @{binding STRUCT_EQ}
        "Autoref: Equality modulo structural expansion" (expand_tac) phi
  end
›
```

with the source's motivation quoted in full, because it is what the
`STRUCT_EQ` solver is *for*:

> In some situations, autoref imitates the operations on typeclasses and
> the typeclass hierarchy. This may result in structural mismatches,
> e.g., a hashcode side-condition may look like
> `is_hashcode (prod_eq (=) (=)) hashcode`. This cannot be discharged by
> the rule `is_hashcode (=) hashcode`. In order to handle such cases, we
> introduce a set of simplification lemmas that expand the structure of
> an operator as far as possible. These lemmas are integrated into a
> tagged solver, that can prove equality between operators modulo
> structural expansion.

## Substrate deltas and departures, each flagged

**B1 — the operation patterns are authored, to the shape the tutorial's
route requires.** The extraction records that the `is_None_pat` /
`is_Nil_pat` rules — the `autoref_op_pat` entries that rewrite `a = None`
to `is_None$a` and `[] = a` to `is_Nil$a` *before* any relator-level rule
fires — "were elided from §3" of the tutorial extract, and the tool
extract's §1.4 confirms they exist but were not quoted. So the four
rules below are authored, not transcribed: their *shape* is the
source's own `autoref_op_pat` shape (`E``{v} ≡ op_succ$E$v` — raw
pattern on the left, tagged operator application on the right), their
*content* is fixed by what the tutorial's three equality entries need,
and each is `#guard`-refuted at concrete data in the gate below before
being proved. The fidelity charter forbids guessing at a source
statement that has not been read; this records that these four are not
readings of one.

Two of the four have no source counterpart at all and exist for
substrate reasons:

* `append_pat`, because Lean's `l ++ l'` is
  `@HAppend.hAppend _ _ _ inst l l'` and the rule wave B1 proved is
  stated at `List.append`, where HOL's `@` *is* `append`. Rewriting the
  surface operator to the one that carries a rule is exactly what an
  operation pattern is for.
* the *reversed* `is_Nil` / `is_None` patterns (`a = []` as well as
  `[] = a`), because the tutorial's third entry is `[1,2,3] = []` — the
  empty list on the right — while its sixth is `[] = a`. The source must
  have both for the same reason.

**B2 — `decide` needs an instance where HOL's `(=)` needs nothing, and
the instance is schematic in the pattern.** Wave B1's delta PM8 settled
that HOL's `bool`-valued `(=)` is Lean's `decide (a = b)`. For lists and
options that decision is available *without* `DecidableEq` on the
element type — `List.instDecidableEqNil` and `Option.decidableEqNone`
decide exactly `l = []` and `o = none` — which is what keeps the
tutorial's own remark on its `a = None` entry true here: "Note that we
do not require equality on the element type!". The patterns are stated
with the instance as an instance-implicit *variable*, so that they fire
whichever instance the elaborator picked (`instDecidableEqList` when the
element type happens to have one, `List.instDecidableEqNil` when it does
not).

**B3 — the generic layer is ported at two of its seven statements.**
`((=),(=))` and `(numeral x, OP (numeral x) ::: Id) ∈ Id` are ported —
the first because it is the one the priority mechanism is *demonstrated*
on (it matches list equality too, at minor priority −10, and must lose
to `autoref_list_eq` at (0,0)), the second because it covers the
source's `(0,0)` and `(1,1)` as well (wave B1's delta PM7: Lean has no
`numeral`, and `@OfNat.ofNat α k inst` is the operator). `((<),(≤))` and
`uminus` are not ported: each needs a Lean order/negation type-class
binder that HOL's `ord`/`uminus` classes do not translate to one-for-one,
and no acceptance entry consults them. They are a demand-driven
addition, not a gap in the mechanism.

**B4 — `hd` is `List.headI`.** HOL's `hd` is total-but-underspecified on
`[]`; Lean's `List.head` takes a proof that the list is non-empty, which
would put the `SIDE_PRECOND` *inside* the term rather than beside it.
`List.headI` (mathlib) is the `Inhabited`-defaulting total function, so
`autoref_hd` ports clause for clause with its `SIDE_PRECOND (l' ≠ [])`
premise intact — and that premise is exactly what the `PRECOND` solver
discharges, which is what makes the `hd` entries worth reproducing.

**B5 — `autoref_list_eq` is stated at wave B1's `list_eq`**, whose
equality argument is `Bool`-valued (delta PM8), with its `GEN_OP`
premise at the operator `fun a a' : α => decide (a = a')` — the shape
the identification phase produces (`Autoref/IdOps.lean` delta I4) and the
shape wave B1's `autoref_nat_eq` is stated at, so the `GEN_OP` solver
finds it. The source's `(overloaded)` mode flag has nothing to suppress
here (`Autoref/FixRel.lean` delta F6).

**B6 — `list_eq_expand` gets its `[autoref_struct_expand]` tag here**,
resolving wave B1's PM10: the tag is applied across the module boundary
by `attribute [autoref_struct_expand] list_eq_expand`, so B1's statement
and proof are untouched. Every other `[autoref_rules]` tag in this file
is applied the same way, which is why wave B1's file needed no edit at
all.
-/

open Lean Meta Elab

universe u

namespace Lax13Proofs.Refine

/-! ### The `autoref_rules` database: wave B1's bindings, tagged
(delta B6)

The source tags each of these `[autoref_rules]` at its declaration;
wave B1 proved them under the source's names and tagged them `@[param]`
(its delta PM11, "when wave C lands `autoref_rules`, these declarations
get that tag too; nothing about their statements changes"). This is that
tag, applied across the module boundary. -/

-- `autoref_nat` (tutorial extract §3), split per statement by wave B1's
-- delta PM3 and with numerals collapsed by its PM7.
attribute [autoref_rules]
  autoref_nat_lit autoref_nat_zero autoref_nat_one autoref_nat_succ
  autoref_nat_lt autoref_nat_le autoref_nat_eq
  autoref_nat_add autoref_nat_sub autoref_nat_div autoref_nat_mul autoref_nat_mod

-- `autoref_append` and `refine_list`.
attribute [autoref_rules]
  autoref_append refine_list_nil refine_list_cons refine_list_cases

-- `autoref_opt`, which wave B1 named after the source's `param_option`
-- (the two are the same four statements).
attribute [autoref_rules]
  param_option_none param_option_some param_option_cases param_option_rec

-- `autoref_is_None` / `autoref_is_Nil`, which the source tags
-- `[param,autoref_rules]`.
attribute [autoref_rules] autoref_is_None autoref_is_Nil

-- `list_eq_expand`, the source's `[autoref_struct_expand]` (delta B6,
-- resolving wave B1's PM10).
attribute [autoref_struct_expand] list_eq_expand

/-! ### The generic layer (delta B3) -/

/-- The source's generic `((=), (=)) ∈ Id→Id→bool_rel` under
`PRIO_TAG_GEN_ALGO`: equality on *any* decidable type, at minor priority
−10 — so a type-specific rule at the default (0,0) always wins, which is
what the priority mechanism is for. -/
@[autoref_rules] theorem autoref_gen_eq {α : Type} [DecidableEq α]
    (_p : PRIO_TAG_GEN_ALGO) :
    ((fun a b : α => decide (a = b)), (fun a b : α => decide (a = b))) ∈
      Set.diagonal α →ᵣ Set.diagonal α →ᵣ boolRel :=
  funRel_diagonal_self₂ _

/-- The source's `(numeral x, OP (numeral x) ::: Id) ∈ Id` under
`PRIO_TAG_GEN_ALGO`, which by wave B1's delta PM7 also covers its
`(0,0) ∈ Id` and `(1,1) ∈ Id`: a literal of any type with an `OfNat`
instance refines itself at the identity relation. -/
@[autoref_rules] theorem autoref_gen_numeral {α : Type} (k : ℕ) [OfNat α k]
    (_p : PRIO_TAG_GEN_ALGO) :
    ((OfNat.ofNat k : α), OP (OfNat.ofNat k : α) ::: Set.diagonal α) ∈ Set.diagonal α :=
  rfl

/-! ### `hd` (delta B4) -/

/-- The source's `autoref_hd`, at `List.headI` (delta B4):

```isabelle
lemma autoref_hd[autoref_rules]:
  "⟦ SIDE_PRECOND (l'≠[]); (l,l') ∈ ⟨R⟩list_rel ⟧ ⟹
    (hd l,(OP hd ::: ⟨R⟩list_rel → R)$l') ∈ R"
```

The `SIDE_PRECOND` premise is what the `PRECOND` solver discharges, and
the annotated, *applied* conclusion is what makes this the one rule in
the acceptance scope whose operator's relator is read off its own `:::`
annotation (`Autoref/FixRel.lean`'s `constraintOfConcl`). -/
@[autoref_rules] theorem autoref_hd {γ α : Type} [Inhabited γ] [Inhabited α]
    {R : Set (γ × α)} {l : List γ} {l' : List α}
    (hne : SIDE_PRECOND (l' ≠ [])) (hl : (l, l') ∈ listRel R) :
    (List.headI l, (OP List.headI ::: (listRel R →ᵣ R)) $ᵃ l') ∈ R := by
  simp only [PREFER_tag_def, PRECOND_tag_def, REMOVE_INTERNAL_def] at hne
  show (List.headI l, List.headI l') ∈ R
  rw [mem_listRel_iff] at hl
  cases hl with
  | nil => exact absurd rfl hne
  | cons hx _ => exact hx

/-! ### List equality: the `GEN_OP` route (delta B5) -/

/-- The source's `autoref_list_eq`:

```isabelle
lemma autoref_list_eq[autoref_rules (overloaded)]:
  "GEN_OP eq (=) (R→R→Id) ⟹ (list_eq eq, (=))
   ∈ ⟨R⟩list_rel → ⟨R⟩list_rel → Id"
  unfolding autoref_tag_defs
  apply (subst list_eq_expand)
  apply (parametricity add: autoref_list_eq_aux)
  done
```

with the source's own proof: unfold the tags, rewrite the abstract
equality into `list_eq` form by `list_eq_expand`, and finish by
parametricity of `list_eq`. Note what the statement does *not* require:
nothing about `R`, so list equality refines without any equality on the
element type — the tutorial's own remark on its `[1,2] = [2,3]` entry. -/
@[autoref_rules] theorem autoref_list_eq {γ α : Type} [DecidableEq α]
    {R : Set (γ × α)} {eq : γ → γ → Bool}
    (h : GEN_OP eq (fun a a' : α => decide (a = a')) (R →ᵣ R →ᵣ boolRel)) :
    (list_eq eq, (fun l l' : List α => decide (l = l'))) ∈
      listRel R →ᵣ listRel R →ᵣ boolRel := by
  simp only [autoref_tag_defs] at h
  rw [list_eq_expand]
  parametricity [autoref_list_eq_aux]

/-! ### Structural expansion and the `STRUCT_EQ` solver
(tool extract §8)

The extraction left the placement open — "should the Lean port's
structural-expansion mechanism live alongside the generic phase
machinery, or alongside the concrete HOL/nat/list bindings the way it
does upstream?". It lives here, where the source puts it. -/

/-- The source's `STRUCT_EQ_tag x y ≡ x = y`. -/
def STRUCT_EQ_tag {α : Sort u} (x y : α) : Prop := x = y

/-- The source's `STRUCT_EQ_tag` definition, with the source's own
`[simp]`. -/
@[simp] theorem STRUCT_EQ_tag_def {α : Sort u} (x y : α) :
    STRUCT_EQ_tag x y ↔ x = y := Iff.rfl

/-- The source's `STRUCT_EQ_tagI`. -/
theorem STRUCT_EQ_tagI {α : Sort u} {x y : α} (h : x = y) : STRUCT_EQ_tag x y := h

open Autoref in
/-- The source's `expand_tac`: `SOLVED' (asm_simp_tac ss)` where `ss` is
`HOL_basic_ss` plus exactly the `[autoref_struct_expand]` lemmas. -/
elab "autoref_expand" : tactic => Tactic.liftMetaTactic fun g => do
  let mut thms : SimpTheorems := {}
  for n in ← Lean.labelled `autoref_struct_expand do
    thms ← thms.addConst n
  let ctx ← Simp.mkContext {} (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  match ← simpGoal g ctx with
  | (none, _) => return []
  | (some (_, g'), _) => return [g']

section Solvers

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

-- The source's `STRUCT_EQ` solver, `Tagged_Solver.declare_solver
-- @{thms STRUCT_EQ_tagI} @{binding STRUCT_EQ} "Autoref: Equality modulo
-- structural expansion" expand_tac`.
declare_solver STRUCT_EQ for STRUCT_EQ_tag at 0
    with "Autoref: Equality modulo structural expansion" :=
  simp only [STRUCT_EQ_tag_def]
  autoref_expand
  try rfl

end Solvers

/-! ### Operation patterns (delta B1)

The source's `autoref_op_pat` shape, from `Simple_DFS.thy`:

```isabelle
context begin interpretation autoref_syn .
  lemma [autoref_op_pat]: "E``{v} ≡ op_succ$E$v" by simp
end
```

— raw surface pattern on the left, tagged operator application on the
right. Wave B2's `Autoref/Tagging.lean` made `$ᵃ` global notation
(its delta T3), so no locale interpretation is needed. -/

/-- Lean's `l ++ l'` is `HAppend.hAppend`, not `List.append`, and the
rule wave B1 proved is at `List.append` (delta B1). -/
@[autoref_op_pat] theorem append_pat {α : Type} (l l' : List α) :
    l ++ l' = (List.append $ᵃ l $ᵃ l') := rfl

/-- The source's elided `is_Nil_pat`: `a = []` is the `is_Nil`
operation (delta B1, B2). -/
@[autoref_op_pat] theorem is_Nil_pat {α : Type} (l : List α) [Decidable (l = [])] :
    decide (l = []) = (List.isEmpty $ᵃ l) := by
  rw [APP_def, Bool.eq_iff_iff, decide_eq_true_eq, List.isEmpty_iff]

/-- The source's elided `is_Nil_pat`, other way round: `[] = a` is the
`is_Nil` operation. This is the direction the tutorial's `[] = a` entry
takes (delta B1). -/
@[autoref_op_pat] theorem is_Nil_pat' {α : Type} (l : List α) [Decidable (([] : List α) = l)] :
    decide (([] : List α) = l) = (List.isEmpty $ᵃ l) := by
  rw [APP_def, Bool.eq_iff_iff, decide_eq_true_eq, List.isEmpty_iff, eq_comm]

/-- The source's elided `is_None_pat`: `a = None` is the `is_None`
operation (delta B1, B2). -/
@[autoref_op_pat] theorem is_None_pat {α : Type} (o : Option α) [Decidable (o = none)] :
    decide (o = none) = (Option.isNone $ᵃ o) := by
  rw [APP_def, Bool.eq_iff_iff, decide_eq_true_eq, Option.isNone_iff_eq_none]

/-- The source's elided `is_None_pat`, other way round (delta B1). -/
@[autoref_op_pat] theorem is_None_pat' {α : Type} (o : Option α)
    [Decidable ((none : Option α) = o)] :
    decide ((none : Option α) = o) = (Option.isNone $ᵃ o) := by
  rw [APP_def, Bool.eq_iff_iff, decide_eq_true_eq, Option.isNone_iff_eq_none, eq_comm]

/-! ### The executable gate (design record ledger D4)

Every operation pattern above is an equation between two `Bool`-valued
terms, so at concrete data it runs — and each was `#guard`-checked here
before it was proved (repo practice: refute before prove). The
`STRUCT_EQ` solver and the `[autoref_struct_expand]` tag get the one
exercise the acceptance file does not give them. -/

namespace Sanity

-- The registered pipeline is the source's, in the source's order. The
-- extract's headline finding was that there are *four* phases and not
-- three —
--
-- > `id_op` (priority 10) → `rel_inf` (20) → `fix_rel` (22) →
-- > `trans` (30) — one phase more than the task's suggested
-- > "id_ops → fix_rel → translate" framing
--
-- — so the registry is read back and compared. The check lives here
-- rather than in `Autoref/Tool.lean`, which registers the phases,
-- because Lean runs an `initialize` block at *import* time: the
-- registry is empty in the module that fills it and full in every
-- module downstream (`Autoref/Phases.lean` delta P4).
/-- info: id_op(10) → rel_inf(20) → fix_rel(22) → trans(30) -/
#guard_msgs in
#eval show CoreM Unit from do IO.println (← Autoref.phaseList)

-- `append_pat`, both sides.
#guard ([1, 2, 3] ++ [4] : List ℕ) == (List.append $ᵃ [1, 2, 3] $ᵃ [4])
#guard ([] ++ [4] : List ℕ) == (List.append $ᵃ [] $ᵃ [4])

-- `is_Nil_pat` / `is_Nil_pat'`, positive and negative.
#guard decide (([1, 2, 3] : List ℕ) = []) == (List.isEmpty $ᵃ [1, 2, 3])
#guard decide (([] : List ℕ) = []) == (List.isEmpty $ᵃ ([] : List ℕ))
#guard !decide (([1, 2, 3] : List ℕ) = [])
#guard decide (([] : List ℕ) = ([] : List ℕ)) == (List.isEmpty $ᵃ ([] : List ℕ))

-- `is_None_pat` / `is_None_pat'`, positive and negative.
#guard decide ((some 4 : Option ℕ) = none) == (Option.isNone $ᵃ (some 4 : Option ℕ))
#guard decide ((none : Option ℕ) = none) == (Option.isNone $ᵃ (none : Option ℕ))
#guard !decide ((some 4 : Option ℕ) = none)
#guard decide ((none : Option ℕ) = (none : Option ℕ)) == Option.isNone (none : Option ℕ)

-- The generic layer is `Id`-relatedness: equal, and only equal.
#guard ((decide ((2 : ℕ) = 2)), decide ((2 : ℕ) = 2)) ∈ boolRel
#guard ((4 : ℕ), (4 : ℕ)) ∈ Set.diagonal ℕ

-- `autoref_hd` at data: related lists have related heads, and the
-- `SIDE_PRECOND` is what rules out the empty case.
#guard List.headI [2, 4, 6] == 2
#guard (List.headI ([] : List ℕ)) == 0            -- the `Inhabited` default (delta B4)

-- `autoref_list_eq`'s conclusion at `Id`: `list_eq` with decidable
-- equality *is* equality.
#guard list_eq (fun a b : ℕ => decide (a = b)) [1, 2] [1, 2]
#guard !list_eq (fun a b : ℕ => decide (a = b)) [1, 2] [2, 3]

-- The `STRUCT_EQ` solver, through `tagged_solver`, on exactly the
-- mismatch the source's motivation describes: an operator that must be
-- recognised *modulo* structural expansion. This is what the
-- `[autoref_struct_expand]` tag on `list_eq_expand` buys (delta B6).
example : STRUCT_EQ_tag (fun l l' : List ℕ => decide (l = l'))
    (list_eq (fun a a' : ℕ => decide (a = a'))) := by
  tagged_solver

end Sanity

end Lax13Proofs.Refine
