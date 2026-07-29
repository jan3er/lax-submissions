import Lax13Proofs.Refine.Autoref.BindingsHOL

/-!
P2's acceptance: the tutorial's derivations, reproduced mechanically.

The target is the `subsection "Examples"` that closes
`thys/Automatic_Refinement/Autoref_Bindings_HOL.thy` of AFP
`Automatic_Refinement` (Lammich), at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 — AFP for Isabelle2025-2,
release 2026-02-06. The extraction's own recommendation
(`plans/word-ram/refinement-tower/p2-tutorial-extracts.md`, closing
section) picked it over `Simple_DFS.thy`:

> Target the `Autoref_Bindings_HOL.thy` §"Examples" list append entry […]
> it is the simplest possible non-trivial exercise of the full P2 spine —
> relator inference (`nat_rel`, `⟨nat_rel⟩list_rel`), operator
> identification and rule-DB lookup (`autoref_append`, `refine_list`'s
> `Nil`/`Cons`, `autoref_nat`'s numeral rules), and the phase pipeline,
> all in one `by autoref` call — while touching *zero* Collections data
> structures and *zero* Refine_Monadic determinization machinery.

The eight entries, verbatim from that section (extract §4):

```isabelle
subsection "Examples"

text ‹Be careful to make the concrete type a schematic type variable.
  The default behaviour of ‹schematic_lemma› makes it a fixed variable,
  that will not unify with the infered term!›
schematic_goal
  "(?f::?'c,[1,2,3]@[4::nat])∈?R"
  by autoref

schematic_goal
  "(?f::?'c,[1::nat,
    2,3,4,5,6,7,8,9,0,1,43,5,5,435,5,1,5,6,5,6,5,63,56
  ]
  )∈?R"
  apply (autoref)
  done

schematic_goal
  "(?f::?'c,[1,2,3] = [])∈?R"
  by autoref

text ‹
  When specifying custom refinement rules on the fly, be careful with
  the type-inference between ‹notes› and ‹shows›. It's
  too easy to ,,decouple'' the type ‹'a› in the autoref-rule and
  the actual goal, as shown below!
›

schematic_goal
  notes [autoref_rules] = IdI[where 'a="'a"]
  notes [autoref_itype] = itypeI[where 't="'a::numeral" and I=i_std]
  shows "(?f::?'c, hd [a,b,c::'a::numeral])∈?R"
  txt ‹The autoref-rule is bound with type ‹'a::typ›, while
    the goal statement has ‹'a::numeral›!›
  apply (autoref (keep_goal))
  txt ‹We get an unsolved goal, as it finds no rule to translate
    ‹a››
  oops

text ‹Here comes the correct version. Note the duplicate sort annotation
  of type ‹'a›:›
schematic_goal
  notes [autoref_rules_raw] = IdI[where 'a="'a::numeral"]
  notes [autoref_itype] = itypeI[where 't="'a::numeral" and I=i_std]
  shows "(?f::?'c, hd [a,b,c::'a::numeral])∈?R"
  by (autoref)

text ‹Special cases of equality: Note that we do not require equality
  on the element type!›
schematic_goal
  assumes [autoref_rules]: "(ai,a)∈⟨R⟩option_rel"
  shows "(?f::?'c, a = None)∈?R"
  apply (autoref (keep_goal))
  done

schematic_goal
  assumes [autoref_rules]: "(ai,a)∈⟨R⟩list_rel"
  shows "(?f::?'c, [] = a)∈?R"
  apply (autoref (keep_goal))
  done

schematic_goal
  shows "(?f::?'c, [1,2] = [2,3::nat])∈?R"
  apply (autoref (keep_goal))
  done
```

## The scorecard

| # | source entry | here | status |
|---|---|---|---|
| 1 | `[1,2,3]@[4::nat]` | `accept_append` | reproduced |
| 2 | the 24-element literal | `accept_literals` | reproduced |
| 3 | `[1,2,3] = []` | `accept_isNil_right` | reproduced |
| 4 | `hd [a,b,c]`, the *wrong* version (`oops`) | — | adapted: delta A3 |
| 5 | `hd [a,b,c]`, the correct version | `accept_hd` | adapted: delta A3 |
| 6 | `a = None` | `accept_isNone` | reproduced |
| 7 | `[] = a` | `accept_isNil_left` | reproduced |
| 8 | `[1,2] = [2,3::nat]` | `accept_listEq` | reproduced |

## Deltas

**A1 — `autoref_synth`, not `schematic_goal`.** `Autoref/Tool.lean`'s
delta O2 in full: Lean has no schematic goal at the top level of a
declaration, so the command elaborates the abstract term, runs the
pipeline against fresh `?γ`/`?c`/`?R` metavariables and *adds* the
resulting theorem — plus, when the concrete term is closed, a definition
holding it, which is the source's `concrete_definition`. The tactic
form, on the goal `refine ⟨?γ, ?c, ?R, ?main⟩` leaves behind, is
exercised at the bottom of this file so that both vehicles are on the
record; the command is what the entries use, because it is the form in
which the synthesized term can be `#guard`ed.

**A2 — `assumes [autoref_rules]` is a binder.** Entries 6 and 7 bind a
rule on the fly. `autoref_synth`'s binders become the theorem's binders,
and a binder of refinement shape `(h : (ai, a) ∈ ⟨R⟩option_rel)` is
picked up as an extra rule by the same local-context sweep the tactic
uses (`Autoref/Tool.lean` delta O1). That is the vehicle, and it is
flagged rather than silently substituted for an attribute.

**A3 — the two `hd` entries collapse into one, and the pitfall they
demonstrate has no Lean analogue.** Entries 4 and 5 are the *same*
derivation twice: the first fails and is `oops`ed, the second succeeds,
and the only difference is `[autoref_rules] = IdI[where 'a="'a"]` versus
`[autoref_rules_raw] = IdI[where 'a="'a::numeral"]` — an Isabelle
sort-annotation subtlety ("It's too easy to ,,decouple'' the type ‹'a›
in the autoref-rule and the actual goal"). Lean has no sorts on type
variables: a binder `{α : Type}` in an `autoref_synth` binder list *is*
the goal's `α`, and there is no second, silently different one to
decouple from. The failing entry therefore has nothing to reproduce; the
succeeding one is `accept_hd`, and this paragraph is the record of the
pitfall's absence — a substrate note, as the task asked, not an omission.

The extraction's finding about `i_std` (its Gaps section: "`i_std` […] is
**not declared anywhere** in `Automatic_Refinement` […] a bare
schematic/free term variable standing in for 'the standard/generic
interface'") is what makes this cheap. Both `hd` entries carry
`notes [autoref_itype] = itypeI[where 't="'a::numeral" and I=i_std]`,
and since `i_std` is a placeholder there is nothing to look up:
`Autoref/IdOps.lean`'s delta I5 assigns exactly `Interface.const "i_std"`
to a type its structural walk cannot decompose, which is what a type
variable `α` is. The annotation is therefore not *needed* here — the
interface it would declare is the one the walk produces anyway — and
`accept_hd` does without it.

**A4 — `IdI[of …]` becomes an explicit hypothesis.** The source's
`hd` entry binds `IdI` as a rule so that the free variables `a`, `b`,
`c` translate to themselves. Wave B1 deliberately left `IdI` untagged
(its own words: "its conclusion `(?a, ?a) ∈ Set.diagonal ?α` unifies
with any goal whose relation is still a metavariable, which is precisely
the mis-firing the source's head-constant rule indexing avoids"), so
`accept_hd` states it as a binder, which is exactly what `notes` does:
scope it to this one derivation.

**A5 — `keep_goal` on entries 6–8.** The source writes
`apply (autoref (keep_goal)); done` for the last three: `keep_goal` is
belt-and-braces there, since all three succeed (the `done` proves it).
The reproductions call the pipeline plainly and let a failure fail;
`keep_goal` itself is exercised once, at the bottom, on a derivation
that really does fail.
-/

namespace Lax13Proofs.Refine

namespace AutorefTutorial

open Autoref

-- A rule bound as a binder (delta A2) is consumed by the pipeline's
-- local-context sweep, not by any proof text, so the linter sees an
-- unused hypothesis. It is right about the text and wrong about the
-- file: deleting `h` breaks the derivation.
set_option linter.unusedVariables false

/-! ### Entry 1 — the recommended first target

```isabelle
schematic_goal "(?f::?'c,[1,2,3]@[4::nat])∈?R"  by autoref
```

`autoref_synth` adds `accept_append` (the theorem) and
`accept_append_impl` (the source's `concrete_definition`). Nothing else
is written: no rule is applied by hand, and the concrete term
`[1,2,3].append [4]` and the relator `⟨nat_rel⟩list_rel` are both the
pipeline's. -/

autoref_synth accept_append for ([1, 2, 3] ++ [4] : List ℕ)

/-- info: accept_append : ([1, 2, 3].append [4], [1, 2, 3] ++ [4]) ∈ listRel natRel -/
#guard_msgs in
#check @accept_append

/-! ### Entry 2 — the 24-element literal list

```isabelle
schematic_goal
  "(?f::?'c,[1::nat, 2,3,4,5,6,7,8,9,0,1,43,5,5,435,5,1,5,6,5,6,5,63,56])∈?R"
  apply (autoref) done
```
-/

autoref_synth accept_literals for
  ([1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 43, 5, 5, 435, 5, 1, 5, 6, 5, 6, 5, 63, 56] : List ℕ)

/-! ### Entry 3 — `[1,2,3] = []`, the `is_Nil` operation-pattern route

```isabelle
schematic_goal "(?f::?'c,[1,2,3] = [])∈?R"  by autoref
```

The `autoref_op_pat` net rewrites `[1,2,3] = []` into `is_Nil$[1,2,3]`
during `id_op`, *before* any relator-level rule is consulted, which is
why the synthesized term is `List.isEmpty` and not a list comparison
(`Autoref/BindingsHOL.lean` delta B1). -/

autoref_synth accept_isNil_right for (decide (([1, 2, 3] : List ℕ) = []))

/-- info: accept_isNil_right : ([1, 2, 3].isEmpty, decide ([1, 2, 3] = [])) ∈ boolRel -/
#guard_msgs in
#check @accept_isNil_right

/-! ### Entries 4 and 5 — `hd [a,b,c]`

```isabelle
schematic_goal
  notes [autoref_rules_raw] = IdI[where 'a="'a::numeral"]
  notes [autoref_itype] = itypeI[where 't="'a::numeral" and I=i_std]
  shows "(?f::?'c, hd [a,b,c::'a::numeral])∈?R"
  by (autoref)
```

Deltas A3 (the two entries collapse; the sort pitfall has no analogue;
`i_std` needs no declaration) and A4 (`IdI` as a binder). This is the
one entry whose rule carries a `SIDE_PRECOND`, so it is the one that
exercises the side-condition solver registry end to end: `autoref_hd`'s
`SIDE_PRECOND (l' ≠ [])` is manufactured by the `trans` phase, stripped
of its `PREFER`/`REMOVE_INTERNAL` tags, and dispatched through wave B2's
`tagged_solver` to the `PRECOND` solver, which discharges
`[a, b, c] ≠ []`. -/

autoref_synth accept_hd {α : Type} [Inhabited α] (a b c : α)
    (hId : ∀ x : α, (x, x) ∈ Set.diagonal α) for (List.headI [a, b, c])

/--
info: @accept_hd : ∀ {α : Type} [inst : Inhabited α] (a b c : α),
  (∀ (x : α), (x, x) ∈ Set.diagonal α) → ([a, b, c].headI, [a, b, c].headI) ∈ Set.diagonal α
-/
#guard_msgs in
#check @accept_hd

/-! ### Entry 6 — `a = None` under a locally bound rule

```isabelle
schematic_goal
  assumes [autoref_rules]: "(ai,a)∈⟨R⟩option_rel"
  shows "(?f::?'c, a = None)∈?R"
  apply (autoref (keep_goal)) done
```

Delta A2 for the binder. The source's own remark on this entry — "Note
that we do not require equality on the element type!" — survives
literally: `R` is an arbitrary relation, and the `Decidable` instance
Lean needs for `decide (a = none)` is `Option.decidableEqNone`, which
decides exactly this and asks nothing of `α`
(`Autoref/BindingsHOL.lean` delta B2). -/

autoref_synth accept_isNone {α γ : Type} {R : Set (γ × α)}
    (ai : Option γ) (a : Option α) (h : (ai, a) ∈ optionRel R)
    for (decide (a = none))

/--
info: @accept_isNone : ∀ {α γ : Type} {R : Set (γ × α)} (ai : Option γ) (a : Option α),
  (ai, a) ∈ optionRel R → (ai.isNone, decide (a = none)) ∈ boolRel
-/
#guard_msgs in
#check @accept_isNone

/-! ### Entry 7 — `[] = a`

```isabelle
schematic_goal
  assumes [autoref_rules]: "(ai,a)∈⟨R⟩list_rel"
  shows "(?f::?'c, [] = a)∈?R"
  apply (autoref (keep_goal)) done
```

The `is_Nil` pattern in its other direction (delta B1). -/

autoref_synth accept_isNil_left {α γ : Type} {R : Set (γ × α)}
    (ai : List γ) (a : List α) (h : (ai, a) ∈ listRel R)
    for (decide (([] : List α) = a))

/--
info: @accept_isNil_left : ∀ {α γ : Type} {R : Set (γ × α)} (ai : List γ) (a : List α),
  (ai, a) ∈ listRel R → (ai.isEmpty, decide ([] = a)) ∈ boolRel
-/
#guard_msgs in
#check @accept_isNil_left

/-! ### Entry 8 — `[1,2] = [2,3]`, the `GEN_OP` route

```isabelle
schematic_goal shows "(?f::?'c, [1,2] = [2,3::nat])∈?R"
  apply (autoref (keep_goal)) done
```

The heaviest of the eight, and the one that exercises the whole
side-condition architecture at once. Neither list is `[]`, so no
operation pattern fires and the operator reaching `fix_rel` is Lean's
`fun l l' : List ℕ => decide (l = l')`. Two rules match it: the generic
`autoref_gen_eq` at minor priority −10 (`PRIO_TAG_GEN_ALGO`) and
`autoref_list_eq` at the default (0,0). Priority decides, and
`autoref_list_eq` wins — which is exactly what the source's own
`PRIO_TAG_GEN_ALGO` comment promises ("Generic algorithm, considered to
be less efficient than default algorithm"). Its `GEN_OP eq (=) (R→R→Id)`
premise is then a `PREFER`-tagged side condition, dispatched through
`tagged_solver` to the `GEN_OP` solver, which re-enters the *translate*
phase to instantiate `eq := fun a b => decide (a = b)` from
`autoref_nat_eq`. The result is `list_eq`, not `decide (· = ·)`: the
priority mechanism and the generic-algorithm solver both did their
jobs. -/

autoref_synth accept_listEq for (decide (([1, 2] : List ℕ) = [2, 3]))

/--
info: accept_listEq : (list_eq (fun a b => decide (a = b)) [1, 2] [2, 3], decide ([1, 2] = [2, 3])) ∈ boolRel
-/
#guard_msgs in
#check @accept_listEq

/-! ### The executable gate (design record ledger D4)

Every closed entry synthesized a *definition* as well as a theorem
(delta A1), and every one of these examples is pure, so the D4 check is
available in its strongest form: the synthesized concrete term is
`#guard`ed to agree in value with the abstract term it refines. The
relators here are `⟨nat_rel⟩list_rel` and `bool_rel`, both identity
relations at their carriers, so agreement in value is exactly what the
synthesized theorem *says* — the `#guard`s are the computational
shadow of the theorems above, not a substitute for them.

Entries 5–7 carry free variables and synthesize no definition; their
statements are pinned by the `#check`s above instead, which is the
stronger check of the two (it names the concrete term *and* the
relator). -/

namespace Gate

-- Entry 1.
#guard accept_append_impl == ([1, 2, 3] ++ [4] : List ℕ)
#guard accept_append_impl == [1, 2, 3, 4]

-- Entry 2.
#guard accept_literals_impl ==
  ([1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 43, 5, 5, 435, 5, 1, 5, 6, 5, 6, 5, 63, 56] : List ℕ)

-- Entry 3: the `is_Nil` route computes the equality it replaced.
#guard accept_isNil_right_impl == decide (([1, 2, 3] : List ℕ) = [])
#guard accept_isNil_right_impl == false

-- Entry 8: the `list_eq` route likewise.
#guard accept_listEq_impl == decide (([1, 2] : List ℕ) = [2, 3])
#guard accept_listEq_impl == false

-- …and it is not vacuously false: `list_eq` says `true` when it should.
#guard list_eq (fun a b : ℕ => decide (a = b)) [1, 2] [1, 2] == decide (([1, 2] : List ℕ) = [1, 2])

-- Entries 5–7 at concrete data: the theorems instantiate, which is the
-- check that their *statements* are usable and not just well-formed.
example : (Option.isNone (some 4), decide ((some 2 : Option ℕ) = none)) ∈ boolRel :=
  accept_isNone (R := Sanity.halfRel) (some 4) (some 2)
    (mem_optionRel_some_some.mpr (Sanity.halfB_eq 4 2 |>.mp rfl))

example : (List.isEmpty [2, 4], decide (([] : List ℕ) = [1, 2])) ∈ boolRel :=
  accept_isNil_left (R := Sanity.halfRel) [2, 4] [1, 2]
    (Sanity.listHalf_eq [2, 4] [1, 2] |>.mp rfl)

example : (List.headI [1, 2, 3], List.headI [1, 2, 3]) ∈ Set.diagonal ℕ :=
  accept_hd 1 2 3 (fun _ => rfl)

end Gate

/-! ### The tactic vehicle

`autoref_synth` is the acceptance vehicle (delta A1); the tactic is the
other half of the source's `apply (autoref …)`, on the goal a
`refine ⟨?γ, ?c, ?R, ?main⟩` against
`∃ (γ : Type) (c : γ) (R : Set (γ × α)), (c, a) ∈ R` leaves behind —
Lean's honest rendering of `(?f::?'c, a) ∈ ?R`, schematic concrete type
and all. -/

example : ∃ (γ : Type) (c : γ) (R : Set (γ × List ℕ)), (c, [1, 2, 3] ++ [4]) ∈ R := by
  refine ⟨?γ, ?c, ?R, ?main⟩
  case main => autoref

-- The source's `phases: …` argument, restricting the run to a prefix.
-- All four phases named is the same as naming none.
example : ∃ (γ : Type) (c : γ) (R : Set (γ × List ℕ)), (c, [1, 2, 3] ++ [4]) ∈ R := by
  refine ⟨?γ, ?c, ?R, ?main⟩
  case main => autoref phases: id_op rel_inf fix_rel trans

-- Local refinement hypotheses are rules, without being named (delta O1).
example {α γ : Type} {R : Set (γ × α)} (ai : Option γ) (a : Option α)
    (h : (ai, a) ∈ optionRel R) :
    ∃ (δ : Type) (c : δ) (S : Set (δ × Bool)), (c, decide (a = none)) ∈ S := by
  refine ⟨?δ, ?c, ?S, ?main⟩
  case main => autoref

/-! ### The trace

The source's `apply (autoref (trace))` (`Simple_DFS.thy`, tutorial
extract §2.4), on the smallest possible derivation so that the whole
trace fits in a checked message. Each phase reports what it did, in the
source's own vocabulary — `CONSTRAINT f R` for `fix_rel`, the rule that
solved it, the rule that translated each subterm — and the flag also
prints the two things the caller wanted, the concrete term and its
relator. This is the telemetry the phase record asks for: it names, per
example, which database each step consulted. -/

set_option pp.mvars false in
/--
info: id_op: 4 ⤳ ANNOT (OP 4) (i_annot (Interface.const "i_nat")) : i_nat
---
info: phase 'id_op' (priority 10) succeeded
---
info: rel_inf: ANNOT (OP 4) (rel_annot natRel)
---
info: phase 'rel_inf' (priority 20) succeeded
---
info: fix_rel: CONSTRAINT 4 natRel solved by Lax13Proofs.Refine.autoref_nat_lit
---
info: phase 'fix_rel' (priority 22) succeeded
---
info: trans: ANNOT (OP 4) (rel_annot natRel) by Lax13Proofs.Refine.autoref_nat_lit
---
info: phase 'trans' (priority 30) succeeded
---
info: autoref_synth Lax13Proofs.Refine.AutorefTutorial.accept_trace:
  concrete
  4
  relator
  natRel
-/
#guard_msgs in
autoref_synth (trace) accept_trace for ((4 : ℕ))

/-! ### Negative controls (design record ledger D4)

Two derivations the pipeline must *fail* on, with the failure messages
checked verbatim. The plan's supervision-legibility watch item is what
these check: every pipeline failure names its phase and its unmet side
condition.

`pp.mvars` is turned off so that the checked text does not depend on
metavariable numbering, which is an artefact of elaboration order rather
than of the pipeline. -/

set_option pp.mvars false in
/--
error: autoref: phase 'fix_rel' (priority 22) failed.
no rule fixes the relator of the operator
  "a"
at the relator
  ?_
26 rules were considered (26 of them in the autoref_rules database, 0 supplied at the call site); 0 match the operator but not the relator: (none)
goal at this phase:
  (?_, ANNOT (OP "a") (rel_annot ?_)) ∈ ?_
-/
#guard_msgs in
autoref_synth nc_no_rule for ("a" : String)

set_option pp.mvars false in
/--
error: autoref: phase 'trans' (priority 30) failed.
cannot translate the term
  ANNOT (OP List.headI) (rel_annot (listRel ?_ →ᵣ ?_))
at the relator
  ?_ →ᵣ ?_
no rule's conclusion matched it.
Side conditions that went unmet along the way:
Lax13Proofs.Refine.autoref_hd: tagged_solver: the highest-priority solver for tag 'Lax13Proofs.Refine.PRECOND_tag' failed; candidates in priority order: PRECOND (priority 0); 'tagged_solver_full' would try the rest. The solver failed with: tagged_solver: solver PRECOND (priority 0) ran on tag 'Lax13Proofs.Refine.PRECOND_tag' but did not close the goal; use 'tagged_solver_step' to keep what it produced
(26 rules were available: 0 from the call site, 26 from the autoref_rules databases)
-/
#guard_msgs in
autoref_synth nc_side_condition for (List.headI ([] : List ℕ))

/-! ### `keep_goal`

The source's `apply (autoref (keep_goal))` leaves an inspectable goal
instead of failing (`Autoref/Tool.lean` delta O3). Here the relator is
pinned to `Id` on lists of `String`, for which no `autoref_append` rule
can apply; the pipeline reports, rolls back, and hands the goal to the
caller, who closes it by hand. -/

set_option pp.mvars false in
set_option linter.unusedTactic false in
/--
info: autoref: phase 'fix_rel' (priority 22) failed.
no rule fixes the relator of the operator
  List.append
at the relator
  ?_ →ᵣ ?_ →ᵣ Set.diagonal (List String)
26 rules were considered (26 of them in the autoref_rules database, 0 supplied at the call site); 1 match the operator but not the relator: Lax13Proofs.Refine.autoref_append
goal at this phase:
  (["a"] ++ ["b"],
      ANNOT (OP List.append) (rel_annot (?_ →ᵣ ?_ →ᵣ Set.diagonal (List String))) $ᵃ
          (ANNOT (OP List.cons) (rel_annot (?_ →ᵣ ?_ →ᵣ ?_)) $ᵃ ANNOT (OP "a") (rel_annot ?_) $ᵃ
            ANNOT (OP []) (rel_annot ?_)) $ᵃ
        (ANNOT (OP List.cons) (rel_annot (?_ →ᵣ ?_ →ᵣ ?_)) $ᵃ ANNOT (OP "b") (rel_annot ?_) $ᵃ
          ANNOT (OP []) (rel_annot ?_))) ∈
    Set.diagonal (List String)
-/
#guard_msgs in
example : ∃ (γ : Type) (c : γ) (R : Set (γ × List String)), (c, ["a"] ++ ["b"]) ∈ R := by
  refine ⟨List String, ["a"] ++ ["b"], Set.diagonal (List String), ?main⟩
  case main =>
    autoref (keep_goal)
    exact rfl

end AutorefTutorial

end Lax13Proofs.Refine
