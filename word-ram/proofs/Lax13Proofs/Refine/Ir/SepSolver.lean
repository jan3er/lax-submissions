import Lax13Proofs.Refine.Ir.Attrs
import Lax13Proofs.Refine.Ir.Triples

/-!
Frame inference: the `ENTAILS` / `FRAME` / `FRAME_INFER` calculus and its
solver.

Port of `thys/lib/Frame_Infer.thy` at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 (`isabelle_llvm_time` @
`42dd7f5`), quoted verbatim in
`plans/word-ram/refinement-tower/p3-sl-deep-extracts.md` §2 — the tags,
the four structural rules, the three rule databases, and the
`start / round / end` search loop; plus, from §3 of the same extract,
the one rule that connects a Hoare triple to frame inference
(`htriple_vcg_frame_erule`).

The extract's own summary of the calculus is the specification this file
is measured against:

```isabelle
definition "FRI_END ≡ □"
definition "FRAME_INFER P Qs F ≡ P ⊢ Qs ** F"
definition "FRAME P Q F ≡ P ⊢ Q ** F"
definition "ENTAILS P Q ≡ P ⊢ Q"
definition "is_sep_red P' Q' P Q ≡ ∀Ps Qs. (P'**Ps⊢Q'**Qs) ⟶ (P**Ps⊢Q**Qs)"

lemma fri_prepare:   "FRAME_INFER Ps (Qs**FRI_END) F ⟹ FRAME_INFER Ps Qs F"
lemma fri_end:       "Ps ⊢ F ⟹ FRAME_INFER Ps FRI_END F"
lemma fri_step_rl:   "⟦P ⊢ Q; FRAME_INFER Ps Qs F⟧ ⟹ FRAME_INFER (P**Ps) (Q**Qs) F"
lemma fri_reduce_rl: "⟦is_sep_red P' Q' P Q; FRAME_INFER (P'**Ps) (Q'**Qs) F⟧
                        ⟹ FRAME_INFER (P**Ps) (Q**Qs) F"
lemma fri_startI:
  "⟦pure_part P ⟹ FRAME_INFER P Q F⟧ ⟹ FRAME P Q F"
  "⟦pure_part P ⟹ FRAME_INFER P Q □⟧ ⟹ ENTAILS P Q"
```

"these four ARE the whole calculus of frame inference; everything else
is search control" — the extract's words, and the reason this file is
short on lemmas and long on tactic.

Wave B left the *calculus half* of frame inference in place (`⊢` and its
lemma block, `conj_entails_mono`, `sepConj_assoc/comm/left_comm`,
`credits_add`, `GC_absorb`, `entails_GC`, `empty_ent_GC`); everything
above is new here, and so is every step lemma the search loop resolves
against. Nothing in `Assn.lean` / `Wp.lean` / `Triples.lean` is modified.

## The search loop, as implemented

The source's ML (`structure Frame_Infer`, described structurally in the
extract, not quoted — it is search control) is four tactics:
`start_tac`, `round_tac` (`start_round_tac` → `rotations_tac` →
`solve_round_tac`), `end_tac`, and `infer_tac = start_tac THEN repeat
(end_tac ORELSE round_tac)`. The port keeps that decomposition:

* **start** — dispatch on the goal's tag (`FRAME`, `ENTAILS`, a bare
  `⊢`, or an already-open `FRAME_INFER`) through `fri_startI_frame` /
  `fri_startI_entails`; normalize both sides with the
  `fri_prepare_simps` set; apply `fri_prepare`, which parks `FRI_END`
  at the end of the target list. After this phase both sides are
  `∗`-lists in a known normal form: right-nested, `□`-free, compound
  credit assertions split into atoms, the premise list terminated by
  `□` and the target list by `FRI_END`.
* **extract** — the source's `fri_extract`: every `⌜Φ⌝` conjunct of the
  premise becomes a hypothesis of the goal, so the facts an assertion
  carries are available to the side-condition solver and are not left
  over at the end (judgment call D-ac).
* **round** — look at the leading target conjunct and consume it
  against exactly one premise conjunct (`fri_step_rl`) or reduce the
  pair (`fri_reduce_rl`). Which premise conjunct is decided by a scan
  over the premise list, first match wins; the chosen conjunct is
  brought to the front by a permutation equality fed through
  `fri_prems_cong`, which is this port's rendering of the source's
  `rotations_tac` (judgment call D-y).
* **end** — the target list is down to `FRI_END`; `fri_end` turns the
  goal into `Ps ⊢ F`, `entails_refl` is tried first (the source's one
  hard-coded priority — it is what *instantiates the frame*), then the
  `fri_end_rules` database.

There is no higher-order unification anywhere: every match is a
first-order `isDefEq` between two conjuncts, exactly as in the source,
which is why `design.md`'s P3 row judged this algorithm portable under
Lean's weaker HOU.

## Judgment calls

**D-y — rotation is replaced by index selection; the search order is
unchanged.** The source brings a premise conjunct to the front by
cycling the whole `∗`-list through a `sep_conj_commute` /
`sep_conj_assoc` rewriting loop under the `fri_prems_cong` congruence,
and tries the registered rules at each rotation. Ours computes the list
once, scans it, and — having chosen index `k` — builds *one*
permutation equality `P₁ ∗ … ∗ Pₙ = P_k ∗ (the rest, in order)` from
`sepConj_left_comm`, then feeds it through the same `fri_prems_cong`.
The permutation group, the candidate order (premise index outer, rule
inner) and the first-match-wins rule are the source's; what changes is
that a selection costs `k` rewrites instead of a full rotation sweep
costing `O(n²)`, and that the list is never re-parsed between rounds.
The alternative — a literal rotation loop — was rejected because in Lean
each rotation would have to re-associate the whole list, and the
quadratic term is paid on *every* round, not once.

**D-z — the step set is a database with one member,
`entails_refl`.** The source's `fri_rules` is populated by the rules
that consume a points-to conjunct against a *differently shaped* target
conjunct — an `ll_range` opened at one index, an `ll_pto` under a
`dr_assn` wrapper. Judgment call D-m of `Assn.lean` removed exactly that
possibility from our assertion language: `a ↦ₐ xs` owns one indivisible
named cell, so a target conjunct is matched by a premise conjunct if and
only if the two are the same assertion. The database, the attribute and
the `fri_step_rl` plumbing are ported in full, and the solver enumerates
`fri_rules` after `entails_refl` on every candidate pair — there is
simply nothing else to register *yet*. P4's `hn_refine` layer is the
first consumer with a reason to add to it.

**D-aa — credit matching is numeral arithmetic, not a reduction
search.** Matching `¤¤n k` (wanted) against `¤¤n j` (held) needs
`j = k + l` or `k = j + l`, which is arithmetic on the two literals, not
unification. The source's mechanism for "consume part of a conjunct and
leave the rest" is `is_sep_red`/`fri_reduce_rl`, so that is what the two
splittings are *stated* as (`isSepRed_costCredits_ge` /
`_le`, registered `@[fri_red_rules]`), and `fri_credit_ge` /
`fri_credit_le` are the derived one-step forms the loop applies, with
the numeral supplied by the tactic and the side condition closed by
`rfl`. Compound credit assertions (`¤(a + b)`, `¤(k • c)`) are split
in the *prepare* phase instead, by `fri_prepare_simps`, which is where
the source puts its own `$`-splitting rules.

**D-ab — `GC` is processed last and absorbs greedily.** The source's
`fri_end_rules` carries `empty_ent_GC`, `entails_GC` and the
credit-absorption rule `$c ** P ⊢ GC`, so leftover credits are swallowed
by a trailing `GC` *at the end of the match*. Ours does the same job one
phase earlier, in the round loop: a `GC` target conjunct is sorted to
the back of the target list during prepare, and when it is reached it
absorbs every credit conjunct (and every other `GC`) left in the premise
before being discharged by `fri_gc_end`. The reason is that our `GC`
(`SND sepTrue`, `Assn.lean`) absorbs *credits only* — it cannot hold a
cell — so "absorb what is absorbable, then close" is a complete and
deterministic rule, whereas leaving it to `fri_end` would make the
frame-instantiating `entails_refl` and the GC rules compete for the same
goal. The `fri_end_rules` database is populated with the source's
members regardless, and `end` still consults it.

**D-ac — pure conjuncts: the premise's are extracted, the target's are
deferred.** The source treats the two sides differently and so does
this port. A `⌜Φ⌝` on the *premise* side is pulled into the goal's
context before matching begins (`fri_extract_pure`, the source's
`fri_extract`), which is what makes the facts an invariant carries —
`⌜k ≤ n⌝`, an index bound — available to everything downstream; the
acceptance file's loop invariant depends on exactly this. A `⌜Φ⌝` on the
*target* side is discharged by `fri_pure`, whose side goal `Φ` goes to a
fixed side tactic (`assumption`, `rfl`, `trivial`, `omega`, `decide`,
`simp`). What that tactic does not close is *handed back as a goal*,
which is the source's `SOLVE_AUTO_DEFER` discipline ("the solver does
not fail silently, it stalls visibly") rather than a failure. What is
*not* ported is the source's `PRECOND` tagging and its solver registry:
the side tactic is a fixed list, not a dispatch table, because P3 has
one shape of side condition and P4's driver is where a table belongs.
`fri_startI`'s `pure_part P` hypothesis is supplied exactly as in the
source and, as there, is not itself consumed — the extraction is done
conjunct by conjunct instead, which is strictly more informative.

**D-ad — `aget_rule_pure`'s registration is the `vcg_rules` database,
and `aset_rule_pure` is added to match.** Wave B's D-u left the array
rules with their index bound as a Lean hypothesis and stated
`aget_rule_pure` as the source-shaped variant with `⌜k < xs.length⌝` as
a precondition conjunct, "the form wave C will register". Both pure
forms are tagged `@[vcg_rules]` here (`Basic_VCG.thy`'s own database
name), together with the credit-and-cells rules that need no side
condition, so P4 inherits a populated table. The bound is then
discharged *by this solver*, as a `⌜⌝` target conjunct — the acceptance
file exercises exactly that path.

**D-ae — the triple/frame connection lands here, not in P4.**
`htriple_vcg_frame_erule` (extract §3) is the rule that turns "prove
`wp c Q' s`" into a frame inference plus an entailment. Its *driver* is
P4's; but the acceptance programs need to apply a triple to a state the
triple does not exactly describe, so the rule itself is ported here in
its two triple-level forms, `irTriple_frame` and `irHtriple_frame`,
whose two side conditions are literally `FRAME P' P ?F` and
`ENTAILS (Q ∗ ?F) Q'` — one `fri` call each. That is the whole of the
VCG that wave C ports: no goal-form dispatcher, no `PRECOND` tags, no
priority table, no normalization loop.

**D-af — the entry point is named `fri`, and it serves both front
ends.** The source's user-facing method for frame inference is `fri`
(and its variants `fri_extract`, `fri_keep`); the `ENTAILS` front end
is not a separate method there either — it is the *same* solver, reached
because `fri_startI` has two clauses and the solver is registered for
both tags (extract §2's `add_solver (@{thms fri_startI}, …)`). So `fri`
here dispatches on the tag and `ir_entails` is a one-line alias kept for
readability at entailment goals. `fri_trace` is ours, following
`Autoref/Solver.lean`'s precedent: it reports a failure as an `info`
message instead of throwing, so the gate can pin the message text
without leaving a failing declaration in the environment.
-/

open Lean Elab Meta Tactic

namespace Lax13Proofs.Refine.Ir

/-! ## 1. The tags

`Frame_Infer.thy`'s four definitions, rendered the way
`Autoref/Tagging.lean` renders its tags: a plain `def` plus an
unfolding lemma, no axiom, no opaque constant. They are stated at the
same generality as the source's — any separation algebra — even though
every consumer in this file is at `Assn`. -/

section Tags

variable {α : Type} [Zero α] [Add α] [SepDisj α] [SepAlgebra α]

/-- The source's `FRI_END ≡ □`: the marker parked at the end of the
target list, so that "consumed so far / still to match" is visible in
the term itself. -/
def FRI_END : α → Prop := □

/-- The source's `FRAME_INFER P Qs F ≡ P ⊢ Qs ** F`: the solver's
working goal — `P` must cover `Qs`, and `F` is what is left over. -/
def FRAME_INFER (P Qs F : α → Prop) : Prop := P ⊢ Qs ∗ F

/-- The source's `FRAME P Q F ≡ P ⊢ Q ** F`: the tag a VCG attaches to
a frame side condition, with `F` schematic. -/
def FRAME (P Q F : α → Prop) : Prop := P ⊢ Q ∗ F

/-- The source's `ENTAILS P Q ≡ P ⊢ Q`: the tag for a plain entailment
side condition. -/
def ENTAILS (P Q : α → Prop) : Prop := P ⊢ Q

/-- The source's
`is_sep_red P' Q' P Q ≡ ∀Ps Qs. (P'**Ps⊢Q'**Qs) ⟶ (P**Ps⊢Q**Qs)` —
"if the smaller entailment holds for any residue, so does the bigger
one". -/
def IsSepRed (P' Q' P Q : α → Prop) : Prop :=
  ∀ Ps Qs : α → Prop, (P' ∗ Ps ⊢ Q' ∗ Qs) → (P ∗ Ps ⊢ Q ∗ Qs)

omit [Add α] [SepDisj α] [SepAlgebra α] in
@[simp] theorem FRI_END_def : (FRI_END : α → Prop) = □ := rfl

theorem FRAME_INFER_def (P Qs F : α → Prop) : FRAME_INFER P Qs F = (P ⊢ Qs ∗ F) := rfl

theorem FRAME_def (P Q F : α → Prop) : FRAME P Q F = (P ⊢ Q ∗ F) := rfl

omit [Zero α] [Add α] [SepDisj α] [SepAlgebra α] in
theorem ENTAILS_def (P Q : α → Prop) : ENTAILS P Q = (P ⊢ Q) := rfl

theorem IsSepRed_def (P' Q' P Q : α → Prop) :
    IsSepRed P' Q' P Q = ∀ Ps Qs : α → Prop, (P' ∗ Ps ⊢ Q' ∗ Qs) → (P ∗ Ps ⊢ Q ∗ Qs) := rfl

/-- The source's `is_sep_redD`. -/
theorem IsSepRed.dest {P' Q' P Q : α → Prop} (h : IsSepRed P' Q' P Q) (Ps Qs : α → Prop)
    (h' : P' ∗ Ps ⊢ Q' ∗ Qs) : P ∗ Ps ⊢ Q ∗ Qs := h Ps Qs h'

end Tags

/-! ## 2. The calculus

`fri_prepare`, `fri_end`, `fri_step_rl`, `fri_reduce_rl`, `fri_startI` —
the four structural rules and the two entry rules, and nothing else.
Everything in §3 is derived from these. -/

section Calculus

variable {α : Type} [Zero α] [Add α] [SepDisj α] [SepAlgebra α]
variable {P Q P' Q' Ps Ps' Qs Qs' F : α → Prop}

/-- The source's `fri_prepare`: park `FRI_END` at the end of the target
list. -/
theorem fri_prepare (h : FRAME_INFER Ps (Qs ∗ FRI_END) F) : FRAME_INFER Ps Qs F := by
  rw [FRI_END_def, sepConj_emp] at h
  exact h

/-- The source's `fri_prepare_round`: prepend a `□` to the premise list,
so that a rule with nothing to consume still has something to match. -/
theorem fri_prepare_round (h : FRAME_INFER (□ ∗ Ps) Qs F) : FRAME_INFER Ps Qs F := by
  rwa [emp_sepConj] at h

/-- The source's `fri_end`: the target list is exhausted, so whatever is
left of the premise must be the frame. -/
theorem fri_end (h : Ps ⊢ F) : FRAME_INFER Ps FRI_END F := by
  rw [FRAME_INFER_def, FRI_END_def, emp_sepConj]
  exact h

/-- The source's `fri_step_rl`: consume one premise conjunct against one
target conjunct, justified by a `fri_rules` member. -/
theorem fri_step_rl (h1 : P ⊢ Q) (h2 : FRAME_INFER Ps Qs F) :
    FRAME_INFER (P ∗ Ps) (Q ∗ Qs) F := by
  rw [FRAME_INFER_def, sepConj_assoc]
  exact conj_entails_mono h1 h2

/-- The source's `fri_reduce_rl`: rewrite one premise/target conjunct
pair into a smaller one, justified by a `fri_red_rules` member. -/
theorem fri_reduce_rl (h1 : IsSepRed P' Q' P Q) (h2 : FRAME_INFER (P' ∗ Ps) (Q' ∗ Qs) F) :
    FRAME_INFER (P ∗ Ps) (Q ∗ Qs) F := by
  rw [FRAME_INFER_def, sepConj_assoc] at h2 ⊢
  exact h1.dest Ps (Qs ∗ F) h2

/-- The source's `fri_startI`, first clause. -/
theorem fri_startI_frame (h : purePart P → FRAME_INFER P Q F) : FRAME P Q F :=
  entails_pureI h

/-- The source's `fri_startI`, second clause. -/
theorem fri_startI_entails (h : purePart P → FRAME_INFER P Q (□ : α → Prop)) : ENTAILS P Q := by
  refine entails_pureI (fun hp => ?_)
  have h' := h hp
  rw [FRAME_INFER_def, sepConj_emp] at h'
  exact h'

/-- The source's `fri_prems_cong`: rewrite the premise list. This is
what the search loop's permutation equalities are fed through. -/
theorem fri_prems_cong (h : Ps = Ps') (h2 : FRAME_INFER Ps' Qs F) : FRAME_INFER Ps Qs F := by
  rw [h]; exact h2

omit [Zero α] [Add α] [SepDisj α] [SepAlgebra α] in
/-- Rewrite the premise of a bare entailment: what the end phase uses to
strip the premise list's terminating `□` before matching it against a
frame the caller supplied. -/
theorem entails_congr_left (h : Ps = Ps') (h2 : Ps' ⊢ F) : Ps ⊢ F := by
  rw [h]; exact h2

/-- The target-side companion of `fri_prems_cong`. -/
theorem fri_target_cong (h : Qs = Qs') (h2 : FRAME_INFER Ps Qs' F) : FRAME_INFER Ps Qs F := by
  rw [h]; exact h2

/-- Congruence under a leading conjunct: the recursion step of every
permutation equality the solver builds. -/
theorem sep_congr_right (A : α → Prop) {B B' : α → Prop} (h : B = B') : A ∗ B = A ∗ B' := by
  rw [h]

/-- The mirror of `sep_congr_right`; kept for symmetry with the source's
`fri_prems_cong` pair. -/
theorem sep_congr_left {A A' : α → Prop} (B : α → Prop) (h : A = A') : A ∗ B = A' ∗ B := by
  rw [h]

end Calculus

/-! ## 3. The rule databases

The source's three `named_theorems`, populated. `entails_refl` heads the
step set (judgment call D-z); the end set is the source's own list. -/

attribute [fri_rules] entails_refl

attribute [fri_end_rules] entails_true empty_ent_GC entails_GC

/-! ### The step rules the loop applies directly

Each is `fri_step_rl` or `fri_reduce_rl` at a fixed instantiation, with
the instantiation's side condition already discharged — the shape the
tactic can `mkAppM` without leaving a metavariable behind. -/

section Steps

variable {α : Type} [Zero α] [Add α] [SepDisj α] [SepAlgebra α]

/-- `fri_step_rl` at `entails_refl`: the match that closes almost every
round (judgment call D-z). -/
theorem fri_step_refl {P Ps Qs F : α → Prop} (h : FRAME_INFER Ps Qs F) :
    FRAME_INFER (P ∗ Ps) (P ∗ Qs) F :=
  fri_step_rl (entails_refl P) h

/-- A pure target conjunct owns nothing, so it is discharged by its
proposition alone and consumes no premise conjunct — the reason the
source prepends a `□` to the premise list each round
(`fri_prepare_round`). -/
theorem fri_pure {Φ : Prop} {Ps Qs F : α → Prop} (hΦ : Φ) (h : FRAME_INFER Ps Qs F) :
    FRAME_INFER Ps (⌜Φ⌝ ∗ Qs) F := by
  have e : (⌜Φ⌝ : α → Prop) = □ := by
    funext s; exact propext ⟨fun hs => hs.2, fun hs => ⟨hΦ, hs⟩⟩
  rw [e, emp_sepConj]
  exact h

/-- The source's `fri_extract`: a pure conjunct of the premise is a
*hypothesis* of the whole frame inference, not something to be matched.
Extracting it is what makes the pure facts an assertion carries
available to the side-condition solver (judgment call D-ac). -/
theorem fri_extract_pure {Φ : Prop} {Ps Qs F : α → Prop} (h : Φ → FRAME_INFER Ps Qs F) :
    FRAME_INFER (⌜Φ⌝ ∗ Ps) Qs F := by
  intro s hs
  have hs' := predLift_sepConj_iff.1 hs
  exact h hs'.1 s hs'.2

end Steps

/-! ### `GC`

Judgment call D-ab: a `GC` target conjunct absorbs every absorbable
premise conjunct and is then discharged. `GC` is `SND sepTrue`
(`Assn.lean`), so "absorbable" is exactly "owns no cell": a credit
assertion, or another `GC`. -/

/-- `GC` swallows a `GC` sitting under it: the source's `GC_absorb`, in
the shape the absorption loop consumes. -/
theorem GC_sepConj_GC_left (X : Assn) : GC ∗ (GC ∗ X) = GC ∗ X := by
  rw [← sepConj_assoc, GC_absorb]

/-- One absorption step, at an arbitrary justification `A ⊢ GC`. -/
theorem fri_gc_absorb_of {A : Assn} (hA : A ⊢ GC) {Ps Qs F : Assn}
    (h : FRAME_INFER Ps (GC ∗ Qs) F) : FRAME_INFER (A ∗ Ps) (GC ∗ Qs) F := by
  rw [FRAME_INFER_def, sepConj_assoc] at h ⊢
  refine entails_trans (conj_entails_mono hA h) ?_
  rw [GC_sepConj_GC_left]

/-- Absorb a credit conjunct into the target's `GC` — the source's
credit-absorption `fri_end_rules` member, applied one phase earlier. -/
theorem fri_gc_absorb_credits {c : ECost} {Ps Qs F : Assn}
    (h : FRAME_INFER Ps (GC ∗ Qs) F) : FRAME_INFER ((¤c) ∗ Ps) (GC ∗ Qs) F :=
  fri_gc_absorb_of (entails_GC c) h

/-- Absorb a `GC` conjunct into the target's `GC`. -/
theorem fri_gc_absorb_gc {Ps Qs F : Assn} (h : FRAME_INFER Ps (GC ∗ Qs) F) :
    FRAME_INFER (GC ∗ Ps) (GC ∗ Qs) F :=
  fri_gc_absorb_of (entails_refl GC) h

/-- Discharge the target's `GC` once nothing absorbable is left: the
source's `empty_ent_GC`, as a round step. -/
theorem fri_gc_end {Ps Qs F : Assn} (h : FRAME_INFER Ps Qs F) : FRAME_INFER Ps (GC ∗ Qs) F := by
  rw [FRAME_INFER_def, sepConj_assoc]
  refine entails_trans h ?_
  have hm : (□ : Assn) ∗ (Qs ∗ F) ⊢ GC ∗ (Qs ∗ F) :=
    conj_entails_mono empty_ent_GC (entails_refl _)
  rwa [emp_sepConj] at hm

/-- A priced credit assertion is absorbed by `GC`: `entails_GC` at the
`¤¤` spelling, which is the form every op triple is priced in. -/
theorem costCredits_entails_GC (n : String) (k : ℕ) : (¤¤n k) ⊢ GC := entails_GC _

/-- `GC` absorbs itself. -/
theorem GC_entails_GC : (GC : Assn) ⊢ GC := entails_refl GC

/-- `GC` really does absorb only credits: it does not entail, and is not
entailed by, ownership of a cell. The negative control behind D-ab. -/
theorem ptoVar_not_entails_GC (x : String) (v : Val) : ¬ ((x ↦ᵥ v) ⊢ GC) := by
  intro h
  have hs : (x ↦ᵥ v) ((Cells.single x v, 0, 0), 0) := ⟨⟨rfl, rfl⟩, rfl⟩
  have hc : (Cells.single x v, ((0 : Cells (List Val)), (0 : HCells))) = 0 := (h _ hs).1
  have hx := congrFun (congrArg Prod.fst hc) x
  simp [Cells.single] at hx

/-! ### Credits (judgment call D-aa)

The two splittings, first as `is_sep_red` facts — the source's mechanism
for "consume part of a conjunct" — and then as the one-step forms the
loop applies. -/

/-- Splitting one currency's credits by a numeral. -/
theorem costCredits_add (n : String) (j k : ℕ) : (¤¤n (j + k) : Assn) = ¤¤n j ∗ ¤¤n k := by
  rw [costCredits_def, costCredits_def, costCredits_def, ← credits_add, ACost.cost_add_cost]
  congr 1

/-- Splitting a credit bundle taken `j + 1` times: what a loop invariant
carrying `k • payload` is split by, one iteration at a time. -/
theorem credits_nsmul_succ (c : ECost) (j : ℕ) : (¤((j + 1) • c) : Assn) = ¤c ∗ ¤(j • c) := by
  rw [← credits_add]
  congr 1
  rw [succ_nsmul']

/-- The source's `is_sep_red` at "the premise holds more of a currency
than the target wants". -/
theorem isSepRed_costCredits_ge (n : String) (k l : ℕ) :
    IsSepRed (¤¤n l) (□ : Assn) (¤¤n (k + l)) (¤¤n k) := by
  intro Ps Qs h
  rw [costCredits_add, sepConj_assoc]
  refine conj_entails_mono (entails_refl _) (entails_trans h ?_)
  rw [emp_sepConj]

/-- The source's `is_sep_red` at "the target wants more of a currency
than the premise holds". -/
theorem isSepRed_costCredits_le (n : String) (j l : ℕ) :
    IsSepRed (□ : Assn) (¤¤n l) (¤¤n j) (¤¤n (j + l)) := by
  intro Ps Qs h
  rw [costCredits_add, sepConj_assoc]
  refine conj_entails_mono (entails_refl _) ?_
  rwa [emp_sepConj] at h

attribute [fri_red_rules] isSepRed_costCredits_ge isSepRed_costCredits_le

/-- The one-step form of `isSepRed_costCredits_ge`: the target wants
`k`, the premise holds `j = k + l`, and `l` stays behind. -/
theorem fri_credit_ge {n : String} {j k l : ℕ} (hj : j = k + l) {Ps Qs F : Assn}
    (h : FRAME_INFER (¤¤n l ∗ Ps) Qs F) : FRAME_INFER (¤¤n j ∗ Ps) (¤¤n k ∗ Qs) F := by
  subst hj
  rw [costCredits_add n k l, sepConj_assoc (¤¤n k) (¤¤n l) Ps]
  exact fri_step_rl (entails_refl _) h

/-- The one-step form of `isSepRed_costCredits_le`: the premise holds
`j`, the target wants `k = j + l`, and `l` is still owed. -/
theorem fri_credit_le {n : String} {j k l : ℕ} (hk : k = j + l) {Ps Qs F : Assn}
    (h : FRAME_INFER Ps (¤¤n l ∗ Qs) F) : FRAME_INFER (¤¤n j ∗ Ps) (¤¤n k ∗ Qs) F := by
  subst hk
  rw [costCredits_add n j l, sepConj_assoc (¤¤n j) (¤¤n l) Qs]
  exact fri_step_rl (entails_refl _) h

/-! ### The prepare-phase normalizer

The source's `fri_prepare_simps`. Splitting a compound credit assertion
into atoms is what makes the round loop's job first-order: after this
set has run, every credit conjunct is a `¤¤n k` with `k` a numeral, or
an opaque `¤c` the loop can only match by `entails_refl`. -/

/-- …and the same bundle taken no times at all, which is what the loop
invariant is left holding when the measure reaches zero. -/
theorem credits_nsmul_zero (c : ECost) : (¤((0 : ℕ) • c) : Assn) = □ := by
  rw [zero_nsmul, credits_zero]

attribute [fri_prepare_simps] credits_add credits_zero credits_nsmul_succ credits_nsmul_zero
  costCredits_add
/-! ## 4. The tactic-facing rule forms

Every rule the solver applies, restated with *all* of its arguments
explicit and in a fixed order. The reason is mechanical, and worth
recording because it cost a debugging session: Lean's `mkAppM` elaborates
inside `withNewMCtxDepth`, so an application whose implicit arguments
must be recovered from a term mentioning the caller's *frame
metavariable* — which is the normal case here, since `FRAME P Q ?F` is
what a VCG hands the solver — fails whenever the goal itself is being
elaborated inside another (a `have … := by fri`, a `refine … ?_`). With
the arguments explicit there is no unification left to do: the solver
computes the premise and target lists itself, so it *knows* every
argument, and the only defeq check in the whole run is the final one in
`assignChecked`.

A second substrate note, same character, belongs next to it: `simp`
wraps a rewritten goal in `Expr.mdata`, and `getAppFnArgs` on an
unstripped goal reports *no head constant at all* — so every place this
solver dispatches on a head constant goes through `headArgs`, which
strips it first. Both notes are recorded rather than worked around
silently, in the style of P1's delta B7.

Each of these is its own rule of §2–§3 with nothing added. -/

section Explicit

variable {α : Type} [Zero α] [Add α] [SepDisj α] [SepAlgebra α]

/-- `sep_congr_right` with both sides explicit. -/
theorem friE_congr_right (A B B' : α → Prop) (h : B = B') : A ∗ B = A ∗ B' :=
  sep_congr_right A h

/-- `fri_prepare`, explicit. -/
theorem friE_prepare (Ps Qs F : α → Prop) (h : FRAME_INFER Ps (Qs ∗ FRI_END) F) :
    FRAME_INFER Ps Qs F := fri_prepare h

/-- `fri_prems_cong`, explicit. -/
theorem friE_prems_cong (Ps Ps' Qs F : α → Prop) (h : Ps = Ps')
    (h2 : FRAME_INFER Ps' Qs F) : FRAME_INFER Ps Qs F := fri_prems_cong h h2

/-- `fri_target_cong`, explicit. -/
theorem friE_target_cong (Ps Qs Qs' F : α → Prop) (h : Qs = Qs')
    (h2 : FRAME_INFER Ps Qs' F) : FRAME_INFER Ps Qs F := fri_target_cong h h2

/-- `fri_step_rl`, explicit. -/
theorem friE_step (P Q Ps Qs F : α → Prop) (h1 : P ⊢ Q) (h2 : FRAME_INFER Ps Qs F) :
    FRAME_INFER (P ∗ Ps) (Q ∗ Qs) F := fri_step_rl h1 h2

/-- `fri_end`, explicit. -/
theorem friE_end (Ps F : α → Prop) (h : Ps ⊢ F) : FRAME_INFER Ps FRI_END F := fri_end h

set_option linter.unusedSectionVars false in
/-- `entails_congr_left`, explicit. The carrier's four instances are
carried even though the statement does not need them, so that this
constant has the same five-argument prefix as every other `friE_` rule
and the solver can build it with one code path. -/
theorem friE_entails_congr (Ps Ps' F : α → Prop) (h : Ps = Ps') (h2 : Ps' ⊢ F) : Ps ⊢ F :=
  entails_congr_left h h2

/-- `fri_extract`, explicit: a pure conjunct of the *premise* is a
hypothesis of the frame inference. -/
theorem friE_extract_pure (Φ : Prop) (Ps Qs F : α → Prop) (h : Φ → FRAME_INFER Ps Qs F) :
    FRAME_INFER (⌜Φ⌝ ∗ Ps) Qs F := fri_extract_pure h

/-- `fri_pure`, explicit. -/
theorem friE_pure (Φ : Prop) (Ps Qs F : α → Prop) (hΦ : Φ) (h : FRAME_INFER Ps Qs F) :
    FRAME_INFER Ps (⌜Φ⌝ ∗ Qs) F := fri_pure hΦ h

end Explicit

/-- `fri_gc_absorb_of`, explicit. -/
theorem friE_gc_absorb (A Ps Qs F : Assn) (hA : A ⊢ GC) (h : FRAME_INFER Ps (GC ∗ Qs) F) :
    FRAME_INFER (A ∗ Ps) (GC ∗ Qs) F := fri_gc_absorb_of hA h

/-- `fri_gc_end`, explicit. -/
theorem friE_gc_end (Ps Qs F : Assn) (h : FRAME_INFER Ps Qs F) :
    FRAME_INFER Ps (GC ∗ Qs) F := fri_gc_end h

/-- `fri_credit_ge`, explicit and with the leftover `l` as an argument
rather than an equation: the tactic supplies the numeral, and the goal's
own `¤¤n j` meets `¤¤n (k + l)` at `assignChecked`'s defeq check. -/
theorem friE_credit_ge (n : String) (k l : ℕ) (Ps Qs F : Assn)
    (h : FRAME_INFER (¤¤n l ∗ Ps) Qs F) : FRAME_INFER (¤¤n (k + l) ∗ Ps) (¤¤n k ∗ Qs) F :=
  fri_credit_ge rfl h

/-- `fri_credit_le`, likewise. -/
theorem friE_credit_le (n : String) (j l : ℕ) (Ps Qs F : Assn)
    (h : FRAME_INFER Ps (¤¤n l ∗ Qs) F) : FRAME_INFER (¤¤n j ∗ Ps) (¤¤n (j + l) ∗ Qs) F :=
  fri_credit_le rfl h

/-! ## 5. The solver

The search control. Everything below is `MetaM` plumbing that resolves
against the rules of §2–§4 and proves nothing on its own: every proof
term it builds is an application of `friE_prepare` / `friE_prems_cong` /
`friE_target_cong` / `friE_step` / `friE_end` and the derived step
forms, so the calculus is exactly the source's and the tactic is exactly
search (judgment call D-y). -/

namespace FriSolver

/-- The carrier and its four instances, read off the goal once and
carried through the loop so that no step has to re-synthesize them. -/
structure Ctx where
  /-- The separation-algebra carrier. -/
  α : Expr
  /-- Its `Zero` instance. -/
  z : Expr
  /-- Its `Add` instance. -/
  add : Expr
  /-- Its `SepDisj` instance. -/
  disj : Expr
  /-- Its `SepAlgebra` instance. -/
  alg : Expr
  deriving Inhabited

/-- Apply a constant whose first five arguments are this carrier and its
four instances. -/
def Ctx.app (c : Ctx) (n : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst n) (#[c.α, c.z, c.add, c.disj, c.alg] ++ args)

/-- `P ∗ Q` at this carrier. -/
def Ctx.sep (c : Ctx) (x y : Expr) : Expr := c.app ``sepConj #[x, y]

/-- `□` at this carrier. -/
def Ctx.emp (c : Ctx) : Expr := mkAppN (mkConst ``emp) #[c.α, c.z]

/-- `FRI_END` at this carrier. -/
def Ctx.friEnd (c : Ctx) : Expr := mkAppN (mkConst ``FRI_END) #[c.α, c.z]

/-- `FRAME_INFER P Qs F` at this carrier. -/
def Ctx.frameInfer (c : Ctx) (P Qs F : Expr) : Expr := c.app ``FRAME_INFER #[P, Qs, F]

/-- `P ⊢ Q` at this carrier. -/
def Ctx.entails (c : Ctx) (P Q : Expr) : Expr :=
  mkAppN (mkConst ``entails) #[c.α, P, Q]

/-- The normal form of a `∗`-list: `P₁ ∗ (P₂ ∗ (… ∗ tail))`, and `tail`
itself when the list is empty. The premise side is built with
`tail = □`, the target side with `tail = FRI_END`. -/
def Ctx.build (c : Ctx) : List Expr → Expr → Expr
  | [], tail => tail
  | x :: l, tail => c.sep x (c.build l tail)

/-- The residue's normal form once the loop is over: like `build`, but
without the terminating `□`, which is what a caller-supplied frame is
written in. -/
def Ctx.buildBare (c : Ctx) : List Expr → Expr
  | [] => c.emp
  | [x] => x
  | x :: l => c.sep x (c.buildBare l)

/-- `friE_congr_right A B B' h`, the recursion step of every equality
the solver builds. -/
def Ctx.congrRight (c : Ctx) (a b b' h : Expr) : Expr :=
  c.app ``friE_congr_right #[a, b, b', h]

/-- Head-and-arguments of an expression, with `mdata` stripped: `simp`
routinely wraps a rewritten goal in metadata, and an unstripped
`getAppFnArgs` then reports no head constant at all. -/
def headArgs (e : Expr) : Name × Array Expr := e.consumeMData.getAppFnArgs

/-- Assign a step's proof to a goal, checking that it fits. Every step
below goes through this, so a mis-instantiated rule is reported at the
step that built it rather than at the end of the proof. -/
def assignChecked (goal : MVarId) (prf : Expr) : MetaM Unit := do
  let want := (← instantiateMVars (← goal.getType)).consumeMData
  let have_ ← inferType prf
  unless ← isDefEq want have_ do
    throwError "fri: internal error: a step proof does not fit its goal.\n\
      goal:{indentExpr want}\nproof:{indentExpr have_}"
  goal.assign prf

/-! ### Flattening

`norm c e tail` returns the conjuncts of `e` together with a proof that
`e ∗ tail` is their normal form. This is the associativity/`emp` half of
the source's `fri_prepare_simps` run, done structurally so that the
result's *shape* is known to the caller rather than read back off the
goal. The credit-splitting half is the `fri_prepare_simps` attribute
proper, run as a simp set by the `fri` macro before the core starts. -/

/-- `norm c e tail = (l, h)` with `h : e ∗ tail = c.build l tail`. -/
partial def norm (c : Ctx) (e tail : Expr) : MetaM (List Expr × Expr) := do
  match headArgs e with
  | (``sepConj, #[_, _, _, _, _, a, b]) => do
      let (lb, hb) ← norm c b tail
      let tb := c.build lb tail
      let (la, ha) ← norm c a tb
      let h1 := c.app ``sepConj_assoc #[a, b, tail]
      let h2 := c.congrRight a (c.sep b tail) tb hb
      return (la ++ lb, ← mkEqTrans h1 (← mkEqTrans h2 ha))
  | (``emp, _) => return ([], c.app ``emp_sepConj #[tail])
  | _ => return ([e], ← mkEqRefl (c.sep e tail))

/-! ### Selection and permutation

The source's `rotations_tac`, as a permutation equality (judgment call
D-y). `selectAt` brings one conjunct to the front; `permute` reorders a
whole list by repeated selection. Both produce equalities that are fed
through `friE_prems_cong` / `friE_target_cong`. -/

/-- `selectAt c l tail k : c.build l tail = c.build (l[k] :: l.eraseIdx k) tail`. -/
partial def selectAt (c : Ctx) (l : List Expr) (tail : Expr) (k : Nat) : MetaM Expr := do
  match k, l with
  | 0, _ => mkEqRefl (c.build l tail)
  | k' + 1, a :: l' => do
      let some b := l'[k']? | throwError "fri: internal error: selection index out of range"
      let l'' := l'.eraseIdx k'
      let h' ← selectAt c l' tail k'
      let h1 := c.congrRight a (c.build l' tail) (c.build (b :: l'') tail) h'
      let h2 := c.app ``sepConj_left_comm #[a, b, c.build l'' tail]
      mkEqTrans h1 h2
  | _ + 1, [] => throwError "fri: internal error: selection index out of range"

/-- `permute c l tail order` reorders `l` by the index sequence `order`
(a permutation of `l`'s indices), returning the reordered list and
`c.build l tail = c.build reordered tail`. -/
partial def permute (c : Ctx) (l : List Expr) (tail : Expr) (order : List Nat) :
    MetaM (List Expr × Expr) := do
  match order with
  | [] => return (l, ← mkEqRefl (c.build l tail))
  | k :: rest => do
      let some a := l[k]? | throwError "fri: internal error: permutation index out of range"
      let l' := l.eraseIdx k
      let h1 ← selectAt c l tail k
      let rest' := rest.map fun i => if i > k then i - 1 else i
      let (res, h2) ← permute c l' tail rest'
      let h3 := c.congrRight a (c.build l' tail) (c.build res tail) h2
      return (a :: res, ← mkEqTrans h1 h3)

/-- `dropTail c l : c.build l □ = c.buildBare l` — peel the terminating
`□` off the residue. -/
partial def dropTail (c : Ctx) : List Expr → MetaM Expr
  | [] => mkEqRefl c.emp
  | [x] => return c.app ``sepConj_emp #[x]
  | x :: l => do
      return c.congrRight x (c.build l c.emp) (c.buildBare l) (← dropTail c l)

/-! ### Recognizers -/

/-- Is this conjunct the garbage collector? -/
def isGC (e : Expr) : Bool := (headArgs e).1 == ``GC

/-- The balance of a `¤c` conjunct. -/
def credits? (e : Expr) : Option Expr :=
  match headArgs e with
  | (``credits, #[a]) => some a
  | _ => none

/-- The currency and amount of a `¤¤n k` conjunct, with `k` a numeral. -/
def costCredits? (e : Expr) : MetaM (Option (Expr × Expr × Nat)) := do
  match headArgs e with
  | (``costCredits, #[n, k]) =>
      match k.nat? with
      | some kv => return some (n, k, kv)
      | none => return ((← whnf k).nat?).map fun kv => (n, k, kv)
  | _ => return none

/-- The proposition of a `⌜Φ⌝` conjunct. -/
def predLift? (e : Expr) : Option Expr :=
  match headArgs e with
  | (``predLift, #[_, _, φ]) => some φ
  | _ => none

/-- What a target `GC` can swallow: a conjunct owning no cell. -/
def absorbable (e : Expr) : MetaM Bool := do
  if isGC e then return true
  if (credits? e).isSome then return true
  return (← costCredits? e).isSome

/-- The `A ⊢ GC` justification for an absorbable conjunct. -/
def absorbProof (e : Expr) : MetaM Expr := do
  if isGC e then return mkConst ``GC_entails_GC
  if let some (n, k, _) ← costCredits? e then
    return mkAppN (mkConst ``costCredits_entails_GC) #[n, k]
  if let some ce := credits? e then return mkAppN (mkConst ``entails_GC) #[ce]
  throwError "fri: internal error: conjunct is not absorbable{indentExpr e}"

/-! ### Messages

The supervision-legibility requirement, in the style of
`Autoref/Solver.lean`: every failure names the conjunct that could not
be matched and the premise conjuncts that were on offer. -/

/-- A conjunct list, as it appears in a message. -/
def conjunctList (l : List Expr) : MetaM MessageData := do
  if l.isEmpty then return m!"\n  (none)"
  return MessageData.joinSep (l.map fun e => indentExpr e) m!""

/-- The message when no premise conjunct matches a target conjunct. -/
def noMatchMsg (q : Expr) (ps : List Expr) : MetaM MessageData := do
  return m!"fri: no premise conjunct matches the target conjunct{indentExpr q}\n\
    premise conjuncts still unconsumed:{← conjunctList ps}"

/-- The message when the residue does not entail the frame. -/
def endFailMsg (ps : List Expr) (F : Expr) : MetaM MessageData := do
  return m!"fri: every target conjunct was matched, but the leftover premise does not \
    entail the frame{indentExpr F}\nleftover premise conjuncts:{← conjunctList ps}"

/-! ### The end phase

`fri_end`, then `entails_refl` (the source's one hard-coded priority: it
is what instantiates a schematic frame), then the `fri_end_rules`
database. -/

/-- Close `Ps ⊢ F`. The residue's terminating `□` is stripped first, so
that `entails_refl` — which is what *instantiates a schematic frame* —
sees the residue in the shape a caller writes a frame in. -/
def endPhase (c : Ctx) (goal₀ : MVarId) (ps : List Expr) (F : Expr) : MetaM Unit := do
  let m ← mkFreshExprSyntheticOpaqueMVar (c.entails (c.buildBare ps) F)
  assignChecked goal₀
    (c.app ``friE_entails_congr #[c.build ps c.emp, c.buildBare ps, F, ← dropTail c ps, m])
  let goal := m.mvarId!
  let extra ← (try labelled `fri_end_rules catch _ => pure #[])
  for r in #[``entails_refl] ++ extra do
    let st ← saveState
    try
      let gs ← goal.apply (← mkConstWithFreshMVarLevels r)
      if gs.isEmpty then return ()
      st.restore
    catch _ => st.restore
  throwError (← endFailMsg ps F)

/-! ### The round loop -/

/-- Try to match the target conjunct `q` against the premise conjunct
`p` with a `fri_rules` member, returning the entailment proof and any
side goals the member left behind. A premise conjunct that is still a
metavariable is never matched: the frame is what is *left over*, not
something chosen to satisfy a target. -/
def tryRules (p q : Expr) : MetaM (Option (Expr × Array MVarId)) := do
  if (← instantiateMVars p).isMVar then return none
  let extra ← (try labelled `fri_rules catch _ => pure #[])
  for r in extra do
    let st ← saveState
    try
      let rule ← mkConstWithFreshMVarLevels r
      let (mvars, _, concl) ← forallMetaTelescope (← inferType rule)
      match headArgs concl with
      | (``entails, #[_, pE, qE]) =>
          if (← isDefEq pE p) && (← isDefEq qE q) then
            let mut side := #[]
            for mv in mvars do
              if (← instantiateMVars mv).isMVar then
                let mvid := mv.mvarId!
                if (← isProp (← mvid.getType)) then side := side.push mvid
                else throwError "fri: rule {r} left an unresolved argument"
            return some (mkAppN rule mvars, side)
          else st.restore
      | _ => st.restore
    catch _ => st.restore
  return none

/-- One `fri` round, then recursion. `ps` / `qs` are the premise and
target conjunct lists, `F` the frame; the goal is always
`FRAME_INFER (build ps □) (build qs FRI_END) F`. -/
partial def round (c : Ctx) (goal : MVarId) (ps qs : List Expr) (F : Expr)
    (side : Array MVarId) : MetaM (Array MVarId) := do
  let psE := c.build ps c.emp
  match qs with
  | [] => do
      let m ← mkFreshExprSyntheticOpaqueMVar (c.entails psE F)
      assignChecked goal (c.app ``friE_end #[psE, F, m])
      endPhase c m.mvarId! ps F
      return side
  | q :: qs' => do
      let qsE := c.build qs c.friEnd
      let qsE' := c.build qs' c.friEnd
      -- (1) `GC`: absorb everything absorbable, then discharge (D-ab).
      if isGC q then
        let mut absIdx : Option Nat := none
        for i in [0 : ps.length] do
          if absIdx.isNone then
            if let some p := ps[i]? then
              if ← absorbable p then absIdx := some i
        if let some i := absIdx then
          let some a := ps[i]? | throwError "fri: internal error"
          let ps' := ps.eraseIdx i
          let ps'E := c.build ps' c.emp
          let m ← mkFreshExprSyntheticOpaqueMVar (c.frameInfer ps'E qsE F)
          let step := mkAppN (mkConst ``friE_gc_absorb)
            #[a, ps'E, qsE', F, ← absorbProof a, m]
          assignChecked goal
            (c.app ``friE_prems_cong #[psE, c.sep a ps'E, qsE, F, ← selectAt c ps c.emp i, step])
          return ← round c m.mvarId! ps' qs F side
        else
          let m ← mkFreshExprSyntheticOpaqueMVar (c.frameInfer psE qsE' F)
          assignChecked goal (mkAppN (mkConst ``friE_gc_end) #[psE, qsE', F, m])
          return ← round c m.mvarId! ps qs' F side
      -- (2) the step set: one premise conjunct against this target conjunct.
      for i in [0 : ps.length] do
        let some p := ps[i]? | continue
        let st ← saveState
        match ← tryRules p q with
        | some (ruleProof, ruleSide) =>
            let ps' := ps.eraseIdx i
            let ps'E := c.build ps' c.emp
            let m ← mkFreshExprSyntheticOpaqueMVar (c.frameInfer ps'E qsE' F)
            let step := c.app ``friE_step #[p, q, ps'E, qsE', F, ruleProof, m]
            assignChecked goal
              (c.app ``friE_prems_cong
                #[psE, c.sep p ps'E, qsE, F, ← selectAt c ps c.emp i, step])
            return ← round c m.mvarId! ps' qs' F (side ++ ruleSide)
        | none => st.restore
      -- (3) credits: match `¤¤n k` against `¤¤n j` by numeral arithmetic (D-aa).
      if let some (nq, _, k) ← costCredits? q then
        for i in [0 : ps.length] do
          let some p := ps[i]? | continue
          if let some (np, _, j) ← costCredits? p then
            if ← isDefEq nq np then
              let ps' := ps.eraseIdx i
              let ps'E := c.build ps' c.emp
              let hsel ← selectAt c ps c.emp i
              if j > k then
                let lE := mkNatLit (j - k)
                let pNew := mkAppN (mkConst ``costCredits) #[nq, lE]
                let m ← mkFreshExprSyntheticOpaqueMVar
                  (c.frameInfer (c.sep pNew ps'E) qsE' F)
                let step := mkAppN (mkConst ``friE_credit_ge)
                  #[nq, mkNatLit k, lE, ps'E, qsE', F, m]
                assignChecked goal
                  (c.app ``friE_prems_cong #[psE, c.sep p ps'E, qsE, F, hsel, step])
                return ← round c m.mvarId! (pNew :: ps') qs' F side
              else
                let lE := mkNatLit (k - j)
                let qNew := mkAppN (mkConst ``costCredits) #[nq, lE]
                let m ← mkFreshExprSyntheticOpaqueMVar
                  (c.frameInfer ps'E (c.sep qNew qsE') F)
                let step := mkAppN (mkConst ``friE_credit_le)
                  #[nq, mkNatLit j, lE, ps'E, qsE', F, m]
                assignChecked goal
                  (c.app ``friE_prems_cong #[psE, c.sep p ps'E, qsE, F, hsel, step])
                return ← round c m.mvarId! ps' (qNew :: qs') F side
      -- (4) a pure target conjunct owns nothing: defer it (D-ac).
      if let some φ := predLift? q then
        let mφ ← mkFreshExprSyntheticOpaqueMVar φ
        let m ← mkFreshExprSyntheticOpaqueMVar (c.frameInfer psE qsE' F)
        assignChecked goal (c.app ``friE_pure #[φ, psE, qsE', F, mφ, m])
        return ← round c m.mvarId! ps qs' F (side.push mφ.mvarId!)
      throwError (← noMatchMsg q ps)

/-! ### The extraction phase

The source's `fri_extract`: before matching begins, every pure conjunct
of the premise is turned into a hypothesis of the goal, so that the
side-condition solver can use the facts the precondition carries and so
that a pure conjunct the target does not want is not left over at the
end (judgment call D-ac). -/

/-- Peel every `⌜Φ⌝` off the premise list into the goal's context. -/
partial def extractPure (c : Ctx) (goal : MVarId) (ps qs : List Expr) (F : Expr) :
    MetaM (MVarId × List Expr) :=
  goal.withContext do
    let mut found : Option (Nat × Expr × Expr) := none
    for i in [0 : ps.length] do
      if found.isNone then
        if let some p := ps[i]? then
          if let some φ := predLift? p then found := some (i, p, φ)
    match found with
    | none => return (goal, ps)
    | some (i, p, φ) =>
        let ps' := ps.eraseIdx i
        let psE := c.build ps c.emp
        let ps'E := c.build ps' c.emp
        let qsE := c.build qs c.friEnd
        let m ← mkFreshExprSyntheticOpaqueMVar
          (.forallE `hpure φ (c.frameInfer ps'E qsE F) .default)
        let step := c.app ``friE_extract_pure #[φ, ps'E, qsE, F, m]
        assignChecked goal
          (c.app ``friE_prems_cong #[psE, c.sep p ps'E, qsE, F, ← selectAt c ps c.emp i, step])
        let (_, g) ← m.mvarId!.intro1P
        extractPure c g ps' qs F

/-! ### The start phase -/

/-- Read the carrier and its instances off a `FRAME_INFER` application. -/
def ctxOf (ty : Expr) : MetaM (Ctx × Expr × Expr × Expr) := do
  match headArgs ty with
  | (``FRAME_INFER, #[α, z, add, disj, alg, P, Qs, F]) =>
      return (⟨α, z, add, disj, alg⟩, P, Qs, F)
  | _ => throwError "fri: expected a FRAME_INFER goal, got{indentExpr ty}"

/-- The source's `start_tac`: dispatch on the tag, then normalize both
sides into `∗`-lists and park `FRI_END`. -/
def start (goal : MVarId) : MetaM MVarId := do
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  match headArgs ty with
  | (``FRAME, _) => do
      let gs ← goal.apply (← mkConstWithFreshMVarLevels ``fri_startI_frame)
      let some g := gs[0]? | throwError "fri: fri_startI_frame left no goal"
      let (_, g) ← g.intro1P
      return g
  | (``ENTAILS, _) | (``entails, _) => do
      let gs ← goal.apply (← mkConstWithFreshMVarLevels ``fri_startI_entails)
      let some g := gs[0]? | throwError "fri: fri_startI_entails left no goal"
      let (_, g) ← g.intro1P
      return g
  | (``FRAME_INFER, _) => return goal
  | (hd, _) => throwError "fri: the goal is not a FRAME / ENTAILS / FRAME_INFER goal \
      (its head is '{hd}'):{indentExpr ty}"

/-- The whole solver: `start`, then rounds until the target list is
exhausted, then `end`. Returns the side conditions it deferred. -/
def solve (goal₀ : MVarId) : MetaM (Array MVarId) := do
  let goal ← start goal₀
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  let (c, P, Qs, F) ← ctxOf ty
  -- premise side: `P = build ps □`
  let (ps, hp0) ← norm c P c.emp
  let hp ← mkEqTrans (← mkEqSymm (c.app ``sepConj_emp #[P])) hp0
  -- target side: `Qs ∗ FRI_END = build qs FRI_END`, with `GC` sorted last (D-ab).
  let (qs, hq) ← norm c Qs c.friEnd
  let idx := List.range qs.length
  let order := idx.filter (fun i => !isGC qs[i]!) ++ idx.filter (fun i => isGC qs[i]!)
  let (qsSorted, hperm) ← permute c qs c.friEnd order
  let hqAll ← mkEqTrans hq hperm
  let psE := c.build ps c.emp
  let qsE := c.build qsSorted c.friEnd
  let m ← mkFreshExprSyntheticOpaqueMVar (c.frameInfer psE qsE F)
  let inner := c.app ``friE_target_cong #[psE, c.sep Qs c.friEnd, qsE, F, hqAll, m]
  let outer := c.app ``friE_prems_cong #[P, psE, c.sep Qs c.friEnd, F, hp, inner]
  assignChecked goal (c.app ``friE_prepare #[P, Qs, F, outer])
  let (g, ps') ← extractPure c m.mvarId! ps qsSorted F
  g.withContext (round c g ps' qsSorted F #[])

end FriSolver

/-! ### The tactics

`fri` is the source's own method name for frame inference, and — as in
the source — it serves the `ENTAILS` front end too, because
`fri_startI` has two clauses (judgment call D-af). -/

/-- The solver core: no prepare-phase simp set, no side-condition
tactic. Leaves the deferred pure side conditions as goals. -/
elab "fri_core" : tactic => do
  let goal ← getMainGoal
  -- `withContext` is load-bearing: the deferred side conditions are fresh
  -- metavariables, and without the goal's own local context they would be
  -- created in the ambient one and lose every hypothesis the surrounding
  -- tactic block introduced.
  let side ← goal.withContext (FriSolver.solve goal)
  replaceMainGoal side.toList

/-- The side-condition tactic the deferred `⌜Φ⌝` goals are handed to
(judgment call D-ac). What it does not close stays a goal. -/
macro "fri_side" : tactic =>
  `(tactic| try (first | assumption | rfl | trivial | omega | decide | simp))

/-- Frame inference. Normalizes with the `fri_prepare_simps` set, runs
the solver, and hands each deferred pure side condition to `fri_side`.

Dispatches on the goal's tag: `FRAME P Q ?F` instantiates the frame
metavariable with whatever the match leaves over; `ENTAILS P Q` (or a
bare `P ⊢ Q`) requires the match to be exact, modulo a trailing `GC` in
the target absorbing leftover credits. -/
macro "fri" : tactic =>
  `(tactic| ((try simp only [fri_prepare_simps]); fri_core <;> fri_side))

/-- `fri` at an entailment goal, under a name that says so. -/
macro "ir_entails" : tactic => `(tactic| fri)

/-- Report what `fri` would fail with, as an `info` message, instead of
throwing — the `Autoref/Solver.lean` precedent, so the gate can pin a
failure message without leaving a failing declaration behind. -/
elab "fri_trace" : tactic => do
  let goal ← getMainGoal
  try
    let side ← goal.withContext (FriSolver.solve goal)
    replaceMainGoal side.toList
  catch e => logInfo (← e.toMessageData.toString)

/-! ## 5. Applying a triple with a frame

`Sep_Generic_Wp.thy`'s `htriple_vcg_frame_erule` (extract §3) is the
rule that turns a Hoare-triple application into a frame inference plus
an entailment:

```isabelle
lemma htriple_vcg_frame_erule[vcg_frame_erules]:
  assumes S: "STATE α P' s"
  assumes F: "PRECOND (FRAME P' P F)"
  assumes HT: "htriple α P c Q"
  assumes P: "⋀r s. STATE α (Q r ** F) s ⟹ PRECOND (EXTRACT (Q' r s))"
  shows "wp c Q' s"
```

At the triple level — which is where the acceptance programs need it,
and where it costs no VCG machinery at all — that is the two lemmas
below (judgment call D-ae). Their two side conditions are literally
`FRAME P' P ?F` and `ENTAILS (Q ∗ ?F) Q'`: one `fri` call each, with
the frame metavariable instantiated by the first and consumed by the
second. -/

/-- Apply an exact triple to a precondition it does not exactly
describe: infer the frame, then check the postcondition. -/
theorem irTriple_frame {P P' Q Q' F : Assn} {c : Com} (h : irTriple P c Q)
    (hpre : FRAME P' P F) (hpost : ENTAILS (Q ∗ F) Q') : irTriple P' c Q' :=
  cons_rule (frame_rule F h) (fun s hs => hpre s hs) (fun _ s hs => hpost s hs)

/-- The same at the source's garbage-collecting triple: the `GC` the
postcondition already carries is merged with the frame by the second
side condition. -/
theorem irHtriple_frame {P P' Q Q' F : Assn} {c : Com} (h : irHtriple P c Q)
    (hpre : FRAME P' P F) (hpost : ENTAILS ((Q ∗ GC) ∗ F) (Q' ∗ GC)) : irHtriple P' c Q' :=
  cons_rule (frame_rule F h) (fun s hs => hpre s hs) (fun _ s hs => hpost s hs)

/-- Apply the exact triple `t` to the goal, discharging both the frame
inference and the postcondition entailment with `fri`. -/
macro "ir_frame " t:term : tactic => `(tactic| (apply irTriple_frame $t <;> fri))

/-- `ir_frame` at a garbage-collecting triple. -/
macro "ir_frame_gc " t:term : tactic => `(tactic| (apply irHtriple_frame $t <;> fri))

/-! ## 6. The `vcg_rules` database (judgment call D-ad)

Wave B's D-u left the array rules with their index bound as a Lean
hypothesis, and stated `aget_rule_pure` — the bound as a `⌜⌝` conjunct
of the precondition — as "the form wave C will register". Here is the
registration, with the `aset` companion added so the pair is symmetric.
The bound is now discharged by this file's own solver, as a pure target
conjunct (judgment call D-ac); the acceptance file exercises that path
on both rules. -/

/-- `a[i] := v` with the index bound as a precondition conjunct: the
source's own shape (`ll_store_rule_range`'s `↑⇩!(…)`), and the companion
of wave B's `aget_rule_pure`. -/
theorem aset_rule_pure (a i v : String) (k n : Val) (xs : List Val) :
    irHtriple (⌜k < xs.length⌝ ∗ ¤¤Currency.aset 1 ∗ a ↦ₐ xs ∗ i ↦ᵥ k ∗ v ↦ᵥ n) (.aset a i v)
      (a ↦ₐ xs.set k n ∗ i ↦ᵥ k ∗ v ↦ᵥ n) := by
  intro F p hp
  rw [sepConj_assoc, predLift_sepConj_iff] at hp
  obtain ⟨hk, hp⟩ := hp
  exact aset_rule a i v k n xs hk F p hp

/-- …and its exact form, which is what a composition of triples wants
(wave B's D-v: composing exact triples does not leak a `GC` into every
intermediate assertion). -/
theorem aset_triple_pure (a i v : String) (k n : Val) (xs : List Val) :
    irTriple (⌜k < xs.length⌝ ∗ ¤¤Currency.aset 1 ∗ a ↦ₐ xs ∗ i ↦ᵥ k ∗ v ↦ᵥ n) (.aset a i v)
      (a ↦ₐ xs.set k n ∗ i ↦ᵥ k ∗ v ↦ᵥ n) := by
  intro F p hp
  rw [sepConj_assoc, predLift_sepConj_iff] at hp
  obtain ⟨hk, hp⟩ := hp
  exact aset_triple a i v k n xs hk F p hp

/-- The exact form of wave B's `aget_rule_pure`. -/
theorem aget_triple_pure (x a i : String) (v k : Val) (xs : List Val) :
    irTriple (⌜k < xs.length⌝ ∗ ¤¤Currency.aget 1 ∗ x ↦ᵥ v ∗ a ↦ₐ xs ∗ i ↦ᵥ k) (.aget x a i)
      (x ↦ᵥ xs.getD k 0 ∗ a ↦ₐ xs ∗ i ↦ᵥ k) := by
  intro F p hp
  rw [sepConj_assoc, predLift_sepConj_iff] at hp
  obtain ⟨hk, hp⟩ := hp
  have hw : xs[k]? = some (xs.getD k 0) := by
    rw [List.getElem?_eq_getElem hk]
    simp [List.getD, List.getElem?_eq_getElem hk]
  exact aget_triple x a i v k _ xs hw F p hp

attribute [vcg_rules] skip_rule const_rule copy_rule binop_rule binop_self_rule
  aget_rule_pure aset_rule_pure

/-! ## 6b. Reading a state through the frame inferencer

`start_entailsE` (wave B, `Sep_Generic_Wp.thy`) turns a state fact into
an entailment goal; composing it with `fri` is how a proof gets at *one*
conjunct of a many-conjunct precondition without touching the others.
This is the working part of the source's `fri_extract` — the part that
extracts a fact — in lemma form rather than as a context-modifying
tactic (judgment call D-ac). In each of the three, the frame `F` is a
metavariable that the `by fri` at the call site instantiates. -/

/-- Rearrange a state fact by frame inference. -/
theorem irSTATE_frame {P P' F : Assn} {p : State × ECost} (h : irSTATE P p)
    (hf : FRAME P P' F) : irSTATE (P' ∗ F) p := start_entailsE h hf

/-- Read a scalar cell out of a many-conjunct precondition. -/
theorem ptoVar_of_frame {P F : Assn} {x : String} {v : Val} {s : State} {cr : ECost}
    (h : irSTATE P (s, cr)) (hf : FRAME P (x ↦ᵥ v) F) : s.vars x = some v :=
  ptoVar_vars (irSTATE_frame h hf)

/-- Read an array out of a many-conjunct precondition. -/
theorem ptoArr_of_frame {P F : Assn} {a : String} {xs : List Val} {s : State} {cr : ECost}
    (h : irSTATE P (s, cr)) (hf : FRAME P (a ↦ₐ xs) F) : s.arrs a = some xs :=
  ptoArr_arrs (irSTATE_frame h hf)

/-- Read a pure fact out of a many-conjunct precondition. -/
theorem pure_of_frame {P F : Assn} {Φ : Prop} {p : State × ECost} (h : irSTATE P p)
    (hf : FRAME P ⌜Φ⌝ F) : Φ := by
  have h' : (⌜Φ⌝ ∗ F) (irα p) := irSTATE_frame h hf
  exact (predLift_sepConj_iff.1 h').1

/-! ### Two shapes a triple is applied in

Neither is frame inference; both are the plumbing that lets a triple
whose precondition carries a pure conjunct, or whose postcondition is an
existential, be handled by `fri` at the conjunct level. -/

/-- A pure conjunct in the precondition is a hypothesis of the triple —
the converse of wave B's D-u, and what makes an invariant carrying
`⌜k ≤ n⌝` usable. -/
theorem irTriple_pure {Φ : Prop} {P Q : Assn} {c : Com} (h : Φ → irTriple P c Q) :
    irTriple (⌜Φ⌝ ∗ P) c Q := by
  intro F p hp
  rw [sepConj_assoc, predLift_sepConj_iff] at hp
  exact h hp.1 F p hp.2

/-- Instantiate an existential postcondition: the solver matches
conjuncts, so the witness is chosen before it runs. -/
theorem irTriple_ex {β : Type} {P : Assn} {Q : β → Assn} {c : Com} (x : β)
    (h : irTriple P c (Q x)) : irTriple P c (∃ᵃ y, Q y) :=
  cons_rule h (fun _ hs => hs) (fun _ _ hs => ⟨x, hs⟩)

/-! ## 7. The gate (ledger D4)

Positive controls first: a six-conjunct entailment under two nontrivial
permutations, credit splitting matched in both directions across the
turnstile, `GC` absorbing what is left. Then the negative controls, each
in two forms — `fail_if_success`, which checks the *behaviour*, and
`#fri_report`, which pins the *message* by running the solver on a
synthetic goal and printing what came back, so that nothing failing is
left in the environment. -/

namespace Gate

open Lean Elab

/-- Run the solver on a goal written inline and report the outcome. The
`Autoref/Solver.lean` precedent (`tagged_solver_trace`) in command form:
it elaborates the statement, runs `FriSolver.solve` on a fresh
metavariable, and logs either success or the failure message — the
metavariable is discarded either way, so a pinned failure costs the
environment nothing. -/
syntax (name := friReportCmd) "#fri_report " term : command

elab_rules : command
  | `(command| #fri_report $t:term) => Command.liftTermElabM do
      let ty ← Term.elabType t
      let m ← Meta.mkFreshExprSyntheticOpaqueMVar ty
      try
        let side ← FriSolver.solve m.mvarId!
        if side.isEmpty then logInfo "fri: closed the goal"
        else logInfo s!"fri: closed the goal, {side.size} side condition(s) deferred"
      catch e => logInfo (← e.toMessageData.toString)

/-! ### Positive controls -/

/-- Six conjuncts, reversed. -/
example (a b c d e f : Assn) : ENTAILS (a ∗ b ∗ c ∗ d ∗ e ∗ f) (f ∗ e ∗ d ∗ c ∗ b ∗ a) := by fri

/-- Six conjuncts, a permutation that is not a rotation and not a
reversal — the shape a rotate-only search would have to sweep for. -/
example (a b c d e f : Assn) : ENTAILS (a ∗ b ∗ c ∗ d ∗ e ∗ f) (d ∗ a ∗ f ∗ c ∗ e ∗ b) := by fri

/-- Seven conjuncts of the IR's own vocabulary, scrambled. -/
example (xs : List Val) : ENTAILS
    (¤¤Currency.aget 1 ∗ "x" ↦ᵥ 1 ∗ "A" ↦ₐ xs ∗ "i" ↦ᵥ 2 ∗ "p" ↦ᵥ 3 ∗ "q" ↦ᵥ 4 ∗ "r" ↦ᵥ 5)
    ("q" ↦ᵥ 4 ∗ "A" ↦ₐ xs ∗ "r" ↦ᵥ 5 ∗ ¤¤Currency.aget 1 ∗ "i" ↦ᵥ 2 ∗ "p" ↦ᵥ 3 ∗ "x" ↦ᵥ 1) := by
  fri

/-- The frame metavariable is instantiated by what is left over. -/
example (a b c : Assn) : FRAME (a ∗ b ∗ c) b (a ∗ c) := by fri

/-- Credit splitting, across the turnstile, in both directions. -/
example (p q : ECost) : ENTAILS (¤(p + q)) (¤p ∗ ¤q) := by fri
example (p q : ECost) : ENTAILS (¤p ∗ ¤q) (¤(p + q)) := by fri

/-- …and at the `¤¤` spelling, where the split is numeral arithmetic
(judgment call D-aa): three units cover one and two, and one and two
cover three. -/
example : ENTAILS (¤¤Currency.aget 3) (¤¤Currency.aget 1 ∗ ¤¤Currency.aget 2) := by fri
example : ENTAILS (¤¤Currency.aget 1 ∗ ¤¤Currency.aget 2) (¤¤Currency.aget 3) := by fri

/-- A bundled per-iteration payload, split off one copy at a time — the
`fri_prepare_simps` extension point, at the shape a loop invariant
uses. -/
example (c : ECost) (j : ℕ) : ENTAILS (¤((j + 1) • c)) (¤c ∗ ¤(j • c)) := by fri

/-- `GC` absorbs leftover credits, and only credits. -/
example (x : String) (v : Val) (p : ECost) :
    ENTAILS ((x ↦ᵥ v) ∗ ¤p) ((x ↦ᵥ v) ∗ GC) := by fri

example (x : String) (v : Val) :
    ENTAILS ((x ↦ᵥ v) ∗ ¤¤Currency.aget 2 ∗ ¤¤Currency.aset 1 ∗ GC) ((x ↦ᵥ v) ∗ GC) := by fri

/-- A pure target conjunct is discharged by the side tactic. -/
example (x : String) (v : Val) : ENTAILS (x ↦ᵥ v) (⌜(2 : ℕ) < 5⌝ ∗ x ↦ᵥ v) := by fri

/-- …and one the side tactic cannot close is *deferred*, not failed
(judgment call D-ac): `fri` leaves it as a goal. -/
example (x : String) (v : Val) (n : ℕ) (hn : n < 5) : ENTAILS (x ↦ᵥ v) (⌜n < 5⌝ ∗ x ↦ᵥ v) := by
  fri_core
  exact hn

/-! ### Negative controls -/

/-- A points-to the premise does not own is not derivable. -/
example : True := by
  fail_if_success (have : ENTAILS (("x" : String) ↦ᵥ 3) (("y" : String) ↦ᵥ 3) := by fri)
  trivial

/-- Credits of the wrong currency do not pay for an op. -/
example : True := by
  fail_if_success
    (have : ENTAILS (¤¤Currency.aget 1) (¤¤Currency.aset 1) := by fri)
  trivial

/-- Nor do too few credits of the right one. -/
example : True := by
  fail_if_success
    (have : ENTAILS (¤¤Currency.aset 1) (¤¤Currency.aset 2) := by fri)
  trivial

/-- `GC` does not swallow a cell. -/
example : True := by
  fail_if_success (have : ENTAILS (("x" : String) ↦ᵥ 3) GC := by fri)
  trivial

/-! ### The failure messages, pinned

Each of the four negative controls again, as a message. The solver names
the target conjunct it could not match and lists the premise conjuncts
that were still on offer — the supervision-legibility requirement, and
the reason a stalled `fri` is diagnosable without reading the term. -/

/--
info: fri: no premise conjunct matches the target conjunct
  "y" ↦ᵥ 4
premise conjuncts still unconsumed:
  "x" ↦ᵥ 3
  ¤¤"ir.aget"1
-/
#guard_msgs in
#fri_report ENTAILS (("x" : String) ↦ᵥ 3 ∗ ¤¤"ir.aget" 1) (("y" : String) ↦ᵥ 4 ∗ ¤¤"ir.aget" 1)

/--
info: fri: no premise conjunct matches the target conjunct
  ¤¤"ir.aset"1
premise conjuncts still unconsumed:
  ¤¤"ir.aget"1
  "x" ↦ᵥ 3
-/
#guard_msgs in
#fri_report ENTAILS (¤¤"ir.aget" 1 ∗ ("x" : String) ↦ᵥ 3) (¤¤"ir.aset" 1 ∗ ("x" : String) ↦ᵥ 3)

/-! Too few credits of the right currency: the reduce step fires, the
premise is exhausted, and what is *still owed* is what the message
names — one `ir.aset`, the difference. -/

/--
info: fri: no premise conjunct matches the target conjunct
  ¤¤"ir.aset"1
premise conjuncts still unconsumed:
  (none)
-/
#guard_msgs in
#fri_report ENTAILS (¤¤"ir.aset" 1) (¤¤"ir.aset" 2)

/--
info: fri: every target conjunct was matched, but the leftover premise does not entail the frame
  □
leftover premise conjuncts:
  "x" ↦ᵥ 3
-/
#guard_msgs in
#fri_report ENTAILS (("x" : String) ↦ᵥ 3) GC

/-! …and the positive side of the same instrument, so that the reports
above are read against a run that succeeded. -/

/-- info: fri: closed the goal -/
#guard_msgs in
#fri_report FRAME (("x" : String) ↦ᵥ 3 ∗ ("y" : String) ↦ᵥ 4) (("y" : String) ↦ᵥ 4)
  (("x" : String) ↦ᵥ 3)

end Gate

end Lax13Proofs.Refine.Ir
