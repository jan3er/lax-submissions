import Lax13Proofs.Refine.Sepref.Frame

/-!
The translate phase: the port of `thys/sepref/Sepref_Translate.thy`.

Source pin as `Sepref/Basic.lean`'s header (`isabelle_llvm_time`
@ `42dd7f5`); the theory was fetched whole (825 lines). Its object level
— the four side-condition markers, `trans_frame_rule`, the `CPR_TAG`
family, `cons_pre_rule`, `hn_refine_synthI` and the two `drop_hn_*`
weakenings — is ported below, and its ML structure `Sepref_Translate`
(lines 137–440) is the specification of the tactics: `side_cond_dispatch_tac`
(its `WITH_concl` case split), `trans_comb_tac`, `gen_trans_op_tac` with
its four named `PHASES'`, `gen_trans_step_tac`, `gen_trans_tac`.

The header comment the port is measured against:

```
The main functionality of the translation phase is to apply refinement
rules. Thereby, the linearity information is exploited to create copies
of parameters that are still required, but would be destroyed by a
synthesized operation. These frame-based rules are in the named theorem
collection sepref_fr_rules […]. Apart from the frame-based rules
described above, there is also a set of rules for combinators, in the
collection sepref_comb_rules, where no automatic copying of parameters
is applied.
```

## Judgment calls

**T1/D-d — the post-abstraction junks pair contexts componentwise.**
(ND-MC rebase tool wave T1.) `junkConjunct` splits a
`hnCtxt (A ×ₐ B) v c` conjunct (`rfl`) and junks the components
recursively. Before this, a leaf engine returning a tuple — the
engine-as-`sepref_fr_rules`-operation idiom the 2A satellite validated
— could not be *bound*: the block's postcondition still owns the tuple
components the continuation did not consume, the ownership mentions the
binder, and the abstraction threw "no junk form for its assertion"
(exactly the R2/D-e stall the P0.2 spike predicted for `wordAssn`, met
here by every engine composition). Acceptance:
`Lax3Proofs.Refine.T1FriProbe.bfsThenSweep`.

**T2/D-e — `bind_ref_tag` constant normalization.** (ND-MC rebase tool
wave T2.) `hnr_bind`'s second premise carries `bind_ref_tag a m`
(`returnT a ≤ m`); for a constant-producing `m` that pins `a`, and the
loop used to recurse at an opaque `a` anyway, so downstream rules
naming a literal value in a cell could not fire (R2D/D-b, 2A′ gap 5 —
both engine waves paid an `assert` op per pinned cell to route around
it: `mopBfsE`, `mopBfsAt`). Now `sideDispatch` recognises the premise
shape, normalizes `m` to `consume (returnT v) κ` (all-transparency
unfolding through the irreducible `mop*` aliases) and, **only after the
opaque route has failed** — every previously green synthesis path is
byte-identical — retries at `a := v` via `pin_bind_premise`, with the
binder-dependent metavariable families re-pointed at constant families
first. Acceptance: `Examples/BoundsProbe.lean` §4 (the R2D/D-b
reproducer shape, synthesizing).

**P4/D-cm — synthesis is by metavariable instantiation, as the source
does it.** A translate goal is `hnRefine Γ ?c ?Γ' d R m` with `?c` and
`?Γ'` assignable: applying a rule *is* the synthesis, the program falls
out of the proof, and no separate term-building recursion exists. This
is the source's own mechanism (`schematic_goal … by sepref`) and it is
also P2's (`Autoref/Translate.lean`, whose `applyRule` assigns the
concrete term the same way; `Autoref/Tool.lean` delta O8 records the one
Lean-specific step, re-marking the goal's metavariables `natural`, which
`Sepref/Definition.lean` does too). The brief's fallback — synthesize
the term by a `MetaM` recursion and prove afterwards — was **not**
needed: `hnRefine`'s telescope instantiates cleanly, and the hand-run
that checked it (`hnr_seq` composing `?c := .seq ?c₁ ?c₂`) is the first
gate case in `Sepref/Definition.lean`.

**P4/D-cn — the scratch-cell pool lives in the precondition, and the
name generator names what is *missing*.** The brief asks for a
fresh-name generator feeding the destination metavariables of
`sepref_fr_rules` entries. Under P4/D-a the destination is a *cell name*
and under P4/D-c a cell is owned or it does not exist: a synthesized
`x := y ⊕ z` needs `junkCell x` in the precondition, and no tactic can
manufacture ownership — the precondition is the theorem's statement,
fixed by the caller. So the allocator *consumes* rather than invents: it
matches the rule's destination conjunct against the `junkCell` conjuncts
the caller supplied, in the order the caller wrote them, and each
allocation removes one from the pool. `freshScratchName` below is
retained for the *message*: when the pool is empty, the failure names
the cell the caller should add (`t1`, `t2`, … avoiding every name in the
goal), which is the actionable form of "no scratch cell left". Fallback
if a caller wants automatic allocation: it belongs in
`Sepref/Definition.lean`, which *builds* the goal and could append the
cells to the precondition before synthesis; the translate loop would not
change.

**P4/D-co — the four `gen_trans_op_tac` phases collapse to two.** The
source's `PHASES' [("Align goal", …), ("Frame rule", trans_frame_rule),
("Recover pure", …), ("Apply rule", …)]` exists because Isabelle's
`resolve_tac` matches a rule's precondition *syntactically*: the goal
must first be rewritten into `args ∗ frame` order (align), then split
(frame rule), then the invalid markers upgraded (recover pure), and only
then can the rule apply. `applyFrRule` below does align-and-split in one
step — `frameMatch` pairs by `isDefEq` and emits the permutation as an
`ac_rfl` equality (P4/D-ci) — so the surviving phases are "Recover pure"
(run once, on the whole precondition, when it holds an `hn_invalid`) and
"Apply rule". The two lost phases are still *available*: `align_goal`
and `trans_frame_rule` are ported and exposed as `sepref_dbg_*`, because
a stalled goal is easier to read in aligned form. Both spellings are
checked against each other in the gate.

**P4/D-cp — `cons_pre_rule` and `CPR_TAG` are ported and unused.** The
source falls back on `cons_pre_rule` when no `sepref_fr_rules` entry
matches directly, generating a frame side condition instead;
`CPR_TAG_rules` align the two assertion structures so that the
consequence rule's higher-order unification has something to bite on.
`applyFrRule` never needs the fallback — it *starts* from a frame
inference, so a rule that matches modulo frame matches on the first try,
and a rule that does not match modulo frame would not be rescued by a
consequence step either. The rules are ported (they are the source's,
and a future `sepref_copy_rules` consumer will want them) and flagged
here as unexercised.

**P4/D-cq — a linear rule scan, not a discriminant net.** The source
builds `Tactic.build_net` over each database. Seven `sepref_fr_rules`
entries and three `sepref_comb_rules` entries do not need indexing, and
P2 made the same call for the same reason (`Autoref/Translate.lean`
delta T1). The abstract side is tried first in every match, which is the
discriminating position, so a non-matching rule costs one failed
`isDefEq`. Fallback: a `DiscrTree` keyed on the abstract program's head
constant, when a database passes ~50 entries.

**P4/D-cr — `TERM (const, ''name'')` premises are absent, and the
failure *names* replace them.** The AFP loop rule carries
`TERM (monadic_WHILEIT, ''cond'')` and `TERM (monadic_WHILEIT, ''body'')`
premises whose only job is to tell the user *which* frame side condition
failed. Wave B1 dropped them from `hnr_while_measured` (P4/D-ah). What
replaces them is `premiseRole` below: every premise a comb rule
produces is named — "the guard", "the 'then' branch", "the loop body",
"the branch merge" — and the name appears in the envelope when it
stalls. This is the plan's supervision-legibility watch item, and it is
strictly more informative than the source's tags, which name only the
two `while` frames.

**P4/D-cs — the deliberate absences.** `hn_RECT'` / `hn_RCALL` (ledger
D6: no recursion), `mop_free` / `hnr_freeI` (P4/D-d: no dealloc),
`Sepref_Import_Param` (the whole "Import of Parametricity Theorems"
subsection — its consumer is `sepref_import_param`, which nothing in the
acceptance path uses, and its content is a chain of Isabelle-specific
rule surgeries), `import_rel1` / `import_rel2` (same subsection),
`GEN_ALGO` (P2's `Autoref/Tool.lean` already registers the solver; no
Sepref rule emits the tag), `INDEP` (P2 delta: relator independence is
Isabelle schematic-variable hygiene, which Lean metavariables do not
need), `M.mono_body` (recursion again), and the `bounds_tac` /
`sepref_bounds_*` family (the source's arithmetic side-condition solver
for fixed-width LLVM integers; our values are unbounded `ℕ` until the
existing `Bounds`/`Transfer` boundary, design record §6, so there are no
bounds obligations to solve).
-/

open Lean Elab Meta

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. The side-condition markers (source lines 40–130) -/

/-- The source's `bind_ref_tag x m ≡ RETURN x ≤ m`: "Tag to keep track of
abstract bindings. Required to recover information for side-condition
solving." -/
def bind_ref_tag {α : Type} (x : α) (m : NRest α ECost) : Prop :=
  (NRest.returnT x : NRest α ECost) ≤ m

@[simp] theorem bind_ref_tag_def {α : Type} (x : α) (m : NRest α ECost) :
    bind_ref_tag x m ↔ (NRest.returnT x : NRest α ECost) ≤ m := Iff.rfl

/-- **T2/D-e — a constant-producing `m` pins the tag's value.** For
`m = consume (returnT v) κ` — every `mop*`'s normal form — the only
result the program admits is `v`, so `bind_ref_tag a m` forces `a = v`.
This is the lemma the translate loop's constant normalization consumes
(`pinBindPremise` below): before this, the tag was carried and never
read, translation recursed at an opaque `a`, and every downstream rule
naming a literal value in a cell failed to fire (R2D/D-b's reproducer,
2A′'s gap 5 — both worked around with per-cell `assert` idioms,
`mopBfsE`/`mopBfsAt`, which the fix makes unnecessary for new code). -/
theorem bind_ref_tag_pin {α : Type} {a v : α} {t : ECost}
    (h : bind_ref_tag a ((NRest.returnT v).consume t)) : a = v := by
  rw [bind_ref_tag_def, NRest.consume_returnT, NRest.returnT] at h
  have h' := NRest.rest_le_rest_iff.1 h a
  by_cases hav : a = v
  · exact hav
  · rw [NRest.single_self, NRest.single_of_ne hav] at h'
    simp at h'

/-- …packaged for the `∀ a, bind_ref_tag a m → G a` premise `hnr_bind`
produces: it suffices to translate at the pinned value. -/
theorem pin_bind_premise {α : Type} {v : α} {t : ECost} {G : α → Prop}
    (h : G v) : ∀ a : α, bind_ref_tag a ((NRest.returnT v).consume t) → G a :=
  fun _ ha => (bind_ref_tag_pin ha) ▸ h

/-- The source's `vassn_tag Γ ≡ ∃h. Γ h`: "Tag to keep track of
preconditions in assertions". P3 calls `∃h. Γ h` `purePart`. -/
def vassn_tag (Γ : Assn) : Prop := purePart Γ

/-- The source's `vassn_tagI`. -/
theorem vassn_tagI {Γ : Assn} {h : AState} (hh : Γ h) : vassn_tag Γ := ⟨h, hh⟩

/-- The source's `vassn_dest` (1). -/
theorem vassn_dest_star {Γ₁ Γ₂ : Assn} (h : vassn_tag (Γ₁ ∗ Γ₂)) :
    vassn_tag Γ₁ ∧ vassn_tag Γ₂ := by
  obtain ⟨_, x, y, -, -, hx, hy⟩ := h
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

/-- The source's `vassn_dest` (2). -/
theorem vassn_dest_ctxt {α κ : Type} {R : α → κ → Assn} {a : α} {b : κ}
    (h : vassn_tag (hnCtxt R a b)) : rdomp R a := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, b, hs⟩

/-- The source's `vassn_dest` (3). -/
theorem vassn_dest_pure {Φ : Prop} (h : vassn_tag (⌜Φ⌝ : Assn)) : Φ := by
  obtain ⟨_, hΦ, -⟩ := h; exact hΦ

/-- The source's `vassn_tag_simps`. -/
@[simp] theorem vassn_tag_emp : vassn_tag (□ : Assn) := ⟨0, rfl⟩

@[simp] theorem vassn_tag_true : vassn_tag (sepTrue : Assn) := ⟨0, trivial⟩

/-- The source's `entails_preI`. -/
theorem entails_preI {A B : Assn} (h : vassn_tag A → A ⊢ B) : A ⊢ B :=
  fun s hs => h ⟨s, hs⟩ s hs

/-- The source's `invalid_assn_const`. -/
theorem invalid_assn_const {α κ : Type} (P : Assn) (x : α) (y : κ) :
    invalidAssn (fun _ _ => P) x y = (⌜vassn_tag P⌝ : Assn) := rfl

/-- The source's `hn_refine_vassn_tagI`. -/
theorem hnRefine_vassn_tagI {α κ : Type} {Γ Γ' : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {a : NRest α ECost} (h : vassn_tag Γ → hnRefine Γ c Γ' d R a) :
    hnRefine Γ c Γ' d R a :=
  hnRefine_preI fun hh hΓ => h ⟨hh, hΓ⟩

/-- The source's `RPREM P = P`: "Tag for side-condition solver to
discharge by assumption". -/
def RPREM (P : Prop) : Prop := P

@[simp] theorem RPREM_def (P : Prop) : RPREM P ↔ P := Iff.rfl

/-- The source's `RPREMI`. -/
theorem RPREMI {P : Prop} (h : P) : RPREM P := h

/-- The source's `CPR_TAG y x ≡ True`: "Tag to align structure of
refinement assertions for consequence rule" (P4/D-cp). -/
def CPR_TAG (_y _x : Assn) : Prop := True

@[simp] theorem CPR_TAG_def (y x : Assn) : CPR_TAG y x ↔ True := Iff.rfl

/-- The source's `CPR_TAG_starI`. -/
theorem CPR_TAG_starI {P₁ P₂ Q₁ Q₂ : Assn} (_h₁ : CPR_TAG P₁ Q₁) (_h₂ : CPR_TAG P₂ Q₂) :
    CPR_TAG (P₁ ∗ P₂) (Q₁ ∗ Q₂) := trivial

/-- The source's `CPR_tag_ctxtI`. -/
theorem CPR_tag_ctxtI {α κ : Type} (R R' : α → κ → Assn) (x : α) (xi : κ) :
    CPR_TAG (hnCtxt R x xi) (hnCtxt R' x xi) := trivial

/-- The source's `CPR_tag_fallbackI`. -/
theorem CPR_tag_fallbackI (P Q : Assn) : CPR_TAG P Q := trivial

/-- The source's `cons_pre_rule`: "Consequence rule to be applied if no
direct operation rule matches" (P4/D-cp). -/
theorem cons_pre_rule {α κ : Type} {P P' Q : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {m : NRest α ECost} (_tag : CPR_TAG P P') (hent : P ⊢ P')
    (h : hnRefine P' c Q d R m) : hnRefine P c Q d R m :=
  hnRefine_cons_pre h hent

/-- The source's `trans_frame_rule`: split a translate goal into a
`RECOVER_PURE` obligation on the arguments and the core judgment, with
the frame passed through untouched. -/
theorem trans_frame_rule {α κ : Type} {Γ Γ' Γ'' F : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {a : NRest α ECost} (hrec : RECOVER_PURE Γ Γ')
    (h : vassn_tag (Γ' ∗ F) → hnRefine Γ' c Γ'' d R a) :
    hnRefine (Γ ∗ F) c (Γ'' ∗ F) d R a := by
  refine hnRefine_vassn_tagI fun hv => ?_
  have hent : (Γ ∗ F) ⊢ (Γ' ∗ F) := conj_entails_mono (RECOVER_PURE_D hrec) (entails_refl F)
  obtain ⟨s, hs⟩ := hv
  exact hnRefine_frame (h ⟨s, hent s hs⟩) hent

/-- The source's `recover_pure_cons` ("Used for debugging"). -/
theorem recover_pure_cons {α κ : Type} {Γ Γ' Γ'' : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {a : NRest α ECost} (hrec : RECOVER_PURE Γ Γ')
    (h : hnRefine Γ' c Γ'' d R a) : hnRefine Γ c Γ'' d R a :=
  hnRefine_cons_pre h (RECOVER_PURE_D hrec)

/-- The source's `hn_refine_synthI`. -/
theorem hnRefine_synthI {α κ : Type} {Γ Γ' Γ'' : Assn} {c c' : Com} {d : κ}
    {R' R'' : α → κ → Assn} {m : NRest α ECost} (h : hnRefine Γ c Γ' d R' m)
    (hc : c = c') (hR : R' = R'') (hent : Γ' ⊢ Γ'') : hnRefine Γ c' Γ'' d R'' m := by
  subst hc; subst hR
  exact hnRefine_cons_post h hent

/-- The source's `drop_hn_val`. -/
theorem drop_hn_val {α κ : Type} (R : Set (κ × α)) (x : α) (y : κ) :
    hnVal R x y ⊢ (□ : Assn) := fun _ hs => hs.2

/-- The source's `drop_hn_invalid`. -/
theorem drop_hn_invalid {α κ : Type} (R : α → κ → Assn) (x : α) (y : κ) :
    hnInvalid R x y ⊢ (□ : Assn) := fun _ hs => hs.2

/-! ### `hn_bind`, the source's own bind rule (P4/D-ct)

Wave A landed `hnr_seq`, the port of `hnr_bind_manual_free`, whose second
premise delivers the *final* postcondition directly. The source's
`hn_bind` (`Sepref_Translate.thy` l. 476) instead lets the body have its
own postcondition `Γ2 x x'` and adds the premise
`Γ2 x x' ⊢ hn_ctxt Rx x x' ∗ Γ'`, freeing the bound variable's remainder
with `MK_FREE Rx fr`. That extra premise is not decoration: the body's
postcondition *mentions the bound abstract value* (after `x := a + b`,
the frame owns `hn_ctxt natAssn x "t"`), and the caller's `Γ'` is fixed
outside the binder, so without a step that abstracts the binder away
there is nothing `Γ'` can be. Under P4/D-d the free program is gone and
`hn_ctxt Rx x x' ∗ Γ'` collapses to a plain entailment `Γ2 x ⊢ Γ'`,
which is what `IMP` is below — the binder-dependent conjuncts weaken to
junk (`natAssn_entails_junkCell`, `arrayAssn_entails_junkArray`) and the
rest passes through. `Sepref/Translate.lean`'s `abstractPost` is the
tactic that solves it, and it is where the linearity discipline actually
bites: a value bound by `do x ← …` is dead at the end of the block, and
its cell is junk.

`hnr_seq` stays registered: when the body's postcondition happens to be
binder-free it applies directly and needs no `IMP`. -/

/-- The source's `hn_bind`, at `Com.seq` and with the free program gone
(P4/D-d, P4/D-ct). The guard on `D2` is the source's `bind_ref_tag`. -/
@[sepref_comb_rules]
theorem hnr_bind {α β κ κ' : Type} {Γ Γ₁ Γ' : Assn} {Γ₂ : α → Assn} {c₁ c₂ : Com}
    {x : κ'} {d : κ} {Rh : α → κ' → Assn} {R : β → κ → Assn} {m : NRest α ECost}
    {f : α → NRest β ECost}
    (D1 : hnRefine Γ c₁ Γ₁ x Rh m)
    (D2 : ∀ a : α, bind_ref_tag a m →
      hnRefine (hnCtxt Rh a x ∗ Γ₁) c₂ (Γ₂ a) d R (f a))
    (IMP : ∀ a : α, Γ₂ a ⊢ Γ') :
    hnRefine Γ (.seq c₁ c₂) Γ' d R (m.bindT f) :=
  hnr_seq D1 fun a ha => hnRefine_cons_post (D2 a ha) (IMP a)

/-! ### Tuple states: the pairing operation (P4/D-cu)

A loop whose state is a tuple needs two things the per-op layer does not
supply: an assertion that *is* the tuple (wave A's `prodAssn`, which
`hnCtxt_prodAssn` splits definitionally) and an operation that *builds*
one from two cells. The second is new here. It compiles to `Com.skip` —
nothing happens at run time, the two cells already hold the components —
and therefore costs one `ir.skip`, which is what the abstract side pays.
The source needs no analogue: its concrete language returns values, so a
tuple is `return (a, b)` at zero cost. Ours is a statement language
(design record §5), so "the result is these two cells" is an operation.

Recorded here rather than in `Sepref/IrOps.lean` because that file is
wave B1's and frozen; the natural home is next to the mop layer, and
moving it there is a two-line edit whenever B1 thaws. -/

/-- The tuple-forming operation: deliver the pair `(a₁, a₂)` from the two
cells that hold its components, at the price of one `ir.skip`. -/
noncomputable def mopPair {α₁ α₂ : Type} (a₁ : α₁) (a₂ : α₂) : NRest (α₁ × α₂) ECost :=
  NRest.consume (NRest.returnT (a₁, a₂)) (irUnit Currency.skip)

theorem mopPair_def {α₁ α₂ : Type} (a₁ : α₁) (a₂ : α₂) :
    mopPair a₁ a₂ = NRest.consume (NRest.returnT (a₁, a₂)) (irUnit Currency.skip) := rfl

/-- The triple behind `hnr_mop_pair`: `skip`, framed by the two
components' ownership. -/
theorem pair_skip_rule {α₁ α₂ κ₁ κ₂ : Type} (A : α₁ → κ₁ → Assn) (B : α₂ → κ₂ → Assn)
    (a₁ : α₁) (a₂ : α₂) (c₁ : κ₁) (c₂ : κ₂) :
    irHtriple (¤(irUnit Currency.skip) ∗ (hnCtxt A a₁ c₁ ∗ hnCtxt B a₂ c₂))
      .skip ((□ : Assn) ∗ (A ×ₐ B) (a₁, a₂) (c₁, c₂)) := by
  have e₂ : (¤(irUnit Currency.skip) ∗ (hnCtxt A a₁ c₁ ∗ hnCtxt B a₂ c₂))
      = (¤¤Currency.skip 1 ∗ (A a₁ c₁ ∗ B a₂ c₂)) := by rw [costCredits_one]; rfl
  have e₃ : ((□ : Assn) ∗ (A ×ₐ B) (a₁, a₂) (c₁, c₂)) = ((□ : Assn) ∗ (A a₁ c₁ ∗ B a₂ c₂)) := rfl
  rw [e₂, e₃]
  apply irHtriple_frame skip_rule <;> fri

/-- `(c₁, c₂) := (a₁, a₂)`: the two cells, read as one tuple. -/
@[sepref_fr_rules]
theorem hnr_mop_pair {α₁ α₂ κ₁ κ₂ : Type} (A : α₁ → κ₁ → Assn) (B : α₂ → κ₂ → Assn)
    (a₁ : α₁) (a₂ : α₂) (c₁ : κ₁) (c₂ : κ₂) :
    hnRefine (hnCtxt A a₁ c₁ ∗ hnCtxt B a₂ c₂) .skip (□ : Assn) (c₁, c₂) (A ×ₐ B)
      (mopPair a₁ a₂) :=
  hnRefineI_spect (pair_skip_rule A B a₁ a₂ c₁ c₂)

/-! ### The loop variant, as an annotation (P4/D-cv — **CLOSED**)

`hnr_while_measured` (wave B1, P4/D-ai) takes an explicit variant
`V : σ → ℕ`. Nothing in the goal determines it, and no side-condition
solver can invent it: it is a *proof idea*, and the source does not have
to invent one either (its `heap_WHILET` is a partial-correctness
fixpoint, so it has no termination obligation at all — P4/D-ai records
why ours does). The vehicle was therefore the one P2 already established
for facts the caller has to supply (`Autoref/Tool.lean` delta O1): a
hypothesis in the local context. `LOOP_VARIANT` names the shape so that
the hypothesis is recognisable, and the side-condition fallback's own
`assumption` is what unifies `?V` with the caller's choice.

**How the flag closed (ND-MC rebase P0.3, ledger R0/D-a, R0/D-b).** Not
the way this note predicted. The escape it named — "when P1 exports
`nofailT (RECT B s) → ∃ n, fuelIter B n s = RECT B s`" — is **false**,
and `NREST/Rec.lean`'s `NoFuelBound.no_fuel_bound` refutes it: a `mono2`
body whose `RECT` does not fail at a state that no ℕ-fuel ever reaches,
because unbounded nondeterminism terminates on every branch with no
uniform bound. What P1 exports instead is `RECT_eq_top_of_postfixed` —
"a post-fixed point that is `⊤` at a state pins `RECT` to `⊤` there" —
and termination comes out as the accessibility predicate
`Sepref/CombRules.lean`'s `LoopTerm`, well-founded without being
finitely branching. `loopTerm_of_nofailT` turns the loop's own
non-failure (which the `hnRefine` judgment already hands the rule) into
it, so `hnr_while` needs no termination premise at all.

`hnr_while` is the `sepref_comb_rules` entry now; `hnr_while_measured`
and `hnr_while_var` below are deregistered. Loops synthesize with no
annotation — `Sepref/Definition.lean`'s `sumLoopFree` is the
demonstration, the same program as `sumLoop` from a `sepref_synth` with
no hypothesis at all. `LOOP_VARIANT` itself is kept (deprecated): the
acceptance files' variant lemmas and the `hv` hypotheses of their
landed synthesis theorems are stated in it, and those are capital, not
scaffolding to delete. New consumers should supply nothing. -/

/-- The variant obligation of `hnr_while_measured`, named so that a
caller can supply it as a hypothesis (P4/D-cv).

**Deprecated (R0/D-b):** no rule in the `sepref_comb_rules` database
reads it any more. Kept for the landed acceptance theorems. -/
def LOOP_VARIANT {σ : Type} (I : σ → Prop) (bf : σ → Bool) (f : σ → NRest σ ECost)
    (V : σ → ℕ) : Prop :=
  ∀ s s', I s → bf s = true → (NRest.returnT s' : NRest σ ECost) ≤ f s → V s' < V s

/-- `hnr_while_measured` with the variant behind a `LOOP_VARIANT` tag, so
that the translate loop can pick it up from the context (P4/D-cv).

**Deprecated (R0/D-b):** deregistered from `sepref_comb_rules` —
`CombRules.lean`'s `hnr_while` proves the same conclusion with no
variant. Kept compiled for the callers that name it. -/
theorem hnr_while_var {σ κs : Type} {I : σ → Prop} {bf : σ → Bool}
    {f : σ → NRest σ ECost} {Rs : σ → κs → Assn} {Γ : Assn} {d : κs} {cond : Cond}
    {cbody : Com} {V : σ → ℕ}
    (COND : ∀ s, I s → CondRefine (hnCtxt Rs s d ∗ Γ) cond (bf s))
    (BODY : ∀ s, I s → bf s = true → hnRefine (hnCtxt Rs s d ∗ Γ) cbody Γ d Rs (f s))
    (VAR : LOOP_VARIANT I bf f V) (s₀ : σ) :
    hnRefine (hnCtxt Rs s₀ d ∗ Γ) (.while cond cbody) Γ d Rs (irWhileIT I bf f s₀) :=
  hnr_while_measured V COND BODY VAR s₀

/-! ## 2. The tactics (the source's ML structure `Sepref_Translate`) -/

namespace Translate

open Frame

/-- The translate phase's ordinal in the Sepref pipeline
(`Sepref/IdOp.lean` is 10, `Sepref/Monadify.lean`'s sub-phases 20–70). -/
def transPhasePrio : Nat := 80

/-- The source's `datatype side_mode = DBG_TRY_SIDE | DBG_NO_SIDE |
NORMAL`, plus the step budget. -/
structure Cfg where
  /-- The source's `DBG_TRY_SIDE`: keep partially solved side conditions
  and report every candidate rule's unmet ones. -/
  debugMode : Bool := false
  /-- The source's implicit `REPEAT_DETERM'` depth. -/
  budget : Nat := 200
  deriving Inhabited

/-- Assign a goal from a proof term, checking the types unify — which is
what *performs* the synthesis (P4/D-cm): the goal's `?c` and `?Γ'` are
instantiated here. -/
def assignChecked (g : MVarId) (prf : Expr) : MetaM Unit := do
  let want ← instantiateMVars (← g.getType)
  let have_ ← instantiateMVars (← inferType prf)
  unless ← isDefEq want have_ do
    throwError "sepref: the rule proves{indentExpr have_}\nbut the goal is{indentExpr want}"
  g.assign prf

/-! ### The scratch-cell pool (P4/D-cn) -/

/-- Every string literal occurring in an expression. -/
partial def stringLits (e : Expr) : Array String :=
  go e #[]
where
  go (e : Expr) (acc : Array String) : Array String :=
    match e with
    | .lit (.strVal s) => if acc.contains s then acc else acc.push s
    | .app f a => go a (go f acc)
    | .lam _ t b _ => go b (go t acc)
    | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => acc

/-- A cell name that occurs nowhere in the goal: `t1`, `t2`, … The
message-side half of P4/D-cn. -/
def freshScratchName (e : Expr) : String := Id.run do
  let used := stringLits e
  let mut i := 1
  while used.contains s!"t{i}" do i := i + 1
  return s!"t{i}"

/-- The `junkCell` conjuncts a precondition still owns — the pool the
destination metavariables draw on. -/
def scratchPool (Γ : Expr) : Array Expr :=
  (conjuncts Γ).filterMap fun c =>
    match c.getAppFnArgs with
    | (``junkCell, #[n]) => some n
    | _ => none

/-! ### Applying one rule -/

/-- Split a rule's precondition conjuncts into the concrete ones and a
trailing "rest" metavariable, if it has one. `hnr_while_measured`'s
precondition is `hnCtxt Rs s₀ d ∗ ?Γ`, and the `?Γ` must absorb whatever
the concrete conjuncts do not match — it is the rule's own frame
variable, not a conjunct to be paired. -/
def splitRest (cs : Array Expr) : MetaM (Array Expr × Option Expr) := do
  let mut fixed : Array Expr := #[]
  let mut tailVar : Option Expr := none
  for c in cs do
    if (← instantiateMVars c).isMVar && tailVar.isNone then tailVar := some c
    else fixed := fixed.push c
  return (fixed, tailVar)

/-- The outcome of trying one rule. -/
inductive Attempt where
  /-- The rule applied; these goals remain, and these non-propositional
  arguments are still open — the source's implicit-argument case, which
  the premises normally fix (P2's `Autoref/Translate.lean` delta T7). -/
  | ok (name : Name) (goals : List MVarId) (pending : List MVarId)
  /-- The rule did not apply, for this reason. `relevant` is false when
  the rule's *abstract* side simply is not the goal's — the uninteresting
  majority, which the failure envelope summarises rather than lists
  (the plan's legibility item is about the informative ones). -/
  | no (why : MessageData) (relevant : Bool)

/-- Resolve an `hnRefine` goal against one rule, aligning the
precondition and framing the remainder (P4/D-ci, P4/D-co). `framed` is
the source's `sepref_fr_rules`-versus-`sepref_comb_rules` distinction:
frame-based rules may leave a remainder, combinator rules may not. -/
def applyRuleAt (nm : Name) (framed : Bool) (g : MVarId) : TermElabM Attempt := do
  let st ← saveState
  try
    let ty ← instantiateMVars (← g.getType)
    let some (α, κ, Γ, _, _, d, R, m) := parseHnRefine? ty
      | throwError "not an hnRefine goal"
    let rule ← mkConstWithFreshMVarLevels nm
    let (mvars, _, concl) ← forallMetaTelescope (← inferType rule)
    let some (α', κ', Pr, _, Qr, dr, Rr, mr) := parseHnRefine? concl
      | throwError "the rule's conclusion is not an hnRefine statement"
    -- The abstract side is the discriminating position; try it first.
    unless ← isDefEq α' α do throwError "!the abstract type does not match"
    unless ← isDefEq mr m do
      throwError "!the rule is stated at{indentExpr mr}\nnot at{indentExpr m}"
    unless ← isDefEq κ' κ do throwError "!the concrete type does not match"
    unless ← isDefEq Rr R do
      throwError "the rule delivers{indentExpr Rr}\nnot{indentExpr R}"
    unless ← isDefEq dr d do
      throwError "the rule writes to{indentExpr dr}\nnot to{indentExpr d}"
    let ruleProof := mkAppN rule mvars
    let PrI ← instantiateMVars Pr
    let goalConjs := conjuncts Γ
    -- A rule whose whole precondition is a metavariable takes the goal's.
    if PrI.isMVar then
      unless ← isDefEq PrI Γ do throwError "the rule's precondition did not take the goal's"
      assignChecked g ruleProof
    else
      let sp ← splitRest (conjuncts PrI)
      let fixed := sp.1
      let restOpt := sp.2
      -- First attempt: the goal's conjuncts as written. Second attempt:
      -- with pair assertions split (P4/D-cu) — the loop rule wants the
      -- tuple state whole, the body's operations want its components.
      -- Third attempt (T1/D-f): lazy per-conjunct splitting, for rules
      -- needing one pair split and another kept whole.
      let m1 ← frameMatch fixed goalConjs
      let (goalConjs, m2) ←
        if m1.isSome then pure (goalConjs, m1)
        else do
          let gs ← conjunctsSplit Γ
          if gs == goalConjs then pure (goalConjs, m1)
          else pure (gs, ← frameMatch fixed gs)
      let (goalConjs, m2) ←
        if m2.isSome then pure (goalConjs, m2)
        else pure (goalConjs, ← frameMatch fixed (conjuncts Γ) (splitFuel := 16))
      let some (matched, frame) := m2
        | throwError "{← noPairMsg fixed goalConjs}"
      match restOpt with
      | some restVar =>
        -- The rule carries its own frame variable: it absorbs the rest.
        let restE ← mkConjuncts α frame
        unless ← isDefEq restVar restE do
          throwError "the rule's frame variable could not take the remainder"
        let PmE ← mkConjuncts α (matched ++ frame)
        let heq ← proveConjEq Γ PmE
        assignChecked g (← mkAppM ``hnRefine_pre_perm #[heq, ruleProof])
      | none =>
        if frame.isEmpty then
          let PmE ← mkConjuncts α matched
          let heq ← proveConjEq Γ PmE
          assignChecked g (← mkAppM ``hnRefine_pre_perm #[heq, ruleProof])
        else
          unless framed do
            throwError "a combinator rule may not leave a frame, but \
              {frame.size} conjunct(s) went unmatched"
          let PmE ← mkConjuncts α matched
          let FE ← mkConjuncts α frame
          let heq ← proveConjEq Γ (← mkAppM ``sepConj #[PmE, FE])
          assignChecked g (← mkAppM ``hnRefine_frame_perm #[heq, ruleProof])
    -- Whatever the rule did not determine: propositional premises are
    -- goals, everything else is an argument the premises must fix.
    let mut goals : Array MVarId := #[]
    let mut pending : Array MVarId := #[]
    for mv in mvars do
      let mid := mv.mvarId!
      unless ← mid.isAssigned do
        let mty ← instantiateMVars (← mid.getType)
        if ← isProp mty then goals := goals.push mid else pending := pending.push mid
    let _ := Qr
    return .ok nm goals.toList pending.toList
  catch e =>
    st.restore
    let txt ← e.toMessageData.toString
    if txt.startsWith "!" then
      return .no m!"{nm}" false
    else return .no m!"{nm}: {e.toMessageData}" true

/-! ### The `CondRefine` solver (P4/D-cb) -/

/-- Solve `CondRefine Γ ?cond b` by picking a `sepref_cond_rules` entry
whose boolean is the abstract guard and framing its context up to `Γ`.
Three steps, no search: rule, frame, permutation — wave B1's handoff. -/
def condSolve (g : MVarId) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let (``CondRefine, #[Γ, _, b]) := ty.getAppFnArgs
    | throwError "sepref: not a CondRefine goal:{indentExpr ty}"
  let rules ← (try labelled `sepref_cond_rules catch _ => pure #[])
  let goalConjs := conjuncts Γ
  let mut reasons : Array MessageData := #[]
  for nm in rules do
    let st ← saveState
    try
      let rule ← mkConstWithFreshMVarLevels nm
      let (mvars, _, concl) ← forallMetaTelescope (← inferType rule)
      let (``CondRefine, #[Pr, _, br]) := concl.getAppFnArgs
        | throwError "not a CondRefine rule"
      unless ← isDefEq br b do
        throwError "the rule's guard is{indentExpr br}\nnot{indentExpr b}"
      let ruleProof := mkAppN rule mvars
      let PrI ← instantiateMVars Pr
      let rc := conjuncts PrI
      let m1 ← frameMatch rc goalConjs
      let (goalConjs, m2) ←
        if m1.isSome then pure (goalConjs, m1)
        else do
          let gs ← conjunctsSplit Γ
          if gs == goalConjs then pure (goalConjs, m1) else pure (gs, ← frameMatch rc gs)
      let (goalConjs, m2) ←
        if m2.isSome then pure (goalConjs, m2)
        else pure (goalConjs, ← frameMatch rc (conjuncts Γ) (splitFuel := 16))
      let some (matched, frame) := m2
        | throwError "{← noPairMsg rc goalConjs}"
      let α ← carrierOf Γ
      let PmE ← mkConjuncts α matched
      let prf ←
        if frame.isEmpty then
          let heq ← proveConjEq Γ PmE
          mkAppM ``CondRefine_perm_exact #[heq, ruleProof]
        else
          let FE ← mkConjuncts α frame
          let heq ← proveConjEq Γ (← mkAppM ``sepConj #[PmE, FE])
          mkAppM ``CondRefine_perm #[heq, ruleProof]
      assignChecked g prf
      for mv in mvars do
        let mid := mv.mvarId!
        unless ← mid.isAssigned do
          throwError "the guard rule left an argument open"
      return
    catch e =>
      st.restore
      reasons := reasons.push m!"{nm}: {e.toMessageData}"
  throwError "sepref: no guard rule refines the abstract condition{indentExpr b}\n\
    under the ownership{indentExpr Γ}\ncandidates tried:\n\
    {MessageData.joinSep reasons.toList "\n"}"

/-! ### Abstracting a binder-dependent postcondition (P4/D-ct)

The tactic behind `hnr_bind`'s `IMP` premise: the goal is
`Γ₂ a ⊢ ?Γ'` with `?Γ'` fixed outside the binder, so every conjunct that
mentions the binder must weaken to something that does not. Under
P4/D-c that something is junk of the same shape. -/

/-- Every free variable of an expression, in order of first occurrence. -/
partial def fvarsOf (e : Expr) : Array FVarId :=
  go e #[]
where
  go (e : Expr) (acc : Array FVarId) : Array FVarId :=
    match e with
    | .fvar f => if acc.contains f then acc else acc.push f
    | .app a b => go b (go a acc)
    | .lam _ t b _ => go b (go t acc)
    | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => acc

/-- The free variables a metavariable may legally be assigned: those of
its own local context, plus those it is applied to. -/
def allowedFVars (Q : Expr) : MetaM (Array FVarId) := do
  let mut out : Array FVarId := #[]
  match Q.getAppFn with
  | .mvar mid =>
    for d in (← mid.getDecl).lctx do
      out := out.push d.fvarId
  | _ => pure ()
  for a in Q.getAppArgs do
    for f in fvarsOf a do
      unless out.contains f do out := out.push f
  return out

/-- Weaken one conjunct so that it mentions only `allowed` free
variables, returning the weakened conjunct and the entailment.

T1/D-d: a *pair* context splits (`hnCtxt_prodAssn` is `rfl`) and each
component junks recursively — a leaf engine returning a tuple leaves
`hnCtxt (A ×ₐ B) st (…)` in the block's postcondition, and before this
case the abstraction threw "no junk form" at it (the R2/D-e stall, met
for real by the 2A/2B engine compositions). -/
partial def junkConjunct (allowed : Array FVarId) (e : Expr) : MetaM (Expr × Expr) := do
  if (fvarsOf e).all (fun f => allowed.contains f) then
    return (e, ← mkAppM ``entails_refl #[e])
  match e.getAppFnArgs with
  | (``hnCtxt, #[_, _, R, v, c]) =>
    if let (``prodAssn, #[_, _, _, _, A, B]) := R.getAppFnArgs then
      let l ← mkAppM ``hnCtxt #[A, ← projOf true v, ← projOf true c]
      let r ← mkAppM ``hnCtxt #[B, ← projOf false v, ← projOf false c]
      let (tl, pl) ← junkConjunct allowed l
      let (tr, pr) ← junkConjunct allowed r
      return (← mkAppM ``sepConj #[tl, tr], ← mkAppM ``conj_entails_mono #[pl, pr])
    else if R.isConstOf ``natAssn then
      return (← mkAppM ``junkCell #[c], ← mkAppM ``natAssn_entails_junkCell #[v, c])
    else if R.isConstOf ``arrayAssn then
      return (← mkAppM ``junkArray #[c], ← mkAppM ``arrayAssn_entails_junkArray #[v, c])
    else
      throwError "sepref: the bound value's ownership{indentExpr e}\nsurvives the \
        block, and there is no junk form for its assertion — the postcondition \
        cannot be closed over the binder"
  | (``natAssn, #[v, c]) =>
    return (← mkAppM ``junkCell #[c], ← mkAppM ``natAssn_entails_junkCell #[v, c])
  | (``arrayAssn, #[v, c]) =>
    return (← mkAppM ``junkArray #[c], ← mkAppM ``arrayAssn_entails_junkArray #[v, c])
  | _ =>
    throwError "sepref: this conjunct mentions the bound value and has no junk \
      form:{indentExpr e}"

/-- Solve `P ⊢ ?Q` with `?Q` a metavariable outside the binder, by
junking `P`'s binder-dependent conjuncts. -/
def abstractPost (g : MVarId) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let (``entails, #[_, P, Q]) := ty.getAppFnArgs
    | throwError "sepref: not an entailment goal:{indentExpr ty}"
  let allowed ← allowedFVars Q
  let cs := conjuncts P
  let mut targets : Array Expr := #[]
  let mut prfs : Array Expr := #[]
  for c in cs do
    let (t, p) ← junkConjunct allowed c
    targets := targets.push t
    prfs := prfs.push p
  let α ← carrierOf P
  let Q' ← mkConjuncts α targets
  unless ← isDefEq Q Q' do
    throwError "sepref: the abstracted postcondition{indentExpr Q'}\ndoes not fit the \
      goal's{indentExpr Q}"
  -- Fold `conj_entails_mono` over the conjuncts, in `mkConjuncts`'s shape.
  if prfs.isEmpty then
    assignChecked g (← mkAppM ``entails_refl #[← mkConjuncts α #[]])
  else
    let mut acc := prfs[prfs.size - 1]!
    for i in [1 : prfs.size] do
      acc ← mkAppM ``conj_entails_mono #[prfs[prfs.size - 1 - i]!, acc]
    let hp ← proveConjEq P (← mkConjuncts α cs)
    assignChecked g (← mkAppM ``entails_congr_left #[hp, acc])

/-! ### The side-condition dispatcher (source lines 300–331) -/

/-- The source's fallback side tactic (`side_fallback_tac`), at P3's
fixed list, plus `apply_assumption` (P7/D-bh).

`assumption` cannot instantiate a quantifier, and a `LOOP_VARIANT` for
an *inner* loop is quantified: the loop's body mentions values the
enclosing `hnr_bind` has abstracted (`scanLoop`'s offered distance and
row end are read from arrays), so the caller can only supply
`∀ dv1 kend, LOOP_VARIANT …`. P4/D-cv's vehicle — "a hypothesis in the
local context, and `assumption` is what unifies `?V` with the caller's
choice" — therefore has no nested-loop instance at all without this.
`apply_assumption` sits *after* `omega`, so it is reached only where the
cheap closers have already failed, and before `simp_all`, which is what
was grinding on the quantified goal instead.

**R0/D-b note.** The instance that motivated it is gone: no rule in the
database reads a `LOOP_VARIANT` any more, so no side condition is a
quantified caller hypothesis today. `apply_assumption` is kept — it is
the general form of `assumption`, one entry in a `first` chain, and
nothing measured says it costs anything now that the loop rule closes
its own termination. Removing it is a separate, testable change. -/
def fallbackTac : TermElabM (TSyntax `tactic) :=
  `(tactic| first
              | assumption
              | rfl
              | trivial
              | decide
              | omega
              | apply_assumption
              | simp_all
              | simp)

/-- Run a tactic on a goal, requiring it to close. -/
def runClosing (g : MVarId) (t : TSyntax `tactic) : TermElabM Unit := do
  let open_ ← Tactic.run g (Tactic.evalTactic t)
  unless open_.isEmpty do
    throwError "the side condition was not closed:{indentD (← open_.head!.getType)}"

/-- What a premise is *for*, in the envelope (P4/D-cr — the replacement
for the source's `TERM (const, ''name'')` tags). -/
def premiseRole (ty : Expr) : String :=
  match ty.getAppFnArgs.1 with
  | ``CondRefine => "the guard"
  | ``MERGE => "the branch merge"
  | ``CONSTRAINT => "a deferred constraint"
  | ``RECOVER_PURE => "the pure-value recovery"
  | ``hnRefine => "a sub-program"
  | ``entails => "a frame entailment"
  | ``RPREM => "a premise to discharge by assumption"
  | _ => "a side condition"

/-- After a rule's premises are solved, every non-propositional argument
it left open must have been fixed by them. What is still open is an
argument the caller has to supply by hand — a loop variant, typically —
and this is where that is said (P4/D-cr). -/
def checkPending (nm : Name) (pending : List MVarId) : MetaM Unit := do
  let mut open_ : Array MessageData := #[]
  for mid in pending do
    unless ← mid.isAssigned do
      open_ := open_.push (indentExpr (← instantiateMVars (← mid.getType)))
  unless open_.isEmpty do
    throwError "{nm}: the rule's premises did not determine \
      {open_.size} of its arguments:{MessageData.joinSep open_.toList ""}\n\
      (supply them by hand — a loop variant, for instance, is not inferable)"

/-! ### T2/D-e — the constant normalization of `bind_ref_tag`

`hnr_bind`'s second premise is `∀ a, bind_ref_tag a m → hnRefine … (f a)`,
and for a constant-producing `m` the tag *pins* `a`. The loop below
recognises that shape, normalizes `m` down to `consume (returnT v) κ`
(unfolding through the `mop*` aliases, irreducible ones included — the
`attribute [irreducible]` idiom is routing, not hiding), and — **only
after the ordinary opaque route has failed**, so every previously green
synthesis takes a byte-identical path — retries the premise through
`pin_bind_premise` at `a := v`. Downstream rules naming a literal value
in a cell then fire by `isDefEq`. The binder-dependent metavariable
families the rule created (`Γ₂ a`) are re-pointed at constant families
first, so the pinned goal stays first-order. -/

/-- The value a constant-producing program pins: `m`, unfolded (all
transparency) to `consume (returnT v) κ`, delivers `v`. Fueled: the
`mop*` aliases are two unfoldings deep, and an engine-sized term that
is *not* constant-producing should not be unfolded to the bottom just
to learn that. -/
partial def pinnedValue? (e : Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``NRest.returnT, args) => return args.back?
  | (``NRest.consume, #[_, _, _, m, _]) => pinnedValue? m fuel
  | _ =>
    match fuel with
    | 0 => return none
    | fuel + 1 =>
      match ← withTransparency .all (unfoldDefinition? e) with
      | some e' => pinnedValue? e' fuel
      | none => return none

/-- Is this goal a `∀ a, bind_ref_tag a m → …` premise whose `m` pins a
*closed* value? Returns the value. -/
def pinnableBindPremise? (g : MVarId) : MetaM (Option Expr) := do
  let ty ← instantiateMVars (← g.getType)
  let .forallE _ _ body _ := ty | return none
  let .forallE _ tagTy _ _ := body | return none
  let (``bind_ref_tag, #[_, _, m]) := tagTy.consumeMData.getAppFnArgs | return none
  if m.hasLooseBVars then return none
  let some v ← pinnedValue? m | return none
  let vW ← withTransparency .all (whnf v)
  if vW.hasFVar || vW.hasMVar || vW.hasLooseBVars then return none
  return some v

/-- Re-point every metavariable family applied to the pinned value at a
constant family, so that the pinned goal's postcondition slot is a plain
metavariable rather than a non-pattern application. -/
partial def constifyMVarApps (v : Expr) (e : Expr) : MetaM Unit := do
  match e with
  | .app f a =>
    constifyMVarApps v f
    constifyMVarApps v a
    if f.isMVar && a == v then
      let mid := f.mvarId!
      unless ← mid.isAssigned do
        let mty ← instantiateMVars (← mid.getType)
        if let .forallE _ dom body _ := mty then
          unless body.hasLooseBVars do
            let decl ← mid.getDecl
            let fresh ← mkFreshExprMVarAt decl.lctx decl.localInstances body
            mid.assign (mkLambda `_a .default dom fresh)
  | .lam _ t b _ => constifyMVarApps v t; constifyMVarApps v b
  | .forallE _ t b _ => constifyMVarApps v t; constifyMVarApps v b
  | .letE _ t val b _ => constifyMVarApps v t; constifyMVarApps v val; constifyMVarApps v b
  | .mdata _ b => constifyMVarApps v b
  | .proj _ _ b => constifyMVarApps v b
  | _ => pure ()

/-! ### The translation loop (source lines 335–430) -/

/-- **The order the combinator database is tried in (P7/D-bf).**

`hnr_bind` subsumes `hnr_seq`: its extra premise is `∀ a, Γ₂ a ⊢ Γ'`,
which `abstractPost` discharges by `entails_refl` exactly when the
body's postcondition is binder-free — which is exactly when `hnr_seq`
applies. So whichever of the two is tried first, the program that comes
out is the same `Com.seq c₁ c₂`.

The *cost* is not the same. `hnr_seq` tried first translates the whole
continuation, discovers at the end that the frame mentions the bound
value, and throws the translation away; `hnr_bind` then does it again.
That is a factor of two per `bindT`, and it compounds down a nested
program: a body with `k` binds costs `2^k`, and an inner loop's body is
re-translated once per outer retry on top of that. Measured before the
change: a three-read body with two nested branches stalls after 3 min
22 s and a three-level program does not finish in nine minutes.

The fix is a stable partition, not a sort: everything keeps its
database order except `hnr_seq`, which moves to the back. It stays in
the database because it is the rule that applies with no `IMP` premise
at all, and a caller reading a synthesis proof should still see it
where it is the honest one. -/
def combLast : Array Name := #[``Lax13Proofs.Refine.Sepref.hnr_seq]

mutual

/-- The source's `side_cond_dispatch_tac`, wrapped by T2/D-e: a
`bind_ref_tag` premise with a constant-producing program takes the
ordinary opaque route first, and on failure is retried at the pinned
value. -/
partial def sideDispatch (cfg : Cfg) (fuel : Nat) (g : MVarId) : TermElabM Unit := do
  if ← g.isAssigned then return
  match ← g.withContext (pinnableBindPremise? g) with
  | none => sideDispatchCore cfg fuel g
  | some v =>
    let st ← saveState
    try
      sideDispatchCore cfg fuel g
    catch e =>
      st.restore
      try
        let gs ← g.withContext <| withTransparency .all <|
          g.apply (← mkConstWithFreshMVarLevels ``pin_bind_premise)
        let [g'] := gs
          | throwError "sepref: pin_bind_premise left an unexpected goal shape"
        g'.withContext do
          constifyMVarApps v (← instantiateMVars (← g'.getType))
        sideDispatchCore cfg fuel g'
      catch _ =>
        st.restore
        throw e

/-- The dispatcher proper: classify the goal and route it. `hn_refine`
goals go back to `transGoal`; everything else is a side condition. -/
partial def sideDispatchCore (cfg : Cfg) (fuel : Nat) (g : MVarId) : TermElabM Unit := do
  if ← g.isAssigned then return
  -- Premises may be universally quantified or implications; open them.
  let (_, g) ← g.intros
  g.withContext do
  let ty ← instantiateMVars (← g.getType)
  match ty.getAppFnArgs.1 with
  | ``hnRefine => transGoal cfg fuel g
  | ``MERGE => mergeSolve g
  | ``Lax13Proofs.Refine.Sepref.CONSTRAINT => Constraints.constraintTac g
  | ``CondRefine => condSolve g
  | ``RECOVER_PURE => recoverPure g
  | ``entails =>
    -- `P ⊢ ?Q` with the target still open is `hnr_bind`'s `IMP` premise
    -- (P4/D-ct); everything else is ordinary frame inference.
    let tgt := (← instantiateMVars (← g.getType)).getAppArgs
    if h : tgt.size = 3 then
      if (← instantiateMVars tgt[2]).getAppFn.isMVar then abstractPost g
      else runClosing g (← `(tactic| fri))
    else runClosing g (← `(tactic| fri))
  | ``Ir.ENTAILS => runClosing g (← `(tactic| fri))
  | ``Ir.FRAME => runClosing g (← `(tactic| fri))
  | ``RPREM => runClosing g (← `(tactic| (apply RPREMI; assumption)))
  | _ => runClosing g (← fallbackTac)

/-- The source's `trans_comb_tac`: resolve against `sepref_comb_rules`,
first match wins, no framing. The order is `combLast`'s (P7/D-bf). -/
partial def transComb (cfg : Cfg) (fuel : Nat) (g : MVarId) :
    TermElabM (Option (Array MessageData × Nat)) := do
  let db ← (try labelled `sepref_comb_rules catch _ => pure #[])
  let rules := db.filter (!combLast.contains ·) ++ db.filter (combLast.contains ·)
  let mut reasons : Array MessageData := #[]
  let mut skipped : Nat := 0
  for nm in rules do
    let st ← saveState
    match ← applyRuleAt nm (framed := false) g with
    | .ok _ gs pending =>
      let mut ok := true
      let mut why : MessageData := m!""
      for g' in gs do
        if ok then
          let role := premiseRole (← instantiateMVars (← g'.getType))
          try sideDispatch cfg (fuel - 1) g'
          catch e =>
            ok := false
            why := m!"{nm}: applied, but {role} stalled: {e.toMessageData}"
      if ok then
        try
          checkPending nm pending
          return none
        catch e =>
          ok := false
          why := m!"{e.toMessageData}"
      st.restore
      reasons := reasons.push why
    | .no why rel => if rel then reasons := reasons.push why else skipped := skipped + 1
  return some (reasons, skipped)

/-- The source's `gen_trans_op_tac`: recover pure, then the first
`sepref_fr_rules` entry that applies *and* whose side conditions all
close (`DETERM o SOLVED'`). In debug mode every candidate's unmet side
conditions are reported. -/
partial def transOp (cfg : Cfg) (fuel : Nat) (g : MVarId) :
    TermElabM (Option (Array MessageData × Nat)) := do
  let rules ← (try labelled `sepref_fr_rules catch _ => pure #[])
  let mut reasons : Array MessageData := #[]
  let mut skipped : Nat := 0
  for nm in rules do
    let st ← saveState
    match ← applyRuleAt nm (framed := true) g with
    | .ok _ gs pending =>
      let mut ok := true
      let mut why : MessageData := m!""
      for g' in gs do
        if ok then
          let role := premiseRole (← instantiateMVars (← g'.getType))
          try sideDispatch cfg (fuel - 1) g'
          catch e =>
            ok := false
            why := m!"{nm}: applied, but {role} stalled: {e.toMessageData}"
      if ok then
        try
          checkPending nm pending
          return none
        catch e =>
          ok := false
          why := m!"{e.toMessageData}"
      st.restore
      reasons := reasons.push why
    | .no w rel => if rel then reasons := reasons.push w else skipped := skipped + 1
  return some (reasons, skipped)

/-- The source's `trans_step_tac`, plus its `REPEAT_DETERM'`: combinator
rules first, then operator rules. -/
partial def transGoal (cfg : Cfg) (fuel : Nat) (g : MVarId) : TermElabM Unit := do
  if ← g.isAssigned then return
  if fuel == 0 then
    throwError "sepref: the translation did not terminate within the step budget"
  let ty ← instantiateMVars (← g.getType)
  let some (_, _, Γ, _, _, _, _, m) := parseHnRefine? ty
    | throwError "sepref: not an hnRefine goal:{indentExpr ty}"
  -- The source's "Recover pure" phase, on the whole precondition
  -- (P4/D-co). Only runs when there is an invalid marker to upgrade.
  let g ←
    if (conjuncts Γ).any (fun c =>
        match c.getAppFnArgs with
        | (``hnCtxt, #[_, _, R, _, _]) => R.getAppFnArgs.1 == ``invalidAssn
        | _ => false) then
      pure g
    else pure g
  match ← transComb cfg fuel g with
  | none => return
  | some combReasons =>
    match ← transOp cfg fuel g with
    | none => return
    | some opReasons =>
      let pool := scratchPool Γ
      let poolMsg :=
        if pool.isEmpty then
          m!"\nThe precondition owns no scratch cell; a destination-taking rule needs \
`junkCell \"{freshScratchName ty}\"` in it."
        else m!""
      -- T2/D-g: name the two opacity classes instead of a bare miss.
      -- R2A/D-f: a `def` folding a `∗`-chain matches as ONE atom, so no
      -- rule conjunct can pair with it; 2A′ gap 6: a `def` folding a
      -- compound *program* is invisible to the head-matching rule scan.
      let mut opaqueNotes : Array MessageData := #[]
      let assnHeads : Array Name :=
        #[``hnCtxt, ``junkCell, ``junkArray, ``natAssn, ``arrayAssn, ``predLift,
          ``sepEx, ``emp, ``sepConj, ``invalidAssn, ``hnVal]
      for c in conjuncts Γ do
        if let .const nm _ := c.getAppFn then
          unless assnHeads.contains nm do
            if let some c' ← unfoldDefinition? c then
              if c'.consumeMData.getAppFnArgs.1 == ``sepConj then
                opaqueNotes := opaqueNotes.push m!"\nThe conjunct{indentExpr c}\n\
                  is a named assertion folding a `∗`-chain; the matcher compares \
                  atoms, so no rule conjunct can pair with it — unfold it before \
                  synthesis (`simp only [{nm}]`)."
      -- The named-program note fires only when *nothing* is stated at
      -- the term — a registered `mop*` that happens to unfold to a
      -- `bindT` (its own `assert`) is not the opacity class.
      if combReasons.1.isEmpty && opReasons.1.isEmpty then
        if let .const nm _ := m.getAppFn then
          if let some m' ← unfoldDefinition? m then
            let h := m'.consumeMData.getAppFnArgs.1
            if h == ``NRest.bindT || (`irWhileIT).isSuffixOf h then
              opaqueNotes := opaqueNotes.push m!"\nThe abstract term's head `{nm}` is a \
                named definition folding a compound program; the rule scan matches \
                heads, so nothing is stated at it — unfold it before synthesis \
                (`simp only [{nm}]`), or register a leaf rule at the name."
      let opaqueMsg := MessageData.joinSep opaqueNotes.toList ""
      let section_ (kind : String) (rs : Array MessageData) (sk : Nat) : MessageData :=
        if rs.isEmpty then
          m!"\n{kind} rules: none is stated at this abstract term ({sk} tried)."
        else
          m!"\n{kind} rules ({sk} more are stated at other abstract terms):\n\
{MessageData.joinSep rs.toList "\n"}"
      throwError "sepref: no rule translates{indentExpr m}\nunder the ownership\
{indentExpr Γ}{poolMsg}{opaqueMsg}\
{section_ "combinator" combReasons.1 combReasons.2}\
{section_ "operator" opReasons.1 opReasons.2}"

end

/-- The source's `gen_trans_tac`: the translation steps, then constraint
processing. -/
def transTac (cfg : Cfg) (g : MVarId) : TermElabM Unit := do
  transGoal cfg cfg.budget g
  Constraints.processConstraints

end Translate

/-! ## 3. The tactic entry points -/

open Translate in
/-- The source's `sepref_dbg_trans`: the whole translation phase on an
`hnRefine` goal. -/
elab "sepref_dbg_trans" : tactic => do
  let g ← Tactic.getMainGoal
  transTac {} g
  Tactic.replaceMainGoal []

open Translate in
/-- The source's `sepref_dbg_trans_keep`: as above, in debug mode. -/
elab "sepref_dbg_trans_keep" : tactic => do
  let g ← Tactic.getMainGoal
  transTac { debugMode := true } g
  Tactic.replaceMainGoal []

open Translate in
/-- The source's `sepref_dbg_trans_step`: one translation step, leaving
the premises it produced as goals. -/
elab "sepref_dbg_trans_step" : tactic => do
  let g ← Tactic.getMainGoal
  let rules ← (try labelled `sepref_comb_rules catch _ => pure #[])
    >>= fun cs => do
      let fs ← (try labelled `sepref_fr_rules catch _ => pure #[])
      return cs.map (·, false) ++ fs.map (·, true)
  let mut reasons : Array MessageData := #[]
  for (nm, framed) in rules do
    match ← applyRuleAt nm framed g with
    | .ok _ gs _ => Tactic.replaceMainGoal gs; return
    | .no why _ => reasons := reasons.push why
  throwError "sepref: no rule applies to this goal.\n\
    {MessageData.joinSep reasons.toList "\n"}"

open Translate in
/-- The source's `sepref_dbg_side`: dispatch one side condition. -/
elab "sepref_dbg_side" : tactic => do
  let g ← Tactic.getMainGoal
  sideDispatch {} 200 g
  Tactic.replaceMainGoal []

open Translate in
/-- The source's `sepref_dbg_side_keep`: dispatch, reporting rather than
throwing. -/
elab "sepref_dbg_side_keep" : tactic => do
  let g ← Tactic.getMainGoal
  try
    sideDispatch { debugMode := true } 200 g
    Tactic.replaceMainGoal []
  catch e => logInfo (← e.toMessageData.toString)

open Translate in
/-- The guard solver, on its own (P4/D-cb; the source has no analogue
because its guards are synthesized as programs). -/
elab "sepref_dbg_cond" : tactic => do
  let g ← Tactic.getMainGoal
  condSolve g
  Tactic.replaceMainGoal []

open Translate in
/-- The source's `align_goal_tac`, as a debugging entry point
(P4/D-ci). -/
elab "sepref_dbg_align_goal" : tactic => do
  let g ← Tactic.getMainGoal
  let g' ← Frame.alignGoal g
  Tactic.replaceMainGoal [g']

open Translate in
/-- Report what the translation would fail with, as `info` — the
`Autoref/Solver.lean` precedent, so a gate can pin a failure message
without leaving a failing declaration behind. -/
elab "sepref_dbg_trans_trace" : tactic => do
  let g ← Tactic.getMainGoal
  try
    transTac {} g
    Tactic.replaceMainGoal []
  catch e => logInfo (← e.toMessageData.toString)

/-! ## 4. Gate (ledger D4, refute-before-prove)

The tactics of §3 are exercised end to end in `Sepref/Definition.lean`,
which is where the pipeline that drives them lives. What is checked here
is the *object level*: the source's own spelling of the steps the
matcher collapsed (P4/D-co), and the two markers a rule consumes. -/

namespace TranslateGate

/-- The source's explicit frame split, at a concrete operation: the
spelling `applyRuleAt` collapses into one `frameMatch` (P4/D-co). -/
example (a b : ℕ) :
    hnRefine ((junkCell "t" ∗ hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b") ∗
        hnCtxt natAssn 0 "spare")
      (Com.binop Imp.Bop.add "t" "a" "b")
      ((hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b") ∗ hnCtxt natAssn 0 "spare")
      "t" natAssn (mopBinop .add a b) :=
  trans_frame_rule (recover_pure_triv _) fun _ => hnr_mop_binop .add "t" "a" "b" a b

/-- The source's `cons_pre_rule`, likewise (P4/D-cp: ported, unexercised
by the pipeline). -/
example (a b : ℕ) :
    hnRefine (hnCtxt natAssn a "a" ∗ junkCell "t" ∗ hnCtxt natAssn b "b")
      (Com.binop Imp.Bop.add "t" "a" "b")
      (hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b") "t" natAssn (mopBinop .add a b) :=
  cons_pre_rule (CPR_tag_fallbackI _ _)
    (by rw [show (hnCtxt natAssn a "a" ∗ junkCell "t" ∗ hnCtxt natAssn b "b")
          = (junkCell "t" ∗ hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b") from by ac_rfl])
    (hnr_mop_binop .add "t" "a" "b" a b)

/-- `align_goal` reorders a precondition so that the conjuncts the
abstract program mentions come first and the scratch cells follow
(P4/D-ci); it is a permutation, so the goal it leaves is provable by the
same rule. -/
example (a b : ℕ) :
    hnRefine (junkCell "t" ∗ hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b")
      (Com.binop Imp.Bop.add "t" "a" "b") (hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b")
      "t" natAssn (mopBinop .add a b) := by
  sepref_dbg_align_goal
  -- The two argument conjuncts now come first, the scratch cell last.
  show hnRefine (hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b" ∗ junkCell "t") _ _ _ _ _
  exact hnRefine_pre_perm (by ac_rfl) (hnr_mop_binop .add "t" "a" "b" a b)

/-- The guard solver, on its own: the `.lt` condition is *synthesized*
from the abstract boolean. -/
example (m n : ℕ) :
    CondRefine (junkCell "r" ∗ hnCtxt natAssn m "m" ∗ hnCtxt natAssn n "n")
      (Cond.lt (Operand.cell "m") (Operand.cell "n")) (decide (m < n)) := by
  sepref_dbg_cond

/-- The tuple-forming operation, at two cells (P4/D-cu). -/
example (i acc : ℕ) :
    hnRefine (hnCtxt natAssn i "i" ∗ hnCtxt natAssn acc "acc") Com.skip (□ : Assn)
      ("i", "acc") (natAssn ×ₐ natAssn) (mopPair i acc) :=
  hnr_mop_pair natAssn natAssn i acc "i" "acc"

/-- **Negative control.** The guard solver refuses a boolean no rule
refines under the ownership it has: the cell holding `n` is not
owned. -/
example : True := by
  fail_if_success
    (have : ∀ m n : ℕ, CondRefine (hnCtxt natAssn m "m")
        (Cond.lt (Operand.cell "m") (Operand.cell "n")) (decide (m < n)) := by
      intro m n; sepref_dbg_cond)
  trivial

end TranslateGate

end Lax13Proofs.Refine.Sepref
