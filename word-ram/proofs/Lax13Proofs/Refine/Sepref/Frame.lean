import Lax13Proofs.Refine.Sepref.Constraints
import Lax13Proofs.Refine.Sepref.CombRules
import Lax13Proofs.Refine.Ir.SepSolver

/-!
Frame inference and branch merging: the port of
`thys/sepref/Sepref_Frame.thy`.

Source pin as `Sepref/Basic.lean`'s header (`isabelle_llvm_time`
@ `42dd7f5`); the theory was fetched whole (558 lines) and is the
authority for everything below — its object level (lines 21–163) is
ported rule for rule, and its ML structure `Sepref_Frame` (lines
166–526) is the specification of the tactics. The header comment the
port is measured against:

```
The first tactic, frame_tac, is a standard frame inference tactic,
based on the assumption that only hn_ctxt-assertions need to be matched.

The second tactic, merge_tac, resolves entailments of the form
  F1 ∨⇩A F2 ⟹⇩t ?F
that occur during translation of if and case statements.
It synthesizes a new frame ?F, where refinements of variables
with equal refinements in F1 and F2 are preserved,
and the others are set to hn_invalid.
```

## Judgment calls

**T1/D-a — `merge_tac` pairs in the split spelling.** (ND-MC rebase
tool wave T1.) `mergeSolve` normalizes both branch postconditions with
`conjunctsSplit` before pairing: an arm that consumed a projection of a
bound tuple leaves its post with the pair ownership split while the
other arm's is whole, the two spell the same assertion (`rfl`), and
pairing by cell key could not see it. This was the P2/2B/D-a stall —
`hnr_If` failing inside a nested translation, then the combinator
phase's retry cascade burning the heartbeat budget "at `whnf`". The
`degRowF` reproducer family is `Examples/T1Probe.lean` (R1/R2 pass
before the fix, R3a/R3 stall before and pass after, `r3Loop` pinned).

**T1/D-b — `fri` sees pair contexts in the split spelling** (the
attribute registration at `hnCtxt_prodAssn`/`prodAssn_apply` below;
same disease in the frame solver, met by the 2A leaf-composition
probe). The `fri` direction of P4/D-cu's `conjunctsSplit`; acceptance
is `Lax3Proofs.Refine.T1FriProbe.bfsThenSweep` in the ND-MC package.

**P4/D-ch — `frame_tac` is P3's `fri`, with the Sepref match rules in
its rule base.** The source's `frame_tac` is
`prepare_frame_tac THEN' resolve conj_entails_mono THEN_ALL_NEW_LIST
[frame_loop_tac, solve_remainder_tac]`: pair the two sides' `hn_ctxt`
conjuncts by their concrete term, split the pairing with
`conj_entails_mono`, close each pair with `frame_thms` +
`sepref_frame_match_rules`, and mop up the remainder with
`frame_rem_thms`. P3's `fri` (`Ir/SepSolver.lean`, the port of
`Frame_Infer.thy`, which `Sepref_Frame.thy` itself builds on rather than
redefining) is the *same* algorithm with the same three parts —
per-conjunct pairing, a `fri_rules` step set, and a residue-versus-frame
end phase — already built, already tested, and already carrying the
failure messages the plan's legibility item asks for. So the five
`frame_thms` and the weakenings of P4/D-c are registered as `fri_rules`
and `frame_tac` is `fri`. What is *added* on top, because the source has
it and `fri` does not, is `prepare_frame` (below): the source's
`prepare_fi_conv`, which reorders both sides so that paired conjuncts
align, and which is what makes a *failure* legible — it is the pass that
knows which target conjunct had no partner. What is *not* added is a
per-pair `conj_entails_mono` split: `fri` matches conjunct against
conjunct directly. Fallback if the two solvers must diverge: `frameMatch` below is a standalone, exact, permutation-only
matcher (it is what the translate phase uses), and `frame_tac` can be
re-based on it in a dozen lines.

**T1/D-e, T1/D-f — junk-guarded pairing, and lazy pair splitting as a
third attempt.** See `absAgree` and `matchLoop`'s docstrings; both are
ND-MC rebase tool-wave T1 additions. D-e closes P7/D-bg's remaining
hole (an open-relator rule conjunct eating a junk conjunct); D-f is
the per-conjunct split the mixed whole/split matching shapes need
(`hnr_mop_pair` binding one component of an earlier result to a fresh
pack). D-f is reachable only through `applyRuleAt`/`condSolve`'s
attempt-3, so every synthesis that was green before T1 takes an
identical path.

**P4/D-ci — the *rule-application* alignment lives in the matcher, not
in a goal conversion.** The source's `align_goal_conv` rewrites the
`hn_refine` goal's precondition into `args ∗ frame` order *before*
resolution, because Isabelle's `resolve_tac` matches syntactically and
would otherwise fail on a permuted precondition. `Sepref/Translate.lean`
aligns instead at the moment of application: `frameMatch` pairs the
rule's precondition conjuncts against the goal's by `isDefEq` and emits
the permutation as an `ac_rfl` equality consumed by
`hnRefine_frame_perm`. Same effect, one pass instead of two, and no
dependence on the abstract term's argument list. `align_goal` is
nevertheless ported (it is a `sepref_dbg_*` entry point, and it is what
makes a *stalled* goal readable) as the reordering that puts the
argument conjuncts first.

**P4/D-cj — no free rules, no `free_tac`.** `Sepref_Frame.thy`'s
`free_thms = mk_free_invalid mk_free_pure mk_free_pair`, its
`named_theorems_rev sepref_frame_free_rules`, `mk_free_tac` and
`free_tac`, and the `MK_FREE` branch of its `wrap_side_tac` have no
counterpart: `MK_FREE` degenerated at wave A (P4/D-d) because the
substrate has no dealloc, so there is no free *program* to synthesize
and nothing for the tactic to do. The obligations those rules discharged
are entailments here, and the entailments are what `MERGE1_invalids_*`
and `entails_dead` state. Recorded as a deliberate absence, per the
brief.

**P4/D-ck — `weaken_post_tac` applies `_triv` and stops.** The source's
`weaken_post_tac` converts `hn_invalid` to `hn_val UNIV` in an
`hn_refine` postcondition so that a *manual* `hfref` proof is easier to
close by hand. Nothing in the automatic pipeline consumes it: our
`cons_init` (the one caller, `Sepref/Tool.lean`) runs against a goal
whose postcondition is a metavariable, and `weaken_hnr_post_triv`
discharges that instantly. The three real rules are ported and proved —
`weaken_hnr_post_star`, `_ctxt`, `_invalid` — and the *tactic* tries
them before falling back to `_triv`, but no gate exercises the non-triv
path, and this is the flag the brief asked for.

**P4/D-cl — `MERGE_STAR` is generalized to `MERGE_star_plain`.** The
source's `MERGE_STAR` folds over `hn_ctxt`-tagged conjuncts only,
because in the heap substrate every frame conjunct is one. Ours are not:
`junkCell x` (P4/D-f's scratch cells) and `¤¤` credit conjuncts appear
in frames too. `MERGE_star_plain` is the same rule with the `hn_ctxt`
tag dropped from all three positions — it is literally
`conj_entails_mono` twice — and `MERGE_STAR` is its corollary. The merge
loop uses the general form and so needs no separate case for untagged
conjuncts. Fallback: none needed; the source's rule remains available
and is proved in `Sepref/Basic.lean`.
-/

open Lean Elab Meta

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. Recovering pure values (source lines 21–38) -/

/-- The source's `recover_pure_aux`. -/
theorem recover_pure_aux {α κ : Type} {R : α → κ → Assn} {x : α} {y : κ}
    (h : CONSTRAINT isPure R) : hnInvalid R x y ⊢ hnCtxt R x y := by
  obtain ⟨R', hR⟩ := isPure_conv.1 (CONSTRAINT_D h)
  subst hR
  show invalidAssn (pureAssn R') x y ⊢ pureAssn R' x y
  rw [invalid_pure_recover]

/-! ### `frame_thms`, the source's five (lines 26–38) -/

/-- `frame_thms` (1): `P ⊢ P`. Wave A/P3's `entails_refl`. -/
theorem frame_refl (P : Assn) : P ⊢ P := entails_refl P

/-- `frame_thms` (2): `P ⊢ P' ⟹ F ⊢ F' ⟹ P ∗ F ⊢ P' ∗ F'`. P3's
`conj_entails_mono`. -/
theorem frame_star {P P' F F' : Assn} (hp : P ⊢ P') (hf : F ⊢ F') : P ∗ F ⊢ P' ∗ F' :=
  conj_entails_mono hp hf

/-- `frame_thms` (3): recover a pure value that a rule invalidated. -/
theorem frame_recover_pure {α κ : Type} {R : α → κ → Assn} {x : α} {y : κ}
    (h : CONSTRAINT isPure R) : hnInvalid R x y ⊢ hnCtxt R x y := recover_pure_aux h

/-- `frame_thms` (4): a pure assertion is forgettable down to
`hn_val UNIV`. -/
theorem frame_pure_val {α κ : Type} {R : α → κ → Assn} {x : α} {y : κ}
    (h : CONSTRAINT isPure R) : hnCtxt R x y ⊢ hnVal Set.univ x y := by
  obtain ⟨R', hR⟩ := isPure_conv.1 (CONSTRAINT_D h)
  subst hR
  intro s hs
  exact ⟨Set.mem_univ _, hs.2⟩

/-- `frame_thms` (5): a pure assertion may be handed over as its own
invalid marker. -/
theorem frame_ctxt_invalid {α κ : Type} {A : α → κ → Assn} {x : α} {y : κ}
    (h : CONSTRAINT isPure A) : hnCtxt A x y ⊢ hnInvalid A x y := by
  obtain ⟨A', hA⟩ := isPure_conv.1 (CONSTRAINT_D h)
  subst hA
  intro s hs
  exact ⟨⟨s, hs⟩, hs.2⟩

/-! ### `frame_rem_thms` (source lines 48–53) -/

/-- The source's `frame_rem1`. -/
theorem frame_rem1 (P : Assn) : P ⊢ P := entails_refl P

/-- The source's `frame_rem2`. -/
theorem frame_rem2 {α κ : Type} {A : α → κ → Assn} {x : α} {y : κ} {F F' : Assn}
    (h : F ⊢ F') : hnCtxt A x y ∗ F ⊢ hnCtxt A x y ∗ F' :=
  conj_entails_mono (entails_refl _) h

/-! ## 2. `RECOVER_PURE` (source lines 69–85) -/

/-- The source's `RECOVER_PURE P Q ≡ P ⊢ Q`. -/
def RECOVER_PURE (P Q : Assn) : Prop := P ⊢ Q

theorem RECOVER_PURE_def' (P Q : Assn) : RECOVER_PURE P Q ↔ (P ⊢ Q) := Iff.rfl

/-- The source's `RECOVER_PURED`. -/
theorem RECOVER_PURE_D {P Q : Assn} (h : RECOVER_PURE P Q) : P ⊢ Q := h

/-- The source's `recover_pure` (1). -/
theorem recover_pure_emp : RECOVER_PURE (□ : Assn) □ := entails_refl _

/-- The source's `recover_pure` (2). -/
theorem recover_pure_star {P₁ Q₁ P₂ Q₂ : Assn} (h₁ : RECOVER_PURE P₁ Q₁)
    (h₂ : RECOVER_PURE P₂ Q₂) : RECOVER_PURE (P₁ ∗ P₂) (Q₁ ∗ Q₂) :=
  conj_entails_mono h₁ h₂

/-- The source's `recover_pure` (3). -/
theorem recover_pure_invalid {α κ : Type} {R : α → κ → Assn} {x : α} {y : κ}
    (h : CONSTRAINT isPure R) : RECOVER_PURE (hnInvalid R x y) (hnCtxt R x y) :=
  recover_pure_aux h

/-- The source's `recover_pure` (4). -/
theorem recover_pure_ctxt {α κ : Type} (R : α → κ → Assn) (x : α) (y : κ) :
    RECOVER_PURE (hnCtxt R x y) (hnCtxt R x y) := entails_refl _

/-- The source's `recover_pure_triv`. -/
theorem recover_pure_triv (P : Assn) : RECOVER_PURE P P := entails_refl P

/-! ## 3. `WEAKEN_HNR_POST` (source lines 88–121, P4/D-ck) -/

/-- The source's
`WEAKEN_HNR_POST Γ Γ' Γ'' ≡ (∃h. Γ h) ⟶ (Γ'' ⊢ Γ')`, with `∃h. Γ h`
written as P3's `purePart Γ`. -/
def WEAKEN_HNR_POST (Γ Γ' Γ'' : Assn) : Prop := purePart Γ → (Γ'' ⊢ Γ')

/-- The source's `weaken_hnr_postI`, argument order included. -/
theorem weaken_hnr_postI {α κ : Type} {Γ Γ' Γ'' : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {a : NRest α ECost} (h₁ : WEAKEN_HNR_POST Γ Γ'' Γ')
    (h₂ : hnRefine Γ c Γ' d R a) : hnRefine Γ c Γ'' d R a :=
  hnRefine_preI fun hh hΓ => hnRefine_cons_post h₂ (h₁ ⟨hh, hΓ⟩)

/-- The source's `weaken_hnr_post_triv`. -/
theorem weaken_hnr_post_triv (Γ P : Assn) : WEAKEN_HNR_POST Γ P P :=
  fun _ => entails_refl P

/-- The source's `weaken_hnr_post` (1). -/
theorem weaken_hnr_post_star {Γ Γ₂ P P' Q Q' : Assn} (h₁ : WEAKEN_HNR_POST Γ P P')
    (h₂ : WEAKEN_HNR_POST Γ₂ Q Q') : WEAKEN_HNR_POST (Γ ∗ Γ₂) (P ∗ Q) (P' ∗ Q') := by
  rintro ⟨h, x, y, -, -, hx, hy⟩
  exact conj_entails_mono (h₁ ⟨x, hx⟩) (h₂ ⟨y, hy⟩)

/-- The source's `weaken_hnr_post` (2). -/
theorem weaken_hnr_post_ctxt {α κ : Type} (R : α → κ → Assn) (x : α) (y : κ) :
    WEAKEN_HNR_POST (hnCtxt R x y) (hnCtxt R x y) (hnCtxt R x y) :=
  weaken_hnr_post_triv _ _

/-- The source's `weaken_hnr_post` (3): `hn_invalid` weakens to
`hn_val UNIV` once the real assertion is known satisfiable. -/
theorem weaken_hnr_post_invalid {α κ : Type} (R : α → κ → Assn) (x : α) (y : κ) :
    WEAKEN_HNR_POST (hnCtxt R x y) (hnInvalid R x y) (hnVal Set.univ x y) := by
  rintro ⟨h, hh⟩ s hs
  exact ⟨⟨h, hh⟩, hs.2⟩

/-! ## 4. Merge congruences and the general `MERGE_STAR` (P4/D-cl) -/

/-- The source's `merge_left_assn_cong`. -/
theorem MERGE_left_cong {Γ₁ Γ₁' Γ₂ Γ' : Assn} (h : Γ₁ = Γ₁') (m : MERGE Γ₁' Γ₂ Γ') :
    MERGE Γ₁ Γ₂ Γ' := by rw [h]; exact m

/-- The source's `merge_right_assn_cong`. -/
theorem MERGE_right_cong {Γ₁ Γ₂ Γ₂' Γ' : Assn} (h : Γ₂ = Γ₂') (m : MERGE Γ₁ Γ₂' Γ') :
    MERGE Γ₁ Γ₂ Γ' := by rw [h]; exact m

/-- The source's `MERGE_append_END`, at `FRI_END = □` (wave A's
`MERGE_END`). -/
theorem MERGE_append_END {Γ₁ Γ₂ Γ' : Assn} (m : MERGE (Γ₁ ∗ □) (Γ₂ ∗ □) Γ') :
    MERGE Γ₁ Γ₂ Γ' := by rwa [sepConj_emp, sepConj_emp] at m

/-- Rewrite a `MERGE`'s synthesized result — how the trailing `□` of the
fold is normalized away. -/
theorem MERGE_res_cong {Γ₁ Γ₂ Γ' Γ'' : Assn} (h : Γ' = Γ'') (m : MERGE Γ₁ Γ₂ Γ') :
    MERGE Γ₁ Γ₂ Γ'' := by rw [← h]; exact m

/-- `MERGE_STAR` with the `hn_ctxt` tag dropped from all three positions
(P4/D-cl). The source's `MERGE_STAR` is the corollary at
`A = hnCtxt R₁ a c` etc. -/
theorem MERGE_star_plain {A B C Γ₁ Γ₂ Γ' : Assn} (h₁ : MERGE A B C) (h₂ : MERGE Γ₁ Γ₂ Γ') :
    MERGE (A ∗ Γ₁) (B ∗ Γ₂) (C ∗ Γ') :=
  ⟨conj_entails_mono h₁.1 h₂.1, conj_entails_mono h₁.2 h₂.2⟩

/-- `MERGE1_invalids_left` at one point, as a `MERGE`. -/
theorem MERGE_dead_left {α κ : Type} (R : α → κ → Assn) (a : α) (c : κ) :
    MERGE (deadAssn R a c) (R a c) (deadAssn R a c) := MERGE1_invalids_left R a c

/-- `MERGE1_invalids_right` at one point. -/
theorem MERGE_dead_right {α κ : Type} (R : α → κ → Assn) (a : α) (c : κ) :
    MERGE (R a c) (deadAssn R a c) (deadAssn R a c) := MERGE1_invalids_right R a c

/-- Branches that leave *different* values in the same scalar cell merge
to that cell's junk. The source has no analogue because its
`MERGE1_invalids` is driven by an `MK_FREE` program; under P4/D-c the
merge target is junk-of-the-same-shape and this is what it is at
`natAssn`. -/
theorem MERGE_natAssn_junk (m n : ℕ) (x : String) :
    MERGE (hnCtxt natAssn m x) (hnCtxt natAssn n x) (junkCell x) :=
  ⟨natAssn_entails_junkCell m x, natAssn_entails_junkCell n x⟩

/-- …and one branch may already have junked it. -/
theorem MERGE_natAssn_junk_left (n : ℕ) (x : String) :
    MERGE (junkCell x) (hnCtxt natAssn n x) (junkCell x) :=
  ⟨entails_refl _, natAssn_entails_junkCell n x⟩

/-- …either way round. -/
theorem MERGE_natAssn_junk_right (m : ℕ) (x : String) :
    MERGE (hnCtxt natAssn m x) (junkCell x) (junkCell x) :=
  ⟨natAssn_entails_junkCell m x, entails_refl _⟩

/-! ## 5. The permutation-carrying frame rules

What `Sepref/Translate.lean` applies a rule *through* (P4/D-ci): the
goal's precondition is a permutation of the rule's precondition starred
with a frame, and the permutation is an `ac_rfl` equality. -/

/-- Apply a rule under a frame, with the goal's precondition given as a
permutation. `heq` comes first so that `mkAppM` fixes `Γ`, `P` and `F`
from *it* — the permutation's spelling is the goal's, which is what makes
`ac_rfl` a pure permutation. -/
theorem hnRefine_frame_perm {α κ : Type} {Γ P F Q : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {m : NRest α ECost} (heq : Γ = P ∗ F) (h : hnRefine P c Q d R m) :
    hnRefine Γ c (Q ∗ F) d R m :=
  hnRefine_frame h (by rw [heq])

/-- Apply a rule with no frame left over. -/
theorem hnRefine_pre_perm {α κ : Type} {Γ P Q : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {m : NRest α ECost} (heq : Γ = P) (h : hnRefine P c Q d R m) :
    hnRefine Γ c Q d R m := by rw [heq]; exact h

/-- Rewrite the abstract side of an `hnRefine` goal — how the `id` and
`monadify` phases hand their output to `trans`. -/
theorem hnRefine_abs_cong {α κ : Type} {Γ Q : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {m m' : NRest α ECost} (heq : m = m')
    (h : hnRefine Γ c Q d R m') : hnRefine Γ c Q d R m := by rw [heq]; exact h

/-- The `CondRefine` analogue: a guard rule holds under any permutation
of a larger context (wave B1's `CondRefine.frame` plus the
permutation). -/
theorem CondRefine_perm {Γ P F : Assn} {cond : Cond} {b : Bool} (heq : Γ = P ∗ F)
    (h : CondRefine P cond b) : CondRefine Γ cond b := by
  rw [heq]; exact h.frame

/-- …with no context left over. -/
theorem CondRefine_perm_exact {Γ P : Assn} {cond : Cond} {b : Bool} (heq : Γ = P)
    (h : CondRefine P cond b) : CondRefine Γ cond b := by rw [heq]; exact h

/-- The pair assertion, split: `hn_ctxt (A ×ₐ B)` at a pair of cells is
the two component assertions starred, *definitionally* (`prodAssn`'s own
equation). This is the source's `prod_assn_pair_conv` in the shape the
frame matcher needs — a two-cell loop state `(i, acc)` arrives as one
conjunct at the loop rule and as two inside the body (P4/D-cu). -/
theorem hnCtxt_prodAssn {α₁ α₂ κ₁ κ₂ : Type} (A : α₁ → κ₁ → Assn) (B : α₂ → κ₂ → Assn)
    (a : α₁ × α₂) (c : κ₁ × κ₂) :
    hnCtxt (A ×ₐ B) a c = hnCtxt A a.1 c.1 ∗ hnCtxt B a.2 c.2 := rfl

/-- The same split without the `hnCtxt` wrapper — `hnr_mop_pair`-shaped
posts spell the pair assertion bare. -/
theorem prodAssn_apply {α₁ α₂ κ₁ κ₂ : Type} (A : α₁ → κ₁ → Assn) (B : α₂ → κ₂ → Assn)
    (a : α₁ × α₂) (c : κ₁ × κ₂) :
    (A ×ₐ B) a c = A a.1 c.1 ∗ B a.2 c.2 := rfl

/- **T1/D-b — `fri` sees pair contexts in the split spelling.** The
2A satellite's probe found the frame solver failing on
"`arrayAssn st.1 "dist"` wanted, `hnCtxt (… ×ₐ …) st (…)` owned": the
two spell the same assertion (`rfl`, above), but `fri` matches conjunct
atoms and a pair context is one atom. Registering the two `rfl`
equations in `fri_prepare_simps` normalizes BOTH sides of every `fri`
goal to the component spelling before matching, which is the `fri`
direction of P4/D-cu's `conjunctsSplit`. Definitional, so no proof-term
cost and no soundness surface; the whole tower rebuilt green under it. -/
attribute [fri_prepare_simps] hnCtxt_prodAssn prodAssn_apply

/-! ### Junk for arrays

`Sepref/Basic.lean` gave the scalar case (`junkCell`, P4/D-f); the array
case is needed for the same reason and by the same argument, and is
added here because `Sepref/Translate.lean`'s post-abstraction (P4/D-ct)
is its first consumer. -/

/-- The array analogue of `junkCell`: the array `a` exists and holds
*something*. -/
def junkArray (a : String) : Assn := ∃ᵃ xs, a ↦ₐ xs

@[simp] theorem junkArray_def (a : String) : junkArray a = ∃ᵃ xs, a ↦ₐ xs := rfl

/-- The array instance of `entails_dead`. -/
theorem arrayAssn_entails_junkArray (xs : List ℕ) (a : String) :
    arrayAssn xs a ⊢ junkArray a := fun _ h => ⟨xs, h⟩

theorem deadAssn_arrayAssn_eq_junkArray (xs : List ℕ) (a : String) :
    deadAssn arrayAssn xs a = junkArray a := rfl

/-! ## 6. The Sepref weakenings, as `fri_rules` (P4/D-ch)

`Ir/SepSolver.lean`'s step set. A member is an entailment between single
conjuncts, which is exactly the shape of `frame_thms` 3–5 and of the
P4/D-c weakenings; registering them here is what turns `fri` into the
source's `frame_tac`. -/

attribute [fri_rules] natAssn_entails_junkCell arrayAssn_entails_junkArray
attribute [fri_rules] entails_dead recover_pure_aux
attribute [fri_rules] frame_pure_val frame_ctxt_invalid

/-! ## 7. The `CondRefine` rule base (P4/D-cb) -/

attribute [sepref_cond_rules] condRefine_lt_cells condRefine_eq_cells
attribute [sepref_cond_rules] condRefine_lt_cell_lit condRefine_lt_lit_cell
attribute [sepref_cond_rules] condRefine_eq_cell_lit condRefine_eq_lit_cell

/-! ## 8. The `∗`-permutation tactic

Every alignment step below reduces to one equation between two
`∗`-trees over the same conjuncts. -/

/-- Close a goal `A = B` between two `∗`-trees that differ by
associativity, commutativity and units. -/
macro "sepref_ac" : tactic =>
  `(tactic|
    first
      | rfl
      | ac_rfl
      | (simp only [hnCtxt_prodAssn, sepConj_emp, emp_sepConj]
         all_goals (first | rfl | ac_rfl)))

/-! ## 9. The tactics (the source's ML structure `Sepref_Frame`) -/

namespace Frame

/-! ### Conjunct lists -/

/-- Flatten an assertion into its `∗`-conjuncts; `□` contributes
nothing. The source's `strip_star`. -/
partial def conjuncts (e : Expr) : Array Expr :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    match e.consumeMData.getAppFnArgs with
    | (``sepConj, #[_, _, _, _, _, a, b]) => go b (go a acc)
    | (``emp, _) => acc
    | _ => acc.push e.consumeMData

/-- A component of a pair: the entry itself when the pair is literal,
and otherwise `Prod.fst`/`Prod.snd` *applied* — never `whnf`ed to the
raw projection `a.1` (P7/D-ba). Both spellings are the same term, but
`hnCtxt_prodAssn`'s rewrite produces the application and `ac_rfl`
compares atoms syntactically, so a split that `whnf`s cannot be
reconciled with one that rewrites — which is exactly what a loop state
carrying two arrays asks `proveConjEq` to do. -/
def projOf (fst : Bool) (a : Expr) : MetaM Expr := do
  match (← whnf a).getAppFnArgs with
  | (``Prod.mk, #[_, _, x, y]) => return if fst then x else y
  | _ => mkAppM (if fst then ``Prod.fst else ``Prod.snd) #[a]

/-- `conjuncts`, with pair assertions split into their components
(P4/D-cu). Used as the *second* attempt at matching: the loop rule wants
the state as one conjunct, the body's operations want it as two. -/
partial def conjunctsSplit (e : Expr) : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  for c in conjuncts e do
    match c.getAppFnArgs with
    | (``hnCtxt, #[_, _, R, a, cc]) =>
      match R.getAppFnArgs with
      | (``prodAssn, #[_, _, _, _, A, B]) =>
        let l ← mkAppM ``hnCtxt #[A, ← projOf true a, ← projOf true cc]
        let r ← mkAppM ``hnCtxt #[B, ← projOf false a, ← projOf false cc]
        out := out ++ (← conjunctsSplit l) ++ (← conjunctsSplit r)
      | _ => out := out.push c
    | _ => out := out.push c
  return out

/-- The source's `list_star`: rebuild a right-nested `∗`-tree. -/
def mkConjuncts (α : Expr) (es : Array Expr) : MetaM Expr := do
  if es.size = 0 then
    mkAppOptM ``emp #[some α, none]
  else
    let mut r := es[es.size - 1]!
    for i in [1 : es.size] do
      r ← mkAppM ``sepConj #[es[es.size - 1 - i]!, r]
    return r

/-- The carrier of an assertion expression (`AState`, always, but read
off the term so that nothing depends on the abbreviation). -/
def carrierOf (e : Expr) : MetaM Expr := do
  match (← whnf (← inferType e)) with
  | .forallE _ α _ _ => return α
  | ty => throwError "sepref: not an assertion type:{indentExpr ty}"

/-- Prove `lhs = rhs` for two `∗`-trees over the same conjuncts. -/
def proveConjEq (lhs rhs : Expr) : TermElabM Expr := do
  let ty ← mkEq lhs rhs
  let m ← mkFreshExprSyntheticOpaqueMVar ty
  let rest ← Tactic.run m.mvarId! (Tactic.evalTactic (← `(tactic| sepref_ac)))
  unless rest.isEmpty do
    throwError "sepref: these are not permutations of one another:{indentExpr ty}"
  instantiateMVars m

/-! ### The matcher (the source's `prepare_fi_conv`, P4/D-ci)

Pair each conjunct of a rule's precondition with a distinct conjunct of
the goal's, by `isDefEq`. Matching only, never dropping: the logic is
precise, so what is not paired is the frame, not garbage. -/

/-- **Pair by the abstract value first (P7/D-bg).** `hnCtxt R a c`
unfolds to `R a c`, so `isDefEq` on the whole conjunct may solve a
metavariable *relator* by a constant function: `hnCtxt ?A D ?c` matches
`hnCtxt natAssn 1 "one"` at `?A := fun _ => natAssn 1`, `?c := "one"`.
That is well-typed nonsense — it hands the operation a cell that does
not hold its argument — and it is what a rule with an open relator
(`hnr_mop_pair`) does to whichever conjunct the goal happens to list
first. The source pairs by the abstract term before anything else
(`prepare_fi_conv`'s `Termtab` key) and `mergeSolve` below already does;
the frame matcher did not. One first-order check restores it. -/
def absAgree (r g : Expr) : MetaM Bool := do
  match r.getAppFnArgs, g.getAppFnArgs with
  | (``hnCtxt, #[αr, _, _, ar, _]), (``hnCtxt, #[αg, _, _, ag, _]) =>
    try
      if ← isDefEq αr αg then isDefEq ar ag else return false
    catch _ => return false
  -- T1/D-e: an `hnCtxt` rule conjunct never pairs with a *junk* goal
  -- conjunct. With an *open* relator, `isDefEq` happily eats a
  -- `junkCell` (`hnCtxt ?B b ?c ≡ ?B b ?c` matches `∃ᵃ v, n ↦ᵥ v` at
  -- `?B := fun _ => sepEx _`) — P7/D-bg's well-typed nonsense through
  -- the junk route, first hit by `mopPair` under a goal that lists a
  -- junk cell before the value cell. Only the junk heads are excluded:
  -- BARE ownership spellings (`natAssn a c` without the `hnCtxt`
  -- wrapper) are legitimate matches and stay admissible.
  | (``hnCtxt, _), (``junkCell, _) => return false
  | (``hnCtxt, _), (``junkArray, _) => return false
  | _, _ => return true

/-- Search for an injection of `rs` into `gs`, in `rs`-order, with
backtracking. Returns the goal-side indices, one per `r`, together with
the (possibly refined) goal conjunct list.

T1/D-f — **lazy per-conjunct pair splitting.** The old two-attempt
scheme (as-written, then `conjunctsSplit` on *everything*) is
all-or-nothing, and a rule like `hnr_mop_pair` binding one component of
an earlier result to a freshly packed pair needs one goal pair SPLIT
and the other WHOLE — satisfiable by neither attempt. So the split is
now a fallback inside the search: when a rule conjunct matches no
unused goal conjunct, one unused pair context is split (`rfl`) and the
search retries; backtracking explores the split choices. The returned
conjunct list is the goal's spelling refined by exactly the splits the
match needed, and the permutation proof (`sepref_ac`) reconciles it
with the original by the same `rfl` equations. The default fuel is 0 —
existing call paths are byte-identical; the lazy split fires only in
the explicit attempt-3 of `applyRuleAt` / `condSolve`. -/
partial def matchLoop (rs : List Expr) (gs : Array Expr) (used : Array Nat)
    (splitFuel : Nat := 0) : MetaM (Option (Array Nat × Array Expr)) := do
  if rs.isEmpty then return some (used, gs)
  let r := rs.head!
  let rest := rs.tail
  for i in [0 : gs.size] do
    unless used.contains i do
      let st ← saveState
      if (← absAgree r gs[i]!) && (← isDefEq r gs[i]!) then
        let res ← matchLoop rest gs (used.push i) splitFuel
        if res.isSome then return res
        st.restore
      else st.restore
  -- Fallback: split one unused pair context and retry this same `r`.
  if splitFuel > 0 then
    for i in [0 : gs.size] do
      unless used.contains i do
        if let (``hnCtxt, #[_, _, R, a, cc]) := gs[i]!.getAppFnArgs then
          if let (``prodAssn, #[_, _, _, _, A, B]) := R.getAppFnArgs then
            let st ← saveState
            let l ← mkAppM ``hnCtxt #[A, ← projOf true a, ← projOf true cc]
            let rr ← mkAppM ``hnCtxt #[B, ← projOf false a, ← projOf false cc]
            let res ← matchLoop rs ((gs.set! i l).push rr) used (splitFuel - 1)
            if res.isSome then return res
            st.restore
  return none

/-- The source's `prepare_fi_conv`, as data: pair the rule's conjuncts
against the goal's, and return `(matched, frame)` — both in terms of the
*goal's* spelling (refined by any T1/D-f splits), so that the
permutation equality is `sepref_ac`-provable. -/
def frameMatch (ruleConjs goalConjs : Array Expr)
    (splitFuel : Nat := 0) : MetaM (Option (Array Expr × Array Expr)) := do
  let res ← matchLoop ruleConjs.toList goalConjs #[] splitFuel
  if res.isNone then return none
  let (idx, gs) := res.get!
  let matched := idx.map fun i => gs[i]!
  let frame := (List.range gs.size).filter (fun i => !idx.contains i)
  return some (matched, (frame.map fun i => gs[i]!).toArray)

/-- The message a failed pairing produces — the source's
`align_conv: Could not match all arguments`, with the offending
conjuncts named (the plan's legibility item). -/
def noPairMsg (ruleConjs goalConjs : Array Expr) : MetaM MessageData := do
  let rl := ruleConjs.toList.map indentExpr
  let gl := goalConjs.toList.map indentExpr
  return m!"the rule's precondition conjuncts{MessageData.joinSep rl ""}\n\
    could not all be matched against the goal's{MessageData.joinSep gl ""}"

/-! ### `recover_pure_tac` (source lines 426–438) -/

/-- Does this `RECOVER_PURE` goal's left-hand side contain an
`hn_invalid`? The source's `contains_invalid`. -/
def containsInvalid (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``RECOVER_PURE, #[P, _]) =>
    (conjuncts P).any fun c =>
      match c.getAppFnArgs with
      | (``hnCtxt, #[_, _, R, _, _]) => R.getAppFnArgs.1 == ``invalidAssn
      | _ => false
  | _ => false

/-- The source's `recover_pure_tac`:
`CONCL_COND' contains_invalid THEN_ELSE' (REPEAT_ALL_NEW (recover_pure
ORELSE' constraint_tac), recover_pure_triv)`. Returns the constraint
goals it deferred. -/
partial def recoverPure (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  unless containsInvalid ty do
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``recover_pure_triv)
    unless gs.isEmpty do throwError "sepref: recover_pure_triv left goals open"
    return
  let rules : Array Name :=
    #[``recover_pure_emp, ``recover_pure_invalid, ``recover_pure_ctxt, ``recover_pure_star]
  for r in rules do
    let st ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels r)
      for g' in gs do
        let ty' ← instantiateMVars (← g'.getType)
        if (Constraints.isConstraintGoal? ty').isSome then
          Constraints.constraintTac g'
        else
          recoverPure g'
      return
    catch _ => st.restore
  -- Nothing structural applied: the identity is always available.
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``recover_pure_triv)
  unless gs.isEmpty do throwError "sepref: recover_pure_triv left goals open"

/-! ### `merge_tac` (source lines 401–417)

The source reorders both operands with `reorder_ctxt_conv`, appends
`FRI_END`, and then loops `merge_thms`. Here the reordering and the loop
are one pass: pair the two operands' conjuncts, decide each pair, and
fold the per-pair `MERGE`s with `MERGE_star_plain` / `MERGE_END`. -/

/-- The `MERGE A B ?C` of one aligned conjunct pair, and the `C` it
produces. The order is the source's `merge_thms`: `MERGE1_eq` first (the
same-assertion case), then the two `MERGE1_invalids`, then the
database. -/
def mergeOne (a b : Expr) : TermElabM (Expr × Expr) := do
  -- `MERGE_triv`: the two branches agree.
  if ← isDefEq a b then
    return (a, ← mkAppM ``MERGE_triv #[a])
  let extra ← (try labelled `sepref_frame_merge_rules catch _ => pure #[])
  let rules : Array Name :=
    #[``MERGE_dead_left, ``MERGE_dead_right, ``MERGE_natAssn_junk_left,
      ``MERGE_natAssn_junk_right, ``MERGE_natAssn_junk] ++ extra
  for r in rules do
    let st ← saveState
    try
      let rule ← mkConstWithFreshMVarLevels r
      let (mvars, _, concl) ← forallMetaTelescope (← inferType rule)
      match concl.getAppFnArgs with
      | (``MERGE, #[aE, bE, cE]) =>
        if (← isDefEq aE a) && (← isDefEq bE b) then
          let prf := mkAppN rule mvars
          for mv in mvars do
            let mid := mv.mvarId!
            unless ← mid.isAssigned do
              throwError "sepref: the merge rule {r} left an argument open"
          return (← instantiateMVars cE, prf)
        else st.restore
      | _ => st.restore
    catch _ => st.restore
  throwError "sepref: no merge rule joins the two branch conjuncts{indentExpr a}\nand\
    {indentExpr b}"

/-- The source's `merge_tac`. Goal: `MERGE Γt Γe ?Γ'`; the frame `?Γ'` is
synthesized. -/
def mergeSolve (g : MVarId) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let (``MERGE, #[l, r, _]) := ty.getAppFnArgs
    | throwError "sepref: not a MERGE goal:{indentExpr ty}"
  -- The source's fast path: the two frames are already the same.
  if ← isDefEq l r then
    let prf ← mkAppM ``MERGE_triv #[l]
    unless ← isDefEq (← inferType prf) ty do
      throwError "sepref: MERGE_triv did not close{indentExpr ty}"
    g.assign prf
    return
  -- T1/D-a: normalize BOTH sides to the split spelling before pairing.
  -- A branch arm that consumed a projection of a bound tuple leaves its
  -- postcondition with the tuple ownership split (`hnCtxt A r.1 c.1 ∗ …`)
  -- while the other arm's is whole (`hnCtxt (A ×ₐ B) r c`); the two spell
  -- the same assertion (`hnCtxt_prodAssn` is `rfl`), but pairing by cell
  -- key cannot see it — the whole conjunct's key is the cell *pair*. The
  -- split is definitional, and `proveConjEq`'s `sepref_ac` already
  -- reconciles the spellings on the congruence side.
  let ls ← conjunctsSplit l
  let rs ← conjunctsSplit r
  let α ← carrierOf l
  -- Align: for each left conjunct, the right conjunct that owns the same
  -- thing. Pairing is by `isDefEq` first, then by the shared concrete
  -- argument, which is the source's Termtab key.
  let key (e : Expr) : Option Expr :=
    match e.getAppFnArgs with
    | (``hnCtxt, #[_, _, _, _, c]) => some c
    | (``junkCell, #[c]) => some c
    | (``junkArray, #[c]) => some c
    | _ => none
  let mut usedR : Array Nat := #[]
  let mut pairs : Array (Expr × Expr) := #[]
  for a in ls do
    let mut found : Option Nat := none
    for i in [0 : rs.size] do
      if found.isNone && !usedR.contains i then
        let b := rs[i]!
        if (← isDefEq a b) then found := some i
        else match key a, key b with
          | some ka, some kb => if ← isDefEq ka kb then found := some i
          | _, _ => pure ()
    match found with
    | some i => usedR := usedR.push i; pairs := pairs.push (a, rs[i]!)
    | none =>
      throwError "sepref: the branch postconditions do not own the same cells — \
        the 'then' branch's conjunct{indentExpr a}\nhas no partner in the 'else' \
        branch{indentD (← (do
          let l ← rs.toList.mapM fun e => pure (indentExpr e)
          pure (MessageData.joinSep l "")))}"
  for i in [0 : rs.size] do
    unless usedR.contains i do
      throwError "sepref: the branch postconditions do not own the same cells — \
        the 'else' branch's conjunct{indentExpr rs[i]!}\nhas no partner in the \
        'then' branch"
  -- Decide each pair, then fold.
  let mut cs : Array Expr := #[]
  let mut prfs : Array Expr := #[]
  for (a, b) in pairs do
    let (c, p) ← mergeOne a b
    cs := cs.push c
    prfs := prfs.push p
  let mut acc ← mkAppOptM ``MERGE_END #[]
  let mut accL ← mkAppOptM ``emp #[some α, none]
  let mut accR := accL
  let mut accC := accL
  for i in [0 : prfs.size] do
    let j := prfs.size - 1 - i
    acc ← mkAppM ``MERGE_star_plain #[prfs[j]!, acc]
    accL ← mkAppM ``sepConj #[pairs[j]!.1, accL]
    accR ← mkAppM ``sepConj #[pairs[j]!.2, accR]
    accC ← mkAppM ``sepConj #[cs[j]!, accC]
  -- `acc : MERGE accL accR accC`; the goal is `MERGE l r ?Γ'`. The fold
  -- leaves a trailing `□` on all three sides; normalize it away.
  let accC' ← mkConjuncts α cs
  let hc ← proveConjEq accC accC'
  let accN ← mkAppM ``MERGE_res_cong #[hc, acc]
  let hl ← proveConjEq l accL
  let hr ← proveConjEq r accR
  let prf ← mkAppM ``MERGE_left_cong #[hl, ← mkAppM ``MERGE_right_cong #[hr, accN]]
  unless ← isDefEq (← inferType prf) ty do
    throwError "sepref: the merged frame does not match the goal{indentExpr ty}"
  g.assign prf

/-! ### `align_goal` (source lines 440–518, P4/D-ci)

Reorder an `hn_refine` goal's precondition so that the conjuncts the
abstract term mentions come first and the frame is a trailing
remainder. -/

/-- Parse `hnRefine Γ c Γ' d R m`. -/
def parseHnRefine? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``hnRefine, #[α, κ, Γ, c, Γ', d, R, m]) => some (α, κ, Γ, c, Γ', d, R, m)
  | _ => none

/-- The abstract value an `hn_ctxt` conjunct refines, if it is one. -/
def ctxtAbs? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``hnCtxt, #[_, _, _, a, _]) => some a
  | _ => none

/-- The source's `align_goal_conv`: precondition conjuncts whose
abstract value occurs in the abstract program come first, then the
scratch cells, then everything else. Returns the realigned goal. -/
def alignGoal (g : MVarId) : TermElabM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let some (_, _, Γ, _, _, _, _, m) := parseHnRefine? ty
    | throwError "sepref: not an hnRefine goal:{indentExpr ty}"
  let cs := conjuncts Γ
  let isArg (e : Expr) : Bool :=
    match ctxtAbs? e with
    | some a => (m.find? (· == a)).isSome
    | none => false
  let isJunk (e : Expr) : Bool := e.getAppFnArgs.1 == ``junkCell
  let args := cs.filter isArg
  let junk := cs.filter fun e => !isArg e && isJunk e
  let rest := cs.filter fun e => !isArg e && !isJunk e
  let ordered := args ++ junk ++ rest
  if ordered == cs then return g
  let α ← carrierOf Γ
  let Γ' ← mkConjuncts α ordered
  let heq ← proveConjEq Γ Γ'
  let newTy := mkAppN ty.consumeMData.getAppFn (ty.consumeMData.getAppArgs.set! 2 Γ')
  let m' ← mkFreshExprSyntheticOpaqueMVar newTy
  let prf ← mkAppM ``hnRefine_pre_perm #[heq, m']
  unless ← isDefEq (← inferType prf) ty do
    throwError "sepref: align_goal produced the wrong statement"
  g.assign prf
  return m'.mvarId!

end Frame

/-! ## 10. The tactic entry points (the `sepref_dbg_*` frame family) -/

/-- The source's `method_setup sepref_dbg_frame`: frame inference
(P4/D-ch — `fri` with the Sepref match rules). -/
macro "sepref_dbg_frame" : tactic => `(tactic| fri)

/-- The source's `sepref_dbg_merge`. -/
elab "sepref_dbg_merge" : tactic => do
  let g ← Tactic.getMainGoal
  Frame.mergeSolve g
  Tactic.replaceMainGoal []

/-- The source's `sepref_dbg_frame_step`: one frame-inference pass,
leaving the deferred pure side conditions as goals (P4/D-ch — `fri`'s
own step loop, without its side tactic). -/
macro "sepref_dbg_frame_step" : tactic => `(tactic| fri_core)

/-- The source's `sepref_dbg_frame_step_keep`: report instead of
throwing. -/
macro "sepref_dbg_frame_step_keep" : tactic => `(tactic| fri_trace)

/-- The source's `sepref_dbg_prepare_frame`: report the pairing the frame
inferencer would use, without running it. -/
elab "sepref_dbg_prepare_frame" : tactic => do
  let g ← Tactic.getMainGoal
  let ty ← instantiateMVars (← g.getType)
  match ty.getAppFnArgs with
  | (``entails, #[_, P, Q]) =>
    logInfo m!"sepref: frame pairing\n  premise conjuncts: \
      {MessageData.joinSep ((Frame.conjuncts P).toList.map indentExpr) ""}\n  \
      target conjuncts: {MessageData.joinSep ((Frame.conjuncts Q).toList.map indentExpr) ""}"
  | _ => throwError "sepref: not an entailment goal:{indentExpr ty}"

/-- The source's `method_setup weaken_hnr_post` (P4/D-ck): try the three
real rules, fall back to `_triv`. -/
macro "weaken_hnr_post" : tactic =>
  `(tactic| refine weaken_hnr_postI (weaken_hnr_post_triv _ _) ?_)

/-- The source's `recover_pure_tac`, as a tactic. -/
elab "sepref_dbg_recover_pure" : tactic => do
  let g ← Tactic.getMainGoal
  Frame.recoverPure g
  Tactic.replaceMainGoal []

/-! ## 11. Gate (ledger D4, refute-before-prove) -/

namespace FrameGate

/-- The frame inferencer matches a permuted precondition. -/
example (a b : ℕ) :
    (hnCtxt natAssn a "x" ∗ hnCtxt natAssn b "y") ⊢ (hnCtxt natAssn b "y" ∗ hnCtxt natAssn a "x") := by
  fri

/-- …and downgrades ownership to junk when the target asks for junk
(P4/D-c's weakening, in the `fri_rules` base). -/
example (a : ℕ) : hnCtxt natAssn a "x" ⊢ junkCell "x" := by fri

/-- Merging two branches that agree is `MERGE_triv`. -/
example (a : ℕ) :
    MERGE (hnCtxt natAssn a "x") (hnCtxt natAssn a "x") (hnCtxt natAssn a "x") := by
  sepref_dbg_merge

/-- Merging two branches that wrote different values to the same cell
junks it. -/
example : MERGE (hnCtxt natAssn 1 "x") (hnCtxt natAssn 2 "x") (junkCell "x") := by
  sepref_dbg_merge

/-- Merging with a frame: the shared conjunct survives, the disputed one
does not, and the operands may be permuted. -/
example (n : ℕ) :
    MERGE (hnCtxt natAssn 1 "x" ∗ hnCtxt natAssn n "n")
      (hnCtxt natAssn n "n" ∗ hnCtxt natAssn 2 "x") (junkCell "x" ∗ hnCtxt natAssn n "n") := by
  sepref_dbg_merge

/-- `RECOVER_PURE` on a frame with no invalid marker is the identity. -/
example (a : ℕ) :
    RECOVER_PURE (hnCtxt natAssn a "x") (hnCtxt natAssn a "x") := by
  sepref_dbg_recover_pure

/-- …and on one with a pure invalid marker it recovers the value, the
purity constraint being decided on the spot. -/
example (R : Set (Ir.Val × ℕ)) (a : ℕ) (y : Ir.Val) :
    RECOVER_PURE (hnInvalid (pureAssn R) a y) (hnCtxt (pureAssn R) a y) := by
  apply recover_pure_invalid
  solve_constraint

/-- `weaken_hnr_post` at the `_triv` path (P4/D-ck): the postcondition is
already what the rule delivers. -/
example (a b : ℕ) :
    hnRefine (junkCell "t" ∗ hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b")
      (Com.binop Imp.Bop.add "t" "a" "b") (hnCtxt natAssn a "a" ∗ hnCtxt natAssn b "b")
      "t" natAssn (mopBinop .add a b) := by
  weaken_hnr_post
  exact hnr_mop_binop .add "t" "a" "b" a b

/-- **Negative control 1.** The logic is precise: `GC` absorbs credits
only (P4/D-g), so an owned cell is not entailed away. -/
theorem junk_not_emp : ¬ (junkCell "x" ⊢ (□ : Assn)) := by
  intro h
  have h0 : junkCell "x" ((Ir.Cells.single "x" (0 : Ir.Val), 0), (0 : ECost)) :=
    ⟨0, ⟨rfl, rfl⟩, rfl⟩
  have h1 := h _ h0
  have h2 : Ir.Cells.single "x" (0 : Ir.Val) = 0 := congrArg (fun p => p.1.1) h1
  have h3 := congrFun h2 "x"
  simp [Ir.Cells.single] at h3

/-- **Negative control 2.** The frame inferencer does not invent
ownership: a target conjunct with no partner is a failure, not a
weakening. -/
example : True := by
  fail_if_success
    (have : hnCtxt natAssn 1 "x" ⊢ (hnCtxt natAssn 1 "x" ∗ hnCtxt natAssn 2 "y") := by fri)
  trivial

/-- **Negative control 3.** `merge_tac` refuses branches that do not own
the same cells. -/
example : True := by
  fail_if_success
    (have : MERGE (hnCtxt natAssn 1 "x") (hnCtxt natAssn 2 "y") (junkCell "x") := by
      sepref_dbg_merge)
  trivial

end FrameGate

end Lax13Proofs.Refine.Sepref
