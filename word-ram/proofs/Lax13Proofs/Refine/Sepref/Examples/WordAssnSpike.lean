import Lax13Proofs.Refine.Sepref.Definition
import Lax13Proofs.Refine.Codegen.Cash

/-!
# The `wordAssn` spike (ND-MC rebase P0.2)

The P8 verdict's option (b), built and measured. §2 item 2 of
`plans/word-ram/refinement-tower/p8-verdict.md` priced the **bounds
pass** at 560 Lean lines and named it the one genuinely new per-program
cost of the tower; §3 (b) proposed retiring it by moving `< B` *into
the assertions* — a `wordAssn B` whose ownership carries the bound,
with arithmetic `hnr` rules that surface `< B` as synthesis side
conditions, "the source's own architecture, where machine words carry
the bound in the type".

This file builds that layer and reports what it does and does not buy.
Everything here is new; nothing existing is edited.

## The three findings, up front

**R2/D-a — `wordAssn` is `natAssn` wherever it is inhabited.**
`wordAssn B a c := natAssn a c ∗ ⌜a < B⌝` is a *pure* extension, so
`wordAssn_of_lt` says `a < B → wordAssn B a c = natAssn a c` and
`wordAssn_of_ge` says `¬ a < B → wordAssn B a c = sepFalse`. The
assertion therefore carries no resource the plain one does not; the
whole content is the side condition. §2 makes that formal, and it is
why §3's bounded rule layer is *derived* from the existing rules in
three lines each rather than re-proved from the triples.

**R2/D-b — the bound is not what the bounds pass needs, and the
assertion is not where it is missing.** `Codegen/Cash.lean`'s
`spec_of_hnRefine` asks for `∃ s' κ, Ir.BigStepB B c s₀ s' κ`, and
`hnRefine`'s conclusion is a `wp` over the *plain* `Ir.BigStep`.
Adding a pure conjunct to `hnRefine`'s postcondition changes nothing
about the run, so a synthesis carried out entirely in `wordAssn` still
leaves `bfsQ_bpre` exactly where it was. What the pass actually needs is
a **second component of the judgment** that transports `bpre`. §4 builds
it (`BRefine`), and the striking part is that it needs no assertion
change at all: `natAssn m y` already *names* the abstract value `m` held
by the cell `y`, which is precisely the identification
`Examples/BfsQSynth.lean` §12 spends its `Option.some.inj` chains
re-establishing against `Ir.State`.

**R2/D-c — `wordAssn` cannot reach an engine-sized synthesis without a
`Translate.lean` edit.** `Sepref/Translate.lean`'s `junkConjunct` (the
tactic behind `hnr_bind`'s `IMP` premise) dispatches on the *constant*
`natAssn` / `arrayAssn` to find a conjunct's junk form. `wordAssn B` is
an application, so every `do x ← …` that binds a scalar throws
"there is no junk form for its assertion". §5's probe *reproduces* that
failure on a two-operation program, and the P6/D-bc wrapper idiom does
not help, because by R2/D-a the wrapper is the identity.

Taken together: option (b) as written is *insufficient*; the thing it is
a proxy for — creation-site `< B` as a rule side condition, discharged
against the abstract program rather than against `Ir.State` — is real,
is built here as `BRefine`, and does not need `wordAssn`.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

namespace WordSpike

/-! ## 1. The bounded assertions

`wordAssn B` is `natAssn` with the bound as a pure conjunct — the exact
formulation the verdict's option (b) names. `wordArrayAssn B` is its
array analogue: every entry fits. -/

/-- A scalar cell whose ownership carries `< B`. -/
def wordAssn (B : ℕ) : ℕ → String → Assn := fun a c => natAssn a c ∗ ⌜a < B⌝

/-- An array cell whose ownership carries `< B` on every entry. -/
def wordArrayAssn (B : ℕ) : List ℕ → String → Assn :=
  fun xs a => arrayAssn xs a ∗ ⌜∀ v ∈ xs, v < B⌝

theorem wordAssn_def (B a : ℕ) (c : String) :
    wordAssn B a c = (natAssn a c ∗ ⌜a < B⌝) := rfl

theorem wordArrayAssn_def (B : ℕ) (xs : List ℕ) (a : String) :
    wordArrayAssn B xs a = (arrayAssn xs a ∗ ⌜∀ v ∈ xs, v < B⌝) := rfl

/-! ## 2. R2/D-a: the assertion *is* the side condition, and nothing else

A pure conjunct owns no resource. So a `wordAssn` is either the plain
`natAssn` (when the bound holds) or the empty assertion (when it does
not) — there is no third case, and in particular no state in which
`wordAssn` restricts a run that `natAssn` admits. -/

/-- **Inhabited: `wordAssn` *is* `natAssn`.** -/
theorem wordAssn_of_lt {B a : ℕ} {c : String} (h : a < B) : wordAssn B a c = natAssn a c := by
  rw [wordAssn_def, predLift_of_true h, sepConj_emp]

/-- **Uninhabited: no ownership at all.** This is the negative half —
the side condition has content because failing it *deletes* the
assertion, not because it weakens it. -/
theorem wordAssn_of_ge {B a : ℕ} {c : String} (h : ¬ a < B) :
    wordAssn B a c = (sepFalse : Assn) := by
  funext p
  refine propext ⟨fun hp => absurd ?_ h, fun hp => hp.elim⟩
  rw [wordAssn_def, sepConj_comm, predLift_sepConj_iff] at hp
  exact hp.1

theorem wordArrayAssn_of_mem {B : ℕ} {xs : List ℕ} {a : String} (h : ∀ v ∈ xs, v < B) :
    wordArrayAssn B xs a = arrayAssn xs a := by
  rw [wordArrayAssn_def, predLift_of_true h, sepConj_emp]

theorem wordArrayAssn_of_not_mem {B : ℕ} {xs : List ℕ} {a : String} (h : ¬ ∀ v ∈ xs, v < B) :
    wordArrayAssn B xs a = (sepFalse : Assn) := by
  funext p
  refine propext ⟨fun hp => absurd ?_ h, fun hp => hp.elim⟩
  rw [wordArrayAssn_def, sepConj_comm, predLift_sepConj_iff] at hp
  exact hp.1

/-- The bound, read back off ownership: this is all a consumer ever gets
out of a `wordAssn`. -/
theorem lt_of_wordAssn {B a : ℕ} {c : String} {p : AState} (h : wordAssn B a c p) : a < B := by
  rw [wordAssn_def, sepConj_comm, predLift_sepConj_iff] at h
  exact h.1

/-- Dropping the bound is free (a pure conjunct owns nothing). -/
theorem wordAssn_entails_natAssn (B a : ℕ) (c : String) : wordAssn B a c ⊢ natAssn a c := by
  intro p h
  rw [wordAssn_def, sepConj_comm, predLift_sepConj_iff] at h
  exact h.2

theorem wordArrayAssn_entails_arrayAssn (B : ℕ) (xs : List ℕ) (a : String) :
    wordArrayAssn B xs a ⊢ arrayAssn xs a := by
  intro p h
  rw [wordArrayAssn_def, sepConj_comm, predLift_sepConj_iff] at h
  exact h.2

/-- …and the junk forms, for the frame layer (`fri_rules`). -/
theorem wordAssn_entails_junkCell (B a : ℕ) (c : String) : wordAssn B a c ⊢ junkCell c :=
  entails_trans (wordAssn_entails_natAssn B a c) (natAssn_entails_junkCell a c)

theorem wordArrayAssn_entails_junkArray (B : ℕ) (xs : List ℕ) (a : String) :
    wordArrayAssn B xs a ⊢ junkArray a :=
  entails_trans (wordArrayAssn_entails_arrayAssn B xs a) (arrayAssn_entails_junkArray xs a)

attribute [fri_rules] wordAssn_entails_junkCell wordArrayAssn_entails_junkArray

/-! ## 3. The bounded rule layer

One rule per operation an engine actually uses, each consuming and
producing `wordAssn`/`wordArrayAssn`, each surfacing its *creation-site*
`< B` as a side condition. R2/D-a is what makes them cheap: the
precondition and the frame rewrite to the plain assertions, and the only
real work is the result slot, which is `hnRefine_augment_res`. -/

/-- The result-slot lemma: a `consume (returnT a)` program admits exactly
`a`, so a bound on `a` bounds every admissible result. -/
theorem bound_res_consume_returnT {α : Type} {a : α} {t : ECost} {Φ : α → Prop}
    (h : Φ a) :
    ∀ M, ((NRest.returnT a).consume t : NRest α ECost) = .rest M →
      ∀ (a' : α) (t' : ECost), M a' = (t' : WithBot ECost) → Φ a' := by
  intro M hM a' t' ht'
  rw [NRest.consume_returnT, NRest.rest_inj_iff] at hM
  subst hM
  by_cases hne : a' = a
  · exact hne ▸ h
  · rw [NRest.single_of_ne hne] at ht'
    exact absurd ht'.symm WithBot.coe_ne_bot

/-- The same, through a satisfied `assert`. -/
theorem bound_res_assert_consume {α : Type} {a : α} {t : ECost} {Ψ : Prop}
    {Φ : α → Prop} (hΨ : Ψ) (h : Φ a) :
    ∀ M, (NRest.bindT (NRest.assert Ψ) (fun _ =>
        (NRest.returnT a).consume t) : NRest α ECost) = .rest M →
      ∀ (a' : α) (t' : ECost), M a' = (t' : WithBot ECost) → Φ a' := by
  rw [NRest.assert_pos hΨ, NRest.returnT_bindT]
  exact bound_res_consume_returnT h

/-- Upgrade a `natAssn`-result judgment to a `wordAssn`-result one. This
is `hnRefine_augment_res` at `Φ := (· < B)`; `wordAssn B` is
*definitionally* the augmented relator. -/
theorem hnRefine_word_res {Γ Γ' : Assn} {c : Com} {x : String} {B : ℕ} {m : NRest ℕ ECost}
    (A : hnRefine Γ c Γ' x natAssn m)
    (Bd : ∀ M, m = .rest M → ∀ (a : ℕ) (t : ECost), M a = (t : WithBot ECost) → a < B) :
    hnRefine Γ c Γ' x (wordAssn B) m := hnRefine_augment_res A Bd

/-- …and its array analogue. -/
theorem hnRefine_wordArray_res {Γ Γ' : Assn} {c : Com} {x : String} {B : ℕ}
    {m : NRest (List ℕ) ECost} (A : hnRefine Γ c Γ' x arrayAssn m)
    (Bd : ∀ M, m = .rest M → ∀ (a : List ℕ) (t : ECost), M a = (t : WithBot ECost) →
      ∀ v ∈ a, v < B) :
    hnRefine Γ c Γ' x (wordArrayAssn B) m := hnRefine_augment_res A Bd

/-! ### Vacuity: an unsatisfiable precondition needs no rule

R2/D-a's negative half, put to work. If a rule's precondition owns a
`wordAssn B` at an out-of-range value it owns `sepFalse`, and an
`hnRefine` with an unsatisfiable precondition is *free*. So the operand
bounds need not be side conditions at all — which is the difference
between a rule the synthesis can fire and one it cannot (R2/D-e). -/

variable {α κ : Type}

theorem hnRefine_of_pre_false {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} (h : ∀ p : AState, ¬ Γ p) : hnRefine Γ c Γ' d R m := by
  intro _ M F s cr _ hs
  obtain ⟨u, v, -, -, hu, -⟩ := hs
  exact absurd hu (h u)

theorem sepConj_false_left {Γ Δ : Assn} (h : ∀ p : AState, ¬ Γ p) :
    ∀ p : AState, ¬ (Γ ∗ Δ) p := by
  rintro p ⟨u, v, -, -, hu, -⟩
  exact absurd hu (h u)

theorem sepConj_false_right {Γ Δ : Assn} (h : ∀ p : AState, ¬ Δ p) :
    ∀ p : AState, ¬ (Γ ∗ Δ) p := by
  rintro p ⟨u, v, -, -, -, hv⟩
  exact absurd hv (h v)

theorem wordAssn_false {B a : ℕ} {c : String} (h : ¬ a < B) : ∀ p : AState, ¬ wordAssn B a c p :=
  fun _ hp => h (lt_of_wordAssn hp)

theorem wordArrayAssn_false {B : ℕ} {xs : List ℕ} {a : String} (h : ¬ ∀ v ∈ xs, v < B) :
    ∀ p : AState, ¬ wordArrayAssn B xs a p := by
  intro p hp
  rw [wordArrayAssn_def, sepConj_comm, predLift_sepConj_iff] at hp
  exact h hp.1

/-! ### The rules

**R2/D-e — the only side conditions are the creation sites.** Every
operand bound is discharged by vacuity above, and every index bound by
the `mop`'s own `assert` (`hnr_assert`). What is left is `n < B` at
`const` and `op.apply m n < B` at `binop` — exactly P7/D-bl's residual,
and exactly the goals the synthesis has to hand to the caller. -/

/-- `x := n`. **Side condition: `n < B`** — the literal must fit. -/
@[sepref_fr_rules]
theorem hnr_mop_constN_word (B : ℕ) (x : String) (n : ℕ) (hn : n < B) :
    hnRefine (junkCell x) (.const x n) (□ : Assn) x (wordAssn B) (mopConstN n) := by
  refine hnRefine_word_res (hnr_mop_constN x n) ?_
  rw [mopConstN_def]
  exact bound_res_consume_returnT hn

/-- `x := y`. **No side condition**: the operand's bound comes off its
own ownership, and where it does not hold the precondition is
`sepFalse`. -/
@[sepref_fr_rules]
theorem hnr_mop_copy_word (B : ℕ) (x y : String) (w : ℕ) :
    hnRefine (junkCell x ∗ hnCtxt (wordAssn B) w y) (.copy x y)
      (hnCtxt (wordAssn B) w y) x (wordAssn B) (mopCopy w) := by
  by_cases hw : w < B
  · simp only [hnCtxt_def, wordAssn_of_lt hw]
    refine hnRefine_word_res (hnr_mop_copy x y w) ?_
    rw [mopCopy_def]
    exact bound_res_consume_returnT hw
  · exact hnRefine_of_pre_false (sepConj_false_right (wordAssn_false hw))

/-- `x := y ⊕ z`. **Side condition: `op.apply m n < B`, and nothing
else** — the *creation site*. The operands' own bounds are not
hypotheses: `hm`/`hn` would be unusable to the synthesis anyway (they are
Lean goals, and the solver cannot read them off the assertion — R2/D-e),
and they are not needed, because a rule whose precondition is
uninhabitable holds for free. Note that they would not suffice either:
`x := y + 1` at `y = B - 1` leaves `B` (P7/D-bl). -/
@[sepref_fr_rules]
theorem hnr_mop_binop_word (B : ℕ) (op : Imp.Bop) (x y z : String) (m n : ℕ)
    (hb : op.apply m n < B) :
    hnRefine (junkCell x ∗ hnCtxt (wordAssn B) m y ∗ hnCtxt (wordAssn B) n z)
      (.binop op x y z)
      (hnCtxt (wordAssn B) m y ∗ hnCtxt (wordAssn B) n z) x (wordAssn B)
      (mopBinop op m n) := by
  by_cases hm : m < B
  · by_cases hn : n < B
    · simp only [hnCtxt_def, wordAssn_of_lt hm, wordAssn_of_lt hn]
      refine hnRefine_word_res (hnr_mop_binop op x y z m n) ?_
      rw [mopBinop_def]
      exact bound_res_consume_returnT hb
    · exact hnRefine_of_pre_false (sepConj_false_right
        (sepConj_false_right (wordAssn_false hn)))
  · exact hnRefine_of_pre_false (sepConj_false_right
      (sepConj_false_left (wordAssn_false hm)))

/-- `x := x ⊕ z`, in place. Same side condition, same reason. -/
@[sepref_fr_rules]
theorem hnr_mop_binop_self_word (B : ℕ) (op : Imp.Bop) (x z : String) (m n : ℕ)
    (hb : op.apply m n < B) :
    hnRefine (hnCtxt (wordAssn B) m x ∗ hnCtxt (wordAssn B) n z) (.binop op x x z)
      (hnCtxt (wordAssn B) n z) x (wordAssn B) (mopBinop op m n) := by
  by_cases hm : m < B
  · by_cases hn : n < B
    · simp only [hnCtxt_def, wordAssn_of_lt hm, wordAssn_of_lt hn]
      refine hnRefine_word_res (hnr_mop_binop_self op x z m n) ?_
      rw [mopBinop_def]
      exact bound_res_consume_returnT hb
    · exact hnRefine_of_pre_false (sepConj_false_right (wordAssn_false hn))
  · exact hnRefine_of_pre_false (sepConj_false_left (wordAssn_false hm))

/-- `x := a[i]`. **No side condition**: the result's bound comes off the
*array's* ownership, and the index bound off the `mop`'s own `assert`.
This is the one operation where the verdict's story works exactly as
advertised. -/
@[sepref_fr_rules]
theorem hnr_mop_aget_word (B : ℕ) (x a i : String) (xs : List ℕ) (k : ℕ) :
    hnRefine (junkCell x ∗ hnCtxt (wordArrayAssn B) xs a ∗ hnCtxt (wordAssn B) k i)
      (.aget x a i)
      (hnCtxt (wordArrayAssn B) xs a ∗ hnCtxt (wordAssn B) k i) x (wordAssn B)
      (mopAget xs k) := by
  by_cases hxs : ∀ v ∈ xs, v < B
  · by_cases hk : k < B
    · simp only [hnCtxt_def, wordAssn_of_lt hk, wordArrayAssn_of_mem hxs]
      rw [mopAget_def]
      refine hnr_assert fun hklen => ?_
      refine hnRefine_word_res (hnRefineI_spect (aget_junk_rule x a i xs k hklen)) ?_
      refine bound_res_consume_returnT ?_
      rw [getElem!_pos xs k hklen]
      exact hxs _ (List.getElem_mem hklen)
    · exact hnRefine_of_pre_false (sepConj_false_right
        (sepConj_false_right (wordAssn_false hk)))
  · exact hnRefine_of_pre_false (sepConj_false_right
      (sepConj_false_left (wordArrayAssn_false hxs)))

/-- `a[i] := v`. **No side condition**: the stored value's bound comes
off its own cell, so the array stays bounded. -/
@[sepref_fr_rules]
theorem hnr_mop_aset_word (B : ℕ) (a i v : String) (xs : List ℕ) (k n : ℕ) :
    hnRefine (hnCtxt (wordArrayAssn B) xs a ∗ hnCtxt (wordAssn B) k i ∗
        hnCtxt (wordAssn B) n v) (.aset a i v)
      (hnCtxt (wordAssn B) k i ∗ hnCtxt (wordAssn B) n v) a (wordArrayAssn B)
      (mopAset xs k n) := by
  by_cases hxs : ∀ w ∈ xs, w < B
  · by_cases hk : k < B
    · by_cases hn : n < B
      · simp only [hnCtxt_def, wordAssn_of_lt hk, wordAssn_of_lt hn,
          wordArrayAssn_of_mem hxs]
        rw [mopAset_def]
        refine hnr_assert fun hklen => ?_
        refine hnRefine_wordArray_res (hnRefineI_spect (aset_mop_rule a i v xs k n hklen)) ?_
        refine bound_res_consume_returnT ?_
        intro w hw
        rcases List.mem_or_eq_of_mem_set hw with hw' | rfl
        · exact hxs w hw'
        · exact hn
      · exact hnRefine_of_pre_false (sepConj_false_right
          (sepConj_false_right (wordAssn_false hn)))
    · exact hnRefine_of_pre_false (sepConj_false_right
        (sepConj_false_left (wordAssn_false hk)))
  · exact hnRefine_of_pre_false (sepConj_false_left (wordArrayAssn_false hxs))

/-! ## 4. `BRefine` — the component the bounds pass actually needs

R2/D-b, built. `Codegen/Cash.lean` wants `∃ s' κ, Ir.BigStepB B c s₀ s' κ`,
and `BigStep.exists_bigStepB_of_inv` reduces that to `Ir.bpre B c Q s₀`.
`bpre` is *syntax-directed on the concrete `Com`*, exactly like
`hnRefine`'s translate phase, so it can be carried alongside the
judgment by rules of the same shape.

`BRefine B Γ c Γ'` is that second component, in continuation-passing
form: from any state the precondition holds of, under the state
invariant `Ir.StateBound B`, the residual bounds precondition holds.

**No `wordAssn` appears in it.** The abstract values are pinned by
ordinary `natAssn`/`arrayAssn` ownership — `natAssn m y` says the cell
`y` holds *exactly* `m` — and that is what replaces
`Examples/BfsQSynth.lean` §12's `FInv`/`DInv` state predicates, their
five `setVar`/`setArr` closure lemmas and their `Option.some.inj`
identification chains.

**R2/D-d — credits are threaded existentially, and the assertions must
be credit-free.** `bpre` knows nothing about credits, so the
continuation quantifies the balance. Every data assertion used with
`BRefine` must therefore own no `¤` conjunct; all of
`natAssn`/`arrayAssn`/`junkCell`/`junkArray` qualify. -/

/-- `BRefine B Γ c Γ'`: the `bpre` half of a synthesis. -/
def BRefine (B : ℕ) (Γ : Assn) (c : Com) (Γ' : Assn) : Prop :=
  ∀ (F : Assn) (Q : Ir.State → Prop) (s : Ir.State) (cr : ECost),
    irSTATE (Γ ∗ F) (s, cr) → Ir.StateBound B s →
    (∀ (s' : Ir.State) (cr' : ECost), irSTATE (Γ' ∗ F) (s', cr') →
      Ir.StateBound B s' → Q s') →
      Ir.bpre B c Q s

/-- Rewrite an `irSTATE` along an assertion equation — the `ac_rfl`
vehicle every op rule below permutes with. -/
theorem irSTATE_cong {P P' : Assn} {s : Ir.State} {cr : ECost} (he : P = P')
    (h : irSTATE P (s, cr)) : irSTATE P' (s, cr) := he ▸ h

/-! The four extraction lemmas of `Ir/Assn.lean`, restated at the
`natAssn`/`arrayAssn` spelling. They are the same theorems (`natAssn` is
`↦ᵥ` by definition), but `ac_rfl` compares atoms *syntactically*, so a
permutation goal must be stated in one spelling throughout — the P7/D-ba
lesson, one layer down. -/

theorem natAssn_vars {x : String} {v : ℕ} {F : Assn} {s : Ir.State} {cr : ECost}
    (h : irSTATE (natAssn v x ∗ F) (s, cr)) : s.vars x = some v := Ir.ptoVar_vars h

theorem natAssn_setVar {x : String} {v n : ℕ} {F : Assn} {s : Ir.State} {cr : ECost}
    (h : irSTATE (natAssn v x ∗ F) (s, cr)) :
    irSTATE (natAssn n x ∗ F) (s.setVar x n, cr) := Ir.ptoVar_setVar h

theorem arrayAssn_arrs {a : String} {xs : List ℕ} {F : Assn} {s : Ir.State} {cr : ECost}
    (h : irSTATE (arrayAssn xs a ∗ F) (s, cr)) : s.arrs a = some xs := Ir.ptoArr_arrs h

theorem arrayAssn_setArr {a : String} {xs ys : List ℕ} {F : Assn} {s : Ir.State}
    {cr : ECost} (h : irSTATE (arrayAssn xs a ∗ F) (s, cr)) :
    irSTATE (arrayAssn ys a ∗ F) (s.setArr a ys, cr) := Ir.ptoArr_setArr h

/-- **The consumer.** A `BRefine` at the caller's own hole is exactly the
`bpre` witness `exists_bigStepB_of_hnRefine` asks for. -/
theorem bpre_of_BRefine {B : ℕ} {Γ Γ' F : Assn} {c : Com} {s : Ir.State} {cr : ECost}
    (h : BRefine B Γ c Γ') (hs : irSTATE (Γ ∗ F) (s, cr)) (hSB : Ir.StateBound B s) :
    Ir.bpre B c (fun _ => True) s :=
  h F (fun _ => True) s cr hs hSB (fun _ _ _ _ => trivial)

/-! ### Structural rules -/

theorem BRefine.cons {B : ℕ} {Γ Γ₀ Γ' Γ'₀ : Assn} {c : Com} (h : BRefine B Γ₀ c Γ'₀)
    (hpre : Γ ⊢ Γ₀) (hpost : Γ'₀ ⊢ Γ') : BRefine B Γ c Γ' := by
  intro F Q s cr hs hSB hQ
  refine h F Q s cr (start_entailsE hs (sepConj_mono_left hpre)) hSB ?_
  exact fun s' cr' hs' hSB' => hQ s' cr' (start_entailsE hs' (sepConj_mono_left hpost)) hSB'

theorem BRefine.frame {B : ℕ} {Γ Γ' D : Assn} {c : Com} (h : BRefine B Γ c Γ') :
    BRefine B (Γ ∗ D) c (Γ' ∗ D) := by
  intro F Q s cr hs hSB hQ
  refine h (D ∗ F) Q s cr (irSTATE_cong (by ac_rfl) hs) hSB ?_
  exact fun s' cr' hs' hSB' => hQ s' cr' (irSTATE_cong (by ac_rfl) hs') hSB'

theorem BRefine.perm {B : ℕ} {Γ P Γ' P' : Assn} {c : Com} (he : Γ = P) (he' : P' = Γ')
    (h : BRefine B P c P') : BRefine B Γ c Γ' := by rw [he, ← he']; exact h

/-- Extracting a pure conjunct from the precondition — how a store's own
in-range hypothesis reaches the next operation. -/
theorem BRefine.pre_pure {B : ℕ} {Φ : Prop} {Γ Γ' : Assn} {c : Com}
    (h : Φ → BRefine B Γ c Γ') : BRefine B (⌜Φ⌝ ∗ Γ) c Γ' := by
  intro F Q s cr hs hSB hQ
  rw [sepConj_assoc] at hs
  obtain ⟨hΦ, hs'⟩ := predLift_sepConj_iff.1 hs
  exact h hΦ F Q s cr hs' hSB hQ

/-- …and opening an existential (`junkCell`, `junkArray`). -/
theorem BRefine.pre_ex {β : Type} {B : ℕ} {Γ : β → Assn} {Γ' : Assn} {c : Com}
    (h : ∀ y, BRefine B (Γ y) c Γ') : BRefine B (∃ᵃ y, Γ y) c Γ' := by
  intro F Q s cr hs hSB hQ
  rw [sepEx_sepConj] at hs
  obtain ⟨y, hy⟩ := hs
  exact h y F Q s cr hy hSB hQ

theorem BRefine.skip {B : ℕ} {Γ : Assn} : BRefine B Γ .skip Γ :=
  fun _ _ _ _ hs hSB hQ => hQ _ _ hs hSB

theorem BRefine.seq {B : ℕ} {Γ Γ₁ Γ' : Assn} {c d : Com}
    (h₁ : BRefine B Γ c Γ₁) (h₂ : BRefine B Γ₁ d Γ') : BRefine B Γ (.seq c d) Γ' := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_seq]
  exact h₁ F _ s cr hs hSB fun s' cr' hs' hSB' => h₂ F Q s' cr' hs' hSB' hQ

/-! ### The operation rules

One per `BigStepB` constructor that has a residual (P7/D-bl's table).
The side conditions are exactly the ones §3's `wordAssn` rules
surfaced — which is the point: the *content* of option (b) lives here,
and the assertion change does not. -/

/-- `x := n`: **the literal must fit**. -/
theorem BRefine.const {B : ℕ} {x : String} {n v : ℕ} (hn : n < B) :
    BRefine B (natAssn v x) (.const x n) (natAssn n x) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_const]
  exact ⟨hn, hQ _ cr (natAssn_setVar hs) (hSB.setVar hn)⟩

/-- `x := y`: nothing is created. -/
theorem BRefine.copy {B : ℕ} {x y : String} {v w : ℕ} :
    BRefine B (natAssn v x ∗ natAssn w y) (.copy x y) (natAssn w x ∗ natAssn w y) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_copy]
  intro w' hw'
  have hy : s.vars y = some w :=
    natAssn_vars (F := natAssn v x ∗ F) (irSTATE_cong (by ac_rfl) hs)
  obtain rfl : w = w' := Option.some.inj (hy ▸ hw')
  have h1 : irSTATE (natAssn v x ∗ (natAssn w y ∗ F)) (s, cr) := irSTATE_cong (by ac_rfl) hs
  have h2 := natAssn_setVar (n := w) h1
  exact hQ _ cr (irSTATE_cong (by ac_rfl) h2) (hSB.setVar (hSB.var hy))

/-- `x := y ⊕ z`: **the creation site**. The side condition is on the
*abstract* operands, which is where the abstract program's own loop
invariant is available — the whole content of the spike. -/
theorem BRefine.binop {B : ℕ} {op : Imp.Bop} {x y z : String} {v m n : ℕ}
    (hb : op.apply m n < B) :
    BRefine B (natAssn v x ∗ natAssn m y ∗ natAssn n z) (.binop op x y z)
      (natAssn (op.apply m n) x ∗ natAssn m y ∗ natAssn n z) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_binop]
  intro m' n' hm' hn'
  have hy : s.vars y = some m :=
    natAssn_vars (F := natAssn v x ∗ natAssn n z ∗ F) (irSTATE_cong (by ac_rfl) hs)
  have hz : s.vars z = some n :=
    natAssn_vars (F := natAssn v x ∗ natAssn m y ∗ F) (irSTATE_cong (by ac_rfl) hs)
  obtain rfl : m = m' := Option.some.inj (hy ▸ hm')
  obtain rfl : n = n' := Option.some.inj (hz ▸ hn')
  have h1 : irSTATE (natAssn v x ∗ (natAssn m y ∗ natAssn n z ∗ F)) (s, cr) :=
    irSTATE_cong (by ac_rfl) hs
  have h2 := natAssn_setVar (n := op.apply m n) h1
  exact ⟨hb, hQ _ cr (irSTATE_cong (by ac_rfl) h2) (hSB.setVar hb)⟩

/-- `x := x ⊕ z`, in place (the `mopSucc` shape). -/
theorem BRefine.binop_self {B : ℕ} {op : Imp.Bop} {x z : String} {m n : ℕ}
    (hb : op.apply m n < B) :
    BRefine B (natAssn m x ∗ natAssn n z) (.binop op x x z)
      (natAssn (op.apply m n) x ∗ natAssn n z) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_binop]
  intro m' n' hm' hn'
  have h0 : irSTATE (natAssn m x ∗ (natAssn n z ∗ F)) (s, cr) := irSTATE_cong (by ac_rfl) hs
  have hx : s.vars x = some m := natAssn_vars h0
  have hz : s.vars z = some n :=
    natAssn_vars (F := natAssn m x ∗ F) (irSTATE_cong (by ac_rfl) hs)
  obtain rfl : m = m' := Option.some.inj (hx ▸ hm')
  obtain rfl : n = n' := Option.some.inj (hz ▸ hn')
  have h2 := natAssn_setVar (n := op.apply m n) h0
  exact ⟨hb, hQ _ cr (irSTATE_cong (by ac_rfl) h2) (hSB.setVar hb)⟩

/-- `x := a[i]`: nothing is created — and the run *hands over*
`k < xs.length`, which is what makes the index facts free (P7/D-bl's
`aget` row). -/
theorem BRefine.aget {B : ℕ} {x a i : String} {v k : ℕ} {xs : List ℕ} :
    BRefine B (natAssn v x ∗ arrayAssn xs a ∗ natAssn k i) (.aget x a i)
      (⌜k < xs.length⌝ ∗ natAssn xs[k]! x ∗ arrayAssn xs a ∗ natAssn k i) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_aget]
  intro k' ys w hk' hys hw
  have hi : s.vars i = some k :=
    natAssn_vars (F := natAssn v x ∗ arrayAssn xs a ∗ F) (irSTATE_cong (by ac_rfl) hs)
  have ha : s.arrs a = some xs :=
    arrayAssn_arrs (F := natAssn v x ∗ natAssn k i ∗ F) (irSTATE_cong (by ac_rfl) hs)
  obtain rfl : k = k' := Option.some.inj (hi ▸ hk')
  obtain rfl : xs = ys := Option.some.inj (ha ▸ hys)
  obtain ⟨hklen, rfl⟩ := List.getElem?_eq_some_iff.1 hw
  rw [← getElem!_pos xs k hklen] at hw ⊢
  have h1 : irSTATE (natAssn v x ∗ (arrayAssn xs a ∗ natAssn k i ∗ F)) (s, cr) :=
    irSTATE_cong (by ac_rfl) hs
  have h2 := natAssn_setVar (n := xs[k]!) h1
  refine hQ _ cr (irSTATE_cong ?_ h2) (hSB.setVar (hSB.getElem ha hw))
  rw [predLift_of_true hklen, emp_sepConj]
  ac_rfl

/-- `a[i] := v`: nothing is created, and the store's own in-range
hypothesis is **handed to the caller** — the row of P7/D-bl's table that
pays for the whole file, here delivered as a pure postcondition
conjunct. -/
theorem BRefine.aset {B : ℕ} {a i v : String} {k n : ℕ} {xs : List ℕ} :
    BRefine B (arrayAssn xs a ∗ natAssn k i ∗ natAssn n v) (.aset a i v)
      (⌜k < xs.length⌝ ∗ arrayAssn (xs.set k n) a ∗ natAssn k i ∗ natAssn n v) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_aset]
  intro k' n' ys hk' hn' hys hklen
  have hi : s.vars i = some k :=
    natAssn_vars (F := arrayAssn xs a ∗ natAssn n v ∗ F) (irSTATE_cong (by ac_rfl) hs)
  have hv : s.vars v = some n :=
    natAssn_vars (F := arrayAssn xs a ∗ natAssn k i ∗ F) (irSTATE_cong (by ac_rfl) hs)
  have h0 : irSTATE (arrayAssn xs a ∗ (natAssn k i ∗ natAssn n v ∗ F)) (s, cr) :=
    irSTATE_cong (by ac_rfl) hs
  have ha : s.arrs a = some xs := arrayAssn_arrs h0
  obtain rfl : k = k' := Option.some.inj (hi ▸ hk')
  obtain rfl : n = n' := Option.some.inj (hv ▸ hn')
  obtain rfl : xs = ys := Option.some.inj (ha ▸ hys)
  have h2 := arrayAssn_setArr (ys := xs.set k n) h0
  refine hQ _ cr (irSTATE_cong ?_ h2) (hSB.setArr ha (hSB.var hv))
  rw [predLift_of_true hklen, emp_sepConj]
  ac_rfl

/-! ### Control

A loop's assertion is `LoopAssn I Γ`: the abstract state exists, the
abstract invariant holds of it, and the concrete assertion is at that
state. This is where the *abstract* program's own invariant — the one
wave A already proved for correctness — is what supplies `tl ≤ n` and
the queue's vertex facts, rather than a second copy of them over
`Ir.State`. -/

/-- The loop's assertion, over the abstract state. -/
def LoopAssn {σ : Type} (I : σ → Prop) (Γ : σ → Assn) : Assn := ∃ᵃ t, (⌜I t⌝ ∗ Γ t)

theorem loopAssn_intro {σ : Type} {I : σ → Prop} {Γ : σ → Assn} {t : σ}
    (hI : I t) : Γ t ⊢ LoopAssn I Γ := by
  intro p hp
  exact ⟨t, predLift_sepConj_iff.2 ⟨hI, hp⟩⟩

/-- A branch: the guard's literals must fit, and both arms must reach the
same postcondition (merge by `BRefine.cons`, as the frame layer's
`MERGE` does). -/
theorem BRefine.ite {B : ℕ} {Γ Γ' : Assn} {b : Cond} {c d : Com}
    (hlit : b.LitLt B) (ht : BRefine B Γ c Γ') (he : BRefine B Γ d Γ') :
    BRefine B Γ (.ite b c d) Γ' := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_ite]
  exact ⟨fun _ hev => Ir.Cond.evalB_of_stateBound hSB hlit hev,
    fun _ => ht F Q s cr hs hSB hQ, fun _ => he F Q s cr hs hSB hQ⟩

/-- A loop: the guard's literals must fit and the body must preserve the
loop assertion. **No variant** — termination comes from the run
(P7/D-bl's `while` row, and R0/D-b at the synthesis layer). -/
theorem BRefine.while {B : ℕ} {σ : Type} {I : σ → Prop} {Γ : σ → Assn} {Γ' : Assn}
    {b : Cond} {c : Com} (hlit : b.LitLt B)
    (hbody : BRefine B (LoopAssn I Γ) c (LoopAssn I Γ))
    (hexit : LoopAssn I Γ ⊢ Γ') :
    BRefine B (LoopAssn I Γ) (.while b c) Γ' := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_while]
  refine ⟨fun t => (∃ cr', irSTATE (LoopAssn I Γ ∗ F) (t, cr')) ∧ Ir.StateBound B t,
    ⟨⟨cr, hs⟩, hSB⟩, ?_, ?_, ?_⟩
  · exact fun t _ hInv hev => Ir.Cond.evalB_of_stateBound hInv.2 hlit hev
  · rintro t ⟨⟨cr', hs'⟩, hSB'⟩ _
    exact hbody F _ t cr' hs' hSB' fun s'' cr'' h'' hSB'' => ⟨⟨cr'', h''⟩, hSB''⟩
  · rintro t ⟨⟨cr', hs'⟩, hSB'⟩ _
    exact hQ t cr' (start_entailsE hs' (sepConj_mono_left hexit)) hSB'

/-- **The loop rule an engine actually needs**: the body is entered only
when the guard holds, and `hg` is what turns the *concrete* guard's truth
into the *abstract* guard's — the `CondRefine` obligation of the
synthesis layer, restated for the bounds pass. This is the one place the
two layers must agree, and it is one lemma per guard shape, not one per
program. -/
theorem BRefine.while_guard {B : ℕ} {σ : Type} {I : σ → Prop} {Γ : σ → Assn} {Γ' : Assn}
    {b : Cond} {c : Com} {bf : σ → Bool} (hlit : b.LitLt B)
    (hg : ∀ (t : σ) (F : Assn) (s : Ir.State) (cr : ECost) (r : Bool),
      I t → irSTATE (Γ t ∗ F) (s, cr) → b.eval s = some r → bf t = r)
    (hbody : ∀ t, I t → bf t = true → BRefine B (Γ t) c (LoopAssn I Γ))
    (hexit : ∀ t, I t → bf t = false → (Γ t ⊢ Γ')) :
    BRefine B (LoopAssn I Γ) (.while b c) Γ' := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_while]
  refine ⟨fun t => (∃ cr', irSTATE (LoopAssn I Γ ∗ F) (t, cr')) ∧ Ir.StateBound B t,
    ⟨⟨cr, hs⟩, hSB⟩, ?_, ?_, ?_⟩
  · exact fun t _ hInv hev => Ir.Cond.evalB_of_stateBound hInv.2 hlit hev
  · rintro t ⟨⟨cr', hs'⟩, hSB'⟩ hev
    rw [LoopAssn, sepEx_sepConj] at hs'
    obtain ⟨u, hu⟩ := hs'
    rw [sepConj_assoc] at hu
    obtain ⟨hIu, hu'⟩ := predLift_sepConj_iff.1 hu
    exact hbody u hIu (hg u F t cr' true hIu hu' hev) F _ t cr' hu' hSB'
      fun s'' cr'' h'' hSB'' => ⟨⟨cr'', h''⟩, hSB''⟩
  · rintro t ⟨⟨cr', hs'⟩, hSB'⟩ hev
    rw [LoopAssn, sepEx_sepConj] at hs'
    obtain ⟨u, hu⟩ := hs'
    rw [sepConj_assoc] at hu
    obtain ⟨hIu, hu'⟩ := predLift_sepConj_iff.1 hu
    have hu2 : irSTATE (Γ u ∗ F) (t, cr') := hu'
    exact hQ t cr' (start_entailsE hu2
      (sepConj_mono_left (hexit u hIu (hg u F t cr' false hIu hu' hev)))) hSB'

/-! ## 5. Gate (ledger D4, refute before prove)

Every authored rule of §3 gets its side condition exercised negatively;
§4's rules get a positive end-to-end control and a negative one; and the
pipeline probe of R2/D-c is pinned. -/

namespace Gate

/-! ### The refutation vehicle

A `wordAssn B`-result judgment *forces* an admissible result to be
bounded — the assertion is not decoration. Everything below is an
instance. -/

theorem lt_of_sepConj_wordAssn {B a : ℕ} {c : String} {R : Assn} {h : AState}
    (hh : (wordAssn B a c ∗ R) h) : a < B := by
  obtain ⟨u, v, -, -, hu, -⟩ := hh
  exact lt_of_wordAssn hu

/-- **The vehicle.** If a synthesis delivers its result at `wordAssn B`,
then some result the abstract program admits is below `B`. Refuting a
rule is therefore refuting an arithmetic fact. -/
theorem res_lt_of_hnRefine_wordAssn {B : ℕ} {Γ Γ' F : Assn} {c : Com} {x : String}
    {m : NRest ℕ ECost} {M : ℕ → WithBot ECost} {s : Ir.State} {cr : ECost}
    (h : hnRefine Γ c Γ' x (wordAssn B) m) (hm : m = .rest M)
    (hs : irSTATE (Γ ∗ F) (s, cr)) : ∃ a, M a ≠ ⊥ ∧ a < B := by
  obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD h hm hs
  refine ⟨ra, ?_, ?_⟩
  · intro hbot
    rw [hbot, le_bot_iff] at hCa
    exact absurd hCa WithBot.coe_ne_bot
  · rw [Ir.wp_def] at w
    obtain ⟨s', κ, -, hpost, -⟩ := w
    obtain ⟨u, v, -, -, -, hv⟩ := hpost
    exact lt_of_sepConj_wordAssn hv

/-! ### One state, for all the controls -/

def gState : Ir.State := Ir.State.ofPairs [("x", 0), ("y", 3), ("z", 4)] [("A", [1, 2, 3])]

def gFrame : Assn :=
  EXACT (((((vcells gState).erase "x").erase "y").erase "z", (acells gState).erase "A"), 0)

/-- The owned half, with the destination cell *live* (§4's shape). -/
def gPreL : Assn :=
  natAssn 0 "x" ∗ hnCtxt natAssn 3 "y" ∗ hnCtxt natAssn 4 "z" ∗
    hnCtxt arrayAssn [1, 2, 3] "A"

/-- …and with it junk (§3's shape). -/
def gPre : Assn :=
  junkCell "x" ∗ hnCtxt natAssn 3 "y" ∗ hnCtxt natAssn 4 "z" ∗
    hnCtxt arrayAssn [1, 2, 3] "A"

theorem gPreL_holds : irSTATE (gPreL ∗ gFrame) (gState, 0) := by
  show (gPreL ∗ gFrame) ((vcells gState, acells gState), 0)
  simp only [gPreL, hnCtxt_def, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact Ir.ptoArr_sepConj_iff.2 ⟨rfl, rfl⟩

theorem gPre_holds : irSTATE (gPre ∗ gFrame) (gState, 0) :=
  start_entailsE gPreL_holds
    (sepConj_mono_left (sepConj_mono_left (natAssn_entails_junkCell 0 "x")))

theorem gState_bound : Ir.StateBound 100 gState :=
  Codegen.stateBound_ofPairs (by decide) (by decide)

/-! ### Positive controls for §3 -/

example : hnRefine (junkCell "x" ∗ hnCtxt (wordAssn 8) 3 "y" ∗ hnCtxt (wordAssn 8) 4 "z")
    (.binop .add "x" "y" "z") (hnCtxt (wordAssn 8) 3 "y" ∗ hnCtxt (wordAssn 8) 4 "z") "x"
    (wordAssn 8) (mopBinop .add 3 4) :=
  hnr_mop_binop_word 8 .add "x" "y" "z" 3 4 (by decide)

example : hnRefine (junkCell "x") (.const "x" 7) (□ : Assn) "x" (wordAssn 8)
    (mopConstN 7) := hnr_mop_constN_word 8 "x" 7 (by decide)

example : hnRefine (junkCell "x" ∗ hnCtxt (wordArrayAssn 8) [1, 2, 3] "A" ∗
      hnCtxt (wordAssn 8) 1 "y") (.aget "x" "A" "y")
    (hnCtxt (wordArrayAssn 8) [1, 2, 3] "A" ∗ hnCtxt (wordAssn 8) 1 "y") "x" (wordAssn 8)
    (mopAget [1, 2, 3] 1) :=
  hnr_mop_aget_word 8 "x" "A" "y" [1, 2, 3] 1

example : hnRefine (hnCtxt (wordArrayAssn 8) [1, 2, 3] "A" ∗ hnCtxt (wordAssn 8) 1 "y" ∗
      hnCtxt (wordAssn 8) 4 "z") (.aset "A" "y" "z")
    (hnCtxt (wordAssn 8) 1 "y" ∗ hnCtxt (wordAssn 8) 4 "z") "A" (wordArrayAssn 8)
    (mopAset [1, 2, 3] 1 4) :=
  hnr_mop_aset_word 8 "A" "y" "z" [1, 2, 3] 1 4

/-! ### Negative controls for §3: every side condition bites

Four families, one refutation each.

1. **The operand bounds** (`hm`/`hn`/`hxs`/`hk` of every rule). A
   `wordAssn` at an out-of-range value is not a weaker assertion, it is
   `sepFalse`: the rule is inapplicable because its precondition owns
   nothing. -/

example : wordAssn 8 8 "x" = (sepFalse : Assn) := wordAssn_of_ge (by decide)

example : wordArrayAssn 8 [1, 9, 3] "A" = (sepFalse : Assn) :=
  wordArrayAssn_of_not_mem (by decide)

/-! 2. **The `aget`/`aset` index bound** (`hklen`). Without it the
abstract operation is `fail`, and a `fail` has no `hnRefine` consumer at
all — `hnRefine`'s first premise is `m.nofailT`. -/

example : mopAget [1, 2, 3] 5 = NRest.fail := by
  rw [mopAget_def, NRest.assert_neg (by decide), NRest.bindT_fail]

example : mopAset [1, 2, 3] 5 0 = NRest.fail := by
  rw [mopAset_def, NRest.assert_neg (by decide), NRest.bindT_fail]

/-! 3. **The `const` creation site** (`hn`). `x := 8` at `B = 8` has no
`wordAssn 8` judgment — not because the rule refuses to fire, but
because the conclusion is *false*: the vehicle would give `8 < 8`. -/

theorem mopConstN_gate (n : ℕ) :
    mopConstN n = NRest.rest (NRest.single n ((irUnit Currency.const : ECost) :
      WithBot ECost)) := by
  rw [mopConstN_def, NRest.consume_returnT]

theorem no_constN_word_at_bound :
    ¬ hnRefine (junkCell "x") (.const "x" 8) (□ : Assn) "x" (wordAssn 8) (mopConstN 8) := by
  intro h
  obtain ⟨a, hne, hlt⟩ := res_lt_of_hnRefine_wordAssn
    (F := hnCtxt natAssn 3 "y" ∗ hnCtxt natAssn 4 "z" ∗
      hnCtxt arrayAssn [1, 2, 3] "A" ∗ gFrame)
    h (mopConstN_gate 8) (irSTATE_cong (by rw [gPre]; ac_rfl) gPre_holds)
  by_cases ha : a = 8
  · omega
  · exact hne (NRest.single_of_ne ha _)

/-! 4. **The `binop` creation site** (`hb`) — the row P7/D-bl says cannot
be made state-local. Both operands fit in `B = 7`; their sum does not. -/

theorem mopBinop_gate (op : Imp.Bop) (m n : ℕ) :
    mopBinop op m n = NRest.rest (NRest.single (op.apply m n)
      ((irUnit (binopCurrency op) : ECost) : WithBot ECost)) := by
  rw [mopBinop_def, NRest.consume_returnT]

theorem no_binop_word_at_bound :
    ¬ hnRefine gPre (.binop .add "x" "y" "z")
      (hnCtxt natAssn 3 "y" ∗ hnCtxt natAssn 4 "z" ∗ hnCtxt arrayAssn [1, 2, 3] "A") "x"
      (wordAssn 7) (mopBinop .add 3 4) := by
  intro h
  obtain ⟨a, hne, hlt⟩ := res_lt_of_hnRefine_wordAssn (F := gFrame)
    h (mopBinop_gate .add 3 4) gPre_holds
  by_cases ha : a = Imp.Bop.apply .add 3 4
  · rw [Imp.Bop.apply_add] at ha; omega
  · exact hne (NRest.single_of_ne ha _)

/-- …and the in-place rule shares that side condition exactly
(`hnr_mop_binop_self_word`'s `hb` is `hnr_mop_binop_word`'s), so the same
refutation covers it. -/
theorem no_binop_self_word_at_bound :
    ¬ hnRefine (hnCtxt natAssn 3 "y" ∗ hnCtxt natAssn 4 "z") (.binop .add "y" "y" "z")
      (hnCtxt natAssn 4 "z") "y" (wordAssn 7) (mopBinop .add 3 4) := by
  intro h
  obtain ⟨a, hne, hlt⟩ := res_lt_of_hnRefine_wordAssn
    (F := junkCell "x" ∗ hnCtxt arrayAssn [1, 2, 3] "A" ∗ gFrame)
    h (mopBinop_gate .add 3 4) (irSTATE_cong (by rw [gPre]; ac_rfl) gPre_holds)
  by_cases ha : a = Imp.Bop.apply .add 3 4
  · rw [Imp.Bop.apply_add] at ha; omega
  · exact hne (NRest.single_of_ne ha _)

/-! ### Controls for §4 (`BRefine`)

The positive control runs a two-op straight-line program all the way to
an `Ir.bpre` witness at a concrete state; the negative one is the same
program at a bound its arithmetic overflows. -/

/-- `x := y + z` then `x := x + z`, at `B = 100`. Two creation sites,
two side conditions, both `by decide`; the frame carries `y` across the
second, and no `Ir.State` predicate is authored anywhere. -/
theorem brefine_demo :
    BRefine 100 (natAssn 0 "x" ∗ natAssn 3 "y" ∗ natAssn 4 "z")
      ((Com.binop .add "x" "y" "z").seq (Com.binop .add "x" "x" "z"))
      (natAssn (Imp.Bop.apply .add (Imp.Bop.apply .add 3 4) 4) "x" ∗ natAssn 4 "z" ∗
        natAssn 3 "y") := by
  refine BRefine.seq (BRefine.binop (v := 0) (by decide)) ?_
  refine BRefine.perm
    (P := (natAssn (Imp.Bop.apply .add 3 4) "x" ∗ natAssn 4 "z") ∗ natAssn 3 "y")
    (P' := (natAssn (Imp.Bop.apply .add (Imp.Bop.apply .add 3 4) 4) "x" ∗ natAssn 4 "z") ∗
      natAssn 3 "y")
    (by ac_rfl) (by ac_rfl) ?_
  exact BRefine.frame (D := natAssn 3 "y")
    (BRefine.binop_self (op := .add) (x := "x") (z := "z")
      (m := Imp.Bop.apply .add 3 4) (n := 4) (by decide))

/-- **The bounds witness, end to end.** `Ir.bpre` at a concrete state,
with no `Ir.State` invariant authored: the assertion *is* the
invariant. This is what `Codegen/Cash.lean`'s `exists_bigStepB_of_hnRefine`
consumes. -/
theorem brefine_demo_bpre :
    Ir.bpre 100 ((Com.binop .add "x" "y" "z").seq (Com.binop .add "x" "x" "z"))
      (fun _ => True) gState :=
  bpre_of_BRefine (F := hnCtxt arrayAssn [1, 2, 3] "A" ∗ gFrame) brefine_demo
    (irSTATE_cong (by rw [gPreL]; ac_rfl) gPreL_holds) gState_bound

/-- **Refuted at the bound.** The same program at `B = 8`: `3 + 4 = 7`
still fits, `7 + 4 = 11` does not, and `bpre` is false at the second
site — so no `BRefine 8` for this program can exist. -/
theorem no_bpre_at_bound :
    ¬ Ir.bpre 8 ((Com.binop .add "x" "y" "z").seq (Com.binop .add "x" "x" "z"))
      (fun _ => True) gState := by
  rw [Ir.bpre_seq]
  intro h
  rw [Ir.bpre_binop] at h
  obtain ⟨-, h2⟩ := h 3 4 rfl rfl
  rw [Ir.bpre_binop] at h2
  exact absurd (h2 7 4 rfl rfl).1 (by decide)


/-! ### R2/D-c: the pipeline probe

Two `#sepref_synth` runs at `wordAssn`, reported rather than thrown
(`Sepref/Definition.lean`'s negative-control precedent). The first is a
single operation; the second adds a `bindT`, which is what makes
`hnr_bind` abstract the bound value's ownership.

**What they report** (the spike's pipeline telemetry):

1. **One operation synthesizes.** `Com.binop Imp.Bop.add "t" "a" "b"`,
   at `wordAssn` throughout. So the frame matcher has *no* problem with
   `wordAssn`: `hnCtxt (wordAssn B) a "a"` is a single `Expr` atom, and
   `absAgree` pairs it by the abstract value as usual. The P6/D-bc
   composite-assertion opacity does **not** bite, and no wrapper is
   needed. This is the one clean positive result for option (b).

2. **Two operations do not.** Both combinator routes stall on the same
   root cause:

   * `hnr_bind`: *"the bound value's ownership `hnCtxt (wordAssn B) a✝
     "t"` survives the block, and there is no junk form for its
     assertion — the postcondition cannot be closed over the binder"* —
     `Sepref/Translate.lean`'s `junkConjunct`, verbatim;
   * `hnr_seq`: the rule fires and produces the right
     `Com.binop mul "r" "t" "c"`, but the postcondition it proves
     mentions the binder and `?Γ'` cannot be assigned it.

   Fix: two lines in `junkConjunct` (a `wordAssn`/`wordArrayAssn` case),
   or better, replace its constant dispatch by an `MK_FREE`-style
   database lookup. Neither is in this spike's remit (new files only).

An earlier revision of §3 took the operand bounds as rule hypotheses;
the probe then stalled *earlier still*, on `"the side condition was not
closed: a✝¹ < B"`. That is R2/D-e in the flesh: the bound sits in the
assertion, and the side-condition solver cannot read it, because a
side condition is an ordinary Lean goal with no access to the
precondition. Discharging the operand bounds by vacuity instead is what
made probe 1 succeed at all. -/

section Probe

#sepref_synth (B a b : ℕ) (hab : Imp.Bop.apply .add a b < B) :
  hnRefine (junkCell "t" ∗ hnCtxt (wordAssn B) a "a" ∗ hnCtxt (wordAssn B) b "b")
    _ _ "t" (wordAssn B) (mopBinop .add a b)

#sepref_synth (B a b c : ℕ) (hab : Imp.Bop.apply .add a b < B)
    (habc : ∀ x : ℕ, Imp.Bop.apply .mul x c < B) :
  hnRefine (junkCell "t" ∗ junkCell "r" ∗ hnCtxt (wordAssn B) a "a" ∗
      hnCtxt (wordAssn B) b "b" ∗ hnCtxt (wordAssn B) c "c")
    _ _ "r" (wordAssn B)
    (NRest.bindT (mopBinop .add a b) fun x => mopBinop .mul x c)

end Probe

/-! ### Axioms -/

#print axioms hnr_mop_binop_word
#print axioms hnr_mop_aget_word
#print axioms brefine_demo_bpre
#print axioms no_binop_word_at_bound

end Gate

end WordSpike

end Lax13Proofs.Refine.Sepref
