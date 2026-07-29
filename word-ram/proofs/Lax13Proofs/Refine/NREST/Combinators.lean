import Lax13Proofs.Refine.NREST.Rec

/-!
The derived program combinators: monadic `if`, `whileT`, and `FOREACH`.

Port of the `Monadic if` and `While` sections of `thys/nrest/NREST.thy`
of `isabelle_llvm_time` (Haslbeck–Lammich, ESOP'21 artifact) at the pin
recorded in `plans/word-ram/refinement-tower/design.md` §1,
github.com/lammich/isabelle_llvm_time @ 42dd7f5, plus the `FOREACH`
definitions of AFP `NREST`'s `Refine_Foreach.thy` (Isabelle2025-2).
Fetched 2026-07-29 from the pins.

## Where the combinators actually live (checked, not assumed)

`Monadic_Operations.thy` of the artifact does **not** hold any control
combinator: its 62 lines are the `mop_…` data-structure interface
operations (`mop_set_pick_extract`, `mop_matrix_get`, `mop_append`, …),
which belong to the IICF layer (P6). `MIf`, `monadic_If`, `RECT`,
`whileT`, `whileIET`, `monadic_WHILEIT` are all in `NREST.thy` itself.

**FOREACH is absent from the cost artifact entirely.** `grep FOREACH`
over the artifact's whole `thys/nrest/` (`Data_Refinement`,
`Monadic_Operations`, `NREST`, `NREST_Automation`,
`NREST_Backwards_Reasoning`, `NREST_Main`, `NREST_Misc`,
`NREST_Type_Classes`, `Refine_Heuristics`, `Remdups`,
`Time_Refinement`) returns nothing. It exists only in the AFP `NREST`
entry's `Refine_Foreach.thy`, which is the *pre-currency* nrest — its
resource carrier is plain `enat`, not `(_, enat) acost`. The `FOREACH`
section below is therefore ported from that file, monomorphically at
`ℕ∞`, as the campaign brief directs: definitions plus the arm/mono
lemmas only. The rule suite (`FOREACHoci_rule`, `FOREACHci_rule`,
`nfoldli`/`nfoldliIE` and the `LIST_FOREACH` refinements) is
`gwp`-shaped and waits for the backwards-reasoning file, and the
currency-carrying re-statement waits for a consumer that needs it.

## The source, verbatim

`NREST.thy`, `Monadic if`:

```isabelle
definition "consumea T = SPECT [()↦T]"
lemma consume_alt2: fixes M :: "(_,(_,enat) acost) nrest"
  shows "consume M T = do { consumea T; M}"

definition "MIf a b c = consume (if a then b else c) (cost ''if'' 1)"
abbreviation monadic_If :: "(bool,_) nrest ⇒ ('b,_) nrest ⇒ ('b,_) nrest ⇒ ('b,_) nrest"
  where "monadic_If b x y ≡ do { t ← b; MIf t x y }"
lemma flat_ge_MIf[refine_mono]: fixes f :: "(_,(_,enat)acost) nrest"
  shows "⟦flat_ge f f'; flat_ge g g'⟧ ⟹ flat_ge (MIf xb f g) (MIf xb f' g')"
lemma MIf_mono[refine_mono]:    fixes f :: "(_,(_,enat)acost) nrest"
  shows "⟦f ≤ f'; g ≤ g'⟧ ⟹ (MIf xb f g) ≤ (MIf xb f' g')"
```

`NREST.thy`, `While`:

```isabelle
definition whileT :: "('a ⇒ bool) ⇒ ('a ⇒ ('a,_) nrest) ⇒ 'a ⇒ ('a,_) nrest" where
  "whileT b c = RECT (λwhileT s. (if b s then bindT (c s) whileT else RETURNT s))"

lemma whileT_unfold_enat:  fixes c :: "_⇒(_,enat) nrest"
  shows "whileT b c = (λs. (if b s then bindT (c s) (whileT b c) else RETURNT s))"
lemma whileT_unfold_acost: fixes c :: "_⇒(_,(_,enat)acost) nrest"   (same statement)
lemma whileT_mono_enat:  fixes c :: "_⇒(_,enat) nrest"
  assumes "⋀x. b x ⟹ c x ≤ c' x"  shows "(whileT b c x) ≤ (whileT b c' x)"
lemma whileT_mono_fenat: fixes c :: "_⇒(_,(_,enat)acost) nrest"     (same statement)

definition "monadic_WHILEIT I b f s ≡ do {
  SPECT [()↦ (cost ''call'' 1)];
  RECT (λD s. do {
    ASSERT (I s);
    bv ← b s;
    MIf bv (do { s ← f s; SPECT [()↦ (cost ''call'' 1)]; D s }) (do {RETURNT s})
  }) s }"

lemma monadic_WHILEIT_RECT'_conv: fixes f :: "'b ⇒ ('b, (char list, enat) acost) nrest"
  shows "monadic_WHILEIT I b f s ≡ do {
  RECT' (λD s. do { ASSERT (I s); bv ← b s;
    MIf bv (do { s ← f s; D s }) (do {RETURNT s}) }) s }"

definition "monadic_WHILEIT' I b f s ≡ do {
  RECT (λD s. do { ASSERT (I s); bv ← b s;
    MIf bv (do { s ← f s; SPECT [()↦ (cost ''call'' 1)]; D s }) (do {RETURNT s}) }) s }"

definition whileIET :: "('a ⇒ bool) ⇒ ('a ⇒ _) ⇒ ('a ⇒ bool)
    ⇒ ('a ⇒ ('a,'c::{complete_lattice,plus,zero,monoid_add}) nrest) ⇒ 'a ⇒ ('a,'c) nrest" where
  "⋀E c. whileIET I E b c = whileT b c"

definition "monadic_WHILEIET  I E b f s ≡ monadic_WHILEIT  I b f s"
definition "monadic_WHILEIET' I E b f s ≡ monadic_WHILEIT' I b f s"
```

AFP `NREST`, `Refine_Foreach.thy`:

```isabelle
definition "FOREACH_body f ≡ λ(xs, σ). do {
  x ← RETURNT( hd xs); σ'←f x σ; RETURNT (tl xs,σ') }"
definition FOREACH_cond where "FOREACH_cond c ≡ (λ(xs,σ). xs≠[] ∧ c σ)"

definition FOREACHoci where "FOREACHoci R Φ S c f σ0 inittime body_time ≡ do {
  ASSERT (finite S);
  xs ← SPECT (emb (λxs. distinct xs ∧ S = set xs ∧ sorted_wrt R xs) inittime);
  (_,σ) ← whileIET (λ(it,σ). ∃xs'. xs = xs' @ it ∧ Φ (set it) σ)
                   (λ(it,_). length it * body_time)
                   (FOREACH_cond c) (FOREACH_body f) (xs,σ0);
  RETURNT σ }"
definition FOREACHci where "FOREACHci ≡ FOREACHoci (λ_ _. True)"

definition emb' where "⋀Q T. emb' Q (T::'a ⇒ enat) = (λx. if Q x then Some (T x) else None)"
abbreviation "emb Q t ≡ emb' Q (λ_. t)"
lemma SPEC_REST_emb'_conv: "SPEC P t = REST (emb' P t)"
```

## Substrate decisions and deviations, individually

**C1 (`bool` splits).** HOL's single `bool` becomes two Lean types here.
Loop and branch *conditions* are `Bool`: this is forced by the source
text, not chosen — `monadic_WHILEIT` binds `bv ← b s` with
`b : 'a ⇒ (bool,_) nrest` and feeds the bound value to `MIf`, so the
first argument of `MIf` is a *program value* of type bool, which in Lean
must be `Bool`; `whileT`'s `b : 'a ⇒ bool` follows it. Specification
predicates (invariants `I`, `Φ`, the orders `R`) stay `Prop`, which is
what `Basic.lean` already chose for `ASSERT` and `SPEC`. So `whileT`
and `MIf` compute their branch, and `assert` does not.

**C2 (`whileT_unfold` stated once).** The source states
`whileT_unfold_enat` and `whileT_unfold_acost` separately, and likewise
the two `whileT_mono`s, because its `refine_mono` seeds
(`bindT_mono'`, `bindT_flat_mono`, …) are stated at `enat` and at
`(_,enat) acost`. Our `NRest.bindT_mono` (`Pw.lean`) and
`NRest.bindT_flatGe` (`Rec.lean`) are generic and need no continuity of
`+` over `Sup`, so the same proof runs at every carrier: the primary
statements below are generic, and the four source-named corollaries
`whileT_unfold_enat` / `_acost` / `whileT_mono_enat` / `_fenat` are
kept, at exactly the source's carriers, as the citable forms. This is a
*recorded generalisation*, and it is the opposite case to fidelity note
F7's monad laws, where the source's monomorphism carries real
mathematical content (continuity) and was therefore preserved.

**C3 (the body is named).** The source writes `whileT`'s body inline
inside `whileT_def`. `NRest.whileBody` names it, so that the `mono2`
obligation every `RECT` lemma takes can be discharged once
(`NRest.mono2_whileBody`) instead of inside each proof;
`NRest.whileT_def` records that `whileT` is still literally the source's
term.

**C4 (`hd`).** `FOREACH_body` uses HOL's `hd`, total by `undefined` on
`[]`. Lean's counterpart is `List.headI`, which asks for `Inhabited`.
`FOREACH_cond` guarantees the list is non-empty wherever the body runs,
so nothing depends on the value; the class argument is the only trace.

**C5 (`emb`).** AFP `NREST`'s `emb Q t` is not ported as a separate
definition: `SPEC_REST_emb'_conv` says `SPEC P t = REST (emb' P t)`, so
`emb Q t` *is* `NRest.spec Q (fun _ => t)` of `Basic.lean`, and that is
what `FOREACHoci` uses.

**C6 (`consumea` landed here, and has since moved).** `consumea` sits in
`NREST.thy` next to `consume`, i.e. logically in `Basic.lean`; P1
defined it here instead because `Basic.lean` was frozen for that slice
and `consume_alt2` is what `monadic_WHILEIT_RECT'_conv` runs on. **P2
wave A moved both up to `Basic.lean`**, names unchanged
(`NRest.consumea`, `NRest.consumea_ne_fail`, `NRest.consume_alt2`);
this file still uses them, now through its existing import chain.
`consume_alt2`'s proof had to change: `Basic.lean` sits below
`Pw.lean`, so `bindT_rest_eq_iSup` is not available there and the same
fact is read off `bindT_rest`'s set comprehension directly, which at
`Unit` is a singleton. The statement is untouched.

**C7 (the D4 gate).** As in `Rec.lean` (substrate decision S6): the
fuel approximants of `Rec.lean`, the executable twins of `Sanity.lean`,
and `RECT_eq_of_fuelIter_stable` turn a kernel-checked stability test
into an exact value for `whileT` itself. Plausible then samples loop
bodies against the approximants.
-/

namespace Lax13Proofs.Refine

namespace NRest

variable {α β γ σ ε κ : Type}

/-! ### Monadic `if`

`MIf` is where the loop/branch overhead currency enters: taking a branch
costs one `''if''` unit, on top of whatever the branch itself costs. -/

/-- The source's `MIf a b c = consume (if a then b else c) (cost ''if'' 1)`.
The condition is a `Bool` — a value the program computed — per substrate
decision C1. -/
noncomputable def MIf [AddMonoid γ] [One γ] (a : Bool) (b c : NRest α (ACost String γ)) :
    NRest α (ACost String γ) :=
  consume (if a then b else c) (ACost.cost "if" 1)

@[simp] theorem MIf_true [AddMonoid γ] [One γ] (b c : NRest α (ACost String γ)) :
    MIf true b c = consume b (ACost.cost "if" 1) := by simp [MIf]

@[simp] theorem MIf_false [AddMonoid γ] [One γ] (b c : NRest α (ACost String γ)) :
    MIf false b c = consume c (ACost.cost "if" 1) := by simp [MIf]

/-- The source's `monadic_If b x y ≡ do { t ← b; MIf t x y }`: the
condition is itself a computation, so it may cost and it may fail. -/
noncomputable def monadicIf [CompleteLattice γ] [AddMonoid γ] [One γ]
    (b : NRest Bool (ACost String γ)) (x y : NRest α (ACost String γ)) :
    NRest α (ACost String γ) :=
  bindT b fun t => MIf t x y

@[simp] theorem monadicIf_fail [CompleteLattice γ] [AddMonoid γ] [One γ]
    (x y : NRest α (ACost String γ)) : monadicIf fail x y = fail := rfl

/-- The source's `flat_ge_MIf`, at the source's carrier. -/
theorem flatGe_MIf {a : Bool} {f f' g g' : NRest α ECost} (hf : flatGe f f')
    (hg : flatGe g g') : flatGe (MIf a f g) (MIf a f' g') :=
  flatGe_consume (monotoneRel_ite (a = true) hf hg) _

/-- The source's `MIf_mono`, at the source's carrier. -/
theorem MIf_mono {a : Bool} {f f' g g' : NRest α ECost} (hf : f ≤ f') (hg : g ≤ g') :
    MIf a f g ≤ MIf a f' g' :=
  consume_mono (monotoneRel_ite (a = true) hf hg) le_rfl

/-! ### `whileT`

The source's while loop: a `RECT` whose body runs one iteration and
recurses, or returns. Everything below rests on `mono2_whileBody`,
which is the `refine_mono` seed set of `Rec.lean` applied once
(substrate decision C3). -/

/-- The body functional of the source's
`whileT b c = RECT (λwhileT s. if b s then bindT (c s) whileT else RETURNT s)`. -/
noncomputable def whileBody [CompleteLattice γ] [AddMonoid γ] (b : α → Bool)
    (c : α → NRest α γ) : (α → NRest α γ) → α → NRest α γ :=
  fun D s => if b s then bindT (c s) D else returnT s

@[simp] theorem whileBody_apply [CompleteLattice γ] [AddMonoid γ] (b : α → Bool)
    (c : α → NRest α γ) (D : α → NRest α γ) (s : α) :
    whileBody b c D s = if b s then bindT (c s) D else returnT s := rfl

/-- The source's `whileT`. -/
noncomputable def whileT [CompleteLattice γ] [AddMonoid γ] (b : α → Bool)
    (c : α → NRest α γ) : α → NRest α γ :=
  RECT (whileBody b c)

/-- `whileT` is literally the source's term (substrate decision C3). -/
theorem whileT_def [CompleteLattice γ] [AddMonoid γ] (b : α → Bool) (c : α → NRest α γ) :
    whileT b c = RECT (fun D s => if b s then bindT (c s) D else returnT s) := rfl

/-- The `RECT` side condition for a while body. The `flat_ge` half is
`bindT_flatGe`, the `≤` half is `bindT_mono`; both branches go through
`monotoneRel_ite`. -/
theorem mono2_whileBody [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    (b : α → Bool) (c : α → NRest α γ) : mono2 (whileBody b c) := by
  refine ⟨monotoneRel_funOrd fun _ _ s hfg => ?_, monotone_of_apply fun _ _ s hfg => ?_⟩
  · exact monotoneRel_ite (b s = true) (bindT_flatGe (flatOrd_refl _ _) hfg) (flatOrd_refl _ _)
  · exact monotoneRel_ite (b s = true) (bindT_mono le_rfl hfg) le_rfl

/-- **The source's `whileT_unfold`**, stated once (substrate decision
C2). -/
theorem whileT_unfold [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    (b : α → Bool) (c : α → NRest α γ) :
    whileT b c = fun s => if b s then bindT (c s) (whileT b c) else returnT s :=
  RECT_unfold (mono2_whileBody b c)

/-- `whileT_unfold`, applied. -/
theorem whileT_unfold_apply [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    (b : α → Bool) (c : α → NRest α γ) (s : α) :
    whileT b c s = if b s then bindT (c s) (whileT b c) else returnT s := by
  conv_lhs => rw [whileT_unfold b c]

/-- The source's `whileT_unfold_enat`: the statement at `enat`. -/
theorem whileT_unfold_enat (b : α → Bool) (c : α → NRest α ℕ∞) :
    whileT b c = fun s => if b s then bindT (c s) (whileT b c) else returnT s :=
  whileT_unfold b c

/-- The source's `whileT_unfold_acost`: the statement at `(_, enat) acost`. -/
theorem whileT_unfold_acost (b : α → Bool) (c : α → NRest α (ACost κ ℕ∞)) :
    whileT b c = fun s => if b s then bindT (c s) (whileT b c) else returnT s :=
  whileT_unfold b c

/-- A loop whose condition fails returns its state. -/
@[simp] theorem whileT_of_false [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    {b : α → Bool} (c : α → NRest α γ) {s : α} (h : b s = false) :
    whileT b c s = returnT s := by
  rw [whileT_unfold_apply, h]
  simp

/-- A loop whose condition holds runs one iteration and recurses. -/
@[simp] theorem whileT_of_true [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    {b : α → Bool} (c : α → NRest α γ) {s : α} (h : b s = true) :
    whileT b c s = bindT (c s) (whileT b c) := by
  rw [whileT_unfold_apply, h]
  simp

/-- **The source's `whileT_mono`**, stated once (substrate decision C2):
only the iterations the condition actually reaches have to refine. -/
theorem whileT_mono [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    {b : α → Bool} {c c' : α → NRest α γ} (h : ∀ x, b x = true → c x ≤ c' x) (x : α) :
    whileT b c x ≤ whileT b c' x := by
  refine RECT_mono (mono2_whileBody b c) (fun F y => ?_) x
  simp only [whileBody_apply]
  by_cases hy : b y = true
  · rw [if_pos hy, if_pos hy]
    exact bindT_mono (h y hy) fun _ => le_rfl
  · rw [if_neg hy, if_neg hy]

/-- The source's `whileT_mono_enat`. -/
theorem whileT_mono_enat {b : α → Bool} {c c' : α → NRest α ℕ∞}
    (h : ∀ x, b x = true → c x ≤ c' x) (x : α) : whileT b c x ≤ whileT b c' x :=
  whileT_mono h x

/-- The source's `whileT_mono_fenat`. -/
theorem whileT_mono_fenat {b : α → Bool} {c c' : α → NRest α (ACost κ ℕ∞)}
    (h : ∀ x, b x = true → c x ≤ c' x) (x : α) : whileT b c x ≤ whileT b c' x :=
  whileT_mono h x

/-! ### The annotated variants

The source's `whileIET` is `whileT` with an invariant and an energy
(potential) function attached: the annotations are *definitionally
inert*, carried only so that the VCG can read them off the term. -/

set_option linter.unusedVariables false in
/-- The source's `whileIET I E b c = whileT b c`. `I` is the loop
invariant, `E` the remaining-energy annotation; both are inert, carried
so that the VCG can read them off the term. -/
noncomputable def whileIET [CompleteLattice γ] [AddMonoid γ] (I : α → Prop) (E : α → ε)
    (b : α → Bool) (c : α → NRest α γ) : α → NRest α γ :=
  whileT b c

@[simp] theorem whileIET_eq [CompleteLattice γ] [AddMonoid γ] (I : α → Prop) (E : α → ε)
    (b : α → Bool) (c : α → NRest α γ) : whileIET I E b c = whileT b c := rfl

/-- The body functional shared by `monadic_WHILEIT` and
`monadic_WHILEIT'`: assert the invariant, run the condition
*computation*, and on `true` run one iteration, pay a `''call''` unit,
and recurse. -/
noncomputable def monadicWhileBody [CompleteLattice γ] [AddMonoid γ] [One γ] (I : α → Prop)
    (b : α → NRest Bool (ACost String γ)) (f : α → NRest α (ACost String γ)) :
    (α → NRest α (ACost String γ)) → α → NRest α (ACost String γ) :=
  fun D s =>
    bindT (assert (I s)) fun _ =>
      bindT (b s) fun bv =>
        MIf bv
          (bindT (f s) fun s' => bindT (consumea (ACost.cost "call" 1)) fun _ => D s')
          (returnT s)

@[simp] theorem monadicWhileBody_apply [CompleteLattice γ] [AddMonoid γ] [One γ] (I : α → Prop)
    (b : α → NRest Bool (ACost String γ)) (f : α → NRest α (ACost String γ))
    (D : α → NRest α (ACost String γ)) (s : α) :
    monadicWhileBody I b f D s =
      bindT (assert (I s)) fun _ =>
        bindT (b s) fun bv =>
          MIf bv
            (bindT (f s) fun s' => bindT (consumea (ACost.cost "call" 1)) fun _ => D s')
            (returnT s) := rfl

/-- The source's `monadic_WHILEIT`: one `''call''` unit on entry, then
the recursion. -/
noncomputable def monadicWhileIT [CompleteLattice γ] [AddMonoid γ] [One γ] (I : α → Prop)
    (b : α → NRest Bool (ACost String γ)) (f : α → NRest α (ACost String γ)) (s : α) :
    NRest α (ACost String γ) :=
  bindT (consumea (ACost.cost "call" 1)) fun _ => RECT (monadicWhileBody I b f) s

/-- The source's `monadic_WHILEIT'`: the same recursion without the
entry payment. -/
noncomputable def monadicWhileIT' [CompleteLattice γ] [AddMonoid γ] [One γ] (I : α → Prop)
    (b : α → NRest Bool (ACost String γ)) (f : α → NRest α (ACost String γ)) (s : α) :
    NRest α (ACost String γ) :=
  RECT (monadicWhileBody I b f) s

set_option linter.unusedVariables false in
/-- The source's `monadic_WHILEIET I E b f s ≡ monadic_WHILEIT I b f s`. -/
noncomputable def monadicWhileIET [CompleteLattice γ] [AddMonoid γ] [One γ] (I : α → Prop)
    (E : α → ε) (b : α → NRest Bool (ACost String γ)) (f : α → NRest α (ACost String γ))
    (s : α) : NRest α (ACost String γ) :=
  monadicWhileIT I b f s

@[simp] theorem monadicWhileIET_eq [CompleteLattice γ] [AddMonoid γ] [One γ] (I : α → Prop)
    (E : α → ε) (b : α → NRest Bool (ACost String γ)) (f : α → NRest α (ACost String γ))
    (s : α) : monadicWhileIET I E b f s = monadicWhileIT I b f s := rfl

set_option linter.unusedVariables false in
/-- The source's `monadic_WHILEIET' I E b f s ≡ monadic_WHILEIT' I b f s`. -/
noncomputable def monadicWhileIET' [CompleteLattice γ] [AddMonoid γ] [One γ] (I : α → Prop)
    (E : α → ε) (b : α → NRest Bool (ACost String γ)) (f : α → NRest α (ACost String γ))
    (s : α) : NRest α (ACost String γ) :=
  monadicWhileIT' I b f s

@[simp] theorem monadicWhileIET'_eq [CompleteLattice γ] [AddMonoid γ] [One γ] (I : α → Prop)
    (E : α → ε) (b : α → NRest Bool (ACost String γ)) (f : α → NRest α (ACost String γ))
    (s : α) : monadicWhileIET' I E b f s = monadicWhileIT' I b f s := rfl

/-- **The source's `monadic_WHILEIT_RECT'_conv`.** The explicit
`''call''` payments of `monadic_WHILEIT` are exactly what `RECT'` adds
on its own, so the annotated monadic while *is* a `RECT'` of the plain
loop body. -/
theorem monadicWhileIT_eq_RECT' [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    [One γ] (I : α → Prop) (b : α → NRest Bool (ACost String γ))
    (f : α → NRest α (ACost String γ)) (s : α) :
    monadicWhileIT I b f s =
      RECT' (fun D s =>
        bindT (assert (I s)) fun _ =>
          bindT (b s) fun bv => MIf bv (bindT (f s) fun s' => D s') (returnT s)) s := by
  have hbody :
      (fun D s => (fun D s =>
          bindT (assert (I s)) fun _ =>
            bindT (b s) fun bv => MIf bv (bindT (f s) fun s' => D s') (returnT s))
        (fun y => consume (D y) (ACost.cost "call" 1)) s) = monadicWhileBody I b f := by
    funext D s
    simp only [monadicWhileBody_apply, consume_alt2]
  rw [RECT', hbody, monadicWhileIT, consume_alt2]

/-! ### `FOREACH`

Ported from AFP `NREST`'s `Refine_Foreach.thy` at `ℕ∞`, definitions and
arm/mono lemmas only; see the header for why the cost artifact has no
counterpart and what is deferred. -/

/-- The source's `FOREACH_cond c ≡ (λ(xs,σ). xs ≠ [] ∧ c σ)`. -/
def FOREACH_cond (c : σ → Bool) (p : List α × σ) : Bool := !p.1.isEmpty && c p.2

@[simp] theorem FOREACH_cond_nil (c : σ → Bool) (s : σ) :
    FOREACH_cond c (([] : List α), s) = false := rfl

@[simp] theorem FOREACH_cond_cons (c : σ → Bool) (x : α) (xs : List α) (s : σ) :
    FOREACH_cond c (x :: xs, s) = c s := by simp [FOREACH_cond]

/-- The source's
`FOREACH_body f ≡ λ(xs, σ). do { x ← RETURNT (hd xs); σ' ← f x σ; RETURNT (tl xs, σ') }`.
`List.headI` is HOL's total `hd` (substrate decision C4). -/
noncomputable def FOREACH_body [Inhabited α] (f : α → σ → NRest σ ℕ∞) (p : List α × σ) :
    NRest (List α × σ) ℕ∞ :=
  bindT (returnT p.1.headI) fun x => bindT (f x p.2) fun s' => returnT (p.1.tail, s')

@[simp] theorem FOREACH_body_apply [Inhabited α] (f : α → σ → NRest σ ℕ∞)
    (p : List α × σ) :
    FOREACH_body f p = bindT (f p.1.headI p.2) fun s' => returnT (p.1.tail, s') := by
  rw [FOREACH_body, returnT_bindT]

/-- The body of a `FOREACH` is monotone in the iterated function. -/
theorem FOREACH_body_mono [Inhabited α] {f f' : α → σ → NRest σ ℕ∞}
    (h : ∀ x s, f x s ≤ f' x s) (p : List α × σ) :
    FOREACH_body f p ≤ FOREACH_body f' p := by
  rw [FOREACH_body_apply, FOREACH_body_apply]
  exact bindT_mono (h _ _) fun _ => le_rfl

/-- The source's `FOREACHoci`: iterate `f` over `S` in some `R`-sorted
order, keeping `Φ` invariant, continuing while `c` holds, paying
`inittime` to pick the order and `bodyTime` per element. `emb` is
`spec` (substrate decision C5). -/
noncomputable def FOREACHoci [Inhabited α] (R : α → α → Prop) (Φ : Set α → σ → Prop)
    (S : Set α) (c : σ → Bool) (f : α → σ → NRest σ ℕ∞) (s0 : σ)
    (inittime bodyTime : ℕ∞) : NRest σ ℕ∞ :=
  bindT (assert S.Finite) fun _ =>
    bindT (spec (fun xs : List α => xs.Nodup ∧ S = {x | x ∈ xs} ∧ xs.Pairwise R)
        (fun _ => inittime)) fun xs =>
      bindT
        (whileIET (fun p : List α × σ => ∃ xs', xs = xs' ++ p.1 ∧ Φ {x | x ∈ p.1} p.2)
          (fun p : List α × σ => (p.1.length : ℕ∞) * bodyTime)
          (FOREACH_cond c) (FOREACH_body f) (xs, s0))
        fun p => returnT p.2

/-- The source's `FOREACHci ≡ FOREACHoci (λ_ _. True)`: no order
constraint. -/
noncomputable def FOREACHci [Inhabited α] (Φ : Set α → σ → Prop) (S : Set α) (c : σ → Bool)
    (f : α → σ → NRest σ ℕ∞) (s0 : σ) (inittime bodyTime : ℕ∞) : NRest σ ℕ∞ :=
  FOREACHoci (fun _ _ => True) Φ S c f s0 inittime bodyTime

@[simp] theorem FOREACHci_eq [Inhabited α] (Φ : Set α → σ → Prop) (S : Set α) (c : σ → Bool)
    (f : α → σ → NRest σ ℕ∞) (s0 : σ) (inittime bodyTime : ℕ∞) :
    FOREACHci Φ S c f s0 inittime bodyTime
      = FOREACHoci (fun _ _ => True) Φ S c f s0 inittime bodyTime := rfl

/-- An infinite iteration set makes a `FOREACH` fail: the source's
`ASSERT (finite S)`, read off. -/
@[simp] theorem FOREACHoci_of_infinite [Inhabited α] (R : α → α → Prop) (Φ : Set α → σ → Prop)
    {S : Set α} (hS : ¬ S.Finite) (c : σ → Bool) (f : α → σ → NRest σ ℕ∞) (s0 : σ)
    (inittime bodyTime : ℕ∞) :
    FOREACHoci R Φ S c f s0 inittime bodyTime = fail := by
  rw [FOREACHoci, assert_neg hS, bindT_fail]

end NRest

/-! ### The D4 gate

Substrate decision C7. The loop checked is a countdown on `Fin 3`
paying one time unit per iteration; three approximants stabilise it, so
the theorem `whileT_sample` turns a kernel-computed value into a
statement about `NRest.whileT` itself. The `#test`s then sample loop
bodies. -/

namespace Sanity

open Plausible

/-- The sample loop condition: keep going until `0`. -/
def bSample (s : Fin 3) : Bool := s ≠ 0

/-- The sample loop body: step down, paying one time unit. -/
def cSample (s : Fin 3) : SRest := NRest.consume (returnE (dec s)) 1

/-- The executable twin of `NRest.whileBody`, built from `Sanity.lean`'s
`bindE`/`returnE`. -/
def whileBodyE (b : Fin 3 → Bool) (c : Fin 3 → SRest) (D : Fin 3 → SRest) (s : Fin 3) : SRest :=
  if b s then bindE (c s) D else returnE s

@[simp] theorem whileBodyE_apply (b : Fin 3 → Bool) (c D : Fin 3 → SRest) (s : Fin 3) :
    whileBodyE b c D s = if b s then bindE (c s) D else returnE s := rfl

/-- **The bridge**: the twin is the real body. -/
theorem whileBodyE_eq (b : Fin 3 → Bool) (c : Fin 3 → SRest) :
    whileBodyE b c = NRest.whileBody b c := by
  funext D s
  simp only [whileBodyE_apply, NRest.whileBody_apply, bindE_eq, returnE_eq]

/-- Once the approximants of a loop stop moving, they *are* the loop. -/
theorem whileT_eq_fuelIterE (b : Fin 3 → Bool) (c : Fin 3 → SRest) (n : ℕ)
    (hstab : ∀ s, whileBodyE b c (fuelIterE (whileBodyE b c) n) s
      = fuelIterE (whileBodyE b c) n s) :
    NRest.whileT b c = fuelIterE (whileBodyE b c) n := by
  rw [whileBodyE_eq] at hstab ⊢
  rw [fuelIterE_eq] at hstab ⊢
  exact funext fun s => RECT_eq_of_fuelIter_stable (NRest.mono2_whileBody b c) hstab s

/-- The sample loop, solved. -/
theorem whileT_sample : NRest.whileT bSample cSample = fuelIterE (whileBodyE bSample cSample) 3 :=
  whileT_eq_fuelIterE _ _ 3 (by decide)

-- The loop's value from each starting state: `k` steps cost `k`.
#guard fuelIterE (whileBodyE bSample cSample) 3 0 = returnE 0
#guard fuelIterE (whileBodyE bSample cSample) 3 1 = NRest.rest ![((1 : ℕ∞) : WithBot ℕ∞), ⊥, ⊥]
#guard fuelIterE (whileBodyE bSample cSample) 3 2 = NRest.rest ![((2 : ℕ∞) : WithBot ℕ∞), ⊥, ⊥]

-- Two approximants are not enough from `2`, so the stability test above
-- is not vacuous.
#guard fuelIterE (whileBodyE bSample cSample) 2 2 = (NRest.fail : SRest)
#guard fuelIterE (whileBodyE bSample cSample) 4 = fuelIterE (whileBodyE bSample cSample) 3

/-- The loop's value at `2`, as a statement about `NRest.whileT`. -/
theorem whileT_sample_two :
    NRest.whileT bSample cSample 2 = NRest.rest ![((2 : ℕ∞) : WithBot ℕ∞), ⊥, ⊥] := by
  rw [whileT_sample]
  decide

/-- A loop whose condition never holds returns at once — the source's
`whileT_unfold` in its base case, checked at the sample carrier. -/
theorem whileT_sample_false (c : Fin 3 → SRest) (s : Fin 3) :
    NRest.whileT (fun _ => false) c s = NRest.returnT s :=
  NRest.whileT_of_false c rfl

/-- `MIf` charges the branch overhead on top of the branch: taking the
`true` branch of a `returnT` leaves exactly one `''if''` unit. -/
theorem MIf_true_returnT (x : Fin 3) (n : NRest (Fin 3) ECost) :
    NRest.MIf true (NRest.returnT x) n
      = NRest.rest (NRest.single x ((ACost.cost "if" 1 : ECost) : WithBot ECost)) := by
  rw [NRest.MIf_true, NRest.consume_returnT]

/-- And the `false` branch is charged the same. -/
theorem MIf_false_returnT (x : Fin 3) (m : NRest (Fin 3) ECost) :
    NRest.MIf false m (NRest.returnT x)
      = NRest.rest (NRest.single x ((ACost.cost "if" 1 : ECost) : WithBot ECost)) := by
  rw [NRest.MIf_false, NRest.consume_returnT]

-- The `''if''` currency is the only one `MIf` spends.
#guard (ACost.cost "if" (1 : ℕ∞)).toFun "if" = 1
#guard (ACost.cost "if" (1 : ℕ∞)).toFun "call" = 0

/-! Property checks. The approximants are the same functional the fixed
point is taken of, so a counterexample below is a counterexample to
`mono2_whileBody`, hence to `whileT_mono` / `whileT_unfold`. -/

-- The approximants decrease: `fuelIter` starts at `⊤` and `whileBody`
-- is monotone.
#test ∀ (c₀ c₁ c₂ : SRest) (n : ℕ),
  fuelIterE (whileBodyE bSample ![c₀, c₁, c₂]) 4 (mk3 n)
    ≤ fuelIterE (whileBodyE bSample ![c₀, c₁, c₂]) 3 (mk3 n)

-- `whileT_mono`, guarded form.
#test ∀ (c₀ c₁ c₂ d₀ d₁ d₂ : SRest) (n : ℕ),
  c₀ ≤ d₀ → c₁ ≤ d₁ → c₂ ≤ d₂ →
    fuelIterE (whileBodyE bSample ![c₀, c₁, c₂]) 3 (mk3 n)
      ≤ fuelIterE (whileBodyE bSample ![d₀, d₁, d₂]) 3 (mk3 n)

-- `whileT_mono`, in the hypothesis-free form its premises are always
-- satisfiable in.
#test ∀ (c₀ c₁ c₂ d₀ d₁ d₂ : SRest) (n : ℕ),
  fuelIterE (whileBodyE bSample ![c₀, c₁, c₂]) 3 (mk3 n)
    ≤ fuelIterE (whileBodyE bSample fun s => joinE (![c₀, c₁, c₂] s) (![d₀, d₁, d₂] s)) 3 (mk3 n)

-- The chain decreases at *every* fuel level, not just at one: this is
-- the whole content of `mono2_whileBody`'s `≤` half.
#test ∀ (c₀ c₁ c₂ : SRest) (n k : ℕ),
  fuelIterE (whileBodyE bSample ![c₀, c₁, c₂]) (k % 5 + 1) (mk3 n)
    ≤ fuelIterE (whileBodyE bSample ![c₀, c₁, c₂]) (k % 5) (mk3 n)

-- Refuted while this gate was written, and worth keeping: a loop whose
-- body has *no results at all* (`SUCCEEDT`) does not fail — the bind
-- has nothing to charge, so the loop is `SUCCEEDT` too. The plausible
-- guess "a non-terminating loop is `FAILT`" is only true of bodies that
-- actually produce results.
#guard fuelIterE (whileBodyE (fun _ => true) fun _ => NRest.rest fun _ => (⊥ : WithBot ℕ∞)) 1 0
  = NRest.rest fun _ => (⊥ : WithBot ℕ∞)

end Sanity

end Lax13Proofs.Refine
