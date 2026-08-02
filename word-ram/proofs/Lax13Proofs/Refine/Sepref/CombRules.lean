import Lax13Proofs.Refine.Sepref.IrOps

/-!
The derived control-flow rules: `hnr_If` and the loop rule.

**Provenance: these two are OURS, derived.** The cost-carrying artifact
(`isabelle_llvm_time` @ `42dd7f5`, the pin of `Basic.lean`'s header) has
**no** `If`/`While` `hn_refine` rule under any name — a repo-wide grep of
its `thys/sepref/*.thy` found none, and its examples route control flow
through `hn_RECT'` instead (design record §3, P4 row, "Source gap found
by the P2–P4 deep read"; `p4-sepref-extracts.md`, Gaps). The *shapes* are
therefore taken from the no-cost AFP twin `Refine_Imperative_HOL`
(`Sepref_Basic.thy`'s `hnr_If`, `Sepref_Translate.thy`'s
`hn_monadic_WHILE_lin`, both quoted in `p4-sepref-extracts.md` §2) and
the cost-carrying versions are *derived* from wave A's `hnRefine`,
`hnr_seq` and the MERGE calculus. Each premise below carries its
correspondence: **AFP premise ↦ our premise ↦ delta**.

## Judgment calls (continuing `IrOps.lean`'s P4/D-aa … P4/D-ae)

**P4/D-af — the guard is a *fused* judgment `CondRefine`, not an
`hn_refine` at `pure bool_rel`.** The AFP rules synthesize the guard as a
*program*: `hnr_If`'s `P ⟹⇩t Γ1 * hn_val bool_rel a a'` says the boolean
lives in a concrete location `a'`, and `hn_monadic_WHILE_lin`'s `b_ref`
premise is a whole `hn_refine … (b s) … (pure bool_rel) (b' s')`
synthesizing a bool-valued program. Our IR has **no boolean cell and no
boolean-valued op** (design record §6: conditions are structural
`Ir.Cond` over cells and literals, evaluated *inside* the `ite`/`while`
op's own charge). So the guard premise is
`CondRefine Γ cond b : ∀ F s cr, irSTATE (Γ ∗ F) (s, cr) → cond.eval s = some b`
— "under the ownership `Γ`, the structural condition evaluates to the
abstract program's branch value". This is substrate-forced, and it is
*cheaper* than the source's, not weaker: there is no separate program to
synthesize, no `Γb` to frame back (`b_fr` disappears), and no cost, since
the IR pays for guard evaluation inside `ir.ite` / `ir.while`. `Γ` here
is the *whole* precondition, which is why `CondRefine` needs
`CondRefine.frame` rather than a weakening: our separation logic is
precise (`A ∗ B ⊬ A`), so a condition rule is extended to a larger
context by *framing*, never by dropping conjuncts.

**P4/D-ag — `hnr_If`'s join is wave A's entailment-form MERGE.** The AFP
rule's `Γ2b ∨⇩A Γ2c ⟹⇩t Γ'` is a disjunction-entailment discharged by
`Sepref_Frame.thy`'s `merge_tac`; wave A ported that calculus as
`MERGE Γ₁ Γ₂ Γ' := (Γ₁ ⊢ Γ') ∧ (Γ₂ ⊢ Γ')` (P4/D-e), which is exactly
`Γ₁ ∨⇩A Γ₂ ⊢ Γ'` unfolded. So `MRG : MERGE Γt Γe Γ'` *is* the source's
`IMP`, and `MERGE1_invalids_left/right` at `deadAssn` are what let the
branches disagree about a live temporary.

**P4/D-ah — the loop's state lives in fixed cells, so the post is `Γ`.**
The AFP loop rule ends at `Γ * hn_invalid Rs s' s`: the loop's abstract
result is a *fresh value* whose concrete twin invalidates the entry
state's ownership. Ours cannot: the loop state occupies the *same* cells
`d` across every iteration (three-address code, no SSA), so the result is
delivered where every `hnRefine` delivers a result — in the judgment's
own result slot `R ra d` — and what remains of the post is the loop frame
`Γ`. The premise roles are otherwise the AFP rule's one for one; the
`INDEP Rs` and `TERM (monadic_WHILEIT, ''cond''/''body'')` premises are
tactic bookkeeping (they name which frame side condition failed, for
debugging) and are omitted, per the AFP rule's own comment — they are
wave C's business, not the logic's.

**P4/D-ai — the loop rule is *measured*, and that is the landed form.**
**(CLOSED by R0/D-b, §4b — the named blocker is refuted, not filled: the
unfueled rule `hnr_while` is the database entry now, and the measured
rule below is deregistered capital. The entry is kept verbatim because
its blocker analysis is exactly what R0/D-b corrects.)**
`hnr_while_measured` takes a variant `V : σ → ℕ` that decreases on every
state the body can produce. The unfueled general rule — where termination
comes from the abstract loop's own `nofailT` — is **backlog**, and the
blocker is precise: `RECT` is P1's `gfp` (`Rec.lean`), so an abstract
loop that diverges *is* `FAILT` and `nofailT` really does carry the
termination information, but turning it into an induction needs a P1
lemma that does not exist —
`nofailT (RECT B s) → ∃ n, fuelIter B n s = RECT B s`, or an
accessibility predicate for the body. `Rec.lean` has only
`RECT_le_fuelIter` and `RECT_eq_of_fuelIter_stable`, neither of which
gives it. The measured rule suffices for every loop the acceptance
programs contain (all have counter variants), and the general rule is a
strictly weaker premise on the same conclusion, so nothing proved with
the measured rule has to change when it lands. Note what the measured
rule does *not* need: no `INV` premise. The invariant is read off the
abstract program's non-failure (`irWhileIT` asserts `I s`, P4/D-ad), so
`I s` is available in the induction step for free and a state where the
invariant fails makes the abstract side `fail`, hence the judgment
vacuous — pinned in the gate.

**P4/D-aj — the two arithmetic helpers are named.** `afford_pay` /
`minus_pay` (and their zero-`Ca` forms) are the whole cost content of
both rules: paying an op's price out of a balance the abstract side just
topped up. They are `Wp.lean`'s `leCostECost_cash_add` /
`minusECost_cash_add` with one `add_left_comm`, isolated so that neither
rule's proof does arithmetic inline.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 0. Registering wave A's rules

`Sepref/Basic.lean` sits *upstream* of `Sepref/Attrs.lean` (an attribute
is unavailable to its own defining module, and `Basic.lean` predates the
declaration), so its two database members are registered here, at the
first point downstream of both. The database assignment is the source's:
`hn_bind` is a `sepref_comb_rules` entry and `hn_pass` a
`sepref_fr_rules` one (`p4-sepref-extracts.md` §2). -/

attribute [sepref_comb_rules] hnr_seq
attribute [sepref_fr_rules] hnr_return_pass

/-! ## 1. The cost bookkeeping (P4/D-aj) -/

/-- `cash` of a one-unit run cost is the one-unit balance cost: the
`ℕ`-versus-`ℕ∞` seam, closed once. -/
theorem cash_irUnit (n : String) : cash (ACost.cost n 1) = irUnit n := by
  rw [cash_cost]
  norm_num

/-- The balance an abstract top-up of `cash κc + Ca` leaves affords `κc`. -/
theorem afford_pay (κc : Cost) (cr Ca : ECost) : leCostECost κc (cr + (cash κc + Ca)) := by
  rw [add_left_comm]
  exact leCostECost_cash_add _ _

/-- …and paying it leaves exactly `cr + Ca`. -/
theorem minus_pay (κc : Cost) (cr Ca : ECost) :
    minusECost (cr + (cash κc + Ca)) κc = cr + Ca := by
  rw [add_left_comm, minusECost_cash_add]

/-- The `Ca = 0` forms, for the rules that pay only the op's own price. -/
theorem afford_pay' (κc : Cost) (cr : ECost) : leCostECost κc (cr + cash κc) := by
  rw [add_comm]
  exact leCostECost_cash_add _ _

theorem minus_pay' (κc : Cost) (cr : ECost) : minusECost (cr + cash κc) κc = cr := by
  rw [add_comm, minusECost_cash_add]

/-! ## 2. `CondRefine` (P4/D-af)

The fused guard judgment: the IR's structural condition evaluates, under
the ownership the rule holds, to the abstract program's branch value. -/

/-- The guard premise of both control-flow rules (P4/D-af). -/
def CondRefine (Γ : Assn) (cond : Cond) (b : Bool) : Prop :=
  ∀ (F : Assn) (s : State) (cr : ECost), irSTATE (Γ ∗ F) (s, cr) → cond.eval s = some b

/-- Strengthening the context: anything entailing a context that
determines the guard determines it too. (Weakening is *not* available —
the logic is precise; use `CondRefine.frame`.) -/
theorem CondRefine.cons {Γ Γ' : Assn} {cond : Cond} {b : Bool} (hent : Γ ⊢ Γ')
    (h : CondRefine Γ' cond b) : CondRefine Γ cond b :=
  fun F s cr hs => h F s cr (start_entailsE hs (sepConj_mono_left hent))

/-- **Frame monotonicity**: a guard rule applies under any larger
context. -/
theorem CondRefine.frame {Γ Δ : Assn} {cond : Cond} {b : Bool} (h : CondRefine Γ cond b) :
    CondRefine (Γ ∗ Δ) cond b := by
  intro F s cr hs
  rw [sepConj_assoc] at hs
  exact h (Δ ∗ F) s cr hs

/-- …on the left as well. -/
theorem CondRefine.frame_left {Γ Δ : Assn} {cond : Cond} {b : Bool} (h : CondRefine Γ cond b) :
    CondRefine (Δ ∗ Γ) cond b := by
  rw [sepConj_comm]
  exact h.frame

/-! ### The four shapes

`.lt` and `.eq` over two cells, and over a cell and a literal either way
round. Each is `ptoVar_vars` and `Cond.eval`'s own equation. -/

theorem condRefine_lt_cells (m n : ℕ) (y z : String) :
    CondRefine (hnCtxt natAssn m y ∗ hnCtxt natAssn n z) (.lt (.cell y) (.cell z))
      (decide (m < n)) := by
  intro F s cr hs
  simp only [hnCtxt_def, natAssn_def] at hs
  rw [sepConj_assoc] at hs
  have hy : s.vars y = some m := ptoVar_vars hs
  have hz : s.vars z = some n := ptoVar_vars (irSTATE_rot hs)
  simp [hy, hz]

theorem condRefine_eq_cells (m n : ℕ) (y z : String) :
    CondRefine (hnCtxt natAssn m y ∗ hnCtxt natAssn n z) (.eq (.cell y) (.cell z))
      (decide (m = n)) := by
  intro F s cr hs
  simp only [hnCtxt_def, natAssn_def] at hs
  rw [sepConj_assoc] at hs
  have hy : s.vars y = some m := ptoVar_vars hs
  have hz : s.vars z = some n := ptoVar_vars (irSTATE_rot hs)
  simp [hy, hz]
  rfl

theorem condRefine_lt_cell_lit (m : ℕ) (y : String) (c : ℕ) :
    CondRefine (hnCtxt natAssn m y) (.lt (.cell y) (.lit c)) (decide (m < c)) := by
  intro F s cr hs
  simp only [hnCtxt_def, natAssn_def] at hs
  simp [ptoVar_vars hs]

theorem condRefine_lt_lit_cell (c n : ℕ) (z : String) :
    CondRefine (hnCtxt natAssn n z) (.lt (.lit c) (.cell z)) (decide (c < n)) := by
  intro F s cr hs
  simp only [hnCtxt_def, natAssn_def] at hs
  simp [ptoVar_vars hs]

theorem condRefine_eq_cell_lit (m : ℕ) (y : String) (c : ℕ) :
    CondRefine (hnCtxt natAssn m y) (.eq (.cell y) (.lit c)) (decide (m = c)) := by
  intro F s cr hs
  simp only [hnCtxt_def, natAssn_def] at hs
  simp [ptoVar_vars hs]
  rfl

theorem condRefine_eq_lit_cell (c n : ℕ) (z : String) :
    CondRefine (hnCtxt natAssn n z) (.eq (.lit c) (.cell z)) (decide (c = n)) := by
  intro F s cr hs
  simp only [hnCtxt_def, natAssn_def] at hs
  simp [ptoVar_vars hs]
  rfl

/-! ## 3. `hnr_If` (P4/D-af, P4/D-ag)

Clause by clause against the AFP rule
(`Refine_Imperative_HOL/Sepref_Basic.thy`, `p4-sepref-extracts.md` §2):

| AFP premise | ours | delta |
|---|---|---|
| `P ⟹⇩t Γ1 * hn_val bool_rel a a'` | `COND : CondRefine Γ cond b` | P4/D-af: no bool cell; the condition is structural and its evaluation is inside the `ite` op's charge, so the guard is a *fact about `Γ`*, not a split of it. `Γ1` disappears with it. |
| `a ⟹ hn_refine (Γ1 * hn_val …) b' Γ2b R b` | `RT : b = true → hnRefine Γ ct Γt d R t` | the branch judgment, unchanged; the precondition is `Γ` because there is no boolean conjunct to carry |
| `¬a ⟹ … Γ2c … c` | `RE : b = false → hnRefine Γ ce Γe d R e` | as above |
| `Γ2b ∨⇩A Γ2c ⟹⇩t Γ'` | `MRG : MERGE Γt Γe Γ'` | P4/D-ag: wave A's entailment-form MERGE *is* that disjunction-entailment |
| conclusion `hn_refine Γ (if a' then b' else c') Γ' R (if a then b else c)` | `hnRefine Γ (.ite cond ct ce) Γ' d R (irIf b t e)` | the abstract side is `MIf`'s ir-currency form (`irIf`, P4/D-ad), which *pays* `ir.ite`; the AFP rule's `if` is cost-free because its monad is |

The cost step is one balance lemma: `irIf` hands over `ir.ite` on top of
the branch's own cost, and `wp_ite` spends exactly that before running the
branch. -/

@[sepref_comb_rules]
theorem hnr_If {α κ : Type} {Γ Γt Γe Γ' : Assn} {cond : Cond} {b : Bool} {ct ce : Com}
    {d : κ} {R : α → κ → Assn} {t e : NRest α ECost}
    (COND : CondRefine Γ cond b)
    (RT : b = true → hnRefine Γ ct Γt d R t)
    (RE : b = false → hnRefine Γ ce Γe d R e)
    (MRG : MERGE Γt Γe Γ') :
    hnRefine Γ (.ite cond ct ce) Γ' d R (irIf b t e) := by
  -- the branch, uniformly in `b`
  have hbr : hnRefine Γ (if b then ct else ce) (if b then Γt else Γe) d R
      (if b then t else e) := by
    cases b
    · simpa using RE rfl
    · simpa using RT rfl
  have hent : (if b then Γt else Γe) ⊢ Γ' := by
    cases b
    · simpa using MRG.2
    · simpa using MRG.1
  intro hnf M F s cr hm hst
  rw [irIf_def] at hm hnf
  have hnfb : (if b then t else e).nofailT := nofailT_consume_iff.1 hnf
  cases hmb : (if b then t else e) with
  | fail => exact absurd hmb (NRest.nofailT_iff.1 hnfb)
  | rest Mb =>
    obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD hbr hmb hst
    have hM : M = fun x => WithBot.map (irUnit Currency.ite + ·) (Mb x) := by
      rw [hmb, NRest.consume_rest] at hm
      exact (NRest.rest_inj_iff.1 hm).symm
    refine ⟨ra, irUnit Currency.ite + Ca, ?_, ?_⟩
    · rw [hM]
      have hmono := withBot_map_mono (f := (irUnit Currency.ite + ·))
        (fun _ _ hab => add_le_add (le_refl _) hab) hCa
      simpa using hmono
    · rw [← cash_irUnit, wp_ite]
      refine ⟨b, COND F s cr hst, afford_pay _ _ _, ?_⟩
      rw [minus_pay]
      refine wp_mono_ir (fun _ p hp => ?_) w
      exact conj_entails_mono hent (entails_refl _) _ hp

/-! ## 4. The loop rule (P4/D-ah, P4/D-ai)

Clause by clause against the AFP rule
(`Refine_Imperative_HOL/Sepref_Translate.thy`'s `hn_monadic_WHILE_lin`,
`p4-sepref-extracts.md` §2):

| AFP premise | ours | delta |
|---|---|---|
| `INDEP Rs` | — | tactic bookkeeping (P4/D-ah) |
| `FR : P ⟹⇩t Γ * hn_ctxt Rs s' s` | — | our conclusion is *stated* at `hnCtxt Rs s₀ d ∗ Γ`; the entry weakening is `hnRefine_cons_pre`, which the caller applies |
| `b_ref : I s' ⟹ hn_refine (Γ * hn_ctxt Rs s' s) (b s) (Γb s' s) (pure bool_rel) (b' s')` | `COND : ∀ s, I s → CondRefine (hnCtxt Rs s d ∗ Γ) cond (bf s)` | P4/D-af: the guard is structural, so the whole synthesized bool program collapses to a fact |
| `b_fr : … Γb s' s ⟹⇩t Γ * hn_ctxt Rs s' s` | — | nothing to frame back: `CondRefine` consumes nothing |
| `f_ref : I s' ⟹ hn_refine (Γ * hn_ctxt Rs s' s) (f s) (Γf s' s) Rs (f' s')` | `BODY : ∀ s, I s → bf s = true → hnRefine (hnCtxt Rs s d ∗ Γ) cbody Γ d Rs (f s)` | the body judgment. Two deltas: the post is `Γ` (P4/D-ah — the body's *result* is the new loop state, delivered in the result slot at the same cells `d`), and the guard hypothesis `bf s = true` is added, because the body only runs then (the AFP rule gets this from `b_ref`'s synthesized program) |
| `f_fr : … Γf s' s ⟹⇩t Γ * hn_ctxt (λ_ _. true) s' s` | — | subsumed: `BODY`'s post *is* `Γ` |
| — | `VAR : ∀ s s', I s → bf s = true → returnT s' ≤ f s → V s' < V s` | **added** (P4/D-ai): the variant. The AFP rule needs none because `heap_WHILET`'s partial correctness is a fixpoint statement; ours is a total-correctness `wp` over a deep `while`, so termination has to come from somewhere, and until P1 exports the `nofailT`-to-well-foundedness lemma it comes from `V` |
| conclusion `hn_refine P (heap_WHILET b f s) (Γ * hn_invalid Rs s' s) Rs (monadic_WHILEIT I b' f' s')` | `hnRefine (hnCtxt Rs s₀ d ∗ Γ) (.while cond cbody) Γ d Rs (irWhileIT I bf f s₀)` | P4/D-ah for the post; `irWhileIT` for the abstract side (P4/D-ad) |

The proof is one induction on `V`, and inside it the *whole* iteration
step is `hnr_seq` — body then loop — which is what makes the cost
accounting come out: `hnr_seq` threads the two payments, and the
`ir.while` unit of this iteration's guard is prepaid in front of it by the
same `afford_pay` / `minus_pay` pair `hnr_If` uses. -/

/-- The measured rule. **Not** a `sepref_comb_rules` entry any more
(R0/D-b): `hnr_while` below proves the same conclusion from strictly
fewer premises, and a database entry that is tried and fails costs a
whole body translation (P7/D-bf). It stays compiled — it is the shorter
route when a variant is already at hand, and the acceptance files name
it. -/
theorem hnr_while_measured {σ κs : Type} {I : σ → Prop} {bf : σ → Bool}
    {f : σ → NRest σ ECost} {Rs : σ → κs → Assn} {Γ : Assn} {d : κs} {cond : Cond}
    {cbody : Com} (V : σ → ℕ)
    (COND : ∀ s, I s → CondRefine (hnCtxt Rs s d ∗ Γ) cond (bf s))
    (BODY : ∀ s, I s → bf s = true → hnRefine (hnCtxt Rs s d ∗ Γ) cbody Γ d Rs (f s))
    (VAR : ∀ s s', I s → bf s = true → (NRest.returnT s' : NRest σ ECost) ≤ f s → V s' < V s)
    (s₀ : σ) :
    hnRefine (hnCtxt Rs s₀ d ∗ Γ) (.while cond cbody) Γ d Rs (irWhileIT I bf f s₀) := by
  suffices H : ∀ n s, V s < n →
      hnRefine (hnCtxt Rs s d ∗ Γ) (.while cond cbody) Γ d Rs (irWhileIT I bf f s) from
    H (V s₀ + 1) s₀ (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun s hs => absurd hs (Nat.not_lt_zero _)
  | succ n ih =>
    intro s hsn hnf M F st cr hm hst
    rw [NRest.nofailT_iff] at hnf
    -- the invariant is *read off* non-failure (P4/D-ai)
    have hI : I s := by
      by_contra hcon
      exact hnf (irWhileIT_of_not_inv hcon)
    cases hb : bf s with
    | false =>
      -- the exit: pay this guard evaluation, hand back the loop state
      rw [irWhileIT_of_false hI hb, NRest.consume_returnT] at hm
      have hM : M = NRest.single s ((irUnit Currency.«while» : ECost) : WithBot ECost) :=
        (NRest.rest_inj_iff.1 hm).symm
      refine ⟨s, irUnit Currency.«while», ?_, ?_⟩
      · rw [hM, NRest.single_self]
      · rw [← cash_irUnit, wp_while_unfold]
        refine ⟨false, ?_, afford_pay' _ _, ?_⟩
        · rw [← hb]; exact COND s hI F st cr hst
        · rw [if_neg (by simp), minus_pay']
          refine start_entailsE hst ?_
          intro h hh
          have h2 : (((hnCtxt Rs s d ∗ Γ) ∗ F) ∗ GC) h := entails_gc_right _ h hh
          have e : (((hnCtxt Rs s d ∗ Γ) ∗ F) ∗ GC) = (Γ ∗ Rs s d ∗ F ∗ GC) := by
            simp only [hnCtxt_def]; ac_rfl
          rwa [e] at h2
    | true =>
      -- one iteration: body, then the loop again — exactly `hnr_seq`
      rw [irWhileIT_of_true hI hb] at hm
      have hseq : hnRefine (hnCtxt Rs s d ∗ Γ) (.seq cbody (.while cond cbody)) Γ d Rs
          (NRest.bindT (f s) fun s' => irWhileIT I bf f s') :=
        hnr_seq (BODY s hI hb) fun a ha =>
          ih a (Nat.lt_of_lt_of_le (VAR s a hI hb ha) (Nat.lt_succ_iff.1 hsn))
      cases hX : NRest.bindT (f s) (fun s' => irWhileIT I bf f s') with
      | fail =>
        rw [hX, NRest.consume_fail] at hm
        exact absurd hm (NRest.fail_ne_rest M)
      | rest MX =>
        rw [hX, NRest.consume_rest] at hm
        obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD hseq hX hst
        refine ⟨ra, irUnit Currency.«while» + Ca, ?_, ?_⟩
        · rw [show M = fun x => WithBot.map (irUnit Currency.«while» + ·) (MX x) from
            (NRest.rest_inj_iff.1 hm).symm]
          have hmono := withBot_map_mono (f := (irUnit Currency.«while» + ·))
            (fun _ _ hab => add_le_add (le_refl _) hab) hCa
          simpa using hmono
        · rw [← cash_irUnit, wp_while_unfold]
          refine ⟨true, ?_, afford_pay _ _ _, ?_⟩
          · rw [← hb]; exact COND s hI F st cr hst
          · rw [if_pos rfl, minus_pay, ← wp_seq]
            exact w

/-! ## 4b. The *unfueled* loop rule (ND-MC rebase P0.3, ledger R0/D-b)

P4/D-ai above left the general rule in backlog and named its blocker as
one missing P1 lemma, `nofailT (RECT B s) → ∃ n, fuelIter B n s = RECT B s`.
`NREST/Rec.lean`'s S7 **refutes** that lemma (`NoFuelBound.no_fuel_bound`:
a `mono2` body whose `RECT` does not fail and which no fuel reaches),
so the blocker is not a gap to be filled — the shape was wrong. ℕ-fuel
counts *iterations of the whole state space*, and a body with unbounded
nondeterminism terminates on every branch without any uniform bound.

**R0/D-b — termination is accessibility, not a number.** `LoopTerm` is
the inductive "every run from here reaches an exit": the exit states are
accessible, and a state is accessible when the guard holds and *every*
successor the body can produce is. It is well-founded without being
finitely branching, which is exactly the room the counterexample needs,
and it is a predicate over the *abstract program alone* — no proof idea,
nothing for the caller to invent.

`loopTerm_of_nofailT` is what makes it disappear from the interface: the
loop's own non-failure, which the `hnRefine` judgment hands over for
free, *is* accessibility. The proof is `Rec.lean`'s new
`RECT_eq_top_of_postfixed`, at the post-fixed point that marks the
inaccessible states with `⊤`: a state that is stuck sends the body to
`FAILT`, either because its invariant fails, or because a successor of
its is stuck too, and `bindT` propagates a failing continuation.

So `hnr_while` is `hnr_while_measured` with the `VAR` premise deleted
and nothing put in its place. The measured rule stays compiled (landed
capital, and the shorter proof when a variant is at hand), but leaves
the `sepref_comb_rules` database: everything it can synthesize,
`hnr_while` synthesizes with one premise fewer, and a database entry
that is tried and fails costs a whole body translation (P7/D-bf). -/

/-- **The loop terminates here.** Accessibility for the abstract loop:
the guard is false, or the guard is true and every successor the body
can produce terminates. -/
inductive LoopTerm {σ : Type} (bf : σ → Bool) (f : σ → NRest σ ECost) : σ → Prop
  | exit {s : σ} (hb : bf s = false) : LoopTerm bf f s
  | step {s : σ} (hb : bf s = true)
      (h : ∀ s', (NRest.returnT s' : NRest σ ECost) ≤ f s → LoopTerm bf f s') :
      LoopTerm bf f s

/-- The stuck states send the loop's body functional to `FAILT`: this is
the post-fixed point `RECT_eq_top_of_postfixed` is applied to. -/
theorem irWhileBody_top_of_not_loopTerm {σ : Type} {I : σ → Prop} {bf : σ → Bool}
    {f : σ → NRest σ ECost} (w : σ → NRest σ ECost)
    (hw : ∀ y, ¬ LoopTerm bf f y → w y = ⊤) {s : σ} (hs : ¬ LoopTerm bf f s) :
    irWhileBody I bf f (fun z => NRest.consume (w z) (irUnit Currency.«while»)) s = ⊤ := by
  rw [irWhileBody_apply]
  by_cases hI : I s
  · rw [NRest.assert_pos hI, NRest.returnT_bindT]
    cases hb : bf s with
    | false => exact absurd (LoopTerm.exit hb) hs
    | true =>
      obtain ⟨s', hle, hs'⟩ : ∃ s', (NRest.returnT s' : NRest σ ECost) ≤ f s ∧
          ¬ LoopTerm bf f s' := by
        by_contra hcon
        refine hs (LoopTerm.step hb fun s' hle => ?_)
        by_contra hns'
        exact hcon ⟨s', hle, hns'⟩
      rw [if_pos rfl]
      refine top_le_iff.mp (le_trans (le_of_eq ?_)
        (NRest.bindT_mono hle (fun _ => le_rfl) (f := fun z =>
          NRest.consume (w z) (irUnit Currency.«while»))))
      rw [NRest.returnT_bindT, hw s' hs', NRest.top_eq_fail, NRest.consume_fail]
  · rw [NRest.assert_neg hI, NRest.bindT_fail, NRest.top_eq_fail]

/-- **Non-failure *is* termination (R0/D-b).** A loop that does not fail
at `s` is accessible at `s`; contrapositively, a stuck state is `FAILT`,
which is the total-correctness reading of `RECT` (`Rec.lean` S2). -/
theorem loopTerm_of_nofailT {σ : Type} {I : σ → Prop} {bf : σ → Bool}
    {f : σ → NRest σ ECost} {s : σ} (hnf : (irWhileIT I bf f s).nofailT) :
    LoopTerm bf f s := by
  classical
  by_contra hs
  refine hnf ?_
  have hG : mono2 (fun D y => irWhileBody I bf f
      (fun z => NRest.consume (D z) (irUnit Currency.«while»)) y) :=
    mono2_consume_call (mono2_irWhileBody I bf f) (irUnit Currency.«while»)
  set G := fun (D : σ → NRest σ ECost) (y : σ) => irWhileBody I bf f
    (fun z => NRest.consume (D z) (irUnit Currency.«while»)) y with hGdef
  set w : σ → NRest σ ECost := fun y => if LoopTerm bf f y then RECT G y else ⊤ with hwdef
  have hRw : ∀ y, RECT G y ≤ w y := by
    intro y
    by_cases hy : LoopTerm bf f y
    · rw [hwdef]; simp only [if_pos hy]; exact le_rfl
    · rw [hwdef]; simp only [if_neg hy]; exact le_top
  have hw : ∀ y, ¬ LoopTerm bf f y → w y = ⊤ := by
    intro y hy; rw [hwdef]; simp only [if_neg hy]
  have hpost : ∀ y, w y ≤ G w y := by
    intro y
    by_cases hy : LoopTerm bf f y
    · rw [hwdef]
      simp only [if_pos hy]
      conv_lhs => rw [RECT_unfold_apply hG]
      exact hG.monotone (fun z => hRw z) y
    · rw [hw y hy, hGdef]
      exact le_of_eq (irWhileBody_top_of_not_loopTerm w hw hy).symm
  have htop : RECT G s = ⊤ := RECT_eq_top_of_postfixed hG hpost (hw s hs)
  show irWhileIT I bf f s = ⊤
  rw [irWhileIT, htop, NRest.top_eq_fail, NRest.consume_fail]

/-- **The loop rule, unfueled (R0/D-b).** `hnr_while_measured` without
the variant: the abstract loop's own non-failure — which `hnRefine`
supplies — is the induction. Same conclusion, one premise fewer, and
nothing for the caller to annotate. -/
@[sepref_comb_rules]
theorem hnr_while {σ κs : Type} {I : σ → Prop} {bf : σ → Bool}
    {f : σ → NRest σ ECost} {Rs : σ → κs → Assn} {Γ : Assn} {d : κs} {cond : Cond}
    {cbody : Com}
    (COND : ∀ s, I s → CondRefine (hnCtxt Rs s d ∗ Γ) cond (bf s))
    (BODY : ∀ s, I s → bf s = true → hnRefine (hnCtxt Rs s d ∗ Γ) cbody Γ d Rs (f s))
    (s₀ : σ) :
    hnRefine (hnCtxt Rs s₀ d ∗ Γ) (.while cond cbody) Γ d Rs (irWhileIT I bf f s₀) := by
  refine hnRefine_nofailI fun hnf₀ => ?_
  have hterm : LoopTerm bf f s₀ := loopTerm_of_nofailT hnf₀
  clear hnf₀
  induction hterm with
  | @exit s hb =>
    intro hnf M F st cr hm hst
    rw [NRest.nofailT_iff] at hnf
    have hI : I s := by
      by_contra hcon
      exact hnf (irWhileIT_of_not_inv hcon)
    -- the exit: pay this guard evaluation, hand back the loop state
    rw [irWhileIT_of_false hI hb, NRest.consume_returnT] at hm
    have hM : M = NRest.single s ((irUnit Currency.«while» : ECost) : WithBot ECost) :=
      (NRest.rest_inj_iff.1 hm).symm
    refine ⟨s, irUnit Currency.«while», ?_, ?_⟩
    · rw [hM, NRest.single_self]
    · rw [← cash_irUnit, wp_while_unfold]
      refine ⟨false, ?_, afford_pay' _ _, ?_⟩
      · rw [← hb]; exact COND s hI F st cr hst
      · rw [if_neg (by simp), minus_pay']
        refine start_entailsE hst ?_
        intro h hh
        have h2 : (((hnCtxt Rs s d ∗ Γ) ∗ F) ∗ GC) h := entails_gc_right _ h hh
        have e : (((hnCtxt Rs s d ∗ Γ) ∗ F) ∗ GC) = (Γ ∗ Rs s d ∗ F ∗ GC) := by
          simp only [hnCtxt_def]; ac_rfl
        rwa [e] at h2
  | @step s hb _ ih =>
    intro hnf M F st cr hm hst
    rw [NRest.nofailT_iff] at hnf
    have hI : I s := by
      by_contra hcon
      exact hnf (irWhileIT_of_not_inv hcon)
    -- one iteration: body, then the loop again — exactly `hnr_seq`
    rw [irWhileIT_of_true hI hb] at hm
    have hseq : hnRefine (hnCtxt Rs s d ∗ Γ) (.seq cbody (.while cond cbody)) Γ d Rs
        (NRest.bindT (f s) fun s' => irWhileIT I bf f s') :=
      hnr_seq (BODY s hI hb) fun a ha => ih a ha
    cases hX : NRest.bindT (f s) (fun s' => irWhileIT I bf f s') with
    | fail =>
      rw [hX, NRest.consume_fail] at hm
      exact absurd hm (NRest.fail_ne_rest M)
    | rest MX =>
      rw [hX, NRest.consume_rest] at hm
      obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD hseq hX hst
      refine ⟨ra, irUnit Currency.«while» + Ca, ?_, ?_⟩
      · rw [show M = fun x => WithBot.map (irUnit Currency.«while» + ·) (MX x) from
          (NRest.rest_inj_iff.1 hm).symm]
        have hmono := withBot_map_mono (f := (irUnit Currency.«while» + ·))
          (fun _ _ hab => add_le_add (le_refl _) hab) hCa
        simpa using hmono
      · rw [← cash_irUnit, wp_while_unfold]
        refine ⟨true, ?_, afford_pay _ _ _, ?_⟩
        · rw [← hb]; exact COND s hI F st cr hst
        · rw [if_pos rfl, minus_pay, ← wp_seq]
          exact w

/-! ## 5. Gate (ledger D4, refute-before-prove)

Two end-to-end instances — a two-branch program and a three-iteration
counter loop — each driven from its `hnRefine` down to a `BigStep` whose
cost vector is pinned by kernel computation; then three negative
controls, of which the third pins the *vacuity* that a failing invariant
produces, rather than leaving it implicit. -/

namespace Gate

/-! ### `hnr_If`, end to end

`if 3 < n then x := 1 else x := 2`, at `n = 5`. -/

def ifCondT : Cond := .lt (.lit 3) (.cell "n")

def ifProg : Com := .ite ifCondT (.const "x" 1) (.const "x" 2)

def ifPre : Assn := junkCell "x" ∗ hnCtxt natAssn 5 "n"

def ifPost : Assn := (□ : Assn) ∗ hnCtxt natAssn 5 "n"

/-- The guard: the literal-versus-cell shape, framed by the destination's
junk cell. -/
theorem if_cond : CondRefine ifPre ifCondT true := by
  have h : CondRefine (junkCell "x" ∗ hnCtxt natAssn 5 "n") ifCondT (decide (3 < 5)) :=
    (condRefine_lt_lit_cell 3 5 "n").frame_left
  rw [show decide (3 < 5) = true from by decide] at h
  exact h

/-- The rule, applied: both branches write the destination, so the merge
is trivial. -/
theorem if_rule :
    hnRefine ifPre ifProg ifPost "x" natAssn (irIf true (mopConstN 1) (mopConstN 2)) := by
  show hnRefine ifPre (.ite ifCondT (.const "x" 1) (.const "x" 2)) ifPost "x" natAssn _
  refine hnr_If (Γt := ifPost) (Γe := ifPost) if_cond (fun _ => ?_)
    (fun h => absurd h (by decide)) (MERGE_triv _)
  exact hnRefine_frame' (hnr_mop_constN "x" 1)

/-- The abstract side, solved: one `ir.ite` unit and one `ir.const`. -/
theorem if_abs : irIf true (mopConstN 1) (mopConstN 2)
    = NRest.rest (NRest.single 1
        (((irUnit Currency.ite + irUnit Currency.const : ECost)) : WithBot ECost)) := by
  rw [irIf_true, mopConstN_def, NRest.consume_consume, NRest.consume_returnT]

def ifState : State := State.ofPairs [("x", 0), ("n", 5)] []

def ifOut : State × Cost := (evalFuel 4 ifProg ifState).getD (ifState, 0)

theorem if_evalFuel : evalFuel 4 ifProg ifState = some ifOut := rfl

theorem if_bigStep : BigStep ifProg ifState ifOut.1 ifOut.2 := bigStep_of_evalFuel if_evalFuel

-- The concrete run's state and cost vector: the `true` branch, one
-- `ir.ite` for the test and one `ir.const` for the assignment.
#guard Ir.Gate.readVars ifOut.1 ["x", "n"] = [("x", some 1), ("n", some 5)]
#guard Ir.Gate.costVector ifOut.2 =
  [("ir.skip", 0), ("ir.const", 1), ("ir.copy", 0), ("ir.aget", 0), ("ir.aset", 0),
   ("ir.ite", 1), ("ir.while", 0), ("ir.add", 0), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

def ifFrame : Assn :=
  EXACT (((((vcells ifState).erase "x").erase "n"), acells ifState, hcells ifState), 0)

theorem ifPre_holds : irSTATE (ifPre ∗ ifFrame) (ifState, 0) := by
  show (ifPre ∗ ifFrame) ((vcells ifState, acells ifState, hcells ifState), 0)
  simp only [ifPre, junkCell_def, hnCtxt_def, natAssn_def, sepConj_assoc, sepEx_sepConj]
  refine ⟨0, ?_⟩
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

/-- **End to end.** `hnr_If`'s judgment, at that state, runs the program:
the branch taken is the `true` one and the cost vector is the pinned
one. -/
theorem if_runs :
    ∃ s' κ, BigStep ifProg ifState s' κ ∧ Ir.Gate.readVars s' ["x"] = [("x", some 1)] ∧
      Ir.Gate.costVector κ = Ir.Gate.costVector ifOut.2 := by
  obtain ⟨ra, Ca, -, w⟩ := hnRefineD (F := ifFrame) if_rule if_abs ifPre_holds
  obtain ⟨s', κ, hrun, -, -⟩ := w
  refine ⟨s', κ, hrun, ?_, ?_⟩
  all_goals obtain ⟨rfl, rfl⟩ := hrun.unique if_bigStep
  · rfl
  · rfl

/-! ### `hnr_while_measured`, end to end

`while x < three do x := x + y`, at `x = 0`, `y = 1`, `three = 3`: three
iterations, four guard evaluations. The loop state is the value of `x`,
living in the one cell `"x"` across every iteration (P4/D-ah). -/

def wI : ℕ → Prop := fun _ => True

def wbf : ℕ → Bool := fun v => decide (v < 3)

noncomputable def wf : ℕ → NRest ℕ ECost := fun v => mopBinop .add v 1

def wCond : Cond := .lt (.cell "x") (.cell "three")

def wBody : Com := .binop .add "x" "x" "y"

def wProg : Com := .while wCond wBody

/-- The loop frame: the step's operand and the bound, neither touched by
the body. -/
def wFrame : Assn := hnCtxt natAssn 1 "y" ∗ hnCtxt natAssn 3 "three"

theorem w_cond (v : ℕ) (_ : wI v) : CondRefine (hnCtxt natAssn v "x" ∗ wFrame) wCond (wbf v) := by
  have e : (hnCtxt natAssn v "x" ∗ wFrame)
      = ((hnCtxt natAssn v "x" ∗ hnCtxt natAssn 3 "three") ∗ hnCtxt natAssn 1 "y") := by
    unfold wFrame; ac_rfl
  rw [e]
  exact (condRefine_lt_cells v 3 "x" "three").frame

theorem w_body (v : ℕ) (_ : wI v) (_ : wbf v = true) :
    hnRefine (hnCtxt natAssn v "x" ∗ wFrame) wBody wFrame "x" natAssn (wf v) := by
  have e : (hnCtxt natAssn v "x" ∗ wFrame)
      = ((hnCtxt natAssn v "x" ∗ hnCtxt natAssn 1 "y") ∗ hnCtxt natAssn 3 "three") := by
    unfold wFrame; ac_rfl
  rw [e]
  exact hnRefine_frame' (F := hnCtxt natAssn 3 "three") (hnr_mop_binop_self .add "x" "y" v 1)

/-- The body's abstract program, solved: one result, one `ir.add`. -/
theorem wf_rest (v : ℕ) :
    wf v = NRest.rest (NRest.single (v + 1) ((irUnit Currency.add : ECost) : WithBot ECost)) := by
  show mopBinop .add v 1 = _
  rw [mopBinop_def, NRest.consume_returnT]
  rfl

theorem w_var (v v' : ℕ) (_ : wI v) (hb : wbf v = true)
    (h : (NRest.returnT v' : NRest ℕ ECost) ≤ wf v) : 3 - v' < 3 - v := by
  rw [wf_rest, returnT_le_rest_iff] at h
  have hv' : v' = v + 1 := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at h
    exact WithBot.coe_ne_bot h
  have hv : v < 3 := by simpa [wbf] using hb
  omega

/-- The rule, applied: the variant is `3 - x`. -/
theorem w_rule :
    hnRefine (hnCtxt natAssn 0 "x" ∗ wFrame) wProg wFrame "x" natAssn (irWhileIT wI wbf wf 0) := by
  show hnRefine (hnCtxt natAssn 0 "x" ∗ wFrame) (.while wCond wBody) wFrame "x" natAssn _
  exact hnr_while_measured (fun v => 3 - v) w_cond w_body w_var 0

/-- **The same judgment, unfueled (R0/D-b).** `w_var` is not passed, and
not proved for this application: the loop's own non-failure is the
induction. Everything below — the value, the cost vector, the run —
holds of this judgment exactly as of `w_rule`, because it is the same
statement. -/
theorem w_rule_unfueled :
    hnRefine (hnCtxt natAssn 0 "x" ∗ wFrame) wProg wFrame "x" natAssn (irWhileIT wI wbf wf 0) := by
  show hnRefine (hnCtxt natAssn 0 "x" ∗ wFrame) (.while wCond wBody) wFrame "x" natAssn _
  exact hnr_while w_cond w_body 0

/-! #### The abstract loop's value

One unfolding per iteration: the entry unit of the *next* iteration and
the body's `ir.add`, so three iterations cost `3 • (ir.while + ir.add)`
on top of the final guard's `ir.while` — `n` iterations, `n + 1` guard
evaluations (P3 ledger D-h). -/

theorem w_step (v : ℕ) (hv : v < 3) :
    irWhileIT wI wbf wf v
      = NRest.consume (irWhileIT wI wbf wf (v + 1))
          (irUnit Currency.«while» + irUnit Currency.add) := by
  rw [irWhileIT_of_true (show wI v from trivial) (show wbf v = true from by simp [wbf, hv]),
    wf_rest, ← NRest.consume_returnT, NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.returnT_bindT, NRest.consume_consume]

/-- What the whole loop costs: four guard evaluations and three
additions. -/
def wLoopCost : ECost :=
  irUnit Currency.«while» + irUnit Currency.add +
    (irUnit Currency.«while» + irUnit Currency.add) +
      (irUnit Currency.«while» + irUnit Currency.add) + irUnit Currency.«while»

theorem w_value : irWhileIT wI wbf wf 0 = NRest.consume (NRest.returnT 3) wLoopCost := by
  rw [w_step 0 (by norm_num), w_step 1 (by norm_num), w_step 2 (by norm_num),
    irWhileIT_of_false (show wI 3 from trivial) (show wbf 3 = false from by simp [wbf]),
    NRest.consume_consume, NRest.consume_consume, NRest.consume_consume]
  rfl

theorem w_abs :
    irWhileIT wI wbf wf 0
      = NRest.rest (NRest.single 3 ((wLoopCost : ECost) : WithBot ECost)) := by
  rw [w_value, NRest.consume_returnT]

-- The abstract loop's cost vector: four `ir.while`, three `ir.add`.
theorem wLoopCost_while : wLoopCost.toFun Currency.«while» = 4 := by decide
theorem wLoopCost_add : wLoopCost.toFun Currency.add = 3 := by decide
theorem wLoopCost_ite : wLoopCost.toFun Currency.ite = 0 := by decide

def wState : State := State.ofPairs [("x", 0), ("y", 1), ("three", 3)] []

def wOut : State × Cost := (evalFuel 20 wProg wState).getD (wState, 0)

theorem w_evalFuel : evalFuel 20 wProg wState = some wOut := rfl

theorem w_bigStep : BigStep wProg wState wOut.1 wOut.2 := bigStep_of_evalFuel w_evalFuel

-- The concrete run agrees with the abstract account, currency by
-- currency: four guard evaluations, three additions.
#guard Ir.Gate.readVars wOut.1 ["x", "y", "three"] =
  [("x", some 3), ("y", some 1), ("three", some 3)]
#guard Ir.Gate.costVector wOut.2 =
  [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 0), ("ir.aset", 0),
   ("ir.ite", 0), ("ir.while", 4), ("ir.add", 3), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

def wFrameAssn : Assn :=
  EXACT ((((((vcells wState).erase "x").erase "y").erase "three"), acells wState,
    hcells wState), 0)

theorem wPre_holds :
    irSTATE ((hnCtxt natAssn 0 "x" ∗ wFrame) ∗ wFrameAssn) (wState, 0) := by
  show ((hnCtxt natAssn 0 "x" ∗ wFrame) ∗ wFrameAssn)
    ((vcells wState, acells wState, hcells wState), 0)
  simp only [wFrame, hnCtxt_def, natAssn_def, sepConj_assoc]
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

/-- **End to end.** The loop rule's judgment runs the loop: three
iterations, and the cost vector the evaluator pinned. -/
theorem w_runs :
    ∃ s' κ, BigStep wProg wState s' κ ∧ Ir.Gate.readVars s' ["x"] = [("x", some 3)] ∧
      Ir.Gate.costVector κ = Ir.Gate.costVector wOut.2 := by
  obtain ⟨ra, Ca, -, w⟩ := hnRefineD (F := wFrameAssn) w_rule w_abs wPre_holds
  obtain ⟨s', κ, hrun, -, -⟩ := w
  refine ⟨s', κ, hrun, ?_, ?_⟩
  all_goals obtain ⟨rfl, rfl⟩ := hrun.unique w_bigStep
  · rfl
  · rfl

/-! ### Negative control 1 — a wrong-cost branch combinator

`irIf` that charges `ir.skip` instead of `ir.ite` cannot drive an `ite`:
the abstract side then caps the credits it hands over at
`ir.skip + ir.const`, and the program's test is priced in `ir.ite`, of
which the balance holds nothing. -/

/-- The ledger fact behind it. -/
example : Currency.ite ≠ Currency.skip := by decide

noncomputable def irIfWrong {α : Type} (b : Bool) (t e : NRest α ECost) : NRest α ECost :=
  NRest.consume (if b then t else e) (irUnit Currency.skip)

theorem irIfWrong_abs : irIfWrong true (mopConstN 1) (mopConstN 2)
    = NRest.rest (NRest.single 1
        (((irUnit Currency.skip + irUnit Currency.const : ECost)) : WithBot ECost)) := by
  rw [irIfWrong, if_pos rfl, mopConstN_def, NRest.consume_consume, NRest.consume_returnT]

theorem irIf_wrong_currency :
    ¬ hnRefine ifPre ifProg ifPost "x" natAssn (irIfWrong true (mopConstN 1) (mopConstN 2)) := by
  intro h
  obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD (F := ifFrame) h irIfWrong_abs ifPre_holds
  have hra : ra = 1 := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff] at hCa
    exact WithBot.coe_ne_bot hCa
  subst hra
  rw [NRest.single_self, WithBot.coe_le_coe] at hCa
  rw [zero_add, ifProg, wp_ite] at w
  obtain ⟨-, -, hi, -⟩ := w
  have h1 := hi Currency.ite
  have h2 := ACost.le_def.1 hCa Currency.ite
  rw [ACost.toFun_cost_self] at h1
  rw [ACost.toFun_add, ACost.toFun_cost_ne (by decide : Currency.ite ≠ Currency.skip),
    ACost.toFun_cost_ne (by decide : Currency.ite ≠ Currency.const), add_zero,
    le_zero_iff] at h2
  rw [h2] at h1
  simp at h1

/-! ### Negative control 2 — a `CondRefine` that does not hold

The context fixes `n = 5`, so `3 < n` is `true`; claiming `false` is
refutable at the very state the gate uses. -/

def nFrame : Assn := EXACT (((vcells ifState).erase "n", acells ifState, hcells ifState), 0)

theorem condRefine_mismatch : ¬ CondRefine (hnCtxt natAssn 5 "n") ifCondT false := by
  intro h
  have hs : irSTATE (hnCtxt natAssn 5 "n" ∗ nFrame) (ifState, 0) := by
    show (hnCtxt natAssn 5 "n" ∗ nFrame) ((vcells ifState, acells ifState, hcells ifState), 0)
    simp only [hnCtxt_def, natAssn_def]
    exact ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩
  have hcon := h nFrame ifState 0 hs
  rw [show ifCondT.eval ifState = some true from rfl] at hcon
  exact absurd hcon (by decide)

/-! ### Negative control 3 — a failing invariant makes the judgment vacuous

Not a defect: it is the discipline. A loop whose invariant does not hold
at the current state *fails* on the abstract side, and `hnRefine` at a
failing abstract program is trivially true — so the rule proves nothing
there, and this is pinned rather than left implicit. -/

theorem badInv_fails {σ : Type} (bf : σ → Bool) (f : σ → NRest σ ECost) (s : σ) :
    irWhileIT (fun _ => False) bf f s = NRest.fail :=
  irWhileIT_of_not_inv (fun h => h)

theorem badInv_vacuous {σ κ : Type} (bf : σ → Bool) (f : σ → NRest σ ECost) (s : σ)
    (Γ Γ' : Assn) (c : Com) (d : κ) (R : σ → κ → Assn) :
    hnRefine Γ c Γ' d R (irWhileIT (fun _ => False) bf f s) := by
  rw [badInv_fails]
  exact hnr_fail

/-- …and the vacuity is *only* vacuity: the same judgment at a *true*
invariant is the real one, and it is `w_rule` above, which runs. -/
example : wI 0 := trivial

/-! ### Negative control 4 — a loop that genuinely diverges (R0/D-b)

`loopTerm_of_nofailT`'s hypothesis is not decoration. `while true do
skip` — guard always true, body the identity — is nowhere accessible,
and the statement *without* the no-failure hypothesis ("every loop is
`LoopTerm`") is therefore false. What the export says about this loop is
the other half of the same fact: it **is** `FAILT`, which is the
total-correctness reading of the greatest fixed point (`Rec.lean` S2,
`Sanity.RECT_bodyLoop`) and is here derived through the new post-fixed
point rather than from a stability computation. Note also that
`hnr_while` proves the judgment for it — vacuously, exactly as at a
failing invariant, and for the same reason. -/

def dvI : ℕ → Prop := fun _ => True

def dvBf : ℕ → Bool := fun _ => true

noncomputable def dvF : ℕ → NRest ℕ ECost := fun s => NRest.returnT s

/-- Divergence: no state of the spinning loop is accessible. -/
theorem dv_not_loopTerm (s : ℕ) : ¬ LoopTerm dvBf dvF s := by
  intro h
  induction h with
  | @exit s hb => exact absurd hb (by simp [dvBf])
  | @step s _ _ ih => exact ih s le_rfl

/-- …so it fails, by the export itself. -/
theorem dv_fails (s : ℕ) : irWhileIT dvI dvBf dvF s = NRest.fail := by
  by_contra h
  exact dv_not_loopTerm s (loopTerm_of_nofailT (I := dvI) (NRest.nofailT_iff.mpr h))

/-- …and the unfueled rule at it says nothing, which is what a rule at a
failing abstract program must say. -/
theorem dv_vacuous {κ : Type} (s : ℕ) (Γ Γ' : Assn) (c : Com) (d : κ) (R : ℕ → κ → Assn) :
    hnRefine Γ c Γ' d R (irWhileIT dvI dvBf dvF s) := by
  rw [dv_fails]
  exact hnr_fail

end Gate

end Lax13Proofs.Refine.Sepref
