import Lax13Proofs.Refine.NREST.DataRefinement

/-!
Currency refinement for `NRest`: the exchange operator `⇓C`.

Port of `thys/nrest/Time_Refinement.thy` of `isabelle_llvm_time`
(Haslbeck–Lammich, ESOP'21 artifact) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1,
github.com/lammich/isabelle_llvm_time @ 42dd7f5, together with the one
lemma of `thys/nrest/NREST_Main.thy` that makes `⇓C` and `⇓R` talk to
each other (`timerefine_conc_fun_ge2`, delta T6). The definitions and
the lemma statements ported here, verbatim from those files:

```isabelle
definition timerefine ::"('b ⇒ ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost)
                             ⇒ ('a, ('b,'d) acost) nrest ⇒ ('a, ('c,'d) acost) nrest" ("⇓C")
  where "⇓C R m = (case m of FAILi ⇒ FAILi |
                REST M ⇒ REST (λr. case M r of None ⇒ None |
                  Some cm ⇒ Some (acostC (λcc. Sum_any (λac. the_acost cm ac *
                                     the_acost (R ac) cc)))))"
definition timerefineF R M = (λr. case M r of None ⇒ None |
                  Some cm ⇒ Some (acostC (λcc. Sum_any (λac. …))))
definition timerefineA R cm = (acostC (λcc. Sum_any (λac. the_acost cm ac * the_acost (R ac) cc)))
lemma timerefineA_0[simp]: "timerefineA r 0 = 0"
lemma timerefine_SPECT: "⇓C R (SPECT Q) = SPECT (timerefineF R Q)"
lemma SPEC_timerefine_conv: "⇓C R (SPEC A B') = SPEC A (λx. timerefineA R (B' x))"
lemma timerefineA_cost_apply: "timerefineA TR (cost n (t::enat)) = acostC (λx. t * the_acost (TR n) x)"
lemma timerefineA_cost: "timerefineA TR (cost n (1::enat)) = TR n"
lemma timerefineA_update_apply_same_cost:
  "timerefineA (F(n := y)) (cost n (t::enat)) = acostC (λx. t * the_acost y x)"
lemma timerefineA_update_cost[simp]:
  "n≠m ⟹ timerefineA (F(n := y)) (cost m (t::enat)) = timerefineA F (cost m t)"
definition wfn m = (case m of FAILi ⇒ True |
                REST M ⇒ ∀r∈dom M. (case M r of None ⇒ True
                  | Some cm ⇒ finite {x. the_acost cm x ≠ 0}))
definition "wfR R = (finite {(s,f). the_acost (R s) f ≠ 0})"
definition "wfR' R = (∀s. finite {f. the_acost (R s) f ≠ 0})"
definition "wfR'' R = (∀f. finite {s. the_acost (R s) f ≠ 0})"
definition "wfR2 R = (finite {f. the_acost R f ≠ 0})"
lemma wfR''_upd[intro]: "wfR'' F ⟹ wfR'' (F(x:=y))"
lemma "wfR R ⟹ wfR'' R"     lemma "wfR R ⟹ wfR' R"
lemma wfR_fst: "⋀y. wfR R ⟹ finite {x. the_acost (R x) y ≠ 0}"
lemma wfR_snd: "⋀s. wfR R ⟹ finite {y. the_acost (R s) y ≠ 0}"
lemma wfR''_finite_mult_left:
  assumes "wfR'' R" shows "finite {ac. the_acost cm ac * the_acost (R ac) cc ≠ 0}"
lemma wfR_finite_mult_left:
  assumes "wfR R" shows "finite {a. the_acost Mc a * the_acost (R2 a) ac ≠ 0}"
lemma wfR_finite_Sum_any:
  assumes *: "wfR R"
  shows "finite {x. ((Sum_any (λac. (the_acost Mc ac * (the_acost (R ac) x)))) ≠ 0)}"
lemma wfn_timerefine: "wfn m ⟹ wfR R ⟹ wfn (⇓C R m)"
lemma [simp]: "⇓C R FAILT = FAILT"
definition pp where
  "pp R2 R1 = (λa. acostC (λc. Sum_any (%b. the_acost (R1 a) b * the_acost (R2 b) c  ) ))"
lemma pp_fun_upd: "pp A (B(a:=b)) = (pp A B)(a:=timerefineA A b)"
lemma timerefineA_propagate:
  assumes "wfR'' E" fixes a b :: "('a, enat) acost"
  shows "timerefineA E (a + b) = timerefineA E a + timerefineA E b"
lemma timerefine_consume:
  assumes "wfR'' E"
  shows "⇓C E (consume M t) = consume (⇓C E (M:: (_, (_, enat) acost) nrest)) (timerefineA E t)"
lemma timerefineA_iter2:
  fixes R1 :: "_ ⇒ ('a, enat) acost"   assumes "wfR'' R1" "wfR'' R2"
  shows "timerefineA R1 (timerefineA R2 c) =  timerefineA (pp R1 R2) c"
lemma pp_assoc: fixes A :: "'d ⇒ ('b, enat) acost"
  assumes A: "wfR'' A" and B: "wfR'' B"  shows "pp A (pp B C) = pp (pp A B) C"
lemma wfR''_ppI: fixes R1 :: "'a ⇒ ('b, enat) acost"
  assumes R1: "wfR'' R1" and R2: "wfR'' R2"  shows "wfR'' (pp R1 R2)"
lemma timerefine_iter2: fixes R1 :: "_ ⇒ ('a, enat) acost"
  assumes "wfR'' R1" "wfR'' R2"  shows "⇓C R1 (⇓C R2 c) =  ⇓C (pp R1 R2) c"
lemma timerefine_mono2:
  fixes R :: "_ ⇒ ('a, 'b::{complete_lattice,nonneg,mult_zero,ordered_semiring}) acost"
  assumes "wfR'' R"  shows "c≤c' ⟹ ⇓C R c ≤ ⇓C R c'"
lemma timerefine_R_mono_wfR'': fixes R :: "_ ⇒ ('a, enat) acost"
  assumes "wfR'' R'"  shows "R≤R' ⟹ ⇓C R c ≤ ⇓C R' c"
lemma timerefine_trans: assumes "wfR R1" "wfR R2"
  shows "a ≤ ⇓C R1 b ⟹ b ≤ ⇓C R2 c ⟹ a ≤ ⇓C (pp R1 R2) c"
lemma timerefine_RETURNT: "⇓C E (RETURNT x') = RETURNT x'"
lemma timerefine_SPECT_map: "⇓C E (SPECT [x'↦t]) = SPECT [x'↦timerefineA E t]"
lemma nofailT_timerefine[refine_pw_simps]: "nofailT (⇓C R m) ⟷ nofailT m"
lemma timerefine_bindT_ge2: fixes R :: "_ ⇒ ('a,enat) acost"
  assumes wfR'': "wfR'' R"
  shows "bindT (⇓C R m) (λx. ⇓C R (f x)) ≤ ⇓C R (bindT m f)"
definition "struct_preserving E ≡ (∀t. cost ''call'' t ≤ timerefineA E (cost ''call'' t))
                                   ∧ (∀t. cost ''if'' t ≤ timerefineA E (cost ''if'' t))"
lemma struct_preserving_upd_I[intro]: fixes F:: "char list ⇒ (char list, enat) acost"
  shows "struct_preserving F ⟹ x≠''if''⟹ x≠''call'' ⟹ struct_preserving (F(x:=y))"
definition "preserves_curr R n ⟷ (R n = (cost n 1))"
lemma preserves_curr_other_updI: "preserves_curr R m ⟹ n≠m ⟹ preserves_curr (R(n:=t)) m"
definition "TId = (λx. acostC (λy. (if x=y then 1 else 0)))"
lemma TId_apply: "TId x = cost x 1"
lemma preserves_curr_TId[simp]: "preserves_curr TId n"
lemma cost_n_leq_TId_n: "cost n (1::enat) ≤ TId n"
lemma timerefine_id: fixes M :: "(_,(_,enat)acost) nrest"  shows "⇓C TId M = M"
lemma timerefineA_TId: fixes T :: "(_,enat) acost"  shows "T ≤ T' ⟹ T ≤ timerefineA TId T'"
lemma sp_TId[simp]: "struct_preserving (TId::_⇒(string, enat) acost)"
lemma pp_TId_absorbs_right: fixes A :: "'b ⇒ ('c, enat) acost"  shows "pp A TId = A"
lemma pp_TId_absorbs_left:  fixes A :: "'b ⇒ ('c, enat) acost"  shows "pp TId A  = A"
lemma timerefineA_TId_eq[simp]: shows "timerefineA TId x = (x:: ('b, enat) acost)"
lemma "wfR' TId"    lemma wfR''_TId[simp]: "wfR'' TId"
lemma SPEC_timerefine:
  "A ≤ A' ⟹ (⋀x. B x ≤ timerefineA R (B' x)) ⟹ SPEC A B ≤ ⇓C R (SPEC A' B')"
lemma SPEC_timerefine_eq: "(⋀x. B x = timerefineA R (B' x)) ⟹ SPEC A B = ⇓C R (SPEC A B')"
lemma finite_sum_nonzero_cost: "finite {a. the_acost (cost n m) a ≠ 0}"
```

and, from `NREST_Main.thy` (same pin), the `⇓R`/`⇓C` interaction:

```isabelle
lemma timerefine_conc_fun_ge2:
  fixes C :: "('f, ('b, enat) acost) nrest"
  assumes "wfR'' E"
  shows "⇓C E (⇓ R C) ≥ ⇓R (⇓C E C)"
```

## Substrate deltas, each flagged

**T1 — `Sum_any` is mathlib's `∑ᶠ`.** Isabelle's
`Sum_any f = (if finite {a. f a ≠ 0} then sum f {a. f a ≠ 0} else 0)`
*is* mathlib's `finsum`, definition for definition, so the source's
finite-support side conditions (`wfR`, `wfR'`, `wfR''`) keep their exact
role: they are what makes the sums have finitely many nonzero terms.
Design record F2 (plain functions, not `Finsupp`) is what lets that role
survive.

**T2 — where the class constraints went.** The source's sort
`'d::{complete_lattice,comm_monoid_add,times,mult_zero}` on `timerefine`
cannot be transcribed: in Lean `AddCommMonoid γ` and `MulZeroClass γ`
each carry their own `Zero γ`, so assuming both introduces a `Zero`
diamond, whereas Isabelle's type classes share the single `zero`. The
definitions here therefore ask only for what they use —
`[AddCommMonoid γ] [Mul γ]`, no `CompleteLattice` at all, since
`Basic.lean` already put the sort constraints on the *operations* rather
than on `NRest` — and every algebraic lemma is stated at the source's
own carrier `ℕ∞` (`enat`), which is where the source states essentially
all of them anyway (design record F7). The one lemma the source states
generally and this file states at `ℕ∞` is `timerefineA_0`
(`timerefineA_zero` below); it needs `0 * a = 0`, i.e. exactly the
`mult_zero` that cannot be assumed separately.

**T3 — currency-typed arguments.** Abstract currencies are `κ`,
concrete ones `κ'`; an exchange rate is `κ → ACost κ' γ` and
`⇓C R : NRest α (ACost κ γ) → NRest α (ACost κ' γ)`. The source's
`string` currencies (design record F1) are the instance the tower uses;
`struct_preserving` and `sp_TId` are stated there, at `ECost`, exactly
as the source does.

**T4 — one mathlib gap filled locally.** `finsum_comm_of_support`: a
Fubini principle for `∑ᶠ` under a rectangular finite-support bound.
Mathlib has `finsum_mem_comm` (both index sets restricted and finite)
and `sum_finsum_comm` (one side a `Finset`), neither of which is the
shape `timerefineA_iter2` needs. It is proved here from
`finsum_eq_sum_of_support_subset` and `Finset.sum_comm`, and is a
candidate for upstreaming. `finsum_le_finsum'` (mathlib) replaces the
source's `Sum_any_mono`; the source derives `f`'s finite support from
its `nonneg` class, we derive it from `f ≤ g` at `ℕ∞`.

**T5 — `wfn` and the `dom` spelling.** The source's
`∀r∈dom M. case M r of None ⇒ True | Some cm ⇒ …` is `∀ r cm, M r = ↑cm → …`:
the `dom` restriction and the `None` arm are the same condition twice.

**T6 — placement of `timerefine_conc_fun_ge2`.** The `⇓R`/`⇓C`
commutation the tower needs is in the source's `NREST_Main.thy`, not in
`Time_Refinement.thy` or `Data_Refinement.thy` (the latter has only a
commented-out `datarefine_timerefine_commute` inside an `experiment`
block, which is not part of its API). It is ported here, since this is
the file that has `⇓C`. Note that it is an *inequality*, in the source's
direction: `⇓R (⇓C E C) ≤ ⇓C E (⇓R C)`. The source's `⇓R` side takes a
supremum over related abstract results and `⇓C` is not
supremum-continuous, so equality is not available and the tower does not
use it.

**T7 — not ported.** `limRef`, `pl`, `pl2`, `kkk`, `kkk2`, `aaa`,
`***`, `limRef_bindT_le`, `inresT_limRef_D`, `inresTf'`,
`pw_bindT_nofailTf'`, `nofailT_limRef`, `limRef_limit_timerefine`: this
is the source's *proof machinery* for `timerefine_bindT_ge`, routed
through `project_acost` (not in the frozen `Basic.lean`/`Pw.lean` API).
The statement `timerefine_bindT_ge2` is ported and proved directly here
from `timerefine_consume` and monotonicity, which is shorter and needs
none of it — a change of proof, not of statement (charter: restructure
proofs, never the surface). Also not ported: the `wfR`-hypothesis twins
of lemmas whose `wfR''` version is ported (`timerefine_mono`,
`timerefine_R_mono`, `timerefine_bindT_ge`, `timerefine_iter`,
`timerefine_conc_fun_ge`) — `wfR` implies `wfR''` (`wfR.wfR''` below),
so each follows in one step and the source itself marks `wfR''` as the
better notion ("I think this is better. It captures 'finitely
branching'"); `timerefine_alt3`/`timerefine_alt4`/`timerefine'`
(alternative spellings of the definition); `timerefine_mono_both`,
`timerefine_mono3` (immediate variants); `timerefine_inf_top_distrib`
and its `enat`-arithmetic auxiliaries (a `SPEC`-with-`⊤`-time
convenience the tower has no consumer for yet); `SPECT_emb'_timerefine`
(needs `emb'`); the `enum`/`foldr` setup section (an Isabelle code-
generation convenience); `Sum_any_mono`, `finite_support_mult`,
`wfR_finite_crossprod`, `finite_wfR_middle_mult`, `wfR_sup`,
`wfR2_If_if_wfR2`, `wfR2_enum` (auxiliaries whose consumers are not
ported, or which mathlib supplies).
-/

namespace Lax13Proofs.Refine

variable {α γ κ κ' κ'' : Type}

/-! ### Two `∑ᶠ` facts (delta T4) -/

/-- A `∑ᶠ` all of whose terms vanish is zero. Isabelle reads this off
`Sum_any.expand_set`; here it is one rewrite. -/
theorem finsum_eq_zero_of_forall {ι M : Type} [AddCommMonoid M] {f : ι → M}
    (h : ∀ i, f i = 0) : (∑ᶠ i, f i) = 0 := by
  rw [show f = fun _ => (0 : M) from funext h, finsum_zero]

/-- Two iterated `∑ᶠ`s commute when every nonzero term sits inside a
finite rectangle `A × B`. Mathlib has `finsum_mem_comm` (both sums
restricted to finite sets) and `sum_finsum_comm` (one side a `Finset`);
neither is this shape. -/
theorem finsum_comm_of_support {ι₁ ι₂ M : Type} [AddCommMonoid M] {A : Set ι₁} {B : Set ι₂}
    (hA : A.Finite) (hB : B.Finite) (F : ι₁ → ι₂ → M)
    (h : ∀ a b, F a b ≠ 0 → a ∈ A ∧ b ∈ B) :
    (∑ᶠ b, ∑ᶠ a, F a b) = ∑ᶠ a, ∑ᶠ b, F a b := by
  classical
  have hrow : ∀ b, Function.support (fun a => F a b) ⊆ (hA.toFinset : Set ι₁) := by
    intro b a ha
    simpa using (h a b ha).1
  have hcol : ∀ a, Function.support (fun b => F a b) ⊆ (hB.toFinset : Set ι₂) := by
    intro a b hb
    simpa using (h a b hb).2
  have hrowSum : ∀ b, (∑ᶠ a, F a b) = ∑ a ∈ hA.toFinset, F a b := fun b =>
    finsum_eq_sum_of_support_subset _ (hrow b)
  have hcolSum : ∀ a, (∑ᶠ b, F a b) = ∑ b ∈ hB.toFinset, F a b := fun a =>
    finsum_eq_sum_of_support_subset _ (hcol a)
  have houter1 : Function.support (fun b => ∑ᶠ a, F a b) ⊆ (hB.toFinset : Set ι₂) := by
    intro b hb
    simp only [Function.mem_support] at hb
    by_contra hbB
    refine hb ?_
    have hz : (fun a => F a b) = fun _ => (0 : M) := by
      funext a
      by_contra hab
      exact hbB (by simpa using (h a b hab).2)
    rw [hz, finsum_zero]
  have houter2 : Function.support (fun a => ∑ᶠ b, F a b) ⊆ (hA.toFinset : Set ι₁) := by
    intro a ha
    simp only [Function.mem_support] at ha
    by_contra haA
    refine ha ?_
    have hz : (fun b => F a b) = fun _ => (0 : M) := by
      funext b
      by_contra hab
      exact haA (by simpa using (h a b hab).1)
    rw [hz, finsum_zero]
  rw [finsum_eq_sum_of_support_subset _ houter1, finsum_eq_sum_of_support_subset _ houter2]
  rw [Finset.sum_congr rfl fun b _ => hrowSum b, Finset.sum_congr rfl fun a _ => hcolSum a]
  exact Finset.sum_comm

namespace NRest

/-! ### The exchange operator -/

/-- The source's `timerefineA R cm`: the cost `cm`, repriced by the
exchange rate `R`. Each abstract currency `ac` is bought at
`R ac` concrete currencies, and the bill is summed over the (finitely
many, by `wfR''`) abstract currencies actually charged. -/
noncomputable def timerefineA [AddCommMonoid γ] [Mul γ] (R : κ → ACost κ' γ) (cm : ACost κ γ) :
    ACost κ' γ :=
  ⟨fun cc => ∑ᶠ ac, cm.toFun ac * (R ac).toFun cc⟩

@[simp] theorem toFun_timerefineA [AddCommMonoid γ] [Mul γ] (R : κ → ACost κ' γ)
    (cm : ACost κ γ) (cc : κ') :
    (timerefineA R cm).toFun cc = ∑ᶠ ac, cm.toFun ac * (R ac).toFun cc := rfl

/-- The source's `timerefineF`: `timerefineA` on a whole result map. -/
noncomputable def timerefineF [AddCommMonoid γ] [Mul γ] (R : κ → ACost κ' γ)
    (M : α → WithBot (ACost κ γ)) : α → WithBot (ACost κ' γ) :=
  fun r => WithBot.map (timerefineA R) (M r)

@[simp] theorem timerefineF_apply [AddCommMonoid γ] [Mul γ] (R : κ → ACost κ' γ)
    (M : α → WithBot (ACost κ γ)) (r : α) :
    timerefineF R M r = WithBot.map (timerefineA R) (M r) := rfl

/-- The source's `timerefine R m`, written `⇓C R m`: the program `m`
with every cost repriced by the exchange rate `R`. -/
noncomputable def timerefine [AddCommMonoid γ] [Mul γ] (R : κ → ACost κ' γ)
    (m : NRest α (ACost κ γ)) : NRest α (ACost κ' γ) :=
  match m with
  | .fail => .fail
  | .rest M => .rest (timerefineF R M)

@[simp] theorem timerefine_fail [AddCommMonoid γ] [Mul γ] (R : κ → ACost κ' γ) :
    timerefine R (fail : NRest α (ACost κ γ)) = fail := rfl

@[simp] theorem timerefine_rest [AddCommMonoid γ] [Mul γ] (R : κ → ACost κ' γ)
    (M : α → WithBot (ACost κ γ)) : timerefine R (rest M) = rest (timerefineF R M) := rfl

/-- The source's `nofailT_timerefine`. -/
@[simp] theorem nofailT_timerefine [CompleteLattice γ] [AddCommMonoid γ] [Mul γ]
    (R : κ → ACost κ' γ) (m : NRest α (ACost κ γ)) :
    nofailT (timerefine R m) ↔ nofailT m := by
  cases m <;> simp [nofailT_iff, timerefine]

@[simp] theorem timerefine_eq_fail_iff [AddCommMonoid γ] [Mul γ] {R : κ → ACost κ' γ}
    {m : NRest α (ACost κ γ)} : timerefine R m = fail ↔ m = fail := by
  cases m <;> simp

/-- The source's `timerefine_SPECT`. -/
theorem timerefine_spect [AddCommMonoid γ] [Mul γ] (R : κ → ACost κ' γ)
    (Q : α → WithBot (ACost κ γ)) : timerefine R (rest Q) = rest (timerefineF R Q) := rfl

/-! ### Well-formed exchange rates

The source's four finite-support predicates, verbatim. `wfR''`
("finitely branching": each *concrete* currency is priced by finitely
many abstract ones) is the one almost every lemma below asks for; the
source says so itself. -/

/-- The source's `wfR R`: finitely many nonzero entries in total. -/
def wfR [Zero γ] (R : κ → ACost κ' γ) : Prop := {p : κ × κ' | (R p.1).toFun p.2 ≠ 0}.Finite

/-- The source's `wfR' R`: each abstract currency costs finitely many
concrete ones. -/
def wfR' [Zero γ] (R : κ → ACost κ' γ) : Prop := ∀ s, {f | (R s).toFun f ≠ 0}.Finite

/-- The source's `wfR'' R`: each concrete currency is bought by finitely
many abstract ones. -/
def wfR'' [Zero γ] (R : κ → ACost κ' γ) : Prop := ∀ f, {s | (R s).toFun f ≠ 0}.Finite

/-- The source's `wfR2`: a single cost has finite support. -/
def wfR2 [Zero γ] (c : ACost κ γ) : Prop := {f | c.toFun f ≠ 0}.Finite

/-- The source's `wfn`: every cost the program can pay has finite
support (delta T5). -/
def wfn [Zero γ] (m : NRest α (ACost κ γ)) : Prop :=
  match m with
  | .fail => True
  | .rest M => ∀ (r : α) (cm : ACost κ γ), M r = (cm : WithBot (ACost κ γ)) →
      {x | cm.toFun x ≠ 0}.Finite

@[simp] theorem wfn_fail [Zero γ] : wfn (fail : NRest α (ACost κ γ)) := by
  show True
  trivial

@[simp] theorem wfn_rest [Zero γ] (M : α → WithBot (ACost κ γ)) :
    wfn (rest M) ↔ ∀ (r : α) (cm : ACost κ γ), M r = (cm : WithBot (ACost κ γ)) →
      {x | cm.toFun x ≠ 0}.Finite := Iff.rfl

/-- The source's `wfR_fst`. -/
theorem wfR.fst [Zero γ] {R : κ → ACost κ' γ} (h : wfR R) (y : κ') :
    {x | (R x).toFun y ≠ 0}.Finite :=
  (h.image Prod.fst).subset fun x hx => ⟨(x, y), hx, rfl⟩

/-- The source's `wfR_snd`. -/
theorem wfR.snd [Zero γ] {R : κ → ACost κ' γ} (h : wfR R) (s : κ) :
    {y | (R s).toFun y ≠ 0}.Finite :=
  (h.image Prod.snd).subset fun y hy => ⟨(s, y), hy, rfl⟩

/-- The source's `"wfR R ⟹ wfR'' R"`. -/
theorem wfR.wfR'' [Zero γ] {R : κ → ACost κ' γ} (h : wfR R) : wfR'' R := h.fst

/-- The source's `"wfR R ⟹ wfR' R"`. -/
theorem wfR.wfR' [Zero γ] {R : κ → ACost κ' γ} (h : wfR R) : wfR' R := h.snd

/-- The source's `wfR''_upd`. -/
theorem wfR''.update [Zero γ] [DecidableEq κ] {F : κ → ACost κ' γ} (h : wfR'' F) (x : κ)
    (y : ACost κ' γ) : wfR'' (Function.update F x y) := by
  intro f
  refine ((h f).union (Set.finite_singleton x)).subset fun s hs => ?_
  by_cases hsx : s = x
  · exact Or.inr hsx
  · left
    simpa [Function.update_of_ne hsx] using hs

/-- The source's `finite_sum_nonzero_cost`. -/
theorem wfR2_cost [DecidableEq κ] [Zero γ] (n : κ) (m : γ) : wfR2 (ACost.cost n m) :=
  (Set.finite_singleton n).subset fun a ha => by
    by_contra hne
    exact ha (ACost.toFun_cost_ne hne m)

/-- The source's `wfR''_finite_mult_left`. -/
theorem wfR''.finite_mult_left {R : κ → ACost κ' ℕ∞} (h : wfR'' R) (cm : ACost κ ℕ∞) (cc : κ') :
    {ac | cm.toFun ac * (R ac).toFun cc ≠ 0}.Finite :=
  (h cc).subset fun ac hac hz => hac (by rw [hz, mul_zero])

/-- The source's `wfR_finite_mult_left`. -/
theorem wfR.finite_mult_left {R : κ → ACost κ' ℕ∞} (h : wfR R) (cm : ACost κ ℕ∞) (cc : κ') :
    {ac | cm.toFun ac * (R ac).toFun cc ≠ 0}.Finite :=
  h.wfR''.finite_mult_left cm cc

/-- The source's `wfR_finite_Sum_any`. -/
theorem wfR.finite_finsum {R : κ → ACost κ' ℕ∞} (h : wfR R) (cm : ACost κ ℕ∞) :
    {x | (∑ᶠ ac, cm.toFun ac * (R ac).toFun x) ≠ 0}.Finite := by
  refine (h.image Prod.snd).subset fun x hx => ?_
  simp only [Set.mem_setOf_eq] at hx
  by_contra hnot
  refine hx (finsum_eq_zero_of_forall fun ac => ?_)
  by_cases hac : (R ac).toFun x = 0
  · rw [hac, mul_zero]
  · exact absurd ⟨(ac, x), hac, rfl⟩ hnot

/-- The source's `wfn_timerefine`. -/
theorem wfn_timerefine {R : κ → ACost κ' ℕ∞} {m : NRest α (ACost κ ℕ∞)} (hm : wfn m)
    (hR : wfR R) : wfn (timerefine R m) := by
  cases m with
  | fail => exact wfn_fail
  | rest M =>
    rw [timerefine_rest, wfn_rest]
    intro r cm hcm
    rcases withBot_eq_bot_or_coe (M r) with hb | ⟨cm', hb⟩
    · rw [timerefineF_apply, hb] at hcm
      simp at hcm
    · rw [timerefineF_apply, hb, WithBot.map_coe] at hcm
      have hcm' : cm = timerefineA R cm' := (WithBot.coe_inj.mp hcm).symm
      subst hcm'
      exact hR.finite_finsum cm'

/-! ### The algebra of `timerefineA`

All at the source's carrier `enat` (delta T2). -/

/-- The source's `timerefineA_0` (delta T2: at `ℕ∞`). -/
@[simp] theorem timerefineA_zero (R : κ → ACost κ' ℕ∞) : timerefineA R 0 = 0 := by
  ext cc
  simp

/-- The source's `timerefineA_propagate`. -/
theorem timerefineA_add {E : κ → ACost κ' ℕ∞} (hE : wfR'' E) (a b : ACost κ ℕ∞) :
    timerefineA E (a + b) = timerefineA E a + timerefineA E b := by
  ext cc
  simp only [toFun_timerefineA, ACost.toFun_add]
  rw [show (fun ac => (a.toFun ac + b.toFun ac) * (E ac).toFun cc)
      = fun ac => a.toFun ac * (E ac).toFun cc + b.toFun ac * (E ac).toFun cc from
        funext fun ac => by rw [add_mul]]
  exact finsum_add_distrib (hE.finite_mult_left a cc) (hE.finite_mult_left b cc)

/-- `timerefineA` is monotone in the cost. Isabelle gets this from
`Sum_any_mono`; mathlib's `finsum_le_finsum'` wants both supports
finite, and at `ℕ∞` the smaller one's support is contained in the
larger one's. -/
theorem timerefineA_mono {E : κ → ACost κ' ℕ∞} (hE : wfR'' E) {a b : ACost κ ℕ∞} (h : a ≤ b) :
    timerefineA E a ≤ timerefineA E b := by
  intro cc
  refine finsum_le_finsum' (hE.finite_mult_left a cc) (hE.finite_mult_left b cc) fun ac => ?_
  have := ACost.le_def.mp h ac
  gcongr

/-- `timerefineA` is monotone in the exchange rate. -/
theorem timerefineA_R_mono {E E' : κ → ACost κ' ℕ∞} (hE' : wfR'' E') (h : E ≤ E')
    (a : ACost κ ℕ∞) : timerefineA E a ≤ timerefineA E' a := by
  intro cc
  have hsub : {ac | a.toFun ac * (E ac).toFun cc ≠ 0}
      ⊆ {ac | a.toFun ac * (E' ac).toFun cc ≠ 0} := by
    intro ac hac hz
    refine hac ?_
    rcases mul_eq_zero.mp hz with h0 | h0
    · rw [h0, zero_mul]
    · have : (E ac).toFun cc = 0 :=
        le_antisymm (h0 ▸ ACost.le_def.mp (h ac) cc) zero_le
      rw [this, mul_zero]
  refine finsum_le_finsum' ((hE'.finite_mult_left a cc).subset hsub)
    (hE'.finite_mult_left a cc) fun ac => ?_
  have := ACost.le_def.mp (h ac) cc
  gcongr

/-! ### Composition of exchange rates: `pp` -/

/-- The source's `pp R2 R1`: the exchange rate that applies `R1` and
then `R2`. Note the argument order — the *outer* rate comes first,
matching `timerefineA_iter2`. -/
noncomputable def pp [AddCommMonoid γ] [Mul γ] (R2 : κ' → ACost κ'' γ) (R1 : κ → ACost κ' γ) :
    κ → ACost κ'' γ :=
  fun a => ⟨fun c => ∑ᶠ b, (R1 a).toFun b * (R2 b).toFun c⟩

/-- `pp` is `timerefineA` on the rate itself. This is the source's own
reading — its `pp_fun_upd` says exactly this at one point. -/
theorem pp_apply [AddCommMonoid γ] [Mul γ] (R2 : κ' → ACost κ'' γ) (R1 : κ → ACost κ' γ)
    (a : κ) : pp R2 R1 a = timerefineA R2 (R1 a) := rfl

/-- The source's `pp_fun_upd`. -/
theorem pp_update [AddCommMonoid γ] [Mul γ] [DecidableEq κ] (A : κ' → ACost κ'' γ)
    (B : κ → ACost κ' γ) (a : κ) (b : ACost κ' γ) :
    pp A (Function.update B a b) = Function.update (pp A B) a (timerefineA A b) := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [pp_apply]
  · simp [pp_apply, Function.update_of_ne hx]

/-- The source's `timerefineA_iter2`: repricing twice is repricing at
the composed rate. This is where the `∑ᶠ` Fubini principle of delta T4
is used. -/
theorem timerefineA_iter2 {R1 : κ' → ACost κ'' ℕ∞} {R2 : κ → ACost κ' ℕ∞}
    (h1 : wfR'' R1) (h2 : wfR'' R2) (c : ACost κ ℕ∞) :
    timerefineA R1 (timerefineA R2 c) = timerefineA (pp R1 R2) c := by
  ext cc
  simp only [toFun_timerefineA, pp]
  -- both sides are the double sum of `F a b = c a * R2 a b * R1 b cc`
  have hleft : (∑ᶠ b, (∑ᶠ ac, c.toFun ac * (R2 ac).toFun b) * (R1 b).toFun cc)
      = ∑ᶠ (b : κ'), ∑ᶠ (a : κ), c.toFun a * (R2 a).toFun b * (R1 b).toFun cc :=
    finsum_congr fun b => finsum_mul _ _
  have hright : (∑ᶠ ac, c.toFun ac * ∑ᶠ b, (R2 ac).toFun b * (R1 b).toFun cc)
      = ∑ᶠ (a : κ), ∑ᶠ (b : κ'), c.toFun a * (R2 a).toFun b * (R1 b).toFun cc :=
    finsum_congr fun a =>
      (mul_finsum _ _).trans (finsum_congr fun b => (mul_assoc _ _ _).symm)
  rw [hleft, hright]
  refine finsum_comm_of_support (A := ⋃ b ∈ {b | (R1 b).toFun cc ≠ 0}, {a | (R2 a).toFun b ≠ 0})
    (B := {b | (R1 b).toFun cc ≠ 0}) ((h1 cc).biUnion fun b _ => h2 b) (h1 cc) _ ?_
  intro a b hab
  have hb : (R1 b).toFun cc ≠ 0 := fun h0 => hab (by rw [h0, mul_zero])
  have ha : (R2 a).toFun b ≠ 0 := fun h0 => hab (by rw [h0, mul_zero, zero_mul])
  exact ⟨Set.mem_biUnion hb ha, hb⟩

/-- The source's `pp_assoc`. -/
theorem pp_assoc {A : κ' → ACost κ'' ℕ∞} {B : κ → ACost κ' ℕ∞} (hA : wfR'' A) (hB : wfR'' B)
    {ι : Type} (C : ι → ACost κ ℕ∞) : pp A (pp B C) = pp (pp A B) C := by
  funext a
  simp only [pp_apply]
  exact timerefineA_iter2 hA hB (C a)

/-- The source's `wfR''_ppI`. -/
theorem wfR''.pp {R1 : κ' → ACost κ'' ℕ∞} {R2 : κ → ACost κ' ℕ∞} (h1 : wfR'' R1)
    (h2 : wfR'' R2) : wfR'' (pp R1 R2) := by
  intro f
  refine (((h1 f).biUnion fun b _ => h2 b)).subset fun s hs => ?_
  by_contra hnot
  refine hs ?_
  show (∑ᶠ b, (R2 s).toFun b * (R1 b).toFun f) = 0
  refine finsum_eq_zero_of_forall fun b => ?_
  by_cases hb : (R1 b).toFun f = 0
  · rw [hb, mul_zero]
  · by_cases hs2 : (R2 s).toFun b = 0
    · rw [hs2, zero_mul]
    · exact absurd (Set.mem_biUnion hb hs2) hnot

/-! ### Monotonicity, identity and composition of `⇓C` -/

/-- The source's `timerefine_mono2`. -/
theorem timerefine_mono {R : κ → ACost κ' ℕ∞} (hR : wfR'' R) {c c' : NRest α (ACost κ ℕ∞)}
    (h : c ≤ c') : timerefine R c ≤ timerefine R c' := by
  cases c' with
  | fail => simp
  | rest X' =>
    cases c with
    | fail => simp at h
    | rest X =>
      have hle := rest_le_rest_iff.mp h
      rw [timerefine_rest, timerefine_rest, rest_le_rest_iff]
      intro r
      rcases withBot_eq_bot_or_coe (X r) with hb | ⟨cm, hb⟩
      · simp [timerefineF_apply, hb]
      · rcases withBot_eq_bot_or_coe (X' r) with hb' | ⟨cm', hb'⟩
        · have := hle r
          rw [hb, hb'] at this
          simp at this
        · have hcm : cm ≤ cm' := by
            have := hle r
            rw [hb, hb'] at this
            exact WithBot.coe_le_coe.mp this
          simp only [timerefineF_apply, hb, hb', WithBot.map_coe, WithBot.coe_le_coe]
          exact timerefineA_mono hR hcm

/-- The source's `timerefine_R_mono_wfR''`. -/
theorem timerefine_R_mono {R R' : κ → ACost κ' ℕ∞} (hR' : wfR'' R') (h : R ≤ R')
    (c : NRest α (ACost κ ℕ∞)) : timerefine R c ≤ timerefine R' c := by
  cases c with
  | fail => simp
  | rest X =>
    rw [timerefine_rest, timerefine_rest, rest_le_rest_iff]
    intro r
    rcases withBot_eq_bot_or_coe (X r) with hb | ⟨cm, hb⟩
    · simp [timerefineF_apply, hb]
    · simp only [timerefineF_apply, hb, WithBot.map_coe, WithBot.coe_le_coe]
      exact timerefineA_R_mono hR' h cm

/-- The source's `timerefine_iter2`. -/
theorem timerefine_iter2 {R1 : κ' → ACost κ'' ℕ∞} {R2 : κ → ACost κ' ℕ∞} (h1 : wfR'' R1)
    (h2 : wfR'' R2) (c : NRest α (ACost κ ℕ∞)) :
    timerefine R1 (timerefine R2 c) = timerefine (pp R1 R2) c := by
  cases c with
  | fail => rfl
  | rest X =>
    rw [timerefine_rest, timerefine_rest, timerefine_rest, rest_inj_iff]
    funext r
    rcases withBot_eq_bot_or_coe (X r) with hb | ⟨cm, hb⟩
    · simp [timerefineF_apply, hb]
    · simp only [timerefineF_apply, hb, WithBot.map_coe]
      rw [timerefineA_iter2 h1 h2]

/-- The source's `timerefine_trans` (at `wfR''`, delta T7). -/
theorem timerefine_trans {R1 : κ' → ACost κ'' ℕ∞} {R2 : κ → ACost κ' ℕ∞} (h1 : wfR'' R1)
    (h2 : wfR'' R2) {a : NRest α (ACost κ'' ℕ∞)} {b : NRest α (ACost κ' ℕ∞)}
    {c : NRest α (ACost κ ℕ∞)} (hab : a ≤ timerefine R1 b) (hbc : b ≤ timerefine R2 c) :
    a ≤ timerefine (pp R1 R2) c := by
  rw [← timerefine_iter2 h1 h2]
  exact hab.trans (timerefine_mono h1 hbc)

/-! ### `⇓C` and the monadic operations -/

/-- The source's `timerefine_RETURNT`. -/
@[simp] theorem timerefine_returnT (E : κ → ACost κ' ℕ∞) (x : α) :
    timerefine E (returnT x : NRest α (ACost κ ℕ∞)) = returnT x := by
  show timerefine E (rest (single x (0 : WithBot (ACost κ ℕ∞))))
    = rest (single x (0 : WithBot (ACost κ' ℕ∞)))
  rw [timerefine_rest, rest_inj_iff]
  funext v
  by_cases h : v = x
  · subst h; simp [timerefineF_apply]
  · simp [timerefineF_apply, h]

/-- The source's `timerefine_SPECT_map`. -/
theorem timerefine_single (E : κ → ACost κ' ℕ∞) (x : α) (t : ACost κ ℕ∞) :
    timerefine E (rest (single x (t : WithBot (ACost κ ℕ∞))))
      = rest (single x ((timerefineA E t : ACost κ' ℕ∞) : WithBot (ACost κ' ℕ∞))) := by
  rw [timerefine_rest, rest_inj_iff]
  funext v
  by_cases h : v = x
  · subst h; simp [timerefineF_apply]
  · simp [timerefineF_apply, h]

/-- The source's `SPEC_timerefine_conv`. -/
theorem timerefine_spec (R : κ → ACost κ' ℕ∞) (A : α → Prop) (B : α → ACost κ ℕ∞) :
    timerefine R (spec A B) = spec A (fun x => timerefineA R (B x)) := by
  classical
  rw [spec, timerefine_rest, spec, rest_inj_iff]
  funext v
  by_cases h : A v <;> simp [timerefineF_apply, h]

/-- The source's `SPEC_timerefine`. -/
theorem spec_timerefine {R : κ → ACost κ' ℕ∞} {A A' : α → Prop} {B : α → ACost κ' ℕ∞}
    {B' : α → ACost κ ℕ∞} (hA : ∀ x, A x → A' x) (hB : ∀ x, B x ≤ timerefineA R (B' x)) :
    spec A B ≤ timerefine R (spec A' B') := by
  classical
  rw [timerefine_spec, spec, spec, rest_le_rest_iff]
  intro v
  by_cases h : A v
  · simp only [if_pos h, if_pos (hA v h), WithBot.coe_le_coe]
    exact hB v
  · simp [h]

/-- The source's `SPEC_timerefine_eq`. -/
theorem spec_timerefine_eq {R : κ → ACost κ' ℕ∞} {A : α → Prop} {B : α → ACost κ' ℕ∞}
    {B' : α → ACost κ ℕ∞} (hB : ∀ x, B x = timerefineA R (B' x)) :
    spec A B = timerefine R (spec A B') := by
  rw [timerefine_spec]
  congr 1
  funext x
  exact hB x

/-- The source's `timerefine_consume`. -/
theorem timerefine_consume {E : κ → ACost κ' ℕ∞} (hE : wfR'' E) (M : NRest α (ACost κ ℕ∞))
    (t : ACost κ ℕ∞) :
    timerefine E (consume M t) = consume (timerefine E M) (timerefineA E t) := by
  cases M with
  | fail => rfl
  | rest X =>
    rw [consume_rest', timerefine_rest, timerefine_rest, consume_rest', rest_inj_iff]
    funext r
    rcases withBot_eq_bot_or_coe (X r) with hb | ⟨cm, hb⟩
    · simp [timerefineF_apply, hb]
    · simp only [timerefineF_apply, hb, ← WithBot.coe_add, WithBot.map_coe]
      rw [timerefineA_add hE]

/-- `⇓C` and `consumeB`, the `WithBot`-costed form. -/
theorem timerefine_consumeB {E : κ → ACost κ' ℕ∞} (hE : wfR'' E) (M : NRest α (ACost κ ℕ∞))
    (u : WithBot (ACost κ ℕ∞)) :
    timerefine E (consumeB M u) = consumeB (timerefine E M) (WithBot.map (timerefineA E) u) := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · rw [consumeB_bot, WithBot.map_bot, consumeB_bot, bot_eq_rest_bot, timerefine_rest,
      bot_eq_rest_bot, rest_inj_iff]
    funext r
    simp [timerefineF_apply]
  · rw [consumeB_coe, WithBot.map_coe, consumeB_coe, timerefine_consume hE]

/-- The source's `timerefine_bindT_ge2`: repricing a bind is at least as
generous as binding the repriced pieces. The inequality direction is the
source's, and it is strict in general: `bindT` is a supremum and `⇓C` is
not supremum-continuous.

The source proves this through its `limRef`/`project_acost` machinery
(delta T7); here it follows from `timerefine_consume` and monotonicity
alone. -/
theorem timerefine_bindT_ge {β : Type} {R : κ → ACost κ' ℕ∞} (hR : wfR'' R)
    (m : NRest α (ACost κ ℕ∞)) (f : α → NRest β (ACost κ ℕ∞)) :
    bindT (timerefine R m) (fun x => timerefine R (f x)) ≤ timerefine R (bindT m f) := by
  cases m with
  | fail => simp
  | rest X =>
    rw [timerefine_rest, bindT_rest_eq_iSup, bindT_rest_eq_iSup]
    refine iSup_le fun x => ?_
    rw [timerefineF_apply, ← timerefine_consumeB hR]
    exact timerefine_mono hR (le_iSup (fun x => consumeB (f x) (X x)) x)

/-! ### The identity exchange rate `TId` -/

/-- The source's `TId`: every currency buys one of itself. -/
def TId [DecidableEq κ] [Zero γ] [One γ] : κ → ACost κ γ :=
  fun x => ⟨fun y => if x = y then 1 else 0⟩

@[simp] theorem toFun_TId [DecidableEq κ] [Zero γ] [One γ] (x y : κ) :
    (TId x : ACost κ γ).toFun y = if x = y then 1 else 0 := rfl

/-- The source's `TId_apply`. -/
theorem TId_apply [DecidableEq κ] [Zero γ] [One γ] (x : κ) :
    (TId x : ACost κ γ) = ACost.cost x 1 := by
  ext y
  rw [toFun_TId, ACost.toFun_cost]
  by_cases h : y = x
  · simp [h]
  · simp [h, Ne.symm h]

/-- The source's `wfR''_TId`. -/
@[simp] theorem wfR''_TId [DecidableEq κ] [Zero γ] [One γ] [NeZero (1 : γ)] :
    wfR'' (TId : κ → ACost κ γ) := by
  intro f
  refine (Set.finite_singleton f).subset fun s hs => ?_
  refine Set.mem_singleton_iff.mpr ?_
  by_contra hne
  exact hs (by simp [hne])

/-- The source's `"wfR' TId"`. -/
theorem wfR'_TId [DecidableEq κ] [Zero γ] [One γ] [NeZero (1 : γ)] :
    wfR' (TId : κ → ACost κ γ) := by
  intro s
  refine (Set.finite_singleton s).subset fun f hf => ?_
  refine Set.mem_singleton_iff.mpr ?_
  by_contra hne
  exact hf (by simp [show ¬ s = f from fun h => hne h.symm])

/-- The source's `timerefineA_TId_eq`. -/
@[simp] theorem timerefineA_TId [DecidableEq κ] (x : ACost κ ℕ∞) : timerefineA TId x = x := by
  ext cc
  rw [toFun_timerefineA, finsum_eq_single _ cc fun b hb => by simp [toFun_TId, hb]]
  simp

/-- The source's `timerefineA_TId`. -/
theorem le_timerefineA_TId [DecidableEq κ] {T T' : ACost κ ℕ∞} (h : T ≤ T') :
    T ≤ timerefineA TId T' := by rwa [timerefineA_TId]

/-- The source's `timerefine_id`. -/
@[simp] theorem timerefine_TId [DecidableEq κ] (M : NRest α (ACost κ ℕ∞)) :
    timerefine TId M = M := by
  cases M with
  | fail => rfl
  | rest X =>
    rw [timerefine_rest, rest_inj_iff]
    funext r
    rcases withBot_eq_bot_or_coe (X r) with hb | ⟨cm, hb⟩ <;> simp [timerefineF_apply, hb]

/-- The source's `timerefineA_cost`. -/
@[simp] theorem timerefineA_cost_one [DecidableEq κ] (TR : κ → ACost κ' ℕ∞) (n : κ) :
    timerefineA TR (ACost.cost n 1) = TR n := by
  ext cc
  rw [toFun_timerefineA, finsum_eq_single _ n fun b hb => by simp [ACost.toFun_cost_ne hb]]
  simp

/-- The source's `timerefineA_cost_apply`. -/
theorem timerefineA_cost [DecidableEq κ] (TR : κ → ACost κ' ℕ∞) (n : κ) (t : ℕ∞) :
    timerefineA TR (ACost.cost n t) = ⟨fun x => t * (TR n).toFun x⟩ := by
  ext cc
  rw [toFun_timerefineA, finsum_eq_single _ n fun b hb => by simp [ACost.toFun_cost_ne hb]]
  simp

/-- The source's `timerefineA_update_apply_same_cost`. -/
theorem timerefineA_update_cost_self [DecidableEq κ] (F : κ → ACost κ' ℕ∞) (n : κ)
    (y : ACost κ' ℕ∞) (t : ℕ∞) :
    timerefineA (Function.update F n y) (ACost.cost n t) = ⟨fun x => t * y.toFun x⟩ := by
  rw [timerefineA_cost, Function.update_self]

/-- The source's `timerefineA_update_cost`. -/
@[simp] theorem timerefineA_update_cost_ne [DecidableEq κ] {F : κ → ACost κ' ℕ∞} {n m : κ}
    (h : n ≠ m) (y : ACost κ' ℕ∞) (t : ℕ∞) :
    timerefineA (Function.update F n y) (ACost.cost m t) = timerefineA F (ACost.cost m t) := by
  rw [timerefineA_cost, timerefineA_cost, Function.update_of_ne (Ne.symm h)]

/-- The source's `pp_TId_absorbs_right`. -/
@[simp] theorem pp_TId_right [DecidableEq κ] (A : κ → ACost κ' ℕ∞) : pp A TId = A := by
  funext a
  rw [pp_apply, TId_apply, timerefineA_cost_one]

/-- The source's `pp_TId_absorbs_left`. -/
@[simp] theorem pp_TId_left [DecidableEq κ'] (A : κ → ACost κ' ℕ∞) : pp TId A = A := by
  funext a
  rw [pp_apply, timerefineA_TId]

/-! ### Structure preservation and currency preservation

Stated where the source states them: at `String` currencies over `ℕ∞`,
i.e. at `ECost` (design record F1, delta T3). -/

/-- The source's `struct_preserving`. -/
def StructPreserving (E : String → ECost) : Prop :=
  (∀ t, ACost.cost "call" t ≤ timerefineA E (ACost.cost "call" t)) ∧
    (∀ t, ACost.cost "if" t ≤ timerefineA E (ACost.cost "if" t))

/-- The source's `struct_preservingI`. -/
theorem structPreserving_of {E : String → ECost}
    (h1 : ∀ t, ACost.cost "call" t ≤ timerefineA E (ACost.cost "call" t))
    (h2 : ∀ t, ACost.cost "if" t ≤ timerefineA E (ACost.cost "if" t)) :
    StructPreserving E := ⟨h1, h2⟩

/-- The source's `struct_preservingD`, first clause. -/
theorem StructPreserving.call {E : String → ECost} (h : StructPreserving E) (t : ℕ∞) :
    ACost.cost "call" t ≤ timerefineA E (ACost.cost "call" t) := h.1 t

/-- The source's `struct_preservingD`, second clause. -/
theorem StructPreserving.if_ {E : String → ECost} (h : StructPreserving E) (t : ℕ∞) :
    ACost.cost "if" t ≤ timerefineA E (ACost.cost "if" t) := h.2 t

/-- The source's `struct_preserving_upd_I`. -/
theorem StructPreserving.update {E : String → ECost} (h : StructPreserving E) {x : String}
    (hif : x ≠ "if") (hcall : x ≠ "call") (y : ECost) :
    StructPreserving (Function.update E x y) :=
  ⟨fun t => by rw [timerefineA_update_cost_ne (Ne.symm hcall).symm]; exact h.1 t,
   fun t => by rw [timerefineA_update_cost_ne (Ne.symm hif).symm]; exact h.2 t⟩

/-- The source's `sp_TId`. -/
@[simp] theorem structPreserving_TId : StructPreserving TId :=
  ⟨fun t => by rw [timerefineA_TId], fun t => by rw [timerefineA_TId]⟩

/-- The source's `preserves_curr`. -/
def PreservesCurr [DecidableEq κ] (R : κ → ACost κ ℕ∞) (n : κ) : Prop :=
  R n = ACost.cost n 1

/-- The source's `preserves_curr_D`. -/
theorem PreservesCurr.eq [DecidableEq κ] {R : κ → ACost κ ℕ∞} {n : κ} (h : PreservesCurr R n) :
    R n = ACost.cost n 1 := h

/-- The source's `preserves_curr_other_updI`. -/
theorem PreservesCurr.update [DecidableEq κ] {R : κ → ACost κ ℕ∞} {n m : κ}
    (h : PreservesCurr R m) (hnm : n ≠ m) (t : ACost κ ℕ∞) :
    PreservesCurr (Function.update R n t) m := by
  rw [PreservesCurr, Function.update_of_ne (Ne.symm hnm)]
  exact h

/-- The source's `preserves_curr_TId`. -/
@[simp] theorem preservesCurr_TId [DecidableEq κ] (n : κ) : PreservesCurr TId n := TId_apply n

/-- The source's `cost_n_leq_TId_n`. -/
theorem cost_le_TId [DecidableEq κ] (n : κ) : ACost.cost n (1 : ℕ∞) ≤ (TId n : ACost κ ℕ∞) :=
  le_of_eq (TId_apply n).symm

/-! ### `⇓C` against `⇓R` (delta T6) -/

/-- `WithBot.map` of a monotone function is monotone. -/
theorem withBot_map_mono {A B : Type} [Preorder A] [Preorder B] {f : A → B}
    (hf : Monotone f) {u v : WithBot A} (h : u ≤ v) : WithBot.map f u ≤ WithBot.map f v := by
  induction u using WithBot.recBotCoe with
  | bot => simp
  | coe a =>
    induction v using WithBot.recBotCoe with
    | bot => simp at h
    | coe b => simpa using hf (WithBot.coe_le_coe.mp h)

/-- The source's `timerefine_conc_fun_ge2` (`NREST_Main.thy`, delta T6):
concretising and then repricing is at least as generous as repricing and
then concretising. -/
theorem concFun_timerefine_le {β : Type} {E : κ → ACost κ' ℕ∞} (hE : wfR'' E)
    (R : Set (β × α)) (C : NRest α (ACost κ ℕ∞)) :
    concFun R (timerefine E C) ≤ timerefine E (concFun R C) := by
  cases C with
  | fail => simp
  | rest X =>
    rw [timerefine_rest, concFun_rest_eq, concFun_rest_eq, timerefine_rest, rest_le_rest_iff]
    intro c
    rw [concMap_apply, timerefineF_apply, concMap_apply]
    refine iSup_le fun a => iSup_le fun ha => ?_
    exact withBot_map_mono (fun _ _ h => timerefineA_mono hE h)
      (le_iSup_of_le a (le_iSup_of_le ha le_rfl))

end NRest

/-! ### The executable gate (design record ledger D4)

`timerefineA` is a `∑ᶠ`, and over a finite currency type that sum is a
plain finite sum, so it has an executable twin with a proved agreement
theorem. The gate carrier is two currencies (`Fin 2`), costs in `ℕ∞`,
three results (`Fin 3`); note that over a finite currency type `wfR''`
holds for every exchange rate, so the side conditions of the laws below
are discharged by `Set.toFinite` and the checks really are about the
laws. -/

namespace Sanity

open NRest

/-- The gate's currency type: two currencies. -/
abbrev SCur := ACost (Fin 2) ℕ∞

/-- The gate's exchange rates. -/
abbrev SRate := Fin 2 → SCur

/-- Programs over three results, paying in two currencies. -/
abbrev SRestC := NRest (Fin 3) SCur

/-- Equality of costs over two currencies is decidable. -/
instance instDecidableEqSCur : DecidableEq SCur := fun a b =>
  decidable_of_iff (∀ k, a.toFun k = b.toFun k) ⟨fun h => ACost.ext (funext h), fun h _ => by
    rw [h]⟩

/-- And so is equality of programs over them. -/
instance instDecidableEqSRestC : DecidableEq SRestC := fun m n =>
  match m, n with
  | .fail, .fail => isTrue rfl
  | .fail, .rest _ => isFalse (by simp)
  | .rest _, .fail => isFalse (by simp)
  | .rest X, .rest Y => decidable_of_iff (∀ i, X i = Y i)
      ⟨fun h => by rw [funext h], fun h i => by rw [NRest.rest_inj_iff.mp h]⟩

/-- The cost order is decidable, currency by currency. -/
instance instDecidableLESCur : DecidableLE SCur := fun a b =>
  decidable_of_iff (∀ k, a.toFun k ≤ b.toFun k) ACost.le_def.symm

/-- And so is the program order, by the three clauses of
`less_eq_nrest`. -/
instance instDecidableLESRestC : DecidableLE SRestC := fun m n =>
  match m, n with
  | _, .fail => isTrue (NRest.le_fail _)
  | .fail, .rest _ => isFalse (by simp)
  | .rest X, .rest Y => decidable_of_iff (∀ i, X i ≤ Y i) (by simp [Pi.le_def])

/-- A decidable "`R` is pointwise below `S`" for rates. -/
def rateLeE (R S : SRate) : Bool := decide (∀ k : Fin 2, R k ≤ S k)

/-- The executable rate order agrees with `≤`. -/
theorem rateLeE_eq (R S : SRate) : rateLeE R S = true ↔ R ≤ S := by
  simp only [rateLeE, decide_eq_true_eq]
  exact ⟨fun h k => h k, fun h k => h k⟩

/-- Over a finite currency type every exchange rate is well formed. -/
theorem wfR''_of_finite (R : SRate) : wfR'' R := fun _ => Set.toFinite _

/-- Executable `timerefineA`: the `∑ᶠ` over `Fin 2`, written out. -/
def timerefineAE (R : SRate) (cm : SCur) : SCur :=
  ⟨fun cc => cm.toFun 0 * (R 0).toFun cc + cm.toFun 1 * (R 1).toFun cc⟩

/-- **The bridge.** Everything checked below is checked about
`timerefineA`. -/
theorem timerefineAE_eq (R : SRate) (cm : SCur) : timerefineAE R cm = timerefineA R cm := by
  ext cc
  rw [toFun_timerefineA,
    finsum_eq_sum_of_support_subset _ (s := Finset.univ) (by intro x _; simp),
    Fin.sum_univ_two]
  rfl

/-- Executable `timerefine`. -/
def timerefineE (R : SRate) (m : SRestC) : SRestC :=
  match m with
  | .fail => .fail
  | .rest M => .rest (fun r => WithBot.map (timerefineAE R) (M r))

@[simp] theorem timerefineE_fail (R : SRate) : timerefineE R .fail = .fail := rfl

@[simp] theorem timerefineE_rest (R : SRate) (M : Fin 3 → WithBot SCur) :
    timerefineE R (.rest M) = .rest (fun r => WithBot.map (timerefineAE R) (M r)) := rfl

/-- **The bridge**, at the program level. -/
theorem timerefineE_eq (R : SRate) (m : SRestC) : timerefineE R m = timerefine R m := by
  cases m with
  | fail => rfl
  | rest M =>
    rw [timerefineE, timerefine_rest, NRest.rest_inj_iff]
    funext r
    rw [timerefineF_apply]
    congr 1
    funext cm
    exact timerefineAE_eq R cm

/-- Executable `pp`. -/
def ppE (A B : SRate) : SRate := fun a => timerefineAE A (B a)

/-- The executable rate composition agrees with `pp`. -/
theorem ppE_eq (A B : SRate) : ppE A B = pp A B := by
  funext a
  rw [ppE, timerefineAE_eq, pp_apply]

/-- The identity rate, executably. -/
def TIdE : SRate := fun x => ⟨fun y => if x = y then 1 else 0⟩

/-- The executable identity rate *is* `TId`. -/
theorem TIdE_eq : TIdE = (TId : SRate) := rfl

/-- A sample cost: two of currency `0`, three of currency `1`. -/
def c23 : SCur := ⟨![2, 3]⟩

/-- A second sample cost: one of currency `0`, none of currency `1`. -/
def c10 : SCur := ⟨![1, 0]⟩

/-- An exchange rate that prices currency `0` at two of currency `1`,
and currency `1` at one of each. -/
def rate1 : SRate := ![⟨![0, 2]⟩, ⟨![1, 1]⟩]

/-- A second exchange rate. -/
def rate2 : SRate := ![⟨![3, 0]⟩, ⟨![0, 1]⟩]

/-! #### Spot checks -/

-- `timerefineA_TId_eq`: the identity rate reprices nothing.
#guard timerefineAE TIdE c23 = c23
#guard timerefineAE TIdE c10 = c10

-- `timerefineA_0`
#guard timerefineAE rate1 0 = 0

-- repricing by hand: `2` of currency 0 at `⟨0,2⟩` plus `3` of
-- currency 1 at `⟨1,1⟩` is `⟨3, 7⟩`.
#guard timerefineAE rate1 c23 = ⟨![3, 7]⟩

-- `timerefineA_cost`: `cost n t` is repriced to `t * R n`.
#guard timerefineAE rate1 (ACost.cost 0 (5 : ℕ∞)) = ⟨![0, 10]⟩
#guard timerefineAE rate1 (ACost.cost 1 (1 : ℕ∞)) = rate1 1

-- `timerefineA_propagate`
#guard timerefineAE rate1 (c23 + c10) = timerefineAE rate1 c23 + timerefineAE rate1 c10

-- `timerefineA_iter2` / `pp`
#guard timerefineAE rate1 (timerefineAE rate2 c23) = timerefineAE (ppE rate1 rate2) c23

-- `pp_TId_absorbs_left/right`
#guard ppE rate1 TIdE = rate1
#guard ppE TIdE rate1 = rate1

-- `timerefine_id` and `nofailT_timerefine`, on a program
#guard timerefineE TIdE (.rest ![(c23 : WithBot SCur), ⊥, (c10 : WithBot SCur)])
  = (.rest ![(c23 : WithBot SCur), ⊥, (c10 : WithBot SCur)] : SRestC)
#guard timerefineE rate1 (NRest.fail : SRestC) = (NRest.fail : SRestC)
#guard timerefineE rate1 (.rest ![(c23 : WithBot SCur), ⊥, ⊥])
  = (.rest ![((⟨![3, 7]⟩ : SCur) : WithBot SCur), ⊥, ⊥] : SRestC)

/-! #### Property checks -/

open Plausible

/-- Sampling proxy for costs over two currencies. -/
instance instSampleableExtSCur : SampleableExt SCur where
  proxy := ℕ × ℕ
  sample := inferInstance
  interp := fun p => ⟨![(p.1 : ℕ∞), (p.2 : ℕ∞)]⟩

/-- Sampling proxy for exchange rates. -/
instance instSampleableExtSRate : SampleableExt SRate where
  proxy := (ℕ × ℕ) × (ℕ × ℕ)
  sample := inferInstance
  interp := fun p => ![⟨![(p.1.1 : ℕ∞), (p.1.2 : ℕ∞)]⟩, ⟨![(p.2.1 : ℕ∞), (p.2.2 : ℕ∞)]⟩]

/-- Sampling proxy for programs over two currencies. -/
instance instSampleableExtSRestC : SampleableExt SRestC where
  proxy := Option (List (ℕ × (ℕ × ℕ)))
  sample := inferInstance
  interp := fun
    | none => .fail
    | some l => .rest (l.foldr (fun p X => Function.update X (mk3 p.1)
        ((⟨![(p.2.1 : ℕ∞), (p.2.2 : ℕ∞)]⟩ : SCur) : WithBot SCur)) (fun _ => ⊥))

-- `timerefineA_0`
#test ∀ R : SRate, timerefineAE R 0 = 0

-- `timerefineA_propagate`
#test ∀ (R : SRate) (a b : SCur), timerefineAE R (a + b) = timerefineAE R a + timerefineAE R b

-- `timerefineA` is monotone in the cost, and in the rate.
#test ∀ (R : SRate) (a b : SCur), a ≤ b → timerefineAE R a ≤ timerefineAE R b
#test ∀ (R S : SRate) (a : SCur), rateLeE R S = true → timerefineAE R a ≤ timerefineAE S a

-- `timerefineA_iter2`: repricing twice is repricing at `pp`.
#test ∀ (A B : SRate) (c : SCur), timerefineAE A (timerefineAE B c) = timerefineAE (ppE A B) c

-- `pp_assoc`
#test ∀ (A B C : SRate) (x : Fin 2), ppE A (ppE B C) x = ppE (ppE A B) C x

-- `timerefineA_TId_eq`, `pp_TId_absorbs_*`
#test ∀ c : SCur, timerefineAE TIdE c = c
#test ∀ (A : SRate) (x : Fin 2), ppE A TIdE x = A x ∧ ppE TIdE A x = A x

-- `timerefine_id`, `timerefine_mono2`, `timerefine_iter2` on programs.
#test ∀ M : SRestC, timerefineE TIdE M = M
#test ∀ (R : SRate) (M N : SRestC), M ≤ N → timerefineE R M ≤ timerefineE R N
#test ∀ (A B : SRate) (M : SRestC),
  timerefineE A (timerefineE B M) = timerefineE (ppE A B) M

-- `timerefine_consume`
#test ∀ (R : SRate) (M : SRestC) (t : SCur),
  timerefineE R (NRest.consume M t) = NRest.consume (timerefineE R M) (timerefineAE R t)

end Sanity

end Lax13Proofs.Refine
