import Lax13Proofs.Refine.NREST.Combinators
import Lax13Proofs.Refine.NREST.TimeRefinement

/-!
Backwards reasoning for `NREST`: the `gwp` predicate transformer and the
seed of the abstract VCG.

Port of `thys/nrest/NREST_Backwards_Reasoning.thy` and
`thys/nrest/NREST_Type_Classes.thy` of `isabelle_llvm_time`
(Haslbeck–Lammich, ESOP'21 artifact) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1,
github.com/lammich/isabelle_llvm_time @ 42dd7f5, together with
`lift_acost` from `thys/cost/Enat_Cost.thy` and the `RECT` induction
principles of `thys/nrest/NREST.thy` that `Rec.lean` deferred to this
file. `thys/nrest/NREST_Automation.thy` was read for the automation
architecture (`Named_Thms` `refine_vcg` / `refine_vcg_cons` / `refine0`
/ `refine` / `refine2`, and `refine_rcg`); its `sc_solve` cost-side-
condition solver and its normalisation lemma collections are P2 material
and are not ported here. Everything fetched 2026-07-29 from the pins.

## The source, verbatim

`NREST_Type_Classes.thy` (also quoted in
`plans/word-ram/refinement-tower/source-extracts.md`):

```isabelle
class nonneg = ord + zero +
  assumes needname_nonneg: "0 ≤ x"

class needname = complete_lattice + minus + plus +
  assumes top_absorb: "⋀a. top - a = top"
      and minus_plus_assoc2: "⋀a b c. a - (b + c) = a - c - b"
      and le_diff_if_add_le: "⋀a b c. ⟦a + b ≤ c; b ≤ c⟧ ⟹ a ≤ c - b"
      and add_leD2: "⋀a b c. a + b ≤ c ⟹ b ≤ c"
      and add_le_if_le_diff: "⋀t1 a aa b. ⟦t1 ≤ b - a; aa ≤ b - a - t1; a ≤ b⟧ ⟹ t1 + a ≤ b"
lemma needname_cancle: "t1 + t2 ≤ t ⟹ t2 ≤ t"
lemma needname_adjoint: "a + b ≤ c ⟹ a ≤ c - b"

class drm = minus + plus + ord + Inf + Sup +
  assumes diff_right_mono: "a ≤ b ⟹ a - c ≤ b - c"
  and diff_left_mono: "⋀a b c. b ≤ c ⟹ a - c ≤ a - b"
  and minus_continuousInf: "R≠{} ⟹ (INF r∈R. r - mt) ≤ Inf R - mt"
  and minus_continuousSup: "⋀X t q. X≠{} ⟹ ∀x∈X. t ≤ q - (x::'a) ⟹ t ≤ q - (Sup X)"
  and plus_left_mono: "a ≤ b ⟹ c + a ≤ c + b"

class needname_zero = needname + nonneg + drm + ordered_comm_monoid_add + mult_zero +
  assumes needname_minus_absorb: "x - 0 = x"
   and needname_plus_absorb: "0 + x = x"

instance enat :: needname          instantiation acost :: (type, needname) needname
instance enat :: drm               instantiation acost :: (type, needname_zero) needname_zero
instance enat :: needname_zero     definition "a*b = acostC (λx. the_acost a x * the_acost b x)"
```

`NREST_Backwards_Reasoning.thy`:

```isabelle
definition mm3 where
  "mm3 t A = (case A of None ⇒ None | Some t' ⇒ if t'≤t then Some (t-t') else None)"

definition minus_potential :: "('a ⇒ ('d::{minus,ord,top}) option) ⇒ ('a ⇒ 'd option) ⇒ ('a ⇒ 'd option)"
  where "minus_potential R m = (λx. (case m x of None ⇒ Some top
                                | Some mt ⇒ (case R x of None ⇒ None
                                             | Some rt ⇒ (if mt ≤ rt then Some (rt - mt) else None))))"
definition minus_cost :: "(('d::{minus,ord,top}) option) ⇒ (_ option) ⇒ (_ option)" where
  "minus_cost r m = (case m of None ⇒ Some top | Some mt ⇒
        (case r of None ⇒ None | Some rt ⇒ (if mt ≤ rt then Some (rt - mt) else None)))"
lemma minus_potential_alt: "minus_potential r m = (λx. minus_cost (r x) (m x))"
lemma minus_cost_None: "minus_cost r None = Some top"
lemma minus_cost_mono:     "(m ≠ None ⟹ q' ≤ q) ⟹ minus_cost q m ≥ minus_cost q' m"
lemma minus_cost_antimono: "x ≤ y ⟹ minus_cost q x ≥ minus_cost q y"
lemma minus_cost_contiuous2: "∀x∈X. t ≤ minus_cost q x ⟹ t ≤ minus_cost q (Sup X)"
lemma mm_continousInf': "R≠{} ⟹ minus_cost (Inf R) m = Inf ((λr. minus_cost r m)`R)"

definition minus_p_m :: "('a ⇒ ('b::{minus,complete_lattice,monoid_add}) option) ⇒ ('a,'b) nrest ⇒ 'a ⇒ 'b option"
  where "minus_p_m Qf M x = (case M of FAILi ⇒ None | REST Mf ⇒ (minus_potential Qf Mf) x)"
lemma minus_p_m_Failt: "minus_p_m Q FAILT x = None"
lemma minus_p_m_mono / minus_p_m_antimono / minus_p_m_continuousInf / minus_p_m_continuous
lemma minus_p_m_bindT:
  "(t ≤ minus_p_m Q (bindT m f) x) ⟷ (∀y. t ≤ minus_p_m (λy. minus_p_m Q (f y) x) m y)"

definition gwp :: "('a,'b) nrest ⇒ ('a ⇒ ('b::{complete_lattice,minus,ord,top,drm,monoid_add}) option) ⇒ 'b option"
  where "gwp M Qf = Inf { minus_p_m Qf M x | x. True}"
definition "gwp⇩n m Q ≡ (if nofailT m then gwp m Q else Some top)"
lemma gwp_FAILT[simp]: "gwp FAILT Q = None"
lemma gwp_mono / gwp_antimono
lemma gwp_pw: "gwp M Q ≥ t ⟷ (∀x. minus_p_m Q M x ≥ t)"
lemma gwp_specifies_I:     "gwp m Q ≥ Some 0 ⟹ (m ≤ SPECT Q)"
lemma gwp_specifies_rev_I: "(m ≤ SPECT Q) ⟹ gwp m Q ≥ Some 0"
lemma gwp_specifies_time_I: "gwp m (timerefineF E Q) ≥ Some 0 ⟹ (m ≤ timerefine E (SPECT Q))"
definition nres3 where "nres3 Q M x t ⟷ minus_p_m Q M x ≥ t"
lemma pw_gwp_le / pw_gwp_eqI
lemma gwp_bindT: "gwp (bindT M f) Q = gwp M (λy. gwp (f y) Q)"   (* only need ≥ *)

definition "progress m ≡ ∀s' M. m = SPECT M ⟶ M s' ≠ None ⟶ M s' > Some 0"
lemma progressD / progress_REST_iff / progress_SPECT_emb / progress_ASSERT_bind / progress_bind

named_theorems vcg_rules'
lemma gwp_bindT_I[vcg_rules']:      "Some t ≤ gwp M (λy. gwp (f y) Q) ⟹ Some t ≤ gwp (M ⤜ f) Q"
lemma gwp_SPECT_emb_I[vcg_rules']:  "(⋀x. X x ⟹ Some (t' + t x) ≤ Q x) ⟹ Some t' ≤ gwp (SPECT (emb' X t)) Q"
lemma gwp_consume[vcg_rules']:      "Some (T+t) ≤ gwp m Q ⟹ Some t ≤ gwp (consume m T) Q"
lemma gwp_RETURNT_I[vcg_rules']:    "t ≤ Q x ⟹ t ≤ gwp (RETURNT x) Q"
lemma gwp_SPECT_I[vcg_rules']:      "Some (t' + t) ≤ Q x ⟹ Some t' ≤ gwp (SPECT [x ↦ t]) Q"
lemma gwp_If_I[vcg_rules']:  "(b ⟹ t ≤ gwp Ma Q) ⟹ (¬b ⟹ t ≤ gwp Mb Q) ⟹ t ≤ gwp (if b then Ma else Mb) Q"
lemma gwp_MIf_I[vcg_rules']: "(b ⟹ Some (cost ''if'' 1 + t) ≤ gwp c1 Q) ⟹
                              (¬b ⟹ Some (cost ''if'' 1 + t) ≤ gwp c2 Q) ⟹ Some t ≤ gwp (MIf b c1 c2) Q"
lemma gwp_ASSERT_I[vcg_rules']:      "(Φ ⟹ Some t ≤ Q ()) ⟹ Φ ⟹ Some t ≤ gwp (ASSERT Φ) Q"
lemma gwp_ASSERT_bind_I[vcg_rules']: "(Φ ⟹ Some t ≤ gwp M Q) ⟹ Φ ⟹ Some t ≤ gwp (do {ASSERT Φ; M}) Q"

lemma gwp_conseq_aux1: "Some t ≤ minus_cost Q (Some t') ⟷ Some (t+t') ≤ Q"
lemma gwp_conseq_0 / gwp_conseq / gwp_conseq4 (+ gwp_conseq4_aux2, gwp_conseq4_aux3)

lemma gwp_whileT_rule_wf:
  assumes "whileT b c s = r"
  assumes IS: "⋀s t'. I s = Some t' ⟹ b s ⟹ Some t' ≤ gwp (c s) (λs'. if (s',s)∈R then I s' else None)"
  assumes "I s = Some t"  assumes wf: "wf R"
  shows "gwp r (λx. if b x then None else I x) ≥ Some t"
definition ffSacost where "ffSacost f = {(s,s')| s s'. the_acost (f s) < the_acost (f s')}"
lemma wf_ffSacost: "(⋀s. finite {x. the_acost (f s) x ≠ 0}) ⟹ wf (ffSacost f)"
lemma While[vcg_rules']:
  assumes "⋀s. wfR2 (if I s then E s else 0)"
  assumes "I s0"
     "(⋀s. I s ⟹ b s ⟹ Some 0 ≤ gwp (C s) (λs'. mm3 (lift_acost (E s))
                                          (if I s' then Some (lift_acost (E s')) else None)))"
     "(⋀s. progress (C s))"
     "(⋀x. ¬ b x ⟹ I x ⟹ (E x) ≤ (E s0) ⟹ Some (t + lift_acost ((E s0) - E x)) ≤ Q x)"
  shows "Some t ≤ gwp (whileIET I E b C s0) Q"
```

`NREST.thy` (the `RECT` induction principles `Rec.lean` deferred here):

```isabelle
lemma wf_fp_induct:
  assumes fp: "⋀x. f x = B (f) x"  assumes wf: "wf R"
  assumes "⋀x D. ⟦⋀y. (y,x)∈R ⟹ P y (D y)⟧ ⟹ P x (B D x)"
  shows "P x (f x)"
lemma RECT_wf_induct_aux:
  assumes wf: "wf R"  assumes mono: "mono2 B"
  assumes "(⋀x D. (⋀y. (y, x) ∈ R ⟹ P y (D y)) ⟹ P x (B D x))"
  shows "P x (RECT B x)"
```

`Enat_Cost.thy`: `definition "lift_acost c ≡ acostC (enat o the_acost c)"`.

## Substrate deltas, each flagged

**B1 — the source's `minus` is not mathlib's `Sub`, and the difference
is load-bearing.** Isabelle's `enat` subtraction is
`a - b = (case a of enat x ⇒ (case b of enat y ⇒ enat (x-y) | ∞ ⇒ 0) | ∞ ⇒ ∞)`,
so `∞ - ∞ = ∞`; mathlib's `Sub ℕ∞` is truncated subtraction, so
`⊤ - ⊤ = 0` (checked by `#guard` in the gate below). The `needname`
axiom `top_absorb : top - a = top` is exactly this point, and the whole
`gwp` theory rests on it. **Under mathlib's `-` the ported
`minus_p_m_bindT` is false**: take `α = β = Unit`, `m = REST [() ↦ ⊤]`,
`f () = REST (λ_. None)`; then `bindT m f = REST (λ_. None)` so the
left-hand side is `t ≤ Some ⊤`, always true, while the right-hand side
is `t ≤ minus_cost (Some ⊤) (Some ⊤) = Some (⊤ - ⊤) = Some 0`, false for
`t = Some 1`. HOL's `minus` is its own type class; ours is `ResSub`,
written `-ᵣ`, and mathlib's `Sub` is left alone. This is a *refutation
found while porting*, and it is the one place where taking mathlib's
"obvious" operation would have silently broken the calculus.

**B2 — resolved: the cost-carrier material moved to `ACost.lean`.** The
source's `minus_acost_alt` and the `times_acost_def` of its
`acost :: needname_zero` instantiation belong beside the other pointwise
operations, but `ACost.lean` was frozen for P1's third slice, so
`ResSub` itself, `ACost.instResSub`, `ACost.instSub`, `ACost.instMul`
and `ACost.toFun_iInf` were declared here. **P2 wave A moved them up to
`Cost/ACost.lean`**, names, statements and proofs unchanged, together
with the `-ᵣ` notation, the `ℕ∞` instance, the `enat_resSub_*` lemmas
and the four `#guard`s recording delta B1's counterexample. This file
uses them all through its existing import chain; nothing stated here
changed. What stays is what `NREST_Type_Classes.thy` puts here: the
classes `Nonneg` / `Needname` / `Drm` / `NeednameZero` and their `enat`
and `acost` instances.

**B3 — HOL sort constraints become instance parameters.** HOL bundles
the operations into the class (`class needname = complete_lattice +
minus + plus + …`); Lean takes them as instance arguments
(`class Needname (γ) [CompleteLattice γ] [ResSub γ] [Add γ]`). This is
the adaptation `Basic.lean` already made for `nrest`'s sort constraints,
and it is the smallest one that works: the assumption *lists* are the
source's, one field per assumption, under the source's names. Two
assumptions could not be restated as fields:
`ordered_comm_monoid_add` is mathlib's `AddCommMonoid` + `PartialOrder`
+ `IsOrderedAddMonoid` (the bundled class was retired) and it already
*proves* `needname_plus_absorb : 0 + x = x`, so that assumption is a
theorem here; and `mult_zero` would be mathlib's `MulZeroClass`, which
bundles its own `Zero` and would diamond with `AddCommMonoid`'s, so its
two axioms are fields of `NeednameZero` instead.

**B4 — definitions carry `CompleteLattice γ` + `ResSub γ` throughout.**
The source gives `minus_cost` the finer sort `{minus, ord, top}` and
adds `complete_lattice` per lemma. `WithBot γ`'s order is only a lattice
at complete-lattice strength, and every use in the tower is at one, so
the finer gradation buys nothing here and is not reproduced.

**B5 — nonemptiness side conditions.** HOL types are nonempty by
construction; Lean's need not be. Three ported statements are false at
an empty result type and carry `[Nonempty _]`: `gwp_FAILT` (`gwp FAILT Q`
is `⨅ x : α, ⊥`, which is `⊤` when `α` is empty), `gwp_specifies_I`, and
`minus_p_m_bindT` — hence `gwp_bindT`, which needs both result types
nonempty, and `minusPM_iInf`, which needs the index type nonempty. The
`≥` half of the bind rule that the VCG actually uses (`le_gwp_bindT`,
`gwp_bindT_I`) needs only the *bound* computation's type.

**B6 — the loop-rule chain is shortened.** The source reaches its
`[vcg_rules']` entry `While` through `whileT_rule'''` → `whileIET_rule`
→ `whileIET_rule'`, each a repackaging of the previous one under a
different spelling of the invariant, with `gwp_conseq4` applied twice.
`While` here is derived from `gwp_whileT_rule_wf` directly, at the
invariant-plus-energy instantiation
`Iw s = (if I s ∧ E s ≤ E s0 then Some (t + lift_acost (E s0 - E s)) else None)`,
which is the composite of the source's three steps. The endpoints —
`gwp_whileT_rule_wf` and `While` — are stated exactly as the source
states them; only the intermediate spellings are absent. `gwp_conseq4`
*is* ported (with its `aux2`/`aux3`), because it is a citable
consequence rule in its own right.

**B7 — the attribute cannot be used in the module that declares it.**
Lean runs `initialize` blocks at *import* time, so `@[refine_vcg]` is
unavailable to this file. The ported rules therefore sit in
`RefineVcg.coreRules`, a list the tactic tries first, and
`@[refine_vcg]` extends that set from downstream modules — which is
where P2–P6's rules will live anyway. Isabelle's `named_theorems` has no
such restriction; this is a pure substrate cost, recorded rather than
worked around.

Inherited from the earlier slices and used unchanged: **F6** (result
maps are `α → WithBot γ`, so `Some t` reads `(t : WithBot γ)`, `None`
reads `⊥` and `Some top` reads `((⊤ : γ) : WithBot γ)`, which is
`WithBot γ`'s own `⊤`), **F1** (currency names are `String`), **C1**
(loop and branch conditions are `Bool`, so the source's `b` / `¬b`
premises read `b = true` / `b = false`).

## What is *not* ported, and why

* `gwp_SELECT_I` and `progress_SELECT_iff`: `SELECT` is not in the
  frozen `Basic.lean`/`Combinators.lean` API.
* The `monadic_WHILEIET` chain — `monadic_WHILE_rule''`,
  `monadic_WHILE_rule_real`, `neueWhile_rule''`,
  `neueWhile_rule''_real`, `gwp_monadic_WHILEIET`, and their vocabulary
  `Someplus` / `mm22` / `loopbody_cond` / `loopexit_cond` /
  `loop_body_condition` / `loop_exit_condition`. That chain is the loop
  rule for `monadic_WHILEIT` (a loop whose *condition* is itself a
  costed computation); the `whileIET` rule ported here is the one the P1
  acceptance program needs, and the monadic-condition variant follows
  the same argument with `MIf` in the middle. Deferred to the consumer
  that needs it.
* `progress_bind` and `progress_SELECT_iff` from the progress suite;
  `progress_REST_iff`, `progress_SPECT_emb` and `progress_ASSERT_bind`
  are ported, plus `progress_consume_returnT`, which is what loop bodies
  in the `consume`-of-`RETURNT` shape need.
* The `gwp⇩n` rule suite (`gwpn_bindT_I`, `gwpn_MIf_I`,
  `gwpn_monadic_WHILEIET`, …): `gwpn` itself and `gwpn_FAIL` are here,
  the rules wait for a consumer. They are `gwp` rules plus a
  `nofailT` bookkeeping layer.
* The `inres` section (`inres`, `nofailT_bindT`, `gwp_mono_alt`, …):
  `Pw.lean` already carries `nofailT`/`inresT` and
  `pw_bindT_nofailT`; `inres` is the `t`-free projection of `inresT` and
  belongs beside them when it is ported. P1 ported *none* of that
  section, so P2 wave A's relocation pass found nothing to move: the
  `t`-free projection still awaits a port from the source text (whose
  statements are not in either extract file), and when it lands it lands
  in `Pw.lean`, not here.
* `VCG_Case_Splitter` (the ML case splitter) and `NREST_Automation`'s
  `sc_solve` / `norm_cost` / `norm_pp`: automation, P2 material.

## Tactic maturity (stated honestly, per the campaign brief)

`refine_vcg` is a *seed*, not the source's method. What it does: peel
syntactic binders, then apply the first rule of `RefineVcg.coreRules`
(the ported `[vcg_rules']` set, most specific first) or of the
`@[refine_vcg]` database whose conclusion matches, repeat over all
goals, and leave everything else as a goal. That is enough to drive a
`whileIET` program with a `consume`/`RETURNT`/`bindT`/`MIf`/`ASSERT`
body from `gwp_specifies_I` down to arithmetic side conditions — which
is what the demo at the bottom of this file exercises end to end.

What it does *not* do, all of which the source's `refine_vcg` does:
no DiscrTree indexing (rules are tried in list order, so the cost is
linear in the rule set — fine at ten rules, not at a hundred); no
`refine_vcg_split_case` (a goal about `gwp (case x of …) Q` is not split
on `x`); no `progress` prover (the `progress` side condition is left to
the user, where the source's `method progress` discharges it); no
side-condition solver (`sc_solve`) for the cost inequalities, which are
the bulk of what is left over; no `rules:` argument for ad-hoc rules at
the call site; no consequence-rule stage (`refine_vcg_cons`). Closing
those gaps is P2's `Autoref/Solver.lean` work (design record §3, ledger
D1), and the rule *format* here is already the one that work consumes.

## The executable gate

Ledger D4: `gwp` is `noncomputable` twice over (the classical `if`
inside `minus_cost`, and `sInf`), so the gate is the campaign's standard
executable-twin route — `minusCostE`, `gwpE`, each with a *proved*
agreement theorem, at `Sanity.lean`'s `NRest (Fin 3) ℕ∞`. The
`#guard`s and Plausible `#test`s at the bottom therefore check `gwp`
itself, including `gwp_bindT`, the hardest ported statement. The first
two `#guard`s are the recorded counterexample of delta B1.
-/

namespace Lax13Proofs.Refine

variable {α β γ κ : Type}

/-! ### The resource type classes of `NREST_Type_Classes.thy`

Ported with the source's assumption lists, one field per assumption.
HOL bundles the operations into the class; Lean takes them as instance
parameters (substrate delta B3), which is the same adaptation
`Basic.lean` already made for `nrest`'s sort constraints. -/

/-- The source's `class nonneg = ord + zero + assumes needname_nonneg: "0 ≤ x"`. -/
class Nonneg (γ : Type) [LE γ] [Zero γ] : Prop where
  /-- `0` is the least resource. -/
  needname_nonneg : ∀ x : γ, (0 : γ) ≤ x

/-- The source's
`class needname = complete_lattice + minus + plus + assumes top_absorb,
minus_plus_assoc2, le_diff_if_add_le, add_leD2, add_le_if_le_diff`. -/
class Needname (γ : Type) [CompleteLattice γ] [ResSub γ] [Add γ] : Prop where
  /-- `⋀a. top - a = top` — paying out of an unbounded budget leaves it
  unbounded. This is the axiom mathlib's `Sub ℕ∞` fails (delta B1). -/
  top_absorb : ∀ a : γ, (⊤ : γ) -ᵣ a = ⊤
  /-- `⋀a b c. a - (b + c) = a - c - b`. -/
  minus_plus_assoc2 : ∀ a b c : γ, a -ᵣ (b + c) = a -ᵣ c -ᵣ b
  /-- `⋀a b c. ⟦a + b ≤ c; b ≤ c⟧ ⟹ a ≤ c - b`. -/
  le_diff_if_add_le : ∀ a b c : γ, a + b ≤ c → b ≤ c → a ≤ c -ᵣ b
  /-- `⋀a b c. a + b ≤ c ⟹ b ≤ c`. -/
  add_leD2 : ∀ a b c : γ, a + b ≤ c → b ≤ c
  /-- `⋀t1 a aa b. ⟦t1 ≤ b - a; aa ≤ b - a - t1; a ≤ b⟧ ⟹ t1 + a ≤ b`. -/
  add_le_if_le_diff : ∀ t1 a aa b : γ, t1 ≤ b -ᵣ a → aa ≤ b -ᵣ a -ᵣ t1 → a ≤ b → t1 + a ≤ b

/-- The source's `needname_cancle` (its spelling). -/
theorem needname_cancle [CompleteLattice γ] [ResSub γ] [Add γ] [Needname γ] {t1 t2 t : γ}
    (h : t1 + t2 ≤ t) : t2 ≤ t := Needname.add_leD2 _ _ _ h

/-- The source's `needname_adjoint`. -/
theorem needname_adjoint [CompleteLattice γ] [ResSub γ] [Add γ] [Needname γ] {a b c : γ}
    (h : a + b ≤ c) : a ≤ c -ᵣ b :=
  Needname.le_diff_if_add_le _ _ _ h (Needname.add_leD2 _ _ _ h)

/-- The source's
`class drm = minus + plus + ord + Inf + Sup + assumes diff_right_mono,
diff_left_mono, minus_continuousInf, minus_continuousSup, plus_left_mono`.
(The source spells the third assumption `minus_continousInf` in one
lemma name and `minus_continuousInf` in the class; the class spelling is
kept.) -/
class Drm (γ : Type) [ResSub γ] [Add γ] [LE γ] [InfSet γ] [SupSet γ] : Prop where
  /-- `a ≤ b ⟹ a - c ≤ b - c`. -/
  diff_right_mono : ∀ a b c : γ, a ≤ b → a -ᵣ c ≤ b -ᵣ c
  /-- `⋀a b c. b ≤ c ⟹ a - c ≤ a - b`. -/
  diff_left_mono : ∀ a b c : γ, b ≤ c → a -ᵣ c ≤ a -ᵣ b
  /-- `R ≠ {} ⟹ (INF r∈R. r - mt) ≤ Inf R - mt`. -/
  minus_continuousInf : ∀ (R : Set γ) (mt : γ), R.Nonempty → (⨅ r ∈ R, r -ᵣ mt) ≤ sInf R -ᵣ mt
  /-- `⋀X t q. X ≠ {} ⟹ ∀x∈X. t ≤ q - x ⟹ t ≤ q - (Sup X)`. -/
  minus_continuousSup :
    ∀ (X : Set γ) (t q : γ), X.Nonempty → (∀ x ∈ X, t ≤ q -ᵣ x) → t ≤ q -ᵣ sSup X
  /-- `a ≤ b ⟹ c + a ≤ c + b`. -/
  plus_left_mono : ∀ a b c : γ, a ≤ b → c + a ≤ c + b

/-- The source's
`class needname_zero = needname + nonneg + drm + ordered_comm_monoid_add
+ mult_zero + assumes needname_minus_absorb, needname_plus_absorb`.

Two deltas, both flagged. `ordered_comm_monoid_add` is mathlib's
`AddCommMonoid` + `PartialOrder` + `IsOrderedAddMonoid` (the bundled
class was retired), and it already proves the source's
`needname_plus_absorb : 0 + x = x`, which is therefore a *theorem*
(`zero_add`) rather than a field. `mult_zero` would be mathlib's
`MulZeroClass`, but that bundles its own `Zero`, which diamonds with
`AddCommMonoid`'s; its two axioms are fields here instead. -/
class NeednameZero (γ : Type) [CompleteLattice γ] [ResSub γ] [AddCommMonoid γ]
    [IsOrderedAddMonoid γ] [Mul γ] : Prop extends Needname γ, Nonneg γ, Drm γ where
  /-- The source's `needname_minus_absorb : x - 0 = x`. -/
  needname_minus_absorb : ∀ x : γ, x -ᵣ (0 : γ) = x
  /-- `mult_zero`'s `mult_zero_left`. -/
  mul_zero_left : ∀ x : γ, (0 : γ) * x = 0
  /-- `mult_zero`'s `mult_zero_right`. -/
  mul_zero_right : ∀ x : γ, x * (0 : γ) = 0

/-- The source's `needname_plus_absorb`, which mathlib's `AddCommMonoid`
already supplies. -/
theorem needname_plus_absorb [AddCommMonoid γ] (x : γ) : (0 : γ) + x = x := zero_add x

/-! ### The instance at `enat`

The one piece of `enat` arithmetic every axiom below reduces to: once
the result is known to be finite, all three operands are, and the
statement is a `ℕ` fact. -/

/-- `a + b ≤ c` with `c` finite gives `a ≤ c - b` at mathlib's truncated
subtraction. The finiteness is essential: `1 + ⊤ ≤ ⊤` but
`⊤ - ⊤ = 0` (delta B1 again). -/
theorem enat_le_sub_of_add_le {a b c : ℕ∞} (hc : c ≠ ⊤) (h : a + b ≤ c) : a ≤ c - b := by
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top hc (le_trans le_add_self h)
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top hc (le_trans le_self_add h)
  lift a to ℕ using ha
  lift b to ℕ using hb
  lift c to ℕ using hc
  rw [← Nat.cast_add, Nat.cast_le] at h
  rw [← ENat.coe_sub, Nat.cast_le]
  omega

instance instNonnegENat : Nonneg ℕ∞ := ⟨fun _ => zero_le⟩

/-- The source's `instance enat :: needname`. -/
instance instNeednameENat : Needname ℕ∞ where
  top_absorb _ := by simp
  minus_plus_assoc2 a b c := by
    rcases eq_or_ne a ⊤ with rfl | ha
    · simp
    · have hac : a - c ≠ ⊤ := ne_top_of_le_ne_top ha tsub_le_self
      rw [enat_resSub_of_ne_top ha (b + c), enat_resSub_of_ne_top ha c,
        enat_resSub_of_ne_top hac b, tsub_add_eq_tsub_tsub, tsub_right_comm]
  le_diff_if_add_le a b c hab _ := by
    rcases eq_or_ne c ⊤ with rfl | hc
    · simp
    · rw [enat_resSub_of_ne_top hc]
      exact enat_le_sub_of_add_le hc hab
  add_leD2 _ _ _ h := le_trans le_add_self h
  add_le_if_le_diff t1 a _ b h1 _ h3 := by
    rcases eq_or_ne b ⊤ with rfl | hb
    · exact le_top
    · rw [enat_resSub_of_ne_top hb] at h1
      calc t1 + a ≤ (b - a) + a := add_le_add h1 le_rfl
        _ = b := tsub_add_cancel_of_le h3

/-- The source's `instance enat :: drm`. `minus_continuousInf` is the
source's own argument: on `enat` the infimum of a nonempty set is
attained (`csInf_mem`), so the family already contains the value. -/
instance instDrmENat : Drm ℕ∞ where
  diff_right_mono a b c h := by
    rcases eq_or_ne b ⊤ with rfl | hb
    · simp
    · have ha : a ≠ ⊤ := ne_top_of_le_ne_top hb h
      rw [enat_resSub_of_ne_top ha, enat_resSub_of_ne_top hb]
      exact tsub_le_tsub_right h c
  diff_left_mono a b c h := by
    rcases eq_or_ne a ⊤ with rfl | ha
    · simp
    · rw [enat_resSub_of_ne_top ha, enat_resSub_of_ne_top ha]
      exact tsub_le_tsub_left h a
  minus_continuousInf R mt hR := iInf₂_le (sInf R) (csInf_mem hR)
  minus_continuousSup X t q hX h := by
    rcases eq_or_ne q ⊤ with rfl | hq
    · simp
    rcases eq_or_ne t 0 with rfl | ht
    · exact zero_le
    have hstep : ∀ x ∈ X, t + x ≤ q := by
      intro x hx
      have h1 : t ≤ q - x := by rw [← enat_resSub_of_ne_top hq]; exact h x hx
      by_cases hxq : x ≤ q
      · calc t + x ≤ (q - x) + x := add_le_add h1 le_rfl
          _ = q := tsub_add_cancel_of_le hxq
      · exact absurd (le_antisymm (by simpa [tsub_eq_zero_of_le (le_of_not_ge hxq)] using h1)
          zero_le) ht
    obtain ⟨x0, hx0⟩ := hX
    have htq : t ≤ q := le_trans le_self_add (hstep x0 hx0)
    have hsup : sSup X ≤ q - t :=
      sSup_le fun x hx => enat_le_sub_of_add_le hq (by rw [add_comm]; exact hstep x hx)
    rw [enat_resSub_of_ne_top hq]
    refine enat_le_sub_of_add_le hq ?_
    calc t + sSup X ≤ t + (q - t) := add_le_add le_rfl hsup
      _ = q := add_tsub_cancel_of_le htq
  plus_left_mono _ _ _ h := add_le_add le_rfl h

/-- The source's `instance enat :: needname_zero`. -/
instance instNeednameZeroENat : NeednameZero ℕ∞ where
  needname_minus_absorb := enat_resSub_zero
  mul_zero_left := zero_mul
  mul_zero_right := mul_zero

/-! ### The instances at `acost`

The source's `instantiation acost :: (type, needname) needname` and
`instantiation acost :: (type, needname_zero) needname_zero`, both
proved currency by currency exactly as the source proves them. -/

namespace ACost

instance instNonneg [LE γ] [Zero γ] [Nonneg γ] : Nonneg (ACost κ γ) :=
  ⟨fun _ => le_def.mpr fun _ => Nonneg.needname_nonneg _⟩

/-- The source's `instantiation acost :: (type, needname) needname`. -/
instance instNeedname [CompleteLattice γ] [ResSub γ] [Add γ] [Needname γ] :
    Needname (ACost κ γ) where
  top_absorb a := by ext k; simp [Needname.top_absorb]
  minus_plus_assoc2 a b c := by ext k; simp [Needname.minus_plus_assoc2]
  le_diff_if_add_le a b c h1 h2 :=
    le_def.mpr fun k =>
      Needname.le_diff_if_add_le _ _ _ (by simpa using le_def.mp h1 k) (le_def.mp h2 k)
  add_leD2 a b c h := le_def.mpr fun k => Needname.add_leD2 (a.toFun k) _ _ (by
    simpa using le_def.mp h k)
  add_le_if_le_diff t1 a aa b h1 h2 h3 :=
    le_def.mpr fun k =>
      Needname.add_le_if_le_diff _ _ (aa.toFun k) _ (by simpa using le_def.mp h1 k)
        (by simpa using le_def.mp h2 k) (le_def.mp h3 k)

/-- The `drm` half of the source's `acost :: needname_zero`
instantiation. Both continuity axioms reduce to the carrier's, currency
by currency, through `sInf_image`/`sSup_image`. -/
instance instDrm [CompleteLattice γ] [ResSub γ] [Add γ] [Drm γ] : Drm (ACost κ γ) where
  diff_right_mono _ _ _ h := le_def.mpr fun k => Drm.diff_right_mono _ _ _ (le_def.mp h k)
  diff_left_mono _ _ _ h := le_def.mpr fun k => Drm.diff_left_mono _ _ _ (le_def.mp h k)
  minus_continuousInf R mt hR := le_def.mpr fun k => by
    have h := Drm.minus_continuousInf ((fun a : ACost κ γ => a.toFun k) '' R) (mt.toFun k)
      (hR.image _)
    rw [iInf_image, sInf_image] at h
    simpa using h
  minus_continuousSup X t q hX h := le_def.mpr fun k => by
    have h' := Drm.minus_continuousSup ((fun a : ACost κ γ => a.toFun k) '' X) (t.toFun k)
      (q.toFun k) (hX.image _) (by rintro _ ⟨x, hx, rfl⟩; simpa using le_def.mp (h x hx) k)
    rw [sSup_image] at h'
    simpa using h'
  plus_left_mono _ _ _ h := le_def.mpr fun k => Drm.plus_left_mono _ _ _ (le_def.mp h k)

/-- The source's `instantiation acost :: (type, needname_zero) needname_zero`. -/
instance instNeednameZero [CompleteLattice γ] [ResSub γ] [AddCommMonoid γ]
    [IsOrderedAddMonoid γ] [Mul γ] [NeednameZero γ] : NeednameZero (ACost κ γ) where
  needname_minus_absorb x := by ext k; simp [NeednameZero.needname_minus_absorb]
  mul_zero_left x := by ext k; simp [NeednameZero.mul_zero_left]
  mul_zero_right x := by ext k; simp [NeednameZero.mul_zero_right]

end ACost

/-! ### `lift_acost`

`Enat_Cost.thy`'s embedding of a `nat`-valued cost into the `enat`-valued
carrier: `lift_acost c ≡ acostC (enat ∘ the_acost c)`. The `While` rule
below is stated over it, exactly as the source states it. -/

/-- The source's `lift_acost`. -/
def liftACost (c : ACost κ ℕ) : ACost κ ℕ∞ := ⟨fun k => (c.toFun k : ℕ∞)⟩

@[simp] theorem toFun_liftACost (c : ACost κ ℕ) (k : κ) :
    (liftACost c).toFun k = (c.toFun k : ℕ∞) := rfl

@[simp] theorem liftACost_ne_top (c : ACost κ ℕ) (k : κ) : (liftACost c).toFun k ≠ ⊤ := by
  simp

/-- The source's `lift_acost_zero`. -/
@[simp] theorem liftACost_zero : liftACost (0 : ACost κ ℕ) = 0 := by ext k; simp

/-- The source's `lift_acost_cost`. -/
@[simp] theorem liftACost_cost [DecidableEq κ] (n : κ) (x : ℕ) :
    liftACost (ACost.cost n x) = ACost.cost n (x : ℕ∞) := by
  ext k; rw [toFun_liftACost, ACost.toFun_cost, ACost.toFun_cost]; split <;> simp

/-- The source's `lift_acost_propagate` (`NREST_Automation.thy`). -/
theorem liftACost_add (A B : ACost κ ℕ) : liftACost (A + B) = liftACost A + liftACost B := by
  ext k; simp

/-- The source's `lift_acost_mono` and `lift_acost_mono'`, together;
`lift_acost_leq_conv` is this read as an iff. -/
@[simp] theorem liftACost_le_iff {A B : ACost κ ℕ} : liftACost A ≤ liftACost B ↔ A ≤ B := by
  simp only [ACost.le_def, toFun_liftACost, Nat.cast_le]

/-- The source's `lift_acost_minus`, with the resource subtraction on
the left and `nat` subtraction on the right. -/
theorem liftACost_resSub (A B : ACost κ ℕ) :
    liftACost A -ᵣ liftACost B = liftACost (A - B) := by
  ext k
  have h : ((A.toFun k : ℕ) : ℕ∞) ≠ ⊤ := by simp
  show ((A.toFun k : ℕ) : ℕ∞) -ᵣ ((B.toFun k : ℕ) : ℕ∞) = ((A.toFun k - B.toFun k : ℕ) : ℕ∞)
  rw [enat_resSub_of_ne_top h, ← ENat.coe_sub]

/-- The source's `lift_acost_cancel`. -/
@[simp] theorem liftACost_resSub_self (A : ACost κ ℕ) : liftACost A -ᵣ liftACost A = 0 := by
  rw [liftACost_resSub]; ext k; simp

/-! ### `mm3` -/

open Classical in
/-- The source's
`mm3 t A = (case A of None ⇒ None | Some t' ⇒ if t' ≤ t then Some (t - t') else None)`:
what is left of the budget `t` after paying `A`, and "unaffordable"
(`⊥`) when `A` does not fit or does not exist. -/
noncomputable def mm3 [ResSub γ] [LE γ] (t : γ) (A : WithBot γ) : WithBot γ :=
  A.recBotCoe ⊥ fun t' => if t' ≤ t then ((t -ᵣ t' : γ) : WithBot γ) else ⊥

/-- The source's `mm3_None`. -/
@[simp] theorem mm3_bot [ResSub γ] [LE γ] (t : γ) : mm3 t (⊥ : WithBot γ) = ⊥ := rfl

open Classical in
@[simp] theorem mm3_coe [ResSub γ] [LE γ] (t t' : γ) :
    mm3 t ((t' : γ) : WithBot γ) = if t' ≤ t then ((t -ᵣ t' : γ) : WithBot γ) else ⊥ := rfl

open Classical in
/-- The source's `Some_le_mm3_Some_conv`. -/
theorem le_mm3_coe_iff [ResSub γ] [PartialOrder γ] {t t' t'' : γ} :
    ((t : γ) : WithBot γ) ≤ mm3 t' ((t'' : γ) : WithBot γ) ↔ t'' ≤ t' ∧ t ≤ t' -ᵣ t'' := by
  rw [mm3_coe]
  split <;> simp_all

/-- The source's `mm3_Some_is_Some_enat`: a `lift_acost` budget pays for
itself exactly. (The source's finiteness side condition is discharged by
`lift_acost` here rather than assumed.) -/
@[simp] theorem mm3_liftACost_self (t : ACost κ ℕ) :
    mm3 (liftACost t) ((liftACost t : ACost κ ℕ∞) : WithBot (ACost κ ℕ∞)) = ((0 : ACost κ ℕ∞)) := by
  rw [mm3_coe, if_pos le_rfl, liftACost_resSub_self]

/-! ### `minus_cost`, `minus_potential`, `minus_p_m`

The source's three layers of "what is left of the postcondition's budget
after paying the program's cost": on a single cost, on a result map, and
on a computation. Under `F6` the source's `'d option` is `WithBot γ`, so
`None` reads `⊥` and `Some top` reads `((⊤ : γ) : WithBot γ)`, which is
`WithBot γ`'s own `⊤`. -/

section MinusCost

variable [CompleteLattice γ] [ResSub γ]

omit [ResSub γ] in
/-- Coercion commutes with set-indexed infima on `WithBot`. mathlib's
`WithBot.coe_sInf'` does the work; the empty case is fine because
`sInf ∅ = ⊤` on both sides. -/
theorem withBot_coe_iInf₂ (V : Set γ) (f : γ → γ) :
    (⨅ a ∈ V, ((f a : γ) : WithBot γ)) = ((⨅ a ∈ V, f a : γ) : WithBot γ) := by
  rw [← sInf_image, ← sInf_image, WithBot.coe_sInf' (OrderBot.bddBelow _), ← Set.image_comp]
  rfl

omit [ResSub γ] in
/-- A set of `WithBot`s whose supremum is not `⊥` has a nonempty
preimage under the coercion, and its supremum is that preimage's. -/
theorem withBot_sSup_of_ne_bot {U : Set (WithBot γ)} (h : sSup U ≠ ⊥) :
    (((↑) : γ → WithBot γ) ⁻¹' U).Nonempty ∧
      sSup U = ((sSup (((↑) : γ → WithBot γ) ⁻¹' U) : γ) : WithBot γ) := by
  have hsub : ¬ U ⊆ {⊥} := by
    intro hs
    exact h (le_antisymm (sSup_le fun u hu => le_of_eq (hs hu)) bot_le)
  obtain ⟨u, hu, hne⟩ : ∃ u ∈ U, u ≠ ⊥ := by
    by_contra hc
    refine hsub fun u hu => Set.mem_singleton_iff.mpr ?_
    by_contra hne
    exact hc ⟨u, hu, hne⟩
  rcases withBot_eq_bot_or_coe u with rfl | ⟨a, rfl⟩
  · exact absurd rfl hne
  · exact ⟨⟨a, hu⟩, WithBot.sSup_eq hsub (OrderTop.bddAbove _)⟩

open Classical in
/-- The source's `minus_cost`: `r` is what the postcondition allows and
`m` what the program charges; the result is what is left, `⊥` when the
charge does not fit, and `⊤` when the program cannot produce the result
at all (so nothing is charged). -/
noncomputable def minusCost (r m : WithBot γ) : WithBot γ :=
  m.recBotCoe ((⊤ : γ) : WithBot γ) fun mt =>
    r.recBotCoe ⊥ fun rt => if mt ≤ rt then ((rt -ᵣ mt : γ) : WithBot γ) else ⊥

/-- The source's `minus_cost_None`. -/
@[simp] theorem minusCost_bot_right (r : WithBot γ) : minusCost r (⊥ : WithBot γ) = ⊤ := rfl

@[simp] theorem minusCost_bot_left (mt : γ) :
    minusCost (⊥ : WithBot γ) ((mt : γ) : WithBot γ) = ⊥ := rfl

open Classical in
@[simp] theorem minusCost_coe (rt mt : γ) :
    minusCost ((rt : γ) : WithBot γ) ((mt : γ) : WithBot γ)
      = if mt ≤ rt then ((rt -ᵣ mt : γ) : WithBot γ) else ⊥ := rfl

/-- The `top_absorb` axiom, read on `minus_cost`: an unconstrained
postcondition is affordable whatever the program charges. -/
@[simp] theorem minusCost_top_left [Add γ] [Needname γ] (m : WithBot γ) :
    minusCost (⊤ : WithBot γ) m = ⊤ := by
  rcases withBot_eq_bot_or_coe m with rfl | ⟨mt, rfl⟩
  · rfl
  · show minusCost (((⊤ : γ) : WithBot γ)) ((mt : γ) : WithBot γ) = ⊤
    rw [minusCost_coe, if_pos le_top, Needname.top_absorb]
    rfl

/-- The source's `minus_cost_mono`. -/
theorem minusCost_mono [Add γ] [Drm γ] {q q' m : WithBot γ} (h : m ≠ ⊥ → q' ≤ q) :
    minusCost q' m ≤ minusCost q m := by
  rcases withBot_eq_bot_or_coe m with rfl | ⟨mt, rfl⟩
  · simp
  have hq := h (by simp)
  rcases withBot_eq_bot_or_coe q' with rfl | ⟨rt', rfl⟩
  · simp
  rcases withBot_eq_bot_or_coe q with rfl | ⟨rt, rfl⟩
  · simp at hq
  rw [minusCost_coe, minusCost_coe]
  rw [WithBot.coe_le_coe] at hq
  split
  · rw [if_pos (‹mt ≤ rt'›.trans hq), WithBot.coe_le_coe]
    exact Drm.diff_right_mono _ _ _ hq
  · exact bot_le

/-- The source's `minus_cost_antimono`. -/
theorem minusCost_antimono [Add γ] [Drm γ] {x y : WithBot γ} (q : WithBot γ) (h : x ≤ y) :
    minusCost q y ≤ minusCost q x := by
  rcases withBot_eq_bot_or_coe x with rfl | ⟨xt, rfl⟩
  · simp
  rcases withBot_eq_bot_or_coe y with rfl | ⟨yt, rfl⟩
  · simp at h
  rcases withBot_eq_bot_or_coe q with rfl | ⟨rt, rfl⟩
  · simp
  rw [minusCost_coe, minusCost_coe]
  rw [WithBot.coe_le_coe] at h
  split
  · rw [if_pos (h.trans ‹yt ≤ rt›), WithBot.coe_le_coe]
    exact Drm.diff_left_mono _ _ _ h
  · exact bot_le

/-- The source's `minus_cost_contiuous2` (its spelling): paying the
supremum of a set of charges is affordable as soon as every single
charge is. -/
theorem le_minusCost_sSup [Add γ] [Drm γ] {t q : WithBot γ} {U : Set (WithBot γ)}
    (h : ∀ u ∈ U, t ≤ minusCost q u) : t ≤ minusCost q (sSup U) := by
  rcases eq_or_ne (sSup U) ⊥ with hU | hU
  · rw [hU, minusCost_bot_right]; exact le_top
  set V : Set γ := ((↑) : γ → WithBot γ) ⁻¹' U with hVdef
  obtain ⟨⟨a₀, ha₀⟩, hV⟩ := withBot_sSup_of_ne_bot hU
  rcases withBot_eq_bot_or_coe q with rfl | ⟨rt, rfl⟩
  · have ht : t = ⊥ := le_bot_iff.mp (by simpa using h _ ha₀)
    rw [ht]; exact bot_le
  rcases withBot_eq_bot_or_coe t with rfl | ⟨tt, rfl⟩
  · exact bot_le
  have hall : ∀ a ∈ V, a ≤ rt ∧ tt ≤ rt -ᵣ a := by
    intro a ha
    have := h _ ha
    rw [minusCost_coe] at this
    split at this
    · exact ⟨‹a ≤ rt›, WithBot.coe_le_coe.mp this⟩
    · simp at this
  have hle : sSup V ≤ rt := sSup_le fun a ha => (hall a ha).1
  rw [hV, minusCost_coe, if_pos hle, WithBot.coe_le_coe]
  exact Drm.minus_continuousSup V tt rt ⟨a₀, ha₀⟩ fun a ha => (hall a ha).2

/-- The pointwise reading of the previous lemma: `minus_cost` turns
suprema of charges into universal quantification. -/
theorem le_minusCost_sSup_iff [Add γ] [Drm γ] {t q : WithBot γ} {U : Set (WithBot γ)} :
    t ≤ minusCost q (sSup U) ↔ ∀ u ∈ U, t ≤ minusCost q u :=
  ⟨fun h u hu => h.trans (minusCost_antimono q (show u ≤ sSup U from le_sSup hu)),
    le_minusCost_sSup⟩

/-- The source's `mm_continousInf'` (its spelling): `minus_cost` is
continuous in the postcondition's budget. -/
theorem minusCost_sInf [Add γ] [Drm γ] {R : Set (WithBot γ)} (hR : R.Nonempty)
    (m : WithBot γ) : minusCost (sInf R) m = ⨅ r ∈ R, minusCost r m := by
  rcases withBot_eq_bot_or_coe m with rfl | ⟨mt, rfl⟩
  · simp
  by_cases hbot : (⊥ : WithBot γ) ∈ R
  · have h1 : sInf R = ⊥ := le_antisymm (sInf_le hbot) bot_le
    rw [h1, minusCost_bot_left]
    refine le_antisymm bot_le ?_
    calc (⨅ r ∈ R, minusCost r ((mt : γ) : WithBot γ))
        ≤ minusCost (⊥ : WithBot γ) ((mt : γ) : WithBot γ) := iInf₂_le _ hbot
      _ = ⊥ := minusCost_bot_left mt
  · set V : Set γ := ((↑) : γ → WithBot γ) ⁻¹' R with hVdef
    have hRV : R = ((↑) : γ → WithBot γ) '' V := by
      ext u
      constructor
      · intro hu
        rcases withBot_eq_bot_or_coe u with rfl | ⟨a, rfl⟩
        · exact absurd hu hbot
        · exact ⟨a, hu, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ha
    obtain ⟨u₀, hu₀⟩ := hR
    have hVne : V.Nonempty := by
      rcases withBot_eq_bot_or_coe u₀ with rfl | ⟨a, rfl⟩
      · exact absurd hu₀ hbot
      · exact ⟨a, hu₀⟩
    have hsInf : sInf R = ((sInf V : γ) : WithBot γ) :=
      WithBot.sInf_eq hbot (OrderBot.bddBelow _)
    rw [hsInf, minusCost_coe, hRV, iInf_image]
    by_cases hmt : mt ≤ sInf V
    · rw [if_pos hmt]
      have harm : (⨅ a ∈ V, minusCost ((a : γ) : WithBot γ) ((mt : γ) : WithBot γ))
          = ⨅ a ∈ V, ((a -ᵣ mt : γ) : WithBot γ) :=
        iInf_congr fun a => iInf_congr fun ha => by
          rw [minusCost_coe, if_pos (hmt.trans (sInf_le ha))]
      rw [harm, withBot_coe_iInf₂, WithBot.coe_inj]
      exact le_antisymm (le_iInf₂ fun a ha => Drm.diff_right_mono _ _ _ (sInf_le ha))
        (Drm.minus_continuousInf V mt hVne)
    · rw [if_neg hmt]
      obtain ⟨a, ha, hna⟩ : ∃ a ∈ V, ¬ mt ≤ a := by
        by_contra hc
        exact hmt (le_sInf fun a ha => by
          by_contra hna
          exact hc ⟨a, ha, hna⟩)
      refine le_antisymm bot_le ?_
      refine le_trans (iInf₂_le a ha) ?_
      rw [minusCost_coe, if_neg hna]

/-- The heart of the bind rule (the source's `lem` and `lem2`, merged
into the single equivalence they are used through): charging `T` first
and then measuring against `q` is, as far as affordability goes, the
same as measuring against what is left of `q` after `T`. This is where
`top_absorb`, `minus_plus_assoc2`, `needname_adjoint`,
`add_le_if_le_diff` and `add_leD2` are all consumed. -/
theorem le_minusCost_add_iff [Add γ] [Needname γ] {t q : WithBot γ} (T : γ) (v : WithBot γ) :
    t ≤ minusCost q (((T : γ) : WithBot γ) + v)
      ↔ t ≤ minusCost (minusCost q v) ((T : γ) : WithBot γ) := by
  rcases withBot_eq_bot_or_coe v with rfl | ⟨mt, rfl⟩
  · rw [WithBot.add_bot, minusCost_bot_right, minusCost_top_left]
  rcases withBot_eq_bot_or_coe q with rfl | ⟨rt, rfl⟩
  · simp [← WithBot.coe_add]
  rw [← WithBot.coe_add, minusCost_coe, minusCost_coe]
  by_cases hmt : mt ≤ rt
  · rw [if_pos hmt, minusCost_coe, Needname.minus_plus_assoc2]
    by_cases hsum : T + mt ≤ rt
    · rw [if_pos hsum, if_pos (needname_adjoint hsum)]
    · rw [if_neg hsum]
      constructor
      · intro h; exact le_trans h bot_le
      · intro h
        split at h
        · rcases withBot_eq_bot_or_coe t with rfl | ⟨tt, rfl⟩
          · exact bot_le
          · exact absurd (Needname.add_le_if_le_diff T mt tt rt ‹T ≤ rt -ᵣ mt›
              (WithBot.coe_le_coe.mp h) hmt) hsum
        · exact h
  · rw [if_neg hmt, minusCost_bot_left]
    constructor
    · intro h
      split at h
      · exact absurd (Needname.add_leD2 T mt rt ‹T + mt ≤ rt›) hmt
      · exact h
    · intro h; exact le_trans h bot_le

end MinusCost

/-! ### `minus_potential` and `minus_p_m` -/

section MinusPM

variable [CompleteLattice γ] [ResSub γ]

/-- The source's `minus_potential`, given in the form its own
`minus_potential_alt` puts it in. -/
noncomputable def minusPotential (R m : α → WithBot γ) : α → WithBot γ :=
  fun x => minusCost (R x) (m x)

/-- The source's `minus_potential_alt`. -/
@[simp] theorem minusPotential_apply (R m : α → WithBot γ) (x : α) :
    minusPotential R m x = minusCost (R x) (m x) := rfl

/-- The source's `minus_p_m`. -/
noncomputable def minusPM (Q : α → WithBot γ) (M : NRest α γ) (x : α) : WithBot γ :=
  match M with
  | .fail => ⊥
  | .rest Mf => minusPotential Q Mf x

/-- The source's `minus_p_m_Failt`. -/
@[simp] theorem minusPM_fail (Q : α → WithBot γ) (x : α) :
    minusPM Q (NRest.fail : NRest α γ) x = ⊥ := rfl

/-- The source's `minus_p_m_alt`. -/
@[simp] theorem minusPM_rest (Q Mf : α → WithBot γ) (x : α) :
    minusPM Q (NRest.rest Mf) x = minusCost (Q x) (Mf x) := rfl

/-- The source's `minus_p_m_mono`. -/
theorem minusPM_mono [Add γ] [Drm γ] {q q' : α → WithBot γ} {m : NRest α γ}
    (h : ∀ P x, m = NRest.rest P → P x ≠ ⊥ → q x ≤ q' x) (x : α) :
    minusPM q m x ≤ minusPM q' m x := by
  cases m with
  | fail => simp
  | rest P => exact minusCost_mono fun hne => h P x rfl hne

/-- The source's `minus_p_m_antimono`. -/
theorem minusPM_antimono [Add γ] [Drm γ] {M M' : NRest α γ} (Q : α → WithBot γ)
    (h : M ≤ M') (x : α) : minusPM Q M' x ≤ minusPM Q M x := by
  cases M' with
  | fail => simp
  | rest Y' =>
    cases M with
    | fail => simp at h
    | rest Y => exact minusCost_antimono (Q x) (h x)

/-- The source's `minus_p_m_continuous`, in the `iSup` form `bindT`
delivers. -/
theorem le_minusPM_iSup_iff [Add γ] [Drm γ] {ι : Sort*} {t : WithBot γ}
    (Q : α → WithBot γ) (F : ι → NRest α γ) (x : α) :
    t ≤ minusPM Q (⨆ i, F i) x ↔ ∀ i, t ≤ minusPM Q (F i) x := by
  by_cases hf : ∃ i, F i = NRest.fail
  · obtain ⟨i, hi⟩ := hf
    rw [NRest.iSup_eq_fail_iff.mpr ⟨i, hi⟩, minusPM_fail]
    refine ⟨fun h j => le_trans h bot_le, fun h => ?_⟩
    simpa [hi] using h i
  · simp only [not_exists] at hf
    have hrest : ∀ i, F i = NRest.rest (NRest.resultsOf (F i)) := fun i =>
      NRest.eq_rest_resultsOf (hf i)
    have h1 : (⨆ i, F i) = NRest.rest (⨆ i, NRest.resultsOf (F i)) := by
      rw [show (⨆ i, F i) = ⨆ i, NRest.rest (NRest.resultsOf (F i)) from iSup_congr hrest,
        NRest.iSup_rest]
    rw [h1, minusPM_rest, iSup_apply, iSup,
      le_minusCost_sSup_iff (U := Set.range fun i => NRest.resultsOf (F i) x)]
    constructor
    · intro h i
      rw [hrest i, minusPM_rest]
      exact h _ ⟨i, rfl⟩
    · rintro h _ ⟨i, rfl⟩
      have hi := h i
      rwa [hrest i, minusPM_rest] at hi

/-- The source's `minus_p_m_continuousInf`. The index type is required
nonempty: HOL types always are, Lean's need not be (substrate delta
B5). -/
theorem minusPM_iInf [Add γ] [Drm γ] {ι : Sort*} [Nonempty ι] (f : ι → α → WithBot γ)
    (m : NRest α γ) (y : α) :
    minusPM (fun z => ⨅ i, f i z) m y = ⨅ i, minusPM (fun z => f i z) m y := by
  cases m with
  | fail => simp
  | rest M =>
    simp only [minusPM_rest]
    rw [show (⨅ i, f i y) = sInf (Set.range fun i => f i y) from rfl,
      minusCost_sInf (Set.range_nonempty _), iInf_range]

/-- The source's
`(t ≤ minus_p_m Q (consume m T) x) = (t ≤ minus_cost (minus_p_m Q m x) T)`,
the `blub` step of `minus_p_m_bindT`. -/
theorem le_minusPM_consumeB_iff [AddMonoid γ] [Needname γ] {t : WithBot γ}
    (Q : α → WithBot γ) (n : NRest α γ) (u : WithBot γ) (x : α) :
    t ≤ minusPM Q (NRest.consumeB n u) x ↔ t ≤ minusCost (minusPM Q n x) u := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨T, rfl⟩
  · rw [NRest.consumeB_bot, minusCost_bot_right, NRest.bot_eq_rest_bot, minusPM_rest]
    simp
  cases n with
  | fail => simp [NRest.consumeB_coe]
  | rest N =>
    rw [NRest.consumeB_coe, NRest.consume_rest', minusPM_rest, minusPM_rest]
    exact le_minusCost_add_iff T (N x)

/-- **The source's `minus_p_m_bindT`.** `α` is required nonempty for the
same reason as `minusPM_iInf` (delta B5): with `m = FAILT` and no
possible `y`, the right-hand side is vacuous while the left-hand side is
not. -/
theorem le_minusPM_bindT [Nonempty α] [AddCommMonoid γ] [Needname γ] [Drm γ]
    {t : WithBot γ} (Q : β → WithBot γ) (m : NRest α γ) (f : α → NRest β γ) (x : β) :
    t ≤ minusPM Q (NRest.bindT m f) x
      ↔ ∀ y, t ≤ minusPM (fun z => minusPM Q (f z) x) m y := by
  cases m with
  | fail =>
    rw [NRest.bindT_fail, minusPM_fail]
    exact ⟨fun h _ => by simpa using h, fun h => by simpa using h (Classical.arbitrary α)⟩
  | rest M =>
    rw [NRest.bindT_rest_eq_iSup, le_minusPM_iSup_iff]
    exact forall_congr' fun y => by rw [le_minusPM_consumeB_iff, minusPM_rest]

end MinusPM

/-! ### `gwp`

The source's `gwp M Qf = Inf { minus_p_m Qf M x | x. True}`: the largest
budget from which `M` can be run and still leave `Qf`'s allowance at
every result. -/

section Gwp

variable [CompleteLattice γ] [ResSub γ]

/-- The source's `gwp`. The set comprehension `{ … | x. True}` is the
range of the family, so this is its `⨅`; `gwp_def_sInf` records the
source's own spelling. -/
noncomputable def gwp (M : NRest α γ) (Q : α → WithBot γ) : WithBot γ :=
  ⨅ x, minusPM Q M x

theorem gwp_def_sInf (M : NRest α γ) (Q : α → WithBot γ) :
    gwp M Q = sInf {u | ∃ x, u = minusPM Q M x} := by
  rw [gwp, iInf]
  congr 1
  ext u
  simp [Set.range, eq_comm]

/-- The source's `gwp_pw`. -/
theorem gwp_pw {t : WithBot γ} {M : NRest α γ} {Q : α → WithBot γ} :
    t ≤ gwp M Q ↔ ∀ x, t ≤ minusPM Q M x := le_iInf_iff

theorem gwp_le (M : NRest α γ) (Q : α → WithBot γ) (x : α) : gwp M Q ≤ minusPM Q M x :=
  iInf_le _ x

/-- The source's `gwp_FAILT`. Nonempty `α` per delta B5. -/
@[simp] theorem gwp_fail [Nonempty α] (Q : α → WithBot γ) :
    gwp (NRest.fail : NRest α γ) Q = ⊥ := by
  rw [gwp]
  simp only [minusPM_fail]
  exact iInf_const

open Classical in
/-- The source's `gwp⇩n`: the "no-fail" variant, which reads a failing
computation as unconstrained rather than unaffordable. -/
noncomputable def gwpn (M : NRest α γ) (Q : α → WithBot γ) : WithBot γ :=
  if M.nofailT then gwp M Q else ⊤

/-- The source's `gwpn_FAIL`. -/
@[simp] theorem gwpn_fail (Q : α → WithBot γ) : gwpn (NRest.fail : NRest α γ) Q = ⊤ := by
  simp [gwpn, NRest.nofailT]

theorem gwpn_of_nofailT {M : NRest α γ} (h : M.nofailT) (Q : α → WithBot γ) :
    gwpn M Q = gwp M Q := by simp [gwpn, h]

/-- The source's `gwp_mono`. -/
theorem gwp_mono [Add γ] [Drm γ] {m : NRest α γ} {q q' : α → WithBot γ}
    (h : ∀ P x, m = NRest.rest P → P x ≠ ⊥ → q x ≤ q' x) : gwp m q ≤ gwp m q' :=
  iInf_mono fun x => minusPM_mono h x

/-- The source's `gwp_antimono`. -/
theorem gwp_antimono [Add γ] [Drm γ] {M M' : NRest α γ} (Q : α → WithBot γ) (h : M ≤ M') :
    gwp M' Q ≤ gwp M Q :=
  iInf_mono fun x => minusPM_antimono Q h x

/-! ### The affordability calculus

The source's `gwp_conseq_aux1` is the one algebraic fact every rule
below is a corollary of: a budget `t` survives paying `t'` out of an
allowance `Q` exactly when `Q` allows `t + t'`. -/

/-- The source's `gwp_conseq_aux1`. -/
theorem le_minusCost_coe_iff [Add γ] [Needname γ] {t t' : γ} {Q : WithBot γ} :
    ((t : γ) : WithBot γ) ≤ minusCost Q ((t' : γ) : WithBot γ)
      ↔ ((t + t' : γ) : WithBot γ) ≤ Q := by
  rcases withBot_eq_bot_or_coe Q with rfl | ⟨q, rfl⟩
  · simp
  rw [minusCost_coe]
  by_cases hq : t' ≤ q
  · rw [if_pos hq, WithBot.coe_le_coe, WithBot.coe_le_coe]
    exact ⟨fun h => Needname.add_le_if_le_diff t t' (q -ᵣ t' -ᵣ t) q h le_rfl hq,
      fun h => needname_adjoint h⟩
  · rw [if_neg hq]
    simp only [le_bot_iff, WithBot.coe_ne_bot, WithBot.coe_le_coe, false_iff]
    exact fun h => hq (Needname.add_leD2 t t' q h)

/-- The workhorse characterisation of `gwp` on a non-failing
computation: every reachable result must leave the postcondition's
allowance. Every vcg rule below is an instance of it. -/
theorem le_gwp_rest_iff [Add γ] [Needname γ] {t : γ} {P Q : α → WithBot γ} :
    ((t : γ) : WithBot γ) ≤ gwp (NRest.rest P) Q
      ↔ ∀ x mt, P x = ((mt : γ) : WithBot γ) → ((t + mt : γ) : WithBot γ) ≤ Q x := by
  rw [gwp_pw]
  constructor
  · intro h x mt hx
    have hx' := h x
    rw [minusPM_rest, hx] at hx'
    exact le_minusCost_coe_iff.mp hx'
  · intro h x
    rw [minusPM_rest]
    rcases withBot_eq_bot_or_coe (P x) with hx | ⟨mt, hx⟩
    · rw [hx, minusCost_bot_right]; exact le_top
    · rw [hx]; exact le_minusCost_coe_iff.mpr (h x mt hx)

/-! ### The vcg entry lemma -/

/-- **The source's `gwp_specifies_I`** — the entry point of the whole
calculus: a program that can be run from budget `0` against `Q` refines
`SPECT Q`. Nonempty `α` per delta B5. -/
theorem gwp_specifies_I [Nonempty α] [Zero γ] {m : NRest α γ} {Q : α → WithBot γ}
    (h : ((0 : γ) : WithBot γ) ≤ gwp m Q) : m ≤ NRest.rest Q := by
  rw [gwp_pw] at h
  cases m with
  | fail =>
    have hc := h (Classical.arbitrary α)
    rw [minusPM_fail, le_bot_iff] at hc
    exact absurd hc WithBot.coe_ne_bot
  | rest M =>
    refine NRest.rest_le_rest_iff.mpr fun x => ?_
    have hx := h x
    rw [minusPM_rest] at hx
    rcases withBot_eq_bot_or_coe (M x) with hM | ⟨mt, hM⟩
    · rw [hM]; exact bot_le
    rcases withBot_eq_bot_or_coe (Q x) with hQ | ⟨rt, hQ⟩
    · rw [hM, hQ] at hx; simp at hx
    · rw [hM, hQ, minusCost_coe] at hx
      split at hx
      · rw [hM, hQ, WithBot.coe_le_coe]; exact ‹mt ≤ rt›
      · simp at hx

/-- The source's `gwp_specifies_rev_I`: the converse, at
`needname_zero`. -/
theorem gwp_specifies_rev_I [AddCommMonoid γ] [IsOrderedAddMonoid γ] [Mul γ]
    [NeednameZero γ] {m : NRest α γ} {Q : α → WithBot γ} (h : m ≤ NRest.rest Q) :
    ((0 : γ) : WithBot γ) ≤ gwp m Q := by
  rw [gwp_pw]
  intro x
  cases m with
  | fail => simp at h
  | rest M =>
    rw [minusPM_rest]
    have hx := NRest.rest_le_rest_iff.mp h x
    rcases withBot_eq_bot_or_coe (M x) with hM | ⟨mt, hM⟩
    · rw [hM, minusCost_bot_right]; exact le_top
    rcases withBot_eq_bot_or_coe (Q x) with hQ | ⟨rt, hQ⟩
    · rw [hM, hQ] at hx; simp at hx
    · rw [hM, hQ] at hx ⊢
      rw [minusCost_coe, if_pos (WithBot.coe_le_coe.mp hx), WithBot.coe_le_coe]
      exact Nonneg.needname_nonneg _

/-! ### Pointwise reasoning about `gwp` via `nres3` -/

/-- The source's `nres3 Q M x t ⟷ minus_p_m Q M x ≥ t`. -/
def nres3 (Q : α → WithBot γ) (M : NRest α γ) (x : α) (t : WithBot γ) : Prop :=
  t ≤ minusPM Q M x

/-- The source's `pw_gwp_le`. -/
theorem pw_gwp_le {M : NRest α γ} {M' : NRest β γ} {Q : α → WithBot γ} {Q' : β → WithBot γ}
    (h : ∀ t, (∀ x, nres3 Q M x t) → ∀ x, nres3 Q' M' x t) : gwp M Q ≤ gwp M' Q' :=
  gwp_pw.mpr (h (gwp M Q) fun x => gwp_le M Q x)

/-- The source's `pw_gwp_eqI`. -/
theorem pw_gwp_eqI {M : NRest α γ} {M' : NRest β γ} {Q : α → WithBot γ} {Q' : β → WithBot γ}
    (h1 : ∀ t, (∀ x, nres3 Q M x t) → ∀ x, nres3 Q' M' x t)
    (h2 : ∀ t, (∀ x, nres3 Q' M' x t) → ∀ x, nres3 Q M x t) : gwp M Q = gwp M' Q' :=
  le_antisymm (pw_gwp_le h1) (pw_gwp_le h2)

/-! ### The bind rule -/

/-- The `≥` half of the source's `gwp_bindT` (whose own comment marks it
"only need ≥"), stated as the affordability transfer the vcg rule uses.
Unlike the full equality it needs nothing of `β`. -/
theorem le_gwp_bindT [Nonempty α] [AddCommMonoid γ] [Needname γ] [Drm γ] {t : WithBot γ}
    {M : NRest α γ} {f : α → NRest β γ} {Q : β → WithBot γ}
    (h : t ≤ gwp M fun y => gwp (f y) Q) : t ≤ gwp (NRest.bindT M f) Q := by
  rw [gwp_pw] at h ⊢
  intro x
  rw [le_minusPM_bindT]
  intro y
  exact le_trans (h y) (minusPM_mono (fun _ z _ _ => gwp_le (f z) Q x) y)

/-- **The source's `gwp_bindT`**, in full. Both result types are
required nonempty (delta B5). -/
theorem gwp_bindT [Nonempty α] [Nonempty β] [AddCommMonoid γ] [Needname γ] [Drm γ]
    (M : NRest α γ) (f : α → NRest β γ) (Q : β → WithBot γ) :
    gwp (NRest.bindT M f) Q = gwp M fun y => gwp (f y) Q := by
  have key : ∀ t : WithBot γ,
      t ≤ gwp (NRest.bindT M f) Q ↔ t ≤ gwp M fun y => gwp (f y) Q := by
    intro t
    refine ⟨fun h => ?_, le_gwp_bindT⟩
    rw [gwp_pw] at h ⊢
    intro y
    have hall : ∀ x, t ≤ minusPM (fun z => minusPM Q (f z) x) M y := fun x =>
      (le_minusPM_bindT Q M f x).mp (h x) y
    have hrw : minusPM (fun z => ⨅ x, minusPM Q (f z) x) M y
        = ⨅ x, minusPM (fun z => minusPM Q (f z) x) M y :=
      minusPM_iInf (fun x z => minusPM Q (f z) x) M y
    show t ≤ minusPM (fun z => ⨅ x, minusPM Q (f z) x) M y
    rw [hrw]
    exact le_iInf hall
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

/-! ### The vcg rule suite

The source's `[vcg_rules']` set, one lemma per syntactic form. Every one
is registered with the `refine_vcg` seed set at the bottom of the
file. -/

/-- The source's `gwp_bindT_I`. -/
theorem gwp_bindT_I [Nonempty α] [AddCommMonoid γ] [Needname γ] [Drm γ] {t : γ}
    {M : NRest α γ} {f : α → NRest β γ} {Q : β → WithBot γ}
    (h : ((t : γ) : WithBot γ) ≤ gwp M fun y => gwp (f y) Q) :
    ((t : γ) : WithBot γ) ≤ gwp (NRest.bindT M f) Q := le_gwp_bindT h

/-- The source's `gwp_RETURNT_I`. -/
theorem gwp_RETURNT_I [AddCommMonoid γ] [IsOrderedAddMonoid γ] [Mul γ] [NeednameZero γ]
    {t : WithBot γ} {Q : α → WithBot γ} {x : α} (h : t ≤ Q x) :
    t ≤ gwp (NRest.returnT x) Q := by
  rw [NRest.returnT, gwp_pw]
  intro v
  rw [minusPM_rest]
  rcases eq_or_ne v x with rfl | hv
  · rw [NRest.single_self, ← WithBot.coe_zero]
    rcases withBot_eq_bot_or_coe (Q v) with hq | ⟨rt, hq⟩
    · rw [hq, minusCost_bot_left]; rwa [hq] at h
    · rw [hq, minusCost_coe, if_pos (Nonneg.needname_nonneg rt),
        NeednameZero.needname_minus_absorb]
      rwa [hq] at h
  · rw [NRest.single_of_ne hv, minusCost_bot_right]; exact le_top

/-- The source's `gwp_SPECT_I` (`SPECT [x ↦ t]` is `Basic.lean`'s
`single`). -/
theorem gwp_SPECT_I [AddCommMonoid γ] [Needname γ] {t' t : γ} {Q : α → WithBot γ} {x : α}
    (h : ((t' + t : γ) : WithBot γ) ≤ Q x) :
    ((t' : γ) : WithBot γ) ≤ gwp (NRest.rest (NRest.single x ((t : γ) : WithBot γ))) Q := by
  refine le_gwp_rest_iff.mpr fun v mt hv => ?_
  rcases eq_or_ne v x with rfl | hne
  · rw [NRest.single_self, WithBot.coe_inj] at hv
    subst hv
    exact h
  · rw [NRest.single_of_ne hne] at hv
    exact absurd hv.symm WithBot.coe_ne_bot

/-- The source's `gwp_SPECT_emb_I` (`emb' X t` is `Basic.lean`'s
`spec`). -/
theorem gwp_SPECT_emb_I [AddCommMonoid γ] [Needname γ] {X : α → Prop} {tf : α → γ} {t' : γ}
    {Q : α → WithBot γ} (h : ∀ x, X x → ((t' + tf x : γ) : WithBot γ) ≤ Q x) :
    ((t' : γ) : WithBot γ) ≤ gwp (NRest.spec X tf) Q := by
  rw [NRest.spec]
  refine le_gwp_rest_iff.mpr fun x mt hx => ?_
  by_cases hX : X x
  · rw [if_pos hX, WithBot.coe_inj] at hx
    subst hx
    exact h x hX
  · rw [if_neg hX] at hx
    exact absurd hx.symm WithBot.coe_ne_bot

/-- The source's `gwp_consume`. -/
theorem gwp_consume [AddCommMonoid γ] [Needname γ] {T t : γ} {m : NRest α γ}
    {Q : α → WithBot γ} (h : ((T + t : γ) : WithBot γ) ≤ gwp m Q) :
    ((t : γ) : WithBot γ) ≤ gwp (NRest.consume m T) Q := by
  rw [gwp_pw] at h ⊢
  intro x
  rw [show NRest.consume m T = NRest.consumeB m ((T : γ) : WithBot γ) from rfl,
    le_minusPM_consumeB_iff, le_minusCost_coe_iff, add_comm t T]
  exact h x

/-- The source's `gwp_If_I`. -/
theorem gwp_If_I {b : Prop} [Decidable b] {Ma Mb : NRest α γ} {Q : α → WithBot γ}
    {t : WithBot γ} (h1 : b → t ≤ gwp Ma Q) (h2 : ¬ b → t ≤ gwp Mb Q) :
    t ≤ gwp (if b then Ma else Mb) Q := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

/-- The source's `gwp_ASSERT_I`. -/
theorem gwp_ASSERT_I [AddCommMonoid γ] [IsOrderedAddMonoid γ] [Mul γ] [NeednameZero γ]
    {Φ : Prop} {t : WithBot γ} {Q : Unit → WithBot γ} (hΦ : Φ) (h : Φ → t ≤ Q ()) :
    t ≤ gwp (NRest.assert Φ) Q := by
  rw [NRest.assert_pos hΦ]
  exact gwp_RETURNT_I (h hΦ)

/-- The source's `gwp_ASSERT_bind_I`. -/
theorem gwp_ASSERT_bind_I [AddMonoid γ] {Φ : Prop} {t : WithBot γ} {M : NRest α γ}
    {Q : α → WithBot γ} (hΦ : Φ) (h : Φ → t ≤ gwp M Q) :
    t ≤ gwp (NRest.bindT (NRest.assert Φ) fun _ => M) Q := by
  rw [NRest.assert_pos hΦ, NRest.returnT_bindT]
  exact h hΦ

/-! ### Consequence rules -/

/-- The source's `gwp_conseq`. -/
theorem gwp_conseq [AddCommMonoid γ] [Needname γ] {t : γ} {f : NRest α γ}
    {Q Q' : α → WithBot γ} (h1 : ((t : γ) : WithBot γ) ≤ gwp f Q')
    (h2 : ∀ x t'' M, f = NRest.rest M → M x ≠ ⊥ → Q' x = ((t'' : γ) : WithBot γ) →
      ((t'' : γ) : WithBot γ) ≤ Q x) :
    ((t : γ) : WithBot γ) ≤ gwp f Q := by
  rw [gwp_pw] at h1 ⊢
  intro x
  cases f with
  | fail => simpa using h1 x
  | rest M =>
    rw [minusPM_rest]
    rcases withBot_eq_bot_or_coe (M x) with hM | ⟨mt, hM⟩
    · rw [hM, minusCost_bot_right]; exact le_top
    have hx := h1 x
    rw [minusPM_rest, hM, le_minusCost_coe_iff] at hx
    rcases withBot_eq_bot_or_coe (Q' x) with hQ | ⟨qv, hQ⟩
    · rw [hQ] at hx; simp at hx
    rw [hQ, WithBot.coe_le_coe] at hx
    rw [hM]
    refine le_minusCost_coe_iff.mpr (le_trans ?_ (h2 x qv M rfl (by rw [hM]; simp) hQ))
    exact WithBot.coe_le_coe.mpr hx

/-- The source's `gwp_conseq_0`. -/
theorem gwp_conseq_0 [AddCommMonoid γ] [Needname γ] [Drm γ] {t : γ} {f : NRest α γ}
    {Q Q' : α → WithBot γ} (h1 : ((0 : γ) : WithBot γ) ≤ gwp f Q')
    (h2 : ∀ x t'' M, f = NRest.rest M → M x ≠ ⊥ → Q' x = ((t'' : γ) : WithBot γ) →
      ((t + t'' : γ) : WithBot γ) ≤ Q x) :
    ((t : γ) : WithBot γ) ≤ gwp f Q := by
  rw [gwp_pw] at h1 ⊢
  intro x
  cases f with
  | fail => simpa using h1 x
  | rest M =>
    rw [minusPM_rest]
    rcases withBot_eq_bot_or_coe (M x) with hM | ⟨mt, hM⟩
    · rw [hM, minusCost_bot_right]; exact le_top
    have hx := h1 x
    rw [minusPM_rest, hM, le_minusCost_coe_iff] at hx
    rcases withBot_eq_bot_or_coe (Q' x) with hQ | ⟨qv, hQ⟩
    · rw [hQ] at hx; simp at hx
    rw [hQ, WithBot.coe_le_coe, zero_add] at hx
    rw [hM]
    refine le_minusCost_coe_iff.mpr (le_trans ?_ (h2 x qv M rfl (by rw [hM]; simp) hQ))
    exact WithBot.coe_le_coe.mpr (Drm.plus_left_mono _ _ _ hx)

/-- The source's `gwp_conseq4_aux2`. -/
theorem gwp_conseq4_aux2 {t t' b c a : ℕ∞} (h1 : t -ᵣ t' + b ≤ c) (h2 : t' + a ≤ b) :
    t + a ≤ c := by
  rcases eq_or_ne t ⊤ with rfl | ht
  · rw [enat_top_resSub] at h1
    have hc : c = ⊤ := top_le_iff.mp (le_trans le_self_add h1)
    rw [hc]; exact le_top
  · rw [enat_resSub_of_ne_top ht] at h1
    calc t + a ≤ (t - t' + t') + a := add_le_add le_tsub_add le_rfl
      _ = (t - t') + (t' + a) := by rw [add_assoc]
      _ ≤ (t - t') + b := add_le_add le_rfl h2
      _ ≤ c := h1

/-- The source's `gwp_conseq4_aux3`, currency by currency. -/
theorem gwp_conseq4_aux3 {t t' b c a : ACost κ ℕ∞} (h1 : t -ᵣ t' + b ≤ c)
    (h2 : t' + a ≤ b) : t + a ≤ c :=
  ACost.le_def.mpr fun k =>
    gwp_conseq4_aux2 (by simpa using ACost.le_def.mp h1 k) (by simpa using ACost.le_def.mp h2 k)

/-- The source's `gwp_conseq4`, at the source's own carrier. -/
theorem gwp_conseq4 {t t' : ACost κ ℕ∞} {f : NRest α (ACost κ ℕ∞)}
    {Q Q' : α → WithBot (ACost κ ℕ∞)}
    (h1 : ((t' : ACost κ ℕ∞) : WithBot (ACost κ ℕ∞)) ≤ gwp f Q')
    (h2 : ∀ x t'', Q' x = ((t'' : ACost κ ℕ∞) : WithBot (ACost κ ℕ∞)) →
      (((t -ᵣ t') + t'' : ACost κ ℕ∞) : WithBot (ACost κ ℕ∞)) ≤ Q x) :
    ((t : ACost κ ℕ∞) : WithBot (ACost κ ℕ∞)) ≤ gwp f Q := by
  rw [gwp_pw] at h1 ⊢
  intro x
  cases f with
  | fail => simpa using h1 x
  | rest M =>
    rw [minusPM_rest]
    rcases withBot_eq_bot_or_coe (M x) with hM | ⟨mt, hM⟩
    · rw [hM, minusCost_bot_right]; exact le_top
    have hx := h1 x
    rw [minusPM_rest, hM, le_minusCost_coe_iff] at hx
    rcases withBot_eq_bot_or_coe (Q' x) with hQ | ⟨qv, hQ⟩
    · rw [hQ] at hx; simp at hx
    rw [hQ, WithBot.coe_le_coe] at hx
    have hQx := h2 x qv hQ
    rcases withBot_eq_bot_or_coe (Q x) with hQx' | ⟨cv, hQx'⟩
    · rw [hQx'] at hQx; simp at hQx
    rw [hQx', WithBot.coe_le_coe] at hQx
    rw [hM, hQx']
    exact le_minusCost_coe_iff.mpr (WithBot.coe_le_coe.mpr (gwp_conseq4_aux3 hQx hx))


end Gwp

section Progress

variable [CompleteLattice γ]

/-! ### `progress`

The side condition the loop rule needs: a step that can produce a result
must charge something for it. -/

/-- The source's
`progress m ≡ ∀s' M. m = SPECT M ⟶ M s' ≠ None ⟶ M s' > Some 0`. -/
def progress [Zero γ] (m : NRest α γ) : Prop :=
  ∀ (s' : α) (M : α → WithBot γ), m = NRest.rest M → M s' ≠ ⊥ →
    ((0 : γ) : WithBot γ) < M s'

/-- The source's `progressD`. -/
theorem progressD [Zero γ] {m : NRest α γ} (h : progress m) {M : α → WithBot γ}
    (hm : m = NRest.rest M) (s' : α) (hs : M s' ≠ ⊥) : ((0 : γ) : WithBot γ) < M s' :=
  h s' M hm hs

/-- The source's `progress_REST_iff`, in the `single` spelling
`Basic.lean` gives `[x ↦ t]`. -/
theorem progress_rest_single [Zero γ] {t : γ} (h : (0 : γ) < t) (x : α) :
    progress (NRest.rest (NRest.single x ((t : γ) : WithBot γ)) : NRest α γ) := by
  rintro s' M hM hs
  rw [NRest.rest_inj_iff] at hM
  subst hM
  by_cases hv : s' = x
  · subst hv; rw [NRest.single_self]; exact WithBot.coe_lt_coe.mpr h
  · rw [NRest.single_of_ne hv] at hs; exact absurd rfl hs

/-- The source's `progress_SPECT_emb`. -/
theorem progress_spec [Zero γ] {P : α → Prop} {tf : α → γ} (h : ∀ x, (0 : γ) < tf x) :
    progress (NRest.spec P tf) := by
  rintro s' M hM hs
  rw [NRest.spec, NRest.rest_inj_iff] at hM
  subst hM
  by_cases hp : P s'
  · simpa [hp] using WithBot.coe_lt_coe.mpr (h s')
  · simp [hp] at hs

/-- The source's `progress_ASSERT_bind`. -/
theorem progress_assert_bind [AddMonoid γ] {Φ : Prop} {f : Unit → NRest α γ} (hΦ : Φ)
    (h : Φ → progress (f ())) : progress (NRest.bindT (NRest.assert Φ) f) := by
  rw [NRest.assert_pos hΦ, NRest.returnT_bindT]
  exact h hΦ

/-- `progress` transfers along `consume` of a `RETURNT`, which is how
the loop bodies below get it: `consume (RETURNT x) T = SPECT [x ↦ T]`. -/
theorem progress_consume_returnT [AddMonoid γ] {T : γ} (h : (0 : γ) < T) (x : α) :
    progress (NRest.consume (NRest.returnT x) T : NRest α γ) := by
  rw [NRest.consume_returnT]
  exact progress_rest_single h x

/-! ### Well-founded induction over `RECT`

`Rec.lean` deferred these to "the backwards-reasoning file, where they
are used"; here they are, from `NREST.thy`:

```isabelle
lemma wf_fp_induct:
  assumes fp: "⋀x. f x = B (f) x"  assumes wf: "wf R"
  assumes "⋀x D. ⟦⋀y. (y,x)∈R ⟹ P y (D y)⟧ ⟹ P x (B D x)"
  shows "P x (f x)"
lemma RECT_wf_induct_aux:
  assumes wf: "wf R"  assumes mono: "mono2 B"
  assumes "(⋀x D. (⋀y. (y, x) ∈ R ⟹ P y (D y)) ⟹ P x (B D x))"
  shows "P x (RECT B x)"
```
-/

/-- The source's `wf_fp_induct`. -/
theorem wf_fp_induct {β : Type} {f : α → β} {B : (α → β) → α → β} {R : α → α → Prop}
    (fp : ∀ x, f x = B f x) (wf : WellFounded R) {P : α → β → Prop}
    (step : ∀ x D, (∀ y, R y x → P y (D y)) → P x (B D x)) (x : α) : P x (f x) :=
  wf.induction (C := fun x => P x (f x)) x fun y ih => by
    show P y (f y)
    rw [fp y]
    exact step y f ih

/-- The source's `RECT_wf_induct_aux` / `RECT_wf_induct`. -/
theorem RECT_wf_induct {β : Type} [CompleteLattice β] {B : (α → β) → α → β}
    {R : α → α → Prop} (wf : WellFounded R) (hmono : mono2 B) {P : α → β → Prop}
    (step : ∀ x D, (∀ y, R y x → P y (D y)) → P x (B D x)) (x : α) : P x (RECT B x) :=
  wf_fp_induct (fun y => RECT_unfold_apply hmono y) wf step x

/-! ### The well-founded order on energies

The source's `ffSacost` and `wf_ffSacost`:

```isabelle
definition ffSacost :: "('a ⇒ (_,nat) acost) ⇒ ('a × 'a) set"
  where "ffSacost f = {(s,s')| s s'. the_acost (f s) < the_acost (f s')}"
lemma wf_ffSacost: "(⋀s. finite {x. the_acost (f s) x ≠ 0}) ⟹ wf (ffSacost f)"
```

The source's proof measures a cost by `Sum_any`; ours measures it by
`∑ᶠ`, which is the same object (`TimeRefinement.lean`, delta T4). -/

/-- The source's `za`: a strictly smaller finitely-supported `nat`
family has a strictly smaller total. -/
theorem finsum_lt_finsum {ι : Type} {g h : ι → ℕ} (hfin : {x | h x ≠ 0}.Finite)
    (hlt : g < h) : ∑ᶠ i, g i < ∑ᶠ i, h i := by
  obtain ⟨hle, hne⟩ := lt_iff_le_not_ge.mp hlt
  obtain ⟨x₀, hx₀⟩ : ∃ x, g x < h x := by
    by_contra hc
    exact hne fun x => le_of_not_gt fun hgt => hc ⟨x, hgt⟩
  have hsub : Function.support g ⊆ (hfin.toFinset : Set ι) := fun x hx => by
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact fun h0 => hx (Nat.le_zero.mp (h0 ▸ hle x))
  have hsub' : Function.support h ⊆ (hfin.toFinset : Set ι) := fun x hx => by
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact hx
  rw [finsum_eq_finsetSum_of_support_subset g hsub,
    finsum_eq_finsetSum_of_support_subset h hsub']
  refine Finset.sum_lt_sum (fun i _ => hle i) ⟨x₀, ?_, hx₀⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  omega

/-- The source's `ffSacost`, as a relation. -/
def ffSacost (f : α → ACost κ ℕ) : α → α → Prop := fun s s' => (f s).toFun < (f s').toFun

/-- The source's `wf_ffSacost`. -/
theorem wf_ffSacost {f : α → ACost κ ℕ} (h : ∀ s, NRest.wfR2 (f s)) :
    WellFounded (ffSacost f) := by
  have hm : WellFounded fun s s' : α => (∑ᶠ k, (f s).toFun k) < ∑ᶠ k, (f s').toFun k :=
    InvImage.wf (fun s => ∑ᶠ k, (f s).toFun k) (IsWellFounded.wf)
  exact Subrelation.wf (fun {s s'} hss => finsum_lt_finsum (h s') hss) hm

/-! ### The loop rules -/

open Classical in
/-- **The source's `gwp_whileT_rule_wf`**: the raw well-founded loop
rule, with the invariant carrying the remaining budget and an arbitrary
well-founded decrease. -/
theorem gwp_whileT_rule_wf [Nonempty α] {b : α → Bool} {c : α → NRest α ECost}
    {I : α → WithBot ECost} {R : α → α → Prop} {s : α} {t : ECost}
    (IS : ∀ s' t', I s' = ((t' : ECost) : WithBot ECost) → b s' = true →
      ((t' : ECost) : WithBot ECost) ≤
        gwp (c s') fun s'' => if R s'' s' then I s'' else ⊥)
    (hIs : I s = ((t : ECost) : WithBot ECost)) (wf : WellFounded R) :
    ((t : ECost) : WithBot ECost) ≤
      gwp (NRest.whileT b c s) fun x => if b x then ⊥ else I x := by
  have key : ∀ x : α, ∀ tt : ECost, I x = ((tt : ECost) : WithBot ECost) →
      ((tt : ECost) : WithBot ECost) ≤
        gwp (RECT (NRest.whileBody b c) x) fun z => if b z then ⊥ else I z := by
    intro x
    refine RECT_wf_induct (P := fun x r => ∀ tt : ECost,
      I x = ((tt : ECost) : WithBot ECost) → ((tt : ECost) : WithBot ECost) ≤
        gwp r fun z => if b z then ⊥ else I z)
      wf (NRest.mono2_whileBody b c) ?_ x
    intro y D ih tt hIy
    show ((tt : ECost) : WithBot ECost) ≤
      gwp (NRest.whileBody b c D y) fun z => if b z then ⊥ else I z
    rw [NRest.whileBody_apply]
    by_cases hb : b y = true
    · rw [if_pos hb]
      refine gwp_bindT_I (gwp_conseq (IS y tt hIy hb) ?_)
      rintro z t'' M - - hQ'
      by_cases hR : R z y
      · rw [if_pos hR] at hQ'
        exact ih z hR t'' hQ'
      · rw [if_neg hR] at hQ'
        exact absurd hQ'.symm WithBot.coe_ne_bot
    · rw [if_neg hb]
      refine gwp_RETURNT_I ?_
      simp only [Bool.not_eq_true] at hb
      show ((tt : ECost) : WithBot ECost) ≤ (if b y then ⊥ else I y)
      simp [hb, hIy]
  exact key s t hIs

/-- Pointwise arithmetic of `lift_acost` differences, the shape the loop
rule's energy bookkeeping takes. -/
theorem liftACost_sub_add_sub {A B C : ACost κ ℕ} (h1 : C ≤ B) (h2 : B ≤ A) :
    liftACost (A - B) + liftACost (B - C) = liftACost (A - C) := by
  ext k
  have hk1 := ACost.le_def.mp h1 k
  have hk2 := ACost.le_def.mp h2 k
  simp only [ACost.toFun_add, toFun_liftACost, ACost.toFun_sub, ← Nat.cast_add]
  congr 1
  omega

/-- The source's `the_acost_less_aux`: a strictly positive `lift_acost`
difference is a strict decrease of the energy. -/
theorem toFun_lt_of_liftACost_sub_pos {A B : ACost κ ℕ} (hle : B ≤ A)
    (hpos : (0 : ACost κ ℕ∞) < liftACost (A - B)) : B.toFun < A.toFun := by
  obtain ⟨-, hne⟩ := lt_iff_le_not_ge.mp hpos
  obtain ⟨k, hk⟩ : ∃ k, A.toFun k - B.toFun k ≠ 0 := by
    by_contra hc
    refine hne (ACost.le_def.mpr fun k => ?_)
    have h0 : A.toFun k - B.toFun k = 0 := not_not.mp fun h => hc ⟨k, h⟩
    simp [toFun_liftACost, ACost.toFun_sub, h0]
  refine lt_iff_le_not_ge.mpr ⟨fun j => ACost.le_def.mp hle j, fun hc => ?_⟩
  have hk2 : A.toFun k ≤ B.toFun k := hc k
  omega

open Classical in
/-- **The source's `While`** (its `[vcg_rules']` loop rule), derived
from `gwp_whileT_rule_wf` at the invariant-plus-energy instantiation.
The source reaches it through three intermediate repackagings; see the
module header, delta B6. -/
theorem While [Nonempty α] {I : α → Prop} {E : α → ACost String ℕ} {b : α → Bool}
    {C : α → NRest α ECost} {s0 : α} {t : ECost} {Q : α → WithBot ECost}
    (hwf : ∀ s, NRest.wfR2 (if I s then E s else 0))
    (hI0 : I s0)
    (hstep : ∀ s, I s → b s = true →
      ((0 : ECost) : WithBot ECost) ≤ gwp (C s) fun s' =>
        mm3 (liftACost (E s)) (if I s' then ((liftACost (E s') : ECost) : WithBot ECost) else ⊥))
    (hprog : ∀ s, progress (C s))
    (hexit : ∀ x, b x = false → I x → E x ≤ E s0 →
      (((t + liftACost (E s0 - E x) : ECost)) : WithBot ECost) ≤ Q x) :
    ((t : ECost) : WithBot ECost) ≤ gwp (NRest.whileIET I E b C s0) Q := by
  classical
  set Iw : α → WithBot ECost := fun s =>
    if I s ∧ E s ≤ E s0 then (((t + liftACost (E s0 - E s) : ECost)) : WithBot ECost) else ⊥
    with hIwdef
  have hIw : ∀ s, Iw s =
      if I s ∧ E s ≤ E s0 then (((t + liftACost (E s0 - E s) : ECost)) : WithBot ECost) else ⊥ :=
    fun _ => rfl
  have hstart : Iw s0 = ((t : ECost) : WithBot ECost) := by
    rw [hIw, if_pos (⟨hI0, le_rfl⟩ : I s0 ∧ E s0 ≤ E s0)]
    have hz : E s0 - E s0 = 0 := by ext k; simp
    rw [hz, liftACost_zero, add_zero]
  have hstepw : ∀ s' t', Iw s' = ((t' : ECost) : WithBot ECost) → b s' = true →
      ((t' : ECost) : WithBot ECost) ≤ gwp (C s') fun s'' =>
        if ffSacost (fun z => if I z then E z else 0) s'' s' then Iw s'' else ⊥ := by
    intro s t' hIws hb
    rw [hIw] at hIws
    have hc : I s ∧ E s ≤ E s0 := by
      by_contra hc
      rw [if_neg hc] at hIws
      exact absurd hIws.symm WithBot.coe_ne_bot
    rw [if_pos hc, WithBot.coe_inj] at hIws
    subst hIws
    refine gwp_conseq_0 (hstep s hc.1 hb) ?_
    intro s' t'' M hM hne hQ'
    have hIs' : I s' := by
      by_contra hIs'
      rw [if_neg hIs', mm3_bot] at hQ'
      exact absurd hQ'.symm WithBot.coe_ne_bot
    rw [if_pos hIs', mm3_coe] at hQ'
    have hEle : liftACost (E s') ≤ liftACost (E s) := by
      by_contra hEle
      rw [if_neg hEle] at hQ'
      exact absurd hQ'.symm WithBot.coe_ne_bot
    rw [if_pos hEle, WithBot.coe_inj, liftACost_resSub] at hQ'
    have hEle' : E s' ≤ E s := liftACost_le_iff.mp hEle
    have hpos : (0 : ECost) < t'' := by
      have h0 := gwp_pw.mp (hstep s hc.1 hb) s'
      rw [hM, minusPM_rest] at h0
      rcases withBot_eq_bot_or_coe (M s') with hMs | ⟨mt, hMs⟩
      · exact absurd hMs hne
      rw [hMs, if_pos hIs', mm3_coe, if_pos hEle, liftACost_resSub,
        le_minusCost_coe_iff, WithBot.coe_le_coe, zero_add] at h0
      have hprogs := progressD (hprog s) hM s' hne
      rw [hMs, WithBot.coe_lt_coe] at hprogs
      rw [← hQ']
      exact lt_of_lt_of_le hprogs h0
    have hlt : ffSacost (fun z => if I z then E z else 0) s' s := by
      show (if I s' then E s' else 0).toFun < (if I s then E s else 0).toFun
      rw [if_pos hIs', if_pos hc.1]
      exact toFun_lt_of_liftACost_sub_pos hEle' (by rw [hQ']; exact hpos)
    rw [if_pos hlt, hIw, if_pos (⟨hIs', le_trans hEle' hc.2⟩ : I s' ∧ E s' ≤ E s0),
      WithBot.coe_le_coe, ← hQ', add_assoc, liftACost_sub_add_sub hEle' hc.2]
  have hmain := gwp_whileT_rule_wf (b := b) (c := C) (I := Iw)
    (R := ffSacost fun z => if I z then E z else 0) (s := s0) (t := t)
    hstepw hstart (wf_ffSacost hwf)
  rw [NRest.whileIET_eq]
  refine le_trans hmain (gwp_mono ?_)
  rintro P x - -
  show (if b x then ⊥ else Iw x) ≤ Q x
  by_cases hb : b x = true
  · rw [if_pos (by simp [hb])]
    exact bot_le
  · simp only [Bool.not_eq_true] at hb
    rw [if_neg (by simp [hb]), hIw]
    by_cases hcx : I x ∧ E x ≤ E s0
    · rw [if_pos hcx]
      exact hexit x hb hcx.1 hcx.2
    · rw [if_neg hcx]
      exact bot_le

end Progress

/-! ### The monadic-`if` rule -/

/-- The source's `gwp_MIf_I`. The condition is a `Bool` — a value the
program computed — per `Combinators.lean`'s substrate decision C1, so
the source's `b` / `¬b` premises read `b = true` / `b = false`. -/
theorem gwp_MIf_I {b : Bool} {c1 c2 : NRest α ECost} {Q : α → WithBot ECost} {t : ECost}
    (h1 : b = true → (((ACost.cost "if" 1 + t : ECost)) : WithBot ECost) ≤ gwp c1 Q)
    (h2 : b = false → (((ACost.cost "if" 1 + t : ECost)) : WithBot ECost) ≤ gwp c2 Q) :
    ((t : ECost) : WithBot ECost) ≤ gwp (NRest.MIf b c1 c2) Q := by
  rw [NRest.MIf]
  refine gwp_consume ?_
  cases b with
  | true => simpa using h1 rfl
  | false => simpa using h2 rfl

/-- The source's `gwp_specifies_time_I`: the entry lemma against a
currency-refined specification. -/
theorem gwp_specifies_time_I {κ' : Type} [Nonempty α] {E : κ → ACost κ' ℕ∞}
    {m : NRest α (ACost κ' ℕ∞)} {Q : α → WithBot (ACost κ ℕ∞)}
    (h : ((0 : ACost κ' ℕ∞) : WithBot (ACost κ' ℕ∞)) ≤ gwp m (NRest.timerefineF E Q)) :
    m ≤ NRest.timerefine E (NRest.rest Q) := by
  rw [NRest.timerefine_rest]
  exact gwp_specifies_I h

/-! ### The `refine_vcg` attribute and tactic

Design record §3 (`named_theorems → persistent attribute + DiscrTree`)
and §10.3. This is the *seed* of the abstract VCG, and its maturity is
stated honestly in the module header: a rule-application loop with no
DiscrTree indexing, no case splitter, no `progress` prover, and no
side-condition solver.

**Substrate delta B7.** Lean forbids using an attribute in the module
that declares it (`initialize` values are not available to their own
module). The ported rules therefore sit in `RefineVcg.coreRules`, a list
the tactic tries first, and `@[refine_vcg]` extends that set from
*downstream* modules — which is where P2–P6's rules will live anyway.
Isabelle's `named_theorems` has no such restriction; this is a pure
substrate cost, recorded rather than worked around. -/

register_label_attr refine_vcg

namespace RefineVcg

/-- The rules `refine_vcg` tries before consulting the `@[refine_vcg]`
database: the ported `[vcg_rules']` set, most specific first. -/
def coreRules : List Lean.Name :=
  [``gwp_ASSERT_bind_I, ``gwp_ASSERT_I, ``gwp_MIf_I, ``While, ``gwp_bindT_I,
    ``gwp_consume, ``gwp_RETURNT_I, ``gwp_SPECT_I, ``gwp_SPECT_emb_I, ``gwp_If_I]

end RefineVcg

open Lean Elab Tactic Meta in
/-- One step of `refine_vcg`: apply the first rule — core set first,
then the `@[refine_vcg]` database — whose conclusion matches the goal,
leaving its premises as goals. -/
elab "refine_vcg_step" : tactic => do
  -- delta B7: in the declaring module the attribute does not yet exist,
  -- so an empty extension is the honest answer there.
  let extra ← (try labelled `refine_vcg catch _ => pure #[])
  let goal ← getMainGoal
  for n in RefineVcg.coreRules ++ extra.toList do
    let st ← saveState
    try
      let gs ← goal.apply (← mkConstWithFreshMVarLevels n)
      replaceMainGoal gs
      return
    catch _ => restoreState st
  throwError "refine_vcg: no rule applies to this goal"

open Lean Elab Tactic Meta in
/-- Peel one binder, but only when the goal is *syntactically* a
quantifier. Plain `intro` would happily unfold a definition to expose
one — `progress m` is a `∀` under its own name — which is not what a
side condition wants. -/
elab "refine_vcg_intro" : tactic => do
  let goal ← getMainGoal
  match ← instantiateMVars (← goal.getType) with
  | .forallE .. => let (_, g) ← goal.intro1; replaceMainGoal [g]
  | _ => throwError "refine_vcg: the goal is not a quantifier"

/-- The abstract VCG, seed version: peel binders and apply `gwp` rules
until nothing matches, leaving the side conditions as goals. -/
macro "refine_vcg" : tactic => `(tactic| repeat' (first | refine_vcg_intro | refine_vcg_step))

/-! ### The executable gate (design record ledger D4)

`gwp` is `noncomputable` twice over — the classical `if` inside
`minus_cost` and `sInf` — so the route is the campaign's standard one:
executable twins with *proved* agreement, so that a `#guard` about the
twin is a `#guard` about `gwp`. The carrier is `Sanity.lean`'s
`NRest (Fin 3) ℕ∞`.

The recorded counterexample of delta B1 — mathlib's `Sub ℕ∞` and
Isabelle's `enat` subtraction disagree at `⊤ - ⊤`, which is exactly the
point the `needname` axiom `top - a = top` lives at — travelled with
`ResSub` to `Cost/ACost.lean` in P2 wave A (delta B2); it is the four
`#guard`s at the head of that file. -/

namespace Sanity

open Plausible

/-- Executable `⊓` on `WithBot ℕ∞`, decided by the (computable) order. -/
def minE (u v : WithBot ℕ∞) : WithBot ℕ∞ := if u ≤ v then u else v

theorem minE_eq (u v : WithBot ℕ∞) : minE u v = u ⊓ v := by
  rw [minE]
  split
  · exact (inf_eq_left.mpr ‹_›).symm
  · exact (inf_eq_right.mpr (le_of_not_ge ‹_›)).symm

/-- Executable `⊔` on `WithBot ℕ∞`. -/
def maxE (u v : WithBot ℕ∞) : WithBot ℕ∞ := if u ≤ v then v else u

theorem maxE_eq (u v : WithBot ℕ∞) : maxE u v = u ⊔ v := by
  rw [maxE]
  split
  · exact (sup_eq_right.mpr ‹_›).symm
  · exact (sup_eq_left.mpr (le_of_not_ge ‹_›)).symm

/-- Executable `minus_cost` at the gate carrier. -/
def minusCostE (r m : WithBot ℕ∞) : WithBot ℕ∞ :=
  m.recBotCoe ((⊤ : ℕ∞) : WithBot ℕ∞) fun mt =>
    r.recBotCoe ⊥ fun rt => if mt ≤ rt then ((rt -ᵣ mt : ℕ∞) : WithBot ℕ∞) else ⊥

/-- **The bridge for `minus_cost`.** -/
theorem minusCostE_eq (r m : WithBot ℕ∞) : minusCostE r m = minusCost r m := by
  rcases withBot_eq_bot_or_coe m with rfl | ⟨mt, rfl⟩
  · rfl
  rcases withBot_eq_bot_or_coe r with rfl | ⟨rt, rfl⟩
  · rfl
  · rw [minusCostE, minusCost_coe]
    simp only [WithBot.recBotCoe_coe]
    split <;> rfl

/-- `⨅` over `Fin 3`, unfolded — the shape `gwpE` computes in
(`Sanity.lean` proves the `⨆` twin). -/
theorem iInf_fin3 {A : Type} [CompleteLattice A] (g : Fin 3 → A) :
    (⨅ i, g i) = g 0 ⊓ g 1 ⊓ g 2 := by
  refine le_antisymm (le_inf (le_inf (iInf_le g 0) (iInf_le g 1)) (iInf_le g 2))
    (le_iInf fun i => ?_)
  fin_cases i
  · exact le_trans inf_le_left inf_le_left
  · exact le_trans inf_le_left inf_le_right
  · exact inf_le_right

/-- Executable `gwp` at the gate carrier. -/
def gwpE (M : SRest) (Q : Fin 3 → WithBot ℕ∞) : WithBot ℕ∞ :=
  match M with
  | .fail => ⊥
  | .rest X =>
    minE (minE (minusCostE (Q 0) (X 0)) (minusCostE (Q 1) (X 1))) (minusCostE (Q 2) (X 2))

/-- **The bridge.** Everything `#guard`ed and `#test`ed below is checked
about `gwp` itself. -/
theorem gwpE_eq (M : SRest) (Q : Fin 3 → WithBot ℕ∞) : gwpE M Q = gwp M Q := by
  cases M with
  | fail =>
    rw [gwpE, gwp]
    simp only [minusPM_fail]
    exact (iInf_const).symm
  | rest X =>
    rw [gwpE, gwp, iInf_fin3, minE_eq, minE_eq, minusCostE_eq, minusCostE_eq, minusCostE_eq]
    rfl

/-- A sample allowance: result `0` is free, result `1` costs at most
`3`, result `2` is forbidden. -/
def sampleQ : Fin 3 → WithBot ℕ∞ := ![((0 : ℕ∞) : WithBot ℕ∞), ((3 : ℕ∞) : WithBot ℕ∞), ⊥]

-- `RETURNT 1` fits inside an allowance of `3` with `3` to spare, and a
-- program that may deliver the forbidden result `2` is unaffordable.
#guard gwpE (returnE 1) sampleQ = ((3 : ℕ∞) : WithBot ℕ∞)
#guard gwpE (returnE 0) sampleQ = ((0 : ℕ∞) : WithBot ℕ∞)
#guard gwpE (returnE 2) sampleQ = ⊥
#guard gwpE (.rest ![⊥, ((1 : ℕ∞) : WithBot ℕ∞), ⊥]) sampleQ = ((2 : ℕ∞) : WithBot ℕ∞)
#guard gwpE (NRest.fail : SRest) sampleQ = ⊥
-- a program with no results at all is free
#guard gwpE (.rest ![⊥, ⊥, ⊥]) sampleQ = ((⊤ : ℕ∞) : WithBot ℕ∞)

/-- Sampling for allowances, reusing `Sanity.lean`'s pair-list proxy. -/
def qOfProxy (l : List (ℕ × ℕ)) : Fin 3 → WithBot ℕ∞ := mapOfPairs l

-- `gwp_specifies_I` and its converse, run against sampled data:
-- `Some 0 ≤ gwp m Q` is exactly `m ≤ SPECT Q`.
#test ∀ (M : SRest) (l : List (ℕ × ℕ)),
  (((0 : ℕ∞) : WithBot ℕ∞) ≤ gwpE M (qOfProxy l)) = (M ≤ NRest.rest (qOfProxy l))

-- `gwp_antimono`: a refined program is at least as affordable.
#test ∀ (M M' : SRest) (l : List (ℕ × ℕ)),
  M ≤ M' → gwpE M' (qOfProxy l) ≤ gwpE M (qOfProxy l)

-- `gwp_bindT`, the hardest ported statement, run end to end.
#test ∀ (M f₀ f₁ f₂ : SRest) (l : List (ℕ × ℕ)),
  gwpE (bindE M ![f₀, f₁, f₂]) (qOfProxy l)
    = gwpE M fun y => gwpE (![f₀, f₁, f₂] y) (qOfProxy l)

-- `gwp_consume`: charging `T` up front costs exactly `T` of the budget.
#test ∀ (M : SRest) (c : ℕ) (l : List (ℕ × ℕ)),
  (((c : ℕ∞) : WithBot ℕ∞) ≤ gwpE (NRest.consume M ((c : ℕ∞))) (qOfProxy l))
    = (((c : ℕ∞) + (c : ℕ∞) : ℕ∞) ≤ gwpE M (qOfProxy l))

-- `gwp_mono`: a laxer allowance is at least as affordable (the premise
-- is met by construction, via the executable join).
#test ∀ (M : SRest) (l l' : List (ℕ × ℕ)),
  gwpE M (qOfProxy l) ≤ gwpE M fun i => maxE (qOfProxy l i) (qOfProxy l' i)

/-! ### The end-to-end demo

A counted countdown loop, proved to refine an explicit-cost `SPEC` by
`gwp_specifies_I` + the `refine_vcg` tactic. The invariant and the
energy annotation are supplied by hand on the `whileIET` term, exactly
as the source's methodology prescribes; every side condition the tactic
leaves is closed by `simp`/`omega`. -/

/-- One iteration: step down, paying one `''step''` unit. -/
noncomputable def demoBody (s : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT (s - 1)) (ACost.cost "step" 1)

/-- Keep going until `0`. -/
def demoCond (s : ℕ) : Bool := decide (s ≠ 0)

/-- The energy annotation: `s` steps left. -/
def demoE (s : ℕ) : ACost String ℕ := ACost.cost "step" s

/-- The counted countdown loop, with its invariant and energy attached
so the VCG can read them off the term. -/
noncomputable def demoLoop (n : ℕ) : NRest ℕ ECost :=
  NRest.whileIET (fun _ => True) demoE demoCond demoBody n

theorem cost_step_pos : (0 : ECost) < ACost.cost "step" (1 : ℕ∞) := by
  refine lt_iff_le_not_ge.mpr ⟨Nonneg.needname_nonneg _, fun hc => ?_⟩
  have := ACost.le_def.mp hc "step"
  simp at this

/-- **The demo.** `demoLoop n` refines "return `0`, having spent exactly
`n` `''step''` units". -/
theorem demoLoop_spec (n : ℕ) :
    demoLoop n ≤ NRest.spec (fun x => x = 0) fun _ => ACost.cost "step" (n : ℕ∞) := by
  refine gwp_specifies_I ?_
  rw [demoLoop]
  refine_vcg
  · -- the energy annotation is finitely supported
    rename_i s
    simpa [demoE] using NRest.wfR2_cost (κ := String) (γ := ℕ) "step" s
  · -- the invariant holds at the start
    trivial
  · -- what the tactic left of the step: one `''step''` unit buys one
    -- unit of energy
    rename_i s _ hb
    simp only [demoCond, decide_eq_true_eq, ne_eq] at hb
    simp only [demoE, liftACost_cost, if_pos trivial, mm3_coe, add_zero]
    have hle : (ACost.cost "step" (((s - 1 : ℕ) : ℕ∞)) : ECost)
        ≤ ACost.cost "step" ((s : ℕ) : ℕ∞) := by
      refine ACost.le_def.mpr fun k => ?_
      rcases eq_or_ne k "step" with rfl | hk
      · rw [ACost.toFun_cost_self, ACost.toFun_cost_self, Nat.cast_le]
        omega
      · rw [ACost.toFun_cost_ne hk, ACost.toFun_cost_ne hk]
    rw [if_pos hle]
    refine WithBot.coe_le_coe.mpr (ACost.le_def.mpr fun k => ?_)
    rw [ACost.toFun_resSub]
    rcases eq_or_ne k "step" with rfl | hk
    · rw [ACost.toFun_cost_self, ACost.toFun_cost_self, ACost.toFun_cost_self,
        enat_resSub_of_ne_top (by simp), ← ENat.coe_sub,
        show s - (s - 1) = 1 from by omega]
      simp
    · rw [ACost.toFun_cost_ne hk, ACost.toFun_cost_ne hk, ACost.toFun_cost_ne hk]
      simp
  · -- the body makes progress
    exact progress_consume_returnT cost_step_pos _
  · -- on exit the spent energy is exactly the advertised cost
    rename_i x hb _ _
    simp only [demoCond, decide_eq_false_iff_not, ne_eq, not_not] at hb
    subst hb
    have hz : demoE n - demoE 0 = demoE n := by
      ext k; simp [demoE]
    rw [hz]
    simp [demoE]

end Sanity

end Lax13Proofs.Refine
