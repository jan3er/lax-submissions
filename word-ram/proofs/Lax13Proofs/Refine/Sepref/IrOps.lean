import Lax13Proofs.Refine.Sepref.Attrs
import Lax13Proofs.Refine.Sepref.Basic
import Lax13Proofs.Refine.NREST.Combinators
import Lax13Proofs.Refine.NREST.TimeRefinement

/-!
The ir-currency operation layer: the abstract `mop_…` operations of the
IR's op set, and the `hn_refine` rule for each.

Provenance. The *layer* is the artifact's
(`thys/sepref/…`+`thys/nrest/Monadic_Operations.thy`, pin
`isabelle_llvm_time` @ `42dd7f5` per `plans/word-ram/refinement-tower/design.md`
§1): an interface operation `mop_x` that asserts its precondition and
`consume`s an explicit cost, plus one `hn_refine` rule per operation
registered in `sepref_fr_rules`. The *content* is ours, and flagged: the
artifact's `mop_…`s take their cost as a parameter (`mop_array_nth`'s
`cost ''load'' 1` is supplied by the IICF instance), while ours are
**pinned to the IR's own currencies** — design record F4, "cost
currencies survive down to the IR (per-op currencies); collapsing to a
single time unit happens once, in P5's cashing theorem". So there is one
`mop` per IR op, at the currency `Ir/Syntax.lean` declares for that op,
and no cost parameter anywhere.

What each rule is checked against: `Ir/Triples.lean`'s per-op triple
(itself the port of `ll_load_rule`/`ll_store_rule`, p3-sl-deep-extracts
§5) composed with `Sepref/Basic.lean`'s `hnRefineI_spect` (the source's
`hn_refineI_SPECT`). The `hnCtxt` discipline of the statements is the
source's (`hn_ctxt` keeps frame matching syntax-directed —
p4-sepref-extracts §3), and it is what wave C's frame inferencer will
consume.

## Judgment calls (P4/D-aa … , continuing `Basic.lean`'s D-a … D-p)

`P4/D-aa` is in `Sepref/Attrs.lean` (where the three rule databases are
declared).

**P4/D-ab — the destination is a `junkCell` in the precondition, not an
allocation.** The source's per-op rules deliver their result into a
*fresh* SSA register that the shallow monad conjures (`hn_refine … (f c)`
returns a value). Our IR is three-address over a fixed name space with no
allocation (design record §6, ledger D2), so the destination cell must
already exist and be owned: every rule whose destination is a scratch
cell takes `junkCell x` in the precondition and returns
`natAssn v x` in the judgment's result slot. This is what wave A's
P4/D-c/P4/D-f anticipated ("a cell owned at the start of a run is owned
at its end"), and it is the exact place where the substrate's
no-allocation property is paid for: the *caller* owns the scratch cell,
so wave C's translate phase must supply a scratch name rather than a
fresh register (handoff note, §6). Fallback: none needed — `junkCell` is
`deadAssn natAssn` (`Basic.lean`'s `deadAssn_natAssn_eq_junkCell`), so a
temporary invalidated by an earlier op is *already* in the shape the next
op's precondition wants.

**P4/D-ac — no name-distinctness side conditions.** `∗` on cell
assertions is already false when two names coincide
(`Assn.lean`'s `ptoVar_sepConj_self`), so `hnr_mop_binop` needs no
`x ≠ y`: the rule is simply inapplicable in the aliased case. This is
P3's judgment call D-w, inherited. Where in-place update is *wanted* —
`i := i + one`, every loop's step — the aliased instance is its own rule
(`hnr_mop_binop_self`, off P3's `binop_self_triple`), destructive in `x`
exactly as `hnr_mop_aset` is destructive in the array.

**P4/D-ad — `irWhileIT` is `monadic_WHILEIT` at a *pure* guard and the
`ir.while` currency, defined through the source's own `RECT'` shape.**
The source's `monadic_WHILEIT I b f s` (a) takes the guard as a
*computation* `b : α ⇒ (bool,_) nrest`, (b) pays `cost ''call'' 1` on
entry and per iteration, and (c) routes the branch through `MIf`, which
pays `cost ''if'' 1` as well. The IR's `while` op evaluates a
*structural* `Ir.Cond` and charges one `ir.while` per guard evaluation
and nothing else (P3 ledger D-h): `n` iterations charge `n + 1`. So
`irWhileIT` keeps (b) verbatim at `Currency.«while»` — this is the shape
`RECT'` has (`Rec.lean`, the source's `RECT'`: one unit on entry and one
per recursive call), with the currency a parameter instead of the
hard-wired `''call''` — and drops (a) and (c), which have no IR
counterpart. The invariant `assert (I s)` stays exactly where the source
puts it, and is load-bearing: `hnr_while_measured` reads `I s` *off the
abstract program's non-failure*, so no `INV` premise is needed
(`CombRules.lean`, P4/D-ai).

**P4/D-ae — the branch exchange is an equality, the loop exchange an
inequality with a variant.** §4 proves
`timerefine E (MIf b t e) = irIf b (timerefine E t) (timerefine E e)`
as an *equality*, at general `E` with the two hypotheses the equality
needs (`wfR'' E`, `E "if" = ACost.cost Currency.ite 1`): `⇓C` commutes
with `consume` exactly (P1's `timerefine_consume`), so no inequality
creeps in. §5 proves the `monadic_WHILEIT` analogue as
`irWhileIT … ≤ timerefine E (monadicWhileIT …)` — the *useful* direction,
since `hnRefine_ref` is monotone upward in the abstract program — under
`E "call" = ACost.cost Currency.while 1` and a variant `V`, and the two
reasons it cannot be an equality are recorded there (the source's loop
also pays `''if''` per iteration; `⇓C` through `bindT` is
`timerefine_bindT_ge`, an inequality, because `bindT` is a supremum and
`⇓C` is not supremum-continuous — P1 delta T7). The variant premise is
the same one `CombRules.lean`'s loop rule takes, for the same reason
(P4/D-ai). Both are also available at the concrete map `irE` (§4), which
is all the acceptance needs. Three helper lemmas that P1 does not export
are proved in §5 and belong upstream — result-guarded `bindT`
monotonicity, `mono2` for `monadicWhileBody`, and the pure-guard
unfolding; moving them is a backlog item with no proof content.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. The mop layer

One abstract operation per IR op: assert what the op needs, return what
it computes, `consume` the op's own currency. These are the terms wave
C's operator-identification phase will register, and the terms a user
program is written in. -/

/-- One unit of a currency, as an `ECost`. The `¤¤`-facing form of the
same cost: `costCredits_one` below is the bridge. -/
abbrev irUnit (n : String) : ECost := ACost.cost n 1

/-- `¤¤n 1` and `¤(irUnit n)` are the same assertion — the `ℕ`-versus-`ℕ∞`
seam of `Assn.lean`'s `costCredits`, closed once. -/
theorem costCredits_one (n : String) : (¤¤n 1) = ¤(irUnit n) := by
  rw [costCredits_def]
  norm_num

/-- `x := y ⊕ z` at the abstract level: the value is IMP+'s own
`Bop.apply` and the price is `binopCurrency op`, so no operator can drift
between this operation, the semantics, the triple and P5's lowering. -/
noncomputable def mopBinop (op : Imp.Bop) (m n : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT (op.apply m n)) (irUnit (binopCurrency op))

/-- `x := a[i]`: guarded by the index bound, priced at `ir.aget`. -/
noncomputable def mopAget (xs : List ℕ) (i : ℕ) : NRest ℕ ECost :=
  NRest.bindT (NRest.assert (i < xs.length)) fun _ =>
    NRest.consume (NRest.returnT xs[i]!) (irUnit Currency.aget)

/-- `a[i] := v`: guarded by the index bound, priced at `ir.aset`. The
result is the updated list — the array's ownership *moves*, which is what
makes this the linearity showcase (`hnr_mop_aset`). -/
noncomputable def mopAset (xs : List ℕ) (i v : ℕ) : NRest (List ℕ) ECost :=
  NRest.bindT (NRest.assert (i < xs.length)) fun _ =>
    NRest.consume (NRest.returnT (xs.set i v)) (irUnit Currency.aset)

/-- `x := y`, priced at `ir.copy`. -/
noncomputable def mopCopy (v : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT v) (irUnit Currency.copy)

/-- `x := n`, priced at `ir.const`. -/
noncomputable def mopConstN (n : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT n) (irUnit Currency.const)

/-- The source's `MIf` at the IR's branch currency (P4/D-ad): take a
branch, pay one `ir.ite`. -/
noncomputable def irIf {α : Type} (b : Bool) (t e : NRest α ECost) : NRest α ECost :=
  NRest.consume (if b then t else e) (irUnit Currency.ite)

@[simp] theorem irIf_true {α : Type} (t e : NRest α ECost) :
    irIf true t e = NRest.consume t (irUnit Currency.ite) := by simp [irIf]

@[simp] theorem irIf_false {α : Type} (t e : NRest α ECost) :
    irIf false t e = NRest.consume e (irUnit Currency.ite) := by simp [irIf]

/-! ### The loop combinator

`monadic_WHILEIT`'s shape at a pure guard and the `ir.while` currency
(P4/D-ad). The body functional is the source's, minus the guard
computation and the `MIf`; the entry-and-per-call payment is `RECT'`'s,
with the currency a parameter. -/

/-- The body functional of `irWhileIT`: assert the invariant, and on
`true` run one iteration and recurse. -/
noncomputable def irWhileBody {σ : Type} (I : σ → Prop) (bf : σ → Bool)
    (f : σ → NRest σ ECost) : (σ → NRest σ ECost) → σ → NRest σ ECost :=
  fun D s =>
    NRest.bindT (NRest.assert (I s)) fun _ =>
      if bf s then NRest.bindT (f s) D else NRest.returnT s

@[simp] theorem irWhileBody_apply {σ : Type} (I : σ → Prop) (bf : σ → Bool)
    (f : σ → NRest σ ECost) (D : σ → NRest σ ECost) (s : σ) :
    irWhileBody I bf f D s =
      NRest.bindT (NRest.assert (I s)) fun _ =>
        if bf s then NRest.bindT (f s) D else NRest.returnT s := rfl

/-- The `RECT` side condition for the loop body: `bindT_flatGe` /
`bindT_mono` through `monotoneRel_ite`, exactly as `mono2_whileBody`. -/
theorem mono2_irWhileBody {σ : Type} (I : σ → Prop) (bf : σ → Bool)
    (f : σ → NRest σ ECost) : mono2 (irWhileBody I bf f) := by
  refine ⟨monotoneRel_funOrd fun _ _ s hfg => ?_, monotone_of_apply fun _ _ s hfg => ?_⟩
  · exact NRest.bindT_flatGe (flatOrd_refl _ _)
      (fun _ => monotoneRel_ite (bf s = true)
        (NRest.bindT_flatGe (flatOrd_refl _ _) fun y => hfg y) (flatOrd_refl _ _))
  · exact NRest.bindT_mono le_rfl
      (fun _ => monotoneRel_ite (bf s = true)
        (NRest.bindT_mono le_rfl fun y => hfg y) le_rfl)

/-- `monadic_WHILEIT` at the IR (P4/D-ad): one `ir.while` unit on entry
and one per iteration entered, so `n` iterations pay `n + 1` — exactly
the `n + 1` guard evaluations the IR's `while` charges (P3 ledger D-h). -/
noncomputable def irWhileIT {σ : Type} (I : σ → Prop) (bf : σ → Bool)
    (f : σ → NRest σ ECost) (s : σ) : NRest σ ECost :=
  NRest.consume
    (RECT (fun D s => irWhileBody I bf f
      (fun y => NRest.consume (D y) (irUnit Currency.«while»)) s) s)
    (irUnit Currency.«while»)

/-- **The one-step unfolding.** The source's `RECT'_unfold` at the
`ir.while` currency: the payment on entry, then the body, whose recursive
call is again a whole `irWhileIT`. -/
theorem irWhileIT_unfold {σ : Type} (I : σ → Prop) (bf : σ → Bool)
    (f : σ → NRest σ ECost) (s : σ) :
    irWhileIT I bf f s =
      NRest.consume (irWhileBody I bf f (fun y => irWhileIT I bf f y) s)
        (irUnit Currency.«while») := by
  have h2 := mono2_consume_call (mono2_irWhileBody I bf f) (irUnit Currency.«while»)
  simp only [irWhileIT]
  conv_lhs => rw [RECT_unfold_apply h2]

/-- The loop, one step, with the guard `true`: pay the entry unit, run the
body, recurse. -/
theorem irWhileIT_of_true {σ : Type} {I : σ → Prop} {bf : σ → Bool}
    {f : σ → NRest σ ECost} {s : σ} (hI : I s) (hb : bf s = true) :
    irWhileIT I bf f s =
      NRest.consume (NRest.bindT (f s) fun s' => irWhileIT I bf f s')
        (irUnit Currency.«while») := by
  rw [irWhileIT_unfold, irWhileBody_apply, NRest.assert_pos hI, NRest.returnT_bindT, hb, if_pos rfl]

/-- …and with the guard `false`: pay the entry unit and stop. -/
theorem irWhileIT_of_false {σ : Type} {I : σ → Prop} {bf : σ → Bool}
    {f : σ → NRest σ ECost} {s : σ} (hI : I s) (hb : bf s = false) :
    irWhileIT I bf f s = NRest.consume (NRest.returnT s) (irUnit Currency.«while») := by
  rw [irWhileIT_unfold, irWhileBody_apply, NRest.assert_pos hI, NRest.returnT_bindT, hb]
  simp

/-- A loop whose invariant fails at the current state *fails*, which is
what makes `hnRefine` vacuous there — the vacuity `CombRules.lean`'s gate
pins explicitly. -/
theorem irWhileIT_of_not_inv {σ : Type} {I : σ → Prop} {bf : σ → Bool}
    {f : σ → NRest σ ECost} {s : σ} (hI : ¬ I s) :
    irWhileIT I bf f s = NRest.fail := by
  rw [irWhileIT_unfold, irWhileBody_apply, NRest.assert_neg hI, NRest.bindT_fail,
    NRest.consume_fail]

/-- `consume` never turns a failure into a success, nor the other way. -/
theorem nofailT_consume_iff {α : Type} {m : NRest α ECost} {t : ECost} :
    (NRest.consume m t).nofailT ↔ m.nofailT := by
  cases m with
  | fail => simp [NRest.consume_fail]
  | rest X => simp [NRest.consume_rest]

/-! ### Equation lemmas

Each `mop` is a definition over `bindT`/`consume`; the equations are
recorded immediately so that no proof below has to `unfold`. They are
*not* `simp` lemmas: the rules of §3 match on the `mop` heads, which is
what makes wave C's lookup syntax-directed. -/

theorem mopBinop_def (op : Imp.Bop) (m n : ℕ) :
    mopBinop op m n =
      NRest.consume (NRest.returnT (op.apply m n)) (irUnit (binopCurrency op)) := rfl

theorem mopAget_def (xs : List ℕ) (i : ℕ) :
    mopAget xs i =
      NRest.bindT (NRest.assert (i < xs.length)) fun _ =>
        NRest.consume (NRest.returnT xs[i]!) (irUnit Currency.aget) := rfl

theorem mopAset_def (xs : List ℕ) (i v : ℕ) :
    mopAset xs i v =
      NRest.bindT (NRest.assert (i < xs.length)) fun _ =>
        NRest.consume (NRest.returnT (xs.set i v)) (irUnit Currency.aset) := rfl

theorem mopCopy_def (v : ℕ) : mopCopy v = NRest.consume (NRest.returnT v) (irUnit Currency.copy) :=
  rfl

theorem mopConstN_def (n : ℕ) :
    mopConstN n = NRest.consume (NRest.returnT n) (irUnit Currency.const) := rfl

theorem irIf_def {α : Type} (b : Bool) (t e : NRest α ECost) :
    irIf b t e = NRest.consume (if b then t else e) (irUnit Currency.ite) := rfl

/-! ## 2. The triples behind the rules

One `irHtriple` per operation, in the shape `hnRefineI_spect` consumes:
`¤t ∗ Γ` in front (the abstract side pays `t`), `Γ' ∗ R a d` behind.
Each is P3's own per-op triple, permuted — `ac_rfl` on `∗` — with the
destination's old contents eliminated by `irHtriple_junk` (P4/D-ab). -/

/-- Eliminating a `junkCell` from a triple's precondition: the
destination's old contents are existentially quantified, while every
per-op triple of `Ir/Triples.lean` is stated at a named old value. -/
theorem irHtriple_junk {x : String} {P Q : Assn} {c : Com}
    (h : ∀ v : Val, irHtriple ((x ↦ᵥ v) ∗ P) c Q) : irHtriple (junkCell x ∗ P) c Q := by
  intro F p hp
  rw [sepConj_assoc, junkCell_def, sepEx_sepConj] at hp
  obtain ⟨v, hv⟩ := hp
  exact h v F p (by rw [sepConj_assoc]; exact hv)

/-- P3's `binop_triple`, in rule shape: the two operands stay owned, the
destination is overwritten. -/
theorem binop_junk_rule (op : Imp.Bop) (x y z : String) (m n : ℕ) :
    irHtriple (¤(irUnit (binopCurrency op)) ∗
        (junkCell x ∗ hnCtxt natAssn m y ∗ hnCtxt natAssn n z))
      (.binop op x y z)
      ((hnCtxt natAssn m y ∗ hnCtxt natAssn n z) ∗ natAssn (op.apply m n) x) := by
  have e₁ : (¤(irUnit (binopCurrency op)) ∗
      (junkCell x ∗ hnCtxt natAssn m y ∗ hnCtxt natAssn n z))
      = junkCell x ∗ (¤(irUnit (binopCurrency op)) ∗
        hnCtxt natAssn m y ∗ hnCtxt natAssn n z) := by ac_rfl
  rw [e₁]
  refine irHtriple_junk fun v => ?_
  have e₂ : ((x ↦ᵥ v) ∗ (¤(irUnit (binopCurrency op)) ∗
      hnCtxt natAssn m y ∗ hnCtxt natAssn n z))
      = (¤¤(binopCurrency op) 1 ∗ x ↦ᵥ v ∗ y ↦ᵥ m ∗ z ↦ᵥ n) := by
    rw [costCredits_one]; simp only [hnCtxt_def, natAssn_def]; ac_rfl
  have e₃ : ((hnCtxt natAssn m y ∗ hnCtxt natAssn n z) ∗ natAssn (op.apply m n) x)
      = (x ↦ᵥ op.apply m n ∗ y ↦ᵥ m ∗ z ↦ᵥ n) := by
    simp only [hnCtxt_def, natAssn_def]; ac_rfl
  rw [e₂, e₃]
  exact (binop_triple op x y z v m n).gc

/-- P3's `binop_self_triple`, in rule shape: `x := x ⊕ z`, destructive in
`x` (P4/D-ac). -/
theorem binop_self_mop_rule (op : Imp.Bop) (x z : String) (m n : ℕ) :
    irHtriple (¤(irUnit (binopCurrency op)) ∗ (hnCtxt natAssn m x ∗ hnCtxt natAssn n z))
      (.binop op x x z) (hnCtxt natAssn n z ∗ natAssn (op.apply m n) x) := by
  have e₂ : (¤(irUnit (binopCurrency op)) ∗ (hnCtxt natAssn m x ∗ hnCtxt natAssn n z))
      = (¤¤(binopCurrency op) 1 ∗ x ↦ᵥ m ∗ z ↦ᵥ n) := by
    rw [costCredits_one]; simp only [hnCtxt_def, natAssn_def]
  have e₃ : (hnCtxt natAssn n z ∗ natAssn (op.apply m n) x)
      = (x ↦ᵥ op.apply m n ∗ z ↦ᵥ n) := by
    simp only [hnCtxt_def, natAssn_def]; ac_rfl
  rw [e₂, e₃]
  exact (binop_self_triple op x z m n).gc

/-- P3's `aget_triple`, in rule shape: the array and the index stay owned
(a read consumes neither), the destination is overwritten. -/
theorem aget_junk_rule (x a i : String) (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    irHtriple (¤(irUnit Currency.aget) ∗
        (junkCell x ∗ hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i))
      (.aget x a i)
      ((hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i) ∗ natAssn xs[k]! x) := by
  have hval : xs[k]! = xs[k] := getElem!_pos xs k hk
  have hw : xs[k]? = some xs[k]! := by rw [hval, List.getElem?_eq_getElem hk]
  have e₁ : (¤(irUnit Currency.aget) ∗
      (junkCell x ∗ hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i))
      = junkCell x ∗ (¤(irUnit Currency.aget) ∗
        hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i) := by ac_rfl
  rw [e₁]
  refine irHtriple_junk fun v => ?_
  have e₂ : ((x ↦ᵥ v) ∗ (¤(irUnit Currency.aget) ∗
      hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i))
      = (¤¤Currency.aget 1 ∗ x ↦ᵥ v ∗ a ↦ₐ xs ∗ i ↦ᵥ k) := by
    rw [costCredits_one]; simp only [hnCtxt_def, natAssn_def, arrayAssn_def]; ac_rfl
  have e₃ : ((hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i) ∗ natAssn xs[k]! x)
      = (x ↦ᵥ xs[k]! ∗ a ↦ₐ xs ∗ i ↦ᵥ k) := by
    simp only [hnCtxt_def, natAssn_def, arrayAssn_def]; ac_rfl
  rw [e₂, e₃]
  exact (aget_triple x a i v k xs[k]! xs hw).gc

/-- P3's `aset_triple`, in rule shape: **destructive**. The array's
ownership at `xs` does not survive — it *is* the result, at `xs.set k n`,
delivered in the judgment's result slot at the destination `a`. -/
theorem aset_mop_rule (a i v : String) (xs : List ℕ) (k n : ℕ) (hk : k < xs.length) :
    irHtriple (¤(irUnit Currency.aset) ∗
        (hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i ∗ hnCtxt natAssn n v))
      (.aset a i v)
      ((hnCtxt natAssn k i ∗ hnCtxt natAssn n v) ∗ arrayAssn (xs.set k n) a) := by
  have e₂ : (¤(irUnit Currency.aset) ∗
      (hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i ∗ hnCtxt natAssn n v))
      = (¤¤Currency.aset 1 ∗ a ↦ₐ xs ∗ i ↦ᵥ k ∗ v ↦ᵥ n) := by
    rw [costCredits_one]; simp only [hnCtxt_def, natAssn_def, arrayAssn_def]
  have e₃ : ((hnCtxt natAssn k i ∗ hnCtxt natAssn n v) ∗ arrayAssn (xs.set k n) a)
      = (a ↦ₐ xs.set k n ∗ i ↦ᵥ k ∗ v ↦ᵥ n) := by
    simp only [hnCtxt_def, natAssn_def, arrayAssn_def]; ac_rfl
  rw [e₂, e₃]
  exact (aset_triple a i v k n xs hk).gc

/-- P3's `copy_triple`, in rule shape: the source cell stays owned. -/
theorem copy_junk_rule (x y : String) (w : ℕ) :
    irHtriple (¤(irUnit Currency.copy) ∗ (junkCell x ∗ hnCtxt natAssn w y))
      (.copy x y) (hnCtxt natAssn w y ∗ natAssn w x) := by
  have e₁ : (¤(irUnit Currency.copy) ∗ (junkCell x ∗ hnCtxt natAssn w y))
      = junkCell x ∗ (¤(irUnit Currency.copy) ∗ hnCtxt natAssn w y) := by ac_rfl
  rw [e₁]
  refine irHtriple_junk fun v => ?_
  have e₂ : ((x ↦ᵥ v) ∗ (¤(irUnit Currency.copy) ∗ hnCtxt natAssn w y))
      = (¤¤Currency.copy 1 ∗ x ↦ᵥ v ∗ y ↦ᵥ w) := by
    rw [costCredits_one]; simp only [hnCtxt_def, natAssn_def]; ac_rfl
  have e₃ : (hnCtxt natAssn w y ∗ natAssn w x) = (x ↦ᵥ w ∗ y ↦ᵥ w) := by
    simp only [hnCtxt_def, natAssn_def]; ac_rfl
  rw [e₂, e₃]
  exact (copy_triple x y v w).gc

/-- Wave A's `const_junk_rule`, restated with the price on the abstract
side (`¤(irUnit …)` rather than `¤¤… 1`) so that `hnRefineI_spect`
applies: the difference is `costCredits_one` and nothing else. -/
theorem constN_junk_rule (x : String) (n : ℕ) :
    irHtriple (¤(irUnit Currency.const) ∗ junkCell x) (.const x n)
      ((□ : Assn) ∗ natAssn n x) := by
  rw [← costCredits_one]
  exact const_junk_rule x n

/-! ## 3. The rules (`sepref_fr_rules`)

`hnCtxt`-discipline throughout: every argument that survives the
operation appears as an `hnCtxt`-tagged conjunct in *both* the pre- and
the postcondition, and the operation's own result is delivered in the
judgment's result slot at the destination cell. Wave C's frame
inferencer matches on exactly those tags. -/

/-- `x := y ⊕ z`. The destination is an owned scratch cell (P4/D-ab); both
operands survive. -/
@[sepref_fr_rules]
theorem hnr_mop_binop (op : Imp.Bop) (x y z : String) (m n : ℕ) :
    hnRefine (junkCell x ∗ hnCtxt natAssn m y ∗ hnCtxt natAssn n z) (.binop op x y z)
      (hnCtxt natAssn m y ∗ hnCtxt natAssn n z) x natAssn (mopBinop op m n) :=
  hnRefineI_spect (binop_junk_rule op x y z m n)

/-- `x := x ⊕ z`, the in-place step (P4/D-ac): destructive in `x`, whose
old value's ownership is what the result slot replaces. -/
@[sepref_fr_rules]
theorem hnr_mop_binop_self (op : Imp.Bop) (x z : String) (m n : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn n z) (.binop op x x z)
      (hnCtxt natAssn n z) x natAssn (mopBinop op m n) :=
  hnRefineI_spect (binop_self_mop_rule op x z m n)

/-- `x := a[i]`. The array and the index stay owned in `Γ'`; the index
bound comes from the `mop`'s own `assert`, through `hnr_assert`. -/
@[sepref_fr_rules]
theorem hnr_mop_aget (x a i : String) (xs : List ℕ) (k : ℕ) :
    hnRefine (junkCell x ∗ hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i) (.aget x a i)
      (hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i) x natAssn (mopAget xs k) := by
  rw [mopAget_def]
  exact hnr_assert fun hk => hnRefineI_spect (aget_junk_rule x a i xs k hk)

/-- `a[i] := v`. **The linearity showcase**: `hnCtxt arrayAssn xs a` in
the precondition does *not* reappear in `Γ'` — the array's ownership moves
into the result slot, at `xs.set k v`'s value and the same destination
`a`. A second use of `xs` after this rule is therefore not derivable,
which is the whole point of the ownership discipline. -/
@[sepref_fr_rules]
theorem hnr_mop_aset (a i v : String) (xs : List ℕ) (k n : ℕ) :
    hnRefine (hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i ∗ hnCtxt natAssn n v) (.aset a i v)
      (hnCtxt natAssn k i ∗ hnCtxt natAssn n v) a arrayAssn (mopAset xs k n) := by
  rw [mopAset_def]
  exact hnr_assert fun hk => hnRefineI_spect (aset_mop_rule a i v xs k n hk)

/-- `x := y`. -/
@[sepref_fr_rules]
theorem hnr_mop_copy (x y : String) (w : ℕ) :
    hnRefine (junkCell x ∗ hnCtxt natAssn w y) (.copy x y) (hnCtxt natAssn w y) x natAssn
      (mopCopy w) :=
  hnRefineI_spect (copy_junk_rule x y w)

/-- `x := n`. -/
@[sepref_fr_rules]
theorem hnr_mop_constN (x : String) (n : ℕ) :
    hnRefine (junkCell x) (.const x n) (□ : Assn) x natAssn (mopConstN n) :=
  hnRefineI_spect (constN_junk_rule x n)

/-! ## 4. Exchange (design record F4, P4/D-ae)

The route *in* for a program written at P1's own currencies: `⇓C E` — P1's
`timerefine` — reprices the source's `''if''` / `''call''` into the IR's
`ir.ite` / `ir.while`, and the combinator on the far side is the one this
file defines. `⇓C` commutes with `consume` exactly (`timerefine_consume`),
so the branch exchange is an *equality*; the loop's is not, and §5 says
why. -/

/-- **The branch exchange, as an equality.** `MIf`'s only cost is its own
`''if''` unit, so repricing it is repricing that unit: at any `E` with
`E "if" = ACost.cost Currency.ite 1`, `⇓C E (MIf b t e)` *is*
`irIf b (⇓C E t) (⇓C E e)`. -/
theorem timerefine_MIf {α : Type} {E : String → ECost} (hE : wfR'' E)
    (hif : E "if" = irUnit Currency.ite) (b : Bool) (t e : NRest α ECost) :
    timerefine E (NRest.MIf b t e) = irIf b (timerefine E t) (timerefine E e) := by
  have hbr : timerefine E (if b then t else e)
      = (if b then timerefine E t else timerefine E e) := by cases b <;> simp
  simp only [NRest.MIf, irIf_def]
  rw [timerefine_consume hE, hbr, timerefineA_cost_one, hif]

/-- The concrete exchange map the acceptance uses: the source's two
structural currencies are bought at the IR's structural currencies, and
every other currency buys one of itself (P1's `TId`). Named `irE` and
fixed by cases, as P4's brief prescribes for the case where the general-`E`
statement needs side conditions the consumer would have to carry. -/
def irE : String → ECost := fun n =>
  if n = "if" then irUnit Currency.ite
  else if n = "call" then irUnit Currency.«while»
  else ACost.cost n 1

@[simp] theorem irE_if : irE "if" = irUnit Currency.ite := by simp [irE]

@[simp] theorem irE_call : irE "call" = irUnit Currency.«while» := by
  have h : ("call" : String) ≠ "if" := by decide
  simp [irE, h]

theorem irE_other {n : String} (h₁ : n ≠ "if") (h₂ : n ≠ "call") :
    irE n = ACost.cost n 1 := by simp [irE, h₁, h₂]

/-- `irE` is well-formed in the source's sense (`wfR''`): every target
currency is bought by finitely many source currencies — here by at most
three. This is the side condition every `⇓C` lemma of P1 carries. -/
theorem wfR''_irE : wfR'' irE := by
  intro f
  refine Set.Finite.subset (((Set.finite_singleton f).insert "call").insert "if") ?_
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  by_cases h₁ : s = "if"
  · simp [h₁]
  by_cases h₂ : s = "call"
  · simp [h₂]
  · rw [irE_other h₁ h₂, ACost.toFun_cost] at hs
    have hfs : f = s := by by_contra hne; simp [hne] at hs
    simp [hfs]

/-- The branch exchange at `irE`. -/
theorem timerefine_irE_MIf {α : Type} (b : Bool) (t e : NRest α ECost) :
    timerefine irE (NRest.MIf b t e) = irIf b (timerefine irE t) (timerefine irE e) :=
  timerefine_MIf wfR''_irE irE_if b t e

/-! ## 5. The loop exchange (P4/D-ae)

What holds, and in which direction. The source's pure-guard
`monadic_WHILEIT` exchanges into `irWhileIT` as an **inequality**

```
irWhileIT I bf (⇓C E ∘ g) s ≤ ⇓C E (monadicWhileIT I (returnT ∘ bf) g s)
```

and this is the useful direction, because `hnRefine` is monotone upward
in the abstract program (`Basic.lean`'s `hnRefine_ref`): a rule proved at
the cheaper left-hand side transfers to the exchanged loop. It is not an
equality, for two independent reasons, both recorded rather than papered
over:

* the source's loop pays `''if''` per iteration as well (its body routes
  the branch through `MIf`, P4/D-ad (c)) and the IR's `while` op has no
  branch charge of its own, so the right-hand side is dearer by one
  `E "if"` per iteration — the *only* hypothesis on `E` is therefore
  `E "call" = ACost.cost Currency.while 1`, and `E "if"` is free;
* `⇓C` through `bindT` holds only as `timerefine_bindT_ge` (P1 delta T7:
  `bindT` is a supremum and `⇓C` is not supremum-continuous).

Like `CombRules.lean`'s loop rule, the statement is **measured**
(P4/D-ai): the induction needs the inductive hypothesis under a bind, at
the states the body can actually produce, so a variant `V` supplies the
well-foundedness. The three lemmas it needs and P1 does not export —
result-guarded `bindT` monotonicity, `mono2` for the source's
`monadicWhileBody`, and the pure-guard unfolding — are proved here and
belong upstream (`NREST/Pw.lean`, `NREST/Combinators.lean`); moving them
is a backlog item with no proof content. -/

/-- **Result-guarded `bindT` monotonicity.** The continuations only have
to compare at the results the bound computation can actually produce.
P1's `Pw.lean` has the unguarded `bindT_mono` only; this belongs next to
it (backlog: move upstream). -/
theorem bindT_mono_res {α β : Type} {X : α → WithBot ECost} {f f' : α → NRest β ECost}
    (h : ∀ x, X x ≠ ⊥ → f x ≤ f' x) :
    NRest.bindT (NRest.rest X) f ≤ NRest.bindT (NRest.rest X) f' := by
  rw [NRest.bindT_rest_eq_iSup, NRest.bindT_rest_eq_iSup]
  refine iSup_mono fun x => ?_
  by_cases hx : X x = ⊥
  · rw [hx, NRest.consumeB_bot, NRest.consumeB_bot]
  · exact NRest.consumeB_mono (h x hx) le_rfl

/-- A result the computation admits is a `returnT` below it — the bridge
between `bindT_mono_res`'s guard and the variant premise's. -/
theorem returnT_le_rest_of_ne_bot {α : Type} {X : α → WithBot ECost} {a : α} (h : X a ≠ ⊥) :
    (NRest.returnT a : NRest α ECost) ≤ NRest.rest X := by
  rw [returnT_le_rest_iff]
  obtain ⟨c, hc⟩ := WithBot.ne_bot_iff_exists.1 h
  rw [← hc, ← WithBot.coe_zero, WithBot.coe_le_coe]
  exact ACost.le_def.2 fun _ => zero_le

/-- Paying more is being more permissive. -/
theorem le_consume {α : Type} (m : NRest α ECost) (t : ECost) : m ≤ NRest.consume m t := by
  conv_lhs => rw [← NRest.consume_zero m]
  exact NRest.consume_mono le_rfl (ACost.le_def.2 fun _ => zero_le)

/-- The `RECT` side condition for the source's `monadicWhileBody`.
`Combinators.lean` proves `monadicWhileIT_eq_RECT'` without needing it
(the two bodies are literally equal there), so P1 never stated it;
backlog: move upstream. -/
theorem mono2_monadicWhileBody {σ : Type} (I : σ → Prop) (b : σ → NRest Bool ECost)
    (g : σ → NRest σ ECost) : mono2 (NRest.monadicWhileBody I b g) := by
  refine ⟨monotoneRel_funOrd fun _ _ s hfg => ?_, monotone_of_apply fun _ _ s hfg => ?_⟩
  · exact NRest.bindT_flatGe (flatOrd_refl _ _) fun _ =>
      NRest.bindT_flatGe (flatOrd_refl _ _) fun _ =>
        NRest.flatGe_MIf (NRest.bindT_flatGe (flatOrd_refl _ _) fun _ =>
          NRest.bindT_flatGe (flatOrd_refl _ _) fun _ => hfg _) (flatOrd_refl _ _)
  · exact NRest.bindT_mono le_rfl fun _ =>
      NRest.bindT_mono le_rfl fun _ =>
        NRest.MIf_mono (NRest.bindT_mono le_rfl fun _ =>
          NRest.bindT_mono le_rfl fun _ => hfg _) le_rfl

/-- The source's `monadic_WHILEIT`, unfolded once at a *pure* guard: the
entry payment, the invariant assertion, the `MIf`, and a recursive call
that is again a whole `monadicWhileIT` (its own entry payment is this
iteration's `''call''` unit). -/
theorem monadicWhileIT_unfold_pure {σ : Type} (I : σ → Prop) (bf : σ → Bool)
    (g : σ → NRest σ ECost) (s : σ) :
    NRest.monadicWhileIT I (fun s => NRest.returnT (bf s)) g s
      = NRest.consume
          (NRest.bindT (NRest.assert (I s)) fun _ =>
            NRest.MIf (bf s)
              (NRest.bindT (g s) fun s' =>
                NRest.monadicWhileIT I (fun s => NRest.returnT (bf s)) g s')
              (NRest.returnT s))
          (ACost.cost "call" 1) := by
  have h1 : NRest.monadicWhileIT I (fun s => NRest.returnT (bf s)) g s
      = NRest.consume (RECT (NRest.monadicWhileBody I (fun s => NRest.returnT (bf s)) g) s)
          (ACost.cost "call" 1) := by
    rw [NRest.consume_alt2]; rfl
  rw [h1, RECT_unfold_apply (mono2_monadicWhileBody I _ g), NRest.monadicWhileBody_apply,
    NRest.returnT_bindT]
  rfl

/-- **The loop exchange, measured.** Under `E "call" = ir.while 1` (and
nothing at all on `E "if"`), the ir-currency loop is *below* the
exchanged source loop, so any `hnRefine` proved at the former holds at
the latter. The variant `V` decreases on every state the body admits —
the same premise shape `hnr_while_measured` takes, for the same reason
(P4/D-ai). -/
theorem irWhileIT_le_timerefine {σ : Type} {E : String → ECost} (hE : wfR'' E)
    (hcall : E "call" = irUnit Currency.«while») {I : σ → Prop} {bf : σ → Bool}
    {g : σ → NRest σ ECost} (V : σ → ℕ)
    (VAR : ∀ s s', I s → bf s = true →
      (NRest.returnT s' : NRest σ ECost) ≤ timerefine E (g s) → V s' < V s)
    (s₀ : σ) :
    irWhileIT I bf (fun s => timerefine E (g s)) s₀
      ≤ timerefine E (NRest.monadicWhileIT I (fun s => NRest.returnT (bf s)) g s₀) := by
  suffices H : ∀ n s, V s < n →
      irWhileIT I bf (fun s => timerefine E (g s)) s
        ≤ timerefine E (NRest.monadicWhileIT I (fun s => NRest.returnT (bf s)) g s) from
    H (V s₀ + 1) s₀ (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun s hs => absurd hs (Nat.not_lt_zero _)
  | succ n ih =>
    intro s hsn
    rw [monadicWhileIT_unfold_pure, timerefine_consume hE, timerefineA_cost_one, hcall]
    by_cases hI : I s
    · rw [NRest.assert_pos hI, NRest.returnT_bindT, NRest.MIf, timerefine_consume hE,
        timerefineA_cost_one]
      cases hb : bf s with
      | false =>
        rw [irWhileIT_of_false hI hb, if_neg (by simp), timerefine_returnT]
        exact NRest.consume_mono (le_consume _ _) le_rfl
      | true =>
        rw [irWhileIT_of_true hI hb, if_pos rfl]
        refine NRest.consume_mono (le_trans ?_ (le_consume _ _)) le_rfl
        refine le_trans ?_ (timerefine_bindT_ge hE (g s) _)
        cases hgs : timerefine E (g s) with
        | fail => simp
        | rest X =>
          refine bindT_mono_res fun x hx => ?_
          exact ih x (Nat.lt_of_lt_of_le
            (VAR s x hI hb (by rw [hgs]; exact returnT_le_rest_of_ne_bot hx))
            (Nat.lt_succ_iff.1 hsn))
    · rw [irWhileIT_of_not_inv hI, NRest.assert_neg hI, NRest.bindT_fail, timerefine_fail,
        NRest.consume_fail]

/-- The loop exchange at the concrete map `irE` — the form the
acceptance uses. -/
theorem irWhileIT_le_timerefine_irE {σ : Type} {I : σ → Prop} {bf : σ → Bool}
    {g : σ → NRest σ ECost} (V : σ → ℕ)
    (VAR : ∀ s s', I s → bf s = true →
      (NRest.returnT s' : NRest σ ECost) ≤ timerefine irE (g s) → V s' < V s)
    (s₀ : σ) :
    irWhileIT I bf (fun s => timerefine irE (g s)) s₀
      ≤ timerefine irE (NRest.monadicWhileIT I (fun s => NRest.returnT (bf s)) g s₀) :=
  irWhileIT_le_timerefine wfR''_irE irE_call V VAR s₀

/-! ## 6. Gate (ledger D4, refute-before-prove)

Each rule instantiated once at concrete arguments; one of them driven all
the way down to a `BigStep` run with its cost vector pinned; then the
negative control that the cost vector is load-bearing. -/

namespace Gate

/-- The ledger facts the negative controls turn into refutations. -/
example : Currency.aset ≠ Currency.skip := by decide
example : Currency.ite ≠ Currency.«while» := by decide

/-- Positive control: `x := y + z`, both operands surviving. -/
example : hnRefine (junkCell "x" ∗ hnCtxt natAssn 3 "y" ∗ hnCtxt natAssn 4 "z")
    (.binop .add "x" "y" "z") (hnCtxt natAssn 3 "y" ∗ hnCtxt natAssn 4 "z") "x" natAssn
    (mopBinop .add 3 4) := hnr_mop_binop .add "x" "y" "z" 3 4

/-- Positive control: `i := i + one`, the in-place loop step. -/
example : hnRefine (hnCtxt natAssn 2 "i" ∗ hnCtxt natAssn 1 "one")
    (.binop .add "i" "i" "one") (hnCtxt natAssn 1 "one") "i" natAssn (mopBinop .add 2 1) :=
  hnr_mop_binop_self .add "i" "one" 2 1

/-- Positive control: `x := A[i]`. -/
example : hnRefine (junkCell "x" ∗ hnCtxt arrayAssn [3, 1, 4] "A" ∗ hnCtxt natAssn 0 "i")
    (.aget "x" "A" "i") (hnCtxt arrayAssn [3, 1, 4] "A" ∗ hnCtxt natAssn 0 "i") "x" natAssn
    (mopAget [3, 1, 4] 0) := hnr_mop_aget "x" "A" "i" [3, 1, 4] 0

/-- Positive control: `A[i] := x`, destructive — note that
`hnCtxt arrayAssn [3,1,4] "A"` is absent from `Γ'`. -/
example : hnRefine (hnCtxt arrayAssn [3, 1, 4] "A" ∗ hnCtxt natAssn 2 "i" ∗ hnCtxt natAssn 3 "x")
    (.aset "A" "i" "x") (hnCtxt natAssn 2 "i" ∗ hnCtxt natAssn 3 "x") "A" arrayAssn
    (mopAset [3, 1, 4] 2 3) := hnr_mop_aset "A" "i" "x" [3, 1, 4] 2 3

/-- Positive control: `x := y`. -/
example : hnRefine (junkCell "x" ∗ hnCtxt natAssn 7 "y") (.copy "x" "y")
    (hnCtxt natAssn 7 "y") "x" natAssn (mopCopy 7) := hnr_mop_copy "x" "y" 7

/-- Positive control: `x := 7`. -/
example : hnRefine (junkCell "x") (.const "x" 7) (□ : Assn) "x" natAssn (mopConstN 7) :=
  hnr_mop_constN "x" 7

/-- Positive control: the branch exchange at a concrete branch. -/
example (t e : NRest ℕ ECost) :
    timerefine irE (NRest.MIf true t e) = irIf true (timerefine irE t) (timerefine irE e) :=
  timerefine_irE_MIf true t e

/-! ### End to end: `A[i] := x` at a state, down to a `BigStep` -/

/-- The gate program and state: `A = [3,1,4]`, `i = 2`, `x = 3`. -/
def gateProg : Com := .aset "A" "i" "x"

def gateState : State := State.ofPairs [("i", 2), ("x", 3)] [("A", [3, 1, 4])]

/-- The evaluator's outcome, as data (the shape `Semantics.lean`'s gate
uses, so that the run below is pinned by kernel computation). -/
def gateOut : State × Cost := (evalFuel 2 gateProg gateState).getD (gateState, 0)

theorem gate_evalFuel : evalFuel 2 gateProg gateState = some gateOut := rfl

theorem gate_bigStep : BigStep gateProg gateState gateOut.1 gateOut.2 :=
  bigStep_of_evalFuel gate_evalFuel

-- The state and the cost vector the run leaves, currency by currency.
#guard Ir.Gate.readArrs gateOut.1 ["A"] = [("A", some [3, 1, 3])]
#guard Ir.Gate.readVars gateOut.1 ["i", "x"] = [("i", some 2), ("x", some 3)]
#guard Ir.Gate.costVector gateOut.2 =
  [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 0), ("ir.aset", 1),
   ("ir.ite", 0), ("ir.while", 0), ("ir.add", 0), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-- The precondition of `hnr_mop_aset` at that state. -/
def gatePre : Assn :=
  hnCtxt arrayAssn [3, 1, 4] "A" ∗ hnCtxt natAssn 2 "i" ∗ hnCtxt natAssn 3 "x"

/-- Everything of the state the precondition does not own — nothing, at
this state, but written as an `EXACT` resource so the assertion is checked
by kernel computation rather than by extensionality. -/
def gateFrame : Assn :=
  EXACT (((((vcells gateState).erase "i").erase "x"), (acells gateState).erase "A",
    hcells gateState), 0)

theorem gatePre_holds : irSTATE (gatePre ∗ gateFrame) (gateState, 0) := by
  show (gatePre ∗ gateFrame) ((vcells gateState, acells gateState, hcells gateState), 0)
  simp only [gatePre, hnCtxt_def, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

/-- The abstract side, solved: one `ir.aset` unit for the one result. -/
theorem mopAset_gate :
    mopAset [3, 1, 4] 2 3
      = NRest.rest (NRest.single [3, 1, 3] ((irUnit Currency.aset : ECost) : WithBot ECost)) := by
  rw [mopAset_def, NRest.assert_pos (by decide : (2 : ℕ) < ([3, 1, 4] : List ℕ).length),
    NRest.returnT_bindT, NRest.consume_returnT]
  rfl

/-- **End to end.** The rule's `hnRefine`, at the state above, *runs* the
program: the run is the one the evaluator pinned, so its array is the
updated one and its cost vector is one `ir.aset` unit. -/
theorem aset_runs :
    ∃ s' κ, BigStep gateProg gateState s' κ ∧ Ir.Gate.readArrs s' ["A"] = [("A", some [3, 1, 3])] ∧
      Ir.Gate.costVector κ = Ir.Gate.costVector gateOut.2 := by
  obtain ⟨ra, Ca, -, w⟩ :=
    hnRefineD (F := gateFrame) (hnr_mop_aset "A" "i" "x" [3, 1, 4] 2 3) mopAset_gate gatePre_holds
  obtain ⟨s', κ, hrun, -, -⟩ := w
  refine ⟨s', κ, hrun, ?_, ?_⟩
  all_goals obtain ⟨rfl, rfl⟩ := hrun.unique gate_bigStep
  · rfl
  · rfl

/-! ### Negative control: the wrong currency does not pay

A `mop` that charges `ir.skip` cannot drive an `aset`: the abstract side
caps the credits it hands over at one `ir.skip` unit, and the program's
own price is in `ir.aset`, of which the balance then holds nothing. -/

/-- The mispriced `aset` mop: the same result, the wrong currency. -/
noncomputable def mopAsetWrong (xs : List ℕ) (i v : ℕ) : NRest (List ℕ) ECost :=
  NRest.consume (NRest.returnT (xs.set i v)) (irUnit Currency.skip)

theorem mopAsetWrong_gate :
    mopAsetWrong [3, 1, 4] 2 3
      = NRest.rest (NRest.single [3, 1, 3] ((irUnit Currency.skip : ECost) : WithBot ECost)) := by
  rw [mopAsetWrong, NRest.consume_returnT]
  rfl

theorem hnr_mop_aset_wrong_currency :
    ¬ hnRefine gatePre gateProg (hnCtxt natAssn 2 "i" ∗ hnCtxt natAssn 3 "x") "A"
      arrayAssn (mopAsetWrong [3, 1, 4] 2 3) := by
  intro h
  obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD (F := gateFrame) h mopAsetWrong_gate gatePre_holds
  have hra : ra = [3, 1, 3] := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff] at hCa
    exact WithBot.coe_ne_bot hCa
  subst hra
  rw [NRest.single_self, WithBot.coe_le_coe] at hCa
  rw [zero_add, gateProg, wp_aset] at w
  obtain ⟨-, -, -, -, -, -, -, hi, -⟩ := w
  have h1 := hi Currency.aset
  have h2 := ACost.le_def.1 hCa Currency.aset
  rw [ACost.toFun_cost_self] at h1
  rw [ACost.toFun_cost_ne (by decide : Currency.aset ≠ Currency.skip)] at h2
  rw [le_zero_iff] at h2
  rw [h2] at h1
  simp at h1

end Gate

end Lax13Proofs.Refine.Sepref
