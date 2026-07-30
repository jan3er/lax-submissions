import Lax13Proofs.Refine.Sepref.IrOps
import Lax13Proofs.Refine.NREST.BackwardsReasoning

/-!
# The VCG at the IR's loop, and the cost algebra a linear budget needs

Two pieces of tower that P7 discovered were missing, both stated for any
program and neither about breadth-first search.

## 1. `irWhileIT` meets `While` (P7/T-a)

`Sepref/Translate.lean`'s loop rule synthesizes `irWhileIT I bf f s₀`,
and `NREST/BackwardsReasoning.lean`'s `While` reasons about
`whileIET I E b C s₀`. Nothing connected them, so a program the tool can
translate had no VCG, and a program the VCG can handle could not be
translated.

The two differ in exactly one place. `irWhileIT` asserts its invariant
**before** the guard is tested, so it asserts it once more than
`whileT` does — at the exit state. Where the assertion can fail there,
`irWhileIT` is the *larger* program (a failure is the top of `NRest`),
so no inequality goes the way a `≤ SPEC` proof needs.

`irWhileIT_eq_whileIET` closes the gap by fixing the *shape* of the
invariant: an invariant of the guarded form `bf s = true → P s` is
vacuous exactly where the extra assertion sits, and then the two
programs are **equal**. The guarded form is not a restriction in
practice — it is the form P4's own examples already use (`rvI`, P4/D-ed:
"stated as an implication so that the initial state satisfies it"),
because the only consumer of the invariant is the body, which runs only
when the guard holds.

The `whileIET` side carries a *second* invariant `J` and an energy `E`,
both free: they are the annotations `While` reads off the term, and they
have nothing to do with the assertion the program makes. So a caller
picks the program's `P` for the operation bounds its body needs, and the
proof's `J`/`E` for the correctness argument — which is the right
separation, and the one the source's `whileIET` was designed for.

## 2. Two-currency energies (P7/T-b)

A loop whose budget is linear in two independent sizes carries an
energy `a • A + b • B`. `ACost`'s subtraction is pointwise and
truncated, so the one fact every such argument needs — that the energy
gives up exactly `(a - a') • A + (b - b') • B` — is not `abel`; it is
`Nat.add_mul` and `omega`, once.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. `irWhileIT` as a `whileIET` -/

/-- **Charging after a bind is charging the bind.** The distribution law
`Pw.lean` states only on the left (`bindT_consume`); the loop bridge
needs it on the right too, because that is where `irWhileIT` puts the
iteration's own unit — inside the recursive call. -/
theorem bindT_consume_right {α β γ : Type} [CompleteLattice γ] [AddCommMonoid γ]
    (hc : NRest.AddSupContinuousB γ) (m : NRest α γ) (g : α → NRest β γ) (t : γ) :
    NRest.bindT m (fun z => NRest.consume (g z) t) = NRest.consume (NRest.bindT m g) t := by
  cases m with
  | fail => simp
  | rest X =>
    rw [NRest.bindT_rest_eq_iSup, NRest.bindT_rest_eq_iSup, NRest.consume_iSup hc]
    refine iSup_congr fun x => ?_
    rcases withBot_eq_bot_or_coe (X x) with h | ⟨u, h⟩
    · rw [h, NRest.consumeB_bot, NRest.consumeB_bot, NRest.consume_bot]
    · rw [h, NRest.consumeB_coe, NRest.consumeB_coe, NRest.consume_consume,
        NRest.consume_consume, add_comm]

/-- The `whileT` body an `irWhileIT` body induces: assert the invariant,
then run a body that has paid the iteration's own `ir.while` unit. -/
noncomputable def irWhileC {σ : Type} (I : σ → Prop) (f : σ → NRest σ ECost) :
    σ → NRest σ ECost := fun y =>
  NRest.bindT (NRest.assert (I y)) fun _ =>
    NRest.consume (f y) (irUnit Currency.«while»)

/-- **The bridge.** At a guarded invariant, the translator's loop and
the VCG's loop are the same program; `J` and `E` are the caller's
annotations and are unconstrained. -/
theorem irWhileIT_eq_whileIET {σ ε : Type} (P : σ → Prop) (bf : σ → Bool)
    (f : σ → NRest σ ECost) (J : σ → Prop) (E : σ → ε) (s : σ) :
    irWhileIT (fun y => bf y = true → P y) bf f s
      = NRest.consume
          (NRest.whileIET J E bf (irWhileC (fun y => bf y = true → P y) f) s)
          (irUnit Currency.«while») := by
  rw [NRest.whileIET_eq, irWhileIT, NRest.whileT]
  refine congrArg (NRest.consume · _)
    (congrFun (congrArg RECT (funext fun D => funext fun y => ?_)) s)
  rw [irWhileBody_apply, NRest.whileBody_apply]
  by_cases hb : bf y = true
  · simp only [if_pos hb, irWhileC, NRest.bindT_assoc_acost,
      NRest.bindT_consume NRest.addSupContinuousB_acost,
      bindT_consume_right NRest.addSupContinuousB_acost]
  · simp only [Bool.not_eq_true] at hb
    rw [if_neg (by simp [hb]), NRest.assert_pos (fun h => absurd h (by simp [hb])),
      NRest.returnT_bindT, if_neg (by simp [hb])]

/-- Binding a one-operation program is charging its cost and going on. -/
theorem bindT_unitT {α β : Type} (x : α) (c : ECost) (f : α → NRest β ECost) :
    NRest.bindT (NRest.consume (NRest.returnT x) c) f = NRest.consume (f x) c := by
  rw [NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.returnT_bindT]

/-- A cost is at most itself plus something. -/
theorem cost_le_add {κ : Type} (a b : ACost κ ℕ∞) : a ≤ a + b :=
  ACost.le_def.mpr fun k => by rw [ACost.toFun_add]; exact le_self_add

/-- A one-result program meets a specification it satisfies. -/
theorem consume_returnT_le_spec {α : Type} {x : α} {c : ECost} {P : α → Prop} {T : α → ECost}
    (hP : P x) (hc : c ≤ T x) : NRest.consume (NRest.returnT x) c ≤ NRest.spec P T := by
  rw [NRest.consume_returnT, NRest.spec]
  refine NRest.rest_le_rest_iff.mpr fun y => ?_
  by_cases hy : y = x
  · subst hy; rw [NRest.single_self, if_pos hP]; exact WithBot.coe_le_coe.mpr hc
  · rw [NRest.single_of_ne hy]; exact bot_le

/-- Charging a specification raises its price. -/
theorem consume_spec {α : Type} (P : α → Prop) (T : α → ECost) (c : ECost) :
    NRest.consume (NRest.spec P T) c = NRest.spec P (fun x => c + T x) := by
  rw [NRest.spec, NRest.consume_rest', NRest.spec]
  congr 1
  funext v
  by_cases hv : P v <;> simp [hv]

/-- A specification weakens to a dearer one. -/
theorem spec_mono {α : Type} {P P' : α → Prop} {T T' : α → ECost} (hP : ∀ x, P x → P' x)
    (hT : ∀ x, P x → T x ≤ T' x) : NRest.spec P T ≤ NRest.spec P' T' := by
  refine NRest.rest_le_rest_iff.mpr fun y => ?_
  by_cases hy : P y
  · rw [if_pos hy, if_pos (hP y hy)]; exact WithBot.coe_le_coe.mpr (hT y hy)
  · rw [if_neg hy]; exact bot_le

/-- Composing with a specification: the costs add. -/
theorem bindT_spec_le {α β : Type} (P : α → Prop) (c : ECost) (g : α → NRest β ECost)
    (P' : β → Prop) (c' : ECost)
    (h : ∀ x, P x → g x ≤ NRest.spec P' (fun _ => c')) :
    NRest.bindT (NRest.spec P (fun _ => c)) g ≤ NRest.spec P' (fun _ => c + c') := by
  rw [NRest.spec, NRest.bindT_rest_eq_iSup]
  refine iSup_le fun x => ?_
  by_cases hx : P x
  · rw [if_pos hx, NRest.consumeB_coe]
    refine le_trans (NRest.consume_mono (h x hx) le_rfl) ?_
    rw [consume_spec]
  · rw [if_neg hx, NRest.consumeB_bot]
    exact bot_le

/-- **Reading a specification back through a projection (P7/T-c).**
A synthesized program ends at its loop state; the abstract program the
caller specified ends at one *component* of it. The bound transfers
because every result of `m` is a result of the projected bind at its
image: if `x` is affordable at `Ca` in `m`, then `f x` is affordable at
`Ca` in `bindT m (returnT ∘ f)`, and the specification prices that.

Placement (P7/D-bi): this belongs beside `NREST/Pw.lean`'s `bindT`/
`spec` calculus, not in a Sepref file; it is here because the rest of
this campaign's `spec` lemmas are, and the P1 files are frozen. -/
theorem le_spec_of_bindT_returnT {α β : Type} {m : NRest α ECost} {f : α → β} {Φ : β → Prop}
    {T : ECost} (h : NRest.bindT m (fun x => NRest.returnT (f x)) ≤ NRest.spec Φ (fun _ => T)) :
    m ≤ NRest.spec (fun x => Φ (f x)) (fun _ => T) := by
  cases hm : m with
  | fail =>
    rw [hm, NRest.bindT_fail, NRest.spec] at h
    exact absurd h (NRest.not_fail_le_rest _)
  | rest M =>
    rw [NRest.spec]
    refine NRest.rest_le_rest_iff.mpr fun x => ?_
    rcases withBot_eq_bot_or_coe (M x) with hx | ⟨Ca, hx⟩
    · rw [hx]; exact bot_le
    · have hle : NRest.consume (NRest.returnT x) Ca ≤ m := by
        rw [hm, NRest.consume_returnT]
        refine NRest.rest_le_rest_iff.mpr fun y => ?_
        by_cases hy : y = x
        · subst hy; rw [NRest.single_self, hx]
        · rw [NRest.single_of_ne hy]; exact bot_le
      have h2 := le_trans (NRest.bindT_mono hle fun _ => le_rfl) h
      rw [bindT_unitT, NRest.consume_returnT, NRest.spec, NRest.rest_le_rest_iff] at h2
      have h4 := h2 (f x)
      rw [NRest.single_self] at h4
      rw [hx]
      by_cases hΦ : Φ (f x)
      · simpa [hΦ] using h4
      · exfalso
        simp only [hΦ, if_false] at h4
        exact WithBot.coe_ne_bot (le_bot_iff.mp h4)

/-! ## 2. Two-currency energies -/

/-- The energy of a loop with a linear budget in two independent sizes:
`a` units of `A` still to spend and `b` of `B`. -/
def E2 {κ : Type} (A B : ACost κ ℕ) (a b : ℕ) : ACost κ ℕ := a • A + b • B

/-- **What an iteration gives up.** Pointwise, and truncated
subtraction is not the obstacle it looks like: both counts only ever
decrease. -/
theorem E2_sub {κ : Type} (A B : ACost κ ℕ) {a a' b b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) :
    E2 A B a b - E2 A B a' b' = E2 A B (a - a') (b - b') := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hb
  ext k
  simp only [E2, ACost.toFun_add, ACost.toFun_sub, ACost.toFun_nsmul, smul_eq_mul,
    Nat.add_sub_cancel_left, Nat.add_mul]
  omega

theorem E2_mono {κ : Type} (A B : ACost κ ℕ) {a a' b b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) :
    E2 A B a' b' ≤ E2 A B a b := by
  refine ACost.le_def.mpr fun k => ?_
  simp only [E2, ACost.toFun_add, ACost.toFun_nsmul, smul_eq_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ ha) (Nat.mul_le_mul_right _ hb)

/-- One iteration off a two-currency energy. -/
theorem E2_split {κ : Type} (A B : ACost κ ℕ) (a b r : ℕ) :
    E2 A B (a + 1) (b + r) = (A + r • B) + E2 A B a b := by
  simp only [E2, add_nsmul, one_nsmul]
  ac_rfl

theorem liftACost_nsmul {κ : Type} (a : ℕ) (A : ACost κ ℕ) :
    liftACost (a • A) = a • liftACost A := by
  ext k; simp [ACost.toFun_nsmul, nsmul_eq_mul]

theorem wfR2_nsmul {κ : Type} (a : ℕ) {A : ACost κ ℕ} (h : NRest.wfR2 A) :
    NRest.wfR2 (a • A) := by
  refine h.subset fun k hk => ?_
  simp only [Set.mem_setOf_eq, ACost.toFun_nsmul, smul_eq_mul] at hk ⊢
  exact fun hc => hk (by rw [hc, Nat.mul_zero])

end Lax13Proofs.Refine.Sepref
