import Lax13Proofs.Refine.NREST.Combinators
import Lax13Proofs.Refine.NREST.DataRefinement

/-!
# Currency-carrying list folds and FOREACH

Tower-expansion P2.A's authored currency-vector adaptation of AFP NREST
`Refine_Foreach.thy`.  No pinned source contains a multi-currency FOREACH
(campaign ledger E5): the recursion and invariant organization come from
AFP, while the carrier is the repository's `ECost = ACost String ℕ∞`.

The central discipline is deliberately source-shaped. `nfoldli` itself does
not invent a loop charge; every step is an `NRest` computation and therefore
carries its own currency vector. Consequently a walk over a member list is
charged by that list's length, never by an ambient carrier size.
-/

namespace Lax13Proofs.Refine

namespace NRest

variable {α β σ τ γ : Type}

/-! ## Interruptible monadic list fold -/

/-- AFP `nfoldli`: fold left through a list while `c` remains true.  The
definition is structurally recursive in Lean; AFP expresses the same
equations through `RECT`. -/
noncomputable def nfoldli [CompleteLattice γ] [AddMonoid γ]
    (c : σ → Bool) (f : α → σ → NRest σ γ) : List α → σ → NRest σ γ
  | [], s => returnT s
  | x :: xs, s => if c s then bindT (f x s) (nfoldli c f xs) else returnT s

@[simp] theorem nfoldli_nil [CompleteLattice γ] [AddMonoid γ]
    (c : σ → Bool) (f : α → σ → NRest σ γ) (s : σ) :
    nfoldli c f [] s = returnT s := rfl

@[simp] theorem nfoldli_cons [CompleteLattice γ] [AddMonoid γ]
    (c : σ → Bool) (f : α → σ → NRest σ γ) (x : α) (xs : List α) (s : σ) :
    nfoldli c f (x :: xs) s =
      if c s then bindT (f x s) (nfoldli c f xs) else returnT s := rfl

@[simp] theorem nfoldli_no_continue [CompleteLattice γ] [AddMonoid γ]
    (l : List α) (c : σ → Bool) (f : α → σ → NRest σ γ) (s : σ)
    (hc : c s = false) : nfoldli c f l s = returnT s := by
  cases l <;> simp [hc]

/-- Source `nfoldli_mono`, generalized over the repository's ordered cost
carriers. -/
theorem nfoldli_mono [CompleteLattice γ] [AddCommMonoid γ] [IsOrderedAddMonoid γ]
    (l : List α) (c : σ → Bool) {f g : α → σ → NRest σ γ}
    (hfg : ∀ x s, f x s ≤ g x s) (s : σ) :
    nfoldli c f l s ≤ nfoldli c g l s := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons x xs ih =>
      simp only [nfoldli_cons]
      split
      · exact bindT_mono (hfg x s) ih
      · exact le_rfl

/-- The source's `nfoldli_append`, at the repository cost carrier. -/
theorem nfoldli_append (l₁ l₂ : List α) (c : σ → Bool)
    (f : α → σ → NRest σ ECost) (s : σ) :
    nfoldli c f (l₁ ++ l₂) s = bindT (nfoldli c f l₁ s) (nfoldli c f l₂) := by
  induction l₁ generalizing s with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, nfoldli_cons]
      split
      · rw [NRest.bindT_assoc_acost]
        congr 1
        funext s'
        exact ih s'
      · have hc : c s = false := Bool.eq_false_of_not_eq_true ‹¬ c s = true›
        rw [returnT_bindT, nfoldli_no_continue l₂ c f s hc]

/-- The source's `nfoldli_assert`: an element assertion already implied
by the input list does not change the fold. -/
theorem nfoldli_assert (l : List α) (S : Set α) (c : σ → Bool)
    (f : α → σ → NRest σ ECost) (s : σ) (hl : ∀ x ∈ l, x ∈ S) :
    nfoldli c (fun x s => bindT (assert (x ∈ S)) fun _ => f x s) l s =
      nfoldli c f l s := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ∈ S := hl x (by simp)
      have hxs : ∀ y ∈ xs, y ∈ S := fun y hy => hl y (by simp [hy])
      simp only [nfoldli_cons]
      split
      · rw [assert_pos hx, returnT_bindT]
        congr 1
        funext s'
        exact ih s' hxs
      · rfl

/-- The source's `param_nfoldli`/`nfoldli_refine`, rendered directly with
`List.Forall₂` and `concFun`.  It is the NREST refinement rule consumed by
the Sepref lowering below. -/
theorem nfoldli_refine {αi σi : Type} (Ra : Set (αi × α)) (Rs : Set (σi × σ))
    {li : List αi} {l : List α} {ci : σi → Bool} {c : σ → Bool}
    {fi : αi → σi → NRest σi ECost} {f : α → σ → NRest σ ECost}
    {si : σi} {s : σ}
    (hl : List.Forall₂ (fun xi x => (xi, x) ∈ Ra) li l)
    (hs : (si, s) ∈ Rs)
    (hc : ∀ si s, (si, s) ∈ Rs → ci si = c s)
    (hf : ∀ xi x si s, (xi, x) ∈ Ra → (si, s) ∈ Rs → c s = true →
      fi xi si ≤ concFun Rs (f x s)) :
    nfoldli ci fi li si ≤ concFun Rs (nfoldli c f l s) := by
  induction hl generalizing si s with
  | nil => simpa using (returnT_refine (R := Rs) hs)
  | cons hxx hll ih =>
      rw [nfoldli_cons, nfoldli_cons, hc si s hs]
      by_cases hcs : c s = true
      · rw [hcs, if_pos rfl]
        exact bindT_refine_of addSupContinuousB_acost (hf _ _ _ _ hxx hs hcs)
          (fun si' s' hs' => ih hs')
      · have hfalse : c s = false := Bool.eq_false_of_not_eq_true hcs
        rw [hfalse]
        simpa using (returnT_refine (R := Rs) hs)

/-! ## Annotation and exact vector cost -/

set_option linter.unusedVariables false in
/-- Source `nfoldliIE`: invariant and remaining-cost annotations are
definitionally inert and are read by proof rules. -/
noncomputable def nfoldliIE (I : List α → List α → σ → Prop) (E : List α → ECost)
    (l : List α) (c : σ → Bool) (f : α → σ → NRest σ ECost) (s : σ) :
    NRest σ ECost := nfoldli c f l s

@[simp] theorem nfoldliIE_eq (I : List α → List α → σ → Prop) (E : List α → ECost)
    (l : List α) (c : σ → Bool) (f : α → σ → NRest σ ECost) (s : σ) :
    nfoldliIE I E l c f s = nfoldli c f l s := rfl

/-- Pure value computed by an uninterrupted fold, used by the executable
cost gate and later by the Sepref lowering proof. -/
def foldState (step : α → σ → σ) : List α → σ → σ
  | [], s => s
  | x :: xs, s => foldState step xs (step x s)

@[simp] theorem foldState_nil (step : α → σ → σ) (s : σ) :
    foldState step [] s = s := rfl

@[simp] theorem foldState_cons (step : α → σ → σ) (x : α) (xs : List α) (s : σ) :
    foldState step (x :: xs) s = foldState step xs (step x s) := rfl

/-- State-invariant half of the authored vector `nfoldliIE` rule. -/
theorem foldState_preserves (I : σ → Prop) (step : α → σ → σ)
    (hstep : ∀ x s, I s → I (step x s)) (l : List α) (s : σ) (hI : I s) :
    I (foldState step l s) := by
  induction l generalizing s with
  | nil => exact hI
  | cons x xs ih => exact ih (step x s) (hstep x s hI)

/-- Exact currency theorem: one constant-cost deterministic step per member.
This is the vector counterpart of AFP's `body_time * length l` bound, but
strictly stronger for the deterministic gate. -/
theorem nfoldli_consume_exact (l : List α) (step : α → σ → σ) (κ : ECost) (s : σ) :
    nfoldli (fun _ => true)
        (fun x s => consume (returnT (step x s)) κ) l s =
      consume (returnT (foldState step l s)) (l.length • κ) := by
  induction l generalizing s with
  | nil => simp
  | cons x xs ih =>
      rw [nfoldli_cons, if_pos rfl,
        NRest.bindT_consume NRest.addSupContinuousB_acost,
        NRest.returnT_bindT, ih, NRest.consume_consume]
      simp only [foldState_cons, List.length_cons, succ_nsmul]
      congr 1
      ac_rfl

/-- Invariant-and-energy rule for the deterministic vector fold.  It is
the authored ECost counterpart of the source's `nfoldliIE_rule`: the
annotation exposes the invariant, while the exact budget is one vector
`κ` for each remaining member. -/
theorem nfoldliIE_consume_rule (I : σ → Prop) (l : List α)
    (step : α → σ → σ) (κ : ECost) (s : σ)
    (hstep : ∀ x s, I s → I (step x s)) (hI : I s) :
    nfoldliIE (fun _ _ s => I s) (fun xs => xs.length • κ) l
        (fun _ => true) (fun x s => consume (returnT (step x s)) κ) s =
      consume (returnT (foldState step l s)) (l.length • κ) ∧
    I (foldState step l s) :=
  ⟨nfoldli_consume_exact l step κ s, foldState_preserves I step hstep l s hI⟩

/-! ## Currency-vector FOREACH family -/

/-- Vector-cost counterpart of the earlier `FOREACH_body`. -/
noncomputable def FOREACH_bodyE [Inhabited α]
    (f : α → σ → NRest σ ECost) (p : List α × σ) : NRest (List α × σ) ECost :=
  bindT (returnT p.1.headI) fun x =>
    bindT (f x p.2) fun s' => returnT (p.1.tail, s')

@[simp] theorem FOREACH_bodyE_apply [Inhabited α]
    (f : α → σ → NRest σ ECost) (p : List α × σ) :
    FOREACH_bodyE f p = bindT (f p.1.headI p.2) fun s' => returnT (p.1.tail, s') := by
  rw [FOREACH_bodyE, returnT_bindT]

/-- Currency-vector `FOREACHoci`. `inittime` and `bodyTime` are full
vectors, and the energy annotation is repeated addition rather than a
single scalar multiplication. -/
noncomputable def FOREACHociE [Inhabited α] (R : α → α → Prop)
    (Φ : Set α → σ → Prop) (S : Set α) (c : σ → Bool)
    (f : α → σ → NRest σ ECost) (s₀ : σ) (inittime bodyTime : ECost) :
    NRest σ ECost :=
  bindT (assert S.Finite) fun _ =>
    bindT (spec (fun xs : List α => xs.Nodup ∧ S = {x | x ∈ xs} ∧ xs.Pairwise R)
        (fun _ => inittime)) fun xs =>
      bindT
        (whileIET (fun p : List α × σ =>
            ∃ xs', xs = xs' ++ p.1 ∧ Φ {x | x ∈ p.1} p.2)
          (fun p : List α × σ => p.1.length • bodyTime)
          (FOREACH_cond c) (FOREACH_bodyE f) (xs, s₀))
        fun p => returnT p.2

/-- Currency-vector unordered FOREACH. -/
noncomputable def FOREACHciE [Inhabited α] (Φ : Set α → σ → Prop)
    (S : Set α) (c : σ → Bool) (f : α → σ → NRest σ ECost) (s₀ : σ)
    (inittime bodyTime : ECost) : NRest σ ECost :=
  FOREACHociE (fun _ _ => True) Φ S c f s₀ inittime bodyTime

@[simp] theorem FOREACHciE_eq [Inhabited α] (Φ : Set α → σ → Prop)
    (S : Set α) (c : σ → Bool) (f : α → σ → NRest σ ECost) (s₀ : σ)
    (inittime bodyTime : ECost) :
    FOREACHciE Φ S c f s₀ inittime bodyTime =
      FOREACHociE (fun _ _ => True) Φ S c f s₀ inittime bodyTime := rfl

@[simp] theorem FOREACHociE_of_infinite [Inhabited α] (R : α → α → Prop)
    (Φ : Set α → σ → Prop) {S : Set α} (hS : ¬ S.Finite) (c : σ → Bool)
    (f : α → σ → NRest σ ECost) (s₀ : σ) (inittime bodyTime : ECost) :
    FOREACHociE R Φ S c f s₀ inittime bodyTime = fail := by
  rw [FOREACHociE, assert_neg hS, bindT_fail]

/-! ## Source decomposition through a list iterator -/

/-- Source placeholder `it_to_sorted_list`, at vector cost. -/
noncomputable def itToSortedListE (R : α → α → Prop) (S : Set α)
    (toSortedListCost : ECost) : NRest (List α) ECost :=
  spec (fun xs => xs.Nodup ∧ S = {x | x ∈ xs} ∧ xs.Pairwise R)
    (fun _ => toSortedListCost)

/-- The placeholder returns exactly distinct enumerations of `S`, ordered
by `R`, and admits precisely the budgets below its declared vector. -/
@[simp] theorem inresT_itToSortedListE_iff (R : α → α → Prop) (S : Set α)
    (toSortedListCost : ECost) (xs : List α) (t : ECost) :
    inresT (itToSortedListE R S toSortedListCost) xs t ↔
      (xs.Nodup ∧ S = {x | x ∈ xs} ∧ xs.Pairwise R) ∧ t ≤ toSortedListCost := by
  simp only [itToSortedListE, inresT, spec, rest_le_rest_iff, single_le_iff]
  by_cases hp : xs.Nodup ∧ S = {x | x ∈ xs} ∧ xs.Pairwise R
  · simp [hp]
  · simp [hp]

/-- Source `LIST_FOREACH`, at vector cost. -/
noncomputable def LIST_FOREACHE [Inhabited α] (Φ : Set α → σ → Prop)
    (toList : NRest (List α) ECost) (c : σ → Bool)
    (f : α → σ → NRest σ ECost) (s₀ : σ) (bodyTime : ECost) : NRest σ ECost :=
  bindT toList fun xs =>
    bindT
      (whileIET (fun p : List α × σ =>
          ∃ xs', xs = xs' ++ p.1 ∧ Φ {x | x ∈ p.1} p.2)
        (fun p : List α × σ => p.1.length • bodyTime)
        (FOREACH_cond c) (FOREACH_bodyE f) (xs, s₀))
      fun p => returnT p.2

/-- The source's `FOREACHoci_by_LIST_FOREACH`, now preserving the entire
currency vector. -/
theorem FOREACHociE_by_LIST_FOREACHE [Inhabited α] (R : α → α → Prop)
    (Φ : Set α → σ → Prop) (S : Set α) (c : σ → Bool)
    (f : α → σ → NRest σ ECost) (s₀ : σ) (toSortedListCost bodyTime : ECost) :
    FOREACHociE R Φ S c f s₀ toSortedListCost bodyTime =
      bindT (assert S.Finite) fun _ =>
        LIST_FOREACHE Φ (itToSortedListE R S toSortedListCost) c f s₀ bodyTime := rfl

/-! ## D4 carrier-blindness gate -/

namespace ForeachGate

/-- A two-member arena embedded in a 100-cell carrier. -/
def members : List ℕ := [7, 91]

def carrier : List ℕ := List.replicate 100 0

def visit (i acc : ℕ) : ℕ := acc + i

def visitCost : ECost := ACost.cost "member" 1

theorem walk_exact :
    nfoldli (fun _ => true)
        (fun i acc => consume (returnT (visit i acc)) visitCost) members 0 =
      consume (returnT 98) (2 • visitCost) := by
  simpa [members, visit, foldState] using
    nfoldli_consume_exact members visit visitCost 0

-- The vector depends on the two members, not on the 100-cell carrier.
#guard members.length = 2
#guard carrier.length = 100
#guard (2 • visitCost).toFun "member" = 2
#guard (2 • visitCost).toFun "carrier" = 0

/-- info: 'Lax13Proofs.Refine.NRest.ForeachGate.walk_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms walk_exact

end ForeachGate

end NRest

end Lax13Proofs.Refine
