import Lax13Proofs.Refine.Iicf.Intf.Multiset

/-!
# Priority-bag interface

Source-faithful semantic leaf for `IICF/Intf/IICF_Prio_Bag.thy` at
`isabelle_llvm_time` commit `42dd7f5`.

The source first proves genuinely relational rules for two potentially
different priority functions.  Its registered interface then protects the
priority function as a constant and obtains self-parametricity from
`IS_BELOW_ID A`.  Lean has no `PR_CONST`/`UNPROTECT` term-rewriting layer, so
that boundary is represented directly: `prioPopMin_param` and
`prioPeekMin_param` are the general rules, while the two `sepref_decl_op`s
below fix one priority function and use `IsBelowId` only at registration.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {α β κ μ : Type}

/-! ## Semantic operations -/

/-- Source `mop_prio_pop_min`: nondeterministically remove a global minimum.
The specification is cost-silent, as in the source's bare `SPEC`. -/
noncomputable def prioPopMin [LinearOrder κ] (prio : α → κ)
    (m : Multiset α) : NRest (α × Multiset α) ECost :=
  NRest.bindT (NRest.assert (m ≠ 0)) fun _ =>
    NRest.spec
      (fun p => p.1 ∈ m ∧ p.2 = msetErase m p.1 ∧
        ∀ x ∈ m, prio p.1 ≤ prio x)
      (fun _ => 0)

/-- Source `mop_prio_peek_min`: nondeterministically return a global minimum
without changing the bag. -/
noncomputable def prioPeekMin [LinearOrder κ] (prio : α → κ)
    (m : Multiset α) : NRest α ECost :=
  NRest.bindT (NRest.assert (m ≠ 0)) fun _ =>
    NRest.spec
      (fun x => x ∈ m ∧ ∀ y ∈ m, prio x ≤ prio y)
      (fun _ => 0)

/-! ## General relational theorem -/

/-- Relational spelling of the source premise
`((≤),(≤)) ∈ B → B → bool_rel`.  Lean comparisons are propositions, so the
identity result relation is equivalence. -/
def OrderPreserved [LE κ] [LE μ] (B : Set (κ × μ)) : Prop :=
  ∀ ⦃a a' : κ⦄ ⦃b b' : μ⦄, (a, b) ∈ B → (a', b') ∈ B →
    (a ≤ a' ↔ b ≤ b')

/-- A minimum and its exact erase remainder can be transported through a
multiset relation without any single-valuedness assumption: the witness is
chosen from the same `Multiset.Rel` cons decomposition. -/
private theorem prio_min_transfer [LinearOrder κ] [LinearOrder μ]
    {A : Set (α × β)} {B : Set (κ × μ)}
    {prio' : α → κ} {prio : β → μ}
    (hprio : (prio', prio) ∈ A →ᵣ B) (hord : OrderPreserved B)
    {m : Multiset α} {n : Multiset β} (hmn : (m, n) ∈ msetRel A)
    {x : α} (hx : x ∈ m) (hmin : ∀ x' ∈ m, prio' x ≤ prio' x') :
    ∃ y, (x, y) ∈ A ∧ y ∈ n ∧
      (msetErase m x, msetErase n y) ∈ msetRel A ∧
      ∀ y' ∈ n, prio y ≤ prio y' := by
  classical
  obtain ⟨mr, hm⟩ := Multiset.exists_cons_of_mem hx
  have hrel : Multiset.Rel (fun a b => (a, b) ∈ A) (x ::ₘ mr) n := by
    simpa [hm] using hmn
  obtain ⟨y, nr, hxy, hrest, hn⟩ := Multiset.rel_cons_left.mp hrel
  refine ⟨y, hxy, ?_, ?_, ?_⟩
  · simp [hn]
  · simpa [msetErase, hm, hn] using hrest
  · intro y' hy'
    have hflip : Multiset.Rel (fun b a => (a, b) ∈ A) n m :=
      Multiset.rel_flip.mpr hmn
    obtain ⟨x', hx'm, hx'y'⟩ :=
      Multiset.exists_mem_of_rel_of_mem hflip hy'
    exact (hord (hprio x y hxy) (hprio x' y' hx'y')).mp (hmin x' hx'm)

/-- Source `param_mop_prio_pop_min`, retaining its different domains,
different priority codomains, and related priority functions. -/
theorem prioPopMin_param [LinearOrder κ] [LinearOrder μ]
    {A : Set (α × β)} {B : Set (κ × μ)}
    {prio' : α → κ} {prio : β → μ}
    (hprio : (prio', prio) ∈ A →ᵣ B) (hord : OrderPreserved B) :
    (prioPopMin prio', prioPopMin prio) ∈
      msetRel A →ᵣ NRest.nrestRel (A ×ᵣ msetRel A) := by
  intro m n hmn
  by_cases hn : n ≠ 0
  · have hm : m ≠ 0 := by
      intro hm0
      exact hn (msetRel_empty_left.mp (hm0 ▸ hmn))
    simp only [prioPopMin, NRest.assert_pos hm, NRest.assert_pos hn,
      NRest.returnT_bindT]
    apply NRest.nrestRel_of_le
    rw [NRest.spec, NRest.spec]
    apply NRest.rest_refines_concFun'
    intro X hX p hp
    have hX' := NRest.rest_inj_iff.mp hX
    subst X
    rcases p with ⟨x, mr⟩
    have hpost : x ∈ m ∧ mr = msetErase m x ∧
        ∀ x' ∈ m, prio' x ≤ prio' x' := by
      simpa using hp
    obtain ⟨y, hxy, hyn, herase, hymin⟩ :=
      prio_min_transfer hprio hord hmn hpost.1 hpost.2.2
    refine ⟨(y, msetErase n y), ⟨hxy, ?_⟩, ?_⟩
    · simpa [hpost.2.1] using herase
    · have hr : y ∈ n ∧ msetErase n y = msetErase n y ∧
          ∀ y' ∈ n, prio y ≤ prio y' := ⟨hyn, rfl, hymin⟩
      simp only [if_pos hpost, if_pos hr]
      exact le_rfl
  · have hn0 : n = 0 := not_ne_iff.mp hn
    have hm0 : m = 0 := msetRel_empty_right.mp (hn0 ▸ hmn)
    simp [prioPopMin, hm0, hn0, NRest.nrestRel]

/-- Source `param_mop_prio_peek_min`, with the same genuinely relational
priority-function premise. -/
theorem prioPeekMin_param [LinearOrder κ] [LinearOrder μ]
    {A : Set (α × β)} {B : Set (κ × μ)}
    {prio' : α → κ} {prio : β → μ}
    (hprio : (prio', prio) ∈ A →ᵣ B) (hord : OrderPreserved B) :
    (prioPeekMin prio', prioPeekMin prio) ∈
      msetRel A →ᵣ NRest.nrestRel A := by
  intro m n hmn
  by_cases hn : n ≠ 0
  · have hm : m ≠ 0 := by
      intro hm0
      exact hn (msetRel_empty_left.mp (hm0 ▸ hmn))
    simp only [prioPeekMin, NRest.assert_pos hm, NRest.assert_pos hn,
      NRest.returnT_bindT]
    apply NRest.nrestRel_of_le
    rw [NRest.spec, NRest.spec]
    apply NRest.rest_refines_concFun'
    intro X hX x hx
    have hX' := NRest.rest_inj_iff.mp hX
    subst X
    have hpost : x ∈ m ∧ ∀ x' ∈ m, prio' x ≤ prio' x' := by
      simpa using hx
    obtain ⟨y, hxy, hyn, -, hymin⟩ :=
      prio_min_transfer hprio hord hmn hpost.1 hpost.2
    refine ⟨y, hxy, ?_⟩
    have hr : y ∈ n ∧ ∀ y' ∈ n, prio y ≤ prio y' := ⟨hyn, hymin⟩
    simp only [if_pos hpost, if_pos hr]
    exact le_rfl
  · have hn0 : n = 0 := not_ne_iff.mp hn
    have hm0 : m = 0 := msetRel_empty_right.mp (hn0 ▸ hmn)
    simp [prioPeekMin, hm0, hn0, NRest.nrestRel]

/-! ## Protected-constant registration boundary -/

/-- Faithful Lean spelling of the source's `IS_BELOW_ID A`. -/
def IsBelowId (A : Set (α × α)) : Prop :=
  A ⊆ Set.diagonal α

theorem prio_self_param_of_belowId {A : Set (α × α)}
    (hA : IsBelowId A) (prio : α → κ) :
    (prio, prio) ∈ A →ᵣ Set.diagonal κ := by
  intro x y hxy
  exact congrArg prio (hA hxy)

theorem diagonal_orderPreserved [Preorder κ] :
    OrderPreserved (Set.diagonal κ) := by
  intro a a' b b' hab hab'
  change a = b at hab
  change a' = b' at hab'
  subst b
  subst b'
  rfl

sepref_decl_op prio_pop_min (α κ : Type) [LinearOrder κ]
    (prio : α → κ) :
    Multiset α → NRest (α × Multiset α) ECost :=
    prioPopMin prio
  interface := ∀ α κ : Type, [LinearOrder κ] →
    (α → κ) → MultisetI α → NRest (α × MultisetI α) ECost
  precondition := fun _ : Multiset α => True
  parametricity : ∀ (A : Set (α × α)), IsBelowId A →
      ((op_prio_pop_min α κ prio, op_prio_pop_min α κ prio) ∈
        fref (fun _ : Multiset α => True) (msetRel A)
          (fun _ => NRest.nrestRel (A ×ᵣ msetRel A))) := by
    intro A hA m n _ hmn
    exact prioPopMin_param (prio_self_param_of_belowId hA prio)
      diagonal_orderPreserved m n hmn

sepref_decl_op prio_peek_min (α κ : Type) [LinearOrder κ]
    (prio : α → κ) :
    Multiset α → NRest α ECost :=
    prioPeekMin prio
  interface := ∀ α κ : Type, [LinearOrder κ] →
    (α → κ) → MultisetI α → NRest α ECost
  precondition := fun _ : Multiset α => True
  parametricity : ∀ (A : Set (α × α)), IsBelowId A →
      ((op_prio_peek_min α κ prio, op_prio_peek_min α κ prio) ∈
        fref (fun _ : Multiset α => True) (msetRel A)
          (fun _ => NRest.nrestRel A)) := by
    intro A hA m n _ hmn
    exact prioPeekMin_param (prio_self_param_of_belowId hA prio)
      diagonal_orderPreserved m n hmn

/-! The source's two `PR_CONST`/`UNPROTECT` pattern equations are definition
folds here; no synthetic protection operator is introduced. -/

theorem fold_op_prio_pop_min [LinearOrder κ] (prio : α → κ) :
    op_prio_pop_min α κ prio = prioPopMin prio := rfl

theorem fold_op_prio_peek_min [LinearOrder κ] (prio : α → κ) :
    op_prio_peek_min α κ prio = prioPeekMin prio := rfl

/-! ## Generic, below-identity, diagonal, and registration gates -/

private example [LinearOrder κ] [LinearOrder μ]
    (A : Set (α × β)) (B : Set (κ × μ))
    (prio' : α → κ) (prio : β → μ)
    (hprio : (prio', prio) ∈ A →ᵣ B) (hord : OrderPreserved B) :
    (prioPopMin prio', prioPopMin prio) ∈
      msetRel A →ᵣ NRest.nrestRel (A ×ᵣ msetRel A) :=
  prioPopMin_param hprio hord

private example [LinearOrder κ] [LinearOrder μ]
    (A : Set (α × β)) (B : Set (κ × μ))
    (prio' : α → κ) (prio : β → μ)
    (hprio : (prio', prio) ∈ A →ᵣ B) (hord : OrderPreserved B) :
    (prioPeekMin prio', prioPeekMin prio) ∈
      msetRel A →ᵣ NRest.nrestRel A :=
  prioPeekMin_param hprio hord

private example [LinearOrder κ] (prio : α → κ)
    (A : Set (α × α)) (hA : IsBelowId A) :
    ((op_prio_pop_min α κ prio, op_prio_pop_min α κ prio) ∈
      fref (fun _ : Multiset α => True) (msetRel A)
        (fun _ => NRest.nrestRel (A ×ᵣ msetRel A))) :=
  op_prio_pop_min_fref α κ prio A hA

private example [LinearOrder κ] (prio : α → κ)
    (A : Set (α × α)) (hA : IsBelowId A) :
    ((op_prio_peek_min α κ prio, op_prio_peek_min α κ prio) ∈
      fref (fun _ : Multiset α => True) (msetRel A)
        (fun _ => NRest.nrestRel A)) :=
  op_prio_peek_min_fref α κ prio A hA

private example (prio : ℕ → ℕ) :
    ((op_prio_pop_min ℕ ℕ prio, op_prio_pop_min ℕ ℕ prio) ∈
      fref (fun _ : Multiset ℕ => True) (msetRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel
          (Set.diagonal ℕ ×ᵣ msetRel (Set.diagonal ℕ)))) :=
  op_prio_pop_min_fref ℕ ℕ prio (Set.diagonal ℕ) fun _ h => h

private example (prio : ℕ → ℕ) :
    ((op_prio_peek_min ℕ ℕ prio, op_prio_peek_min ℕ ℕ prio) ∈
      fref (fun _ : Multiset ℕ => True) (msetRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (Set.diagonal ℕ))) :=
  op_prio_peek_min_fref ℕ ℕ prio (Set.diagonal ℕ) fun _ h => h

example : op_prio_pop_min ::ᵢ
    ((α κ : Type) → [LinearOrder κ] →
      (α → κ) → MultisetI α → NRest (α × MultisetI α) ECost) :=
  op_prio_pop_min_registration_itype

example : op_prio_peek_min ::ᵢ
    ((α κ : Type) → [LinearOrder κ] →
      (α → κ) → MultisetI α → NRest α ECost) :=
  op_prio_peek_min_registration_itype

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``op_prio_pop_min_fref, ``op_prio_peek_min_fref] do
    unless rules.contains n do
      throwError "priority-bag interface gate: missing parametricity rule {n}"

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.prioPopMin_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prioPopMin_param

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_prio_pop_min_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_prio_pop_min_fref

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_prio_peek_min_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_prio_peek_min_fref

end Lax13Proofs.Refine.Sepref.Iicf
