import Lax13Proofs.Refine.Iicf.Basic

/-!
# Set interface

Source-faithful interface leaf for
`IICF/Intf/IICF_Set.thy` at `isabelle_llvm_time` commit `42dd7f5`.
This file declares the abstract set interface and its eleven cost-silent
operations.  It deliberately contains no concrete representation.

## Source table

| Source declaration | Lean declaration | Parametricity requirements |
|---|---|---|
| `set_empty` | `op_set_empty` | none |
| `set_is_empty` | `op_set_is_empty` | none |
| `set_member` | `op_set_member` | `SingleValued R`, `SingleValued (relConverse R)` |
| `set_insert` | `op_set_insert` | `SingleValued R` |
| `set_delete` | `op_set_delete` | relation and converse single-valued |
| `set_union` | `op_set_union` | none |
| `set_inter` | `op_set_inter` | relation and converse single-valued |
| `set_diff` | `op_set_diff` | relation and converse single-valued |
| `set_subseteq` | `op_set_subseteq` | relation and converse single-valued |
| `set_subset` | `op_set_subset` | relation and converse single-valued |
| `set_pick` | `op_set_pick` | nonempty precondition; nondeterministic result |
| `pat_set`, `pat_set2` | no separate declaration | Isabelle term-pattern rewrites are replaced by the explicit `op_set_*` definitions and operation registrations |
| `set_custom_empty` locale | no separate locale | any concrete empty operation registers directly against `op_set_empty` through `sepref_decl_impl` |

The source's `set_rel` is a bidirectional lifting: every element on
either side has a related element on the other side.  No generic set
relator existed in the imported tower, so it is defined here rather than
replacing the source contracts by diagonal relations.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {α β : Type}

/-! ## Set relator and its source-side relation properties -/

/-- Converse of a concrete-first relation. -/
def relConverse (R : Set (α × β)) : Set (β × α) :=
  {p | (p.2, p.1) ∈ R}

@[simp] theorem mem_relConverse_iff {R : Set (α × β)} {a : α} {b : β} :
    (b, a) ∈ relConverse R ↔ (a, b) ∈ R := Iff.rfl

/-- The source's `⟨R⟩set_rel`: both sets consist precisely of elements
covered by `R`, without assuming that `R` is functional. -/
def setRel (R : Set (α × β)) : Set (Set α × Set β) :=
  {p |
    (∀ a, a ∈ p.1 → ∃ b, b ∈ p.2 ∧ (a, b) ∈ R) ∧
    (∀ b, b ∈ p.2 → ∃ a, a ∈ p.1 ∧ (a, b) ∈ R)}

@[simp] theorem mem_setRel_iff {R : Set (α × β)} {s : Set α} {t : Set β} :
    (s, t) ∈ setRel R ↔
      (∀ a, a ∈ s → ∃ b, b ∈ t ∧ (a, b) ∈ R) ∧
      (∀ b, b ∈ t → ∃ a, a ∈ s ∧ (a, b) ∈ R) := Iff.rfl

theorem setRel_empty (R : Set (α × β)) :
    ((∅ : Set α), (∅ : Set β)) ∈ setRel R := by simp

theorem setRel_isEmpty {R : Set (α × β)} {s : Set α} {t : Set β}
    (hst : (s, t) ∈ setRel R) : (s = ∅) = (t = ∅) := by
  apply propext
  constructor
  · intro hs
    subst s
    ext b
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hb
    obtain ⟨a, ha, -⟩ := hst.2 b hb
    exact ha
  · intro ht
    subst t
    ext a
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ha
    obtain ⟨b, hb, -⟩ := hst.1 a ha
    exact hb

theorem setRel_member {R : Set (α × β)}
    (hR : SingleValued R) (hRc : SingleValued (relConverse R))
    {a : α} {b : β} (hab : (a, b) ∈ R) {s : Set α} {t : Set β}
    (hst : (s, t) ∈ setRel R) : (a ∈ s) = (b ∈ t) := by
  apply propext
  constructor
  · intro ha
    obtain ⟨b', hb', hab'⟩ := hst.1 a ha
    have : b' = b := hR a b' b hab' hab
    simpa [this] using hb'
  · intro hb
    obtain ⟨a', ha', ha'b⟩ := hst.2 b hb
    have : a' = a := hRc b a' a ha'b hab
    simpa [this] using ha'

theorem setRel_insert {R : Set (α × β)} (_hR : SingleValued R)
    {a : α} {b : β} (hab : (a, b) ∈ R) {s : Set α} {t : Set β}
    (hst : (s, t) ∈ setRel R) :
    (Set.insert a s, Set.insert b t) ∈ setRel R := by
  constructor
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨b, Set.mem_insert b t, hab⟩
    · obtain ⟨y, hy, hxy⟩ := hst.1 x hx
      exact ⟨y, Set.mem_insert_of_mem b hy, hxy⟩
  · intro y hy
    rcases hy with rfl | hy
    · exact ⟨a, Set.mem_insert a s, hab⟩
    · obtain ⟨x, hx, hxy⟩ := hst.2 y hy
      exact ⟨x, Set.mem_insert_of_mem a hx, hxy⟩

theorem setRel_delete {R : Set (α × β)}
    (hR : SingleValued R) (hRc : SingleValued (relConverse R))
    {a : α} {b : β} (hab : (a, b) ∈ R) {s : Set α} {t : Set β}
    (hst : (s, t) ∈ setRel R) :
    (s \ {a}, t \ {b}) ∈ setRel R := by
  constructor
  · rintro x ⟨hxs, hxa⟩
    obtain ⟨y, hyt, hxy⟩ := hst.1 x hxs
    refine ⟨y, ⟨hyt, ?_⟩, hxy⟩
    intro hyb
    subst y
    exact hxa (hRc b x a hxy hab)
  · rintro y ⟨hyt, hyb⟩
    obtain ⟨x, hxs, hxy⟩ := hst.2 y hyt
    refine ⟨x, ⟨hxs, ?_⟩, hxy⟩
    intro hxa
    subst x
    exact hyb (hR a y b hxy hab)

theorem setRel_union {R : Set (α × β)} {s₁ s₂ : Set α} {t₁ t₂ : Set β}
    (h₁ : (s₁, t₁) ∈ setRel R) (h₂ : (s₂, t₂) ∈ setRel R) :
    (s₁ ∪ s₂, t₁ ∪ t₂) ∈ setRel R := by
  constructor
  · rintro a (ha | ha)
    · obtain ⟨b, hb, hab⟩ := h₁.1 a ha
      exact ⟨b, Or.inl hb, hab⟩
    · obtain ⟨b, hb, hab⟩ := h₂.1 a ha
      exact ⟨b, Or.inr hb, hab⟩
  · rintro b (hb | hb)
    · obtain ⟨a, ha, hab⟩ := h₁.2 b hb
      exact ⟨a, Or.inl ha, hab⟩
    · obtain ⟨a, ha, hab⟩ := h₂.2 b hb
      exact ⟨a, Or.inr ha, hab⟩

theorem setRel_inter {R : Set (α × β)}
    (hR : SingleValued R) (hRc : SingleValued (relConverse R))
    {s₁ s₂ : Set α} {t₁ t₂ : Set β}
    (h₁ : (s₁, t₁) ∈ setRel R) (h₂ : (s₂, t₂) ∈ setRel R) :
    (s₁ ∩ s₂, t₁ ∩ t₂) ∈ setRel R := by
  constructor
  · rintro a ⟨ha₁, ha₂⟩
    obtain ⟨b₁, hb₁, hab₁⟩ := h₁.1 a ha₁
    obtain ⟨b₂, hb₂, hab₂⟩ := h₂.1 a ha₂
    have : b₁ = b₂ := hR a b₁ b₂ hab₁ hab₂
    subst b₂
    exact ⟨b₁, ⟨hb₁, hb₂⟩, hab₁⟩
  · rintro b ⟨hb₁, hb₂⟩
    obtain ⟨a₁, ha₁, ha₁b⟩ := h₁.2 b hb₁
    obtain ⟨a₂, ha₂, ha₂b⟩ := h₂.2 b hb₂
    have : a₁ = a₂ := hRc b a₁ a₂ ha₁b ha₂b
    subst a₂
    exact ⟨a₁, ⟨ha₁, ha₂⟩, ha₁b⟩

theorem setRel_diff {R : Set (α × β)}
    (hR : SingleValued R) (hRc : SingleValued (relConverse R))
    {s₁ s₂ : Set α} {t₁ t₂ : Set β}
    (h₁ : (s₁, t₁) ∈ setRel R) (h₂ : (s₂, t₂) ∈ setRel R) :
    (s₁ \ s₂, t₁ \ t₂) ∈ setRel R := by
  constructor
  · rintro a ⟨ha₁, ha₂⟩
    obtain ⟨b, hb₁, hab⟩ := h₁.1 a ha₁
    refine ⟨b, ⟨hb₁, ?_⟩, hab⟩
    intro hb₂
    obtain ⟨a', ha'₂, ha'b⟩ := h₂.2 b hb₂
    exact ha₂ (by simpa [hRc b a' a ha'b hab] using ha'₂)
  · rintro b ⟨hb₁, hb₂⟩
    obtain ⟨a, ha₁, hab⟩ := h₁.2 b hb₁
    refine ⟨a, ⟨ha₁, ?_⟩, hab⟩
    intro ha₂
    obtain ⟨b', hb'₂, hab'⟩ := h₂.1 a ha₂
    exact hb₂ (by simpa [hR a b' b hab' hab] using hb'₂)

theorem setRel_subseteq {R : Set (α × β)}
    (hR : SingleValued R) (hRc : SingleValued (relConverse R))
    {s₁ s₂ : Set α} {t₁ t₂ : Set β}
    (h₁ : (s₁, t₁) ∈ setRel R) (h₂ : (s₂, t₂) ∈ setRel R) :
    (s₁ ⊆ s₂) = (t₁ ⊆ t₂) := by
  apply propext
  constructor
  · intro hs b hb₁
    obtain ⟨a, ha₁, hab⟩ := h₁.2 b hb₁
    exact (setRel_member hR hRc hab h₂).mp (hs ha₁)
  · intro ht a ha₁
    obtain ⟨b, hb₁, hab⟩ := h₁.1 a ha₁
    exact (setRel_member hR hRc hab h₂).mpr (ht hb₁)

theorem setRel_eq {R : Set (α × β)}
    (hR : SingleValued R) (hRc : SingleValued (relConverse R))
    {s₁ s₂ : Set α} {t₁ t₂ : Set β}
    (h₁ : (s₁, t₁) ∈ setRel R) (h₂ : (s₂, t₂) ∈ setRel R) :
    (s₁ = s₂) = (t₁ = t₂) := by
  simp only [Set.Subset.antisymm_iff]
  rw [setRel_subseteq hR hRc h₁ h₂, setRel_subseteq hR hRc h₂ h₁]

theorem setRel_subset {R : Set (α × β)}
    (hR : SingleValued R) (hRc : SingleValued (relConverse R))
    {s₁ s₂ : Set α} {t₁ t₂ : Set β}
    (h₁ : (s₁, t₁) ∈ setRel R) (h₂ : (s₂, t₂) ∈ setRel R) :
    (s₁ ⊂ s₂) = (t₁ ⊂ t₂) := by
  simp only [ssubset_iff_subset_ne]
  have hsub := setRel_subseteq hR hRc h₁ h₂
  have hne : (s₁ ≠ s₂) = (t₁ ≠ t₂) := congrArg Not (setRel_eq hR hRc h₁ h₂)
  rw [hsub, hne]

/-- Classical truth-value projection used by the source's Boolean set
queries.  The interface is abstract, so computability is neither claimed
nor needed at this layer. -/
noncomputable def propBool (P : Prop) : Bool :=
  @decide P (Classical.propDecidable P)

theorem propBool_congr {P Q : Prop} (h : P = Q) : propBool P = propBool Q :=
  congrArg propBool h

/-! ## Nominal interface and relation inference -/

sepref_decl_intf (α) SetI is Set α

@[intf_of_rel] theorem setRel_intf (R : Set (α × β)) :
    intfOfRel (setRel R) (SetI β) := trivial

#guard_rel_interface (setRel (Set.diagonal ℕ)) is SetI ℕ

/-! ## Eleven source operations -/

sepref_decl_op set_empty (α : Type) : NRest (Set α) ECost :=
    NRest.returnT ∅
  interface := ∀ α : Type, NRest (SetI α) ECost
  precondition := True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      (op_set_empty α, op_set_empty β) ∈ NRest.nrestRel (setRel R) := by
    intro β R
    exact NRest.param_returnT (setRel_empty R)

sepref_decl_op set_is_empty (α : Type) : Set α → NRest Bool ECost :=
    fun s => NRest.returnT (propBool (s = ∅))
  interface := ∀ α : Type, SetI α → NRest Bool ECost
  precondition := fun _ : Set α => True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      ((op_set_is_empty α, op_set_is_empty β) ∈
        fref (fun _ : Set β => True) (setRel R)
          (fun _ => NRest.nrestRel (Set.diagonal Bool))) := by
    intro β R s t _ hst
    exact NRest.param_returnT (propBool_congr (setRel_isEmpty hst))

sepref_decl_op set_member (α : Type) : α → Set α → NRest Bool ECost :=
    fun a s => NRest.returnT (propBool (a ∈ s))
  interface := ∀ α : Type, α → SetI α → NRest Bool ECost
  precondition := fun _ : α => fun _ : Set α => True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      SingleValued R → SingleValued (relConverse R) →
      ((op_set_member α, op_set_member β) ∈
        fref (fun _ : β => True) R
          (fun _ => setRel R →ᵣ NRest.nrestRel (Set.diagonal Bool))) := by
    intro β R hR hRc a b _ hab s t hst
    exact NRest.param_returnT (propBool_congr (setRel_member hR hRc hab hst))

sepref_decl_op set_insert (α : Type) : α → Set α → NRest (Set α) ECost :=
    fun a s => NRest.returnT (Set.insert a s)
  interface := ∀ α : Type, α → SetI α → NRest (SetI α) ECost
  precondition := fun _ : α => fun _ : Set α => True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      SingleValued R →
      ((op_set_insert α, op_set_insert β) ∈
        fref (fun _ : β => True) R
          (fun _ => setRel R →ᵣ NRest.nrestRel (setRel R))) := by
    intro β R hR a b _ hab s t hst
    exact NRest.param_returnT (setRel_insert hR hab hst)

sepref_decl_op set_delete (α : Type) : α → Set α → NRest (Set α) ECost :=
    fun a s => NRest.returnT (s \ {a})
  interface := ∀ α : Type, α → SetI α → NRest (SetI α) ECost
  precondition := fun _ : α => fun _ : Set α => True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      SingleValued R → SingleValued (relConverse R) →
      ((op_set_delete α, op_set_delete β) ∈
        fref (fun _ : β => True) R
          (fun _ => setRel R →ᵣ NRest.nrestRel (setRel R))) := by
    intro β R hR hRc a b _ hab s t hst
    exact NRest.param_returnT (setRel_delete hR hRc hab hst)

sepref_decl_op set_union (α : Type) : Set α → Set α → NRest (Set α) ECost :=
    fun s₁ s₂ => NRest.returnT (s₁ ∪ s₂)
  interface := ∀ α : Type, SetI α → SetI α → NRest (SetI α) ECost
  precondition := fun _ : Set α => fun _ : Set α => True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      ((op_set_union α, op_set_union β) ∈
        fref (fun _ : Set β => True) (setRel R)
          (fun _ => setRel R →ᵣ NRest.nrestRel (setRel R))) := by
    intro β R s₁ t₁ _ h₁ s₂ t₂ h₂
    exact NRest.param_returnT (setRel_union h₁ h₂)

sepref_decl_op set_inter (α : Type) : Set α → Set α → NRest (Set α) ECost :=
    fun s₁ s₂ => NRest.returnT (s₁ ∩ s₂)
  interface := ∀ α : Type, SetI α → SetI α → NRest (SetI α) ECost
  precondition := fun _ : Set α => fun _ : Set α => True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      SingleValued R → SingleValued (relConverse R) →
      ((op_set_inter α, op_set_inter β) ∈
        fref (fun _ : Set β => True) (setRel R)
          (fun _ => setRel R →ᵣ NRest.nrestRel (setRel R))) := by
    intro β R hR hRc s₁ t₁ _ h₁ s₂ t₂ h₂
    exact NRest.param_returnT (setRel_inter hR hRc h₁ h₂)

sepref_decl_op set_diff (α : Type) : Set α → Set α → NRest (Set α) ECost :=
    fun s₁ s₂ => NRest.returnT (s₁ \ s₂)
  interface := ∀ α : Type, SetI α → SetI α → NRest (SetI α) ECost
  precondition := fun _ : Set α => fun _ : Set α => True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      SingleValued R → SingleValued (relConverse R) →
      ((op_set_diff α, op_set_diff β) ∈
        fref (fun _ : Set β => True) (setRel R)
          (fun _ => setRel R →ᵣ NRest.nrestRel (setRel R))) := by
    intro β R hR hRc s₁ t₁ _ h₁ s₂ t₂ h₂
    exact NRest.param_returnT (setRel_diff hR hRc h₁ h₂)

sepref_decl_op set_subseteq (α : Type) : Set α → Set α → NRest Bool ECost :=
    fun s₁ s₂ => NRest.returnT (propBool (s₁ ⊆ s₂))
  interface := ∀ α : Type, SetI α → SetI α → NRest Bool ECost
  precondition := fun _ : Set α => fun _ : Set α => True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      SingleValued R → SingleValued (relConverse R) →
      ((op_set_subseteq α, op_set_subseteq β) ∈
        fref (fun _ : Set β => True) (setRel R)
          (fun _ => setRel R →ᵣ NRest.nrestRel (Set.diagonal Bool))) := by
    intro β R hR hRc s₁ t₁ _ h₁ s₂ t₂ h₂
    exact NRest.param_returnT (propBool_congr (setRel_subseteq hR hRc h₁ h₂))

sepref_decl_op set_subset (α : Type) : Set α → Set α → NRest Bool ECost :=
    fun s₁ s₂ => NRest.returnT (propBool (s₁ ⊂ s₂))
  interface := ∀ α : Type, SetI α → SetI α → NRest Bool ECost
  precondition := fun _ : Set α => fun _ : Set α => True
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      SingleValued R → SingleValued (relConverse R) →
      ((op_set_subset α, op_set_subset β) ∈
        fref (fun _ : Set β => True) (setRel R)
          (fun _ => setRel R →ᵣ NRest.nrestRel (Set.diagonal Bool))) := by
    intro β R hR hRc s₁ t₁ _ h₁ s₂ t₂ h₂
    exact NRest.param_returnT (propBool_congr (setRel_subset hR hRc h₁ h₂))

sepref_decl_op set_pick (α : Type) : Set α → NRest α ECost :=
    fun s => NRest.bindT (NRest.assert s.Nonempty) fun _ =>
      NRest.spec (fun a => a ∈ s) (fun _ => 0)
  interface := ∀ α : Type, SetI α → NRest α ECost
  precondition := fun s : Set α => s.Nonempty
  parametricity : ∀ {β : Type} (R : Set (α × β)),
      ((op_set_pick α, op_set_pick β) ∈
        fref (fun t : Set β => t.Nonempty) (setRel R)
          (fun _ => NRest.nrestRel R)) := by
    intro β R s t ht hst
    have hs : s.Nonempty := by
      obtain ⟨b, hb⟩ := ht
      obtain ⟨a, ha, -⟩ := hst.2 b hb
      exact ⟨a, ha⟩
    simp only [op_set_pick, NRest.assert_pos hs, NRest.assert_pos ht,
      NRest.returnT_bindT]
    apply NRest.nrestRel_of_le
    rw [NRest.spec, NRest.spec]
    apply NRest.rest_refines_concFun'
    intro X hX a ha
    have hX' := NRest.rest_inj_iff.mp hX
    subst X
    have has : a ∈ s := by
      by_contra hnot
      simp [hnot] at ha
    obtain ⟨b, hbt, hab⟩ := hst.1 a has
    exact ⟨b, hab, by simp [has, hbt]⟩

/-! ## Compact concrete, registration, and database gates -/

private theorem diagonal_setRel (s : Set ℕ) :
    (s, s) ∈ setRel (Set.diagonal ℕ) := by
  constructor <;> intro x hx <;> exact ⟨x, hx, rfl⟩

private theorem diagonal_converse_singleValued :
    SingleValued (relConverse (Set.diagonal ℕ)) := by
  rintro b a a' hba hba'
  change a = b at hba
  change a' = b at hba'
  exact hba.trans hba'.symm

private example :
    (op_set_empty ℕ, op_set_empty ℕ) ∈ NRest.nrestRel (setRel (Set.diagonal ℕ)) :=
  op_set_empty_fref ℕ (Set.diagonal ℕ)

private example :
    (op_set_is_empty ℕ, op_set_is_empty ℕ) ∈
      fref (fun _ : Set ℕ => True) (setRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) :=
  op_set_is_empty_fref ℕ (Set.diagonal ℕ)

private example :
    (op_set_member ℕ, op_set_member ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => setRel (Set.diagonal ℕ) →ᵣ NRest.nrestRel (Set.diagonal Bool)) :=
  op_set_member_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued

private example :
    (op_set_insert ℕ, op_set_insert ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => setRel (Set.diagonal ℕ) →ᵣ NRest.nrestRel (setRel (Set.diagonal ℕ))) :=
  op_set_insert_fref ℕ (Set.diagonal ℕ) singleValued_diagonal

private example :
    (op_set_delete ℕ, op_set_delete ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => setRel (Set.diagonal ℕ) →ᵣ NRest.nrestRel (setRel (Set.diagonal ℕ))) :=
  op_set_delete_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued

private example :
    (op_set_union ℕ, op_set_union ℕ) ∈
      fref (fun _ : Set ℕ => True) (setRel (Set.diagonal ℕ))
        (fun _ => setRel (Set.diagonal ℕ) →ᵣ NRest.nrestRel (setRel (Set.diagonal ℕ))) :=
  op_set_union_fref ℕ (Set.diagonal ℕ)

private example :
    (op_set_inter ℕ, op_set_inter ℕ) ∈
      fref (fun _ : Set ℕ => True) (setRel (Set.diagonal ℕ))
        (fun _ => setRel (Set.diagonal ℕ) →ᵣ NRest.nrestRel (setRel (Set.diagonal ℕ))) :=
  op_set_inter_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued

private example :
    (op_set_diff ℕ, op_set_diff ℕ) ∈
      fref (fun _ : Set ℕ => True) (setRel (Set.diagonal ℕ))
        (fun _ => setRel (Set.diagonal ℕ) →ᵣ NRest.nrestRel (setRel (Set.diagonal ℕ))) :=
  op_set_diff_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued

private example :
    (op_set_subseteq ℕ, op_set_subseteq ℕ) ∈
      fref (fun _ : Set ℕ => True) (setRel (Set.diagonal ℕ))
        (fun _ => setRel (Set.diagonal ℕ) →ᵣ NRest.nrestRel (Set.diagonal Bool)) :=
  op_set_subseteq_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued

private example :
    (op_set_subset ℕ, op_set_subset ℕ) ∈
      fref (fun _ : Set ℕ => True) (setRel (Set.diagonal ℕ))
        (fun _ => setRel (Set.diagonal ℕ) →ᵣ NRest.nrestRel (Set.diagonal Bool)) :=
  op_set_subset_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued

private example :
    (op_set_pick ℕ, op_set_pick ℕ) ∈
      fref (fun s : Set ℕ => s.Nonempty) (setRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) :=
  op_set_pick_fref ℕ (Set.diagonal ℕ)

example : op_set_empty ℕ ::ᵢ NRest (SetI ℕ) ECost :=
  op_set_empty_registration_itype
example : op_set_is_empty ℕ ::ᵢ (SetI ℕ → NRest Bool ECost) :=
  op_set_is_empty_registration_itype
example : op_set_member ℕ ::ᵢ (ℕ → SetI ℕ → NRest Bool ECost) :=
  op_set_member_registration_itype
example : op_set_insert ℕ ::ᵢ (ℕ → SetI ℕ → NRest (SetI ℕ) ECost) :=
  op_set_insert_registration_itype
example : op_set_delete ℕ ::ᵢ (ℕ → SetI ℕ → NRest (SetI ℕ) ECost) :=
  op_set_delete_registration_itype
example : op_set_union ℕ ::ᵢ (SetI ℕ → SetI ℕ → NRest (SetI ℕ) ECost) :=
  op_set_union_registration_itype
example : op_set_inter ℕ ::ᵢ (SetI ℕ → SetI ℕ → NRest (SetI ℕ) ECost) :=
  op_set_inter_registration_itype
example : op_set_diff ℕ ::ᵢ (SetI ℕ → SetI ℕ → NRest (SetI ℕ) ECost) :=
  op_set_diff_registration_itype
example : op_set_subseteq ℕ ::ᵢ (SetI ℕ → SetI ℕ → NRest Bool ECost) :=
  op_set_subseteq_registration_itype
example : op_set_subset ℕ ::ᵢ (SetI ℕ → SetI ℕ → NRest Bool ECost) :=
  op_set_subset_registration_itype
example : op_set_pick ℕ ::ᵢ (SetI ℕ → NRest ℕ ECost) :=
  op_set_pick_registration_itype

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``op_set_empty_fref, ``op_set_is_empty_fref, ``op_set_member_fref,
      ``op_set_insert_fref, ``op_set_delete_fref, ``op_set_union_fref,
      ``op_set_inter_fref, ``op_set_diff_fref, ``op_set_subseteq_fref,
      ``op_set_subset_fref, ``op_set_pick_fref] do
    unless rules.contains n do
      throwError "set interface gate: missing parametricity rule {n}"

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.setRel_inter' does not depend on any axioms -/
#guard_msgs in
#print axioms setRel_inter

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_set_member_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_set_member_fref

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_set_pick_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_set_pick_fref

end Lax13Proofs.Refine.Sepref.Iicf
