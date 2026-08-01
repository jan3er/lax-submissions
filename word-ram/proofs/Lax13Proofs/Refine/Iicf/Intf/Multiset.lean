import Lax13Proofs.Refine.Iicf.Intf.Set

/-!
# Multiset interface

Source-faithful semantic leaf for `IICF/Intf/IICF_Multiset.thy` at
`isabelle_llvm_time` commit `42dd7f5`.

## Source accounting

| Active source family | Lean disposition |
|---|---|
| additions to `rel_mset` | `rel_mset_add`, `rel_mset_single`, `rel_mset_erase`, `rel_mset_sub`, and `rel_mset_count` |
| `mset_rel` conversions and parameters | `msetRel`, its diagonal/empty/add/insert/sub/count results, and `msetRel_carrier` |
| `mset_is_empty` | `msetIsEmpty` and `msetRel_isEmpty` |
| nine operations | exactly nine cost-silent `sepref_decl_op`s below |
| commented-out `mset_single` operation | inactive source text; no operation is emitted |
| two pattern blocks | the explicit operations plus the fold/algebra lemmas below are the Lean boundary; there is no second term-pattern API |
| `mset_custom_empty` locale | `msetCustomEmpty_fold`; concrete representations register their own empty implementation against `op_mset_empty` |

Mathlib's `Multiset.Rel` is the direct analogue of Isabelle's `rel_mset`.
Deletion, subtraction, membership, and count retain both source uniqueness
hypotheses; no diagonal weakening is used in their generic rules.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {α β : Type}

/-! ## Relational multiset theory -/

/-- Classical spelling of multiset subtraction, independent of an exposed
`DecidableEq` parameter at the abstract interface. -/
noncomputable def msetSub (m n : Multiset α) : Multiset α :=
  @Multiset.sub α (Classical.decEq α) m n

noncomputable def msetErase (m : Multiset α) (x : α) : Multiset α :=
  @Multiset.erase α (Classical.decEq α) m x

noncomputable def msetCount (m : Multiset α) (x : α) : ℕ :=
  @Multiset.count α (Classical.decEq α) x m

/-- Source `⟨A⟩mset_rel`. -/
def msetRel (A : Set (α × β)) : Set (Multiset α × Multiset β) :=
  {p | Multiset.Rel (fun a b => (a, b) ∈ A) p.1 p.2}

@[simp] theorem mem_msetRel_iff {A : Set (α × β)}
    {m : Multiset α} {n : Multiset β} :
    (m, n) ∈ msetRel A ↔ Multiset.Rel (fun a b => (a, b) ∈ A) m n :=
  Iff.rfl

@[simp] theorem msetRel_diagonal :
    msetRel (Set.diagonal α) = Set.diagonal (Multiset α) := by
  apply Set.Subset.antisymm
  · rintro ⟨m, n⟩ h
    change m = n
    exact Multiset.rel_eq.mp h
  · rintro ⟨m, n⟩ h
    change m = n at h
    subst n
    exact Multiset.rel_eq_refl

/-- Source `rel_mset_Plus_gen`. -/
theorem rel_mset_add {A : Set (α × β)} {m₁ m₂ : Multiset α}
    {n₁ n₂ : Multiset β} (h₁ : (m₁, n₁) ∈ msetRel A)
    (h₂ : (m₂, n₂) ∈ msetRel A) :
    (m₁ + m₂, n₁ + n₂) ∈ msetRel A :=
  Multiset.Rel.add h₁ h₂

/-- Source `rel_mset_single`. -/
theorem rel_mset_single {A : Set (α × β)} {x : α} {y : β}
    (hxy : (x, y) ∈ A) :
    (({x} : Multiset α), ({y} : Multiset β)) ∈ msetRel A :=
  show Multiset.Rel (fun a b => (a, b) ∈ A) {x} {y} from
    Multiset.Rel.cons hxy Multiset.Rel.zero

private theorem mset_related_eq {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A))
    {x a : α} {y b : β} (hxy : (x, y) ∈ A) (hab : (a, b) ∈ A) :
    (x = a) = (y = b) := by
  apply propext
  constructor
  · intro h
    subst a
    exact hA x y b hxy hab
  · intro h
    subst b
    exact hAc y x a hxy hab

/-- Source `rel_mset_Minus`: synchronized deletion of one related value. -/
theorem rel_mset_erase {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A))
    {m : Multiset α} {n : Multiset β} (hmn : (m, n) ∈ msetRel A)
    {x : α} {y : β} (hxy : (x, y) ∈ A) :
    (msetErase m x, msetErase n y) ∈ msetRel A := by
  classical
  change Multiset.Rel (fun a b => (a, b) ∈ A) m n at hmn
  induction hmn with
  | zero => simp [msetErase]
  | @cons a b m n hab hmn ih =>
      by_cases hax : a = x
      · subst a
        have hby : b = y := hA x b y hab hxy
        subst b
        simpa [msetErase] using hmn
      · have hby : b ≠ y := by
          intro h
          subst b
          exact hax (hAc y a x hab hxy)
        rw [msetErase, Multiset.erase_cons_tail m hax,
          msetErase, Multiset.erase_cons_tail n hby]
        exact Multiset.Rel.cons hab ih

@[simp] theorem msetSub_zero (m : Multiset α) : msetSub m 0 = m := by
  classical
  exact Multiset.sub_zero m

@[simp] theorem msetSub_cons (m n : Multiset α) (x : α) :
    msetSub m (x ::ₘ n) = msetSub (msetErase m x) n := by
  classical
  exact Multiset.sub_cons x m n

/-- Source `rel_mset_Minus_gen`. -/
theorem rel_mset_sub {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A))
    {m₁ m₂ : Multiset α} {n₁ n₂ : Multiset β}
    (h₁ : (m₁, n₁) ∈ msetRel A) (h₂ : (m₂, n₂) ∈ msetRel A) :
    (msetSub m₁ m₂, msetSub n₁ n₂) ∈ msetRel A := by
  classical
  change Multiset.Rel (fun a b => (a, b) ∈ A) m₂ n₂ at h₂
  induction h₂ generalizing m₁ n₁ with
  | zero => simpa using h₁
  | @cons x y m₂ n₂ hxy h₂ ih =>
      rw [msetSub_cons, msetSub_cons]
      exact ih (rel_mset_erase hA hAc h₁ hxy)

/-- Source `pcr_count`. -/
theorem rel_mset_count {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A))
    {m : Multiset α} {n : Multiset β} (hmn : (m, n) ∈ msetRel A)
    {x : α} {y : β} (hxy : (x, y) ∈ A) :
    msetCount m x = msetCount n y := by
  classical
  change Multiset.Rel (fun a b => (a, b) ∈ A) m n at hmn
  induction hmn with
  | zero => simp [msetCount]
  | @cons a b m n hab hmn ih =>
      have heq := mset_related_eq hA hAc hxy hab
      simp only [msetCount] at ih
      simp only [msetCount, Multiset.count_cons]
      rw [ih]
      congr 1
      by_cases hxa : x = a
      · have hyb : y = b := Eq.mp heq hxa
        simp [hxa, hyb]
      · have hyb : y ≠ b := by
          intro h
          exact hxa (Eq.mpr heq h)
        simp [hxa, hyb]

@[simp] theorem msetRel_empty_left {A : Set (α × β)} {n : Multiset β} :
    ((0 : Multiset α), n) ∈ msetRel A ↔ n = 0 :=
  Multiset.rel_zero_left

@[simp] theorem msetRel_empty_right {A : Set (α × β)} {m : Multiset α} :
    (m, (0 : Multiset β)) ∈ msetRel A ↔ m = 0 :=
  Multiset.rel_zero_right

theorem param_mset_empty (A : Set (α × β)) :
    ((0 : Multiset α), (0 : Multiset β)) ∈ msetRel A :=
  Multiset.Rel.zero

theorem param_mset_add {A : Set (α × β)} :
    ((fun m n : Multiset α => m + n), fun m n : Multiset β => m + n) ∈
      msetRel A →ᵣ msetRel A →ᵣ msetRel A := by
  intro m₁ n₁ h₁ m₂ n₂ h₂
  exact rel_mset_add h₁ h₂

theorem param_mset_insert {A : Set (α × β)} :
    ((fun x m => x ::ₘ m), fun y n => y ::ₘ n) ∈
      A →ᵣ msetRel A →ᵣ msetRel A := by
  intro x y hxy m n hmn
  exact Multiset.Rel.cons hxy hmn

theorem param_mset_sub {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A)) :
    (msetSub, msetSub) ∈ msetRel A →ᵣ msetRel A →ᵣ msetRel A := by
  intro m₁ n₁ h₁ m₂ n₂ h₂
  exact rel_mset_sub hA hAc h₁ h₂

theorem param_mset_count {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A)) :
    ((fun x m => msetCount m x), fun y n => msetCount n y) ∈
      A →ᵣ msetRel A →ᵣ Set.diagonal ℕ := by
  intro x y hxy m n hmn
  exact rel_mset_count hA hAc hmn hxy

/-- Source carrier conversion `set_mset`. -/
def msetCarrier (m : Multiset α) : Set α := {x | x ∈ m}

theorem msetRel_carrier {A : Set (α × β)} {m : Multiset α}
    {n : Multiset β} (hmn : (m, n) ∈ msetRel A) :
    (msetCarrier m, msetCarrier n) ∈ setRel A := by
  constructor
  · intro a ha
    obtain ⟨b, hb, hab⟩ := Multiset.exists_mem_of_rel_of_mem hmn ha
    exact ⟨b, hb, hab⟩
  · intro b hb
    have hflip : Multiset.Rel (fun b a => (a, b) ∈ A) n m :=
      Multiset.rel_flip.mpr hmn
    obtain ⟨a, ha, hab⟩ := Multiset.exists_mem_of_rel_of_mem hflip hb
    exact ⟨a, ha, hab⟩

def msetIsEmpty (m : Multiset α) : Prop := m = 0

theorem msetRel_isEmpty {A : Set (α × β)} {m : Multiset α}
    {n : Multiset β} (hmn : (m, n) ∈ msetRel A) :
    msetIsEmpty m = msetIsEmpty n := by
  apply propext
  constructor
  · intro hm
    exact msetRel_empty_left.mp (hm ▸ hmn)
  · intro hn
    exact msetRel_empty_right.mp (hn ▸ hmn)

/-! ## Nominal interface -/

sepref_decl_intf (α) MultisetI is Multiset α

@[intf_of_rel] theorem msetRel_intf (A : Set (α × β)) :
    intfOfRel (msetRel A) (MultisetI β) := trivial

#guard_rel_interface (msetRel (Set.diagonal ℕ)) is MultisetI ℕ

/-! ## Nine source operations -/

sepref_decl_op mset_empty (α : Type) : NRest (Multiset α) ECost :=
    NRest.returnT 0
  interface := ∀ α : Type, NRest (MultisetI α) ECost
  precondition := True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      (op_mset_empty α, op_mset_empty β) ∈ NRest.nrestRel (msetRel A) := by
    intro β A
    exact NRest.param_returnT (param_mset_empty A)

sepref_decl_op mset_is_empty (α : Type) : Multiset α → NRest Bool ECost :=
    fun m => NRest.returnT (propBool (msetIsEmpty m))
  interface := ∀ α : Type, MultisetI α → NRest Bool ECost
  precondition := fun _ : Multiset α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_mset_is_empty α, op_mset_is_empty β) ∈
        fref (fun _ : Multiset β => True) (msetRel A)
          (fun _ => NRest.nrestRel (Set.diagonal Bool))) := by
    intro β A m n _ hmn
    exact NRest.param_returnT (propBool_congr (msetRel_isEmpty hmn))

sepref_decl_op mset_insert (α : Type) :
    α → Multiset α → NRest (Multiset α) ECost :=
    fun x m => NRest.returnT (x ::ₘ m)
  interface := ∀ α : Type, α → MultisetI α → NRest (MultisetI α) ECost
  precondition := fun _ : α => fun _ : Multiset α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_mset_insert α, op_mset_insert β) ∈
        fref (fun _ : β => True) A
          (fun _ => msetRel A →ᵣ NRest.nrestRel (msetRel A))) := by
    intro β A x y _ hxy m n hmn
    exact NRest.param_returnT (Multiset.Rel.cons hxy hmn)

sepref_decl_op mset_delete (α : Type) :
    α → Multiset α → NRest (Multiset α) ECost :=
    fun x m => NRest.returnT (msetErase m x)
  interface := ∀ α : Type, α → MultisetI α → NRest (MultisetI α) ECost
  precondition := fun _ : α => fun _ : Multiset α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      SingleValued A → SingleValued (relConverse A) →
      ((op_mset_delete α, op_mset_delete β) ∈
        fref (fun _ : β => True) A
          (fun _ => msetRel A →ᵣ NRest.nrestRel (msetRel A))) := by
    intro β A hA hAc x y _ hxy m n hmn
    exact NRest.param_returnT (rel_mset_erase hA hAc hmn hxy)

sepref_decl_op mset_plus (α : Type) :
    Multiset α → Multiset α → NRest (Multiset α) ECost :=
    fun m n => NRest.returnT (m + n)
  interface := ∀ α : Type,
    MultisetI α → MultisetI α → NRest (MultisetI α) ECost
  precondition := fun _ : Multiset α => fun _ : Multiset α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_mset_plus α, op_mset_plus β) ∈
        fref (fun _ : Multiset β => True) (msetRel A)
          (fun _ => msetRel A →ᵣ NRest.nrestRel (msetRel A))) := by
    intro β A m₁ n₁ _ h₁ m₂ n₂ h₂
    exact NRest.param_returnT (rel_mset_add h₁ h₂)

sepref_decl_op mset_minus (α : Type) :
    Multiset α → Multiset α → NRest (Multiset α) ECost :=
    fun m n => NRest.returnT (msetSub m n)
  interface := ∀ α : Type,
    MultisetI α → MultisetI α → NRest (MultisetI α) ECost
  precondition := fun _ : Multiset α => fun _ : Multiset α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      SingleValued A → SingleValued (relConverse A) →
      ((op_mset_minus α, op_mset_minus β) ∈
        fref (fun _ : Multiset β => True) (msetRel A)
          (fun _ => msetRel A →ᵣ NRest.nrestRel (msetRel A))) := by
    intro β A hA hAc m₁ n₁ _ h₁ m₂ n₂ h₂
    exact NRest.param_returnT (rel_mset_sub hA hAc h₁ h₂)

sepref_decl_op mset_contains (α : Type) : α → Multiset α → NRest Bool ECost :=
    fun x m => NRest.returnT (propBool (x ∈ m))
  interface := ∀ α : Type, α → MultisetI α → NRest Bool ECost
  precondition := fun _ : α => fun _ : Multiset α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      SingleValued A → SingleValued (relConverse A) →
      ((op_mset_contains α, op_mset_contains β) ∈
        fref (fun _ : β => True) A
          (fun _ => msetRel A →ᵣ
            NRest.nrestRel (Set.diagonal Bool))) := by
    intro β A hA hAc x y _ hxy m n hmn
    have hmem := setRel_member hA hAc hxy (msetRel_carrier hmn)
    exact NRest.param_returnT (propBool_congr hmem)

sepref_decl_op mset_count (α : Type) : α → Multiset α → NRest ℕ ECost :=
    fun x m => NRest.returnT (msetCount m x)
  interface := ∀ α : Type, α → MultisetI α → NRest ℕ ECost
  precondition := fun _ : α => fun _ : Multiset α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      SingleValued A → SingleValued (relConverse A) →
      ((op_mset_count α, op_mset_count β) ∈
        fref (fun _ : β => True) A
          (fun _ => msetRel A →ᵣ NRest.nrestRel (Set.diagonal ℕ))) := by
    intro β A hA hAc x y _ hxy m n hmn
    exact NRest.param_returnT (rel_mset_count hA hAc hmn hxy)

sepref_decl_op mset_pick (α : Type) :
    Multiset α → NRest (α × Multiset α) ECost :=
    fun m => NRest.bindT (NRest.assert (m ≠ 0)) fun _ =>
      NRest.spec (fun p => m = ({p.1} : Multiset α) + p.2) (fun _ => 0)
  interface := ∀ α : Type,
    MultisetI α → NRest (α × MultisetI α) ECost
  precondition := fun m : Multiset α => m ≠ 0
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_mset_pick α, op_mset_pick β) ∈
        fref (fun n : Multiset β => n ≠ 0) (msetRel A)
          (fun _ => NRest.nrestRel (A ×ᵣ msetRel A))) := by
    intro β A m n hn hmn
    have hm : m ≠ 0 := by
      intro hm0
      exact hn (msetRel_empty_left.mp (hm0 ▸ hmn))
    simp only [op_mset_pick, NRest.assert_pos hm, NRest.assert_pos hn,
      NRest.returnT_bindT]
    apply NRest.nrestRel_of_le
    rw [NRest.spec, NRest.spec]
    apply NRest.rest_refines_concFun'
    intro X hX p hp
    have hX' := NRest.rest_inj_iff.mp hX
    subst X
    rcases p with ⟨x, mr⟩
    have hsplit : m = ({x} : Multiset α) + mr := by
      simpa using hp
    have hcons : Multiset.Rel (fun a b => (a, b) ∈ A) (x ::ₘ mr) n := by
      simpa [hsplit] using hmn
    obtain ⟨y, nr, hxy, hrest, hncons⟩ := Multiset.rel_cons_left.mp hcons
    refine ⟨(y, nr), ⟨hxy, hrest⟩, ?_⟩
    simp [hncons, hsplit]

/-! ## Pattern and custom-empty boundary -/

theorem fold_op_mset_empty : op_mset_empty α = NRest.returnT 0 := rfl

theorem fold_op_mset_is_empty (m : Multiset α) :
    op_mset_is_empty α m = NRest.returnT (propBool (m = 0)) := rfl

theorem fold_op_mset_insert (x : α) (m : Multiset α) :
    op_mset_insert α x m = NRest.returnT (x ::ₘ m) := rfl

theorem fold_op_mset_plus (m n : Multiset α) :
    op_mset_plus α m n = NRest.returnT (m + n) := rfl

theorem fold_op_mset_minus (m n : Multiset α) :
    op_mset_minus α m n = NRest.returnT (msetSub m n) := rfl

@[simp] theorem mset_single_add_left (x : α) (m : Multiset α) :
    ({x} : Multiset α) + m = x ::ₘ m := by simp

@[simp] theorem mset_single_add_right (x : α) (m : Multiset α) :
    m + ({x} : Multiset α) = x ::ₘ m := by
  calc
    m + ({x} : Multiset α) = ({x} : Multiset α) + m := Multiset.add_comm _ _
    _ = x ::ₘ m := mset_single_add_left x m

theorem mset_sub_single (m : Multiset α) (x : α) :
    msetSub m ({x} : Multiset α) = msetErase m x := by
  classical
  simpa only [msetSub, msetErase] using (Multiset.sub_singleton x m)

theorem mset_contains_iff_count_pos (m : Multiset α) (x : α) :
    x ∈ m ↔ 0 < msetCount m x := by
  classical
  exact Multiset.count_pos.symm

theorem msetCarrier_mem (m : Multiset α) (x : α) :
    x ∈ msetCarrier m ↔ x ∈ m := Iff.rfl

theorem fold_mset_plus_single_right (m : Multiset α) (x : α) :
    op_mset_plus α m {x} = op_mset_insert α x m := by
  unfold op_mset_plus op_mset_insert
  rw [mset_single_add_right]

theorem fold_mset_plus_single_left (m : Multiset α) (x : α) :
    op_mset_plus α {x} m = op_mset_insert α x m := by
  unfold op_mset_plus op_mset_insert
  rw [mset_single_add_left]

theorem fold_mset_minus_single (m : Multiset α) (x : α) :
    op_mset_minus α m {x} = op_mset_delete α x m := by
  unfold op_mset_minus op_mset_delete
  rw [mset_sub_single]

theorem fold_mset_contains_count (m : Multiset α) (x : α) :
    op_mset_contains α x m =
      NRest.returnT (propBool (0 < msetCount m x)) := by
  unfold op_mset_contains
  exact congrArg NRest.returnT
    (propBool_congr (propext (mset_contains_iff_count_pos m x)))

theorem fold_mset_contains_carrier (m : Multiset α) (x : α) :
    op_mset_contains α x m =
      NRest.returnT (propBool (x ∈ msetCarrier m)) := rfl

/-- Portable conclusion of source locale `mset_custom_empty`. -/
theorem msetCustomEmpty_fold (custom : Multiset α) (h : custom = 0) :
    custom = (0 : Multiset α) ∧
      op_mset_empty α = NRest.returnT custom := by
  subst custom
  exact ⟨rfl, rfl⟩

/-! ## Registration and theorem-database gates -/

private theorem diagonal_converse_singleValued_mset :
    SingleValued (relConverse (Set.diagonal ℕ)) := by
  rintro b a a' hba hba'
  change a = b at hba
  change a' = b at hba'
  exact hba.trans hba'.symm

private example :
    (op_mset_empty ℕ, op_mset_empty ℕ) ∈
      NRest.nrestRel (msetRel (Set.diagonal ℕ)) :=
  op_mset_empty_fref ℕ (Set.diagonal ℕ)

private example :
    (op_mset_is_empty ℕ, op_mset_is_empty ℕ) ∈
      fref (fun _ : Multiset ℕ => True) (msetRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) :=
  op_mset_is_empty_fref ℕ (Set.diagonal ℕ)

private example :
    (op_mset_insert ℕ, op_mset_insert ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => msetRel (Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (msetRel (Set.diagonal ℕ))) :=
  op_mset_insert_fref ℕ (Set.diagonal ℕ)

private example :
    (op_mset_delete ℕ, op_mset_delete ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => msetRel (Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (msetRel (Set.diagonal ℕ))) :=
  op_mset_delete_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued_mset

private example :
    (op_mset_plus ℕ, op_mset_plus ℕ) ∈
      fref (fun _ : Multiset ℕ => True) (msetRel (Set.diagonal ℕ))
        (fun _ => msetRel (Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (msetRel (Set.diagonal ℕ))) :=
  op_mset_plus_fref ℕ (Set.diagonal ℕ)

private example :
    (op_mset_minus ℕ, op_mset_minus ℕ) ∈
      fref (fun _ : Multiset ℕ => True) (msetRel (Set.diagonal ℕ))
        (fun _ => msetRel (Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (msetRel (Set.diagonal ℕ))) :=
  op_mset_minus_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued_mset

private example :
    (op_mset_contains ℕ, op_mset_contains ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => msetRel (Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (Set.diagonal Bool)) :=
  op_mset_contains_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued_mset

private example :
    (op_mset_count ℕ, op_mset_count ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => msetRel (Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (Set.diagonal ℕ)) :=
  op_mset_count_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued_mset

private example :
    (op_mset_pick ℕ, op_mset_pick ℕ) ∈
      fref (fun n : Multiset ℕ => n ≠ 0) (msetRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel
          (Set.diagonal ℕ ×ᵣ msetRel (Set.diagonal ℕ))) :=
  op_mset_pick_fref ℕ (Set.diagonal ℕ)

example : op_mset_empty ℕ ::ᵢ NRest (MultisetI ℕ) ECost :=
  op_mset_empty_registration_itype
example : op_mset_is_empty ℕ ::ᵢ
    (MultisetI ℕ → NRest Bool ECost) :=
  op_mset_is_empty_registration_itype
example : op_mset_insert ℕ ::ᵢ
    (ℕ → MultisetI ℕ → NRest (MultisetI ℕ) ECost) :=
  op_mset_insert_registration_itype
example : op_mset_delete ℕ ::ᵢ
    (ℕ → MultisetI ℕ → NRest (MultisetI ℕ) ECost) :=
  op_mset_delete_registration_itype
example : op_mset_plus ℕ ::ᵢ
    (MultisetI ℕ → MultisetI ℕ → NRest (MultisetI ℕ) ECost) :=
  op_mset_plus_registration_itype
example : op_mset_minus ℕ ::ᵢ
    (MultisetI ℕ → MultisetI ℕ → NRest (MultisetI ℕ) ECost) :=
  op_mset_minus_registration_itype
example : op_mset_contains ℕ ::ᵢ
    (ℕ → MultisetI ℕ → NRest Bool ECost) :=
  op_mset_contains_registration_itype
example : op_mset_count ℕ ::ᵢ
    (ℕ → MultisetI ℕ → NRest ℕ ECost) :=
  op_mset_count_registration_itype
example : op_mset_pick ℕ ::ᵢ
    (MultisetI ℕ → NRest (ℕ × MultisetI ℕ) ECost) :=
  op_mset_pick_registration_itype

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``op_mset_empty_fref, ``op_mset_is_empty_fref,
      ``op_mset_insert_fref, ``op_mset_delete_fref, ``op_mset_plus_fref,
      ``op_mset_minus_fref, ``op_mset_contains_fref, ``op_mset_count_fref,
      ``op_mset_pick_fref] do
    unless rules.contains n do
      throwError "multiset interface gate: missing parametricity rule {n}"

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.rel_mset_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rel_mset_sub

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_mset_count_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_mset_count_fref

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_mset_pick_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_mset_pick_fref

end Lax13Proofs.Refine.Sepref.Iicf
