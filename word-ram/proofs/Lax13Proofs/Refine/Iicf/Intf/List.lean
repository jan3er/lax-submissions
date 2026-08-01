import Lax13Proofs.Refine.Iicf.Intf.Set

/-!
# List interface

Source-faithful interface leaf for `IICF/Intf/IICF_List.thy` at
`isabelle_llvm_time` commit `42dd7f5`.  The existing `listRel` is reused;
this file supplies its IICF-facing results and the 22 cost-silent abstract
operations, without a concrete list representation.

## Source table

| Active source family | Lean accounting |
|---|---|
| `param_index` | `listRel_index` / `param_index` |
| `swap_param`, `swap_param_fref` | `swap_param`, `swap_param_fref` |
| `param_list_null` | `param_list_null` |
| 22 `sepref_decl_op list_*` declarations | 22 declarations below, with the same product inputs and preconditions |
| `def_pat_rules` block | explicit `op_list_*` declarations and registrations; no second term-pattern API |
| `list_rel_pres_neq_nil`, `list_rel_pres_length` | `listRel_pres_ne_nil`, `listRel_pres_length` |
| `list_rel_imp_same_length[sepref_bounds_dest]` | `listRel_pres_length` is the exported bounds fact; Lean has no `sepref_bounds_dest` database |
| `list_custom_empty` | no locale clone; concrete empty implementations register directly against `op_list_empty` |
| `gen_swap`, `gen_mop_list_swap`, `gen_op_list_swap` | semantic expansion `listSwap_eq_of_bounds` and monadic `gen_op_list_swap` |

The duplicated `hd` and `tl` source patterns are recorded by the single
corresponding Lean operation each; duplicating a registration would add no
semantic rule.  No operation beyond the active source family is introduced.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {α β : Type}

/-! ## Total source functions and list-relational support -/

/-- Total option-valued spelling of source `nth`; under the operation
precondition it contains exactly one element. -/
def listAt? : List α → ℕ → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listAt? xs n

/-- Source `list_update`, totalized out of bounds exactly as the list itself. -/
def listSet : List α → ℕ → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

def listButlast (xs : List α) : List α := xs.reverse.tail.reverse

def listRotate1 : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]

/-- Source list index: first related equality, or the list length. -/
noncomputable def listIndex (xs : List α) (a : α) : ℕ :=
  match xs with
  | [] => 0
  | x :: xs => if propBool (x = a) then 0 else listIndex xs a + 1

/-- Semantic source `swap`, with an irrelevant out-of-bounds fallback. -/
def listSwap (xs : List α) (i j : ℕ) : List α :=
  match listAt? xs i, listAt? xs j with
  | some xi, some xj => listSet (listSet xs i xj) j xi
  | _, _ => xs

theorem listRel_length {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) : xs.length = ys.length := h.length_eq

theorem listRel_pres_length {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) : xs.length = ys.length := h.length_eq

theorem listRel_pres_ne_nil {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) : (xs ≠ []) = (ys ≠ []) := by
  apply propext
  cases h <;> simp

theorem param_list_null {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) : (xs.isEmpty = true) = (ys.isEmpty = true) := by
  apply propext
  cases h <;> simp

theorem listRel_at {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) (i : ℕ) :
    (listAt? xs i, listAt? ys i) ∈ optionRel A := by
  change List.Forall₂ (fun x y => (x, y) ∈ A) xs ys at h
  induction h generalizing i with
  | nil => cases i <;> exact mem_optionRel_none_none
  | cons hxy htl ih =>
      cases i with
      | zero => exact mem_optionRel_some_some.mpr hxy
      | succ i => exact ih i

theorem listRel_set {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) {x : α} {y : β} (hxy : (x, y) ∈ A) (i : ℕ) :
    (listSet xs i x, listSet ys i y) ∈ listRel A := by
  change List.Forall₂ (fun x y => (x, y) ∈ A) xs ys at h
  induction h generalizing i with
  | nil => exact List.Forall₂.nil
  | cons hab htl ih =>
      cases i with
      | zero => exact List.Forall₂.cons hxy htl
      | succ i => exact List.Forall₂.cons hab (ih i)

theorem listRel_tail {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) : (xs.tail, ys.tail) ∈ listRel A := by
  cases h with
  | nil => exact List.Forall₂.nil
  | cons _ htl => exact htl

theorem listRel_butlast {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) : (listButlast xs, listButlast ys) ∈ listRel A := by
  exact List.rel_reverse (listRel_tail (List.rel_reverse h))

theorem listRel_rotate1 {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) : (listRotate1 xs, listRotate1 ys) ∈ listRel A := by
  cases h with
  | nil => exact List.Forall₂.nil
  | cons hxy htl => exact List.rel_append htl (List.Forall₂.cons hxy List.Forall₂.nil)

theorem listRel_replicate {A : Set (α × β)} {x : α} {y : β} (hxy : (x, y) ∈ A) :
    ∀ n, (List.replicate n x, List.replicate n y) ∈ listRel A
  | 0 => List.Forall₂.nil
  | n + 1 => List.Forall₂.cons hxy (listRel_replicate hxy n)

@[simp] theorem listSet_length (xs : List α) (i : ℕ) (x : α) :
    (listSet xs i x).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons a xs ih => cases i <;> simp [listSet, ih]

theorem related_eq {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A))
    {x a : α} {y b : β} (hxy : (x, y) ∈ A) (hab : (a, b) ∈ A) :
    (x = a) = (y = b) := by
  apply propext
  constructor
  · intro hxa
    subst a
    exact hA x y b hxy hab
  · intro hyb
    subst b
    exact hAc y x a hxy hab

theorem listRel_contains {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A))
    {x : α} {y : β} (hxy : (x, y) ∈ A) {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) : (x ∈ xs) = (y ∈ ys) := by
  change List.Forall₂ (fun x y => (x, y) ∈ A) xs ys at h
  induction h with
  | nil => simp
  | cons hab htl ih =>
      simp only [List.mem_cons]
      rw [related_eq hA hAc hxy hab, ih]

/-- Source `param_index`. -/
theorem listRel_index {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A))
    {xs : List α} {ys : List β} (h : (xs, ys) ∈ listRel A)
    {x : α} {y : β} (hxy : (x, y) ∈ A) : listIndex xs x = listIndex ys y := by
  change List.Forall₂ (fun x y => (x, y) ∈ A) xs ys at h
  induction h with
  | nil => rfl
  | cons hab htl ih =>
      simp only [listIndex]
      rw [propBool_congr (related_eq hA hAc hab hxy), ih]

theorem param_index {A : Set (α × β)}
    (hA : SingleValued A) (hAc : SingleValued (relConverse A)) :
    (listIndex, listIndex) ∈ listRel A →ᵣ A →ᵣ Set.diagonal ℕ := by
  intro xs ys h x y hxy
  exact listRel_index hA hAc h hxy

theorem listOption_obtain_left {A : Set (α × β)} {x : α} {o : Option β}
    (h : (some x, o) ∈ optionRel A) : ∃ y, o = some y ∧ (x, y) ∈ A := by
  cases o with
  | none => simp at h
  | some y => exact ⟨y, rfl, mem_optionRel_some_some.mp h⟩

theorem listAt?_some_of_lt {xs : List α} {i : ℕ} (h : i < xs.length) :
    ∃ x, listAt? xs i = some x := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
      cases i with
      | zero => exact ⟨x, rfl⟩
      | succ i => exact ih (Nat.lt_of_succ_lt_succ h)

/-- Source `swap_param`. -/
theorem swap_param {A : Set (α × β)} {xs : List α} {ys : List β}
    (h : (xs, ys) ∈ listRel A) {i j : ℕ}
    (hi : i < xs.length) (hj : j < xs.length) :
    (listSwap xs i j, listSwap ys i j) ∈ listRel A := by
  have hlen := h.length_eq
  have hi' : i < ys.length := by simpa [← hlen] using hi
  have hj' : j < ys.length := by simpa [← hlen] using hj
  have hai := listRel_at h i
  have haj := listRel_at h j
  cases hxi : listAt? xs i with
  | none =>
      obtain ⟨xi, hxi'⟩ := listAt?_some_of_lt hi
      rw [hxi] at hxi'
      contradiction
  | some xi =>
      cases hxj : listAt? xs j with
      | none =>
          obtain ⟨xj, hxj'⟩ := listAt?_some_of_lt hj
          rw [hxj] at hxj'
          contradiction
      | some xj =>
          obtain ⟨yi, hyi, hxiyi⟩ := listOption_obtain_left (by simpa [hxi] using hai)
          obtain ⟨yj, hyj, hxjyj⟩ := listOption_obtain_left (by simpa [hxj] using haj)
          simp [listSwap, hxi, hxj, hyi, hyj]
          exact listRel_set (listRel_set h hxjyj i) hxiyi j

/-- Source `swap_param_fref`, with its nested triple input. -/
theorem swap_param_fref (A : Set (α × β)) :
    (fun p : (List α × ℕ) × ℕ => listSwap p.1.1 p.1.2 p.2,
      fun p : (List β × ℕ) × ℕ => listSwap p.1.1 p.1.2 p.2) ∈
      fref (fun p => p.1.2 < p.1.1.length ∧ p.2 < p.1.1.length)
        ((listRel A ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => listRel A) := by
  rintro ⟨⟨xs, i⟩, j⟩ ⟨⟨ys, i'⟩, j'⟩ hq hpq
  obtain ⟨⟨hl, hiEq⟩, hjEq⟩ := hpq
  change i = i' at hiEq
  change j = j' at hjEq
  subst i'
  subst j'
  have hlen := hl.length_eq
  exact swap_param hl (by simpa [hlen] using hq.1) (by simpa [hlen] using hq.2)

/-! Option/spec helpers used by the bounded selectors. -/

theorem listOptionSpec_eq_returnT {o : Option α} {x : α} (h : o = some x) :
    NRest.spec (fun y => o = some y) (fun _ => (0 : ECost)) = NRest.returnT x := by
  subst o
  rw [NRest.spec, NRest.returnT, NRest.rest_inj_iff]
  funext y
  by_cases hy : y = x
  · subst y
    simp [NRest.single]
  · have hne : some x ≠ some y := fun h => hy (Option.some.inj h).symm
    simp [NRest.single, hy, hne]

theorem listSwap_eq_of_bounds (xs : List α) {i j : ℕ}
    (hi : i < xs.length) (hj : j < xs.length) :
    ∃ xi xj, listAt? xs i = some xi ∧ listAt? xs j = some xj ∧
      listSwap xs i j = listSet (listSet xs i xj) j xi := by
  obtain ⟨xi, hxi⟩ := listAt?_some_of_lt hi
  obtain ⟨xj, hxj⟩ := listAt?_some_of_lt hj
  exact ⟨xi, xj, hxi, hxj, by simp [listSwap, hxi, hxj]⟩

/-! ## Nominal interface and relation inference -/

sepref_decl_intf (α) ListI is List α

@[intf_of_rel] theorem listRel_intf (A : Set (α × β)) :
    intfOfRel (listRel A) (ListI β) := trivial

#guard_rel_interface (listRel (Set.diagonal ℕ)) is ListI ℕ

/-! ## Twenty-two source operations -/

sepref_decl_op list_empty (α : Type) : NRest (List α) ECost :=
    NRest.returnT []
  interface := ∀ α : Type, NRest (ListI α) ECost
  precondition := True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      (op_list_empty α, op_list_empty β) ∈ NRest.nrestRel (listRel A) := by
    intro β A
    exact NRest.param_returnT List.Forall₂.nil

sepref_decl_op list_is_empty (α : Type) : List α → NRest Bool ECost :=
    fun xs => NRest.returnT (propBool (xs = []))
  interface := ∀ α : Type, ListI α → NRest Bool ECost
  precondition := fun _ : List α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_is_empty α, op_list_is_empty β) ∈
        fref (fun _ : List β => True) (listRel A)
          (fun _ => NRest.nrestRel (Set.diagonal Bool))) := by
    intro β A xs ys _ h
    have he : (xs = []) = (ys = []) := by
      apply propext
      change List.Forall₂ (fun x y => (x, y) ∈ A) xs ys at h
      cases h <;> simp
    exact NRest.param_returnT (propBool_congr he)

sepref_decl_op list_replicate (α : Type) : ℕ → α → NRest (List α) ECost :=
    fun n x => NRest.returnT (List.replicate n x)
  interface := ∀ α : Type, ℕ → α → NRest (ListI α) ECost
  precondition := fun _ : ℕ => fun _ : α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_replicate α, op_list_replicate β) ∈
        fref (fun _ : ℕ => True) (Set.diagonal ℕ)
          (fun _ => A →ᵣ NRest.nrestRel (listRel A))) := by
    intro β A n m _ hnm x y hxy
    change n = m at hnm
    subst m
    exact NRest.param_returnT (listRel_replicate hxy n)

sepref_decl_op list_copy (α : Type) : List α → NRest (List α) ECost :=
    fun xs => NRest.returnT xs
  interface := ∀ α : Type, ListI α → NRest (ListI α) ECost
  precondition := fun _ : List α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_copy α, op_list_copy β) ∈
        fref (fun _ : List β => True) (listRel A)
          (fun _ => NRest.nrestRel (listRel A))) := by
    intro β A xs ys _ h
    exact NRest.param_returnT h

sepref_decl_op list_prepend (α : Type) : α → List α → NRest (List α) ECost :=
    fun x xs => NRest.returnT (x :: xs)
  interface := ∀ α : Type, α → ListI α → NRest (ListI α) ECost
  precondition := fun _ : α => fun _ : List α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_prepend α, op_list_prepend β) ∈
        fref (fun _ : β => True) A
          (fun _ => listRel A →ᵣ NRest.nrestRel (listRel A))) := by
    intro β A x y _ hxy xs ys h
    exact NRest.param_returnT (List.Forall₂.cons hxy h)

sepref_decl_op list_append (α : Type) : List α → α → NRest (List α) ECost :=
    fun xs x => NRest.returnT (xs ++ [x])
  interface := ∀ α : Type, ListI α → α → NRest (ListI α) ECost
  precondition := fun _ : List α => fun _ : α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_append α, op_list_append β) ∈
        fref (fun _ : List β => True) (listRel A)
          (fun _ => A →ᵣ NRest.nrestRel (listRel A))) := by
    intro β A xs ys _ h x y hxy
    exact NRest.param_returnT (List.rel_append h (List.Forall₂.cons hxy List.Forall₂.nil))

sepref_decl_op list_concat (α : Type) : List α → List α → NRest (List α) ECost :=
    fun xs ys => NRest.returnT (xs ++ ys)
  interface := ∀ α : Type, ListI α → ListI α → NRest (ListI α) ECost
  precondition := fun _ : List α => fun _ : List α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_concat α, op_list_concat β) ∈
        fref (fun _ : List β => True) (listRel A)
          (fun _ => listRel A →ᵣ NRest.nrestRel (listRel A))) := by
    intro β A xs xs' _ hx ys ys' hy
    exact NRest.param_returnT (List.rel_append hx hy)

sepref_decl_op list_take (α : Type) : (ℕ × List α) → NRest (List α) ECost :=
    fun p => NRest.bindT (NRest.assert (p.1 ≤ p.2.length)) fun _ =>
      NRest.returnT (p.2.take p.1)
  interface := ∀ α : Type, (ℕ × ListI α) → NRest (ListI α) ECost
  precondition := fun p : ℕ × List α => p.1 ≤ p.2.length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_take α, op_list_take β) ∈
        fref (fun p : ℕ × List β => p.1 ≤ p.2.length)
          (Set.diagonal ℕ ×ᵣ listRel A) (fun _ => NRest.nrestRel (listRel A))) := by
    rintro β A ⟨i, xs⟩ ⟨j, ys⟩ hq hpq
    obtain ⟨hij, hl⟩ := hpq
    change i = j at hij
    subst j
    have hp : i ≤ xs.length := by simpa [hl.length_eq] using hq
    simp only [op_list_take, NRest.assert_pos hp, NRest.assert_pos hq, NRest.returnT_bindT]
    exact NRest.param_returnT (List.forall₂_take i hl)

sepref_decl_op list_drop (α : Type) : (ℕ × List α) → NRest (List α) ECost :=
    fun p => NRest.bindT (NRest.assert (p.1 ≤ p.2.length)) fun _ =>
      NRest.returnT (p.2.drop p.1)
  interface := ∀ α : Type, (ℕ × ListI α) → NRest (ListI α) ECost
  precondition := fun p : ℕ × List α => p.1 ≤ p.2.length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_drop α, op_list_drop β) ∈
        fref (fun p : ℕ × List β => p.1 ≤ p.2.length)
          (Set.diagonal ℕ ×ᵣ listRel A) (fun _ => NRest.nrestRel (listRel A))) := by
    rintro β A ⟨i, xs⟩ ⟨j, ys⟩ hq hpq
    obtain ⟨hij, hl⟩ := hpq
    change i = j at hij
    subst j
    have hp : i ≤ xs.length := by simpa [hl.length_eq] using hq
    simp only [op_list_drop, NRest.assert_pos hp, NRest.assert_pos hq, NRest.returnT_bindT]
    exact NRest.param_returnT (List.forall₂_drop i hl)

sepref_decl_op list_length (α : Type) : List α → NRest ℕ ECost :=
    fun xs => NRest.returnT xs.length
  interface := ∀ α : Type, ListI α → NRest ℕ ECost
  precondition := fun _ : List α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_length α, op_list_length β) ∈
        fref (fun _ : List β => True) (listRel A)
          (fun _ => NRest.nrestRel (Set.diagonal ℕ))) := by
    intro β A xs ys _ h
    exact NRest.param_returnT h.length_eq

sepref_decl_op list_get (α : Type) : (List α × ℕ) → NRest α ECost :=
    fun p => NRest.bindT (NRest.assert (p.2 < p.1.length)) fun _ =>
      NRest.spec (fun x => listAt? p.1 p.2 = some x) (fun _ => 0)
  interface := ∀ α : Type, (ListI α × ℕ) → NRest α ECost
  precondition := fun p : List α × ℕ => p.2 < p.1.length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_get α, op_list_get β) ∈
        fref (fun p : List β × ℕ => p.2 < p.1.length)
          (listRel A ×ᵣ Set.diagonal ℕ) (fun _ => NRest.nrestRel A)) := by
    rintro β A ⟨xs, i⟩ ⟨ys, j⟩ hq hpq
    obtain ⟨hl, hij⟩ := hpq
    change i = j at hij
    subst j
    have hp : i < xs.length := by simpa [hl.length_eq] using hq
    obtain ⟨x, hx⟩ := listAt?_some_of_lt hp
    obtain ⟨y, hy, hxy⟩ := listOption_obtain_left (by simpa [hx] using listRel_at hl i)
    simp only [op_list_get, NRest.assert_pos hp, NRest.assert_pos hq, NRest.returnT_bindT]
    rw [listOptionSpec_eq_returnT hx, listOptionSpec_eq_returnT hy]
    exact NRest.param_returnT hxy

sepref_decl_op list_set (α : Type) : ((List α × ℕ) × α) → NRest (List α) ECost :=
    fun p => NRest.bindT (NRest.assert (p.1.2 < p.1.1.length)) fun _ =>
      NRest.returnT (listSet p.1.1 p.1.2 p.2)
  interface := ∀ α : Type, ((ListI α × ℕ) × α) → NRest (ListI α) ECost
  precondition := fun p : (List α × ℕ) × α => p.1.2 < p.1.1.length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_set α, op_list_set β) ∈
        fref (fun p : (List β × ℕ) × β => p.1.2 < p.1.1.length)
          ((listRel A ×ᵣ Set.diagonal ℕ) ×ᵣ A)
          (fun _ => NRest.nrestRel (listRel A))) := by
    rintro β A ⟨⟨xs, i⟩, x⟩ ⟨⟨ys, j⟩, y⟩ hq hpq
    obtain ⟨⟨hl, hij⟩, hxy⟩ := hpq
    change i = j at hij
    subst j
    have hp : i < xs.length := by simpa [hl.length_eq] using hq
    simp only [op_list_set, NRest.assert_pos hp, NRest.assert_pos hq, NRest.returnT_bindT]
    exact NRest.param_returnT (listRel_set hl hxy i)

sepref_decl_op list_hd (α : Type) : List α → NRest α ECost :=
    fun xs => NRest.bindT (NRest.assert (xs ≠ [])) fun _ =>
      NRest.spec (fun x => listAt? xs 0 = some x) (fun _ => 0)
  interface := ∀ α : Type, ListI α → NRest α ECost
  precondition := fun xs : List α => xs ≠ []
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_hd α, op_list_hd β) ∈
        fref (fun ys : List β => ys ≠ []) (listRel A) (fun _ => NRest.nrestRel A)) := by
    intro β A xs ys hys h
    have hxs : xs ≠ [] := (listRel_pres_ne_nil h).mpr hys
    have hxlen : 0 < xs.length := by cases xs <;> simp_all
    obtain ⟨x, hx⟩ := listAt?_some_of_lt hxlen
    obtain ⟨y, hy, hxy⟩ := listOption_obtain_left (by simpa [hx] using listRel_at h 0)
    simp only [op_list_hd, NRest.assert_pos hxs, NRest.assert_pos hys, NRest.returnT_bindT]
    rw [listOptionSpec_eq_returnT hx, listOptionSpec_eq_returnT hy]
    exact NRest.param_returnT hxy

sepref_decl_op list_tl (α : Type) : List α → NRest (List α) ECost :=
    fun xs => NRest.bindT (NRest.assert (xs ≠ [])) fun _ => NRest.returnT xs.tail
  interface := ∀ α : Type, ListI α → NRest (ListI α) ECost
  precondition := fun xs : List α => xs ≠ []
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_tl α, op_list_tl β) ∈
        fref (fun ys : List β => ys ≠ []) (listRel A)
          (fun _ => NRest.nrestRel (listRel A))) := by
    intro β A xs ys hys h
    have hxs : xs ≠ [] := (listRel_pres_ne_nil h).mpr hys
    simp only [op_list_tl, NRest.assert_pos hxs, NRest.assert_pos hys, NRest.returnT_bindT]
    exact NRest.param_returnT (listRel_tail h)

sepref_decl_op list_last (α : Type) : List α → NRest α ECost :=
    fun xs => NRest.bindT (NRest.assert (xs ≠ [])) fun _ =>
      NRest.spec (fun x => listAt? xs.reverse 0 = some x) (fun _ => 0)
  interface := ∀ α : Type, ListI α → NRest α ECost
  precondition := fun xs : List α => xs ≠ []
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_last α, op_list_last β) ∈
        fref (fun ys : List β => ys ≠ []) (listRel A) (fun _ => NRest.nrestRel A)) := by
    intro β A xs ys hys h
    have hxs : xs ≠ [] := (listRel_pres_ne_nil h).mpr hys
    have hr := List.rel_reverse h
    have hxlen : 0 < xs.reverse.length := by cases xs <;> simp_all
    obtain ⟨x, hx⟩ := listAt?_some_of_lt hxlen
    obtain ⟨y, hy, hxy⟩ := listOption_obtain_left (by simpa [hx] using listRel_at hr 0)
    simp only [op_list_last, NRest.assert_pos hxs, NRest.assert_pos hys, NRest.returnT_bindT]
    rw [listOptionSpec_eq_returnT hx, listOptionSpec_eq_returnT hy]
    exact NRest.param_returnT hxy

sepref_decl_op list_butlast (α : Type) : List α → NRest (List α) ECost :=
    fun xs => NRest.bindT (NRest.assert (xs ≠ [])) fun _ => NRest.returnT (listButlast xs)
  interface := ∀ α : Type, ListI α → NRest (ListI α) ECost
  precondition := fun xs : List α => xs ≠ []
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_butlast α, op_list_butlast β) ∈
        fref (fun ys : List β => ys ≠ []) (listRel A)
          (fun _ => NRest.nrestRel (listRel A))) := by
    intro β A xs ys hys h
    have hxs : xs ≠ [] := (listRel_pres_ne_nil h).mpr hys
    simp only [op_list_butlast, NRest.assert_pos hxs, NRest.assert_pos hys,
      NRest.returnT_bindT]
    exact NRest.param_returnT (listRel_butlast h)

sepref_decl_op list_pop_last (α : Type) : List α → NRest (α × List α) ECost :=
    fun xs => NRest.bindT (NRest.assert (xs ≠ [])) fun _ =>
      NRest.bindT (NRest.spec (fun x => listAt? xs.reverse 0 = some x) (fun _ => 0)) fun x =>
        NRest.returnT (x, listButlast xs)
  interface := ∀ α : Type, ListI α → NRest (α × ListI α) ECost
  precondition := fun xs : List α => xs ≠ []
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_pop_last α, op_list_pop_last β) ∈
        fref (fun ys : List β => ys ≠ []) (listRel A)
          (fun _ => NRest.nrestRel (A ×ᵣ listRel A))) := by
    intro β A xs ys hys h
    have hxs : xs ≠ [] := (listRel_pres_ne_nil h).mpr hys
    have hr := List.rel_reverse h
    have hxlen : 0 < xs.reverse.length := by cases xs <;> simp_all
    obtain ⟨x, hx⟩ := listAt?_some_of_lt hxlen
    obtain ⟨y, hy, hxy⟩ := listOption_obtain_left (by simpa [hx] using listRel_at hr 0)
    simp only [op_list_pop_last, NRest.assert_pos hxs, NRest.assert_pos hys,
      NRest.returnT_bindT]
    rw [listOptionSpec_eq_returnT hx, listOptionSpec_eq_returnT hy]
    simp only [NRest.returnT_bindT]
    exact NRest.param_returnT (γ := ECost)
      (show ((x, listButlast xs), (y, listButlast ys)) ∈ A ×ᵣ listRel A from
        ⟨hxy, listRel_butlast h⟩)

sepref_decl_op list_contains (α : Type) : α → List α → NRest Bool ECost :=
    fun x xs => NRest.returnT (propBool (x ∈ xs))
  interface := ∀ α : Type, α → ListI α → NRest Bool ECost
  precondition := fun _ : α => fun _ : List α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      SingleValued A → SingleValued (relConverse A) →
      ((op_list_contains α, op_list_contains β) ∈
        fref (fun _ : β => True) A
          (fun _ => listRel A →ᵣ NRest.nrestRel (Set.diagonal Bool))) := by
    intro β A hA hAc x y _ hxy xs ys h
    exact NRest.param_returnT (propBool_congr (listRel_contains hA hAc hxy h))

sepref_decl_op list_swap (α : Type) : ((List α × ℕ) × ℕ) → NRest (List α) ECost :=
    fun p => NRest.bindT
      (NRest.assert (p.1.2 < p.1.1.length ∧ p.2 < p.1.1.length)) fun _ =>
        NRest.returnT (listSwap p.1.1 p.1.2 p.2)
  interface := ∀ α : Type, ((ListI α × ℕ) × ℕ) → NRest (ListI α) ECost
  precondition := fun p : (List α × ℕ) × ℕ =>
    p.1.2 < p.1.1.length ∧ p.2 < p.1.1.length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_swap α, op_list_swap β) ∈
        fref (fun p : (List β × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧ p.2 < p.1.1.length)
          ((listRel A ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
          (fun _ => NRest.nrestRel (listRel A))) := by
    rintro β A ⟨⟨xs, i⟩, j⟩ ⟨⟨ys, i'⟩, j'⟩ hq hpq
    obtain ⟨⟨hl, hiEq⟩, hjEq⟩ := hpq
    change i = i' at hiEq
    change j = j' at hjEq
    subst i'
    subst j'
    have hp : i < xs.length ∧ j < xs.length := by
      simpa [hl.length_eq] using hq
    simp only [op_list_swap, NRest.assert_pos hp, NRest.assert_pos hq, NRest.returnT_bindT]
    exact NRest.param_returnT (swap_param hl hp.1 hp.2)

sepref_decl_op list_rotate1 (α : Type) : List α → NRest (List α) ECost :=
    fun xs => NRest.returnT (listRotate1 xs)
  interface := ∀ α : Type, ListI α → NRest (ListI α) ECost
  precondition := fun _ : List α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_rotate1 α, op_list_rotate1 β) ∈
        fref (fun _ : List β => True) (listRel A)
          (fun _ => NRest.nrestRel (listRel A))) := by
    intro β A xs ys _ h
    exact NRest.param_returnT (listRel_rotate1 h)

sepref_decl_op list_rev (α : Type) : List α → NRest (List α) ECost :=
    fun xs => NRest.returnT xs.reverse
  interface := ∀ α : Type, ListI α → NRest (ListI α) ECost
  precondition := fun _ : List α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_rev α, op_list_rev β) ∈
        fref (fun _ : List β => True) (listRel A)
          (fun _ => NRest.nrestRel (listRel A))) := by
    intro β A xs ys _ h
    exact NRest.param_returnT (List.rel_reverse h)

sepref_decl_op list_index (α : Type) : List α → α → NRest ℕ ECost :=
    fun xs x => NRest.returnT (listIndex xs x)
  interface := ∀ α : Type, ListI α → α → NRest ℕ ECost
  precondition := fun _ : List α => fun _ : α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      SingleValued A → SingleValued (relConverse A) →
      ((op_list_index α, op_list_index β) ∈
        fref (fun _ : List β => True) (listRel A)
          (fun _ => A →ᵣ NRest.nrestRel (Set.diagonal ℕ))) := by
    intro β A hA hAc xs ys _ h x y hxy
    exact NRest.param_returnT (listRel_index hA hAc h hxy)

/-! ## Semantic generic swap expansion -/

theorem gen_op_list_swap (xs : List α) (i j : ℕ)
    (hi : i < xs.length) (hj : j < xs.length) :
    op_list_swap α ((xs, i), j) =
      NRest.bindT (op_list_get α (xs, i)) fun xi =>
      NRest.bindT (op_list_get α (xs, j)) fun xj =>
      NRest.bindT (op_list_set α ((xs, i), xj)) fun xs' =>
      NRest.bindT (op_list_set α ((xs', j), xi)) fun xs'' =>
      NRest.returnT xs'' := by
  obtain ⟨xi, hxi⟩ := listAt?_some_of_lt hi
  obtain ⟨xj, hxj⟩ := listAt?_some_of_lt hj
  have hswap : i < xs.length ∧ j < xs.length := ⟨hi, hj⟩
  have hsj : j < (listSet xs i xj).length := by simpa using hj
  simp only [op_list_swap, op_list_get, op_list_set, NRest.assert_pos hswap,
    NRest.assert_pos hi, NRest.assert_pos hj, NRest.returnT_bindT]
  rw [listOptionSpec_eq_returnT hxi, listOptionSpec_eq_returnT hxj]
  simp only [NRest.returnT_bindT, NRest.assert_pos hsj]
  simp [listSwap, hxi, hxj]

/-! ## Source-shaped diagonal, registration, and database gates -/

private theorem diagonal_converse_singleValued_list :
    SingleValued (relConverse (Set.diagonal ℕ)) := by
  rintro b a a' hba hba'
  change a = b at hba
  change a' = b at hba'
  exact hba.trans hba'.symm

private example :
    (op_list_empty ℕ, op_list_empty ℕ) ∈
      NRest.nrestRel (listRel (Set.diagonal ℕ)) :=
  op_list_empty_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_is_empty ℕ, op_list_is_empty ℕ) ∈
      fref (fun _ : List ℕ => True) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) :=
  op_list_is_empty_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_replicate ℕ, op_list_replicate ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => Set.diagonal ℕ →ᵣ NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_replicate_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_copy ℕ, op_list_copy ℕ) ∈
      fref (fun _ : List ℕ => True) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_copy_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_prepend ℕ, op_list_prepend ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => listRel (Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_prepend_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_append ℕ, op_list_append ℕ) ∈
      fref (fun _ : List ℕ => True) (listRel (Set.diagonal ℕ))
        (fun _ => Set.diagonal ℕ →ᵣ NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_append_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_concat ℕ, op_list_concat ℕ) ∈
      fref (fun _ : List ℕ => True) (listRel (Set.diagonal ℕ))
        (fun _ => listRel (Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_concat_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_take ℕ, op_list_take ℕ) ∈
      fref (fun p : ℕ × List ℕ => p.1 ≤ p.2.length)
        (Set.diagonal ℕ ×ᵣ listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_take_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_drop ℕ, op_list_drop ℕ) ∈
      fref (fun p : ℕ × List ℕ => p.1 ≤ p.2.length)
        (Set.diagonal ℕ ×ᵣ listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_drop_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_length ℕ, op_list_length ℕ) ∈
      fref (fun _ : List ℕ => True) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) :=
  op_list_length_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_get ℕ, op_list_get ℕ) ∈
      fref (fun p : List ℕ × ℕ => p.2 < p.1.length)
        (listRel (Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) :=
  op_list_get_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_set ℕ, op_list_set ℕ) ∈
      fref (fun p : (List ℕ × ℕ) × ℕ => p.1.2 < p.1.1.length)
        ((listRel (Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_set_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_hd ℕ, op_list_hd ℕ) ∈
      fref (fun xs : List ℕ => xs ≠ []) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) :=
  op_list_hd_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_tl ℕ, op_list_tl ℕ) ∈
      fref (fun xs : List ℕ => xs ≠ []) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_tl_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_last ℕ, op_list_last ℕ) ∈
      fref (fun xs : List ℕ => xs ≠ []) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) :=
  op_list_last_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_butlast ℕ, op_list_butlast ℕ) ∈
      fref (fun xs : List ℕ => xs ≠ []) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_butlast_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_pop_last ℕ, op_list_pop_last ℕ) ∈
      fref (fun xs : List ℕ => xs ≠ []) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel
          (Set.diagonal ℕ ×ᵣ listRel (Set.diagonal ℕ))) :=
  op_list_pop_last_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_contains ℕ, op_list_contains ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => listRel (Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (Set.diagonal Bool)) :=
  op_list_contains_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued_list

private example :
    (op_list_swap ℕ, op_list_swap ℕ) ∈
      fref (fun p : (List ℕ × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧ p.2 < p.1.1.length)
        ((listRel (Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_swap_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_rotate1 ℕ, op_list_rotate1 ℕ) ∈
      fref (fun _ : List ℕ => True) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_rotate1_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_rev ℕ, op_list_rev ℕ) ∈
      fref (fun _ : List ℕ => True) (listRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (listRel (Set.diagonal ℕ))) :=
  op_list_rev_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_index ℕ, op_list_index ℕ) ∈
      fref (fun _ : List ℕ => True) (listRel (Set.diagonal ℕ))
        (fun _ => Set.diagonal ℕ →ᵣ NRest.nrestRel (Set.diagonal ℕ)) :=
  op_list_index_fref ℕ (Set.diagonal ℕ) singleValued_diagonal
    diagonal_converse_singleValued_list

example : op_list_empty ℕ ::ᵢ NRest (ListI ℕ) ECost :=
  op_list_empty_registration_itype
example : op_list_is_empty ℕ ::ᵢ (ListI ℕ → NRest Bool ECost) :=
  op_list_is_empty_registration_itype
example : op_list_replicate ℕ ::ᵢ (ℕ → ℕ → NRest (ListI ℕ) ECost) :=
  op_list_replicate_registration_itype
example : op_list_copy ℕ ::ᵢ (ListI ℕ → NRest (ListI ℕ) ECost) :=
  op_list_copy_registration_itype
example : op_list_prepend ℕ ::ᵢ (ℕ → ListI ℕ → NRest (ListI ℕ) ECost) :=
  op_list_prepend_registration_itype
example : op_list_append ℕ ::ᵢ (ListI ℕ → ℕ → NRest (ListI ℕ) ECost) :=
  op_list_append_registration_itype
example : op_list_concat ℕ ::ᵢ
    (ListI ℕ → ListI ℕ → NRest (ListI ℕ) ECost) :=
  op_list_concat_registration_itype
example : op_list_take ℕ ::ᵢ ((ℕ × ListI ℕ) → NRest (ListI ℕ) ECost) :=
  op_list_take_registration_itype
example : op_list_drop ℕ ::ᵢ ((ℕ × ListI ℕ) → NRest (ListI ℕ) ECost) :=
  op_list_drop_registration_itype
example : op_list_length ℕ ::ᵢ (ListI ℕ → NRest ℕ ECost) :=
  op_list_length_registration_itype
example : op_list_get ℕ ::ᵢ ((ListI ℕ × ℕ) → NRest ℕ ECost) :=
  op_list_get_registration_itype
example : op_list_set ℕ ::ᵢ
    (((ListI ℕ × ℕ) × ℕ) → NRest (ListI ℕ) ECost) :=
  op_list_set_registration_itype
example : op_list_hd ℕ ::ᵢ (ListI ℕ → NRest ℕ ECost) :=
  op_list_hd_registration_itype
example : op_list_tl ℕ ::ᵢ (ListI ℕ → NRest (ListI ℕ) ECost) :=
  op_list_tl_registration_itype
example : op_list_last ℕ ::ᵢ (ListI ℕ → NRest ℕ ECost) :=
  op_list_last_registration_itype
example : op_list_butlast ℕ ::ᵢ (ListI ℕ → NRest (ListI ℕ) ECost) :=
  op_list_butlast_registration_itype
example : op_list_pop_last ℕ ::ᵢ (ListI ℕ → NRest (ℕ × ListI ℕ) ECost) :=
  op_list_pop_last_registration_itype
example : op_list_contains ℕ ::ᵢ (ℕ → ListI ℕ → NRest Bool ECost) :=
  op_list_contains_registration_itype
example : op_list_swap ℕ ::ᵢ
    (((ListI ℕ × ℕ) × ℕ) → NRest (ListI ℕ) ECost) :=
  op_list_swap_registration_itype
example : op_list_rotate1 ℕ ::ᵢ (ListI ℕ → NRest (ListI ℕ) ECost) :=
  op_list_rotate1_registration_itype
example : op_list_rev ℕ ::ᵢ (ListI ℕ → NRest (ListI ℕ) ECost) :=
  op_list_rev_registration_itype
example : op_list_index ℕ ::ᵢ (ListI ℕ → ℕ → NRest ℕ ECost) :=
  op_list_index_registration_itype

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``op_list_empty_fref, ``op_list_is_empty_fref,
      ``op_list_replicate_fref, ``op_list_copy_fref, ``op_list_prepend_fref,
      ``op_list_append_fref, ``op_list_concat_fref, ``op_list_take_fref,
      ``op_list_drop_fref, ``op_list_length_fref, ``op_list_get_fref,
      ``op_list_set_fref, ``op_list_hd_fref, ``op_list_tl_fref,
      ``op_list_last_fref, ``op_list_butlast_fref, ``op_list_pop_last_fref,
      ``op_list_contains_fref, ``op_list_swap_fref, ``op_list_rotate1_fref,
      ``op_list_rev_fref, ``op_list_index_fref] do
    unless rules.contains n do
      throwError "list interface gate: missing parametricity rule {n}"

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.listRel_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms listRel_index

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.swap_param' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms swap_param

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_list_pop_last_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_list_pop_last_fref

end Lax13Proofs.Refine.Sepref.Iicf
