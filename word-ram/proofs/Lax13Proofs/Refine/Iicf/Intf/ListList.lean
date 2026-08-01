import Lax13Proofs.Refine.Iicf.Intf.List

/-!
# List-of-lists interface

Source-faithful interface leaf for `IICF/Intf/IICF_List_List.thy` at
`isabelle_llvm_time` commit `42dd7f5`.  The source abbreviates its relation
as `list_rel (list_rel A)` and explicitly leaves a proper subtype interface
as a TODO.  Lean's interface normalizer cannot nest `ListI` (it normalizes
`ListI (ListI α)` only to `List (ListI α)`), so the smallest usable faithful
encoding is one nominal `ListListI α` for the unchanged semantic type
`List (List α)`; no separate operations or representation are introduced.

## Source table

| Active source family | Lean accounting |
|---|---|
| 8 operations `lempty`, `push_back`, `pop_back`, `upd`, `idx`, `llen`, `len`, `take` | the eight `sepref_decl_op list_list_*` declarations below |
| Nested relation abbreviation `LR A` | `listRel (listRel A)` directly |
| Six `fold_op_list_list_*` lemmas | six cost-silent semantic fold equalities below |
| `list_list_custom_empty` | concrete empty implementations register directly against `op_list_list_lempty`; no locale clone |

The total helper `listListAt` agrees with source `(!)` whenever the explicit
outer-index precondition holds; its empty fallback is unreachable there.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {α β : Type}

/-! ## Nested-list support -/

/-- Total spelling of outer-list selection.  The source preconditions make
the empty fallback irrelevant. -/
def listListAt (xss : List (List α)) (i : ℕ) : List α :=
  match listAt? xss i with
  | some xs => xs
  | none => []

theorem listListAt_rel {A : Set (α × β)} {xss : List (List α)}
    {yss : List (List β)} (h : (xss, yss) ∈ listRel (listRel A)) (i : ℕ) :
    (listListAt xss i, listListAt yss i) ∈ listRel A := by
  have ho := listRel_at h i
  cases hx : listAt? xss i with
  | none =>
      cases hy : listAt? yss i with
      | none => simp [listListAt, hx, hy]
      | some ys => simp [hx, hy] at ho
  | some xs =>
      cases hy : listAt? yss i with
      | none => simp [hx, hy] at ho
      | some ys => simpa [listListAt, hx, hy] using ho

theorem listListAt_length {A : Set (α × β)} {xss : List (List α)}
    {yss : List (List β)} (h : (xss, yss) ∈ listRel (listRel A)) (i : ℕ) :
    (listListAt xss i).length = (listListAt yss i).length :=
  (listListAt_rel h i).length_eq

theorem listListAt_ne_nil {A : Set (α × β)} {xss : List (List α)}
    {yss : List (List β)} (h : (xss, yss) ∈ listRel (listRel A)) (i : ℕ) :
    (listListAt xss i ≠ []) = (listListAt yss i ≠ []) :=
  listRel_pres_ne_nil (listListAt_rel h i)

/-! The source notes that a dedicated subtype interface is future work.
This nominal interface is required only because the current normalizer does
not recursively expand `ListI`; its semantics and relation stay exactly the
source's nested lists. -/

sepref_decl_intf (α) ListListI is List (List α)

attribute [-intf_of_rel] listRel_intf

@[intf_of_rel] theorem listListRel_intf (A : Set (α × β)) :
    intfOfRel (listRel (listRel A)) (ListListI β) := trivial

attribute [intf_of_rel] listRel_intf

#guard_rel_interface (listRel (listRel (Set.diagonal ℕ))) is ListListI ℕ

/-! ## Eight source operations -/

sepref_decl_op list_list_lempty (α : Type) : ℕ → NRest (List (List α)) ECost :=
    fun n => NRest.returnT (List.replicate n [])
  interface := ∀ α : Type, ℕ → NRest (ListListI α) ECost
  precondition := fun _ : ℕ => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_list_lempty α, op_list_list_lempty β) ∈
        fref (fun _ : ℕ => True) (Set.diagonal ℕ)
          (fun _ => NRest.nrestRel (listRel (listRel A)))) := by
    intro β A n m _ hnm
    change n = m at hnm
    subst m
    exact NRest.param_returnT (listRel_replicate List.Forall₂.nil n)

sepref_decl_op list_list_push_back (α : Type) :
    ((List (List α) × ℕ) × α) → NRest (List (List α)) ECost :=
    fun p => NRest.bindT (NRest.assert (p.1.2 < p.1.1.length)) fun _ =>
      NRest.returnT (listSet p.1.1 p.1.2 (listListAt p.1.1 p.1.2 ++ [p.2]))
  interface := ∀ α : Type,
    ((ListListI α × ℕ) × α) → NRest (ListListI α) ECost
  precondition := fun p : (List (List α) × ℕ) × α => p.1.2 < p.1.1.length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_list_push_back α, op_list_list_push_back β) ∈
        fref (fun p : (List (List β) × ℕ) × β => p.1.2 < p.1.1.length)
          ((listRel (listRel A) ×ᵣ Set.diagonal ℕ) ×ᵣ A)
          (fun _ => NRest.nrestRel (listRel (listRel A)))) := by
    rintro β A ⟨⟨xss, i⟩, x⟩ ⟨⟨yss, j⟩, y⟩ hq hpq
    obtain ⟨⟨hxy, hij⟩, hxyElem⟩ := hpq
    change i = j at hij
    subst j
    have hp : i < xss.length := by simpa [hxy.length_eq] using hq
    have hinner := listListAt_rel hxy i
    have happ := List.rel_append hinner (List.Forall₂.cons hxyElem List.Forall₂.nil)
    simp only [op_list_list_push_back, NRest.assert_pos hp, NRest.assert_pos hq,
      NRest.returnT_bindT]
    exact NRest.param_returnT (listRel_set hxy happ i)

sepref_decl_op list_list_pop_back (α : Type) :
    (List (List α) × ℕ) → NRest (α × List (List α)) ECost :=
    fun p => NRest.bindT
      (NRest.assert (p.2 < p.1.length ∧ listListAt p.1 p.2 ≠ [])) fun _ =>
        NRest.bindT
          (NRest.spec
            (fun x => listAt? (listListAt p.1 p.2).reverse 0 = some x)
            (fun _ => 0)) fun x =>
          NRest.returnT
            (x, listSet p.1 p.2 (listButlast (listListAt p.1 p.2)))
  interface := ∀ α : Type,
    (ListListI α × ℕ) → NRest (α × ListListI α) ECost
  precondition := fun p : List (List α) × ℕ =>
    p.2 < p.1.length ∧ listListAt p.1 p.2 ≠ []
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_list_pop_back α, op_list_list_pop_back β) ∈
        fref (fun p : List (List β) × ℕ =>
          p.2 < p.1.length ∧ listListAt p.1 p.2 ≠ [])
          (listRel (listRel A) ×ᵣ Set.diagonal ℕ)
          (fun _ => NRest.nrestRel (A ×ᵣ listRel (listRel A)))) := by
    rintro β A ⟨xss, i⟩ ⟨yss, j⟩ hq hpq
    obtain ⟨hxy, hij⟩ := hpq
    change i = j at hij
    subst j
    have hinner := listListAt_rel hxy i
    have hp : i < xss.length ∧ listListAt xss i ≠ [] := by
      exact ⟨by simpa [hxy.length_eq] using hq.1,
        (listListAt_ne_nil hxy i).mpr hq.2⟩
    have hr := List.rel_reverse hinner
    have hxlen : 0 < (listListAt xss i).reverse.length := by
      cases hxi : listListAt xss i <;> simp_all
    obtain ⟨x, hx⟩ := listAt?_some_of_lt hxlen
    obtain ⟨y, hy, hrel⟩ := listOption_obtain_left
      (by simpa [hx] using listRel_at hr 0)
    simp only [op_list_list_pop_back, NRest.assert_pos hp, NRest.assert_pos hq,
      NRest.returnT_bindT]
    rw [listOptionSpec_eq_returnT hx, listOptionSpec_eq_returnT hy]
    simp only [NRest.returnT_bindT]
    exact NRest.param_returnT (γ := ECost)
      (show ((x, listSet xss i (listButlast (listListAt xss i))),
          (y, listSet yss i (listButlast (listListAt yss i)))) ∈
          A ×ᵣ listRel (listRel A) from
        ⟨hrel, listRel_set hxy (listRel_butlast hinner) i⟩)

sepref_decl_op list_list_upd (α : Type) :
    (((List (List α) × ℕ) × ℕ) × α) → NRest (List (List α)) ECost :=
    fun p => NRest.bindT
      (NRest.assert (p.1.1.2 < p.1.1.1.length ∧
        p.1.2 < (listListAt p.1.1.1 p.1.1.2).length)) fun _ =>
      NRest.returnT (listSet p.1.1.1 p.1.1.2
        (listSet (listListAt p.1.1.1 p.1.1.2) p.1.2 p.2))
  interface := ∀ α : Type,
    (((ListListI α × ℕ) × ℕ) × α) → NRest (ListListI α) ECost
  precondition := fun p : ((List (List α) × ℕ) × ℕ) × α =>
    p.1.1.2 < p.1.1.1.length ∧
      p.1.2 < (listListAt p.1.1.1 p.1.1.2).length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_list_upd α, op_list_list_upd β) ∈
        fref (fun p : ((List (List β) × ℕ) × ℕ) × β =>
          p.1.1.2 < p.1.1.1.length ∧
            p.1.2 < (listListAt p.1.1.1 p.1.1.2).length)
          (((listRel (listRel A) ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ) ×ᵣ A)
          (fun _ => NRest.nrestRel (listRel (listRel A)))) := by
    rintro β A ⟨⟨⟨xss, i⟩, k⟩, x⟩ ⟨⟨⟨yss, j⟩, l⟩, y⟩ hq hpq
    obtain ⟨⟨⟨hxy, hij⟩, hkl⟩, hElem⟩ := hpq
    change i = j at hij
    change k = l at hkl
    subst j
    subst l
    have hinner := listListAt_rel hxy i
    have hp : i < xss.length ∧ k < (listListAt xss i).length :=
      ⟨by simpa [hxy.length_eq] using hq.1,
        by simpa [hinner.length_eq] using hq.2⟩
    simp only [op_list_list_upd, NRest.assert_pos hp, NRest.assert_pos hq,
      NRest.returnT_bindT]
    exact NRest.param_returnT
      (listRel_set hxy (listRel_set hinner hElem k) i)

sepref_decl_op list_list_idx (α : Type) :
    ((List (List α) × ℕ) × ℕ) → NRest α ECost :=
    fun p => NRest.bindT
      (NRest.assert (p.1.2 < p.1.1.length ∧
        p.2 < (listListAt p.1.1 p.1.2).length)) fun _ =>
      NRest.spec
        (fun x => listAt? (listListAt p.1.1 p.1.2) p.2 = some x)
        (fun _ => 0)
  interface := ∀ α : Type,
    ((ListListI α × ℕ) × ℕ) → NRest α ECost
  precondition := fun p : (List (List α) × ℕ) × ℕ =>
    p.1.2 < p.1.1.length ∧ p.2 < (listListAt p.1.1 p.1.2).length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_list_idx α, op_list_list_idx β) ∈
        fref (fun p : (List (List β) × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧ p.2 < (listListAt p.1.1 p.1.2).length)
          ((listRel (listRel A) ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
          (fun _ => NRest.nrestRel A)) := by
    rintro β A ⟨⟨xss, i⟩, k⟩ ⟨⟨yss, j⟩, l⟩ hq hpq
    obtain ⟨⟨hxy, hij⟩, hkl⟩ := hpq
    change i = j at hij
    change k = l at hkl
    subst j
    subst l
    have hinner := listListAt_rel hxy i
    have hp : i < xss.length ∧ k < (listListAt xss i).length :=
      ⟨by simpa [hxy.length_eq] using hq.1,
        by simpa [hinner.length_eq] using hq.2⟩
    obtain ⟨x, hx⟩ := listAt?_some_of_lt hp.2
    obtain ⟨y, hy, hrel⟩ := listOption_obtain_left
      (by simpa [hx] using listRel_at hinner k)
    simp only [op_list_list_idx, NRest.assert_pos hp, NRest.assert_pos hq,
      NRest.returnT_bindT]
    rw [listOptionSpec_eq_returnT hx, listOptionSpec_eq_returnT hy]
    exact NRest.param_returnT hrel

sepref_decl_op list_list_llen (α : Type) :
    (List (List α) × ℕ) → NRest ℕ ECost :=
    fun p => NRest.bindT (NRest.assert (p.2 < p.1.length)) fun _ =>
      NRest.returnT (listListAt p.1 p.2).length
  interface := ∀ α : Type, (ListListI α × ℕ) → NRest ℕ ECost
  precondition := fun p : List (List α) × ℕ => p.2 < p.1.length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_list_llen α, op_list_list_llen β) ∈
        fref (fun p : List (List β) × ℕ => p.2 < p.1.length)
          (listRel (listRel A) ×ᵣ Set.diagonal ℕ)
          (fun _ => NRest.nrestRel (Set.diagonal ℕ))) := by
    rintro β A ⟨xss, i⟩ ⟨yss, j⟩ hq hpq
    obtain ⟨hxy, hij⟩ := hpq
    change i = j at hij
    subst j
    have hp : i < xss.length := by simpa [hxy.length_eq] using hq
    simp only [op_list_list_llen, NRest.assert_pos hp, NRest.assert_pos hq,
      NRest.returnT_bindT]
    exact NRest.param_returnT (listListAt_length hxy i)

sepref_decl_op list_list_len (α : Type) : List (List α) → NRest ℕ ECost :=
    fun xss => NRest.returnT xss.length
  interface := ∀ α : Type, ListListI α → NRest ℕ ECost
  precondition := fun _ : List (List α) => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_list_len α, op_list_list_len β) ∈
        fref (fun _ : List (List β) => True) (listRel (listRel A))
          (fun _ => NRest.nrestRel (Set.diagonal ℕ))) := by
    intro β A xss yss _ h
    exact NRest.param_returnT h.length_eq

sepref_decl_op list_list_take (α : Type) :
    ((List (List α) × ℕ) × ℕ) → NRest (List (List α)) ECost :=
    fun p => NRest.bindT
      (NRest.assert (p.1.2 < p.1.1.length ∧
        p.2 ≤ (listListAt p.1.1 p.1.2).length)) fun _ =>
      NRest.returnT (listSet p.1.1 p.1.2
        ((listListAt p.1.1 p.1.2).take p.2))
  interface := ∀ α : Type,
    ((ListListI α × ℕ) × ℕ) → NRest (ListListI α) ECost
  precondition := fun p : (List (List α) × ℕ) × ℕ =>
    p.1.2 < p.1.1.length ∧ p.2 ≤ (listListAt p.1.1 p.1.2).length
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_list_list_take α, op_list_list_take β) ∈
        fref (fun p : (List (List β) × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧ p.2 ≤ (listListAt p.1.1 p.1.2).length)
          ((listRel (listRel A) ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
          (fun _ => NRest.nrestRel (listRel (listRel A)))) := by
    rintro β A ⟨⟨xss, i⟩, n⟩ ⟨⟨yss, j⟩, m⟩ hq hpq
    obtain ⟨⟨hxy, hij⟩, hnm⟩ := hpq
    change i = j at hij
    change n = m at hnm
    subst j
    subst m
    have hinner := listListAt_rel hxy i
    have hp : i < xss.length ∧ n ≤ (listListAt xss i).length :=
      ⟨by simpa [hxy.length_eq] using hq.1,
        by simpa [hinner.length_eq] using hq.2⟩
    simp only [op_list_list_take, NRest.assert_pos hp, NRest.assert_pos hq,
      NRest.returnT_bindT]
    exact NRest.param_returnT
      (listRel_set hxy (List.forall₂_take n hinner) i)

/-! ## Six source fold lemmas -/

theorem fold_op_list_list_push_back (xss : List (List α)) (i : ℕ) (x : α)
    (hi : i < xss.length) :
    op_list_list_push_back α ((xss, i), x) =
      NRest.returnT (listSet xss i (listListAt xss i ++ [x])) := by
  simp [op_list_list_push_back, hi]

theorem fold_op_list_list_pop_back (xss : List (List α)) (i : ℕ)
    (hpre : i < xss.length ∧ listListAt xss i ≠ []) :
    op_list_list_pop_back α (xss, i) =
      NRest.bindT
        (NRest.spec
          (fun x => listAt? (listListAt xss i).reverse 0 = some x)
          (fun _ => 0)) fun x =>
        NRest.returnT (x, listSet xss i (listButlast (listListAt xss i))) := by
  simp [op_list_list_pop_back, hpre]

theorem fold_op_list_list_upd (xss : List (List α)) (i j : ℕ) (x : α)
    (hpre : i < xss.length ∧ j < (listListAt xss i).length) :
    op_list_list_upd α (((xss, i), j), x) =
      NRest.returnT (listSet xss i (listSet (listListAt xss i) j x)) := by
  simp [op_list_list_upd, hpre]

theorem fold_op_list_list_idx (xss : List (List α)) (i j : ℕ)
    (hpre : i < xss.length ∧ j < (listListAt xss i).length) :
    op_list_list_idx α ((xss, i), j) =
      NRest.spec (fun x => listAt? (listListAt xss i) j = some x) (fun _ => 0) := by
  simp [op_list_list_idx, hpre]

theorem fold_op_list_list_llen (xss : List (List α)) (i : ℕ)
    (hi : i < xss.length) :
    op_list_list_llen α (xss, i) = NRest.returnT (listListAt xss i).length := by
  simp [op_list_list_llen, hi]

theorem fold_op_list_list_take (xss : List (List α)) (i n : ℕ)
    (hpre : i < xss.length ∧ n ≤ (listListAt xss i).length) :
    op_list_list_take α ((xss, i), n) =
      NRest.returnT (listSet xss i ((listListAt xss i).take n)) := by
  simp [op_list_list_take, hpre]

/-! ## Source-shaped diagonal, registration, and database gates -/

private example :
    (op_list_list_lempty ℕ, op_list_list_lempty ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => NRest.nrestRel
          (listRel (listRel (Set.diagonal ℕ)))) :=
  op_list_list_lempty_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_list_push_back ℕ, op_list_list_push_back ℕ) ∈
      fref (fun p : (List (List ℕ) × ℕ) × ℕ =>
          p.1.2 < p.1.1.length)
        ((listRel (listRel (Set.diagonal ℕ)) ×ᵣ Set.diagonal ℕ) ×ᵣ
          Set.diagonal ℕ)
        (fun _ => NRest.nrestRel
          (listRel (listRel (Set.diagonal ℕ)))) :=
  op_list_list_push_back_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_list_pop_back ℕ, op_list_list_pop_back ℕ) ∈
      fref (fun p : List (List ℕ) × ℕ =>
          p.2 < p.1.length ∧ listListAt p.1 p.2 ≠ [])
        (listRel (listRel (Set.diagonal ℕ)) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel
          (Set.diagonal ℕ ×ᵣ listRel (listRel (Set.diagonal ℕ)))) :=
  op_list_list_pop_back_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_list_upd ℕ, op_list_list_upd ℕ) ∈
      fref (fun p : ((List (List ℕ) × ℕ) × ℕ) × ℕ =>
          p.1.1.2 < p.1.1.1.length ∧
            p.1.2 < (listListAt p.1.1.1 p.1.1.2).length)
        (((listRel (listRel (Set.diagonal ℕ)) ×ᵣ Set.diagonal ℕ) ×ᵣ
          Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel
          (listRel (listRel (Set.diagonal ℕ)))) :=
  op_list_list_upd_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_list_idx ℕ, op_list_list_idx ℕ) ∈
      fref (fun p : (List (List ℕ) × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧
            p.2 < (listListAt p.1.1 p.1.2).length)
        ((listRel (listRel (Set.diagonal ℕ)) ×ᵣ Set.diagonal ℕ) ×ᵣ
          Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) :=
  op_list_list_idx_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_list_llen ℕ, op_list_list_llen ℕ) ∈
      fref (fun p : List (List ℕ) × ℕ => p.2 < p.1.length)
        (listRel (listRel (Set.diagonal ℕ)) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) :=
  op_list_list_llen_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_list_len ℕ, op_list_list_len ℕ) ∈
      fref (fun _ : List (List ℕ) => True)
        (listRel (listRel (Set.diagonal ℕ)))
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) :=
  op_list_list_len_fref ℕ (Set.diagonal ℕ)

private example :
    (op_list_list_take ℕ, op_list_list_take ℕ) ∈
      fref (fun p : (List (List ℕ) × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧
            p.2 ≤ (listListAt p.1.1 p.1.2).length)
        ((listRel (listRel (Set.diagonal ℕ)) ×ᵣ Set.diagonal ℕ) ×ᵣ
          Set.diagonal ℕ)
        (fun _ => NRest.nrestRel
          (listRel (listRel (Set.diagonal ℕ)))) :=
  op_list_list_take_fref ℕ (Set.diagonal ℕ)

example : op_list_list_lempty ℕ ::ᵢ
    (ℕ → NRest (ListListI ℕ) ECost) :=
  op_list_list_lempty_registration_itype
example : op_list_list_push_back ℕ ::ᵢ
    (((ListListI ℕ × ℕ) × ℕ) → NRest (ListListI ℕ) ECost) :=
  op_list_list_push_back_registration_itype
example : op_list_list_pop_back ℕ ::ᵢ
    ((ListListI ℕ × ℕ) → NRest (ℕ × ListListI ℕ) ECost) :=
  op_list_list_pop_back_registration_itype
example : op_list_list_upd ℕ ::ᵢ
    ((((ListListI ℕ × ℕ) × ℕ) × ℕ) → NRest (ListListI ℕ) ECost) :=
  op_list_list_upd_registration_itype
example : op_list_list_idx ℕ ::ᵢ
    (((ListListI ℕ × ℕ) × ℕ) → NRest ℕ ECost) :=
  op_list_list_idx_registration_itype
example : op_list_list_llen ℕ ::ᵢ
    ((ListListI ℕ × ℕ) → NRest ℕ ECost) :=
  op_list_list_llen_registration_itype
example : op_list_list_len ℕ ::ᵢ (ListListI ℕ → NRest ℕ ECost) :=
  op_list_list_len_registration_itype
example : op_list_list_take ℕ ::ᵢ
    (((ListListI ℕ × ℕ) × ℕ) → NRest (ListListI ℕ) ECost) :=
  op_list_list_take_registration_itype

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``op_list_list_lempty_fref, ``op_list_list_push_back_fref,
      ``op_list_list_pop_back_fref, ``op_list_list_upd_fref,
      ``op_list_list_idx_fref, ``op_list_list_llen_fref,
      ``op_list_list_len_fref, ``op_list_list_take_fref] do
    unless rules.contains n do
      throwError "list-list interface gate: missing parametricity rule {n}"

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.listListAt_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms listListAt_rel

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_list_list_pop_back_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_list_list_pop_back_fref

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_list_list_upd_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_list_list_upd_fref

end Lax13Proofs.Refine.Sepref.Iicf
