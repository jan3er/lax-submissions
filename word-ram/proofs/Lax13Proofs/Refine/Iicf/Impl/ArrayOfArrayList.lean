import Lax13Proofs.Refine.Iicf.Impl.MSArrayList
import Lax13Proofs.Refine.Iicf.Intf.ListList

/-!
# Array of array lists

Faithful semantic adaptation of
`IICF/Impl/IICF_Array_of_Array_List.thy` and `ds/Array_of_Array_List.thy`
at `isabelle_llvm_time` commit `42dd7f59998d76047bb4b6bce76d8f67b53a08b6`.

The source owns an outer array of pointers to independently owned dynamic
array lists.  This IR has neither allocation/deallocation nor dynamic array
name selection, so no such outer-selection command is claimed here.  The
carrier instead records caller-established fixed-capacity rows.  The full
nested-list refinement is semantic; executable rules begin only after a
selected row's ordinary array/metadata ownership has been supplied.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

structure ArrayOfArrayList where
  outerLength : ℕ
  rows : List MSArrayList
deriving DecidableEq, Repr

/-- The source bound `length row + 1 < max_snat innerWidth` leaves exactly
`innerMax - 1` usable physical cells in this nonallocating adaptation. -/
def aalRowRel (innerMax : ℕ) : Set (MSArrayList × List ℕ) :=
  isMSArrayList (innerMax - 1)

def aalRel1 (outerMax innerMax : ℕ) :
    Set (ArrayOfArrayList × List (List ℕ)) :=
  {p | p.1.outerLength = p.1.rows.length ∧
    p.1.rows.length < outerMax ∧
    (p.1.rows, p.2) ∈ listRel (aalRowRel innerMax)}

theorem aalRel1_singleValued (outerMax innerMax : ℕ) :
    SingleValued (aalRel1 outerMax innerMax) := by
  intro s xs ys hx hy
  rcases hx with ⟨_, _, hx⟩
  rcases hy with ⟨_, _, hy⟩
  change List.Forall₂ (fun row zs => (row, zs) ∈ aalRowRel innerMax)
    s.rows xs at hx
  change List.Forall₂ (fun row zs => (row, zs) ∈ aalRowRel innerMax)
    s.rows ys at hy
  have aux : ∀ (rows : List MSArrayList) (xss yss : List (List ℕ)),
      List.Forall₂ (fun row zs => (row, zs) ∈ aalRowRel innerMax) rows xss →
      List.Forall₂ (fun row zs => (row, zs) ∈ aalRowRel innerMax) rows yss →
      xss = yss := by
    intro rows xss yss has
    induction has generalizing yss with
    | nil => intro hbs; cases hbs; rfl
    | cons hrow hrows ih =>
        intro hbs
        cases hbs with
        | cons hrow' hrows' =>
            congr
            · exact (isMSArrayList_singleValued (innerMax - 1))
                _ _ _ hrow hrow'
            · exact ih _ hrows'
  exact aux s.rows xs ys hx hy

def aalRel {α : Type} (outerMax innerMax : ℕ) (A : α → ℕ → Assn) :
    Set (ArrayOfArrayList × List (List α)) :=
  relComp (aalRel1 outerMax innerMax)
    (listRel (listRel (thePure A)))

/-- Source `aal_assn A`, retained as the same two-stage generic nested-list
composition.  It is deliberately pure at the outer carrier boundary because
the current heap language cannot represent arrays of owned row pointers. -/
def aalAssn {α : Type} (outerMax innerMax : ℕ) (A : α → ℕ → Assn) :
    List (List α) → ArrayOfArrayList → Assn :=
  pureAssn (aalRel outerMax innerMax A)

@[intf_of_assn] theorem aalAssn_intf {α : Type} (outerMax innerMax : ℕ)
    (A : α → ℕ → Assn) : intfOfAssn (aalAssn outerMax innerMax A)
      (ListListI α) := trivial

theorem aalRel1_outer_bound {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) : xss.length < outerMax := by
  simpa [h.2.2.length_eq] using h.2.1

private theorem listAt?_eq_getElem?_aal {β : Type} (xs : List β) (i : ℕ) :
    listAt? xs i = xs[i]? := by
  induction xs generalizing i with
  | nil => simp [listAt?]
  | cons x xs ih => cases i <;> simp [listAt?, ih]

theorem aalRel1_inner_bound {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {xs : List ℕ}
    (hinner : 0 < innerMax) (hxs : xs ∈ xss) :
    xs.length + 1 ≤ innerMax := by
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hxs
  have hr := listRel_at h.2.2 i
  have hxopt : listAt? xss i = some xs := by
    rw [listAt?_eq_getElem?_aal, List.getElem?_eq_getElem hi, hix]
  cases hrow : listAt? s.rows i with
  | none => simp [hrow, hxopt] at hr
  | some row =>
    have hrx : (row, xs) ∈ aalRowRel innerMax := by
      simpa [hrow, hxopt] using hr
    have hlen := isMSArrayList_length hrx
    have hle : xs.length ≤ innerMax - 1 := by
      rw [← hlen]
      exact hrx.2.1
    omega

/-! ## Pure/caller-owned empty establishment -/

def aalEmptyModel (innerMax n : ℕ) : ArrayOfArrayList :=
  ⟨n, List.replicate n (marlEmptyModel (innerMax - 1))⟩

open Classical in
noncomputable def aalEmptyIn (outerMax innerMax outerLength : ℕ)
    (rows : List MSArrayList) : Option ArrayOfArrayList :=
  if outerLength = rows.length ∧ rows.length < outerMax ∧
      ∀ row ∈ rows, (row, []) ∈ aalRowRel innerMax then
    some ⟨outerLength, rows⟩
  else none

theorem aalEmptyModel_refines {outerMax innerMax n : ℕ}
    (hn : n < outerMax) :
    (aalEmptyModel innerMax n, List.replicate n []) ∈
      aalRel1 outerMax innerMax := by
  refine ⟨by simp [aalEmptyModel], by simpa [aalEmptyModel], ?_⟩
  change List.Forall₂ (fun row xs => (row, xs) ∈ aalRowRel innerMax)
    (List.replicate n (marlEmptyModel (innerMax - 1)))
    (List.replicate n [])
  exact listRel_replicate (marlEmptyModel_refines (innerMax - 1)) n

theorem aalEmptyIn_some {outerMax innerMax outerLength : ℕ}
    {rows : List MSArrayList} {s : ArrayOfArrayList}
    (h : aalEmptyIn outerMax innerMax outerLength rows = some s) :
    (s, List.replicate outerLength []) ∈ aalRel1 outerMax innerMax := by
  simp only [aalEmptyIn] at h
  split at h
  · rename_i hs
    simp only [Option.some.injEq] at h
    subst s
    refine ⟨hs.1, by simpa [hs.1] using hs.2.1, ?_⟩
    change List.Forall₂ (fun row xs => (row, xs) ∈ aalRowRel innerMax)
      rows (List.replicate outerLength [])
    rw [hs.1]
    have build : ∀ rs : List MSArrayList,
        (∀ r ∈ rs, (r, []) ∈ aalRowRel innerMax) →
        List.Forall₂ (fun row xs => (row, xs) ∈ aalRowRel innerMax)
          rs (List.replicate rs.length []) := by
      intro rs hall
      induction rs with
      | nil => exact List.Forall₂.nil
      | cons row rs ih =>
          exact List.Forall₂.cons (hall row (by simp))
            (ih (fun r hr => hall r (by simp [hr])))
    exact build rows hs.2.2
  · contradiction

noncomputable def opAalEmptySz (α : Type) (_outerMax _innerMax : ℕ) :
    ℕ → NRest (List (List α)) ECost := op_list_list_lempty α

sepref_register opAalEmptySz : opAalEmptySz as
  (∀ α : Type, ℕ → ℕ → ℕ → NRest (ListListI α) ECost)

theorem aal_fold_custom_empty {α : Type} (outerMax innerMax n : ℕ) :
    op_list_list_lempty α n = opAalEmptySz α outerMax innerMax n := rfl

theorem aal_fold_custom_empty_replicate {α : Type}
    (outerMax innerMax n : ℕ) :
    NRest.returnT (List.replicate n ([] : List α)) =
      opAalEmptySz α outerMax innerMax n := rfl

noncomputable def aalEmptyOp (outerMax innerMax n : ℕ) :
    NRest ArrayOfArrayList ECost :=
  NRest.bindT (NRest.assert (n < outerMax ∧ 4 < innerMax)) fun _ =>
    NRest.returnT (aalEmptyModel innerMax n)

@[sepref_fref_thms] theorem aalEmptyOp_refines {α : Type} (outerMax innerMax : ℕ)
    (A : α → ℕ → Assn) :
    (aalEmptyOp outerMax innerMax, opAalEmptySz α outerMax innerMax) ∈
      fref (fun n : ℕ => n < outerMax ∧ 4 < innerMax) (Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (aalRel outerMax innerMax A)) := by
  intro n m hm hnm
  change n = m at hnm
  subst m
  simp [aalEmptyOp, hm, opAalEmptySz]
  exact NRest.param_returnT
    ⟨List.replicate n [], aalEmptyModel_refines hm.1,
      listRel_replicate List.Forall₂.nil n⟩

/-! ## Semantic carrier operations -/

def aalPush (innerMax : ℕ) (s : ArrayOfArrayList) (i x : ℕ) :
    Option ArrayOfArrayList :=
  match listAt? s.rows i with
  | none => none
  | some row =>
      match marlAppend (innerMax - 1) row x with
      | none => none
      | some row' => some ⟨s.outerLength, listSet s.rows i row'⟩

def aalPop (s : ArrayOfArrayList) (i : ℕ) :
    Option (ℕ × ArrayOfArrayList) :=
  match listAt? s.rows i with
  | none => none
  | some row =>
      match marlLast? row, marlButlast row with
      | some x, some row' => some (x, ⟨s.outerLength, listSet s.rows i row'⟩)
      | _, _ => none

def aalIdx (s : ArrayOfArrayList) (i j : ℕ) : Option ℕ :=
  match listAt? s.rows i with
  | none => none
  | some row => marlGet? row j

def aalUpd (s : ArrayOfArrayList) (i j x : ℕ) :
    Option ArrayOfArrayList :=
  match listAt? s.rows i with
  | none => none
  | some row =>
      match marlSet row j x with
      | none => none
      | some row' => some ⟨s.outerLength, listSet s.rows i row'⟩

def aalInnerLength (s : ArrayOfArrayList) (i : ℕ) : Option ℕ :=
  (listAt? s.rows i).map marlLength

def aalOuterLength (s : ArrayOfArrayList) : ℕ := s.outerLength

def aalTake (s : ArrayOfArrayList) (i l : ℕ) : Option ArrayOfArrayList :=
  match listAt? s.rows i with
  | none => none
  | some row =>
      if l ≤ row.length then
        some ⟨s.outerLength,
          listSet s.rows i ⟨row.buffer, l, row.capacity⟩⟩
      else none

/-! Source `aal_free` is intentionally not represented: P0 has no free
operation, and this IR has no deallocation semantics. -/

/-! ## Representation-preserving semantic bridges -/

theorem aalRel1_select {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i : ℕ}
    (hi : i < xss.length) :
    ∃ row xs, listAt? s.rows i = some row ∧ listAt? xss i = some xs ∧
      (row, xs) ∈ aalRowRel innerMax := by
  have hir : i < s.rows.length := by simpa [h.2.2.length_eq] using hi
  obtain ⟨row, hrow⟩ := listAt?_some_of_lt hir
  obtain ⟨xs, hxs⟩ := listAt?_some_of_lt hi
  have hr := listRel_at h.2.2 i
  exact ⟨row, xs, hrow, hxs, by simpa [hrow, hxs] using hr⟩

theorem aalRel1_set {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) (i : ℕ)
    {row : MSArrayList} {xs : List ℕ}
    (hrow : (row, xs) ∈ aalRowRel innerMax) :
    (⟨s.outerLength, listSet s.rows i row⟩,
      listSet xss i xs) ∈ aalRel1 outerMax innerMax := by
  refine ⟨by simpa using h.1, by simpa using h.2.1, ?_⟩
  exact listRel_set h.2.2 hrow i

theorem aalRowTake_refines {innerMax : ℕ} {row : MSArrayList}
    {xs : List ℕ} (h : (row, xs) ∈ aalRowRel innerMax)
    {l : ℕ} (hl : l ≤ xs.length) :
    (⟨row.buffer, l, row.capacity⟩, xs.take l) ∈ aalRowRel innerMax := by
  change row.buffer.length = innerMax - 1 ∧ row.length ≤ innerMax - 1 ∧
    row.capacity = innerMax - 1 ∧ row.active = xs at h
  change row.buffer.length = innerMax - 1 ∧ l ≤ innerMax - 1 ∧
    row.capacity = innerMax - 1 ∧ row.buffer.take l = xs.take l
  refine ⟨h.1, ?_, h.2.2.1, ?_⟩
  · rw [← isMSArrayList_length h] at hl
    omega
  · have hactive : row.buffer.take row.length = xs := by
      simpa [BoundedArray.active, Nat.min_eq_left h.2.1] using h.2.2.2
    rw [← hactive, List.take_take,
      Nat.min_eq_left (by simpa [isMSArrayList_length h] using hl)]

theorem aalPush_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i x : ℕ}
    (hi : i < xss.length)
    (hspace : (listListAt xss i).length + 1 < innerMax) :
    ∃ t, aalPush innerMax s i x = some t ∧
      (t, listSet xss i (listListAt xss i ++ [x])) ∈
        aalRel1 outerMax innerMax := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  have hxss : listListAt xss i = xs := by simp [listListAt, hxs]
  have hlen : row.length = xs.length := isMSArrayList_length hr
  have hroom : row.length < innerMax - 1 := by
    rw [hlen]
    rw [hxss] at hspace
    omega
  let row' : MSArrayList :=
    ⟨row.buffer.set row.length x, row.length + 1, innerMax - 1⟩
  have hp : marlAppend (innerMax - 1) row x = some row' := by
    simp [marlAppend, hroom, row']
  let t : ArrayOfArrayList :=
    ⟨s.outerLength, listSet s.rows i row'⟩
  refine ⟨t, by simp [aalPush, hrow, hp, t], ?_⟩
  have hr' := marlAppend_some_refines hr hp
  simpa [t, hxss] using aalRel1_set h i hr'

theorem aalPop_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i : ℕ}
    (hi : i < xss.length) (hne : listListAt xss i ≠ []) :
    ∃ x t, aalPop s i = some (x, t) ∧
      listAt? (listListAt xss i).reverse 0 = some x ∧
      (t, listSet xss i (listButlast (listListAt xss i))) ∈
        aalRel1 outerMax innerMax := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  have hxss : listListAt xss i = xs := by simp [listListAt, hxs]
  have hxsne : xs ≠ [] := by simpa [hxss] using hne
  have hlen : row.length ≠ 0 := by
    rw [isMSArrayList_length hr]
    exact fun hz => hxsne (List.eq_nil_of_length_eq_zero hz)
  obtain ⟨x, hx⟩ := listAt?_some_of_lt
    (show 0 < xs.reverse.length by cases xs <;> simp_all)
  let row' : MSArrayList := ⟨row.buffer, row.length - 1, row.capacity⟩
  have hlast : marlLast? row = some x := by simpa [marlLast_refines hr] using hx
  have hbut : marlButlast row = some row' := by
    simp [marlButlast, hlen, row']
  let t : ArrayOfArrayList :=
    ⟨s.outerLength, listSet s.rows i row'⟩
  refine ⟨x, t, by simp [aalPop, hrow, hlast, hbut, t], by simpa [hxss], ?_⟩
  have hr' := marlButlast_some_refines hr hbut
  simpa [t, hxss] using aalRel1_set h i hr'

theorem aalIdx_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i j : ℕ}
    (hi : i < xss.length) :
    aalIdx s i j = listAt? (listListAt xss i) j := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  simp [aalIdx, hrow, marlGet_refines hr, listListAt, hxs]

theorem aalUpd_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i j x : ℕ}
    (hi : i < xss.length) (hj : j < (listListAt xss i).length) :
    ∃ t, aalUpd s i j x = some t ∧
      (t, listSet xss i (listSet (listListAt xss i) j x)) ∈
        aalRel1 outerMax innerMax := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  have hxss : listListAt xss i = xs := by simp [listListAt, hxs]
  have hjr : j < row.length := by
    rw [isMSArrayList_length hr]
    simpa [hxss] using hj
  let row' : MSArrayList :=
    ⟨row.buffer.set j x, row.length, row.capacity⟩
  have hp : marlSet row j x = some row' := by simp [marlSet, hjr, row']
  let t : ArrayOfArrayList :=
    ⟨s.outerLength, listSet s.rows i row'⟩
  refine ⟨t, by simp [aalUpd, hrow, hp, t], ?_⟩
  have hr' := marlSet_some_refines hr hp
  simpa [t, hxss] using aalRel1_set h i hr'

theorem aalInnerLength_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i : ℕ}
    (hi : i < xss.length) :
    aalInnerLength s i = some (listListAt xss i).length := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  simp [aalInnerLength, hrow, marlLength_refines hr, listListAt, hxs]

theorem aalOuterLength_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) :
    aalOuterLength s = xss.length := by
  rw [aalOuterLength, h.1, h.2.2.length_eq]

theorem aalTake_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i l : ℕ}
    (hi : i < xss.length) (hl : l ≤ (listListAt xss i).length) :
    ∃ t, aalTake s i l = some t ∧
      (t, listSet xss i ((listListAt xss i).take l)) ∈
        aalRel1 outerMax innerMax := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  have hxss : listListAt xss i = xs := by simp [listListAt, hxs]
  have hlr : l ≤ row.length := by
    rw [isMSArrayList_length hr]
    simpa [hxss] using hl
  let row' : MSArrayList := ⟨row.buffer, l, row.capacity⟩
  let t : ArrayOfArrayList :=
    ⟨s.outerLength, listSet s.rows i row'⟩
  refine ⟨t, by simp [aalTake, hrow, hlr, row', t], ?_⟩
  have hr' := aalRowTake_refines hr (by simpa [hxss] using hl)
  simpa [row', t, hxss] using aalRel1_set h i hr'

/-! ## Generic nested-list operation refinements -/

noncomputable def aalPushOp (innerMax : ℕ)
    (p : (ArrayOfArrayList × ℕ) × ℕ) : NRest ArrayOfArrayList ECost :=
  match aalPush innerMax p.1.1 p.1.2 p.2 with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def aalPopOp (p : ArrayOfArrayList × ℕ) :
    NRest (ℕ × ArrayOfArrayList) ECost :=
  match aalPop p.1 p.2 with
  | some q => NRest.returnT q
  | none => NRest.fail

noncomputable def aalIdxOp (p : (ArrayOfArrayList × ℕ) × ℕ) :
    NRest ℕ ECost :=
  NRest.spec (fun x => aalIdx p.1.1 p.1.2 p.2 = some x) (fun _ => 0)

noncomputable def aalUpdOp (p : ((ArrayOfArrayList × ℕ) × ℕ) × ℕ) :
    NRest ArrayOfArrayList ECost :=
  match aalUpd p.1.1.1 p.1.1.2 p.1.2 p.2 with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def aalInnerLengthOp (p : ArrayOfArrayList × ℕ) :
    NRest ℕ ECost :=
  match aalInnerLength p.1 p.2 with
  | some n => NRest.returnT n
  | none => NRest.fail

noncomputable def aalOuterLengthOp (s : ArrayOfArrayList) : NRest ℕ ECost :=
  NRest.returnT (aalOuterLength s)

noncomputable def aalTakeOp (p : (ArrayOfArrayList × ℕ) × ℕ) :
    NRest ArrayOfArrayList ECost :=
  match aalTake p.1.1 p.1.2 p.2 with
  | some t => NRest.returnT t
  | none => NRest.fail

@[sepref_fref_thms] theorem aalPushOp_refines {α : Type}
    (outerMax innerMax : ℕ) (A : α → ℕ → Assn) (_hPure : isPure A) :
    (aalPushOp innerMax, op_list_list_push_back α) ∈
      fref (fun p : (List (List α) × ℕ) × α =>
          p.1.2 < p.1.1.length ∧
          (listListAt p.1.1 p.1.2).length + 1 < innerMax)
        ((aalRel outerMax innerMax A ×ᵣ Set.diagonal ℕ) ×ᵣ thePure A)
        (fun _ => NRest.nrestRel (aalRel outerMax innerMax A)) := by
  rintro ⟨⟨s, i⟩, x⟩ ⟨⟨xss, j⟩, a⟩ hpre ⟨⟨hs, hij⟩, hxa⟩
  change i = j at hij
  subst j
  obtain ⟨nss, hsn, hnx⟩ := hs
  have hp : i < nss.length ∧
      (listListAt nss i).length + 1 < innerMax := by
    exact ⟨by simpa [hnx.length_eq] using hpre.1,
      by simpa [listListAt_length hnx i] using hpre.2⟩
  obtain ⟨t, ht, hrel⟩ := aalPush_refines hsn (x := x) hp.1 hp.2
  have hinner := listListAt_rel hnx i
  have hout := listRel_set hnx
    (List.rel_append hinner (List.Forall₂.cons hxa List.Forall₂.nil)) i
  simp [aalPushOp, ht, op_list_list_push_back, hpre.1]
  exact NRest.param_returnT
    ⟨listSet nss i (listListAt nss i ++ [x]), hrel, hout⟩

@[sepref_fref_thms] theorem aalPopOp_refines {α : Type}
    (outerMax innerMax : ℕ) (A : α → ℕ → Assn) :
    (aalPopOp, op_list_list_pop_back α) ∈
      fref (fun p : List (List α) × ℕ =>
          p.2 < p.1.length ∧ listListAt p.1 p.2 ≠ [])
        (aalRel outerMax innerMax A ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (thePure A ×ᵣ aalRel outerMax innerMax A)) := by
  rintro ⟨s, i⟩ ⟨xss, j⟩ hpre ⟨hs, hij⟩
  change i = j at hij
  subst j
  obtain ⟨nss, hsn, hnx⟩ := hs
  have hp : i < nss.length ∧ listListAt nss i ≠ [] :=
    ⟨by simpa [hnx.length_eq] using hpre.1,
      (listListAt_ne_nil hnx i).mpr hpre.2⟩
  obtain ⟨x, t, ht, hx, hrel⟩ := aalPop_refines hsn hp.1 hp.2
  have hinner := listListAt_rel hnx i
  have hr := List.rel_reverse hinner
  obtain ⟨a, ha, hxa⟩ := listOption_obtain_left
    (by simpa [hx] using listRel_at hr 0)
  have hout := listRel_set hnx (listRel_butlast hinner) i
  simp only [op_list_list_pop_back, NRest.assert_pos hpre,
    NRest.returnT_bindT]
  rw [listOptionSpec_eq_returnT ha]
  simp [aalPopOp, ht]
  exact NRest.param_returnT
    ⟨hxa, ⟨listSet nss i (listButlast (listListAt nss i)), hrel, hout⟩⟩

@[sepref_fref_thms] theorem aalIdxOp_refines {α : Type}
    (outerMax innerMax : ℕ) (A : α → ℕ → Assn) :
    (aalIdxOp, op_list_list_idx α) ∈
      fref (fun p : (List (List α) × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧
          p.2 < (listListAt p.1.1 p.1.2).length)
        ((aalRel outerMax innerMax A ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (thePure A)) := by
  rintro ⟨⟨s, i⟩, k⟩ ⟨⟨xss, j⟩, l⟩ hpre ⟨⟨hs, hij⟩, hkl⟩
  change i = j at hij
  change k = l at hkl
  subst j
  subst l
  obtain ⟨nss, hsn, hnx⟩ := hs
  have hp : i < nss.length ∧ k < (listListAt nss i).length :=
    ⟨by simpa [hnx.length_eq] using hpre.1,
      by simpa [listListAt_length hnx i] using hpre.2⟩
  obtain ⟨x, hx⟩ := listAt?_some_of_lt hp.2
  obtain ⟨a, ha, hxa⟩ := listOption_obtain_left
    (by simpa [hx] using listRel_at (listListAt_rel hnx i) k)
  change (aalIdxOp ((s, i), k), op_list_list_idx α ((xss, i), k)) ∈
    NRest.nrestRel (thePure A)
  simp only [op_list_list_idx, NRest.assert_pos hpre, NRest.returnT_bindT]
  rw [listOptionSpec_eq_returnT ha]
  rw [aalIdxOp, aalIdx_refines hsn hp.1,
    listOptionSpec_eq_returnT hx]
  exact NRest.param_returnT hxa

@[sepref_fref_thms] theorem aalUpdOp_refines {α : Type}
    (outerMax innerMax : ℕ) (A : α → ℕ → Assn) :
    (aalUpdOp, op_list_list_upd α) ∈
      fref (fun p : ((List (List α) × ℕ) × ℕ) × α =>
          p.1.1.2 < p.1.1.1.length ∧
          p.1.2 < (listListAt p.1.1.1 p.1.1.2).length)
        (((aalRel outerMax innerMax A ×ᵣ Set.diagonal ℕ) ×ᵣ
          Set.diagonal ℕ) ×ᵣ thePure A)
        (fun _ => NRest.nrestRel (aalRel outerMax innerMax A)) := by
  rintro ⟨⟨⟨s, i⟩, k⟩, x⟩ ⟨⟨⟨xss, j⟩, l⟩, a⟩ hpre
    ⟨⟨⟨hs, hij⟩, hkl⟩, hxa⟩
  change i = j at hij
  change k = l at hkl
  subst j
  subst l
  obtain ⟨nss, hsn, hnx⟩ := hs
  have hp : i < nss.length ∧ k < (listListAt nss i).length :=
    ⟨by simpa [hnx.length_eq] using hpre.1,
      by simpa [listListAt_length hnx i] using hpre.2⟩
  obtain ⟨t, ht, hrel⟩ := aalUpd_refines hsn (x := x) hp.1 hp.2
  have hout := listRel_set hnx
    (listRel_set (listListAt_rel hnx i) hxa k) i
  simp [aalUpdOp, ht, op_list_list_upd, hpre]
  exact NRest.param_returnT
    ⟨listSet nss i (listSet (listListAt nss i) k x), hrel, hout⟩

@[sepref_fref_thms] theorem aalInnerLengthOp_refines {α : Type}
    (outerMax innerMax : ℕ) (A : α → ℕ → Assn) :
    (aalInnerLengthOp, op_list_list_llen α) ∈
      fref (fun p : List (List α) × ℕ => p.2 < p.1.length)
        (aalRel outerMax innerMax A ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  rintro ⟨s, i⟩ ⟨xss, j⟩ hi ⟨hs, hij⟩
  change i = j at hij
  subst j
  obtain ⟨nss, hsn, hnx⟩ := hs
  have hin : i < nss.length := by simpa [hnx.length_eq] using hi
  change (aalInnerLengthOp (s, i), op_list_list_llen α (xss, i)) ∈
    NRest.nrestRel (Set.diagonal ℕ)
  simp [aalInnerLengthOp, aalInnerLength_refines hsn hin,
    op_list_list_llen, hi, listListAt_length hnx i]

@[sepref_fref_thms] theorem aalOuterLengthOp_refines {α : Type}
    (outerMax innerMax : ℕ) (A : α → ℕ → Assn) :
    (aalOuterLengthOp, op_list_list_len α) ∈
      fref (fun _ : List (List α) => True) (aalRel outerMax innerMax A)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro s xss _ hs
  obtain ⟨nss, hsn, hnx⟩ := hs
  apply NRest.param_returnT
  change aalOuterLength s = xss.length
  rw [aalOuterLength_refines hsn, hnx.length_eq]

@[sepref_fref_thms] theorem aalTakeOp_refines {α : Type}
    (outerMax innerMax : ℕ) (A : α → ℕ → Assn) :
    (aalTakeOp, op_list_list_take α) ∈
      fref (fun p : (List (List α) × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧
          p.2 ≤ (listListAt p.1.1 p.1.2).length)
        ((aalRel outerMax innerMax A ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (aalRel outerMax innerMax A)) := by
  rintro ⟨⟨s, i⟩, n⟩ ⟨⟨xss, j⟩, m⟩ hpre ⟨⟨hs, hij⟩, hnm⟩
  change i = j at hij
  change n = m at hnm
  subst j
  subst m
  obtain ⟨nss, hsn, hnx⟩ := hs
  have hp : i < nss.length ∧ n ≤ (listListAt nss i).length :=
    ⟨by simpa [hnx.length_eq] using hpre.1,
      by simpa [listListAt_length hnx i] using hpre.2⟩
  obtain ⟨t, ht, hrel⟩ := aalTake_refines hsn hp.1 hp.2
  have hout := listRel_set hnx
    (List.forall₂_take n (listListAt_rel hnx i)) i
  simp [aalTakeOp, ht, op_list_list_take, hpre]
  exact NRest.param_returnT
    ⟨listSet nss i ((listListAt nss i).take n), hrel, hout⟩

/-! ## Exact executable selected-row boundary

There is intentionally no command for selecting `s.rows[i]`: the IR cannot
store an outer array of row pointers.  These rules start after the caller has
supplied the selected row's array, length, and capacity cells. -/

noncomputable abbrev aalRowPushCost := marlAppendCost
noncomputable abbrev aalRowIdxCost := marlGetCost
noncomputable abbrev aalRowUpdCost := marlSetCost
noncomputable abbrev aalRowInnerLengthCost := marlLengthCost
noncomputable abbrev aalOuterLengthCost := marlLengthCost

noncomputable abbrev aalRowPushExecSpec := marlAppendExecSpec
noncomputable abbrev aalRowIdxExecSpec := marlGetExecSpec
noncomputable abbrev aalRowUpdExecSpec := marlSetExecSpec
noncomputable abbrev aalRowInnerLengthExecSpec := marlLengthExecSpec
noncomputable abbrev aalOuterLengthExecSpec := marlLengthExecSpec

abbrev aalRowPushCom := marlAppendCom
abbrev aalRowIdxCom := marlGetCom
abbrev aalRowUpdCom := marlSetCom
abbrev aalRowInnerLengthCom := marlLengthCom
abbrev aalOuterLengthCom := marlLengthCom

noncomputable def aalRowPopRaw (buffer : List ℕ) (n cap : ℕ) :
    NRest (ℕ × (List ℕ × (ℕ × ℕ))) ECost :=
  NRest.bindT (marlPred n) fun n' =>
    NRest.bindT (mopAget buffer n') fun x =>
      NRest.bindT (mopPair n' cap) fun md =>
        NRest.bindT (mopPair buffer md) fun row => mopPair x row

noncomputable def aalRowPopCost : ECost :=
  irUnit Currency.sub + irUnit Currency.aget + 3 • irUnit Currency.skip

noncomputable def aalRowPopExecSpec (buffer : List ℕ) (n cap : ℕ) :
    NRest (ℕ × (List ℕ × (ℕ × ℕ))) ECost :=
  NRest.consume
    (NRest.returnT (buffer[n - 1]!, (buffer, (n - 1, cap))))
    aalRowPopCost

theorem aalRowPopRaw_eq (buffer : List ℕ) (n cap : ℕ)
    (hn : n ≠ 0) (hle : n ≤ buffer.length) :
    aalRowPopRaw buffer n cap = aalRowPopExecSpec buffer n cap := by
  have hi : n - 1 < buffer.length := by omega
  simp [aalRowPopRaw, aalRowPopExecSpec, aalRowPopCost, marlPred,
    mopBinop_def, Imp.Bop.apply_sub, binopCurrency_sub, mopAget_def,
    NRest.assert_pos hi, Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def,
    NRest.consume_consume, three_nsmul]
  ac_rfl

sepref_synth aalRowPopSynth (A len cap one out : String)
    (buffer : List ℕ) (n c : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn 1 one ∗
      junkCell out)
    _ _ (out, (A, (len, cap)))
      (natAssn ×ₐ (arrayAssn ×ₐ (natAssn ×ₐ natAssn)))
    (aalRowPopRaw buffer n c)

def aalRowPopCom (A len _cap one out : String) : Com :=
  (Com.binop .sub len len one).seq
    ((Com.aget out A len).seq (Com.skip.seq (Com.skip.seq Com.skip)))

noncomputable def aalRowTakeRaw (buffer : List ℕ) (_oldLen cap newLen : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopPair newLen cap) fun md => mopPair buffer md

noncomputable def aalRowTakeCost : ECost := 2 • irUnit Currency.skip

noncomputable def aalRowTakeExecSpec (buffer : List ℕ)
    (_oldLen cap newLen : ℕ) : NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT (buffer, (newLen, cap))) aalRowTakeCost

theorem aalRowTakeRaw_eq (buffer : List ℕ) (oldLen cap newLen : ℕ) :
    aalRowTakeRaw buffer oldLen cap newLen =
      aalRowTakeExecSpec buffer oldLen cap newLen := by
  rw [aalRowTakeRaw, mopPair_def, bindT_unit, mopPair_def,
    NRest.consume_consume]
  simp only [aalRowTakeExecSpec, aalRowTakeCost, two_nsmul]

sepref_synth aalRowTakeSynth (A len cap newLen : String)
    (buffer : List ℕ) (n c l : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn l newLen)
    _ _ (A, (newLen, cap)) (arrayAssn ×ₐ (natAssn ×ₐ natAssn))
    (aalRowTakeRaw buffer n c l)

def aalRowTakeCom : Com := Com.skip.seq Com.skip

@[sepref_fr_rules] theorem aalRowPush_exec_hnr
    (A len cap value one : String) (buffer : List ℕ) (n c x : ℕ)
    (hi : n < buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn x value ∗ hnCtxt natAssn 1 one)
      (aalRowPushCom A len cap value one)
      (hnCtxt natAssn 1 one ∗ hnCtxt natAssn x value)
      (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (aalRowPushExecSpec buffer n c x) :=
  marlAppend_exec_hnr A len cap value one buffer n c x hi

@[sepref_fr_rules] theorem aalRowPop_exec_hnr
    (A len cap one out : String) (buffer : List ℕ) (n c : ℕ)
    (hn : n ≠ 0) (hle : n ≤ buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn 1 one ∗ junkCell out)
      (aalRowPopCom A len cap one out)
      (hnCtxt natAssn 1 one) (out, (A, (len, cap)))
      (natAssn ×ₐ (arrayAssn ×ₐ (natAssn ×ₐ natAssn)))
      (aalRowPopExecSpec buffer n c) := by
  rw [← aalRowPopRaw_eq buffer n c hn hle]
  exact aalRowPopSynth A len cap one out buffer n c

@[sepref_fr_rules] theorem aalRowIdx_exec_hnr
    (A idx out : String) (buffer : List ℕ) (i : ℕ)
    (hi : i < buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗ junkCell out)
      (aalRowIdxCom A idx out)
      (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx) out natAssn
      (aalRowIdxExecSpec buffer i) :=
  marlGet_exec_hnr A idx out buffer i hi

@[sepref_fr_rules] theorem aalRowUpd_exec_hnr
    (A len cap idx value : String) (buffer : List ℕ) (n c i x : ℕ)
    (hi : i < buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn i idx ∗ hnCtxt natAssn x value)
      (aalRowUpdCom A len cap idx value)
      (hnCtxt natAssn i idx ∗ hnCtxt natAssn x value)
      (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (aalRowUpdExecSpec buffer n c i x) :=
  marlSet_exec_hnr A len cap idx value buffer n c i x hi

@[sepref_fr_rules] theorem aalRowInnerLength_exec_hnr
    (len out : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ junkCell out)
      (aalRowInnerLengthCom len out) (hnCtxt natAssn n len) out natAssn
      (aalRowInnerLengthExecSpec n) :=
  marlLength_exec_hnr len out n

@[sepref_fr_rules] theorem aalOuterLength_exec_hnr
    (len out : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ junkCell out)
      (aalOuterLengthCom len out) (hnCtxt natAssn n len) out natAssn
      (aalOuterLengthExecSpec n) :=
  marlLength_exec_hnr len out n

@[sepref_fr_rules] theorem aalRowTake_exec_hnr
    (A len cap newLen : String) (buffer : List ℕ) (n c l : ℕ) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn l newLen)
      aalRowTakeCom (hnCtxt natAssn n len)
      (A, (newLen, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (aalRowTakeExecSpec buffer n c l) := by
  rw [← aalRowTakeRaw_eq buffer n c l]
  exact aalRowTakeSynth A len cap newLen buffer n c l

/-! ## Executable/whole-state bridges -/

theorem aalRowPushExecSpec_whole_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i x : ℕ}
    (hi : i < xss.length)
    (hspace : (listListAt xss i).length + 1 < innerMax) :
    ∃ row xs, listAt? s.rows i = some row ∧ listAt? xss i = some xs ∧
      aalRowPushExecSpec row.buffer row.length row.capacity x =
        NRest.consume (NRest.returnT
          (row.buffer.set row.length x, (row.length + 1, row.capacity)))
          aalRowPushCost ∧
      (⟨s.outerLength, listSet s.rows i
          ⟨row.buffer.set row.length x, row.length + 1, row.capacity⟩⟩,
        listSet xss i (listListAt xss i ++ [x])) ∈
          aalRel1 outerMax innerMax := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  have hxss : listListAt xss i = xs := by simp [listListAt, hxs]
  have hroom : xs.length < innerMax - 1 := by rw [hxss] at hspace; omega
  have he := marlAppendExecSpec_refines hr (x := x) hroom
  refine ⟨row, xs, hrow, hxs, he.1, ?_⟩
  simpa [hxss] using aalRel1_set h i he.2

theorem aalRowPopExecSpec_whole_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i : ℕ}
    (hi : i < xss.length) (hne : listListAt xss i ≠ []) :
    ∃ row xs x, listAt? s.rows i = some row ∧ listAt? xss i = some xs ∧
      listAt? xs.reverse 0 = some x ∧
      aalRowPopExecSpec row.buffer row.length row.capacity =
        NRest.consume (NRest.returnT
          (x, (row.buffer, (row.length - 1, row.capacity))))
          aalRowPopCost ∧
      (⟨s.outerLength, listSet s.rows i
          ⟨row.buffer, row.length - 1, row.capacity⟩⟩,
        listSet xss i (listButlast (listListAt xss i))) ∈
          aalRel1 outerMax innerMax := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  have hxss : listListAt xss i = xs := by simp [listListAt, hxs]
  have hxsne : xs ≠ [] := by simpa [hxss] using hne
  obtain ⟨x, hx, hlast⟩ := marlLastExecSpec_refines hr hxsne
  have hv : row.buffer[row.length - 1]! = x := by
    change NRest.consume (NRest.returnT row.buffer[row.length - 1]!)
        marlLastCost = NRest.consume (NRest.returnT x) marlLastCost at hlast
    simp only [NRest.consume_returnT] at hlast
    rw [NRest.rest_inj_iff] at hlast
    by_contra hne
    have he := congrFun hlast row.buffer[row.length - 1]!
    simp [NRest.single] at he
    apply hne
    simpa [List.getElem!_eq_getElem?_getD] using he
  have hbut := marlButlastExecSpec_refines hr hxsne
  refine ⟨row, xs, x, hrow, hxs, hx, ?_, ?_⟩
  · simp [aalRowPopExecSpec, hv]
  · simpa [hxss] using aalRel1_set h i hbut.2

theorem aalRowIdxExecSpec_refines {innerMax : ℕ} {row : MSArrayList}
    {xs : List ℕ} (h : (row, xs) ∈ aalRowRel innerMax)
    {i : ℕ} (hi : i < xs.length) :
    aalRowIdxExecSpec row.buffer i =
      NRest.consume (NRest.returnT xs[i]!) aalRowIdxCost :=
  marlGetExecSpec_refines h hi

theorem aalRowUpdExecSpec_whole_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i j x : ℕ}
    (hi : i < xss.length) (hj : j < (listListAt xss i).length) :
    ∃ row xs, listAt? s.rows i = some row ∧ listAt? xss i = some xs ∧
      aalRowUpdExecSpec row.buffer row.length row.capacity j x =
        NRest.consume (NRest.returnT
          (row.buffer.set j x, (row.length, row.capacity))) aalRowUpdCost ∧
      (⟨s.outerLength, listSet s.rows i
          ⟨row.buffer.set j x, row.length, row.capacity⟩⟩,
        listSet xss i (listSet (listListAt xss i) j x)) ∈
          aalRel1 outerMax innerMax := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  have hxss : listListAt xss i = xs := by simp [listListAt, hxs]
  have hjx : j < xs.length := by simpa [hxss] using hj
  have he := marlSetExecSpec_refines hr (x := x) hjx
  refine ⟨row, xs, hrow, hxs, he.1, ?_⟩
  simpa [hxss] using aalRel1_set h i he.2

theorem aalRowInnerLengthExecSpec_refines {innerMax : ℕ}
    {row : MSArrayList} {xs : List ℕ}
    (h : (row, xs) ∈ aalRowRel innerMax) :
    aalRowInnerLengthExecSpec row.length =
      NRest.consume (NRest.returnT xs.length) aalRowInnerLengthCost :=
  marlLengthExecSpec_refines h

theorem aalOuterLengthExecSpec_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) :
    aalOuterLengthExecSpec s.outerLength =
      NRest.consume (NRest.returnT xss.length) aalOuterLengthCost := by
  change NRest.consume (NRest.returnT s.outerLength) marlLengthCost = _
  rw [h.1, h.2.2.length_eq]

theorem aalRowTakeExecSpec_whole_refines {outerMax innerMax : ℕ}
    {s : ArrayOfArrayList} {xss : List (List ℕ)}
    (h : (s, xss) ∈ aalRel1 outerMax innerMax) {i l : ℕ}
    (hi : i < xss.length) (hl : l ≤ (listListAt xss i).length) :
    ∃ row xs, listAt? s.rows i = some row ∧ listAt? xss i = some xs ∧
      aalRowTakeExecSpec row.buffer row.length row.capacity l =
        NRest.consume (NRest.returnT (row.buffer, (l, row.capacity)))
          aalRowTakeCost ∧
      (⟨s.outerLength, listSet s.rows i
          ⟨row.buffer, l, row.capacity⟩⟩,
        listSet xss i ((listListAt xss i).take l)) ∈
          aalRel1 outerMax innerMax := by
  obtain ⟨row, xs, hrow, hxs, hr⟩ := aalRel1_select h hi
  have hxss : listListAt xss i = xs := by simp [listListAt, hxs]
  refine ⟨row, xs, hrow, hxs, rfl, ?_⟩
  simpa [hxss] using
    aalRel1_set h i (aalRowTake_refines hr (by simpa [hxss] using hl))

/-! The missing outer pointer-array operation is a checked negative
capability, not an omitted proof obligation. -/
def aalOuterSelectionSupported : Prop := False

theorem aalOuterSelection_unsupported : ¬ aalOuterSelectionSupported := by
  simp [aalOuterSelectionSupported]

/-! ## Regression and registration/cost gates -/

def aalLogical (s : ArrayOfArrayList) : List (List ℕ) :=
  s.rows.map (fun row => row.active)

def aalSourceRegression : Option ArrayOfArrayList := do
  let s0 := aalEmptyModel 8 2
  let s1 ← aalPush 8 s0 1 42
  let s2 ← aalPush 8 s1 1 43
  let (x, s3) ← aalPop s2 1
  let s4 ← aalPush 8 s3 1 x
  aalTake s4 1 1

#guard (aalSourceRegression.map aalLogical) = some [[], [42]]

#guard aalRowPushCom "A" "len" "cap" "value" "one" =
  (Com.aset "A" "len" "value").seq
    ((Com.binop .add "len" "len" "one").seq (Com.skip.seq Com.skip))
#guard aalRowPopCom "A" "len" "cap" "one" "out" =
  (Com.binop .sub "len" "len" "one").seq
    ((Com.aget "out" "A" "len").seq (Com.skip.seq (Com.skip.seq Com.skip)))
#guard aalRowIdxCom "A" "idx" "out" = .aget "out" "A" "idx"
#guard aalRowUpdCom "A" "len" "cap" "idx" "value" =
  .seq (.aset "A" "idx" "value") (.seq .skip .skip)
#guard aalRowInnerLengthCom "len" "out" = .copy "out" "len"
#guard aalOuterLengthCom "len" "out" = .copy "out" "len"
#guard aalRowTakeCom = Com.skip.seq Com.skip

theorem aalRowPushCost_aset : aalRowPushCost.toFun Currency.aset = 1 := by decide +kernel
theorem aalRowPopCost_sub : aalRowPopCost.toFun Currency.sub = 1 := by decide +kernel
theorem aalRowPopCost_aget : aalRowPopCost.toFun Currency.aget = 1 := by decide +kernel
theorem aalRowPopCost_skip : aalRowPopCost.toFun Currency.skip = 3 := by decide +kernel
theorem aalRowIdxCost_aget : aalRowIdxCost.toFun Currency.aget = 1 := by decide +kernel
theorem aalRowUpdCost_aset : aalRowUpdCost.toFun Currency.aset = 1 := by decide +kernel
theorem aalRowInnerLengthCost_copy :
    aalRowInnerLengthCost.toFun Currency.copy = 1 := by decide +kernel
theorem aalOuterLengthCost_copy :
    aalOuterLengthCost.toFun Currency.copy = 1 := by decide +kernel
theorem aalRowTakeCost_skip : aalRowTakeCost.toFun Currency.skip = 2 := by decide +kernel

private theorem ecost_ne_zero_of_pos (C : ECost) (c : String)
    (h : 0 < C.toFun c) : C ≠ 0 := by
  intro hz
  rw [hz] at h
  simp at h

theorem aalRowPushCost_ne_zero : aalRowPushCost ≠ 0 :=
  ecost_ne_zero_of_pos _ Currency.aset (by simp [aalRowPushCost_aset])
theorem aalRowPopCost_ne_zero : aalRowPopCost ≠ 0 :=
  ecost_ne_zero_of_pos _ Currency.sub (by simp [aalRowPopCost_sub])
theorem aalRowIdxCost_ne_zero : aalRowIdxCost ≠ 0 :=
  ecost_ne_zero_of_pos _ Currency.aget (by simp [aalRowIdxCost_aget])
theorem aalRowUpdCost_ne_zero : aalRowUpdCost ≠ 0 :=
  ecost_ne_zero_of_pos _ Currency.aset (by simp [aalRowUpdCost_aset])
theorem aalRowInnerLengthCost_ne_zero : aalRowInnerLengthCost ≠ 0 :=
  ecost_ne_zero_of_pos _ Currency.copy (by simp [aalRowInnerLengthCost_copy])
theorem aalOuterLengthCost_ne_zero : aalOuterLengthCost ≠ 0 :=
  ecost_ne_zero_of_pos _ Currency.copy (by simp [aalOuterLengthCost_copy])
theorem aalRowTakeCost_ne_zero : aalRowTakeCost ≠ 0 :=
  ecost_ne_zero_of_pos _ Currency.skip (by simp [aalRowTakeCost_skip])

example : opAalEmptySz ::ᵢ
    (∀ α : Type, ℕ → ℕ → ℕ → NRest (ListListI α) ECost) :=
  opAalEmptySz_itype

run_cmd do
  let frefs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``aalEmptyOp_refines, ``aalPushOp_refines, ``aalPopOp_refines,
      ``aalIdxOp_refines, ``aalUpdOp_refines, ``aalInnerLengthOp_refines,
      ``aalOuterLengthOp_refines, ``aalTakeOp_refines] do
    unless frefs.contains n do
      throwError "array-of-array-list source rule missing from DB: {n}"
  let frules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  for n in #[``aalRowPush_exec_hnr, ``aalRowPop_exec_hnr,
      ``aalRowIdx_exec_hnr, ``aalRowUpd_exec_hnr,
      ``aalRowInnerLength_exec_hnr, ``aalOuterLength_exec_hnr,
      ``aalRowTake_exec_hnr] do
    unless frules.contains n do
      throwError "array-of-array-list executable rule missing from DB: {n}"

/-! Allocation-backed empty and generic runtime outer selection have no
executable rule and therefore no invented zero-cost placeholder. -/

/-! ## Kernel-three gates -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.aalRel1_singleValued' does not depend on any axioms -/
#guard_msgs in
#print axioms aalRel1_singleValued

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.aalPushOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aalPushOp_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.aalRowPop_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aalRowPop_exec_hnr

end Lax13Proofs.Refine.Sepref.Iicf
