import Lax13Proofs.Refine.Iicf.Intf.PrioBag
import Lax13Proofs.Refine.Iicf.Intf.List
import Mathlib.Data.List.GetD

/-!
# Abstract binary heaps on lists

Port of Sepreftime's `IICF_Abs_Heap.thy` at
`c1c987b45ec886d289ba215768182ac87b82f20d`.

This is the semantic/list layer.  It deliberately contains no IR commands,
heap assertions, allocation rules, or vector costs.  Isabelle's recursive
`RECT` swim and optimized sink programs are represented by explicit
fuel-bounded structural recursion.  Their public wrappers supply sufficient
fuel from the one-based position/list length and retain the exact internal
list result expected by downstream `Impl_Heap` synthesis.

Isabelle/HOL types are inhabited.  The explicit `[Inhabited α]` below is the
Lean counterpart needed to keep source `val_of` total outside its validity
precondition.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {α κ : Type}

abbrev AbsHeap (α : Type) := List α

/-! ## One-based tree navigation -/

def heapValid (h : AbsHeap α) (i : ℕ) : Prop := 0 < i ∧ i ≤ h.length

def heapValue [Inhabited α] (h : AbsHeap α) (i : ℕ) : α :=
  h.getD (i - 1) default

def heapParent (i : ℕ) : ℕ := i / 2
def heapLeft (i : ℕ) : ℕ := 2 * i
def heapRight (i : ℕ) : ℕ := 2 * i + 1

def heapHasParent (h : AbsHeap α) (i : ℕ) : Prop :=
  heapValid h (heapParent i)

def heapHasLeft (h : AbsHeap α) (i : ℕ) : Prop :=
  heapValid h (heapLeft i)

def heapHasRight (h : AbsHeap α) (i : ℕ) : Prop :=
  heapValid h (heapRight i)

@[simp] theorem heapValid_zero (h : AbsHeap α) : ¬ heapValid h 0 := by
  simp [heapValid]

@[simp] theorem heapParent_left (i : ℕ) : heapParent (heapLeft i) = i := by
  simp [heapParent, heapLeft]

@[simp] theorem heapParent_right (i : ℕ) : heapParent (heapRight i) = i := by
  simp [heapParent, heapRight, Nat.add_div]

theorem heap_parent_lt {i : ℕ} (hi : 0 < i) : heapParent i < i := by
  simp [heapParent]
  omega

theorem heap_parent_valid {h : AbsHeap α} {i : ℕ}
    (hi : heapValid h i) (hlarge : 1 < i) : heapValid h (heapParent i) := by
  rcases hi with ⟨hi0, hil⟩
  constructor
  · simp [heapParent]
    omega
  · have hp_le : heapParent i ≤ i := Nat.div_le_self i 2
    omega

theorem heap_right_implies_left {h : AbsHeap α} {i : ℕ}
    (hi : heapValid h i) (hr : heapHasRight h i) : heapHasLeft h i := by
  rcases hi with ⟨hi0, hil⟩
  rcases hr with ⟨hr0, hrl⟩
  constructor
  · simp [heapLeft]
    omega
  · simp [heapLeft, heapRight] at hrl ⊢
    omega

theorem heap_child_of_parent {h : AbsHeap α} {i : ℕ}
    (hp : heapHasParent h i) :
    heapLeft (heapParent i) = i ∨ heapRight (heapParent i) = i := by
  rcases hp with ⟨hp0, -⟩
  simp [heapParent, heapLeft, heapRight] at hp0 ⊢
  omega

theorem heapLeft_ne_self {i : ℕ} (hi : 0 < i) : heapLeft i ≠ i := by
  simp [heapLeft]
  omega

theorem heapRight_ne_self {i : ℕ} (hi : 0 < i) : heapRight i ≠ i := by
  simp [heapRight]
  omega

theorem heapLeft_ne_right (i : ℕ) : heapLeft i ≠ heapRight i := by
  simp [heapLeft, heapRight]

theorem heapHasParent_left {h : AbsHeap α} {i : ℕ}
    (hi : heapValid h i) : heapHasParent h (heapLeft i) := by
  simpa [heapHasParent] using hi

theorem heapHasParent_right {h : AbsHeap α} {i : ℕ}
    (hi : heapValid h i) : heapHasParent h (heapRight i) := by
  simpa [heapHasParent] using hi

/-! ## Heap property and root-minimum theorem -/

def heapInvariant [Inhabited α] [LinearOrder κ] (prio : α → κ)
    (h : AbsHeap α) : Prop :=
  ∀ i, heapValid h i → heapHasParent h i →
    prio (heapValue h (heapParent i)) ≤ prio (heapValue h i)

@[simp] theorem heapInvariant_nil [Inhabited α] [LinearOrder κ]
    (prio : α → κ) : heapInvariant prio [] := by
  intro i hi _
  simp [heapValid] at hi
  omega

theorem heap_root_min [Inhabited α] [LinearOrder κ] (prio : α → κ)
    {h : AbsHeap α} (hinv : heapInvariant prio h) {i : ℕ}
    (hi : heapValid h i) :
    prio (heapValue h 1) ≤ prio (heapValue h i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      by_cases hsmall : i ≤ 1
      · have hi1 : i = 1 := by
          rcases hi with ⟨hi0, -⟩
          omega
        subst i
        exact le_rfl
      · have hlarge : 1 < i := by omega
        have hpv := heap_parent_valid hi hlarge
        exact le_trans (ih (heapParent i) (heap_parent_lt hi.1) hpv)
          (hinv i hi hpv)

/-! ## Basic list updates -/

def heapUpdate (h : AbsHeap α) (i : ℕ) (v : α) : AbsHeap α :=
  listSet h (i - 1) v

def heapExchange (h : AbsHeap α) (i j : ℕ) : AbsHeap α :=
  listSwap h (i - 1) (j - 1)

def heapButlast (h : AbsHeap α) : AbsHeap α := listButlast h

def heapAppend (h : AbsHeap α) (v : α) : AbsHeap α := h ++ [v]

@[simp] theorem heapUpdate_length (h : AbsHeap α) (i : ℕ) (v : α) :
    (heapUpdate h i v).length = h.length := by
  simp [heapUpdate]

@[simp] theorem heapUpdate_valid (h : AbsHeap α) (i j : ℕ) (v : α) :
    heapValid (heapUpdate h i v) j ↔ heapValid h j := by
  simp [heapValid]

@[simp] theorem heapExchange_length (h : AbsHeap α) (i j : ℕ) :
    (heapExchange h i j).length = h.length := by
  simp only [heapExchange, listSwap]
  split <;> simp

@[simp] theorem heapExchange_valid (h : AbsHeap α) (i j k : ℕ) :
    heapValid (heapExchange h i j) k ↔ heapValid h k := by
  simp [heapValid]

@[simp] theorem heapAppend_length (h : AbsHeap α) (v : α) :
    (heapAppend h v).length = h.length + 1 := by
  simp [heapAppend]

@[simp] theorem heapAppend_valid (h : AbsHeap α) (v : α) (i : ℕ) :
    heapValid (heapAppend h v) i ↔ heapValid h i ∨ i = h.length + 1 := by
  simp [heapValid, heapAppend]
  omega

theorem listSet_getD_self (xs : List α) (i : ℕ) (v d : α)
    (hi : i < xs.length) : (listSet xs i v).getD i d = v := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [listSet, List.getD_cons_succ]
          exact ih i (by simpa using hi)

theorem listSet_getD_ne (xs : List α) (i : ℕ) (v d : α) (j : ℕ)
    (hj : j < xs.length) (hne : j ≠ i) :
    (listSet xs i v).getD j d = xs.getD j d := by
  induction xs generalizing i j with
  | nil => simp at hj
  | cons x xs ih =>
      cases i <;> cases j
      · contradiction
      · rfl
      · rfl
      · simp only [listSet, List.getD_cons_succ]
        apply ih
        · simpa using hj
        · omega

theorem listSet_bag [DecidableEq α] (xs : List α) (i : ℕ) (v d : α)
    (hi : i < xs.length) :
    (listSet xs i v : Multiset α) =
      v ::ₘ Multiset.erase (xs : Multiset α) (xs.getD i d) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp [listSet]
      | succ i =>
          simp only [listSet, List.getD_cons_succ]
          change x ::ₘ (listSet xs i v : Multiset α) =
            v ::ₘ Multiset.erase (x ::ₘ (xs : Multiset α)) (xs.getD i d)
          rw [ih i (by simpa using hi)]
          have hold : xs.getD i d ∈ (xs : Multiset α) := by
            have hii : i < xs.length := by simpa using hi
            let fi : Fin xs.length := ⟨i, hii⟩
            change xs.getD i d ∈ xs
            rw [List.getD_eq_get xs d fi]
            exact List.get_mem xs fi
          by_cases hxi : x = xs.getD i d
          · subst x
            rw [Multiset.erase_cons_head, Multiset.cons_swap,
              Multiset.cons_erase hold]
          · rw [Multiset.erase_cons_tail _ hxi]
            rw [Multiset.cons_swap x v]

theorem listAt?_eq_some_getD (xs : List α) (i : ℕ) (d : α)
    (hi : i < xs.length) : listAt? xs i = some (xs.getD i d) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [listAt?, List.getD_cons_succ]
          exact ih i (by simpa using hi)

@[simp] theorem heapUpdate_value_self [Inhabited α] (h : AbsHeap α)
    (i : ℕ) (v : α) (hi : heapValid h i) :
    heapValue (heapUpdate h i v) i = v := by
  have hidx : i - 1 < h.length := by
    rcases hi with ⟨hi0, hilen⟩
    omega
  exact listSet_getD_self h (i - 1) v default hidx

theorem heapUpdate_value_ne [Inhabited α] (h : AbsHeap α)
    (i : ℕ) (v : α) (hi : heapValid h i) {j : ℕ}
    (hj : heapValid h j) (hji : j ≠ i) :
    heapValue (heapUpdate h i v) j = heapValue h j := by
  have hjidx : j - 1 < h.length := by
    rcases hj with ⟨hj0, hjlen⟩
    omega
  have hidxne : j - 1 ≠ i - 1 := by
    rcases hj with ⟨hj0, -⟩
    intro heq
    rcases hi with ⟨hi0, -⟩
    omega
  exact listSet_getD_ne h (i - 1) v default (j - 1) hjidx hidxne

theorem heapUpdate_bag [Inhabited α] (h : AbsHeap α)
    (i : ℕ) (v : α) (hi : heapValid h i) :
    (heapUpdate h i v : Multiset α) =
      v ::ₘ msetErase (h : Multiset α) (heapValue h i) := by
  classical
  have hidx : i - 1 < h.length := by
    rcases hi with ⟨hi0, hilen⟩
    omega
  exact listSet_bag h (i - 1) v default hidx

theorem heapExchange_value [Inhabited α] (h : AbsHeap α) (i j k : ℕ)
    (hi : heapValid h i) (hj : heapValid h j) (hk : heapValid h k) :
    heapValue (heapExchange h i j) k =
      if k = i then heapValue h j
      else if k = j then heapValue h i
      else heapValue h k := by
  have hi0 : 0 < i := hi.1
  have hj0 : 0 < j := hj.1
  have hk0 : 0 < k := hk.1
  have hii : i - 1 < h.length := by rcases hi with ⟨hi0, hi⟩; omega
  have hjj : j - 1 < h.length := by rcases hj with ⟨hj0, hj⟩; omega
  have hkk : k - 1 < h.length := by rcases hk with ⟨hk0, hk⟩; omega
  have hai := listAt?_eq_some_getD h (i - 1) default hii
  have haj := listAt?_eq_some_getD h (j - 1) default hjj
  simp only [heapExchange, listSwap, hai, haj, heapValue]
  by_cases hki : k = i
  · subst k
    simp only [if_pos]
    by_cases hij : i = j
    · subst j
      exact listSet_getD_self (listSet h (i - 1) (h.getD (i - 1) default))
        (i - 1) (h.getD (i - 1) default) default (by simpa using hii)
    · calc
        (listSet (listSet h (i - 1) (h.getD (j - 1) default))
            (j - 1) (h.getD (i - 1) default)).getD (i - 1) default =
            (listSet h (i - 1) (h.getD (j - 1) default)).getD
              (i - 1) default :=
          listSet_getD_ne _ _ _ _ _ (by simpa using hii) (by omega)
        _ = h.getD (j - 1) default :=
          listSet_getD_self h (i - 1) (h.getD (j - 1) default) default hii
  · simp only [if_neg hki]
    by_cases hkj : k = j
    · subst k
      simp only [if_pos]
      exact listSet_getD_self (listSet h (i - 1) (h.getD (j - 1) default))
        (j - 1) (h.getD (i - 1) default) default (by simpa using hjj)
    · simp only [if_neg hkj]
      calc
        (listSet (listSet h (i - 1) (h.getD (j - 1) default))
            (j - 1) (h.getD (i - 1) default)).getD (k - 1) default =
            (listSet h (i - 1) (h.getD (j - 1) default)).getD
              (k - 1) default :=
          listSet_getD_ne _ _ _ _ _ (by simpa using hkk) (by omega)
        _ = h.getD (k - 1) default :=
          listSet_getD_ne h (i - 1) (h.getD (j - 1) default) default
            (k - 1) hkk (by omega)

theorem heapExchange_bag [Inhabited α] (h : AbsHeap α) (i j : ℕ)
    (hi : heapValid h i) (hj : heapValid h j) :
    (heapExchange h i j : Multiset α) = (h : Multiset α) := by
  classical
  have hii : i - 1 < h.length := by rcases hi with ⟨hi0, hi⟩; omega
  have hjj : j - 1 < h.length := by rcases hj with ⟨hj0, hj⟩; omega
  have hai := listAt?_eq_some_getD h (i - 1) default hii
  have haj := listAt?_eq_some_getD h (j - 1) default hjj
  simp only [heapExchange, listSwap, hai, haj]
  let h1 := listSet h (i - 1) (h.getD (j - 1) default)
  have h1len : h1.length = h.length := by simp [h1]
  have hj1 : j - 1 < h1.length := by simpa [h1len] using hjj
  have hjval : h1.getD (j - 1) default = h.getD (j - 1) default := by
    by_cases hij : i = j
    · subst j
      exact listSet_getD_self h (i - 1) (h.getD (i - 1) default) default hii
    · exact listSet_getD_ne h (i - 1) (h.getD (j - 1) default) default
        (j - 1) hjj (by rcases hi with ⟨hi0, -⟩; rcases hj with ⟨hj0, -⟩; omega)
  change (listSet h1 (j - 1) (h.getD (i - 1) default) : Multiset α) =
    (h : Multiset α)
  rw [listSet_bag h1 (j - 1) (h.getD (i - 1) default) default hj1, hjval]
  dsimp [h1]
  change h.getD (i - 1) default ::ₘ
      Multiset.erase (listSet h (i - 1) (h.getD (j - 1) default) : Multiset α)
        (h.getD (j - 1) default) = (h : Multiset α)
  have hb1 := listSet_bag h (i - 1) (h.getD (j - 1) default) default hii
  rw [hb1]
  rw [Multiset.erase_cons_head]
  apply Multiset.cons_erase
  change h.getD (i - 1) default ∈ h
  let fi : Fin h.length := ⟨i - 1, hii⟩
  rw [List.getD_eq_get h default fi]
  exact List.get_mem h fi

@[simp] theorem heapAppend_value_last [Inhabited α] (h : AbsHeap α) (v : α) :
    heapValue (heapAppend h v) (h.length + 1) = v := by
  simp [heapValue, heapAppend]

@[simp] theorem heapAppend_value_old [Inhabited α] (h : AbsHeap α) (v : α)
    {i : ℕ} (hi : heapValid h i) :
    heapValue (heapAppend h v) i = heapValue h i := by
  have hidx : i - 1 < h.length := by rcases hi with ⟨hi0, hi⟩; omega
  exact List.getD_append h [v] default (i - 1) hidx

@[simp] theorem heapButlast_append (h : AbsHeap α) (v : α) :
    heapButlast (heapAppend h v) = h := by
  simp [heapButlast, heapAppend, listButlast]

@[simp] theorem heapButlast_bag_append (h : AbsHeap α) (v : α) :
    (heapButlast (heapAppend h v) : Multiset α) = (h : Multiset α) := by
  simp

theorem heapButlast_eq_dropLast (h : AbsHeap α) :
    heapButlast h = h.dropLast := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h v _ =>
      simpa [heapAppend] using heapButlast_append h v

@[simp] theorem heapButlast_length (h : AbsHeap α) :
    (heapButlast h).length = h.length - 1 := by
  rw [heapButlast_eq_dropLast]
  simp

theorem heapButlast_valid_iff (h : AbsHeap α) (i : ℕ) :
    heapValid (heapButlast h) i ↔ heapValid h i ∧ i < h.length := by
  simp [heapValid]
  omega

theorem heapButlast_value [Inhabited α] (h : AbsHeap α) {i : ℕ}
    (hi : heapValid (heapButlast h) i) :
    heapValue (heapButlast h) i = heapValue h i := by
  have hne : h ≠ [] := by
    intro heq
    subst h
    simp [heapValid, heapButlast, listButlast] at hi
    omega
  have hdrop : heapValid h.dropLast i := by
    simpa [heapButlast_eq_dropLast] using hi
  have hv := heapAppend_value_old h.dropLast (h.getLast hne) hdrop
  rw [heapButlast_eq_dropLast]
  calc
    heapValue h.dropLast i =
        heapValue (heapAppend h.dropLast (h.getLast hne)) i := hv.symm
    _ = heapValue h i := by
      simpa [heapAppend] using congrArg (fun l => heapValue l i)
        (List.dropLast_append_getLast hne)

theorem heapButlast_bag [Inhabited α] (h : AbsHeap α) (hne : h ≠ []) :
    (heapButlast h : Multiset α) =
      msetErase (h : Multiset α) (heapValue h h.length) := by
  induction h using List.reverseRecOn with
  | nil => contradiction
  | append_singleton h v _ =>
      have hv := heapAppend_value_last h v
      rw [show (h ++ [v]).length = h.length + 1 by simp]
      rw [show heapValue (h ++ [v]) (h.length + 1) = v by
        simpa [heapAppend] using hv]
      rw [show (heapButlast (h ++ [v]) : Multiset α) = (h : Multiset α) by
        simpa [heapAppend] using heapButlast_bag_append h v]
      rw [show ((h ++ [v] : List α) : Multiset α) =
          v ::ₘ (h : Multiset α) by simp]
      simp [msetErase]

/-! ## Membership and minimum consequences -/

theorem heapValue_mem [Inhabited α] {h : AbsHeap α} {i : ℕ}
    (hi : heapValid h i) : heapValue h i ∈ h := by
  have hidx : i - 1 < h.length := by
    rcases hi with ⟨hi0, hilen⟩
    omega
  let fi : Fin h.length := ⟨i - 1, hidx⟩
  change h.getD (i - 1) default ∈ h
  rw [List.getD_eq_get h default fi]
  exact List.get_mem h fi

theorem heap_min_mem [Inhabited α] [LinearOrder κ] (prio : α → κ)
    {h : AbsHeap α} (hinv : heapInvariant prio h) {x : α} (hx : x ∈ h) :
    prio (heapValue h 1) ≤ prio x := by
  obtain ⟨fi, hget⟩ := List.get_of_mem hx
  have hi : heapValid h (fi.1 + 1) := by
    constructor <;> omega
  have hv : heapValue h (fi.1 + 1) = x := by
    change h.getD fi.1 default = x
    rw [List.getD_eq_get h default fi]
    exact hget
  simpa [hv] using heap_root_min prio hinv hi

/-! ## Swim, sink, and repair contracts -/

def heapChildrenGe [Inhabited α] [LinearOrder κ] (prio : α → κ)
    (h : AbsHeap α) (p : κ) (i : ℕ) : Prop :=
  (heapHasLeft h i → p ≤ prio (heapValue h (heapLeft i))) ∧
  (heapHasRight h i → p ≤ prio (heapValue h (heapRight i)))

def swimInvariant [Inhabited α] [LinearOrder κ] (prio : α → κ)
    (h : AbsHeap α) (i : ℕ) : Prop :=
  heapValid h i ∧
  (∀ j, heapValid h j → heapHasParent h j → j ≠ i →
    prio (heapValue h (heapParent j)) ≤ prio (heapValue h j)) ∧
  (heapHasParent h i → ∀ j, heapValid h j → heapHasParent h j →
    heapParent j = i →
    prio (heapValue h (heapParent i)) ≤ prio (heapValue h j))

def sinkInvariant [Inhabited α] [LinearOrder κ] (prio : α → κ)
    (h : AbsHeap α) (i : ℕ) : Prop :=
  heapValid h i ∧
  (∀ j, heapValid h j → j ≠ i →
    heapChildrenGe prio h (prio (heapValue h j)) j) ∧
  (heapHasParent h i →
    heapChildrenGe prio h (prio (heapValue h (heapParent i))) i)

theorem heapInvariant_childrenGe [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h)
    {i : ℕ} (hi : heapValid h i) :
    heapChildrenGe prio h (prio (heapValue h i)) i := by
  constructor
  · intro hl
    simpa using hinv (heapLeft i) hl (by simpa [heapHasParent])
  · intro hr
    simpa using hinv (heapRight i) hr (by simpa [heapHasParent])

theorem heapInvariant_swimInvariant [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h)
    {i : ℕ} (hi : heapValid h i) : swimInvariant prio h i := by
  refine ⟨hi, fun j hj hp _ => hinv j hj hp, ?_⟩
  intro hp j hj hjp hjpar
  exact le_trans (hinv i hi hp) (by simpa [hjpar] using hinv j hj hjp)

theorem heapInvariant_sinkInvariant [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h)
    {i : ℕ} (hi : heapValid h i) : sinkInvariant prio h i := by
  refine ⟨hi, fun j hj _ => heapInvariant_childrenGe prio hinv hj, ?_⟩
  intro hp
  constructor
  · intro hl
    exact le_trans (hinv i hi hp) (by simpa using hinv (heapLeft i) hl (by
      simpa [heapHasParent]))
  · intro hr
    exact le_trans (hinv i hi hp) (by simpa using hinv (heapRight i) hr (by
      simpa [heapHasParent]))

theorem swimInvariant_update_of_le [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h)
    {i : ℕ} (hi : heapValid h i) (v : α)
    (hle : prio v ≤ prio (heapValue h i)) :
    swimInvariant prio (heapUpdate h i v) i := by
  unfold swimInvariant
  refine ⟨by simpa, ?_, ?_⟩
  · intro j hj hjp hji
    have hj0 : heapValid h j := by simpa using hj
    have hjp0 : heapHasParent h j := by simpa [heapHasParent] using hjp
    rw [heapUpdate_value_ne h i v hi hj0 hji]
    by_cases hpji : heapParent j = i
    · rw [hpji, heapUpdate_value_self h i v hi]
      exact le_trans hle (by simpa [hpji] using hinv j hj0 hjp0)
    · rw [heapUpdate_value_ne h i v hi hjp0 hpji]
      exact hinv j hj0 hjp0
  · intro hp j hj hjp hjpar
    have hp0 : heapHasParent h i := by simpa [heapHasParent] using hp
    have hj0 : heapValid h j := by simpa using hj
    have hjp0 : heapHasParent h j := by simpa [heapHasParent] using hjp
    have hpine : heapParent i ≠ i := ne_of_lt (heap_parent_lt hi.1)
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hpine hjpar
    rw [heapUpdate_value_ne h i v hi hp0 hpine,
      heapUpdate_value_ne h i v hi hj0 hji]
    exact le_trans (hinv i hi hp0)
      (by simpa [hjpar] using hinv j hj0 hjp0)

theorem sinkInvariant_update_of_ge [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h)
    {i : ℕ} (hi : heapValid h i) (v : α)
    (hle : prio (heapValue h i) ≤ prio v) :
    sinkInvariant prio (heapUpdate h i v) i := by
  unfold sinkInvariant
  refine ⟨by simpa, ?_, ?_⟩
  · intro j hj hji
    have hj0 : heapValid h j := by simpa using hj
    constructor
    · intro hl
      have hl0 : heapValid h (heapLeft j) := by
        change heapValid (heapUpdate h i v) (heapLeft j) at hl
        exact (heapUpdate_valid h i (heapLeft j) v).mp hl
      have hedge : prio (heapValue h j) ≤
          prio (heapValue h (heapLeft j)) := by
        simpa using hinv (heapLeft j) hl0 (heapHasParent_left hj0)
      rw [heapUpdate_value_ne h i v hi hj0 hji]
      by_cases hli : heapLeft j = i
      · rw [hli, heapUpdate_value_self h i v hi]
        rw [hli] at hedge
        exact le_trans hedge hle
      · rw [heapUpdate_value_ne h i v hi hl0 hli]
        exact hedge
    · intro hr
      have hr0 : heapValid h (heapRight j) := by
        change heapValid (heapUpdate h i v) (heapRight j) at hr
        exact (heapUpdate_valid h i (heapRight j) v).mp hr
      have hedge : prio (heapValue h j) ≤
          prio (heapValue h (heapRight j)) := by
        simpa using hinv (heapRight j) hr0 (heapHasParent_right hj0)
      rw [heapUpdate_value_ne h i v hi hj0 hji]
      by_cases hri : heapRight j = i
      · rw [hri, heapUpdate_value_self h i v hi]
        rw [hri] at hedge
        exact le_trans hedge hle
      · rw [heapUpdate_value_ne h i v hi hr0 hri]
        exact hedge
  · intro hp
    have hp0 : heapHasParent h i := by simpa [heapHasParent] using hp
    have horig := (heapInvariant_sinkInvariant prio hinv hi).2.2 hp0
    have hpine : heapParent i ≠ i := ne_of_lt (heap_parent_lt hi.1)
    constructor
    · intro hl
      have hl0 : heapHasLeft h i := by simpa [heapHasLeft] using hl
      have hline : heapLeft i ≠ i := heapLeft_ne_self hi.1
      rw [heapUpdate_value_ne h i v hi hp0 hpine,
        heapUpdate_value_ne h i v hi hl0 hline]
      exact horig.1 hl0
    · intro hr
      have hr0 : heapHasRight h i := by simpa [heapHasRight] using hr
      have hrine : heapRight i ≠ i := heapRight_ne_self hi.1
      rw [heapUpdate_value_ne h i v hi hp0 hpine,
        heapUpdate_value_ne h i v hi hr0 hrine]
      exact horig.2 hr0

theorem heapChildrenGe_update_of_le [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h)
    {i : ℕ} (hi : heapValid h i) (v : α)
    (hle : prio v ≤ prio (heapValue h i)) :
    heapChildrenGe prio (heapUpdate h i v)
      (prio (heapValue (heapUpdate h i v) i)) i := by
  have horig := heapInvariant_childrenGe prio hinv hi
  rw [heapUpdate_value_self h i v hi]
  constructor
  · intro hl
    have hl0 : heapHasLeft h i := by
      change heapValid (heapUpdate h i v) (heapLeft i) at hl
      exact (heapUpdate_valid h i (heapLeft i) v).mp hl
    have hline : heapLeft i ≠ i := heapLeft_ne_self hi.1
    rw [heapUpdate_value_ne h i v hi hl0 hline]
    exact le_trans hle (horig.1 hl0)
  · intro hr
    have hr0 : heapHasRight h i := by
      change heapValid (heapUpdate h i v) (heapRight i) at hr
      exact (heapUpdate_valid h i (heapRight i) v).mp hr
    have hrine : heapRight i ≠ i := heapRight_ne_self hi.1
    rw [heapUpdate_value_ne h i v hi hr0 hrine]
    exact le_trans hle (horig.2 hr0)

theorem swimInvariant_exchange_parent [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} {i : ℕ}
    (hp : heapHasParent h i)
    (hbad : prio (heapValue h i) < prio (heapValue h (heapParent i)))
    (hinv : swimInvariant prio h i) :
    swimInvariant prio (heapExchange h i (heapParent i)) (heapParent i) := by
  unfold swimInvariant at hinv ⊢
  rcases hinv with ⟨hi, hall, hchildren⟩
  have hpv : heapValid h (heapParent i) := hp
  have hi0 : 0 < i := hi.1
  have hpi : heapParent i < i := heap_parent_lt hi0
  constructor
  · simpa using hpv
  constructor
  · intro j hj hjp hjne
    have hj0 : heapValid h j := (heapExchange_valid h i (heapParent i) j).mp hj
    have hjp0 : heapHasParent h j :=
      (heapExchange_valid h i (heapParent i) (heapParent j)).mp hjp
    rw [heapExchange_value h i (heapParent i) j hi hpv hj0,
      heapExchange_value h i (heapParent i) (heapParent j) hi hpv hjp0]
    by_cases hji : j = i
    · subst j
      simp only [if_pos]
      have hpne : heapParent i ≠ i := by omega
      simp [hpne]
      exact le_of_lt hbad
    · simp only [if_neg hji]
      by_cases hjpidx : j = heapParent i
      · exact False.elim (hjne hjpidx)
      · simp only [if_neg hjpidx]
        by_cases hpji : heapParent j = i
        · have hpne : heapParent i ≠ i := by omega
          simpa [hpji, hji, hjpidx, hpne] using hchildren hp j hj0 hjp0 hpji
        · simp only [if_neg hpji]
          by_cases hpjp : heapParent j = heapParent i
          · have hs := hall j hj0 hjp0 hji
            rw [hpjp] at hs
            simpa [hpjp, hji, hjpidx] using le_trans (le_of_lt hbad) hs
          · simp only [if_neg hpjp]
            exact hall j hj0 hjp0 hji
  · intro hpp j hj hjp hjpar
    have hj0 : heapValid h j := (heapExchange_valid h i (heapParent i) j).mp hj
    have hjp0 : heapHasParent h j :=
      (heapExchange_valid h i (heapParent i) (heapParent j)).mp hjp
    have hpp0 : heapValid h (heapParent (heapParent i)) :=
      (heapExchange_valid h i (heapParent i) (heapParent (heapParent i))).mp hpp
    rw [heapExchange_value h i (heapParent i) j hi hpv hj0,
      heapExchange_value h i (heapParent i) (heapParent (heapParent i)) hi hpv hpp0]
    have hpne : heapParent i ≠ i := by omega
    have hqplt : heapParent (heapParent i) < heapParent i := heap_parent_lt hpv.1
    have hppi : heapParent (heapParent i) ≠ i := by omega
    have hppp : heapParent (heapParent i) ≠ heapParent i :=
      ne_of_lt (heap_parent_lt hpv.1)
    have hqp : prio (heapValue h (heapParent (heapParent i))) ≤
        prio (heapValue h (heapParent i)) :=
      hall (heapParent i) hpv hpp0 hpne
    by_cases hji : j = i
    · subst j
      simpa [hpne, hppi, hppp] using hqp
    · have hjpidx : j ≠ heapParent i := by
        intro hjpidx
        subst j
        exact hppp hjpar
      simp [hji, hjpidx, hppi, hppp]
      have hs := hall j hj0 hjp0 hji
      rw [hjpar] at hs
      exact le_trans hqp hs

theorem sinkInvariant_exchange_child [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} {i j : ℕ}
    (hinv : sinkInvariant prio h i) (hj : heapValid h j)
    (hjpar : heapParent j = i)
    (hmin : heapChildrenGe prio h (prio (heapValue h j)) i)
    (hbad : prio (heapValue h j) < prio (heapValue h i)) :
    sinkInvariant prio (heapExchange h i j) j := by
  unfold sinkInvariant heapChildrenGe at hinv ⊢
  rcases hinv with ⟨hi, hall, hparent⟩
  have hjp : heapHasParent h j := by simpa [heapHasParent, hjpar] using hi
  have hijlt : i < j := by
    rw [← hjpar]
    exact heap_parent_lt hj.1
  have hji : j ≠ i := ne_of_gt hijlt
  have hexv (k : ℕ) (hk : heapValid h k) := heapExchange_value h i j k hi hj hk
  simp only [heapExchange_valid]
  constructor
  · exact hj
  constructor
  · intro k hk hkj
    constructor
    · intro hkl
      have hkl0 : heapValid h (heapLeft k) :=
        (heapExchange_valid h i j (heapLeft k)).mp hkl
      rw [hexv k hk, hexv (heapLeft k) hkl0]
      by_cases hki : k = i
      · subst k
        have hli : heapLeft i ≠ i := heapLeft_ne_self hi.1
        simp only [if_pos, if_neg hli]
        by_cases hlj : heapLeft i = j
        · simp only [hlj, if_pos]
          exact le_of_lt hbad
        · simp only [if_neg hlj]
          exact hmin.1 hkl0
      · simp only [if_neg hki, if_neg hkj]
        by_cases hlj : heapLeft k = j
        · simp only [hlj, if_pos]
          simp only [if_neg hji]
          have hedge := (hall k hk hki).1 hkl0
          rw [hlj] at hedge
          exact le_trans hedge (le_of_lt hbad)
        · simp only [if_neg hlj]
          by_cases hli : heapLeft k = i
          · simp only [hli, if_pos]
            have hparki : heapParent i = k := by
              rw [← hli, heapParent_left]
            have hpi : heapHasParent h i := by simpa [heapHasParent, hparki] using hk
            rcases heap_child_of_parent hjp with hjl | hjr
            · have hjl' : heapLeft i = j := by simpa [hjpar] using hjl
              simpa [hparki, hjl'] using (hparent hpi).1 (by
                simpa [heapHasLeft, hjl'] using hj)
            · have hjr' : heapRight i = j := by simpa [hjpar] using hjr
              simpa [hparki, hjr'] using (hparent hpi).2 (by
                simpa [heapHasRight, hjr'] using hj)
          · simp only [if_neg hli]
            exact (hall k hk hki).1 hkl0
    · intro hkr
      have hkr0 : heapValid h (heapRight k) :=
        (heapExchange_valid h i j (heapRight k)).mp hkr
      rw [hexv k hk, hexv (heapRight k) hkr0]
      by_cases hki : k = i
      · subst k
        have hri : heapRight i ≠ i := heapRight_ne_self hi.1
        simp only [if_pos, if_neg hri]
        by_cases hrj : heapRight i = j
        · simp only [hrj, if_pos]
          exact le_of_lt hbad
        · simp only [if_neg hrj]
          exact hmin.2 hkr0
      · simp only [if_neg hki, if_neg hkj]
        by_cases hrj : heapRight k = j
        · simp only [hrj, if_pos]
          simp only [if_neg hji]
          have hedge := (hall k hk hki).2 hkr0
          rw [hrj] at hedge
          exact le_trans hedge (le_of_lt hbad)
        · simp only [if_neg hrj]
          by_cases hri : heapRight k = i
          · simp only [hri, if_pos]
            have hparki : heapParent i = k := by
              rw [← hri, heapParent_right]
            have hpi : heapHasParent h i := by simpa [heapHasParent, hparki] using hk
            rcases heap_child_of_parent hjp with hjl | hjr
            · have hjl' : heapLeft i = j := by simpa [hjpar] using hjl
              simpa [hparki, hjl'] using (hparent hpi).1 (by
                simpa [heapHasLeft, hjl'] using hj)
            · have hjr' : heapRight i = j := by simpa [hjpar] using hjr
              simpa [hparki, hjr'] using (hparent hpi).2 (by
                simpa [heapHasRight, hjr'] using hj)
          · simp only [if_neg hri]
            exact (hall k hk hki).2 hkr0
  · intro hjp'
    constructor
    · intro hjl
      have hjl0 : heapValid h (heapLeft j) :=
        (heapExchange_valid h i j (heapLeft j)).mp hjl
      rw [hjpar, hexv i hi, hexv (heapLeft j) hjl0]
      have hlj : heapLeft j ≠ j := heapLeft_ne_self hj.1
      have hli : heapLeft j ≠ i := by simp [heapLeft]; omega
      simp [hlj, hli]
      exact (hall j hj hji).1 hjl0
    · intro hjr
      have hjr0 : heapValid h (heapRight j) :=
        (heapExchange_valid h i j (heapRight j)).mp hjr
      rw [hjpar, hexv i hi, hexv (heapRight j) hjr0]
      have hrj : heapRight j ≠ j := heapRight_ne_self hj.1
      have hri : heapRight j ≠ i := by simp [heapRight]; omega
      simp [hrj, hri]
      exact (hall j hj hji).2 hjr0

/-- Source `swim_op`, with structural fuel replacing `RECT`. -/
def heapSwimFuel [Inhabited α] [LinearOrder κ] (prio : α → κ) :
    ℕ → AbsHeap α → ℕ → AbsHeap α
  | 0, h, _ => h
  | fuel + 1, h, i =>
      if 0 < heapParent i ∧ heapParent i ≤ h.length then
        if prio (heapValue h (heapParent i)) ≤ prio (heapValue h i) then h
        else heapSwimFuel prio fuel (heapExchange h i (heapParent i))
          (heapParent i)
      else h

def heapSwim [Inhabited α] [LinearOrder κ] (prio : α → κ)
    (h : AbsHeap α) (i : ℕ) : AbsHeap α := heapSwimFuel prio i h i

/-- The smaller valid child selected by source `sink_op_opt`; ties go left. -/
def heapSinkChild? [Inhabited α] [LinearOrder κ] (prio : α → κ)
    (h : AbsHeap α) (i : ℕ) : Option ℕ :=
  if 0 < heapRight i ∧ heapRight i ≤ h.length then
    if prio (heapValue h (heapRight i)) < prio (heapValue h (heapLeft i)) then
      some (heapRight i)
    else some (heapLeft i)
  else if 0 < heapLeft i ∧ heapLeft i ≤ h.length then some (heapLeft i)
  else none

/-- Source optimized sink with structural fuel replacing `RECT`. -/
def heapSinkFuel [Inhabited α] [LinearOrder κ] (prio : α → κ) :
    ℕ → AbsHeap α → ℕ → AbsHeap α
  | 0, h, _ => h
  | fuel + 1, h, i =>
      match heapSinkChild? prio h i with
      | none => h
      | some j =>
          if prio (heapValue h j) < prio (heapValue h i) then
            heapSinkFuel prio fuel (heapExchange h i j) j
          else h

def heapSink [Inhabited α] [LinearOrder κ] (prio : α → κ)
    (h : AbsHeap α) (i : ℕ) : AbsHeap α :=
  heapSinkFuel prio (h.length + 1) h i

def heapRepair [Inhabited α] [LinearOrder κ] (prio : α → κ)
    (h : AbsHeap α) (i : ℕ) : AbsHeap α :=
  heapSwim prio (heapSink prio h i) i

theorem heapSinkChild?_some [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} {i j : ℕ} (hi : heapValid h i)
    (hc : heapSinkChild? prio h i = some j) :
    heapValid h j ∧ heapParent j = i ∧
      heapChildrenGe prio h (prio (heapValue h j)) i := by
  unfold heapSinkChild? at hc
  split at hc
  · rename_i hr
    have hl := heap_right_implies_left hi hr
    split at hc
    · rename_i hrl
      simp only [Option.some.injEq] at hc
      subst j
      refine ⟨hr, heapParent_right i, ?_⟩
      exact ⟨fun _ => le_of_lt hrl, fun _ => le_rfl⟩
    · rename_i hnot
      simp only [Option.some.injEq] at hc
      subst j
      refine ⟨hl, heapParent_left i, ?_⟩
      exact ⟨fun _ => le_rfl, fun _ => le_of_not_gt hnot⟩
  · rename_i hnright
    split at hc
    · rename_i hl
      simp only [Option.some.injEq] at hc
      subst j
      refine ⟨hl, heapParent_left i, ?_⟩
      exact ⟨fun _ => le_rfl, fun hr => False.elim (hnright hr)⟩
    · simp at hc

theorem heapSinkChild?_none [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} {i : ℕ}
    (hc : heapSinkChild? prio h i = none) :
    ¬ heapHasLeft h i ∧ ¬ heapHasRight h i := by
  unfold heapSinkChild? at hc
  split at hc
  · split at hc <;> simp at hc
  · rename_i hr
    split at hc
    · simp at hc
    · rename_i hl
      exact ⟨hl, hr⟩

/-- Source `sink_op_swim_rule`: a swim-only defect makes sink observationally
unchanged because the current value is already no greater than either child. -/
theorem heapSink_eq_of_childrenGe [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} {i : ℕ} (hi : heapValid h i)
    (hge : heapChildrenGe prio h (prio (heapValue h i)) i) :
    heapSink prio h i = h := by
  unfold heapSink
  rw [heapSinkFuel]
  cases hc : heapSinkChild? prio h i with
  | none => rfl
  | some j =>
      obtain ⟨hj, hjpar, -⟩ := heapSinkChild?_some prio hi hc
      have hjp : heapHasParent h j := by
        simpa [heapHasParent, hjpar] using hi
      have hle : prio (heapValue h i) ≤ prio (heapValue h j) := by
        rcases heap_child_of_parent hjp with hl | hr
        · have hl' : heapLeft i = j := by simpa [hjpar] using hl
          simpa [hl'] using hge.1 (by simpa [heapHasLeft, hl'] using hj)
        · have hr' : heapRight i = j := by simpa [hjpar] using hr
          simpa [hr'] using hge.2 (by simpa [heapHasRight, hr'] using hj)
      simp only
      rw [if_neg (not_lt_of_ge hle)]

theorem sinkInvariant_exit [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} {i : ℕ}
    (hinv : sinkInvariant prio h i)
    (hfit : heapChildrenGe prio h (prio (heapValue h i)) i) :
    heapInvariant prio h := by
  intro j hj hp
  have childAt (k : ℕ) (hk : heapValid h k) :
      heapChildrenGe prio h (prio (heapValue h k)) k := by
    by_cases hki : k = i
    · simpa [hki] using hfit
    · exact hinv.2.1 k hk hki
  rcases heap_child_of_parent hp with hl | hr
  · have hc := (childAt (heapParent j) hp).1
    have hleft : heapHasLeft h (heapParent j) := by
      rw [heapHasLeft, hl]
      exact hj
    simpa [hl] using hc hleft
  · have hc := (childAt (heapParent j) hp).2
    have hright : heapHasRight h (heapParent j) := by
      rw [heapHasRight, hr]
      exact hj
    simpa [hr] using hc hright

theorem heapSinkFuel_correct [Inhabited α] [LinearOrder κ] (prio : α → κ)
    {fuel : ℕ} {h : AbsHeap α} {i : ℕ}
    (hinv : sinkInvariant prio h i) (hfuel : h.length - i < fuel) :
    (heapSinkFuel prio fuel h i : Multiset α) = (h : Multiset α) ∧
      heapInvariant prio (heapSinkFuel prio fuel h i) ∧
      (heapSinkFuel prio fuel h i).length = h.length := by
  induction fuel generalizing h i with
  | zero => omega
  | succ fuel ih =>
      rw [heapSinkFuel]
      cases hc : heapSinkChild? prio h i with
      | none =>
          simp only []
          have hn := heapSinkChild?_none prio hc
          have hfit : heapChildrenGe prio h (prio (heapValue h i)) i :=
            ⟨fun hl => False.elim (hn.1 hl), fun hr => False.elim (hn.2 hr)⟩
          exact ⟨trivial, sinkInvariant_exit prio hinv hfit, trivial⟩
      | some j =>
          simp only []
          obtain ⟨hj, hjpar, hmin⟩ := heapSinkChild?_some prio hinv.1 hc
          by_cases hbad : prio (heapValue h j) < prio (heapValue h i)
          · simp only [if_pos hbad]
            have hnext := sinkInvariant_exchange_child prio hinv hj hjpar hmin hbad
            have hij : i < j := by
              rw [← hjpar]
              exact heap_parent_lt hj.1
            have hjle : j ≤ h.length := hj.2
            have hfuel' : h.length - j < fuel := by omega
            have hrec := ih hnext (by simpa using hfuel')
            refine ⟨hrec.1.trans ?_, hrec.2.1, hrec.2.2.trans ?_⟩
            · exact heapExchange_bag h i j hinv.1 hj
            · exact heapExchange_length h i j
          · simp only [if_neg hbad]
            have hijle : prio (heapValue h i) ≤ prio (heapValue h j) :=
              le_of_not_gt hbad
            have hfit : heapChildrenGe prio h (prio (heapValue h i)) i :=
              ⟨fun hl => le_trans hijle (hmin.1 hl),
                fun hr => le_trans hijle (hmin.2 hr)⟩
            exact ⟨trivial, sinkInvariant_exit prio hinv hfit, trivial⟩

theorem swimInvariant_exit_no_parent [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} {i : ℕ}
    (hinv : swimInvariant prio h i) (hp : ¬ heapHasParent h i) :
    heapInvariant prio h := by
  intro j hj hjp
  by_cases hji : j = i
  · subst j
    exact False.elim (hp hjp)
  · exact hinv.2.1 j hj hjp hji

theorem swimInvariant_exit_le [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} {i : ℕ}
    (hinv : swimInvariant prio h i)
    (hle : prio (heapValue h (heapParent i)) ≤ prio (heapValue h i)) :
    heapInvariant prio h := by
  intro j hj hjp
  by_cases hji : j = i
  · subst j
    exact hle
  · exact hinv.2.1 j hj hjp hji

theorem heapSwimFuel_correct [Inhabited α] [LinearOrder κ] (prio : α → κ)
    {fuel : ℕ} {h : AbsHeap α} {i : ℕ}
    (hinv : swimInvariant prio h i) (hfuel : i ≤ fuel) :
    (heapSwimFuel prio fuel h i : Multiset α) = (h : Multiset α) ∧
      heapInvariant prio (heapSwimFuel prio fuel h i) ∧
      (heapSwimFuel prio fuel h i).length = h.length := by
  induction fuel generalizing h i with
  | zero =>
      have hi0 := hinv.1.1
      omega
  | succ fuel ih =>
      rw [heapSwimFuel]
      by_cases hp : 0 < heapParent i ∧ heapParent i ≤ h.length
      · simp only [if_pos hp]
        by_cases hle : prio (heapValue h (heapParent i)) ≤ prio (heapValue h i)
        · simp only [if_pos hle]
          exact ⟨trivial, swimInvariant_exit_le prio hinv hle, trivial⟩
        · simp only [if_neg hle]
          have hbad : prio (heapValue h i) <
              prio (heapValue h (heapParent i)) := lt_of_not_ge hle
          have hp' : heapHasParent h i := hp
          have hnext := swimInvariant_exchange_parent prio hp' hbad hinv
          have hip : heapParent i < i := heap_parent_lt hinv.1.1
          have hfuel' : heapParent i ≤ fuel := by omega
          have hrec := ih hnext hfuel'
          refine ⟨hrec.1.trans ?_, hrec.2.1, hrec.2.2.trans ?_⟩
          · exact heapExchange_bag h i (heapParent i) hinv.1 hp'
          · exact heapExchange_length h i (heapParent i)
      · simp only [if_neg hp]
        exact ⟨trivial, swimInvariant_exit_no_parent prio hinv hp, trivial⟩

theorem heapSwim_correct [Inhabited α] [LinearOrder κ] (prio : α → κ)
    {h : AbsHeap α} {i : ℕ} (_hinv : swimInvariant prio h i) :
    (heapSwim prio h i : Multiset α) = (h : Multiset α) ∧
      heapInvariant prio (heapSwim prio h i) ∧
      (heapSwim prio h i).length = h.length := by
  exact heapSwimFuel_correct prio _hinv le_rfl

theorem heapSink_correct [Inhabited α] [LinearOrder κ] (prio : α → κ)
    {h : AbsHeap α} {i : ℕ} (_hinv : sinkInvariant prio h i) :
    (heapSink prio h i : Multiset α) = (h : Multiset α) ∧
      heapInvariant prio (heapSink prio h i) ∧
      (heapSink prio h i).length = h.length := by
  apply heapSinkFuel_correct prio _hinv
  omega

theorem heapRepair_invariant_correct [Inhabited α] [LinearOrder κ]
    (prio : α → κ)
    {h : AbsHeap α} {i : ℕ} (hinv : heapInvariant prio h)
    (hi : heapValid h i) :
    (heapRepair prio h i : Multiset α) = (h : Multiset α) ∧
      heapInvariant prio (heapRepair prio h i) ∧
      (heapRepair prio h i).length = h.length := by
  have hs := heapSink_correct prio (heapInvariant_sinkInvariant prio hinv hi)
  have hi' : heapValid (heapSink prio h i) i := by
    rw [heapValid, hs.2.2]
    exact hi
  have hw := heapSwim_correct prio
    (heapInvariant_swimInvariant prio hs.2.1 hi')
  unfold heapRepair
  exact ⟨hw.1.trans hs.1, hw.2.1, hw.2.2.trans hs.2.2⟩

/-- Source `repair_correct` for `change_key_op = update_op; repair_op`.
Replacing one valid cell may create either a swim defect or a sink defect;
the source repair order handles both while preserving exactly the updated
list's multiset and length. -/
theorem heapRepair_correct [Inhabited α] [LinearOrder κ] (prio : α → κ)
    {h : AbsHeap α} {i : ℕ} (hinv : heapInvariant prio h)
    (hi : heapValid h i) (v : α) :
    (heapRepair prio (heapUpdate h i v) i : Multiset α) =
        (heapUpdate h i v : Multiset α) ∧
      heapInvariant prio (heapRepair prio (heapUpdate h i v) i) ∧
      (heapRepair prio (heapUpdate h i v) i).length = h.length := by
  have hi' : heapValid (heapUpdate h i v) i := by simpa
  by_cases hle : prio v ≤ prio (heapValue h i)
  · have hswimInv := swimInvariant_update_of_le prio hinv hi v hle
    have hchildren := heapChildrenGe_update_of_le prio hinv hi v hle
    have hsink : heapSink prio (heapUpdate h i v) i = heapUpdate h i v :=
      heapSink_eq_of_childrenGe prio hi' hchildren
    have hs := heapSwim_correct prio hswimInv
    unfold heapRepair
    rw [hsink]
    exact ⟨hs.1, hs.2.1, hs.2.2.trans (heapUpdate_length h i v)⟩
  · have hge : prio (heapValue h i) ≤ prio v :=
      le_of_lt (lt_of_not_ge hle)
    have hs := heapSink_correct prio
      (sinkInvariant_update_of_ge prio hinv hi v hge)
    have hi'' : heapValid (heapSink prio (heapUpdate h i v) i) i := by
      rw [heapValid, hs.2.2]
      exact hi'
    have hw := heapSwim_correct prio
      (heapInvariant_swimInvariant prio hs.2.1 hi'')
    unfold heapRepair
    exact ⟨hw.1.trans hs.1, hw.2.1,
      hw.2.2.trans (hs.2.2.trans (heapUpdate_length h i v))⟩

theorem sinkInvariant_pop_init [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h)
    (hlen : 1 < h.length) :
    sinkInvariant prio
      (heapButlast (heapExchange h 1 h.length)) 1 := by
  let e := heapExchange h 1 h.length
  let moved := heapButlast e
  have hroot : heapValid h 1 := by
    simp [heapValid]
    omega
  have hlast : heapValid h h.length := by
    simp [heapValid]
    omega
  have validOld {k : ℕ} (hk : heapValid moved k) : heapValid h k := by
    have hke : heapValid e k := (heapButlast_valid_iff e k).mp hk |>.1
    simpa [e] using hke
  have oldValue {k : ℕ} (hk : heapValid moved k) (hkroot : k ≠ 1) :
      heapValue moved k = heapValue h k := by
    have hcut := (heapButlast_valid_iff e k).mp hk
    have hkh : heapValid h k := validOld hk
    have hklast : k ≠ h.length := by
      have hklt : k < e.length := hcut.2
      simp [e] at hklt
      omega
    rw [heapButlast_value e hk]
    dsimp [e]
    rw [heapExchange_value h 1 h.length k hroot hlast hkh]
    simp [hkroot, hklast]
  change sinkInvariant prio moved 1
  unfold sinkInvariant
  have hmroot : heapValid moved 1 := by
    simp [moved, e, heapValid]
    omega
  refine ⟨hmroot, ?_, ?_⟩
  · intro j hj hjroot
    have hjh : heapValid h j := validOld hj
    have hc := heapInvariant_childrenGe prio hinv hjh
    constructor
    · intro hl
      have hlh : heapValid h (heapLeft j) := validOld hl
      have hlroot : heapLeft j ≠ 1 := by
        rcases hj with ⟨hj0, -⟩
        simp [heapLeft]
      rw [oldValue hj hjroot, oldValue hl hlroot]
      exact hc.1 hlh
    · intro hr
      have hrh : heapValid h (heapRight j) := validOld hr
      have hrroot : heapRight j ≠ 1 := by
        rcases hj with ⟨hj0, -⟩
        simp [heapRight]
        omega
      rw [oldValue hj hjroot, oldValue hr hrroot]
      exact hc.2 hrh
  · intro hp
    simp [heapHasParent, heapParent, heapValid] at hp

theorem swimInvariant_append [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h) (v : α) :
    swimInvariant prio (heapAppend h v) (h.length + 1) := by
  unfold swimInvariant
  have hlast : heapValid (heapAppend h v) (h.length + 1) := by
    simp
  refine ⟨hlast, ?_, ?_⟩
  · intro j hj hjp hjne
    have hjold : heapValid h j := by
      rw [heapAppend_valid] at hj
      rcases hj with hj | hj
      · exact hj
      · exact False.elim (hjne hj)
    have hpold : heapHasParent h j := by
      change heapValid (heapAppend h v) (heapParent j) at hjp
      change heapValid h (heapParent j)
      rw [heapAppend_valid] at hjp
      rcases hjp with hp | hp
      · exact hp
      · have hp_le : heapParent j < j := heap_parent_lt hjold.1
        have hjleold : j ≤ h.length := hjold.2
        omega
    simpa [heapAppend_value_old h v hjold,
      heapAppend_value_old h v hpold] using hinv j hjold hpold
  · intro hp j hj hjp hjpar
    have hjle : j ≤ (heapAppend h v).length := hj.2
    have hlastlen : (heapAppend h v).length = h.length + 1 := by simp
    have hjgt : h.length + 1 < j := by
      rw [← hjpar]
      have hpj := heap_parent_lt hj.1
      simp [heapParent] at hpj ⊢
      omega
    omega

/-! ## Priority-heap operations -/

def heapEmpty (α : Type) : AbsHeap α := []

noncomputable def heapIsEmpty (h : AbsHeap α) : Bool := propBool (h = [])

def heapInsert [Inhabited α] [LinearOrder κ] (prio : α → κ) (v : α) (h : AbsHeap α) :
    AbsHeap α := heapSwim prio (heapAppend h v) (h.length + 1)

def heapPeekMin? (h : AbsHeap α) : Option α := h.head?

def heapPopMin? [Inhabited α] [LinearOrder κ] (prio : α → κ) (h : AbsHeap α) :
    Option (α × AbsHeap α) :=
  match h with
  | [] => none
  | x :: xs =>
      let moved := heapButlast (heapExchange (x :: xs) 1 (x :: xs).length)
      some (x, if moved = [] then [] else heapSink prio moved 1)

@[simp] theorem heapInsert_invariant [Inhabited α] [LinearOrder κ]
    (prio : α → κ) (v : α) (h : AbsHeap α)
    (hinv : heapInvariant prio h) :
    heapInvariant prio (heapInsert prio v h) := by
  exact (heapSwim_correct prio (swimInvariant_append prio
    (h := h) hinv v)).2.1

@[simp] theorem heapInsert_bag [Inhabited α] [LinearOrder κ] (prio : α → κ)
    (v : α) (h : AbsHeap α) (hinv : heapInvariant prio h) :
    (heapInsert prio v h : Multiset α) =
      v ::ₘ (h : Multiset α) := by
  have hs := heapSwim_correct prio (swimInvariant_append prio
    (h := h) hinv v)
  exact hs.1.trans (by simp [heapAppend])

@[simp] theorem heapIsEmpty_eq (h : AbsHeap α) :
    heapIsEmpty h = true ↔ (h : Multiset α) = 0 := by
  unfold heapIsEmpty propBool
  simp

theorem heapPeekMin?_correct [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h)
    (hne : h ≠ []) :
    ∃ x, heapPeekMin? h = some x ∧ x ∈ (h : Multiset α) ∧
      ∀ y ∈ (h : Multiset α), prio x ≤ prio y := by
  cases h with
  | nil => contradiction
  | cons x xs =>
      refine ⟨x, rfl, by simp, ?_⟩
      intro y hy
      simpa [heapValue] using heap_min_mem prio hinv (by simpa using hy)

theorem heapPopMin?_correct [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} (hinv : heapInvariant prio h)
    (hne : h ≠ []) :
    ∃ x h', heapPopMin? prio h = some (x, h') ∧
      heapInvariant prio h' ∧ x ∈ (h : Multiset α) ∧
      (h' : Multiset α) = msetErase (h : Multiset α) x ∧
      ∀ y ∈ (h : Multiset α), prio x ≤ prio y := by
  cases h with
  | nil => contradiction
  | cons x xs =>
      have hxmem : x ∈ ((x :: xs : List α) : Multiset α) := by simp
      have hmin : ∀ y ∈ ((x :: xs : List α) : Multiset α),
          prio x ≤ prio y := by
        intro y hy
        have hy' : y ∈ (x :: xs) := by simpa using hy
        simpa [heapValue] using heap_min_mem prio hinv hy'
      by_cases hxsnil : xs = []
      · subst xs
        refine ⟨x, [], ?_, heapInvariant_nil prio, by simp, ?_, hmin⟩
        · have hmoved : heapButlast (heapExchange [x] 1 [x].length) = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp
          have hmoved' : heapButlast (heapExchange [x] 1 1) = [] := by
            simpa using hmoved
          change some (x, if heapButlast (heapExchange [x] 1 1) = [] then []
              else heapSink prio (heapButlast (heapExchange [x] 1 1)) 1) =
            some (x, [])
          rw [if_pos hmoved']
        · simp [msetErase]
      · let h := x :: xs
        let moved := heapButlast (heapExchange h 1 h.length)
        have hxspos : 0 < xs.length := by
          have hxslen : xs.length ≠ 0 := by simpa using hxsnil
          omega
        have hlen : 1 < h.length := by
          simp [h]
          exact hxspos
        have hroot : heapValid h 1 := by
          constructor <;> omega
        have hlast : heapValid h h.length := by
          constructor <;> omega
        have hmovedlen : moved.length = xs.length := by
          simp [moved, h]
        have hmovedne : moved ≠ [] := by
          apply List.ne_nil_of_length_pos
          rw [hmovedlen]
          exact hxspos
        have hsinv : sinkInvariant prio moved 1 := by
          dsimp [moved]
          exact sinkInvariant_pop_init prio hinv hlen
        have hs := heapSink_correct prio hsinv
        have hexne : heapExchange h 1 h.length ≠ [] := by
          apply List.ne_nil_of_length_pos
          simp [h]
        have hexlast :
            heapValue (heapExchange h 1 h.length) h.length = x := by
          rw [heapExchange_value h 1 h.length h.length hroot hlast hlast]
          have hlenne : h.length ≠ 1 := by omega
          simp only [if_neg hlenne, if_pos]
          simp [h, heapValue]
        have hmovedbag : (moved : Multiset α) =
            msetErase (h : Multiset α) x := by
          have hb := heapButlast_bag (heapExchange h 1 h.length) hexne
          rw [heapExchange_length, hexlast,
            heapExchange_bag h 1 h.length hroot hlast] at hb
          exact hb
        refine ⟨x, heapSink prio moved 1, ?_, hs.2.1, hxmem, ?_, hmin⟩
        · change some (x, if moved = [] then [] else heapSink prio moved 1) =
              some (x, heapSink prio moved 1)
          rw [if_neg hmovedne]
        · exact hs.1.trans hmovedbag

/-! ## Multiset representation and semantic frefs -/

def absHeapRel [Inhabited α] [LinearOrder κ] (prio : α → κ) :
    Set (AbsHeap α × Multiset α) :=
  {p | heapInvariant prio p.1 ∧ (p.1 : Multiset α) = p.2}

@[simp] theorem mem_absHeapRel_iff [Inhabited α] [LinearOrder κ]
    (prio : α → κ) {h : AbsHeap α} {m : Multiset α} :
    (h, m) ∈ absHeapRel prio ↔
      heapInvariant prio h ∧ (h : Multiset α) = m := Iff.rfl

@[intf_of_rel] theorem absHeapRel_intf [Inhabited α] [LinearOrder κ]
    (prio : α → κ) : intfOfRel (absHeapRel prio) (MultisetI α) := trivial

theorem absHeapRel_singleValued [Inhabited α] [LinearOrder κ]
    (prio : α → κ) : SingleValued (absHeapRel prio) := by
  intro h m n hm hn
  exact hm.2.symm.trans hn.2

noncomputable def absHeapEmptyOp (α : Type) : NRest (AbsHeap α) ECost :=
  NRest.returnT (heapEmpty α)

noncomputable def absHeapIsEmptyOp (h : AbsHeap α) : NRest Bool ECost :=
  NRest.returnT (heapIsEmpty h)

noncomputable def absHeapInsertOp [Inhabited α] [LinearOrder κ] (prio : α → κ) (v : α)
    (h : AbsHeap α) : NRest (AbsHeap α) ECost :=
  NRest.returnT (heapInsert prio v h)

noncomputable def absHeapPeekMinOp (h : AbsHeap α) : NRest α ECost :=
  match h with
  | [] => NRest.fail
  | x :: _ => NRest.returnT x

noncomputable def absHeapPopMinOp [Inhabited α] [LinearOrder κ] (prio : α → κ) (h : AbsHeap α) :
    NRest (α × AbsHeap α) ECost :=
  match h with
  | [] => NRest.fail
  | x :: xs =>
      let moved := heapButlast (heapExchange (x :: xs) 1 (x :: xs).length)
      NRest.returnT (x, if moved = [] then [] else heapSink prio moved 1)

private theorem returnT_le_spec_zero {γ : Type} {x : γ} {P : γ → Prop}
    (hP : P x) :
    (NRest.returnT x : NRest γ ECost) ≤ NRest.spec P (fun _ => 0) := by
  rw [NRest.returnT, NRest.spec]
  refine NRest.rest_le_rest_iff.mpr fun y => ?_
  by_cases hy : y = x
  · subst y
    simp [hP]
  · simp [NRest.single_of_ne hy]

@[sepref_fref_thms] theorem absHeapEmptyOp_refines [Inhabited α]
    [LinearOrder κ] (prio : α → κ) :
    (absHeapEmptyOp α, op_mset_empty α) ∈
      NRest.nrestRel (absHeapRel prio) := by
  exact NRest.param_returnT ⟨heapInvariant_nil prio, rfl⟩

@[sepref_fref_thms] theorem absHeapIsEmptyOp_refines [Inhabited α]
    [LinearOrder κ] (prio : α → κ) :
    (absHeapIsEmptyOp, op_mset_is_empty α) ∈
      fref (fun _ : Multiset α => True) (absHeapRel prio)
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) := by
  intro h m _ hm
  change heapInvariant prio h ∧ (h : Multiset α) = m at hm
  unfold absHeapIsEmptyOp op_mset_is_empty
  apply NRest.param_returnT
  change heapIsEmpty h = propBool (msetIsEmpty m)
  apply propBool_congr
  apply propext
  change h = [] ↔ m = 0
  rw [← hm.2]
  simp

@[sepref_fref_thms] theorem absHeapInsertOp_refines [Inhabited α]
    [LinearOrder κ] (prio : α → κ) :
    (absHeapInsertOp prio, op_mset_insert α) ∈
      fref (fun _ : α => True) (Set.diagonal α)
        (fun _ => fref (fun _ : Multiset α => True) (absHeapRel prio)
          (fun _ => NRest.nrestRel (absHeapRel prio))) := by
  intro x y _ hxy h m _ hm
  change x = y at hxy
  subst y
  apply NRest.param_returnT
  refine ⟨heapInsert_invariant prio x h hm.1, ?_⟩
  rw [heapInsert_bag prio x h hm.1, hm.2]

@[sepref_fref_thms] theorem absHeapPeekMinOp_refines [Inhabited α]
    [LinearOrder κ] (prio : α → κ) :
    (absHeapPeekMinOp, op_prio_peek_min α κ prio) ∈
      fref (fun _ : Multiset α => True) (absHeapRel prio)
        (fun _ => NRest.nrestRel (Set.diagonal α)) := by
  intro h m _ hm
  change heapInvariant prio h ∧ (h : Multiset α) = m at hm
  cases h with
  | nil =>
      have hm0 : m = 0 := by simpa using hm.2.symm
      rw [fold_op_prio_peek_min]
      simp [absHeapPeekMinOp, prioPeekMin, hm0]
  | cons x xs =>
      have hmne : m ≠ 0 := by
        rw [← hm.2]
        simp
      have hpost : x ∈ m ∧ ∀ y ∈ m, prio x ≤ prio y := by
        constructor
        · rw [← hm.2]
          simp
        · intro y hy
          have hy' : y ∈ (x :: xs) := by
            rw [← hm.2] at hy
            simpa using hy
          simpa [heapValue] using heap_min_mem prio hm.1 hy'
      unfold absHeapPeekMinOp
      rw [fold_op_prio_peek_min]
      apply NRest.nrestRel_of_le
      refine (NRest.returnT_refine (R := Set.diagonal α) rfl).trans ?_
      apply NRest.concFun_mono
      simp only [prioPeekMin, NRest.assert_pos hmne, NRest.returnT_bindT]
      exact returnT_le_spec_zero hpost

@[sepref_fref_thms] theorem absHeapPopMinOp_refines [Inhabited α]
    [LinearOrder κ] (prio : α → κ) :
    (absHeapPopMinOp prio, op_prio_pop_min α κ prio) ∈
      fref (fun _ : Multiset α => True) (absHeapRel prio)
        (fun _ => NRest.nrestRel
          (Set.diagonal α ×ᵣ absHeapRel prio)) := by
  intro h m _ hm
  change heapInvariant prio h ∧ (h : Multiset α) = m at hm
  cases h with
  | nil =>
      have hm0 : m = 0 := by simpa using hm.2.symm
      rw [fold_op_prio_pop_min]
      simp [absHeapPopMinOp, prioPopMin, hm0]
  | cons x xs =>
      have hmne : m ≠ 0 := by
        rw [← hm.2]
        simp
      obtain ⟨x', h', hpop, h'inv, hx'mem, h'bag, hmin⟩ :=
        heapPopMin?_correct prio hm.1 (by simp)
      have hxx : x' = x := by
        have hpairs := Option.some.inj hpop
        exact (congrArg Prod.fst hpairs).symm
      subst x'
      have h'rel : (h', msetErase m x) ∈ absHeapRel prio := by
        constructor
        · exact h'inv
        · simpa [hm.2] using h'bag
      have hpost : x ∈ m ∧ msetErase m x = msetErase m x ∧
          ∀ y ∈ m, prio x ≤ prio y := by
        refine ⟨?_, rfl, ?_⟩
        · simpa [hm.2] using hx'mem
        · intro y hy
          apply hmin y
          simpa [hm.2] using hy
      have habs : absHeapPopMinOp prio (x :: xs) =
          NRest.returnT (x, h') := by
        unfold heapPopMin? at hpop
        simp only [Option.some.injEq] at hpop
        unfold absHeapPopMinOp
        change NRest.returnT
            (x, if heapButlast (heapExchange (x :: xs) 1 (x :: xs).length) = []
              then [] else heapSink prio
                (heapButlast (heapExchange (x :: xs) 1 (x :: xs).length)) 1) =
          NRest.returnT (x, h')
        rw [hpop]
      change (absHeapPopMinOp prio (x :: xs),
          op_prio_pop_min α κ prio m) ∈
        NRest.nrestRel (Set.diagonal α ×ᵣ absHeapRel prio)
      rw [habs]
      rw [fold_op_prio_pop_min]
      apply NRest.nrestRel_of_le
      refine (NRest.returnT_refine
        (R := Set.diagonal α ×ᵣ absHeapRel prio)
        (show ((x, h'), (x, msetErase m x)) ∈
          Set.diagonal α ×ᵣ absHeapRel prio from ⟨rfl, h'rel⟩)).trans ?_
      apply NRest.concFun_mono
      simp only [prioPopMin, NRest.assert_pos hmne, NRest.returnT_bindT]
      exact returnT_le_spec_zero hpost

/-! ## Source accounting, regression, and registration gates -/

#guard heapParent (heapLeft 17) = 17
#guard heapParent (heapRight 17) = 17
#guard heapSwim id [1, 3, 2] 3 = [1, 3, 2]
#guard heapSink id [4, 2, 3] 1 = [2, 4, 3]
#guard heapInsert id 2 [1, 4, 3, 5] = [1, 2, 3, 5, 4]
#guard heapPopMin? id [1, 4, 2, 5, 6, 3] = some (1, [2, 4, 3, 5, 6])
#guard heapRepair id (heapUpdate [1, 2, 3, 4, 5, 6, 7] 2 8) 2 =
  [1, 4, 3, 8, 5, 6, 7]
#guard heapRepair id (heapUpdate [1, 2, 3, 4, 5, 6, 7] 4 0) 4 =
  [0, 1, 3, 2, 5, 6, 7]

/- The source declarations are intentionally gated as one family.  The exact
source-shaped structural repair definitions account for both RECT loops and the
optimized sink equation; the five `absHeap*Op` definitions are semantic
NRest programs, never executable IR rules. -/
run_cmd do
  let env ← Lean.Elab.Command.liftCoreM Lean.getEnv
  for n in #[``heapValid, ``heapValue, ``heapParent, ``heapLeft, ``heapRight,
      ``heapInvariant, ``heap_root_min, ``heapUpdate, ``heapExchange,
      ``heapButlast, ``heapAppend, ``swimInvariant, ``heapSwim,
      ``heapSwim_correct, ``sinkInvariant, ``heapSink, ``heapSink_correct,
      ``heapRepair, ``heapRepair_correct, ``heapEmpty, ``heapIsEmpty,
      ``heapInsert, ``heapPopMin?, ``heapPeekMin?, ``absHeapRel,
      ``absHeapEmptyOp_refines, ``absHeapIsEmptyOp_refines,
      ``absHeapInsertOp_refines, ``absHeapPopMinOp_refines,
      ``absHeapPeekMinOp_refines] do
    unless env.contains n do
      throwError "abstract-heap source gate: missing declaration {n}"

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``absHeapEmptyOp_refines, ``absHeapIsEmptyOp_refines,
      ``absHeapInsertOp_refines, ``absHeapPopMinOp_refines,
      ``absHeapPeekMinOp_refines] do
    unless rules.contains n do
      throwError "abstract-heap fref gate: missing rule {n}"

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.heap_root_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms heap_root_min

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.heapRepair_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms heapRepair_correct

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.absHeapPopMinOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms absHeapPopMinOp_refines

end Lax13Proofs.Refine.Sepref.Iicf
