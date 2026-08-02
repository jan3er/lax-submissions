import Lax13Proofs.Refine.Iicf.Impl.AbsHeap
import Lax13Proofs.Refine.Iicf.Intf.PrioMap

/-!
# Abstract heap maps

Semantic port of Sepreftime's `IICF_Abs_Heapmap.thy` at
`maxhaslbeck/Sepreftime@c1c987b45ec886d289ba215768182ac87b82f20d`.
A heap map is the source pair of a
distinct, one-based heap of keys and a partial map from those keys to values.
This file is deliberately independent of imperative arrays, separation
assertions, IR commands, and cost models.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {K V P : Type}

abbrev AbsHeapmap (K V : Type) := List K × (K → Option V)

def heapmapKeys (hm : AbsHeapmap K V) : List K := hm.1
def heapmapMap (hm : AbsHeapmap K V) : K → Option V := hm.2

def heapmapLookupD [Inhabited V] (hm : AbsHeapmap K V) (k : K) : V :=
  (heapmapMap hm k).getD default

def heapmapHeapView [Inhabited V] (hm : AbsHeapmap K V) : AbsHeap V :=
  (heapmapKeys hm).map (heapmapLookupD hm)

def hmKeyPrio [Inhabited V] (prio : V → P)
    (hm : AbsHeapmap K V) : K → P :=
  fun k => prio (heapmapLookupD hm k)

def heapmapPriorityView [Inhabited V] (prio : V → P)
    (hm : AbsHeapmap K V) : AbsHeap P :=
  (heapmapKeys hm).map (hmKeyPrio prio hm)

def heapmapStructInv (hm : AbsHeapmap K V) : Prop :=
  (heapmapKeys hm).Nodup ∧ mapDom (heapmapMap hm) = {k | k ∈ heapmapKeys hm}

def heapmapInvariant [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    (hm : AbsHeapmap K V) : Prop :=
  heapmapStructInv hm ∧ heapInvariant id (heapmapPriorityView prio hm)

def heapmapHeapRel [Inhabited V] :
    Set (AbsHeapmap K V × AbsHeap V) :=
  {p | heapmapStructInv p.1 ∧ heapmapHeapView p.1 = p.2}

def heapmapRel [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P) :
    Set (AbsHeapmap K V × (K → Option V)) :=
  {p | heapmapInvariant prio p.1 ∧ heapmapMap p.1 = p.2}

@[simp] theorem mem_heapmapHeapRel_iff [Inhabited V]
    {hm : AbsHeapmap K V} {h : AbsHeap V} :
    (hm, h) ∈ heapmapHeapRel ↔
      heapmapStructInv hm ∧ heapmapHeapView hm = h := Iff.rfl

@[simp] theorem mem_heapmapRel_iff [Inhabited V] [Inhabited P] [LinearOrder P]
    (prio : V → P) {hm : AbsHeapmap K V} {m : K → Option V} :
    (hm, m) ∈ heapmapRel prio ↔
      heapmapInvariant prio hm ∧ heapmapMap hm = m := Iff.rfl

@[simp] theorem heapmapStructInv_empty :
    heapmapStructInv (([], mapEmpty) : AbsHeapmap K V) := by
  simp [heapmapStructInv, heapmapKeys, heapmapMap, mapDom, mapEmpty]

@[simp] theorem heapmapInvariant_empty [Inhabited V] [Inhabited P] [LinearOrder P]
    (prio : V → P) :
    heapmapInvariant prio (([], mapEmpty) : AbsHeapmap K V) := by
  constructor
  · exact heapmapStructInv_empty
  · change heapInvariant (id : P → P) []
    exact heapInvariant_nil (id : P → P)

/-! ## Exact indexed primitives -/

def hmLength (hm : AbsHeapmap K V) : ℕ := (heapmapKeys hm).length

def hmValid (hm : AbsHeapmap K V) (i : ℕ) : Prop :=
  0 < i ∧ i ≤ hmLength hm

def hmKeyOf [Inhabited K] (hm : AbsHeapmap K V) (i : ℕ) : K :=
  (heapmapKeys hm).getD (i - 1) default

def hmLookup (hm : AbsHeapmap K V) (k : K) : Option V := heapmapMap hm k

def hmValueOf [Inhabited K] [Inhabited V]
    (hm : AbsHeapmap K V) (i : ℕ) : V :=
  heapmapLookupD hm (hmKeyOf hm i)

def hmPrioOf [Inhabited K] [Inhabited V]
    (prio : V → P) (hm : AbsHeapmap K V) (i : ℕ) : P :=
  prio (hmValueOf hm i)

def hmExchange (hm : AbsHeapmap K V) (i j : ℕ) : AbsHeapmap K V :=
  (heapExchange (heapmapKeys hm) i j, heapmapMap hm)

noncomputable def hmIndex [DecidableEq K]
    (hm : AbsHeapmap K V) (k : K) : ℕ :=
  (heapmapKeys hm).idxOf k + 1

noncomputable def hmUpdateAt [Inhabited K]
    (hm : AbsHeapmap K V) (i : ℕ) (v : V) : AbsHeapmap K V :=
  (heapmapKeys hm, mapUpdate (heapmapMap hm) (hmKeyOf hm i) v)

noncomputable def hmButlast [Inhabited K]
    (hm : AbsHeapmap K V) : AbsHeapmap K V :=
  (heapButlast (heapmapKeys hm),
    mapDelete (heapmapMap hm) (hmKeyOf hm (hmLength hm)))

noncomputable def hmAppend (hm : AbsHeapmap K V) (k : K) (v : V) :
    AbsHeapmap K V :=
  (heapAppend (heapmapKeys hm) k, mapUpdate (heapmapMap hm) k v)

@[simp] theorem hmLength_exchange (hm : AbsHeapmap K V) (i j : ℕ) :
    hmLength (hmExchange hm i j) = hmLength hm := by
  simp [hmLength, hmExchange, heapmapKeys]

@[simp] theorem hmValid_exchange (hm : AbsHeapmap K V) (i j : ℕ) :
    hmValid (hmExchange hm i j) = hmValid hm := by
  funext k
  simp [hmValid]

@[simp] theorem heapmapMap_exchange (hm : AbsHeapmap K V) (i j : ℕ) :
    heapmapMap (hmExchange hm i j) = heapmapMap hm := rfl

theorem hmKeyOf_exchange [Inhabited K] (hm : AbsHeapmap K V)
    {i j k : ℕ} (hi : hmValid hm i) (hj : hmValid hm j)
    (hk : hmValid hm k) :
    hmKeyOf (hmExchange hm i j) k =
      if k = i then hmKeyOf hm j
      else if k = j then hmKeyOf hm i else hmKeyOf hm k := by
  exact heapExchange_value (heapmapKeys hm) i j k hi hj hk

theorem hmIndex_valid [DecidableEq K] [Inhabited K]
    {hm : AbsHeapmap K V} {k : K}
    (hstruct : heapmapStructInv hm) (hk : heapmapMap hm k ≠ none) :
    hmValid hm (hmIndex hm k) := by
  have hmem : k ∈ heapmapKeys hm := by
    have : k ∈ mapDom (heapmapMap hm) := hk
    rw [hstruct.2] at this
    exact this
  simp [hmValid, hmLength, hmIndex, List.idxOf_lt_length_iff.mpr hmem]

theorem hmKeyOf_index [DecidableEq K] [Inhabited K]
    {hm : AbsHeapmap K V} {k : K}
    (hstruct : heapmapStructInv hm) (hk : heapmapMap hm k ≠ none) :
    hmKeyOf hm (hmIndex hm k) = k := by
  have hmem : k ∈ heapmapKeys hm := by
    have : k ∈ mapDom (heapmapMap hm) := hk
    rw [hstruct.2] at this
    exact this
  simp [hmKeyOf, hmIndex, List.getD_eq_getElem?_getD, hmem]

/-! ## Mapping and permutation support for heap motion -/

theorem listAt?_map (f : K → V) (xs : List K) (i : ℕ) :
    listAt? (xs.map f) i = (listAt? xs i).map f := by
  induction xs generalizing i with
  | nil => simp [listAt?]
  | cons x xs ih => cases i <;> simp [listAt?, ih]

theorem listSet_map (f : K → V) (xs : List K) (i : ℕ) (x : K) :
    listSet (xs.map f) i (f x) = (listSet xs i x).map f := by
  induction xs generalizing i with
  | nil => simp [listSet]
  | cons a xs ih => cases i <;> simp [listSet, ih]

theorem listSwap_map (f : K → V) (xs : List K) (i j : ℕ) :
    listSwap (xs.map f) i j = (listSwap xs i j).map f := by
  rw [listSwap, listAt?_map, listAt?_map]
  cases hi : listAt? xs i <;> cases hj : listAt? xs j <;>
    simp [listSwap, hi, hj, listSet_map]

theorem heapExchange_map (f : K → V) (xs : List K) (i j : ℕ) :
    heapExchange (xs.map f) i j = (heapExchange xs i j).map f := by
  simp [heapExchange, listSwap_map]

theorem heapValue_map_of_valid [Inhabited K] [Inhabited V]
    (f : K → V) {xs : List K} {i : ℕ} (hi : heapValid xs i) :
    heapValue (xs.map f) i = f (heapValue xs i) := by
  rcases hi with ⟨hi0, hile⟩
  have hlt : i - 1 < xs.length := by omega
  let fi : Fin xs.length := ⟨i - 1, hlt⟩
  rw [heapValue, heapValue]
  rw [List.getD_eq_get (xs.map f) default ⟨i - 1, by simpa using hlt⟩]
  rw [List.getD_eq_get xs default fi]
  simp [fi]

theorem heapSwimFuel_map [Inhabited K] [Inhabited V] [LinearOrder P]
    (f : K → V) (q : V → P) {fuel : ℕ} {xs : List K} {i : ℕ}
    (hi : heapValid xs i) :
    heapSwimFuel q fuel (xs.map f) i =
      (heapSwimFuel (q ∘ f) fuel xs i).map f := by
  induction fuel generalizing xs i with
  | zero => simp [heapSwimFuel]
  | succ fuel ih =>
      rw [heapSwimFuel, heapSwimFuel]
      by_cases hp : 0 < heapParent i ∧ heapParent i ≤ xs.length
      · have hpmap : 0 < heapParent i ∧ heapParent i ≤ (xs.map f).length := by
          simpa using hp
        simp only [if_pos hp, if_pos hpmap]
        rw [heapValue_map_of_valid f hp, heapValue_map_of_valid f hi]
        by_cases hle : q (f (heapValue xs (heapParent i))) ≤
            q (f (heapValue xs i))
        · simp [hle]
        · simp only [if_neg hle]
          rw [heapExchange_map]
          simp only [Function.comp_apply, if_neg hle]
          apply ih
          simpa using hp
      · have hpmap : ¬ (0 < heapParent i ∧
            heapParent i ≤ (xs.map f).length) := by simpa using hp
        simp [hp]

theorem heapSwim_map [Inhabited K] [Inhabited V] [LinearOrder P]
    (f : K → V) (q : V → P) {xs : List K} {i : ℕ}
    (hi : heapValid xs i) :
    heapSwim q (xs.map f) i = (heapSwim (q ∘ f) xs i).map f :=
  heapSwimFuel_map f q hi

theorem heapSinkChild?_map [Inhabited K] [Inhabited V] [LinearOrder P]
    (f : K → V) (q : V → P) {xs : List K} {i : ℕ}
    (hi : heapValid xs i) :
    heapSinkChild? q (xs.map f) i = heapSinkChild? (q ∘ f) xs i := by
  unfold heapSinkChild?
  by_cases hr : 0 < heapRight i ∧ heapRight i ≤ xs.length
  · have hrmap : 0 < heapRight i ∧ heapRight i ≤ (xs.map f).length := by
      simpa using hr
    have hl : heapValid xs (heapLeft i) := heap_right_implies_left hi hr
    simp only [if_pos hr, if_pos hrmap]
    rw [heapValue_map_of_valid f hr, heapValue_map_of_valid f hl]
    simp [Function.comp_apply]
  · have hrmap : ¬ (0 < heapRight i ∧
        heapRight i ≤ (xs.map f).length) := by simpa using hr
    simp only [if_neg hr, if_neg hrmap]
    by_cases hl : 0 < heapLeft i ∧ heapLeft i ≤ xs.length
    · simp [hl]
    · simp [hl]

theorem heapSinkFuel_map [Inhabited K] [Inhabited V] [LinearOrder P]
    (f : K → V) (q : V → P) {fuel : ℕ} {xs : List K} {i : ℕ}
    (hi : heapValid xs i) :
    heapSinkFuel q fuel (xs.map f) i =
      (heapSinkFuel (q ∘ f) fuel xs i).map f := by
  induction fuel generalizing xs i with
  | zero => simp [heapSinkFuel]
  | succ fuel ih =>
      rw [heapSinkFuel, heapSinkFuel, heapSinkChild?_map f q hi]
      cases hc : heapSinkChild? (q ∘ f) xs i with
      | none => rfl
      | some j =>
          have hj := (heapSinkChild?_some (q ∘ f) hi hc).1
          simp only
          rw [heapValue_map_of_valid f hj, heapValue_map_of_valid f hi]
          by_cases hlt : q (f (heapValue xs j)) < q (f (heapValue xs i))
          · simp only [if_pos hlt, Function.comp_apply]
            rw [heapExchange_map]
            apply ih
            simpa using hj
          · simp [hlt, Function.comp_apply]

theorem heapSink_map [Inhabited K] [Inhabited V] [LinearOrder P]
    (f : K → V) (q : V → P) {xs : List K} {i : ℕ}
    (hi : heapValid xs i) :
    heapSink q (xs.map f) i = (heapSink (q ∘ f) xs i).map f := by
  unfold heapSink
  rw [List.length_map]
  exact heapSinkFuel_map f q hi

@[simp] theorem heapSinkFuel_length [Inhabited K] [LinearOrder P]
    (q : K → P) (fuel : ℕ) (xs : List K) (i : ℕ) :
    (heapSinkFuel q fuel xs i).length = xs.length := by
  induction fuel generalizing xs i with
  | zero => rfl
  | succ fuel ih =>
      rw [heapSinkFuel]
      cases heapSinkChild? q xs i with
      | none => rfl
      | some j =>
          by_cases hlt : q (heapValue xs j) < q (heapValue xs i)
          · simp [hlt, ih]
          · simp [hlt]

@[simp] theorem heapSink_length [Inhabited K] [LinearOrder P]
    (q : K → P) (xs : List K) (i : ℕ) :
    (heapSink q xs i).length = xs.length := by
  simp [heapSink]

theorem heapRepair_map [Inhabited K] [Inhabited V] [LinearOrder P]
    (f : K → V) (q : V → P) {xs : List K} {i : ℕ}
    (hi : heapValid xs i) :
    heapRepair q (xs.map f) i = (heapRepair (q ∘ f) xs i).map f := by
  unfold heapRepair
  rw [heapSink_map f q hi]
  apply heapSwim_map
  simpa [heapValid] using hi

theorem heapSwimFuel_bag [Inhabited K] [LinearOrder P]
    (q : K → P) {fuel : ℕ} {xs : List K} {i : ℕ}
    (hi : heapValid xs i) :
    (heapSwimFuel q fuel xs i : Multiset K) = (xs : Multiset K) := by
  induction fuel generalizing xs i with
  | zero => rfl
  | succ fuel ih =>
      rw [heapSwimFuel]
      by_cases hp : 0 < heapParent i ∧ heapParent i ≤ xs.length
      · simp only [if_pos hp]
        by_cases hle : q (heapValue xs (heapParent i)) ≤ q (heapValue xs i)
        · simp [hle]
        · simp only [if_neg hle]
          exact (ih (by simpa using hp)).trans
            (heapExchange_bag xs i (heapParent i) hi hp)
      · simp [hp]

theorem heapSwim_bag [Inhabited K] [LinearOrder P]
    (q : K → P) {xs : List K} {i : ℕ} (hi : heapValid xs i) :
    (heapSwim q xs i : Multiset K) = (xs : Multiset K) :=
  heapSwimFuel_bag q hi

theorem heapSinkFuel_bag [Inhabited K] [LinearOrder P]
    (q : K → P) {fuel : ℕ} {xs : List K} {i : ℕ}
    (hi : heapValid xs i) :
    (heapSinkFuel q fuel xs i : Multiset K) = (xs : Multiset K) := by
  induction fuel generalizing xs i with
  | zero => rfl
  | succ fuel ih =>
      rw [heapSinkFuel]
      cases hc : heapSinkChild? q xs i with
      | none => rfl
      | some j =>
          have hj := (heapSinkChild?_some q hi hc).1
          by_cases hlt : q (heapValue xs j) < q (heapValue xs i)
          · simp only [if_pos hlt]
            exact (ih (by simpa using hj)).trans
              (heapExchange_bag xs i j hi hj)
          · simp [hlt]

theorem heapSink_bag [Inhabited K] [LinearOrder P]
    (q : K → P) {xs : List K} {i : ℕ} (hi : heapValid xs i) :
    (heapSink q xs i : Multiset K) = (xs : Multiset K) :=
  heapSinkFuel_bag q hi

theorem heapRepair_bag [Inhabited K] [LinearOrder P]
    (q : K → P) {xs : List K} {i : ℕ} (hi : heapValid xs i) :
    (heapRepair q xs i : Multiset K) = (xs : Multiset K) := by
  unfold heapRepair
  have hi' : heapValid (heapSink q xs i) i := by
    simpa [heapValid] using hi
  exact (heapSwim_bag q hi').trans (heapSink_bag q hi)

theorem heapButlast_exchange_eq_update [Inhabited K]
    {h : AbsHeap K} {i : ℕ} (hi : heapValid h i) (hin : i ≠ h.length) :
    heapButlast (heapExchange h i h.length) =
      heapUpdate (heapButlast h) i (heapValue h h.length) := by
  have hne : h ≠ [] := by
    intro he
    subst h
    simp [heapValid] at hi
    omega
  have hn : heapValid h h.length :=
    ⟨lt_of_lt_of_le hi.1 hi.2, le_rfl⟩
  apply List.ext_get
  · simp
  · intro t ht₁ ht₂
    let j := t + 1
    have hjcut : heapValid (heapButlast (heapExchange h i h.length)) j := by
      constructor
      · simp [j]
      · simpa [j] using ht₁
    have hjold : heapValid h j := by
      have hje :=
        (heapButlast_valid_iff (heapExchange h i h.length) j).mp hjcut
      simpa using hje.1
    have hjbase : heapValid (heapButlast h) j := by
      rw [heapButlast_valid_iff]
      exact ⟨hjold, by
        have : j ≤ h.length - 1 := by simpa [j] using ht₁
        omega⟩
    have hibase : heapValid (heapButlast h) i := by
      rw [heapButlast_valid_iff]
      exact ⟨hi, lt_of_le_of_ne hi.2 hin⟩
    have hv : heapValue (heapButlast (heapExchange h i h.length)) j =
        heapValue (heapUpdate (heapButlast h) i (heapValue h h.length)) j := by
      rw [heapButlast_value (heapExchange h i h.length) hjcut]
      by_cases hji : j = i
      · rw [hji]
        rw [heapExchange_value h i h.length i hi hn hi]
        simp
        rw [heapUpdate_value_self (heapButlast h) i (heapValue h h.length)]
        exact hibase
      · rw [heapExchange_value h i h.length j hi hn hjold]
        simp [hji]
        have hjn : j ≠ h.length := by
          have := (heapButlast_valid_iff h j).mp hjbase
          omega
        simp [hjn]
        rw [heapUpdate_value_ne (heapButlast h) i (heapValue h h.length)
          hibase hjbase hji]
        exact (heapButlast_value h hjbase).symm
    rw [← List.getD_eq_get _ default ⟨t, ht₁⟩,
      ← List.getD_eq_get _ default ⟨t, ht₂⟩]
    simpa [heapValue, j] using hv

theorem heapExchange_self [Inhabited K] (h : AbsHeap K) {i : ℕ}
    (hi : heapValid h i) : heapExchange h i i = h := by
  apply List.ext_get
  · simp
  · intro t ht₁ ht₂
    let j := t + 1
    have hj : heapValid h j := by
      constructor
      · simp [j]
      · simpa [j] using ht₂
    have hv : heapValue (heapExchange h i i) j = heapValue h j := by
      rw [heapExchange_value h i i j hi hi hj]
      by_cases hji : j = i
      · simpa [hji]
      · simp [hji]
    rw [← List.getD_eq_get _ default ⟨t, ht₁⟩,
      ← List.getD_eq_get _ default ⟨t, ht₂⟩]
    simpa [heapValue, j] using hv

theorem heapInvariant_butlast [Inhabited K] [LinearOrder P]
    (q : K → P) {h : AbsHeap K} (hinv : heapInvariant q h) :
    heapInvariant q (heapButlast h) := by
  intro i hi hp
  have hi' := (heapButlast_valid_iff h i).mp hi |>.1
  have hp' := (heapButlast_valid_iff h (heapParent i)).mp hp |>.1
  rw [heapButlast_value h hi, heapButlast_value h hp]
  exact hinv i hi' hp'

theorem mapPriority_updateAt [Inhabited K] [Inhabited V]
    (q : V → P) (m : K → Option V) {xs : List K} (hnd : xs.Nodup)
    {i : ℕ} (hi : i < xs.length) (v : V) :
    xs.map (fun k => q ((mapUpdate m (xs.getD i default) v k).getD default)) =
      listSet (xs.map (fun k => q ((m k).getD default))) i (q v) := by
  classical
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp only [List.getD_cons_zero, listSet, List.map_cons]
          rw [show (mapUpdate m x v x).getD default = v by simp [mapUpdate]]
          apply congrArg (List.cons (q v))
          apply List.map_congr_left
          intro y hy
          have hyx : y ≠ x :=
            fun h => (List.nodup_cons.mp hnd).1 (h ▸ hy)
          simp [mapUpdate, hyx]
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          have hmem : xs.getD i default ∈ xs := by
            let fi : Fin xs.length := ⟨i, hi'⟩
            rw [List.getD_eq_get xs default fi]
            exact List.get_mem xs fi
          have hx : x ≠ xs.getD i default :=
            fun h => (List.nodup_cons.mp hnd).1 (h ▸ hmem)
          simp only [List.getD_cons_succ, listSet, List.map_cons]
          rw [show (mapUpdate m (xs.getD i default) v x).getD default =
              (m x).getD default by
                rw [mapUpdate, Function.update_of_ne hx]]
          exact congrArg (List.cons (q ((m x).getD default)))
            (ih (List.nodup_cons.mp hnd).2 hi')

/-! ## Exact source-shaped heap motion -/

def hmSwim [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) (hm : AbsHeapmap K V) (i : ℕ) : AbsHeapmap K V :=
  (heapSwim (hmKeyPrio prio hm) (heapmapKeys hm) i, heapmapMap hm)

def hmSink [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) (hm : AbsHeapmap K V) (i : ℕ) : AbsHeapmap K V :=
  (heapSink (hmKeyPrio prio hm) (heapmapKeys hm) i, heapmapMap hm)

def hmRepair [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) (hm : AbsHeapmap K V) (i : ℕ) : AbsHeapmap K V :=
  (heapRepair (hmKeyPrio prio hm) (heapmapKeys hm) i, heapmapMap hm)

@[simp] theorem heapmapMap_swim [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) (hm : AbsHeapmap K V) (i : ℕ) :
    heapmapMap (hmSwim prio hm i) = heapmapMap hm := rfl

@[simp] theorem heapmapMap_sink [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) (hm : AbsHeapmap K V) (i : ℕ) :
    heapmapMap (hmSink prio hm i) = heapmapMap hm := rfl

@[simp] theorem heapmapMap_repair [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) (hm : AbsHeapmap K V) (i : ℕ) :
    heapmapMap (hmRepair prio hm i) = heapmapMap hm := rfl

theorem heapmapStructInv_of_motion {hm hm' : AbsHeapmap K V}
    (hinv : heapmapStructInv hm)
    (hmap : heapmapMap hm' = heapmapMap hm)
    (hbag : (heapmapKeys hm' : Multiset K) =
      (heapmapKeys hm : Multiset K)) :
    heapmapStructInv hm' := by
  have hp : (heapmapKeys hm').Perm (heapmapKeys hm) :=
    Multiset.coe_eq_coe.mp hbag
  constructor
  · exact hp.nodup_iff.mpr hinv.1
  · rw [hmap, hinv.2]
    apply Set.ext
    intro k
    exact hp.mem_iff.symm

theorem heapmapStructInv_swim [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) {hm : AbsHeapmap K V} {i : ℕ}
    (hinv : heapmapStructInv hm) (hi : hmValid hm i) :
    heapmapStructInv (hmSwim prio hm i) := by
  refine heapmapStructInv_of_motion (hm' := hmSwim prio hm i) hinv rfl ?_
  exact heapSwim_bag (hmKeyPrio prio hm) hi

theorem heapmapStructInv_sink [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) {hm : AbsHeapmap K V} {i : ℕ}
    (hinv : heapmapStructInv hm) (hi : hmValid hm i) :
    heapmapStructInv (hmSink prio hm i) := by
  refine heapmapStructInv_of_motion (hm' := hmSink prio hm i) hinv rfl ?_
  exact heapSink_bag (hmKeyPrio prio hm) hi

theorem heapmapStructInv_repair [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) {hm : AbsHeapmap K V} {i : ℕ}
    (hinv : heapmapStructInv hm) (hi : hmValid hm i) :
    heapmapStructInv (hmRepair prio hm i) := by
  refine heapmapStructInv_of_motion (hm' := hmRepair prio hm i) hinv rfl ?_
  exact heapRepair_bag (hmKeyPrio prio hm) hi

theorem heapmapPriorityView_swim [Inhabited K] [Inhabited V] [Inhabited P]
    [LinearOrder P] (prio : V → P) {hm : AbsHeapmap K V} {i : ℕ}
    (hi : hmValid hm i) :
    heapmapPriorityView prio (hmSwim prio hm i) =
      heapSwim id (heapmapPriorityView prio hm) i := by
  simpa [heapmapPriorityView, hmSwim, heapmapKeys, hmKeyPrio,
    heapmapLookupD, heapmapMap, Function.comp_def] using
    (heapSwim_map (hmKeyPrio prio hm) id hi).symm

theorem heapmapPriorityView_sink [Inhabited K] [Inhabited V] [Inhabited P]
    [LinearOrder P] (prio : V → P) {hm : AbsHeapmap K V} {i : ℕ}
    (hi : hmValid hm i) :
    heapmapPriorityView prio (hmSink prio hm i) =
      heapSink id (heapmapPriorityView prio hm) i := by
  simpa [heapmapPriorityView, hmSink, heapmapKeys, hmKeyPrio,
    heapmapLookupD, heapmapMap, Function.comp_def] using
    (heapSink_map (hmKeyPrio prio hm) id hi).symm

theorem heapmapPriorityView_repair [Inhabited K] [Inhabited V] [Inhabited P]
    [LinearOrder P] (prio : V → P) {hm : AbsHeapmap K V} {i : ℕ}
    (hi : hmValid hm i) :
    heapmapPriorityView prio (hmRepair prio hm i) =
      heapRepair id (heapmapPriorityView prio hm) i := by
  simpa [heapmapPriorityView, hmRepair, heapmapKeys, hmKeyPrio,
    heapmapLookupD, heapmapMap, Function.comp_def] using
    (heapRepair_map (hmKeyPrio prio hm) id hi).symm

theorem heapmapPriorityView_updateAt [Inhabited K] [Inhabited V]
    (prio : V → P) {hm : AbsHeapmap K V} {i : ℕ}
    (hstruct : heapmapStructInv hm) (hi : hmValid hm i) (v : V) :
    heapmapPriorityView prio (hmUpdateAt hm i v) =
      heapUpdate (heapmapPriorityView prio hm) i (prio v) := by
  rcases hi with ⟨hi0, hile⟩
  have hlt : i - 1 < (heapmapKeys hm).length := by
    simpa [hmLength] using (show i - 1 < hmLength hm by omega)
  simpa [heapmapPriorityView, hmUpdateAt, heapmapKeys, hmKeyPrio,
    heapmapLookupD, heapmapMap, hmKeyOf, heapUpdate] using
    mapPriority_updateAt prio (heapmapMap hm) hstruct.1 hlt v

theorem hmKeyOf_mem [Inhabited K] {hm : AbsHeapmap K V} {i : ℕ}
    (hi : hmValid hm i) : hmKeyOf hm i ∈ heapmapKeys hm := by
  rcases hi with ⟨hi0, hile⟩
  have hlt : i - 1 < (heapmapKeys hm).length := by
    simpa [hmLength] using (show i - 1 < hmLength hm by omega)
  let fi : Fin (heapmapKeys hm).length := ⟨i - 1, hlt⟩
  rw [hmKeyOf, List.getD_eq_get (heapmapKeys hm) default fi]
  exact List.get_mem _ fi

theorem heapmapStructInv_updateAt [Inhabited K]
    {hm : AbsHeapmap K V} {i : ℕ} (hstruct : heapmapStructInv hm)
    (hi : hmValid hm i) (v : V) :
    heapmapStructInv (hmUpdateAt hm i v) := by
  classical
  constructor
  · exact hstruct.1
  · have hdom : hmKeyOf hm i ∈ mapDom (heapmapMap hm) := by
      rw [hstruct.2]
      exact hmKeyOf_mem hi
    apply Set.ext
    intro k
    by_cases hk : k = hmKeyOf hm i
    · subst k
      simpa [hmUpdateAt, heapmapKeys, heapmapMap, mapDom, mapUpdate] using
        hmKeyOf_mem hi
    · simp [hmUpdateAt, heapmapKeys, heapmapMap, mapDom, mapUpdate,
        Function.update_of_ne hk]
      exact Set.ext_iff.mp hstruct.2 k

theorem heapmapStructInv_append [Inhabited K]
    {hm : AbsHeapmap K V} (hstruct : heapmapStructInv hm)
    {k : K} (hk : heapmapMap hm k = none) (v : V) :
    heapmapStructInv (hmAppend hm k v) := by
  classical
  have hnotmem : k ∉ heapmapKeys hm := by
    intro hmem
    have hkdom : k ∈ mapDom (heapmapMap hm) := by
      rw [hstruct.2]
      exact hmem
    exact hkdom hk
  constructor
  · simpa [hmAppend, heapmapKeys] using hstruct.1.append
      (List.nodup_singleton k) (by simp [hnotmem])
  · apply Set.ext
    intro x
    by_cases hx : x = k
    · subst x
      simp [hmAppend, heapmapKeys, heapmapMap, mapDom, mapUpdate, heapAppend]
    · simp [hmAppend, heapmapKeys, heapmapMap, mapDom, mapUpdate,
        Function.update_of_ne hx, heapAppend, hx]
      exact Set.ext_iff.mp hstruct.2 x

theorem hmKeyOf_length_eq_getLast [Inhabited K]
    {hm : AbsHeapmap K V} (hne : heapmapKeys hm ≠ []) :
    hmKeyOf hm (hmLength hm) = (heapmapKeys hm).getLast hne := by
  have hv := heapAppend_value_last (heapmapKeys hm).dropLast
    ((heapmapKeys hm).getLast hne)
  simp only [heapAppend] at hv
  rw [List.dropLast_append_getLast hne] at hv
  simpa [hmKeyOf, hmLength, heapValue] using hv

theorem heapmapStructInv_butlast [Inhabited K]
    {hm : AbsHeapmap K V} (hstruct : heapmapStructInv hm)
    (hne : heapmapKeys hm ≠ []) : heapmapStructInv (hmButlast hm) := by
  classical
  let last := (heapmapKeys hm).getLast hne
  have hlast : hmKeyOf hm (hmLength hm) = last :=
    hmKeyOf_length_eq_getLast hne
  have hdecomp : (heapmapKeys hm).dropLast ++ [last] = heapmapKeys hm :=
    List.dropLast_append_getLast hne
  have hndApp : ((heapmapKeys hm).dropLast ++ [last]).Nodup := by
    simpa [hdecomp] using hstruct.1
  have hdropNodup : (heapmapKeys hm).dropLast.Nodup := by
    exact (List.nodup_append.mp hndApp).1
  have hlastNot : last ∉ (heapmapKeys hm).dropLast := by
    have hdis := (List.nodup_append.mp hndApp).2.2
    intro hl
    exact hdis last hl last (by simp) rfl
  constructor
  · simpa [hmButlast, heapmapKeys, heapButlast_eq_dropLast] using hdropNodup
  · change mapDom (mapDelete (heapmapMap hm)
        (hmKeyOf hm (hmLength hm))) =
      {x | x ∈ heapButlast (heapmapKeys hm)}
    rw [hlast]
    rw [heapButlast_eq_dropLast]
    unfold mapDom
    apply Set.ext
    intro x
    by_cases hx : x = last
    · subst x
      change (mapDelete (heapmapMap hm) last last ≠ none) ↔
        last ∈ (heapmapKeys hm).dropLast
      simp [mapDelete, hlastNot]
    · change (mapDelete (heapmapMap hm) last x ≠ none) ↔
        x ∈ (heapmapKeys hm).dropLast
      rw [mapDelete, Function.update_of_ne hx]
      have hold := Set.ext_iff.mp hstruct.2 x
      change (heapmapMap hm x ≠ none) ↔ x ∈ heapmapKeys hm at hold
      rw [hold, ← hdecomp]
      simp [hx]

theorem heapmapPriorityView_exchange [Inhabited V]
    (prio : V → P) (hm : AbsHeapmap K V) (i j : ℕ) :
    heapmapPriorityView prio (hmExchange hm i j) =
      heapExchange (heapmapPriorityView prio hm) i j := by
  simpa [heapmapPriorityView, hmExchange, heapmapKeys, hmKeyPrio,
    heapmapLookupD, heapmapMap] using
    (heapExchange_map (hmKeyPrio prio hm) (heapmapKeys hm) i j).symm

theorem heapmapPriorityView_butlast [Inhabited K] [Inhabited V]
    (prio : V → P) {hm : AbsHeapmap K V} (hstruct : heapmapStructInv hm)
    (hne : heapmapKeys hm ≠ []) :
    heapmapPriorityView prio (hmButlast hm) =
      heapButlast (heapmapPriorityView prio hm) := by
  classical
  let last := (heapmapKeys hm).getLast hne
  have hlast : hmKeyOf hm (hmLength hm) = last :=
    hmKeyOf_length_eq_getLast hne
  have hdecomp : (heapmapKeys hm).dropLast ++ [last] = heapmapKeys hm :=
    List.dropLast_append_getLast hne
  have hndApp : ((heapmapKeys hm).dropLast ++ [last]).Nodup := by
    simpa [hdecomp] using hstruct.1
  have hlastNot : last ∉ (heapmapKeys hm).dropLast := by
    have hdis := (List.nodup_append.mp hndApp).2.2
    intro hl
    exact hdis last hl last (by simp) rfl
  unfold heapmapPriorityView hmButlast heapmapKeys hmKeyPrio
    heapmapLookupD heapmapMap
  rw [hlast, heapButlast_eq_dropLast, heapButlast_eq_dropLast]
  simp only
  rw [← List.map_dropLast]
  apply List.map_congr_left
  intro x hx
  have hxlast : x ≠ last := fun h => hlastNot (h ▸ hx)
  rw [mapDelete, Function.update_of_ne hxlast]

theorem heapmapPriorityView_append [Inhabited K] [Inhabited V]
    (prio : V → P) {hm : AbsHeapmap K V} (hstruct : heapmapStructInv hm)
    {k : K} (hk : heapmapMap hm k = none) (v : V) :
    heapmapPriorityView prio (hmAppend hm k v) =
      heapAppend (heapmapPriorityView prio hm) (prio v) := by
  classical
  have hnotmem : k ∉ heapmapKeys hm := by
    intro hmem
    have hkdom : k ∈ mapDom (heapmapMap hm) := by
      rw [hstruct.2]
      exact hmem
    exact hkdom hk
  simp only [heapmapPriorityView, hmAppend, heapmapKeys, hmKeyPrio,
    heapmapLookupD, heapmapMap, heapAppend, List.map_append, List.map_singleton]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro x hx
    have hxk : x ≠ k := fun h => hnotmem (h ▸ hx)
    simp [hmKeyPrio, heapmapLookupD, heapmapMap, mapUpdate,
      Function.update_of_ne hxk]
  · simp [mapUpdate]

/-! ## Priority-map operations -/

def hmEmpty (K V : Type) : AbsHeapmap K V := ([], mapEmpty)

def hmIsEmpty (hm : AbsHeapmap K V) : Bool := decide (hmLength hm = 0)

def hmContains (hm : AbsHeapmap K V) (k : K) : Bool :=
  decide (heapmapMap hm k ≠ none)

noncomputable def hmInsert [Inhabited K] [Inhabited V] [LinearOrder P]
    (prio : V → P) (k : K) (v : V) (hm : AbsHeapmap K V) :
    AbsHeapmap K V :=
  let h' := hmAppend hm k v
  hmSwim prio h' (hmLength h')

noncomputable def hmDecreaseKey [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    (k : K) (v : V) (hm : AbsHeapmap K V) : AbsHeapmap K V :=
  let i := hmIndex hm k
  hmSwim prio (hmUpdateAt hm i v) i

noncomputable def hmIncreaseKey [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    (k : K) (v : V) (hm : AbsHeapmap K V) : AbsHeapmap K V :=
  let i := hmIndex hm k
  hmSink prio (hmUpdateAt hm i v) i

noncomputable def hmChangeKey [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    (k : K) (v : V) (hm : AbsHeapmap K V) : AbsHeapmap K V :=
  let i := hmIndex hm k
  hmRepair prio (hmUpdateAt hm i v) i

noncomputable def hmSet [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    (k : K) (v : V) (hm : AbsHeapmap K V) : AbsHeapmap K V :=
  if heapmapMap hm k = none then hmInsert prio k v hm
  else hmChangeKey prio k v hm

noncomputable def hmRemove [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    (k : K) (hm : AbsHeapmap K V) : AbsHeapmap K V :=
  let i := hmIndex hm k
  let n := hmLength hm
  let moved := hmButlast (hmExchange hm i n)
  if i = n then moved else hmRepair prio moved i

noncomputable def hmPeekMin? [Inhabited K] [Inhabited V]
    (hm : AbsHeapmap K V) : Option (K × V) := do
  let k ← (heapmapKeys hm).head?
  let v ← heapmapMap hm k
  pure (k, v)

noncomputable def hmPopMin? [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    (hm : AbsHeapmap K V) : Option ((K × V) × AbsHeapmap K V) := do
  let kv ← hmPeekMin? hm
  pure (kv, hmRemove prio kv.1 hm)

/-! ## Invariant preservation -/

theorem heapmapInvariant_insert [Inhabited K] [Inhabited V] [Inhabited P]
    [LinearOrder P] (prio : V → P) {hm : AbsHeapmap K V}
    (hinv : heapmapInvariant prio hm) {k : K}
    (hk : heapmapMap hm k = none) (v : V) :
    heapmapInvariant prio (hmInsert prio k v hm) := by
  let appended := hmAppend hm k v
  have hstruct' : heapmapStructInv appended :=
    heapmapStructInv_append hinv.1 hk v
  have hview : heapmapPriorityView prio appended =
      heapAppend (heapmapPriorityView prio hm) (prio v) :=
    heapmapPriorityView_append prio hinv.1 hk v
  have hi : hmValid appended (hmLength appended) := by
    simp [hmValid, hmLength, appended, hmAppend, heapmapKeys]
  constructor
  · simpa [hmInsert, appended] using
      heapmapStructInv_swim prio hstruct' hi
  · rw [show heapmapPriorityView prio (hmInsert prio k v hm) =
        heapSwim id (heapAppend (heapmapPriorityView prio hm) (prio v))
          ((heapmapPriorityView prio hm).length + 1) by
      change heapmapPriorityView prio
          (hmSwim prio appended (hmLength appended)) = _
      rw [heapmapPriorityView_swim prio hi, hview]
      simp [hmLength, heapmapPriorityView, appended, hmAppend, heapmapKeys]]
    exact heapInsert_invariant id (prio v) (heapmapPriorityView prio hm) hinv.2

theorem heapmapInvariant_changeKey [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} (hinv : heapmapInvariant prio hm)
    {k : K} (hk : heapmapMap hm k ≠ none) (v : V) :
    heapmapInvariant prio (hmChangeKey prio k v hm) := by
  let i := hmIndex hm k
  let updated := hmUpdateAt hm i v
  have hi : hmValid hm i := hmIndex_valid hinv.1 hk
  have hiView : heapValid (heapmapPriorityView prio hm) i := by
    simpa [heapValid, hmValid, hmLength, heapmapPriorityView] using hi
  have hstruct' : heapmapStructInv updated :=
    heapmapStructInv_updateAt hinv.1 hi v
  have hi' : hmValid updated i := by simpa [updated, hmValid, hmLength]
  have hview : heapmapPriorityView prio updated =
      heapUpdate (heapmapPriorityView prio hm) i (prio v) :=
    heapmapPriorityView_updateAt prio hinv.1 hi v
  constructor
  · simpa [hmChangeKey, i, updated] using
      heapmapStructInv_repair prio hstruct' hi'
  · change heapInvariant id
      (heapmapPriorityView prio (hmRepair prio updated i))
    rw [heapmapPriorityView_repair prio hi', hview]
    exact (heapRepair_correct id hinv.2 hiView (prio v)).2.1

theorem heapmapPriorityCell [Inhabited K] [Inhabited V] [Inhabited P]
    (prio : V → P) {hm : AbsHeapmap K V} {i : ℕ} (hi : hmValid hm i) :
    heapValue (heapmapPriorityView prio hm) i =
      prio (heapmapLookupD hm (hmKeyOf hm i)) := by
  simpa [heapmapPriorityView, hmKeyPrio, heapmapLookupD, hmKeyOf,
    heapmapMap, heapmapKeys, heapValue] using
    heapValue_map_of_valid (hmKeyPrio prio hm) hi

theorem heapmapInvariant_decreaseKey [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} (hinv : heapmapInvariant prio hm)
    {k : K} {v : V} (hpre : decreaseKeyPre prio ((k, v), heapmapMap hm)) :
    heapmapInvariant prio (hmDecreaseKey prio k v hm) := by
  have hk : heapmapMap hm k ≠ none := hpre.1
  obtain ⟨old, hold⟩ : ∃ old, heapmapMap hm k = some old := by
    cases h : heapmapMap hm k with
    | none => exact False.elim (hk h)
    | some old => exact ⟨old, rfl⟩
  let i := hmIndex hm k
  let updated := hmUpdateAt hm i v
  have hi : hmValid hm i := hmIndex_valid hinv.1 hk
  have hiView : heapValid (heapmapPriorityView prio hm) i := by
    simpa [heapValid, hmValid, hmLength, heapmapPriorityView] using hi
  have hcell : heapValue (heapmapPriorityView prio hm) i = prio old := by
    rw [heapmapPriorityCell prio hi, hmKeyOf_index hinv.1 hk]
    simp [heapmapLookupD, hold]
  have hle : prio v ≤ heapValue (heapmapPriorityView prio hm) i := by
    rw [hcell]
    exact hpre.2 old hold
  have hstruct' : heapmapStructInv updated :=
    heapmapStructInv_updateAt hinv.1 hi v
  have hi' : hmValid updated i := by simpa [updated, hmValid, hmLength]
  have hview : heapmapPriorityView prio updated =
      heapUpdate (heapmapPriorityView prio hm) i (prio v) :=
    heapmapPriorityView_updateAt prio hinv.1 hi v
  constructor
  · simpa [hmDecreaseKey, i, updated] using
      heapmapStructInv_swim prio hstruct' hi'
  · change heapInvariant id
      (heapmapPriorityView prio (hmSwim prio updated i))
    rw [heapmapPriorityView_swim prio hi', hview]
    exact (heapSwim_correct id
      (swimInvariant_update_of_le id hinv.2 hiView (prio v) hle)).2.1

theorem heapmapInvariant_increaseKey [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} (hinv : heapmapInvariant prio hm)
    {k : K} {v : V} (hpre : increaseKeyPre prio ((k, v), heapmapMap hm)) :
    heapmapInvariant prio (hmIncreaseKey prio k v hm) := by
  have hk : heapmapMap hm k ≠ none := hpre.1
  obtain ⟨old, hold⟩ : ∃ old, heapmapMap hm k = some old := by
    cases h : heapmapMap hm k with
    | none => exact False.elim (hk h)
    | some old => exact ⟨old, rfl⟩
  let i := hmIndex hm k
  let updated := hmUpdateAt hm i v
  have hi : hmValid hm i := hmIndex_valid hinv.1 hk
  have hiView : heapValid (heapmapPriorityView prio hm) i := by
    simpa [heapValid, hmValid, hmLength, heapmapPriorityView] using hi
  have hcell : heapValue (heapmapPriorityView prio hm) i = prio old := by
    rw [heapmapPriorityCell prio hi, hmKeyOf_index hinv.1 hk]
    simp [heapmapLookupD, hold]
  have hge : heapValue (heapmapPriorityView prio hm) i ≤ prio v := by
    rw [hcell]
    exact hpre.2 old hold
  have hstruct' : heapmapStructInv updated :=
    heapmapStructInv_updateAt hinv.1 hi v
  have hi' : hmValid updated i := by simpa [updated, hmValid, hmLength]
  have hview : heapmapPriorityView prio updated =
      heapUpdate (heapmapPriorityView prio hm) i (prio v) :=
    heapmapPriorityView_updateAt prio hinv.1 hi v
  constructor
  · simpa [hmIncreaseKey, i, updated] using
      heapmapStructInv_sink prio hstruct' hi'
  · change heapInvariant id
      (heapmapPriorityView prio (hmSink prio updated i))
    rw [heapmapPriorityView_sink prio hi', hview]
    exact (heapSink_correct id
      (sinkInvariant_update_of_ge id hinv.2 hiView (prio v) hge)).2.1

theorem heapmapInvariant_set [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} (hinv : heapmapInvariant prio hm)
    (k : K) (v : V) : heapmapInvariant prio (hmSet prio k v hm) := by
  by_cases hk : heapmapMap hm k = none
  · simp [hmSet, hk, heapmapInvariant_insert prio hinv hk v]
  · simp [hmSet, hk, heapmapInvariant_changeKey prio hinv hk v]

theorem heapmapInvariant_remove [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} (hinv : heapmapInvariant prio hm)
    {k : K} (hk : heapmapMap hm k ≠ none) :
    heapmapInvariant prio (hmRemove prio k hm) := by
  let i := hmIndex hm k
  let n := hmLength hm
  let exchanged := hmExchange hm i n
  let moved := hmButlast exchanged
  have hi : hmValid hm i := hmIndex_valid hinv.1 hk
  have hn : hmValid hm n := by
    have hnpos : 0 < n := lt_of_lt_of_le hi.1 hi.2
    exact ⟨hnpos, le_rfl⟩
  have hne : heapmapKeys hm ≠ [] := by
    intro he
    simp [hmValid, hmLength, he] at hi
    omega
  have hstructEx : heapmapStructInv exchanged := by
    refine heapmapStructInv_of_motion (hm' := exchanged) hinv.1 rfl ?_
    exact heapExchange_bag (heapmapKeys hm) i n hi hn
  have hneEx : heapmapKeys exchanged ≠ [] := by
    intro he
    have hlen : hmLength exchanged = hmLength hm := by
      simp [exchanged]
    have hz : hmLength exchanged = 0 := by simp [hmLength, he]
    have hpos : 0 < hmLength hm := lt_of_lt_of_le hi.1 hi.2
    omega
  have hstructMoved : heapmapStructInv moved :=
    heapmapStructInv_butlast hstructEx hneEx
  have hviewMoved : heapmapPriorityView prio moved =
      heapButlast (heapExchange (heapmapPriorityView prio hm) i n) := by
    calc
      heapmapPriorityView prio moved =
          heapButlast (heapmapPriorityView prio exchanged) :=
        heapmapPriorityView_butlast prio hstructEx hneEx
      _ = heapButlast (heapExchange (heapmapPriorityView prio hm) i n) := by
        rw [show heapmapPriorityView prio exchanged =
          heapExchange (heapmapPriorityView prio hm) i n by
            exact heapmapPriorityView_exchange prio hm i n]
  change heapmapInvariant prio
    (if i = n then moved else hmRepair prio moved i)
  by_cases hin : i = n
  · rw [if_pos hin]
    have hexself : heapExchange (heapmapPriorityView prio hm) i n =
        heapmapPriorityView prio hm := by
      rw [← hin]
      apply heapExchange_self
      simpa [heapValid, hmValid, hmLength, heapmapPriorityView] using hi
    constructor
    · exact hstructMoved
    · rw [hviewMoved, hexself]
      exact heapInvariant_butlast id hinv.2
  · rw [if_neg hin]
    have hiView : heapValid (heapmapPriorityView prio hm) i := by
      simpa [heapValid, hmValid, hmLength, heapmapPriorityView] using hi
    have hiBase : heapValid
        (heapButlast (heapmapPriorityView prio hm)) i := by
      rw [heapButlast_valid_iff]
      exact ⟨hiView, by
        have hile : i ≤ n := hi.2
        have hnlen : n = (heapmapPriorityView prio hm).length := by
          simp [n, hmLength, heapmapPriorityView]
        omega⟩
    have hviewMoved' : heapmapPriorityView prio moved =
        heapUpdate (heapButlast (heapmapPriorityView prio hm)) i
          (heapValue (heapmapPriorityView prio hm) n) := by
      rw [hviewMoved]
      have hlen : n = (heapmapPriorityView prio hm).length := by
        simp [n, hmLength, heapmapPriorityView]
      have hinView : i ≠ (heapmapPriorityView prio hm).length := by
        simpa [← hlen] using hin
      rw [hlen]
      exact heapButlast_exchange_eq_update hiView hinView
    have hiMoved : hmValid moved i := by
      have hiMovedView : heapValid (heapmapPriorityView prio moved) i := by
        rw [hviewMoved']
        simpa using hiBase
      simpa [hmValid, hmLength, heapValid, heapmapPriorityView] using hiMovedView
    constructor
    · exact heapmapStructInv_repair prio hstructMoved hiMoved
    · change heapInvariant id
        (heapmapPriorityView prio (hmRepair prio moved i))
      rw [heapmapPriorityView_repair prio hiMoved, hviewMoved']
      exact (heapRepair_correct id (heapInvariant_butlast id hinv.2)
        hiBase (heapValue (heapmapPriorityView prio hm) n)).2.1

/-! ## Map-abstraction correctness -/

@[simp] theorem heapmapMap_append (hm : AbsHeapmap K V) (k : K) (v : V) :
    heapmapMap (hmAppend hm k v) = mapUpdate (heapmapMap hm) k v := rfl

@[simp] theorem heapmapMap_updateAt [Inhabited K]
    (hm : AbsHeapmap K V) (i : ℕ) (v : V) :
    heapmapMap (hmUpdateAt hm i v) =
      mapUpdate (heapmapMap hm) (hmKeyOf hm i) v := rfl

@[simp] theorem heapmapMap_insert [Inhabited K] [Inhabited V]
    [LinearOrder P] (prio : V → P) (hm : AbsHeapmap K V) (k : K) (v : V) :
    heapmapMap (hmInsert prio k v hm) = mapUpdate (heapmapMap hm) k v := by
  simp [hmInsert]

theorem heapmapMap_decreaseKey [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} {k : K} (v : V)
    (hstruct : heapmapStructInv hm) (hk : heapmapMap hm k ≠ none) :
    heapmapMap (hmDecreaseKey prio k v hm) =
      mapUpdate (heapmapMap hm) k v := by
  simp [hmDecreaseKey, hmKeyOf_index hstruct hk]

theorem heapmapMap_increaseKey [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} {k : K} (v : V)
    (hstruct : heapmapStructInv hm) (hk : heapmapMap hm k ≠ none) :
    heapmapMap (hmIncreaseKey prio k v hm) =
      mapUpdate (heapmapMap hm) k v := by
  simp [hmIncreaseKey, hmKeyOf_index hstruct hk]

theorem heapmapMap_changeKey [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} {k : K} (v : V)
    (hstruct : heapmapStructInv hm) (hk : heapmapMap hm k ≠ none) :
    heapmapMap (hmChangeKey prio k v hm) =
      mapUpdate (heapmapMap hm) k v := by
  simp [hmChangeKey, hmKeyOf_index hstruct hk]

theorem heapmapMap_set [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} (k : K) (v : V)
    (hstruct : heapmapStructInv hm) :
    heapmapMap (hmSet prio k v hm) = mapUpdate (heapmapMap hm) k v := by
  by_cases hk : heapmapMap hm k = none
  · simp [hmSet, hk]
  · simp [hmSet, hk, heapmapMap_changeKey prio v hstruct hk]

theorem heapmapMap_remove [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} {k : K} (hstruct : heapmapStructInv hm)
    (hk : heapmapMap hm k ≠ none) :
    heapmapMap (hmRemove prio k hm) = mapDelete (heapmapMap hm) k := by
  let i := hmIndex hm k
  let n := hmLength hm
  let exchanged := hmExchange hm i n
  let moved := hmButlast exchanged
  have hi : hmValid hm i := hmIndex_valid hstruct hk
  have hn : hmValid hm n := by
    exact ⟨lt_of_lt_of_le hi.1 hi.2, le_rfl⟩
  have hkeyi : hmKeyOf hm i = k := by
    exact hmKeyOf_index hstruct hk
  have hlast : hmKeyOf exchanged n = k := by
    rw [show hmKeyOf exchanged n =
      if n = i then hmKeyOf hm n
      else if n = n then hmKeyOf hm i else hmKeyOf hm n by
        exact hmKeyOf_exchange hm hi hn hn]
    by_cases hni : n = i
    · rw [if_pos hni, hni, hkeyi]
    · rw [if_neg hni]
      simp [hkeyi]
  have hmoved : heapmapMap moved = mapDelete (heapmapMap hm) k := by
    change mapDelete (heapmapMap exchanged)
      (hmKeyOf exchanged (hmLength exchanged)) = _
    have hlen : hmLength exchanged = n := by simp [exchanged, n]
    rw [hlen, hlast]
    rfl
  change heapmapMap (if i = n then moved else hmRepair prio moved i) = _
  by_cases hin : i = n
  · rw [if_pos hin, hmoved]
  · rw [if_neg hin, heapmapMap_repair, hmoved]

theorem hmLength_zero_iff_mapEmpty {hm : AbsHeapmap K V}
    (hstruct : heapmapStructInv hm) :
    hmLength hm = 0 ↔ heapmapMap hm = mapEmpty := by
  constructor
  · intro hlen
    have hkeys : heapmapKeys hm = [] := List.eq_nil_of_length_eq_zero hlen
    apply funext
    intro k
    by_cases hk : heapmapMap hm k = none
    · simpa [mapEmpty] using hk
    · have hkdom : k ∈ mapDom (heapmapMap hm) := hk
      rw [hstruct.2, hkeys] at hkdom
      simp at hkdom
  · intro hmap
    have hnone : ∀ k, k ∉ heapmapKeys hm := by
      intro k hk
      have : k ∈ mapDom (heapmapMap hm) := by
        rw [hstruct.2]
        exact hk
      rw [hmap] at this
      simpa [mapDom, mapEmpty] using this
    have : heapmapKeys hm = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr hnone
    simpa [hmLength, this]

theorem hmIsEmpty_eq (hm : AbsHeapmap K V) (hstruct : heapmapStructInv hm) :
    hmIsEmpty hm = propBool (heapmapMap hm = mapEmpty) := by
  unfold hmIsEmpty propBool
  exact decide_eq_decide.mpr (hmLength_zero_iff_mapEmpty hstruct)

theorem hmContains_eq (hm : AbsHeapmap K V) (k : K) :
    hmContains hm k = propBool (k ∈ mapDom (heapmapMap hm)) := by
  simp [hmContains, propBool, mapDom]

theorem hmPeekMin?_correct [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} (hinv : heapmapInvariant prio hm)
    (hne : heapmapMap hm ≠ mapEmpty) :
    ∃ k v, hmPeekMin? hm = some (k, v) ∧
      heapmapMap hm k = some v ∧
      ∀ k' v', heapmapMap hm k' = some v' → prio v ≤ prio v' := by
  have hkeys : heapmapKeys hm ≠ [] := by
    intro hnil
    apply hne
    apply funext
    intro k
    have hnot : k ∉ mapDom (heapmapMap hm) := by
      rw [hinv.1.2, hnil]
      simp
    simpa [mapEmpty, mapDom] using not_ne_iff.mp hnot
  cases hks : heapmapKeys hm with
  | nil => exact False.elim (hkeys hks)
  | cons k ks =>
      change hm.1 = k :: ks at hks
      have hks' : heapmapKeys hm = k :: ks := hks
      have hkdom : k ∈ mapDom (heapmapMap hm) := by
        rw [hinv.1.2, hks']
        simp
      obtain ⟨v, hv⟩ : ∃ v, heapmapMap hm k = some v := by
        cases h : heapmapMap hm k with
        | none => exact False.elim (hkdom h)
        | some v => exact ⟨v, rfl⟩
      change hm.2 k = some v at hv
      refine ⟨k, v, ?_, hv, ?_⟩
      · simp [hmPeekMin?, hks, hv, heapmapKeys, heapmapMap]
      · intro k' v' hv'
        have hi := hmIndex_valid hinv.1 (by rw [hv']; simp)
        have hiView : heapValid (heapmapPriorityView prio hm) (hmIndex hm k') := by
          simpa [heapValid, hmValid, hmLength, heapmapPriorityView] using hi
        have hroot : heapValue (heapmapPriorityView prio hm) 1 = prio v := by
          have hvalid : hmValid hm 1 := by
            simp [hmValid, hmLength, hks, heapmapKeys]
          rw [heapmapPriorityCell prio hvalid]
          simp [hmKeyOf, heapmapLookupD, hks, hv, heapmapKeys, heapmapMap]
        have hcell : heapValue (heapmapPriorityView prio hm) (hmIndex hm k') =
            prio v' := by
          rw [heapmapPriorityCell prio hi, hmKeyOf_index hinv.1 (by rw [hv']; simp)]
          simp [heapmapLookupD, hv']
        simpa [hroot, hcell] using heap_root_min id hinv.2 hiView

theorem hmPopMin?_correct [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    {hm : AbsHeapmap K V} (hinv : heapmapInvariant prio hm)
    (hne : heapmapMap hm ≠ mapEmpty) :
    ∃ k v hm', hmPopMin? prio hm = some ((k, v), hm') ∧
      heapmapInvariant prio hm' ∧ heapmapMap hm k = some v ∧
      heapmapMap hm' = mapDelete (heapmapMap hm) k ∧
      ∀ k' v', heapmapMap hm k' = some v' → prio v ≤ prio v' := by
  obtain ⟨k, v, hpeek, hv, hmin⟩ := hmPeekMin?_correct prio hinv hne
  refine ⟨k, v, hmRemove prio k hm, ?_,
    heapmapInvariant_remove prio hinv (by rw [hv]; simp), hv,
    heapmapMap_remove prio hinv.1 (by rw [hv]; simp), hmin⟩
  simp [hmPopMin?, hpeek]

/-! The source operations are abstract NRest programs.  These wrappers keep
that boundary: they expose assertions and semantic return values, but no IR
command or cost rule. -/

noncomputable def hmInsertOp [Inhabited K] [Inhabited V] [Inhabited P]
    [LinearOrder P]
    (prio : V → P) (k : K) (v : V) (hm : AbsHeapmap K V) :
    NRest (AbsHeapmap K V) ECost :=
  NRest.bindT (NRest.assert (heapmapInvariant prio hm ∧
    heapmapMap hm k = none)) fun _ => NRest.returnT (hmInsert prio k v hm)

noncomputable def hmChangeKeyOp [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    (k : K) (v : V) (hm : AbsHeapmap K V) : NRest (AbsHeapmap K V) ECost :=
  NRest.bindT (NRest.assert (heapmapInvariant prio hm ∧
    heapmapMap hm k ≠ none)) fun _ => NRest.returnT (hmChangeKey prio k v hm)

noncomputable def hmDecreaseKeyOp [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    (k : K) (v : V) (hm : AbsHeapmap K V) : NRest (AbsHeapmap K V) ECost :=
  NRest.bindT (NRest.assert (heapmapInvariant prio hm ∧
    decreaseKeyPre prio ((k, v), heapmapMap hm))) fun _ =>
    NRest.returnT (hmDecreaseKey prio k v hm)

noncomputable def hmIncreaseKeyOp [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    (k : K) (v : V) (hm : AbsHeapmap K V) : NRest (AbsHeapmap K V) ECost :=
  NRest.bindT (NRest.assert (heapmapInvariant prio hm ∧
    increaseKeyPre prio ((k, v), heapmapMap hm))) fun _ =>
    NRest.returnT (hmIncreaseKey prio k v hm)

noncomputable def hmRemoveOp [DecidableEq K] [Inhabited K]
    [Inhabited V] [Inhabited P] [LinearOrder P] (prio : V → P)
    (k : K) (hm : AbsHeapmap K V) : NRest (AbsHeapmap K V) ECost :=
  NRest.bindT (NRest.assert (heapmapInvariant prio hm ∧
    heapmapMap hm k ≠ none)) fun _ => NRest.returnT (hmRemove prio k hm)

noncomputable def hmPeekMinOp [Inhabited K] [Inhabited V]
    (hm : AbsHeapmap K V) : NRest (K × V) ECost :=
  match hmPeekMin? hm with
  | some kv => NRest.returnT kv
  | none => NRest.fail

noncomputable def hmPopMinOp [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    (hm : AbsHeapmap K V) : NRest ((K × V) × AbsHeapmap K V) ECost :=
  match hmPopMin? prio hm with
  | some p => NRest.returnT p
  | none => NRest.fail

noncomputable def hmEmptyOp (K V : Type) : NRest (AbsHeapmap K V) ECost :=
  NRest.returnT (hmEmpty K V)

noncomputable def hmIsEmptyOp (hm : AbsHeapmap K V) : NRest Bool ECost :=
  NRest.returnT (hmIsEmpty hm)

noncomputable def hmLookupOp (k : K) (hm : AbsHeapmap K V) : NRest (Option V) ECost :=
  NRest.returnT (hmLookup hm k)

noncomputable def hmContainsOp (k : K) (hm : AbsHeapmap K V) : NRest Bool ECost :=
  NRest.returnT (hmContains hm k)

noncomputable def hmSetOp [DecidableEq K] [Inhabited K]
    [Inhabited V] [LinearOrder P] (prio : V → P)
    (k : K) (v : V) (hm : AbsHeapmap K V) : NRest (AbsHeapmap K V) ECost :=
  NRest.returnT (hmSet prio k v hm)

/-! ## Priority-map refinement seams -/

@[intf_of_rel] theorem heapmapRel_intf [Inhabited V] [Inhabited P]
    [LinearOrder P] (prio : V → P) :
    intfOfRel (heapmapRel (K := K) prio) (MapI K V) := trivial

private theorem hmReturnT_le_spec_zero {A : Type} {x : A} {Q : A → Prop}
    (hQ : Q x) :
    (NRest.returnT x : NRest A ECost) ≤ NRest.spec Q (fun _ => 0) := by
  rw [NRest.returnT, NRest.spec]
  refine NRest.rest_le_rest_iff.mpr fun y => ?_
  by_cases hy : y = x
  · subst y
    simp [hQ]
  · simp [NRest.single_of_ne hy]

@[sepref_fref_thms] theorem hmEmptyOp_refines [Inhabited V] [Inhabited P]
    [LinearOrder P] (prio : V → P) :
    (hmEmptyOp K V, op_map_empty K V) ∈
      NRest.nrestRel (heapmapRel (K := K) prio) := by
  unfold hmEmptyOp op_map_empty
  apply NRest.param_returnT
  exact ⟨heapmapInvariant_empty prio, rfl⟩

@[sepref_fref_thms] theorem hmIsEmptyOp_refines [Inhabited V] [Inhabited P]
    [LinearOrder P] (prio : V → P) :
    (hmIsEmptyOp, op_map_is_empty K V) ∈
      heapmapRel prio →ᵣ NRest.nrestRel (Set.diagonal Bool) := by
  intro hm m hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  unfold hmIsEmptyOp op_map_is_empty
  apply NRest.param_returnT
  change hmIsEmpty hm = propBool (m = mapEmpty)
  rw [hmIsEmpty_eq hm hrel.1.1, hrel.2]

@[sepref_fref_thms] theorem hmLookupOp_refines [Inhabited V] [Inhabited P]
    [LinearOrder P] (prio : V → P) (k : K) :
    (hmLookupOp k, op_map_lookup K V k) ∈
      heapmapRel prio →ᵣ NRest.nrestRel (Set.diagonal (Option V)) := by
  intro hm m hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  unfold hmLookupOp op_map_lookup hmLookup
  apply NRest.param_returnT
  exact congrFun hrel.2 k

@[sepref_fref_thms] theorem hmContainsOp_refines [Inhabited V] [Inhabited P]
    [LinearOrder P] (prio : V → P) (k : K) :
    (hmContainsOp k, op_map_contains_key K V k) ∈
      heapmapRel prio →ᵣ NRest.nrestRel (Set.diagonal Bool) := by
  intro hm m hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  unfold hmContainsOp op_map_contains_key
  apply NRest.param_returnT
  change hmContains hm k = propBool (k ∈ mapDom m)
  rw [hmContains_eq, hrel.2]

@[sepref_fref_thms] theorem hmSetOp_refines [DecidableEq K]
    [Inhabited K] [Inhabited V] [Inhabited P] [LinearOrder P]
    (prio : V → P) (k : K) (v : V) :
    (hmSetOp prio k v, op_map_update K V k v) ∈
      heapmapRel prio →ᵣ NRest.nrestRel (heapmapRel prio) := by
  intro hm m hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  unfold hmSetOp op_map_update
  apply NRest.param_returnT
  exact ⟨heapmapInvariant_set prio hrel.1 k v,
    (heapmapMap_set prio k v hrel.1.1).trans
      (congrArg (fun m => mapUpdate m k v) hrel.2)⟩

@[sepref_fref_thms] theorem hmInsertOp_refines [Inhabited K] [Inhabited V]
    [Inhabited P] [LinearOrder P] (prio : V → P) (k : K) (v : V) :
    (hmInsertOp prio k v,
      fun m => op_map_update_new K V ((k, v), m)) ∈
      fref (fun m : K → Option V => k ∉ mapDom m) (heapmapRel prio)
        (fun _ => NRest.nrestRel (heapmapRel prio)) := by
  intro hm m hpre hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  have hnone : heapmapMap hm k = none := by
    by_cases h : heapmapMap hm k = none
    · exact h
    · exact False.elim (hpre (by simpa [hrel.2] using h))
  have hass : heapmapInvariant prio hm ∧ heapmapMap hm k = none :=
    ⟨hrel.1, hnone⟩
  dsimp only
  unfold hmInsertOp
  rw [NRest.assert_pos hass, NRest.returnT_bindT]
  unfold op_map_update_new
  apply NRest.param_returnT
  exact ⟨heapmapInvariant_insert prio hrel.1 hnone v,
    (heapmapMap_insert prio hm k v).trans
      (congrArg (fun m => mapUpdate m k v) hrel.2)⟩

@[sepref_fref_thms] theorem hmChangeKeyOp_refines [DecidableEq K]
    [Inhabited K] [Inhabited V] [Inhabited P] [LinearOrder P]
    (prio : V → P) (k : K) (v : V) :
    (hmChangeKeyOp prio k v,
      fun m => op_map_update_ex K V ((k, v), m)) ∈
      fref (fun m : K → Option V => k ∈ mapDom m) (heapmapRel prio)
        (fun _ => NRest.nrestRel (heapmapRel prio)) := by
  intro hm m hpre hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  have hk : heapmapMap hm k ≠ none := by simpa [hrel.2] using hpre
  have hass : heapmapInvariant prio hm ∧ heapmapMap hm k ≠ none :=
    ⟨hrel.1, hk⟩
  dsimp only
  unfold hmChangeKeyOp
  rw [NRest.assert_pos hass, NRest.returnT_bindT]
  unfold op_map_update_ex
  apply NRest.param_returnT
  exact ⟨heapmapInvariant_changeKey prio hrel.1 hk v,
    (heapmapMap_changeKey prio v hrel.1.1 hk).trans
      (congrArg (fun m => mapUpdate m k v) hrel.2)⟩

@[sepref_fref_thms] theorem hmDecreaseKeyOp_refines [DecidableEq K]
    [Inhabited K] [Inhabited V] [Inhabited P] [LinearOrder P]
    (prio : V → P) (k : K) (v : V) :
    (hmDecreaseKeyOp prio k v,
      fun m => op_pm_decrease_key K V P prio ((k, v), m)) ∈
      fref (fun m : K → Option V => decreaseKeyPre prio ((k, v), m))
        (heapmapRel prio) (fun _ => NRest.nrestRel (heapmapRel prio)) := by
  intro hm m hpre hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  have hpre' : decreaseKeyPre prio ((k, v), heapmapMap hm) := by
    simpa [hrel.2] using hpre
  have hass : heapmapInvariant prio hm ∧
      decreaseKeyPre prio ((k, v), heapmapMap hm) := ⟨hrel.1, hpre'⟩
  dsimp only
  unfold hmDecreaseKeyOp
  rw [NRest.assert_pos hass, NRest.returnT_bindT]
  unfold op_pm_decrease_key
  apply NRest.param_returnT
  exact ⟨heapmapInvariant_decreaseKey prio hrel.1 hpre',
    (heapmapMap_decreaseKey prio v hrel.1.1 hpre'.1).trans
      (congrArg (fun m => mapUpdate m k v) hrel.2)⟩

@[sepref_fref_thms] theorem hmIncreaseKeyOp_refines [DecidableEq K]
    [Inhabited K] [Inhabited V] [Inhabited P] [LinearOrder P]
    (prio : V → P) (k : K) (v : V) :
    (hmIncreaseKeyOp prio k v,
      fun m => op_pm_increase_key K V P prio ((k, v), m)) ∈
      fref (fun m : K → Option V => increaseKeyPre prio ((k, v), m))
        (heapmapRel prio) (fun _ => NRest.nrestRel (heapmapRel prio)) := by
  intro hm m hpre hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  have hpre' : increaseKeyPre prio ((k, v), heapmapMap hm) := by
    simpa [hrel.2] using hpre
  have hass : heapmapInvariant prio hm ∧
      increaseKeyPre prio ((k, v), heapmapMap hm) := ⟨hrel.1, hpre'⟩
  dsimp only
  unfold hmIncreaseKeyOp
  rw [NRest.assert_pos hass, NRest.returnT_bindT]
  unfold op_pm_increase_key
  apply NRest.param_returnT
  exact ⟨heapmapInvariant_increaseKey prio hrel.1 hpre',
    (heapmapMap_increaseKey prio v hrel.1.1 hpre'.1).trans
      (congrArg (fun m => mapUpdate m k v) hrel.2)⟩

@[sepref_fref_thms] theorem hmRemoveOp_refines [DecidableEq K]
    [Inhabited K] [Inhabited V] [Inhabited P] [LinearOrder P]
    (prio : V → P) (k : K) :
    (hmRemoveOp prio k,
      fun m => op_map_delete_ex K V (k, m)) ∈
      fref (fun m : K → Option V => k ∈ mapDom m) (heapmapRel prio)
        (fun _ => NRest.nrestRel (heapmapRel prio)) := by
  intro hm m hpre hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  have hk : heapmapMap hm k ≠ none := by simpa [hrel.2] using hpre
  have hass : heapmapInvariant prio hm ∧ heapmapMap hm k ≠ none :=
    ⟨hrel.1, hk⟩
  dsimp only
  unfold hmRemoveOp
  rw [NRest.assert_pos hass, NRest.returnT_bindT]
  unfold op_map_delete_ex
  apply NRest.param_returnT
  exact ⟨heapmapInvariant_remove prio hrel.1 hk,
    (heapmapMap_remove prio hrel.1.1 hk).trans
      (congrArg (fun m => mapDelete m k) hrel.2)⟩

@[sepref_fref_thms] theorem hmPeekMinOp_refines [DecidableEq K]
    [Inhabited K] [Inhabited V] [Inhabited P] [LinearOrder P]
    (prio : V → P) :
    (hmPeekMinOp, op_pm_peek_min K V P prio) ∈
      fref (fun m : K → Option V => m ≠ mapEmpty) (heapmapRel prio)
        (fun _ => NRest.nrestRel (Set.diagonal (K × V))) := by
  intro hm m hpre hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  have hne : heapmapMap hm ≠ mapEmpty := by
    intro he
    exact hpre (hrel.2 ▸ he)
  obtain ⟨k, v, hpeek, hv, hmin⟩ := hmPeekMin?_correct prio hrel.1 hne
  dsimp only
  unfold hmPeekMinOp op_pm_peek_min prioMapPeekMin
  rw [hpeek]
  apply NRest.nrestRel_of_le
  refine (NRest.returnT_refine (R := Set.diagonal (K × V)) rfl).trans ?_
  apply NRest.concFun_mono
  exact hmReturnT_le_spec_zero ⟨by simpa [hrel.2] using hv, by
    intro k' v' hv'
    exact hmin k' v' (by simpa [hrel.2] using hv')⟩

@[sepref_fref_thms] theorem hmPopMinOp_refines [DecidableEq K]
    [Inhabited K] [Inhabited V] [Inhabited P] [LinearOrder P]
    (prio : V → P) :
    (hmPopMinOp prio, op_pm_pop_min K V P prio) ∈
      fref (fun m : K → Option V => m ≠ mapEmpty) (heapmapRel prio)
        (fun _ => NRest.nrestRel
          (Set.diagonal (K × V) ×ᵣ heapmapRel prio)) := by
  intro hm m hpre hrel
  change heapmapInvariant prio hm ∧ heapmapMap hm = m at hrel
  have hne : heapmapMap hm ≠ mapEmpty := by
    intro he
    exact hpre (hrel.2 ▸ he)
  obtain ⟨k, v, hm', hpop, hinv', hv, hmap', hmin⟩ :=
    hmPopMin?_correct prio hrel.1 hne
  dsimp only
  unfold hmPopMinOp op_pm_pop_min prioMapPopMin
  rw [hpop]
  apply NRest.nrestRel_of_le
  refine (NRest.returnT_refine
    (R := Set.diagonal (K × V) ×ᵣ heapmapRel prio)
    (show (((k, v), hm'), ((k, v), mapDelete m k)) ∈
      Set.diagonal (K × V) ×ᵣ heapmapRel prio from
      ⟨rfl, ⟨hinv', hmap'.trans
        (congrArg (fun m => mapDelete m k) hrel.2)⟩⟩)).trans ?_
  apply NRest.concFun_mono
  exact hmReturnT_le_spec_zero ⟨by simpa [hrel.2] using hv, rfl, by
    intro k' v' hv'
    exact hmin k' v' (by simpa [hrel.2] using hv')⟩

/-! ## Source and zero-hole gates -/

run_cmd do
  let env ← Lean.Elab.Command.liftCoreM Lean.getEnv
  for n in #[``AbsHeapmap, ``heapmapHeapView, ``heapmapStructInv,
      ``heapmapInvariant, ``heapmapHeapRel, ``heapmapRel, ``hmLength,
      ``hmValid, ``hmKeyOf, ``hmLookup, ``hmExchange, ``hmIndex,
      ``hmUpdateAt, ``hmButlast, ``hmAppend, ``hmValueOf, ``hmPrioOf,
      ``hmSwim, ``hmSink, ``hmRepair, ``hmInsert, ``hmDecreaseKey,
      ``hmIncreaseKey, ``hmChangeKey, ``hmSet, ``hmRemove,
      ``hmContains, ``hmPeekMin?, ``hmPopMin?, ``heapmapInvariant_insert,
      ``heapmapInvariant_changeKey, ``heapmapInvariant_decreaseKey,
      ``heapmapInvariant_increaseKey, ``heapmapInvariant_set,
      ``heapmapInvariant_remove, ``heapmapMap_remove,
      ``hmPeekMin?_correct, ``hmPopMin?_correct] do
    unless env.contains n do
      throwError "abs-heapmap source gate: missing declaration {n}"

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``hmEmptyOp_refines, ``hmIsEmptyOp_refines,
      ``hmLookupOp_refines, ``hmContainsOp_refines, ``hmInsertOp_refines,
      ``hmSetOp_refines, ``hmChangeKeyOp_refines,
      ``hmDecreaseKeyOp_refines, ``hmIncreaseKeyOp_refines,
      ``hmRemoveOp_refines, ``hmPeekMinOp_refines, ``hmPopMinOp_refines] do
    unless rules.contains n do
      throwError "abs-heapmap fref gate: missing rule {n}"

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.heapmapInvariant_remove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms heapmapInvariant_remove

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hmPopMinOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmPopMinOp_refines

end Lax13Proofs.Refine.Sepref.Iicf
