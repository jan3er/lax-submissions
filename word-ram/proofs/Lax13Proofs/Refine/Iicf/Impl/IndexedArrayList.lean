import Lax13Proofs.Refine.Iicf.Impl.MSArrayList

/-!
# Indexed fixed-capacity array lists

Port of Sepreftime's `IICF_Indexed_Array_List.thy` at
`c1c987b45ec886d289ba215768182ac87b82f20d`.

The concrete carrier is a fixed-maximum-size list together with an inverse
position array.  Both buffers are caller-owned.  Thus source empty-size is a
pure model/establishment boundary, never an allocation or replicate HNR rule.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

abbrev IndexedArrayList := MSArrayList × List ℕ

/-! ## Source invariant and consequences -/

structure IalInvar (N : ℕ) (l qp : List ℕ) : Prop where
  maxsize_eq : qp.length = N
  list_nodup : l.Nodup
  list_bounded : ∀ k ∈ l, k < N
  qp_def : ∀ k, k < N → qp[k]! = if k ∈ l then listIndex l k else N

theorem listIndex_eq_idxOf (l : List ℕ) (k : ℕ) :
    listIndex l k = l.idxOf k := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : x = k
      · subst x
        simp [listIndex, propBool]
      · simp [listIndex, propBool, h, ih, List.idxOf_cons_ne]

theorem IalInvar.list_length_le {N : ℕ} {l qp : List ℕ}
    (h : IalInvar N l qp) : l.length ≤ N := by
  classical
  calc
    l.length = l.toFinset.card := (List.toFinset_card_of_nodup h.list_nodup).symm
    _ ≤ (Finset.range N).card := Finset.card_le_card (by
      intro k hk
      simp only [List.mem_toFinset] at hk ⊢
      simpa using h.list_bounded k hk)
    _ = N := Finset.card_range N

theorem IalInvar.elem_lt {N : ℕ} {l qp : List ℕ}
    (h : IalInvar N l qp) {i : ℕ} (hi : i < l.length) : l[i]! < N := by
  exact h.list_bounded l[i]! (by simp [getElem!_pos l i hi])

theorem IalInvar.qp_index_iff {N : ℕ} {l qp : List ℕ}
    (h : IalInvar N l qp) {k : ℕ} (hk : k < N) :
    qp[k]! < l.length ↔ k ∈ l := by
  rw [h.qp_def k hk]
  split
  · rename_i hmem
    simp only [hmem, iff_true]
    rw [listIndex_eq_idxOf]
    exact List.idxOf_lt_length_of_mem hmem
  · rename_i hnot
    simp only [hnot, iff_false]
    exact Nat.not_lt_of_ge (h.list_length_le)

theorem IalInvar.lookup_index {N : ℕ} {l qp : List ℕ}
    (h : IalInvar N l qp) {k : ℕ} (hk : k ∈ l) :
    qp[k]! = listIndex l k := by
  rw [h.qp_def k (h.list_bounded k hk), if_pos hk]

theorem IalInvar.list_lookup_qp {N : ℕ} {l qp : List ℕ}
    (h : IalInvar N l qp) {k : ℕ} (hk : k ∈ l) :
    l[qp[k]!]! = k := by
  rw [h.lookup_index hk, listIndex_eq_idxOf, getElem!_pos]
  · exact List.idxOf_get _
  · exact List.idxOf_lt_length_of_mem hk

theorem IalInvar.room_of_fresh {N : ℕ} {l qp : List ℕ}
    (h : IalInvar N l qp) {k : ℕ} (hk : k < N) (hnot : k ∉ l) :
    l.length < N := by
  have hle := h.list_length_le
  apply Nat.lt_of_le_of_ne hle
  intro heq
  classical
  have hsub : l.toFinset ⊆ Finset.range N := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simpa using h.list_bounded x hx
  have hcards : (Finset.range N).card ≤ l.toFinset.card := by
    simp [List.toFinset_card_of_nodup h.list_nodup, heq]
  have hall := Finset.eq_of_subset_of_card_le hsub hcards
  apply hnot
  have : k ∈ Finset.range N := by simpa
  rw [← hall] at this
  simpa using this

theorem IalInvar.append {N : ℕ} {l qp : List ℕ}
    (h : IalInvar N l qp) {k : ℕ} (hk : k < N) (hnot : k ∉ l) :
    IalInvar N (l ++ [k]) (qp.set k l.length) := by
  classical
  refine ⟨by simpa using h.maxsize_eq,
    by simpa [List.concat_eq_append] using
      (List.nodup_concat l k).2 ⟨hnot, h.list_nodup⟩,
    ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    exact hx.elim (h.list_bounded x) (fun hxe => hxe ▸ hk)
  · intro x hx
    have hxqp : x < qp.length := by simpa [h.maxsize_eq] using hx
    by_cases hxk : x = k
    · subst x
      rw [getElem!_pos (qp.set k l.length) k (by simpa using hxqp),
        List.getElem_set_self]
      simp [hnot, listIndex_eq_idxOf, List.idxOf_append_of_notMem]
    · rw [getElem!_pos (qp.set k l.length) x (by simpa using hxqp),
        List.getElem_set_of_ne (Ne.symm hxk)]
      have hq := h.qp_def x hx
      rw [getElem!_pos qp x hxqp] at hq
      rw [hq]
      by_cases hxl : x ∈ l
      · simp [hxl, hxk, listIndex_eq_idxOf, List.idxOf_append_of_mem]
      · have hxnew : x ∉ l ++ [k] := by simp [hxl, hxk]
        simp [hxl, hxnew]

theorem listButlast_eq_dropLast (l : List ℕ) : listButlast l = l.dropLast := by
  simp [listButlast, List.dropLast_eq_take]

theorem IalInvar.butlast {N : ℕ} {l qp : List ℕ}
    (h : IalInvar N l qp) (hne : l ≠ []) :
    IalInvar N (listButlast l) (qp.set (l.getLast hne) N) := by
  classical
  let last := l.getLast hne
  have hdecomp : l.dropLast ++ [last] = l := List.dropLast_append_getLast hne
  have hndApp : (l.dropLast ++ [last]).Nodup := by simpa [hdecomp] using h.list_nodup
  have hndParts := (List.nodup_concat l.dropLast last).1
    (by simpa [List.concat_eq_append] using hndApp)
  have hlastMem : last ∈ l := List.getLast_mem hne
  have hlastN : last < N := h.list_bounded last hlastMem
  have hlastQp : last < qp.length := by simpa [h.maxsize_eq] using hlastN
  rw [listButlast_eq_dropLast]
  refine ⟨by simpa using h.maxsize_eq, hndParts.2, ?_, ?_⟩
  · intro x hx
    exact h.list_bounded x (List.mem_of_mem_dropLast hx)
  · intro x hxN
    have hxqp : x < qp.length := by simpa [h.maxsize_eq] using hxN
    by_cases hxl : x = last
    · subst x
      rw [getElem!_pos (qp.set last N) last (by simpa using hlastQp),
        List.getElem_set_self]
      simp [hndParts.1]
    · rw [getElem!_pos (qp.set last N) x (by simpa using hxqp),
        List.getElem_set_of_ne (Ne.symm hxl)]
      have hq := h.qp_def x hxN
      rw [getElem!_pos qp x hxqp] at hq
      rw [hq]
      by_cases hxdrop : x ∈ l.dropLast
      · have hxin : x ∈ l := List.mem_of_mem_dropLast hxdrop
        have hidx : listIndex l.dropLast x = listIndex l x := by
          rw [listIndex_eq_idxOf, listIndex_eq_idxOf]
          calc
            l.dropLast.idxOf x = (l.dropLast ++ [last]).idxOf x :=
              (List.idxOf_append_of_mem hxdrop).symm
            _ = l.idxOf x := congrArg (fun xs : List ℕ => xs.idxOf x) hdecomp
        simp [hxdrop, hxin, hidx]
      · have hxnot : x ∉ l := by
          rw [← hdecomp]
          simp [hxdrop, hxl]
        simp [hxdrop, hxnot]

def swapIndex (i j k : ℕ) : ℕ :=
  if k = i then j else if k = j then i else k

theorem swapIndex_injective (i j : ℕ) : Function.Injective (swapIndex i j) := by
  apply Function.LeftInverse.injective (g := swapIndex i j)
  intro k
  by_cases hij : i = j
  · subst j
    by_cases hki : k = i <;> simp [swapIndex, hki]
  · by_cases hki : k = i
    · subst k
      simp [swapIndex, Ne.symm hij]
    · by_cases hkj : k = j
      · subst k
        simp [swapIndex]
      · simp [swapIndex, hki, hkj]

theorem swapIndex_lt {i j k n : ℕ} (hi : i < n) (hj : j < n) (hk : k < n) :
    swapIndex i j k < n := by
  simp only [swapIndex]
  split
  · exact hj
  · split
    · exact hi
    · exact hk

theorem listSwap_eq_set (l : List ℕ) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) :
    listSwap l i j = (l.set i l[j]!).set j l[i]! := by
  unfold listSwap
  rw [listAt?_eq_getElem?, listAt?_eq_getElem?,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp [listSet_eq_set, getElem!_pos, hi, hj]

theorem listSwap_length (l : List ℕ) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) :
    (listSwap l i j).length = l.length := by
  rw [listSwap_eq_set l hi hj]
  simp

theorem listSwap_getElem (l : List ℕ) {i j k : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hk : k < l.length) :
    (listSwap l i j)[k]'(by simpa [listSwap_length l hi hj] using hk) =
      l[swapIndex i j k]'(swapIndex_lt hi hj hk) := by
  simp only [listSwap_eq_set l hi hj]
  by_cases hkj : k = j
  · subst k
    by_cases hji : j = i
    · subst j
      simp [swapIndex, getElem!_pos, hi]
    · simp [swapIndex, hji, List.getElem_set_self, getElem!_pos, hi, hj]
  · rw [List.getElem_set_of_ne (Ne.symm hkj)]
    by_cases hki : k = i
    · subst k
      simp [swapIndex, List.getElem_set_self, getElem!_pos, hj]
    · rw [List.getElem_set_of_ne (Ne.symm hki)]
      simp [swapIndex, hki, hkj]

theorem listSwap_nodup {l : List ℕ} (hnd : l.Nodup) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) : (listSwap l i j).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro a b hab
  have ha : a.val < l.length := by simpa [listSwap_length l hi hj] using a.isLt
  have hb : b.val < l.length := by simpa [listSwap_length l hi hj] using b.isLt
  have hv : l[swapIndex i j a.val]'(swapIndex_lt hi hj ha) =
      l[swapIndex i j b.val]'(swapIndex_lt hi hj hb) := by
    rw [← listSwap_getElem l hi hj ha, ← listSwap_getElem l hi hj hb]
    exact hab
  have hidx : swapIndex i j a.val = swapIndex i j b.val := by
    let aa : Fin l.length := ⟨swapIndex i j a.val, swapIndex_lt hi hj ha⟩
    let bb : Fin l.length := ⟨swapIndex i j b.val, swapIndex_lt hi hj hb⟩
    have hab' : l[aa] = l[bb] := by simpa [aa, bb] using hv
    exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd) hab')
  exact Fin.ext (swapIndex_injective i j hidx)

theorem listSwap_self (l : List ℕ) {i : ℕ} (hi : i < l.length) :
    listSwap l i i = l := by
  apply List.ext_getElem (listSwap_length l hi hi)
  intro k hk hk'
  by_cases hki : k = i
  · subst k
    simpa [swapIndex] using listSwap_getElem l hi hi hk'
  · simpa [swapIndex, hki] using listSwap_getElem l hi hi hk'

theorem listSwap_mem_iff (l : List ℕ) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (x : ℕ) :
    x ∈ listSwap l i j ↔ x ∈ l := by
  constructor
  · intro hx
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
    have hk' : k < l.length := by simpa [listSwap_length l hi hj] using hk
    have hv := listSwap_getElem l hi hj hk'
    rw [hkx] at hv
    rw [hv]
    exact List.getElem_mem (swapIndex_lt hi hj hk')
  · intro hx
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
    let k' := swapIndex i j k
    have hk' : k' < l.length := swapIndex_lt hi hj hk
    have hout : k' < (listSwap l i j).length := by
      simpa [listSwap_length l hi hj] using hk'
    have hmemout := List.getElem_mem hout
    have hswap2 : swapIndex i j k' = k := by
      by_cases hij : i = j
      · subst j
        by_cases hki : k = i <;> simp [k', swapIndex, hki]
      · by_cases hki : k = i
        · subst k
          simp [k', swapIndex, Ne.symm hij]
        · by_cases hkj : k = j
          · subst k
            simp [k', swapIndex, Ne.symm hij]
          · simp [k', swapIndex, hki, hkj]
    have heq : (listSwap l i j)[k']'hout = x := by
      rw [listSwap_getElem l hi hj hk']
      let aa : Fin l.length :=
        ⟨swapIndex i j k', swapIndex_lt hi hj hk'⟩
      let bb : Fin l.length := ⟨k, hk⟩
      have hab : aa = bb := Fin.ext hswap2
      have hv2 := congrArg (fun q : Fin l.length => l[q]) hab
      simpa [aa, bb, hkx] using hv2
    rwa [heq] at hmemout

theorem IalInvar.swap {N : ℕ} {l qp : List ℕ}
    (h : IalInvar N l qp) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) :
    IalInvar N (listSwap l i j)
      ((qp.set l[j]! i).set l[i]! j) := by
  classical
  let vi := l[i]!
  let vj := l[j]!
  have hviEq : vi = l[i]'hi := getElem!_pos l i hi
  have hvjEq : vj = l[j]'hj := getElem!_pos l j hj
  have hviN : vi < N := h.elem_lt hi
  have hvjN : vj < N := h.elem_lt hj
  have hviQ : vi < qp.length := by simpa [h.maxsize_eq] using hviN
  have hvjQ : vj < qp.length := by simpa [h.maxsize_eq] using hvjN
  have hnd' := listSwap_nodup h.list_nodup hi hj
  refine ⟨by simp [h.maxsize_eq], hnd', ?_, ?_⟩
  · intro x hx
    exact h.list_bounded x ((listSwap_mem_iff l hi hj x).mp hx)
  · intro x hxN
    have hxQ : x < qp.length := by simpa [h.maxsize_eq] using hxN
    have hmem : (x ∈ listSwap l i j) = (x ∈ l) :=
      propext (listSwap_mem_iff l hi hj x)
    by_cases hij : i = j
    · subst j
      by_cases hxv : x = vi
      · subst x
        rw [getElem!_pos _ vi (by simp [hviQ]), List.getElem_set_self]
        rw [listSwap_self l hi]
        have hviMem : vi ∈ l := by
          rw [hviEq]
          exact List.getElem_mem hi
        simp only [if_pos hviMem]
        rw [listIndex_eq_idxOf]
        have hidx := List.get_idxOf h.list_nodup ⟨i, hi⟩
        simpa [hviEq] using hidx.symm
      · rw [getElem!_pos _ x (by simp [hxQ]),
          List.getElem_set_of_ne (Ne.symm hxv),
          List.getElem_set_of_ne (Ne.symm hxv)]
        have hq := h.qp_def x hxN
        rw [getElem!_pos qp x hxQ] at hq
        rw [hq, listSwap_self l hi]
    · have hvneq : vi ≠ vj := by
        intro hv
        dsimp [vi, vj] at hv
        rw [getElem!_pos l i hi, getElem!_pos l j hj] at hv
        let ii : Fin l.length := ⟨i, hi⟩
        let jj : Fin l.length := ⟨j, hj⟩
        have hv' : l[ii] = l[jj] := by simpa [ii, jj] using hv
        have := (List.nodup_iff_injective_getElem.mp h.list_nodup) hv'
        exact hij (congrArg Fin.val this)
      by_cases hxvi : x = vi
      · subst x
        rw [getElem!_pos _ vi (by simp [hviQ]), List.getElem_set_self]
        have hget : (listSwap l i j)[j]'(by simpa [listSwap_length l hi hj] using hj) = vi := by
          rw [listSwap_getElem l hi hj hj]
          simp only [swapIndex, if_neg (Ne.symm hij), if_pos]
          exact (getElem!_pos l i hi).symm
        have hidx := List.get_idxOf hnd'
          ⟨j, by simpa [listSwap_length l hi hj] using hj⟩
        simp only [if_pos ((listSwap_mem_iff l hi hj vi).2
          (by simp [vi, getElem!_pos, hi]))]
        rw [listIndex_eq_idxOf]
        simpa [hget] using hidx.symm
      · by_cases hxvj : x = vj
        · subst x
          rw [getElem!_pos _ vj (by simp [hvjQ]),
            List.getElem_set_of_ne hvneq, List.getElem_set_self]
          have hget : (listSwap l i j)[i]'(by simpa [listSwap_length l hi hj] using hi) = vj := by
            rw [listSwap_getElem l hi hj hi]
            simp only [swapIndex, if_pos]
            exact (getElem!_pos l j hj).symm
          have hidx := List.get_idxOf hnd'
            ⟨i, by simpa [listSwap_length l hi hj] using hi⟩
          simp only [if_pos ((listSwap_mem_iff l hi hj vj).2
            (by simp [vj, getElem!_pos, hj]))]
          rw [listIndex_eq_idxOf]
          simpa [hget] using hidx.symm
        · rw [getElem!_pos _ x (by simp [hxQ]),
            List.getElem_set_of_ne (Ne.symm hxvi),
            List.getElem_set_of_ne (Ne.symm hxvj)]
          have hq := h.qp_def x hxN
          rw [getElem!_pos qp x hxQ] at hq
          rw [hq]
          by_cases hxl : x ∈ l
          · have hpos := List.idxOf_lt_length_of_mem hxl
            have hxl' : x ∈ listSwap l i j :=
              (listSwap_mem_iff l hi hj x).2 hxl
            have hpi : l.idxOf x ≠ i := by
              intro heq
              have hg := List.idxOf_get hpos
              let ii : Fin l.length := ⟨l.idxOf x, hpos⟩
              let jj : Fin l.length := ⟨i, hi⟩
              have hijFin : ii = jj := Fin.ext heq
              have hval : l[i]'hi = x := by simpa [ii, jj, hijFin] using hg
              exact hxvi (hval.symm.trans hviEq.symm)
            have hpj : l.idxOf x ≠ j := by
              intro heq
              have hg := List.idxOf_get hpos
              let ii : Fin l.length := ⟨l.idxOf x, hpos⟩
              let jj : Fin l.length := ⟨j, hj⟩
              have hijFin : ii = jj := Fin.ext heq
              have hval : l[j]'hj = x := by simpa [ii, jj, hijFin] using hg
              exact hxvj (hval.symm.trans hvjEq.symm)
            have hget : (listSwap l i j)[l.idxOf x]'(by
                simpa [listSwap_length l hi hj] using hpos) = x := by
              rw [listSwap_getElem l hi hj hpos]
              simp only [swapIndex, if_neg hpi, if_neg hpj]
              exact List.idxOf_get hpos
            have hidx := List.get_idxOf hnd'
              ⟨l.idxOf x, by simpa [listSwap_length l hi hj] using hpos⟩
            simp only [if_pos hxl, if_pos hxl']
            rw [listIndex_eq_idxOf, listIndex_eq_idxOf]
            simpa [hget] using hidx.symm
          · have hxl' : x ∉ listSwap l i j := fun hx =>
              hxl ((listSwap_mem_iff l hi hj x).1 hx)
            simp [hxl, hxl']

/-! The source's commented `ial_assn_precise` attempt remains a disposition:
this substrate has no heap-level `precise` class.  `ialRel1_singleValued`
below is the available relational analogue.  Its unrelated `oops` Boolean
lemma and the TODO about injecting domain conditions into assertions are not
exported as APIs. -/

def ialRel1 (N : ℕ) : Set (IndexedArrayList × List ℕ) :=
  {p | (p.1.1, p.2) ∈ isMSArrayList N ∧ IalInvar N p.2 p.1.2}

theorem ialRel1_singleValued (N : ℕ) : SingleValued (ialRel1 N) := by
  intro s xs ys hx hy
  exact (isMSArrayList_singleValued N) s.1 xs ys hx.1 hy.1

def ialAssn2 (_N : ℕ) :
    IndexedArrayList → (String × String × String) × String → Assn :=
  boundedArrayAssn ×ₐ arrayAssn

def ialBaseAssn (N : ℕ) :
    List ℕ → (String × String × String) × String → Assn :=
  hrComp (ialAssn2 N) (ialRel1 N)

def ialRel {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    Set (IndexedArrayList × List α) :=
  relComp (ialRel1 N) (listRel (thePure A))

/-- Source `ial_assn N A`, composed through `ial_rel1` then the pure list
relation. -/
def ialAssn {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    List α → (String × String × String) × String → Assn :=
  hrComp (ialBaseAssn N) (listRel (thePure A))

@[intf_of_assn] theorem ialAssn_intf {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) : intfOfAssn (ialAssn N A) (ListI α) := trivial

theorem ial_assn_combined {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    ialAssn N A = hrComp (ialAssn2 N) (ialRel N A) := by
  rw [ialAssn, ialBaseAssn, ialRel, hr_comp_assoc]

/-! ## Empty-size: two caller-owned buffers, no allocation -/

def ialEmptyModel (N : ℕ) : IndexedArrayList :=
  (marlEmptyModel N, List.replicate N N)

def ialEmptyIn (N : ℕ) (logical qp : List ℕ) : Option IndexedArrayList :=
  if logical.length = N ∧ qp = List.replicate N N then
    some (⟨logical, 0, N⟩, qp)
  else none

theorem ialEmptyInvar (N : ℕ) :
    IalInvar N [] (List.replicate N N) := by
  refine ⟨by simp, List.nodup_nil, by simp, ?_⟩
  intro k hk
  simp [getElem!_pos, hk]

theorem ialEmptyModel_refines (N : ℕ) :
    (ialEmptyModel N, []) ∈ ialRel1 N :=
  ⟨marlEmptyModel_refines N, ialEmptyInvar N⟩

theorem ialEmptyIn_some {N : ℕ} {logical qp : List ℕ}
    {s : IndexedArrayList} (h : ialEmptyIn N logical qp = some s) :
    (s, []) ∈ ialRel1 N := by
  simp only [ialEmptyIn] at h
  split at h
  · rename_i hsizes
    simp only [Option.some.injEq] at h
    subst s
    refine ⟨?_, ?_⟩
    · simp [isMSArrayList, hsizes.1, BoundedArray.active]
    · refine ⟨by simp [hsizes.2], List.nodup_nil, by simp, ?_⟩
      intro k hk
      simp [hsizes.2, getElem!_pos, hk]
  · contradiction

noncomputable def opIalEmptySz (_N : ℕ) : NRest (List ℕ) ECost :=
  op_list_empty ℕ

sepref_register opIalEmptySz : opIalEmptySz as
  (ℕ → NRest (ListI ℕ) ECost)

theorem ial_fold_custom_empty_sz (N : ℕ) :
    op_list_empty ℕ = opIalEmptySz N := rfl

theorem ial_custom_empty_identity (N : ℕ) :
    opIalEmptySz N = NRest.returnT [] := rfl

noncomputable def ialEmptyOp (N : ℕ) : NRest IndexedArrayList ECost :=
  NRest.returnT (ialEmptyModel N)

theorem ialEmptyOp_refines (N : ℕ) :
    (ialEmptyOp N, opIalEmptySz N) ∈ NRest.nrestRel (ialRel1 N) := by
  exact NRest.param_returnT (ialEmptyModel_refines N)

/-! ## Value operations -/

def ialSwap (s : IndexedArrayList) (i j : ℕ) : Option IndexedArrayList :=
  let l := s.1.active
  if hi : i < l.length then
    if hj : j < l.length then
      let vi := l[i]'hi
      let vj := l[j]'hj
      let ms' : MSArrayList :=
        ⟨s.1.buffer.set i vj |>.set j vi, s.1.length, s.1.capacity⟩
      some (ms', (s.2.set vj i).set vi j)
    else none
  else none

def ialLength (s : IndexedArrayList) : ℕ := s.1.length

def ialIndex? (s : IndexedArrayList) (k : ℕ) : Option ℕ :=
  if k ∈ s.1.active then some s.2[k]! else none

def ialButlast (N : ℕ) (s : IndexedArrayList) : Option IndexedArrayList :=
  if s.1.length = 0 then none
  else
    let i := s.1.length - 1
    let k := s.1.buffer[i]!
    some (⟨s.1.buffer, i, s.1.capacity⟩, s.2.set k N)

def ialAppend (N : ℕ) (s : IndexedArrayList) (k : ℕ) : Option IndexedArrayList :=
  if k < N ∧ k ∉ s.1.active then
    let oldLen := s.1.length
    some (⟨s.1.buffer.set oldLen k, oldLen + 1, s.1.capacity⟩,
      s.2.set k oldLen)
  else none

def ialGet? (s : IndexedArrayList) (i : ℕ) : Option ℕ :=
  listAt? s.1.active i

def ialContains (N k : ℕ) (s : IndexedArrayList) : Bool :=
  if k < N then decide (s.2[k]! < N) else false

private theorem ial_state_wf_of_nonempty {N : ℕ} {s : MSArrayList}
    {l : List ℕ} (hs : (s, l) ∈ isMSArrayList N) (hne : l ≠ []) : s.Wf := by
  change s.buffer.length = N ∧ s.length ≤ N ∧
    s.capacity = N ∧ s.active = l at hs
  have hN : 0 < N := by
    have : 0 < s.length := by
      rw [isMSArrayList_length hs]
      cases l <;> simp_all
    omega
  exact ⟨by omega, by omega, by omega⟩

theorem ialAppend_refines {N : ℕ} {s : IndexedArrayList} {l : List ℕ}
    (hs : (s, l) ∈ ialRel1 N) {k : ℕ} (hk : k < N) (hnot : k ∉ l) :
    ∃ t, ialAppend N s k = some t ∧ (t, l ++ [k]) ∈ ialRel1 N := by
  rcases hs with ⟨hms, hinv⟩
  have hactive : s.1.active = l := hms.2.2.2
  have hlenEq : s.1.length = l.length := isMSArrayList_length hms
  have hroom := hinv.room_of_fresh hk hnot
  have hsroom : s.1.length < N := by rw [hlenEq]; exact hroom
  have hcap : s.1.capacity = N := hms.2.2.1
  let t : IndexedArrayList :=
    (⟨s.1.buffer.set s.1.length k, s.1.length + 1, s.1.capacity⟩,
      s.2.set k s.1.length)
  refine ⟨t, ?_, ?_⟩
  · simp [ialAppend, hk, hactive, hnot, t]
  · refine ⟨?_, ?_⟩
    · have hp : marlAppend N s.1 k = some
          ⟨s.1.buffer.set s.1.length k, s.1.length + 1, N⟩ := by
        simp [marlAppend, hsroom]
      have hm := marlAppend_some_refines hms hp
      simpa [t, hcap] using hm
    · simpa [t, hlenEq] using hinv.append hk hnot

theorem ialButlast_refines {N : ℕ} {s : IndexedArrayList} {l : List ℕ}
    (hs : (s, l) ∈ ialRel1 N) (hne : l ≠ []) :
    ∃ t, ialButlast N s = some t ∧ (t, listButlast l) ∈ ialRel1 N := by
  rcases hs with ⟨hms, hinv⟩
  have hlenEq : s.1.length = l.length := isMSArrayList_length hms
  have hlen : s.1.length ≠ 0 := by
    rw [hlenEq]
    exact fun hz => hne (List.eq_nil_of_length_eq_zero hz)
  let i := s.1.length - 1
  have hi : i < s.1.length := by
    dsimp [i]
    omega
  have hwf := ial_state_wf_of_nonempty hms hne
  have hbuf := buffer_getElem_eq_active hwf hi
  have hactive : s.1.active = l := hms.2.2.2
  have hil : i = l.length - 1 := by simp [i, hlenEq]
  have hk : s.1.buffer[i]! = l.getLast hne := by
    rw [hbuf, hactive, hil, getElem!_pos]
    exact (List.getLast_eq_getElem hne).symm
  let t : IndexedArrayList :=
    (⟨s.1.buffer, i, s.1.capacity⟩, s.2.set (l.getLast hne) N)
  refine ⟨t, ?_, ?_⟩
  · simp [ialButlast, hlen, i, hk, t]
  · refine ⟨?_, ?_⟩
    · have hp : marlButlast s.1 = some ⟨s.1.buffer, i, s.1.capacity⟩ := by
        simp [marlButlast, hlen, i]
      exact marlButlast_some_refines hms hp
    · simpa [t] using hinv.butlast hne

theorem ialSwap_refines {N : ℕ} {s : IndexedArrayList} {l : List ℕ}
    (hs : (s, l) ∈ ialRel1 N) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) :
    ∃ t, ialSwap s i j = some t ∧ (t, listSwap l i j) ∈ ialRel1 N := by
  rcases hs with ⟨hms, hinv⟩
  have hactive : s.1.active = l := hms.2.2.2
  have his : i < s.1.active.length := by simpa [hactive] using hi
  have hjs : j < s.1.active.length := by simpa [hactive] using hj
  let vi := l[i]
  let vj := l[j]
  let t : IndexedArrayList :=
    (⟨(s.1.buffer.set i vj).set j vi, s.1.length, s.1.capacity⟩,
      (s.2.set vj i).set vi j)
  refine ⟨t, ?_, ?_⟩
  · simp [ialSwap, hactive, hi, hj, vi, vj, t]
  · refine ⟨?_, ?_⟩
    · have hmsRel : (s.1, l) ∈ isMSArrayList N := hms
      have hne : l ≠ [] := by
        intro hl
        rw [hl] at hi
        exact Nat.not_lt_zero i hi
      change s.1.buffer.length = N ∧ s.1.length ≤ N ∧
        s.1.capacity = N ∧ s.1.active = l at hms
      refine ⟨by simp [t, hms.1], hms.2.1, hms.2.2.1, ?_⟩
      have hwf := ial_state_wf_of_nonempty hmsRel hne
      have hbi := buffer_getElem_eq_active hwf
        (show i < s.1.length by simpa [isMSArrayList_length hmsRel] using hi)
      have hbj := buffer_getElem_eq_active hwf
        (show j < s.1.length by simpa [isMSArrayList_length hmsRel] using hj)
      rw [hactive] at hbi hbj
      have harl := arlSwapExecState_refines
        (show (s.1, l) ∈ arrayListRel from ⟨hwf, hactive⟩) hi hj
      simpa [t, arlSwapExecState, vi, vj, hbi, hbj,
        getElem!_pos, hi, hj] using harl.2
    · simpa [t, vi, vj, getElem!_pos, hi, hj] using hinv.swap hi hj

theorem ialIndex_refines {N : ℕ} {s : IndexedArrayList} {l : List ℕ}
    (hs : (s, l) ∈ ialRel1 N) {k : ℕ} (hk : k ∈ l) :
    ialIndex? s k = some (listIndex l k) := by
  rcases hs with ⟨hms, hinv⟩
  simp [ialIndex?, hms.2.2.2, hk, hinv.lookup_index hk]

theorem ialGet_refines {N : ℕ} {s : IndexedArrayList} {l : List ℕ}
    (hs : (s, l) ∈ ialRel1 N) (i : ℕ) :
    ialGet? s i = listAt? l i := by
  rcases hs with ⟨hms, _⟩
  simp [ialGet?, hms.2.2.2]

theorem ialContains_refines {N : ℕ} {s : IndexedArrayList} {l : List ℕ}
    (hs : (s, l) ∈ ialRel1 N) (k : ℕ) :
    ialContains N k s = propBool (k ∈ l) := by
  rcases hs with ⟨_, hinv⟩
  apply Bool.eq_iff_iff.mpr
  by_cases hkN : k < N
  · simp only [ialContains, if_pos hkN, decide_eq_true_eq, propBool]
    rw [hinv.qp_def k hkN]
    by_cases hmem : k ∈ l
    · simp [hmem, listIndex_eq_idxOf,
        lt_of_lt_of_le (List.idxOf_lt_length_of_mem hmem) hinv.list_length_le]
    · simp [hmem]
  · have hnot : k ∉ l := fun hmem => hkN (hinv.list_bounded k hmem)
    simp [ialContains, hkN, propBool, hnot]

/-! ## Cost-silent list-interface refinements -/

/-- The source's append rule requires the element relation to be below the
identity: abstract vertex names must be their concrete array indices. -/
def IalBelowIdentity (A : ℕ → ℕ → Assn) : Prop :=
  ∀ n a, (n, a) ∈ thePure A → n = a

theorem ialBelowIdentity_diagonal :
    IalBelowIdentity (pureAssn (Set.diagonal ℕ)) := by
  intro n a h
  simpa using h

noncomputable def ialSwapOp (p : (IndexedArrayList × ℕ) × ℕ) :
    NRest IndexedArrayList ECost :=
  match ialSwap p.1.1 p.1.2 p.2 with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def ialLengthOp (s : IndexedArrayList) : NRest ℕ ECost :=
  NRest.returnT (ialLength s)

noncomputable def ialIndexOp (_N : ℕ) (s : IndexedArrayList) (k : ℕ) :
    NRest ℕ ECost :=
  NRest.spec (fun i => ialIndex? s k = some i) (fun _ => 0)

noncomputable def ialButlastOp (N : ℕ) (s : IndexedArrayList) :
    NRest IndexedArrayList ECost :=
  match ialButlast N s with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def ialAppendOp (N : ℕ) (s : IndexedArrayList) (k : ℕ) :
    NRest IndexedArrayList ECost :=
  match ialAppend N s k with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def ialGetOp (p : IndexedArrayList × ℕ) : NRest ℕ ECost :=
  NRest.spec (fun x => ialGet? p.1 p.2 = some x) (fun _ => 0)

noncomputable def ialContainsOp (N k : ℕ) (s : IndexedArrayList) :
    NRest Bool ECost :=
  NRest.returnT (ialContains N k s)

theorem ialSwapOp_refines (N : ℕ) :
    (ialSwapOp, op_list_swap ℕ) ∈
      fref (fun p : (List ℕ × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧ p.2 < p.1.1.length)
        ((ialRel1 N ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (ialRel1 N)) := by
  rintro ⟨⟨s, i⟩, j⟩ ⟨⟨l, i'⟩, j'⟩ hpre ⟨⟨hs, hiEq⟩, hjEq⟩
  change i = i' at hiEq
  change j = j' at hjEq
  subst i'
  subst j'
  obtain ⟨t, ht, hrel⟩ := ialSwap_refines hs hpre.1 hpre.2
  simp [ialSwapOp, ht, op_list_swap, hpre]
  exact NRest.param_returnT hrel

theorem ialLengthOp_refines (N : ℕ) :
    (ialLengthOp, op_list_length ℕ) ∈
      fref (fun _ : List ℕ => True) (ialRel1 N)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro s l _ hs
  apply NRest.param_returnT
  change s.1.length = l.length
  exact isMSArrayList_length hs.1

theorem ialIndexOp_refines (N : ℕ) :
    (ialIndexOp N, op_list_index ℕ) ∈
      fref (fun _ : List ℕ => True) (ialRel1 N)
        (fun l => fref (fun k : ℕ => k ∈ l) (Set.diagonal ℕ)
          (fun _ => NRest.nrestRel (Set.diagonal ℕ))) := by
  intro s l _ hs k k' hk hkk
  change k = k' at hkk
  subst k'
  change (ialIndexOp N s k, op_list_index ℕ l k) ∈
    NRest.nrestRel (Set.diagonal ℕ)
  unfold ialIndexOp
  rw [listOptionSpec_eq_returnT (ialIndex_refines hs hk)]
  simp [op_list_index]

theorem ialButlastOp_refines (N : ℕ) :
    (ialButlastOp N, op_list_butlast ℕ) ∈
      fref (fun l : List ℕ => l ≠ []) (ialRel1 N)
        (fun _ => NRest.nrestRel (ialRel1 N)) := by
  intro s l hne hs
  obtain ⟨t, ht, hrel⟩ := ialButlast_refines hs hne
  simp [ialButlastOp, ht, op_list_butlast, hne]
  exact NRest.param_returnT hrel

theorem ialAppendOp_refines (N : ℕ) :
    (ialAppendOp N, op_list_append ℕ) ∈
      fref (fun _ : List ℕ => True) (ialRel1 N)
        (fun l => fref (fun k : ℕ => k < N ∧ k ∉ l) (Set.diagonal ℕ)
          (fun _ => NRest.nrestRel (ialRel1 N))) := by
  intro s l _ hs k k' hk hkk
  change k = k' at hkk
  subst k'
  obtain ⟨t, ht, hrel⟩ := ialAppend_refines hs hk.1 hk.2
  simp [ialAppendOp, ht, op_list_append]
  exact NRest.param_returnT hrel

theorem ialGetOp_refines (N : ℕ) :
    (ialGetOp, op_list_get ℕ) ∈
      fref (fun p : List ℕ × ℕ => p.2 < p.1.length)
        (ialRel1 N ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  rintro ⟨s, i⟩ ⟨l, i'⟩ hi ⟨hs, hii⟩
  change i = i' at hii
  subst i'
  obtain ⟨x, hx⟩ := listAt?_some_of_lt hi
  change (ialGetOp (s, i), op_list_get ℕ (l, i)) ∈
    NRest.nrestRel (Set.diagonal ℕ)
  simp only [op_list_get, NRest.assert_pos hi, NRest.returnT_bindT]
  rw [listOptionSpec_eq_returnT hx]
  rw [ialGetOp, ialGet_refines hs, listOptionSpec_eq_returnT hx]
  exact NRest.param_returnT rfl

theorem ialContainsOp_refines (N : ℕ) :
    (ialContainsOp N, op_list_contains ℕ) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => fref (fun _ : List ℕ => True) (ialRel1 N)
          (fun _ => NRest.nrestRel (Set.diagonal Bool))) := by
  intro k k' _ hkk s l _ hs
  change k = k' at hkk
  subst k'
  apply NRest.param_returnT
  exact ialContains_refines hs k

/-! ### Source-shaped rules through the generic pure element composition -/

theorem listRel_eq_of_ialBelowIdentity {A : ℕ → ℕ → Assn}
    (hbelow : IalBelowIdentity A) {xs ys : List ℕ}
    (h : (xs, ys) ∈ listRel (thePure A)) : xs = ys := by
  change List.Forall₂ (fun x y => (x, y) ∈ thePure A) xs ys at h
  induction h with
  | nil => rfl
  | cons hxy htl ih => simp [hbelow _ _ hxy, ih]

@[sepref_fref_thms] theorem ialSwapOp_refines_rel {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (ialSwapOp, op_list_swap α) ∈
      fref (fun p : (List α × ℕ) × ℕ =>
          p.1.2 < p.1.1.length ∧ p.2 < p.1.1.length)
        ((ialRel N A ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (ialRel N A)) := by
  rintro ⟨⟨s, i⟩, j⟩ ⟨⟨xs, i'⟩, j'⟩ hpre ⟨⟨hs, hiEq⟩, hjEq⟩
  change i = i' at hiEq
  change j = j' at hjEq
  subst i'
  subst j'
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hp : i < ns.length ∧ j < ns.length := by
    simpa [hnxs.length_eq] using hpre
  obtain ⟨t, ht, hrel⟩ := ialSwap_refines hsn hp.1 hp.2
  simp [ialSwapOp, ht, op_list_swap, hpre]
  exact NRest.param_returnT
    ⟨listSwap ns i j, hrel, swap_param hnxs hp.1 hp.2⟩

@[sepref_fref_thms] theorem ialLengthOp_refines_rel {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (ialLengthOp, op_list_length α) ∈
      fref (fun _ : List α => True) (ialRel N A)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro s xs _ hs
  obtain ⟨ns, hsn, hnxs⟩ := hs
  apply NRest.param_returnT
  change s.1.length = xs.length
  rw [isMSArrayList_length hsn.1, hnxs.length_eq]

@[sepref_fref_thms] theorem ialIndexOp_refines_rel {α : Type}
    (N : ℕ) (A : α → ℕ → Assn)
    (hA : SingleValued (thePure A))
    (hAc : SingleValued (relConverse (thePure A))) :
    (ialIndexOp N, op_list_index α) ∈
      fref (fun _ : List α => True) (ialRel N A)
        (fun xs => fref (fun a : α => a ∈ xs) (thePure A)
          (fun _ => NRest.nrestRel (Set.diagonal ℕ))) := by
  intro s xs _ hs k a ha hka
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hmemEq := listRel_contains hA hAc hka hnxs
  have hk : k ∈ ns := by simpa [hmemEq] using ha
  have hidx := listRel_index hA hAc hnxs hka
  change (ialIndexOp N s k, op_list_index α xs a) ∈
    NRest.nrestRel (Set.diagonal ℕ)
  unfold ialIndexOp
  rw [listOptionSpec_eq_returnT (ialIndex_refines hsn hk)]
  simp [op_list_index, hidx]

@[sepref_fref_thms] theorem ialButlastOp_refines_rel {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (ialButlastOp N, op_list_butlast α) ∈
      fref (fun xs : List α => xs ≠ []) (ialRel N A)
        (fun _ => NRest.nrestRel (ialRel N A)) := by
  intro s xs hne hs
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hns : ns ≠ [] := (listRel_pres_ne_nil hnxs).mpr hne
  obtain ⟨t, ht, hrel⟩ := ialButlast_refines hsn hns
  simp [ialButlastOp, ht, op_list_butlast, hne]
  exact NRest.param_returnT
    ⟨listButlast ns, hrel, listRel_butlast hnxs⟩

@[sepref_fref_thms] theorem ialAppendOp_refines_rel
    (N : ℕ) (A : ℕ → ℕ → Assn) (_hPure : isPure A)
    (hbelow : IalBelowIdentity A) :
    (ialAppendOp N, op_list_append ℕ) ∈
      fref (fun _ : List ℕ => True) (ialRel N A)
        (fun xs => fref (fun a : ℕ => a < N ∧ a ∉ xs) (thePure A)
          (fun _ => NRest.nrestRel (ialRel N A))) := by
  intro s xs _ hs k a ha hka
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hkaEq : k = a := hbelow k a hka
  have hnxsEq : ns = xs := listRel_eq_of_ialBelowIdentity hbelow hnxs
  have hkN : k < N := by simpa [hkaEq] using ha.1
  have hknot : k ∉ ns := by simpa [hkaEq, hnxsEq] using ha.2
  obtain ⟨t, ht, hrel⟩ := ialAppend_refines hsn hkN hknot
  simp [ialAppendOp, ht, op_list_append]
  exact NRest.param_returnT
    ⟨ns ++ [k], hrel,
      List.rel_append hnxs (List.Forall₂.cons hka List.Forall₂.nil)⟩

@[sepref_fref_thms] theorem ialGetOp_refines_rel {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (ialGetOp, op_list_get α) ∈
      fref (fun p : List α × ℕ => p.2 < p.1.length)
        (ialRel N A ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (thePure A)) := by
  rintro ⟨s, i⟩ ⟨xs, i'⟩ hi ⟨hs, hii⟩
  change i = i' at hii
  subst i'
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hni : i < ns.length := by simpa [hnxs.length_eq] using hi
  obtain ⟨n, hn⟩ := listAt?_some_of_lt hni
  obtain ⟨a, ha, hna⟩ := listOption_obtain_left
    (by simpa [hn] using listRel_at hnxs i)
  change (ialGetOp (s, i), op_list_get α (xs, i)) ∈
    NRest.nrestRel (thePure A)
  simp only [op_list_get, NRest.assert_pos hi, NRest.returnT_bindT]
  rw [listOptionSpec_eq_returnT ha]
  rw [ialGetOp, ialGet_refines hsn, listOptionSpec_eq_returnT hn]
  exact NRest.param_returnT hna

@[sepref_fref_thms] theorem ialContainsOp_refines_rel {α : Type}
    (N : ℕ) (A : α → ℕ → Assn)
    (hA : SingleValued (thePure A))
    (hAc : SingleValued (relConverse (thePure A))) :
    (ialContainsOp N, op_list_contains α) ∈
      fref (fun _ : α => True) (thePure A)
        (fun _ => fref (fun _ : List α => True) (ialRel N A)
          (fun _ => NRest.nrestRel (Set.diagonal Bool))) := by
  intro k a _ hka s xs _ hs
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hmem := listRel_contains hA hAc hka hnxs
  change (k ∈ ns) = (a ∈ xs) at hmem
  apply NRest.param_returnT
  change ialContains N k s = propBool (a ∈ xs)
  rw [ialContains_refines hsn k, propBool_congr hmem]

/-! ## Exact executable twins -/

abbrev IalRawState := (List ℕ × (ℕ × ℕ)) × List ℕ

noncomputable def ialPackRaw (buffer : List ℕ) (n cap : ℕ)
    (qp : List ℕ) : NRest IalRawState ECost :=
  NRest.bindT (mopPair n cap) fun md =>
    NRest.bindT (mopPair buffer md) fun ms => mopPair ms qp

noncomputable def ialSwapRaw (buffer qp : List ℕ) (n cap i j : ℕ) :
    NRest IalRawState ECost :=
  NRest.bindT (mopAget buffer i) fun xi =>
    NRest.bindT (mopAget buffer j) fun xj =>
      NRest.bindT (mopAset buffer i xj) fun buffer' =>
        NRest.bindT (mopAset buffer' j xi) fun buffer'' =>
          NRest.bindT (mopAset qp xj i) fun qp' =>
            NRest.bindT (mopAset qp' xi j) fun qp'' =>
              ialPackRaw buffer'' n cap qp''

noncomputable def ialLengthRaw (n : ℕ) : NRest ℕ ECost := mopCopy n

noncomputable def ialIndexRaw (qp : List ℕ) (k : ℕ) : NRest ℕ ECost :=
  mopAget qp k

noncomputable def ialButlastRaw (N : ℕ) (buffer qp : List ℕ)
    (n cap : ℕ) : NRest IalRawState ECost :=
  NRest.bindT (marlPred n) fun n' =>
    NRest.bindT (mopAget buffer n') fun k =>
      NRest.bindT (mopAset qp k N) fun qp' =>
        ialPackRaw buffer n' cap qp'

noncomputable def ialAppendRaw (buffer qp : List ℕ) (n cap k : ℕ) :
    NRest IalRawState ECost :=
  NRest.bindT (mopCopy n) fun oldLen =>
    NRest.bindT (mopAset buffer n k) fun buffer' =>
      NRest.bindT (mopBinop .add n 1) fun n' =>
        NRest.bindT (mopAset qp k oldLen) fun qp' =>
          ialPackRaw buffer' n' cap qp'

noncomputable def ialGetRaw (buffer : List ℕ) (i : ℕ) : NRest ℕ ECost :=
  mopAget buffer i

noncomputable def ialContainsRaw (N : ℕ) (qp : List ℕ) (k : ℕ) :
    NRest ℕ ECost :=
  irIf (decide (k < N))
    (NRest.bindT (mopAget qp k) fun pos =>
      irIf (decide (pos < N)) (mopConstN 1) (mopConstN 0))
    (mopConstN 0)

noncomputable def ialSwapCost : ECost :=
  irUnit Currency.aget + irUnit Currency.aget +
    irUnit Currency.aset + irUnit Currency.aset +
    irUnit Currency.aset + irUnit Currency.aset +
    irUnit Currency.skip + (irUnit Currency.skip + irUnit Currency.skip)
noncomputable def ialLengthCost : ECost := irUnit Currency.copy
noncomputable def ialIndexCost : ECost := irUnit Currency.aget
noncomputable def ialButlastCost : ECost :=
  irUnit Currency.sub + irUnit Currency.aget + irUnit Currency.aset +
    irUnit Currency.skip + (irUnit Currency.skip + irUnit Currency.skip)
noncomputable def ialAppendCost : ECost :=
  irUnit Currency.copy + irUnit Currency.aset + irUnit Currency.add +
    irUnit Currency.aset + irUnit Currency.skip +
    (irUnit Currency.skip + irUnit Currency.skip)
noncomputable def ialGetCost : ECost := irUnit Currency.aget
noncomputable def ialContainsCost (N k : ℕ) : ECost :=
  irUnit Currency.ite +
    if k < N then
      irUnit Currency.aget + irUnit Currency.ite + irUnit Currency.const
    else irUnit Currency.const

noncomputable def ialSwapExecSpec (buffer qp : List ℕ) (n cap i j : ℕ) :
    NRest IalRawState ECost :=
  NRest.consume (NRest.returnT
    (((buffer.set i buffer[j]!).set j buffer[i]!, (n, cap)),
      (qp.set buffer[j]! i).set buffer[i]! j)) ialSwapCost

noncomputable def ialLengthExecSpec (n : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT n) ialLengthCost

noncomputable def ialIndexExecSpec (qp : List ℕ) (k : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT qp[k]!) ialIndexCost

noncomputable def ialButlastExecSpec (N : ℕ) (buffer qp : List ℕ)
    (n cap : ℕ) : NRest IalRawState ECost :=
  NRest.consume (NRest.returnT
    ((buffer, (n - 1, cap)), qp.set buffer[n - 1]! N)) ialButlastCost

noncomputable def ialAppendExecSpec (buffer qp : List ℕ) (n cap k : ℕ) :
    NRest IalRawState ECost :=
  NRest.consume (NRest.returnT
    ((buffer.set n k, (n + 1, cap)), qp.set k n)) ialAppendCost

noncomputable def ialGetExecSpec (buffer : List ℕ) (i : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT buffer[i]!) ialGetCost

noncomputable def ialContainsExecSpec (N : ℕ) (qp : List ℕ) (k : ℕ) :
    NRest ℕ ECost :=
  NRest.consume (NRest.returnT
    (if k < N then if qp[k]! < N then 1 else 0 else 0))
    (ialContainsCost N k)

theorem ialPackRaw_eq (buffer : List ℕ) (n cap : ℕ) (qp : List ℕ) :
    ialPackRaw buffer n cap qp = NRest.consume
      (NRest.returnT ((buffer, (n, cap)), qp))
      (irUnit Currency.skip + (irUnit Currency.skip + irUnit Currency.skip)) := by
  simp [ialPackRaw, mopPair_def,
    Lax13Proofs.Refine.Iicf.bindT_unit, NRest.consume_consume]

theorem ialSwapRaw_eq (buffer qp : List ℕ) (n cap i j : ℕ)
    (hi : i < buffer.length) (hj : j < buffer.length)
    (hqi : buffer[i]! < qp.length) (hqj : buffer[j]! < qp.length) :
    ialSwapRaw buffer qp n cap i j =
      ialSwapExecSpec buffer qp n cap i j := by
  have hqj0 : buffer[j]?.getD 0 < qp.length := by
    simpa [List.getElem?_eq_getElem hj, getElem!_pos, hj] using hqj
  have hqi0 : buffer[i]?.getD 0 < qp.length := by
    simpa [List.getElem?_eq_getElem hi, getElem!_pos, hi] using hqi
  simp [ialSwapRaw, ialSwapExecSpec, ialSwapCost, ialPackRaw,
    mopAget_def, mopAset_def, NRest.assert_pos hi, NRest.assert_pos hj,
    hqj0, hqi0,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def,
    NRest.consume_consume]
  ac_rfl

theorem ialLengthRaw_eq (n : ℕ) :
    ialLengthRaw n = ialLengthExecSpec n := by
  simp [ialLengthRaw, ialLengthExecSpec, ialLengthCost, mopCopy_def]

theorem ialIndexRaw_eq (qp : List ℕ) (k : ℕ) (hk : k < qp.length) :
    ialIndexRaw qp k = ialIndexExecSpec qp k := by
  simp [ialIndexRaw, ialIndexExecSpec, ialIndexCost, mopAget_def,
    NRest.assert_pos hk]

theorem ialButlastRaw_eq (N : ℕ) (buffer qp : List ℕ) (n cap : ℕ)
    (hn : n ≠ 0) (hlen : n ≤ buffer.length)
    (hq : buffer[n - 1]! < qp.length) :
    ialButlastRaw N buffer qp n cap =
      ialButlastExecSpec N buffer qp n cap := by
  have hi : n - 1 < buffer.length := by omega
  have hq0 : buffer[n - 1]?.getD 0 < qp.length := by
    simpa [List.getElem?_eq_getElem hi, getElem!_pos, hi] using hq
  simp [ialButlastRaw, ialButlastExecSpec, ialButlastCost, ialPackRaw,
    marlPred, mopBinop_def, Imp.Bop.apply_sub, binopCurrency_sub, mopAget_def,
    mopAset_def, NRest.assert_pos hi, hq0,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def,
    NRest.consume_consume]
  ac_rfl

theorem ialAppendRaw_eq (buffer qp : List ℕ) (n cap k : ℕ)
    (hn : n < buffer.length) (hk : k < qp.length) :
    ialAppendRaw buffer qp n cap k =
      ialAppendExecSpec buffer qp n cap k := by
  simp [ialAppendRaw, ialAppendExecSpec, ialAppendCost, ialPackRaw,
    mopCopy_def, mopAset_def, mopBinop_def, Imp.Bop.apply_add,
    binopCurrency_add, NRest.assert_pos hn, NRest.assert_pos hk,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def,
    NRest.consume_consume]
  ac_rfl

theorem ialGetRaw_eq (buffer : List ℕ) (i : ℕ) (hi : i < buffer.length) :
    ialGetRaw buffer i = ialGetExecSpec buffer i := by
  simp [ialGetRaw, ialGetExecSpec, ialGetCost, mopAget_def,
    NRest.assert_pos hi]

theorem ialContainsRaw_eq (N : ℕ) (qp : List ℕ) (k : ℕ)
    (hqp : qp.length = N) :
    ialContainsRaw N qp k = ialContainsExecSpec N qp k := by
  by_cases hk : k < N
  · have hkq : k < qp.length := by simpa [hqp] using hk
    by_cases hp : qp[k]! < N
    · have hp0 : qp[k]?.getD 0 < N := by
        simpa [List.getElem?_eq_getElem hkq, getElem!_pos, hkq] using hp
      simp [ialContainsRaw, ialContainsExecSpec, ialContainsCost, hk, hp0,
        irIf_true, mopAget_def, NRest.assert_pos hkq, mopConstN,
        Lax13Proofs.Refine.Iicf.bindT_unit, NRest.consume_consume]
      ac_rfl
    · have hp0 : ¬ qp[k]?.getD 0 < N := by
        simpa [List.getElem?_eq_getElem hkq, getElem!_pos, hkq] using hp
      simp [ialContainsRaw, ialContainsExecSpec, ialContainsCost, hk, hp0,
        irIf_true, irIf_false, mopAget_def, NRest.assert_pos hkq, mopConstN,
        Lax13Proofs.Refine.Iicf.bindT_unit, NRest.consume_consume]
      ac_rfl
  · simp [ialContainsRaw, ialContainsExecSpec, ialContainsCost, hk,
      irIf_false, mopConstN, NRest.consume_consume]

sepref_synth ialLengthSynth (len out : String) (n : ℕ) :
  hnRefine (hnCtxt natAssn n len ∗ junkCell out)
    _ _ out natAssn (ialLengthRaw n)

sepref_synth ialIndexSynth (Q key out : String) (qp : List ℕ) (k : ℕ) :
  hnRefine (hnCtxt arrayAssn qp Q ∗ hnCtxt natAssn k key ∗ junkCell out)
    _ _ out natAssn (ialIndexRaw qp k)

sepref_synth ialGetSynth (A idx out : String) (buffer : List ℕ) (i : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗ junkCell out)
    _ _ out natAssn (ialGetRaw buffer i)

sepref_synth ialAppendSynth
    (A Q len cap key one oldLen : String)
    (buffer qp : List ℕ) (n c k : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt arrayAssn qp Q ∗
      hnCtxt natAssn n len ∗ hnCtxt natAssn c cap ∗
      hnCtxt natAssn k key ∗ hnCtxt natAssn 1 one ∗ junkCell oldLen)
    _ _ ((A, (len, cap)), Q)
      ((arrayAssn ×ₐ natAssn ×ₐ natAssn) ×ₐ arrayAssn)
    (ialAppendRaw buffer qp n c k)

sepref_synth ialButlastSynth
    (A Q len cap maxCell one key : String)
    (N : ℕ) (buffer qp : List ℕ) (n c : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt arrayAssn qp Q ∗
      hnCtxt natAssn n len ∗ hnCtxt natAssn c cap ∗
      hnCtxt natAssn N maxCell ∗ hnCtxt natAssn 1 one ∗ junkCell key)
    _ _ ((A, (len, cap)), Q)
      ((arrayAssn ×ₐ natAssn ×ₐ natAssn) ×ₐ arrayAssn)
    (ialButlastRaw N buffer qp n c)

sepref_synth ialSwapSynth
    (A Q len cap I J XI XJ : String)
    (buffer qp : List ℕ) (n c i j : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt arrayAssn qp Q ∗
      hnCtxt natAssn n len ∗ hnCtxt natAssn c cap ∗
      hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
      junkCell XI ∗ junkCell XJ)
    _ _ ((A, (len, cap)), Q)
      ((arrayAssn ×ₐ natAssn ×ₐ natAssn) ×ₐ arrayAssn)
    (ialSwapRaw buffer qp n c i j)

set_option maxHeartbeats 800000 in
sepref_synth ialContainsSynth
    (Q maxCell key pos out : String) (N : ℕ) (qp : List ℕ) (k : ℕ) :
  hnRefine (hnCtxt arrayAssn qp Q ∗ hnCtxt natAssn N maxCell ∗
      hnCtxt natAssn k key ∗ junkCell pos ∗ junkCell out)
    _ _ out natAssn (ialContainsRaw N qp k)

def ialLengthCom (len out : String) : Com := .copy out len

def ialIndexCom (Q key out : String) : Com := .aget out Q key

def ialGetCom (A idx out : String) : Com := .aget out A idx

def ialAppendCom (A Q len _cap key one oldLen : String) : Com :=
  (Com.copy oldLen len).seq
    ((Com.aset A len key).seq
      ((Com.binop .add len len one).seq
        ((Com.aset Q key oldLen).seq (Com.skip.seq (Com.skip.seq Com.skip)))))

def ialButlastCom (A Q len _cap maxCell one key : String) : Com :=
  (Com.binop .sub len len one).seq
    ((Com.aget key A len).seq
      ((Com.aset Q key maxCell).seq (Com.skip.seq (Com.skip.seq Com.skip))))

def ialSwapCom (A Q _len _cap I J XI XJ : String) : Com :=
  (Com.aget XI A I).seq
    ((Com.aget XJ A J).seq
      ((Com.aset A I XJ).seq
        ((Com.aset A J XI).seq
          ((Com.aset Q XJ I).seq
            ((Com.aset Q XI J).seq (Com.skip.seq (Com.skip.seq Com.skip)))))))

def ialContainsCom (Q maxCell key pos out : String) : Com :=
  Com.ite (Cond.lt (Operand.cell key) (Operand.cell maxCell))
    ((Com.aget pos Q key).seq
      (Com.ite (Cond.lt (Operand.cell pos) (Operand.cell maxCell))
        (Com.const out 1) (Com.const out 0)))
    (Com.const out 0)

@[sepref_fr_rules] theorem ialLength_exec_hnr (len out : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ junkCell out)
      (ialLengthCom len out) (hnCtxt natAssn n len) out natAssn
      (ialLengthExecSpec n) := by
  rw [← ialLengthRaw_eq n]
  exact ialLengthSynth len out n

@[sepref_fr_rules] theorem ialIndex_exec_hnr
    (Q key out : String) (qp : List ℕ) (k : ℕ) (hk : k < qp.length) :
    hnRefine (hnCtxt arrayAssn qp Q ∗ hnCtxt natAssn k key ∗ junkCell out)
      (ialIndexCom Q key out)
      (hnCtxt arrayAssn qp Q ∗ hnCtxt natAssn k key)
      out natAssn (ialIndexExecSpec qp k) := by
  rw [← ialIndexRaw_eq qp k hk]
  exact ialIndexSynth Q key out qp k

@[sepref_fr_rules] theorem ialGet_exec_hnr
    (A idx out : String) (buffer : List ℕ) (i : ℕ) (hi : i < buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗ junkCell out)
      (ialGetCom A idx out)
      (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx)
      out natAssn (ialGetExecSpec buffer i) := by
  rw [← ialGetRaw_eq buffer i hi]
  exact ialGetSynth A idx out buffer i

@[sepref_fr_rules] theorem ialAppend_exec_hnr
    (A Q len cap key one oldLen : String)
    (buffer qp : List ℕ) (n c k : ℕ)
    (hn : n < buffer.length) (hk : k < qp.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt arrayAssn qp Q ∗
        hnCtxt natAssn n len ∗ hnCtxt natAssn c cap ∗
        hnCtxt natAssn k key ∗ hnCtxt natAssn 1 one ∗ junkCell oldLen)
      (ialAppendCom A Q len cap key one oldLen)
      (hnCtxt natAssn k key ∗ junkCell oldLen ∗ hnCtxt natAssn 1 one)
      ((A, (len, cap)), Q)
      ((arrayAssn ×ₐ natAssn ×ₐ natAssn) ×ₐ arrayAssn)
      (ialAppendExecSpec buffer qp n c k) := by
  rw [← ialAppendRaw_eq buffer qp n c k hn hk]
  exact ialAppendSynth A Q len cap key one oldLen buffer qp n c k

@[sepref_fr_rules] theorem ialButlast_exec_hnr
    (A Q len cap maxCell one key : String)
    (N : ℕ) (buffer qp : List ℕ) (n c : ℕ)
    (hn : n ≠ 0) (hlen : n ≤ buffer.length)
    (hq : buffer[n - 1]! < qp.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt arrayAssn qp Q ∗
        hnCtxt natAssn n len ∗ hnCtxt natAssn c cap ∗
        hnCtxt natAssn N maxCell ∗ hnCtxt natAssn 1 one ∗ junkCell key)
      (ialButlastCom A Q len cap maxCell one key)
      (junkCell key ∗ hnCtxt natAssn N maxCell ∗ hnCtxt natAssn 1 one)
      ((A, (len, cap)), Q)
      ((arrayAssn ×ₐ natAssn ×ₐ natAssn) ×ₐ arrayAssn)
      (ialButlastExecSpec N buffer qp n c) := by
  rw [← ialButlastRaw_eq N buffer qp n c hn hlen hq]
  exact ialButlastSynth A Q len cap maxCell one key N buffer qp n c

@[sepref_fr_rules] theorem ialSwap_exec_hnr
    (A Q len cap I J XI XJ : String)
    (buffer qp : List ℕ) (n c i j : ℕ)
    (hi : i < buffer.length) (hj : j < buffer.length)
    (hqi : buffer[i]! < qp.length) (hqj : buffer[j]! < qp.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt arrayAssn qp Q ∗
        hnCtxt natAssn n len ∗ hnCtxt natAssn c cap ∗
        hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell XI ∗ junkCell XJ)
      (ialSwapCom A Q len cap I J XI XJ)
      (junkCell XI ∗ hnCtxt natAssn j J ∗ junkCell XJ ∗ hnCtxt natAssn i I)
      ((A, (len, cap)), Q)
      ((arrayAssn ×ₐ natAssn ×ₐ natAssn) ×ₐ arrayAssn)
      (ialSwapExecSpec buffer qp n c i j) := by
  rw [← ialSwapRaw_eq buffer qp n c i j hi hj hqi hqj]
  exact ialSwapSynth A Q len cap I J XI XJ buffer qp n c i j

@[sepref_fr_rules] theorem ialContains_exec_hnr
    (Q maxCell key pos out : String) (N : ℕ) (qp : List ℕ) (k : ℕ)
    (hqp : qp.length = N) :
    hnRefine (hnCtxt arrayAssn qp Q ∗ hnCtxt natAssn N maxCell ∗
        hnCtxt natAssn k key ∗ junkCell pos ∗ junkCell out)
      (ialContainsCom Q maxCell key pos out)
      (junkCell pos ∗ hnCtxt arrayAssn qp Q ∗ hnCtxt natAssn k key ∗
        hnCtxt natAssn N maxCell)
      out natAssn (ialContainsExecSpec N qp k) := by
  rw [← ialContainsRaw_eq N qp k hqp]
  exact ialContainsSynth Q maxCell key pos out N qp k

/-! ## Executable/list bridges -/

theorem ialLengthExecSpec_refines {N : ℕ} {s : IndexedArrayList}
    {l : List ℕ} (hs : (s, l) ∈ ialRel1 N) :
    ialLengthExecSpec s.1.length =
      NRest.consume (NRest.returnT l.length) ialLengthCost := by
  rw [ialLengthExecSpec, isMSArrayList_length hs.1]

theorem ialIndexExecSpec_refines {N : ℕ} {s : IndexedArrayList}
    {l : List ℕ} (hs : (s, l) ∈ ialRel1 N) {k : ℕ} (hk : k ∈ l) :
    ialIndexExecSpec s.2 k =
      NRest.consume (NRest.returnT (listIndex l k)) ialIndexCost := by
  simp [ialIndexExecSpec, hs.2.lookup_index hk]

theorem ialGetExecSpec_refines {N : ℕ} {s : IndexedArrayList}
    {l : List ℕ} (hs : (s, l) ∈ ialRel1 N) {i : ℕ} (hi : i < l.length) :
    ialGetExecSpec s.1.buffer i =
      NRest.consume (NRest.returnT l[i]!) ialGetCost := by
  have hne : l ≠ [] := by
    intro hl
    rw [hl] at hi
    exact Nat.not_lt_zero i hi
  have hwf := ial_state_wf_of_nonempty hs.1 hne
  have his : i < s.1.length := by
    rw [isMSArrayList_length hs.1]
    exact hi
  have hb := buffer_getElem_eq_active hwf his
  rw [hs.1.2.2.2] at hb
  simp [ialGetExecSpec, hb]

theorem ialAppendExecSpec_refines {N : ℕ} {s : IndexedArrayList}
    {l : List ℕ} (hs : (s, l) ∈ ialRel1 N) {k : ℕ}
    (hk : k < N) (hnot : k ∉ l) :
    ialAppendExecSpec s.1.buffer s.2 s.1.length s.1.capacity k =
        NRest.consume (NRest.returnT
          ((s.1.buffer.set s.1.length k, (s.1.length + 1, s.1.capacity)),
            s.2.set k s.1.length)) ialAppendCost ∧
      ((⟨s.1.buffer.set s.1.length k, s.1.length + 1, s.1.capacity⟩,
          s.2.set k s.1.length), l ++ [k]) ∈ ialRel1 N := by
  refine ⟨rfl, ?_⟩
  obtain ⟨t, ht, hrel⟩ := ialAppend_refines hs hk hnot
  have hactive : s.1.active = l := hs.1.2.2.2
  have hexec : ialAppend N s k = some
      (⟨s.1.buffer.set s.1.length k, s.1.length + 1, s.1.capacity⟩,
        s.2.set k s.1.length) := by
    simp [ialAppend, hk, hnot, hactive]
  rw [hexec] at ht
  exact Option.some.inj ht ▸ hrel

theorem ialButlastExecSpec_refines {N : ℕ} {s : IndexedArrayList}
    {l : List ℕ} (hs : (s, l) ∈ ialRel1 N) (hne : l ≠ []) :
    ialButlastExecSpec N s.1.buffer s.2 s.1.length s.1.capacity =
        NRest.consume (NRest.returnT
          ((s.1.buffer, (s.1.length - 1, s.1.capacity)),
            s.2.set s.1.buffer[s.1.length - 1]! N)) ialButlastCost ∧
      ((⟨s.1.buffer, s.1.length - 1, s.1.capacity⟩,
          s.2.set s.1.buffer[s.1.length - 1]! N), listButlast l) ∈ ialRel1 N := by
  refine ⟨rfl, ?_⟩
  obtain ⟨t, ht, hrel⟩ := ialButlast_refines hs hne
  have hlen : s.1.length ≠ 0 := by
    rw [isMSArrayList_length hs.1]
    exact fun hz => hne (List.eq_nil_of_length_eq_zero hz)
  have hexec : ialButlast N s = some
      (⟨s.1.buffer, s.1.length - 1, s.1.capacity⟩,
        s.2.set s.1.buffer[s.1.length - 1]! N) := by
    simp [ialButlast, hlen]
  rw [hexec] at ht
  exact Option.some.inj ht ▸ hrel

theorem ialSwapExecSpec_refines {N : ℕ} {s : IndexedArrayList}
    {l : List ℕ} (hs : (s, l) ∈ ialRel1 N) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) :
    ialSwapExecSpec s.1.buffer s.2 s.1.length s.1.capacity i j =
        NRest.consume (NRest.returnT
          ((((s.1.buffer.set i s.1.buffer[j]!).set j s.1.buffer[i]!),
              (s.1.length, s.1.capacity)),
            (s.2.set s.1.buffer[j]! i).set s.1.buffer[i]! j)) ialSwapCost ∧
      ((⟨(s.1.buffer.set i s.1.buffer[j]!).set j s.1.buffer[i]!,
            s.1.length, s.1.capacity⟩,
          (s.2.set s.1.buffer[j]! i).set s.1.buffer[i]! j),
        listSwap l i j) ∈ ialRel1 N := by
  refine ⟨rfl, ?_⟩
  obtain ⟨t, ht, hrel⟩ := ialSwap_refines hs hi hj
  have hne : l ≠ [] := by
    intro hl
    rw [hl] at hi
    exact Nat.not_lt_zero i hi
  have hwf := ial_state_wf_of_nonempty hs.1 hne
  have his : i < s.1.length := by
    rw [isMSArrayList_length hs.1]
    exact hi
  have hjs : j < s.1.length := by
    rw [isMSArrayList_length hs.1]
    exact hj
  have hbi := buffer_getElem_eq_active hwf his
  have hbj := buffer_getElem_eq_active hwf hjs
  rw [hs.1.2.2.2] at hbi hbj
  have hexec : ialSwap s i j = some
      (⟨(s.1.buffer.set i s.1.buffer[j]!).set j s.1.buffer[i]!,
          s.1.length, s.1.capacity⟩,
        (s.2.set s.1.buffer[j]! i).set s.1.buffer[i]! j) := by
    simp [ialSwap, hs.1.2.2.2, hi, hj, hbi, hbj, getElem!_pos]
  rw [hexec] at ht
  exact Option.some.inj ht ▸ hrel

theorem ialContainsExecSpec_refines {N : ℕ} {s : IndexedArrayList}
    {l : List ℕ} (hs : (s, l) ∈ ialRel1 N) (k : ℕ) :
    ialContainsExecSpec N s.2 k = NRest.consume
      (NRest.returnT (if k ∈ l then 1 else 0)) (ialContainsCost N k) := by
  simp only [ialContainsExecSpec]
  by_cases hkN : k < N
  · rw [hs.2.qp_def k hkN]
    by_cases hmem : k ∈ l
    · have hidxN : listIndex l k < N := by
        rw [listIndex_eq_idxOf]
        exact (List.idxOf_lt_length_of_mem hmem).trans_le hs.2.list_length_le
      simp [hkN, hmem, hidxN]
    · simp [hkN, hmem]
  · have hnot : k ∉ l := fun hmem => hkN (hs.2.list_bounded k hmem)
    simp [hkN, hnot]

/-! ## Command, budget, registration, and database gates -/

#guard ialLengthCom "len" "out" = .copy "out" "len"
#guard ialIndexCom "Q" "key" "out" = .aget "out" "Q" "key"
#guard ialGetCom "A" "idx" "out" = .aget "out" "A" "idx"
#guard ialAppendCom "A" "Q" "len" "cap" "key" "one" "old" =
  (Com.copy "old" "len").seq
    ((Com.aset "A" "len" "key").seq
      ((Com.binop .add "len" "len" "one").seq
        ((Com.aset "Q" "key" "old").seq
          (Com.skip.seq (Com.skip.seq Com.skip)))))
#guard ialButlastCom "A" "Q" "len" "cap" "N" "one" "key" =
  (Com.binop .sub "len" "len" "one").seq
    ((Com.aget "key" "A" "len").seq
      ((Com.aset "Q" "key" "N").seq
        (Com.skip.seq (Com.skip.seq Com.skip))))
#guard ialSwapCom "A" "Q" "len" "cap" "i" "j" "xi" "xj" =
  (Com.aget "xi" "A" "i").seq
    ((Com.aget "xj" "A" "j").seq
      ((Com.aset "A" "i" "xj").seq
        ((Com.aset "A" "j" "xi").seq
          ((Com.aset "Q" "xj" "i").seq
            ((Com.aset "Q" "xi" "j").seq
              (Com.skip.seq (Com.skip.seq Com.skip)))))))
#guard ialContainsCom "Q" "N" "key" "pos" "out" =
  Com.ite (.lt (.cell "key") (.cell "N"))
    ((Com.aget "pos" "Q" "key").seq
      (Com.ite (.lt (.cell "pos") (.cell "N"))
        (.const "out" 1) (.const "out" 0)))
    (.const "out" 0)

theorem ialSwapCost_aget : ialSwapCost.toFun Currency.aget = 2 := by decide +kernel
theorem ialSwapCost_aset : ialSwapCost.toFun Currency.aset = 4 := by decide +kernel
theorem ialSwapCost_skip : ialSwapCost.toFun Currency.skip = 3 := by decide +kernel
theorem ialLengthCost_copy : ialLengthCost.toFun Currency.copy = 1 := by decide +kernel
theorem ialIndexCost_aget : ialIndexCost.toFun Currency.aget = 1 := by decide +kernel
theorem ialButlastCost_sub : ialButlastCost.toFun Currency.sub = 1 := by decide +kernel
theorem ialButlastCost_aget : ialButlastCost.toFun Currency.aget = 1 := by decide +kernel
theorem ialButlastCost_aset : ialButlastCost.toFun Currency.aset = 1 := by decide +kernel
theorem ialButlastCost_skip : ialButlastCost.toFun Currency.skip = 3 := by decide +kernel
theorem ialAppendCost_copy : ialAppendCost.toFun Currency.copy = 1 := by decide +kernel
theorem ialAppendCost_aset : ialAppendCost.toFun Currency.aset = 2 := by decide +kernel
theorem ialAppendCost_add : ialAppendCost.toFun Currency.add = 1 := by decide +kernel
theorem ialAppendCost_skip : ialAppendCost.toFun Currency.skip = 3 := by decide +kernel
theorem ialGetCost_aget : ialGetCost.toFun Currency.aget = 1 := by decide +kernel
theorem ialContainsCost_const (N k : ℕ) :
    (ialContainsCost N k).toFun Currency.const = 1 := by
  by_cases h : k < N <;>
    simp [ialContainsCost, irUnit, h, ACost.toFun_add, ACost.toFun_cost] <;>
    decide +kernel
theorem ialContainsCost_aget (N k : ℕ) :
    (ialContainsCost N k).toFun Currency.aget = if k < N then 1 else 0 := by
  by_cases h : k < N <;>
    simp [ialContainsCost, irUnit, h, ACost.toFun_add, ACost.toFun_cost] <;>
    decide +kernel
theorem ialContainsCost_ite (N k : ℕ) :
    (ialContainsCost N k).toFun Currency.ite = if k < N then 2 else 1 := by
  by_cases h : k < N <;>
    simp [ialContainsCost, irUnit, h, ACost.toFun_add, ACost.toFun_cost] <;>
    decide +kernel

example : opIalEmptySz ::ᵢ (ℕ → NRest (ListI ℕ) ECost) := opIalEmptySz_itype

run_cmd do
  let frefs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``ialSwapOp_refines_rel, ``ialLengthOp_refines_rel,
      ``ialIndexOp_refines_rel, ``ialButlastOp_refines_rel,
      ``ialAppendOp_refines_rel, ``ialGetOp_refines_rel,
      ``ialContainsOp_refines_rel] do
    unless frefs.contains n do
      throwError "indexed-array-list source rule missing from DB: {n}"
  let frules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  for n in #[``ialSwap_exec_hnr, ``ialLength_exec_hnr,
      ``ialIndex_exec_hnr, ``ialButlast_exec_hnr, ``ialAppend_exec_hnr,
      ``ialGet_exec_hnr, ``ialContains_exec_hnr] do
    unless frules.contains n do
      throwError "indexed-array-list executable rule missing from DB: {n}"

/-! ## Kernel-three gates -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.IalInvar.swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IalInvar.swap

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.ialAppend_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ialAppend_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.ialContains_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ialContains_exec_hnr

/-! ## Executable examples, including the sentinel and update cases -/

def ialExample : IndexedArrayList :=
  (⟨[1, 3, 0, 0, 0], 2, 5⟩, [5, 0, 5, 1, 5])

#guard ialContains 5 1 ialExample
#guard ialContains 5 2 ialExample = false
#guard ialContains 5 7 ialExample = false
#guard ialAppend 5 ialExample 4 =
  some (⟨[1, 3, 4, 0, 0], 3, 5⟩, [5, 0, 5, 1, 2])
#guard ialButlast 5 ialExample =
  some (⟨[1, 3, 0, 0, 0], 1, 5⟩, [5, 0, 5, 5, 5])
#guard ialSwap ialExample 0 1 =
  some (⟨[3, 1, 0, 0, 0], 2, 5⟩, [5, 1, 5, 0, 5])

end Lax13Proofs.Refine.Sepref.Iicf
