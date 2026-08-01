import Lax13Proofs.Refine.Iicf.Impl.ArrayList

/-!
# Fixed-maximum-size array lists

Adaptation of Sepreftime's `IICF_MS_Array_List.thy` at commit
`c1c987b45ec886d289ba215768182ac87b82f20d`.

The source representation is an array of fixed physical size `N` paired with
a logical length.  Here the bounded-array carrier retains an explicit capacity
cell, and the relation pins both that cell and the physical buffer length to
`N`.  Empty construction is a pure model/caller-owned establishment boundary:
there is deliberately no allocation command or allocation HNR rule.

Every nonallocating source operation has a cost-silent List refinement and an
exact executable budget twin.  The fixed-capacity append is only array-set plus
length increment; butlast only decrements length.  In particular neither path
uses dynamic growth or shrink branches.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

abbrev MSArrayList := BoundedArray

/-! ## Representation, precision, and composed assertion -/

def isMSArrayList (N : ℕ) : Set (MSArrayList × List ℕ) :=
  {p | p.1.buffer.length = N ∧ p.1.length ≤ N ∧
    p.1.capacity = N ∧ p.1.active = p.2}

@[simp] theorem mem_isMSArrayList_iff {N : ℕ} {s : MSArrayList} {xs : List ℕ} :
    (s, xs) ∈ isMSArrayList N ↔
      s.buffer.length = N ∧ s.length ≤ N ∧ s.capacity = N ∧ s.active = xs := Iff.rfl

/-- Precision analogue: a represented concrete state determines one list. -/
theorem isMSArrayList_singleValued (N : ℕ) : SingleValued (isMSArrayList N) := by
  intro s xs ys hx hy
  exact hx.2.2.2.symm.trans hy.2.2.2

theorem isMSArrayList_length {N : ℕ} {s : MSArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ isMSArrayList N) : s.length = xs.length := by
  change s.buffer.length = N ∧ s.length ≤ N ∧
    s.capacity = N ∧ s.active = xs at h
  rw [← h.2.2.2]
  simp [BoundedArray.active, Nat.min_eq_left (h.2.1.trans_eq h.1.symm)]

def msArrayListAssn (N : ℕ) :
    List ℕ → String × String × String → Assn :=
  hrComp boundedArrayAssn (isMSArrayList N)

@[intf_of_assn] theorem msArrayListAssn_intf (N : ℕ) :
    intfOfAssn (msArrayListAssn N) (ListI ℕ) := trivial

def marlRel {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    Set (MSArrayList × List α) :=
  relComp (isMSArrayList N) (listRel (thePure A))

/-- Source `marl_assn N A = hr_comp (is_ms_array_list N)
    (<the_pure A>list_rel)`. -/
def marlAssn {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    List α → String × String × String → Assn :=
  hrComp (msArrayListAssn N) (listRel (thePure A))

@[intf_of_assn] theorem marlAssn_intf {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) : intfOfAssn (marlAssn N A) (ListI α) := trivial

theorem marl_assn_combined {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    marlAssn N A = hrComp boundedArrayAssn (marlRel N A) := by
  rw [marlAssn, msArrayListAssn, marlRel, hr_comp_assoc]

/-! ## Empty-size: pure and caller-owned only -/

def marlEmptyModel (N : ℕ) : MSArrayList :=
  ⟨List.replicate N 0, 0, N⟩

def marlEmptyIn (N : ℕ) (buffer : List ℕ) : Option MSArrayList :=
  if buffer.length = N then some ⟨buffer, 0, N⟩ else none

@[simp] theorem marlEmptyModel_refines (N : ℕ) :
    (marlEmptyModel N, []) ∈ isMSArrayList N := by
  simp [isMSArrayList, marlEmptyModel, BoundedArray.active]

theorem marlEmptyIn_some {N : ℕ} {buffer : List ℕ} {s : MSArrayList}
    (h : marlEmptyIn N buffer = some s) : (s, []) ∈ isMSArrayList N := by
  simp only [marlEmptyIn] at h
  split at h
  · rename_i hN
    simp only [Option.some.injEq] at h
    subst s
    simp [isMSArrayList, hN, BoundedArray.active]
  · contradiction

noncomputable def opMarlEmptySz (_N : ℕ) : NRest (List ℕ) ECost :=
  op_list_empty ℕ

sepref_register opMarlEmptySz : opMarlEmptySz as
  (ℕ → NRest (ListI ℕ) ECost)

theorem marl_fold_custom_empty_sz (N : ℕ) :
    op_list_empty ℕ = opMarlEmptySz N := rfl

theorem marl_custom_empty_identity (N : ℕ) :
    opMarlEmptySz N = NRest.returnT [] := rfl

noncomputable def marlEmptyOp (N : ℕ) : NRest MSArrayList ECost :=
  NRest.returnT (marlEmptyModel N)

theorem marlEmptyOp_refines (N : ℕ) :
    (marlEmptyOp N, opMarlEmptySz N) ∈
      NRest.nrestRel (isMSArrayList N) := by
  exact NRest.param_returnT (marlEmptyModel_refines N)

theorem marlEmptyOp_refines_rel {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    (marlEmptyOp N, op_list_empty α) ∈ NRest.nrestRel (marlRel N A) := by
  exact NRest.param_returnT
    ⟨[], marlEmptyModel_refines N, mem_listRel_nil⟩

/-! ## Fixed-capacity value operations -/

def marlAppend (N : ℕ) (s : MSArrayList) (x : ℕ) : Option MSArrayList :=
  if s.length < N then
    some ⟨s.buffer.set s.length x, s.length + 1, N⟩
  else none

def marlLength (s : MSArrayList) : ℕ := s.length
def marlIsEmpty (s : MSArrayList) : Bool := decide (s.length = 0)
def marlLast? (s : MSArrayList) : Option ℕ := listAt? s.active.reverse 0
def marlGet? (s : MSArrayList) (i : ℕ) : Option ℕ := listAt? s.active i

def marlButlast (s : MSArrayList) : Option MSArrayList :=
  if s.length = 0 then none else some ⟨s.buffer, s.length - 1, s.capacity⟩

def marlSet (s : MSArrayList) (i x : ℕ) : Option MSArrayList :=
  if i < s.length then some ⟨s.buffer.set i x, s.length, s.capacity⟩ else none

private theorem take_set_self_ms (buffer : List ℕ) (n x : ℕ) :
    (buffer.set n x).take n = buffer.take n := by
  induction buffer generalizing n with
  | nil => simp
  | cons y ys ih =>
      cases n <;> simp [ih]

private theorem take_succ_set (buffer : List ℕ) (n x : ℕ)
    (h : n < buffer.length) :
    (buffer.set n x).take (n + 1) = buffer.take n ++ [x] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using h),
    take_set_self_ms]
  simp

private theorem take_pred_eq_butlast_ms (buffer : List ℕ) {n : ℕ}
    (hn : n ≤ buffer.length) :
    buffer.take (n - 1) = listButlast (buffer.take n) := by
  have ht : (buffer.take n).length = n := by simp [Nat.min_eq_left hn]
  have hdrop : (buffer.take n).dropLast = buffer.take (n - 1) := by
    rw [List.dropLast_eq_take, ht, List.take_take,
      Nat.min_eq_left (Nat.sub_le n 1)]
  simpa [listButlast, List.dropLast] using hdrop.symm

theorem marlAppend_some_refines {N : ℕ} {s t : MSArrayList}
    {xs : List ℕ} {x : ℕ} (hs : (s, xs) ∈ isMSArrayList N)
    (hp : marlAppend N s x = some t) :
    (t, xs ++ [x]) ∈ isMSArrayList N := by
  change s.buffer.length = N ∧ s.length ≤ N ∧
    s.capacity = N ∧ s.active = xs at hs
  simp only [marlAppend] at hp
  split at hp
  · rename_i hspace
    simp only [Option.some.injEq] at hp
    subst t
    change (s.buffer.set s.length x).length = N ∧ s.length + 1 ≤ N ∧
      N = N ∧ (s.buffer.set s.length x).take (s.length + 1) = xs ++ [x]
    refine ⟨by simpa using hs.1, by omega, rfl, ?_⟩
    have hactive : s.buffer.take s.length = xs := hs.2.2.2
    rw [take_succ_set s.buffer s.length x (by omega), hactive]
  · contradiction

theorem marlButlast_some_refines {N : ℕ} {s t : MSArrayList}
    {xs : List ℕ} (hs : (s, xs) ∈ isMSArrayList N)
    (hp : marlButlast s = some t) :
    (t, listButlast xs) ∈ isMSArrayList N := by
  change s.buffer.length = N ∧ s.length ≤ N ∧
    s.capacity = N ∧ s.active = xs at hs
  simp only [marlButlast] at hp
  split at hp
  · contradiction
  · rename_i hne
    simp only [Option.some.injEq] at hp
    subst t
    change s.buffer.length = N ∧ s.length - 1 ≤ N ∧
      s.capacity = N ∧ s.buffer.take (s.length - 1) = listButlast xs
    refine ⟨hs.1, by omega, hs.2.2.1, ?_⟩
    have hactive : s.buffer.take s.length = xs := hs.2.2.2
    rw [← hactive]
    apply take_pred_eq_butlast_ms
    omega

theorem marlSet_some_refines {N : ℕ} {s t : MSArrayList}
    {xs : List ℕ} {i x : ℕ} (hs : (s, xs) ∈ isMSArrayList N)
    (hp : marlSet s i x = some t) :
    (t, listSet xs i x) ∈ isMSArrayList N := by
  change s.buffer.length = N ∧ s.length ≤ N ∧
    s.capacity = N ∧ s.active = xs at hs
  simp only [marlSet] at hp
  split at hp
  · rename_i hi
    simp only [Option.some.injEq] at hp
    subst t
    change (s.buffer.set i x).length = N ∧ s.length ≤ N ∧
      s.capacity = N ∧ (s.buffer.set i x).take s.length = listSet xs i x
    refine ⟨by simpa using hs.1, hs.2.1, hs.2.2.1, ?_⟩
    have hactive : s.buffer.take s.length = xs := hs.2.2.2
    rw [List.take_set, hactive, listSet_eq_set]
  · contradiction

theorem marlLength_refines {N : ℕ} {s : MSArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ isMSArrayList N) : marlLength s = xs.length :=
  isMSArrayList_length h

theorem marlIsEmpty_refines {N : ℕ} {s : MSArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ isMSArrayList N) : marlIsEmpty s = propBool (xs = []) := by
  apply Bool.eq_iff_iff.mpr
  simp [marlIsEmpty, propBool, isMSArrayList_length h]

@[simp] theorem marlLast_refines {N : ℕ} {s : MSArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ isMSArrayList N) :
    marlLast? s = listAt? xs.reverse 0 := by simp [marlLast?, h.2.2.2]

@[simp] theorem marlGet_refines {N : ℕ} {s : MSArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ isMSArrayList N) (i : ℕ) :
    marlGet? s i = listAt? xs i := by simp [marlGet?, h.2.2.2]

/-! ## Source-shaped List refinement rules -/

def marlReadyRel {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    Set (MSArrayList × List α) :=
  {p | (p.1, p.2) ∈ marlRel N A ∧ p.1.length < N}

noncomputable def marlAppendOp (N : ℕ) (s : MSArrayList) (x : ℕ) :
    NRest MSArrayList ECost :=
  match marlAppend N s x with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def marlLengthOp (s : MSArrayList) : NRest ℕ ECost :=
  NRest.returnT (marlLength s)

noncomputable def marlIsEmptyOp (s : MSArrayList) : NRest Bool ECost :=
  NRest.returnT (marlIsEmpty s)

noncomputable def marlLastOp (s : MSArrayList) : NRest ℕ ECost :=
  NRest.spec (fun x => marlLast? s = some x) (fun _ => 0)

noncomputable def marlButlastOp (s : MSArrayList) : NRest MSArrayList ECost :=
  match marlButlast s with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def marlGetOp (p : MSArrayList × ℕ) : NRest ℕ ECost :=
  NRest.spec (fun x => marlGet? p.1 p.2 = some x) (fun _ => 0)

noncomputable def marlSetOp (p : (MSArrayList × ℕ) × ℕ) :
    NRest MSArrayList ECost :=
  match marlSet p.1.1 p.1.2 p.2 with
  | some t => NRest.returnT t
  | none => NRest.fail

@[sepref_fref_thms] theorem marlAppendOp_refines {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) (_hA : isPure A) :
    (marlAppendOp N, op_list_append α) ∈
      fref (fun _ : List α => True) (marlReadyRel N A)
        (fun _ => thePure A →ᵣ NRest.nrestRel (marlRel N A)) := by
  intro s xs _ hs x a hxa
  obtain ⟨ns, hsn, hnxs⟩ := hs.1
  have hp : marlAppend N s x = some
      ⟨s.buffer.set s.length x, s.length + 1, N⟩ := by
    simp [marlAppend, hs.2]
  simp [marlAppendOp, hp, op_list_append]
  refine NRest.param_returnT ⟨ns ++ [x], marlAppend_some_refines hsn hp, ?_⟩
  exact List.rel_append hnxs (List.Forall₂.cons hxa List.Forall₂.nil)

@[sepref_fref_thms] theorem marlLengthOp_refines {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (marlLengthOp, op_list_length α) ∈
      fref (fun _ : List α => True) (marlRel N A)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro s xs _ hs
  obtain ⟨ns, hsn, hnxs⟩ := hs
  apply NRest.param_returnT
  change marlLength s = xs.length
  rw [marlLength, isMSArrayList_length hsn, hnxs.length_eq]

@[sepref_fref_thms] theorem marlIsEmptyOp_refines {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (marlIsEmptyOp, op_list_is_empty α) ∈
      fref (fun _ : List α => True) (marlRel N A)
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) := by
  intro s xs _ hs
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have he : (ns = []) = (xs = []) := by
    apply propext
    cases hnxs <;> simp
  apply NRest.param_returnT
  change marlIsEmpty s = propBool (xs = [])
  rw [marlIsEmpty_refines hsn, he]

@[sepref_fref_thms] theorem marlLastOp_refines {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (marlLastOp, op_list_last α) ∈
      fref (fun xs : List α => xs ≠ []) (marlRel N A)
        (fun _ => NRest.nrestRel (thePure A)) := by
  intro s xs hxs hs
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hns : ns ≠ [] := (listRel_pres_ne_nil hnxs).mpr hxs
  have hr := List.rel_reverse hnxs
  have hnlen : 0 < ns.reverse.length := by cases ns <;> simp_all
  obtain ⟨n, hn⟩ := listAt?_some_of_lt hnlen
  obtain ⟨a, ha, hna⟩ := listOption_obtain_left
    (by simpa [hn] using listRel_at hr 0)
  simp only [op_list_last, NRest.assert_pos hxs,
    NRest.returnT_bindT]
  rw [listOptionSpec_eq_returnT ha]
  rw [marlLastOp, marlLast_refines hsn, listOptionSpec_eq_returnT hn]
  exact NRest.param_returnT hna

@[sepref_fref_thms] theorem marlButlastOp_refines {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (marlButlastOp, op_list_butlast α) ∈
      fref (fun xs : List α => xs ≠ []) (marlRel N A)
        (fun _ => NRest.nrestRel (marlRel N A)) := by
  intro s xs hxs hs
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hns : ns ≠ [] := (listRel_pres_ne_nil hnxs).mpr hxs
  have hlen : s.length ≠ 0 := by
    rw [isMSArrayList_length hsn]
    simpa using hns
  have hp : marlButlast s = some ⟨s.buffer, s.length - 1, s.capacity⟩ := by
    simp [marlButlast, hlen]
  simp [marlButlastOp, hp, op_list_butlast, hxs]
  exact NRest.param_returnT
    ⟨listButlast ns, marlButlast_some_refines hsn hp, listRel_butlast hnxs⟩

@[sepref_fref_thms] theorem marlGetOp_refines {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (marlGetOp, op_list_get α) ∈
      fref (fun p : List α × ℕ => p.2 < p.1.length)
        (marlRel N A ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (thePure A)) := by
  rintro ⟨s, i⟩ ⟨xs, j⟩ hpre ⟨hs, hij⟩
  change i = j at hij
  subst j
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hni : i < ns.length := by simpa [hnxs.length_eq] using hpre
  obtain ⟨n, hn⟩ := listAt?_some_of_lt hni
  obtain ⟨a, ha, hna⟩ := listOption_obtain_left
    (by simpa [hn] using listRel_at hnxs i)
  simp only [op_list_get, NRest.assert_pos hpre,
    NRest.returnT_bindT]
  rw [listOptionSpec_eq_returnT ha]
  rw [marlGetOp, marlGet_refines hsn, listOptionSpec_eq_returnT hn]
  exact NRest.param_returnT hna

@[sepref_fref_thms] theorem marlSetOp_refines {α : Type}
    (N : ℕ) (A : α → ℕ → Assn) :
    (marlSetOp, op_list_set α) ∈
      fref (fun p : (List α × ℕ) × α => p.1.2 < p.1.1.length)
        ((marlRel N A ×ᵣ Set.diagonal ℕ) ×ᵣ thePure A)
        (fun _ => NRest.nrestRel (marlRel N A)) := by
  rintro ⟨⟨s, i⟩, x⟩ ⟨⟨xs, j⟩, a⟩ hpre ⟨⟨hs, hij⟩, hxa⟩
  change i = j at hij
  subst j
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have hni : i < ns.length := by simpa [hnxs.length_eq] using hpre
  have his : i < s.length := by
    rw [isMSArrayList_length hsn]
    exact hni
  have hp : marlSet s i x = some ⟨s.buffer.set i x, s.length, s.capacity⟩ := by
    simp [marlSet, his]
  simp [marlSetOp, hp, op_list_set, hpre]
  exact NRest.param_returnT
    ⟨listSet ns i x, marlSet_some_refines hsn hp, listRel_set hnxs hxa i⟩

/-! ## Exact executable twins -/

noncomputable def marlAppendRaw (buffer : List ℕ) (n cap x : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopAset buffer n x) fun buffer' =>
    NRest.bindT (mopBinop .add n 1) fun n' =>
      NRest.bindT (mopPair n' cap) fun md => mopPair buffer' md

noncomputable def marlPred (n : ℕ) : NRest ℕ ECost := mopBinop .sub n 1

@[sepref_fr_rules] private theorem hnr_marlPred (len one : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ hnCtxt natAssn 1 one)
      (.binop .sub len len one) (hnCtxt natAssn 1 one) len natAssn
      (marlPred n) := by
  unfold marlPred
  exact hnr_mop_binop_self .sub len one n 1

attribute [irreducible] marlPred

noncomputable def marlButlastRaw (buffer : List ℕ) (n cap : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (marlPred n) fun n' =>
    NRest.bindT (mopPair n' cap) fun md => mopPair buffer md

noncomputable def marlAppendCost : ECost :=
  irUnit Currency.aset + irUnit Currency.add + 2 • irUnit Currency.skip

noncomputable def marlButlastCost : ECost :=
  irUnit Currency.sub + 2 • irUnit Currency.skip

noncomputable abbrev marlLengthCost := arlLengthCost
noncomputable abbrev marlIsEmptyCost := arlIsEmptyCost
noncomputable abbrev marlLastCost := arlLastCost
noncomputable abbrev marlGetCost := arlGetCost
noncomputable abbrev marlSetCost := arlSetCost

noncomputable def marlAppendExecSpec (buffer : List ℕ) (n cap x : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT (buffer.set n x, (n + 1, cap))) marlAppendCost

noncomputable def marlButlastExecSpec (buffer : List ℕ) (n cap : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT (buffer, (n - 1, cap))) marlButlastCost

noncomputable abbrev marlLengthExecSpec := arlLengthExecSpec
noncomputable abbrev marlIsEmptyExecSpec := arlIsEmptyExecSpec
noncomputable abbrev marlLastExecSpec := arlLastExecSpec
noncomputable abbrev marlGetExecSpec := arlGetExecSpec
noncomputable abbrev marlSetExecSpec := arlSetExecSpec

theorem marlAppendRaw_eq (buffer : List ℕ) (n cap x : ℕ)
    (hi : n < buffer.length) :
    marlAppendRaw buffer n cap x = marlAppendExecSpec buffer n cap x := by
  simp [marlAppendRaw, marlAppendExecSpec, marlAppendCost, mopAset_def,
    NRest.assert_pos hi, Lax13Proofs.Refine.Iicf.bindT_unit, mopBinop_def,
    Imp.Bop.apply_add, binopCurrency_add, mopPair_def, NRest.consume_consume,
    two_nsmul]
  ac_rfl

theorem marlButlastRaw_eq (buffer : List ℕ) (n cap : ℕ) :
    marlButlastRaw buffer n cap = marlButlastExecSpec buffer n cap := by
  simp [marlButlastRaw, marlButlastExecSpec, marlButlastCost, marlPred,
    mopBinop_def, Imp.Bop.apply_sub, binopCurrency_sub,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def, NRest.consume_consume,
    two_nsmul]

sepref_synth marlAppendSynth (A len cap value one : String)
    (buffer : List ℕ) (n c x : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn x value ∗ hnCtxt natAssn 1 one)
    _ _ (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (marlAppendRaw buffer n c x)

sepref_synth marlButlastSynth (A len cap one : String)
    (buffer : List ℕ) (n c : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn 1 one)
    _ _ (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (marlButlastRaw buffer n c)

def marlAppendCom (A len _cap value one : String) : Com :=
  (Com.aset A len value).seq
    ((Com.binop .add len len one).seq (Com.skip.seq Com.skip))

def marlButlastCom (_A len _cap one : String) : Com :=
  (Com.binop .sub len len one).seq (Com.skip.seq Com.skip)

abbrev marlLengthCom := arlLengthCom
abbrev marlIsEmptyCom := arlIsEmptyCom
abbrev marlLastCom := arlLastCom
abbrev marlGetCom := arlGetCom
abbrev marlSetCom := arlSetCom

@[sepref_fr_rules] theorem marlAppend_exec_hnr
    (A len cap value one : String) (buffer : List ℕ) (n c x : ℕ)
    (hi : n < buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn x value ∗ hnCtxt natAssn 1 one)
      (marlAppendCom A len cap value one)
      (hnCtxt natAssn 1 one ∗ hnCtxt natAssn x value)
      (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (marlAppendExecSpec buffer n c x) := by
  rw [← marlAppendRaw_eq buffer n c x hi]
  exact marlAppendSynth A len cap value one buffer n c x

@[sepref_fr_rules] theorem marlButlast_exec_hnr
    (A len cap one : String) (buffer : List ℕ) (n c : ℕ) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn 1 one)
      (marlButlastCom A len cap one)
      (hnCtxt natAssn 1 one)
      (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (marlButlastExecSpec buffer n c) := by
  rw [← marlButlastRaw_eq buffer n c]
  exact marlButlastSynth A len cap one buffer n c

abbrev marlLength_exec_hnr := arlLength_exec_hnr
abbrev marlIsEmpty_exec_hnr := arlIsEmpty_exec_hnr
abbrev marlLast_exec_hnr := arlLast_exec_hnr
abbrev marlGet_exec_hnr := arlGet_exec_hnr
abbrev marlSet_exec_hnr := arlSet_exec_hnr

attribute [sepref_fr_rules] marlLength_exec_hnr marlIsEmpty_exec_hnr
  marlLast_exec_hnr marlGet_exec_hnr marlSet_exec_hnr

/-! ## Executable/list bridges and gates -/

theorem marlLengthExecSpec_refines {N : ℕ} {s : MSArrayList}
    {xs : List ℕ} (h : (s, xs) ∈ isMSArrayList N) :
    marlLengthExecSpec s.length =
      NRest.consume (NRest.returnT xs.length) marlLengthCost := by
  change NRest.consume (NRest.returnT s.length) marlLengthCost = _
  rw [isMSArrayList_length h]

theorem marlIsEmptyExecSpec_refines {N : ℕ} {s : MSArrayList}
    {xs : List ℕ} (h : (s, xs) ∈ isMSArrayList N) :
    marlIsEmptyExecSpec s.length = NRest.consume
      (NRest.returnT (if decide (xs = []) then 1 else 0)) marlIsEmptyCost := by
  rw [isMSArrayList_length h]
  cases xs <;> simp [arlIsEmptyExecSpec]

private theorem isMSArrayList_wf_of_pos {N : ℕ} {s : MSArrayList}
    {xs : List ℕ} (h : (s, xs) ∈ isMSArrayList N) (hN : 0 < N) : s.Wf := by
  change s.buffer.length = N ∧ s.length ≤ N ∧
    s.capacity = N ∧ s.active = xs at h
  exact ⟨by simpa [h.2.2.1] using hN, by simpa [h.2.2.1] using h.2.1,
    by omega⟩

theorem marlLastExecSpec_refines {N : ℕ} {s : MSArrayList}
    {xs : List ℕ} (h : (s, xs) ∈ isMSArrayList N) (hne : xs ≠ []) :
    ∃ x, listAt? xs.reverse 0 = some x ∧
      marlLastExecSpec s.buffer s.length =
        NRest.consume (NRest.returnT x) marlLastCost := by
  have hlen : 0 < s.length := by
    rw [isMSArrayList_length h]
    cases xs <;> simp_all
  have hN : 0 < N := hlen.trans_le (by
    change s.buffer.length = N ∧ s.length ≤ N ∧
      s.capacity = N ∧ s.active = xs at h
    exact h.2.1)
  exact arlLastExecSpec_refines
    (show (s, xs) ∈ arrayListRel from ⟨isMSArrayList_wf_of_pos h hN, h.2.2.2⟩)
    hne

theorem marlGetExecSpec_refines {N : ℕ} {s : MSArrayList}
    {xs : List ℕ} {i : ℕ} (h : (s, xs) ∈ isMSArrayList N)
    (hi : i < xs.length) :
    marlGetExecSpec s.buffer i =
      NRest.consume (NRest.returnT xs[i]!) marlGetCost := by
  have hlen : 0 < s.length := by
    rw [isMSArrayList_length h]
    omega
  have hN : 0 < N := hlen.trans_le (by
    change s.buffer.length = N ∧ s.length ≤ N ∧
      s.capacity = N ∧ s.active = xs at h
    exact h.2.1)
  exact arlGetExecSpec_refines
    (show (s, xs) ∈ arrayListRel from ⟨isMSArrayList_wf_of_pos h hN, h.2.2.2⟩)
    hi

theorem marlSetExecSpec_refines {N : ℕ} {s : MSArrayList}
    {xs : List ℕ} {i x : ℕ} (h : (s, xs) ∈ isMSArrayList N)
    (hi : i < xs.length) :
    marlSetExecSpec s.buffer s.length s.capacity i x =
        NRest.consume (NRest.returnT
          (s.buffer.set i x, (s.length, s.capacity))) marlSetCost ∧
      (⟨s.buffer.set i x, s.length, s.capacity⟩, listSet xs i x) ∈
        isMSArrayList N := by
  refine ⟨rfl, marlSet_some_refines h ?_⟩
  have his : i < s.length := by simpa [isMSArrayList_length h] using hi
  simp [marlSet, his]

theorem marlAppendExecSpec_refines {N : ℕ} {s : MSArrayList}
    {xs : List ℕ} {x : ℕ} (h : (s, xs) ∈ isMSArrayList N)
    (hspace : xs.length < N) :
    marlAppendExecSpec s.buffer s.length s.capacity x =
        NRest.consume (NRest.returnT
          ((s.buffer.set s.length x), (s.length + 1, s.capacity)))
          marlAppendCost ∧
      (⟨s.buffer.set s.length x, s.length + 1, s.capacity⟩,
        xs ++ [x]) ∈ isMSArrayList N := by
  refine ⟨rfl, ?_⟩
  apply marlAppend_some_refines h
  change s.buffer.length = N ∧ s.length ≤ N ∧
    s.capacity = N ∧ s.active = xs at h
  rw [h.2.2.1]
  simp [marlAppend, isMSArrayList_length h, hspace]

theorem marlButlastExecSpec_refines {N : ℕ} {s : MSArrayList}
    {xs : List ℕ} (h : (s, xs) ∈ isMSArrayList N) (hne : xs ≠ []) :
    marlButlastExecSpec s.buffer s.length s.capacity =
        NRest.consume (NRest.returnT
          (s.buffer, (s.length - 1, s.capacity))) marlButlastCost ∧
      (⟨s.buffer, s.length - 1, s.capacity⟩, listButlast xs) ∈
        isMSArrayList N := by
  refine ⟨rfl, ?_⟩
  apply marlButlast_some_refines h
  have hsne : s.length ≠ 0 := by simpa [isMSArrayList_length h] using hne
  simp [marlButlast, hsne]

#guard marlEmptyIn 0 [] = some ⟨[], 0, 0⟩
#guard marlEmptyIn 4 [0, 0, 0, 0] = some ⟨[0, 0, 0, 0], 0, 4⟩
#guard marlEmptyIn 4 [0, 0, 0] = none
#guard marlAppend 4 ⟨[0, 0, 0, 0], 1, 4⟩ 7 =
  some ⟨[0, 7, 0, 0], 2, 4⟩
#guard marlAppend 4 ⟨[1, 2, 3, 4], 4, 4⟩ 9 = none
#guard marlButlast ⟨[1, 2, 3, 4], 3, 4⟩ = some ⟨[1, 2, 3, 4], 2, 4⟩

#guard marlAppendCom "A" "len" "cap" "value" "one" =
  (Com.aset "A" "len" "value").seq
    ((Com.binop .add "len" "len" "one").seq (Com.skip.seq Com.skip))
#guard marlLengthCom "len" "out" = .copy "out" "len"
#guard marlIsEmptyCom "len" "out" =
  .ite (.eq (.cell "len") (.lit 0)) (.const "out" 1) (.const "out" 0)
#guard marlLastCom "A" "len" "one" "idx" "out" =
  .seq (.binop .sub "idx" "len" "one") (.aget "out" "A" "idx")
#guard marlButlastCom "A" "len" "cap" "one" =
  (Com.binop .sub "len" "len" "one").seq (Com.skip.seq Com.skip)
#guard marlGetCom "A" "idx" "out" = .aget "out" "A" "idx"
#guard marlSetCom "A" "len" "cap" "idx" "value" =
  .seq (.aset "A" "idx" "value") (.seq .skip .skip)

theorem marlAppendCost_aset : marlAppendCost.toFun Currency.aset = 1 := by decide +kernel
theorem marlAppendCost_add : marlAppendCost.toFun Currency.add = 1 := by decide +kernel
theorem marlAppendCost_skip : marlAppendCost.toFun Currency.skip = 2 := by decide +kernel
theorem marlLengthCost_copy : marlLengthCost.toFun Currency.copy = 1 := by decide +kernel
theorem marlIsEmptyCost_ite : marlIsEmptyCost.toFun Currency.ite = 1 := by decide +kernel
theorem marlLastCost_aget : marlLastCost.toFun Currency.aget = 1 := by decide +kernel
theorem marlButlastCost_sub : marlButlastCost.toFun Currency.sub = 1 := by decide +kernel
theorem marlButlastCost_skip : marlButlastCost.toFun Currency.skip = 2 := by decide +kernel
theorem marlGetCost_aget : marlGetCost.toFun Currency.aget = 1 := by decide +kernel
theorem marlSetCost_aset : marlSetCost.toFun Currency.aset = 1 := by decide +kernel

/-! The source's two synthesis examples are represented at the honest
caller-owned boundary: both buffers are established first, then the same
fixed-capacity append command applies. -/
def marlSynthExampleLarge : MSArrayList := marlEmptyModel 11
def marlSynthExampleFolded : MSArrayList := marlEmptyModel 10

#guard marlAppend 11 marlSynthExampleLarge 1 =
  some ⟨(List.replicate 11 0).set 0 1, 1, 11⟩
#guard marlAppend 10 marlSynthExampleFolded 1 =
  some ⟨(List.replicate 10 0).set 0 1, 1, 10⟩

theorem marlSynthExampleLarge_hnr (A len cap value one : String) :
    hnRefine
      (hnCtxt arrayAssn (List.replicate 11 0) A ∗ hnCtxt natAssn 0 len ∗
        hnCtxt natAssn 11 cap ∗ hnCtxt natAssn 1 value ∗
        hnCtxt natAssn 1 one)
      (marlAppendCom A len cap value one)
      (hnCtxt natAssn 1 one ∗ hnCtxt natAssn 1 value)
      (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (marlAppendExecSpec (List.replicate 11 0) 0 11 1) := by
  exact marlAppend_exec_hnr A len cap value one (List.replicate 11 0) 0 11 1
    (by simp)

theorem marlSynthExampleFolded_hnr (A len cap value one : String) :
    hnRefine
      (hnCtxt arrayAssn (List.replicate 10 0) A ∗ hnCtxt natAssn 0 len ∗
        hnCtxt natAssn 10 cap ∗ hnCtxt natAssn 1 value ∗
        hnCtxt natAssn 1 one)
      (marlAppendCom A len cap value one)
      (hnCtxt natAssn 1 one ∗ hnCtxt natAssn 1 value)
      (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (marlAppendExecSpec (List.replicate 10 0) 0 10 1) := by
  exact marlAppend_exec_hnr A len cap value one (List.replicate 10 0) 0 10 1
    (by simp)

example : opMarlEmptySz ::ᵢ (ℕ → NRest (ListI ℕ) ECost) :=
  opMarlEmptySz_itype

run_cmd do
  let frefs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``marlAppendOp_refines, ``marlLengthOp_refines,
      ``marlIsEmptyOp_refines, ``marlLastOp_refines,
      ``marlButlastOp_refines, ``marlGetOp_refines, ``marlSetOp_refines] do
    unless frefs.contains n do
      throwError "ms-array-list source rule missing from DB: {n}"
  let frules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  for n in #[``marlAppend_exec_hnr, ``marlLength_exec_hnr,
      ``marlIsEmpty_exec_hnr, ``marlLast_exec_hnr,
      ``marlButlast_exec_hnr, ``marlGet_exec_hnr, ``marlSet_exec_hnr] do
    unless frules.contains n do
      throwError "ms-array-list executable rule missing from DB: {n}"

/-! No executable operation has a zero budget.  Empty-size is absent from the
executable DB because its source implementation allocates. -/

/-! ## Kernel-three gates -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.isMSArrayList_singleValued' does not depend on any axioms -/
#guard_msgs in
#print axioms isMSArrayList_singleValued

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.marlAppend_some_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms marlAppend_some_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.marlAppend_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms marlAppend_exec_hnr

end Lax13Proofs.Refine.Sepref.Iicf
