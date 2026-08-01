import Lax13Proofs.Refine.Iicf.Intf.Map
import Lax13Proofs.Refine.Iicf.IicfArray

/-!
# Fixed-capacity array map

Faithful adaptation of `IICF/Impl/IICF_Array_Map.thy` at
`isabelle_llvm_time` commit
`42dd7f59998d76047bb4b6bce76d8f67b53a08b6`.

The source owns one allocated array of `Option` values.  This IR has only
natural-number arrays, and no natural can soundly serve as an absent-value
sentinel.  We therefore use two caller-owned arrays of the same fixed length:
a canonical 0/1 presence array and an unrestricted value array.  Allocation
and `free` are not claimed.  The executable empty operation fills an already
owned presence array with zero and preserves the value array, whose contents
are semantically irrelevant while entries are absent.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

structure ArrayMap where
  present : List ℕ
  values : List ℕ
deriving DecidableEq, Repr

def ArrayMap.Wf (N : ℕ) (s : ArrayMap) : Prop :=
  s.present.length = N ∧ s.values.length = N ∧
    ∀ i < N, s.present[i]! = 0 ∨ s.present[i]! = 1

def amConcrete (s : ArrayMap) : ℕ → Option ℕ := fun k =>
  if k < s.present.length then
    if s.present[k]! = 0 then none else some s.values[k]!
  else none

def am1Rel (N : ℕ) : Set (ArrayMap × (ℕ → Option ℕ)) :=
  {p | p.1.Wf N ∧ p.2 = amConcrete p.1}

theorem am1Rel_singleValued (N : ℕ) : SingleValued (am1Rel N) := by
  intro s m n hm hn
  exact hm.2.trans hn.2.symm

private theorem getElem!_replicate {α : Type} [Inhabited α]
    (n i : ℕ) (x : α) (hi : i < n) : (List.replicate n x)[i]! = x := by
  rw [getElem!_def]
  simp [hi]

private theorem getElem!_set {α : Type} [Inhabited α]
    (xs : List α) (i j : ℕ) (x : α) (hj : j < xs.length) :
    (xs.set i x)[j]! = if j = i then x else xs[j]! := by
  induction xs generalizing i j with
  | nil => simp at hj
  | cons a xs ih =>
      cases i with
      | zero => cases j <;> simp
      | succ i =>
          cases j with
          | zero => simp
          | succ j =>
              simpa using ih i j (by simpa using hj)

def amRel {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    Set (ArrayMap × (ℕ → Option α)) :=
  relComp (am1Rel N) (mapRel (Set.diagonal ℕ) (thePure A))

def arrayMapRawAssn (s : ArrayMap) (c : String × String) : Assn :=
  arrayAssn s.present c.1 ∗ arrayAssn s.values c.2

def arrayMapAssn {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    (ℕ → Option α) → String × String → Assn :=
  hrComp arrayMapRawAssn (amRel N A)

@[intf_of_assn] theorem arrayMapAssn_intf {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) : intfOfAssn (arrayMapAssn N A) (MapI ℕ α) := trivial

theorem am1Rel_key_bound {N : ℕ} {s : ArrayMap} {m : ℕ → Option ℕ}
    (h : (s, m) ∈ am1Rel N) {k v : ℕ} (hm : m k = some v) : k < N := by
  change s.Wf N ∧ m = amConcrete s at h
  by_contra hk
  have hk' : ¬ k < s.present.length := by simpa [h.1.1] using hk
  rw [h.2] at hm
  simp [amConcrete, hk'] at hm

/-! ## Source-shaped semantic operations -/

def amEmptyModel (N : ℕ) : ArrayMap :=
  ⟨List.replicate N 0, List.replicate N 0⟩

def amEmptyIn (N : ℕ) (present values : List ℕ) : Option ArrayMap :=
  if present.length = N ∧ values.length = N then
    some ⟨List.replicate N 0, values⟩
  else none

def amUpdate (s : ArrayMap) (k v : ℕ) : Option ArrayMap :=
  if k < s.present.length ∧ k < s.values.length then
    some ⟨s.present.set k 1, s.values.set k v⟩
  else none

def amDelete (s : ArrayMap) (k : ℕ) : Option ArrayMap :=
  if k < s.present.length then some ⟨s.present.set k 0, s.values⟩ else none

def amLookup (s : ArrayMap) (k : ℕ) : Option ℕ := amConcrete s k

def amContains (s : ArrayMap) (k : ℕ) : Bool :=
  decide (amLookup s k ≠ none)

theorem amEmptyModel_refines (N : ℕ) :
    (amEmptyModel N, (mapEmpty : ℕ → Option ℕ)) ∈ am1Rel N := by
  refine ⟨?_, ?_⟩
  · refine ⟨by simp [amEmptyModel], by simp [amEmptyModel], ?_⟩
    intro i hi
    exact Or.inl (getElem!_replicate N i 0 hi)
  · funext k
    by_cases hk : k < N
    · simp [amEmptyModel, amConcrete, mapEmpty, hk]
    · simp [amEmptyModel, amConcrete, mapEmpty, hk]

theorem amEmptyIn_refines {N : ℕ} {present values : List ℕ} {s : ArrayMap}
    (h : amEmptyIn N present values = some s) :
    (s, (mapEmpty : ℕ → Option ℕ)) ∈ am1Rel N := by
  simp only [amEmptyIn] at h
  split at h
  · rename_i hw
    simp only [Option.some.injEq] at h
    subst s
    refine ⟨⟨by simp, hw.2, ?_⟩, ?_⟩
    · intro i hi
      exact Or.inl (getElem!_replicate N i 0 hi)
    funext k
    by_cases hk : k < N
    · simp [amConcrete, mapEmpty, hk]
    · simp [amConcrete, mapEmpty, hk]
  · contradiction

theorem amUpdate_refines {N : ℕ} {s : ArrayMap} {m : ℕ → Option ℕ}
    (h : (s, m) ∈ am1Rel N) {k v : ℕ} (hk : k < N) :
    ∃ t, amUpdate s k v = some t ∧
      (t, mapUpdate m k v) ∈ am1Rel N := by
  change s.Wf N ∧ m = amConcrete s at h
  have hkp : k < s.present.length := by simpa [h.1.1] using hk
  have hkv : k < s.values.length := by simpa [h.1.2.1] using hk
  let t : ArrayMap := ⟨s.present.set k 1, s.values.set k v⟩
  refine ⟨t, by simp [amUpdate, hkp, hkv, t], ?_, ?_⟩
  · refine ⟨by simpa [t] using h.1.1, by simpa [t] using h.1.2.1, ?_⟩
    intro i hi
    by_cases hik : i = k
    · subst i; simp [t, hkp]
    · rw [getElem!_set s.present k i 1 (by simpa [h.1.1] using hi), if_neg hik]
      exact h.1.2.2 i hi
  · change mapUpdate m k v = amConcrete t
    rw [h.2]
    funext i
    by_cases hik : i = k
    · subst i
      simp [amConcrete, mapUpdate, t, hkp, hkv]
    · by_cases hi : i < s.present.length
      · have hiv : i < s.values.length := by simpa [h.1.1, h.1.2.1] using hi
        simp [amConcrete, mapUpdate, t, hi, hiv, hik]
        rw [List.getElem_set_of_ne (Ne.symm hik)]
        rw [List.getElem_set_of_ne (Ne.symm hik)]
      · simp [amConcrete, mapUpdate, t, hi, hik]

theorem amDelete_refines {N : ℕ} {s : ArrayMap} {m : ℕ → Option ℕ}
    (h : (s, m) ∈ am1Rel N) {k : ℕ} (hk : k < N) :
    ∃ t, amDelete s k = some t ∧
      (t, mapDelete m k) ∈ am1Rel N := by
  change s.Wf N ∧ m = amConcrete s at h
  have hkp : k < s.present.length := by simpa [h.1.1] using hk
  let t : ArrayMap := ⟨s.present.set k 0, s.values⟩
  refine ⟨t, by simp [amDelete, hkp, t], ?_, ?_⟩
  · refine ⟨by simpa [t] using h.1.1, by simpa [t] using h.1.2.1, ?_⟩
    intro i hi
    by_cases hik : i = k
    · subst i; simp [t, hkp]
    · rw [getElem!_set s.present k i 0 (by simpa [h.1.1] using hi), if_neg hik]
      exact h.1.2.2 i hi
  · change mapDelete m k = amConcrete t
    rw [h.2]
    funext i
    by_cases hik : i = k
    · subst i; simp [amConcrete, mapDelete, t, hkp]
    · by_cases hi : i < s.present.length
      · simp [amConcrete, mapDelete, t, hi, hik]
        rw [List.getElem_set_of_ne (Ne.symm hik)]
      · simp [amConcrete, mapDelete, t, hi, hik]

theorem amLookup_refines {N : ℕ} {s : ArrayMap} {m : ℕ → Option ℕ}
    (h : (s, m) ∈ am1Rel N) (k : ℕ) : amLookup s k = m k := by
  change s.Wf N ∧ m = amConcrete s at h
  rw [h.2]
  rfl

theorem amContains_refines {N : ℕ} {s : ArrayMap} {m : ℕ → Option ℕ}
    (h : (s, m) ∈ am1Rel N) (k : ℕ) :
    amContains s k = propBool (k ∈ mapDom m) := by
  apply Bool.eq_iff_iff.mpr
  simp [amContains, propBool, mapDom, amLookup_refines h k]

/-! ## Custom empty and generic map refinements -/

noncomputable def opAmEmptySz (α : Type) (_N : ℕ) :
    NRest (ℕ → Option α) ECost := op_map_empty ℕ α

sepref_register opAmEmptySz : opAmEmptySz as
  (∀ α : Type, ℕ → NRest (MapI ℕ α) ECost)

theorem fold_am_custom_empty {α : Type} (N : ℕ) :
    op_map_empty ℕ α = opAmEmptySz α N := rfl

noncomputable def amEmptyOp (N : ℕ) : NRest ArrayMap ECost :=
  NRest.returnT (amEmptyModel N)

@[sepref_fref_thms] theorem amEmptyOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amEmptyOp N, opAmEmptySz α N) ∈ NRest.nrestRel (amRel N A) := by
  apply NRest.param_returnT
  exact ⟨mapEmpty, amEmptyModel_refines N,
    mapRel_empty (Set.diagonal ℕ) (thePure A)⟩

noncomputable def amUpdateOp (_N k v : ℕ) (s : ArrayMap) :
    NRest ArrayMap ECost :=
  match amUpdate s k v with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def amDeleteOp (_N k : ℕ) (s : ArrayMap) :
    NRest ArrayMap ECost :=
  match amDelete s k with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def amLookupOp (k : ℕ) (s : ArrayMap) :
    NRest (Option ℕ) ECost := NRest.returnT (amLookup s k)

noncomputable def amContainsOp (k : ℕ) (s : ArrayMap) : NRest Bool ECost :=
  NRest.returnT (amContains s k)

private theorem diagonal_converse_singleValued_am :
    SingleValued (relConverse (Set.diagonal ℕ)) := by
  rintro b a a' h h'
  change a = b at h
  change a' = b at h'
  exact h.trans h'.symm

@[sepref_fref_thms] theorem amUpdateOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amUpdateOp N, op_map_update ℕ α) ∈
      fref (fun k : ℕ => k < N) (Set.diagonal ℕ)
        (fun _ => thePure A →ᵣ amRel N A →ᵣ NRest.nrestRel (amRel N A)) := by
  intro k l hk hkl v a hva s m hsm
  change k = l at hkl
  subst l
  obtain ⟨cm, hscm, hcmm⟩ := hsm
  obtain ⟨t, ht, htm⟩ := amUpdate_refines hscm (v := v) hk
  simp [amUpdateOp, ht, op_map_update]
  exact NRest.param_returnT ⟨mapUpdate cm k v, htm,
    mapRel_update singleValued_diagonal diagonal_converse_singleValued_am
      rfl hva hcmm⟩

@[sepref_fref_thms] theorem amDeleteOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amDeleteOp N, op_map_delete ℕ α) ∈
      fref (fun k : ℕ => k < N) (Set.diagonal ℕ)
        (fun _ => amRel N A →ᵣ NRest.nrestRel (amRel N A)) := by
  intro k l hk hkl s m hsm
  change k = l at hkl
  subst l
  obtain ⟨cm, hscm, hcmm⟩ := hsm
  obtain ⟨t, ht, htm⟩ := amDelete_refines hscm hk
  simp [amDeleteOp, ht, op_map_delete]
  exact NRest.param_returnT ⟨mapDelete cm k, htm,
    mapRel_delete singleValued_diagonal diagonal_converse_singleValued_am
      rfl hcmm⟩

@[sepref_fref_thms] theorem amLookupOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amLookupOp, op_map_lookup ℕ α) ∈
      fref (fun k : ℕ => k < N) (Set.diagonal ℕ)
        (fun _ => amRel N A →ᵣ NRest.nrestRel (optionRel (thePure A))) := by
  intro k l _ hkl s m hsm
  change k = l at hkl
  subst l
  obtain ⟨cm, hscm, hcmm⟩ := hsm
  exact NRest.param_returnT (by
    simpa [amLookupOp, op_map_lookup, amLookup_refines hscm k] using
      mapRel_lookup (K := Set.diagonal ℕ) (V := thePure A) rfl hcmm)

@[sepref_fref_thms] theorem amContainsOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amContainsOp, op_map_contains_key ℕ α) ∈
      fref (fun k : ℕ => k < N) (Set.diagonal ℕ)
        (fun _ => amRel N A →ᵣ NRest.nrestRel (Set.diagonal Bool)) := by
  intro k l _ hkl s m hsm
  change k = l at hkl
  subst l
  obtain ⟨cm, hscm, hcmm⟩ := hsm
  apply NRest.param_returnT
  change amContains s k = propBool (k ∈ mapDom m)
  rw [amContains_refines hscm]
  exact propBool_congr (mapRel_contains (K := Set.diagonal ℕ)
    (V := thePure A) rfl hcmm)

/-! ## Exact executable two-array operations -/

noncomputable def amEmptyRaw (present values : List ℕ) :
    NRest (List ℕ × List ℕ) ECost :=
  NRest.bindT (mop_array_fill present 0) fun present' => mopPair present' values

noncomputable def amLookupRaw (present values : List ℕ) (k : ℕ) :
    NRest (ℕ × ℕ) ECost :=
  NRest.bindT (mopAget present k) fun tag =>
    NRest.bindT (mopAget values k) fun value => mopPair tag value

noncomputable def amContainsRaw (present : List ℕ) (k : ℕ) : NRest ℕ ECost :=
  mopAget present k

noncomputable def amUpdateRaw (present values : List ℕ) (k v : ℕ) :
    NRest (List ℕ × List ℕ) ECost :=
  NRest.bindT (mopAset present k 1) fun present' =>
    NRest.bindT (mopAset values k v) fun values' => mopPair present' values'

noncomputable def amDeleteRaw (present values : List ℕ) (k : ℕ) :
    NRest (List ℕ × List ℕ) ECost :=
  NRest.bindT (mopAset present k 0) fun present' => mopPair present' values

noncomputable def amEmptyCost (N : ℕ) : ECost :=
  fillCost N + irUnit Currency.skip
noncomputable def amLookupCost : ECost :=
  2 • irUnit Currency.aget + irUnit Currency.skip
noncomputable def amContainsCost : ECost := irUnit Currency.aget
noncomputable def amUpdateCost : ECost :=
  2 • irUnit Currency.aset + irUnit Currency.skip
noncomputable def amDeleteCost : ECost :=
  irUnit Currency.aset + irUnit Currency.skip

noncomputable def amEmptyExecSpec (present values : List ℕ) :
    NRest (List ℕ × List ℕ) ECost :=
  NRest.consume (NRest.returnT (List.replicate present.length 0, values))
    (amEmptyCost present.length)

noncomputable def amLookupExecSpec (present values : List ℕ) (k : ℕ) :
    NRest (ℕ × ℕ) ECost :=
  NRest.consume (NRest.returnT (present[k]!, values[k]!)) amLookupCost

noncomputable def amContainsExecSpec (present : List ℕ) (k : ℕ) :
    NRest ℕ ECost :=
  NRest.consume (NRest.returnT present[k]!) amContainsCost

noncomputable def amUpdateExecSpec (present values : List ℕ) (k v : ℕ) :
    NRest (List ℕ × List ℕ) ECost :=
  NRest.consume (NRest.returnT (present.set k 1, values.set k v)) amUpdateCost

noncomputable def amDeleteExecSpec (present values : List ℕ) (k : ℕ) :
    NRest (List ℕ × List ℕ) ECost :=
  NRest.consume (NRest.returnT (present.set k 0, values)) amDeleteCost

theorem amEmptyRaw_eq (present values : List ℕ) :
    amEmptyRaw present values = amEmptyExecSpec present values := by
  rw [amEmptyRaw, mop_array_fill_def, bindT_unit, mopPair_def,
    NRest.consume_consume]
  rfl

theorem amLookupRaw_eq (present values : List ℕ) (k : ℕ)
    (hp : k < present.length) (hv : k < values.length) :
    amLookupRaw present values k = amLookupExecSpec present values k := by
  simp [amLookupRaw, amLookupExecSpec, amLookupCost, mopAget_def,
    NRest.assert_pos hp, NRest.assert_pos hv, bindT_unit, mopPair_def,
    NRest.consume_consume, two_nsmul]
  ac_rfl

theorem amContainsRaw_eq (present : List ℕ) (k : ℕ)
    (hk : k < present.length) :
    amContainsRaw present k = amContainsExecSpec present k := by
  simp [amContainsRaw, amContainsExecSpec, amContainsCost, mopAget_def,
    NRest.assert_pos hk]

theorem amUpdateRaw_eq (present values : List ℕ) (k v : ℕ)
    (hp : k < present.length) (hv : k < values.length) :
    amUpdateRaw present values k v = amUpdateExecSpec present values k v := by
  simp [amUpdateRaw, amUpdateExecSpec, amUpdateCost, mopAset_def,
    NRest.assert_pos hp, NRest.assert_pos hv, bindT_unit, mopPair_def,
    NRest.consume_consume, two_nsmul]
  ac_rfl

theorem amDeleteRaw_eq (present values : List ℕ) (k : ℕ)
    (hk : k < present.length) :
    amDeleteRaw present values k = amDeleteExecSpec present values k := by
  simp [amDeleteRaw, amDeleteExecSpec, amDeleteCost, mopAset_def,
    NRest.assert_pos hk, bindT_unit, mopPair_def, NRest.consume_consume]

sepref_synth amEmptySynth (i P V zero n one : String)
    (present values : List ℕ) :
  hnRefine (junkCell i ∗ hnCtxt arrayAssn present P ∗
      hnCtxt arrayAssn values V ∗ hnCtxt natAssn 0 zero ∗
      hnCtxt natAssn present.length n ∗ hnCtxt natAssn 1 one)
    _ _ (P, V) (arrayAssn ×ₐ arrayAssn) (amEmptyRaw present values)

sepref_synth amLookupSynth (P V key tag out : String)
    (present values : List ℕ) (k : ℕ) :
  hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
      hnCtxt natAssn k key ∗ junkCell tag ∗ junkCell out)
    _ _ (tag, out) (natAssn ×ₐ natAssn) (amLookupRaw present values k)

sepref_synth amContainsSynth (P key out : String) (present : List ℕ) (k : ℕ) :
  hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt natAssn k key ∗ junkCell out)
    _ _ out natAssn (amContainsRaw present k)

sepref_synth amUpdateSynth (P V key value one : String)
    (present values : List ℕ) (k v : ℕ) :
  hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
      hnCtxt natAssn k key ∗ hnCtxt natAssn v value ∗ hnCtxt natAssn 1 one)
    _ _ (P, V) (arrayAssn ×ₐ arrayAssn) (amUpdateRaw present values k v)

sepref_synth amDeleteSynth (P V key zero : String)
    (present values : List ℕ) (k : ℕ) :
  hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
      hnCtxt natAssn k key ∗ hnCtxt natAssn 0 zero)
    _ _ (P, V) (arrayAssn ×ₐ arrayAssn) (amDeleteRaw present values k)

def amEmptyCom (i P _V zero n one : String) : Com :=
  (fillCom i P zero one n).seq Com.skip
def amLookupCom (P V key tag out : String) : Com :=
  (Com.aget tag P key).seq ((Com.aget out V key).seq Com.skip)
def amContainsCom (P key out : String) : Com := Com.aget out P key
def amUpdateCom (P V key value one : String) : Com :=
  (Com.aset P key one).seq ((Com.aset V key value).seq Com.skip)
def amDeleteCom (P _V key zero : String) : Com :=
  (Com.aset P key zero).seq Com.skip

@[sepref_fr_rules] theorem amEmpty_exec_hnr
    (i P V zero n one : String) (present values : List ℕ) :
    hnRefine (junkCell i ∗ hnCtxt arrayAssn present P ∗
        hnCtxt arrayAssn values V ∗ hnCtxt natAssn 0 zero ∗
        hnCtxt natAssn present.length n ∗ hnCtxt natAssn 1 one)
      (amEmptyCom i P V zero n one)
      (junkCell i ∗ hnCtxt natAssn 0 zero ∗
        hnCtxt natAssn present.length n ∗ hnCtxt natAssn 1 one)
      (P, V) (arrayAssn ×ₐ arrayAssn) (amEmptyExecSpec present values) := by
  rw [← amEmptyRaw_eq present values]
  exact amEmptySynth i P V zero n one present values

@[sepref_fr_rules] theorem amLookup_exec_hnr
    (P V key tag out : String) (present values : List ℕ) (k : ℕ)
    (hp : k < present.length) (hv : k < values.length) :
    hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
        hnCtxt natAssn k key ∗ junkCell tag ∗ junkCell out)
      (amLookupCom P V key tag out)
      (hnCtxt arrayAssn values V ∗ hnCtxt natAssn k key ∗
        hnCtxt arrayAssn present P)
      (tag, out) (natAssn ×ₐ natAssn) (amLookupExecSpec present values k) := by
  rw [← amLookupRaw_eq present values k hp hv]
  simpa only [amLookupCom] using
    (amLookupSynth P V key tag out present values k)

@[sepref_fr_rules] theorem amContains_exec_hnr
    (P key out : String) (present : List ℕ) (k : ℕ)
    (hk : k < present.length) :
    hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt natAssn k key ∗ junkCell out)
      (amContainsCom P key out)
      (hnCtxt arrayAssn present P ∗ hnCtxt natAssn k key)
      out natAssn (amContainsExecSpec present k) := by
  rw [← amContainsRaw_eq present k hk]
  exact amContainsSynth P key out present k

@[sepref_fr_rules] theorem amUpdate_exec_hnr
    (P V key value one : String) (present values : List ℕ) (k v : ℕ)
    (hp : k < present.length) (hv : k < values.length) :
    hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
        hnCtxt natAssn k key ∗ hnCtxt natAssn v value ∗ hnCtxt natAssn 1 one)
      (amUpdateCom P V key value one)
      (hnCtxt natAssn k key ∗ hnCtxt natAssn v value ∗ hnCtxt natAssn 1 one)
      (P, V) (arrayAssn ×ₐ arrayAssn) (amUpdateExecSpec present values k v) := by
  rw [← amUpdateRaw_eq present values k v hp hv]
  exact amUpdateSynth P V key value one present values k v

@[sepref_fr_rules] theorem amDelete_exec_hnr
    (P V key zero : String) (present values : List ℕ) (k : ℕ)
    (hk : k < present.length) :
    hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
        hnCtxt natAssn k key ∗ hnCtxt natAssn 0 zero)
      (amDeleteCom P V key zero)
      (hnCtxt natAssn k key ∗ hnCtxt natAssn 0 zero)
      (P, V) (arrayAssn ×ₐ arrayAssn) (amDeleteExecSpec present values k) := by
  rw [← amDeleteRaw_eq present values k hk]
  exact amDeleteSynth P V key zero present values k

/-! ## Executable semantic bridges -/

theorem amEmptyExecSpec_refines {N : ℕ} {present values : List ℕ}
    (hp : present.length = N) (hv : values.length = N) :
    amEmptyExecSpec present values = NRest.consume
        (NRest.returnT (List.replicate N 0, values)) (amEmptyCost N) ∧
      (⟨List.replicate N 0, values⟩, (mapEmpty : ℕ → Option ℕ)) ∈
        am1Rel N := by
  refine ⟨by simp [amEmptyExecSpec, hp], ?_⟩
  apply amEmptyIn_refines (present := present) (values := values)
  simp [amEmptyIn, hp, hv]

theorem amLookupExecSpec_refines {N : ℕ} {s : ArrayMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ am1Rel N) {k : ℕ} (hk : k < N) :
    amLookupExecSpec s.present s.values k =
        NRest.consume (NRest.returnT (s.present[k]!, s.values[k]!)) amLookupCost ∧
      (if s.present[k]! = 0 then none else some s.values[k]!) = m k := by
  refine ⟨rfl, ?_⟩
  have hp : k < s.present.length := by simpa [h.1.1] using hk
  simpa [amLookup, amConcrete, hp] using amLookup_refines h k

theorem amContainsExecSpec_refines {N : ℕ} {s : ArrayMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ am1Rel N) {k : ℕ} (hk : k < N) :
    amContainsExecSpec s.present k = NRest.consume
      (NRest.returnT (if decide (m k ≠ none) then 1 else 0)) amContainsCost := by
  have hp : k < s.present.length := by simpa [h.1.1] using hk
  have htag := h.1.2.2 k hk
  have hm := amLookup_refines h k
  simp only [amContainsExecSpec]
  by_cases hz : s.present[k]! = 0
  · have hmnone : m k = none := by
      rw [← hm]
      have hz' : s.present[k] = 0 := by simpa [getElem!_def, hp] using hz
      simp [amLookup, amConcrete, hp, hz']
    simp [hz, hmnone]
  · have hone : s.present[k]! = 1 := htag.resolve_left hz
    have hmne : m k ≠ none := by
      rw [← hm]
      have hz' : s.present[k] ≠ 0 := by
        intro hzero
        apply hz
        simpa [getElem!_def, hp] using hzero
      simp [amLookup, amConcrete, hp, hz']
    simp [hone, hmne]

theorem amUpdateExecSpec_refines {N : ℕ} {s : ArrayMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ am1Rel N) {k v : ℕ} (hk : k < N) :
    amUpdateExecSpec s.present s.values k v = NRest.consume
        (NRest.returnT (s.present.set k 1, s.values.set k v)) amUpdateCost ∧
      (⟨s.present.set k 1, s.values.set k v⟩, mapUpdate m k v) ∈ am1Rel N := by
  refine ⟨rfl, ?_⟩
  obtain ⟨t, ht, hrel⟩ := amUpdate_refines h (v := v) hk
  have hp : k < s.present.length := by simpa [h.1.1] using hk
  have hv : k < s.values.length := by simpa [h.1.2.1] using hk
  have ht' : t = ⟨s.present.set k 1, s.values.set k v⟩ := by
    symm
    simpa [amUpdate, hp, hv] using ht
  subst t
  exact hrel

theorem amDeleteExecSpec_refines {N : ℕ} {s : ArrayMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ am1Rel N) {k : ℕ} (hk : k < N) :
    amDeleteExecSpec s.present s.values k = NRest.consume
        (NRest.returnT (s.present.set k 0, s.values)) amDeleteCost ∧
      (⟨s.present.set k 0, s.values⟩, mapDelete m k) ∈ am1Rel N := by
  refine ⟨rfl, ?_⟩
  obtain ⟨t, ht, hrel⟩ := amDelete_refines h hk
  have hp : k < s.present.length := by simpa [h.1.1] using hk
  have ht' : t = ⟨s.present.set k 0, s.values⟩ := by
    symm
    simpa [amDelete, hp] using ht
  subst t
  exact hrel

/-! Source `am_assn_free`, allocation-backed `am2_empty`, LLVM code export,
and pointer regression are accounted for but unsupported in P0.  The
caller-owned `amEmpty_exec_hnr` is the executable replacement; it does not
claim to implement allocation or deallocation. -/

/-! ## Regression, command, currency, and database gates -/

def amRegression : Option ArrayMap := do
  let s0 := amEmptyModel 12
  let s1 ← amUpdate s0 4 2
  if amContains s1 4 then
    let s2 ← amUpdate s1 5 2
    let s3 ← amUpdate s2 6 2
    amDelete s3 5
  else none

#guard (amRegression.bind (fun s => amLookup s 4)) = some 2
#guard (amRegression.map (fun s => amLookup s 5)) = some none
#guard (amRegression.map (fun s => amContains s 6)) = some true

#guard amEmptyCom "i" "P" "V" "zero" "n" "one" =
  (fillCom "i" "P" "zero" "one" "n").seq Com.skip
#guard amLookupCom "P" "V" "key" "tag" "out" =
  (Com.aget "tag" "P" "key").seq
    ((Com.aget "out" "V" "key").seq Com.skip)
#guard amContainsCom "P" "key" "out" = Com.aget "out" "P" "key"
#guard amUpdateCom "P" "V" "key" "value" "one" =
  (Com.aset "P" "key" "one").seq
    ((Com.aset "V" "key" "value").seq Com.skip)
#guard amDeleteCom "P" "V" "key" "zero" =
  (Com.aset "P" "key" "zero").seq Com.skip

theorem amEmptyCost_aset : (amEmptyCost 3).toFun Currency.aset = 3 := by decide +kernel
theorem amEmptyCost_add : (amEmptyCost 3).toFun Currency.add = 3 := by decide +kernel
theorem amEmptyCost_while : (amEmptyCost 3).toFun Currency.«while» = 4 := by decide +kernel
theorem amEmptyCost_const : (amEmptyCost 3).toFun Currency.const = 1 := by decide +kernel
theorem amEmptyCost_skip : (amEmptyCost 3).toFun Currency.skip = 5 := by decide +kernel
theorem amLookupCost_aget : amLookupCost.toFun Currency.aget = 2 := by decide +kernel
theorem amLookupCost_skip : amLookupCost.toFun Currency.skip = 1 := by decide +kernel
theorem amContainsCost_aget : amContainsCost.toFun Currency.aget = 1 := by decide +kernel
theorem amUpdateCost_aset : amUpdateCost.toFun Currency.aset = 2 := by decide +kernel
theorem amUpdateCost_skip : amUpdateCost.toFun Currency.skip = 1 := by decide +kernel
theorem amDeleteCost_aset : amDeleteCost.toFun Currency.aset = 1 := by decide +kernel
theorem amDeleteCost_skip : amDeleteCost.toFun Currency.skip = 1 := by decide +kernel

private theorem ecost_ne_zero_of_pos_am (C : ECost) (c : String)
    (h : 0 < C.toFun c) : C ≠ 0 := by
  intro hz
  rw [hz] at h
  simp at h

theorem amEmptyCost_ne_zero : amEmptyCost 3 ≠ 0 :=
  ecost_ne_zero_of_pos_am _ Currency.aset (by simp [amEmptyCost_aset])
theorem amLookupCost_ne_zero : amLookupCost ≠ 0 :=
  ecost_ne_zero_of_pos_am _ Currency.aget (by simp [amLookupCost_aget])
theorem amContainsCost_ne_zero : amContainsCost ≠ 0 :=
  ecost_ne_zero_of_pos_am _ Currency.aget (by simp [amContainsCost_aget])
theorem amUpdateCost_ne_zero : amUpdateCost ≠ 0 :=
  ecost_ne_zero_of_pos_am _ Currency.aset (by simp [amUpdateCost_aset])
theorem amDeleteCost_ne_zero : amDeleteCost ≠ 0 :=
  ecost_ne_zero_of_pos_am _ Currency.aset (by simp [amDeleteCost_aset])

example : opAmEmptySz ::ᵢ
    (∀ α : Type, ℕ → NRest (MapI ℕ α) ECost) := opAmEmptySz_itype

run_cmd do
  let frefs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``amEmptyOp_refines, ``amUpdateOp_refines,
      ``amDeleteOp_refines, ``amLookupOp_refines, ``amContainsOp_refines] do
    unless frefs.contains n do
      throwError "array-map source rule missing from DB: {n}"
  let frules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  for n in #[``amEmpty_exec_hnr, ``amLookup_exec_hnr,
      ``amContains_exec_hnr, ``amUpdate_exec_hnr, ``amDelete_exec_hnr] do
    unless frules.contains n do
      throwError "array-map executable rule missing from DB: {n}"

/-! Allocation/free have no executable rules and hence no zero-cost
placeholders.  Every registered caller-owned operation has a positive budget
above. -/

/-! ## Kernel-three gates -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.am1Rel_singleValued' depends on axioms: [propext] -/
#guard_msgs in
#print axioms am1Rel_singleValued

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amUpdateOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amUpdateOp_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amEmpty_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amEmpty_exec_hnr

end Lax13Proofs.Refine.Sepref.Iicf
