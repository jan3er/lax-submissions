import Lax13Proofs.Refine.Iicf.Impl.ArrayMap

/-!
# Cardinality-carrying array map

Faithful adaptation of `Refine_Imperative_HOL/IICF/Impl/IICF_ArrayMap_Map.thy`
from `maxhaslbeck/Sepreftime` commit
`c1c987b45ec886d289ba215768182ac87b82f20d`.

The source's `is_liam n M` owns an array of optional values and a scalar
reference equal to `card (dom M)`.  This IR has only natural-number arrays,
so we reuse `ArrayMap`'s honest two-array encoding: canonical 0/1 presence
tags plus unrestricted values.  A third, owned natural-number cell stores
the exact cardinality of the finite abstract domain.  No natural is used as
an absence sentinel.

The source allocates in `new_liam`; P0 cannot allocate or free.  Empty below
therefore initializes caller-owned arrays and a caller-owned scalar cell.
Source SepLogicTime/enat scalar bounds (`n+3` for empty, `6` for update,
and `2` for membership and present-key lookup) are provenance only: they are
not equated with this IR's vector-valued `ECost`.  The executable costs below
are instead derived exactly from the synthesized IR commands.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

structure ArrayMapMap where
  present : List ℕ
  values : List ℕ
  count : ℕ
deriving DecidableEq, Repr

def ArrayMapMap.base (s : ArrayMapMap) : ArrayMap :=
  ⟨s.present, s.values⟩

/-- The finite domain whose cardinality the source scalar owns.  Under
`am1Rel N`, every key outside `range N` is absent, so this is the entire map
domain rather than merely a bounded approximation. -/
def ammDomain (N : ℕ) (m : ℕ → Option ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k => (m k).isSome

def amm1Rel (N : ℕ) : Set (ArrayMapMap × (ℕ → Option ℕ)) :=
  {p | (p.1.base, p.2) ∈ am1Rel N ∧ p.1.count = (ammDomain N p.2).card}

theorem amm1Rel_singleValued (N : ℕ) : SingleValued (amm1Rel N) := by
  intro s m m' hm hm'
  exact hm.1.2.trans hm'.1.2.symm

theorem amm1Rel_key_bound {N : ℕ} {s : ArrayMapMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ amm1Rel N) {k v : ℕ}
    (hm : m k = some v) : k < N :=
  am1Rel_key_bound h.1 hm

theorem ammDomain_exact {N : ℕ} {s : ArrayMapMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ amm1Rel N) (k : ℕ) :
    k ∈ ammDomain N m ↔ m k ≠ none := by
  constructor
  · intro hk
    have hk' : k < N ∧ (m k).isSome = true := by
      simpa [ammDomain] using hk
    have hs : (m k).isSome = true := hk'.2
    intro hnone
    simp [hnone] at hs
  · intro hne
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hne
    have hk : k < N := amm1Rel_key_bound h hv
    simp [ammDomain, hk, hv]

def ammRel {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    Set (ArrayMapMap × (ℕ → Option α)) :=
  relComp (amm1Rel N) (mapRel (Set.diagonal ℕ) (thePure A))

def arrayMapMapRawAssn (s : ArrayMapMap) (c : String × String × String) : Assn :=
  arrayAssn s.present c.1 ∗ arrayAssn s.values c.2.1 ∗ natAssn s.count c.2.2

def arrayMapMapAssn {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    (ℕ → Option α) → String × String × String → Assn :=
  hrComp arrayMapMapRawAssn (ammRel N A)

@[intf_of_assn] theorem arrayMapMapAssn_intf {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) : intfOfAssn (arrayMapMapAssn N A) (MapI ℕ α) := trivial

/-! ## Domain-cardinality lemmas -/

theorem ammDomain_empty (N : ℕ) :
    (ammDomain N (mapEmpty : ℕ → Option ℕ)).card = 0 := by
  simp [ammDomain, mapEmpty]

theorem ammDomain_update {N k v : ℕ} {m : ℕ → Option ℕ} (hk : k < N) :
    (ammDomain N (mapUpdate m k v)).card =
      if m k = none then (ammDomain N m).card + 1 else (ammDomain N m).card := by
  by_cases hm : m k = none
  · have hnot : k ∉ ammDomain N m := by simp [ammDomain, hm]
    have heq : ammDomain N (mapUpdate m k v) = insert k (ammDomain N m) := by
      ext i
      by_cases hik : i = k
      · subst i
        simp [ammDomain, mapUpdate, hk]
      · simp [ammDomain, mapUpdate, hik]
    rw [heq, Finset.card_insert_of_notMem hnot]
    simp [hm]
  · have heq : ammDomain N (mapUpdate m k v) = ammDomain N m := by
      ext i
      by_cases hik : i = k
      · subst i
        obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hm
        simp [ammDomain, mapUpdate, hk, hw]
      · simp [ammDomain, mapUpdate, hik]
    rw [heq]
    simp [hm]

/-! ## Source-shaped semantic operations -/

def ammEmptyModel (N : ℕ) : ArrayMapMap :=
  ⟨List.replicate N 0, List.replicate N 0, 0⟩

def ammEmptyIn (N : ℕ) (present values : List ℕ) : Option ArrayMapMap :=
  if present.length = N ∧ values.length = N then
    some ⟨List.replicate N 0, values, 0⟩
  else none

def ammUpdate (s : ArrayMapMap) (k v : ℕ) : Option ArrayMapMap :=
  if k < s.present.length ∧ k < s.values.length then
    some ⟨s.present.set k 1, s.values.set k v,
      if amLookup s.base k = none then s.count + 1 else s.count⟩
  else none

def ammContains (s : ArrayMapMap) (k : ℕ) : Bool :=
  amContains s.base k

def ammLookup (s : ArrayMapMap) (k : ℕ) : Option ℕ :=
  amLookup s.base k

theorem ammEmptyModel_refines (N : ℕ) :
    (ammEmptyModel N, (mapEmpty : ℕ → Option ℕ)) ∈ amm1Rel N := by
  exact ⟨amEmptyModel_refines N, by simp [ammEmptyModel, ammDomain_empty]⟩

theorem ammEmptyIn_refines {N : ℕ} {present values : List ℕ} {s : ArrayMapMap}
    (h : ammEmptyIn N present values = some s) :
    (s, (mapEmpty : ℕ → Option ℕ)) ∈ amm1Rel N := by
  simp only [ammEmptyIn] at h
  split at h
  · rename_i hw
    simp only [Option.some.injEq] at h
    subst s
    refine ⟨?_, by simp [ammDomain_empty]⟩
    change (⟨List.replicate N 0, values⟩,
      (mapEmpty : ℕ → Option ℕ)) ∈ am1Rel N
    exact amEmptyIn_refines (present := present) (values := values)
      (by simp [amEmptyIn, hw])
  · contradiction

theorem ammUpdate_refines {N : ℕ} {s : ArrayMapMap} {m : ℕ → Option ℕ}
    (h : (s, m) ∈ amm1Rel N) {k v : ℕ} (hk : k < N) :
    ∃ t, ammUpdate s k v = some t ∧
      (t, mapUpdate m k v) ∈ amm1Rel N := by
  have hp : k < s.present.length := by
    have hp' : k < s.base.present.length := by
      rw [h.1.1.1]
      exact hk
    simpa [ArrayMapMap.base] using hp'
  have hv : k < s.values.length := by
    have hv' : k < s.base.values.length := by
      rw [h.1.1.2.1]
      exact hk
    simpa [ArrayMapMap.base] using hv'
  let t : ArrayMapMap :=
    ⟨s.present.set k 1, s.values.set k v,
      if amLookup s.base k = none then s.count + 1 else s.count⟩
  refine ⟨t, by simp [ammUpdate, hp, hv, t], ?_, ?_⟩
  · obtain ⟨b, hb, hbrel⟩ := amUpdate_refines h.1 (v := v) hk
    have hbeq : b = ⟨s.present.set k 1, s.values.set k v⟩ := by
      symm
      simpa [amUpdate, ArrayMapMap.base, hp, hv] using hb
    subst b
    simpa [ArrayMapMap.base, t] using hbrel
  · simp only [t]
    rw [ammDomain_update hk, ← h.2]
    rw [amLookup_refines h.1 k]

theorem ammContains_refines {N : ℕ} {s : ArrayMapMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ amm1Rel N) (k : ℕ) :
    ammContains s k = propBool (k ∈ mapDom m) :=
  amContains_refines h.1 k

theorem ammLookup_refines {N : ℕ} {s : ArrayMapMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ amm1Rel N) (k : ℕ) :
    ammLookup s k = m k :=
  amLookup_refines h.1 k

/-! ## Generic map refinements -/

noncomputable def opAmmEmptySz (α : Type) (_N : ℕ) :
    NRest (ℕ → Option α) ECost := op_map_empty ℕ α

sepref_register opAmmEmptySz : opAmmEmptySz as
  (∀ α : Type, ℕ → NRest (MapI ℕ α) ECost)

theorem amm_fold_custom_empty {α : Type} (N : ℕ) :
    op_map_empty ℕ α = opAmmEmptySz α N := rfl

noncomputable def ammEmptyOp (N : ℕ) : NRest ArrayMapMap ECost :=
  NRest.returnT (ammEmptyModel N)

noncomputable def ammUpdateOp (_N k v : ℕ) (s : ArrayMapMap) :
    NRest ArrayMapMap ECost :=
  match ammUpdate s k v with
  | some t => NRest.returnT t
  | none => NRest.fail

noncomputable def ammContainsOp (k : ℕ) (s : ArrayMapMap) : NRest Bool ECost :=
  NRest.returnT (ammContains s k)

noncomputable def ammLookupOp (k : ℕ) (s : ArrayMapMap) : NRest ℕ ECost :=
  match ammLookup s k with
  | some v => NRest.returnT v
  | none => NRest.fail

private theorem diagonal_converse_singleValued_amm :
    SingleValued (relConverse (Set.diagonal ℕ)) := by
  rintro b a a' h h'
  change a = b at h
  change a' = b at h'
  exact h.trans h'.symm

@[sepref_fref_thms] theorem ammEmptyOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (ammEmptyOp N, opAmmEmptySz α N) ∈ NRest.nrestRel (ammRel N A) := by
  apply NRest.param_returnT
  exact ⟨mapEmpty, ammEmptyModel_refines N,
    mapRel_empty (Set.diagonal ℕ) (thePure A)⟩

@[sepref_fref_thms] theorem ammUpdateOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (ammUpdateOp N, op_map_update ℕ α) ∈
      fref (fun k : ℕ => k < N) (Set.diagonal ℕ)
        (fun _ => thePure A →ᵣ ammRel N A →ᵣ NRest.nrestRel (ammRel N A)) := by
  intro k l hk hkl v a hva s m hsm
  change k = l at hkl
  subst l
  obtain ⟨cm, hscm, hcmm⟩ := hsm
  obtain ⟨t, ht, htm⟩ := ammUpdate_refines hscm (v := v) hk
  simp [ammUpdateOp, ht, op_map_update]
  exact NRest.param_returnT ⟨mapUpdate cm k v, htm,
    mapRel_update singleValued_diagonal diagonal_converse_singleValued_amm
      rfl hva hcmm⟩

@[sepref_fref_thms] theorem ammContainsOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (ammContainsOp, op_map_contains_key ℕ α) ∈
      fref (fun k : ℕ => k < N) (Set.diagonal ℕ)
        (fun _ => ammRel N A →ᵣ NRest.nrestRel (Set.diagonal Bool)) := by
  intro k l _ hkl s m hsm
  change k = l at hkl
  subst l
  obtain ⟨cm, hscm, hcmm⟩ := hsm
  apply NRest.param_returnT
  change ammContains s k = propBool (k ∈ mapDom m)
  rw [ammContains_refines hscm]
  exact propBool_congr (mapRel_contains (K := Set.diagonal ℕ)
    (V := thePure A) rfl hcmm)

@[sepref_fref_thms] theorem ammLookupOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (ammLookupOp, fun k m => op_map_the_lookup ℕ α (k, m)) ∈
      fref (fun k : ℕ => k < N) (Set.diagonal ℕ)
        (fun k => fref (fun m : ℕ → Option α => m k ≠ none)
          (ammRel N A) (fun _ => NRest.nrestRel (thePure A))) := by
  intro k l _ hkl s m hm hrel
  change k = l at hkl
  subst l
  obtain ⟨cm, hscm, hcmm⟩ := hrel
  have hcm : cm k ≠ none := by
    intro hnone
    exact hm ((optionRel_none_iff
      (mapRel_lookup (K := Set.diagonal ℕ) (V := thePure A) rfl hcmm)).mp hnone)
  obtain ⟨v, hcv⟩ := Option.ne_none_iff_exists'.mp hcm
  have hcv' : cm k = some v := hcv
  obtain ⟨a, hma, hva⟩ := optionRel_obtain_left (by
    simpa [hcv'] using mapRel_lookup (K := Set.diagonal ℕ)
      (V := thePure A) (k := k) (l := k) rfl hcmm)
  simp only [op_map_the_lookup, NRest.assert_pos hm, NRest.returnT_bindT]
  rw [optionSpec_eq_returnT hma]
  simp [ammLookupOp, ammLookup_refines hscm k, hcv']
  exact NRest.param_returnT hva

/-! ## Exact executable operations -/

/-- Overwrite the already-owned scalar cell with the caller's zero cell.
This is the no-allocation counterpart of the source's fresh `ref 0`. -/
noncomputable def ammZeroCount (_old : ℕ) : NRest ℕ ECost :=
  mopCopy 0

@[sepref_fr_rules] private theorem hnr_ammZeroCount
    (count zero : String) (old : ℕ) :
    hnRefine (hnCtxt natAssn old count ∗ hnCtxt natAssn 0 zero)
      (.copy count zero) (hnCtxt natAssn 0 zero)
      count natAssn (ammZeroCount old) := by
  unfold ammZeroCount
  exact hnRefine_cons_pre (hnr_mop_copy count zero 0)
    (conj_entails_mono (natAssn_entails_junkCell old count) (entails_refl _))

attribute [irreducible] ammZeroCount

noncomputable def ammPack (present values : List ℕ) (count : ℕ) :
    NRest (List ℕ × List ℕ × ℕ) ECost :=
  NRest.bindT (mopPair values count) fun vc => mopPair present vc

noncomputable def ammEmptyRaw (present values : List ℕ) (oldCount : ℕ) :
    NRest (List ℕ × List ℕ × ℕ) ECost :=
  NRest.bindT (mop_array_fill present 0) fun present' =>
    NRest.bindT (ammZeroCount oldCount) fun count' =>
      ammPack present' values count'

noncomputable def ammContainsRaw (present : List ℕ) (k : ℕ) :
    NRest ℕ ECost :=
  mopAget present k

noncomputable def ammLookupRaw (present values : List ℕ) (k : ℕ) :
    NRest (ℕ × ℕ) ECost :=
  NRest.bindT (mopAget present k) fun tag =>
    NRest.bindT (mopAget values k) fun value => mopPair tag value

/-- Read the old presence tag before either write.  Both branches form the
same triple; only the absent-key branch increments the owned count cell, so
the generated command and exact cost retain the source's branch distinction. -/
noncomputable def ammUpdateRaw (present values : List ℕ) (count k v : ℕ) :
    NRest (List ℕ × List ℕ × ℕ) ECost :=
  NRest.bindT (mopAget present k) fun oldTag =>
    NRest.bindT (mopAset present k 1) fun present' =>
      NRest.bindT (mopAset values k v) fun values' =>
        irIf (decide (oldTag = 0))
          (NRest.bindT (mopBinop .add count 1) fun count' =>
            ammPack present' values' count')
          (ammPack present' values' count)

noncomputable def ammPackCost : ECost :=
  2 • irUnit Currency.skip

noncomputable def ammEmptyCost (N : ℕ) : ECost :=
  fillCost N + irUnit Currency.copy + ammPackCost

noncomputable def ammContainsCost : ECost := irUnit Currency.aget

noncomputable def ammLookupCost : ECost :=
  2 • irUnit Currency.aget + irUnit Currency.skip

noncomputable def ammUpdateCost (fresh : Bool) : ECost :=
  irUnit Currency.aget + 2 • irUnit Currency.aset + irUnit Currency.ite +
    (if fresh then irUnit Currency.add else 0) + ammPackCost

noncomputable def ammEmptyExecSpec (present values : List ℕ) :
    NRest (List ℕ × List ℕ × ℕ) ECost :=
  NRest.consume
    (NRest.returnT (List.replicate present.length 0, values, 0))
    (ammEmptyCost present.length)

noncomputable def ammContainsExecSpec (present : List ℕ) (k : ℕ) :
    NRest ℕ ECost :=
  NRest.consume (NRest.returnT present[k]!) ammContainsCost

noncomputable def ammLookupExecSpec (present values : List ℕ) (k : ℕ) :
    NRest (ℕ × ℕ) ECost :=
  NRest.consume (NRest.returnT (present[k]!, values[k]!)) ammLookupCost

noncomputable def ammUpdateExecSpec
    (present values : List ℕ) (count k v : ℕ) :
    NRest (List ℕ × List ℕ × ℕ) ECost :=
  let fresh := decide (present[k]! = 0)
  NRest.consume
    (NRest.returnT
      (present.set k 1, values.set k v, if fresh then count + 1 else count))
    (ammUpdateCost fresh)

theorem ammEmptyRaw_eq (present values : List ℕ) (oldCount : ℕ) :
    ammEmptyRaw present values oldCount = ammEmptyExecSpec present values := by
  simp [ammEmptyRaw, ammEmptyExecSpec, ammZeroCount, ammPack, ammEmptyCost,
    ammPackCost, mop_array_fill_def, mopCopy, mopPair_def, bindT_unit,
    NRest.consume_consume, two_nsmul]
  ac_rfl

theorem ammContainsRaw_eq (present : List ℕ) (k : ℕ)
    (hk : k < present.length) :
    ammContainsRaw present k = ammContainsExecSpec present k := by
  simp [ammContainsRaw, ammContainsExecSpec, ammContainsCost, mopAget_def,
    NRest.assert_pos hk]

theorem ammLookupRaw_eq (present values : List ℕ) (k : ℕ)
    (hp : k < present.length) (hv : k < values.length) :
    ammLookupRaw present values k = ammLookupExecSpec present values k := by
  simp [ammLookupRaw, ammLookupExecSpec, ammLookupCost, mopAget_def,
    NRest.assert_pos hp, NRest.assert_pos hv, bindT_unit, mopPair_def,
    NRest.consume_consume, two_nsmul]
  ac_rfl

theorem ammUpdateRaw_eq (present values : List ℕ) (count k v : ℕ)
    (hp : k < present.length) (hv : k < values.length) :
    ammUpdateRaw present values count k v =
      ammUpdateExecSpec present values count k v := by
  by_cases fresh : present[k]! = 0
  · have fresh' : present[k]?.getD 0 = 0 := by
      simpa [List.getElem!_eq_getElem?_getD] using fresh
    simp [ammUpdateRaw, ammUpdateExecSpec, mopAget_def, mopAset_def,
      NRest.assert_pos hp, NRest.assert_pos hv, irIf_def, fresh',
      mopBinop_def, ammPack, mopPair_def, ammUpdateCost, ammPackCost,
      NRest.bindT_consume NRest.addSupContinuousB_acost,
      NRest.consume_consume, two_nsmul]
    ac_rfl
  · have fresh' : ¬ present[k]?.getD 0 = 0 := by
      simpa [List.getElem!_eq_getElem?_getD] using fresh
    simp [ammUpdateRaw, ammUpdateExecSpec, mopAget_def, mopAset_def,
      NRest.assert_pos hp, NRest.assert_pos hv, irIf_def, fresh',
      ammPack, mopPair_def, ammUpdateCost, ammPackCost,
      NRest.bindT_consume NRest.addSupContinuousB_acost,
      NRest.consume_consume, two_nsmul]
    ac_rfl

sepref_synth ammEmptySynth (i P V count zero n one : String)
    (present values : List ℕ) (oldCount : ℕ) :
  hnRefine (junkCell i ∗ hnCtxt arrayAssn present P ∗
      hnCtxt arrayAssn values V ∗ hnCtxt natAssn oldCount count ∗
      hnCtxt natAssn 0 zero ∗ hnCtxt natAssn present.length n ∗
      hnCtxt natAssn 1 one)
    _ _ (P, V, count) (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (ammEmptyRaw present values oldCount)

sepref_synth ammContainsSynth (P key out : String)
    (present : List ℕ) (k : ℕ) :
  hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt natAssn k key ∗ junkCell out)
    _ _ out natAssn (ammContainsRaw present k)

sepref_synth ammLookupSynth (P V key tag out : String)
    (present values : List ℕ) (k : ℕ) :
  hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
      hnCtxt natAssn k key ∗ junkCell tag ∗ junkCell out)
    _ _ (tag, out) (natAssn ×ₐ natAssn)
    (ammLookupRaw present values k)

sepref_synth ammUpdateSynth (P V count key value tag zero one : String)
    (present values : List ℕ) (oldCount k v : ℕ) :
  hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
      hnCtxt natAssn oldCount count ∗ hnCtxt natAssn k key ∗
      hnCtxt natAssn v value ∗ junkCell tag ∗ hnCtxt natAssn 0 zero ∗
      hnCtxt natAssn 1 one)
    _ _ (P, V, count) (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (ammUpdateRaw present values oldCount k v)

def ammEmptyCom (i P _V count zero n one : String) : Com :=
  (fillCom i P zero one n).seq
    ((Com.copy count zero).seq (Com.skip.seq Com.skip))

def ammContainsCom (P key out : String) : Com :=
  Com.aget out P key

def ammLookupCom (P V key tag out : String) : Com :=
  (Com.aget tag P key).seq ((Com.aget out V key).seq Com.skip)

def ammUpdateCom (P V count key value tag zero one : String) : Com :=
  (Com.aget tag P key).seq
    ((Com.aset P key one).seq
      ((Com.aset V key value).seq
        (Com.ite (Cond.eq (Operand.cell tag) (Operand.cell zero))
          ((Com.binop .add count count one).seq (Com.skip.seq Com.skip))
          (Com.skip.seq Com.skip))))

@[sepref_fr_rules] theorem ammEmpty_exec_hnr
    (i P V count zero n one : String)
    (present values : List ℕ) (oldCount : ℕ) :
    hnRefine (junkCell i ∗ hnCtxt arrayAssn present P ∗
        hnCtxt arrayAssn values V ∗ hnCtxt natAssn oldCount count ∗
        hnCtxt natAssn 0 zero ∗ hnCtxt natAssn present.length n ∗
        hnCtxt natAssn 1 one)
      (ammEmptyCom i P V count zero n one)
      (hnCtxt natAssn 0 zero ∗ junkCell i ∗
        hnCtxt natAssn present.length n ∗ hnCtxt natAssn 1 one)
      (P, V, count) (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
      (ammEmptyExecSpec present values) := by
  rw [← ammEmptyRaw_eq present values oldCount]
  simpa only [ammEmptyCom] using
    (ammEmptySynth i P V count zero n one present values oldCount)

@[sepref_fr_rules] theorem ammContains_exec_hnr
    (P key out : String) (present : List ℕ) (k : ℕ)
    (hk : k < present.length) :
    hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt natAssn k key ∗ junkCell out)
      (ammContainsCom P key out)
      (hnCtxt arrayAssn present P ∗ hnCtxt natAssn k key)
      out natAssn (ammContainsExecSpec present k) := by
  rw [← ammContainsRaw_eq present k hk]
  exact ammContainsSynth P key out present k

@[sepref_fr_rules] theorem ammLookup_exec_hnr
    (P V key tag out : String) (present values : List ℕ) (k : ℕ)
    (hp : k < present.length) (hv : k < values.length) :
    hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
        hnCtxt natAssn k key ∗ junkCell tag ∗ junkCell out)
      (ammLookupCom P V key tag out)
      (hnCtxt arrayAssn values V ∗ hnCtxt natAssn k key ∗
        hnCtxt arrayAssn present P)
      (tag, out) (natAssn ×ₐ natAssn)
      (ammLookupExecSpec present values k) := by
  rw [← ammLookupRaw_eq present values k hp hv]
  simpa only [ammLookupCom] using
    (ammLookupSynth P V key tag out present values k)

@[sepref_fr_rules] theorem ammUpdate_exec_hnr
    (P V count key value tag zero one : String)
    (present values : List ℕ) (oldCount k v : ℕ)
    (hp : k < present.length) (hv : k < values.length) :
    hnRefine (hnCtxt arrayAssn present P ∗ hnCtxt arrayAssn values V ∗
        hnCtxt natAssn oldCount count ∗ hnCtxt natAssn k key ∗
        hnCtxt natAssn v value ∗ junkCell tag ∗ hnCtxt natAssn 0 zero ∗
        hnCtxt natAssn 1 one)
      (ammUpdateCom P V count key value tag zero one)
      (hnCtxt natAssn 1 one ∗ hnCtxt natAssn k key ∗
        hnCtxt natAssn v value ∗ junkCell tag ∗ hnCtxt natAssn 0 zero)
      (P, V, count) (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
      (ammUpdateExecSpec present values oldCount k v) := by
  rw [← ammUpdateRaw_eq present values oldCount k v hp hv]
  simpa only [ammUpdateCom] using
    (ammUpdateSynth P V count key value tag zero one
      present values oldCount k v)

/-! ## Whole-state executable bridges -/

theorem ammEmptyExecSpec_refines {N : ℕ} {present values : List ℕ}
    (hp : present.length = N) (hv : values.length = N) :
    ammEmptyExecSpec present values = NRest.consume
        (NRest.returnT (List.replicate N 0, values, 0)) (ammEmptyCost N) ∧
      (⟨List.replicate N 0, values, 0⟩,
        (mapEmpty : ℕ → Option ℕ)) ∈ amm1Rel N := by
  refine ⟨by simp [ammEmptyExecSpec, hp], ?_⟩
  apply ammEmptyIn_refines (present := present) (values := values)
  simp [ammEmptyIn, hp, hv]

theorem ammContainsExecSpec_refines {N : ℕ} {s : ArrayMapMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ amm1Rel N) {k : ℕ} (hk : k < N) :
    ammContainsExecSpec s.present k = NRest.consume
      (NRest.returnT (if decide (m k ≠ none) then 1 else 0)) ammContainsCost := by
  simpa [ArrayMapMap.base] using amContainsExecSpec_refines h.1 hk

theorem ammLookupExecSpec_refines {N : ℕ} {s : ArrayMapMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ amm1Rel N)
    {k v : ℕ} (hm : m k = some v) :
    ammLookupExecSpec s.present s.values k =
      NRest.consume (NRest.returnT (1, v)) ammLookupCost := by
  have hk : k < N := amm1Rel_key_bound h hm
  have hp : k < s.present.length := by
    have : k < s.base.present.length := by simpa [h.1.1.1] using hk
    simpa [ArrayMapMap.base] using this
  have htag := h.1.1.2.2 k hk
  have hlook := ammLookup_refines h k
  have heq : s.present[k]! = 1 ∧ s.values[k]! = v := by
    by_cases hz : s.present[k]! = 0
    · have hz' : s.present[k] = 0 := by
        simpa [getElem!_def, hp] using hz
      have : ammLookup s k = none := by
        simp [ammLookup, amLookup, amConcrete, ArrayMapMap.base, hp, hz']
      rw [hlook, hm] at this
      contradiction
    · have hone : s.present[k]! = 1 := htag.resolve_left hz
      refine ⟨hone, ?_⟩
      have hz' : s.present[k] ≠ 0 := by
        simpa [getElem!_def, hp] using hz
      have : ammLookup s k = some s.values[k]! := by
        simp [ammLookup, amLookup, amConcrete, ArrayMapMap.base, hp, hz']
      rw [hlook, hm] at this
      exact Option.some.inj this.symm
  simp [ammLookupExecSpec, heq.1, heq.2]

theorem ammUpdateExecSpec_refines {N : ℕ} {s : ArrayMapMap}
    {m : ℕ → Option ℕ} (h : (s, m) ∈ amm1Rel N)
    {k v : ℕ} (hk : k < N) :
    ammUpdateExecSpec s.present s.values s.count k v =
        NRest.consume
          (NRest.returnT
            (s.present.set k 1, s.values.set k v,
              if decide (s.present[k]! = 0) then s.count + 1 else s.count))
          (ammUpdateCost (decide (s.present[k]! = 0))) ∧
      (⟨s.present.set k 1, s.values.set k v,
          if decide (s.present[k]! = 0) then s.count + 1 else s.count⟩,
        mapUpdate m k v) ∈ amm1Rel N := by
  refine ⟨rfl, ?_⟩
  obtain ⟨t, ht, hrel⟩ := ammUpdate_refines h (v := v) hk
  have hp : k < s.present.length := by
    have : k < s.base.present.length := by simpa [h.1.1.1] using hk
    simpa [ArrayMapMap.base] using this
  have hv : k < s.values.length := by
    have : k < s.base.values.length := by simpa [h.1.1.2.1] using hk
    simpa [ArrayMapMap.base] using this
  have hcount :
      (if decide (s.present[k]! = 0) then s.count + 1 else s.count) =
        if amLookup s.base k = none then s.count + 1 else s.count := by
    by_cases hz : s.present[k]! = 0
    · have hz' : s.present[k] = 0 := by
        simpa [getElem!_def, hp] using hz
      simp [amLookup, amConcrete, ArrayMapMap.base, hp, hz']
    · have hz' : s.present[k] ≠ 0 := by
        simpa [getElem!_def, hp] using hz
      simp [amLookup, amConcrete, ArrayMapMap.base, hp, hz']
  have ht' : t =
      ⟨s.present.set k 1, s.values.set k v,
        if decide (s.present[k]! = 0) then s.count + 1 else s.count⟩ := by
    symm
    rw [hcount]
    simpa [ammUpdate, hp, hv] using ht
  subst t
  exact hrel

/-! The source's allocation-backed `new_liam`, deallocation, heap-reference
construction, and LLVM pointer export are unsupported.  `ammEmpty_exec_hnr`
is only the caller-owned initialization boundary and has no zero-cost stand-in
for any unsupported operation. -/

/-! ## Regression, source provenance, and gates -/

def ammRegression : Option ArrayMapMap := do
  let s0 := ammEmptyModel 8
  let s1 ← ammUpdate s0 2 41
  let s2 ← ammUpdate s1 2 42
  ammUpdate s2 5 7

#guard (ammRegression.map ArrayMapMap.count) = some 2
#guard (ammRegression.bind (fun s => ammLookup s 2)) = some 42
#guard (ammRegression.bind (fun s => ammLookup s 5)) = some 7
#guard (ammRegression.map (fun s => ammContains s 4)) = some false

/-- Scalar SepLogicTime/enat costs in the pinned Isabelle source. -/
def ammSourceEmptyBound (N : ℕ) : ℕ := N + 3
def ammSourceUpdateBound : ℕ := 6
def ammSourceContainsBound : ℕ := 2
def ammSourceLookupBound : ℕ := 2

#guard ammSourceEmptyBound 8 = 11
#guard ammSourceUpdateBound = 6
#guard ammSourceContainsBound = 2
#guard ammSourceLookupBound = 2

#guard ammEmptyCom "i" "P" "V" "count" "zero" "n" "one" =
  (fillCom "i" "P" "zero" "one" "n").seq
    ((Com.copy "count" "zero").seq (Com.skip.seq Com.skip))
#guard ammContainsCom "P" "key" "out" = Com.aget "out" "P" "key"
#guard ammLookupCom "P" "V" "key" "tag" "out" =
  (Com.aget "tag" "P" "key").seq
    ((Com.aget "out" "V" "key").seq Com.skip)
#guard ammUpdateCom "P" "V" "count" "key" "value" "tag" "zero" "one" =
  (Com.aget "tag" "P" "key").seq
    ((Com.aset "P" "key" "one").seq
      ((Com.aset "V" "key" "value").seq
        (Com.ite (Cond.eq (Operand.cell "tag") (Operand.cell "zero"))
          ((Com.binop .add "count" "count" "one").seq
            (Com.skip.seq Com.skip))
          (Com.skip.seq Com.skip))))

theorem ammEmptyCost_aset : (ammEmptyCost 3).toFun Currency.aset = 3 := by decide +kernel
theorem ammEmptyCost_copy : (ammEmptyCost 3).toFun Currency.copy = 1 := by decide +kernel
theorem ammEmptyCost_skip : (ammEmptyCost 3).toFun Currency.skip = 6 := by decide +kernel
theorem ammContainsCost_aget : ammContainsCost.toFun Currency.aget = 1 := by decide +kernel
theorem ammLookupCost_aget : ammLookupCost.toFun Currency.aget = 2 := by decide +kernel
theorem ammLookupCost_skip : ammLookupCost.toFun Currency.skip = 1 := by decide +kernel
theorem ammUpdateCost_fresh_aget : (ammUpdateCost true).toFun Currency.aget = 1 := by decide +kernel
theorem ammUpdateCost_fresh_aset : (ammUpdateCost true).toFun Currency.aset = 2 := by decide +kernel
theorem ammUpdateCost_fresh_ite : (ammUpdateCost true).toFun Currency.ite = 1 := by decide +kernel
theorem ammUpdateCost_fresh_add : (ammUpdateCost true).toFun Currency.add = 1 := by decide +kernel
theorem ammUpdateCost_existing_add : (ammUpdateCost false).toFun Currency.add = 0 := by decide +kernel
theorem ammUpdateCost_skip (fresh : Bool) :
    (ammUpdateCost fresh).toFun Currency.skip = 2 := by cases fresh <;> decide +kernel

private theorem ecost_ne_zero_of_pos_amm (C : ECost) (c : String)
    (h : 0 < C.toFun c) : C ≠ 0 := by
  intro hz
  rw [hz] at h
  simp at h

theorem ammEmptyCost_ne_zero : ammEmptyCost 3 ≠ 0 :=
  ecost_ne_zero_of_pos_amm _ Currency.aset (by simp [ammEmptyCost_aset])
theorem ammContainsCost_ne_zero : ammContainsCost ≠ 0 :=
  ecost_ne_zero_of_pos_amm _ Currency.aget (by simp [ammContainsCost_aget])
theorem ammLookupCost_ne_zero : ammLookupCost ≠ 0 :=
  ecost_ne_zero_of_pos_amm _ Currency.aget (by simp [ammLookupCost_aget])
theorem ammUpdateCost_ne_zero (fresh : Bool) : ammUpdateCost fresh ≠ 0 :=
  ecost_ne_zero_of_pos_amm _ Currency.aget (by
    cases fresh <;> decide +kernel)

example : opAmmEmptySz ::ᵢ
    (∀ α : Type, ℕ → NRest (MapI ℕ α) ECost) := opAmmEmptySz_itype

run_cmd do
  let frefs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``ammEmptyOp_refines, ``ammUpdateOp_refines,
      ``ammContainsOp_refines, ``ammLookupOp_refines] do
    unless frefs.contains n do
      throwError "array-map-map source rule missing from DB: {n}"
  let frules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  for n in #[``ammEmpty_exec_hnr, ``ammContains_exec_hnr,
      ``ammLookup_exec_hnr, ``ammUpdate_exec_hnr] do
    unless frules.contains n do
      throwError "array-map-map executable rule missing from DB: {n}"

/-! Every registered caller-owned operation above has a positive exact
vector cost.  Unsupported allocation/free have neither rules nor invented
budgets. -/

/-! ## Kernel-three gates -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amm1Rel_singleValued' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amm1Rel_singleValued

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.ammUpdateOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ammUpdateOp_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.ammEmpty_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ammEmpty_exec_hnr

end Lax13Proofs.Refine.Sepref.Iicf
