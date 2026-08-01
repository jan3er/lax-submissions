import Lax13Proofs.Refine.Iicf.Intf.Map
import Lax13Proofs.Refine.Iicf.IicfArray

/-!
# Partial dense array map

Faithful adaptation of `IICF/Impl/IICF_Array_Map_Total.thy` at
`isabelle_llvm_time` commit
`42dd7f59998d76047bb4b6bce76d8f67b53a08b6`.

Despite the source name, this is deliberately a *partial* map whose lookup is
valid only for keys already present.  A single length-`N` backing array is
used.  Present abstract entries constrain their corresponding cells; absent
entries leave arbitrary garbage.  Consequently the representation relation
is intentionally not single-valued.

The source allocates its initialized array and later derives `free`.  P0 has
neither operation, so executable init below fills an already-owned `N`-cell
array.  No allocation, deallocation, pointer export, or zero-cost placeholder
is claimed.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

def amt1Rel (N : ℕ) : Set (List ℕ × (ℕ → Option ℕ)) :=
  {p | p.1.length = N ∧
    ∀ k v, p.2 k = some v → k < N ∧ v = p.1[k]!}

theorem amt1Rel_domain_bound {N : ℕ} {xs : List ℕ} {m : ℕ → Option ℕ}
    (h : (xs, m) ∈ amt1Rel N) {k v : ℕ} (hm : m k = some v) : k < N :=
  (h.2 k v hm).1

def amtRel {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    Set (List ℕ × (ℕ → Option α)) :=
  relComp (amt1Rel N) (mapRel (Set.diagonal ℕ) (thePure A))

def amt1Assn (N : ℕ) : (ℕ → Option ℕ) → String → Assn :=
  hrComp arrayAssn (amt1Rel N)

/-- The source's double assertion composition: array → concrete map →
generic interface map. -/
def amtAssn {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    (ℕ → Option α) → String → Assn :=
  hrComp (amt1Assn N) (mapRel (Set.diagonal ℕ) (thePure A))

@[intf_of_assn] theorem amtAssn_intf {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) : intfOfAssn (amtAssn N A) (MapI ℕ α) := trivial

theorem amtAssn_comp {α : Type} (N : ℕ) (A : α → ℕ → Assn) :
    amtAssn N A = hrComp arrayAssn (amtRel N A) := by
  rw [amtAssn, amt1Assn, amtRel, hr_comp_assoc]

/-! ## Functional representation operations -/

def amtInitModel (N : ℕ) : List ℕ := List.replicate N 0

def amtInitIn (N : ℕ) (xs : List ℕ) : Option (List ℕ) :=
  if xs.length = N then some (List.replicate N 0) else none

def amtLookup (xs : List ℕ) (k : ℕ) : Option ℕ :=
  if k < xs.length then some xs[k]! else none

def amtUpdate (xs : List ℕ) (k v : ℕ) : Option (List ℕ) :=
  if k < xs.length then some (xs.set k v) else none

theorem amtInitModel_refines (N : ℕ) :
    (amtInitModel N, (mapEmpty : ℕ → Option ℕ)) ∈ amt1Rel N := by
  refine ⟨by simp [amtInitModel], ?_⟩
  intro k v hm
  simp [mapEmpty] at hm

theorem amtInitIn_refines {N : ℕ} {xs ys : List ℕ}
    (h : amtInitIn N xs = some ys) :
    (ys, (mapEmpty : ℕ → Option ℕ)) ∈ amt1Rel N := by
  simp only [amtInitIn] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst ys
    exact amtInitModel_refines N
  · contradiction

theorem amtLookup_refines {N : ℕ} {xs : List ℕ} {m : ℕ → Option ℕ}
    (h : (xs, m) ∈ amt1Rel N) {k v : ℕ} (hm : m k = some v) :
    amtLookup xs k = some v := by
  have hk := (h.2 k v hm).1
  have hv := (h.2 k v hm).2
  have hkx : k < xs.length := by simpa [h.1] using hk
  simp [amtLookup, hkx, hv]

private theorem getElem!_set_self (xs : List ℕ) (k v : ℕ)
    (hk : k < xs.length) : (xs.set k v)[k]! = v := by
  rw [getElem!_def]
  simp [hk]

private theorem getElem!_set_of_ne (xs : List ℕ) (k i v : ℕ)
    (hi : i < xs.length) (hik : i ≠ k) :
    (xs.set k v)[i]! = xs[i]! := by
  induction xs generalizing k i with
  | nil => simp at hi
  | cons x xs ih =>
      cases k with
      | zero => cases i <;> simp_all
      | succ k =>
          cases i with
          | zero => simp
          | succ i => simpa using ih k i (by simpa using hi) (by omega)

theorem amtUpdate_refines {N : ℕ} {xs : List ℕ} {m : ℕ → Option ℕ}
    (h : (xs, m) ∈ amt1Rel N) {k v : ℕ} (hk : k < N) :
    ∃ ys, amtUpdate xs k v = some ys ∧
      (ys, mapUpdate m k v) ∈ amt1Rel N := by
  have hkx : k < xs.length := by simpa [h.1] using hk
  refine ⟨xs.set k v, by simp [amtUpdate, hkx], by simp [h.1], ?_⟩
  intro i w hiw
  by_cases hik : i = k
  · subst i
    have hw : w = v := by simpa [mapUpdate] using hiw.symm
    subst w
    exact ⟨hk, (getElem!_set_self xs k v hkx).symm⟩
  · have hm : m i = some w := by simpa [mapUpdate, hik] using hiw
    have hold := h.2 i w hm
    exact ⟨hold.1, hold.2.trans
      (getElem!_set_of_ne xs k i v (by simpa [h.1] using hold.1) hik).symm⟩

/-! ## Custom empty and generic interface refinements -/

noncomputable def opAmtEmptySz (α : Type) (_N : ℕ) :
    NRest (ℕ → Option α) ECost := op_map_empty ℕ α

sepref_register opAmtEmptySz : opAmtEmptySz as
  (∀ α : Type, ℕ → NRest (MapI ℕ α) ECost)

theorem amt_fold_custom_empty {α : Type} (N : ℕ) :
    op_map_empty ℕ α = opAmtEmptySz α N := rfl

noncomputable def amtInitOp (N : ℕ) : NRest (List ℕ) ECost :=
  NRest.returnT (amtInitModel N)

noncomputable def amtLookupOp (k : ℕ) (xs : List ℕ) : NRest ℕ ECost :=
  match amtLookup xs k with
  | some v => NRest.returnT v
  | none => NRest.fail

noncomputable def amtUpdateOp (_N k v : ℕ) (xs : List ℕ) :
    NRest (List ℕ) ECost :=
  match amtUpdate xs k v with
  | some ys => NRest.returnT ys
  | none => NRest.fail

private theorem diagonal_converse_singleValued_amt :
    SingleValued (relConverse (Set.diagonal ℕ)) := by
  rintro b a a' h h'
  change a = b at h
  change a' = b at h'
  exact h.trans h'.symm

@[sepref_fref_thms] theorem amtInitOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amtInitOp N, opAmtEmptySz α N) ∈ NRest.nrestRel (amtRel N A) := by
  apply NRest.param_returnT
  exact ⟨mapEmpty, amtInitModel_refines N,
    mapRel_empty (Set.diagonal ℕ) (thePure A)⟩

@[sepref_fref_thms] theorem amtLookupOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amtLookupOp, fun k m => op_map_the_lookup ℕ α (k, m)) ∈
      fref (fun k : ℕ => k < N) (Set.diagonal ℕ)
        (fun k => fref (fun m : ℕ → Option α => m k ≠ none)
          (amtRel N A) (fun _ => NRest.nrestRel (thePure A))) := by
  intro k l _ hkl xs m hm hrel
  change k = l at hkl
  subst l
  obtain ⟨cm, hxcm, hcmm⟩ := hrel
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
  simp [amtLookupOp, amtLookup_refines hxcm hcv']
  exact NRest.param_returnT hva

@[sepref_fref_thms] theorem amtUpdateOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amtUpdateOp N, op_map_update ℕ α) ∈
      fref (fun k : ℕ => k < N) (Set.diagonal ℕ)
        (fun _ => thePure A →ᵣ amtRel N A →ᵣ NRest.nrestRel (amtRel N A)) := by
  intro k l hk hkl v a hva xs m hrel
  change k = l at hkl
  subst l
  obtain ⟨cm, hxcm, hcmm⟩ := hrel
  obtain ⟨ys, hys, hycm⟩ := amtUpdate_refines hxcm (v := v) hk
  simp [amtUpdateOp, hys, op_map_update]
  exact NRest.param_returnT ⟨mapUpdate cm k v, hycm,
    mapRel_update singleValued_diagonal diagonal_converse_singleValued_amt
      rfl hva hcmm⟩

/-! ## Exact executable one-array operations -/

noncomputable def amtInitRaw (xs : List ℕ) : NRest (List ℕ) ECost :=
  mop_array_fill xs 0

noncomputable def amtLookupRaw (xs : List ℕ) (k : ℕ) : NRest ℕ ECost :=
  mopAget xs k

noncomputable def amtUpdateRaw (xs : List ℕ) (k v : ℕ) :
    NRest (List ℕ) ECost := mopAset xs k v

noncomputable def amtInitCost (N : ℕ) : ECost := fillCost N
noncomputable def amtLookupCost : ECost := irUnit Currency.aget
noncomputable def amtUpdateCost : ECost := irUnit Currency.aset

noncomputable def amtInitExecSpec (xs : List ℕ) : NRest (List ℕ) ECost :=
  NRest.consume (NRest.returnT (List.replicate xs.length 0))
    (amtInitCost xs.length)

noncomputable def amtLookupExecSpec (xs : List ℕ) (k : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT xs[k]!) amtLookupCost

noncomputable def amtUpdateExecSpec (xs : List ℕ) (k v : ℕ) :
    NRest (List ℕ) ECost :=
  NRest.consume (NRest.returnT (xs.set k v)) amtUpdateCost

theorem amtInitRaw_eq (xs : List ℕ) :
    amtInitRaw xs = amtInitExecSpec xs := rfl

theorem amtLookupRaw_eq (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    amtLookupRaw xs k = amtLookupExecSpec xs k := by
  simp [amtLookupRaw, amtLookupExecSpec, amtLookupCost, mopAget_def,
    NRest.assert_pos hk]

theorem amtUpdateRaw_eq (xs : List ℕ) (k v : ℕ) (hk : k < xs.length) :
    amtUpdateRaw xs k v = amtUpdateExecSpec xs k v := by
  simp [amtUpdateRaw, amtUpdateExecSpec, amtUpdateCost, mopAset_def,
    NRest.assert_pos hk]

sepref_synth amtInitSynth (i A zero n one : String) (xs : List ℕ) :
  hnRefine (junkCell i ∗ hnCtxt arrayAssn xs A ∗ hnCtxt natAssn 0 zero ∗
      hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one)
    _ _ A arrayAssn (amtInitRaw xs)

sepref_synth amtLookupSynth (A key out : String) (xs : List ℕ) (k : ℕ) :
  hnRefine (hnCtxt arrayAssn xs A ∗ hnCtxt natAssn k key ∗ junkCell out)
    _ _ out natAssn (amtLookupRaw xs k)

sepref_synth amtUpdateSynth (A key value : String) (xs : List ℕ) (k v : ℕ) :
  hnRefine (hnCtxt arrayAssn xs A ∗ hnCtxt natAssn k key ∗
      hnCtxt natAssn v value)
    _ _ A arrayAssn (amtUpdateRaw xs k v)

def amtInitCom := fillCom
def amtLookupCom (A key out : String) : Com := Com.aget out A key
def amtUpdateCom (A key value : String) : Com := Com.aset A key value

@[sepref_fr_rules] theorem amtInit_exec_hnr
    (i A zero n one : String) (xs : List ℕ) :
    hnRefine (junkCell i ∗ hnCtxt arrayAssn xs A ∗ hnCtxt natAssn 0 zero ∗
        hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one)
      (amtInitCom i A zero one n)
      (junkCell i ∗ hnCtxt natAssn 0 zero ∗
        hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one)
      A arrayAssn (amtInitExecSpec xs) := by
  rw [← amtInitRaw_eq xs]
  exact amtInitSynth i A zero n one xs

@[sepref_fr_rules] theorem amtLookup_exec_hnr
    (A key out : String) (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    hnRefine (hnCtxt arrayAssn xs A ∗ hnCtxt natAssn k key ∗ junkCell out)
      (amtLookupCom A key out)
      (hnCtxt arrayAssn xs A ∗ hnCtxt natAssn k key)
      out natAssn (amtLookupExecSpec xs k) := by
  rw [← amtLookupRaw_eq xs k hk]
  exact amtLookupSynth A key out xs k

@[sepref_fr_rules] theorem amtUpdate_exec_hnr
    (A key value : String) (xs : List ℕ) (k v : ℕ) (hk : k < xs.length) :
    hnRefine (hnCtxt arrayAssn xs A ∗ hnCtxt natAssn k key ∗
        hnCtxt natAssn v value)
      (amtUpdateCom A key value)
      (hnCtxt natAssn k key ∗ hnCtxt natAssn v value)
      A arrayAssn (amtUpdateExecSpec xs k v) := by
  rw [← amtUpdateRaw_eq xs k v hk]
  exact amtUpdateSynth A key value xs k v

/-! ## Whole-state executable bridges -/

theorem amtInitExecSpec_refines {N : ℕ} {xs : List ℕ}
    (hN : xs.length = N) :
    amtInitExecSpec xs = NRest.consume
        (NRest.returnT (List.replicate N 0)) (amtInitCost N) ∧
      (List.replicate N 0, (mapEmpty : ℕ → Option ℕ)) ∈ amt1Rel N := by
  exact ⟨by simp [amtInitExecSpec, hN], amtInitModel_refines N⟩

theorem amtLookupExecSpec_refines {N : ℕ} {xs : List ℕ}
    {m : ℕ → Option ℕ} (h : (xs, m) ∈ amt1Rel N)
    {k v : ℕ} (hm : m k = some v) :
    amtLookupExecSpec xs k =
      NRest.consume (NRest.returnT v) amtLookupCost := by
  have hk : k < xs.length := by simpa [h.1] using (h.2 k v hm).1
  have hv := (h.2 k v hm).2
  simp [amtLookupExecSpec, hv]

theorem amtUpdateExecSpec_refines {N : ℕ} {xs : List ℕ}
    {m : ℕ → Option ℕ} (h : (xs, m) ∈ amt1Rel N)
    {k v : ℕ} (hk : k < N) :
    amtUpdateExecSpec xs k v =
        NRest.consume (NRest.returnT (xs.set k v)) amtUpdateCost ∧
      (xs.set k v, mapUpdate m k v) ∈ amt1Rel N := by
  refine ⟨rfl, ?_⟩
  obtain ⟨ys, hys, hrel⟩ := amtUpdate_refines h (v := v) hk
  have hkx : k < xs.length := by simpa [h.1] using hk
  have heq : ys = xs.set k v := by
    symm
    simpa [amtUpdate, hkx] using hys
  subst ys
  exact hrel

/-! Source allocation-backed init, `MK_FREE`, and LLVM pointer export are
unsupported.  `amtInit_exec_hnr` is the caller-owned initialization boundary.
-/

/-! ## Regression and gates -/

def amtRegression : Option (List ℕ) := do
  let xs0 := amtInitModel 8
  let xs1 ← amtUpdate xs0 2 42
  amtUpdate xs1 4 7

#guard (amtRegression.bind (fun xs => amtLookup xs 2)) = some 42
#guard (amtRegression.bind (fun xs => amtLookup xs 4)) = some 7

#guard amtInitCom "i" "A" "zero" "one" "n" =
  fillCom "i" "A" "zero" "one" "n"
#guard amtLookupCom "A" "key" "out" = Com.aget "out" "A" "key"
#guard amtUpdateCom "A" "key" "value" = Com.aset "A" "key" "value"

theorem amtInitCost_aset : (amtInitCost 3).toFun Currency.aset = 3 := by decide +kernel
theorem amtInitCost_add : (amtInitCost 3).toFun Currency.add = 3 := by decide +kernel
theorem amtInitCost_while : (amtInitCost 3).toFun Currency.«while» = 4 := by decide +kernel
theorem amtInitCost_const : (amtInitCost 3).toFun Currency.const = 1 := by decide +kernel
theorem amtInitCost_skip : (amtInitCost 3).toFun Currency.skip = 4 := by decide +kernel
theorem amtLookupCost_aget : amtLookupCost.toFun Currency.aget = 1 := by decide +kernel
theorem amtUpdateCost_aset : amtUpdateCost.toFun Currency.aset = 1 := by decide +kernel

private theorem ecost_ne_zero_of_pos_amt (C : ECost) (c : String)
    (h : 0 < C.toFun c) : C ≠ 0 := by
  intro hz
  rw [hz] at h
  simp at h

theorem amtInitCost_ne_zero : amtInitCost 3 ≠ 0 :=
  ecost_ne_zero_of_pos_amt _ Currency.aset (by simp [amtInitCost_aset])
theorem amtLookupCost_ne_zero : amtLookupCost ≠ 0 :=
  ecost_ne_zero_of_pos_amt _ Currency.aget (by simp [amtLookupCost_aget])
theorem amtUpdateCost_ne_zero : amtUpdateCost ≠ 0 :=
  ecost_ne_zero_of_pos_amt _ Currency.aset (by simp [amtUpdateCost_aset])

example : opAmtEmptySz ::ᵢ
    (∀ α : Type, ℕ → NRest (MapI ℕ α) ECost) := opAmtEmptySz_itype

run_cmd do
  let frefs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``amtInitOp_refines, ``amtLookupOp_refines,
      ``amtUpdateOp_refines] do
    unless frefs.contains n do
      throwError "array-map-total source rule missing from DB: {n}"
  let frules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  for n in #[``amtInit_exec_hnr, ``amtLookup_exec_hnr,
      ``amtUpdate_exec_hnr] do
    unless frules.contains n do
      throwError "array-map-total executable rule missing from DB: {n}"

/-! Allocation/free have no rule and no invented budget.  Every registered
caller-owned operation has a positive exact cost above. -/

/-! ## Kernel-three gates -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amt1Rel_domain_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms amt1Rel_domain_bound

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amtLookupOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amtLookupOp_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amtInit_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amtInit_exec_hnr

end Lax13Proofs.Refine.Sepref.Iicf
