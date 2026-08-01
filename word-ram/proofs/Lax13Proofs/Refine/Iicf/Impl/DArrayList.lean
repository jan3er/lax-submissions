import Lax13Proofs.Refine.Iicf.IicfDynamicArray
import Lax13Proofs.Refine.Iicf.Intf.List

/-!
# Dynamic-array lists

Adaptation of Sepreftime's `IICF_DArray_List.thy` at commit
`c1c987b45ec886d289ba215768182ac87b82f20d`.

The source file is deliberately small: `da_assn R` composes a dynamic-array
assertion with `list_rel (the_pure R)`; it gives allocating empty and push
rules with scalar bounds 12 and 23, records `dyn_da`/cast/tag facts, and keeps
only the synthesis experiment using that exact 12/23 pair.

This backend has no allocator.  Consequently the 12/23 constants below are
source provenance, not executable `ECost`s.  Empty is a pure model plus a
caller-owned establishment boundary.  Push has two honest surfaces:

* a source-shaped successful List rule, restricted to pure element
  assertions and a representation known to have bounded room; and
* P4's fallible bounded dispatcher, including its observable success flag,
  exact branch-sensitive vector cost, and synthesized command.

No scalar source bound is transplanted into the IR cost algebra.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## Source constants and synthesis-experiment disposition -/

structure DaSourceBounds where
  empty : ℕ
  push : ℕ
  deriving DecidableEq, Repr

def daPinnedSourceBounds : DaSourceBounds := ⟨12, 23⟩

/-- Metadata for the source's two experiment declarations: only the exact
12/23 instantiation is the successful one.  This is intentionally not an IR
cost specification. -/
def daSourceExperimentSucceeds (b : DaSourceBounds) : Bool :=
  decide (b = daPinnedSourceBounds)

#guard daPinnedSourceBounds.empty = 12
#guard daPinnedSourceBounds.push = 23
#guard daSourceExperimentSucceeds ⟨12, 23⟩
#guard !daSourceExperimentSucceeds ⟨12, 12⟩

/-! ## `dyn_array`, `da_assn`, and their composition facts -/

def dynArrayRel : Set (BoundedArray × List ℕ) :=
  {p | p.1.Wf ∧ p.1.active = p.2}

def dynArrayAssn : List ℕ → String × String × String → Assn :=
  hrComp boundedArrayAssn dynArrayRel

@[intf_of_assn] theorem dynArrayAssn_intf :
    intfOfAssn dynArrayAssn (ListI ℕ) := trivial

def daRel {α : Type} (R : α → ℕ → Assn) : Set (BoundedArray × List α) :=
  relComp dynArrayRel (listRel (thePure R))

/-- Source `da_assn R = hr_comp dyn_array (<the_pure R>list_rel)`. -/
def daAssn {α : Type} (R : α → ℕ → Assn) :
    List α → String × String × String → Assn :=
  hrComp dynArrayAssn (listRel (thePure R))

@[intf_of_assn] theorem daAssn_intf {α : Type} (R : α → ℕ → Assn) :
    intfOfAssn (daAssn R) (ListI α) := trivial

private theorem listRel_diagonal_eq :
    listRel (Set.diagonal ℕ) = Set.diagonal (List ℕ) := by
  apply Set.ext
  rintro ⟨xs, ys⟩
  change List.Forall₂ (fun x y : ℕ => x = y) xs ys ↔ xs = ys
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons hxy _ ih =>
        cases hxy
        exact congrArg _ ih
  · intro h
    subst ys
    induction xs with
    | nil => exact List.Forall₂.nil
    | cons x xs ih => exact List.Forall₂.cons rfl ih

/-- The actual source `dyn_da` cast: `dyn_array = da_assn (pure Id)`. -/
theorem dyn_da :
    dynArrayAssn = daAssn (pureAssn (Set.diagonal ℕ)) := by
  rw [daAssn, thePure_pureAssn, listRel_diagonal_eq, hr_comp_Id2]

/-- Combined assertion fact (`dyn_array_assn`): open both `hr_comp`s at
once, without changing the pure element relation. -/
theorem dyn_array_assn {α : Type} (R : α → ℕ → Assn) :
    daAssn R = hrComp boundedArrayAssn (daRel R) := by
  rw [daAssn, dynArrayAssn, daRel, hr_comp_assoc]

/-- The empty-list simplification from the source: the element relation has
no witnesses to check. -/
@[simp] theorem daAssn_empty {α : Type} (R : α → ℕ → Assn)
    (c : String × String × String) :
    daAssn R [] c = dynArrayAssn [] c := by
  simp only [daAssn, hrComp_def]
  apply le_antisymm
  · intro st h
    obtain ⟨xs, hxs⟩ := h
    rw [sepConj_comm] at hxs
    obtain ⟨hrel, hda⟩ := predLift_sepConj_iff.1 hxs
    have : xs = [] := by
      change List.Forall₂ (fun x x' => (x, x') ∈ thePure R) xs [] at hrel
      cases hrel
      rfl
    simpa [this] using hda
  · intro st h
    refine ⟨[], ?_⟩
    change (dynArrayAssn [] c ∗ ⌜(([] : List ℕ), ([] : List α)) ∈
      listRel (thePure R)⌝) st
    rw [sepConj_comm]
    exact predLift_sepConj_iff.2 ⟨mem_listRel_nil, h⟩

/-! ## Empty: model and caller-owned boundary, never an allocation rule -/

def daInitialCapacity : ℕ := 16

def daEmptyState : BoundedArray :=
  ⟨List.replicate daInitialCapacity 0, 0, daInitialCapacity⟩

def daEmptyIn (buffer : List ℕ) : Option BoundedArray :=
  if daInitialCapacity ≤ buffer.length then
    some ⟨buffer, 0, daInitialCapacity⟩
  else none

theorem daEmptyState_dyn : (daEmptyState, []) ∈ dynArrayRel := by
  simp [dynArrayRel, daEmptyState, daInitialCapacity, BoundedArray.Wf,
    BoundedArray.active]

theorem daEmptyState_rel {α : Type} (R : α → ℕ → Assn) :
    (daEmptyState, []) ∈ daRel R :=
  ⟨[], daEmptyState_dyn, mem_listRel_nil⟩

theorem daEmptyIn_some {buffer : List ℕ} {s : BoundedArray}
    (h : daEmptyIn buffer = some s) : (s, []) ∈ dynArrayRel := by
  simp only [daEmptyIn] at h
  split at h
  · rename_i hcap
    simp only [Option.some.injEq] at h
    subst s
    exact ⟨⟨by simp [daInitialCapacity], by simp, by simpa using hcap⟩,
      by simp [BoundedArray.active]⟩
  · contradiction

noncomputable def daEmptyOp : NRest BoundedArray ECost :=
  NRest.returnT daEmptyState

theorem daEmptyOp_refines {α : Type} (R : α → ℕ → Assn) :
    (daEmptyOp, op_list_empty α) ∈ NRest.nrestRel (daRel R) := by
  exact NRest.param_returnT (daEmptyState_rel R)

/-! ## Push: source-shaped value rule and bounded executable rule -/

def daPush (s : BoundedArray) (x : ℕ) : Option BoundedArray :=
  boundedPush s x

noncomputable def daPushOp (s : BoundedArray) (x : ℕ) : NRest BoundedArray ECost :=
  match daPush s x with
  | some t => NRest.returnT t
  | none => NRest.fail

def daReadyRel {α : Type} (R : α → ℕ → Assn) : Set (BoundedArray × List α) :=
  {p | (p.1, p.2) ∈ daRel R ∧ boundedPush p.1 0 ≠ none}

theorem daPush_some_refines {α : Type} {R : α → ℕ → Assn}
    {s t : BoundedArray} {xs : List α} {x : ℕ} {a : α}
    (hs : (s, xs) ∈ daRel R) (hxa : (x, a) ∈ thePure R)
    (hp : daPush s x = some t) : (t, xs ++ [a]) ∈ daRel R := by
  obtain ⟨ns, hsn, hnxs⟩ := hs
  have ht : (t, ns ++ [x]) ∈ dynArrayRel := by
    rcases hsn with ⟨hwf, hactive⟩
    exact ⟨boundedPush_some_wf s t x hwf hp,
      (boundedPush_some_active s t x hwf hp).trans (congrArg (· ++ [x]) hactive)⟩
  have htail : ([x], [a]) ∈ listRel (thePure R) := by
    exact List.Forall₂.cons hxa List.Forall₂.nil
  exact ⟨ns ++ [x], ht, List.rel_append hnxs htail⟩

/-- The successful source-shaped rule keeps the source's pure-element
restriction.  Its abstract List operation is cost-silent; the executable
rule below is the separate exact-cost level. -/
@[sepref_fref_thms] theorem daPushOp_refines {α : Type}
    (R : α → ℕ → Assn) (_hR : isPure R) :
    (daPushOp, op_list_append α) ∈
      fref (fun _ : List α => True) (daReadyRel R)
        (fun _ => thePure R →ᵣ NRest.nrestRel (daRel R)) := by
  intro s xs _ hs x a hxa
  have hsome : ∃ t, daPush s x = some t := by
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hwf : s.Wf := hs.1.choose_spec.1.1
    have hf := (boundedPush_eq_none_iff s x hwf).mp hnone
    have h0 : boundedPush s 0 = none :=
      (boundedPush_eq_none_iff s 0 hwf).mpr hf
    exact hs.2 h0
  obtain ⟨t, ht⟩ := hsome
  simp [daPushOp, ht, op_list_append]
  exact NRest.param_returnT (daPush_some_refines hs.1 hxa ht)

/-- Exact, fallible P4 dispatcher.  Failure remains observable as flag `0`;
success returns flag `1`.  Its cost is `boundedExecCost s`, derived from this
actual command's branches and currencies. -/
@[sepref_fr_rules] theorem daPush_exec_hnr
    (s : BoundedArray) (x : ℕ) (hwf : s.Wf)
    (A len cap phys value one two outLen outCap ok doubled : String) :
    hnRefine (boundedExecPre s x A len cap phys value one two outLen outCap ok doubled)
      (boundedExecCom A len cap phys value one two outLen outCap ok doubled)
      (boundedExecPost s x len cap value one two doubled)
      (ok, (A, (outLen, (outCap, phys)))) boundedRawAssn (boundedExecSpec s x) :=
  boundedExec_hnr s x hwf A len cap phys value one two outLen outCap ok doubled

/-! ## Gates -/

#guard daInitialCapacity = 16
#guard daEmptyIn (List.replicate 16 9) = some ⟨List.replicate 16 9, 0, 16⟩
#guard daEmptyIn (List.replicate 15 9) = none
#guard daPush ⟨[0, 0, 0, 0], 1, 4⟩ 7 = some ⟨[0, 7, 0, 0], 2, 4⟩
#guard daPush ⟨List.replicate 8 0, 2, 2⟩ 5 =
  some ⟨(List.replicate 8 0).set 2 5, 3, 4⟩
#guard daPush ⟨[1, 2, 3, 4], 4, 4⟩ 9 = none

#guard boundedExecCom "A" "len" "cap" "phys" "value" "one" "two"
    "outLen" "outCap" "ok" "doubled" =
  Com.ite (.lt (.cell "len") (.cell "cap"))
    (boundedSuccessCom "A" "len" "cap" "value" "one" "outLen" "outCap" "ok")
    ((Com.binop .mul "doubled" "cap" "two").seq
      (Com.ite (.lt (.cell "phys") (.cell "doubled"))
        (boundedFailCom "len" "cap" "outLen" "outCap" "ok")
        (boundedSuccessCom "A" "len" "doubled" "value" "one"
          "outLen" "outCap" "ok")))

def daNoResizeSample : BoundedArray := ⟨[0, 0, 0, 0], 1, 4⟩
def daGrowSample : BoundedArray := ⟨List.replicate 8 0, 2, 2⟩
def daFailSample : BoundedArray := ⟨[1, 2, 3, 4], 4, 4⟩

theorem daNoResizeCost_aset :
    (boundedExecCost daNoResizeSample).toFun Currency.aset = 1 := by decide +kernel
theorem daNoResizeCost_ite :
    (boundedExecCost daNoResizeSample).toFun Currency.ite = 1 := by decide +kernel
theorem daGrowCost_mul :
    (boundedExecCost daGrowSample).toFun Currency.mul = 1 := by decide +kernel
theorem daGrowCost_ite :
    (boundedExecCost daGrowSample).toFun Currency.ite = 2 := by decide +kernel
theorem daFailCost_aset_zero :
    (boundedExecCost daFailSample).toFun Currency.aset = 0 := by decide +kernel
theorem daFailCost_copy_nonzero :
    (boundedExecCost daFailSample).toFun Currency.copy = 2 := by decide +kernel

run_cmd do
  let irules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `intf_of_assn
  for n in #[``dynArrayAssn_intf, ``daAssn_intf] do
    unless irules.contains n do
      throwError "darray-list tag gate: missing assertion interface {n}"
  let frefs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  unless frefs.contains ``daPushOp_refines do
    throwError "darray-list rule gate: source-shaped push rule was not consumed"
  let frules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  unless frules.contains ``daPush_exec_hnr do
    throwError "darray-list rule gate: executable push rule was not consumed"

/-! The only zero executable component above is the failed branch's array
write, which is a semantic negative control.  The executed failure branch
still pays two metadata copies; no whole-operation zero placeholder exists. -/

/-! ## Kernel-three gates -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.dyn_da' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dyn_da

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.daPush_some_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms daPush_some_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.daPush_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms daPush_exec_hnr

end Lax13Proofs.Refine.Sepref.Iicf
