import Lax13Proofs.Refine.Iicf.Basic
import Lax13Proofs.Refine.Sepref.Amortization

/-!
# Dynamic arrays: abstract amortization and a bounded no-allocation adapter

The source's mathematical dynamic array doubles an owned buffer.  Its concrete
allocator is unfinished, and this repository's IR has no allocation operation.
Accordingly this module has two deliberately separate faces:

* `SourceArray` is the source-faithful functional model.  It doubles a list,
  proves the list abstraction, and carries the standard `2 * length - capacity`
  potential proof.
* `BoundedArray` owns one caller-provided physical buffer.  Its logical capacity
  may double only when the already-owned buffer is large enough.  A push returns
  `none` when no such operation is possible.  Nothing here allocates or frees.

Source accounting:

| source | range | disposition |
|---|---:|---|
| `Dynamic_Array.thy` | 464--585 | landed: snoc, representation, push specification/refinement |
| `Dynamic_Array.thy` | 596--618 | bounded init is adaptation glue; allocation itself is excluded |
| `Dynamic_Array.thy` | 622--628 | excluded: the source proof is unfinished |
| `Dynamic_Array.thy` | 646--715, 746--795 | landed: doubling, basic push, potential and amortized push |
| `Dynamic_Array.thy` | 717--742 | excluded: unfinished sketch superseded by the completed theorem |
| `Dynamic_Array.thy` | 798--818 | abstract empty state landed; allocating implementation excluded |
| `Dynamic_Array.thy` | 820--1005, 1028--1091 | existing A1 composition API plus bounded assertion below |
| `IHT_Dynamic_Array.thy` | 5--203 | landed: raw model, doubling, push, abstraction and first potential |
| `IHT_Dynamic_Array_More.thy` | 5--147 | landed: public constant advertised push surface; swap/filter excluded by range |

The cost used in proofs is vector-valued.  `PushCost` is its executable mirror;
`PushCost.toECost` embeds it into A1's `ECost` without scalarization.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Ir NRest

/-! ## 1. Executable vector costs -/

/-- An executable mirror of the four independent dynamic-array currencies. -/
structure PushCost where
  control : ℕ
  write : ℕ
  add : ℕ
  copy : ℕ
  deriving DecidableEq, Repr

namespace PushCost

def zero : PushCost := ⟨0, 0, 0, 0⟩

def plus (a b : PushCost) : PushCost :=
  ⟨a.control + b.control, a.write + b.write, a.add + b.add, a.copy + b.copy⟩

def le (a b : PushCost) : Prop :=
  a.control ≤ b.control ∧ a.write ≤ b.write ∧ a.add ≤ b.add ∧ a.copy ≤ b.copy

instance : LE PushCost := ⟨le⟩

@[simp] theorem le_def (a b : PushCost) :
    a ≤ b ↔ a.control ≤ b.control ∧ a.write ≤ b.write ∧
      a.add ≤ b.add ∧ a.copy ≤ b.copy := Iff.rfl

abbrev controlCurrency : String := "dyn.control"
abbrev writeCurrency : String := "dyn.write"
abbrev addCurrency : String := "dyn.add"
abbrev copyCurrency : String := "dyn.copy"

/-- The primary vector cost, embedded into the tower's `ECost`. -/
noncomputable def toECost (c : PushCost) : ECost :=
  ACost.cost controlCurrency (c.control : ℕ∞) +
    ACost.cost writeCurrency (c.write : ℕ∞) +
    ACost.cost addCurrency (c.add : ℕ∞) +
    ACost.cost copyCurrency (c.copy : ℕ∞)

theorem toECost_plus (a b : PushCost) :
    toECost (plus a b) = toECost a + toECost b := by
  simp only [toECost, plus, Nat.cast_add, ← ACost.cost_add_cost]
  abel

theorem toECost_mono {a b : PushCost} (h : a ≤ b) : toECost a ≤ toECost b := by
  apply ACost.le_def.mpr
  intro k
  rcases h with ⟨hc, hw, ha, hp⟩
  by_cases hcontrol : k = controlCurrency
  · subst k
    simpa [toECost, controlCurrency, writeCurrency, addCurrency, copyCurrency] using
      ENat.coe_le_coe.mpr hc
  · by_cases hwrite : k = writeCurrency
    · subst k
      simpa [toECost, controlCurrency, writeCurrency, addCurrency, copyCurrency] using
        ENat.coe_le_coe.mpr hw
    · by_cases hadd : k = addCurrency
      · subst k
        simpa [toECost, controlCurrency, writeCurrency, addCurrency, copyCurrency] using
          ENat.coe_le_coe.mpr ha
      · by_cases hcopy : k = copyCurrency
        · subst k
          simpa [toECost, controlCurrency, writeCurrency, addCurrency, copyCurrency] using
            ENat.coe_le_coe.mpr hp
        · simp [toECost, hcontrol, hwrite, hadd, hcopy]

end PushCost

/-! ## 2. The source-faithful abstract array -/

structure SourceArray where
  buffer : List ℕ
  length : ℕ
  deriving DecidableEq, Repr

def SourceArray.capacity (s : SourceArray) : ℕ := s.buffer.length

def SourceArray.Wf (s : SourceArray) : Prop :=
  0 < s.capacity ∧ s.length ≤ s.capacity

def SourceArray.active (s : SourceArray) : List ℕ := s.buffer.take s.length

def sourceEmpty (initialCapacity : ℕ) : SourceArray :=
  ⟨List.replicate initialCapacity 0, 0⟩

def sourceDouble (s : SourceArray) : SourceArray :=
  ⟨s.buffer ++ List.replicate s.capacity 0, s.length⟩

def sourcePushBasic (s : SourceArray) (x : ℕ) : SourceArray :=
  ⟨s.buffer.set s.length x, s.length + 1⟩

def sourcePush (s : SourceArray) (x : ℕ) : SourceArray :=
  if s.length < s.capacity then sourcePushBasic s x
  else sourcePushBasic (sourceDouble s) x

/-- The standard doubling potential, in the resize/copy currency. -/
def sourcePotentialN (s : SourceArray) : PushCost :=
  ⟨0, 0, 0, 2 * s.length - s.capacity⟩

/-- Actual source cost: fixed overhead, plus one copy per old slot on resize. -/
def sourceRawCostN (s : SourceArray) : PushCost :=
  ⟨1, 1, 1, if s.length < s.capacity then 0 else s.capacity⟩

/-- The advertised cost is independent of the current length and capacity. -/
def sourceAdvertisedCostN : PushCost := ⟨1, 1, 1, 2⟩

/-- IHT More's second potential: four credits per live element. -/
def sourceOuterPotentialN (s : SourceArray) : PushCost :=
  ⟨0, 0, 0, 4 * s.length⟩

/-- The nested public assertion carries both source potentials. -/
def sourcePublicPotentialN (s : SourceArray) : PushCost :=
  PushCost.plus (sourcePotentialN s) (sourceOuterPotentialN s)

/-- Public push pays four more credits to replenish the outer potential. -/
def sourcePublicAdvertisedCostN : PushCost := ⟨1, 1, 1, 6⟩

noncomputable def sourcePotential (s : SourceArray) : ECost :=
  sourcePotentialN s |>.toECost

noncomputable def sourceRawCost (s : SourceArray) : ECost :=
  sourceRawCostN s |>.toECost

noncomputable def sourceAdvertisedCost : ECost := sourceAdvertisedCostN.toECost

private theorem take_set_self (l : List ℕ) (k a : ℕ) :
    (l.set k a).take k = l.take k := by
  refine List.ext_getElem (by simp) fun m h1 h2 => ?_
  have hm : m < k := (show m < k ∧ m < l.length by simpa using h1).1
  simp [Nat.ne_of_lt' hm]

private theorem take_succ_set (l : List ℕ) (k a : ℕ) (h : k < l.length) :
    (l.set k a).take (k + 1) = l.take k ++ [a] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using h), take_set_self]
  simp

@[simp] theorem sourceEmpty_capacity (initialCapacity : ℕ) (h : 0 < initialCapacity) :
    (sourceEmpty initialCapacity).Wf := by
  simp [SourceArray.Wf, SourceArray.capacity, sourceEmpty, h]

theorem sourceDouble_wf (s : SourceArray) (h : s.Wf) : (sourceDouble s).Wf := by
  change 0 < s.buffer.length ∧ s.length ≤ s.buffer.length at h
  rcases h with ⟨hpos, hlen⟩
  simp only [SourceArray.Wf, SourceArray.capacity, sourceDouble, List.length_append,
    List.length_replicate]
  omega

theorem sourceDouble_active (s : SourceArray) (h : s.Wf) :
    (sourceDouble s).active = s.active := by
  change 0 < s.buffer.length ∧ s.length ≤ s.buffer.length at h
  simp only [SourceArray.active, sourceDouble]
  exact List.take_append_of_le_length h.2

theorem sourcePushBasic_wf (s : SourceArray) (x : ℕ) (h : s.Wf)
    (hspace : s.length < s.capacity) :
    (sourcePushBasic s x).Wf := by
  change 0 < s.buffer.length ∧ s.length ≤ s.buffer.length at h
  change s.length < s.buffer.length at hspace
  rcases h with ⟨hpos, hlen⟩
  simp only [SourceArray.Wf, SourceArray.capacity, sourcePushBasic, List.length_set]
  omega

theorem sourcePushBasic_active (s : SourceArray) (x : ℕ)
    (hspace : s.length < s.capacity) :
    (sourcePushBasic s x).active = s.active ++ [x] := by
  simp only [SourceArray.active, sourcePushBasic]
  exact take_succ_set s.buffer s.length x hspace

theorem sourcePush_wf (s : SourceArray) (x : ℕ) (h : s.Wf) : (sourcePush s x).Wf := by
  have hwf : 0 < s.buffer.length ∧ s.length ≤ s.buffer.length := h
  by_cases hspace : s.length < s.buffer.length
  · simp only [sourcePush, SourceArray.capacity, if_pos hspace]
    exact sourcePushBasic_wf s x h hspace
  · simp only [sourcePush, SourceArray.capacity, if_neg hspace]
    have heq : s.length = s.buffer.length := by omega
    apply sourcePushBasic_wf (sourceDouble s) x (sourceDouble_wf s h)
    simp [sourceDouble, SourceArray.capacity, heq, hwf.1]

/-- Functional push agreement with abstract list snoc. -/
theorem sourcePush_active (s : SourceArray) (x : ℕ) (h : s.Wf) :
    (sourcePush s x).active = s.active ++ [x] := by
  have hwf : 0 < s.buffer.length ∧ s.length ≤ s.buffer.length := h
  by_cases hspace : s.length < s.buffer.length
  · simp only [sourcePush, SourceArray.capacity, if_pos hspace]
    exact sourcePushBasic_active s x hspace
  · simp only [sourcePush, SourceArray.capacity, if_neg hspace]
    have heq : s.length = s.buffer.length := by omega
    rw [sourcePushBasic_active (sourceDouble s) x]
    · exact congrArg (· ++ [x]) (sourceDouble_active s h)
    · simp [sourceDouble, SourceArray.capacity, heq, hwf.1]

/-- The source's potential inequality, componentwise over the cost vector. -/
theorem sourcePush_amortized_costN (s : SourceArray) (x : ℕ) (h : s.Wf) :
    PushCost.plus (sourceRawCostN s) (sourcePotentialN (sourcePush s x)) ≤
      PushCost.plus sourceAdvertisedCostN (sourcePotentialN s) := by
  change 0 < s.buffer.length ∧ s.length ≤ s.buffer.length at h
  rcases h with ⟨hpos, hlen⟩
  by_cases hspace : s.length < s.buffer.length
  · simp only [PushCost.le_def, PushCost.plus, sourceRawCostN, sourcePotentialN,
      sourceAdvertisedCostN, sourcePush, SourceArray.capacity, if_pos hspace]
    simp only [sourcePushBasic, List.length_set]
    omega
  · have heq : s.length = s.buffer.length := by omega
    simp only [PushCost.le_def, PushCost.plus, sourceRawCostN, sourcePotentialN,
      sourceAdvertisedCostN, SourceArray.capacity, sourcePush, if_neg hspace,
      sourcePushBasic, sourceDouble, List.length_set, List.length_append,
      List.length_replicate]
    omega

/-- IHT More's nested-potential public O(1) push bound. -/
theorem sourcePush_public_amortized_costN (s : SourceArray) (x : ℕ) (h : s.Wf) :
    PushCost.plus (sourceRawCostN s) (sourcePublicPotentialN (sourcePush s x)) ≤
      PushCost.plus sourcePublicAdvertisedCostN (sourcePublicPotentialN s) := by
  change 0 < s.buffer.length ∧ s.length ≤ s.buffer.length at h
  rcases h with ⟨hpos, hlen⟩
  by_cases hspace : s.length < s.buffer.length
  · simp only [PushCost.le_def, PushCost.plus, sourceRawCostN, sourcePotentialN,
      sourceOuterPotentialN, sourcePublicPotentialN, sourcePublicAdvertisedCostN,
      sourcePush, SourceArray.capacity, if_pos hspace, sourcePushBasic, List.length_set]
    omega
  · have heq : s.length = s.buffer.length := by omega
    simp only [PushCost.le_def, PushCost.plus, sourceRawCostN, sourcePotentialN,
      sourceOuterPotentialN, sourcePublicPotentialN, sourcePublicAdvertisedCostN,
      SourceArray.capacity, sourcePush, if_neg hspace, sourcePushBasic, sourceDouble,
      List.length_set, List.length_append, List.length_replicate]
    omega

/-- The same amortized O(1) bound in A1's vector-valued `ECost`. -/
theorem sourcePush_amortized_cost (s : SourceArray) (x : ℕ) (h : s.Wf) :
    sourceRawCost s + sourcePotential (sourcePush s x) ≤
      sourceAdvertisedCost + sourcePotential s := by
  unfold sourceRawCost sourcePotential sourceAdvertisedCost
  rw [← PushCost.toECost_plus, ← PushCost.toECost_plus]
  exact PushCost.toECost_mono (sourcePush_amortized_costN s x h)

/-- Raw deterministic source push. -/
noncomputable def sourcePushRaw (s : SourceArray) (x : ℕ) : NRest SourceArray ECost :=
  NRest.consume (NRest.returnT (sourcePush s x)) (sourceRawCost s)

/-- Constant-cost public push specification. -/
noncomputable def sourcePushSpec (s : SourceArray) (x : ℕ) : NRest SourceArray ECost :=
  NRest.consume (NRest.returnT (sourcePush s x)) sourceAdvertisedCost

/-- A1's reclaim/consume surface for the standard dynamic-array potential. -/
noncomputable def sourcePushAmortized (s : SourceArray) (x : ℕ) :
    NRest SourceArray ECost :=
  NRest.reclaim (NRest.consume (sourcePushSpec s x) (sourcePotential s)) sourcePotential

private theorem consume_returnT_eq_spec {α : Type} (x : α) (c : ECost) :
    NRest.consume (NRest.returnT x) c =
      NRest.spec (fun y => y = x) (fun _ => c) := by
  rw [NRest.consume_returnT, NRest.spec, NRest.rest_inj_iff]
  funext y
  by_cases hy : y = x
  · subst y
    simp
  · simp [hy]

/-- The raw source operation refines the public constant-cost operation after
A1 reclaims the post-potential.  This is the exported amortized O(1) push
statement; all costs remain vectors. -/
theorem sourcePushRaw_le_amortized (s : SourceArray) (x : ℕ) (h : s.Wf) :
    sourcePushRaw s x ≤ sourcePushAmortized s x := by
  unfold sourcePushRaw sourcePushAmortized sourcePushSpec
  rw [NRest.consume_consume, consume_returnT_eq_spec, consume_returnT_eq_spec]
  apply le_trans (b := NRest.spec (fun y => y = sourcePush s x)
      (fun y => (sourcePotential s + sourceAdvertisedCost) -ᵣ sourcePotential y))
  · rw [NRest.spec, NRest.spec, NRest.rest_le_rest_iff]
    intro y
    by_cases hy : y = sourcePush s x
    · subst y
      simp only [ite_true, WithBot.coe_le_coe]
      apply Needname.le_diff_if_add_le
      · have hc := sourcePush_amortized_cost s x h
        simpa [add_comm] using hc
      · apply Needname.add_leD2 (sourceRawCost s) (sourcePotential (sourcePush s x))
        simpa [add_comm] using sourcePush_amortized_cost s x h
    · simp [hy]
  · exact NRest.reclaim_spec_le

/-! ## 3. Bounded adapter over caller-owned storage -/

structure BoundedArray where
  buffer : List ℕ
  length : ℕ
  capacity : ℕ
  deriving DecidableEq, Repr

/-- Physical ownership is `buffer.length`; `capacity` is only the exposed prefix. -/
def BoundedArray.Wf (s : BoundedArray) : Prop :=
  0 < s.capacity ∧ s.length ≤ s.capacity ∧ s.capacity ≤ s.buffer.length

def BoundedArray.active (s : BoundedArray) : List ℕ := s.buffer.take s.length

def boundedCanPush (s : BoundedArray) : Bool :=
  decide (s.length < s.capacity ∨ 2 * s.capacity ≤ s.buffer.length)

def boundedPush (s : BoundedArray) (x : ℕ) : Option BoundedArray :=
  if s.length < s.capacity then
    some ⟨s.buffer.set s.length x, s.length + 1, s.capacity⟩
  else if 2 * s.capacity ≤ s.buffer.length then
    some ⟨s.buffer.set s.length x, s.length + 1, 2 * s.capacity⟩
  else none

/-- The adapter's executable cost twin.  Logical resize is constant-cost: no copy occurs. -/
def boundedPushCostN (s : BoundedArray) : Option PushCost :=
  if s.length < s.capacity then some ⟨1, 1, 1, 0⟩
  else if 2 * s.capacity ≤ s.buffer.length then some ⟨2, 1, 1, 0⟩
  else none

/-- A sequence runner used by the compiled differential gates. -/
def boundedPushMany : BoundedArray → List ℕ → Option (BoundedArray × PushCost)
  | s, [] => some (s, PushCost.zero)
  | s, x :: xs => do
      let s' ← boundedPush s x
      let c ← boundedPushCostN s
      let (t, d) ← boundedPushMany s' xs
      pure (t, PushCost.plus c d)

def boundedCostFromTransition (s t : BoundedArray) : PushCost :=
  if t.capacity = s.capacity then ⟨1, 1, 1, 0⟩ else ⟨2, 1, 1, 0⟩

-- No resize: functional result and exact vector cost.
#guard boundedPushMany ⟨[0, 0, 0, 0], 1, 4⟩ [7, 8] =
  some (⟨[0, 7, 8, 0], 3, 4⟩, ⟨2, 2, 2, 0⟩)

-- Resize boundary: logical capacity 2 becomes 4 inside an owned length-8 buffer.
#guard boundedPushMany ⟨List.replicate 8 0, 2, 2⟩ [5] =
  some (⟨(List.replicate 8 0).set 2 5, 3, 4⟩, ⟨2, 1, 1, 0⟩)

-- Full physical capacity: no mutation and no advertised successful cost.
#guard boundedPush ⟨[1, 2, 3, 4], 4, 4⟩ 9 = none
#guard boundedPushCostN ⟨[1, 2, 3, 4], 4, 4⟩ = none

-- Differential cost gate: the independently reconstructed branch cost agrees.
#guard (boundedPush ⟨List.replicate 8 0, 2, 2⟩ 5).map
    (boundedCostFromTransition ⟨List.replicate 8 0, 2, 2⟩) =
  boundedPushCostN ⟨List.replicate 8 0, 2, 2⟩

theorem boundedPush_some_wf (s t : BoundedArray) (x : ℕ) (h : s.Wf)
    (hp : boundedPush s x = some t) : t.Wf := by
  rcases h with ⟨hpos, hlen, hcap⟩
  simp only [boundedPush] at hp
  split at hp
  · rename_i hspace
    simp only [Option.some.injEq] at hp
    subst t
    simp only [BoundedArray.Wf, List.length_set]
    omega
  · rename_i hfull
    split at hp
    · rename_i hgrow
      simp only [Option.some.injEq] at hp
      subst t
      simp only [BoundedArray.Wf, List.length_set]
      omega
    · contradiction

theorem boundedPush_some_active (s t : BoundedArray) (x : ℕ) (h : s.Wf)
    (hp : boundedPush s x = some t) :
    t.active = s.active ++ [x] := by
  rcases h with ⟨hpos, hlen, hcap⟩
  simp only [boundedPush] at hp
  split at hp
  · rename_i hspace
    simp only [Option.some.injEq] at hp
    subst t
    exact take_succ_set s.buffer s.length x (by omega)
  · rename_i hfull
    split at hp
    · rename_i hgrow
      simp only [Option.some.injEq] at hp
      subst t
      exact take_succ_set s.buffer s.length x (by omega)
    · contradiction

/-- The executable branch-cost mirror agrees with the successful transition. -/
theorem boundedPush_cost_agrees (s t : BoundedArray) (x : ℕ) (h : s.Wf)
    (hp : boundedPush s x = some t) :
    boundedPushCostN s = some (boundedCostFromTransition s t) := by
  rcases h with ⟨hpos, hlen, hcap⟩
  simp only [boundedPush] at hp
  split at hp
  · rename_i hspace
    simp only [Option.some.injEq] at hp
    subst t
    simp [boundedPushCostN, boundedCostFromTransition, hspace]
  · rename_i hfull
    split at hp
    · rename_i hgrow
      simp only [Option.some.injEq] at hp
      subst t
      have hne : 2 * s.capacity ≠ s.capacity := by omega
      simp [boundedPushCostN, boundedCostFromTransition, hfull, hgrow, hne]
    · contradiction

/-- Failure is clean: the state is a pure input, and failure means no current
slot and no room to double the logical capacity in caller-owned storage. -/
theorem boundedPush_eq_none_iff (s : BoundedArray) (x : ℕ) (h : s.Wf) :
    boundedPush s x = none ↔
      s.length = s.capacity ∧ s.buffer.length < 2 * s.capacity := by
  rcases h with ⟨-, hlen, -⟩
  simp only [boundedPush]
  by_cases hspace : s.length < s.capacity
  · rw [if_pos hspace]
    constructor
    · intro hp
      contradiction
    · rintro ⟨heq, -⟩
      omega
  · have heq : s.length = s.capacity := by omega
    rw [if_neg hspace]
    by_cases hgrow : 2 * s.capacity ≤ s.buffer.length
    · rw [if_pos hgrow]
      constructor
      · intro hp
        contradiction
      · rintro ⟨-, hlt⟩
        omega
    · rw [if_neg hgrow]
      simp [heq]
      omega

/-- In particular, a physically full well-formed buffer rejects a push. -/
theorem boundedPush_full (s : BoundedArray) (x : ℕ) (h : s.Wf)
    (hfull : s.length = s.buffer.length) :
    boundedPush s x = none := by
  rw [boundedPush_eq_none_iff s x h]
  rcases h with ⟨hpos, hlen, hcap⟩
  constructor
  · omega
  · omega

/-! ## 4. Loop-free executable adapter -/

/-- Observable convention: `1` carries the pushed state; `0` carries the
unchanged input state. -/
def boundedPushObs (s : BoundedArray) (x : ℕ) : ℕ × BoundedArray :=
  match boundedPush s x with
  | some t => (1, t)
  | none => (0, s)

@[simp] theorem boundedPushObs_success (s t : BoundedArray) (x : ℕ)
    (hp : boundedPush s x = some t) :
    boundedPushObs s x = (1, t) := by simp [boundedPushObs, hp]

@[simp] theorem boundedPushObs_failure (s : BoundedArray) (x : ℕ)
    (hp : boundedPush s x = none) :
    boundedPushObs s x = (0, s) := by simp [boundedPushObs, hp]

private def irCostN (c : String) : Ir.Cost := ACost.cost c 1

private def packCostN : Ir.Cost := 4 • irCostN Currency.skip

private def successCostN : Ir.Cost :=
  irCostN Currency.aset + irCostN Currency.add + irCostN Currency.copy +
    irCostN Currency.const + packCostN

private def failCostN : Ir.Cost :=
  irCostN Currency.copy + irCostN Currency.copy + irCostN Currency.const + packCostN

/-- Exact synthesized-command cost, including every branch, scalar operation,
array write and tuple `skip`. -/
def boundedExecCostN (s : BoundedArray) : Ir.Cost :=
  if s.length < s.capacity then
    irCostN Currency.ite + successCostN
  else if s.buffer.length < 2 * s.capacity then
    irCostN Currency.ite + irCostN (binopCurrency .mul) +
      irCostN Currency.ite + failCostN
  else
    irCostN Currency.ite + irCostN (binopCurrency .mul) +
      irCostN Currency.ite + successCostN

noncomputable def boundedExecCost (s : BoundedArray) : ECost :=
  liftACost (boundedExecCostN s)

private noncomputable def packBoundedRaw (ok : ℕ) (buf : List ℕ)
    (len cap phys : ℕ) : NRest (ℕ × (List ℕ × (ℕ × (ℕ × ℕ)))) ECost :=
  NRest.bindT (mopPair cap phys) fun cp =>
    NRest.bindT (mopPair len cp) fun lcp =>
      NRest.bindT (mopPair buf lcp) fun st => mopPair ok st

private noncomputable def boundedSuccessRaw (s : BoundedArray) (x newCap : ℕ) :
    NRest (ℕ × (List ℕ × (ℕ × (ℕ × ℕ)))) ECost :=
  NRest.bindT (mopAset s.buffer s.length x) fun buf' =>
    NRest.bindT (mopBinop .add s.length 1) fun len' =>
      NRest.bindT (mopCopy newCap) fun cap' =>
        NRest.bindT (mopConstN 1) fun ok =>
          packBoundedRaw ok buf' len' cap' s.buffer.length

private noncomputable def boundedFailRaw (s : BoundedArray) :
    NRest (ℕ × (List ℕ × (ℕ × (ℕ × ℕ)))) ECost :=
  NRest.bindT (mopCopy s.length) fun len' =>
    NRest.bindT (mopCopy s.capacity) fun cap' =>
      NRest.bindT (mopConstN 0) fun ok =>
        packBoundedRaw ok s.buffer len' cap' s.buffer.length

/-- Raw branch tree.  The physical bound is an operand of both fit tests. -/
noncomputable def boundedExecRaw (s : BoundedArray) (x : ℕ) :
    NRest (ℕ × (List ℕ × (ℕ × (ℕ × ℕ)))) ECost :=
  irIf (decide (s.length < s.capacity))
    (boundedSuccessRaw s x s.capacity)
    (NRest.bindT (mopBinop .mul s.capacity 2) fun doubled =>
      irIf (decide (s.buffer.length < doubled))
        (boundedFailRaw s) (boundedSuccessRaw s x doubled))

sepref_synth boundedSuccessSynth
    (A len newCapCell phys value one outLen outCap ok : String)
    (s : BoundedArray) (x newCap : ℕ) :
  hnRefine (junkCell outLen ∗ junkCell outCap ∗ junkCell ok ∗
      hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn newCap newCapCell ∗ hnCtxt natAssn s.buffer.length phys ∗
      hnCtxt natAssn x value ∗ hnCtxt natAssn 1 one)
    _ _ (ok, (A, (outLen, (outCap, phys))))
    (natAssn ×ₐ (arrayAssn ×ₐ (natAssn ×ₐ (natAssn ×ₐ natAssn))))
    (boundedSuccessRaw s x newCap)

sepref_synth boundedFailSynth
    (A len cap phys outLen outCap ok : String) (s : BoundedArray) :
  hnRefine (junkCell outLen ∗ junkCell outCap ∗ junkCell ok ∗
      hnCtxt arrayAssn s.buffer A ∗ hnCtxt natAssn s.length len ∗
      hnCtxt natAssn s.capacity cap ∗ hnCtxt natAssn s.buffer.length phys)
    _ _ (ok, (A, (outLen, (outCap, phys))))
    (natAssn ×ₐ (arrayAssn ×ₐ (natAssn ×ₐ (natAssn ×ₐ natAssn))))
    (boundedFailRaw s)

attribute [sepref_fr_rules] boundedSuccessSynth boundedFailSynth

/-! ## 5. Explicit ownership assertion and bounded executable specification -/

/-- Three caller-owned cells: physical buffer, logical length, logical capacity. -/
def boundedArrayAssn : BoundedArray → String × String × String → Assn := fun s c =>
  ⌜s.Wf⌝ ∗ (arrayAssn s.buffer c.1 ∗ natAssn s.length c.2.1 ∗ natAssn s.capacity c.2.2)

theorem boundedArrayAssn_unfold (s : BoundedArray) (c : String × String × String) :
    hnCtxt boundedArrayAssn s c =
      ⌜s.Wf⌝ ∗ (hnCtxt arrayAssn s.buffer c.1 ∗ hnCtxt natAssn s.length c.2.1 ∗
        hnCtxt natAssn s.capacity c.2.2) := rfl

/-- Package three already-owned cells as a bounded array; this is the adapter's
no-allocation initialization boundary. -/
theorem boundedArrayAssn_intro (s : BoundedArray) (c : String × String × String)
    (h : s.Wf) :
    (arrayAssn s.buffer c.1 ∗ natAssn s.length c.2.1 ∗ natAssn s.capacity c.2.2) ⊢
      boundedArrayAssn s c :=
  fun _ hs => predLift_sepConj_iff.2 ⟨h, hs⟩

/-- Release returns exactly the caller's three cells; no deallocation is claimed. -/
theorem boundedArrayAssn_release (s : BoundedArray) (c : String × String × String) :
    hnCtxt boundedArrayAssn s c ⊢ junkArrayOfLen s.buffer.length c.1 ∗
      junkCell c.2.1 ∗ junkCell c.2.2 := by
  intro st hs
  obtain ⟨-, hs⟩ := predLift_sepConj_iff.1 hs
  exact conj_entails_mono (arrayAssn_entails_junkArrayOfLen s.buffer c.1)
    (conj_entails_mono (natAssn_entails_junkCell s.length c.2.1)
      (natAssn_entails_junkCell s.capacity c.2.2)) st hs

noncomputable def boundedPushSpec (s : BoundedArray) (x : ℕ) :
    NRest BoundedArray ECost :=
  match boundedPush s x, boundedPushCostN s with
  | some t, some c => NRest.consume (NRest.returnT t) c.toECost
  | _, _ => .fail

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.sourcePush_active' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sourcePush_active

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.sourcePush_amortized_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sourcePush_amortized_cost

/--
info: 'Lax13Proofs.Refine.Sepref.Iicf.sourcePush_public_amortized_costN' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sourcePush_public_amortized_costN

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.sourcePushRaw_le_amortized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sourcePushRaw_le_amortized

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.boundedPush_some_active' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms boundedPush_some_active

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.boundedPush_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms boundedPush_full

end Lax13Proofs.Refine.Sepref.Iicf
