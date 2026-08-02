import Lax13Proofs.Refine.Iicf.IicfDynamicArray
import Lax13Proofs.Refine.Iicf.IicfArray
import Lax13Proofs.Refine.Iicf.IicfStack
import Lax13Proofs.Refine.Iicf.Intf.List

/-!
# Array-backed lists on caller-owned bounded storage

Adaptation of Sepreftime's `IICF_Array_List.thy` at commit `c1c987b`.

The source owns a heap array and may allocate, copy, grow, and shrink it.

**P5.E re-seat, 2026-08-02 (ledger E16 discharged).**  Until P4.5 landed an
allocator, this repository had no way to obtain a *fresh* buffer, so append
was fallible and its registered refinement rule was stated over a
`arrayListReadyRel` — a relation with no source counterpart, carrying the
extra conjunct `boundedPush s 0 ≠ none`.  A caller holding only
`arrayListAssn` could therefore not conclude that append succeeds, which
`IICF_Array_List.thy:177` (`arl_append_hnr_aux`) states with no precondition
slot at all.  That relation is **gone**, and `arlAppendOp_refines` is now
registered over `arrayListRel` with exactly the hypothesis list of
`arlCopyOp_refines`: `fun _ => True`.

* The relation, list semantics, capacities, and all correctness/refinement
  facts are retained unchanged; this is statement strengthening plus
  substrate substitution, not a re-derivation.
* `arlAppendTotal` is the source's `arl_append` (`:30–42`): push in place when
  a slot exists, otherwise `array_grow a (2 * cap) default` — a fresh block of
  twice the capacity holding the copied active prefix and the allocator's
  zeros — and then write.  It is **total**: `arlAppendTotal_refines` has no
  side condition beyond the relation itself, and `arlAppendOp` never fails.
* `arlAppend`/`arlAppendExecSpec`/`arlAppend_exec_hnr` — the fallible,
  caller-owned, no-allocation forms — are **retained as landed capital**, per
  ledger E29: they are the loop-interior form, and `arlAppendTotal`'s
  in-place branch is literally `boundedPush`, so P4's representation theory is
  threaded rather than duplicated.
* `arlEmptyModel`, `arlEmptySizeModel`, and `arlCopyModel` are pure allocation
  boundary models.  `arlEmptyIn` and `arlEmptySizeIn` establish an empty list
  in caller-owned storage when it is large enough.
* Source shrinking is adapted to a logical-capacity reduction in the same
  owned buffer.  No allocation or copy is claimed.

**Cost (§ "Amortized cost").**  Growth copies the whole buffer, so the raw
price of append is *not* constant: `arlAppendCostN` charges one copy credit
per live element on the growth branch, plus the allocator's two `n`-independent
units (`HeapAlloc.allocCost`).  The public statement is the amortized one —
`arlAppendRaw_le_amortized`, over the standard doubling potential
`2 * length - capacity` — and it is O(1): four control, one write, one add,
two copy credits, independent of the length.  No constant price is invented
for the raw operation and no currency is used to make the copy disappear.

**Space (§ "Allocation accounting").**  A.3's `free` is LIFO only and growth
allocates *above* the live block, so the superseded buffer leaks
(`free_nontop_false` makes that a theorem, not an oversight).  The leak is
bounded, which is what ledger E29 requires of a geometric-growth structure:
`arlAllocatedMany_live_bounded` proves that the total heap ever allocated by
a run of appends — every leaked block included — is at most `4 ×` the number
of elements live at the end.

The pure registered rules are cost-silent because the P5.A list operations are
cost-silent.  A second layer gives exact costed IR rules for the seven
nonallocating list families; explicit bridge lemmas connect their values back
to those pure rules.  The allocator-backed growth program itself lives in
`ArrayListGrow.lean`, so that this file's `sepref_synth` environment is
unchanged by the re-seat.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## Representation and composed assertion -/

abbrev ArrayList := BoundedArray

def arrayListRel : Set (ArrayList × List ℕ) :=
  {p | p.1.Wf ∧ p.1.active = p.2}

@[simp] theorem mem_arrayListRel_iff {s : ArrayList} {xs : List ℕ} :
    (s, xs) ∈ arrayListRel ↔ s.Wf ∧ s.active = xs := Iff.rfl

/-- Precision analogue: one represented bounded state determines exactly one
logical list.  Heap-cell precision itself is inherited from
`boundedArrayAssn`. -/
theorem arrayListRel_singleValued : SingleValued arrayListRel := by
  intro s xs ys hx hy
  change s.Wf ∧ s.active = xs at hx
  change s.Wf ∧ s.active = ys at hy
  exact hx.2.symm.trans hy.2

def arrayListAssn : List ℕ → String × String × String → Assn :=
  hrComp boundedArrayAssn arrayListRel

@[intf_of_assn] theorem arrayListAssn_intf :
    intfOfAssn arrayListAssn (ListI ℕ) := trivial

theorem arrayListAssn_unfold (xs : List ℕ) (c : String × String × String) :
    arrayListAssn xs c =
      ∃ᵃ s, boundedArrayAssn s c ∗ ⌜s.Wf ∧ s.active = xs⌝ := rfl

theorem arrayListAssn_intro {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) (c : String × String × String) :
    boundedArrayAssn s c ⊢ arrayListAssn xs c :=
  hr_compI h

/-- Source `arl_assn A`: compose the raw representation with a pure element
relation lifted to lists. -/
def arrayListAssnRel {α : Type} (A : Set (ℕ × α)) :
    List α → String × String × String → Assn :=
  hrComp boundedArrayAssn (relComp arrayListRel (listRel A))

theorem arrayListAssn_comp {α : Type} (A : Set (ℕ × α)) :
    hrComp arrayListAssn (listRel A) = arrayListAssnRel A := by
  rw [arrayListAssn, arrayListAssnRel, hr_comp_assoc]

/-! ## Capacities and pure allocation-boundary models -/

def arlInitialCapacity : ℕ := 16
def arlMinimumCapacity : ℕ := 16

def arlEmptyState (cap : ℕ) : ArrayList :=
  ⟨List.replicate cap 0, 0, cap⟩

def arlEmptyModel : ArrayList := arlEmptyState arlInitialCapacity

def arlEmptySizeModel (requested : ℕ) : ArrayList :=
  arlEmptyState (max requested arlMinimumCapacity)

def arlEmptyIn (buffer : List ℕ) : Option ArrayList :=
  if arlInitialCapacity ≤ buffer.length then
    some ⟨buffer, 0, arlInitialCapacity⟩
  else none

def arlEmptySizeIn (requested : ℕ) (buffer : List ℕ) : Option ArrayList :=
  let cap := max requested arlMinimumCapacity
  if cap ≤ buffer.length then some ⟨buffer, 0, cap⟩ else none

@[simp] theorem arlEmptyModel_refines :
    (arlEmptyModel, []) ∈ arrayListRel := by
  simp [arrayListRel, arlEmptyModel, arlEmptyState, BoundedArray.Wf,
    BoundedArray.active, arlInitialCapacity]

@[simp] theorem arlEmptySizeModel_refines (requested : ℕ) :
    (arlEmptySizeModel requested, []) ∈ arrayListRel := by
  simp [arrayListRel, arlEmptySizeModel, arlEmptyState, BoundedArray.Wf,
    BoundedArray.active, arlMinimumCapacity]

theorem arlEmptyIn_some {buffer : List ℕ} {s : ArrayList}
    (h : arlEmptyIn buffer = some s) : (s, []) ∈ arrayListRel := by
  simp only [arlEmptyIn] at h
  split at h
  · rename_i hcap
    simp only [Option.some.injEq] at h
    subst s
    refine ⟨⟨by simp [arlInitialCapacity], by simp, ?_⟩, by simp [BoundedArray.active]⟩
    simpa [arlInitialCapacity] using hcap
  · contradiction

theorem arlEmptySizeIn_some {requested : ℕ} {buffer : List ℕ} {s : ArrayList}
    (h : arlEmptySizeIn requested buffer = some s) : (s, []) ∈ arrayListRel := by
  simp only [arlEmptySizeIn] at h
  split at h
  · rename_i hcap
    simp only [Option.some.injEq] at h
    subst s
    refine ⟨⟨by simp [arlMinimumCapacity], by simp, ?_⟩, by simp [BoundedArray.active]⟩
    simpa using hcap
  · contradiction

/-! ## Executable bounded state transformers -/

def arlAppend (s : ArrayList) (x : ℕ) : Option ArrayList := boundedPush s x

/-- Source `array_grow a (2 * cap) default` (`IICF_Array_List.thy:38`).  A
**fresh** block of twice the logical capacity, holding the copied active
prefix and the allocator's zeros.  `ArrayListGrow.lean` shows this is exactly
what `mopAlloc (2 * cap)` followed by an `s.length`-element copy produces. -/
def arlGrow (s : ArrayList) : ArrayList :=
  ⟨s.active ++ List.replicate (2 * s.capacity - s.length) 0, s.length, 2 * s.capacity⟩

/-- Grow, then write at the old length: the source's full branch. -/
def arlPushGrown (s : ArrayList) (x : ℕ) : ArrayList :=
  ⟨(arlGrow s).buffer.set s.length x, s.length + 1, 2 * s.capacity⟩

/-- **Append at source strength** (`arl_append`, source `:30–42`).  Total: the
in-place branch is P4's `boundedPush` verbatim, and the branch P4 had to
reject is now the allocating one.  There is no precondition slot, which is the
whole point of the P5.E re-seat. -/
def arlAppendTotal (s : ArrayList) (x : ℕ) : ArrayList :=
  (boundedPush s x).getD (arlPushGrown s x)

theorem arlAppendTotal_of_some {s t : ArrayList} {x : ℕ}
    (hp : boundedPush s x = some t) : arlAppendTotal s x = t := by
  simp [arlAppendTotal, hp]

theorem arlAppendTotal_of_none {s : ArrayList} {x : ℕ}
    (hp : boundedPush s x = none) : arlAppendTotal s x = arlPushGrown s x := by
  simp [arlAppendTotal, hp]

/-- Costed executable boundary, exactly P4's successful/failing bounded push
specification.  Retained: this is the loop-interior, no-allocation form
(ledger E29). -/
noncomputable def arlAppendExecSpec (s : ArrayList) (x : ℕ) :
    NRest ArrayList ECost := boundedPushSpec s x

theorem arlAppendExecSpec_success {s t : ArrayList} {x : ℕ} {c : PushCost}
    (hp : boundedPush s x = some t) (hc : boundedPushCostN s = some c) :
    arlAppendExecSpec s x = NRest.consume (NRest.returnT t) c.toECost := by
  simp [arlAppendExecSpec, boundedPushSpec, hp, hc]

theorem arlAppendExecSpec_failure {s : ArrayList} {x : ℕ}
    (hp : boundedPush s x = none) : arlAppendExecSpec s x = NRest.fail := by
  simp [arlAppendExecSpec, boundedPushSpec, hp]

/-- The existing P4 command-level rule, re-exported at the array-list
boundary.  Its result includes the success flag and metadata because failure
must remain observable. -/
theorem arlAppend_exec_hnr
    (s : ArrayList) (x : ℕ) (hwf : s.Wf)
    (A len cap phys value one two outLen outCap ok doubled : String) :
    hnRefine (boundedExecPre s x A len cap phys value one two outLen outCap ok doubled)
      (boundedExecCom A len cap phys value one two outLen outCap ok doubled)
      (boundedExecPost s x len cap value one two doubled)
      (ok, (A, (outLen, (outCap, phys)))) boundedRawAssn (boundedExecSpec s x) :=
  boundedExec_hnr s x hwf A len cap phys value one two outLen outCap ok doubled

/-- Pure copy boundary.  The value model is identity; an executable heap copy
is intentionally absent because it would need fresh independent ownership. -/
def arlCopyModel (s : ArrayList) : ArrayList := s

def arlLength (s : ArrayList) : ℕ := s.length

def arlIsEmpty (s : ArrayList) : Bool := decide (s.length = 0)

def arlLast? (s : ArrayList) : Option ℕ := listAt? s.active.reverse 0

def arlGet? (s : ArrayList) (i : ℕ) : Option ℕ := listAt? s.active i

/-- Replace the active prefix and retain the caller-owned inactive suffix. -/
def arlWithActive (s : ArrayList) (xs : List ℕ) : ArrayList :=
  ⟨xs ++ s.buffer.drop s.length, xs.length, s.capacity⟩

def arlSet? (s : ArrayList) (i x : ℕ) : Option ArrayList :=
  if i < s.length then some (arlWithActive s (listSet s.active i x)) else none

def arlShrinkCapacity (s : ArrayList) (newLength : ℕ) : ℕ :=
  if newLength * 4 < s.capacity ∧ arlMinimumCapacity ≤ newLength * 2 then
    newLength * 2
  else s.capacity

def arlButlast? (s : ArrayList) : Option ArrayList :=
  if s.length = 0 then none
  else
    let n := s.length - 1
    some ⟨s.buffer, n, arlShrinkCapacity s n⟩

def arlSwap? (s : ArrayList) (i j : ℕ) : Option ArrayList :=
  if i < s.length ∧ j < s.length then
    some (arlWithActive s (listSwap s.active i j))
  else none

/-! ## Representation correctness -/

@[simp] theorem boundedActive_length (s : ArrayList) (h : s.Wf) :
    s.active.length = s.length := by
  have hlen : s.length ≤ s.buffer.length := h.2.1.trans h.2.2
  simp [BoundedArray.active, Nat.min_eq_left hlen]

@[simp] theorem arrayListRel_length {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) : s.length = xs.length := by
  change s.Wf ∧ s.active = xs at h
  rw [← h.2]
  exact (boundedActive_length s h.1).symm

theorem arrayListRel_nonempty {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) : (s.length ≠ 0) = (xs ≠ []) := by
  rw [arrayListRel_length h]
  cases xs <;> simp

theorem arlAppend_some_refines {s t : ArrayList} {xs : List ℕ} {x : ℕ}
    (hs : (s, xs) ∈ arrayListRel) (hp : arlAppend s x = some t) :
    (t, xs ++ [x]) ∈ arrayListRel := by
  change s.Wf ∧ s.active = xs at hs
  exact ⟨boundedPush_some_wf s t x hs.1 hp,
    (boundedPush_some_active s t x hs.1 hp).trans (congrArg (· ++ [x]) hs.2)⟩

theorem arlAppend_failure_iff {s : ArrayList} {x : ℕ} (hs : s.Wf) :
    arlAppend s x = none ↔
      s.length = s.capacity ∧ s.buffer.length < 2 * s.capacity :=
  boundedPush_eq_none_iff s x hs

/-! ### The growth branch

`boundedPush` fails exactly when the caller-owned buffer cannot hold the
doubled capacity.  The re-seat replaces that failure by a fresh allocation,
and the two lemmas below are all the new representation theory it needs. -/

private theorem take_set_self (l : List ℕ) (k a : ℕ) :
    (l.set k a).take k = l.take k := by
  refine List.ext_getElem (by simp) fun m h1 h2 => ?_
  have hm : m < k := (show m < k ∧ m < l.length by simpa using h1).1
  simp [Nat.ne_of_lt' hm]

private theorem take_succ_set (l : List ℕ) (k a : ℕ) (h : k < l.length) :
    (l.set k a).take (k + 1) = l.take k ++ [a] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using h), take_set_self]
  simp

/-- The fresh block is exactly twice the logical capacity — the source's
`array_grow a (2 * cap)`. -/
theorem arlGrow_buffer_length {s : ArrayList} (h : s.Wf) :
    (arlGrow s).buffer.length = 2 * s.capacity := by
  have hact := boundedActive_length s h
  rcases h with ⟨hpos, hlen, hcap⟩
  simp only [arlGrow, List.length_append, List.length_replicate, hact]
  omega

/-- Growth preserves the represented list: the copy is faithful. -/
theorem arlGrow_active {s : ArrayList} (h : s.Wf) : (arlGrow s).active = s.active := by
  have hact := boundedActive_length s h
  change (s.active ++ List.replicate (2 * s.capacity - s.length) 0).take s.length = s.active
  rw [List.take_append_of_le_length (by omega), ← hact]
  simp

theorem arlPushGrown_wf {s : ArrayList} {x : ℕ} (h : s.Wf) : (arlPushGrown s x).Wf := by
  have hbuf := arlGrow_buffer_length h
  have hblen : ((arlGrow s).buffer.set s.length x).length = 2 * s.capacity := by
    rw [List.length_set, hbuf]
  rcases h with ⟨hpos, hlen, hcap⟩
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 2 * s.capacity
    omega
  · show s.length + 1 ≤ 2 * s.capacity
    omega
  · show 2 * s.capacity ≤ ((arlGrow s).buffer.set s.length x).length
    omega

theorem arlPushGrown_active {s : ArrayList} {x : ℕ} (h : s.Wf) :
    (arlPushGrown s x).active = s.active ++ [x] := by
  have hbuf := arlGrow_buffer_length h
  have hgrow := arlGrow_active h
  have hpos := h.1
  have hlen := h.2.1
  have hlt : s.length < (arlGrow s).buffer.length := by omega
  change ((arlGrow s).buffer.set s.length x).take (s.length + 1) = s.active ++ [x]
  rw [take_succ_set _ _ _ hlt]
  exact congrArg (· ++ [x]) hgrow

/-- **The unconditional refinement.** Its complete hypothesis list is
`(s, xs) ∈ arrayListRel`: nothing about capacity, nothing about the physical
buffer, and no `boundedPush` side condition. -/
theorem arlAppendTotal_refines {s : ArrayList} {xs : List ℕ} {x : ℕ}
    (hs : (s, xs) ∈ arrayListRel) : (arlAppendTotal s x, xs ++ [x]) ∈ arrayListRel := by
  have hs' : s.Wf ∧ s.active = xs := hs
  cases hp : boundedPush s x with
  | some t =>
      rw [arlAppendTotal_of_some hp]
      exact arlAppend_some_refines hs hp
  | none =>
      rw [arlAppendTotal_of_none hp]
      exact ⟨arlPushGrown_wf hs'.1,
        (arlPushGrown_active hs'.1).trans (congrArg (· ++ [x]) hs'.2)⟩

@[simp] theorem arlAppendTotal_length (s : ArrayList) (x : ℕ) :
    (arlAppendTotal s x).length = s.length + 1 := by
  simp only [arlAppendTotal, boundedPush]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem arlAppendTotal_capacity (s : ArrayList) (x : ℕ) :
    (arlAppendTotal s x).capacity =
      if s.length < s.capacity then s.capacity else 2 * s.capacity := by
  simp only [arlAppendTotal, boundedPush]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem arlAppendTotal_capacity_ge (s : ArrayList) (x : ℕ) :
    s.capacity ≤ (arlAppendTotal s x).capacity := by
  rw [arlAppendTotal_capacity]
  split <;> omega

@[simp] theorem arlCopyModel_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) : (arlCopyModel s, xs) ∈ arrayListRel := h

@[simp] theorem arlLength_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) : arlLength s = xs.length :=
  arrayListRel_length h

@[simp] theorem arlIsEmpty_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) : arlIsEmpty s = propBool (xs = []) := by
  apply Bool.eq_iff_iff.mpr
  simp [arlIsEmpty, propBool, arrayListRel_length h]

@[simp] theorem arlLast?_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) : arlLast? s = listAt? xs.reverse 0 := by
  change s.Wf ∧ s.active = xs at h
  simp [arlLast?, h.2]

@[simp] theorem arlGet?_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) (i : ℕ) :
    arlGet? s i = listAt? xs i := by
  change s.Wf ∧ s.active = xs at h
  simp [arlGet?, h.2]

@[simp] theorem arlWithActive_active {s : ArrayList} {xs : List ℕ}
    (hlen : xs.length = s.length) :
    (arlWithActive s xs).active = xs := by
  have htake : (xs ++ s.buffer.drop s.length).take xs.length = xs :=
    by simpa using (List.take_append_of_le_length (l₂ := s.buffer.drop s.length)
      (le_refl xs.length))
  simpa [arlWithActive, BoundedArray.active, hlen] using htake

theorem arlWithActive_wf {s : ArrayList} {xs : List ℕ}
    (hs : s.Wf) (hlen : xs.length = s.length) : (arlWithActive s xs).Wf := by
  rcases hs with ⟨hpos, hlenCap, hcap⟩
  have hdrop : (s.buffer.drop s.length).length = s.buffer.length - s.length := by simp
  simp only [arlWithActive, BoundedArray.Wf, List.length_append, hdrop]
  constructor
  · exact hpos
  constructor
  · simpa [hlen] using hlenCap
  · rw [hlen]
    omega

theorem arlSet?_some_refines {s t : ArrayList} {xs : List ℕ} {i x : ℕ}
    (hs : (s, xs) ∈ arrayListRel) (hp : arlSet? s i x = some t) :
    (t, listSet xs i x) ∈ arrayListRel := by
  change s.Wf ∧ s.active = xs at hs
  simp only [arlSet?] at hp
  split at hp
  · rename_i hi
    simp only [Option.some.injEq] at hp
    subst t
    have hsetLen : (listSet s.active i x).length = s.length := by
      rw [listSet_length]
      exact boundedActive_length s hs.1
    exact ⟨arlWithActive_wf hs.1 hsetLen,
      (arlWithActive_active hsetLen).trans (congrArg (fun l => listSet l i x) hs.2)⟩
  · contradiction

private theorem take_pred_eq_butlast (buffer : List ℕ) {n : ℕ}
    (hn : n ≤ buffer.length) :
    buffer.take (n - 1) = listButlast (buffer.take n) := by
  have ht : (buffer.take n).length = n := by simp [Nat.min_eq_left hn]
  have hdrop : (buffer.take n).dropLast = buffer.take (n - 1) := by
    rw [List.dropLast_eq_take, ht, List.take_take,
      Nat.min_eq_left (Nat.sub_le n 1)]
  simpa [listButlast, List.dropLast] using hdrop.symm

theorem arlButlast?_some_refines {s t : ArrayList} {xs : List ℕ}
    (hs : (s, xs) ∈ arrayListRel) (hp : arlButlast? s = some t) :
    (t, listButlast xs) ∈ arrayListRel := by
  change s.Wf ∧ s.active = xs at hs
  rcases hs.1 with ⟨hpos, hlenCap, hcap⟩
  simp only [arlButlast?] at hp
  split at hp
  · contradiction
  · rename_i hne
    simp only [Option.some.injEq] at hp
    subst t
    have hnewLe : s.length - 1 ≤ arlShrinkCapacity s (s.length - 1) := by
      simp only [arlShrinkCapacity]
      split
      · omega
      · omega
    have hnewCap : arlShrinkCapacity s (s.length - 1) ≤ s.buffer.length := by
      simp only [arlShrinkCapacity]
      split
      · rename_i hshrink
        have hmin := hshrink.2
        simp [arlMinimumCapacity] at hmin
        omega
      · exact hcap
    have hnewPos : 0 < arlShrinkCapacity s (s.length - 1) := by
      simp only [arlShrinkCapacity]
      split
      · rename_i hshrink
        have hmin := hshrink.2
        simp [arlMinimumCapacity] at hmin
        omega
      · exact hpos
    refine ⟨⟨hnewPos, hnewLe, hnewCap⟩, ?_⟩
    change s.buffer.take (s.length - 1) = listButlast xs
    rw [← hs.2]
    exact take_pred_eq_butlast s.buffer (hlenCap.trans hcap)

theorem arlSwap?_some_refines {s t : ArrayList} {xs : List ℕ} {i j : ℕ}
    (hs : (s, xs) ∈ arrayListRel) (hp : arlSwap? s i j = some t) :
    (t, listSwap xs i j) ∈ arrayListRel := by
  change s.Wf ∧ s.active = xs at hs
  simp only [arlSwap?] at hp
  split at hp
  · simp only [Option.some.injEq] at hp
    subst t
    have hswapLen : (listSwap s.active i j).length = s.active.length := by
      unfold listSwap
      split <;> simp [listSet_length]
    have hlen : (listSwap s.active i j).length = s.length := by
      rw [hswapLen]
      exact boundedActive_length s hs.1
    exact ⟨arlWithActive_wf hs.1 hlen,
      (arlWithActive_active hlen).trans (congrArg (fun l => listSwap l i j) hs.2)⟩
  · contradiction

/-! ## Pure list-operation refinement rules -/

noncomputable def arlEmptyOp : NRest ArrayList ECost := NRest.returnT arlEmptyModel
noncomputable def arlEmptySizeOp (n : ℕ) : NRest ArrayList ECost :=
  NRest.returnT (arlEmptySizeModel n)
noncomputable def arlCopyOp (s : ArrayList) : NRest ArrayList ECost :=
  NRest.returnT (arlCopyModel s)
/-- Total: no `NRest.fail` branch, because there is no failing branch. -/
noncomputable def arlAppendOp (s : ArrayList) (x : ℕ) : NRest ArrayList ECost :=
  NRest.returnT (arlAppendTotal s x)
noncomputable def arlLengthOp (s : ArrayList) : NRest ℕ ECost := NRest.returnT (arlLength s)
noncomputable def arlIsEmptyOp (s : ArrayList) : NRest Bool ECost :=
  NRest.returnT (arlIsEmpty s)
noncomputable def arlLastOp (s : ArrayList) : NRest ℕ ECost :=
  NRest.spec (fun x => arlLast? s = some x) (fun _ => 0)
noncomputable def arlButlastOp (s : ArrayList) : NRest ArrayList ECost :=
  match arlButlast? s with
  | some t => NRest.returnT t
  | none => NRest.fail
noncomputable def arlGetOp (p : ArrayList × ℕ) : NRest ℕ ECost :=
  NRest.spec (fun x => arlGet? p.1 p.2 = some x) (fun _ => 0)
noncomputable def arlSetOp (p : (ArrayList × ℕ) × ℕ) : NRest ArrayList ECost :=
  match arlSet? p.1.1 p.1.2 p.2 with
  | some t => NRest.returnT t
  | none => NRest.fail
noncomputable def arlSwapOp (p : (ArrayList × ℕ) × ℕ) : NRest ArrayList ECost :=
  match arlSwap? p.1.1 p.1.2 p.2 with
  | some t => NRest.returnT t
  | none => NRest.fail

theorem arlEmptyOp_refines :
    (arlEmptyOp, op_list_empty ℕ) ∈ NRest.nrestRel arrayListRel := by
  exact NRest.param_returnT arlEmptyModel_refines

theorem arlEmptySizeOp_refines (n : ℕ) :
    (arlEmptySizeOp n, op_list_empty ℕ) ∈ NRest.nrestRel arrayListRel := by
  exact NRest.param_returnT (arlEmptySizeModel_refines n)

@[sepref_fref_thms] theorem arlCopyOp_refines :
    (arlCopyOp, op_list_copy ℕ) ∈
      fref (fun _ : List ℕ => True) arrayListRel
        (fun _ => NRest.nrestRel arrayListRel) := by
  intro s xs _ hs
  exact NRest.param_returnT (arlCopyModel_refines hs)

/-- **The re-seated public guarantee** (source `arl_append_hnr_aux`,
`IICF_Array_List.thy:177`).  The source rule has no precondition slot; neither
has this one.  Compare the pre-P5.E statement, which took
`arrayListReadyRel` — `arrayListRel` plus `boundedPush s 0 ≠ none` — as its
argument relation.  A caller holding `arrayListAssn xs c` alone can now
conclude that append succeeds. -/
@[sepref_fref_thms] theorem arlAppendOp_refines :
    (arlAppendOp, op_list_append ℕ) ∈
      fref (fun _ : List ℕ => True) arrayListRel
        (fun _ => Set.diagonal ℕ →ᵣ NRest.nrestRel arrayListRel) := by
  intro s xs _ hs x y hxy
  change x = y at hxy
  subst y
  simp [arlAppendOp, op_list_append]
  exact NRest.param_returnT (arlAppendTotal_refines hs)

@[sepref_fref_thms] theorem arlLengthOp_refines :
    (arlLengthOp, op_list_length ℕ) ∈
      fref (fun _ : List ℕ => True) arrayListRel
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro s xs _ hs
  exact NRest.param_returnT (arlLength_refines hs)

@[sepref_fref_thms] theorem arlIsEmptyOp_refines :
    (arlIsEmptyOp, op_list_is_empty ℕ) ∈
      fref (fun _ : List ℕ => True) arrayListRel
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) := by
  intro s xs _ hs
  exact NRest.param_returnT (arlIsEmpty_refines hs)

@[sepref_fref_thms] theorem arlLastOp_refines :
    (arlLastOp, op_list_last ℕ) ∈
      fref (fun xs : List ℕ => xs ≠ []) arrayListRel
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro s xs hxs hs
  have hsne : s.length ≠ 0 := (arrayListRel_nonempty hs).mpr hxs
  simp only [op_list_last, NRest.assert_pos hxs, NRest.returnT_bindT]
  rw [arlLastOp, arlLast?_refines hs]
  apply NRest.nrestRel_of_le
  rw [NRest.concFun_diagonal]

@[sepref_fref_thms] theorem arlButlastOp_refines :
    (arlButlastOp, op_list_butlast ℕ) ∈
      fref (fun xs : List ℕ => xs ≠ []) arrayListRel
        (fun _ => NRest.nrestRel arrayListRel) := by
  intro s xs hxs hs
  have hsne : s.length ≠ 0 := (arrayListRel_nonempty hs).mpr hxs
  obtain ⟨t, ht⟩ : ∃ t, arlButlast? s = some t := by
    simp [arlButlast?, hsne]
  simp [arlButlastOp, ht, op_list_butlast, hxs]
  exact NRest.param_returnT (arlButlast?_some_refines hs ht)

@[sepref_fref_thms] theorem arlGetOp_refines :
    (arlGetOp, op_list_get ℕ) ∈
      fref (fun p : List ℕ × ℕ => p.2 < p.1.length)
        (arrayListRel ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  rintro ⟨s, i⟩ ⟨xs, j⟩ hj hpq
  obtain ⟨hs, hij⟩ := hpq
  change i = j at hij
  subst j
  have hi : i < xs.length := hj
  simp only [op_list_get, NRest.assert_pos hi, NRest.returnT_bindT]
  rw [arlGetOp, arlGet?_refines hs]
  apply NRest.nrestRel_of_le
  rw [NRest.concFun_diagonal]

@[sepref_fref_thms] theorem arlSetOp_refines :
    (arlSetOp, op_list_set ℕ) ∈
      fref (fun p : (List ℕ × ℕ) × ℕ => p.1.2 < p.1.1.length)
        ((arrayListRel ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel arrayListRel) := by
  rintro ⟨⟨s, i⟩, x⟩ ⟨⟨xs, j⟩, y⟩ hq hpq
  obtain ⟨⟨hs, hij⟩, hxy⟩ := hpq
  change i = j at hij
  change x = y at hxy
  subst j
  subst y
  have hi : i < s.length := by simpa [← arrayListRel_length hs] using hq
  have ht : ∃ t, arlSet? s i x = some t := by simp [arlSet?, hi]
  obtain ⟨t, ht⟩ := ht
  simp [arlSetOp, ht, op_list_set, hq]
  exact NRest.param_returnT (arlSet?_some_refines hs ht)

@[sepref_fref_thms] theorem arlSwapOp_refines :
    (arlSwapOp, op_list_swap ℕ) ∈
      fref (fun p : (List ℕ × ℕ) × ℕ =>
        p.1.2 < p.1.1.length ∧ p.2 < p.1.1.length)
        ((arrayListRel ×ᵣ Set.diagonal ℕ) ×ᵣ Set.diagonal ℕ)
        (fun _ => NRest.nrestRel arrayListRel) := by
  rintro ⟨⟨s, i⟩, j⟩ ⟨⟨xs, i'⟩, j'⟩ hq hpq
  obtain ⟨⟨hs, hii⟩, hjj⟩ := hpq
  change i = i' at hii
  change j = j' at hjj
  subst i'
  subst j'
  have hb : i < s.length ∧ j < s.length := by
    simpa [← arrayListRel_length hs] using hq
  obtain ⟨t, ht⟩ : ∃ t, arlSwap? s i j = some t := by simp [arlSwap?, hb]
  simp [arlSwapOp, ht, op_list_swap, hq]
  exact NRest.param_returnT (arlSwap?_some_refines hs ht)

/-- The swap rule is the concrete representation wrapper around P5.A's
generic get/get/set/set expansion, rather than a second swap algorithm. -/
theorem arlSwap_via_generic (s : ArrayList) (i j : ℕ)
    (hi : i < s.active.length) (hj : j < s.active.length) :
    op_list_swap ℕ ((s.active, i), j) =
      NRest.bindT (op_list_get ℕ (s.active, i)) fun xi =>
      NRest.bindT (op_list_get ℕ (s.active, j)) fun xj =>
      NRest.bindT (op_list_set ℕ ((s.active, i), xj)) fun xs' =>
      NRest.bindT (op_list_set ℕ ((xs', j), xi)) fun xs'' =>
      NRest.returnT xs'' :=
  gen_op_list_swap s.active i j hi hj

/-! ## Amortized cost of the unconditional append

The growth branch copies the whole buffer, so the *raw* price of
`arlAppendTotal` is linear in the live length.  It is not hidden and it is not
priced by fiat: `arlAppendCostN` is P4's `boundedPushCostN` on the two
in-place branches, and on the growth branch it charges one copy credit per
live element plus the allocator's two units (`HeapAlloc.allocCost` is
`copy + add`, `n`-independent — `allocCost_const`).

The public statement is the amortized one, over the standard doubling
potential `2 * length - capacity` that P4 already proved for the source-shaped
`SourceArray`.  It is the same potential and the same argument, re-run on the
carrier the re-seat actually uses. -/

/-- Exact branch cost.  Branches one and two are `boundedPushCostN` verbatim;
branch three is the allocating one: two control units for `mopAlloc`, on top
of the in-place doubling branch's two, and `s.length` copies. -/
def arlAppendCostN (s : ArrayList) : PushCost :=
  match boundedPushCostN s with
  | some c => c
  | none => ⟨4, 1, 1, s.length⟩

theorem arlAppendCostN_of_some {s : ArrayList} {c : PushCost}
    (h : boundedPushCostN s = some c) : arlAppendCostN s = c := by
  simp [arlAppendCostN, h]

theorem arlAppendCostN_of_none {s : ArrayList} (h : boundedPushCostN s = none) :
    arlAppendCostN s = ⟨4, 1, 1, s.length⟩ := by
  simp [arlAppendCostN, h]

/-- The standard doubling potential, in the copy currency. -/
def arlPotentialN (s : ArrayList) : PushCost := ⟨0, 0, 0, 2 * s.length - s.capacity⟩

/-- The advertised price: length-independent and capacity-independent. -/
def arlAdvertisedCostN : PushCost := ⟨4, 1, 1, 2⟩

/-- **Amortized O(1) append**, componentwise over the cost vector. -/
theorem arlAppend_amortized_costN (s : ArrayList) (x : ℕ) (h : s.Wf) :
    PushCost.plus (arlAppendCostN s) (arlPotentialN (arlAppendTotal s x)) ≤
      PushCost.plus arlAdvertisedCostN (arlPotentialN s) := by
  rcases h with ⟨hpos, hlen, hcap⟩
  have hcapEq := arlAppendTotal_capacity s x
  by_cases hspace : s.length < s.capacity
  · rw [arlAppendCostN_of_some (c := ⟨1, 1, 1, 0⟩) (by simp [boundedPushCostN, hspace])]
    simp only [PushCost.le_def, PushCost.plus, arlPotentialN, arlAdvertisedCostN,
      arlAppendTotal_length, hcapEq, if_pos hspace]
    omega
  · by_cases hroom : 2 * s.capacity ≤ s.buffer.length
    · rw [arlAppendCostN_of_some (c := ⟨2, 1, 1, 0⟩)
        (by simp [boundedPushCostN, hspace, hroom])]
      simp only [PushCost.le_def, PushCost.plus, arlPotentialN, arlAdvertisedCostN,
        arlAppendTotal_length, hcapEq, if_neg hspace]
      omega
    · rw [arlAppendCostN_of_none (by simp [boundedPushCostN, hspace, hroom])]
      simp only [PushCost.le_def, PushCost.plus, arlPotentialN, arlAdvertisedCostN,
        arlAppendTotal_length, hcapEq, if_neg hspace]
      omega

noncomputable def arlPotential (s : ArrayList) : ECost := (arlPotentialN s).toECost
noncomputable def arlAppendRawCost (s : ArrayList) : ECost := (arlAppendCostN s).toECost
noncomputable def arlAdvertisedCost : ECost := arlAdvertisedCostN.toECost

/-- The same bound in the tower's vector-valued `ECost`; costs stay vectors. -/
theorem arlAppend_amortized_cost (s : ArrayList) (x : ℕ) (h : s.Wf) :
    arlAppendRawCost s + arlPotential (arlAppendTotal s x) ≤
      arlAdvertisedCost + arlPotential s := by
  unfold arlAppendRawCost arlPotential arlAdvertisedCost
  rw [← PushCost.toECost_plus, ← PushCost.toECost_plus]
  exact PushCost.toECost_mono (arlAppend_amortized_costN s x h)

/-- Raw deterministic append: the state transition, at the price it really
costs on the branch it really takes. -/
noncomputable def arlAppendRaw (s : ArrayList) (x : ℕ) : NRest ArrayList ECost :=
  NRest.consume (NRest.returnT (arlAppendTotal s x)) (arlAppendRawCost s)

/-- Constant-price public append specification. -/
noncomputable def arlAppendPublicSpec (s : ArrayList) (x : ℕ) : NRest ArrayList ECost :=
  NRest.consume (NRest.returnT (arlAppendTotal s x)) arlAdvertisedCost

noncomputable def arlAppendAmortized (s : ArrayList) (x : ℕ) : NRest ArrayList ECost :=
  NRest.reclaim (NRest.consume (arlAppendPublicSpec s x) (arlPotential s)) arlPotential

private theorem consume_returnT_eq_spec' {α : Type} (y : α) (c : ECost) :
    NRest.consume (NRest.returnT y) c =
      NRest.spec (fun z => z = y) (fun _ => c) := by
  rw [NRest.consume_returnT, NRest.spec, NRest.rest_inj_iff]
  funext z
  by_cases hz : z = y
  · subst z
    simp
  · simp [hz]

/-- **The exported amortized statement.**  The raw operation refines the
constant-price one after the post-potential is reclaimed.  This is the honest
headline: worst-case `O(length)` on a growth step, `O(1)` amortized, and every
cost a vector. -/
theorem arlAppendRaw_le_amortized (s : ArrayList) (x : ℕ) (h : s.Wf) :
    arlAppendRaw s x ≤ arlAppendAmortized s x := by
  unfold arlAppendRaw arlAppendAmortized arlAppendPublicSpec
  rw [NRest.consume_consume, consume_returnT_eq_spec', consume_returnT_eq_spec']
  apply le_trans (b := NRest.spec (fun y => y = arlAppendTotal s x)
      (fun y => (arlPotential s + arlAdvertisedCost) -ᵣ arlPotential y))
  · rw [NRest.spec, NRest.spec, NRest.rest_le_rest_iff]
    intro y
    by_cases hy : y = arlAppendTotal s x
    · subst y
      simp only [ite_true, WithBot.coe_le_coe]
      apply Needname.le_diff_if_add_le
      · have hc := arlAppend_amortized_cost s x h
        simpa [add_comm] using hc
      · apply Needname.add_leD2 (arlAppendRawCost s) (arlPotential (arlAppendTotal s x))
        simpa [add_comm] using arlAppend_amortized_cost s x h
    · simp [hy]
  · exact NRest.reclaim_spec_le

/-! ## Allocation accounting: the LIFO leak, and its bound

A.3's `free` is LIFO only (`free_nontop_false`): it releases the topmost
block, and it is a compiled theorem that a non-top free is underivable.
Growth allocates the doubled block *above* the live one, so the superseded
buffer is not on top and **cannot be freed**.  That is a real leak, and this
section states it and bounds it rather than pretending otherwise.

Ledger E29 rules that geometric-growth leaks are tolerable exactly when they
are live-set-bounded.  They are: capacities at least double between
allocations, so the whole geometric series is bounded by twice the final
capacity, and the final capacity is bounded by twice the live length. -/

/-- Fresh heap claimed by one append: the doubled block, or nothing. -/
def arlAllocatedBy (s : ArrayList) (x : ℕ) : ℕ :=
  if boundedPush s x = none then 2 * s.capacity else 0

def arlAppendMany : ArrayList → List ℕ → ArrayList
  | s, [] => s
  | s, x :: ys => arlAppendMany (arlAppendTotal s x) ys

/-- Total heap ever claimed by a run of appends, leaked blocks included. -/
def arlAllocatedMany : ArrayList → List ℕ → ℕ
  | _, [] => 0
  | s, x :: ys => arlAllocatedBy s x + arlAllocatedMany (arlAppendTotal s x) ys

theorem arlAllocatedBy_ne_zero {s : ArrayList} {x : ℕ} (h : arlAllocatedBy s x ≠ 0) :
    arlAllocatedBy s x = 2 * s.capacity ∧
      (arlAppendTotal s x).capacity = 2 * s.capacity := by
  simp only [arlAllocatedBy] at h ⊢
  split at h
  · rename_i hnone
    have hfull : ¬ s.length < s.capacity := by
      intro hlt
      rw [boundedPush, if_pos hlt] at hnone
      simp at hnone
    exact ⟨by rw [if_pos hnone], by rw [arlAppendTotal_capacity, if_neg hfull]⟩
  · exact absurd rfl h

/-- **The geometric bound.**  Every block ever handed out, plus the block the
run started with, fits in twice the final capacity. -/
theorem arlAllocatedMany_le (s : ArrayList) (ys : List ℕ) :
    arlAllocatedMany s ys + 2 * s.capacity ≤ 2 * (arlAppendMany s ys).capacity := by
  induction ys generalizing s with
  | nil => simp [arlAllocatedMany, arlAppendMany]
  | cons x ys ih =>
      have hstep := ih (s := arlAppendTotal s x)
      simp only [arlAllocatedMany, arlAppendMany]
      by_cases hz : arlAllocatedBy s x = 0
      · have hge := arlAppendTotal_capacity_ge s x
        omega
      · obtain ⟨hval, hcap⟩ := arlAllocatedBy_ne_zero hz
        omega

/-- Capacity never runs ahead of the live length by more than the block the
run started with: the invariant behind "the final capacity is `O(live)`". -/
theorem arlAppendMany_capacity_bound (c₀ : ℕ) (s : ArrayList) (ys : List ℕ)
    (h : s.capacity ≤ c₀ + 2 * s.length) :
    (arlAppendMany s ys).capacity ≤ c₀ + 2 * (arlAppendMany s ys).length := by
  induction ys generalizing s with
  | nil => simpa [arlAppendMany] using h
  | cons x ys ih =>
      refine ih (s := arlAppendTotal s x) ?_
      rw [arlAppendTotal_capacity, arlAppendTotal_length]
      split <;> omega

/-- **The E29 statement.**  Total heap ever allocated by a run of appends —
every LIFO-unfreeable superseded buffer included — is at most `4 ×` the number
of elements live at the end.  The leak is live-set-bounded, so the space
budget survives geometric growth. -/
theorem arlAllocatedMany_live_bounded (s : ArrayList) (ys : List ℕ) :
    arlAllocatedMany s ys ≤ 4 * (arlAppendMany s ys).length := by
  have hgeo := arlAllocatedMany_le s ys
  have hinv := arlAppendMany_capacity_bound s.capacity s ys (by omega)
  omega

/-! ## Exact executable layer

The list interface above is intentionally cost-silent.  A positive-cost IR
program cannot refine such an operation at the same `NRest` type, so the
executable rules below use exact budgeted twins.  The `*_exec_refines`
lemmas then connect those twins back to the list relation.  This keeps both
claims honest: the IR theorem states precisely what the command spends, and
the pure theorem states precisely which list operation its value implements.

Reads preserve all three representation cells.  `set` and `swap` destroy the
old array assertion and return one for the updated array.  `butlast` is the
no-allocation adaptation: it decrements the logical length and applies the
source's conditional *logical* capacity shrink, while retaining the physical
buffer.  Allocation-backed empty, empty-size, and copy deliberately have no
rules in this section.
-/

noncomputable def arlLengthRaw (n : ℕ) : NRest ℕ ECost := mopCopy n

noncomputable def arlIsEmptyRaw (n : ℕ) : NRest ℕ ECost :=
  irIf (decide (n = 0)) (mopConstN 1) (mopConstN 0)

noncomputable def arlLastRaw (buffer : List ℕ) (n : ℕ) : NRest ℕ ECost :=
  NRest.bindT (mopBinop .sub n 1) fun i => mopAget buffer i

noncomputable def arlGetRaw (buffer : List ℕ) (i : ℕ) : NRest ℕ ECost :=
  mopAget buffer i

noncomputable def arlSetRaw (buffer : List ℕ) (n cap i x : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopAset buffer i x) fun buffer' =>
    NRest.bindT (mopPair n cap) fun md => mopPair buffer' md

noncomputable def arlPred (n : ℕ) : NRest ℕ ECost := mopBinop .sub n 1

@[sepref_fr_rules] private theorem hnr_arlPred (len one : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ hnCtxt natAssn 1 one)
      (.binop .sub len len one) (hnCtxt natAssn 1 one) len natAssn (arlPred n) := by
  unfold arlPred
  exact hnr_mop_binop_self .sub len one n 1

attribute [irreducible] arlPred

noncomputable def arlCopyOverwrite (_old new : ℕ) : NRest ℕ ECost := mopCopy new

@[sepref_fr_rules] private theorem hnr_arlCopyOverwrite
    (dst src : String) (old new : ℕ) :
    hnRefine (hnCtxt natAssn old dst ∗ hnCtxt natAssn new src) (.copy dst src)
      (hnCtxt natAssn new src) dst natAssn (arlCopyOverwrite old new) := by
  unfold arlCopyOverwrite
  exact hnRefine_cons_pre (hnr_mop_copy dst src new)
    (conj_entails_mono (natAssn_entails_junkCell old dst) (entails_refl _))

noncomputable def arlSelectCap (cap₀ fourN twoN cap : ℕ) : NRest ℕ ECost :=
  irIf (decide (fourN < cap))
    (irIf (decide (15 < twoN))
      (arlCopyOverwrite cap₀ twoN) (arlCopyOverwrite cap₀ cap))
    (arlCopyOverwrite cap₀ cap)

def arlSelectCapCom (fourN twoN cap outCap : String) : Com :=
  .ite (.lt (.cell fourN) (.cell cap))
    (.ite (.lt (.lit 15) (.cell twoN))
      (.copy outCap twoN) (.copy outCap cap))
    (.copy outCap cap)

@[sepref_fr_rules] private theorem hnr_arlSelectCap
    (fourCell twoCell capCell outCap : String) (fourN twoN cap₀ cap : ℕ) :
    hnRefine (hnCtxt natAssn fourN fourCell ∗ hnCtxt natAssn twoN twoCell ∗
        hnCtxt natAssn cap capCell ∗ hnCtxt natAssn cap₀ outCap)
      (arlSelectCapCom fourCell twoCell capCell outCap)
      (hnCtxt natAssn fourN fourCell ∗ hnCtxt natAssn twoN twoCell ∗
        hnCtxt natAssn cap capCell)
      outCap natAssn (arlSelectCap cap₀ fourN twoN cap) := by
  let Γ : Assn := hnCtxt natAssn fourN fourCell ∗ hnCtxt natAssn twoN twoCell ∗
    hnCtxt natAssn cap capCell ∗ hnCtxt natAssn cap₀ outCap
  let Γ' : Assn := hnCtxt natAssn fourN fourCell ∗ hnCtxt natAssn twoN twoCell ∗
    hnCtxt natAssn cap capCell
  have hcopyTwo : hnRefine Γ (.copy outCap twoCell) Γ' outCap natAssn
      (arlCopyOverwrite cap₀ twoN) := by
    apply hnRefine_cons_post
      (hnRefine_frame_perm
        (F := hnCtxt natAssn fourN fourCell ∗ hnCtxt natAssn cap capCell)
        (by simp only [Γ]; ac_rfl)
        (hnr_arlCopyOverwrite outCap twoCell cap₀ twoN))
    simp only [Γ']
    fri
  have hcopyCap : hnRefine Γ (.copy outCap capCell) Γ' outCap natAssn
      (arlCopyOverwrite cap₀ cap) := by
    apply hnRefine_cons_post
      (hnRefine_frame_perm
        (F := hnCtxt natAssn fourN fourCell ∗ hnCtxt natAssn twoN twoCell)
        (by simp only [Γ]; ac_rfl)
        (hnr_arlCopyOverwrite outCap capCell cap₀ cap))
    simp only [Γ']
    fri
  have hcondOuter : CondRefine Γ (.lt (.cell fourCell) (.cell capCell))
      (decide (fourN < cap)) := by
    rw [show Γ = (hnCtxt natAssn fourN fourCell ∗ hnCtxt natAssn cap capCell) ∗
        (hnCtxt natAssn twoN twoCell ∗ hnCtxt natAssn cap₀ outCap) by
      simp only [Γ]; ac_rfl]
    exact (condRefine_lt_cells fourN cap fourCell capCell).frame
  have hcondInner : CondRefine Γ (.lt (.lit 15) (.cell twoCell))
      (decide (15 < twoN)) := by
    rw [show Γ = hnCtxt natAssn twoN twoCell ∗
        (hnCtxt natAssn fourN fourCell ∗ hnCtxt natAssn cap capCell ∗
          hnCtxt natAssn cap₀ outCap) by simp only [Γ]; ac_rfl]
    exact (condRefine_lt_lit_cell 15 twoN twoCell).frame
  unfold arlSelectCap arlSelectCapCom
  refine hnr_If (Γt := Γ') (Γe := Γ') hcondOuter (fun _ => ?_)
    (fun _ => hcopyCap) (MERGE_triv Γ')
  exact hnr_If (Γt := Γ') (Γe := Γ') hcondInner (fun _ => hcopyTwo)
    (fun _ => hcopyCap) (MERGE_triv Γ')

attribute [irreducible] arlSelectCap

/-- Logical shrink only: compute the source's conditional capacity decision,
but never allocate or copy the physical array. -/
noncomputable def arlButlastRaw (buffer : List ℕ) (n cap : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (arlPred n) fun n' =>
    NRest.bindT (mopBinop .mul n' 4) fun fourN =>
      NRest.bindT (mopBinop .mul n' 2) fun twoN =>
        NRest.bindT (mopCopy cap) fun cap₀ =>
          NRest.bindT (arlSelectCap cap₀ fourN twoN cap) fun cap' =>
            NRest.bindT (mopPair n' cap') fun md => mopPair buffer md

/-- The executable swap is literally get/get/set/set, matching
`gen_op_list_swap`, followed only by the two tuple-packaging skips. -/
noncomputable def arlSwapRaw (buffer : List ℕ) (n cap i j : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopAget buffer i) fun xi =>
    NRest.bindT (mopAget buffer j) fun xj =>
      NRest.bindT (mopAset buffer i xj) fun buffer' =>
        NRest.bindT (mopAset buffer' j xi) fun buffer'' =>
          NRest.bindT (mopPair n cap) fun md => mopPair buffer'' md

noncomputable def arlLengthCost : ECost := irUnit Currency.copy
noncomputable def arlIsEmptyCost : ECost :=
  irUnit Currency.ite + irUnit Currency.const
noncomputable def arlLastCost : ECost :=
  irUnit Currency.sub + irUnit Currency.aget
noncomputable def arlGetCost : ECost := irUnit Currency.aget
noncomputable def arlSetCost : ECost :=
  irUnit Currency.aset + 2 • irUnit Currency.skip
noncomputable def arlButlastCost (n cap : ℕ) : ECost :=
  irUnit Currency.sub + 2 • irUnit Currency.mul + irUnit Currency.ite +
    (if (n - 1) * 4 < cap then irUnit Currency.ite else 0) +
    2 • irUnit Currency.copy + 2 • irUnit Currency.skip
noncomputable def arlSwapCost : ECost :=
  2 • irUnit Currency.aget + 2 • irUnit Currency.aset + 2 • irUnit Currency.skip

noncomputable def arlLengthExecSpec (n : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT n) arlLengthCost
noncomputable def arlIsEmptyExecSpec (n : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT (if decide (n = 0) then 1 else 0)) arlIsEmptyCost
noncomputable def arlLastExecSpec (buffer : List ℕ) (n : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT buffer[n - 1]!) arlLastCost
noncomputable def arlGetExecSpec (buffer : List ℕ) (i : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT buffer[i]!) arlGetCost
noncomputable def arlSetExecSpec (buffer : List ℕ) (n cap i x : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT (buffer.set i x, (n, cap))) arlSetCost
noncomputable def arlButlastExecSpec (buffer : List ℕ) (n cap : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  let s : ArrayList := ⟨buffer, n, cap⟩
  NRest.consume
    (NRest.returnT (buffer, (n - 1, arlShrinkCapacity s (n - 1))))
    (arlButlastCost n cap)
noncomputable def arlSwapExecSpec (buffer : List ℕ) (n cap i j : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT
    ((buffer.set i buffer[j]!).set j buffer[i]!, (n, cap))) arlSwapCost

theorem arlLengthRaw_eq (n : ℕ) :
    arlLengthRaw n = NRest.consume (NRest.returnT n) arlLengthCost := by
  simp [arlLengthRaw, arlLengthCost, mopCopy_def]

theorem arlIsEmptyRaw_eq (n : ℕ) :
    arlIsEmptyRaw n =
      NRest.consume (NRest.returnT (if decide (n = 0) then 1 else 0)) arlIsEmptyCost := by
  by_cases h : n = 0
  · simp [arlIsEmptyRaw, arlIsEmptyCost, h, irIf_true, mopConstN,
      NRest.consume_consume, add_comm]
  · simp [arlIsEmptyRaw, arlIsEmptyCost, h, irIf_false, mopConstN,
      NRest.consume_consume, add_comm]

theorem arlLastRaw_eq (buffer : List ℕ) (n : ℕ)
    (hn : n ≠ 0) (hle : n ≤ buffer.length) :
    arlLastRaw buffer n =
      NRest.consume (NRest.returnT buffer[n - 1]!) arlLastCost := by
  have hi : n - 1 < buffer.length := by omega
  simp [arlLastRaw, arlLastCost, mopBinop_def, mopAget_def,
    NRest.assert_pos hi, Lax13Proofs.Refine.Iicf.bindT_unit,
    Imp.Bop.apply_sub, binopCurrency_sub, NRest.consume_consume]

theorem arlGetRaw_eq (buffer : List ℕ) (i : ℕ) (hi : i < buffer.length) :
    arlGetRaw buffer i = NRest.consume (NRest.returnT buffer[i]!) arlGetCost := by
  simp [arlGetRaw, arlGetCost, mopAget_def, NRest.assert_pos hi]

theorem arlSetRaw_eq (buffer : List ℕ) (n cap i x : ℕ) (hi : i < buffer.length) :
    arlSetRaw buffer n cap i x =
      NRest.consume (NRest.returnT (buffer.set i x, (n, cap))) arlSetCost := by
  simp [arlSetRaw, arlSetCost, mopAset_def, NRest.assert_pos hi,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def, NRest.consume_consume,
    two_nsmul]

theorem arlButlastRaw_eq (buffer : List ℕ) (n cap : ℕ) :
    arlButlastRaw buffer n cap =
      arlButlastExecSpec buffer n cap := by
  by_cases hfour : (n - 1) * 4 < cap
  · by_cases htwo : 15 < (n - 1) * 2
    · have hmin : arlMinimumCapacity ≤ (n - 1) * 2 := by
        simp [arlMinimumCapacity]
        omega
      simp [arlButlastRaw, arlButlastExecSpec, arlButlastCost, arlShrinkCapacity,
        arlPred, arlSelectCap, arlCopyOverwrite, hfour, htwo, hmin, mopBinop_def,
        Lax13Proofs.Refine.Iicf.bindT_unit,
        Imp.Bop.apply_sub, Imp.Bop.apply_mul, binopCurrency_sub, binopCurrency_mul,
        irIf_true, mopCopy_def, mopPair_def, NRest.consume_consume, two_nsmul]
      ac_rfl
    · have hmin : ¬ arlMinimumCapacity ≤ (n - 1) * 2 := by
        simp [arlMinimumCapacity]
        omega
      simp [arlButlastRaw, arlButlastExecSpec, arlButlastCost, arlShrinkCapacity,
        arlPred, arlSelectCap, arlCopyOverwrite, hfour, htwo, hmin, mopBinop_def,
        Lax13Proofs.Refine.Iicf.bindT_unit,
        Imp.Bop.apply_sub, Imp.Bop.apply_mul, binopCurrency_sub, binopCurrency_mul,
        irIf_true, irIf_false, mopCopy_def, mopPair_def, NRest.consume_consume,
        two_nsmul]
      ac_rfl
  · simp [arlButlastRaw, arlButlastExecSpec, arlButlastCost, arlShrinkCapacity,
      arlPred, arlSelectCap, arlCopyOverwrite, hfour, mopBinop_def,
      Lax13Proofs.Refine.Iicf.bindT_unit,
      Imp.Bop.apply_sub, Imp.Bop.apply_mul, binopCurrency_sub, binopCurrency_mul,
      irIf_false, mopCopy_def, mopPair_def, NRest.consume_consume, two_nsmul]
    ac_rfl

theorem arlSwapRaw_eq (buffer : List ℕ) (n cap i j : ℕ)
    (hi : i < buffer.length) (hj : j < buffer.length) :
    arlSwapRaw buffer n cap i j = NRest.consume
      (NRest.returnT
        ((buffer.set i buffer[j]!).set j buffer[i]!, (n, cap))) arlSwapCost := by
  simp [arlSwapRaw, arlSwapCost, mopAget_def, mopAset_def,
    NRest.assert_pos hi, NRest.assert_pos hj,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def, NRest.consume_consume,
    two_nsmul]
  ac_rfl

/-! The following seven rules are the executable boundary.  Their inferred
commands are pinned below, so the budget definitions above are read from the
commands rather than assigned to abstract operations by fiat. -/

sepref_synth arlLengthSynth (len out : String) (n : ℕ) :
  hnRefine (hnCtxt natAssn n len ∗ junkCell out)
    _ _ out natAssn (arlLengthRaw n)

sepref_synth arlIsEmptySynth (len out : String) (n : ℕ) :
  hnRefine (hnCtxt natAssn n len ∗ junkCell out)
    _ _ out natAssn (arlIsEmptyRaw n)

sepref_synth arlLastSynth (A len one idx out : String) (buffer : List ℕ) (n : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn 1 one ∗ junkCell idx ∗ junkCell out)
    _ _ out natAssn (arlLastRaw buffer n)

sepref_synth arlGetSynth (A idx out : String) (buffer : List ℕ) (i : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗ junkCell out)
    _ _ out natAssn (arlGetRaw buffer i)

sepref_synth arlSetSynth (A len cap idx value : String)
    (buffer : List ℕ) (n c i x : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn i idx ∗ hnCtxt natAssn x value)
    _ _ (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (arlSetRaw buffer n c i x)

set_option maxHeartbeats 800000 in
sepref_synth arlButlastSynth
    (A len cap one four two fourN twoN outCap : String)
    (buffer : List ℕ) (n c : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn 1 one ∗ hnCtxt natAssn 4 four ∗
      hnCtxt natAssn 2 two ∗ junkCell fourN ∗ junkCell twoN ∗ junkCell outCap)
    _ _ (A, (len, outCap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (arlButlastRaw buffer n c)

sepref_synth arlSwapSynth (A len cap I J XI XJ : String)
    (buffer : List ℕ) (n c i j : ℕ) :
  hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
      junkCell XI ∗ junkCell XJ)
    _ _ (A, (len, cap)) (arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (arlSwapRaw buffer n c i j)

def arlLengthCom (len out : String) : Com := .copy out len

def arlIsEmptyCom (len out : String) : Com :=
  .ite (.eq (.cell len) (.lit 0)) (.const out 1) (.const out 0)

def arlLastCom (A len one idx out : String) : Com :=
  .seq (.binop .sub idx len one) (.aget out A idx)

def arlGetCom (A idx out : String) : Com := .aget out A idx

def arlSetCom (A _len _cap idx value : String) : Com :=
  .seq (.aset A idx value) (.seq .skip .skip)

def arlButlastCom (_A len cap one four two fourN twoN outCap : String) : Com :=
  .seq (.binop .sub len len one)
    (.seq (.binop .mul fourN len four)
      (.seq (.binop .mul twoN len two)
        (.seq (.copy outCap cap)
          (.seq (arlSelectCapCom fourN twoN cap outCap) (.seq .skip .skip)))))

def arlSwapCom (A _len _cap I J XI XJ : String) : Com :=
  .seq (.aget XI A I)
    (.seq (.aget XJ A J)
      (.seq (.aset A I XJ) (.seq (.aset A J XI) (.seq .skip .skip))))

@[sepref_fr_rules] theorem arlLength_exec_hnr (len out : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ junkCell out)
      (arlLengthCom len out) (hnCtxt natAssn n len) out natAssn
      (arlLengthExecSpec n) := by
  rw [arlLengthExecSpec]
  rw [← arlLengthRaw_eq]
  exact arlLengthSynth len out n

@[sepref_fr_rules] theorem arlIsEmpty_exec_hnr (len out : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ junkCell out)
      (arlIsEmptyCom len out) ((□ : Assn) ∗ hnCtxt natAssn n len) out natAssn
      (arlIsEmptyExecSpec n) := by
  rw [arlIsEmptyExecSpec]
  rw [← arlIsEmptyRaw_eq]
  exact arlIsEmptySynth len out n

@[sepref_fr_rules] theorem arlLast_exec_hnr
    (A len one idx out : String) (buffer : List ℕ) (n : ℕ)
    (hn : n ≠ 0) (hle : n ≤ buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn 1 one ∗ junkCell idx ∗ junkCell out)
      (arlLastCom A len one idx out)
      (hnCtxt arrayAssn buffer A ∗ junkCell idx ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn 1 one) out natAssn
      (arlLastExecSpec buffer n) := by
  rw [arlLastExecSpec]
  rw [← arlLastRaw_eq buffer n hn hle]
  exact arlLastSynth A len one idx out buffer n

@[sepref_fr_rules] theorem arlGet_exec_hnr
    (A idx out : String) (buffer : List ℕ) (i : ℕ)
    (hi : i < buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx ∗ junkCell out)
      (arlGetCom A idx out)
      (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn i idx) out natAssn
      (arlGetExecSpec buffer i) := by
  rw [arlGetExecSpec]
  rw [← arlGetRaw_eq buffer i hi]
  exact arlGetSynth A idx out buffer i

@[sepref_fr_rules] theorem arlSet_exec_hnr (A len cap idx value : String)
    (buffer : List ℕ) (n c i x : ℕ) (hi : i < buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn i idx ∗ hnCtxt natAssn x value)
      (arlSetCom A len cap idx value)
      (hnCtxt natAssn i idx ∗ hnCtxt natAssn x value) (A, (len, cap))
      (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (arlSetExecSpec buffer n c i x) := by
  rw [arlSetExecSpec]
  rw [← arlSetRaw_eq buffer n c i x hi]
  exact arlSetSynth A len cap idx value buffer n c i x

@[sepref_fr_rules] theorem arlButlast_exec_hnr
    (A len cap one four two fourN twoN outCap : String)
    (buffer : List ℕ) (n c : ℕ) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn 1 one ∗ hnCtxt natAssn 4 four ∗
      hnCtxt natAssn 2 two ∗ junkCell fourN ∗ junkCell twoN ∗ junkCell outCap)
      (arlButlastCom A len cap one four two fourN twoN outCap)
      (junkCell fourN ∗ junkCell twoN ∗ hnCtxt natAssn c cap ∗
        hnCtxt natAssn 2 two ∗ hnCtxt natAssn 4 four ∗ hnCtxt natAssn 1 one)
      (A, (len, outCap))
      (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (arlButlastExecSpec buffer n c) := by
  rw [← arlButlastRaw_eq buffer n c]
  exact arlButlastSynth A len cap one four two fourN twoN outCap buffer n c

@[sepref_fr_rules] theorem arlSwap_exec_hnr (A len cap I J XI XJ : String)
    (buffer : List ℕ) (n c i j : ℕ)
    (hi : i < buffer.length) (hj : j < buffer.length) :
    hnRefine (hnCtxt arrayAssn buffer A ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        junkCell XI ∗ junkCell XJ)
      (arlSwapCom A len cap I J XI XJ)
      (hnCtxt natAssn j J ∗ junkCell XI ∗ hnCtxt natAssn i I ∗ junkCell XJ)
      (A, (len, cap))
      (arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (arlSwapExecSpec buffer n c i j) := by
  rw [arlSwapExecSpec]
  rw [← arlSwapRaw_eq buffer n c i j hi hj]
  exact arlSwapSynth A len cap I J XI XJ buffer n c i j

/-! ### Bridges to the cost-silent list interface -/

theorem listAt?_eq_getElem? (xs : List ℕ) (i : ℕ) : listAt? xs i = xs[i]? := by
  induction xs generalizing i with
  | nil => simp [listAt?]
  | cons x xs ih => cases i <;> simp [listAt?, ih]

theorem listSet_eq_set (xs : List ℕ) (i x : ℕ) : listSet xs i x = xs.set i x := by
  induction xs generalizing i with
  | nil => simp [listSet]
  | cons y ys ih => cases i <;> simp [listSet, ih]

theorem buffer_getElem_eq_active {s : ArrayList} (hs : s.Wf) {i : ℕ}
    (hi : i < s.length) : s.buffer[i]! = s.active[i]! := by
  have hib : i < s.buffer.length := hi.trans_le (hs.2.1.trans hs.2.2)
  have hia : i < s.active.length := by
    rw [boundedActive_length s hs]
    exact hi
  unfold BoundedArray.active at hia ⊢
  calc
    s.buffer[i]! = s.buffer[i] := getElem!_pos s.buffer i hib
    _ = (s.buffer.take s.length)[i] := List.getElem_take.symm
    _ = (s.buffer.take s.length)[i]! :=
      (getElem!_pos (s.buffer.take s.length) i hia).symm

theorem arlLengthExecSpec_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) :
    arlLengthExecSpec s.length =
      NRest.consume (NRest.returnT xs.length) arlLengthCost := by
  rw [arlLengthExecSpec, arrayListRel_length h]

/-- A Boolean result is stored as the conventional natural `1`/`0`. -/
theorem arlIsEmptyExecSpec_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) :
    arlIsEmptyExecSpec s.length = NRest.consume
      (NRest.returnT (if decide (xs = []) then 1 else 0)) arlIsEmptyCost := by
  rw [arrayListRel_length h]
  cases xs <;> simp [arlIsEmptyExecSpec]

theorem arlGetExecSpec_refines {s : ArrayList} {xs : List ℕ} {i : ℕ}
    (h : (s, xs) ∈ arrayListRel) (hi : i < xs.length) :
    arlGetExecSpec s.buffer i =
      NRest.consume (NRest.returnT xs[i]!) arlGetCost := by
  have his : i < s.length := by simpa [arrayListRel_length h] using hi
  change s.Wf ∧ s.active = xs at h
  rw [arlGetExecSpec, buffer_getElem_eq_active h.1 his, h.2]

theorem arlLastExecSpec_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) (hne : xs ≠ []) :
    ∃ x, listAt? xs.reverse 0 = some x ∧
      arlLastExecSpec s.buffer s.length =
        NRest.consume (NRest.returnT x) arlLastCost := by
  have hn : s.length ≠ 0 := by simpa [arrayListRel_length h] using hne
  have hi : s.length - 1 < s.length := by omega
  change s.Wf ∧ s.active = xs at h
  have hb := buffer_getElem_eq_active h.1 hi
  rw [h.2] at hb
  have hlen : s.length = xs.length := arrayListRel_length ⟨h.1, h.2⟩
  have hv : s.buffer[s.length - 1]! = xs.getLast hne := by
    rw [hb, hlen, getElem!_pos]
    exact (List.getLast_eq_getElem hne).symm
  refine ⟨xs.getLast hne, ?_, ?_⟩
  · have hr : xs.reverse ≠ [] := by simpa
    have hh := List.getLast_eq_head_reverse hne
    cases he : xs.reverse with
    | nil => exact absurd he hr
    | cons y ys => simpa [listAt?, he] using congrArg some hh.symm
  · rw [arlLastExecSpec, hv]

def arlSetExecState (s : ArrayList) (i x : ℕ) : ArrayList :=
  ⟨s.buffer.set i x, s.length, s.capacity⟩

def arlButlastExecState (s : ArrayList) : ArrayList :=
  ⟨s.buffer, s.length - 1, arlShrinkCapacity s (s.length - 1)⟩

def arlSwapExecState (s : ArrayList) (i j : ℕ) : ArrayList :=
  ⟨(s.buffer.set i s.buffer[j]!).set j s.buffer[i]!, s.length, s.capacity⟩

theorem arlButlast?_eq_execState {s : ArrayList} (hne : s.length ≠ 0) :
    arlButlast? s = some (arlButlastExecState s) := by
  simp [arlButlast?, arlButlastExecState, hne]

theorem arlSetExecState_refines {s : ArrayList} {xs : List ℕ} {i x : ℕ}
    (h : (s, xs) ∈ arrayListRel) (hi : i < xs.length) :
    (arlSetExecState s i x, listSet xs i x) ∈ arrayListRel := by
  change s.Wf ∧ s.active = xs at h
  have hal := boundedActive_length s h.1
  rw [h.2] at hal
  have his : i < s.length := by omega
  rcases h.1 with ⟨hpos, hlen, hcap⟩
  refine ⟨⟨hpos, hlen, by simpa [arlSetExecState] using hcap⟩, ?_⟩
  simp [arlSetExecState, BoundedArray.active, List.take_set, listSet_eq_set, ← h.2]

theorem arlButlastExecState_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) (hne : xs ≠ []) :
    (arlButlastExecState s, listButlast xs) ∈ arrayListRel := by
  have hsne : s.length ≠ 0 := (arrayListRel_nonempty h).mpr hne
  apply arlButlast?_some_refines h
  exact arlButlast?_eq_execState hsne

theorem arlSwapExecState_refines {s : ArrayList} {xs : List ℕ} {i j : ℕ}
    (h : (s, xs) ∈ arrayListRel) (hi : i < xs.length) (hj : j < xs.length) :
    (arlSwapExecState s i j, listSwap xs i j) ∈ arrayListRel := by
  change s.Wf ∧ s.active = xs at h
  have hal := boundedActive_length s h.1
  rw [h.2] at hal
  have his : i < s.length := by omega
  have hjs : j < s.length := by omega
  have hbi := buffer_getElem_eq_active h.1 his
  have hbj := buffer_getElem_eq_active h.1 hjs
  have hswap : listSwap xs i j = (xs.set i xs[j]!).set j xs[i]! := by
    unfold listSwap
    rw [listAt?_eq_getElem?, listAt?_eq_getElem?,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simp [listSet_eq_set, getElem!_pos, hi, hj]
  rcases h.1 with ⟨hpos, hlen, hcap⟩
  refine ⟨⟨hpos, hlen, by simpa [arlSwapExecState] using hcap⟩, ?_⟩
  simp only [arlSwapExecState, BoundedArray.active, List.take_set]
  have hactive : s.buffer.take s.length = xs := h.2
  rw [hbi, hbj, h.2, hactive, hswap]

theorem arlSetExecSpec_refines {s : ArrayList} {xs : List ℕ} {i x : ℕ}
    (h : (s, xs) ∈ arrayListRel) (hi : i < xs.length) :
    arlSetExecSpec s.buffer s.length s.capacity i x = NRest.consume
        (NRest.returnT ((arlSetExecState s i x).buffer,
          ((arlSetExecState s i x).length, (arlSetExecState s i x).capacity)))
        arlSetCost ∧
      (arlSetExecState s i x, listSet xs i x) ∈ arrayListRel := by
  exact ⟨rfl, arlSetExecState_refines h hi⟩

theorem arlButlastExecSpec_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) (hne : xs ≠ []) :
    arlButlastExecSpec s.buffer s.length s.capacity = NRest.consume
        (NRest.returnT ((arlButlastExecState s).buffer,
          ((arlButlastExecState s).length, (arlButlastExecState s).capacity)))
        (arlButlastCost s.length s.capacity) ∧
      (arlButlastExecState s, listButlast xs) ∈ arrayListRel := by
  exact ⟨rfl, arlButlastExecState_refines h hne⟩

theorem arlSwapExecSpec_refines {s : ArrayList} {xs : List ℕ} {i j : ℕ}
    (h : (s, xs) ∈ arrayListRel) (hi : i < xs.length) (hj : j < xs.length) :
    arlSwapExecSpec s.buffer s.length s.capacity i j = NRest.consume
        (NRest.returnT ((arlSwapExecState s i j).buffer,
          ((arlSwapExecState s i j).length, (arlSwapExecState s i j).capacity)))
        arlSwapCost ∧
      (arlSwapExecState s i j, listSwap xs i j) ∈ arrayListRel := by
  exact ⟨rfl, arlSwapExecState_refines h hi hj⟩

/-! ## Executable and disposition gates -/

#guard arlInitialCapacity = 16
#guard arlMinimumCapacity = 16
#guard arlEmptyIn (List.replicate 16 9) = some ⟨List.replicate 16 9, 0, 16⟩
#guard arlEmptyIn (List.replicate 15 9) = none
#guard arlAppend ⟨[0, 0, 0, 0], 1, 4⟩ 7 = some ⟨[0, 7, 0, 0], 2, 4⟩
#guard arlAppend ⟨List.replicate 8 0, 2, 2⟩ 5 =
  some ⟨(List.replicate 8 0).set 2 5, 3, 4⟩
/-! ### The old failure mode, as compiled data

`⟨[1,2,3,4], 4, 4⟩` is the state the pre-P5.E rule could say nothing about:
well-formed, physically full, `boundedPush` returns `none`.  The re-seated
append succeeds on it, allocating a block of 8. -/

#guard arlAppend ⟨[1, 2, 3, 4], 4, 4⟩ 9 = none
#guard arlAppendTotal ⟨[1, 2, 3, 4], 4, 4⟩ 9 =
  ⟨[1, 2, 3, 4, 9, 0, 0, 0], 5, 8⟩
#guard (arlAppendTotal ⟨[1, 2, 3, 4], 4, 4⟩ 9).active = [1, 2, 3, 4, 9]
#guard arlAllocatedBy ⟨[1, 2, 3, 4], 4, 4⟩ 9 = 8

/-- **Non-smuggling control.**  The registered refinement, instantiated at
exactly the state the deleted `arrayListReadyRel` excluded: well-formed,
physically full, `boundedPush` returns `none`.  The only hypothesis supplied is
membership in `arrayListRel`.  If a readiness conjunct had been re-added
anywhere along the chain — in the relation, in the assertion, or as a fref side
condition — this would not elaborate. -/
theorem arlAppend_succeeds_at_full_buffer :
    (arlAppendTotal ⟨[1, 2, 3, 4], 4, 4⟩ 9, [1, 2, 3, 4] ++ [9]) ∈ arrayListRel ∧
      boundedPush (⟨[1, 2, 3, 4], 4, 4⟩ : ArrayList) 0 = none := by
  refine ⟨arlAppendTotal_refines (xs := [1, 2, 3, 4]) ?_, by decide⟩
  exact ⟨⟨by decide, by decide, by decide⟩, rfl⟩
-- in-place branch: no allocation, and the buffer is the caller's
#guard arlAppendTotal ⟨[0, 0, 0, 0], 1, 4⟩ 7 = ⟨[0, 7, 0, 0], 2, 4⟩
#guard arlAllocatedBy ⟨[0, 0, 0, 0], 1, 4⟩ 7 = 0
-- logical-doubling branch: still no allocation
#guard arlAppendTotal ⟨List.replicate 8 0, 2, 2⟩ 5 =
  ⟨(List.replicate 8 0).set 2 5, 3, 4⟩
#guard arlAllocatedBy ⟨List.replicate 8 0, 2, 2⟩ 5 = 0
-- negative control: `arlAppendTotal` is NOT `arlPushGrown` — the branch is
-- what keeps the amortized bound, and flipping to unconditional growth
-- changes the state and would allocate on every push.
#guard arlPushGrown ⟨[0, 0, 0, 0], 1, 4⟩ 7 ≠ arlAppendTotal ⟨[0, 0, 0, 0], 1, 4⟩ 7

/-! ### The leak bound is not vacuous

Sixteen appends into an initially-full capacity-1 buffer really do leak
`2 + 4 + 8 + 16 + 32 = 62` cells against `17` live elements; the proved
`4 × live` bound is `68`, and a `3 × live` bound would be false right here. -/

#guard arlAllocatedMany ⟨[7], 1, 1⟩ (List.range 16) = 62
#guard (arlAppendMany ⟨[7], 1, 1⟩ (List.range 16)).length = 17
#guard arlAllocatedMany ⟨[7], 1, 1⟩ (List.range 16) ≤
  4 * (arlAppendMany ⟨[7], 1, 1⟩ (List.range 16)).length
#guard ¬ (arlAllocatedMany ⟨[7], 1, 1⟩ (List.range 16) ≤
  3 * (arlAppendMany ⟨[7], 1, 1⟩ (List.range 16)).length)
#guard (arlAppendMany ⟨[7], 1, 1⟩ (List.range 16)).active =
  7 :: List.range 16

/-! ### The amortized bound is not vacuous either

Each negative control below is the same inequality with one component
weakened; each is false, so each of the numbers in `arlAdvertisedCostN` and
the potential itself is load-bearing.  The Boolean mirror is `PushCost.le_def`
spelled out, so it is the same inequality the theorem states. -/

private def arlAmortizedHolds (s : ArrayList) (x : ℕ)
    (adv pot potNext : PushCost) : Bool :=
  let l := PushCost.plus (arlAppendCostN s) potNext
  let r := PushCost.plus adv pot
  l.control ≤ r.control && l.write ≤ r.write && l.add ≤ r.add && l.copy ≤ r.copy

private def arlAmortizedStep (s : ArrayList) (x : ℕ) (adv : PushCost) : Bool :=
  arlAmortizedHolds s x adv (arlPotentialN s) (arlPotentialN (arlAppendTotal s x))

#guard arlAmortizedStep ⟨[1, 2, 3, 4], 4, 4⟩ 9 arlAdvertisedCostN
#guard arlAmortizedStep ⟨[0, 0, 0, 0], 1, 4⟩ 7 arlAdvertisedCostN
#guard arlAmortizedStep ⟨List.replicate 8 0, 2, 2⟩ 5 arlAdvertisedCostN
-- one fewer copy credit: the growth branch no longer pays for itself
#guard ¬ arlAmortizedStep ⟨[1, 2, 3, 4], 4, 4⟩ 9 ⟨4, 1, 1, 1⟩
-- one fewer control credit: the allocator's two units are real
#guard ¬ arlAmortizedStep ⟨[1, 2, 3, 4], 4, 4⟩ 9 ⟨3, 1, 1, 2⟩
-- the potential itself is load-bearing: with no potential the copy is naked
#guard ¬ arlAmortizedHolds ⟨[1, 2, 3, 4], 4, 4⟩ 9 arlAdvertisedCostN
  ⟨0, 0, 0, 0⟩ ⟨0, 0, 0, 0⟩

#guard arlButlast? ⟨List.replicate 80 0, 20, 80⟩ =
  some ⟨List.replicate 80 0, 19, 38⟩
#guard arlButlast? ⟨List.replicate 16 0, 1, 16⟩ =
  some ⟨List.replicate 16 0, 0, 16⟩
#guard arlButlastExecState ⟨List.replicate 80 0, 20, 80⟩ =
  ⟨List.replicate 80 0, 19, 38⟩
#guard arlButlastExecState ⟨List.replicate 16 0, 5, 16⟩ =
  ⟨List.replicate 16 0, 4, 16⟩

#guard arlLengthCom "len" "out" = .copy "out" "len"
#guard arlIsEmptyCom "len" "out" =
  .ite (.eq (.cell "len") (.lit 0)) (.const "out" 1) (.const "out" 0)
#guard arlLastCom "A" "len" "one" "idx" "out" =
  .seq (.binop .sub "idx" "len" "one") (.aget "out" "A" "idx")
#guard arlGetCom "A" "idx" "out" = .aget "out" "A" "idx"
#guard arlSetCom "A" "len" "cap" "idx" "value" =
  .seq (.aset "A" "idx" "value") (.seq .skip .skip)
#guard arlSelectCapCom "fourN" "twoN" "cap" "outCap" =
  .ite (.lt (.cell "fourN") (.cell "cap"))
    (.ite (.lt (.lit 15) (.cell "twoN"))
      (.copy "outCap" "twoN") (.copy "outCap" "cap"))
    (.copy "outCap" "cap")
#guard arlButlastCom "A" "len" "cap" "one" "four" "two" "fourN" "twoN" "outCap" =
  .seq (.binop .sub "len" "len" "one")
    (.seq (.binop .mul "fourN" "len" "four")
      (.seq (.binop .mul "twoN" "len" "two")
        (.seq (.copy "outCap" "cap")
          (.seq (arlSelectCapCom "fourN" "twoN" "cap" "outCap")
            (.seq .skip .skip)))))
#guard arlSwapCom "A" "len" "cap" "i" "j" "xi" "xj" =
  .seq (.aget "xi" "A" "i")
    (.seq (.aget "xj" "A" "j")
      (.seq (.aset "A" "i" "xj")
        (.seq (.aset "A" "j" "xi") (.seq .skip .skip))))

theorem arlLengthCost_copy : arlLengthCost.toFun Currency.copy = 1 := by decide +kernel
theorem arlIsEmptyCost_ite : arlIsEmptyCost.toFun Currency.ite = 1 := by decide +kernel
theorem arlIsEmptyCost_const : arlIsEmptyCost.toFun Currency.const = 1 := by decide +kernel
theorem arlLastCost_sub : arlLastCost.toFun Currency.sub = 1 := by decide +kernel
theorem arlLastCost_aget : arlLastCost.toFun Currency.aget = 1 := by decide +kernel
theorem arlGetCost_aget : arlGetCost.toFun Currency.aget = 1 := by decide +kernel
theorem arlSetCost_aset : arlSetCost.toFun Currency.aset = 1 := by decide +kernel
theorem arlSetCost_skip : arlSetCost.toFun Currency.skip = 2 := by decide +kernel
theorem arlButlastCost_sub : (arlButlastCost 20 80).toFun Currency.sub = 1 := by
  decide +kernel
theorem arlButlastCost_mul : (arlButlastCost 20 80).toFun Currency.mul = 2 := by
  decide +kernel
theorem arlButlastCost_copy : (arlButlastCost 20 80).toFun Currency.copy = 2 := by
  decide +kernel
theorem arlButlastCost_skip : (arlButlastCost 20 80).toFun Currency.skip = 2 := by
  decide +kernel
theorem arlButlastCost_ite_shrink : (arlButlastCost 20 80).toFun Currency.ite = 2 := by
  decide +kernel
theorem arlButlastCost_ite_keep : (arlButlastCost 5 16).toFun Currency.ite = 1 := by
  decide +kernel
theorem arlSwapCost_aget : arlSwapCost.toFun Currency.aget = 2 := by decide +kernel
theorem arlSwapCost_aset : arlSwapCost.toFun Currency.aset = 2 := by decide +kernel
theorem arlSwapCost_skip : arlSwapCost.toFun Currency.skip = 2 := by decide +kernel

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``arlCopyOp_refines, ``arlAppendOp_refines,
      ``arlLengthOp_refines, ``arlIsEmptyOp_refines, ``arlLastOp_refines,
      ``arlButlastOp_refines, ``arlGetOp_refines, ``arlSetOp_refines,
      ``arlSwapOp_refines] do
    unless rules.contains n do
      throwError "array-list rule gate: missing refinement rule {n}"

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  for n in #[``arlLength_exec_hnr, ``arlIsEmpty_exec_hnr, ``arlLast_exec_hnr,
      ``arlButlast_exec_hnr, ``arlGet_exec_hnr, ``arlSet_exec_hnr,
      ``arlSwap_exec_hnr] do
    unless rules.contains n do
      throwError "array-list executable rule gate: missing concrete rule {n}"

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppend_some_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlAppend_some_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppendTotal_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlAppendTotal_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppendOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlAppendOp_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppendRaw_le_amortized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlAppendRaw_le_amortized

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAllocatedMany_live_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arlAllocatedMany_live_bounded

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlButlast?_some_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arlButlast?_some_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppend_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlAppend_exec_hnr

end Lax13Proofs.Refine.Sepref.Iicf
