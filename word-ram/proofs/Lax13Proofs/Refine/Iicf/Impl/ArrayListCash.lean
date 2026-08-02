import Lax13Proofs.Refine.Iicf.Impl.ArrayListGrow

/-!
# Cashing the array list's amortized headline into machine currencies

Leaf **P4.5.A.5**, satellite of `ArrayList.lean` and `ArrayListGrow.lean`
(ledger **E35**).

`ArrayList.lean` states `arlAppend_amortized_costN` and
`arlAppendRaw_le_amortized` in `PushCost`'s four *abstract* currencies
`dyn.control` / `dyn.write` / `dyn.add` / `dyn.copy`.  `ArrayListGrow.lean`
says in prose that those and the IR's own currencies "are related by prose,
not by a theorem".  Until this file, `dyn.*` occurred nowhere but its own
definition, and no `Iicf/` file used `timerefine` at all: the amortized-O(1)
claim was internally consistent and had **no machine content**.

This file supplies the missing exchange rate `dynRate : String → ECost`,
proves it well formed (`dynRate_wf : wfR'' dynRate`), proves that it
**dominates what the emitted programs actually charge on every branch**, and
restates the amortized bound in the IR currencies that
`computesInTime_of_spec` consumes.

## The rate, and where each price comes from

| abstract | buys | why |
|---|---|---|
| `dyn.control` | `ir.ite + ir.mul + ir.while + 2·ir.copy + ir.const + 4·ir.skip` | one push's branch/bookkeeping share |
| `dyn.write` | `ir.aset` | the element write |
| `dyn.add` | `3·ir.add` | length bump, allocator's pointer bump, copy's end cursor |
| `dyn.copy` | `blitPayload` = `ir.while + ir.aget + ir.aset + 2·ir.add` | **one iteration** of the emitted copy loop |

Nothing here is chosen to make a theorem come out.  Each component is forced,
and `IrVecN`-level compiled gates below flip each one down by a unit and
exhibit the branch on which domination then fails.

* `ir.ite`, `ir.copy`, `ir.const`, `4·ir.skip` in the control unit are forced
  by the **in-place** branch, which pays `dyn.control = 1`: the adapter's
  emitted command charges exactly `ite + aset + add + copy + const + 4·skip`
  (`boundedExecCostN_space`).
* `ir.mul` is forced by the **logical-doubling** branch, which pays
  `dyn.control = 2` against an emitted `2·ite + mul + …`
  (`boundedExecCostN_double`); a control unit with no `ir.mul` buys none.
* `ir.while` in the control unit is forced by the **growth** branch — see the
  trailing-guard paragraph.
* `2·ir.copy` per control unit is forced by the growth branch, which needs
  five `ir.copy`: one for `mopAlloc`'s pointer (`allocCost`), three for the
  cursor-setup block `si`/`di`/`dc` that `ArrayListGrow.lean` names, and one
  for the push's capacity copy.  Four control units at one `ir.copy` each
  would buy four, and four is less than five.
* `3·ir.add` per `dyn.add` is forced by the growth branch, which pays
  `2n + 3` additions: `2n` inside the copy loop (bought by `dyn.copy`), plus
  the allocator's bump, the end cursor `se ← sp + n`, and the length bump.

## Where the trailing `+1` guard went

`blitCost n = (n+1)·ir.while + n·ir.aget + n·ir.aset + 2n·ir.add`.  The `n`
successful guard tests ride with the elements, in `dyn.copy`.  The **trailing
failed guard is folded into `dyn.control`**: every push's control unit buys
one `ir.while`, so the growth branch's four control units buy four, of which
the copy loop needs exactly one beyond the `n` that `dyn.copy` supplies.
`n + 1 ≤ n + 4`.  On the two in-place branches no loop runs and those
`ir.while` credits are unspent slack — the cost of pricing the guard
per-push rather than per-growth-event.  Deleting `ir.while` from the control
unit leaves the growth branch with `n` guard credits against `n + 1` needed,
for every `n`; that is the compiled negative control `dominates_growth_no_while`.

## Does the growth branch's `dyn.control = 4` cover allocation and setup?

**Yes, with one unit of slack.**  The growth branch needs, outside the write,
the length bump and the copy loop: `2·ir.ite`, `1·ir.mul`, `1·ir.while`,
`5·ir.copy`, `2·ir.const`, `4·ir.skip`.  Four control units buy
`4/4/4/8/4/16`.  The binding component is `ir.copy` (5 needed, 8 bought);
`3` control units would already buy `6 ≥ 5` and suffice.  So P4's constant
`4` is **sound but not tight** at this rate — unlike `arlCopyCost` (E34) it
is an over-estimate, not an under-estimate, and the amortized statement is
unaffected.  This is recorded rather than "corrected": lowering it would
change `arlAdvertisedCostN`, which is source-shaped.

## What the growth branch's machine cost is

There is no landed single emitted command for growth — `ArrayListGrow.lean`
names the missing piece as the cursor-setup block.  So the machine cost is
assembled here from the three landed, program-pinned prices plus that named
block:

* dispatch `2·ir.ite + ir.mul` — the same two branch tests and the same
  `2 * capacity` as the doubling branch of `boundedExecCostN`;
* `allocCost` = `ir.copy + ir.add`, size-independent (`allocCost_const`);
* the five-instruction cursor setup `si`/`di`/`dc` (`ir.copy`),
  `se ← sp + n` (`ir.add`), `one ← 1` (`ir.const`), exactly the cells
  `arlGrowCopy_hnr` requires;
* `blitCost s.length`, pinned against `blitProg` (`blitCost_eq`);
* the push and the observable packing, exactly the adapter's
  `boundedExecCostN` success payload.

## What is *not* touched

`arlAppendOp_refines` is unchanged — still `@[sepref_fref_thms]` over
`arrayListRel` at precondition `fun _ : List ℕ => True`.  It is re-checked
here as a compiled term (`arlAppendOp_refines_unchanged`).  The `dyn.*`
statements in `ArrayList.lean` are untouched: they are the source-shaped
layer, and this file is additive.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## 1. A nine-currency executable cost vector

The array list's whole stack — adapter, allocator, copy loop, packing —
touches exactly nine IR currencies.  Working in an executable record of nine
naturals makes every domination claim a `#guard`-able `Prop` and every
proof an `omega`. -/

/-- The nine IR currencies the array-list stack can pay, as naturals. -/
structure IrVecN where
  ite : ℕ
  mul : ℕ
  loop : ℕ
  copy : ℕ
  const : ℕ
  skip : ℕ
  aset : ℕ
  aget : ℕ
  add : ℕ
  deriving DecidableEq, Repr

namespace IrVecN

instance : Add IrVecN :=
  ⟨fun v w => ⟨v.ite + w.ite, v.mul + w.mul, v.loop + w.loop, v.copy + w.copy,
    v.const + w.const, v.skip + w.skip, v.aset + w.aset, v.aget + w.aget, v.add + w.add⟩⟩

instance : SMul ℕ IrVecN :=
  ⟨fun k v => ⟨k * v.ite, k * v.mul, k * v.loop, k * v.copy, k * v.const, k * v.skip,
    k * v.aset, k * v.aget, k * v.add⟩⟩

@[simp] theorem padd_ite (v w : IrVecN) : (v + w).ite = v.ite + w.ite := rfl
@[simp] theorem padd_mul (v w : IrVecN) : (v + w).mul = v.mul + w.mul := rfl
@[simp] theorem padd_loop (v w : IrVecN) : (v + w).loop = v.loop + w.loop := rfl
@[simp] theorem padd_copy (v w : IrVecN) : (v + w).copy = v.copy + w.copy := rfl
@[simp] theorem padd_const (v w : IrVecN) : (v + w).const = v.const + w.const := rfl
@[simp] theorem padd_skip (v w : IrVecN) : (v + w).skip = v.skip + w.skip := rfl
@[simp] theorem padd_aset (v w : IrVecN) : (v + w).aset = v.aset + w.aset := rfl
@[simp] theorem padd_aget (v w : IrVecN) : (v + w).aget = v.aget + w.aget := rfl
@[simp] theorem padd_add (v w : IrVecN) : (v + w).add = v.add + w.add := rfl

@[simp] theorem psmul_ite (k : ℕ) (v : IrVecN) : (k • v).ite = k * v.ite := rfl
@[simp] theorem psmul_mul (k : ℕ) (v : IrVecN) : (k • v).mul = k * v.mul := rfl
@[simp] theorem psmul_loop (k : ℕ) (v : IrVecN) : (k • v).loop = k * v.loop := rfl
@[simp] theorem psmul_copy (k : ℕ) (v : IrVecN) : (k • v).copy = k * v.copy := rfl
@[simp] theorem psmul_const (k : ℕ) (v : IrVecN) : (k • v).const = k * v.const := rfl
@[simp] theorem psmul_skip (k : ℕ) (v : IrVecN) : (k • v).skip = k * v.skip := rfl
@[simp] theorem psmul_aset (k : ℕ) (v : IrVecN) : (k • v).aset = k * v.aset := rfl
@[simp] theorem psmul_aget (k : ℕ) (v : IrVecN) : (k • v).aget = k * v.aget := rfl
@[simp] theorem psmul_add (k : ℕ) (v : IrVecN) : (k • v).add = k * v.add := rfl

theorem ext' {v w : IrVecN} (h₁ : v.ite = w.ite) (h₂ : v.mul = w.mul)
    (h₃ : v.loop = w.loop) (h₄ : v.copy = w.copy) (h₅ : v.const = w.const)
    (h₆ : v.skip = w.skip) (h₇ : v.aset = w.aset) (h₈ : v.aget = w.aget)
    (h₉ : v.add = w.add) : v = w := by
  cases v; cases w; simp_all

/-- Componentwise domination.  Decidable, hence `#guard`-able. -/
def Dominates (v w : IrVecN) : Prop :=
  v.ite ≤ w.ite ∧ v.mul ≤ w.mul ∧ v.loop ≤ w.loop ∧ v.copy ≤ w.copy ∧
    v.const ≤ w.const ∧ v.skip ≤ w.skip ∧ v.aset ≤ w.aset ∧ v.aget ≤ w.aget ∧
    v.add ≤ w.add

instance (v w : IrVecN) : Decidable (Dominates v w) := by
  unfold Dominates; infer_instance

/-- The vector, spent into the tower's `ECost`. -/
def toE (v : IrVecN) : ECost :=
  ACost.cost Currency.ite (v.ite : ℕ∞) + ACost.cost Currency.mul (v.mul : ℕ∞) +
    ACost.cost Currency.«while» (v.loop : ℕ∞) + ACost.cost Currency.copy (v.copy : ℕ∞) +
    ACost.cost Currency.const (v.const : ℕ∞) + ACost.cost Currency.skip (v.skip : ℕ∞) +
    ACost.cost Currency.aset (v.aset : ℕ∞) + ACost.cost Currency.aget (v.aget : ℕ∞) +
    ACost.cost Currency.add (v.add : ℕ∞)

private theorem cost_mono (c : String) {x y : ℕ∞} (h : x ≤ y) :
    ACost.cost c x ≤ ACost.cost c y := by
  refine ACost.le_def.mpr fun k => ?_
  rw [ACost.toFun_cost, ACost.toFun_cost]
  split
  · exact h
  · exact le_rfl

private theorem nsmul_cost' (c : String) (k : ℕ) (x : ℕ∞) :
    k • ACost.cost c x = ACost.cost c (k • x) := by
  refine ACost.toFun_injective (funext fun m => ?_)
  rw [ACost.toFun_nsmul, ACost.toFun_cost, ACost.toFun_cost]
  split <;> simp

theorem toE_mono {v w : IrVecN} (h : Dominates v w) : v.toE ≤ w.toE := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := h
  simp only [toE]
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_ <;>
    exact cost_mono _ (ENat.coe_le_coe.mpr (by omega))

theorem toE_add (v w : IrVecN) : (v + w).toE = v.toE + w.toE := by
  simp only [toE, padd_ite, padd_mul, padd_loop, padd_copy, padd_const, padd_skip,
    padd_aset, padd_aget, padd_add, Nat.cast_add, ← ACost.cost_add_cost]
  abel

theorem toE_smul (k : ℕ) (v : IrVecN) : (k • v).toE = k • v.toE := by
  simp only [toE, psmul_ite, psmul_mul, psmul_loop, psmul_copy, psmul_const, psmul_skip,
    psmul_aset, psmul_aget, psmul_add, Nat.cast_mul, _root_.smul_add, nsmul_cost',
    nsmul_eq_mul]

end IrVecN

/-! ## 2. What the emitted programs actually charge

Every constant below is either a landed program-pinned price or the
five-instruction cursor block `ArrayListGrow.lean` names.  Nothing is a
guess and nothing is chosen to fit. -/

/-- The in-place branch's dispatch: one branch test. -/
def arlDispatchInPlaceN : IrVecN := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The resizing branches' dispatch: two branch tests and `2 * capacity`. -/
def arlDispatchGrowN : IrVecN := ⟨2, 1, 0, 0, 0, 0, 0, 0, 0⟩

/-- The push itself plus the observable packing: `boundedExecCostN`'s success
payload — write, length bump, capacity copy, success flag, four `skip`s. -/
def arlPushPackN : IrVecN := ⟨0, 0, 0, 1, 1, 4, 1, 0, 1⟩

/-- `HeapAlloc.allocCost`: two `irUnit`s, independent of the block size. -/
def arlAllocN : IrVecN := ⟨0, 0, 0, 1, 0, 0, 0, 0, 1⟩

/-- The cursor-setup block: `si`, `di`, `dc` from the two base pointers,
`se ← sp + n`, and the literal `1` in `one` — the five straight-line
instructions `ArrayListGrow.lean` names and `arlGrowCopy_hnr` requires. -/
def arlBlitSetupN : IrVecN := ⟨0, 0, 0, 3, 1, 0, 0, 0, 1⟩

/-- `HeapCopy.blitCost n`, currency by currency (`blitCost_eq`). -/
def arlBlitN (n : ℕ) : IrVecN := ⟨0, 0, n + 1, 0, 0, 0, n, n, 2 * n⟩

/-- **What one `arlAppendTotal` really costs the machine**, branch by branch. -/
def arlAppendMachineN (s : ArrayList) : IrVecN :=
  if s.length < s.capacity then
    arlDispatchInPlaceN + arlPushPackN
  else if 2 * s.capacity ≤ s.buffer.length then
    arlDispatchGrowN + arlPushPackN
  else
    arlDispatchGrowN + arlAllocN + arlBlitSetupN + arlBlitN s.length + arlPushPackN

theorem arlAppendMachineN_space (s : ArrayList) (h : s.length < s.capacity) :
    arlAppendMachineN s = ⟨1, 0, 0, 1, 1, 4, 1, 0, 1⟩ := by
  rw [arlAppendMachineN, if_pos h]
  refine IrVecN.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [arlDispatchInPlaceN, arlPushPackN]

theorem arlAppendMachineN_double (s : ArrayList) (h₁ : ¬ s.length < s.capacity)
    (h₂ : 2 * s.capacity ≤ s.buffer.length) :
    arlAppendMachineN s = ⟨2, 1, 0, 1, 1, 4, 1, 0, 1⟩ := by
  rw [arlAppendMachineN, if_neg h₁, if_pos h₂]
  refine IrVecN.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [arlDispatchGrowN, arlPushPackN]

theorem arlAppendMachineN_grow (s : ArrayList) (h₁ : ¬ s.length < s.capacity)
    (h₂ : ¬ 2 * s.capacity ≤ s.buffer.length) :
    arlAppendMachineN s =
      ⟨2, 1, s.length + 1, 5, 2, 4, s.length + 1, s.length, 2 * s.length + 3⟩ := by
  rw [arlAppendMachineN, if_neg h₁, if_neg h₂]
  refine IrVecN.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (simp [arlDispatchGrowN, arlAllocN, arlBlitSetupN, arlBlitN, arlPushPackN]; try omega)

/-! ### The vectors are the landed prices, not new ones -/

theorem arlBlitN_toE (n : ℕ) : (arlBlitN n).toE = blitCost n := by
  rw [blitCost_eq, arlBlitN, IrVecN.toE]
  simp only [Nat.cast_zero, ACost.cost_zero]
  abel

theorem arlAllocN_toE (n : ℕ) : arlAllocN.toE = allocCost n := by
  rw [allocCost_eq, arlAllocN, IrVecN.toE]
  simp only [Nat.cast_zero, Nat.cast_one, ACost.cost_zero, irUnit]
  abel

theorem arlAppendMachineN_toE_space (s : ArrayList) (h : s.length < s.capacity) :
    (arlAppendMachineN s).toE = liftACost (boundedExecCostN s) := by
  rw [arlAppendMachineN_space s h, boundedExecCostN_space s h, IrVecN.toE]
  simp only [Nat.cast_zero, Nat.cast_one, ACost.cost_zero, liftACost_add, liftACost_cost,
    Nat.cast_ofNat]
  abel

theorem arlAppendMachineN_toE_double (s : ArrayList) (h₁ : ¬ s.length < s.capacity)
    (h₂ : 2 * s.capacity ≤ s.buffer.length) :
    (arlAppendMachineN s).toE = liftACost (boundedExecCostN s) := by
  rw [arlAppendMachineN_double s h₁ h₂, boundedExecCostN_double s h₁ h₂, IrVecN.toE]
  simp only [Nat.cast_zero, Nat.cast_one, ACost.cost_zero, liftACost_add, liftACost_cost,
    Nat.cast_ofNat]
  abel

/-- **The growth branch, assembled from the landed prices.**  Dispatch, the
allocator, the cursor block, the emitted copy loop, and the push. -/
theorem arlAppendMachineN_toE_grow (s : ArrayList) (h₁ : ¬ s.length < s.capacity)
    (h₂ : ¬ 2 * s.capacity ≤ s.buffer.length) :
    (arlAppendMachineN s).toE =
      arlDispatchGrowN.toE + allocCost (2 * s.capacity) + arlBlitSetupN.toE +
        blitCost s.length + arlPushPackN.toE := by
  rw [arlAppendMachineN, if_neg h₁, if_neg h₂, ← arlAllocN_toE (2 * s.capacity),
    ← arlBlitN_toE s.length]
  rw [IrVecN.toE_add, IrVecN.toE_add, IrVecN.toE_add, IrVecN.toE_add]

/-! ## 3. The exchange rate

Four abstract currencies, four bundles of machine currencies. -/

/-- One `dyn.control`: a branch test, the doubling multiplication, one loop
guard evaluation, two pointer/word copies, one constant, and the four `skip`s
that pack the observable tuple. -/
def dynControlUnitN : IrVecN := ⟨1, 1, 1, 2, 1, 4, 0, 0, 0⟩

/-- One `dyn.write`: the element write. -/
def dynWriteUnitN : IrVecN := ⟨0, 0, 0, 0, 0, 0, 1, 0, 0⟩

/-- One `dyn.add`: the length bump, the allocator's pointer bump, and the
copy's end cursor. -/
def dynAddUnitN : IrVecN := ⟨0, 0, 0, 0, 0, 0, 0, 0, 3⟩

/-- One `dyn.copy`: exactly one iteration of the emitted copy loop. -/
def dynCopyUnitN : IrVecN := ⟨0, 0, 1, 0, 0, 0, 1, 1, 2⟩

theorem dynCopyUnitN_toE : dynCopyUnitN.toE = blitPayload := by
  have h2 : (ACost.cost Currency.add (2 : ℕ∞) : ECost)
      = ACost.cost Currency.add 1 + ACost.cost Currency.add 1 := by
    rw [ACost.cost_add_cost]
    norm_num
  rw [dynCopyUnitN, IrVecN.toE, blitPayload]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ACost.cost_zero]
  rw [h2]
  abel

/-- **The `dyn.*` → `ir.*` exchange rate.** -/
def dynRate (k : String) : ECost :=
  if k = PushCost.controlCurrency then dynControlUnitN.toE
  else if k = PushCost.writeCurrency then dynWriteUnitN.toE
  else if k = PushCost.addCurrency then dynAddUnitN.toE
  else if k = PushCost.copyCurrency then dynCopyUnitN.toE
  else 0

@[simp] theorem dynRate_control : dynRate PushCost.controlCurrency = dynControlUnitN.toE := rfl
@[simp] theorem dynRate_write : dynRate PushCost.writeCurrency = dynWriteUnitN.toE := rfl
@[simp] theorem dynRate_add : dynRate PushCost.addCurrency = dynAddUnitN.toE := rfl
@[simp] theorem dynRate_copy : dynRate PushCost.copyCurrency = dynCopyUnitN.toE := rfl

/-- **The rate is well formed**: each machine currency is bought by at most
the four abstract ones. -/
theorem dynRate_wf : NRest.wfR'' dynRate := by
  intro f
  refine ((((Set.finite_singleton PushCost.copyCurrency).insert PushCost.addCurrency).insert
    PushCost.writeCurrency).insert PushCost.controlCurrency).subset ?_
  intro k hk
  by_contra hmem
  apply hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hmem
  simp [dynRate, h₁, h₂, h₃, h₄]

/-- The exchange, as an executable vector: `c.control` control bundles,
`c.write` writes, `c.add` add bundles, `c.copy` loop iterations. -/
def dynExchangeWithN (ctrl wr ad cp : IrVecN) (c : PushCost) : IrVecN :=
  c.control • ctrl + c.write • wr + c.add • ad + c.copy • cp

/-- The exchange at the real rate. -/
def dynExchangeN (c : PushCost) : IrVecN :=
  dynExchangeWithN dynControlUnitN dynWriteUnitN dynAddUnitN dynCopyUnitN c

private theorem timerefineA_cost_nat (R : String → ECost) (k : String) (m : ℕ) :
    NRest.timerefineA R (ACost.cost k ((m : ℕ) : ℕ∞)) = m • R k := by
  rw [NRest.timerefineA_cost]
  ext x
  simp [ACost.toFun_nsmul, nsmul_eq_mul]

/-- **The bridge**: the executable vector is literally `timerefine`'s exchange
of the abstract cost at `dynRate`. -/
theorem dynExchangeN_toE (c : PushCost) :
    NRest.timerefineA dynRate c.toECost = (dynExchangeN c).toE := by
  rw [PushCost.toECost, NRest.timerefineA_add dynRate_wf,
    NRest.timerefineA_add dynRate_wf, NRest.timerefineA_add dynRate_wf,
    timerefineA_cost_nat, timerefineA_cost_nat, timerefineA_cost_nat,
    timerefineA_cost_nat, dynRate_control, dynRate_write, dynRate_add, dynRate_copy,
    dynExchangeN, dynExchangeWithN, IrVecN.toE_add, IrVecN.toE_add, IrVecN.toE_add,
    IrVecN.toE_smul, IrVecN.toE_smul, IrVecN.toE_smul, IrVecN.toE_smul]

theorem dynExchangeN_closed (c : PushCost) :
    dynExchangeN c =
      ⟨c.control, c.control, c.control + c.copy, 2 * c.control, c.control,
       4 * c.control, c.write + c.copy, c.copy, 3 * c.add + 2 * c.copy⟩ := by
  rw [dynExchangeN, dynExchangeWithN]
  refine IrVecN.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [dynControlUnitN, dynWriteUnitN, dynAddUnitN, dynCopyUnitN] <;> omega

/-! ## 4. Falsification gates — before the proofs

Three representative states, one per branch, taken from `ArrayList.lean`'s
own compiled gates.  Each positive gate is followed by controls that reduce
exactly one component of the rate by one unit and must **fail**. -/

/-- In-place: room in the logical capacity. -/
def arlGateInPlace : ArrayList := ⟨[0, 0, 0, 0], 1, 4⟩
/-- Logical doubling: full logical capacity, spare physical buffer. -/
def arlGateDouble : ArrayList := ⟨List.replicate 8 0, 2, 2⟩
/-- Growth: physically full, so the append must allocate and copy. -/
def arlGateGrow : ArrayList := ⟨[1, 2, 3, 4], 4, 4⟩

#guard arlAppendCostN arlGateInPlace = ⟨1, 1, 1, 0⟩
#guard arlAppendCostN arlGateDouble = ⟨2, 1, 1, 0⟩
#guard arlAppendCostN arlGateGrow = ⟨4, 1, 1, 4⟩

#guard arlAppendMachineN arlGateInPlace = ⟨1, 0, 0, 1, 1, 4, 1, 0, 1⟩
#guard arlAppendMachineN arlGateDouble = ⟨2, 1, 0, 1, 1, 4, 1, 0, 1⟩
#guard arlAppendMachineN arlGateGrow = ⟨2, 1, 5, 5, 2, 4, 5, 4, 11⟩

-- The rate dominates on all three branches.
#guard IrVecN.Dominates (arlAppendMachineN arlGateInPlace)
  (dynExchangeN (arlAppendCostN arlGateInPlace))
#guard IrVecN.Dominates (arlAppendMachineN arlGateDouble)
  (dynExchangeN (arlAppendCostN arlGateDouble))
#guard IrVecN.Dominates (arlAppendMachineN arlGateGrow)
  (dynExchangeN (arlAppendCostN arlGateGrow))

/-- Shorthand for a control: exchange at a perturbed rate. -/
private def gateDom (s : ArrayList) (ctrl wr ad cp : IrVecN) : Prop :=
  IrVecN.Dominates (arlAppendMachineN s) (dynExchangeWithN ctrl wr ad cp (arlAppendCostN s))

instance (s : ArrayList) (ctrl wr ad cp : IrVecN) : Decidable (gateDom s ctrl wr ad cp) := by
  unfold gateDom; infer_instance

-- Control unit, one `ir.ite` fewer: the in-place branch's own test is unpaid.
#guard ¬ gateDom arlGateInPlace ⟨0, 1, 1, 2, 1, 4, 0, 0, 0⟩ dynWriteUnitN dynAddUnitN dynCopyUnitN
-- one `ir.mul` fewer: the doubling branch's `2 * capacity` is unpaid.
#guard ¬ gateDom arlGateDouble ⟨1, 0, 1, 2, 1, 4, 0, 0, 0⟩ dynWriteUnitN dynAddUnitN dynCopyUnitN
-- one `ir.while` fewer: the copy loop's trailing failed guard is unpaid.
#guard ¬ gateDom arlGateGrow ⟨1, 1, 0, 2, 1, 4, 0, 0, 0⟩ dynWriteUnitN dynAddUnitN dynCopyUnitN
-- one `ir.copy` fewer: allocation + cursor setup + capacity copy is unpaid.
#guard ¬ gateDom arlGateGrow ⟨1, 1, 1, 1, 1, 4, 0, 0, 0⟩ dynWriteUnitN dynAddUnitN dynCopyUnitN
-- one `ir.const` fewer: the in-place branch's success flag is unpaid.
#guard ¬ gateDom arlGateInPlace ⟨1, 1, 1, 2, 0, 4, 0, 0, 0⟩ dynWriteUnitN dynAddUnitN dynCopyUnitN
-- one `ir.skip` fewer: the observable tuple's packing is unpaid.
#guard ¬ gateDom arlGateInPlace ⟨1, 1, 1, 2, 1, 3, 0, 0, 0⟩ dynWriteUnitN dynAddUnitN dynCopyUnitN
-- `dyn.write` buying nothing: the element write is unpaid.
#guard ¬ gateDom arlGateInPlace dynControlUnitN ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ dynAddUnitN dynCopyUnitN
-- `dyn.add` buying two `ir.add` instead of three: the growth branch is one short.
#guard ¬ gateDom arlGateGrow dynControlUnitN dynWriteUnitN ⟨0, 0, 0, 0, 0, 0, 0, 0, 2⟩ dynCopyUnitN
-- `dyn.copy` without its guard test / read / write / one increment: each bites on growth.
#guard ¬ gateDom arlGateGrow dynControlUnitN dynWriteUnitN dynAddUnitN ⟨0, 0, 0, 0, 0, 0, 1, 1, 2⟩
#guard ¬ gateDom arlGateGrow dynControlUnitN dynWriteUnitN dynAddUnitN ⟨0, 0, 1, 0, 0, 0, 1, 0, 2⟩
#guard ¬ gateDom arlGateGrow dynControlUnitN dynWriteUnitN dynAddUnitN ⟨0, 0, 1, 0, 0, 0, 0, 1, 2⟩
#guard ¬ gateDom arlGateGrow dynControlUnitN dynWriteUnitN dynAddUnitN ⟨0, 0, 1, 0, 0, 0, 1, 1, 1⟩

-- The trailing guard, at symbolic length: dropping `ir.while` from the control
-- unit leaves `n` guard credits against the `n + 1` the loop evaluates.
theorem dominates_growth_no_while (s : ArrayList) (h₁ : ¬ s.length < s.capacity)
    (h₂ : ¬ 2 * s.capacity ≤ s.buffer.length) :
    ¬ gateDom s ⟨1, 1, 0, 2, 1, 4, 0, 0, 0⟩ dynWriteUnitN dynAddUnitN dynCopyUnitN := by
  rw [gateDom, arlAppendMachineN_grow s h₁ h₂,
    arlAppendCostN_of_none (by simp [boundedPushCostN, h₁, h₂])]
  simp [IrVecN.Dominates, dynExchangeWithN, dynWriteUnitN, dynAddUnitN, dynCopyUnitN]

/-- A physically full state of live length `n + 1`: the growth branch. -/
private def arlGrowAt (n : ℕ) : ArrayList := ⟨List.replicate (n + 1) 0, n + 1, n + 1⟩

-- A twenty-point size sweep of the growth branch: the rate dominates at every
-- live length, and the `ir.while`-less control unit fails at every one.
#guard (List.range 20).all fun n =>
  decide (IrVecN.Dominates (arlAppendMachineN (arlGrowAt n))
    (dynExchangeN (arlAppendCostN (arlGrowAt n))))
#guard (List.range 20).all fun n =>
  decide (¬ gateDom (arlGrowAt n) ⟨1, 1, 0, 2, 1, 4, 0, 0, 0⟩ dynWriteUnitN dynAddUnitN
    dynCopyUnitN)
#guard (List.range 20).all fun n =>
  decide (¬ gateDom (arlGrowAt n) dynControlUnitN dynWriteUnitN
    ⟨0, 0, 0, 0, 0, 0, 0, 0, 2⟩ dynCopyUnitN)

-- The exchanged growth-branch cost really covers `allocCost + blitCost` at a
-- concrete size — 4 live elements, so 4 copy credits.
#guard IrVecN.Dominates (arlAllocN + arlBlitSetupN + arlBlitN 4)
  (dynExchangeN (arlAppendCostN arlGateGrow))
-- …and one copy credit fewer does not.
#guard ¬ IrVecN.Dominates (arlAllocN + arlBlitSetupN + arlBlitN 4)
  (dynExchangeN ⟨4, 1, 1, 3⟩)

/-- The amortized step at the machine level: raw machine cost plus the new
potential against the advertised constant plus the old one. -/
private def arlIrAmortizedStep (s : ArrayList) (x : ℕ) (adv : PushCost) : Prop :=
  IrVecN.Dominates
    (arlAppendMachineN s + dynExchangeN (arlPotentialN (arlAppendTotal s x)))
    (dynExchangeN adv + dynExchangeN (arlPotentialN s))

instance (s : ArrayList) (x : ℕ) (adv : PushCost) : Decidable (arlIrAmortizedStep s x adv) := by
  unfold arlIrAmortizedStep; infer_instance

#guard arlIrAmortizedStep arlGateInPlace 7 arlAdvertisedCostN
#guard arlIrAmortizedStep arlGateDouble 5 arlAdvertisedCostN
#guard arlIrAmortizedStep arlGateGrow 9 arlAdvertisedCostN
-- The potential is load-bearing: without it the growth branch is naked.
#guard ¬ IrVecN.Dominates (arlAppendMachineN arlGateGrow) (dynExchangeN arlAdvertisedCostN)
-- One fewer advertised copy credit: the growth branch stops paying for itself.
#guard ¬ arlIrAmortizedStep arlGateGrow 9 ⟨4, 1, 1, 1⟩
-- **Not** a refutation, and the reason is the finding recorded in the header:
-- at the abstract layer `ArrayList.lean` refutes `dyn.control = 3`
-- (`¬ arlAmortizedStep ⟨[1,2,3,4],4,4⟩ 9 ⟨3,1,1,2⟩`), but after exchange three
-- control units already buy `6 ≥ 5` `ir.copy`, so `4` is sound-but-slack.
#guard arlIrAmortizedStep arlGateGrow 9 ⟨3, 1, 1, 2⟩
-- Two, however, do not: `2 * 2 = 4 < 5` copies on the growth branch.
#guard ¬ arlIrAmortizedStep arlGateGrow 9 ⟨2, 1, 1, 2⟩

/-! ## 5. Domination, on every branch -/

/-- **The exchange dominates the machine.**  On the in-place branch, on the
logical-doubling branch, and on the allocating-and-copying growth branch. -/
theorem arlAppendMachineN_dominated (s : ArrayList) :
    IrVecN.Dominates (arlAppendMachineN s) (dynExchangeN (arlAppendCostN s)) := by
  by_cases h₁ : s.length < s.capacity
  · rw [arlAppendMachineN_space s h₁,
      arlAppendCostN_of_some (c := ⟨1, 1, 1, 0⟩) (by simp [boundedPushCostN, h₁]),
      dynExchangeN_closed]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · by_cases h₂ : 2 * s.capacity ≤ s.buffer.length
    · rw [arlAppendMachineN_double s h₁ h₂,
        arlAppendCostN_of_some (c := ⟨2, 1, 1, 0⟩) (by simp [boundedPushCostN, h₁, h₂]),
        dynExchangeN_closed]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
    · rw [arlAppendMachineN_grow s h₁ h₂,
        arlAppendCostN_of_none (by simp [boundedPushCostN, h₁, h₂]), dynExchangeN_closed]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp; try omega)

/-- The raw branch cost, in machine currencies. -/
def arlIrAppendCost (s : ArrayList) : ECost := (dynExchangeN (arlAppendCostN s)).toE

/-- The doubling potential, in machine currencies. -/
def arlIrPotential (s : ArrayList) : ECost := (dynExchangeN (arlPotentialN s)).toE

/-- The advertised amortized price, in machine currencies.  A closed term:
**no length, no capacity**. -/
def arlIrAdvertisedCost : ECost := (dynExchangeN arlAdvertisedCostN).toE

/-- These are `timerefine`'s exchange, not a parallel account. -/
theorem arlIrAppendCost_eq_timerefine (s : ArrayList) :
    arlIrAppendCost s = NRest.timerefineA dynRate (arlAppendCostN s).toECost :=
  (dynExchangeN_toE _).symm

theorem arlIrPotential_eq_timerefine (s : ArrayList) :
    arlIrPotential s = NRest.timerefineA dynRate (arlPotentialN s).toECost :=
  (dynExchangeN_toE _).symm

theorem arlIrAdvertisedCost_eq_timerefine :
    arlIrAdvertisedCost = NRest.timerefineA dynRate arlAdvertisedCostN.toECost :=
  (dynExchangeN_toE _).symm

/-- **The exchange dominates the machine, in the tower's `ECost`.** -/
theorem arlAppendMachineCost_le_exchange (s : ArrayList) :
    (arlAppendMachineN s).toE ≤ arlIrAppendCost s :=
  IrVecN.toE_mono (arlAppendMachineN_dominated s)

/-- **The growth branch's four control units really do buy the allocator and
the copy.**  Everything the growth step pays beyond the abstract account's
element-wise copy credits — allocation, cursor setup, dispatch, packing — is
covered. -/
theorem arlGrowth_covers_alloc_and_blit (s : ArrayList) (h₁ : ¬ s.length < s.capacity)
    (h₂ : ¬ 2 * s.capacity ≤ s.buffer.length) :
    arlDispatchGrowN.toE + allocCost (2 * s.capacity) + arlBlitSetupN.toE +
        blitCost s.length + arlPushPackN.toE ≤ arlIrAppendCost s := by
  rw [← arlAppendMachineN_toE_grow s h₁ h₂]
  exact arlAppendMachineCost_le_exchange s

/-! ## 6. The cashed amortized headline -/

/-- The advertised price, spelled out.  Fifty-four machine operations per
push, amortized, and every one of them a currency the endorsed IR charges. -/
theorem arlIrAdvertisedCost_vector :
    arlIrAdvertisedCost = (⟨4, 4, 6, 8, 4, 16, 3, 2, 7⟩ : IrVecN).toE := by
  rw [arlIrAdvertisedCost, dynExchangeN_closed]
  rfl

theorem arlIrAdvertisedCost_ite : arlIrAdvertisedCost.toFun Currency.ite = 4 := by
  rw [arlIrAdvertisedCost_vector, IrVecN.toE]
  simp [Currency.ite, Currency.mul, Currency.«while», Currency.copy, Currency.const,
    Currency.skip, Currency.aset, Currency.aget, Currency.add]

theorem arlIrAdvertisedCost_while : arlIrAdvertisedCost.toFun Currency.«while» = 6 := by
  rw [arlIrAdvertisedCost_vector, IrVecN.toE]
  simp [Currency.ite, Currency.mul, Currency.«while», Currency.copy, Currency.const,
    Currency.skip, Currency.aset, Currency.aget, Currency.add]

theorem arlIrAdvertisedCost_aget : arlIrAdvertisedCost.toFun Currency.aget = 2 := by
  rw [arlIrAdvertisedCost_vector, IrVecN.toE]
  simp [Currency.ite, Currency.mul, Currency.«while», Currency.copy, Currency.const,
    Currency.skip, Currency.aset, Currency.aget, Currency.add]

theorem arlIrAdvertisedCost_add : arlIrAdvertisedCost.toFun Currency.add = 7 := by
  rw [arlIrAdvertisedCost_vector, IrVecN.toE]
  simp [Currency.ite, Currency.mul, Currency.«while», Currency.copy, Currency.const,
    Currency.skip, Currency.aset, Currency.aget, Currency.add]

/-- **Amortized O(1) append, in IR currencies.**  The exchange of
`ArrayList.lean`'s abstract bound, currency by currency, at a rate that is
well formed and that dominates the emitted programs. -/
theorem arlAppend_amortized_ir (s : ArrayList) (x : ℕ) (h : s.Wf) :
    arlIrAppendCost s + arlIrPotential (arlAppendTotal s x) ≤
      arlIrAdvertisedCost + arlIrPotential s := by
  have h₁ := NRest.timerefineA_mono dynRate_wf (arlAppend_amortized_cost s x h)
  rw [NRest.timerefineA_add dynRate_wf, NRest.timerefineA_add dynRate_wf] at h₁
  rw [arlIrAppendCost, arlIrPotential, arlIrPotential, arlIrAdvertisedCost,
    ← dynExchangeN_toE, ← dynExchangeN_toE, ← dynExchangeN_toE, ← dynExchangeN_toE]
  simpa [arlAppendRawCost, arlPotential, arlAdvertisedCost] using h₁

/-- **The headline, cashed.**  What the *machine* pays for one append, plus
the new potential, is at most a constant plus the old potential — and the
constant is `arlIrAdvertisedCost`, a closed vector of IR currencies that
mentions neither the length nor the capacity. -/
theorem arlAppendMachine_amortized_ir (s : ArrayList) (x : ℕ) (h : s.Wf) :
    (arlAppendMachineN s).toE + arlIrPotential (arlAppendTotal s x) ≤
      arlIrAdvertisedCost + arlIrPotential s :=
  le_trans (add_le_add (arlAppendMachineCost_le_exchange s) (le_refl _))
    (arlAppend_amortized_ir s x h)

/-! ### …and at the `NRest` level -/

/-- The machine's deterministic append: the state transition at the price the
branch really costs, in IR currencies. -/
noncomputable def arlAppendMachineRaw (s : ArrayList) (x : ℕ) : NRest ArrayList ECost :=
  NRest.consume (NRest.returnT (arlAppendTotal s x)) (arlAppendMachineN s).toE

/-- Constant-price public append, in IR currencies. -/
noncomputable def arlIrAppendPublicSpec (s : ArrayList) (x : ℕ) : NRest ArrayList ECost :=
  NRest.consume (NRest.returnT (arlAppendTotal s x)) arlIrAdvertisedCost

noncomputable def arlIrAppendAmortized (s : ArrayList) (x : ℕ) : NRest ArrayList ECost :=
  NRest.reclaim (NRest.consume (arlIrAppendPublicSpec s x) (arlIrPotential s)) arlIrPotential

private theorem consume_returnT_eq_spec'' {α : Type} (y : α) (c : ECost) :
    NRest.consume (NRest.returnT y) c =
      NRest.spec (fun z => z = y) (fun _ => c) := by
  rw [NRest.consume_returnT, NRest.spec, NRest.rest_inj_iff]
  funext z
  by_cases hz : z = y
  · subst z
    simp
  · simp [hz]

/-- **The exported cashed statement.**  The machine-priced append refines the
constant-price one after the post-potential is reclaimed — the same shape as
`arlAppendRaw_le_amortized`, but every currency is one the endorsed IR
charges. -/
theorem arlAppendMachineRaw_le_amortized (s : ArrayList) (x : ℕ) (h : s.Wf) :
    arlAppendMachineRaw s x ≤ arlIrAppendAmortized s x := by
  unfold arlAppendMachineRaw arlIrAppendAmortized arlIrAppendPublicSpec
  rw [NRest.consume_consume, consume_returnT_eq_spec'', consume_returnT_eq_spec'']
  apply le_trans (b := NRest.spec (fun y => y = arlAppendTotal s x)
      (fun y => (arlIrPotential s + arlIrAdvertisedCost) -ᵣ arlIrPotential y))
  · rw [NRest.spec, NRest.spec, NRest.rest_le_rest_iff]
    intro y
    by_cases hy : y = arlAppendTotal s x
    · subst y
      simp only [ite_true, WithBot.coe_le_coe]
      apply Needname.le_diff_if_add_le
      · have hc := arlAppendMachine_amortized_ir s x h
        simpa [add_comm] using hc
      · apply Needname.add_leD2 ((arlAppendMachineN s).toE)
          (arlIrPotential (arlAppendTotal s x))
        simpa [add_comm] using arlAppendMachine_amortized_ir s x h
    · simp [hy]
  · exact NRest.reclaim_spec_le

/-! ## 7. The append guarantee is unchanged

Cashing the cost restates nothing about the refinement.  This is the landed
rule, re-checked as a compiled term: no precondition, `arrayListRel` on both
sides, and no `arrayListReadyRel` anywhere. -/

theorem arlAppendOp_refines_unchanged :
    (arlAppendOp, op_list_append ℕ) ∈
      fref (fun _ : List ℕ => True) arrayListRel
        (fun _ => Set.diagonal ℕ →ᵣ NRest.nrestRel arrayListRel) :=
  arlAppendOp_refines

/-! ## 8. Axiom gates -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.dynRate_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dynRate_wf

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppendMachineN_dominated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlAppendMachineN_dominated

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppendMachineCost_le_exchange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms arlAppendMachineCost_le_exchange

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowth_covers_alloc_and_blit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms arlGrowth_covers_alloc_and_blit

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppend_amortized_ir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlAppend_amortized_ir

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppendMachine_amortized_ir' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms arlAppendMachine_amortized_ir

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppendMachineRaw_le_amortized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms arlAppendMachineRaw_le_amortized

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppendOp_refines_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms arlAppendOp_refines_unchanged

end Lax13Proofs.Refine.Sepref.Iicf
