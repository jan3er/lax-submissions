import Lax13Proofs.Refine.Iicf.Impl.ArrayList
import Lax13Proofs.Refine.Sepref.HeapAlloc
import Lax13Proofs.Refine.Sepref.HeapCopy

/-!
# The array list's growth step, on the P4.5 allocator

Leaf **P5.E**, satellite of `ArrayList.lean`.  `ArrayList.lean` states the
re-seated append and its amortized price; this file exhibits the growth branch
as an actual program over A.2's allocator, so that `arlGrow` is a *derived*
state rather than a postulated one.

Source: `IICF_Array_List.thy` @ `c1c987b`, `arl_append` at `:30–42` — when the
physical array is full, `array_grow a (2 * len) default`, copy, then write.

The file is separate from `ArrayList.lean` on purpose.  Importing
`Sepref/HeapAlloc.lean` there would put `hnr_mop_alloc`, `hnr_mop_allocRaw`
and `hnr_mop_free` into the `sepref_fr_rules` database *before* that file's
seven `sepref_synth` invocations run, and P5.E has no business perturbing the
seven landed nonallocating commands.  Nothing here is needed to state the
re-seated guarantee; it is needed to justify it.

## What is proved here, and what is not

`arlGrowSpec` is the growth program: `mopAlloc (2 * cap)` — the landed,
unconditional, `n`-independent-cost allocator — followed by `mopBlit`, the
`s.length`-element copy into the fresh block.  `arlGrowSpec_eq` shows its
value is exactly `ArrayList.lean`'s `arlGrow s`, and its price exactly
`allocCost (2 * cap) + arlCopyCost s.length`.

**Both halves are now landed registered rules.**  The allocation is A.2's
`hnr_mop_alloc`; the copy is A.4's `hnr_mop_blit`
(`Sepref/HeapCopy.lean`), whose IR realization is the bounded `while` over two
`↦ₕ` ranges that the P5.E re-seat named as its one open item (ledger E34).
`arlGrowAlloc_hnr` and `arlGrowCopy_hnr` instantiate them at the growth block.

**The correction that landing the loop forced (ledger E34/F11).**  Before the
loop existed, `arlCopyCost n` was `n • (ir.aget + ir.aset)`.  That is
*understated*: the emitted loop also evaluates its guard `n + 1` times and
bumps two cursors per iteration, so its real price is `blitCost n`, i.e.
`(n+1)·ir.while + n·ir.aget + n·ir.aset + 2n·ir.add`.  This is F11's failure
class for the third time — the cost function nobody consumed was the cost
function nobody checked.  `arlCopyCost` is now *defined* to be `blitCost`, so
it cannot drift from the program again, and in particular `arlCopyCost 0` is
**not** `0`: an empty copy still pays its one failed guard test.

The correction moves no statement in `ArrayList.lean`.  That is not luck and
it is not a currency collision being papered over: `arlAppendCostN` and the
amortized theorems above it are stated in `PushCost`'s four *abstract*
currencies (`dyn.control`, `dyn.write`, `dyn.add`, `dyn.copy`), while
`arlCopyCost` is in the IR's own currencies; the two accounts are related by
prose, not by a theorem, and only the IR-side one is corrected here.  What
remains true either way is the shape: one copy credit per live element, so
`⟨4, 1, 1, s.length⟩` on the growth branch and amortized `O(1)` over the
doubling potential, unchanged.

## Where the composition lives

Growth is two registered rules and an exact price *here*; the **cursor-setup
block** that composes them — `si` and `se` from the live block's base, `di`
and `dc` from `mopAlloc`'s result cell, and the literal `1` in `one`, five
straight-line instructions at constant cost and no loop — is landed in the
satellite `ArrayListGrowSynth.lean`, together with the composition that makes
growth **one synthesized IR command** (`arlGrowSynth_impl`, and
`arlGrowPushSynth_impl` with the element write).  That file also checks the
setup block's price against `ArrayListCash.lean`'s prediction `arlBlitSetupN`,
by an equation and by running the emitted program.

It is a separate file for the same reason this one is separate from
`ArrayList.lean`: its two composed rules go into `sepref_fr_rules`, and the
seven landed nonallocating commands must be synthesized before they do.

What that still does **not** close is end-to-end synthesis of
`arlAppendTotal`, and the obstacle is representational rather than
combinatorial: `ArrayList.lean` holds the buffer as a named IR array
(`arrayAssn`), while the allocator and the copy loop work on heap ranges
(`↦ₕ`), and no bridge between the two is landed.  That is named there rather
than softened.

## Registration default (ledger E29)

`sepref_fr_rules` gains nothing *from this file*; what it gains from A.4 is
`hnr_mop_blit`, and that is deliberate.  A copy loop is loop-interior by
nature, so E29's warning applies — but `blitProg` is closed and
**allocation-free** (`blitProg_pinned` pins the emitted term: a `while` over
`aget`/`aset`/`add`, no `hpName`, no `allocProg`), so synthesis cannot use it
to place an allocation inside a loop.  The array-list family's registered
executable rules stay exactly the seven nonallocating commands plus P4's
in-place `arlAppend_exec_hnr`; the *allocating* growth path is still reachable
only by explicitly naming `arlGrowSpec`.  The allocating *value-level* rule
`arlAppendOp_refines` **is** the `sepref_fref_thms` default, which is the
right default for append — append is the growing operation, and the abstract
layer is where the source states it unconditionally.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## The copy -/

/-- Copy the first `n` cells of `src` over `dst`: the source's `array_copy`
at the growth step.  `dst` is the freshly allocated block.  This is A.4's
`hblit`, which is what the landed copy loop computes — the same definition,
kept under this name because `ArrayList.lean` and the gates below quote it. -/
def arlBlit (dst src : List ℕ) (n : ℕ) : List ℕ := hblit dst src n

theorem arlBlit_eq_hblit (dst src : List ℕ) (n : ℕ) : arlBlit dst src n = hblit dst src n :=
  rfl

@[simp] theorem arlBlit_length (dst src : List ℕ) (n : ℕ) (h : n ≤ src.length) :
    (arlBlit dst src n).length = n + (dst.length - n) := by
  simp [arlBlit, hblit, Nat.min_eq_left h]

/-- Copying `n` cells into a fresh zero block gives the active prefix followed
by the allocator's zeros — which is `arlGrow`'s buffer, on the nose. -/
theorem arlBlit_replicate (src : List ℕ) (n k : ℕ) :
    arlBlit (List.replicate k 0) src n = src.take n ++ List.replicate (k - n) 0 :=
  hblit_replicate src n k

/-- **The copy's exact price — the emitted loop's, not a guess.**  A.4's
`blitCost`: `(n+1)·ir.while + n·ir.aget + n·ir.aset + 2n·ir.add`
(`blitCost_eq`), which is what `blitProg` actually charges (`BlitGate`'s
pinned cost vector).  Defining it *as* `blitCost` is what stops it drifting
from the program again.

The earlier reading of this constant — `n • (ir.aget + ir.aset)` — omitted the
guard evaluations and the two cursor increments, exactly as
`implHeapSwimCost` / `implHeapSinkCost` omitted their bodies' `ir.skip`
(ledger F11). -/
noncomputable def arlCopyCost (n : ℕ) : ECost := blitCost n

theorem arlCopyCost_eq_blitCost (n : ℕ) : arlCopyCost n = blitCost n := rfl

/-- **The empty copy is not free.**  `arlCopyCost 0` is one `ir.while`, the
single failed guard test — *not* `0`, which is what this theorem said before
the loop existed. -/
theorem arlCopyCost_zero : arlCopyCost 0 = irUnit Currency.«while» := blitCost_zero

theorem arlCopyCost_zero_ne_zero : arlCopyCost 0 ≠ 0 := blitCost_zero_ne_zero

/-- The copy is not free, and its price is linear — the fact that makes the
amortized statement in `ArrayList.lean` the only honest headline. -/
theorem arlCopyCost_succ (n : ℕ) : arlCopyCost (n + 1) = arlCopyCost n + blitPayload :=
  blitCost_succ n

/-- …and the credit vector, spelled out. -/
theorem arlCopyCost_vector (n : ℕ) :
    arlCopyCost n =
      ACost.cost Currency.«while» ((n + 1 : ℕ) : ℕ∞) +
        (ACost.cost Currency.aget ((n : ℕ) : ℕ∞) +
          (ACost.cost Currency.aset ((n : ℕ) : ℕ∞) +
            ACost.cost Currency.add ((2 * n : ℕ) : ℕ∞))) := blitCost_eq n

/-! ## The growth program -/

/-- **Growth, on the landed allocator.**  `mopAlloc (2 * cap)` hands back a
fresh zeroed block of twice the capacity at `allocCost`, which is two `irUnit`s
and independent of the block size (`allocCost_const`).  Then the live prefix is
copied in.  There is no `assert` anywhere: `mopAlloc` has none
(`mopAlloc_nofail`), which is exactly the property that lets append be
restated unconditionally. -/
noncomputable def arlGrowSpec (s : ArrayList) : NRest ArrayList ECost :=
  NRest.bindT (mopAlloc (2 * s.capacity)) fun blk =>
    NRest.bindT (mopBlit blk s.buffer s.length) fun buf =>
      NRest.returnT (⟨buf, s.length, 2 * s.capacity⟩ : ArrayList)

/-- **The growth program computes `arlGrow`.**  This is what makes
`ArrayList.lean`'s growth branch a derived state rather than a postulate: the
buffer `arlGrow` names is literally what the allocator returns after the copy,
and the price is the allocator's plus the copy's. -/
theorem arlGrowSpec_eq (s : ArrayList) (h : s.Wf) :
    arlGrowSpec s =
      NRest.consume (NRest.returnT (arlGrow s))
        (allocCost (2 * s.capacity) + arlCopyCost s.length) := by
  have hactive : s.buffer.take s.length = s.active := rfl
  have hstate : (⟨hblit (List.replicate (2 * s.capacity) 0) s.buffer s.length,
      s.length, 2 * s.capacity⟩ : ArrayList) = arlGrow s := by
    rw [hblit_replicate, hactive]
    rfl
  rw [arlGrowSpec, mopAlloc_def, Lax13Proofs.Refine.Iicf.bindT_unit, mopBlit_def,
    Lax13Proofs.Refine.Iicf.bindT_unit, hstate, NRest.consume_consume,
    arlCopyCost_eq_blitCost]

/-- Growth never fails.  The whole point. -/
theorem arlGrowSpec_nofail (s : ArrayList) (h : s.Wf) : (arlGrowSpec s).nofailT := by
  rw [arlGrowSpec_eq s h]
  exact nofailT_consume_iff.2 (NRest.nofailT_returnT _)

/-- The allocation half of growth is a *registered* rule, not a new axiom: it
is A.2's `hnr_mop_alloc` at the growth block size, in the shape
`sepref_synth` consumes.  Instantiating it here is the compiled check that the
growth step's allocation is reachable from the landed rule database. -/
theorem arlGrowAlloc_hnr (pc nc : String) (hp k : ℕ) (s : ArrayList) :
    hnRefine (junkCell pc ∗ avail hp (2 * s.capacity + k) ∗
        hnCtxt natAssn (2 * s.capacity) nc)
      (allocProg pc nc)
      (avail (hp + 2 * s.capacity) k ∗ hnCtxt natAssn (2 * s.capacity) nc)
      pc heapBlockAssn (mopAlloc (2 * s.capacity)) :=
  hnr_mop_alloc pc nc hp (2 * s.capacity) k

/-- **The copy half of growth is a registered rule too** — the item ledger E34
left open.  This is A.4's `hnr_mop_blit` at the growth step: the live prefix
`s.buffer` at base `sp`, the fresh block at base `dp`, `s.length` elements.
Both bound hypotheses come straight out of `s.Wf` (`length ≤ capacity ≤
buffer.length`, and `capacity ≤ 2 * capacity`), so the caller supplies
nothing the array list does not already know.

The concrete command is `blitProg`, a `while` over `heapName` — an actual IR
program, not a specification, which is what makes `arlGrow` a derived state
all the way down. -/
theorem arlGrowCopy_hnr (t si di se one dc : String) (sp dp : ℕ) (s : ArrayList)
    (h : s.Wf) :
    hnRefine
      (junkCell t ∗ (si ↦ᵥ sp) ∗ (di ↦ᵥ dp) ∗ (se ↦ᵥ (sp + s.length)) ∗ (one ↦ᵥ 1) ∗
        (sp ↦ₕ s.buffer) ∗ (dc ↦ᵥ dp) ∗ (dp ↦ₕ List.replicate (2 * s.capacity) 0))
      (blitProg t si di se one)
      (junkCell t ∗ (si ↦ᵥ (sp + s.length)) ∗ (di ↦ᵥ (dp + s.length)) ∗
        (se ↦ᵥ (sp + s.length)) ∗ (one ↦ᵥ 1) ∗ (sp ↦ₕ s.buffer))
      dc heapBlockAssn
      (mopBlit (List.replicate (2 * s.capacity) 0) s.buffer s.length) := by
  obtain ⟨-, hlc, hcb⟩ := h
  exact hnr_mop_blit t si di se one dc sp dp s.length s.buffer
    (List.replicate (2 * s.capacity) 0) (by omega) (by simpa using by omega)

/-- …and what that copy hands back is exactly `arlGrow`'s buffer. -/
theorem arlGrowCopy_value (s : ArrayList) :
    hblit (List.replicate (2 * s.capacity) 0) s.buffer s.length = (arlGrow s).buffer := by
  rw [hblit_replicate]
  rfl

/-! ## The LIFO leak, at the program level

`free` is LIFO: its precondition is ownership of the block *together with* the
availability that starts at the block's end (`free_triple`), and
`free_nontop_false` compiles the converse — a block with anything live above it
cannot be freed at all.  `arlGrowSpec` allocates the doubled block above the
live one, so after the copy the old block is not on top and is unreclaimable.

That is stated, not hidden.  What makes it tolerable under ledger E29 is
`ArrayList.lean`'s `arlAllocatedMany_live_bounded`: the sum of every leaked
block over a whole run of appends is at most `4 ×` the final live length. -/

/-- The superseded block is exactly the one the leak bound accounts for: an
append that grows claims `2 * capacity` fresh cells and gives none back. -/
theorem arlGrow_claims (s : ArrayList) (x : ℕ) (h : boundedPush s x = none) :
    arlAllocatedBy s x = 2 * s.capacity := by
  simp [arlAllocatedBy, h]

/-! ## Gates -/

-- The blit really is a copy: the live prefix survives, the rest is zeros.
#guard arlBlit (List.replicate 8 0) [1, 2, 3, 4] 4 = [1, 2, 3, 4, 0, 0, 0, 0]
#guard arlBlit (List.replicate 8 0) [1, 2, 3, 4] 0 = List.replicate 8 0
-- …and the growth-branch state of `ArrayList.lean` is what the blit builds.
#guard (⟨arlBlit (List.replicate 8 0) [1, 2, 3, 4] 4, 4, 8⟩ : ArrayList) =
  arlGrow ⟨[1, 2, 3, 4], 4, 4⟩
-- negative control: blitting the wrong count does NOT reproduce `arlGrow`.
#guard (⟨arlBlit (List.replicate 8 0) [1, 2, 3, 4] 3, 4, 8⟩ : ArrayList) ≠
  arlGrow ⟨[1, 2, 3, 4], 4, 4⟩

/-- **The cost correction, currency by currency.**  The old constant said an
`n`-element copy pays `n` reads, `n` writes and nothing else; the emitted loop
pays `n + 1` guard evaluations and `2n` increments too. -/
theorem arlCopyCost_components (n : ℕ) :
    (arlCopyCost n).toFun Currency.aget = (n : ℕ∞) ∧
      (arlCopyCost n).toFun Currency.aset = (n : ℕ∞) ∧
      (arlCopyCost n).toFun Currency.«while» = ((n + 1 : ℕ) : ℕ∞) ∧
      (arlCopyCost n).toFun Currency.add = ((2 * n : ℕ) : ℕ∞) := by
  rw [arlCopyCost_vector]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Currency.aget, Currency.aset, Currency.«while», Currency.add]

/-- …and the empty copy is not free: one `ir.while`, not nothing. -/
theorem arlCopyCost_zero_while : (arlCopyCost 0).toFun Currency.«while» = 1 := by
  rw [arlCopyCost_zero]
  simp [irUnit]

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowSpec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowSpec_eq

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowAlloc_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowAlloc_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowCopy_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowCopy_hnr

end Lax13Proofs.Refine.Sepref.Iicf
