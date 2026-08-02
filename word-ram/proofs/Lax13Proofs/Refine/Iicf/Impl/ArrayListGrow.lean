import Lax13Proofs.Refine.Iicf.Impl.ArrayList
import Lax13Proofs.Refine.Sepref.HeapAlloc

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
unconditional, `n`-independent-cost allocator — followed by an
`s.length`-element copy into the fresh block.  `arlGrowSpec_eq` shows its
value is exactly `ArrayList.lean`'s `arlGrow s`, and its price exactly
`allocCost (2 * cap) + arlCopyCost s.length`.

The element-wise copy is priced but **not synthesized**: its IR realization is
a bounded `while` over two heap ranges, and no such loop rule is landed yet.
So this file's honest claim is: the *allocation* half of growth is a landed
registered rule (`hnr_mop_alloc`), and the *copy* half is a specification with
its exact price — `s.length` heap reads and `s.length` heap writes — folded
into the amortized statement, never into a constant.  Recorded as the leaf's
one open item; it does not affect any statement in `ArrayList.lean`, all of
which are about values and prices rather than commands.

## Registration default (ledger E29)

`sepref_fr_rules` gains **nothing** from this file.  The array-list family's
registered executable rules stay exactly the seven nonallocating commands plus
P4's in-place `arlAppend_exec_hnr`; the allocating growth path is reachable
only by explicitly naming `arlGrowSpec`.  That is deliberate and it is the
conservative direction of E29's discipline: synthesis cannot silently place an
allocation inside a loop, because there is no registered rule for it to pick.
The allocating *value-level* rule `arlAppendOp_refines` **is** the
`sepref_fref_thms` default, which is the right default for append — append is
the growing operation, and the abstract layer is where the source states it
unconditionally.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## The copy -/

/-- Copy the first `n` cells of `src` over `dst`: the source's `array_copy`
at the growth step.  `dst` is the freshly allocated block. -/
def arlBlit (dst src : List ℕ) (n : ℕ) : List ℕ := src.take n ++ dst.drop n

@[simp] theorem arlBlit_length (dst src : List ℕ) (n : ℕ) (h : n ≤ src.length) :
    (arlBlit dst src n).length = n + (dst.length - n) := by
  simp [arlBlit, Nat.min_eq_left h]

/-- Copying `n` cells into a fresh zero block gives the active prefix followed
by the allocator's zeros — which is `arlGrow`'s buffer, on the nose. -/
theorem arlBlit_replicate (src : List ℕ) (n k : ℕ) :
    arlBlit (List.replicate k 0) src n = src.take n ++ List.replicate (k - n) 0 := by
  simp [arlBlit, List.drop_replicate]

/-- The copy's exact price: one heap read and one heap write per live element.
`O(n)`, stated as `O(n)`.  It is paid for in `ArrayList.lean`'s
`arlAppendCostN`, whose growth branch carries `s.length` copy credits. -/
noncomputable def arlCopyCost (n : ℕ) : ECost :=
  n • (irUnit Currency.aget + irUnit Currency.aset)

theorem arlCopyCost_zero : arlCopyCost 0 = 0 := by simp [arlCopyCost]

/-- The copy is not free, and its price is linear — the fact that makes the
amortized statement in `ArrayList.lean` the only honest headline. -/
theorem arlCopyCost_succ (n : ℕ) :
    arlCopyCost (n + 1) = arlCopyCost n + (irUnit Currency.aget + irUnit Currency.aset) := by
  simp [arlCopyCost, succ_nsmul]
  abel

/-! ## The growth program -/

/-- **Growth, on the landed allocator.**  `mopAlloc (2 * cap)` hands back a
fresh zeroed block of twice the capacity at `allocCost`, which is two `irUnit`s
and independent of the block size (`allocCost_const`).  Then the live prefix is
copied in.  There is no `assert` anywhere: `mopAlloc` has none
(`mopAlloc_nofail`), which is exactly the property that lets append be
restated unconditionally. -/
noncomputable def arlGrowSpec (s : ArrayList) : NRest ArrayList ECost :=
  NRest.bindT (mopAlloc (2 * s.capacity)) fun blk =>
    NRest.consume
      (NRest.returnT (⟨arlBlit blk s.buffer s.length, s.length, 2 * s.capacity⟩ : ArrayList))
      (arlCopyCost s.length)

/-- **The growth program computes `arlGrow`.**  This is what makes
`ArrayList.lean`'s growth branch a derived state rather than a postulate: the
buffer `arlGrow` names is literally what the allocator returns after the copy,
and the price is the allocator's plus the copy's. -/
theorem arlGrowSpec_eq (s : ArrayList) (h : s.Wf) :
    arlGrowSpec s =
      NRest.consume (NRest.returnT (arlGrow s))
        (allocCost (2 * s.capacity) + arlCopyCost s.length) := by
  have hactive : s.buffer.take s.length = s.active := rfl
  have hstate : (⟨arlBlit (List.replicate (2 * s.capacity) 0) s.buffer s.length,
      s.length, 2 * s.capacity⟩ : ArrayList) = arlGrow s := by
    rw [arlBlit_replicate, hactive]
    rfl
  rw [arlGrowSpec, mopAlloc_def, Lax13Proofs.Refine.Iicf.bindT_unit, hstate,
    NRest.consume_consume]

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

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowSpec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowSpec_eq

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowAlloc_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowAlloc_hnr

end Lax13Proofs.Refine.Sepref.Iicf
