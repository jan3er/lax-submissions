import Lax13Proofs.Refine.Iicf.Impl.ArrayListCash

/-!
# The cursor-setup block, and growth as one synthesized command

Leaf **P4.5.A.6**, the last named gap of the P5.E re-seat (ledger **E35**).
`ArrayListGrow.lean` left growth as *two registered rules and an exact price,
but not one synthesized command*, and named what was missing: a
**cursor-setup block** — `si`/`se` from the live block's base, `di`/`dc` from
`mopAlloc`'s result cell, and the literal `1` in `one` — five straight-line
instructions at constant cost, plus the composition that threads them.  This
file lands the block, closes the chain, and drives the whole thing through
`sepref_synth`.

## The emitted command

```
pc := $hp ; $hp := $hp + nc            -- allocProg  (A.2, registered)
si := sc                               -- ┐
se := sc + lc                          -- │ the cursor-setup block:
one := 1                               -- │ five straight-line instructions,
di := pc                               -- │ constant cost, no loop
dc := pc                               -- ┘
while si < se do { t := heap[si]; heap[di] := t; si += one; di += one }
heap[di] := xc                         -- the element write (push form only)
```

`arlGrowSynth_impl` is the first seven instructions plus the loop;
`arlGrowPushSynth_impl` adds the element write, and is the growth *branch* of
`arl_append` — its value is `arlPushGrown`'s buffer, checked by execution
against the pure model in `§ GrowGate`.

## Why the setup block sits *after* the allocation, and in one rule

The obvious shape — synthesize `si := sc`, `se := sc + lc`, `one := 1` as
three separate `mopCopy` / `mopBinop` / `mopConstN` steps and then apply
`hnr_mop_blit` — **does not compose, and the failure is structural rather
than tactical.**  `hnr_seq`'s continuation premise is `∀ a, returnT a ≤ m →
hnRefine (hnCtxt Rh a x ∗ Γ₁) …`: the value a synthesized step leaves in its
destination cell is *universally quantified*, so downstream the context says
only "`one` holds something", never "`one` holds `1`".  `hnr_mop_blit`
genuinely needs `si ↦ᵥ sp`, `se ↦ᵥ sp + n` and `one ↦ᵥ 1`, and no frame
inference can recover those from an opaque binder.  That is why every landed
consumer in this tower (`rowEndSynth`, `arlButlastSynth`, `arlLastSynth`)
takes its `one` cell as a *caller-supplied* `hnCtxt natAssn 1 one` rather
than synthesizing it.

The same wall stands in front of the allocation: `mopAlloc`'s result is
`heapBlockAssn (List.replicate n 0) pc = ∃ᵃ p, (pc ↦ᵥ p) ∗ (p ↦ₕ …)`, so the
fresh block's base pointer exists only under an existential, and `di := pc`,
`dc := pc` and the loop's `dp ↦ₕ zs` all mention it.  A rule that leaves the
block's ownership *surviving* the binder cannot be composed at all — the
synthesizer says so in as many words ("there is no junk form for its
assertion — the postcondition cannot be closed over the binder").

Both are answered the same way, and it is the source's own discipline: the
block is **one rule**.  `hnr_mop_growBlock` takes the six scratch cells as
`junkCell`s, the two live values as `hnCtxt`s and the fresh block as a whole
`hnCtxt heapBlockAssn zs pc`, eliminates the existential *inside* the rule
(`hnr_pre_ex_conv`'s triple-level twin `irHtriple_sepEx'`), and hands the
block back at `dc`.  The existential never escapes and no synthesized value
is ever constrained downstream.  What remains for `sepref_synth` is exactly
two steps — allocate, then the block — and it finds both.

## The prediction check (ledger F11's failure class, fourth appearance)

`ArrayListCash.lean`'s `arlBlitSetupN = ⟨copy 3, const 1, add 1⟩` was written
from a *description* of this block, hours before the block existed.  It is
checked here, not assumed, and in two independent ways:

* `arlBlitSetupN_toE : arlBlitSetupN.toE = arlSetupCost` — the vector equals
  the price the composed triple actually pays;
* `#guard growRunVec growDemoOut.2 = arlAllocN + arlBlitSetupN + arlBlitN 3` —
  the *emitted program*, run on a concrete heap by `evalFuel`, charges
  exactly that vector.

**It matched, exactly.**  Three `ir.copy` (`si` from the live base, `di` and
`dc` from the allocator's result cell), one `ir.add` (`se ← sp + n`), one
`ir.const` (`one ← 1`), and nothing else.  So `arlAppendMachineN`'s growth
branch stands unchanged and `ArrayListCash.lean` needs no correction — unlike
`arlCopyCost` (E34) and `implHeapSwimCost`/`implHeapSinkCost` (F11), which is
worth recording precisely because the same check is what caught those.

One degree of freedom is worth naming rather than hiding: `dc` and `pc` are
kept distinct, so the block costs three copies.  A caller willing to let the
block live in the allocator's own result cell could instantiate `dc := pc`
and save one `ir.copy`.  That is *not* what a real caller wants — the block
has to land in the array list's own buffer cell, which is occupied by the old
base pointer at allocation time and so cannot be the allocator's junk
destination — and it is not what `arlBlitSetupN` predicted, so the distinct
cells are kept and the extra copy is real.

## Disjointness (hazard: it is discharged, not assumed)

`hnr_mop_blit` requires the source and destination ranges separated, and the
premise that says so is the separating conjunction itself: `(sp ↦ₕ xs) ∗
(dp ↦ₕ zs)` (`HeapCopy.lean`'s D-A4a, with `blitPre_overlap_false` compiling
the converse).  In the composed rule that conjunction is *produced*, not
required: the caller supplies `sp ↦ₕ xs` and the availability resource, the
allocator's `hnr_mop_alloc` splits `dp ↦ₕ List.replicate n 0` **out of**
`avail hp (n + k)` by `avail_split`, and the two conjuncts then sit side by
side in one assertion.  What makes that legitimate is `avail_owns_nothing_below`
and `alloc_no_reuse`: the availability resource owns nothing below its bump
pointer, so the fresh range cannot be any part of the live one.  The
top-level statement therefore carries **no** arithmetic disjointness
hypothesis for a caller to supply — the only side conditions are the two
length bounds, and they are inside the `mop`'s own `assert`
(`hnr_assert`), where the array list's `Wf` discharges them
(`arlGrowRaw_eq`, `arlGrowPushRaw_eq`).

## Registration (ledger E29)

`hnr_mop_growBlock` and `hnr_mop_growPush` **are** registered in
`sepref_fr_rules`; `arlGrowSynth` and `arlGrowPushSynth` — the composed
commands, which *do* contain an allocation — are **not**.

The registered rules are safe under E29 for the same reason `hnr_mop_blit`
is, and it is checked rather than argued: their programs are closed and
allocation-free.  `growBlock_no_hp` / `growPush_no_hp` are compiled
`#guard`s that neither block mentions `hpName` anywhere, at fresh cell names;
`allocProg_uses_hp` is the positive control that the check can fail.  So
synthesis cannot use these rules to place an allocation inside a loop: there
is no allocation in them to place.

The composed commands are a different matter, and that is exactly why they
stay out of the database.  `arlGrowSynth_impl` begins with `allocProg`, so
registering it would let the frame inferencer drop an allocation into any
loop body whose abstract program happened to mention `arlGrowRaw`.  Nothing
needs it registered: growth is reached by *naming* `arlGrowRaw` /
`arlGrowPushRaw`, exactly as `ArrayListGrow.lean` says the allocating path
should be, and the array-list family's registered executable rules stay the
seven nonallocating commands plus P4's in-place `arlAppend_exec_hnr`.

## What this does *not* close

Append is **not** synthesizable end to end, and the remaining gap is
representational rather than combinatorial.  `ArrayList.lean` represents the
buffer as a *named IR array* (`arrayAssn buffer A`, `A ↦ₐ xs`), while the
allocator and the copy loop work on *heap ranges* (`p ↦ₕ xs` inside the one
reserved `heapName` array).  There is no landed bridge `arrayAssn ⟷
heapBlockAssn`, so the growth command proved here cannot yet be plugged into
`arlAppendTotal`'s dispatch as its `else` branch: the branch test, the length
bump and the observable `(A, len, cap)` packing all live on the `arrayAssn`
side.  That bridge, and `hnr_If` over the two branches, is what a further
leaf would need; it is named here rather than softened, and nothing in this
file pretends otherwise.

`arlAppendOp_refines` is untouched — still `@[sepref_fref_thms]` over
`arrayListRel` at precondition `fun _ : List ℕ => True`, still guarded by
`ArrayListCash.lean`'s compiled `arlAppendOp_refines_unchanged`.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## 1. The cursor-setup block and the copy loop -/

/-- The cursor-setup block, then the copy loop. -/
def arlGrowBlockCom (t si se one di dc sc lc pc : String) : Com :=
  .seq (.copy si sc)
    (.seq (.binop .add se sc lc)
      (.seq (.const one 1)
        (.seq (.copy di pc)
          (.seq (.copy dc pc) (blitProg t si di se one)))))

noncomputable def arlSetupCost : ECost :=
  irUnit Currency.copy + irUnit Currency.add + irUnit Currency.const +
    irUnit Currency.copy + irUnit Currency.copy

noncomputable def arlGrowBlockCost (n : ℕ) : ECost := arlSetupCost + blitCost n

theorem arlGrowBlock_triple (t si se one di dc sc lc pc : String) (sp dp n : ℕ)
    (xs zs : List Val) (hxs : n ≤ xs.length) (hzs : n ≤ zs.length)
    (v₀ vsi vse vone vdi vdc : Val) :
    irTriple
      (¤(arlGrowBlockCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ vsi) ∗ (se ↦ᵥ vse) ∗ (one ↦ᵥ vone) ∗
        (di ↦ᵥ vdi) ∗ (dc ↦ᵥ vdc) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
        (pc ↦ᵥ dp) ∗ (dp ↦ₕ zs))
      (arlGrowBlockCom t si se one di dc sc lc pc)
      (blitPost t si di se one sp dp n xs zs ∗ (dc ↦ᵥ dp) ∗ (pc ↦ᵥ dp) ∗
        (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n)) := by
  have hadd : irTriple (¤¤Currency.add 1 ∗ (se ↦ᵥ vse) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n))
      (.binop .add se sc lc) ((se ↦ᵥ (sp + n)) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n)) := by
    have h := binop_triple .add se sc lc vse sp n
    rwa [binopCurrency_add, Imp.Bop.apply_add] at h
  rw [arlGrowBlockCom, arlGrowBlockCost, arlSetupCost]
  simp only [credits_add, ← costCredits_one]
  refine seq_triple
    (R := ¤¤Currency.add 1 ∗ ¤¤Currency.const 1 ∗ ¤¤Currency.copy 1 ∗ ¤¤Currency.copy 1 ∗
      ¤(blitCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ sp) ∗ (se ↦ᵥ vse) ∗ (one ↦ᵥ vone) ∗
      (di ↦ᵥ vdi) ∗ (dc ↦ᵥ vdc) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
      (pc ↦ᵥ dp) ∗ (dp ↦ₕ zs)) ?_ ?_
  · ir_frame (copy_triple si sc vsi sp)
  refine seq_triple
    (R := ¤¤Currency.const 1 ∗ ¤¤Currency.copy 1 ∗ ¤¤Currency.copy 1 ∗
      ¤(blitCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ sp) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ vone) ∗
      (di ↦ᵥ vdi) ∗ (dc ↦ᵥ vdc) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
      (pc ↦ᵥ dp) ∗ (dp ↦ₕ zs)) ?_ ?_
  · ir_frame hadd
  refine seq_triple
    (R := ¤¤Currency.copy 1 ∗ ¤¤Currency.copy 1 ∗
      ¤(blitCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ sp) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
      (di ↦ᵥ vdi) ∗ (dc ↦ᵥ vdc) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
      (pc ↦ᵥ dp) ∗ (dp ↦ₕ zs)) ?_ ?_
  · ir_frame (const_triple one 1 vone)
  refine seq_triple
    (R := ¤¤Currency.copy 1 ∗
      ¤(blitCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ sp) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
      (di ↦ᵥ dp) ∗ (dc ↦ᵥ vdc) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
      (pc ↦ᵥ dp) ∗ (dp ↦ₕ zs)) ?_ ?_
  · ir_frame (copy_triple di pc vdi dp)
  refine seq_triple
    (R := ¤(blitCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ sp) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
      (di ↦ᵥ dp) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ zs) ∗ (dc ↦ᵥ dp) ∗ (pc ↦ᵥ dp) ∗
      (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n)) ?_ ?_
  · ir_frame (copy_triple dc pc vdc dp)
  · ir_frame (blit_triple t si di se one sp dp n xs zs hxs hzs v₀)

/-- The growth branch: the cursor block, the copy loop, and the element write
the destination cursor is already standing on. -/
def arlGrowPushCom (t si se one di dc sc lc pc xc : String) : Com :=
  .seq (arlGrowBlockCom t si se one di dc sc lc pc) (.aset heapName di xc)

noncomputable def arlGrowPushCost (n : ℕ) : ECost :=
  arlGrowBlockCost n + irUnit Currency.aset

/-- What the growth branch leaves: the fresh block with the copied prefix and
the new element at the old length. -/
def arlGrowPushPost (t si se one di dc sc lc pc xc : String) (sp dp n x : ℕ)
    (xs zs : List Val) : Assn :=
  ∃ᵃ v, ((t ↦ᵥ v) ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
    (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ (hblit zs xs n).set n x) ∗ (dc ↦ᵥ dp) ∗
    (pc ↦ᵥ dp) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (xc ↦ᵥ x))

theorem arlGrowPushPost_eq (t si se one di dc sc lc pc xc : String) (sp dp n x : ℕ)
    (xs zs : List Val) :
    arlGrowPushPost t si se one di dc sc lc pc xc sp dp n x xs zs =
      (junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ (hblit zs xs n).set n x) ∗ (dc ↦ᵥ dp) ∗
        (pc ↦ᵥ dp) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (xc ↦ᵥ x)) := by
  rw [junkCell_def, sepEx_sepConj]
  rfl

private theorem irTriple_sepEx' {β : Type} {P : β → Assn} {Q R : Assn} {c : Com}
    (h : ∀ y, irTriple (P y ∗ Q) c R) : irTriple ((∃ᵃ y, P y) ∗ Q) c R := by
  intro F p hp
  rw [sepConj_assoc, sepEx_sepConj] at hp
  obtain ⟨y, hy⟩ := hp
  exact h y F p (by rw [sepConj_assoc]; exact hy)

theorem arlGrowPush_triple (t si se one di dc sc lc pc xc : String) (sp dp n x : ℕ)
    (xs zs : List Val) (hxs : n ≤ xs.length) (hzs : n < zs.length)
    (v₀ vsi vse vone vdi vdc : Val) :
    irTriple
      (¤(arlGrowPushCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ vsi) ∗ (se ↦ᵥ vse) ∗ (one ↦ᵥ vone) ∗
        (di ↦ᵥ vdi) ∗ (dc ↦ᵥ vdc) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
        (pc ↦ᵥ dp) ∗ (dp ↦ₕ zs) ∗ (xc ↦ᵥ x))
      (arlGrowPushCom t si se one di dc sc lc pc xc)
      (arlGrowPushPost t si se one di dc sc lc pc xc sp dp n x xs zs) := by
  have hlen : n < (hblit zs xs n).length := by
    rw [hblit_length hxs (le_of_lt hzs)]; exact hzs
  rw [arlGrowPushCom, arlGrowPushCost, credits_add, ← costCredits_one]
  refine seq_triple
    (R := blitPost t si di se one sp dp n xs zs ∗ (dc ↦ᵥ dp) ∗ (pc ↦ᵥ dp) ∗
      (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ ¤¤Currency.aset 1 ∗ (xc ↦ᵥ x)) ?_ ?_
  · ir_frame (arlGrowBlock_triple t si se one di dc sc lc pc sp dp n xs zs hxs
      (le_of_lt hzs) v₀ vsi vse vone vdi vdc)
  rw [blitPost]
  refine irTriple_sepEx' fun v => ?_
  refine irTriple_ex v ?_
  ir_frame (haset_triple di xc dp n (hblit zs xs n) x hlen)

private theorem irHtriple_sepEx' {β : Type} {P : β → Assn} {Q R : Assn} {c : Com}
    (h : ∀ y, irHtriple (P y ∗ Q) c R) : irHtriple ((∃ᵃ y, P y) ∗ Q) c R := by
  intro F p hp
  rw [sepConj_assoc, sepEx_sepConj] at hp
  obtain ⟨y, hy⟩ := hp
  exact h y F p (by rw [sepConj_assoc]; exact hy)

private theorem irHtriple_junk' {x : String} {A P Q : Assn} {c : Com}
    (h : ∀ v : Val, irHtriple (A ∗ (x ↦ᵥ v) ∗ P) c Q) :
    irHtriple (A ∗ junkCell x ∗ P) c Q := by
  rw [show (A ∗ junkCell x ∗ P) = junkCell x ∗ (A ∗ P) from by ac_rfl]
  refine irHtriple_junk fun v => ?_
  rw [show ((x ↦ᵥ v) ∗ A ∗ P) = (A ∗ (x ↦ᵥ v) ∗ P) from by ac_rfl]
  exact h v

private theorem irHtriple_junk6 {x1 x2 x3 x4 x5 x6 : String} {A P Q : Assn} {c : Com}
    (h : ∀ v1 v2 v3 v4 v5 v6 : Val,
      irHtriple (A ∗ (x1 ↦ᵥ v1) ∗ (x2 ↦ᵥ v2) ∗ (x3 ↦ᵥ v3) ∗ (x4 ↦ᵥ v4) ∗ (x5 ↦ᵥ v5) ∗
        (x6 ↦ᵥ v6) ∗ P) c Q) :
    irHtriple (A ∗ junkCell x1 ∗ junkCell x2 ∗ junkCell x3 ∗ junkCell x4 ∗ junkCell x5 ∗
      junkCell x6 ∗ P) c Q := by
  refine irHtriple_junk' fun v1 => ?_
  rw [← sepConj_assoc]
  refine irHtriple_junk' fun v2 => ?_
  rw [← sepConj_assoc]
  refine irHtriple_junk' fun v3 => ?_
  rw [← sepConj_assoc]
  refine irHtriple_junk' fun v4 => ?_
  rw [← sepConj_assoc]
  refine irHtriple_junk' fun v5 => ?_
  rw [← sepConj_assoc]
  refine irHtriple_junk' fun v6 => ?_
  rw [show (((((A ∗ (x1 ↦ᵥ v1)) ∗ (x2 ↦ᵥ v2)) ∗ (x3 ↦ᵥ v3)) ∗ (x4 ↦ᵥ v4)) ∗ (x5 ↦ᵥ v5)) ∗
      (x6 ↦ᵥ v6) ∗ P
      = A ∗ (x1 ↦ᵥ v1) ∗ (x2 ↦ᵥ v2) ∗ (x3 ↦ᵥ v3) ∗ (x4 ↦ᵥ v4) ∗ (x5 ↦ᵥ v5) ∗
        (x6 ↦ᵥ v6) ∗ P from by ac_rfl]
  exact h v1 v2 v3 v4 v5 v6

theorem arlGrowBlock_junk_rule (t si se one di dc sc lc pc : String) (sp n : ℕ)
    (xs zs : List Val) (hxs : n ≤ xs.length) (hzs : n ≤ zs.length) :
    irHtriple (¤(arlGrowBlockCost n) ∗
        (junkCell t ∗ junkCell si ∗ junkCell se ∗ junkCell one ∗ junkCell di ∗
          junkCell dc ∗ hnCtxt natAssn sp sc ∗ hnCtxt natAssn n lc ∗ (sp ↦ₕ xs) ∗
          hnCtxt heapBlockAssn zs pc))
      (arlGrowBlockCom t si se one di dc sc lc pc)
      ((junkCell t ∗ hnCtxt natAssn (sp + n) si ∗ hnCtxt natAssn (sp + n) se ∗
          hnCtxt natAssn 1 one ∗ junkCell di ∗ junkCell pc ∗ hnCtxt natAssn sp sc ∗
          hnCtxt natAssn n lc ∗ (sp ↦ₕ xs)) ∗
        heapBlockAssn (hblit zs xs n) dc) := by
  set REST : Assn := ¤(arlGrowBlockCost n) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) with hREST
  rw [show (¤(arlGrowBlockCost n) ∗
      (junkCell t ∗ junkCell si ∗ junkCell se ∗ junkCell one ∗ junkCell di ∗
        junkCell dc ∗ hnCtxt natAssn sp sc ∗ hnCtxt natAssn n lc ∗ (sp ↦ₕ xs) ∗
        hnCtxt heapBlockAssn zs pc))
      = (∃ᵃ p, (pc ↦ᵥ p) ∗ (p ↦ₕ zs)) ∗ (junkCell t ∗ junkCell si ∗ junkCell se ∗
        junkCell one ∗ junkCell di ∗ junkCell dc ∗ REST) from by
    simp only [hREST, hnCtxt_def, natAssn_def, heapBlockAssn_def]; ac_rfl]
  refine irHtriple_sepEx' fun dp => ?_
  refine irHtriple_junk6 fun v₀ vsi vse vone vdi vdc => ?_
  refine cons_rule (irTriple.gc
    (arlGrowBlock_triple t si se one di dc sc lc pc sp dp n xs zs hxs hzs
      v₀ vsi vse vone vdi vdc)) (fun s hs => ?_) (fun _ s hs => ?_)
  · revert hs
    rw [show (((pc ↦ᵥ dp) ∗ (dp ↦ₕ zs)) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ vsi) ∗ (se ↦ᵥ vse) ∗
        (one ↦ᵥ vone) ∗ (di ↦ᵥ vdi) ∗ (dc ↦ᵥ vdc) ∗ REST)
        = (¤(arlGrowBlockCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ vsi) ∗ (se ↦ᵥ vse) ∗ (one ↦ᵥ vone) ∗
          (di ↦ᵥ vdi) ∗ (dc ↦ᵥ vdc) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
          (pc ↦ᵥ dp) ∗ (dp ↦ₕ zs)) from by rw [hREST]; ac_rfl]
    exact fun h => h
  · revert hs
    rw [blitPost_eq]
    rw [show ((junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs n)) ∗ (dc ↦ᵥ dp) ∗ (pc ↦ᵥ dp) ∗
        (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n))
        = ((junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
          (di ↦ᵥ (dp + n)) ∗ (pc ↦ᵥ dp) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs)) ∗
          ((dc ↦ᵥ dp) ∗ (dp ↦ₕ hblit zs xs n))) from by ac_rfl]
    refine conj_entails_mono (conj_entails_mono ?_ ?_) (entails_refl GC) s
    · simp only [hnCtxt_def, natAssn_def]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right ?_)))
      refine entails_trans (sepConj_mono_left (natAssn_entails_junkCell (dp + n) di)) ?_
      exact sepConj_mono_right (sepConj_mono_left (natAssn_entails_junkCell dp pc))
    · exact fun _ hh => ⟨dp, hh⟩

noncomputable def mopGrowBlock (dst src : List Val) (n : ℕ) : NRest (List Val) ECost :=
  NRest.bindT (NRest.assert (n ≤ src.length ∧ n ≤ dst.length)) fun _ =>
    NRest.consume (NRest.returnT (hblit dst src n)) (arlGrowBlockCost n)

@[sepref_fr_rules]
theorem hnr_mop_growBlock (t si se one di dc sc lc pc : String) (sp n : ℕ)
    (xs zs : List Val) :
    hnRefine
      (junkCell t ∗ junkCell si ∗ junkCell se ∗ junkCell one ∗ junkCell di ∗
        junkCell dc ∗ hnCtxt natAssn sp sc ∗ hnCtxt natAssn n lc ∗ (sp ↦ₕ xs) ∗
        hnCtxt heapBlockAssn zs pc)
      (arlGrowBlockCom t si se one di dc sc lc pc)
      (junkCell t ∗ hnCtxt natAssn (sp + n) si ∗ hnCtxt natAssn (sp + n) se ∗
        hnCtxt natAssn 1 one ∗ junkCell di ∗ junkCell pc ∗ hnCtxt natAssn sp sc ∗
        hnCtxt natAssn n lc ∗ (sp ↦ₕ xs))
      dc heapBlockAssn (mopGrowBlock zs xs n) :=
  hnr_assert fun h =>
    hnRefineI_spect (arlGrowBlock_junk_rule t si se one di dc sc lc pc sp n xs zs h.1 h.2)

theorem arlGrowPush_junk_rule (t si se one di dc sc lc pc xc : String) (sp n x : ℕ)
    (xs zs : List Val) (hxs : n ≤ xs.length) (hzs : n < zs.length) :
    irHtriple (¤(arlGrowPushCost n) ∗
        (junkCell t ∗ junkCell si ∗ junkCell se ∗ junkCell one ∗ junkCell di ∗
          junkCell dc ∗ hnCtxt natAssn sp sc ∗ hnCtxt natAssn n lc ∗ (sp ↦ₕ xs) ∗
          hnCtxt natAssn x xc ∗ hnCtxt heapBlockAssn zs pc))
      (arlGrowPushCom t si se one di dc sc lc pc xc)
      ((junkCell t ∗ hnCtxt natAssn (sp + n) si ∗ hnCtxt natAssn (sp + n) se ∗
          hnCtxt natAssn 1 one ∗ junkCell di ∗ junkCell pc ∗ hnCtxt natAssn sp sc ∗
          hnCtxt natAssn n lc ∗ (sp ↦ₕ xs) ∗ hnCtxt natAssn x xc) ∗
        heapBlockAssn ((hblit zs xs n).set n x) dc) := by
  set REST : Assn := ¤(arlGrowPushCost n) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
    (xc ↦ᵥ x) with hREST
  rw [show (¤(arlGrowPushCost n) ∗
      (junkCell t ∗ junkCell si ∗ junkCell se ∗ junkCell one ∗ junkCell di ∗
        junkCell dc ∗ hnCtxt natAssn sp sc ∗ hnCtxt natAssn n lc ∗ (sp ↦ₕ xs) ∗
        hnCtxt natAssn x xc ∗ hnCtxt heapBlockAssn zs pc))
      = (∃ᵃ p, (pc ↦ᵥ p) ∗ (p ↦ₕ zs)) ∗ (junkCell t ∗ junkCell si ∗ junkCell se ∗
        junkCell one ∗ junkCell di ∗ junkCell dc ∗ REST) from by
    simp only [hREST, hnCtxt_def, natAssn_def, heapBlockAssn_def]; ac_rfl]
  refine irHtriple_sepEx' fun dp => ?_
  refine irHtriple_junk6 fun v₀ vsi vse vone vdi vdc => ?_
  refine cons_rule (irTriple.gc
    (arlGrowPush_triple t si se one di dc sc lc pc xc sp dp n x xs zs hxs hzs
      v₀ vsi vse vone vdi vdc)) (fun s hs => ?_) (fun _ s hs => ?_)
  · revert hs
    rw [show (((pc ↦ᵥ dp) ∗ (dp ↦ₕ zs)) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ vsi) ∗ (se ↦ᵥ vse) ∗
        (one ↦ᵥ vone) ∗ (di ↦ᵥ vdi) ∗ (dc ↦ᵥ vdc) ∗ REST)
        = (¤(arlGrowPushCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ vsi) ∗ (se ↦ᵥ vse) ∗ (one ↦ᵥ vone) ∗
          (di ↦ᵥ vdi) ∗ (dc ↦ᵥ vdc) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
          (pc ↦ᵥ dp) ∗ (dp ↦ₕ zs) ∗ (xc ↦ᵥ x)) from by rw [hREST]; ac_rfl]
    exact fun h => h
  · revert hs
    rw [arlGrowPushPost_eq]
    rw [show ((junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ (hblit zs xs n).set n x) ∗ (dc ↦ᵥ dp) ∗
        (pc ↦ᵥ dp) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (xc ↦ᵥ x)))
        = ((junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
          (di ↦ᵥ (dp + n)) ∗ (pc ↦ᵥ dp) ∗ (sc ↦ᵥ sp) ∗ (lc ↦ᵥ n) ∗ (sp ↦ₕ xs) ∗
          (xc ↦ᵥ x)) ∗ ((dc ↦ᵥ dp) ∗ (dp ↦ₕ (hblit zs xs n).set n x))) from by ac_rfl]
    refine conj_entails_mono (conj_entails_mono ?_ ?_) (entails_refl GC) s
    · simp only [hnCtxt_def, natAssn_def]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right ?_)))
      refine entails_trans (sepConj_mono_left (natAssn_entails_junkCell (dp + n) di)) ?_
      exact sepConj_mono_right (sepConj_mono_left (natAssn_entails_junkCell dp pc))
    · exact fun _ hh => ⟨dp, hh⟩

noncomputable def mopGrowPush (dst src : List Val) (n x : ℕ) : NRest (List Val) ECost :=
  NRest.bindT (NRest.assert (n ≤ src.length ∧ n < dst.length)) fun _ =>
    NRest.consume (NRest.returnT ((hblit dst src n).set n x)) (arlGrowPushCost n)

@[sepref_fr_rules]
theorem hnr_mop_growPush (t si se one di dc sc lc pc xc : String) (sp n x : ℕ)
    (xs zs : List Val) :
    hnRefine
      (junkCell t ∗ junkCell si ∗ junkCell se ∗ junkCell one ∗ junkCell di ∗
        junkCell dc ∗ hnCtxt natAssn sp sc ∗ hnCtxt natAssn n lc ∗ (sp ↦ₕ xs) ∗
        hnCtxt natAssn x xc ∗ hnCtxt heapBlockAssn zs pc)
      (arlGrowPushCom t si se one di dc sc lc pc xc)
      (junkCell t ∗ hnCtxt natAssn (sp + n) si ∗ hnCtxt natAssn (sp + n) se ∗
        hnCtxt natAssn 1 one ∗ junkCell di ∗ junkCell pc ∗ hnCtxt natAssn sp sc ∗
        hnCtxt natAssn n lc ∗ (sp ↦ₕ xs) ∗ hnCtxt natAssn x xc)
      dc heapBlockAssn (mopGrowPush zs xs n x) :=
  hnr_assert fun h =>
    hnRefineI_spect
      (arlGrowPush_junk_rule t si se one di dc sc lc pc xc sp n x xs zs h.1 h.2)

noncomputable def arlGrowRaw (s : ArrayList) : NRest (List Val) ECost :=
  NRest.bindT (mopAlloc (2 * s.capacity)) fun blk => mopGrowBlock blk s.buffer s.length

set_option maxHeartbeats 1000000 in
sepref_synth arlGrowSynth (sp hp k : ℕ) (s : ArrayList) :
  hnRefine (junkCell "pc" ∗ avail hp (2 * s.capacity + k) ∗
      hnCtxt natAssn (2 * s.capacity) "nc" ∗
      junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ junkCell "one" ∗ junkCell "di" ∗
      junkCell "dc" ∗ hnCtxt natAssn sp "sc" ∗ hnCtxt natAssn s.length "lc" ∗
      (sp ↦ₕ s.buffer))
    _ _ "dc" heapBlockAssn (arlGrowRaw s)

noncomputable def arlGrowPushRaw (s : ArrayList) (x : ℕ) : NRest (List Val) ECost :=
  NRest.bindT (mopAlloc (2 * s.capacity)) fun blk => mopGrowPush blk s.buffer s.length x

set_option maxHeartbeats 1000000 in
sepref_synth arlGrowPushSynth (sp hp k x : ℕ) (s : ArrayList) :
  hnRefine (junkCell "pc" ∗ avail hp (2 * s.capacity + k) ∗
      hnCtxt natAssn (2 * s.capacity) "nc" ∗
      junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ junkCell "one" ∗ junkCell "di" ∗
      junkCell "dc" ∗ hnCtxt natAssn sp "sc" ∗ hnCtxt natAssn s.length "lc" ∗
      (sp ↦ₕ s.buffer) ∗ hnCtxt natAssn x "xc")
    _ _ "dc" heapBlockAssn (arlGrowPushRaw s x)

theorem arlGrowPushRaw_eq (s : ArrayList) (x : ℕ) (h : s.Wf) (hcap : 0 < s.capacity) :
    arlGrowPushRaw s x = NRest.consume (NRest.returnT (arlPushGrown s x).buffer)
      (allocCost (2 * s.capacity) + arlGrowPushCost s.length) := by
  obtain ⟨-, hlc, hcb⟩ := h
  rw [arlGrowPushRaw, mopAlloc_def, Lax13Proofs.Refine.Iicf.bindT_unit, mopGrowPush,
    NRest.assert_pos (⟨by omega, by simpa using by omega⟩ :
      s.length ≤ s.buffer.length ∧ s.length < (List.replicate (2 * s.capacity) 0).length),
    NRest.returnT_bindT, NRest.consume_consume, arlGrowCopy_value]
  rfl

theorem arlGrowRaw_eq (s : ArrayList) (h : s.Wf) :
    arlGrowRaw s = NRest.consume (NRest.returnT (arlGrow s).buffer)
      (allocCost (2 * s.capacity) + arlGrowBlockCost s.length) := by
  obtain ⟨-, hlc, hcb⟩ := h
  rw [arlGrowRaw, mopAlloc_def, Lax13Proofs.Refine.Iicf.bindT_unit, mopGrowBlock,
    NRest.assert_pos (⟨by omega, by simpa using by omega⟩ :
      s.length ≤ s.buffer.length ∧ s.length ≤ (List.replicate (2 * s.capacity) 0).length),
    NRest.returnT_bindT, NRest.consume_consume, arlGrowCopy_value]

private theorem cost_copy_three :
    (ACost.cost Currency.copy ((3 : ℕ) : ℕ∞) : ECost)
      = ACost.cost Currency.copy 1 + ACost.cost Currency.copy 1 +
        ACost.cost Currency.copy 1 := by
  rw [ACost.cost_add_cost, ACost.cost_add_cost]
  norm_num

/-- The setup block's derived price, currency by currency. -/
theorem arlSetupCost_eq :
    arlSetupCost =
      ACost.cost Currency.copy ((3 : ℕ) : ℕ∞) +
        (ACost.cost Currency.add ((1 : ℕ) : ℕ∞) +
          ACost.cost Currency.const ((1 : ℕ) : ℕ∞)) := by
  rw [arlSetupCost, cost_copy_three]
  simp only [irUnit, Nat.cast_one]
  abel

/-- **The prediction check.**  `ArrayListCash.lean`'s `arlBlitSetupN` was
written from a description of this block before the block existed. -/
theorem arlBlitSetupN_toE : arlBlitSetupN.toE = arlSetupCost := by
  rw [arlSetupCost_eq, arlBlitSetupN, IrVecN.toE, cost_copy_three]
  simp only [Nat.cast_zero, Nat.cast_one, ACost.cost_zero]
  rw [← cost_copy_three]
  abel

namespace GrowGate

open Lax13Proofs.Refine.Ir.Gate (costVector readVars readArrs)

/-- The emitted body of the copy loop. -/
private def gateLoop : Com :=
  Com.while (.lt (.cell "si") (.cell "se"))
    ((Com.aget "t" heapName "si").seq
      ((Com.aset heapName "di" "t").seq
        ((Com.binop .add "si" "si" "one").seq (Com.binop .add "di" "di" "one"))))

/-- The emitted command, pinned: the allocator's two instructions, the
five-instruction cursor block, and the copy loop. -/
theorem arlGrowSynth_pinned :
    arlGrowSynth_impl =
      ((Com.copy "pc" hpName).seq (Com.binop .add hpName hpName "nc")).seq
        ((Com.copy "si" "sc").seq
          ((Com.binop .add "se" "sc" "lc").seq
            ((Com.const "one" 1).seq
              ((Com.copy "di" "pc").seq ((Com.copy "dc" "pc").seq gateLoop))))) := rfl

#guard arlGrowSynth_impl =
  ((Com.copy "pc" "$hp").seq (Com.binop .add "$hp" "$hp" "nc")).seq
    ((Com.copy "si" "sc").seq
      ((Com.binop .add "se" "sc" "lc").seq
        ((Com.const "one" 1).seq
          ((Com.copy "di" "pc").seq
            ((Com.copy "dc" "pc").seq
              (Com.while (.lt (.cell "si") (.cell "se"))
                ((Com.aget "t" "$heap" "si").seq
                  ((Com.aset "$heap" "di" "t").seq
                    ((Com.binop .add "si" "si" "one").seq
                      (Com.binop .add "di" "di" "one"))))))))))

/-! ### The emitted command, run -/

/-- A three-element live block at `0`, eight free cells above it. -/
def growGateHeap : List Val := [7, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The six scratch cells start at distinctive **junk** — not at the values the
setup block is supposed to write.  That is what makes every "drop one
instruction" control below bite. -/
def growDemoState : State :=
  State.ofPairs [("sc", 0), ("lc", 3), ("nc", 8), (hpName, 3), ("pc", 91), ("t", 92),
    ("si", 93), ("se", 94), ("one", 95), ("di", 96), ("dc", 97)] [(heapName, growGateHeap)]

def growDemoOut : State × Cost :=
  (evalFuel 80 arlGrowSynth_impl growDemoState).getD (growDemoState, 0)

theorem growDemo_evalFuel : evalFuel 80 arlGrowSynth_impl growDemoState = some growDemoOut := rfl

theorem growDemo_bigStep :
    BigStep arlGrowSynth_impl growDemoState growDemoOut.1 growDemoOut.2 :=
  bigStep_of_evalFuel growDemo_evalFuel

-- The fresh block starts at `3` and holds the copied prefix; the live block is
-- untouched; the block cell and the allocator's cell agree.
#guard readArrs growDemoOut.1 [heapName] = [(heapName, some [7, 8, 9, 7, 8, 9, 0, 0, 0, 0, 0])]
#guard readVars growDemoOut.1 ["dc", "pc", hpName, "si", "se", "di", "one", "sc"] =
  [("dc", some 3), ("pc", some 3), (hpName, some 11), ("si", some 3), ("se", some 3),
   ("di", some 6), ("one", some 1), ("sc", some 0)]

-- …and what the fresh block holds is `arlGrow`'s buffer, on the nose.
#guard ((readArrs growDemoOut.1 [heapName]).head?.map fun r => (r.2.getD []).drop 3)
  = some (arlGrow ⟨[7, 8, 9], 3, 4⟩).buffer

/-- The run's cost, as one of `ArrayListCash.lean`'s nine-currency vectors. -/
def growRunVec (κ : Cost) : IrVecN :=
  ⟨κ.toFun Currency.ite, κ.toFun Currency.mul, κ.toFun Currency.«while»,
    κ.toFun Currency.copy, κ.toFun Currency.const, κ.toFun Currency.skip,
    κ.toFun Currency.aset, κ.toFun Currency.aget, κ.toFun Currency.add⟩

-- **The differential cost test.**  What the emitted command charges is exactly
-- the allocator's price plus the *predicted* cursor block plus the copy loop.
#guard growRunVec growDemoOut.2 = arlAllocN + arlBlitSetupN + arlBlitN 3

-- …spelled out, so the number is visible and not only relative.
#guard costVector growDemoOut.2 =
  [("ir.skip", 0), ("ir.const", 1), ("ir.copy", 4), ("ir.aget", 3), ("ir.aset", 3),
   ("ir.ite", 0), ("ir.while", 4), ("ir.add", 8), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! ### Negative controls that bite -/

/-- Dropping the `one := 1` instruction: the loop never advances, so the
program does not terminate within any fuel the correct one needs. -/
def growNoOneProg : Com :=
  (Com.copy "pc" hpName).seq ((Com.binop .add hpName hpName "nc").seq
    ((Com.copy "si" "sc").seq ((Com.binop .add "se" "sc" "lc").seq
      ((Com.copy "di" "pc").seq ((Com.copy "dc" "pc").seq
        (blitProg "t" "si" "di" "se" "one"))))))

#guard readArrs ((evalFuel 80 growNoOneProg growDemoState).getD (growDemoState, 0)).1 [heapName]
  ≠ [(heapName, some [7, 8, 9, 7, 8, 9, 0, 0, 0, 0, 0])]

/-- Dropping the `si := sc` instruction: `si` keeps its junk value, so the
guard `si < se` fails at once and nothing is copied. -/
def growNoSiProg : Com :=
  (Com.copy "pc" hpName).seq ((Com.binop .add hpName hpName "nc").seq
    ((Com.binop .add "se" "sc" "lc").seq
      ((Com.const "one" 1).seq ((Com.copy "di" "pc").seq ((Com.copy "dc" "pc").seq
        (blitProg "t" "si" "di" "se" "one"))))))

#guard readArrs ((evalFuel 80 growNoSiProg growDemoState).getD (growDemoState, 0)).1 [heapName]
  ≠ [(heapName, some [7, 8, 9, 7, 8, 9, 0, 0, 0, 0, 0])]

/-- Dropping the `di := pc` instruction: the copy lands at `di`'s junk value —
on top of the live block — instead of in the fresh one. -/
def growNoDiProg : Com :=
  (Com.copy "pc" hpName).seq ((Com.binop .add hpName hpName "nc").seq
    ((Com.copy "si" "sc").seq ((Com.binop .add "se" "sc" "lc").seq
      ((Com.const "one" 1).seq ((Com.copy "dc" "pc").seq
        (blitProg "t" "si" "di" "se" "one"))))))

#guard readArrs ((evalFuel 80 growNoDiProg growDemoState).getD (growDemoState, 0)).1 [heapName]
  ≠ [(heapName, some [7, 8, 9, 7, 8, 9, 0, 0, 0, 0, 0])]

/-- Dropping the `dc := pc` instruction: the block cell keeps its junk value,
so the caller is handed the wrong base pointer. -/
def growNoDcProg : Com :=
  (Com.copy "pc" hpName).seq ((Com.binop .add hpName hpName "nc").seq
    ((Com.copy "si" "sc").seq ((Com.binop .add "se" "sc" "lc").seq
      ((Com.const "one" 1).seq ((Com.copy "di" "pc").seq
        (blitProg "t" "si" "di" "se" "one"))))))

#guard readVars ((evalFuel 80 growNoDcProg growDemoState).getD (growDemoState, 0)).1 ["dc"]
  ≠ [("dc", some 3)]

/-- Dropping the `se := sc + lc` instruction: the bound cell keeps its junk
value, so the loop copies the wrong number of elements. -/
def growNoSeProg : Com :=
  (Com.copy "pc" hpName).seq ((Com.binop .add hpName hpName "nc").seq
    ((Com.copy "si" "sc").seq
      ((Com.const "one" 1).seq ((Com.copy "di" "pc").seq ((Com.copy "dc" "pc").seq
        (blitProg "t" "si" "di" "se" "one"))))))

#guard readArrs ((evalFuel 80 growNoSeProg growDemoState).getD (growDemoState, 0)).1 [heapName]
  ≠ [(heapName, some [7, 8, 9, 7, 8, 9, 0, 0, 0, 0, 0])]

/-! ### The cursor arithmetic, off by one

`se` is `sp + n` with `n` the **live length**, not the capacity.  Both
neighbouring bounds are caught. -/

def growOffByOneState (d : ℕ) : State :=
  State.ofPairs [("sc", 0), ("lc", 3 + d), ("nc", 8), (hpName, 3), ("pc", 91), ("t", 92),
    ("si", 93), ("se", 94), ("one", 95), ("di", 96), ("dc", 97)] [(heapName, growGateHeap)]

#guard readArrs ((evalFuel 80 arlGrowSynth_impl (growOffByOneState 1)).getD
    (growDemoState, 0)).1 [heapName]
  ≠ [(heapName, some [7, 8, 9, 7, 8, 9, 0, 0, 0, 0, 0])]

-- …and the *capacity*-sized copy — the `n²` bug touched-only costs exist to
-- forbid — is neither the right value nor the right price.
#guard growRunVec ((evalFuel 80 arlGrowSynth_impl (growOffByOneState 5)).getD
    (growDemoState, 0)).2 ≠ arlAllocN + arlBlitSetupN + arlBlitN 3

/-! ### The growth branch, with the element write -/

#guard arlGrowPushSynth_impl =
  ((Com.copy "pc" "$hp").seq (Com.binop .add "$hp" "$hp" "nc")).seq
    (((Com.copy "si" "sc").seq
      ((Com.binop .add "se" "sc" "lc").seq
        ((Com.const "one" 1).seq
          ((Com.copy "di" "pc").seq
            ((Com.copy "dc" "pc").seq
              (Com.while (.lt (.cell "si") (.cell "se"))
                ((Com.aget "t" "$heap" "si").seq
                  ((Com.aset "$heap" "di" "t").seq
                    ((Com.binop .add "si" "si" "one").seq
                      (Com.binop .add "di" "di" "one")))))))))).seq
      (Com.aset "$heap" "di" "xc"))

def growPushDemoState : State :=
  State.ofPairs [("sc", 0), ("lc", 3), ("nc", 8), (hpName, 3), ("pc", 91), ("t", 92),
    ("si", 93), ("se", 94), ("one", 95), ("di", 96), ("dc", 97), ("xc", 42)]
    [(heapName, growGateHeap)]

def growPushDemoOut : State × Cost :=
  (evalFuel 80 arlGrowPushSynth_impl growPushDemoState).getD (growPushDemoState, 0)

theorem growPushDemo_evalFuel :
    evalFuel 80 arlGrowPushSynth_impl growPushDemoState = some growPushDemoOut := rfl

theorem growPushDemo_bigStep :
    BigStep arlGrowPushSynth_impl growPushDemoState growPushDemoOut.1 growPushDemoOut.2 :=
  bigStep_of_evalFuel growPushDemo_evalFuel

#guard readArrs growPushDemoOut.1 [heapName] =
  [(heapName, some [7, 8, 9, 7, 8, 9, 42, 0, 0, 0, 0])]

-- **The differential test against the pure model.**  What the emitted growth
-- branch leaves in the fresh block is exactly `arlPushGrown`'s buffer.
#guard ((readArrs growPushDemoOut.1 [heapName]).head?.map fun r => (r.2.getD []).drop 3)
  = some (arlPushGrown ⟨[7, 8, 9], 3, 4⟩ 42).buffer

-- …and one `ir.aset` more than growth alone, and nothing else.
#guard growRunVec growPushDemoOut.2 =
  arlAllocN + arlBlitSetupN + arlBlitN 3 + ⟨0, 0, 0, 0, 0, 0, 1, 0, 0⟩

-- Negative control: the write lands at the *old length*, not anywhere else.
#guard ((readArrs growPushDemoOut.1 [heapName]).head?.map fun r => (r.2.getD []).drop 3)
  ≠ some (arlPushGrown ⟨[7, 8, 9], 3, 4⟩ 43).buffer
#guard ((readArrs growPushDemoOut.1 [heapName]).head?.map fun r => (r.2.getD []).drop 3)
  ≠ some ((arlGrow ⟨[7, 8, 9], 3, 4⟩).buffer.set 2 42)

/-- **The composed rule is not derivable at one payload too few.** -/
example : True := by
  fail_if_success
    (have : irTriple
        (¤(arlSetupCost + (irUnit Currency.«while» + (2 : ℕ) • blitPayload)) ∗
          ("t" ↦ᵥ 0) ∗ ("si" ↦ᵥ 0) ∗ ("se" ↦ᵥ 0) ∗ ("one" ↦ᵥ 0) ∗ ("di" ↦ᵥ 0) ∗
          ("dc" ↦ᵥ 0) ∗ ("sc" ↦ᵥ 0) ∗ ("lc" ↦ᵥ 3) ∗ ((0 : ℕ) ↦ₕ [7, 8, 9]) ∗
          ("pc" ↦ᵥ 4) ∗ ((4 : ℕ) ↦ₕ [0, 0, 0, 0]))
        (arlGrowBlockCom "t" "si" "se" "one" "di" "dc" "sc" "lc" "pc")
        (blitPost "t" "si" "di" "se" "one" 0 4 3 [7, 8, 9] [0, 0, 0, 0] ∗
          ("dc" ↦ᵥ 4) ∗ ("pc" ↦ᵥ 4) ∗ ("sc" ↦ᵥ 0) ∗ ("lc" ↦ᵥ 3)) := by
      exact arlGrowBlock_triple "t" "si" "se" "one" "di" "dc" "sc" "lc" "pc" 0 4 3
        [7, 8, 9] [0, 0, 0, 0] (by simp) (by simp) 0 0 0 0 0 0)
  trivial

/-! ### E29: the registered blocks are allocation-free, mechanically

The rules put into `sepref_fr_rules` are the two blocks, not the composed
commands.  A block can only mention the cells its caller names, so the check
that matters is that neither block mentions the allocator's bump pointer
`hpName` at any instantiation — here at fresh names disjoint from it. -/

private def condMentions (x : String) : Cond → Bool
  | .eq u v => opMentions u || opMentions v
  | .lt u v => opMentions u || opMentions v
where
  opMentions : Operand → Bool
    | .cell y => y == x
    | .lit _ => false

/-- Does a command name the cell `x` anywhere? -/
private def mentions (x : String) : Com → Bool
  | .skip => false
  | .const y _ => y == x
  | .copy y z => y == x || z == x
  | .binop _ y z w => y == x || z == x || w == x
  | .aget y a i => y == x || a == x || i == x
  | .aset a i v => a == x || i == x || v == x
  | .seq c d => mentions x c || mentions x d
  | .ite b c d => condMentions x b || mentions x c || mentions x d
  | .while b c => condMentions x b || mentions x c

/-- **The E29 discharge.**  The registered cursor block never touches the bump
pointer, so no synthesis using it can place an allocation anywhere. -/
theorem growBlock_no_hp :
    mentions hpName (arlGrowBlockCom "t" "si" "se" "one" "di" "dc" "sc" "lc" "pc")
      = false := by decide +kernel

theorem growPush_no_hp :
    mentions hpName (arlGrowPushCom "t" "si" "se" "one" "di" "dc" "sc" "lc" "pc" "xc")
      = false := by decide +kernel

#guard mentions hpName (arlGrowBlockCom "t" "si" "se" "one" "di" "dc" "sc" "lc" "pc") = false
#guard mentions hpName
  (arlGrowPushCom "t" "si" "se" "one" "di" "dc" "sc" "lc" "pc" "xc") = false

/-- **The positive control**: the check does fail on a program that *does*
allocate, so `growBlock_no_hp` is not vacuous.  This is also why the composed
commands are deliberately left out of `sepref_fr_rules`. -/
theorem allocProg_uses_hp : mentions hpName (allocProg "pc" "nc") = true := by decide +kernel

#guard mentions hpName arlGrowSynth_impl = true
#guard mentions hpName arlGrowPushSynth_impl = true

end GrowGate

/-! ## 6. Axiom hygiene -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowBlock_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowBlock_triple

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_mop_growBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_growBlock

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_mop_growPush' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_growPush

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowSynth

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowPushSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowPushSynth

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowRaw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowRaw_eq

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlGrowPushRaw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlGrowPushRaw_eq

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlBlitSetupN_toE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlBlitSetupN_toE

end Lax13Proofs.Refine.Sepref.Iicf
