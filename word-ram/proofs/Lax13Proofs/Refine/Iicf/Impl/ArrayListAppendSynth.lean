import Lax13Proofs.Refine.Iicf.Impl.ArrayListHeap

/-!
# The append dispatch, and end-to-end append

Leaf **P4.5.A.8**, satellite of `ArrayListHeap.lean` (ledger **E38**).

`ArrayListHeap.lean` put the array list on the heap and named the one thing
still missing: *append is not synthesizable end to end, and the gap is
`hnr_If` over a **moving base pointer**.*  The in-place branch ends at
`heapBlockAssnAt p`, the growth branch at `heapBlockAssnAt p'`, and `hnr_If`
requires the two branches to agree on the result assertion `R`, which those
two do not.  This file closes it, and the shape of the answer is exactly the
one E38 predicted.

## The emitted command

```
nc := cap * two                          -- the doubled capacity, once
if len < cap then
  adr := bc + len ; heap[adr] := xc      -- the element write, in place
  len := len + one ; dc := bc            -- bump, and re-seat the block cell
  skip ; skip                            -- pack (dc, (len, cap))
else
  pc := $hp ; $hp := $hp + nc            -- allocate the doubled block
  si := bc ; se := bc + len ; one := 1
  di := pc ; dc := pc                    -- the cursor-setup block (A.6)
  while si < se { t := heap[si] ; heap[di] := t ; si += one ; di += one }
  heap[di] := xc                         -- the element write, in the copy
  len := len + one ; cap := nc
  skip ; skip
```

`arlHAppendCom` is that command, pinned by `#guard` in § 10 against the two
`sepref_synth` outputs it is assembled from, and **run** on both branches.

## Is append synthesizable end to end?

**Yes, and here is exactly what that means.**  Both *branches* are produced by
`sepref_synth` from the registered rule database and nothing else —
`arlHAppendInPlaceSynth` and `arlHAppendGrowSynth`, whose emitted programs are
logged by the synthesizer and pinned below.  The *dispatch* around them is the
composed rule `arlHAppend_dispatch`: `hnr_seq` for the leading `mul`, then
`hnr_If` with the two synthesized branches and the merge below.  That
composition is proved once and used **by name**, which is the shape E38 asked
for and the shape `ArrayListGrowSynth.lean` already uses for `arlGrowSynth`;
it is deliberately not a database entry, for the reason in the next section.
The result is one `Com` (`arlHAppendCom`), one `hnRefine`
(`arlHAppend_exec_hnr`) whose abstract side is `arlAppendTotal`'s value at an
exact price, and a compiled run of that very command on both branches.

## The merge, and why it is at the packed assertion

`hnr_If` merges the two branches' *contexts* with `MERGE`; it does not merge
their result assertion, which has to be one and the same `R`.  So the moving
base has to disappear from `R` before the branches meet, and the only form in
which it does is `heapBlockAssn` — the **packed** one, base existential.

That is reached the cheap way rather than by a conversion.  The growth branch
is *already* packed: `hnr_mop_growPush` hands the fresh block back at
`heapBlockAssn`, because `mopAlloc`'s base only ever exists under an
existential.  The in-place branch is pinned, and one `hnRefine_cons_res` —
`heapBlockAssnAt_entails_heapBlockAssn`, landed in `ArrayListHeap.lean` —
weakens it.  No program runs for the weakening and no ownership is created or
destroyed: forgetting the base is an entailment.

**The packed form is not registered** (hazard, ledger E29 /
`HeapEO.lean`'s judgment call D-B1d).  `arlHAppend_dispatch` and
`arlHAppend_exec_hnr` carry no attribute and are used **by name**, in exactly
the idiom `ArrayListGrowSynth.lean` uses for `arlGrowSynth` — and for the same
concrete reason: the command contains an allocation (`mentions hpName
arlHAppendCom = true` is compiled in § 10, against
`mentions hpName arlHAppendInPlaceCom = false`), so a database entry for it
would let the frame inferencer drop an allocation into a loop body.  The three
new *operator* rules that are registered — `hnr_arlSucc`, `hnr_arlHNewCap`,
`hnr_arlBlockMove` — are straight-line, allocation-free, and stated at the
**pinned** assertion or at `natAssn`; none of them mentions the packed form.

## What `MERGE` had to say, and it is not "nothing"

The two branches disagree about exactly three things, and the merged
assertion says so rather than hiding it:

* **which cell still names the live block.**  In place, `bc`'s value is dead
  (the block is now reached through `dc`); after growth, `bc` still holds the
  *old* base.  Both weaken to `junkCell "bc"`.
* **where the allocator's availability starts.**  In place it is still
  `avail hp (2·cap + k)`; after growth it is `avail (hp + 2·cap) k`.
* **whether a superseded block is still allocated.**  In place, none; after
  growth, `sp ↦ₕ s.buffer` — the leak `ArrayList.lean`'s
  `arlAllocatedMany_live_bounded` bounds, and which A.3's LIFO `free` cannot
  reclaim (`free_nontop_false`).

The last two are one assertion, `arlAppendResidue k`: *at least `k` cells of
availability somewhere, and at most one superseded block.*  Both branches
entail it (`avail_entails_residue`, `avail_dead_entails_residue`), and it is
the honest post — an append may or may not have allocated, and the caller
cannot tell which without the branch.

## Tightness, and why it is an invariant rather than a precondition

`arlAppendTotal` has **three** branches: push in place, *logically* double the
capacity inside a physically larger buffer, and allocate-copy-push.  The
middle one exists only when the caller owns more storage than its capacity
advertises — and a heap block owns exactly what was allocated for it.  So the
heap-native dispatch is two-way, and what makes that faithful is
`arlTight s : s.capacity = s.buffer.length`.

It is not a precondition smuggled back in (hazard: the whole point of
`ef7a06c`).  It is an **invariant**: `arlAppendTotal_tight` proves append
preserves it, and `arlTight_no_double` proves it kills the middle branch.  A
caller that builds its array list with the allocator has it for free.  The
compiled control `arlPushGrown ⟨replicate 8 0, 2, 2⟩ 5 ≠
arlAppendTotal ⟨replicate 8 0, 2, 2⟩ 5` shows what it is doing: at a *slack*
state the two models genuinely disagree, so the hypothesis is load-bearing and
not decoration.

The *dispatch itself* introduces no caller obligation: the guard `len < cap`
is internal, both branches are total, and `arlHAppend_exec_hnr` holds at every
`Wf`, tight state and every element.

## The cost, measured

| branch | `ite` | `mul` | `while` | `copy` | `const` | `skip` | `aset` | `aget` | `add` |
|---|---|---|---|---|---|---|---|---|---|
| in place | 1 | 1 | 0 | 1 | 0 | 2 | 1 | 0 | 2 |
| growth (`n` live) | 1 | 1 | n+1 | 5 | 1 | 2 | n+1 | n | 2n+3 |

`arlHAppendMachineN` is that table; `arlHAppendRaw_eq` proves it is what the
*judgment* pays (through `arlHAppendInPlaceN_toE` / `arlHAppendGrowN_toE`,
which go back to the landed `arlAllocN_toE`, `arlBlitSetupN_toE`,
`arlBlitN_toE`), and § 10 `#guard`s it against what the *emitted program*
charges on a concrete heap, on both branches.  Ledger **F11**, fifth
appearance: **it matched, exactly, on both branches, with nothing adjusted.**

`dynRate` is **untouched and still dominates** — `arlHAppendMachineN_dominated`
— so the amortized headline transfers verbatim:
`arlHAppendMachine_amortized_ir` says the emitted program's cost plus the new
potential is at most the length- and capacity-free constant
`arlIrAdvertisedCost` plus the old potential.  No constant in
`ArrayListCash.lean` needed bumping, and that file is not edited.  The
dispatch is in fact *cheaper* than the named-array adapter's
`arlAppendMachineN` on every currency except `ir.copy` on growth (5 against 5)
and `ir.add` in place (2 against 1) — the `+ir.add` is D-B1c's address
arithmetic, which `ArrayListHeap.lean` priced.

## What is *not* touched

`arlAppendOp_refines` is unchanged — still `@[sepref_fref_thms]` over
`arrayListRel` at precondition `fun _ : List ℕ => True`, `arrayListReadyRel`
still deleted — and `arlHAppend_leaves_append_unchanged` re-checks
`ArrayListCash.lean`'s compiled guard as a term of this file.  `ArrayList.lean`,
`ArrayListCash.lean`, `ArrayListGrow.lean`, `ArrayListGrowSynth.lean` and
`ArrayListHeap.lean` are all unedited: this file is additive.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## 1. Tightness -/

/-- A heap-backed array list owns exactly its capacity. -/
def arlTight (s : ArrayList) : Prop := s.capacity = s.buffer.length

instance (s : ArrayList) : Decidable (arlTight s) := by unfold arlTight; infer_instance

theorem arlTight_no_double {s : ArrayList} (hwf : s.Wf) (ht : arlTight s) :
    ¬ 2 * s.capacity ≤ s.buffer.length := by
  obtain ⟨hc, -, -⟩ := hwf
  rw [arlTight] at ht
  omega

theorem arlAppendTotal_tight {s : ArrayList} {x : ℕ} (hwf : s.Wf) (ht : arlTight s) :
    arlTight (arlAppendTotal s x) := by
  obtain ⟨hc, hlc, hcb⟩ := hwf
  rw [arlTight] at ht
  by_cases h : s.length < s.capacity
  · rw [arlAppendTotal_of_some (t := ⟨s.buffer.set s.length x, s.length + 1, s.capacity⟩)
      (by simp [boundedPush, h])]
    simpa [arlTight] using ht
  · have hnone : boundedPush s x = none := by
      simp only [boundedPush, if_neg h]
      rw [if_neg (by omega)]
    rw [arlAppendTotal_of_none hnone, arlTight, arlPushGrown, arlGrow]
    simp only [List.length_set, List.length_append, List.length_replicate,
      BoundedArray.active, List.length_take]
    omega

/-! ## 2. Three small operations -/

noncomputable def arlSucc (n : ℕ) : NRest ℕ ECost := mopBinop .add n 1

theorem arlSucc_rest (n : ℕ) :
    arlSucc n = NRest.consume (NRest.returnT (n + 1)) (irUnit Currency.add) := by
  rw [arlSucc, mopBinop_def, Imp.Bop.apply_add, binopCurrency_add]

@[sepref_fr_rules] private theorem hnr_arlSucc (len one : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ hnCtxt natAssn 1 one)
      (.binop .add len len one) (hnCtxt natAssn 1 one) len natAssn (arlSucc n) := by
  unfold arlSucc
  exact hnr_mop_binop_self .add len one n 1

attribute [irreducible] arlSucc

/-- `cap := nc`: overwrite the capacity cell with the doubled value. -/
noncomputable def arlHNewCap (_old new : ℕ) : NRest ℕ ECost := mopCopy new

theorem arlHNewCap_def (old new : ℕ) :
    arlHNewCap old new = NRest.consume (NRest.returnT new) (irUnit Currency.copy) := rfl

@[sepref_fr_rules] private theorem hnr_arlHNewCap (cap nc : String) (old new : ℕ) :
    hnRefine (hnCtxt natAssn old cap ∗ hnCtxt natAssn new nc) (.copy cap nc)
      (hnCtxt natAssn new nc) cap natAssn (arlHNewCap old new) := by
  unfold arlHNewCap
  exact hnRefine_cons_pre (hnr_mop_copy cap nc new)
    (conj_entails_mono (natAssn_entails_junkCell old cap) (entails_refl _))

attribute [irreducible] arlHNewCap

/-- `dst := src` at a **pinned** block: the base pointer is copied into a
second cell and the range travels with it.  The base does not move — this is
not a repacking rule (ledger E29) and the packed form does not occur in it. -/
noncomputable def arlBlockMove (xs : List Val) : NRest (List Val) ECost :=
  NRest.consume (NRest.returnT xs) (irUnit Currency.copy)

theorem arlBlockMove_def (xs : List Val) :
    arlBlockMove xs = NRest.consume (NRest.returnT xs) (irUnit Currency.copy) := rfl

theorem blockMove_junk_rule (dst src : String) (p : ℕ) (xs : List Val) :
    irHtriple (¤(irUnit Currency.copy) ∗ (junkCell dst ∗ hnCtxt (heapBlockAssnAt p) xs src))
      (.copy dst src)
      (junkCell src ∗ heapBlockAssnAt p xs dst) := by
  rw [show (¤(irUnit Currency.copy) ∗ (junkCell dst ∗ hnCtxt (heapBlockAssnAt p) xs src))
      = junkCell dst ∗ (¤(irUnit Currency.copy) ∗ hnCtxt (heapBlockAssnAt p) xs src) from by
    ac_rfl]
  refine irHtriple_junk fun v => ?_
  have hcopy : irTriple (¤¤Currency.copy 1 ∗ (dst ↦ᵥ v) ∗ (src ↦ᵥ p) ∗ (p ↦ₕ xs))
      (.copy dst src) ((dst ↦ᵥ p) ∗ (src ↦ᵥ p) ∗ (p ↦ₕ xs)) := by
    have h := copy_triple dst src v p
    ir_frame h
  rw [show ((dst ↦ᵥ v) ∗ (¤(irUnit Currency.copy) ∗ hnCtxt (heapBlockAssnAt p) xs src))
      = (¤¤Currency.copy 1 ∗ (dst ↦ᵥ v) ∗ (src ↦ᵥ p) ∗ (p ↦ₕ xs)) from by
    rw [costCredits_one]
    simp only [hnCtxt_def, heapBlockAssnAt_def]; ac_rfl]
  refine cons_rule hcopy.gc (fun _ h => h) (fun _ s hs => ?_)
  revert hs
  refine conj_entails_mono ?_ (entails_refl GC) s
  rw [show ((dst ↦ᵥ p) ∗ (src ↦ᵥ p) ∗ (p ↦ₕ xs))
      = ((src ↦ᵥ p) ∗ (dst ↦ᵥ p) ∗ (p ↦ₕ xs)) from by ac_rfl]
  exact conj_entails_mono (fun _ hh => ⟨p, hh⟩) (entails_refl _)

@[sepref_fr_rules]
theorem hnr_arlBlockMove (dst src : String) (p : ℕ) (xs : List Val) :
    hnRefine (junkCell dst ∗ hnCtxt (heapBlockAssnAt p) xs src) (.copy dst src)
      (junkCell src) dst (heapBlockAssnAt p) (arlBlockMove xs) :=
  hnRefineI_spect (blockMove_junk_rule dst src p xs)

/-! ## 3. The two branches -/

noncomputable def arlHAppendInPlaceRaw (p : ℕ) (buffer : List Val) (n cap x : ℕ) :
    NRest (List Val × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopHaddr p n) fun a =>
    NRest.bindT (mopHaset p buffer a x) fun buffer' =>
      NRest.bindT (arlSucc n) fun n' =>
        NRest.bindT (arlBlockMove buffer') fun buffer'' =>
          NRest.bindT (mopPair n' cap) fun md => mopPair buffer'' md

set_option maxHeartbeats 1000000 in
sepref_synth arlHAppendInPlaceSynth (bc len cap xc one adr dc : String)
    (p : ℕ) (buffer : List Val) (n c x : ℕ) :
  hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn x xc ∗ hnCtxt natAssn 1 one ∗
      junkCell adr ∗ junkCell dc)
    _ _ (dc, (len, cap)) (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn)
    (arlHAppendInPlaceRaw p buffer n c x)

noncomputable def arlHAppendGrowRaw (s : ArrayList) (x : ℕ) :
    NRest (List Val × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopAlloc (2 * s.capacity)) fun blk =>
    NRest.bindT (mopGrowPush blk s.buffer s.length x) fun buffer' =>
      NRest.bindT (arlSucc s.length) fun n' =>
        NRest.bindT (arlHNewCap s.capacity (2 * s.capacity)) fun cap' =>
          NRest.bindT (mopPair n' cap') fun md => mopPair buffer' md

set_option maxHeartbeats 1000000 in
sepref_synth arlHAppendGrowSynth (sp hp k x : ℕ) (s : ArrayList) :
  hnRefine (junkCell "pc" ∗ avail hp (2 * s.capacity + k) ∗
      hnCtxt natAssn (2 * s.capacity) "nc" ∗
      junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ junkCell "one" ∗ junkCell "di" ∗
      junkCell "dc" ∗ hnCtxt natAssn sp "bc" ∗ hnCtxt natAssn s.length "len" ∗
      (sp ↦ₕ s.buffer) ∗ hnCtxt natAssn x "xc" ∗ hnCtxt natAssn s.capacity "cap")
    _ _ ("dc", ("len", "cap")) (heapBlockAssn ×ₐ natAssn ×ₐ natAssn)
    (arlHAppendGrowRaw s x)

/-! ## 4. The residue, and the merged assertion -/

/-- At most one superseded block. -/
def deadHeapBlock : Option (ℕ × List Val) → Assn
  | none => (□ : Assn)
  | some q => (q.1 ↦ₕ q.2)

/-- What an append leaves the caller besides the array list: at least `k`
cells of availability, and at most one superseded block. -/
def arlAppendResidue (k : ℕ) : Assn :=
  sepEx fun r : ℕ × ℕ × Option (ℕ × List Val) =>
    avail r.1 (k + r.2.1) ∗ deadHeapBlock r.2.2

theorem avail_entails_residue (h k j : ℕ) : avail h (j + k) ⊢ arlAppendResidue k := by
  intro st hs
  refine ⟨(h, j, none), ?_⟩
  show (avail h (k + j) ∗ deadHeapBlock none) st
  rw [deadHeapBlock, sepConj_emp, Nat.add_comm k j]
  exact hs

theorem avail_dead_entails_residue (h k q : ℕ) (ys : List Val) :
    avail h k ∗ (q ↦ₕ ys) ⊢ arlAppendResidue k := by
  intro st hs
  refine ⟨(h, 0, some (q, ys)), ?_⟩
  show (avail h (k + 0) ∗ deadHeapBlock (some (q, ys))) st
  rw [deadHeapBlock, Nat.add_zero]
  exact hs

/-! ## 5. The dispatch -/

def arlHAppendInPlaceCom : Com :=
  (Com.binop .add "adr" "bc" "len").seq
    ((Com.aset heapName "adr" "xc").seq
      ((Com.binop .add "len" "len" "one").seq
        ((Com.copy "dc" "bc").seq (Com.skip.seq Com.skip))))

/-- **The append command**: double the capacity into the scratch cell, test
whether the live length still fits, and take the in-place branch or the
growth branch. -/
def arlHAppendCom : Com :=
  (Com.binop .mul "nc" "cap" "two").seq
    (Com.ite (.lt (.cell "len") (.cell "cap"))
      arlHAppendInPlaceCom arlHAppendGrowSynth_impl)

noncomputable def arlHAppendRaw (sp : ℕ) (s : ArrayList) (x : ℕ) :
    NRest (List Val × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopBinop .mul s.capacity 2) fun _ =>
    irIf (decide (s.length < s.capacity))
      (arlHAppendInPlaceRaw sp s.buffer s.length s.capacity x)
      (arlHAppendGrowRaw s x)

def arlHAppendPre (sp hp k x : ℕ) (s : ArrayList) : Assn :=
  hnCtxt (heapBlockAssnAt sp) s.buffer "bc" ∗ hnCtxt natAssn s.length "len" ∗
    hnCtxt natAssn s.capacity "cap" ∗ hnCtxt natAssn x "xc" ∗
    hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 2 "two" ∗
    junkCell "adr" ∗ junkCell "dc" ∗ junkCell "pc" ∗ junkCell "nc" ∗
    junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ junkCell "di" ∗
    avail hp (2 * s.capacity + k)

def arlHAppendPost (k x c : ℕ) : Assn :=
  hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 2 "two" ∗ hnCtxt natAssn x "xc" ∗
    hnCtxt natAssn (2 * c) "nc" ∗
    junkCell "bc" ∗ junkCell "adr" ∗ junkCell "pc" ∗ junkCell "t" ∗
    junkCell "si" ∗ junkCell "se" ∗ junkCell "di" ∗ arlAppendResidue k

/-- The in-place branch's frame. -/
private def ipFrame (hp k c : ℕ) : Assn :=
  hnCtxt natAssn (2 * c) "nc" ∗ hnCtxt natAssn 2 "two" ∗ junkCell "pc" ∗
    junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ junkCell "di" ∗
    avail hp (2 * c + k)

private def grFrame : Assn := junkCell "adr" ∗ hnCtxt natAssn 2 "two"

/-- The in-place branch's leftover. -/
private def ipPost (x : ℕ) : Assn :=
  junkCell "bc" ∗ hnCtxt natAssn 1 "one" ∗ junkCell "adr" ∗ hnCtxt natAssn x "xc"

/-- The growth branch's leftover. -/
private def grPost (sp hp k x : ℕ) (s : ArrayList) : Assn :=
  hnCtxt natAssn (2 * s.capacity) "nc" ∗ hnCtxt natAssn 1 "one" ∗ junkCell "t" ∗
    hnCtxt natAssn (sp + s.length) "si" ∗ hnCtxt natAssn (sp + s.length) "se" ∗
    junkCell "di" ∗ junkCell "pc" ∗ hnCtxt natAssn sp "bc" ∗ (sp ↦ₕ s.buffer) ∗
    hnCtxt natAssn x "xc" ∗ avail (hp + 2 * s.capacity) k

/-- **The merge, at the packed assertion.**  The two branches disagree about
three things and only three: which cell still names the live block, where the
allocator's availability now starts, and whether a superseded block is still
allocated.  The first two merge to junk / an existential base; the third is
the whole content of `arlAppendResidue`. -/
theorem arlHAppendMerge (sp hp k x : ℕ) (s : ArrayList) :
    MERGE (ipPost x ∗ ipFrame hp k s.capacity) (grPost sp hp k x s ∗ grFrame)
      (arlHAppendPost k x s.capacity) := by
  constructor
  · rw [show (ipPost x ∗ ipFrame hp k s.capacity)
        = ((("one" ↦ᵥ 1) ∗ ("two" ↦ᵥ 2) ∗ ("xc" ↦ᵥ x) ∗ ("nc" ↦ᵥ (2 * s.capacity)) ∗
            junkCell "bc" ∗ junkCell "adr" ∗ junkCell "pc" ∗ junkCell "t" ∗
            junkCell "si" ∗ junkCell "se" ∗ junkCell "di") ∗
          avail hp (2 * s.capacity + k)) from by
      simp only [ipPost, ipFrame, hnCtxt_def, natAssn_def]; ac_rfl,
      show arlHAppendPost k x s.capacity
        = ((("one" ↦ᵥ 1) ∗ ("two" ↦ᵥ 2) ∗ ("xc" ↦ᵥ x) ∗ ("nc" ↦ᵥ (2 * s.capacity)) ∗
            junkCell "bc" ∗ junkCell "adr" ∗ junkCell "pc" ∗ junkCell "t" ∗
            junkCell "si" ∗ junkCell "se" ∗ junkCell "di") ∗
          arlAppendResidue k) from by
      simp only [arlHAppendPost, hnCtxt_def, natAssn_def]; ac_rfl]
    exact conj_entails_mono (entails_refl _) (avail_entails_residue hp k (2 * s.capacity))
  · rw [show (grPost sp hp k x s ∗ grFrame)
        = ((("one" ↦ᵥ 1) ∗ ("two" ↦ᵥ 2) ∗ ("xc" ↦ᵥ x) ∗ ("nc" ↦ᵥ (2 * s.capacity)) ∗
            ("bc" ↦ᵥ sp) ∗ junkCell "adr" ∗ junkCell "pc" ∗ junkCell "t" ∗
            ("si" ↦ᵥ (sp + s.length)) ∗ ("se" ↦ᵥ (sp + s.length)) ∗ junkCell "di") ∗
          (avail (hp + 2 * s.capacity) k ∗ (sp ↦ₕ s.buffer))) from by
      simp only [grPost, grFrame, hnCtxt_def, natAssn_def]; ac_rfl,
      show arlHAppendPost k x s.capacity
        = ((("one" ↦ᵥ 1) ∗ ("two" ↦ᵥ 2) ∗ ("xc" ↦ᵥ x) ∗ ("nc" ↦ᵥ (2 * s.capacity)) ∗
            junkCell "bc" ∗ junkCell "adr" ∗ junkCell "pc" ∗ junkCell "t" ∗
            junkCell "si" ∗ junkCell "se" ∗ junkCell "di") ∗
          arlAppendResidue k) from by
      simp only [arlHAppendPost, hnCtxt_def, natAssn_def]; ac_rfl]
    refine conj_entails_mono ?_ (avail_dead_entails_residue _ _ _ _)
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right ?_)))
    refine conj_entails_mono (natAssn_entails_junkCell sp "bc") ?_
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
    exact conj_entails_mono (natAssn_entails_junkCell (sp + s.length) "si")
      (conj_entails_mono (natAssn_entails_junkCell (sp + s.length) "se") (entails_refl _))

/-! ## 6. The dispatch rule -/

private def d1Frame (sp hp k x : ℕ) (s : ArrayList) : Assn :=
  hnCtxt (heapBlockAssnAt sp) s.buffer "bc" ∗ hnCtxt natAssn s.length "len" ∗
    hnCtxt natAssn x "xc" ∗ hnCtxt natAssn 1 "one" ∗
    junkCell "adr" ∗ junkCell "dc" ∗ junkCell "pc" ∗
    junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ junkCell "di" ∗
    avail hp (2 * s.capacity + k)

private def iteCtxt (sp hp k x : ℕ) (s : ArrayList) : Assn :=
  hnCtxt natAssn (2 * s.capacity) "nc" ∗
    ((hnCtxt natAssn s.capacity "cap" ∗ hnCtxt natAssn 2 "two") ∗ d1Frame sp hp k x s)

private theorem packed_res (p : ℕ) (a : List Val × (ℕ × ℕ))
    (e : String × (String × String)) :
    (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn) a e ⊢
      (heapBlockAssn ×ₐ natAssn ×ₐ natAssn) a e :=
  conj_entails_mono (heapBlockAssnAt_entails_heapBlockAssn p a.1 e.1) (entails_refl _)

private theorem ite_cond (sp hp k x : ℕ) (s : ArrayList) :
    CondRefine (iteCtxt sp hp k x s) (.lt (.cell "len") (.cell "cap"))
      (decide (s.length < s.capacity)) := by
  have h : iteCtxt sp hp k x s
      = (hnCtxt natAssn s.length "len" ∗ hnCtxt natAssn s.capacity "cap") ∗
        (hnCtxt natAssn (2 * s.capacity) "nc" ∗ hnCtxt natAssn 2 "two" ∗
          hnCtxt (heapBlockAssnAt sp) s.buffer "bc" ∗ hnCtxt natAssn x "xc" ∗
          hnCtxt natAssn 1 "one" ∗ junkCell "adr" ∗ junkCell "dc" ∗ junkCell "pc" ∗
          junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ junkCell "di" ∗
          avail hp (2 * s.capacity + k)) := by
    simp only [iteCtxt, d1Frame]; ac_rfl
  exact CondRefine.cons (fun st hs => h ▸ hs) (condRefine_lt_cells _ _ _ _).frame

private theorem ite_pre_inplace (sp hp k x : ℕ) (s : ArrayList) :
    iteCtxt sp hp k x s ⊢
      (hnCtxt (heapBlockAssnAt sp) s.buffer "bc" ∗ hnCtxt natAssn s.length "len" ∗
        hnCtxt natAssn s.capacity "cap" ∗ hnCtxt natAssn x "xc" ∗
        hnCtxt natAssn 1 "one" ∗ junkCell "adr" ∗ junkCell "dc") ∗
      ipFrame hp k s.capacity := by
  have h : iteCtxt sp hp k x s
      = (hnCtxt (heapBlockAssnAt sp) s.buffer "bc" ∗ hnCtxt natAssn s.length "len" ∗
          hnCtxt natAssn s.capacity "cap" ∗ hnCtxt natAssn x "xc" ∗
          hnCtxt natAssn 1 "one" ∗ junkCell "adr" ∗ junkCell "dc") ∗
        ipFrame hp k s.capacity := by
    simp only [iteCtxt, d1Frame, ipFrame]; ac_rfl
  exact fun st hs => h ▸ hs

private theorem ite_pre_grow (sp hp k x : ℕ) (s : ArrayList) :
    iteCtxt sp hp k x s ⊢
      (junkCell "pc" ∗ avail hp (2 * s.capacity + k) ∗
        hnCtxt natAssn (2 * s.capacity) "nc" ∗
        junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ junkCell "one" ∗ junkCell "di" ∗
        junkCell "dc" ∗ hnCtxt natAssn sp "bc" ∗ hnCtxt natAssn s.length "len" ∗
        (sp ↦ₕ s.buffer) ∗ hnCtxt natAssn x "xc" ∗ hnCtxt natAssn s.capacity "cap") ∗
      grFrame := by
  have h : iteCtxt sp hp k x s
      = ((junkCell "pc" ∗ avail hp (2 * s.capacity + k) ∗
          hnCtxt natAssn (2 * s.capacity) "nc" ∗
          junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ hnCtxt natAssn 1 "one" ∗
          junkCell "di" ∗ junkCell "dc" ∗ hnCtxt natAssn sp "bc" ∗
          hnCtxt natAssn s.length "len" ∗ (sp ↦ₕ s.buffer) ∗ hnCtxt natAssn x "xc" ∗
          hnCtxt natAssn s.capacity "cap") ∗ grFrame) := by
    simp only [iteCtxt, d1Frame, grFrame, hnCtxt_def, natAssn_def, heapBlockAssnAt_def]
    ac_rfl
  refine entails_trans (fun st hs => h ▸ hs) ?_
  refine conj_entails_mono ?_ (entails_refl _)
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
  exact conj_entails_mono (natAssn_entails_junkCell 1 "one") (entails_refl _)

/-- **The append dispatch, stated at the packed assertion and never
registered** (hazard: ledger E29 / `HeapEO.lean`'s D-B1d).  It is used *by
name*, in exactly the idiom `ArrayListGrowSynth.lean` uses for
`arlGrowSynth`: the composed command is not a database entry, because the
growth branch it contains allocates. -/
theorem arlHAppend_dispatch (sp hp k x : ℕ) (s : ArrayList) :
    hnRefine (arlHAppendPre sp hp k x s) arlHAppendCom (arlHAppendPost k x s.capacity)
      ("dc", ("len", "cap")) (heapBlockAssn ×ₐ natAssn ×ₐ natAssn)
      (arlHAppendRaw sp s x) := by
  rw [arlHAppendCom, arlHAppendRaw]
  refine hnr_seq (Γ₁ := (hnCtxt natAssn s.capacity "cap" ∗ hnCtxt natAssn 2 "two") ∗
      d1Frame sp hp k x s) (x := "nc") (Rh := natAssn) ?_ ?_
  · refine hnRefine_frame (F := d1Frame sp hp k x s)
      (hnr_mop_binop .mul "nc" "cap" "two" s.capacity 2) ?_
    have h : arlHAppendPre sp hp k x s
        = (junkCell "nc" ∗ hnCtxt natAssn s.capacity "cap" ∗ hnCtxt natAssn 2 "two") ∗
          d1Frame sp hp k x s := by simp only [arlHAppendPre, d1Frame]; ac_rfl
    exact fun st hs => h ▸ hs
  · intro a ha
    have hrest : mopBinop .mul s.capacity 2
        = NRest.rest (NRest.single (s.capacity * 2)
            ((irUnit Currency.mul : ECost) : WithBot ECost)) := by
      rw [mopBinop_def, Imp.Bop.apply_mul, binopCurrency_mul, NRest.consume_returnT]
    have hval : a = s.capacity * 2 := by
      rw [hrest, returnT_le_rest_iff] at ha
      by_contra hne
      rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at ha
      exact WithBot.coe_ne_bot ha
    subst hval
    rw [Nat.mul_comm s.capacity 2]
    show hnRefine (iteCtxt sp hp k x s) _ _ _ _ _
    refine hnr_If (Γt := ipPost x ∗ ipFrame hp k s.capacity)
      (Γe := grPost sp hp k x s ∗ grFrame) (ite_cond sp hp k x s) (fun _ => ?_)
      (fun _ => ?_) (arlHAppendMerge sp hp k x s)
    · exact hnRefine_frame (F := ipFrame hp k s.capacity)
        (hnRefine_cons_res
          (arlHAppendInPlaceSynth "bc" "len" "cap" "xc" "one" "adr" "dc" sp s.buffer
            s.length s.capacity x) (packed_res sp))
        (ite_pre_inplace sp hp k x s)
    · exact hnRefine_frame (F := grFrame) (arlHAppendGrowSynth sp hp k x s)
        (ite_pre_grow sp hp k x s)


/-! ## 7. What the dispatch costs -/

/-- The in-place branch, instruction by instruction: address, write, length
bump, block move, and the two `skip`s that pack the observable triple. -/
def arlHAppendInPlaceN : IrVecN := ⟨0, 0, 0, 1, 0, 2, 1, 0, 2⟩

/-- The growth branch: the allocator, the cursor block, the copy loop, and
the element write plus the same tail as the in-place branch. -/
def arlHAppendGrowN (n : ℕ) : IrVecN :=
  arlAllocN + arlBlitSetupN + arlBlitN n + ⟨0, 0, 0, 1, 0, 2, 1, 0, 1⟩

/-- The dispatch itself: the doubling multiplication and the branch test. -/
def arlHAppendDispatchN : IrVecN := ⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩

/-- **What one heap-native `arlAppendTotal` really costs the machine.** -/
def arlHAppendMachineN (s : ArrayList) : IrVecN :=
  arlHAppendDispatchN +
    (if s.length < s.capacity then arlHAppendInPlaceN else arlHAppendGrowN s.length)

theorem arlHAppendMachineN_space (s : ArrayList) (h : s.length < s.capacity) :
    arlHAppendMachineN s = ⟨1, 1, 0, 1, 0, 2, 1, 0, 2⟩ := by
  rw [arlHAppendMachineN, if_pos h]
  refine IrVecN.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [arlHAppendDispatchN, arlHAppendInPlaceN]

theorem arlHAppendMachineN_grow (s : ArrayList) (h : ¬ s.length < s.capacity) :
    arlHAppendMachineN s =
      ⟨1, 1, s.length + 1, 5, 1, 2, s.length + 1, s.length, 2 * s.length + 3⟩ := by
  rw [arlHAppendMachineN, if_neg h, arlHAppendGrowN]
  refine IrVecN.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (simp [arlHAppendDispatchN, arlAllocN, arlBlitSetupN, arlBlitN]; try omega)

/-! ### The prices as `ECost`, against what the mops charge -/

noncomputable def arlHInPlaceCost : ECost :=
  irUnit Currency.add + irUnit Currency.aset + irUnit Currency.add +
    irUnit Currency.copy + irUnit Currency.skip + irUnit Currency.skip

noncomputable def arlHGrowCost (c n : ℕ) : ECost :=
  allocCost (2 * c) + arlGrowPushCost n + irUnit Currency.add +
    irUnit Currency.copy + irUnit Currency.skip + irUnit Currency.skip

noncomputable def arlHDispatchCost : ECost := irUnit Currency.mul + irUnit Currency.ite

private theorem cost_two' (c : String) :
    (ACost.cost c (2 : ℕ∞) : ECost) = ACost.cost c 1 + ACost.cost c 1 := by
  rw [ACost.cost_add_cost]; norm_num

theorem arlHAppendInPlaceN_toE : arlHAppendInPlaceN.toE = arlHInPlaceCost := by
  rw [arlHAppendInPlaceN, arlHInPlaceCost, IrVecN.toE]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ACost.cost_zero, irUnit, cost_two']
  abel

theorem arlHAppendDispatchN_toE : arlHAppendDispatchN.toE = arlHDispatchCost := by
  rw [arlHAppendDispatchN, arlHDispatchCost, IrVecN.toE]
  simp only [Nat.cast_zero, Nat.cast_one, ACost.cost_zero, irUnit]
  abel

theorem arlHAppendGrowN_toE (c n : ℕ) : (arlHAppendGrowN n).toE = arlHGrowCost c n := by
  have htail : (⟨0, 0, 0, 1, 0, 2, 1, 0, 1⟩ : IrVecN).toE
      = irUnit Currency.copy + irUnit Currency.skip + irUnit Currency.skip +
        irUnit Currency.aset + irUnit Currency.add := by
    rw [IrVecN.toE]
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ACost.cost_zero, irUnit, cost_two']
    abel
  rw [arlHAppendGrowN, IrVecN.toE_add, IrVecN.toE_add, IrVecN.toE_add, htail,
    arlAllocN_toE (2 * c), arlBlitSetupN_toE, arlBlitN_toE, arlHGrowCost,
    arlGrowPushCost, arlGrowBlockCost]
  abel

/-! ### The raw program's value and price -/

theorem arlHAppendInPlaceRaw_eq (p : ℕ) (buffer : List Val) (n cap x : ℕ)
    (hn : n < buffer.length) :
    arlHAppendInPlaceRaw p buffer n cap x =
      NRest.consume (NRest.returnT (buffer.set n x, (n + 1, cap))) arlHInPlaceCost := by
  have hset : mopHaset p buffer (p + n) x
      = NRest.consume (NRest.returnT (buffer.set n x)) (irUnit Currency.aset) := by
    rw [mopHaset_def,
      NRest.assert_pos (show p ≤ p + n ∧ p + n - p < buffer.length from
        ⟨Nat.le_add_right _ _, by omega⟩),
      NRest.returnT_bindT, Nat.add_sub_cancel_left]
  rw [arlHAppendInPlaceRaw, mopHaddr_def, Lax13Proofs.Refine.Iicf.bindT_unit, hset,
    Lax13Proofs.Refine.Iicf.bindT_unit, arlSucc_rest, Lax13Proofs.Refine.Iicf.bindT_unit,
    arlBlockMove_def, Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def, arlHInPlaceCost]
  simp only [NRest.consume_consume]
  congr 1
  abel

theorem arlHAppendGrowRaw_eq (s : ArrayList) (x : ℕ) (hwf : s.Wf) :
    arlHAppendGrowRaw s x =
      NRest.consume (NRest.returnT ((arlPushGrown s x).buffer, (s.length + 1, 2 * s.capacity)))
        (arlHGrowCost s.capacity s.length) := by
  obtain ⟨hc, hlc, hcb⟩ := hwf
  rw [arlHAppendGrowRaw, mopAlloc_def, Lax13Proofs.Refine.Iicf.bindT_unit, mopGrowPush,
    NRest.assert_pos (⟨by omega, by simpa using by omega⟩ :
      s.length ≤ s.buffer.length ∧ s.length < (List.replicate (2 * s.capacity) 0).length),
    NRest.returnT_bindT, Lax13Proofs.Refine.Iicf.bindT_unit, arlSucc_rest,
    Lax13Proofs.Refine.Iicf.bindT_unit, arlHNewCap_def,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def, arlGrowCopy_value, arlHGrowCost]
  simp only [NRest.consume_consume]
  congr 1
  abel

theorem arlHAppendRaw_eq (sp : ℕ) (s : ArrayList) (x : ℕ) (hwf : s.Wf) (ht : arlTight s) :
    arlHAppendRaw sp s x =
      NRest.consume (NRest.returnT ((arlAppendTotal s x).buffer,
        ((arlAppendTotal s x).length, (arlAppendTotal s x).capacity)))
        (arlHAppendMachineN s).toE := by
  have hmul : mopBinop .mul s.capacity 2
      = NRest.consume (NRest.returnT (s.capacity * 2)) (irUnit Currency.mul) := by
    rw [mopBinop_def, Imp.Bop.apply_mul, binopCurrency_mul]
  rw [arlHAppendRaw, hmul, Lax13Proofs.Refine.Iicf.bindT_unit]
  by_cases h : s.length < s.capacity
  · obtain ⟨hc, hlc, hcb⟩ := hwf
    have hval : arlAppendTotal s x = ⟨s.buffer.set s.length x, s.length + 1, s.capacity⟩ :=
      arlAppendTotal_of_some (by simp [boundedPush, h])
    rw [show decide (s.length < s.capacity) = true from by simp [h], irIf_true,
      arlHAppendInPlaceRaw_eq sp s.buffer s.length s.capacity x (by omega), hval,
      arlHAppendMachineN, if_pos h, IrVecN.toE_add, arlHAppendDispatchN_toE,
      arlHAppendInPlaceN_toE, arlHDispatchCost]
    simp only [NRest.consume_consume]
    congr 1
    abel
  · have hnone : boundedPush s x = none := by
      simp only [boundedPush, if_neg h]
      exact if_neg (arlTight_no_double hwf ht)
    have hval : arlAppendTotal s x = arlPushGrown s x := arlAppendTotal_of_none hnone
    rw [show decide (s.length < s.capacity) = false from by simp [h], irIf_false,
      arlHAppendGrowRaw_eq s x hwf, hval, arlHAppendMachineN, if_neg h, IrVecN.toE_add,
      arlHAppendDispatchN_toE, arlHAppendGrowN_toE s.capacity, arlHDispatchCost]
    simp only [NRest.consume_consume]
    congr 1
    abel

/-! ## 8. The executable rule -/

/-- The dispatched append, at the price the emitted program charges. -/
noncomputable def arlHAppendExecSpec (s : ArrayList) (x : ℕ) :
    NRest (List Val × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT ((arlAppendTotal s x).buffer,
    ((arlAppendTotal s x).length, (arlAppendTotal s x).capacity)))
    (arlHAppendMachineN s).toE

/-- **End-to-end append, as one command.**  Deliberately *not* registered
(ledger E29): the command contains an allocation, exactly as `arlGrowSynth`
does, so it is reached by naming it. -/
theorem arlHAppend_exec_hnr (sp hp k x : ℕ) (s : ArrayList) (hwf : s.Wf) (ht : arlTight s) :
    hnRefine (arlHAppendPre sp hp k x s) arlHAppendCom (arlHAppendPost k x s.capacity)
      ("dc", ("len", "cap")) (heapBlockAssn ×ₐ natAssn ×ₐ natAssn)
      (arlHAppendExecSpec s x) := by
  rw [arlHAppendExecSpec, ← arlHAppendRaw_eq sp s x hwf ht]
  exact arlHAppend_dispatch sp hp k x s

/-- The bridge to the cost-silent list interface: the value the command
leaves is `arlAppendTotal`'s, and `ArrayList.lean`'s own
`arlAppendTotal_refines` is what takes it to `xs ++ [x]`.  Nothing is
re-derived. -/
theorem arlHAppendExecSpec_refines {s : ArrayList} {xs : List ℕ} {x : ℕ}
    (h : (s, xs) ∈ arrayListRel) :
    arlHAppendExecSpec s x = NRest.consume (NRest.returnT ((arlAppendTotal s x).buffer,
        ((arlAppendTotal s x).length, (arlAppendTotal s x).capacity)))
        (arlHAppendMachineN s).toE ∧
      (arlAppendTotal s x, xs ++ [x]) ∈ arrayListRel :=
  ⟨rfl, arlAppendTotal_refines h⟩

/-! ## 9. The amortized shape survives the dispatch -/

theorem arlHAppendMachineN_dominated (s : ArrayList) (hwf : s.Wf) (ht : arlTight s) :
    IrVecN.Dominates (arlHAppendMachineN s) (dynExchangeN (arlAppendCostN s)) := by
  by_cases h : s.length < s.capacity
  · rw [arlHAppendMachineN_space s h,
      arlAppendCostN_of_some (c := ⟨1, 1, 1, 0⟩) (by simp [boundedPushCostN, h]),
      dynExchangeN_closed]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · rw [arlHAppendMachineN_grow s h,
      arlAppendCostN_of_none (by simp [boundedPushCostN, h, arlTight_no_double hwf ht]),
      dynExchangeN_closed]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp; try omega)

/-- **The headline holds of the dispatched command.**  What the *emitted
program* charges for one append, plus the new potential, is at most the
length- and capacity-free constant `arlIrAdvertisedCost` plus the old
potential.  The exchange rate `dynRate` is the landed one, unchanged. -/
theorem arlHAppendMachine_amortized_ir (s : ArrayList) (x : ℕ) (hwf : s.Wf)
    (ht : arlTight s) :
    (arlHAppendMachineN s).toE + arlIrPotential (arlAppendTotal s x) ≤
      arlIrAdvertisedCost + arlIrPotential s :=
  le_trans
    (add_le_add (IrVecN.toE_mono (arlHAppendMachineN_dominated s hwf ht)) (le_refl _))
    (arlAppend_amortized_ir s x hwf)

/-! ## 10. The compiled gate

The one emitted command, pinned, and run on a concrete heap on **both**
branches: the values against `arlAppendTotal`'s own model, the costs against
the predicted vectors of § 7.  Ledger **F11**: no price here is asserted, each
is compared with what the program charges.

Every negative control is a *mutilation* of the emitted command, stated as
`≠` against the correct run, so it compiles only because the mutilated program
really answers differently.  Each junk scratch value is a **legal but wrong**
heap address, so a mutilated program runs to completion instead of faulting
(the precedent is ledger E38's controls). -/

namespace ArrayListAppendGate

open Lax13Proofs.Refine.Ir.Gate (costVector readVars readArrs)

/-! ### Refute first: the pure model, before any program -/

/-- Room in the capacity. -/
def ipList : ArrayList := ⟨[5, 6, 7, 0], 3, 4⟩
/-- Physically and logically full: the append must allocate and copy. -/
def grList : ArrayList := ⟨[7, 8, 9], 3, 3⟩

#guard arlTight ipList
#guard arlTight grList
#guard arlAppendTotal ipList 42 = ⟨[5, 6, 7, 42], 4, 4⟩
#guard arlAppendTotal grList 42 = ⟨[7, 8, 9, 42, 0, 0], 4, 6⟩
-- tightness is an invariant, not a standing assumption
#guard arlTight (arlAppendTotal ipList 42)
#guard arlTight (arlAppendTotal grList 42)

-- **Tightness is load-bearing.**  At a *slack* state — spare physical buffer
-- beyond the logical capacity — `arlAppendTotal` takes its logical-doubling
-- branch, which a two-way dispatch does not have; the growth model and the
-- source model then genuinely disagree, which is why the rules carry
-- `arlTight` and why `arlTight_no_double` has to be a theorem.
#guard arlPushGrown ⟨List.replicate 8 0, 2, 2⟩ 5 ≠ arlAppendTotal ⟨List.replicate 8 0, 2, 2⟩ 5

-- The predicted vectors, and the domination that carries the amortized shape.
#guard arlHAppendMachineN ipList = ⟨1, 1, 0, 1, 0, 2, 1, 0, 2⟩
#guard arlHAppendMachineN grList = ⟨1, 1, 4, 5, 1, 2, 4, 3, 9⟩
#guard IrVecN.Dominates (arlHAppendMachineN ipList) (dynExchangeN (arlAppendCostN ipList))
#guard IrVecN.Dominates (arlHAppendMachineN grList) (dynExchangeN (arlAppendCostN grList))
-- …and the landed rate is not slack on the in-place branch's `ir.add`: two
-- machine additions against the three one `dyn.add` buys.
#guard ¬ IrVecN.Dominates (arlHAppendMachineN ipList)
  (dynExchangeN ⟨1, 1, 0, 0⟩)
#guard (List.range 20).all fun n =>
  decide (IrVecN.Dominates (arlHAppendMachineN ⟨List.replicate (n + 1) 0, n + 1, n + 1⟩)
    (dynExchangeN (arlAppendCostN ⟨List.replicate (n + 1) 0, n + 1, n + 1⟩)))

/-! ### The emitted command, pinned -/

#guard arlHAppendInPlaceCom =
  (Com.binop .add "adr" "bc" "len").seq
    ((Com.aset "$heap" "adr" "xc").seq
      ((Com.binop .add "len" "len" "one").seq
        ((Com.copy "dc" "bc").seq (Com.skip.seq Com.skip))))

#guard arlHAppendCom =
  (Com.binop .mul "nc" "cap" "two").seq
    (Com.ite (.lt (.cell "len") (.cell "cap"))
      ((Com.binop .add "adr" "bc" "len").seq
        ((Com.aset "$heap" "adr" "xc").seq
          ((Com.binop .add "len" "len" "one").seq
            ((Com.copy "dc" "bc").seq (Com.skip.seq Com.skip)))))
      (((Com.copy "pc" "$hp").seq (Com.binop .add "$hp" "$hp" "nc")).seq
        ((((Com.copy "si" "bc").seq
            ((Com.binop .add "se" "bc" "len").seq
              ((Com.const "one" 1).seq
                ((Com.copy "di" "pc").seq
                  ((Com.copy "dc" "pc").seq
                    (Com.while (.lt (.cell "si") (.cell "se"))
                      ((Com.aget "t" "$heap" "si").seq
                        ((Com.aset "$heap" "di" "t").seq
                          ((Com.binop .add "si" "si" "one").seq
                            (Com.binop .add "di" "di" "one")))))))))).seq
          (Com.aset "$heap" "di" "xc")).seq
          ((Com.binop .add "len" "len" "one").seq
            ((Com.copy "cap" "nc").seq (Com.skip.seq Com.skip))))))

/-- The run's cost as one of `ArrayListCash.lean`'s nine-currency vectors. -/
def runVec (κ : Cost) : IrVecN :=
  ⟨κ.toFun Currency.ite, κ.toFun Currency.mul, κ.toFun Currency.«while»,
    κ.toFun Currency.copy, κ.toFun Currency.const, κ.toFun Currency.skip,
    κ.toFun Currency.aset, κ.toFun Currency.aget, κ.toFun Currency.add⟩

/-! ### The in-place branch, run

`ipList`'s block sits at base `3`; the thirteen cells above index `10` are the
allocator's availability, untouched by an in-place append. -/

def ipHeap : List Val :=
  [91, 92, 93, 5, 6, 7, 0, 94, 95, 96, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def ipState : State :=
  State.ofPairs
    [("bc", 3), ("len", 3), ("cap", 4), ("xc", 42), ("one", 1), ("two", 2),
     ("adr", 9), ("dc", 99), ("pc", 98), ("nc", 97), ("t", 96), ("si", 95),
     ("se", 94), ("di", 10), (hpName, 11)]
    [(heapName, ipHeap)]

def ipOut : State × Cost := (evalFuel 40 arlHAppendCom ipState).getD (ipState, 0)

theorem ipOut_evalFuel : evalFuel 40 arlHAppendCom ipState = some ipOut := rfl

theorem ipOut_bigStep : BigStep arlHAppendCom ipState ipOut.1 ipOut.2 :=
  bigStep_of_evalFuel ipOut_evalFuel

-- The block does not move, the element lands at the old length, and the
-- allocator's bump pointer is **untouched**: nothing was allocated.
#guard readVars ipOut.1 ["dc", "len", "cap", hpName] =
  [("dc", some 3), ("len", some 4), ("cap", some 4), (hpName, some 11)]
#guard readArrs ipOut.1 [heapName] =
  [(heapName, some [91, 92, 93, 5, 6, 7, 42, 94, 95, 96, 97,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]
-- **Differentially**, against `arlAppendTotal`'s own answer.
#guard ((readArrs ipOut.1 [heapName]).head?.map fun r => ((r.2.getD []).drop 3).take 4)
  = some (arlAppendTotal ipList 42).buffer
#guard readVars ipOut.1 ["len", "cap"] =
  [("len", some (arlAppendTotal ipList 42).length),
   ("cap", some (arlAppendTotal ipList 42).capacity)]
-- …and the price is the predicted vector, on the nose.
#guard runVec ipOut.2 = arlHAppendMachineN ipList
#guard costVector ipOut.2 =
  [("ir.skip", 2), ("ir.const", 0), ("ir.copy", 1), ("ir.aget", 0), ("ir.aset", 1),
   ("ir.ite", 1), ("ir.while", 0), ("ir.add", 2), ("ir.sub", 0), ("ir.mul", 1),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! ### The growth branch, run

`grList` is physically full at base `0`; the eight cells above it are the
availability, and the fresh block is carved out of them. -/

def grHeap : List Val := [7, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0]

def grState : State :=
  State.ofPairs
    [("bc", 0), ("len", 3), ("cap", 3), ("xc", 42), ("one", 1), ("two", 2),
     ("adr", 9), ("dc", 99), ("pc", 98), ("nc", 97), ("t", 96), ("si", 95),
     ("se", 94), ("di", 93), (hpName, 3)]
    [(heapName, grHeap)]

def grOut : State × Cost := (evalFuel 80 arlHAppendCom grState).getD (grState, 0)

theorem grOut_evalFuel : evalFuel 80 arlHAppendCom grState = some grOut := rfl

theorem grOut_bigStep : BigStep arlHAppendCom grState grOut.1 grOut.2 :=
  bigStep_of_evalFuel grOut_evalFuel

-- The fresh block is at `3`, the capacity doubled, the bump pointer advanced
-- by exactly the doubled capacity, and the superseded block still readable at
-- `0` — the leak `arlAppendResidue`'s `deadHeapBlock` names.
#guard readVars grOut.1 ["dc", "len", "cap", "nc", hpName] =
  [("dc", some 3), ("len", some 4), ("cap", some 6), ("nc", some 6), (hpName, some 9)]
#guard readArrs grOut.1 [heapName] =
  [(heapName, some [7, 8, 9, 7, 8, 9, 42, 0, 0, 0, 0])]
-- **Differentially**, against `arlAppendTotal`'s own answer: an append at a
-- full buffer goes through the growth branch and produces the right buffer.
#guard ((readArrs grOut.1 [heapName]).head?.map fun r => ((r.2.getD []).drop 3).take 6)
  = some (arlAppendTotal grList 42).buffer
#guard readVars grOut.1 ["len", "cap"] =
  [("len", some (arlAppendTotal grList 42).length),
   ("cap", some (arlAppendTotal grList 42).capacity)]
#guard runVec grOut.2 = arlHAppendMachineN grList
#guard costVector grOut.2 =
  [("ir.skip", 2), ("ir.const", 1), ("ir.copy", 5), ("ir.aget", 3), ("ir.aset", 4),
   ("ir.ite", 1), ("ir.while", 4), ("ir.add", 9), ("ir.sub", 0), ("ir.mul", 1),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! ### Negative controls, each flipped and confirmed to bite -/

/-- **Control 1 — the dispatch takes the wrong branch.**  Test the live
length against the *doubled* capacity in `nc`, which is always larger: a full
buffer then takes the in-place branch and writes one past the block, leaving
the capacity unchanged and no copy at all. -/
def wrongGuardCom : Com :=
  (Com.binop .mul "nc" "cap" "two").seq
    (Com.ite (.lt (.cell "len") (.cell "nc")) arlHAppendInPlaceCom arlHAppendGrowSynth_impl)

#guard (evalFuel 80 wrongGuardCom grState).isSome
#guard readArrs ((evalFuel 80 wrongGuardCom grState).getD (grState, 0)).1 [heapName]
  ≠ readArrs grOut.1 [heapName]
#guard readVars ((evalFuel 80 wrongGuardCom grState).getD (grState, 0)).1 ["dc", "cap"]
  ≠ readVars grOut.1 ["dc", "cap"]

/-- **Control 2 — the guard reversed.**  `cap < len` sends a state with room
down the growth branch: it allocates, copies, and hands back a different base
and a different capacity, and the bump pointer moves. -/
def flipGuardCom : Com :=
  (Com.binop .mul "nc" "cap" "two").seq
    (Com.ite (.lt (.cell "cap") (.cell "len")) arlHAppendInPlaceCom arlHAppendGrowSynth_impl)

#guard (evalFuel 80 flipGuardCom ipState).isSome
#guard readArrs ((evalFuel 80 flipGuardCom ipState).getD (ipState, 0)).1 [heapName]
  ≠ readArrs ipOut.1 [heapName]
#guard readVars ((evalFuel 80 flipGuardCom ipState).getD (ipState, 0)).1 ["dc", "cap", hpName]
  ≠ readVars ipOut.1 ["dc", "cap", hpName]

/-- **Control 3 — the in-place branch's block move dropped.**  The result cell
`dc` keeps its junk value, so the caller is handed a base pointer that is not
the block's, and the run is one `ir.copy` cheaper: the *charge* fails with the
instruction, which is what ledger F11's discipline asks to be tested. -/
def noMoveCom : Com :=
  (Com.binop .mul "nc" "cap" "two").seq
    (Com.ite (.lt (.cell "len") (.cell "cap"))
      ((Com.binop .add "adr" "bc" "len").seq
        ((Com.aset heapName "adr" "xc").seq
          ((Com.binop .add "len" "len" "one").seq (Com.skip.seq Com.skip))))
      arlHAppendGrowSynth_impl)

#guard (evalFuel 40 noMoveCom ipState).isSome
#guard readVars ((evalFuel 40 noMoveCom ipState).getD (ipState, 0)).1 ["dc"]
  ≠ readVars ipOut.1 ["dc"]
#guard runVec ((evalFuel 40 noMoveCom ipState).getD (ipState, 0)).2 ≠ arlHAppendMachineN ipList

/-- **Control 4 — the growth branch's capacity write dropped.**  The block is
twice as long but the capacity cell still says the old one, so the next append
would overrun; and the run is again one `ir.copy` short. -/
def noCapCom : Com :=
  (Com.binop .mul "nc" "cap" "two").seq
    (Com.ite (.lt (.cell "len") (.cell "cap"))
      arlHAppendInPlaceCom
      (((Com.copy "pc" hpName).seq (Com.binop .add hpName hpName "nc")).seq
        ((arlGrowPushCom "t" "si" "se" "one" "di" "dc" "bc" "len" "pc" "xc").seq
          ((Com.binop .add "len" "len" "one").seq (Com.skip.seq Com.skip)))))

#guard (evalFuel 80 noCapCom grState).isSome
#guard readVars ((evalFuel 80 noCapCom grState).getD (grState, 0)).1 ["cap"]
  ≠ readVars grOut.1 ["cap"]
#guard runVec ((evalFuel 80 noCapCom grState).getD (grState, 0)).2 ≠ arlHAppendMachineN grList

/-- **Control 5 — the length bump dropped**, on the growth branch: the block
is right but the observable length is not, so the array list would lose the
element it just stored. -/
def noBumpCom : Com :=
  (Com.binop .mul "nc" "cap" "two").seq
    (Com.ite (.lt (.cell "len") (.cell "cap"))
      arlHAppendInPlaceCom
      (((Com.copy "pc" hpName).seq (Com.binop .add hpName hpName "nc")).seq
        ((arlGrowPushCom "t" "si" "se" "one" "di" "dc" "bc" "len" "pc" "xc").seq
          ((Com.copy "cap" "nc").seq (Com.skip.seq Com.skip)))))

#guard (evalFuel 80 noBumpCom grState).isSome
#guard readVars ((evalFuel 80 noBumpCom grState).getD (grState, 0)).1 ["len"]
  ≠ readVars grOut.1 ["len"]

/-! **Control 6 — the cost claims themselves.**  One unit off the predicted
vector fails against the run, on each branch. -/
#guard runVec ipOut.2 ≠ (⟨1, 1, 0, 0, 0, 2, 1, 0, 2⟩ : IrVecN)
#guard runVec ipOut.2 ≠ (⟨1, 0, 0, 1, 0, 2, 1, 0, 2⟩ : IrVecN)
#guard runVec ipOut.2 ≠ (⟨1, 1, 0, 1, 0, 2, 1, 0, 1⟩ : IrVecN)
#guard runVec grOut.2 ≠ (⟨1, 1, 3, 5, 1, 2, 4, 3, 9⟩ : IrVecN)
#guard runVec grOut.2 ≠ (⟨1, 1, 4, 4, 1, 2, 4, 3, 9⟩ : IrVecN)
#guard runVec grOut.2 ≠ (⟨1, 1, 4, 5, 1, 2, 4, 3, 8⟩ : IrVecN)

/-! **Control 7 — the composed command *does* allocate**, which is exactly why
it stays out of `sepref_fr_rules` (ledger E29).  The in-place branch does not:
the positive and the negative half of the same check. -/
private def condMentions (x : String) : Cond → Bool
  | .eq u v => opMentions u || opMentions v
  | .lt u v => opMentions u || opMentions v
where
  opMentions : Operand → Bool
    | .cell y => y == x
    | .lit _ => false

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

#guard mentions hpName arlHAppendCom = true
#guard mentions hpName arlHAppendInPlaceCom = false

end ArrayListAppendGate

/-! ## 11. Axiom gate -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_arlBlockMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_arlBlockMove

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHAppendMerge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHAppendMerge

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHAppend_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHAppend_dispatch

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHAppendRaw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHAppendRaw_eq

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHAppend_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHAppend_exec_hnr

/--
info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHAppendMachine_amortized_ir' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms arlHAppendMachine_amortized_ir

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlAppendTotal_tight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arlAppendTotal_tight

/-! ## 12. The append guarantee is unchanged

The dispatch adds an executable command.  It restates nothing about the
refinement: `arlAppendOp_refines` is still `@[sepref_fref_thms]` over
`arrayListRel` at precondition `fun _ : List ℕ => True`, `arrayListReadyRel`
is still deleted, and `ArrayListCash.lean`'s compiled guard still passes. -/

theorem arlHAppend_leaves_append_unchanged :
    (arlAppendOp, op_list_append ℕ) ∈
      fref (fun _ : List ℕ => True) arrayListRel
        (fun _ => Set.diagonal ℕ →ᵣ NRest.nrestRel arrayListRel) :=
  arlAppendOp_refines_unchanged

end Lax13Proofs.Refine.Sepref.Iicf
