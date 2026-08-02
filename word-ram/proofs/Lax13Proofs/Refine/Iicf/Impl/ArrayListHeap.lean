import Lax13Proofs.Refine.Iicf.Impl.ArrayListGrowSynth

/-!
# The array list, re-seated on the heap

Leaf **P4.5.A.7** of the P5.E re-seat (ledger **E38**), satellite of
`ArrayList.lean` and `ArrayListGrowSynth.lean`.

`ArrayListGrowSynth.lean` closed growth as one synthesized command and named
what still blocked end-to-end append: the array list keeps its buffer in a
**named IR array** (`arrayAssn buffer A`, i.e. `A ↦ₐ xs`), while the
allocator and the copy loop work on **heap ranges** (`p ↦ₕ xs` inside the one
reserved `heapName` array).  It proposed a bridge `arrayAssn ⟷ heapBlockAssn`.

**There is no such bridge, and there must not be one.**  The two assertions
own *different physical storage*, so a conversion is either an honest O(n)
element copy — which, invoked per push, destroys the amortized-O(1) headline
`ArrayListCash.lean` cashed — or it is unsound.  A.1 makes the second
impossible by construction: `acells` sends `heapName` to `Tsa.zero` and
`not_irSTATE_ptoArr_heapName` is the compiled fact that the heap name is not
ownable as an ordinary array.

So the representation moves instead, and no conversion ever happens.  This is
P5.E's own description of the work — *re-seating is statement strengthening
plus substrate substitution; the representation theory and the abstract
refinement layer are reused, not rewritten*.  `ArrayList` (= `BoundedArray`),
`arrayListRel`, `boundedPush`, `arlShrinkCapacity`, and **every value-level
theorem** are reused verbatim; the `*ExecState_refines` bridges of
`ArrayList.lean` are literally the ones this file cites.  What changes is the
assertion and the executable rules beneath it.

## The representation

| landed (`ArrayList.lean`) | here |
|---|---|
| `boundedArrayAssn s c = ⌜s.Wf⌝ ∗ (arrayAssn s.buffer c.1 ∗ …)` | `heapBoundedArrayAssn p s c = ⌜s.Wf⌝ ∗ (heapBlockAssnAt p s.buffer c.1 ∗ …)` |
| `arrayListAssn = hrComp boundedArrayAssn arrayListRel` | `heapArrayListAssn p = hrComp (heapBoundedArrayAssn p) arrayListRel` |

`heapBlockAssnAt p xs c = (c ↦ᵥ p) ∗ (p ↦ₕ xs)` is `HeapAlloc.lean`'s
`heapBlockAssn` with the base pointer **pinned** rather than existential.  The
pinned form is the registered one and the packed form
(`heapArrayListAssnPacked`, `heapBlockAssn`'s own shape) is deliberately not
registered — this is `HeapEO.lean`'s judgment call **D-B1d** verbatim, and the
reason is E29: a packed form in the database lets synthesis silently repack
inside a loop.  `heapArrayListAssn_entails_packed` reaches it when an
interface must hide the pointer.

The *interface* is untouched (hazard: rule 5).  `intfOfAssn (heapArrayListAssn p)
(ListI ℕ)` holds, `arrayListAssn_intf` is untouched, and the P5.A interface
layer, the `sepref_fref_thms` over `arrayListRel`, and every pure registered
rule are shared between the two representations without change: they are
stated at the *relation*, which is the same relation.

## Address arithmetic is the caller's — and it is charged

A.1's `haget_triple` / `haset_triple` take the **absolute** address `p + j` in
the index cell, so a heap read is one `ir.aget` and nothing is smuggled; the
caller that must form `p + j` emits an ordinary `binop .add` and pays its own
`ir.add`.  That is `HeapEO.lean`'s judgment call **D-B1c**, and it is the one
real cost difference between the two representations:

| op | named-array command | heap command | Δ |
|---|---|---|---|
| `length`, `isEmpty` | metadata only | *the same rule* | — |
| `get` | `aget` | `add ; aget` | `+ir.add` |
| `last` | `sub ; aget` | `sub ; add ; aget` | `+ir.add` |
| `set` | `aset ; skip ; skip` | `add ; aset ; skip ; skip` | `+ir.add` |
| `butlast` | metadata only | *the same command* | — |
| `swap` | 2·`aget` 2·`aset` 2·`skip` | 2·`add` 2·`aget` 2·`aset` 2·`skip` | `+2·ir.add` |

Every one of those costs is read off the *emitted* program by a `#guard` in
§ 6 (ledger **F11**, whose failure class has now bitten four times), not
assigned by fiat.

## Registration, and why nothing competes (ledger E29)

This is **additive**: `ArrayList.lean`'s seven registered rules are untouched
and stay the right rules for a caller who owns a named array.  So the E29
question — two registered representations of one interface — has to be
answered, and it is answered operation by operation rather than waved at.

* The heap layer introduces **its own mops**: `mopHaddr`, `mopHaget`,
  `mopHaset`, `arlH*Raw`, `arlH*ExecSpec`.  Nothing is re-registered at a
  second assertion.
* For `get`, `last`, `set` and `swap` the two abstract operations are
  genuinely different — `arlHGetExecSpec` costs an `ir.add` that
  `arlGetExecSpec` does not — so the rules are not interchangeable at all.
* For `butlast` the program *and* the price are unchanged by the re-seat, so
  its heap rule differs from the landed one only in the assertion it consumes.
  `arlHButlastExecSpec` is therefore a distinct `irreducible` constant, which
  makes the two keys syntactically distinct; and even without that, selection
  is "the first entry that applies **and** whose side conditions close", with
  backtracking (`Translate.lean`'s `transOp`), so a context holding one
  representation cannot be served the other rule — the frame premise fails.
* `length` and `isEmpty` are not re-registered at all: their landed rules are
  reused as proof terms (`arlHLength_exec_hnr`, `arlHIsEmpty_exec_hnr`) and
  carry no attribute.

What E29 actually warns against is synthesis silently choosing an
**allocating or repacking** form inside a loop.  None of the rules registered
here allocates, none repacks, and every one hands the block back at the same
base and the same cell.  The empirical check is the consumer package, whose
own `sepref_synth` invocations all run with these rules in the database.

## What is *not* touched, and what this does not close

`arlAppendOp_refines` is unchanged — still `@[sepref_fref_thms]` over
`arrayListRel` at precondition `fun _ : List ℕ => True`, `arrayListReadyRel`
still deleted, `ArrayListCash.lean`'s compiled `arlAppendOp_refines_unchanged`
still passing.  `dynRate` and its domination proofs are untouched **and
unaffected**: they are stated about `arlAppendMachineN`, which is assembled
from the *named-array* adapter's emitted programs, and this file adds
programs without changing any of those.  Should append later be re-seated
too, its growth branch is already heap-native (`arlGrowPushSynth_impl`) and
only the in-place branch's `+ir.add` would need cashing; that is named here
rather than pre-empted.

**Append is still not synthesizable end to end**, and the remaining gap is no
longer representational — it is `hnr_If` over the two branches at a *moving*
base pointer.  The in-place branch keeps the block at `p`; the growth branch
returns a block at a fresh base `p'`, so the two branches' postconditions are
`heapBlockAssnAt p` and `heapBlockAssnAt p'` and `MERGE` cannot identify them.
The merged form has to be the packed `heapBlockAssn` — which is exactly the
form D-B1d keeps out of the database.  So append's dispatch needs a rule
stated at the packed assertion and used *by name*, never registered, in the
idiom `ArrayListGrowSynth.lean` used for `arlGrowSynth`.  That is one further
leaf; it is named precisely and nothing here pretends to have done it.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## 1. The heap-backed representation -/

/-- A heap block at a **pinned** base: the cell `c` holds `p`, and `p` owns the
range holding `xs`.  `HeapAlloc.lean`'s `heapBlockAssn` is this with `p`
existentially quantified; `HeapEO.lean`'s `eoarrayAssnAt` is its EO sibling. -/
def heapBlockAssnAt (p : ℕ) : List Val → String → Assn := fun xs c => (c ↦ᵥ p) ∗ (p ↦ₕ xs)

@[simp] theorem heapBlockAssnAt_def (p : ℕ) (xs : List Val) (c : String) :
    heapBlockAssnAt p xs c = ((c ↦ᵥ p) ∗ (p ↦ₕ xs)) := rfl

theorem heapBlockAssnAt_entails_heapBlockAssn (p : ℕ) (xs : List Val) (c : String) :
    heapBlockAssnAt p xs c ⊢ heapBlockAssn xs c := fun _ h => ⟨p, h⟩

/-- `boundedArrayAssn`'s heap twin: same three caller-owned cells, same `Wf`,
but the buffer cell holds a **base pointer** into the reserved heap array
instead of naming an IR array. -/
def heapBoundedArrayAssn (p : ℕ) : BoundedArray → String × String × String → Assn :=
  fun s c =>
    ⌜s.Wf⌝ ∗ (heapBlockAssnAt p s.buffer c.1 ∗ natAssn s.length c.2.1 ∗
      natAssn s.capacity c.2.2)

theorem heapBoundedArrayAssn_unfold (p : ℕ) (s : BoundedArray)
    (c : String × String × String) :
    hnCtxt (heapBoundedArrayAssn p) s c =
      ⌜s.Wf⌝ ∗ (hnCtxt (heapBlockAssnAt p) s.buffer c.1 ∗ hnCtxt natAssn s.length c.2.1 ∗
        hnCtxt natAssn s.capacity c.2.2) := rfl

/-- Package three already-owned cells as a heap-backed bounded array.  The
allocator's own boundary: `hnr_mop_alloc` delivers `heapBlockAssn`, and
pinning its base is `heapBlockAssnAt`. -/
theorem heapBoundedArrayAssn_intro (p : ℕ) (s : BoundedArray)
    (c : String × String × String) (h : s.Wf) :
    (heapBlockAssnAt p s.buffer c.1 ∗ natAssn s.length c.2.1 ∗
        natAssn s.capacity c.2.2) ⊢ heapBoundedArrayAssn p s c :=
  fun _ hs => predLift_sepConj_iff.2 ⟨h, hs⟩

/-- Release returns the caller's three cells **and the range**.  Unlike
`boundedArrayAssn_release`, the buffer's resource does not vanish into a
`junkArrayOfLen`: a heap block is owned memory that someone must still hold,
which is precisely why `ArrayList.lean`'s leak bound
(`arlAllocatedMany_live_bounded`) is a theorem there. -/
theorem heapBoundedArrayAssn_release (p : ℕ) (s : BoundedArray)
    (c : String × String × String) :
    hnCtxt (heapBoundedArrayAssn p) s c ⊢
      (junkCell c.1 ∗ (p ↦ₕ s.buffer)) ∗ junkCell c.2.1 ∗ junkCell c.2.2 := by
  intro st hs
  obtain ⟨-, hs⟩ := predLift_sepConj_iff.1 hs
  exact conj_entails_mono
    (conj_entails_mono (fun _ hh => ⟨p, hh⟩) (entails_refl _))
    (conj_entails_mono (natAssn_entails_junkCell s.length c.2.1)
      (natAssn_entails_junkCell s.capacity c.2.2)) st hs

/-- The heap-backed array list: **the same** `hrComp … arrayListRel`.  The
representation theory is reused, not re-derived. -/
def heapArrayListAssn (p : ℕ) : List ℕ → String × String × String → Assn :=
  hrComp (heapBoundedArrayAssn p) arrayListRel

@[intf_of_assn] theorem heapArrayListAssn_intf (p : ℕ) :
    intfOfAssn (heapArrayListAssn p) (ListI ℕ) := trivial

theorem heapArrayListAssn_unfold (p : ℕ) (xs : List ℕ) (c : String × String × String) :
    heapArrayListAssn p xs c =
      ∃ᵃ s, heapBoundedArrayAssn p s c ∗ ⌜s.Wf ∧ s.active = xs⌝ := rfl

theorem heapArrayListAssn_intro {p : ℕ} {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) (c : String × String × String) :
    heapBoundedArrayAssn p s c ⊢ heapArrayListAssn p xs c :=
  hr_compI h

/-! ### The packed form (deliberately unregistered, ledger E29 / D-B1d) -/

/-- The base pointer hidden, `heapBlockAssn`'s own shape.  For interfaces that
must not expose the pointer — and for a future append, whose two branches end
at *different* bases. -/
def heapBoundedArrayAssnPacked : BoundedArray → String × String × String → Assn :=
  fun s c =>
    ⌜s.Wf⌝ ∗ (heapBlockAssn s.buffer c.1 ∗ natAssn s.length c.2.1 ∗
      natAssn s.capacity c.2.2)

def heapArrayListAssnPacked : List ℕ → String × String × String → Assn :=
  hrComp heapBoundedArrayAssnPacked arrayListRel

theorem heapBoundedArrayAssn_entails_packed (p : ℕ) (s : BoundedArray)
    (c : String × String × String) :
    heapBoundedArrayAssn p s c ⊢ heapBoundedArrayAssnPacked s c := by
  intro st hs
  obtain ⟨hwf, hs⟩ := predLift_sepConj_iff.1 hs
  exact predLift_sepConj_iff.2 ⟨hwf,
    conj_entails_mono (heapBlockAssnAt_entails_heapBlockAssn p s.buffer c.1)
      (entails_refl _) st hs⟩

theorem heapArrayListAssn_entails_packed (p : ℕ) (xs : List ℕ)
    (c : String × String × String) :
    heapArrayListAssn p xs c ⊢ heapArrayListAssnPacked xs c := by
  rintro st ⟨s, hst⟩
  exact ⟨s, conj_entails_mono (heapBoundedArrayAssn_entails_packed p s c)
    (entails_refl _) st hst⟩

/-! ## 2. The heap access primitives

Three mops, three registered rules.  They are *new* operations, not the
landed `mopBinop`/`mopAget`/`mopAset` re-registered at a second assertion —
see the header's E29 paragraph.  `mopHaget`/`mopHaset` take the **absolute**
address as their abstract operand, which is what `haget_triple` /
`haset_triple` take in the index cell, and what makes the address value flow
*through* `hnr_seq`'s binder: a rule whose mop mentioned only the offset would
have to recover `a = p + ?j` from an opaque binder, which is the wall
`ArrayListGrowSynth.lean`'s header names. -/

/-- `adr := base + idx`.  The block's base cell is **read** out of the pinned
assertion — the block survives — and the caller pays one `ir.add`
(`HeapEO.lean`'s judgment call D-B1c: address arithmetic is not hidden inside
the access, it is charged where it is emitted). -/
noncomputable def mopHaddr (p i : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT (p + i)) (irUnit Currency.add)

theorem mopHaddr_def (p i : ℕ) :
    mopHaddr p i = NRest.consume (NRest.returnT (p + i)) (irUnit Currency.add) := rfl

/-- `x := heap[adr]` inside a block based at `p`.  The guard is the source's
pointer-compatibility premise in arithmetic form: the address is inside the
block.  Price: one `ir.aget`. -/
noncomputable def mopHaget (p : ℕ) (xs : List Val) (a : ℕ) : NRest ℕ ECost :=
  NRest.bindT (NRest.assert (p ≤ a ∧ a - p < xs.length)) fun _ =>
    NRest.consume (NRest.returnT xs[a - p]!) (irUnit Currency.aget)

theorem mopHaget_def (p : ℕ) (xs : List Val) (a : ℕ) :
    mopHaget p xs a = NRest.bindT (NRest.assert (p ≤ a ∧ a - p < xs.length)) fun _ =>
      NRest.consume (NRest.returnT xs[a - p]!) (irUnit Currency.aget) := rfl

/-- `heap[adr] := v` inside a block based at `p`.  **Destructive**, exactly as
`mopAset` is: the block's ownership at `xs` moves into the result slot at the
same cell and the same base. -/
noncomputable def mopHaset (p : ℕ) (xs : List Val) (a v : ℕ) : NRest (List Val) ECost :=
  NRest.bindT (NRest.assert (p ≤ a ∧ a - p < xs.length)) fun _ =>
    NRest.consume (NRest.returnT (xs.set (a - p) v)) (irUnit Currency.aset)

theorem mopHaset_def (p : ℕ) (xs : List Val) (a v : ℕ) :
    mopHaset p xs a v = NRest.bindT (NRest.assert (p ≤ a ∧ a - p < xs.length)) fun _ =>
      NRest.consume (NRest.returnT (xs.set (a - p) v)) (irUnit Currency.aset) := rfl

theorem haddr_junk_rule (adr c idx : String) (p i : ℕ) (xs : List Val) :
    irHtriple (¤(irUnit Currency.add) ∗
        (junkCell adr ∗ hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn i idx))
      (.binop .add adr c idx)
      ((hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn i idx) ∗ natAssn (p + i) adr) := by
  rw [show (¤(irUnit Currency.add) ∗
      (junkCell adr ∗ hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn i idx))
      = junkCell adr ∗ (¤(irUnit Currency.add) ∗
        hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn i idx) from by ac_rfl]
  refine irHtriple_junk fun v => ?_
  have hbase : irTriple
      (¤¤Currency.add 1 ∗ (adr ↦ᵥ v) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ i) ∗ (p ↦ₕ xs))
      (.binop .add adr c idx)
      ((adr ↦ᵥ (p + i)) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ i) ∗ (p ↦ₕ xs)) := by
    have h := binop_triple .add adr c idx v p i
    rw [binopCurrency_add, Imp.Bop.apply_add] at h
    ir_frame h
  rw [show ((adr ↦ᵥ v) ∗ (¤(irUnit Currency.add) ∗
      hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn i idx))
      = (¤¤Currency.add 1 ∗ (adr ↦ᵥ v) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ i) ∗ (p ↦ₕ xs)) from by
    rw [costCredits_one]
    simp only [hnCtxt_def, natAssn_def, heapBlockAssnAt_def]; ac_rfl,
    show ((hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn i idx) ∗ natAssn (p + i) adr)
      = ((adr ↦ᵥ (p + i)) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ i) ∗ (p ↦ₕ xs)) from by
    simp only [hnCtxt_def, natAssn_def, heapBlockAssnAt_def]; ac_rfl]
  exact hbase.gc

/-- **The address rule.**  Registered: it is the only rule for `mopHaddr`. -/
@[sepref_fr_rules]
theorem hnr_mop_haddr (adr c idx : String) (p i : ℕ) (xs : List Val) :
    hnRefine (junkCell adr ∗ hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn i idx)
      (.binop .add adr c idx)
      (hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn i idx) adr natAssn (mopHaddr p i) :=
  hnRefineI_spect (haddr_junk_rule adr c idx p i xs)

theorem haget_junk_rule (x c idx : String) (p a : ℕ) (xs : List Val)
    (hp : p ≤ a) (hk : a - p < xs.length) :
    irHtriple (¤(irUnit Currency.aget) ∗
        (junkCell x ∗ hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn a idx))
      (.aget x heapName idx)
      ((hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn a idx) ∗ natAssn xs[a - p]! x) := by
  obtain ⟨j, rfl⟩ : ∃ j, a = p + j := ⟨a - p, by omega⟩
  rw [Nat.add_sub_cancel_left] at hk ⊢
  have hval : xs[j]! = xs[j] := getElem!_pos xs j hk
  rw [show (¤(irUnit Currency.aget) ∗
      (junkCell x ∗ hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn (p + j) idx))
      = junkCell x ∗ (¤(irUnit Currency.aget) ∗
        hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn (p + j) idx) from by ac_rfl]
  refine irHtriple_junk fun v => ?_
  have hread : irTriple
      (¤¤Currency.aget 1 ∗ (x ↦ᵥ v) ∗ (p ↦ₕ xs) ∗ (idx ↦ᵥ (p + j)) ∗ (c ↦ᵥ p))
      (.aget x heapName idx)
      ((x ↦ᵥ xs[j]!) ∗ (p ↦ₕ xs) ∗ (idx ↦ᵥ (p + j)) ∗ (c ↦ᵥ p)) := by
    have h := haget_triple x idx v p j xs xs[j]! hk hval.symm
    ir_frame h
  rw [show ((x ↦ᵥ v) ∗ (¤(irUnit Currency.aget) ∗
      hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn (p + j) idx))
      = (¤¤Currency.aget 1 ∗ (x ↦ᵥ v) ∗ (p ↦ₕ xs) ∗ (idx ↦ᵥ (p + j)) ∗ (c ↦ᵥ p)) from by
    rw [costCredits_one]
    simp only [hnCtxt_def, natAssn_def, heapBlockAssnAt_def]; ac_rfl,
    show ((hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn (p + j) idx) ∗ natAssn xs[j]! x)
      = ((x ↦ᵥ xs[j]!) ∗ (p ↦ₕ xs) ∗ (idx ↦ᵥ (p + j)) ∗ (c ↦ᵥ p)) from by
    simp only [hnCtxt_def, natAssn_def, heapBlockAssnAt_def]; ac_rfl]
  exact hread.gc

/-- **The heap read rule.**  A read consumes nothing: the block and the
address both survive into `Γ'`. -/
@[sepref_fr_rules]
theorem hnr_mop_haget (x c idx : String) (p a : ℕ) (xs : List Val) :
    hnRefine (junkCell x ∗ hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn a idx)
      (.aget x heapName idx)
      (hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn a idx) x natAssn
      (mopHaget p xs a) := by
  rw [mopHaget_def]
  exact hnr_assert fun h => hnRefineI_spect (haget_junk_rule x c idx p a xs h.1 h.2)

theorem haset_mop_rule (c idx v : String) (p a n : ℕ) (xs : List Val)
    (hp : p ≤ a) (hk : a - p < xs.length) :
    irHtriple (¤(irUnit Currency.aset) ∗
        (hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn a idx ∗ hnCtxt natAssn n v))
      (.aset heapName idx v)
      ((hnCtxt natAssn a idx ∗ hnCtxt natAssn n v) ∗
        heapBlockAssnAt p (xs.set (a - p) n) c) := by
  obtain ⟨j, rfl⟩ : ∃ j, a = p + j := ⟨a - p, by omega⟩
  rw [Nat.add_sub_cancel_left] at hk ⊢
  have hwrite : irTriple
      (¤¤Currency.aset 1 ∗ (p ↦ₕ xs) ∗ (idx ↦ᵥ (p + j)) ∗ (v ↦ᵥ n) ∗ (c ↦ᵥ p))
      (.aset heapName idx v)
      ((p ↦ₕ xs.set j n) ∗ (idx ↦ᵥ (p + j)) ∗ (v ↦ᵥ n) ∗ (c ↦ᵥ p)) := by
    have h := haset_triple idx v p j xs n hk
    ir_frame h
  rw [show (¤(irUnit Currency.aset) ∗
      (hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn (p + j) idx ∗ hnCtxt natAssn n v))
      = (¤¤Currency.aset 1 ∗ (p ↦ₕ xs) ∗ (idx ↦ᵥ (p + j)) ∗ (v ↦ᵥ n) ∗ (c ↦ᵥ p)) from by
    rw [costCredits_one]
    simp only [hnCtxt_def, natAssn_def, heapBlockAssnAt_def]; ac_rfl,
    show ((hnCtxt natAssn (p + j) idx ∗ hnCtxt natAssn n v) ∗
        heapBlockAssnAt p (xs.set j n) c)
      = ((p ↦ₕ xs.set j n) ∗ (idx ↦ᵥ (p + j)) ∗ (v ↦ᵥ n) ∗ (c ↦ᵥ p)) from by
    simp only [hnCtxt_def, natAssn_def, heapBlockAssnAt_def]; ac_rfl]
  exact hwrite.gc

/-- **The heap write rule**, `hnr_mop_aset`'s linearity showcase at a block:
`hnCtxt (heapBlockAssnAt p) xs c` is absent from `Γ'`, so a second use of `xs`
after this rule is not derivable.  The base does **not** move — a write is
in place — which is why the result assertion is `heapBlockAssnAt p` again. -/
@[sepref_fr_rules]
theorem hnr_mop_haset (c idx v : String) (p a n : ℕ) (xs : List Val) :
    hnRefine (hnCtxt (heapBlockAssnAt p) xs c ∗ hnCtxt natAssn a idx ∗ hnCtxt natAssn n v)
      (.aset heapName idx v)
      (hnCtxt natAssn a idx ∗ hnCtxt natAssn n v) c (heapBlockAssnAt p)
      (mopHaset p xs a n) := by
  rw [mopHaset_def]
  exact hnr_assert fun h => hnRefineI_spect (haset_mop_rule c idx v p a n xs h.1 h.2)

/-! ## 3. The seven operations, re-seated

`length` and `isEmpty` touch only the metadata cells, so their landed rules
are representation-independent and are reused **verbatim** — the proof terms
below are `ArrayList.lean`'s own theorems, not re-derivations, and they are
deliberately not re-tagged (there is exactly one registered rule per
operation).  `butlast` emits a command that never mentions the buffer cell, so
only its *ownership threading* changes.  The remaining four —
`get`, `last`, `set`, `swap` — gain the address instruction the header's table
prices. -/

theorem arlHLength_exec_hnr (len out : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ junkCell out)
      (arlLengthCom len out) (hnCtxt natAssn n len) out natAssn
      (arlLengthExecSpec n) :=
  arlLength_exec_hnr len out n

theorem arlHIsEmpty_exec_hnr (len out : String) (n : ℕ) :
    hnRefine (hnCtxt natAssn n len ∗ junkCell out)
      (arlIsEmptyCom len out) ((□ : Assn) ∗ hnCtxt natAssn n len) out natAssn
      (arlIsEmptyExecSpec n) :=
  arlIsEmpty_exec_hnr len out n

noncomputable def arlHGetRaw (p : ℕ) (buffer : List ℕ) (i : ℕ) : NRest ℕ ECost :=
  NRest.bindT (mopHaddr p i) fun a => mopHaget p buffer a

noncomputable def arlHLastRaw (p : ℕ) (buffer : List ℕ) (n : ℕ) : NRest ℕ ECost :=
  NRest.bindT (mopBinop .sub n 1) fun i =>
    NRest.bindT (mopHaddr p i) fun a => mopHaget p buffer a

noncomputable def arlHSetRaw (p : ℕ) (buffer : List ℕ) (n cap i x : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopHaddr p i) fun a =>
    NRest.bindT (mopHaset p buffer a x) fun buffer' =>
      NRest.bindT (mopPair n cap) fun md => mopPair buffer' md

noncomputable def arlHSwapRaw (p : ℕ) (buffer : List ℕ) (n cap i j : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopHaddr p i) fun ai =>
    NRest.bindT (mopHaddr p j) fun aj =>
      NRest.bindT (mopHaget p buffer ai) fun xi =>
        NRest.bindT (mopHaget p buffer aj) fun xj =>
          NRest.bindT (mopHaset p buffer ai xj) fun buffer' =>
            NRest.bindT (mopHaset p buffer' aj xi) fun buffer'' =>
              NRest.bindT (mopPair n cap) fun md => mopPair buffer'' md

/-- Logical shrink only, exactly as `arlButlastRaw`: the emitted command never
touches the buffer, so the *program* is unchanged by the re-seat.  This is a
separate definition rather than an alias so that the rule database keeps one
rule per operation (ledger E29). -/
noncomputable def arlHButlastRaw (buffer : List ℕ) (n cap : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (arlPred n) fun n' =>
    NRest.bindT (mopBinop .mul n' 4) fun fourN =>
      NRest.bindT (mopBinop .mul n' 2) fun twoN =>
        NRest.bindT (mopCopy cap) fun cap₀ =>
          NRest.bindT (arlSelectCap cap₀ fourN twoN cap) fun cap' =>
            NRest.bindT (mopPair n' cap') fun md => mopPair buffer md

sepref_synth arlHGetSynth (bc idx adr out : String) (p : ℕ) (buffer : List ℕ) (i : ℕ) :
  hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn i idx ∗
      junkCell adr ∗ junkCell out)
    _ _ out natAssn (arlHGetRaw p buffer i)

sepref_synth arlHLastSynth (bc len one idx adr out : String)
    (p : ℕ) (buffer : List ℕ) (n : ℕ) :
  hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn 1 one ∗ junkCell idx ∗ junkCell adr ∗ junkCell out)
    _ _ out natAssn (arlHLastRaw p buffer n)

sepref_synth arlHSetSynth (bc len cap idx adr value : String)
    (p : ℕ) (buffer : List ℕ) (n c i x : ℕ) :
  hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn i idx ∗ junkCell adr ∗
      hnCtxt natAssn x value)
    _ _ (bc, (len, cap)) (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn)
    (arlHSetRaw p buffer n c i x)

set_option maxHeartbeats 1000000 in
sepref_synth arlHSwapSynth (bc len cap I J AI AJ XI XJ : String)
    (p : ℕ) (buffer : List ℕ) (n c i j : ℕ) :
  hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
      junkCell AI ∗ junkCell AJ ∗ junkCell XI ∗ junkCell XJ)
    _ _ (bc, (len, cap)) (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn)
    (arlHSwapRaw p buffer n c i j)

set_option maxHeartbeats 800000 in
sepref_synth arlHButlastSynth
    (bc len cap one four two fourN twoN outCap : String)
    (p : ℕ) (buffer : List ℕ) (n c : ℕ) :
  hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn 1 one ∗ hnCtxt natAssn 4 four ∗
      hnCtxt natAssn 2 two ∗ junkCell fourN ∗ junkCell twoN ∗ junkCell outCap)
    _ _ (bc, (len, outCap)) (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn)
    (arlHButlastRaw buffer n c)

/-! ### The prices, read off the commands above -/

noncomputable def arlHGetCost : ECost := irUnit Currency.add + irUnit Currency.aget
noncomputable def arlHLastCost : ECost :=
  irUnit Currency.sub + irUnit Currency.add + irUnit Currency.aget
noncomputable def arlHSetCost : ECost :=
  irUnit Currency.add + irUnit Currency.aset + 2 • irUnit Currency.skip
noncomputable def arlHSwapCost : ECost :=
  2 • irUnit Currency.add + 2 • irUnit Currency.aget + 2 • irUnit Currency.aset +
    2 • irUnit Currency.skip

/-- The re-seat's whole cost delta, as an equation per operation. -/
theorem arlHGetCost_eq : arlHGetCost = arlGetCost + irUnit Currency.add := by
  rw [arlHGetCost, arlGetCost]; abel

theorem arlHLastCost_eq : arlHLastCost = arlLastCost + irUnit Currency.add := by
  rw [arlHLastCost, arlLastCost]; abel

theorem arlHSetCost_eq : arlHSetCost = arlSetCost + irUnit Currency.add := by
  rw [arlHSetCost, arlSetCost]; abel

theorem arlHSwapCost_eq : arlHSwapCost = arlSwapCost + 2 • irUnit Currency.add := by
  rw [arlHSwapCost, arlSwapCost]; abel

noncomputable def arlHGetExecSpec (buffer : List ℕ) (i : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT buffer[i]!) arlHGetCost
noncomputable def arlHLastExecSpec (buffer : List ℕ) (n : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT buffer[n - 1]!) arlHLastCost
noncomputable def arlHSetExecSpec (buffer : List ℕ) (n cap i x : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT (buffer.set i x, (n, cap))) arlHSetCost
noncomputable def arlHSwapExecSpec (buffer : List ℕ) (n cap i j : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT
    ((buffer.set i buffer[j]!).set j buffer[i]!, (n, cap))) arlHSwapCost

private theorem hbound {p i : ℕ} {buffer : List ℕ} (hi : i < buffer.length) :
    p ≤ p + i ∧ p + i - p < buffer.length := ⟨Nat.le_add_right _ _, by omega⟩

/-- The heap read at a formed address: the guard discharges and the offset
comes back.  This is where "the abstract operand is the absolute address"
pays off — nothing downstream ever has to invert `p + ·`. -/
private theorem mopHaget_add (p : ℕ) (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    mopHaget p xs (p + i) =
      NRest.consume (NRest.returnT xs[i]!) (irUnit Currency.aget) := by
  rw [mopHaget_def, NRest.assert_pos (hbound (p := p) hi), NRest.returnT_bindT,
    Nat.add_sub_cancel_left]

private theorem mopHaset_add (p : ℕ) (xs : List ℕ) (i v : ℕ) (hi : i < xs.length) :
    mopHaset p xs (p + i) v =
      NRest.consume (NRest.returnT (xs.set i v)) (irUnit Currency.aset) := by
  rw [mopHaset_def, NRest.assert_pos (hbound (p := p) hi), NRest.returnT_bindT,
    Nat.add_sub_cancel_left]

theorem arlHGetRaw_eq (p : ℕ) (buffer : List ℕ) (i : ℕ) (hi : i < buffer.length) :
    arlHGetRaw p buffer i = NRest.consume (NRest.returnT buffer[i]!) arlHGetCost := by
  rw [arlHGetRaw, arlHGetCost, mopHaddr_def, Lax13Proofs.Refine.Iicf.bindT_unit,
    mopHaget_add p buffer i hi, NRest.consume_consume, add_comm]

theorem arlHLastRaw_eq (p : ℕ) (buffer : List ℕ) (n : ℕ)
    (hn : n ≠ 0) (hle : n ≤ buffer.length) :
    arlHLastRaw p buffer n =
      NRest.consume (NRest.returnT buffer[n - 1]!) arlHLastCost := by
  have hi : n - 1 < buffer.length := by omega
  rw [arlHLastRaw, arlHLastCost, mopBinop_def, Lax13Proofs.Refine.Iicf.bindT_unit,
    Imp.Bop.apply_sub, binopCurrency_sub, mopHaddr_def,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopHaget_add p buffer (n - 1) hi,
    NRest.consume_consume, NRest.consume_consume]

theorem arlHSetRaw_eq (p : ℕ) (buffer : List ℕ) (n cap i x : ℕ) (hi : i < buffer.length) :
    arlHSetRaw p buffer n cap i x =
      NRest.consume (NRest.returnT (buffer.set i x, (n, cap))) arlHSetCost := by
  rw [arlHSetRaw, arlHSetCost, mopHaddr_def, Lax13Proofs.Refine.Iicf.bindT_unit,
    mopHaset_add p buffer i x hi, Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def, NRest.consume_consume,
    NRest.consume_consume, NRest.consume_consume, two_nsmul]
  congr 1
  abel

theorem arlHSwapRaw_eq (p : ℕ) (buffer : List ℕ) (n cap i j : ℕ)
    (hi : i < buffer.length) (hj : j < buffer.length) :
    arlHSwapRaw p buffer n cap i j = NRest.consume
      (NRest.returnT
        ((buffer.set i buffer[j]!).set j buffer[i]!, (n, cap))) arlHSwapCost := by
  have hj' : j < (buffer.set i buffer[j]!).length := by simpa using hj
  rw [arlHSwapRaw, arlHSwapCost, mopHaddr_def, Lax13Proofs.Refine.Iicf.bindT_unit,
    mopHaddr_def, Lax13Proofs.Refine.Iicf.bindT_unit,
    mopHaget_add p buffer i hi, Lax13Proofs.Refine.Iicf.bindT_unit,
    mopHaget_add p buffer j hj, Lax13Proofs.Refine.Iicf.bindT_unit,
    mopHaset_add p buffer i buffer[j]! hi, Lax13Proofs.Refine.Iicf.bindT_unit,
    mopHaset_add p (buffer.set i buffer[j]!) j buffer[i]! hj',
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def,
    Lax13Proofs.Refine.Iicf.bindT_unit, mopPair_def]
  simp only [NRest.consume_consume, two_nsmul]
  congr 1
  abel

/-- `butlast`'s price and value are exactly the landed ones — the shrink is
metadata-only, so the re-seat cannot change either.  It is nevertheless given
its own constant, and made `irreducible`, so that the rule database keeps one
syntactically distinct key per operation. -/
noncomputable def arlHButlastExecSpec (buffer : List ℕ) (n cap : ℕ) :
    NRest (List ℕ × (ℕ × ℕ)) ECost := arlButlastExecSpec buffer n cap

theorem arlHButlastExecSpec_eq (buffer : List ℕ) (n cap : ℕ) :
    arlHButlastExecSpec buffer n cap = arlButlastExecSpec buffer n cap := rfl

theorem arlHButlastRaw_eq (buffer : List ℕ) (n cap : ℕ) :
    arlHButlastRaw buffer n cap = arlHButlastExecSpec buffer n cap :=
  arlButlastRaw_eq buffer n cap

attribute [irreducible] arlHButlastExecSpec

/-! ### The emitted commands, pinned -/

def arlHGetCom (bc idx adr out : String) : Com :=
  .seq (.binop .add adr bc idx) (.aget out heapName adr)

def arlHLastCom (bc len one idx adr out : String) : Com :=
  .seq (.binop .sub idx len one) (arlHGetCom bc idx adr out)

def arlHSetCom (bc _len _cap idx adr value : String) : Com :=
  .seq (.binop .add adr bc idx) (.seq (.aset heapName adr value) (.seq .skip .skip))

def arlHSwapCom (bc _len _cap I J AI AJ XI XJ : String) : Com :=
  .seq (.binop .add AI bc I)
    (.seq (.binop .add AJ bc J)
      (.seq (.aget XI heapName AI)
        (.seq (.aget XJ heapName AJ)
          (.seq (.aset heapName AI XJ)
            (.seq (.aset heapName AJ XI) (.seq .skip .skip))))))

/-- Identical to `arlButlastCom`: the shrink never touches the buffer. -/
def arlHButlastCom (_bc len cap one four two fourN twoN outCap : String) : Com :=
  .seq (.binop .sub len len one)
    (.seq (.binop .mul fourN len four)
      (.seq (.binop .mul twoN len two)
        (.seq (.copy outCap cap)
          (.seq (arlSelectCapCom fourN twoN cap outCap) (.seq .skip .skip)))))

theorem arlHButlastCom_eq (bc len cap one four two fourN twoN outCap : String) :
    arlHButlastCom bc len cap one four two fourN twoN outCap =
      arlButlastCom bc len cap one four two fourN twoN outCap := rfl

/-! ### The registered executable rules -/

@[sepref_fr_rules] theorem arlHGet_exec_hnr
    (bc idx adr out : String) (p : ℕ) (buffer : List ℕ) (i : ℕ)
    (hi : i < buffer.length) :
    hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn i idx ∗
        junkCell adr ∗ junkCell out)
      (arlHGetCom bc idx adr out)
      (hnCtxt (heapBlockAssnAt p) buffer bc ∗ junkCell adr ∗ hnCtxt natAssn i idx)
      out natAssn (arlHGetExecSpec buffer i) := by
  rw [arlHGetExecSpec]
  rw [← arlHGetRaw_eq p buffer i hi]
  exact arlHGetSynth bc idx adr out p buffer i

@[sepref_fr_rules] theorem arlHLast_exec_hnr
    (bc len one idx adr out : String) (p : ℕ) (buffer : List ℕ) (n : ℕ)
    (hn : n ≠ 0) (hle : n ≤ buffer.length) :
    hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn 1 one ∗ junkCell idx ∗ junkCell adr ∗ junkCell out)
      (arlHLastCom bc len one idx adr out)
      (hnCtxt (heapBlockAssnAt p) buffer bc ∗ junkCell adr ∗ junkCell idx ∗
        hnCtxt natAssn n len ∗ hnCtxt natAssn 1 one)
      out natAssn (arlHLastExecSpec buffer n) := by
  rw [arlHLastExecSpec]
  rw [← arlHLastRaw_eq p buffer n hn hle]
  exact arlHLastSynth bc len one idx adr out p buffer n

@[sepref_fr_rules] theorem arlHSet_exec_hnr (bc len cap idx adr value : String)
    (p : ℕ) (buffer : List ℕ) (n c i x : ℕ) (hi : i < buffer.length) :
    hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn i idx ∗ junkCell adr ∗
        hnCtxt natAssn x value)
      (arlHSetCom bc len cap idx adr value)
      (junkCell adr ∗ hnCtxt natAssn x value ∗ hnCtxt natAssn i idx)
      (bc, (len, cap)) (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn)
      (arlHSetExecSpec buffer n c i x) := by
  rw [arlHSetExecSpec]
  rw [← arlHSetRaw_eq p buffer n c i x hi]
  exact arlHSetSynth bc len cap idx adr value p buffer n c i x

@[sepref_fr_rules] theorem arlHSwap_exec_hnr (bc len cap I J AI AJ XI XJ : String)
    (p : ℕ) (buffer : List ℕ) (n c i j : ℕ)
    (hi : i < buffer.length) (hj : j < buffer.length) :
    hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn n len ∗
        hnCtxt natAssn c cap ∗ hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        junkCell AI ∗ junkCell AJ ∗ junkCell XI ∗ junkCell XJ)
      (arlHSwapCom bc len cap I J AI AJ XI XJ)
      (junkCell AJ ∗ junkCell XI ∗ junkCell AI ∗ junkCell XJ ∗
        hnCtxt natAssn j J ∗ hnCtxt natAssn i I)
      (bc, (len, cap)) (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn)
      (arlHSwapExecSpec buffer n c i j) := by
  rw [arlHSwapExecSpec]
  rw [← arlHSwapRaw_eq p buffer n c i j hi hj]
  exact arlHSwapSynth bc len cap I J AI AJ XI XJ p buffer n c i j

@[sepref_fr_rules] theorem arlHButlast_exec_hnr
    (bc len cap one four two fourN twoN outCap : String)
    (p : ℕ) (buffer : List ℕ) (n c : ℕ) :
    hnRefine (hnCtxt (heapBlockAssnAt p) buffer bc ∗ hnCtxt natAssn n len ∗
      hnCtxt natAssn c cap ∗ hnCtxt natAssn 1 one ∗ hnCtxt natAssn 4 four ∗
      hnCtxt natAssn 2 two ∗ junkCell fourN ∗ junkCell twoN ∗ junkCell outCap)
      (arlHButlastCom bc len cap one four two fourN twoN outCap)
      (junkCell fourN ∗ junkCell twoN ∗ hnCtxt natAssn c cap ∗
        hnCtxt natAssn 2 two ∗ hnCtxt natAssn 4 four ∗ hnCtxt natAssn 1 one)
      (bc, (len, outCap))
      (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn)
      (arlHButlastExecSpec buffer n c) := by
  rw [← arlHButlastRaw_eq buffer n c]
  exact arlHButlastSynth bc len cap one four two fourN twoN outCap p buffer n c

/-! ## 4. Bridges to the cost-silent list interface

**Nothing here is re-derived.**  Each bridge is `ArrayList.lean`'s own
value-level theorem — `arlSetExecState_refines`, `arlButlastExecState_refines`,
`arlSwapExecState_refines`, `buffer_getElem_eq_active` — with this file's
cost substituted.  That is the whole content of "the representation theory and
the abstract refinement layer are reused": the re-seat cannot touch them,
because they say nothing about where the buffer lives. -/

theorem arlHGetExecSpec_refines {s : ArrayList} {xs : List ℕ} {i : ℕ}
    (h : (s, xs) ∈ arrayListRel) (hi : i < xs.length) :
    arlHGetExecSpec s.buffer i = NRest.consume (NRest.returnT xs[i]!) arlHGetCost := by
  have his : i < s.length := by simpa [arrayListRel_length h] using hi
  change s.Wf ∧ s.active = xs at h
  rw [arlHGetExecSpec, buffer_getElem_eq_active h.1 his, h.2]

theorem arlHLastExecSpec_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) (hne : xs ≠ []) :
    ∃ x, listAt? xs.reverse 0 = some x ∧
      arlHLastExecSpec s.buffer s.length = NRest.consume (NRest.returnT x) arlHLastCost := by
  obtain ⟨x, hx, hspec⟩ := arlLastExecSpec_refines h hne
  refine ⟨x, hx, ?_⟩
  have key : arlHLastExecSpec s.buffer s.length
      = NRest.consume (arlLastExecSpec s.buffer s.length) (irUnit Currency.add) := by
    rw [arlHLastExecSpec, arlLastExecSpec, NRest.consume_consume, arlHLastCost_eq]
    congr 1
    abel
  rw [key, hspec, NRest.consume_consume]
  congr 1
  rw [arlHLastCost_eq]
  abel

theorem arlHSetExecSpec_refines {s : ArrayList} {xs : List ℕ} {i x : ℕ}
    (h : (s, xs) ∈ arrayListRel) (hi : i < xs.length) :
    arlHSetExecSpec s.buffer s.length s.capacity i x = NRest.consume
        (NRest.returnT ((arlSetExecState s i x).buffer,
          ((arlSetExecState s i x).length, (arlSetExecState s i x).capacity)))
        arlHSetCost ∧
      (arlSetExecState s i x, listSet xs i x) ∈ arrayListRel :=
  ⟨rfl, arlSetExecState_refines h hi⟩

theorem arlHSwapExecSpec_refines {s : ArrayList} {xs : List ℕ} {i j : ℕ}
    (h : (s, xs) ∈ arrayListRel) (hi : i < xs.length) (hj : j < xs.length) :
    arlHSwapExecSpec s.buffer s.length s.capacity i j = NRest.consume
        (NRest.returnT ((arlSwapExecState s i j).buffer,
          ((arlSwapExecState s i j).length, (arlSwapExecState s i j).capacity)))
        arlHSwapCost ∧
      (arlSwapExecState s i j, listSwap xs i j) ∈ arrayListRel :=
  ⟨rfl, arlSwapExecState_refines h hi hj⟩

/-- `butlast`'s bridge is `ArrayList.lean`'s, verbatim: same spec, same cost,
same relation step.  Nothing about it is representation-dependent. -/
theorem arlHButlastExecSpec_refines {s : ArrayList} {xs : List ℕ}
    (h : (s, xs) ∈ arrayListRel) (hne : xs ≠ []) :
    arlHButlastExecSpec s.buffer s.length s.capacity = NRest.consume
        (NRest.returnT ((arlButlastExecState s).buffer,
          ((arlButlastExecState s).length, (arlButlastExecState s).capacity)))
        (arlButlastCost s.length s.capacity) ∧
      (arlButlastExecState s, listButlast xs) ∈ arrayListRel := by
  rw [arlHButlastExecSpec_eq]
  exact arlButlastExecSpec_refines h hne

/-! ## 5. The prices, as nine-currency vectors

`ArrayListCash.lean`'s `IrVecN`, so that each price is checkable in two
independent ways: `_toE` says the vector *is* the `ECost` this file's rules
pay, and the `#guard`s of § 6 say the *emitted program*, run on a concrete
heap, charges exactly that vector.  Ledger **F11**: every cost written here is
compared against what a program actually charges. -/

def arlHGetN : IrVecN := ⟨0, 0, 0, 0, 0, 0, 0, 1, 1⟩
/-- `last` pays one `ir.sub` beyond `get`, and `ir.sub` is **not** one of the
nine currencies `IrVecN` carries; the two vectors therefore coincide and the
`ir.sub` is checked by the run's full sixteen-currency vector in § 6 instead.
Recording the coincidence as an equation keeps that from looking like a slip. -/
def arlHLastN : IrVecN := ⟨0, 0, 0, 0, 0, 0, 0, 1, 1⟩

theorem arlHLastN_eq_get : arlHLastN = arlHGetN := rfl
def arlHSetN : IrVecN := ⟨0, 0, 0, 0, 0, 2, 1, 0, 1⟩
def arlHSwapN : IrVecN := ⟨0, 0, 0, 0, 0, 2, 2, 2, 2⟩

private theorem cost_two (c : String) :
    (ACost.cost c (2 : ℕ∞) : ECost) = ACost.cost c 1 + ACost.cost c 1 := by
  rw [ACost.cost_add_cost]; norm_num

theorem arlHGetN_toE : arlHGetN.toE = arlHGetCost := by
  rw [arlHGetN, arlHGetCost, IrVecN.toE]
  simp only [Nat.cast_zero, Nat.cast_one, ACost.cost_zero, irUnit]
  abel

/-- `last`'s `ECost`, against `get`'s. -/
theorem arlHLastCost_eq_get_add_sub :
    arlHLastCost = arlHGetCost + irUnit Currency.sub := by
  rw [arlHLastCost, arlHGetCost]; abel

theorem arlHSetN_toE : arlHSetN.toE = arlHSetCost := by
  rw [arlHSetN, arlHSetCost, IrVecN.toE]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, ACost.cost_zero, irUnit,
    two_nsmul, cost_two]
  abel

theorem arlHSwapN_toE : arlHSwapN.toE = arlHSwapCost := by
  rw [arlHSwapN, arlHSwapCost, IrVecN.toE]
  simp only [Nat.cast_zero, Nat.cast_ofNat, ACost.cost_zero, irUnit,
    two_nsmul, cost_two]
  abel

/-! ## 6. The compiled gate

The five emitted commands, run on a concrete heap by `evalFuel`, with their
values, their full cost vectors, and — for `get` and `swap` — a **differential**
against the landed named-array command on the same data, so that the `+ir.add`
of the header's table is measured rather than asserted. -/

namespace ArrayListHeapGate

open Lax13Proofs.Refine.Ir.Gate (costVector readVars readArrs)

/-- Eleven heap cells.  The live block is `[5, 6, 7, 8]` based at `3`; every
cell outside it is distinctive junk that must not move. -/
def gateHeap : List Val := [91, 92, 93, 5, 6, 7, 8, 94, 95, 96, 97]

def gateBase : ℕ := 3
def gateBuffer : List Val := [5, 6, 7, 8]

/-- Every scratch cell starts at distinctive **junk**, and where a control below
needs the wrong program to *run* rather than fault, that junk is a legal but
wrong heap address (`adr = 9`, `AI = 10`, `AJ = 9`).  Precedent: the previous
leaf's first draft of five controls ran from *zeroed* cells, and one of them was
vacuous because zero happened to be the right value. -/
def gateState : State :=
  State.ofPairs
    [("bc", 3), ("len", 4), ("cap", 4), ("one", 1), ("four", 4), ("two", 2),
      ("idx", 2), ("value", 40), ("I", 1), ("J", 3),
      ("adr", 9), ("out", 72), ("AI", 10), ("AJ", 9), ("XI", 75), ("XJ", 76)]
    [(heapName, gateHeap)]

/-! ### The five emitted commands, pinned

`arlH*_exec_hnr` already pins each command by definitional equality against the
synthesizer's output (that is what its `exact arlH*Synth …` checks).  These are
the same pins in literal, readable form. -/

#guard arlHGetCom "bc" "idx" "adr" "out" =
  (Com.binop .add "adr" "bc" "idx").seq (Com.aget "out" "$heap" "adr")

#guard arlHLastCom "bc" "len" "one" "idx" "adr" "out" =
  (Com.binop .sub "idx" "len" "one").seq
    ((Com.binop .add "adr" "bc" "idx").seq (Com.aget "out" "$heap" "adr"))

#guard arlHSetCom "bc" "len" "cap" "idx" "adr" "value" =
  (Com.binop .add "adr" "bc" "idx").seq
    ((Com.aset "$heap" "adr" "value").seq (Com.skip.seq Com.skip))

#guard arlHSwapCom "bc" "len" "cap" "I" "J" "AI" "AJ" "XI" "XJ" =
  (Com.binop .add "AI" "bc" "I").seq
    ((Com.binop .add "AJ" "bc" "J").seq
      ((Com.aget "XI" "$heap" "AI").seq
        ((Com.aget "XJ" "$heap" "AJ").seq
          ((Com.aset "$heap" "AI" "XJ").seq
            ((Com.aset "$heap" "AJ" "XI").seq (Com.skip.seq Com.skip))))))

-- `butlast` emits the landed command unchanged — that is the pin.
#guard arlHButlastCom "bc" "len" "cap" "one" "four" "two" "fourN" "twoN" "outCap" =
  arlButlastCom "bc" "len" "cap" "one" "four" "two" "fourN" "twoN" "outCap"

/-- The run's cost as one of `ArrayListCash.lean`'s nine-currency vectors. -/
def runVec (κ : Cost) : IrVecN :=
  ⟨κ.toFun Currency.ite, κ.toFun Currency.mul, κ.toFun Currency.«while»,
    κ.toFun Currency.copy, κ.toFun Currency.const, κ.toFun Currency.skip,
    κ.toFun Currency.aset, κ.toFun Currency.aget, κ.toFun Currency.add⟩

/-! ### `get` -/

def getOut : State × Cost :=
  (evalFuel 20 (arlHGetCom "bc" "idx" "adr" "out") gateState).getD (gateState, 0)

theorem getOut_evalFuel :
    evalFuel 20 (arlHGetCom "bc" "idx" "adr" "out") gateState = some getOut := rfl

theorem getOut_bigStep :
    BigStep (arlHGetCom "bc" "idx" "adr" "out") gateState getOut.1 getOut.2 :=
  bigStep_of_evalFuel getOut_evalFuel

-- The address is formed from the *base*, and the value read is the block's.
#guard readVars getOut.1 ["out", "adr", "bc"] =
  [("out", some 7), ("adr", some 5), ("bc", some 3)]
#guard readArrs getOut.1 [heapName] = [(heapName, some gateHeap)]
-- …and `7` is `gateBuffer[2]`, the abstract answer.
#guard (readVars getOut.1 ["out"]).head?.map (fun r => r.2) = some (some gateBuffer[2]!)
#guard runVec getOut.2 = arlHGetN
#guard costVector getOut.2 =
  [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 1), ("ir.aset", 0),
   ("ir.ite", 0), ("ir.while", 0), ("ir.add", 1), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! #### The differential against the landed named-array `get` -/

def arrGateState : State :=
  State.ofPairs [("idx", 2), ("out", 72)] [("A", gateBuffer)]

def arrGetOut : State × Cost :=
  (evalFuel 20 (arlGetCom "A" "idx" "out") arrGateState).getD (arrGateState, 0)

-- Same answer …
#guard (readVars arrGetOut.1 ["out"]) = (readVars getOut.1 ["out"])
-- … at exactly one extra `ir.add`, and nothing else.
#guard runVec getOut.2 = runVec arrGetOut.2 + ⟨0, 0, 0, 0, 0, 0, 0, 0, 1⟩

/-! ### `last` -/

def lastOut : State × Cost :=
  (evalFuel 20 (arlHLastCom "bc" "len" "one" "idx" "adr" "out") gateState).getD (gateState, 0)

theorem lastOut_evalFuel :
    evalFuel 20 (arlHLastCom "bc" "len" "one" "idx" "adr" "out") gateState = some lastOut := rfl

theorem lastOut_bigStep :
    BigStep (arlHLastCom "bc" "len" "one" "idx" "adr" "out") gateState lastOut.1 lastOut.2 :=
  bigStep_of_evalFuel lastOut_evalFuel

#guard readVars lastOut.1 ["out", "idx", "adr"] =
  [("out", some 8), ("idx", some 3), ("adr", some 6)]
#guard readArrs lastOut.1 [heapName] = [(heapName, some gateHeap)]
#guard (readVars lastOut.1 ["out"]).head?.map (fun r => r.2) = some (some gateBuffer[3]!)
#guard runVec lastOut.2 = arlHLastN
#guard costVector lastOut.2 =
  [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 1), ("ir.aset", 0),
   ("ir.ite", 0), ("ir.while", 0), ("ir.add", 1), ("ir.sub", 1), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! ### `set` -/

def setOut : State × Cost :=
  (evalFuel 20 (arlHSetCom "bc" "len" "cap" "idx" "adr" "value") gateState).getD (gateState, 0)

theorem setOut_evalFuel :
    evalFuel 20 (arlHSetCom "bc" "len" "cap" "idx" "adr" "value") gateState
      = some setOut := rfl

theorem setOut_bigStep :
    BigStep (arlHSetCom "bc" "len" "cap" "idx" "adr" "value") gateState setOut.1 setOut.2 :=
  bigStep_of_evalFuel setOut_evalFuel

-- Exactly one heap cell changed, and it is offset 2 of the block.
#guard readArrs setOut.1 [heapName] =
  [(heapName, some [91, 92, 93, 5, 6, 40, 8, 94, 95, 96, 97])]
#guard ((readArrs setOut.1 [heapName]).head?.map fun r =>
    ((r.2.getD []).drop gateBase).take 4) = some (gateBuffer.set 2 40)
#guard readVars setOut.1 ["adr", "bc", "len", "cap"] =
  [("adr", some 5), ("bc", some 3), ("len", some 4), ("cap", some 4)]
#guard runVec setOut.2 = arlHSetN
#guard costVector setOut.2 =
  [("ir.skip", 2), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 0), ("ir.aset", 1),
   ("ir.ite", 0), ("ir.while", 0), ("ir.add", 1), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! ### `swap` -/

def swapOut : State × Cost :=
  (evalFuel 30 (arlHSwapCom "bc" "len" "cap" "I" "J" "AI" "AJ" "XI" "XJ") gateState).getD
    (gateState, 0)

theorem swapOut_evalFuel :
    evalFuel 30 (arlHSwapCom "bc" "len" "cap" "I" "J" "AI" "AJ" "XI" "XJ") gateState
      = some swapOut := rfl

theorem swapOut_bigStep :
    BigStep (arlHSwapCom "bc" "len" "cap" "I" "J" "AI" "AJ" "XI" "XJ") gateState
      swapOut.1 swapOut.2 :=
  bigStep_of_evalFuel swapOut_evalFuel

#guard readArrs swapOut.1 [heapName] =
  [(heapName, some [91, 92, 93, 5, 8, 7, 6, 94, 95, 96, 97])]
-- …and the block, read back, is `listSwap`'s answer at the abstract level.
#guard ((readArrs swapOut.1 [heapName]).head?.map fun r =>
    ((r.2.getD []).drop gateBase).take 4) = some (listSwap gateBuffer 1 3)
#guard readVars swapOut.1 ["AI", "AJ", "XI", "XJ"] =
  [("AI", some 4), ("AJ", some 6), ("XI", some 6), ("XJ", some 8)]
#guard runVec swapOut.2 = arlHSwapN
#guard costVector swapOut.2 =
  [("ir.skip", 2), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 2), ("ir.aset", 2),
   ("ir.ite", 0), ("ir.while", 0), ("ir.add", 2), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

def arrSwapState : State :=
  State.ofPairs [("I", 1), ("J", 3), ("XI", 75), ("XJ", 76)] [("A", gateBuffer)]

def arrSwapOut : State × Cost :=
  (evalFuel 30 (arlSwapCom "A" "len" "cap" "I" "J" "XI" "XJ") arrSwapState).getD
    (arrSwapState, 0)

-- Same answer, two extra `ir.add`, nothing else.
#guard readArrs arrSwapOut.1 ["A"] = [("A", some (listSwap gateBuffer 1 3))]
#guard runVec swapOut.2 = runVec arrSwapOut.2 + ⟨0, 0, 0, 0, 0, 0, 0, 0, 2⟩

/-! ### `butlast`

The shrink is metadata-only, so what has to be checked here is that the
re-seat did **not** turn it into a heap operation: the emitted command is the
landed one and the heap is bit-identical after the run. -/

def butlastState : State :=
  State.ofPairs
    [("bc", 3), ("len", 17), ("cap", 100), ("one", 1), ("four", 4), ("two", 2),
      ("fourN", 77), ("twoN", 78), ("outCap", 79)]
    [(heapName, gateHeap)]

def butlastOut : State × Cost :=
  (evalFuel 30 (arlHButlastCom "bc" "len" "cap" "one" "four" "two" "fourN" "twoN" "outCap")
    butlastState).getD (butlastState, 0)

theorem butlastOut_evalFuel :
    evalFuel 30 (arlHButlastCom "bc" "len" "cap" "one" "four" "two" "fourN" "twoN" "outCap")
      butlastState = some butlastOut := rfl

-- `len` drops to 16, `16 * 4 = 64 < 100`, `15 < 32`, so the capacity shrinks to 32 …
#guard readVars butlastOut.1 ["len", "outCap", "fourN", "twoN", "cap", "bc"] =
  [("len", some 16), ("outCap", some 32), ("fourN", some 64), ("twoN", some 32),
   ("cap", some 100), ("bc", some 3)]
-- …which is `arlShrinkCapacity`'s answer, and the heap is untouched.
#guard (readVars butlastOut.1 ["outCap"]).head?.map (fun r => r.2)
  = some (some (arlShrinkCapacity ⟨List.replicate 100 0, 17, 100⟩ 16))
#guard readArrs butlastOut.1 [heapName] = [(heapName, some gateHeap)]

/-! ### Negative controls, each flipped and confirmed to bite

Every control is a *mutilation* of an emitted command above.  They are stated
as `≠` against the correct run, so each one compiles only because the mutilated
program really does produce a different answer. -/

/-- **Control 1 — no address formation.**  Read `heap[adr]` with `adr` at its
junk value `9`: a legal heap index, so the program runs to completion and
answers `96` instead of `7`.  This is the control that would be vacuous from a
zeroed scratch cell. -/
def getNoAddrProg : Com := .aget "out" heapName "adr"

#guard readVars ((evalFuel 20 getNoAddrProg gateState).getD (gateState, 0)).1 ["out"]
  ≠ readVars getOut.1 ["out"]

/-- **Control 2 — the base pointer ignored.**  Use the *offset* as the address,
i.e. read as if the block were based at `0`.  This is the one control that is
specifically about the re-seat: it answers `93`, a cell below the block. -/
def getBaseZeroProg : Com := .aget "out" heapName "idx"

#guard readVars ((evalFuel 20 getBaseZeroProg gateState).getD (gateState, 0)).1 ["out"]
  ≠ readVars getOut.1 ["out"]

/-- **Control 3 — `last` without the predecessor step.**  `idx` keeps its
input value `2`, so the read lands one slot short of the end. -/
def lastNoSubProg : Com := arlHGetCom "bc" "idx" "adr" "out"

#guard readVars ((evalFuel 20 lastNoSubProg gateState).getD (gateState, 0)).1 ["out"]
  ≠ readVars lastOut.1 ["out"]

/-- **Control 4 — `set` without address formation.**  The write lands at the
junk address `9`, outside the block: the buffer is unchanged and the junk
above it is corrupted. -/
def setNoAddrProg : Com :=
  .seq (.aset heapName "adr" "value") (.seq .skip .skip)

#guard readArrs ((evalFuel 20 setNoAddrProg gateState).getD (gateState, 0)).1 [heapName]
  ≠ readArrs setOut.1 [heapName]

/-- **Control 5 — `swap` missing the second address.**  `AJ` keeps its junk
value `9`, so the second half of the exchange happens outside the block. -/
def swapNoAJProg : Com :=
  .seq (.binop .add "AI" "bc" "I")
    (.seq (.aget "XI" heapName "AI")
      (.seq (.aget "XJ" heapName "AJ")
        (.seq (.aset heapName "AI" "XJ")
          (.seq (.aset heapName "AJ" "XI") (.seq .skip .skip)))))

#guard readArrs ((evalFuel 30 swapNoAJProg gateState).getD (gateState, 0)).1 [heapName]
  ≠ readArrs swapOut.1 [heapName]

/-! **Control 6 — the cost claim itself.**  Dropping the `ir.add` from `get`'s
predicted vector makes the prediction fail against the run.  This is the check
that ledger F11's failure class is being tested for and not merely mentioned. -/
#guard runVec getOut.2 ≠ ⟨0, 0, 0, 0, 0, 0, 0, 1, 0⟩

end ArrayListHeapGate

/-! ## 7. Axiom gate -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_mop_haget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_haget

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_mop_haset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_haset

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_mop_haddr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_haddr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHGet_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHGet_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHLast_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHLast_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHSet_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHSet_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHSwap_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHSwap_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHButlast_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHButlast_exec_hnr

/--
info: 'Lax13Proofs.Refine.Sepref.Iicf.heapArrayListAssn_entails_packed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms heapArrayListAssn_entails_packed

end Lax13Proofs.Refine.Sepref.Iicf
