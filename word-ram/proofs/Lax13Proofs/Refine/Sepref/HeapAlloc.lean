import Lax13Proofs.Refine.Sepref.IrOps
import Lax13Proofs.Refine.Sepref.Definition
import Lax13Proofs.Refine.Ir.Heap

/-!
The costed bump allocator, `free`, and their registered refinement rules.

Leaves **P4.5.A.2** and **P4.5.A.3** of
`plans/word-ram/tower-expansion/p4.5-design.md` (decision **D-A2**,
ledger **E24**), on top of A.1's range ownership.

Source pin `isabelle_llvm_time` @ `42dd7f5`,
`thys/sepref/Hnr_Primitives_Experiment.thy` (design note §3A):

```isabelle
mop_oarray_new n = consume (RETURNT (replicate n None)) (lift_acost (cost'_narray_new n))
lemma hnr_eoarray_new'[sepref_fr_rules]:
  "(narrayo_new TYPE('a), mop_oarray_new) ∈ snat_assn^k →⇩a (eoarray_assn A)"
```

Two things port verbatim and one deviates.

*Verbatim.* The **shape**: the abstract value is the list, the concrete
value is the **base pointer**, and the assertion (`eoarray_assn` there,
`heapBlockAssn` here) relates them; and the **unconditionality** — the
size argument is *kept* (`snat_assn⇧k`, `hnCtxt` on both sides) and there
is no `ASSERT` beyond the source's tagging no-op. `mopAlloc` below has no
`assert` either, which is the property the whole phase exists to
reproduce.

*Deviating.* The **cost**, ledger **E24**. The source pays
`cost ''malloc'' n`, because a real LLVM `malloc` costs proportionally to
the block it hands back. Ours is `irUnit copy + irUnit add` — two IR
steps, *independent of `n`*. That is a **substrate** deviation, not an
optimisation: `Lax13/Ram.lean`'s cells already exist and already hold
zero (`Imp.lean:305`, "an array costs nothing, since the machine's memory
starts zeroed"), so we are not doing the source's work faster, we are on
a machine where that work does not exist. `allocCost` is a function of
the block size that does not mention it, and §4's controls fail if a
linear term ever creeps in.

At this leaf the element layer does not exist yet (that is B), so the
abstract value is the zero-filled list rather than the `None`-filled one.

## A.3 — the E23 correction, and what it buys

Ledger **E23** gave two reasons for excluding deallocation. The second
still holds; **the first does not, and A.2 is what showed it.** E23 said
the O(1) allocation is bought by never reusing memory. What it is
actually bought by is the handed-out region being *known to read zero*,
and `avail` carries that knowledge **in the assertion** rather than
deriving it from "never touched". Non-reuse is only how zeroness is
established at entry. Since `lo_init` says an all-`None` EO array owns no
element memory whatever the concrete contents, leaf B's arrays need no
zeroed backing at all, so for them reuse is free rather than O(n).

So there are two availability flavours — `avail` (zeroed) and `availRaw`
(contents unspecified) — with `avail_entails_availRaw` one way and **no
theorem the other way**, because restoring zeroness is O(n).
`availRaw_not_entails_avail` states that boundary rather than leaving it
as an absence. Consequently:

* O(1) **zeroed** allocation is untouched — `alloc_triple`, `alloc_rule`
  and `hnr_mop_alloc` keep their exact statements, so E24's headline and
  the n² dissolution are undisturbed;
* O(1) **raw** allocation is available (`hnr_mop_allocRaw`), which is
  what leaf B will want;
* O(1) **reuse** is available (`free_allocRaw_reuse`);
* a **zeroed** block out of reused memory in O(1) is *not* available, and
  nothing here should look as though it were.

`allocGen_triple` is why the two flavours cost the same: the allocator
never reads or writes the heap, so the space assertion rides through as a
frame and both flavours are instances of one triple.

## The design point: ownership, not a precondition (D-A2)

An allocator cannot conjure ownership. The naive way to arrange it is a
side condition like `hp + n ≤ limit`, which would put conditionality back
on the operation and defeat the phase. Instead the unallocated space is a
**resource in an assertion** — `avail hp k`, owning the bump-pointer cell
and the `k` zero-reading cells above it — and `alloc n` *consumes* `n`
units of it, splitting `[hp, hp + n)` off by A.1's `ptoH_append`. The
abstract operation stays unconditional; what a caller must supply is
ownership, exactly as it must already supply `¤¤` credits, and the frame
rule carries the rest. The rule's precondition is `avail hp (n + k)` for
an arbitrary leftover `k`: that is a decomposition of what the caller
owns, not an inequality the operation imposes.

Two consequences are theorems here, not comments:

* **No reuse is linearity, not an invariant.** `avail_split` *moves*
  `[hp, hp + n)` out of the availability resource, so what is left owns
  nothing below `hp + n` (`avail_owns_nothing_below`) and the same range
  cannot be handed out twice (`alloc_no_reuse`). Nothing is assumed.
* **Zero contents come from the machine, established once.**
  `avail_of_entry` reads the availability resource off an entry state
  whose reserved heap array is `List.replicate m 0` and whose bump cell
  is `0` — which is exactly `Imp.initEnv`'s shape (`vars := fun _ => 0`,
  `arrs := fun a => List.replicate (ext a) 0`). It is discharged once,
  at entry, and never re-proved per call.

## Exhaustion is global, and is not restated here (D-A3)

The program-level condition already exists: `Layout.FitsWords B w`
(`Compile.lean:85`), whose `span` clause is `L.span B ≤ 2 ^ w` with
`L.span B = L.temps + L.scalars.length + L.arrays.length * B`, and the
array lengths are existential per input (`Codegen/Cash.lean:389`,
`solves_of_spec`). **This file authors no second exhaustion condition** —
a per-operation copy is precisely the rule-5 violation the phase exists
to remove. The relation is *recorded* instead: the availability resource
has size `m`, the reserved heap array's length; an index of that array is
addressed at `L.arrAddr heapName i = L.arrBase heapName + L.arrays.length * i`
and `Layout.span` reserves `L.arrays.length * B` for all array cells
together, so `m ≤ B` puts the whole availability resource inside the
span, and `FitsWords.span` then puts it inside `2 ^ w`.

That relation is recorded **here, in prose, and nowhere as a theorem of
this file**. A statement worth proving would have to relate the
availability resource's size to `ext heapName` and thence to `B`, which
puts it at the `Codegen/` boundary where `initEnv` and `Solves` live —
not in a refinement rule, which has no business seeing which layout a
program is compiled under. Nothing below takes a `Layout` argument and
this file does not import `Compile`.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. The availability resource -/

/-- The reserved scalar cell holding the bump pointer. Named in exactly
one place, like `Ir.heapName`; unlike `heapName` it needs no partition of
the carrier, because it is an ordinary scalar cell that the availability
assertion simply owns. -/
def hpName : String := "$hp"

/-- **The unallocated space, as a resource.** The bump pointer, and the
`k` cells above it that have not been handed out — which read zero
because the machine's memory starts zeroed and the allocator never
returns a cell twice.

This is the object that replaces a `hp + n ≤ limit` precondition: a
caller supplies ownership, not an inequality. -/
def avail (hp k : ℕ) : Assn := (hpName ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate k 0)

/-- **The split law**, and it is an equation: the `n + k` cells of
unallocated space *are* the `n` handed out beside the `k` left above
them. This is A.1's `ptoH_append` at a replicated range, and it is the
whole mechanism of the allocator — the block is not created, it is
carved out of what the caller already owned. -/
theorem availSpace_split (hp n k : ℕ) :
    (hp ↦ₕ List.replicate (n + k) 0)
      = (hp ↦ₕ List.replicate n 0) ∗ ((hp + n) ↦ₕ List.replicate k 0) := by
  rw [List.replicate_add, ptoH_append, List.length_replicate]

/-- The same at the whole availability resource: the bump-pointer cell,
the block handed out, and the space left above it. The bump pointer's
*value* is not part of this equation — advancing it is the program's
doing, which is why the consumption shows up in `alloc_triple` rather
than as a resource identity. -/
theorem avail_split (hp n k : ℕ) :
    avail hp (n + k) = (hpName ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗
      ((hp + n) ↦ₕ List.replicate k 0) := by
  rw [avail, availSpace_split]

/-! ### Raw availability (A.3)

**The E23 correction.** Ledger E23 said the O(1) allocation is bought by
never reusing memory. That is wrong, and `avail` above is the evidence:
what the O(1) actually needs is that the handed-out region is *known to
read zero*, and that knowledge is carried **in the assertion**, not
derived from "never touched". Non-reuse is merely how zeroness is
established at entry (`avail_of_entry`). Since `lo_init`
(`p4.5-design.md` §3) says an all-`None` EO array owns no element memory
*whatever the concrete contents*, leaf B's arrays do not need zeroed
backing at all — so for them reuse is free rather than O(n).

Hence two flavours, one refining the other:

* **zeroed** — `avail`, above: `k` cells I own, known to read zero;
* **raw** — `availRaw`, here: `k` cells I own, contents unspecified.

`avail_entails_availRaw` is the refinement. **The converse has no
theorem, and must not**: turning raw memory back into zeroed memory costs
one write per cell, so it is O(n), and stating it in O(1) would be
false. `availRaw_not_entails_avail` pins that as a theorem rather than
leaving it as an absence. Fresh memory arrives zeroed from
`Imp.initEnv`; freed memory returns **raw**. -/

/-- `k` cells at `hp` that I own and whose contents are unspecified. The
existential is the source's own device: `nao_assn A xs p` is
`EXS xsi. narray_assn xsi p ** …`, hiding the concrete backing exactly
this way. -/
def rawSpace (hp k : ℕ) : Assn := ∃ᵃ zs, (⌜zs.length = k⌝ ∗ (hp ↦ₕ zs))

theorem rawSpace_apply {hp k : ℕ} {h : AState} :
    rawSpace hp k h ↔ ∃ zs : List Val, zs.length = k ∧ (hp ↦ₕ zs) h := by
  constructor
  · rintro ⟨zs, hz⟩
    exact ⟨zs, (predLift_sepConj_iff.1 hz).1, (predLift_sepConj_iff.1 hz).2⟩
  · rintro ⟨zs, hl, hz⟩
    exact ⟨zs, predLift_sepConj_iff.2 ⟨hl, hz⟩⟩

/-- A concrete block is raw space: forget the contents, keep the size. -/
theorem ptoH_entails_rawSpace (hp : ℕ) (zs : List Val) :
    (hp ↦ₕ zs) ⊢ rawSpace hp zs.length := fun _ h => rawSpace_apply.2 ⟨zs, rfl, h⟩

/-- **The raw split law**, and it is an equation, exactly as the zeroed
one is. -/
theorem rawSpace_split (hp n k : ℕ) :
    rawSpace hp (n + k) = rawSpace hp n ∗ rawSpace (hp + n) k := by
  funext h
  refine propext ⟨?_, ?_⟩
  · intro hh
    obtain ⟨zs, hlen, hz⟩ := rawSpace_apply.1 hh
    have htake : (zs.take n).length = n := by rw [List.length_take]; omega
    have hsplit : (hp ↦ₕ zs) = ((hp ↦ₕ zs.take n) ∗ ((hp + n) ↦ₕ zs.drop n)) := by
      conv_lhs => rw [← List.take_append_drop n zs]
      rw [ptoH_append, htake]
    rw [hsplit] at hz
    obtain ⟨x, y, hd, hxy, hx, hy⟩ := hz
    exact ⟨x, y, hd, hxy, rawSpace_apply.2 ⟨zs.take n, htake, hx⟩,
      rawSpace_apply.2 ⟨zs.drop n, by rw [List.length_drop]; omega, hy⟩⟩
  · rintro ⟨x, y, hd, hxy, hx, hy⟩
    obtain ⟨xs, hxl, hxs⟩ := rawSpace_apply.1 hx
    obtain ⟨ys, hyl, hys⟩ := rawSpace_apply.1 hy
    refine rawSpace_apply.2 ⟨xs ++ ys, by simp [hxl, hyl], ?_⟩
    rw [ptoH_append hp xs ys, hxl]
    exact ⟨x, y, hd, hxy, hxs, hys⟩

/-- The unallocated space with its contents forgotten: the bump pointer
and `k` cells I own but know nothing about. This is what `free` returns
and what leaf B's allocation will consume. -/
def availRaw (hp k : ℕ) : Assn := (hpName ↦ᵥ hp) ∗ rawSpace hp k

theorem availRaw_split (hp n k : ℕ) :
    availRaw hp (n + k) = (hpName ↦ᵥ hp) ∗ rawSpace hp n ∗ rawSpace (hp + n) k := by
  rw [availRaw, rawSpace_split]

/-- **Zeroed refines raw.** Forgetting the contents is free. -/
theorem avail_entails_availRaw (hp k : ℕ) : avail hp k ⊢ availRaw hp k := by
  rw [avail, availRaw]
  refine sepConj_mono_right ?_
  intro h hh
  exact rawSpace_apply.2 ⟨List.replicate k 0, List.length_replicate, hh⟩

/-- **…and the converse is false.** Raw memory is not zeroed memory: no
O(1) rule turns one into the other, and this theorem is why there is no
such rule to look for. Restoring zeroness costs one write per cell. -/
theorem availRaw_not_entails_avail (hp : ℕ) : ¬ (availRaw hp 1 ⊢ avail hp 1) := by
  intro hent
  have hw : availRaw hp 1 ((Cells.single hpName hp, 0, hrange hp [7]), 0) := by
    refine ⟨((Cells.single hpName hp, 0, 0), 0), ((0, 0, hrange hp [7]), 0),
      ⟨⟨fun y => ?_, fun b => Tsa.zero_disj _, fun i => Tsa.zero_disj _⟩, trivial⟩, ?_,
      ⟨⟨rfl, rfl⟩, rfl⟩, rawSpace_apply.2 ⟨[7], rfl, ⟨⟨rfl, rfl, rfl⟩, rfl⟩⟩⟩
    · exact Tsa.disj_zero _
    · show ((Cells.single hpName hp, 0, hrange hp [7]), (0 : ECost))
        = ((Cells.single hpName hp, 0, 0), 0) + ((0, 0, hrange hp [7]), 0)
      rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_add_mk, sep_add_zero, sep_zero_add,
        sep_zero_add, sep_zero_add]
  have hz := hent _ hw
  obtain ⟨-, hz2⟩ := ptoVar_sepConj_iff.1 hz
  obtain ⟨-, -, hH, -⟩ := ptoH_apply.1 hz2
  have h7 : hrange hp [7] hp = Tsa.triv 7 := hrange_apply_mem (xs := [7]) (j := 0) (by simp)
  have h0 : hrange hp (List.replicate 1 0) hp = Tsa.triv 0 :=
    hrange_apply_mem (xs := List.replicate 1 0) (j := 0) (by simp)
  have hcell := congrFun hH hp
  rw [h7, h0] at hcell
  simp at hcell

/-! ### No reuse, as a consequence of linearity

Neither of these is an invariant carried alongside the allocator; both
are read off `avail_split`. -/

/-- The availability resource left after an allocation owns **nothing**
below the new bump pointer: the range just handed out is gone from it.
That is why a later allocation cannot return any index of an earlier
one — the resource it draws from does not contain them. -/
theorem avail_owns_nothing_below {hp k i : ℕ} (hi : i < hp) {V : Cells Val}
    {Ar : Cells (List Val)} {H : HCells} {cr : ECost} (h : avail hp k ((V, Ar, H), cr)) :
    H i = 0 := by
  obtain ⟨-, h2⟩ := ptoVar_sepConj_iff.1 h
  obtain ⟨-, -, rfl, -⟩ := ptoH_apply.1 h2
  exact hrange_apply_of_lt hi

/-- **No reuse.** The same block cannot be handed out twice: owning
`[hp, hp + n)` twice is `sepFalse`. With `avail_split` this is the whole
no-reuse argument — the first allocation removed the range, so a second
copy of it is not derivable from what is left. -/
theorem alloc_no_reuse (hp n : ℕ) (hn : 0 < n) :
    ((hp ↦ₕ List.replicate n 0) ∗ (hp ↦ₕ List.replicate n 0)) = (sepFalse : Assn) := by
  refine ptoH_sepConj_overlap (le_refl hp) ?_ ?_ <;> simpa using hn

/-- …while two *successive* allocations do compose: their ranges are
disjoint by construction, because the second draws from `avail (hp + n)`.
-/
theorem alloc_succ_disj (hp n n' : ℕ) :
    hrange hp (List.replicate n 0) ## hrange (hp + n) (List.replicate n' 0) := by
  have h := hrange_disj_append hp (List.replicate n 0) (List.replicate n' 0)
  rwa [List.length_replicate] at h

/-! ### Zero contents, established once at entry -/

/-- The reserved heap array of a zero-filled entry state *is* the
availability range. -/
theorem hcells_replicate {s : State} {m : ℕ}
    (h : s.arrs heapName = some (List.replicate m 0)) :
    hcells s = hrange 0 (List.replicate m 0) := by
  funext i
  rw [hcells_apply, h]
  by_cases hi : i < m
  · have := hrange_apply_mem (p := 0) (xs := List.replicate m 0) (j := i)
      (by simpa using hi)
    simp only [Nat.zero_add] at this
    rw [this]
    simp [hi]
  · rw [hrange_apply_of_ge (by simpa using Nat.le_of_not_lt hi)]
    simp [Nat.le_of_not_lt hi]

/-- **Zero contents come from the machine, once.** At an entry state
whose bump cell reads `0` and whose reserved heap array holds
`List.replicate m 0` — exactly `Imp.initEnv`'s shape, `vars := fun _ => 0`
and `arrs := fun a => List.replicate (ext a) 0` — the availability
resource holds for the whole heap. Discharged here, never per call. -/
theorem avail_of_entry {s : State} {F : Assn} {m : ℕ} {cr : ECost}
    (hhp : s.vars hpName = some 0)
    (harr : s.arrs heapName = some (List.replicate m 0))
    (hF : F (((vcells s).erase hpName, acells s, 0), cr)) :
    irSTATE (avail 0 m ∗ F) (s, cr) := by
  rw [avail, sepConj_assoc]
  show ((hpName ↦ᵥ 0) ∗ (0 ↦ₕ List.replicate m 0) ∗ F) ((vcells s, acells s, hcells s), cr)
  refine ptoVar_sepConj_iff.2 ⟨by simp [hhp], ?_⟩
  rw [hcells_replicate harr]
  refine ptoH_sepConj_iff.2 ⟨fun j hj => ?_, ?_⟩
  · rw [← hcells_replicate harr]
    rw [hcells_apply, harr]
    simp only [Nat.zero_add]
    have hj' : j < m := by simpa using hj
    simp [hj']
  · have hz : HCells.eraseRange (hrange 0 (List.replicate m 0)) 0
        (List.replicate m 0).length = 0 := by
      funext i
      by_cases hi : i < m
      · simp [HCells.eraseRange, hi]
      · simp only [HCells.eraseRange, List.length_replicate, Nat.zero_add,
          if_neg (by omega : ¬ ((0 : ℕ) ≤ i ∧ i < m))]
        exact hrange_apply_of_ge (by simpa using Nat.le_of_not_lt hi)
    rw [hz]
    exact hF

/-! ## 2. The program, its cost, and its triple -/

/-- **The allocator's price**, as a function of the block size — which it
does not mention. Two IR steps: read the bump pointer, advance it.
Ledger E24: this is a *substrate* deviation from `cost'_narray_new n`,
not an optimisation. -/
def allocCost (_n : ℕ) : ECost := irUnit Currency.copy + irUnit Currency.add

/-- The cost is `n`-independent, as an equation. -/
theorem allocCost_const (n n' : ℕ) : allocCost n = allocCost n' := rfl

/-- …and here it is, spelled out. -/
theorem allocCost_eq (n : ℕ) : allocCost n = irUnit Currency.copy + irUnit Currency.add := rfl

/-- **The allocator**, as two existing constructors: `pc := hp`, then
`hp := hp + nc`. No new `Ir.Com` constructor, so the sixteen currencies,
`embed`, `weight`/`cash`, `BigStepB` and `embed_sim` are inherited
unchanged and the D3 codegen obligation stays discharged by
inheritance. -/
def allocProg (pc nc : String) : Com :=
  (Com.copy pc hpName).seq (Com.binop Imp.Bop.add hpName hpName nc)

/-- The assertion between the allocator's two instructions: the base
pointer is already in `pc`, the bump pointer has not moved yet, and the
`add`'s own unit is still unspent. -/
private def allocMid (pc nc : String) (hp n : ℕ) (S : Assn) : Assn :=
  ¤¤Currency.add 1 ∗ (pc ↦ᵥ hp) ∗ (hpName ↦ᵥ hp) ∗ (nc ↦ᵥ n) ∗ S

/-- **The allocator is heap-blind.** Neither instruction reads or writes
the heap, so whatever space assertion `S` the caller owns rides through
as a frame. Both availability flavours are instances of this one triple,
which is why raw allocation costs exactly what zeroed allocation costs:
the program is the same program. -/
theorem allocGen_triple (pc nc : String) (old hp n : ℕ) (S : Assn) :
    irTriple (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ (hpName ↦ᵥ hp) ∗ S ∗ (nc ↦ᵥ n))
      (allocProg pc nc)
      ((pc ↦ᵥ hp) ∗ (hpName ↦ᵥ (hp + n)) ∗ S ∗ (nc ↦ᵥ n)) := by
  have h1 : irTriple (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ (hpName ↦ᵥ hp) ∗ S ∗ (nc ↦ᵥ n))
      (Com.copy pc hpName) (allocMid pc nc hp n S) := by
    have hcopy := frame_rule (wp := wp) (α := irα)
      (¤¤Currency.add 1 ∗ (nc ↦ᵥ n) ∗ S) (copy_triple pc hpName old hp)
    have ePre : (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ (hpName ↦ᵥ hp) ∗ S ∗ (nc ↦ᵥ n))
        = ((¤¤Currency.copy 1 ∗ (pc ↦ᵥ old) ∗ (hpName ↦ᵥ hp)) ∗
          (¤¤Currency.add 1 ∗ (nc ↦ᵥ n) ∗ S)) := by
      rw [allocCost_eq, credits_add]
      simp only [costCredits_one]
      ac_rfl
    have ePost : allocMid pc nc hp n S
        = (((pc ↦ᵥ hp) ∗ (hpName ↦ᵥ hp)) ∗ (¤¤Currency.add 1 ∗ (nc ↦ᵥ n) ∗ S)) := by
      rw [allocMid]
      ac_rfl
    rw [ePre, ePost]
    exact hcopy
  have h2 : irTriple (allocMid pc nc hp n S) (Com.binop Imp.Bop.add hpName hpName nc)
      ((pc ↦ᵥ hp) ∗ (hpName ↦ᵥ (hp + n)) ∗ S ∗ (nc ↦ᵥ n)) := by
    have hadd := frame_rule (wp := wp) (α := irα) ((pc ↦ᵥ hp) ∗ S)
      (binop_self_triple Imp.Bop.add hpName nc hp n)
    rw [Imp.Bop.apply_add, binopCurrency_add] at hadd
    have ePre : allocMid pc nc hp n S
        = ((¤¤Currency.add 1 ∗ (hpName ↦ᵥ hp) ∗ (nc ↦ᵥ n)) ∗ ((pc ↦ᵥ hp) ∗ S)) := by
      rw [allocMid]
      ac_rfl
    have ePost : ((pc ↦ᵥ hp) ∗ (hpName ↦ᵥ (hp + n)) ∗ S ∗ (nc ↦ᵥ n))
        = ((((hpName ↦ᵥ (hp + n)) ∗ (nc ↦ᵥ n))) ∗ ((pc ↦ᵥ hp) ∗ S)) := by
      ac_rfl
    rw [ePre, ePost]
    exact hadd
  rw [allocProg]
  exact seq_triple h1 h2

/-- **The allocator's exact triple.** Pay `allocCost n` — two units, no
`n` — own the bump pointer and `n + k` cells of unallocated space, and
get back the base pointer in `pc`, the block `[hp, hp + n)` holding
zeros, and the availability resource at the advanced pointer. The size
cell survives, as the source's `snat_assn⇧k` keeps it. -/
theorem alloc_triple (pc nc : String) (old hp n k : ℕ) :
    irTriple (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
      (allocProg pc nc)
      ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n)) := by
  have h := allocGen_triple pc nc old hp n (hp ↦ₕ List.replicate (n + k) 0)
  have ePre : (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
      = (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ (hpName ↦ᵥ hp) ∗
        (hp ↦ₕ List.replicate (n + k) 0) ∗ (nc ↦ᵥ n)) := by
    rw [avail]
    ac_rfl
  have ePost : ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n))
      = ((pc ↦ᵥ hp) ∗ (hpName ↦ᵥ (hp + n)) ∗
        (hp ↦ₕ List.replicate (n + k) 0) ∗ (nc ↦ᵥ n)) := by
    rw [avail, availSpace_split]
    ac_rfl
  rw [ePre, ePost]
  exact h

/-- **The raw allocator's exact triple** — the same program, the same
cost, a weaker precondition and a weaker postcondition. This is the one
leaf B will use, because an all-`None` EO array owns no element memory
and so does not need zeroed backing (`lo_init`). -/
theorem allocRaw_triple (pc nc : String) (old hp n k : ℕ) :
    irTriple (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ availRaw hp (n + k) ∗ (nc ↦ᵥ n))
      (allocProg pc nc)
      ((pc ↦ᵥ hp) ∗ rawSpace hp n ∗ availRaw (hp + n) k ∗ (nc ↦ᵥ n)) := by
  have h := allocGen_triple pc nc old hp n (rawSpace hp (n + k))
  have ePre : (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ availRaw hp (n + k) ∗ (nc ↦ᵥ n))
      = (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ (hpName ↦ᵥ hp) ∗ rawSpace hp (n + k) ∗ (nc ↦ᵥ n)) := by
    rw [availRaw]
    ac_rfl
  have ePost : ((pc ↦ᵥ hp) ∗ rawSpace hp n ∗ availRaw (hp + n) k ∗ (nc ↦ᵥ n))
      = ((pc ↦ᵥ hp) ∗ (hpName ↦ᵥ (hp + n)) ∗ rawSpace hp (n + k) ∗ (nc ↦ᵥ n)) := by
    rw [availRaw, rawSpace_split]
    ac_rfl
  rw [ePre, ePost]
  exact h

/-- The garbage-collecting forms. -/
theorem alloc_rule (pc nc : String) (old hp n k : ℕ) :
    irHtriple (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
      (allocProg pc nc)
      ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n)) :=
  (alloc_triple pc nc old hp n k).gc

theorem allocRaw_rule (pc nc : String) (old hp n k : ℕ) :
    irHtriple (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ availRaw hp (n + k) ∗ (nc ↦ᵥ n))
      (allocProg pc nc)
      ((pc ↦ᵥ hp) ∗ rawSpace hp n ∗ availRaw (hp + n) k ∗ (nc ↦ᵥ n)) :=
  (allocRaw_triple pc nc old hp n k).gc

/-! ## 3. The mop and the registered rule -/

/-- The refinement relation for a heap-allocated block: the cell `c`
holds a base pointer, and that base owns the range holding `xs`. This is
the source's split exactly — abstract value the list, concrete value the
pointer, assertion relating them (`eoarray_assn A`). -/
def heapBlockAssn (xs : List Val) (c : String) : Assn := ∃ᵃ p, (c ↦ᵥ p) ∗ (p ↦ₕ xs)

@[simp] theorem heapBlockAssn_def (xs : List Val) (c : String) :
    heapBlockAssn xs c = ∃ᵃ p, (c ↦ᵥ p) ∗ (p ↦ₕ xs) := rfl

/-- **`mop_oarray_new`, at this leaf.** Return the block, pay the
allocator's price. There is **no `assert`**: allocation is unconditional,
which is the property P4.5 exists to reproduce and what
`arrayListReadyRel` / `daReadyRel` were standing in for. -/
noncomputable def mopAlloc (n : ℕ) : NRest (List Val) ECost :=
  NRest.consume (NRest.returnT (List.replicate n 0)) (allocCost n)

theorem mopAlloc_def (n : ℕ) :
    mopAlloc n = NRest.consume (NRest.returnT (List.replicate n 0)) (allocCost n) := rfl

/-- The triple in the shape `hnRefineI_spect` consumes: the price on the
abstract side, the result in the judgment's result slot. -/
theorem alloc_junk_rule (pc nc : String) (hp n k : ℕ) :
    irHtriple (¤(allocCost n) ∗ (junkCell pc ∗ avail hp (n + k) ∗ hnCtxt natAssn n nc))
      (allocProg pc nc)
      ((avail (hp + n) k ∗ hnCtxt natAssn n nc) ∗ heapBlockAssn (List.replicate n 0) pc) := by
  have e₁ : (¤(allocCost n) ∗ (junkCell pc ∗ avail hp (n + k) ∗ hnCtxt natAssn n nc))
      = (junkCell pc ∗ (¤(allocCost n) ∗ avail hp (n + k) ∗ hnCtxt natAssn n nc)) := by
    ac_rfl
  rw [e₁]
  refine irHtriple_junk fun v => ?_
  refine cons_rule (alloc_rule pc nc v hp n k) (fun s hs => ?_) (fun _ s hs => ?_)
  · revert hs
    have e₂ : ((pc ↦ᵥ v) ∗ (¤(allocCost n) ∗ avail hp (n + k) ∗ hnCtxt natAssn n nc))
        = (¤(allocCost n) ∗ (pc ↦ᵥ v) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n)) := by
      simp only [hnCtxt_def, natAssn_def]; ac_rfl
    rw [e₂]
    exact fun h => h
  · revert hs
    have e₃ : ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n))
        = ((avail (hp + n) k ∗ hnCtxt natAssn n nc) ∗
            ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0))) := by
      simp only [hnCtxt_def, natAssn_def]; ac_rfl
    rw [e₃]
    have hblk : ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0))
        ⊢ heapBlockAssn (List.replicate n 0) pc := fun _ hh => ⟨hp, hh⟩
    exact conj_entails_mono (sepConj_mono_right hblk) (entails_refl GC) s

/-- **The registered rule.** `sepref_synth` can consume this: it is an
`hnRefine` over `irSTATE` like every other rule in `Sepref/IrOps.lean`,
in `hnr_mop_aset`'s idiom. The size argument survives as an `hnCtxt`
(the source's `snat_assn⇧k`), the availability resource is threaded
`avail hp (n + k)` → `avail (hp + n) k`, and the block is delivered in
the result slot at the destination cell `pc`. -/
@[sepref_fr_rules]
theorem hnr_mop_alloc (pc nc : String) (hp n k : ℕ) :
    hnRefine (junkCell pc ∗ avail hp (n + k) ∗ hnCtxt natAssn n nc) (allocProg pc nc)
      (avail (hp + n) k ∗ hnCtxt natAssn n nc) pc heapBlockAssn (mopAlloc n) :=
  hnRefineI_spect (alloc_junk_rule pc nc hp n k)

/-! ### The raw flavour, registered

The abstract value of a *raw* allocation is its **size**: the contents
are unspecified, so they are hidden inside the relation rather than
exposed as a value. That is the source's own device again —
`nao_assn A xs p = EXS xsi. narray_assn xsi p ** …` existentially
quantifies the concrete backing — and it is what keeps the abstract
operation deterministic, so the landed `hnRefineI_spect` still applies. -/

/-- The refinement relation for a raw block: the cell `c` holds a base
pointer, and that base owns `n` cells of unspecified contents. -/
def rawBlockAssn (n : ℕ) (c : String) : Assn := ∃ᵃ p, (c ↦ᵥ p) ∗ rawSpace p n

@[simp] theorem rawBlockAssn_def (n : ℕ) (c : String) :
    rawBlockAssn n c = ∃ᵃ p, (c ↦ᵥ p) ∗ rawSpace p n := rfl

/-- Raw allocation: return a block of `n` cells, pay the allocator's
price. No `assert`, exactly as `mopAlloc` has none, and the same cost —
the program is the same program. -/
noncomputable def mopAllocRaw (n : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT n) (allocCost n)

theorem mopAllocRaw_def (n : ℕ) :
    mopAllocRaw n = NRest.consume (NRest.returnT n) (allocCost n) := rfl

theorem allocRaw_junk_rule (pc nc : String) (hp n k : ℕ) :
    irHtriple (¤(allocCost n) ∗ (junkCell pc ∗ availRaw hp (n + k) ∗ hnCtxt natAssn n nc))
      (allocProg pc nc)
      ((availRaw (hp + n) k ∗ hnCtxt natAssn n nc) ∗ rawBlockAssn n pc) := by
  have e₁ : (¤(allocCost n) ∗ (junkCell pc ∗ availRaw hp (n + k) ∗ hnCtxt natAssn n nc))
      = (junkCell pc ∗ (¤(allocCost n) ∗ availRaw hp (n + k) ∗ hnCtxt natAssn n nc)) := by
    ac_rfl
  rw [e₁]
  refine irHtriple_junk fun v => ?_
  refine cons_rule (allocRaw_rule pc nc v hp n k) (fun s hs => ?_) (fun _ s hs => ?_)
  · revert hs
    have e₂ : ((pc ↦ᵥ v) ∗ (¤(allocCost n) ∗ availRaw hp (n + k) ∗ hnCtxt natAssn n nc))
        = (¤(allocCost n) ∗ (pc ↦ᵥ v) ∗ availRaw hp (n + k) ∗ (nc ↦ᵥ n)) := by
      simp only [hnCtxt_def, natAssn_def]; ac_rfl
    rw [e₂]
    exact fun h => h
  · revert hs
    have e₃ : ((pc ↦ᵥ hp) ∗ rawSpace hp n ∗ availRaw (hp + n) k ∗ (nc ↦ᵥ n))
        = ((availRaw (hp + n) k ∗ hnCtxt natAssn n nc) ∗ ((pc ↦ᵥ hp) ∗ rawSpace hp n)) := by
      simp only [hnCtxt_def, natAssn_def]; ac_rfl
    rw [e₃]
    have hblk : ((pc ↦ᵥ hp) ∗ rawSpace hp n) ⊢ rawBlockAssn n pc := fun _ hh => ⟨hp, hh⟩
    exact conj_entails_mono (sepConj_mono_right hblk) (entails_refl GC) s

/-- **The registered raw rule**, in `hnr_mop_alloc`'s idiom. This is the
one that makes reuse O(1): its precondition is `availRaw`, which is
exactly what `free` below returns. -/
@[sepref_fr_rules]
theorem hnr_mop_allocRaw (pc nc : String) (hp n k : ℕ) :
    hnRefine (junkCell pc ∗ availRaw hp (n + k) ∗ hnCtxt natAssn n nc) (allocProg pc nc)
      (availRaw (hp + n) k ∗ hnCtxt natAssn n nc) pc rawBlockAssn (mopAllocRaw n) :=
  hnRefineI_spect (allocRaw_junk_rule pc nc hp n k)

/-! ## 4. `free`, as stack discipline

**What this provides, and what it does not.** `free` is LIFO only: the
block released must be the topmost one. The source frees arbitrary
blocks; we do not, and there is no free list and no fragmentation story
here. What makes it sound is not an arithmetic check but the *shape of
the precondition* — you must own the block `p ↦ₕ xs` **together with the
availability that starts exactly at `p + xs.length`**, so "this block is
on top" is ownership of the adjacent region, in the same way that "there
is room" was ownership in A.2 rather than `hp + n ≤ limit`. A block with
anything still live above it cannot satisfy that precondition
(`free_nontop_false`).

LIFO is a real restriction against the source. It is also exactly the
shape of a recursive per-arena pass, which is what the consumers in this
campaign are; that is a reason it is tolerable, not a reason it is
general.

The block returns to **raw** availability, never to zeroed
(`avail_of_entry` is the only source of zeroness, and it fires once, at
program entry). `free_preserves_heap` is the theorem behind that: `free`
does not write a single heap cell. -/

/-- **`free`'s price**, as a function of the block size — which it does
not mention, exactly as `allocCost` does not. -/
def freeCost (_n : ℕ) : ECost := irUnit Currency.sub

theorem freeCost_const (n n' : ℕ) : freeCost n = freeCost n' := rfl

theorem freeCost_eq (n : ℕ) : freeCost n = irUnit Currency.sub := rfl

/-- **`free`**, as one existing constructor: `hp := hp - nc`. It is one
instruction where `alloc` is two, and the asymmetry is real rather than
an omission: `alloc` must both *read* the old bump pointer (that is its
result) and advance it, while `free` returns nothing and so only has to
move the pointer back. No new `Ir.Com` constructor either. -/
def freeProg (nc : String) : Com := Com.binop Imp.Bop.sub hpName hpName nc

/-- **`free`'s exact triple.** Give up the topmost block and the
availability above it; get back availability covering both, raw. There is
no side condition at all: `xs.length` *is* the block's size and the
adjacency is the shape of the precondition. -/
theorem free_triple (nc : String) (p k : ℕ) (xs : List Val) :
    irTriple (¤(freeCost xs.length) ∗ (p ↦ₕ xs) ∗ availRaw (p + xs.length) k ∗
        (nc ↦ᵥ xs.length))
      (freeProg nc)
      (availRaw p (xs.length + k) ∗ (nc ↦ᵥ xs.length)) := by
  have hsub := frame_rule (wp := wp) (α := irα) ((p ↦ₕ xs) ∗ rawSpace (p + xs.length) k)
    (binop_self_triple Imp.Bop.sub hpName nc (p + xs.length) xs.length)
  rw [Imp.Bop.apply_sub, binopCurrency_sub, Nat.add_sub_cancel] at hsub
  refine cons_rule hsub (fun s hs => ?_) (fun _ s hs => ?_)
  · revert hs
    have ePre : (¤(freeCost xs.length) ∗ (p ↦ₕ xs) ∗ availRaw (p + xs.length) k ∗
        (nc ↦ᵥ xs.length))
        = ((¤¤Currency.sub 1 ∗ (hpName ↦ᵥ (p + xs.length)) ∗ (nc ↦ᵥ xs.length)) ∗
          ((p ↦ₕ xs) ∗ rawSpace (p + xs.length) k)) := by
      rw [availRaw, freeCost_eq, ← costCredits_one]
      ac_rfl
    rw [ePre]
    exact fun h => h
  · revert hs
    have ePost : ((((hpName ↦ᵥ p) ∗ (nc ↦ᵥ xs.length))) ∗
        ((p ↦ₕ xs) ∗ rawSpace (p + xs.length) k))
        = (((hpName ↦ᵥ p) ∗ ((p ↦ₕ xs) ∗ rawSpace (p + xs.length) k)) ∗
          (nc ↦ᵥ xs.length)) := by
      ac_rfl
    have eGoal : (availRaw p (xs.length + k) ∗ (nc ↦ᵥ xs.length))
        = (((hpName ↦ᵥ p) ∗ (rawSpace p xs.length ∗ rawSpace (p + xs.length) k)) ∗
          (nc ↦ᵥ xs.length)) := by
      rw [availRaw, rawSpace_split]
    have hent : (((hpName ↦ᵥ p) ∗ ((p ↦ₕ xs) ∗ rawSpace (p + xs.length) k)) ∗
        (nc ↦ᵥ xs.length))
        ⊢ (((hpName ↦ᵥ p) ∗ (rawSpace p xs.length ∗ rawSpace (p + xs.length) k)) ∗
          (nc ↦ᵥ xs.length)) :=
      sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (ptoH_entails_rawSpace p xs)))
    rw [ePost, eGoal]
    exact hent s

/-- The garbage-collecting form. -/
theorem free_rule (nc : String) (p k : ℕ) (xs : List Val) :
    irHtriple (¤(freeCost xs.length) ∗ (p ↦ₕ xs) ∗ availRaw (p + xs.length) k ∗
        (nc ↦ᵥ xs.length))
      (freeProg nc)
      (availRaw p (xs.length + k) ∗ (nc ↦ᵥ xs.length)) :=
  (free_triple nc p k xs).gc

/-- `free` returns nothing: its whole effect is on the context. -/
def noResultAssn : Unit → Unit → Assn := fun _ _ => (□ : Assn)

/-- Giving up a block, at the abstract level. The block's value `xs` is
an *argument*, so the abstract program must hold it and hand it over —
which is the linearity that makes a use-after-free underivable. -/
noncomputable def mopFree (xs : List Val) : NRest Unit ECost :=
  NRest.consume (NRest.returnT ()) (freeCost xs.length)

theorem mopFree_def (xs : List Val) :
    mopFree xs = NRest.consume (NRest.returnT ()) (freeCost xs.length) := rfl

theorem free_mop_rule (nc : String) (p k : ℕ) (xs : List Val) :
    irHtriple (¤(freeCost xs.length) ∗
        ((p ↦ₕ xs) ∗ availRaw (p + xs.length) k ∗ hnCtxt natAssn xs.length nc))
      (freeProg nc)
      ((availRaw p (xs.length + k) ∗ hnCtxt natAssn xs.length nc) ∗ noResultAssn () ()) := by
  refine cons_rule (free_rule nc p k xs) (fun s hs => ?_) (fun _ s hs => ?_)
  · revert hs
    have e : (¤(freeCost xs.length) ∗
        ((p ↦ₕ xs) ∗ availRaw (p + xs.length) k ∗ hnCtxt natAssn xs.length nc))
        = (¤(freeCost xs.length) ∗ (p ↦ₕ xs) ∗ availRaw (p + xs.length) k ∗
          (nc ↦ᵥ xs.length)) := by
      simp only [hnCtxt_def, natAssn_def]
    rw [e]
    exact fun h => h
  · revert hs
    have e : (availRaw p (xs.length + k) ∗ (nc ↦ᵥ xs.length))
        = ((availRaw p (xs.length + k) ∗ hnCtxt natAssn xs.length nc) ∗ noResultAssn () ()) := by
      simp [noResultAssn]
    rw [e]
    exact fun h => h

/-- **The registered `free` rule.** The block's ownership is in `Γ` and
does *not* reappear in `Γ'` — it has become availability — so a second
use of the same block after this rule is not derivable. That is
`hnr_mop_aset`'s linearity showcase, at deallocation. -/
@[sepref_fr_rules]
theorem hnr_mop_free (nc : String) (p k : ℕ) (xs : List Val) :
    hnRefine ((p ↦ₕ xs) ∗ availRaw (p + xs.length) k ∗ hnCtxt natAssn xs.length nc)
      (freeProg nc)
      (availRaw p (xs.length + k) ∗ hnCtxt natAssn xs.length nc) () noResultAssn
      (mopFree xs) :=
  hnRefineI_spect (free_mop_rule nc p k xs)

/-! ### Round trips

`alloc` then `free` returns the space, raw; `free` then `allocRaw` is
reuse, at O(1). Both are composed triples, so the costs add and neither
mentions the block size. -/

/-- **Alloc-then-free round-trips.** The availability comes back exactly
as it went out, minus the knowledge that it reads zero. -/
theorem alloc_free_roundtrip (pc nc : String) (old hp n k : ℕ) :
    irTriple (¤(allocCost n + freeCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
      ((allocProg pc nc).seq (freeProg nc))
      ((pc ↦ᵥ hp) ∗ availRaw hp (n + k) ∗ (nc ↦ᵥ n)) := by
  have hfree := frame_rule (wp := wp) (α := irα) (pc ↦ᵥ hp)
    (free_triple nc hp k (List.replicate n 0))
  rw [List.length_replicate] at hfree
  have h1 : irTriple (¤(allocCost n + freeCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
      (allocProg pc nc)
      (¤(freeCost n) ∗ (pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗
        avail (hp + n) k ∗ (nc ↦ᵥ n)) := by
    have h := frame_rule (wp := wp) (α := irα) (¤(freeCost n)) (alloc_triple pc nc old hp n k)
    have ePre : (¤(allocCost n + freeCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
        = ((¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n)) ∗ ¤(freeCost n)) := by
      rw [credits_add]
      ac_rfl
    have ePost : (¤(freeCost n) ∗ (pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗
        avail (hp + n) k ∗ (nc ↦ᵥ n))
        = (((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n)) ∗
          ¤(freeCost n)) := by
      ac_rfl
    rw [ePre, ePost]
    exact h
  have h2 : irTriple (¤(freeCost n) ∗ (pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗
      avail (hp + n) k ∗ (nc ↦ᵥ n))
      (freeProg nc) ((pc ↦ᵥ hp) ∗ availRaw hp (n + k) ∗ (nc ↦ᵥ n)) := by
    refine cons_rule hfree (fun s hs => ?_) (fun _ s hs => ?_)
    · revert hs
      have e : (¤(freeCost n) ∗ (pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗
          avail (hp + n) k ∗ (nc ↦ᵥ n))
          = ((¤(freeCost n) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n)) ∗
            (pc ↦ᵥ hp)) := by
        ac_rfl
      have hent : ((¤(freeCost n) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗
          (nc ↦ᵥ n)) ∗ (pc ↦ᵥ hp))
          ⊢ ((¤(freeCost n) ∗ (hp ↦ₕ List.replicate n 0) ∗ availRaw (hp + n) k ∗
            (nc ↦ᵥ n)) ∗ (pc ↦ᵥ hp)) :=
        sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (avail_entails_availRaw (hp + n) k))))
      rw [e]
      exact hent s
    · revert hs
      have e : ((availRaw hp (n + k) ∗ (nc ↦ᵥ n)) ∗ (pc ↦ᵥ hp))
          = ((pc ↦ᵥ hp) ∗ availRaw hp (n + k) ∗ (nc ↦ᵥ n)) := by ac_rfl
      rw [e]
      exact fun h => h
  rw [show (allocProg pc nc).seq (freeProg nc) = (allocProg pc nc).seq (freeProg nc) from rfl]
  exact seq_triple h1 h2

/-- **Reuse is O(1).** Free a block, then allocate out of the space it
returned: two constant costs, and the second allocation hands back the
very cells the first block occupied, at the same base. Under E23's old
reading this would have been O(n), because the block would have had to be
re-zeroed before it could be handed out again. -/
theorem free_allocRaw_reuse (pc nc : String) (old p k : ℕ) (xs : List Val) :
    irTriple (¤(freeCost xs.length + allocCost xs.length) ∗ (pc ↦ᵥ old) ∗ (p ↦ₕ xs) ∗
        availRaw (p + xs.length) k ∗ (nc ↦ᵥ xs.length))
      ((freeProg nc).seq (allocProg pc nc))
      ((pc ↦ᵥ p) ∗ rawSpace p xs.length ∗ availRaw (p + xs.length) k ∗
        (nc ↦ᵥ xs.length)) := by
  have h1 : irTriple (¤(freeCost xs.length + allocCost xs.length) ∗ (pc ↦ᵥ old) ∗
      (p ↦ₕ xs) ∗ availRaw (p + xs.length) k ∗ (nc ↦ᵥ xs.length))
      (freeProg nc)
      (¤(allocCost xs.length) ∗ (pc ↦ᵥ old) ∗ availRaw p (xs.length + k) ∗
        (nc ↦ᵥ xs.length)) := by
    have h := frame_rule (wp := wp) (α := irα) ((pc ↦ᵥ old) ∗ ¤(allocCost xs.length))
      (free_triple nc p k xs)
    have ePre : (¤(freeCost xs.length + allocCost xs.length) ∗ (pc ↦ᵥ old) ∗ (p ↦ₕ xs) ∗
        availRaw (p + xs.length) k ∗ (nc ↦ᵥ xs.length))
        = ((¤(freeCost xs.length) ∗ (p ↦ₕ xs) ∗ availRaw (p + xs.length) k ∗
          (nc ↦ᵥ xs.length)) ∗ ((pc ↦ᵥ old) ∗ ¤(allocCost xs.length))) := by
      rw [credits_add]
      ac_rfl
    have ePost : (¤(allocCost xs.length) ∗ (pc ↦ᵥ old) ∗ availRaw p (xs.length + k) ∗
        (nc ↦ᵥ xs.length))
        = ((availRaw p (xs.length + k) ∗ (nc ↦ᵥ xs.length)) ∗
          ((pc ↦ᵥ old) ∗ ¤(allocCost xs.length))) := by
      ac_rfl
    rw [ePre, ePost]
    exact h
  have h2 : irTriple (¤(allocCost xs.length) ∗ (pc ↦ᵥ old) ∗ availRaw p (xs.length + k) ∗
      (nc ↦ᵥ xs.length))
      (allocProg pc nc)
      ((pc ↦ᵥ p) ∗ rawSpace p xs.length ∗ availRaw (p + xs.length) k ∗
        (nc ↦ᵥ xs.length)) :=
    allocRaw_triple pc nc old p xs.length k
  exact seq_triple h1 h2

/-! ### What is *not* available, as theorems

`availRaw_not_entails_avail` above already pins that raw memory is not
zeroed memory. Two more, both about `free`. -/

/-- **`free` writes nothing.** It moves the bump pointer and touches no
heap cell, so the freed block still reads whatever it held. This is the
theorem behind "freed memory returns raw, never zeroed": a zeroed
postcondition would have to be false unless the block was already
zero. -/
theorem free_preserves_heap (nc : String) (s : State) (s' : State) (κ : Cost)
    (h : BigStep (freeProg nc) s s' κ) : hcells s' = hcells s := by
  rw [freeProg, bigStep_binop_iff] at h
  obtain ⟨-, m, n, -, -, rfl, -⟩ := h
  exact hcells_setVar s hpName (Imp.Bop.sub.apply m n)

/-- Availability of size `k` really is ownership of those `k` cells, so a
live block inside it cannot coexist with it. -/
theorem rawSpace_sepConj_overlap {q m j : ℕ} {zs : List Val} (hj : j < m)
    (hz : 0 < zs.length) : (rawSpace q m ∗ ((q + j) ↦ₕ zs)) = (sepFalse : Assn) := by
  funext h
  refine propext ⟨?_, fun h' => h'.elim⟩
  rintro ⟨x, y, hd, hxy, hx, hy⟩
  obtain ⟨ws, hwl, hws⟩ := rawSpace_apply.1 hx
  have : ((q ↦ₕ ws) ∗ ((q + j) ↦ₕ zs)) h := ⟨x, y, hd, hxy, hws, hy⟩
  rw [ptoH_sepConj_overlap (Nat.le_add_right q j) (by omega) hz] at this
  exact this.elim

/-- **A block that is not the topmost one is not freeable.** `free`'s
precondition owns availability of size `k` starting at `p + n`; if some
other block is still live `j < k` cells above the bump pointer, it lies
*inside* that availability, and the two cannot be owned at once. So the
precondition is unsatisfiable exactly when the block is not on top —
enforced by ownership, not by an arithmetic check. -/
theorem free_nontop_false {p n k j : ℕ} {xs zs : List Val} (hj : j < k)
    (hz : 0 < zs.length) :
    ((p ↦ₕ xs) ∗ availRaw (p + n) k ∗ ((p + n + j) ↦ₕ zs)) = (sepFalse : Assn) := by
  have e : ((p ↦ₕ xs) ∗ availRaw (p + n) k ∗ ((p + n + j) ↦ₕ zs))
      = ((rawSpace (p + n) k ∗ ((p + n + j) ↦ₕ zs)) ∗
        ((p ↦ₕ xs) ∗ (hpName ↦ᵥ (p + n)))) := by
    rw [availRaw]
    ac_rfl
  rw [e, rawSpace_sepConj_overlap hj hz]
  funext h
  refine propext ⟨?_, fun h' => h'.elim⟩
  rintro ⟨x, y, -, -, hx, -⟩
  exact hx.elim

/-! ## 5. Negative controls

Ledger E24's controls. This is authored with no source counterpart in
our shape, so the falsification law's clause 2 applies: the cost claim
and the no-reuse claim are both checked by computation, and both were
verified to fail when flipped. -/

namespace AllocGate

open Plausible Ir.HeapGate

/-- The allocator's price, currency by currency. -/
def costOf (n : ℕ) : List (String × ℕ∞) := Ir.Gate.creditVector (allocCost n)

-- **The `n`-independence control.** A linear term in the block size
-- would break these; they are what stands between E24's O(1) claim and
-- an unnoticed `cost ''malloc'' n`.
#guard costOf 0 == costOf 1000
#guard costOf 1 == costOf 7
#guard costOf 3 == [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 1), ("ir.aget", 0),
  ("ir.aset", 0), ("ir.ite", 0), ("ir.while", 0), ("ir.add", 1), ("ir.sub", 0),
  ("ir.mul", 0), ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0),
  ("ir.shiftl", 0), ("ir.shiftr", 0)]

-- Sampled: the price is the same at every size.
#test ∀ m n : ℕ, costOf m == costOf n

-- The program really is two instructions, and neither is a loop.
#guard allocProg "p" "n" == (Com.copy "p" hpName).seq (Com.binop .add hpName hpName "n")

/-- `free`'s price, currency by currency. -/
def freeCostOf (n : ℕ) : List (String × ℕ∞) := Ir.Gate.creditVector (freeCost n)

-- **`free`'s `n`-independence control**, the same shape as the
-- allocator's: a linear term in the block size would break these.
#guard freeCostOf 0 == freeCostOf 1000
#guard freeCostOf 3 == [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 0),
  ("ir.aset", 0), ("ir.ite", 0), ("ir.while", 0), ("ir.add", 0), ("ir.sub", 1),
  ("ir.mul", 0), ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0),
  ("ir.shiftl", 0), ("ir.shiftr", 0)]
#test ∀ m n : ℕ, freeCostOf m == freeCostOf n

-- `free` is one instruction, `alloc` two — and `free` pays `ir.sub`, not
-- a second `ir.copy`, so the two prices are genuinely different vectors.
#guard freeProg "n" == Com.binop .sub hpName hpName "n"
#guard costOf 3 != freeCostOf 3

-- **Raw is not zeroed.** The two ranges differ at the very first cell,
-- which is why `availRaw ⊢ avail` has no proof and must not.
#guard hrange 0 [7] 0 != hrange 0 (List.replicate 1 0) 0
#guard hrange 0 (List.replicate 1 0) 0 == Tsa.triv 0

-- **The no-reuse control.** Successive allocations of 3 then 2 cells
-- hand out disjoint ranges…
#guard disjOnB idxs (hrange 0 (List.replicate 3 0)) (hrange 3 (List.replicate 2 0))

-- …while handing the *same* base out twice — the reuse bug — does not
-- compose. Were this `disjOnB`, two live blocks could alias.
#guard !disjOnB idxs (hrange 0 (List.replicate 3 0)) (hrange 0 (List.replicate 2 0))
#guard !disjOnB idxs (hrange 3 (List.replicate 2 0)) (hrange 2 (List.replicate 2 0))

-- Sampled: whatever the two sizes, the second allocation's range is
-- disjoint from the first's.
#test ∀ m n : ℕ, disjOnB idxs
  (hrange 0 (List.replicate (m % 4) 0)) (hrange (m % 4) (List.replicate (n % 4) 0))

-- The availability resource really does shrink: after handing out `n`,
-- what is left starts at `hp + n` and owns nothing below it.
#guard idxs.all fun i =>
  (i < 3) == (hrange 3 (List.replicate 5 0) i == 0 && hrange 0 (List.replicate 3 0) i != 0)

/-- **Non-vacuity**: `mopAlloc` never fails, which is the unconditionality
the phase is after — an `assert` would make this false at some `n`. -/
theorem mopAlloc_nofail (n : ℕ) : (mopAlloc n).nofailT := by
  rw [mopAlloc_def]
  exact nofailT_consume_iff.2 (NRest.nofailT_returnT _)

/-- The registered rule is instantiable at concrete arguments. -/
example : hnRefine (junkCell "p" ∗ avail 0 (3 + 5) ∗ hnCtxt natAssn 3 "n")
    (allocProg "p" "n") (avail 3 5 ∗ hnCtxt natAssn 3 "n") "p" heapBlockAssn (mopAlloc 3) :=
  hnr_mop_alloc "p" "n" 0 3 5

/-! ### `sepref_synth` really does consume the rule

This is the acceptance criterion the leaf turns on, and it is *checked*
rather than assumed: the synthesizer is handed a goal whose abstract
program is `mopAlloc`, with the concrete program a hole, and it must
find `hnr_mop_alloc` in `sepref_fr_rules` and emit the two-instruction
allocator. -/

sepref_synth allocSynth (n : ℕ) :
  hnRefine (junkCell "p" ∗ avail 0 (n + 5) ∗ hnCtxt natAssn n "n")
    _ _ "p" heapBlockAssn (mopAlloc n)

-- The synthesized program, pinned: exactly `allocProg`.
#guard allocSynth_impl = allocProg "p" "n"

-- The same for **raw** allocation: `hnr_mop_allocRaw` is reachable, and
-- the emitted program is the same two instructions at the same price.
sepref_synth allocRawSynth (n : ℕ) :
  hnRefine (junkCell "p" ∗ availRaw 0 (n + 5) ∗ hnCtxt natAssn n "n")
    _ _ "p" rawBlockAssn (mopAllocRaw n)

#guard allocRawSynth_impl = allocProg "p" "n"

-- …and for `free`.
sepref_synth freeSynth (xs : List Val) :
  hnRefine ((3 ↦ₕ xs) ∗ availRaw (3 + xs.length) 5 ∗ hnCtxt natAssn xs.length "n")
    _ _ () noResultAssn (mopFree xs)

#guard freeSynth_impl = freeProg "n"

end AllocGate

end Lax13Proofs.Refine.Sepref
