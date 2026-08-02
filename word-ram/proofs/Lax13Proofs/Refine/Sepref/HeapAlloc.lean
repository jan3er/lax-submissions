import Lax13Proofs.Refine.Sepref.IrOps
import Lax13Proofs.Refine.Sepref.Definition
import Lax13Proofs.Refine.Ir.Heap

/-!
The costed bump allocator, and its registered refinement rule.

Leaf **P4.5.A.2** of `plans/word-ram/tower-expansion/p4.5-design.md`
(decision **D-A2**, ledger **E24**), on top of A.1's range ownership.

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
private def allocMid (pc nc : String) (hp n k : ℕ) : Assn :=
  ¤¤Currency.add 1 ∗ (pc ↦ᵥ hp) ∗ (hpName ↦ᵥ hp) ∗ (nc ↦ᵥ n) ∗
    (hp ↦ₕ List.replicate (n + k) 0)

/-- **The allocator's exact triple.** Pay `allocCost n` — two units, no
`n` — own the bump pointer and `n + k` cells of unallocated space, and
get back the base pointer in `pc`, the block `[hp, hp + n)` holding
zeros, and the availability resource at the advanced pointer. The size
cell survives, as the source's `snat_assn⇧k` keeps it. -/
theorem alloc_triple (pc nc : String) (old hp n k : ℕ) :
    irTriple (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
      (allocProg pc nc)
      ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n)) := by
  have h1 : irTriple (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
      (Com.copy pc hpName) (allocMid pc nc hp n k) := by
    have hcopy := frame_rule (wp := wp) (α := irα)
      (¤¤Currency.add 1 ∗ (nc ↦ᵥ n) ∗ (hp ↦ₕ List.replicate (n + k) 0))
      (copy_triple pc hpName old hp)
    have ePre : (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
        = ((¤¤Currency.copy 1 ∗ (pc ↦ᵥ old) ∗ (hpName ↦ᵥ hp)) ∗
          (¤¤Currency.add 1 ∗ (nc ↦ᵥ n) ∗ (hp ↦ₕ List.replicate (n + k) 0))) := by
      rw [avail, allocCost_eq, credits_add]
      simp only [costCredits_one]
      ac_rfl
    have ePost : allocMid pc nc hp n k
        = (((pc ↦ᵥ hp) ∗ (hpName ↦ᵥ hp)) ∗
          (¤¤Currency.add 1 ∗ (nc ↦ᵥ n) ∗ (hp ↦ₕ List.replicate (n + k) 0))) := by
      rw [allocMid]
      ac_rfl
    rw [ePre, ePost]
    exact hcopy
  have h2 : irTriple (allocMid pc nc hp n k) (Com.binop Imp.Bop.add hpName hpName nc)
      ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n)) := by
    have hadd := frame_rule (wp := wp) (α := irα)
      ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate (n + k) 0))
      (binop_self_triple Imp.Bop.add hpName nc hp n)
    rw [Imp.Bop.apply_add, binopCurrency_add] at hadd
    have ePre : allocMid pc nc hp n k
        = ((¤¤Currency.add 1 ∗ (hpName ↦ᵥ hp) ∗ (nc ↦ᵥ n)) ∗
          ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate (n + k) 0))) := by
      rw [allocMid]
      ac_rfl
    have ePost : ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n))
        = ((((hpName ↦ᵥ (hp + n)) ∗ (nc ↦ᵥ n))) ∗
          ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate (n + k) 0))) := by
      rw [avail, availSpace_split]
      ac_rfl
    rw [ePre, ePost]
    exact hadd
  rw [allocProg]
  exact seq_triple h1 h2

/-- The garbage-collecting form. -/
theorem alloc_rule (pc nc : String) (old hp n k : ℕ) :
    irHtriple (¤(allocCost n) ∗ (pc ↦ᵥ old) ∗ avail hp (n + k) ∗ (nc ↦ᵥ n))
      (allocProg pc nc)
      ((pc ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate n 0) ∗ avail (hp + n) k ∗ (nc ↦ᵥ n)) :=
  (alloc_triple pc nc old hp n k).gc

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

/-! ## 4. Negative controls

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

end AllocGate

end Lax13Proofs.Refine.Sepref
