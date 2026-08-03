import Lax13Proofs.Refine.Iicf.Impl.ArrayListAppendSynth

/-!
# `butlast` then `append`, as one command

Leaf **P4.5.A.9**, satellite of `ArrayListHeap.lean` and
`ArrayListAppendSynth.lean` (ledger **E39**).

`ArrayListAppendSynth.lean` landed append as one `Com` and one `hnRefine`, at
the representation invariant

```
def arlTight (s : ArrayList) : Prop := s.capacity = s.buffer.length
```

sitting in exactly the position `s.Wf` occupies in the exec-rule convention.
It had one violator, and the violator was the array list's own `butlast`: the
landed `arlButlastExecState` applies the source's conditional **logical**
capacity shrink, so the tight state `⟨replicate 100 0, 17, 100⟩` butlasts to
capacity `32` in a buffer of length `100`, `arlTight` fails, and
`arlHAppend_exec_hnr` no longer applies.  **A program that did `butlast` then
`append` could not be synthesized at all.**  Nothing about the abstract
guarantee was ever weak — `arlAppendOp_refines` and `arlButlastOp_refines` are
unconditional and untouched — the gap was in the executable layer.

`ArrayListHeap.lean` closed it by dropping the logical shrink **in the heap
representation only**: `arlHButlastExecState s = ⟨s.buffer, s.length - 1,
s.capacity⟩`.  Its header carries the argument (the shrink is metadata-only,
neither command performs a heap operation, so occupancy is identical and the
cost is a space constant).  This file is the acceptance test for that decision.

## What is proved here

* **`arlTight` is preserved** by the heap `butlast` — `arlHButlast_tight`, and
  it is a one-liner because the capacity is carried through untouched.  The
  compiled contrast with the named-array `butlast`, which does *not* preserve
  it at E39's own counterexample, is § 6.
* **`butlast` then `append` is one `Com`** — `arlHButlastAppendCom`, the
  composition of `arlHButlastCom` and `arlHAppendCom` — and **one `hnRefine`**,
  `arlHButlastAppend_exec_hnr`, composed by `hnr_seq` from the two landed rules
  and used *by name*, in the idiom `ArrayListAppendSynth.lean` uses for
  `arlHAppendCom` itself.
* **at an exact, closed-form price.**  `arlTight` is what makes the append's
  dispatch apply at the butlasted state; `arlHButlast_lt` is what fixes which
  branch it takes.
* **the value read back is `arlAppendTotal (arlHButlastExecState s) x`**, and
  refines `listButlast xs ++ [x]` through `arrayListRel` —
  `arlHButlastAppendExecSpec_refines`.

## `arlTight` is exactly the hypothesis that makes this go through

That is the whole point of the leaf, so it is worth being precise about where
it enters.  `arlHAppend_exec_hnr` carries `arlTight s` because
`arlAppendTotal` has **three** branches and a heap-native dispatch has two: the
middle branch logically doubles the capacity inside a physically larger buffer,
which can only happen to a caller owning more storage than its capacity
advertises, and a heap block owns exactly what was allocated for it.  So the
composed rule needs `arlTight (arlHButlastExecState s)`, and it gets it from
`arlTight s` for free — `arlHButlast_tight` is `id` up to unfolding — precisely
because the shrink is gone.  With the shrink, that step is **false**, and § 6
compiles the failure: the same composition with the landed `butlast` spliced in
runs to completion and leaves a capacity of `16` for a block of `33`, a state
at which `arlPushGrown` and `arlAppendTotal` genuinely disagree.

`butlast` itself acquired no new caller obligation in the repair:
`arlHButlast_exec_hnr` has no hypotheses at all.  `arlTight` is carried by the
rules, never demanded of `butlast`'s caller.

## The composed command, and its price

```
len := len - one ; skip ; skip          -- butlast: the decrement, and the pack
nc := cap * two                         -- append: the doubled capacity
if len < cap then                       -- …and the branch, which is always
  adr := bc + len ; heap[adr] := xc     --    this one (`arlHButlast_lt`)
  len := len + one ; dc := bc
  skip ; skip
else … allocate, copy, push …           -- present, never executed
```

| `ite` | `mul` | `while` | `copy` | `const` | `skip` | `aset` | `aget` | `add` | (`sub`) |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 0 | 1 | 0 | 4 | 1 | 0 | 2 | 1 |

`ir.sub` is not one of the nine currencies `IrVecN` carries, so
`arlHButlastAppendCost` is the vector *plus* that `ir.sub`, and § 6 checks the
`ir.sub` against the run's full sixteen-currency vector.  Ledger **F11**, sixth
appearance: the vector is written from the emitted command, `_toE`-proved to be
what the judgment pays (`arlHButlastAppendRaw_eq`), **and** `#guard`ed against
what the emitted program charges on a concrete heap.  It matched with nothing
adjusted.

The price is free of `s.length` and `s.capacity` — no loop, no allocation, and
`while = const = 0` says so.  That is not an accident of the gate state:
`arlHButlast_lt` proves `s.length - 1 < s.capacity` at every `Wf` state, so the
growth branch of the embedded dispatch is **unreachable after a `butlast`**.
The bump pointer is compiled untouched in § 6.

## Registration (ledger E29)

`arlHButlastAppendCom` is **not** registered, for the reason `arlHAppendCom` is
not: it contains an allocation in a branch (`mentions hpName` is `true` of it,
compiled in § 6), so a database entry would let the frame inferencer drop an
allocation into a loop body.  It is composed once and used by name.  No rule is
added to `sepref_fr_rules` by this file at all.

## What is not touched

`ArrayList.lean` keeps its shrink and its seven registered rules — the named
array's buffer is not sized by an allocator, so `arlTight` is not its invariant
and the middle branch of `arlAppendTotal` is genuinely available to it.  The
two representations therefore reach *different concrete states* for the same
abstract list, and agree exactly where it counts: both refine
`op_list_butlast` through the same `arrayListRel`.  `ArrayListCash.lean` is
untouched and unaffected — `dynRate` domination is stated about
`arlHAppendMachineN`, this file lowers a price and adds no append cost, and
`arlHButlastAppend_leaves_the_cost_story_unchanged` re-checks its compiled
guard as a term here.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

/-! ## 1. The heap `butlast` preserves what the append dispatch needs -/

/-- **The repair, in one line.**  The heap `butlast` carries the capacity
through, and the buffer is untouched, so tightness cannot break. -/
theorem arlHButlast_tight {s : ArrayList} (ht : arlTight s) :
    arlTight (arlHButlastExecState s) := ht

theorem arlHButlast_wf {s : ArrayList} (hwf : s.Wf) : (arlHButlastExecState s).Wf := by
  obtain ⟨hpos, hlc, hcb⟩ := hwf
  exact ⟨hpos, by show s.length - 1 ≤ s.capacity; omega, hcb⟩

/-- **After a `butlast` the append is always in place.**  `Wf` gives
`0 < capacity` and `length ≤ capacity`, and the decrement is saturating, so the
decremented length is strictly below the capacity whatever the input — the
growth branch of the embedded dispatch is unreachable, and the composed price
is therefore free of `s.length`. -/
theorem arlHButlast_lt {s : ArrayList} (hwf : s.Wf) :
    (arlHButlastExecState s).length < (arlHButlastExecState s).capacity := by
  obtain ⟨hpos, hlc, -⟩ := hwf
  show s.length - 1 < s.capacity
  omega

/-! ## 2. The composed command and the composed abstract program -/

/-- **`butlast` then `append`, as one command.**  Nothing is inlined or
rewritten: this is `ArrayListHeap.lean`'s emitted `butlast` followed by
`ArrayListAppendSynth.lean`'s emitted `append`. -/
def arlHButlastAppendCom : Com :=
  (arlHButlastCom "bc" "len" "cap" "one").seq arlHAppendCom

/-- The abstract side: the `butlast` spec's value fed to the append spec, which
is what `hnr_seq` produces. -/
noncomputable def arlHButlastAppendRaw (s : ArrayList) (x : ℕ) :
    NRest (List Val × (ℕ × ℕ)) ECost :=
  NRest.bindT (arlHButlastExecSpec s.buffer s.length s.capacity) fun r =>
    arlHAppendExecSpec ⟨r.1, r.2.1, r.2.2⟩ x

/-! ## 3. The composed rule -/

/-- The cells the append needs and the `butlast` never touches. -/
private def baFrame (hp k x c : ℕ) : Assn :=
  hnCtxt natAssn x "xc" ∗ hnCtxt natAssn 2 "two" ∗
    junkCell "adr" ∗ junkCell "dc" ∗ junkCell "pc" ∗ junkCell "nc" ∗
    junkCell "t" ∗ junkCell "si" ∗ junkCell "se" ∗ junkCell "di" ∗
    avail hp (2 * c + k)

/-- The composition's precondition: the `butlast` rule's three representation
cells and its `one`, plus the append's own scratch and availability. -/
def arlHButlastAppendPre (p hp k x : ℕ) (s : ArrayList) : Assn :=
  (hnCtxt (heapBlockAssnAt p) s.buffer "bc" ∗ hnCtxt natAssn s.length "len" ∗
    hnCtxt natAssn s.capacity "cap" ∗ hnCtxt natAssn 1 "one") ∗ baFrame hp k x s.capacity

private theorem ba_pre_append (p hp k x : ℕ) (s : ArrayList) :
    hnCtxt (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn)
        (s.buffer, (s.length - 1, s.capacity)) ("bc", ("len", "cap")) ∗
      (hnCtxt natAssn 1 "one" ∗ baFrame hp k x s.capacity) ⊢
    arlHAppendPre p hp k x (arlHButlastExecState s) := by
  have h : hnCtxt (heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn)
        (s.buffer, (s.length - 1, s.capacity)) ("bc", ("len", "cap")) ∗
      (hnCtxt natAssn 1 "one" ∗ baFrame hp k x s.capacity)
      = arlHAppendPre p hp k x (arlHButlastExecState s) := by
    simp only [arlHAppendPre, baFrame, arlHButlastExecState, hnCtxt_def, prodAssn]
    ac_rfl
  exact fun st hs => h ▸ hs

/-- **The composition, by `hnr_seq`.**  Deliberately *not* registered (ledger
E29): the embedded dispatch allocates in one branch. -/
theorem arlHButlastAppend_dispatch (p hp k x : ℕ) (s : ArrayList)
    (hwf : s.Wf) (ht : arlTight s) :
    hnRefine (arlHButlastAppendPre p hp k x s) arlHButlastAppendCom
      (arlHAppendPost k x s.capacity) ("dc", ("len", "cap"))
      (heapBlockAssn ×ₐ natAssn ×ₐ natAssn) (arlHButlastAppendRaw s x) := by
  rw [arlHButlastAppendCom, arlHButlastAppendRaw]
  refine hnr_seq (Γ₁ := hnCtxt natAssn 1 "one" ∗ baFrame hp k x s.capacity)
    (x := ("bc", ("len", "cap")))
    (Rh := heapBlockAssnAt p ×ₐ natAssn ×ₐ natAssn) ?_ ?_
  · exact hnRefine_frame' (F := baFrame hp k x s.capacity)
      (arlHButlast_exec_hnr "bc" "len" "cap" "one" p s.buffer s.length s.capacity)
  · intro a ha
    have hrest : arlHButlastExecSpec s.buffer s.length s.capacity
        = NRest.rest (NRest.single (s.buffer, (s.length - 1, s.capacity))
            ((arlHButlastCost : ECost) : WithBot ECost)) := by
      rw [arlHButlastExecSpec_def, NRest.consume_returnT]
    have hval : a = (s.buffer, (s.length - 1, s.capacity)) := by
      rw [hrest, returnT_le_rest_iff] at ha
      by_contra hne
      rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at ha
      exact WithBot.coe_ne_bot ha
    subst hval
    exact hnRefine_cons_pre
      (arlHAppend_exec_hnr p hp k x (arlHButlastExecState s)
        (arlHButlast_wf hwf) (arlHButlast_tight ht))
      (ba_pre_append p hp k x s)

/-! ## 4. The price, predicted from the emitted command -/

/-- The composed price: the `butlast`'s two packing `skip`s on top of the
in-place append's own vector.  Free of `s.length` and `s.capacity`. -/
def arlHButlastAppendN : IrVecN := ⟨1, 1, 0, 1, 0, 4, 1, 0, 2⟩

theorem arlHButlastAppendN_split :
    arlHButlastAppendN = arlHButlastN + (⟨1, 1, 0, 1, 0, 2, 1, 0, 2⟩ : IrVecN) := by
  decide

noncomputable def arlHButlastAppendCost : ECost :=
  arlHButlastAppendN.toE + irUnit Currency.sub

theorem arlHButlastAppendCost_split :
    arlHButlastAppendCost =
      (⟨1, 1, 0, 1, 0, 2, 1, 0, 2⟩ : IrVecN).toE + arlHButlastCost := by
  rw [arlHButlastAppendCost, arlHButlastAppendN_split, IrVecN.toE_add,
    ← arlHButlastN_toE]
  abel

/-- **What the composition really pays**, against what the judgment charges.
The append half is `arlHAppendMachineN` at the butlasted state, which
`arlHButlast_lt` pins to the in-place row. -/
theorem arlHButlastAppendRaw_eq (s : ArrayList) (x : ℕ) (hwf : s.Wf) :
    arlHButlastAppendRaw s x =
      NRest.consume (NRest.returnT
        ((arlAppendTotal (arlHButlastExecState s) x).buffer,
          ((arlAppendTotal (arlHButlastExecState s) x).length,
            (arlAppendTotal (arlHButlastExecState s) x).capacity)))
        arlHButlastAppendCost := by
  rw [arlHButlastAppendRaw, arlHButlastExecSpec_def,
    Lax13Proofs.Refine.Iicf.bindT_unit]
  show NRest.consume (arlHAppendExecSpec (arlHButlastExecState s) x) arlHButlastCost = _
  rw [arlHAppendExecSpec, arlHAppendMachineN_space _ (arlHButlast_lt hwf),
    NRest.consume_consume, arlHButlastAppendCost_split]
  congr 1
  abel

/-! ## 5. The composed rule, and the bridge to the list interface -/

noncomputable def arlHButlastAppendExecSpec (s : ArrayList) (x : ℕ) :
    NRest (List Val × (ℕ × ℕ)) ECost :=
  NRest.consume (NRest.returnT
    ((arlAppendTotal (arlHButlastExecState s) x).buffer,
      ((arlAppendTotal (arlHButlastExecState s) x).length,
        (arlAppendTotal (arlHButlastExecState s) x).capacity)))
    arlHButlastAppendCost

/-- **`butlast` then `append`, end to end**: one command, one judgment, one
exact price.  The hypotheses are the append's own — `arlTight` is what makes
the dispatch apply at the butlasted state — and the `butlast` contributes
none. -/
theorem arlHButlastAppend_exec_hnr (p hp k x : ℕ) (s : ArrayList)
    (hwf : s.Wf) (ht : arlTight s) :
    hnRefine (arlHButlastAppendPre p hp k x s) arlHButlastAppendCom
      (arlHAppendPost k x s.capacity) ("dc", ("len", "cap"))
      (heapBlockAssn ×ₐ natAssn ×ₐ natAssn) (arlHButlastAppendExecSpec s x) := by
  rw [arlHButlastAppendExecSpec, ← arlHButlastAppendRaw_eq s x hwf]
  exact arlHButlastAppend_dispatch p hp k x s hwf ht

/-- The value the command leaves refines `listButlast xs ++ [x]`, through the
same `arrayListRel` the interface is stated at.  Nothing is re-derived:
`arlHButlastExecState_refines` and `arlAppendTotal_refines` are the landed
theorems. -/
theorem arlHButlastAppendExecSpec_refines {s : ArrayList} {xs : List ℕ} {x : ℕ}
    (h : (s, xs) ∈ arrayListRel) (hne : xs ≠ []) :
    arlHButlastAppendExecSpec s x = NRest.consume (NRest.returnT
        ((arlAppendTotal (arlHButlastExecState s) x).buffer,
          ((arlAppendTotal (arlHButlastExecState s) x).length,
            (arlAppendTotal (arlHButlastExecState s) x).capacity)))
        arlHButlastAppendCost ∧
      (arlAppendTotal (arlHButlastExecState s) x, listButlast xs ++ [x]) ∈ arrayListRel :=
  ⟨rfl, arlAppendTotal_refines
    (arlHButlastExecState_refines h ((arrayListRel_nonempty h).symm ▸ hne))⟩

/-- Tightness survives the whole round trip, so the composition can be iterated
without ever re-establishing it. -/
theorem arlHButlastAppend_tight {s : ArrayList} {x : ℕ} (hwf : s.Wf) (ht : arlTight s) :
    arlTight (arlAppendTotal (arlHButlastExecState s) x) :=
  arlAppendTotal_tight (arlHButlast_wf hwf) (arlHButlast_tight ht)

/-! ## 6. The compiled gate

The composed command, pinned and **run** on a concrete heap, at ledger E39's
own kind of state: a tight block whose `butlast` *would* have triggered the
logical shrink.  Every price is compared with what the program charges.

Every negative control is a mutilation of the emitted command, stated as `≠`
against the correct run, so it compiles only because the mutilated program
really answers differently; each is `isSome`-guarded, and each junk scratch
value is a legal but wrong heap address, so a mutilated program runs to
completion rather than faulting (the precedent is ledger E38's controls). -/

namespace ArrayListButlastAppendGate

open Lax13Proofs.Refine.Ir.Gate (costVector readVars readArrs)

/-! ### Refute first: the pure model, before any program -/

/-- E39's counterexample, verbatim: tight, and the shrink fires on `butlast`. -/
def e39 : ArrayList := ⟨List.replicate 100 0, 17, 100⟩

#guard arlTight e39
-- The heap `butlast` keeps the capacity, and tightness with it …
#guard arlHButlastExecState e39 = ⟨List.replicate 100 0, 16, 100⟩
#guard arlTight (arlHButlastExecState e39)
-- … where the named-array `butlast` shrinks to 32 in a buffer of 100, and
-- tightness fails.  **The two representations genuinely disagree here**, and
-- that disagreement is this leaf's content.
#guard arlButlastExecState e39 = ⟨List.replicate 100 0, 16, 32⟩
#guard ¬ arlTight (arlButlastExecState e39)
#guard arlHButlastExecState e39 ≠ arlButlastExecState e39
-- They agree exactly where it counts: same abstract list.
#guard (arlHButlastExecState e39).active = (arlButlastExecState e39).active

/-- The gate's own state: the smallest tight block on which the shrink still
fires (`8 * 4 = 32 < 33` and `arlMinimumCapacity ≤ 16`). -/
def baList : ArrayList := ⟨List.replicate 33 0, 9, 33⟩

#guard arlTight baList
#guard arlHButlastExecState baList = ⟨List.replicate 33 0, 8, 33⟩
#guard arlTight (arlHButlastExecState baList)
#guard arlButlastExecState baList = ⟨List.replicate 33 0, 8, 16⟩
#guard ¬ arlTight (arlButlastExecState baList)

-- The composed answer, at the model level, and the invariant that lets it
-- iterate.
#guard arlAppendTotal (arlHButlastExecState baList) 42 =
  ⟨(List.replicate 33 0).set 8 42, 9, 33⟩
#guard arlTight (arlAppendTotal (arlHButlastExecState baList) 42)
-- …and it is `listButlast xs ++ [x]`, compiled.
#guard (arlAppendTotal (arlHButlastExecState baList) 42).active =
  listButlast baList.active ++ [42]

-- **The `butlast` is not a no-op**: with it the element lands at index 8, and
-- without it at index 9.
#guard arlAppendTotal (arlHButlastExecState baList) 42 ≠ arlAppendTotal baList 42

-- **Why the shrink is fatal to the composition.**  After the *landed*
-- `butlast` the state is not tight, and at a slack state `arlAppendTotal`
-- takes its logical-doubling branch, which the two-way heap dispatch does not
-- have: the model the dispatch implements and the source model disagree.  That
-- is the compiled form of ledger E39.
#guard arlPushGrown ⟨List.replicate 33 0, 16, 16⟩ 5 ≠
  arlAppendTotal ⟨List.replicate 33 0, 16, 16⟩ 5

-- The predicted price, before any run.
#guard arlHButlastAppendN = arlHButlastN + arlHAppendMachineN (arlHButlastExecState baList)
#guard arlHAppendMachineN (arlHButlastExecState baList) = ⟨1, 1, 0, 1, 0, 2, 1, 0, 2⟩

/-! ### The emitted command, pinned -/

#guard arlHButlastAppendCom =
  ((Com.binop .sub "len" "len" "one").seq (Com.skip.seq Com.skip)).seq arlHAppendCom

/-- The run's cost as one of `ArrayListCash.lean`'s nine-currency vectors. -/
def runVec (κ : Cost) : IrVecN :=
  ⟨κ.toFun Currency.ite, κ.toFun Currency.mul, κ.toFun Currency.«while»,
    κ.toFun Currency.copy, κ.toFun Currency.const, κ.toFun Currency.skip,
    κ.toFun Currency.aset, κ.toFun Currency.aget, κ.toFun Currency.add⟩

/-! ### The composed command, run

`baList`'s block sits at base `3` in a heap of `38`; the two cells above it are
distinctive junk that must not move, and the bump pointer starts past the whole
block. -/

def baHeap : List Val := [91, 92, 93] ++ List.replicate 33 0 ++ [94, 95]

def baState : State :=
  State.ofPairs
    [("bc", 3), ("len", 9), ("cap", 33), ("xc", 42), ("one", 1), ("two", 2),
     ("adr", 9), ("dc", 99), ("pc", 98), ("nc", 97), ("t", 96), ("si", 95),
     ("se", 94), ("di", 10), ("four", 4), ("fourN", 77), ("twoN", 78),
     ("outCap", 79), (hpName, 38)]
    [(heapName, baHeap)]

def baOut : State × Cost := (evalFuel 40 arlHButlastAppendCom baState).getD (baState, 0)

theorem baOut_evalFuel : evalFuel 40 arlHButlastAppendCom baState = some baOut := rfl

theorem baOut_bigStep : BigStep arlHButlastAppendCom baState baOut.1 baOut.2 :=
  bigStep_of_evalFuel baOut_evalFuel

-- The length went down and back up, the capacity never moved, the block did
-- not move, and **the bump pointer is untouched**: after a `butlast` the append
-- is always in place, so the composition never allocates.
#guard readVars baOut.1 ["dc", "len", "cap", hpName] =
  [("dc", some 3), ("len", some 9), ("cap", some 33), (hpName, some 38)]
#guard readArrs baOut.1 [heapName] =
  [(heapName, some ([91, 92, 93] ++ (List.replicate 33 0).set 8 42 ++ [94, 95]))]
-- **Differentially**, against the model: the block read back is
-- `arlAppendTotal (arlHButlastExecState baList) 42`.
#guard ((readArrs baOut.1 [heapName]).head?.map fun r => ((r.2.getD []).drop 3).take 33)
  = some (arlAppendTotal (arlHButlastExecState baList) 42).buffer
#guard readVars baOut.1 ["len", "cap"] =
  [("len", some (arlAppendTotal (arlHButlastExecState baList) 42).length),
   ("cap", some (arlAppendTotal (arlHButlastExecState baList) 42).capacity)]
-- …and the price is the predicted vector, on the nose.
#guard runVec baOut.2 = arlHButlastAppendN
#guard costVector baOut.2 =
  [("ir.skip", 4), ("ir.const", 0), ("ir.copy", 1), ("ir.aget", 0), ("ir.aset", 1),
   ("ir.ite", 1), ("ir.while", 0), ("ir.add", 2), ("ir.sub", 1), ("ir.mul", 1),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! ### Negative controls, each flipped and confirmed to bite -/

/-- **Control 1 — the length decrement dropped.**  Only the two packing
`skip`s are left, so the append writes at index `9` instead of `8`: the program
runs to completion, corrupts a different cell, and is one `ir.sub` cheaper. -/
def noPredCom : Com := (Com.skip.seq Com.skip).seq arlHAppendCom

#guard (evalFuel 40 noPredCom baState).isSome
#guard readArrs ((evalFuel 40 noPredCom baState).getD (baState, 0)).1 [heapName]
  ≠ readArrs baOut.1 [heapName]
#guard readVars ((evalFuel 40 noPredCom baState).getD (baState, 0)).1 ["len"]
  ≠ readVars baOut.1 ["len"]
#guard costVector ((evalFuel 40 noPredCom baState).getD (baState, 0)).2
  ≠ costVector baOut.2

/-- **Control 2 — the *landed*, shrinking `butlast` spliced into the
composition.**  This is the compiled form of the bug being fixed.  Its result
triple is `(bc, (len, outCap))`, so composing it with an append that reads
`cap` means re-seating the new capacity where the append expects it; the run
then completes and hands back a capacity of `16` for a block of `33`.  The heap
cell written is the same one — the defect is not a wrong answer in one step, it
is that the state left behind is **not tight**, so `arlHAppend_exec_hnr` no
longer applies to it and the model the dispatch implements diverges from
`arlAppendTotal` (the `arlPushGrown ≠ arlAppendTotal` guard above). -/
def oldButlastCom : Com :=
  (arlButlastCom "bc" "len" "cap" "one" "four" "two" "fourN" "twoN" "outCap").seq
    (Com.copy "cap" "outCap")

def oldCom : Com := oldButlastCom.seq arlHAppendCom

def oldOut : State × Cost := (evalFuel 60 oldCom baState).getD (baState, 0)

#guard (evalFuel 60 oldCom baState).isSome
-- **A heap-level or length-level control would not have bitten**, and saying so
-- is the point: the spliced-in shrink leaves the heap bit-identical, the same
-- length, and the same base.  Compiled, so that the one cell that does differ
-- is not mistaken for a lucky catch.
#guard readArrs oldOut.1 [heapName] = readArrs baOut.1 [heapName]
#guard readVars oldOut.1 ["dc", "len"] = readVars baOut.1 ["dc", "len"]
-- It bites on the capacity cell, and only there …
#guard readVars oldOut.1 ["cap"] = [("cap", some 16)]
#guard readVars oldOut.1 ["cap"] ≠ readVars baOut.1 ["cap"]
-- … which is exactly `arlShrinkCapacity`'s answer, i.e. the landed `butlast`
-- really is what was spliced in …
#guard readVars oldOut.1 ["cap"] =
  [("cap", some (arlButlastExecState baList).capacity)]
-- … and the state it leaves is the one `arlTight` rejects.
#guard ¬ arlTight ⟨(List.replicate 33 0).set 8 42, 9, 16⟩
-- It also costs four instructions more, so the price claim moves with it.
#guard runVec oldOut.2 ≠ arlHButlastAppendN

/-! **Control 3 — the composition without the `butlast` at all.**  The append
alone writes at index `9`; the `butlast` is load-bearing, not decoration. -/
#guard (evalFuel 40 arlHAppendCom baState).isSome
#guard readArrs ((evalFuel 40 arlHAppendCom baState).getD (baState, 0)).1 [heapName]
  ≠ readArrs baOut.1 [heapName]
#guard runVec ((evalFuel 40 arlHAppendCom baState).getD (baState, 0)).2
  ≠ arlHButlastAppendN

/-- **Control 4 — the append's block move dropped**, inside the composition:
the result cell `dc` keeps its junk value `99`, so the caller is handed a base
pointer that is not the block's, and the run is one `ir.copy` short. -/
def noMoveCom : Com :=
  ((Com.binop .sub "len" "len" "one").seq (Com.skip.seq Com.skip)).seq
    ((Com.binop .mul "nc" "cap" "two").seq
      (Com.ite (.lt (.cell "len") (.cell "cap"))
        ((Com.binop .add "adr" "bc" "len").seq
          ((Com.aset heapName "adr" "xc").seq
            ((Com.binop .add "len" "len" "one").seq (Com.skip.seq Com.skip))))
        arlHAppendGrowSynth_impl))

#guard (evalFuel 40 noMoveCom baState).isSome
#guard readVars ((evalFuel 40 noMoveCom baState).getD (baState, 0)).1 ["dc"]
  ≠ readVars baOut.1 ["dc"]
#guard runVec ((evalFuel 40 noMoveCom baState).getD (baState, 0)).2 ≠ arlHButlastAppendN

/-! **Control 5 — the cost claims themselves.**  One unit off the predicted
vector fails against the run, on every currency the composition spends, and the
`ir.sub` that `IrVecN` cannot carry is checked in the full vector. -/
#guard runVec baOut.2 ≠ (⟨0, 1, 0, 1, 0, 4, 1, 0, 2⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 0, 0, 1, 0, 4, 1, 0, 2⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 1, 1, 1, 0, 4, 1, 0, 2⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 1, 0, 2, 0, 4, 1, 0, 2⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 1, 0, 1, 1, 4, 1, 0, 2⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 1, 0, 1, 0, 3, 1, 0, 2⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 1, 0, 1, 0, 5, 1, 0, 2⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 1, 0, 1, 0, 4, 0, 0, 2⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 1, 0, 1, 0, 4, 1, 1, 2⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 1, 0, 1, 0, 4, 1, 0, 1⟩ : IrVecN)
#guard runVec baOut.2 ≠ (⟨1, 1, 0, 1, 0, 4, 1, 0, 3⟩ : IrVecN)
#guard costVector baOut.2 ≠
  [("ir.skip", 4), ("ir.const", 0), ("ir.copy", 1), ("ir.aget", 0), ("ir.aset", 1),
   ("ir.ite", 1), ("ir.while", 0), ("ir.add", 2), ("ir.sub", 0), ("ir.mul", 1),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! **Control 6 — the composed command *does* allocate**, which is exactly why
it stays out of `sepref_fr_rules` (ledger E29).  The `butlast` half does not:
the positive and the negative half of the same check.  The `butlast` half also
never mentions the heap array, which is the compiled form of the space argument
— dropping the shrink cannot change occupancy because neither version performs
a heap operation. -/
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

#guard mentions hpName arlHButlastAppendCom = true
#guard mentions hpName (arlHButlastCom "bc" "len" "cap" "one") = false
#guard mentions heapName (arlHButlastCom "bc" "len" "cap" "one") = false

end ArrayListButlastAppendGate

/-! ## 7. Axiom gate -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHButlast_tight' does not depend on any axioms -/
#guard_msgs in
#print axioms arlHButlast_tight

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHButlast_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arlHButlast_lt

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHButlastAppend_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHButlastAppend_dispatch

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHButlastAppendRaw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHButlastAppendRaw_eq

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHButlastAppend_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arlHButlastAppend_exec_hnr

/--
info: 'Lax13Proofs.Refine.Sepref.Iicf.arlHButlastAppendExecSpec_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms arlHButlastAppendExecSpec_refines

/-! ## 8. The guarantees are unchanged

This file adds an executable command and restates nothing about the
refinement.  `arlAppendOp_refines` is still `@[sepref_fref_thms]` over
`arrayListRel` at precondition `fun _ : List ℕ => True`, `arlButlastOp_refines`
still over the same relation at `xs ≠ []`, and `ArrayListCash.lean`'s compiled
guard still passes — as terms of this file. -/

theorem arlHButlastAppend_leaves_append_unchanged :
    (arlAppendOp, op_list_append ℕ) ∈
      fref (fun _ : List ℕ => True) arrayListRel
        (fun _ => Set.diagonal ℕ →ᵣ NRest.nrestRel arrayListRel) :=
  arlAppendOp_refines_unchanged

theorem arlHButlastAppend_leaves_butlast_unchanged :
    (arlButlastOp, op_list_butlast ℕ) ∈
      fref (fun xs : List ℕ => xs ≠ []) arrayListRel
        (fun _ => NRest.nrestRel arrayListRel) :=
  arlButlastOp_refines

theorem arlHButlastAppend_leaves_the_cost_story_unchanged (s : ArrayList) (x : ℕ)
    (hwf : s.Wf) (ht : arlTight s) :
    (arlHAppendMachineN s).toE + arlIrPotential (arlAppendTotal s x) ≤
      arlIrAdvertisedCost + arlIrPotential s :=
  arlHAppendMachine_amortized_ir s x hwf ht

end Lax13Proofs.Refine.Sepref.Iicf
