import Mathlib.Combinatorics.Colex
import Lax13Proofs.Refine.Iicf.IicfStack

/-!
# IICF: bitmask sets over one scalar cell

Structure 6 of `plans/word-ram/refinement-tower/p6-iicf-design.md`: an
abstract `Finset ℕ` living in **one** scalar cell holding
`∑ i ∈ S, 2 ^ i`. Three operations — `bmEmpty` (a constant), `bmInsert`
(shift-left and or), `bmMem` (shift-right and mask) — with membership
delivered as a fused guard on the result cell.

**The codegen trade-off, recorded here as the design record asks.** The
value in the cell is `∑ i ∈ S, 2 ^ i`, so a mask over elements `< n`
needs a word budget `B > 2 ^ n`. At *this* layer that is invisible: the
IR's `Val` is an unbounded `ℕ` (`Ir/Syntax.lean`: "the word bound is not
here — it enters once, at the existing `Bounds`/`Transfer` boundary"), so
nothing below constrains `n`, and every cost is an honest count of
`ir.shiftl` / `ir.or` / `ir.shiftr` / `ir.and` units. The bound is paid
at codegen, exactly as it is in the ND-MC campaign's RAM programs, which
use the same representation. A caller who needs `B` polynomial keeps
`n = O(log B)`; a caller who does not must use a different set structure.
The trade-off is *why* this structure is O(1) per operation, so it is
stated rather than hidden.

The wave's shared bridges come from `IicfStack.lean` (flag `P6/D-ba`).

## Judgment calls (continuing `IicfCsr.lean`'s P6/D-bk … P6/D-bm)

**P6/D-bn — the bitmask assertion is a *reindexing* of `natAssn`, with
neither an existential nor a pure conjunct.** `bmAssn S c = natAssn
(bmVal S) c`: the abstract value determines the concrete word exactly
(the representation map is injective — `Finset.geomSum_injective`), so
there is nothing to hide and nothing to assert. It is still opaque to the
P4 frame matcher, because `bmAssn` and `natAssn` are not defeq as
*functions*, which is what the matcher unifies; so the composite is
matched by name like every other structure, and `hnRefine_reinterp` does
the one type change (`ℕ` → `Finset ℕ`) at the two operations that produce
a set.

**P6/D-bo — membership is a fused guard on the *result* cell, not on the
structure.** `bmMem` is an ordinary operation returning `0` or `1` into a
scratch cell; the `sepref_cond_rules` entry `condRefine_bm_mem` then
reads `i ∈ S` off *that cell* (`r = 1`). This is the design record's
D6-P6-5 route applied to a value the structure computed rather than to
one it stores, and it is what lets the counting exercise branch on
membership with no boolean cell anywhere.

**P6/D-bp — the number theory is mathlib's.** `testBit_bmVal` is
`Finset.toFinset_bitIndices_sum_two_pow` (`Mathlib/Combinatorics/Colex`)
plus `Nat.mem_bitIndices`; `bmVal_insert` and `bmVal_mem` follow by
`Nat.eq_of_testBit_eq` and `Nat.testBit_div_two_pow`. Nothing was
hand-proved that mathlib already had; the one new import in the
Lax13Proofs tree is `Mathlib.Combinatorics.Colex`, for that single
`@[simp]` lemma.
-/

namespace Lax13Proofs.Refine.Iicf

open Sepref Ir NRest

/-! ## 1. The mask value and its three number-theoretic facts (P6/D-bp) -/

/-- The word a finite set of bit positions is stored as. -/
def bmVal (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2 ^ i

@[simp] theorem bmVal_empty : bmVal ∅ = 0 := by simp [bmVal]

/-- **The characteristic fact**: the mask's bits are the set. -/
theorem testBit_bmVal (S : Finset ℕ) (j : ℕ) : (bmVal S).testBit j = decide (j ∈ S) := by
  rw [bmVal]
  by_cases h : j ∈ S
  · simpa [h] using (Nat.mem_bitIndices (i := j) (n := ∑ i ∈ S, 2 ^ i)).1
      (by rw [← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]; exact h)
  · have hc : ¬ ((∑ i ∈ S, 2 ^ i).testBit j = true) := by
      intro hc
      exact h (by
        have := Nat.mem_bitIndices.2 hc
        rwa [← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow] at this)
    simp [h, hc]

/-- Insertion is a bitwise or with the element's power of two. -/
theorem bmVal_insert (S : Finset ℕ) (i : ℕ) : Nat.lor (bmVal S) (2 ^ i) = bmVal (insert i S) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  show ((bmVal S ||| 2 ^ i).testBit j) = _
  rw [Nat.testBit_or, testBit_bmVal, Nat.testBit_two_pow, testBit_bmVal]
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, Ne.symm hj]

/-- Membership is a shift and a mask. -/
theorem bmVal_mem (S : Finset ℕ) (i : ℕ) :
    Nat.land (bmVal S / 2 ^ i) 1 = if i ∈ S then 1 else 0 := by
  show ((bmVal S / 2 ^ i) &&& 1) = _
  rw [Nat.and_one_is_mod]
  have h : (bmVal S / 2 ^ i).testBit 0 = decide (i ∈ S) := by
    rw [Nat.testBit_div_two_pow, Nat.zero_add, testBit_bmVal]
  rw [Nat.testBit_zero] at h
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have h1 : bmVal S / 2 ^ i % 2 = 1 := by simpa [hi] using h
    exact h1
  · rw [if_neg hi]
    have h1 : ¬ (bmVal S / 2 ^ i % 2 = 1) := by simpa [hi] using h
    omega

/-! ## 2. The bitmask assertion (P6/D-bn) -/

/-- The composite assertion: one scalar cell holding the mask. -/
def bmAssn : Finset ℕ → String → Assn := fun S c => natAssn (bmVal S) c

/-- The unfold lemma (definitional). -/
theorem bmAssn_unfold (S : Finset ℕ) (c : String) :
    hnCtxt bmAssn S c = hnCtxt natAssn (bmVal S) c := rfl

/-- Closing the composite. -/
theorem bmAssn_intro (S : Finset ℕ) (v : ℕ) (c : String) (hv : v = bmVal S) :
    natAssn v c ⊢ bmAssn S c := by rw [hv]; exact entails_refl _

/-- **Establishment from junk**: a cell holding `0` is the empty set.
There is no allocation (design D6-P6-2). -/
theorem bmAssn_init (c : String) : hnCtxt natAssn 0 c ⊢ hnCtxt bmAssn ∅ c := by
  rw [bmAssn_unfold, bmVal_empty]

/-- **Release to junk.** -/
theorem bmAssn_release (S : Finset ℕ) (c : String) : hnCtxt bmAssn S c ⊢ junkCell c :=
  natAssn_entails_junkCell (bmVal S) c

/-! ## 3. Refute before prove

The mask arithmetic, executed on concrete sets before anything is proved
about it: `bmVal` is the representation, and the two `#guard`ed
identities are exactly `bmVal_insert` and `bmVal_mem` at those sets. -/

/-- The abstract operations, as computable twins. -/
def bmInsertTwin (S : Finset ℕ) (i : ℕ) : Finset ℕ := insert i S
def bmMemTwin (S : Finset ℕ) (i : ℕ) : ℕ := if i ∈ S then 1 else 0

#guard bmVal ∅ = 0
#guard bmVal {0} = 1
#guard bmVal {0, 2} = 5
#guard bmVal {0, 1, 2} = 7
#guard bmVal {3} = 8

-- `bmVal_insert`, on concrete sets — including the idempotent case.
#guard Nat.lor (bmVal {0, 2}) (2 ^ 1) = bmVal (bmInsertTwin {0, 2} 1)
#guard Nat.lor (bmVal {0, 2}) (2 ^ 2) = bmVal (bmInsertTwin {0, 2} 2)
#guard Nat.lor (bmVal ∅) (2 ^ 3) = bmVal (bmInsertTwin ∅ 3)

-- `bmVal_mem`, on concrete sets.
#guard Nat.land (bmVal {0, 2} / 2 ^ 0) 1 = bmMemTwin {0, 2} 0
#guard Nat.land (bmVal {0, 2} / 2 ^ 1) 1 = bmMemTwin {0, 2} 1
#guard Nat.land (bmVal {0, 2} / 2 ^ 2) 1 = bmMemTwin {0, 2} 2
#guard Nat.land (bmVal {0, 2} / 2 ^ 5) 1 = bmMemTwin {0, 2} 5

-- **Negative control 1.** The mask is little-endian: `{0,2}` is `5`,
-- not `6`.
/--
error: Expression
  decide (bmVal {0, 2} = 6)
did not evaluate to `true`
-/
#guard_msgs in
#guard bmVal {0, 2} = 6

-- **Negative control 2.** Membership is a *bit* test, not a comparison:
-- `1 ∉ {0,2}` even though the mask `5` is odd at other positions.
/--
error: Expression
  decide ((bmVal {0, 2} / 2 ^ 1).land 1 = 1)
did not evaluate to `true`
-/
#guard_msgs in
#guard Nat.land (bmVal {0, 2} / 2 ^ 1) 1 = 1

/-! ## 4. The interface operations (design D6-P6-1) -/

/-- `bmEmpty`: one constant write. -/
noncomputable def bmEmptyCost : ECost := irUnit Currency.const

/-- `bmInsert`: a shift and an or. -/
noncomputable def bmInsertCost : ECost := irUnit Currency.shiftl + irUnit Currency.or

/-- `bmMem`: a shift and a mask. -/
noncomputable def bmMemCost : ECost := irUnit Currency.shiftr + irUnit Currency.and

/-- The empty set, as an operation. -/
noncomputable def mopBmEmpty : NRest (Finset ℕ) ECost :=
  NRest.consume (NRest.returnT (∅ : Finset ℕ)) bmEmptyCost

/-- Insert `i`; idempotent, as the bitwise or is. -/
noncomputable def mopBmInsert (S : Finset ℕ) (i : ℕ) : NRest (Finset ℕ) ECost :=
  NRest.consume (NRest.returnT (insert i S)) bmInsertCost

/-- Test `i`, delivering `1` or `0` into a scratch cell (P6/D-bo). -/
noncomputable def mopBmMem (S : Finset ℕ) (i : ℕ) : NRest ℕ ECost :=
  NRest.consume (NRest.returnT (if i ∈ S then 1 else 0)) bmMemCost

theorem mopBmEmpty_def :
    mopBmEmpty = NRest.consume (NRest.returnT (∅ : Finset ℕ)) bmEmptyCost := rfl

theorem mopBmInsert_def (S : Finset ℕ) (i : ℕ) :
    mopBmInsert S i = NRest.consume (NRest.returnT (insert i S)) bmInsertCost := rfl

theorem mopBmMem_def (S : Finset ℕ) (i : ℕ) :
    mopBmMem S i = NRest.consume (NRest.returnT (if i ∈ S then 1 else 0)) bmMemCost := rfl

/-! ## 5. The raw chains and their synthesis (P6/D-bc) -/

/-- The raw chain `bmInsert` expands to: `t := 1 << i`, `m := m ||| t`. -/
noncomputable def bmInsertRaw (m i : ℕ) : NRest ℕ ECost :=
  NRest.bindT (mopBinop .shiftl 1 i) fun b => mopBinop .or m b

/-- The raw chain `bmMem` expands to: `r := m >> i`, `r := r &&& 1`. -/
noncomputable def bmMemRaw (m i : ℕ) : NRest ℕ ECost :=
  NRest.bindT (mopBinop .shiftr m i) fun a => mopBinop .and a 1

theorem bmInsertRaw_eq (m i : ℕ) :
    bmInsertRaw m i = NRest.consume (NRest.returnT (Nat.lor m (2 ^ i))) bmInsertCost := by
  show NRest.bindT (mopBinop .shiftl 1 i) _ = _
  rw [mopBinop_def, bindT_unit, mopBinop_def, NRest.consume_consume]
  simp only [Imp.Bop.apply_shiftl, Imp.Bop.apply_or, one_mul, binopCurrency_shiftl,
    binopCurrency_or, bmInsertCost]

theorem bmMemRaw_eq (m i : ℕ) :
    bmMemRaw m i = NRest.consume (NRest.returnT (Nat.land (m / 2 ^ i) 1)) bmMemCost := by
  show NRest.bindT (mopBinop .shiftr m i) _ = _
  rw [mopBinop_def, bindT_unit, mopBinop_def, NRest.consume_consume]
  simp only [Imp.Bop.apply_shiftr, Imp.Bop.apply_and, binopCurrency_shiftr,
    binopCurrency_and, bmMemCost]

/-- The program `bmEmpty` compiles to. -/
def bmEmptyCom (m : String) : Com := .const m 0

/-- The program `bmInsert` compiles to. -/
def bmInsertCom (m t ic one : String) : Com :=
  .seq (.binop .shiftl t one ic) (.binop .or m m t)

/-- The program `bmMem` compiles to. -/
def bmMemCom (m ic r one : String) : Com :=
  .seq (.binop .shiftr r m ic) (.binop .and r r one)

#guard bmEmptyCom "m" = Com.const "m" 0
#guard bmInsertCom "m" "t" "i" "one" =
  Com.seq (Com.binop Imp.Bop.shiftl "t" "one" "i") (Com.binop Imp.Bop.or "m" "m" "t")
#guard bmMemCom "m" "i" "r" "one" =
  Com.seq (Com.binop Imp.Bop.shiftr "r" "m" "i") (Com.binop Imp.Bop.and "r" "r" "one")

sepref_synth bmEmptySynth (m : String) :
  hnRefine (junkCell m) _ _ m natAssn (mopConstN 0)

sepref_synth bmInsertSynth (m t ic one : String) (w i : ℕ) :
  hnRefine (hnCtxt natAssn w m ∗ junkCell t ∗ hnCtxt natAssn i ic ∗ hnCtxt natAssn 1 one)
    _ _ m natAssn (bmInsertRaw w i)

sepref_synth bmMemSynth (m ic r one : String) (w i : ℕ) :
  hnRefine (hnCtxt natAssn w m ∗ junkCell r ∗ hnCtxt natAssn i ic ∗ hnCtxt natAssn 1 one)
    _ _ r natAssn (bmMemRaw w i)

/-! ## 6. The composite rules (P6/D-bc, P6/D-bn)

`bmEmpty` and `bmInsert` produce a *set*, so they go through
`hnRefine_reinterp`; `bmMem` produces a scalar and does not. -/

@[sepref_fr_rules]
theorem hnr_mop_bmEmpty (m : String) :
    hnRefine (junkCell m) (bmEmptyCom m) (□ : Assn) m bmAssn mopBmEmpty := by
  rw [mopBmEmpty_def]
  refine hnRefine_reinterp (A := natAssn) (r := 0) ?_ (bmAssn_intro ∅ 0 m bmVal_empty.symm)
  exact bmEmptySynth m

@[sepref_fr_rules]
theorem hnr_mop_bmInsert (S : Finset ℕ) (i : ℕ) (m t ic one : String) :
    hnRefine (hnCtxt bmAssn S m ∗ junkCell t ∗ hnCtxt natAssn i ic ∗ hnCtxt natAssn 1 one)
      (bmInsertCom m t ic one)
      (hnCtxt natAssn i ic ∗ junkCell t ∗ hnCtxt natAssn 1 one) m bmAssn
      (mopBmInsert S i) := by
  rw [mopBmInsert_def]
  have hsyn := hnRefine_abs_cong (bmInsertRaw_eq (bmVal S) i).symm
    (bmInsertSynth m t ic one (bmVal S) i)
  refine hnRefine_cons_post
    (hnRefine_reinterp hsyn (bmAssn_intro (insert i S) _ m (bmVal_insert S i))) ?_
  fri

@[sepref_fr_rules]
theorem hnr_mop_bmMem (S : Finset ℕ) (i : ℕ) (m ic r one : String) :
    hnRefine (hnCtxt bmAssn S m ∗ junkCell r ∗ hnCtxt natAssn i ic ∗ hnCtxt natAssn 1 one)
      (bmMemCom m ic r one)
      (hnCtxt bmAssn S m ∗ hnCtxt natAssn i ic ∗ hnCtxt natAssn 1 one) r natAssn
      (mopBmMem S i) := by
  rw [mopBmMem_def]
  have hsyn := hnRefine_abs_cong
    (show NRest.consume (NRest.returnT (if i ∈ S then 1 else 0)) bmMemCost
        = NRest.consume (NRest.returnT (Nat.land (bmVal S / 2 ^ i) 1)) bmMemCost from by
      rw [bmVal_mem])
    (hnRefine_abs_cong (bmMemRaw_eq (bmVal S) i).symm (bmMemSynth m ic r one (bmVal S) i))
  refine hnRefine_cons_post hsyn ?_
  show _ ⊢ hnCtxt natAssn (bmVal S) m ∗ hnCtxt natAssn i ic ∗ hnCtxt natAssn 1 one
  fri

/-! ## 7. Membership as a fused guard on the result cell (P6/D-bo) -/

@[sepref_cond_rules]
theorem condRefine_bm_mem (S : Finset ℕ) (i : ℕ) (r : String) :
    CondRefine (hnCtxt natAssn (if i ∈ S then 1 else 0) r) (.eq (.cell r) (.lit 1))
      (decide (i ∈ S)) := by
  intro F st cr hs
  simp only [hnCtxt_def, natAssn_def] at hs
  have hv := ptoVar_vars hs
  rw [Cond.eval_eq, Operand.eval_cell, Operand.eval_lit, hv]
  simp only [Option.bind_some, Option.map_some, Option.some.injEq]
  by_cases hi : i ∈ S <;> simp [hi]

/-! ## 8. Exercise: insert loop, then membership count

Three programs through `sepref_synth`, consuming only the registered
rules of §6 and §7 (plus `IicfStack.lean`'s, for the loop that feeds the
mask) — no bespoke tactic, no hand-written frame clause. -/

namespace BmExercise

/-! ### Refute before prove -/

/-- The insert loop's twin: drain a stack into a mask. -/
def bmFillRun : ℕ → Finset ℕ × List ℕ → Finset ℕ × List ℕ
  | 0, st => st
  | k + 1, st => if st.2 ≠ [] then bmFillRun k (insert st.2.head! st.1, st.2.tail) else st

/-- The count loop's twin: `∑_{i<n} [i ∈ S]`. -/
def bmCountRun (S : Finset ℕ) (n : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, st => st
  | k + 1, st =>
    if st.1 < n then bmCountRun S n k (st.1 + 1, st.2 + (if st.1 ∈ S then 1 else 0)) else st

/-- Drain the list into a mask, then count its members below `n`. -/
def fillCount (l : List ℕ) (n : ℕ) : ℕ :=
  (bmCountRun (bmFillRun l.length (∅, l)).1 n n (0, 0)).2

#guard (bmFillRun 3 (∅, [0, 2, 3])).1 = ({0, 2, 3} : Finset ℕ)
#guard bmVal (bmFillRun 3 (∅, [0, 2, 3])).1 = 13
#guard fillCount [0, 2, 3] 4 = 3
#guard fillCount [0, 2, 3] 3 = 2
#guard fillCount [] 4 = 0
-- Duplicates collapse: the mask is a *set*.
#guard fillCount [1, 1, 1] 4 = 1
#guard fillCount [0, 1, 2, 3] 4 = 4
-- …and against an independent decider of the same quantity.
#guard fillCount [0, 2, 3] 5 = ((List.range 5).filter (· ∈ [0, 2, 3])).length

-- **Negative control.** A wrong expected count fails.
/--
error: Expression
  decide (fillCount [0, 2, 3] 4 = 4)
did not evaluate to `true`
-/
#guard_msgs in
#guard fillCount [0, 2, 3] 4 = 4

/-! ### The insert loop, driven by a stack drain

The loop that would be *natural* here — `for i in 0..n: insert i` —
cannot be synthesized, and the reason is P4's greedy scratch allocation
again (`IicfStack.lean`'s P6/D-be): the composite `bmInsert` hands its
scratch cell **back as junk**, so the counter bump that follows it finds
a free cell and `hnr_mop_binop` (destination-taking) is tried before
`hnr_mop_binop_self` (in-place), which breaks the loop state. Draining a
stack into the mask has no counter to bump, the scratch cells are
consumed in the order the pool offers them, and the exercise doubles as
the wave's **cross-structure composition** demo: `IicfStack`'s `pop` and
this file's `bmInsert` in one synthesized body, with the emptiness guard
coming from the stack (flag `P6/D-bq`). -/

/-- No invariant: the guard gives `pop`'s nonemptiness. -/
def bmFillI : Finset ℕ × List ℕ → Prop := fun _ => True

/-- The guard: the feeding stack is nonempty. -/
def bmFillBf : Finset ℕ × List ℕ → Bool := fun st => decide (st.2 ≠ [])

/-- The body: pop an element, insert it, retuple. -/
noncomputable def bmFillF : Finset ℕ × List ℕ → NRest (Finset ℕ × List ℕ) ECost := fun st =>
  NRest.bindT (mopPop st.2) fun p =>
    NRest.bindT (mopBmInsert st.1 p.1) fun S' => mopPair S' p.2

/-- One iteration's price: a pop, an insert and the tuple. -/
noncomputable def bmFillCost : ECost := popCost + bmInsertCost + irUnit Currency.skip

theorem bmFillF_eq (st : Finset ℕ × List ℕ) (h : st.2 ≠ []) :
    bmFillF st
      = NRest.consume (NRest.returnT (insert st.2.head! st.1, st.2.tail)) bmFillCost := by
  show NRest.bindT (mopPop st.2) _ = _
  rw [mopPop_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, mopBmInsert_def,
    bindT_unit, mopPair_def, NRest.consume_consume, NRest.consume_consume]
  simp only [bmFillCost]

theorem bmFill_variant : LOOP_VARIANT bmFillI bmFillBf bmFillF (fun st => st.2.length) := by
  intro st st' _ hb hle
  have hb' : st.2 ≠ [] := by simpa [bmFillBf] using hb
  rw [bmFillF_eq st hb', NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hst : st' = (insert st.2.head! st.1, st.2.tail) := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hst
  show st.2.tail.length < st.2.length
  cases hs : st.2 with
  | nil => exact absurd hs hb'
  | cons a t => simp

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth bmFill (l₀ : List ℕ)
    (hv : LOOP_VARIANT bmFillI bmFillBf bmFillF (fun st => st.2.length)) :
  hnRefine (hnCtxt (bmAssn ×ₐ stackAssn 8) (∅, l₀) ("m", ("S", "top")) ∗
      junkCell "r" ∗ junkCell "t" ∗ hnCtxt natAssn 1 "one")
    _ _ ("m", ("S", "top")) (bmAssn ×ₐ stackAssn 8)
    (irWhileIT bmFillI bmFillBf bmFillF (∅, l₀))

/-! ### The count loop

Branchless: `bmMem` already delivers `0` or `1`, so the count is a sum.
The *branching* use of the fused membership guard is the straight-line
program below it. -/

def bmCountI : ℕ × ℕ → Prop := fun _ => True

def bmCountBf (n : ℕ) : ℕ × ℕ → Bool := fun st => decide (st.1 < n)

/-- The body: test membership into the scratch cell, accumulate,
advance. -/
noncomputable def bmCountF (S : Finset ℕ) : ℕ × ℕ → NRest (ℕ × ℕ) ECost := fun st =>
  NRest.bindT (mopBmMem S st.1) fun w =>
    NRest.bindT (mopBinop .add st.2 w) fun c' =>
      NRest.bindT (mopBinop .add st.1 1) fun i' => mopPair i' c'

/-- One iteration's price. -/
noncomputable def bmCountCost : ECost :=
  bmMemCost + irUnit Currency.add + irUnit Currency.add + irUnit Currency.skip

theorem bmCountF_eq (S : Finset ℕ) (st : ℕ × ℕ) :
    bmCountF S st = NRest.consume
      (NRest.returnT (st.1 + 1, st.2 + (if st.1 ∈ S then 1 else 0))) bmCountCost := by
  show NRest.bindT (mopBmMem S st.1) _ = _
  rw [mopBmMem_def, bindT_unit, mopBinop_def, bindT_unit, mopBinop_def, bindT_unit,
    mopPair_def, NRest.consume_consume, NRest.consume_consume, NRest.consume_consume]
  simp only [bmCountCost, Imp.Bop.apply_add, binopCurrency_add]

theorem bmCount_variant (S : Finset ℕ) (n : ℕ) :
    LOOP_VARIANT bmCountI (bmCountBf n) (bmCountF S) (fun st => n - st.1) := by
  intro st st' _ hb hle
  have hb' : st.1 < n := by simpa [bmCountBf] using hb
  rw [bmCountF_eq S st, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hst : st' = (st.1 + 1, st.2 + (if st.1 ∈ S then 1 else 0)) := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hst
  show n - (st.1 + 1) < n - st.1
  omega

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth bmCount (S : Finset ℕ) (n : ℕ)
    (hv : LOOP_VARIANT bmCountI (bmCountBf n) (bmCountF S) (fun st => n - st.1)) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn) (0, 0) ("i", "cnt") ∗ junkCell "w" ∗
      hnCtxt bmAssn S "m" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one")
    _ _ ("i", "cnt") (natAssn ×ₐ natAssn)
    (irWhileIT bmCountI (bmCountBf n) (bmCountF S) (0, 0))

/-! ### The fused membership guard, branching (P6/D-br)

`if i ∈ S then r := 1 else r := 0`, with the guard `w = 1` read off the
cell `bmMem` just wrote. No boolean cell anywhere.

**P6/D-br — the branch is written at `decide (w = 1)`, not at
`decide (i ∈ S)`, and this is forced by `hnr_bind`.** The bind rule
delivers its result as a *universally quantified* value `a` with only
`bind_ref_tag a m` to relate it to the operation (`Sepref/Translate.lean`,
`hnr_bind`), so inside the continuation the cell `w` is owned at `a`, not
at `if i ∈ S then 1 else 0` — a `CondRefine` rule stated at the latter
can never match. The honest program therefore branches on the *value the
operation returned*, which the primitive `condRefine_eq_cell_lit`
translates directly; `bmMem_guard` below is the one-line interface fact
that turns that branch back into membership for the caller.
`condRefine_bm_mem` stays registered for the case where the cell's value
*is* syntactically the membership test (a caller who inlines it), and is
the design record's D6-P6-5 shape; the two together are what the
structure offers. -/

/-- The interface fact behind the guard: `bmMem`'s result is `1` exactly
on members. -/
theorem bmMem_guard (S : Finset ℕ) (i : ℕ) :
    decide ((if i ∈ S then 1 else 0) = 1) = decide (i ∈ S) := by
  by_cases hi : i ∈ S <;> simp [hi]

sepref_synth bmBranch (S : Finset ℕ) (i : ℕ) :
  hnRefine (hnCtxt bmAssn S "m" ∗ junkCell "w" ∗ hnCtxt natAssn i "i" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "r")
    _ _ "r" natAssn
    (NRest.bindT (mopBmMem S i) fun w =>
      irIf (decide (w = 1)) (mopConstN 1) (mopConstN 0))

-- The synthesized insert loop, pinned: `IicfStack`'s `pop` and this
-- file's `bmInsert`, in one body, with the stack's emptiness guard.
#guard bmFill_impl =
  Com.while (Cond.lt (Operand.cell "top") (Operand.lit 8))
    (Com.seq (Com.seq (Com.aget "r" "S" "top")
        (Com.seq (Com.binop Imp.Bop.add "top" "top" "one") (Com.seq Com.skip Com.skip)))
      (Com.seq (Com.seq (Com.binop Imp.Bop.shiftl "t" "one" "r")
          (Com.binop Imp.Bop.or "m" "m" "t")) Com.skip))

-- …the count loop: shift, mask, accumulate, advance.
#guard bmCount_impl =
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    (Com.seq (Com.seq (Com.binop Imp.Bop.shiftr "w" "m" "i")
        (Com.binop Imp.Bop.and "w" "w" "one"))
      (Com.seq (Com.binop Imp.Bop.add "cnt" "cnt" "w")
        (Com.seq (Com.binop Imp.Bop.add "i" "i" "one") Com.skip)))

-- …and the branch, whose condition `w = one` is the fused membership
-- guard the tool synthesized from `decide (w = 1)` (P6/D-br).
#guard bmBranch_impl =
  Com.seq (Com.seq (Com.binop Imp.Bop.shiftr "w" "m" "i")
      (Com.binop Imp.Bop.and "w" "w" "one"))
    (Com.ite (Cond.eq (Operand.cell "w") (Operand.cell "one"))
      (Com.const "r" 1) (Com.const "r" 0))

/-- The insert loop with its variant discharged. -/
theorem bmFill' (l₀ : List ℕ) :
    hnRefine (hnCtxt (bmAssn ×ₐ stackAssn 8) (∅, l₀) ("m", ("S", "top")) ∗
        junkCell "r" ∗ junkCell "t" ∗ hnCtxt natAssn 1 "one")
      bmFill_impl (junkCell "r" ∗ junkCell "t" ∗ hnCtxt natAssn 1 "one")
      ("m", ("S", "top")) (bmAssn ×ₐ stackAssn 8)
      (irWhileIT bmFillI bmFillBf bmFillF (∅, l₀)) :=
  bmFill l₀ bmFill_variant

/-- The count loop with its variant discharged. -/
theorem bmCount' (S : Finset ℕ) (n : ℕ) :
    hnRefine (hnCtxt (natAssn ×ₐ natAssn) (0, 0) ("i", "cnt") ∗ junkCell "w" ∗
        hnCtxt bmAssn S "m" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one")
      bmCount_impl (junkCell "w" ∗ hnCtxt bmAssn S "m" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn 1 "one") ("i", "cnt") (natAssn ×ₐ natAssn)
      (irWhileIT bmCountI (bmCountBf n) (bmCountF S) (0, 0)) :=
  bmCount S n (bmCount_variant S n)

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_bmEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_bmEmpty

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_bmInsert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_bmInsert

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_bmMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_bmMem

/-- info: 'Lax13Proofs.Refine.Iicf.BmExercise.bmFill'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bmFill'

/-- info: 'Lax13Proofs.Refine.Iicf.BmExercise.bmCount'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bmCount'

/-- info: 'Lax13Proofs.Refine.Iicf.BmExercise.bmBranch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bmBranch

end BmExercise

end Lax13Proofs.Refine.Iicf
