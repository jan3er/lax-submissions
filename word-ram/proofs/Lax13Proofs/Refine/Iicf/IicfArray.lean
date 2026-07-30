import Lax13Proofs.Refine.Iicf.Basic
import Lax13Proofs.Refine.Examples.ArrayFill

/-!
# Plain arrays — the interface completions (design record §"The structures" 1)

`arrayAssn` and the primitive `mopAget`/`mopAset` already exist
(`Sepref/IrOps.lean`); what an *interface* needs on top of them is the
compound operations, and the one this file adds is **fill**:
`mop_array_fill xs v` overwrites every entry of `xs` with `v`, as **one
interface op** with a closed-form linear cost (P6/D-j).

The point of the file is not the operation — it is *how it is produced*
(D6-P6-3):

```
primitive mops (mopAset, mopBinop, mopPair, mopConstN)
  ──sepref_synth──▶  fillLoop_impl : Ir.Com          (§3, pinned by #guard)
  ──fillLoop_value──▶ closed form consume (returnT …) fillCost   (§4)
  ──hnRefine_res_cast──▶ hnr_mop_array_fill @[sepref_fr_rules]   (§5)
  ──sepref──▶ consumed by an exercise with no hand frame work    (§6)
```

Nobody writes the implementation, and nobody writes the cost: `fillCost`
is read off what the pipeline spent.

## Judgment calls

**P6/D-l — the array-shape lemmas are reused from
`Refine/Examples/ArrayFill.lean`, not re-proved.** That file's `filled m
val xs = List.replicate m val ++ xs.drop m` and its three facts
(`filled_length`, `filled_set`, `filled_all`) are exactly the induction
step of the fill loop, landed in P3 and proved once. Standing practice
("landed proofs are capital") says thread them. The direction of the
dependency — a library file importing an examples file — is the wart;
the fix is to move `filled` into a shared list-lemma module, which is a
rename and is backlog, not proof content.

**P6/D-m — static length, no `mop_array_length` (design D6-P6-4).** The
abstract type is `List ℕ`, which knows its length; the *concrete* length
must nevertheless be readable by the loop guard, so `hnr_mop_array_fill`
takes a cell holding `xs.length` in its precondition rather than an op
that computes it. This is the source's own discipline (`IICF_Array.thy`
has no `array_length`: `op_list_length` is refined by a *pure* rule off
the length being statically known) and it is what "capacity fixed at
init" means on a no-alloc substrate. Fallback: `Com` has no length
instruction at all, so an op is not merely undesirable but unavailable.

**P6/D-n — the op zeroes its own index cell, so its precondition takes
`junkCell` and not a cell that already holds `0`.** The synthesized
program is `i := 0; while i < n do {A[i] := v; i := i + 1}`, i.e. the
abstract program is `mopConstN 0 >>= fun z => irWhileIT … (z, xs)`, not
the bare loop. Without the prefix the rule would only be applicable to a
caller who happens to own a zeroed index cell, which is not an
interface. The price is one `ir.const` in `fillCost`, and the pipeline
charges it whether or not we like it.

**P6/D-o — the loop state is `(i, xs)` and the op's result is `xs`
alone; the gap is closed by `hnRefine_res_cast` (P6/D-k), not by a
projection rule.** P4/D-ec forces the array into the loop state (the loop
rule's body post is its frame, so everything the body mutates is in the
state). An interface op that returned a pair would push that
implementation detail onto every consumer.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

namespace Iicf

open Ir.Examples (filled)

/-! ## 1. Refute before prove

The abstract fill loop is *run* before anything is proved about it,
through a computable twin of its own step function — `fillStep` is the
function §4's body-value lemma proves the abstract body equal to, so a
`#guard` here is a `#guard` about the abstract program. -/

/-- The loop guard: `i < n`, read from the cell holding the static
length (P6/D-m). -/
def fillBf (n : ℕ) : ℕ × List ℕ → Bool := fun s => decide (s.1 < n)

/-- One iteration: write `val` at `i`, advance. -/
def fillStep (val : ℕ) (s : ℕ × List ℕ) : ℕ × List ℕ := (s.1 + 1, s.2.set s.1 val)

/-- The twin loop. -/
def fillRun (n val : ℕ) : ℕ → ℕ × List ℕ → ℕ × List ℕ
  | 0, s => s
  | k + 1, s => if fillBf n s then fillRun n val k (fillStep val s) else s

/-- What the abstract program computes. -/
def fillOut (val : ℕ) (xs : List ℕ) : List ℕ := (fillRun xs.length val xs.length (0, xs)).2

#guard fillOut 7 [1, 2, 3] = [7, 7, 7]
#guard fillOut 0 [5] = [0]
#guard fillOut 7 ([] : List ℕ) = []
-- …and against the specification the interface op states.
#guard fillOut 7 [1, 2, 3] = List.replicate 3 7
#guard fillOut 4 [9, 9, 9, 9, 9] = List.replicate 5 4
#guard fillOut 4 ([] : List ℕ) = List.replicate 0 4

-- **Negative control.** A wrong expected array fails, and says so.
/--
error: Expression
  decide (fillOut 7 [1, 2, 3] = [7, 7, 1])
did not evaluate to `true`
-/
#guard_msgs in
#guard fillOut 7 [1, 2, 3] = [7, 7, 1]

/-! ## 2. The abstract loop

The invariant is the *static length* discipline (P6/D-m): the loop's list
has the length the guard's cell holds. Together with the guard it gives
the write's index bound, which is all the body-value lemma needs
(P4/D-ed). -/

/-- The invariant: the state's list has the static length. -/
def fillI (n : ℕ) : ℕ × List ℕ → Prop := fun s => s.2.length = n

/-- **The body.** `A[i] := v; i := i + 1; (i, A)`. -/
noncomputable def fillF (val : ℕ) : ℕ × List ℕ → NRest (ℕ × List ℕ) ECost := fun s =>
  NRest.bindT (mopAset s.2 s.1 val) fun ys =>
    NRest.bindT (mopBinop .add s.1 1) fun i' => mopPair i' ys

/-- One iteration's price: a write, an increment, and the tuple. -/
noncomputable def fillStepCost : ECost :=
  irUnit Currency.aset + irUnit Currency.add + irUnit Currency.skip

/-- **The body's value** — the fact §1's twin is a twin of. -/
theorem fillF_eq (val : ℕ) (s : ℕ × List ℕ) (h : s.1 < s.2.length) :
    fillF val s = NRest.consume (NRest.returnT (fillStep val s)) fillStepCost := by
  show NRest.bindT (mopAset s.2 s.1 val) _ = _
  simp only [mopAset_def, mopBinop_def, mopPair_def, NRest.assert_pos h,
    NRest.returnT_bindT, bindT_unit, NRest.consume_consume, fillStep,
    fillStepCost, Imp.Bop.apply_add, binopCurrency_add]
  congr 1
  ac_rfl

/-- The variant: the iterations still to run. -/
def fillV (n : ℕ) : ℕ × List ℕ → ℕ := fun s => n - s.1

/-- The variant obligation `sepref_synth` takes as an annotation
(P4/D-cv). -/
theorem fill_variant (n val : ℕ) : LOOP_VARIANT (fillI n) (fillBf n) (fillF val) (fillV n) := by
  intro s s' hI hb hle
  have hlen : s.2.length = n := hI
  have hlt : s.1 < n := by simpa [fillBf] using hb
  have h : s.1 < s.2.length := by omega
  rw [fillF_eq val s h, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = fillStep val s := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hs'
  show n - (s.1 + 1) < n - s.1
  omega

/-! ## 3. The synthesis (D6-P6-3)

Six owned conjuncts: the index cell (junk — the program zeroes it,
P6/D-n), the array, the fill value, the static length, and the constants
`0` and `1` the `const` and the increment need. -/

/-- **The abstract implementation**: zero the index, bundle it with the
array into the loop state, then loop. -/
noncomputable def fillProg (val : ℕ) (xs : List ℕ) : NRest (ℕ × List ℕ) ECost :=
  NRest.bindT (mopConstN 0) fun z =>
    NRest.bindT (mopPair z xs) fun s₀ =>
      irWhileIT (fillI xs.length) (fillBf xs.length) (fillF val) s₀

/--
info: sepref_synth Lax13Proofs.Refine.Sepref.Iicf.fillLoop:
  (Com.const i 0).seq
    (Com.skip.seq
      (Com.while (Cond.lt (Operand.cell i) (Operand.cell n))
        ((Com.aset A i v).seq ((Com.binop Imp.Bop.add i i one).seq Com.skip))))
-/
#guard_msgs in
-- The `hv` annotation is inert since R0/D-b (`CombRules.lean`'s
-- `hnr_while` needs no variant); it is kept because `fillLoop`'s
-- signature is what §5 below and the IICF callers use.
set_option linter.unusedVariables false in
sepref_synth fillLoop (i A v one n : String) (val : ℕ) (xs : List ℕ)
    (hv : LOOP_VARIANT (fillI xs.length) (fillBf xs.length) (fillF val) (fillV xs.length)) :
  hnRefine (junkCell i ∗ hnCtxt arrayAssn xs A ∗ hnCtxt natAssn val v ∗
      hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one)
    _ _ (i, A) (natAssn ×ₐ arrayAssn)
    (fillProg val xs)

/-! ## 4. The closed form (P6/D-j)

The loop's *value*, by induction on the iterations left to run. `filled j
val xs` (P6/D-l) is the array after `j` writes, so the loop's state at
step `j` is exactly `(j, filled j val xs)` and the induction step is
`filled_set`. -/

/-- What the loop still owes at index `j`: one step per remaining write,
one guard evaluation per remaining iteration plus the exit's. -/
noncomputable def fillRest (n j : ℕ) : ECost :=
  (n - j) • fillStepCost + (n - j + 1) • irUnit Currency.«while»

theorem fillLoop_value (val n : ℕ) (xs : List ℕ) (hlen : xs.length = n) :
    ∀ (m j : ℕ), n - j ≤ m → j ≤ n →
      irWhileIT (fillI n) (fillBf n) (fillF val) (j, filled j val xs)
        = NRest.consume (NRest.returnT (n, filled n val xs)) (fillRest n j) := by
  intro m
  induction m with
  | zero =>
    intro j hm hj
    have hI : fillI n (j, filled j val xs) := by
      show (filled j val xs).length = n
      rw [Ir.Examples.filled_length j val xs (by omega), hlen]
    have hjn : j = n := by omega
    have hb : fillBf n (j, filled j val xs) = false := by
      simp only [fillBf, decide_eq_false_iff_not, not_lt]; omega
    rw [irWhileIT_of_false hI hb, hjn]
    congr 1
    simp [fillRest]
  | succ m ih =>
    intro j hm hj
    have hI : fillI n (j, filled j val xs) := by
      show (filled j val xs).length = n
      rw [Ir.Examples.filled_length j val xs (by omega), hlen]
    by_cases hjn : j = n
    · have hb : fillBf n (j, filled j val xs) = false := by
        simp only [fillBf, decide_eq_false_iff_not, not_lt]; omega
      rw [irWhileIT_of_false hI hb, hjn]
      congr 1
      simp [fillRest]
    · have hjlt : j < n := by omega
      have hb : fillBf n (j, filled j val xs) = true := by
        simp only [fillBf, decide_eq_true_eq]; omega
      have hidx : j < (filled j val xs).length := by
        rw [Ir.Examples.filled_length j val xs (by omega), hlen]; exact hjlt
      have hstep : fillStep val (j, filled j val xs) = (j + 1, filled (j + 1) val xs) := by
        show (j + 1, (filled j val xs).set j val) = _
        rw [Ir.Examples.filled_set j val xs (by omega)]
      rw [irWhileIT_of_true hI hb, fillF_eq val _ hidx, hstep, bindT_unit,
        ih (j + 1) (by omega) (by omega), NRest.consume_consume, NRest.consume_consume]
      congr 1
      have hd : n - j = (n - (j + 1)) + 1 := by omega
      simp only [fillRest, hd, succ_nsmul]
      abel

/-! ## 5. The interface op and its rule (D6-P6-1, D6-P6-3)

The cost is not designed, it is *read off*: `fillCost` is what the
pipeline spent — one `ir.const` to zero the index (P6/D-n), one `ir.skip`
to bundle the loop state, then per entry a write, an increment and the
tuple, and one `ir.while` per guard evaluation. -/

/-- **The interface op's price**, linear in the array's length. -/
noncomputable def fillCost (n : ℕ) : ECost :=
  irUnit Currency.const + irUnit Currency.skip +
    (n • fillStepCost + (n + 1) • irUnit Currency.«while»)

/-- **The interface op** (design record: "the P3 fill loop as one op,
cost linear"). -/
noncomputable def mop_array_fill (xs : List ℕ) (val : ℕ) : NRest (List ℕ) ECost :=
  NRest.consume (NRest.returnT (List.replicate xs.length val)) (fillCost xs.length)

theorem mop_array_fill_def (xs : List ℕ) (val : ℕ) :
    mop_array_fill xs val
      = NRest.consume (NRest.returnT (List.replicate xs.length val)) (fillCost xs.length) := rfl

/-- The compound program `sepref_synth` produced in §3, named. -/
def fillCom (i A v one n : String) : Com :=
  .seq (.const i 0)
    (.seq .skip
      (.while (.lt (.cell i) (.cell n))
        (.seq (.aset A i v) (.seq (.binop .add i i one) .skip))))

/-- The synthesized program's abstract side, in closed form. -/
theorem fillProg_value (val : ℕ) (xs : List ℕ) :
    fillProg val xs
      = NRest.consume (NRest.returnT (xs.length, List.replicate xs.length val))
          (fillCost xs.length) := by
  have h := fillLoop_value val xs.length xs rfl xs.length 0 (by omega) (by omega)
  rw [Ir.Examples.filled_zero, Ir.Examples.filled_all xs.length val xs (le_refl _)] at h
  show NRest.bindT (mopConstN 0) _ = _
  rw [mopConstN_def, bindT_unit, mopPair_def, bindT_unit, h,
    NRest.consume_consume, NRest.consume_consume]
  congr 1

/-- **The registered rule** (design D6-P6-3): one interface op, one hnr
rule, at caller-chosen cell names. Everything about the implementation —
the loop, the scratch index, the two constants — is behind it. -/
@[sepref_fr_rules]
theorem hnr_mop_array_fill (i A v one n : String) (val : ℕ) (xs : List ℕ) :
    hnRefine (junkCell i ∗ hnCtxt arrayAssn xs A ∗ hnCtxt natAssn val v ∗
        hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one)
      (fillCom i A v one n)
      (junkCell i ∗ hnCtxt natAssn val v ∗ hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one)
      A arrayAssn (mop_array_fill xs val) := by
  have h := fillLoop i A v one n val xs (fill_variant xs.length val)
  rw [fillProg_value] at h
  refine hnRefine_res_cast' h ?_
  have e : ((hnCtxt natAssn val v ∗ hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one) ∗
        (natAssn ×ₐ arrayAssn) (xs.length, List.replicate xs.length val) (i, A))
      = ((natAssn xs.length i ∗
            (hnCtxt natAssn val v ∗ hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one)) ∗
          arrayAssn (List.replicate xs.length val) A) := by
    show ((hnCtxt natAssn val v ∗ hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one) ∗
        (natAssn xs.length i ∗ arrayAssn (List.replicate xs.length val) A)) = _
    ac_rfl
  rw [e]
  exact conj_entails_mono
    (conj_entails_mono (natAssn_entails_junkCell _ i) (entails_refl _)) (entails_refl _)

/-- The release entailment (§2 of `Iicf/Basic.lean`): a filled array is
capacity-fixed junk again. -/
theorem mop_array_fill_release (val : ℕ) (xs : List ℕ) (A : String) :
    arrayAssn (List.replicate xs.length val) A ⊢ junkArrayOfLen xs.length A :=
  arrayAssn_entails_junkArrayOfLen' _ A (by simp)

/-! ## 6. The cost, pinned

What the pipeline spent, per currency, at a concrete length — the
design record's "`#guard`-style checks where computable". `decide
+kernel` rather than `decide`: the currencies are strings and the
elaborator's `Decidable` evaluation is quadratic in the chain, the
kernel's is not. -/

theorem fillCost_aset : (fillCost 3).toFun Currency.aset = 3 := by decide +kernel
theorem fillCost_add : (fillCost 3).toFun Currency.add = 3 := by decide +kernel
theorem fillCost_while : (fillCost 3).toFun Currency.«while» = 4 := by decide +kernel
theorem fillCost_const : (fillCost 3).toFun Currency.const = 1 := by decide +kernel
theorem fillCost_skip : (fillCost 3).toFun Currency.skip = 4 := by decide +kernel

/-- The op touches no other currency: it never reads. -/
theorem fillCost_aget : (fillCost 3).toFun Currency.aget = 0 := by decide +kernel

-- **Negative control.** The pipeline did not spend four writes on three
-- entries, and the pin says so.
/-- error: Tactic `decide` proved that the proposition
  (fillCost 3).toFun Currency.aset = 4
is false -/
#guard_msgs in
example : (fillCost 3).toFun Currency.aset = 4 := by decide +kernel

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_mop_array_fill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_array_fill

end Iicf

end Lax13Proofs.Refine.Sepref
