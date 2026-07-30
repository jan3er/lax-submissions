import Lax13Proofs.Refine.Iicf.IicfTrailArray

/-!
# P6 wave A acceptance — the exercises

The design record's acceptance criterion for a structure is: *an exercise
program written at the abstract layer and pushed through `sepref`
mechanically — zero bespoke tactics, zero hand frame clauses*. This file
is the two wave-A exercises, and the telemetry (§3) is the count.

* **Arrays** (§1): an in-place pass — fill the array with a constant,
  read a slot, bump it, write it back — consuming `mop_array_fill`'s
  registered rule together with the primitive `aget`/`aset`.
* **Trail arrays** (§2): write–reset–reuse across two rounds, with the
  round-2 reset's cost read off the round-2 touch counter and pinned
  against the array's length.

Neither program mentions an assertion, a frame, a cell permutation, a
`Com`, or a cost: they are `do`-blocks over the interface ops, and one
`sepref_synth` line each.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

namespace Iicf

namespace ExercisesA

/-! ## 1. Arrays — an in-place pass

`A := replicate n c; A[0] := A[0] + 1`. Three interface ops, one of them
the compound `mop_array_fill` of `Iicf/IicfArray.lean`. -/

/-! ### Refute before prove -/

/-- The computable twin of what the pass computes. -/
def bumpOut (xs : List ℕ) (c : ℕ) : List ℕ := (List.replicate xs.length c).set 0 (c + 1)

#guard bumpOut [9, 9, 9] 0 = [1, 0, 0]
#guard bumpOut [9, 9, 9] 4 = [5, 4, 4]
#guard bumpOut [7] 0 = [1]
#guard bumpOut ([] : List ℕ) 0 = []

-- **Negative control.** The pass bumps the *first* slot, not the last.
/--
error: Expression
  decide (bumpOut [9, 9, 9] 0 = [0, 0, 1])
did not evaluate to `true`
-/
#guard_msgs in
#guard bumpOut [9, 9, 9] 0 = [0, 0, 1]

/-! ### The program, and its synthesis -/

/-- **The exercise, at the abstract layer.** Nothing here is concrete:
`xs` is a list, `mop_array_fill` is an interface op, and the two
primitives are the ones `Sepref/IrOps.lean` supplies. -/
noncomputable def bumpProg (xs : List ℕ) : NRest (List ℕ) ECost :=
  NRest.bindT (mop_array_fill xs 0) fun ys =>
    NRest.bindT (mopAget ys 0) fun a =>
      NRest.bindT (mopBinop .add a 1) fun b => mopAset ys 0 b

-- The whole exercise: one command. The cell `"z"` holds `0` and does
-- double duty as the fill's value and the read's index; `"i"` is the
-- only scratch, reused by the fill's loop index and the read's
-- destination.
/--
info: sepref_synth Lax13Proofs.Refine.Sepref.Iicf.ExercisesA.bumpSynth:
  (fillCom "i" "A" "z" "one" "n").seq
    ((Com.aget "i" "A" "z").seq ((Com.binop Imp.Bop.add "i" "i" "one").seq (Com.aset "A" "z" "i")))
-/
#guard_msgs in
sepref_synth bumpSynth (xs : List ℕ) :
  hnRefine (hnCtxt arrayAssn xs "A" ∗ junkCell "i" ∗ hnCtxt natAssn 0 "z" ∗
      hnCtxt natAssn xs.length "n" ∗ hnCtxt natAssn 1 "one")
    _ _ "A" arrayAssn
    (bumpProg xs)

/-- The pass's price: the fill, a read, an increment, a write. -/
noncomputable def bumpCost (n : ℕ) : ECost :=
  fillCost n + irUnit Currency.aget + irUnit Currency.add + irUnit Currency.aset

/-- **What the exercise computes and what it costs**, in closed form —
the `bumpOut` twin above, at `bumpCost`. -/
theorem bumpProg_value (xs : List ℕ) (h : 0 < xs.length) :
    bumpProg xs
      = NRest.consume (NRest.returnT (bumpOut xs 0)) (bumpCost xs.length) := by
  have h1 : 0 < (List.replicate xs.length 0).length := by simpa using h
  show NRest.bindT (mop_array_fill xs 0) _ = _
  rw [mop_array_fill_def, bindT_unit, mopAget_def, NRest.assert_pos h1, NRest.returnT_bindT,
    bindT_unit, mopBinop_def, bindT_unit, mopAset_def, NRest.assert_pos h1,
    NRest.returnT_bindT, NRest.consume_consume, NRest.consume_consume, NRest.consume_consume]
  have h2 : (List.replicate xs.length 0)[0]! = 0 := by
    rw [getElem!_pos _ 0 h1]; simp
  simp only [bumpOut, bumpCost, Imp.Bop.apply_add, binopCurrency_add, h2]

theorem bumpCost_aget : (bumpCost 3).toFun Currency.aget = 1 := by decide +kernel
theorem bumpCost_aset : (bumpCost 3).toFun Currency.aset = 4 := by decide +kernel
theorem bumpCost_while : (bumpCost 3).toFun Currency.«while» = 4 := by decide +kernel

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.ExercisesA.bumpSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bumpSynth

/-! ## 2. Trail arrays — write, reset, reuse

Two rounds over one trail array: three writes and a reset, then two
writes and a reset. The point of the exercise is the *second* reset:
its price is `resetCost 2`, which mentions the touch counter and not the
array's length.

The two rounds use the same cells throughout — nothing is allocated,
nothing is freed, and the reset is what makes the array reusable. -/

/-- **The exercise, at the abstract layer.** `s` is a trail array's
abstract value; `i` and `j` are two slots, written in the pattern
`i, j, i` and then `j, i`. -/
noncomputable def twoRounds (dflt n : ℕ) (s : List ℕ × ℕ) (i j v : ℕ) :
    NRest (List ℕ × ℕ) ECost :=
  NRest.bindT (mop_tset n s i v) fun s₁ =>
    NRest.bindT (mop_tset n s₁ j v) fun s₂ =>
      NRest.bindT (mop_tset n s₂ i v) fun s₃ =>
        NRest.bindT (mop_treset dflt n s₃) fun s₄ =>
          NRest.bindT (mop_tset n s₄ j v) fun s₅ =>
            NRest.bindT (mop_tset n s₅ i v) fun s₆ => mop_treset dflt n s₆

/--
info: sepref_synth Lax13Proofs.Refine.Sepref.Iicf.ExercisesA.twoRoundsSynth:
  (tsetCom "A" "T" "t" "I" "V" "one").seq
    ((tsetCom "A" "T" "t" "J2" "V" "one").seq
      ((tsetCom "A" "T" "t" "I" "V" "one").seq
        ((resetCom "A" "T" "t" "P" "Q" "D" "one").seq
          ((tsetCom "A" "T" "t" "J2" "V" "one").seq
            ((tsetCom "A" "T" "t" "I" "V" "one").seq (resetCom "A" "T" "t" "P" "Q" "D" "one"))))))
-/
#guard_msgs in
sepref_synth twoRoundsSynth (dflt n : ℕ) (s : List ℕ × ℕ) (i j v : ℕ) :
  hnRefine (hnCtxt (trailAssn dflt n) s ("A", "T", "t") ∗ hnCtxt natAssn i "I" ∗
      hnCtxt natAssn j "J2" ∗ hnCtxt natAssn v "V" ∗ junkCell "P" ∗ junkCell "Q" ∗
      hnCtxt natAssn dflt "D" ∗ hnCtxt natAssn 1 "one")
    _ _ ("A", "T", "t") (trailAssn dflt n)
    (twoRounds dflt n s i j v)

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.ExercisesA.twoRoundsSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoRoundsSynth

/-! ### The touched-only reading

A computable twin of the touch counter, `#guard`ed on the two rounds,
and the bridge from it to the `ECost` the interface charges. -/

/-- What a reset pops, computably. -/
def popsOf (s : List ℕ × ℕ) : ℕ := s.2

/-- The bridge: the reset's price *is* a function of `popsOf`. -/
theorem trailResetCost_popsOf (s : List ℕ × ℕ) : trailResetCost s = resetCost (popsOf s) := rfl

/-- Round one's state, after three writes into a length-8 array. -/
def st1 : List ℕ × ℕ := ((List.replicate 8 0).set 2 5, 3)

/-- Round two's state, after two writes into the *reset* array. -/
def st2 : List ℕ × ℕ := ((List.replicate 8 0).set 6 7, 2)

-- The array is eight slots long in both rounds…
#guard st1.1.length = 8
#guard st2.1.length = 8
-- …and the resets pop three and two times, not eight.
#guard popsOf st1 = 3
#guard popsOf st2 = 2
#guard popsOf st2 < st2.1.length
#guard popsOf st2 < popsOf st1

-- **Negative control.** Reset does not pop once per slot.
/--
error: Expression
  decide (popsOf st2 = st2.1.length)
did not evaluate to `true`
-/
#guard_msgs in
#guard popsOf st2 = st2.1.length

/-- **The exercise's cost claim, round two**: two touches, two restoring
writes — in an eight-slot array. -/
theorem st2_reset_aset : (trailResetCost st2).toFun Currency.aset = 2 := by decide +kernel

/-- …and round one's, three. -/
theorem st1_reset_aset : (trailResetCost st1).toFun Currency.aset = 3 := by decide +kernel

/-- **The length does not enter.** The very same round-two state, in an
array a hundred times longer, costs the very same reset. -/
theorem st2_reset_length_free (xs : List ℕ) :
    trailResetCost (xs, 2) = trailResetCost st2 :=
  treset_cost_touched_only rfl

/-! ## 3. Telemetry (the phase's acceptance numbers)

* **Hand-written frame clauses in this file: 0.** Nothing here rewrites
  with `sepConj_assoc`, `sepConj_comm`, `ac_rfl` *on assertions*,
  `irSTATE_rot`, `fri`, `iicf_perm`, `hnRefine_pre_perm`,
  `hnRefine_frame` or `entails_of_eq`. The `∗`-lists in the two
  `sepref_synth` goals are *interface* — the cells the caller owns — and
  every permutation, split and frame that turns them into rule instances
  is inferred. The three `ac_rfl`-free `rw` chains in `bumpProg_value`
  are on `NRest` programs and `ECost` sums, not on `∗`.

* **Bespoke tactics: 0.** Two `sepref_synth` invocations, four
  `decide +kernel` cost pins, one `simp only` inside a value lemma.

* **Interface ops consumed: 5** — `mop_array_fill`, `mopAget`,
  `mopAset`, `mopBinop` (§1); `mop_tset`, `mop_treset` (§2) — of which
  three are P6 compound ops whose implementations were themselves
  synthesized (`Iicf/IicfArray.lean` §3, `Iicf/IicfTrailArray.lean` §3).

* **Axioms.** `#print axioms` is pinned above for both synthesized
  judgments: `[propext, Classical.choice, Quot.sound]` and nothing
  else. -/

end ExercisesA

end Iicf

end Lax13Proofs.Refine.Sepref
