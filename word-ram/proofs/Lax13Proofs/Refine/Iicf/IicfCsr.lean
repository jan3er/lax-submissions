import Lax13Proofs.Refine.Iicf.IicfStack

/-!
# IICF: CSR graphs over two fixed arrays — the thin instance

Structure 5 of `plans/word-ram/refinement-tower/p6-iicf-design.md`, and
the design record calls it **thin**: the abstract value is the pair of
lists `(off, tgt)` itself, the CSR well-formedness is a *pure conjunct*
of the assertion, and row iteration is a plain abstract `while` loop.
`FOREACH` is unported backlog (design D6-P6-7) and nothing here needs it.

The wave's shared bridges come from `IicfStack.lean` (flag `P6/D-ba`
there).

## Judgment calls (continuing `IicfQueue.lean`'s P6/D-bh … P6/D-bj)

**P6/D-bk — CSR needs no representation existential, so it needs no
reinterpretation either.** The abstract value *is* the concrete pair of
lists, so `csrAssn n g d = ⌜CsrWf n g⌝ ∗ (arrayAssn ×ₐ arrayAssn) g d` —
a pure conjunct over a `prodAssn`, no `∃ᵃ`. Consequently the three
operations are derived from their synthesized raw theorems with
`hnRefine_abs_cong` (the abstract programs agree once the interface's
`assert` is discharged) and *no* `hnRefine_reinterp`: nothing changes
type. All three are read-only, so the structure does not move into the
result slot — it is reassembled in the postcondition instead, which is
where `CsrWf` comes back in as `□` (`predLift_of_true`).

**P6/D-bl — `rowEnd` is a two-op composite because the IR has no
immediate operands.** `off[v+1]` needs `v+1` in a cell, so `rowEnd` is
`tmp := i + one; r := off[tmp]` — one `ir.add` and one `ir.aget`. Its
rule therefore asks the caller for *two* scratch cells, and the caller
must list them in consumption order (`tmp` before `r`), for the greedy
allocation reason recorded in `IicfStack.lean`'s P6/D-be. The fallback —
a `mop_off_at` taking the index directly, of which `rowStart v` and
`rowEnd v` are the instances at `v` and `v+1` — would be one op and one
scratch cell, but would push the `+1` onto every caller.

**P6/D-bm — row iteration is an ordinary abstract loop** (design
D6-P6-7). The exercise below walks one vertex's slots with
`hnr_while_var` and the primitive `condRefine_lt_cells`; the CSR
structure sits in the *loop frame*, read-only, and is never split. This
is the whole reason the thin design works: a read-only composite never
has to be taken apart by the frame matcher.
-/

namespace Lax13Proofs.Refine.Iicf

open Sepref Ir NRest

/-! ## 1. The CSR assertion (P6/D-bk) -/

/-- CSR well-formedness: `off` has one entry per vertex plus the
sentinel, the offsets are monotone, the sentinel is the slot count, and
every target is a vertex. -/
def CsrWf (n : ℕ) (g : List ℕ × List ℕ) : Prop :=
  g.1.length = n + 1 ∧ (∀ i, i < n → g.1[i]! ≤ g.1[i + 1]!) ∧ g.1[n]! = g.2.length ∧
    ∀ k, k < g.2.length → g.2[k]! < n

/-- The composite assertion: the offset array at `d.1`, the target array
at `d.2`, and the well-formedness as a pure conjunct. -/
def csrAssn (n : ℕ) : List ℕ × List ℕ → String × String → Assn := fun g d =>
  ⌜CsrWf n g⌝ ∗ ((arrayAssn ×ₐ arrayAssn) g d)

/-- The unfold lemma (definitional). -/
theorem csrAssn_unfold (n : ℕ) (g : List ℕ × List ℕ) (d : String × String) :
    hnCtxt (csrAssn n) g d
      = ⌜CsrWf n g⌝ ∗ (hnCtxt arrayAssn g.1 d.1 ∗ hnCtxt arrayAssn g.2 d.2) := rfl

/-- Closing the composite: two arrays plus the invariant. -/
theorem csrAssn_intro (n : ℕ) (g : List ℕ × List ℕ) (d : String × String) (hwf : CsrWf n g) :
    (hnCtxt arrayAssn g.1 d.1 ∗ hnCtxt arrayAssn g.2 d.2) ⊢ hnCtxt (csrAssn n) g d :=
  fun _ hh => predLift_sepConj_iff.2 ⟨hwf, hh⟩

/-- Opening the composite in a precondition. -/
theorem csr_pre {n : ℕ} {g : List ℕ × List ℕ} {dC : String × String} {Γ Γ' : Assn} {c : Com}
    {α κ : Type} {d : κ} {R : α → κ → Assn} {m : NRest α ECost}
    (h : CsrWf n g →
      hnRefine ((hnCtxt arrayAssn g.1 dC.1 ∗ hnCtxt arrayAssn g.2 dC.2) ∗ Γ) c Γ' d R m) :
    hnRefine (hnCtxt (csrAssn n) g dC ∗ Γ) c Γ' d R m :=
  hnr_pre_pure_star h

/-- **Establishment from junk**: two arrays that happen to satisfy
`CsrWf` are a CSR graph. There is no `*_new` (design D6-P6-2). -/
theorem csrAssn_init (n : ℕ) (g : List ℕ × List ℕ) (d : String × String) (hwf : CsrWf n g) :
    (hnCtxt arrayAssn g.1 d.1 ∗ hnCtxt arrayAssn g.2 d.2) ⊢ hnCtxt (csrAssn n) g d :=
  csrAssn_intro n g d hwf

/-- **Release to junk.** -/
theorem csrAssn_release (n : ℕ) (g : List ℕ × List ℕ) (d : String × String) :
    hnCtxt (csrAssn n) g d ⊢ junkArray d.1 ∗ junkArray d.2 := by
  intro h hh
  obtain ⟨-, hh⟩ := predLift_sepConj_iff.1 hh
  exact conj_entails_mono (arrayAssn_entails_junkArray g.1 d.1)
    (arrayAssn_entails_junkArray g.2 d.2) h hh

/-- The two index bounds every operation needs, off `CsrWf`. -/
theorem CsrWf.rowStart_lt {n : ℕ} {g : List ℕ × List ℕ} (h : CsrWf n g) {v : ℕ} (hv : v < n) :
    v < g.1.length := by rw [h.1]; omega

theorem CsrWf.rowEnd_lt {n : ℕ} {g : List ℕ × List ℕ} (h : CsrWf n g) {v : ℕ} (hv : v < n) :
    v + 1 < g.1.length := by rw [h.1]; omega

/-! ## 2. Refute before prove

A concrete four-vertex graph, its well-formedness decided, and the row
walks the exercise of §6 performs — all executed before anything is
proved. -/

/-- `CsrWf`, decided. -/
def csrWfTwin (n : ℕ) (off tgt : List ℕ) : Bool :=
  decide (off.length = n + 1) && decide (∀ i, i < n → off[i]! ≤ off[i + 1]!) &&
    decide (off[n]! = tgt.length) && decide (∀ k, k < tgt.length → tgt[k]! < n)

/-- A four-vertex graph: `0 → 1, 2`, `1 → 2`, `2 → 0, 1, 3`, `3 → ∅`. -/
def gOff : List ℕ := [0, 2, 3, 6, 6]

/-- …and its target array. -/
def gTgt : List ℕ := [1, 2, 2, 0, 1, 3]

#guard csrWfTwin 4 gOff gTgt = true

/-- The abstract row bounds and the slot reader, as twins. -/
def rowStartTwin (off : List ℕ) (v : ℕ) : ℕ := off[v]!
def rowEndTwin (off : List ℕ) (v : ℕ) : ℕ := off[v + 1]!
def slotTwin (tgt : List ℕ) (k : ℕ) : ℕ := tgt[k]!

/-- The degree of a vertex: the width of its slot range. -/
def degTwin (off : List ℕ) (v : ℕ) : ℕ := rowEndTwin off v - rowStartTwin off v

#guard degTwin gOff 0 = 2
#guard degTwin gOff 1 = 1
#guard degTwin gOff 2 = 3
#guard degTwin gOff 3 = 0
#guard (List.range 4).map (degTwin gOff) = [2, 1, 3, 0]
-- The degrees sum to the slot count — the CSR consistency check.
#guard ((List.range 4).map (degTwin gOff)).sum = gTgt.length

/-- The row walk of §6's exercise: sum the targets of one row. -/
def walkRun (tgt : List ℕ) (e : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, st => st
  | m + 1, st => if st.1 < e then walkRun tgt e m (st.1 + 1, st.2 + slotTwin tgt st.1) else st

/-- …started at a vertex's row. -/
def rowSum (off tgt : List ℕ) (v : ℕ) : ℕ :=
  (walkRun tgt (rowEndTwin off v) tgt.length (rowStartTwin off v, 0)).2

#guard rowSum gOff gTgt 0 = 3
#guard rowSum gOff gTgt 1 = 2
#guard rowSum gOff gTgt 2 = 4
#guard rowSum gOff gTgt 3 = 0
-- …and against an independent decider of the same quantity.
#guard rowSum gOff gTgt 2 = ((gTgt.drop (gOff[2]!)).take (gOff[3]! - gOff[2]!)).sum
#guard rowSum gOff gTgt 0 = ((gTgt.take 2).sum)

-- **Negative control 1.** A non-monotone offset array is not CSR.
/--
error: Expression
  decide (csrWfTwin 4 [0, 2, 1, 6, 6] gTgt = true)
did not evaluate to `true`
-/
#guard_msgs in
#guard csrWfTwin 4 ([0, 2, 1, 6, 6] : List ℕ) gTgt = true

-- **Negative control 2.** A target out of vertex range is not CSR.
/--
error: Expression
  decide (csrWfTwin 4 gOff [1, 2, 2, 0, 1, 4] = true)
did not evaluate to `true`
-/
#guard_msgs in
#guard csrWfTwin 4 gOff ([1, 2, 2, 0, 1, 4] : List ℕ) = true

/-! ## 3. The interface operations (design D6-P6-1) -/

/-- `rowStart`: one array read. -/
noncomputable def rowStartCost : ECost := irUnit Currency.aget

/-- `rowEnd`: an increment and an array read (P6/D-bl). -/
noncomputable def rowEndCost : ECost := irUnit Currency.add + irUnit Currency.aget

/-- `slotTarget`: one array read. -/
noncomputable def slotTargetCost : ECost := irUnit Currency.aget

/-- The first slot index of vertex `v`'s row. -/
noncomputable def mopRowStart (n : ℕ) (g : List ℕ × List ℕ) (v : ℕ) : NRest ℕ ECost :=
  NRest.bindT (NRest.assert (v < n)) fun _ =>
    NRest.consume (NRest.returnT g.1[v]!) rowStartCost

/-- One past the last slot index of vertex `v`'s row. -/
noncomputable def mopRowEnd (n : ℕ) (g : List ℕ × List ℕ) (v : ℕ) : NRest ℕ ECost :=
  NRest.bindT (NRest.assert (v < n)) fun _ =>
    NRest.consume (NRest.returnT g.1[v + 1]!) rowEndCost

/-- The target stored in slot `k`. -/
noncomputable def mopSlotTarget (g : List ℕ × List ℕ) (k : ℕ) : NRest ℕ ECost :=
  NRest.bindT (NRest.assert (k < g.2.length)) fun _ =>
    NRest.consume (NRest.returnT g.2[k]!) slotTargetCost

theorem mopRowStart_def (n : ℕ) (g : List ℕ × List ℕ) (v : ℕ) :
    mopRowStart n g v = NRest.bindT (NRest.assert (v < n)) fun _ =>
      NRest.consume (NRest.returnT g.1[v]!) rowStartCost := rfl

theorem mopRowEnd_def (n : ℕ) (g : List ℕ × List ℕ) (v : ℕ) :
    mopRowEnd n g v = NRest.bindT (NRest.assert (v < n)) fun _ =>
      NRest.consume (NRest.returnT g.1[v + 1]!) rowEndCost := rfl

theorem mopSlotTarget_def (g : List ℕ × List ℕ) (k : ℕ) :
    mopSlotTarget g k = NRest.bindT (NRest.assert (k < g.2.length)) fun _ =>
      NRest.consume (NRest.returnT g.2[k]!) slotTargetCost := rfl

/-! ## 4. The raw chains and their synthesis (P6/D-bc, P6/D-bl) -/

/-- The raw chain `rowEnd` expands to: bump, read. -/
noncomputable def rowEndRaw (off : List ℕ) (v : ℕ) : NRest ℕ ECost :=
  NRest.bindT (mopBinop .add v 1) fun j => mopAget off j

theorem rowEndRaw_eq (off : List ℕ) (v : ℕ) (h : v + 1 < off.length) :
    rowEndRaw off v = NRest.consume (NRest.returnT off[v + 1]!) rowEndCost := by
  show NRest.bindT (mopBinop .add v 1) _ = _
  rw [mopBinop_def, bindT_unit]
  simp only [Imp.Bop.apply_add, binopCurrency_add]
  rw [mopAget_def, NRest.assert_pos h, NRest.returnT_bindT, NRest.consume_consume]
  simp only [rowEndCost]

/-- The program `rowStart` compiles to. -/
def rowStartCom (O i r : String) : Com := .aget r O i

/-- The program `rowEnd` compiles to (P6/D-bl). -/
def rowEndCom (O i tmp r one : String) : Com := .seq (.binop .add tmp i one) (.aget r O tmp)

/-- The program `slotTarget` compiles to. -/
def slotTargetCom (T k r : String) : Com := .aget r T k

#guard rowStartCom "O" "v" "s" = Com.aget "s" "O" "v"
#guard rowEndCom "O" "v" "t" "e" "one" =
  Com.seq (Com.binop Imp.Bop.add "t" "v" "one") (Com.aget "e" "O" "t")
#guard slotTargetCom "T" "k" "w" = Com.aget "w" "T" "k"

sepref_synth csrAgetSynth (O i r : String) (off : List ℕ) (v : ℕ) :
  hnRefine (hnCtxt arrayAssn off O ∗ junkCell r ∗ hnCtxt natAssn v i)
    _ _ r natAssn (mopAget off v)

sepref_synth rowEndSynth (O i tmp r one : String) (off : List ℕ) (v : ℕ) :
  hnRefine (hnCtxt arrayAssn off O ∗ junkCell tmp ∗ junkCell r ∗ hnCtxt natAssn v i ∗
      hnCtxt natAssn 1 one)
    _ _ r natAssn (rowEndRaw off v)

/-! ## 5. The composite rules (P6/D-bk)

Three read-only operations. Each is the synthesized raw theorem with its
`assert` discharged (`hnRefine_abs_cong`), the *other* array framed
(`hnRefine_frame_perm`) and the structure reassembled in the
postcondition, where `CsrWf` returns as `□`. No `hnRefine_reinterp`:
nothing changes type. -/

@[sepref_fr_rules]
theorem hnr_mop_rowStart (n : ℕ) (g : List ℕ × List ℕ) (v : ℕ) (O T i r : String) :
    hnRefine (hnCtxt (csrAssn n) g (O, T) ∗ junkCell r ∗ hnCtxt natAssn v i)
      (rowStartCom O i r) (hnCtxt (csrAssn n) g (O, T) ∗ hnCtxt natAssn v i) r natAssn
      (mopRowStart n g v) := by
  rw [mopRowStart_def]
  refine hnr_assert fun hv => ?_
  refine csr_pre fun hwf => ?_
  have hb := hwf.rowStart_lt hv
  have hsyn := hnRefine_abs_cong
    (show NRest.consume (NRest.returnT g.1[v]!) rowStartCost = mopAget g.1 v from by
      rw [mopAget_def, NRest.assert_pos hb, NRest.returnT_bindT]; rfl)
    (csrAgetSynth O i r g.1 v)
  refine hnRefine_cons_post
    (hnRefine_frame_perm (F := hnCtxt arrayAssn g.2 T) (by ac_rfl) hsyn) ?_
  rw [csrAssn_unfold, predLift_of_true hwf, emp_sepConj]
  fri

@[sepref_fr_rules]
theorem hnr_mop_slotTarget (n : ℕ) (g : List ℕ × List ℕ) (k : ℕ) (O T kc r : String) :
    hnRefine (hnCtxt (csrAssn n) g (O, T) ∗ junkCell r ∗ hnCtxt natAssn k kc)
      (slotTargetCom T kc r) (hnCtxt (csrAssn n) g (O, T) ∗ hnCtxt natAssn k kc) r natAssn
      (mopSlotTarget g k) := by
  rw [mopSlotTarget_def]
  refine hnr_assert fun hk => ?_
  refine csr_pre fun hwf => ?_
  have hsyn := hnRefine_abs_cong
    (show NRest.consume (NRest.returnT g.2[k]!) slotTargetCost = mopAget g.2 k from by
      rw [mopAget_def, NRest.assert_pos hk, NRest.returnT_bindT]; rfl)
    (csrAgetSynth T kc r g.2 k)
  refine hnRefine_cons_post
    (hnRefine_frame_perm (F := hnCtxt arrayAssn g.1 O) (by ac_rfl) hsyn) ?_
  rw [csrAssn_unfold, predLift_of_true hwf, emp_sepConj]
  fri

@[sepref_fr_rules]
theorem hnr_mop_rowEnd (n : ℕ) (g : List ℕ × List ℕ) (v : ℕ) (O T i tmp r one : String) :
    hnRefine (hnCtxt (csrAssn n) g (O, T) ∗ junkCell tmp ∗ junkCell r ∗
        hnCtxt natAssn v i ∗ hnCtxt natAssn 1 one)
      (rowEndCom O i tmp r one)
      (junkCell tmp ∗ hnCtxt (csrAssn n) g (O, T) ∗ hnCtxt natAssn v i ∗
        hnCtxt natAssn 1 one)
      r natAssn (mopRowEnd n g v) := by
  rw [mopRowEnd_def]
  refine hnr_assert fun hv => ?_
  refine csr_pre fun hwf => ?_
  have hb := hwf.rowEnd_lt hv
  have hsyn := hnRefine_abs_cong (rowEndRaw_eq g.1 v hb).symm (rowEndSynth O i tmp r one g.1 v)
  refine hnRefine_cons_post
    (hnRefine_frame_perm (F := hnCtxt arrayAssn g.2 T) (by ac_rfl) hsyn) ?_
  rw [csrAssn_unfold, predLift_of_true hwf, emp_sepConj]
  fri

/-! ## 6. Exercise: one row's degree and slot walk (P6/D-bm)

Two programs through `sepref_synth`, consuming only the rules of §5 and
P4's own primitives — no bespoke tactic, no hand-written frame clause.
The first is straight-line (`deg := off[v+1] - off[v]`); the second is
the row walk, an ordinary abstract `while` loop with the CSR structure
sitting **read-only in the loop frame**, never split. -/

namespace CsrExercise

/-! ### The degree of one vertex, straight-line

Four scratch cells, listed in consumption order (P6/D-bl): `rowStart`
takes `s`, `rowEnd` takes `t` for its `+1` and `e` for its read, and the
subtraction takes `deg`. -/

sepref_synth csrDegree (n : ℕ) (g : List ℕ × List ℕ) (v : ℕ) :
  hnRefine (hnCtxt (csrAssn n) g ("O", "T") ∗ junkCell "s" ∗ junkCell "t" ∗ junkCell "e" ∗
      junkCell "deg" ∗ hnCtxt natAssn v "v" ∗ hnCtxt natAssn 1 "one")
    _ _ "deg" natAssn
    (NRest.bindT (mopRowStart n g v) fun a =>
      NRest.bindT (mopRowEnd n g v) fun b => mopBinop .sub b a)

#guard csrDegree_impl =
  Com.seq (Com.aget "s" "O" "v")
    (Com.seq (Com.seq (Com.binop Imp.Bop.add "t" "v" "one") (Com.aget "e" "O" "t"))
      (Com.binop Imp.Bop.sub "deg" "e" "s"))

/-! ### The row walk -/

/-- No invariant is needed: the guard plus `e ≤ |tgt|` give
`slotTarget`'s bound, and `e ≤ |tgt|` is a hypothesis of the variant
lemma rather than of the loop. -/
def walkI : ℕ × ℕ → Prop := fun _ => True

/-- The guard: `k < e`. -/
def walkBf (e : ℕ) : ℕ × ℕ → Bool := fun st => decide (st.1 < e)

/-- The body: read the slot, accumulate, advance. -/
noncomputable def walkF (g : List ℕ × List ℕ) : ℕ × ℕ → NRest (ℕ × ℕ) ECost := fun st =>
  NRest.bindT (mopSlotTarget g st.1) fun w =>
    NRest.bindT (mopBinop .add st.2 w) fun acc' =>
      NRest.bindT (mopBinop .add st.1 1) fun k' => mopPair k' acc'

/-- One iteration's price: a slot read, two additions and the tuple. -/
noncomputable def walkCost : ECost :=
  slotTargetCost + irUnit Currency.add + irUnit Currency.add + irUnit Currency.skip

theorem walkF_eq (g : List ℕ × List ℕ) (st : ℕ × ℕ) (h : st.1 < g.2.length) :
    walkF g st
      = NRest.consume (NRest.returnT (st.1 + 1, st.2 + g.2[st.1]!)) walkCost := by
  show NRest.bindT (mopSlotTarget g st.1) _ = _
  rw [mopSlotTarget_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, mopBinop_def,
    bindT_unit, mopBinop_def, bindT_unit, mopPair_def, NRest.consume_consume,
    NRest.consume_consume, NRest.consume_consume]
  simp only [walkCost, Imp.Bop.apply_add, binopCurrency_add]

theorem walk_variant (g : List ℕ × List ℕ) (e : ℕ) (he : e ≤ g.2.length) :
    LOOP_VARIANT walkI (walkBf e) (walkF g) (fun st => e - st.1) := by
  intro st st' _ hb hle
  have hb' : st.1 < e := by simpa [walkBf] using hb
  have hlt : st.1 < g.2.length := by omega
  rw [walkF_eq g st hlt, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hst : st' = (st.1 + 1, st.2 + g.2[st.1]!) := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hst
  show e - (st.1 + 1) < e - st.1
  omega

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth csrRowWalk (n : ℕ) (g : List ℕ × List ℕ) (e s₀ : ℕ)
    (hv : LOOP_VARIANT walkI (walkBf e) (walkF g) (fun st => e - st.1)) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn) (s₀, 0) ("k", "acc") ∗ junkCell "w" ∗
      hnCtxt (csrAssn n) g ("O", "T") ∗ hnCtxt natAssn e "e" ∗ hnCtxt natAssn 1 "one")
    _ _ ("k", "acc") (natAssn ×ₐ natAssn)
    (irWhileIT walkI (walkBf e) (walkF g) (s₀, 0))

#guard csrRowWalk_impl =
  Com.while (Cond.lt (Operand.cell "k") (Operand.cell "e"))
    (Com.seq (Com.aget "w" "T" "k")
      (Com.seq (Com.binop Imp.Bop.add "acc" "acc" "w")
        (Com.seq (Com.binop Imp.Bop.add "k" "k" "one") Com.skip)))

/-- The row walk with its variant discharged. -/
theorem csrRowWalk' (n : ℕ) (g : List ℕ × List ℕ) (e s₀ : ℕ) (he : e ≤ g.2.length) :
    hnRefine (hnCtxt (natAssn ×ₐ natAssn) (s₀, 0) ("k", "acc") ∗ junkCell "w" ∗
        hnCtxt (csrAssn n) g ("O", "T") ∗ hnCtxt natAssn e "e" ∗ hnCtxt natAssn 1 "one")
      csrRowWalk_impl (junkCell "w" ∗ hnCtxt (csrAssn n) g ("O", "T") ∗
        hnCtxt natAssn e "e" ∗ hnCtxt natAssn 1 "one") ("k", "acc") (natAssn ×ₐ natAssn)
      (irWhileIT walkI (walkBf e) (walkF g) (s₀, 0)) :=
  csrRowWalk n g e s₀ (walk_variant g e he)

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_rowStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_rowStart

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_rowEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_rowEnd

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_slotTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_slotTarget

/-- info: 'Lax13Proofs.Refine.Iicf.CsrExercise.csrDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms csrDegree

/-- info: 'Lax13Proofs.Refine.Iicf.CsrExercise.csrRowWalk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms csrRowWalk'

end CsrExercise

end Lax13Proofs.Refine.Iicf
