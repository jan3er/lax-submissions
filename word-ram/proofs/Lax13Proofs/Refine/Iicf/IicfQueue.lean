import Lax13Proofs.Refine.Iicf.IicfStack

/-!
# IICF: one-shot FIFO queue over three fixed cells

Structure 4 of `plans/word-ram/refinement-tower/p6-iicf-design.md`: a
**one-shot** FIFO — no wraparound, capacity = total enqueues, the BFS
discipline (design D6-P6-6) — living in the three caller-named cells
`(Q, head, tail)`.

The wave's shared bridges (`hnRefine_reinterp`, `hnr_pre_ex_pure`,
`bindT_unit`) come from `IicfStack.lean`; see `P6/D-ba` there for why
they live in that file rather than in a `Iicf/Basic.lean` this wave may
not create.

## Judgment calls (continuing `IicfStack.lean`'s P6/D-ba … P6/D-bg)

**P6/D-bh — the abstract queue carries its head index.** The design
record says "abstract `List Val`", and for the *contents* that is what
this file has; but a one-shot queue's capacity condition is
`head + |q| < cap`, and `head` is not a function of the contents — it is
how much has already been dequeued, which the abstract layer must be able
to say if `enq`'s precondition is to be stated at the interface at all.
So the abstract type is `ℕ × List ℕ`, exactly as the design record's own
trail array is `(xs, k)` with a counter carrier. Everything else is
unchanged: `enq` appends, `deq` takes the head, and the contents are a
plain list. Fallback if a consumer wants the pure-list interface: fix
`head = 0` and the pair collapses, at the price of a `deq` that has to
shift.

**P6/D-bi — the operation order is the one P4's greedy scratch
allocation admits** (`IicfStack.lean`'s P6/D-be, same finding). `deq`
reads *before* it bumps `head`, so the scratch cell is already spent when
the in-place `binop` is translated; `enq` writes *before* it bumps
`tail`, and owns no scratch cell at all. Both orders are also the natural
ones for this layout, so nothing was distorted to fit.

**P6/D-bj — emptiness is the fused guard `head = tail`, nonemptiness
`head < tail`** (design D6-P6-6), both two-cell conditions, both
registered in `sepref_cond_rules`. Unlike the stack's `top < cap` these
mention no literal, so a queue exercise synthesizes a *closed* program
even at a symbolic capacity.
-/

namespace Lax13Proofs.Refine.Iicf

open Sepref Ir NRest

/-! ## 1. The queue assertion -/

/-- The backing array of a one-shot queue: `cap` slots, of which
`[head, head + |q|)` hold the pending elements in order. Nothing else is
constrained — the already-dequeued prefix and the not-yet-written suffix
are both hidden by the existential in `queueAssn`. -/
def QueueWf (cap h : ℕ) (q xs : List ℕ) : Prop :=
  xs.length = cap ∧ h + q.length ≤ cap ∧ (xs.drop h).take q.length = q

/-- The composite assertion: the pending list `s.2` with head index
`s.1`, at the cell triple `d = (Q, (head, tail))`. `tail` holds
`head + |q|`, which is what makes emptiness `head = tail`. -/
def queueAssn (cap : ℕ) : ℕ × List ℕ → String × String × String → Assn := fun s d =>
  ∃ᵃ xs, ⌜QueueWf cap s.1 s.2 xs⌝ ∗
    ((arrayAssn ×ₐ (natAssn ×ₐ natAssn)) (xs, (s.1, s.1 + s.2.length)) d)

/-- The unfold lemma (definitional). -/
theorem queueAssn_unfold (cap : ℕ) (s : ℕ × List ℕ) (d : String × String × String) :
    hnCtxt (queueAssn cap) s d
      = ∃ᵃ xs, ⌜QueueWf cap s.1 s.2 xs⌝ ∗
          (hnCtxt arrayAssn xs d.1 ∗
            (hnCtxt natAssn s.1 d.2.1 ∗ hnCtxt natAssn (s.1 + s.2.length) d.2.2)) := rfl

/-- Closing the composite, in the `prodAssn` spelling
`hnRefine_reinterp` hands it. -/
theorem queueAssn_intro' (cap : ℕ) (s : ℕ × List ℕ) (xs : List ℕ) (h t : ℕ)
    (d : String × String × String) (hwf : QueueWf cap s.1 s.2 xs) (hh : h = s.1)
    (ht : t = s.1 + s.2.length) :
    (arrayAssn ×ₐ (natAssn ×ₐ natAssn)) (xs, (h, t)) d ⊢ queueAssn cap s d := by
  subst hh; subst ht
  exact fun _ hx => ⟨xs, predLift_sepConj_iff.2 ⟨hwf, hx⟩⟩

/-- Opening the composite in a precondition. -/
theorem queue_pre {cap : ℕ} {s : ℕ × List ℕ} {dQ : String × String × String} {Γ Γ' : Assn}
    {c : Com} {α κ : Type} {d : κ} {R : α → κ → Assn} {m : NRest α ECost}
    (h : ∀ xs : List ℕ, QueueWf cap s.1 s.2 xs →
      hnRefine ((hnCtxt arrayAssn xs dQ.1 ∗
          (hnCtxt natAssn s.1 dQ.2.1 ∗ hnCtxt natAssn (s.1 + s.2.length) dQ.2.2)) ∗ Γ)
        c Γ' d R m) :
    hnRefine (hnCtxt (queueAssn cap) s dQ ∗ Γ) c Γ' d R m :=
  hnr_pre_ex_pure h

/-- **Establishment from junk** (design D6-P6-2): an array of `cap` slots
holding anything, and two cells both holding `0`, are an empty queue. -/
theorem queueAssn_init (cap : ℕ) (xs : List ℕ) (d : String × String × String)
    (hlen : xs.length = cap) :
    (hnCtxt arrayAssn xs d.1 ∗ (hnCtxt natAssn 0 d.2.1 ∗ hnCtxt natAssn 0 d.2.2))
      ⊢ hnCtxt (queueAssn cap) (0, []) d :=
  queueAssn_intro' cap (0, []) xs 0 0 d ⟨hlen, by simp, by simp⟩ rfl (by simp)

/-- **Release to junk.** -/
theorem queueAssn_release (cap : ℕ) (s : ℕ × List ℕ) (d : String × String × String) :
    hnCtxt (queueAssn cap) s d ⊢ junkArray d.1 ∗ (junkCell d.2.1 ∗ junkCell d.2.2) := by
  rintro h ⟨xs, hh⟩
  obtain ⟨-, hh⟩ := predLift_sepConj_iff.1 hh
  exact conj_entails_mono (arrayAssn_entails_junkArray xs d.1)
    (conj_entails_mono (natAssn_entails_junkCell s.1 d.2.1)
      (natAssn_entails_junkCell (s.1 + s.2.length) d.2.2)) h hh

/-! ## 2. Refute before prove

The two operations as computable twins, executed before anything is
proved. `enqTwin`/`deqTwin` are the values §3's interface operations
return, `repEnq`/`repDeq` the values §4's raw chains return, and
`qwfTwin` decides `QueueWf`. -/

/-- The abstract enqueue: append at the back. -/
def enqTwin (s : ℕ × List ℕ) (v : ℕ) : ℕ × List ℕ := (s.1, s.2 ++ [v])

/-- The abstract dequeue: the front, and the rest with the head bumped. -/
def deqTwin (s : ℕ × List ℕ) : ℕ × (ℕ × List ℕ) := (s.2.head!, (s.1 + 1, s.2.tail))

/-- The representation after an enqueue: the slot at `tail`. -/
def repEnq (xs : List ℕ) (h t v : ℕ) : List ℕ × (ℕ × ℕ) := (xs.set t v, (h, t + 1))

/-- …and after a dequeue: the array is untouched, `head` advances. -/
def repDeq (xs : List ℕ) (h t : ℕ) : ℕ × (List ℕ × (ℕ × ℕ)) := (xs[h]!, (xs, (h + 1, t)))

/-- `QueueWf`, decided. -/
def qwfTwin (cap h : ℕ) (q xs : List ℕ) : Bool :=
  decide (xs.length = cap) && decide (h + q.length ≤ cap) &&
    decide ((xs.drop h).take q.length = q)

#guard enqTwin (0, [3, 1]) 7 = (0, [3, 1, 7])
#guard deqTwin (0, [3, 1, 7]) = (3, (1, [1, 7]))

-- The invariant is established by `init` …
#guard qwfTwin 4 0 [] [0, 0, 0, 0] = true
-- … maintained by enqueue (`tail` starts at `head = 0`) …
#guard repEnq [0, 0, 0, 0] 0 0 3 = ([3, 0, 0, 0], (0, 1))
#guard qwfTwin 4 0 [3] [3, 0, 0, 0] = true
#guard repEnq [3, 0, 0, 0] 0 1 1 = ([3, 1, 0, 0], (0, 2))
#guard qwfTwin 4 0 [3, 1] [3, 1, 0, 0] = true
-- … and by dequeue, which leaves the array alone and is FIFO.
#guard repDeq ([3, 1, 0, 0] : List ℕ) 0 2 = (3, ([3, 1, 0, 0], (1, 2)))
#guard deqTwin (0, [3, 1]) = (3, (1, [1]))
#guard qwfTwin 4 1 [1] ([3, 1, 0, 0] : List ℕ) = true

-- **Negative control 1.** The queue is FIFO, not LIFO: dequeuing the
-- *last* element is refutable.
/--
error: Expression
  decide (deqTwin (0, [3, 1]) = (1, 1, [3]))
did not evaluate to `true`
-/
#guard_msgs in
#guard deqTwin (0, [3, 1]) = (1, (1, [3]))

-- **Negative control 2.** One-shot: the region before `head` is *not*
-- reused, so a head that has run past the written region is not
-- well-formed for a nonempty queue.
/--
error: Expression
  decide (qwfTwin 4 3 [1] [3, 1, 0, 0] = true)
did not evaluate to `true`
-/
#guard_msgs in
#guard qwfTwin 4 3 [1] ([3, 1, 0, 0] : List ℕ) = true

/-! ## 3. The interface operations (design D6-P6-1) -/

/-- `enq`: one array write, one increment, two tuple steps. -/
noncomputable def enqCost : ECost :=
  irUnit Currency.aset + irUnit Currency.add + irUnit Currency.skip + irUnit Currency.skip

/-- `deq`: one array read, one increment, three tuple steps. -/
noncomputable def deqCost : ECost :=
  irUnit Currency.aget + irUnit Currency.add + irUnit Currency.skip + irUnit Currency.skip +
    irUnit Currency.skip

/-- The interface operation `enq`. Its precondition is the one-shot
capacity condition (design D6-P6-6): the *total* number of enqueues,
past and present, must stay below `cap`. -/
noncomputable def mopEnq (cap : ℕ) (s : ℕ × List ℕ) (v : ℕ) : NRest (ℕ × List ℕ) ECost :=
  NRest.bindT (NRest.assert (s.1 + s.2.length < cap)) fun _ =>
    NRest.consume (NRest.returnT (s.1, s.2 ++ [v])) enqCost

/-- The interface operation `deq`: the front element *and* the shortened
queue. -/
noncomputable def mopDeq (s : ℕ × List ℕ) : NRest (ℕ × (ℕ × List ℕ)) ECost :=
  NRest.bindT (NRest.assert (s.2 ≠ [])) fun _ =>
    NRest.consume (NRest.returnT (s.2.head!, (s.1 + 1, s.2.tail))) deqCost

theorem mopEnq_def (cap : ℕ) (s : ℕ × List ℕ) (v : ℕ) :
    mopEnq cap s v = NRest.bindT (NRest.assert (s.1 + s.2.length < cap)) fun _ =>
      NRest.consume (NRest.returnT (s.1, s.2 ++ [v])) enqCost := rfl

theorem mopDeq_def (s : ℕ × List ℕ) :
    mopDeq s = NRest.bindT (NRest.assert (s.2 ≠ [])) fun _ =>
      NRest.consume (NRest.returnT (s.2.head!, (s.1 + 1, s.2.tail))) deqCost := rfl

/-! ## 4. The raw chains and their synthesis (P6/D-bc, P6/D-bi) -/

/-- The raw chain `enq` expands to: write, bump `tail`, two tuples. -/
noncomputable def enqRaw (xs : List ℕ) (h t v : ℕ) : NRest (List ℕ × (ℕ × ℕ)) ECost :=
  NRest.bindT (mopAset xs t v) fun xs' =>
    NRest.bindT (mopBinop .add t 1) fun t' =>
      NRest.bindT (mopPair h t') fun p => mopPair xs' p

/-- The raw chain `deq` expands to: read, bump `head`, three tuples. -/
noncomputable def deqRaw (xs : List ℕ) (h t : ℕ) : NRest (ℕ × (List ℕ × (ℕ × ℕ))) ECost :=
  NRest.bindT (mopAget xs h) fun w =>
    NRest.bindT (mopBinop .add h 1) fun h' =>
      NRest.bindT (mopPair h' t) fun p =>
        NRest.bindT (mopPair xs p) fun qq => mopPair w qq

theorem enqRaw_eq (xs : List ℕ) (h t v : ℕ) (ht : t < xs.length) :
    enqRaw xs h t v = NRest.consume (NRest.returnT (xs.set t v, (h, t + 1))) enqCost := by
  show NRest.bindT (mopAset xs t v) _ = _
  rw [mopAset_def, NRest.assert_pos ht, NRest.returnT_bindT, bindT_unit, mopBinop_def,
    bindT_unit, mopPair_def, bindT_unit, mopPair_def, NRest.consume_consume,
    NRest.consume_consume, NRest.consume_consume]
  simp only [enqCost, Imp.Bop.apply_add, binopCurrency_add]

theorem deqRaw_eq (xs : List ℕ) (h t : ℕ) (hh : h < xs.length) :
    deqRaw xs h t = NRest.consume (NRest.returnT (xs[h]!, (xs, (h + 1, t)))) deqCost := by
  show NRest.bindT (mopAget xs h) _ = _
  rw [mopAget_def, NRest.assert_pos hh, NRest.returnT_bindT, bindT_unit, mopBinop_def,
    bindT_unit]
  simp only [Imp.Bop.apply_add, binopCurrency_add]
  rw [mopPair_def, bindT_unit, mopPair_def, bindT_unit, mopPair_def, NRest.consume_consume,
    NRest.consume_consume, NRest.consume_consume, NRest.consume_consume]
  simp only [deqCost]

/-- The program `enq` compiles to (P6/D-bd: the pin). -/
def enqCom (Q _head tail vc one : String) : Com :=
  .seq (.aset Q tail vc) (.seq (.binop .add tail tail one) (.seq .skip .skip))

/-- The program `deq` compiles to. -/
def deqCom (Q head _tail r one : String) : Com :=
  .seq (.aget r Q head) (.seq (.binop .add head head one) (.seq .skip (.seq .skip .skip)))

#guard enqCom "Q" "head" "tail" "v" "one" =
  Com.seq (Com.aset "Q" "tail" "v")
    (Com.seq (Com.binop Imp.Bop.add "tail" "tail" "one") (Com.seq Com.skip Com.skip))

#guard deqCom "Q" "head" "tail" "r" "one" =
  Com.seq (Com.aget "r" "Q" "head")
    (Com.seq (Com.binop Imp.Bop.add "head" "head" "one")
      (Com.seq Com.skip (Com.seq Com.skip Com.skip)))

sepref_synth enqSynth (Q head tail vc one : String) (xs : List ℕ) (h t v : ℕ) :
  hnRefine (hnCtxt arrayAssn xs Q ∗ hnCtxt natAssn h head ∗ hnCtxt natAssn t tail ∗
      hnCtxt natAssn v vc ∗ hnCtxt natAssn 1 one)
    _ _ (Q, (head, tail)) (arrayAssn ×ₐ (natAssn ×ₐ natAssn)) (enqRaw xs h t v)

sepref_synth deqSynth (Q head tail r one : String) (xs : List ℕ) (h t : ℕ) :
  hnRefine (hnCtxt arrayAssn xs Q ∗ hnCtxt natAssn h head ∗ hnCtxt natAssn t tail ∗
      junkCell r ∗ hnCtxt natAssn 1 one)
    _ _ (r, (Q, (head, tail))) (natAssn ×ₐ (arrayAssn ×ₐ (natAssn ×ₐ natAssn)))
    (deqRaw xs h t)

/-! ## 5. The composite rules (P6/D-bc)

Three list facts, then one `sepref_fr_rules` entry per operation, each
derived from the synthesized raw theorem above in the same four steps as
`IicfStack.lean`'s. -/

theorem take_drop_one {ys t : List ℕ} {a : ℕ} (hq : ys.take (t.length + 1) = a :: t) :
    (ys.drop 1).take t.length = t := by
  have e : List.take t.length (List.drop 1 ys)
      = List.take (t.length + 1 - 1) (List.drop 1 ys) := by norm_num
  rw [e, ← List.drop_take, hq]
  rfl

theorem take_getElem!_zero {ys t : List ℕ} {a : ℕ} (hq : ys.take (t.length + 1) = a :: t)
    (h : 0 < ys.length) : ys[0]! = a := by
  have h1 : (ys.take (t.length + 1))[0]? = some a := by rw [hq]; rfl
  rw [List.getElem?_take, if_pos (by omega)] at h1
  have h2 : some ys[0] = some a := by rw [← List.getElem?_eq_getElem h, h1]
  rw [getElem!_pos ys 0 h]
  exact Option.some.inj h2

theorem drop_getElem!_zero (xs : List ℕ) (h : ℕ) (hh : h < xs.length) :
    (xs.drop h)[0]! = xs[h]! := by
  have h1 : 0 < (xs.drop h).length := by rw [List.length_drop]; omega
  rw [getElem!_pos _ 0 h1, getElem!_pos xs h hh, List.getElem_drop]
  simp

@[sepref_fr_rules]
theorem hnr_mop_enq (cap : ℕ) (s : ℕ × List ℕ) (v : ℕ) (Q head tail vc one : String) :
    hnRefine (hnCtxt (queueAssn cap) s (Q, (head, tail)) ∗ hnCtxt natAssn v vc ∗
        hnCtxt natAssn 1 one)
      (enqCom Q head tail vc one) (hnCtxt natAssn v vc ∗ hnCtxt natAssn 1 one)
      (Q, (head, tail)) (queueAssn cap) (mopEnq cap s v) := by
  rw [mopEnq_def]
  refine hnr_assert fun hlt => ?_
  refine queue_pre fun xs hwf => ?_
  have ht : s.1 + s.2.length < xs.length := by rw [hwf.1]; exact hlt
  have hsyn := hnRefine_abs_cong (enqRaw_eq xs s.1 (s.1 + s.2.length) v ht).symm
    (enqSynth Q head tail vc one xs s.1 (s.1 + s.2.length) v)
  have hwf' : QueueWf cap s.1 (s.2 ++ [v]) (xs.set (s.1 + s.2.length) v) := by
    refine ⟨by simpa using hwf.1, by simp; omega, ?_⟩
    have hd : (xs.set (s.1 + s.2.length) v).drop s.1 = (xs.drop s.1).set s.2.length v := by
      rw [List.drop_set, if_neg (by omega)]
      congr 1
      omega
    have hlen : s.2.length < (xs.drop s.1).length := by rw [List.length_drop]; omega
    simp only [List.length_append, List.length_cons, List.length_nil, hd]
    rw [List.take_set, List.take_add_one, hwf.2.2]
    simp [List.getElem?_eq_getElem hlen]
  have hent : (arrayAssn ×ₐ (natAssn ×ₐ natAssn))
      (xs.set (s.1 + s.2.length) v, (s.1, s.1 + s.2.length + 1)) (Q, (head, tail))
      ⊢ queueAssn cap (s.1, s.2 ++ [v]) (Q, (head, tail)) :=
    queueAssn_intro' cap (s.1, s.2 ++ [v]) _ _ _ _ hwf' rfl (by simp; omega)
  exact hnRefine_pre_perm (by ac_rfl)
    (hnRefine_cons_post (hnRefine_reinterp hsyn hent) (by fri))

/-- The two facts a dequeue needs, packaged so that the main proof never
destructures the abstract state (which would put unreduced projections
into the `∗`-permutation the frame step has to prove). -/
theorem queue_head_tail {xs : List ℕ} {h : ℕ} {q : List ℕ}
    (hrep : (xs.drop h).take q.length = q) (hne : q ≠ []) (hh : h < xs.length) :
    xs[h]! = q.head! ∧ (xs.drop (h + 1)).take q.tail.length = q.tail := by
  cases q with
  | nil => exact absurd rfl hne
  | cons a t =>
    have hys : 0 < (xs.drop h).length := by rw [List.length_drop]; omega
    refine ⟨?_, ?_⟩
    · rw [← drop_getElem!_zero xs h hh]
      exact take_getElem!_zero hrep hys
    · simp only [List.tail_cons]
      rw [show xs.drop (h + 1) = (xs.drop h).drop 1 from by rw [List.drop_drop]]
      exact take_drop_one hrep

theorem tail_length_succ {q : List ℕ} (hne : q ≠ []) : q.tail.length + 1 = q.length := by
  cases q with
  | nil => exact absurd rfl hne
  | cons a t => simp

@[sepref_fr_rules]
theorem hnr_mop_deq (cap : ℕ) (s : ℕ × List ℕ) (Q head tail r one : String) :
    hnRefine (hnCtxt (queueAssn cap) s (Q, (head, tail)) ∗ junkCell r ∗ hnCtxt natAssn 1 one)
      (deqCom Q head tail r one) (hnCtxt natAssn 1 one) (r, (Q, (head, tail)))
      (natAssn ×ₐ queueAssn cap) (mopDeq s) := by
  rw [mopDeq_def]
  refine hnr_assert fun hne => ?_
  refine queue_pre fun xs hwf => ?_
  obtain ⟨hlen, hbnd, hrep⟩ := hwf
  have hlt := tail_length_succ hne
  have hh : s.1 < xs.length := by rw [hlen]; omega
  obtain ⟨hval, htail⟩ := queue_head_tail hrep hne hh
  have hwft : QueueWf cap (s.1 + 1) s.2.tail xs := ⟨hlen, by omega, htail⟩
  have hsyn := hnRefine_abs_cong (deqRaw_eq xs s.1 (s.1 + s.2.length) hh).symm
    (deqSynth Q head tail r one xs s.1 (s.1 + s.2.length))
  have hent : (natAssn ×ₐ (arrayAssn ×ₐ (natAssn ×ₐ natAssn)))
      (xs[s.1]!, (xs, (s.1 + 1, s.1 + s.2.length))) (r, (Q, (head, tail)))
      ⊢ (natAssn ×ₐ queueAssn cap) (s.2.head!, (s.1 + 1, s.2.tail)) (r, (Q, (head, tail))) := by
    refine conj_entails_mono ?_
      (queueAssn_intro' cap (s.1 + 1, s.2.tail) xs _ _ _ hwft rfl (by dsimp only; omega))
    rw [hval]
  exact hnRefine_pre_perm (by ac_rfl)
    (hnRefine_cons_post (hnRefine_reinterp hsyn hent) (by fri))

/-! ## 6. Emptiness as a fused guard (P6/D-bj, design D6-P6-6) -/

/-- The `head` and `tail` cells' contents, read out of the composite. -/
theorem queueAssn_vars {cap : ℕ} {s : ℕ × List ℕ} {Q head tail : String} {F : Assn}
    {st : State} {cr : ECost}
    (hs : irSTATE (hnCtxt (queueAssn cap) s (Q, (head, tail)) ∗ F) (st, cr)) :
    st.vars head = some s.1 ∧ st.vars tail = some (s.1 + s.2.length) := by
  rw [queueAssn_unfold, sepEx_sepConj] at hs
  obtain ⟨xs, hxs⟩ := hs
  rw [sepConj_assoc] at hxs
  obtain ⟨-, hxs⟩ := predLift_sepConj_iff.1 hxs
  simp only [hnCtxt_def, natAssn_def, arrayAssn_def] at hxs
  rw [sepConj_assoc] at hxs
  have h2 := irSTATE_rot hxs
  rw [sepConj_assoc] at h2
  exact ⟨ptoVar_vars h2, ptoVar_vars (irSTATE_rot h2)⟩

@[sepref_cond_rules]
theorem condRefine_queue_nonempty (cap : ℕ) (s : ℕ × List ℕ) (Q head tail : String) :
    CondRefine (hnCtxt (queueAssn cap) s (Q, (head, tail))) (.lt (.cell head) (.cell tail))
      (decide (s.2 ≠ [])) := by
  intro F st cr hs
  obtain ⟨h1, h2⟩ := queueAssn_vars hs
  have h : (s.2 ≠ []) ↔ (s.1 < s.1 + s.2.length) := by
    rcases s.2 with _ | ⟨a, t⟩ <;> simp
  simp [h1, h2, h]

@[sepref_cond_rules]
theorem condRefine_queue_empty (cap : ℕ) (s : ℕ × List ℕ) (Q head tail : String) :
    CondRefine (hnCtxt (queueAssn cap) s (Q, (head, tail))) (.eq (.cell head) (.cell tail))
      (decide (s.2 = [])) := by
  intro F st cr hs
  obtain ⟨h1, h2⟩ := queueAssn_vars hs
  rw [Cond.eval_eq, Operand.eval_cell, Operand.eval_cell, h1, h2]
  simp only [Option.bind_some, Option.map_some, Option.some.injEq]
  rcases s.2 with _ | ⟨a, t⟩
  · simp
  · simp

/-! ## 7. Exercise: enq–drain sum

Two abstract loops through `sepref_synth`, consuming only the registered
rules of §5 and §6 — no bespoke tactic, no hand-written frame clause.
Unlike the stack's exercise both programs are *closed* even at a symbolic
capacity, because the queue's guards mention no literal (P6/D-bj). -/

namespace QExercise

/-! ### Refute before prove -/

/-- The fill loop's twin. -/
def qFillRun (n : ℕ) : ℕ → ℕ × (ℕ × List ℕ) → ℕ × (ℕ × List ℕ)
  | 0, st => st
  | k + 1, st => if st.1 < n then qFillRun n k (st.1 + 1, (st.2.1, st.2.2 ++ [st.1])) else st

/-- The drain loop's twin. -/
def qDrainRun : ℕ → ℕ × (ℕ × List ℕ) → ℕ × (ℕ × List ℕ)
  | 0, st => st
  | k + 1, st =>
    if st.2.2 ≠ [] then qDrainRun k (st.1 + st.2.2.head!, (st.2.1 + 1, st.2.2.tail)) else st

/-- Enqueue `0 … n-1`, then drain, summing. -/
def enqDrainSum (n : ℕ) : ℕ := (qDrainRun n (0, (qFillRun n n (0, (0, []))).2)).1

#guard (qFillRun 4 4 (0, (0, []))).2 = (0, [0, 1, 2, 3])
#guard enqDrainSum 4 = 6
#guard enqDrainSum 5 = 10
#guard enqDrainSum 0 = 0
#guard enqDrainSum 5 = (List.range 5).sum
#guard enqDrainSum 7 = (List.range 7).sum
-- FIFO, not LIFO: the drain visits `0` first, so the head index ends at `n`.
#guard (qDrainRun 4 (0, (qFillRun 4 4 (0, (0, []))).2)).2.1 = 4

-- **Negative control.** A wrong expected sum fails.
/--
error: Expression
  decide (enqDrainSum 5 = 11)
did not evaluate to `true`
-/
#guard_msgs in
#guard enqDrainSum 5 = 11

/-! ### The fill loop -/

/-- The invariant: as many enqueues as the counter counts. It is what
makes `enq`'s one-shot capacity assertion pass. -/
def qFillI : ℕ × (ℕ × List ℕ) → Prop := fun st => st.2.1 + st.2.2.length = st.1

/-- The guard: `i < n`. -/
def qFillBf (n : ℕ) : ℕ × (ℕ × List ℕ) → Bool := fun st => decide (st.1 < n)

/-- The body: enqueue the counter, bump it, retuple. -/
noncomputable def qFillF (cap : ℕ) : ℕ × (ℕ × List ℕ) → NRest (ℕ × (ℕ × List ℕ)) ECost :=
  fun st =>
    NRest.bindT (mopEnq cap st.2 st.1) fun s' =>
      NRest.bindT (mopBinop .add st.1 1) fun i' => mopPair i' s'

/-- One iteration's price. -/
noncomputable def qFillCost : ECost := enqCost + irUnit Currency.add + irUnit Currency.skip

theorem qFillF_eq (cap : ℕ) (st : ℕ × (ℕ × List ℕ)) (h : st.2.1 + st.2.2.length < cap) :
    qFillF cap st
      = NRest.consume (NRest.returnT (st.1 + 1, (st.2.1, st.2.2 ++ [st.1]))) qFillCost := by
  show NRest.bindT (mopEnq cap st.2 st.1) _ = _
  rw [mopEnq_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, mopBinop_def,
    bindT_unit, mopPair_def, NRest.consume_consume, NRest.consume_consume]
  simp only [qFillCost, Imp.Bop.apply_add, binopCurrency_add]

theorem qFill_variant (cap n : ℕ) (hn : n ≤ cap) :
    LOOP_VARIANT qFillI (qFillBf n) (qFillF cap) (fun st => n - st.1) := by
  intro st st' hI hb hle
  have hI' : st.2.1 + st.2.2.length = st.1 := hI
  have hb' : st.1 < n := by simpa [qFillBf] using hb
  have hlt : st.2.1 + st.2.2.length < cap := by omega
  rw [qFillF_eq cap st hlt, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hst : st' = (st.1 + 1, (st.2.1, st.2.2 ++ [st.1])) := by
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
sepref_synth queueFill (cap n : ℕ)
    (hv : LOOP_VARIANT qFillI (qFillBf n) (qFillF cap) (fun st => n - st.1)) :
  hnRefine (hnCtxt (natAssn ×ₐ queueAssn cap) (0, (0, [])) ("i", ("Q", ("head", "tail"))) ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn n "n")
    _ _ ("i", ("Q", ("head", "tail"))) (natAssn ×ₐ queueAssn cap)
    (irWhileIT qFillI (qFillBf n) (qFillF cap) (0, (0, [])))

/-! ### The drain loop -/

/-- No invariant is needed: the guard gives `deq`'s nonemptiness. -/
def qDrainI : ℕ × (ℕ × List ℕ) → Prop := fun _ => True

/-- The guard: the queue is nonempty — the fused `head < tail` of §6. -/
def qDrainBf : ℕ × (ℕ × List ℕ) → Bool := fun st => decide (st.2.2 ≠ [])

/-- The body: dequeue into the scratch cell, accumulate, retuple. -/
noncomputable def qDrainF : ℕ × (ℕ × List ℕ) → NRest (ℕ × (ℕ × List ℕ)) ECost := fun st =>
  NRest.bindT (mopDeq st.2) fun p =>
    NRest.bindT (mopBinop .add st.1 p.1) fun acc' => mopPair acc' p.2

/-- One iteration's price. -/
noncomputable def qDrainCost : ECost := deqCost + irUnit Currency.add + irUnit Currency.skip

theorem qDrainF_eq (st : ℕ × (ℕ × List ℕ)) (h : st.2.2 ≠ []) :
    qDrainF st = NRest.consume
      (NRest.returnT (st.1 + st.2.2.head!, (st.2.1 + 1, st.2.2.tail))) qDrainCost := by
  show NRest.bindT (mopDeq st.2) _ = _
  rw [mopDeq_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, mopBinop_def,
    bindT_unit, mopPair_def, NRest.consume_consume, NRest.consume_consume]
  simp only [qDrainCost, Imp.Bop.apply_add, binopCurrency_add]

theorem qDrain_variant : LOOP_VARIANT qDrainI qDrainBf qDrainF (fun st => st.2.2.length) := by
  intro st st' _ hb hle
  have hb' : st.2.2 ≠ [] := by simpa [qDrainBf] using hb
  rw [qDrainF_eq st hb', NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hst : st' = (st.1 + st.2.2.head!, (st.2.1 + 1, st.2.2.tail)) := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hst
  show st.2.2.tail.length < st.2.2.length
  cases hs : st.2.2 with
  | nil => exact absurd hs hb'
  | cons a t => simp

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth queueDrain (cap : ℕ) (q₀ : ℕ × List ℕ)
    (hv : LOOP_VARIANT qDrainI qDrainBf qDrainF (fun st => st.2.2.length)) :
  hnRefine (hnCtxt (natAssn ×ₐ queueAssn cap) (0, q₀) ("acc", ("Q", ("head", "tail"))) ∗
      junkCell "r" ∗ hnCtxt natAssn 1 "one")
    _ _ ("acc", ("Q", ("head", "tail"))) (natAssn ×ₐ queueAssn cap)
    (irWhileIT qDrainI qDrainBf qDrainF (0, q₀))

-- The synthesized fill loop, pinned.
#guard queueFill_impl =
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    (Com.seq (Com.seq (Com.aset "Q" "tail" "i")
        (Com.seq (Com.binop Imp.Bop.add "tail" "tail" "one") (Com.seq Com.skip Com.skip)))
      (Com.seq (Com.binop Imp.Bop.add "i" "i" "one") Com.skip))

-- …and the drain loop, whose guard `head < tail` the tool synthesized
-- from `decide (q ≠ [])`.
#guard queueDrain_impl =
  Com.while (Cond.lt (Operand.cell "head") (Operand.cell "tail"))
    (Com.seq (Com.seq (Com.aget "r" "Q" "head")
        (Com.seq (Com.binop Imp.Bop.add "head" "head" "one")
          (Com.seq Com.skip (Com.seq Com.skip Com.skip))))
      (Com.seq (Com.binop Imp.Bop.add "acc" "acc" "r") Com.skip))

/-- The fill loop with its variant discharged. -/
theorem queueFill' (cap n : ℕ) (hn : n ≤ cap) :
    hnRefine (hnCtxt (natAssn ×ₐ queueAssn cap) (0, (0, [])) ("i", ("Q", ("head", "tail"))) ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn n "n")
      queueFill_impl (hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn n "n")
      ("i", ("Q", ("head", "tail"))) (natAssn ×ₐ queueAssn cap)
      (irWhileIT qFillI (qFillBf n) (qFillF cap) (0, (0, []))) :=
  queueFill cap n (qFill_variant cap n hn)

/-- The drain loop with its variant discharged. -/
theorem queueDrain' (cap : ℕ) (q₀ : ℕ × List ℕ) :
    hnRefine (hnCtxt (natAssn ×ₐ queueAssn cap) (0, q₀) ("acc", ("Q", ("head", "tail"))) ∗
        junkCell "r" ∗ hnCtxt natAssn 1 "one")
      queueDrain_impl (junkCell "r" ∗ hnCtxt natAssn 1 "one")
      ("acc", ("Q", ("head", "tail"))) (natAssn ×ₐ queueAssn cap)
      (irWhileIT qDrainI qDrainBf qDrainF (0, q₀)) :=
  queueDrain cap q₀ qDrain_variant

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_enq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_enq

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_deq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_deq

/-- info: 'Lax13Proofs.Refine.Iicf.QExercise.queueFill'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queueFill'

/-- info: 'Lax13Proofs.Refine.Iicf.QExercise.queueDrain'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queueDrain'

end QExercise

end Lax13Proofs.Refine.Iicf
