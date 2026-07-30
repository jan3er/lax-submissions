import Lax13Proofs.Refine.Iicf.IicfArray

/-!
# Trail-backed touched-only arrays — the D5 default array

The ND-MC campaign's touched-only-costs discipline (memory
`touched-only-costs.md`: "recursive per-arena RAM passes must charge
active sets from the FIRST brief; O(n) init × n arenas = n² kills
sublinear headlines") made a library object, as ledger D5 asks.

A trail array is a data array `A` of length `n`, a *trail* array `T` of
the same capacity recording which slots have been written since the last
reset, and a top-of-trail counter `t`. Reading is a plain read. Writing
writes and pushes the index. Resetting pops the trail, restoring each
touched slot to the default — so **the reset costs one pop per write
since the last reset, and nothing per untouched slot**. That is the
theorem this file exists for (§7).

The abstract type is `List Val × ℕ`: the array's contents, and the
*touch budget counter* `k` — the design record's "abstract cost carrier
that makes reset's touched-proportional cost sayable abstractly". `k` is
not an implementation detail leaking upward; it is the resource the
interface charges against, exactly as a credit balance is.

## Judgment calls

**P6/D-p — `k` counts *writes*, not *distinct touched slots*, and
`tset` therefore asserts `k < n`.** The trail is pushed
unconditionally: `tset` does not first test whether the slot is already
on the trail (that test is a read plus a branch per write, and it is not
what the source's trail structures do either). The consequence is that
the trail's capacity — which the design record fixes at `|xs|` — bounds
the number of writes *between resets*, not the number of distinct slots,
so `mop_tset`'s precondition includes `k < n`. A program that writes one
slot `n + 1` times between resets must reset in between. This is a real
restriction and it is the price of an unconditional push; the fallback
is a `cap` parameter decoupled from `|xs|`, which changes `trailAssn`'s
signature and nothing else.

**P6/D-q — the trail's *contents* are ghost state, the counter is not.**
`trailAssn` existentially owns the trail array and states the invariant
relating it to `(xs, k)`; the counter `k` is part of the abstract value
because reset's cost depends on it. Consequently `tget`/`tset`/`treset`
are proved at the raw three-cell assertion and lifted (P6/D-h), and no
consumer ever sees `T`'s contents.

**P6/D-r — `treset`'s implementation is synthesized, `tget`'s and
`tset`'s are too.** All three raw programs go through `sepref_synth`
from the primitive mops; the pop-loop needed no hand derivation from the
P4 combinator rules. What is *not* synthesized is the lift from the raw
three-cell assertion to `trailAssn` — that is `hnr_pre_ex_conv` +
`hnr_pre_pure_conv` + `hnRefine_res_cast'`, three lines per op, and it is
where the invariant is discharged.

**P6/D-s — the reset loop's invariant is the structure's own
well-formedness.** `irWhileIT` asserts its invariant at every iteration,
so the invariant is where the index bounds for the pop's read and write
come from (P4/D-ed). Making it `TrailWf` rather than something weaker is
free — the entry state satisfies it by the assertion, and preserving it
is the induction step of the value lemma anyway.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

namespace Iicf

/-! ## 1. The representation invariant -/

/-- `TrailWf dflt n xs tr k`: the data array `xs`, the trail `tr` and the
top `k` represent an array of length `n` whose *untouched* slots hold
`dflt`. Both arrays have the fixed capacity `n` (design record: "trail
array (capacity = |xs|)"), the trail's live prefix is `tr.take k`, its
entries are in range, and every slot not on it is default. -/
structure TrailWf (dflt n : ℕ) (xs tr : List ℕ) (k : ℕ) : Prop where
  data_len : xs.length = n
  trail_len : tr.length = n
  top_le : k ≤ n
  mem_lt : ∀ j ∈ tr.take k, j < n
  off_trail : ∀ i, i < n → i ∉ tr.take k → xs[i]! = dflt

/-- **The composite assertion** (P6/D-h, P6/D-q): the three cells, with
the trail's contents existentially owned and the invariant as a pure
conjunct. -/
def trailAssn (dflt n : ℕ) : List ℕ × ℕ → String × String × String → Assn :=
  fun s c => ∃ᵃ tr, ⌜TrailWf dflt n s.1 tr s.2⌝ ∗
    (arrayAssn s.1 c.1 ∗ arrayAssn tr c.2.1 ∗ natAssn s.2 c.2.2)

/-- The unfold lemma the frame matcher's cell-name pairing needs
(`Iicf/Basic.lean` §1). -/
theorem trailAssn_unfold (dflt n : ℕ) (s : List ℕ × ℕ) (c : String × String × String) :
    trailAssn dflt n s c = ∃ᵃ tr, ⌜TrailWf dflt n s.1 tr s.2⌝ ∗
      (arrayAssn s.1 c.1 ∗ arrayAssn tr c.2.1 ∗ natAssn s.2 c.2.2) := rfl

/-- Packing: three raw cells plus the invariant are the structure. -/
theorem trailAssn_pack {dflt n : ℕ} {xs tr : List ℕ} {k : ℕ}
    (c : String × String × String) (h : TrailWf dflt n xs tr k) :
    (arrayAssn xs c.1 ∗ arrayAssn tr c.2.1 ∗ natAssn k c.2.2) ⊢ trailAssn dflt n (xs, k) c :=
  fun _ hh => ⟨tr, predLift_sepConj_iff.2 ⟨h, hh⟩⟩

/-- Releasing a trail array (`Iicf/Basic.lean` §3): its three cells go
back to being capacity-fixed junk. Nothing is freed. -/
theorem trailAssn_release (dflt n : ℕ) (s : List ℕ × ℕ) (c : String × String × String) :
    trailAssn dflt n s c ⊢
      junkArrayOfLen n c.1 ∗ junkArrayOfLen n c.2.1 ∗ junkCell c.2.2 := by
  intro h hh
  obtain ⟨tr, hh⟩ := hh
  obtain ⟨hwf, hh⟩ := predLift_sepConj_iff.1 hh
  refine conj_entails_mono (arrayAssn_entails_junkArrayOfLen' s.1 c.1 hwf.data_len)
    (conj_entails_mono (arrayAssn_entails_junkArrayOfLen' tr c.2.1 hwf.trail_len)
      (natAssn_entails_junkCell s.2 c.2.2)) _ hh

/-! ## 2. Refute before prove

The trail discipline is *run* — write, reset, write, reset — through
computable twins of the abstract ops, before any of them is refined.
`tsetT` and `tresetT` are the functions §5's value lemmas prove the
abstract ops equal to. -/

/-- The computable twin of `tset`: write, push, bump. -/
def tsetT (s : (List ℕ × ℕ) × List ℕ) (i v : ℕ) : (List ℕ × ℕ) × List ℕ :=
  ((s.1.1.set i v, s.1.2 + 1), s.2.set s.1.2 i)

/-- The computable twin of `treset`, as the pop loop actually runs it —
*not* as `List.replicate`, so that the `#guard`s below test the loop's
own behaviour against the specification rather than restating it. -/
def tresetT (dflt : ℕ) : ℕ → (List ℕ × ℕ) × List ℕ → (List ℕ × ℕ) × List ℕ
  | 0, s => s
  | m + 1, s =>
    if s.1.2 = 0 then s
    else tresetT dflt m ((s.1.1.set (s.2[s.1.2 - 1]!) dflt, s.1.2 - 1), s.2)

/-- The number of pops a reset performs — the quantity the cost is
proportional to. -/
def tresetPops (s : (List ℕ × ℕ) × List ℕ) : ℕ := s.1.2

/-- A fresh trail array of capacity `n`. -/
def tinit (dflt n : ℕ) : (List ℕ × ℕ) × List ℕ :=
  ((List.replicate n dflt, 0), List.replicate n 0)

/-- Round one: three writes into a length-8 array, then a reset. -/
def round1 : (List ℕ × ℕ) × List ℕ :=
  tsetT (tsetT (tsetT (tinit 0 8) 2 5) 6 7) 0 1

/-- Round two, on the *reset* state: two writes, then a reset. -/
def round2 : (List ℕ × ℕ) × List ℕ :=
  tsetT (tsetT (tresetT 0 8 round1) 3 9) 4 4

#guard round1.1.1 = [1, 0, 5, 0, 0, 0, 7, 0]
#guard round1.1.2 = 3
-- Reset restores the default everywhere, whatever the writes were.
#guard (tresetT 0 8 round1).1.1 = List.replicate 8 0
#guard (tresetT 0 8 round1).1.2 = 0
#guard round2.1.1 = [0, 0, 0, 9, 4, 0, 0, 0]
#guard round2.1.2 = 2
#guard (tresetT 0 8 round2).1.1 = List.replicate 8 0
#guard (tresetT 0 8 round2).1.2 = 0

-- **The touched-only claim, as arithmetic**: round one pops three times,
-- round two pops twice, and the array's length (8) is nowhere in either
-- number.
#guard tresetPops round1 = 3
#guard tresetPops round2 = 2
#guard tresetPops round2 < tresetPops round1

-- **Negative control.** Reset does not pop once per slot.
/--
error: Expression
  decide (tresetPops round2 = 8)
did not evaluate to `true`
-/
#guard_msgs in
#guard tresetPops round2 = 8

-- **Negative control 2.** A reset that stops one pop short leaves the
-- array dirty — the loop is not vacuously correct.
/--
error: Expression
  decide ((tresetT 0 1 round1).1.1 = List.replicate 8 0)
did not evaluate to `true`
-/
#guard_msgs in
#guard (tresetT 0 1 round1).1.1 = List.replicate 8 0

/-! ## 3. The raw programs and their synthesis (D6-P6-3, P6/D-r)

Everything below the composite assertion. The three raw programs are
written at the primitive mop layer over the three cells `(A, T, t)`, and
`sepref_synth` turns each into an `Ir.Com`. -/

/-- **`tset`, raw**: push the index onto the trail, bump the top, write
the value. -/
noncomputable def tsetRaw (xs tr : List ℕ) (k i v : ℕ) :
    NRest (List ℕ × List ℕ × ℕ) ECost :=
  NRest.bindT (mopAset tr k i) fun tr' =>
    NRest.bindT (mopBinop .add k 1) fun k' =>
      NRest.bindT (mopAset xs i v) fun xs' =>
        NRest.bindT (mopPair tr' k') fun p => mopPair xs' p

/--
info: sepref_synth Lax13Proofs.Refine.Sepref.Iicf.tsetSynth:
  (Com.aset T t I).seq ((Com.binop Imp.Bop.add t t one).seq ((Com.aset A I V).seq (Com.skip.seq Com.skip)))
-/
#guard_msgs in
sepref_synth tsetSynth (A T t I V one : String) (xs tr : List ℕ) (k i v : ℕ) :
  hnRefine (hnCtxt arrayAssn xs A ∗ hnCtxt arrayAssn tr T ∗ hnCtxt natAssn k t ∗
      hnCtxt natAssn i I ∗ hnCtxt natAssn v V ∗ hnCtxt natAssn 1 one)
    _ _ (A, T, t) (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (tsetRaw xs tr k i v)

/-! ### The pop loop

Two things about its shape are forced by the pipeline and recorded as
flags.

**P6/D-t — the trail array stays in the *frame*, not in the loop
state.** `hnr_while_measured`'s body post is its frame, so everything the
body *mutates* must be in the state (P4/D-ec) — but `T` is only read by
the pop loop, so it is a frame conjunct and the loop state is the pair
`(xs, k)` at `(A, t)`. This is not cosmetic: with two arrays inside one
`prodAssn` state the frame matcher's split-and-permute step failed to
close, and with one it does.

**P6/D-u — the top is decremented twice: once into a scratch cell for
the read, once in place.** The pop needs the index `t - 1` in a *cell* to
read `T[t-1]`, and it needs the state's own `t` cell to end up holding
`t - 1`. `hnr_mop_binop` (destination = a junk cell) is tried before
`hnr_mop_binop_self` (in place) and the pipeline does not backtrack
across that choice, so a single `mopBinop` in the presence of a free
scratch cell always lands in the scratch cell — and then the loop state's
`t` is never updated. Writing the subtraction twice makes the choice
deterministic: the first has a scratch cell available and takes it, the
second does not and goes in place. The price is one extra `ir.sub` per
pop, which is still Θ(1) per *touch* and so does not affect the
characteristic theorem. Fallbacks, in preference order: a `mop_move`
whose destination is a live cell; making `hnr_mop_binop_self` take
priority; or making the operator phase backtrack. -/

/-- The guard: the trail is non-empty. A *structural* guard on the top
cell (P4/D-af), not a boolean operation — the design record's D6-P6-5
route, here for `treset`'s loop rather than for an `isEmpty` op. -/
def resetBf : List ℕ × ℕ → Bool := fun s => decide (0 < s.2)

/-- The loop invariant is the structure's own well-formedness
(P6/D-s); the trail `tr` it is stated against is the frame's (P6/D-t). -/
def resetI (dflt n : ℕ) (tr : List ℕ) : List ℕ × ℕ → Prop :=
  fun s => TrailWf dflt n s.1 tr s.2

/-- **The pop**: compute the top's predecessor, read the slot the trail
records there, restore the default in it, lower the top (P6/D-u). -/
noncomputable def resetF (dflt : ℕ) (tr : List ℕ) :
    List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  NRest.bindT (mopBinop .sub s.2 1) fun p =>
    NRest.bindT (mopAget tr p) fun j =>
      NRest.bindT (mopAset s.1 j dflt) fun xs' =>
        NRest.bindT (mopBinop .sub s.2 1) fun k' => mopPair xs' k'

/-- The variant: the trail's height. -/
def resetV : List ℕ × ℕ → ℕ := fun s => s.2

/--
info: sepref_synth Lax13Proofs.Refine.Sepref.Iicf.resetSynth:
  Com.while (Cond.lt (Operand.lit 0) (Operand.cell t))
    ((Com.binop Imp.Bop.sub P t one).seq
      ((Com.aget J T P).seq ((Com.aset A J D).seq ((Com.binop Imp.Bop.sub t t one).seq Com.skip))))
-/
#guard_msgs in
-- The `hv` annotation is inert since R0/D-b (`CombRules.lean`'s
-- `hnr_while` needs no variant); the signature is kept for the callers.
set_option linter.unusedVariables false in
sepref_synth resetSynth (A T t P J D one : String) (dflt n : ℕ) (xs tr : List ℕ) (k : ℕ)
    (hv : LOOP_VARIANT (resetI dflt n tr) resetBf (resetF dflt tr) resetV) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (xs, k) (A, t) ∗ hnCtxt arrayAssn tr T ∗
      junkCell P ∗ junkCell J ∗ hnCtxt natAssn dflt D ∗ hnCtxt natAssn 1 one)
    _ _ (A, t) (arrayAssn ×ₐ natAssn)
    (irWhileIT (resetI dflt n tr) resetBf (resetF dflt tr) (xs, k))


/-! ## 4. List lemmas the trail discipline needs

Three, all about the live prefix `tr.take k` and one write into it. -/

theorem take_set_self (l : List ℕ) (k a : ℕ) : (l.set k a).take k = l.take k := by
  refine List.ext_getElem (by simp) fun m h1 h2 => ?_
  have hm : m < k := (show m < k ∧ m < l.length by simpa using h1).1
  simp [Nat.ne_of_lt' hm]

theorem take_succ_eq (l : List ℕ) (k : ℕ) (h : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]!] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, getElem!_pos l k h]
  rfl

theorem mem_take_succ {l : List ℕ} {k x : ℕ} (h : k < l.length) :
    x ∈ l.take (k + 1) ↔ x ∈ l.take k ∨ x = l[k]! := by
  rw [take_succ_eq l k h]; simp

theorem eq_replicate_of_forall {xs : List ℕ} {n dflt : ℕ} (hlen : xs.length = n)
    (h : ∀ i, i < n → xs[i]! = dflt) : xs = List.replicate n dflt := by
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  have := h i (by omega)
  rw [getElem!_pos xs i h1] at this
  simp [this]

/-! ## 5. The interface ops, their costs, and their values (D6-P6-1, P6/D-j)

Each op's cost is exactly what §3's synthesis spent; each op's value is
proved equal to what the raw program computes. -/

/-- **`tget`**: a read. The touch counter is untouched, so no cost beyond
the read itself. -/
noncomputable def mop_tget (s : List ℕ × ℕ) (i : ℕ) : NRest ℕ ECost := mopAget s.1 i

/-- **`tset`'s price**: the trail push, the top's bump, the write, and
the two tuple steps. -/
noncomputable def tsetCost : ECost :=
  irUnit Currency.aset + irUnit Currency.add + irUnit Currency.aset +
    irUnit Currency.skip + irUnit Currency.skip

/-- **`tset`**: write, and spend one unit of the touch budget. The
precondition `s.2 < n` is the trail's capacity (P6/D-p). -/
noncomputable def mop_tset (n : ℕ) (s : List ℕ × ℕ) (i v : ℕ) : NRest (List ℕ × ℕ) ECost :=
  NRest.bindT (NRest.assert (i < n ∧ s.2 < n)) fun _ =>
    NRest.consume (NRest.returnT (s.1.set i v, s.2 + 1)) tsetCost

/-- **One pop's price** (P6/D-u for the second `ir.sub`). -/
noncomputable def resetStepCost : ECost :=
  irUnit Currency.sub + irUnit Currency.aget + irUnit Currency.aset +
    irUnit Currency.sub + irUnit Currency.skip

/-- **`treset`'s price**: one pop per unit of touch budget spent, plus
one guard evaluation per pop and the exit's. **`k` is the only
parameter** — the array's length does not occur (§7). -/
noncomputable def resetCost (k : ℕ) : ECost :=
  k • resetStepCost + (k + 1) • irUnit Currency.«while»

/-- **`treset`**: every slot back to the default, the touch budget back
to full. -/
noncomputable def mop_treset (dflt n : ℕ) (s : List ℕ × ℕ) : NRest (List ℕ × ℕ) ECost :=
  NRest.consume (NRest.returnT (List.replicate n dflt, 0)) (resetCost s.2)

/-- The raw `tset` program's value. -/
theorem tsetRaw_eq (xs tr : List ℕ) (k i v : ℕ) (hk : k < tr.length) (hi : i < xs.length) :
    tsetRaw xs tr k i v
      = NRest.consume (NRest.returnT (xs.set i v, tr.set k i, k + 1)) tsetCost := by
  show NRest.bindT (mopAset tr k i) _ = _
  simp only [mopAset_def, mopBinop_def, mopPair_def, NRest.assert_pos hk,
    NRest.assert_pos hi, NRest.returnT_bindT, bindT_unit, NRest.consume_consume,
    tsetCost, Imp.Bop.apply_add, binopCurrency_add]
  congr 1
  ac_rfl

/-- One pop's value: the slot the trail's top records goes back to the
default, and the top comes down. -/
theorem resetF_eq (dflt : ℕ) (tr : List ℕ) (s : List ℕ × ℕ) (hp : s.2 - 1 < tr.length)
    (hj : tr[s.2 - 1]! < s.1.length) :
    resetF dflt tr s
      = NRest.consume (NRest.returnT (s.1.set tr[s.2 - 1]! dflt, s.2 - 1)) resetStepCost := by
  show NRest.bindT (mopBinop .sub s.2 1) _ = _
  simp only [mopBinop_def, mopAget_def, mopAset_def, bindT_unit, NRest.assert_pos hp,
    NRest.assert_pos hj, NRest.returnT_bindT, mopPair_def, NRest.consume_consume,
    resetStepCost, Imp.Bop.apply_sub, binopCurrency_sub]
  congr 1
  ac_rfl

/-- The variant obligation, at the invariant the loop carries
(P6/D-s). -/
theorem reset_variant (dflt n : ℕ) (tr : List ℕ) :
    LOOP_VARIANT (resetI dflt n tr) resetBf (resetF dflt tr) resetV := by
  intro s s' hI hb hle
  have hpos : 0 < s.2 := by simpa [resetBf] using hb
  have htop := hI.top_le
  have hp : s.2 - 1 < tr.length := by rw [hI.trail_len]; omega
  have hmem : tr[s.2 - 1]! ∈ tr.take s.2 := by
    have h1 : tr[s.2 - 1]! ∈ tr.take (s.2 - 1 + 1) := (mem_take_succ hp).2 (Or.inr rfl)
    rwa [Nat.sub_add_cancel hpos] at h1
  have hj : tr[s.2 - 1]! < s.1.length := by
    rw [hI.data_len]; exact hI.mem_lt _ hmem
  rw [resetF_eq dflt tr s hp hj, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = (s.1.set tr[s.2 - 1]! dflt, s.2 - 1) := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hs'
  show s.2 - 1 < s.2
  omega

/-- Popping one entry preserves the invariant at the lower top. -/
theorem trailWf_pop {dflt n : ℕ} {xs tr : List ℕ} {k : ℕ}
    (h : TrailWf dflt n xs tr (k + 1)) :
    TrailWf dflt n (xs.set tr[k]! dflt) tr k := by
  have htop := h.top_le
  have hk : k < tr.length := by rw [h.trail_len]; omega
  have hmem : tr[k]! ∈ tr.take (k + 1) := (mem_take_succ hk).2 (Or.inr rfl)
  have hjn : tr[k]! < n := h.mem_lt _ hmem
  refine ⟨by simpa using h.data_len, h.trail_len, by omega, ?_, ?_⟩
  · intro j hj
    exact h.mem_lt j ((mem_take_succ hk).2 (Or.inl hj))
  · intro i hi hni
    have hlt : i < xs.length := by rw [h.data_len]; exact hi
    have hlt' : i < (xs.set tr[k]! dflt).length := by simpa using hlt
    by_cases hij : i = tr[k]!
    · rw [getElem!_pos _ i hlt']
      simp [hij]
    · rw [getElem!_pos _ i hlt', List.getElem_set_ne (Ne.symm hij), ← getElem!_pos xs i hlt]
      exact h.off_trail i hi (fun hc => hni ((mem_take_succ hk).1 hc |>.resolve_right hij))

/-- **The pop loop's value**: whatever the writes were, the array comes
back to all-default and the top to zero, at a price that depends on `k`
alone. -/
theorem resetLoop_value (dflt n : ℕ) (tr : List ℕ) :
    ∀ (k : ℕ) (xs : List ℕ), TrailWf dflt n xs tr k →
      irWhileIT (resetI dflt n tr) resetBf (resetF dflt tr) (xs, k)
        = NRest.consume (NRest.returnT (List.replicate n dflt, 0)) (resetCost k) := by
  intro k
  induction k with
  | zero =>
    intro xs hwf
    have hI : resetI dflt n tr (xs, (0 : ℕ)) := hwf
    have hb : resetBf (xs, (0 : ℕ)) = false := by simp [resetBf]
    rw [irWhileIT_of_false hI hb]
    have hx : xs = List.replicate n dflt :=
      eq_replicate_of_forall hwf.data_len fun i hi => hwf.off_trail i hi (by simp)
    rw [hx]
    congr 1
    simp [resetCost]
  | succ k ih =>
    intro xs hwf
    have hI : resetI dflt n tr (xs, k + 1) := hwf
    have hb : resetBf (xs, k + 1) = true := by simp [resetBf]
    have htop := hwf.top_le
    have hp : k + 1 - 1 < tr.length := by rw [hwf.trail_len]; omega
    have hmem : tr[k]! ∈ tr.take (k + 1) := (mem_take_succ hp).2 (Or.inr rfl)
    have hj : tr[(k + 1) - 1]! < xs.length := by
      rw [hwf.data_len]; exact hwf.mem_lt _ hmem
    rw [irWhileIT_of_true hI hb, resetF_eq dflt tr (xs, k + 1) hp hj, bindT_unit]
    show NRest.consume (irWhileIT _ _ _ (xs.set tr[k]! dflt, k) |>.consume resetStepCost) _ = _
    rw [ih _ (trailWf_pop hwf), NRest.consume_consume, NRest.consume_consume]
    congr 1
    simp only [resetCost, succ_nsmul]
    abel

/-! ## 6. The lifted rules (P6/D-h, D6-P6-3)

Three registered rules, one per interface op, each at caller-chosen cell
names and each stated at the composite assertion. This is the file's
`FCOMP`: the raw judgment goes in, `hnr_pre_ex_conv` +
`hnr_pre_pure_conv` discharge the ghost trail and the invariant on the
way in, `hnRefine_res_cast'` re-packs them on the way out. -/

/-- A judgment whose precondition owns a trail array is a judgment at
every concrete trail satisfying the invariant. -/
theorem hnr_trail_pre {α κ : Type} {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
    {m : NRest α ECost} {dflt n : ℕ} {s : List ℕ × ℕ} {cc : String × String × String}
    (h : ∀ tr, TrailWf dflt n s.1 tr s.2 →
        hnRefine ((arrayAssn s.1 cc.1 ∗ arrayAssn tr cc.2.1 ∗ natAssn s.2 cc.2.2) ∗ Γ)
          c Γ' d R m) :
    hnRefine (hnCtxt (trailAssn dflt n) s cc ∗ Γ) c Γ' d R m := by
  rw [hnCtxt_def, trailAssn_unfold, sepEx_sepConj]
  refine hnr_pre_ex_conv.2 fun tr => ?_
  rw [sepConj_assoc]
  exact hnr_pre_pure_conv.2 fun hwf => h tr hwf

/-- Pushing preserves the invariant, at one more unit of budget spent. -/
theorem trailWf_push {dflt n : ℕ} {xs tr : List ℕ} {k i v : ℕ}
    (h : TrailWf dflt n xs tr k) (hi : i < n) (hk : k < n) :
    TrailWf dflt n (xs.set i v) (tr.set k i) (k + 1) := by
  have hklen : k < (tr.set k i).length := by rw [List.length_set, h.trail_len]; exact hk
  have htake : (tr.set k i).take (k + 1) = tr.take k ++ [i] := by
    rw [take_succ_eq _ k hklen, take_set_self]
    congr 1
    rw [getElem!_pos _ k hklen]
    simp
  refine ⟨by simpa using h.data_len, by simpa using h.trail_len, by omega, ?_, ?_⟩
  · intro j hj
    rw [htake] at hj
    rcases List.mem_append.1 hj with hj | hj
    · exact h.mem_lt j hj
    · rw [List.mem_singleton.1 hj]; exact hi
  · intro m hm hnm
    rw [htake] at hnm
    have hmi : m ≠ i := fun hc => hnm (List.mem_append.2 (Or.inr (by simp [hc])))
    have hmt : m ∉ tr.take k := fun hc => hnm (List.mem_append.2 (Or.inl hc))
    have hlt : m < xs.length := by rw [h.data_len]; exact hm
    have hlt' : m < (xs.set i v).length := by simpa using hlt
    rw [getElem!_pos _ m hlt', List.getElem_set_ne (Ne.symm hmi), ← getElem!_pos xs m hlt]
    exact h.off_trail m hm hmt

/-- A reset array is well-formed against any trail of the right
capacity: nothing is on the live prefix. -/
theorem trailWf_empty {dflt n : ℕ} {tr : List ℕ} (h : tr.length = n) :
    TrailWf dflt n (List.replicate n dflt) tr 0 :=
  ⟨by simp, h, Nat.zero_le _, by simp, fun i hi _ => by
    rw [getElem!_pos _ i (by simpa using hi)]; simp⟩

/-! ### `tget` -/

/-- The compound program of `tget` — a plain read; the structure is
what makes it an interface op. -/
def tgetCom (x A I : String) : Com := .aget x A I

@[sepref_fr_rules]
theorem hnr_mop_tget (dflt n : ℕ) (x A T t I : String) (s : List ℕ × ℕ) (i : ℕ) :
    hnRefine (hnCtxt (trailAssn dflt n) s (A, T, t) ∗ junkCell x ∗ hnCtxt natAssn i I)
      (tgetCom x A I)
      (hnCtxt (trailAssn dflt n) s (A, T, t) ∗ hnCtxt natAssn i I)
      x natAssn (mop_tget s i) := by
  refine hnr_trail_pre fun tr hwf => ?_
  refine hnRefine_cons_pre (hnRefine_cons_post
    (hnRefine_frame' (F := arrayAssn tr T ∗ natAssn s.2 t) (hnr_mop_aget x A I s.1 i)) ?_)
    (by iicf_perm)
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono (trailAssn_pack (dflt := dflt) (n := n) (A, T, t) hwf) (entails_refl _))
  simp only [hnCtxt_def]
  ac_rfl

/-! ### `tset` -/

/-- The compound program `sepref_synth` produced for `tset`. -/
def tsetCom (A T t I V one : String) : Com :=
  .seq (.aset T t I) (.seq (.binop .add t t one) (.seq (.aset A I V) (.seq .skip .skip)))

@[sepref_fr_rules]
theorem hnr_mop_tset (dflt n : ℕ) (A T t I V one : String) (s : List ℕ × ℕ) (i v : ℕ) :
    hnRefine (hnCtxt (trailAssn dflt n) s (A, T, t) ∗ hnCtxt natAssn i I ∗
        hnCtxt natAssn v V ∗ hnCtxt natAssn 1 one)
      (tsetCom A T t I V one)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn v V ∗ hnCtxt natAssn 1 one)
      (A, T, t) (trailAssn dflt n) (mop_tset n s i v) := by
  refine hnr_trail_pre fun tr hwf => ?_
  show hnRefine _ _ _ _ _ (NRest.bindT (NRest.assert (i < n ∧ s.2 < n)) _)
  refine hnr_assert fun hcond => ?_
  obtain ⟨hi, hk⟩ := hcond
  have hk' : s.2 < tr.length := by rw [hwf.trail_len]; exact hk
  have hi' : i < s.1.length := by rw [hwf.data_len]; exact hi
  have hraw := tsetSynth A T t I V one s.1 tr s.2 i v
  rw [tsetRaw_eq s.1 tr s.2 i v hk' hi'] at hraw
  refine hnRefine_cons_pre (hnRefine_res_cast' hraw ?_) (by iicf_perm)
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono (entails_refl _)
      (trailAssn_pack (dflt := dflt) (n := n) (A, T, t) (trailWf_push hwf hi hk)))
  simp only [hnCtxt_def, prodAssn_apply, emp_sepConj]

/-! ### `treset` -/

/-- The compound program `sepref_synth` produced for `treset`: the pop
loop. -/
def resetCom (A T t P J D one : String) : Com :=
  .while (.lt (.lit 0) (.cell t))
    (.seq (.binop .sub P t one)
      (.seq (.aget J T P) (.seq (.aset A J D) (.seq (.binop .sub t t one) .skip))))

@[sepref_fr_rules]
theorem hnr_mop_treset (dflt n : ℕ) (A T t P J D one : String) (s : List ℕ × ℕ) :
    hnRefine (hnCtxt (trailAssn dflt n) s (A, T, t) ∗ junkCell P ∗ junkCell J ∗
        hnCtxt natAssn dflt D ∗ hnCtxt natAssn 1 one)
      (resetCom A T t P J D one)
      (junkCell P ∗ junkCell J ∗ hnCtxt natAssn dflt D ∗ hnCtxt natAssn 1 one)
      (A, T, t) (trailAssn dflt n) (mop_treset dflt n s) := by
  refine hnr_trail_pre fun tr hwf => ?_
  have hraw := resetSynth A T t P J D one dflt n s.1 tr s.2 (reset_variant dflt n tr)
  rw [resetLoop_value dflt n tr s.2 s.1 hwf] at hraw
  refine hnRefine_cons_pre (hnRefine_res_cast' hraw ?_) (by iicf_perm)
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono (entails_refl _)
      (trailAssn_pack (dflt := dflt) (n := n) (A, T, t) (trailWf_empty hwf.trail_len)))
  simp only [hnCtxt_def, prodAssn_apply]
  ac_rfl

/-! ## 7. The characteristic theorem — reset is touched-only

This is what the whole file is for. `treset`'s price is a function of
the touch counter alone: the array's length does not occur in it, so a
program that writes `k` slots of a length-`n` array and resets pays
Θ(k), not Θ(n). That is the ND-MC discipline
(`touched-only-costs.md`) as a *type*, not a review reminder. -/

/-- The price of resetting a trail array, as a function of the abstract
state. Note what it is a function of. -/
noncomputable def trailResetCost (s : List ℕ × ℕ) : ECost := resetCost s.2

theorem mop_treset_eq (dflt n : ℕ) (s : List ℕ × ℕ) :
    mop_treset dflt n s
      = NRest.consume (NRest.returnT (List.replicate n dflt, 0)) (trailResetCost s) := rfl

/-- **The characteristic theorem.** Two trail arrays whose touch
counters agree cost exactly the same to reset — whatever their lengths,
whatever their contents. Resetting a length-1000 array that was written
twice costs what resetting a length-2 array that was written twice
costs. -/
theorem treset_cost_touched_only {s₁ s₂ : List ℕ × ℕ} (h : s₁.2 = s₂.2) :
    trailResetCost s₁ = trailResetCost s₂ := by
  rw [trailResetCost, trailResetCost, h]

/-- …and the quantitative half: one more touch is exactly one more pop
plus one more guard evaluation. Linear in the counter, with no constant
term that depends on `n`. -/
theorem resetCost_succ (k : ℕ) :
    resetCost (k + 1) = resetCost k + (resetStepCost + irUnit Currency.«while») := by
  simp only [resetCost, succ_nsmul]
  abel

/-- The empty reset: nothing to pop, one guard evaluation. -/
theorem resetCost_zero : resetCost 0 = irUnit Currency.«while» := by simp [resetCost]

/-! ### The costs, pinned

Concrete per-currency readings, at *two different array lengths with the
same touch counter* — which is the theorem above, computed. -/

theorem resetCost_aset : (resetCost 2).toFun Currency.aset = 2 := by decide +kernel
theorem resetCost_aget : (resetCost 2).toFun Currency.aget = 2 := by decide +kernel
theorem resetCost_sub : (resetCost 2).toFun Currency.sub = 4 := by decide +kernel
theorem resetCost_while : (resetCost 2).toFun Currency.«while» = 3 := by decide +kernel

/-- Length 8, two touches. -/
theorem trailResetCost_len8 :
    (trailResetCost (List.replicate 8 0, 2)).toFun Currency.aset = 2 := by decide +kernel

/-- Length 1000, two touches — the same price. -/
theorem trailResetCost_len1000 :
    (trailResetCost (List.replicate 1000 0, 2)).toFun Currency.aset = 2 := by decide +kernel

theorem tsetCost_aset : tsetCost.toFun Currency.aset = 2 := by decide +kernel
theorem tsetCost_add : tsetCost.toFun Currency.add = 1 := by decide +kernel
theorem tsetCost_skip : tsetCost.toFun Currency.skip = 2 := by decide +kernel

-- **Negative control.** Reset does not cost one write per *slot*.
/-- error: Tactic `decide` proved that the proposition
  (trailResetCost (List.replicate 8 0, 2)).toFun Currency.aset = 8
is false -/
#guard_msgs in
example : (trailResetCost (List.replicate 8 0, 2)).toFun Currency.aset = 8 := by decide +kernel

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_mop_treset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_treset

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_mop_tset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_tset

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.hnr_mop_tget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_tget

/-! ## 8. Init from junk (design D6-P6-2, `Iicf/Basic.lean` §2)

The replacement for the source's `*_new`. There is no allocation: the
caller already owns three cells of the right capacity, holding junk, and
`tinit` is the program that makes the invariant true of them. Note what
it is built from — `mop_array_fill`'s **registered rule**, consumed here
exactly as a consumer would consume it, through the same pipeline. The
trail array is *never touched*: its contents are ghost (P6/D-q) and any
capacity-`n` junk satisfies the invariant at `k = 0`.

**P6/D-v — init takes the top cell already holding `0`, it does not zero
it.** Zeroing would be a `mopConstN 0` whose destination is a *fresh*
metavariable at the point the operator phase chooses a rule, so — by the
same rule-preference limitation as P6/D-u — it lands in whichever junk
cell comes first, which after the fill is the fill's own scratch index.
The tuple-forming step `mopPair ys 0` has no such problem: its
destination is the judgment's `d`, fixed by the goal. So init's
precondition asks for `hnCtxt natAssn 0 t`, which a caller owns anyway
(every program of this shape sets up its literal cells first), and the
`ir.const` disappears from `tinitCost`. Fallback: the same three as
P6/D-u. -/

/-- **The abstract init**: fill the data array with the default; the top
is already zero (P6/D-v). -/
noncomputable def tinitProg (dflt : ℕ) (xs : List ℕ) : NRest (List ℕ × ℕ) ECost :=
  NRest.bindT (mop_array_fill xs dflt) fun ys => mopPair ys 0

/--
info: sepref_synth Lax13Proofs.Refine.Sepref.Iicf.tinitSynth:
  (fillCom i A D one N).seq Com.skip
-/
#guard_msgs in
sepref_synth tinitSynth (A t i D N one : String) (dflt : ℕ) (xs : List ℕ) :
  hnRefine (hnCtxt arrayAssn xs A ∗ junkCell i ∗ hnCtxt natAssn 0 t ∗ hnCtxt natAssn dflt D ∗
      hnCtxt natAssn xs.length N ∗ hnCtxt natAssn 1 one)
    _ _ (A, t) (arrayAssn ×ₐ natAssn)
    (tinitProg dflt xs)

/-- Init's price: the fill, and the tuple. -/
noncomputable def tinitCost (n : ℕ) : ECost := fillCost n + irUnit Currency.skip

theorem tinitProg_value (dflt : ℕ) (xs : List ℕ) :
    tinitProg dflt xs
      = NRest.consume (NRest.returnT (List.replicate xs.length dflt, 0))
          (tinitCost xs.length) := by
  show NRest.bindT (mop_array_fill xs dflt) _ = _
  rw [mop_array_fill_def, bindT_unit, mopPair_def, NRest.consume_consume]
  congr 1

/-- The compound program `sepref_synth` produced for `tinit`. -/
def tinitCom (A i D N one : String) : Com := .seq (fillCom i A D one N) .skip

/-- **Init from junk**: two capacity-`n` junk arrays and a zeroed top in,
a well-formed empty trail array out. The trail cell `T` is owned
throughout and never written. -/
theorem hnr_trail_init (dflt n : ℕ) (A T t i D N one : String) :
    hnRefine (junkArrayOfLen n A ∗ junkArrayOfLen n T ∗ junkCell i ∗ hnCtxt natAssn 0 t ∗
        hnCtxt natAssn dflt D ∗ hnCtxt natAssn n N ∗ hnCtxt natAssn 1 one)
      (tinitCom A i D N one)
      (junkCell i ∗ hnCtxt natAssn dflt D ∗ hnCtxt natAssn n N ∗ hnCtxt natAssn 1 one)
      (A, T, t) (trailAssn dflt n)
      (NRest.consume (NRest.returnT (List.replicate n dflt, 0)) (tinitCost n)) := by
  refine hnRefine_junkArrayOfLen fun xs hxs => ?_
  refine hnRefine_cons_pre
    (hnRefine_junkArrayOfLen (a := T) (n := n)
      (Γ := arrayAssn xs A ∗ junkCell i ∗ hnCtxt natAssn 0 t ∗ hnCtxt natAssn dflt D ∗
        hnCtxt natAssn n N ∗ hnCtxt natAssn 1 one) fun tr htr => ?_)
    (by iicf_perm)
  have hraw := tinitSynth A t i D N one dflt xs
  rw [tinitProg_value dflt xs, hxs] at hraw
  have hframe := hnRefine_frame' (F := arrayAssn tr T) hraw
  refine hnRefine_cons_pre (hnRefine_res_cast' hframe ?_) (by iicf_perm)
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono (entails_refl _)
      (trailAssn_pack (dflt := dflt) (n := n) (A, T, t) (trailWf_empty htr)))
  simp only [hnCtxt_def, prodAssn_apply, emp_sepConj]
  ac_rfl

end Iicf

end Lax13Proofs.Refine.Sepref
