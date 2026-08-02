import Lax13Proofs.Refine.Ir.SepSolver

/-!
P3's acceptance: hand-proved credit-carrying triples for array get, set
and fill, with every frame step discharged by the solver.

The campaign plan's P3 criterion is "hand-proved credit-carrying triples
for array get/set/fill". This file is those three, as *programs* — three
`Ir.Com` terms, not three restatements of `Triples.lean`'s rules — each
with a source-shaped triple whose credit vector is exact, and each
proved without a single hand rearrangement of a `∗`-list: the frame
inference is `Ir/SepSolver.lean`'s `fri`, applied through
`irTriple_frame` (the triple-level form of `htriple_vcg_frame_erule`,
judgment call D-ae there), and nothing in this file rewrites with
`sepConj_assoc`, `sepConj_comm`, `ac_rfl` or wave B's `irSTATE_rot`.

The three programs, in design record §6's op set:

| program | IR | price |
|---|---|---|
| get | `x := A[i]` | one `ir.aget` |
| set | `A[i] := v` | one `ir.aset` |
| fill | `while i < n do { A[i] := v; i := i + one }` | `(n+1)·ir.while + n·ir.aset + n·ir.add` |

The fill accounting is wave A's convention (judgment call D-d of
`Syntax.lean`): a loop charges one `ir.while` per *guard evaluation*, so
`n` iterations charge `n + 1` — `n` successful tests and the trailing
failed one. The body charges one `ir.aset` and one `ir.add` per
iteration. Those three lines are the `fillPayload` below, and the
loop invariant carries `k` copies of it for the `k` iterations still to
come — the ESOP'21 per-iteration discipline wave B's `cd_while`
introduced, here at a program that actually does something.

## Judgment calls

**D-ag — `n` is a cell, and the measure is the number of iterations
still to run.** Design record §6 has no `len` op (array lengths live in
the `↦ₐ` assertion), so the loop bound has to be *read from somewhere*:
it is the scalar cell `"n"`, owned by the invariant and never written.
Likewise `i := i + 1` needs its `1` in a cell (judgment call D-b of
`Syntax.lean`: binop operands are cells), so the program owns `"one"`.
The measure is `k`, the iterations remaining, with `i = n - k`; the
alternative — measuring by `i` and taking the well-founded relation to
be `InvImage (·<·) (n - ·)` — needs the same subtraction one level
further in, and `Nat.lt_wfRel.wf` is what wave B's loop example already
uses.

**D-ah — the bound `k ≤ n` rides in the invariant as a `⌜⌝`
conjunct.** `while_triple`'s body obligation is `∀ t, g t = true →
irTriple (Inv t) c …`, quantified over *every* value of the measure,
including the ones the loop can never reach. The invariant therefore has
to carry its own well-formedness, and `⌜k ≤ n⌝` is it; `irTriple_pure`
(`Ir/SepSolver.lean`) turns that conjunct back into a Lean hypothesis at
the top of the body proof, and `fri` re-establishes it at the end from
the same hypothesis through its side tactic. This is exactly the shape
the source's `↑⇩!` side conditions have — a pure conjunct of an
assertion, discharged by a solver — and wave B's D-u anticipated it.

**D-ai — the array's contents are `filled m val xs`, a prefix of
`val`s over the original.** `filled m val xs = replicate m val ++
xs.drop m` is the smallest description of "the first `m` entries have
been overwritten" that is *stable under one more write*
(`filled_set`) and that collapses to the whole array at `m = xs.length`
(`filled_all`). The alternative, `xs` iterated under `List.set`, needs a
fold to state and an induction to use.

**D-aj — the assertions are `def`s whose defining equations are
registered with `fri_prepare_simps`.** The solver matches conjuncts, so
it has to *see* the conjuncts: a named assertion is opaque to it. Rather
than spelling every precondition out at every call site, each named
assertion here contributes its own `rfl` equation to the
prepare-phase simp set, which is precisely the extension point
`Ir/Attrs.lean` documents ("a consumer that defines a bundled cost tags
its own splitting lemma here and the solver sees the parts"). The same
mechanism carries `fillPayload`'s three-way split.

**D-ak — the end-to-end run goes through the *exact* triple, not the
garbage-collecting one.** Wave B's D-v keeps both forms; `irHtriple`'s
postcondition absorbs unspent credits into `GC`, which is what a
composition wants and what a *measurement* does not — the point of the
run below is that the cost vector is exactly `(4, 3, 3)`, so the triple
that reaches `BigStep` is the one whose postcondition owns no slack.
The `GC` form is exercised separately, on the set program, so that
`irHtriple_frame` and the solver's `GC`-absorption path are covered too.
-/

namespace Lax13Proofs.Refine.Ir

namespace Examples

/-! ## 1. The array-shape lemmas

`filled m val xs` is `xs` with its first `m` entries overwritten by
`val` (judgment call D-ai). Three facts about it are all the loop needs:
its length, what one more write does to it, and what it is once every
entry has been written. -/

/-- The array after its first `m` entries have been overwritten with
`val`. -/
def filled (m : ℕ) (val : Val) (xs : List Val) : List Val :=
  List.replicate m val ++ xs.drop m

@[simp] theorem filled_zero (val : Val) (xs : List Val) : filled 0 val xs = xs := by
  simp [filled]

theorem filled_length (m : ℕ) (val : Val) (xs : List Val) (h : m ≤ xs.length) :
    (filled m val xs).length = xs.length := by
  simp [filled]; omega

/-- Writing `val` at the first not-yet-written index extends the prefix
by one — the one array fact the loop body needs. -/
theorem filled_set (m : ℕ) (val : Val) (xs : List Val) (h : m < xs.length) :
    (filled m val xs).set m val = filled (m + 1) val xs := by
  unfold filled
  rw [List.set_append_right m val (by simp)]
  simp only [List.length_replicate, Nat.sub_self, List.replicate_succ', List.append_assoc,
    List.drop_eq_getElem_cons h, List.set_cons_zero]
  simp

/-- Once the prefix covers the array, the array *is* the constant. -/
theorem filled_all (m : ℕ) (val : Val) (xs : List Val) (h : xs.length ≤ m) :
    filled m val xs = List.replicate m val := by
  simp [filled, List.drop_eq_nil_of_le h]

/-! ## 2. Array get

`x := A[i]`, with four names the program does not touch owned around
it and the precondition written in a scrambled order. The proof is one
`ir_frame` against wave B's array rule in its pure-side-condition form
(judgment call D-ad of `Ir/SepSolver.lean`): the solver finds the three
cells the rule wants among the seven on offer, discharges the index
bound as a `⌜⌝` conjunct, and instantiates the frame with the rest. -/

/-- `x := A[i]`. -/
def getProg : Com := .aget "x" "A" "i"

/-- Own the array, the index, the destination — and four names that have
nothing to do with the read, deliberately interleaved with them. -/
def getPre (k : Val) (xs : List Val) : Assn :=
  "p" ↦ᵥ 7 ∗ "i" ↦ᵥ k ∗ "B" ↦ₐ [9, 9] ∗ ¤¤Currency.aget 1 ∗ "A" ↦ₐ xs ∗ "q" ↦ᵥ 8 ∗ "x" ↦ᵥ 0

/-- After the read: the destination holds the entry, the array and the
unrelated state are untouched, and the credit is gone. -/
def getPost (k : Val) (xs : List Val) : Assn :=
  "x" ↦ᵥ xs.getD k 0 ∗ "A" ↦ₐ xs ∗ "i" ↦ᵥ k ∗ "p" ↦ᵥ 7 ∗ "B" ↦ₐ [9, 9] ∗ "q" ↦ᵥ 8

@[fri_prepare_simps] theorem getPre_def (k : Val) (xs : List Val) :
    getPre k xs =
      ("p" ↦ᵥ 7 ∗ "i" ↦ᵥ k ∗ "B" ↦ₐ [9, 9] ∗ ¤¤Currency.aget 1 ∗ "A" ↦ₐ xs ∗ "q" ↦ᵥ 8 ∗
        "x" ↦ᵥ 0) := rfl

@[fri_prepare_simps] theorem getPost_def (k : Val) (xs : List Val) :
    getPost k xs =
      ("x" ↦ᵥ xs.getD k 0 ∗ "A" ↦ₐ xs ∗ "i" ↦ᵥ k ∗ "p" ↦ᵥ 7 ∗ "B" ↦ₐ [9, 9] ∗ "q" ↦ᵥ 8) := rfl

/-- The get triple: exactly one `ir.aget` credit, and the frame is found
by the solver. -/
theorem get_triple (k : Val) (xs : List Val) (hk : k < xs.length) :
    irTriple (getPre k xs) getProg (getPost k xs) := by
  ir_frame (aget_triple_pure "x" "A" "i" 0 k xs)

/-! ## 3. Array set

The mirror image, and the place the garbage-collecting triple form gets
its exercise: `irHtriple`'s postcondition carries a `GC`, so the
solver's absorption path (judgment call D-ab) runs on the second side
condition. -/

/-- `A[i] := v`. -/
def setProg : Com := .aset "A" "i" "v"

/-- Own the array, the index, the value — and, again, unrelated state. -/
def setPre (k n : Val) (xs : List Val) : Assn :=
  "p" ↦ᵥ 7 ∗ ¤¤Currency.aset 1 ∗ "i" ↦ᵥ k ∗ "B" ↦ₐ [9, 9] ∗ "A" ↦ₐ xs ∗ "q" ↦ᵥ 8 ∗ "v" ↦ᵥ n

/-- After the write: the array is updated at the one index. -/
def setPost (k n : Val) (xs : List Val) : Assn :=
  "A" ↦ₐ xs.set k n ∗ "i" ↦ᵥ k ∗ "v" ↦ᵥ n ∗ "p" ↦ᵥ 7 ∗ "B" ↦ₐ [9, 9] ∗ "q" ↦ᵥ 8

@[fri_prepare_simps] theorem setPre_def (k n : Val) (xs : List Val) :
    setPre k n xs =
      ("p" ↦ᵥ 7 ∗ ¤¤Currency.aset 1 ∗ "i" ↦ᵥ k ∗ "B" ↦ₐ [9, 9] ∗ "A" ↦ₐ xs ∗ "q" ↦ᵥ 8 ∗
        "v" ↦ᵥ n) := rfl

@[fri_prepare_simps] theorem setPost_def (k n : Val) (xs : List Val) :
    setPost k n xs =
      ("A" ↦ₐ xs.set k n ∗ "i" ↦ᵥ k ∗ "v" ↦ᵥ n ∗ "p" ↦ᵥ 7 ∗ "B" ↦ₐ [9, 9] ∗ "q" ↦ᵥ 8) := rfl

/-- The set triple: exactly one `ir.aset` credit. -/
theorem set_triple (k n : Val) (xs : List Val) (hk : k < xs.length) :
    irTriple (setPre k n xs) setProg (setPost k n xs) := by
  ir_frame (aset_triple_pure "A" "i" "v" k n xs)

/-- …and the source's own triple form, whose postcondition absorbs
whatever the program did not spend. The second side condition is
`ENTAILS ((setPost ∗ GC) ∗ ?F) (setPost ∗ GC)`, so this is the
`GC`-absorption path (judgment call D-ab of `Ir/SepSolver.lean`) under
test. -/
theorem set_rule (k n : Val) (xs : List Val) (hk : k < xs.length) :
    irHtriple (setPre k n xs) setProg (setPost k n xs) := by
  ir_frame_gc (aset_rule_pure "A" "i" "v" k n xs)

/-! ## 4. Fill

`while i < n do { A[i] := v; i := i + one }`. -/

/-- The loop body: one write, one increment. -/
def fillBody : Com := .seq (.aset "A" "i" "v") (.add "i" "i" "one")

/-- The program. -/
def fill : Com := .while (.lt (.cell "i") (.cell "n")) fillBody

/-- What one iteration costs: its guard evaluation, its write, and its
increment. -/
def fillPayload : ECost :=
  ACost.cost Currency.«while» ((1 : ℕ) : ℕ∞) +
    (ACost.cost Currency.aset ((1 : ℕ) : ℕ∞) + ACost.cost Currency.add ((1 : ℕ) : ℕ∞))

/-- The payload as three atomic credit assertions — the
`fri_prepare_simps` extension point (judgment call D-aj), and what makes
one iteration's price visible to the solver as three conjuncts. -/
@[fri_prepare_simps] theorem credits_fillPayload :
    (¤fillPayload : Assn) = ¤¤Currency.«while» 1 ∗ ¤¤Currency.aset 1 ∗ ¤¤Currency.add 1 := by
  rw [fillPayload, credits_add, credits_add]
  rfl

/-- The invariant at "`k` iterations still to run": the index is `n - k`,
the array's first `n - k` entries are already `val`, and the balance
carries `k` payloads (judgment calls D-ag, D-ah). -/
def fillInv (n val : ℕ) (xs : List Val) (k : ℕ) : Assn :=
  ⌜k ≤ n⌝ ∗ ¤(k • fillPayload) ∗ "i" ↦ᵥ (n - k) ∗ "n" ↦ᵥ n ∗ "v" ↦ᵥ val ∗ "one" ↦ᵥ 1 ∗
    "A" ↦ₐ filled (n - k) val xs

@[fri_prepare_simps] theorem fillInv_def (n val : ℕ) (xs : List Val) (k : ℕ) :
    fillInv n val xs k =
      (⌜k ≤ n⌝ ∗ ¤(k • fillPayload) ∗ "i" ↦ᵥ (n - k) ∗ "n" ↦ᵥ n ∗ "v" ↦ᵥ val ∗ "one" ↦ᵥ 1 ∗
        "A" ↦ₐ filled (n - k) val xs) := rfl

/-- What the loop leaves: the index at `n`, every entry `val`, no
credits. -/
def fillPost (n val : ℕ) : Assn :=
  "i" ↦ᵥ n ∗ "n" ↦ᵥ n ∗ "v" ↦ᵥ val ∗ "one" ↦ᵥ 1 ∗ "A" ↦ₐ List.replicate n val

@[fri_prepare_simps] theorem fillPost_def (n val : ℕ) :
    fillPost n val =
      ("i" ↦ᵥ n ∗ "n" ↦ᵥ n ∗ "v" ↦ᵥ val ∗ "one" ↦ᵥ 1 ∗ "A" ↦ₐ List.replicate n val) := rfl

/-! ### One iteration

Stated with every index explicit — `m` before, `m'` after — so that the
solver's matches are syntactic and no arithmetic normalization is needed
at the conjunct level. Two `ir_frame`s: the write, then the increment. -/

theorem fill_step (n val : ℕ) (xs : List Val) (m m' j : ℕ) (hm' : m' = m + 1)
    (hmj : m + j + 1 = n) (hlen : xs.length = n) :
    irTriple
      (¤fillPayload ∗ ¤(j • fillPayload) ∗ "i" ↦ᵥ m ∗ "n" ↦ᵥ n ∗ "v" ↦ᵥ val ∗ "one" ↦ᵥ 1 ∗
        "A" ↦ₐ filled m val xs)
      fillBody
      (¤¤Currency.«while» 1 ∗ ¤(j • fillPayload) ∗ "i" ↦ᵥ m' ∗ "n" ↦ᵥ n ∗ "v" ↦ᵥ val ∗
        "one" ↦ᵥ 1 ∗ "A" ↦ₐ filled m' val xs) := by
  subst hm'
  have hmn : m < xs.length := by omega
  have hlenf : (filled m val xs).length = xs.length := filled_length m val xs (by omega)
  refine seq_triple
    (R := ¤¤Currency.add 1 ∗ ¤¤Currency.«while» 1 ∗ ¤(j • fillPayload) ∗ "i" ↦ᵥ m ∗ "n" ↦ᵥ n ∗
      "v" ↦ᵥ val ∗ "one" ↦ᵥ 1 ∗ "A" ↦ₐ (filled m val xs).set m val) ?_ ?_
  · ir_frame (aset_triple_pure "A" "i" "v" m val (filled m val xs))
    rw [hlenf]
    exact hmn
  · rw [filled_set m val xs hmn]
    ir_frame (binop_self_triple .add "i" "one" m 1)

/-! ### The three obligations of `while_triple` -/

/-- The guard is determined by the measure: with `k ≤ n` from the
invariant's own pure conjunct, `i < n` holds exactly when `k > 0`. Both
cells are read through the frame inferencer (`ptoVar_of_frame`), so this
proof rearranges nothing either. -/
theorem fill_guard (n val : ℕ) (xs : List Val) (F : Assn) (k : ℕ) (s : State) (cr : ECost)
    (h : irSTATE ((¤¤Currency.«while» 1 ∗ fillInv n val xs k) ∗ F) (s, cr)) :
    (Cond.lt (.cell "i") (.cell "n")).eval s = some (decide (0 < k)) := by
  have hkn : k ≤ n := pure_of_frame h (by fri)
  have hi : s.vars "i" = some (n - k) := ptoVar_of_frame h (by fri)
  have hn : s.vars "n" = some n := ptoVar_of_frame h (by fri)
  have hdec : decide (n - k < n) = decide (0 < k) := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    · have h1 : n - k < n := by omega
      simp [h1, hpos]
  simp only [Cond.eval_lt, Operand.eval_cell, hi, hn, Option.bind_some, Option.map_some, hdec]

/-- One iteration, as `while_triple` asks for it: pay the body, hand
back the next guard's credit, and land at a smaller measure. -/
theorem fill_body_triple (n val : ℕ) (xs : List Val) (hlen : xs.length = n) (k : ℕ)
    (hk : decide (0 < k) = true) :
    irTriple (fillInv n val xs k) fillBody
      (∃ᵃ k', ⌜k' < k⌝ ∗ ¤¤Currency.«while» 1 ∗ fillInv n val xs k') := by
  have hk0 : 0 < k := of_decide_eq_true hk
  refine irTriple_pure (fun hkn => ?_)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine irTriple_ex j ?_
  ir_frame (fill_step n val xs (n - (j + 1)) (n - j) j (by omega) (by omega) hlen)

/-- On exit the measure is zero, so the index is `n` and every entry has
been written. -/
theorem fill_exit (n val : ℕ) (xs : List Val) (hlen : xs.length = n) (k : ℕ)
    (hk : decide (0 < k) = false) : fillInv n val xs k ⊢ fillPost n val := by
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · simp [h] at hk
  subst hk0
  have harr : filled n val xs = List.replicate n val := filled_all n val xs (by omega)
  simp only [fillInv_def, Nat.sub_zero, harr]
  fri

/-- The loop: `k` iterations, `k` payloads, the measure is the number of
iterations still to run. -/
theorem fill_loop (n val : ℕ) (xs : List Val) (hlen : xs.length = n) :
    irTriple (¤¤Currency.«while» 1 ∗ fillInv n val xs n) fill (fillPost n val) :=
  while_triple (r := fun a b => a < b) Nat.lt_wfRel.wf (fill_guard n val xs)
    (fill_body_triple n val xs hlen) (fill_exit n val xs hlen) n

/-- **The fill triple.** Own the array, the four cells, and
`1 + n` guard credits' worth of payload; get back the constant array.
The credit vector is `(n + 1)` of `ir.while`, `n` of `ir.aset`, `n` of
`ir.add`, and nothing else — the leading `¤¤ir.while 1` is the trailing
*failed* guard test, and the `n` payloads are the `n` iterations. -/
theorem fill_triple (n val : ℕ) (xs : List Val) (hlen : xs.length = n) :
    irTriple
      (¤¤Currency.«while» 1 ∗ ¤(n • fillPayload) ∗ "i" ↦ᵥ 0 ∗ "n" ↦ᵥ n ∗ "v" ↦ᵥ val ∗
        "one" ↦ᵥ 1 ∗ "A" ↦ₐ xs)
      fill (fillPost n val) := by
  have h := fill_loop n val xs hlen
  simp only [fillInv_def, Nat.sub_self, filled_zero] at h
  exact irTriple_frame h (by fri) (by fri)

/-- The same in the source's garbage-collecting form. -/
theorem fill_rule (n val : ℕ) (xs : List Val) (hlen : xs.length = n) :
    irHtriple
      (¤¤Currency.«while» 1 ∗ ¤(n • fillPayload) ∗ "i" ↦ᵥ 0 ∗ "n" ↦ᵥ n ∗ "v" ↦ᵥ val ∗
        "one" ↦ᵥ 1 ∗ "A" ↦ₐ xs)
      fill (fillPost n val) := (fill_triple n val xs hlen).gc

/-! ## 5. End to end, and the gate (ledger D4)

The fill triple, taken all the way down: the precondition holds of a
concrete state, so the triple's `wp` holds, so the program *runs*, and
what it leaves behind — the array, and the cost vector, currency by
currency — is pinned. Then the same claim as a *family*, checked on
wave A's executable twin (`evalFuel`) over a range of `n`, which is what
turns "cost linear in `n`" from a sentence in the header into something
falsifiable. -/

namespace Gate

open Lax13Proofs.Refine.Ir.Gate (costVector readVars readArrs)

/-- Three zeroes, and the four cells the loop needs. -/
def fillDemoState : State :=
  State.ofPairs [("i", 0), ("n", 3), ("v", 7), ("one", 1)] [("A", [0, 0, 0])]

/-- The balance the triple asks for at `n = 3`: one guard credit for the
trailing failed test, plus three payloads. -/
def fillDemoBalance : ECost :=
  ACost.cost Currency.«while» ((1 : ℕ) : ℕ∞) + (3 : ℕ) • fillPayload

/-- Everything in the state the precondition does not own — which, at
this state, is nothing at all, but writing it as an `EXACT` resource is
what lets the assertion be checked by `rfl` rather than by
extensionality over the name space (wave B's `rtFrame`, same trick). -/
def fillDemoFrame : Assn :=
  EXACT ((((((vcells fillDemoState).erase "i").erase "n").erase "v").erase "one",
    (acells fillDemoState).erase "A", hcells fillDemoState), 0)

/-- The precondition and the frame, spelled as one right-nested
`∗`-list, checked conjunct by conjunct against the concrete state. -/
theorem fillDemoRaw :
    irSTATE (¤¤Currency.«while» 1 ∗ ¤((3 : ℕ) • fillPayload) ∗ "i" ↦ᵥ 0 ∗ "n" ↦ᵥ 3 ∗
      "v" ↦ᵥ 7 ∗ "one" ↦ᵥ 1 ∗ "A" ↦ₐ [0, 0, 0] ∗ fillDemoFrame)
      (fillDemoState, fillDemoBalance) := by
  show (¤¤Currency.«while» 1 ∗ ¤((3 : ℕ) • fillPayload) ∗ "i" ↦ᵥ 0 ∗ "n" ↦ᵥ 3 ∗
      "v" ↦ᵥ 7 ∗ "one" ↦ᵥ 1 ∗ "A" ↦ₐ [0, 0, 0] ∗ fillDemoFrame)
    ((vcells fillDemoState, acells fillDemoState, hcells fillDemoState), fillDemoBalance)
  rw [costCredits_def]
  refine credits_sepConj_iff.2 ⟨_, rfl, ?_⟩
  refine credits_sepConj_iff.2 ⟨0, (add_zero _).symm, ?_⟩
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact ptoArr_sepConj_iff.2 ⟨rfl, rfl⟩

/-- …in the shape the triple consumes. The re-association is the
solver's, not a hand `sepConj_assoc` chain. -/
theorem fillDemo_holds :
    irSTATE ((¤¤Currency.«while» 1 ∗ ¤((3 : ℕ) • fillPayload) ∗ "i" ↦ᵥ 0 ∗ "n" ↦ᵥ 3 ∗
      "v" ↦ᵥ 7 ∗ "one" ↦ᵥ 1 ∗ "A" ↦ₐ [0, 0, 0]) ∗ fillDemoFrame)
      (fillDemoState, fillDemoBalance) :=
  start_entailsE fillDemoRaw (by fri)

/-- The executable twin's answer, as data. -/
def fillDemoOut : State × Cost := (evalFuel 30 fill fillDemoState).getD (fillDemoState, 0)

theorem fillDemo_evalFuel : evalFuel 30 fill fillDemoState = some fillDemoOut := rfl

theorem fillDemo_bigStep : BigStep fill fillDemoState fillDemoOut.1 fillDemoOut.2 :=
  bigStep_of_evalFuel fillDemo_evalFuel

-- The state the run leaves, and its cost vector: three writes, three
-- increments, and *four* guard evaluations for three iterations.
#guard readVars fillDemoOut.1 ["i", "n", "v", "one"]
  = [("i", some 3), ("n", some 3), ("v", some 7), ("one", some 1)]

#guard readArrs fillDemoOut.1 ["A"] = [("A", some [7, 7, 7])]

#guard costVector fillDemoOut.2 =
  [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 0), ("ir.aset", 3),
   ("ir.ite", 0), ("ir.while", 4), ("ir.add", 3), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-- **End to end.** The triple's precondition holds of `fillDemoState`,
so the triple hands back a derivation; the array is read off the
postcondition through the solver, and the cost is the vector the
`#guard` above pinned — `n + 1 = 4` guard evaluations, `n = 3` writes,
`n = 3` increments, and nothing else. -/
theorem fill_runs :
    ∃ s' κ, BigStep fill fillDemoState s' κ ∧ s'.arrs "A" = some [7, 7, 7] ∧
      κ.toFun Currency.«while» = 4 ∧ κ.toFun Currency.aset = 3 ∧
      κ.toFun Currency.add = 3 ∧ κ.toFun Currency.aget = 0 := by
  obtain ⟨s', κ, hrun, hpost, -⟩ :=
    fill_triple 3 7 [0, 0, 0] rfl fillDemoFrame (fillDemoState, fillDemoBalance) fillDemo_holds
  refine ⟨s', κ, hrun, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : irSTATE (fillPost 3 7 ∗ fillDemoFrame)
        (s', minusECost fillDemoBalance κ) := hpost
    have harr : s'.arrs "A" = some (List.replicate 3 7) := ptoArr_of_frame hp (by fri)
    simpa using harr
  all_goals
    obtain ⟨-, rfl⟩ := hrun.unique fillDemo_bigStep
    rfl

/-! ### The cost, as a function of `n`

The header's claim is `(n + 1)·ir.while + n·ir.aset + n·ir.add`. Wave A's
`evalFuel` twin agrees with `BigStep` in both directions
(`bigStep_iff_exists_evalFuel`), so a Plausible check on the twin is a
check on the semantics — and these are the checks that would have caught
an off-by-one in the guard accounting. -/

/-- An `n`-cell array of zeroes, and the loop's four cells. -/
def fillState (n val : ℕ) : State :=
  State.ofPairs [("i", 0), ("n", n), ("v", val), ("one", 1)] [("A", List.replicate n 0)]

/-- Enough fuel for `n` iterations of a two-statement body. -/
def fillFuel (n : ℕ) : ℕ := 3 * n + 8

-- The loop fills the array…
#test ∀ m : ℕ, ((evalFuel (fillFuel (m % 6)) fill (fillState (m % 6) 7)).map
  fun r => r.1.arrs "A") = some (some (List.replicate (m % 6) 7))

-- …leaves the index at `n`…
#test ∀ m : ℕ, ((evalFuel (fillFuel (m % 6)) fill (fillState (m % 6) 7)).map
  fun r => r.1.vars "i") = some (some (m % 6))

-- …charges `n + 1` guard evaluations…
#test ∀ m : ℕ, ((evalFuel (fillFuel (m % 6)) fill (fillState (m % 6) 7)).map
  fun r => r.2.toFun Currency.«while») = some (m % 6 + 1)

-- …exactly `n` writes…
#test ∀ m : ℕ, ((evalFuel (fillFuel (m % 6)) fill (fillState (m % 6) 7)).map
  fun r => r.2.toFun Currency.aset) = some (m % 6)

-- …exactly `n` increments…
#test ∀ m : ℕ, ((evalFuel (fillFuel (m % 6)) fill (fillState (m % 6) 7)).map
  fun r => r.2.toFun Currency.add) = some (m % 6)

-- …and nothing in any other currency.
#test ∀ m : ℕ, ((evalFuel (fillFuel (m % 6)) fill (fillState (m % 6) 7)).map
  fun r => r.2.toFun Currency.aget) = some 0

/-! ### Negative controls -/

-- The off-by-one that the `n + 1` convention exists to prevent: the run
-- from `n = 3` does *not* pay three guard credits.
#guard ¬ (fillDemoOut.2.toFun Currency.«while» = 3)

/-- …and not merely for the evaluator: by determinism, no derivation
pays three. -/
theorem fill_no_wrong_cost {s' : State} {κ : Cost} (h : BigStep fill fillDemoState s' κ) :
    κ.toFun Currency.«while» ≠ 3 := by
  obtain ⟨-, rfl⟩ := BigStep.unique fillDemo_bigStep h
  decide

/-- The get triple is not derivable without its credit: the solver
cannot find an `ir.aget` conjunct, and says which one it wanted. -/
example : True := by
  fail_if_success
    (have : irTriple ("x" ↦ᵥ 0 ∗ "A" ↦ₐ [3, 1, 4] ∗ "i" ↦ᵥ 1) getProg
        ("x" ↦ᵥ 1 ∗ "A" ↦ₐ [3, 1, 4] ∗ "i" ↦ᵥ 1) := by
      ir_frame (aget_triple_pure "x" "A" "i" 0 1 [3, 1, 4]))
  trivial

/-- Nor with the wrong currency's credit. -/
example : True := by
  fail_if_success
    (have : irTriple (¤¤Currency.aset 1 ∗ "x" ↦ᵥ 0 ∗ "A" ↦ₐ [3, 1, 4] ∗ "i" ↦ᵥ 1) getProg
        ("x" ↦ᵥ 1 ∗ "A" ↦ₐ [3, 1, 4] ∗ "i" ↦ᵥ 1) := by
      ir_frame (aget_triple_pure "x" "A" "i" 0 1 [3, 1, 4]))
  trivial

/-- And the fill triple is not derivable with one payload too few: the
invariant would have to hand the last iteration credits it does not
hold. -/
example : True := by
  fail_if_success
    (have : irTriple
        (¤¤Currency.«while» 1 ∗ ¤((2 : ℕ) • fillPayload) ∗ "i" ↦ᵥ 0 ∗ "n" ↦ᵥ 3 ∗ "v" ↦ᵥ 7 ∗
          "one" ↦ᵥ 1 ∗ "A" ↦ₐ [0, 0, 0]) fill (fillPost 3 7) := by
      exact fill_triple 3 7 [0, 0, 0] rfl)
  trivial

end Gate

end Examples

end Lax13Proofs.Refine.Ir
