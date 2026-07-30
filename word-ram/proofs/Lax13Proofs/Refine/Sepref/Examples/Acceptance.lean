import Lax13Proofs.Refine.Sepref.Definition

/-!
P4's acceptance: two abstract programs, written at the user layer,
exchanged into the IR's currencies through `⇓C irE`, and **synthesized**
into deep `Ir.Com` programs by `sepref_synth`.

The campaign plan's P4 criterion is "an abstract program with a loop and
a branch, pushed through the exchange route and turned into a `Com` by
the tool, with the tool's output pinned". This file is two such
programs — one for each half of the criterion, and neither of them a
restatement of a rule:

| program | what it exercises |
|---|---|
| **filter-count** | a branch *inside* a loop body: `hnr_If` under `hnr_while_var`, the `MERGE` of two in-place branch posts, a scratch cell live across the branch, and the `MIf`-to-`irIf` exchange (`timerefine_MIf`, an *equality*) |
| **in-place array reverse** | a mutating loop: the array lives *in the loop state*, `hnr_mop_aset`'s linearity moves its ownership twice per iteration, two scratch cells are consumed and junked inside the body, and the state is a nested `prodAssn` |

Both go the whole way. The chain, per program, is

```
user program (source currencies)
  ──⇓C irE──▶  concrete-layer program (ir currencies)   [exchange, §2]
  ──sepref_synth──▶  Ir.Com                             [synthesis, §3/§4]
  ──hnRefine_ref──▶  hnRefine … (⇓C irE userProg)       [the corollary]
```

and the corollary is the point: the cost bound the synthesized `Com`
carries is a bound on the *user* program's exchanged cost, so a caller
who writes at `''if''`/`''call''` never has to know the IR's currencies.

Not one clause of `∗`-rearrangement is written by hand anywhere below —
see the telemetry block at the end, which is the plan's frame-clause
count.

## Judgment calls (P4/D-ea …)

**P4/D-ea — the user layer's loop is `monadic_WHILEIT`, not
`whileIET`.** The brief names `whileIET`; P1's `whileIET I E b c` is
*definitionally* `whileT b c` (`NREST/Combinators.lean`, the source's own
`whileIET_def`), which charges **no currency at all**. There is therefore
nothing for `⇓C` to exchange at a `whileIET`, and `Sepref/IrOps.lean` §5
proves the loop exchange at `monadicWhileIT` — the combinator that does
pay `cost ''call'' 1` per iteration, which is what `irE` buys at
`ir.while`. So the user-layer loop here is `NRest.monadicWhileIT I
(fun s => returnT (bf s)) g s₀`, the pure-guard instance the exchange
lemma is stated at. Fallback: none needed; `monadicWhileIET I E …` is
`monadicWhileIT I …` by `rfl`, so a caller who wants the energy
annotation writes it and nothing below changes.

**P4/D-eb — only the *structural* currencies are exchanged; the
operations are already at the IR's.** P1's user layer has no array or
scalar operations at all (its `NREST.thy` port is the monad and the
combinators; the `mop_…` layer is ours, `Sepref/IrOps.lean` §1, and by
design record F4 each `mop` is pinned to the IR's own currency). So a
"user program" that is honest about what exists writes the *operations*
at the mop layer and the *control flow* at the source's currencies, and
`⇓C irE` reprices exactly the control flow. Filter-count therefore
exchanges a real `MIf` (`''if''` → `ir.ite`) and a real
`monadicWhileIT` (`''call''` → `ir.while`); reverse, which has no
branch, exchanges only the loop, and its body is a fixed point of the
exchange (§2's per-`mop` invariance lemmas). Fallback when P6's IICF
layer lands with cost-parametric operations: the `ExchOk` calculus of §2
is what a genuinely two-layer program composes through, unchanged.

**P4/D-ec — reverse's destination is the loop state, not the array
cell.** The wave-C handoff expected `d = "A"` with the result assertion
`arrayAssn xs.reverse "A"`. The loop rule forbids it:
`hnr_while_var`'s body judgment is
`hnRefine (hnCtxt Rs s d ∗ Γ) cbody Γ d Rs (f s)` — the frame `Γ` is the
same before and after the body, so *everything the body mutates must be
in `Rs s d`*, and reverse mutates the array. So the loop state is the
triple `(i, j, xs)` at `d = ("i", "j", "A")` with
`Rs = natAssn ×ₐ natAssn ×ₐ arrayAssn`, and the array is its third
component. `rvLoop_array` below then weakens the two index components to
junk through `hnRefine_cons_res`, which *is* the handoff's statement —
`arrayAssn` at `"A"`, with the indices' cells owned but dead. Fallback:
a projection operation (`mop_fst`-style) would let the top-level program
end at the array alone; it is one rule and one `Com.skip`, and nothing
else would change.

**P4/D-ed — the loop invariants carry exactly what the *variant* needs,
and nothing else.** `hnr_mop_aget`/`hnr_mop_aset` discharge their index
bounds internally (`hnr_assert`, Tool.lean's P4/D-cs), so a bound is
never a synthesis obligation; the only consumer of `I` is
`LOOP_VARIANT`, which has to know the body's *value* and so needs the
bounds. Filter-count's guard already implies its bound, so `fcI` is
`True`; reverse's does not, so `rvI s` is `s.1 < s.2.1 → s.2.1 <
s.2.2.length` — an implication rather than a conjunction, so that the
initial state of an *empty* array satisfies it and the theorem is not
vacuous there.

**P4/D-ee — the `else` branch of filter-count is `acc := acc + zero`.**
The mop layer has no in-place no-op: `mopCopy` at `x = y` is the aliased
instance `hnr_mop_copy` is inapplicable at (P4/D-ac), and `mopPair`
cannot deliver a scalar. Both branches must write the same destination
in place for the `MERGE` to be `hnCtxt`-for-`hnCtxt`, so the `else`
branch adds a cell holding `0`. This is what a real compiler emits for a
branch that must leave a register defined, and it keeps the branch
merge honest: the two posts are permutations of one another, which is
what `mergeSolve` reconciles. Fallback: a `mop_skip` at `ir.skip` with
an in-place rule would replace it, at the price of one more rule.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

namespace Acceptance

/-! ## 1. Refute before prove

Both abstract programs are *executed* before anything is proved about
them, on concrete inputs, through computable twins of their own step and
guard functions. The twins are not independent specifications: `fcBf`,
`fcStep`, `rvBf` and `rvStep` are the very functions the abstract bodies
are proved equal to in §3 and §4 (`fcF_eq`, `rvF_eq`), so a `#guard`
here is a `#guard` about the abstract program.

Three of the guards are deliberately wrong and pinned as errors — the
standing refute-before-prove control that the checks can fail. -/

/-! ### Filter-count -/

/-- The loop guard: `k < |xs|`, read from the cell `"n"`. -/
def fcBf (xs : List ℕ) : ℕ × ℕ → Bool := fun s => decide (s.1 < xs.length)

/-- One iteration: read `xs[k]`, bump the accumulator if it is below the
threshold, advance. -/
def fcStep (xs : List ℕ) (t : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  (s.1 + 1, s.2 + (if xs[s.1]! < t then 1 else 0))

/-- The twin loop: the guard and the step, iterated. -/
def fcRun (xs : List ℕ) (t : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | k + 1, s => if fcBf xs s then fcRun xs t k (fcStep xs t s) else s

/-- What the abstract program computes: the accumulator at exit. -/
def fcCount (xs : List ℕ) (t : ℕ) : ℕ := (fcRun xs t xs.length (0, 0)).2

#guard fcCount [3, 1, 4, 1, 5] 4 = 3
#guard fcCount [3, 1, 4, 1, 5] 0 = 0
#guard fcCount [3, 1, 4, 1, 5] 6 = 5
#guard fcCount [] 4 = 0
-- …and against an independent decider of the same property.
#guard fcCount [3, 1, 4, 1, 5] 4 = ([3, 1, 4, 1, 5].filter (fun v => decide (v < 4))).length

-- **Negative control.** A wrong expected count fails, and says so.
/--
error: Expression
  decide (fcCount [3, 1, 4, 1, 5] 4 = 4)
did not evaluate to `true`
-/
#guard_msgs in
#guard fcCount [3, 1, 4, 1, 5] 4 = 4

/-! ### In-place reverse -/

/-- The loop guard: `i < j`. -/
def rvBf : ℕ × ℕ × List ℕ → Bool := fun s => decide (s.1 < s.2.1)

/-- The loop invariant, as a decidable twin (`rvI` below is the `Prop`).
The abstract loop `assert`s it at every entry, so a run that violates it
*fails*; the twin therefore returns `none` there. -/
def rvIb (s : ℕ × ℕ × List ℕ) : Bool :=
  !decide (s.1 < s.2.1) || decide (s.2.1 < s.2.2.length)

/-- One iteration: swap `xs[i]` and `xs[j]`, then close the gap. -/
def rvStep (s : ℕ × ℕ × List ℕ) : ℕ × ℕ × List ℕ :=
  (s.1 + 1, s.2.1 - 1, (s.2.2.set s.1 s.2.2[s.2.1]!).set s.2.1 s.2.2[s.1]!)

/-- The twin loop, failing exactly where the abstract one does. -/
def rvRun : ℕ → ℕ × ℕ × List ℕ → Option (ℕ × ℕ × List ℕ)
  | 0, s => if rvIb s then some s else none
  | k + 1, s => if rvIb s then (if rvBf s then rvRun k (rvStep s) else some s) else none

/-- What the abstract program computes: the array at exit. -/
def rvOut (xs : List ℕ) : Option (List ℕ) :=
  (rvRun xs.length (0, xs.length - 1, xs)).map (·.2.2)

#guard rvOut [1, 2, 3, 4] = some [4, 3, 2, 1]
#guard rvOut [5] = some [5]
#guard rvOut [] = some []
-- …and, on every input below, it is `List.reverse` — the honest check,
-- since the theorems of §4 are about the loop, not about `List.reverse`.
#guard rvOut [1, 2, 3, 4] = some (List.reverse [1, 2, 3, 4])
#guard rvOut [1, 2, 3, 4, 5] = some (List.reverse [1, 2, 3, 4, 5])
#guard rvOut [7, 7, 0] = some (List.reverse [7, 7, 0])
#guard rvOut [5] = some (List.reverse [5])
#guard rvOut [] = some (List.reverse ([] : List ℕ))

-- **Negative control 1.** A wrong expected array fails.
/--
error: Expression
  decide (rvOut [1, 2, 3, 4] = some [1, 2, 3, 4])
did not evaluate to `true`
-/
#guard_msgs in
#guard rvOut [1, 2, 3, 4] = some [1, 2, 3, 4]

-- **Negative control 2.** The invariant is load-bearing: started outside
-- it, the abstract loop *fails* rather than computing a reverse.
/--
error: Expression
  decide (Option.map (fun x => x.2.2) (rvRun 4 (0, 9, [1, 2, 3])) = some [3, 2, 1])
did not evaluate to `true`
-/
#guard_msgs in
#guard (rvRun 4 (0, 9, [1, 2, 3])).map (·.2.2) = some [3, 2, 1]

#guard (rvRun 4 (0, 9, [1, 2, 3])).map (·.2.2) = none

/-! ## 2. The exchange route (`⇓C irE`)

`Sepref/IrOps.lean` §4–5 supplies the two structural exchange lemmas —
`timerefine_irE_MIf` (an equality) and `irWhileIT_le_timerefine_irE` (a
≤, with a variant). What is missing for a whole *program* is the rest of
the congruence: `⇓C irE` fixes every `mop` (they are already at ir
currencies, and `irE` is the identity there), and it passes through
`bindT` in the useful direction. `ExchOk` packages the three cases so a
program's exchange proof is one term with the program's own shape. -/

/-- `⇓C irE` fixes a one-op program at an ir currency. -/
theorem timerefine_irE_unitT {α : Type} (x : α) (n : String) (h₁ : n ≠ "if") (h₂ : n ≠ "call") :
    timerefine irE (NRest.consume (NRest.returnT x) (irUnit n))
      = NRest.consume (NRest.returnT x) (irUnit n) := by
  rw [timerefine_consume wfR''_irE, timerefineA_cost_one, irE_other h₁ h₂, timerefine_returnT]

theorem timerefine_irE_mopBinop (op : Imp.Bop) (m n : ℕ) :
    timerefine irE (mopBinop op m n) = mopBinop op m n := by
  rw [mopBinop_def]
  exact timerefine_irE_unitT _ _ (by cases op <;> decide) (by cases op <;> decide)

theorem timerefine_irE_mopAget (xs : List ℕ) (i : ℕ) :
    timerefine irE (mopAget xs i) = mopAget xs i := by
  rw [mopAget_def]
  by_cases h : i < xs.length
  · rw [NRest.assert_pos h, NRest.returnT_bindT]
    exact timerefine_irE_unitT _ _ (by decide) (by decide)
  · rw [NRest.assert_neg h, NRest.bindT_fail, timerefine_fail]

theorem timerefine_irE_mopAset (xs : List ℕ) (i v : ℕ) :
    timerefine irE (mopAset xs i v) = mopAset xs i v := by
  rw [mopAset_def]
  by_cases h : i < xs.length
  · rw [NRest.assert_pos h, NRest.returnT_bindT]
    exact timerefine_irE_unitT _ _ (by decide) (by decide)
  · rw [NRest.assert_neg h, NRest.bindT_fail, timerefine_fail]

theorem timerefine_irE_mopPair {α₁ α₂ : Type} (a₁ : α₁) (a₂ : α₂) :
    timerefine irE (mopPair a₁ a₂) = mopPair a₁ a₂ := by
  rw [mopPair_def]
  exact timerefine_irE_unitT _ _ (by decide) (by decide)

/-- **The exchange judgment**: the ir-currency program `m` costs no more
than the exchanged user program `mu`. This is the direction `hnRefine`
transfers along (`hnRefine_ref` is monotone upward in the abstract
program), and the direction `Sepref/IrOps.lean` §5 proves at the loop. -/
def ExchOk {α : Type} (m mu : NRest α ECost) : Prop := m ≤ timerefine irE mu

/-- An operation the exchange fixes. -/
theorem ExchOk.of_eq {α : Type} {m mu : NRest α ECost} (h : timerefine irE mu = m) :
    ExchOk m mu := le_of_eq h.symm

/-- The `bindT` congruence: `⇓C` distributes over a bind in this
direction only (P1 delta T7, `timerefine_bindT_ge`), which is exactly the
one the judgment wants. -/
theorem ExchOk.bind {α β : Type} {m mu : NRest α ECost} {f fu : α → NRest β ECost}
    (hm : ExchOk m mu) (hf : ∀ x, ExchOk (f x) (fu x)) :
    ExchOk (NRest.bindT m f) (NRest.bindT mu fu) :=
  le_trans (NRest.bindT_mono hm hf) (timerefine_bindT_ge wfR''_irE mu fu)

/-- The branch congruence, off `timerefine_MIf`'s *equality*: the
source's `''if''` unit buys the IR's `ir.ite` unit exactly, so nothing is
lost here. -/
theorem ExchOk.irIf {α : Type} {b : Bool} {t e tu eu : NRest α ECost}
    (ht : ExchOk t tu) (he : ExchOk e eu) : ExchOk (irIf b t e) (NRest.MIf b tu eu) := by
  rw [ExchOk, timerefine_irE_MIf, irIf_def, irIf_def]
  refine NRest.consume_mono ?_ le_rfl
  cases b <;> simpa using ‹_›

/-- The loop congruence in the *body*: `irWhileIT` is monotone in `f`,
so a body-wise exchange lifts to the loop. `RECT_mono` at the
`consume`-wrapped body functional `irWhileIT` is built from. -/
theorem irWhileIT_mono {σ : Type} {I : σ → Prop} {bf : σ → Bool} {f f' : σ → NRest σ ECost}
    (h : ∀ s, f s ≤ f' s) (s : σ) : irWhileIT I bf f s ≤ irWhileIT I bf f' s := by
  refine NRest.consume_mono ?_ le_rfl
  refine RECT_mono (mono2_consume_call (mono2_irWhileBody I bf f) (irUnit Currency.«while»))
    (fun F y => ?_) s
  simp only [irWhileBody_apply]
  refine NRest.bindT_mono le_rfl fun _ => ?_
  by_cases hy : bf y = true
  · rw [if_pos hy, if_pos hy]
    exact NRest.bindT_mono (h y) fun _ => le_rfl
  · rw [if_neg hy, if_neg hy]

/-- Binding a one-op program is charging its cost and going on: the one
normalization step every body-value lemma below runs on. -/
theorem bindT_unit {α β : Type} (x : α) (c : ECost) (f : α → NRest β ECost) :
    NRest.bindT (NRest.consume (NRest.returnT x) c) f = NRest.consume (f x) c := by
  rw [NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.returnT_bindT]

/-! ## 3. Filter-count

`acc := |{k < n | xs[k] < t}|`, as a loop over the pair state
`(k, acc)` in the cells `"k"` and `"acc"`, with the array read-only in
the frame. The branch inside the body is what nothing before this file
tested: `hnr_If` under `hnr_while_var`, with the scratch cell `"v"` live
across the branch and junked by the body's own `IMP` step. -/

/-- No invariant is needed: the guard already gives the index bound
(P4/D-ed). -/
def fcI : ℕ × ℕ → Prop := fun _ => True

/-- **The concrete-layer body.** `v := A[k]; if v < t then acc := acc + 1
else acc := acc + 0; k := k + 1; (k, acc)`. -/
noncomputable def fcF (xs : List ℕ) (t : ℕ) : ℕ × ℕ → NRest (ℕ × ℕ) ECost := fun s =>
  NRest.bindT (mopAget xs s.1) fun v =>
    NRest.bindT (irIf (decide (v < t)) (mopBinop .add s.2 1) (mopBinop .add s.2 0)) fun acc' =>
      NRest.bindT (mopBinop .add s.1 1) fun k' => mopPair k' acc'

/-- **The user-layer body**: the same program with the source's own
branch combinator, which pays `cost ''if'' 1` (P4/D-eb). -/
noncomputable def fcUF (xs : List ℕ) (t : ℕ) : ℕ × ℕ → NRest (ℕ × ℕ) ECost := fun s =>
  NRest.bindT (mopAget xs s.1) fun v =>
    NRest.bindT (NRest.MIf (decide (v < t)) (mopBinop .add s.2 1) (mopBinop .add s.2 0))
      fun acc' => NRest.bindT (mopBinop .add s.1 1) fun k' => mopPair k' acc'

/-- The body exchange, as one term with the body's shape. -/
theorem fcF_exch (xs : List ℕ) (t : ℕ) (s : ℕ × ℕ) : ExchOk (fcF xs t s) (fcUF xs t s) :=
  ExchOk.bind (.of_eq (timerefine_irE_mopAget _ _)) fun _ =>
    ExchOk.bind (ExchOk.irIf (.of_eq (timerefine_irE_mopBinop _ _ _))
        (.of_eq (timerefine_irE_mopBinop _ _ _))) fun _ =>
      ExchOk.bind (.of_eq (timerefine_irE_mopBinop _ _ _)) fun _ =>
        .of_eq (timerefine_irE_mopPair _ _)

/-- One iteration's price at the IR: a read, a branch, two additions and
the tuple. -/
noncomputable def fcCost : ECost :=
  irUnit Currency.aget + irUnit Currency.ite + irUnit Currency.add + irUnit Currency.add +
    irUnit Currency.skip

/-- …and at the user's currencies: the same, with `''if''` in place of
`ir.ite`. -/
noncomputable def fcUCost : ECost :=
  irUnit Currency.aget + irUnit "if" + irUnit Currency.add + irUnit Currency.add +
    irUnit Currency.skip

/-- **The concrete body's value** — the fact §1's twin is a twin of. -/
theorem fcF_eq (xs : List ℕ) (t : ℕ) (s : ℕ × ℕ) (h : s.1 < xs.length) :
    fcF xs t s = NRest.consume (NRest.returnT (fcStep xs t s)) fcCost := by
  show NRest.bindT (mopAget xs s.1) _ = _
  rw [mopAget_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, irIf_def,
    NRest.bindT_consume NRest.addSupContinuousB_acost]
  simp only [decide_eq_true_eq, fcStep, fcCost]
  by_cases hb : xs[s.1]! < t <;>
    simp only [hb, if_pos, if_false, mopBinop_def, mopPair_def, bindT_unit,
      NRest.consume_consume, Imp.Bop.apply_add, binopCurrency_add] <;>
    (congr 1; ac_rfl)

/-- **The user body's value**: the same result, the source's price. -/
theorem fcUF_eq (xs : List ℕ) (t : ℕ) (s : ℕ × ℕ) (h : s.1 < xs.length) :
    fcUF xs t s = NRest.consume (NRest.returnT (fcStep xs t s)) fcUCost := by
  show NRest.bindT (mopAget xs s.1) _ = _
  rw [mopAget_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, NRest.MIf,
    NRest.bindT_consume NRest.addSupContinuousB_acost]
  simp only [decide_eq_true_eq, fcStep, fcUCost]
  by_cases hb : xs[s.1]! < t <;>
    simp only [hb, if_pos, if_false, mopBinop_def, mopPair_def, bindT_unit,
      NRest.consume_consume, Imp.Bop.apply_add, binopCurrency_add] <;>
    (congr 1; ac_rfl)

/-- The two prices are the same price: `irE` buys `''if''` at `ir.ite`
and every other currency at itself. -/
theorem timerefineA_irE_fcUCost : timerefineA irE fcUCost = fcCost := by
  simp only [fcUCost, fcCost, timerefineA_add wfR''_irE, timerefineA_cost_one, irE_if,
    irE_other (show Currency.aget ≠ "if" by decide) (show Currency.aget ≠ "call" by decide),
    irE_other (show Currency.add ≠ "if" by decide) (show Currency.add ≠ "call" by decide),
    irE_other (show Currency.skip ≠ "if" by decide) (show Currency.skip ≠ "call" by decide)]

/-- The variant: the iterations still to run. -/
def fcV (xs : List ℕ) : ℕ × ℕ → ℕ := fun s => xs.length - s.1

/-- The variant obligation `sepref_synth` takes as an annotation
(P4/D-cv). -/
theorem fc_variant (xs : List ℕ) (t : ℕ) : LOOP_VARIANT fcI (fcBf xs) (fcF xs t) (fcV xs) := by
  intro s s' _ hb hle
  have h : s.1 < xs.length := by simpa [fcBf] using hb
  rw [fcF_eq xs t s h, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = fcStep xs t s := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hs'
  show xs.length - (s.1 + 1) < xs.length - s.1
  omega

/-- …and the same obligation at the *exchanged* body, which is what the
loop exchange lemma asks for. -/
theorem fc_variant_user (xs : List ℕ) (t : ℕ) : ∀ s s', fcI s → fcBf xs s = true →
    (NRest.returnT s' : NRest (ℕ × ℕ) ECost) ≤ timerefine irE (fcUF xs t s) →
    fcV xs s' < fcV xs s := by
  intro s s' _ hb hle
  have h : s.1 < xs.length := by simpa [fcBf] using hb
  rw [fcUF_eq xs t s h, timerefine_consume wfR''_irE, timerefine_returnT,
    timerefineA_irE_fcUCost, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = fcStep xs t s := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hs'
  show xs.length - (s.1 + 1) < xs.length - s.1
  omega

/-- **The user program**: the source's `monadic_WHILEIT` at a pure guard,
over the user-layer body (P4/D-ea). -/
noncomputable def fcUser (xs : List ℕ) (t : ℕ) : NRest (ℕ × ℕ) ECost :=
  NRest.monadicWhileIT fcI (fun s => NRest.returnT (fcBf xs s)) (fcUF xs t) (0, 0)

/-- **The exchange, whole**: body-wise through `ExchOk`, then the loop
through `Sepref/IrOps.lean` §5. -/
theorem fc_exchange (xs : List ℕ) (t : ℕ) :
    irWhileIT fcI (fcBf xs) (fcF xs t) (0, 0) ≤ timerefine irE (fcUser xs t) :=
  le_trans (irWhileIT_mono (fun s => fcF_exch xs t s) (0, 0))
    (irWhileIT_le_timerefine_irE (fcV xs) (fc_variant_user xs t) (0, 0))

/-! **The synthesis.** Seven owned conjuncts: the pair state, the
scratch cell the read lands in, the array, the threshold, the bound, and
the two constants the two in-place additions need (P4/D-ee). -/

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth fcLoop (xs : List ℕ) (t : ℕ)
    (hv : LOOP_VARIANT fcI (fcBf xs) (fcF xs t) (fcV xs)) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn) (0, 0) ("k", "acc") ∗ junkCell "v" ∗
      hnCtxt arrayAssn xs "A" ∗ hnCtxt natAssn t "t" ∗ hnCtxt natAssn xs.length "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero")
    _ _ ("k", "acc") (natAssn ×ₐ natAssn)
    (irWhileIT fcI (fcBf xs) (fcF xs t) (0, 0))

-- The synthesized program, pinned. The `ite` is the branch the
-- combinator phase built, its guard the fused `CondRefine` on `v < t`;
-- the trailing `skip` is `mopPair`.
#guard fcLoop_impl =
  Com.while (Cond.lt (Operand.cell "k") (Operand.cell "n"))
    (Com.seq (Com.aget "v" "A" "k")
      (Com.seq (Com.ite (Cond.lt (Operand.cell "v") (Operand.cell "t"))
          (Com.binop Imp.Bop.add "acc" "acc" "one") (Com.binop Imp.Bop.add "acc" "acc" "zero"))
        (Com.seq (Com.binop Imp.Bop.add "k" "k" "one") Com.skip)))

/-- The precondition, named. -/
def fcPre (xs : List ℕ) (t : ℕ) : Assn :=
  hnCtxt (natAssn ×ₐ natAssn) (0, 0) ("k", "acc") ∗ junkCell "v" ∗
    hnCtxt arrayAssn xs "A" ∗ hnCtxt natAssn t "t" ∗ hnCtxt natAssn xs.length "n" ∗
    hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero"

/-- The loop frame — the precondition minus the state, and the
postcondition the tool synthesized. Note `junkCell "v"`: the cell the
read used is owned and dead at the end of every iteration, which is what
makes the body's post the loop's frame. -/
def fcFrame (xs : List ℕ) (t : ℕ) : Assn :=
  junkCell "v" ∗ hnCtxt arrayAssn xs "A" ∗ hnCtxt natAssn t "t" ∗
    hnCtxt natAssn xs.length "n" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero"

/-- The synthesis theorem with the variant discharged. -/
theorem fcLoop' (xs : List ℕ) (t : ℕ) :
    hnRefine (fcPre xs t) fcLoop_impl (fcFrame xs t) ("k", "acc") (natAssn ×ₐ natAssn)
      (irWhileIT fcI (fcBf xs) (fcF xs t) (0, 0)) :=
  fcLoop xs t (fc_variant xs t)

/-- **The acceptance statement for filter-count**: the synthesized `Com`
refines the *user* program's exchange, so its cost bound is a bound on
the user program priced at `''if''`/`''call''`. -/
theorem fcLoop_user (xs : List ℕ) (t : ℕ) :
    hnRefine (fcPre xs t) fcLoop_impl (fcFrame xs t) ("k", "acc") (natAssn ×ₐ natAssn)
      (timerefine irE (fcUser xs t)) :=
  hnRefine_ref (fcLoop' xs t) (fc_exchange xs t)

/-- info: 'Lax13Proofs.Refine.Sepref.Acceptance.fcLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fcLoop

/-- info: 'Lax13Proofs.Refine.Sepref.Acceptance.fcLoop_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fcLoop_user

/-! ## 4. In-place array reverse

`while i < j do { swap A[i] A[j]; i := i + 1; j := j - 1 }`. The array is
the third component of the loop state (P4/D-ec), so the two `aset`s move
its ownership inside the loop frame; the two reads land in the scratch
cells `"t1"` and `"t2"`, which are junk again at the end of every
iteration. -/

/-- The invariant (P4/D-ed): whenever the loop runs, the upper index is
in range. Stated as an implication so that the initial state of an empty
array satisfies it. -/
def rvI : ℕ × ℕ × List ℕ → Prop := fun s => s.1 < s.2.1 → s.2.1 < s.2.2.length

/-- **The body.** Two reads, two writes, two index updates, and the
tuple — nested, because the state is a triple. -/
noncomputable def rvF : ℕ × ℕ × List ℕ → NRest (ℕ × ℕ × List ℕ) ECost := fun s =>
  NRest.bindT (mopAget s.2.2 s.1) fun a =>
    NRest.bindT (mopAget s.2.2 s.2.1) fun b =>
      NRest.bindT (mopAset s.2.2 s.1 b) fun ys =>
        NRest.bindT (mopAset ys s.2.1 a) fun zs =>
          NRest.bindT (mopBinop .add s.1 1) fun i' =>
            NRest.bindT (mopBinop .sub s.2.1 1) fun j' =>
              NRest.bindT (mopPair j' zs) fun p => mopPair i' p

/-- Reverse has no branch, so its body is a *fixed point* of the
exchange: every operation is already at an ir currency (P4/D-eb). -/
theorem rvF_exch (s : ℕ × ℕ × List ℕ) : ExchOk (rvF s) (rvF s) :=
  ExchOk.bind (.of_eq (timerefine_irE_mopAget _ _)) fun _ =>
    ExchOk.bind (.of_eq (timerefine_irE_mopAget _ _)) fun _ =>
      ExchOk.bind (.of_eq (timerefine_irE_mopAset _ _ _)) fun _ =>
        ExchOk.bind (.of_eq (timerefine_irE_mopAset _ _ _)) fun _ =>
          ExchOk.bind (.of_eq (timerefine_irE_mopBinop _ _ _)) fun _ =>
            ExchOk.bind (.of_eq (timerefine_irE_mopBinop _ _ _)) fun _ =>
              ExchOk.bind (.of_eq (timerefine_irE_mopPair _ _)) fun _ =>
                .of_eq (timerefine_irE_mopPair _ _)

/-- One iteration's price: two reads, two writes, an addition, a
subtraction, and the two tuple steps. -/
noncomputable def rvCost : ECost :=
  irUnit Currency.aget + irUnit Currency.aget + irUnit Currency.aset + irUnit Currency.aset +
    irUnit Currency.add + irUnit Currency.sub + irUnit Currency.skip + irUnit Currency.skip

/-- **The body's value** — the fact §1's twin is a twin of. -/
theorem rvF_eq (s : ℕ × ℕ × List ℕ) (h1 : s.1 < s.2.2.length) (h2 : s.2.1 < s.2.2.length) :
    rvF s = NRest.consume (NRest.returnT (rvStep s)) rvCost := by
  have h2' : s.2.1 < (s.2.2.set s.1 s.2.2[s.2.1]!).length := by simpa using h2
  show NRest.bindT (mopAget s.2.2 s.1) _ = _
  simp only [mopAget_def, mopAset_def, mopBinop_def, mopPair_def,
    NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h2',
    NRest.returnT_bindT, bindT_unit, NRest.consume_consume, rvStep, rvCost,
    Imp.Bop.apply_add, Imp.Bop.apply_sub, binopCurrency_add, binopCurrency_sub]
  congr 1
  ac_rfl

/-- Every currency the body spends is bought at itself. -/
theorem timerefineA_irE_rvCost : timerefineA irE rvCost = rvCost := by
  simp only [rvCost, timerefineA_add wfR''_irE, timerefineA_cost_one,
    irE_other (show Currency.aget ≠ "if" by decide) (show Currency.aget ≠ "call" by decide),
    irE_other (show Currency.aset ≠ "if" by decide) (show Currency.aset ≠ "call" by decide),
    irE_other (show Currency.add ≠ "if" by decide) (show Currency.add ≠ "call" by decide),
    irE_other (show Currency.sub ≠ "if" by decide) (show Currency.sub ≠ "call" by decide),
    irE_other (show Currency.skip ≠ "if" by decide) (show Currency.skip ≠ "call" by decide)]

/-- The variant: the gap between the two indices. -/
def rvV : ℕ × ℕ × List ℕ → ℕ := fun s => s.2.1 - s.1

/-- The invariant and the guard together give both index bounds — the
only thing the invariant is for (P4/D-ed). -/
theorem rv_bounds {s : ℕ × ℕ × List ℕ} (hI : rvI s) (hb : rvBf s = true) :
    s.1 < s.2.2.length ∧ s.2.1 < s.2.2.length := by
  have hlt : s.1 < s.2.1 := by simpa [rvBf] using hb
  exact ⟨lt_trans hlt (hI hlt), hI hlt⟩

theorem rv_variant : LOOP_VARIANT rvI rvBf rvF rvV := by
  intro s s' hI hb hle
  obtain ⟨h1, h2⟩ := rv_bounds hI hb
  rw [rvF_eq s h1 h2, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = rvStep s := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  have hlt : s.1 < s.2.1 := by simpa [rvBf] using hb
  subst hs'
  show s.2.1 - 1 - (s.1 + 1) < s.2.1 - s.1
  omega

theorem rv_variant_user : ∀ s s', rvI s → rvBf s = true →
    (NRest.returnT s' : NRest (ℕ × ℕ × List ℕ) ECost) ≤ timerefine irE (rvF s) →
    rvV s' < rvV s := by
  intro s s' hI hb hle
  obtain ⟨h1, h2⟩ := rv_bounds hI hb
  rw [rvF_eq s h1 h2, timerefine_consume wfR''_irE, timerefine_returnT,
    timerefineA_irE_rvCost, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = rvStep s := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  have hlt : s.1 < s.2.1 := by simpa [rvBf] using hb
  subst hs'
  show s.2.1 - 1 - (s.1 + 1) < s.2.1 - s.1
  omega

/-- **The user program**: the source's loop combinator over the same
body (P4/D-ea, P4/D-eb). -/
noncomputable def rvUser (xs : List ℕ) : NRest (ℕ × ℕ × List ℕ) ECost :=
  NRest.monadicWhileIT rvI (fun s => NRest.returnT (rvBf s)) rvF (0, xs.length - 1, xs)

theorem rv_exchange (xs : List ℕ) :
    irWhileIT rvI rvBf rvF (0, xs.length - 1, xs) ≤ timerefine irE (rvUser xs) :=
  le_trans (irWhileIT_mono (fun s => rvF_exch s) _)
    (irWhileIT_le_timerefine_irE rvV rv_variant_user _)

/-! **The synthesis.** Four owned conjuncts: the triple state, the two
scratch cells the two reads land in — listed in the order the body
consumes them — and the constant the two index updates need. -/

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth rvLoop (xs : List ℕ) (hv : LOOP_VARIANT rvI rvBf rvF rvV) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn ×ₐ arrayAssn) (0, xs.length - 1, xs) ("i", "j", "A") ∗
      junkCell "t1" ∗ junkCell "t2" ∗ hnCtxt natAssn 1 "one")
    _ _ ("i", "j", "A") (natAssn ×ₐ natAssn ×ₐ arrayAssn)
    (irWhileIT rvI rvBf rvF (0, xs.length - 1, xs))

-- The synthesized program, pinned: the swap is `aget/aget/aset/aset`
-- with no temporary beyond the two the precondition supplied, and the
-- two trailing `skip`s are the nested `mopPair`.
#guard rvLoop_impl =
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "j"))
    (Com.seq (Com.aget "t1" "A" "i")
      (Com.seq (Com.aget "t2" "A" "j")
        (Com.seq (Com.aset "A" "i" "t2")
          (Com.seq (Com.aset "A" "j" "t1")
            (Com.seq (Com.binop Imp.Bop.add "i" "i" "one")
              (Com.seq (Com.binop Imp.Bop.sub "j" "j" "one") (Com.seq Com.skip Com.skip)))))))

def rvPre (xs : List ℕ) : Assn :=
  hnCtxt (natAssn ×ₐ natAssn ×ₐ arrayAssn) (0, xs.length - 1, xs) ("i", "j", "A") ∗
    junkCell "t1" ∗ junkCell "t2" ∗ hnCtxt natAssn 1 "one"

def rvFrame : Assn := junkCell "t1" ∗ junkCell "t2" ∗ hnCtxt natAssn 1 "one"

theorem rvLoop' (xs : List ℕ) :
    hnRefine (rvPre xs) rvLoop_impl rvFrame ("i", "j", "A")
      (natAssn ×ₐ natAssn ×ₐ arrayAssn) (irWhileIT rvI rvBf rvF (0, xs.length - 1, xs)) :=
  rvLoop xs rv_variant

/-- **The acceptance statement for reverse.** -/
theorem rvLoop_user (xs : List ℕ) :
    hnRefine (rvPre xs) rvLoop_impl rvFrame ("i", "j", "A")
      (natAssn ×ₐ natAssn ×ₐ arrayAssn) (timerefine irE (rvUser xs)) :=
  hnRefine_ref (rvLoop' xs) (rv_exchange xs)

/-- The result assertion the handoff asked for (P4/D-ec): the array at
`"A"`, with the two index cells owned but dead. -/
def rvRes : ℕ × ℕ × List ℕ → String × String × String → Assn :=
  fun s c => junkCell c.1 ∗ junkCell c.2.1 ∗ arrayAssn s.2.2 c.2.2

/-- …and the same theorem at it, through `hnRefine_cons_res`: the
program's *result* is the reversed array in the cell `"A"`. -/
theorem rvLoop_array (xs : List ℕ) :
    hnRefine (rvPre xs) rvLoop_impl rvFrame ("i", "j", "A") rvRes
      (timerefine irE (rvUser xs)) :=
  hnRefine_cons_res (rvLoop_user xs) fun a e =>
    conj_entails_mono (natAssn_entails_junkCell a.1 e.1)
      (conj_entails_mono (natAssn_entails_junkCell a.2.1 e.2.1) (entails_refl _))

/-- info: 'Lax13Proofs.Refine.Sepref.Acceptance.rvLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rvLoop

/-- info: 'Lax13Proofs.Refine.Sepref.Acceptance.rvLoop_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rvLoop_user

/-- info: 'Lax13Proofs.Refine.Sepref.Acceptance.rvLoop_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rvLoop_array

/-! ## 5. The per-phase failure demo

Reverse's *first* body step, with its scratch cell omitted. The envelope
names the phase and its priority, the term it could not translate, the
ownership it had, the cell the caller has to add, and — under
`hnr_mop_aget` — the precise conjunct that went unmatched. Run through
`#sepref_synth`, which reports instead of throwing, so the text is
`#guard_msgs`-checkable and no failing declaration is left behind.

(The suggested name in the pool line is `"t2"` rather than `"t1"`:
`freshScratchName` picks a name that occurs *nowhere* in the goal, and
`"t1"` occurs there as the destination. The rule-level report below it
names `junkCell "t1"` exactly.) -/

/--
info: sepref: phase 'trans' (priority 80) failed.
sepref: no rule translates
  Lax13Proofs.Refine.Sepref.mopAget xs i
under the ownership
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.arrayAssn xs "A" ∗
    Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn i "i"
The precondition owns no scratch cell; a destination-taking rule needs `junkCell "t2"` in it.
combinator rules (2 more are stated at other abstract terms):
Lax13Proofs.Refine.Sepref.hnr_bind: applied, but a sub-program stalled: sepref: no rule translates
  Lax13Proofs.Refine.NRest.assert (i < xs.length)
under the ownership
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.arrayAssn xs "A" ∗
    Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn i "i"
The precondition owns no scratch cell; a destination-taking rule needs `junkCell "t1"` in it.
combinator rules: none is stated at this abstract term (4 tried).
operator rules: none is stated at this abstract term (8 tried).
Lax13Proofs.Refine.Sepref.hnr_seq: applied, but a sub-program stalled: sepref: no rule translates
  Lax13Proofs.Refine.NRest.assert (i < xs.length)
under the ownership
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.arrayAssn xs "A" ∗
    Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn i "i"
The precondition owns no scratch cell; a destination-taking rule needs `junkCell "t1"` in it.
combinator rules: none is stated at this abstract term (4 tried).
operator rules: none is stated at this abstract term (8 tried).
operator rules (7 more are stated at other abstract terms):
Lax13Proofs.Refine.Sepref.hnr_mop_aget: the rule's precondition conjuncts
  Lax13Proofs.Refine.Sepref.junkCell "t1"
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.arrayAssn xs ?a
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn i ?i
could not all be matched against the goal's
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.arrayAssn xs "A"
  Lax13Proofs.Refine.Sepref.hnCtxt Lax13Proofs.Refine.Sepref.natAssn i "i"
-/
#guard_msgs in
#sepref_synth (xs : List ℕ) (i : ℕ) :
  hnRefine (hnCtxt arrayAssn xs "A" ∗ hnCtxt natAssn i "i") _ _ "t1" natAssn (mopAget xs i)

/-! ## 6. Telemetry (the plan's P4 gate numbers)

* **Authored lines: 323.** Method: `wc -l` is 762; a nesting-aware scan
  classifies 113 lines as blank and 326 as comment (inside a block
  comment or a docstring, or a `--` line), leaving 323 lines of Lean.
  The 34 lines of `#guard_msgs`-pinned tool output in §5 and the five
  pinned `#print axioms` lines sit inside docstrings, so they are in the
  *comment* bucket and are not counted as authored. Of the 323, the
  three abstract loop bodies are 16 lines, the two user-layer loops 4,
  and the two `sepref_synth` invocations 12; the rest is the reusable
  exchange route (§2) and the value and variant lemmas the *variant
  annotation* needs (P4/D-cv's fallback deletes those).

* **Hand-written frame clauses: 0.** Nothing in this file rewrites with
  `sepConj_assoc`, `sepConj_comm`, `ac_rfl` *on assertions*,
  `irSTATE_rot`, `fri`, `hnRefine_pre_perm` or `hnRefine_frame`. The
  `∗`-lists in the `sepref_synth` goals and in
  `fcPre`/`fcFrame`/`rvPre`/`rvFrame` are interface — what the caller
  owns — and every permutation, split and frame that turns them into
  rule instances is inferred. Two things are worth naming rather than
  hiding under the zero. The three `ac_rfl`s below `congr 1` in
  `fcF_eq`/`fcUF_eq`/`rvF_eq` are on **cost sums** (`ECost`, an
  `AddCommMonoid`), not on `∗`. And `rvLoop_array` applies
  `conj_entails_mono` twice: that is a *result-assertion* weakening
  (three conjuncts, weakened in place, no associativity or commutativity
  used) outside the synthesis pipeline, and it is the only `∗`-shaped
  step written by hand in the file.

* **Synthesis wall clock**, differential against the same file with the
  two `sepref_synth` commands removed, warm build,
  `lake env lean` on the single file (baseline 4.7 s):
  `fcLoop` ≈ **2.8 s**, `rvLoop` ≈ **1.8 s**.

* **Axioms.** `#print axioms` is pinned above for `fcLoop`,
  `fcLoop_user`, `rvLoop`, `rvLoop_user` and `rvLoop_array`: all five are
  `[propext, Classical.choice, Quot.sound]` and nothing else.

* **Backlog.** (i) That the reverse loop computes `List.reverse` is
  checked on samples (§1), not proved — the proof is a loop-invariant
  argument over `List.set`, and P4's gate is the *synthesis*, not the
  functional correctness of the example. (ii) `ExchOk` and the per-`mop`
  invariance lemmas of §2 belong next to `Sepref/IrOps.lean` §4 once
  that file thaws; they are stated here because they are what a
  *program*, as opposed to a combinator, needs. (iii) `irWhileIT_mono`
  belongs in `Sepref/IrOps.lean` beside `irWhileIT_unfold`. -/

end Acceptance

end Lax13Proofs.Refine.Sepref
