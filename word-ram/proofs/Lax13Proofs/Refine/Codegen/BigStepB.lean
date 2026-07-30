import Lax13Proofs.Refine.Ir.Semantics
import Lax13Proofs.Bounds

/-!
Bounded IR runs: the mirror at the IR of IMP+'s own `BigStepB`.

**This file is ours** (ledger **D3**); its specification is
`plans/word-ram/refinement-tower/p5-codegen-design.md` §2.

IMP+ is the *unbounded* reference semantics and the machine is not: the
two agree exactly while no value of the run reaches `B = 2 ^ w`. The
kit deals with that once, in `Bounds.lean`, by threading the bound
through the derivation — `Imp.BigStepB B` is the big-step semantics
driven by `Expr.evalB B`, so "one derivation carries correctness, cost
and the bound together". The codegen boundary needs the same thing one
layer up: to compile an IR run into an IMP+ *bounded* run, the values
that run produces have to be below `B`, and the place to say so is the
IR derivation itself.

`BigStepB B` is therefore `BigStep` with the bound woven in. The side
conditions sit only where a run can *create* a value or *read* an
operand that IMP+ would refuse:

* `const x n` — `n < B`, the literal being written;
* `binop op x y z` — `op.apply m n < B`, the result being written;
* `ite` / `while` — the guard is evaluated by a *bounded* operand
  evaluation `Cond.evalB B` (judgment call **P5/D-i**).

Everything else — `copy`, `aget`, `aset` — only moves values that are
already in the state, so under the state invariant `StateBound B` they
create nothing new; that invariant is what `BigStepB.stateBound`
propagates and what the simulation reads bounds out of.

Three theorems make this usable: `BigStepB.bigStep` projects a bounded
run to a plain one, `BigStepB.stateBound` propagates the invariant to
the final state, and `BigStep.eq_of_bigStepB` transfers determinism —
a plain run and a bounded run from the same state are the same run, so
the wp-adequacy chain (which delivers a `BigStep`) and the bounds pass
(which delivers a `BigStepB`) can be tied together at wave B without
either being re-derived.

## Judgment calls

**P5/D-i — the guard of an `ite` or a `while` is evaluated by a bounded
operand evaluation, not by the plain `Cond.eval`.** The design record
§2 puts `< B` side conditions "only at value-creation sites", listing
`const` and `binop`. That is the right list for *scalar cells* but it
misses the conditions: `Ir.Cond` admits literals (`Ir/Syntax.lean`
judgment call D-b), a literal in a guard is created by no op, and IMP+'s
`Cond.evalB B` refuses it once it reaches `B`. Without a side condition
there, the simulation theorem is simply false — `while (0 < n)` with the
literal replaced by one at or above the bound has an IR run and no
bounded IMP+ run (the negative control in `Sim.lean` pins exactly this).
The fix is the smallest one that also mirrors IMP+ *more* closely, since
IMP+'s own `BigStepB` evaluates its guards with `Cond.evalB`: this file
gives `Operand.evalB` and `Cond.evalB` the same shape as `Bounds.lean`'s
and uses them in the two control rules. The cost to a consumer is nil
for the common guard, two cells, where the obligation is discharged from
`StateBound`; a literal guard is the one place a real goal appears, and
it is `n < B` on a numeral.

**P5/D-j — `StateBound` bounds array *entries*, not array lengths.** An
IR run never reads a length (there is no `len` op; lengths live in the
assertions), so a length at or above `B` is harmless: what the compiled
program evaluates are the entries and the indices, and indices are
scalar cells, already covered. Bounding lengths as well would be a
strictly stronger invariant with no consumer, and it would have to be
carried by the harness for no reason.
-/

namespace Lax13Proofs.Refine.Ir

open Lax13Proofs.Imp (fit fit_self fit_eq_some)

/-! ### Bounded operand and condition evaluation

`Bounds.lean`'s `Expr.evalB` / `Cond.evalB`, transcribed to the IR's
operands (judgment call P5/D-i). An operand has a bounded value when it
has a value at all and that value is below `B`. -/

/-- The value of an operand, refused once it reaches `B`. -/
def Operand.evalB (B : ℕ) : Operand → State → Option Val
  | .cell x, s => (s.vars x).bind (fit B)
  | .lit n, _ => fit B n

@[simp] theorem Operand.evalB_cell (B : ℕ) (x : String) (s : State) :
    (Operand.cell x).evalB B s = (s.vars x).bind (fit B) := rfl

@[simp] theorem Operand.evalB_lit (B : ℕ) (n : Val) (s : State) :
    (Operand.lit n).evalB B s = fit B n := rfl

/-- Bounded evaluation is evaluation. -/
theorem Operand.eval_of_evalB {B : ℕ} {u : Operand} {s : State} {v : Val}
    (h : u.evalB B s = some v) : u.eval s = some v := by
  cases u with
  | cell x =>
      rw [Operand.evalB_cell, Option.bind_eq_some_iff] at h
      obtain ⟨w, hw, hfit⟩ := h
      rw [fit_eq_some] at hfit
      obtain ⟨rfl, -⟩ := hfit
      exact hw
  | lit n =>
      rw [Operand.evalB_lit, fit_eq_some] at h
      obtain ⟨rfl, -⟩ := h
      rfl

/-- The value of a bounded evaluation is below the bound. -/
theorem Operand.lt_of_evalB {B : ℕ} {u : Operand} {s : State} {v : Val}
    (h : u.evalB B s = some v) : v < B := by
  cases u with
  | cell x =>
      rw [Operand.evalB_cell, Option.bind_eq_some_iff] at h
      obtain ⟨w, -, hfit⟩ := h
      rw [fit_eq_some] at hfit
      exact hfit.1 ▸ hfit.2
  | lit n =>
      rw [Operand.evalB_lit, fit_eq_some] at h
      exact h.1 ▸ h.2

/-- The introduction rule: a value that the operand has and that is
below the bound. -/
theorem Operand.evalB_of_eval {B : ℕ} {u : Operand} {s : State} {v : Val}
    (h : u.eval s = some v) (hv : v < B) : u.evalB B s = some v := by
  cases u with
  | cell x =>
      rw [Operand.eval_cell] at h
      rw [Operand.evalB_cell, h, Option.bind_some, fit_self hv]
  | lit n =>
      rw [Operand.eval_lit] at h
      cases h
      rw [Operand.evalB_lit, fit_self hv]

/-- Condition evaluation with the same bound on both operands. -/
def Cond.evalB (B : ℕ) : Cond → State → Option Bool
  | .eq u v, s => (u.evalB B s).bind fun m => (v.evalB B s).map fun n => m == n
  | .lt u v, s => (u.evalB B s).bind fun m => (v.evalB B s).map fun n => decide (m < n)

@[simp] theorem Cond.evalB_eq (B : ℕ) (u v : Operand) (s : State) :
    (Cond.eq u v).evalB B s = (u.evalB B s).bind fun m => (v.evalB B s).map fun n => m == n :=
  rfl

@[simp] theorem Cond.evalB_lt (B : ℕ) (u v : Operand) (s : State) :
    (Cond.lt u v).evalB B s =
      (u.evalB B s).bind fun m => (v.evalB B s).map fun n => decide (m < n) := rfl

/-- A bounded condition evaluation is a condition evaluation. -/
theorem Cond.eval_of_evalB {B : ℕ} {b : Cond} {s : State} {r : Bool}
    (h : b.evalB B s = some r) : b.eval s = some r := by
  cases b with
  | eq u v =>
      rw [Cond.evalB_eq, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      rw [Cond.eval_eq, Operand.eval_of_evalB hm, Operand.eval_of_evalB hn]; rfl
  | lt u v =>
      rw [Cond.evalB_lt, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      rw [Cond.eval_lt, Operand.eval_of_evalB hm, Operand.eval_of_evalB hn]; rfl

/-! ### The state invariant -/

/-- `StateBound B s`: every defined scalar cell and every entry of every
defined array is below `B`. Array *lengths* are not bounded (judgment
call P5/D-j): no op reads one.

This is the invariant the bounded semantics runs under. It is what makes
`copy`, `aget` and `aset` need no side condition of their own — they move
values that are already in the state — and it is what the simulation
reads its `< B` facts out of. -/
def StateBound (B : ℕ) (s : State) : Prop :=
  (∀ x v, s.vars x = some v → v < B) ∧
    (∀ a xs, s.arrs a = some xs → ∀ v ∈ xs, v < B)

/-- A defined scalar cell is below the bound. -/
theorem StateBound.var {B : ℕ} {s : State} (h : StateBound B s) {x : String} {v : Val}
    (hx : s.vars x = some v) : v < B := h.1 x v hx

/-- Every entry of a defined array is below the bound. -/
theorem StateBound.mem {B : ℕ} {s : State} (h : StateBound B s) {a : String} {xs : List Val}
    (ha : s.arrs a = some xs) {v : Val} (hv : v ∈ xs) : v < B := h.2 a xs ha v hv

/-- An entry read in range is below the bound. -/
theorem StateBound.getElem {B : ℕ} {s : State} (h : StateBound B s) {a : String}
    {xs : List Val} (ha : s.arrs a = some xs) {k : ℕ} {v : Val} (hv : xs[k]? = some v) :
    v < B := h.mem ha (List.mem_of_getElem? hv)

/-- Writing a bounded value into a scalar cell keeps the invariant. -/
theorem StateBound.setVar {B : ℕ} {s : State} (h : StateBound B s) {x : String} {v : Val}
    (hv : v < B) : StateBound B (s.setVar x v) := by
  refine ⟨fun y w hy => ?_, fun a xs ha => h.2 a xs ha⟩
  rw [State.vars_setVar] at hy
  split at hy
  · exact (Option.some.inj hy) ▸ hv
  · exact h.var hy

/-- Storing a bounded value into a defined array keeps the invariant. -/
theorem StateBound.setArr {B : ℕ} {s : State} (h : StateBound B s) {a : String}
    {xs : List Val} (ha : s.arrs a = some xs) {k n : ℕ} (hn : n < B) :
    StateBound B (s.setArr a (xs.set k n)) := by
  refine ⟨fun y w hy => h.var hy, fun b ys hb v hv => ?_⟩
  rw [State.arrs_setArr] at hb
  split at hb
  · subst_vars
    cases Option.some.inj hb
    rcases List.mem_or_eq_of_mem_set hv with hv | rfl
    · exact h.mem ha hv
    · exact hn
  · exact h.mem hb hv

/-! ### The bounded semantics

`Ir.BigStep` with the bound woven in: the same eleven constructors, the
same costs, the same shape, and `< B` exactly where a value is created
(`const`, `binop`) or an operand is read by a guard (`ite`, `while`,
judgment call P5/D-i). -/

/-- `BigStepB B c s s' κ`: running `c` in `s` terminates in `s'` having
paid `κ`, with every value the run creates and every guard operand it
reads below `B`. -/
inductive BigStepB (B : ℕ) : Com → State → State → Cost → Prop
  /-- `skip` changes nothing. -/
  | skip {s : State} : BigStepB B .skip s s (ACost.cost Currency.skip 1)
  /-- `x := n` writes a literal, which must fit. -/
  | const {s : State} {x : String} {n : Val} (hx : s.vars x ≠ none) (hn : n < B) :
      BigStepB B (.const x n) s (s.setVar x n) (ACost.cost Currency.const 1)
  /-- `x := y` moves an existing value; nothing is created. -/
  | copy {s : State} {x y : String} {v : Val}
      (hx : s.vars x ≠ none) (hy : s.vars y = some v) :
      BigStepB B (.copy x y) s (s.setVar x v) (ACost.cost Currency.copy 1)
  /-- `x := y ⊕ z` creates a value, which must fit. -/
  | binop {s : State} {op : Imp.Bop} {x y z : String} {m n : Val}
      (hx : s.vars x ≠ none) (hy : s.vars y = some m) (hz : s.vars z = some n)
      (hb : op.apply m n < B) :
      BigStepB B (.binop op x y z) s (s.setVar x (op.apply m n))
        (ACost.cost (binopCurrency op) 1)
  /-- `x := a[i]` moves an existing entry; nothing is created. -/
  | aget {s : State} {x a i : String} {k v : Val} {xs : List Val}
      (hx : s.vars x ≠ none) (hi : s.vars i = some k) (ha : s.arrs a = some xs)
      (hv : xs[k]? = some v) :
      BigStepB B (.aget x a i) s (s.setVar x v) (ACost.cost Currency.aget 1)
  /-- `a[i] := v` moves an existing value; nothing is created. -/
  | aset {s : State} {a i v : String} {k n : Val} {xs : List Val}
      (hi : s.vars i = some k) (hv : s.vars v = some n) (ha : s.arrs a = some xs)
      (hk : k < xs.length) :
      BigStepB B (.aset a i v) s (s.setArr a (xs.set k n)) (ACost.cost Currency.aset 1)
  /-- Costs of a sequence add up. -/
  | seq {c d : Com} {s s' s'' : State} {κ κ' : Cost} :
      BigStepB B c s s' κ → BigStepB B d s' s'' κ' → BigStepB B (.seq c d) s s'' (κ + κ')
  /-- A conditional whose guard holds runs its first branch. -/
  | ite_true {b : Cond} {c d : Com} {s s' : State} {κ : Cost}
      (hb : b.evalB B s = some true) (hc : BigStepB B c s s' κ) :
      BigStepB B (.ite b c d) s s' (ACost.cost Currency.ite 1 + κ)
  /-- A conditional whose guard fails runs its second branch. -/
  | ite_false {b : Cond} {c d : Com} {s s' : State} {κ : Cost}
      (hb : b.evalB B s = some false) (hd : BigStepB B d s s' κ) :
      BigStepB B (.ite b c d) s s' (ACost.cost Currency.ite 1 + κ)
  /-- A loop whose guard holds runs its body once and then again. -/
  | while_true {b : Cond} {c : Com} {s s' s'' : State} {κ κ' : Cost}
      (hb : b.evalB B s = some true) (hc : BigStepB B c s s' κ)
      (hw : BigStepB B (.while b c) s' s'' κ') :
      BigStepB B (.while b c) s s'' (ACost.cost Currency.«while» 1 + κ + κ')
  /-- A loop whose guard fails does nothing but pay for the test. -/
  | while_false {b : Cond} {c : Com} {s : State} (hb : b.evalB B s = some false) :
      BigStepB B (.while b c) s s (ACost.cost Currency.«while» 1)

/-- **Projection.** A bounded run is a run: same final state, same cost.
This is how the functional correctness and the cost proved against the
plain semantics — everything above P3 — are available to a consumer
holding a bounded derivation. -/
theorem BigStepB.bigStep {B : ℕ} {c : Com} {s s' : State} {κ : Cost}
    (h : BigStepB B c s s' κ) : BigStep c s s' κ := by
  induction h with
  | skip => exact .skip
  | const hx _ => exact .const hx
  | copy hx hy => exact .copy hx hy
  | binop hx hy hz _ => exact .binop hx hy hz
  | aget hx hi ha hv => exact .aget hx hi ha hv
  | aset hi hv ha hk => exact .aset hi hv ha hk
  | seq _ _ ih ih' => exact .seq ih ih'
  | ite_true hb _ ih => exact .ite_true (Cond.eval_of_evalB hb) ih
  | ite_false hb _ ih => exact .ite_false (Cond.eval_of_evalB hb) ih
  | while_true hb _ _ ih ih' => exact .while_true (Cond.eval_of_evalB hb) ih ih'
  | while_false hb => exact .while_false (Cond.eval_of_evalB hb)

/-- **The invariant is preserved.** Every value a bounded run writes is
either a literal it checked, an arithmetic result it checked, or a value
it read out of a state that already satisfied the invariant. -/
theorem BigStepB.stateBound {B : ℕ} {c : Com} {s s' : State} {κ : Cost}
    (h : BigStepB B c s s' κ) (hs : StateBound B s) : StateBound B s' := by
  induction h with
  | skip => exact hs
  | const _ hn => exact hs.setVar hn
  | copy _ hy => exact hs.setVar (hs.var hy)
  | binop _ _ _ hb => exact hs.setVar hb
  | aget _ _ ha hv => exact hs.setVar (hs.getElem ha hv)
  | aset _ hv ha _ => exact hs.setArr ha (hs.var hv)
  | seq _ _ ih ih' => exact ih' (ih hs)
  | ite_true _ _ ih => exact ih hs
  | ite_false _ _ ih => exact ih hs
  | while_true _ _ _ ih ih' => exact ih' (ih hs)
  | while_false _ => exact hs

/-- **Determinism transfer.** A plain run and a bounded run of the same
command from the same state are the same run. This is the seam wave B's
cashing theorem is assembled at: the abstract chain (wp adequacy)
delivers a `BigStep`, the per-program bounds pass delivers a `BigStepB`,
and neither has to be re-derived to know they describe one execution. -/
theorem BigStep.eq_of_bigStepB {B : ℕ} {c : Com} {s s' s₂ : State} {κ κ₂ : Cost}
    (h : BigStep c s s' κ) (hB : BigStepB B c s s₂ κ₂) : s' = s₂ ∧ κ = κ₂ :=
  h.unique hB.bigStep

/-- …and its bounded half, in the direction wave B uses it: a bounded
witness upgrades a plain run to a bounded one. -/
theorem BigStep.bigStepB_of_eq {B : ℕ} {c : Com} {s s' s₂ : State} {κ κ₂ : Cost}
    (h : BigStep c s s' κ) (hB : BigStepB B c s s₂ κ₂) : BigStepB B c s s' κ := by
  obtain ⟨rfl, rfl⟩ := h.eq_of_bigStepB hB
  exact hB

/-! ## Bounding a run one already has (judgment call P7/D-bl)

`BigStep.bigStepB_of_eq` needs a bounded run to start with, and
`BoundVcg.lean` builds one from nothing: it re-proves that every index
is in range and that every loop terminates. For a program whose
in-range facts are a counting argument — P7's queue BFS, where
`q[tl] := u` is in range because the queue never receives more vertices
than there are undiscovered live ones — that is the expensive half of
the abstract proof, done twice.

It is also unnecessary, because the consumer already *has* a run:
`hnRefine`'s wp adequacy delivers a `BigStep`, and a `BigStep` carries
its own `hk : k < xs.length` at every store and its own
`hv : xs[k]? = some v` at every read. Comparing the two inductive
definitions constructor by constructor, `BigStepB` adds exactly three
things: `n < B` at `const`, `op.apply m n < B` at `binop`, and
`Cond.evalB` in place of `Cond.eval` at the four control rules. So
*along a derivation* the residual is three `< B` facts and nothing
else — no in-range goals, no variants.

**P7/D-bl — the residual is a weakest precondition, not a state-local
side condition.** The tempting shape is a hypothesis "at bounded
operands the result is bounded", discharged once per program. It is
false for the only arithmetic this program does: `x := y + 1` at
`y = B - 1` leaves `B`. The bound on a `binop` result is available only
relative to where the run has got to — for `head := head + one` it is
`head < tl ≤ n < B`, and `tl ≤ n` is maintained by the *previous*
statement's successful `q[tl] := u`. That is an invariant, and an
invariant threaded through a derivation is a verification-condition
generator. `bpre` below is therefore `BoundVcg.lean`'s `bwp` with every
obligation the derivation already discharges deleted:

| clause | `bwp` (build a run) | `bpre` (bound a run one has) |
|---|---|---|
| `const` | cell defined, `n < B` | `n < B` |
| `copy`/`aget` | cell defined, index in range | — |
| `aset` | index in range | — (and `hk` is *handed to* the caller) |
| `binop` | cell defined, result `< B` | result `< B` |
| `ite`/`while` | the guard's `evalB` value | `eval` ⟹ `evalB` |
| `while` | invariant **and variant** | invariant |

The `aset` row is the one that pays for the whole file: `k < xs.length`
moves from a goal to a hypothesis, and that is exactly what makes
`tl ≤ n` inductive without the counting argument. -/

/-! ### Literals of a guard

The one obligation `StateBound` cannot discharge on its own: a cell is
bounded because the invariant says so, a literal because it is a
numeral (judgment call P5/D-i). -/

/-- The literal an operand may carry is below the bound. -/
def Operand.LitLt (B : ℕ) : Operand → Prop
  | .cell _ => True
  | .lit n => n < B

/-- …for both operands of a condition. -/
def Cond.LitLt (B : ℕ) : Cond → Prop
  | .eq u v => u.LitLt B ∧ v.LitLt B
  | .lt u v => u.LitLt B ∧ v.LitLt B

/-- Under the state invariant, an operand with a small literal evaluates
below the bound whenever it evaluates at all. -/
theorem Operand.evalB_of_stateBound {B : ℕ} {s : State} (hs : StateBound B s) {u : Operand}
    (hl : u.LitLt B) {v : Val} (h : u.eval s = some v) : u.evalB B s = some v := by
  cases u with
  | cell x => exact Operand.evalB_of_eval h (hs.var (by simpa using h))
  | lit n => exact Operand.evalB_of_eval h (by cases h; exact hl)

/-- …and so does a condition. -/
theorem Cond.evalB_of_stateBound {B : ℕ} {s : State} (hs : StateBound B s) {b : Cond}
    (hl : b.LitLt B) {r : Bool} (h : b.eval s = some r) : b.evalB B s = some r := by
  cases b with
  | eq u v =>
      rw [Cond.eval_eq, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      rw [Cond.evalB_eq, Operand.evalB_of_stateBound hs hl.1 hm,
        Operand.evalB_of_stateBound hs hl.2 hn]; rfl
  | lt u v =>
      rw [Cond.eval_lt, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      rw [Cond.evalB_lt, Operand.evalB_of_stateBound hs hl.1 hm,
        Operand.evalB_of_stateBound hs hl.2 hn]; rfl

/-! ### The residual precondition -/

/-- `bpre B c Q s` — what a state must satisfy for an *existing* run of
`c` from `s` to be a bounded run into `Q`. One clause per op, each of
them the difference between the op's `BigStep` rule and its `BigStepB`
rule: the definedness and in-range facts are hypotheses handed to the
caller, and what is left is the `< B` of a created value and the
bounded reading of a guard. A loop carries an invariant and no
variant. -/
def bpre (B : ℕ) : Com → (State → Prop) → State → Prop
  | .skip, Q => Q
  | .const x n, Q => fun s => n < B ∧ Q (s.setVar x n)
  | .copy x y, Q => fun s => ∀ v, s.vars y = some v → Q (s.setVar x v)
  | .binop op x y z, Q => fun s => ∀ m n, s.vars y = some m → s.vars z = some n →
      op.apply m n < B ∧ Q (s.setVar x (op.apply m n))
  | .aget x a i, Q => fun s => ∀ k xs v, s.vars i = some k → s.arrs a = some xs →
      xs[k]? = some v → Q (s.setVar x v)
  | .aset a i v, Q => fun s => ∀ k n xs, s.vars i = some k → s.vars v = some n →
      s.arrs a = some xs → k < xs.length → Q (s.setArr a (xs.set k n))
  | .seq c d, Q => bpre B c (bpre B d Q)
  | .ite b c d, Q => fun s => (∀ r, b.eval s = some r → b.evalB B s = some r) ∧
      (b.eval s = some true → bpre B c Q s) ∧ (b.eval s = some false → bpre B d Q s)
  | .while b c, Q => fun s => ∃ Inv : State → Prop, Inv s ∧
      (∀ t r, Inv t → b.eval t = some r → b.evalB B t = some r) ∧
      (∀ t, Inv t → b.eval t = some true → bpre B c Inv t) ∧
      (∀ t, Inv t → b.eval t = some false → Q t)

@[simp] theorem bpre_skip (B : ℕ) (Q : State → Prop) : bpre B .skip Q = Q := rfl

@[simp] theorem bpre_const (B : ℕ) (x : String) (n : Val) (Q : State → Prop) (s : State) :
    bpre B (.const x n) Q s ↔ n < B ∧ Q (s.setVar x n) := Iff.rfl

@[simp] theorem bpre_copy (B : ℕ) (x y : String) (Q : State → Prop) (s : State) :
    bpre B (.copy x y) Q s ↔ ∀ v, s.vars y = some v → Q (s.setVar x v) := Iff.rfl

@[simp] theorem bpre_binop (B : ℕ) (op : Imp.Bop) (x y z : String) (Q : State → Prop)
    (s : State) :
    bpre B (.binop op x y z) Q s ↔ ∀ m n, s.vars y = some m → s.vars z = some n →
      op.apply m n < B ∧ Q (s.setVar x (op.apply m n)) := Iff.rfl

@[simp] theorem bpre_aget (B : ℕ) (x a i : String) (Q : State → Prop) (s : State) :
    bpre B (.aget x a i) Q s ↔ ∀ k xs v, s.vars i = some k → s.arrs a = some xs →
      xs[k]? = some v → Q (s.setVar x v) := Iff.rfl

@[simp] theorem bpre_aset (B : ℕ) (a i v : String) (Q : State → Prop) (s : State) :
    bpre B (.aset a i v) Q s ↔ ∀ k n xs, s.vars i = some k → s.vars v = some n →
      s.arrs a = some xs → k < xs.length → Q (s.setArr a (xs.set k n)) := Iff.rfl

@[simp] theorem bpre_seq (B : ℕ) (c d : Com) (Q : State → Prop) :
    bpre B (.seq c d) Q = bpre B c (bpre B d Q) := rfl

@[simp] theorem bpre_ite (B : ℕ) (b : Cond) (c d : Com) (Q : State → Prop) (s : State) :
    bpre B (.ite b c d) Q s ↔ (∀ r, b.eval s = some r → b.evalB B s = some r) ∧
      (b.eval s = some true → bpre B c Q s) ∧
      (b.eval s = some false → bpre B d Q s) := Iff.rfl

theorem bpre_while (B : ℕ) (b : Cond) (c : Com) (Q : State → Prop) (s : State) :
    bpre B (.while b c) Q s ↔ ∃ Inv : State → Prop, Inv s ∧
      (∀ t r, Inv t → b.eval t = some r → b.evalB B t = some r) ∧
      (∀ t, Inv t → b.eval t = some true → bpre B c Inv t) ∧
      (∀ t, Inv t → b.eval t = some false → Q t) := Iff.rfl

/-- **The bounds pass along a derivation** (judgment call P7/D-bl). A
run one already has is a *bounded* run — same final state, same cost —
as soon as the caller can thread an invariant through it that bounds
the literals it writes, the results it computes and the operands its
guards read. Every definedness fact, every in-range index and the
termination of every loop come from the derivation and cost nothing.

This is the theorem P7's export is assembled at: `hnRefine`'s wp
adequacy hands over the `BigStep`, this hands back the `BigStepB` that
`Sim.lean` consumes. -/
theorem BigStep.bigStepB_of_inv {B : ℕ} {c : Com} {s s' : State} {κ : Cost}
    (h : BigStep c s s' κ) :
    ∀ {Q : State → Prop}, bpre B c Q s → BigStepB B c s s' κ ∧ Q s' := by
  induction h with
  | skip => intro Q hs; exact ⟨.skip, hs⟩
  | const hx => intro Q hs; exact ⟨.const hx hs.1, hs.2⟩
  | copy hx hy => intro Q hs; exact ⟨.copy hx hy, hs _ hy⟩
  | binop hx hy hz =>
      intro Q hs
      exact ⟨.binop hx hy hz (hs _ _ hy hz).1, (hs _ _ hy hz).2⟩
  | aget hx hi ha hv => intro Q hs; exact ⟨.aget hx hi ha hv, hs _ _ _ hi ha hv⟩
  | aset hi hv ha hk => intro Q hs; exact ⟨.aset hi hv ha hk, hs _ _ _ hi hv ha hk⟩
  | seq _ _ ih ih' =>
      intro Q hs
      obtain ⟨hb, hm⟩ := ih hs
      obtain ⟨hb', hq⟩ := ih' hm
      exact ⟨.seq hb hb', hq⟩
  | ite_true hb _ ih =>
      intro Q hs
      obtain ⟨hg, ht, -⟩ := hs
      obtain ⟨hc, hq⟩ := ih (ht hb)
      exact ⟨.ite_true (hg _ hb) hc, hq⟩
  | ite_false hb _ ih =>
      intro Q hs
      obtain ⟨hg, -, hf⟩ := hs
      obtain ⟨hd, hq⟩ := ih (hf hb)
      exact ⟨.ite_false (hg _ hb) hd, hq⟩
  | while_true hb _ _ ih ih' =>
      intro Q hs
      obtain ⟨Inv, hI, hg, hbody, hexit⟩ := hs
      obtain ⟨hc, hI'⟩ := ih (hbody _ hI hb)
      obtain ⟨hw, hq⟩ := ih' (Q := Q) ⟨Inv, hI', hg, hbody, hexit⟩
      exact ⟨.while_true (hg _ _ hI hb) hc hw, hq⟩
  | while_false hb =>
      intro Q hs
      obtain ⟨Inv, hI, hg, -, hexit⟩ := hs
      exact ⟨.while_false (hg _ _ hI hb), hexit _ hI hb⟩

/-- The form the cashing theorem's `hbd` hypothesis is in. -/
theorem BigStep.exists_bigStepB_of_inv {B : ℕ} {c : Com} {s s' : State} {κ : Cost}
    {Q : State → Prop} (h : BigStep c s s' κ) (hs : bpre B c Q s) :
    ∃ s₂ κ₂, BigStepB B c s s₂ κ₂ :=
  ⟨s', κ, (h.bigStepB_of_inv hs).1⟩

/-! ### The gate

The bounded semantics is not a look-alike of the plain one: it is the
plain one with side conditions, and the two negative controls below pin
that the side conditions bite. -/

namespace BoundGate

/-- `x := 200` in a state where `x` exists. -/
def bigConstState : State := State.ofPairs [("x", 0)] []

-- The plain semantics runs it…
theorem bigConst_bigStep :
    BigStep (.const "x" 200) bigConstState (bigConstState.setVar "x" 200)
      (ACost.cost Currency.const 1) := .const (by decide)

/-- …and the bounded semantics refuses it below the bound: a literal
that does not fit is not written. -/
theorem no_bigStepB_bigConst :
    ¬ ∃ s' κ, BigStepB 128 (.const "x" 200) bigConstState s' κ := by
  rintro ⟨s', κ, h⟩
  cases h with | const _ hn => exact absurd hn (by decide)

/-- A guard comparing a cell against a literal at the bound. -/
def bigGuardState : State := State.ofPairs [("n", 3)] []

/-- The literal in a guard is refused too — this is judgment call P5/D-i
in negative form: without a side condition at the guard the simulation
theorem would be false here, since IMP+'s own `evalB` refuses the
literal. -/
theorem no_bigStepB_bigGuard :
    ¬ ∃ s' κ, BigStepB 128 (.ite (.lt (.cell "n") (.lit 200)) .skip .skip)
      bigGuardState s' κ := by
  rintro ⟨s', κ, h⟩
  cases h with
  | ite_true hb => exact absurd hb (by decide)
  | ite_false hb => exact absurd hb (by decide)

-- The same guard below the bound is fine.
theorem bigStepB_smallGuard :
    BigStepB 128 (.ite (.lt (.cell "n") (.lit 100)) .skip .skip) bigGuardState
      bigGuardState (ACost.cost Currency.ite 1 + ACost.cost Currency.skip 1) :=
  .ite_true (by decide) .skip

end BoundGate

end Lax13Proofs.Refine.Ir
