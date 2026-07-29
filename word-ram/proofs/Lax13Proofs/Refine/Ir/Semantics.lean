import Lax13Proofs.Refine.Ir.Syntax
import Lax13Proofs.Refine.Cost.ACost

/-!
The IR's states and its cost-indexed big-step semantics.

**This file is ours** (ledger **D2**), and it is the file where that
deviation is actually spent, so it is worth saying precisely what is and
is not inherited from `isabelle_llvm_time`.

*Not inherited.* The source's concrete layer is a shallow monad: `llM`
is `('a, unit, cost, llvm_memory, err) M`, whose `mres` outcome type has
five constructors — `NTERM`, `FAIL`, `EXC`, `SUCC` — and whose programs
are Lean-side (there, HOL-side) functions. None of that is here. There
is no `M`, no `mres`, no exception carrier and no `NTERM`: a *deep*
`Ir.Com` (`Syntax.lean`) is given a big-step relation, so

* nontermination is *no derivation* rather than an `NTERM` outcome,
* failure (a stuck configuration) is *no derivation* rather than `FAIL`,
* and the shallow monad's `run : 's → mres` is replaced by the relation
  `BigStep c s s' κ`, which is what makes P5's verified codegen (**D3**)
  a statement about a *term* rather than about a printer's output.

This mirrors IMP+ exactly, on purpose: `Lax13Proofs.Imp.BigStep` has the
same shape (`Com → Env → Env → ℕ → Prop`), the same constructor names
where the constructs coincide (`skip`, `seq`, `ite_true`, `ite_false`,
`while_true`, `while_false`), and the same "out-of-bounds access is
stuck, not defaulted" discipline, which IMP+'s own header calls one of
its three load-bearing design points. A reader who knows IMP+ knows this
file.

*Inherited, and the whole point of the port.* The **rule granularity**:
one primitive op is exactly one `consume (cost "…" 1)` glued to the op's
effect, which is the artifact's own shape
(`plans/word-ram/refinement-tower/p3-ir-sl-extracts.md` §3, `ll_load` /
`ll_store`) and is "one op = one cost = one hnr rule" — the property
`design.md` §3's P3 row says P4's fidelity consumes. Every primitive
rule below charges `ACost.cost c 1` for its own `c` and nothing else.

## Judgment calls

**D-e — the cost index is `ACost String ℕ`, not `ECost`.** The task's
carrier question (design record §10 default 1) is decided the source's
own way, and the two carriers are not competitors but different layers:
the artifact's `llM` consumes `cost = (string, nat) acost`, while the
`ecost = (string, enat) acost` carrier appears in the *assertions* —
`time_credits_assn :: ecost ⇒ …`, `ll_astate = llvm_amemory × ecost`.
So: a *run* is finite and pays finitely, and the ℕ∞ balance is a fact
about credits, which is wave B's `Ir/Assn.lean` and the `Ca.cash` seam
of design record §5. Nothing here needs ℕ∞ arithmetic and nothing here
would be helped by it. `ECost` is *not* redefined; `ACost` and
`ACost.cost` come from `Refine/Cost/ACost.lean` unchanged.

**D-f — writes require the cell to exist; there is no allocation.**
Design record §6: arrays are pre-existing named objects, and the state
is not grown by any op. Rendered as: `const`, `copy`, `binop` and
`aget` all carry a premise `s.vars x ≠ none` on their *destination*, and
`aset` requires the array to be present and the index in range. A
missing name and an out-of-range index are therefore stuck — no
derivation — exactly as an out-of-range array read is stuck in IMP+, and
exactly as the artifact's ops *fail* on a bad access. Two things depend
on this: wave B's separation logic can own names, because a program that
writes a name it does not own has no run at all; and `BigStep` preserves
the name space and every array length (`BigStep.vars_isSome`,
`BigStep.arrs_length` below), which is the frame property. It also keeps
P5 sound in the direction P5 needs: the IR's precondition for a step is
*stronger* than IMP+'s, so every IR run has an IMP+ run to be compiled
into.

**D-g — "finite map" is rendered as a partial function.** Design record
§3's P3 row asks for a "finite scalar map + finite array map". A partial
function `String → Option _` is what carries the structure that is
actually used: `0 = fun _ => none` and disjoint domains give the PCM
wave B needs (the source's own memory separation algebra is likewise
built from option-valued maps), whereas a finite-map *data structure*
would buy a quotient type and buy nothing else — no statement in this
file mentions finiteness. Finiteness is nevertheless available and
preserved — `State.Finite` and `BigStep.finite` below, a definition and
a corollary of the invariants D-f buys — so that a later wave can ask
for it without a re-representation.

**D-h — `ite` charges one unit, `while` one unit per guard
evaluation.** So an `n`-iteration loop charges `n + 1` of `ir.while`,
one per test including the failing one. This is IMP+'s own accounting
(`1 + b.size` at each `while_true` *and* at `while_false`) and it is
what makes P5's price map a constant per currency. `seq` charges
nothing of its own: it is not an instruction, and its cost is the sum of
its parts, as in IMP+.

**D-i — the evaluator's fuel counts derivation *depth*, not steps.**
`evalFuel` decreases its fuel at every recursive call, including the two
of a `seq`, so it is structurally recursive on the fuel and each of its
ten clauses is an equation by `rfl` — which is what makes the `#guard`s
below kernel-computable and the equation lemmas free. The price is that
the fuel needed by a program is its derivation depth rather than its
step count; `evalFuel_mono` makes that invisible in every statement, all
of which are existential in the fuel.

## The executable twin

Ledger **D4**: every layer gets its executable instances and property
checks the day it lands. `evalFuel` is the fuel-indexed evaluator, and
`bigStep_of_evalFuel` / `exists_evalFuel` are the two directions of
agreement, so the `#guard`s and Plausible `#test`s in the `Gate` section
below are checks of the *relation*, not of a look-alike. The gate pins,
for three programs, the final state **and** the exact cost vector
currency by currency, and carries two negative controls: an
out-of-bounds `aget` has no derivation at all, and a wrong cost is
rejected (by determinism, not merely by the evaluator).
-/

namespace Lax13Proofs.Refine.Ir

/-- The IR's cost: a finite bundle of currencies, the source's
`cost = (string, nat) acost` (judgment call D-e). The ℕ∞-valued `ECost`
is the *credit balance* of the assertion layer, not the index of a run. -/
abbrev Cost : Type := ACost String ℕ

/-! ### States -/

/-- An IR state: the scalar cells and the arrays that exist, each by
name. Partial in both components (judgment call D-g) — a name that is
absent is a name no program may touch — and tape-free (ledger note N3).
Distinct names are distinct objects, so no two names can alias; this is
IMP+'s aliasing-freedom, kept *below* the separation logic (ledger note
N1). -/
@[ext]
structure State where
  /-- The value of each scalar cell that exists. -/
  vars : String → Option Val
  /-- The contents of each array that exists. -/
  arrs : String → Option (List Val)

/-- The state with the scalar cell `x` set to `v`. -/
def State.setVar (s : State) (x : String) (v : Val) : State :=
  { s with vars := fun y => if y = x then some v else s.vars y }

/-- The state with the array `a` replaced by `xs`. -/
def State.setArr (s : State) (a : String) (xs : List Val) : State :=
  { s with arrs := fun b => if b = a then some xs else s.arrs b }

@[simp] theorem State.vars_setVar (s : State) (x : String) (v : Val) (y : String) :
    (s.setVar x v).vars y = if y = x then some v else s.vars y := rfl

@[simp] theorem State.arrs_setVar (s : State) (x : String) (v : Val) :
    (s.setVar x v).arrs = s.arrs := rfl

@[simp] theorem State.vars_setArr (s : State) (a : String) (xs : List Val) :
    (s.setArr a xs).vars = s.vars := rfl

@[simp] theorem State.arrs_setArr (s : State) (a : String) (xs : List Val) (b : String) :
    (s.setArr a xs).arrs b = if b = a then some xs else s.arrs b := rfl

/-- A cell that is not absent holds something. -/
theorem State.exists_of_vars_ne_none {s : State} {x : String} (hx : s.vars x ≠ none) :
    ∃ v, s.vars x = some v := by
  cases hv : s.vars x with
  | none => exact absurd hv hx
  | some v => exact ⟨v, rfl⟩

/-- Writing an *existing* cell does not change which cells exist. -/
theorem State.isSome_vars_setVar {s : State} {x : String} (hx : s.vars x ≠ none)
    (v : Val) (y : String) : ((s.setVar x v).vars y).isSome = (s.vars y).isSome := by
  obtain ⟨w, hw⟩ := State.exists_of_vars_ne_none hx
  simp only [State.vars_setVar]
  split
  · subst_vars; simp [hw]
  · rfl

/-- Replacing an array by one of the same length changes neither which
arrays exist nor any array's length. -/
theorem State.map_length_arrs_setArr {s : State} {a : String} {xs ys : List Val}
    (ha : s.arrs a = some xs) (hlen : ys.length = xs.length) (b : String) :
    ((s.setArr a ys).arrs b).map List.length = (s.arrs b).map List.length := by
  simp only [State.arrs_setArr]
  split
  · subst_vars; rw [ha]; simp [hlen]
  · rfl

/-- The state built from an association list of scalars and one of
arrays; every other name is absent. The `initEnv` of this layer, used by
the executable gate. -/
def State.ofPairs (vs : List (String × Val)) (as : List (String × List Val)) : State where
  vars := fun x => vs.lookup x
  arrs := fun a => as.lookup a

/-- A state has finite domains (judgment call D-g). Nothing in this file
needs it; it is stated and preserved so that a later wave can. -/
def State.Finite (s : State) : Prop :=
  {x | s.vars x ≠ none}.Finite ∧ {a | s.arrs a ≠ none}.Finite

/-! ### Operands and conditions -/

/-- The value of an operand, or `none` if it names a cell that does not
exist. -/
def Operand.eval : Operand → State → Option Val
  | .cell x, s => s.vars x
  | .lit n, _ => some n

@[simp] theorem Operand.eval_cell (x : String) (s : State) :
    (Operand.cell x).eval s = s.vars x := rfl

@[simp] theorem Operand.eval_lit (n : Val) (s : State) :
    (Operand.lit n).eval s = some n := rfl

/-- Whether a condition holds, or `none` if it names a cell that does
not exist. IMP+'s `Cond.eval`, over operands. -/
def Cond.eval : Cond → State → Option Bool
  | .eq u v, s => (u.eval s).bind fun m => (v.eval s).map fun n => m == n
  | .lt u v, s => (u.eval s).bind fun m => (v.eval s).map fun n => decide (m < n)

@[simp] theorem Cond.eval_eq (u v : Operand) (s : State) :
    (Cond.eq u v).eval s = (u.eval s).bind fun m => (v.eval s).map fun n => m == n := rfl

@[simp] theorem Cond.eval_lt (u v : Operand) (s : State) :
    (Cond.lt u v).eval s = (u.eval s).bind fun m => (v.eval s).map fun n => decide (m < n) := rfl

/-! ### The cost-indexed big-step semantics

`BigStep c s s' κ`: running `c` in `s` terminates in `s'`, having paid
`κ`. There is no derivation when a name is absent or an index is out of
range, so such a program is stuck rather than continuing with a default
value (judgment call D-f), and none when the program does not terminate.

Each primitive rule charges exactly one unit of exactly its own
currency, which is the artifact's `consume (cost ''load'' 1)` line glued
to the op's effect, one op at a time. -/

inductive BigStep : Com → State → State → Cost → Prop
  /-- `skip` changes nothing. -/
  | skip {s : State} : BigStep .skip s s (ACost.cost Currency.skip 1)
  /-- `x := n` writes a literal into an existing cell. -/
  | const {s : State} {x : String} {n : Val} (hx : s.vars x ≠ none) :
      BigStep (.const x n) s (s.setVar x n) (ACost.cost Currency.const 1)
  /-- `x := y` copies one existing cell into another. -/
  | copy {s : State} {x y : String} {v : Val}
      (hx : s.vars x ≠ none) (hy : s.vars y = some v) :
      BigStep (.copy x y) s (s.setVar x v) (ACost.cost Currency.copy 1)
  /-- `x := y ⊕ z` applies IMP+'s `Bop.apply` — the machine's own
  arithmetic with the truncation removed (judgment call D-a). -/
  | binop {s : State} {op : Imp.Bop} {x y z : String} {m n : Val}
      (hx : s.vars x ≠ none) (hy : s.vars y = some m) (hz : s.vars z = some n) :
      BigStep (.binop op x y z) s (s.setVar x (op.apply m n))
        (ACost.cost (binopCurrency op) 1)
  /-- `x := a[i]` reads an existing array in range. -/
  | aget {s : State} {x a i : String} {k v : Val} {xs : List Val}
      (hx : s.vars x ≠ none) (hi : s.vars i = some k) (ha : s.arrs a = some xs)
      (hv : xs[k]? = some v) :
      BigStep (.aget x a i) s (s.setVar x v) (ACost.cost Currency.aget 1)
  /-- `a[i] := v` writes an existing array in range. -/
  | aset {s : State} {a i v : String} {k n : Val} {xs : List Val}
      (hi : s.vars i = some k) (hv : s.vars v = some n) (ha : s.arrs a = some xs)
      (hk : k < xs.length) :
      BigStep (.aset a i v) s (s.setArr a (xs.set k n)) (ACost.cost Currency.aset 1)
  /-- Costs of a sequence add up; `seq` charges nothing of its own. -/
  | seq {c d : Com} {s s' s'' : State} {κ κ' : Cost} :
      BigStep c s s' κ → BigStep d s' s'' κ' → BigStep (.seq c d) s s'' (κ + κ')
  /-- A conditional whose condition holds runs its first branch. -/
  | ite_true {b : Cond} {c d : Com} {s s' : State} {κ : Cost}
      (hb : b.eval s = some true) (hc : BigStep c s s' κ) :
      BigStep (.ite b c d) s s' (ACost.cost Currency.ite 1 + κ)
  /-- A conditional whose condition fails runs its second branch. -/
  | ite_false {b : Cond} {c d : Com} {s s' : State} {κ : Cost}
      (hb : b.eval s = some false) (hd : BigStep d s s' κ) :
      BigStep (.ite b c d) s s' (ACost.cost Currency.ite 1 + κ)
  /-- A loop whose condition holds runs its body once and then again. -/
  | while_true {b : Cond} {c : Com} {s s' s'' : State} {κ κ' : Cost}
      (hb : b.eval s = some true) (hc : BigStep c s s' κ)
      (hw : BigStep (.while b c) s' s'' κ') :
      BigStep (.while b c) s s'' (ACost.cost Currency.«while» 1 + κ + κ')
  /-- A loop whose condition fails does nothing but pay for the test. -/
  | while_false {b : Cond} {c : Com} {s : State} (hb : b.eval s = some false) :
      BigStep (.while b c) s s (ACost.cost Currency.«while» 1)

/-! ### Inversion

The equation lemmas the wave-B `wp` construction unfolds against. The
primitive ones and the two structural ones are `simp` lemmas; the loop's
is not, because its right-hand side mentions a `BigStep` of the same
loop at another state and rewriting with it does not terminate. -/

@[simp] theorem bigStep_skip_iff {s s' : State} {κ : Cost} :
    BigStep .skip s s' κ ↔ s' = s ∧ κ = ACost.cost Currency.skip 1 := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .skip

@[simp] theorem bigStep_const_iff {s s' : State} {κ : Cost} {x : String} {n : Val} :
    BigStep (.const x n) s s' κ ↔
      s.vars x ≠ none ∧ s' = s.setVar x n ∧ κ = ACost.cost Currency.const 1 := by
  constructor
  · intro h; cases h with | const hx => exact ⟨hx, rfl, rfl⟩
  · rintro ⟨hx, rfl, rfl⟩; exact .const hx

@[simp] theorem bigStep_copy_iff {s s' : State} {κ : Cost} {x y : String} :
    BigStep (.copy x y) s s' κ ↔
      s.vars x ≠ none ∧ ∃ v, s.vars y = some v ∧ s' = s.setVar x v ∧
        κ = ACost.cost Currency.copy 1 := by
  constructor
  · intro h; cases h with | copy hx hy => exact ⟨hx, _, hy, rfl, rfl⟩
  · rintro ⟨hx, v, hy, rfl, rfl⟩; exact .copy hx hy

@[simp] theorem bigStep_binop_iff {s s' : State} {κ : Cost} {op : Imp.Bop} {x y z : String} :
    BigStep (.binop op x y z) s s' κ ↔
      s.vars x ≠ none ∧ ∃ m n, s.vars y = some m ∧ s.vars z = some n ∧
        s' = s.setVar x (op.apply m n) ∧ κ = ACost.cost (binopCurrency op) 1 := by
  constructor
  · intro h; cases h with | binop hx hy hz => exact ⟨hx, _, _, hy, hz, rfl, rfl⟩
  · rintro ⟨hx, m, n, hy, hz, rfl, rfl⟩; exact .binop hx hy hz

@[simp] theorem bigStep_aget_iff {s s' : State} {κ : Cost} {x a i : String} :
    BigStep (.aget x a i) s s' κ ↔
      s.vars x ≠ none ∧ ∃ k xs v, s.vars i = some k ∧ s.arrs a = some xs ∧ xs[k]? = some v ∧
        s' = s.setVar x v ∧ κ = ACost.cost Currency.aget 1 := by
  constructor
  · intro h; cases h with | aget hx hi ha hv => exact ⟨hx, _, _, _, hi, ha, hv, rfl, rfl⟩
  · rintro ⟨hx, k, xs, v, hi, ha, hv, rfl, rfl⟩; exact .aget hx hi ha hv

@[simp] theorem bigStep_aset_iff {s s' : State} {κ : Cost} {a i v : String} :
    BigStep (.aset a i v) s s' κ ↔
      ∃ k n xs, s.vars i = some k ∧ s.vars v = some n ∧ s.arrs a = some xs ∧
        k < xs.length ∧ s' = s.setArr a (xs.set k n) ∧ κ = ACost.cost Currency.aset 1 := by
  constructor
  · intro h; cases h with | aset hi hv ha hk => exact ⟨_, _, _, hi, hv, ha, hk, rfl, rfl⟩
  · rintro ⟨k, n, xs, hi, hv, ha, hk, rfl, rfl⟩; exact .aset hi hv ha hk

/-- Cost additivity over `seq`, in both directions: a sequence runs
through an intermediate state and pays the sum. -/
@[simp] theorem bigStep_seq_iff {c d : Com} {s s'' : State} {κ : Cost} :
    BigStep (.seq c d) s s'' κ ↔
      ∃ s' κ₁ κ₂, BigStep c s s' κ₁ ∧ BigStep d s' s'' κ₂ ∧ κ = κ₁ + κ₂ := by
  constructor
  · intro h; cases h with | seq hc hd => exact ⟨_, _, _, hc, hd, rfl⟩
  · rintro ⟨s', κ₁, κ₂, hc, hd, rfl⟩; exact .seq hc hd

@[simp] theorem bigStep_ite_iff {b : Cond} {c d : Com} {s s' : State} {κ : Cost} :
    BigStep (.ite b c d) s s' κ ↔
      ∃ t κ', b.eval s = some t ∧ BigStep (if t then c else d) s s' κ' ∧
        κ = ACost.cost Currency.ite 1 + κ' := by
  constructor
  · intro h
    cases h with
    | ite_true hb hc => exact ⟨true, _, hb, by simpa using hc, rfl⟩
    | ite_false hb hd => exact ⟨false, _, hb, by simpa using hd, rfl⟩
  · rintro ⟨t, κ', hb, h, rfl⟩
    cases t
    · exact .ite_false hb (by simpa using h)
    · exact .ite_true hb (by simpa using h)

/-- The loop unfolds through its guard, exactly as IMP+'s does: either
the guard holds and the body runs once before the loop runs again, or
the guard fails and only the test is paid for. Not a `simp` lemma — its
right-hand side mentions the same loop. -/
theorem bigStep_while_iff {b : Cond} {c : Com} {s s'' : State} {κ : Cost} :
    BigStep (.while b c) s s'' κ ↔
      (b.eval s = some true ∧ ∃ s' κ₁ κ₂, BigStep c s s' κ₁ ∧
          BigStep (.while b c) s' s'' κ₂ ∧ κ = ACost.cost Currency.«while» 1 + κ₁ + κ₂) ∨
        (b.eval s = some false ∧ s'' = s ∧ κ = ACost.cost Currency.«while» 1) := by
  constructor
  · intro h
    cases h with
    | while_true hb hc hw => exact Or.inl ⟨hb, _, _, _, hc, hw, rfl⟩
    | while_false hb => exact Or.inr ⟨hb, rfl, rfl⟩
  · rintro (⟨hb, s', κ₁, κ₂, hc, hw, rfl⟩ | ⟨hb, rfl, rfl⟩)
    · exact .while_true hb hc hw
    · exact .while_false hb

/-! ### Determinism

The IR is deterministic: there is no nondeterminism below `NRest`, which
is where nondeterminism lives in this tower. IMP+'s `BigStep.unique`,
one for one. -/

/-- The semantics is deterministic in both the final state and the cost:
a command run in a given state has at most one outcome. So the cost of a
terminating run is a function of the program and its input, not a
quantity the prover gets to choose. -/
theorem BigStep.unique {c : Com} {s s₁ s₂ : State} {κ₁ κ₂ : Cost}
    (h₁ : BigStep c s s₁ κ₁) (h₂ : BigStep c s s₂ κ₂) : s₁ = s₂ ∧ κ₁ = κ₂ := by
  induction h₁ generalizing s₂ κ₂ with
  | skip => cases h₂; exact ⟨rfl, rfl⟩
  | const hx => cases h₂ with
    | const hx' => exact ⟨rfl, rfl⟩
  | copy hx hy => cases h₂ with
    | copy hx' hy' => rw [hy] at hy'; cases hy'; exact ⟨rfl, rfl⟩
  | binop hx hy hz => cases h₂ with
    | binop hx' hy' hz' =>
      rw [hy] at hy'; rw [hz] at hz'; cases hy'; cases hz'; exact ⟨rfl, rfl⟩
  | aget hx hi ha hv => cases h₂ with
    | aget hx' hi' ha' hv' =>
      rw [hi] at hi'; cases hi'; rw [ha] at ha'; cases ha'
      rw [hv] at hv'; cases hv'; exact ⟨rfl, rfl⟩
  | aset hi hv ha hk => cases h₂ with
    | aset hi' hv' ha' hk' =>
      rw [hi] at hi'; cases hi'; rw [hv] at hv'; cases hv'
      rw [ha] at ha'; cases ha'; exact ⟨rfl, rfl⟩
  | seq _ _ ih ih' => cases h₂ with
    | seq h h' =>
      obtain ⟨rfl, rfl⟩ := ih h
      obtain ⟨rfl, rfl⟩ := ih' h'
      exact ⟨rfl, rfl⟩
  | ite_true hb _ ih => cases h₂ with
    | ite_true hb' h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
    | ite_false hb' _ => rw [hb] at hb'; exact absurd hb' (by simp)
  | ite_false hb _ ih => cases h₂ with
    | ite_true hb' _ => rw [hb] at hb'; exact absurd hb' (by simp)
    | ite_false hb' h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
  | while_true hb _ _ ih ih' => cases h₂ with
    | while_true hb' h h' =>
      obtain ⟨rfl, rfl⟩ := ih h
      obtain ⟨rfl, rfl⟩ := ih' h'
      exact ⟨rfl, rfl⟩
    | while_false hb' => rw [hb] at hb'; exact absurd hb' (by simp)
  | while_false hb => cases h₂ with
    | while_true hb' _ _ => rw [hb] at hb'; exact absurd hb' (by simp)
    | while_false hb' => exact ⟨rfl, rfl⟩

/-- Determinism of the final state. -/
theorem BigStep.state_unique {c : Com} {s s₁ s₂ : State} {κ₁ κ₂ : Cost}
    (h₁ : BigStep c s s₁ κ₁) (h₂ : BigStep c s s₂ κ₂) : s₁ = s₂ :=
  (h₁.unique h₂).1

/-- Determinism of the cost: a run's price is not a quantity the prover
chooses. -/
theorem BigStep.cost_unique {c : Com} {s s₁ s₂ : State} {κ₁ κ₂ : Cost}
    (h₁ : BigStep c s s₁ κ₁) (h₂ : BigStep c s s₂ κ₂) : κ₁ = κ₂ :=
  (h₁.unique h₂).2

/-! ### The name space is not grown, and no array changes length

The structural property judgment call D-f exists for: a run touches only
the names that were already there, and leaves every array's length
alone. This is the frame property in its pre-separation-logic form, and
wave B's `↦ᵥ` / `↦ₐ` assertions rest on it. -/

/-- No op creates or destroys a scalar cell. -/
theorem BigStep.vars_isSome {c : Com} {s s' : State} {κ : Cost}
    (h : BigStep c s s' κ) (x : String) : (s'.vars x).isSome = (s.vars x).isSome := by
  induction h with
  | skip => rfl
  | const hx | copy hx _ | binop hx _ _ | aget hx _ _ _ =>
    exact State.isSome_vars_setVar hx _ _
  | aset _ _ _ _ => rfl
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false => rfl

/-- The scalar name space is literally invariant. -/
theorem BigStep.vars_dom {c : Com} {s s' : State} {κ : Cost} (h : BigStep c s s' κ) :
    {x | s'.vars x ≠ none} = {x | s.vars x ≠ none} := by
  ext x
  have := h.vars_isSome x
  simp only [Set.mem_setOf_eq, ← Option.isSome_iff_ne_none, this]

/-- No op creates, destroys or resizes an array. -/
theorem BigStep.arrs_length {c : Com} {s s' : State} {κ : Cost}
    (h : BigStep c s s' κ) (a : String) :
    (s'.arrs a).map List.length = (s.arrs a).map List.length := by
  induction h with
  | skip => rfl
  | const _ | copy _ _ | binop _ _ _ | aget _ _ _ _ => rfl
  | aset _ _ ha _ =>
    exact State.map_length_arrs_setArr ha (List.length_set ..) _
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false => rfl

/-- The array name space is invariant too. -/
theorem BigStep.arrs_dom {c : Com} {s s' : State} {κ : Cost} (h : BigStep c s s' κ) :
    {a | s'.arrs a ≠ none} = {a | s.arrs a ≠ none} := by
  ext a
  have := h.arrs_length a
  constructor <;> intro hx <;> simp only [Set.mem_setOf_eq] at hx ⊢ <;>
    · rcases hy : s.arrs a with _ | xs <;> rcases hz : s'.arrs a with _ | ys <;>
        simp_all

/-- Finiteness of the domains is preserved (judgment call D-g). -/
theorem BigStep.finite {c : Com} {s s' : State} {κ : Cost}
    (h : BigStep c s s' κ) (hs : s.Finite) : s'.Finite :=
  ⟨h.vars_dom ▸ hs.1, h.arrs_dom ▸ hs.2⟩

/-! ### The executable twin (ledger D4)

A fuel-indexed evaluator, fuel decreasing at every recursive call, so
that it is structurally recursive and every clause is an equation by
`rfl`. `none` means "out of fuel, stuck, or nonterminating"; the two
agreement theorems below say which. -/

/-- The evaluator: `evalFuel f c s` runs `c` from `s` with `f` units of
fuel, returning the final state and the cost paid. -/
def evalFuel : ℕ → Com → State → Option (State × Cost)
  | 0, _, _ => none
  | _ + 1, .skip, s => some (s, ACost.cost Currency.skip 1)
  | _ + 1, .const x n, s =>
      (s.vars x).bind fun _ =>
        some (s.setVar x n, ACost.cost Currency.const 1)
  | _ + 1, .copy x y, s =>
      (s.vars x).bind fun _ => (s.vars y).bind fun v =>
        some (s.setVar x v, ACost.cost Currency.copy 1)
  | _ + 1, .binop op x y z, s =>
      (s.vars x).bind fun _ => (s.vars y).bind fun m => (s.vars z).bind fun n =>
        some (s.setVar x (op.apply m n), ACost.cost (binopCurrency op) 1)
  | _ + 1, .aget x a i, s =>
      (s.vars x).bind fun _ => (s.vars i).bind fun k => (s.arrs a).bind fun xs =>
        (xs[k]?).bind fun v => some (s.setVar x v, ACost.cost Currency.aget 1)
  | _ + 1, .aset a i v, s =>
      (s.vars i).bind fun k => (s.vars v).bind fun n => (s.arrs a).bind fun xs =>
        if k < xs.length then some (s.setArr a (xs.set k n), ACost.cost Currency.aset 1)
        else none
  | f + 1, .seq c d, s =>
      (evalFuel f c s).bind fun r => (evalFuel f d r.1).bind fun r' =>
        some (r'.1, r.2 + r'.2)
  | f + 1, .ite b c d, s =>
      (b.eval s).bind fun t => (evalFuel f (if t then c else d) s).bind fun r =>
        some (r.1, ACost.cost Currency.ite 1 + r.2)
  | f + 1, .while b c, s =>
      (b.eval s).bind fun t =>
        if t then
          (evalFuel f c s).bind fun r => (evalFuel f (.while b c) r.1).bind fun r' =>
            some (r'.1, ACost.cost Currency.«while» 1 + r.2 + r'.2)
        else some (s, ACost.cost Currency.«while» 1)

@[simp] theorem evalFuel_zero (c : Com) (s : State) : evalFuel 0 c s = none := rfl

@[simp] theorem evalFuel_skip (f : ℕ) (s : State) :
    evalFuel (f + 1) .skip s = some (s, ACost.cost Currency.skip 1) := rfl

@[simp] theorem evalFuel_const (f : ℕ) (x : String) (n : Val) (s : State) :
    evalFuel (f + 1) (.const x n) s =
      (s.vars x).bind fun _ =>
        some (s.setVar x n, ACost.cost Currency.const 1) := rfl

@[simp] theorem evalFuel_copy (f : ℕ) (x y : String) (s : State) :
    evalFuel (f + 1) (.copy x y) s =
      (s.vars x).bind fun _ => (s.vars y).bind fun v =>
        some (s.setVar x v, ACost.cost Currency.copy 1) := rfl

@[simp] theorem evalFuel_binop (f : ℕ) (op : Imp.Bop) (x y z : String) (s : State) :
    evalFuel (f + 1) (.binop op x y z) s =
      (s.vars x).bind fun _ => (s.vars y).bind fun m => (s.vars z).bind fun n =>
        some (s.setVar x (op.apply m n), ACost.cost (binopCurrency op) 1) := rfl

@[simp] theorem evalFuel_aget (f : ℕ) (x a i : String) (s : State) :
    evalFuel (f + 1) (.aget x a i) s =
      (s.vars x).bind fun _ => (s.vars i).bind fun k => (s.arrs a).bind fun xs =>
        (xs[k]?).bind fun v => some (s.setVar x v, ACost.cost Currency.aget 1) := rfl

@[simp] theorem evalFuel_aset (f : ℕ) (a i v : String) (s : State) :
    evalFuel (f + 1) (.aset a i v) s =
      (s.vars i).bind fun k => (s.vars v).bind fun n => (s.arrs a).bind fun xs =>
        if k < xs.length then some (s.setArr a (xs.set k n), ACost.cost Currency.aset 1)
        else none := rfl

@[simp] theorem evalFuel_seq (f : ℕ) (c d : Com) (s : State) :
    evalFuel (f + 1) (.seq c d) s =
      (evalFuel f c s).bind fun r => (evalFuel f d r.1).bind fun r' =>
        some (r'.1, r.2 + r'.2) := rfl

@[simp] theorem evalFuel_ite (f : ℕ) (b : Cond) (c d : Com) (s : State) :
    evalFuel (f + 1) (.ite b c d) s =
      (b.eval s).bind fun t => (evalFuel f (if t then c else d) s).bind fun r =>
        some (r.1, ACost.cost Currency.ite 1 + r.2) := rfl

@[simp] theorem evalFuel_while (f : ℕ) (b : Cond) (c : Com) (s : State) :
    evalFuel (f + 1) (.while b c) s =
      (b.eval s).bind fun t =>
        if t then
          (evalFuel f c s).bind fun r => (evalFuel f (.while b c) r.1).bind fun r' =>
            some (r'.1, ACost.cost Currency.«while» 1 + r.2 + r'.2)
        else some (s, ACost.cost Currency.«while» 1) := rfl

/-- Soundness of the evaluator: whatever it returns, the relation
derives. -/
theorem bigStep_of_evalFuel : ∀ {f : ℕ} {c : Com} {s s' : State} {κ : Cost},
    evalFuel f c s = some (s', κ) → BigStep c s s' κ := by
  intro f
  induction f with
  | zero => intro c s s' κ h; simp at h
  | succ f ih =>
    intro c s s' κ h
    cases c with
    | skip =>
      simp only [evalFuel_skip, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact .skip
    | const x n =>
      simp only [evalFuel_const, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨v₀, hx, rfl, rfl⟩ := h
      exact .const (by rw [hx]; simp)
    | copy x y =>
      simp only [evalFuel_copy, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨v₀, hx, v, hy, rfl, rfl⟩ := h
      exact .copy (by rw [hx]; simp) hy
    | binop op x y z =>
      simp only [evalFuel_binop, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨v₀, hx, m, hy, n, hz, rfl, rfl⟩ := h
      exact .binop (by rw [hx]; simp) hy hz
    | aget x a i =>
      simp only [evalFuel_aget, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨v₀, hx, k, hi, xs, ha, v, hv, rfl, rfl⟩ := h
      exact .aget (by rw [hx]; simp) hi ha hv
    | aset a i v =>
      simp only [evalFuel_aset, Option.bind_eq_some_iff] at h
      obtain ⟨k, hi, n, hv, xs, ha, hlast⟩ := h
      split_ifs at hlast with hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hlast
      obtain ⟨rfl, rfl⟩ := hlast
      exact .aset hi hv ha hk
    | seq c d =>
      simp only [evalFuel_seq, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨⟨s₁, κ₁⟩, hc, ⟨s₂, κ₂⟩, hd, rfl, rfl⟩ := h
      exact .seq (ih hc) (ih hd)
    | ite b c d =>
      simp only [evalFuel_ite, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨t, hb, ⟨s₁, κ₁⟩, hr, rfl, rfl⟩ := h
      exact bigStep_ite_iff.mpr ⟨t, κ₁, hb, ih hr, rfl⟩
    | «while» b c =>
      simp only [evalFuel_while, Option.bind_eq_some_iff] at h
      obtain ⟨t, hb, hrest⟩ := h
      cases t
      · simp only [Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        exact .while_false hb
      · simp only [if_true, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at hrest
        obtain ⟨⟨s₁, κ₁⟩, hc, ⟨s₂, κ₂⟩, hw, rfl, rfl⟩ := hrest
        exact .while_true hb (ih hc) (ih hw)

/-- More fuel never changes an answer. -/
theorem evalFuel_mono : ∀ {f g : ℕ} {c : Com} {s : State} {r : State × Cost},
    f ≤ g → evalFuel f c s = some r → evalFuel g c s = some r := by
  intro f
  induction f with
  | zero => intro g c s r _ h; simp at h
  | succ f ih =>
    intro g c s r hfg h
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hfg' : f ≤ g := by omega
    cases c with
    | skip => rw [evalFuel_skip] at h ⊢; exact h
    | const x n => rw [evalFuel_const] at h ⊢; exact h
    | copy x y => rw [evalFuel_copy] at h ⊢; exact h
    | binop op x y z => rw [evalFuel_binop] at h ⊢; exact h
    | aget x a i => rw [evalFuel_aget] at h ⊢; exact h
    | aset a i v => rw [evalFuel_aset] at h ⊢; exact h
    | seq c d =>
      simp only [evalFuel_seq, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨r₁, hc, r₂, hd, hlast⟩ := h
      exact ⟨r₁, ih hfg' hc, r₂, ih hfg' hd, hlast⟩
    | ite b c d =>
      simp only [evalFuel_ite, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨t, hb, r₁, hr, hlast⟩ := h
      exact ⟨t, hb, r₁, ih hfg' hr, hlast⟩
    | «while» b c =>
      simp only [evalFuel_while, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨t, hb, hrest⟩ := h
      refine ⟨t, hb, ?_⟩
      cases t
      · simpa using hrest
      · simp only [if_true, Option.bind_eq_some_iff] at hrest ⊢
        obtain ⟨r₁, hc, r₂, hw, hlast⟩ := hrest
        exact ⟨r₁, ih hfg' hc, r₂, ih hfg' hw, hlast⟩

/-- Completeness of the evaluator: every derivation is found at some
fuel. -/
theorem exists_evalFuel {c : Com} {s s' : State} {κ : Cost} (h : BigStep c s s' κ) :
    ∃ f, evalFuel f c s = some (s', κ) := by
  induction h with
  | skip => exact ⟨1, rfl⟩
  | const hx =>
    obtain ⟨v, hv⟩ := State.exists_of_vars_ne_none hx
    exact ⟨1, by rw [evalFuel_const, hv]; rfl⟩
  | copy hx hy =>
    obtain ⟨v₀, hv₀⟩ := State.exists_of_vars_ne_none hx
    exact ⟨1, by rw [evalFuel_copy, hv₀, hy]; rfl⟩
  | binop hx hy hz =>
    obtain ⟨v₀, hv₀⟩ := State.exists_of_vars_ne_none hx
    exact ⟨1, by rw [evalFuel_binop, hv₀, hy, hz]; rfl⟩
  | aget hx hi ha hv =>
    obtain ⟨v₀, hv₀⟩ := State.exists_of_vars_ne_none hx
    exact ⟨1, by rw [evalFuel_aget, hv₀, hi, ha]; simp [hv]⟩
  | aset hi hv ha hk =>
    exact ⟨1, by rw [evalFuel_aset, hi, hv, ha]; simp [hk]⟩
  | seq _ _ ih ih' =>
    obtain ⟨f₁, h₁⟩ := ih
    obtain ⟨f₂, h₂⟩ := ih'
    exact ⟨max f₁ f₂ + 1, by
      simp [evalFuel_mono (le_max_left f₁ f₂) h₁, evalFuel_mono (le_max_right f₁ f₂) h₂]⟩
  | ite_true hb _ ih =>
    obtain ⟨f₁, h₁⟩ := ih
    exact ⟨f₁ + 1, by simp [evalFuel_ite, hb, h₁]⟩
  | ite_false hb _ ih =>
    obtain ⟨f₁, h₁⟩ := ih
    exact ⟨f₁ + 1, by simp [evalFuel_ite, hb, h₁]⟩
  | while_true hb _ _ ih ih' =>
    obtain ⟨f₁, h₁⟩ := ih
    obtain ⟨f₂, h₂⟩ := ih'
    exact ⟨max f₁ f₂ + 1, by
      simp [evalFuel_while, hb, evalFuel_mono (le_max_left f₁ f₂) h₁,
        evalFuel_mono (le_max_right f₁ f₂) h₂]⟩
  | while_false hb => exact ⟨1, by simp [evalFuel_while, hb]⟩

/-- The evaluator *is* the relation: the D4 twin agrees in both
directions, so every `#guard` below is a check of `BigStep`. -/
theorem bigStep_iff_exists_evalFuel {c : Com} {s s' : State} {κ : Cost} :
    BigStep c s s' κ ↔ ∃ f, evalFuel f c s = some (s', κ) :=
  ⟨exists_evalFuel, fun ⟨_, h⟩ => bigStep_of_evalFuel h⟩

/-! ### The gate (ledger D4)

Three programs — straight-line arithmetic, an array get/set roundtrip,
and a countdown loop — each pinned by its final state *and* its exact
cost vector, currency by currency, zeros included. Then two negative
controls. Nothing here is used by any other module; it is a gate, not a
library. -/

namespace Gate

open Plausible

/-- A state's scalar cells, by name. -/
def readVars (s : State) (xs : List String) : List (String × Option Val) :=
  xs.map fun x => (x, s.vars x)

/-- A state's arrays, by name. -/
def readArrs (s : State) (as : List String) : List (String × Option (List Val)) :=
  as.map fun a => (a, s.arrs a)

/-- The whole cost vector: every currency of the IR against what the run
paid in it. Pinning this — rather than a single total — is what makes
the per-op account (design record F4) checkable. -/
def costVector (κ : Cost) : List (String × ℕ) :=
  Currency.all.map fun n => (n, κ.toFun n)

/-! #### Straight-line arithmetic -/

/-- `a := 6; b := 7; c := a * b; d := c - b`. -/
def arith : Com :=
  .seq (.const "a" 6) (.seq (.const "b" 7) (.seq (.mul "c" "a" "b") (.sub "d" "c" "b")))

/-- Four cells, all existing (judgment call D-f: nothing is allocated). -/
def arithState : State := State.ofPairs [("a", 0), ("b", 0), ("c", 0), ("d", 0)] []

/-- The evaluator's outcome, as data. -/
def arithOut : State × Cost := (evalFuel 8 arith arithState).getD (arithState, 0)

theorem arith_evalFuel : evalFuel 8 arith arithState = some arithOut := rfl

/-- …and therefore a derivation. -/
theorem arith_bigStep : BigStep arith arithState arithOut.1 arithOut.2 :=
  bigStep_of_evalFuel arith_evalFuel

#guard readVars arithOut.1 ["a", "b", "c", "d"]
  = [("a", some 6), ("b", some 7), ("c", some 42), ("d", some 35)]

#guard costVector arithOut.2 =
  [("ir.skip", 0), ("ir.const", 2), ("ir.copy", 0), ("ir.aget", 0), ("ir.aset", 0),
   ("ir.ite", 0), ("ir.while", 0), ("ir.add", 0), ("ir.sub", 1), ("ir.mul", 1),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! #### An array get/set roundtrip -/

/-- `x := A[i]; A[j] := x`. -/
def roundtrip : Com := .seq (.aget "x" "A" "i") (.aset "A" "j" "x")

/-- `A = [3, 1, 4]`, `i = 0`, `j = 2`: read the head, write it at the
last position. -/
def roundtripState : State :=
  State.ofPairs [("x", 0), ("i", 0), ("j", 2)] [("A", [3, 1, 4])]

/-- The evaluator's outcome, as data. -/
def roundtripOut : State × Cost :=
  (evalFuel 8 roundtrip roundtripState).getD (roundtripState, 0)

theorem roundtrip_evalFuel : evalFuel 8 roundtrip roundtripState = some roundtripOut := rfl

/-- …and therefore a derivation. -/
theorem roundtrip_bigStep : BigStep roundtrip roundtripState roundtripOut.1 roundtripOut.2 :=
  bigStep_of_evalFuel roundtrip_evalFuel

#guard readVars roundtripOut.1 ["x", "i", "j"] = [("x", some 3), ("i", some 0), ("j", some 2)]

#guard readArrs roundtripOut.1 ["A"] = [("A", some [3, 1, 3])]

#guard costVector roundtripOut.2 =
  [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 1), ("ir.aset", 1),
   ("ir.ite", 0), ("ir.while", 0), ("ir.add", 0), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! #### A countdown loop -/

/-- `one := 1; while 0 < n do n := n - one`. -/
def countdown : Com :=
  .seq (.const "one" 1) (.while (.lt (.lit 0) (.cell "n")) (.sub "n" "n" "one"))

/-- The loop's state: `n` counting down and the constant cell it
subtracts. -/
def countdownState (n : ℕ) : State := State.ofPairs [("n", n), ("one", 0)] []

/-- Enough fuel for `n` iterations: the loop needs `n + 1`, the leading
`const` one more. -/
def countdownFuel (n : ℕ) : ℕ := n + 4

/-- The evaluator's outcome, as data. -/
def countdownOut (n : ℕ) : State × Cost :=
  (evalFuel (countdownFuel n) countdown (countdownState n)).getD (countdownState n, 0)

theorem countdown_evalFuel :
    evalFuel (countdownFuel 5) countdown (countdownState 5) = some (countdownOut 5) := rfl

/-- …and therefore a derivation. -/
theorem countdown_bigStep :
    BigStep countdown (countdownState 5) (countdownOut 5).1 (countdownOut 5).2 :=
  bigStep_of_evalFuel countdown_evalFuel

#guard readVars (countdownOut 5).1 ["n", "one"] = [("n", some 0), ("one", some 1)]

#guard costVector (countdownOut 5).2 =
  [("ir.skip", 0), ("ir.const", 1), ("ir.copy", 0), ("ir.aget", 0), ("ir.aset", 0),
   ("ir.ite", 0), ("ir.while", 6), ("ir.add", 0), ("ir.sub", 5), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! #### Property checks

Plausible over the countdown's parameter: the loop's answer and its
*cost*, currency by currency, as a function of the number of iterations
— `n + 1` guard evaluations and `n` subtractions. The parameter is
reduced modulo a small bound so that the sampler stays inside the fuel
the family is stated with. -/

-- The countdown reaches zero.
#test ∀ n : ℕ, ((evalFuel (countdownFuel (n % 12)) countdown (countdownState (n % 12))).map
  fun r => r.1.vars "n") = some (some 0)

-- `n` iterations charge `n + 1` guard evaluations.
#test ∀ n : ℕ, ((evalFuel (countdownFuel (n % 12)) countdown (countdownState (n % 12))).map
  fun r => r.2.toFun Currency.«while») = some (n % 12 + 1)

-- …and exactly `n` subtractions.
#test ∀ n : ℕ, ((evalFuel (countdownFuel (n % 12)) countdown (countdownState (n % 12))).map
  fun r => r.2.toFun Currency.sub) = some (n % 12)

-- A binop computes IMP+'s `Bop.apply`, on sampled operands.
#test ∀ m n : ℕ, ((evalFuel 2 (.add "z" "x" "y")
  (State.ofPairs [("x", m), ("y", n), ("z", 0)] [])).map fun r => r.1.vars "z")
    = some (some (m + n))

/-! #### Negative controls -/

/-- `A` has three entries and `i` holds `5`. -/
def oobState : State := State.ofPairs [("x", 0), ("i", 5)] [("A", [3, 1, 4])]

-- The evaluator refuses…
#guard evalFuel 8 (.aget "x" "A" "i") oobState = none

/-- …and there is no derivation at all: an out-of-range read is stuck,
not defaulted (judgment call D-f). -/
theorem no_bigStep_oob : ¬ ∃ s' κ, BigStep (.aget "x" "A" "i") oobState s' κ := by
  rintro ⟨s', κ, h⟩
  rw [bigStep_aget_iff] at h
  obtain ⟨-, k, xs, v, hi, ha, hv, -, -⟩ := h
  rw [show oobState.vars "i" = some 5 from rfl] at hi
  rw [show oobState.arrs "A" = some [3, 1, 4] from rfl] at ha
  cases hi
  cases ha
  rw [show ([3, 1, 4] : List Val)[(5 : ℕ)]? = none from rfl] at hv
  exact absurd hv (by simp)

-- A wrong cost is rejected: the countdown from 5 pays six guard
-- evaluations, not five.
#guard ¬ ((countdownOut 5).2.toFun Currency.«while» = 5)

/-- …and not merely by the evaluator: by determinism, *no* derivation
pays five. -/
theorem countdown_no_wrong_cost {s' : State} {κ : Cost}
    (h : BigStep countdown (countdownState 5) s' κ) :
    κ.toFun Currency.«while» ≠ 5 := by
  obtain ⟨-, rfl⟩ :=
    BigStep.unique countdown_bigStep h
  decide

end Gate

end Lax13Proofs.Refine.Ir
