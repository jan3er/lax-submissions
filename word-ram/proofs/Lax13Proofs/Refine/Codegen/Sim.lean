import Lax13Proofs.Refine.Codegen.Embed
import Lax13Proofs.Refine.Codegen.BigStepB

/-!
The simulation theorem: an IR run compiles into an IMP+ run, and the
per-op cost account is cashed into IMP+'s single time unit.

**This file is ours** (ledger **D3**); its specification is
`plans/word-ram/refinement-tower/p5-codegen-design.md` §3.

## The price map

The tower keeps its currencies apart all the way down — a cost is a
*per-op account*, `ACost String ℕ`, and `Ir/Syntax.lean` gives one
currency per op precisely so that a cost vector records which arithmetic
a run did. Collapsing that account into one number happens exactly once,
here, and the exchange rate is what the embedded program actually pays:

| currency | `weight` | what IMP+ charges for the embedded op |
|---|---|---|
| `ir.skip` | 1 | `skip`: `1` |
| `ir.const` | 2 | `assign x (lit n)`: `1 + 1` |
| `ir.copy` | 2 | `assign x (var y)`: `1 + 1` |
| `ir.aget` | 3 | `assign x (get a (var i))`: `1 + 2` |
| `ir.aset` | 3 | `store a (var i) (var v)`: `1 + 1 + 1` |
| `ir.ite` | 4 | test: `1 + 3` |
| `ir.while` | 4 | test: `1 + 3` |
| each of the nine binop currencies | 4 | `assign x (bin op (var y) (var z))`: `1 + 3` |

The table of the design record is exact, not merely safe: every entry is
the IMP+ cost of the embedded op **on the nose**, so `k ≤ cash κ` below
is in fact an equality for every derivation, and the constant factor the
tower loses at codegen is `4`. (The inequality is what is stated, because
that is what `Run`/`Spec` consume and because a later change of the
embedding should not have to be exact to stay sound.) The gate at the end
of the file pins the two sides against each other for three programs.

## The theorem

```
Ir.BigStepB B c s s' κ → Ir.StateBound B s → agree s σ →
  ∃ σ' k, Imp.BigStepB B (embed c) σ σ' k ∧ agree s' σ' ∧ k ≤ cash κ
        ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out
```

by induction on the bounded IR derivation. The three hypotheses each do
one job: the bounded derivation supplies the `< B` facts at the two
value-creation sites and at the guards, the state invariant supplies them
everywhere a value is merely *moved* (`copy`, `aget`, `aset`, and the
cells of a guard) and is carried along the induction by
`BigStepB.stateBound`, and agreement supplies the values themselves. The
two tape clauses are not decoration: the IR has no tape ops (ledger note
N3), so a compiled IR run is exactly the part of a harnessed program that
leaves the tapes alone, which is what wave A2's prelude/epilogue lemmas
compose against.

## Judgment calls

**P5/D-k — `cash` is a function `Codegen.cash`, not dot notation on the
cost.** The design record writes `κ.cash`. `Ir.Cost` is an `abbrev` for
`ACost String ℕ`, so dot notation on it resolves against `ACost`, and a
declaration `ACost.cash` would put an IR-specific price map — one that
mentions `Ir.Currency.all` — into the generic cost-algebra namespace two
directories up. `cash κ` is written out instead; nothing else changes.

**P5/D-l — the price map is total, `0` off the IR's sixteen
currencies.** `weight` is a function `String → ℕ` and `cash` sums over
`Currency.all`, so a currency outside the IR's own set is priced at zero
and, being outside the sum, contributes nothing either way. No support
lemma about IR costs is therefore needed anywhere: `cash` is additive
(`cash_add`) and its value on each per-op singleton is a numeral
(`cash_cost_*`), and those two facts carry the whole induction.
-/

namespace Lax13Proofs.Refine.Codegen

open Lax13Proofs.Refine.Ir

/-! ### The price map -/

/-- The price of one unit of a currency, in IMP+ time units: what the
embedded op actually costs. Currencies outside the IR's own sixteen are
free — they never occur in an IR cost (judgment call P5/D-l). -/
def weight (c : String) : ℕ :=
  if c = Currency.skip then 1
  else if c = Currency.const then 2
  else if c = Currency.copy then 2
  else if c = Currency.aget then 3
  else if c = Currency.aset then 3
  else if c = Currency.ite then 4
  else if c = Currency.«while» then 4
  else if c = Currency.add then 4
  else if c = Currency.sub then 4
  else if c = Currency.mul then 4
  else if c = Currency.div then 4
  else if c = Currency.and then 4
  else if c = Currency.or then 4
  else if c = Currency.xor then 4
  else if c = Currency.shiftl then 4
  else if c = Currency.shiftr then 4
  else 0

@[simp] theorem weight_skip : weight Currency.skip = 1 := by decide +kernel
@[simp] theorem weight_const : weight Currency.const = 2 := by decide +kernel
@[simp] theorem weight_copy : weight Currency.copy = 2 := by decide +kernel
@[simp] theorem weight_aget : weight Currency.aget = 3 := by decide +kernel
@[simp] theorem weight_aset : weight Currency.aset = 3 := by decide +kernel
@[simp] theorem weight_ite : weight Currency.ite = 4 := by decide +kernel
@[simp] theorem weight_while : weight Currency.«while» = 4 := by decide +kernel

/-- Every arithmetic op costs the same four units: the embedded
`assign x (bin op (var y) (var z))` evaluates an expression of size
three whatever the operator is. -/
@[simp] theorem weight_binopCurrency (op : Imp.Bop) : weight (binopCurrency op) = 4 := by
  cases op <;> decide +kernel

/-- No currency of the IR is priced above four: the constant factor the
tower loses at the codegen boundary. Currencies outside `Currency.all`
are irrelevant — `cash` does not sum over them. -/
theorem weight_le_four : ∀ c ∈ Currency.all, weight c ≤ 4 := by decide +kernel

/-- **Cashing.** A per-op cost account, valued in IMP+ time units.
Written `cash κ` rather than `κ.cash` (judgment call P5/D-k). -/
def cash (κ : Ir.Cost) : ℕ := (Currency.all.map fun c => weight c * κ.toFun c).sum

@[simp] theorem cash_zero : cash 0 = 0 := by simp [cash, Currency.all]

/-- The generic step behind additivity: the price map is linear in the
account, list by list. -/
private theorem sum_map_weight_add (l : List String) (f g : String → ℕ) :
    (l.map fun c => weight c * (f c + g c)).sum
      = (l.map fun c => weight c * f c).sum + (l.map fun c => weight c * g c).sum := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Nat.mul_add]
      omega

/-- Cashing is additive, which is what carries it through `seq`, `ite`
and `while`. -/
@[simp] theorem cash_add (κ κ' : Ir.Cost) : cash (κ + κ') = cash κ + cash κ' := by
  simp only [cash, ACost.toFun_add]
  exact sum_map_weight_add _ _ _

@[simp] theorem cash_cost_skip : cash (ACost.cost Currency.skip 1) = 1 := by decide +kernel
@[simp] theorem cash_cost_const : cash (ACost.cost Currency.const 1) = 2 := by decide +kernel
@[simp] theorem cash_cost_copy : cash (ACost.cost Currency.copy 1) = 2 := by decide +kernel
@[simp] theorem cash_cost_aget : cash (ACost.cost Currency.aget 1) = 3 := by decide +kernel
@[simp] theorem cash_cost_aset : cash (ACost.cost Currency.aset 1) = 3 := by decide +kernel
@[simp] theorem cash_cost_ite : cash (ACost.cost Currency.ite 1) = 4 := by decide +kernel
@[simp] theorem cash_cost_while : cash (ACost.cost Currency.«while» 1) = 4 := by decide +kernel

@[simp] theorem cash_cost_binop (op : Imp.Bop) :
    cash (ACost.cost (binopCurrency op) 1) = 4 := by cases op <;> decide +kernel

/-! ### Guards through the embedding -/

/-- A bounded IR guard evaluates, on the IMP+ side, to the same truth
value. Both operands are read through `agree`, and both are below the
bound because the IR guard was evaluated by the bounded `Cond.evalB`
(judgment call P5/D-i in `BigStepB.lean`). -/
theorem agree.evalB_cond {B : ℕ} {s : Ir.State} {σ : Imp.Env} (h : agree s σ)
    {b : Ir.Cond} {r : Bool} (hb : b.evalB B s = some r) :
    (embedCond b).evalB B σ = some r := by
  cases b with
  | eq u v =>
      rw [Ir.Cond.evalB_eq, Option.bind_eq_some_iff] at hb
      obtain ⟨m, hm, hb⟩ := hb
      rw [Option.map_eq_some_iff] at hb
      obtain ⟨n, hn, rfl⟩ := hb
      exact Reasoning.evalB_condEq
        (h.evalB_operand (Ir.Operand.eval_of_evalB hm) (Ir.Operand.lt_of_evalB hm))
        (h.evalB_operand (Ir.Operand.eval_of_evalB hn) (Ir.Operand.lt_of_evalB hn))
  | lt u v =>
      rw [Ir.Cond.evalB_lt, Option.bind_eq_some_iff] at hb
      obtain ⟨m, hm, hb⟩ := hb
      rw [Option.map_eq_some_iff] at hb
      obtain ⟨n, hn, rfl⟩ := hb
      exact Reasoning.evalB_condLt
        (h.evalB_operand (Ir.Operand.eval_of_evalB hm) (Ir.Operand.lt_of_evalB hm))
        (h.evalB_operand (Ir.Operand.eval_of_evalB hn) (Ir.Operand.lt_of_evalB hn))

/-! ### The simulation theorem -/

/-- **The simulation theorem.** A bounded IR run of `c` from a state
satisfying the value invariant, matched by an IMP+ environment, is
matched by a bounded IMP+ run of `embed c`: the final states agree, the
IMP+ cost is at most the cashed IR cost, and neither tape moves. -/
theorem embed_sim {B : ℕ} {c : Ir.Com} {s s' : Ir.State} {κ : Ir.Cost} {σ : Imp.Env}
    (h : Ir.BigStepB B c s s' κ) (hs : Ir.StateBound B s) (hσ : agree s σ) :
    ∃ σ' k, Imp.BigStepB B (embed c) σ σ' k ∧ agree s' σ' ∧ k ≤ cash κ ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have key : ∀ (c : Ir.Com) (s s' : Ir.State) (κ : Ir.Cost), Ir.BigStepB B c s s' κ →
      ∀ σ : Imp.Env, Ir.StateBound B s → agree s σ →
        ∃ σ' k, Imp.BigStepB B (embed c) σ σ' k ∧ agree s' σ' ∧ k ≤ cash κ ∧
          σ'.inp = σ.inp ∧ σ'.out = σ.out := by
    clear h hs hσ σ κ s s' c
    intro c s s' κ h
    induction h with
    | skip => exact fun σ _ hσ => ⟨σ, 1, .skip, hσ, by simp, rfl, rfl⟩
    | @const s x n hx hn =>
        intro σ _ hσ
        exact ⟨σ.setVar x n, _, .assign (Imp.fit_self hn), hσ.setVar x n, by simp, rfl, rfl⟩
    | @copy s x y v hx hy =>
        intro σ hs hσ
        exact ⟨σ.setVar x v, _, .assign (hσ.evalB_var hy (hs.var hy)), hσ.setVar x v,
          by simp, rfl, rfl⟩
    | @binop s op x y z m n hx hy hz hb =>
        intro σ hs hσ
        refine ⟨σ.setVar x (op.apply m n), _,
          .assign (Reasoning.evalB_bin (hσ.evalB_var hy (hs.var hy))
            (hσ.evalB_var hz (hs.var hz)) hb), hσ.setVar x _, ?_, rfl, rfl⟩
        simp
    | @aget s x a i k v xs hx hi ha hv =>
        intro σ hs hσ
        refine ⟨σ.setVar x v, _,
          .assign (Reasoning.evalB_get (hσ.evalB_var hi (hs.var hi))
            (by rw [hσ.arr ha]; exact hv) (hs.getElem ha hv)), hσ.setVar x v, ?_, rfl, rfl⟩
        simp
    | @aset s a i v k n xs hi hv ha hk =>
        intro σ hs hσ
        refine ⟨σ.setArr a k n, _,
          .store (hσ.evalB_var hi (hs.var hi)) (hσ.evalB_var hv (hs.var hv))
            (by rw [hσ.arr ha]; exact hk), hσ.setArr ha k n, ?_, rfl, rfl⟩
        simp
    | @seq c d s s₁ s₂ κ₁ κ₂ hc hd ihc ihd =>
        intro σ hs hσ
        obtain ⟨σ₁, k₁, hrun₁, hag₁, hk₁, hi₁, ho₁⟩ := ihc σ hs hσ
        obtain ⟨σ₂, k₂, hrun₂, hag₂, hk₂, hi₂, ho₂⟩ := ihd σ₁ (hc.stateBound hs) hag₁
        exact ⟨σ₂, k₁ + k₂, .seq hrun₁ hrun₂, hag₂, by rw [cash_add]; omega,
          by rw [hi₂, hi₁], by rw [ho₂, ho₁]⟩
    | @ite_true b c d s s₁ κ₁ hb _ ih =>
        intro σ hs hσ
        obtain ⟨σ₁, k₁, hrun, hag, hk, hi, ho⟩ := ih σ hs hσ
        refine ⟨σ₁, _, .ite_true (hσ.evalB_cond hb) hrun, hag, ?_, hi, ho⟩
        rw [cash_add, cash_cost_ite, size_embedCond]
        omega
    | @ite_false b c d s s₁ κ₁ hb _ ih =>
        intro σ hs hσ
        obtain ⟨σ₁, k₁, hrun, hag, hk, hi, ho⟩ := ih σ hs hσ
        refine ⟨σ₁, _, .ite_false (hσ.evalB_cond hb) hrun, hag, ?_, hi, ho⟩
        rw [cash_add, cash_cost_ite, size_embedCond]
        omega
    | @while_true b c s s₁ s₂ κ₁ κ₂ hb hbody _ ih ihw =>
        intro σ hs hσ
        obtain ⟨σ₁, k₁, hrun₁, hag₁, hk₁, hi₁, ho₁⟩ := ih σ hs hσ
        obtain ⟨σ₂, k₂, hrun₂, hag₂, hk₂, hi₂, ho₂⟩ := ihw σ₁ (hbody.stateBound hs) hag₁
        refine ⟨σ₂, _, .while_true (hσ.evalB_cond hb) hrun₁ hrun₂, hag₂, ?_,
          by rw [hi₂, hi₁], by rw [ho₂, ho₁]⟩
        rw [cash_add, cash_add, cash_cost_while, size_embedCond]
        omega
    | @while_false b c s hb =>
        intro σ _ hσ
        refine ⟨σ, _, .while_false (hσ.evalB_cond hb), hσ, ?_, rfl, rfl⟩
        rw [cash_cost_while, size_embedCond]
  exact key c s s' κ h σ hs hσ

/-- The cost half of the simulation, in the shape the reasoning kit's
`Run` judgment takes: an IR run of cashed cost `K` compiles into an IMP+
run of cost at most `K`. -/
theorem embed_run {B : ℕ} {c : Ir.Com} {s s' : Ir.State} {κ : Ir.Cost} {σ : Imp.Env}
    (h : Ir.BigStepB B c s s' κ) (hs : Ir.StateBound B s) (hσ : agree s σ) :
    ∃ σ', Reasoning.Run B (embed c) σ σ' (cash κ) ∧ agree s' σ' ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  obtain ⟨σ', k, hrun, hag, hk, hi, ho⟩ := embed_sim h hs hσ
  exact ⟨σ', ⟨k, hk, hrun⟩, hag, hi, ho⟩

/-! ### The gate (ledger D4)

The price map is an arithmetic claim about two semantics, so it is
checked against both: the IR side by the executable twin of
`Ir/Semantics.lean` (`#guard` on `cash` of the cost vector the evaluator
computes), the IMP+ side by an explicit bounded derivation whose cost the
constructors fix. The three programs are `Ir/Semantics.lean`'s own gate
programs — straight-line arithmetic, an array roundtrip, and a loop —
so the two sides are run on literally the same code.

Then two negative controls: a price map with the binop weight lowered to
three, shown to under-cover a real run; and the guard-literal program of
`BigStepB.lean`'s judgment call P5/D-i, shown to have no bounded IMP+ run
at all. -/

namespace Gate

/-- The bound the gate runs under. -/
def B : ℕ := 128

/-! #### Straight-line arithmetic: `a := 6; b := 7; c := a * b; d := c - b` -/

/-- The IMP+ environment of the IR gate state — agreement is free
(`agree_envOf`), so the two sides are run on the same data as well as on
the same code. -/
def arithEnv : Imp.Env := envOf Ir.Gate.arithState

-- The IR side: the per-op account of the run, cashed.
#guard cash Ir.Gate.arithOut.2 = 12

/-- The IMP+ side, from an explicit bounded derivation: the compiled
program costs exactly what the account cashes for, and computes the same
answer. -/
theorem gate_arith :
    ∃ σ' k, Imp.BigStepB B (embed Ir.Gate.arith) arithEnv σ' k ∧
      k = cash Ir.Gate.arithOut.2 ∧ σ'.vars "d" = 35 := by
  have h1 : (Imp.Expr.lit 6).evalB B arithEnv = some 6 := by decide +kernel
  have h2 : (Imp.Expr.lit 7).evalB B (arithEnv.setVar "a" 6) = some 7 := by decide +kernel
  have h3 : (Imp.Expr.bin .mul (.var "a") (.var "b")).evalB B
      ((arithEnv.setVar "a" 6).setVar "b" 7) = some 42 := by decide +kernel
  have h4 : (Imp.Expr.bin .sub (.var "c") (.var "b")).evalB B
      (((arithEnv.setVar "a" 6).setVar "b" 7).setVar "c" 42) = some 35 := by decide +kernel
  exact ⟨_, _, .seq (.assign h1) (.seq (.assign h2) (.seq (.assign h3) (.assign h4))),
    by decide +kernel, by decide +kernel⟩

/-! #### An array roundtrip: `x := A[i]; A[j] := x` -/

/-- The IMP+ environment of `Ir.Gate.roundtripState`. -/
def rtEnv : Imp.Env := envOf Ir.Gate.roundtripState

#guard cash Ir.Gate.roundtripOut.2 = 6

theorem gate_roundtrip :
    ∃ σ' k, Imp.BigStepB B (embed Ir.Gate.roundtrip) rtEnv σ' k ∧
      k = cash Ir.Gate.roundtripOut.2 ∧ σ'.arrs "A" = [3, 1, 3] := by
  have h1 : (Imp.Expr.get "A" (.var "i")).evalB B rtEnv = some 3 := by decide +kernel
  have h2 : (Imp.Expr.var "j").evalB B (rtEnv.setVar "x" 3) = some 2 := by decide +kernel
  have h3 : (Imp.Expr.var "x").evalB B (rtEnv.setVar "x" 3) = some 3 := by decide +kernel
  have h4 : 2 < ((rtEnv.setVar "x" 3).arrs "A").length := by decide +kernel
  exact ⟨_, _, .seq (.assign h1) (.store h2 h3 h4), by decide +kernel, by decide +kernel⟩

/-! #### A loop: `one := 1; while 0 < n do n := n - one`, from `n = 2` -/

/-- The environment the countdown starts in. -/
def cdEnv0 : Imp.Env := envOf (Ir.Gate.countdownState 2)

/-- After the leading `one := 1`. -/
def cdEnv1 : Imp.Env := cdEnv0.setVar "one" 1
/-- After the first iteration. -/
def cdEnv2 : Imp.Env := cdEnv1.setVar "n" 1
/-- After the second iteration. -/
def cdEnv3 : Imp.Env := cdEnv2.setVar "n" 0

-- Two iterations: one `const`, three guard evaluations, two subtractions
-- — `2 + 3 * 4 + 2 * 4 = 22`.
#guard cash (Ir.Gate.countdownOut 2).2 = 22

theorem gate_countdown :
    ∃ σ' k, Imp.BigStepB B (embed Ir.Gate.countdown) cdEnv0 σ' k ∧
      k = cash (Ir.Gate.countdownOut 2).2 ∧ σ'.vars "n" = 0 := by
  have hone : (Imp.Expr.lit 1).evalB B cdEnv0 = some 1 := by decide +kernel
  have hb1 : (Imp.Cond.lt (.lit 0) (.var "n")).evalB B cdEnv1 = some true := by decide +kernel
  have hs1 : (Imp.Expr.bin .sub (.var "n") (.var "one")).evalB B cdEnv1 = some 1 := by decide +kernel
  have hb2 : (Imp.Cond.lt (.lit 0) (.var "n")).evalB B cdEnv2 = some true := by decide +kernel
  have hs2 : (Imp.Expr.bin .sub (.var "n") (.var "one")).evalB B cdEnv2 = some 0 := by decide +kernel
  have hb3 : (Imp.Cond.lt (.lit 0) (.var "n")).evalB B cdEnv3 = some false := by decide +kernel
  exact ⟨_, _, .seq (.assign hone)
      (.while_true hb1 (.assign hs1) (.while_true hb2 (.assign hs2) (.while_false hb3))),
    by decide +kernel, by decide +kernel⟩

/-! #### Negative control 1: a price map that under-covers

The design table's binop weight is `4`, the cost of
`assign x (bin op (var y) (var z))`. Lowering it to `3` is the natural
off-by-one, and it makes the cashing inequality false on the very first
gate program — the run costs `12` and the wrong map cashes `10`. -/

/-- The price map with the weight of the two arithmetic ops the gate
program uses lowered by one. -/
def weightBad (c : String) : ℕ := if c = Currency.mul ∨ c = Currency.sub then 3 else weight c

/-- …and its cashing. -/
def cashBad (κ : Ir.Cost) : ℕ := (Currency.all.map fun c => weightBad c * κ.toFun c).sum

-- The real run costs 12 (`gate_arith`), the wrong map cashes 10: the
-- inequality `k ≤ cash κ` fails.
#guard cashBad Ir.Gate.arithOut.2 = 10
#guard ¬ (12 ≤ cashBad Ir.Gate.arithOut.2)

/-- Stated as the refutation it is: with the wrong weights there is a
run of the compiled program whose cost exceeds the cashed account. -/
theorem cashBad_undercovers :
    ∃ σ' k, Imp.BigStepB B (embed Ir.Gate.arith) arithEnv σ' k ∧
      ¬ (k ≤ cashBad Ir.Gate.arithOut.2) := by
  obtain ⟨σ', k, hrun, hk, -⟩ := gate_arith
  exact ⟨σ', k, hrun, by rw [hk]; decide⟩

/-! #### Negative control 2: judgment call P5/D-i

A guard comparing a cell against a literal at or above the bound. The
*plain* IR semantics runs it, and `BigStepB.lean`'s `no_bigStepB_bigGuard`
shows the bounded IR semantics does not; here is the other half of the
reason it must not — the embedded program has no bounded IMP+ run either,
so a simulation theorem stated over plain IR runs would be false. -/

/-- `n = 3`, and the guard tests `n < 200` against a bound of `128`. -/
def guardEnv : Imp.Env := envOf Ir.BoundGate.bigGuardState

theorem no_bigStepB_embed_bigGuard :
    ¬ ∃ σ' k, Imp.BigStepB B
      (embed (.ite (.lt (.cell "n") (.lit 200)) .skip .skip)) guardEnv σ' k := by
  rintro ⟨σ', k, h⟩
  cases h with
  | ite_true hb => exact absurd hb (by decide)
  | ite_false hb => exact absurd hb (by decide)

/-! #### The axiom check -/

#print axioms embed_sim
#print axioms embed_run
#print axioms Ir.BigStepB.stateBound
#print axioms Ir.BigStep.eq_of_bigStepB
#print axioms gate_arith
#print axioms gate_roundtrip
#print axioms gate_countdown
#print axioms cashBad_undercovers
#print axioms no_bigStepB_embed_bigGuard

end Gate

end Lax13Proofs.Refine.Codegen
