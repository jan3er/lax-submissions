import Lax13Proofs.Refine.Ir.Semantics
import Lax13Proofs.Reasoning

/-!
The embedding of the IR into IMP+, and the state agreement it preserves.

**This file is ours.** So is the whole of `Refine/Codegen/`: ledger
**D3** records that `isabelle_llvm_time`'s last step is a *trusted*
printer from `llM` to LLVM text, whereas ours is a verified translation
into the deep IMP+ embedding that the endorsed `Transfer` boundary
already consumes. There is therefore no Isabelle original to stay
faithful to, and the specification is
`plans/word-ram/refinement-tower/p5-codegen-design.md` §1; deviations
from *that* are the `P5/D-…` flags below.

## What the embedding is

One IMP+ command per IR op, name for name — the IR is three-address and
IMP+ is name-based, so no layout map is needed here and none is
introduced (the endorsed `Compile.compileProgram L` is what turns names
into machine addresses, downstream).

| IR | IMP+ | IMP+ cost |
|---|---|---|
| `skip` | `skip` | `1` |
| `const x n` | `assign x (lit n)` | `1 + 1 = 2` |
| `copy x y` | `assign x (var y)` | `1 + 1 = 2` |
| `binop op x y z` | `assign x (bin op (var y) (var z))` | `1 + 3 = 4` |
| `aget x a i` | `assign x (get a (var i))` | `1 + 2 = 3` |
| `aset a i v` | `store a (var i) (var v)` | `1 + 1 + 1 = 3` |
| `seq` / `ite` / `while` | structural | test `1 + 3 = 4` |

The IR's binary operators *are* `Imp.Bop` (`Ir/Syntax.lean`, judgment
call D-a), so the arithmetic of the two layers agrees definitionally and
`embed` carries the operator across unchanged. Conditions embed operand
for operand: a cell becomes `Expr.var`, a literal becomes `Expr.lit`,
both of size `1`, so every embedded condition has size `3` whatever the
operand mix — which is what makes the price of a test a constant.

## Agreement

`Ir.State` is partial and `Imp.Env` is total, so the two can only be
compared where the IR state is defined: `agree s σ` says that every
scalar cell and every array that *exists* in `s` holds in `σ` what it
holds in `s`, and says nothing about the rest of `σ`. That is the right
strength in both directions. It is weak enough to be established by an
initialising prelude that has also set up cells the IR never mentions,
and strong enough to run the simulation, because an IR op that touches
an undefined name has no derivation at all (`Ir/Semantics.lean` judgment
call D-f): the simulation never has to look where `agree` is silent.

Agreement is preserved by exactly the two updates the semantics
performs — `State.setVar` against `Env.setVar`, and `State.setArr` of a
pointwise-updated list against `Env.setArr` — and those two lemmas,
with the operand-reading lemma, are the whole interface `Sim.lean`
consumes.

## Judgment calls

**P5/D-h — `agree` is a plain conjunction of two universally quantified
implications, not a structure.** The design record names it `agree` in
lower case and uses it only through its two projections; a `def` into
`Prop` with `agree.var` / `agree.arr` accessors gives exactly that,
keeps the name the record uses, and avoids introducing a one-off
structure whose constructor no consumer would ever name.
-/

namespace Lax13Proofs.Refine.Codegen

open Lax13Proofs.Refine.Ir

/-! ### The translation -/

/-- An IR operand becomes an IMP+ expression: a cell is a variable, a
literal is a literal. Both have size `1`, so an embedded condition costs
the same whatever its operands are. -/
def embedOperand : Ir.Operand → Imp.Expr
  | .cell x => .var x
  | .lit n => .lit n

@[simp] theorem embedOperand_cell (x : String) : embedOperand (.cell x) = .var x := rfl
@[simp] theorem embedOperand_lit (n : Ir.Val) : embedOperand (.lit n) = .lit n := rfl

/-- Every embedded operand has size `1`. -/
@[simp] theorem size_embedOperand (u : Ir.Operand) : (embedOperand u).size = 1 := by
  cases u <;> rfl

/-- An IR condition becomes the IMP+ condition with the same
constructor over the embedded operands. -/
def embedCond : Ir.Cond → Imp.Cond
  | .eq u v => .eq (embedOperand u) (embedOperand v)
  | .lt u v => .lt (embedOperand u) (embedOperand v)

@[simp] theorem embedCond_eq (u v : Ir.Operand) :
    embedCond (.eq u v) = .eq (embedOperand u) (embedOperand v) := rfl
@[simp] theorem embedCond_lt (u v : Ir.Operand) :
    embedCond (.lt u v) = .lt (embedOperand u) (embedOperand v) := rfl

/-- Every embedded condition has size `3`, so every test of an embedded
program costs `1 + 3 = 4`. This is the fact behind the `ite` and
`while` entries of the price map (`Sim.lean`). -/
@[simp] theorem size_embedCond (b : Ir.Cond) : (embedCond b).size = 3 := by
  cases b <;> simp [embedCond, Imp.Cond.size]

/-- **The code generator.** One IMP+ command per IR op, name for name,
per the table in the module header. -/
def embed : Ir.Com → Imp.Com
  | .skip => .skip
  | .const x n => .assign x (.lit n)
  | .copy x y => .assign x (.var y)
  | .binop op x y z => .assign x (.bin op (.var y) (.var z))
  | .aget x a i => .assign x (.get a (.var i))
  | .aset a i v => .store a (.var i) (.var v)
  | .seq c d => .seq (embed c) (embed d)
  | .ite b c d => .ite (embedCond b) (embed c) (embed d)
  | .while b c => .while (embedCond b) (embed c)

@[simp] theorem embed_skip : embed .skip = .skip := rfl
@[simp] theorem embed_const (x : String) (n : Ir.Val) :
    embed (.const x n) = .assign x (.lit n) := rfl
@[simp] theorem embed_copy (x y : String) : embed (.copy x y) = .assign x (.var y) := rfl
@[simp] theorem embed_binop (op : Imp.Bop) (x y z : String) :
    embed (.binop op x y z) = .assign x (.bin op (.var y) (.var z)) := rfl
@[simp] theorem embed_aget (x a i : String) :
    embed (.aget x a i) = .assign x (.get a (.var i)) := rfl
@[simp] theorem embed_aset (a i v : String) :
    embed (.aset a i v) = .store a (.var i) (.var v) := rfl
@[simp] theorem embed_seq (c d : Ir.Com) : embed (.seq c d) = .seq (embed c) (embed d) := rfl
@[simp] theorem embed_ite (b : Ir.Cond) (c d : Ir.Com) :
    embed (.ite b c d) = .ite (embedCond b) (embed c) (embed d) := rfl
@[simp] theorem embed_while (b : Ir.Cond) (c : Ir.Com) :
    embed (.while b c) = .while (embedCond b) (embed c) := rfl

/-- The IR has no tape operations (ledger note N3), so no embedded
program writes: the output tape of a compiled IR run is whatever the
harness left there. -/
theorem noWrite_embed (c : Ir.Com) : (embed c).NoWrite := by
  induction c with
  | skip => exact Imp.Com.noWrite_skip
  | const _ _ => trivial
  | copy _ _ => trivial
  | binop _ _ _ _ => trivial
  | aget _ _ _ => trivial
  | aset _ _ _ => trivial
  | seq _ _ ih ih' => exact ⟨ih, ih'⟩
  | ite _ _ _ ih ih' => exact ⟨ih, ih'⟩
  | «while» _ _ ih => exact ih

/-! ### Agreement between a partial IR state and a total IMP+ environment -/

/-- `agree s σ`: the IMP+ environment `σ` holds what the IR state `s`
holds, on every scalar cell and every array that `s` defines. Nothing is
said about the names `s` leaves undefined — an IR op that touches one has
no derivation (`Ir/Semantics.lean`, judgment call D-f), so the simulation
never looks there. Judgment call P5/D-h: a conjunction, used through the
two accessors below. -/
def agree (s : Ir.State) (σ : Imp.Env) : Prop :=
  (∀ x v, s.vars x = some v → σ.vars x = v) ∧
    (∀ a xs, s.arrs a = some xs → σ.arrs a = xs)

/-- Reading a defined scalar cell out of the environment. -/
theorem agree.var {s : Ir.State} {σ : Imp.Env} (h : agree s σ) {x : String} {v : Ir.Val}
    (hx : s.vars x = some v) : σ.vars x = v := h.1 x v hx

/-- Reading a defined array out of the environment. -/
theorem agree.arr {s : Ir.State} {σ : Imp.Env} (h : agree s σ) {a : String} {xs : List Ir.Val}
    (ha : s.arrs a = some xs) : σ.arrs a = xs := h.2 a xs ha

theorem agree_iff {s : Ir.State} {σ : Imp.Env} :
    agree s σ ↔ (∀ x v, s.vars x = some v → σ.vars x = v) ∧
      (∀ a xs, s.arrs a = some xs → σ.arrs a = xs) := Iff.rfl

/-- Writing the same value into the same scalar cell on both sides
preserves agreement. -/
theorem agree.setVar {s : Ir.State} {σ : Imp.Env} (h : agree s σ) (x : String) (v : Ir.Val) :
    agree (s.setVar x v) (σ.setVar x v) := by
  refine ⟨fun y w hy => ?_, fun a xs ha => h.arr ha⟩
  rw [Ir.State.vars_setVar] at hy
  rw [Reasoning.vars_setVar]
  split at hy
  · rw [if_pos ‹y = x›]; exact (Option.some.inj hy).symm ▸ rfl
  · rw [if_neg ‹¬ y = x›]; exact h.var hy

/-- Storing into an array preserves agreement: the IR replaces the whole
list by a pointwise update of it, IMP+ updates the position in place, and
the two coincide because the environment holds the very list the IR state
does. -/
theorem agree.setArr {s : Ir.State} {σ : Imp.Env} (h : agree s σ) {a : String}
    {xs : List Ir.Val} (ha : s.arrs a = some xs) (k n : ℕ) :
    agree (s.setArr a (xs.set k n)) (σ.setArr a k n) := by
  refine ⟨fun y w hy => h.var hy, fun b ys hb => ?_⟩
  rw [Ir.State.arrs_setArr] at hb
  rw [Reasoning.arrs_setArr]
  split at hb
  · rw [if_pos ‹b = a›, h.arr ha]; exact (Option.some.inj hb).symm ▸ rfl
  · rw [if_neg ‹¬ b = a›]; exact h.arr hb

/-- The canonical environment of an IR state: every defined name holds
what it holds, every other name holds a default, and both tapes are
empty. Agreement with it is free, so it is what a gate — and any
consumer that has no harness in front of it yet — starts from. -/
def envOf (s : Ir.State) : Imp.Env where
  vars := fun x => (s.vars x).getD 0
  arrs := fun a => (s.arrs a).getD []
  inp := []
  out := []

@[simp] theorem agree_envOf (s : Ir.State) : agree s (envOf s) :=
  ⟨fun _ _ hx => by simp [envOf, hx], fun _ _ ha => by simp [envOf, ha]⟩

/-! ### Reading an operand through the embedding

The bounded-evaluation form is the one `Sim.lean` needs: IMP+'s
`Expr.evalB B` refuses a value that reaches `B`, so an operand can be
read on the IMP+ side exactly when its IR value is below the bound —
which for a cell is the state invariant and for a literal is a genuine
side condition of the run. -/

/-- An operand that has a value in the IR state, and whose value is
below the bound, evaluates to that value on the IMP+ side. -/
theorem agree.evalB_operand {B : ℕ} {s : Ir.State} {σ : Imp.Env} (h : agree s σ)
    {u : Ir.Operand} {v : Ir.Val} (hu : u.eval s = some v) (hv : v < B) :
    (embedOperand u).evalB B σ = some v := by
  cases u with
  | cell x =>
      rw [Ir.Operand.eval_cell] at hu
      rw [embedOperand_cell, Imp.Expr.evalB, h.var hu, Imp.fit_self hv]
  | lit n =>
      rw [Ir.Operand.eval_lit] at hu
      cases hu
      rw [embedOperand_lit, Imp.Expr.evalB, Imp.fit_self hv]

/-- A defined scalar cell, read on the IMP+ side. -/
theorem agree.evalB_var {B : ℕ} {s : Ir.State} {σ : Imp.Env} (h : agree s σ)
    {x : String} {v : Ir.Val} (hx : s.vars x = some v) (hv : v < B) :
    (Imp.Expr.var x).evalB B σ = some v := by
  rw [Imp.Expr.evalB, h.var hx, Imp.fit_self hv]

/-! ### The gate

The translation itself is data, so it is checked as data: the three
programs of `Ir/Semantics.lean`'s own gate, embedded, against the IMP+
terms written out by hand. Sizes and costs are checked in `Sim.lean`,
where the price map lives. -/

section Gate

-- `Imp.Com` carries no `DecidableEq` (it is the kit's, and nothing in
-- the kit needs one), so the translation is pinned by `rfl` rather than
-- by `#guard`; the check is the same one.
example : embed Ir.Gate.arith =
    .seq (.assign "a" (.lit 6))
      (.seq (.assign "b" (.lit 7))
        (.seq (.assign "c" (.bin .mul (.var "a") (.var "b")))
          (.assign "d" (.bin .sub (.var "c") (.var "b"))))) := rfl

example : embed Ir.Gate.roundtrip =
    .seq (.assign "x" (.get "A" (.var "i"))) (.store "A" (.var "j") (.var "x")) := rfl

example : embed Ir.Gate.countdown =
    .seq (.assign "one" (.lit 1))
      (.while (.lt (.lit 0) (.var "n"))
        (.assign "n" (.bin .sub (.var "n") (.var "one")))) := rfl

-- Every embedded condition costs the same, whatever the operand mix.
#guard (embedCond (.lt (.lit 0) (.cell "n"))).size = 3
#guard (embedCond (.eq (.cell "i") (.cell "n"))).size = 3

end Gate

end Lax13Proofs.Refine.Codegen
