import Lax13Proofs.Imp

/-!
The IR: deep three-address syntax over named cells.

**This file is ours.** Everything else in `Refine/` is a port of an
Isabelle theory; the IR is the one layer the sources do not have, and
the design record says so twice — ledger **D2** (the concrete layer is a
*deep* three-address `Ir.Com` over named cells rather than the source's
shallow SSA-style `llM` over a heap, because the claims' meaning lives
on the endorsed word RAM and fixed-width LLVM cannot state parametric-`w`
theorems) and ledger **D3** (codegen into that deep embedding is
verified at P5, where the source trusts a printer). What is *not* ours,
and is what P4's fidelity actually consumes, is the **rule granularity**:
one primitive op is exactly one currency is exactly one future `hn_refine`
rule, mirroring the artifact's `consume (cost ''load'' 1) ≫ do the thing`
shape (`plans/word-ram/refinement-tower/p3-ir-sl-extracts.md` §3).

The op set is `plans/word-ram/refinement-tower/design.md` §6 (v0.1),
transcribed:

| op | form | lowers to (P5) |
|---|---|---|
| const | `x := n` | `assign x (lit n)` |
| copy | `x := y` | `assign x (var y)` |
| binop (×9) | `x := y ⊕ z` | `assign x (bin ⊕ (var y) (var z))` |
| aget | `x := a[i]` | `assign x (get a (var i))` |
| aset | `a[i] := v` | `store a (var i) (var v)` |
| seq / ite / while | conditions `eq u v` / `lt u v` | structural; conds map onto `Cond.eq/lt` |

with the conditions taken "over cells and literals", §6's own words.

**Deliberately absent**, each with its ledger citation:

* `alloc` / `free` — there is no heap (**D2**); arrays are pre-existing
  named objects and no op ever grows the name space, which is what lets
  the wave-B separation logic own *names* rather than addresses.
* tapes, i.e. `read` / `write` (**N3**) — the tower is tape-free; a thin
  kit-proved IMP+ prologue/epilogue moves input tape → arrays and result
  → output tape once, at the P5 boundary.
* calls and recursion (**D6**) — IMP+ `Com` has no procedures, so
  translate targets loop-form only and abstract `RECT` is refined to
  `whileT` before synthesis.
* `len` — array lengths live in assertions (the `↦ₐ` points-to carries
  its length), exactly as in the source's array points-to.

## Judgment calls

**D-a — the nine binary operators are IMP+'s `Bop`, reused, not
re-declared.** §6 asks for "exactly IMP+'s `Bop`, exactly the machine's
arithmetic set". The strongest available form of "exactly" is to *be*
the type: `Com.binop` carries a `Lax13Proofs.Imp.Bop` and the meaning of
an IR binop is `Imp.Bop.apply`, unchanged, so P5's lowering is
`assign x (bin op …)` with literally the same `op` and no translation
table can drift. The cost is one import of the kit's `Imp.lean` into the
tower — acceptable, since P5 compiles into that very file's `Com`. The
fallback, if a later wave needs the IR's operator set to move
independently, is a private copy plus a proved translation; nothing
below depends on which is chosen. The conventions inherited, each
pinned by a `#guard` at the end of this file:

* `add`/`mul` — `m + n`, `m * n` on ℕ, **no reduction modulo `2 ^ w`**:
  IMP+ is the unbounded reference semantics and the word bound enters
  once, downstream, through `Bounds`/`Transfer`. Same for every clause
  below.
* `sub` — **truncated** at zero (ℕ monus), not ring subtraction: the
  machine is unsigned and `Ram.lean` makes truncation the choice that
  keeps comparisons alive.
* `div` — `Nat` division, rounding down, with **`m / 0 = 0`**.
* `and`/`or`/`xor` — `Nat.land`, `Nat.lor`, `Nat.xor`.
* `shiftl` — `m * 2 ^ n`; `shiftr` — `m / 2 ^ n`. The shift *count* is
  used as written (no reduction), so a large count sends `shiftr` to `0`
  and lets `shiftl` grow; the machine's own truncation is what bounds
  these, downstream.

**D-b — binop operands are cells; only conditions admit literals.** §6's
table writes `x := y ⊕ z` (three addresses, all cells) and gives the
control row conditions "over cells and literals", so `Operand` — the
cell/literal sum — is used exactly where §6 uses it. `x := y + 1`
therefore costs a `const` into a cell, hoistable out of any loop; the
alternative (operands everywhere) is a strict superset that would cost
nothing downstream, and is the one-line change if a consumer asks. Kept
narrow here so the op set is the table and nothing else.

**D-c — `skip` is added, as the unit of `seq`.** §6's control row lists
seq / ite / while and no unit, but `ite` needs a second branch and the
translate phase needs an identity command. It is IMP+'s own `skip`, it
lowers to IMP+'s `skip`, and it charges its own currency (`ir.skip`, one
unit) because IMP+ charges `1` for it — a zero-cost `skip` would leave
that unit uncovered in P5's cashing inequality.

**D-d — currency names are `"ir.<op>"` strings, one per op** (design
record F1/F4): `cost "ir.add" 1` is the source's `cost ''load'' 1`
with our op names. They are defined here, not in `Semantics.lean`, so
that the semantics, the wave-B triples and P4's `hn_refine` rules all
name the same constants, and P5's price map has exactly this domain to
quantify over. `seq` has no currency of its own — it is not an
instruction, and its cost is the sum of its parts, as in IMP+; `ite`
charges one unit per test taken and `while` one unit per guard
evaluation (so `n` iterations charge `n + 1`), which is the shape of
IMP+'s own `1 + b.size` per test.
-/

namespace Lax13Proofs.Refine.Ir

/-- An IR value: a clean, unbounded natural number, exactly as IMP+
(design record §6). The word bound is *not* here — it enters once, at
the existing `Bounds`/`Transfer` boundary. -/
abbrev Val : Type := ℕ

/-- An operand: a named scalar cell or a literal. §6 admits literals in
conditions only (judgment call D-b), which is where this type is used. -/
inductive Operand
  /-- The contents of the scalar cell `x`. -/
  | cell (x : String)
  /-- The literal value `n`. -/
  | lit (n : Val)
  deriving DecidableEq, Repr

/-- Conditions: equality and strict order of two operands. The two
constructors of IMP+'s `Cond`, over operands instead of expressions, so
that they map onto `Cond.eq` / `Cond.lt` one for one at P5. -/
inductive Cond
  /-- The two operands have equal values. -/
  | eq (u v : Operand)
  /-- The first value is smaller than the second. -/
  | lt (u v : Operand)
  deriving DecidableEq, Repr

/-- Commands: the five primitive ops of design record §6, the structured
control of its last row, and `skip` (judgment call D-c). Every operand
is a name — the IR is three-address and aliasing-free by construction,
as IMP+ is. -/
inductive Com
  /-- Do nothing. -/
  | skip
  /-- `x := n`: write the literal `n` into the scalar cell `x`. -/
  | const (x : String) (n : Val)
  /-- `x := y`: copy the scalar cell `y` into the scalar cell `x`. -/
  | copy (x y : String)
  /-- `x := y ⊕ z`: apply the operator to two scalar cells. -/
  | binop (op : Imp.Bop) (x y z : String)
  /-- `x := a[i]`: read the entry of array `a` at the position held in
  the scalar cell `i` into the scalar cell `x`. -/
  | aget (x a i : String)
  /-- `a[i] := v`: write the scalar cell `v` into array `a` at the
  position held in the scalar cell `i`. -/
  | aset (a i v : String)
  /-- Run `c`, then `d`. -/
  | seq (c d : Com)
  /-- Run `c` or `d` according to the condition. -/
  | ite (b : Cond) (c d : Com)
  /-- Run the body while the condition holds. -/
  | while (b : Cond) (c : Com)
  deriving DecidableEq, Repr

/-! ### The nine binary operators, by name

IMP+ collects its operators into one `Bop` and offers the nine familiar
names as abbreviations, "so `.add e f` still writes a sum". The IR does
the same for its `binop` node. -/

/-- `x := y + z`. -/
abbrev Com.add (x y z : String) : Com := .binop .add x y z
/-- `x := y - z`, truncated at zero. -/
abbrev Com.sub (x y z : String) : Com := .binop .sub x y z
/-- `x := y * z`. -/
abbrev Com.mul (x y z : String) : Com := .binop .mul x y z
/-- `x := y / z`, rounding down, by zero yielding zero. -/
abbrev Com.div (x y z : String) : Com := .binop .div x y z
/-- `x := y &&& z`. -/
abbrev Com.and (x y z : String) : Com := .binop .and x y z
/-- `x := y ||| z`. -/
abbrev Com.or (x y z : String) : Com := .binop .or x y z
/-- `x := y ^^^ z`. -/
abbrev Com.xor (x y z : String) : Com := .binop .xor x y z
/-- `x := y <<< z`. -/
abbrev Com.shiftl (x y z : String) : Com := .binop .shiftl x y z
/-- `x := y >>> z`. -/
abbrev Com.shiftr (x y z : String) : Com := .binop .shiftr x y z

@[simp] theorem Com.add_def (x y z : String) : Com.add x y z = .binop .add x y z := rfl
@[simp] theorem Com.sub_def (x y z : String) : Com.sub x y z = .binop .sub x y z := rfl
@[simp] theorem Com.mul_def (x y z : String) : Com.mul x y z = .binop .mul x y z := rfl
@[simp] theorem Com.div_def (x y z : String) : Com.div x y z = .binop .div x y z := rfl
@[simp] theorem Com.and_def (x y z : String) : Com.and x y z = .binop .and x y z := rfl
@[simp] theorem Com.or_def (x y z : String) : Com.or x y z = .binop .or x y z := rfl
@[simp] theorem Com.xor_def (x y z : String) : Com.xor x y z = .binop .xor x y z := rfl
@[simp] theorem Com.shiftl_def (x y z : String) : Com.shiftl x y z = .binop .shiftl x y z := rfl
@[simp] theorem Com.shiftr_def (x y z : String) : Com.shiftr x y z = .binop .shiftr x y z := rfl

/-! ### Currencies

One name per op (judgment call D-d, design record F1/F4). These are the
strings the semantics charges, the wave-B triples pay in, P4's
`hn_refine` rules quote, and P5's price map is indexed by; they are
declared once, here, so that no two layers can name the same op
differently. -/

namespace Currency

/-- The currency of `skip`. -/
def skip : String := "ir.skip"
/-- The currency of `const`. -/
def const : String := "ir.const"
/-- The currency of `copy`. -/
def copy : String := "ir.copy"
/-- The currency of `aget`. -/
def aget : String := "ir.aget"
/-- The currency of `aset`. -/
def aset : String := "ir.aset"
/-- The currency of a conditional's test. -/
def ite : String := "ir.ite"
/-- The currency of a loop's guard evaluation: `n` iterations charge
`n + 1`, one for each test, the last of which fails. `while` is a Lean
token, so the identifier is written `Currency.«while»`. -/
def «while» : String := "ir.while"
/-- The currency of `add`. -/
def add : String := "ir.add"
/-- The currency of `sub`. -/
def sub : String := "ir.sub"
/-- The currency of `mul`. -/
def mul : String := "ir.mul"
/-- The currency of `div`. -/
def div : String := "ir.div"
/-- The currency of `and`. -/
def and : String := "ir.and"
/-- The currency of `or`. -/
def or : String := "ir.or"
/-- The currency of `xor`. -/
def xor : String := "ir.xor"
/-- The currency of `shiftl`. -/
def shiftl : String := "ir.shiftl"
/-- The currency of `shiftr`. -/
def shiftr : String := "ir.shiftr"

end Currency

/-- The currency of a binary operator: one per operator, so that a
per-phase cost account distinguishes a multiplication from a shift all
the way down to P5's price map. -/
def binopCurrency : Imp.Bop → String
  | .add => Currency.add
  | .sub => Currency.sub
  | .mul => Currency.mul
  | .div => Currency.div
  | .and => Currency.and
  | .or => Currency.or
  | .xor => Currency.xor
  | .shiftl => Currency.shiftl
  | .shiftr => Currency.shiftr

@[simp] theorem binopCurrency_add : binopCurrency .add = Currency.add := rfl
@[simp] theorem binopCurrency_sub : binopCurrency .sub = Currency.sub := rfl
@[simp] theorem binopCurrency_mul : binopCurrency .mul = Currency.mul := rfl
@[simp] theorem binopCurrency_div : binopCurrency .div = Currency.div := rfl
@[simp] theorem binopCurrency_and : binopCurrency .and = Currency.and := rfl
@[simp] theorem binopCurrency_or : binopCurrency .or = Currency.or := rfl
@[simp] theorem binopCurrency_xor : binopCurrency .xor = Currency.xor := rfl
@[simp] theorem binopCurrency_shiftl : binopCurrency .shiftl = Currency.shiftl := rfl
@[simp] theorem binopCurrency_shiftr : binopCurrency .shiftr = Currency.shiftr := rfl

/-- Every operator has its own currency: the currency map is injective,
so a cost vector records *which* arithmetic a run did, not merely how
much. -/
theorem binopCurrency_injective : Function.Injective binopCurrency := by
  intro a b h; revert h; cases a <;> cases b <;> decide

/-- The sixteen currencies of the IR, in the order of the op set. -/
def Currency.all : List String :=
  [Currency.skip, Currency.const, Currency.copy, Currency.aget, Currency.aset,
    Currency.ite, Currency.«while», Currency.add, Currency.sub, Currency.mul,
    Currency.div, Currency.and, Currency.or, Currency.xor, Currency.shiftl,
    Currency.shiftr]

/-- The currencies are pairwise distinct: no two constructs of the IR
are ever paid for out of the same account. This is what makes a cost
vector a *per-op* account (design record F4) and what P5's price map
quantifies over. -/
theorem Currency.all_nodup : Currency.all.Nodup := by decide

/-- Every binop currency is one of the sixteen. -/
theorem binopCurrency_mem_all (op : Imp.Bop) : binopCurrency op ∈ Currency.all := by
  cases op <;> decide

/-! ### The audit trail: the conventions this IR inherits

Judgment call D-a says the IR's arithmetic *is* IMP+'s. These are the
conventions that claim buys, each checked by computation rather than
read off prose — truncated subtraction, division by zero, `Nat` bitwise
operations, and shifts by a count used as written. -/

-- Addition and multiplication are ℕ's, with no reduction modulo `2 ^ w`.
#guard Imp.Bop.add.apply 6 7 = 13
#guard Imp.Bop.mul.apply 6 7 = 42

-- Subtraction is truncated at zero, not ring subtraction.
#guard Imp.Bop.sub.apply 7 3 = 4
#guard Imp.Bop.sub.apply 3 7 = 0

-- Division rounds down, and division by zero yields zero.
#guard Imp.Bop.div.apply 7 2 = 3
#guard Imp.Bop.div.apply 7 0 = 0

-- The bitwise operations are `Nat.land` / `Nat.lor` / `Nat.xor`.
#guard Imp.Bop.and.apply 6 3 = 2
#guard Imp.Bop.or.apply 6 3 = 7
#guard Imp.Bop.xor.apply 6 3 = 5

-- The shifts are multiplication and division by a power of two, with
-- the count used as written: `shiftr` by a large count empties the
-- cell, `shiftl` by one grows without truncation.
#guard Imp.Bop.shiftl.apply 1 10 = 1024
#guard Imp.Bop.shiftr.apply 5 1 = 2
#guard Imp.Bop.shiftr.apply 5 64 = 0

-- The currency names, pinned.
#guard binopCurrency .add = "ir.add"
#guard binopCurrency .shiftr = "ir.shiftr"
#guard Currency.aset = "ir.aset"

end Lax13Proofs.Refine.Ir
