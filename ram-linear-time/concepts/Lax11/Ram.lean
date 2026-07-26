import Mathlib.Data.List.Basic

/-!
---
title: The random access machine
type: definition
---
A random access machine is the textbook model of a sequential computer.
It has an unbounded memory of cells holding natural numbers, addressed
by number, and a distinguished accumulator register. A program is a
finite sequence of instructions, executed in order unless a jump
instruction changes the program counter. Each instruction loads a value
into the accumulator, stores the accumulator into memory, adds or
subtracts, jumps, or halts. An operand is either a literal, the
contents of a memory cell, or the contents of the cell whose address is
the contents of a memory cell.

Input and output are memory-resident: the machine starts with the input
word laid out in memory, cell 0 holding its length and cell *i+1* its
*i*-th entry, all other cells zero; it halts with the output word laid
out the same way. The running time is the number of instructions
executed, each costing one time unit.

# Formalization notes

The instruction set is that of Aho, Hopcroft and Ullman (*The Design
and Analysis of Computer Algorithms*, §1.2) without multiplication and
division: with only addition, truncated subtraction and comparisons
against zero, a machine cannot manufacture large numbers quickly, and
charging one time unit per instruction on unbounded natural numbers is
the standard honest unit-cost model. Adding multiplication would be a
different — and, under unit cost, much stronger — machine, so it is
deliberately absent rather than silently included.

Subtraction is truncated, which is what the natural-number `-` already
is. Reading and writing are total: an out-of-range program counter
halts the machine, and every memory cell holds a number, so no
error states are needed.

`step` is a function into `Option State`, returning `none` exactly when
the machine has halted, so the semantics is deterministic and total by
construction. `run p t` is `t`-fold application of `step`, and it is
`none` as soon as the machine halts, which is what makes "halts after
exactly `t` steps" in `RunsTo` a statement about the *number of
instructions executed*: the time measure is intrinsic to the machine
and is not an annotation carried alongside the program.

`RunsTo` constrains only the first `y.length + 1` memory cells on
halting — the output word and its length. The rest of memory is
scratch space and is left unconstrained; on the input side, by
contrast, `cells x` pins every cell, so cells beyond the input are
zero. There is no space measure in this submission.
-/

namespace Lax11.Ram

/-- An operand: a literal, the contents of a memory cell, or the
contents of the cell addressed by a memory cell. -/
inductive Op
  /-- The literal number `n`. -/
  | lit (n : ℕ)
  /-- The contents of cell `a`. -/
  | mem (a : ℕ)
  /-- The contents of the cell whose address is the contents of cell
  `a`. -/
  | ind (a : ℕ)

/-- An instruction: accumulator transfers, arithmetic, jumps, and
halting. -/
inductive Instr
  /-- Load the operand into the accumulator. -/
  | load (o : Op)
  /-- Store the accumulator into cell `a`. -/
  | store (a : ℕ)
  /-- Store the accumulator into the cell addressed by cell `a`. -/
  | storeInd (a : ℕ)
  /-- Add the operand to the accumulator. -/
  | add (o : Op)
  /-- Subtract the operand from the accumulator, truncated at zero. -/
  | sub (o : Op)
  /-- Continue at instruction `l`. -/
  | jump (l : ℕ)
  /-- Continue at instruction `l` if the accumulator is zero. -/
  | jzero (l : ℕ)
  /-- Continue at instruction `l` if the accumulator is positive. -/
  | jgtz (l : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite sequence of instructions, numbered from `0`. -/
abbrev Program : Type := List Instr

/-- A machine state: the program counter, the accumulator, and the
contents of every memory cell. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The accumulator. -/
  acc : ℕ
  /-- The contents of the memory cells. -/
  mem : ℕ → ℕ

/-- The value of an operand in a memory. -/
def Op.value : Op → (ℕ → ℕ) → ℕ
  | lit n, _ => n
  | mem a, m => m a
  | ind a, m => m (m a)

/-- The memory `m` with cell `a` set to `v`. -/
def write (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a then v else m b

/-- One step of the machine: the successor state, or `none` if the
machine has halted, which happens on a `halt` instruction and when the
program counter has run past the program. -/
def step (p : Program) (s : State) : Option State :=
  match p[s.pc]? with
  | none => none
  | some .halt => none
  | some (.load o) => some { s with pc := s.pc + 1, acc := o.value s.mem }
  | some (.store a) => some { s with pc := s.pc + 1, mem := write s.mem a s.acc }
  | some (.storeInd a) =>
      some { s with pc := s.pc + 1, mem := write s.mem (s.mem a) s.acc }
  | some (.add o) => some { s with pc := s.pc + 1, acc := s.acc + o.value s.mem }
  | some (.sub o) => some { s with pc := s.pc + 1, acc := s.acc - o.value s.mem }
  | some (.jump l) => some { s with pc := l }
  | some (.jzero l) => some { s with pc := if s.acc = 0 then l else s.pc + 1 }
  | some (.jgtz l) => some { s with pc := if 0 < s.acc then l else s.pc + 1 }

/-- The state after `t` steps, or `none` if the machine halts before
executing `t` instructions. -/
def run (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step p s).bind (run p t)

/-- The memory layout of a word: cell `0` holds its length, cell `i+1`
its `i`-th entry, and every further cell holds `0`. -/
def cells (x : List ℕ) : ℕ → ℕ
  | 0 => x.length
  | i + 1 => x.getD i 0

/-- The initial state on input `x`: program counter and accumulator
zero, the input word laid out in memory. -/
def initState (x : List ℕ) : State where
  pc := 0
  acc := 0
  mem := cells x

/-- Started on input `x`, the machine executes exactly `t` instructions
and then halts with the word `y` laid out in memory. -/
def RunsTo (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ s : State, run p t (initState x) = some s ∧ step p s = none ∧
    ∀ i ≤ y.length, s.mem i = cells y i

end Lax11.Ram
