import Mathlib.Data.List.Basic

/-!
---
title: The random access machine
type: definition
---
A random access machine is the textbook model of a sequential computer.
It has an unbounded memory of cells holding natural numbers, addressed
by number, and a distinguished accumulator register. Input arrives on a
read-only input tape and output is written on a write-only output tape.
A program is a finite sequence of instructions, executed in order unless
a jump instruction changes the program counter. Each instruction reads
the next input number into a cell, writes a number to the output, loads
a value into the accumulator, stores the accumulator into memory, adds
or subtracts, jumps, or halts. An operand is either a literal, the
contents of a memory cell, or the contents of the cell whose address is
the contents of a memory cell.

The machine starts with all memory cells zero, the whole input word on
the input tape and the output tape empty; it halts having written the
output word. The running time is the number of instructions executed,
each costing one time unit.

# Formalization notes

The instruction set is that of Aho, Hopcroft and Ullman (*The Design
and Analysis of Computer Algorithms*, §1.2) without multiplication and
division: with only addition, truncated subtraction and comparisons
against zero, a machine cannot manufacture large numbers quickly, and
charging one time unit per instruction on unbounded natural numbers is
the standard honest unit-cost model. Adding multiplication would be a
different — and, under unit cost, much stronger — machine, so it is
deliberately absent rather than silently included.

The input and output tapes are the ones of the cited source. They are
what makes the machine's memory start out empty, and hence what lets a
program address it by fixed cell numbers; an input laid out in memory
instead would begin at a cell number depending on the input length. A
program that wants random access to its input copies it into memory
first, at a cost of one instruction per number, so this is a constraint
only on algorithms that would read less than their whole input.

Subtraction is truncated, which is what the natural-number `-` already
is. Reading and writing are total: an out-of-range program counter halts
the machine, as does a read from an exhausted input tape, and every
memory cell holds a number, so no error states are needed.

`Instr.effect` is the whole of the instruction semantics and `step` adds
only the fetch, returning `none` exactly when the machine has halted, so
the semantics is deterministic and total by construction. `run p t` is
`t`-fold application of `step`, and it is `none` as soon as the machine
halts, which is what makes "halts after exactly `t` steps" in `RunsTo` a
statement about the *number of instructions executed*: the time measure
is intrinsic to the machine and is not an annotation carried alongside
the program.

`RunsTo` constrains the output tape and nothing else: memory is scratch
space and is left unconstrained on halting. There is no space measure in
this submission.
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

/-- An instruction: tape transfers, accumulator transfers, arithmetic,
jumps, and halting. -/
inductive Instr
  /-- Read the next number of the input tape into cell `a`. -/
  | read (a : ℕ)
  /-- Append the value of the operand to the output tape. -/
  | write (o : Op)
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

/-- A machine state: the program counter, the accumulator, the contents
of every memory cell, the part of the input tape not yet read, and the
output tape written so far. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The accumulator. -/
  acc : ℕ
  /-- The contents of the memory cells. -/
  mem : ℕ → ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The value of an operand in a memory. -/
def Op.value : Op → (ℕ → ℕ) → ℕ
  | lit n, _ => n
  | mem a, m => m a
  | ind a, m => m (m a)

/-- The memory `m` with cell `a` set to `v`. -/
def setCell (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a then v else m b

/-- The effect of one instruction on the state, or `none` if it halts
the machine, which a `halt` instruction and a read from an exhausted
input tape do. -/
def Instr.effect : Instr → State → Option State
  | read a, s =>
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell s.mem a v, inp := s.inp.tail }
  | write o, s => some { s with pc := s.pc + 1, out := s.out ++ [o.value s.mem] }
  | load o, s => some { s with pc := s.pc + 1, acc := o.value s.mem }
  | store a, s => some { s with pc := s.pc + 1, mem := setCell s.mem a s.acc }
  | storeInd a, s =>
      some { s with pc := s.pc + 1, mem := setCell s.mem (s.mem a) s.acc }
  | add o, s => some { s with pc := s.pc + 1, acc := s.acc + o.value s.mem }
  | sub o, s => some { s with pc := s.pc + 1, acc := s.acc - o.value s.mem }
  | jump l, s => some { s with pc := l }
  | jzero l, s => some { s with pc := if s.acc = 0 then l else s.pc + 1 }
  | jgtz l, s => some { s with pc := if 0 < s.acc then l else s.pc + 1 }
  | halt, _ => none

/-- One step of the machine: fetch the instruction the program counter
points at and execute it. The result is `none` if the machine has
halted, which also happens when the program counter has run past the
program. -/
def step (p : Program) (s : State) : Option State :=
  p[s.pc]?.bind fun i => i.effect s

/-- The state after `t` steps, or `none` if the machine halts before
executing `t` instructions. -/
def run (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step p s).bind (run p t)

/-- The initial state on input `x`: program counter and accumulator
zero, all memory cells zero, the input word on the input tape, the
output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  acc := 0
  mem := fun _ => 0
  inp := x
  out := []

/-- Started on input `x`, the machine executes exactly `t` instructions
and then halts, having written the word `y` to its output tape. -/
def RunsTo (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ s : State, run p t (initState x) = some s ∧ step p s = none ∧ s.out = y

end Lax11.Ram
