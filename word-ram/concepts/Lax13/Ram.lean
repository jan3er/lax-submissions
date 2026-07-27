import Mathlib.Data.List.Basic

/-!
---
title: The word RAM
type: definition
---
A word RAM is a random access machine whose cells hold *words*: natural
numbers below `2 ^ w`, for a word length `w` that is a parameter of the
model. It has a memory of `2 ^ w` cells, addressed by number, and a
distinguished accumulator register. Input arrives on a read-only input
tape and output is written on a write-only output tape. A program is a
finite sequence of instructions, executed in order unless a jump
instruction changes the program counter. Each instruction reads the next
input number into a cell, writes a number to the output, loads a value
into the accumulator, stores the accumulator into memory — directly or
at an address held in a memory cell — combines the accumulator with an
operand by addition, subtraction, multiplication, division, bitwise
conjunction, disjunction or exclusive or, or a shift, jumps
unconditionally or on the accumulator being zero or positive, or halts.
An operand is either a literal, the contents of a memory cell, or the
contents of the cell whose address is the contents of a memory cell.

All arithmetic is arithmetic on words: every value the machine produces
is taken modulo `2 ^ w`, and every address is taken modulo `2 ^ w`.
Subtraction is the exception a machine on unsigned words needs, and is
truncated at zero rather than wrapping. Division is integer division,
with `x / 0 = 0`.

The machine starts with all memory cells zero, the whole input word on
the input tape and the output tape empty; it halts having written the
output word. The running time is the number of instructions executed,
each costing one time unit.

# Formalization notes

This is the machine the modern analysis of algorithms is stated on. The
unbounded-number RAM of Aho, Hopcroft and Ullman (*The Design and
Analysis of Computer Algorithms*, §1.2) and of Cook and Reckhow is
honest under unit cost only if its arithmetic is weak, because unit-cost
operations on numbers of unbounded length are a form of parallelism. The
literature's answer, standard since Fredman and Willard's fusion trees
and surveyed by Hagerup (*Sorting and searching on the word RAM*), is to
bound the numbers instead of the instruction set: cells hold `w`-bit
words, `w` is large enough to address the input — `w ≥ log n`, here
always written as an explicit inequality against `2 ^ w` at the point of
use — and a word operation costs one time unit because it is one machine
instruction on a real machine. Multiplication, division, bitwise
operations and shifts are then unproblematic, and this is what makes the
model the one in which the results of the algorithms literature are
actually stated. The instruction skeleton is still that of Aho, Hopcroft
and Ullman: an accumulator, direct and indirect addressing, tapes, and
jumps against zero.

Truncation is definitional and follows a single rule, applied
everywhere and with no exceptions: **every value the machine produces is
reduced modulo `2 ^ w` at the point of production, and every address is
reduced modulo `2 ^ w` at the point of use.** Values are produced into
the accumulator (`load` and every arithmetic instruction), into memory
(`store`, `storeInd`, and the number `read` takes off the input tape)
and onto the output tape (`write`); addresses are used by `Op.mem` and
`Op.ind` when reading and by `setCell` when writing. A literal operand
is not reduced where it is written down — that would be a third rule —
but the value it produces is, so an oversized literal is never
observable except through a word, and for `add`, `mul` and the bitwise
instructions this comes to exactly the same thing as reducing the
literal. It differs only for the instructions that are not arithmetic
modulo `2 ^ w` — truncated subtraction, division and the shifts, whose
operands are used as written: an oversized subtrahend empties the
accumulator, as does a shift by `w` or more, and division by a number
too large to be a word yields zero. Only a program's own literals can be
oversized in the first place, since every value it can read out of
memory is a word. Two consequences make the rule worth its uniformity:
the accumulator and every cell the machine can reach hold words, by
construction rather than by an invariant to be proved; and the memory,
although indexed by all of `ℕ`, is touched only at the residues below
`2 ^ w`, so it is exactly the canonical `2 ^ w`-cell store. On words,
truncated subtraction, division, the bitwise operations and the right
shift cannot leave the words, so for those instructions the reduction
does nothing; it is written anyway, because a rule without exceptions is
easier to review than a case distinction.

Subtraction is natural-number monus, not subtraction in the ring of
residues. The accumulator-and-jump architecture tests `a > b` by
subtracting and jumping on a positive accumulator, which is exactly why
Aho, Hopcroft and Ullman give their machine signed integers; on an
unsigned carrier, truncation at zero is the same load-bearing choice,
and without it no comparison would survive. Nothing is lost by it:
ring subtraction is `add` of the two's complement, that is `xor` with
the all-ones word, `add 1`, `add`, at constant cost once the all-ones
word is in a cell, and the two machines therefore simulate each other
with constant overhead, so no statement about the model can depend on
the choice.

Two familiar operations are omitted because a program derives them at
constant cost. The remainder of `a` by `b` is `a - b * (a / b)`: save
`a`, divide by `b`, multiply by `b`, subtract from the saved `a` — exact
because `b * (a / b) ≤ a` never wraps. Bitwise negation is `xor` with
the all-ones word `2 ^ w - 1`, which a program obtains once, in `O(w)`
steps, by doubling a register from `1` until it wraps to zero and
summing the values it passed through. Counting those iterations gives
`w` itself, which is why the model needs no instruction reporting the
word length: the machine can measure it. Programs are therefore uniform
in `w` in the strong sense — one program, all word lengths — and the
statements built on this model quantify accordingly.

`read` reduces the number it takes off the input tape modulo `2 ^ w`,
like every other value. The alternative — halting, or refusing to run —
would make the machine partial in the input rather than in its own
control flow. The machine stays total and honesty about inputs whose
entries do not fit into a word lives on the statement side, in the set
of admissible inputs a claim quantifies over, where the rest of the
input's well-formedness already lives.

Time is the machine's own step count, one unit per instruction, and it
is now honest for multiplication precisely because the factors are
words. There is no space measure: it would be a further definition over
`run`, and space is in any case bounded by the `2 ^ w` cells the machine
can address. Randomness is deliberately absent as well; a randomized
program is a deterministic program that consumes a word list of random
numbers, which is definable downstream over this same machine, with no
change to the model.

The input and output tapes are the ones of the cited source. They are
what makes the machine's memory start out empty, and hence what lets a
program address it by fixed cell numbers; an input laid out in memory
instead would begin at a cell number depending on the input length. A
program that wants random access to its input copies it into memory
first, at a cost of one instruction per number, so this is a constraint
only on algorithms that would read less than their whole input.

Reading and writing are total: an out-of-range program counter halts the
machine, as does a read from an exhausted input tape, and every memory
cell holds a number, so no error states are needed. `Instr.effect` is
the whole of the instruction semantics and `step` adds only the fetch,
returning `none` exactly when the machine has halted, so the semantics
is deterministic and total by construction. `run w p t` is `t`-fold
application of `step`, and it is `none` as soon as the machine halts,
which is what makes "halts after exactly `t` steps" in `RunsTo` a
statement about the *number of instructions executed*: the time measure
is intrinsic to the machine and is not an annotation carried alongside
the program. `RunsTo` constrains the output tape and nothing else:
memory is scratch space and is left unconstrained on halting.
-/

namespace Lax13.Ram

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
bitwise operations, jumps, and halting. -/
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
  /-- Add the operand to the accumulator, wrapping around modulo
  `2 ^ w`. -/
  | add (o : Op)
  /-- Subtract the operand from the accumulator, truncated at zero
  rather than wrapping around. -/
  | sub (o : Op)
  /-- Multiply the accumulator by the operand, wrapping around modulo
  `2 ^ w`. -/
  | mul (o : Op)
  /-- Divide the accumulator by the operand, rounding towards zero;
  division by zero yields zero. -/
  | div (o : Op)
  /-- Replace the accumulator by its bitwise conjunction with the
  operand. -/
  | and (o : Op)
  /-- Replace the accumulator by its bitwise disjunction with the
  operand. -/
  | or (o : Op)
  /-- Replace the accumulator by its bitwise exclusive or with the
  operand. -/
  | xor (o : Op)
  /-- Shift the accumulator left by the operand many bits, wrapping
  around modulo `2 ^ w`; a shift by `w` or more yields zero. -/
  | shiftl (o : Op)
  /-- Shift the accumulator right by the operand many bits, discarding
  the bits shifted out. -/
  | shiftr (o : Op)
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
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The value of an operand in a memory, at word length `w`: every
address is taken modulo `2 ^ w` before the cell it names is read. -/
def Op.value (w : ℕ) : Op → (ℕ → ℕ) → ℕ
  | lit n, _ => n
  | mem a, m => m (a % 2 ^ w)
  | ind a, m => m (m (a % 2 ^ w) % 2 ^ w)

/-- The memory `m` with cell `a` set to `v`, at word length `w`: the
address and the value written are both taken modulo `2 ^ w`. -/
def setCell (w : ℕ) (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a % 2 ^ w then v % 2 ^ w else m b

/-- The effect of one instruction on the state at word length `w`, or
`none` if it halts the machine, which a `halt` instruction and a read
from an exhausted input tape do. Every value produced is reduced modulo
`2 ^ w` and every address used is reduced modulo `2 ^ w`. -/
def Instr.effect (w : ℕ) : Instr → State → Option State
  | read a, s =>
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := s.inp.tail }
  | write o, s =>
      some { s with pc := s.pc + 1, out := s.out ++ [o.value w s.mem % 2 ^ w] }
  | load o, s => some { s with pc := s.pc + 1, acc := o.value w s.mem % 2 ^ w }
  | store a, s => some { s with pc := s.pc + 1, mem := setCell w s.mem a s.acc }
  | storeInd a, s =>
      some { s with pc := s.pc + 1, mem := setCell w s.mem (s.mem (a % 2 ^ w)) s.acc }
  | add o, s => some { s with pc := s.pc + 1, acc := (s.acc + o.value w s.mem) % 2 ^ w }
  | sub o, s => some { s with pc := s.pc + 1, acc := (s.acc - o.value w s.mem) % 2 ^ w }
  | mul o, s => some { s with pc := s.pc + 1, acc := (s.acc * o.value w s.mem) % 2 ^ w }
  | div o, s => some { s with pc := s.pc + 1, acc := (s.acc / o.value w s.mem) % 2 ^ w }
  | and o, s => some { s with pc := s.pc + 1, acc := Nat.land s.acc (o.value w s.mem) % 2 ^ w }
  | or o, s => some { s with pc := s.pc + 1, acc := Nat.lor s.acc (o.value w s.mem) % 2 ^ w }
  | xor o, s => some { s with pc := s.pc + 1, acc := Nat.xor s.acc (o.value w s.mem) % 2 ^ w }
  | shiftl o, s =>
      some { s with pc := s.pc + 1, acc := s.acc * 2 ^ o.value w s.mem % 2 ^ w }
  | shiftr o, s =>
      some { s with pc := s.pc + 1, acc := s.acc / 2 ^ o.value w s.mem % 2 ^ w }
  | jump l, s => some { s with pc := l }
  | jzero l, s => some { s with pc := if s.acc = 0 then l else s.pc + 1 }
  | jgtz l, s => some { s with pc := if 0 < s.acc then l else s.pc + 1 }
  | halt, _ => none

/-- One step of the machine at word length `w`: fetch the instruction
the program counter points at and execute it. The result is `none` if
the machine has halted, which also happens when the program counter has
run past the program. -/
def step (w : ℕ) (p : Program) (s : State) : Option State :=
  p[s.pc]?.bind fun i => i.effect w s

/-- The state after `t` steps at word length `w`, or `none` if the
machine halts before executing `t` instructions. -/
def run (w : ℕ) (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

/-- The initial state on input `x`: program counter and accumulator
zero, all memory cells zero, the input word on the input tape, the
output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  acc := 0
  mem := fun _ => 0
  inp := x
  out := []

/-- Started on input `x` at word length `w`, the machine executes
exactly `t` instructions and then halts, having written the word `y` to
its output tape. -/
def RunsTo (w : ℕ) (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ s : State, run w p t (initState x) = some s ∧ step w p s = none ∧ s.out = y

end Lax13.Ram
