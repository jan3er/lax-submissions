The word RAM is the machine the modern analysis of algorithms is
stated on. It is the random access machine of Aho, Hopcroft and Ullman
— an accumulator, a memory of cells addressed by number, direct and
indirect addressing, an input and an output tape, jumps against zero —
with its numbers bounded instead of its instruction set: cells hold
`w`-bit words, and multiplication, division, shifts and the bitwise
operations each cost one time unit because on words each of them is
one instruction of a real machine. This submission fixes the archive's
canonical encoding of that model. It carries two definitions and no
proof obligations: the machine, whose semantics is parameterized by
the word length and obeys one uniform truncation rule — every value
the machine produces and every address it uses is taken modulo `2 ^ w`
— and the predicate saying that a program computes a function of words
within a time bound on a set of admissible inputs, the running time
being the machine's own step count rather than an annotation carried
alongside the program. Neither is a claim, so neither is stated as
one; the review question is faithfulness of the model, and the
formalization notes argue every choice a reviewer would want argued:
why subtraction truncates at zero rather than wrapping, why remainder
and bitwise negation are omitted as derivable, why a program can
measure `w` and therefore needs no instruction reporting it, and why
the machine reduces oversized input entries instead of rejecting them.

Statements about algorithms are then made downstream, over these two
concepts, in a fixed shape: one program is quantified before the word
length, so that a claim is about a single program uniform in `w` and
no advice can be smuggled in, and the hypotheses on the word length
are explicit inequalities against `2 ^ w` rather than logarithms.
The proof package discharges nothing — there is nothing to discharge —
and instead carries a reusable verified pipeline for the submissions
that will: a structured while-language with named scalars and arrays
whose big-step semantics counts the statements it executes, a compiler
into machine code, a simulation theorem bounding the machine's step
count by a constant multiple of that cost provided every intermediate
value fits into a word, and a reasoning layer of Hoare-style rules
with a cost potential and compositional value bounds. The word length
enters that pipeline exactly once, at its boundary, so an algorithm is
verified on clean unbounded natural-number semantics and lands as a
running-time claim about this machine.
