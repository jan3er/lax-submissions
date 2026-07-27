import Lax11Proofs.CCSweep
import Lax13Proofs.Transfer

/-!
The theorem, cashed in at the concept surface.

Everything has been proved by now; what is left is to bundle the run of
the driver as the pipeline's `Solves` predicate, hand it to the
transfer theorem, and do the arithmetic of the constant. The layout has
four arrays, so one array access compiles to six instructions and the
machine pays thirty-one steps per unit of IMP+ cost; the run itself
costs at most eighty-four per entry of the input word. The product is
the constant of the statement, and no part of it was fought over.

The word length is dealt with in the same step and in the same place.
The value bound the driver runs under is the length of the input word,
so the layout spans `17 + 4|x|` cells, and the statement's hypothesis —
that `2604(|x|+1)` is itself a word — is more than that, by a margin
nobody has to compute.
-/

namespace Lax11Proofs.CCMain

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding Lax11.ConnectedComponents
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax13Proofs.Transfer
open Lax11Proofs.CC

/-- The machine pays thirty-one steps per unit of IMP+ cost: four
arrays make one index computation six instructions long. -/
theorem const_eq : layout.const = 31 := by
  simp [Layout.const, Layout.idxLen, layout]

/-- What the pipeline asks of the driver: on every admissible input it
computes the labelling, at a cost of `84` per entry of the input word,
with every value it produces below the length of that word. The bound
is the one quantity the encoding makes available — every entry of an
encoding, and every count of entries the algorithm keeps, is smaller
than the encoding is long. -/
theorem ccCom_solves (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ) :
    Solves layout ccCom {x | EncodesGraph x n G ∧ 2604 * (x.length + 1) ≤ 2 ^ w}
      (fun _ => ccLabels G) (fun x => x.length) (fun x => 84 * (x.length + 1)) where
  ok := ccCom_ok
  inp := fun _ hx _ hv => mem_lt_length hx.1 hv
  run := fun x hx => by
    obtain ⟨σ', K, hrun, hout, hK⟩ := ccCom_run hx.1 rfl le_rfl
    exact ⟨ccExt n (edgeCount x), σ', hrun.mono hK, hout⟩

/--
---
conclusion: Lax11.ConnectedComponents.exists_linearTime_program_ccLabels
---
Connected components can be computed in linear time on a word random
access machine: `ccProgram` labels the vertices of every graph given in
compressed sparse row form by the least vertex of their component,
within `2604 * (|x| + 1)` machine steps, at every word length at which
that many steps fit into a word.

# Proof strategy

The witness is the compiled driver `ccProgram`. Its IMP+ source
`ccCom` reads the encoding into four arrays, sweeps the vertices in
increasing order starting a breadth-first search at every unlabelled
one, and writes the label array out; `ccCom_run` is that run, end to
end, with output `ccLabels G` and cost at most `84 * (|x| + 1)`. The
cost is a single amortized argument — one potential
`c₁·(2m − scanned) + c₀·(n − tail) + c₀·(tail − head) + c₂·(n − u)`
for the whole sweep, so the searches are never counted separately —
and the linearity in `|x|` comes from the encoding's `length_eq`,
which makes `n` and `2m` both at most the length of the word.

`computesInTime_of_solves` discharges the compiler, the layout
invariant and the machine in one step, charging `layout.const = 31`
machine steps per unit of IMP+ cost. The array extents are chosen per
input, as that lemma allows: `ccExt n m` declares `off ↦ n+1`,
`tgt ↦ 2m`, `lab ↦ n`, `q ↦ n`, which is what the reads fill.

# Where the word length is paid for

The machine truncates every value modulo `2 ^ w`, so the run on the
machine is the run in the unbounded semantics only as long as nothing
the program computes reaches `2 ^ w`. The bound the driver is proved
under is the length of the input word itself: every entry of an
encoding is smaller than the encoding is long (`mem_lt_length`), and
every quantity the algorithm keeps of its own — vertex numbers,
offsets, the queue pointers, the counter of scanned slots — is bounded
by `n` or by `2m`, hence again by the length. So the whole run needs
the single hypothesis `|x| ≤ B`, and the compiled program needs in
addition that the cells the layout addresses are words, which is
`17 + 4|x| ≤ 2 ^ w`. The statement's hypothesis, that the time bound
`2604(|x| + 1)` is itself a word, gives both with room to spare; it is
stated in that form because a bound on the running time is the
condition a reader of an algorithm expects, and because it is the one
inequality the machine model actually needs to be told.

# What the program is allowed to help itself to

Two details of the program are shaped by the cost proof rather than by
the algorithm, and a reader is entitled to ask whether either of them
smuggles work out of the bound. Neither does.

*The queue is global.* It is never reset between searches: a search
leaves its head and tail pointers equal, and the next search continues
from there. So the tail only ever increases, and since a vertex is put
on the queue only in the step that labels it, the tail never passes the
number of vertices. "Queue capacity not yet used" is therefore a budget
for the whole run out of which every enqueue is paid, instead of a
budget per search that would force the searches to be counted one at a
time. Resetting the queue is what would cost something; not resetting
it is free.

*A scalar counts the adjacency slots already scanned.* The potential has
to be a function of the program's own scalars, and "how much of the
target array has been looked at" is not otherwise one of them, since the
scan pointer restarts inside each vertex's block. The counter is
incremented once per slot and read nowhere, so it costs one addition per
slot — a constant factor on work already being done — and deleting it
would leave the computed labels unchanged.

Nothing else is precomputed. The input word is read once into the four
arrays in the order the tape presents it, so the reading phase is a
plain copy and the encoding stays the dumb one the concept fixes.

# Attribution

The first theorem of the submission; the algorithm is the textbook
sweep of breadth-first searches.
-/
theorem exists_linearTime_program_ccLabels :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ),
      ComputesInTime w p {x | EncodesGraph x n G ∧ c * (x.length + 1) ≤ 2 ^ w}
        (fun _ => ccLabels G) (fun x => c * (x.length + 1)) := by
  refine ⟨ccProgram, 2604, fun n G w =>
    computesInTime_of_solves (ccCom_solves n G w) ?_ ?_⟩
  · rintro x ⟨hx, hw⟩
    have hlen := hx.length_eq
    exact fitsWords_of_max_le (by omega) (by simp [Layout.span, layout]; omega)
  · rintro x -
    rw [const_eq]
    omega

end Lax11Proofs.CCMain
