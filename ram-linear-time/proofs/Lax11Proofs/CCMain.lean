import Lax11Proofs.CCSweep

/-!
The theorem, cashed in at the concept surface.

Everything has been proved by now; what is left is to hand the `Run` of
the driver to the simulation theorem and do the arithmetic of the
constant. The layout has four arrays, so one array access compiles to
six instructions and the machine pays thirty-one steps per unit of IMP+
cost; the run itself costs at most eighty-four per entry of the input
word. The product is the constant of the statement, and no part of it
was fought over.
-/

namespace Lax11Proofs.CCMain

open Lax11.Ram Lax11.RamComputes Lax11.GraphEncoding Lax11.ConnectedComponents
open Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning Lax11Proofs.CC

/-- The machine pays thirty-one steps per unit of IMP+ cost: four
arrays make one index computation six instructions long. -/
theorem const_eq : layout.const = 31 := by
  simp [Layout.const, Layout.idxLen, layout]

/--
---
conclusion: Lax11.ConnectedComponents.exists_linearTime_program_ccLabels
---
Connected components can be computed in linear time on a random access
machine: `ccProgram` labels the vertices of every graph given in
compressed sparse row form by the least vertex of their component,
within `2604 * (|x| + 1)` machine steps.

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

`computesInTime_of_run` discharges the compiler, the layout invariant
and the machine in one step, charging `layout.const = 31` machine steps
per unit of IMP+ cost. The array extents are chosen per input, as that
lemma allows: `ccExt n m` declares `off ↦ n+1`, `tgt ↦ 2m`, `lab ↦ n`,
`q ↦ n`, which is what the reads fill.

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

The theorem of the submission; the algorithm is the textbook sweep of
breadth-first searches.
-/
theorem exists_linearTime_program_ccLabels :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ComputesInTime p {x | EncodesGraph x n G} (fun _ => ccLabels G)
        (fun x => c * (x.length + 1)) := by
  refine ⟨ccProgram, 2604, fun n G => computesInTime_of_run ccCom_ok ?_⟩
  intro x hx
  obtain ⟨σ', K, hrun, hout, hK⟩ := ccCom_run hx rfl
  exact ⟨ccExt n (edgeCount x), σ', K, hrun, hout, by rw [const_eq]; omega⟩

end Lax11Proofs.CCMain
