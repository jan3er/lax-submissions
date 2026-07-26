import Lax11.Ram
import Lax11.RamComputes
import Mathlib.Tactic

/-!
Sanity checks for the machine semantics: a concrete program is run
end-to-end against `RunsTo`, so that the definitions are known to
describe a machine that actually halts with an output, and the step
count is known to be the number of instructions executed.

Nothing here is a proof of a submitted statement; these are the smoke
tests of the concept surface.
-/

namespace Lax11Proofs.RamSanity

open Lax11.Ram Lax11.RamComputes

/-- Four instructions and a halt: copy the input length into cell 1,
then set cell 0 to 1, leaving the one-entry output word holding the
length of the input. -/
def lengthProgram : Program :=
  [.load (.mem 0), .store 1, .load (.lit 1), .store 0, .halt]

/-- The machine executes exactly the four instructions and halts with
the length of the input as its output. -/
theorem lengthProgram_runsTo (x : List ℕ) :
    RunsTo lengthProgram x [x.length] 4 := by
  refine ⟨⟨4, 1, write (write (cells x) 1 x.length) 0 1⟩, rfl, rfl, ?_⟩
  intro i hi
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at hi
  interval_cases i <;> rfl

/-- The length of the input is computed on every input, in a number of
steps independent of the input. -/
theorem lengthProgram_computesInTime :
    ComputesInTime lengthProgram Set.univ (fun x => [x.length])
      (fun _ => 4) :=
  fun x _ => ⟨4, Nat.le_refl 4, lengthProgram_runsTo x⟩

end Lax11Proofs.RamSanity
