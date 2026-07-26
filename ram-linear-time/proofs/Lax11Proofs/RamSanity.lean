import Lax11.Ram
import Lax11.RamComputes
import Mathlib.Tactic

/-!
Sanity checks for the machine semantics: a concrete program is run
end-to-end against `RunsTo`, so that the definitions are known to
describe a machine that actually reads its input, halts, and writes an
output, and the step count is known to be the number of instructions
executed.

Nothing here is a proof of a submitted statement; these are the smoke
tests of the concept surface.
-/

namespace Lax11Proofs.RamSanity

open Lax11.Ram Lax11.RamComputes

/-- Six instructions and a halt: read the first two numbers of the
input into cells 1 and 2, add them, and write the sum. -/
def sumProgram : Program :=
  [.read 1, .read 2, .load (.mem 1), .add (.mem 2), .store 0,
   .write (.mem 0), .halt]

/-- The machine executes exactly the six instructions and halts, having
written the sum of the first two input numbers. -/
theorem sumProgram_runsTo (a b : ℕ) (x : List ℕ) :
    RunsTo sumProgram (a :: b :: x) [a + b] 6 :=
  ⟨_, rfl, rfl, rfl⟩

/-- The sum of the first two numbers is computed on every input that
has at least two, in a number of steps independent of the input. -/
theorem sumProgram_computesInTime :
    ComputesInTime sumProgram {x : List ℕ | 2 ≤ x.length}
      (fun x => [x.getD 0 0 + x.getD 1 0]) (fun _ => 6) := by
  rintro (_ | ⟨a, _ | ⟨b, x⟩⟩) hx
  · simp at hx
  · simp at hx
  · exact ⟨6, Nat.le_refl 6, sumProgram_runsTo a b x⟩

end Lax11Proofs.RamSanity
