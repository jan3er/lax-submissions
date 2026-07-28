import Lax15.VertexCoverFpt
import Lax11Proofs.VCMain

/-!
The base rung, cashed in at the concept surface.

There is nothing to prove that has not been proved: the driver, its
invariant, its potential and its assembly live in `Lax11Proofs.VCMain`
of *Algorithmic Experiments on a Random Access Machine*, required as
proved theorems, and the conclusion below is that theorem, restated on
this surface and checked to be the same proposition.
-/

namespace Lax15Proofs.VCFptMain

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding Lax11.VertexCover

/--
---
conclusion: Lax15.VertexCoverFpt.exists_fptTime_program_vertexCover
---
Vertex cover is fixed-parameter tractable with the parameter dependence
written into the bound: `vcProgram` decides, on every graph in
compressed sparse row form followed by the parameter `k`, whether the
graph has a vertex cover of at most `k` vertices, within
`33300 * 2 ^ k * (|x| + 1)` machine steps, at every word length at
which `33300 * (|x| + k + 1)` fits into a word.

# Proof strategy

The witness is the compiled driver `vcProgram` of *Algorithmic
Experiments on a Random Access Machine*, and the proof is that
submission's, required as proved theorems rather than reproved:
`Lax11Proofs.VCMain.exists_fptTime_program_vertexCover` is this very
proposition, the identity check below says so, and the kernel checks a
required theorem like any other, so the requirement adds nothing to the
axiom set.

The argument, in one paragraph: the driver runs the textbook bounded
search tree as a single loop on a mode scalar, branching on an edge
with neither endpoint marked — one of the two endpoints lies in every
cover, so trying both to depth `k` is exhaustive. Correctness is one
invariant splitting the answer between the marking committed to and the
alternatives the frames still owe; the cost is one amortized potential,
`4 * 2 ^ b − 3` for the subtree still to be searched at remaining
budget `b` plus slack per frame, which every transition strictly
decreases, so the whole tree is paid for by a single application of the
loop rule and the factor `2 ^ k` enters exactly once, as the potential
of the initial configuration. The constant is `33300 = 37 · 900`:
thirty-seven machine steps per statement of the compiled program, times
nine hundred statements per `2 ^ k` per input letter.

The full account — where the constant comes from, where the word
length is paid for, and what the program is allowed to help itself
to — is the annotation of `Lax11Proofs.VCMain.
exists_fptTime_program_vertexCover` in that submission's proof package,
and is not restated here. The two rungs above this one
(`Main.lean`, `Main3.lean`) reuse the same apparatus and sharpen the
branching rule; their drivers are new, this one is the original.

# Attribution

The opening result of parameterized complexity, by the textbook bounded
search tree — Downey and Fellows. The base 2 is the point of the
statement: no reduction rules are applied, and nothing here competes
with the refined analyses that beat it — the two statements above it in
this submission among them.
-/
theorem exists_fptTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ),
      ComputesInTime w p
        {x | EncodesParamInstance x n G k ∧ c * (x.length + k + 1) ≤ 2 ^ w}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * 2 ^ k * (x.length + 1)) :=
  Lax11Proofs.VCMain.exists_fptTime_program_vertexCover

/-- The theorem discharges the concept's axiom and not a variant of it:
the equation typechecks only if the two statements are the same
proposition. -/
example : @exists_fptTime_program_vertexCover =
    @Lax15.VertexCoverFpt.exists_fptTime_program_vertexCover := rfl

end Lax15Proofs.VCFptMain
