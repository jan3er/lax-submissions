import Lax15.VertexCover
import Lax11Proofs.VCSpec
import Lax13Proofs.Reasoning

/-!
A placeholder module: it exists so that the package's root has
something to import while the development is being written, and it does
nothing but check that everything the development is built on is in
scope — the concept surface of this submission, the reasoning kit of
the word RAM, and the vertex cover model of the earlier submission,
whose search predicate `Ok` and its bridge to the concept's answer are
reused here rather than restated.

Every declaration in this file is `private` and every one of them will
go once the real modules land.
-/

namespace Lax15Proofs.Basic

open Lax13Proofs.Reasoning Lax11Proofs.VC

/-- The reasoning kit is in scope. -/
private theorem run_skip {B : ℕ} {σ : Lax13Proofs.Imp.Env} :
    Run B .skip σ σ 1 :=
  Run.skip

/-- The imported search predicate is in scope, and so is the Fibonacci
sequence the bound is stated through: a marking that is already a cover
meets every budget, and the search tree of a budget is never empty. -/
private theorem ok_of_isVertexCover {n : ℕ} {G : SimpleGraph (Fin n)}
    {M : Finset (Fin n)} (hM : G.IsVertexCover ↑M) (b : ℕ) :
    Ok G M b ∧ 0 < Nat.fib (b + 2) :=
  ⟨Ok.of_isVertexCover hM, Nat.fib_pos.2 (by omega)⟩

end Lax15Proofs.Basic
