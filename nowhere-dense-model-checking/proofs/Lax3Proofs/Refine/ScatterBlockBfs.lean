import Lax3Proofs.Refine.BfsBlock

/-!
# The block-driven search, re-exported for the scatter engine — RETIRED
to a delegation (rebase G2/E6)

E4b's finding was that `Refine/BfsBlock.lean`'s `bfsBlock_specW`
computed two facts a scatter consumer needs — `∀ i < tail, Q i < n`
(the queue entries index arrays) and `tail ≤ nb` (the segment walk is
charged to the ball, not the carrier) — and dropped both at its final
`refine`, forcing this file to walk the whole proof a second time to
route them into the postcondition.

E6 folded the two clauses into `BfsBlock.bfsBlock_specW` itself (the
fix E4b's report names as preferred), so the re-walk is gone: the
theorem below is the same statement, character for character, proved by
delegation. It is kept (rather than deleted) because the landed
`Refine/ScatterBlock*.lean` engine files consume it by this name.
-/

namespace Lax3Proofs.Refine.ScatterBlock

open Lax3.ColoredGraphs Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.Refine

/-- **Block-driven breadth-first search, charged to its ball, with the
queue segment ranged and ball-bounded.** Since rebase G2/E6 this is
`BfsBlock.bfsBlock_specW` verbatim — precondition, program, cost AND
postcondition — and the proof is the delegation that certifies it. -/
theorem bfsBlockA_specW {B : ℕ} {n ns nt d s : ℕ} {G : SimpleGraph (Fin n)} {M O T : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
        σ.arrs "alv" = arrOf n M ∧ σ.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g))
      (BfsBlock.bfsBlockCom d)
      (fun _ σ' => σ'.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        ∃ Q QD, σ'.arrs "q" = arrOf n Q ∧ σ'.arrs "qd" = arrOf n QD ∧
          σ'.vars "tail" ≤ n ∧ σ'.vars "tail" ≤ nb ∧
          (∀ i, i < σ'.vars "tail" → Q i < n) ∧
          (∀ v, v < n →
            ((∃ i, i < σ'.vars "tail" ∧ Q i = v) ↔ (M v ≠ 0 ∧ WD G M d s v))) ∧
          (∀ i, i < σ'.vars "tail" → ∀ j, j < σ'.vars "tail" → Q i = Q j → i = j) ∧
          (∀ i, i < σ'.vars "tail" → ∀ k, k ≤ d → (QD i ≤ k ↔ WD G M k s (Q i))))
      (BfsBlock.bfsBlockK bw nb) :=
  BfsBlock.bfsBlock_specW hcsr hs hnB hnsB hnt hdB hMB hA hbw hnb

#print axioms bfsBlockA_specW

end Lax3Proofs.Refine.ScatterBlock
