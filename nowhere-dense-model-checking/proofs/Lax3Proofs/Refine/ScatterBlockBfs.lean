import Lax3Proofs.Refine.BfsBlock

/-!
# The block-driven search, re-exported for the scatter engine

`Refine/BfsBlock.lean`'s `bfsBlock_specW` searches a ball and charges the
ball, and its postcondition hands the answer back as the queue segment
`q[0 .. tail)`. Two facts its own proof establishes do not survive into
that postcondition, and a scatter consumer needs both:

* **`∀ i < tail, Q i < n`.** The consumer indexes arrays *by queue
  entries*. In IMP+ a store outside an array is stuck, so without a range
  fact for `Q i` no scatter over the segment can even be shown to run.
  The search's frame carries it — `qmem` says every queue entry is a live
  vertex of the carrier — and the export drops it.

* **`tail ≤ nb`.** The consumer walks the segment and must charge the
  walk. The exported `tail ≤ n` charges it to the *carrier*, which is
  precisely the `Ω(n)`-per-centre term the block engine exists to
  delete; `tail ≤ nb` charges it to the ball. The search's frame carries
  this too, through `tail_le_card` and the caller's `A.card ≤ nb`.

Both are recovered here without touching `BfsBlock`: every lemma its
proof uses is public, so `bfsBlockA_specW` below is that proof walked
again, with the two facts routed into the postcondition instead of
discarded. Nothing else moves — precondition, program and cost are
`bfsBlock_specW`'s, character for character.
-/

namespace Lax3Proofs.Refine.ScatterBlock

open Lax3.ColoredGraphs Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.Refine

/-- **Block-driven breadth-first search, charged to its ball, with the
queue segment ranged and ball-bounded.** This is `BfsBlock.bfsBlock_specW`
with two clauses added to the postcondition and nothing else changed:

* `σ'.vars "tail" ≤ nb` — the segment is charged to the ball, not to the
  carrier, which is what lets a consumer walk it at block cost;
* `∀ i < σ'.vars "tail", Q i < n` — every queue entry is a vertex of the
  carrier, which is what lets a consumer index an array by one.

The proof is `bfsBlock_specW`'s own: both facts are computed there (from
`Frame.qmem` and `tail_le_card`) and then dropped at the final `refine`.
-/
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
      (BfsBlock.bfsBlockK bw nb) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hsrc, hoff, htgt, halv, hdist, ⟨g₁, hq⟩, ⟨g₂, hqd⟩⟩ := hσ
  -- the seed, on an array that is clean already
  obtain ⟨σ₁, K₁, hrun₁, hK₁, hI₁, hhead₁, hsc₁⟩ :=
    seedSrc_run (G := G) (O := O) (T := T) (nt := nt) hs hnB hdB hMB hn hsrc hoff htgt
      halv hdist (fun _ _ => rfl) hq
  -- the search, charged to the ball
  obtain ⟨σ₂, K₂, hrun₂, hI₂, hhead₂, hpay⟩ :=
    BfsBlock.drain_ball hcsr hnB hnsB hnt hdB hMB hA hbw hnb hI₁
  obtain ⟨D, Q, ⟨hn₂, hsrc₂, hoff₂, htgt₂, halv₂, hdist₂, hq₂⟩, hFr₂, -⟩ := hI₂
  rw [hhead₂] at hFr₂
  -- neither the seed nor the search touches the second output array
  have hqd₂ : σ₂.arrs "qd" = arrOf n g₂ := by
    rw [hrun₂.frame_arr "qd" (by simp [bfsDrain, expandRow, scanSlot, Csr.loadRow, Csr.scan,
        Queue.drain, Com.warrs]),
      hrun₁.frame_arr "qd" (by simp [seedSrc, Com.warrs])]
    exact hqd
  -- what the search leaves, in the form the unwind asks for
  have htl : σ₂.vars "tail" ≤ n := hFr₂.tl
  have hqn : ∀ i, i < σ₂.vars "tail" → Q i < n := fun i hi => (hFr₂.qmem i hi).1
  have hDd : ∀ z, z < n → D z ≤ d + 1 := hFr₂.cap
  have hdisc0 : ∀ z, z < n → D z ≤ d → z = s ∨ ∃ j, j < σ₂.vars "tail" ∧ Q j = z := by
    intro z hz hzd
    by_cases hmz : M z = 0
    · -- a dead discovered vertex can only be the source
      refine Or.inl ?_
      by_contra hzs
      exact BfsBlock.alive_of_wd (hFr₂.sound z hz hzd) (Ne.symm hzs) hmz
    · obtain ⟨i, hi, hqi⟩ := hFr₂.qall z hz hmz hzd
      exact Or.inr ⟨i, hi, hqi⟩
  -- the unwind
  obtain ⟨σ₃, K₃, hrun₃, hK₃, hdist₃, hq₃, QD, hqd₃, hcopy₃⟩ :=
    BfsBlock.unwind_run (O := O) (T := T) (nt := nt) (M := M) hs hnB hdB htl hqn
      (fun i hi j hj => hFr₂.qinj i hi j hj) hDd hdisc0 hn₂ hsrc₂ rfl hoff₂ htgt₂ halv₂
      hdist₂ hq₂ hqd₂
  have htail₃ : σ₃.vars "tail" = σ₂.vars "tail" :=
    hrun₃.frame_var "tail" (by simp [BfsBlock.unwind, BfsBlock.unwindSlot, Csr.scan, Com.wvars])
  -- the ball bound at the seed, which is what the potential starts at
  obtain ⟨D₁, Q₁, -, hFr₁, -⟩ := hI₁
  have htail₁ : σ₁.vars "tail" ≤ nb := le_trans (BfsBlock.tail_le_card hFr₁ hA) hnb
  -- and the ball bound at the exit, which the landed export drops
  have htail₂nb : σ₂.vars "tail" ≤ nb := le_trans (BfsBlock.tail_le_card hFr₂ hA) hnb
  have hpot₁ : BfsBlock.BallPot bw nb σ₁ = 44 * bw + 40 * nb := by
    simp only [BfsBlock.BallPot, hhead₁, hsc₁]; omega
  refine ⟨σ₃, _, (hrun₁.seq (hrun₂.seq hrun₃)).mono ?_, le_rfl, hdist₃, Q, QD, hq₃, hqd₃,
    by omega, by omega, fun i hi => hqn i (by omega), fun v hv => ?_,
    fun i hi j hj => hFr₂.qinj i (by omega) j (by omega), fun i hi k hk => ?_⟩
  · -- the charge
    rw [hpot₁] at hpay
    simp only [BfsBlock.bfsBlockK]
    omega
  · -- the queue segment is the ball
    rw [htail₃]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hqn', hqd', hqm'⟩ := hFr₂.qmem i hi
      exact ⟨hqm', WD.mono hqd' (hFr₂.sound _ hqn' hqd')⟩
    · rintro ⟨hmv, hwv⟩
      obtain ⟨i, hi, hqi⟩ := hFr₂.qall v hv hmv (hFr₂.complete d le_rfl v hwv)
      exact ⟨i, hi, hqi⟩
  · -- and the distances it carries are the landed thresholds
    rw [htail₃] at hi
    rw [hcopy₃ i hi]
    exact hFr₂.dist_le_iff (hqn i hi) hk

#print axioms bfsBlockA_specW

end Lax3Proofs.Refine.ScatterBlock
