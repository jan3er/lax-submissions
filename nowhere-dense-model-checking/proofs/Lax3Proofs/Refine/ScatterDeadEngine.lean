import Lax3Proofs.Refine.ScatterDeadFold
import Lax3Proofs.Refine.ScatterBlock
import Lax3Proofs.Refine.ScatterBlockDiff

/-!
# The engine's count, exported — the E4 dead fold meets the machine

`ScatterDeadFold.scatVal_fold` splits a scatter atom's answer into three
terms: the greedy count of the *alive* part of the atom's set, the kill
bits, and the outside class's bit times its count. The landed active-set
engine (`Refine.ScatterBlock.scatBlock_specW`) decides only a threshold
flag about the one set it walks, so the two dead terms — runtime
scalars, unknown at construction time — cannot be folded into the
threshold literal of the program text. What CAN carry them is the
engine's own counter: the scan leaves `"cnt"` holding the greedy count
capped at the threshold, and the capped count decides `t ≤ count + e`
for **every** additive term `e` — that is `cnt_decides` below, and
`scatVal_of_cnt` is the atom's answer assembled from it.

## The falsification first

The naive export — `cnt` IS the greedy count — is **false**: the scan
stops counting at the threshold. The two compiled gates below run the
engine on `ScatterBlockDiff`'s five-vertex arena (greedy count three)
and watch the counter: at threshold `2` the machine reports `2`, not
`3`. The `∀ e` form is exactly what survives the cap, and the second
gate (`threshold 4`, counter `3`) is the uncapped control.
-/

namespace Lax3Proofs.Refine.ScatterDeadEngine

open Lax3.ColoredGraphs Lax3.ScatterSentences
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamScatter
open Lax3Proofs.Refine.ScatterBlock

variable {n ns nt mm r t : ℕ} {G : SimpleGraph (Fin n)} {M O T Mem : ℕ → ℕ}
  {X : Set (Fin n)}

/-! ### §1 The counter is capped — the compiled refutation -/

/-- The differential arena's run, watching `"cnt"` instead of
`"flag"`. -/
def demoCnt (b2 r t : ℕ) : Com :=
  .seq (Diff.demoSetup b2 r) (.seq (scatBlockCom r t) (.write (.var "cnt")))

/-- Its machine program, at the differential file's own layout. -/
def demoCntProg (b2 r t : ℕ) : Lax13.Ram.Program :=
  Lax13Proofs.Compile.compileProgram Diff.demoLayout (demoCnt b2 r t)

def demoCntRun (b2 r t : ℕ) : Option (List ℕ × ℕ) :=
  runOut 16 40000 (demoCntProg b2 r t) (Lax13.Ram.initState []) 0

/- **The cap is real**: the greedy count of the full-table arena is
three, and at threshold two the counter reports two. `cnt = count` is
refuted; only the `∀ e` reading below is true. -/
#guard (demoCntRun 1 1 2).map Prod.fst = some [2]

/- **And below the cap the counter is the count**: threshold four,
counter three. -/
#guard (demoCntRun 1 1 4).map Prod.fst = some [3]

/-! ### §2 The export

`scatBlock_specW`'s own proof, re-run with the counter kept in the
postcondition. The landed flag clauses are unchanged; what is new is
`cnt ≤ t` and the `∀ e` decision clause, read off the scan invariant's
exit disjunction (`ProgressA` at the end of the carrier): either the
counter hit the threshold — then both sides of the biconditional are
true outright — or the scan ran out of members and the counter is the
whole greedy count (`selBelow_all`). -/

/-- **The active-set pass, with its counter.** Identical hypotheses and
program as `Refine.ScatterBlock.scatBlock_specW`; the postcondition
keeps `"cnt"`, which decides the threshold against the greedy count
*plus any additive term* — the shape the dead fold consumes. -/
theorem scatBlockCnt_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaA n nt mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1 ∧ σ'.vars "cnt" ≤ t ∧
        ∀ e : ℕ, (t ≤ σ'.vars "cnt" + e ↔ t ≤ (greedySet (masked G M) r X).ncard + e))
      (scatBlockK mm bw nb t) := by
  have hmmn : mm ≤ n := hml.card_le
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hA, g, hexc⟩ := hσ
  obtain ⟨hn, hmmv, hoff, htgt, halv, hmem, hdist, hqex, hqdex⟩ := id hA
  -- the counter
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = σ.setVar "cnt" 0 := ⟨_, rfl⟩
  have run₁ : Run B (.assign "cnt" (.lit 0)) σ τ₁ 2 := by
    rw [hτ₁]; exact (Run.assign (v := 0) (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hv₁ : ∀ y, y ≠ "cnt" → τ₁.vars y = σ.vars y := by
    intro y hy; rw [hτ₁]; simp [hy]
  have ha₁ : τ₁.arrs = σ.arrs := by rw [hτ₁]; simp
  have hcnt₁ : τ₁.vars "cnt" = 0 := by rw [hτ₁]; simp
  have hA₁ : ArenaA n nt mm r O T M Mem τ₁ := by
    rw [hτ₁]; exact hA.setVar (by decide) (by decide)
  -- the exclusion bits, at the members
  obtain ⟨τ₂, K₂, run₂, hK₂, hmem₂, E, hexc₂, hclear, -⟩ :=
    clearMem_run (n := n) (mm := mm) (B := B) (Mem := Mem) (X := X)
      hnB (by omega) hml (by rw [hv₁ "n" (by decide)]; exact hn)
      (by rw [hv₁ "mm" (by decide)]; exact hmmv)
      (by rw [ha₁]; exact hmem) (by rw [ha₁]; exact hexc)
  have hcnt₂ : τ₂.vars "cnt" = 0 := by
    rw [run₂.frame_var "cnt" (notMem_clearMem_wvars "cnt" (by simp)), hcnt₁]
  have harr₂ : ∀ a, a ∈ ["off", "tgt", "alv", "dist", "q", "qd"] → τ₂.arrs a = σ.arrs a := by
    intro a ha
    rw [run₂.frame_arr a (notMem_clearMem_warrs a (by fin_cases ha <;> simp)), ha₁]
  have hA₂ : ArenaA n nt mm r O T M Mem τ₂ := by
    obtain ⟨g₆, hq⟩ := hqex
    obtain ⟨g₇, hqd⟩ := hqdex
    refine ⟨?_, ?_, by rw [harr₂ "off" (by simp)]; exact hoff,
      by rw [harr₂ "tgt" (by simp)]; exact htgt,
      by rw [harr₂ "alv" (by simp)]; exact halv, hmem₂,
      by rw [harr₂ "dist" (by simp)]; exact hdist,
      ⟨g₆, by rw [harr₂ "q" (by simp)]; exact hq⟩,
      ⟨g₇, by rw [harr₂ "qd" (by simp)]; exact hqd⟩⟩
    · rw [run₂.frame_var "n" (notMem_clearMem_wvars "n" (by simp)),
        hv₁ "n" (by decide), hn]
    · rw [run₂.frame_var "mm" (notMem_clearMem_wvars "mm" (by simp)),
        hv₁ "mm" (by decide), hmmv]
  -- the scan starts with nothing selected and nothing excluded
  have hI₂ : ScatBlockInv n nt mm r t G M O T Mem X (τ₂.setVar "sj" 0) := by
    refine ⟨hA₂.setVar (by decide) (by decide), by simp, ?_⟩
    refine progressA_start hml ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact Or.inl ⟨by simp [hcnt₂], by omega⟩
    · refine Or.inr ⟨by simp [hcnt₂]; omega, by simp [hcnt₂, selBelow_zero], E,
        by simp [hexc₂], fun w hw => by rw [hclear w hw]; omega,
        fun w hw => by rw [hclear w hw]; simp⟩
  obtain ⟨τ₃, run₃, hA₃, hP₃, hsj₃⟩ :=
    (loop_spec hcsr hnB hnsB hnt hrB htB hMB hml hbud).run (σ := τ₂) hI₂
  -- the counter clauses, off the exit disjunction
  have hcntt : τ₃.vars "cnt" ≤ t := hP₃.cnt_le
  have hcntB : τ₃.vars "cnt" < B := by omega
  have hkey : ∀ e : ℕ, (t ≤ τ₃.vars "cnt" + e ↔
      t ≤ (greedySet (masked G M) r X).ncard + e) := by
    intro e
    rcases hP₃ with ⟨hc, hle⟩ | ⟨-, hsel, -⟩
    · exact ⟨fun _ => by omega, fun _ => by omega⟩
    · rw [selBelow_all] at hsel
      rw [hsel]
  -- the answer
  have hcv : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B τ₃
      = some (decide (τ₃.vars "cnt" < t)) := evalB_condLt (evalB_var hcntB) (evalB_lit htB)
  by_cases hlt : τ₃.vars "cnt" < t
  · have hns : ¬ t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨h, -⟩ | ⟨-, h, -⟩
      · omega
      · rw [selBelow_all] at h; omega
    refine ⟨τ₃.setVar "flag" 0, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_true (by rw [hcv]; simp [hlt])
        (Run.assign (v := 0) (evalB_lit (by omega)))))),
      ?_, by simp [hns], by simp, by simpa using hcntt, by simpa using hkey⟩
    simp only [scatBlockK, clearMemK, scanMemK, Cond.size, Expr.size]
    have : K₂ ≤ clearMemK mm := hK₂
    simp only [clearMemK] at this
    omega
  · have hyes : t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    refine ⟨τ₃.setVar "flag" 1, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_false (by rw [hcv]; simp [hlt])
        (Run.assign (v := 1) (evalB_lit (by omega)))))),
      ?_, by simp [hyes], by simp, by simpa using hcntt, by simpa using hkey⟩
    simp only [scatBlockK, clearMemK, scanMemK, Cond.size, Expr.size]
    have : K₂ ≤ clearMemK mm := hK₂
    simp only [clearMemK] at this
    omega

/-! ### §3 The atom's answer, assembled

The lynchpin of flag F-1: the engine's counter at the atom's *alive*
part, the kill scalar and the outside scalar decide `ScatVal` — no term
of which reads a row outside `alive ∪ kills`. The two scalar hypotheses
are what the kill-list walk and the outside probe leave
(`ScatterDeadFold.outside_ncard_of_probe` /
`outside_ncard_of_empty` turn the probe's bit into `oc`). -/

open Lax3Proofs.Refine.ScatterDeadFold in
/-- **`ScatVal`, decided by the engine's counter and the two dead
scalars.** `cnt` is the engine's counter at the member list of the
atom's alive part, `kc` the kill bits' sum, `oc` the outside term; the
atom's answer is the threshold against their sum. -/
theorem scatVal_of_cnt {L mb cap : ℕ} {G A : SimpleGraph (Fin n)} {M' : ℕ → ℕ}
    {col : Coloring n L} {Xc : Set (Fin n)} {w : Fin mb → Fin n}
    (σs : ScatterSentence (Lax3Proofs.Evaluator.isoPalette (L + 1) mb cap))
    {cnt kc oc : ℕ}
    (hcnt : ∀ e : ℕ, (σs.t ≤ cnt + e ↔
      σs.t ≤ (greedySet (masked G M') σs.r
        (satSet G A M' col Xc w σs.β ∩ Lax3Proofs.RamDriverCluster.markSet n M')).ncard + e))
    (hkc : kc = (ScatterDeadFold.deadSet n M' ∩ Xc ∩ satSet G A M' col Xc w σs.β).ncard)
    (hoc : oc = ((ScatterDeadFold.deadSet n M' \ Xc) ∩ satSet G A M' col Xc w σs.β).ncard) :
    (Lax3Proofs.RamDriverCluster.ScatVal (masked G M')
        (Lax3Proofs.RamDriver.stepColoringP cap A col Xc w) σs ↔
      σs.t ≤ cnt + (kc + oc)) := by
  rw [scatVal_fold σs, hkc, hoc]
  exact (hcnt _).symm

/-! ### §4 Axioms -/

/-- info: 'Lax3Proofs.Refine.ScatterDeadEngine.scatBlockCnt_specW' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms scatBlockCnt_specW

/-- info: 'Lax3Proofs.Refine.ScatterDeadEngine.scatVal_of_cnt' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms scatVal_of_cnt

end Lax3Proofs.Refine.ScatterDeadEngine
