import Lax3Proofs.RamDriver

/-!
**The counted scan at per-turn costs** — the Σ-shaped loop rule of the
ND-MC integration wave.

`Lax13Proofs.Reasoning.Spec.forRangeZero` charges every turn of a
counted scan the same budget `Kb`, so a loop over the centres of a
cover pays `n · max-turn` even when the true total is `Σ_c |X_c|` —
the star instance (`Refine.CostShapeProbe`) shows the gap is
quadratic-vs-linear. `forRangeZeroSum` below is the same rule with the
body given **per counter value**: turn `k` owes `Kb k`, and the loop
exports `Σ_{k<N} (Kb k + 4) + 6`. Instantiating `Kb` constantly
recovers `forRangeZero`'s bound exactly, so the rule strictly refines
the uniform one (`sum_const_bound` in `CostShapeProbe` is that
comparison, compiled).

This is *capital for the Σ-shape revision* of
`RamDriverCluster.levelImplements` (integration-design.md §5): the
centre loop's per-turn budget must read the turn's own cluster data —
`Kb k` there is the per-turn overhead plus the nested driver at the
sub-arena of block `k`. The rule lives here, in the consumer package,
because `word-ram/` is owned by a parallel wave; it is proved from
`Spec.while_potential` alone, exactly as `Spec.forRange` is.

The potential is `Φ σ = Σ_{k ∈ [x, N)} (Kb k + 4)`: one guard (`+4` is
`1 + size(x < m)`) and one body per remaining turn. The peel at the
step is `Finset.sum_eq_sum_Ico_succ_bot`; everything else is
`forRangeZero`'s own walk.
-/

namespace Lax3Proofs.Refine.SigmaLoop

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Finset

variable {B : ℕ} {c : Com}

/-- **The counted scan from zero, with one budget per turn.**
`x := 0; while x < m do c`, where the turn at counter value `k` is
specified with its own cost `Kb k`. The loop costs the sum of the
turns, not `N` times the worst one: `Σ_{k<N} (Kb k + 4) + 6`.

The hypotheses are `Spec.forRangeZero`'s with the body quantified over
the counter value; a body that does not care recovers the uniform rule
by ignoring `k`. -/
theorem forRangeZeroSum (x m : String) (I : Env → Prop) (N : ℕ) (Kb : ℕ → ℕ)
    (hNB : N < B)
    (hxN : ∀ σ, I σ → σ.vars x ≤ N) (hm : ∀ σ, I σ → σ.vars m = N)
    (hbody : ∀ k, k < N → Spec B (fun σ => I σ ∧ σ.vars x = k) c
      (fun _ σ' => I σ' ∧ σ'.vars x = k + 1) (Kb k)) :
    Spec B (fun σ => I (σ.setVar x 0))
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) c))
      (fun _ σ' => I σ' ∧ σ'.vars x = N)
      ((∑ k ∈ range N, (Kb k + 4)) + 6) := by
  have hsize : (Cond.lt (Expr.var x) (Expr.var m)).size = 3 := by simp
  have hloop : Spec B I (.while (.lt (.var x) (.var m)) c)
      (fun _ σ' => I σ' ∧ σ'.vars x = N)
      ((∑ k ∈ range N, (Kb k + 4)) + 4) := by
    refine (Spec.while_potential (b := .lt (.var x) (.var m)) (c := c) I
      (fun σ => ∑ k ∈ Ico (σ.vars x) N, (Kb k + 4))
      (fun σ hI => evalB_condLt_vars (lt_of_le_of_lt (hxN σ hI) hNB)
        (by rw [hm σ hI]; exact hNB)) ?_ (fun _ h => h) ?_).post ?_
    · -- the step: turn `σ.vars x`, paid out of the potential's bottom cell
      intro σ hI hv
      have hlt : σ.vars x < N := by
        have := lt_of_condLt_true hv
        rw [hm σ hI] at this
        exact this
      obtain ⟨σ', hr, hI', hx'⟩ := (hbody (σ.vars x) hlt).run ⟨hI, rfl⟩
      refine ⟨σ', Kb (σ.vars x), hr, hI', ?_⟩
      have hpeel : ∑ k ∈ Ico (σ.vars x) N, (Kb k + 4) =
          (Kb (σ.vars x) + 4) + ∑ k ∈ Ico (σ.vars x + 1) N, (Kb k + 4) :=
        sum_eq_sum_Ico_succ_bot hlt _
      show 1 + (Cond.lt (Expr.var x) (Expr.var m)).size + Kb (σ.vars x) +
          (∑ k ∈ Ico (σ'.vars x) N, (Kb k + 4)) ≤ ∑ k ∈ Ico (σ.vars x) N, (Kb k + 4)
      rw [hsize, hx', hpeel]
      omega
    · -- the entry: the whole potential fits under the exported cost
      intro σ hI
      have hsub : ∑ k ∈ Ico (σ.vars x) N, (Kb k + 4) ≤ ∑ k ∈ range N, (Kb k + 4) := by
        rw [← Nat.Ico_zero_eq_range]
        exact sum_le_sum_of_subset (Ico_subset_Ico (Nat.zero_le _) le_rfl)
      show (∑ k ∈ Ico (σ.vars x) N, (Kb k + 4)) + 1 +
          (Cond.lt (Expr.var x) (Expr.var m)).size ≤ (∑ k ∈ range N, (Kb k + 4)) + 4
      rw [hsize]
      omega
    · -- the exit: a failed `x < m` at `x ≤ N`, `m = N` is `x = N`
      intro σ σ' hI hq
      refine ⟨hq.1, ?_⟩
      have h₁ := le_of_condLt_false hq.2
      have h₂ := hm σ' hq.1
      have h₃ := hxN σ' hq.1
      omega
  intro σ hσ
  obtain ⟨σ', hrun, hI', hx'⟩ := hloop.run hσ
  exact ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono (by simp; omega),
    hI', hx'⟩

/-- **The uniform rule is the constant instantiation**: with every turn
at the same `Kb`, the Σ-shaped cost is exactly `forRangeZero`'s
`(Kb + 4) * N + 6`. So re-threading a consumer from the uniform rule to
this one never costs slack. -/
theorem sum_const_eq_uniform (N Kb : ℕ) :
    (∑ _k ∈ range N, (Kb + 4)) + 6 = (Kb + 4) * N + 6 := by
  rw [sum_const, card_range, smul_eq_mul, Nat.mul_comm]

end Lax3Proofs.Refine.SigmaLoop
