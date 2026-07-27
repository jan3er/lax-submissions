import Lax14.Ramsey
import Lax14.MulticolorRamsey
import Mathlib.Tactic.FinCases

/-!
Ramsey's theorem in its graph form, assembled from the multicolour statement
of this submission.  This module consumes no source material: it colours a
pair by whether it is an edge and reads the two colour classes as a clique and
an independent set.
-/

namespace Lax14Proofs.Ramsey

open Lax14.MulticolorRamsey

/--
---
conclusion: Lax14.Ramsey.exists_clique_or_indepSet
assumptions:
  - Lax14.MulticolorRamsey.exists_monochromatic_set
---
Every large enough graph contains a clique on `a` vertices or an independent
set on `b` vertices, derived from the multicolour Ramsey theorem for pairs of
this submission.

# Proof strategy

The graph form is the two-colour case of the multicolour statement, and this
module derives it that way rather than reproving it, so that the archive
records the derivation.

Apply `Lax14.MulticolorRamsey.exists_monochromatic_set` with two colours and
requested size `max a b`, and colour a pair of vertices by `0` when it is an
edge of the graph and by `1` otherwise.  The colouring is well defined on
unordered pairs because adjacency is symmetric, which is what `Sym2.lift`
requires.  The resulting monochromatic set of size at least `max a b` is a
clique when its colour is `0` and an independent set when its colour is `1`,
since `Set.Pairwise` in either case says exactly that distinct members are
adjacent, respectively non-adjacent; `max` then supplies the requested bound
`a` in the first branch and `b` in the second.

# Attribution

Ramsey, *On a problem of formal logic* (Proc. London Math. Soc. 1930).  The
mathematical content sits in the proof of the multicolour statement
(`Lax14Proofs.MulticolorRamsey`), ported from the proof package of the
submission *Monadic dependence and neighborhood complexity*; this module is
only the two-colour specialization.
-/
theorem exists_clique_or_indepSet (a b : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n →
      (∃ S : Set (Fin n), G.IsClique S ∧ a ≤ S.ncard) ∨
      (∃ S : Set (Fin n), G.IsIndepSet S ∧ b ≤ S.ncard) := by
  classical
  obtain ⟨N, hN⟩ := exists_monochromatic_set 2 (max a b)
  refine ⟨N, fun n G hn => ?_⟩
  set c : Sym2 (Fin n) → Fin 2 :=
    Sym2.lift ⟨fun u v => if G.Adj u v then 0 else 1, by
      intro u v
      simp [SimpleGraph.adj_comm]⟩ with hc
  obtain ⟨i, S, hcard, hpair⟩ := hN n c hn
  have hcval : ∀ u v : Fin n, c s(u, v) = if G.Adj u v then 0 else 1 := by
    intro u v; rw [hc]; rfl
  fin_cases i
  · refine Or.inl ⟨S, ?_, le_trans (le_max_left a b) hcard⟩
    intro u hu v hv huv
    have := hpair hu hv huv
    simp only [hcval] at this
    by_cases h : G.Adj u v
    · exact h
    · simp [h] at this
  · refine Or.inr ⟨S, ?_, le_trans (le_max_right a b) hcard⟩
    intro u hu v hv huv
    have := hpair hu hv huv
    simp only [hcval] at this
    by_cases h : G.Adj u v
    · simp [h] at this
    · exact h

end Lax14Proofs.Ramsey
