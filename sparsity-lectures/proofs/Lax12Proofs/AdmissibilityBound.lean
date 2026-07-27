import Lax12.AdmissibilityBound
import Lax12Proofs.MinorBridge
import Lax12Proofs.OrderBridge
import Lax12Proofs.AdmByDensity

/-!
Lemma 3.2 of Chapter 2 of the notes, transported to the submitted
concepts: an edge-density bound on the shallow topological minors of a
graph bounds its admissibility.
-/

namespace Lax12Proofs.AdmissibilityBound

open Lax12.Admissibility Lax12.ShallowTopologicalMinors
open Lax12Proofs.MinorBridge Lax12Proofs.OrderBridge

/--
---
conclusion: Lax12.AdmissibilityBound.adm_le_of_hasTopologicalDensityAtMost
---
If every depth-`r` topological minor of a graph `G` has at most `d`
times as many edges as vertices, then the `(r+1)`-admissibility of `G` is
at most `1 + 6 * (r+1) * d ^ 3`.

# Proof strategy

The ported development proves exactly this statement, at radius `r + 1`
with its hypothesis at depth `(r + 1) - 1 = r`, so the discharge is pure
idiom translation and no weakening step is needed.

Two translations are involved.  On the hypothesis side, the ported
topological minor model routes each *edge* of the minor along a path,
with a chosen tail and `Sym2` plumbing, while the submitted model carries
a walk for each adjacent *pair*; the repackaging orients an edge by its
chosen tail and reverses the walk for the other orientation.  The
submitted density predicate ranges over minors on the canonical carriers
`Fin m` only, so the arbitrary finite carrier of the ported hypothesis is
transported along `Fintype.equivFin` and the edge counts are matched by
`Set.ncard`-to-`edgeFinset` and by invariance of the edge count under a
graph isomorphism.  On the conclusion side, the ported theorem produces a
linear order; its rank permutation witnesses `HasAdmAtMost`, because a
submitted admissible family of walks bypasses to a ported admissible
family of paths of the same size, and the submitted `adm` — an infimum
over permutations — is then bounded by `Nat.sInf_le`.

# Attribution

The statement is Lemma 3.2 of Chapter 2 of the sparsity lecture notes of
Pilipczuk and Pilipczuk (2019/20 edition), with the radius index shifted
by one.  The proof is a port of the formalization accompanying those
notes, whose per-order version is
`Lax12Proofs.AdmByDensity.adm_le_of_topGrad_bound`.
-/
theorem adm_le_of_hasTopologicalDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n))
    (r d : ℕ) (h : HasTopologicalDensityAtMost G r d) :
    adm G (r + 1) ≤ 1 + 6 * (r + 1) * d ^ 3 := by
  classical
  have hd : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W)
      [DecidableRel H.Adj],
      Lax12Proofs.TopologicalMinors.IsShallowTopologicalMinor H G (r + 1 - 1) →
      H.edgeFinset.card ≤ d * Fintype.card W := by
    intro W _ _ H _ hM
    have hM' : HasShallowTopologicalMinor G r H := by
      simpa using hasShallowTopologicalMinor_of_isShallowTopologicalMinor hM
    let e := Fintype.equivFin W
    let H' : SimpleGraph (Fin (Fintype.card W)) := SimpleGraph.map (⇑e) H
    have hiso : H ≃g H' := SimpleGraph.Iso.map e H
    have hcount := h (Fintype.card W) H'
      (hasShallowTopologicalMinor_of_iso hiso.symm hM')
    rw [ncard_edgeSet] at hcount
    rw [hiso.card_edgeFinset_eq]
    exact hcount
  obtain ⟨ord, hadm⟩ :=
    Lax12Proofs.AdmByDensity.adm_le_of_topGrad_bound G (r + 1) d hd
  letI := ord
  refine Nat.sInf_le ⟨rankPerm ord, fun v j hj => ?_⟩
  obtain ⟨F⟩ := hj
  have h1 : j + 1 ≤ Lax12Proofs.OrderedParameters.admVertex G (r + 1) v :=
    le_admVertex_of_admFamily F
  have h2 : Lax12Proofs.OrderedParameters.admVertex G (r + 1) v ≤
      Lax12Proofs.OrderedParameters.adm G (r + 1) :=
    Finset.le_sup (f := fun x => Lax12Proofs.OrderedParameters.admVertex G (r + 1) x)
      (Finset.mem_univ v)
  omega

end Lax12Proofs.AdmissibilityBound
