import Lax12.NowhereDenseUQW
import Lax12Proofs.MinorBridge
import Lax12Proofs.QuasiWidenessInduction

/-!
Lemma 3.4 of Chapter 4 of the notes, transported to the submitted
concepts: nowhere dense classes are uniformly quasi-wide.
-/

namespace Lax12Proofs.NowhereDenseUQW

open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.UniformQuasiWideness
open Lax12Proofs.MinorBridge

/--
---
conclusion: Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense
assumptions:
  - Lax14.MulticolorRamsey.exists_monochromatic_set
  - Lax14.Ramsey.exists_clique_or_indepSet
---
Every nowhere dense graph class is uniformly quasi-wide: for every radius
`r` there are a threshold function `N` and a separator bound `s` such that
in every member, every vertex set of size at least `N m` contains a
distance-`r` independent subset of size at least `m` after deleting at
most `s` vertices.

# Proof strategy

The ported development proves the statement for classes indexed by
arbitrary finite vertex types.  The submitted class `C` is therefore
closed under subgraph copies — the closure is nowhere dense in the ported
sense as soon as `C` is nowhere dense in the submitted sense, since a
ported minor model of a clique in a copy pushes forward to a submitted
minor model in the host — the ported theorem is applied to the closure,
and the conclusion is specialized back to the members of `C` themselves.
What remains is packaging: the ported statement is phrased with `Finset`
and `card`, the submitted one with `Set` and `Set.ncard`, and the two are
matched by `Set.toFinset` and `Set.ncard_coe_finset`.  Distance
independence and vertex deletion need no translation at all: the ported
step-reduction modules are stated over the definitions of the submitted
concept.

The ported induction alternates an odd and an even distance-reduction
step and consumes Ramsey's theorem twice — directly, to extract a
homogeneous set, and through the bipartite Ramsey lemma (Lemma 3.9 of the
notes) — so both Ramsey statements of the `finite-ramsey` submission are
assumed rather than reproved here.

# Attribution

The statement is Lemma 3.4 of Chapter 4 of the sparsity lecture notes of
Pilipczuk and Pilipczuk (2019/20 edition), the hard direction of their
Theorem 3.2.  The proof is a port of the formalization accompanying those
notes, whose type-polymorphic version is
`Lax12Proofs.QuasiWidenessInduction.nd_implies_uqw`.
-/
theorem uniformlyQuasiWide_of_nowhereDense (C : GraphClass) (h : NowhereDense C) :
    UniformlyQuasiWide C := by
  classical
  intro r
  obtain ⟨N, s, huqw⟩ := Lax12Proofs.QuasiWidenessInduction.nd_implies_uqw
    (subgraphClosure C) (isNowhereDense_subgraphClosure h) r
  refine ⟨N, s, fun m n G hG A hA => ?_⟩
  have hAcard : N m ≤ A.toFinset.card := by
    rwa [← Set.ncard_eq_toFinset_card']
  obtain ⟨S, B, hS, hBsub, hBcard, hBindep⟩ :=
    huqw m G (subgraphClosure_self hG) A.toFinset hAcard
  refine ⟨↑S, ↑B, ?_, ?_, ?_, hBindep⟩
  · rw [Set.ncard_coe_finset]; exact hS
  · intro x hx
    have hx' := hBsub hx
    simp only [Finset.mem_sdiff, Set.mem_toFinset] at hx'
    exact ⟨hx'.1, hx'.2⟩
  · rw [Set.ncard_coe_finset]; exact hBcard

end Lax12Proofs.NowhereDenseUQW
