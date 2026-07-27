import Lax14.Ramsey
import Lax14.MulticolorRamsey
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
Ramsey's theorem in the finite unordered form the ported sparsity
development consumes: two colors (clique versus independent set), then an
arbitrary finite list of colors.  Nothing is proved here — both lemmas are
transports of the statements of the `finite-ramsey` submission from its
canonical `Fin n` carriers to the varying finite vertex types of the
ported development, along `Fintype.equivFin`.
-/

namespace Lax12Proofs.Ramsey

open SimpleGraph Finset

/-- Ramsey's theorem (two colors): for any `a b : ℕ` there exists `N` such that
    every graph on at least `N` vertices either contains a clique of size `a` or
    an independent set of size `b`. (Theorem 3.7) -/
theorem ramsey (a b : ℕ) : ∃ N : ℕ,
    ∀ {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
    N ≤ Fintype.card V → ¬G.CliqueFree a ∨ ¬Gᶜ.CliqueFree b := by
  classical
  obtain ⟨N, hN⟩ := Lax14.Ramsey.exists_clique_or_indepSet a b
  refine ⟨N, ?_⟩
  intro V _ _ G _ hcard
  set e := Fintype.equivFin V with he
  have hinj : Function.Injective (e.symm : Fin (Fintype.card V) → V) :=
    e.symm.injective
  rcases hN (Fintype.card V) (G.comap (e.symm : Fin (Fintype.card V) → V)) hcard with
    ⟨S, hS, hSa⟩ | ⟨S, hS, hSb⟩
  · left
    have hcardT : a ≤ (S.toFinset.image (e.symm : Fin (Fintype.card V) → V)).card := by
      rw [Finset.card_image_of_injective _ hinj, ← Set.ncard_eq_toFinset_card']
      exact hSa
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcardT
    refine SimpleGraph.IsNClique.not_cliqueFree (s := T) ⟨?_, hTcard⟩
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 (hTsub hx)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (hTsub hy)
    exact hS (Set.mem_toFinset.1 hu) (Set.mem_toFinset.1 hv) fun h => hxy (by rw [h])
  · right
    have hcardT : b ≤ (S.toFinset.image (e.symm : Fin (Fintype.card V) → V)).card := by
      rw [Finset.card_image_of_injective _ hinj, ← Set.ncard_eq_toFinset_card']
      exact hSb
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcardT
    refine SimpleGraph.IsNClique.not_cliqueFree (s := T) ⟨?_, hTcard⟩
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 (hTsub hx)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (hTsub hy)
    refine ⟨hxy, ?_⟩
    exact (SimpleGraph.isIndepSet_iff _).1 hS (Set.mem_toFinset.1 hu)
      (Set.mem_toFinset.1 hv) fun h => hxy (by rw [h])

/-- Multicolor Ramsey theorem: for any list of natural numbers
    `sizes = [n₁, …, nₖ]`, there exists `N` such that every `k`-coloring of
    edges of a complete graph on at least `N` vertices yields a monochromatic
    clique of size `nᵢ` in color `i`, for some `i`. (Theorem 3.8) -/
theorem multicolor_ramsey (sizes : List ℕ) (_hk : sizes ≠ []) :
    ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V],
      N ≤ Fintype.card V →
      ∀ (c : Sym2 V → Fin sizes.length),
        ∃ (i : Fin sizes.length) (S : Finset V),
          sizes.get i ≤ S.card ∧
          (↑S : Set V).Pairwise (fun u v => c s(u, v) = i) := by
  classical
  obtain ⟨N, hN⟩ := Lax14.MulticolorRamsey.exists_monochromatic_set sizes.length
    (Finset.univ.sup fun i : Fin sizes.length => sizes.get i)
  refine ⟨N, ?_⟩
  intro V _ _ hcard c
  set e := Fintype.equivFin V with he
  have hinj : Function.Injective (e.symm : Fin (Fintype.card V) → V) :=
    e.symm.injective
  obtain ⟨i, S, hS, hpair⟩ :=
    hN (Fintype.card V) (fun p => c (Sym2.map (e.symm : Fin (Fintype.card V) → V) p)) hcard
  refine ⟨i, S.toFinset.image (e.symm : Fin (Fintype.card V) → V), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, ← Set.ncard_eq_toFinset_card']
    exact le_trans (Finset.le_sup (f := fun j : Fin sizes.length => sizes.get j)
      (Finset.mem_univ i)) hS
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Set.coe_toFinset, Set.mem_image] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    have := hpair hu hv fun h => hxy (by rw [h])
    simpa using this

end Lax12Proofs.Ramsey
