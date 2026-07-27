import Lax14.MulticolorRamsey
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card

/-!
Ramsey's theorem for colourings of pairs, in the finite unordered form the
nowhere-dense bridge consumes: an arbitrary finite list of colours over a
varying finite vertex type.  Nothing is proved here — the lemma is a
transport of `Lax14.MulticolorRamsey.exists_monochromatic_set`, the
statement of the `finite-ramsey` submission, from its canonical `Fin n`
carriers along `Fintype.equivFin`.  The signature is unchanged from the
version that carried the proof, so `Lax5Proofs.NowhereDenseBridge` needs
no edits.
-/

namespace Lax5Proofs.Ramsey

/-- Multicolor Ramsey theorem: for any list of natural numbers
    `sizes = [n₁, …, nₖ]`, there exists `N` such that every `k`-coloring of
    edges of a complete graph on at least `N` vertices yields a monochromatic
    clique of size `nᵢ` in color `i`, for some `i`. (Theorem 3.8)

The `sizes ≠ []` hypothesis is not needed by this derivation — the assumed
statement places no condition on the number of colours — but is kept in the
signature so that consumers are untouched. -/
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

end Lax5Proofs.Ramsey
