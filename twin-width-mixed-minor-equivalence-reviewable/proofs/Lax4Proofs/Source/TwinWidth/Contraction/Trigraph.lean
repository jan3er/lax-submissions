import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic

/-!
# Trigraph states

Trigraph states are represented on a fixed original vertex type by a partition
of the original vertices into current bags, together with black and red
adjacency relations between bags.
-/

namespace Lax4Proofs.TwinWidth

/-- A trigraph state consists of a bag partition of the original vertices and
black/red adjacency relations between bags.  Red edges are the errors counted by
twin-width. -/
structure TrigraphState (V : Type*) where
  /-- Current bags, represented as nonempty finite subsets of the original
  vertex set. -/
  bags : Finset (Finset V)
  /-- Every current bag is nonempty. -/
  bag_nonempty : ∀ ⦃A⦄, A ∈ bags → A.Nonempty
  /-- Current bags are pairwise disjoint. -/
  bag_disjoint : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → A ≠ B → Disjoint A B
  /-- Current bags cover the original vertex set. -/
  bag_cover : ∀ v : V, ∃ A ∈ bags, v ∈ A
  /-- Black, homogeneous adjacencies between current bags. -/
  blackAdj : Finset V → Finset V → Prop
  /-- Red, error adjacencies between current bags. -/
  redAdj : Finset V → Finset V → Prop
  /-- Black adjacency is symmetric on bags. -/
  black_symm : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → blackAdj B A
  /-- Red adjacency is symmetric on bags. -/
  red_symm : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → redAdj A B → redAdj B A
  /-- No bag has a black loop. -/
  black_irrefl : ∀ ⦃A⦄, A ∈ bags → ¬ blackAdj A A
  /-- No bag has a red loop. -/
  red_irrefl : ∀ ⦃A⦄, A ∈ bags → ¬ redAdj A A
  /-- A pair of bags is not simultaneously black and red. -/
  black_red_disjoint : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → ¬ redAdj A B

namespace TrigraphState

/-- The singleton bag family of the finest partition. -/
noncomputable def singletonBags (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.image (fun v : V => ({v} : Finset V))

@[simp] theorem mem_singletonBags {V : Type*} [Fintype V] [DecidableEq V]
    {A : Finset V} :
    A ∈ singletonBags V ↔ ∃ v : V, A = {v} := by
  classical
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨v, _hv, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact Finset.mem_image.mpr ⟨v, by simp, rfl⟩

@[simp] theorem card_singletonBags (V : Type*) [Fintype V] [DecidableEq V] :
    (singletonBags V).card = Fintype.card V := by
  classical
  rw [singletonBags]
  refine Finset.card_image_of_injective _ ?_
  intro a b h
  exact Finset.singleton_inj.mp h

/-- The red degree of a bag in a trigraph state. -/
noncomputable def redDegree {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A : Finset V) : ℕ :=
  by
    classical
    exact (T.bags.filter fun B => T.redAdj A B).card

end TrigraphState

end Lax4Proofs.TwinWidth
