import Lax5.NowhereDenseClasses
import Lax5Proofs.Source.Catalog.SparsityLectures.NDImpliesUQW.Full
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
Uniform quasi-wideness in the submission's encoding: the concept
`NowhereDense` transfers to the catalog's shallow-minor
nowhere-denseness of the copy closure (the easy bridge direction —
catalog minor models carry paths, which are in particular the walks the
concept model asks for), and the ported `nd_implies_uqw` then yields,
for every radius, a threshold function and a separator bound that are
uniform over the class.
-/

namespace Lax5Proofs.QuasiWideness

open scoped SimpleGraph
open Lax5.GraphClasses
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor
open Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense
open Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness
open Lax5Proofs.Source.Catalog.SparsityLectures.NDImpliesUQW

/-- The type-polymorphic closure of a submitted class under graph copies. -/
def copyClosure (C : Lax5.GraphClasses.GraphClass) :
    Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries.GraphClass :=
  fun {_} _ _ H => ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧ H ⊑ G

/-- Push a catalog shallow-minor model through a graph copy. -/
private theorem isShallowMinor_of_copy {U W V : Type}
    {K : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (f : SimpleGraph.Copy H G) (h : IsShallowMinor K H d) :
    IsShallowMinor K G d := by
  obtain ⟨M⟩ := h
  refine ⟨{
    branchSet := fun u => f '' M.branchSet u
    center := fun u => f (M.center u)
    center_mem := fun u => ⟨M.center u, M.center_mem u, rfl⟩
    branchDisjoint := fun u v huv => ?_
    branchRadius := fun u x hx => ?_
    branchEdge := fun u v hadj => ?_ }⟩
  · exact Set.disjoint_image_of_injective f.injective (M.branchDisjoint u v huv)
  · obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨p, hp, hlen, hsupp⟩ := M.branchRadius u y hy
    refine ⟨p.map f.toHom,
      SimpleGraph.Walk.map_isPath_of_injective f.injective hp, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_map]; exact hlen
    · intro w hw
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      exact ⟨z, hsupp z hz, rfl⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := M.branchEdge u v hadj
    exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, f.toHom.map_adj hxy⟩

/-- A catalog minor model of the complete graph converts to a submitted
shallow-minor model (paths are walks). -/
private theorem shallowMinorModel_of_isShallowMinor {n t d : ℕ}
    {G : SimpleGraph (Fin n)}
    (h : IsShallowMinor (SimpleGraph.completeGraph (Fin t)) G d) :
    Lax5.NowhereDenseClasses.HasShallowMinor G d (⊤ : SimpleGraph (Fin t)) := by
  obtain ⟨M⟩ := h
  refine ⟨{
    branch := M.branchSet
    center := M.center
    center_mem := M.center_mem
    disjoint := M.branchDisjoint
    radius_le := fun u x hx => ?_
    adj := fun u v huv => M.branchEdge u v (by simpa using huv) }⟩
  obtain ⟨p, _, hlen, hsupp⟩ := M.branchRadius u x hx
  exact ⟨p, hlen, hsupp⟩

/-- The concept formulation of nowhere-denseness transfers to the
catalog formulation for the copy closure. -/
theorem isNowhereDense_copyClosure_of_nowhereDense
    (C : Lax5.GraphClasses.GraphClass)
    (h : Lax5.NowhereDenseClasses.NowhereDense C) :
    IsNowhereDense (copyClosure C) := by
  intro d
  obtain ⟨t, ht⟩ := h d
  refine ⟨t, fun {V} _ _ H hH hminor => ?_⟩
  obtain ⟨n, G, hG, ⟨f⟩⟩ := hH
  have hG_minor := isShallowMinor_of_copy f hminor
  have hconcept := shallowMinorModel_of_isShallowMinor hG_minor
  obtain ⟨M⟩ := hconcept
  have hle : t ≤ t + 1 := Nat.le_succ t
  exact ht n G hG ⟨{
    branch := fun u => M.branch (Fin.castLE hle u)
    center := fun u => M.center (Fin.castLE hle u)
    center_mem := fun u => M.center_mem _
    disjoint := fun u v huv =>
      M.disjoint _ _ fun hc => huv (Fin.castLE_injective hle hc)
    radius_le := fun u => M.radius_le _
    adj := fun u v huv => by
      have hne : u ≠ v := by simpa using huv
      exact M.adj _ _ (by simpa using fun hc => hne (Fin.castLE_injective hle hc)) }⟩

/-- Uniform quasi-wideness of a nowhere dense class, specialized to the
submitted members: for every radius `r` there are a threshold function
`N` and a separator bound `s` such that every `A` of size at least
`N m` in a member contains, after deleting a set `S` of at most `s`
vertices, a subset `B` of size at least `m` that is pairwise more than
`r` apart in `G − S`. -/
theorem uqw_of_nowhereDense (C : Lax5.GraphClasses.GraphClass)
    (h : Lax5.NowhereDenseClasses.NowhereDense C) (r : ℕ) :
    ∃ (N : ℕ → ℕ) (s : ℕ),
      ∀ (m n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ A : Finset (Fin n), N m ≤ A.card →
          ∃ S B : Finset (Fin n),
            S.card ≤ s ∧ ↑B ⊆ ↑A \ ↑S ∧ m ≤ B.card ∧
            DistIndependent (deleteVerts G ↑S) r ↑B := by
  obtain ⟨N, s, huqw⟩ :=
    nd_implies_uqw _ (isNowhereDense_copyClosure_of_nowhereDense C h) r
  exact ⟨N, s, fun m n G hG A hA =>
    huqw m G ⟨n, G, hG, SimpleGraph.IsContained.refl G⟩ A hA⟩

end Lax5Proofs.QuasiWideness
