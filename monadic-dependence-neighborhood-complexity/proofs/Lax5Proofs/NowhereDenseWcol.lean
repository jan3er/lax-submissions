import Lax5.NowhereDenseWcol
import Lax5Proofs.Source.Catalog.SparsityLectures.NDSubpolynomialWcol.Full
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Sort

/-!
The proof is transported from the axiom-free catalog development of
Theorem 3.4 in the sparsity lecture notes.  This file supplies the bridge
from its type-polymorphic graph classes and order-instance coloring numbers
to the submission's canonical `Fin n` classes and permutation-based minimum.
-/

namespace Lax5Proofs.NowhereDenseWcol

open scoped SimpleGraph
open Lax5.GraphClasses
open Lax5.NowhereDenseWcol
open Lax5.NowhereDenseClasses
open Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries
open Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor
open Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense

noncomputable section

/-- The type-polymorphic closure of a submitted class under graph copies. -/
private def copyClosure (C : Lax5.GraphClasses.GraphClass) :
    Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries.GraphClass :=
  fun {_} _ _ H =>
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧ H ⊑ G

/-- A catalog shallow-minor model of a clique in a copied subgraph gives a
submitted shallow-minor model of the preceding clique in the host graph. -/
private theorem copyClosure_isNowhereDense (C : Lax5.GraphClasses.GraphClass)
    (hC : Lax5.NowhereDenseClasses.NowhereDense C) :
    IsNowhereDense (copyClosure C) := by
  intro d
  obtain ⟨t, ht⟩ := hC d
  refine ⟨t, ?_⟩
  intro V _ _ H hH hminor
  rcases hH with ⟨n, G, hCG, ⟨f⟩⟩
  apply ht n G hCG
  rcases hminor with ⟨M⟩
  refine ⟨{
    branch := fun u => f '' M.branchSet u.castSucc
    center := fun u => f (M.center u.castSucc)
    center_mem := fun u => ⟨M.center u.castSucc, M.center_mem u.castSucc, rfl⟩
    disjoint := ?_
    radius_le := ?_
    adj := ?_
  }⟩
  · intro u v huv
    apply Set.disjoint_left.2
    intro x hxu hxv
    rcases hxu with ⟨xu, hxu, rfl⟩
    rcases hxv with ⟨xv, hxv, hEq⟩
    have huv' : u.castSucc ≠ v.castSucc := fun h => huv (Fin.castSucc_injective t h)
    exact Set.disjoint_left.1 (M.branchDisjoint _ _ huv') hxu
      (f.injective hEq ▸ hxv)
  · intro u x hx
    rcases hx with ⟨y, hy, rfl⟩
    obtain ⟨p, _, hpLen, hpSupport⟩ := M.branchRadius u.castSucc y hy
    refine ⟨p.map f.toHom, ?_, ?_⟩
    · simpa using hpLen
    · intro z hz
      simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, hpSupport w hw, rfl⟩
  · intro u v huv
    have huv' : u.castSucc ≠ v.castSucc :=
      fun h => huv.ne (Fin.castSucc_injective t h)
    have hcomplete :
        (SimpleGraph.completeGraph (Fin (t + 1))).Adj u.castSucc v.castSucc := by
      simpa [SimpleGraph.completeGraph_eq_top] using huv'
    obtain ⟨x, hx, y, hy, hxy⟩ := M.branchEdge _ _ hcomplete
    exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, f.toHom.map_adj hxy⟩

/-- A type copy used to keep the supplied order distinct from the canonical
order on `Fin m` while constructing ranks. -/
private structure OrderedCopy (m : ℕ) where
  val : Fin m
deriving Fintype

private def orderedCopyEquiv (m : ℕ) : OrderedCopy m ≃ Fin m where
  toFun := OrderedCopy.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/-- The rank permutation associated with a finite linear order. -/
private def rankPerm {m : ℕ} (ord : LinearOrder (Fin m)) : Equiv.Perm (Fin m) := by
  letI := ord
  letI : LinearOrder (OrderedCopy m) :=
    LinearOrder.lift' OrderedCopy.val fun x y h => by cases x; cases y; simp_all
  let e := Fintype.orderIsoFinOfCardEq (k := m) (OrderedCopy m) (by
    rw [Fintype.card_congr (orderedCopyEquiv m)]
    exact Fintype.card_fin m)
  exact (orderedCopyEquiv m).symm.trans e.symm.toEquiv

/-- Walk-based submitted weak reachability is contained in the catalog's
path-based weak reachability for the corresponding rank permutation. -/
private theorem wreach_subset_WReach {m : ℕ} (ord : LinearOrder (Fin m))
    (H : SimpleGraph (Fin m)) (r : ℕ) (v : Fin m) :
    letI := ord
    Lax5.NowhereDenseWcol.wreach H (rankPerm ord) r v ⊆ WReach H r v := by
  letI := ord
  intro u hu
  rcases hu with ⟨w, hwLen, hwMin⟩
  letI : LinearOrder (OrderedCopy m) :=
    LinearOrder.lift' OrderedCopy.val fun x y h => by cases x; cases y; simp_all
  let e := Fintype.orderIsoFinOfCardEq (k := m) (OrderedCopy m) (by
    rw [Fintype.card_congr (orderedCopyEquiv m)]
    exact Fintype.card_fin m)
  have huvRank := hwMin v w.start_mem_support
  change e.symm ⟨u⟩ ≤ e.symm ⟨v⟩ at huvRank
  have huv := e.symm.le_iff_le.mp huvRank
  change @LE.le (Fin m) ord.toLE u v at huv
  refine ⟨huv, ⟨w.toPath, w.toPath.property, ?_, ?_⟩⟩
  · exact (SimpleGraph.Walk.length_bypass_le w).trans hwLen
  · intro i hi0 hiLen
    have hmemPath : w.toPath.val.getVert i ∈ w.toPath.val.support :=
      w.toPath.val.getVert_mem_support i
    have hmemWalk : w.toPath.val.getVert i ∈ w.support :=
      w.support_toPath_subset hmemPath
    have hleRank := hwMin _ hmemWalk
    change e.symm ⟨u⟩ ≤ e.symm ⟨w.toPath.val.getVert i⟩ at hleRank
    have hle := e.symm.le_iff_le.mp hleRank
    change @LE.le (Fin m) ord.toLE u (w.toPath.val.getVert i) at hle
    have hne : u ≠ w.toPath.val.getVert i := by
      intro hEq
      have hiEq := (w.toPath.property.getVert_eq_end_iff
        (Nat.le_of_lt hiLen)).mp hEq.symm
      omega
    change @LT.lt (Fin m) ord.toLT u (w.toPath.val.getVert i)
    refine (ord.toPartialOrder.toPreorder.lt_iff_le_not_ge _ _).2 ⟨hle, ?_⟩
    intro hge
    exact hne (ord.toPartialOrder.le_antisymm _ _ hle hge)

/-- The submitted minimum over rank permutations is bounded by the catalog
weak coloring number for any fixed linear order. -/
private theorem submitted_wcol_le_catalog {m : ℕ} (ord : LinearOrder (Fin m))
    (H : SimpleGraph (Fin m)) (r : ℕ) :
    letI := ord
    Lax5.NowhereDenseWcol.wcol H r ≤
      Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.wcol H r := by
  letI := ord
  apply Nat.sInf_le
  refine ⟨rankPerm ord, fun v => ?_⟩
  calc
    (Lax5.NowhereDenseWcol.wreach H (rankPerm ord) r v).ncard
        ≤ (WReach H r v).ncard :=
      Set.ncard_le_ncard (wreach_subset_WReach ord H r v)
    _ ≤ Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.wcol H r := by
      unfold Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.wcol
      exact Finset.le_sup (f := fun x => (WReach H r x).ncard) (Finset.mem_univ v)

/--
---
conclusion: Lax5.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense
---
Nowhere dense classes have subpolynomial weak coloring numbers, uniformly
over graph copies contained in their members.

# Proof strategy

Close the submitted class under graph copies and transport its shallow-minor
exclusion to the catalog definition.  Apply the catalog proof, which combines
subpolynomial shallow-minor density with admissibility and weak-coloring-number
bounds.  Finally translate its linear order to the corresponding rank
permutation and use the submitted minimum over all permutations.

# Attribution

The source proof formalizes Theorem 3.4 of the sparsity lecture notes of
Pilipczuk, Pilipczuk, and Siebertz.
-/
theorem hasSubpolynomialWcol_of_nowhereDense
    (C : Lax5.GraphClasses.GraphClass)
    (hC : Lax5.NowhereDenseClasses.NowhereDense C) :
    Lax5.NowhereDenseWcol.HasSubpolynomialWcol C := by
  intro r ε hε
  obtain ⟨c, _, hc⟩ :=
    Lax5Proofs.Source.Catalog.SparsityLectures.NDSubpolynomialWcol.nd_subpolynomial_wcol
      (copyClosure C) (copyClosure_isNowhereDense C hC) r ε hε
  refine ⟨c, ?_⟩
  intro n G hCG m H hHG
  obtain ⟨ord, hord⟩ := hc H ⟨n, G, hCG, hHG⟩
  letI := ord
  calc
    (Lax5.NowhereDenseWcol.wcol H r : ℝ)
        ≤ (Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.wcol H r : ℝ) :=
      by exact_mod_cast submitted_wcol_le_catalog ord H r
    _ ≤ c * (m : ℝ) ^ ε := by simpa using hord

end

end Lax5Proofs.NowhereDenseWcol
