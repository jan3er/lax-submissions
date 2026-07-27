import Lax5.WeaklySparseDependent
import Lax5Proofs.NowhereDenseBridge
import Lax5Proofs.SubdividedBicliqueRamsey
import Lax5Proofs.CrossingTransduction
import Mathlib.Data.Fintype.Pigeonhole

/-!
Corollary 6a of DMMPT26 = Mählmann Lemma 13.7: every weakly sparse
monadically dependent graph class is nowhere dense.  This discharges the
open concept obligation
`Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent`.

Proof layout (thesis Ch. 13, with the forbidden-pattern endpoint replaced
by an honest transduction):

* Negate nowhere-denseness and cross the encoding bridge: the copy
  closure of the class is not nowhere dense in the catalog's
  shallow-minor sense, so by `isLocallyNowhereDense_iff_isNowhereDense`
  some radius `r` admits `r`-subdivided cliques of every order as
  subgraphs of members.
* `r = 0`: a subdivided clique of radius `0` is a clique and contains a
  large biclique, contradicting weak sparseness.
* `r ≥ 1`: subdivided cliques contain subdivided bicliques of half the
  order; Lemma 13.8 (`subdividedBiclique_ramsey`) turns those into
  either large bicliques (contradicting weak sparseness) or *induced*
  `r'`-subdivided bicliques with `1 ≤ r' ≤ r`.  A pigeonhole fixes a
  single `r'` occurring at unbounded orders, and the star-crossing
  transduction (`transduces_allGraphs_of_isIndContained_subdividedBiclique`)
  then transduces all graphs, contradicting monadic dependence.
-/

namespace Lax5Proofs.Corollary6a

open scoped SimpleGraph
open Lax5.GraphClasses Lax5.MonadicDependence
open Lax5Proofs.ShallowMinors
open Lax5Proofs.NowhereDenseBridge
open Lax5Proofs.SubdividedBicliqueRamsey
open Lax5Proofs.CrossingTransduction
open Lax5Proofs.Subdivision

/-! ### Encoding bridges -/

/-- The type-polymorphic closure of a submitted class under graph copies. -/
private def copyClosure (C : Lax5.GraphClasses.GraphClass) :
    Lax5Proofs.ShallowMinors.GraphClass :=
  fun {_} _ _ H =>
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧ H ⊑ G

/-- A submitted shallow-minor model of a clique yields a catalog one:
walks inside branch sets are replaced by their bypass paths. -/
private theorem isShallowMinor_of_shallowMinorModel {n t r : ℕ}
    {G : SimpleGraph (Fin n)}
    (M : Lax5.NowhereDenseClasses.ShallowMinorModel r
      (⊤ : SimpleGraph (Fin t)) G) :
    IsShallowMinor (SimpleGraph.completeGraph (Fin t)) G r := by
  refine ⟨{
    branchSet := M.branch
    center := M.center
    center_mem := M.center_mem
    branchDisjoint := M.disjoint
    branchRadius := ?_
    branchEdge := ?_ }⟩
  · intro v x hx
    obtain ⟨w, hlen, hsupp⟩ := M.radius_le v x hx
    exact ⟨w.bypass, w.bypass_isPath, w.length_bypass_le.trans hlen,
      fun y hy => hsupp y (w.support_bypass_subset hy)⟩
  · intro u v huv
    exact M.adj u v (by simpa using huv)

/-- Catalog nowhere-denseness of the copy closure transfers back to the
submitted shallow-minor formulation. -/
private theorem nowhereDense_of_isNowhereDense_copyClosure
    (C : Lax5.GraphClasses.GraphClass)
    (h : IsNowhereDense (copyClosure C)) :
    Lax5.NowhereDenseClasses.NowhereDense C := by
  intro r
  obtain ⟨t, ht⟩ := h r
  refine ⟨t + 1, ?_⟩
  intro n G hCG hM
  obtain ⟨M⟩ := hM
  exact ht G ⟨n, G, hCG, ⟨⟨SimpleGraph.Hom.id, fun _ _ hxy => hxy⟩⟩⟩
    (isShallowMinor_of_shallowMinorModel M)

/-! ### Pattern-graph containments

An `r`-subdivided biclique of order `⌊N/2⌋` sits inside the
`r`-subdivided clique of order `N`: left roots go to `{0, …, ⌊N/2⌋-1}`,
right roots to `{⌊N/2⌋, …, 2⌊N/2⌋-1}`, and each subdivision path to the
path of the corresponding ordered edge. -/

/-- Left-half embedding `Fin (N/2) ↪ Fin N`: `i ↦ i`. -/
private def leftFin (N : ℕ) (i : Fin (N / 2)) : Fin N :=
  ⟨i.val, lt_of_lt_of_le i.isLt (Nat.div_le_self N 2)⟩

/-- Right-half embedding `Fin (N/2) ↪ Fin N`: `j ↦ ⌊N/2⌋ + j`. -/
private def rightFin (N : ℕ) (j : Fin (N / 2)) : Fin N :=
  ⟨N / 2 + j.val, by
    have h1 : j.val < N / 2 := j.isLt
    have h2 : N / 2 * 2 ≤ N := Nat.div_mul_le_self N 2
    omega⟩

private lemma leftFin_lt_rightFin (N : ℕ) (i j : Fin (N / 2)) :
    (leftFin N i).val < (rightFin N j).val := by
  show i.val < N / 2 + j.val
  have := i.isLt; omega

private lemma leftFin_ne_rightFin (N : ℕ) (i j : Fin (N / 2)) :
    leftFin N i ≠ rightFin N j := fun h => by
  have h' : (leftFin N i).val = (rightFin N j).val := by rw [h]
  have hi := i.isLt
  simp only [leftFin, rightFin] at h'
  omega

private lemma leftFin_injective (N : ℕ) : Function.Injective (leftFin N) := by
  intro i j h
  have h' : (leftFin N i).val = (leftFin N j).val := congrArg Fin.val h
  exact Fin.ext h'

private lemma rightFin_injective (N : ℕ) : Function.Injective (rightFin N) :=
  fun i j h => Fin.ext (by
    have h' : N / 2 + i.val = N / 2 + j.val := congrArg Fin.val h
    omega)

/-- Vertex embedding `SubdividedBicliqueVert (N/2) r → SubdividedCliqueVert N r`. -/
private def bicliqueVertToClique (N r : ℕ) :
    SubdividedBicliqueVert (N / 2) r → SubdividedCliqueVert N r
  | .inl (.inl i) => .inl (leftFin N i)
  | .inl (.inr j) => .inl (rightFin N j)
  | .inr ⟨⟨i, j⟩, k⟩ =>
      .inr ⟨⟨(leftFin N i, rightFin N j), leftFin_lt_rightFin N i j⟩, k⟩

private lemma bicliqueVertToClique_injective (N r : ℕ) :
    Function.Injective (bicliqueVertToClique N r) := by
  intro u v heq
  rcases u with (iU | jU) | ⟨⟨iU, jU⟩, kU⟩ <;>
  rcases v with (iV | jV) | ⟨⟨iV, jV⟩, kV⟩ <;>
  dsimp only [bicliqueVertToClique] at heq
  · exact congrArg (fun x => (Sum.inl (Sum.inl x) : SubdividedBicliqueVert (N/2) r))
      (leftFin_injective N (Sum.inl.inj heq))
  · exact absurd (Sum.inl.inj heq) (leftFin_ne_rightFin N _ _)
  · cases heq
  · exact absurd (Sum.inl.inj heq).symm (leftFin_ne_rightFin N _ _)
  · exact congrArg (fun x => (Sum.inl (Sum.inr x) : SubdividedBicliqueVert (N/2) r))
      (rightFin_injective N (Sum.inl.inj heq))
  · cases heq
  · cases heq
  · cases heq
  · have h := Sum.inr.inj heq
    obtain ⟨hSub, hk⟩ := Prod.mk.inj h
    have hpair : (leftFin N iU, rightFin N jU) = (leftFin N iV, rightFin N jV) :=
      Subtype.ext_iff.mp hSub
    obtain ⟨hil, hir⟩ := Prod.mk.inj hpair
    have hi : iU = iV := leftFin_injective N hil
    have hj : jU = jV := rightFin_injective N hir
    subst hi; subst hj; subst hk; rfl

/-- Adjacency-preserving hom induced by `bicliqueVertToClique`. -/
private def bicliqueHomToClique (N r : ℕ) :
    subdividedBiclique (N / 2) r →g subdividedClique N r where
  toFun := bicliqueVertToClique N r
  map_rel' := by
    intro u v huv
    rw [subdividedBiclique, SimpleGraph.fromRel_adj] at huv
    rw [subdividedClique, SimpleGraph.fromRel_adj]
    obtain ⟨hne, hor⟩ := huv
    refine ⟨fun h => hne (bicliqueVertToClique_injective N r h), ?_⟩
    rcases u with (iU | jU) | ⟨⟨iU, jU⟩, kU⟩ <;>
      rcases v with (iV | jV) | ⟨⟨iV, jV⟩, kV⟩ <;>
      dsimp only [bicliqueVertToClique] at *
    · exact (hor.elim id id).elim
    · rcases hor with h | h
      · exact Or.inl h
      · exact h.elim
    · rcases hor with ⟨hii, hk⟩ | h
      · exact Or.inl (Or.inl ⟨by rw [hii], hk⟩)
      · exact h.elim
    · rcases hor with h | h
      · exact h.elim
      · exact Or.inr h
    · exact (hor.elim id id).elim
    · rcases hor with ⟨hjj, hk⟩ | h
      · exact Or.inl (Or.inr ⟨by rw [hjj], hk⟩)
      · exact h.elim
    · rcases hor with h | ⟨hii, hk⟩
      · exact h.elim
      · exact Or.inr (Or.inl ⟨by rw [hii], hk⟩)
    · rcases hor with h | ⟨hjj, hk⟩
      · exact h.elim
      · exact Or.inr (Or.inr ⟨by rw [hjj], hk⟩)
    · rcases hor with ⟨hij, hk⟩ | ⟨hij, hk⟩
      · refine Or.inl ⟨?_, hk⟩
        obtain ⟨hii, hjj⟩ := Prod.mk.inj hij
        apply Subtype.ext
        simp only [hii, hjj]
      · refine Or.inr ⟨?_, hk⟩
        obtain ⟨hii, hjj⟩ := Prod.mk.inj hij
        apply Subtype.ext
        simp only [hii, hjj]

/-- An `r`-subdivided biclique of order `⌊N/2⌋` is contained as a
subgraph in the `r`-subdivided clique of order `N`. -/
private lemma subdividedBiclique_isContained_subdividedClique (N r : ℕ) :
    (subdividedBiclique (N / 2) r).IsContained (subdividedClique N r) :=
  ⟨⟨bicliqueHomToClique N r, bicliqueVertToClique_injective N r⟩⟩

/-- Root embedding into the `0`-subdivided (= complete) clique. -/
private def bicliqueVertToCliqueZero (N : ℕ) :
    (Fin (N / 2) ⊕ Fin (N / 2)) → SubdividedCliqueVert N 0
  | .inl i => .inl (leftFin N i)
  | .inr j => .inl (rightFin N j)

private lemma bicliqueVertToCliqueZero_injective (N : ℕ) :
    Function.Injective (bicliqueVertToCliqueZero N) := by
  intro u v heq
  rcases u with iU | jU <;> rcases v with iV | jV <;>
      simp only [bicliqueVertToCliqueZero] at heq
  · exact congrArg Sum.inl (leftFin_injective N (Sum.inl.inj heq))
  · exact absurd (Sum.inl.inj heq) (leftFin_ne_rightFin N _ _)
  · exact absurd (Sum.inl.inj heq).symm (leftFin_ne_rightFin N _ _)
  · exact congrArg Sum.inr (rightFin_injective N (Sum.inl.inj heq))

private def bicliqueHomToCliqueZero (N : ℕ) :
    biclique (N / 2) →g subdividedClique N 0 where
  toFun := bicliqueVertToCliqueZero N
  map_rel' := by
    intro u v huv
    rcases u with iU | jU <;> rcases v with iV | jV
    · exact absurd huv (by simp [biclique, completeBipartiteGraph])
    · refine ⟨fun h => leftFin_ne_rightFin N _ _ (Sum.inl.inj h), ?_⟩
      exact Or.inl (by show (0 : ℕ) = 0; rfl)
    · refine ⟨fun h => (leftFin_ne_rightFin N _ _) (Sum.inl.inj h).symm, ?_⟩
      exact Or.inl (by show (0 : ℕ) = 0; rfl)
    · exact absurd huv (by simp [biclique, completeBipartiteGraph])

/-- A biclique of order `⌊N/2⌋` is contained as a subgraph in the
`0`-subdivided clique of order `N`. -/
private lemma biclique_isContained_subdividedClique_zero (N : ℕ) :
    (biclique (N / 2)).IsContained (subdividedClique N 0) :=
  ⟨⟨bicliqueHomToCliqueZero N, bicliqueVertToCliqueZero_injective N⟩⟩

/-- `biclique k ⊑ biclique m` whenever `k ≤ m`. -/
private lemma biclique_isContained_biclique_of_le {k m : ℕ} (h : k ≤ m) :
    (biclique k).IsContained (biclique m) := by
  refine ⟨?_⟩
  refine
    { toHom :=
        { toFun := fun v =>
            match v with
            | .inl i => .inl (Fin.castLE h i)
            | .inr j => .inr (Fin.castLE h j)
          map_rel' := by
            intro u v huv
            rcases u with iU | jU <;> rcases v with iV | jV <;>
              simp_all [biclique, completeBipartiteGraph] }
      injective' := ?_ }
  intro u v heq
  rcases u with iU | jU <;> rcases v with iV | jV
  · have h := Sum.inl.inj heq
    exact congrArg (fun x => (Sum.inl x : Fin k ⊕ Fin k))
      (Fin.ext (by simpa using congrArg (Fin.val : Fin m → ℕ) h))
  · cases heq
  · cases heq
  · have h := Sum.inr.inj heq
    exact congrArg (fun x => (Sum.inr x : Fin k ⊕ Fin k))
      (Fin.ext (by simpa using congrArg (Fin.val : Fin m → ℕ) h))

/-- `subdividedBiclique k r ⊴ subdividedBiclique m r` whenever `k ≤ m`,
via `Fin.castLE` on each coordinate. -/
private lemma subdividedBiclique_isIndContained_of_le {k m r : ℕ} (h : k ≤ m) :
    (subdividedBiclique k r).IsIndContained (subdividedBiclique m r) := by
  refine ⟨{
    toFun := fun v => match v with
      | .inl (.inl i) => .inl (.inl (Fin.castLE h i))
      | .inl (.inr j) => .inl (.inr (Fin.castLE h j))
      | .inr ⟨⟨i, j⟩, k'⟩ => .inr ⟨⟨Fin.castLE h i, Fin.castLE h j⟩, k'⟩
    inj' := by
      intro u v heq
      rcases u with (iU | jU) | ⟨⟨iU, jU⟩, kU⟩ <;>
        rcases v with (iV | jV) | ⟨⟨iV, jV⟩, kV⟩ <;>
        simp_all [Fin.ext_iff]
    map_rel_iff' := by
      intro u v
      simp only [subdividedBiclique, SimpleGraph.fromRel_adj]
      rcases u with (iU | jU) | ⟨⟨iU, jU⟩, kU⟩ <;>
        rcases v with (iV | jV) | ⟨⟨iV, jV⟩, kV⟩ <;>
        simp_all [Fin.ext_iff, Prod.ext_iff]
  }⟩

/-! ### Corollary 6a -/

/--
---
conclusion: Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent
assumptions:
  - Lax14.MulticolorRamsey.exists_monochromatic_set
  - Lax14.TupleRamsey.exists_orderType_homogeneous
---
Corollary 6a of DMMPT26 (Mählmann Lemma 13.7): every weakly sparse
monadically dependent graph class is nowhere dense.  This proves the
statement of the concept axiom
`Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent`.

# Proof strategy

As sketched in the module docstring.  The two Ramsey inputs are assumed
from the `finite-ramsey` submission rather than reproved: the
monochromatic-subset extraction inside the nowhere-dense bridge is the
multicolour Ramsey statement, and the order-type homogeneity behind
Lemma 13.8 is the tuple Ramsey statement. -/
theorem nowhereDense_of_weaklySparse_of_monadicallyDependent
    (C : Lax5.GraphClasses.GraphClass) (hs : WeaklySparse C)
    (hd : MonadicallyDependent C) :
    Lax5.NowhereDenseClasses.NowhereDense C := by
  obtain ⟨kWS, hWS⟩ := hs
  by_contra hNotND
  -- Cross the encoding bridge: the copy closure is not locally nowhere
  -- dense, so some radius admits subdivided cliques of every order.
  have hNotLoc : ¬ IsLocallyNowhereDense (copyClosure C) := fun h =>
    hNotND (nowhereDense_of_isNowhereDense_copyClosure C
      ((isLocallyNowhereDense_iff_isNowhereDense _).1 h))
  have hBad : ∃ r : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      C n G ∧ (subdividedClique N r).IsContained G := by
    classical
    by_contra hGood
    apply hNotLoc
    intro r
    by_contra hNoN
    apply hGood
    refine ⟨r, ?_⟩
    intro N
    by_contra hNoWitness
    apply hNoN
    refine ⟨N, ?_⟩
    intro V _ _ H hCH hContained
    obtain ⟨n, G, hCG, hHG⟩ := hCH
    exact hNoWitness ⟨n, G, hCG, hContained.trans hHG⟩
  obtain ⟨r, hr⟩ := hBad
  rcases Nat.eq_zero_or_pos r with hr0 | hrPos
  -- `r = 0`: the subdivided clique is a clique; extract a biclique and
  -- contradict weak sparseness.
  · subst hr0
    obtain ⟨n, G, hCG, hContained⟩ := hr (2 * kWS + 1)
    have hContBiclique : (biclique ((2 * kWS + 1) / 2)).IsContained G :=
      (biclique_isContained_subdividedClique_zero (2 * kWS + 1)).trans hContained
    have hDiv : (2 * kWS + 1) / 2 = kWS := by omega
    rw [hDiv] at hContBiclique
    exact hWS n G hCG hContBiclique
  -- `r ≥ 1`: subdivided bicliques of every order occur as subgraphs.
  have hBiclique : ∀ m : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      C n G ∧ (subdividedBiclique m r).IsContained G := by
    intro m
    obtain ⟨n, G, hCG, hContained⟩ := hr (2 * m + 1)
    refine ⟨n, G, hCG, ?_⟩
    have hDiv : (2 * m + 1) / 2 = m := by omega
    have step := subdividedBiclique_isContained_subdividedClique (2 * m + 1) r
    rw [hDiv] at step
    exact step.trans hContained
  -- Lemma 13.8: bicliques or induced `r'`-subdivided bicliques.
  obtain ⟨U, _hUmono, hUunb, hRamsey⟩ := subdividedBiclique_ramsey r
  have hAlt : ∀ m : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
      ((biclique (U m)).IsContained G ∨
        ∃ r' : ℕ, 1 ≤ r' ∧ r' ≤ r ∧
          (subdividedBiclique (U m) r').IsIndContained G) := by
    intro m
    obtain ⟨n, G, hCG, hContained⟩ := hBiclique m
    exact ⟨n, G, hCG, hRamsey G m hContained⟩
  by_cases hBranch1 : ∀ M : ℕ, ∃ m : ℕ, M ≤ U m ∧
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
        (biclique (U m)).IsContained G
  -- Biclique branch at unbounded orders: weak-sparseness contradiction.
  · obtain ⟨m, hUm, n, G, hCG, hContained⟩ := hBranch1 kWS
    exact hWS n G hCG
      ((biclique_isContained_biclique_of_le hUm).trans hContained)
  -- Induced branch at unbounded orders: pigeonhole a single `r'`.
  · push Not at hBranch1
    obtain ⟨M₀, hM₀⟩ := hBranch1
    have hIndUnb : ∃ r' : ℕ, 1 ≤ r' ∧ r' ≤ r ∧ ∀ m : ℕ,
        ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
          ∃ k : ℕ, m ≤ k ∧ (subdividedBiclique k r').IsIndContained G := by
      classical
      have step : ∀ M : ℕ, ∃ (r' : Fin r) (m : ℕ), M ≤ U m ∧
          ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
            (subdividedBiclique (U m) (r'.val + 1)).IsIndContained G := by
        intro M
        obtain ⟨m, hm⟩ := hUunb (max M M₀)
        have hmM : M ≤ U m := (le_max_left _ _).trans hm
        have hmM₀ : M₀ ≤ U m := (le_max_right _ _).trans hm
        obtain ⟨n, G, hCG, hAltCase⟩ := hAlt m
        rcases hAltCase with hbc | ⟨r', hr'1, hr'r, hIC⟩
        · exact ((hM₀ m hmM₀ n G hCG).false hbc.some).elim
        · refine ⟨⟨r' - 1, by omega⟩, m, hmM, n, G, hCG, ?_⟩
          have hplus : r' - 1 + 1 = r' := by omega
          rw [hplus]; exact hIC
      choose rChoice mChoice hChoice using step
      obtain ⟨r₀, hr₀inf⟩ := Finite.exists_infinite_fiber rChoice
      have hr₀lt := r₀.isLt
      refine ⟨r₀.val + 1, by omega, by omega, ?_⟩
      intro m
      have hSetInf : (rChoice ⁻¹' {r₀}).Infinite :=
        Set.infinite_coe_iff.mp hr₀inf
      obtain ⟨M, hMmem, hMlt⟩ := hSetInf.exists_gt m
      have hMeq : rChoice M = r₀ := hMmem
      obtain ⟨hMbd, n, G, hCG, hICM⟩ := hChoice M
      exact ⟨n, G, hCG, U (mChoice M), hMlt.le.trans hMbd, hMeq ▸ hICM⟩
    obtain ⟨r', hr'1, _hr'r, hInd⟩ := hIndUnb
    -- The star-crossing transduction contradicts monadic dependence.
    apply hd
    apply transduces_allGraphs_of_isIndContained_subdividedBiclique hr'1
    intro m
    obtain ⟨n, G, hCG, k, hmk, hIC⟩ := hInd m
    exact ⟨n, G, hCG, (subdividedBiclique_isIndContained_of_le hmk).trans hIC⟩

end Lax5Proofs.Corollary6a
