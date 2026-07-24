import Lax5.NowhereDenseWcol
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds

/-!
Elementary graph-theoretic bridges used by the radius-one neighborhood
complexity proof.  They are kept separate from the asymptotic assembly in
`Corollary6b` so the shallow-minor and weak-ordering bookkeeping can be
checked independently.
-/

namespace Lax5Proofs.NowhereDenseNeighborhoods

open scoped SimpleGraph
open Lax5.GraphClasses
open Lax5.NowhereDenseClasses
open Lax5.NowhereDenseWcol

/-- A (not necessarily induced) copy of `K_{t,t}` in `G`, represented by
injective maps for its two disjoint sides. -/
def HasBiclique {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ l r : Fin t → V,
    Function.Injective l ∧ Function.Injective r ∧
    Disjoint (Set.range l) (Set.range r) ∧
    ∀ i j, G.Adj (l i) (r j)

/-- A `K_{t,t}` subgraph contains `K_t` as a depth-one minor: pair the
`i`-th vertices on the two sides into a radius-one branch set. -/
theorem hasShallowMinor_top_of_hasBiclique {V : Type*}
    {G : SimpleGraph V} {t : ℕ} (h : HasBiclique G t) :
    HasShallowMinor G 1 (⊤ : SimpleGraph (Fin t)) := by
  rcases h with ⟨l, r, hl, hr, hlr, hadj⟩
  refine ⟨{
    branch := fun i => {l i, r i}
    center := l
    center_mem := fun i => by simp
    disjoint := ?_
    radius_le := ?_
    adj := ?_
  }⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxi hxj
    rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
    · exact hij (hl (hxi.symm.trans hxj))
    · exact Set.disjoint_left.1 hlr ⟨i, hxi.symm⟩ ⟨j, hxj.symm⟩
    · exact Set.disjoint_left.1 hlr ⟨j, hxj.symm⟩ ⟨i, hxi.symm⟩
    · exact hij (hr (hxi.symm.trans hxj))
  · intro i x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨SimpleGraph.Walk.nil, by simp, ?_⟩
      simp
    · refine ⟨SimpleGraph.Walk.cons (hadj i i) .nil, by simp, ?_⟩
      simp
  · intro i j hij
    refine ⟨l i, by simp, r j, by simp, hadj i j⟩

/-- Depth-one clique exclusion immediately gives a uniform excluded
biclique for every nowhere dense class. -/
theorem exists_forall_not_hasBiclique (C : GraphClass) (hC : NowhereDense C) :
    ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ¬ HasBiclique G t := by
  obtain ⟨t, ht⟩ := hC 1
  refine ⟨t, fun n G hG hKt => ?_⟩
  exact ht n G hG (hasShallowMinor_top_of_hasBiclique hKt)

/-- The minimum in the definition of `wcol` is attained. -/
theorem exists_ordering_wreach_le_wcol {n : ℕ} (G : SimpleGraph (Fin n))
    (r : ℕ) :
    ∃ π : Equiv.Perm (Fin n), ∀ v, (wreach G π r v).ncard ≤ wcol G r := by
  unfold wcol
  have hs : {k : ℕ | ∃ π : Equiv.Perm (Fin n),
      ∀ v, (wreach G π r v).ncard ≤ k}.Nonempty := by
    refine ⟨n, Equiv.refl _, fun v => ?_⟩
    simpa using Set.ncard_le_card (wreach G (Equiv.refl _) r v)
  exact Nat.sInf_mem hs

/-- At radius one, weak reachability consists exactly of the vertex itself
and its neighbors that occur no later in the ordering. -/
theorem mem_wreach_one_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (v u : Fin n) :
    u ∈ wreach G π 1 v ↔ u = v ∨ (G.Adj v u ∧ π u ≤ π v) := by
  constructor
  · rintro ⟨w, hwlen, hwmin⟩
    by_cases hzero : w.length = 0
    · exact Or.inl (SimpleGraph.Walk.eq_of_length_eq_zero hzero).symm
    · right
      have hone : w.length = 1 := by omega
      exact ⟨SimpleGraph.Walk.adj_of_length_eq_one hone,
        hwmin v w.start_mem_support⟩
  · rintro (rfl | ⟨hvu, huv⟩)
    · refine ⟨SimpleGraph.Walk.nil, by simp, ?_⟩
      simp
    · refine ⟨SimpleGraph.Walk.cons hvu .nil, by simp, ?_⟩
      intro y hy
      simp at hy
      rcases hy with rfl | rfl
      · exact huv
      · exact le_rfl

/-- A family whose member indexed by `u` contains only `u` and neighbors
of `u`.  Both open-neighborhood traces and radius-one weak-reachability
traces have this property. -/
def SelfOrAdjacentFamily {V : Type*} (G : SimpleGraph V)
    (Φ : V → Finset V) : Prop :=
  ∀ u x, x ∈ Φ u → x = u ∨ G.Adj u x

/-- Excluding `K_{t,t}` bounds the VC dimension of every self-or-adjacent
set family.  The deliberately coarse bound `3t` is enough downstream.

If a shattered set has a `t`-set `T` and another `2t` vertices `y`, use
the traces `T ∪ {y}`.  Their realizing vertices are distinct; at most
`t` lie in `T`, so `t` of them outside `T` form the other biclique side. -/
theorem vcDim_image_le_of_not_hasBiclique {V : Type*}
    [Fintype V] [LinearOrder V] (G : SimpleGraph V) (t : ℕ)
    (hKt : ¬ HasBiclique G t) (Φ : V → Finset V)
    (hΦ : SelfOrAdjacentFamily G Φ) :
    (Finset.univ.image Φ).vcDim ≤ 3 * t := by
  classical
  unfold Finset.vcDim
  apply Finset.sup_le
  intro s hs
  have hsh : (Finset.univ.image Φ).Shatters s :=
    Finset.mem_shatterer.1 hs
  by_contra hcard
  have hlarge : 3 * t < s.card := Nat.lt_of_not_ge hcard
  obtain ⟨T, hTs, hTcard⟩ :=
    Finset.exists_subset_card_eq (show t ≤ s.card by omega)
  have hdiff : 2 * t ≤ (s \ T).card := by
    rw [Finset.card_sdiff_of_subset hTs, hTcard]
    omega
  obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hdiff
  have hUs : U ⊆ s := hUsub.trans Finset.sdiff_subset
  have hUT : Disjoint U T :=
    Finset.disjoint_left.2 fun x hxU hxT =>
      (Finset.mem_sdiff.1 (hUsub hxU)).2 hxT
  let y : Fin (2 * t) → V := fun i => (U.orderIsoOfFin hUcard i).val
  have hyU (i : Fin (2 * t)) : y i ∈ U := (U.orderIsoOfFin hUcard i).property
  have hyinj : Function.Injective y := by
    intro i j hij
    exact (U.orderIsoOfFin hUcard).injective (Subtype.ext hij)
  have hyT (i : Fin (2 * t)) : y i ∉ T :=
    Finset.disjoint_left.1 hUT (hyU i)
  have hex (i : Fin (2 * t)) :
      ∃ u : V, s ∩ Φ u = insert (y i) T := by
    have hsub : insert (y i) T ⊆ s := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hUs (hyU i)
      · exact hTs hx
    obtain ⟨F, hF, htrace⟩ := hsh hsub
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hF
    exact ⟨u, htrace⟩
  let rep : Fin (2 * t) → V := fun i => Classical.choose (hex i)
  have hrep (i : Fin (2 * t)) :
      s ∩ Φ (rep i) = insert (y i) T := Classical.choose_spec (hex i)
  have hrepinj : Function.Injective rep := by
    intro i j hij
    have hins : insert (y i) T = insert (y j) T := by
      rw [← hrep i, ← hrep j, hij]
    have hyimem : y i ∈ insert (y j) T := by rw [← hins]; simp
    have hyij : y i = y j := by simpa [hyT i] using hyimem
    exact hyinj hyij
  let good : Finset (Fin (2 * t)) := Finset.univ.filter fun i => rep i ∉ T
  let bad : Finset (Fin (2 * t)) := Finset.univ.filter fun i => rep i ∈ T
  have hbad : bad.card ≤ t := by
    calc
      bad.card = (bad.image rep).card :=
        (Finset.card_image_of_injOn hrepinj.injOn).symm
      _ ≤ T.card := Finset.card_le_card <| by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact (Finset.mem_filter.1 hi).2
      _ = t := hTcard
  have hgood : t ≤ good.card := by
    have hsum : good.card + bad.card = 2 * t := by
      simpa [good, bad, add_comm] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin (2 * t))))
          (p := fun i => rep i ∉ T))
    omega
  obtain ⟨R, hRgood, hRcard⟩ := Finset.exists_subset_card_eq hgood
  let left : Fin t → V := fun i => (T.orderIsoOfFin hTcard i).val
  let right : Fin t → V := fun i => rep (R.orderIsoOfFin hRcard i).val
  apply hKt
  refine ⟨left, right, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (T.orderIsoOfFin hTcard).injective (Subtype.ext hij)
  · intro i j hij
    exact (R.orderIsoOfFin hRcard).injective
      (Subtype.ext (hrepinj hij))
  · rw [Set.disjoint_left]
    intro x hxL hxR
    obtain ⟨i, rfl⟩ := hxL
    obtain ⟨j, hj⟩ := hxR
    have hleftT : left i ∈ T := (T.orderIsoOfFin hTcard i).property
    have hjgood : (R.orderIsoOfFin hRcard j).val ∈ good :=
      hRgood (R.orderIsoOfFin hRcard j).property
    have hrightT : right j ∉ T := (Finset.mem_filter.1 hjgood).2
    exact hrightT (hj ▸ hleftT)
  · intro i j
    let q : Fin (2 * t) := (R.orderIsoOfFin hRcard j).val
    have hleftT : left i ∈ T := (T.orderIsoOfFin hTcard i).property
    have hleftS : left i ∈ s := hTs hleftT
    have hleftΦ : left i ∈ Φ (rep q) := by
      have : left i ∈ s ∩ Φ (rep q) := by
        rw [hrep q]
        exact Finset.mem_insert_of_mem hleftT
      exact (Finset.mem_inter.1 this).2
    have hqgood : q ∈ good := hRgood (R.orderIsoOfFin hRcard j).property
    have hrepT : rep q ∉ T := (Finset.mem_filter.1 hqgood).2
    rcases hΦ (rep q) (left i) hleftΦ with heq | hadj
    · exact (hrepT (heq ▸ hleftT)).elim
    · exact hadj.symm

/-- A Sauer–Shelah bound in a form convenient for families whose actual
ground set is a finset `Z` inside a larger finite type. -/
theorem card_le_mul_pow_of_vcDim {V : Type*} [Fintype V] [DecidableEq V]
    (family : Finset (Finset V)) (Z : Finset V) (d : ℕ)
    (hground : ∀ F ∈ family, F ⊆ Z) (hvc : family.vcDim ≤ d) :
    family.card ≤ (d + 1) * (Z.card + 1) ^ d := by
  classical
  calc
    family.card ≤ family.shatterer.card := Finset.card_le_card_shatterer family
    _ ≤ ((Finset.range (d + 1)).biUnion Z.powersetCard).card :=
      Finset.card_le_card <| by
        intro s hs
        have hsh := Finset.mem_shatterer.1 hs
        obtain ⟨F, hF, hsF⟩ := hsh.exists_superset
        rw [Finset.mem_biUnion]
        refine ⟨s.card, Finset.mem_range.2 ?_, ?_⟩
        · exact Nat.lt_succ_of_le (hsh.card_le_vcDim.trans hvc)
        · exact Finset.mem_powersetCard.2 ⟨hsF.trans (hground F hF), rfl⟩
    _ ≤ ∑ i ∈ Finset.range (d + 1), (Z.powersetCard i).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (d + 1), Z.card.choose i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.card_powersetCard i Z
    _ ≤ ∑ _i ∈ Finset.range (d + 1), (Z.card + 1) ^ d := by
      apply Finset.sum_le_sum
      intro i hi
      have hid : i ≤ d := by simpa using Finset.mem_range.1 hi
      calc
        Z.card.choose i ≤ Z.card ^ i := Nat.choose_le_pow _ _
        _ ≤ (Z.card + 1) ^ i := by gcongr <;> omega
        _ ≤ (Z.card + 1) ^ d := by gcongr <;> omega
    _ = (d + 1) * (Z.card + 1) ^ d := by simp

/-- Open-neighborhood traces on the finite ground set `Z`. -/
noncomputable def neighborTrace {V : Type*} (G : SimpleGraph V)
    (Z : Finset V) (u : V) : Finset V := by
  classical
  exact Z.filter (G.Adj u)

/-- Radius-one weak-reachability traces, written in their elementary
lower-neighborhood form. -/
noncomputable def lowerTrace {V : Type*} [LE V] (G : SimpleGraph V)
    (ord : V → V) (Z : Finset V) (u : V) : Finset V :=
  by classical exact Z.filter fun x => x = u ∨ (G.Adj u x ∧ ord x ≤ ord u)

@[simp] theorem mem_neighborTrace_iff {V : Type*} (G : SimpleGraph V)
    (Z : Finset V) (u x : V) :
    x ∈ neighborTrace G Z u ↔ x ∈ Z ∧ G.Adj u x := by
  classical
  simp [neighborTrace]

@[simp] theorem mem_lowerTrace_iff {V : Type*} [LinearOrder V]
    (G : SimpleGraph V) (ord : V → V) (Z : Finset V) (u x : V) :
    x ∈ lowerTrace G ord Z u ↔
      x ∈ Z ∧ (x = u ∨ (G.Adj u x ∧ ord x ≤ ord u)) := by
  classical
  simp only [lowerTrace, Finset.mem_filter]

theorem selfOrAdjacent_neighborTrace {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (Z : Finset V) :
    SelfOrAdjacentFamily G (neighborTrace G Z) := by
  classical
  intro u x hx
  exact Or.inr (mem_neighborTrace_iff G Z u x |>.1 hx).2

theorem selfOrAdjacent_lowerTrace {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (ord : V → V) (Z : Finset V) :
    SelfOrAdjacentFamily G (lowerTrace G ord Z) := by
  classical
  intro u x hx
  rcases (mem_lowerTrace_iff G ord Z u x).1 hx |>.2 with hxu | ⟨hux, -⟩
  · exact Or.inl hxu
  · exact Or.inr hux

/-- Polynomial coarse bound for open-neighborhood traces in a
`K_{t,t}`-free graph. -/
theorem card_neighborTraces_le {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (t : ℕ) (hKt : ¬ HasBiclique G t)
    (Z : Finset V) :
    (Finset.univ.image (neighborTrace G Z)).card ≤
      (3 * t + 1) * (Z.card + 1) ^ (3 * t) := by
  apply card_le_mul_pow_of_vcDim
    (family := Finset.univ.image (neighborTrace G Z)) (Z := Z) (d := 3 * t)
  · intro F hF
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hF
    intro x hx
    exact (mem_neighborTrace_iff G Z u x |>.1 hx).1
  · exact vcDim_image_le_of_not_hasBiclique G t hKt _
      (selfOrAdjacent_neighborTrace G Z)

/-- The same polynomial bound for lower-neighborhood (equivalently,
radius-one weak-reachability) traces. -/
theorem card_lowerTraces_le {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (t : ℕ) (hKt : ¬ HasBiclique G t)
    (ord : V → V) (Z : Finset V) :
    (Finset.univ.image (lowerTrace G ord Z)).card ≤
      (3 * t + 1) * (Z.card + 1) ^ (3 * t) := by
  apply card_le_mul_pow_of_vcDim
    (family := Finset.univ.image (lowerTrace G ord Z)) (Z := Z) (d := 3 * t)
  · intro F hF
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hF
    intro x hx
    exact (mem_lowerTrace_iff G ord Z u x |>.1 hx).1
  · exact vcDim_image_le_of_not_hasBiclique G t hKt _
      (selfOrAdjacent_lowerTrace G ord Z)

/-- On `Fin n`, `lowerTrace` with the rank permutation is exactly the
restriction of the submitted radius-one weak-reachability set. -/
theorem mem_lowerTrace_iff_mem_wreach_one {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (Z : Finset (Fin n)) (u x : Fin n) :
    x ∈ lowerTrace G π Z u ↔ x ∈ Z ∧ x ∈ wreach G π 1 u := by
  rw [mem_lowerTrace_iff, mem_wreach_one_iff]

/-- Every restricted lower trace is bounded by the weak reachability
number of the vertex in the same ordering. -/
theorem card_lowerTrace_le_wreach {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (Z : Finset (Fin n)) (u : Fin n) :
    (lowerTrace G π Z u).card ≤ (wreach G π 1 u).ncard := by
  simpa using Set.ncard_le_ncard (s := (lowerTrace G π Z u : Set (Fin n)))
    (t := wreach G π 1 u) fun x hx =>
      (mem_lowerTrace_iff_mem_wreach_one G π Z u x).1 hx |>.2

end Lax5Proofs.NowhereDenseNeighborhoods
