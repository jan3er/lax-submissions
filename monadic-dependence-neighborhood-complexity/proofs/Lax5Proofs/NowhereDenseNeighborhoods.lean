import Lax5.NowhereDenseWcol
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
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

/-! ## Local separators from a weak coloring order -/

/-- The finset version of a submitted weak-reachability set. -/
noncomputable def weakReachFinset {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (r : ℕ) (u : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x => x ∈ wreach G π r u

@[simp] theorem mem_weakReachFinset_iff {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (u x : Fin n) :
    x ∈ weakReachFinset G π r u ↔ x ∈ wreach G π r u := by
  classical
  simp [weakReachFinset]

theorem card_weakReachFinset {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (r : ℕ) (u : Fin n) :
    (weakReachFinset G π r u).card = (wreach G π r u).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp

/-- Every vertex weakly reaches itself, at every radius. -/
theorem mem_wreach_self {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (r : ℕ) (u : Fin n) :
    u ∈ wreach G π r u := by
  refine ⟨SimpleGraph.Walk.nil, by simp, ?_⟩
  simp

theorem wreach_mono_radius {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) {r s : ℕ} (hrs : r ≤ s) (u : Fin n) :
    wreach G π r u ⊆ wreach G π s u := by
  rintro x ⟨w, hw, hmin⟩
  exact ⟨w, hw.trans hrs, hmin⟩

/-- The witness ground set used in the radius-one counting argument:
all vertices weakly one-reachable from a vertex of `A`. -/
noncomputable def witnessGround {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (A : Finset (Fin n)) : Finset (Fin n) :=
  A.biUnion (weakReachFinset G π 1)

@[simp] theorem mem_witnessGround_iff {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (x : Fin n) :
    x ∈ witnessGround G π A ↔
      ∃ a ∈ A, x ∈ wreach G π 1 a := by
  classical
  simp [witnessGround]

theorem subset_witnessGround {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (A : Finset (Fin n)) :
    A ⊆ witnessGround G π A := by
  intro a ha
  exact (mem_witnessGround_iff G π A a).2
    ⟨a, ha, mem_wreach_self G π 1 a⟩

theorem card_witnessGround_le {n d : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (hπ : ∀ u, (wreach G π 1 u).ncard ≤ d) :
    (witnessGround G π A).card ≤ A.card * d := by
  classical
  calc
    (witnessGround G π A).card
        ≤ ∑ a ∈ A, (weakReachFinset G π 1 a).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, d := by
      apply Finset.sum_le_sum
      intro a ha
      simpa [card_weakReachFinset] using hπ a
    _ = A.card * d := by simp

/-- The local separator at `u`: the part of the witness ground set weakly
one-reachable from `u`. -/
noncomputable def localSeparator {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (u : Fin n) :
    Finset (Fin n) :=
  lowerTrace G π (witnessGround G π A) u

@[simp] theorem mem_localSeparator_iff {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (u x : Fin n) :
    x ∈ localSeparator G π A u ↔
      x ∈ witnessGround G π A ∧ x ∈ wreach G π 1 u := by
  exact mem_lowerTrace_iff_mem_wreach_one G π _ u x

theorem card_localSeparator_le {n d : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (hπ : ∀ u, (wreach G π 1 u).ncard ≤ d) (u : Fin n) :
    (localSeparator G π A u).card ≤ d := by
  exact (card_lowerTrace_le_wreach G π _ u).trans (hπ u)

/-- Every edge from `u` to the target `A` meets the local separator at
one of its endpoints.  This is the radius-one separator claim. -/
theorem adjacent_target_meets_localSeparator {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (u a : Fin n) (ha : a ∈ A) (hua : G.Adj u a) :
    u ∈ localSeparator G π A u ∨ a ∈ localSeparator G π A u := by
  by_cases huaOrd : π u ≤ π a
  · left
    rw [mem_localSeparator_iff]
    refine ⟨?_, mem_wreach_self G π 1 u⟩
    exact (mem_witnessGround_iff G π A u).2
      ⟨a, ha, (mem_wreach_one_iff G π a u).2
        (Or.inr ⟨hua.symm, huaOrd⟩)⟩
  · right
    rw [mem_localSeparator_iff]
    refine ⟨subset_witnessGround G π A ha, ?_⟩
    exact (mem_wreach_one_iff G π u a).2
      (Or.inr ⟨hua, le_of_not_ge huaOrd⟩)

/-- Outside the witness ground set, the open-neighborhood trace on `A` is
determined by the local separator and the open-neighborhood trace on that
separator. -/
theorem neighborTrace_eq_of_outside_of_local_data_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (u v : Fin n)
    (hu : u ∉ witnessGround G π A) (hv : v ∉ witnessGround G π A)
    (hsep : localSeparator G π A u = localSeparator G π A v)
    (hprofile : neighborTrace G (localSeparator G π A u) u =
      neighborTrace G (localSeparator G π A u) v) :
    neighborTrace G A u = neighborTrace G A v := by
  classical
  ext a
  simp only [mem_neighborTrace_iff]
  constructor
  · rintro ⟨ha, hua⟩
    have huSep : u ∉ localSeparator G π A u := fun hu' =>
      hu ((mem_localSeparator_iff G π A u u).1 hu').1
    have haSep : a ∈ localSeparator G π A u :=
      (adjacent_target_meets_localSeparator G π A u a ha hua).resolve_left
        huSep
    have haProf : a ∈ neighborTrace G (localSeparator G π A u) u :=
      (mem_neighborTrace_iff G _ u a).2 ⟨haSep, hua⟩
    have haProf' : a ∈ neighborTrace G (localSeparator G π A u) v := by
      rw [← hprofile]
      exact haProf
    have haProf'' : a ∈ neighborTrace G (localSeparator G π A v) v := by
      rwa [← hsep]
    exact ⟨ha, (mem_neighborTrace_iff G _ v a).1 haProf'' |>.2⟩
  · rintro ⟨ha, hva⟩
    have hvSep : v ∉ localSeparator G π A v := fun hv' =>
      hv ((mem_localSeparator_iff G π A v v).1 hv').1
    have haSep : a ∈ localSeparator G π A v :=
      (adjacent_target_meets_localSeparator G π A v a ha hva).resolve_left
        hvSep
    have haProf : a ∈ neighborTrace G (localSeparator G π A u) v := by
      rw [hsep]
      exact (mem_neighborTrace_iff G _ v a).2 ⟨haSep, hva⟩
    have haProf' : a ∈ neighborTrace G (localSeparator G π A u) u := by
      rw [hprofile]
      exact haProf
    exact ⟨ha, (mem_neighborTrace_iff G _ u a).1 haProf' |>.2⟩

/-- Two vertices weakly one-reachable from a common vertex are weakly
two-reachable from the later one.  This is the elementary path-concatenation
behind localization of the separator family. -/
theorem mem_wreach_two_of_common_one {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (u b x : Fin n) (hx : x ∈ wreach G π 1 u)
    (hb : b ∈ wreach G π 1 u) (hxb : π x ≤ π b) :
    x ∈ wreach G π 2 b := by
  rw [mem_wreach_one_iff] at hx hb
  rcases hx with rfl | ⟨hux, hxu⟩
  · rcases hb with rfl | ⟨hub, -⟩
    · exact mem_wreach_self G π 2 b
    · refine ⟨SimpleGraph.Walk.cons hub.symm .nil, by simp, ?_⟩
      intro y hy
      simp at hy
      rcases hy with rfl | rfl
      · exact hxb
      · exact le_rfl
  · rcases hb with rfl | ⟨hub, -⟩
    · refine ⟨SimpleGraph.Walk.cons hux .nil, by simp, ?_⟩
      intro y hy
      simp at hy
      rcases hy with rfl | rfl
      · exact hxu
      · exact le_rfl
    · refine ⟨SimpleGraph.Walk.cons hub.symm
          (SimpleGraph.Walk.cons hux .nil), by simp, ?_⟩
      intro y hy
      simp at hy
      rcases hy with rfl | rfl | rfl
      · exact hxb
      · exact hxu
      · exact le_rfl

/-- If `b` is a latest vertex of a nonempty local separator, that separator
is contained in the weak radius-two set of `b`. -/
theorem localSeparator_subset_wreach_two {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (u b : Fin n)
    (hb : b ∈ localSeparator G π A u)
    (hbmax : ∀ x ∈ localSeparator G π A u, π x ≤ π b) :
    localSeparator G π A u ⊆ weakReachFinset G π 2 b := by
  intro x hx
  rw [mem_weakReachFinset_iff]
  exact mem_wreach_two_of_common_one G π u b x
    ((mem_localSeparator_iff G π A u x).1 hx).2
    ((mem_localSeparator_iff G π A u b).1 hb).2 (hbmax x hx)

/-- Once a separator lies in a localized ground set `Z`, restricting the
lower trace to `Z` recovers the same separator. -/
theorem lowerTrace_eq_localSeparator_of_subset {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A Z : Finset (Fin n)) (u : Fin n)
    (hZ : localSeparator G π A u ⊆ Z)
    (hZW : Z ⊆ witnessGround G π A) :
    lowerTrace G π Z u = localSeparator G π A u := by
  ext x
  rw [mem_lowerTrace_iff_mem_wreach_one, mem_localSeparator_iff]
  constructor
  · rintro ⟨hxZ, hxW⟩
    exact ⟨hZW hxZ, hxW⟩
  · rintro ⟨hxB, hxW⟩
    exact ⟨hZ ((mem_localSeparator_iff G π A u x).2 ⟨hxB, hxW⟩), hxW⟩

/-- Every nonempty local separator has an anchor in the witness ground set
whose radius-two weak-reachability set contains the separator. -/
theorem exists_anchor_localSeparator {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (u : Fin n)
    (hne : (localSeparator G π A u).Nonempty) :
    ∃ b ∈ witnessGround G π A,
      localSeparator G π A u ⊆ weakReachFinset G π 2 b := by
  obtain ⟨b, hb, hbmax⟩ :=
    Finset.exists_max_image (localSeparator G π A u) π hne
  exact ⟨b, (mem_localSeparator_iff G π A u b).1 hb |>.1,
    localSeparator_subset_wreach_two G π A u b hb hbmax⟩

/-- Anchoring realizes each nonempty separator as a lower trace on a ground
set of size bounded by the radius-two weak coloring number. -/
theorem exists_anchor_lowerTrace_eq_localSeparator {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (u : Fin n)
    (hne : (localSeparator G π A u).Nonempty) :
    ∃ b ∈ witnessGround G π A,
      lowerTrace G π
        (witnessGround G π A ∩ weakReachFinset G π 2 b) u =
          localSeparator G π A u := by
  obtain ⟨b, hbB, hb⟩ := exists_anchor_localSeparator G π A u hne
  refine ⟨b, hbB, lowerTrace_eq_localSeparator_of_subset G π A _ u ?_ ?_⟩
  · exact fun x hx => Finset.mem_inter.2
      ⟨(mem_localSeparator_iff G π A u x).1 hx |>.1, hb hx⟩
  · exact Finset.inter_subset_left

theorem card_anchorGround_le {n d : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (hπ : ∀ u, (wreach G π 2 u).ncard ≤ d)
    (b : Fin n) :
    (witnessGround G π A ∩ weakReachFinset G π 2 b).card ≤ d := by
  calc
    (witnessGround G π A ∩ weakReachFinset G π 2 b).card
        ≤ (weakReachFinset G π 2 b).card :=
      Finset.card_le_card Finset.inter_subset_right
    _ = (wreach G π 2 b).ncard := card_weakReachFinset G π 2 b
    _ ≤ d := hπ b

/-- The coarse Sauer--Shelah polynomial used throughout the counting
argument. -/
def tracePolynomial (t d : ℕ) : ℕ :=
  (3 * t + 1) * (d + 1) ^ (3 * t)

theorem tracePolynomial_mono_right (t : ℕ) {d e : ℕ} (hde : d ≤ e) :
    tracePolynomial t d ≤ tracePolynomial t e := by
  unfold tracePolynomial
  gcongr

/-- The realized local separators. -/
noncomputable def localSeparatorFamily {n : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.image (localSeparator G π A)

/-- Local separators have only almost linearly many possible values when
radius-two weak reachability is bounded.  The empty separator contributes
one value; every nonempty separator is anchored at a vertex of the witness
ground, and Sauer--Shelah counts its possible localized lower traces. -/
theorem card_localSeparatorFamily_le {n d t : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (hKt : ¬ HasBiclique G t)
    (hπ : ∀ u, (wreach G π 2 u).ncard ≤ d) :
    (localSeparatorFamily G π A).card ≤
      1 + (witnessGround G π A).card * tracePolynomial t d := by
  classical
  let B := witnessGround G π A
  let localizedFamily : Fin n → Finset (Finset (Fin n)) := fun b =>
    Finset.univ.image
      (lowerTrace G π (B ∩ weakReachFinset G π 2 b))
  have hsubset : localSeparatorFamily G π A ⊆
      insert ∅ (B.biUnion localizedFamily) := by
    intro X hX
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hX
    by_cases hne : (localSeparator G π A u).Nonempty
    · obtain ⟨b, hbB, hbEq⟩ :=
        exists_anchor_lowerTrace_eq_localSeparator G π A u hne
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_biUnion]
      refine ⟨b, hbB, Finset.mem_image.2 ⟨u, Finset.mem_univ _, ?_⟩⟩
      simpa [B, localizedFamily] using hbEq
    · have hempty : localSeparator G π A u = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
      simp [hempty]
  calc
    (localSeparatorFamily G π A).card
        ≤ (insert ∅ (B.biUnion localizedFamily)).card :=
      Finset.card_le_card hsubset
    _ ≤ 1 + (B.biUnion localizedFamily).card := by
      simpa [Nat.add_comm] using
        (Finset.card_insert_le (∅ : Finset (Fin n))
          (B.biUnion localizedFamily))
    _ ≤ 1 + ∑ b ∈ B, (localizedFamily b).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ ≤ 1 + ∑ _b ∈ B, tracePolynomial t d := by
      gcongr with b hb
      calc
        (localizedFamily b).card
            ≤ tracePolynomial t
                (B ∩ weakReachFinset G π 2 b).card := by
          simpa [localizedFamily, tracePolynomial] using
            card_lowerTraces_le G t hKt π
              (B ∩ weakReachFinset G π 2 b)
        _ ≤ tracePolynomial t d :=
          tracePolynomial_mono_right t (by
            simpa [B] using card_anchorGround_le G π A hπ b)
    _ = 1 + B.card * tracePolynomial t d := by simp
    _ = 1 + (witnessGround G π A).card * tracePolynomial t d := by rfl

/-- If equality of `g`-values forces equality of `f`-values on a finite
domain, the image of `f` is no larger than the image of `g`. -/
theorem card_image_le_card_image_of_eq_imp_eq
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ x ∈ s, ∀ y ∈ s, g x = g y → f x = f y) :
    (s.image f).card ≤ (s.image g).card := by
  classical
  by_cases hs : s.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.1 hs]
  have hex (z : β) (hz : z ∈ s.image f) :
      ∃ x ∈ s, f x = z := by
    simpa [eq_comm] using Finset.mem_image.1 hz
  let rep : β → α := fun z => if hz : z ∈ s.image f then
    Classical.choose (hex z hz) else hs.choose
  have hrep_mem (z : β) (hz : z ∈ s.image f) : rep z ∈ s := by
    simp only [rep, dif_pos hz]
    exact (Classical.choose_spec (hex z hz)).1
  have hrep_eq (z : β) (hz : z ∈ s.image f) : f (rep z) = z := by
    simp only [rep, dif_pos hz]
    exact (Classical.choose_spec (hex z hz)).2
  apply Finset.card_le_card_of_injOn (fun z => g (rep z))
  · intro z hz
    exact Finset.mem_image.2 ⟨rep z, hrep_mem z hz, rfl⟩
  · intro z hz w hw hzw
    rw [← hrep_eq z hz, ← hrep_eq w hw]
    exact h (rep z) (hrep_mem z hz) (rep w) (hrep_mem w hw) hzw

/-- The radius-one counting theorem for one fixed weak coloring order.
The bound is deliberately coarse: its only downstream role is to be a fixed
polynomial in the weak radius-two bound `d`, times `|A|`. -/
theorem card_neighborTraceFamily_le_of_wreach {n d t : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (hKt : ¬ HasBiclique G t)
    (hπ : ∀ u, (wreach G π 2 u).ncard ≤ d) :
    (Finset.univ.image (neighborTrace G A)).card ≤
      A.card * d +
        (1 + A.card * d * tracePolynomial t d) * tracePolynomial t d := by
  classical
  let B := witnessGround G π A
  let outside : Finset (Fin n) := Finset.univ \ B
  let sep : Fin n → Finset (Fin n) := localSeparator G π A
  let key : Fin n → Finset (Fin n) × Finset (Fin n) := fun u =>
    (sep u, neighborTrace G (sep u) u)
  let profileKeys : Finset (Fin n) →
      Finset (Finset (Fin n) × Finset (Fin n)) := fun X =>
    Finset.univ.image fun u => (X, neighborTrace G X u)
  have hout : (outside.image (neighborTrace G A)).card ≤
      (outside.image key).card := by
    apply card_image_le_card_image_of_eq_imp_eq outside
    intro u hu v hv huv
    have huB : u ∉ B := (Finset.mem_sdiff.1 hu).2
    have hvB : v ∉ B := (Finset.mem_sdiff.1 hv).2
    have hsep : sep u = sep v := congrArg Prod.fst huv
    have hprofOwn : neighborTrace G (sep u) u =
        neighborTrace G (sep v) v := congrArg Prod.snd huv
    apply neighborTrace_eq_of_outside_of_local_data_eq G π A u v
      (by simpa [B] using huB) (by simpa [B] using hvB)
      (by simpa [sep] using hsep)
    simpa [sep, hsep] using hprofOwn
  have hkeySubset : outside.image key ⊆
      (localSeparatorFamily G π A).biUnion profileKeys := by
    intro K hK
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hK
    rw [Finset.mem_biUnion]
    refine ⟨sep u, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨u, Finset.mem_univ _, by simp [sep]⟩
    · exact Finset.mem_image.2 ⟨u, Finset.mem_univ _, by simp [key]⟩
  have hprofile (X : Finset (Fin n))
      (hX : X ∈ localSeparatorFamily G π A) :
      (profileKeys X).card ≤ tracePolynomial t d := by
    have hcardX : X.card ≤ d := by
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hX
      exact card_localSeparator_le G π A (fun u =>
        (Set.ncard_mono (wreach_mono_radius G π (by omega) u)).trans
          (hπ u)) u
    have hkeys : profileKeys X =
        (Finset.univ.image (neighborTrace G X)).image
          (fun p => (X, p)) := by
      ext K
      simp [profileKeys]
    calc
      (profileKeys X).card
          = ((Finset.univ.image (neighborTrace G X)).image
              (fun p => (X, p))).card := congrArg Finset.card hkeys
      _ = (Finset.univ.image (neighborTrace G X)).card :=
        Finset.card_image_of_injective _
          (fun _ _ h => congrArg Prod.snd h)
      _ ≤ tracePolynomial t X.card := by
        simpa [tracePolynomial] using card_neighborTraces_le G t hKt X
      _ ≤ tracePolynomial t d := tracePolynomial_mono_right t hcardX
  have hkeyCard : (outside.image key).card ≤
      (localSeparatorFamily G π A).card * tracePolynomial t d := by
    calc
      (outside.image key).card
          ≤ ((localSeparatorFamily G π A).biUnion profileKeys).card :=
        Finset.card_le_card hkeySubset
      _ ≤ ∑ X ∈ localSeparatorFamily G π A, (profileKeys X).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _X ∈ localSeparatorFamily G π A, tracePolynomial t d := by
        exact Finset.sum_le_sum fun X hX => hprofile X hX
      _ = (localSeparatorFamily G π A).card * tracePolynomial t d := by simp
  have hsplit : Finset.univ = B ∪ outside := by
    simp [outside]
  calc
    (Finset.univ.image (neighborTrace G A)).card
        = ((B.image (neighborTrace G A)) ∪
            (outside.image (neighborTrace G A))).card := by
      rw [← Finset.image_union, ← hsplit]
    _ ≤ (B.image (neighborTrace G A)).card +
          (outside.image (neighborTrace G A)).card :=
      Finset.card_union_le _ _
    _ ≤ B.card + (localSeparatorFamily G π A).card *
          tracePolynomial t d := by
      gcongr
      · exact Finset.card_image_le
      · exact hout.trans hkeyCard
    _ ≤ A.card * d +
          (1 + A.card * d * tracePolynomial t d) * tracePolynomial t d := by
      have hB : B.card ≤ A.card * d := by
        simpa [B] using card_witnessGround_le G π A (fun u =>
          (Set.ncard_mono (wreach_mono_radius G π (by omega) u)).trans (hπ u))
      have hSep : (localSeparatorFamily G π A).card ≤
          1 + B.card * tracePolynomial t d := by
        simpa [B] using card_localSeparatorFamily_le G π A hKt hπ
      calc
        B.card + (localSeparatorFamily G π A).card * tracePolynomial t d
            ≤ B.card + (1 + B.card * tracePolynomial t d) *
                tracePolynomial t d := by gcongr
        _ ≤ A.card * d +
              (1 + A.card * d * tracePolynomial t d) *
                tracePolynomial t d := by gcongr

/-- The polynomial factor in the fixed-order neighborhood bound. -/
def orderCountingPolynomial (t d : ℕ) : ℕ :=
  d + tracePolynomial t d + d * tracePolynomial t d ^ 2

/-- A single monomial upper bound for the fixed-order polynomial. -/
theorem orderCountingPolynomial_le (t d : ℕ) :
    orderCountingPolynomial t d ≤
      (1 + (3 * t + 1) + (3 * t + 1) ^ 2) *
        (d + 1) ^ (6 * t + 1) := by
  let C := 3 * t + 1
  let x := d + 1
  have hx : 1 ≤ x := by simp [x]
  have hd : d ≤ x := by simp [x]
  have hD : 3 * t ≤ 6 * t + 1 := by omega
  have h2D : 2 * (3 * t) + 1 = 6 * t + 1 := by omega
  have hpD : x ^ (3 * t) ≤ x ^ (6 * t + 1) := by gcongr
  have hpd : d ≤ x ^ (6 * t + 1) := by
    calc d ≤ x := hd
      _ ≤ x ^ (6 * t + 1) := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ hx (show 1 ≤ 6 * t + 1 by omega) :
            x ^ 1 ≤ x ^ (6 * t + 1))
  have hlast : d * (C * x ^ (3 * t)) ^ 2 ≤
      C ^ 2 * x ^ (6 * t + 1) := by
    calc
      d * (C * x ^ (3 * t)) ^ 2
          ≤ x * (C * x ^ (3 * t)) ^ 2 := by gcongr
      _ = C ^ 2 * (x * x ^ ((3 * t) * 2)) := by
        simp only [pow_two, pow_mul]
        ring
      _ = C ^ 2 * x ^ ((3 * t) * 2 + 1) := by
        rw [pow_succ]
        ring
      _ = C ^ 2 * x ^ (6 * t + 1) := by congr 2 <;> omega
  change d + C * x ^ (3 * t) + d * (C * x ^ (3 * t)) ^ 2 ≤
    (1 + C + C ^ 2) * x ^ (6 * t + 1)
  calc
    d + C * x ^ (3 * t) + d * (C * x ^ (3 * t)) ^ 2
        ≤ x ^ (6 * t + 1) + C * x ^ (6 * t + 1) +
            C ^ 2 * x ^ (6 * t + 1) := by gcongr
    _ = (1 + C + C ^ 2) * x ^ (6 * t + 1) := by ring

/-- Multiplicative form of the fixed-order counting theorem for nonempty
target sets. -/
theorem card_neighborTraceFamily_le_mul_of_wreach {n d t : ℕ}
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (hA : A.Nonempty) (hKt : ¬ HasBiclique G t)
    (hπ : ∀ u, (wreach G π 2 u).ncard ≤ d) :
    (Finset.univ.image (neighborTrace G A)).card ≤
      A.card * orderCountingPolynomial t d := by
  let P := tracePolynomial t d
  calc
    (Finset.univ.image (neighborTrace G A)).card
        ≤ A.card * d + (1 + A.card * d * P) * P := by
      simpa [P] using card_neighborTraceFamily_le_of_wreach G π A hKt hπ
    _ = A.card * d + P + A.card * d * P ^ 2 := by ring
    _ ≤ A.card * d + A.card * P + A.card * d * P ^ 2 := by
      gcongr
      exact Nat.le_mul_of_pos_left P hA.card_pos
    _ = A.card * orderCountingPolynomial t d := by
      simp only [orderCountingPolynomial, P]
      ring

/-! ## Polynomial witness localization -/

/-- Every neighborhood trace on `A` is already realized in an induced copy
on `A` together with one representative per trace.  The coarse VC bound
makes the resulting carrier polynomial in `|A|`. -/
theorem exists_localized_copy {n t : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (hKt : ¬ HasBiclique G t) :
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)) (A' : Finset (Fin m)),
      H ⊑ G ∧ ¬ HasBiclique H t ∧ A'.card = A.card ∧
      (Finset.univ.image (neighborTrace G A)).card ≤
        (Finset.univ.image (neighborTrace H A')).card ∧
      m ≤ A.card + (3 * t + 1) * (A.card + 1) ^ (3 * t) := by
  classical
  let T := Finset.univ.image (neighborTrace G A)
  have rep_exists (q : ↑T) : ∃ u : Fin n, neighborTrace G A u = q.val := by
    obtain ⟨u, -, hu⟩ := Finset.mem_image.1 q.property
    exact ⟨u, hu⟩
  let rep : ↑T → Fin n := fun q => Classical.choose (rep_exists q)
  have rep_key (q : ↑T) : neighborTrace G A (rep q) = q.val :=
    Classical.choose_spec (rep_exists q)
  have rep_inj : Function.Injective rep := by
    intro q q' hqq'
    apply Subtype.ext
    rw [← rep_key q, ← rep_key q', hqq']
  let reps : Finset (Fin n) := T.attach.image rep
  have hreps_card : reps.card = T.card := by
    rw [show reps = T.attach.image rep by rfl, Finset.card_image_of_injective _ rep_inj]
    simp
  have hrep_mem (q : ↑T) : rep q ∈ reps := by
    refine Finset.mem_image.2 ⟨q, ?_, rfl⟩
    simp
  let X := A ∪ reps
  let e := X.orderIsoOfFin rfl
  let E : Fin X.card ↪ Fin n :=
    ⟨fun i => (e i).val, fun i j hij => e.injective (Subtype.ext hij)⟩
  let H : SimpleGraph (Fin X.card) := G.comap E
  let A' : Finset (Fin X.card) := Finset.univ.filter fun i => E i ∈ A
  have hA'_iff (i : Fin X.card) : i ∈ A' ↔ E i ∈ A := by
    simp [A']
  have hA'_card : A'.card = A.card := by
    let f : ↑A' → ↑A := fun i =>
      ⟨E i.val, (hA'_iff i.val).1 i.property⟩
    have hf_inj : Function.Injective f := fun i j hij => by
      apply Subtype.ext
      have hE : E i.val = E j.val := by
        simpa [f] using congrArg Subtype.val hij
      exact E.injective hE
    have hf_surj : Function.Surjective f := by
      intro a
      have haX : a.val ∈ X := Finset.mem_union_left reps a.property
      let i : Fin X.card := e.symm ⟨a.val, haX⟩
      have hEi : E i = a.val := by
        simp [E, i]
      have hiA' : i ∈ A' := (hA'_iff i).2 (hEi ▸ a.property)
      refine ⟨⟨i, hiA'⟩, ?_⟩
      apply Subtype.ext
      exact hEi
    simpa only [Fintype.card_coe] using
      Fintype.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  let lift : ↑T → Finset (Fin X.card) := fun q =>
    neighborTrace H A' (e.symm ⟨rep q,
      Finset.mem_union_right A (hrep_mem q)⟩)
  have lift_inj : Function.Injective lift := by
    intro q q' hqq'
    apply Subtype.ext
    apply Finset.ext
    intro x
    have hxsub : x ∈ q.val → x ∈ A := by
      intro hx
      rw [← rep_key q] at hx
      exact (mem_neighborTrace_iff G A (rep q) x).1 hx |>.1
    have hxsub' : x ∈ q'.val → x ∈ A := by
      intro hx
      rw [← rep_key q'] at hx
      exact (mem_neighborTrace_iff G A (rep q') x).1 hx |>.1
    by_cases hxA : x ∈ A
    · have hxX : x ∈ X := Finset.mem_union_left reps hxA
      let i : Fin X.card := e.symm ⟨x, hxX⟩
      have hEi : E i = x := by simp [E, i]
      have hiA' : i ∈ A' := (hA'_iff i).2 (hEi ▸ hxA)
      have hmem (r : ↑T) :
          i ∈ lift r ↔ x ∈ r.val := by
        rw [show lift r = neighborTrace H A'
          (e.symm ⟨rep r, Finset.mem_union_right A (hrep_mem r)⟩) by rfl,
          mem_neighborTrace_iff]
        simp only [hiA', true_and]
        change G.Adj (E (e.symm ⟨rep r,
          Finset.mem_union_right A (hrep_mem r)⟩)) (E i) ↔ x ∈ r.val
        simp only [E, hEi]
        rw [← rep_key r, mem_neighborTrace_iff]
        simp [hxA, G.adj_comm]
      rw [← hmem q, hqq', hmem q']
    · constructor <;> intro hx
      · exact absurd (hxsub hx) hxA
      · exact absurd (hxsub' hx) hxA
  refine ⟨X.card, H, A', ?_, ?_, hA'_card, ?_, ?_⟩
  · exact ⟨{
      toHom := {
        toFun := E
        map_rel' := fun h => h }
      injective' := E.injective }⟩
  · intro hbic
    rcases hbic with ⟨l, r, hl, hr, hlr, hadj⟩
    apply hKt
    refine ⟨E ∘ l, E ∘ r, E.injective.comp hl, E.injective.comp hr, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x ⟨i, hi⟩ ⟨j, hj⟩
      exact Set.disjoint_left.1 hlr
        ⟨i, rfl⟩ ⟨j, (E.injective (hi.trans hj.symm)).symm⟩
    · intro i j
      exact hadj i j
  · calc
      T.card = (T.attach.image lift).card := by
        rw [Finset.card_image_of_injective _ lift_inj]
        simp
      _ ≤ (Finset.univ.image (neighborTrace H A')).card := by
        apply Finset.card_le_card
        intro F hF
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hF
        exact Finset.mem_image.2 ⟨e.symm ⟨rep q,
          Finset.mem_union_right A (hrep_mem q)⟩, Finset.mem_univ _, rfl⟩
  · calc
      X.card ≤ A.card + reps.card := by
        change (A ∪ reps).card ≤ A.card + reps.card
        exact Finset.card_union_le A reps
      _ = A.card + T.card := by rw [hreps_card]
      _ ≤ A.card + (3 * t + 1) * (A.card + 1) ^ (3 * t) := by
        gcongr
        exact card_neighborTraces_le G t hKt A

end Lax5Proofs.NowhereDenseNeighborhoods
