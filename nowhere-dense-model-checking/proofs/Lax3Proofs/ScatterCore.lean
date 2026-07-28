import Lax3Proofs.Clusters
import Mathlib.Data.Set.Card
import Mathlib.Order.Minimal

/-!
The combinatorial core of the locality theorem (arXiv:2606.23180, Lem.
`scatter`): a scatter count decides whether a vertex set `X` reaches
beyond the `r`-neighborhood of a tuple.

Fix a tuple `a` of vertices, a cluster system for it at radius `r`
(`Lax3Proofs.Clusters`) with radius `R`, and a set `X`. Let `S` be an
inclusion-wise maximal `4R`-scattered subset of `X` — the object a
scatter sentence measures the size of. Then

  `X` has a vertex farther than `r` from the tuple

holds exactly when

  `X` has a vertex at distance more than `r` and at most `H` from the
  tuple, or fewer than `|S|` clusters meet `X`.

The point of the equivalence is that both alternatives on the right are
*local* to the tuple: the first is a statement inside the ball of radius
`H`, the second is a count of clusters, which a scatter sentence
supplies. The left-hand side, by contrast, quantifies over the whole
graph. This is the step at which the locality proof discharges a
quantifier that ranges arbitrarily far away.

The proof is the source's. Either some vertex of `X` sits in the margin
`r < dist(x, a) ≤ 4R + r`, and then both sides hold outright, or no
vertex does, and then every vertex of `X` within `4R + r` of the tuple
is already within `r` of it. Under that margin condition each cluster
meeting `X` contains exactly one vertex of `S`: maximality of `S` puts
some `s ∈ S` within `4R` of the cluster, the margin puts `s` inside the
`r`-neighborhood hence inside some cluster, pairwise farness of clusters
puts it inside *this* cluster, and the `2R` bound on cluster diameter
forbids a second one. So the cluster count equals `|S ∩ N_r(a)|`, and
the equivalence becomes `|S ∩ N_r(a)| < |S|`, i.e. `S ⊄ N_r(a)`, which
is the left-hand side: a vertex of `S` outside `N_r(a)` is a witness,
and conversely a witness `x` outside `N_{4R+r}(a)` could be added to `S`
were all of `S` inside `N_r(a)`, contradicting maximality.

# Formalization notes

The number of clusters meeting `X` is `Set.ncard` of the set of
surviving indices whose cluster meets `X`, rather than a `Finset.card`;
the set is a subset of the finite index set `C.I`, and `Set.ncard`
avoids carrying decidability instances for the intersection condition.
The counting step is an explicit bijection — index ↦ its unique vertex
of `S` — and `Set.InjOn.ncard_image`.

`Maximal (fun T => T ⊆ X ∧ DistIndependent G (4 * C.R) T) S` is the
hypothesis shape of `Lax3.ScatterSentences.ScatterChoice.spec`, so a
scatter value can be handed to this lemma exactly as the choice
produces it. Finiteness of `S` is a hypothesis rather than a consequence
because the statement is over an arbitrary vertex type; over `Fin n`,
where the model checking theorem lives, it is automatic.
-/

namespace Lax3Proofs.ScatterCore

open Lax3.ColoredGraphs Lax3Proofs.WalkDistance Lax3Proofs.Clusters Lax12.UniformQuasiWideness

section Scattered

variable {V : Type*} {G : SimpleGraph V} {d : ℕ} {X S : Set V} {x : V}

/-- Lax12's `DistIndependent` in the walk-distance vocabulary: a set is
distance-`d` independent exactly when no two distinct members are within
distance `d`. -/
theorem distIndependent_iff_not_withinDist {A : Set V} :
    DistIndependent G d A ↔ ∀ u ∈ A, ∀ v ∈ A, u ≠ v → ¬ WithinDist G d u v := by
  constructor
  · rintro h u hu v hv huv ⟨p, hp⟩
    exact absurd (h hu hv huv p) (by omega)
  · intro h u hu v hv huv p
    by_contra hlen
    exact h u hu v hv huv ⟨p, by omega⟩

/-- A distance-`d` independent set stays independent when a vertex
farther than `d` from all of it is added. -/
theorem distIndependent_insert (hS : DistIndependent G d S)
    (hx : ∀ s ∈ S, ¬ WithinDist G d s x) : DistIndependent G d (insert x S) := by
  rw [distIndependent_iff_not_withinDist] at hS ⊢
  intro u hu v hv huv
  simp only [Set.mem_insert_iff] at hu hv
  rcases hu with hu | hu
  · rcases hv with hv | hv
    · exact absurd (hu.trans hv.symm) huv
    · subst hu
      exact fun h => hx v hv (withinDist_symm h)
  · rcases hv with hv | hv
    · subst hv
      exact hx u hu
    · exact hS u hu v hv huv

/-- Maximality read as a covering property: a maximal distance-`d`
independent subset of `X` has a member within distance `d` of every
vertex of `X`. Otherwise that vertex could be added. -/
theorem exists_withinDist_of_maximal
    (hSmax : Maximal (fun T => T ⊆ X ∧ DistIndependent G d T) S) (hxX : x ∈ X) :
    ∃ s ∈ S, WithinDist G d s x := by
  by_contra hcon
  push Not at hcon
  have hxS : x ∈ S :=
    hSmax.mem_of_prop_insert
      ⟨Set.insert_subset hxX hSmax.1.1, distIndependent_insert hSmax.1.2 hcon⟩
  exact hcon x hxS (withinDist_refl G d x)

end Scattered

/-- The core lemma: with `S` an inclusion-wise maximal `4R`-scattered
subset of `X` and `H ≥ 4R + r`, the set `X` reaches beyond the
`r`-neighborhood of the tuple `a` exactly when it does so already within
distance `H`, or fewer than `|S|` clusters of the system meet `X`. This
is Lem. `scatter` of the source. -/
theorem scatterCore {V : Type*} {G : SimpleGraph V} {r k H : ℕ} {a : Fin k → V}
    (C : ClusterSystem G r a) {X S : Set V} (hSfin : S.Finite)
    (hSmax : Maximal (fun T => T ⊆ X ∧ DistIndependent G (4 * C.R) T) S)
    (hH : 4 * C.R + r ≤ H) :
    (∃ x ∈ X, ∀ i, ¬ WithinDist G r (a i) x) ↔
      ((∃ x ∈ X, (∃ i, WithinDist G H (a i) x) ∧ (∀ i, ¬ WithinDist G r (a i) x)) ∨
        {i | i ∈ C.I ∧ (X ∩ cluster G r a C.sel i).Nonempty}.ncard < S.ncard) := by
  classical
  by_cases hmid :
      ∃ x ∈ X, (∃ i, WithinDist G (4 * C.R + r) (a i) x) ∧ ∀ i, ¬ WithinDist G r (a i) x
  -- A vertex of `X` in the margin `r < dist(x, a) ≤ 4R + r` satisfies both sides at once.
  · obtain ⟨x, hxX, ⟨i, hix⟩, hxfar⟩ := hmid
    exact iff_of_true ⟨x, hxX, hxfar⟩
      (Or.inl ⟨x, hxX, ⟨i, withinDist_mono_radius hH hix⟩, hxfar⟩)
  -- Otherwise the source's margin condition holds: within `4R + r` of the tuple means
  -- within `r` of it, for vertices of `X`.
  push Not at hmid
  have hSX : S ⊆ X := hSmax.1.1
  have hSind : DistIndependent G (4 * C.R) S := hSmax.1.2
  -- Every cluster meeting `X` contains a vertex of `S` …
  have hclEx : ∀ i ∈ C.I, (X ∩ cluster G r a C.sel i).Nonempty →
      ∃ s, s ∈ S ∧ s ∈ cluster G r a C.sel i := by
    rintro i hi ⟨v, hvX, hvC⟩
    obtain ⟨s, hsS, hsv⟩ := exists_withinDist_of_maximal hSmax hvX
    obtain ⟨j, -, hjv⟩ := mem_cluster.1 hvC
    obtain ⟨j', hj's⟩ := hmid s (hSX hsS)
      ⟨j, withinDist_mono_radius (by omega) (withinDist_trans hjv (withinDist_symm hsv))⟩
    obtain ⟨i', hi', hsC'⟩ := exists_mem_cluster C (mem_iUnion_ball.2 ⟨j', hj's⟩)
    by_cases hii : i' = i
    · exact ⟨s, hsS, hii ▸ hsC'⟩
    · exact absurd hsv (cluster_pairwise_far C i' hi' i hi hii s hsC' v hvC)
  -- … and at most one, since a cluster has diameter at most `4R`.
  have hclUniq : ∀ i ∈ C.I, ∀ s ∈ S, ∀ s' ∈ S, s ∈ cluster G r a C.sel i →
      s' ∈ cluster G r a C.sel i → s = s' := by
    intro i hi s hs s' hs' hsC hs'C
    by_contra hne
    exact distIndependent_iff_not_withinDist.1 hSind s hs s' hs' hne
      (withinDist_mono_radius (by omega)
        (withinDist_trans (withinDist_symm (mem_ball.1 (cluster_subset_ball C i hi hsC)))
          (mem_ball.1 (cluster_subset_ball C i hi hs'C))))
  -- Hence the clusters meeting `X` are in bijection with `S ∩ N_r(a)`.
  have hex : ∀ i : Fin k, ∃ s : V,
      (i ∈ C.I ∧ (X ∩ cluster G r a C.sel i).Nonempty) →
        s ∈ S ∧ s ∈ cluster G r a C.sel i := by
    intro i
    by_cases h : i ∈ C.I ∧ (X ∩ cluster G r a C.sel i).Nonempty
    · obtain ⟨s, hs⟩ := hclEx i h.1 h.2
      exact ⟨s, fun _ => hs⟩
    · exact ⟨a i, fun h' => absurd h' h⟩
  choose f hf using hex
  have hfimg : f '' {i | i ∈ C.I ∧ (X ∩ cluster G r a C.sel i).Nonempty}
      = S ∩ ⋃ j, ball G r (a j) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hfS, hfC⟩ := hf i hi
      exact ⟨hfS, cluster_subset_iUnion_ball _ hfC⟩
    · rintro ⟨hyS, hyN⟩
      obtain ⟨i, hi, hyC⟩ := exists_mem_cluster C hyN
      have hiIcl : i ∈ C.I ∧ (X ∩ cluster G r a C.sel i).Nonempty := ⟨hi, ⟨y, hSX hyS, hyC⟩⟩
      obtain ⟨hfS, hfC⟩ := hf i hiIcl
      exact ⟨i, hiIcl, hclUniq i hi (f i) hfS y hyS hfC hyC⟩
  have hfinj : Set.InjOn f {i | i ∈ C.I ∧ (X ∩ cluster G r a C.sel i).Nonempty} := by
    intro i hi j hj hij
    by_contra hne
    obtain ⟨-, hfi⟩ := hf i hi
    obtain ⟨-, hfj⟩ := hf j hj
    rw [hij] at hfi
    exact cluster_disjoint C i hi.1 j hj.1 hne hfi hfj
  have hcount : {i | i ∈ C.I ∧ (X ∩ cluster G r a C.sel i).Nonempty}.ncard
      = (S ∩ ⋃ j, ball G r (a j)).ncard := by
    rw [← hfimg, hfinj.ncard_image]
  rw [hcount]
  constructor
  · rintro ⟨x, hxX, hxfar⟩
    refine Or.inr ?_
    -- The margin upgrades the witness: it is farther than `4R + r` from the tuple.
    have hx4 : ∀ i, ¬ WithinDist G (4 * C.R + r) (a i) x := by
      intro i hi
      obtain ⟨j, hj⟩ := hmid x hxX ⟨i, hi⟩
      exact hxfar j hj
    -- So `S` cannot lie inside `N_r(a)`: the witness could be added to it.
    have hexs : ∃ s ∈ S, s ∉ ⋃ j, ball G r (a j) := by
      by_contra hcon
      push Not at hcon
      have hfarx : ∀ s ∈ S, ¬ WithinDist G (4 * C.R) s x := by
        intro s hs hsx
        obtain ⟨j, hj⟩ := mem_iUnion_ball.1 (hcon s hs)
        exact hx4 j (withinDist_mono_radius (by omega) (withinDist_trans hj hsx))
      obtain ⟨s, hsS, hsx⟩ := exists_withinDist_of_maximal hSmax hxX
      exact hfarx s hsS hsx
    obtain ⟨s, hsS, hsN⟩ := hexs
    exact Set.ncard_lt_ncard
      ((Set.ssubset_iff_of_subset Set.inter_subset_left).2 ⟨s, hsS, fun h => hsN h.2⟩) hSfin
  · rintro (⟨x, hxX, -, hxfar⟩ | hlt)
    · exact ⟨x, hxX, hxfar⟩
    · by_contra hcon
      push Not at hcon
      have hsub : S ⊆ ⋃ j, ball G r (a j) := fun s hs =>
        mem_iUnion_ball.2 (hcon s (hSX hs))
      rw [Set.inter_eq_self_of_subset_left hsub] at hlt
      exact absurd hlt (lt_irrefl _)

end Lax3Proofs.ScatterCore
