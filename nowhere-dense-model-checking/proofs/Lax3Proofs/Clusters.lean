import Lax3Proofs.WalkDistance
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

/-!
The Vitali-style grouping of a tuple of vertices into clusters
(arXiv:2606.23180, Lem. `vitali` and Cor. `clusters`, with the source's
constant `c = 8`).

A tuple `a : Fin k → V` need not be spread out: its entries may sit at
any distances from one another, and a local analysis around each of
them separately would double count where the balls overlap. The Vitali
argument replaces the tuple by a *scale* `R` and a subtuple of
*surviving* indices at that scale, such that every entry is within `R`
of a surviving one and the surviving entries are pairwise farther apart
than `8R`. The price is that `R` is not `r` but `r · 9 ^ t` for some
`t < k`: each round of the iteration merges two entries that are too
close, which costs one index and multiplies the radius by nine.

`ClusterSystem` bundles the outcome — the exponent `t`, the surviving
index set `I`, and the retraction `sel : Fin k → Fin k` onto `I` — with
its three defining properties, so that a consumer holds one object
rather than six existentials. The exact form `R = r · 9 ^ t` with
`t + 1 ≤ k` is kept rather than the source's inequality
`r ≤ R ≤ 9 ^ (k-1) · r`, because the downstream quantification argument
needs `R` to range over a *finite explicitly indexed* set of radii, one
per exponent, and not merely to lie in an interval.

The clusters themselves are the sets `cluster G r a sel i`, the union of
the radius-`r` balls around the entries that `sel` sends to `i`. Over
the surviving indices they cover `N_r(a)` exactly (`iUnion_cluster`),
each sits inside a ball of radius `2R` around its representative
(`cluster_subset_ball`), and two of them are farther apart than `4R`
(`cluster_pairwise_far`). Those three facts, and nothing else about the
construction, are what the scatter argument of `Lax3Proofs.ScatterCore`
consumes.

The source states the grouping for a *set* `K` of vertices; it is
carried here for a tuple, with index sets and a selection map, which is
the form Cor. `clusters` actually extracts and the form the model
checking proof passes around. Repeated entries in the tuple need no
special treatment: two equal entries are at distance zero, so the
iteration merges them like any other close pair.
-/

namespace Lax3Proofs.Clusters

open Lax3.ColoredGraphs Lax3Proofs.WalkDistance

/-- A cluster system for the tuple `a` at radius `r`: a scale exponent
`t < k`, a set `I` of surviving indices, and a selection map `sel`
retracting `Fin k` onto `I`, such that every entry `a i` is within
`R = r · 9 ^ t` of its representative `a (sel i)` and two surviving
entries are farther apart than `8R`. This is the conclusion of the
source's Vitali lemma, in the index form its corollary uses. -/
structure ClusterSystem {V : Type*} (G : SimpleGraph V) (r : ℕ) {k : ℕ} (a : Fin k → V) where
  /-- The scale exponent: the radius of the system is `r · 9 ^ t`. -/
  t : ℕ
  /-- The exponent stays below the length of the tuple; each round of
  the source's iteration spends one index. -/
  ht : t + 1 ≤ k
  /-- The surviving indices. -/
  I : Finset (Fin k)
  /-- The selection map, sending every index to the surviving index
  representing it. -/
  sel : Fin k → Fin k
  /-- Selection lands in the surviving indices. -/
  sel_mem : ∀ i, sel i ∈ I
  /-- Selection fixes the surviving indices. -/
  sel_id : ∀ i ∈ I, sel i = i
  /-- Every entry is within the radius of its representative. -/
  sel_close : ∀ i, WithinDist G (r * 9 ^ t) (a i) (a (sel i))
  /-- Two distinct surviving entries are farther apart than eight times
  the radius. -/
  far : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ WithinDist G (8 * (r * 9 ^ t)) (a i) (a j)

variable {V : Type*} {G : SimpleGraph V} {r k : ℕ} {a : Fin k → V}

/-- The radius of a cluster system: `R = r · 9 ^ t`. -/
def ClusterSystem.R (C : ClusterSystem G r a) : ℕ := r * 9 ^ C.t

/-- The radius of a cluster system, unfolded. -/
theorem ClusterSystem.R_eq (C : ClusterSystem G r a) : C.R = r * 9 ^ C.t := rfl

/-- The radius of a cluster system is at least the radius of the balls
it groups. -/
theorem ClusterSystem.r_le_R (C : ClusterSystem G r a) : r ≤ C.R := by
  show r ≤ r * 9 ^ C.t
  calc r = r * 1 := (Nat.mul_one r).symm
    _ ≤ r * 9 ^ C.t := Nat.mul_le_mul (Nat.le_refl r) (Nat.one_le_pow _ _ (by omega))

/-- The source's upper bound on the radius: `R ≤ 9 ^ (k-1) · r`, since
the scale exponent stays below the length of the tuple. -/
theorem ClusterSystem.R_le (C : ClusterSystem G r a) : C.R ≤ r * 9 ^ (k - 1) := by
  have h := C.ht
  show r * 9 ^ C.t ≤ r * 9 ^ (k - 1)
  exact Nat.mul_le_mul (Nat.le_refl r) (Nat.pow_le_pow_right (by omega) (by omega))

/-- Every entry is within the radius of its representative, stated with
`ClusterSystem.R`. -/
theorem ClusterSystem.sel_close_R (C : ClusterSystem G r a) (i : Fin k) :
    WithinDist G C.R (a i) (a (C.sel i)) := C.sel_close i

/-- Two distinct surviving entries are farther apart than `8R`, stated
with `ClusterSystem.R`. -/
theorem ClusterSystem.far_R (C : ClusterSystem G r a) (i : Fin k) (hi : i ∈ C.I) (j : Fin k)
    (hj : j ∈ C.I) (hij : i ≠ j) : ¬ WithinDist G (8 * C.R) (a i) (a j) :=
  C.far i hi j hj hij

/-! ### Existence -/

/-- The source's iteration, as an induction on a bound for the number
of surviving indices: from a selection map at scale `t` whose surviving
set is nonempty and satisfies `t + |I| ≤ k`, a cluster system is
reached. Each round picks two surviving entries within `8R` of each
other, drops one of them and redirects the map through the other, which
costs one index and raises the scale from `r · 9 ^ t` to `r · 9 ^ (t+1)`
— the recharging step, since a vertex within `R` of the dropped entry is
within `R + 8R = 9R` of the entry it is redirected to. -/
theorem nonempty_clusterSystem_of_card_le (G : SimpleGraph V) (r : ℕ) {k : ℕ} (a : Fin k → V) :
    ∀ (n t : ℕ) (I : Finset (Fin k)) (sel : Fin k → Fin k), I.card ≤ n → I.Nonempty →
      t + I.card ≤ k → (∀ i, sel i ∈ I) → (∀ i ∈ I, sel i = i) →
      (∀ i, WithinDist G (r * 9 ^ t) (a i) (a (sel i))) → Nonempty (ClusterSystem G r a) := by
  intro n
  induction n with
  | zero =>
    intro t I sel hcard hne _ _ _ _
    exact absurd (Finset.card_pos.2 hne) (by omega)
  | succ n ih =>
    intro t I sel hcard hne hsum hmem hid hclose
    by_cases hfar : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ WithinDist G (8 * (r * 9 ^ t)) (a i) (a j)
    · have hpos : 0 < I.card := Finset.card_pos.2 hne
      exact ⟨{ t := t, ht := by omega, I := I, sel := sel, sel_mem := hmem, sel_id := hid,
               sel_close := hclose, far := hfar }⟩
    · push Not at hfar
      obtain ⟨u, hu, v, hv, huv, hduv⟩ := hfar
      have hpos : 0 < I.card := Finset.card_pos.2 hne
      have herase : (I.erase u).card = I.card - 1 := Finset.card_erase_of_mem hu
      have hvI : v ∈ I.erase u := Finset.mem_erase.2 ⟨huv.symm, hv⟩
      have harith : r * 9 ^ t + 8 * (r * 9 ^ t) = r * 9 ^ (t + 1) := by
        rw [pow_succ]; ring
      have hmono : r * 9 ^ t ≤ r * 9 ^ (t + 1) :=
        Nat.mul_le_mul (Nat.le_refl r) (Nat.pow_le_pow_right (by omega) (by omega))
      refine ih (t + 1) (I.erase u) (fun i => if sel i = u then v else sel i)
        (by omega) ⟨v, hvI⟩ (by omega) ?_ ?_ ?_
      · intro i
        by_cases h : sel i = u
        · simpa [h] using hvI
        · simpa [h] using Finset.mem_erase.2 ⟨h, hmem i⟩
      · intro i hi
        have hiI : i ∈ I := Finset.mem_of_mem_erase hi
        have hne' : i ≠ u := (Finset.mem_erase.1 hi).1
        have : sel i = i := hid i hiI
        simp [this, hne']
      · intro i
        by_cases h : sel i = u
        · have h1 : WithinDist G (r * 9 ^ t) (a i) (a u) := by
            have := hclose i; rwa [h] at this
          have h2 : WithinDist G (r * 9 ^ t + 8 * (r * 9 ^ t)) (a i) (a v) :=
            withinDist_trans h1 hduv
          simpa [h, harith] using h2
        · simpa [h] using withinDist_mono_radius hmono (hclose i)

/-- Every nonempty tuple has a cluster system: start the source's
iteration at scale `t = 0` with all indices surviving and the identity
selection. -/
theorem nonempty_clusterSystem (G : SimpleGraph V) (r : ℕ) {k : ℕ} (hk : 1 ≤ k) (a : Fin k → V) :
    Nonempty (ClusterSystem G r a) := by
  refine nonempty_clusterSystem_of_card_le G r a k 0 Finset.univ id (by simp)
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (by simp) (fun i => Finset.mem_univ _) (fun i _ => rfl)
    (fun i => withinDist_refl G (r * 9 ^ 0) (a i))

/-! ### Clusters -/

/-- The cluster of the surviving index `i`: the union of the radius-`r`
balls around the entries that `sel` sends to `i`. -/
def cluster (G : SimpleGraph V) (r : ℕ) (a : Fin k → V) (sel : Fin k → Fin k) (i : Fin k) :
    Set V :=
  ⋃ j ∈ {j | sel j = i}, ball G r (a j)

/-- Membership in a cluster: being within `r` of an entry the selection
map sends to its index. -/
theorem mem_cluster {sel : Fin k → Fin k} {i : Fin k} {x : V} :
    x ∈ cluster G r a sel i ↔ ∃ j, sel j = i ∧ WithinDist G r (a j) x := by
  simp [cluster, ball]

/-- Membership in the `r`-neighborhood of the tuple. -/
theorem mem_iUnion_ball {x : V} : x ∈ ⋃ j, ball G r (a j) ↔ ∃ j, WithinDist G r (a j) x := by
  simp [ball]

/-- Every cluster lies in the `r`-neighborhood of the tuple. -/
theorem cluster_subset_iUnion_ball {sel : Fin k → Fin k} (i : Fin k) :
    cluster G r a sel i ⊆ ⋃ j, ball G r (a j) := by
  intro x hx
  obtain ⟨j, -, hjx⟩ := mem_cluster.1 hx
  exact mem_iUnion_ball.2 ⟨j, hjx⟩

/-- Every vertex of the `r`-neighborhood of the tuple lies in the
cluster of some surviving index. -/
theorem exists_mem_cluster (C : ClusterSystem G r a) {x : V}
    (hx : x ∈ ⋃ j, ball G r (a j)) : ∃ i ∈ C.I, x ∈ cluster G r a C.sel i := by
  obtain ⟨j, hjx⟩ := mem_iUnion_ball.1 hx
  exact ⟨C.sel j, C.sel_mem j, mem_cluster.2 ⟨j, rfl, hjx⟩⟩

/-- Every cluster is contained in the ball of radius `2R` around its
representative: an entry selecting `i` is within `R` of `a i`, and the
ball it contributes has radius `r ≤ R`. -/
theorem cluster_subset_ball (C : ClusterSystem G r a) :
    ∀ i ∈ C.I, cluster G r a C.sel i ⊆ ball G (2 * C.R) (a i) := by
  intro i _ x hx
  obtain ⟨j, hj, hjx⟩ := mem_cluster.1 hx
  have h1 : WithinDist G C.R (a i) (a j) := by
    have h := C.sel_close_R j
    rw [hj] at h
    exact withinDist_symm h
  exact withinDist_mono_radius (by have := C.r_le_R; omega) (withinDist_trans h1 hjx)

/-- Two clusters of distinct surviving indices are farther apart than
`4R`: a walk of length at most `4R` between them, prefixed and suffixed
by the two `2R`-walks to the representatives, would put those within
`8R` of each other. -/
theorem cluster_pairwise_far (C : ClusterSystem G r a) :
    ∀ i ∈ C.I, ∀ j ∈ C.I, i ≠ j → ∀ x ∈ cluster G r a C.sel i, ∀ y ∈ cluster G r a C.sel j,
      ¬ WithinDist G (4 * C.R) x y := by
  intro i hi j hj hij x hx y hy hxy
  refine C.far_R i hi j hj hij ?_
  have hix : WithinDist G (2 * C.R) (a i) x := cluster_subset_ball C i hi hx
  have hjy : WithinDist G (2 * C.R) (a j) y := cluster_subset_ball C j hj hy
  have h : WithinDist G (2 * C.R + 4 * C.R + 2 * C.R) (a i) (a j) :=
    withinDist_trans (withinDist_trans hix hxy) (withinDist_symm hjy)
  exact withinDist_mono_radius (by omega) h

/-- Two clusters of distinct surviving indices are disjoint. -/
theorem cluster_disjoint (C : ClusterSystem G r a) (i : Fin k) (hi : i ∈ C.I) (j : Fin k)
    (hj : j ∈ C.I) (hij : i ≠ j) {x : V} (hxi : x ∈ cluster G r a C.sel i)
    (hxj : x ∈ cluster G r a C.sel j) : False :=
  cluster_pairwise_far C i hi j hj hij x hxi x hxj (withinDist_refl G _ x)

/-- The clusters of the surviving indices cover the `r`-neighborhood of
the tuple exactly. -/
theorem iUnion_cluster (C : ClusterSystem G r a) :
    (⋃ i ∈ C.I, cluster G r a C.sel i) = ⋃ j, ball G r (a j) := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨i, -, hx⟩
    exact mem_iUnion_ball.1 (cluster_subset_iUnion_ball i hx)
  · intro hx
    obtain ⟨i, hi, hxi⟩ := exists_mem_cluster C (mem_iUnion_ball.2 hx)
    exact ⟨i, hi, hxi⟩

end Lax3Proofs.Clusters
