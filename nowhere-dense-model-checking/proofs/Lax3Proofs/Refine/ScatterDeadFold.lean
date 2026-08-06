import Lax3Proofs.Refine.DeadRowProbe

/-!
# The scatter fold's dead half — flag F-3, compiled

`plans/nowhere-dense-model-checking/r18-design.md` §4 leaves the E4
scatter re-derivation one piece of mathematics it cannot proceed
without, and §7 flags it F-3: the **greedy-count split**

    |greedySet A r S| = |greedy over the alive part| + |S ∩ dead|,

*"isolated vertices are mutually scattered and scattered from
everything"*. This file is that obligation, refuted first and then
proved, together with the arithmetic that turns the second summand into
the design's *"individual kill bits + (default bit × outside count)"*.

## What the split is worth, and why the arena matters

The scatter atom of a turn is decided in the CHILD arena
`masked G Alv'` (`RamDriverCluster.masked_alv_eq`), and its set is the
one the child depth's table bits define. Under the R1.8 domain change
those bits exist at the alive vertices and the turn's kills, and nowhere
else — so a pass that reads the set over the carrier is exactly the
compiled-dead road (`DeadRowProbe.no_coeff_pays_outsideRows`). The split
below is what lets the pass read only what exists:

* the ALIVE half is a member-list walk — `Refine.ScatterBlock`'s landed
  active-set engine at the child depth's own member list, whose charge
  contains neither `n` nor `ns`;
* the KILL half is `≤ mb` bits, the turn's own;
* the OUTSIDE half is **all or nothing** (`outside_all_or_nothing`,
  off `DeadRowProbe.sat_outside_uniform`), so it is one bit times one
  count, and the count is `n − mm − kills` off landed scalars
  (`outside_ncard_eq`).

## The refutation first (§1)

The identity is false for a general subset in place of the dead set, and
false for a subset of the ALIVE vertices of the very arena the driver
runs in: `split_needs_dead` and `split_needs_isolation` are the two
instances. What makes it true is that a dead vertex is isolated in
`RamBfs.masked` (`Refine.DeadRow.masked_isolated`) — it excludes nothing
and nothing excludes it — and the two directions of that are §2's two
lemmas.
-/

namespace Lax3Proofs.Refine.ScatterDeadFold

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences
open Lax3Proofs.WalkDistance
open Lax3Proofs.RamBfs (masked masked_adj)
open Lax3Proofs.RamScatter (greedyMem_iff mem_greedySet)
open Lax3Proofs.RamDriverCluster (markSet mem_markSet)
open Lax3Proofs.Refine.DeadRow (masked_isolated withinDist_isolated_iff)

variable {n r : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ} {X : Set (Fin n)}

/-- The vertices a mask kills, as a set — the complement of
`RamDriverCluster.markSet` inside the carrier. -/
def deadSet (n : ℕ) (M : ℕ → ℕ) : Set (Fin n) := {v | M (v : ℕ) = 0}

theorem mem_deadSet {M : ℕ → ℕ} {v : Fin n} : v ∈ deadSet n M ↔ M (v : ℕ) = 0 := Iff.rfl

theorem markSet_union_deadSet (n : ℕ) (M : ℕ → ℕ) :
    markSet n M ∪ deadSet n M = Set.univ := by
  ext v; by_cases h : M (v : ℕ) = 0 <;> simp [markSet, deadSet, h]

theorem markSet_disjoint_deadSet (n : ℕ) (M : ℕ → ℕ) :
    Disjoint (markSet n M) (deadSet n M) :=
  Set.disjoint_left.2 fun _ ha hd => ha hd

/-! ## §1 Refutation: the identity is about DEAD vertices, not about a
subset

Both instances live in a two-vertex carrier with the complete arena and
radius one, where the greedy process picks `0` and then excludes `1`.
Splitting off `{1}` as if it were unconstrained double-counts it. The
first instance is stated for a bare graph, the second for the driver's
own `RamBfs.masked` at a mask that kills nothing — so the hypothesis
that fails is not "the graph is a masked one" but `M v = 0`. -/

section Falsification

/-- In the complete two-vertex graph at radius one, `0` and `1` are
within distance one of each other. -/
theorem top_withinDist_two :
    WithinDist (⊤ : SimpleGraph (Fin 2)) 1 (0 : Fin 2) (1 : Fin 2) :=
  ⟨SimpleGraph.Walk.cons (by decide) SimpleGraph.Walk.nil, by simp⟩

theorem top_greedy_zero : GreedyMem (⊤ : SimpleGraph (Fin 2)) 1 Set.univ (0 : Fin 2) :=
  greedyMem_iff.2 ⟨Set.mem_univ _, fun _ hu _ _ => absurd hu (by simp)⟩

theorem top_not_greedy_one : ¬ GreedyMem (⊤ : SimpleGraph (Fin 2)) 1 Set.univ (1 : Fin 2) :=
  fun h => (greedyMem_iff.1 h).2 0 (by decide) top_greedy_zero top_withinDist_two

/-- **The split is false for an arbitrary subset.** With `D = {1}` the
right-hand side re-admits the vertex the greedy process passed over, so
the counts differ by one. This is the shape the design's F-3 flag would
have if "dead" were dropped from it. -/
theorem split_needs_dead :
    ∃ (X D : Set (Fin 2)),
      greedySet (⊤ : SimpleGraph (Fin 2)) 1 X ≠
        greedySet (⊤ : SimpleGraph (Fin 2)) 1 (X \ D) ∪ (X ∩ D) := by
  refine ⟨Set.univ, {1}, fun h => top_not_greedy_one ?_⟩
  have h1 : (1 : Fin 2) ∈
      greedySet (⊤ : SimpleGraph (Fin 2)) 1 (Set.univ \ {1}) ∪ (Set.univ ∩ {1}) :=
    Or.inr ⟨Set.mem_univ _, rfl⟩
  rw [← h] at h1
  exact h1

/-- The mask that kills nothing: every vertex of the two-vertex carrier
is alive, and the masked arena is the complete one. -/
def liveMask : ℕ → ℕ := fun _ => 1

theorem masked_top_adj {u v : Fin 2} (h : u ≠ v) :
    (masked (⊤ : SimpleGraph (Fin 2)) liveMask).Adj u v :=
  masked_adj.2 ⟨h, by simp [liveMask], by simp [liveMask]⟩

/-- **And false for a subset of the ALIVE vertices of a masked arena.**
The very arena the driver's scatter atom runs in, at a mask that kills
nothing: splitting off an alive vertex overshoots. So the hypothesis
carrying the identity is `M v = 0` — isolation — and not any property of
`RamBfs.masked` itself. -/
theorem split_needs_isolation :
    ∃ (X D : Set (Fin 2)),
      greedySet (masked (⊤ : SimpleGraph (Fin 2)) liveMask) 1 X ≠
        greedySet (masked (⊤ : SimpleGraph (Fin 2)) liveMask) 1 (X \ D) ∪ (X ∩ D) := by
  have hwd : WithinDist (masked (⊤ : SimpleGraph (Fin 2)) liveMask) 1 (0 : Fin 2) 1 :=
    ⟨SimpleGraph.Walk.cons (masked_top_adj (by decide)) SimpleGraph.Walk.nil, by simp⟩
  have hg0 : GreedyMem (masked (⊤ : SimpleGraph (Fin 2)) liveMask) 1 Set.univ (0 : Fin 2) :=
    greedyMem_iff.2 ⟨Set.mem_univ _, fun _ hu _ _ => absurd hu (by simp)⟩
  have hg1 : ¬ GreedyMem (masked (⊤ : SimpleGraph (Fin 2)) liveMask) 1 Set.univ (1 : Fin 2) :=
    fun h => (greedyMem_iff.1 h).2 0 (by decide) hg0 hwd
  refine ⟨Set.univ, {1}, fun h => hg1 ?_⟩
  have h1 : (1 : Fin 2) ∈
      greedySet (masked (⊤ : SimpleGraph (Fin 2)) liveMask) 1 (Set.univ \ {1}) ∪
        (Set.univ ∩ {1}) :=
    Or.inr ⟨Set.mem_univ _, rfl⟩
  rw [← h] at h1
  exact h1

end Falsification

/-! ## §2 A dead vertex is scattered from everything, and scatters
nothing

Both halves of `withinDist_isolated_iff` at
`Refine.DeadRow.masked_isolated`: a dead vertex reaches only itself in
`masked G M`, so no *other* vertex is within any radius of it, in either
direction. -/

/-- **Nothing is within reach of a dead vertex.** -/
theorem not_withinDist_of_dead {u v : Fin n} (hu : M (u : ℕ) = 0) (hne : v ≠ u) :
    ¬ WithinDist (masked G M) r u v :=
  fun h => hne ((withinDist_isolated_iff (masked_isolated hu)).1 h)

/-- **And a dead vertex is within reach of nothing.** -/
theorem not_withinDist_dead {u v : Fin n} (hv : M (v : ℕ) = 0) (hne : u ≠ v) :
    ¬ WithinDist (masked G M) r u v :=
  fun h => not_withinDist_of_dead hv hne (withinDist_symm h)

/-- **Every dead member of the set is selected.** No earlier vertex can
exclude it, because nothing reaches it. -/
theorem greedyMem_of_dead {v : Fin n} (hv : M (v : ℕ) = 0) (hX : v ∈ X) :
    GreedyMem (masked G M) r X v :=
  greedyMem_iff.2 ⟨hX, fun _ hu _ hwd => not_withinDist_dead hv (Fin.ne_of_lt hu) hwd⟩

/-- **A dead vertex excludes nothing.** The `∀` a later vertex's clause
quantifies over may drop its dead entries. -/
theorem greedyMem_alive_iff (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (r : ℕ) (X : Set (Fin n)) :
    ∀ v : Fin n, M (v : ℕ) ≠ 0 →
      (GreedyMem (masked G M) r X v ↔
        GreedyMem (masked G M) r (X ∩ markSet n M) v) := by
  have key : ∀ N : ℕ, ∀ v : Fin n, (v : ℕ) = N → M (v : ℕ) ≠ 0 →
      (GreedyMem (masked G M) r X v ↔
        GreedyMem (masked G M) r (X ∩ markSet n M) v) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      rintro v rfl hal
      constructor
      · intro h
        obtain ⟨hX, hfar⟩ := greedyMem_iff.1 h
        refine greedyMem_iff.2 ⟨⟨hX, hal⟩, fun u hu hgu hwd => ?_⟩
        have hau : M (u : ℕ) ≠ 0 := (greedyMem_iff.1 hgu).1.2
        exact hfar u hu ((ih (u : ℕ) (by simpa using hu) u rfl hau).2 hgu) hwd
      · intro h
        obtain ⟨⟨hX, -⟩, hfar⟩ := greedyMem_iff.1 h
        refine greedyMem_iff.2 ⟨hX, fun u hu hgu hwd => ?_⟩
        by_cases hau : M (u : ℕ) = 0
        · exact not_withinDist_of_dead hau (Fin.ne_of_gt hu) hwd
        · exact hfar u hu ((ih (u : ℕ) (by simpa using hu) u rfl hau).1 hgu) hwd
  exact fun v hv => key (v : ℕ) v rfl hv

/-! ## §3 The split, as a set and as a count — flag F-3

The greedy set of the whole set is the greedy set of its alive part,
together with **every** dead member. The two halves are disjoint (the
first lies in the alive set), so the counts add. -/

/-- The greedy set of the alive part is alive. -/
theorem greedySet_alive_subset :
    greedySet (masked G M) r (X ∩ markSet n M) ⊆ markSet n M :=
  fun _ hv => (greedyMem_iff.1 hv).1.2

/-- **The set split.** Every dead member of `X` is in the greedy set,
and every alive one is in it exactly when the alive-restricted process
selects it. -/
theorem greedySet_split (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (r : ℕ) (X : Set (Fin n)) :
    greedySet (masked G M) r X =
      greedySet (masked G M) r (X ∩ markSet n M) ∪ (X ∩ deadSet n M) := by
  ext v
  constructor
  · intro hv
    by_cases hd : M (v : ℕ) = 0
    · exact Or.inr ⟨(greedyMem_iff.1 hv).1, hd⟩
    · exact Or.inl ((greedyMem_alive_iff G M r X v hd).1 hv)
  · rintro (hv | ⟨hX, hd⟩)
    · exact (greedyMem_alive_iff G M r X v (greedySet_alive_subset hv)).2 hv
    · exact greedyMem_of_dead hd hX

/-- **F-3, the count.** The greedy count is the alive process's count
plus the number of dead members — one term the active-set engine walks
and one term that is pure arithmetic. -/
theorem ncard_greedySet_split (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (r : ℕ)
    (X : Set (Fin n)) :
    (greedySet (masked G M) r X).ncard =
      (greedySet (masked G M) r (X ∩ markSet n M)).ncard + (X ∩ deadSet n M).ncard := by
  rw [greedySet_split G M r X]
  refine Set.ncard_union_eq (Set.disjoint_left.2 fun v hv hd => ?_) (Set.toFinite _)
    (Set.toFinite _)
  exact greedySet_alive_subset hv hd.2

/-! ## §4 The dead half, at the cluster: kills and the outside class

The dead members split again along the turn's cluster indicator
(`DeadRowProbe.deadRows_split`'s partition, at the counting level): the
KILL half is `≤ mb` vertices whose bits the kill pass wrote, and the
OUTSIDE half is the colour-uniform class. -/

/-- The dead members split along any indicator — the counting twin of
`DeadRowProbe.deadRows_split`. -/
theorem ncard_dead_split (S Xa : Set (Fin n)) :
    S.ncard = (S ∩ Xa).ncard + (S \ Xa).ncard := by
  have hd : Disjoint (S ∩ Xa) (S \ Xa) :=
    Set.disjoint_left.2 fun _ hv hv' => hv'.2 hv.2
  have hu : (S ∩ Xa) ∪ (S \ Xa) = S := by
    ext v
    constructor
    · rintro (⟨hv, -⟩ | ⟨hv, -⟩) <;> exact hv
    · intro hv
      by_cases h : v ∈ Xa
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, h⟩
  conv_lhs => rw [← hu]
  exact Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)

/-- **The outside class is all or nothing.** If any two members of a set
agree on membership in `X`, then `X` either swallows the set or misses
it entirely — so its contribution to a count is `D.ncard` or `0`, one
multiplication by one bit. This is `DeadRowProbe.sat_outside_uniform`
read at the count. -/
theorem outside_all_or_nothing {D : Set (Fin n)} {X : Set (Fin n)}
    (hunif : ∀ u ∈ D, ∀ v ∈ D, (u ∈ X ↔ v ∈ X)) :
    D ⊆ X ∨ D ∩ X = ∅ := by
  by_cases h : ∃ z ∈ D, z ∈ X
  · obtain ⟨z, hzD, hzX⟩ := h
    exact Or.inl fun v hv => (hunif z hzD v hv).1 hzX
  · push Not at h
    exact Or.inr (Set.eq_empty_iff_forall_notMem.2 fun v hv => h v hv.1 hv.2)

/-- The two readings of the outside contribution: the whole count, or
nothing. -/
theorem ncard_inter_of_all_or_nothing {D X : Set (Fin n)}
    (h : D ⊆ X ∨ D ∩ X = ∅) : (D ∩ X).ncard = D.ncard ∨ (D ∩ X).ncard = 0 := by
  rcases h with h | h
  · exact Or.inl (by rw [Set.inter_eq_self_of_subset_left h])
  · exact Or.inr (by rw [h, Set.ncard_empty])

/-- **The outside count is `n − mm − kills`** — the design's arithmetic,
off the member clause's `mm` and the turn's kill count. Nothing here
walks anything: the three numbers are a landed scalar, a landed scalar
and the turn's own. -/
theorem outside_ncard_eq (n : ℕ) (M : ℕ → ℕ) (Xa : Set (Fin n)) :
    (deadSet n M \ Xa).ncard =
      n - (markSet n M).ncard - (deadSet n M ∩ Xa).ncard := by
  have huniv : (Set.univ : Set (Fin n)).ncard = n := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hsplit : (Set.univ : Set (Fin n)).ncard =
      (markSet n M).ncard + (deadSet n M).ncard := by
    rw [← markSet_union_deadSet n M]
    exact Set.ncard_union_eq (markSet_disjoint_deadSet n M) (Set.toFinite _) (Set.toFinite _)
  have hdead := ncard_dead_split (deadSet n M) Xa
  omega

/-! ## §5 The whole fold, in one statement

The scatter atom's count, as the E4 pass computes it: the alive process
over the child depth's member list, plus the kill bits, plus one bit
times the outside count. -/

/-- **The dead contribution, folded.** The greedy count of a set in a
masked arena is the alive process's count, plus the members among the
turn's kills, plus the members of the outside class — the last being
`0` or the whole outside count by `outside_all_or_nothing`. -/
theorem ncard_greedySet_fold (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (r : ℕ)
    (X Xa : Set (Fin n)) :
    (greedySet (masked G M) r X).ncard =
      (greedySet (masked G M) r (X ∩ markSet n M)).ncard +
        ((deadSet n M ∩ Xa ∩ X).ncard + ((deadSet n M \ Xa) ∩ X).ncard) := by
  rw [ncard_greedySet_split G M r X]
  congr 1
  have h1 : X ∩ deadSet n M = (deadSet n M ∩ Xa ∩ X) ∪ ((deadSet n M \ Xa) ∩ X) := by
    ext v
    constructor
    · rintro ⟨hX, hd⟩
      by_cases h : v ∈ Xa
      · exact Or.inl ⟨⟨hd, h⟩, hX⟩
      · exact Or.inr ⟨⟨hd, h⟩, hX⟩
    · rintro (⟨⟨hd, -⟩, hX⟩ | ⟨⟨hd, -⟩, hX⟩) <;> exact ⟨hX, hd⟩
  rw [h1]
  exact Set.ncard_union_eq (Set.disjoint_left.2 fun _ hv hv' => hv'.1.2 hv.1.2)
    (Set.toFinite _) (Set.toFinite _)

end Lax3Proofs.Refine.ScatterDeadFold
