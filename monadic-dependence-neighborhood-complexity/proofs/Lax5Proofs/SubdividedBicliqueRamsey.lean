import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Monotone.Basic
import Lax5Proofs.Subdivision
import Lax5Proofs.TupleRamsey

/-!
Mählmann's thesis, Lemma 13.8: a graph containing a large `r`-subdivided
biclique as a subgraph contains either a large biclique or, for some
`1 ≤ r' ≤ r`, a large exactly-`r'`-subdivided biclique as an *induced*
subgraph.  Shortest-path atomic types are made homogeneous with the
order-type bipartite Ramsey theorem from `Lax5Proofs.TupleRamsey`.
-/

namespace Lax5Proofs.SubdividedBicliqueRamsey

open Lax5Proofs.Subdivision


/-- Boolean masks for equality / adjacency patterns on
`(aᵢ, p_{i,j,0}, …, p_{i,j,r}, bⱼ)`, i.e. `(r + 3)`-tuples in the successor
case. -/
private abbrev AtomicMask (r : ℕ) : Type :=
  Fin (r + 3) × Fin (r + 3) → Bool

/-- Encodes the atomic type of two `(r + 3)`-tuples by their equality and
adjacency masks. This is the finite color space fed into Bipartite Ramsey. -/
private abbrev AtomicType (r : ℕ) : Type :=
  AtomicMask r × AtomicMask r

private noncomputable abbrev atomicTypeEquivFin (r : ℕ) :
    AtomicType r ≃ Fin (Fintype.card (AtomicType r)) :=
  Fintype.equivFin (AtomicType r)

private lemma atomicType_card_pos (r : ℕ) :
    0 < Fintype.card (AtomicType r) := by
  classical
  refine Fintype.card_pos_iff.mpr ?_
  exact ⟨(fun _ => false, fun _ => false)⟩

private theorem biclique_isContained_subdividedBiclique_zero (n : ℕ) :
    (biclique n).IsContained (subdividedBiclique n 0) := by
  refine ⟨⟨{ toFun := Sum.inl, map_rel' := ?_ }, Sum.inl_injective⟩⟩
  intro x y hxy
  rcases x with i | j <;> rcases y with i' | j' <;>
    simp [biclique, subdividedBiclique] at hxy ⊢

private theorem subdividedBiclique_ramsey_zero :
    ∃ U : ℕ → ℕ, Monotone U ∧ (∀ N : ℕ, ∃ n : ℕ, N ≤ U n) ∧
      ∀ {V : Type} [DecidableEq V] [Fintype V]
        (G : SimpleGraph V) (n : ℕ),
        (subdividedBiclique n 0).IsContained G →
          (biclique (U n)).IsContained G ∨
          ∃ r' : ℕ, 1 ≤ r' ∧ r' ≤ 0 ∧
            (subdividedBiclique (U n) r').IsIndContained G := by
  refine ⟨id, fun _ _ hmn => hmn, ?_, ?_⟩
  · intro N
    exact ⟨N, le_rfl⟩
  · intro V _ _ G n hsub
    left
    exact (biclique_isContained_subdividedBiclique_zero n).trans hsub

private def leftRootVertex {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (i : Fin n) : V :=
  copy (.inl (.inl i))

private def rightRootVertex {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (j : Fin n) : V :=
  copy (.inl (.inr j))

private def pathVertex {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) (k : Fin (r + 1)) : V :=
  copy (.inr ((i, j), k))

private def tupleVertexSet {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) : Set V :=
  {v | v = leftRootVertex copy i ∨ v = rightRootVertex copy j ∨
    ∃ k : Fin (r + 1), v = pathVertex copy i j k}

private def tupleInduced {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) : SimpleGraph {v // v ∈ tupleVertexSet copy i j} :=
  G.induce (tupleVertexSet copy i j)

private theorem mem_tupleVertexSet_left {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) :
    leftRootVertex copy i ∈ tupleVertexSet copy i j := by
  simp [tupleVertexSet]

private theorem mem_tupleVertexSet_right {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) :
    rightRootVertex copy j ∈ tupleVertexSet copy i j := by
  simp [tupleVertexSet]

private theorem mem_tupleVertexSet_path {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) (k : Fin (r + 1)) :
    pathVertex copy i j k ∈ tupleVertexSet copy i j := by
  simp [tupleVertexSet]

private def tupleLeftRoot {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) : {v // v ∈ tupleVertexSet copy i j} :=
  ⟨leftRootVertex copy i, mem_tupleVertexSet_left copy i j⟩

private def tupleRightRoot {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) : {v // v ∈ tupleVertexSet copy i j} :=
  ⟨rightRootVertex copy j, mem_tupleVertexSet_right copy i j⟩

private def tuplePathVertex {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) (k : Fin (r + 1)) : {v // v ∈ tupleVertexSet copy i j} :=
  ⟨pathVertex copy i j k, mem_tupleVertexSet_path copy i j k⟩

private def tuplePathToRight {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) :
    (k : ℕ) → (hk : k < r + 1) →
      (tupleInduced copy i j).Walk
        (tuplePathVertex copy i j ⟨k, hk⟩)
        (tupleRightRoot copy i j)
  | k, hk =>
      if hlast : k + 1 = r + 1 then
        .cons
          (by
            have hk_eq : k = r := by omega
            apply SimpleGraph.induce_adj.2
            simpa [tuplePathVertex, tupleRightRoot, pathVertex, rightRootVertex] using
              (copy.toHom.map_adj <| by
                simp [subdividedBiclique, hk_eq]))
          .nil
      else
        let hk' : k + 1 < r + 1 := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) hlast
        .cons
          (by
            apply SimpleGraph.induce_adj.2
            simpa [tuplePathVertex, pathVertex] using
              (copy.toHom.map_adj <| by
                simp [subdividedBiclique]))
          (tuplePathToRight copy i j (k + 1) hk')
termination_by k => r + 1 - k
decreasing_by
  omega

private def tupleWitnessWalk {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) :
    (tupleInduced copy i j).Walk
      (tupleLeftRoot copy i j)
      (tupleRightRoot copy i j) :=
  .cons
    (by
      apply SimpleGraph.induce_adj.2
      simpa [tupleLeftRoot, tuplePathVertex, leftRootVertex, pathVertex] using
        (copy.toHom.map_adj <| by
          simp [subdividedBiclique]))
    (tuplePathToRight copy i j 0 (Nat.succ_pos r))

private def lastFin (n : ℕ) (hn : 1 ≤ n) : Fin n :=
  ⟨n - 1, Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn) Nat.zero_lt_one⟩

private def firstFin (n : ℕ) (hn : 1 ≤ n) : Fin n :=
  ⟨0, hn⟩

/-- The degenerate two-point tuple sending both coordinates to `i`. Used to
probe the self atomic type of a single `(r + 2)`-tuple via the bipartite
Ramsey homogeneity statement. -/
private def diagPair {n : ℕ} (i : Fin n) : Fin 2 → Fin n :=
  fun _ => i

private theorem orderType_diagPair {n : ℕ} (i : Fin n) :
    TupleRamsey.orderType (diagPair i) =
      fun _ => Ordering.eq := by
  ext p
  simp [diagPair, TupleRamsey.orderType]

/-- The `(r + 3)`-tuple `(aᵢ, p_{i,j,0}, …, p_{i,j,r}, bⱼ)` used for the
atomic-type coloring in the successor case. -/
private def atomicTuple {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (a b : Fin n) : Fin (r + 3) → V :=
  fun t =>
    if h : t.1 = 0 then
      leftRootVertex copy a
    else if hlast : t.1 = r + 2 then
      rightRootVertex copy b
    else
      pathVertex copy a b
        ⟨t.1 - 1, by
          have ht : t.1 < r + 3 := t.2
          have hpos : 0 < t.1 := Nat.pos_of_ne_zero h
          have hlt : t.1 < r + 2 := by omega
          exact (Nat.sub_lt_iff_lt_add hpos).2 hlt⟩

private theorem atomicTuple_zero {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (a b : Fin n) :
    atomicTuple copy a b 0 = leftRootVertex copy a := by
  simp [atomicTuple]

private theorem atomicTuple_last {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (a b : Fin n) :
    atomicTuple copy a b (lastFin (r + 3) (by omega)) = rightRootVertex copy b := by
  have hne : ¬((lastFin (r + 3) (by omega) : Fin (r + 3)).1 = 0) := by
    simp [lastFin]
  have hlast :
      (lastFin (r + 3) (by omega) : Fin (r + 3)).1 = r + 2 := by
    simp [lastFin]
  simp [atomicTuple, hlast]

private theorem atomicTuple_mem_tupleVertexSet {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (a b : Fin n) (t : Fin (r + 3)) :
    atomicTuple copy a b t ∈ tupleVertexSet copy a b := by
  by_cases h0 : t.1 = 0
  · simp [atomicTuple, h0, tupleVertexSet]
  by_cases hlast : t.1 = r + 2
  · simp [atomicTuple, hlast, tupleVertexSet]
  · simp [atomicTuple, h0, hlast, tupleVertexSet]

/-- The labeled tuple graph on positions `0, …, r + 2`, where position `0`
is the left root, positions `1, …, r + 1` are the subdivision vertices, and
position `r + 2` is the right root. This is the discrete graph whose shortest
paths should eventually be transported across the Ramsey block. -/
private def tuplePositionGraph {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (a b : Fin n) : SimpleGraph (Fin (r + 3)) where
  Adj s t := G.Adj (atomicTuple copy a b s) (atomicTuple copy a b t)
  symm := by
    intro s t h
    exact G.symm h
  loopless := ⟨fun s => G.loopless.irrefl (atomicTuple copy a b s)⟩

private noncomputable def atomicTypeOf {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (a : Fin 2 → Fin n) (b : Fin 2 → Fin n) : AtomicType r := by
  classical
  let t₀ := atomicTuple copy (a 0) (b 0)
  let t₁ := atomicTuple copy (a 1) (b 1)
  exact
    (fun p => decide (t₀ p.1 = t₁ p.2),
      fun p => decide (G.Adj (t₀ p.1) (t₁ p.2)))

/-- Step 3 coloring extracted from a subdivided-biclique witness. It records a
copy of the `subdividedBiclique n (r + 1)` inside `G`, and `c` is exactly the
finite encoding of the equality/adjacency masks between the two selected
root-plus-path tuples. -/
private structure HasAtomicTypeColoring (r : ℕ) {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (n : ℕ)
    (_hsub : (subdividedBiclique n (r + 1)).IsContained G)
    (c : (Fin 2 → Fin n) → (Fin 2 → Fin n) → Fin (Fintype.card (AtomicType r))) where
  copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G
  color_eq : ∀ a b, c a b = atomicTypeEquivFin r (atomicTypeOf G copy a b)

/-- Packaged Step 5 data on a homogeneous Ramsey block.

At the current scaffold stage we expose the witness copy together with the
chosen shortest paths and the first genuine homogeneity consequence available
from the Ramsey block: every diagonal tuple `(aᵢ, p_{i,j,*}, bⱼ)` with
`i ∈ I`, `j ∈ J` has the same self atomic type. The eventual common-index
sequence can be extracted from this without changing consumers of the record. -/
private structure HasHomogeneousShortestPaths (r : ℕ) {V : Type}
    [DecidableEq V] [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (_hsub : (subdividedBiclique n (r + 1)).IsContained G)
    (_I _J : Finset (Fin n)) where
  copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G
  shortestPath :
    ∀ i j,
      let H := tupleInduced copy i j
      H.Path (tupleLeftRoot copy i j) (tupleRightRoot copy i j)
  shortestPath_length_eq_dist : ∀ i j,
    let H := tupleInduced copy i j
    ((shortestPath i j : H.Walk (tupleLeftRoot copy i j) (tupleRightRoot copy i j)).length) =
      H.dist (tupleLeftRoot copy i j) (tupleRightRoot copy i j)
  atomicType_eq_of_orderType :
    ∀ {a a' b b' : Fin 2 → Fin n},
      (∀ i, a i ∈ _I) → (∀ i, a' i ∈ _I) →
      (∀ j, b j ∈ _J) → (∀ j, b' j ∈ _J) →
      TupleRamsey.orderType a =
        TupleRamsey.orderType a' →
      TupleRamsey.orderType b =
        TupleRamsey.orderType b' →
        atomicTypeOf G copy a b = atomicTypeOf G copy a' b'
  diagonal_atomicType_eq :
    ∀ {i i' j j' : Fin n},
      i ∈ _I → i' ∈ _I → j ∈ _J → j' ∈ _J →
        atomicTypeOf G copy (diagPair i) (diagPair j) =
          atomicTypeOf G copy (diagPair i') (diagPair j')

/-- Generic two-point tuple used to talk about ordered pairs of indices on a
Ramsey block. -/
private def pairTuple {n : ℕ} (x y : Fin n) : Fin 2 → Fin n
  | 0 => x
  | 1 => y

private theorem diagonal_left_right_adj_iff {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {hsub : (subdividedBiclique n (r + 1)).IsContained G}
    {I J : Finset (Fin n)}
    (hpaths : HasHomogeneousShortestPaths r G n hsub I J)
    {i i' j j' : Fin n}
    (hi : i ∈ I) (hi' : i' ∈ I) (hj : j ∈ J) (hj' : j' ∈ J) :
    G.Adj (leftRootVertex hpaths.copy i) (rightRootVertex hpaths.copy j) ↔
      G.Adj (leftRootVertex hpaths.copy i') (rightRootVertex hpaths.copy j') := by
  have hEq :=
    hpaths.diagonal_atomicType_eq hi hi' hj hj'
  let z : Fin (r + 3) := 0
  let l : Fin (r + 3) := lastFin (r + 3) (by omega)
  have hMask :
      (atomicTypeOf G hpaths.copy (diagPair i) (diagPair j)).2 (z, l) =
        (atomicTypeOf G hpaths.copy (diagPair i') (diagPair j')).2 (z, l) := by
    exact congrArg (fun t => t.2 (z, l)) hEq
  simp [atomicTypeOf, diagPair, z, l, atomicTuple_zero, atomicTuple_last] at hMask ⊢
  exact hMask

private theorem atomicType_eq_iff_eq {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    {a a' b b' : Fin 2 → Fin n} {s t : Fin (r + 3)}
    (hEq : atomicTypeOf G copy a b = atomicTypeOf G copy a' b') :
    atomicTuple copy (a 0) (b 0) s = atomicTuple copy (a 1) (b 1) t ↔
      atomicTuple copy (a' 0) (b' 0) s = atomicTuple copy (a' 1) (b' 1) t := by
  have hMask :
      (atomicTypeOf G copy a b).1 (s, t) =
        (atomicTypeOf G copy a' b').1 (s, t) := by
    exact congrArg (fun ty => ty.1 (s, t)) hEq
  simpa [atomicTypeOf] using hMask

private theorem atomicType_eq_iff_adj {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    {a a' b b' : Fin 2 → Fin n} {s t : Fin (r + 3)}
    (hEq : atomicTypeOf G copy a b = atomicTypeOf G copy a' b') :
    G.Adj (atomicTuple copy (a 0) (b 0) s) (atomicTuple copy (a 1) (b 1) t) ↔
      G.Adj (atomicTuple copy (a' 0) (b' 0) s) (atomicTuple copy (a' 1) (b' 1) t) := by
  have hMask :
      (atomicTypeOf G copy a b).2 (s, t) =
        (atomicTypeOf G copy a' b').2 (s, t) := by
    exact congrArg (fun ty => ty.2 (s, t)) hEq
  simpa [atomicTypeOf] using hMask

private theorem diagonal_atomicTuple_eq_iff {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {hsub : (subdividedBiclique n (r + 1)).IsContained G}
    {I J : Finset (Fin n)}
    (hpaths : HasHomogeneousShortestPaths r G n hsub I J)
    {i i' j j' : Fin n}
    (hi : i ∈ I) (hi' : i' ∈ I) (hj : j ∈ J) (hj' : j' ∈ J)
    {s t : Fin (r + 3)} :
    atomicTuple hpaths.copy i j s = atomicTuple hpaths.copy i j t ↔
      atomicTuple hpaths.copy i' j' s = atomicTuple hpaths.copy i' j' t := by
  exact atomicType_eq_iff_eq hpaths.copy (hpaths.diagonal_atomicType_eq hi hi' hj hj')

private theorem diagonal_atomicTuple_adj_iff {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {hsub : (subdividedBiclique n (r + 1)).IsContained G}
    {I J : Finset (Fin n)}
    (hpaths : HasHomogeneousShortestPaths r G n hsub I J)
    {i i' j j' : Fin n}
    (hi : i ∈ I) (hi' : i' ∈ I) (hj : j ∈ J) (hj' : j' ∈ J)
    {s t : Fin (r + 3)} :
    G.Adj (atomicTuple hpaths.copy i j s) (atomicTuple hpaths.copy i j t) ↔
      G.Adj (atomicTuple hpaths.copy i' j' s) (atomicTuple hpaths.copy i' j' t) := by
  exact atomicType_eq_iff_adj hpaths.copy (hpaths.diagonal_atomicType_eq hi hi' hj hj')

private theorem pair_atomicType_eq {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {hsub : (subdividedBiclique n (r + 1)).IsContained G}
    {I J : Finset (Fin n)}
    (hpaths : HasHomogeneousShortestPaths r G n hsub I J)
    {i₀ i₁ i₀' i₁' j₀ j₁ j₀' j₁' : Fin n}
    (hi : ∀ t, pairTuple i₀ i₁ t ∈ I)
    (hi' : ∀ t, pairTuple i₀' i₁' t ∈ I)
    (hj : ∀ t, pairTuple j₀ j₁ t ∈ J)
    (hj' : ∀ t, pairTuple j₀' j₁' t ∈ J)
    (hoti :
      TupleRamsey.orderType (pairTuple i₀ i₁) =
        TupleRamsey.orderType (pairTuple i₀' i₁'))
    (hotj :
      TupleRamsey.orderType (pairTuple j₀ j₁) =
        TupleRamsey.orderType (pairTuple j₀' j₁')) :
    atomicTypeOf G hpaths.copy (pairTuple i₀ i₁) (pairTuple j₀ j₁) =
      atomicTypeOf G hpaths.copy (pairTuple i₀' i₁') (pairTuple j₀' j₁') := by
  exact hpaths.atomicType_eq_of_orderType hi hi' hj hj' hoti hotj

private theorem pair_atomicTuple_adj_iff {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {hsub : (subdividedBiclique n (r + 1)).IsContained G}
    {I J : Finset (Fin n)}
    (hpaths : HasHomogeneousShortestPaths r G n hsub I J)
    {i₀ i₁ i₀' i₁' j₀ j₁ j₀' j₁' : Fin n}
    (hi : ∀ t, pairTuple i₀ i₁ t ∈ I)
    (hi' : ∀ t, pairTuple i₀' i₁' t ∈ I)
    (hj : ∀ t, pairTuple j₀ j₁ t ∈ J)
    (hj' : ∀ t, pairTuple j₀' j₁' t ∈ J)
    (hoti :
      TupleRamsey.orderType (pairTuple i₀ i₁) =
        TupleRamsey.orderType (pairTuple i₀' i₁'))
    (hotj :
      TupleRamsey.orderType (pairTuple j₀ j₁) =
        TupleRamsey.orderType (pairTuple j₀' j₁'))
    {s t : Fin (r + 3)} :
    G.Adj (atomicTuple hpaths.copy i₀ j₀ s) (atomicTuple hpaths.copy i₁ j₁ t) ↔
      G.Adj (atomicTuple hpaths.copy i₀' j₀' s) (atomicTuple hpaths.copy i₁' j₁' t) := by
  exact atomicType_eq_iff_adj hpaths.copy
    (pair_atomicType_eq hpaths hi hi' hj hj' hoti hotj)

private theorem diagonal_tuplePositionGraph_eq {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    {hsub : (subdividedBiclique n (r + 1)).IsContained G}
    {I J : Finset (Fin n)}
    (hpaths : HasHomogeneousShortestPaths r G n hsub I J)
    {i i' j j' : Fin n}
    (hi : i ∈ I) (hi' : i' ∈ I) (hj : j ∈ J) (hj' : j' ∈ J) :
    tuplePositionGraph hpaths.copy i j = tuplePositionGraph hpaths.copy i' j' := by
  ext s t
  exact diagonal_atomicTuple_adj_iff hpaths hi hi' hj hj'

private def leftRootEmbedding {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) : Fin n ↪ V where
  toFun := leftRootVertex copy
  inj' := by
    intro i i' h
    have h' : copy (.inl (.inl i)) = copy (.inl (.inl i')) := by
      simpa [leftRootVertex] using h
    have hs : (.inl (.inl i) : SubdividedBicliqueVert n (r + 1)) =
        .inl (.inl i') := copy.injective h'
    simpa using hs

private def rightRootEmbedding {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) : Fin n ↪ V where
  toFun := rightRootVertex copy
  inj' := by
    intro j j' h
    have h' : copy (.inl (.inr j)) = copy (.inl (.inr j')) := by
      simpa [rightRootVertex] using h
    have hs : (.inl (.inr j) : SubdividedBicliqueVert n (r + 1)) =
        .inl (.inr j') := copy.injective h'
    simpa using hs

/-- Embedding `Fin n ↪ V` that fixes a right-root `j` and an internal index `k`
and varies the left-root `i`, sending `i ↦ p_{i,j,k}`. Used in the D-3 biclique
packager when the cross-edge witness pins `j` and `k`. -/
private def pathLeftEmbedding {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (j : Fin n) (k : Fin (r + 1)) : Fin n ↪ V where
  toFun := fun i => pathVertex copy i j k
  inj' := by
    intro i i' h
    have h' : copy (.inr ((i, j), k)) = copy (.inr ((i', j), k)) := by
      simpa [pathVertex] using h
    have hs : (.inr ((i, j), k) : SubdividedBicliqueVert n (r + 1)) =
        .inr ((i', j), k) := copy.injective h'
    have h₁ : ((i, j), k) = ((i', j), k) := by simpa using hs
    exact (Prod.mk.inj (Prod.mk.inj h₁).1).1

/-- Embedding `Fin n ↪ V` that fixes a left-root `i` and an internal index `k`
and varies the right-root `j`, sending `j ↦ p_{i,j,k}`. Used in the D-4 biclique
packager when the cross-edge witness pins `i` and `k`. -/
private def pathRightEmbedding {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i : Fin n) (k : Fin (r + 1)) : Fin n ↪ V where
  toFun := fun j => pathVertex copy i j k
  inj' := by
    intro j j' h
    have h' : copy (.inr ((i, j), k)) = copy (.inr ((i, j'), k)) := by
      simpa [pathVertex] using h
    have hs : (.inr ((i, j), k) : SubdividedBicliqueVert n (r + 1)) =
        .inr ((i, j'), k) := copy.injective h'
    have h₁ : ((i, j), k) = ((i, j'), k) := by simpa using hs
    exact (Prod.mk.inj (Prod.mk.inj h₁).1).2

private theorem biclique_isContained_of_completeRoots {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n m : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (I J : Finset (Fin n)) (hIcard : m ≤ I.card) (hJcard : m ≤ J.card)
    (hcomplete : ∀ i, i ∈ I → ∀ j, j ∈ J →
      G.Adj (leftRootVertex copy i) (rightRootVertex copy j)) :
    (biclique m).IsContained G := by
  classical
  obtain ⟨I', hI', hI'card⟩ := Finset.exists_subset_card_eq hIcard
  obtain ⟨J', hJ', hJ'card⟩ := Finset.exists_subset_card_eq hJcard
  rw [biclique, SimpleGraph.completeBipartiteGraph_isContained_iff]
  refine ⟨I'.map (leftRootEmbedding copy), J'.map (rightRootEmbedding copy), ?_, ?_, ?_⟩
  · simp [hI'card]
  · simp [hJ'card]
  · intro u hu v hv
    rw [Finset.mem_coe, Finset.mem_map] at hu hv
    rcases hu with ⟨i, hiI', rfl⟩
    rcases hv with ⟨j, hjJ', rfl⟩
    exact hcomplete i (hI' hiI') j (hJ' hjJ')

/-- Like `biclique_isContained_of_completeRoots`, but both biclique sides land
on the left-root vertex set. Used in the `{a_i}` clique halving (Block D-1):
splitting `I` into a "small half" `L` and a "large half" `R` with every
`a_i ∼ a_{i'}` edge present between them already witnesses a biclique. -/
private theorem biclique_isContained_of_leftLeftComplete {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n m : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (L R : Finset (Fin n)) (hLcard : m ≤ L.card) (hRcard : m ≤ R.card)
    (hcomplete : ∀ i, i ∈ L → ∀ i', i' ∈ R →
      G.Adj (leftRootVertex copy i) (leftRootVertex copy i')) :
    (biclique m).IsContained G := by
  classical
  obtain ⟨L', hL', hL'card⟩ := Finset.exists_subset_card_eq hLcard
  obtain ⟨R', hR', hR'card⟩ := Finset.exists_subset_card_eq hRcard
  rw [biclique, SimpleGraph.completeBipartiteGraph_isContained_iff]
  refine ⟨L'.map (leftRootEmbedding copy), R'.map (leftRootEmbedding copy), ?_, ?_, ?_⟩
  · simp [hL'card]
  · simp [hR'card]
  · intro u hu v hv
    rw [Finset.mem_coe, Finset.mem_map] at hu hv
    rcases hu with ⟨i, hiL', rfl⟩
    rcases hv with ⟨i', hi'R', rfl⟩
    exact hcomplete i (hL' hiL') i' (hR' hi'R')

/-- Symmetric to `biclique_isContained_of_leftLeftComplete`: clique on the
right roots `{b_j}` yields a biclique. Used in Block D-2. -/
private theorem biclique_isContained_of_rightRightComplete {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n m : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (L R : Finset (Fin n)) (hLcard : m ≤ L.card) (hRcard : m ≤ R.card)
    (hcomplete : ∀ j, j ∈ L → ∀ j', j' ∈ R →
      G.Adj (rightRootVertex copy j) (rightRootVertex copy j')) :
    (biclique m).IsContained G := by
  classical
  obtain ⟨L', hL', hL'card⟩ := Finset.exists_subset_card_eq hLcard
  obtain ⟨R', hR', hR'card⟩ := Finset.exists_subset_card_eq hRcard
  rw [biclique, SimpleGraph.completeBipartiteGraph_isContained_iff]
  refine ⟨L'.map (rightRootEmbedding copy), R'.map (rightRootEmbedding copy), ?_, ?_, ?_⟩
  · simp [hL'card]
  · simp [hR'card]
  · intro u hu v hv
    rw [Finset.mem_coe, Finset.mem_map] at hu hv
    rcases hu with ⟨j, hjL', rfl⟩
    rcases hv with ⟨j', hj'R', rfl⟩
    exact hcomplete j (hL' hjL') j' (hR' hj'R')

/-- General biclique packager: given two embeddings `fL, fR : Fin n ↪ V` and
finsets `L, R ⊆ Fin n` with `|L|, |R| ≥ m`, if `G` has every edge between
`fL '' L` and `fR '' R`, then `(biclique m).IsContained G`. Used by the
"one-axis-halved" Block D-3/D-4/D-5 cross-edge halving cases, where one
embedding is a root embedding and the other is a `pathLeftEmbedding` /
`pathRightEmbedding`. -/
private theorem biclique_isContained_of_complete {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n m : ℕ}
    (fL fR : Fin n ↪ V) (L R : Finset (Fin n))
    (hLcard : m ≤ L.card) (hRcard : m ≤ R.card)
    (hcomplete : ∀ i, i ∈ L → ∀ i', i' ∈ R → G.Adj (fL i) (fR i')) :
    (biclique m).IsContained G := by
  classical
  obtain ⟨L', hL', hL'card⟩ := Finset.exists_subset_card_eq hLcard
  obtain ⟨R', hR', hR'card⟩ := Finset.exists_subset_card_eq hRcard
  rw [biclique, SimpleGraph.completeBipartiteGraph_isContained_iff]
  refine ⟨L'.map fL, R'.map fR, ?_, ?_, ?_⟩
  · simp [hL'card]
  · simp [hR'card]
  · intro u hu v hv
    rw [Finset.mem_coe, Finset.mem_map] at hu hv
    rcases hu with ⟨i, hiL', rfl⟩
    rcases hv with ⟨i', hi'R', rfl⟩
    exact hcomplete i (hL' hiL') i' (hR' hi'R')

/-- Any two strictly-ordered pairs on `Fin n` carry the same `orderType`. -/
private theorem orderType_pairTuple_eq_of_lt {n : ℕ} {i i' i'' i''' : Fin n}
    (hlt : i < i') (hlt' : i'' < i''') :
    TupleRamsey.orderType (pairTuple i i') =
      TupleRamsey.orderType (pairTuple i'' i''') := by
  ext ⟨p, q⟩
  fin_cases p <;> fin_cases q <;>
    simp [TupleRamsey.orderType, pairTuple,
      compare_lt_iff_lt.mpr hlt, compare_lt_iff_lt.mpr hlt',
      compare_gt_iff_gt.mpr hlt, compare_gt_iff_gt.mpr hlt']

/-- Any two strictly-reverse-ordered pairs on `Fin n` carry the same
`orderType`. Companion to `orderType_pairTuple_eq_of_lt` for the `gt` case. -/
private theorem orderType_pairTuple_eq_of_gt {n : ℕ} {i i' i'' i''' : Fin n}
    (hgt : i > i') (hgt' : i'' > i''') :
    TupleRamsey.orderType (pairTuple i i') =
      TupleRamsey.orderType (pairTuple i'' i''') := by
  ext ⟨p, q⟩
  fin_cases p <;> fin_cases q <;>
    simp [TupleRamsey.orderType, pairTuple,
      compare_lt_iff_lt.mpr hgt, compare_lt_iff_lt.mpr hgt',
      compare_gt_iff_gt.mpr hgt, compare_gt_iff_gt.mpr hgt']

/-- `diagPair` and `pairTuple` agree on repeated arguments. -/
private theorem pairTuple_self_eq_diagPair {n : ℕ} (i : Fin n) :
    pairTuple i i = diagPair i := by
  funext t
  fin_cases t <;> rfl

/-- First-m elements (smallest) of `I`, indexed by the order-embedding
`I.orderEmbOfFin rfl`. Requires `m ≤ |I|`. -/
private noncomputable def firstHalfFinset {n : ℕ} (I : Finset (Fin n))
    {m : ℕ} (hm : m ≤ I.card) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin m)).map
    (Fin.castLEEmb hm |>.trans (I.orderEmbOfFin rfl).toEmbedding)

/-- Last-m elements (largest) of `I`. Requires `m ≤ |I|`. -/
private noncomputable def lastHalfFinset {n : ℕ} (I : Finset (Fin n))
    {m : ℕ} (hm : m ≤ I.card) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin m)).map
    ((⟨fun k : Fin m => ⟨I.card - m + k.val, by omega⟩,
        fun a b hab => by
          have : (I.card - m) + a.val = (I.card - m) + b.val := by
            simpa using congrArg Fin.val hab
          exact Fin.ext (by omega)⟩ : Fin m ↪ Fin I.card).trans
      (I.orderEmbOfFin rfl).toEmbedding)

private theorem firstHalfFinset_subset {n : ℕ} (I : Finset (Fin n)) {m : ℕ}
    (hm : m ≤ I.card) : firstHalfFinset I hm ⊆ I := by
  intro x hx
  rw [firstHalfFinset, Finset.mem_map] at hx
  obtain ⟨k, _, rfl⟩ := hx
  exact Finset.orderEmbOfFin_mem I rfl _

private theorem lastHalfFinset_subset {n : ℕ} (I : Finset (Fin n)) {m : ℕ}
    (hm : m ≤ I.card) : lastHalfFinset I hm ⊆ I := by
  intro x hx
  rw [lastHalfFinset, Finset.mem_map] at hx
  obtain ⟨k, _, rfl⟩ := hx
  exact Finset.orderEmbOfFin_mem I rfl _

private theorem firstHalfFinset_card {n : ℕ} (I : Finset (Fin n)) {m : ℕ}
    (hm : m ≤ I.card) : (firstHalfFinset I hm).card = m := by
  simp [firstHalfFinset]

private theorem lastHalfFinset_card {n : ℕ} (I : Finset (Fin n)) {m : ℕ}
    (hm : m ≤ I.card) : (lastHalfFinset I hm).card = m := by
  simp [lastHalfFinset]

private theorem firstHalfFinset_lt_lastHalfFinset {n : ℕ} (I : Finset (Fin n))
    {m : ℕ} (h2m : 2 * m ≤ I.card)
    {i i' : Fin n}
    (hi : i ∈ firstHalfFinset I (by omega : m ≤ I.card))
    (hi' : i' ∈ lastHalfFinset I (by omega : m ≤ I.card)) :
    i < i' := by
  rw [firstHalfFinset, Finset.mem_map] at hi
  obtain ⟨k, _, rfl⟩ := hi
  rw [lastHalfFinset, Finset.mem_map] at hi'
  obtain ⟨k', _, rfl⟩ := hi'
  apply (I.orderEmbOfFin rfl).strictMono
  rw [Fin.lt_def]
  simp only [Fin.castLEEmb_apply, Function.Embedding.coeFn_mk, Fin.val_castLE]
  have hk : k.val < m := k.isLt
  have hk' : k'.val < m := k'.isLt
  omega

private noncomputable def shortestTuplePathData {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) :
    Σ' p : (tupleInduced copy i j).Path (tupleLeftRoot copy i j) (tupleRightRoot copy i j),
      ((p : (tupleInduced copy i j).Walk (tupleLeftRoot copy i j) (tupleRightRoot copy i j)).length) =
        (tupleInduced copy i j).dist (tupleLeftRoot copy i j) (tupleRightRoot copy i j) := by
  classical
  let h := (tupleWitnessWalk copy i j).reachable.exists_path_of_dist
  exact ⟨⟨Classical.choose h, (Classical.choose_spec h).1⟩, (Classical.choose_spec h).2⟩

private noncomputable def shortestTuplePath {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) :
    (tupleInduced copy i j).Path (tupleLeftRoot copy i j) (tupleRightRoot copy i j) :=
  (shortestTuplePathData copy i j).1

private theorem shortestTuplePath_length_eq_dist {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    (i j : Fin n) :
    ((shortestTuplePath copy i j :
        (tupleInduced copy i j).Walk (tupleLeftRoot copy i j) (tupleRightRoot copy i j)).length) =
      (tupleInduced copy i j).dist (tupleLeftRoot copy i j) (tupleRightRoot copy i j) :=
  (shortestTuplePathData copy i j).2

private noncomputable def ramseyBlockLeftEmbedding {m n : ℕ}
    (I : Finset (Fin n)) (hIcard : m ≤ I.card) : Fin m ↪ Fin n :=
  by
    let hcard' : Fintype.card (Fin m) ≤ I.card := by simpa using hIcard
    exact Classical.choose
      (Function.Embedding.exists_of_card_le_finset (α := Fin m) (s := I) hcard')

private theorem ramseyBlockLeftEmbedding_mem {m n : ℕ}
    (I : Finset (Fin n)) (hIcard : m ≤ I.card) (x : Fin m) :
    ramseyBlockLeftEmbedding I hIcard x ∈ I :=
  by
    let hcard' : Fintype.card (Fin m) ≤ I.card := by simpa using hIcard
    exact Classical.choose_spec
      (Function.Embedding.exists_of_card_le_finset (α := Fin m) (s := I) hcard') ⟨x, rfl⟩

private noncomputable def ramseyBlockRightEmbedding {m n : ℕ}
    (J : Finset (Fin n)) (hJcard : m ≤ J.card) : Fin m ↪ Fin n :=
  by
    let hcard' : Fintype.card (Fin m) ≤ J.card := by simpa using hJcard
    exact Classical.choose
      (Function.Embedding.exists_of_card_le_finset (α := Fin m) (s := J) hcard')

private theorem ramseyBlockRightEmbedding_mem {m n : ℕ}
    (J : Finset (Fin n)) (hJcard : m ≤ J.card) (x : Fin m) :
    ramseyBlockRightEmbedding J hJcard x ∈ J :=
  by
    let hcard' : Fintype.card (Fin m) ≤ J.card := by simpa using hJcard
    exact Classical.choose_spec
      (Function.Embedding.exists_of_card_le_finset (α := Fin m) (s := J) hcard') ⟨x, rfl⟩

private theorem subdividedBiclique_zero_isIndContained {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] (G : SimpleGraph V) :
    (subdividedBiclique 0 (r + 1)).IsIndContained G := by
  classical
  letI : IsEmpty (SubdividedBicliqueVert 0 (r + 1)) := by
    dsimp [SubdividedBicliqueVert]
    infer_instance
  exact SimpleGraph.IsIndContained.of_isEmpty

/-- The last position `r + 2` in `Fin (r + 3)`. Under `atomicTuple` this position
maps to the right root `bⱼ`. -/
private def positionLast (r : ℕ) : Fin (r + 3) := ⟨r + 2, by omega⟩

private theorem atomicTuple_positionLast {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    atomicTuple copy a b (positionLast r) = rightRootVertex copy b := by
  simp [atomicTuple, positionLast]

private theorem atomicTuple_one {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    atomicTuple copy a b ⟨1, by omega⟩ = pathVertex copy a b ⟨0, by omega⟩ := by
  simp [atomicTuple]

private theorem atomicTuple_intermediate {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    {k : ℕ} (hk0 : k ≠ 0) (hklast : k ≠ r + 2) (hk : k < r + 3) :
    atomicTuple copy a b ⟨k, hk⟩ =
      pathVertex copy a b ⟨k - 1, by
        have hpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hlt : k < r + 2 := lt_of_le_of_ne (by omega) hklast
        omega⟩ := by
  have hpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hlt : k < r + 2 := lt_of_le_of_ne (by omega) hklast
  simp [atomicTuple, hk0, hklast]

/-- Convenient packaging of `atomicTuple_intermediate`: an internal index
`k : Fin (r + 1)` lifts to position `k.val + 1` in the `Fin (r + 3)`
atomic tuple, where it agrees with `pathVertex copy a b k`. Used in
Block D-3/D-4/D-5 to bridge `pathVertex`-stated cross-edge witnesses to
`pair_atomicTuple_adj_iff` queries. -/
private theorem atomicTuple_succ_eq_pathVertex {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (k : Fin (r + 1)) :
    atomicTuple copy a b ⟨k.val + 1, by have := k.isLt; omega⟩ =
      pathVertex copy a b k := by
  have hk0 : k.val + 1 ≠ 0 := by omega
  have hklast : k.val + 1 ≠ r + 2 := by have := k.isLt; omega
  have hk : k.val + 1 < r + 3 := by have := k.isLt; omega
  have heq := atomicTuple_intermediate copy a b (k := k.val + 1) hk0 hklast hk
  rw [heq]
  congr 1

/-- Adjacency `s → s + 1` in the tuple position graph. Unfolds to a step along
the subdivided-biclique path and transports through `copy`. -/
private theorem tuplePositionGraph_step_adj {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (k : ℕ) (hk : k + 1 ≤ r + 2) :
    (tuplePositionGraph copy a b).Adj ⟨k, by omega⟩ ⟨k + 1, by omega⟩ := by
  show G.Adj (atomicTuple copy a b ⟨k, by omega⟩) (atomicTuple copy a b ⟨k + 1, by omega⟩)
  by_cases hk0 : k = 0
  · subst hk0
    have h0 : atomicTuple copy a b (⟨0, by omega⟩ : Fin (r + 3)) = leftRootVertex copy a := by
      simp [atomicTuple]
    rw [h0, atomicTuple_one]
    refine copy.toHom.map_adj ?_
    show (subdividedBiclique n (r + 1)).Adj
      (.inl (.inl a)) (.inr ((a, b), ⟨0, by omega⟩))
    simp [subdividedBiclique]
  by_cases hklast : k = r + 1
  · subst hklast
    have h1 : atomicTuple copy a b (⟨r + 1, by omega⟩ : Fin (r + 3)) =
        pathVertex copy a b ⟨r, by omega⟩ := by
      have := atomicTuple_intermediate (r := r) copy a b
        (k := r + 1) (by omega) (by omega) (by omega)
      simpa using this
    have h2 : atomicTuple copy a b (⟨r + 1 + 1, by omega⟩ : Fin (r + 3)) =
        rightRootVertex copy b := by
      have : atomicTuple copy a b (positionLast r) = rightRootVertex copy b :=
        atomicTuple_positionLast copy a b
      simpa [positionLast] using this
    rw [h1, h2]
    refine copy.toHom.map_adj ?_
    show (subdividedBiclique n (r + 1)).Adj
      (.inr ((a, b), ⟨r, by omega⟩)) (.inl (.inr b))
    simp [subdividedBiclique]
  -- 0 < k < r + 1, so k + 1 < r + 2
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hksucc_ne_last : k + 1 ≠ r + 2 := by omega
  have h1 : atomicTuple copy a b (⟨k, by omega⟩ : Fin (r + 3)) =
      pathVertex copy a b ⟨k - 1, by omega⟩ :=
    atomicTuple_intermediate (r := r) copy a b (k := k) hk0 (by omega) (by omega)
  have h2 : atomicTuple copy a b (⟨k + 1, by omega⟩ : Fin (r + 3)) =
      pathVertex copy a b ⟨k, by omega⟩ := by
    have := atomicTuple_intermediate (r := r) copy a b
      (k := k + 1) (by omega) hksucc_ne_last (by omega)
    simpa using this
  rw [h1, h2]
  refine copy.toHom.map_adj ?_
  show (subdividedBiclique n (r + 1)).Adj
    (.inr ((a, b), ⟨k - 1, by omega⟩)) (.inr ((a, b), ⟨k, by omega⟩))
  simp [subdividedBiclique]
  omega

/-- Step-by-step walk `⟨k, _⟩ → ⟨k+1, _⟩ → ⋯ → positionLast r` in the tuple
position graph. -/
private def tuplePositionTailWalk {r : ℕ} {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    (k : ℕ) → (hk : k ≤ r + 2) →
      (tuplePositionGraph copy a b).Walk ⟨k, by omega⟩ (positionLast r)
  | k, hk =>
      if hlast : k = r + 2 then
        (SimpleGraph.Walk.nil (G := tuplePositionGraph copy a b)
            (u := positionLast r)).copy
          (by apply Fin.ext; simp [positionLast, hlast]) rfl
      else
        have hk' : k + 1 ≤ r + 2 := Nat.lt_of_le_of_ne hk hlast
        let hadj := tuplePositionGraph_step_adj copy a b k hk'
        .cons hadj (tuplePositionTailWalk copy a b (k + 1) hk')
termination_by k _ => r + 2 - k

private theorem tuplePositionTailWalk_length {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    ∀ (k : ℕ) (hk : k ≤ r + 2),
      (tuplePositionTailWalk copy a b k hk).length = r + 2 - k := by
  intro k hk
  induction hd : r + 2 - k generalizing k with
  | zero =>
      have hk_eq : k = r + 2 := by omega
      unfold tuplePositionTailWalk
      simp [hk_eq]
  | succ d ih =>
      have hlast : k ≠ r + 2 := by omega
      have hk' : k + 1 ≤ r + 2 := by omega
      have hd' : r + 2 - (k + 1) = d := by omega
      unfold tuplePositionTailWalk
      rw [dif_neg hlast]
      simp [SimpleGraph.Walk.length_cons, ih (k + 1) hk' hd']

/-- Explicit witness walk in `tuplePositionGraph copy a b` from position `0` to
`positionLast r`. Length exactly `r + 2`. -/
private def tuplePositionWitnessWalk {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    (tuplePositionGraph copy a b).Walk ⟨0, by omega⟩ (positionLast r) :=
  tuplePositionTailWalk copy a b 0 (by omega)

private theorem tuplePositionWitnessWalk_length {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    (tuplePositionWitnessWalk copy a b).length = r + 2 := by
  have := tuplePositionTailWalk_length (r := r) copy a b 0 (by omega)
  simpa [tuplePositionWitnessWalk] using this

/-- Distance in `tuplePositionGraph copy a b` from `0` to `positionLast r` is
bounded above by `r + 2`, courtesy of `tuplePositionWitnessWalk`. -/
private theorem tuplePositionGraph_dist_le {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    (tuplePositionGraph copy a b).dist ⟨0, by omega⟩ (positionLast r) ≤ r + 2 := by
  have h := SimpleGraph.dist_le (tuplePositionWitnessWalk copy a b)
  rw [tuplePositionWitnessWalk_length] at h
  exact h

/-- Under no direct `aᵢ bⱼ` edge, the positions `0` and `positionLast r` are not
directly adjacent in the tuple position graph, so their distance is at least
`2`. -/
private theorem tuplePositionGraph_one_lt_dist_of_no_direct {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b)) :
    1 < (tuplePositionGraph copy a b).dist ⟨0, by omega⟩ (positionLast r) := by
  have hne : (⟨0, by omega⟩ : Fin (r + 3)) ≠ positionLast r := by
    intro h
    have := congrArg Fin.val h
    simp [positionLast] at this
  have hnadj : ¬ (tuplePositionGraph copy a b).Adj ⟨0, by omega⟩ (positionLast r) := by
    intro hadj
    apply hNoDirect
    have : G.Adj (atomicTuple copy a b ⟨0, by omega⟩) (atomicTuple copy a b (positionLast r)) :=
      hadj
    have h0 : atomicTuple copy a b (⟨0, by omega⟩ : Fin (r + 3)) = leftRootVertex copy a := by
      simp [atomicTuple]
    rw [h0, atomicTuple_positionLast] at this
    exact this
  have hreach : (tuplePositionGraph copy a b).Reachable ⟨0, by omega⟩ (positionLast r) :=
    (tuplePositionWitnessWalk copy a b).reachable
  exact hreach.one_lt_dist_of_ne_of_not_adj hne hnadj

/-- Internal length `r' := dist - 1` of the canonical shortest path in the base
tuple position graph. Under no direct edge, this lives in `[1, r + 1]`. -/
private noncomputable def canonicalInternalLength {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) : ℕ :=
  (tuplePositionGraph copy a b).dist ⟨0, by omega⟩ (positionLast r) - 1

private theorem canonicalInternalLength_le {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    canonicalInternalLength copy a b ≤ r + 1 := by
  have := tuplePositionGraph_dist_le (r := r) copy a b
  unfold canonicalInternalLength
  omega

private theorem one_le_canonicalInternalLength_of_no_direct {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b)) :
    1 ≤ canonicalInternalLength copy a b := by
  have := tuplePositionGraph_one_lt_dist_of_no_direct (r := r) copy a b hNoDirect
  unfold canonicalInternalLength
  omega

/-- Chord-freeness of a shortest walk.

If `p : G.Walk u v` realises the distance `G.dist u v` and `i < j` are both
positions at most `p.length`, then `G.Adj (p.getVert i) (p.getVert j)` forces
`j = i + 1`. Contrapositively: distinct non-consecutive vertices of a shortest
walk are non-adjacent.

Proof. `p` is a path (by `Walk.isPath_of_length_eq_dist`), so its `getVert`
is injective on `[0, p.length]` and `length (takeUntil (getVert k))` equals
`k`. Splicing a hypothetical chord `hadj` into
`takeUntil i ++ cons hadj (dropUntil j)` yields a walk of length
`i + 1 + (p.length - j)`, which by `dist_le` dominates `p.length`. The
conclusion follows by arithmetic. -/
private theorem walk_noChord_of_length_eq_dist {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hlen : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) (hlt : i < j)
    (hadj : G.Adj (p.getVert i) (p.getVert j)) : j = i + 1 := by
  classical
  have hp : p.IsPath := p.isPath_of_length_eq_dist hlen
  have hmem_i : p.getVert i ∈ p.support := p.getVert_mem_support i
  have hmem_j : p.getVert j ∈ p.support := p.getVert_mem_support j
  have hti_len : (p.takeUntil (p.getVert i) hmem_i).length = i := by
    have h1 : (p.takeUntil (p.getVert i) hmem_i).length ≤ p.length :=
      p.length_takeUntil_le hmem_i
    have h2 : p.getVert (p.takeUntil (p.getVert i) hmem_i).length = p.getVert i :=
      p.getVert_length_takeUntil hmem_i
    exact hp.getVert_injOn h1 hi h2
  have htj_len : (p.takeUntil (p.getVert j) hmem_j).length = j := by
    have h1 : (p.takeUntil (p.getVert j) hmem_j).length ≤ p.length :=
      p.length_takeUntil_le hmem_j
    have h2 : p.getVert (p.takeUntil (p.getVert j) hmem_j).length = p.getVert j :=
      p.getVert_length_takeUntil hmem_j
    exact hp.getVert_injOn h1 hj h2
  have hdj_len : (p.dropUntil (p.getVert j) hmem_j).length = p.length - j := by
    have h := congr_arg SimpleGraph.Walk.length (p.take_spec hmem_j)
    rw [SimpleGraph.Walk.length_append, htj_len] at h
    omega
  let q : G.Walk u v :=
    (p.takeUntil (p.getVert i) hmem_i).append
      ((p.dropUntil (p.getVert j) hmem_j).cons hadj)
  have hq_len : q.length = i + 1 + (p.length - j) := by
    show ((p.takeUntil _ hmem_i).append
      ((p.dropUntil _ hmem_j).cons hadj)).length = _
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
      hti_len, hdj_len]
    omega
  have hdist_le : G.dist u v ≤ q.length := SimpleGraph.dist_le q
  rw [← hlen, hq_len] at hdist_le
  omega

/-- Canonical shortest walk from position `0` to `positionLast r` in the base
tuple position graph, chosen noncomputably via `Reachable.exists_path_of_dist`
applied to `tuplePositionWitnessWalk`. The walk is a path and its length equals
`dist`. -/
private noncomputable def canonicalShortestWalk {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    (tuplePositionGraph copy a b).Walk ⟨0, by omega⟩ (positionLast r) :=
  ((tuplePositionWitnessWalk copy a b).reachable.exists_path_of_dist).choose

private theorem canonicalShortestWalk_isPath {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    (canonicalShortestWalk copy a b).IsPath :=
  (((tuplePositionWitnessWalk copy a b).reachable.exists_path_of_dist).choose_spec).1

private theorem canonicalShortestWalk_length_eq_dist {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n) :
    (canonicalShortestWalk copy a b).length =
      (tuplePositionGraph copy a b).dist ⟨0, by omega⟩ (positionLast r) :=
  (((tuplePositionWitnessWalk copy a b).reachable.exists_path_of_dist).choose_spec).2

/-- Under no direct `a-b` edge, the canonical shortest walk has length exactly
`canonicalInternalLength + 1 = dist`. -/
private theorem canonicalShortestWalk_length_eq_succ {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b)) :
    (canonicalShortestWalk copy a b).length = canonicalInternalLength copy a b + 1 := by
  rw [canonicalShortestWalk_length_eq_dist]
  have hge : 1 < (tuplePositionGraph copy a b).dist ⟨0, by omega⟩ (positionLast r) :=
    tuplePositionGraph_one_lt_dist_of_no_direct copy a b hNoDirect
  unfold canonicalInternalLength
  omega

/-- The `k`-th canonical internal index on the base pair `(a, b)`. Defined as
`(k + 1)`-th vertex of `canonicalShortestWalk`. Lives in `Fin (r + 3)`, i.e.
as a tuple position. -/
private noncomputable def canonicalInternalIndex {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (k : Fin (canonicalInternalLength copy a b)) : Fin (r + 3) :=
  (canonicalShortestWalk copy a b).getVert (k.val + 1)

/-- Consecutive canonical internal indices are adjacent in the base tuple
position graph. -/
private theorem tuplePositionGraph_adj_canonicalInternalIndex_succ {r : ℕ}
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b))
    (k : Fin (canonicalInternalLength copy a b))
    (hsucc : k.val + 1 < canonicalInternalLength copy a b) :
    (tuplePositionGraph copy a b).Adj
      (canonicalInternalIndex copy a b k)
      (canonicalInternalIndex copy a b ⟨k.val + 1, hsucc⟩) := by
  have hlen : (canonicalShortestWalk copy a b).length =
      canonicalInternalLength copy a b + 1 :=
    canonicalShortestWalk_length_eq_succ copy a b hNoDirect
  have hlt : k.val + 1 < (canonicalShortestWalk copy a b).length := by
    rw [hlen]; omega
  exact (canonicalShortestWalk copy a b).adj_getVert_succ hlt

/-- The position `0` is adjacent to the first canonical internal index. -/
private theorem tuplePositionGraph_adj_zero_canonicalInternalIndex {r : ℕ}
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b))
    (h : 0 < canonicalInternalLength copy a b) :
    (tuplePositionGraph copy a b).Adj ⟨0, by omega⟩
      (canonicalInternalIndex copy a b ⟨0, h⟩) := by
  have hlen : (canonicalShortestWalk copy a b).length =
      canonicalInternalLength copy a b + 1 :=
    canonicalShortestWalk_length_eq_succ copy a b hNoDirect
  have hlt : 0 < (canonicalShortestWalk copy a b).length := by
    rw [hlen]; omega
  have hadj := (canonicalShortestWalk copy a b).adj_getVert_succ hlt
  have h0 : (canonicalShortestWalk copy a b).getVert 0 = ⟨0, by omega⟩ := by
    simp
  simpa [canonicalInternalIndex, h0] using hadj

/-- The last canonical internal index is adjacent to `positionLast r`. -/
private theorem tuplePositionGraph_adj_canonicalInternalIndex_last {r : ℕ}
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b))
    (k : Fin (canonicalInternalLength copy a b))
    (hlast : k.val + 1 = canonicalInternalLength copy a b) :
    (tuplePositionGraph copy a b).Adj
      (canonicalInternalIndex copy a b k) (positionLast r) := by
  have hlen : (canonicalShortestWalk copy a b).length =
      canonicalInternalLength copy a b + 1 :=
    canonicalShortestWalk_length_eq_succ copy a b hNoDirect
  have hlt : k.val + 1 < (canonicalShortestWalk copy a b).length := by
    rw [hlen]; omega
  have hadj := (canonicalShortestWalk copy a b).adj_getVert_succ hlt
  have hend :
      (canonicalShortestWalk copy a b).getVert (k.val + 1 + 1) = positionLast r := by
    have hlen_le : (canonicalShortestWalk copy a b).length ≤ k.val + 1 + 1 := by
      rw [hlen]; omega
    exact (canonicalShortestWalk copy a b).getVert_of_length_le hlen_le
  have hval : k.val + 1 + 1 = (canonicalShortestWalk copy a b).length := by
    rw [hlen]; omega
  rw [canonicalInternalIndex]
  rw [show (canonicalShortestWalk copy a b).getVert (k.val + 1 + 1) = positionLast r from hend] at hadj
  exact hadj

/-- Canonical internal indices are distinct from the start position `0`. -/
private theorem canonicalInternalIndex_ne_zero {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b))
    (k : Fin (canonicalInternalLength copy a b)) :
    canonicalInternalIndex copy a b k ≠ ⟨0, by omega⟩ := by
  have hp := canonicalShortestWalk_isPath (r := r) copy a b
  have hlen : (canonicalShortestWalk copy a b).length =
      canonicalInternalLength copy a b + 1 :=
    canonicalShortestWalk_length_eq_succ copy a b hNoDirect
  have hle : k.val + 1 ≤ (canonicalShortestWalk copy a b).length := by
    rw [hlen]; omega
  intro hEq
  have : (canonicalShortestWalk copy a b).getVert (k.val + 1) = ⟨0, by omega⟩ :=
    hEq
  have h := (hp.getVert_eq_start_iff hle).1 this
  omega

/-- Canonical internal indices are distinct from the end position `positionLast r`. -/
private theorem canonicalInternalIndex_ne_last {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b))
    (k : Fin (canonicalInternalLength copy a b)) :
    canonicalInternalIndex copy a b k ≠ positionLast r := by
  have hp := canonicalShortestWalk_isPath (r := r) copy a b
  have hlen : (canonicalShortestWalk copy a b).length =
      canonicalInternalLength copy a b + 1 :=
    canonicalShortestWalk_length_eq_succ copy a b hNoDirect
  have hle : k.val + 1 ≤ (canonicalShortestWalk copy a b).length := by
    rw [hlen]; omega
  intro hEq
  have hv : (canonicalShortestWalk copy a b).getVert (k.val + 1) = positionLast r :=
    hEq
  have h := (hp.getVert_eq_end_iff hle).1 hv
  rw [hlen] at h
  omega

/-- The `val` of a canonical internal index is strictly positive. -/
private theorem canonicalInternalIndex_val_pos {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b))
    (k : Fin (canonicalInternalLength copy a b)) :
    0 < (canonicalInternalIndex copy a b k).val := by
  have hne := canonicalInternalIndex_ne_zero (r := r) copy a b hNoDirect k
  rcases Nat.eq_zero_or_pos (canonicalInternalIndex copy a b k).val with h | h
  · exfalso
    apply hne
    apply Fin.ext
    simp [h]
  · exact h

/-- The `val` of a canonical internal index is strictly less than `r + 2`, i.e.
less than `positionLast r`. -/
private theorem canonicalInternalIndex_val_lt {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b))
    (k : Fin (canonicalInternalLength copy a b)) :
    (canonicalInternalIndex copy a b k).val < r + 2 := by
  have hne := canonicalInternalIndex_ne_last (r := r) copy a b hNoDirect k
  have hlt : (canonicalInternalIndex copy a b k).val < r + 3 :=
    (canonicalInternalIndex copy a b k).isLt
  rcases Nat.lt_or_ge (canonicalInternalIndex copy a b k).val (r + 2) with h | h
  · exact h
  · exfalso
    apply hne
    apply Fin.ext
    simp [positionLast]
    omega

/-- Canonical internal indices are injective in `k`. -/
private theorem canonicalInternalIndex_injective {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b)) :
    Function.Injective (canonicalInternalIndex copy a b) := by
  have hp := canonicalShortestWalk_isPath (r := r) copy a b
  have hlen : (canonicalShortestWalk copy a b).length =
      canonicalInternalLength copy a b + 1 :=
    canonicalShortestWalk_length_eq_succ copy a b hNoDirect
  intro k₁ k₂ hEq
  have hk₁ : k₁.val + 1 ≤ (canonicalShortestWalk copy a b).length := by
    rw [hlen]; omega
  have hk₂ : k₂.val + 1 ≤ (canonicalShortestWalk copy a b).length := by
    rw [hlen]; omega
  have h := hp.getVert_injOn (by simpa using hk₁) (by simpa using hk₂) hEq
  apply Fin.ext
  omega

/-- Generalized atomic-tuple decoding: on positions strictly between `0` and
`positionLast r`, `atomicTuple` lands in the path-vertex branch. -/
private theorem atomicTuple_of_strict {r : ℕ} {V : Type} [DecidableEq V]
    [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (t : Fin (r + 3)) (hpos : 0 < t.val) (hlt : t.val < r + 2) :
    atomicTuple copy a b t = pathVertex copy a b ⟨t.val - 1, by omega⟩ :=
  atomicTuple_intermediate (r := r) copy a b (k := t.val)
    (by omega) (by omega) t.isLt

/-- Decoding `atomicTuple` at a canonical internal index. The canonical
internal index lives strictly between `0` and `positionLast r`, so
`atomicTuple` lands in the path-vertex branch regardless of the `(a', b')`
tuple coordinates plugged in. -/
private theorem atomicTuple_canonicalInternalIndex_eq {r : ℕ} {V : Type}
    [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G) (a b : Fin n)
    (hNoDirect : ¬ G.Adj (leftRootVertex copy a) (rightRootVertex copy b))
    (a' b' : Fin n) (k : Fin (canonicalInternalLength copy a b)) :
    atomicTuple copy a' b' (canonicalInternalIndex copy a b k) =
      pathVertex copy a' b'
        ⟨(canonicalInternalIndex copy a b k).val - 1, by
          have h1 := canonicalInternalIndex_val_pos copy a b hNoDirect k
          have h2 := canonicalInternalIndex_val_lt copy a b hNoDirect k
          omega⟩ :=
  atomicTuple_of_strict copy a' b' (canonicalInternalIndex copy a b k)
    (canonicalInternalIndex_val_pos copy a b hNoDirect k)
    (canonicalInternalIndex_val_lt copy a b hNoDirect k)

/-- Candidate vertex map for the induced-copy embedding
`subdividedBiclique (m + 1) (canonicalInternalLength copy i₀ j₀) ↪ V`.

Sends left/right roots of the target subdivided biclique to
`leftRootVertex`/`rightRootVertex` at the Ramsey-block indices `eI i`, `eJ j`,
and sends the `k`-th path vertex of the `(i, j)` diagonal to the `k`-th
canonical internal-index position of the shortest path on the *base* diagonal
`(i₀, j₀)` — decoded through the atomic-tuple encoding at `(eI i, eJ j)`. -/
private noncomputable def candidateInducedMap
    {r : ℕ} {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    {m : ℕ} (eI eJ : Fin (m + 1) ↪ Fin n) (i₀ j₀ : Fin n) :
    SubdividedBicliqueVert (m + 1) (canonicalInternalLength copy i₀ j₀) → V :=
  fun v =>
    match v with
    | .inl (.inl i) => leftRootVertex copy (eI i)
    | .inl (.inr j) => rightRootVertex copy (eJ j)
    | .inr ((i, j), k) =>
        atomicTuple copy (eI i) (eJ j) (canonicalInternalIndex copy i₀ j₀ k)

@[simp] private theorem candidateInducedMap_inl_inl
    {r : ℕ} {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    {m : ℕ} (eI eJ : Fin (m + 1) ↪ Fin n) (i₀ j₀ : Fin n) (i : Fin (m + 1)) :
    candidateInducedMap copy eI eJ i₀ j₀ (.inl (.inl i)) =
      leftRootVertex copy (eI i) := rfl

@[simp] private theorem candidateInducedMap_inl_inr
    {r : ℕ} {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    {m : ℕ} (eI eJ : Fin (m + 1) ↪ Fin n) (i₀ j₀ : Fin n) (j : Fin (m + 1)) :
    candidateInducedMap copy eI eJ i₀ j₀ (.inl (.inr j)) =
      rightRootVertex copy (eJ j) := rfl

@[simp] private theorem candidateInducedMap_inr
    {r : ℕ} {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    {m : ℕ} (eI eJ : Fin (m + 1) ↪ Fin n) (i₀ j₀ : Fin n)
    (i j : Fin (m + 1))
    (k : Fin (canonicalInternalLength copy i₀ j₀)) :
    candidateInducedMap copy eI eJ i₀ j₀ (.inr ((i, j), k)) =
      atomicTuple copy (eI i) (eJ j) (canonicalInternalIndex copy i₀ j₀ k) := rfl

/-- The candidate map evaluated on a subdivision vertex decodes to a
`pathVertex` via `atomicTuple_canonicalInternalIndex_eq`. Convenient for
reducing case analysis of injectivity and adjacency down to `copy`-level
constructor equalities. -/
private theorem candidateInducedMap_inr_eq_pathVertex
    {r : ℕ} {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    {m : ℕ} (eI eJ : Fin (m + 1) ↪ Fin n) (i₀ j₀ : Fin n)
    (hNoDirect₀ : ¬ G.Adj (leftRootVertex copy i₀) (rightRootVertex copy j₀))
    (i j : Fin (m + 1))
    (k : Fin (canonicalInternalLength copy i₀ j₀)) :
    candidateInducedMap copy eI eJ i₀ j₀ (.inr ((i, j), k)) =
      pathVertex copy (eI i) (eJ j)
        ⟨(canonicalInternalIndex copy i₀ j₀ k).val - 1, by
          have h1 := canonicalInternalIndex_val_pos copy i₀ j₀ hNoDirect₀ k
          have h2 := canonicalInternalIndex_val_lt copy i₀ j₀ hNoDirect₀ k
          omega⟩ := by
  show atomicTuple copy (eI i) (eJ j) (canonicalInternalIndex copy i₀ j₀ k) = _
  exact atomicTuple_canonicalInternalIndex_eq copy i₀ j₀ hNoDirect₀ (eI i) (eJ j) k

/-- The candidate map is injective, driven purely by `copy.injective`, the
injectivity of `eI`, `eJ`, and `canonicalInternalIndex_injective`. No
adjacency hypotheses are required. -/
private theorem candidateInducedMap_injective
    {r : ℕ} {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G)
    {m : ℕ} (eI eJ : Fin (m + 1) ↪ Fin n) (i₀ j₀ : Fin n)
    (hNoDirect₀ : ¬ G.Adj (leftRootVertex copy i₀) (rightRootVertex copy j₀)) :
    Function.Injective (candidateInducedMap copy eI eJ i₀ j₀) := by
  intro u v huv
  -- Reduce every branch to an equality inside `SubdividedBicliqueVert n (r + 1)`
  -- under `copy`, then peel `copy.injective`, then `eI.injective` / `eJ.injective`
  -- or `canonicalInternalIndex_injective` as needed.
  have key :
      ∀ {u v : SubdividedBicliqueVert (m + 1) (canonicalInternalLength copy i₀ j₀)},
        candidateInducedMap copy eI eJ i₀ j₀ u =
          candidateInducedMap copy eI eJ i₀ j₀ v → u = v := by
    intro u v huv
    have hPathDecode :
        ∀ (i j : Fin (m + 1)) (k : Fin (canonicalInternalLength copy i₀ j₀)),
          candidateInducedMap copy eI eJ i₀ j₀ (.inr ((i, j), k)) =
            copy (.inr ((eI i, eJ j),
              ⟨(canonicalInternalIndex copy i₀ j₀ k).val - 1, by
                have h1 := canonicalInternalIndex_val_pos copy i₀ j₀ hNoDirect₀ k
                have h2 := canonicalInternalIndex_val_lt copy i₀ j₀ hNoDirect₀ k
                omega⟩)) := by
      intro i j k
      have := candidateInducedMap_inr_eq_pathVertex copy eI eJ i₀ j₀ hNoDirect₀ i j k
      simpa [pathVertex] using this
    rcases u with ((i | j) | ⟨⟨i, j⟩, k⟩) <;>
      rcases v with ((i' | j') | ⟨⟨i', j'⟩, k'⟩) <;>
      simp only [candidateInducedMap_inl_inl, candidateInducedMap_inl_inr] at huv
    · -- left root = left root
      have hv : (Sum.inl (Sum.inl (eI i)) : SubdividedBicliqueVert n (r + 1)) =
          Sum.inl (Sum.inl (eI i')) :=
        copy.injective (by simpa [leftRootVertex] using huv)
      have : eI i = eI i' := by simpa using hv
      exact congrArg (fun x => (Sum.inl (Sum.inl x) : _)) (eI.injective this)
    · -- left root = right root: impossible
      exact absurd
        (copy.injective (by simpa [leftRootVertex, rightRootVertex] using huv))
        (by simp)
    · -- left root = path vertex: impossible
      rw [hPathDecode] at huv
      have hv := copy.injective (by simpa [leftRootVertex] using huv)
      simp at hv
    · -- right root = left root: impossible
      exact absurd
        (copy.injective (by simpa [leftRootVertex, rightRootVertex] using huv))
        (by simp)
    · -- right root = right root
      have hv : (Sum.inl (Sum.inr (eJ j)) : SubdividedBicliqueVert n (r + 1)) =
          Sum.inl (Sum.inr (eJ j')) :=
        copy.injective (by simpa [rightRootVertex] using huv)
      have : eJ j = eJ j' := by simpa using hv
      exact congrArg (fun x => (Sum.inl (Sum.inr x) : _)) (eJ.injective this)
    · -- right root = path vertex: impossible
      rw [hPathDecode] at huv
      have hv := copy.injective (by simpa [rightRootVertex] using huv)
      simp at hv
    · -- path vertex = left root: impossible
      rw [hPathDecode] at huv
      have hv := copy.injective (by simpa [leftRootVertex] using huv)
      simp at hv
    · -- path vertex = right root: impossible
      rw [hPathDecode] at huv
      have hv := copy.injective (by simpa [rightRootVertex] using huv)
      simp at hv
    · -- path vertex = path vertex
      rw [hPathDecode, hPathDecode] at huv
      have hv := copy.injective huv
      have hv' := Sum.inr.inj hv
      obtain ⟨hij, hk⟩ := Prod.mk.inj hv'
      obtain ⟨hi, hj⟩ := Prod.mk.inj hij
      have hi' := eI.injective hi
      have hj' := eJ.injective hj
      subst hi'; subst hj'
      have hk_val : (canonicalInternalIndex copy i₀ j₀ k).val - 1 =
          (canonicalInternalIndex copy i₀ j₀ k').val - 1 := by
        have := congrArg Fin.val hk
        simpa using this
      have hv1 := canonicalInternalIndex_val_pos copy i₀ j₀ hNoDirect₀ k
      have hv2 := canonicalInternalIndex_val_pos copy i₀ j₀ hNoDirect₀ k'
      have hidx :
          canonicalInternalIndex copy i₀ j₀ k =
            canonicalInternalIndex copy i₀ j₀ k' := by
        apply Fin.ext
        omega
      have := canonicalInternalIndex_injective copy i₀ j₀ hNoDirect₀ hidx
      subst this
      rfl
  exact key huv

/-- Proposition packaged by the remaining Step 5 argument after the direct
`aᵢ bⱼ`-edge branch has been excluded.

At the current scaffold stage this is intentionally the exact existential
statement consumed by the final theorem: the missing work is to extract a
common shortest-path profile from the Ramsey block and turn the resulting
cross-edge-free configuration into this induced-subdivision witness. -/
private def CrossEdgeFreeData (r : ℕ) {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (U : ℕ → ℕ) (n : ℕ)
    (_hsub : (subdividedBiclique n (r + 1)).IsContained G)
    (_I _J : Finset (Fin n)) : Prop :=
  ∃ r' : ℕ, 1 ≤ r' ∧ r' ≤ r + 1 ∧
    (subdividedBiclique (U n) r').IsIndContained G

/-- Remaining Step 5 scaffold: assuming the Ramsey block is cross-edge-free
(no direct `aᵢ bⱼ` edges and no cross-root / cross-internal edges between
different diagonals), extract the common shortest-path profile and package
the resulting induced subdivided biclique witness.

Source-proof pairing: the five `hNo*Cross` hypotheses are the five
"cross-edge-free" assumptions produced by the halving arguments in the
Mählmann proof — `hNoAACross` and `hNoBBCross` come from the "both root
sides are independent sets" reduction, and `hNoAQCross`, `hNoBQCross`,
`hNoQQCross` are the three semi-induced-biclique halvings for internal-vs-
root and internal-vs-internal cross edges. The caller
(`homogeneousCaseSplit`) is responsible for producing these hypotheses
from the Ramsey block (either directly or by branching to the biclique
alternative). -/
private theorem buildCrossEdgeFreeData (r : ℕ) {V : Type}
    [DecidableEq V] [Fintype V] (G : SimpleGraph V) (U : ℕ → ℕ) (n : ℕ)
    (hsub : (subdividedBiclique n (r + 1)).IsContained G)
    (I J : Finset (Fin n)) (hIcard : U n ≤ I.card) (hJcard : U n ≤ J.card)
    (hpaths : HasHomogeneousShortestPaths r G n hsub I J)
    (hNoDirectEdges :
      ∀ i, i ∈ I → ∀ j, j ∈ J →
        ¬ G.Adj (leftRootVertex hpaths.copy i) (rightRootVertex hpaths.copy j))
    (hNoAACross :
      ∀ i, i ∈ I → ∀ i', i' ∈ I → i ≠ i' →
        ¬ G.Adj (leftRootVertex hpaths.copy i) (leftRootVertex hpaths.copy i'))
    (hNoBBCross :
      ∀ j, j ∈ J → ∀ j', j' ∈ J → j ≠ j' →
        ¬ G.Adj (rightRootVertex hpaths.copy j) (rightRootVertex hpaths.copy j'))
    (hNoAQCross :
      ∀ i, i ∈ I → ∀ i', i' ∈ I → i ≠ i' → ∀ j', j' ∈ J →
        ∀ k : Fin (r + 1),
        ¬ G.Adj (leftRootVertex hpaths.copy i)
          (pathVertex hpaths.copy i' j' k))
    (hNoBQCross :
      ∀ j, j ∈ J → ∀ j', j' ∈ J → j ≠ j' → ∀ i', i' ∈ I →
        ∀ k : Fin (r + 1),
        ¬ G.Adj (rightRootVertex hpaths.copy j)
          (pathVertex hpaths.copy i' j' k))
    (hNoQQCross :
      ∀ i, i ∈ I → ∀ i', i' ∈ I → ∀ j, j ∈ J → ∀ j', j' ∈ J →
        (i, j) ≠ (i', j') → ∀ k k' : Fin (r + 1),
        ¬ G.Adj (pathVertex hpaths.copy i j k)
          (pathVertex hpaths.copy i' j' k')) :
    CrossEdgeFreeData r G U n hsub I J := by
  classical
  cases hUn : U n with
  | zero =>
      refine ⟨1, by simp, by omega, ?_⟩
      rw [hUn]
      simpa using subdividedBiclique_zero_isIndContained (r := 0) G
  | succ m =>
    let eI : Fin (Nat.succ m) ↪ Fin n := ramseyBlockLeftEmbedding I (by simpa [hUn] using hIcard)
    let eJ : Fin (Nat.succ m) ↪ Fin n := ramseyBlockRightEmbedding J (by simpa [hUn] using hJcard)
    have heI : ∀ x : Fin (Nat.succ m), eI x ∈ I := by
      intro x
      simpa [eI] using
        ramseyBlockLeftEmbedding_mem I (by simpa [hUn] using hIcard) x
    have heJ : ∀ x : Fin (Nat.succ m), eJ x ∈ J := by
      intro x
      simpa [eJ] using
        ramseyBlockRightEmbedding_mem J (by simpa [hUn] using hJcard) x
    let i₀ : Fin n := eI ⟨0, Nat.succ_pos m⟩
    let j₀ : Fin n := eJ ⟨0, Nat.succ_pos m⟩
    have hi₀ : i₀ ∈ I := heI ⟨0, Nat.succ_pos m⟩
    have hj₀ : j₀ ∈ J := heJ ⟨0, Nat.succ_pos m⟩
    have hNoDirect₀ :
        ¬ G.Adj (leftRootVertex hpaths.copy i₀) (rightRootVertex hpaths.copy j₀) :=
      hNoDirectEdges i₀ hi₀ j₀ hj₀
    have hGraphEq :
        ∀ {i j : Fin n}, i ∈ I → j ∈ J →
          tuplePositionGraph hpaths.copy i j = tuplePositionGraph hpaths.copy i₀ j₀ := by
      intro i j hi hj
      symm
      exact diagonal_tuplePositionGraph_eq hpaths hi₀ hi hj₀ hj
    -- The Step 5 internal path length `r' := dist - 1`, canonical on `(i₀, j₀)`.
    let r' : ℕ := canonicalInternalLength hpaths.copy i₀ j₀
    have hr'_pos : 1 ≤ r' :=
      one_le_canonicalInternalLength_of_no_direct hpaths.copy i₀ j₀ hNoDirect₀
    have hr'_le : r' ≤ r + 1 :=
      canonicalInternalLength_le hpaths.copy i₀ j₀
    -- The canonical shortest walk on `(i₀, j₀)` together with its internal
    -- position sequence is now entirely available as named API at this point.
    --   `canonicalShortestWalk hpaths.copy i₀ j₀` — a Walk in the base tuple
    --     position graph, with `.IsPath`, length `r' + 1`
    --     (`canonicalShortestWalk_length_eq_succ ... hNoDirect₀`).
    --   `canonicalInternalIndex hpaths.copy i₀ j₀ : Fin r' → Fin (r + 3)` —
    --     the ordered sequence `k₁, …, k_{r'}`, injective
    --     (`canonicalInternalIndex_injective`), strictly between `0` and
    --     `positionLast r` (`canonicalInternalIndex_val_pos/_lt`), adjacent
    --     consecutively and to the endpoints
    --     (`tuplePositionGraph_adj_canonicalInternalIndex_succ/_zero/_last`),
    --     and decoded by `atomicTuple` into path vertices via
    --     `atomicTuple_canonicalInternalIndex_eq`.
    have hlenCanon : (canonicalShortestWalk hpaths.copy i₀ j₀).length = r' + 1 :=
      canonicalShortestWalk_length_eq_succ hpaths.copy i₀ j₀ hNoDirect₀
    have hCanonPath : (canonicalShortestWalk hpaths.copy i₀ j₀).IsPath :=
      canonicalShortestWalk_isPath hpaths.copy i₀ j₀
    refine ⟨r', hr'_pos, hr'_le, ?_⟩
    rw [hUn]
    -- Package `candidateInducedMap` + `candidateInducedMap_injective` into a
    -- `SimpleGraph.Embedding (subdividedBiclique (m + 1) r') G`. The remaining
    -- work is exactly the `Adj ↔ Adj` direction.
    refine ⟨⟨⟨candidateInducedMap hpaths.copy eI eJ i₀ j₀,
            candidateInducedMap_injective hpaths.copy eI eJ i₀ j₀ hNoDirect₀⟩,
          ?_⟩⟩
    -- Remaining gap: the `map_rel_iff'` clause of the `SimpleGraph.Embedding`.
    -- goal: ∀ {u v : SubdividedBicliqueVert (m + 1) r'},
    --         G.Adj (candidateInducedMap hpaths.copy eI eJ i₀ j₀ u)
    --               (candidateInducedMap hpaths.copy eI eJ i₀ j₀ v) ↔
    --           (subdividedBiclique (m + 1) r').Adj u v
    intro u v
    refine ⟨?mp, ?mpr⟩
    · -- `mp`: G-adjacency of the images forces adjacency in `subdividedBiclique`.
      --
      -- Block B (same diagonal, closed): non-adjacency of non-consecutive
      -- vertices on the canonical walk, by `walk_noChord_of_length_eq_dist`
      -- applied to `canonicalShortestWalk hpaths.copy i₀ j₀` (length = `dist`)
      -- and transported to `(eI i, eJ j)` via `hGraphEq`. Cross-root direct
      -- edges (a-b / b-a) are ruled out by `hNoDirectEdges`.
      --
      -- Block C (off-diagonal, closed): three cross-edge types —
      -- `a-a`/`b-b`, `a-q`/`b-q`/`q-a`/`q-b`, and `q-q` with
      -- `(i, j) ≠ (i', j')`. Each is now ruled out directly by one of the
      -- `hNo*Cross` hypotheses. Producing those hypotheses is now Block D,
      -- lifted to the caller `homogeneousCaseSplit`.
      intro h
      change G.Adj (candidateInducedMap hpaths.copy eI eJ i₀ j₀ u)
                  (candidateInducedMap hpaths.copy eI eJ i₀ j₀ v) at h
      -- Transport: adjacency at any block pair equals adjacency at the base
      -- pair `(i₀, j₀)`.
      have hTransport :
          ∀ (i j : Fin (m + 1)) {s t : Fin (r + 3)},
            (tuplePositionGraph hpaths.copy (eI i) (eJ j)).Adj s t →
            (tuplePositionGraph hpaths.copy i₀ j₀).Adj s t := by
        intro i j s t hadj
        exact hGraphEq (heI i) (heJ j) ▸ hadj
      -- Canonical-walk no-chord: positions in `tuplePositionGraph i₀ j₀` that
      -- are adjacent on the canonical shortest walk are forced to be
      -- consecutive walk positions.
      have hlenDist : (canonicalShortestWalk hpaths.copy i₀ j₀).length =
          (tuplePositionGraph hpaths.copy i₀ j₀).dist
            ⟨0, by omega⟩ (positionLast r) :=
        canonicalShortestWalk_length_eq_dist hpaths.copy i₀ j₀
      have hStart :
          (canonicalShortestWalk hpaths.copy i₀ j₀).getVert 0 =
            (⟨0, by omega⟩ : Fin (r + 3)) := by
        simp
      have hEnd :
          (canonicalShortestWalk hpaths.copy i₀ j₀).getVert (r' + 1) =
            positionLast r := by
        rw [show r' + 1 = (canonicalShortestWalk hpaths.copy i₀ j₀).length
              from hlenCanon.symm]
        simp
      -- `noChord pos₁ pos₂`: if positions `pos₁ < pos₂` on the canonical walk
      -- are `tuplePositionGraph`-adjacent, then `pos₂ = pos₁ + 1`.
      have noChord :
          ∀ {p₁ p₂ : ℕ}, p₁ < p₂ → p₂ ≤ r' + 1 →
            (tuplePositionGraph hpaths.copy i₀ j₀).Adj
              ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert p₁)
              ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert p₂) →
            p₂ = p₁ + 1 := by
        intro p₁ p₂ hlt hle hadj
        have hlen' : (canonicalShortestWalk hpaths.copy i₀ j₀).length =
            (tuplePositionGraph hpaths.copy i₀ j₀).dist ⟨0, by omega⟩
              (positionLast r) := hlenDist
        have hp1 : p₁ ≤ (canonicalShortestWalk hpaths.copy i₀ j₀).length := by
          rw [hlenCanon]; omega
        have hp2 : p₂ ≤ (canonicalShortestWalk hpaths.copy i₀ j₀).length := by
          rw [hlenCanon]; exact hle
        exact walk_noChord_of_length_eq_dist
          (canonicalShortestWalk hpaths.copy i₀ j₀) hlen' hp1 hp2 hlt hadj
      rcases u with ((i | j) | ⟨⟨i, j⟩, k⟩) <;>
        rcases v with ((i' | j') | ⟨⟨i', j'⟩, k'⟩) <;>
        dsimp only [candidateInducedMap] at h
      · -- `(a_i, a_{i'})`: `a`s form an independent set on the Ramsey block,
        -- so `hNoAACross` rules out any adjacency between two distinct left
        -- roots. Loop `i = i'` contradicts `G`'s irreflexivity.
        exfalso
        rcases eq_or_ne i i' with rfl | hii
        · exact h.ne rfl
        · exact hNoAACross (eI i) (heI i) (eI i') (heI i')
            (fun heq => hii (eI.injective heq)) h
      · -- `(a_i, b_{j'})`: direct edge ruled out by `hNoDirectEdges`.
        exact absurd h (hNoDirectEdges (eI i) (heI i) (eJ j') (heJ j'))
      · -- `(a_i, q_{i', j', k'})`.
        by_cases hii : i = i'
        · -- Block B: same i. Force `k'.val = 0` via no-chord on canonical walk.
          subst hii
          -- Convert h to a `tuplePositionGraph (eI i) (eJ j')` adjacency at
          -- positions `0` and `canonicalInternalIndex i₀ j₀ k'`.
          have h0 : leftRootVertex hpaths.copy (eI i) =
              atomicTuple hpaths.copy (eI i) (eJ j') (⟨0, by omega⟩ : Fin (r + 3)) := by
            simp [atomicTuple]
          rw [h0] at h
          have hadjPair :
              (tuplePositionGraph hpaths.copy (eI i) (eJ j')).Adj
                ⟨0, by omega⟩ (canonicalInternalIndex hpaths.copy i₀ j₀ k') := h
          have hadjBase :
              (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                ⟨0, by omega⟩ (canonicalInternalIndex hpaths.copy i₀ j₀ k') :=
            (hGraphEq (heI i) (heJ j')) ▸ hadjPair
          -- Apply no-chord with p₁ := 0, p₂ := k'.val + 1.
          have hadj' :
              (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert 0)
                ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                  (k'.val + 1)) := by
            rw [hStart]
            show (tuplePositionGraph hpaths.copy i₀ j₀).Adj
              ⟨0, by omega⟩ (canonicalInternalIndex hpaths.copy i₀ j₀ k')
            exact hadjBase
          have hk' : k'.val + 1 = 0 + 1 :=
            noChord (by omega) (by have := k'.isLt; omega) hadj'
          have hk'_zero : k'.val = 0 := by omega
          refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_, Or.inl ?_⟩
          · simp
          · exact ⟨rfl, hk'_zero⟩
        · -- Block C: i ≠ i', off-diagonal a-q. Rule out via `hNoAQCross`
          -- after decoding the atomicTuple into `pathVertex` at the canonical
          -- internal index.
          exfalso
          rw [atomicTuple_canonicalInternalIndex_eq hpaths.copy i₀ j₀
                hNoDirect₀ (eI i') (eJ j') k'] at h
          exact hNoAQCross (eI i) (heI i) (eI i') (heI i')
            (fun heq => hii (eI.injective heq)) (eJ j') (heJ j') _ h
      · -- `(b_j, a_{i'})`: direct edge ruled out by `hNoDirectEdges`.
        have h' := h.symm
        exact absurd h' (hNoDirectEdges (eI i') (heI i') (eJ j) (heJ j))
      · -- `(b_j, b_{j'})`: symmetric to `(a, a)`. Use `hNoBBCross` and
        -- irreflexivity.
        exfalso
        rcases eq_or_ne j j' with rfl | hjj
        · exact h.ne rfl
        · exact hNoBBCross (eJ j) (heJ j) (eJ j') (heJ j')
            (fun heq => hjj (eJ.injective heq)) h
      · -- `(b_j, q_{i', j', k'})`.
        by_cases hjj : j = j'
        · -- Block B: same j. Force `k'.val = r' - 1` via no-chord.
          subst hjj
          have hLast : rightRootVertex hpaths.copy (eJ j) =
              atomicTuple hpaths.copy (eI i') (eJ j) (positionLast r) :=
            (atomicTuple_positionLast hpaths.copy (eI i') (eJ j)).symm
          rw [hLast] at h
          have hadjPair :
              (tuplePositionGraph hpaths.copy (eI i') (eJ j)).Adj
                (positionLast r) (canonicalInternalIndex hpaths.copy i₀ j₀ k') := h
          have hadjBase :
              (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                (positionLast r) (canonicalInternalIndex hpaths.copy i₀ j₀ k') :=
            (hGraphEq (heI i') (heJ j)) ▸ hadjPair
          -- Apply no-chord with p₁ := k'.val + 1, p₂ := r' + 1.
          have hadj' :
              (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                  (k'.val + 1))
                ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                  (r' + 1)) := by
            rw [hEnd]
            show (tuplePositionGraph hpaths.copy i₀ j₀).Adj
              (canonicalInternalIndex hpaths.copy i₀ j₀ k') (positionLast r)
            exact hadjBase.symm
          have hk' : r' + 1 = k'.val + 1 + 1 :=
            noChord (by have := k'.isLt; omega) (by omega) hadj'
          have hk'_eq : k'.val = r' - 1 := by omega
          refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_, Or.inl ?_⟩
          · simp
          · exact ⟨rfl, hk'_eq⟩
        · -- Block C: j ≠ j', off-diagonal b-q. Rule out via `hNoBQCross`
          -- after decoding the atomicTuple into `pathVertex`.
          exfalso
          rw [atomicTuple_canonicalInternalIndex_eq hpaths.copy i₀ j₀
                hNoDirect₀ (eI i') (eJ j') k'] at h
          exact hNoBQCross (eJ j) (heJ j) (eJ j') (heJ j')
            (fun heq => hjj (eJ.injective heq)) (eI i') (heI i') _ h
      · -- `(q_{i, j, k}, a_{i'})`: symmetric to `(a, q)`.
        by_cases hii : i = i'
        · subst hii
          have h0 : leftRootVertex hpaths.copy (eI i) =
              atomicTuple hpaths.copy (eI i) (eJ j) (⟨0, by omega⟩ : Fin (r + 3)) := by
            simp [atomicTuple]
          rw [h0] at h
          have hadjPair :
              (tuplePositionGraph hpaths.copy (eI i) (eJ j)).Adj
                (canonicalInternalIndex hpaths.copy i₀ j₀ k) ⟨0, by omega⟩ := h
          have hadjBase :
              (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                ⟨0, by omega⟩ (canonicalInternalIndex hpaths.copy i₀ j₀ k) :=
            ((hGraphEq (heI i) (heJ j)) ▸ hadjPair).symm
          have hadj' :
              (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert 0)
                ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                  (k.val + 1)) := by
            rw [hStart]
            show (tuplePositionGraph hpaths.copy i₀ j₀).Adj
              ⟨0, by omega⟩ (canonicalInternalIndex hpaths.copy i₀ j₀ k)
            exact hadjBase
          have hk : k.val + 1 = 0 + 1 :=
            noChord (by omega) (by have := k.isLt; omega) hadj'
          have hk_zero : k.val = 0 := by omega
          refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_, Or.inr ?_⟩
          · simp
          · exact ⟨rfl, hk_zero⟩
        · -- Block C: i ≠ i', off-diagonal q-a. Symmetric to `(a, q)`; flip `h`
          -- and apply `hNoAQCross`.
          exfalso
          rw [atomicTuple_canonicalInternalIndex_eq hpaths.copy i₀ j₀
                hNoDirect₀ (eI i) (eJ j) k] at h
          exact hNoAQCross (eI i') (heI i') (eI i) (heI i)
            (fun heq => hii (eI.injective heq).symm) (eJ j) (heJ j) _ h.symm
      · -- `(q_{i, j, k}, b_{j'})`: symmetric to `(b, q)`.
        by_cases hjj : j = j'
        · subst hjj
          have hLast : rightRootVertex hpaths.copy (eJ j) =
              atomicTuple hpaths.copy (eI i) (eJ j) (positionLast r) :=
            (atomicTuple_positionLast hpaths.copy (eI i) (eJ j)).symm
          rw [hLast] at h
          have hadjPair :
              (tuplePositionGraph hpaths.copy (eI i) (eJ j)).Adj
                (canonicalInternalIndex hpaths.copy i₀ j₀ k) (positionLast r) := h
          have hadjBase :
              (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                (positionLast r) (canonicalInternalIndex hpaths.copy i₀ j₀ k) :=
            ((hGraphEq (heI i) (heJ j)) ▸ hadjPair).symm
          have hadj' :
              (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                  (k.val + 1))
                ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                  (r' + 1)) := by
            rw [hEnd]
            show (tuplePositionGraph hpaths.copy i₀ j₀).Adj
              (canonicalInternalIndex hpaths.copy i₀ j₀ k) (positionLast r)
            exact hadjBase.symm
          have hk : r' + 1 = k.val + 1 + 1 :=
            noChord (by have := k.isLt; omega) (by omega) hadj'
          have hk_eq : k.val = r' - 1 := by omega
          refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_, Or.inr ?_⟩
          · simp
          · exact ⟨rfl, hk_eq⟩
        · -- Block C: j ≠ j', off-diagonal q-b. Symmetric to `(b, q)`; flip `h`
          -- and apply `hNoBQCross`.
          exfalso
          rw [atomicTuple_canonicalInternalIndex_eq hpaths.copy i₀ j₀
                hNoDirect₀ (eI i) (eJ j) k] at h
          exact hNoBQCross (eJ j') (heJ j') (eJ j) (heJ j)
            (fun heq => hjj (eJ.injective heq).symm) (eI i) (heI i) _ h.symm
      · -- `(q_{i, j, k}, q_{i', j', k'})`.
        by_cases hij : (i, j) = (i', j')
        · -- Block B: same diagonal. Force `k.val + 1 = k'.val` (or vice versa)
          -- via no-chord on canonical walk.
          obtain ⟨hii, hjj⟩ := Prod.mk.inj hij
          subst hii; subst hjj
          have hadjPair :
              (tuplePositionGraph hpaths.copy (eI i) (eJ j)).Adj
                (canonicalInternalIndex hpaths.copy i₀ j₀ k)
                (canonicalInternalIndex hpaths.copy i₀ j₀ k') := h
          have hadjBase :
              (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                (canonicalInternalIndex hpaths.copy i₀ j₀ k)
                (canonicalInternalIndex hpaths.copy i₀ j₀ k') :=
            (hGraphEq (heI i) (heJ j)) ▸ hadjPair
          rcases lt_trichotomy k.val k'.val with hlt | heq | hgt
          · -- k.val < k'.val: forces k'.val = k.val + 1.
            have hadj' :
                (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                  ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                    (k.val + 1))
                  ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                    (k'.val + 1)) := hadjBase
            have hkk : k'.val + 1 = k.val + 1 + 1 :=
              noChord (by omega) (by have := k'.isLt; omega) hadj'
            have hkk' : k.val + 1 = k'.val := by omega
            refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_, Or.inl ?_⟩
            · intro hcontra
              have := Sum.inr.inj hcontra
              have hkeq : k = k' := (Prod.mk.inj this).2
              omega
            · exact ⟨rfl, hkk'⟩
          · -- k.val = k'.val: contradicts loopless of tuplePositionGraph.
            exfalso
            have hkeq : k = k' := Fin.ext heq
            subst hkeq
            exact hadjBase.ne rfl
          · -- k.val > k'.val: symmetric — forces k.val = k'.val + 1.
            have hadj' :
                (tuplePositionGraph hpaths.copy i₀ j₀).Adj
                  ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                    (k'.val + 1))
                  ((canonicalShortestWalk hpaths.copy i₀ j₀).getVert
                    (k.val + 1)) := hadjBase.symm
            have hkk : k.val + 1 = k'.val + 1 + 1 :=
              noChord (by omega) (by have := k.isLt; omega) hadj'
            have hkk' : k'.val + 1 = k.val := by omega
            refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_, Or.inr ?_⟩
            · intro hcontra
              have := Sum.inr.inj hcontra
              have hkeq : k = k' := (Prod.mk.inj this).2
              omega
            · exact ⟨rfl, hkk'⟩
        · -- Block C: off-diagonal q-q. Decode both atomicTuples into
          -- `pathVertex`s and rule out via `hNoQQCross`.
          exfalso
          rw [atomicTuple_canonicalInternalIndex_eq hpaths.copy i₀ j₀
                hNoDirect₀ (eI i) (eJ j) k,
              atomicTuple_canonicalInternalIndex_eq hpaths.copy i₀ j₀
                hNoDirect₀ (eI i') (eJ j') k'] at h
          have hne : (eI i, eJ j) ≠ (eI i', eJ j') := by
            intro heq
            obtain ⟨hi, hj⟩ := Prod.mk.inj heq
            exact hij (by rw [eI.injective hi, eJ.injective hj])
          exact hNoQQCross (eI i) (heI i) (eI i') (heI i')
            (eJ j) (heJ j) (eJ j') (heJ j') hne _ _ h
    · -- `mpr` = Block A (no halving): adjacency in
      -- `subdividedBiclique (m + 1) r'` is realised by G.
      --
      -- 9-case analysis on `u`, `v`. After `simp [subdividedBiclique] at h`,
      -- the two trivial diagonals (`(aᵢ, aᵢ')` and `(bⱼ, bⱼ')`) close
      -- automatically; the cross-root case (`aᵢ ∼ bⱼ`) forces `r' = 0`,
      -- contradicting `hr'_pos`; the remaining five cases use one of the
      -- three canonical-walk adjacency lemmas transported from `(i₀, j₀)`
      -- to `(eI i, eJ j)` via `hGraphEq`.
      intro h
      -- Transport: adjacency in the base tuple position graph equals
      -- adjacency at any block pair. Uses `hGraphEq` via rewriting.
      have hTransport :
          ∀ (i j : Fin (m + 1)) {s t : Fin (r + 3)},
            (tuplePositionGraph hpaths.copy i₀ j₀).Adj s t →
            (tuplePositionGraph hpaths.copy (eI i) (eJ j)).Adj s t := by
        intro i j s t hadj
        have hEq :
            tuplePositionGraph hpaths.copy i₀ j₀ =
              tuplePositionGraph hpaths.copy (eI i) (eJ j) :=
          (hGraphEq (heI i) (heJ j)).symm
        exact hEq ▸ hadj
      rcases u with ((i | j) | ⟨⟨i, j⟩, k⟩) <;>
        rcases v with ((i' | j') | ⟨⟨i', j'⟩, k'⟩) <;>
        simp [subdividedBiclique] at h
      · -- `(aᵢ, bⱼ')`: would need `r' = 0`, contradicting `hr'_pos`.
        exfalso; omega
      · -- `(aᵢ, p_{i', j', k'})`: `i = i'` and `k'.val = 0`.
        -- Use `tuplePositionGraph_adj_zero_canonicalInternalIndex` at
        -- `(i₀, j₀)`, transported to `(eI i, eJ j')`.
        obtain ⟨hii, hk0⟩ := h
        subst hii
        have hk_eq : k' = (⟨0, hr'_pos⟩ : Fin r') := Fin.ext hk0
        have hAdj0 := tuplePositionGraph_adj_zero_canonicalInternalIndex
            hpaths.copy i₀ j₀ hNoDirect₀ hr'_pos
        have hAdjPair := hTransport i j' hAdj0
        have h0 : atomicTuple hpaths.copy (eI i) (eJ j')
            (⟨0, by omega⟩ : Fin (r + 3)) =
            leftRootVertex hpaths.copy (eI i) := by
          simp [atomicTuple]
        show G.Adj (leftRootVertex hpaths.copy (eI i))
            (atomicTuple hpaths.copy (eI i) (eJ j')
              (canonicalInternalIndex hpaths.copy i₀ j₀ k'))
        rw [hk_eq, ← h0]
        exact hAdjPair
      · -- `(bⱼ, aᵢ')`: would need `r' = 0`, contradicting `hr'_pos`.
        exfalso; omega
      · -- `(bⱼ, p_{i', j', k'})`: `j = j'` and `k'.val = r' - 1`.
        -- Use `tuplePositionGraph_adj_canonicalInternalIndex_last` at
        -- `(i₀, j₀)`, transported to `(eI i', eJ j)`, then flip.
        obtain ⟨hjj, hkR⟩ := h
        subst hjj
        have hk_eq : k' = (⟨r' - 1, by omega⟩ : Fin r') := Fin.ext hkR
        have hsucc : (⟨r' - 1, by omega⟩ : Fin r').val + 1 = r' := by
          show (r' - 1) + 1 = r'
          omega
        have hAdjLast := tuplePositionGraph_adj_canonicalInternalIndex_last
            hpaths.copy i₀ j₀ hNoDirect₀ ⟨r' - 1, by omega⟩ hsucc
        have hAdjPair := hTransport i' j hAdjLast
        have hLast : atomicTuple hpaths.copy (eI i') (eJ j) (positionLast r) =
            rightRootVertex hpaths.copy (eJ j) :=
          atomicTuple_positionLast hpaths.copy (eI i') (eJ j)
        show G.Adj (rightRootVertex hpaths.copy (eJ j))
            (atomicTuple hpaths.copy (eI i') (eJ j)
              (canonicalInternalIndex hpaths.copy i₀ j₀ k'))
        rw [hk_eq, ← hLast]
        exact hAdjPair.symm
      · -- `(p_{i, j, k}, aᵢ')`: symmetric to the `(a, p)` case.
        obtain ⟨hii, hk0⟩ := h
        subst hii
        have hk_eq : k = (⟨0, hr'_pos⟩ : Fin r') := Fin.ext hk0
        have hAdj0 := tuplePositionGraph_adj_zero_canonicalInternalIndex
            hpaths.copy i₀ j₀ hNoDirect₀ hr'_pos
        have hAdjPair := hTransport i' j hAdj0
        have h0 : atomicTuple hpaths.copy (eI i') (eJ j)
            (⟨0, by omega⟩ : Fin (r + 3)) =
            leftRootVertex hpaths.copy (eI i') := by
          simp [atomicTuple]
        show G.Adj (atomicTuple hpaths.copy (eI i') (eJ j)
              (canonicalInternalIndex hpaths.copy i₀ j₀ k))
            (leftRootVertex hpaths.copy (eI i'))
        rw [hk_eq, ← h0]
        exact hAdjPair.symm
      · -- `(p_{i, j, k}, bⱼ')`: symmetric to the `(b, p)` case.
        obtain ⟨hjj, hkR⟩ := h
        subst hjj
        have hk_eq : k = (⟨r' - 1, by omega⟩ : Fin r') := Fin.ext hkR
        have hsucc : (⟨r' - 1, by omega⟩ : Fin r').val + 1 = r' := by
          show (r' - 1) + 1 = r'
          omega
        have hAdjLast := tuplePositionGraph_adj_canonicalInternalIndex_last
            hpaths.copy i₀ j₀ hNoDirect₀ ⟨r' - 1, by omega⟩ hsucc
        have hAdjPair := hTransport i j' hAdjLast
        have hLast : atomicTuple hpaths.copy (eI i) (eJ j') (positionLast r) =
            rightRootVertex hpaths.copy (eJ j') :=
          atomicTuple_positionLast hpaths.copy (eI i) (eJ j')
        show G.Adj (atomicTuple hpaths.copy (eI i) (eJ j')
              (canonicalInternalIndex hpaths.copy i₀ j₀ k))
            (rightRootVertex hpaths.copy (eJ j'))
        rw [hk_eq, ← hLast]
        exact hAdjPair
      · -- `(p_{i, j, k}, p_{i', j', k'})`: same diagonal, consecutive
        -- `k`. Use `tuplePositionGraph_adj_canonicalInternalIndex_succ`.
        obtain ⟨_, hrel⟩ := h
        rcases hrel with ⟨⟨hii, hjj⟩, hkk⟩ | ⟨⟨hii, hjj⟩, hkk⟩
        · -- `k.val + 1 = k'.val`
          subst hii; subst hjj
          have hsucc : k.val + 1 < r' := by
            have := k'.isLt
            omega
          have hk'_eq : k' = (⟨k.val + 1, hsucc⟩ : Fin r') :=
            Fin.ext hkk.symm
          have hAdjSucc := tuplePositionGraph_adj_canonicalInternalIndex_succ
              hpaths.copy i₀ j₀ hNoDirect₀ k hsucc
          have hAdjPair := hTransport i j hAdjSucc
          show G.Adj (atomicTuple hpaths.copy (eI i) (eJ j)
                (canonicalInternalIndex hpaths.copy i₀ j₀ k))
              (atomicTuple hpaths.copy (eI i) (eJ j)
                (canonicalInternalIndex hpaths.copy i₀ j₀ k'))
          rw [hk'_eq]
          exact hAdjPair
        · -- `k'.val + 1 = k.val`; symmetric (`i' = i`, `j' = j`).
          subst hii; subst hjj
          have hsucc : k'.val + 1 < r' := by
            have := k.isLt
            omega
          have hk_eq : k = (⟨k'.val + 1, hsucc⟩ : Fin r') :=
            Fin.ext hkk.symm
          have hAdjSucc := tuplePositionGraph_adj_canonicalInternalIndex_succ
              hpaths.copy i₀ j₀ hNoDirect₀ k' hsucc
          have hAdjPair := hTransport i' j' hAdjSucc
          show G.Adj (atomicTuple hpaths.copy (eI i') (eJ j')
                (canonicalInternalIndex hpaths.copy i₀ j₀ k))
              (atomicTuple hpaths.copy (eI i') (eJ j')
                (canonicalInternalIndex hpaths.copy i₀ j₀ k'))
          rw [hk_eq]
          exact hAdjPair.symm

private theorem bipartiteHomogeneity (r : ℕ) :
    ∃ U : ℕ → ℕ, Monotone U ∧ (∀ N : ℕ, ∃ n : ℕ, N ≤ U n) ∧
      ∀ (n : ℕ)
        (c : (Fin 2 → Fin n) → (Fin 2 → Fin n) → Fin (Fintype.card (AtomicType r))),
        ∃ I J : Finset (Fin n),
          U n ≤ I.card ∧ U n ≤ J.card ∧
          ∃ f : (Fin 2 × Fin 2 → Ordering) →
                (Fin 2 × Fin 2 → Ordering) → Fin (Fintype.card (AtomicType r)),
            ∀ (a : Fin 2 → Fin n) (b : Fin 2 → Fin n),
              (∀ i, a i ∈ I) → (∀ j, b j ∈ J) →
                c a b = f (TupleRamsey.orderType a)
                  (TupleRamsey.orderType b) := by
  simpa [AtomicType] using TupleRamsey.bipartite_tuple_ramsey
    (Fintype.card (AtomicType r)) 2 2
    (atomicType_card_pos r)

private noncomputable def buildAtomicTypeColoring (r : ℕ) {V : Type}
    [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (n : ℕ)
    (hsub : (subdividedBiclique n (r + 1)).IsContained G) :
    Σ c : (Fin 2 → Fin n) → (Fin 2 → Fin n) → Fin (Fintype.card (AtomicType r)),
      HasAtomicTypeColoring r G n hsub c := by
  classical
  let copy : SimpleGraph.Copy (subdividedBiclique n (r + 1)) G := Classical.choice hsub
  refine ⟨fun a b => atomicTypeEquivFin r (atomicTypeOf G copy a b), ?_⟩
  exact { copy := copy, color_eq := fun _ _ => rfl }

private noncomputable def extractHomogeneousShortestPaths (r : ℕ) {V : Type}
    [DecidableEq V] [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (hsub : (subdividedBiclique n (r + 1)).IsContained G)
    (I J : Finset (Fin n))
    (c : (Fin 2 → Fin n) → (Fin 2 → Fin n) → Fin (Fintype.card (AtomicType r)))
    (hc : HasAtomicTypeColoring r G n hsub c)
    (f : (Fin 2 × Fin 2 → Ordering) →
      (Fin 2 × Fin 2 → Ordering) → Fin (Fintype.card (AtomicType r)))
    (_hf : ∀ (a : Fin 2 → Fin n) (b : Fin 2 → Fin n),
      (∀ i, a i ∈ I) → (∀ j, b j ∈ J) →
        c a b = f (TupleRamsey.orderType a)
          (TupleRamsey.orderType b)) :
    HasHomogeneousShortestPaths r G n hsub I J := by
  have hdiag_color :
      ∀ {i i' j j' : Fin n},
        i ∈ I → i' ∈ I → j ∈ J → j' ∈ J →
          c (diagPair i) (diagPair j) = c (diagPair i') (diagPair j') := by
    intro i i' j j' hi hi' hj hj'
    rw [_hf (diagPair i) (diagPair j) (by intro a; simp [diagPair, hi])
        (by intro b; simp [diagPair, hj])]
    rw [_hf (diagPair i') (diagPair j') (by intro a; simp [diagPair, hi'])
        (by intro b; simp [diagPair, hj'])]
    simp [orderType_diagPair]
  exact
    { copy := hc.copy
      shortestPath := fun i j => shortestTuplePath hc.copy i j
      shortestPath_length_eq_dist := fun i j => shortestTuplePath_length_eq_dist hc.copy i j
      atomicType_eq_of_orderType := by
        intro a a' b b' ha ha' hb hb' hota hotb
        apply (atomicTypeEquivFin r).injective
        rw [← hc.color_eq a b, ← hc.color_eq a' b']
        rw [_hf a b ha hb, _hf a' b' ha' hb']
        simp [hota, hotb]
      diagonal_atomicType_eq := by
        intro i i' j j' hi hi' hj hj'
        apply (atomicTypeEquivFin r).injective
        rw [← hc.color_eq (diagPair i) (diagPair j)]
        rw [← hc.color_eq (diagPair i') (diagPair j')]
        exact hdiag_color hi hi' hj hj' }

private theorem homogeneousCaseSplit (r : ℕ) {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (U : ℕ → ℕ) (n : ℕ)
    (hsub : (subdividedBiclique n (r + 1)).IsContained G)
    (I J : Finset (Fin n)) (hIcard : 2 * U n ≤ I.card) (hJcard : 2 * U n ≤ J.card)
    (hpaths : HasHomogeneousShortestPaths r G n hsub I J) :
    (biclique (U n)).IsContained G ∨ CrossEdgeFreeData r G U n hsub I J := by
  classical
  have hIcard' : U n ≤ I.card := by omega
  have hJcard' : U n ≤ J.card := by omega
  by_cases hU : U n = 0
  · -- `biclique 0` is the empty graph, trivially contained.
    left
    rw [hU]
    refine biclique_isContained_of_leftLeftComplete hpaths.copy
      (∅ : Finset (Fin n)) (∅ : Finset (Fin n)) ?_ ?_ ?_
    · simp
    · simp
    · intro i hi _ _
      exact absurd hi (Finset.notMem_empty _)
  · have hUpos : 0 < U n := Nat.pos_of_ne_zero hU
    -- Pick reference elements for the adjacency-homogeneity transports.
    have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨iStar, hiStar⟩ := hIne
    obtain ⟨jStar, hjStar⟩ := hJne
    by_cases hEdge :
        ∃ i, i ∈ I ∧ ∃ j, j ∈ J ∧
          G.Adj (leftRootVertex hpaths.copy i) (rightRootVertex hpaths.copy j)
    · -- Case A: direct `aᵢ–bⱼ` edge. Full `I × J` is a biclique.
      left
      rcases hEdge with ⟨i₀, hi₀, j₀, hj₀, hAdj₀⟩
      refine biclique_isContained_of_completeRoots hpaths.copy I J hIcard' hJcard' ?_
      intro i hi j hj
      exact (diagonal_left_right_adj_iff hpaths hi hi₀ hj hj₀).2 hAdj₀
    · have hNoDirect : ∀ i, i ∈ I → ∀ j, j ∈ J →
          ¬ G.Adj (leftRootVertex hpaths.copy i) (rightRootVertex hpaths.copy j) := by
        intro i hi j hj hij
        exact hEdge ⟨i, hi, j, hj, hij⟩
      by_cases hAA :
          ∃ i, i ∈ I ∧ ∃ i', i' ∈ I ∧ i ≠ i' ∧
            G.Adj (leftRootVertex hpaths.copy i) (leftRootVertex hpaths.copy i')
      · -- Block D-1: an `aᵢ ∼ aᵢ'` cross edge exists. By orderType
        -- homogeneity, every strictly-ordered pair `(i, i')` in `I × I` has
        -- the same adjacency. Halve `I` into its smallest / largest `U n`
        -- elements and package via `biclique_isContained_of_leftLeftComplete`.
        left
        obtain ⟨iW₀, hiW₀, iW₁, hiW₁, hneW, hAdjW⟩ := hAA
        -- WLOG the witnessed pair is strictly ordered.
        have hWit : ∃ x y, x ∈ I ∧ y ∈ I ∧ x < y ∧
            G.Adj (leftRootVertex hpaths.copy x) (leftRootVertex hpaths.copy y) := by
          rcases lt_or_gt_of_ne hneW with h | h
          · exact ⟨iW₀, iW₁, hiW₀, hiW₁, h, hAdjW⟩
          · exact ⟨iW₁, iW₀, hiW₁, hiW₀, h, hAdjW.symm⟩
        obtain ⟨xW, yW, hxW, hyW, hltW, hAdjW⟩ := hWit
        -- Halves of `I`.
        refine biclique_isContained_of_leftLeftComplete hpaths.copy
          (firstHalfFinset I hIcard') (lastHalfFinset I hIcard')
          (by rw [firstHalfFinset_card]) (by rw [lastHalfFinset_card]) ?_
        intro i hiL i' hi'R
        have hiI : i ∈ I := firstHalfFinset_subset I hIcard' hiL
        have hi'I : i' ∈ I := lastHalfFinset_subset I hIcard' hi'R
        have hlt : i < i' := firstHalfFinset_lt_lastHalfFinset I hIcard hiL hi'R
        have hOtI := orderType_pairTuple_eq_of_lt hltW hlt
        have hPair := pair_atomicTuple_adj_iff hpaths
          (i₀ := xW) (i₁ := yW) (i₀' := i) (i₁' := i')
          (j₀ := jStar) (j₁ := jStar) (j₀' := jStar) (j₁' := jStar)
          (s := 0) (t := 0)
          (by intro t; fin_cases t <;> simp [pairTuple, hxW, hyW])
          (by intro t; fin_cases t <;> simp [pairTuple, hiI, hi'I])
          (by intro t; fin_cases t <;> simp [pairTuple, hjStar])
          (by intro t; fin_cases t <;> simp [pairTuple, hjStar])
          hOtI rfl
        rw [atomicTuple_zero, atomicTuple_zero, atomicTuple_zero, atomicTuple_zero] at hPair
        exact hPair.mp hAdjW
      · have hNoAA : ∀ i, i ∈ I → ∀ i', i' ∈ I → i ≠ i' →
            ¬ G.Adj (leftRootVertex hpaths.copy i) (leftRootVertex hpaths.copy i') := by
          intro i hi i' hi' hne hij
          exact hAA ⟨i, hi, i', hi', hne, hij⟩
        by_cases hBB :
            ∃ j, j ∈ J ∧ ∃ j', j' ∈ J ∧ j ≠ j' ∧
              G.Adj (rightRootVertex hpaths.copy j) (rightRootVertex hpaths.copy j')
        · -- Block D-2: symmetric to D-1 on `J`.
          left
          obtain ⟨jW₀, hjW₀, jW₁, hjW₁, hneW, hAdjW⟩ := hBB
          have hWit : ∃ x y, x ∈ J ∧ y ∈ J ∧ x < y ∧
              G.Adj (rightRootVertex hpaths.copy x) (rightRootVertex hpaths.copy y) := by
            rcases lt_or_gt_of_ne hneW with h | h
            · exact ⟨jW₀, jW₁, hjW₀, hjW₁, h, hAdjW⟩
            · exact ⟨jW₁, jW₀, hjW₁, hjW₀, h, hAdjW.symm⟩
          obtain ⟨xW, yW, hxW, hyW, hltW, hAdjW⟩ := hWit
          refine biclique_isContained_of_rightRightComplete hpaths.copy
            (firstHalfFinset J hJcard') (lastHalfFinset J hJcard')
            (by rw [firstHalfFinset_card]) (by rw [lastHalfFinset_card]) ?_
          intro j hjL j' hj'R
          have hjJ : j ∈ J := firstHalfFinset_subset J hJcard' hjL
          have hj'J : j' ∈ J := lastHalfFinset_subset J hJcard' hj'R
          have hlt : j < j' := firstHalfFinset_lt_lastHalfFinset J hJcard hjL hj'R
          have hOtJ := orderType_pairTuple_eq_of_lt hltW hlt
          have hPair := pair_atomicTuple_adj_iff hpaths
            (i₀ := iStar) (i₁ := iStar) (i₀' := iStar) (i₁' := iStar)
            (j₀ := xW) (j₁ := yW) (j₀' := j) (j₁' := j')
            (s := lastFin (r + 3) (by omega)) (t := lastFin (r + 3) (by omega))
            (by intro t; fin_cases t <;> simp [pairTuple, hiStar])
            (by intro t; fin_cases t <;> simp [pairTuple, hiStar])
            (by intro t; fin_cases t <;> simp [pairTuple, hxW, hyW])
            (by intro t; fin_cases t <;> simp [pairTuple, hjJ, hj'J])
            rfl hOtJ
          rw [atomicTuple_last, atomicTuple_last, atomicTuple_last, atomicTuple_last] at hPair
          exact hPair.mp hAdjW
        · have hNoBB : ∀ j, j ∈ J → ∀ j', j' ∈ J → j ≠ j' →
              ¬ G.Adj (rightRootVertex hpaths.copy j) (rightRootVertex hpaths.copy j') := by
            intro j hj j' hj' hne hij
            exact hBB ⟨j, hj, j', hj', hne, hij⟩
          by_cases hAQ :
              ∃ i, i ∈ I ∧ ∃ i', i' ∈ I ∧ i ≠ i' ∧ ∃ j', j' ∈ J ∧
                ∃ k : Fin (r + 1), G.Adj (leftRootVertex hpaths.copy i)
                  (pathVertex hpaths.copy i' j' k)
          · -- Block D-3: an `aᵢ ∼ p_{i', j', k}` cross-edge exists with `i ≠ i'`.
            -- Halve `I`; orderType-homogeneity propagates the witness adjacency
            -- across the halves to give a biclique on `(leftRoot, pathLeft)`.
            left
            obtain ⟨iW, hiWI, i'W, hi'WI, hneW, j'W, hj'WJ, kW, hAdjW⟩ := hAQ
            -- Helper: position `kW.val + 1` in `Fin (r + 3)`.
            have hkLt : kW.val + 1 < r + 3 := by have := kW.isLt; omega
            rcases lt_or_gt_of_ne hneW with hltW | hgtW
            · -- `iW < i'W`: leftRoot side = firstHalf, pathLeft side = lastHalf.
              refine biclique_isContained_of_complete (G := G)
                (leftRootEmbedding hpaths.copy)
                (pathLeftEmbedding hpaths.copy j'W kW)
                (firstHalfFinset I hIcard') (lastHalfFinset I hIcard')
                (by rw [firstHalfFinset_card]) (by rw [lastHalfFinset_card]) ?_
              intro i hiL i' hi'R
              have hiI : i ∈ I := firstHalfFinset_subset I hIcard' hiL
              have hi'I : i' ∈ I := lastHalfFinset_subset I hIcard' hi'R
              have hlt : i < i' := firstHalfFinset_lt_lastHalfFinset I hIcard hiL hi'R
              have hOtI := orderType_pairTuple_eq_of_lt hltW hlt
              have hPair := pair_atomicTuple_adj_iff hpaths
                (i₀ := iW) (i₁ := i'W) (i₀' := i) (i₁' := i')
                (j₀ := j'W) (j₁ := j'W) (j₀' := j'W) (j₁' := j'W)
                (s := 0) (t := ⟨kW.val + 1, hkLt⟩)
                (by intro t; fin_cases t <;> simp [pairTuple, hiWI, hi'WI])
                (by intro t; fin_cases t <;> simp [pairTuple, hiI, hi'I])
                (by intro t; fin_cases t <;> simp [pairTuple, hj'WJ])
                (by intro t; fin_cases t <;> simp [pairTuple, hj'WJ])
                hOtI rfl
              rw [atomicTuple_zero, atomicTuple_zero,
                atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex] at hPair
              exact hPair.mp hAdjW
            · -- `iW > i'W`: leftRoot side = lastHalf, pathLeft side = firstHalf.
              refine biclique_isContained_of_complete (G := G)
                (leftRootEmbedding hpaths.copy)
                (pathLeftEmbedding hpaths.copy j'W kW)
                (lastHalfFinset I hIcard') (firstHalfFinset I hIcard')
                (by rw [lastHalfFinset_card]) (by rw [firstHalfFinset_card]) ?_
              intro i hiR i' hi'L
              have hiI : i ∈ I := lastHalfFinset_subset I hIcard' hiR
              have hi'I : i' ∈ I := firstHalfFinset_subset I hIcard' hi'L
              have hgt : i > i' := firstHalfFinset_lt_lastHalfFinset I hIcard hi'L hiR
              have hOtI := orderType_pairTuple_eq_of_gt hgtW hgt
              have hPair := pair_atomicTuple_adj_iff hpaths
                (i₀ := iW) (i₁ := i'W) (i₀' := i) (i₁' := i')
                (j₀ := j'W) (j₁ := j'W) (j₀' := j'W) (j₁' := j'W)
                (s := 0) (t := ⟨kW.val + 1, hkLt⟩)
                (by intro t; fin_cases t <;> simp [pairTuple, hiWI, hi'WI])
                (by intro t; fin_cases t <;> simp [pairTuple, hiI, hi'I])
                (by intro t; fin_cases t <;> simp [pairTuple, hj'WJ])
                (by intro t; fin_cases t <;> simp [pairTuple, hj'WJ])
                hOtI rfl
              rw [atomicTuple_zero, atomicTuple_zero,
                atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex] at hPair
              exact hPair.mp hAdjW
          · have hNoAQCross : ∀ i, i ∈ I → ∀ i', i' ∈ I → i ≠ i' → ∀ j', j' ∈ J →
                ∀ k : Fin (r + 1),
                ¬ G.Adj (leftRootVertex hpaths.copy i)
                  (pathVertex hpaths.copy i' j' k) := by
              intro i hi i' hi' hne j' hj' k hadj
              exact hAQ ⟨i, hi, i', hi', hne, j', hj', k, hadj⟩
            by_cases hBQ :
                ∃ j, j ∈ J ∧ ∃ j', j' ∈ J ∧ j ≠ j' ∧ ∃ i', i' ∈ I ∧
                  ∃ k : Fin (r + 1), G.Adj (rightRootVertex hpaths.copy j)
                    (pathVertex hpaths.copy i' j' k)
            · -- Block D-4: symmetric to D-3, halving `J`.
              left
              obtain ⟨jW, hjWJ, j'W, hj'WJ, hneW, i'W, hi'WI, kW, hAdjW⟩ := hBQ
              have hkLt : kW.val + 1 < r + 3 := by have := kW.isLt; omega
              rcases lt_or_gt_of_ne hneW with hltW | hgtW
              · -- `jW < j'W`.
                refine biclique_isContained_of_complete (G := G)
                  (rightRootEmbedding hpaths.copy)
                  (pathRightEmbedding hpaths.copy i'W kW)
                  (firstHalfFinset J hJcard') (lastHalfFinset J hJcard')
                  (by rw [firstHalfFinset_card]) (by rw [lastHalfFinset_card]) ?_
                intro j hjL j' hj'R
                have hjJ : j ∈ J := firstHalfFinset_subset J hJcard' hjL
                have hj'J : j' ∈ J := lastHalfFinset_subset J hJcard' hj'R
                have hlt : j < j' := firstHalfFinset_lt_lastHalfFinset J hJcard hjL hj'R
                have hOtJ := orderType_pairTuple_eq_of_lt hltW hlt
                have hPair := pair_atomicTuple_adj_iff hpaths
                  (i₀ := i'W) (i₁ := i'W) (i₀' := i'W) (i₁' := i'W)
                  (j₀ := jW) (j₁ := j'W) (j₀' := j) (j₁' := j')
                  (s := lastFin (r + 3) (by omega)) (t := ⟨kW.val + 1, hkLt⟩)
                  (by intro t; fin_cases t <;> simp [pairTuple, hi'WI])
                  (by intro t; fin_cases t <;> simp [pairTuple, hi'WI])
                  (by intro t; fin_cases t <;> simp [pairTuple, hjWJ, hj'WJ])
                  (by intro t; fin_cases t <;> simp [pairTuple, hjJ, hj'J])
                  rfl hOtJ
                rw [atomicTuple_last, atomicTuple_last,
                  atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex] at hPair
                exact hPair.mp hAdjW
              · -- `jW > j'W`.
                refine biclique_isContained_of_complete (G := G)
                  (rightRootEmbedding hpaths.copy)
                  (pathRightEmbedding hpaths.copy i'W kW)
                  (lastHalfFinset J hJcard') (firstHalfFinset J hJcard')
                  (by rw [lastHalfFinset_card]) (by rw [firstHalfFinset_card]) ?_
                intro j hjR j' hj'L
                have hjJ : j ∈ J := lastHalfFinset_subset J hJcard' hjR
                have hj'J : j' ∈ J := firstHalfFinset_subset J hJcard' hj'L
                have hgt : j > j' := firstHalfFinset_lt_lastHalfFinset J hJcard hj'L hjR
                have hOtJ := orderType_pairTuple_eq_of_gt hgtW hgt
                have hPair := pair_atomicTuple_adj_iff hpaths
                  (i₀ := i'W) (i₁ := i'W) (i₀' := i'W) (i₁' := i'W)
                  (j₀ := jW) (j₁ := j'W) (j₀' := j) (j₁' := j')
                  (s := lastFin (r + 3) (by omega)) (t := ⟨kW.val + 1, hkLt⟩)
                  (by intro t; fin_cases t <;> simp [pairTuple, hi'WI])
                  (by intro t; fin_cases t <;> simp [pairTuple, hi'WI])
                  (by intro t; fin_cases t <;> simp [pairTuple, hjWJ, hj'WJ])
                  (by intro t; fin_cases t <;> simp [pairTuple, hjJ, hj'J])
                  rfl hOtJ
                rw [atomicTuple_last, atomicTuple_last,
                  atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex] at hPair
                exact hPair.mp hAdjW
            · have hNoBQCross : ∀ j, j ∈ J → ∀ j', j' ∈ J → j ≠ j' → ∀ i', i' ∈ I →
                  ∀ k : Fin (r + 1),
                  ¬ G.Adj (rightRootVertex hpaths.copy j)
                    (pathVertex hpaths.copy i' j' k) := by
                intro j hj j' hj' hne i' hi' k hadj
                exact hBQ ⟨j, hj, j', hj', hne, i', hi', k, hadj⟩
              by_cases hQQ :
                  ∃ i, i ∈ I ∧ ∃ i', i' ∈ I ∧ ∃ j, j ∈ J ∧ ∃ j', j' ∈ J ∧
                    (i, j) ≠ (i', j') ∧ ∃ k k' : Fin (r + 1),
                    G.Adj (pathVertex hpaths.copy i j k)
                      (pathVertex hpaths.copy i' j' k')
              · -- Block D-5: a `p_{i,j,k} ∼ p_{i',j',k'}` cross-edge exists with
                -- `(i, j) ≠ (i', j')`. Two subcases on which coordinate differs.
                left
                obtain ⟨iW, hiWI, i'W, hi'WI, jW, hjWJ, j'W, hj'WJ,
                  hneW, kW, k'W, hAdjW⟩ := hQQ
                have hkLt : kW.val + 1 < r + 3 := by have := kW.isLt; omega
                have hk'Lt : k'W.val + 1 < r + 3 := by have := k'W.isLt; omega
                by_cases hiNe : iW = i'W
                · -- Subcase: `iW = i'W`, so `jW ≠ j'W`. Halve `J`.
                  subst hiNe
                  have hjNe : jW ≠ j'W := by
                    intro h
                    apply hneW
                    rw [h]
                  rcases lt_or_gt_of_ne hjNe with hltW | hgtW
                  · refine biclique_isContained_of_complete (G := G)
                      (pathRightEmbedding hpaths.copy iW kW)
                      (pathRightEmbedding hpaths.copy iW k'W)
                      (firstHalfFinset J hJcard') (lastHalfFinset J hJcard')
                      (by rw [firstHalfFinset_card]) (by rw [lastHalfFinset_card]) ?_
                    intro j hjL j' hj'R
                    have hjJ : j ∈ J := firstHalfFinset_subset J hJcard' hjL
                    have hj'J : j' ∈ J := lastHalfFinset_subset J hJcard' hj'R
                    have hlt : j < j' := firstHalfFinset_lt_lastHalfFinset J hJcard hjL hj'R
                    have hOtJ := orderType_pairTuple_eq_of_lt hltW hlt
                    have hPair := pair_atomicTuple_adj_iff hpaths
                      (i₀ := iW) (i₁ := iW) (i₀' := iW) (i₁' := iW)
                      (j₀ := jW) (j₁ := j'W) (j₀' := j) (j₁' := j')
                      (s := ⟨kW.val + 1, hkLt⟩) (t := ⟨k'W.val + 1, hk'Lt⟩)
                      (by intro t; fin_cases t <;> simp [pairTuple, hiWI])
                      (by intro t; fin_cases t <;> simp [pairTuple, hiWI])
                      (by intro t; fin_cases t <;> simp [pairTuple, hjWJ, hj'WJ])
                      (by intro t; fin_cases t <;> simp [pairTuple, hjJ, hj'J])
                      rfl hOtJ
                    rw [atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex,
                      atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex] at hPair
                    exact hPair.mp hAdjW
                  · refine biclique_isContained_of_complete (G := G)
                      (pathRightEmbedding hpaths.copy iW kW)
                      (pathRightEmbedding hpaths.copy iW k'W)
                      (lastHalfFinset J hJcard') (firstHalfFinset J hJcard')
                      (by rw [lastHalfFinset_card]) (by rw [firstHalfFinset_card]) ?_
                    intro j hjR j' hj'L
                    have hjJ : j ∈ J := lastHalfFinset_subset J hJcard' hjR
                    have hj'J : j' ∈ J := firstHalfFinset_subset J hJcard' hj'L
                    have hgt : j > j' := firstHalfFinset_lt_lastHalfFinset J hJcard hj'L hjR
                    have hOtJ := orderType_pairTuple_eq_of_gt hgtW hgt
                    have hPair := pair_atomicTuple_adj_iff hpaths
                      (i₀ := iW) (i₁ := iW) (i₀' := iW) (i₁' := iW)
                      (j₀ := jW) (j₁ := j'W) (j₀' := j) (j₁' := j')
                      (s := ⟨kW.val + 1, hkLt⟩) (t := ⟨k'W.val + 1, hk'Lt⟩)
                      (by intro t; fin_cases t <;> simp [pairTuple, hiWI])
                      (by intro t; fin_cases t <;> simp [pairTuple, hiWI])
                      (by intro t; fin_cases t <;> simp [pairTuple, hjWJ, hj'WJ])
                      (by intro t; fin_cases t <;> simp [pairTuple, hjJ, hj'J])
                      rfl hOtJ
                    rw [atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex,
                      atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex] at hPair
                    exact hPair.mp hAdjW
                · -- Subcase: `iW ≠ i'W`. Halve `I`.
                  rcases lt_or_gt_of_ne hiNe with hltW | hgtW
                  · refine biclique_isContained_of_complete (G := G)
                      (pathLeftEmbedding hpaths.copy jW kW)
                      (pathLeftEmbedding hpaths.copy j'W k'W)
                      (firstHalfFinset I hIcard') (lastHalfFinset I hIcard')
                      (by rw [firstHalfFinset_card]) (by rw [lastHalfFinset_card]) ?_
                    intro i hiL i' hi'R
                    have hiI : i ∈ I := firstHalfFinset_subset I hIcard' hiL
                    have hi'I : i' ∈ I := lastHalfFinset_subset I hIcard' hi'R
                    have hlt : i < i' := firstHalfFinset_lt_lastHalfFinset I hIcard hiL hi'R
                    have hOtI := orderType_pairTuple_eq_of_lt hltW hlt
                    have hPair := pair_atomicTuple_adj_iff hpaths
                      (i₀ := iW) (i₁ := i'W) (i₀' := i) (i₁' := i')
                      (j₀ := jW) (j₁ := j'W) (j₀' := jW) (j₁' := j'W)
                      (s := ⟨kW.val + 1, hkLt⟩) (t := ⟨k'W.val + 1, hk'Lt⟩)
                      (by intro t; fin_cases t <;> simp [pairTuple, hiWI, hi'WI])
                      (by intro t; fin_cases t <;> simp [pairTuple, hiI, hi'I])
                      (by intro t; fin_cases t <;> simp [pairTuple, hjWJ, hj'WJ])
                      (by intro t; fin_cases t <;> simp [pairTuple, hjWJ, hj'WJ])
                      hOtI rfl
                    rw [atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex,
                      atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex] at hPair
                    exact hPair.mp hAdjW
                  · refine biclique_isContained_of_complete (G := G)
                      (pathLeftEmbedding hpaths.copy jW kW)
                      (pathLeftEmbedding hpaths.copy j'W k'W)
                      (lastHalfFinset I hIcard') (firstHalfFinset I hIcard')
                      (by rw [lastHalfFinset_card]) (by rw [firstHalfFinset_card]) ?_
                    intro i hiR i' hi'L
                    have hiI : i ∈ I := lastHalfFinset_subset I hIcard' hiR
                    have hi'I : i' ∈ I := firstHalfFinset_subset I hIcard' hi'L
                    have hgt : i > i' := firstHalfFinset_lt_lastHalfFinset I hIcard hi'L hiR
                    have hOtI := orderType_pairTuple_eq_of_gt hgtW hgt
                    have hPair := pair_atomicTuple_adj_iff hpaths
                      (i₀ := iW) (i₁ := i'W) (i₀' := i) (i₁' := i')
                      (j₀ := jW) (j₁ := j'W) (j₀' := jW) (j₁' := j'W)
                      (s := ⟨kW.val + 1, hkLt⟩) (t := ⟨k'W.val + 1, hk'Lt⟩)
                      (by intro t; fin_cases t <;> simp [pairTuple, hiWI, hi'WI])
                      (by intro t; fin_cases t <;> simp [pairTuple, hiI, hi'I])
                      (by intro t; fin_cases t <;> simp [pairTuple, hjWJ, hj'WJ])
                      (by intro t; fin_cases t <;> simp [pairTuple, hjWJ, hj'WJ])
                      hOtI rfl
                    rw [atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex,
                      atomicTuple_succ_eq_pathVertex, atomicTuple_succ_eq_pathVertex] at hPair
                    exact hPair.mp hAdjW
              · have hNoQQCross : ∀ i, i ∈ I → ∀ i', i' ∈ I → ∀ j, j ∈ J → ∀ j', j' ∈ J →
                    (i, j) ≠ (i', j') → ∀ k k' : Fin (r + 1),
                    ¬ G.Adj (pathVertex hpaths.copy i j k)
                      (pathVertex hpaths.copy i' j' k') := by
                  intro i hi i' hi' j hj j' hj' hne k k' hadj
                  exact hQQ ⟨i, hi, i', hi', j, hj, j', hj', hne, k, k', hadj⟩
                right
                exact buildCrossEdgeFreeData r G U n hsub I J hIcard' hJcard' hpaths
                  hNoDirect hNoAA hNoBB hNoAQCross hNoBQCross hNoQQCross

private theorem crossEdgeFreeGivesInducedSubdivision (r : ℕ) {V : Type}
    [DecidableEq V] [Fintype V] (G : SimpleGraph V) (U : ℕ → ℕ) (n : ℕ)
    (hsub : (subdividedBiclique n (r + 1)).IsContained G)
    (I J : Finset (Fin n)) (_hIcard : U n ≤ I.card) (_hJcard : U n ≤ J.card)
    (hfree : CrossEdgeFreeData r G U n hsub I J) :
    ∃ r' : ℕ, 1 ≤ r' ∧ r' ≤ r + 1 ∧
      (subdividedBiclique (U n) r').IsIndContained G := by
  exact hfree

private theorem subdividedBiclique_ramsey_succ (r : ℕ) :
    ∃ U : ℕ → ℕ, Monotone U ∧ (∀ N : ℕ, ∃ n : ℕ, N ≤ U n) ∧
      ∀ {V : Type} [DecidableEq V] [Fintype V]
        (G : SimpleGraph V) (n : ℕ),
        (subdividedBiclique n (r + 1)).IsContained G →
          (biclique (U n)).IsContained G ∨
          ∃ r' : ℕ, 1 ≤ r' ∧ r' ≤ r + 1 ∧
            (subdividedBiclique (U n) r').IsIndContained G := by
  classical
  -- Outside-in `c(r)` absorption (cf. handshake `architectural decision`):
  -- every Block D cross-edge halving is pre-paid by dividing the inner Ramsey
  -- bound `U_bip` by 2. Only one halving fires per run (the first cross case
  -- that holds returns a biclique of half-size; otherwise `CrossEdgeFreeData`
  -- consumes the full block), so `c(r) = 2` suffices.
  obtain ⟨U, hUmono, hUunb, hRamsey⟩ := bipartiteHomogeneity r
  let U' : ℕ → ℕ := fun n => U n / 2
  refine ⟨U', ?_, ?_, ?_⟩
  · intro a b hab
    exact Nat.div_le_div_right (hUmono hab)
  · intro N
    obtain ⟨n, hn⟩ := hUunb (2 * N)
    refine ⟨n, ?_⟩
    show N ≤ U n / 2
    omega
  · intro V _ _ G n hsub
    obtain ⟨c, hc⟩ := buildAtomicTypeColoring r G n hsub
    obtain ⟨I, J, hIcard, hJcard, f, hf⟩ := hRamsey n c
    have hpaths : HasHomogeneousShortestPaths r G n hsub I J :=
      extractHomogeneousShortestPaths r G n hsub I J c hc f hf
    have hIcard2 : 2 * U' n ≤ I.card := by
      show 2 * (U n / 2) ≤ I.card
      have h2 : 2 * (U n / 2) ≤ U n := Nat.mul_div_le (U n) 2
      omega
    have hJcard2 : 2 * U' n ≤ J.card := by
      show 2 * (U n / 2) ≤ J.card
      have h2 : 2 * (U n / 2) ≤ U n := Nat.mul_div_le (U n) 2
      omega
    rcases homogeneousCaseSplit r G U' n hsub I J hIcard2 hJcard2 hpaths with hBiclique | hfree
    · exact Or.inl hBiclique
    · have hIcard1 : U' n ≤ I.card := by omega
      have hJcard1 : U' n ≤ J.card := by omega
      exact Or.inr
        (crossEdgeFreeGivesInducedSubdivision r G U' n hsub I J hIcard1 hJcard1 hfree)

/-- Mählmann Lemma 13.8. -/
theorem subdividedBiclique_ramsey (r : ℕ) :
    ∃ U : ℕ → ℕ, Monotone U ∧ (∀ N : ℕ, ∃ n : ℕ, N ≤ U n) ∧
      ∀ {V : Type} [DecidableEq V] [Fintype V]
        (G : SimpleGraph V) (n : ℕ),
        (subdividedBiclique n r).IsContained G →
          (biclique (U n)).IsContained G ∨
          ∃ r' : ℕ, 1 ≤ r' ∧ r' ≤ r ∧
            (subdividedBiclique (U n) r').IsIndContained G := by
  cases r with
  | zero =>
      exact subdividedBiclique_ramsey_zero
  | succ r =>
      exact subdividedBiclique_ramsey_succ r


end Lax5Proofs.SubdividedBicliqueRamsey
