import Mathlib

/-!
---
title: χ-Boundedness and Linear Neighbourhood Complexity of Bounded Merge-Width Classes
---
Every class of finite simple graphs with bounded merge-width is χ-bounded and
has linear neighbourhood complexity.

Here a merge sequence consists of a coarsening sequence of partitions together
with monotone sets of resolved vertex pairs. At every step, adjacency is
uniform on unresolved pairs between any two current parts. Its radius-`r`
width is the maximum number of parts from the preceding partition that a
radius-`r` ball in the resolved-pair graph can meet. The radius-`r`
merge-width of a graph is the minimum width of any such sequence.

This file collects clean, human-readable definitions of the notions studied in
Bonamy–Geniet, *χ-Boundedness and Neighbourhood Complexity of Bounded
Merge-Width Graphs* (arXiv:2504.08266):

* a **merge sequence** of a finite simple graph and its **radius-`r` width**;
* the **radius-`r` merge-width** `mwᵣ(G)` of a graph;
* a **graph class of bounded merge-width**;
* **χ-boundedness** of a graph class;
* **linear neighbourhood complexity** of a graph class;
* the **semantic (isomorphism) closure** of a graph class.

We work throughout with finite simple graphs (`SimpleGraph` on a `Fintype`).
-/

namespace Lax8.MergeWidth

open scoped Classical

universe u

variable {V : Type u} [Fintype V]

/-- The **resolved ball** of radius `r` around `v` in a graph `H`:
the set of vertices reachable from `v` by a walk of length at most `r`.
In the paper this is applied to the graph `(V, Rᵢ)` of resolved pairs. -/
def resolvedBall (H : SimpleGraph V) (r : ℕ) (v : V) : Set V :=
  {u | ∃ w : H.Walk v u, w.length ≤ r}

/--
A **merge sequence** for a finite simple graph `G` is a sequence
`(P₁, R₁), …, (P_length, R_length)` where:

* each `part i` is a partition of `V(G)` (encoded as a `Setoid`), with `part 1`
  the partition into singletons (`⊥`) and `part length` the trivial partition
  with one part (`⊤`);
* the partitions are **coarsening**: `part i ≤ part j` for `i ≤ j`
  (recall that for setoids a *coarser* partition is a *larger* relation);
* each `resolved i` is the graph `(V, Rᵢ)` of **resolved pairs**, and these are
  **monotone**: `resolved i ≤ resolved j` for `i ≤ j`;
* (**uniformity**) for any two parts `A, B` of `part i`, the *unresolved* pairs
  between `A` and `B` (pairs `xy ∉ Rᵢ`) are either all edges or all non-edges of
  `G`.
-/
structure MergeSeq (G : SimpleGraph V) where
  /-- The number `m` of steps of the sequence. -/
  length : ℕ
  /-- The sequence is nonempty. -/
  one_le_length : 1 ≤ length
  /-- The partition `Pᵢ` at step `i` (as a setoid on the vertices). -/
  part : ℕ → Setoid V
  /-- The graph `(V, Rᵢ)` of resolved pairs at step `i`. -/
  resolved : ℕ → SimpleGraph V
  /-- `P₁` is the partition into singletons. -/
  part_one : part 1 = ⊥
  /-- `P_m` is the trivial partition with a single part. -/
  part_length : part length = ⊤
  /-- The partitions get coarser. -/
  part_mono : ∀ ⦃i j⦄, 1 ≤ i → i ≤ j → j ≤ length → part i ≤ part j
  /-- The sets of resolved pairs are monotone. -/
  resolved_mono : ∀ ⦃i j⦄, 1 ≤ i → i ≤ j → j ≤ length → resolved i ≤ resolved j
  /-- Uniformity: unresolved pairs between two parts are all edges or all
  non-edges. -/
  uniform : ∀ ⦃i⦄, 1 ≤ i → i ≤ length → ∀ ⦃x x' y y' : V⦄,
      (part i).r x x' → (part i).r y y' → x ≠ y → x' ≠ y' →
      ¬ (resolved i).Adj x y → ¬ (resolved i).Adj x' y' →
      (G.Adj x y ↔ G.Adj x' y')

namespace MergeSeq

variable {G : SimpleGraph V}

/-- The number of parts of `part (i-1)` that are **accessible** from `v` by a
walk of length at most `r` in the resolved graph `resolved i`.  (Note the
intentional mismatch of indices `Pᵢ₋₁` versus `Rᵢ`.) -/
noncomputable def numAccessible (S : MergeSeq G) (r i : ℕ) (v : V) : ℕ :=
  Set.ncard ((fun u => Quotient.mk (S.part (i - 1)) u) '' resolvedBall (S.resolved i) r v)

/-- The **radius-`r` width** of a merge sequence: the maximum over all steps
`i ≥ 2` and vertices `v` of the number of parts of `Pᵢ₋₁` accessible from `v`
within distance `r` in `(V, Rᵢ)`. -/
noncomputable def width (S : MergeSeq G) (r : ℕ) : ℕ :=
  (Finset.Icc 2 S.length).sup fun i => Finset.univ.sup fun v => S.numAccessible r i v

end MergeSeq

/-- The **radius-`r` merge-width** `mwᵣ(G)` of a graph `G`: the minimum
radius-`r` width over all merge sequences of `G`. -/
noncomputable def mergeWidth (r : ℕ) (G : SimpleGraph V) : ℕ :=
  sInf {w | ∃ S : MergeSeq G, S.width r = w}

/-
## Graph classes

A **graph class** is a property of finite simple graphs (over an arbitrary
finite vertex type).
-/

/-- A **graph class**: a property of finite simple graphs. -/
def GraphClass : Type 1 := ∀ ⦃V : Type⦄ [Fintype V], SimpleGraph V → Prop

/-- A class `C` has **bounded merge-width** if there is a function `f` such that
every `G ∈ C` satisfies `mwᵣ(G) ≤ f(r)` for all radii `r`. -/
def BoundedMergeWidth (C : GraphClass) : Prop :=
  ∃ f : ℕ → ℕ, ∀ ⦃V : Type⦄ [Fintype V] (G : SimpleGraph V), C G → ∀ r, mergeWidth r G ≤ f r

/-- A class `C` is **χ-bounded** if there is a function `f` such that every
`G ∈ C` has chromatic number at most `f(ω(G))`, where `ω(G)` is the clique
number.  (`G.Colorable n` says `χ(G) ≤ n`.) -/
def ChiBounded (C : GraphClass) : Prop :=
  ∃ f : ℕ → ℕ, ∀ ⦃V : Type⦄ [Fintype V] (G : SimpleGraph V), C G → G.Colorable (f G.cliqueNum)

/-- The **neighbourhood complexity** `π_G(p)` of a graph `G`: the maximum, over
all vertex sets `X` of size `p`, of the number of distinct sets `N(v) ∩ X` for
`v ∉ X`. -/
noncomputable def neighborhoodComplexity (G : SimpleGraph V) (p : ℕ) : ℕ :=
  (Finset.univ.powersetCard p).sup fun X =>
    ((Finset.univ \ X).image fun v => X.filter fun u => G.Adj v u).card

/-- A class `C` has **linear neighbourhood complexity** if there is a constant
`c` such that every `G ∈ C` satisfies `π_G(p) ≤ c · p` for all `p ≥ 1`.
(The restriction `p ≥ 1` is standard: `π_G(0) = 1` for a nonempty graph, so a
bound `≤ c · p` can only hold for `p ≥ 1`.) -/
def LinearNeighborhoodComplexity (C : GraphClass) : Prop :=
  ∃ c : ℕ, ∀ ⦃V : Type⦄ [Fintype V] (G : SimpleGraph V), C G → ∀ p, 1 ≤ p →
    neighborhoodComplexity G p ≤ c * p

/-
## Semantic closure

A graph-theoretic property is **semantic** if it is invariant under graph
isomorphism.  The **semantic closure** of a class is the smallest
isomorphism-closed class containing it.
-/

/-- A class is **semantic** (isomorphism-invariant) if membership is preserved
by graph isomorphisms. -/
def IsSemantic (C : GraphClass) : Prop :=
  ∀ ⦃V W : Type⦄ [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
    C G → Nonempty (G ≃g H) → C H

/-- The **semantic closure** of a class `C`: all graphs isomorphic to some graph
in `C`. -/
def semanticClosure (C : GraphClass) : GraphClass :=
  fun _ _ H => ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), (C G) ∧ Nonempty (G ≃g H)

/-- **Theorem 1.2.** Every graph class of bounded merge-width is χ-bounded. -/
axiom bounded_mergeWidth_chiBounded
    (C : GraphClass) (h : BoundedMergeWidth C) : ChiBounded C

/-- **Theorem 1.5.** Every graph class of bounded merge-width has linear
neighbourhood complexity. -/
axiom bounded_mergeWidth_linearNeighborhoodComplexity
    (C : GraphClass) (h : BoundedMergeWidth C) : LinearNeighborhoodComplexity C

end Lax8.MergeWidth
