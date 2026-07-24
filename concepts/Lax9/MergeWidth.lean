import Mathlib

/-!
---
title: Merge-Width
type: definition
---
A merge sequence of a finite simple graph consists of a coarsening sequence of
partitions and a monotone sequence of graphs of resolved pairs. At each step,
adjacency is uniform on the unresolved pairs between any two parts. The
radius-$r$ width of a merge sequence is the maximum number of parts of the
preceding partition met by a radius-$r$ ball in the graph of resolved pairs.
The radius-$r$ merge-width of a graph is the minimum width of a merge sequence
of that graph. A graph class has bounded merge-width if these parameters are
bounded by a function of $r$ throughout the class.
-/

namespace Lax9.MergeWidth

open scoped Classical

universe u

variable {V : Type u} [Fintype V]

/-- The **resolved ball** of radius $r$ around $v$ in a graph $H$:
the set of vertices reachable from $v$ by a walk of length at most $r$.
In the paper this is applied to the graph $(V, Rᵢ)$ of resolved pairs. -/
def resolvedBall (H : SimpleGraph V) (r : ℕ) (v : V) : Set V :=
  {u | ∃ w : H.Walk v u, w.length ≤ r}

/--
A **merge sequence** for a finite simple graph $G$ is a sequence
$(P₁, R₁), …, (P_length, R_length)$ where:

* each $part i$ is a partition of $V(G)$ (encoded as a $Setoid$), with $part 1$
  the partition into singletons ($⊥$) and $part length$ the trivial partition
  with one part ($⊤$);
* the partitions are **coarsening**: $part i ≤ part j$ for $i ≤ j$
  (recall that for setoids a *coarser* partition is a *larger* relation);
* each $resolved i$ is the graph $(V, Rᵢ)$ of **resolved pairs**, and these are
  **monotone**: $resolved i ≤ resolved j$ for $i ≤ j$;
* (**uniformity**) for any two parts $A, B$ of $part i$, the *unresolved* pairs
  between $A$ and $B$ (pairs $xy ∉ Rᵢ$) are either all edges or all non-edges of
  $G$.
-/
structure MergeSeq (G : SimpleGraph V) where
  /-- The number $m$ of steps of the sequence. -/
  length : ℕ
  /-- The sequence is nonempty. -/
  one_le_length : 1 ≤ length
  /-- The partition $Pᵢ$ at step $i$ (as a setoid on the vertices). -/
  part : ℕ → Setoid V
  /-- The graph $(V, Rᵢ)$ of resolved pairs at step $i$. -/
  resolved : ℕ → SimpleGraph V
  /-- $P₁$ is the partition into singletons. -/
  part_one : part 1 = ⊥
  /-- $P_m$ is the trivial partition with a single part. -/
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

/-- The number of parts of $part (i-1)$ that are **accessible** from $v$ by a
walk of length at most $r$ in the resolved graph $resolved i$.  (Note the
intentional mismatch of indices $Pᵢ₋₁$ versus $Rᵢ$.) -/
noncomputable def numAccessible (S : MergeSeq G) (r i : ℕ) (v : V) : ℕ :=
  Set.ncard ((fun u => Quotient.mk (S.part (i - 1)) u) '' resolvedBall (S.resolved i) r v)

/-- The **radius-$r$ width** of a merge sequence: the maximum over all steps
$i ≥ 2$ and vertices $v$ of the number of parts of $Pᵢ₋₁$ accessible from $v$
within distance $r$ in $(V, Rᵢ)$. -/
noncomputable def width (S : MergeSeq G) (r : ℕ) : ℕ :=
  (Finset.Icc 2 S.length).sup fun i => Finset.univ.sup fun v => S.numAccessible r i v

end MergeSeq

/-- The **radius-$r$ merge-width** $mwᵣ(G)$ of a graph $G$: the minimum
radius-$r$ width over all merge sequences of $G$. -/
noncomputable def mergeWidth (r : ℕ) (G : SimpleGraph V) : ℕ :=
  sInf {w | ∃ S : MergeSeq G, S.width r = w}

/-- A **graph class**: a property of finite simple graphs. -/
def GraphClass : Type 1 := ∀ ⦃V : Type⦄ [Fintype V], SimpleGraph V → Prop

/-- A class $C$ has **bounded merge-width** if there is a function $f$ such that
every $G ∈ C$ satisfies $mwᵣ(G) ≤ f(r)$ for all radii $r$. -/
def BoundedMergeWidth (C : GraphClass) : Prop :=
  ∃ f : ℕ → ℕ, ∀ ⦃V : Type⦄ [Fintype V] (G : SimpleGraph V), C G → ∀ r, mergeWidth r G ≤ f r

end Lax9.MergeWidth
