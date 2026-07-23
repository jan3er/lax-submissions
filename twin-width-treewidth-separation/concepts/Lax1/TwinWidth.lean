import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice

/-!
---
title: Twin-width
type: definition
---
A contraction sequence of a finite simple graph *G* is a sequence of vertex
partitions: it starts at the partition into singletons and merges two parts
at every step, until at most one part remains. Two parts are homogeneous if
*G* has either all possible edges between them or none; the red degree of a
part is the number of other parts it is not homogeneous with. The width of a
contraction sequence is the largest red degree of any part occurring in it.

The twin-width of *G* is the least *d* such that *G* has a contraction
sequence of width at most *d*.

# Formalization notes

Contracting in any order gives a sequence of width at most the number of
vertices, so the
infimum in `twinWidth` ranges over a nonempty set. Because every state is
reached from the singleton partition by merges, each `partition i` with
`i ≤ stepCount` is automatically a partition of the vertex set; values of
`partition` beyond `stepCount` are irrelevant.
-/

namespace Lax1.TwinWidth

/-- Two vertex sets are homogeneous in `G`: either every pair of vertices
across them is adjacent, or none is. -/
def Homogeneous {V : Type} (G : SimpleGraph V) (A B : Finset V) : Prop :=
  (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∨ (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)

/-- The red degree of a part `A` in a family of parts `P`: the number of
other parts of `P` that are not homogeneous with `A`. -/
noncomputable def redDegree {V : Type} (G : SimpleGraph V)
    (P : Finset (Finset V)) (A : Finset V) : ℕ :=
  {B | B ∈ P ∧ B ≠ A ∧ ¬ Homogeneous G A B}.ncard

/-- The partition of a finite vertex type into singletons. -/
def singletonPartition (V : Type) [Fintype V] [DecidableEq V] :
    Finset (Finset V) :=
  Finset.univ.image fun v : V => ({v} : Finset V)

/-- A contraction sequence for `G` of width at most `d`: starting from the
singleton partition, each step merges two parts, until at most one part
remains; every part of every partition in the sequence has red degree at
most `d`. -/
structure ContractionSequence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) where
  /-- The number of merge steps. -/
  stepCount : ℕ
  /-- The state after each number of merge steps. -/
  partition : ℕ → Finset (Finset V)
  /-- The sequence starts at the singleton partition. -/
  starts : partition 0 = singletonPartition V
  /-- The sequence ends with at most one part. -/
  ends : (partition stepCount).card ≤ 1
  /-- Each step merges two distinct parts and keeps all other parts. -/
  step_merges :
    ∀ i, i < stepCount → ∃ A ∈ partition i, ∃ B ∈ partition i, A ≠ B ∧
      partition (i + 1) = insert (A ∪ B) (((partition i).erase A).erase B)
  /-- Every part of every partition in the sequence has red degree at most
  `d`. -/
  redDegree_le :
    ∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ partition i →
      redDegree G (partition i) A ≤ d

/-- `G` admits a contraction sequence of width at most `d`. -/
def HasTwinWidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (ContractionSequence G d)

/-- The twin-width of a finite simple graph: the least `d` such that the
graph has a contraction sequence of width at most `d`. -/
noncomputable def twinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {d | HasTwinWidthAtMost G d}

end Lax1.TwinWidth
