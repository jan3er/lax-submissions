import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
---
title: Source development for twin-width and mixed minor number
---
The complete source development this submission's statement is phrased in:
divisions of finite intervals, mixed minors and the mixed number of Boolean
matrices, ordered adjacency matrices, the mixed minor number of a graph,
trigraphs, contraction sequences and twin-width, functional equivalence of
graph parameters, and the proved theorem chain (Marcus–Tardos, matrix
Theorem 10, Theorem 14, the twin-decomposition bridge, and the main
equivalence combiner). Concatenated from the original per-topic modules;
`===== begin/end =====` markers delimit them.
-/

namespace Lax2.Source

/- ===== begin Contraction/Trigraph.lean ===== -/

/-
# Trigraph states

Trigraph states are represented on a fixed original vertex type by a partition
of the original vertices into current bags, together with black and red
adjacency relations between bags.
-/

namespace TwinWidth

/-- A trigraph state consists of a bag partition of the original vertices and
black/red adjacency relations between bags.  Red edges are the errors counted by
twin-width. -/
structure TrigraphState (V : Type*) where
  /-- Current bags, represented as nonempty finite subsets of the original
  vertex set. -/
  bags : Finset (Finset V)
  /-- Every current bag is nonempty. -/
  bag_nonempty : ∀ ⦃A⦄, A ∈ bags → A.Nonempty
  /-- Current bags are pairwise disjoint. -/
  bag_disjoint : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → A ≠ B → Disjoint A B
  /-- Current bags cover the original vertex set. -/
  bag_cover : ∀ v : V, ∃ A ∈ bags, v ∈ A
  /-- Black, homogeneous adjacencies between current bags. -/
  blackAdj : Finset V → Finset V → Prop
  /-- Red, error adjacencies between current bags. -/
  redAdj : Finset V → Finset V → Prop
  /-- Black adjacency is symmetric on bags. -/
  black_symm : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → blackAdj B A
  /-- Red adjacency is symmetric on bags. -/
  red_symm : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → redAdj A B → redAdj B A
  /-- No bag has a black loop. -/
  black_irrefl : ∀ ⦃A⦄, A ∈ bags → ¬ blackAdj A A
  /-- No bag has a red loop. -/
  red_irrefl : ∀ ⦃A⦄, A ∈ bags → ¬ redAdj A A
  /-- A pair of bags is not simultaneously black and red. -/
  black_red_disjoint : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → ¬ redAdj A B

namespace TrigraphState

/-- The singleton bag family of the finest partition. -/
noncomputable def singletonBags (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.image (fun v : V => ({v} : Finset V))

@[simp] theorem mem_singletonBags {V : Type*} [Fintype V] [DecidableEq V]
    {A : Finset V} :
    A ∈ singletonBags V ↔ ∃ v : V, A = {v} := by
  classical
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨v, _hv, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact Finset.mem_image.mpr ⟨v, by simp, rfl⟩

@[simp] theorem card_singletonBags (V : Type*) [Fintype V] [DecidableEq V] :
    (singletonBags V).card = Fintype.card V := by
  classical
  rw [singletonBags]
  refine Finset.card_image_of_injective _ ?_
  intro a b h
  exact Finset.singleton_inj.mp h

/-- The red degree of a bag in a trigraph state. -/
noncomputable def redDegree {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A : Finset V) : ℕ :=
  by
    classical
    exact (T.bags.filter fun B => T.redAdj A B).card

end TrigraphState

end TwinWidth

/- ===== end Contraction/Trigraph.lean ===== -/

/- ===== begin Contraction/TwinWidth.lean ===== -/

/-
# Twin-width of finite simple graphs

Twin-width is defined using contraction sequences of trigraph states.  A state
keeps the original vertex type fixed and tracks the current contracted vertices
as bags.  The width of a sequence is the maximum red degree of any bag occurring
in any intermediate state.
-/

namespace TwinWidth
namespace SimpleGraph

/-- The red degree of a current bag in a trigraph state. -/
noncomputable def redDegree {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A : Finset V) : ℕ :=
  T.redDegree A

/-- The initial trigraph state for a graph has singleton bags, black edges
exactly where the graph has edges, and no red edges. -/
def IsInitialState {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (T : TrigraphState V) : Prop :=
  T.bags = TrigraphState.singletonBags V ∧
    (∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags →
      (T.blackAdj A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b)) ∧
    (∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags → ¬ T.redAdj A B)

/-- A final trigraph state has at most one bag.

For nonempty graphs this means the usual single contracted bag.  The `≤ 1`
convention also treats the empty graph as already fully contracted.
-/
def IsFinalState {V : Type*} (T : TrigraphState V) : Prop :=
  T.bags.card ≤ 1

/-- The bag of previous-state vertices represented by a next-state bag after
contracting `A` and `B`. -/
def contractionPreimages {V : Type*} [DecidableEq V]
    (A B X : Finset V) : Finset (Finset V) :=
  if X = A ∪ B then {A, B} else {X}

/-- Red adjacency after contracting `A` and `B`.

For the merged bag, red edges are inherited red edges or disagreements between
the two old black adjacencies.  Pairs of bags not involving the merged bag keep
their old red status.
-/
def contractedRed {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    T.redAdj A Y ∨ T.redAdj B Y ∨ T.blackAdj A Y ≠ T.blackAdj B Y
  else if Y = A ∪ B then
    T.redAdj X A ∨ T.redAdj X B ∨ T.blackAdj X A ≠ T.blackAdj X B
  else
    T.redAdj X Y

/-- Black adjacency after contracting `A` and `B`.

For the merged bag, a black edge to another bag remains only when both old
adjacencies were black and no red edge is created.  Other pairs are unchanged.
-/
def contractedBlack {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    T.blackAdj A Y ∧ T.blackAdj B Y ∧ ¬ contractedRed T A B X Y
  else if Y = A ∪ B then
    T.blackAdj X A ∧ T.blackAdj X B ∧ ¬ contractedRed T A B X Y
  else
    T.blackAdj X Y

/-- `U` is obtained from `T` by contracting two distinct bags. -/
def IsContractionStep {V : Type*} [DecidableEq V]
    (T U : TrigraphState V) : Prop :=
  ∃ A ∈ T.bags, ∃ B ∈ T.bags, A ≠ B ∧
    U.bags = insert (A ∪ B) ((T.bags.erase A).erase B) ∧
    (∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
      (U.redAdj X Y ↔ contractedRed T A B X Y)) ∧
    (∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
      (U.blackAdj X Y ↔ contractedBlack T A B X Y))

theorem IsContractionStep.bags_card_add_one
    {V : Type*} [DecidableEq V] {T U : TrigraphState V}
    (h : IsContractionStep T U) :
    U.bags.card + 1 = T.bags.card := by
  classical
  rcases h with ⟨A, hA, B, hB, hAB, hbags, _hred, _hblack⟩
  have hB_eraseA : B ∈ T.bags.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hA_not_rest : A ∉ (T.bags.erase A).erase B := by simp
  have hB_not_rest : B ∉ (T.bags.erase A).erase B := by simp
  have hUnion_not_rest : A ∪ B ∉ (T.bags.erase A).erase B := by
    intro hU
    have hUold : A ∪ B ∈ T.bags :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hU).2).2
    have hneA : A ≠ A ∪ B := by
      intro h
      have hBinA : B ⊆ A := by
        intro x hxB
        have hxU : x ∈ A ∪ B := Finset.mem_union_right _ hxB
        simpa [← h] using hxU
      rcases T.bag_nonempty hB with ⟨b, hb⟩
      have hbA : b ∈ A := hBinA hb
      exact (Finset.disjoint_left.mp (T.bag_disjoint hA hB hAB)) hbA hb
    rcases T.bag_nonempty hA with ⟨a, ha⟩
    exact (Finset.disjoint_left.mp (T.bag_disjoint hA hUold hneA))
      ha (Finset.mem_union_left _ ha)
  calc
    U.bags.card + 1
        = (insert (A ∪ B) ((T.bags.erase A).erase B)).card + 1 := by rw [hbags]
    _ = ((T.bags.erase A).erase B).card + 2 := by
        rw [Finset.card_insert_of_notMem hUnion_not_rest]
    _ = (T.bags.erase A).card + 1 := by
        rw [Finset.card_erase_of_mem hB_eraseA]
        have hpos : 0 < (T.bags.erase A).card := Finset.card_pos.mpr ⟨B, hB_eraseA⟩
        omega
    _ = T.bags.card := by
        rw [Finset.card_erase_of_mem hA]
        have hpos : 0 < T.bags.card := Finset.card_pos.mpr ⟨A, hA⟩
        omega

/-- A concrete contraction sequence of width at most `d`. -/
structure ContractionSequence {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) where
  /-- Number of contraction steps. -/
  stepCount : ℕ
  /-- The trigraph state at each time. -/
  state : ℕ → TrigraphState V
  /-- The first state is the singleton-bag encoding of `G`. -/
  starts : IsInitialState G (state 0)
  /-- The last state consists of one bag. -/
  ends : IsFinalState (state stepCount)
  /-- Consecutive states are related by one bag contraction. -/
  step_contracts : ∀ i, i < stepCount → IsContractionStep (state i) (state (i + 1))
  /-- Every bag in every state has red degree at most `d`. -/
  redDegree_le : ∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ (state i).bags → redDegree (state i) A ≤ d

namespace ContractionSequence

theorem bags_card_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    (S.state (i + 1)).bags.card + 1 = (S.state i).bags.card :=
  (S.step_contracts i hi).bags_card_add_one

theorem start_bags_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    (S.state 0).bags.card = Fintype.card V := by
  rw [S.starts.1]
  exact TrigraphState.card_singletonBags V

/-- After `i` contractions, the current number of bags plus `i` is the
initial number of vertices. -/
theorem bags_card_add_index
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ ⦃i : ℕ⦄, i ≤ S.stepCount →
      (S.state i).bags.card + i = Fintype.card V := by
  intro i hi
  induction i with
  | zero =>
      simpa using S.start_bags_card
  | succ i ih =>
      have hlt : i < S.stepCount := by omega
      have hprev : (S.state i).bags.card + i = Fintype.card V := ih (by omega)
      have hstep : (S.state (i + 1)).bags.card + 1 = (S.state i).bags.card :=
        S.bags_card_add_one hlt
      omega

/-- The final state of a contraction sequence on a nonempty vertex type has
exactly one bag. -/
theorem final_bags_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    (S.state S.stepCount).bags.card = 1 := by
  rcases ‹Nonempty V› with ⟨v⟩
  rcases (S.state S.stepCount).bag_cover v with ⟨A, hA, _hvA⟩
  have hpos : 0 < (S.state S.stepCount).bags.card :=
    Finset.card_pos.mpr ⟨A, hA⟩
  have hle : (S.state S.stepCount).bags.card ≤ 1 := S.ends
  omega

/-- A contraction sequence on a nonempty finite graph performs exactly
`|V|-1` contractions. -/
theorem stepCount_add_one_eq_card
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.stepCount + 1 = Fintype.card V := by
  have hcount := S.bags_card_add_index (i := S.stepCount) le_rfl
  have hfinal := S.final_bags_card_eq_one
  omega

end ContractionSequence

/-- `G` has twin-width at most `d` if it has a contraction sequence whose red
degree never exceeds `d`. -/
def HasTwinWidthAtMost {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (ContractionSequence G d)

/-- The twin-width of a graph is the least width admitting a contraction
sequence.  The fallback branch is unreachable once existence of contraction
sequences is proved for all finite graphs; keeping it here makes the definition
total without using axioms. -/
noncomputable def twinWidth {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℕ :=
  by
    classical
    exact if h : ∃ d, HasTwinWidthAtMost G d then Nat.find h else 0

theorem hasTwinWidthAtMost_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d e : ℕ}
    (h : HasTwinWidthAtMost G d) (hde : d ≤ e) :
    HasTwinWidthAtMost G e := by
  rcases h with ⟨S⟩
  refine ⟨(?_ : ContractionSequence G e)⟩
  exact ContractionSequence.mk S.stepCount S.state S.starts S.ends S.step_contracts
    (fun i hi A hA => le_trans (S.redDegree_le i hi hA) hde)

theorem twinWidth_le_of_hasTwinWidthAtMost {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (h : HasTwinWidthAtMost G d) :
    twinWidth G ≤ d := by
  classical
  have hex : ∃ e, HasTwinWidthAtMost G e := ⟨d, h⟩
  rw [twinWidth, dif_pos hex]
  exact Nat.find_min' hex h

theorem hasTwinWidthAtMost_twinWidth {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (h : ∃ d, HasTwinWidthAtMost G d) :
    HasTwinWidthAtMost G (twinWidth G) := by
  classical
  rw [twinWidth, dif_pos h]
  exact Nat.find_spec h

end SimpleGraph
end TwinWidth

/- ===== end Contraction/TwinWidth.lean ===== -/

/- ===== begin Equivalence/FunctionalEquivalence.lean ===== -/

/-
# Functional equivalence of graph parameters

This file defines the abstract relation used by the main theorem: each graph
parameter is bounded by a numerical function of the other.
-/

namespace TwinWidth

/-- A finite simple-graph parameter. -/
def GraphParam :=
  ∀ {V : Type}, [Fintype V] → [DecidableEq V] → SimpleGraph V → ℕ

/-- Two graph parameters are functionally equivalent when each is bounded by
some numerical function of the other. -/
def FunctionallyEquivalent (p q : GraphParam) : Prop :=
  (∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    p (V := V) G ≤ f (q (V := V) G)) ∧
  (∃ g : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    q (V := V) G ≤ g (p (V := V) G))

end TwinWidth

/- ===== end Equivalence/FunctionalEquivalence.lean ===== -/

/- ===== begin Order/Divisions.lean ===== -/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TwinWidth contributors
-/

/-
# Divisions of finite intervals

This file contains the finite interval divisions used by the mixed-minor side of
the twin-width/mixed-minor equivalence.  A `Division n k` is represented by its
parts, together with the properties needed downstream: nonempty parts,
disjointness, covering, and order-convexity.
-/

namespace TwinWidth

/-- A `k`-division of `Fin n` is a partition into `k` nonempty convex parts.

The intended use is a partition of the linearly ordered rows or columns of a
matrix into consecutive intervals.  The fields expose exactly the API used by
mixed cells; the concrete representation is deliberately neutral so that a
cut-point implementation can replace it later without changing downstream
statements.
-/
structure Division (n k : ℕ) where
  /-- The `i`-th part of the division. -/
  part : Fin k → Finset (Fin n)
  /-- Every part is nonempty. -/
  part_nonempty : ∀ i, (part i).Nonempty
  /-- Distinct parts are disjoint. -/
  part_disjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (part i) (part j)
  /-- The parts cover the whole finite interval. -/
  part_cover : ∀ x : Fin n, ∃ i, x ∈ part i
  /-- Parts are convex in the natural order on `Fin n`. -/
  part_convex :
    ∀ i ⦃a b c : Fin n⦄, a ∈ part i → c ∈ part i → a ≤ b → b ≤ c → b ∈ part i
  /-- Earlier-indexed parts are strictly before later-indexed parts. -/
  part_ordered :
    ∀ ⦃i j : Fin k⦄, i < j →
      ∀ ⦃a b : Fin n⦄, a ∈ part i → b ∈ part j → a < b

namespace Division

variable {n k : ℕ} (D : Division n k)

@[simp] theorem part_nonempty' (i : Fin k) : (D.part i).Nonempty :=
  D.part_nonempty i

theorem part_disjoint' ⦃i j : Fin k⦄ (hij : i ≠ j) :
    Disjoint (D.part i) (D.part j) :=
  D.part_disjoint hij

theorem part_cover' (x : Fin n) : ∃ i, x ∈ D.part i :=
  D.part_cover x

theorem part_convex' (i : Fin k) ⦃a b c : Fin n⦄
    (ha : a ∈ D.part i) (hc : c ∈ D.part i) (hab : a ≤ b) (hbc : b ≤ c) :
    b ∈ D.part i :=
  D.part_convex i ha hc hab hbc

theorem part_ordered' ⦃i j : Fin k⦄ (hij : i < j)
    ⦃a b : Fin n⦄ (ha : a ∈ D.part i) (hb : b ∈ D.part j) :
    a < b :=
  D.part_ordered hij ha hb

/-- Distinct indices of a division have distinct parts. -/
theorem part_injective : Function.Injective D.part := by
  intro i j hij_parts
  by_contra hij
  rcases D.part_nonempty i with ⟨x, hx⟩
  have hxj : x ∈ D.part j := by simpa [hij_parts] using hx
  exact Finset.disjoint_left.mp (D.part_disjoint hij) hx hxj

/-- A division of `Fin n` into `k` nonempty parts has at most `n` parts. -/
theorem card_parts_le (D : Division n k) : k ≤ n := by
  classical
  let f : Fin k → Fin n := fun i => Classical.choose (D.part_nonempty i)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hi : f i ∈ D.part i := Classical.choose_spec (D.part_nonempty i)
    have hj : f i ∈ D.part j := by
      have hj' : f j ∈ D.part j := Classical.choose_spec (D.part_nonempty j)
      simpa [hij] using hj'
    exact Finset.disjoint_left.mp (D.part_disjoint hne) hi hj
  simpa using Fintype.card_le_of_injective f hf

/-- Build a division as the fibers of an order-preserving surjection.

This constructor is useful for index coarsenings: if consecutive source
indices are sent to the same target index, the fibers are nonempty consecutive
blocks and therefore form a `Division`. -/
noncomputable def ofMonotoneSurjective {n k : ℕ} (f : Fin n → Fin k)
    (hmono : ∀ ⦃a b : Fin n⦄, a ≤ b → f a ≤ f b)
    (hsurj : ∀ j : Fin k, ∃ a : Fin n, f a = j) :
    Division n k where
  part j := (Finset.univ : Finset (Fin n)).filter fun a => f a = j
  part_nonempty := by
    intro j
    rcases hsurj j with ⟨a, ha⟩
    exact ⟨a, by simp [ha]⟩
  part_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hy
    have hxi : f x = i := by simpa using hx
    have hxj : f x = j := by simpa using hy
    exact hij (hxi.symm.trans hxj)
  part_cover := by
    intro x
    exact ⟨f x, by simp⟩
  part_convex := by
    intro i a b c ha hc hab hbc
    have hai : f a = i := by simpa using ha
    have hci : f c = i := by simpa using hc
    have hab' : f a ≤ f b := hmono hab
    have hbc' : f b ≤ f c := hmono hbc
    have hbi : f b = i := by
      exact le_antisymm (by simpa [hci] using hbc') (by simpa [hai] using hab')
    simp [hbi]
  part_ordered := by
    intro i j hij a b ha hb
    have hai : f a = i := by simpa using ha
    have hbj : f b = j := by simpa using hb
    by_contra hnot
    have hba : b ≤ a := le_of_not_gt hnot
    have hle : f b ≤ f a := hmono hba
    have hji : j ≤ i := by simpa [hai, hbj] using hle
    exact (not_lt_of_ge hji) hij

@[simp] theorem mem_ofMonotoneSurjective_part {n k : ℕ}
    (f : Fin n → Fin k)
    (hmono : ∀ ⦃a b : Fin n⦄, a ≤ b → f a ≤ f b)
    (hsurj : ∀ j : Fin k, ∃ a : Fin n, f a = j)
    (j : Fin k) (a : Fin n) :
    a ∈ (ofMonotoneSurjective f hmono hsurj).part j ↔ f a = j := by
  simp [ofMonotoneSurjective]

/-- The first element of a division part. -/
noncomputable def first (i : Fin k) : Fin n :=
  (D.part i).min' (D.part_nonempty i)

/-- The last element of a division part. -/
noncomputable def last (i : Fin k) : Fin n :=
  (D.part i).max' (D.part_nonempty i)

theorem first_mem (i : Fin k) : D.first i ∈ D.part i :=
  Finset.min'_mem _ _

theorem last_mem (i : Fin k) : D.last i ∈ D.part i :=
  Finset.max'_mem _ _

/-- Equal division parts have the same first element. -/
theorem first_eq_of_part_eq {D E : Division n k} {i j : Fin k}
    (hpart : D.part i = E.part j) :
    D.first i = E.first j := by
  classical
  apply le_antisymm
  · exact Finset.min'_le _ _ (by simpa [hpart] using E.first_mem j)
  · exact Finset.min'_le _ _ (by simpa [hpart] using D.first_mem i)

/-- Reindex the parts of a division along an equality of the number of parts. -/
noncomputable def castIndex {l : ℕ} (h : k = l) (D : Division n k) :
    Division n l where
  part i := D.part ((finCongr h).symm i)
  part_nonempty i := D.part_nonempty ((finCongr h).symm i)
  part_disjoint := by
    intro i j hij
    apply D.part_disjoint
    intro heq
    exact hij (by
      apply (finCongr h).symm.injective
      simpa using heq)
  part_cover := by
    intro x
    rcases D.part_cover x with ⟨i, hi⟩
    exact ⟨finCongr h i, by simpa using hi⟩
  part_convex := by
    intro i a b c ha hc hab hbc
    exact D.part_convex ((finCongr h).symm i) ha hc hab hbc
  part_ordered := by
    intro i j hij a b ha hb
    have hij' : (finCongr h).symm i < (finCongr h).symm j := by
      apply Fin.mk_lt_mk.mpr
      exact Fin.mk_lt_mk.mp hij
    exact D.part_ordered hij' ha hb

/-- Reindexing a division does not change its finite set of parts. -/
@[simp] theorem parts_castIndex {n k l : ℕ} (h : k = l) (D : Division n k) :
    ((Finset.univ : Finset (Fin l)).map ⟨(Division.castIndex h D).part,
      (Division.castIndex h D).part_injective⟩) =
    ((Finset.univ : Finset (Fin k)).map ⟨D.part, D.part_injective⟩) := by
  classical
  ext R
  constructor
  · intro hR
    rcases Finset.mem_map.mp hR with ⟨a, _ha, haR⟩
    change (Division.castIndex h D).part a = R at haR
    refine Finset.mem_map.mpr ⟨(finCongr h).symm a, Finset.mem_univ _, ?_⟩
    simpa [Division.castIndex] using haR
  · intro hR
    rcases Finset.mem_map.mp hR with ⟨a, _ha, haR⟩
    change D.part a = R at haR
    refine Finset.mem_map.mpr ⟨finCongr h a, Finset.mem_univ _, ?_⟩
    simpa [Division.castIndex] using haR

/-- The singleton division of `Fin n` into `n` consecutive singleton parts. -/
def singleton (n : ℕ) : Division n n where
  part i := {i}
  part_nonempty i := ⟨i, by simp⟩
  part_disjoint := by
    intro i j hij
    simp [hij]
  part_cover := by
    intro x
    exact ⟨x, by simp⟩
  part_convex := by
    intro i a b c ha hc hab hbc
    have hai : a = i := by simpa using ha
    have hci : c = i := by simpa using hc
    subst a
    subst c
    have hbi : b = i := le_antisymm hbc hab
    simp [hbi]
  part_ordered := by
    intro i j hij a b ha hb
    have hai : a = i := by simpa using ha
    have hbj : b = j := by simpa using hb
    subst a
    subst b
    exact hij

/-- Number of pairs in a nontrivial finite interval.  For an interval of size
`l ≥ 2`, this is positive and equals `⌊l / 2⌋`. -/
def pairCount (l : ℕ) : ℕ :=
  l / 2

theorem pairCount_pos {l : ℕ} (hl : 2 ≤ l) : 0 < pairCount l := by
  unfold pairCount
  exact Nat.div_pos hl (by decide : 0 < 2)

/-- The left paired coarsening map: `0,1 ↦ 0`, `2,3 ↦ 1`, and so on, with the
last target index absorbing a possible leftover source index. -/
def pairLeftIndex {l : ℕ} (hl : 2 ≤ l) (a : Fin l) : Fin (pairCount l) :=
  ⟨min (a.1 / 2) (pairCount l - 1), by
    have hq : 0 < pairCount l := pairCount_pos hl
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

theorem pairLeftIndex_mono {l : ℕ} (hl : 2 ≤ l)
    {a b : Fin l} (hab : a ≤ b) :
    pairLeftIndex hl a ≤ pairLeftIndex hl b := by
  rw [Fin.le_iff_val_le_val]
  have habv : a.1 ≤ b.1 := Fin.le_iff_val_le_val.mp hab
  exact min_le_min (Nat.div_le_div_right habv) le_rfl

theorem pairLeftIndex_surjective {l : ℕ} (hl : 2 ≤ l) :
    ∀ j : Fin (pairCount l), ∃ a : Fin l, pairLeftIndex hl a = j := by
  intro j
  refine ⟨⟨2 * j.1, ?_⟩, ?_⟩
  · have hj : j.1 < l / 2 := j.2
    have hmul : 2 * j.1 < 2 * (l / 2) :=
      Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
    have hle : 2 * (l / 2) ≤ l := by
      calc
        2 * (l / 2) ≤ 2 * (l / 2) + l % 2 := Nat.le_add_right _ _
        _ = l := by rw [Nat.div_add_mod l 2]
    exact lt_of_lt_of_le hmul hle
  · ext
    have hjle : j.1 ≤ pairCount l - 1 := by omega
    have hjle' : j.1 ≤ l / 2 - 1 := by simpa [pairCount] using hjle
    simp [pairLeftIndex, pairCount, hjle']

/-- The left paired division of the index interval. -/
noncomputable def pairLeftIndexDivision (l : ℕ) (hl : 2 ≤ l) :
    Division l (pairCount l) :=
  ofMonotoneSurjective (pairLeftIndex hl)
    (fun _ _ hab => pairLeftIndex_mono hl hab)
    (pairLeftIndex_surjective hl)

/-- The cut index represented by a part of the left paired division.  The
`j`-th paired part always contains source indices `2*j` and `2*j+1`. -/
def pairLeftCutIndex {l : ℕ} (hl : 2 ≤ l) (j : Fin (pairCount l)) : Fin (l - 1) :=
  ⟨2 * j.1, by
    have hj : j.1 < l / 2 := j.2
    have hmul : 2 * j.1 < 2 * (l / 2) :=
      Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
    have hle : 2 * (l / 2) ≤ l := by
      calc
        2 * (l / 2) ≤ 2 * (l / 2) + l % 2 := Nat.le_add_right _ _
        _ = l := by rw [Nat.div_add_mod l 2]
    have hlt : 2 * j.1 < l := lt_of_lt_of_le hmul hle
    omega⟩

@[simp] theorem pairLeftIndex_pairLeftCutIndex_castSucc {l : ℕ} (hl : 2 ≤ l)
    (j : Fin (pairCount l)) :
    pairLeftIndex hl
        ((finCongr (by omega : l - 1 + 1 = l)) (pairLeftCutIndex hl j).castSucc) = j := by
  ext
  have hjle : j.1 ≤ pairCount l - 1 := by omega
  have hjle' : j.1 ≤ l / 2 - 1 := by simpa [pairCount] using hjle
  simp [pairLeftCutIndex, pairLeftIndex, pairCount, hjle']

@[simp] theorem pairLeftIndex_pairLeftCutIndex_succ {l : ℕ} (hl : 2 ≤ l)
    (j : Fin (pairCount l)) :
    pairLeftIndex hl
        ((finCongr (by omega : l - 1 + 1 = l)) (pairLeftCutIndex hl j).succ) = j := by
  ext
  have hjle : j.1 ≤ pairCount l - 1 := by omega
  have hjle' : j.1 ≤ l / 2 - 1 := by simpa [pairCount] using hjle
  have hdiv : (2 * j.1 + 1) / 2 = j.1 := by
    rw [show 2 * j.1 + 1 = 2 * j.1 + 1 by rfl]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [pairLeftCutIndex, pairLeftIndex, pairCount, hdiv, hjle']

theorem pairLeftIndex_val_bounds {l : ℕ} (hl : 2 ≤ l)
    {a : Fin l} {b : Fin (pairCount l)}
    (h : pairLeftIndex hl a = b) :
    2 * b.1 ≤ a.1 ∧ a.1 ≤ 2 * b.1 + 2 := by
  have hqpos : 0 < pairCount l := pairCount_pos hl
  have hbval : b.1 = min (a.1 / 2) (pairCount l - 1) := by
    simpa [pairLeftIndex] using congrArg Fin.val h.symm
  have hble_div : b.1 ≤ a.1 / 2 := by
    rw [hbval]
    exact Nat.min_le_left _ _
  have hleft : 2 * b.1 ≤ a.1 := by
    calc
      2 * b.1 ≤ 2 * (a.1 / 2) := Nat.mul_le_mul_left 2 hble_div
      _ ≤ a.1 := by
        calc
          2 * (a.1 / 2) ≤ 2 * (a.1 / 2) + a.1 % 2 := Nat.le_add_right _ _
          _ = a.1 := by rw [Nat.div_add_mod a.1 2]
  have hright : a.1 ≤ 2 * b.1 + 2 := by
    by_cases hbtop : b.1 = pairCount l - 1
    · have hlbound : l ≤ 2 * pairCount l + 1 := by
        unfold pairCount
        have h := Nat.div_add_mod l 2
        have hmod : l % 2 < 2 := Nat.mod_lt l (by decide : 0 < 2)
        omega
      have ha : a.1 + 1 ≤ l := Nat.succ_le_of_lt a.2
      omega
    · have hmin_left : min (a.1 / 2) (pairCount l - 1) = a.1 / 2 := by
        by_cases hle : a.1 / 2 ≤ pairCount l - 1
        · exact Nat.min_eq_left hle
        · have hmin : min (a.1 / 2) (pairCount l - 1) = pairCount l - 1 :=
            Nat.min_eq_right (le_of_not_ge hle)
          exact False.elim (hbtop (by omega))
      have hdiv : a.1 / 2 = b.1 := by omega
      have hmod : a.1 % 2 < 2 := Nat.mod_lt a.1 (by decide : 0 < 2)
      have hdecomp := Nat.div_add_mod a.1 2
      omega
  exact ⟨hleft, hright⟩

/-- The right paired coarsening map: the first source index is isolated, then
`1,2 ↦ 1`, `3,4 ↦ 2`, and so on, with the last target index absorbing any
leftover tail. -/
def pairRightIndex {l : ℕ} (hl : 2 ≤ l) (a : Fin l) : Fin (pairCount l) :=
  ⟨min ((a.1 + 1) / 2) (pairCount l - 1), by
    have hq : 0 < pairCount l := pairCount_pos hl
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

theorem pairRightIndex_mono {l : ℕ} (hl : 2 ≤ l)
    {a b : Fin l} (hab : a ≤ b) :
    pairRightIndex hl a ≤ pairRightIndex hl b := by
  rw [Fin.le_iff_val_le_val]
  have habv : a.1 ≤ b.1 := Fin.le_iff_val_le_val.mp hab
  have hplus : a.1 + 1 ≤ b.1 + 1 := Nat.succ_le_succ habv
  exact min_le_min (Nat.div_le_div_right hplus) le_rfl

theorem pairRightIndex_surjective {l : ℕ} (hl : 2 ≤ l) :
    ∀ j : Fin (pairCount l), ∃ a : Fin l, pairRightIndex hl a = j := by
  intro j
  by_cases hj0 : j.1 = 0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    ext
    simp [pairRightIndex, pairCount, hj0]
  · refine ⟨⟨2 * j.1 - 1, ?_⟩, ?_⟩
    · have hj : j.1 < l / 2 := j.2
      have hmul : 2 * j.1 < 2 * (l / 2) :=
        Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
      have hle : 2 * (l / 2) ≤ l := by
        calc
          2 * (l / 2) ≤ 2 * (l / 2) + l % 2 := Nat.le_add_right _ _
          _ = l := by rw [Nat.div_add_mod l 2]
      have hpos : 0 < 2 * j.1 := by omega
      exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le hmul hle)
    · ext
      have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj0
      have hjle : j.1 ≤ pairCount l - 1 := by omega
      have hjle' : j.1 ≤ l / 2 - 1 := by simpa [pairCount] using hjle
      have hval : (2 * j.1 - 1 + 1) / 2 = j.1 := by
        have hsub : 2 * j.1 - 1 + 1 = 2 * j.1 := by omega
        rw [hsub]
        exact Nat.mul_div_right j.1 (by decide : 0 < 2)
      simp [pairRightIndex, pairCount, hval, hjle']

/-- The right paired division of the index interval. -/
noncomputable def pairRightIndexDivision (l : ℕ) (hl : 2 ≤ l) :
    Division l (pairCount l) :=
  ofMonotoneSurjective (pairRightIndex hl)
    (fun _ _ hab => pairRightIndex_mono hl hab)
    (pairRightIndex_surjective hl)

theorem pairRightIndex_val_bounds {l : ℕ} (hl : 2 ≤ l)
    {a : Fin l} {b : Fin (pairCount l)}
    (h : pairRightIndex hl a = b) :
    2 * b.1 ≤ a.1 + 1 ∧ a.1 + 1 ≤ 2 * b.1 + 3 := by
  have hqpos : 0 < pairCount l := pairCount_pos hl
  have hbval : b.1 = min ((a.1 + 1) / 2) (pairCount l - 1) := by
    simpa [pairRightIndex] using congrArg Fin.val h.symm
  have hble_div : b.1 ≤ (a.1 + 1) / 2 := by
    rw [hbval]
    exact Nat.min_le_left _ _
  have hleft : 2 * b.1 ≤ a.1 + 1 := by
    calc
      2 * b.1 ≤ 2 * ((a.1 + 1) / 2) := Nat.mul_le_mul_left 2 hble_div
      _ ≤ a.1 + 1 := by
        calc
          2 * ((a.1 + 1) / 2) ≤
              2 * ((a.1 + 1) / 2) + (a.1 + 1) % 2 := Nat.le_add_right _ _
          _ = a.1 + 1 := by rw [Nat.div_add_mod (a.1 + 1) 2]
  have hright : a.1 + 1 ≤ 2 * b.1 + 3 := by
    by_cases hbtop : b.1 = pairCount l - 1
    · have hlbound : l ≤ 2 * pairCount l + 1 := by
        unfold pairCount
        have h := Nat.div_add_mod l 2
        have hmod : l % 2 < 2 := Nat.mod_lt l (by decide : 0 < 2)
        omega
      have ha : a.1 + 1 ≤ l := Nat.succ_le_of_lt a.2
      omega
    · have hmin_left : min ((a.1 + 1) / 2) (pairCount l - 1) = (a.1 + 1) / 2 := by
        by_cases hle : (a.1 + 1) / 2 ≤ pairCount l - 1
        · exact Nat.min_eq_left hle
        · have hmin :
              min ((a.1 + 1) / 2) (pairCount l - 1) = pairCount l - 1 :=
            Nat.min_eq_right (le_of_not_ge hle)
          exact False.elim (hbtop (by omega))
      have hdiv : (a.1 + 1) / 2 = b.1 := by omega
      have hmod : (a.1 + 1) % 2 < 2 := Nat.mod_lt (a.1 + 1) (by decide : 0 < 2)
      have hdecomp := Nat.div_add_mod (a.1 + 1) 2
      omega
  exact ⟨hleft, hright⟩

/-- Every adjacent pair of source indices is grouped by at least one of the two
paired coarsenings.  Even cuts are grouped by the left pairing and odd cuts by
the shifted right pairing. -/
theorem pairIndex_adjacent_same {l : ℕ} (hl : 2 ≤ l) (i : Fin (l - 1)) :
    pairLeftIndex hl ((finCongr (by omega : l - 1 + 1 = l)) i.castSucc) =
        pairLeftIndex hl ((finCongr (by omega : l - 1 + 1 = l)) i.succ) ∨
      pairRightIndex hl ((finCongr (by omega : l - 1 + 1 = l)) i.castSucc) =
        pairRightIndex hl ((finCongr (by omega : l - 1 + 1 = l)) i.succ) := by
  rcases Nat.mod_two_eq_zero_or_one i.1 with hmod | hmod
  · left
    ext
    have hi : i.1 = 2 * (i.1 / 2) := by
      have h := Nat.div_add_mod i.1 2
      omega
    have hdiv : (i.1 + 1) / 2 = i.1 / 2 := by
      rw [hi]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [pairLeftIndex, hdiv]
  · right
    ext
    have hi : i.1 = 2 * (i.1 / 2) + 1 := by
      have h := Nat.div_add_mod i.1 2
      omega
    have hdiv : (i.1 + 2) / 2 = (i.1 + 1) / 2 := by
      rw [hi]
      have h₁ : (2 * (i.1 / 2) + 1 + 2) / 2 = i.1 / 2 + 1 := by
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      have h₂ : (2 * (i.1 / 2) + 1 + 1) / 2 = i.1 / 2 + 1 := by
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      exact h₁.trans h₂.symm
    change
      min ((i.1 + 1) / 2) (pairCount l - 1) =
        min ((i.1 + 1 + 1) / 2) (pairCount l - 1)
    rw [show i.1 + 1 + 1 = i.1 + 2 by omega, hdiv]

/-- Adjacent-pair coverage in the common `k + 1` source-size form. -/
theorem pairIndex_adjacent_same_succ {k : ℕ} (hk : 0 < k) (i : Fin k) :
    pairLeftIndex (l := k + 1) (by omega) i.castSucc =
        pairLeftIndex (l := k + 1) (by omega) i.succ ∨
      pairRightIndex (l := k + 1) (by omega) i.castSucc =
        pairRightIndex (l := k + 1) (by omega) i.succ := by
  rcases Nat.mod_two_eq_zero_or_one i.1 with hmod | hmod
  · left
    ext
    have hi : i.1 = 2 * (i.1 / 2) := by
      have h := Nat.div_add_mod i.1 2
      omega
    have hdiv : (i.1 + 1) / 2 = i.1 / 2 := by
      rw [hi]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [pairLeftIndex, hdiv]
  · right
    ext
    have hi : i.1 = 2 * (i.1 / 2) + 1 := by
      have h := Nat.div_add_mod i.1 2
      omega
    have hdiv : (i.1 + 2) / 2 = (i.1 + 1) / 2 := by
      rw [hi]
      have h₁ : (2 * (i.1 / 2) + 1 + 2) / 2 = i.1 / 2 + 1 := by
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      have h₂ : (2 * (i.1 / 2) + 1 + 1) / 2 = i.1 / 2 + 1 := by
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      exact h₁.trans h₂.symm
    change
      min ((i.1 + 1) / 2) (pairCount (k + 1) - 1) =
      min ((i.1 + 1 + 1) / 2) (pairCount (k + 1) - 1)
    rw [show i.1 + 1 + 1 = i.1 + 2 by omega, hdiv]

/-- The left endpoint of a cut index, viewed as a source index. -/
def cutLeftIndex {l : ℕ} (j : Fin (l - 1)) : Fin l :=
  ⟨j.1, by omega⟩

/-- The right endpoint of a cut index, viewed as a source index. -/
def cutRightIndex {l : ℕ} (j : Fin (l - 1)) : Fin l :=
  ⟨j.1 + 1, by omega⟩

@[simp] theorem cutLeftIndex_val {l : ℕ} (j : Fin (l - 1)) :
    (cutLeftIndex j : Fin l).1 = j.1 := rfl

@[simp] theorem cutRightIndex_val {l : ℕ} (j : Fin (l - 1)) :
    (cutRightIndex j : Fin l).1 = j.1 + 1 := rfl

/-- The paired target used by the Lemma 13 counting proof for an original
zone/cut item.  Zones are assigned to the left pairing; a cut is assigned to
whichever of the two pairings groups its two adjacent column parts. -/
def pairedItemTarget {l : ℕ} (hl : 2 ≤ l) :
    Sum (Fin l) (Fin (l - 1)) → Sum (Fin (pairCount l)) (Fin (pairCount l))
  | Sum.inl j => Sum.inl (pairLeftIndex hl j)
  | Sum.inr j =>
      if _h :
          pairLeftIndex hl (cutLeftIndex j) =
            pairLeftIndex hl (cutRightIndex j) then
        Sum.inl (pairLeftIndex hl (cutLeftIndex j))
      else
        Sum.inr (pairRightIndex hl (cutLeftIndex j))

/-- A small local offset inside the paired target.  Together with
`pairedItemTarget`, this is injective; the target fiber size is therefore
bounded by `10`. -/
def pairedItemCode {l : ℕ} (hl : 2 ≤ l) :
    Sum (Fin l) (Fin (l - 1)) → Fin 10
  | Sum.inl j =>
      let b := pairLeftIndex hl j
      ⟨j.1 - 2 * b.1, by
        have hb := pairLeftIndex_val_bounds hl (a := j) (b := b) rfl
        omega⟩
  | Sum.inr j =>
      let j₀ : Fin l := cutLeftIndex j
      if h :
          pairLeftIndex hl j₀ =
            pairLeftIndex hl (cutRightIndex j) then
        let b := pairLeftIndex hl j₀
        ⟨3 + (j.1 - 2 * b.1), by
          have hb := pairLeftIndex_val_bounds hl (a := j₀) (b := b) rfl
          simp [j₀] at hb
          omega⟩
      else
        let b := pairRightIndex hl j₀
        ⟨6 + (j.1 + 1 - 2 * b.1), by
          have hb := pairRightIndex_val_bounds hl (a := j₀) (b := b) rfl
          simp [j₀] at hb
          omega⟩

/-- The paired target together with the local code determines the original
zone/cut item.  This finite-fiber estimate is used in the Lemma 13 counting
argument: at most ten original mixed items can be charged to one paired
auxiliary entry. -/
theorem pairedItemTarget_code_injective {l : ℕ} (hl : 2 ≤ l) :
    Function.Injective fun x : Sum (Fin l) (Fin (l - 1)) =>
      (pairedItemTarget hl x, pairedItemCode hl x) := by
  intro x y hxy
  have hcode : (pairedItemCode hl x).1 = (pairedItemCode hl y).1 := by
    simpa using congrArg (fun p => (p.2 : Fin 10).1) hxy
  cases x with
  | inl xz =>
      cases y with
      | inl yz =>
          have ht :
              pairLeftIndex hl xz = pairLeftIndex hl yz := by
            have h := congrArg Prod.fst hxy
            simpa [pairedItemTarget] using h
          have hc :
              xz.1 - 2 * (pairLeftIndex hl xz).1 =
                yz.1 - 2 * (pairLeftIndex hl yz).1 := by
            have h := congrArg (fun p => (p.2 : Fin 10).1) hxy
            simpa [pairedItemCode] using h
          have hx := pairLeftIndex_val_bounds hl (a := xz)
            (b := pairLeftIndex hl xz) rfl
          have hy := pairLeftIndex_val_bounds hl (a := yz)
            (b := pairLeftIndex hl yz) rfl
          have hval : xz.1 = yz.1 := by
            have htv : (pairLeftIndex hl xz).1 = (pairLeftIndex hl yz).1 := by
              exact congrArg Fin.val ht
            omega
          apply congrArg Sum.inl
          exact Fin.ext hval
      | inr yc =>
          by_cases hyleft :
              pairLeftIndex hl (cutLeftIndex yc) =
                pairLeftIndex hl (cutRightIndex yc)
          · have hxcode : (pairedItemCode hl (Sum.inl xz)).1 < 3 := by
              have hb := pairLeftIndex_val_bounds hl (a := xz)
                (b := pairLeftIndex hl xz) rfl
              simp [pairedItemCode]
              omega
            have hycode : 3 ≤ (pairedItemCode hl (Sum.inr yc)).1 := by
              let y₀ : Fin l := cutLeftIndex yc
              have hb := pairLeftIndex_val_bounds hl (a := y₀)
                (b := pairLeftIndex hl y₀) rfl
              simp [pairedItemCode, hyleft, y₀] at hb ⊢
            have hcode' :
                (pairedItemCode hl (Sum.inl xz)).1 =
                  (pairedItemCode hl (Sum.inr yc)).1 := hcode
            omega
          · have hxcode : (pairedItemCode hl (Sum.inl xz)).1 < 3 := by
              have hb := pairLeftIndex_val_bounds hl (a := xz)
                (b := pairLeftIndex hl xz) rfl
              simp [pairedItemCode]
              omega
            have hycode : 3 ≤ (pairedItemCode hl (Sum.inr yc)).1 := by
              let y₀ : Fin l := cutLeftIndex yc
              have hb := pairRightIndex_val_bounds hl (a := y₀)
                (b := pairRightIndex hl y₀) rfl
              simp [pairedItemCode, hyleft, y₀] at hb ⊢
              omega
            have hcode' :
                (pairedItemCode hl (Sum.inl xz)).1 =
                  (pairedItemCode hl (Sum.inr yc)).1 := hcode
            omega
  | inr xc =>
      cases y with
      | inl yz =>
          by_cases hxleft :
              pairLeftIndex hl (cutLeftIndex xc) =
                pairLeftIndex hl (cutRightIndex xc)
          · have hxcode : 3 ≤ (pairedItemCode hl (Sum.inr xc)).1 := by
              let x₀ : Fin l := cutLeftIndex xc
              have hb := pairLeftIndex_val_bounds hl (a := x₀)
                (b := pairLeftIndex hl x₀) rfl
              simp [pairedItemCode, hxleft, x₀] at hb ⊢
            have hycode : (pairedItemCode hl (Sum.inl yz)).1 < 3 := by
              have hb := pairLeftIndex_val_bounds hl (a := yz)
                (b := pairLeftIndex hl yz) rfl
              simp [pairedItemCode]
              omega
            have hcode' :
                (pairedItemCode hl (Sum.inr xc)).1 =
                  (pairedItemCode hl (Sum.inl yz)).1 := hcode
            omega
          · have hxcode : 3 ≤ (pairedItemCode hl (Sum.inr xc)).1 := by
              let x₀ : Fin l := cutLeftIndex xc
              have hb := pairRightIndex_val_bounds hl (a := x₀)
                (b := pairRightIndex hl x₀) rfl
              simp [pairedItemCode, hxleft, x₀] at hb ⊢
              omega
            have hycode : (pairedItemCode hl (Sum.inl yz)).1 < 3 := by
              have hb := pairLeftIndex_val_bounds hl (a := yz)
                (b := pairLeftIndex hl yz) rfl
              simp [pairedItemCode]
              omega
            have hcode' :
                (pairedItemCode hl (Sum.inr xc)).1 =
                  (pairedItemCode hl (Sum.inl yz)).1 := hcode
            omega
      | inr yc =>
          by_cases hxleft :
              pairLeftIndex hl (cutLeftIndex xc) =
                pairLeftIndex hl (cutRightIndex xc)
          · by_cases hyleft :
              pairLeftIndex hl (cutLeftIndex yc) =
                pairLeftIndex hl (cutRightIndex yc)
            · have ht :
                pairLeftIndex hl (cutLeftIndex xc) =
                  pairLeftIndex hl (cutLeftIndex yc) := by
                have h := congrArg Prod.fst hxy
                simpa [pairedItemTarget, hxleft, hyleft] using h
              let x₀ : Fin l := cutLeftIndex xc
              let y₀ : Fin l := cutLeftIndex yc
              have hc :
                  3 + (xc.1 - 2 * (pairLeftIndex hl x₀).1) =
                    3 + (yc.1 - 2 * (pairLeftIndex hl y₀).1) := by
                have h := congrArg (fun p => (p.2 : Fin 10).1) hxy
                simpa [pairedItemTarget, pairedItemCode, x₀, y₀, hxleft, hyleft] using h
              have hx := pairLeftIndex_val_bounds hl (a := x₀)
                (b := pairLeftIndex hl x₀) rfl
              have hy := pairLeftIndex_val_bounds hl (a := y₀)
                (b := pairLeftIndex hl y₀) rfl
              have hval : xc.1 = yc.1 := by
                have htv : (pairLeftIndex hl x₀).1 = (pairLeftIndex hl y₀).1 := by
                  simpa [x₀, y₀] using congrArg Fin.val ht
                have hdiff :
                    xc.1 - 2 * (pairLeftIndex hl x₀).1 =
                      yc.1 - 2 * (pairLeftIndex hl y₀).1 := by
                  omega
                have hxge : 2 * (pairLeftIndex hl x₀).1 ≤ xc.1 := by
                  simpa [x₀] using hx.1
                have hyge : 2 * (pairLeftIndex hl y₀).1 ≤ yc.1 := by
                  simpa [y₀] using hy.1
                simp [x₀] at hx
                simp [y₀] at hy
                omega
              apply congrArg Sum.inr
              exact Fin.ext hval
            · have hxcode : (pairedItemCode hl (Sum.inr xc)).1 < 6 := by
                let x₀ : Fin l := cutLeftIndex xc
                have hb := pairLeftIndex_val_bounds hl (a := x₀)
                  (b := pairLeftIndex hl x₀) rfl
                simp [pairedItemCode, hxleft, x₀] at hb ⊢
                omega
              have hycode : 6 ≤ (pairedItemCode hl (Sum.inr yc)).1 := by
                let y₀ : Fin l := cutLeftIndex yc
                have hb := pairRightIndex_val_bounds hl (a := y₀)
                  (b := pairRightIndex hl y₀) rfl
                simp [pairedItemCode, hyleft, y₀] at hb ⊢
              omega
          · by_cases hyleft :
              pairLeftIndex hl (cutLeftIndex yc) =
                pairLeftIndex hl (cutRightIndex yc)
            · have hxcode : 6 ≤ (pairedItemCode hl (Sum.inr xc)).1 := by
                let x₀ : Fin l := cutLeftIndex xc
                have hb := pairRightIndex_val_bounds hl (a := x₀)
                  (b := pairRightIndex hl x₀) rfl
                simp [pairedItemCode, hxleft, x₀] at hb ⊢
              have hycode : (pairedItemCode hl (Sum.inr yc)).1 < 6 := by
                let y₀ : Fin l := cutLeftIndex yc
                have hb := pairLeftIndex_val_bounds hl (a := y₀)
                  (b := pairLeftIndex hl y₀) rfl
                simp [pairedItemCode, hyleft, y₀] at hb ⊢
                omega
              omega
            · have ht :
                pairRightIndex hl (cutLeftIndex xc) =
                  pairRightIndex hl (cutLeftIndex yc) := by
                have h := congrArg Prod.fst hxy
                simpa [pairedItemTarget, hxleft, hyleft] using h
              let x₀ : Fin l := cutLeftIndex xc
              let y₀ : Fin l := cutLeftIndex yc
              have hc :
                  6 + (xc.1 + 1 - 2 * (pairRightIndex hl x₀).1) =
                    6 + (yc.1 + 1 - 2 * (pairRightIndex hl y₀).1) := by
                have h := congrArg (fun p => (p.2 : Fin 10).1) hxy
                simpa [pairedItemCode, x₀, y₀, hxleft, hyleft] using h
              have hx := pairRightIndex_val_bounds hl (a := x₀)
                (b := pairRightIndex hl x₀) rfl
              have hy := pairRightIndex_val_bounds hl (a := y₀)
                (b := pairRightIndex hl y₀) rfl
              have hval : xc.1 = yc.1 := by
                have htv : (pairRightIndex hl x₀).1 = (pairRightIndex hl y₀).1 := by
                  simpa [x₀, y₀] using congrArg Fin.val ht
                have hdiff :
                    xc.1 + 1 - 2 * (pairRightIndex hl x₀).1 =
                      yc.1 + 1 - 2 * (pairRightIndex hl y₀).1 := by
                  omega
                have hxge : 2 * (pairRightIndex hl x₀).1 ≤ xc.1 + 1 := by
                  simpa [x₀] using hx.1
                have hyge : 2 * (pairRightIndex hl y₀).1 ≤ yc.1 + 1 := by
                  simpa [y₀] using hy.1
                simp [x₀] at hx
                simp [y₀] at hy
                omega
              apply congrArg Sum.inr
              exact Fin.ext hval

/-- Cast the common `k + 1` item type to the generic `l`/`l - 1` item type. -/
def pairedItemCastSucc {k : ℕ} :
    Sum (Fin (k + 1)) (Fin k) → Sum (Fin (k + 1)) (Fin ((k + 1) - 1))
  | Sum.inl j => Sum.inl j
  | Sum.inr j => Sum.inr ((finCongr (by omega : k = (k + 1) - 1)) j)

theorem pairedItemCastSucc_injective {k : ℕ} :
    Function.Injective (pairedItemCastSucc (k := k)) := by
  intro x y hxy
  cases x with
  | inl xz =>
      cases y with
      | inl yz =>
          apply congrArg Sum.inl
          simpa [pairedItemCastSucc] using hxy
      | inr yc =>
          simp [pairedItemCastSucc] at hxy
  | inr xc =>
      cases y with
      | inl yz =>
          simp [pairedItemCastSucc] at hxy
      | inr yc =>
          apply congrArg Sum.inr
          have h :
              (finCongr (by omega : k = (k + 1) - 1)) xc =
                (finCongr (by omega : k = (k + 1) - 1)) yc := by
            simpa [pairedItemCastSucc] using hxy
          exact (finCongr (by omega : k = (k + 1) - 1)).injective h

/-- Paired target in the common `k + 1` source-size form. -/
def pairedItemTargetSucc {k : ℕ} (hk : 0 < k) :
    Sum (Fin (k + 1)) (Fin k) →
      Sum (Fin (pairCount (k + 1))) (Fin (pairCount (k + 1))) :=
  fun x => pairedItemTarget (l := k + 1) (by omega) (pairedItemCastSucc x)

/-- Local code in the common `k + 1` source-size form. -/
def pairedItemCodeSucc {k : ℕ} (hk : 0 < k) :
    Sum (Fin (k + 1)) (Fin k) → Fin 10 :=
  fun x => pairedItemCode (l := k + 1) (by omega) (pairedItemCastSucc x)

@[simp] theorem pairedItemTargetSucc_zone {k : ℕ} (hk : 0 < k)
    (j : Fin (k + 1)) :
    pairedItemTargetSucc hk (Sum.inl j) =
      Sum.inl (pairLeftIndex (l := k + 1) (by omega) j) := by
  simp [pairedItemTargetSucc, pairedItemCastSucc, pairedItemTarget]

theorem pairedItemTargetSucc_cut_left {k : ℕ} (hk : 0 < k)
    (j : Fin k)
    (hleft :
      pairLeftIndex (l := k + 1) (by omega) j.castSucc =
        pairLeftIndex (l := k + 1) (by omega) j.succ) :
    pairedItemTargetSucc hk (Sum.inr j) =
      Sum.inl (pairLeftIndex (l := k + 1) (by omega) j.succ) := by
  unfold pairedItemTargetSucc pairedItemCastSucc pairedItemTarget
  simp only
  rw [dif_pos]
  · simpa [cutLeftIndex, cutRightIndex] using hleft
  · simpa [cutLeftIndex, cutRightIndex] using hleft

theorem pairedItemTargetSucc_cut_right {k : ℕ} (hk : 0 < k)
    (j : Fin k)
    (hleft :
      ¬ pairLeftIndex (l := k + 1) (by omega) j.castSucc =
        pairLeftIndex (l := k + 1) (by omega) j.succ) :
    pairedItemTargetSucc hk (Sum.inr j) =
      Sum.inr (pairRightIndex (l := k + 1) (by omega) j.castSucc) := by
  unfold pairedItemTargetSucc pairedItemCastSucc pairedItemTarget
  simp only
  rw [dif_neg]
  · apply congrArg Sum.inr
    ext
    change
      min ((j.1 + 1) / 2) (pairCount (k + 1) - 1) =
        min ((j.1 + 1) / 2) (pairCount (k + 1) - 1)
    rfl
  · intro h
    exact hleft (by simpa [cutLeftIndex, cutRightIndex] using h)

theorem pairedItemTargetSucc_code_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective fun x : Sum (Fin (k + 1)) (Fin k) =>
      (pairedItemTargetSucc hk x, pairedItemCodeSucc hk x) := by
  intro x y hxy
  have h :
      (pairedItemTarget (l := k + 1) (by omega) (pairedItemCastSucc x),
          pairedItemCode (l := k + 1) (by omega) (pairedItemCastSucc x)) =
        (pairedItemTarget (l := k + 1) (by omega) (pairedItemCastSucc y),
          pairedItemCode (l := k + 1) (by omega) (pairedItemCastSucc y)) := by
    simpa [pairedItemTargetSucc, pairedItemCodeSucc] using hxy
  exact pairedItemCastSucc_injective
    (pairedItemTarget_code_injective (l := k + 1) (by omega) h)

/-- Index map that identifies the two consecutive indices `i` and `i+1`.

It is the order-preserving surjection used to build the index division for a
fusion.  Values up to `i` are kept unchanged; values after `i` are shifted down
by one. -/
def fuseIndex {k : ℕ} (i : Fin (k + 1)) (a : Fin (k + 2)) : Fin (k + 1) :=
  if h : a.1 ≤ i.1 then
    ⟨a.1, lt_of_le_of_lt h i.2⟩
  else
    ⟨a.1 - 1, by omega⟩

theorem fuseIndex_mono {k : ℕ} (i : Fin (k + 1))
    {a b : Fin (k + 2)} (hab : a ≤ b) :
    fuseIndex i a ≤ fuseIndex i b := by
  rw [Fin.le_iff_val_le_val]
  have habv : a.1 ≤ b.1 := Fin.le_iff_val_le_val.mp hab
  by_cases ha : a.1 ≤ i.1 <;> by_cases hb : b.1 ≤ i.1 <;>
    simp [fuseIndex, ha, hb] <;> omega

/-- The division of the index interval which groups exactly the two adjacent
indices `i` and `i+1`, leaving all other indices as singleton parts. -/
noncomputable def fusionIndexDivision {k : ℕ} (i : Fin (k + 1)) :
    Division (k + 2) (k + 1) where
  part j := (Finset.univ : Finset (Fin (k + 2))).filter fun a => fuseIndex i a = j
  part_nonempty := by
    intro j
    by_cases hji : j ≤ i
    · refine ⟨j.castSucc, ?_⟩
      have hval : j.1 ≤ i.1 := Fin.le_iff_val_le_val.mp hji
      have hidx : fuseIndex i j.castSucc = j := by
        ext
        unfold fuseIndex
        simp [hval]
      simp [hidx]
    · refine ⟨j.succ, ?_⟩
      have hij : i < j := lt_of_not_ge hji
      have hlt : i.1 < j.1 := Fin.mk_lt_mk.mp hij
      have hnot : ¬ j.1 + 1 ≤ i.1 := by omega
      have hidx : fuseIndex i j.succ = j := by
        ext
        unfold fuseIndex
        simp [hnot]
      simp [hidx]
  part_disjoint := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro x hx hy
    have hx' : fuseIndex i x = a := by simpa using hx
    have hy' : fuseIndex i x = b := by simpa using hy
    exact hab (hx'.symm.trans hy')
  part_cover := by
    intro x
    exact ⟨fuseIndex i x, by simp⟩
  part_convex := by
    intro j a b c ha hc hab hbc
    have ha' : fuseIndex i a = j := by simpa using ha
    have hc' : fuseIndex i c = j := by simpa using hc
    have hab' : fuseIndex i a ≤ fuseIndex i b := fuseIndex_mono i hab
    have hbc' : fuseIndex i b ≤ fuseIndex i c := fuseIndex_mono i hbc
    have hb' : fuseIndex i b = j := by
      exact le_antisymm (by simpa [hc'] using hbc') (by simpa [ha'] using hab')
    simp [hb']
  part_ordered := by
    intro a b hab x y hx hy
    have hx' : fuseIndex i x = a := by simpa using hx
    have hy' : fuseIndex i y = b := by simpa using hy
    by_contra hnot
    have hyx : y ≤ x := le_of_not_gt hnot
    have hmono : fuseIndex i y ≤ fuseIndex i x := fuseIndex_mono i hyx
    have hba : b ≤ a := by simpa [hx', hy'] using hmono
    exact (not_lt_of_ge hba) hab

@[simp] theorem mem_fusionIndexDivision_part {k : ℕ}
    (i : Fin (k + 1)) (j : Fin (k + 1)) (a : Fin (k + 2)) :
    a ∈ (fusionIndexDivision i).part j ↔ fuseIndex i a = j := by
  simp [fusionIndexDivision]

theorem fuseIndex_eq_self_iff {k : ℕ}
    (i : Fin (k + 1)) (a : Fin (k + 2)) :
    fuseIndex i a = i ↔ a = i.castSucc ∨ a = i.succ := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    by_cases ha : a.1 ≤ i.1
    · left
      ext
      simp [fuseIndex, ha] at hv
      exact hv
    · right
      ext
      simp [fuseIndex, ha] at hv
      change a.1 = i.1 + 1
      omega
  · intro h
    rcases h with rfl | rfl
    · ext
      simp [fuseIndex]
    · ext
      have hnot : ¬ i.1 + 1 ≤ i.1 := by omega
      simp [fuseIndex, hnot]

theorem fuseIndex_eq_of_lt_iff {k : ℕ}
    {i j : Fin (k + 1)} (hji : j < i) (a : Fin (k + 2)) :
    fuseIndex i a = j ↔ a = j.castSucc := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    have hlt : j.1 < i.1 := Fin.mk_lt_mk.mp hji
    by_cases ha : a.1 ≤ i.1
    · ext
      simp [fuseIndex, ha] at hv
      exact hv
    · simp [fuseIndex, ha] at hv
      omega
  · intro h
    subst a
    ext
    have hle : j.1 ≤ i.1 := le_of_lt (Fin.mk_lt_mk.mp hji)
    simp [fuseIndex, hle]

theorem fuseIndex_eq_of_gt_iff {k : ℕ}
    {i j : Fin (k + 1)} (hij : i < j) (a : Fin (k + 2)) :
    fuseIndex i a = j ↔ a = j.succ := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    have hlt : i.1 < j.1 := Fin.mk_lt_mk.mp hij
    by_cases ha : a.1 ≤ i.1
    · simp [fuseIndex, ha] at hv
      omega
    · ext
      simp [fuseIndex, ha] at hv
      change a.1 = j.1 + 1
      omega
  · intro h
    subst a
    ext
    have hnot : ¬ j.1 + 1 ≤ i.1 := by
      have hlt : i.1 < j.1 := Fin.mk_lt_mk.mp hij
      omega
    simp [fuseIndex, hnot]

/-- The part family obtained by merging the consecutive parts `i` and `i+1`
of a division with `k+2` parts. -/
noncomputable def fusePart {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) (j : Fin (k + 1)) : Finset (Fin n) :=
  if j = i then
    D.part i.castSucc ∪ D.part i.succ
  else if j < i then
    D.part j.castSucc
  else
    D.part j.succ

@[simp] theorem fusePart_self {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    D.fusePart i i = D.part i.castSucc ∪ D.part i.succ := by
  simp [fusePart]

/-- `E` is obtained from `D` by merging the consecutive parts `i` and `i+1`. -/
def IsFusionAt {k : ℕ} (D : Division n (k + 2))
    (E : Division n (k + 1)) (i : Fin (k + 1)) : Prop :=
  ∀ j : Fin (k + 1), E.part j = D.fusePart i j

/-- Coarsen a division by grouping consecutive indices according to another
division of the index set. -/
noncomputable def coarsen {t : ℕ} (D : Division n k) (I : Division k t) :
    Division n t where
  part a := (I.part a).biUnion fun i => D.part i
  part_nonempty := by
    intro a
    classical
    rcases I.part_nonempty a with ⟨i, hi⟩
    rcases D.part_nonempty i with ⟨x, hx⟩
    exact ⟨x, Finset.mem_biUnion.mpr ⟨i, hi, hx⟩⟩
  part_disjoint := by
    intro a b hab
    classical
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    rcases Finset.mem_biUnion.mp hy with ⟨j, hj, hxj⟩
    have hij : i ≠ j := by
      intro hij
      subst j
      exact Finset.disjoint_left.mp (I.part_disjoint hab) hi hj
    exact Finset.disjoint_left.mp (D.part_disjoint hij) hxi hxj
  part_cover := by
    intro x
    classical
    rcases D.part_cover x with ⟨i, hi⟩
    rcases I.part_cover i with ⟨a, ha⟩
    exact ⟨a, Finset.mem_biUnion.mpr ⟨i, ha, hi⟩⟩
  part_convex := by
    intro a x y z hx hz hxy hyz
    classical
    rcases Finset.mem_biUnion.mp hx with ⟨ix, hix, hxD⟩
    rcases Finset.mem_biUnion.mp hz with ⟨iz, hiz, hzD⟩
    rcases D.part_cover y with ⟨iy, hyD⟩
    have hix_le_iy : ix ≤ iy := by
      by_contra hnot
      have hlt : iy < ix := lt_of_not_ge hnot
      have hyx : y < x := D.part_ordered hlt hyD hxD
      exact (not_lt_of_ge hxy) hyx
    have hiy_le_iz : iy ≤ iz := by
      by_contra hnot
      have hlt : iz < iy := lt_of_not_ge hnot
      have hzy : z < y := D.part_ordered hlt hzD hyD
      exact (not_lt_of_ge hyz) hzy
    have hiy : iy ∈ I.part a := I.part_convex a hix hiz hix_le_iy hiy_le_iz
    exact Finset.mem_biUnion.mpr ⟨iy, hiy, hyD⟩
  part_ordered := by
    intro a b hab x y hx hy
    classical
    rcases Finset.mem_biUnion.mp hx with ⟨ix, hix, hxD⟩
    rcases Finset.mem_biUnion.mp hy with ⟨iy, hiy, hyD⟩
    exact D.part_ordered (I.part_ordered hab hix hiy) hxD hyD

theorem part_subset_coarsen_part {t : ℕ} (D : Division n k) (I : Division k t)
    {a : Fin t} {i : Fin k} (hi : i ∈ I.part a) :
    D.part i ⊆ (D.coarsen I).part a := by
  classical
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩

/-- Fuse the two consecutive parts `i` and `i+1` of a division. -/
noncomputable def fuse {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) : Division n (k + 1) :=
  D.coarsen (fusionIndexDivision i)

theorem coarsen_fusionIndexDivision_part_eq_fusePart {k : ℕ}
    (D : Division n (k + 2)) (i : Fin (k + 1)) (j : Fin (k + 1)) :
    (D.coarsen (fusionIndexDivision i)).part j = D.fusePart i j := by
  classical
  ext x
  by_cases heq : j = i
  · subst j
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
      have hidx : fuseIndex i a = i := (mem_fusionIndexDivision_part i i a).mp ha
      rcases (fuseIndex_eq_self_iff i a).mp hidx with rfl | rfl
      · simp [fusePart, hxa]
      · simp [fusePart, hxa]
    · intro hx
      rw [fusePart_self] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · refine Finset.mem_biUnion.mpr ⟨i.castSucc, ?_, hx⟩
        exact (mem_fusionIndexDivision_part i i i.castSucc).mpr
          ((fuseIndex_eq_self_iff i i.castSucc).mpr (Or.inl rfl))
      · refine Finset.mem_biUnion.mpr ⟨i.succ, ?_, hx⟩
        exact (mem_fusionIndexDivision_part i i i.succ).mpr
          ((fuseIndex_eq_self_iff i i.succ).mpr (Or.inr rfl))
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · constructor
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
        have hidx : fuseIndex i a = j := (mem_fusionIndexDivision_part i j a).mp ha
        have ha' : a = j.castSucc := (fuseIndex_eq_of_lt_iff hlt a).mp hidx
        subst a
        simpa [fusePart, heq, hlt] using hxa
      · intro hx
        refine Finset.mem_biUnion.mpr ⟨j.castSucc, ?_, ?_⟩
        · exact (mem_fusionIndexDivision_part i j j.castSucc).mpr
            ((fuseIndex_eq_of_lt_iff hlt j.castSucc).mpr rfl)
        · simpa [fusePart, heq, hlt] using hx
    · have hnlt : ¬ j < i := not_lt_of_ge (le_of_lt hgt)
      constructor
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
        have hidx : fuseIndex i a = j := (mem_fusionIndexDivision_part i j a).mp ha
        have ha' : a = j.succ := (fuseIndex_eq_of_gt_iff hgt a).mp hidx
        subst a
        simpa [fusePart, heq, hnlt] using hxa
      · intro hx
        refine Finset.mem_biUnion.mpr ⟨j.succ, ?_, ?_⟩
        · exact (mem_fusionIndexDivision_part i j j.succ).mpr
            ((fuseIndex_eq_of_gt_iff hgt j.succ).mpr rfl)
        · simpa [fusePart, heq, hnlt] using hx

theorem isFusionAt_fuse {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    IsFusionAt D (D.fuse i) i := by
  intro j
  exact coarsen_fusionIndexDivision_part_eq_fusePart D i j

theorem fuse_part_self {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    (D.fuse i).part i = D.part i.castSucc ∪ D.part i.succ :=
  by simpa [fuse] using isFusionAt_fuse D i i

theorem fuse_part_of_lt {k : ℕ} (D : Division n (k + 2))
    {i j : Fin (k + 1)} (hji : j < i) :
    (D.fuse i).part j = D.part j.castSucc := by
  rw [isFusionAt_fuse D i j]
  simp [fusePart, ne_of_lt hji, hji]

theorem fuse_part_of_gt {k : ℕ} (D : Division n (k + 2))
    {i j : Fin (k + 1)} (hij : i < j) :
    (D.fuse i).part j = D.part j.succ := by
  rw [isFusionAt_fuse D i j]
  have hne : j ≠ i := ne_of_gt hij
  have hnlt : ¬ j < i := not_lt_of_ge (le_of_lt hij)
  simp [fusePart, hne, hnlt]

/-- The first element of a fused part is the first element of the left old
part. -/
theorem first_fuse_self {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    (D.fuse i).first i = D.first i.castSucc := by
  classical
  apply
    (Finset.min'_eq_iff ((D.fuse i).part i)
      ((D.fuse i).part_nonempty i) (D.first i.castSucc)).mpr
  constructor
  · rw [fuse_part_self]
    exact Finset.mem_union_left _ (D.first_mem i.castSucc)
  · intro x hx
    rw [fuse_part_self] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.min'_le _ _ hx
    · exact le_of_lt (D.part_ordered (by simp) (D.first_mem i.castSucc) hx)

/-- The last element of a fused part is the last element of the right old
part. -/
theorem last_fuse_self {k : ℕ} (D : Division n (k + 2))
    (i : Fin (k + 1)) :
    (D.fuse i).last i = D.last i.succ := by
  classical
  apply
    (Finset.max'_eq_iff ((D.fuse i).part i)
      ((D.fuse i).part_nonempty i) (D.last i.succ)).mpr
  constructor
  · rw [fuse_part_self]
    exact Finset.mem_union_right _ (D.last_mem i.succ)
  · intro x hx
    rw [fuse_part_self] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact le_of_lt (D.part_ordered (by simp) hx (D.last_mem i.succ))
    · exact Finset.le_max' _ _ hx

/-- The set of parts of a fused division is obtained by replacing the two
fused source parts by their union. -/
theorem parts_eq_insert_erase_of_isFusionAt {n k : ℕ}
    {D : Division n (k + 2)} {E : Division n (k + 1)} {i : Fin (k + 1)}
    (h : IsFusionAt D E i) :
    ((Finset.univ : Finset (Fin (k + 1))).map ⟨E.part, E.part_injective⟩) =
      insert (D.part i.castSucc ∪ D.part i.succ)
        ((((Finset.univ : Finset (Fin (k + 2))).map ⟨D.part, D.part_injective⟩).erase
          (D.part i.castSucc)).erase (D.part i.succ)) := by
  classical
  ext R
  constructor
  · intro hR
    rcases Finset.mem_map.mp hR with ⟨j, _hj, hjR⟩
    change E.part j = R at hjR
    rw [← hjR]
    by_cases hji : j = i
    · subst j
      exact Finset.mem_insert.mpr (Or.inl (by simp [h i, fusePart]))
    · rcases lt_or_gt_of_ne hji with hlt | hgt
      · have hpart : E.part j = D.part j.castSucc := by
          rw [h j]
          simp [fusePart, hji, hlt]
        rw [hpart]
        refine Finset.mem_insert.mpr (Or.inr ?_)
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro heq
          have hidx := D.part_injective heq
          have hv := congrArg Fin.val hidx
          simp at hv
          omega
        · refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · intro heq
            have hidx := D.part_injective heq
            have hv := congrArg Fin.val hidx
            simp at hv
            omega
          · exact Finset.mem_map.mpr ⟨j.castSucc, Finset.mem_univ _, rfl⟩
      · have hpart : E.part j = D.part j.succ := by
          rw [h j]
          have hnlt : ¬ j < i := not_lt_of_ge (le_of_lt hgt)
          simp [fusePart, hji, hnlt]
        rw [hpart]
        refine Finset.mem_insert.mpr (Or.inr ?_)
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro heq
          have hidx := D.part_injective heq
          have hv := congrArg Fin.val hidx
          simp at hv
          omega
        · refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · intro heq
            have hidx := D.part_injective heq
            have hv := congrArg Fin.val hidx
            simp at hv
            omega
          · exact Finset.mem_map.mpr ⟨j.succ, Finset.mem_univ _, rfl⟩
  · intro hR
    rcases Finset.mem_insert.mp hR with hR | hR
    · refine Finset.mem_map.mpr ⟨i, Finset.mem_univ _, ?_⟩
      change E.part i = R
      rw [h i]
      rw [hR]
      simp [fusePart]
    · rcases Finset.mem_erase.mp hR with ⟨hR_ne_succ, hR_old_erase⟩
      rcases Finset.mem_erase.mp hR_old_erase with ⟨hR_ne_cast, hR_old⟩
      rcases Finset.mem_map.mp hR_old with ⟨a, _ha, haR⟩
      change D.part a = R at haR
      by_cases hai : a.1 ≤ i.1
      · have hlt_ai : a.1 < i.1 := by
          have hne : a ≠ i.castSucc := by
            intro hae
            exact hR_ne_cast (by rw [← haR, hae])
          by_contra hnot
          have hge : i.1 ≤ a.1 := le_of_not_gt hnot
          have hval : a.1 = i.1 := le_antisymm hai hge
          apply hne
          ext
          simpa using hval
        let j : Fin (k + 1) := ⟨a.1, by omega⟩
        refine Finset.mem_map.mpr ⟨j, Finset.mem_univ _, ?_⟩
        change E.part j = R
        rw [h j]
        have hji : j < i := Fin.mk_lt_mk.mpr hlt_ai
        have hneji : j ≠ i := ne_of_lt hji
        simp [fusePart, hneji, hji]
        rw [← haR]
        congr
      · have hgt_i_a : i.1 + 1 < a.1 := by
          have hgt : i.1 < a.1 := lt_of_not_ge hai
          have hne : a ≠ i.succ := by
            intro hae
            exact hR_ne_succ (by rw [← haR, hae])
          by_contra hnot
          have hle : a.1 ≤ i.1 + 1 := le_of_not_gt hnot
          have hval : a.1 = i.1 + 1 := le_antisymm hle hgt
          apply hne
          ext
          simpa using hval
        let j : Fin (k + 1) := ⟨a.1 - 1, by omega⟩
        refine Finset.mem_map.mpr ⟨j, Finset.mem_univ _, ?_⟩
        change E.part j = R
        rw [h j]
        have hij : i < j := Fin.mk_lt_mk.mpr (by omega)
        have hneji : j ≠ i := ne_of_gt hij
        have hnlt : ¬ j < i := not_lt_of_ge (le_of_lt hij)
        simp [fusePart, hneji, hnlt]
        rw [← haR]
        congr
        ext
        dsimp [j]
        omega

end Division

end TwinWidth

/- ===== end Order/Divisions.lean ===== -/

/- ===== begin Matrix/Cell.lean ===== -/

/-
# Cells of divided matrices

Cells are the submatrices induced by a row division and a column division.  The
paper's mixed-minor notion says that a cell is mixed when it is neither vertical
nor horizontal.
-/

namespace TwinWidth
namespace Matrix

open TwinWidth

variable {α : Type*}

/-- A cell is vertical when each of its columns is constant on the row part. -/
def CellVertical {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R.part i → r₂ ∈ R.part i →
    ∀ ⦃c : Fin m⦄, c ∈ C.part j → M r₁ c = M r₂ c

/-- A cell is horizontal when each of its rows is constant on the column part. -/
def CellHorizontal {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R.part i →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C.part j → c₂ ∈ C.part j →
      M r c₁ = M r c₂

/-- A cell is mixed when it is neither vertical nor horizontal, matching
Section 5 of the first twin-width paper. -/
def CellMixed {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ¬ CellVertical M R C i j ∧ ¬ CellHorizontal M R C i j

theorem cellMixed_iff_not_vertical_and_not_horizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    CellMixed M R C i j ↔ ¬ CellVertical M R C i j ∧ ¬ CellHorizontal M R C i j :=
  Iff.rfl

end Matrix
end TwinWidth

/- ===== end Matrix/Cell.lean ===== -/

/- ===== begin Matrix/MixedMinor.lean ===== -/

/-
# Mixed minors of matrices

This file defines `HasMixedMinor`.  The `k = 0` convention is intentionally
vacuous: every matrix has a `0`-mixed minor, witnessed by the empty family of
cells.  Positive mixed minors require concrete row and column divisions.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

/-- A matrix has a `k`-mixed minor if it admits row and column
`k`-divisions whose every cell is mixed. -/
def HasMixedMinor {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (k : ℕ) : Prop :=
  k = 0 ∨
    ∃ R : Division n k, ∃ C : Division m k,
      ∀ i j : Fin k, CellMixed M R C i j

@[simp] theorem hasMixedMinor_zero {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) : HasMixedMinor M 0 :=
  Or.inl rfl

/-- A mixed minor cannot have order larger than either matrix dimension. -/
theorem hasMixedMinor_le_min_card {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (h : HasMixedMinor M k) : k ≤ min n m := by
  rcases h with rfl | h
  · exact Nat.zero_le _
  · rcases h with ⟨R, C, _⟩
    exact le_min (Division.card_parts_le R) (Division.card_parts_le C)

end Matrix
end TwinWidth

/- ===== end Matrix/MixedMinor.lean ===== -/

/- ===== begin Matrix/MixedNumber.lean ===== -/

/-
# Mixed number of a matrix

The mixed number is the largest `k ≤ min n m` for which the matrix has a
`k`-mixed minor.  The `k = 0` convention from `HasMixedMinor` ensures this
maximum is always defined.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

/-- The mixed number of a matrix: the largest order of a mixed minor,
searched up to the smaller matrix dimension. -/
noncomputable def matrixMixedNumber {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) : ℕ :=
  by
    classical
    exact Nat.findGreatest (HasMixedMinor M) (min n m)

theorem matrixMixedNumber_le_min_card {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) :
    matrixMixedNumber M ≤ min n m :=
  by
    classical
    exact Nat.findGreatest_le (P := HasMixedMinor M) (min n m)

theorem hasMixedMinor_matrixMixedNumber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) :
    HasMixedMinor M (matrixMixedNumber M) := by
  classical
  exact Nat.findGreatest_spec (P := HasMixedMinor M) (m := 0) (n := min n m)
    (Nat.zero_le _) (hasMixedMinor_zero M)

@[simp] theorem matrixMixedNumber_zero_rows {m : ℕ}
    (M : _root_.Matrix (Fin 0) (Fin m) α) :
    matrixMixedNumber M = 0 :=
  Nat.eq_zero_of_le_zero (by
    simpa using matrixMixedNumber_le_min_card M)

@[simp] theorem matrixMixedNumber_zero_cols {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin 0) α) :
    matrixMixedNumber M = 0 :=
  Nat.eq_zero_of_le_zero (by
    simpa using matrixMixedNumber_le_min_card M)

/-- The successor of the mixed number is mixed-free. -/
theorem not_hasMixedMinor_succ_matrixMixedNumber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) :
    ¬ HasMixedMinor M (matrixMixedNumber M + 1) := by
  classical
  by_cases hle : matrixMixedNumber M + 1 ≤ min n m
  · exact Nat.findGreatest_is_greatest
      (P := HasMixedMinor M)
      (hk := Nat.lt_succ_self (matrixMixedNumber M)) hle
  · intro h
    exact hle (hasMixedMinor_le_min_card h)

end Matrix
end TwinWidth

/- ===== end Matrix/MixedNumber.lean ===== -/

/- ===== begin Matrix/OrderedAdjacency.lean ===== -/

/-
# Ordered adjacency matrices

This file turns a finite graph together with an order equivalence into a Boolean
adjacency matrix indexed by `Fin n`.
-/

namespace TwinWidth

/-- An ordering of a finite vertex type by `Fin n`. -/
structure VertexOrder (V : Type*) (n : ℕ) where
  /-- The equivalence listing vertices by positions `0, ..., n - 1`. -/
  equiv : Fin n ≃ V

namespace Matrix

/-- The Boolean adjacency matrix of a graph in a chosen vertex order. -/
noncomputable def orderedAdjacency {V : Type*} {n : ℕ} (G : SimpleGraph V) (σ : VertexOrder V n) :
    _root_.Matrix (Fin n) (Fin n) Bool :=
  by
    classical
    exact fun i j => decide (G.Adj (σ.equiv i) (σ.equiv j))

/-- The mixed number of the ordered adjacency matrix of `G`. -/
noncomputable def orderedAdjacencyMixedNumber {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (σ : VertexOrder V n) : ℕ :=
  matrixMixedNumber (orderedAdjacency G σ)

end Matrix
end TwinWidth

/- ===== end Matrix/OrderedAdjacency.lean ===== -/

/- ===== begin Graph/MixedMinorNumber.lean ===== -/

/-
# Mixed minor number of finite simple graphs

The mixed minor number of a finite graph is the minimum, over all vertex
orderings, of the mixed number of the ordered adjacency matrix.
-/

namespace TwinWidth
namespace SimpleGraph

/-- There is always at least one vertex order of length `Fintype.card V`. -/
theorem exists_vertexOrder_card (V : Type*) [Fintype V] :
    Nonempty (VertexOrder V (Fintype.card V)) := by
  classical
  exact ⟨⟨(Fintype.equivFin V).symm⟩⟩

/-- There is always an ordered-adjacency mixed number realized by some order. -/
theorem exists_orderedAdjacencyMixedNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    ∃ k, ∃ σ : VertexOrder V (Fintype.card V),
      Matrix.orderedAdjacencyMixedNumber G σ = k := by
  classical
  let σ : VertexOrder V (Fintype.card V) := ⟨(Fintype.equivFin V).symm⟩
  exact ⟨Matrix.orderedAdjacencyMixedNumber G σ, σ, rfl⟩

/-- The mixed minor number graph parameter: the minimum mixed number of an
ordered adjacency matrix over all vertex orderings. -/
noncomputable def mixedMinorNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℕ :=
  by
    classical
    exact Nat.find (exists_orderedAdjacencyMixedNumber G)

/-- Some vertex ordering realizes the graph mixed minor number. -/
theorem exists_order_mixedNumber_eq_mixedMinorNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    ∃ σ : VertexOrder V (Fintype.card V),
      Matrix.orderedAdjacencyMixedNumber G σ = mixedMinorNumber G := by
  classical
  simpa [mixedMinorNumber] using Nat.find_spec (exists_orderedAdjacencyMixedNumber G)

/-- The graph mixed minor number is at most the mixed number of every ordered
adjacency matrix with the canonical cardinality-sized index type. -/
theorem mixedMinorNumber_le_orderedAdjacencyMixedNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (σ : VertexOrder V (Fintype.card V)) :
    mixedMinorNumber G ≤ Matrix.orderedAdjacencyMixedNumber G σ := by
  classical
  exact Nat.find_min' (exists_orderedAdjacencyMixedNumber G)
    ⟨σ, rfl⟩

theorem mixedMinorNumber_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    mixedMinorNumber G ≤ Fintype.card V := by
  classical
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  rw [← hσ]
  simpa [Matrix.orderedAdjacencyMixedNumber] using
    (Matrix.matrixMixedNumber_le_min_card (Matrix.orderedAdjacency G σ))

end SimpleGraph
end TwinWidth

/- ===== end Graph/MixedMinorNumber.lean ===== -/

/- ===== begin Equivalence/TwinWidthToMixed.lean ===== -/

/-
# Twin-width to mixed minor number

This module records the directional bound needed for functional equivalence.
The Section 5 proof of the first twin-width paper provides a linear witness;
with the formal diagonal and mirrored-fusion conventions used for simple graph
adjacency matrices the graph-facing witness is `fun d => 2 * (d + 3) + 2`.
-/

namespace TwinWidth
namespace SimpleGraph

/-- The proposition that mixed minor number is bounded by a numerical function
of twin-width. -/
def MixedMinorNumberBoundedByTwinWidth : Prop :=
  ∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
    mixedMinorNumber G ≤ f (twinWidth G)

/-- The linear bound predicted by the first item of the grid-minor theorem for
twin-width: a `d`-twin-ordered matrix is `(2*d+2)`-mixed-free. -/
def mixedMinorNumberBoundOfTwinWidth (d : ℕ) : ℕ :=
  2 * (d + 3) + 2

/-- Matrix-level ordered-adjacency form of the twin-width-to-mixed direction.

This is the exact interface supplied by Section 5's first item: for every graph,
there is a vertex order whose adjacency matrix has mixed number bounded by a
function of the graph twin-width.  Since `mixedMinorNumber` is the minimum over
orders, this immediately gives the graph-parameter direction below. -/
def OrderedAdjacencyMixedNumberBoundedByTwinWidth (f : ℕ → ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
    ∃ σ : VertexOrder V (Fintype.card V),
      Matrix.orderedAdjacencyMixedNumber G σ ≤ f (twinWidth G)

/-- Passing from a bounded ordered adjacency matrix to the graph mixed minor
number. -/
theorem mixedMinorNumber_le_of_orderedAdjacencyMixedNumber_le
    {V : Type} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {f : ℕ → ℕ}
    {σ : VertexOrder V (Fintype.card V)}
    (hσ : Matrix.orderedAdjacencyMixedNumber G σ ≤ f (twinWidth G)) :
    mixedMinorNumber G ≤ f (twinWidth G) :=
  le_trans (mixedMinorNumber_le_orderedAdjacencyMixedNumber G σ) hσ

/-- The graph-parameter direction follows from the ordered-adjacency matrix
bound. -/
theorem mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyBound
    {f : ℕ → ℕ}
    (h : OrderedAdjacencyMixedNumberBoundedByTwinWidth f) :
    MixedMinorNumberBoundedByTwinWidth := by
  refine ⟨f, ?_⟩
  intro V _ _ G
  rcases h G with ⟨σ, hσ⟩
  exact mixedMinorNumber_le_of_orderedAdjacencyMixedNumber_le (G := G) hσ

/-- The concrete one-direction statement with the project's graph-facing
conventions.  The `+3` accounts for the diagonal/self-zone convention and the
two one-sided child zones introduced by mirroring a graph contraction as row
then column fusions. -/
def OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth : Prop :=
  OrderedAdjacencyMixedNumberBoundedByTwinWidth mixedMinorNumberBoundOfTwinWidth

/-- One functional-equivalence direction with the explicit linear witness,
assuming the Section 5 ordered-adjacency bound. -/
theorem mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyLinearBound
    (h : OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth) :
    MixedMinorNumberBoundedByTwinWidth :=
  mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyBound h

/-- Legacy ordered-adjacency reduction: an ordered-adjacency linear bound
immediately gives the same graph-level bound, because `mixedMinorNumber` is the
minimum over vertex orders. -/
theorem mixed_minor_number_le_twice_twin_width_plus_four_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        ∃ σ : VertexOrder V (Fintype.card V),
          Matrix.orderedAdjacencyMixedNumber G σ ≤ 2 * (twinWidth G + 1) + 2) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      mixedMinorNumber G ≤ 2 * (twinWidth G + 1) + 2 := by
  intro V _ _ G
  rcases h G with ⟨σ, hσ⟩
  exact mixedMinorNumber_le_of_orderedAdjacencyMixedNumber_le
    (G := G) (f := fun d => 2 * (d + 1) + 2) hσ

end SimpleGraph
end TwinWidth

/- ===== end Equivalence/TwinWidthToMixed.lean ===== -/

/- ===== begin Graph/Partition.lean ===== -/

/-
# Graph partitions and trigraph states

This file builds the graph-side partition language used by Theorem 14.  A
partition of the original vertex set determines a trigraph state: black edges
join complete homogeneous pairs of parts, red edges join non-homogeneous pairs
of parts, and empty homogeneous pairs carry neither color.
-/

namespace TwinWidth
namespace SimpleGraph

/-- A finite family of bags is a partition of `V`. -/
def IsBagPartition {V : Type*} (bags : Finset (Finset V)) : Prop :=
  (∀ ⦃A⦄, A ∈ bags → A.Nonempty) ∧
    (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → A ≠ B → Disjoint A B) ∧
      ∀ v : V, ∃ A ∈ bags, v ∈ A

theorem singletonBags_isBagPartition (V : Type*) [Fintype V] [DecidableEq V] :
    IsBagPartition (TrigraphState.singletonBags V) := by
  classical
  constructor
  · intro A hA
    rcases Finset.mem_image.mp hA with ⟨v, _hv, rfl⟩
    exact ⟨v, by simp⟩
  constructor
  · intro A B hA hB hAB
    rcases Finset.mem_image.mp hA with ⟨a, _ha, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨b, _hb, rfl⟩
    rw [Finset.disjoint_singleton]
    intro hba
    apply hAB
    ext x
    simp [hba]
  · intro v
    refine ⟨{v}, ?_, by simp⟩
    exact Finset.mem_image.mpr ⟨v, by simp, rfl⟩

theorem IsBagPartition.card_le_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    {bags : Finset (Finset V)} (hbags : IsBagPartition bags) :
    bags.card ≤ Fintype.card V := by
  classical
  let pick : {A : Finset V // A ∈ bags} → V :=
    fun A => Classical.choose (hbags.1 A.2)
  have hpick : ∀ A : {A : Finset V // A ∈ bags}, pick A ∈ A.1 := by
    intro A
    exact Classical.choose_spec (hbags.1 A.2)
  have hinj : Function.Injective pick := by
    intro A B hp
    by_contra hAB
    have hABval : A.1 ≠ B.1 := by
      intro hval
      exact hAB (Subtype.ext hval)
    have hpA : pick A ∈ A.1 := hpick A
    have hpB : pick A ∈ B.1 := by simpa [hp] using hpick B
    exact (Finset.disjoint_left.mp (hbags.2.1 A.2 B.2 hABval)) hpA hpB
  calc
    bags.card = Fintype.card {A : Finset V // A ∈ bags} := by simp
    _ ≤ Fintype.card V := Fintype.card_le_of_injective pick hinj

theorem IsBagPartition.card_pos_of_nonempty_type
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {bags : Finset (Finset V)} (hbags : IsBagPartition bags) :
    0 < bags.card := by
  classical
  rcases ‹Nonempty V› with ⟨v⟩
  rcases hbags.2.2 v with ⟨A, hA, _hvA⟩
  exact Finset.card_pos.mpr ⟨A, hA⟩

/-- Every trigraph state carries a bag partition. -/
theorem TrigraphState.isBagPartition {V : Type*} (T : TrigraphState V) :
    IsBagPartition T.bags :=
  ⟨T.bag_nonempty, T.bag_disjoint, T.bag_cover⟩

/-- Every pair in `A × B` is an edge of `G`. -/
def CompleteBetween {V : Type*} (G : _root_.SimpleGraph V)
    (A B : Finset V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → G.Adj a b

/-- No pair in `A × B` is an edge of `G`. -/
def EmptyBetween {V : Type*} (G : _root_.SimpleGraph V)
    (A B : Finset V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ¬ G.Adj a b

/-- Two bags are homogeneous when the bipartite zone between them is complete
or empty. -/
def HomogeneousBetween {V : Type*} (G : _root_.SimpleGraph V)
    (A B : Finset V) : Prop :=
  CompleteBetween G A B ∨ EmptyBetween G A B

/-- Graph partition red adjacency: distinct bags whose bipartite zone is not
homogeneous. -/
def partitionRedAdj {V : Type*} (G : _root_.SimpleGraph V)
    (A B : Finset V) : Prop :=
  A ≠ B ∧ ¬ HomogeneousBetween G A B

/-- Graph partition black adjacency: distinct bags whose bipartite zone is
complete.  Empty homogeneous pairs are left uncolored. -/
def partitionBlackAdj {V : Type*} (G : _root_.SimpleGraph V)
    (A B : Finset V) : Prop :=
  A ≠ B ∧ CompleteBetween G A B

theorem completeBetween_symm {V : Type*} {G : _root_.SimpleGraph V}
    {A B : Finset V} (h : CompleteBetween G A B) :
    CompleteBetween G B A := by
  intro b a hb ha
  exact G.symm (h ha hb)

theorem emptyBetween_symm {V : Type*} {G : _root_.SimpleGraph V}
    {A B : Finset V} (h : EmptyBetween G A B) :
    EmptyBetween G B A := by
  intro b a hb ha
  exact fun hba => h ha hb (G.symm hba)

theorem homogeneousBetween_symm {V : Type*} {G : _root_.SimpleGraph V}
    {A B : Finset V} (h : HomogeneousBetween G A B) :
    HomogeneousBetween G B A := by
  rcases h with h | h
  · exact Or.inl (completeBetween_symm h)
  · exact Or.inr (emptyBetween_symm h)

theorem partitionRedAdj_symm {V : Type*} {G : _root_.SimpleGraph V}
    {A B : Finset V} (h : partitionRedAdj G A B) :
    partitionRedAdj G B A := by
  exact ⟨h.1.symm, fun hhom => h.2 (homogeneousBetween_symm hhom)⟩

theorem partitionBlackAdj_symm {V : Type*} {G : _root_.SimpleGraph V}
    {A B : Finset V} (h : partitionBlackAdj G A B) :
    partitionBlackAdj G B A := by
  exact ⟨h.1.symm, completeBetween_symm h.2⟩

theorem completeBetween_union_left_iff {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V} :
    CompleteBetween G (A ∪ B) C ↔
      CompleteBetween G A C ∧ CompleteBetween G B C := by
  constructor
  · intro h
    constructor
    · intro a c ha hc
      exact h (by simp [ha]) hc
    · intro b c hb hc
      exact h (by simp [hb]) hc
  · rintro ⟨hA, hB⟩ x c hx hc
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hA hx hc
    · exact hB hx hc

theorem completeBetween_union_right_iff {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V} :
    CompleteBetween G A (B ∪ C) ↔
      CompleteBetween G A B ∧ CompleteBetween G A C := by
  constructor
  · intro h
    constructor
    · intro a b ha hb
      exact h ha (by simp [hb])
    · intro a c ha hc
      exact h ha (by simp [hc])
  · rintro ⟨hB, hC⟩ a x ha hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hB ha hx
    · exact hC ha hx

theorem emptyBetween_union_left_iff {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V} :
    EmptyBetween G (A ∪ B) C ↔
      EmptyBetween G A C ∧ EmptyBetween G B C := by
  constructor
  · intro h
    constructor
    · intro a c ha hc
      exact h (by simp [ha]) hc
    · intro b c hb hc
      exact h (by simp [hb]) hc
  · rintro ⟨hA, hB⟩ x c hx hc
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hA hx hc
    · exact hB hx hc

theorem emptyBetween_union_right_iff {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V} :
    EmptyBetween G A (B ∪ C) ↔
      EmptyBetween G A B ∧ EmptyBetween G A C := by
  constructor
  · intro h
    constructor
    · intro a b ha hb
      exact h ha (by simp [hb])
    · intro a c ha hc
      exact h ha (by simp [hc])
  · rintro ⟨hB, hC⟩ a x ha hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hB ha hx
    · exact hC ha hx

theorem emptyBetween_of_homogeneous_not_complete {V : Type*}
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (hhom : HomogeneousBetween G A B) (hnot : ¬ CompleteBetween G A B) :
    EmptyBetween G A B := by
  rcases hhom with hcomp | hemp
  · exact (hnot hcomp).elim
  · exact hemp

theorem not_completeBetween_of_emptyBetween {V : Type*}
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hemp : EmptyBetween G A B) :
    ¬ CompleteBetween G A B := by
  intro hcomp
  rcases hA with ⟨a, ha⟩
  rcases hB with ⟨b, hb⟩
  exact hemp ha hb (hcomp ha hb)

theorem homogeneousBetween_union_left_of_same_color {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (hA : HomogeneousBetween G A C) (hB : HomogeneousBetween G B C)
    (hsame : CompleteBetween G A C ↔ CompleteBetween G B C) :
    HomogeneousBetween G (A ∪ B) C := by
  by_cases hcompA : CompleteBetween G A C
  · have hcompB : CompleteBetween G B C := hsame.mp hcompA
    exact Or.inl (completeBetween_union_left_iff.mpr ⟨hcompA, hcompB⟩)
  · have hcompB : ¬ CompleteBetween G B C := fun h => hcompA (hsame.mpr h)
    exact Or.inr (emptyBetween_union_left_iff.mpr
      ⟨emptyBetween_of_homogeneous_not_complete hA hcompA,
        emptyBetween_of_homogeneous_not_complete hB hcompB⟩)

theorem homogeneousBetween_left_of_homogeneous_union_left {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (h : HomogeneousBetween G (A ∪ B) C) :
    HomogeneousBetween G A C := by
  rcases h with hcomp | hemp
  · exact Or.inl (completeBetween_union_left_iff.mp hcomp).1
  · exact Or.inr (emptyBetween_union_left_iff.mp hemp).1

theorem homogeneousBetween_right_of_homogeneous_union_left {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (h : HomogeneousBetween G (A ∪ B) C) :
    HomogeneousBetween G B C := by
  rcases h with hcomp | hemp
  · exact Or.inl (completeBetween_union_left_iff.mp hcomp).2
  · exact Or.inr (emptyBetween_union_left_iff.mp hemp).2

theorem homogeneousBetween_union_right_of_same_color {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (hA : HomogeneousBetween G C A) (hB : HomogeneousBetween G C B)
    (hsame : CompleteBetween G C A ↔ CompleteBetween G C B) :
    HomogeneousBetween G C (A ∪ B) := by
  by_cases hcompA : CompleteBetween G C A
  · have hcompB : CompleteBetween G C B := hsame.mp hcompA
    exact Or.inl (completeBetween_union_right_iff.mpr ⟨hcompA, hcompB⟩)
  · have hcompB : ¬ CompleteBetween G C B := fun h => hcompA (hsame.mpr h)
    exact Or.inr (emptyBetween_union_right_iff.mpr
      ⟨emptyBetween_of_homogeneous_not_complete hA hcompA,
        emptyBetween_of_homogeneous_not_complete hB hcompB⟩)

theorem homogeneousBetween_left_of_homogeneous_union_right {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (h : HomogeneousBetween G C (A ∪ B)) :
    HomogeneousBetween G C A := by
  rcases h with hcomp | hemp
  · exact Or.inl (completeBetween_union_right_iff.mp hcomp).1
  · exact Or.inr (emptyBetween_union_right_iff.mp hemp).1

theorem homogeneousBetween_right_of_homogeneous_union_right {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (h : HomogeneousBetween G C (A ∪ B)) :
    HomogeneousBetween G C B := by
  rcases h with hcomp | hemp
  · exact Or.inl (completeBetween_union_right_iff.mp hcomp).2
  · exact Or.inr (emptyBetween_union_right_iff.mp hemp).2

theorem partitionRedAdj_union_left_iff {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hAC : A ≠ C) (hBC : B ≠ C) (hUC : A ∪ B ≠ C) :
    partitionRedAdj G (A ∪ B) C ↔
      partitionRedAdj G A C ∨ partitionRedAdj G B C ∨
        partitionBlackAdj G A C ≠ partitionBlackAdj G B C := by
  constructor
  · intro hred
    by_cases hhomA : HomogeneousBetween G A C
    · by_cases hhomB : HomogeneousBetween G B C
      · right
        right
        intro heq
        have hsameBlack :
            partitionBlackAdj G A C ↔ partitionBlackAdj G B C := by
          rw [heq]
        have hsameComplete :
            CompleteBetween G A C ↔ CompleteBetween G B C := by
          constructor
          · intro hcompA
            exact (hsameBlack.mp ⟨hAC, hcompA⟩).2
          · intro hcompB
            exact (hsameBlack.mpr ⟨hBC, hcompB⟩).2
        exact hred.2
          (homogeneousBetween_union_left_of_same_color hhomA hhomB hsameComplete)
      · exact Or.inr (Or.inl ⟨hBC, hhomB⟩)
    · exact Or.inl ⟨hAC, hhomA⟩
  · intro h
    refine ⟨hUC, ?_⟩
    intro hhomU
    rcases h with hredA | hredB | hblackNe
    · exact hredA.2 (homogeneousBetween_left_of_homogeneous_union_left hhomU)
    · exact hredB.2 (homogeneousBetween_right_of_homogeneous_union_left hhomU)
    · apply hblackNe
      apply propext
      rcases hhomU with hcompU | hempU
      · have hparts := completeBetween_union_left_iff.mp hcompU
        constructor
        · intro _; exact ⟨hBC, hparts.2⟩
        · intro _; exact ⟨hAC, hparts.1⟩
      · have hparts := emptyBetween_union_left_iff.mp hempU
        have hncompA : ¬ CompleteBetween G A C :=
          not_completeBetween_of_emptyBetween hA hC hparts.1
        have hncompB : ¬ CompleteBetween G B C :=
          not_completeBetween_of_emptyBetween hB hC hparts.2
        constructor
        · intro hblackA
          exact (hncompA hblackA.2).elim
        · intro hblackB
          exact (hncompB hblackB.2).elim

theorem partitionBlackAdj_union_left_iff {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hAC : A ≠ C) (hBC : B ≠ C) (hUC : A ∪ B ≠ C) :
    partitionBlackAdj G (A ∪ B) C ↔
      partitionBlackAdj G A C ∧ partitionBlackAdj G B C ∧
        ¬ (partitionRedAdj G A C ∨ partitionRedAdj G B C ∨
          partitionBlackAdj G A C ≠ partitionBlackAdj G B C) := by
  constructor
  · intro hblack
    have hparts := completeBetween_union_left_iff.mp hblack.2
    refine ⟨⟨hAC, hparts.1⟩, ⟨hBC, hparts.2⟩, ?_⟩
    intro hred
    have hredUnion : partitionRedAdj G (A ∪ B) C :=
      (partitionRedAdj_union_left_iff hA hB hC hAC hBC hUC).mpr hred
    exact hredUnion.2 (Or.inl hblack.2)
  · rintro ⟨hblackA, hblackB, hnotRed⟩
    refine ⟨hUC, ?_⟩
    exact completeBetween_union_left_iff.mpr ⟨hblackA.2, hblackB.2⟩

theorem partitionRedAdj_union_right_iff {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hCA : C ≠ A) (hCB : C ≠ B) (hCU : C ≠ A ∪ B) :
    partitionRedAdj G C (A ∪ B) ↔
      partitionRedAdj G C A ∨ partitionRedAdj G C B ∨
        partitionBlackAdj G C A ≠ partitionBlackAdj G C B := by
  constructor
  · intro hred
    by_cases hhomA : HomogeneousBetween G C A
    · by_cases hhomB : HomogeneousBetween G C B
      · right
        right
        intro heq
        have hsameBlack :
            partitionBlackAdj G C A ↔ partitionBlackAdj G C B := by
          rw [heq]
        have hsameComplete :
            CompleteBetween G C A ↔ CompleteBetween G C B := by
          constructor
          · intro hcompA
            exact (hsameBlack.mp ⟨hCA, hcompA⟩).2
          · intro hcompB
            exact (hsameBlack.mpr ⟨hCB, hcompB⟩).2
        exact hred.2
          (homogeneousBetween_union_right_of_same_color hhomA hhomB hsameComplete)
      · exact Or.inr (Or.inl ⟨hCB, hhomB⟩)
    · exact Or.inl ⟨hCA, hhomA⟩
  · intro h
    refine ⟨hCU, ?_⟩
    intro hhomU
    rcases h with hredA | hredB | hblackNe
    · exact hredA.2 (homogeneousBetween_left_of_homogeneous_union_right hhomU)
    · exact hredB.2 (homogeneousBetween_right_of_homogeneous_union_right hhomU)
    · apply hblackNe
      apply propext
      rcases hhomU with hcompU | hempU
      · have hparts := completeBetween_union_right_iff.mp hcompU
        constructor
        · intro _; exact ⟨hCB, hparts.2⟩
        · intro _; exact ⟨hCA, hparts.1⟩
      · have hparts := emptyBetween_union_right_iff.mp hempU
        have hncompA : ¬ CompleteBetween G C A :=
          not_completeBetween_of_emptyBetween hC hA hparts.1
        have hncompB : ¬ CompleteBetween G C B :=
          not_completeBetween_of_emptyBetween hC hB hparts.2
        constructor
        · intro hblackA
          exact (hncompA hblackA.2).elim
        · intro hblackB
          exact (hncompB hblackB.2).elim

theorem partitionBlackAdj_union_right_iff {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B C : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hCA : C ≠ A) (hCB : C ≠ B) (hCU : C ≠ A ∪ B) :
    partitionBlackAdj G C (A ∪ B) ↔
      partitionBlackAdj G C A ∧ partitionBlackAdj G C B ∧
        ¬ (partitionRedAdj G C A ∨ partitionRedAdj G C B ∨
          partitionBlackAdj G C A ≠ partitionBlackAdj G C B) := by
  constructor
  · intro hblack
    have hparts := completeBetween_union_right_iff.mp hblack.2
    refine ⟨⟨hCA, hparts.1⟩, ⟨hCB, hparts.2⟩, ?_⟩
    intro hred
    have hredUnion : partitionRedAdj G C (A ∪ B) :=
      (partitionRedAdj_union_right_iff hA hB hC hCA hCB hCU).mpr hred
    exact hredUnion.2 (Or.inl hblack.2)
  · rintro ⟨hblackA, hblackB, _hnotRed⟩
    refine ⟨hCU, ?_⟩
    exact completeBetween_union_right_iff.mpr ⟨hblackA.2, hblackB.2⟩

theorem partitionBlackAdj_singletonBags_iff {V : Type*}
    [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B : Finset V}
    (hA : A ∈ TrigraphState.singletonBags V)
    (hB : B ∈ TrigraphState.singletonBags V) :
    partitionBlackAdj G A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
  classical
  rcases Finset.mem_image.mp hA with ⟨a, _ha, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨b, _hb, rfl⟩
  constructor
  · intro hblack
    exact ⟨a, by simp, b, by simp, hblack.2 (by simp) (by simp)⟩
  · rintro ⟨a', ha', b', hb', hadj⟩
    have ha_eq : a' = a := by simpa using ha'
    have hb_eq : b' = b := by simpa using hb'
    subst a'
    subst b'
    constructor
    · intro hsingle
      apply G.loopless.irrefl a
      have hab : a = b := Finset.singleton_inj.mp hsingle
      subst b
      exact hadj
    · intro x y hx hy
      have hx_eq : x = a := by simpa using hx
      have hy_eq : y = b := by simpa using hy
      subst x
      subst y
      exact hadj

theorem not_partitionRedAdj_singletonBags {V : Type*}
    [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B : Finset V}
    (hA : A ∈ TrigraphState.singletonBags V)
    (hB : B ∈ TrigraphState.singletonBags V) :
    ¬ partitionRedAdj G A B := by
  classical
  rcases Finset.mem_image.mp hA with ⟨a, _ha, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨b, _hb, rfl⟩
  intro hred
  apply hred.2
  by_cases hab : a = b
  · subst b
    exact Or.inr (by
      intro x y hx hy hxy
      have hx_eq : x = a := by simpa using hx
      have hy_eq : y = a := by simpa using hy
      subst x
      subst y
      exact G.loopless.irrefl a hxy)
  · by_cases hadj : G.Adj a b
    · exact Or.inl (by
        intro x y hx hy
        have hx_eq : x = a := by simpa using hx
        have hy_eq : y = b := by simpa using hy
        subst x
        subst y
        exact hadj)
    · exact Or.inr (by
        intro x y hx hy hxy
        have hx_eq : x = a := by simpa using hx
        have hy_eq : y = b := by simpa using hy
        subst x
        subst y
        exact hadj hxy)

/-- The trigraph state represented by a graph partition. -/
def trigraphStateOfPartition {V : Type*}
    (G : _root_.SimpleGraph V)
    (bags : Finset (Finset V)) (hbags : IsBagPartition bags) :
    TrigraphState V where
  bags := bags
  bag_nonempty := hbags.1
  bag_disjoint := hbags.2.1
  bag_cover := hbags.2.2
  blackAdj := partitionBlackAdj G
  redAdj := partitionRedAdj G
  black_symm := by
    intro A B _ _ h
    exact partitionBlackAdj_symm h
  red_symm := by
    intro A B _ _ h
    exact partitionRedAdj_symm h
  black_irrefl := by
    intro A _ h
    exact h.1 rfl
  red_irrefl := by
    intro A _ h
    exact h.1 rfl
  black_red_disjoint := by
    intro A B _ _ hblack hred
    exact hred.2 (Or.inl hblack.2)

theorem trigraphStateOfPartition_singletonBags_initial {V : Type*}
    [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    IsInitialState G
      (trigraphStateOfPartition G (TrigraphState.singletonBags V)
        (singletonBags_isBagPartition V)) := by
  classical
  refine ⟨rfl, ?_, ?_⟩
  · intro A B hA hB
    change partitionBlackAdj G A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b
    exact partitionBlackAdj_singletonBags_iff hA hB
  · intro A B hA hB
    change ¬ partitionRedAdj G A B
    exact not_partitionRedAdj_singletonBags hA hB

/-- A trigraph state is the semantic state induced by its bag partition in
the original graph: black pairs are complete pairs and red pairs are exactly
the non-homogeneous pairs. -/
def IsSemanticState {V : Type*} (G : _root_.SimpleGraph V)
    (T : TrigraphState V) : Prop :=
  (∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags →
    (T.redAdj A B ↔ partitionRedAdj G A B)) ∧
    ∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags →
      (T.blackAdj A B ↔ partitionBlackAdj G A B)

theorem trigraphStateOfPartition_isSemanticState {V : Type*}
    {G : _root_.SimpleGraph V} {bags : Finset (Finset V)}
    (hbags : IsBagPartition bags) :
    IsSemanticState G (trigraphStateOfPartition G bags hbags) := by
  constructor <;> intro A B hA hB <;> rfl

theorem isInitialState_isSemanticState {V : Type*}
    [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {T : TrigraphState V} (hT : IsInitialState G T) :
    IsSemanticState G T := by
  classical
  rcases hT with ⟨hbags, hblack, hred⟩
  constructor
  · intro A B hA hB
    have hA' : A ∈ TrigraphState.singletonBags V := by simpa [hbags] using hA
    have hB' : B ∈ TrigraphState.singletonBags V := by simpa [hbags] using hB
    constructor
    · intro h
      exact (hred hA hB h).elim
    · intro h
      exact (not_partitionRedAdj_singletonBags hA' hB' h).elim
  · intro A B hA hB
    have hA' : A ∈ TrigraphState.singletonBags V := by simpa [hbags] using hA
    have hB' : B ∈ TrigraphState.singletonBags V := by simpa [hbags] using hB
    rw [hblack hA hB]
    exact (partitionBlackAdj_singletonBags_iff hA' hB').symm

/-- A graph partition has red degree at most `d` when every part has at most
`d` non-homogeneous partners. -/
noncomputable def PartitionRedDegreeAtMost {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (bags : Finset (Finset V)) (d : ℕ) : Prop :=
  by
    classical
    exact ∀ ⦃A⦄, A ∈ bags →
      (bags.filter fun B => partitionRedAdj G A B).card ≤ d

/-- Any bag partition has red degree at most the number of vertices.  This is
the finite fallback used for construction/existence arguments; sharper bounds
come from matrix or contraction hypotheses. -/
theorem partitionRedDegreeAtMost_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {bags : Finset (Finset V)}
    (hbags : IsBagPartition bags) :
    PartitionRedDegreeAtMost G bags (Fintype.card V) := by
  classical
  intro A _hA
  calc
    (bags.filter fun B => partitionRedAdj G A B).card ≤ bags.card :=
      Finset.card_filter_le _ _
    _ ≤ Fintype.card V := hbags.card_le_univ

/-- A contraction of a bag family merges two distinct bags. -/
def IsBagContraction {V : Type*} [DecidableEq V]
    (P Q : Finset (Finset V)) : Prop :=
  ∃ A ∈ P, ∃ B ∈ P, A ≠ B ∧
    Q = insert (A ∪ B) ((P.erase A).erase B)

/-- A semantic trigraph contraction induces the corresponding contraction of
its bag family. -/
theorem IsContractionStep.isBagContraction {V : Type*} [DecidableEq V]
    {T U : TrigraphState V} (h : IsContractionStep T U) :
    IsBagContraction T.bags U.bags := by
  rcases h with ⟨A, hA, B, hB, hAB, hbags, _hred, _hblack⟩
  exact ⟨A, hA, B, hB, hAB, hbags⟩

/-- Reverse one bag contraction in an ordered list of bags: the merged bag
`A ∪ B` is replaced by the adjacent pair `A, B`; all other bags keep their
relative order. -/
def splitMergedBag {V : Type*} [DecidableEq V]
    (A B : Finset V) (L : List (Finset V)) : List (Finset V) :=
  L.flatMap fun X => if X = A ∪ B then [A, B] else [X]

theorem mem_splitMergedBag {V : Type*} [DecidableEq V]
    {A B X : Finset V} {L : List (Finset V)} :
    X ∈ splitMergedBag A B L ↔
      (A ∪ B ∈ L ∧ (X = A ∨ X = B)) ∨ (X ∈ L ∧ X ≠ A ∪ B) := by
  classical
  constructor
  · intro hX
    rw [splitMergedBag, List.mem_flatMap] at hX
    rcases hX with ⟨Y, hYL, hXY⟩
    by_cases hY : Y = A ∪ B
    · subst Y
      simp at hXY
      exact Or.inl ⟨hYL, hXY⟩
    · simp [hY] at hXY
      subst X
      exact Or.inr ⟨hYL, hY⟩
  · rintro (⟨hML, hXAB⟩ | ⟨hXL, hXne⟩)
    · rw [splitMergedBag, List.mem_flatMap]
      refine ⟨A ∪ B, hML, ?_⟩
      rcases hXAB with hXA | hXB
      · simp [hXA]
      · simp [hXB]
    · rw [splitMergedBag, List.mem_flatMap]
      refine ⟨X, hXL, ?_⟩
      simp [hXne]

/-- If the merged bag occurs nowhere in a list, reversing a contraction does
not change that list. -/
theorem splitMergedBag_eq_self_of_notMem {V : Type*} [DecidableEq V]
    {A B : Finset V} {L : List (Finset V)}
    (hM : A ∪ B ∉ L) :
    splitMergedBag A B L = L := by
  classical
  induction L with
  | nil =>
      simp [splitMergedBag]
  | cons X L ih =>
      have hX : X ≠ A ∪ B := by
        intro h
        exact hM (by simp [h])
      have hL : A ∪ B ∉ L := by
        intro h
        exact hM (by simp [h])
      change (if X = A ∪ B then [A, B] else [X]) ++
          splitMergedBag A B L = X :: L
      rw [if_neg hX, ih hL]
      simp

/-- With a unique occurrence of the merged bag, `splitMergedBag` replaces that
occurrence by the adjacent pair of child bags and leaves the prefix and suffix
unchanged. -/
theorem splitMergedBag_eq_append_of_eq_append
    {V : Type*} [DecidableEq V]
    {A B : Finset V} {L P Q : List (Finset V)}
    (hL : L = P ++ [A ∪ B] ++ Q)
    (hP : A ∪ B ∉ P) (hQ : A ∪ B ∉ Q) :
    splitMergedBag A B L = P ++ [A, B] ++ Q := by
  classical
  subst L
  have hPsplit : splitMergedBag A B P = P :=
    splitMergedBag_eq_self_of_notMem hP
  have hQsplit : splitMergedBag A B Q = Q :=
    splitMergedBag_eq_self_of_notMem hQ
  have hPflat :
      List.flatMap (fun X => if X = A ∪ B then [A, B] else [X]) P = P := by
    simpa [splitMergedBag] using hPsplit
  have hQflat :
      List.flatMap (fun X => if X = A ∪ B then [A, B] else [X]) Q = Q := by
    simpa [splitMergedBag] using hQsplit
  unfold splitMergedBag
  rw [List.flatMap_append, List.flatMap_append, hPflat, hQflat]
  simp

/-- A nodup list containing the merged bag can be decomposed around its unique
merged entry, and `splitMergedBag` replaces exactly that entry by the two
children. -/
theorem exists_splitMergedBag_eq_append_of_mem_nodup
    {V : Type*} [DecidableEq V]
    {A B : Finset V} {L : List (Finset V)}
    (hLnodup : L.Nodup) (hM : A ∪ B ∈ L) :
    ∃ P Q : List (Finset V),
      L = P ++ [A ∪ B] ++ Q ∧
        A ∪ B ∉ P ∧ A ∪ B ∉ Q ∧
          splitMergedBag A B L = P ++ [A, B] ++ Q := by
  classical
  rw [List.mem_iff_append] at hM
  rcases hM with ⟨P, Q, hL⟩
  have hnodup : (P ++ [A ∪ B] ++ Q).Nodup := by
    simpa [hL] using hLnodup
  have hnotP : A ∪ B ∉ P := by
    intro hP
    have hnodupP : (P ++ ([A ∪ B] ++ Q)).Nodup := by
      simpa [List.append_assoc] using hnodup
    have hdis := (List.nodup_append'.mp hnodupP).2.2
    exact hdis hP (by simp : A ∪ B ∈ [A ∪ B] ++ Q)
  have hnotQ : A ∪ B ∉ Q := by
    intro hQ
    have hnodup' : ((P ++ [A ∪ B]) ++ Q).Nodup := by
      simpa [List.append_assoc] using hnodup
    have hdis := (List.nodup_append'.mp hnodup').2.2
    exact hdis (by simp : A ∪ B ∈ P ++ [A ∪ B]) hQ
  have hL' : L = P ++ [A ∪ B] ++ Q := by
    simpa using hL
  exact ⟨P, Q, hL', hnotP, hnotQ,
    splitMergedBag_eq_append_of_eq_append hL' hnotP hnotQ⟩

theorem mem_merge_family_iff {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} {A B X : Finset V} :
    X ∈ insert (A ∪ B) ((P.erase A).erase B) ↔
      X = A ∪ B ∨ (X ∈ P ∧ X ≠ A ∧ X ≠ B) := by
  constructor
  · intro hX
    rcases Finset.mem_insert.mp hX with hmerge | hrest
    · exact Or.inl hmerge
    · right
      have hdata : X ≠ B ∧ X ≠ A ∧ X ∈ P := by
        simpa using hrest
      exact ⟨hdata.2.2, hdata.2.1, hdata.1⟩
  · rintro (rfl | ⟨hP, hneA, hneB⟩)
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert.mpr (Or.inr <| by
        simp [hneA, hneB, hP])

/-- Merging two distinct bags of a bag partition again gives a bag partition. -/
theorem isBagPartition_merge {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} (hP : IsBagPartition P)
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) (_hAB : A ≠ B) :
    IsBagPartition (insert (A ∪ B) ((P.erase A).erase B)) := by
  classical
  constructor
  · intro X hX
    rcases mem_merge_family_iff.mp hX with rfl | ⟨hXP, _hXA, _hXB⟩
    · exact (hP.1 hA).mono (by intro x hx; exact Finset.mem_union_left _ hx)
    · exact hP.1 hXP
  constructor
  · intro X Y hX hY hXY
    rw [Finset.disjoint_left]
    have hXclass := mem_merge_family_iff.mp hX
    have hYclass := mem_merge_family_iff.mp hY
    intro x hx hy
    rcases hXclass with rfl | ⟨hXP, hXA, hXB⟩
    · rcases hYclass with hYmerge | ⟨hYP, hYA, hYB⟩
      · exact hXY hYmerge.symm
      · rcases Finset.mem_union.mp hx with hxA | hxB
        · exact Finset.disjoint_left.mp (hP.2.1 hA hYP hYA.symm) hxA hy
        · exact Finset.disjoint_left.mp (hP.2.1 hB hYP hYB.symm) hxB hy
    · rcases hYclass with rfl | ⟨hYP, _hYA, _hYB⟩
      · rcases Finset.mem_union.mp hy with hyA | hyB
        · exact Finset.disjoint_left.mp (hP.2.1 hXP hA hXA) hx hyA
        · exact Finset.disjoint_left.mp (hP.2.1 hXP hB hXB) hx hyB
      · exact Finset.disjoint_left.mp (hP.2.1 hXP hYP hXY) hx hy
  · intro v
    rcases hP.2.2 v with ⟨X, hX, hvX⟩
    by_cases hXA : X = A
    · refine ⟨A ∪ B, Finset.mem_insert_self _ _, ?_⟩
      subst X
      exact Finset.mem_union_left _ hvX
    · by_cases hXB : X = B
      · refine ⟨A ∪ B, Finset.mem_insert_self _ _, ?_⟩
        subst X
        exact Finset.mem_union_right _ hvX
      · refine ⟨X, ?_, hvX⟩
        exact mem_merge_family_iff.mpr (Or.inr ⟨hX, hXA, hXB⟩)

theorem union_ne_bag_of_disjoint_left {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} (hP : IsBagPartition P)
    {A B Y : Finset V} (hA : A ∈ P) (hY : Y ∈ P) (hAY : A ≠ Y) :
    A ∪ B ≠ Y := by
  intro h
  rcases hP.1 hA with ⟨a, ha⟩
  have hay : a ∈ Y := by
    rw [← h]
    exact Finset.mem_union_left _ ha
  exact (Finset.disjoint_left.mp (hP.2.1 hA hY hAY)) ha hay

theorem union_ne_bag_of_disjoint_right {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} (hP : IsBagPartition P)
    {A B Y : Finset V} (hB : B ∈ P) (hY : Y ∈ P) (hBY : B ≠ Y) :
    A ∪ B ≠ Y := by
  rw [Finset.union_comm]
  exact union_ne_bag_of_disjoint_left hP hB hY hBY

theorem splitMergedBag_toFinset_of_merge
    {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} (hP : IsBagPartition P)
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B)
    {L : List (Finset V)}
    (hL : L.toFinset = insert (A ∪ B) ((P.erase A).erase B)) :
    (splitMergedBag A B L).toFinset = P := by
  classical
  ext X
  rw [List.mem_toFinset, mem_splitMergedBag]
  constructor
  · rintro (⟨_hmerge, rfl | rfl⟩ | ⟨hXL, hXne⟩)
    · exact hA
    · exact hB
    · have hXin :
          X ∈ insert (A ∪ B) ((P.erase A).erase B) := by
        simpa [hL] using (List.mem_toFinset.mpr hXL)
      rcases mem_merge_family_iff.mp hXin with hXmerge | hXold
      · exact (hXne hXmerge).elim
      · exact hXold.1
  · intro hXP
    by_cases hXA : X = A
    · subst X
      left
      constructor
      · exact List.mem_toFinset.mp (by simp [hL])
      · exact Or.inl rfl
    · by_cases hXB : X = B
      · subst X
        left
        constructor
        · exact List.mem_toFinset.mp (by simp [hL])
        · exact Or.inr rfl
      · right
        constructor
        · exact List.mem_toFinset.mp (by
            rw [hL]
            exact mem_merge_family_iff.mpr (Or.inr ⟨hXP, hXA, hXB⟩))
        · intro hXmerge
          exact (union_ne_bag_of_disjoint_left hP hA hXP (fun h => hXA h.symm))
            hXmerge.symm

theorem splitMergedBag_nodup_of_merge
    {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} (_hP : IsBagPartition P)
    {A B : Finset V} (_hA : A ∈ P) (_hB : B ∈ P) (hAB : A ≠ B)
    {L : List (Finset V)} (hLnodup : L.Nodup)
    (hL : L.toFinset = insert (A ∪ B) ((P.erase A).erase B)) :
    (splitMergedBag A B L).Nodup := by
  classical
  rw [splitMergedBag, List.nodup_flatMap]
  constructor
  · intro X _hXL
    by_cases hX : X = A ∪ B
    · subst X
      simp [hAB]
    · simp [hX]
  · refine hLnodup.pairwise_of_forall_ne ?_
    intro X hXL Y hYL hXY Z hZX hZY
    have old_of_mem_not_merge :
        ∀ {W : Finset V}, W ∈ L → W ≠ A ∪ B → W ∈ P ∧ W ≠ A ∧ W ≠ B := by
      intro W hWL hWne
      have hWin :
          W ∈ insert (A ∪ B) ((P.erase A).erase B) := by
        simpa [hL] using (List.mem_toFinset.mpr hWL)
      rcases mem_merge_family_iff.mp hWin with hWmerge | hWold
      · exact (hWne hWmerge).elim
      · exact hWold
    by_cases hXmerge : X = A ∪ B
    · subst X
      have hYold := old_of_mem_not_merge hYL (fun h => hXY h.symm)
      by_cases hYmerge : Y = A ∪ B
      · exact hXY hYmerge.symm
      · simp [hYmerge] at hZY
        subst Z
        simp at hZX
        rcases hZX with hYA | hYB
        · exact hYold.2.1 hYA
        · exact hYold.2.2 hYB
    · have hXold := old_of_mem_not_merge hXL hXmerge
      by_cases hYmerge : Y = A ∪ B
      · subst Y
        simp [hXmerge] at hZX
        subst Z
        simp at hZY
        rcases hZY with hXA | hXB
        · exact hXold.2.1 hXA
        · exact hXold.2.2 hXB
      · simp [hXmerge] at hZX
        simp [hYmerge] at hZY
        subst Z
        exact hXY hZY

theorem isContractionStep_isSemanticState
    {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {T U : TrigraphState V}
    (hsem : IsSemanticState G T) (hstep : IsContractionStep T U) :
    IsSemanticState G U := by
  classical
  rcases hstep with ⟨A, hA, B, hB, hAB, hbags, hredStep, hblackStep⟩
  have hTpart : IsBagPartition T.bags :=
    ⟨T.bag_nonempty, T.bag_disjoint, T.bag_cover⟩
  constructor
  · intro X Y hX hY
    have hXclass :
        X = A ∪ B ∨ (X ∈ T.bags ∧ X ≠ A ∧ X ≠ B) := by
      exact mem_merge_family_iff.mp (by simpa [hbags] using hX)
    have hYclass :
        Y = A ∪ B ∨ (Y ∈ T.bags ∧ Y ≠ A ∧ Y ≠ B) := by
      exact mem_merge_family_iff.mp (by simpa [hbags] using hY)
    rw [hredStep hX hY]
    by_cases hXY : X = Y
    · subst Y
      simp [partitionRedAdj, contractedRed]
    · by_cases hXm : X = A ∪ B
      · subst X
        rcases hYclass with hYm | hYold
        · exact (hXY hYm.symm).elim
        · have hUY : A ∪ B ≠ Y :=
            union_ne_bag_of_disjoint_left hTpart hA hYold.1 hYold.2.1.symm
          have hredA :
              T.redAdj A Y ↔ partitionRedAdj G A Y := hsem.1 hA hYold.1
          have hredB :
              T.redAdj B Y ↔ partitionRedAdj G B Y := hsem.1 hB hYold.1
          have hblackA :
              T.blackAdj A Y ↔ partitionBlackAdj G A Y := hsem.2 hA hYold.1
          have hblackB :
              T.blackAdj B Y ↔ partitionBlackAdj G B Y := hsem.2 hB hYold.1
          simpa [contractedRed, hUY, hredA, hredB, hblackA, hblackB] using
            (partitionRedAdj_union_left_iff
              (G := G) (A := A) (B := B) (C := Y)
              (T.bag_nonempty hA) (T.bag_nonempty hB) (T.bag_nonempty hYold.1)
              hYold.2.1.symm hYold.2.2.symm hUY).symm
      · by_cases hYm : Y = A ∪ B
        · subst Y
          rcases hXclass with hXmerge | hXold
          · exact (hXm hXmerge).elim
          · have hXU : X ≠ A ∪ B := hXY
            have hredA :
                T.redAdj X A ↔ partitionRedAdj G X A := hsem.1 hXold.1 hA
            have hredB :
                T.redAdj X B ↔ partitionRedAdj G X B := hsem.1 hXold.1 hB
            have hblackA :
                T.blackAdj X A ↔ partitionBlackAdj G X A := hsem.2 hXold.1 hA
            have hblackB :
                T.blackAdj X B ↔ partitionBlackAdj G X B := hsem.2 hXold.1 hB
            simpa [contractedRed, hXY, hXm, hXU, hredA, hredB, hblackA, hblackB] using
              (partitionRedAdj_union_right_iff
                (G := G) (A := A) (B := B) (C := X)
                (T.bag_nonempty hA) (T.bag_nonempty hB) (T.bag_nonempty hXold.1)
                hXold.2.1 hXold.2.2 hXU).symm
        · rcases hXclass with hXmerge | hXold
          · exact (hXm hXmerge).elim
          rcases hYclass with hYmerge | hYold
          · exact (hYm hYmerge).elim
          have hred :
              T.redAdj X Y ↔ partitionRedAdj G X Y := hsem.1 hXold.1 hYold.1
          simp [contractedRed, hXY, hXm, hYm, hred]
  · intro X Y hX hY
    have hXclass :
        X = A ∪ B ∨ (X ∈ T.bags ∧ X ≠ A ∧ X ≠ B) := by
      exact mem_merge_family_iff.mp (by simpa [hbags] using hX)
    have hYclass :
        Y = A ∪ B ∨ (Y ∈ T.bags ∧ Y ≠ A ∧ Y ≠ B) := by
      exact mem_merge_family_iff.mp (by simpa [hbags] using hY)
    rw [hblackStep hX hY]
    by_cases hXY : X = Y
    · subst Y
      simp [partitionBlackAdj, contractedBlack]
    · by_cases hXm : X = A ∪ B
      · subst X
        rcases hYclass with hYm | hYold
        · exact (hXY hYm.symm).elim
        · have hUY : A ∪ B ≠ Y :=
            union_ne_bag_of_disjoint_left hTpart hA hYold.1 hYold.2.1.symm
          have hredA :
              T.redAdj A Y ↔ partitionRedAdj G A Y := hsem.1 hA hYold.1
          have hredB :
              T.redAdj B Y ↔ partitionRedAdj G B Y := hsem.1 hB hYold.1
          have hblackA :
              T.blackAdj A Y ↔ partitionBlackAdj G A Y := hsem.2 hA hYold.1
          have hblackB :
              T.blackAdj B Y ↔ partitionBlackAdj G B Y := hsem.2 hB hYold.1
          simpa [contractedBlack, contractedRed, hUY, hredA, hredB, hblackA, hblackB] using
            (partitionBlackAdj_union_left_iff
              (G := G) (A := A) (B := B) (C := Y)
              (T.bag_nonempty hA) (T.bag_nonempty hB) (T.bag_nonempty hYold.1)
              hYold.2.1.symm hYold.2.2.symm hUY).symm
      · by_cases hYm : Y = A ∪ B
        · subst Y
          rcases hXclass with hXmerge | hXold
          · exact (hXm hXmerge).elim
          · have hXU : X ≠ A ∪ B := hXY
            have hredA :
                T.redAdj X A ↔ partitionRedAdj G X A := hsem.1 hXold.1 hA
            have hredB :
                T.redAdj X B ↔ partitionRedAdj G X B := hsem.1 hXold.1 hB
            have hblackA :
                T.blackAdj X A ↔ partitionBlackAdj G X A := hsem.2 hXold.1 hA
            have hblackB :
                T.blackAdj X B ↔ partitionBlackAdj G X B := hsem.2 hXold.1 hB
            simpa [contractedBlack, contractedRed, hXY, hXm, hXU, hredA, hredB, hblackA, hblackB] using
              (partitionBlackAdj_union_right_iff
                (G := G) (A := A) (B := B) (C := X)
                (T.bag_nonempty hA) (T.bag_nonempty hB) (T.bag_nonempty hXold.1)
                hXold.2.1 hXold.2.2 hXU).symm
        · rcases hXclass with hXmerge | hXold
          · exact (hXm hXmerge).elim
          rcases hYclass with hYmerge | hYold
          · exact (hYm hYmerge).elim
          have hblack :
              T.blackAdj X Y ↔ partitionBlackAdj G X Y := hsem.2 hXold.1 hYold.1
          simp [contractedBlack, hXY, hXm, hYm, hblack]

theorem ContractionSequence.isSemanticState
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ i, i ≤ S.stepCount → IsSemanticState G (S.state i) := by
  intro i hi
  induction i with
  | zero =>
      exact isInitialState_isSemanticState S.starts
  | succ i ih =>
      have hi' : i < S.stepCount := by omega
      exact isContractionStep_isSemanticState (ih (le_of_lt hi'))
        (S.step_contracts i hi')

/-- The red-degree bound of a contraction sequence, read in the semantic
partition language. -/
theorem ContractionSequence.partitionRedDegreeAtMost_state
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    PartitionRedDegreeAtMost G (S.state i).bags d := by
  classical
  intro A hA
  have hsem := S.isSemanticState i hi
  have hfilter :
      ((S.state i).bags.filter fun B => partitionRedAdj G A B) =
        ((S.state i).bags.filter fun B => (S.state i).redAdj A B) := by
    ext B
    by_cases hB : B ∈ (S.state i).bags
    · simp [hB, (hsem.1 hA hB).symm]
    · simp [hB]
  rw [hfilter]
  exact S.redDegree_le i hi hA

theorem isContractionStep_trigraphStateOfPartition_of_isBagContraction
    {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {P Q : Finset (Finset V)}
    (hP : IsBagPartition P) (hQ : IsBagPartition Q)
    (hPQ : IsBagContraction P Q) :
    IsContractionStep
      (trigraphStateOfPartition G P hP)
      (trigraphStateOfPartition G Q hQ) := by
  classical
  rcases hPQ with ⟨A, hA, B, hB, hAB, rfl⟩
  refine ⟨A, hA, B, hB, hAB, rfl, ?_, ?_⟩
  · show ∀ ⦃X Y : Finset V⦄,
        X ∈ (trigraphStateOfPartition G
          (insert (A ∪ B) ((P.erase A).erase B)) hQ).bags →
        Y ∈ (trigraphStateOfPartition G
          (insert (A ∪ B) ((P.erase A).erase B)) hQ).bags →
          ((trigraphStateOfPartition G
            (insert (A ∪ B) ((P.erase A).erase B)) hQ).redAdj X Y ↔
            contractedRed (trigraphStateOfPartition G P hP) A B X Y)
    refine fun ⦃X Y : Finset V⦄
      (hX : X ∈ (trigraphStateOfPartition G
        (insert (A ∪ B) ((P.erase A).erase B)) hQ).bags)
      (hY : Y ∈ (trigraphStateOfPartition G
        (insert (A ∪ B) ((P.erase A).erase B)) hQ).bags) => by
      show (trigraphStateOfPartition G
          (insert (A ∪ B) ((P.erase A).erase B)) hQ).redAdj X Y ↔
        contractedRed (trigraphStateOfPartition G P hP) A B X Y
      change partitionRedAdj G X Y ↔
        contractedRed (trigraphStateOfPartition G P hP) A B X Y
      have hXclass :
          X = A ∪ B ∨ (X ∈ P ∧ X ≠ A ∧ X ≠ B) :=
        mem_merge_family_iff.mp (by simpa [trigraphStateOfPartition] using hX)
      have hYclass :
          Y = A ∪ B ∨ (Y ∈ P ∧ Y ≠ A ∧ Y ≠ B) :=
        mem_merge_family_iff.mp (by simpa [trigraphStateOfPartition] using hY)
      by_cases hXY : X = Y
      · subst Y
        simp [partitionRedAdj, contractedRed]
      · by_cases hXm : X = A ∪ B
        · subst X
          rcases hYclass with hYm | hYold
          · exact (hXY hYm.symm).elim
          · have hUY : A ∪ B ≠ Y :=
              union_ne_bag_of_disjoint_left hP hA hYold.1 hYold.2.1.symm
            simpa [trigraphStateOfPartition, contractedRed, hUY] using
              (partitionRedAdj_union_left_iff
                (G := G) (A := A) (B := B) (C := Y)
                (hP.1 hA) (hP.1 hB) (hP.1 hYold.1)
                hYold.2.1.symm hYold.2.2.symm hUY)
        · by_cases hYm : Y = A ∪ B
          · subst Y
            rcases hXclass with hXmerge | hXold
            · exact (hXm hXmerge).elim
            · have hXU : X ≠ A ∪ B := hXY
              simpa [trigraphStateOfPartition, contractedRed, hXY, hXm, hXU] using
                (partitionRedAdj_union_right_iff
                  (G := G) (A := A) (B := B) (C := X)
                  (hP.1 hA) (hP.1 hB) (hP.1 hXold.1)
                  hXold.2.1 hXold.2.2 hXU)
          · rcases hXclass with hXmerge | hXold
            · exact (hXm hXmerge).elim
            rcases hYclass with hYmerge | hYold
            · exact (hYm hYmerge).elim
            simp [trigraphStateOfPartition, contractedRed, hXY, hXm, hYm]
  · show ∀ ⦃X Y : Finset V⦄,
        X ∈ (trigraphStateOfPartition G
          (insert (A ∪ B) ((P.erase A).erase B)) hQ).bags →
        Y ∈ (trigraphStateOfPartition G
          (insert (A ∪ B) ((P.erase A).erase B)) hQ).bags →
          ((trigraphStateOfPartition G
            (insert (A ∪ B) ((P.erase A).erase B)) hQ).blackAdj X Y ↔
            contractedBlack (trigraphStateOfPartition G P hP) A B X Y)
    refine fun ⦃X Y : Finset V⦄
      (hX : X ∈ (trigraphStateOfPartition G
        (insert (A ∪ B) ((P.erase A).erase B)) hQ).bags)
      (hY : Y ∈ (trigraphStateOfPartition G
        (insert (A ∪ B) ((P.erase A).erase B)) hQ).bags) => by
      show (trigraphStateOfPartition G
          (insert (A ∪ B) ((P.erase A).erase B)) hQ).blackAdj X Y ↔
        contractedBlack (trigraphStateOfPartition G P hP) A B X Y
      change partitionBlackAdj G X Y ↔
        contractedBlack (trigraphStateOfPartition G P hP) A B X Y
      have hXclass :
          X = A ∪ B ∨ (X ∈ P ∧ X ≠ A ∧ X ≠ B) :=
        mem_merge_family_iff.mp (by simpa [trigraphStateOfPartition] using hX)
      have hYclass :
          Y = A ∪ B ∨ (Y ∈ P ∧ Y ≠ A ∧ Y ≠ B) :=
        mem_merge_family_iff.mp (by simpa [trigraphStateOfPartition] using hY)
      by_cases hXY : X = Y
      · subst Y
        simp [partitionBlackAdj, contractedBlack]
      · by_cases hXm : X = A ∪ B
        · subst X
          rcases hYclass with hYm | hYold
          · exact (hXY hYm.symm).elim
          · have hUY : A ∪ B ≠ Y :=
              union_ne_bag_of_disjoint_left hP hA hYold.1 hYold.2.1.symm
            simpa [trigraphStateOfPartition, contractedBlack, contractedRed, hUY] using
              (partitionBlackAdj_union_left_iff
                (G := G) (A := A) (B := B) (C := Y)
                (hP.1 hA) (hP.1 hB) (hP.1 hYold.1)
                hYold.2.1.symm hYold.2.2.symm hUY)
        · by_cases hYm : Y = A ∪ B
          · subst Y
            rcases hXclass with hXmerge | hXold
            · exact (hXm hXmerge).elim
            · have hXU : X ≠ A ∪ B := hXY
              simpa [trigraphStateOfPartition, contractedBlack, contractedRed, hXY, hXm, hXU] using
                (partitionBlackAdj_union_right_iff
                  (G := G) (A := A) (B := B) (C := X)
                  (hP.1 hA) (hP.1 hB) (hP.1 hXold.1)
                  hXold.2.1 hXold.2.2 hXU)
          · rcases hXclass with hXmerge | hXold
            · exact (hXm hXmerge).elim
            rcases hYclass with hYmerge | hYold
            · exact (hYm hYmerge).elim
            simp [trigraphStateOfPartition, contractedBlack, hXY, hXm, hYm]

/-- A graph partition sequence whose red degree is bounded at every step. -/
structure GraphPartitionSequence {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) where
  /-- Number of contractions. -/
  stepCount : ℕ
  /-- Bag family at each time. -/
  bags : ℕ → Finset (Finset V)
  /-- Every bag family is a partition of `V`. -/
  isPartition : ∀ i, i ≤ stepCount → IsBagPartition (bags i)
  /-- The first partition is the singleton partition. -/
  starts : bags 0 = TrigraphState.singletonBags V
  /-- The first semantic trigraph state is the initial graph state. -/
  starts_state :
    IsInitialState G
      (trigraphStateOfPartition G (bags 0) (isPartition 0 (Nat.zero_le stepCount)))
  /-- The final partition has at most one part. -/
  ends : (bags stepCount).card ≤ 1
  /-- Each step is a trigraph contraction between the semantic states carried
  by the two consecutive graph partitions. -/
  step_contracts : ∀ i, (hi : i < stepCount) →
    IsContractionStep
      (trigraphStateOfPartition G (bags i) (isPartition i (le_of_lt hi)))
      (trigraphStateOfPartition G (bags (i + 1)) (isPartition (i + 1) (by omega)))
  /-- Every partition has red degree at most `d`. -/
  redDegree_le : ∀ i, i ≤ stepCount → PartitionRedDegreeAtMost G (bags i) d

namespace GraphPartitionSequence

/-- The trigraph state at time `i`, using the final state outside the declared
time interval to keep the function total. -/
noncomputable def state {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : GraphPartitionSequence G d) (i : ℕ) : TrigraphState V :=
  if h : i ≤ S.stepCount then
    trigraphStateOfPartition G (S.bags i) (S.isPartition i h)
  else
    trigraphStateOfPartition G (S.bags S.stepCount) (S.isPartition S.stepCount le_rfl)

@[simp] theorem state_of_le {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : GraphPartitionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    S.state i = trigraphStateOfPartition G (S.bags i) (S.isPartition i hi) := by
  simp [state, hi]

theorem initial_state {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : GraphPartitionSequence G d) :
    IsInitialState G (S.state 0) := by
  simpa [state_of_le S (Nat.zero_le S.stepCount)] using S.starts_state

/-- A graph partition sequence is an ordinary graph contraction sequence. -/
noncomputable def toContractionSequence {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : GraphPartitionSequence G d) : ContractionSequence G d where
  stepCount := S.stepCount
  state := S.state
  starts := S.initial_state
  ends := by
    rw [state_of_le S le_rfl]
    exact S.ends
  step_contracts := by
    intro i hi
    rw [state_of_le S (le_of_lt hi),
      state_of_le S (by omega : i + 1 ≤ S.stepCount)]
    exact S.step_contracts i hi
  redDegree_le := by
    intro i hi A hA
    rw [state_of_le S hi] at hA ⊢
    exact S.redDegree_le i hi hA

/-- A bounded graph partition sequence proves the corresponding graph
twin-width bound. -/
theorem hasTwinWidthAtMost_of_graphPartitionSequence {V : Type*}
    [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : GraphPartitionSequence G d) :
    HasTwinWidthAtMost G d :=
  ⟨S.toContractionSequence⟩

end GraphPartitionSequence

/-- A tail of a graph partition sequence starting from a prescribed bag
family.  It is used to prove finite existence by repeatedly merging arbitrary
bags; the sharp width bounds are supplied elsewhere. -/
structure GraphPartitionTail {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) (P₀ : Finset (Finset V)) where
  /-- Number of remaining contractions. -/
  stepCount : ℕ
  /-- Bag family at each time. -/
  bags : ℕ → Finset (Finset V)
  /-- Every bag family is a partition of `V`. -/
  isPartition : ∀ i, i ≤ stepCount → IsBagPartition (bags i)
  /-- The first bag family is the prescribed one. -/
  starts : bags 0 = P₀
  /-- The final partition has at most one part. -/
  ends : (bags stepCount).card ≤ 1
  /-- Consecutive terms are semantic trigraph contractions. -/
  step_contracts : ∀ i, (hi : i < stepCount) →
    IsContractionStep
      (trigraphStateOfPartition G (bags i) (isPartition i (le_of_lt hi)))
      (trigraphStateOfPartition G (bags (i + 1)) (isPartition (i + 1) (by omega)))
  /-- Every partition in the tail satisfies the requested red-degree bound. -/
  redDegree_le : ∀ i, i ≤ stepCount → PartitionRedDegreeAtMost G (bags i) d

namespace GraphPartitionTail

/-- The empty tail from an already final partition. -/
def nil {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ} {P : Finset (Finset V)}
    (hP : IsBagPartition P) (hfinal : P.card ≤ 1)
    (hred : PartitionRedDegreeAtMost G P d) :
    GraphPartitionTail G d P where
  stepCount := 0
  bags := fun _ => P
  isPartition := by intro i hi; simpa using hP
  starts := rfl
  ends := by simpa using hfinal
  step_contracts := by intro i hi; omega
  redDegree_le := by intro i hi; simpa using hred

/-- Prepend one bag contraction to a graph partition tail. -/
def cons {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    {P Q : Finset (Finset V)}
    (hP : IsBagPartition P) (hQ : IsBagPartition Q)
    (hPQ : IsBagContraction P Q)
    (hredP : PartitionRedDegreeAtMost G P d)
    (S : GraphPartitionTail G d Q) :
    GraphPartitionTail G d P where
  stepCount := S.stepCount + 1
  bags := fun i =>
    match i with
    | 0 => P
    | j + 1 => S.bags j
  isPartition := by
    intro i hi
    cases i with
    | zero =>
        simpa using hP
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.isPartition j hj
  starts := rfl
  ends := by
    simpa using S.ends
  step_contracts := by
    intro i hi
    cases i with
    | zero =>
        simpa [S.starts] using
          isContractionStep_trigraphStateOfPartition_of_isBagContraction
            hP hQ hPQ
    | succ j =>
        have hj : j < S.stepCount := by omega
        simpa using S.step_contracts j hj
  redDegree_le := by
    intro i hi
    cases i with
    | zero =>
        simpa using hredP
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.redDegree_le j hj

end GraphPartitionTail

/-- From any bag partition, arbitrary mergers reach a final partition with
red degree bounded by the number of vertices. -/
theorem exists_graphPartitionTail_card_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    ∀ P : Finset (Finset V), IsBagPartition P →
      Nonempty (GraphPartitionTail G (Fintype.card V) P) := by
  classical
  intro P
  refine WellFounded.induction
    (C := fun P : Finset (Finset V) =>
      IsBagPartition P →
        Nonempty (GraphPartitionTail G (Fintype.card V) P))
    (InvImage.wf (fun P : Finset (Finset V) => P.card) <| (Nat.lt_wfRel).2)
    P ?_
  intro P ih hP
  by_cases hfinal : P.card ≤ 1
  · exact ⟨GraphPartitionTail.nil hP hfinal (partitionRedDegreeAtMost_card hP)⟩
  · have hgt : 1 < P.card := by omega
    rcases Finset.one_lt_card.mp hgt with ⟨A, hA, B, hB, hAB⟩
    let Q : Finset (Finset V) := insert (A ∪ B) ((P.erase A).erase B)
    have hQ : IsBagPartition Q := isBagPartition_merge hP hA hB hAB
    have hPQ : IsBagContraction P Q := ⟨A, hA, B, hB, hAB, rfl⟩
    have hcard_add :
        Q.card + 1 = P.card := by
      have hstep :=
        isContractionStep_trigraphStateOfPartition_of_isBagContraction
          (G := G) hP hQ hPQ
      simpa [trigraphStateOfPartition, Q] using hstep.bags_card_add_one
    have hlt : Q.card < P.card := by omega
    rcases ih Q hlt hQ with ⟨S⟩
    exact ⟨GraphPartitionTail.cons hP hQ hPQ
      (partitionRedDegreeAtMost_card hP) S⟩

/-- Every finite graph has a graph partition sequence whose width is bounded
by the number of vertices.  This supplies the total existence fact for
`twinWidth`; sharp bounds are proved by the Theorem 14 construction. -/
theorem exists_graphPartitionSequence_card_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    Nonempty (GraphPartitionSequence G (Fintype.card V)) := by
  classical
  rcases exists_graphPartitionTail_card_bound G
      (TrigraphState.singletonBags V) (singletonBags_isBagPartition V) with ⟨S⟩
  refine ⟨?_⟩
  exact
    { stepCount := S.stepCount
      bags := S.bags
      isPartition := S.isPartition
      starts := S.starts
      starts_state := by
        simpa [S.starts] using trigraphStateOfPartition_singletonBags_initial G
      ends := S.ends
      step_contracts := S.step_contracts
      redDegree_le := S.redDegree_le }

/-- Every finite graph has twin-width at most its number of vertices. -/
theorem hasTwinWidthAtMost_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    HasTwinWidthAtMost G (Fintype.card V) := by
  rcases exists_graphPartitionSequence_card_bound G with ⟨S⟩
  exact GraphPartitionSequence.hasTwinWidthAtMost_of_graphPartitionSequence S

/-- The `twinWidth` minimum is always attained for finite graphs. -/
theorem hasTwinWidthAtMost_twinWidth'
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    HasTwinWidthAtMost G (twinWidth G) :=
  hasTwinWidthAtMost_twinWidth G ⟨Fintype.card V, hasTwinWidthAtMost_card G⟩

/-- A numerical upper bound on `twinWidth` can be witnessed by a contraction
sequence with that bound. -/
theorem hasTwinWidthAtMost_of_twinWidth_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (h : twinWidth G ≤ d) :
    HasTwinWidthAtMost G d :=
  hasTwinWidthAtMost_mono (hasTwinWidthAtMost_twinWidth' G) h

/-- To prove a strict lower bound on twin-width, it is enough to rule out
bounded contraction sequences at that width. -/
theorem lt_twinWidth_of_not_hasTwinWidthAtMost
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (h : ¬ HasTwinWidthAtMost G d) :
    d < twinWidth G := by
  by_contra hnot
  exact h (hasTwinWidthAtMost_of_twinWidth_le (Nat.le_of_not_gt hnot))

/-- The trivial finite upper bound on graph twin-width. -/
theorem twinWidth_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    twinWidth G ≤ Fintype.card V :=
  twinWidth_le_of_hasTwinWidthAtMost (hasTwinWidthAtMost_card G)

end SimpleGraph
end TwinWidth

/- ===== end Graph/Partition.lean ===== -/

/- ===== begin Matrix/MixedWitness.lean ===== -/

/-
# Witnesses for mixed cells

This file proves the elementary witness form of a mixed cell.  A cell is mixed
iff it has a vertical disagreement and a horizontal disagreement.  The separate
corner file distinguishes paper-style adjacent corners from the weaker
non-contiguous `2 x 2` witnesses used in some algebraic proofs.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

/-- A vertical disagreement inside a divided cell. -/
def CellVerticalDisagreement {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∃ r₁ ∈ R.part i, ∃ r₂ ∈ R.part i, ∃ c ∈ C.part j, M r₁ c ≠ M r₂ c

/-- A horizontal disagreement inside a divided cell. -/
def CellHorizontalDisagreement {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∃ r ∈ R.part i, ∃ c₁ ∈ C.part j, ∃ c₂ ∈ C.part j, M r c₁ ≠ M r c₂

theorem not_cellVertical_iff_verticalDisagreement {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    ¬ CellVertical M R C i j ↔ CellVerticalDisagreement M R C i j := by
  classical
  simp [CellVertical, CellVerticalDisagreement]

theorem not_cellHorizontal_iff_horizontalDisagreement {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    ¬ CellHorizontal M R C i j ↔ CellHorizontalDisagreement M R C i j := by
  classical
  simp [CellHorizontal, CellHorizontalDisagreement]

/-- A mixed cell has exactly the two expected disagreement witnesses. -/
theorem cellMixed_iff_disagreements {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    CellMixed M R C i j ↔
      CellVerticalDisagreement M R C i j ∧ CellHorizontalDisagreement M R C i j := by
  rw [CellMixed, not_cellVertical_iff_verticalDisagreement,
    not_cellHorizontal_iff_horizontalDisagreement]

end Matrix
end TwinWidth

/- ===== end Matrix/MixedWitness.lean ===== -/

/- ===== begin Matrix/Partition.lean ===== -/

/-
# Matrix partitions and error value

This file formalizes the partition-and-error language from Section 5.2 of the
first twin-width paper.  A matrix partition is a row partition and a column
partition of the underlying finite intervals.  The error value counts
nonconstant zones.  It is recorded by the predicate `ErrorValueAtMost`,
avoiding a premature commitment to a concrete maximum operator.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

/-- A finite partition of the rows and columns of an `n × m` matrix. -/
structure MatrixPartition (n m : ℕ) where
  /-- Row parts. -/
  rowParts : Finset (Finset (Fin n))
  /-- Every row part is nonempty. -/
  row_nonempty : ∀ ⦃R⦄, R ∈ rowParts → R.Nonempty
  /-- Distinct row parts are disjoint. -/
  row_disjoint : ∀ ⦃R S⦄, R ∈ rowParts → S ∈ rowParts → R ≠ S → Disjoint R S
  /-- Row parts cover all rows. -/
  row_cover : ∀ r : Fin n, ∃ R ∈ rowParts, r ∈ R
  /-- Column parts. -/
  colParts : Finset (Finset (Fin m))
  /-- Every column part is nonempty. -/
  col_nonempty : ∀ ⦃C⦄, C ∈ colParts → C.Nonempty
  /-- Distinct column parts are disjoint. -/
  col_disjoint : ∀ ⦃C D⦄, C ∈ colParts → D ∈ colParts → C ≠ D → Disjoint C D
  /-- Column parts cover all columns. -/
  col_cover : ∀ c : Fin m, ∃ C ∈ colParts, c ∈ C

namespace MatrixPartition

/-- A family of finite sets refines another if every part is contained in a
part of the latter family. -/
def PartsRefine {α : Type*} (P Q : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ P → ∃ B ∈ Q, A ⊆ B

/-- `P` `r`-refines `Q` if it refines `Q` and no part of `Q` contains more
than `r` parts of `P`. -/
def PartsRRefine {α : Type*} [DecidableEq α]
    (P Q : Finset (Finset α)) (r : ℕ) : Prop :=
  PartsRefine P Q ∧ ∀ ⦃B⦄, B ∈ Q → (P.filter fun A => A ⊆ B).card ≤ r

/-- Refinement of matrix partitions, componentwise on rows and columns. -/
def Refines {n m : ℕ} (P Q : MatrixPartition n m) : Prop :=
  PartsRefine P.rowParts Q.rowParts ∧ PartsRefine P.colParts Q.colParts

/-- Bounded refinement of matrix partitions, componentwise on rows and
columns. -/
def RRefines {n m : ℕ} (P Q : MatrixPartition n m) (r : ℕ) : Prop :=
  PartsRRefine P.rowParts Q.rowParts r ∧ PartsRRefine P.colParts Q.colParts r

/-- A row contraction merges two distinct row parts and leaves columns fixed. -/
def IsRowContraction {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]
    (P Q : MatrixPartition n m) : Prop :=
  ∃ R ∈ P.rowParts, ∃ S ∈ P.rowParts, R ≠ S ∧
    Q.rowParts = insert (R ∪ S) ((P.rowParts.erase R).erase S) ∧
    Q.colParts = P.colParts

/-- A column contraction merges two distinct column parts and leaves rows fixed. -/
def IsColContraction {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]
    (P Q : MatrixPartition n m) : Prop :=
  ∃ C ∈ P.colParts, ∃ D ∈ P.colParts, C ≠ D ∧
    Q.colParts = insert (C ∪ D) ((P.colParts.erase C).erase D) ∧
    Q.rowParts = P.rowParts

/-- A matrix partition contraction is either a row contraction or a column
contraction. -/
def IsContraction {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]
    (P Q : MatrixPartition n m) : Prop :=
  IsRowContraction P Q ∨ IsColContraction P Q

end MatrixPartition

/-- A rectangular zone is vertical if each column is constant across the row
set. -/
def ZoneVertical {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R → r₂ ∈ R →
    ∀ ⦃c : Fin m⦄, c ∈ C → M r₁ c = M r₂ c

/-- A rectangular zone is horizontal if each row is constant across the column
set. -/
def ZoneHorizontal {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C → c₂ ∈ C → M r c₁ = M r c₂

/-- A rectangular zone is mixed if it is neither vertical nor horizontal. -/
def ZoneMixed {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ¬ ZoneVertical M R C ∧ ¬ ZoneHorizontal M R C

/-- A zone is constant if all entries in the row part and column part have the
same matrix value. -/
def ZoneConstant {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R → r₂ ∈ R →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C → c₂ ∈ C → M r₁ c₁ = M r₂ c₂

/-- Column parts on which a fixed row part forms a nonconstant zone. -/
noncomputable def rowErrorSet {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (P : MatrixPartition n m) (R : Finset (Fin n)) : Finset (Finset (Fin m)) :=
  by
    classical
    exact P.colParts.filter fun C => ¬ ZoneConstant M R C

/-- Row parts on which a fixed column part forms a nonconstant zone. -/
noncomputable def colErrorSet {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (P : MatrixPartition n m) (C : Finset (Fin m)) : Finset (Finset (Fin n)) :=
  by
    classical
    exact P.rowParts.filter fun R => ¬ ZoneConstant M R C

/-- A matrix partition has error value at most `t` when every row part and
every column part sees at most `t` nonconstant zones. -/
def ErrorValueAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (P : MatrixPartition n m) (t : ℕ) : Prop :=
  (∀ ⦃R⦄, R ∈ P.rowParts → (rowErrorSet M P R).card ≤ t) ∧
    ∀ ⦃C⦄, C ∈ P.colParts → (colErrorSet M P C).card ≤ t

end Matrix
end TwinWidth

/- ===== end Matrix/Partition.lean ===== -/

/- ===== begin Matrix/MixedValue.lean ===== -/

/-
# Mixed zones, mixed cuts, and mixed value

This file formalizes the local quantities from Section 5.6.  Mixed values are
defined for one side of a division at a time: a column set measured against a
row division, and dually a row set measured against a column division.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

/-- The mixed zones of a column set on a row division. -/
noncomputable def rowMixedZones {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Finset (Fin m)) : Finset (Fin k) :=
  by
    classical
    exact Finset.univ.filter fun i => ZoneMixed M (R.part i) C

/-- The mixed zones of a row set on a column division. -/
noncomputable def colMixedZones {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m k) : Finset (Fin k) :=
  by
    classical
    exact Finset.univ.filter fun j => ZoneMixed M R (C.part j)

/-- The two-row cut between consecutive row parts is vertical on a column set
if the last row of the lower part and first row of the upper part agree on all
columns of the set. -/
def RowCutVertical {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) : Prop :=
  ∀ ⦃c : Fin m⦄, c ∈ C →
    M (R.last i.castSucc) c = M (R.first i.succ) c

/-- The two-row cut between consecutive row parts is horizontal on a column set
if each of the two boundary rows is constant on that column set. -/
def RowCutHorizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) : Prop :=
  (∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C → c₂ ∈ C →
      M (R.last i.castSucc) c₁ = M (R.last i.castSucc) c₂) ∧
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C → c₂ ∈ C →
      M (R.first i.succ) c₁ = M (R.first i.succ) c₂

/-- A mixed row cut. -/
def RowCutMixed {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) : Prop :=
  ¬ RowCutVertical M R C i ∧ ¬ RowCutHorizontal M R C i

/-- The mixed row cuts of a column set on a row division. -/
noncomputable def rowMixedCuts {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) : Finset (Fin k) :=
  by
    classical
    exact Finset.univ.filter fun i => RowCutMixed M R C i

/-- Column-cut verticality, dual to `RowCutVertical`. -/
def ColCutVertical {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) : Prop :=
  (∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R → r₂ ∈ R →
      M r₁ (C.last j.castSucc) = M r₂ (C.last j.castSucc)) ∧
    ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R → r₂ ∈ R →
      M r₁ (C.first j.succ) = M r₂ (C.first j.succ)

/-- Column-cut horizontality, dual to `RowCutHorizontal`. -/
def ColCutHorizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R →
    M r (C.last j.castSucc) = M r (C.first j.succ)

/-- A mixed column cut. -/
def ColCutMixed {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) : Prop :=
  ¬ ColCutVertical M R C j ∧ ¬ ColCutHorizontal M R C j

/-- The mixed column cuts of a row set on a column division. -/
noncomputable def colMixedCuts {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) : Finset (Fin k) :=
  by
    classical
    exact Finset.univ.filter fun j => ColCutMixed M R C j

/-- Mixed value of a column set on a row division with `k + 1` parts. -/
noncomputable def rowMixedValue {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) : ℕ :=
  (rowMixedZones M R C).card + (rowMixedCuts M R C).card

/-- Mixed value of a row set on a column division with `k + 1` parts. -/
noncomputable def colMixedValue {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) : ℕ :=
  (colMixedZones M R C).card + (colMixedCuts M R C).card

@[simp] theorem rowMixedValue_castIndex {n m k l : ℕ}
    (h : k = l) (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) :
    rowMixedValue M (Division.castIndex (by omega : k + 1 = l + 1) R) C =
      rowMixedValue M R C := by
  subst l
  simp [Division.castIndex]

@[simp] theorem colMixedValue_castIndex {n m k l : ℕ}
    (h : k = l) (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) :
    colMixedValue M R (Division.castIndex (by omega : k + 1 = l + 1) C) =
      colMixedValue M R C := by
  subst l
  simp [Division.castIndex]

/-- Mixed zones and mixed cuts of a column set on a row division, packaged as
one finite set.  This is useful for injection proofs showing that fusions do
not increase mixed value. -/
noncomputable def rowMixedItems {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) :
    Finset (Sum (Fin (k + 1)) (Fin k)) := by
  classical
  exact (rowMixedZones M R C).map ⟨Sum.inl, by intro a b h; simpa using h⟩ ∪
    (rowMixedCuts M R C).map ⟨Sum.inr, by intro a b h; simpa using h⟩

@[simp] theorem mem_rowMixedItems_zone {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin (k + 1)) :
    Sum.inl i ∈ rowMixedItems M R C ↔ ZoneMixed M (R.part i) C := by
  classical
  simp [rowMixedItems, rowMixedZones]

@[simp] theorem mem_rowMixedItems_cut {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) :
    Sum.inr i ∈ rowMixedItems M R C ↔ RowCutMixed M R C i := by
  classical
  simp [rowMixedItems, rowMixedCuts]

theorem rowMixedItems_card {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) :
    (rowMixedItems M R C).card = rowMixedValue M R C := by
  classical
  rw [rowMixedItems, Finset.card_union_of_disjoint]
  · simp [rowMixedValue]
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp at hx hy
    rcases hx with ⟨a, _ha, hxa⟩
    rcases hy with ⟨b, _hb, hyb⟩
    cases hxa.trans hyb.symm

/-- Mixed zones and mixed cuts of a row set on a column division, packaged as
one finite set. -/
noncomputable def colMixedItems {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) :
    Finset (Sum (Fin (k + 1)) (Fin k)) := by
  classical
  exact (colMixedZones M R C).map ⟨Sum.inl, by intro a b h; simpa using h⟩ ∪
    (colMixedCuts M R C).map ⟨Sum.inr, by intro a b h; simpa using h⟩

@[simp] theorem mem_colMixedItems_zone {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin (k + 1)) :
    Sum.inl j ∈ colMixedItems M R C ↔ ZoneMixed M R (C.part j) := by
  classical
  simp [colMixedItems, colMixedZones]

@[simp] theorem mem_colMixedItems_cut {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) :
    Sum.inr j ∈ colMixedItems M R C ↔ ColCutMixed M R C j := by
  classical
  simp [colMixedItems, colMixedCuts]

theorem colMixedItems_card {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) :
    (colMixedItems M R C).card = colMixedValue M R C := by
  classical
  rw [colMixedItems, Finset.card_union_of_disjoint]
  · simp [colMixedValue]
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp at hx hy
    rcases hx with ⟨a, _ha, hxa⟩
    rcases hy with ⟨b, _hb, hyb⟩
    cases hxa.trans hyb.symm

end Matrix
end TwinWidth

/- ===== end Matrix/MixedValue.lean ===== -/

/- ===== begin Matrix/Corner.lean ===== -/

/-
# Corners

This file separates two related notions.

* A `ZoneCorner` is the paper's notion from Section 5.5: a mixed `2 x 2`
  submatrix on adjacent rows and adjacent columns.
* A `ZoneTwoByTwoSubmatrix` is the weaker algebraic witness that a zone contains
  some mixed `2 x 2` submatrix, without an adjacency requirement.

The second notion is useful for elementary algebraic proofs about mixed zones,
but it is deliberately not called a corner.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

/-- The first index of an adjacent pair in `Fin n`, represented by a cut
position in `Fin (n - 1)`. -/
def adjacentFirst {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le n 1)⟩

/-- The second index of an adjacent pair in `Fin n`, represented by a cut
position in `Fin (n - 1)`. -/
def adjacentSecond {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1 + 1, by
    have hi : i.1 < n - 1 := i.2
    omega⟩

/-- A `2 x 2` submatrix is mixed when it is neither vertical nor horizontal. -/
def TwoByTwoMixed {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (r₁ r₂ : Fin n) (c₁ c₂ : Fin m) : Prop :=
  ((M r₁ c₁ ≠ M r₂ c₁) ∨ (M r₁ c₂ ≠ M r₂ c₂)) ∧
    ((M r₁ c₁ ≠ M r₁ c₂) ∨ (M r₂ c₁ ≠ M r₂ c₂))

/-- A paper-style corner: a mixed `2 x 2` submatrix using adjacent rows and
adjacent columns inside the rectangular zone. -/
def ZoneCorner {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∃ r : Fin (n - 1), adjacentFirst r ∈ R ∧ adjacentSecond r ∈ R ∧
    ∃ c : Fin (m - 1), adjacentFirst c ∈ C ∧ adjacentSecond c ∈ C ∧
      TwoByTwoMixed M (adjacentFirst r) (adjacentSecond r)
        (adjacentFirst c) (adjacentSecond c)

/-- A mixed `2 x 2` submatrix inside a rectangular zone, with no adjacency
requirement.  This is an algebraic witness for mixedness, not a paper corner. -/
def ZoneTwoByTwoSubmatrix {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C,
    TwoByTwoMixed M r₁ r₂ c₁ c₂

theorem not_zoneVertical_iff_exists {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ¬ ZoneVertical M R C ↔
      ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ c ∈ C, M r₁ c ≠ M r₂ c := by
  classical
  simp [ZoneVertical]

theorem not_zoneHorizontal_iff_exists {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ¬ ZoneHorizontal M R C ↔
      ∃ r ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C, M r c₁ ≠ M r c₂ := by
  classical
  simp [ZoneHorizontal]

theorem zoneTwoByTwoSubmatrix_of_zoneMixed {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneMixed M R C) : ZoneTwoByTwoSubmatrix M R C := by
  classical
  rcases (not_zoneVertical_iff_exists M R C).mp h.1 with
    ⟨a, ha, b, hb, x, hx, habx⟩
  rcases (not_zoneHorizontal_iff_exists M R C).mp h.2 with
    ⟨r, hr, y, hy, z, hz, hryz⟩
  by_cases hay : M a x ≠ M a y
  · exact ⟨a, ha, b, hb, x, hx, y, hy, Or.inl habx, Or.inl hay⟩
  · have hay' : M a x = M a y := Classical.not_not.mp hay
    by_cases hby : M b x ≠ M b y
    · exact ⟨a, ha, b, hb, x, hx, y, hy, Or.inl habx, Or.inr hby⟩
    · have hby' : M b x = M b y := Classical.not_not.mp hby
      by_cases haz : M a x ≠ M a z
      · exact ⟨a, ha, b, hb, x, hx, z, hz, Or.inl habx, Or.inl haz⟩
      · have haz' : M a x = M a z := Classical.not_not.mp haz
        by_cases hbz : M b x ≠ M b z
        · exact ⟨a, ha, b, hb, x, hx, z, hz, Or.inl habx, Or.inr hbz⟩
        · have hbz' : M b x = M b z := Classical.not_not.mp hbz
          have hayz : M a y = M a z := hay'.symm.trans haz'
          by_cases hrya : M r y ≠ M a y
          · exact ⟨r, hr, a, ha, y, hy, z, hz, Or.inl hrya, Or.inl hryz⟩
          · have hrya' : M r y = M a y := Classical.not_not.mp hrya
            have hrza : M r z ≠ M a z := by
              intro hrza
              exact hryz (hrya'.trans (hayz.trans hrza.symm))
            exact ⟨r, hr, a, ha, y, hy, z, hz, Or.inr hrza, Or.inl hryz⟩

theorem zoneMixed_of_zoneTwoByTwoSubmatrix {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneTwoByTwoSubmatrix M R C) : ZoneMixed M R C := by
  rcases h with ⟨r₁, hr₁, r₂, hr₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  constructor
  · intro hv
    rcases hvert with h | h
    · exact h (hv hr₁ hr₂ hc₁)
    · exact h (hv hr₁ hr₂ hc₂)
  · intro hh
    rcases hhoriz with h | h
    · exact h (hh hr₁ hc₁ hc₂)
    · exact h (hh hr₂ hc₁ hc₂)

/-- A rectangular zone is mixed iff it contains a mixed `2 x 2` submatrix.
This statement has no adjacency requirement; paper corners are `ZoneCorner`. -/
theorem zoneMixed_iff_zoneTwoByTwoSubmatrix {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ZoneMixed M R C ↔ ZoneTwoByTwoSubmatrix M R C :=
  ⟨zoneTwoByTwoSubmatrix_of_zoneMixed, zoneMixed_of_zoneTwoByTwoSubmatrix⟩

/-- A paper-style adjacent corner is, in particular, a mixed `2 x 2`
submatrix witness. -/
theorem zoneTwoByTwoSubmatrix_of_zoneCorner {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneCorner M R C) : ZoneTwoByTwoSubmatrix M R C := by
  rcases h with ⟨r, hr₁, hr₂, c, hc₁, hc₂, hmix⟩
  exact ⟨adjacentFirst r, hr₁, adjacentSecond r, hr₂,
    adjacentFirst c, hc₁, adjacentSecond c, hc₂, hmix⟩

/-- A paper-style adjacent corner witnesses that the zone is mixed. -/
theorem zoneMixed_of_zoneCorner {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneCorner M R C) : ZoneMixed M R C :=
  zoneMixed_of_zoneTwoByTwoSubmatrix (zoneTwoByTwoSubmatrix_of_zoneCorner h)

end Matrix
end TwinWidth

/- ===== end Matrix/Corner.lean ===== -/

/- ===== begin Matrix/Fusion.lean ===== -/

/-
# Fusion lemmas for mixed zones

This file proves the core fusion argument used in Lemma 12.  If two zones are
not mixed and no mixed `2 x 2` submatrix witness crosses between them, then
their union is not mixed.  The paper's corners are adjacent `2 x 2` witnesses;
the crossing predicates below are intentionally named as submatrix witnesses
because they do not impose adjacency.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

private theorem false_of_or_ne_of_eqs {α : Type*} {a b c d : α}
    (h : (a ≠ b) ∨ (c ≠ d)) (hab : a = b) (hcd : c = d) : False := by
  rcases h with h | h
  · exact h hab
  · exact h hcd

/-- A mixed crossing `2 x 2` submatrix witness between two row sets over a
column set.  This is not necessarily a paper corner, since the selected rows
and columns need not be adjacent. -/
def RowCrossingTwoByTwoSubmatrix {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R S : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∃ r ∈ R, ∃ s ∈ S, ∃ c₁ ∈ C, ∃ c₂ ∈ C,
    TwoByTwoMixed M r s c₁ c₂

/-- A mixed crossing `2 x 2` submatrix witness between two column sets over a
row set.  This is not necessarily a paper corner, since the selected rows and
columns need not be adjacent. -/
def ColCrossingTwoByTwoSubmatrix {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C D : Finset (Fin m)) : Prop :=
  ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ c ∈ C, ∃ d ∈ D,
    TwoByTwoMixed M r₁ r₂ c d

/-- A zone is not mixed exactly when it is vertical or horizontal. -/
theorem not_zoneMixed_iff_vertical_or_horizontal {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ¬ ZoneMixed M R C ↔ ZoneVertical M R C ∨ ZoneHorizontal M R C := by
  classical
  constructor
  · intro h
    by_cases hv : ZoneVertical M R C
    · exact Or.inl hv
    · by_cases hh : ZoneHorizontal M R C
      · exact Or.inr hh
      · exact False.elim (h ⟨hv, hh⟩)
  · intro h hmix
    rcases h with hv | hh
    · exact hmix.1 hv
    · exact hmix.2 hh

/-- A row cut is not mixed exactly when it is vertical or horizontal. -/
theorem not_rowCutMixed_iff_cutVertical_or_cutHorizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) (i : Fin k) :
    ¬ RowCutMixed M R C i ↔
      RowCutVertical M R C i ∨ RowCutHorizontal M R C i := by
  classical
  constructor
  · intro h
    by_cases hv : RowCutVertical M R C i
    · exact Or.inl hv
    · by_cases hh : RowCutHorizontal M R C i
      · exact Or.inr hh
      · exact False.elim (h ⟨hv, hh⟩)
  · intro h hmix
    rcases h with hv | hh
    · exact hmix.1 hv
    · exact hmix.2 hh

/-- A column cut is not mixed exactly when it is vertical or horizontal. -/
theorem not_colCutMixed_iff_cutVertical_or_cutHorizontal {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) (j : Fin k) :
    ¬ ColCutMixed M R C j ↔
      ColCutVertical M R C j ∨ ColCutHorizontal M R C j := by
  classical
  constructor
  · intro h
    by_cases hv : ColCutVertical M R C j
    · exact Or.inl hv
    · by_cases hh : ColCutHorizontal M R C j
      · exact Or.inr hh
      · exact False.elim (h ⟨hv, hh⟩)
  · intro h hmix
    rcases h with hv | hh
    · exact hmix.1 hv
    · exact hmix.2 hh

theorem not_zoneMixed_union_rows_of_no_crossing {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R S : Finset (Fin n)} {C : Finset (Fin m)}
    (hR : ¬ ZoneMixed M R C)
    (hS : ¬ ZoneMixed M S C)
    (hcross : ¬ RowCrossingTwoByTwoSubmatrix M R S C) :
    ¬ ZoneMixed M (R ∪ S) C := by
  intro hmix
  rcases (zoneMixed_iff_zoneTwoByTwoSubmatrix M (R ∪ S) C).mp hmix with
    ⟨r₁, hr₁, r₂, hr₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  rcases Finset.mem_union.mp hr₁ with hR₁ | hS₁
  · rcases Finset.mem_union.mp hr₂ with hR₂ | hS₂
    · exact hR ((zoneMixed_iff_zoneTwoByTwoSubmatrix M R C).mpr
        ⟨r₁, hR₁, r₂, hR₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩)
    · exact hcross ⟨r₁, hR₁, r₂, hS₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  · rcases Finset.mem_union.mp hr₂ with hR₂ | hS₂
    · have hvert' :
          (M r₂ c₁ ≠ M r₁ c₁) ∨ (M r₂ c₂ ≠ M r₁ c₂) := by
        rcases hvert with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have hhoriz' :
          (M r₂ c₁ ≠ M r₂ c₂) ∨ (M r₁ c₁ ≠ M r₁ c₂) := by
        exact hhoriz.symm
      exact hcross ⟨r₂, hR₂, r₁, hS₁, c₁, hc₁, c₂, hc₂, hvert', hhoriz'⟩
    · exact hS ((zoneMixed_iff_zoneTwoByTwoSubmatrix M S C).mpr
        ⟨r₁, hS₁, r₂, hS₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩)

theorem not_zoneMixed_union_cols_of_no_crossing {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C D : Finset (Fin m)}
    (hC : ¬ ZoneMixed M R C)
    (hD : ¬ ZoneMixed M R D)
    (hcross : ¬ ColCrossingTwoByTwoSubmatrix M R C D) :
    ¬ ZoneMixed M R (C ∪ D) := by
  intro hmix
  rcases (zoneMixed_iff_zoneTwoByTwoSubmatrix M R (C ∪ D)).mp hmix with
    ⟨r₁, hr₁, r₂, hr₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  rcases Finset.mem_union.mp hc₁ with hC₁ | hD₁
  · rcases Finset.mem_union.mp hc₂ with hC₂ | hD₂
    · exact hC ((zoneMixed_iff_zoneTwoByTwoSubmatrix M R C).mpr
        ⟨r₁, hr₁, r₂, hr₂, c₁, hC₁, c₂, hC₂, hvert, hhoriz⟩)
    · exact hcross ⟨r₁, hr₁, r₂, hr₂, c₁, hC₁, c₂, hD₂, hvert, hhoriz⟩
  · rcases Finset.mem_union.mp hc₂ with hC₂ | hD₂
    · have hhoriz' :
          (M r₁ c₂ ≠ M r₁ c₁) ∨ (M r₂ c₂ ≠ M r₂ c₁) := by
        rcases hhoriz with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have hvert' :
          (M r₁ c₂ ≠ M r₂ c₂) ∨ (M r₁ c₁ ≠ M r₂ c₁) := by
        exact hvert.symm
      exact hcross ⟨r₁, hr₁, r₂, hr₂, c₂, hC₂, c₁, hD₁, hvert', hhoriz'⟩
    · exact hD ((zoneMixed_iff_zoneTwoByTwoSubmatrix M R D).mpr
        ⟨r₁, hr₁, r₂, hr₂, c₁, hD₁, c₂, hD₂, hvert, hhoriz⟩)

/-- Boundary localization for consecutive row parts.  If two adjacent zones
are not mixed, then a nonmixed boundary cut prevents any mixed `2 x 2`
submatrix witness from crossing the boundary. -/
theorem not_rowCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (R : Division n (k + 1)) {C : Finset (Fin m)} (i : Fin k)
    (hLzone : ¬ ZoneMixed M (R.part i.castSucc) C)
    (hRzone : ¬ ZoneMixed M (R.part i.succ) C)
    (hcut : ¬ RowCutMixed M R C i) :
    ¬ RowCrossingTwoByTwoSubmatrix M (R.part i.castSucc) (R.part i.succ) C := by
  intro hcross
  rcases hcross with
    ⟨r, hr, s, hs, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  have hLast : R.last i.castSucc ∈ R.part i.castSucc := R.last_mem i.castSucc
  have hFirst : R.first i.succ ∈ R.part i.succ := R.first_mem i.succ
  rcases (not_zoneMixed_iff_vertical_or_horizontal M (R.part i.castSucc) C).mp
      hLzone with hLv | hLh
  · rcases (not_zoneMixed_iff_vertical_or_horizontal M (R.part i.succ) C).mp
      hRzone with hRv | hRh
    · rcases (not_rowCutMixed_iff_cutVertical_or_cutHorizontal M R C i).mp
        hcut with hcutv | hcuth
      · have hcol₁ : M r c₁ = M s c₁ := by
          calc
            M r c₁ = M (R.last i.castSucc) c₁ := hLv hr hLast hc₁
            _ = M (R.first i.succ) c₁ := hcutv hc₁
            _ = M s c₁ := (hRv hs hFirst hc₁).symm
        have hcol₂ : M r c₂ = M s c₂ := by
          calc
            M r c₂ = M (R.last i.castSucc) c₂ := hLv hr hLast hc₂
            _ = M (R.first i.succ) c₂ := hcutv hc₂
            _ = M s c₂ := (hRv hs hFirst hc₂).symm
        exact false_of_or_ne_of_eqs hvert hcol₁ hcol₂
      · have hrconst : M r c₁ = M r c₂ := by
          calc
            M r c₁ = M (R.last i.castSucc) c₁ := hLv hr hLast hc₁
            _ = M (R.last i.castSucc) c₂ := hcuth.1 hc₁ hc₂
            _ = M r c₂ := (hLv hr hLast hc₂).symm
        have hsconst : M s c₁ = M s c₂ := by
          calc
            M s c₁ = M (R.first i.succ) c₁ := hRv hs hFirst hc₁
            _ = M (R.first i.succ) c₂ := hcuth.2 hc₁ hc₂
            _ = M s c₂ := (hRv hs hFirst hc₂).symm
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
    · rcases (not_rowCutMixed_iff_cutVertical_or_cutHorizontal M R C i).mp
        hcut with hcutv | hcuth
      · have hrconst : M r c₁ = M r c₂ := by
          calc
            M r c₁ = M (R.last i.castSucc) c₁ := hLv hr hLast hc₁
            _ = M (R.first i.succ) c₁ := hcutv hc₁
            _ = M (R.first i.succ) c₂ := hRh hFirst hc₁ hc₂
            _ = M (R.last i.castSucc) c₂ := (hcutv hc₂).symm
            _ = M r c₂ := (hLv hr hLast hc₂).symm
        have hsconst : M s c₁ = M s c₂ := hRh hs hc₁ hc₂
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
      · have hrconst : M r c₁ = M r c₂ := by
          calc
            M r c₁ = M (R.last i.castSucc) c₁ := hLv hr hLast hc₁
            _ = M (R.last i.castSucc) c₂ := hcuth.1 hc₁ hc₂
            _ = M r c₂ := (hLv hr hLast hc₂).symm
        have hsconst : M s c₁ = M s c₂ := hRh hs hc₁ hc₂
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
  · rcases (not_zoneMixed_iff_vertical_or_horizontal M (R.part i.succ) C).mp
      hRzone with hRv | hRh
    · rcases (not_rowCutMixed_iff_cutVertical_or_cutHorizontal M R C i).mp
        hcut with hcutv | hcuth
      · have hrconst : M r c₁ = M r c₂ := hLh hr hc₁ hc₂
        have hsconst : M s c₁ = M s c₂ := by
          calc
            M s c₁ = M (R.first i.succ) c₁ := hRv hs hFirst hc₁
            _ = M (R.last i.castSucc) c₁ := (hcutv hc₁).symm
            _ = M (R.last i.castSucc) c₂ := hLh hLast hc₁ hc₂
            _ = M (R.first i.succ) c₂ := hcutv hc₂
            _ = M s c₂ := (hRv hs hFirst hc₂).symm
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
      · have hrconst : M r c₁ = M r c₂ := hLh hr hc₁ hc₂
        have hsconst : M s c₁ = M s c₂ := by
          calc
            M s c₁ = M (R.first i.succ) c₁ := hRv hs hFirst hc₁
            _ = M (R.first i.succ) c₂ := hcuth.2 hc₁ hc₂
            _ = M s c₂ := (hRv hs hFirst hc₂).symm
        exact false_of_or_ne_of_eqs hhoriz hrconst hsconst
    · have hrconst : M r c₁ = M r c₂ := hLh hr hc₁ hc₂
      have hsconst : M s c₁ = M s c₂ := hRh hs hc₁ hc₂
      exact false_of_or_ne_of_eqs hhoriz hrconst hsconst

/-- Boundary localization for consecutive column parts, dual to
`not_rowCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut`. -/
theorem not_colCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (C : Division m (k + 1)) (j : Fin k)
    (hLzone : ¬ ZoneMixed M R (C.part j.castSucc))
    (hRzone : ¬ ZoneMixed M R (C.part j.succ))
    (hcut : ¬ ColCutMixed M R C j) :
    ¬ ColCrossingTwoByTwoSubmatrix M R (C.part j.castSucc) (C.part j.succ) := by
  intro hcross
  rcases hcross with
    ⟨r₁, hr₁, r₂, hr₂, c, hc, d, hd, hvert, hhoriz⟩
  have hLast : C.last j.castSucc ∈ C.part j.castSucc := C.last_mem j.castSucc
  have hFirst : C.first j.succ ∈ C.part j.succ := C.first_mem j.succ
  rcases (not_zoneMixed_iff_vertical_or_horizontal M R (C.part j.castSucc)).mp
      hLzone with hLv | hLh
  · rcases (not_zoneMixed_iff_vertical_or_horizontal M R (C.part j.succ)).mp
      hRzone with hRv | hRh
    · have hcvert : M r₁ c = M r₂ c := hLv hr₁ hr₂ hc
      have hdvert : M r₁ d = M r₂ d := hRv hr₁ hr₂ hd
      exact false_of_or_ne_of_eqs hvert hcvert hdvert
    · rcases (not_colCutMixed_iff_cutVertical_or_cutHorizontal M R C j).mp
        hcut with hcutv | hcuth
      · have hcvert : M r₁ c = M r₂ c := hLv hr₁ hr₂ hc
        have hdvert : M r₁ d = M r₂ d := by
          calc
            M r₁ d = M r₁ (C.first j.succ) := (hRh hr₁ hFirst hd).symm
            _ = M r₂ (C.first j.succ) := hcutv.2 hr₁ hr₂
            _ = M r₂ d := hRh hr₂ hFirst hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
      · have hcvert : M r₁ c = M r₂ c := hLv hr₁ hr₂ hc
        have hdvert : M r₁ d = M r₂ d := by
          calc
            M r₁ d = M r₁ (C.first j.succ) := (hRh hr₁ hFirst hd).symm
            _ = M r₁ (C.last j.castSucc) := (hcuth hr₁).symm
            _ = M r₂ (C.last j.castSucc) := hLv hr₁ hr₂ hLast
            _ = M r₂ (C.first j.succ) := hcuth hr₂
            _ = M r₂ d := hRh hr₂ hFirst hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
  · rcases (not_zoneMixed_iff_vertical_or_horizontal M R (C.part j.succ)).mp
      hRzone with hRv | hRh
    · rcases (not_colCutMixed_iff_cutVertical_or_cutHorizontal M R C j).mp
        hcut with hcutv | hcuth
      · have hcvert : M r₁ c = M r₂ c := by
          calc
            M r₁ c = M r₁ (C.last j.castSucc) := hLh hr₁ hc hLast
            _ = M r₂ (C.last j.castSucc) := hcutv.1 hr₁ hr₂
            _ = M r₂ c := (hLh hr₂ hc hLast).symm
        have hdvert : M r₁ d = M r₂ d := hRv hr₁ hr₂ hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
      · have hcvert : M r₁ c = M r₂ c := by
          calc
            M r₁ c = M r₁ (C.last j.castSucc) := hLh hr₁ hc hLast
            _ = M r₁ (C.first j.succ) := hcuth hr₁
            _ = M r₂ (C.first j.succ) := hRv hr₁ hr₂ hFirst
            _ = M r₂ (C.last j.castSucc) := (hcuth hr₂).symm
            _ = M r₂ c := (hLh hr₂ hc hLast).symm
        have hdvert : M r₁ d = M r₂ d := hRv hr₁ hr₂ hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
    · rcases (not_colCutMixed_iff_cutVertical_or_cutHorizontal M R C j).mp
        hcut with hcutv | hcuth
      · have hcvert : M r₁ c = M r₂ c := by
          calc
            M r₁ c = M r₁ (C.last j.castSucc) := hLh hr₁ hc hLast
            _ = M r₂ (C.last j.castSucc) := hcutv.1 hr₁ hr₂
            _ = M r₂ c := (hLh hr₂ hc hLast).symm
        have hdvert : M r₁ d = M r₂ d := by
          calc
            M r₁ d = M r₁ (C.first j.succ) := (hRh hr₁ hFirst hd).symm
            _ = M r₂ (C.first j.succ) := hcutv.2 hr₁ hr₂
            _ = M r₂ d := hRh hr₂ hFirst hd
        exact false_of_or_ne_of_eqs hvert hcvert hdvert
      · have hr₁const : M r₁ c = M r₁ d := by
          calc
            M r₁ c = M r₁ (C.last j.castSucc) := hLh hr₁ hc hLast
            _ = M r₁ (C.first j.succ) := hcuth hr₁
            _ = M r₁ d := hRh hr₁ hFirst hd
        have hr₂const : M r₂ c = M r₂ d := by
          calc
            M r₂ c = M r₂ (C.last j.castSucc) := hLh hr₂ hc hLast
            _ = M r₂ (C.first j.succ) := hcuth hr₂
            _ = M r₂ d := hRh hr₂ hFirst hd
        exact false_of_or_ne_of_eqs hhoriz hr₁const hr₂const

/-- If adjacent row zones are not mixed, a crossing mixed `2 x 2` submatrix
witness forces the boundary row cut to be mixed. -/
theorem rowCutMixed_of_crossingTwoByTwoSubmatrix_of_not_mixed_zones {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (R : Division n (k + 1)) {C : Finset (Fin m)} (i : Fin k)
    (hLzone : ¬ ZoneMixed M (R.part i.castSucc) C)
    (hRzone : ¬ ZoneMixed M (R.part i.succ) C)
    (hcross :
      RowCrossingTwoByTwoSubmatrix M (R.part i.castSucc) (R.part i.succ) C) :
    RowCutMixed M R C i := by
  classical
  by_contra hcut
  exact not_rowCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut
    (M := M) R i hLzone hRzone hcut hcross

/-- If adjacent column zones are not mixed, a crossing mixed `2 x 2` submatrix
witness forces the boundary column cut to be mixed. -/
theorem colCutMixed_of_crossingTwoByTwoSubmatrix_of_not_mixed_zones {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (C : Division m (k + 1)) (j : Fin k)
    (hLzone : ¬ ZoneMixed M R (C.part j.castSucc))
    (hRzone : ¬ ZoneMixed M R (C.part j.succ))
    (hcross :
      ColCrossingTwoByTwoSubmatrix M R (C.part j.castSucc) (C.part j.succ)) :
    ColCutMixed M R C j := by
  classical
  by_contra hcut
  exact not_colCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut
    (M := M) C j hLzone hRzone hcut hcross

/-- Row form of the paper's Lemma 12: fusing two consecutive row zones that
are both nonmixed preserves nonmixedness whenever the boundary cut is also
nonmixed. -/
theorem not_zoneMixed_union_consecutive_rows_of_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (R : Division n (k + 1)) {C : Finset (Fin m)} (i : Fin k)
    (hLzone : ¬ ZoneMixed M (R.part i.castSucc) C)
    (hRzone : ¬ ZoneMixed M (R.part i.succ) C)
    (hcut : ¬ RowCutMixed M R C i) :
    ¬ ZoneMixed M (R.part i.castSucc ∪ R.part i.succ) C :=
  not_zoneMixed_union_rows_of_no_crossing hLzone hRzone
    (not_rowCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut
      (M := M) R i hLzone hRzone hcut)

/-- Column form of the paper's Lemma 12. -/
theorem not_zoneMixed_union_consecutive_cols_of_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (C : Division m (k + 1)) (j : Fin k)
    (hLzone : ¬ ZoneMixed M R (C.part j.castSucc))
    (hRzone : ¬ ZoneMixed M R (C.part j.succ))
    (hcut : ¬ ColCutMixed M R C j) :
    ¬ ZoneMixed M R (C.part j.castSucc ∪ C.part j.succ) :=
  not_zoneMixed_union_cols_of_no_crossing hLzone hRzone
    (not_colCrossingTwoByTwoSubmatrix_of_not_mixed_zones_not_mixed_cut
      (M := M) C j hLzone hRzone hcut)

/-- Lemma 12, local exact row-fusion form: the newly merged row part is
nonmixed on `C` whenever the two old adjacent row zones and their boundary cut
are nonmixed. -/
theorem not_zoneMixed_fused_row_part_of_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : Division n (k + 2)} {E : Division n (k + 1)}
    {C : Finset (Fin m)} {i : Fin (k + 1)}
    (hfuse : Division.IsFusionAt D E i)
    (hLzone : ¬ ZoneMixed M (D.part i.castSucc) C)
    (hRzone : ¬ ZoneMixed M (D.part i.succ) C)
    (hcut : ¬ RowCutMixed M D C i) :
    ¬ ZoneMixed M (E.part i) C := by
  rw [hfuse i, Division.fusePart_self]
  exact not_zoneMixed_union_consecutive_rows_of_not_mixed_cut
    (M := M) D i hLzone hRzone hcut

/-- Contrapositive package of the exact row-fusion form of Lemma 12. -/
theorem rowFusion_old_zone_or_cut_mixed_of_fused_row_part_mixed {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : Division n (k + 2)} {E : Division n (k + 1)}
    {C : Finset (Fin m)} {i : Fin (k + 1)}
    (hfuse : Division.IsFusionAt D E i)
    (hmix : ZoneMixed M (E.part i) C) :
    ZoneMixed M (D.part i.castSucc) C ∨
      ZoneMixed M (D.part i.succ) C ∨ RowCutMixed M D C i := by
  classical
  by_cases hL : ZoneMixed M (D.part i.castSucc) C
  · exact Or.inl hL
  · by_cases hR : ZoneMixed M (D.part i.succ) C
    · exact Or.inr (Or.inl hR)
    · by_cases hcut : RowCutMixed M D C i
      · exact Or.inr (Or.inr hcut)
      · exact False.elim
          (not_zoneMixed_fused_row_part_of_not_mixed_cut
            (M := M) hfuse hL hR hcut hmix)

/-- Lemma 12, local exact column-fusion form. -/
theorem not_zoneMixed_fused_col_part_of_not_mixed_cut {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {D : Division m (k + 2)} {E : Division m (k + 1)}
    {j : Fin (k + 1)}
    (hfuse : Division.IsFusionAt D E j)
    (hLzone : ¬ ZoneMixed M R (D.part j.castSucc))
    (hRzone : ¬ ZoneMixed M R (D.part j.succ))
    (hcut : ¬ ColCutMixed M R D j) :
    ¬ ZoneMixed M R (E.part j) := by
  rw [hfuse j, Division.fusePart_self]
  exact not_zoneMixed_union_consecutive_cols_of_not_mixed_cut
    (M := M) D j hLzone hRzone hcut

/-- Contrapositive package of the exact column-fusion form of Lemma 12. -/
theorem colFusion_old_zone_or_cut_mixed_of_fused_col_part_mixed {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {D : Division m (k + 2)} {E : Division m (k + 1)}
    {j : Fin (k + 1)}
    (hfuse : Division.IsFusionAt D E j)
    (hmix : ZoneMixed M R (E.part j)) :
    ZoneMixed M R (D.part j.castSucc) ∨
      ZoneMixed M R (D.part j.succ) ∨ ColCutMixed M R D j := by
  classical
  by_cases hL : ZoneMixed M R (D.part j.castSucc)
  · exact Or.inl hL
  · by_cases hR : ZoneMixed M R (D.part j.succ)
    · exact Or.inr (Or.inl hR)
    · by_cases hcut : ColCutMixed M R D j
      · exact Or.inr (Or.inr hcut)
      · exact False.elim
          (not_zoneMixed_fused_col_part_of_not_mixed_cut
            (M := M) hfuse hL hR hcut hmix)

theorem rowCutMixed_of_fuse_rowCutMixed_of_lt {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : Division n (k + 2)) {C : Finset (Fin m)}
    {i : Fin (k + 1)} {j : Fin k}
    (hji : j.castSucc < i)
    (hmix : RowCutMixed M (D.fuse i) C j) :
    RowCutMixed M D C j.castSucc := by
  have hleftPart :
      (D.fuse i).part j.castSucc = D.part j.castSucc.castSucc :=
    Division.fuse_part_of_lt D hji
  have hleftLast :
      (D.fuse i).last j.castSucc = D.last j.castSucc.castSucc := by
    simp [Division.last, hleftPart]
  have hrightFirst :
      (D.fuse i).first j.succ = D.first j.castSucc.succ := by
    by_cases hs : j.succ = i
    · subst i
      simp [Division.first_fuse_self]
    · have hslt : j.succ < i := by
        apply Fin.mk_lt_mk.mpr
        have hlt : j.1 < i.1 := Fin.mk_lt_mk.mp hji
        have hne : j.1 + 1 ≠ i.1 := by
          intro hval
          exact hs (Fin.ext hval)
        omega
      have hpart : (D.fuse i).part j.succ = D.part j.succ.castSucc :=
        Division.fuse_part_of_lt D hslt
      simp [Division.first, hpart]
  constructor
  · intro hv
    exact hmix.1 (by
      intro c hc
      rw [hleftLast, hrightFirst]
      exact hv hc)
  · intro hh
    exact hmix.2 (by
      constructor
      · intro c₁ c₂ hc₁ hc₂
        rw [hleftLast]
        exact hh.1 hc₁ hc₂
      · intro c₁ c₂ hc₁ hc₂
        rw [hrightFirst]
        exact hh.2 hc₁ hc₂)

theorem rowCutMixed_of_fuse_rowCutMixed_of_ge {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : Division n (k + 2)) {C : Finset (Fin m)}
    {i : Fin (k + 1)} {j : Fin k}
    (hij : i ≤ j.castSucc)
    (hmix : RowCutMixed M (D.fuse i) C j) :
    RowCutMixed M D C j.succ := by
  have hleftLast :
      (D.fuse i).last j.castSucc = D.last j.succ.castSucc := by
    by_cases hs : j.castSucc = i
    · subst i
      simp [Division.last_fuse_self]
    · have hgt : i < j.castSucc := lt_of_le_of_ne hij (Ne.symm hs)
      have hpart : (D.fuse i).part j.castSucc = D.part j.castSucc.succ :=
        Division.fuse_part_of_gt D hgt
      simp [Division.last, hpart]
  have hrightPart :
      (D.fuse i).part j.succ = D.part j.succ.succ := by
    have hgt : i < j.succ := by
      apply lt_of_le_of_lt hij
      exact Fin.castSucc_lt_succ
    exact Division.fuse_part_of_gt D hgt
  have hrightFirst :
      (D.fuse i).first j.succ = D.first j.succ.succ := by
    simp [Division.first, hrightPart]
  constructor
  · intro hv
    exact hmix.1 (by
      intro c hc
      rw [hleftLast, hrightFirst]
      exact hv hc)
  · intro hh
    exact hmix.2 (by
      constructor
      · intro c₁ c₂ hc₁ hc₂
        rw [hleftLast]
        exact hh.1 hc₁ hc₂
      · intro c₁ c₂ hc₁ hc₂
        rw [hrightFirst]
        exact hh.2 hc₁ hc₂)

theorem colCutMixed_of_fuse_colCutMixed_of_lt {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (D : Division m (k + 2))
    {i : Fin (k + 1)} {j : Fin k}
    (hji : j.castSucc < i)
    (hmix : ColCutMixed M R (D.fuse i) j) :
    ColCutMixed M R D j.castSucc := by
  have hleftPart :
      (D.fuse i).part j.castSucc = D.part j.castSucc.castSucc :=
    Division.fuse_part_of_lt D hji
  have hleftLast :
      (D.fuse i).last j.castSucc = D.last j.castSucc.castSucc := by
    simp [Division.last, hleftPart]
  have hrightFirst :
      (D.fuse i).first j.succ = D.first j.castSucc.succ := by
    by_cases hs : j.succ = i
    · subst i
      simp [Division.first_fuse_self]
    · have hslt : j.succ < i := by
        apply Fin.mk_lt_mk.mpr
        have hlt : j.1 < i.1 := Fin.mk_lt_mk.mp hji
        have hne : j.1 + 1 ≠ i.1 := by
          intro hval
          exact hs (Fin.ext hval)
        omega
      have hpart : (D.fuse i).part j.succ = D.part j.succ.castSucc :=
        Division.fuse_part_of_lt D hslt
      simp [Division.first, hpart]
  constructor
  · intro hv
    exact hmix.1 (by
      constructor
      · intro r₁ r₂ hr₁ hr₂
        rw [hleftLast]
        exact hv.1 hr₁ hr₂
      · intro r₁ r₂ hr₁ hr₂
        rw [hrightFirst]
        exact hv.2 hr₁ hr₂)
  · intro hh
    exact hmix.2 (by
      intro r hr
      rw [hleftLast, hrightFirst]
      exact hh hr)

theorem colCutMixed_of_fuse_colCutMixed_of_ge {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (D : Division m (k + 2))
    {i : Fin (k + 1)} {j : Fin k}
    (hij : i ≤ j.castSucc)
    (hmix : ColCutMixed M R (D.fuse i) j) :
    ColCutMixed M R D j.succ := by
  have hleftLast :
      (D.fuse i).last j.castSucc = D.last j.succ.castSucc := by
    by_cases hs : j.castSucc = i
    · subst i
      simp [Division.last_fuse_self]
    · have hgt : i < j.castSucc := lt_of_le_of_ne hij (Ne.symm hs)
      have hpart : (D.fuse i).part j.castSucc = D.part j.castSucc.succ :=
        Division.fuse_part_of_gt D hgt
      simp [Division.last, hpart]
  have hrightPart :
      (D.fuse i).part j.succ = D.part j.succ.succ := by
    have hgt : i < j.succ := by
      apply lt_of_le_of_lt hij
      exact Fin.castSucc_lt_succ
    exact Division.fuse_part_of_gt D hgt
  have hrightFirst :
      (D.fuse i).first j.succ = D.first j.succ.succ := by
    simp [Division.first, hrightPart]
  constructor
  · intro hv
    exact hmix.1 (by
      constructor
      · intro r₁ r₂ hr₁ hr₂
        rw [hleftLast]
        exact hv.1 hr₁ hr₂
      · intro r₁ r₂ hr₁ hr₂
        rw [hrightFirst]
        exact hv.2 hr₁ hr₂)
  · intro hh
    exact hmix.2 (by
      intro r hr
      rw [hleftLast, hrightFirst]
      exact hh hr)

/-- The old mixed item charged by a mixed item after a row fusion.  Zones away
from the fused pair keep their old zone index, cuts away from the fused
boundary keep their old cut index, and the new fused zone is charged to one of
the two old zones or to the disappearing boundary cut. -/
noncomputable def rowFuseItemMap {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : Division n (k + 2)) (C : Finset (Fin m)) (i : Fin (k + 1)) :
    Sum (Fin (k + 1)) (Fin k) → Sum (Fin (k + 2)) (Fin (k + 1)) := by
  classical
  intro x
  rcases x with j | j
  · exact
      if hj : j = i then
        if ZoneMixed M (D.part i.castSucc) C then
          Sum.inl i.castSucc
        else if ZoneMixed M (D.part i.succ) C then
          Sum.inl i.succ
        else
          Sum.inr i
      else if hji : j < i then
        Sum.inl j.castSucc
      else
        Sum.inl j.succ
  · exact
      if hji : j.castSucc < i then
        Sum.inr j.castSucc
      else
        Sum.inr j.succ

/-- A left inverse for `rowFuseItemMap`.  Old zones are projected by the
fusion index map.  The deleted old boundary cut is sent to the new fused zone. -/
def rowFuseItemPreimage {k : ℕ} (i : Fin (k + 1)) :
    Sum (Fin (k + 2)) (Fin (k + 1)) → Sum (Fin (k + 1)) (Fin k)
  | Sum.inl a => Sum.inl (Division.fuseIndex i a)
  | Sum.inr b =>
      if hlt : b < i then
        Sum.inr ⟨b.1, by
          have hb : b.1 < i.1 := Fin.mk_lt_mk.mp hlt
          omega⟩
      else if hb : b = i then
        Sum.inl i
      else
        Sum.inr ⟨b.1 - 1, by
          have hle : i ≤ b := le_of_not_gt hlt
          have hne : i ≠ b := by exact Ne.symm hb
          have hlt' : i < b := lt_of_le_of_ne hle hne
          have hbpos : 0 < b.1 := by
            have hi_lt : i.1 < b.1 := Fin.mk_lt_mk.mp hlt'
            omega
          omega⟩

theorem rowFuseItemPreimage_map {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : Division n (k + 2)) (C : Finset (Fin m)) (i : Fin (k + 1))
    (x : Sum (Fin (k + 1)) (Fin k)) :
    rowFuseItemPreimage i (rowFuseItemMap M D C i x) = x := by
  classical
  cases x with
  | inl j =>
      by_cases hj : j = i
      · subst j
        by_cases hL : ZoneMixed M (D.part i.castSucc) C
        · simp [rowFuseItemMap, rowFuseItemPreimage, hL, Division.fuseIndex_eq_self_iff]
        · by_cases hR : ZoneMixed M (D.part i.succ) C
          · simp [rowFuseItemMap, rowFuseItemPreimage, hL, hR,
              Division.fuseIndex_eq_self_iff]
          · simp [rowFuseItemMap, rowFuseItemPreimage, hL, hR]
      · by_cases hji : j < i
        · have hidx : Division.fuseIndex i j.castSucc = j :=
            (Division.fuseIndex_eq_of_lt_iff hji j.castSucc).mpr rfl
          simp [rowFuseItemMap, rowFuseItemPreimage, hj, hji, hidx]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj)
          have hidx : Division.fuseIndex i j.succ = j :=
            (Division.fuseIndex_eq_of_gt_iff hij j.succ).mpr rfl
          simp [rowFuseItemMap, rowFuseItemPreimage, hj, hji, hidx]
  | inr j =>
      by_cases hji : j.castSucc < i
      · have hlt : j.castSucc < i := hji
        simp [rowFuseItemMap, rowFuseItemPreimage, hji]
      · have hnot : ¬ j.succ < i := by
          intro hlt
          exact hji (lt_trans Fin.castSucc_lt_succ hlt)
        have hne : ¬ j.succ = i := by
          intro h
          subst i
          exact hji Fin.castSucc_lt_succ
        simp [rowFuseItemMap, rowFuseItemPreimage, hji, hnot, hne]

theorem rowFuseItemMap_injective {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : Division n (k + 2)) (C : Finset (Fin m)) (i : Fin (k + 1)) :
    Function.Injective (rowFuseItemMap M D C i) := by
  intro x y hxy
  have h := congrArg (rowFuseItemPreimage i) hxy
  simpa [rowFuseItemPreimage_map M D C i x,
    rowFuseItemPreimage_map M D C i y] using h

theorem rowFuseItemMap_mem {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : Division n (k + 2)) {C : Finset (Fin m)} (i : Fin (k + 1))
    {x : Sum (Fin (k + 1)) (Fin k)}
    (hx : x ∈ rowMixedItems M (D.fuse i) C) :
    rowFuseItemMap M D C i x ∈ rowMixedItems M D C := by
  classical
  cases x with
  | inl j =>
      have hmix : ZoneMixed M ((D.fuse i).part j) C := by
        simpa using hx
      by_cases hj : j = i
      · subst j
        by_cases hL : ZoneMixed M (D.part i.castSucc) C
        · simp [rowFuseItemMap, hL]
        · by_cases hR : ZoneMixed M (D.part i.succ) C
          · simp [rowFuseItemMap, hL, hR]
          · have hcut : RowCutMixed M D C i := by
              rcases rowFusion_old_zone_or_cut_mixed_of_fused_row_part_mixed
                  (M := M) (D := D) (E := D.fuse i)
                  (C := C) (i := i) (Division.isFusionAt_fuse D i) hmix with h | h | h
              · exact False.elim (hL h)
              · exact False.elim (hR h)
              · exact h
            simp [rowFuseItemMap, hL, hR, hcut]
      · by_cases hji : j < i
        · have hpart : (D.fuse i).part j = D.part j.castSucc :=
            Division.fuse_part_of_lt D hji
          have hold : ZoneMixed M (D.part j.castSucc) C := by
            simpa [hpart] using hmix
          simp [rowFuseItemMap, hj, hji, hold]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj)
          have hpart : (D.fuse i).part j = D.part j.succ :=
            Division.fuse_part_of_gt D hij
          have hold : ZoneMixed M (D.part j.succ) C := by
            simpa [hpart] using hmix
          simp [rowFuseItemMap, hj, hji, hold]
  | inr j =>
      have hmix : RowCutMixed M (D.fuse i) C j := by
        simpa using hx
      by_cases hji : j.castSucc < i
      · have hold : RowCutMixed M D C j.castSucc :=
          rowCutMixed_of_fuse_rowCutMixed_of_lt D hji hmix
        simp [rowFuseItemMap, hji, hold]
      · have hij : i ≤ j.castSucc := le_of_not_gt hji
        have hold : RowCutMixed M D C j.succ :=
          rowCutMixed_of_fuse_rowCutMixed_of_ge D hij hmix
        simp [rowFuseItemMap, hji, hold]

/-- Cardinal form of Lemma 12 for row fusions: fusing two consecutive row
parts does not increase the mixed value of any fixed column interval. -/
theorem rowMixedValue_fuse_le {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : Division n (k + 2)) (C : Finset (Fin m)) (i : Fin (k + 1)) :
    rowMixedValue M (D.fuse i) C ≤ rowMixedValue M D C := by
  classical
  rw [← rowMixedItems_card M (D.fuse i) C, ← rowMixedItems_card M D C]
  exact Finset.card_le_card_of_injOn
    (rowFuseItemMap M D C i)
    (fun x hx => rowFuseItemMap_mem D i hx)
    (fun x _hx y _hy hxy => rowFuseItemMap_injective M D C i hxy)

/-- Column-fusion analogue of `rowFuseItemMap`. -/
noncomputable def colFuseItemMap {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (D : Division m (k + 2)) (i : Fin (k + 1)) :
    Sum (Fin (k + 1)) (Fin k) → Sum (Fin (k + 2)) (Fin (k + 1)) := by
  classical
  intro x
  rcases x with j | j
  · exact
      if hj : j = i then
        if ZoneMixed M R (D.part i.castSucc) then
          Sum.inl i.castSucc
        else if ZoneMixed M R (D.part i.succ) then
          Sum.inl i.succ
        else
          Sum.inr i
      else if hji : j < i then
        Sum.inl j.castSucc
      else
        Sum.inl j.succ
  · exact
      if hji : j.castSucc < i then
        Sum.inr j.castSucc
      else
        Sum.inr j.succ

theorem colFuseItemPreimage_map {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (D : Division m (k + 2)) (i : Fin (k + 1))
    (x : Sum (Fin (k + 1)) (Fin k)) :
    rowFuseItemPreimage i (colFuseItemMap M R D i x) = x := by
  classical
  cases x with
  | inl j =>
      by_cases hj : j = i
      · subst j
        by_cases hL : ZoneMixed M R (D.part i.castSucc)
        · simp [colFuseItemMap, rowFuseItemPreimage, hL, Division.fuseIndex_eq_self_iff]
        · by_cases hR : ZoneMixed M R (D.part i.succ)
          · simp [colFuseItemMap, rowFuseItemPreimage, hL, hR,
              Division.fuseIndex_eq_self_iff]
          · simp [colFuseItemMap, rowFuseItemPreimage, hL, hR]
      · by_cases hji : j < i
        · have hidx : Division.fuseIndex i j.castSucc = j :=
            (Division.fuseIndex_eq_of_lt_iff hji j.castSucc).mpr rfl
          simp [colFuseItemMap, rowFuseItemPreimage, hj, hji, hidx]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj)
          have hidx : Division.fuseIndex i j.succ = j :=
            (Division.fuseIndex_eq_of_gt_iff hij j.succ).mpr rfl
          simp [colFuseItemMap, rowFuseItemPreimage, hj, hji, hidx]
  | inr j =>
      by_cases hji : j.castSucc < i
      · have hlt : j.castSucc < i := hji
        simp [colFuseItemMap, rowFuseItemPreimage, hji]
      · have hnot : ¬ j.succ < i := by
          intro hlt
          exact hji (lt_trans Fin.castSucc_lt_succ hlt)
        have hne : ¬ j.succ = i := by
          intro h
          subst i
          exact hji Fin.castSucc_lt_succ
        simp [colFuseItemMap, rowFuseItemPreimage, hji, hnot, hne]

theorem colFuseItemMap_injective {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (D : Division m (k + 2)) (i : Fin (k + 1)) :
    Function.Injective (colFuseItemMap M R D i) := by
  intro x y hxy
  have h := congrArg (rowFuseItemPreimage i) hxy
  simpa [colFuseItemPreimage_map M R D i x,
    colFuseItemPreimage_map M R D i y] using h

theorem colFuseItemMap_mem {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} (D : Division m (k + 2)) (i : Fin (k + 1))
    {x : Sum (Fin (k + 1)) (Fin k)}
    (hx : x ∈ colMixedItems M R (D.fuse i)) :
    colFuseItemMap M R D i x ∈ colMixedItems M R D := by
  classical
  cases x with
  | inl j =>
      have hmix : ZoneMixed M R ((D.fuse i).part j) := by
        simpa using hx
      by_cases hj : j = i
      · subst j
        by_cases hL : ZoneMixed M R (D.part i.castSucc)
        · simp [colFuseItemMap, hL]
        · by_cases hR : ZoneMixed M R (D.part i.succ)
          · simp [colFuseItemMap, hL, hR]
          · have hcut : ColCutMixed M R D i := by
              rcases colFusion_old_zone_or_cut_mixed_of_fused_col_part_mixed
                  (M := M) (R := R) (D := D) (E := D.fuse i)
                  (j := i) (Division.isFusionAt_fuse D i) hmix with h | h | h
              · exact False.elim (hL h)
              · exact False.elim (hR h)
              · exact h
            simp [colFuseItemMap, hL, hR, hcut]
      · by_cases hji : j < i
        · have hpart : (D.fuse i).part j = D.part j.castSucc :=
            Division.fuse_part_of_lt D hji
          have hold : ZoneMixed M R (D.part j.castSucc) := by
            simpa [hpart] using hmix
          simp [colFuseItemMap, hj, hji, hold]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj)
          have hpart : (D.fuse i).part j = D.part j.succ :=
            Division.fuse_part_of_gt D hij
          have hold : ZoneMixed M R (D.part j.succ) := by
            simpa [hpart] using hmix
          simp [colFuseItemMap, hj, hji, hold]
  | inr j =>
      have hmix : ColCutMixed M R (D.fuse i) j := by
        simpa using hx
      by_cases hji : j.castSucc < i
      · have hold : ColCutMixed M R D j.castSucc :=
          colCutMixed_of_fuse_colCutMixed_of_lt D hji hmix
        simp [colFuseItemMap, hji, hold]
      · have hij : i ≤ j.castSucc := le_of_not_gt hji
        have hold : ColCutMixed M R D j.succ :=
          colCutMixed_of_fuse_colCutMixed_of_ge D hij hmix
        simp [colFuseItemMap, hji, hold]

/-- Cardinal form of Lemma 12 for column fusions. -/
theorem colMixedValue_fuse_le {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (R : Finset (Fin n)) (D : Division m (k + 2)) (i : Fin (k + 1)) :
    colMixedValue M R (D.fuse i) ≤ colMixedValue M R D := by
  classical
  rw [← colMixedItems_card M R (D.fuse i), ← colMixedItems_card M R D]
  exact Finset.card_le_card_of_injOn
    (colFuseItemMap M R D i)
    (fun x hx => colFuseItemMap_mem D i hx)
    (fun x _hx y _hy hxy => colFuseItemMap_injective M R D i hxy)

end Matrix
end TwinWidth

/- ===== end Matrix/Fusion.lean ===== -/

/- ===== begin Matrix/GridMinor.lean ===== -/

/-
# Grid minors of Boolean matrices

This file defines the grid-minor notion used in the Marcus-Tardos ingredient of
the twin-width grid theorem.  A `t`-grid minor in a Boolean matrix is a pair of
`t`-divisions of rows and columns such that every zone contains a `true` entry.
-/

namespace TwinWidth
namespace Matrix

/-- The set of `true` entries of a Boolean matrix. -/
noncomputable def oneEntries {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    Finset (Fin n × Fin m) :=
  by
    classical
    exact Finset.univ.filter fun p : Fin n × Fin m => M p.1 p.2 = true

/-- A cell of a divided Boolean matrix contains a `true` entry. -/
def CellHasOne {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∃ r ∈ R.part i, ∃ c ∈ C.part j, M r c = true

/-- A Boolean matrix has a `t`-grid minor if there are row and column
`t`-divisions such that every zone contains a `true` entry.

The `t = 0` convention is vacuous, matching the empty family of zones.
-/
def HasGridMinor {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool) (t : ℕ) : Prop :=
  t = 0 ∨
    ∃ R : Division n t, ∃ C : Division m t,
      ∀ i j : Fin t, CellHasOne M R C i j

@[simp] theorem hasGridMinor_zero {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    HasGridMinor M 0 :=
  Or.inl rfl

theorem mem_oneEntries_iff {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (p : Fin n × Fin m) :
    p ∈ oneEntries M ↔ M p.1 p.2 = true := by
  classical
  simp [oneEntries]

/-- The one-part division of a nonempty finite interval. -/
def oneDivision (n : ℕ) (hn : 0 < n) : Division n 1 where
  part := fun _ => Finset.univ
  part_nonempty := by
    intro _
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  part_disjoint := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  part_cover := by
    intro x
    exact ⟨0, Finset.mem_univ x⟩
  part_convex := by
    intro _ _ _ _ _ _ _ _
    exact Finset.mem_univ _
  part_ordered := by
    intro i j hij
    exact (not_lt_of_ge (Subsingleton.elim i j ▸ le_rfl) hij).elim

/-- A nonempty Boolean matrix with at least one true entry has a `1`-grid
minor. -/
theorem hasGridMinor_one_of_true_entry {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    {r : Fin n} {c : Fin m} (h : M r c = true) :
    HasGridMinor M 1 := by
  refine Or.inr ?_
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le r.1) r.2
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le c.1) c.2
  refine ⟨oneDivision n hn, oneDivision m hm, ?_⟩
  intro i j
  exact ⟨r, Finset.mem_univ r, c, Finset.mem_univ c, h⟩

/-- If the set of true entries is nonempty, then the matrix has a `1`-grid
minor. -/
theorem hasGridMinor_one_of_oneEntries_nonempty {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (h : (oneEntries M).Nonempty) :
    HasGridMinor M 1 := by
  rcases h with ⟨p, hp⟩
  exact hasGridMinor_one_of_true_entry M ((mem_oneEntries_iff M p).mp hp)

end Matrix
end TwinWidth

/- ===== end Matrix/GridMinor.lean ===== -/

/- ===== begin Matrix/MarcusTardos.lean ===== -/

/-
# Marcus-Tardos theorem

This file records the exact finite-matrix statements needed later in the
twin-width grid theorem.  Section 2 of Marcus--Tardos proves the
Füredi--Hajnal forbidden permutation matrix theorem by a block recursion; the
grid-minor density theorem used by twin-width is then a corollary.

The first part of the file formalizes the ordered-submatrix language of Section
2: containment, avoidance, permutation matrices, and the extremal function
`f(n,P)`.
-/

namespace TwinWidth
namespace Matrix

/- ## Forbidden permutation matrices -/

/-- `A` contains the pattern `P` if some order-preserving choice of rows and
columns of `A` has `true` entries wherever `P` has `true` entries.

This matches Marcus--Tardos containment: extra `true` entries in the selected
submatrix are allowed. -/
def ContainsPattern {n m k l : ℕ}
    (A : _root_.Matrix (Fin n) (Fin m) Bool)
    (P : _root_.Matrix (Fin k) (Fin l) Bool) : Prop :=
  ∃ row : Fin k ↪o Fin n, ∃ col : Fin l ↪o Fin m,
    ∀ i j, P i j = true → A (row i) (col j) = true

/-- A matrix avoids a pattern if it does not contain it as an ordered
submatrix. -/
def AvoidsPattern {n m k l : ℕ}
    (A : _root_.Matrix (Fin n) (Fin m) Bool)
    (P : _root_.Matrix (Fin k) (Fin l) Bool) : Prop :=
  ¬ ContainsPattern A P

/-- A Boolean matrix is a permutation matrix when every row has its unique
`true` entry in the column prescribed by a permutation. -/
def IsPermutationMatrix {k : ℕ} (P : _root_.Matrix (Fin k) (Fin k) Bool) : Prop :=
  ∃ π : Equiv.Perm (Fin k), ∀ i j, P i j = decide (j = π i)

/-- The permutation matrix associated with a permutation of `Fin k`. -/
def permutationMatrix {k : ℕ} (π : Equiv.Perm (Fin k)) :
    _root_.Matrix (Fin k) (Fin k) Bool :=
  fun i j => decide (j = π i)

theorem isPermutationMatrix_permutationMatrix {k : ℕ} (π : Equiv.Perm (Fin k)) :
    IsPermutationMatrix (permutationMatrix π) :=
  ⟨π, by intro i j; rfl⟩

/-- The finite set of square Boolean matrices of order `n` avoiding `P`. -/
noncomputable def avoidingMatrices {k : ℕ}
    (P : _root_.Matrix (Fin k) (Fin k) Bool) (n : ℕ) :
    Finset (_root_.Matrix (Fin n) (Fin n) Bool) :=
  by
    classical
    exact Finset.univ.filter fun A => AvoidsPattern A P

/-- The extremal function `f(n,P)`: the largest number of true entries in an
`n × n` matrix avoiding `P`. -/
noncomputable def forbiddenExtremal {k : ℕ}
    (P : _root_.Matrix (Fin k) (Fin k) Bool) (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest
      (fun q => ∃ A : _root_.Matrix (Fin n) (Fin n) Bool,
        AvoidsPattern A P ∧ (oneEntries A).card = q)
      (n * n)

/-- Every matrix has at most `n * m` true entries. -/
theorem oneEntries_card_le {n m : ℕ}
    (A : _root_.Matrix (Fin n) (Fin m) Bool) :
    (oneEntries A).card ≤ n * m := by
  classical
  calc
    (oneEntries A).card ≤ (Finset.univ : Finset (Fin n × Fin m)).card := by
      exact Finset.card_le_card (by
        intro p hp
        simp [oneEntries] at hp ⊢)
    _ = n * m := by simp [Fintype.card_prod]

theorem forbiddenExtremal_le_square {k n : ℕ}
    (P : _root_.Matrix (Fin k) (Fin k) Bool) :
    forbiddenExtremal P n ≤ n * n := by
  classical
  exact Nat.findGreatest_le
    (P := fun q => ∃ A : _root_.Matrix (Fin n) (Fin n) Bool,
      AvoidsPattern A P ∧ (oneEntries A).card = q)
    (n * n)

/-- The all-false Boolean matrix. -/
def zeroBoolMatrix (n m : ℕ) : _root_.Matrix (Fin n) (Fin m) Bool :=
  fun _ _ => false

@[simp] theorem oneEntries_zeroBoolMatrix (n m : ℕ) :
    oneEntries (zeroBoolMatrix n m) = ∅ := by
  classical
  ext p
  simp [oneEntries, zeroBoolMatrix]

/-- A nonempty permutation pattern is avoided by the all-false matrix. -/
theorem zeroBoolMatrix_avoids_permutation {n k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k)) :
    AvoidsPattern (zeroBoolMatrix n n) (permutationMatrix π) := by
  intro h
  rcases h with ⟨row, col, hcontains⟩
  let i : Fin k := ⟨0, hk⟩
  have htrue := hcontains i (π i) (by simp [permutationMatrix])
  simp [zeroBoolMatrix] at htrue

/-- The extremal value is realized by some avoiding matrix, for nonempty
permutation patterns. -/
theorem exists_forbiddenExtremal_eq {k n : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k)) :
    ∃ A : _root_.Matrix (Fin n) (Fin n) Bool,
      AvoidsPattern A (permutationMatrix π) ∧
        (oneEntries A).card = forbiddenExtremal (permutationMatrix π) n := by
  classical
  let P := fun q => ∃ A : _root_.Matrix (Fin n) (Fin n) Bool,
    AvoidsPattern A (permutationMatrix π) ∧ (oneEntries A).card = q
  have h0 : P 0 := by
    refine ⟨zeroBoolMatrix n n, zeroBoolMatrix_avoids_permutation hk π, ?_⟩
    simp
  simpa [forbiddenExtremal, P] using
    Nat.findGreatest_spec (P := P) (m := 0) (n := n * n) (Nat.zero_le _) h0

/-- Every avoiding matrix has at most the extremal number of true entries. -/
theorem oneEntries_card_le_forbiddenExtremal {k n : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (oneEntries A).card ≤ forbiddenExtremal (permutationMatrix π) n := by
  classical
  by_contra hle
  have hgt : forbiddenExtremal (permutationMatrix π) n < (oneEntries A).card :=
    Nat.lt_of_not_ge hle
  have hbound : (oneEntries A).card ≤ n * n := oneEntries_card_le A
  exact Nat.findGreatest_is_greatest
    (P := fun q => ∃ B : _root_.Matrix (Fin n) (Fin n) Bool,
      AvoidsPattern B (permutationMatrix π) ∧ (oneEntries B).card = q)
    (n := n * n) hgt hbound ⟨A, hA, rfl⟩

/- ## Cropping square matrices -/

/-- The order embedding of an initial segment `Fin m` into `Fin n`. -/
def finCastLEOrderEmb {m n : ℕ} (hmn : m ≤ n) : Fin m ↪o Fin n :=
  OrderEmbedding.ofStrictMono (Fin.castLE hmn) (by
    intro a b hab
    exact Fin.mk_lt_mk.mpr (by simpa using hab))

/-- The upper-left `m × m` submatrix of an `n × n` matrix. -/
def cropMatrix {m n : ℕ} (hmn : m ≤ n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool) :
    _root_.Matrix (Fin m) (Fin m) Bool :=
  fun i j => A (Fin.castLE hmn i) (Fin.castLE hmn j)

/-- Containment in a crop lifts to containment in the original matrix. -/
theorem cropMatrix_lifts_containment {m n k l : ℕ} (hmn : m ≤ n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (P : _root_.Matrix (Fin k) (Fin l) Bool)
    (h : ContainsPattern (cropMatrix hmn A) P) :
    ContainsPattern A P := by
  rcases h with ⟨row, col, hcontains⟩
  let row' : Fin k ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun i => Fin.castLE hmn (row i)) (by
      intro i j hij
      exact Fin.mk_lt_mk.mpr (by simpa using row.strictMono hij))
  let col' : Fin l ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun j => Fin.castLE hmn (col j)) (by
      intro i j hij
      exact Fin.mk_lt_mk.mpr (by simpa using col.strictMono hij))
  exact ⟨row', col', by
    intro i j hij
    simpa [row', col', cropMatrix] using hcontains i j hij⟩

/-- Avoidance is inherited by upper-left crops. -/
theorem cropMatrix_avoids {m n k l : ℕ} (hmn : m ≤ n)
    {A : _root_.Matrix (Fin n) (Fin n) Bool}
    {P : _root_.Matrix (Fin k) (Fin l) Bool}
    (hA : AvoidsPattern A P) :
    AvoidsPattern (cropMatrix hmn A) P := by
  intro h
  exact hA (cropMatrix_lifts_containment hmn A P h)

/-- Restrict a `Fin n` value to `Fin m`, using `0` only outside the initial
segment.  Lemmas below use it on entries known to lie inside the segment. -/
def finRestrict {m n : ℕ} (hm : 0 < m) (x : Fin n) : Fin m :=
  if h : x.1 < m then ⟨x.1, h⟩ else ⟨0, hm⟩

theorem castLE_finRestrict {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {x : Fin n} (hx : x.1 < m) :
    Fin.castLE hmn (finRestrict hm x) = x := by
  ext
  simp [finRestrict, hx]

theorem insideEntries_card_le_forbiddenExtremal {k m n : ℕ}
    (π : Equiv.Perm (Fin k)) (hm : 0 < m) (hmn : m ≤ n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    ((oneEntries A).filter fun p => p.1.1 < m ∧ p.2.1 < m).card ≤
      forbiddenExtremal (permutationMatrix π) m := by
  classical
  let inside := (oneEntries A).filter fun p => p.1.1 < m ∧ p.2.1 < m
  let B := cropMatrix hmn A
  let toCrop := fun p : Fin n × Fin n => (finRestrict hm p.1, finRestrict hm p.2)
  have hmaps : Set.MapsTo toCrop inside (oneEntries B) := by
    intro p hp
    have hp' : p ∈ oneEntries A ∧ (p.1.1 < m ∧ p.2.1 < m) := by
      simpa [inside] using hp
    have htrue : A p.1 p.2 = true := (mem_oneEntries_iff A p).mp hp'.1
    have hrow := castLE_finRestrict hm hmn hp'.2.1
    have hcol := castLE_finRestrict hm hmn hp'.2.2
    exact (mem_oneEntries_iff B (toCrop p)).mpr (by
      simpa [B, cropMatrix, toCrop, hrow, hcol] using htrue)
  have hinj : (inside : Set (Fin n × Fin n)).InjOn toCrop := by
    intro p hp r hr hpr
    have hp' : p ∈ oneEntries A ∧ (p.1.1 < m ∧ p.2.1 < m) := by
      simpa [inside] using hp
    have hr' : r ∈ oneEntries A ∧ (r.1.1 < m ∧ r.2.1 < m) := by
      simpa [inside] using hr
    have hrow : p.1 = r.1 := by
      have hrowFin : (toCrop p).1 = (toCrop r).1 := congrArg Prod.fst hpr
      have hval := congrArg Fin.val hrowFin
      apply Fin.ext
      simpa [toCrop, finRestrict, hp'.2.1, hr'.2.1] using hval
    have hcol : p.2 = r.2 := by
      have hcolFin : (toCrop p).2 = (toCrop r).2 := congrArg Prod.snd hpr
      have hval := congrArg Fin.val hcolFin
      apply Fin.ext
      simpa [toCrop, finRestrict, hp'.2.2, hr'.2.2] using hval
    exact Prod.ext hrow hcol
  calc
    inside.card ≤ (oneEntries B).card :=
      Finset.card_le_card_of_injOn toCrop hmaps hinj
    _ ≤ forbiddenExtremal (permutationMatrix π) m :=
      oneEntries_card_le_forbiddenExtremal π B (cropMatrix_avoids hmn hA)

theorem highFinset_card {m n : ℕ} (hmn : m < n) :
    ((Finset.univ : Finset (Fin n)).filter fun i => m ≤ i.1).card = n - m := by
  let a : Fin n := ⟨m, hmn⟩
  have hset : ((Finset.univ : Finset (Fin n)).filter fun i => m ≤ i.1) =
      Finset.Ici a := by
    ext i
    simp [a, Finset.mem_Ici, Fin.le_iff_val_le_val]
  rw [hset]
  simp [a, Fin.card_Ici]

theorem boundaryPairs_card_le {m n : ℕ} (hmn : m < n) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter
      fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)).card ≤ 2 * (n - m) * n := by
  classical
  let R : Finset (Fin n × Fin n) :=
    (Finset.univ.filter fun p : Fin n × Fin n => m ≤ p.1.1)
  let C : Finset (Fin n × Fin n) :=
    (Finset.univ.filter fun p : Fin n × Fin n => m ≤ p.2.1)
  have hcover :
      ((Finset.univ : Finset (Fin n × Fin n)).filter
        fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)) ⊆ R ∪ C := by
    intro p hp
    have hpnot : ¬ (p.1.1 < m ∧ p.2.1 < m) := by simpa using hp
    by_cases hrow : p.1.1 < m
    · have hcol : m ≤ p.2.1 := Nat.le_of_not_gt (by
        intro h
        exact hpnot ⟨hrow, h⟩)
      simp [R, C, hcol]
    · have hrow' : m ≤ p.1.1 := Nat.le_of_not_gt hrow
      simp [R, C, hrow']
  let rowSet : Finset (Fin n) := Finset.univ.filter fun i => m ≤ i.1
  have hRsub : R ⊆ rowSet.product (Finset.univ : Finset (Fin n)) := by
    intro p hp
    have hp' : m ≤ p.1.1 := by simpa [R] using hp
    exact Finset.mem_product.mpr ⟨by simp [rowSet, hp'], Finset.mem_univ _⟩
  have hCsub : C ⊆ (Finset.univ : Finset (Fin n)).product rowSet := by
    intro p hp
    have hp' : m ≤ p.2.1 := by simpa [C] using hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp [rowSet, hp']⟩
  have hrowSet_card : rowSet.card = n - m := by
    simpa [rowSet] using highFinset_card hmn
  have hRcard : R.card ≤ (n - m) * n := by
    calc
      R.card ≤ (rowSet.product (Finset.univ : Finset (Fin n))).card :=
        Finset.card_le_card hRsub
      _ = rowSet.card * n := by simp
      _ = (n - m) * n := by simp [hrowSet_card]
  have hCcard : C.card ≤ (n - m) * n := by
    calc
      C.card ≤ ((Finset.univ : Finset (Fin n)).product rowSet).card :=
        Finset.card_le_card hCsub
      _ = n * rowSet.card := by simp
      _ = (n - m) * n := by simp [hrowSet_card, Nat.mul_comm]
  calc
    ((Finset.univ : Finset (Fin n × Fin n)).filter
        fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)).card ≤ (R ∪ C).card :=
      Finset.card_le_card hcover
    _ ≤ R.card + C.card := Finset.card_union_le R C
    _ ≤ (n - m) * n + (n - m) * n := Nat.add_le_add hRcard hCcard
    _ = 2 * (n - m) * n := by ring

/-- Cropping to an initial `m × m` submatrix loses at most the boundary rows
and columns. -/
theorem forbiddenExtremal_le_crop_add_boundary {k m n : ℕ}
    (π : Equiv.Perm (Fin k)) (hk : 0 < k) (hm : 0 < m) (hmn : m ≤ n) (hmn' : m < n) :
    forbiddenExtremal (permutationMatrix π) n ≤
      forbiddenExtremal (permutationMatrix π) m + 2 * (n - m) * n := by
  classical
  obtain ⟨A, hA, hcard⟩ := exists_forbiddenExtremal_eq (n := n) hk π
  let inside := (oneEntries A).filter fun p => p.1.1 < m ∧ p.2.1 < m
  let outside := (oneEntries A).filter fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)
  have hsplit : (oneEntries A).card = inside.card + outside.card := by
    simpa [inside, outside, Nat.add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := oneEntries A) (p := fun p : Fin n × Fin n => p.1.1 < m ∧ p.2.1 < m)).symm
  have hinside : inside.card ≤ forbiddenExtremal (permutationMatrix π) m := by
    simpa [inside] using insideEntries_card_le_forbiddenExtremal π hm hmn A hA
  have houtside : outside.card ≤ 2 * (n - m) * n := by
    calc
      outside.card ≤
          ((Finset.univ : Finset (Fin n × Fin n)).filter
            fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)).card :=
        Finset.card_le_card (by
          intro p hp
          have hp' : p ∈ oneEntries A ∧ ¬ (p.1.1 < m ∧ p.2.1 < m) := by
            simpa [outside] using hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hp'.2)
      _ ≤ 2 * (n - m) * n := boundaryPairs_card_le hmn'
  calc
    forbiddenExtremal (permutationMatrix π) n = (oneEntries A).card := hcard.symm
    _ = inside.card + outside.card := hsplit
    _ ≤ forbiddenExtremal (permutationMatrix π) m + 2 * (n - m) * n :=
      Nat.add_le_add hinside houtside

/-- The block-recursion statement of Marcus--Tardos Lemma 7.

For a `k × k` permutation matrix `P`, the extremal function at `q * k^2` is
bounded in terms of the extremal function at `q`.  This is the paper's
`n / k^2` recurrence, stated with the quotient `q` explicit to avoid dependent
casts between `Fin n` and `Fin (q * k^2)`.

The binomial factor is `choose (k^2) k`: each block has side length `k^2`, and
Lemma 5 chooses `k` active columns from those `k^2` columns. -/
def FurediHajnalRecursion : Prop :=
  ∀ {k q : ℕ} (P : _root_.Matrix (Fin k) (Fin k) Bool),
    2 ≤ k → IsPermutationMatrix P →
      forbiddenExtremal P (q * k ^ 2) ≤
        (k - 1) ^ 2 * forbiddenExtremal P q +
          2 * k ^ 3 * Nat.choose (k ^ 2) k * (q * k ^ 2)

/-- The explicit linear bound of Marcus--Tardos Theorem 8, with the constant
appearing in the paper. -/
def FurediHajnalExplicitBound : Prop :=
  ∀ {k n : ℕ} (P : _root_.Matrix (Fin k) (Fin k) Bool),
    2 ≤ k → IsPermutationMatrix P →
      forbiddenExtremal P n ≤ 2 * k ^ 4 * Nat.choose (k ^ 2) k * n

/-- The qualitative Füredi--Hajnal theorem for permutation matrices. -/
def FurediHajnalTheorem : Prop :=
  ∀ {k : ℕ} (P : _root_.Matrix (Fin k) (Fin k) Bool),
    2 ≤ k → IsPermutationMatrix P → ∃ c : ℕ, ∀ n, forbiddenExtremal P n ≤ c * n

theorem furediHajnalTheorem_of_explicitBound
    (h : FurediHajnalExplicitBound) : FurediHajnalTheorem := by
  intro k P hk hP
  exact ⟨2 * k ^ 4 * Nat.choose (k ^ 2) k, fun n => h P hk hP⟩

/- ## Block decomposition from Section 2 -/

/-- Rows belonging to the `I`-th consecutive block when a `q * s` square matrix
is partitioned into `q × q` blocks of side length `s`. -/
def blockRows (q s : ℕ) (I : Fin q) : Finset (Fin (q * s)) :=
  Finset.univ.filter fun r => I.1 * s ≤ r.1 ∧ r.1 < (I.1 + 1) * s

/-- Columns belonging to the `J`-th consecutive block. -/
def blockCols (q s : ℕ) (J : Fin q) : Finset (Fin (q * s)) :=
  Finset.univ.filter fun c => J.1 * s ≤ c.1 ∧ c.1 < (J.1 + 1) * s

/-- The block index of a row or column in a `q × q` block decomposition with
side length `s`. -/
def blockIndex (q s : ℕ) (x : Fin (q * s)) : Fin q :=
  ⟨x.1 / s, Nat.div_lt_of_lt_mul
    (lt_of_lt_of_le x.2 (le_of_eq (Nat.mul_comm q s)))⟩

/-- A row belongs to the block selected by its quotient index. -/
theorem blockIndex_mem_blockRows {q s : ℕ} (hs : 0 < s) (x : Fin (q * s)) :
    x ∈ blockRows q s (blockIndex q s x) := by
  have hlow : (x.1 / s) * s ≤ x.1 := Nat.div_mul_le_self x.1 s
  have hupper : x.1 < (x.1 / s + 1) * s := by
    calc
      x.1 = s * (x.1 / s) + x.1 % s := (Nat.div_add_mod x.1 s).symm
      _ < s * (x.1 / s) + s := Nat.add_lt_add_left (Nat.mod_lt x.1 hs) _
      _ = (x.1 / s + 1) * s := by ring
  simpa [blockRows, blockIndex] using ⟨hlow, hupper⟩

/-- A column belongs to the block selected by its quotient index. -/
theorem blockIndex_mem_blockCols {q s : ℕ} (hs : 0 < s) (x : Fin (q * s)) :
    x ∈ blockCols q s (blockIndex q s x) := by
  have hlow : (x.1 / s) * s ≤ x.1 := Nat.div_mul_le_self x.1 s
  have hupper : x.1 < (x.1 / s + 1) * s := by
    calc
      x.1 = s * (x.1 / s) + x.1 % s := (Nat.div_add_mod x.1 s).symm
      _ < s * (x.1 / s) + s := Nat.add_lt_add_left (Nat.mod_lt x.1 hs) _
      _ = (x.1 / s + 1) * s := by ring
  simpa [blockCols, blockIndex] using ⟨hlow, hupper⟩

/-- The block containing a matrix entry. -/
def entryBlockIndex {q s : ℕ} (p : Fin (q * s) × Fin (q * s)) : Fin q × Fin q :=
  (blockIndex q s p.1, blockIndex q s p.2)

/-- The `(I,J)` block contains a true entry. -/
def BlockNonempty {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I J : Fin q) : Prop :=
  ∃ r ∈ blockRows q s I, ∃ c ∈ blockCols q s J, A r c = true

/-- True entries lying in a specific block. -/
noncomputable def blockEntries {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I J : Fin q) : Finset (Fin (q * s) × Fin (q * s)) :=
  by
    classical
    exact Finset.univ.filter fun p =>
      p.1 ∈ blockRows q s I ∧ p.2 ∈ blockCols q s J ∧ A p.1 p.2 = true

/-- The compressed block matrix `B` of Marcus--Tardos Lemma 4.  Its entry is
`true` precisely when the corresponding block of `A` is nonempty. -/
noncomputable def blockCompression {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) :
    _root_.Matrix (Fin q) (Fin q) Bool :=
  by
    classical
    exact fun I J => decide (BlockNonempty A I J)

/-- Columns of a block containing at least one true entry. -/
noncomputable def activeBlockCols {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I J : Fin q) : Finset (Fin (q * s)) :=
  by
    classical
    exact (blockCols q s J).filter fun c =>
      ∃ r ∈ blockRows q s I, A r c = true

/-- Rows of a block containing at least one true entry. -/
noncomputable def activeBlockRows {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I J : Fin q) : Finset (Fin (q * s)) :=
  by
    classical
    exact (blockRows q s I).filter fun r =>
      ∃ c ∈ blockCols q s J, A r c = true

/-- A block is wide when its true entries appear in at least `threshold`
different columns.  In Section 2 the threshold is `k`. -/
def BlockWide {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I J : Fin q) : Prop :=
  threshold ≤ (activeBlockCols A I J).card

/-- A block is tall when its true entries appear in at least `threshold`
different rows.  In Section 2 the threshold is `k`. -/
def BlockTall {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I J : Fin q) : Prop :=
  threshold ≤ (activeBlockRows A I J).card

/-- The row blocks in a fixed block column that are wide. -/
noncomputable def wideBlocksInColumn {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (J : Fin q) : Finset (Fin q) :=
  by
    classical
    exact Finset.univ.filter fun I => BlockWide A threshold I J

/-- The column blocks in a fixed block row that are tall. -/
noncomputable def tallBlocksInRow {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I : Fin q) : Finset (Fin q) :=
  by
    classical
    exact Finset.univ.filter fun J => BlockTall A threshold I J

/-- The `X₃` blocks from Marcus--Tardos Lemma 7: nonempty blocks that are
neither wide nor tall. -/
noncomputable def nonemptyNarrowBlocks {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) : Finset (Fin q × Fin q) :=
  by
    classical
    exact Finset.univ.filter fun p =>
      BlockNonempty A p.1 p.2 ∧ ¬ BlockWide A threshold p.1 p.2 ∧
        ¬ BlockTall A threshold p.1 p.2

/-- All wide blocks of a block decomposition. -/
noncomputable def wideBlocks {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) : Finset (Fin q × Fin q) :=
  by
    classical
    exact Finset.univ.filter fun p => BlockWide A threshold p.1 p.2

/-- All tall blocks of a block decomposition. -/
noncomputable def tallBlocks {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) : Finset (Fin q × Fin q) :=
  by
    classical
    exact Finset.univ.filter fun p => BlockTall A threshold p.1 p.2

/-- A chosen set of `threshold` active columns in a wide block.

For non-wide blocks this returns `∅`; all lemmas below use it only on wide
blocks. -/
noncomputable def chosenActiveCols {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I J : Fin q) : Finset (Fin (q * s)) :=
  by
    classical
    exact if h : BlockWide A threshold I J then
      Classical.choose (Finset.powersetCard_nonempty.mpr h)
    else
      ∅

/-- A chosen set of `threshold` active rows in a tall block.

For non-tall blocks this returns `∅`; all lemmas below use it only on tall
blocks. -/
noncomputable def chosenActiveRows {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I J : Fin q) : Finset (Fin (q * s)) :=
  by
    classical
    exact if h : BlockTall A threshold I J then
      Classical.choose (Finset.powersetCard_nonempty.mpr h)
    else
      ∅

theorem mem_blockCompression_iff {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    blockCompression A I J = true ↔ BlockNonempty A I J := by
  classical
  simp [blockCompression]

theorem activeBlockCols_subset_blockCols {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    activeBlockCols A I J ⊆ blockCols q s J := by
  classical
  intro c hc
  exact (by
    simpa [activeBlockCols] using hc : c ∈ blockCols q s J ∧
      ∃ r ∈ blockRows q s I, A r c = true).1

theorem activeBlockRows_subset_blockRows {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    activeBlockRows A I J ⊆ blockRows q s I := by
  classical
  intro r hr
  exact (by
    simpa [activeBlockRows] using hr : r ∈ blockRows q s I ∧
      ∃ c ∈ blockCols q s J, A r c = true).1

theorem blockEntries_subset_active_product {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    blockEntries A I J ⊆ (activeBlockRows A I J).product (activeBlockCols A I J) := by
  classical
  intro p hp
  have hp' : p.1 ∈ blockRows q s I ∧ p.2 ∈ blockCols q s J ∧ A p.1 p.2 = true := by
    simpa [blockEntries] using hp
  exact Finset.mem_product.mpr
    ⟨by
      simp [activeBlockRows, hp'.1]
      exact ⟨p.2, hp'.2.1, hp'.2.2⟩,
     by
      simp [activeBlockCols, hp'.2.1]
      exact ⟨p.1, hp'.1, hp'.2.2⟩⟩

theorem blockEntries_card_le_active_mul {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    (blockEntries A I J).card ≤
      (activeBlockRows A I J).card * (activeBlockCols A I J).card := by
  classical
  calc
    (blockEntries A I J).card ≤
        ((activeBlockRows A I J).product (activeBlockCols A I J)).card :=
      Finset.card_le_card (blockEntries_subset_active_product A I J)
    _ = (activeBlockRows A I J).card * (activeBlockCols A I J).card := by simp

theorem blockEntries_card_le_of_not_wide_not_tall {q s k : ℕ} (_hk : 0 < k)
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q)
    (hwide : ¬ BlockWide A k I J) (htall : ¬ BlockTall A k I J) :
    (blockEntries A I J).card ≤ (k - 1) ^ 2 := by
  have hcols_lt : (activeBlockCols A I J).card < k := Nat.lt_of_not_ge hwide
  have hrows_lt : (activeBlockRows A I J).card < k := Nat.lt_of_not_ge htall
  have hcols_le : (activeBlockCols A I J).card ≤ k - 1 := Nat.le_pred_of_lt hcols_lt
  have hrows_le : (activeBlockRows A I J).card ≤ k - 1 := Nat.le_pred_of_lt hrows_lt
  calc
    (blockEntries A I J).card ≤
        (activeBlockRows A I J).card * (activeBlockCols A I J).card :=
      blockEntries_card_le_active_mul A I J
    _ ≤ (k - 1) * (k - 1) := Nat.mul_le_mul hrows_le hcols_le
    _ = (k - 1) ^ 2 := by ring

theorem chosenActiveCols_mem_powersetCard {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (hwide : BlockWide A threshold I J) :
    chosenActiveCols A threshold I J ∈
      (activeBlockCols A I J).powersetCard threshold := by
  classical
  simp [chosenActiveCols, hwide,
    Classical.choose_spec (Finset.powersetCard_nonempty.mpr hwide)]

theorem chosenActiveCols_subset_active {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (hwide : BlockWide A threshold I J) :
    chosenActiveCols A threshold I J ⊆ activeBlockCols A I J :=
  (Finset.mem_powersetCard.mp (chosenActiveCols_mem_powersetCard A hwide)).1

theorem chosenActiveCols_card {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (hwide : BlockWide A threshold I J) :
    (chosenActiveCols A threshold I J).card = threshold :=
  (Finset.mem_powersetCard.mp (chosenActiveCols_mem_powersetCard A hwide)).2

theorem chosenActiveCols_subset_blockCols {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (hwide : BlockWide A threshold I J) :
    chosenActiveCols A threshold I J ⊆ blockCols q s J :=
  (chosenActiveCols_subset_active A hwide).trans (activeBlockCols_subset_blockCols A I J)

theorem chosenActiveRows_mem_powersetCard {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (htall : BlockTall A threshold I J) :
    chosenActiveRows A threshold I J ∈
      (activeBlockRows A I J).powersetCard threshold := by
  classical
  simp [chosenActiveRows, htall,
    Classical.choose_spec (Finset.powersetCard_nonempty.mpr htall)]

theorem chosenActiveRows_subset_active {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (htall : BlockTall A threshold I J) :
    chosenActiveRows A threshold I J ⊆ activeBlockRows A I J :=
  (Finset.mem_powersetCard.mp (chosenActiveRows_mem_powersetCard A htall)).1

theorem chosenActiveRows_card {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (htall : BlockTall A threshold I J) :
    (chosenActiveRows A threshold I J).card = threshold :=
  (Finset.mem_powersetCard.mp (chosenActiveRows_mem_powersetCard A htall)).2

theorem chosenActiveRows_subset_blockRows {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (htall : BlockTall A threshold I J) :
    chosenActiveRows A threshold I J ⊆ blockRows q s I :=
  (chosenActiveRows_subset_active A htall).trans (activeBlockRows_subset_blockRows A I J)

/-- A finite pigeonhole principle in the form needed for Lemma 5.  If a finite
set is larger than `(k - 1)` times the number of fibers of a map, then one fiber
has at least `k` elements. -/
theorem exists_fiber_card_ge_of_sub_one_mul_image_card_lt
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) {k : ℕ}
    (hlarge : (k - 1) * (S.image f).card < S.card) :
    ∃ b ∈ S.image f, k ≤ (S.filter fun a => f a = b).card := by
  classical
  by_contra h
  push Not at h
  have hfiber : ∀ b ∈ S.image f, (S.filter fun a => f a = b).card ≤ k - 1 := by
    intro b hb
    exact Nat.le_pred_of_lt (h b hb)
  have hcard := Finset.card_le_mul_card_image (s := S) (f := f) (n := k - 1) hfiber
  exact not_lt_of_ge hcard hlarge

/-- Membership in `blockRows` is exactly the defining pair of inequalities. -/
theorem mem_blockRows_iff {q s : ℕ} (I : Fin q) (r : Fin (q * s)) :
    r ∈ blockRows q s I ↔ I.1 * s ≤ r.1 ∧ r.1 < (I.1 + 1) * s := by
  simp [blockRows]

/-- Membership in `blockCols` is exactly the defining pair of inequalities. -/
theorem mem_blockCols_iff {q s : ℕ} (J : Fin q) (c : Fin (q * s)) :
    c ∈ blockCols q s J ↔ J.1 * s ≤ c.1 ∧ c.1 < (J.1 + 1) * s := by
  simp [blockCols]

/-- Each row block has side length `s`. -/
theorem blockRows_card {q s : ℕ} (I : Fin q) :
    (blockRows q s I).card = s := by
  classical
  refine Finset.card_eq_of_bijective (s := blockRows q s I) (n := s)
    (fun a ha => (⟨I.1 * s + a, ?_⟩ : Fin (q * s))) ?_ ?_ ?_
  · have hIq : I.1 + 1 ≤ q := Nat.succ_le_of_lt I.2
    have hbound : I.1 * s + s ≤ q * s := by
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.mul_le_mul_right s hIq)
    exact lt_of_lt_of_le (Nat.add_lt_add_left ha _) hbound
  · intro r hr
    have hr' := (mem_blockRows_iff I r).mp hr
    refine ⟨r.1 - I.1 * s, ?_, ?_⟩
    · have hupper : r.1 < I.1 * s + s := by
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hr'.2
      have hsub := (Nat.sub_lt_sub_iff_right hr'.1).2 hupper
      simpa [Nat.add_sub_cancel_left] using hsub
    · ext
      exact Nat.add_sub_cancel' hr'.1
  · intro a ha
    exact (mem_blockRows_iff I _).mpr ⟨Nat.le_add_right _ _, by
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.add_lt_add_left ha (I.1 * s))⟩
  · intro a ha b hb h
    exact Nat.add_left_cancel (Fin.ext_iff.mp h)

/-- Each column block has side length `s`. -/
theorem blockCols_card {q s : ℕ} (J : Fin q) :
    (blockCols q s J).card = s := by
  classical
  refine Finset.card_eq_of_bijective (s := blockCols q s J) (n := s)
    (fun a ha => (⟨J.1 * s + a, ?_⟩ : Fin (q * s))) ?_ ?_ ?_
  · have hJq : J.1 + 1 ≤ q := Nat.succ_le_of_lt J.2
    have hbound : J.1 * s + s ≤ q * s := by
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.mul_le_mul_right s hJq)
    exact lt_of_lt_of_le (Nat.add_lt_add_left ha _) hbound
  · intro c hc
    have hc' := (mem_blockCols_iff J c).mp hc
    refine ⟨c.1 - J.1 * s, ?_, ?_⟩
    · have hupper : c.1 < J.1 * s + s := by
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc'.2
      have hsub := (Nat.sub_lt_sub_iff_right hc'.1).2 hupper
      simpa [Nat.add_sub_cancel_left] using hsub
    · ext
      exact Nat.add_sub_cancel' hc'.1
  · intro a ha
    exact (mem_blockCols_iff J _).mpr ⟨Nat.le_add_right _ _, by
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.add_lt_add_left ha (J.1 * s))⟩
  · intro a ha b hb h
    exact Nat.add_left_cancel (Fin.ext_iff.mp h)

/-- Any entry in an earlier row block is above any entry in a later row block. -/
theorem blockRows_lt_of_lt {q s : ℕ} {I J : Fin q} {r t : Fin (q * s)}
    (hIJ : I < J) (hr : r ∈ blockRows q s I) (ht : t ∈ blockRows q s J) :
    r < t := by
  have hr' := (mem_blockRows_iff I r).mp hr
  have ht' := (mem_blockRows_iff J t).mp ht
  exact Fin.mk_lt_mk.mpr (lt_of_lt_of_le hr'.2 (by
    exact le_trans (Nat.mul_le_mul_right s (Nat.succ_le_of_lt hIJ)) ht'.1))

/-- Any entry in an earlier column block is left of any entry in a later column
block. -/
theorem blockCols_lt_of_lt {q s : ℕ} {I J : Fin q} {r t : Fin (q * s)}
    (hIJ : I < J) (hr : r ∈ blockCols q s I) (ht : t ∈ blockCols q s J) :
    r < t := by
  have hr' := (mem_blockCols_iff I r).mp hr
  have ht' := (mem_blockCols_iff J t).mp ht
  exact Fin.mk_lt_mk.mpr (lt_of_lt_of_le hr'.2 (by
    exact le_trans (Nat.mul_le_mul_right s (Nat.succ_le_of_lt hIJ)) ht'.1))

/-- The permutation-matrix case of Marcus--Tardos Lemma 4: if the compressed
block matrix contains a permutation matrix, then the original matrix contains
it. -/
theorem blockCompression_lifts_permutation_containment {q s k : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (h : ContainsPattern (blockCompression A) (permutationMatrix π)) :
    ContainsPattern A (permutationMatrix π) := by
  classical
  rcases h with ⟨row, col, hcontains⟩
  have hblock : ∀ i : Fin k, BlockNonempty A (row i) (col (π i)) := by
    intro i
    exact (mem_blockCompression_iff A (row i) (col (π i))).mp
      (hcontains i (π i) (by simp [permutationMatrix]))
  choose pickedRow pickedRow_mem pickedCol pickedCol_mem picked_true using hblock
  let row' : Fin k ↪o Fin (q * s) :=
    OrderEmbedding.ofStrictMono pickedRow (by
      intro i j hij
      exact blockRows_lt_of_lt (row.strictMono hij) (pickedRow_mem i) (pickedRow_mem j))
  let col' : Fin k ↪o Fin (q * s) :=
    OrderEmbedding.ofStrictMono (fun j : Fin k => pickedCol (π.symm j)) (by
      intro i j hij
      have hci : pickedCol (π.symm i) ∈ blockCols q s (col i) := by
        simpa using pickedCol_mem (π.symm i)
      have hcj : pickedCol (π.symm j) ∈ blockCols q s (col j) := by
        simpa using pickedCol_mem (π.symm j)
      exact blockCols_lt_of_lt (col.strictMono hij) hci hcj)
  refine ⟨row', col', ?_⟩
  intro i j hP
  have hj : j = π i := by
    simpa [permutationMatrix] using hP
  subst j
  simpa [row', col'] using picked_true i

/-- Marcus--Tardos Lemma 4, packaged as the avoidance form that follows from
`BlockCompressionLiftsPermutationContainment`. -/
theorem blockCompression_avoids_permutation
    {q s k : ℕ} (π : Equiv.Perm (Fin k))
    {A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool}
    (hA : AvoidsPattern A (permutationMatrix π)) :
    AvoidsPattern (blockCompression A) (permutationMatrix π) := by
  intro hB
  exact hA (blockCompression_lifts_permutation_containment π A hB)

/-- The number of nonempty narrow blocks is bounded by the number of true
entries in the compressed block matrix. -/
theorem nonemptyNarrowBlocks_card_le_blockCompression_ones {q s k : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) :
    (nonemptyNarrowBlocks A k).card ≤ (oneEntries (blockCompression A)).card := by
  classical
  refine Finset.card_le_card ?_
  intro p hp
  have hp' : BlockNonempty A p.1 p.2 ∧ ¬ BlockWide A k p.1 p.2 ∧
      ¬ BlockTall A k p.1 p.2 := by
    simpa [nonemptyNarrowBlocks] using hp
  exact (mem_oneEntries_iff (blockCompression A) p).mpr
    ((mem_blockCompression_iff A p.1 p.2).mpr hp'.1)

/-- The `X₃` bound used in Lemma 7: nonempty blocks that are neither wide nor
tall are bounded by the extremal number of the compressed matrix. -/
theorem nonemptyNarrowBlocks_card_le_forbiddenExtremal {q s k : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (nonemptyNarrowBlocks A k).card ≤
      forbiddenExtremal (permutationMatrix π) q := by
  exact le_trans (nonemptyNarrowBlocks_card_le_blockCompression_ones A)
    (oneEntries_card_le_forbiddenExtremal π (blockCompression A)
      (blockCompression_avoids_permutation π hA))

/-- If `k` row blocks in one block column share an ordered family of `k` active
columns, then the original matrix contains the corresponding permutation
matrix.  This is the constructive core of Marcus--Tardos Lemma 5; the remaining
part of Lemma 5 is the finite pigeonhole argument that produces these common
columns from too many wide blocks. -/
theorem contains_permutation_of_common_active_columns {q s k : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (J : Fin q) (rows : Fin k ↪o Fin q)
    (cols : Fin k ↪o Fin (q * s))
    (hactive : ∀ i : Fin k, cols (π i) ∈ activeBlockCols A (rows i) J) :
    ContainsPattern A (permutationMatrix π) := by
  classical
  have hrow_exists :
      ∀ i : Fin k, ∃ r ∈ blockRows q s (rows i), A r (cols (π i)) = true := by
    intro i
    have h := hactive i
    exact (by
      simpa [activeBlockCols] using h :
        cols (π i) ∈ blockCols q s J ∧
          ∃ r ∈ blockRows q s (rows i), A r (cols (π i)) = true).2
  choose pickedRow pickedRow_mem picked_true using hrow_exists
  let row' : Fin k ↪o Fin (q * s) :=
    OrderEmbedding.ofStrictMono pickedRow (by
      intro i j hij
      exact blockRows_lt_of_lt (rows.strictMono hij) (pickedRow_mem i) (pickedRow_mem j))
  refine ⟨row', cols, ?_⟩
  intro i j hP
  have hj : j = π i := by
    simpa [permutationMatrix] using hP
  subst j
  simpa [row'] using picked_true i

/-- Row/column dual of `contains_permutation_of_common_active_columns`: if `k`
column blocks in one block row share an ordered family of `k` active rows, then
the original matrix contains the corresponding permutation matrix. -/
theorem contains_permutation_of_common_active_rows {q s k : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I : Fin q) (cols : Fin k ↪o Fin q)
    (rows : Fin k ↪o Fin (q * s))
    (hactive : ∀ j : Fin k, rows (π.symm j) ∈ activeBlockRows A I (cols j)) :
    ContainsPattern A (permutationMatrix π) := by
  classical
  have hcol_exists :
      ∀ j : Fin k, ∃ c ∈ blockCols q s (cols j), A (rows (π.symm j)) c = true := by
    intro j
    have h := hactive j
    exact (by
      simpa [activeBlockRows] using h :
        rows (π.symm j) ∈ blockRows q s I ∧
          ∃ c ∈ blockCols q s (cols j), A (rows (π.symm j)) c = true).2
  choose pickedCol pickedCol_mem picked_true using hcol_exists
  let col' : Fin k ↪o Fin (q * s) :=
    OrderEmbedding.ofStrictMono pickedCol (by
      intro i j hij
      exact blockCols_lt_of_lt (cols.strictMono hij) (pickedCol_mem i) (pickedCol_mem j))
  refine ⟨rows, col', ?_⟩
  intro i j hP
  have hj : j = π i := by
    simpa [permutationMatrix] using hP
  subst j
  simpa [col'] using picked_true (π i)

/-- Marcus--Tardos Lemma 5 in block language.  For a matrix avoiding a
`k × k` permutation matrix, a fixed block column has fewer than
`k * (#block columns choose k)` wide blocks.

In the paper's application the block side length is `s = k^2`, and
`#blockCols = s`, giving the displayed bound `k * (k^2 choose k)`. -/
theorem wideBlocksInColumn_card_lt {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (J : Fin q)
    (hks : k ≤ (blockCols q s J).card)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (wideBlocksInColumn A k J).card <
      k * Nat.choose (blockCols q s J).card k := by
  classical
  let W := wideBlocksInColumn A k J
  let chooseCols := fun I : Fin q => chosenActiveCols A k I J
  let C := Nat.choose (blockCols q s J).card k
  have hCpos : 0 < C := Nat.choose_pos hks
  by_contra hlt
  have hge : k * C ≤ W.card := le_of_not_gt hlt
  have himage_subset :
      W.image chooseCols ⊆ (blockCols q s J).powersetCard k := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨I, hIW, rfl⟩
    have hwide : BlockWide A k I J := by
      simpa [W, wideBlocksInColumn] using hIW
    exact Finset.mem_powersetCard.mpr
      ⟨chosenActiveCols_subset_blockCols A hwide, chosenActiveCols_card A hwide⟩
  have himage_card_le : (W.image chooseCols).card ≤ C := by
    calc
      (W.image chooseCols).card ≤ ((blockCols q s J).powersetCard k).card :=
        Finset.card_le_card himage_subset
      _ = C := by simp [C, Finset.card_powersetCard]
  have hlarge : (k - 1) * (W.image chooseCols).card < W.card := by
    have hle : (k - 1) * (W.image chooseCols).card ≤ (k - 1) * C :=
      Nat.mul_le_mul_left _ himage_card_le
    have hltKC : (k - 1) * C < k * C := by
      exact Nat.mul_lt_mul_of_pos_right (Nat.pred_lt hk.ne') hCpos
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hltKC hge)
  obtain ⟨commonCols, hcommon_image, hfiber_card⟩ :=
    exists_fiber_card_ge_of_sub_one_mul_image_card_lt W chooseCols hlarge
  have hcommon_powerset : commonCols ∈ (blockCols q s J).powersetCard k :=
    himage_subset hcommon_image
  have hcommon_card : commonCols.card = k :=
    (Finset.mem_powersetCard.mp hcommon_powerset).2
  let fiber := W.filter fun I => chooseCols I = commonCols
  have hfiber_card : k ≤ fiber.card := by
    simpa [fiber] using hfiber_card
  obtain ⟨rowSet, hrowSet_mem⟩ := Finset.powersetCard_nonempty.mpr hfiber_card
  have hrowSet_subset_fiber : rowSet ⊆ fiber := (Finset.mem_powersetCard.mp hrowSet_mem).1
  have hrowSet_card : rowSet.card = k := (Finset.mem_powersetCard.mp hrowSet_mem).2
  let rows : Fin k ↪o Fin q := rowSet.orderEmbOfFin hrowSet_card
  let cols : Fin k ↪o Fin (q * s) := commonCols.orderEmbOfFin hcommon_card
  have hactive : ∀ i : Fin k, cols (π i) ∈ activeBlockCols A (rows i) J := by
    intro i
    have hrow_mem : rows i ∈ rowSet := Finset.orderEmbOfFin_mem rowSet hrowSet_card i
    have hfiber_mem : rows i ∈ fiber := hrowSet_subset_fiber hrow_mem
    have hW_mem : rows i ∈ W := by
      exact (by
        simpa [fiber] using hfiber_mem : rows i ∈ W ∧ chooseCols (rows i) = commonCols).1
    have hchoose_eq : chooseCols (rows i) = commonCols := by
      exact (by
        simpa [fiber] using hfiber_mem : rows i ∈ W ∧ chooseCols (rows i) = commonCols).2
    have hwide : BlockWide A k (rows i) J := by
      simpa [W, wideBlocksInColumn] using hW_mem
    have hcol_common : cols (π i) ∈ commonCols :=
      Finset.orderEmbOfFin_mem commonCols hcommon_card (π i)
    have hcol_chosen : cols (π i) ∈ chooseCols (rows i) := by
      simpa [hchoose_eq] using hcol_common
    exact chosenActiveCols_subset_active A hwide hcol_chosen
  exact hA (contains_permutation_of_common_active_columns π A J rows cols hactive)

/-- Proposition wrapper for Lemma 5. -/
def MarcusTardosLemma5 : Prop :=
  ∀ {q s k : ℕ} (_hk : 0 < k) (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (J : Fin q),
    k ≤ (blockCols q s J).card →
      AvoidsPattern A (permutationMatrix π) →
        (wideBlocksInColumn A k J).card <
          k * Nat.choose (blockCols q s J).card k

theorem marcusTardosLemma5 : MarcusTardosLemma5 :=
  fun hk π A J hks hA => wideBlocksInColumn_card_lt hk π A J hks hA

/-- Marcus--Tardos Lemma 5 with the paper-style bound `k * (s choose k)`,
using that every block column has side length `s`. -/
theorem wideBlocksInColumn_card_lt_choose_side {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (J : Fin q)
    (hks : k ≤ s)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (wideBlocksInColumn A k J).card < k * Nat.choose s k := by
  simpa [blockCols_card J] using
    wideBlocksInColumn_card_lt hk π A J (by simpa [blockCols_card J] using hks) hA

/-- Total number of wide blocks, bounded by summing Lemma 5 over all block
columns. -/
theorem wideBlocks_card_le {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (hks : k ≤ s)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (wideBlocks A k).card ≤ q * (k * Nat.choose s k) := by
  classical
  let f : Fin q × Fin q → Fin q := Prod.snd
  have hfiber : ∀ J ∈ (wideBlocks A k).image f,
      ((wideBlocks A k).filter fun p => f p = J).card ≤ k * Nat.choose s k := by
    intro J hJ
    have hsub :
        ((wideBlocks A k).filter fun p => f p = J).card ≤
          (wideBlocksInColumn A k J).card := by
      let F := (wideBlocks A k).filter fun p => f p = J
      have hcard_image : F.card = (F.image Prod.fst).card := by
        exact (Finset.card_image_of_injOn (s := F) (f := Prod.fst) (by
          intro a ha b hb hab
          have ha' : a ∈ wideBlocks A k ∧ f a = J := by simpa [F] using ha
          have hb' : b ∈ wideBlocks A k ∧ f b = J := by simpa [F] using hb
          ext
          · exact congrArg Fin.val hab
          · exact congrArg Fin.val (ha'.2.trans hb'.2.symm))).symm
      rw [hcard_image]
      refine Finset.card_le_card ?_
      intro I hI
      rcases Finset.mem_image.mp hI with ⟨p, hpF, rfl⟩
      have hp' : p ∈ wideBlocks A k ∧ f p = J := by simpa [F] using hpF
      have hwide : BlockWide A k p.1 p.2 := by simpa [wideBlocks] using hp'.1
      simpa [wideBlocksInColumn, ← hp'.2] using hwide
    exact le_trans hsub (Nat.le_of_lt (wideBlocksInColumn_card_lt_choose_side hk π A J hks hA))
  calc
    (wideBlocks A k).card ≤ (k * Nat.choose s k) * ((wideBlocks A k).image f).card :=
      Finset.card_le_mul_card_image (s := wideBlocks A k) (f := f)
        (n := k * Nat.choose s k) hfiber
    _ ≤ (k * Nat.choose s k) * q := by
      exact Nat.mul_le_mul_left _ (by simpa using Finset.card_le_univ ((wideBlocks A k).image f))
    _ = q * (k * Nat.choose s k) := by ring

/-- Proposition wrapper for the global wide-block count obtained by summing
Marcus--Tardos Lemma 5 over all block columns. -/
def MarcusTardosWideBlockCount : Prop :=
  ∀ {q s k : ℕ} (_hk : 0 < k) (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool),
    k ≤ s →
      AvoidsPattern A (permutationMatrix π) →
        (wideBlocks A k).card ≤ q * (k * Nat.choose s k)

theorem marcusTardosWideBlockCount : MarcusTardosWideBlockCount :=
  fun hk π A hks hA => wideBlocks_card_le hk π A hks hA

/-- Marcus--Tardos Lemma 6 in block language.  For a matrix avoiding a
`k × k` permutation matrix, a fixed block row has fewer than
`k * (#block rows choose k)` tall blocks. -/
theorem tallBlocksInRow_card_lt {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I : Fin q)
    (hks : k ≤ (blockRows q s I).card)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (tallBlocksInRow A k I).card <
      k * Nat.choose (blockRows q s I).card k := by
  classical
  let T := tallBlocksInRow A k I
  let chooseRows := fun J : Fin q => chosenActiveRows A k I J
  let C := Nat.choose (blockRows q s I).card k
  have hCpos : 0 < C := Nat.choose_pos hks
  by_contra hlt
  have hge : k * C ≤ T.card := le_of_not_gt hlt
  have himage_subset :
      T.image chooseRows ⊆ (blockRows q s I).powersetCard k := by
    intro R hR
    rcases Finset.mem_image.mp hR with ⟨J, hJT, rfl⟩
    have htall : BlockTall A k I J := by
      simpa [T, tallBlocksInRow] using hJT
    exact Finset.mem_powersetCard.mpr
      ⟨chosenActiveRows_subset_blockRows A htall, chosenActiveRows_card A htall⟩
  have himage_card_le : (T.image chooseRows).card ≤ C := by
    calc
      (T.image chooseRows).card ≤ ((blockRows q s I).powersetCard k).card :=
        Finset.card_le_card himage_subset
      _ = C := by simp [C, Finset.card_powersetCard]
  have hlarge : (k - 1) * (T.image chooseRows).card < T.card := by
    have hle : (k - 1) * (T.image chooseRows).card ≤ (k - 1) * C :=
      Nat.mul_le_mul_left _ himage_card_le
    have hltKC : (k - 1) * C < k * C := by
      exact Nat.mul_lt_mul_of_pos_right (Nat.pred_lt hk.ne') hCpos
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hltKC hge)
  obtain ⟨commonRows, hcommon_image, hfiber_card⟩ :=
    exists_fiber_card_ge_of_sub_one_mul_image_card_lt T chooseRows hlarge
  have hcommon_powerset : commonRows ∈ (blockRows q s I).powersetCard k :=
    himage_subset hcommon_image
  have hcommon_card : commonRows.card = k :=
    (Finset.mem_powersetCard.mp hcommon_powerset).2
  let fiber := T.filter fun J => chooseRows J = commonRows
  have hfiber_card : k ≤ fiber.card := by
    simpa [fiber] using hfiber_card
  obtain ⟨colSet, hcolSet_mem⟩ := Finset.powersetCard_nonempty.mpr hfiber_card
  have hcolSet_subset_fiber : colSet ⊆ fiber := (Finset.mem_powersetCard.mp hcolSet_mem).1
  have hcolSet_card : colSet.card = k := (Finset.mem_powersetCard.mp hcolSet_mem).2
  let cols : Fin k ↪o Fin q := colSet.orderEmbOfFin hcolSet_card
  let rows : Fin k ↪o Fin (q * s) := commonRows.orderEmbOfFin hcommon_card
  have hactive : ∀ j : Fin k, rows (π.symm j) ∈ activeBlockRows A I (cols j) := by
    intro j
    have hcol_mem : cols j ∈ colSet := Finset.orderEmbOfFin_mem colSet hcolSet_card j
    have hfiber_mem : cols j ∈ fiber := hcolSet_subset_fiber hcol_mem
    have hT_mem : cols j ∈ T := by
      exact (by
        simpa [fiber] using hfiber_mem : cols j ∈ T ∧ chooseRows (cols j) = commonRows).1
    have hchoose_eq : chooseRows (cols j) = commonRows := by
      exact (by
        simpa [fiber] using hfiber_mem : cols j ∈ T ∧ chooseRows (cols j) = commonRows).2
    have htall : BlockTall A k I (cols j) := by
      simpa [T, tallBlocksInRow] using hT_mem
    have hrow_common : rows (π.symm j) ∈ commonRows :=
      Finset.orderEmbOfFin_mem commonRows hcommon_card (π.symm j)
    have hrow_chosen : rows (π.symm j) ∈ chooseRows (cols j) := by
      simpa [hchoose_eq] using hrow_common
    exact chosenActiveRows_subset_active A htall hrow_chosen
  exact hA (contains_permutation_of_common_active_rows π A I cols rows hactive)

/-- Proposition wrapper for Lemma 6. -/
def MarcusTardosLemma6 : Prop :=
  ∀ {q s k : ℕ} (_hk : 0 < k) (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I : Fin q),
    k ≤ (blockRows q s I).card →
      AvoidsPattern A (permutationMatrix π) →
        (tallBlocksInRow A k I).card <
          k * Nat.choose (blockRows q s I).card k

theorem marcusTardosLemma6 : MarcusTardosLemma6 :=
  fun hk π A I hks hA => tallBlocksInRow_card_lt hk π A I hks hA

/-- Marcus--Tardos Lemma 6 with the paper-style bound `k * (s choose k)`,
using that every block row has side length `s`. -/
theorem tallBlocksInRow_card_lt_choose_side {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I : Fin q)
    (hks : k ≤ s)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (tallBlocksInRow A k I).card < k * Nat.choose s k := by
  simpa [blockRows_card I] using
    tallBlocksInRow_card_lt hk π A I (by simpa [blockRows_card I] using hks) hA

/-- Total number of tall blocks, bounded by summing Lemma 6 over all block
rows. -/
theorem tallBlocks_card_le {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (hks : k ≤ s)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (tallBlocks A k).card ≤ q * (k * Nat.choose s k) := by
  classical
  let f : Fin q × Fin q → Fin q := Prod.fst
  have hfiber : ∀ I ∈ (tallBlocks A k).image f,
      ((tallBlocks A k).filter fun p => f p = I).card ≤ k * Nat.choose s k := by
    intro I hI
    have hsub :
        ((tallBlocks A k).filter fun p => f p = I).card ≤
          (tallBlocksInRow A k I).card := by
      let F := (tallBlocks A k).filter fun p => f p = I
      have hcard_image : F.card = (F.image Prod.snd).card := by
        exact (Finset.card_image_of_injOn (s := F) (f := Prod.snd) (by
          intro a ha b hb hab
          have ha' : a ∈ tallBlocks A k ∧ f a = I := by simpa [F] using ha
          have hb' : b ∈ tallBlocks A k ∧ f b = I := by simpa [F] using hb
          ext
          · exact congrArg Fin.val (ha'.2.trans hb'.2.symm)
          · exact congrArg Fin.val hab)).symm
      rw [hcard_image]
      refine Finset.card_le_card ?_
      intro J hJ
      rcases Finset.mem_image.mp hJ with ⟨p, hpF, rfl⟩
      have hp' : p ∈ tallBlocks A k ∧ f p = I := by simpa [F] using hpF
      have htall : BlockTall A k p.1 p.2 := by simpa [tallBlocks] using hp'.1
      simpa [tallBlocksInRow, ← hp'.2] using htall
    exact le_trans hsub (Nat.le_of_lt (tallBlocksInRow_card_lt_choose_side hk π A I hks hA))
  calc
    (tallBlocks A k).card ≤ (k * Nat.choose s k) * ((tallBlocks A k).image f).card :=
      Finset.card_le_mul_card_image (s := tallBlocks A k) (f := f)
        (n := k * Nat.choose s k) hfiber
    _ ≤ (k * Nat.choose s k) * q := by
      exact Nat.mul_le_mul_left _ (by simpa using Finset.card_le_univ ((tallBlocks A k).image f))
    _ = q * (k * Nat.choose s k) := by ring

/-- Proposition wrapper for the global tall-block count obtained by summing
Marcus--Tardos Lemma 6 over all block rows. -/
def MarcusTardosTallBlockCount : Prop :=
  ∀ {q s k : ℕ} (_hk : 0 < k) (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool),
    k ≤ s →
      AvoidsPattern A (permutationMatrix π) →
        (tallBlocks A k).card ≤ q * (k * Nat.choose s k)

theorem marcusTardosTallBlockCount : MarcusTardosTallBlockCount :=
  fun hk π A hks hA => tallBlocks_card_le hk π A hks hA

/- ## Local block-capacity bounds for Lemma 7 -/

/-- A single block contains at most `s^2` true entries. -/
theorem blockEntries_card_le_side_square {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    (blockEntries A I J).card ≤ s ^ 2 := by
  classical
  calc
    (blockEntries A I J).card ≤
        (activeBlockRows A I J).card * (activeBlockCols A I J).card :=
      blockEntries_card_le_active_mul A I J
    _ ≤ (blockRows q s I).card * (blockCols q s J).card :=
      Nat.mul_le_mul
        (Finset.card_le_card (activeBlockRows_subset_blockRows A I J))
        (Finset.card_le_card (activeBlockCols_subset_blockCols A I J))
    _ = s ^ 2 := by
      simp [blockRows_card I, blockCols_card J, pow_two]

/-- In the paper's block size `s = k^2`, a single block has capacity
`k^4`. -/
theorem blockEntries_card_le_paper_side {q k : ℕ}
    (A : _root_.Matrix (Fin (q * k ^ 2)) (Fin (q * k ^ 2)) Bool)
    (I J : Fin q) :
    (blockEntries A I J).card ≤ k ^ 4 := by
  simpa [pow_mul, Nat.pow_mul, pow_two, pow_succ, Nat.mul_assoc] using
    (blockEntries_card_le_side_square A I J)

/-- Entries whose containing block lies in a prescribed block set are bounded
by a uniform per-block capacity times the number of blocks. -/
theorem entriesInBlocks_card_le {q s capacity : ℕ} (hs : 0 < s)
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (Blocks : Finset (Fin q × Fin q))
    (hcap : ∀ b ∈ Blocks, (blockEntries A b.1 b.2).card ≤ capacity) :
    ((oneEntries A).filter fun p => entryBlockIndex p ∈ Blocks).card ≤
      capacity * Blocks.card := by
  classical
  let E := (oneEntries A).filter fun p => entryBlockIndex p ∈ Blocks
  have hfiber : ∀ b ∈ E.image entryBlockIndex,
      (E.filter fun p => entryBlockIndex p = b).card ≤ capacity := by
    intro b hb
    have hbBlocks : b ∈ Blocks := by
      rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
      exact (by
        simpa [E] using hp : p ∈ oneEntries A ∧ entryBlockIndex p ∈ Blocks).2
    refine le_trans (Finset.card_le_card ?_) (hcap b hbBlocks)
    intro p hp
    have hp' : p ∈ E ∧ entryBlockIndex p = b := by
      simpa using hp
    have hpE : p ∈ oneEntries A ∧ entryBlockIndex p ∈ Blocks := by
      simpa [E] using hp'.1
    have htrue : A p.1 p.2 = true := (mem_oneEntries_iff A p).mp hpE.1
    have hrowIndex : blockIndex q s p.1 = b.1 := by
      simpa [entryBlockIndex] using congrArg Prod.fst hp'.2
    have hcolIndex : blockIndex q s p.2 = b.2 := by
      simpa [entryBlockIndex] using congrArg Prod.snd hp'.2
    have hrow : p.1 ∈ blockRows q s b.1 := by
      simpa [hrowIndex] using blockIndex_mem_blockRows (q := q) (s := s) hs p.1
    have hcol : p.2 ∈ blockCols q s b.2 := by
      simpa [hcolIndex] using blockIndex_mem_blockCols (q := q) (s := s) hs p.2
    simp [blockEntries, hrow, hcol, htrue]
  calc
    E.card ≤ capacity * (E.image entryBlockIndex).card :=
      Finset.card_le_mul_card_image (s := E) (f := entryBlockIndex)
        (n := capacity) hfiber
    _ ≤ capacity * Blocks.card := by
      refine Nat.mul_le_mul_left _ (Finset.card_le_card ?_)
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
      exact (by
        simpa [E] using hp : p ∈ oneEntries A ∧ entryBlockIndex p ∈ Blocks).2

/-- Every true entry is charged to a wide block, a tall block, or a nonempty
block that is neither wide nor tall. -/
theorem oneEntries_card_le_block_classification {q s k : ℕ} (hs : 0 < s)
    (hk : 0 < k)
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) :
    (oneEntries A).card ≤
      s ^ 2 * (wideBlocks A k).card +
        s ^ 2 * (tallBlocks A k).card +
          (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card := by
  classical
  let W := (oneEntries A).filter fun p => entryBlockIndex p ∈ wideBlocks A k
  let T := (oneEntries A).filter fun p => entryBlockIndex p ∈ tallBlocks A k
  let N := (oneEntries A).filter fun p => entryBlockIndex p ∈ nonemptyNarrowBlocks A k
  have hcover : oneEntries A ⊆ (W ∪ T) ∪ N := by
    intro p hp
    have htrue : A p.1 p.2 = true := (mem_oneEntries_iff A p).mp hp
    let b := entryBlockIndex p
    have hrow : p.1 ∈ blockRows q s b.1 := by
      simpa [b, entryBlockIndex] using blockIndex_mem_blockRows (q := q) (s := s) hs p.1
    have hcol : p.2 ∈ blockCols q s b.2 := by
      simpa [b, entryBlockIndex] using blockIndex_mem_blockCols (q := q) (s := s) hs p.2
    have hnonempty : BlockNonempty A b.1 b.2 :=
      ⟨p.1, hrow, p.2, hcol, htrue⟩
    by_cases hwide : BlockWide A k b.1 b.2
    · simp [W, b, wideBlocks, hp, hwide]
    · by_cases htall : BlockTall A k b.1 b.2
      · simp [T, b, tallBlocks, hp, htall]
      · simp [N, b, nonemptyNarrowBlocks, hp, hnonempty, hwide, htall]
  have hW : W.card ≤ s ^ 2 * (wideBlocks A k).card :=
    entriesInBlocks_card_le hs A (wideBlocks A k) (by
      intro b _
      exact blockEntries_card_le_side_square A b.1 b.2)
  have hT : T.card ≤ s ^ 2 * (tallBlocks A k).card :=
    entriesInBlocks_card_le hs A (tallBlocks A k) (by
      intro b _
      exact blockEntries_card_le_side_square A b.1 b.2)
  have hN : N.card ≤ (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card :=
    entriesInBlocks_card_le hs A (nonemptyNarrowBlocks A k) (by
      intro b hb
      have hb' : BlockNonempty A b.1 b.2 ∧ ¬ BlockWide A k b.1 b.2 ∧
          ¬ BlockTall A k b.1 b.2 := by
        simpa [nonemptyNarrowBlocks] using hb
      exact blockEntries_card_le_of_not_wide_not_tall hk
        A b.1 b.2 hb'.2.1 hb'.2.2)
  calc
    (oneEntries A).card ≤ ((W ∪ T) ∪ N).card := Finset.card_le_card hcover
    _ ≤ (W ∪ T).card + N.card := Finset.card_union_le (W ∪ T) N
    _ ≤ (W.card + T.card) + N.card := Nat.add_le_add_right (Finset.card_union_le W T) _
    _ ≤ (s ^ 2 * (wideBlocks A k).card + s ^ 2 * (tallBlocks A k).card) +
          (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card :=
      Nat.add_le_add (Nat.add_le_add hW hT) hN
    _ = s ^ 2 * (wideBlocks A k).card +
        s ^ 2 * (tallBlocks A k).card +
          (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card := by ring

/-- Marcus--Tardos Lemma 7: the block recursion for the Füredi--Hajnal
extremal function. -/
theorem furediHajnalRecursion : FurediHajnalRecursion := by
  intro k q P hk hP
  rcases hP with ⟨π, hπ⟩
  have hP_eq : P = permutationMatrix π := by
    ext i j
    exact hπ i j
  subst P
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hs : 0 < k ^ 2 := pow_pos hkpos 2
  have hks : k ≤ k ^ 2 := by
    calc
      k = k * 1 := by ring
      _ ≤ k * k := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hkpos)
      _ = k ^ 2 := by ring
  obtain ⟨A, hA, hcard⟩ :=
    exists_forbiddenExtremal_eq (n := q * k ^ 2) hkpos π
  let C := Nat.choose (k ^ 2) k
  have hclass :
      (oneEntries A).card ≤
        (k ^ 2) ^ 2 * (wideBlocks A k).card +
          (k ^ 2) ^ 2 * (tallBlocks A k).card +
            (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card := by
    simpa using oneEntries_card_le_block_classification
      (q := q) (s := k ^ 2) (k := k) hs hkpos A
  have hwide :
      (wideBlocks A k).card ≤ q * (k * C) := by
    simpa [C] using wideBlocks_card_le hkpos π A hks hA
  have htall :
      (tallBlocks A k).card ≤ q * (k * C) := by
    simpa [C] using tallBlocks_card_le hkpos π A hks hA
  have hnarrow :
      (nonemptyNarrowBlocks A k).card ≤
        forbiddenExtremal (permutationMatrix π) q := by
    exact nonemptyNarrowBlocks_card_le_forbiddenExtremal π A hA
  calc
    forbiddenExtremal (permutationMatrix π) (q * k ^ 2)
        = (oneEntries A).card := hcard.symm
    _ ≤ (k ^ 2) ^ 2 * (wideBlocks A k).card +
          (k ^ 2) ^ 2 * (tallBlocks A k).card +
            (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card := hclass
    _ ≤ (k ^ 2) ^ 2 * (q * (k * C)) +
          (k ^ 2) ^ 2 * (q * (k * C)) +
            (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.mul_le_mul_left _ hwide)
          (Nat.mul_le_mul_left _ htall))
        (Nat.mul_le_mul_left _ hnarrow)
    _ = (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
          2 * k ^ 3 * C * (q * k ^ 2) := by ring
    _ = (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
          2 * k ^ 3 * Nat.choose (k ^ 2) k * (q * k ^ 2) := by simp [C]

theorem furediHajnal_polynomial_factor_le {k : ℕ} (hk : 2 ≤ k) :
    (k - 1) ^ 2 + k + 1 ≤ k ^ 2 := by
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  have hsub : 2 + t - 1 = t + 1 := by omega
  rw [hsub]
  calc
    (t + 1) ^ 2 + (2 + t) + 1 = t ^ 2 + 3 * t + 4 := by ring
    _ ≤ t ^ 2 + 4 * t + 4 := by omega
    _ = (2 + t) ^ 2 := by ring

theorem furediHajnal_base_coefficient_le {k : ℕ} (hk : 2 ≤ k) :
    k ^ 2 ≤ 2 * k ^ 4 * Nat.choose (k ^ 2) k := by
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hs : 0 < k ^ 2 := pow_pos hkpos 2
  have hks : k ≤ k ^ 2 := by
    calc
      k = k * 1 := by ring
      _ ≤ k * k := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hkpos)
      _ = k ^ 2 := by ring
  have hCpos : 0 < Nat.choose (k ^ 2) k := Nat.choose_pos hks
  have hC : 1 ≤ Nat.choose (k ^ 2) k := Nat.succ_le_of_lt hCpos
  have hs1 : 1 ≤ k ^ 2 := Nat.succ_le_of_lt hs
  calc
    k ^ 2 = k ^ 2 * 1 := by ring
    _ ≤ k ^ 2 * k ^ 2 := Nat.mul_le_mul_left _ hs1
    _ = k ^ 4 := by ring
    _ = 1 * k ^ 4 := by ring
    _ ≤ (2 * Nat.choose (k ^ 2) k) * k ^ 4 := by
      exact Nat.mul_le_mul_right _ (by
        calc
          1 ≤ Nat.choose (k ^ 2) k := hC
          _ ≤ 2 * Nat.choose (k ^ 2) k := by
            exact Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
    _ = 2 * k ^ 4 * Nat.choose (k ^ 2) k := by ring

/-- Marcus--Tardos Theorem 8 for a concrete permutation matrix. -/
theorem furediHajnalExplicitBound_permutation {k : ℕ}
    (π : Equiv.Perm (Fin k)) (hk : 2 ≤ k) :
    ∀ n, forbiddenExtremal (permutationMatrix π) n ≤
      2 * k ^ 4 * Nat.choose (k ^ 2) k * n := by
  classical
  let C := Nat.choose (k ^ 2) k
  let B := 2 * k ^ 4 * C
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hs : 0 < k ^ 2 := pow_pos hkpos 2
  have hks : k ≤ k ^ 2 := by
    calc
      k = k * 1 := by ring
      _ ≤ k * k := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hkpos)
      _ = k ^ 2 := by ring
  have hCpos : 0 < C := by
    simpa [C] using Nat.choose_pos hks
  have hC : 1 ≤ C := Nat.succ_le_of_lt hCpos
  have hk2gt1 : 1 < k ^ 2 := by
    calc
      1 < 2 := by decide
      _ ≤ k := hk
      _ ≤ k ^ 2 := hks
  have hpoly : (k - 1) ^ 2 + k + 1 ≤ k ^ 2 :=
    furediHajnal_polynomial_factor_le hk
  have hpoly' : (k - 1) ^ 2 + k ≤ k ^ 2 :=
    le_trans (Nat.le_add_right _ _) hpoly
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n ≤ k ^ 2
      · have hsquare : forbiddenExtremal (permutationMatrix π) n ≤ n * n :=
          forbiddenExtremal_le_square (permutationMatrix π)
        have hnB : n * n ≤ B * n := by
          calc
            n * n ≤ k ^ 2 * n := Nat.mul_le_mul_right n hsmall
            _ ≤ B * n := Nat.mul_le_mul_right n (by
              simpa [B, C] using furediHajnal_base_coefficient_le hk)
        exact le_trans hsquare (by simpa [B, C] using hnB)
      · have hn_gt : k ^ 2 < n := Nat.lt_of_not_ge hsmall
        let q := n / k ^ 2
        let n0 := q * k ^ 2
        have hnpos : 0 < n := lt_trans hs hn_gt
        have hq_lt : q < n := Nat.div_lt_self hnpos hk2gt1
        have hqpos : 0 < q := Nat.div_pos (le_of_lt hn_gt) hs
        have hn0pos : 0 < n0 := Nat.mul_pos hqpos hs
        have hn0le : n0 ≤ n := by
          simpa [n0, q] using Nat.div_mul_le_self n (k ^ 2)
        have hrec :
            forbiddenExtremal (permutationMatrix π) n0 ≤
              (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
                2 * k ^ 3 * C * n0 := by
          simpa [n0, C] using
            furediHajnalRecursion (P := permutationMatrix π) (k := k) (q := q)
              hk (isPermutationMatrix_permutationMatrix π)
        have hiq :
            forbiddenExtremal (permutationMatrix π) q ≤ B * q := ih q hq_lt
        by_cases hrem : n % k ^ 2 = 0
        · have hn_eq : n = n0 := by
            calc
              n = k ^ 2 * (n / k ^ 2) + n % k ^ 2 :=
                (Nat.div_add_mod n (k ^ 2)).symm
              _ = q * k ^ 2 := by simp [q, hrem, Nat.mul_comm]
          rw [hn_eq]
          calc
            forbiddenExtremal (permutationMatrix π) n0 ≤
                (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
                  2 * k ^ 3 * C * n0 := hrec
            _ ≤ (k - 1) ^ 2 * (B * q) + 2 * k ^ 3 * C * n0 := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hiq) _
            _ = 2 * k ^ 4 * C * q * ((k - 1) ^ 2 + k) := by
              simp [B, n0]
              ring
            _ ≤ 2 * k ^ 4 * C * q * (k ^ 2) := by
              exact Nat.mul_le_mul_left _ hpoly'
            _ = B * n0 := by
              simp [B, n0]
              ring
        · have hdecomp : n0 + n % k ^ 2 = n := by
            calc
              n0 + n % k ^ 2 = k ^ 2 * (n / k ^ 2) + n % k ^ 2 := by
                simp [n0, q, Nat.mul_comm]
              _ = n := Nat.div_add_mod n (k ^ 2)
          have hmodpos : 0 < n % k ^ 2 := Nat.pos_of_ne_zero hrem
          have hn0lt : n0 < n := by
            exact lt_of_lt_of_eq (Nat.lt_add_of_pos_right hmodpos) hdecomp
          have hdiff_eq : n - n0 = n % k ^ 2 := by
            calc
              n - n0 = (n0 + n % k ^ 2) - n0 := by rw [hdecomp]
              _ = n % k ^ 2 := Nat.add_sub_cancel_left _ _
          have hdiff_le : n - n0 ≤ k ^ 2 := by
            rw [hdiff_eq]
            exact le_of_lt (Nat.mod_lt n hs)
          have hcrop :
              forbiddenExtremal (permutationMatrix π) n ≤
                forbiddenExtremal (permutationMatrix π) n0 + 2 * (n - n0) * n :=
            forbiddenExtremal_le_crop_add_boundary π hkpos hn0pos hn0le hn0lt
          have hmain :
              (k - 1) ^ 2 * (B * q) + 2 * k ^ 3 * C * n0 ≤
                2 * k ^ 2 * C * ((k - 1) ^ 2 + k) * n := by
            calc
              (k - 1) ^ 2 * (B * q) + 2 * k ^ 3 * C * n0 =
                  2 * k ^ 2 * C * ((k - 1) ^ 2 + k) * n0 := by
                simp [B, n0]
                ring
              _ ≤ 2 * k ^ 2 * C * ((k - 1) ^ 2 + k) * n := by
                exact Nat.mul_le_mul_left _ hn0le
          have hboundary :
              2 * (n - n0) * n ≤ 2 * k ^ 2 * C * n := by
            calc
              2 * (n - n0) * n ≤ 2 * k ^ 2 * n := by
                exact Nat.mul_le_mul_right n (Nat.mul_le_mul_left 2 hdiff_le)
              _ ≤ 2 * k ^ 2 * C * n := by
                exact Nat.mul_le_mul_right n (by
                  calc
                    2 * k ^ 2 = 2 * k ^ 2 * 1 := by ring
                    _ ≤ 2 * k ^ 2 * C := Nat.mul_le_mul_left _ hC)
          calc
            forbiddenExtremal (permutationMatrix π) n ≤
                forbiddenExtremal (permutationMatrix π) n0 + 2 * (n - n0) * n := hcrop
            _ ≤ ((k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
                  2 * k ^ 3 * C * n0) + 2 * (n - n0) * n := by
              exact Nat.add_le_add_right hrec _
            _ ≤ ((k - 1) ^ 2 * (B * q) + 2 * k ^ 3 * C * n0) +
                  2 * (n - n0) * n := by
              exact Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.mul_le_mul_left _ hiq) _) _
            _ ≤ 2 * k ^ 2 * C * ((k - 1) ^ 2 + k) * n + 2 * k ^ 2 * C * n :=
              Nat.add_le_add hmain hboundary
            _ = 2 * k ^ 2 * C * ((k - 1) ^ 2 + k + 1) * n := by ring_nf
            _ ≤ 2 * k ^ 2 * C * (k ^ 2) * n := by
              exact Nat.mul_le_mul_right n (Nat.mul_le_mul_left (2 * k ^ 2 * C) hpoly)
            _ = B * n := by
              change 2 * k ^ 2 * C * (k ^ 2) * n = (2 * k ^ 4 * C) * n
              ring

/-- Marcus--Tardos Theorem 8: the explicit linear Füredi--Hajnal bound. -/
theorem furediHajnalExplicitBound : FurediHajnalExplicitBound := by
  intro k n P hk hP
  rcases hP with ⟨π, hπ⟩
  have hP_eq : P = permutationMatrix π := by
    ext i j
    exact hπ i j
  subst P
  exact furediHajnalExplicitBound_permutation π hk n

/-- The qualitative Füredi--Hajnal theorem, i.e. Theorem 1 of
Marcus--Tardos, obtained from the explicit Section 2 bound. -/
theorem furediHajnalTheorem : FurediHajnalTheorem :=
  furediHajnalTheorem_of_explicitBound furediHajnalExplicitBound

/-- A number `c` is a Marcus-Tardos constant for grid size `t` if density
`c * max n m` forces a `t`-grid minor in every positive-size finite Boolean
matrix.

The explicit `0 < max n m` hypothesis avoids the degenerate `0 × 0` case,
where `c * max n m ≤ 0` is true for every `c` but no positive grid division can
exist. -/
def IsMarcusTardosConstant (t c : ℕ) : Prop :=
  ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
    0 < max n m → c * max n m ≤ (oneEntries M).card → HasGridMinor M t

/-- Marcus--Tardos constants are upward closed. -/
theorem IsMarcusTardosConstant.mono {t c C : ℕ}
    (h : IsMarcusTardosConstant t c) (hc : c ≤ C) :
    IsMarcusTardosConstant t C := by
  intro n m M hpos hden
  exact h M hpos (le_trans (Nat.mul_le_mul_right (max n m) hc) hden)

/-- The Marcus-Tardos theorem in the form needed for the twin-width grid
theorem. -/
def MarcusTardosTheorem : Prop :=
  ∀ t : ℕ, ∃ c : ℕ, IsMarcusTardosConstant t c

/-- The `t = 0` case is immediate from the vacuous grid-minor convention. -/
theorem isMarcusTardosConstant_zero (c : ℕ) :
    IsMarcusTardosConstant 0 c := by
  intro n m M _ _
  exact hasGridMinor_zero M

/-- The all-false `1 × 1` matrix has no positive grid minor. -/
theorem not_hasGridMinor_zeroBoolMatrix_one_of_pos {t : ℕ} (ht : 0 < t) :
    ¬ HasGridMinor (zeroBoolMatrix 1 1) t := by
  intro hgrid
  rcases hgrid with ht0 | hgrid
  · omega
  · rcases hgrid with ⟨R, C, hcell⟩
    let i : Fin t := ⟨0, ht⟩
    let j : Fin t := ⟨0, ht⟩
    rcases hcell i j with ⟨r, _hr, c, _hc, htrue⟩
    simp [zeroBoolMatrix] at htrue

/-- A Marcus--Tardos constant for a positive grid size is positive. -/
theorem IsMarcusTardosConstant.pos {t c : ℕ}
    (hMT : IsMarcusTardosConstant t c) (ht : 0 < t) : 0 < c := by
  by_contra hc
  have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
  have hden : c * max 1 1 ≤ (oneEntries (zeroBoolMatrix 1 1)).card := by
    simp [hc0, oneEntries, zeroBoolMatrix]
  exact not_hasGridMinor_zeroBoolMatrix_one_of_pos ht
    (hMT (zeroBoolMatrix 1 1) (by decide) hden)

/-- The `t = 0` instance of Marcus-Tardos. -/
theorem marcus_tardos_zero : ∃ c : ℕ, IsMarcusTardosConstant 0 c :=
  ⟨0, isMarcusTardosConstant_zero 0⟩

/-- A one-entry witness gives the `t = 1` grid minor.  This is the local base
case used by any full proof of Marcus-Tardos. -/
theorem hasGridMinor_one_of_density_one {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (h : 1 ≤ (oneEntries M).card) :
    HasGridMinor M 1 := by
  exact hasGridMinor_one_of_oneEntries_nonempty M (Finset.card_pos.mp h)

/-- Density `1 * max n m` already forces a `1`-grid minor. -/
theorem isMarcusTardosConstant_one : IsMarcusTardosConstant 1 1 := by
  intro n m M hpos hden
  have hmax : 1 ≤ max n m := Nat.succ_le_of_lt hpos
  have hone : 1 ≤ (oneEntries M).card := by
    calc
      1 ≤ 1 * max n m := by simpa using hmax
      _ ≤ (oneEntries M).card := hden
  exact hasGridMinor_one_of_density_one M hone

/-- The full Marcus-Tardos theorem can be used through this eliminator once its
proof is supplied. -/
theorem marcus_tardos_of_theorem
    (hMT : MarcusTardosTheorem) (t : ℕ) :
    ∃ c : ℕ, IsMarcusTardosConstant t c :=
  hMT t

/- ## Grid-pattern form of Marcus--Tardos -/

/-- The permutation pattern whose `t × t` block division has one `true` entry
in every block.  Under the equivalence `Fin t × Fin t ≃ Fin (t*t)`, it swaps
the two coordinates. -/
def gridPermutation (t : ℕ) : Equiv.Perm (Fin (t * t)) :=
  ((finProdFinEquiv : Fin t × Fin t ≃ Fin (t * t)).symm.trans
      (Equiv.prodComm (Fin t) (Fin t))).trans
    (finProdFinEquiv : Fin t × Fin t ≃ Fin (t * t))

/-- The grid permutation pattern is a permutation matrix. -/
theorem isPermutationMatrix_gridPermutation (t : ℕ) :
    IsPermutationMatrix (permutationMatrix (gridPermutation t)) :=
  isPermutationMatrix_permutationMatrix (gridPermutation t)

/- ### Extending selected grid rows and columns to divisions -/

/-- The row/column index in `Fin (t*t)` corresponding to the grid coordinate
`(i,j)`.  The equivalence `finProdFinEquiv` orders these coordinates by
consecutive row blocks. -/
def gridIndex (t : ℕ) (i j : Fin t) : Fin (t * t) :=
  (finProdFinEquiv : Fin t × Fin t ≃ Fin (t * t)) (i, j)

@[simp] theorem gridIndex_val (t : ℕ) (i j : Fin t) :
    (gridIndex t i j : ℕ) = j.1 + t * i.1 := by
  rfl

@[simp] theorem gridPermutation_gridIndex (t : ℕ) (i j : Fin t) :
    gridPermutation t (gridIndex t i j) = gridIndex t j i := by
  simp [gridPermutation, gridIndex]

theorem gridIndex_le_iff {t : ℕ} {i j a b : Fin t} :
    gridIndex t i j ≤ gridIndex t a b ↔ i < a ∨ i = a ∧ j ≤ b := by
  rw [Fin.le_iff_val_le_val]
  simp [gridIndex]
  have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le j.1) j.2
  have hdiv_left (x y : Fin t) : (y.1 + t * x.1) / t = x.1 := by
    calc
      (y.1 + t * x.1) / t = y.1 / t + x.1 :=
        Nat.add_mul_div_left y.1 x.1 htpos
      _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
      _ = x.1 := by simp
  constructor
  · intro h
    have hia_le : i ≤ a := by
      rw [Fin.le_iff_val_le_val]
      have hdiv := Nat.div_le_div_right (c := t) h
      simpa [hdiv_left] using hdiv
    by_cases hia : i = a
    · right
      refine ⟨hia, ?_⟩
      subst a
      rw [Fin.le_iff_val_le_val]
      omega
    · left
      exact lt_of_le_of_ne hia_le hia
  · rintro (hia | ⟨rfl, hjb⟩)
    · rw [Fin.lt_def] at hia
      have hj_lt : j.1 < t := j.2
      exact le_of_lt <| calc
        j.1 + t * i.1 < t + t * i.1 := Nat.add_lt_add_right hj_lt _
        _ = t * (i.1 + 1) := by ring
        _ ≤ t * a.1 := Nat.mul_le_mul_left t (Nat.succ_le_of_lt hia)
        _ ≤ b.1 + t * a.1 := Nat.le_add_left _ _
    · rw [Fin.le_iff_val_le_val] at hjb
      omega

theorem gridIndex_lt_iff {t : ℕ} {i j a b : Fin t} :
    gridIndex t i j < gridIndex t a b ↔ i < a ∨ i = a ∧ j < b := by
  rw [lt_iff_le_not_ge, gridIndex_le_iff, gridIndex_le_iff]
  constructor
  · rintro ⟨hleft, hnot⟩
    rcases hleft with hia | ⟨rfl, hjb⟩
    · exact Or.inl hia
    · right
      refine ⟨rfl, lt_of_le_of_ne hjb ?_⟩
      intro hbj
      exact hnot (Or.inr ⟨rfl, le_of_eq hbj.symm⟩)
  · rintro (hia | ⟨rfl, hjb⟩)
    · refine ⟨Or.inl hia, ?_⟩
      rintro (hai | ⟨heq, _⟩)
      · exact not_lt_of_ge hia.le hai
      · exact (ne_of_lt hia) heq.symm
    · refine ⟨Or.inr ⟨rfl, hjb.le⟩, ?_⟩
      rintro (hji | ⟨_, hbj⟩)
      · exact (not_lt_of_ge le_rfl) hji
      · exact not_lt_of_ge hbj hjb

/-- Count the number of selected starts not exceeding a row or column.  The
associated division index is this count minus one, with the initial segment
before the first start assigned to block `0`. -/
noncomputable def startDivisionIndex {n t : ℕ} (ht : 0 < t)
    (start : Fin t → Fin n) (x : Fin n) : Fin t :=
  ⟨((Finset.univ.filter fun i : Fin t => start i ≤ x).card - 1), by
    have hcard :
        (Finset.univ.filter fun i : Fin t => start i ≤ x).card ≤ t := by
      calc
        (Finset.univ.filter fun i : Fin t => start i ≤ x).card ≤
            (Finset.univ : Finset (Fin t)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = t := by simp
    omega⟩

theorem startDivisionIndex_mono {n t : ℕ} (ht : 0 < t)
    (start : Fin t → Fin n) :
    ∀ ⦃a b : Fin n⦄, a ≤ b →
      startDivisionIndex ht start a ≤ startDivisionIndex ht start b := by
  intro a b hab
  rw [Fin.le_iff_val_le_val]
  have hsubset :
      (Finset.univ.filter fun i : Fin t => start i ≤ a) ⊆
        (Finset.univ.filter fun i : Fin t => start i ≤ b) := by
    intro i hi
    have hia : start i ≤ a := by simpa using hi
    exact by
      simp [le_trans hia hab]
  exact Nat.sub_le_sub_right (Finset.card_le_card hsubset) 1

theorem starts_filter_eq_Iic {n t : ℕ} {start : Fin t → Fin n}
    (hstart : StrictMono start) (j : Fin t) :
    (Finset.univ.filter fun i : Fin t => start i ≤ start j) = Finset.Iic j := by
  ext i
  constructor
  · intro hi
    have hle : start i ≤ start j := by simpa using hi
    have hij : i ≤ j := by
      by_contra hnot
      have hji : j < i := lt_of_not_ge hnot
      exact (not_lt_of_ge hle) (hstart hji)
    simpa using hij
  · intro hi
    have hij : i ≤ j := by simpa using hi
    simp [hstart.monotone hij]

@[simp] theorem startDivisionIndex_start {n t : ℕ} (ht : 0 < t)
    {start : Fin t → Fin n} (hstart : StrictMono start) (j : Fin t) :
    startDivisionIndex ht start (start j) = j := by
  apply Fin.ext
  change ((Finset.univ.filter fun i : Fin t => start i ≤ start j).card - 1) = j.1
  rw [starts_filter_eq_Iic hstart j]
  simp

/-- A division generated by a strictly increasing sequence of starts.  The
first block also absorbs rows/columns before the first selected start. -/
noncomputable def divisionOfStarts {n t : ℕ} (ht : 0 < t)
    (start : Fin t → Fin n) (hstart : StrictMono start) : Division n t :=
  Division.ofMonotoneSurjective (startDivisionIndex ht start)
    (fun _ _ hab => startDivisionIndex_mono ht start hab)
    (fun j => ⟨start j, startDivisionIndex_start ht hstart j⟩)

@[simp] theorem mem_divisionOfStarts_part {n t : ℕ} (ht : 0 < t)
    {start : Fin t → Fin n} (hstart : StrictMono start)
    (j : Fin t) (x : Fin n) :
    x ∈ (divisionOfStarts ht start hstart).part j ↔
      startDivisionIndex ht start x = j := by
  simp [divisionOfStarts]

theorem start_mem_divisionOfStarts_part {n t : ℕ} (ht : 0 < t)
    {start : Fin t → Fin n} (hstart : StrictMono start) (j : Fin t) :
    start j ∈ (divisionOfStarts ht start hstart).part j := by
  rw [mem_divisionOfStarts_part]
  exact startDivisionIndex_start ht hstart j

theorem grid_row_starts_strictMono {t n : ℕ} (ht : 0 < t)
    (row : Fin (t * t) ↪o Fin n) :
    StrictMono (fun i : Fin t => row (gridIndex t i ⟨0, ht⟩)) := by
  intro i j hij
  exact row.strictMono ((gridIndex_lt_iff).mpr (Or.inl hij))

theorem grid_col_starts_strictMono {t n : ℕ} (ht : 0 < t)
    (col : Fin (t * t) ↪o Fin n) :
    StrictMono (fun j : Fin t => col (gridIndex t j ⟨0, ht⟩)) := by
  intro i j hij
  exact col.strictMono ((gridIndex_lt_iff).mpr (Or.inl hij))

theorem grid_row_selected_mem_part {t n : ℕ} (ht : 0 < t)
    (row : Fin (t * t) ↪o Fin n) (i j : Fin t) :
    row (gridIndex t i j) ∈
      (divisionOfStarts ht
        (fun a : Fin t => row (gridIndex t a ⟨0, ht⟩))
        (grid_row_starts_strictMono ht row)).part i := by
  have hfilter :
      (Finset.univ.filter fun a : Fin t =>
          row (gridIndex t a ⟨0, ht⟩) ≤ row (gridIndex t i j)) =
        Finset.Iic i := by
    ext a
    constructor
    · intro ha
      have hle : gridIndex t a ⟨0, ht⟩ ≤ gridIndex t i j :=
        row.le_iff_le.mp (by simpa using ha)
      rcases (gridIndex_le_iff.mp hle) with hai | ⟨hai, _⟩
      · simpa using hai.le
      · simp [hai]
    · intro ha
      have hai : a ≤ i := by simpa using ha
      have hle : gridIndex t a ⟨0, ht⟩ ≤ gridIndex t i j := by
        rcases lt_or_eq_of_le hai with hai' | rfl
        · exact (gridIndex_le_iff).mpr (Or.inl hai')
        · exact (gridIndex_le_iff).mpr
            (Or.inr ⟨rfl, Fin.le_iff_val_le_val.mpr (Nat.zero_le _)⟩)
      simpa using row.monotone hle
  rw [mem_divisionOfStarts_part]
  apply Fin.ext
  change ((Finset.univ.filter fun a : Fin t =>
    row (gridIndex t a ⟨0, ht⟩) ≤ row (gridIndex t i j)).card - 1) = i.1
  rw [hfilter]
  simp

theorem grid_col_selected_mem_part {t n : ℕ} (ht : 0 < t)
    (col : Fin (t * t) ↪o Fin n) (i j : Fin t) :
    col (gridIndex t j i) ∈
      (divisionOfStarts ht
        (fun b : Fin t => col (gridIndex t b ⟨0, ht⟩))
        (grid_col_starts_strictMono ht col)).part j := by
  simpa using grid_row_selected_mem_part (n := n) ht col j i

/-- Containment of the grid permutation pattern produces the division-based
grid minor used elsewhere in this development. -/
theorem hasGridMinor_of_contains_gridPermutation {t n m : ℕ}
    (ht : 0 < t)
    (A : _root_.Matrix (Fin n) (Fin m) Bool)
    (h : ContainsPattern A (permutationMatrix (gridPermutation t))) :
    HasGridMinor A t := by
  classical
  rcases h with ⟨row, col, hcontains⟩
  refine Or.inr ?_
  let R : Division n t :=
    divisionOfStarts ht
      (fun i : Fin t => row (gridIndex t i ⟨0, ht⟩))
      (grid_row_starts_strictMono ht row)
  let C : Division m t :=
    divisionOfStarts ht
      (fun j : Fin t => col (gridIndex t j ⟨0, ht⟩))
      (grid_col_starts_strictMono ht col)
  refine ⟨R, C, ?_⟩
  intro i j
  refine ⟨row (gridIndex t i j), ?_, col (gridIndex t j i), ?_, ?_⟩
  · exact grid_row_selected_mem_part ht row i j
  · exact grid_col_selected_mem_part ht col i j
  · have hpat :
        permutationMatrix (gridPermutation t) (gridIndex t i j) (gridIndex t j i) = true := by
      simp [permutationMatrix]
    simpa [gridPermutation_gridIndex] using hcontains (gridIndex t i j) (gridIndex t j i) hpat

/-- Pad a rectangular matrix to a square matrix of side `max n m`, filling the
new rows and columns with `false`. -/
def padToSquare {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    _root_.Matrix (Fin (max n m)) (Fin (max n m)) Bool :=
  fun r c =>
    if hr : r.1 < n then
      if hc : c.1 < m then
        M ⟨r.1, hr⟩ ⟨c.1, hc⟩
      else
        false
    else
      false

theorem padToSquare_eq_true_iff {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (r c : Fin (max n m)) :
    padToSquare M r c = true ↔
      ∃ (hr : r.1 < n) (hc : c.1 < m),
        M ⟨r.1, hr⟩ ⟨c.1, hc⟩ = true := by
  unfold padToSquare
  by_cases hr : r.1 < n
  · by_cases hc : c.1 < m
    · simp [hr, hc]
    · simp [hr, hc]
  · simp [hr]

@[simp] theorem padToSquare_castLE {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) (r : Fin n) (c : Fin m) :
    padToSquare M (Fin.castLE (le_max_left n m) r)
      (Fin.castLE (le_max_right n m) c) = M r c := by
  simp [padToSquare]

theorem oneEntries_padToSquare {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    oneEntries (padToSquare M) =
      (oneEntries M).map
        ⟨fun p : Fin n × Fin m =>
          (Fin.castLE (le_max_left n m) p.1, Fin.castLE (le_max_right n m) p.2),
          by
            intro p q hpq
            apply Prod.ext
            · apply Fin.ext
              exact congrArg (fun x : Fin (max n m) × Fin (max n m) => (x.1 : Fin (max n m)).1) hpq
            · apply Fin.ext
              exact congrArg (fun x : Fin (max n m) × Fin (max n m) => (x.2 : Fin (max n m)).1) hpq⟩ := by
  classical
  let e : (Fin n × Fin m) ↪ (Fin (max n m) × Fin (max n m)) :=
    ⟨fun p => (Fin.castLE (le_max_left n m) p.1, Fin.castLE (le_max_right n m) p.2),
      by
        intro p q hpq
        apply Prod.ext
        · apply Fin.ext
          exact congrArg (fun x : Fin (max n m) × Fin (max n m) => (x.1 : Fin (max n m)).1) hpq
        · apply Fin.ext
          exact congrArg (fun x : Fin (max n m) × Fin (max n m) => (x.2 : Fin (max n m)).1) hpq⟩
  change oneEntries (padToSquare M) = (oneEntries M).map e
  ext p
  constructor
  · intro hp
    have hptrue : padToSquare M p.1 p.2 = true := (mem_oneEntries_iff (padToSquare M) p).mp hp
    rcases (padToSquare_eq_true_iff M p.1 p.2).mp hptrue with ⟨hr, hc, hM⟩
    refine Finset.mem_map.mpr ⟨(⟨p.1.1, hr⟩, ⟨p.2.1, hc⟩), ?_, ?_⟩
    · exact (mem_oneEntries_iff M _).mpr hM
    · apply Prod.ext <;> apply Fin.ext <;> rfl
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (mem_oneEntries_iff (padToSquare M) _).mpr (by
      change padToSquare M (Fin.castLE (le_max_left n m) q.1)
        (Fin.castLE (le_max_right n m) q.2) = true
      simpa using (mem_oneEntries_iff M q).mp hq)

@[simp] theorem oneEntries_padToSquare_card {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    (oneEntries (padToSquare M)).card = (oneEntries M).card := by
  rw [oneEntries_padToSquare]
  simp

theorem containsPattern_of_padToSquare_contains_gridPermutation {t n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (h : ContainsPattern (padToSquare M) (permutationMatrix (gridPermutation t))) :
    ContainsPattern M (permutationMatrix (gridPermutation t)) := by
  classical
  rcases h with ⟨row, col, hcontains⟩
  have hrow_inside : ∀ a : Fin (t * t), (row a).1 < n := by
    intro a
    have hpat :
        permutationMatrix (gridPermutation t) a (gridPermutation t a) = true := by
      simp [permutationMatrix]
    have htrue := hcontains a (gridPermutation t a) hpat
    rcases (padToSquare_eq_true_iff M (row a) (col (gridPermutation t a))).mp htrue
      with ⟨hr, _hc, _hM⟩
    exact hr
  have hcol_inside : ∀ b : Fin (t * t), (col b).1 < m := by
    intro b
    let a : Fin (t * t) := (gridPermutation t).symm b
    have hpat : permutationMatrix (gridPermutation t) a b = true := by
      simp [permutationMatrix, a]
    have htrue := hcontains a b hpat
    rcases (padToSquare_eq_true_iff M (row a) (col b)).mp htrue with ⟨_hr, hc, _hM⟩
    exact hc
  let row' : Fin (t * t) ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun a => ⟨(row a).1, hrow_inside a⟩) (by
      intro a b hab
      rw [Fin.lt_def]
      exact row.strictMono hab)
  let col' : Fin (t * t) ↪o Fin m :=
    OrderEmbedding.ofStrictMono (fun a => ⟨(col a).1, hcol_inside a⟩) (by
      intro a b hab
      rw [Fin.lt_def]
      exact col.strictMono hab)
  refine ⟨row', col', ?_⟩
  intro i j hij
  have htrue := hcontains i j hij
  rcases (padToSquare_eq_true_iff M (row i) (col j)).mp htrue with ⟨hr, hc, hM⟩
  simpa [row', col'] using hM

/-- The explicit Füredi--Hajnal constant attached to the grid permutation
pattern of order `t*t`.  We add one in the density theorem below to turn the
non-strict extremal upper bound into a strict contradiction. -/
def gridPatternFurediHajnalConstant (t : ℕ) : ℕ :=
  2 * (t * t) ^ 4 * Nat.choose ((t * t) ^ 2) (t * t)

theorem gridPattern_size_ge_two {t : ℕ} (ht : 2 ≤ t) : 2 ≤ t * t := by
  have htpos : 0 < t := lt_of_lt_of_le (by decide : 0 < 2) ht
  exact le_trans ht (by
    calc
      t = t * 1 := by ring
      _ ≤ t * t := Nat.mul_le_mul_left t (Nat.succ_le_of_lt htpos))

/-- Füredi--Hajnal, specialized to the grid permutation pattern. -/
theorem oneEntries_card_le_gridPatternFurediHajnalConstant {t n : ℕ}
    (ht : 2 ≤ t)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hA : AvoidsPattern A (permutationMatrix (gridPermutation t))) :
    (oneEntries A).card ≤ gridPatternFurediHajnalConstant t * n := by
  calc
    (oneEntries A).card ≤
        forbiddenExtremal (permutationMatrix (gridPermutation t)) n :=
      oneEntries_card_le_forbiddenExtremal (gridPermutation t) A hA
    _ ≤ gridPatternFurediHajnalConstant t * n :=
      furediHajnalExplicitBound (permutationMatrix (gridPermutation t))
        (gridPattern_size_ge_two ht) (isPermutationMatrix_gridPermutation t)

/-- A positive square matrix with density above the Füredi--Hajnal bound
contains the grid permutation pattern.  This is the direct Section 2
Marcus--Tardos/Füredi--Hajnal proof specialized to the pattern used for grid
minors. -/
theorem contains_gridPermutation_of_dense_square {t n : ℕ}
    (ht : 2 ≤ t) (hn : 0 < n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hden : (gridPatternFurediHajnalConstant t + 1) * n ≤ (oneEntries A).card) :
    ContainsPattern A (permutationMatrix (gridPermutation t)) := by
  classical
  by_contra hcontains
  have havoid : AvoidsPattern A (permutationMatrix (gridPermutation t)) := hcontains
  have hupper :
      (oneEntries A).card ≤ gridPatternFurediHajnalConstant t * n :=
    oneEntries_card_le_gridPatternFurediHajnalConstant ht A havoid
  have hstrict :
      gridPatternFurediHajnalConstant t * n <
        (gridPatternFurediHajnalConstant t + 1) * n := by
    exact Nat.mul_lt_mul_of_pos_right
      (Nat.lt_succ_self (gridPatternFurediHajnalConstant t)) hn
  exact (not_le_of_gt (lt_of_lt_of_le hstrict hden)) hupper

/-- Positive-square grid form of Marcus--Tardos.  The theorem is parameterized
by the order-theoretic bridge from containment of the grid permutation pattern
to the division-based `HasGridMinor` predicate. -/
theorem hasGridMinor_of_dense_square
    (hgrid :
      ∀ {t n : ℕ} (A : _root_.Matrix (Fin n) (Fin n) Bool),
        ContainsPattern A (permutationMatrix (gridPermutation t)) → HasGridMinor A t)
    {t n : ℕ} (ht : 2 ≤ t) (hn : 0 < n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hden : (gridPatternFurediHajnalConstant t + 1) * n ≤ (oneEntries A).card) :
    HasGridMinor A t :=
  hgrid A (contains_gridPermutation_of_dense_square ht hn A hden)

/-- Positive-square grid form of Marcus--Tardos with the containment/grid-minor
bridge proved above. -/
theorem hasGridMinor_of_dense_square_explicit {t n : ℕ}
    (ht : 2 ≤ t) (hn : 0 < n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hden : (gridPatternFurediHajnalConstant t + 1) * n ≤ (oneEntries A).card) :
    HasGridMinor A t :=
  hasGridMinor_of_contains_gridPermutation (lt_of_lt_of_le (by decide : 0 < 2) ht) A
    (contains_gridPermutation_of_dense_square ht hn A hden)

/-- The explicit Marcus--Tardos constant obtained from the formalized
Füredi--Hajnal bound and the grid-permutation bridge. -/
theorem isMarcusTardosConstant_gridPattern {t : ℕ} (ht : 2 ≤ t) :
    IsMarcusTardosConstant t (gridPatternFurediHajnalConstant t + 1) := by
  intro n m M hpos hden
  have hpad_den :
      (gridPatternFurediHajnalConstant t + 1) * max n m ≤
        (oneEntries (padToSquare M)).card := by
    simpa using hden
  have hcontains :
      ContainsPattern (padToSquare M) (permutationMatrix (gridPermutation t)) :=
    contains_gridPermutation_of_dense_square ht hpos (padToSquare M) hpad_den
  exact hasGridMinor_of_contains_gridPermutation
    (lt_of_lt_of_le (by decide : 0 < 2) ht) M
    (containsPattern_of_padToSquare_contains_gridPermutation M hcontains)

/-- An explicit Marcus--Tardos constant for the finite rectangular grid-minor
statement.  The cases `0` and `1` are elementary; for `t ≥ 2` this uses the
Füredi--Hajnal constant of the `t × t` grid permutation pattern, plus one to
make the extremal contradiction strict. -/
def marcusTardosConstant (t : ℕ) : ℕ :=
  match t with
  | 0 => 0
  | Nat.succ 0 => 1
  | Nat.succ (Nat.succ s) => gridPatternFurediHajnalConstant (s + 2) + 1

/-- The explicit constant `marcusTardosConstant t` satisfies the
Marcus--Tardos density conclusion for grid size `t`.  This is the most useful
fully explicit interface for downstream bounds. -/
theorem isMarcusTardosConstant_marcusTardosConstant :
    ∀ t : ℕ, IsMarcusTardosConstant t (marcusTardosConstant t) := by
  intro t
  cases t with
  | zero =>
      exact isMarcusTardosConstant_zero 0
  | succ t =>
      cases t with
      | zero =>
          exact isMarcusTardosConstant_one
      | succ s =>
          exact isMarcusTardosConstant_gridPattern (t := s + 2) (by omega)

/-- Marcus--Tardos in the finite rectangular grid-minor form used by the
twin-width proof. -/
theorem marcusTardosTheorem : MarcusTardosTheorem := by
  intro t
  exact ⟨marcusTardosConstant t, isMarcusTardosConstant_marcusTardosConstant t⟩

/-- Direct existential interface for the main Marcus--Tardos statement. -/
theorem marcusTardos (t : ℕ) : ∃ c : ℕ, IsMarcusTardosConstant t c :=
  marcusTardosTheorem t

/-- Contract theorem for `MarcusTardosContract.marcus_tardos_grid_minor_density`.

For every grid order `t`, some constant `c` makes density `c * max n m` force a
`t`-grid minor in every positive-size finite Boolean matrix. -/
theorem marcus_tardos_grid_minor_density :
    ∀ t : ℕ, ∃ c : ℕ,
      ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
        0 < max n m →
          c * max n m ≤ (oneEntries M).card →
            HasGridMinor M t := by
  simpa [MarcusTardosTheorem, IsMarcusTardosConstant] using marcusTardosTheorem

end Matrix
end TwinWidth

/- ===== end Matrix/MarcusTardos.lean ===== -/

/- ===== begin Matrix/TwinWidth.lean ===== -/

/-
# Twin-width of matrices via partition sequences

This file records the Section 5.2 partition-sequence definition of matrix
twin-width.  The definition is intentionally kept in terms of the already
formalized `MatrixPartition` and `ErrorValueAtMost` predicates.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

namespace MatrixPartition

/-- A matrix partition is finest if every row and column part is a singleton
and every singleton occurs. -/
def IsFinest {n m : ℕ} (P : MatrixPartition n m) : Prop :=
  (∀ ⦃R⦄, R ∈ P.rowParts → ∃ r : Fin n, R = {r}) ∧
    (∀ r : Fin n, ({r} : Finset (Fin n)) ∈ P.rowParts) ∧
      (∀ ⦃C⦄, C ∈ P.colParts → ∃ c : Fin m, C = {c}) ∧
        ∀ c : Fin m, ({c} : Finset (Fin m)) ∈ P.colParts

/-- A matrix partition is coarsest if there is at most one row part and at most
one column part.  Empty dimensions are handled by the `≤ 1` convention. -/
def IsCoarsest {n m : ℕ} (P : MatrixPartition n m) : Prop :=
  P.rowParts.card ≤ 1 ∧ P.colParts.card ≤ 1

end MatrixPartition

/-- A concrete matrix contraction sequence of error value at most `d`. -/
structure MatrixContractionSequence {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) where
  /-- Number of partition contractions. -/
  stepCount : ℕ
  /-- Partition at each time. -/
  partition : ℕ → MatrixPartition n m
  /-- The first partition is the singleton partition. -/
  starts : MatrixPartition.IsFinest (partition 0)
  /-- The last partition is the coarsest partition. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Each step contracts one row part or one column part. -/
  step_contracts :
    ∀ i, i < stepCount → MatrixPartition.IsContraction (partition i) (partition (i + 1))
  /-- Every intermediate partition has error value at most `d`. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

/-- A matrix has matrix twin-width at most `d` if it has a partition
contraction sequence whose error value never exceeds `d`. -/
def MatrixTwinWidthAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) : Prop :=
  Nonempty (MatrixContractionSequence M d)

/-- A matrix is `t`-mixed-free if it has no `t`-mixed minor. -/
def MixedFree {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ) : Prop :=
  ¬ HasMixedMinor M t

/-- The matrix-level bound supplied by the second item of Theorem 10. -/
def MatrixTwinWidthBoundedByMixedNumber (f : ℕ → ℕ) : Prop :=
  ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
    MatrixTwinWidthAtMost M (f (matrixMixedNumber M))

end Matrix
end TwinWidth

/- ===== end Matrix/TwinWidth.lean ===== -/

/- ===== begin Matrix/DivisionSequence.lean ===== -/

/-
# Division sequences with bounded mixed value

This file records the formal target of Lemma 13 from Section 5.7.  A matrix
division has a row division and a column division, each with at least one part.
Its mixed value is the maximum of the one-sided mixed values of all row and
column parts.

The proof of Lemma 13 is split into two layers: the local greedy-fusion step,
which uses Marcus--Tardos on the auxiliary matrix of mixed zones, and the
finite descent argument turning that step into a full division sequence.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

/-- The auxiliary matrix whose entries record which zones of a pair of
divisions are mixed. -/
noncomputable def mixedZoneMatrix {n m k l : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m l) :
    _root_.Matrix (Fin k) (Fin l) Bool :=
  by
    classical
    exact fun i j => decide (ZoneMixed M (R.part i) (C.part j))

theorem mixedZoneMatrix_eq_true_iff {n m k l : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m l) (i : Fin k) (j : Fin l) :
    mixedZoneMatrix M R C i j = true ↔ ZoneMixed M (R.part i) (C.part j) := by
  classical
  simp [mixedZoneMatrix]

theorem zoneMixed_of_subset {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R₁ R₂ : Finset (Fin n)} {C₁ C₂ : Finset (Fin m)}
    (hR : R₁ ⊆ R₂) (hC : C₁ ⊆ C₂)
    (hmix : ZoneMixed M R₁ C₁) :
    ZoneMixed M R₂ C₂ := by
  constructor
  · intro hv
    exact hmix.1 (by
      intro r₁ r₂ hr₁ hr₂ c hc
      exact hv (hR hr₁) (hR hr₂) (hC hc))
  · intro hh
    exact hmix.2 (by
      intro r hr c₁ c₂ hc₁ hc₂
      exact hh (hR hr) (hC hc₁) (hC hc₂))

/-- A mixed zone remains mixed after coarsening the column division part that
contains it. -/
theorem zoneMixed_col_coarsen_of_zoneMixed {n m l q : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Division m l} {I : Division l q}
    {a : Fin q} {j : Fin l}
    (hj : j ∈ I.part a)
    (hmix : ZoneMixed M R (C.part j)) :
    ZoneMixed M R ((C.coarsen I).part a) :=
  zoneMixed_of_subset (by intro r hr; exact hr) (C.part_subset_coarsen_part I hj) hmix

/-- A mixed zone remains mixed after coarsening the row division part that
contains it. -/
theorem zoneMixed_row_coarsen_of_zoneMixed {n m k q : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {I : Division k q} {C : Finset (Fin m)}
    {a : Fin q} {i : Fin k}
    (hi : i ∈ I.part a)
    (hmix : ZoneMixed M (R.part i) C) :
    ZoneMixed M ((R.coarsen I).part a) C :=
  zoneMixed_of_subset (R.part_subset_coarsen_part I hi) (by intro c hc; exact hc) hmix

/-- If the two sides of a mixed column cut are grouped into the same coarsened
column part, then the corresponding coarsened zone is mixed. -/
theorem zoneMixed_col_coarsen_of_colCutMixed {n m l q : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Division m (l + 1)} {I : Division (l + 1) q}
    {a : Fin q} {j : Fin l}
    (hj₀ : j.castSucc ∈ I.part a) (hj₁ : j.succ ∈ I.part a)
    (hmix : ColCutMixed M R C j) :
    ZoneMixed M R ((C.coarsen I).part a) := by
  constructor
  · intro hv
    exact hmix.1 ⟨
      (by
        intro r₁ r₂ hr₁ hr₂
        exact hv hr₁ hr₂
          (C.part_subset_coarsen_part I hj₀ (C.last_mem j.castSucc))),
      (by
        intro r₁ r₂ hr₁ hr₂
        exact hv hr₁ hr₂
          (C.part_subset_coarsen_part I hj₁ (C.first_mem j.succ)))⟩
  · intro hh
    exact hmix.2 (by
      intro r hr
      exact hh hr
        (C.part_subset_coarsen_part I hj₀ (C.last_mem j.castSucc))
        (C.part_subset_coarsen_part I hj₁ (C.first_mem j.succ)))

/-- Row-cut version of `zoneMixed_col_coarsen_of_colCutMixed`. -/
theorem zoneMixed_row_coarsen_of_rowCutMixed {n m k q : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n (k + 1)} {I : Division (k + 1) q} {C : Finset (Fin m)}
    {a : Fin q} {i : Fin k}
    (hi₀ : i.castSucc ∈ I.part a) (hi₁ : i.succ ∈ I.part a)
    (hmix : RowCutMixed M R C i) :
    ZoneMixed M ((R.coarsen I).part a) C := by
  constructor
  · intro hv
    exact hmix.1 (by
      intro c hc
      exact hv
        (R.part_subset_coarsen_part I hi₀ (R.last_mem i.castSucc))
        (R.part_subset_coarsen_part I hi₁ (R.first_mem i.succ))
        hc)
  · intro hh
    exact hmix.2 ⟨
      (by
        intro c₁ c₂ hc₁ hc₂
        exact hh
          (R.part_subset_coarsen_part I hi₀ (R.last_mem i.castSucc))
          hc₁ hc₂),
      (by
        intro c₁ c₂ hc₁ hc₂
        exact hh
          (R.part_subset_coarsen_part I hi₁ (R.first_mem i.succ))
          hc₁ hc₂)⟩

/-- A grid minor in the auxiliary mixed-zone matrix induces a mixed minor in
the original matrix by coarsening the row and column divisions. -/
theorem hasMixedMinor_of_mixedZoneMatrix_hasGridMinor {n m k l t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m l}
    (hgrid : HasGridMinor (mixedZoneMatrix M R C) t) :
    HasMixedMinor M t := by
  rcases hgrid with ht | hgrid
  · exact Or.inl ht
  · rcases hgrid with ⟨IR, IC, hcell⟩
    refine Or.inr ⟨R.coarsen IR, C.coarsen IC, ?_⟩
    intro a b
    rcases hcell a b with ⟨i, hi, j, hj, htrue⟩
    have hmix : ZoneMixed M (R.part i) (C.part j) :=
      (mixedZoneMatrix_eq_true_iff M R C i j).mp htrue
    have hR : R.part i ⊆ (R.coarsen IR).part a :=
      R.part_subset_coarsen_part IR hi
    have hC : C.part j ⊆ (C.coarsen IC).part b :=
      C.part_subset_coarsen_part IC hj
    have hbig : ZoneMixed M ((R.coarsen IR).part a) ((C.coarsen IC).part b) :=
      zoneMixed_of_subset hR hC hmix
    simpa [CellMixed, CellVertical, CellHorizontal,
      ZoneMixed, ZoneVertical, ZoneHorizontal] using hbig

/-- Contradiction form used in Lemma 13: a `t`-grid minor in the auxiliary
mixed-zone matrix contradicts `t`-mixed-freeness of the original matrix. -/
theorem mixedFree_not_mixedZoneMatrix_hasGridMinor {n m k l t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m l}
    (hfree : MixedFree M t) :
    ¬ HasGridMinor (mixedZoneMatrix M R C) t := by
  intro hgrid
  exact hfree (hasMixedMinor_of_mixedZoneMatrix_hasGridMinor hgrid)

/-- Marcus--Tardos counting form for the auxiliary mixed-zone matrix: in a
`t`-mixed-free matrix, the auxiliary matrix has fewer than `c * max k l` mixed
zones whenever `c` is a Marcus--Tardos constant for `t`. -/
theorem oneEntries_mixedZoneMatrix_lt_of_mixedFree {n m k l t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m l}
    (hMT : IsMarcusTardosConstant t c)
    (hfree : MixedFree M t)
    (hpos : 0 < max k l) :
    (oneEntries (mixedZoneMatrix M R C)).card < c * max k l := by
  by_contra hnot
  have hden : c * max k l ≤ (oneEntries (mixedZoneMatrix M R C)).card :=
    Nat.le_of_not_gt hnot
  exact mixedFree_not_mixedZoneMatrix_hasGridMinor (R := R) (C := C) hfree
    (hMT (mixedZoneMatrix M R C) hpos hden)

/-- A row/column division of a finite matrix.  The fields `rowCuts` and
`colCuts` are one less than the number of row and column parts; this matches the
`k + 1` indexing used by mixed cuts. -/
structure MatrixDivision (n m : ℕ) where
  /-- One less than the number of row parts. -/
  rowCuts : ℕ
  /-- One less than the number of column parts. -/
  colCuts : ℕ
  /-- Consecutive row parts. -/
  rowDiv : Division n (rowCuts + 1)
  /-- Consecutive column parts. -/
  colDiv : Division m (colCuts + 1)

namespace MatrixDivision

/-- The number of cuts in a matrix division.  A fusion step decreases this
measure by exactly one. -/
def cutCount {n m : ℕ} (D : MatrixDivision n m) : ℕ :=
  D.rowCuts + D.colCuts

/-- The canonical finest matrix division of a positive-size matrix. -/
noncomputable def finest {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    MatrixDivision n m where
  rowCuts := n - 1
  colCuts := m - 1
  rowDiv := Division.castIndex (by omega : n = (n - 1) + 1) (Division.singleton n)
  colDiv := Division.castIndex (by omega : m = (m - 1) + 1) (Division.singleton m)

/-- A matrix division has mixed value at most `d` if every column part has
mixed value at most `d` on the row division, and every row part has mixed value
at most `d` on the column division. -/
def MixedValueAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (d : ℕ) : Prop :=
  (∀ j : Fin (D.colCuts + 1),
      rowMixedValue M D.rowDiv (D.colDiv.part j) ≤ d) ∧
    ∀ i : Fin (D.rowCuts + 1),
      colMixedValue M (D.rowDiv.part i) D.colDiv ≤ d

/-- The finest division: every row part and every column part is a singleton.
The cover field of `Division` then ensures that every row and column appears. -/
def IsFinest {n m : ℕ} (D : MatrixDivision n m) : Prop :=
  (∀ i : Fin (D.rowCuts + 1), ∃ r : Fin n, D.rowDiv.part i = {r}) ∧
    ∀ j : Fin (D.colCuts + 1), ∃ c : Fin m, D.colDiv.part j = {c}

theorem finest_isFinest {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    IsFinest (finest hn hm) := by
  constructor
  · intro i
    simp [finest, Division.castIndex, Division.singleton]
  · intro j
    simp [finest, Division.castIndex, Division.singleton]

/-- The coarsest division: one row part and one column part. -/
def IsCoarsest {n m : ℕ} (D : MatrixDivision n m) : Prop :=
  D.rowCuts = 0 ∧ D.colCuts = 0

/-- A fusion step between divisions.  The first disjunct is a row fusion and
the second is a column fusion; the exact part-identification relation is kept
as the next local API to build on top of Lemma 12. -/
def HasFusionShape {n m : ℕ} (D E : MatrixDivision n m) : Prop :=
  (D.rowCuts = E.rowCuts + 1 ∧ D.colCuts = E.colCuts) ∨
    (D.rowCuts = E.rowCuts ∧ D.colCuts = E.colCuts + 1)

/-- Exact row-fusion data: `E` is obtained from `D` by merging one specified
pair of consecutive row parts and leaving the column division unchanged. -/
def HasRowFusion {n m : ℕ} (D E : MatrixDivision n m) : Prop :=
  ∃ hrow : D.rowCuts = E.rowCuts + 1,
    ∃ hcol : D.colCuts = E.colCuts,
      ∃ i : Fin (E.rowCuts + 1),
        Division.IsFusionAt
          (Division.castIndex (by omega : D.rowCuts + 1 = E.rowCuts + 2) D.rowDiv)
          E.rowDiv i ∧
          ∀ j : Fin (E.colCuts + 1),
            E.colDiv.part j =
              (Division.castIndex (by omega : D.colCuts + 1 = E.colCuts + 1) D.colDiv).part j

/-- Exact column-fusion data, dual to `HasRowFusion`. -/
def HasColFusion {n m : ℕ} (D E : MatrixDivision n m) : Prop :=
  ∃ hrow : D.rowCuts = E.rowCuts,
    ∃ hcol : D.colCuts = E.colCuts + 1,
      ∃ j : Fin (E.colCuts + 1),
        (∀ i : Fin (E.rowCuts + 1),
            E.rowDiv.part i =
              (Division.castIndex (by omega : D.rowCuts + 1 = E.rowCuts + 1) D.rowDiv).part i) ∧
          Division.IsFusionAt
            (Division.castIndex (by omega : D.colCuts + 1 = E.colCuts + 2) D.colDiv)
            E.colDiv j

/-- An exact fusion is either an exact row fusion or an exact column fusion. -/
def HasExactFusion {n m : ℕ} (D E : MatrixDivision n m) : Prop :=
  HasRowFusion D E ∨ HasColFusion D E

/-- Fuse one row cut of a matrix division.  The input index is a boundary
between consecutive row parts. -/
noncomputable def rowFuse {n m : ℕ} (D : MatrixDivision n m)
    (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts) : MatrixDivision n m where
  rowCuts := D.rowCuts - 1
  colCuts := D.colCuts
  rowDiv :=
    (Division.castIndex
      (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv).fuse
        ((finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i)
  colDiv := D.colDiv

/-- Fuse one column cut of a matrix division. -/
noncomputable def colFuse {n m : ℕ} (D : MatrixDivision n m)
    (hcol : 0 < D.colCuts) (j : Fin D.colCuts) : MatrixDivision n m where
  rowCuts := D.rowCuts
  colCuts := D.colCuts - 1
  rowDiv := D.rowDiv
  colDiv :=
    (Division.castIndex
      (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv).fuse
        ((finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j)

/-- Row division obtained by grouping row parts in left pairs
`0,1`, `2,3`, ... with a possible leftover absorbed into the last group. -/
noncomputable def rowPairLeftDiv {n m : ℕ} (D : MatrixDivision n m)
    (hrow : 0 < D.rowCuts) : Division n (Division.pairCount (D.rowCuts + 1)) :=
  D.rowDiv.coarsen
    (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))

/-- Row division obtained by the shifted right pairing. -/
noncomputable def rowPairRightDiv {n m : ℕ} (D : MatrixDivision n m)
    (hrow : 0 < D.rowCuts) : Division n (Division.pairCount (D.rowCuts + 1)) :=
  D.rowDiv.coarsen
    (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega))

/-- Column division obtained by grouping column parts in left pairs. -/
noncomputable def colPairLeftDiv {n m : ℕ} (D : MatrixDivision n m)
    (hcol : 0 < D.colCuts) : Division m (Division.pairCount (D.colCuts + 1)) :=
  D.colDiv.coarsen
    (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))

/-- Column division obtained by grouping column parts in shifted right pairs:
the first part is initially isolated, then `1,2`, `3,4`, ... are grouped,
with a possible tail absorbed into the last group. -/
noncomputable def colPairRightDiv {n m : ℕ} (D : MatrixDivision n m)
    (hcol : 0 < D.colCuts) : Division m (Division.pairCount (D.colCuts + 1)) :=
  D.colDiv.coarsen
    (Division.pairRightIndexDivision (D.colCuts + 1) (by omega))

/-- A mixed column cut is visible as a mixed zone in one of the two paired
column coarsenings. -/
theorem zoneMixed_colPair_of_colCutMixed {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n)) (j : Fin D.colCuts)
    (hmix : ColCutMixed M R D.colDiv j) :
    (∃ a : Fin (Division.pairCount (D.colCuts + 1)),
        ZoneMixed M R ((colPairLeftDiv D hcol).part a)) ∨
      ∃ a : Fin (Division.pairCount (D.colCuts + 1)),
        ZoneMixed M R ((colPairRightDiv D hcol).part a) := by
  let aL : Fin (Division.pairCount (D.colCuts + 1)) :=
    Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j.castSucc
  let aR : Fin (Division.pairCount (D.colCuts + 1)) :=
    Division.pairRightIndex (l := D.colCuts + 1) (by omega) j.castSucc
  rcases Division.pairIndex_adjacent_same_succ hcol j with hleft | hright
  · refine Or.inl ⟨aL, ?_⟩
    have hj₀ :
        j.castSucc ∈
          (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part aL := by
      simp [Division.pairLeftIndexDivision, aL]
    have hj₁ :
        j.succ ∈
          (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part aL := by
      simp [Division.pairLeftIndexDivision, aL, hleft.symm]
    simpa [colPairLeftDiv] using
      zoneMixed_col_coarsen_of_colCutMixed (M := M) (R := R) (C := D.colDiv)
        (I := Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))
        (a := aL) (j := j) hj₀ hj₁ hmix
  · refine Or.inr ⟨aR, ?_⟩
    have hj₀ :
        j.castSucc ∈
          (Division.pairRightIndexDivision (D.colCuts + 1) (by omega)).part aR := by
      simp [Division.pairRightIndexDivision, aR]
    have hj₁ :
        j.succ ∈
          (Division.pairRightIndexDivision (D.colCuts + 1) (by omega)).part aR := by
      simp [Division.pairRightIndexDivision, aR, hright.symm]
    simpa [colPairRightDiv] using
      zoneMixed_col_coarsen_of_colCutMixed (M := M) (R := R) (C := D.colDiv)
        (I := Division.pairRightIndexDivision (D.colCuts + 1) (by omega))
        (a := aR) (j := j) hj₀ hj₁ hmix

/-- A mixed row cut is visible as a mixed zone in one of the two paired row
coarsenings. -/
theorem zoneMixed_rowPair_of_rowCutMixed {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m)) (i : Fin D.rowCuts)
    (hmix : RowCutMixed M D.rowDiv C i) :
    (∃ a : Fin (Division.pairCount (D.rowCuts + 1)),
        ZoneMixed M ((rowPairLeftDiv D hrow).part a) C) ∨
      ∃ a : Fin (Division.pairCount (D.rowCuts + 1)),
        ZoneMixed M ((rowPairRightDiv D hrow).part a) C := by
  let aL : Fin (Division.pairCount (D.rowCuts + 1)) :=
    Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i.castSucc
  let aR : Fin (Division.pairCount (D.rowCuts + 1)) :=
    Division.pairRightIndex (l := D.rowCuts + 1) (by omega) i.castSucc
  rcases Division.pairIndex_adjacent_same_succ hrow i with hleft | hright
  · refine Or.inl ⟨aL, ?_⟩
    have hi₀ :
        i.castSucc ∈
          (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part aL := by
      simp [Division.pairLeftIndexDivision, aL]
    have hi₁ :
        i.succ ∈
          (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part aL := by
      simp [Division.pairLeftIndexDivision, aL, hleft.symm]
    simpa [rowPairLeftDiv] using
      zoneMixed_row_coarsen_of_rowCutMixed (M := M) (R := D.rowDiv)
        (I := Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))
        (C := C) (a := aL) (i := i) hi₀ hi₁ hmix
  · refine Or.inr ⟨aR, ?_⟩
    have hi₀ :
        i.castSucc ∈
          (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega)).part aR := by
      simp [Division.pairRightIndexDivision, aR]
    have hi₁ :
        i.succ ∈
          (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega)).part aR := by
      simp [Division.pairRightIndexDivision, aR, hright.symm]
    simpa [rowPairRightDiv] using
      zoneMixed_row_coarsen_of_rowCutMixed (M := M) (R := D.rowDiv)
        (I := Division.pairRightIndexDivision (D.rowCuts + 1) (by omega))
        (C := C) (a := aR) (i := i) hi₀ hi₁ hmix

/-- Every mixed item of a row set on the column division is visible in one of
the two paired column coarsenings. -/
theorem colMixedItem_visible_pair {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n)) {x : Sum (Fin (D.colCuts + 1)) (Fin D.colCuts)}
    (hx : x ∈ colMixedItems M R D.colDiv) :
    (∃ a : Fin (Division.pairCount (D.colCuts + 1)),
        ZoneMixed M R ((colPairLeftDiv D hcol).part a)) ∨
      ∃ a : Fin (Division.pairCount (D.colCuts + 1)),
        ZoneMixed M R ((colPairRightDiv D hcol).part a) := by
  cases x with
  | inl j =>
      have hmix : ZoneMixed M R (D.colDiv.part j) := by
        simpa using hx
      let a : Fin (Division.pairCount (D.colCuts + 1)) :=
        Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j
      refine Or.inl ⟨a, ?_⟩
      have hj :
          j ∈ (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part a := by
        simp [Division.pairLeftIndexDivision, a]
      simpa [colPairLeftDiv] using
        zoneMixed_col_coarsen_of_zoneMixed (M := M) (R := R) (C := D.colDiv)
          (I := Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))
          (a := a) (j := j) hj hmix
  | inr j =>
      have hmix : ColCutMixed M R D.colDiv j := by
        simpa using hx
      exact zoneMixed_colPair_of_colCutMixed D hcol R j hmix

/-- Row-side version of `colMixedItem_visible_pair`. -/
theorem rowMixedItem_visible_pair {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m)) {x : Sum (Fin (D.rowCuts + 1)) (Fin D.rowCuts)}
    (hx : x ∈ rowMixedItems M D.rowDiv C) :
    (∃ a : Fin (Division.pairCount (D.rowCuts + 1)),
        ZoneMixed M ((rowPairLeftDiv D hrow).part a) C) ∨
      ∃ a : Fin (Division.pairCount (D.rowCuts + 1)),
        ZoneMixed M ((rowPairRightDiv D hrow).part a) C := by
  cases x with
  | inl i =>
      have hmix : ZoneMixed M (D.rowDiv.part i) C := by
        simpa using hx
      let a : Fin (Division.pairCount (D.rowCuts + 1)) :=
        Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i
      refine Or.inl ⟨a, ?_⟩
      have hi :
          i ∈ (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part a := by
        simp [Division.pairLeftIndexDivision, a]
      simpa [rowPairLeftDiv] using
        zoneMixed_row_coarsen_of_zoneMixed (M := M) (R := D.rowDiv)
          (I := Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))
          (C := C) (a := a) (i := i) hi hmix
  | inr i =>
      have hmix : RowCutMixed M D.rowDiv C i := by
        simpa using hx
      exact zoneMixed_rowPair_of_rowCutMixed D hrow C i hmix

/-- The canonical fused part for a left row pair is contained in the
corresponding part of the left paired row coarsening.  The last paired part may
also contain a leftover row part, which is harmless for mixedness because
mixed zones are monotone under enlarging the row set. -/
theorem rowFuse_pairLeft_part_subset {n m : ℕ}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    let i : Fin D.rowCuts := Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
    let fi : Fin ((D.rowCuts - 1) + 1) :=
      (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
    ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) ⊆
      (MatrixDivision.rowPairLeftDiv D hrow).part a := by
  intro i fi x hx
  let Rcast : Division n ((D.rowCuts - 1) + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv
  have hfused :
      (MatrixDivision.rowFuse D hrow i).rowDiv.part fi =
        Rcast.part fi.castSucc ∪ Rcast.part fi.succ := by
    simpa [MatrixDivision.rowFuse, Rcast, fi] using
      Division.fuse_part_self Rcast fi
  rw [hfused] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · refine Finset.mem_biUnion.mpr ⟨(finCongr
        (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm fi.castSucc, ?_, ?_⟩
    · have hidx :
          Division.pairLeftIndex (l := D.rowCuts + 1) (by omega)
              ((finCongr
                (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm fi.castSucc) = a := by
        subst fi
        subst i
        simpa [Division.pairLeftCutIndex] using
          Division.pairLeftIndex_pairLeftCutIndex_castSucc
            (l := D.rowCuts + 1) (by omega) a
      simpa [MatrixDivision.rowPairLeftDiv, Division.pairLeftIndexDivision] using hidx
    · simpa [Rcast, Division.castIndex] using hx
  · refine Finset.mem_biUnion.mpr ⟨(finCongr
        (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm fi.succ, ?_, ?_⟩
    · have hidx :
          Division.pairLeftIndex (l := D.rowCuts + 1) (by omega)
              ((finCongr
                (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm fi.succ) = a := by
        subst fi
        subst i
        simpa [Division.pairLeftCutIndex] using
          Division.pairLeftIndex_pairLeftCutIndex_succ
            (l := D.rowCuts + 1) (by omega) a
      simpa [MatrixDivision.rowPairLeftDiv, Division.pairLeftIndexDivision] using hidx
    · simpa [Rcast, Division.castIndex] using hx

/-- Column-side analogue of `rowFuse_pairLeft_part_subset`. -/
theorem colFuse_pairLeft_part_subset {n m : ℕ}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    let j : Fin D.colCuts := Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) a
    let fj : Fin ((D.colCuts - 1) + 1) :=
      (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
    ((MatrixDivision.colFuse D hcol j).colDiv.part fj) ⊆
      (MatrixDivision.colPairLeftDiv D hcol).part a := by
  intro j fj x hx
  let Ccast : Division m ((D.colCuts - 1) + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv
  have hfused :
      (MatrixDivision.colFuse D hcol j).colDiv.part fj =
        Ccast.part fj.castSucc ∪ Ccast.part fj.succ := by
    simpa [MatrixDivision.colFuse, Ccast, fj] using
      Division.fuse_part_self Ccast fj
  rw [hfused] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · refine Finset.mem_biUnion.mpr ⟨(finCongr
        (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm fj.castSucc, ?_, ?_⟩
    · have hidx :
          Division.pairLeftIndex (l := D.colCuts + 1) (by omega)
              ((finCongr
                (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm fj.castSucc) = a := by
        subst fj
        subst j
        simpa [Division.pairLeftCutIndex] using
          Division.pairLeftIndex_pairLeftCutIndex_castSucc
            (l := D.colCuts + 1) (by omega) a
      simpa [MatrixDivision.colPairLeftDiv, Division.pairLeftIndexDivision] using hidx
    · simpa [Ccast, Division.castIndex] using hx
  · refine Finset.mem_biUnion.mpr ⟨(finCongr
        (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm fj.succ, ?_, ?_⟩
    · have hidx :
          Division.pairLeftIndex (l := D.colCuts + 1) (by omega)
              ((finCongr
                (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm fj.succ) = a := by
        subst fj
        subst j
        simpa [Division.pairLeftCutIndex] using
          Division.pairLeftIndex_pairLeftCutIndex_succ
            (l := D.colCuts + 1) (by omega) a
      simpa [MatrixDivision.colPairLeftDiv, Division.pairLeftIndexDivision] using hidx
    · simpa [Ccast, Division.castIndex] using hx

/-- If no row fusion is good, then every canonical left row-pair fusion has
new row-part mixed value strictly above the bound. -/
theorem colMixedValue_rowPair_gt_of_no_good_row {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (hbad :
      ¬ ∃ hrow' : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
        colMixedValue M
          ((MatrixDivision.rowFuse D hrow' i).rowDiv.part
            ((finCongr
              (by simp [MatrixDivision.rowFuse]; omega :
                D.rowCuts =
                  (MatrixDivision.rowFuse D hrow' i).rowCuts + 1)) i))
          (MatrixDivision.rowFuse D hrow' i).colDiv ≤ d)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    let i : Fin D.rowCuts := Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
    colMixedValue M
      ((MatrixDivision.rowFuse D hrow i).rowDiv.part
        ((finCongr
          (by simp [MatrixDivision.rowFuse]; omega :
            D.rowCuts =
              (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
      (MatrixDivision.rowFuse D hrow i).colDiv > d := by
  intro i
  exact Nat.lt_of_not_ge (by
    intro hle
    exact hbad ⟨hrow, i, hle⟩)

/-- Column-side analogue of `colMixedValue_rowPair_gt_of_no_good_row`. -/
theorem rowMixedValue_colPair_gt_of_no_good_col {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (hbad :
      ¬ ∃ hcol' : 0 < D.colCuts, ∃ j : Fin D.colCuts,
        rowMixedValue M
          (MatrixDivision.colFuse D hcol' j).rowDiv
          ((MatrixDivision.colFuse D hcol' j).colDiv.part
            ((finCongr
              (by simp [MatrixDivision.colFuse]; omega :
                D.colCuts =
                  (MatrixDivision.colFuse D hcol' j).colCuts + 1)) j)) ≤ d)
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    let j : Fin D.colCuts := Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) a
    rowMixedValue M
      (MatrixDivision.colFuse D hcol j).rowDiv
      ((MatrixDivision.colFuse D hcol j).colDiv.part
        ((finCongr
          (by simp [MatrixDivision.colFuse]; omega :
            D.colCuts =
              (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) > d := by
  intro j
  exact Nat.lt_of_not_ge (by
    intro hle
    exact hbad ⟨hcol, j, hle⟩)

/-- Cardinal form of `colMixedValue_rowPair_gt_of_no_good_row`. -/
theorem colMixedItems_rowPair_card_gt_of_no_good_row {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (hbad :
      ¬ ∃ hrow' : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
        colMixedValue M
          ((MatrixDivision.rowFuse D hrow' i).rowDiv.part
            ((finCongr
              (by simp [MatrixDivision.rowFuse]; omega :
                D.rowCuts =
                  (MatrixDivision.rowFuse D hrow' i).rowCuts + 1)) i))
          (MatrixDivision.rowFuse D hrow' i).colDiv ≤ d)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    let i : Fin D.rowCuts := Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
    let fi : Fin ((D.rowCuts - 1) + 1) :=
      (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
    d <
      (colMixedItems M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
        D.colDiv).card := by
  intro i fi
  have hgt := colMixedValue_rowPair_gt_of_no_good_row
    (M := M) D hrow hbad a
  dsimp only at hgt
  have hcard :=
    colMixedItems_card M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) D.colDiv
  rw [hcard]
  simpa [MatrixDivision.rowFuse, i, fi] using hgt

/-- Cardinal form of `rowMixedValue_colPair_gt_of_no_good_col`. -/
theorem rowMixedItems_colPair_card_gt_of_no_good_col {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (hbad :
      ¬ ∃ hcol' : 0 < D.colCuts, ∃ j : Fin D.colCuts,
        rowMixedValue M
          (MatrixDivision.colFuse D hcol' j).rowDiv
          ((MatrixDivision.colFuse D hcol' j).colDiv.part
            ((finCongr
              (by simp [MatrixDivision.colFuse]; omega :
                D.colCuts =
                  (MatrixDivision.colFuse D hcol' j).colCuts + 1)) j)) ≤ d)
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    let j : Fin D.colCuts := Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) a
    let fj : Fin ((D.colCuts - 1) + 1) :=
      (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
    d <
      (rowMixedItems M D.rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part fj)).card := by
  intro j fj
  have hgt := rowMixedValue_colPair_gt_of_no_good_col
    (M := M) D hcol hbad a
  dsimp only at hgt
  have hcard :=
    rowMixedItems_card M D.rowDiv ((MatrixDivision.colFuse D hcol j).colDiv.part fj)
  rw [hcard]
  simpa [MatrixDivision.colFuse, j, fj] using hgt

/-- Mixed targets in the two paired column coarsenings, packaged as one finite
set.  The left summand records mixed zones of the left pairing and the right
summand records mixed zones of the shifted right pairing. -/
noncomputable def colPairedMixedTargets {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n)) :
    Finset (Sum (Fin (Division.pairCount (D.colCuts + 1)))
      (Fin (Division.pairCount (D.colCuts + 1)))) := by
  classical
  exact
    (Finset.univ.filter fun a =>
      ZoneMixed M R ((MatrixDivision.colPairLeftDiv D hcol).part a)).map
        ⟨Sum.inl, by intro a b h; simpa using h⟩ ∪
      (Finset.univ.filter fun a =>
        ZoneMixed M R ((MatrixDivision.colPairRightDiv D hcol).part a)).map
        ⟨Sum.inr, by intro a b h; simpa using h⟩

@[simp] theorem mem_colPairedMixedTargets_left {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n))
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    Sum.inl a ∈ colPairedMixedTargets M D hcol R ↔
      ZoneMixed M R ((MatrixDivision.colPairLeftDiv D hcol).part a) := by
  classical
  simp [colPairedMixedTargets]

@[simp] theorem mem_colPairedMixedTargets_right {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n))
    (a : Fin (Division.pairCount (D.colCuts + 1))) :
    Sum.inr a ∈ colPairedMixedTargets M D hcol R ↔
      ZoneMixed M R ((MatrixDivision.colPairRightDiv D hcol).part a) := by
  classical
  simp [colPairedMixedTargets]

/-- Row-side analogue of `colPairedMixedTargets`. -/
noncomputable def rowPairedMixedTargets {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m)) :
    Finset (Sum (Fin (Division.pairCount (D.rowCuts + 1)))
      (Fin (Division.pairCount (D.rowCuts + 1)))) := by
  classical
  exact
    (Finset.univ.filter fun a =>
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a) C).map
        ⟨Sum.inl, by intro a b h; simpa using h⟩ ∪
      (Finset.univ.filter fun a =>
        ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a) C).map
        ⟨Sum.inr, by intro a b h; simpa using h⟩

@[simp] theorem mem_rowPairedMixedTargets_left {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m))
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    Sum.inl a ∈ rowPairedMixedTargets M D hrow C ↔
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a) C := by
  classical
  simp [rowPairedMixedTargets]

@[simp] theorem mem_rowPairedMixedTargets_right {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m))
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    Sum.inr a ∈ rowPairedMixedTargets M D hrow C ↔
      ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a) C := by
  classical
  simp [rowPairedMixedTargets]

/-- Membership form of `colMixedItem_visible_pair`. -/
theorem exists_mem_colPairedMixedTargets_of_colMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts)
    (R : Finset (Fin n)) {x : Sum (Fin (D.colCuts + 1)) (Fin D.colCuts)}
    (hx : x ∈ colMixedItems M R D.colDiv) :
    ∃ y, y ∈ colPairedMixedTargets M D hcol R := by
  rcases MatrixDivision.colMixedItem_visible_pair D hcol R hx with hleft | hright
  · rcases hleft with ⟨a, ha⟩
    exact ⟨Sum.inl a, by simpa using ha⟩
  · rcases hright with ⟨a, ha⟩
    exact ⟨Sum.inr a, by simpa using ha⟩

/-- Membership form of `rowMixedItem_visible_pair`. -/
theorem exists_mem_rowPairedMixedTargets_of_rowMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts)
    (C : Finset (Fin m)) {x : Sum (Fin (D.rowCuts + 1)) (Fin D.rowCuts)}
    (hx : x ∈ rowMixedItems M D.rowDiv C) :
    ∃ y, y ∈ rowPairedMixedTargets M D hrow C := by
  rcases MatrixDivision.rowMixedItem_visible_pair D hrow C hx with hleft | hright
  · rcases hleft with ⟨a, ha⟩
    exact ⟨Sum.inl a, by simpa using ha⟩
  · rcases hright with ⟨a, ha⟩
    exact ⟨Sum.inr a, by simpa using ha⟩

/-- A finite-fiber counting lemma for paired item targets.  If every source
zone/cut item is charged to an allowed paired target, then there are at least
one tenth as many allowed targets. -/
theorem pairedItem_card_le_ten_mul_target_card {k : ℕ} (hk : 0 < k)
    (S : Finset (Sum (Fin (k + 1)) (Fin k)))
    (T : Finset
      (Sum (Fin (Division.pairCount (k + 1)))
        (Fin (Division.pairCount (k + 1)))))
    (hmem : ∀ ⦃x⦄, x ∈ S → Division.pairedItemTargetSucc hk x ∈ T) :
    S.card ≤ 10 * T.card := by
  classical
  let f : Sum (Fin (k + 1)) (Fin k) →
      Sum (Fin (Division.pairCount (k + 1)))
          (Fin (Division.pairCount (k + 1))) × Fin 10 :=
    fun x => (Division.pairedItemTargetSucc hk x, Division.pairedItemCodeSucc hk x)
  have hmaps : Set.MapsTo f S (T.product (Finset.univ : Finset (Fin 10))) := by
    intro x hx
    simp [f, hmem hx]
  have hinj : (S : Set (Sum (Fin (k + 1)) (Fin k))).InjOn f := by
    intro x _hx y _hy hxy
    exact Division.pairedItemTargetSucc_code_injective hk hxy
  calc
    S.card ≤ (T.product (Finset.univ : Finset (Fin 10))).card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    _ = T.card * 10 := by simp
    _ = 10 * T.card := by omega

/-- The two auxiliary mixed-zone matrices used when row pairs are the rows:
the left summand is the matrix for the left column pairing and the right
summand is the matrix for the shifted right column pairing. -/
noncomputable def rowPairAuxTargets {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts) :
    Finset (Fin (Division.pairCount (D.rowCuts + 1)) ×
      Sum (Fin (Division.pairCount (D.colCuts + 1)))
        (Fin (Division.pairCount (D.colCuts + 1)))) := by
  classical
  exact
    (oneEntries
      (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
        (MatrixDivision.colPairLeftDiv D hcol))).map
        ⟨fun p => (p.1, Sum.inl p.2), by
          intro a b h
          cases a with
          | mk ar ac =>
              cases b with
              | mk br bc =>
                  simp at h
                  exact Prod.ext h.1 h.2⟩ ∪
      (oneEntries
        (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
          (MatrixDivision.colPairRightDiv D hcol))).map
        ⟨fun p => (p.1, Sum.inr p.2), by
          intro a b h
          cases a with
          | mk ar ac =>
              cases b with
              | mk br bc =>
                  simp at h
                  exact Prod.ext h.1 h.2⟩

@[simp] theorem mem_rowPairAuxTargets_left {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    (a, Sum.inl b) ∈ rowPairAuxTargets M D hrow hcol ↔
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
        ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
  classical
  simp [rowPairAuxTargets, oneEntries, mixedZoneMatrix]

@[simp] theorem mem_rowPairAuxTargets_right {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    (a, Sum.inr b) ∈ rowPairAuxTargets M D hrow hcol ↔
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
        ((MatrixDivision.colPairRightDiv D hcol).part b) := by
  classical
  simp [rowPairAuxTargets, oneEntries, mixedZoneMatrix]

/-- Marcus--Tardos upper bound for the two row-pair auxiliary matrices. -/
theorem rowPairAuxTargets_card_lt {n m t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (hMT : IsMarcusTardosConstant t c) (hfree : MixedFree M t) :
    (rowPairAuxTargets M D hrow hcol).card <
      c * max (Division.pairCount (D.rowCuts + 1))
          (Division.pairCount (D.colCuts + 1)) +
        c * max (Division.pairCount (D.rowCuts + 1))
          (Division.pairCount (D.colCuts + 1)) := by
  classical
  have hpos :
      0 < max (Division.pairCount (D.rowCuts + 1))
        (Division.pairCount (D.colCuts + 1)) := by
    have hp : 0 < Division.pairCount (D.rowCuts + 1) :=
      Division.pairCount_pos (by omega)
    exact lt_of_lt_of_le hp (le_max_left _ _)
  have hleft :=
    oneEntries_mixedZoneMatrix_lt_of_mixedFree
      (M := M) (R := MatrixDivision.rowPairLeftDiv D hrow)
      (C := MatrixDivision.colPairLeftDiv D hcol) hMT hfree hpos
  have hright :=
    oneEntries_mixedZoneMatrix_lt_of_mixedFree
      (M := M) (R := MatrixDivision.rowPairLeftDiv D hrow)
      (C := MatrixDivision.colPairRightDiv D hcol) hMT hfree hpos
  have hcard :
      (rowPairAuxTargets M D hrow hcol).card =
        (oneEntries
          (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
            (MatrixDivision.colPairLeftDiv D hcol))).card +
          (oneEntries
            (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
              (MatrixDivision.colPairRightDiv D hcol))).card := by
    rw [rowPairAuxTargets, Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      intro x hx hy
      simp at hx hy
      rcases hx with ⟨a, _ha, hxa⟩
      rcases hy with ⟨b, _hb, hyb⟩
      cases hxa.2.trans hyb.2.symm
  rw [hcard]
  exact Nat.add_lt_add hleft hright

/-- A mixed item of the fused row pair contributes a mixed entry to one of the
two row-pair auxiliary matrices. -/
theorem exists_mem_rowPairAuxTargets_of_rowPair_colMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    {x : Sum (Fin (D.colCuts + 1)) (Fin D.colCuts)}
    (hx :
      let i : Fin D.rowCuts :=
        Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
      let fi : Fin ((D.rowCuts - 1) + 1) :=
        (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
      x ∈ colMixedItems M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
        D.colDiv) :
    ∃ y,
      (a, y) ∈ rowPairAuxTargets M D hrow hcol := by
  dsimp only at hx
  let i : Fin D.rowCuts :=
    Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hsubset :
      ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) ⊆
        (MatrixDivision.rowPairLeftDiv D hrow).part a := by
    simpa [i, fi] using MatrixDivision.rowFuse_pairLeft_part_subset D hrow a
  rcases MatrixDivision.colMixedItem_visible_pair D hcol
      ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) hx with hleft | hright
  · rcases hleft with ⟨b, hb⟩
    refine ⟨Sum.inl b, ?_⟩
    have hbig :
        ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
          ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
      zoneMixed_of_subset hsubset (by intro c hc; exact hc) hb
    simpa using hbig
  · rcases hright with ⟨b, hb⟩
    refine ⟨Sum.inr b, ?_⟩
    have hbig :
        ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
          ((MatrixDivision.colPairRightDiv D hcol).part b) :=
      zoneMixed_of_subset hsubset (by intro c hc; exact hc) hb
    simpa using hbig

/-- Deterministic version of
`exists_mem_rowPairAuxTargets_of_rowPair_colMixedItem`, using the paired target
map from `Division`. -/
theorem pairedItemTarget_mem_rowPairAuxTargets_of_rowPair_colMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    {x : Sum (Fin (D.colCuts + 1)) (Fin D.colCuts)}
    (hx :
      let i : Fin D.rowCuts :=
        Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
      let fi : Fin ((D.rowCuts - 1) + 1) :=
        (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
      x ∈ colMixedItems M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
        D.colDiv) :
    (a, Division.pairedItemTargetSucc hcol x) ∈ rowPairAuxTargets M D hrow hcol := by
  classical
  dsimp only at hx
  let i : Fin D.rowCuts :=
    Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hsubset :
      ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi) ⊆
        (MatrixDivision.rowPairLeftDiv D hrow).part a := by
    simpa [i, fi] using MatrixDivision.rowFuse_pairLeft_part_subset D hrow a
  cases x with
  | inl j =>
      have hmix : ZoneMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
          (D.colDiv.part j) := by
        simpa using hx
      let b : Fin (Division.pairCount (D.colCuts + 1)) :=
        Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j
      have hj :
          j ∈ (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part b := by
        simp [Division.pairLeftIndexDivision, b]
      have hcolmix :
          ZoneMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
            ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
        simpa [MatrixDivision.colPairLeftDiv] using
          zoneMixed_col_coarsen_of_zoneMixed (M := M)
            (R := (MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
            (C := D.colDiv)
            (I := Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))
            (a := b) (j := j) hj hmix
      have hbig :
          ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
            ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
        zoneMixed_of_subset hsubset (by intro c hc; exact hc) hcolmix
      simpa [Division.pairedItemTargetSucc_zone, b] using hbig
  | inr j =>
      have hmix : ColCutMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
          D.colDiv j := by
        simpa using hx
      by_cases hleft :
          Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j.castSucc =
            Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j.succ
      · let b : Fin (Division.pairCount (D.colCuts + 1)) :=
          Division.pairLeftIndex (l := D.colCuts + 1) (by omega) j.succ
        have hj₀ :
            j.castSucc ∈
              (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part b := by
          simp [Division.pairLeftIndexDivision, b, hleft]
        have hj₁ :
            j.succ ∈
              (Division.pairLeftIndexDivision (D.colCuts + 1) (by omega)).part b := by
          simp [Division.pairLeftIndexDivision, b]
        have hcolmix :
            ZoneMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
              ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
          simpa [MatrixDivision.colPairLeftDiv] using
            zoneMixed_col_coarsen_of_colCutMixed (M := M)
              (R := (MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
              (C := D.colDiv)
              (I := Division.pairLeftIndexDivision (D.colCuts + 1) (by omega))
              (a := b) (j := j) hj₀ hj₁ hmix
        have hbig :
            ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
              ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
          zoneMixed_of_subset hsubset (by intro c hc; exact hc) hcolmix
        simpa [Division.pairedItemTargetSucc_cut_left hcol j hleft, b] using hbig
      · have hright :
            Division.pairRightIndex (l := D.colCuts + 1) (by omega) j.castSucc =
              Division.pairRightIndex (l := D.colCuts + 1) (by omega) j.succ := by
          rcases Division.pairIndex_adjacent_same_succ hcol j with h | h
          · exact False.elim (hleft h)
          · exact h
        let b : Fin (Division.pairCount (D.colCuts + 1)) :=
          Division.pairRightIndex (l := D.colCuts + 1) (by omega) j.castSucc
        have hj₀ :
            j.castSucc ∈
              (Division.pairRightIndexDivision (D.colCuts + 1) (by omega)).part b := by
          simp [Division.pairRightIndexDivision, b]
        have hj₁ :
            j.succ ∈
              (Division.pairRightIndexDivision (D.colCuts + 1) (by omega)).part b := by
          simp [Division.pairRightIndexDivision, b, hright.symm]
        have hcolmix :
            ZoneMixed M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
              ((MatrixDivision.colPairRightDiv D hcol).part b) := by
          simpa [MatrixDivision.colPairRightDiv] using
            zoneMixed_col_coarsen_of_colCutMixed (M := M)
              (R := (MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
              (C := D.colDiv)
              (I := Division.pairRightIndexDivision (D.colCuts + 1) (by omega))
              (a := b) (j := j) hj₀ hj₁ hmix
        have hbig :
            ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
              ((MatrixDivision.colPairRightDiv D hcol).part b) :=
          zoneMixed_of_subset hsubset (by intro c hc; exact hc) hcolmix
        simpa [Division.pairedItemTargetSucc_cut_right hcol j hleft, b] using hbig

/-- The row-pair auxiliary entries in a fixed paired row. -/
noncomputable def rowPairAuxFiber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    Finset
      (Sum (Fin (Division.pairCount (D.colCuts + 1)))
        (Fin (Division.pairCount (D.colCuts + 1)))) := by
  classical
  exact Finset.univ.filter fun y => (a, y) ∈ rowPairAuxTargets M D hrow hcol

theorem colMixedItems_rowPair_card_le_ten_mul_rowPairAuxFiber_card {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1))) :
    let i : Fin D.rowCuts :=
      Division.pairLeftCutIndex (l := D.rowCuts + 1) (by omega) a
    let fi : Fin ((D.rowCuts - 1) + 1) :=
      (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
    (colMixedItems M ((MatrixDivision.rowFuse D hrow i).rowDiv.part fi)
        D.colDiv).card ≤
      10 * (rowPairAuxFiber M D hrow hcol a).card := by
  intro i fi
  apply pairedItem_card_le_ten_mul_target_card hcol
  intro x hx
  simp [rowPairAuxFiber]
  exact pairedItemTarget_mem_rowPairAuxTargets_of_rowPair_colMixedItem
    D hrow hcol a (by simpa [i, fi] using hx)

theorem rowPairAuxTargets_card_gt_of_fibers_gt {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (h :
      ∀ a : Fin (Division.pairCount (D.rowCuts + 1)),
        d < (rowPairAuxFiber M D hrow hcol a).card) :
    Division.pairCount (D.rowCuts + 1) * d <
      (rowPairAuxTargets M D hrow hcol).card := by
  classical
  let p := Division.pairCount (D.rowCuts + 1)
  let Y :=
    Sum (Fin (Division.pairCount (D.colCuts + 1)))
      (Fin (Division.pairCount (D.colCuts + 1)))
  let P : Finset (Fin p × Y) := rowPairAuxTargets M D hrow hcol
  let A := Sigma fun a : Fin p => {y : Y // y ∈ rowPairAuxFiber M D hrow hcol a}
  have hcardA :
      Fintype.card A =
        ∑ a : Fin p, (rowPairAuxFiber M D hrow hcol a).card := by
    simp [A]
  have hle : Fintype.card A ≤ P.card := by
    let f : A → {z : Fin p × Y // z ∈ P} := fun z =>
      ⟨(z.1, z.2.1), by
        have hz := z.2.2
        change z.2.1 ∈
          (Finset.univ.filter fun y => (z.1, y) ∈ rowPairAuxTargets M D hrow hcol) at hz
        simpa [P] using (Finset.mem_filter.mp hz).2⟩
    have hinj : Function.Injective f := by
      intro u v huv
      cases u with
      | mk a ya =>
          cases v with
          | mk b yb =>
              have hval := congrArg Subtype.val huv
              simp [f] at hval
              cases hval.1
              cases ya with
              | mk y hy =>
                  cases yb with
                  | mk z hz =>
                      simp at hval
                      subst z
                      rfl
    have hcard := Fintype.card_le_of_injective f hinj
    simpa [P] using hcard
  have hsum_le :
      ∑ _a : Fin p, (d + 1) ≤
        ∑ a : Fin p, (rowPairAuxFiber M D hrow hcol a).card := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin p)))
        (fun a _ha => Nat.succ_le_of_lt (h a)))
  have hp : 0 < p := Division.pairCount_pos (by omega)
  have hmul : p * d < p * (d + 1) :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self d) hp
  have hlt_sum :
      p * d < ∑ a : Fin p, (rowPairAuxFiber M D hrow hcol a).card := by
    refine lt_of_lt_of_le ?_ hsum_le
    simpa [p, Finset.sum_const, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hmul
  have hlt_A : p * d < Fintype.card A := by
    simpa [hcardA] using hlt_sum
  exact lt_of_lt_of_le (by simpa [p, P] using hlt_A) hle

/-- The two auxiliary mixed-zone matrices used when column pairs are the
columns, dual to `rowPairAuxTargets`. -/
noncomputable def colPairAuxTargets {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts) :
    Finset (Sum (Fin (Division.pairCount (D.rowCuts + 1)))
        (Fin (Division.pairCount (D.rowCuts + 1))) ×
      Fin (Division.pairCount (D.colCuts + 1))) := by
  classical
  exact
    (oneEntries
      (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
        (MatrixDivision.colPairLeftDiv D hcol))).map
        ⟨fun p => (Sum.inl p.1, p.2), by
          intro a b h
          cases a with
          | mk ar ac =>
              cases b with
              | mk br bc =>
                  simp at h
                  exact Prod.ext h.1 h.2⟩ ∪
      (oneEntries
        (mixedZoneMatrix M (MatrixDivision.rowPairRightDiv D hrow)
          (MatrixDivision.colPairLeftDiv D hcol))).map
        ⟨fun p => (Sum.inr p.1, p.2), by
          intro a b h
          cases a with
          | mk ar ac =>
              cases b with
              | mk br bc =>
                  simp at h
                  exact Prod.ext h.1 h.2⟩

@[simp] theorem mem_colPairAuxTargets_left {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    (Sum.inl a, b) ∈ colPairAuxTargets M D hrow hcol ↔
      ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
        ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
  classical
  simp [colPairAuxTargets, oneEntries, mixedZoneMatrix]

@[simp] theorem mem_colPairAuxTargets_right {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (a : Fin (Division.pairCount (D.rowCuts + 1)))
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    (Sum.inr a, b) ∈ colPairAuxTargets M D hrow hcol ↔
      ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a)
        ((MatrixDivision.colPairLeftDiv D hcol).part b) := by
  classical
  simp [colPairAuxTargets, oneEntries, mixedZoneMatrix]

/-- Marcus--Tardos upper bound for the two column-pair auxiliary matrices. -/
theorem colPairAuxTargets_card_lt {n m t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (hMT : IsMarcusTardosConstant t c) (hfree : MixedFree M t) :
    (colPairAuxTargets M D hrow hcol).card <
      c * max (Division.pairCount (D.rowCuts + 1))
          (Division.pairCount (D.colCuts + 1)) +
        c * max (Division.pairCount (D.rowCuts + 1))
          (Division.pairCount (D.colCuts + 1)) := by
  classical
  have hpos :
      0 < max (Division.pairCount (D.rowCuts + 1))
        (Division.pairCount (D.colCuts + 1)) := by
    have hp : 0 < Division.pairCount (D.colCuts + 1) :=
      Division.pairCount_pos (by omega)
    exact lt_of_lt_of_le hp (le_max_right _ _)
  have hleft :=
    oneEntries_mixedZoneMatrix_lt_of_mixedFree
      (M := M) (R := MatrixDivision.rowPairLeftDiv D hrow)
      (C := MatrixDivision.colPairLeftDiv D hcol) hMT hfree hpos
  have hright :=
    oneEntries_mixedZoneMatrix_lt_of_mixedFree
      (M := M) (R := MatrixDivision.rowPairRightDiv D hrow)
      (C := MatrixDivision.colPairLeftDiv D hcol) hMT hfree hpos
  have hcard :
      (colPairAuxTargets M D hrow hcol).card =
        (oneEntries
          (mixedZoneMatrix M (MatrixDivision.rowPairLeftDiv D hrow)
            (MatrixDivision.colPairLeftDiv D hcol))).card +
          (oneEntries
            (mixedZoneMatrix M (MatrixDivision.rowPairRightDiv D hrow)
              (MatrixDivision.colPairLeftDiv D hcol))).card := by
    rw [colPairAuxTargets, Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      intro x hx hy
      simp at hx hy
      rcases hx with ⟨a, _ha, hxa⟩
      rcases hy with ⟨b, _hb, hyb⟩
      cases hxa.2.trans hyb.2.symm
  rw [hcard]
  exact Nat.add_lt_add hleft hright

/-- Column-side analogue of
`exists_mem_rowPairAuxTargets_of_rowPair_colMixedItem`. -/
theorem exists_mem_colPairAuxTargets_of_colPair_rowMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (b : Fin (Division.pairCount (D.colCuts + 1)))
    {x : Sum (Fin (D.rowCuts + 1)) (Fin D.rowCuts)}
    (hx :
      let j : Fin D.colCuts :=
        Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
      let fj : Fin ((D.colCuts - 1) + 1) :=
        (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
      x ∈ rowMixedItems M D.rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part fj)) :
    ∃ y,
      (y, b) ∈ colPairAuxTargets M D hrow hcol := by
  dsimp only at hx
  let j : Fin D.colCuts :=
    Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hsubset :
      ((MatrixDivision.colFuse D hcol j).colDiv.part fj) ⊆
        (MatrixDivision.colPairLeftDiv D hcol).part b := by
    simpa [j, fj] using MatrixDivision.colFuse_pairLeft_part_subset D hcol b
  rcases MatrixDivision.rowMixedItem_visible_pair D hrow
      ((MatrixDivision.colFuse D hcol j).colDiv.part fj) hx with hleft | hright
  · rcases hleft with ⟨a, ha⟩
    refine ⟨Sum.inl a, ?_⟩
    have hbig :
        ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
          ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
      zoneMixed_of_subset (by intro r hr; exact hr) hsubset ha
    simpa using hbig
  · rcases hright with ⟨a, ha⟩
    refine ⟨Sum.inr a, ?_⟩
    have hbig :
        ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a)
          ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
      zoneMixed_of_subset (by intro r hr; exact hr) hsubset ha
    simpa using hbig

/-- Column-side deterministic paired-target membership. -/
theorem pairedItemTarget_mem_colPairAuxTargets_of_colPair_rowMixedItem {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (b : Fin (Division.pairCount (D.colCuts + 1)))
    {x : Sum (Fin (D.rowCuts + 1)) (Fin D.rowCuts)}
    (hx :
      let j : Fin D.colCuts :=
        Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
      let fj : Fin ((D.colCuts - 1) + 1) :=
        (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
      x ∈ rowMixedItems M D.rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part fj)) :
    (Division.pairedItemTargetSucc hrow x, b) ∈ colPairAuxTargets M D hrow hcol := by
  classical
  dsimp only at hx
  let j : Fin D.colCuts :=
    Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hsubset :
      ((MatrixDivision.colFuse D hcol j).colDiv.part fj) ⊆
        (MatrixDivision.colPairLeftDiv D hcol).part b := by
    simpa [j, fj] using MatrixDivision.colFuse_pairLeft_part_subset D hcol b
  cases x with
  | inl i =>
      have hmix : ZoneMixed M (D.rowDiv.part i)
          ((MatrixDivision.colFuse D hcol j).colDiv.part fj) := by
        simpa using hx
      let a : Fin (Division.pairCount (D.rowCuts + 1)) :=
        Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i
      have hi :
          i ∈ (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part a := by
        simp [Division.pairLeftIndexDivision, a]
      have hrowmix :
          ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
            ((MatrixDivision.colFuse D hcol j).colDiv.part fj) := by
        simpa [MatrixDivision.rowPairLeftDiv] using
          zoneMixed_row_coarsen_of_zoneMixed (M := M)
            (R := D.rowDiv)
            (I := Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))
            (C := (MatrixDivision.colFuse D hcol j).colDiv.part fj)
            (a := a) (i := i) hi hmix
      have hbig :
          ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
            ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
        zoneMixed_of_subset (by intro r hr; exact hr) hsubset hrowmix
      simpa [Division.pairedItemTargetSucc_zone, a] using hbig
  | inr i =>
      have hmix : RowCutMixed M D.rowDiv
          ((MatrixDivision.colFuse D hcol j).colDiv.part fj) i := by
        simpa using hx
      by_cases hleft :
          Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i.castSucc =
            Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i.succ
      · let a : Fin (Division.pairCount (D.rowCuts + 1)) :=
          Division.pairLeftIndex (l := D.rowCuts + 1) (by omega) i.succ
        have hi₀ :
            i.castSucc ∈
              (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part a := by
          simp [Division.pairLeftIndexDivision, a, hleft]
        have hi₁ :
            i.succ ∈
              (Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega)).part a := by
          simp [Division.pairLeftIndexDivision, a]
        have hrowmix :
            ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
              ((MatrixDivision.colFuse D hcol j).colDiv.part fj) := by
          simpa [MatrixDivision.rowPairLeftDiv] using
            zoneMixed_row_coarsen_of_rowCutMixed (M := M)
              (R := D.rowDiv)
              (I := Division.pairLeftIndexDivision (D.rowCuts + 1) (by omega))
              (C := (MatrixDivision.colFuse D hcol j).colDiv.part fj)
              (a := a) (i := i) hi₀ hi₁ hmix
        have hbig :
            ZoneMixed M ((MatrixDivision.rowPairLeftDiv D hrow).part a)
              ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
          zoneMixed_of_subset (by intro r hr; exact hr) hsubset hrowmix
        simpa [Division.pairedItemTargetSucc_cut_left hrow i hleft, a] using hbig
      · have hright :
            Division.pairRightIndex (l := D.rowCuts + 1) (by omega) i.castSucc =
              Division.pairRightIndex (l := D.rowCuts + 1) (by omega) i.succ := by
          rcases Division.pairIndex_adjacent_same_succ hrow i with h | h
          · exact False.elim (hleft h)
          · exact h
        let a : Fin (Division.pairCount (D.rowCuts + 1)) :=
          Division.pairRightIndex (l := D.rowCuts + 1) (by omega) i.castSucc
        have hi₀ :
            i.castSucc ∈
              (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega)).part a := by
          simp [Division.pairRightIndexDivision, a]
        have hi₁ :
            i.succ ∈
              (Division.pairRightIndexDivision (D.rowCuts + 1) (by omega)).part a := by
          simp [Division.pairRightIndexDivision, a, hright.symm]
        have hrowmix :
            ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a)
              ((MatrixDivision.colFuse D hcol j).colDiv.part fj) := by
          simpa [MatrixDivision.rowPairRightDiv] using
            zoneMixed_row_coarsen_of_rowCutMixed (M := M)
              (R := D.rowDiv)
              (I := Division.pairRightIndexDivision (D.rowCuts + 1) (by omega))
              (C := (MatrixDivision.colFuse D hcol j).colDiv.part fj)
              (a := a) (i := i) hi₀ hi₁ hmix
        have hbig :
            ZoneMixed M ((MatrixDivision.rowPairRightDiv D hrow).part a)
              ((MatrixDivision.colPairLeftDiv D hcol).part b) :=
          zoneMixed_of_subset (by intro r hr; exact hr) hsubset hrowmix
        simpa [Division.pairedItemTargetSucc_cut_right hrow i hleft, a] using hbig

/-- The column-pair auxiliary entries in a fixed paired column. -/
noncomputable def colPairAuxFiber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    Finset
      (Sum (Fin (Division.pairCount (D.rowCuts + 1)))
        (Fin (Division.pairCount (D.rowCuts + 1)))) := by
  classical
  exact Finset.univ.filter fun y => (y, b) ∈ colPairAuxTargets M D hrow hcol

theorem rowMixedItems_colPair_card_le_ten_mul_colPairAuxFiber_card {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (b : Fin (Division.pairCount (D.colCuts + 1))) :
    let j : Fin D.colCuts :=
      Division.pairLeftCutIndex (l := D.colCuts + 1) (by omega) b
    let fj : Fin ((D.colCuts - 1) + 1) :=
      (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
    (rowMixedItems M D.rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part fj)).card ≤
      10 * (colPairAuxFiber M D hrow hcol b).card := by
  intro j fj
  apply pairedItem_card_le_ten_mul_target_card hrow
  intro x hx
  simp [colPairAuxFiber]
  exact pairedItemTarget_mem_colPairAuxTargets_of_colPair_rowMixedItem
    D hrow hcol b (by simpa [j, fj] using hx)

theorem colPairAuxTargets_card_gt_of_fibers_gt {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : 0 < D.colCuts)
    (h :
      ∀ b : Fin (Division.pairCount (D.colCuts + 1)),
        d < (colPairAuxFiber M D hrow hcol b).card) :
    Division.pairCount (D.colCuts + 1) * d <
      (colPairAuxTargets M D hrow hcol).card := by
  classical
  let q := Division.pairCount (D.colCuts + 1)
  let X :=
    Sum (Fin (Division.pairCount (D.rowCuts + 1)))
      (Fin (Division.pairCount (D.rowCuts + 1)))
  let P : Finset (X × Fin q) := colPairAuxTargets M D hrow hcol
  let A := Sigma fun b : Fin q => {x : X // x ∈ colPairAuxFiber M D hrow hcol b}
  have hcardA :
      Fintype.card A =
        ∑ b : Fin q, (colPairAuxFiber M D hrow hcol b).card := by
    simp [A]
  have hle : Fintype.card A ≤ P.card := by
    let f : A → {z : X × Fin q // z ∈ P} := fun z =>
      ⟨(z.2.1, z.1), by
        have hz := z.2.2
        change z.2.1 ∈
          (Finset.univ.filter fun y => (y, z.1) ∈ colPairAuxTargets M D hrow hcol) at hz
        simpa [P] using (Finset.mem_filter.mp hz).2⟩
    have hinj : Function.Injective f := by
      intro u v huv
      cases u with
      | mk a xa =>
          cases v with
          | mk b xb =>
              have hval := congrArg Subtype.val huv
              simp [f] at hval
              cases hval.2
              cases xa with
              | mk x hx =>
                  cases xb with
                  | mk y hy =>
                      simp at hval
                      subst y
                      rfl
    have hcard := Fintype.card_le_of_injective f hinj
    simpa [P] using hcard
  have hsum_le :
      ∑ _b : Fin q, (d + 1) ≤
        ∑ b : Fin q, (colPairAuxFiber M D hrow hcol b).card := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q)))
        (fun b _hb => Nat.succ_le_of_lt (h b)))
  have hq : 0 < q := Division.pairCount_pos (by omega)
  have hmul : q * d < q * (d + 1) :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self d) hq
  have hlt_sum :
      q * d < ∑ b : Fin q, (colPairAuxFiber M D hrow hcol b).card := by
    refine lt_of_lt_of_le ?_ hsum_le
    simpa [q, Finset.sum_const, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hmul
  have hlt_A : q * d < Fintype.card A := by
    simpa [hcardA] using hlt_sum
  exact lt_of_lt_of_le (by simpa [q, P] using hlt_A) hle

theorem hasRowFusion_rowFuse {n m : ℕ} (D : MatrixDivision n m)
    (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts) :
    HasRowFusion D (rowFuse D hrow i) := by
  refine ⟨by simp [rowFuse]; omega, rfl, ?_⟩
  refine ⟨(finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i, ?_, ?_⟩
  · simpa [rowFuse] using
      Division.isFusionAt_fuse
        (Division.castIndex
          (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv)
        ((finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i)
  · intro j
    rfl

theorem hasColFusion_colFuse {n m : ℕ} (D : MatrixDivision n m)
    (hcol : 0 < D.colCuts) (j : Fin D.colCuts) :
    HasColFusion D (colFuse D hcol j) := by
  refine ⟨rfl, by simp [colFuse]; omega, ?_⟩
  refine ⟨(finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j, ?_, ?_⟩
  · intro i
    rfl
  · simpa [colFuse] using
      Division.isFusionAt_fuse
        (Division.castIndex
          (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv)
        ((finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j)

/-- Row fusion does not increase the mixed value of any column part. -/
theorem rowMixedValue_rowFuse_le {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (j : Fin ((rowFuse D hrow i).colCuts + 1)) :
    rowMixedValue M (rowFuse D hrow i).rowDiv
        ((rowFuse D hrow i).colDiv.part j) ≤
      rowMixedValue M D.rowDiv (D.colDiv.part j) := by
  let Rcast : Division n ((D.rowCuts - 1) + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hle := rowMixedValue_fuse_le (M := M) Rcast (D.colDiv.part j) fi
  have hcast :
      rowMixedValue M Rcast (D.colDiv.part j) =
        rowMixedValue M D.rowDiv (D.colDiv.part j) := by
    simpa [Rcast] using
      rowMixedValue_castIndex
        (by omega : D.rowCuts = D.rowCuts - 1 + 1) M D.rowDiv (D.colDiv.part j)
  simpa [rowFuse, Rcast, fi, hcast] using hle

/-- Column fusion does not increase the mixed value of any row part. -/
theorem colMixedValue_colFuse_le {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (i : Fin ((colFuse D hcol j).rowCuts + 1)) :
    colMixedValue M ((colFuse D hcol j).rowDiv.part i)
        (colFuse D hcol j).colDiv ≤
      colMixedValue M (D.rowDiv.part i) D.colDiv := by
  let Ccast : Division m ((D.colCuts - 1) + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hle := colMixedValue_fuse_le (M := M) (D.rowDiv.part i) Ccast fj
  have hcast :
      colMixedValue M (D.rowDiv.part i) Ccast =
        colMixedValue M (D.rowDiv.part i) D.colDiv := by
    simpa [Ccast] using
      colMixedValue_castIndex
        (by omega : D.colCuts = D.colCuts - 1 + 1) M
        (D.rowDiv.part i) D.colDiv
  simpa [colFuse, Ccast, fj, hcast] using hle

/-- A row part strictly before the fused row cut is unchanged. -/
theorem rowFuse_rowPart_eq_of_lt {n m : ℕ}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (a : Fin ((rowFuse D hrow i).rowCuts + 1))
    (ha : a < (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i) :
    (rowFuse D hrow i).rowDiv.part a =
      D.rowDiv.part
        ((finCongr (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm
          a.castSucc) := by
  let Rcast : Division n ((D.rowCuts - 1) + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hpart : (Rcast.fuse fi).part a = Rcast.part a.castSucc :=
    Division.fuse_part_of_lt Rcast ha
  simpa [rowFuse, Rcast, fi, Division.castIndex] using hpart

/-- A row part strictly after the fused row cut is the corresponding shifted
old part. -/
theorem rowFuse_rowPart_eq_of_gt {n m : ℕ}
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (a : Fin ((rowFuse D hrow i).rowCuts + 1))
    (ha : (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i < a) :
    (rowFuse D hrow i).rowDiv.part a =
      D.rowDiv.part
        ((finCongr (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2)).symm
          a.succ) := by
  let Rcast : Division n ((D.rowCuts - 1) + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = (D.rowCuts - 1) + 2) D.rowDiv
  let fi : Fin ((D.rowCuts - 1) + 1) :=
    (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
  have hpart : (Rcast.fuse fi).part a = Rcast.part a.succ :=
    Division.fuse_part_of_gt Rcast ha
  simpa [rowFuse, Rcast, fi, Division.castIndex] using hpart

/-- A column part strictly before the fused column cut is unchanged. -/
theorem colFuse_colPart_eq_of_lt {n m : ℕ}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (b : Fin ((colFuse D hcol j).colCuts + 1))
    (hb : b < (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j) :
    (colFuse D hcol j).colDiv.part b =
      D.colDiv.part
        ((finCongr (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm
          b.castSucc) := by
  let Ccast : Division m ((D.colCuts - 1) + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hpart : (Ccast.fuse fj).part b = Ccast.part b.castSucc :=
    Division.fuse_part_of_lt Ccast hb
  simpa [colFuse, Ccast, fj, Division.castIndex] using hpart

/-- A column part strictly after the fused column cut is the corresponding
shifted old part. -/
theorem colFuse_colPart_eq_of_gt {n m : ℕ}
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (b : Fin ((colFuse D hcol j).colCuts + 1))
    (hb : (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j < b) :
    (colFuse D hcol j).colDiv.part b =
      D.colDiv.part
        ((finCongr (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2)).symm
          b.succ) := by
  let Ccast : Division m ((D.colCuts - 1) + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = (D.colCuts - 1) + 2) D.colDiv
  let fj : Fin ((D.colCuts - 1) + 1) :=
    (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
  have hpart : (Ccast.fuse fj).part b = Ccast.part b.succ :=
    Division.fuse_part_of_gt Ccast hb
  simpa [colFuse, Ccast, fj, Division.castIndex] using hpart

/-- A row fusion preserves bounded mixed value once the newly fused row part
has bounded mixed value on the column division. -/
theorem mixedValueAtMost_rowFuse {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hD : MixedValueAtMost M D d)
    (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (hnew :
      colMixedValue M
        ((rowFuse D hrow i).rowDiv.part
          ((finCongr
            (by simp [rowFuse]; omega :
              D.rowCuts = (rowFuse D hrow i).rowCuts + 1)) i))
        (rowFuse D hrow i).colDiv ≤ d) :
    MixedValueAtMost M (rowFuse D hrow i) d := by
  constructor
  · intro j
    exact le_trans (rowMixedValue_rowFuse_le D hrow i j) (hD.1 j)
  · intro a
    let fi : Fin ((D.rowCuts - 1) + 1) :=
      (finCongr (by omega : D.rowCuts = (D.rowCuts - 1) + 1)) i
    by_cases haeq : a = fi
    · subst a
      simpa [rowFuse, fi] using hnew
    · by_cases halt : a < fi
      · have hpart := rowFuse_rowPart_eq_of_lt D hrow i a halt
        rw [hpart]
        exact hD.2 _
      · have hfilt : fi < a := lt_of_le_of_ne (le_of_not_gt halt) (Ne.symm haeq)
        have hpart := rowFuse_rowPart_eq_of_gt D hrow i a hfilt
        rw [hpart]
        exact hD.2 _

/-- A column fusion preserves bounded mixed value once the newly fused column
part has bounded mixed value on the row division. -/
theorem mixedValueAtMost_colFuse {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hD : MixedValueAtMost M D d)
    (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (hnew :
      rowMixedValue M
        (colFuse D hcol j).rowDiv
        ((colFuse D hcol j).colDiv.part
          ((finCongr
            (by simp [colFuse]; omega :
              D.colCuts = (colFuse D hcol j).colCuts + 1)) j)) ≤ d) :
    MixedValueAtMost M (colFuse D hcol j) d := by
  constructor
  · intro b
    let fj : Fin ((D.colCuts - 1) + 1) :=
      (finCongr (by omega : D.colCuts = (D.colCuts - 1) + 1)) j
    by_cases hbeq : b = fj
    · subst b
      simpa [colFuse, fj] using hnew
    · by_cases hblt : b < fj
      · have hpart := colFuse_colPart_eq_of_lt D hcol j b hblt
        rw [hpart]
        exact hD.1 _
      · have hfjlt : fj < b := lt_of_le_of_ne (le_of_not_gt hblt) (Ne.symm hbeq)
        have hpart := colFuse_colPart_eq_of_gt D hcol j b hfjlt
        rw [hpart]
        exact hD.1 _
  · intro i
    exact le_trans (colMixedValue_colFuse_le D hcol j i) (hD.2 i)

/-- A good row cut gives a valid greedy fusion step. -/
theorem exists_exactFusion_of_goodRowCut {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hD : MixedValueAtMost M D d)
    (hrow : 0 < D.rowCuts) (i : Fin D.rowCuts)
    (hnew :
      colMixedValue M
        ((rowFuse D hrow i).rowDiv.part
          ((finCongr
            (by simp [rowFuse]; omega :
              D.rowCuts = (rowFuse D hrow i).rowCuts + 1)) i))
        (rowFuse D hrow i).colDiv ≤ d) :
    ∃ E : MatrixDivision n m,
      HasExactFusion D E ∧ MixedValueAtMost M E d := by
  refine ⟨rowFuse D hrow i, Or.inl (hasRowFusion_rowFuse D hrow i), ?_⟩
  exact mixedValueAtMost_rowFuse D hD hrow i hnew

/-- A good column cut gives a valid greedy fusion step. -/
theorem exists_exactFusion_of_goodColCut {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hD : MixedValueAtMost M D d)
    (hcol : 0 < D.colCuts) (j : Fin D.colCuts)
    (hnew :
      rowMixedValue M
        (colFuse D hcol j).rowDiv
        ((colFuse D hcol j).colDiv.part
          ((finCongr
            (by simp [colFuse]; omega :
              D.colCuts = (colFuse D hcol j).colCuts + 1)) j)) ≤ d) :
    ∃ E : MatrixDivision n m,
      HasExactFusion D E ∧ MixedValueAtMost M E d := by
  refine ⟨colFuse D hcol j, Or.inr (hasColFusion_colFuse D hcol j), ?_⟩
  exact mixedValueAtMost_colFuse D hD hcol j hnew

theorem hasFusionShape_of_hasRowFusion {n m : ℕ}
    {D E : MatrixDivision n m} (h : HasRowFusion D E) :
    HasFusionShape D E := by
  rcases h with ⟨hrow, hcol, _⟩
  exact Or.inl ⟨hrow, hcol⟩

theorem hasFusionShape_of_hasColFusion {n m : ℕ}
    {D E : MatrixDivision n m} (h : HasColFusion D E) :
    HasFusionShape D E := by
  rcases h with ⟨hrow, hcol, _⟩
  exact Or.inr ⟨hrow, hcol⟩

theorem hasFusionShape_of_hasExactFusion {n m : ℕ}
    {D E : MatrixDivision n m} (h : HasExactFusion D E) :
    HasFusionShape D E := by
  rcases h with h | h
  · exact hasFusionShape_of_hasRowFusion h
  · exact hasFusionShape_of_hasColFusion h

theorem cutCount_lt_of_hasFusionShape {n m : ℕ}
    {D E : MatrixDivision n m}
    (h : HasFusionShape D E) :
    cutCount E < cutCount D := by
  rcases h with h | h <;> dsimp [cutCount] <;> omega

theorem rowMixedValue_eq_zero_of_col_singleton {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) {j : Fin (D.colCuts + 1)} {c : Fin m}
    (hc : D.colDiv.part j = {c}) :
    rowMixedValue M D.rowDiv (D.colDiv.part j) = 0 := by
  classical
  have hz : rowMixedZones M D.rowDiv (D.colDiv.part j) = ∅ := by
    ext i
    simp [rowMixedZones]
    intro hmix
    exact hmix.2 (by
      intro r _ c₁ c₂ hc₁ hc₂
      have h₁ : c₁ = c := by simpa [hc] using hc₁
      have h₂ : c₂ = c := by simpa [hc] using hc₂
      subst c₁
      subst c₂
      rfl)
  have hcuts : rowMixedCuts M D.rowDiv (D.colDiv.part j) = ∅ := by
    ext i
    simp [rowMixedCuts]
    intro hmix
    exact hmix.2 (by
      constructor
      · intro c₁ c₂ hc₁ hc₂
        have h₁ : c₁ = c := by simpa [hc] using hc₁
        have h₂ : c₂ = c := by simpa [hc] using hc₂
        subst c₁
        subst c₂
        rfl
      · intro c₁ c₂ hc₁ hc₂
        have h₁ : c₁ = c := by simpa [hc] using hc₁
        have h₂ : c₂ = c := by simpa [hc] using hc₂
        subst c₁
        subst c₂
        rfl)
  simp [rowMixedValue, hz, hcuts]

theorem colMixedValue_eq_zero_of_row_singleton {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) {i : Fin (D.rowCuts + 1)} {r : Fin n}
    (hr : D.rowDiv.part i = {r}) :
    colMixedValue M (D.rowDiv.part i) D.colDiv = 0 := by
  classical
  have hz : colMixedZones M (D.rowDiv.part i) D.colDiv = ∅ := by
    ext j
    simp [colMixedZones]
    intro hmix
    exact hmix.1 (by
      intro r₁ r₂ hr₁ hr₂ c hc
      have h₁ : r₁ = r := by simpa [hr] using hr₁
      have h₂ : r₂ = r := by simpa [hr] using hr₂
      subst r₁
      subst r₂
      rfl)
  have hcuts : colMixedCuts M (D.rowDiv.part i) D.colDiv = ∅ := by
    ext j
    simp [colMixedCuts]
    intro hmix
    exact hmix.1 (by
      constructor
      · intro r₁ r₂ hr₁ hr₂
        have h₁ : r₁ = r := by simpa [hr] using hr₁
        have h₂ : r₂ = r := by simpa [hr] using hr₂
        subst r₁
        subst r₂
        rfl
      · intro r₁ r₂ hr₁ hr₂
        have h₁ : r₁ = r := by simpa [hr] using hr₁
        have h₂ : r₂ = r := by simpa [hr] using hr₂
        subst r₁
        subst r₂
        rfl)
  simp [colMixedValue, hz, hcuts]

theorem colMixedValue_le_one_of_colCuts_eq_zero {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hcol : D.colCuts = 0)
    (R : Finset (Fin n)) :
    colMixedValue M R D.colDiv ≤ 1 := by
  rcases D with ⟨rowCuts, colCuts, rowDiv, colDiv⟩
  dsimp at hcol ⊢
  subst colCuts
  have hzones : (colMixedZones M R colDiv).card ≤ 1 := by
    calc
      (colMixedZones M R colDiv).card ≤
          (Finset.univ : Finset (Fin 1)).card := by
        exact Finset.card_le_card (by
          intro x hx
          exact Finset.mem_univ x)
      _ = 1 := by simp
  have hcuts : colMixedCuts M R colDiv = ∅ := by
    ext j
    exact Fin.elim0 j
  simpa [colMixedValue, hcuts] using hzones

theorem rowMixedValue_le_one_of_rowCuts_eq_zero {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (D : MatrixDivision n m) (hrow : D.rowCuts = 0)
    (C : Finset (Fin m)) :
    rowMixedValue M D.rowDiv C ≤ 1 := by
  rcases D with ⟨rowCuts, colCuts, rowDiv, colDiv⟩
  dsimp at hrow ⊢
  subst rowCuts
  have hzones : (rowMixedZones M rowDiv C).card ≤ 1 := by
    calc
      (rowMixedZones M rowDiv C).card ≤
          (Finset.univ : Finset (Fin 1)).card := by
        exact Finset.card_le_card (by
          intro x hx
          exact Finset.mem_univ x)
      _ = 1 := by simp
  have hcuts : rowMixedCuts M rowDiv C = ∅ := by
    ext i
    exact Fin.elim0 i
  simpa [rowMixedValue, hcuts] using hzones

theorem exists_goodRowCut_of_colCuts_eq_zero {n m t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hMT : IsMarcusTardosConstant t c) (ht : 0 < t)
    (D : MatrixDivision n m) (hrow : 0 < D.rowCuts) (hcol : D.colCuts = 0) :
    ∃ i : Fin D.rowCuts,
      colMixedValue M
        ((MatrixDivision.rowFuse D hrow i).rowDiv.part
          ((finCongr
            (by simp [MatrixDivision.rowFuse]; omega :
              D.rowCuts =
                (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
        (MatrixDivision.rowFuse D hrow i).colDiv ≤ 2 * c := by
  let i : Fin D.rowCuts := ⟨0, hrow⟩
  refine ⟨i, ?_⟩
  have hle1 :
      colMixedValue M
        ((MatrixDivision.rowFuse D hrow i).rowDiv.part
          ((finCongr
            (by simp [MatrixDivision.rowFuse]; omega :
              D.rowCuts =
                (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
        (MatrixDivision.rowFuse D hrow i).colDiv ≤ 1 :=
    colMixedValue_le_one_of_colCuts_eq_zero
      (MatrixDivision.rowFuse D hrow i) (by simp [MatrixDivision.rowFuse, hcol]) _
  have hcpos : 0 < c := IsMarcusTardosConstant.pos hMT ht
  exact le_trans hle1 (by omega)

theorem exists_goodColCut_of_rowCuts_eq_zero {n m t c : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hMT : IsMarcusTardosConstant t c) (ht : 0 < t)
    (D : MatrixDivision n m) (hcol : 0 < D.colCuts) (hrow : D.rowCuts = 0) :
    ∃ j : Fin D.colCuts,
      rowMixedValue M
        (MatrixDivision.colFuse D hcol j).rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part
          ((finCongr
            (by simp [MatrixDivision.colFuse]; omega :
              D.colCuts =
                (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) ≤ 2 * c := by
  let j : Fin D.colCuts := ⟨0, hcol⟩
  refine ⟨j, ?_⟩
  have hle1 :
      rowMixedValue M
        (MatrixDivision.colFuse D hcol j).rowDiv
        ((MatrixDivision.colFuse D hcol j).colDiv.part
          ((finCongr
            (by simp [MatrixDivision.colFuse]; omega :
              D.colCuts =
                (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) ≤ 1 :=
    rowMixedValue_le_one_of_rowCuts_eq_zero
      (MatrixDivision.colFuse D hcol j) (by simp [MatrixDivision.colFuse, hrow]) _
  have hcpos : 0 < c := IsMarcusTardosConstant.pos hMT ht
  exact le_trans hle1 (by omega)

theorem mixedValueAtMost_of_isFinest {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : IsFinest D) :
    MixedValueAtMost M D d := by
  constructor
  · intro j
    rcases hD.2 j with ⟨c, hc⟩
    rw [rowMixedValue_eq_zero_of_col_singleton D hc]
    exact Nat.zero_le d
  · intro i
    rcases hD.1 i with ⟨r, hr⟩
    rw [colMixedValue_eq_zero_of_row_singleton D hr]
    exact Nat.zero_le d

end MatrixDivision

/-- A tail of a bounded mixed-value division sequence starting from a prescribed
division. -/
structure BoundedMixedValueDivisionTail {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ)
    (D₀ : MatrixDivision n m) where
  /-- Number of remaining fusions. -/
  stepCount : ℕ
  /-- Division at each time. -/
  division : ℕ → MatrixDivision n m
  /-- The first division is the prescribed one. -/
  starts : division 0 = D₀
  /-- The final division is coarsest. -/
  ends : MatrixDivision.IsCoarsest (division stepCount)
  /-- Consecutive divisions are related by one row or column fusion. -/
  step_fuses :
    ∀ s, s < stepCount → MatrixDivision.HasExactFusion (division s) (division (s + 1))
  /-- Every division in the tail has bounded mixed value. -/
  mixedValue_le :
    ∀ s, s ≤ stepCount → MatrixDivision.MixedValueAtMost M (division s) d

/-- A concrete division sequence all of whose divisions have mixed value at
most `d`. -/
structure BoundedMixedValueDivisionSequence {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) where
  /-- Number of fusions. -/
  stepCount : ℕ
  /-- Division at each time. -/
  division : ℕ → MatrixDivision n m
  /-- The first division is the finest one. -/
  starts : MatrixDivision.IsFinest (division 0)
  /-- The final division is the coarsest one. -/
  ends : MatrixDivision.IsCoarsest (division stepCount)
  /-- Consecutive divisions are related by one row or column fusion. -/
  step_fuses :
    ∀ s, s < stepCount → MatrixDivision.HasExactFusion (division s) (division (s + 1))
  /-- Every division in the sequence has bounded mixed value. -/
  mixedValue_le :
    ∀ s, s ≤ stepCount → MatrixDivision.MixedValueAtMost M (division s) d

/-- The local greedy step used in Lemma 13: every non-coarsest division whose
mixed value is already bounded admits one fusion preserving the same bound. -/
def GreedyFusionStep {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) : Prop :=
  ∀ D : MatrixDivision n m,
    MatrixDivision.MixedValueAtMost M D d →
      ¬ MatrixDivision.IsCoarsest D →
        ∃ E : MatrixDivision n m,
          MatrixDivision.HasExactFusion D E ∧
            MatrixDivision.MixedValueAtMost M E d

/-- Greedy-step interface left after the Marcus--Tardos counting argument:
every non-coarsest bounded division has either a good row cut or a good column
cut. -/
theorem greedyFusionStep_of_goodCut {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hgood :
      ∀ D : MatrixDivision n m,
        MatrixDivision.MixedValueAtMost M D d →
          ¬ MatrixDivision.IsCoarsest D →
            (∃ hrow : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
              colMixedValue M
                ((MatrixDivision.rowFuse D hrow i).rowDiv.part
                  ((finCongr
                    (by simp [MatrixDivision.rowFuse]; omega :
                      D.rowCuts =
                        (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
                (MatrixDivision.rowFuse D hrow i).colDiv ≤ d) ∨
              (∃ hcol : 0 < D.colCuts, ∃ j : Fin D.colCuts,
                rowMixedValue M
                  (MatrixDivision.colFuse D hcol j).rowDiv
                  ((MatrixDivision.colFuse D hcol j).colDiv.part
                    ((finCongr
                      (by simp [MatrixDivision.colFuse]; omega :
                        D.colCuts =
                          (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) ≤ d)) :
    GreedyFusionStep M d := by
  intro D hD hcoarse
  rcases hgood D hD hcoarse with hrowgood | hcolgood
  · rcases hrowgood with ⟨hrow, i, hnew⟩
    exact MatrixDivision.exists_exactFusion_of_goodRowCut D hD hrow i hnew
  · rcases hcolgood with ⟨hcol, j, hnew⟩
    exact MatrixDivision.exists_exactFusion_of_goodColCut D hD hcol j hnew

namespace BoundedMixedValueDivisionTail

/-- Prepend one fusion to a bounded tail. -/
def cons {n m d : ℕ} {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDE : MatrixDivision.HasExactFusion D E)
    (hD : MatrixDivision.MixedValueAtMost M D d)
    (S : BoundedMixedValueDivisionTail M d E) :
    BoundedMixedValueDivisionTail M d D where
  stepCount := S.stepCount + 1
  division := fun s =>
    match s with
    | 0 => D
    | r + 1 => S.division r
  starts := rfl
  ends := by
    simpa using S.ends
  step_fuses := by
    intro s hs
    cases s with
    | zero =>
        simpa [S.starts] using hDE
    | succ r =>
        have hr : r < S.stepCount := by omega
        simpa using S.step_fuses r hr
  mixedValue_le := by
    intro s hs
    cases s with
    | zero =>
        simpa using hD
    | succ r =>
        have hr : r ≤ S.stepCount := by omega
        simpa using S.mixedValue_le r hr

end BoundedMixedValueDivisionTail

/-- The finite descent part of Lemma 13.  Once the local greedy-fusion step is
available, repeatedly applying it gives a bounded mixed-value division sequence
from any bounded starting division. -/
theorem exists_boundedMixedValueDivisionTail_of_greedyStep {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hstep : GreedyFusionStep M d) :
    ∀ D : MatrixDivision n m,
      MatrixDivision.MixedValueAtMost M D d →
        Nonempty (BoundedMixedValueDivisionTail M d D) := by
  classical
  intro D
  refine WellFounded.induction
    (C := fun D : MatrixDivision n m =>
      MatrixDivision.MixedValueAtMost M D d →
        Nonempty (BoundedMixedValueDivisionTail M d D))
    (InvImage.wf MatrixDivision.cutCount <| (Nat.lt_wfRel).2) D ?_
  intro D ih hD
  by_cases hcoarse : MatrixDivision.IsCoarsest D
  · exact ⟨{
      stepCount := 0
      division := fun _ => D
      starts := rfl
      ends := hcoarse
      step_fuses := by intro s hs; omega
      mixedValue_le := by intro s hs; simpa using hD
    }⟩
  · rcases hstep D hD hcoarse with ⟨E, hDE, hE⟩
    have hElt : MatrixDivision.cutCount E < MatrixDivision.cutCount D :=
      MatrixDivision.cutCount_lt_of_hasFusionShape
        (MatrixDivision.hasFusionShape_of_hasExactFusion hDE)
    rcases ih E hElt hE with ⟨S⟩
    exact ⟨BoundedMixedValueDivisionTail.cons hDE hD S⟩

/-- Convert a bounded tail from a finest division into the public sequence
object. -/
def boundedMixedValueDivisionSequence_of_tail {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D₀ : MatrixDivision n m}
    (hfinest : MatrixDivision.IsFinest D₀)
    (S : BoundedMixedValueDivisionTail M d D₀) :
    BoundedMixedValueDivisionSequence M d where
  stepCount := S.stepCount
  division := S.division
  starts := by
    rw [S.starts]
    exact hfinest
  ends := S.ends
  step_fuses := S.step_fuses
  mixedValue_le := S.mixedValue_le

/-- Lemma 13 reduced to its local greedy-fusion step and a bounded finest
starting division.  The Marcus--Tardos auxiliary-matrix argument supplies the
local greedy step; see
`greedyFusionStep_of_marcusTardos` for the fully proved explicit constant used
in this formalization. -/
theorem boundedMixedValueDivisionSequence_of_greedyStep {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D₀ : MatrixDivision n m}
    (hfinest : MatrixDivision.IsFinest D₀)
    (hD₀ : MatrixDivision.MixedValueAtMost M D₀ d)
    (hstep : GreedyFusionStep M d) :
    Nonempty (BoundedMixedValueDivisionSequence M d) := by
  rcases exists_boundedMixedValueDivisionTail_of_greedyStep hstep D₀ hD₀ with ⟨S⟩
  exact ⟨boundedMixedValueDivisionSequence_of_tail hfinest S⟩

/-- Explicit mixed-value bound used in the formalized Lemma 13.  The paper
states a bound of the form `2 * c_t`; the finite-fiber charging formalized here
uses the harmless constant `20`. -/
def lemma13MixedValueBound (c : ℕ → ℕ) (t : ℕ) : ℕ :=
  20 * c t

/-- Nondegenerate Marcus--Tardos counting step for Lemma 13 with the explicit
finite-fiber constant used in this formalization. -/
theorem pairedMarcusTardosCountingStep
    {c : ℕ → ℕ} :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
      (_hMT : IsMarcusTardosConstant t (c t)) (_hfree : MixedFree M t)
      (D : MatrixDivision n m),
        MatrixDivision.MixedValueAtMost M D (lemma13MixedValueBound c t) →
          0 < D.rowCuts → 0 < D.colCuts →
            ¬ (∃ hrow : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
              colMixedValue M
                ((MatrixDivision.rowFuse D hrow i).rowDiv.part
                  ((finCongr
                    (by simp [MatrixDivision.rowFuse]; omega :
                      D.rowCuts =
                        (MatrixDivision.rowFuse D hrow i).rowCuts + 1)) i))
                (MatrixDivision.rowFuse D hrow i).colDiv ≤
                  lemma13MixedValueBound c t) →
            ¬ (∃ hcol : 0 < D.colCuts, ∃ j : Fin D.colCuts,
              rowMixedValue M
                (MatrixDivision.colFuse D hcol j).rowDiv
                ((MatrixDivision.colFuse D hcol j).colDiv.part
                  ((finCongr
                    (by simp [MatrixDivision.colFuse]; omega :
                      D.colCuts =
                        (MatrixDivision.colFuse D hcol j).colCuts + 1)) j)) ≤
                lemma13MixedValueBound c t) →
              False := by
  intro n m M t hMT hfree D _hD hrow hcol hbadRow hbadCol
  classical
  let p := Division.pairCount (D.rowCuts + 1)
  let q := Division.pairCount (D.colCuts + 1)
  have htwice_p : c t * p + c t * p = p * (2 * c t) := by
    ring
  have htwice_q : c t * q + c t * q = q * (2 * c t) := by
    ring
  by_cases hpq : q ≤ p
  · have hfib :
        ∀ a : Fin p, 2 * c t < (MatrixDivision.rowPairAuxFiber M D hrow hcol a).card := by
      intro a
      have hgt := MatrixDivision.colMixedItems_rowPair_card_gt_of_no_good_row
        (M := M) (d := lemma13MixedValueBound c t) D hrow hbadRow a
      have hle := MatrixDivision.colMixedItems_rowPair_card_le_ten_mul_rowPairAuxFiber_card
        (M := M) D hrow hcol a
      dsimp [p, lemma13MixedValueBound] at hgt hle
      omega
    have hlower := MatrixDivision.rowPairAuxTargets_card_gt_of_fibers_gt
      (M := M) (d := 2 * c t) D hrow hcol (by simpa [p] using hfib)
    have hupper := MatrixDivision.rowPairAuxTargets_card_lt
      (M := M) D hrow hcol hMT hfree
    have hmax : max p q = p := max_eq_left hpq
    have hupper' :
        (MatrixDivision.rowPairAuxTargets M D hrow hcol).card < p * (2 * c t) := by
      simpa [p, q, hmax, htwice_p] using hupper
    have hlow' :
        p * (2 * c t) < (MatrixDivision.rowPairAuxTargets M D hrow hcol).card := by
      simpa [p] using hlower
    exact (not_lt_of_ge (le_of_lt hupper')) hlow'
  · have hqp : p ≤ q := le_of_not_ge hpq
    have hfib :
        ∀ b : Fin q, 2 * c t < (MatrixDivision.colPairAuxFiber M D hrow hcol b).card := by
      intro b
      have hgt := MatrixDivision.rowMixedItems_colPair_card_gt_of_no_good_col
        (M := M) (d := lemma13MixedValueBound c t) D hcol hbadCol b
      have hle := MatrixDivision.rowMixedItems_colPair_card_le_ten_mul_colPairAuxFiber_card
        (M := M) D hrow hcol b
      dsimp [q, lemma13MixedValueBound] at hgt hle
      omega
    have hlower := MatrixDivision.colPairAuxTargets_card_gt_of_fibers_gt
      (M := M) (d := 2 * c t) D hrow hcol (by simpa [q] using hfib)
    have hupper := MatrixDivision.colPairAuxTargets_card_lt
      (M := M) D hrow hcol hMT hfree
    have hmax : max p q = q := max_eq_right hqp
    have hupper' :
        (MatrixDivision.colPairAuxTargets M D hrow hcol).card < q * (2 * c t) := by
      simpa [p, q, hmax, htwice_q] using hupper
    have hlow' :
        q * (2 * c t) < (MatrixDivision.colPairAuxTargets M D hrow hcol).card := by
      simpa [q] using hlower
    exact (not_lt_of_ge (le_of_lt hupper')) hlow'

/-- Local greedy-fusion step in the proved form of Lemma 13. -/
theorem greedyFusionStep_of_marcusTardos
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ),
      MixedFree M t → GreedyFusionStep M (lemma13MixedValueBound c t) := by
  intro n m M t hfree
  by_cases ht : t = 0
  · subst t
    exact (False.elim (hfree (hasMixedMinor_zero M)))
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    apply greedyFusionStep_of_goodCut
    intro D hD hcoarse
    by_cases hrow : 0 < D.rowCuts
    · by_cases hcol : 0 < D.colCuts
      · by_cases hgoodRow :
          ∃ hrow' : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
            colMixedValue M
              ((MatrixDivision.rowFuse D hrow' i).rowDiv.part
                ((finCongr
                  (by simp [MatrixDivision.rowFuse]; omega :
                    D.rowCuts =
                      (MatrixDivision.rowFuse D hrow' i).rowCuts + 1)) i))
              (MatrixDivision.rowFuse D hrow' i).colDiv ≤
                lemma13MixedValueBound c t
        · exact Or.inl hgoodRow
        · by_cases hgoodCol :
            ∃ hcol' : 0 < D.colCuts, ∃ j : Fin D.colCuts,
              rowMixedValue M
                (MatrixDivision.colFuse D hcol' j).rowDiv
                ((MatrixDivision.colFuse D hcol' j).colDiv.part
                  ((finCongr
                    (by simp [MatrixDivision.colFuse]; omega :
                      D.colCuts =
                        (MatrixDivision.colFuse D hcol' j).colCuts + 1)) j)) ≤
                lemma13MixedValueBound c t
          · exact Or.inr hgoodCol
          · exact False.elim
              (pairedMarcusTardosCountingStep
                M t (hMT t) hfree D hD hrow hcol hgoodRow hgoodCol)
      · have hcol0 : D.colCuts = 0 := Nat.eq_zero_of_not_pos hcol
        rcases MatrixDivision.exists_goodRowCut_of_colCuts_eq_zero
          (M := M) (hMT t) htpos D hrow hcol0 with ⟨i, hi⟩
        exact Or.inl ⟨hrow, i, le_trans hi (by
          have hcpos : 0 < c t := IsMarcusTardosConstant.pos (hMT t) htpos
          simp [lemma13MixedValueBound]
          omega)⟩
    · have hrow0 : D.rowCuts = 0 := Nat.eq_zero_of_not_pos hrow
      have hcol : 0 < D.colCuts := by
        by_contra hcolnot
        have hcol0 : D.colCuts = 0 := Nat.eq_zero_of_not_pos hcolnot
        exact hcoarse ⟨hrow0, hcol0⟩
      rcases MatrixDivision.exists_goodColCut_of_rowCuts_eq_zero
        (M := M) (hMT t) htpos D hcol hrow0 with ⟨j, hj⟩
      exact Or.inr ⟨hcol, j, le_trans hj (by
        have hcpos : 0 < c t := IsMarcusTardosConstant.pos (hMT t) htpos
        simp [lemma13MixedValueBound]
        omega)⟩

/-- Positive-size matrix form of Lemma 13 proved from Marcus--Tardos, with the
explicit finite-fiber constant used in this formalization. -/
theorem boundedMixedValueDivisionSequence_positive_of_marcusTardos
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      (M : _root_.Matrix (Fin n) (Fin m) α) → (t : ℕ) →
        MixedFree M t →
          Nonempty (BoundedMixedValueDivisionSequence M (lemma13MixedValueBound c t)) := by
  intro n m hn hm M t hfree
  exact boundedMixedValueDivisionSequence_of_greedyStep
    (MatrixDivision.finest_isFinest hn hm)
    (MatrixDivision.mixedValueAtMost_of_isFinest
      (MatrixDivision.finest_isFinest hn hm))
    (greedyFusionStep_of_marcusTardos hMT M t hfree)

/-- The greedy-step form of Lemma 13 with the explicit `20 * c_t` bound. -/
theorem greedyFusionProducesBoundedMixedValueSequence
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
      (D₀ : MatrixDivision n m),
        MixedFree M t →
          MatrixDivision.IsFinest D₀ →
            GreedyFusionStep M (lemma13MixedValueBound c t) := by
  intro n m M t _D₀ hfree _hfinest
  exact greedyFusionStep_of_marcusTardos hMT M t hfree

/-- Reusable positive-size Lemma 13 with the explicit `20 * c_t` bound.

The positive-size hypotheses are necessary because a `Division 0 1` cannot
have a nonempty part. -/
theorem boundedMixedValueDivisionSequenceTheorem
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      ∀ (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ),
        MixedFree M t →
          Nonempty (BoundedMixedValueDivisionSequence M (lemma13MixedValueBound c t)) := by
  intro n m hn hm M t hfree
  exact boundedMixedValueDivisionSequence_positive_of_marcusTardos
    hMT hn hm M t hfree

/-- Sequence-level form of Lemma 13, once the greedy-fusion argument has been
proved from the grid-form Marcus--Tardos theorem. -/
theorem boundedMixedValueDivisionSequence_of_greedyFusion
    {c : ℕ → ℕ}
    (hgreedy :
      ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
        (D₀ : MatrixDivision n m),
          MixedFree M t →
            MatrixDivision.IsFinest D₀ →
              GreedyFusionStep M (lemma13MixedValueBound c t)) :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
      (D₀ : MatrixDivision n m),
        MixedFree M t →
          MatrixDivision.IsFinest D₀ →
            Nonempty (BoundedMixedValueDivisionSequence M (lemma13MixedValueBound c t)) := by
  intro n m M t D₀ hfree hfinest
  exact boundedMixedValueDivisionSequence_of_greedyStep hfinest
    (MatrixDivision.mixedValueAtMost_of_isFinest hfinest)
    (hgreedy M t D₀ hfree hfinest)

/-- Positive-size matrix form: using the canonical singleton division as the
finest starting point. -/
theorem boundedMixedValueDivisionSequence_of_greedyFusion_positive
    {c : ℕ → ℕ}
    (hgreedy :
      ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
        (D₀ : MatrixDivision n m),
          MixedFree M t →
            MatrixDivision.IsFinest D₀ →
              GreedyFusionStep M (lemma13MixedValueBound c t))
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ)
    (hfree : MixedFree M t) :
    Nonempty (BoundedMixedValueDivisionSequence M (lemma13MixedValueBound c t)) :=
  boundedMixedValueDivisionSequence_of_greedyFusion hgreedy M t
    (MatrixDivision.finest hn hm) hfree (MatrixDivision.finest_isFinest hn hm)

/-- Contract theorem for
`DivisionSequenceContract.lemma13_bounded_mixed_value_division_sequence`.

If `M` is positive-size and `t`-mixed-free, then it has a full division sequence
whose mixed value is bounded by `20 * c t`, for any Marcus--Tardos constant
family `c`. -/
theorem lemma13_bounded_mixed_value_division_sequence
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      ∀ (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ),
        MixedFree M t →
          Nonempty (BoundedMixedValueDivisionSequence M (20 * c t)) := by
  intro n m hn hm M t hfree
  simpa [lemma13MixedValueBound] using
    boundedMixedValueDivisionSequenceTheorem hMT hn hm M t hfree

end Matrix
end TwinWidth

/- ===== end Matrix/DivisionSequence.lean ===== -/

/- ===== begin Matrix/Theorem10Defs.lean ===== -/

/-
# Definitions for matrix Theorem 10

This file contains only the public predicates and numerical bounds used to
state the matrix form of Theorem 10.  Proofs live in `Theorem10.lean`; contract
wrappers for the public theorem statements live in `Theorem10Contract.lean`.
-/

namespace TwinWidth
namespace Matrix

variable {α : Type*}

/-- The matrix first-item bound predicted by Theorem 10: bounded matrix
twin-width forces bounded matrix mixed number.  The constant follows the
project's current mixed-minor convention. -/
def theorem10MatrixMixedNumberBound (d : ℕ) : ℕ :=
  2 * d + 2

namespace MatrixDivision

/-- Column parts on which a fixed row part is nonconstant in a division.

This is the error notion used in the first item of Theorem 10: an error zone is
any nonconstant zone, not only a mixed zone. -/
noncomputable def nonconstantRowErrorSet {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1)) :
    Finset (Fin (D.colCuts + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j =>
      ¬ ZoneConstant M (D.rowDiv.part i) (D.colDiv.part j)

/-- Row parts on which a fixed column part is nonconstant in a division.

This is the error notion used in the first item of Theorem 10: an error zone is
any nonconstant zone, not only a mixed zone. -/
noncomputable def nonconstantColErrorSet {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1)) :
    Finset (Fin (D.rowCuts + 1)) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      ¬ ZoneConstant M (D.rowDiv.part i) (D.colDiv.part j)

/-- A division has error value at most `t` when each row part and each column
part sees at most `t` nonconstant zones. -/
def NonconstantErrorValueAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (t : ℕ) : Prop :=
  (∀ i, (nonconstantRowErrorSet M D i).card ≤ t) ∧
    ∀ j, (nonconstantColErrorSet M D j).card ≤ t

end MatrixDivision

/-- A concrete division sequence all of whose divisions have nonconstant error
value at most `d`.  This formalizes the `d`-twin-ordered matrix hypothesis used
in the first item of Theorem 10. -/
structure BoundedErrorValueDivisionSequence {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) where
  /-- Number of fusions. -/
  stepCount : ℕ
  /-- Division at each time. -/
  division : ℕ → MatrixDivision n m
  /-- The first division is the finest one. -/
  starts : MatrixDivision.IsFinest (division 0)
  /-- The final division is the coarsest one. -/
  ends : MatrixDivision.IsCoarsest (division stepCount)
  /-- Consecutive divisions are related by one row or column fusion. -/
  step_fuses :
    ∀ s, s < stepCount → MatrixDivision.HasExactFusion (division s) (division (s + 1))
  /-- Every division in the sequence has bounded nonconstant error value. -/
  errorValue_le :
    ∀ s, s ≤ stepCount → MatrixDivision.NonconstantErrorValueAtMost M (division s) d

/-- A matrix is `d`-twin-ordered when its current row and column orders have a
division sequence of nonconstant error value at most `d`. -/
def MatrixTwinOrderedAtMost {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ) : Prop :=
  Nonempty (BoundedErrorValueDivisionSequence M d)

/-- Matrix-level form of the first item of Theorem 10: a `d`-twin-ordered
matrix has mixed number bounded by a function of `d`. -/
def MatrixMixedNumberBoundedByTwinOrdered (f : ℕ → ℕ) : Prop :=
  ∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
    MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ f d

/-- Public matrix-level first item of Theorem 10: bounded matrix twin-width
forces bounded matrix mixed number. -/
def MatrixMixedNumberBoundedByMatrixTwinWidth (f : ℕ → ℕ) : Prop :=
  ∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
    MatrixTwinWidthAtMost M d → matrixMixedNumber M ≤ f d

/-- A concrete contraction path between two prescribed matrix partitions. -/
structure MatrixContractionPath {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ)
    (P₀ P₁ : MatrixPartition n m) where
  /-- Number of contractions in the path. -/
  stepCount : ℕ
  /-- Partition at each time. -/
  partition : ℕ → MatrixPartition n m
  /-- The path starts at `P₀`. -/
  starts : partition 0 = P₀
  /-- The path ends at `P₁`. -/
  ends : partition stepCount = P₁
  /-- Each step contracts one row part or one column part. -/
  step_contracts :
    ∀ i, i < stepCount → MatrixPartition.IsContraction (partition i) (partition (i + 1))
  /-- Every partition in the path has bounded error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

/-- A sequence of partitions where each term has error at most `t` and
`r`-refines the next one.

This is the hypothesis of Lemma 8 in the matrix language. -/
structure BoundedErrorRefinementPartitionSequence {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (r t : ℕ) where
  /-- Number of coarse-graining steps. -/
  stepCount : ℕ
  /-- Partition at each time. -/
  partition : ℕ → MatrixPartition n m
  /-- The first partition is finest. -/
  starts : MatrixPartition.IsFinest (partition 0)
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Each partition boundedly refines the next one. -/
  step_rrefines :
    ∀ i, i < stepCount → MatrixPartition.RRefines (partition i) (partition (i + 1)) r
  /-- Every partition in the sequence has bounded nonconstant error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) t

/-- The mixed-value bound obtained from Marcus--Tardos constants in the second
item of Theorem 10.  The argument is `matrixMixedNumber M`; the proof applies
Lemma 13 at the next mixed-minor order, which is mixed-free by maximality. -/
def theorem10MixedValueBound (c : ℕ → ℕ) (k : ℕ) : ℕ :=
  lemma13MixedValueBound c (k + 1)

/-- The refinement blow-up in the second item of Theorem 10 for alphabet size
`a`.

If a division sequence has mixed value at most `d`, the paper refines it into
a bounded-refinement partition sequence and obtains a contraction sequence of
nonconstant error value bounded by this expression.  Combined with the
formalized Lemma 13 constant, this has the same elementary finite-alphabet
shape as Theorem 10, with explicit constants from the Lean proof. -/
def theorem10AlphabetErrorRefinementBound (a d : ℕ) : ℕ :=
  2 * d * a ^ (2 * (d + 1))

/-- Boolean-alphabet specialization of `theorem10AlphabetErrorRefinementBound`. -/
def theorem10ErrorRefinementBound (d : ℕ) : ℕ :=
  theorem10AlphabetErrorRefinementBound 2 d

/-- The explicit bound used in the final, unconditional second item of
Theorem 10.  It applies the refinement blow-up to Lemma 13's mixed-value bound
at one more than the matrix mixed number, with the formalized Marcus--Tardos
constants. -/
def theorem10AlphabetMatrixTwinWidthBound (a k : ℕ) : ℕ :=
  theorem10AlphabetErrorRefinementBound a (theorem10MixedValueBound marcusTardosConstant k)

/-- Boolean-alphabet specialization of `theorem10AlphabetMatrixTwinWidthBound`. -/
def theorem10MatrixTwinWidthBound (k : ℕ) : ℕ :=
  theorem10AlphabetMatrixTwinWidthBound 2 k

end Matrix
end TwinWidth

/- ===== end Matrix/Theorem10Defs.lean ===== -/

/- ===== begin Matrix/Theorem10.lean ===== -/

/-
# Matrix theorem 10

This file proves the matrix Theorem 10 interface.  It contains the ordered
first item, the Lemma 13 mixed-value sequence packaging, the Section 5.8 profile
refinement from bounded mixed value to bounded error value, and the Lemma 8
expansion from bounded-refinement partition sequences to matrix contraction
sequences.
-/

namespace TwinWidth
namespace Matrix

universe u

variable {α : Type u}

/-- Negating verticality produces two rows and one column witnessing different
entries. -/
theorem not_cellVertical_iff_exists {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    ¬ CellVertical M R C i j ↔
      ∃ r₁, r₁ ∈ R.part i ∧
        ∃ r₂, r₂ ∈ R.part i ∧
          ∃ c, c ∈ C.part j ∧ M r₁ c ≠ M r₂ c := by
  classical
  simp [CellVertical]

/-- Negating horizontality produces one row and two columns witnessing
different entries. -/
theorem not_cellHorizontal_iff_exists {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) :
    ¬ CellHorizontal M R C i j ↔
      ∃ r, r ∈ R.part i ∧
        ∃ c₁, c₁ ∈ C.part j ∧
          ∃ c₂, c₂ ∈ C.part j ∧ M r c₁ ≠ M r c₂ := by
  classical
  simp [CellHorizontal]

namespace Division

/-- If two separated parts of a division meet the same convex part of another
division, then every part between them is contained in that convex part. -/
theorem part_subset_of_between_mem_same_part {n k l : ℕ}
    (A : Division n k) (D : Division n l)
    {p mid q : Fin k} {b : Fin l}
    (hpm : p < mid) (hmq : mid < q)
    {x y : Fin n}
    (hxA : x ∈ A.part p) (hxD : x ∈ D.part b)
    (hyA : y ∈ A.part q) (hyD : y ∈ D.part b) :
    A.part mid ⊆ D.part b := by
  intro z hz
  have hxz : x < z := A.part_ordered hpm hxA hz
  have hzy : z < y := A.part_ordered hmq hz hyA
  exact D.part_convex b hxD hyD (le_of_lt hxz) (le_of_lt hzy)

end Division

namespace MatrixDivision

/-- A division has swallowed one row or column block of a proposed mixed minor
when some mixed-minor row part is contained in one row part of the division, or
some mixed-minor column part is contained in one column part of the division. -/
def ContainsMinorBlock {n m k : ℕ}
    (R : Division n k) (C : Division m k) (D : MatrixDivision n m) : Prop :=
  (∃ i : Fin k, ∃ a : Fin (D.rowCuts + 1), R.part i ⊆ D.rowDiv.part a) ∨
    ∃ j : Fin k, ∃ b : Fin (D.colCuts + 1), C.part j ⊆ D.colDiv.part b

/-- A coarsest division contains every mixed-minor block on both sides. -/
theorem containsMinorBlock_of_isCoarsest {n m k : ℕ}
    (R : Division n k) (C : Division m k) {D : MatrixDivision n m}
    (hD : IsCoarsest D) (hk : 0 < k) :
    ContainsMinorBlock R C D := by
  rcases hD with ⟨hrow, _hcol⟩
  left
  let i : Fin k := ⟨0, hk⟩
  let a : Fin (D.rowCuts + 1) := ⟨0, by omega⟩
  refine ⟨i, a, ?_⟩
  intro x hx
  rcases D.rowDiv.part_cover x with ⟨b, hb⟩
  have hba : b = a := by
    apply Fin.ext
    omega
  simpa [hba] using hb

/-- At the finest division, no block of a positive mixed minor has already been
swallowed by a singleton row or column part. -/
theorem not_containsMinorBlock_of_isFinest_of_mixed {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m k} {D : MatrixDivision n m}
    (hk : 0 < k) (hD : IsFinest D)
    (hmix : ∀ i j : Fin k, CellMixed M R C i j) :
    ¬ ContainsMinorBlock R C D := by
  classical
  intro hcontains
  let j₀ : Fin k := ⟨0, hk⟩
  rcases hcontains with ⟨i, a, hsub⟩ | ⟨j, b, hsub⟩
  · rcases hD.1 a with ⟨r, ha⟩
    have hvert : CellVertical M R C i j₀ := by
      intro r₁ r₂ hr₁ hr₂ c hc
      have hr₁_eq : r₁ = r := by
        have : r₁ ∈ ({r} : Finset (Fin n)) := by
          simpa [ha] using hsub hr₁
        simpa using this
      have hr₂_eq : r₂ = r := by
        have : r₂ ∈ ({r} : Finset (Fin n)) := by
          simpa [ha] using hsub hr₂
        simpa using this
      simp [hr₁_eq, hr₂_eq]
    exact (hmix i j₀).1 hvert
  · rcases hD.2 b with ⟨c, hb⟩
    have hhor : CellHorizontal M R C j₀ j := by
      intro r hr c₁ c₂ hc₁ hc₂
      have hc₁_eq : c₁ = c := by
        have : c₁ ∈ ({c} : Finset (Fin m)) := by
          simpa [hb] using hsub hc₁
        simpa using this
      have hc₂_eq : c₂ = c := by
        have : c₂ ∈ ({c} : Finset (Fin m)) := by
          simpa [hb] using hsub hc₂
        simpa using this
      simp [hc₁_eq, hc₂_eq]
    exact (hmix j₀ j).2 hhor

/-- A column fusion leaves the row division unchanged, so any swallowed row
minor block after the fusion was already swallowed before it. -/
theorem rowBlock_subset_prev_of_hasColFusion {n m k : ℕ}
    {R : Division n k} {C : Division m k} {D E : MatrixDivision n m}
    (hDE : HasColFusion D E)
    (hrow :
      ∃ i : Fin k, ∃ a : Fin (E.rowCuts + 1), R.part i ⊆ E.rowDiv.part a) :
    ContainsMinorBlock R C D := by
  rcases hDE with ⟨hrowCuts, _hcolCuts, _j, hrows, _hcols⟩
  rcases hrow with ⟨i, a, hsub⟩
  left
  let aD : Fin (D.rowCuts + 1) :=
    (finCongr (by omega : E.rowCuts + 1 = D.rowCuts + 1)) a
  refine ⟨i, aD, ?_⟩
  intro x hx
  have hxE := hsub hx
  have hpart := hrows a
  rw [hpart] at hxE
  simpa [Division.castIndex, aD] using hxE

/-- A row fusion leaves the column division unchanged, so any swallowed column
minor block after the fusion was already swallowed before it. -/
theorem colBlock_subset_prev_of_hasRowFusion {n m k : ℕ}
    {R : Division n k} {C : Division m k} {D E : MatrixDivision n m}
    (hDE : HasRowFusion D E)
    (hcol :
      ∃ j : Fin k, ∃ b : Fin (E.colCuts + 1), C.part j ⊆ E.colDiv.part b) :
    ContainsMinorBlock R C D := by
  rcases hDE with ⟨_hrowCuts, hcolCuts, _i, _hrows, hcols⟩
  rcases hcol with ⟨j, b, hsub⟩
  right
  let bD : Fin (D.colCuts + 1) :=
    (finCongr (by omega : E.colCuts + 1 = D.colCuts + 1)) b
  refine ⟨j, bD, ?_⟩
  intro x hx
  have hxE := hsub hx
  have hpart := hcols b
  rw [hpart] at hxE
  simpa [Division.castIndex, bD] using hxE

end MatrixDivision

/-- Row-side counting core of the first item of Theorem 10.

If one row block of a `k`-mixed minor is contained in a row part of a division,
while no column block of the mixed minor is contained in any column part, then
the containing row part sees at least one nonconstant error for every other
minor column block.  Taking the even-indexed column blocks gives `d + 2`
distinct errors when `2 * d + 2 < k`, contradicting error value at most `d`. -/
theorem false_of_rowBlock_subset_of_no_colBlock_subset {n m k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m k} {D : MatrixDivision n m}
    (hk : 2 * d + 2 < k)
    (hmix : ∀ i j : Fin k, CellMixed M R C i j)
    (herror : MatrixDivision.NonconstantErrorValueAtMost M D d)
    {i : Fin k} {a : Fin (D.rowCuts + 1)}
    (hrow : R.part i ⊆ D.rowDiv.part a)
    (hnoCol : ¬ ∃ j : Fin k, ∃ b : Fin (D.colCuts + 1),
      C.part j ⊆ D.colDiv.part b) :
    False := by
  classical
  let idx : Fin (d + 2) → Fin k := fun u => ⟨2 * u.1, by omega⟩
  have hwit :
      ∀ u : Fin (d + 2),
        ∃ r₁, r₁ ∈ R.part i ∧
          ∃ r₂, r₂ ∈ R.part i ∧
            ∃ c, c ∈ C.part (idx u) ∧ M r₁ c ≠ M r₂ c := by
    intro u
    exact (not_cellVertical_iff_exists M R C i (idx u)).mp (hmix i (idx u)).1
  choose r₁ hr₁ hrest₁ using hwit
  choose r₂ hr₂ hrest₂ using hrest₁
  choose c hc hneq using hrest₂
  have hcover : ∀ u : Fin (d + 2), ∃ b : Fin (D.colCuts + 1), c u ∈ D.colDiv.part b := by
    intro u
    exact D.colDiv.part_cover (c u)
  choose b hb using hcover
  have hnotconst :
      ∀ u : Fin (d + 2),
        ¬ ZoneConstant M (D.rowDiv.part a) (D.colDiv.part (b u)) := by
    intro u hconst
    exact hneq u (hconst (hrow (hr₁ u)) (hrow (hr₂ u)) (hb u) (hb u))
  have hb_mem :
      ∀ u : Fin (d + 2), b u ∈ MatrixDivision.nonconstantRowErrorSet M D a := by
    intro u
    simp [MatrixDivision.nonconstantRowErrorSet, hnotconst u]
  have hbinj : Function.Injective b := by
    intro u v huv
    by_cases huv' : u = v
    · exact huv'
    · rcases lt_or_gt_of_ne huv' with huvlt | hvult
      · have hmid_lt : 2 * u.1 + 1 < k := by omega
        let mid : Fin k := ⟨2 * u.1 + 1, hmid_lt⟩
        have hidx_mid : idx u < mid := by
          rw [Fin.lt_def]
          simp [idx, mid]
        have hmid_idx : mid < idx v := by
          rw [Fin.lt_def]
          simp [idx, mid]
          omega
        have hsubset : C.part mid ⊆ D.colDiv.part (b u) :=
          Division.part_subset_of_between_mem_same_part C D.colDiv
            hidx_mid hmid_idx
            (hc u) (hb u) (hc v) (by simpa [huv] using hb v)
        exact False.elim (hnoCol ⟨mid, b u, hsubset⟩)
      · have hmid_lt : 2 * v.1 + 1 < k := by omega
        let mid : Fin k := ⟨2 * v.1 + 1, hmid_lt⟩
        have hidx_mid : idx v < mid := by
          rw [Fin.lt_def]
          simp [idx, mid]
        have hmid_idx : mid < idx u := by
          rw [Fin.lt_def]
          simp [idx, mid]
          omega
        have hsubset : C.part mid ⊆ D.colDiv.part (b v) :=
          Division.part_subset_of_between_mem_same_part C D.colDiv
            hidx_mid hmid_idx
            (hc v) (hb v) (hc u) (by simpa [huv] using hb u)
        exact False.elim (hnoCol ⟨mid, b v, hsubset⟩)
  have hsubset_image :
      (Finset.univ.image b : Finset (Fin (D.colCuts + 1))) ⊆
        MatrixDivision.nonconstantRowErrorSet M D a := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨u, _hu, rfl⟩
    exact hb_mem u
  have hcard :
      d + 2 ≤ (MatrixDivision.nonconstantRowErrorSet M D a).card := by
    calc
      d + 2 = (Finset.univ : Finset (Fin (d + 2))).card := by simp
      _ = (Finset.univ.image b : Finset (Fin (D.colCuts + 1))).card := by
        rw [Finset.card_image_of_injective _ hbinj]
      _ ≤ (MatrixDivision.nonconstantRowErrorSet M D a).card :=
        Finset.card_le_card hsubset_image
  have hle := herror.1 a
  omega

/-- Column-side counting core of the first item of Theorem 10, dual to
`false_of_rowBlock_subset_of_no_colBlock_subset`. -/
theorem false_of_colBlock_subset_of_no_rowBlock_subset {n m k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n k} {C : Division m k} {D : MatrixDivision n m}
    (hk : 2 * d + 2 < k)
    (hmix : ∀ i j : Fin k, CellMixed M R C i j)
    (herror : MatrixDivision.NonconstantErrorValueAtMost M D d)
    {j : Fin k} {b : Fin (D.colCuts + 1)}
    (hcol : C.part j ⊆ D.colDiv.part b)
    (hnoRow : ¬ ∃ i : Fin k, ∃ a : Fin (D.rowCuts + 1),
      R.part i ⊆ D.rowDiv.part a) :
    False := by
  classical
  let idx : Fin (d + 2) → Fin k := fun u => ⟨2 * u.1, by omega⟩
  have hwit :
      ∀ u : Fin (d + 2),
        ∃ r, r ∈ R.part (idx u) ∧
          ∃ c₁, c₁ ∈ C.part j ∧
            ∃ c₂, c₂ ∈ C.part j ∧ M r c₁ ≠ M r c₂ := by
    intro u
    exact (not_cellHorizontal_iff_exists M R C (idx u) j).mp (hmix (idx u) j).2
  choose r hr hrest₁ using hwit
  choose c₁ hc₁ hrest₂ using hrest₁
  choose c₂ hc₂ hneq using hrest₂
  have hcover : ∀ u : Fin (d + 2), ∃ a : Fin (D.rowCuts + 1), r u ∈ D.rowDiv.part a := by
    intro u
    exact D.rowDiv.part_cover (r u)
  choose a ha using hcover
  have hnotconst :
      ∀ u : Fin (d + 2),
        ¬ ZoneConstant M (D.rowDiv.part (a u)) (D.colDiv.part b) := by
    intro u hconst
    exact hneq u (hconst (ha u) (ha u) (hcol (hc₁ u)) (hcol (hc₂ u)))
  have ha_mem :
      ∀ u : Fin (d + 2), a u ∈ MatrixDivision.nonconstantColErrorSet M D b := by
    intro u
    simp [MatrixDivision.nonconstantColErrorSet, hnotconst u]
  have hainj : Function.Injective a := by
    intro u v huv
    by_cases huv' : u = v
    · exact huv'
    · rcases lt_or_gt_of_ne huv' with huvlt | hvult
      · have hmid_lt : 2 * u.1 + 1 < k := by omega
        let mid : Fin k := ⟨2 * u.1 + 1, hmid_lt⟩
        have hidx_mid : idx u < mid := by
          rw [Fin.lt_def]
          simp [idx, mid]
        have hmid_idx : mid < idx v := by
          rw [Fin.lt_def]
          simp [idx, mid]
          omega
        have hsubset : R.part mid ⊆ D.rowDiv.part (a u) :=
          Division.part_subset_of_between_mem_same_part R D.rowDiv
            hidx_mid hmid_idx
            (hr u) (ha u) (hr v) (by simpa [huv] using ha v)
        exact False.elim (hnoRow ⟨mid, a u, hsubset⟩)
      · have hmid_lt : 2 * v.1 + 1 < k := by omega
        let mid : Fin k := ⟨2 * v.1 + 1, hmid_lt⟩
        have hidx_mid : idx v < mid := by
          rw [Fin.lt_def]
          simp [idx, mid]
        have hmid_idx : mid < idx u := by
          rw [Fin.lt_def]
          simp [idx, mid]
          omega
        have hsubset : R.part mid ⊆ D.rowDiv.part (a v) :=
          Division.part_subset_of_between_mem_same_part R D.rowDiv
            hidx_mid hmid_idx
            (hr v) (ha v) (hr u) (by simpa [huv] using ha u)
        exact False.elim (hnoRow ⟨mid, a v, hsubset⟩)
  have hsubset_image :
      (Finset.univ.image a : Finset (Fin (D.rowCuts + 1))) ⊆
        MatrixDivision.nonconstantColErrorSet M D b := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨u, _hu, rfl⟩
    exact ha_mem u
  have hcard :
      d + 2 ≤ (MatrixDivision.nonconstantColErrorSet M D b).card := by
    calc
      d + 2 = (Finset.univ : Finset (Fin (d + 2))).card := by simp
      _ = (Finset.univ.image a : Finset (Fin (D.rowCuts + 1))).card := by
        rw [Finset.card_image_of_injective _ hainj]
      _ ≤ (MatrixDivision.nonconstantColErrorSet M D b).card :=
        Finset.card_le_card hsubset_image
  have hle := herror.2 b
  omega

/-- Ordered first item of matrix Theorem 10: a bounded-error division sequence
for the current row and column orders bounds the matrix mixed number linearly. -/
theorem theorem10_ordered_matrix_mixed_number_le_of_twin_ordered_at_most
    {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) :
    MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ 2 * d + 2 := by
  classical
  rintro ⟨S⟩
  by_contra hle
  have hkgt : 2 * d + 2 < matrixMixedNumber M := Nat.lt_of_not_ge hle
  have hkpos : 0 < matrixMixedNumber M := by omega
  rcases hasMixedMinor_matrixMixedNumber M with hzero | hminor
  · omega
  rcases hminor with ⟨R, C, hmix⟩
  let P : ℕ → Prop := fun s =>
    s ≤ S.stepCount ∧ MatrixDivision.ContainsMinorBlock R C (S.division s)
  have hex : ∃ s, P s := by
    refine ⟨S.stepCount, le_rfl, ?_⟩
    exact MatrixDivision.containsMinorBlock_of_isCoarsest R C S.ends hkpos
  let s : ℕ := Nat.find hex
  have hsP : P s := Nat.find_spec hex
  cases hs : s with
  | zero =>
      have hcontains0 : MatrixDivision.ContainsMinorBlock R C (S.division 0) := by
        simpa [P, s, hs] using hsP.2
      exact (MatrixDivision.not_containsMinorBlock_of_isFinest_of_mixed
        hkpos S.starts hmix) hcontains0
  | succ t =>
      have hcur : MatrixDivision.ContainsMinorBlock R C (S.division (t + 1)) := by
        simpa [P, s, hs] using hsP.2
      have hsle : t + 1 ≤ S.stepCount := by
        simpa [P, s, hs] using hsP.1
      have htstep : t < S.stepCount := by omega
      have hprev_not :
          ¬ MatrixDivision.ContainsMinorBlock R C (S.division t) := by
        intro hprev
        have htP : P t := ⟨by omega, hprev⟩
        have hmin : s ≤ t := Nat.find_min' hex htP
        omega
      have hstep := S.step_fuses t htstep
      rcases hcur with hrowcur | hcolcur
      · rcases hstep with hrowF | hcolF
        · have hnoCol :
              ¬ ∃ j : Fin (matrixMixedNumber M),
                  ∃ b : Fin ((S.division (t + 1)).colCuts + 1),
                    C.part j ⊆ (S.division (t + 1)).colDiv.part b := by
            intro hcol
            exact hprev_not
              (MatrixDivision.colBlock_subset_prev_of_hasRowFusion hrowF hcol)
          rcases hrowcur with ⟨i, a, hrow⟩
          exact false_of_rowBlock_subset_of_no_colBlock_subset
            hkgt hmix (S.errorValue_le (t + 1) hsle) hrow hnoCol
        · exact False.elim
            (hprev_not
              (MatrixDivision.rowBlock_subset_prev_of_hasColFusion hcolF hrowcur))
      · rcases hstep with hrowF | hcolF
        · exact False.elim
            (hprev_not
              (MatrixDivision.colBlock_subset_prev_of_hasRowFusion hrowF hcolcur))
        · have hnoRow :
              ¬ ∃ i : Fin (matrixMixedNumber M),
                  ∃ a : Fin ((S.division (t + 1)).rowCuts + 1),
                    R.part i ⊆ (S.division (t + 1)).rowDiv.part a := by
            intro hrow
            exact hprev_not
              (MatrixDivision.rowBlock_subset_prev_of_hasColFusion hcolF hrow)
          rcases hcolcur with ⟨j, b, hcol⟩
          exact false_of_colBlock_subset_of_no_rowBlock_subset
            hkgt hmix (S.errorValue_le (t + 1) hsle) hcol hnoRow

/-- Predicate-wrapper form of the first item of matrix Theorem 10. -/
theorem theorem10_first_item_ordered :
    MatrixMixedNumberBoundedByTwinOrdered (α := α) theorem10MatrixMixedNumberBound := by
  intro n m d M hM
  exact theorem10_ordered_matrix_mixed_number_le_of_twin_ordered_at_most M hM

namespace MatrixPartition

/-- Split every part of a finite partition according to a label function
attached to that base part.  Empty fibers are discarded. -/
noncomputable def splitPartsByLabel {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    (P : Finset (Finset α)) (label : Finset α → α → β) :
    Finset (Finset α) := by
  classical
  exact
    (P.biUnion fun A =>
      (Finset.univ : Finset β).image fun b =>
        A.filter fun x => label A x = b).filter fun A => A.Nonempty

theorem mem_splitPartsByLabel {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    {F : Finset α} :
    F ∈ splitPartsByLabel P label ↔
      F.Nonempty ∧
        ∃ A ∈ P, ∃ b : β, F = A.filter fun x => label A x = b := by
  classical
  unfold splitPartsByLabel
  rw [Finset.mem_filter, Finset.mem_biUnion]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨A, hA, b, hFb⟩, hF⟩
    exact ⟨hF, A, hA, b, hFb.symm⟩
  · rintro ⟨hF, A, hA, b, rfl⟩
    exact ⟨⟨A, hA, b, rfl⟩, hF⟩

theorem splitPartsByLabel_subset_base {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    {F : Finset α}
    (hF : F ∈ splitPartsByLabel P label) :
    ∃ A ∈ P, F ⊆ A := by
  classical
  rcases (mem_splitPartsByLabel.mp hF).2 with ⟨A, hA, b, rfl⟩
  exact ⟨A, hA, by intro x hx; exact (Finset.mem_filter.mp hx).1⟩

theorem splitPartsByLabel_nonempty {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    {F : Finset α}
    (hF : F ∈ splitPartsByLabel P label) :
    F.Nonempty :=
  (mem_splitPartsByLabel.mp hF).1

theorem splitPartsByLabel_cover {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    (hcover : ∀ x : α, ∃ A ∈ P, x ∈ A) :
    ∀ x : α, ∃ F ∈ splitPartsByLabel P label, x ∈ F := by
  classical
  intro x
  rcases hcover x with ⟨A, hA, hxA⟩
  let F : Finset α := A.filter fun y => label A y = label A x
  have hxF : x ∈ F := by simp [F, hxA]
  have hFnon : F.Nonempty := ⟨x, hxF⟩
  have hFmem : F ∈ splitPartsByLabel P label := by
    rw [mem_splitPartsByLabel]
    exact ⟨hFnon, A, hA, label A x, rfl⟩
  exact ⟨F, hFmem, hxF⟩

theorem splitPartsByLabel_disjoint {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {P : Finset (Finset α)} {label : Finset α → α → β}
    (hdisj : ∀ ⦃A B⦄, A ∈ P → B ∈ P → A ≠ B → Disjoint A B)
    {F G : Finset α}
    (hF : F ∈ splitPartsByLabel P label)
    (hG : G ∈ splitPartsByLabel P label)
    (hFG : F ≠ G) :
    Disjoint F G := by
  classical
  rw [Finset.disjoint_left]
  intro x hxF hxG
  rcases (mem_splitPartsByLabel.mp hF).2 with ⟨A, hA, b, hFdef⟩
  rcases (mem_splitPartsByLabel.mp hG).2 with ⟨B, hB, c, hGdef⟩
  subst F
  subst G
  have hxA : x ∈ A := (Finset.mem_filter.mp hxF).1
  have hxb : label A x = b := (Finset.mem_filter.mp hxF).2
  have hxB : x ∈ B := (Finset.mem_filter.mp hxG).1
  have hxc : label B x = c := (Finset.mem_filter.mp hxG).2
  by_cases hAB : A = B
  · subst B
    have hbc : b = c := hxb.symm.trans hxc
    apply hFG
    simp [hbc]
  · exact Finset.disjoint_left.mp (hdisj hA hB hAB) hxA hxB

/-- Refining each row part and each column part by bounded labels gives a
matrix partition. -/
noncomputable def refineByLabels {n m : ℕ} {β γ : Type*}
    [DecidableEq β] [Fintype β] [DecidableEq γ] [Fintype γ]
    (P : MatrixPartition n m)
    (rowLabel : Finset (Fin n) → Fin n → β)
    (colLabel : Finset (Fin m) → Fin m → γ) :
    MatrixPartition n m where
  rowParts := splitPartsByLabel P.rowParts rowLabel
  row_nonempty := by
    intro R hR
    exact splitPartsByLabel_nonempty hR
  row_disjoint := by
    intro R S hR hS hRS
    exact splitPartsByLabel_disjoint P.row_disjoint hR hS hRS
  row_cover := by
    exact splitPartsByLabel_cover P.row_cover
  colParts := splitPartsByLabel P.colParts colLabel
  col_nonempty := by
    intro C hC
    exact splitPartsByLabel_nonempty hC
  col_disjoint := by
    intro C D hC hD hCD
    exact splitPartsByLabel_disjoint P.col_disjoint hC hD hCD
  col_cover := by
    exact splitPartsByLabel_cover P.col_cover

@[simp] theorem rowParts_refineByLabels {n m : ℕ} {β γ : Type*}
    [DecidableEq β] [Fintype β] [DecidableEq γ] [Fintype γ]
    (P : MatrixPartition n m)
    (rowLabel : Finset (Fin n) → Fin n → β)
    (colLabel : Finset (Fin m) → Fin m → γ) :
    (P.refineByLabels rowLabel colLabel).rowParts =
      splitPartsByLabel P.rowParts rowLabel :=
  rfl

@[simp] theorem colParts_refineByLabels {n m : ℕ} {β γ : Type*}
    [DecidableEq β] [Fintype β] [DecidableEq γ] [Fintype γ]
    (P : MatrixPartition n m)
    (rowLabel : Finset (Fin n) → Fin n → β)
    (colLabel : Finset (Fin m) → Fin m → γ) :
    (P.refineByLabels rowLabel colLabel).colParts =
      splitPartsByLabel P.colParts colLabel :=
  rfl

theorem partsRRefine_splitPartsByLabel {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {r : ℕ}
    {P : Finset (Finset α)} {label : Finset α → α → β}
    (hdisj : ∀ ⦃A B⦄, A ∈ P → B ∈ P → A ≠ B → Disjoint A B)
    (hr : Fintype.card β ≤ r) :
    PartsRRefine (splitPartsByLabel P label) P r := by
  classical
  constructor
  · intro F hF
    exact splitPartsByLabel_subset_base hF
  · intro A hA
    let fibers : Finset (Finset α) :=
      (Finset.univ : Finset β).image fun b =>
        A.filter fun x => label A x = b
    have hsubset :
        (splitPartsByLabel P label).filter (fun F => F ⊆ A) ⊆ fibers := by
      intro F hF
      have hFmem : F ∈ splitPartsByLabel P label := (Finset.mem_filter.mp hF).1
      have hFsub : F ⊆ A := (Finset.mem_filter.mp hF).2
      rcases mem_splitPartsByLabel.mp hFmem with ⟨hFne, B, hB, b, hFdef⟩
      have hBA : B = A := by
        rcases hFne with ⟨x, hxF⟩
        have hxB : x ∈ B := by
          rw [hFdef] at hxF
          exact (Finset.mem_filter.mp hxF).1
        have hxA : x ∈ A := hFsub hxF
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj hB hA hne) hxB hxA
      subst B
      subst F
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
    have hcard :
        ((splitPartsByLabel P label).filter fun F => F ⊆ A).card ≤ fibers.card :=
      Finset.card_le_card hsubset
    have hfibers : fibers.card ≤ Fintype.card β := by
      calc
        fibers.card ≤ (Finset.univ : Finset β).card := Finset.card_image_le
        _ = Fintype.card β := by simp
    exact le_trans hcard (le_trans hfibers hr)

/-- Bounded refinement is preserved by compatible finite labels.  The factor
is multiplied by the number of labels: over each coarse part there are at most
`rb` old base parts, and each old base part contributes at most one fiber for
each label. -/
theorem partsRRefine_splitPartsByLabel_of_partsRRefine {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype β]
    {rb : ℕ}
    {P Q : Finset (Finset α)}
    {pLabel qLabel : Finset α → α → β}
    (hQdisj : ∀ ⦃A B⦄, A ∈ Q → B ∈ Q → A ≠ B → Disjoint A B)
    (hPQ : PartsRRefine P Q rb)
    (hcompat :
      ∀ ⦃A B x y⦄, A ∈ P → B ∈ Q → A ⊆ B →
        x ∈ A → y ∈ A → pLabel A x = pLabel A y →
          qLabel B x = qLabel B y) :
    PartsRRefine (splitPartsByLabel P pLabel)
      (splitPartsByLabel Q qLabel) (rb * Fintype.card β) := by
  classical
  constructor
  · intro F hF
    rcases mem_splitPartsByLabel.mp hF with ⟨hFne, A, hA, b, hFdef⟩
    rcases hPQ.1 hA with ⟨B, hB, hAB⟩
    rcases hFne with ⟨x, hxF⟩
    have hxA : x ∈ A := by
      rw [hFdef] at hxF
      exact (Finset.mem_filter.mp hxF).1
    let G : Finset α := B.filter fun y => qLabel B y = qLabel B x
    have hxG : x ∈ G := by simp [G, hAB hxA]
    have hGmem : G ∈ splitPartsByLabel Q qLabel := by
      rw [mem_splitPartsByLabel]
      exact ⟨⟨x, hxG⟩, B, hB, qLabel B x, rfl⟩
    refine ⟨G, hGmem, ?_⟩
    intro y hyF
    rw [hFdef] at hyF
    have hyA : y ∈ A := (Finset.mem_filter.mp hyF).1
    have hyb : pLabel A y = b := (Finset.mem_filter.mp hyF).2
    have hxb : pLabel A x = b := by
      rw [hFdef] at hxF
      exact (Finset.mem_filter.mp hxF).2
    have hqy : qLabel B y = qLabel B x := by
      exact hcompat hA hB hAB hyA hxA (hyb.trans hxb.symm)
    simp [G, hAB hyA, hqy]
  · intro G hG
    rcases mem_splitPartsByLabel.mp hG with ⟨hGne, B, hB, c, hGdef⟩
    let baseInside : Finset (Finset α) := P.filter fun A => A ⊆ B
    let candidates : Finset (Finset α) :=
      baseInside.biUnion fun A =>
        (Finset.univ : Finset β).image fun b =>
          A.filter fun x => pLabel A x = b
    have hsubset :
        (splitPartsByLabel P pLabel).filter (fun F => F ⊆ G) ⊆ candidates := by
      intro F hF
      have hFmem : F ∈ splitPartsByLabel P pLabel := (Finset.mem_filter.mp hF).1
      have hFG : F ⊆ G := (Finset.mem_filter.mp hF).2
      rcases mem_splitPartsByLabel.mp hFmem with ⟨hFne, A, hA, b, hFdef⟩
      have hAsubB : A ⊆ B := by
        rcases hPQ.1 hA with ⟨B', hB', hAB'⟩
        rcases hFne with ⟨x, hxF⟩
        have hxA : x ∈ A := by
          rw [hFdef] at hxF
          exact (Finset.mem_filter.mp hxF).1
        have hxG : x ∈ G := hFG hxF
        have hxB : x ∈ B := by
          rw [hGdef] at hxG
          exact (Finset.mem_filter.mp hxG).1
        have hxB' : x ∈ B' := hAB' hxA
        have hB'eq : B' = B := by
          by_contra hne
          exact Finset.disjoint_left.mp (hQdisj hB' hB hne) hxB' hxB
        simpa [hB'eq] using hAB'
      have hAbase : A ∈ baseInside := by
        simp [baseInside, hA, hAsubB]
      subst F
      exact Finset.mem_biUnion.mpr
        ⟨A, hAbase, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩
    have hcard_candidates : candidates.card ≤ baseInside.card * Fintype.card β := by
      unfold candidates
      refine Finset.card_biUnion_le_card_mul _ _ _ ?_
      intro A hA
      calc
        ((Finset.univ : Finset β).image fun b =>
            A.filter fun x => pLabel A x = b).card
            ≤ (Finset.univ : Finset β).card := Finset.card_image_le
        _ = Fintype.card β := by simp
    have hbase : baseInside.card ≤ rb := by
      exact hPQ.2 hB
    exact le_trans (Finset.card_le_card hsubset)
      (le_trans hcard_candidates (Nat.mul_le_mul_right _ hbase))

/-- A family of disjoint nonempty parts `2`-refines the family obtained by
merging two of its parts. -/
theorem partsRRefine_self_insert_union_erase {α : Type*} [DecidableEq α]
    {P : Finset (Finset α)} {R S : Finset α}
    (hnonempty : ∀ ⦃A⦄, A ∈ P → A.Nonempty)
    (hdisj : ∀ ⦃A B⦄, A ∈ P → B ∈ P → A ≠ B → Disjoint A B)
    (hR : R ∈ P) (hS : S ∈ P) (_hRS : R ≠ S) :
    PartsRRefine P (insert (R ∪ S) ((P.erase R).erase S)) 2 := by
  classical
  constructor
  · intro A hA
    by_cases hAR : A = R
    · subst A
      refine ⟨R ∪ S, Finset.mem_insert_self _ _, ?_⟩
      intro x hx
      exact Finset.mem_union_left S hx
    · by_cases hAS : A = S
      · subst A
        refine ⟨R ∪ S, Finset.mem_insert_self _ _, ?_⟩
        intro x hx
        exact Finset.mem_union_right R hx
      · refine ⟨A, Finset.mem_insert.mpr ?_, by intro x hx; exact hx⟩
        exact Or.inr (Finset.mem_erase.mpr ⟨hAS, Finset.mem_erase.mpr ⟨hAR, hA⟩⟩)
  · intro B hB
    rcases Finset.mem_insert.mp hB with hBunion | hBold
    · subst B
      have hsubset :
          (P.filter fun A => A ⊆ R ∪ S) ⊆ ({R, S} : Finset (Finset α)) := by
        intro A hAfilter
        have hA : A ∈ P := (Finset.mem_filter.mp hAfilter).1
        have hAsub : A ⊆ R ∪ S := (Finset.mem_filter.mp hAfilter).2
        by_cases hAR : A = R
        · simp [hAR]
        · by_cases hAS : A = S
          · simp [hAS]
          · rcases hnonempty hA with ⟨x, hxA⟩
            have hxUnion : x ∈ R ∪ S := hAsub hxA
            rcases Finset.mem_union.mp hxUnion with hxR | hxS
            · exact False.elim
                (Finset.disjoint_left.mp (hdisj hA hR hAR) hxA hxR)
            · exact False.elim
                (Finset.disjoint_left.mp (hdisj hA hS hAS) hxA hxS)
      calc
        (P.filter fun A => A ⊆ R ∪ S).card
            ≤ ({R, S} : Finset (Finset α)).card := Finset.card_le_card hsubset
        _ ≤ 2 := by
          by_cases h : R = S <;> simp [h]
    · have hBmem : B ∈ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2
      have hBneR : B ≠ R :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).1
      have hBneS : B ≠ S := (Finset.mem_erase.mp hBold).1
      have hsubset :
          (P.filter fun A => A ⊆ B) ⊆ ({B} : Finset (Finset α)) := by
        intro A hAfilter
        have hA : A ∈ P := (Finset.mem_filter.mp hAfilter).1
        have hAsub : A ⊆ B := (Finset.mem_filter.mp hAfilter).2
        by_cases hAB : A = B
        · simp [hAB]
        · rcases hnonempty hA with ⟨x, hxA⟩
          have hxB : x ∈ B := hAsub hxA
          exact False.elim
            (Finset.disjoint_left.mp (hdisj hA hBmem hAB) hxA hxB)
      calc
        (P.filter fun A => A ⊆ B).card
            ≤ ({B} : Finset (Finset α)).card := Finset.card_le_card hsubset
        _ ≤ 2 := by simp

/-- A disjoint nonempty family `r`-refines itself for every positive `r`. -/
theorem partsRRefine_refl_of_partition {α : Type*} [DecidableEq α]
    {P : Finset (Finset α)} {r : ℕ}
    (hnonempty : ∀ ⦃A⦄, A ∈ P → A.Nonempty)
    (hdisj : ∀ ⦃A B⦄, A ∈ P → B ∈ P → A ≠ B → Disjoint A B)
    (hr : 1 ≤ r) :
    PartsRRefine P P r := by
  classical
  constructor
  · intro A hA
    exact ⟨A, hA, by intro x hx; exact hx⟩
  · intro B hB
    have hsubset : (P.filter fun A => A ⊆ B) ⊆ ({B} : Finset (Finset α)) := by
      intro A hAfilter
      have hA : A ∈ P := (Finset.mem_filter.mp hAfilter).1
      have hAB : A ⊆ B := (Finset.mem_filter.mp hAfilter).2
      by_cases h : A = B
      · simp [h]
      · rcases hnonempty hA with ⟨x, hxA⟩
        have hxB : x ∈ B := hAB hxA
        exact False.elim (Finset.disjoint_left.mp (hdisj hA hB h) hxA hxB)
    calc
      (P.filter fun A => A ⊆ B).card ≤ ({B} : Finset (Finset α)).card :=
        Finset.card_le_card hsubset
      _ ≤ r := by simpa using hr

theorem partsRRefine_mono {α : Type*} [DecidableEq α]
    {P Q : Finset (Finset α)} {r s : ℕ}
    (hrs : r ≤ s) (h : PartsRRefine P Q r) :
    PartsRRefine P Q s := by
  constructor
  · exact h.1
  · intro B hB
    exact le_trans (h.2 hB) hrs

theorem rrefines_mono {n m r s : ℕ}
    {P Q : MatrixPartition n m}
    (hrs : r ≤ s) (h : RRefines P Q r) :
    RRefines P Q s := by
  exact ⟨partsRRefine_mono hrs h.1, partsRRefine_mono hrs h.2⟩

/-- If a filter predicate is strictly strengthened inside a finite set, the
filtered cardinality strictly increases. -/
theorem card_filter_lt_card_filter_of_exists {α : Type*} [DecidableEq α]
    {S : Finset α} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hsub : ∀ x, p x → q x)
    (hex : ∃ x ∈ S, q x ∧ ¬ p x) :
    (S.filter p).card < (S.filter q).card := by
  classical
  have hsubset : S.filter p ⊆ S.filter q := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, hsub x (Finset.mem_filter.mp hx).2⟩
  rcases hex with ⟨x, hxS, hxq, hxp⟩
  have hxqmem : x ∈ S.filter q := Finset.mem_filter.mpr ⟨hxS, hxq⟩
  have hxnotpmem : x ∉ S.filter p := by
    intro hx
    exact hxp (Finset.mem_filter.mp hx).2
  have hssub : S.filter p ⊂ S.filter q := by
    refine ⟨hsubset, ?_⟩
    intro hrev
    exact hxnotpmem (hrev hxqmem)
  exact Finset.card_lt_card hssub

/-- Merge two distinct row parts of a matrix partition. -/
noncomputable def rowContract {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (_hRS : R ≠ S) : MatrixPartition n m where
  rowParts := insert (R ∪ S) ((P.rowParts.erase R).erase S)
  row_nonempty := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact (P.row_nonempty hR).mono (by intro x hx; exact Finset.mem_union_left _ hx)
    · exact P.row_nonempty ((Finset.mem_erase.mp (Finset.mem_erase.mp hA).2).2)
  row_disjoint := by
    intro A B hA hB hAB
    rw [Finset.disjoint_left]
    rcases Finset.mem_insert.mp hA with rfl | hAold <;>
      rcases Finset.mem_insert.mp hB with rfl | hBold
    · exact (hAB rfl).elim
    · intro x hx hxB
      rcases Finset.mem_union.mp hx with hxR | hxS
      · exact Finset.disjoint_left.mp
          (P.row_disjoint hR ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2)
            (by intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).1 h.symm))
          hxR hxB
      · exact Finset.disjoint_left.mp
          (P.row_disjoint hS ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2)
            (by intro h; exact (Finset.mem_erase.mp hBold).1 h.symm))
          hxS hxB
    · intro x hxA hx
      rcases Finset.mem_union.mp hx with hxR | hxS
      · exact Finset.disjoint_left.mp
          (P.row_disjoint ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2) hR
            (by intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).1 h))
          hxA hxR
      · exact Finset.disjoint_left.mp
          (P.row_disjoint ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2) hS
            (by intro h; exact (Finset.mem_erase.mp hAold).1 h))
          hxA hxS
    · exact Finset.disjoint_left.mp
        (P.row_disjoint
          ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2)
          ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2) hAB)
  row_cover := by
    intro r
    rcases P.row_cover r with ⟨A, hA, hrA⟩
    by_cases hAR : A = R
    · refine ⟨R ∪ S, Finset.mem_insert_self _ _, ?_⟩
      subst A
      exact Finset.mem_union_left _ hrA
    · by_cases hAS : A = S
      · refine ⟨R ∪ S, Finset.mem_insert_self _ _, ?_⟩
        subst A
        exact Finset.mem_union_right _ hrA
      · refine ⟨A, Finset.mem_insert.mpr (Or.inr ?_), hrA⟩
        exact Finset.mem_erase.mpr ⟨hAS, Finset.mem_erase.mpr ⟨hAR, hA⟩⟩
  colParts := P.colParts
  col_nonempty := P.col_nonempty
  col_disjoint := P.col_disjoint
  col_cover := P.col_cover

/-- Merge two distinct column parts of a matrix partition. -/
noncomputable def colContract {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (_hCD : C ≠ D) : MatrixPartition n m where
  rowParts := P.rowParts
  row_nonempty := P.row_nonempty
  row_disjoint := P.row_disjoint
  row_cover := P.row_cover
  colParts := insert (C ∪ D) ((P.colParts.erase C).erase D)
  col_nonempty := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact (P.col_nonempty hC).mono (by intro x hx; exact Finset.mem_union_left _ hx)
    · exact P.col_nonempty ((Finset.mem_erase.mp (Finset.mem_erase.mp hA).2).2)
  col_disjoint := by
    intro A B hA hB hAB
    rw [Finset.disjoint_left]
    rcases Finset.mem_insert.mp hA with rfl | hAold <;>
      rcases Finset.mem_insert.mp hB with rfl | hBold
    · exact (hAB rfl).elim
    · intro x hx hxB
      rcases Finset.mem_union.mp hx with hxC | hxD
      · exact Finset.disjoint_left.mp
          (P.col_disjoint hC ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2)
            (by intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).1 h.symm))
          hxC hxB
      · exact Finset.disjoint_left.mp
          (P.col_disjoint hD ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2)
            (by intro h; exact (Finset.mem_erase.mp hBold).1 h.symm))
          hxD hxB
    · intro x hxA hx
      rcases Finset.mem_union.mp hx with hxC | hxD
      · exact Finset.disjoint_left.mp
          (P.col_disjoint ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2) hC
            (by intro h; exact (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).1 h))
          hxA hxC
      · exact Finset.disjoint_left.mp
          (P.col_disjoint ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2) hD
            (by intro h; exact (Finset.mem_erase.mp hAold).1 h))
          hxA hxD
    · exact Finset.disjoint_left.mp
        (P.col_disjoint
          ((Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2)
          ((Finset.mem_erase.mp (Finset.mem_erase.mp hBold).2).2) hAB)
  col_cover := by
    intro c
    rcases P.col_cover c with ⟨A, hA, hcA⟩
    by_cases hAC : A = C
    · refine ⟨C ∪ D, Finset.mem_insert_self _ _, ?_⟩
      subst A
      exact Finset.mem_union_left _ hcA
    · by_cases hAD : A = D
      · refine ⟨C ∪ D, Finset.mem_insert_self _ _, ?_⟩
        subst A
        exact Finset.mem_union_right _ hcA
      · refine ⟨A, Finset.mem_insert.mpr (Or.inr ?_), hcA⟩
        exact Finset.mem_erase.mpr ⟨hAD, Finset.mem_erase.mpr ⟨hAC, hA⟩⟩

@[simp] theorem rowParts_rowContract {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    (P.rowContract hR hS hRS).rowParts =
      insert (R ∪ S) ((P.rowParts.erase R).erase S) :=
  rfl

@[simp] theorem colParts_colContract {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    (P.colContract hC hD hCD).colParts =
      insert (C ∪ D) ((P.colParts.erase C).erase D) :=
  rfl

@[simp] theorem colParts_rowContract {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    (P.rowContract hR hS hRS).colParts = P.colParts :=
  rfl

@[simp] theorem rowParts_colContract {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    (P.colContract hC hD hCD).rowParts = P.rowParts :=
  rfl

/-- A partition `2`-refines the result of one row contraction. -/
theorem rrefines_rowContract_self {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    RRefines P (P.rowContract hR hS hRS) 2 := by
  constructor
  · simpa [rowParts_rowContract] using
      partsRRefine_self_insert_union_erase
        P.row_nonempty P.row_disjoint hR hS hRS
  · simpa [colParts_rowContract] using
      partsRRefine_refl_of_partition
        P.col_nonempty P.col_disjoint (by decide : 1 ≤ 2)

/-- A partition `2`-refines the result of one column contraction. -/
theorem rrefines_colContract_self {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    RRefines P (P.colContract hC hD hCD) 2 := by
  constructor
  · simpa [rowParts_colContract] using
      partsRRefine_refl_of_partition
        P.row_nonempty P.row_disjoint (by decide : 1 ≤ 2)
  · simpa [colParts_colContract] using
      partsRRefine_self_insert_union_erase
        P.col_nonempty P.col_disjoint hC hD hCD

theorem isRowContraction_rowContract {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    IsRowContraction P (P.rowContract hR hS hRS) := by
  exact ⟨R, hR, S, hS, hRS, rfl, rfl⟩

theorem isColContraction_colContract {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    IsColContraction P (P.colContract hC hD hCD) := by
  exact ⟨C, hC, D, hD, hCD, rfl, rfl⟩

theorem rowParts_card_rowContract_lt {n m : ℕ} (P : MatrixPartition n m)
    {R S : Finset (Fin n)} (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts)
    (hRS : R ≠ S) :
    (P.rowContract hR hS hRS).rowParts.card < P.rowParts.card := by
  classical
  have hS_erase : S ∈ P.rowParts.erase R := Finset.mem_erase.mpr ⟨hRS.symm, hS⟩
  calc
    (P.rowContract hR hS hRS).rowParts.card
        ≤ ((P.rowParts.erase R).erase S).card + 1 := by
          simp [rowContract, Finset.card_insert_le]
    _ = (P.rowParts.erase R).card := by
          exact Finset.card_erase_add_one hS_erase
    _ < P.rowParts.card := Finset.card_erase_lt_of_mem hR

theorem colParts_card_colContract_lt {n m : ℕ} (P : MatrixPartition n m)
    {C D : Finset (Fin m)} (hC : C ∈ P.colParts) (hD : D ∈ P.colParts)
    (hCD : C ≠ D) :
    (P.colContract hC hD hCD).colParts.card < P.colParts.card := by
  classical
  have hD_erase : D ∈ P.colParts.erase C := Finset.mem_erase.mpr ⟨hCD.symm, hD⟩
  calc
    (P.colContract hC hD hCD).colParts.card
        ≤ ((P.colParts.erase C).erase D).card + 1 := by
          simp [colContract, Finset.card_insert_le]
    _ = (P.colParts.erase C).card := by
          exact Finset.card_erase_add_one hD_erase
    _ < P.colParts.card := Finset.card_erase_lt_of_mem hC

/-- The partition into singleton rows and singleton columns. -/
noncomputable def singleton (n m : ℕ) : MatrixPartition n m where
  rowParts := (Finset.univ : Finset (Fin n)).map ⟨fun r => ({r} : Finset (Fin n)), by
    intro a b h
    simpa using h⟩
  row_nonempty := by
    intro R hR
    rcases Finset.mem_map.mp hR with ⟨r, _hr, rfl⟩
    exact ⟨r, by simp⟩
  row_disjoint := by
    intro R S hR hS hRS
    rcases Finset.mem_map.mp hR with ⟨r, _hr, rfl⟩
    rcases Finset.mem_map.mp hS with ⟨s, _hs, rfl⟩
    rw [Finset.disjoint_left]
    intro x hx hy
    simp at hx hy
    subst r
    subst s
    exact hRS rfl
  row_cover := by
    intro r
    exact ⟨{r}, by simp, by simp⟩
  colParts := (Finset.univ : Finset (Fin m)).map ⟨fun c => ({c} : Finset (Fin m)), by
    intro a b h
    simpa using h⟩
  col_nonempty := by
    intro C hC
    rcases Finset.mem_map.mp hC with ⟨c, _hc, rfl⟩
    exact ⟨c, by simp⟩
  col_disjoint := by
    intro C D hC hD hCD
    rcases Finset.mem_map.mp hC with ⟨c, _hc, rfl⟩
    rcases Finset.mem_map.mp hD with ⟨d, _hd, rfl⟩
    rw [Finset.disjoint_left]
    intro x hx hy
    simp at hx hy
    subst c
    subst d
    exact hCD rfl
  col_cover := by
    intro c
    exact ⟨{c}, by simp, by simp⟩

@[simp] theorem rowParts_singleton (n m : ℕ) :
    (singleton n m).rowParts =
      (Finset.univ : Finset (Fin n)).map ⟨fun r => ({r} : Finset (Fin n)), by
        intro a b h
        simpa using h⟩ :=
  rfl

@[simp] theorem colParts_singleton (n m : ℕ) :
    (singleton n m).colParts =
      (Finset.univ : Finset (Fin m)).map ⟨fun c => ({c} : Finset (Fin m)), by
        intro a b h
        simpa using h⟩ :=
  rfl

/-- The singleton partition is finest. -/
theorem singleton_isFinest (n m : ℕ) :
    IsFinest (singleton n m) := by
  constructor
  · intro R hR
    rcases Finset.mem_map.mp hR with ⟨r, _hr, rfl⟩
    exact ⟨r, rfl⟩
  constructor
  · intro r
    simp [singleton]
  constructor
  · intro C hC
    rcases Finset.mem_map.mp hC with ⟨c, _hc, rfl⟩
    exact ⟨c, rfl⟩
  · intro c
    simp [singleton]

/-- A partition of a matrix with no rows has no row parts. -/
theorem rowParts_eq_empty_of_zero_rows {m : ℕ} (P : MatrixPartition 0 m) :
    P.rowParts = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro R hR
  rcases P.row_nonempty hR with ⟨r, _hr⟩
  exact Fin.elim0 r

/-- A partition of a matrix with no columns has no column parts. -/
theorem colParts_eq_empty_of_zero_cols {n : ℕ} (P : MatrixPartition n 0) :
    P.colParts = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  rcases P.col_nonempty hC with ⟨c, _hc⟩
  exact Fin.elim0 c

/-- Every partition of a matrix with no rows has error value zero. -/
theorem errorValueAtMost_zeroRows {m d : ℕ}
    (M : _root_.Matrix (Fin 0) (Fin m) α) (P : MatrixPartition 0 m) :
    ErrorValueAtMost M P d := by
  constructor
  · intro R hR
    rcases P.row_nonempty hR with ⟨r, _hr⟩
    exact Fin.elim0 r
  · intro C hC
    have hrows := rowParts_eq_empty_of_zero_rows P
    simp [colErrorSet, hrows]

/-- Every partition of a matrix with no columns has error value zero. -/
theorem errorValueAtMost_zeroCols {n d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin 0) α) (P : MatrixPartition n 0) :
    ErrorValueAtMost M P d := by
  constructor
  · intro R hR
    have hcols := colParts_eq_empty_of_zero_cols P
    simp [rowErrorSet, hcols]
  · intro C hC
    rcases P.col_nonempty hC with ⟨c, _hc⟩
    exact Fin.elim0 c

/-- Error-value bounds are monotone in the numerical bound. -/
theorem errorValueAtMost_mono {n m d e : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P : MatrixPartition n m}
    (hde : d ≤ e) (hP : ErrorValueAtMost M P d) :
    ErrorValueAtMost M P e := by
  constructor
  · intro R hR
    exact le_trans (hP.1 hR) hde
  · intro C hC
    exact le_trans (hP.2 hC) hde

/-- A nonempty partition refining a finest partition is itself finest. -/
theorem isFinest_of_refines_isFinest {n m : ℕ}
    {P Q : MatrixPartition n m}
    (href : Refines P Q) (hQ : IsFinest Q) :
    IsFinest P := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    rcases href.1 hR with ⟨B, hB, hRB⟩
    rcases hQ.1 hB with ⟨r, rfl⟩
    rcases P.row_nonempty hR with ⟨x, hxR⟩
    have hxr : x = r := by simpa using hRB hxR
    subst x
    refine ⟨r, ?_⟩
    apply Finset.Subset.antisymm hRB
    intro y hy
    simp at hy
    simpa [hy] using hxR
  · intro r
    rcases P.row_cover r with ⟨R, hR, hrR⟩
    rcases href.1 hR with ⟨B, hB, hRB⟩
    rcases hQ.1 hB with ⟨s, hs⟩
    have hrs : r = s := by
      have hrB : r ∈ B := hRB hrR
      simpa [hs] using hrB
    have hRsingle : R = ({r} : Finset (Fin n)) := by
      apply Finset.Subset.antisymm
      · intro y hy
        have hyB : y ∈ B := hRB hy
        simpa [hs, hrs] using hyB
      · intro y hy
        simp at hy
        simpa [hy] using hrR
    simpa [hRsingle] using hR
  · intro C hC
    rcases href.2 hC with ⟨D, hD, hCD⟩
    rcases hQ.2.2.1 hD with ⟨c, rfl⟩
    rcases P.col_nonempty hC with ⟨x, hxC⟩
    have hxc : x = c := by simpa using hCD hxC
    subst x
    refine ⟨c, ?_⟩
    apply Finset.Subset.antisymm hCD
    intro y hy
    simp at hy
    simpa [hy] using hxC
  · intro c
    rcases P.col_cover c with ⟨C, hC, hcC⟩
    rcases href.2 hC with ⟨D, hD, hCD⟩
    rcases hQ.2.2.1 hD with ⟨t, ht⟩
    have hct : c = t := by
      have hcD : c ∈ D := hCD hcC
      simpa [ht] using hcD
    have hCsingle : C = ({c} : Finset (Fin m)) := by
      apply Finset.Subset.antisymm
      · intro y hy
        have hyD : y ∈ D := hCD hy
        simpa [ht, hct] using hyD
      · intro y hy
        simp at hy
        simpa [hy] using hcC
    simpa [hCsingle] using hC

end MatrixPartition

/-- A contraction tail from a prescribed matrix partition to a coarsest
partition. -/
structure MatrixContractionTail {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) (d : ℕ)
    (P₀ : MatrixPartition n m) where
  /-- Number of remaining contractions. -/
  stepCount : ℕ
  /-- Partition at each time. -/
  partition : ℕ → MatrixPartition n m
  /-- The first partition is the prescribed one. -/
  starts : partition 0 = P₀
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Consecutive partitions are contractions. -/
  step_contracts :
    ∀ i, i < stepCount → MatrixPartition.IsContraction (partition i) (partition (i + 1))
  /-- Every partition in the tail has bounded error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

namespace MatrixContractionTail

/-- Prepend one matrix-partition contraction to a contraction tail. -/
noncomputable def cons {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P Q : MatrixPartition n m}
    (hPQ : MatrixPartition.IsContraction P Q)
    (hP : ErrorValueAtMost M P d)
    (S : MatrixContractionTail M d Q) :
    MatrixContractionTail M d P where
  stepCount := S.stepCount + 1
  partition := fun i =>
    match i with
    | 0 => P
    | j + 1 => S.partition j
  starts := rfl
  ends := by
    simpa using S.ends
  step_contracts := by
    intro i hi
    cases i with
    | zero =>
        simpa [S.starts] using hPQ
    | succ j =>
        have hj : j < S.stepCount := by omega
        simpa using S.step_contracts j hj
  errorValue_le := by
    intro i hi
    cases i with
    | zero =>
        simpa using hP
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.errorValue_le j hj

/-- Relax the numerical error bound on a contraction tail. -/
noncomputable def mono {n m d e : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P : MatrixPartition n m}
    (hde : d ≤ e) (S : MatrixContractionTail M d P) :
    MatrixContractionTail M e P where
  stepCount := S.stepCount
  partition := S.partition
  starts := S.starts
  ends := S.ends
  step_contracts := S.step_contracts
  errorValue_le := by
    intro i hi
    exact MatrixPartition.errorValueAtMost_mono hde (S.errorValue_le i hi)

end MatrixContractionTail

/-- From any partition of a matrix with no rows, repeatedly contract column
parts until the partition is coarsest.  All intermediate error values are zero. -/
theorem exists_matrixContractionTail_zeroRows {m d : ℕ}
    (M : _root_.Matrix (Fin 0) (Fin m) α) :
    ∀ P : MatrixPartition 0 m, Nonempty (MatrixContractionTail M d P) := by
  classical
  intro P
  refine WellFounded.induction
    (C := fun P : MatrixPartition 0 m => Nonempty (MatrixContractionTail M d P))
    (InvImage.wf (fun P : MatrixPartition 0 m => P.colParts.card) <| (Nat.lt_wfRel).2)
    P ?_
  intro P ih
  by_cases hcol : P.colParts.card ≤ 1
  · have hrow : P.rowParts.card ≤ 1 := by
      rw [MatrixPartition.rowParts_eq_empty_of_zero_rows P]
      simp
    exact ⟨{
      stepCount := 0
      partition := fun _ => P
      starts := rfl
      ends := ⟨hrow, hcol⟩
      step_contracts := by intro i hi; omega
      errorValue_le := by
        intro i hi
        exact MatrixPartition.errorValueAtMost_zeroRows M P
    }⟩
  · have hgt : 1 < P.colParts.card := Nat.lt_of_not_ge hcol
    rcases Finset.one_lt_card.mp hgt with ⟨C, hC, D, hD, hCD⟩
    let Q : MatrixPartition 0 m := P.colContract hC hD hCD
    have hlt : Q.colParts.card < P.colParts.card :=
      MatrixPartition.colParts_card_colContract_lt P hC hD hCD
    rcases ih Q hlt with ⟨S⟩
    exact ⟨MatrixContractionTail.cons
      (Or.inr (MatrixPartition.isColContraction_colContract P hC hD hCD))
      (MatrixPartition.errorValueAtMost_zeroRows M P) S⟩

/-- From any partition of a matrix with no columns, repeatedly contract row
parts until the partition is coarsest.  All intermediate error values are zero. -/
theorem exists_matrixContractionTail_zeroCols {n d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin 0) α) :
    ∀ P : MatrixPartition n 0, Nonempty (MatrixContractionTail M d P) := by
  classical
  intro P
  refine WellFounded.induction
    (C := fun P : MatrixPartition n 0 => Nonempty (MatrixContractionTail M d P))
    (InvImage.wf (fun P : MatrixPartition n 0 => P.rowParts.card) <| (Nat.lt_wfRel).2)
    P ?_
  intro P ih
  by_cases hrow : P.rowParts.card ≤ 1
  · have hcol : P.colParts.card ≤ 1 := by
      rw [MatrixPartition.colParts_eq_empty_of_zero_cols P]
      simp
    exact ⟨{
      stepCount := 0
      partition := fun _ => P
      starts := rfl
      ends := ⟨hrow, hcol⟩
      step_contracts := by intro i hi; omega
      errorValue_le := by
        intro i hi
        exact MatrixPartition.errorValueAtMost_zeroCols M P
    }⟩
  · have hgt : 1 < P.rowParts.card := Nat.lt_of_not_ge hrow
    rcases Finset.one_lt_card.mp hgt with ⟨R, hR, S, hS, hRS⟩
    let Q : MatrixPartition n 0 := P.rowContract hR hS hRS
    have hlt : Q.rowParts.card < P.rowParts.card :=
      MatrixPartition.rowParts_card_rowContract_lt P hR hS hRS
    rcases ih Q hlt with ⟨T⟩
    exact ⟨MatrixContractionTail.cons
      (Or.inl (MatrixPartition.isRowContraction_rowContract P hR hS hRS))
      (MatrixPartition.errorValueAtMost_zeroCols M P) T⟩

/-- Matrices with no rows have matrix twin-width at most every bound. -/
theorem matrixTwinWidthAtMost_zeroRows {m d : ℕ}
    (M : _root_.Matrix (Fin 0) (Fin m) α) :
    MatrixTwinWidthAtMost M d := by
  rcases exists_matrixContractionTail_zeroRows (d := d) M
      (MatrixPartition.singleton 0 m) with ⟨S⟩
  exact ⟨{
    stepCount := S.stepCount
    partition := S.partition
    starts := by
      rw [S.starts]
      exact MatrixPartition.singleton_isFinest 0 m
    ends := S.ends
    step_contracts := S.step_contracts
    errorValue_le := S.errorValue_le
  }⟩

/-- Matrices with no columns have matrix twin-width at most every bound. -/
theorem matrixTwinWidthAtMost_zeroCols {n d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin 0) α) :
    MatrixTwinWidthAtMost M d := by
  rcases exists_matrixContractionTail_zeroCols (d := d) M
      (MatrixPartition.singleton n 0) with ⟨S⟩
  exact ⟨{
    stepCount := S.stepCount
    partition := S.partition
    starts := by
      rw [S.starts]
      exact MatrixPartition.singleton_isFinest n 0
    ends := S.ends
    step_contracts := S.step_contracts
    errorValue_le := S.errorValue_le
  }⟩

namespace MatrixPartition

/-- Matrix partitions are equal when their row and column part families are
equal.  The remaining fields are propositions. -/
theorem ext_parts {n m : ℕ} {P Q : MatrixPartition n m}
    (hrow : P.rowParts = Q.rowParts) (hcol : P.colParts = Q.colParts) :
    P = Q := by
  cases P
  cases Q
  simp at hrow hcol
  subst hrow
  subst hcol
  rfl

/-- If a row partition properly refines another row partition, two fine row
parts lie in one coarse row part. -/
theorem exists_two_rowParts_subset_of_refines_ne {n m : ℕ}
    {P Q : MatrixPartition n m}
    (href : PartsRefine P.rowParts Q.rowParts)
    (hne : P.rowParts ≠ Q.rowParts) :
    ∃ B ∈ Q.rowParts, ∃ R ∈ P.rowParts, ∃ S ∈ P.rowParts,
      R ≠ S ∧ R ⊆ B ∧ S ⊆ B := by
  classical
  by_contra hno
  have huniq :
      ∀ ⦃B R S⦄, B ∈ Q.rowParts → R ∈ P.rowParts → S ∈ P.rowParts →
        R ⊆ B → S ⊆ B → R = S := by
    intro B R S hB hR hS hRB hSB
    by_contra hRS
    exact hno ⟨B, hB, R, hR, S, hS, hRS, hRB, hSB⟩
  have hcoarse_subset :
      ∀ ⦃A B⦄, A ∈ P.rowParts → B ∈ Q.rowParts → A ⊆ B → B ⊆ A := by
    intro A B hA hB hAB x hxB
    rcases P.row_cover x with ⟨A', hA', hxA'⟩
    rcases href hA' with ⟨B', hB', hA'B'⟩
    have hxB' : x ∈ B' := hA'B' hxA'
    have hB'eq : B' = B := by
      by_contra hneB
      exact Finset.disjoint_left.mp (Q.row_disjoint hB' hB hneB) hxB' hxB
    have hA'eq : A' = A :=
      huniq hB hA' hA (by simpa [hB'eq] using hA'B') hAB
    simpa [hA'eq] using hxA'
  have hPsubsetQ : P.rowParts ⊆ Q.rowParts := by
    intro A hA
    rcases href hA with ⟨B, hB, hAB⟩
    have hBA : B ⊆ A := hcoarse_subset hA hB hAB
    have hAeqB : A = B := Finset.Subset.antisymm hAB hBA
    simpa [hAeqB] using hB
  have hQsubsetP : Q.rowParts ⊆ P.rowParts := by
    intro B hB
    rcases Q.row_nonempty hB with ⟨x, hxB⟩
    rcases P.row_cover x with ⟨A, hA, hxA⟩
    rcases href hA with ⟨B', hB', hAB'⟩
    have hxB' : x ∈ B' := hAB' hxA
    have hB'eq : B' = B := by
      by_contra hneB
      exact Finset.disjoint_left.mp (Q.row_disjoint hB' hB hneB) hxB' hxB
    have hAB : A ⊆ B := by simpa [hB'eq] using hAB'
    have hBA : B ⊆ A := hcoarse_subset hA hB hAB
    have hBeqA : B = A := Finset.Subset.antisymm hBA hAB
    simpa [hBeqA] using hA
  exact hne (Finset.Subset.antisymm hPsubsetQ hQsubsetP)

/-- Column-side analogue of
`exists_two_rowParts_subset_of_refines_ne`. -/
theorem exists_two_colParts_subset_of_refines_ne {n m : ℕ}
    {P Q : MatrixPartition n m}
    (href : PartsRefine P.colParts Q.colParts)
    (hne : P.colParts ≠ Q.colParts) :
    ∃ B ∈ Q.colParts, ∃ C ∈ P.colParts, ∃ D ∈ P.colParts,
      C ≠ D ∧ C ⊆ B ∧ D ⊆ B := by
  classical
  by_contra hno
  have huniq :
      ∀ ⦃B C D⦄, B ∈ Q.colParts → C ∈ P.colParts → D ∈ P.colParts →
        C ⊆ B → D ⊆ B → C = D := by
    intro B C D hB hC hD hCB hDB
    by_contra hCD
    exact hno ⟨B, hB, C, hC, D, hD, hCD, hCB, hDB⟩
  have hcoarse_subset :
      ∀ ⦃A B⦄, A ∈ P.colParts → B ∈ Q.colParts → A ⊆ B → B ⊆ A := by
    intro A B hA hB hAB x hxB
    rcases P.col_cover x with ⟨A', hA', hxA'⟩
    rcases href hA' with ⟨B', hB', hA'B'⟩
    have hxB' : x ∈ B' := hA'B' hxA'
    have hB'eq : B' = B := by
      by_contra hneB
      exact Finset.disjoint_left.mp (Q.col_disjoint hB' hB hneB) hxB' hxB
    have hA'eq : A' = A :=
      huniq hB hA' hA (by simpa [hB'eq] using hA'B') hAB
    simpa [hA'eq] using hxA'
  have hPsubsetQ : P.colParts ⊆ Q.colParts := by
    intro A hA
    rcases href hA with ⟨B, hB, hAB⟩
    have hBA : B ⊆ A := hcoarse_subset hA hB hAB
    have hAeqB : A = B := Finset.Subset.antisymm hAB hBA
    simpa [hAeqB] using hB
  have hQsubsetP : Q.colParts ⊆ P.colParts := by
    intro B hB
    rcases Q.col_nonempty hB with ⟨x, hxB⟩
    rcases P.col_cover x with ⟨A, hA, hxA⟩
    rcases href hA with ⟨B', hB', hAB'⟩
    have hxB' : x ∈ B' := hAB' hxA
    have hB'eq : B' = B := by
      by_contra hneB
      exact Finset.disjoint_left.mp (Q.col_disjoint hB' hB hneB) hxB' hxB
    have hAB : A ⊆ B := by simpa [hB'eq] using hAB'
    have hBA : B ⊆ A := hcoarse_subset hA hB hAB
    have hBeqA : B = A := Finset.Subset.antisymm hBA hAB
    simpa [hBeqA] using hA
  exact hne (Finset.Subset.antisymm hPsubsetQ hQsubsetP)

/-- Merging two parts that lie in one coarse part preserves bounded
refinement of a finite family of parts. -/
theorem partsRRefine_contract {α : Type*} [DecidableEq α]
    {P Q : Finset (Finset α)} {R S : Finset α} {r : ℕ}
    (hPQ : PartsRRefine P Q r)
    (hR : R ∈ P) (_hS : S ∈ P) (_hRS : R ≠ S)
    (hsame : ∃ B ∈ Q, R ⊆ B ∧ S ⊆ B) :
    PartsRRefine (insert (R ∪ S) ((P.erase R).erase S)) Q r := by
  classical
  constructor
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hAold
    · rcases hsame with ⟨B, hB, hRB, hSB⟩
      exact ⟨B, hB, by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hRB hx
        · exact hSB hx⟩
    · have hAP : A ∈ P :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2
      exact hPQ.1 hAP
  · intro B hB
    let Pnew : Finset (Finset α) := insert (R ∪ S) ((P.erase R).erase S)
    let f : Finset α → Finset α := fun A => if A = R ∪ S then R else A
    have hmap :
        ∀ A ∈ Pnew.filter fun A => A ⊆ B, f A ∈ P.filter fun A => A ⊆ B := by
      intro A hA
      have hAdata : A ∈ Pnew ∧ A ⊆ B := by
        simpa [Pnew] using hA
      by_cases hAunion : A = R ∪ S
      · subst A
        have hRsub : R ⊆ B := by
          intro x hx
          exact hAdata.2 (Finset.mem_union_left S hx)
        simp [f, hR, hRsub]
      · have hAold : A ∈ (P.erase R).erase S := by
          rcases Finset.mem_insert.mp hAdata.1 with h | h
          · exact False.elim (hAunion h)
          · exact h
        have hAP : A ∈ P :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).2
        simp [f, hAunion, hAP, hAdata.2]
    have hinj :
        Set.InjOn f (Pnew.filter fun A => A ⊆ B) := by
      intro A hA C hC hAC
      have hAdata : A ∈ Pnew ∧ A ⊆ B := by
        simpa [Pnew] using hA
      have hCdata : C ∈ Pnew ∧ C ⊆ B := by
        simpa [Pnew] using hC
      by_cases hAunion : A = R ∪ S
      · by_cases hCunion : C = R ∪ S
        · exact hAunion.trans hCunion.symm
        · have hCold : C ∈ (P.erase R).erase S := by
            rcases Finset.mem_insert.mp hCdata.1 with h | h
            · exact False.elim (hCunion h)
            · exact h
          have hCneR : C ≠ R :=
            (Finset.mem_erase.mp (Finset.mem_erase.mp hCold).2).1
          have hCR : C = R := by
            simpa [f, hAunion, hCunion] using hAC.symm
          exact False.elim (hCneR hCR)
      · by_cases hCunion : C = R ∪ S
        · have hAold : A ∈ (P.erase R).erase S := by
            rcases Finset.mem_insert.mp hAdata.1 with h | h
            · exact False.elim (hAunion h)
            · exact h
          have hAneR : A ≠ R :=
            (Finset.mem_erase.mp (Finset.mem_erase.mp hAold).2).1
          have hAR : A = R := by
            simpa [f, hAunion, hCunion] using hAC
          exact False.elim (hAneR hAR)
        · simpa [f, hAunion, hCunion] using hAC
    exact le_trans
      (Finset.card_le_card_of_injOn f hmap hinj)
      (hPQ.2 hB)

/-- Row contractions inside one coarse row part preserve bounded refinement. -/
theorem rrefines_rowContract {n m r : ℕ}
    {P Q : MatrixPartition n m}
    {R S : Finset (Fin n)}
    (hPQ : RRefines P Q r)
    (hR : R ∈ P.rowParts) (hS : S ∈ P.rowParts) (hRS : R ≠ S)
    (hsame : ∃ B ∈ Q.rowParts, R ⊆ B ∧ S ⊆ B) :
    RRefines (P.rowContract hR hS hRS) Q r := by
  constructor
  · simpa [rowParts_rowContract] using
      partsRRefine_contract hPQ.1 hR hS hRS hsame
  · simpa [colParts_rowContract] using hPQ.2

/-- Column contractions inside one coarse column part preserve bounded
refinement. -/
theorem rrefines_colContract {n m r : ℕ}
    {P Q : MatrixPartition n m}
    {C D : Finset (Fin m)}
    (hPQ : RRefines P Q r)
    (hC : C ∈ P.colParts) (hD : D ∈ P.colParts) (hCD : C ≠ D)
    (hsame : ∃ B ∈ Q.colParts, C ⊆ B ∧ D ⊆ B) :
    RRefines (P.colContract hC hD hCD) Q r := by
  constructor
  · simpa [rowParts_colContract] using hPQ.1
  · simpa [colParts_colContract] using
      partsRRefine_contract hPQ.2 hC hD hCD hsame

/-- Error values pull back across bounded refinements, with the expected
multiplicative loss. -/
theorem errorValueAtMost_of_rrefines {n m r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P Q : MatrixPartition n m}
    (hPQ : MatrixPartition.RRefines P Q r)
    (hQ : ErrorValueAtMost M Q t) :
    ErrorValueAtMost M P (r * t) := by
  classical
  constructor
  · intro R hR
    rcases hPQ.1.1 hR with ⟨RQ, hRQ, hRsub⟩
    let badQ : Finset (Finset (Fin m)) := rowErrorSet M Q RQ
    let overBad : Finset (Finset (Fin m)) :=
      badQ.biUnion fun CQ => P.colParts.filter fun C => C ⊆ CQ
    have hsubset :
        rowErrorSet M P R ⊆ overBad := by
      intro C hC
      have hCdata : C ∈ P.colParts ∧ ¬ ZoneConstant M R C := by
        simpa [rowErrorSet] using hC
      have hCparts : C ∈ P.colParts := by
        exact hCdata.1
      have hCnon : ¬ ZoneConstant M R C := by
        exact hCdata.2
      rcases hPQ.2.1 hCparts with ⟨CQ, hCQ, hCsub⟩
      have hCQbad : CQ ∈ badQ := by
        simp [badQ, rowErrorSet, hCQ]
        intro hconst
        exact hCnon (by
          intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
          exact hconst (hRsub hr₁) (hRsub hr₂) (hCsub hc₁) (hCsub hc₂))
      exact Finset.mem_biUnion.mpr ⟨CQ, hCQbad, by simp [hCparts, hCsub]⟩
    have hcard_over :
        overBad.card ≤ badQ.card * r := by
      unfold overBad
      exact Finset.card_biUnion_le_card_mul _ _ _ (by
        intro CQ hCQ
        have hCQdata : CQ ∈ Q.colParts ∧ ¬ ZoneConstant M RQ CQ := by
          simpa [badQ, rowErrorSet] using hCQ
        have hCQparts : CQ ∈ Q.colParts := by
          exact hCQdata.1
        exact hPQ.2.2 hCQparts)
    calc
      (rowErrorSet M P R).card ≤ overBad.card := Finset.card_le_card hsubset
      _ ≤ badQ.card * r := hcard_over
      _ ≤ t * r := Nat.mul_le_mul_right r (hQ.1 hRQ)
      _ = r * t := Nat.mul_comm t r
  · intro C hC
    rcases hPQ.2.1 hC with ⟨CQ, hCQ, hCsub⟩
    let badQ : Finset (Finset (Fin n)) := colErrorSet M Q CQ
    let overBad : Finset (Finset (Fin n)) :=
      badQ.biUnion fun RQ => P.rowParts.filter fun R => R ⊆ RQ
    have hsubset :
        colErrorSet M P C ⊆ overBad := by
      intro R hR
      have hRdata : R ∈ P.rowParts ∧ ¬ ZoneConstant M R C := by
        simpa [colErrorSet] using hR
      have hRparts : R ∈ P.rowParts := by
        exact hRdata.1
      have hRnon : ¬ ZoneConstant M R C := by
        exact hRdata.2
      rcases hPQ.1.1 hRparts with ⟨RQ, hRQ, hRsub⟩
      have hRQbad : RQ ∈ badQ := by
        simp [badQ, colErrorSet, hRQ]
        intro hconst
        exact hRnon (by
          intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
          exact hconst (hRsub hr₁) (hRsub hr₂) (hCsub hc₁) (hCsub hc₂))
      exact Finset.mem_biUnion.mpr ⟨RQ, hRQbad, by simp [hRparts, hRsub]⟩
    have hcard_over :
        overBad.card ≤ badQ.card * r := by
      unfold overBad
      exact Finset.card_biUnion_le_card_mul _ _ _ (by
        intro RQ hRQ
        have hRQdata : RQ ∈ Q.rowParts ∧ ¬ ZoneConstant M RQ CQ := by
          simpa [badQ, colErrorSet] using hRQ
        have hRQparts : RQ ∈ Q.rowParts := by
          exact hRQdata.1
        exact hPQ.1.2 hRQparts)
    calc
      (colErrorSet M P C).card ≤ overBad.card := Finset.card_le_card hsubset
      _ ≤ badQ.card * r := hcard_over
      _ ≤ t * r := Nat.mul_le_mul_right r (hQ.2 hCQ)
      _ = r * t := Nat.mul_comm t r

end MatrixPartition

namespace MatrixContractionPath

/-- The empty contraction path at a partition whose error is already bounded. -/
def nil {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P : MatrixPartition n m}
    (hP : ErrorValueAtMost M P d) :
    MatrixContractionPath M d P P where
  stepCount := 0
  partition := fun _ => P
  starts := rfl
  ends := rfl
  step_contracts := by intro i hi; omega
  errorValue_le := by intro i hi; simpa using hP

/-- Prepend one contraction to a contraction path. -/
noncomputable def cons {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {P Q R : MatrixPartition n m}
    (hPQ : MatrixPartition.IsContraction P Q)
    (hP : ErrorValueAtMost M P d)
    (S : MatrixContractionPath M d Q R) :
    MatrixContractionPath M d P R where
  stepCount := S.stepCount + 1
  partition := fun i =>
    match i with
    | 0 => P
    | j + 1 => S.partition j
  starts := rfl
  ends := by
    simpa using S.ends
  step_contracts := by
    intro i hi
    cases i with
    | zero =>
        simpa [S.starts] using hPQ
    | succ j =>
        have hj : j < S.stepCount := by omega
        simpa using S.step_contracts j hj
  errorValue_le := by
    intro i hi
    cases i with
    | zero =>
        simpa using hP
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.errorValue_le j hj

end MatrixContractionPath

namespace MatrixContractionTail

/-- Expand one bounded-refinement step into ordinary contractions before an
already constructed contraction tail from the coarse partition.

The proof repeatedly merges two fine row or column parts lying in the same
coarse part.  Bounded refinement is preserved at every merge, so the pulled
back error bound remains `r * t`. -/
theorem exists_of_rrefines {n m r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α} :
    ∀ (P Q : MatrixPartition n m),
      MatrixPartition.RRefines P Q r →
      ErrorValueAtMost M Q t →
      MatrixContractionTail M (r * t) Q →
      Nonempty (MatrixContractionTail M (r * t) P) := by
  classical
  intro P
  refine WellFounded.induction
    (C := fun P : MatrixPartition n m =>
      ∀ Q : MatrixPartition n m,
        MatrixPartition.RRefines P Q r →
        ErrorValueAtMost M Q t →
        MatrixContractionTail M (r * t) Q →
        Nonempty (MatrixContractionTail M (r * t) P))
    (InvImage.wf
      (fun P : MatrixPartition n m => P.rowParts.card + P.colParts.card)
      <| (Nat.lt_wfRel).2)
    P ?_
  intro P ih Q hPQ hQ T
  have hPerr : ErrorValueAtMost M P (r * t) :=
    MatrixPartition.errorValueAtMost_of_rrefines hPQ hQ
  by_cases hrow : P.rowParts = Q.rowParts
  · by_cases hcol : P.colParts = Q.colParts
    · have hPQeq : P = Q := MatrixPartition.ext_parts hrow hcol
      subst Q
      exact ⟨T⟩
    · rcases MatrixPartition.exists_two_colParts_subset_of_refines_ne
        hPQ.2.1 hcol with
        ⟨B, hB, C, hC, D, hD, hCD, hCB, hDB⟩
      let P' : MatrixPartition n m := P.colContract hC hD hCD
      have hP'Q : MatrixPartition.RRefines P' Q r :=
        MatrixPartition.rrefines_colContract hPQ hC hD hCD ⟨B, hB, hCB, hDB⟩
      have hlt :
          P'.rowParts.card + P'.colParts.card <
            P.rowParts.card + P.colParts.card := by
        have hcollt := MatrixPartition.colParts_card_colContract_lt P hC hD hCD
        have hroweq : P'.rowParts.card = P.rowParts.card := by
          simp [P']
        have hcoleq : P'.colParts.card = (P.colContract hC hD hCD).colParts.card := rfl
        rw [hroweq, hcoleq]
        omega
      rcases ih P' hlt Q hP'Q hQ T with ⟨T'⟩
      exact ⟨MatrixContractionTail.cons
        (Or.inr (MatrixPartition.isColContraction_colContract P hC hD hCD))
        hPerr T'⟩
  · rcases MatrixPartition.exists_two_rowParts_subset_of_refines_ne
      hPQ.1.1 hrow with
      ⟨B, hB, R, hR, S, hS, hRS, hRB, hSB⟩
    let P' : MatrixPartition n m := P.rowContract hR hS hRS
    have hP'Q : MatrixPartition.RRefines P' Q r :=
      MatrixPartition.rrefines_rowContract hPQ hR hS hRS ⟨B, hB, hRB, hSB⟩
    have hlt :
        P'.rowParts.card + P'.colParts.card <
          P.rowParts.card + P.colParts.card := by
      have hrowlt := MatrixPartition.rowParts_card_rowContract_lt P hR hS hRS
      have hroweq : P'.rowParts.card = (P.rowContract hR hS hRS).rowParts.card := rfl
      have hcoleq : P'.colParts.card = P.colParts.card := by
        simp [P']
      rw [hroweq, hcoleq]
      omega
    rcases ih P' hlt Q hP'Q hQ T with ⟨T'⟩
    exact ⟨MatrixContractionTail.cons
      (Or.inl (MatrixPartition.isRowContraction_rowContract P hR hS hRS))
      hPerr T'⟩

end MatrixContractionTail

/-- Starting from any index in a bounded-refinement partition sequence, the
remaining suffix expands to an ordinary contraction tail of error at most
`r * t`. -/
theorem exists_matrixContractionTail_of_boundedErrorRefinementPartitionSequence
    {n m r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hr : 0 < r)
    (S : BoundedErrorRefinementPartitionSequence M r t) :
    ∀ i, i ≤ S.stepCount →
      Nonempty (MatrixContractionTail M (r * t) (S.partition i)) := by
  classical
  intro i hi
  have ht_le : t ≤ r * t := by
    cases r with
    | zero => omega
    | succ r =>
        rw [Nat.succ_mul]
        exact Nat.le_add_left t (r * t)
  refine WellFounded.induction
    (C := fun a : {i // i ≤ S.stepCount} =>
      Nonempty (MatrixContractionTail M (r * t) (S.partition a.1)))
    (InvImage.wf
      (fun a : {i // i ≤ S.stepCount} => S.stepCount - a.1)
      <| (Nat.lt_wfRel).2)
    ⟨i, hi⟩ ?_
  intro a ih
  by_cases hlast : a.1 = S.stepCount
  · refine ⟨{
      stepCount := 0
      partition := fun _ => S.partition a.1
      starts := rfl
      ends := by simpa [hlast] using S.ends
      step_contracts := by intro j hj; omega
      errorValue_le := by
        intro j hj
        exact MatrixPartition.errorValueAtMost_mono ht_le
          (by simpa [hlast] using S.errorValue_le S.stepCount le_rfl)
    }⟩
  · have hlt : a.1 < S.stepCount := lt_of_le_of_ne a.2 hlast
    let b : {i // i ≤ S.stepCount} := ⟨a.1 + 1, by omega⟩
    have hdec : S.stepCount - b.1 < S.stepCount - a.1 := by
      dsimp [b]
      omega
    rcases ih b hdec with ⟨Tnext⟩
    have hstep : MatrixPartition.RRefines
        (S.partition a.1) (S.partition (a.1 + 1)) r :=
      S.step_rrefines a.1 hlt
    have hnext : ErrorValueAtMost M (S.partition (a.1 + 1)) t :=
      S.errorValue_le (a.1 + 1) (by omega)
    exact MatrixContractionTail.exists_of_rrefines
      (S.partition a.1) (S.partition (a.1 + 1)) hstep hnext Tnext

/-- Lemma 8 in matrix-partition form: a bounded-refinement partition sequence
expands to a matrix contraction sequence, with the multiplicative error
bound `r * t`. -/
theorem matrixTwinWidthAtMost_of_boundedErrorRefinementPartitionSequence
    {n m r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hr : 0 < r)
    (S : Nonempty (BoundedErrorRefinementPartitionSequence M r t)) :
    MatrixTwinWidthAtMost M (r * t) := by
  rcases S with ⟨S⟩
  rcases exists_matrixContractionTail_of_boundedErrorRefinementPartitionSequence
      hr S 0 (Nat.zero_le S.stepCount) with ⟨T⟩
  exact ⟨{
    stepCount := T.stepCount
    partition := T.partition
    starts := by
      rw [T.starts]
      exact S.starts
    ends := T.ends
    step_contracts := T.step_contracts
    errorValue_le := T.errorValue_le
  }⟩

/-- Lemma 8 with the numerical parameters used by Theorem 10 for alphabet size
`a`. -/
theorem matrixTwinWidthAtMost_of_theorem10ErrorRefinementSequence
    {n m a d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (ha : 0 < a)
    (S : Nonempty (BoundedErrorRefinementPartitionSequence M
      (2 * a ^ (d + 1)) (d * a ^ (d + 1)))) :
    MatrixTwinWidthAtMost M (theorem10AlphabetErrorRefinementBound a d) := by
  have hr : 0 < 2 * a ^ (d + 1) := by
    exact Nat.mul_pos (by decide : 0 < 2) (pow_pos ha _)
  have h := matrixTwinWidthAtMost_of_boundedErrorRefinementPartitionSequence
    (M := M) (r := 2 * a ^ (d + 1)) (t := d * a ^ (d + 1)) hr S
  have hmul :
      (2 * a ^ (d + 1)) * (d * a ^ (d + 1)) =
        theorem10AlphabetErrorRefinementBound a d := by
    unfold theorem10AlphabetErrorRefinementBound
    have hp : a ^ (d + 1) * a ^ (d + 1) = a ^ (2 * (d + 1)) := by
      rw [← pow_add]
      have hexp : d + 1 + (d + 1) = 2 * (d + 1) := by omega
      simp [hexp]
    calc
      (2 * a ^ (d + 1)) * (d * a ^ (d + 1))
          = 2 * d * (a ^ (d + 1) * a ^ (d + 1)) := by ring
      _ = 2 * d * a ^ (2 * (d + 1)) := by rw [hp]
  simpa [hmul] using h

namespace MatrixDivision

/-- The unordered matrix partition underlying a consecutive matrix division. -/
noncomputable def toPartition {n m : ℕ} (D : MatrixDivision n m) :
    MatrixPartition n m where
  rowParts :=
    (Finset.univ : Finset (Fin (D.rowCuts + 1))).map
      ⟨D.rowDiv.part, D.rowDiv.part_injective⟩
  row_nonempty := by
    intro R hR
    rcases Finset.mem_map.mp hR with ⟨i, _hi, rfl⟩
    exact D.rowDiv.part_nonempty i
  row_disjoint := by
    intro R S hR hS hRS
    rcases Finset.mem_map.mp hR with ⟨i, _hi, rfl⟩
    rcases Finset.mem_map.mp hS with ⟨j, _hj, rfl⟩
    exact D.rowDiv.part_disjoint (by
      intro hij
      subst j
      exact hRS rfl)
  row_cover := by
    intro r
    rcases D.rowDiv.part_cover r with ⟨i, hi⟩
    exact ⟨D.rowDiv.part i, by simp, hi⟩
  colParts :=
    (Finset.univ : Finset (Fin (D.colCuts + 1))).map
      ⟨D.colDiv.part, D.colDiv.part_injective⟩
  col_nonempty := by
    intro C hC
    rcases Finset.mem_map.mp hC with ⟨j, _hj, rfl⟩
    exact D.colDiv.part_nonempty j
  col_disjoint := by
    intro C E hC hE hCE
    rcases Finset.mem_map.mp hC with ⟨i, _hi, rfl⟩
    rcases Finset.mem_map.mp hE with ⟨j, _hj, rfl⟩
    exact D.colDiv.part_disjoint (by
      intro hij
      subst j
      exact hCE rfl)
  col_cover := by
    intro c
    rcases D.colDiv.part_cover c with ⟨j, hj⟩
    exact ⟨D.colDiv.part j, by simp, hj⟩

@[simp] theorem rowParts_toPartition {n m : ℕ} (D : MatrixDivision n m) :
    (D.toPartition).rowParts =
      (Finset.univ : Finset (Fin (D.rowCuts + 1))).map
        ⟨D.rowDiv.part, D.rowDiv.part_injective⟩ :=
  rfl

@[simp] theorem colParts_toPartition {n m : ℕ} (D : MatrixDivision n m) :
    (D.toPartition).colParts =
      (Finset.univ : Finset (Fin (D.colCuts + 1))).map
        ⟨D.colDiv.part, D.colDiv.part_injective⟩ :=
  rfl

/-- Alphabet profiles used in the Section 5.8 refinement.  A row or column
part of mixed value at most `d` has at most `d + 1` non-mixed intervals, so an
alphabet value on `Fin (d + 1)` is enough to encode its profile. -/
abbrev AlphabetProfile (α : Type u) (d : ℕ) : Type u :=
  Fin (d + 1) → α

@[simp] theorem fintype_card_alphabetProfile [Fintype α] (d : ℕ) :
    Fintype.card (AlphabetProfile α d) = Fintype.card α ^ (d + 1) := by
  simp [AlphabetProfile]

/-- Linear position of a column mixed-value item: zones have even positions
and cuts have odd positions. -/
def colMixedItemPos {k : ℕ} : Sum (Fin (k + 1)) (Fin k) → ℕ
  | Sum.inl j => 2 * j.1
  | Sum.inr j => 2 * j.1 + 1

/-- Linear position of a row mixed-value item: zones have even positions and
cuts have odd positions. -/
def rowMixedItemPos {k : ℕ} : Sum (Fin (k + 1)) (Fin k) → ℕ
  | Sum.inl i => 2 * i.1
  | Sum.inr i => 2 * i.1 + 1

/-- Number of mixed zones/cuts strictly before a column zone. -/
noncomputable def colBadBefore {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (j : Fin (D.colCuts + 1)) : ℕ :=
  ((colMixedItems M (D.rowDiv.part i) D.colDiv).filter
    fun item => colMixedItemPos item < 2 * j.1).card

/-- Number of mixed zones/cuts strictly before a row zone. -/
noncomputable def rowBadBefore {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (i : Fin (D.rowCuts + 1)) : ℕ :=
  ((rowMixedItems M D.rowDiv (D.colDiv.part j)).filter
    fun item => rowMixedItemPos item < 2 * i.1).card

theorem colBadBefore_le_colMixedValue {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (j : Fin (D.colCuts + 1)) :
    colBadBefore M D i j ≤ colMixedValue M (D.rowDiv.part i) D.colDiv := by
  unfold colBadBefore
  calc
    ((colMixedItems M (D.rowDiv.part i) D.colDiv).filter
        fun item => colMixedItemPos item < 2 * j.1).card
        ≤ (colMixedItems M (D.rowDiv.part i) D.colDiv).card :=
          Finset.card_filter_le _ _
    _ = colMixedValue M (D.rowDiv.part i) D.colDiv :=
          colMixedItems_card M (D.rowDiv.part i) D.colDiv

theorem rowBadBefore_le_rowMixedValue {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (i : Fin (D.rowCuts + 1)) :
    rowBadBefore M D j i ≤ rowMixedValue M D.rowDiv (D.colDiv.part j) := by
  unfold rowBadBefore
  calc
    ((rowMixedItems M D.rowDiv (D.colDiv.part j)).filter
        fun item => rowMixedItemPos item < 2 * i.1).card
        ≤ (rowMixedItems M D.rowDiv (D.colDiv.part j)).card :=
          Finset.card_filter_le _ _
    _ = rowMixedValue M D.rowDiv (D.colDiv.part j) :=
          rowMixedItems_card M D.rowDiv (D.colDiv.part j)

theorem colBadBefore_lt_succ_of_mixedValueAtMost {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1)) :
    colBadBefore M D i j < d + 1 := by
  exact Nat.lt_succ_of_le
    (le_trans (colBadBefore_le_colMixedValue M D i j) (hD.2 i))

theorem rowBadBefore_lt_succ_of_mixedValueAtMost {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (j : Fin (D.colCuts + 1)) (i : Fin (D.rowCuts + 1)) :
    rowBadBefore M D j i < d + 1 := by
  exact Nat.lt_succ_of_le
    (le_trans (rowBadBefore_le_rowMixedValue M D j i) (hD.1 j))

/-- Candidate representative column zones for a row-profile coordinate. -/
noncomputable def rowProfileCandidates {n m d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (q : Fin (d + 1)) : Finset (Fin (D.colCuts + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j =>
      ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) ∧
        colBadBefore M D i j = q.1

/-- Candidate representative row zones for a column-profile coordinate. -/
noncomputable def colProfileCandidates {n m d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (q : Fin (d + 1)) : Finset (Fin (D.rowCuts + 1)) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) ∧
        rowBadBefore M D j i = q.1

theorem mem_rowProfileCandidates {n m d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (q : Fin (d + 1)) (j : Fin (D.colCuts + 1)) :
    j ∈ rowProfileCandidates (d := d) M D i q ↔
      ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) ∧
        colBadBefore M D i j = q.1 := by
  classical
  simp [rowProfileCandidates]

theorem mem_colProfileCandidates {n m d : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (q : Fin (d + 1)) (i : Fin (D.rowCuts + 1)) :
    i ∈ colProfileCandidates (d := d) M D j q ↔
      ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) ∧
        rowBadBefore M D j i = q.1 := by
  classical
  simp [colProfileCandidates]

theorem rowProfileCandidates_nonempty_of_not_zoneMixed {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j)) :
    (rowProfileCandidates (d := d) M D i
      ⟨colBadBefore M D i j,
        colBadBefore_lt_succ_of_mixedValueAtMost hD i j⟩).Nonempty := by
  refine ⟨j, ?_⟩
  rw [mem_rowProfileCandidates]
  exact ⟨hnot, rfl⟩

theorem colProfileCandidates_nonempty_of_not_zoneMixed {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j)) :
    (colProfileCandidates (d := d) M D j
      ⟨rowBadBefore M D j i,
        rowBadBefore_lt_succ_of_mixedValueAtMost hD j i⟩).Nonempty := by
  refine ⟨i, ?_⟩
  rw [mem_colProfileCandidates]
  exact ⟨hnot, rfl⟩

theorem no_colMixedItem_between_profile_min_and_zone {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j)) :
    let q : Fin (d + 1) :=
      ⟨colBadBefore M D i j,
        colBadBefore_lt_succ_of_mixedValueAtMost hD i j⟩
    let candidates := rowProfileCandidates (d := d) M D i q
    let rep := candidates.min'
      (rowProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot)
    ∀ item ∈ colMixedItems M (D.rowDiv.part i) D.colDiv,
      colMixedItemPos item < 2 * j.1 →
        colMixedItemPos item < 2 * rep.1 := by
  classical
  intro q candidates rep item hitem hbefore
  have hjmem : j ∈ candidates := by
    rw [mem_rowProfileCandidates]
    exact ⟨hnot, rfl⟩
  have hrep_mem : rep ∈ candidates := by
    exact Finset.min'_mem candidates
      (rowProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot)
  have hrep_le_j : rep ≤ j :=
    Finset.min'_le candidates j hjmem
  by_contra hnot_before_rep
  have hlt :
      (((colMixedItems M (D.rowDiv.part i) D.colDiv).filter
          fun item => colMixedItemPos item < 2 * rep.1).card) <
        (((colMixedItems M (D.rowDiv.part i) D.colDiv).filter
          fun item => colMixedItemPos item < 2 * j.1).card) := by
    refine MatrixPartition.card_filter_lt_card_filter_of_exists ?_ ?_
    · intro x hx
      have hrepj : rep.1 ≤ j.1 := Fin.le_iff_val_le_val.mp hrep_le_j
      omega
    · exact ⟨item, hitem, hbefore, hnot_before_rep⟩
  have hrep_bad :
      colBadBefore M D i rep = q.1 :=
    (mem_rowProfileCandidates M D i q rep).mp hrep_mem |>.2
  have hj_bad :
      colBadBefore M D i j = q.1 :=
    (mem_rowProfileCandidates M D i q j).mp hjmem |>.2
  unfold colBadBefore at hrep_bad hj_bad
  omega

theorem no_rowMixedItem_between_profile_min_and_zone {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j)) :
    let q : Fin (d + 1) :=
      ⟨rowBadBefore M D j i,
        rowBadBefore_lt_succ_of_mixedValueAtMost hD j i⟩
    let candidates := colProfileCandidates (d := d) M D j q
    let rep := candidates.min'
      (colProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot)
    ∀ item ∈ rowMixedItems M D.rowDiv (D.colDiv.part j),
      rowMixedItemPos item < 2 * i.1 →
        rowMixedItemPos item < 2 * rep.1 := by
  classical
  intro q candidates rep item hitem hbefore
  have himem : i ∈ candidates := by
    rw [mem_colProfileCandidates]
    exact ⟨hnot, rfl⟩
  have hrep_mem : rep ∈ candidates := by
    exact Finset.min'_mem candidates
      (colProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot)
  have hrep_le_i : rep ≤ i :=
    Finset.min'_le candidates i himem
  by_contra hnot_before_rep
  have hlt :
      (((rowMixedItems M D.rowDiv (D.colDiv.part j)).filter
          fun item => rowMixedItemPos item < 2 * rep.1).card) <
        (((rowMixedItems M D.rowDiv (D.colDiv.part j)).filter
          fun item => rowMixedItemPos item < 2 * i.1).card) := by
    refine MatrixPartition.card_filter_lt_card_filter_of_exists ?_ ?_
    · intro x hx
      have hrepj : rep.1 ≤ i.1 := Fin.le_iff_val_le_val.mp hrep_le_i
      omega
    · exact ⟨item, hitem, hbefore, hnot_before_rep⟩
  have hrep_bad :
      rowBadBefore M D j rep = q.1 :=
    (mem_colProfileCandidates M D j q rep).mp hrep_mem |>.2
  have hi_bad :
      rowBadBefore M D j i = q.1 :=
    (mem_colProfileCandidates M D j q i).mp himem |>.2
  unfold rowBadBefore at hrep_bad hi_bad
  omega

theorem row_eq_next_col_zone_of_not_mixed_adjacent {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Division m (k + 1)}
    (u : Fin k)
    (hL : ¬ ZoneMixed M R (C.part u.castSucc))
    (hR : ¬ ZoneMixed M R (C.part u.succ))
    (hcut : ¬ ColCutMixed M R C u)
    {r₁ r₂ : Fin n} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R)
    (hleft : M r₁ (C.first u.castSucc) = M r₂ (C.first u.castSucc)) :
    M r₁ (C.first u.succ) = M r₂ (C.first u.succ) := by
  have hunion :
      ¬ ZoneMixed M R (C.part u.castSucc ∪ C.part u.succ) :=
    not_zoneMixed_union_consecutive_cols_of_not_mixed_cut C u hL hR hcut
  rcases (not_zoneMixed_iff_vertical_or_horizontal M R
      (C.part u.castSucc ∪ C.part u.succ)).mp hunion with hv | hh
  · exact hv hr₁ hr₂ (Finset.mem_union_right _ (C.first_mem u.succ))
  · have h₁ :
        M r₁ (C.first u.castSucc) = M r₁ (C.first u.succ) :=
      hh hr₁ (Finset.mem_union_left _ (C.first_mem u.castSucc))
        (Finset.mem_union_right _ (C.first_mem u.succ))
    have h₂ :
        M r₂ (C.first u.castSucc) = M r₂ (C.first u.succ) :=
      hh hr₂ (Finset.mem_union_left _ (C.first_mem u.castSucc))
        (Finset.mem_union_right _ (C.first_mem u.succ))
    exact h₁.symm.trans (hleft.trans h₂)

theorem col_eq_next_row_zone_of_not_mixed_adjacent {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n (k + 1)} {C : Finset (Fin m)}
    (u : Fin k)
    (hL : ¬ ZoneMixed M (R.part u.castSucc) C)
    (hR : ¬ ZoneMixed M (R.part u.succ) C)
    (hcut : ¬ RowCutMixed M R C u)
    {c₁ c₂ : Fin m} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hleft : M (R.first u.castSucc) c₁ = M (R.first u.castSucc) c₂) :
    M (R.first u.succ) c₁ = M (R.first u.succ) c₂ := by
  have hunion :
      ¬ ZoneMixed M (R.part u.castSucc ∪ R.part u.succ) C :=
    not_zoneMixed_union_consecutive_rows_of_not_mixed_cut R u hL hR hcut
  rcases (not_zoneMixed_iff_vertical_or_horizontal M
      (R.part u.castSucc ∪ R.part u.succ) C).mp hunion with hv | hh
  · have h₁ :
        M (R.first u.castSucc) c₁ = M (R.first u.succ) c₁ :=
      hv (Finset.mem_union_left _ (R.first_mem u.castSucc))
        (Finset.mem_union_right _ (R.first_mem u.succ)) hc₁
    have h₂ :
        M (R.first u.castSucc) c₂ = M (R.first u.succ) c₂ :=
      hv (Finset.mem_union_left _ (R.first_mem u.castSucc))
        (Finset.mem_union_right _ (R.first_mem u.succ)) hc₂
    exact h₁.symm.trans (hleft.trans h₂)
  · exact hh (Finset.mem_union_right _ (R.first_mem u.succ)) hc₁ hc₂

theorem row_eq_col_zone_first_of_no_mixed_between {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Finset (Fin n)} {C : Division m (k + 1)}
    {a b : Fin (k + 1)}
    (hab : a ≤ b)
    (hbnot : ¬ ZoneMixed M R (C.part b))
    (hno :
      ∀ item ∈ colMixedItems M R C,
        colMixedItemPos item < 2 * b.1 → colMixedItemPos item < 2 * a.1)
    {r₁ r₂ : Fin n} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R)
    (hstart : M r₁ (C.first a) = M r₂ (C.first a)) :
    M r₁ (C.first b) = M r₂ (C.first b) := by
  classical
  by_cases hEq : a = b
  · subst b
    exact hstart
  · have hablt : a < b := lt_of_le_of_ne hab hEq
    let u : Fin k := ⟨a.1, by
      have hb : b.1 < k + 1 := b.2
      have habv : a.1 < b.1 := Fin.lt_def.mp hablt
      omega⟩
    have hua : u.castSucc = a := by
      ext
      rfl
    let a' : Fin (k + 1) := u.succ
    have ha'val : a'.1 = a.1 + 1 := by
      simp [a', u]
    have ha'le : a' ≤ b := by
      rw [Fin.le_iff_val_le_val]
      have habv : a.1 < b.1 := Fin.lt_def.mp hablt
      simp [a', u]
      omega
    have hL : ¬ ZoneMixed M R (C.part u.castSucc) := by
      rw [hua]
      by_contra hmix
      have hitem : Sum.inl a ∈ colMixedItems M R C := by
        simpa using (mem_colMixedItems_zone M R C a).mpr hmix
      have hbefore : colMixedItemPos (Sum.inl a) < 2 * b.1 := by
        simp [colMixedItemPos]
        have habv : a.1 < b.1 := Fin.lt_def.mp hablt
        omega
      have hbad := hno (Sum.inl a) hitem hbefore
      simp [colMixedItemPos] at hbad
    have hcut : ¬ ColCutMixed M R C u := by
      by_contra hmix
      have hitem : Sum.inr u ∈ colMixedItems M R C := by
        simpa using (mem_colMixedItems_cut M R C u).mpr hmix
      have hbefore : colMixedItemPos (Sum.inr u) < 2 * b.1 := by
        simp [colMixedItemPos, u]
        have habv : a.1 < b.1 := Fin.lt_def.mp hablt
        omega
      have hbad := hno (Sum.inr u) hitem hbefore
      simp [colMixedItemPos, u] at hbad
    have hR : ¬ ZoneMixed M R (C.part u.succ) := by
      by_cases hnext : a' = b
      · simpa [a', hnext] using hbnot
      · have hnextlt : a' < b := lt_of_le_of_ne ha'le hnext
        by_contra hmix
        have hitem : Sum.inl a' ∈ colMixedItems M R C := by
          simpa using (mem_colMixedItems_zone M R C a').mpr hmix
        have hbefore : colMixedItemPos (Sum.inl a') < 2 * b.1 := by
          simp [colMixedItemPos]
          exact hnextlt
        have hbad := hno (Sum.inl a') hitem hbefore
        simp [colMixedItemPos, ha'val] at hbad
    have hstep :
        M r₁ (C.first a') = M r₂ (C.first a') := by
      simpa [a', hua] using
        row_eq_next_col_zone_of_not_mixed_adjacent (M := M) (R := R) (C := C)
          u hL hR hcut hr₁ hr₂ (by simpa [hua] using hstart)
    have hno' :
        ∀ item ∈ colMixedItems M R C,
          colMixedItemPos item < 2 * b.1 → colMixedItemPos item < 2 * a'.1 := by
      intro item hitem hbefore
      by_contra hnot
      have hbad := hno item hitem hbefore
      have ha_lt_a' : a.1 < a'.1 := by omega
      omega
    exact row_eq_col_zone_first_of_no_mixed_between
      (M := M) (R := R) (C := C) ha'le hbnot hno' hr₁ hr₂ hstep
termination_by b.1 - a.1
decreasing_by
  simp_wf
  omega

theorem col_eq_row_zone_first_of_no_mixed_between {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {R : Division n (k + 1)} {C : Finset (Fin m)}
    {a b : Fin (k + 1)}
    (hab : a ≤ b)
    (hbnot : ¬ ZoneMixed M (R.part b) C)
    (hno :
      ∀ item ∈ rowMixedItems M R C,
        rowMixedItemPos item < 2 * b.1 → rowMixedItemPos item < 2 * a.1)
    {c₁ c₂ : Fin m} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hstart : M (R.first a) c₁ = M (R.first a) c₂) :
    M (R.first b) c₁ = M (R.first b) c₂ := by
  classical
  by_cases hEq : a = b
  · subst b
    exact hstart
  · have hablt : a < b := lt_of_le_of_ne hab hEq
    let u : Fin k := ⟨a.1, by
      have hb : b.1 < k + 1 := b.2
      have habv : a.1 < b.1 := Fin.lt_def.mp hablt
      omega⟩
    have hua : u.castSucc = a := by
      ext
      rfl
    let a' : Fin (k + 1) := u.succ
    have ha'val : a'.1 = a.1 + 1 := by
      simp [a', u]
    have ha'le : a' ≤ b := by
      rw [Fin.le_iff_val_le_val]
      have habv : a.1 < b.1 := Fin.lt_def.mp hablt
      simp [a', u]
      omega
    have hL : ¬ ZoneMixed M (R.part u.castSucc) C := by
      rw [hua]
      by_contra hmix
      have hitem : Sum.inl a ∈ rowMixedItems M R C := by
        simpa using (mem_rowMixedItems_zone M R C a).mpr hmix
      have hbefore : rowMixedItemPos (Sum.inl a) < 2 * b.1 := by
        simp [rowMixedItemPos]
        have habv : a.1 < b.1 := Fin.lt_def.mp hablt
        omega
      have hbad := hno (Sum.inl a) hitem hbefore
      simp [rowMixedItemPos] at hbad
    have hcut : ¬ RowCutMixed M R C u := by
      by_contra hmix
      have hitem : Sum.inr u ∈ rowMixedItems M R C := by
        simpa using (mem_rowMixedItems_cut M R C u).mpr hmix
      have hbefore : rowMixedItemPos (Sum.inr u) < 2 * b.1 := by
        simp [rowMixedItemPos, u]
        have habv : a.1 < b.1 := Fin.lt_def.mp hablt
        omega
      have hbad := hno (Sum.inr u) hitem hbefore
      simp [rowMixedItemPos, u] at hbad
    have hR : ¬ ZoneMixed M (R.part u.succ) C := by
      by_cases hnext : a' = b
      · simpa [a', hnext] using hbnot
      · have hnextlt : a' < b := lt_of_le_of_ne ha'le hnext
        by_contra hmix
        have hitem : Sum.inl a' ∈ rowMixedItems M R C := by
          simpa using (mem_rowMixedItems_zone M R C a').mpr hmix
        have hbefore : rowMixedItemPos (Sum.inl a') < 2 * b.1 := by
          simp [rowMixedItemPos]
          exact hnextlt
        have hbad := hno (Sum.inl a') hitem hbefore
        simp [rowMixedItemPos, ha'val] at hbad
    have hstep :
        M (R.first a') c₁ = M (R.first a') c₂ := by
      simpa [a', hua] using
        col_eq_next_row_zone_of_not_mixed_adjacent (M := M) (R := R) (C := C)
          u hL hR hcut hc₁ hc₂ (by simpa [hua] using hstart)
    have hno' :
        ∀ item ∈ rowMixedItems M R C,
          rowMixedItemPos item < 2 * b.1 → rowMixedItemPos item < 2 * a'.1 := by
      intro item hitem hbefore
      by_contra hnot
      have hbad := hno item hitem hbefore
      have ha_lt_a' : a.1 < a'.1 := by omega
      omega
    exact col_eq_row_zone_first_of_no_mixed_between
      (M := M) (R := R) (C := C) ha'le hbnot hno' hc₁ hc₂ hstep
termination_by b.1 - a.1
decreasing_by
  simp_wf
  omega

/-- Row profile for one row part of a division.  The `q`-th coordinate is read at
the first non-mixed column zone whose preceding-bad-item count is `q`, if such
a zone exists. -/
noncomputable def rowProfile {n m d : ℕ}
    [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1))
    (r : Fin n) : AlphabetProfile α d := by
  classical
  exact fun q =>
    if h : (rowProfileCandidates (d := d) M D i q).Nonempty then
      M r (D.colDiv.first ((rowProfileCandidates (d := d) M D i q).min' h))
    else
      default

/-- Column profile dual to `rowProfile`. -/
noncomputable def colProfile {n m d : ℕ}
    [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1))
    (c : Fin m) : AlphabetProfile α d := by
  classical
  exact fun q =>
    if h : (colProfileCandidates (d := d) M D j q).Nonempty then
      M (D.rowDiv.first ((colProfileCandidates (d := d) M D j q).min' h)) c
    else
      default

theorem row_eq_on_horizontal_zone_of_profile_eq {n m d : ℕ}
    [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j))
    (hh : ZoneHorizontal M (D.rowDiv.part i) (D.colDiv.part j))
    {r₁ r₂ : Fin n}
    (hr₁ : r₁ ∈ D.rowDiv.part i) (hr₂ : r₂ ∈ D.rowDiv.part i)
    (hprof : rowProfile (d := d) M D i r₁ =
      rowProfile (d := d) M D i r₂) :
    ∀ ⦃c : Fin m⦄, c ∈ D.colDiv.part j → M r₁ c = M r₂ c := by
  classical
  intro c hc
  let q : Fin (d + 1) :=
    ⟨colBadBefore M D i j,
      colBadBefore_lt_succ_of_mixedValueAtMost hD i j⟩
  let candidates := rowProfileCandidates (d := d) M D i q
  let hcan : candidates.Nonempty :=
    rowProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot
  let rep := candidates.min' hcan
  have hjmem : j ∈ candidates := by
    rw [mem_rowProfileCandidates]
    exact ⟨hnot, rfl⟩
  have hrep_le : rep ≤ j := Finset.min'_le candidates j hjmem
  have hno :
      ∀ item ∈ colMixedItems M (D.rowDiv.part i) D.colDiv,
        colMixedItemPos item < 2 * j.1 → colMixedItemPos item < 2 * rep.1 := by
    simpa [q, candidates, rep] using
      no_colMixedItem_between_profile_min_and_zone hD i j hnot
  have hstart :
      M r₁ (D.colDiv.first rep) = M r₂ (D.colDiv.first rep) := by
    have hq := congrFun hprof q
    simpa [rowProfile, q, candidates, hcan, rep] using hq
  have hfirst :
      M r₁ (D.colDiv.first j) = M r₂ (D.colDiv.first j) :=
    row_eq_col_zone_first_of_no_mixed_between
      (M := M) (R := D.rowDiv.part i) (C := D.colDiv)
      hrep_le hnot hno hr₁ hr₂ hstart
  have h₁ : M r₁ (D.colDiv.first j) = M r₁ c :=
    hh hr₁ (D.colDiv.first_mem j) hc
  have h₂ : M r₂ (D.colDiv.first j) = M r₂ c :=
    hh hr₂ (D.colDiv.first_mem j) hc
  exact h₁.symm.trans (hfirst.trans h₂)

theorem col_eq_on_vertical_zone_of_profile_eq {n m d : ℕ}
    [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1))
    (hnot : ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j))
    (hv : ZoneVertical M (D.rowDiv.part i) (D.colDiv.part j))
    {c₁ c₂ : Fin m}
    (hc₁ : c₁ ∈ D.colDiv.part j) (hc₂ : c₂ ∈ D.colDiv.part j)
    (hprof : colProfile (d := d) M D j c₁ =
      colProfile (d := d) M D j c₂) :
    ∀ ⦃r : Fin n⦄, r ∈ D.rowDiv.part i → M r c₁ = M r c₂ := by
  classical
  intro r hr
  let q : Fin (d + 1) :=
    ⟨rowBadBefore M D j i,
      rowBadBefore_lt_succ_of_mixedValueAtMost hD j i⟩
  let candidates := colProfileCandidates (d := d) M D j q
  let hcan : candidates.Nonempty :=
    colProfileCandidates_nonempty_of_not_zoneMixed hD i j hnot
  let rep := candidates.min' hcan
  have himem : i ∈ candidates := by
    rw [mem_colProfileCandidates]
    exact ⟨hnot, rfl⟩
  have hrep_le : rep ≤ i := Finset.min'_le candidates i himem
  have hno :
      ∀ item ∈ rowMixedItems M D.rowDiv (D.colDiv.part j),
        rowMixedItemPos item < 2 * i.1 → rowMixedItemPos item < 2 * rep.1 := by
    simpa [q, candidates, rep] using
      no_rowMixedItem_between_profile_min_and_zone hD i j hnot
  have hstart :
      M (D.rowDiv.first rep) c₁ = M (D.rowDiv.first rep) c₂ := by
    have hq := congrFun hprof q
    simpa [colProfile, q, candidates, hcan, rep] using hq
  have hfirst :
      M (D.rowDiv.first i) c₁ = M (D.rowDiv.first i) c₂ :=
    col_eq_row_zone_first_of_no_mixed_between
      (M := M) (R := D.rowDiv) (C := D.colDiv.part j)
      hrep_le hnot hno hc₁ hc₂ hstart
  have h₁ : M r c₁ = M (D.rowDiv.first i) c₁ :=
    hv hr (D.rowDiv.first_mem i) hc₁
  have h₂ : M r c₂ = M (D.rowDiv.first i) c₂ :=
    hv hr (D.rowDiv.first_mem i) hc₂
  exact h₁.trans (hfirst.trans h₂.symm)

/-- Recover the row-division index represented by a row part of
`D.toPartition`.  The default branch is never used for actual row parts. -/
noncomputable def rowIndexOfPartitionPart {n m : ℕ}
    (D : MatrixDivision n m) (R : Finset (Fin n)) :
    Fin (D.rowCuts + 1) :=
  if h : R ∈ D.toPartition.rowParts then
    Classical.choose (by
      rcases Finset.mem_map.mp h with ⟨i, _hi, hi⟩
      exact ⟨i, hi⟩)
  else
    0

theorem rowIndexOfPartitionPart_spec {n m : ℕ}
    (D : MatrixDivision n m) {R : Finset (Fin n)}
    (hR : R ∈ D.toPartition.rowParts) :
    D.rowDiv.part (rowIndexOfPartitionPart D R) = R := by
  classical
  unfold rowIndexOfPartitionPart
  simp only [dif_pos hR]
  exact Classical.choose_spec (by
    rcases Finset.mem_map.mp hR with ⟨i, _hi, hi⟩
    exact ⟨i, hi⟩)

/-- Recover the column-division index represented by a column part of
`D.toPartition`.  The default branch is never used for actual column parts. -/
noncomputable def colIndexOfPartitionPart {n m : ℕ}
    (D : MatrixDivision n m) (C : Finset (Fin m)) :
    Fin (D.colCuts + 1) :=
  if h : C ∈ D.toPartition.colParts then
    Classical.choose (by
      rcases Finset.mem_map.mp h with ⟨j, _hj, hj⟩
      exact ⟨j, hj⟩)
  else
    0

theorem colIndexOfPartitionPart_spec {n m : ℕ}
    (D : MatrixDivision n m) {C : Finset (Fin m)}
    (hC : C ∈ D.toPartition.colParts) :
    D.colDiv.part (colIndexOfPartitionPart D C) = C := by
  classical
  unfold colIndexOfPartitionPart
  simp only [dif_pos hC]
  exact Classical.choose_spec (by
    rcases Finset.mem_map.mp hC with ⟨j, _hj, hj⟩
    exact ⟨j, hj⟩)

/-- The profile refinement of a matrix division: each row part is split by
its row profile and each column part by its column profile. -/
noncomputable def profilePartition {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) : MatrixPartition n m :=
  D.toPartition.refineByLabels
    (fun R r => rowProfile (d := d) M D (rowIndexOfPartitionPart D R) r)
    (fun C c => colProfile (d := d) M D (colIndexOfPartitionPart D C) c)

/-- A profile partition refines its underlying division partition with factor
`|α|^(d+1)` on both sides. -/
theorem profilePartition_rrefines_toPartition {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) :
    MatrixPartition.RRefines (profilePartition (d := d) M D) D.toPartition
      (Fintype.card α ^ (d + 1)) := by
  classical
  constructor
  · simpa [profilePartition] using
      MatrixPartition.partsRRefine_splitPartsByLabel
        (P := D.toPartition.rowParts)
        (label := fun R r =>
          rowProfile (d := d) M D (rowIndexOfPartitionPart D R) r)
        D.toPartition.row_disjoint
        (by simp [AlphabetProfile])
  · simpa [profilePartition] using
      MatrixPartition.partsRRefine_splitPartsByLabel
        (P := D.toPartition.colParts)
        (label := fun C c =>
          colProfile (d := d) M D (colIndexOfPartitionPart D C) c)
        D.toPartition.col_disjoint
        (by simp [AlphabetProfile])

theorem rowProfile_eq_of_mem_profilePartition_rowPart_of_subset {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    {R : Finset (Fin n)} {i : Fin (D.rowCuts + 1)}
    (hR : R ∈ (profilePartition (d := d) M D).rowParts)
    (hRi : R ⊆ D.rowDiv.part i)
    {r₁ r₂ : Fin n} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R) :
    rowProfile (d := d) M D i r₁ =
      rowProfile (d := d) M D i r₂ := by
  classical
  rcases MatrixPartition.mem_splitPartsByLabel.mp
      (by simpa [profilePartition] using hR) with ⟨_hne, A, hA, b, hRdef⟩
  have hAeq : A = D.rowDiv.part i := by
    rcases Finset.mem_map.mp hA with ⟨i₀, _hi₀, hi₀A⟩
    change D.rowDiv.part i₀ = A at hi₀A
    rw [← hi₀A]
    by_contra hne
    have hr₁A : r₁ ∈ D.rowDiv.part i₀ := by
      rw [hRdef] at hr₁
      simpa [hi₀A] using (Finset.mem_filter.mp hr₁).1
    have hr₁i : r₁ ∈ D.rowDiv.part i := hRi hr₁
    have hidxne : i₀ ≠ i := by
      intro hij
      exact hne (by rw [hij])
    exact Finset.disjoint_left.mp (D.rowDiv.part_disjoint hidxne) hr₁A hr₁i
  have hidx : rowIndexOfPartitionPart D A = i := by
    apply D.rowDiv.part_injective
    rw [rowIndexOfPartitionPart_spec D hA, hAeq]
  rw [hRdef] at hr₁ hr₂
  have h₁ : rowProfile (d := d) M D (rowIndexOfPartitionPart D A) r₁ = b :=
    (Finset.mem_filter.mp hr₁).2
  have h₂ : rowProfile (d := d) M D (rowIndexOfPartitionPart D A) r₂ = b :=
    (Finset.mem_filter.mp hr₂).2
  simpa [hidx] using h₁.trans h₂.symm

theorem colProfile_eq_of_mem_profilePartition_colPart_of_subset {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    {C : Finset (Fin m)} {j : Fin (D.colCuts + 1)}
    (hC : C ∈ (profilePartition (d := d) M D).colParts)
    (hCj : C ⊆ D.colDiv.part j)
    {c₁ c₂ : Fin m} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) :
    colProfile (d := d) M D j c₁ =
      colProfile (d := d) M D j c₂ := by
  classical
  rcases MatrixPartition.mem_splitPartsByLabel.mp
      (by simpa [profilePartition] using hC) with ⟨_hne, A, hA, b, hCdef⟩
  have hAeq : A = D.colDiv.part j := by
    rcases Finset.mem_map.mp hA with ⟨j₀, _hj₀, hj₀A⟩
    change D.colDiv.part j₀ = A at hj₀A
    rw [← hj₀A]
    by_contra hne
    have hc₁A : c₁ ∈ D.colDiv.part j₀ := by
      rw [hCdef] at hc₁
      simpa [hj₀A] using (Finset.mem_filter.mp hc₁).1
    have hc₁j : c₁ ∈ D.colDiv.part j := hCj hc₁
    have hidxne : j₀ ≠ j := by
      intro hij
      exact hne (by rw [hij])
    exact Finset.disjoint_left.mp (D.colDiv.part_disjoint hidxne) hc₁A hc₁j
  have hidx : colIndexOfPartitionPart D A = j := by
    apply D.colDiv.part_injective
    rw [colIndexOfPartitionPart_spec D hA, hAeq]
  rw [hCdef] at hc₁ hc₂
  have h₁ : colProfile (d := d) M D (colIndexOfPartitionPart D A) c₁ = b :=
    (Finset.mem_filter.mp hc₁).2
  have h₂ : colProfile (d := d) M D (colIndexOfPartitionPart D A) c₂ = b :=
    (Finset.mem_filter.mp hc₂).2
  simpa [hidx] using h₁.trans h₂.symm

/-- The Section 5.8 profile split makes every originally non-mixed zone
constant.  Horizontal zones are handled by the row profile; vertical zones are
handled by the column profile. -/
theorem profilePartition_nonmixed_zones_constant {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d) :
    ∀ ⦃R C⦄,
      R ∈ (profilePartition (d := d) M D).rowParts →
      C ∈ (profilePartition (d := d) M D).colParts →
      ∀ (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1)),
        R ⊆ D.rowDiv.part i → C ⊆ D.colDiv.part j →
          ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) →
            ZoneConstant M R C := by
  classical
  intro R C hR hC i j hRi hCj hnot
  rcases (not_zoneMixed_iff_vertical_or_horizontal M
      (D.rowDiv.part i) (D.colDiv.part j)).mp hnot with hv | hh
  · intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
    have hr₂i : r₂ ∈ D.rowDiv.part i := hRi hr₂
    have hc₁j : c₁ ∈ D.colDiv.part j := hCj hc₁
    have hc₂j : c₂ ∈ D.colDiv.part j := hCj hc₂
    have hcols :
        colProfile (d := d) M D j c₁ =
          colProfile (d := d) M D j c₂ :=
      colProfile_eq_of_mem_profilePartition_colPart_of_subset hC hCj hc₁ hc₂
    have hsame_col :
        M r₂ c₁ = M r₂ c₂ :=
      col_eq_on_vertical_zone_of_profile_eq hD i j hnot hv hc₁j hc₂j hcols hr₂i
    exact (hv (hRi hr₁) hr₂i hc₁j).trans hsame_col
  · intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
    have hr₁i : r₁ ∈ D.rowDiv.part i := hRi hr₁
    have hr₂i : r₂ ∈ D.rowDiv.part i := hRi hr₂
    have hc₁j : c₁ ∈ D.colDiv.part j := hCj hc₁
    have hc₂j : c₂ ∈ D.colDiv.part j := hCj hc₂
    have hrows :
        rowProfile (d := d) M D i r₁ =
          rowProfile (d := d) M D i r₂ :=
      rowProfile_eq_of_mem_profilePartition_rowPart_of_subset hR hRi hr₁ hr₂
    have hsame_row :
        M r₁ c₁ = M r₂ c₁ :=
      row_eq_on_horizontal_zone_of_profile_eq hD i j hnot hh hr₁i hr₂i hrows hc₁j
    exact hsame_row.trans (hh hr₂i hc₁j hc₂j)


/-- Error columns for a division partition are exactly the nonconstant column
indices, transported through the column-part embedding. -/
theorem rowErrorSet_toPartition {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (i : Fin (D.rowCuts + 1)) :
    rowErrorSet M D.toPartition (D.rowDiv.part i) =
      (MatrixDivision.nonconstantRowErrorSet M D i).map
        ⟨D.colDiv.part, D.colDiv.part_injective⟩ := by
  classical
  ext C
  simp [rowErrorSet, MatrixDivision.nonconstantRowErrorSet]
  constructor
  · rintro ⟨⟨j, rfl⟩, hnonconst⟩
    exact ⟨j, hnonconst, rfl⟩
  · rintro ⟨j, hnonconst, rfl⟩
    exact ⟨⟨j, rfl⟩, hnonconst⟩

/-- Error rows for a division partition are exactly the nonconstant row
indices, transported through the row-part embedding. -/
theorem colErrorSet_toPartition {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (D : MatrixDivision n m) (j : Fin (D.colCuts + 1)) :
    colErrorSet M D.toPartition (D.colDiv.part j) =
      (MatrixDivision.nonconstantColErrorSet M D j).map
        ⟨D.rowDiv.part, D.rowDiv.part_injective⟩ := by
  classical
  ext R
  simp [colErrorSet, MatrixDivision.nonconstantColErrorSet]
  constructor
  · rintro ⟨⟨i, rfl⟩, hnonconst⟩
    exact ⟨i, hnonconst, rfl⟩
  · rintro ⟨i, hnonconst, rfl⟩
    exact ⟨⟨i, rfl⟩, hnonconst⟩

/-- Bounded nonconstant division error gives bounded partition error for the
underlying matrix partition. -/
theorem errorValueAtMost_toPartition_of_nonconstantErrorValueAtMost {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MatrixDivision.NonconstantErrorValueAtMost M D d) :
    ErrorValueAtMost M D.toPartition d := by
  classical
  constructor
  · intro R hR
    rcases Finset.mem_map.mp hR with ⟨i, _hi, rfl⟩
    change (rowErrorSet M D.toPartition (D.rowDiv.part i)).card ≤ d
    rw [rowErrorSet_toPartition]
    simpa using hD.1 i
  · intro C hC
    rcases Finset.mem_map.mp hC with ⟨j, _hj, rfl⟩
    change (colErrorSet M D.toPartition (D.colDiv.part j)).card ≤ d
    rw [colErrorSet_toPartition]
    simpa using hD.2 j

/-- Bounded error for the unordered partition underlying a division is
equivalent to bounded nonconstant error for the division.  This direction is
used when a graph partition gives the same row and column parts as an ordered
matrix division. -/
theorem nonconstantErrorValueAtMost_of_errorValueAtMost_toPartition {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : ErrorValueAtMost M D.toPartition d) :
    MatrixDivision.NonconstantErrorValueAtMost M D d := by
  classical
  constructor
  · intro i
    have hrow :
        (rowErrorSet M D.toPartition (D.rowDiv.part i)).card ≤ d :=
      hD.1 (R := D.rowDiv.part i) (by simp [MatrixDivision.toPartition])
    rw [rowErrorSet_toPartition] at hrow
    simpa using hrow
  · intro j
    have hcol :
        (colErrorSet M D.toPartition (D.colDiv.part j)).card ≤ d :=
      hD.2 (C := D.colDiv.part j) (by simp [MatrixDivision.toPartition])
    rw [colErrorSet_toPartition] at hcol
    simpa using hcol

/-- A finest division induces a finest matrix partition. -/
theorem toPartition_isFinest {n m : ℕ}
    {D : MatrixDivision n m} (hD : IsFinest D) :
    MatrixPartition.IsFinest D.toPartition := by
  classical
  rcases hD with ⟨hrow, hcol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    rcases Finset.mem_map.mp hR with ⟨i, _hi, rfl⟩
    exact hrow i
  · intro r
    rcases D.rowDiv.part_cover r with ⟨i, hi⟩
    rcases hrow i with ⟨r', hr'⟩
    have hrr' : r = r' := by
      simpa [hr'] using hi
    subst r'
    exact by
      rw [← hr']
      simp
  · intro C hC
    rcases Finset.mem_map.mp hC with ⟨j, _hj, rfl⟩
    exact hcol j
  · intro c
    rcases D.colDiv.part_cover c with ⟨j, hj⟩
    rcases hcol j with ⟨c', hc'⟩
    have hcc' : c = c' := by
      simpa [hc'] using hj
    subst c'
    exact by
      rw [← hc']
      simp

/-- The profile refinement of a finest division is a finest matrix partition. -/
theorem profilePartition_isFinest_of_isFinest {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    (M : _root_.Matrix (Fin n) (Fin m) α)
    {D : MatrixDivision n m} (hD : IsFinest D) :
    MatrixPartition.IsFinest (profilePartition (d := d) M D) := by
  have hrefine := profilePartition_rrefines_toPartition (d := d) M D
  exact MatrixPartition.isFinest_of_refines_isFinest
    ⟨hrefine.1.1, hrefine.2.1⟩ (toPartition_isFinest hD)

theorem colMixedZones_card_le_colMixedValue {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Finset (Fin n)) (C : Division m (k + 1)) :
    (colMixedZones M R C).card ≤ colMixedValue M R C := by
  unfold colMixedValue
  omega

theorem rowMixedZones_card_le_rowMixedValue {n m k : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : Division n (k + 1)) (C : Finset (Fin m)) :
    (rowMixedZones M R C).card ≤ rowMixedValue M R C := by
  unfold rowMixedValue
  omega

/-- Counting lemma for Section 5.8.  If a refinement of a division makes every
originally non-mixed zone constant, then errors can only occur above originally
mixed zones.  Since each original part is split into at most `a` refined parts,
the error value is bounded by `d * a`. -/
theorem errorValueAtMost_of_rrefines_toPartition_of_nonmixed_zones_constant
    {n m d a : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    {P : MatrixPartition n m}
    (href : MatrixPartition.RRefines P D.toPartition a)
    (hD : MixedValueAtMost M D d)
    (hconst :
      ∀ ⦃R C⦄, R ∈ P.rowParts → C ∈ P.colParts →
        ∀ (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1)),
          R ⊆ D.rowDiv.part i → C ⊆ D.colDiv.part j →
            ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) →
              ZoneConstant M R C) :
    ErrorValueAtMost M P (d * a) := by
  classical
  constructor
  · intro R hR
    rcases href.1.1 hR with ⟨R₀, hR₀, hRR₀⟩
    rcases Finset.mem_map.mp hR₀ with ⟨i, _hi, hiR₀⟩
    change D.rowDiv.part i = R₀ at hiR₀
    subst R₀
    let mixedCols : Finset (Finset (Fin m)) :=
      (colMixedZones M (D.rowDiv.part i) D.colDiv).map
        ⟨D.colDiv.part, D.colDiv.part_injective⟩
    let overMixed : Finset (Finset (Fin m)) :=
      mixedCols.biUnion fun C₀ => P.colParts.filter fun C => C ⊆ C₀
    have hsubset : rowErrorSet M P R ⊆ overMixed := by
      intro C hC
      have hCdata : C ∈ P.colParts ∧ ¬ ZoneConstant M R C := by
        simpa [rowErrorSet] using hC
      rcases href.2.1 hCdata.1 with ⟨C₀, hC₀, hCC₀⟩
      rcases Finset.mem_map.mp hC₀ with ⟨j, _hj, hjC₀⟩
      change D.colDiv.part j = C₀ at hjC₀
      subst C₀
      have hmix : ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) := by
        by_contra hnot
        exact hCdata.2 (hconst hR hCdata.1 i j hRR₀ hCC₀ hnot)
      have hbad : D.colDiv.part j ∈ mixedCols := by
        simp [mixedCols, colMixedZones, hmix]
      exact Finset.mem_biUnion.mpr ⟨D.colDiv.part j, hbad, by
        simp [hCdata.1, hCC₀]⟩
    have hcard_over : overMixed.card ≤ mixedCols.card * a := by
      unfold overMixed
      refine Finset.card_biUnion_le_card_mul _ _ _ ?_
      intro C₀ hC₀
      have hC₀part : C₀ ∈ D.toPartition.colParts := by
        rcases (by
          have := hC₀
          simpa [mixedCols] using this :
            ∃ j ∈ colMixedZones M (D.rowDiv.part i) D.colDiv,
              D.colDiv.part j = C₀) with ⟨j, _hj, rfl⟩
        simp [toPartition]
      exact href.2.2 hC₀part
    have hmixedCols :
        mixedCols.card ≤ d := by
      calc
        mixedCols.card = (colMixedZones M (D.rowDiv.part i) D.colDiv).card := by
          simp [mixedCols]
        _ ≤ colMixedValue M (D.rowDiv.part i) D.colDiv :=
          colMixedZones_card_le_colMixedValue M (D.rowDiv.part i) D.colDiv
        _ ≤ d := hD.2 i
    calc
      (rowErrorSet M P R).card ≤ overMixed.card := Finset.card_le_card hsubset
      _ ≤ mixedCols.card * a := hcard_over
      _ ≤ d * a := Nat.mul_le_mul_right a hmixedCols
  · intro C hC
    rcases href.2.1 hC with ⟨C₀, hC₀, hCC₀⟩
    rcases Finset.mem_map.mp hC₀ with ⟨j, _hj, hjC₀⟩
    change D.colDiv.part j = C₀ at hjC₀
    subst C₀
    let mixedRows : Finset (Finset (Fin n)) :=
      (rowMixedZones M D.rowDiv (D.colDiv.part j)).map
        ⟨D.rowDiv.part, D.rowDiv.part_injective⟩
    let overMixed : Finset (Finset (Fin n)) :=
      mixedRows.biUnion fun R₀ => P.rowParts.filter fun R => R ⊆ R₀
    have hsubset : colErrorSet M P C ⊆ overMixed := by
      intro R hR
      have hRdata : R ∈ P.rowParts ∧ ¬ ZoneConstant M R C := by
        simpa [colErrorSet] using hR
      rcases href.1.1 hRdata.1 with ⟨R₀, hR₀, hRR₀⟩
      rcases Finset.mem_map.mp hR₀ with ⟨i, _hi, hiR₀⟩
      change D.rowDiv.part i = R₀ at hiR₀
      subst R₀
      have hmix : ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) := by
        by_contra hnot
        exact hRdata.2 (hconst hRdata.1 hC i j hRR₀ hCC₀ hnot)
      have hbad : D.rowDiv.part i ∈ mixedRows := by
        simp [mixedRows, rowMixedZones, hmix]
      exact Finset.mem_biUnion.mpr ⟨D.rowDiv.part i, hbad, by
        simp [hRdata.1, hRR₀]⟩
    have hcard_over : overMixed.card ≤ mixedRows.card * a := by
      unfold overMixed
      refine Finset.card_biUnion_le_card_mul _ _ _ ?_
      intro R₀ hR₀
      have hR₀part : R₀ ∈ D.toPartition.rowParts := by
        rcases (by
          have := hR₀
          simpa [mixedRows] using this :
            ∃ i ∈ rowMixedZones M D.rowDiv (D.colDiv.part j),
              D.rowDiv.part i = R₀) with ⟨i, _hi, rfl⟩
        simp [toPartition]
      exact href.1.2 hR₀part
    have hmixedRows :
        mixedRows.card ≤ d := by
      calc
        mixedRows.card = (rowMixedZones M D.rowDiv (D.colDiv.part j)).card := by
          simp [mixedRows]
        _ ≤ rowMixedValue M D.rowDiv (D.colDiv.part j) :=
          rowMixedZones_card_le_rowMixedValue M D.rowDiv (D.colDiv.part j)
        _ ≤ d := hD.1 j
    calc
      (colErrorSet M P C).card ≤ overMixed.card := Finset.card_le_card hsubset
      _ ≤ mixedRows.card * a := hcard_over
      _ ≤ d * a := Nat.mul_le_mul_right a hmixedRows

/-- Profile-partition error bound, reduced to the local profile-correctness
property that every originally non-mixed zone becomes constant after the row
and column profile splits. -/
theorem errorValueAtMost_profilePartition_of_nonmixed_zones_constant
    {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d)
    (hconst :
      ∀ ⦃R C⦄,
        R ∈ (profilePartition (d := d) M D).rowParts →
        C ∈ (profilePartition (d := d) M D).colParts →
        ∀ (i : Fin (D.rowCuts + 1)) (j : Fin (D.colCuts + 1)),
          R ⊆ D.rowDiv.part i → C ⊆ D.colDiv.part j →
            ¬ ZoneMixed M (D.rowDiv.part i) (D.colDiv.part j) →
              ZoneConstant M R C) :
    ErrorValueAtMost M (profilePartition (d := d) M D)
      (d * Fintype.card α ^ (d + 1)) :=
  errorValueAtMost_of_rrefines_toPartition_of_nonmixed_zones_constant
    (profilePartition_rrefines_toPartition (d := d) M D) hD hconst

/-- The profile partition associated to a division of mixed value at most `d`
has nonconstant error value at most `d * |α|^(d+1)`. -/
theorem errorValueAtMost_profilePartition {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D : MatrixDivision n m}
    (hD : MixedValueAtMost M D d) :
    ErrorValueAtMost M (profilePartition (d := d) M D)
      (d * Fintype.card α ^ (d + 1)) :=
  errorValueAtMost_profilePartition_of_nonmixed_zones_constant hD
    (profilePartition_nonmixed_zones_constant hD)

/-- A coarsest division induces a coarsest matrix partition. -/
theorem toPartition_isCoarsest {n m : ℕ}
    {D : MatrixDivision n m} (hD : IsCoarsest D) :
    MatrixPartition.IsCoarsest D.toPartition := by
  rcases hD with ⟨hrow, hcol⟩
  constructor <;> simp [hrow, hcol]

/-- Exact row fusion of consecutive divisions is a row contraction of the
underlying matrix partitions. -/
theorem isRowContraction_toPartition_of_hasRowFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasRowFusion D E) :
    MatrixPartition.IsRowContraction D.toPartition E.toPartition := by
  classical
  rcases hDE with ⟨hrow, hcol, i, hfusion, hcols⟩
  let Rcast : Division n (E.rowCuts + 2) :=
    Division.castIndex (by omega : D.rowCuts + 1 = E.rowCuts + 2) D.rowDiv
  let Ccast : Division m (E.colCuts + 1) :=
    Division.castIndex (by omega : D.colCuts + 1 = E.colCuts + 1) D.colDiv
  let A : Finset (Fin n) := Rcast.part i.castSucc
  let B : Finset (Fin n) := Rcast.part i.succ
  refine ⟨A, ?_, B, ?_, ?_, ?_, ?_⟩
  · simp [A, Rcast, toPartition, Division.castIndex]
  · simp [B, Rcast, toPartition, Division.castIndex]
  · intro hAB
    have hidx := Rcast.part_injective hAB
    have hv := congrArg Fin.val hidx
    simp at hv
  · have hparts := Division.parts_eq_insert_erase_of_isFusionAt hfusion
    have hrow' : D.rowCuts + 1 = E.rowCuts + 2 := by omega
    have hcastParts :
        ((Finset.univ : Finset (Fin (E.rowCuts + 2))).map
            ⟨Rcast.part, Rcast.part_injective⟩) =
          ((Finset.univ : Finset (Fin (D.rowCuts + 1))).map
            ⟨D.rowDiv.part, D.rowDiv.part_injective⟩) := by
      simp [Rcast]
    rw [hcastParts] at hparts
    simpa [A, B, Rcast, toPartition, Division.castIndex] using hparts
  · ext C
    constructor
    · intro hC
      rcases Finset.mem_map.mp hC with ⟨j, _hj, hjC⟩
      change E.colDiv.part j = C at hjC
      rw [← hjC, hcols j]
      simp [toPartition, Division.castIndex]
    · intro hC
      rcases Finset.mem_map.mp hC with ⟨j, _hj, hjC⟩
      change D.colDiv.part j = C at hjC
      rw [← hjC]
      refine Finset.mem_map.mpr ⟨finCongr (by omega : D.colCuts + 1 = E.colCuts + 1) j,
        Finset.mem_univ _, ?_⟩
      change E.colDiv.part (finCongr (by omega : D.colCuts + 1 = E.colCuts + 1) j) =
        D.colDiv.part j
      rw [hcols]
      simp [Division.castIndex]

/-- Exact column fusion of consecutive divisions is a column contraction of the
underlying matrix partitions. -/
theorem isColContraction_toPartition_of_hasColFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasColFusion D E) :
    MatrixPartition.IsColContraction D.toPartition E.toPartition := by
  classical
  rcases hDE with ⟨hrow, hcol, j, hrows, hfusion⟩
  let Rcast : Division n (E.rowCuts + 1) :=
    Division.castIndex (by omega : D.rowCuts + 1 = E.rowCuts + 1) D.rowDiv
  let Ccast : Division m (E.colCuts + 2) :=
    Division.castIndex (by omega : D.colCuts + 1 = E.colCuts + 2) D.colDiv
  let A : Finset (Fin m) := Ccast.part j.castSucc
  let B : Finset (Fin m) := Ccast.part j.succ
  refine ⟨A, ?_, B, ?_, ?_, ?_, ?_⟩
  · simp [A, Ccast, toPartition, Division.castIndex]
  · simp [B, Ccast, toPartition, Division.castIndex]
  · intro hAB
    have hidx := Ccast.part_injective hAB
    have hv := congrArg Fin.val hidx
    simp at hv
  · have hparts := Division.parts_eq_insert_erase_of_isFusionAt hfusion
    have hcol' : D.colCuts + 1 = E.colCuts + 2 := by omega
    have hcastParts :
        ((Finset.univ : Finset (Fin (E.colCuts + 2))).map
            ⟨Ccast.part, Ccast.part_injective⟩) =
          ((Finset.univ : Finset (Fin (D.colCuts + 1))).map
            ⟨D.colDiv.part, D.colDiv.part_injective⟩) := by
      simp [Ccast]
    rw [hcastParts] at hparts
    simpa [A, B, Ccast, toPartition, Division.castIndex] using hparts
  · ext R
    constructor
    · intro hR
      rcases Finset.mem_map.mp hR with ⟨i, _hi, hiR⟩
      change E.rowDiv.part i = R at hiR
      rw [← hiR, hrows i]
      simp [toPartition, Division.castIndex]
    · intro hR
      rcases Finset.mem_map.mp hR with ⟨i, _hi, hiR⟩
      change D.rowDiv.part i = R at hiR
      rw [← hiR]
      refine Finset.mem_map.mpr ⟨finCongr (by omega : D.rowCuts + 1 = E.rowCuts + 1) i,
        Finset.mem_univ _, ?_⟩
      change E.rowDiv.part (finCongr (by omega : D.rowCuts + 1 = E.rowCuts + 1) i) =
        D.rowDiv.part i
      rw [hrows]
      simp [Division.castIndex]

/-- Exact fusion of consecutive divisions is a matrix-partition contraction. -/
theorem isContraction_toPartition_of_hasExactFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasExactFusion D E) :
    MatrixPartition.IsContraction D.toPartition E.toPartition := by
  rcases hDE with hrow | hcol
  · exact Or.inl (isRowContraction_toPartition_of_hasRowFusion hrow)
  · exact Or.inr (isColContraction_toPartition_of_hasColFusion hcol)

/-- Exact row fusion gives `2`-bounded refinement of the underlying matrix
partitions. -/
theorem rrefines_toPartition_of_hasRowFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasRowFusion D E) :
    MatrixPartition.RRefines D.toPartition E.toPartition 2 := by
  classical
  rcases isRowContraction_toPartition_of_hasRowFusion hDE with
    ⟨R, hR, S, hS, hRS, hrow, hcol⟩
  have hEq :
      E.toPartition = D.toPartition.rowContract hR hS hRS := by
    apply MatrixPartition.ext_parts
    · simpa [MatrixPartition.rowParts_rowContract] using hrow
    · simpa [MatrixPartition.colParts_rowContract] using hcol
  rw [hEq]
  exact MatrixPartition.rrefines_rowContract_self D.toPartition hR hS hRS

/-- Exact column fusion gives `2`-bounded refinement of the underlying matrix
partitions. -/
theorem rrefines_toPartition_of_hasColFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasColFusion D E) :
    MatrixPartition.RRefines D.toPartition E.toPartition 2 := by
  classical
  rcases isColContraction_toPartition_of_hasColFusion hDE with
    ⟨C, hC, F, hF, hCF, hcol, hrow⟩
  have hEq :
      E.toPartition = D.toPartition.colContract hC hF hCF := by
    apply MatrixPartition.ext_parts
    · simpa [MatrixPartition.rowParts_colContract] using hrow
    · simpa [MatrixPartition.colParts_colContract] using hcol
  rw [hEq]
  exact MatrixPartition.rrefines_colContract_self D.toPartition hC hF hCF

/-- Exact fusion gives `2`-bounded refinement of the underlying matrix
partitions. -/
theorem rrefines_toPartition_of_hasExactFusion {n m : ℕ}
    {D E : MatrixDivision n m}
    (hDE : HasExactFusion D E) :
    MatrixPartition.RRefines D.toPartition E.toPartition 2 := by
  rcases hDE with hrow | hcol
  · exact rrefines_toPartition_of_hasRowFusion hrow
  · exact rrefines_toPartition_of_hasColFusion hcol

/-- If profiles are monotone across an exact fusion, the corresponding profile
partitions have the bounded-refinement factor from Section 5.8. -/
theorem rrefines_profilePartition_of_hasExactFusion_of_profile_mono
    {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDE : HasExactFusion D E)
    (hrow :
      ∀ ⦃A B x y⦄, A ∈ D.toPartition.rowParts → B ∈ E.toPartition.rowParts →
        A ⊆ B → x ∈ A → y ∈ A →
          rowProfile (d := d) M D (rowIndexOfPartitionPart D A) x =
            rowProfile (d := d) M D (rowIndexOfPartitionPart D A) y →
          rowProfile (d := d) M E (rowIndexOfPartitionPart E B) x =
            rowProfile (d := d) M E (rowIndexOfPartitionPart E B) y)
    (hcol :
      ∀ ⦃A B x y⦄, A ∈ D.toPartition.colParts → B ∈ E.toPartition.colParts →
        A ⊆ B → x ∈ A → y ∈ A →
          colProfile (d := d) M D (colIndexOfPartitionPart D A) x =
            colProfile (d := d) M D (colIndexOfPartitionPart D A) y →
            colProfile (d := d) M E (colIndexOfPartitionPart E B) x =
            colProfile (d := d) M E (colIndexOfPartitionPart E B) y) :
    MatrixPartition.RRefines (profilePartition (d := d) M D)
      (profilePartition (d := d) M E) (2 * Fintype.card α ^ (d + 1)) := by
  classical
  have hbase := rrefines_toPartition_of_hasExactFusion hDE
  constructor
  · simpa [profilePartition, AlphabetProfile] using
      MatrixPartition.partsRRefine_splitPartsByLabel_of_partsRRefine
        (Q := E.toPartition.rowParts)
        (P := D.toPartition.rowParts)
        (pLabel := fun R r =>
          rowProfile (d := d) M D (rowIndexOfPartitionPart D R) r)
        (qLabel := fun R r =>
          rowProfile (d := d) M E (rowIndexOfPartitionPart E R) r)
        E.toPartition.row_disjoint hbase.1 hrow
  · simpa [profilePartition, AlphabetProfile] using
      MatrixPartition.partsRRefine_splitPartsByLabel_of_partsRRefine
        (Q := E.toPartition.colParts)
        (P := D.toPartition.colParts)
        (pLabel := fun C c =>
          colProfile (d := d) M D (colIndexOfPartitionPart D C) c)
        (qLabel := fun C c =>
          colProfile (d := d) M E (colIndexOfPartitionPart E C) c)
        E.toPartition.col_disjoint hbase.2 hcol

/-- Row profiles are monotone under an exact fusion: two rows in an old row
part that had the same old profile also have the same profile in the coarser
row part containing them. -/
theorem rowProfile_mono_of_hasExactFusion {n m d : ℕ}
    [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDmix : MixedValueAtMost M D d)
    (hDE : HasExactFusion D E) :
    ∀ ⦃A B x y⦄, A ∈ D.toPartition.rowParts → B ∈ E.toPartition.rowParts →
      A ⊆ B → x ∈ A → y ∈ A →
        rowProfile (d := d) M D (rowIndexOfPartitionPart D A) x =
          rowProfile (d := d) M D (rowIndexOfPartitionPart D A) y →
        rowProfile (d := d) M E (rowIndexOfPartitionPart E B) x =
          rowProfile (d := d) M E (rowIndexOfPartitionPart E B) y := by
  classical
  intro A B x y hA hB hAB hxA hyA hxy
  funext q
  by_cases hcan :
      (rowProfileCandidates (d := d) M E (rowIndexOfPartitionPart E B) q).Nonempty
  · simp [rowProfile, hcan]
    let iE := rowIndexOfPartitionPart E B
    let candidates := rowProfileCandidates (d := d) M E iE q
    let rep := candidates.min' hcan
    have hrep_mem : rep ∈ candidates := Finset.min'_mem candidates hcan
    have hrep_data :
        ¬ ZoneMixed M (E.rowDiv.part iE) (E.colDiv.part rep) ∧
          colBadBefore M E iE rep = q.1 := by
      simpa [candidates] using
        (mem_rowProfileCandidates M E iE q rep).mp hrep_mem
    let c : Fin m := E.colDiv.first rep
    have hcE : c ∈ E.colDiv.part rep := E.colDiv.first_mem rep
    rcases D.colDiv.part_cover c with ⟨jD, hcD⟩
    have hDcol : D.colDiv.part jD ∈ D.toPartition.colParts := by
      simp [toPartition]
    have hbase := rrefines_toPartition_of_hasExactFusion hDE
    rcases hbase.2.1 hDcol with ⟨CE, hCE, hsubCE⟩
    have hCEeq : CE = E.colDiv.part rep := by
      have hcCE : c ∈ CE := hsubCE hcD
      rcases Finset.mem_map.mp hCE with ⟨jE, _hjE, hjE⟩
      change E.colDiv.part jE = CE at hjE
      rw [← hjE] at hcCE
      by_contra hne
      have hidxne : jE ≠ rep := by
        intro h
        apply hne
        rw [← hjE, h]
      exact Finset.disjoint_left.mp (E.colDiv.part_disjoint hidxne) hcCE hcE
    have hsubCol : D.colDiv.part jD ⊆ E.colDiv.part rep := by
      simpa [hCEeq] using hsubCE
    let iD := rowIndexOfPartitionPart D A
    have hAeq : D.rowDiv.part iD = A := rowIndexOfPartitionPart_spec D hA
    have hBeq : E.rowDiv.part iE = B := rowIndexOfPartitionPart_spec E hB
    have hnot_old :
        ¬ ZoneMixed M (D.rowDiv.part iD) (D.colDiv.part jD) := by
      intro hmix_old
      have hbig : ZoneMixed M (E.rowDiv.part iE) (E.colDiv.part rep) := by
        apply zoneMixed_of_subset _ _ hmix_old
        · intro r hr
          simpa [hBeq] using hAB (by simpa [hAeq] using hr)
        · exact hsubCol
      exact hrep_data.1 hbig
    have hxD : x ∈ D.rowDiv.part iD := by simpa [hAeq] using hxA
    have hyD : y ∈ D.rowDiv.part iD := by simpa [hAeq] using hyA
    rcases (not_zoneMixed_iff_vertical_or_horizontal M
        (D.rowDiv.part iD) (D.colDiv.part jD)).mp hnot_old with hv | hh
    · exact hv hxD hyD hcD
    · exact row_eq_on_horizontal_zone_of_profile_eq
        hDmix iD jD hnot_old hh hxD hyD hxy hcD
  · simp [rowProfile, hcan]

/-- Column-profile analogue of `rowProfile_mono_of_hasExactFusion`. -/
theorem colProfile_mono_of_hasExactFusion {n m d : ℕ}
    [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDmix : MixedValueAtMost M D d)
    (hDE : HasExactFusion D E) :
    ∀ ⦃A B x y⦄, A ∈ D.toPartition.colParts → B ∈ E.toPartition.colParts →
      A ⊆ B → x ∈ A → y ∈ A →
        colProfile (d := d) M D (colIndexOfPartitionPart D A) x =
          colProfile (d := d) M D (colIndexOfPartitionPart D A) y →
        colProfile (d := d) M E (colIndexOfPartitionPart E B) x =
          colProfile (d := d) M E (colIndexOfPartitionPart E B) y := by
  classical
  intro A B x y hA hB hAB hxA hyA hxy
  funext q
  by_cases hcan :
      (colProfileCandidates (d := d) M E (colIndexOfPartitionPart E B) q).Nonempty
  · simp [colProfile, hcan]
    let jE := colIndexOfPartitionPart E B
    let candidates := colProfileCandidates (d := d) M E jE q
    let rep := candidates.min' hcan
    have hrep_mem : rep ∈ candidates := Finset.min'_mem candidates hcan
    have hrep_data :
        ¬ ZoneMixed M (E.rowDiv.part rep) (E.colDiv.part jE) ∧
          rowBadBefore M E jE rep = q.1 := by
      simpa [candidates] using
        (mem_colProfileCandidates M E jE q rep).mp hrep_mem
    let r : Fin n := E.rowDiv.first rep
    have hrE : r ∈ E.rowDiv.part rep := E.rowDiv.first_mem rep
    rcases D.rowDiv.part_cover r with ⟨iD, hrD⟩
    have hDrow : D.rowDiv.part iD ∈ D.toPartition.rowParts := by
      simp [toPartition]
    have hbase := rrefines_toPartition_of_hasExactFusion hDE
    rcases hbase.1.1 hDrow with ⟨RE, hRE, hsubRE⟩
    have hREeq : RE = E.rowDiv.part rep := by
      have hrRE : r ∈ RE := hsubRE hrD
      rcases Finset.mem_map.mp hRE with ⟨iE, _hiE, hiE⟩
      change E.rowDiv.part iE = RE at hiE
      rw [← hiE] at hrRE
      by_contra hne
      have hidxne : iE ≠ rep := by
        intro h
        apply hne
        rw [← hiE, h]
      exact Finset.disjoint_left.mp (E.rowDiv.part_disjoint hidxne) hrRE hrE
    have hsubRow : D.rowDiv.part iD ⊆ E.rowDiv.part rep := by
      simpa [hREeq] using hsubRE
    let jD := colIndexOfPartitionPart D A
    have hAeq : D.colDiv.part jD = A := colIndexOfPartitionPart_spec D hA
    have hBeq : E.colDiv.part jE = B := colIndexOfPartitionPart_spec E hB
    have hnot_old :
        ¬ ZoneMixed M (D.rowDiv.part iD) (D.colDiv.part jD) := by
      intro hmix_old
      have hbig : ZoneMixed M (E.rowDiv.part rep) (E.colDiv.part jE) := by
        apply zoneMixed_of_subset _ _ hmix_old
        · exact hsubRow
        · intro c hc
          simpa [hBeq] using hAB (by simpa [hAeq] using hc)
      exact hrep_data.1 hbig
    have hxD : x ∈ D.colDiv.part jD := by simpa [hAeq] using hxA
    have hyD : y ∈ D.colDiv.part jD := by simpa [hAeq] using hyA
    rcases (not_zoneMixed_iff_vertical_or_horizontal M
        (D.rowDiv.part iD) (D.colDiv.part jD)).mp hnot_old with hv | hh
    · exact col_eq_on_vertical_zone_of_profile_eq
        hDmix iD jD hnot_old hv hxD hyD hxy hrD
    · exact hh hrD hxD hyD
  · simp [colProfile, hcan]

/-- Consecutive profile partitions in a bounded mixed-value division sequence
have the bounded-refinement factor from Section 5.8. -/
theorem rrefines_profilePartition_of_hasExactFusion {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    {D E : MatrixDivision n m}
    (hDmix : MixedValueAtMost M D d)
    (hDE : HasExactFusion D E) :
    MatrixPartition.RRefines (profilePartition (d := d) M D)
      (profilePartition (d := d) M E) (2 * Fintype.card α ^ (d + 1)) :=
  rrefines_profilePartition_of_hasExactFusion_of_profile_mono hDE
    (rowProfile_mono_of_hasExactFusion hDmix hDE)
    (colProfile_mono_of_hasExactFusion hDmix hDE)

end MatrixDivision

/-- A bounded nonconstant-error division sequence induces a matrix contraction
sequence with the same error bound. -/
noncomputable def matrixContractionSequence_of_boundedErrorValueDivisionSequence {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (S : BoundedErrorValueDivisionSequence M d) :
    MatrixContractionSequence M d where
  stepCount := S.stepCount
  partition := fun s => (S.division s).toPartition
  starts := MatrixDivision.toPartition_isFinest S.starts
  ends := MatrixDivision.toPartition_isCoarsest S.ends
  step_contracts := by
    intro s hs
    exact MatrixDivision.isContraction_toPartition_of_hasExactFusion (S.step_fuses s hs)
  errorValue_le := by
    intro s hs
    exact MatrixDivision.errorValueAtMost_toPartition_of_nonconstantErrorValueAtMost
      (S.errorValue_le s hs)

/-- Theorem 10 bridge in predicate form. -/
theorem matrixTwinWidthAtMost_of_boundedErrorValueDivisionSequence {n m d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (S : Nonempty (BoundedErrorValueDivisionSequence M d)) :
    MatrixTwinWidthAtMost M d := by
  rcases S with ⟨S⟩
  exact ⟨matrixContractionSequence_of_boundedErrorValueDivisionSequence S⟩

/-- A coarsest matrix partition has error value at most one. -/
theorem errorValueAtMost_one_of_isCoarsest {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α)
    {P : MatrixPartition n m}
    (hP : MatrixPartition.IsCoarsest P) :
    ErrorValueAtMost M P 1 := by
  classical
  constructor
  · intro R hR
    calc
      (rowErrorSet M P R).card ≤ P.colParts.card := by
        unfold rowErrorSet
        exact Finset.card_filter_le _ _
      _ ≤ 1 := hP.2
  · intro C hC
    calc
      (colErrorSet M P C).card ≤ P.rowParts.card := by
        unfold colErrorSet
        exact Finset.card_filter_le _ _
      _ ≤ 1 := hP.1

/-- Section 5.8 bridge: a positive mixed-value division sequence yields a
bounded-error bounded-refinement partition sequence with finite-alphabet
profile parameters. -/
noncomputable def boundedErrorRefinementPartitionSequence_of_boundedMixedValue
    {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hd : 0 < d)
    (S : BoundedMixedValueDivisionSequence M d) :
    BoundedErrorRefinementPartitionSequence M
      (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1)) where
  stepCount := S.stepCount + 1
  partition := fun s =>
    if h : s ≤ S.stepCount then
      MatrixDivision.profilePartition (d := d) M (S.division s)
    else
      (S.division S.stepCount).toPartition
  starts := by
    simp [MatrixDivision.profilePartition_isFinest_of_isFinest M S.starts]
  ends := by
    have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
    simp [hnot, MatrixDivision.toPartition_isCoarsest S.ends]
  step_rrefines := by
    intro i hi
    by_cases hlast : i = S.stepCount
    · subst i
      have hcur : S.stepCount ≤ S.stepCount := le_rfl
      have hnext : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
      simp [hnext]
      exact MatrixPartition.rrefines_mono
        (by
          calc
            Fintype.card α ^ (d + 1) =
                1 * Fintype.card α ^ (d + 1) := by simp
            _ ≤ 2 * Fintype.card α ^ (d + 1) :=
              Nat.mul_le_mul_right _ (by decide : 1 ≤ 2))
        (MatrixDivision.profilePartition_rrefines_toPartition
          (d := d) M (S.division S.stepCount))
    · have hiS : i < S.stepCount := by omega
      have hcur : i ≤ S.stepCount := by omega
      have hnext : i + 1 ≤ S.stepCount := by omega
      simp [hcur, hnext]
      exact MatrixDivision.rrefines_profilePartition_of_hasExactFusion
        (S.mixedValue_le i hcur) (S.step_fuses i hiS)
  errorValue_le := by
    intro i hi
    by_cases hcur : i ≤ S.stepCount
    · simp [hcur]
      exact MatrixDivision.errorValueAtMost_profilePartition
        (S.mixedValue_le i hcur)
    · have hi_last : i = S.stepCount + 1 := by omega
      subst i
      have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
      simp [hnot]
      have hone :
          ErrorValueAtMost M (S.division S.stepCount).toPartition 1 :=
        errorValueAtMost_one_of_isCoarsest M
          (MatrixDivision.toPartition_isCoarsest S.ends)
      have hle : 1 ≤ d * Fintype.card α ^ (d + 1) := by
        have hαpos : 0 < Fintype.card α := Fintype.card_pos
        have hpos : 0 < d * Fintype.card α ^ (d + 1) :=
          Nat.mul_pos hd (pow_pos hαpos _)
        exact hpos
      exact MatrixPartition.errorValueAtMost_mono hle hone

theorem exists_boundedErrorRefinementPartitionSequence_of_boundedMixedValue
    {n m d : ℕ}
    [Fintype α] [DecidableEq α] [Inhabited α]
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (hd : 0 < d)
    (S : Nonempty (BoundedMixedValueDivisionSequence M d)) :
    Nonempty (BoundedErrorRefinementPartitionSequence M
      (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1))) := by
  rcases S with ⟨S⟩
  exact ⟨boundedErrorRefinementPartitionSequence_of_boundedMixedValue hd S⟩

/-- The second item of Theorem 10 in the division-sequence form proved by the
current matrix development: a positive-size matrix has a bounded mixed-value
fusion sequence, with the bound depending only on its mixed number. -/
theorem theorem10_second_item_mixedValue
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      (M : _root_.Matrix (Fin n) (Fin m) α) →
        Nonempty (BoundedMixedValueDivisionSequence M
          (theorem10MixedValueBound c (matrixMixedNumber M))) := by
  intro n m hn hm M
  exact boundedMixedValueDivisionSequenceTheorem hMT hn hm M
    (matrixMixedNumber M + 1)
    (not_hasMixedMinor_succ_matrixMixedNumber M)

/-- A noncomputable choice of Marcus--Tardos constants from the abstract
Marcus--Tardos theorem. -/
noncomputable def marcusTardosConstantOfTheorem
    (hMT : MarcusTardosTheorem) (t : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (hMT t)

/-- The chosen constants satisfy the Marcus--Tardos density property. -/
theorem isMarcusTardosConstant_marcusTardosConstantOfTheorem
    (hMT : MarcusTardosTheorem) :
    ∀ t : ℕ, IsMarcusTardosConstant t (marcusTardosConstantOfTheorem hMT t) := by
  classical
  intro t
  exact Nat.find_spec (hMT t)

/-- Theorem 10's second item using a bundled proof of Marcus--Tardos. -/
theorem theorem10_second_item_mixedValue_of_marcusTardos
    (hMT : MarcusTardosTheorem) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      (M : _root_.Matrix (Fin n) (Fin m) α) →
        Nonempty (BoundedMixedValueDivisionSequence M
          (theorem10MixedValueBound
            (marcusTardosConstantOfTheorem hMT) (matrixMixedNumber M))) :=
  theorem10_second_item_mixedValue
    (isMarcusTardosConstant_marcusTardosConstantOfTheorem hMT)

/-- The final, unconditional division-sequence form of the second item of
Theorem 10 for positive-size matrices. -/
theorem theorem10_mixedValue :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      (M : _root_.Matrix (Fin n) (Fin m) α) →
        Nonempty (BoundedMixedValueDivisionSequence M
          (theorem10MixedValueBound marcusTardosConstant (matrixMixedNumber M))) :=
  theorem10_second_item_mixedValue isMarcusTardosConstant_marcusTardosConstant

theorem theorem10MixedValueBound_pos (k : ℕ) :
    0 < theorem10MixedValueBound marcusTardosConstant k := by
  unfold theorem10MixedValueBound lemma13MixedValueBound
  exact Nat.mul_pos (by decide : 0 < 20)
    (IsMarcusTardosConstant.pos
      (isMarcusTardosConstant_marcusTardosConstant (k + 1))
      (Nat.succ_pos k))

/-- The remaining bridge needed for the full second item of Theorem 10,
expressed as a precise hypothesis.

Once a bounded mixed-value division sequence is refined into a bounded-error
partition sequence with the finite-alphabet profile parameters, the proved
Lemma 13 machinery and the proved Lemma 8 expansion give the advertised matrix
twin-width bound. -/
theorem theorem10_matrixTwinWidthAtMost_of_mixedValue_refinement
    [Fintype α] [DecidableEq α] [Inhabited α]
    (hrefine :
      ∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
        Nonempty (BoundedMixedValueDivisionSequence M d) →
          Nonempty (BoundedErrorRefinementPartitionSequence M
            (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1)))) :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinWidthAtMost M
        (theorem10AlphabetMatrixTwinWidthBound (Fintype.card α) (matrixMixedNumber M)) := by
  intro n m M
  by_cases hn : n = 0
  · subst n
    exact matrixTwinWidthAtMost_zeroRows M
  · by_cases hm : m = 0
    · subst m
      exact matrixTwinWidthAtMost_zeroCols M
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let d : ℕ := theorem10MixedValueBound marcusTardosConstant (matrixMixedNumber M)
      have hmixed : Nonempty (BoundedMixedValueDivisionSequence M d) := by
        simpa [d] using theorem10_mixedValue hnpos hmpos M
      have hrefined : Nonempty (BoundedErrorRefinementPartitionSequence M
          (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1))) :=
        hrefine M hmixed
      have hαpos : 0 < Fintype.card α := Fintype.card_pos
      have htww :
          MatrixTwinWidthAtMost M
            (theorem10AlphabetErrorRefinementBound (Fintype.card α) d) :=
        matrixTwinWidthAtMost_of_theorem10ErrorRefinementSequence
          (a := Fintype.card α) hαpos hrefined
      simpa [theorem10AlphabetMatrixTwinWidthBound, d] using htww

/-- The completed second item of matrix Theorem 10 over a nonempty finite
alphabet: matrix twin-width is bounded by the explicit Theorem 10 function of
the alphabet size and matrix mixed number. -/
theorem theorem10_matrixTwinWidthAtMost
    [Fintype α] [DecidableEq α] [Inhabited α] :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinWidthAtMost M
        (theorem10AlphabetMatrixTwinWidthBound (Fintype.card α) (matrixMixedNumber M)) := by
  intro n m M
  by_cases hn : n = 0
  · subst n
    exact matrixTwinWidthAtMost_zeroRows M
  · by_cases hm : m = 0
    · subst m
      exact matrixTwinWidthAtMost_zeroCols M
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let d : ℕ := theorem10MixedValueBound marcusTardosConstant (matrixMixedNumber M)
      have hmixed : Nonempty (BoundedMixedValueDivisionSequence M d) := by
        simpa [d] using theorem10_mixedValue hnpos hmpos M
      have hrefined : Nonempty (BoundedErrorRefinementPartitionSequence M
          (2 * Fintype.card α ^ (d + 1)) (d * Fintype.card α ^ (d + 1))) :=
        exists_boundedErrorRefinementPartitionSequence_of_boundedMixedValue
          (by simpa [d] using theorem10MixedValueBound_pos (matrixMixedNumber M))
          hmixed
      have hαpos : 0 < Fintype.card α := Fintype.card_pos
      have htww :
          MatrixTwinWidthAtMost M
            (theorem10AlphabetErrorRefinementBound (Fintype.card α) d) :=
        matrixTwinWidthAtMost_of_theorem10ErrorRefinementSequence
          (a := Fintype.card α) hαpos hrefined
      simpa [theorem10AlphabetMatrixTwinWidthBound, d] using htww

/-- Boolean specialization of the completed second item of matrix Theorem 10. -/
theorem theorem10_bool_matrixTwinWidthAtMost :
    ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
      MatrixTwinWidthAtMost M (theorem10MatrixTwinWidthBound (matrixMixedNumber M)) := by
  intro n m M
  simpa [theorem10MatrixTwinWidthBound, theorem10AlphabetMatrixTwinWidthBound]
    using theorem10_matrixTwinWidthAtMost (α := Bool) M

/-- Matrix Theorem 10 in the public contract shape: bounded matrix
twin-orderedness bounds mixed number, and matrix mixed number bounds matrix
twin-width via the explicit Section 5.8 function. -/
theorem theorem10_matrix_mixed_number_and_matrix_twin_width_bound_each_other
    [Fintype α] [DecidableEq α] [Inhabited α] :
    (∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ 2 * d + 2) ∧
    (∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinWidthAtMost M
        (theorem10AlphabetMatrixTwinWidthBound (Fintype.card α) (matrixMixedNumber M))) := by
  constructor
  · intro n m d M hM
    simpa [theorem10MatrixMixedNumberBound] using
      theorem10_first_item_ordered (n := n) (m := m) (d := d) M hM
  · intro n m M
    exact theorem10_matrixTwinWidthAtMost M

/-- Boolean-alphabet specialization of the public contract shape retained for
graph adjacency matrices. -/
theorem theorem10_bool_matrix_mixed_number_and_matrix_twin_width_bound_each_other :
    (∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
      MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ 2 * d + 2) ∧
    (∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
      MatrixTwinWidthAtMost M (theorem10MatrixTwinWidthBound (matrixMixedNumber M))) := by
  constructor
  · intro n m d M hM
    exact (theorem10_matrix_mixed_number_and_matrix_twin_width_bound_each_other
      (α := Bool)).1 M hM
  · exact theorem10_bool_matrixTwinWidthAtMost

end Matrix
end TwinWidth

/- ===== end Matrix/Theorem10.lean ===== -/

/- ===== begin Matrix/Symmetric.lean ===== -/

/-
# Symmetric matrix contraction sequences

For graph adjacency matrices, Theorem 14 uses the symmetric version of the
matrix construction: every row contraction is immediately mirrored by the
corresponding column contraction, and conversely.  This file records the
front-end structure for those paired contractions.
-/

namespace TwinWidth
namespace Matrix

/-- A square Boolean matrix is symmetric when mirroring about the diagonal
preserves every entry.  This is the matrix property used by Theorem 14 for
ordered adjacency matrices of undirected graphs. -/
def IsSymmetricMatrix {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) : Prop :=
  ∀ i j, M i j = M j i

namespace MatrixDivision

/-- The square matrix division obtained by using the same interval division
for rows and columns.  This is the local model for a perfectly mirrored
division. -/
def same {n k : ℕ} (D : Division n (k + 1)) : MatrixDivision n n where
  rowCuts := k
  colCuts := k
  rowDiv := D
  colDiv := D

end MatrixDivision

theorem zoneConstant_swap_iff_of_isSymmetricMatrix {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (R C : Finset (Fin n)) :
    ZoneConstant M R C ↔ ZoneConstant M C R := by
  constructor
  · intro h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂
    calc
      M c₁ r₁ = M r₁ c₁ := hM c₁ r₁
      _ = M r₂ c₂ := h hr₁ hr₂ hc₁ hc₂
      _ = M c₂ r₂ := (hM c₂ r₂).symm
  · intro h r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
    calc
      M r₁ c₁ = M c₁ r₁ := hM r₁ c₁
      _ = M c₂ r₂ := h hc₁ hc₂ hr₁ hr₂
      _ = M r₂ c₂ := (hM r₂ c₂).symm

theorem zoneVertical_swap_iff_zoneHorizontal_of_isSymmetricMatrix {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (R C : Finset (Fin n)) :
    ZoneVertical M R C ↔ ZoneHorizontal M C R := by
  constructor
  · intro h c hc r₁ r₂ hr₁ hr₂
    calc
      M c r₁ = M r₁ c := hM c r₁
      _ = M r₂ c := h (r₁ := r₁) (r₂ := r₂) hr₁ hr₂ (c := c) hc
      _ = M c r₂ := (hM c r₂).symm
  · intro h r₁ r₂ hr₁ hr₂ c hc
    calc
      M r₁ c = M c r₁ := hM r₁ c
      _ = M c r₂ := h (r := c) hc (c₁ := r₁) (c₂ := r₂) hr₁ hr₂
      _ = M r₂ c := (hM r₂ c).symm

theorem zoneHorizontal_swap_iff_zoneVertical_of_isSymmetricMatrix {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (R C : Finset (Fin n)) :
    ZoneHorizontal M R C ↔ ZoneVertical M C R := by
  constructor
  · intro h c₁ c₂ hc₁ hc₂ r hr
    calc
      M c₁ r = M r c₁ := hM c₁ r
      _ = M r c₂ := h (r := r) hr (c₁ := c₁) (c₂ := c₂) hc₁ hc₂
      _ = M c₂ r := (hM c₂ r).symm
  · intro h r hr c₁ c₂ hc₁ hc₂
    calc
      M r c₁ = M c₁ r := hM r c₁
      _ = M c₂ r := h (r₁ := c₁) (r₂ := c₂) hc₁ hc₂ (c := r) hr
      _ = M r c₂ := (hM r c₂).symm

theorem zoneMixed_swap_iff_of_isSymmetricMatrix {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (R C : Finset (Fin n)) :
    ZoneMixed M R C ↔ ZoneMixed M C R := by
  constructor
  · intro h
    exact
      ⟨fun hv => h.2
          ((zoneHorizontal_swap_iff_zoneVertical_of_isSymmetricMatrix hM R C).mpr hv),
        fun hh => h.1
          ((zoneVertical_swap_iff_zoneHorizontal_of_isSymmetricMatrix hM R C).mpr hh)⟩
  · intro h
    exact
      ⟨fun hv => h.2
          ((zoneVertical_swap_iff_zoneHorizontal_of_isSymmetricMatrix hM R C).mp hv),
        fun hh => h.1
          ((zoneHorizontal_swap_iff_zoneVertical_of_isSymmetricMatrix hM R C).mp hh)⟩

theorem rowCutVertical_iff_colCutHorizontal_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) (i : Fin k) :
    RowCutVertical M D C i ↔ ColCutHorizontal M C D i := by
  constructor
  · intro h c hc
    calc
      M c (D.last i.castSucc) = M (D.last i.castSucc) c := hM c (D.last i.castSucc)
      _ = M (D.first i.succ) c := h hc
      _ = M c (D.first i.succ) := (hM c (D.first i.succ)).symm
  · intro h c hc
    calc
      M (D.last i.castSucc) c = M c (D.last i.castSucc) := hM (D.last i.castSucc) c
      _ = M c (D.first i.succ) := h (r := c) hc
      _ = M (D.first i.succ) c := (hM (D.first i.succ) c).symm

theorem rowCutHorizontal_iff_colCutVertical_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) (i : Fin k) :
    RowCutHorizontal M D C i ↔ ColCutVertical M C D i := by
  constructor
  · intro h
    constructor
    · intro c₁ c₂ hc₁ hc₂
      calc
        M c₁ (D.last i.castSucc) = M (D.last i.castSucc) c₁ :=
          hM c₁ (D.last i.castSucc)
        _ = M (D.last i.castSucc) c₂ := h.1 hc₁ hc₂
        _ = M c₂ (D.last i.castSucc) := (hM c₂ (D.last i.castSucc)).symm
    · intro c₁ c₂ hc₁ hc₂
      calc
        M c₁ (D.first i.succ) = M (D.first i.succ) c₁ :=
          hM c₁ (D.first i.succ)
        _ = M (D.first i.succ) c₂ := h.2 hc₁ hc₂
        _ = M c₂ (D.first i.succ) := (hM c₂ (D.first i.succ)).symm
  · intro h
    constructor
    · intro c₁ c₂ hc₁ hc₂
      calc
        M (D.last i.castSucc) c₁ = M c₁ (D.last i.castSucc) :=
          hM (D.last i.castSucc) c₁
        _ = M c₂ (D.last i.castSucc) := h.1 hc₁ hc₂
        _ = M (D.last i.castSucc) c₂ := (hM (D.last i.castSucc) c₂).symm
    · intro c₁ c₂ hc₁ hc₂
      calc
        M (D.first i.succ) c₁ = M c₁ (D.first i.succ) :=
          hM (D.first i.succ) c₁
        _ = M c₂ (D.first i.succ) := h.2 hc₁ hc₂
        _ = M (D.first i.succ) c₂ := (hM (D.first i.succ) c₂).symm

theorem rowCutMixed_iff_colCutMixed_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) (i : Fin k) :
    RowCutMixed M D C i ↔ ColCutMixed M C D i := by
  constructor
  · intro h
    exact
      ⟨fun hv => h.2
          ((rowCutHorizontal_iff_colCutVertical_of_isSymmetricMatrix hM D C i).mpr hv),
        fun hh => h.1
          ((rowCutVertical_iff_colCutHorizontal_of_isSymmetricMatrix hM D C i).mpr hh)⟩
  · intro h
    exact
      ⟨fun hv => h.2
          ((rowCutVertical_iff_colCutHorizontal_of_isSymmetricMatrix hM D C i).mp hv),
        fun hh => h.1
          ((rowCutHorizontal_iff_colCutVertical_of_isSymmetricMatrix hM D C i).mp hh)⟩

theorem rowMixedValue_eq_colMixedValue_swap_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) :
    rowMixedValue M D C = colMixedValue M C D := by
  classical
  have hzones : rowMixedZones M D C = colMixedZones M C D := by
    ext i
    simp [rowMixedZones, colMixedZones,
      (zoneMixed_swap_iff_of_isSymmetricMatrix hM (D.part i) C)]
  have hcuts : rowMixedCuts M D C = colMixedCuts M C D := by
    ext i
    simp [rowMixedCuts, colMixedCuts,
      (rowCutMixed_iff_colCutMixed_of_isSymmetricMatrix hM D C i)]
  simp [rowMixedValue, colMixedValue, hzones, hcuts]

theorem rowMixedItems_eq_colMixedItems_swap_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (C : Finset (Fin n)) :
    rowMixedItems M D C = colMixedItems M C D := by
  classical
  ext item
  cases item with
  | inl i =>
      simp [zoneMixed_swap_iff_of_isSymmetricMatrix hM (D.part i) C]
  | inr i =>
      simp [rowCutMixed_iff_colCutMixed_of_isSymmetricMatrix hM D C i]

/-- A square matrix partition is symmetric when its row and column parts are
the same family. -/
def MatrixPartition.IsSymmetric {n : ℕ} (P : MatrixPartition n n) : Prop :=
  P.rowParts = P.colParts

namespace MatrixPartition

theorem splitPartsByLabel_eq_of_base_eq_of_labels
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    {P Q : Finset (Finset α)}
    {labelP labelQ : Finset α → α → β}
    (hPQ : P = Q)
    (hlabel :
      ∀ ⦃A⦄, A ∈ P → ∀ ⦃x⦄, x ∈ A → labelP A x = labelQ A x) :
    splitPartsByLabel P labelP = splitPartsByLabel Q labelQ := by
  classical
  subst Q
  ext F
  constructor
  · intro hF
    rcases (mem_splitPartsByLabel.mp hF) with ⟨hne, A, hA, b, rfl⟩
    refine mem_splitPartsByLabel.mpr ⟨?_, A, hA, b, ?_⟩
    · rcases hne with ⟨x, hx⟩
      exact ⟨x, by simpa [hlabel hA (Finset.mem_of_mem_filter x hx)] using hx⟩
    · ext x
      by_cases hxA : x ∈ A
      · simp [hxA, hlabel hA hxA]
      · simp [hxA]
  · intro hF
    rcases (mem_splitPartsByLabel.mp hF) with ⟨hne, A, hA, b, rfl⟩
    refine mem_splitPartsByLabel.mpr ⟨?_, A, hA, b, ?_⟩
    · rcases hne with ⟨x, hx⟩
      exact ⟨x, by simpa [hlabel hA (Finset.mem_of_mem_filter x hx)] using hx⟩
    · ext x
      by_cases hxA : x ∈ A
      · simp [hxA, hlabel hA hxA]
      · simp [hxA]

end MatrixPartition

namespace MatrixDivision

/-- A square division is symmetric when row and column cuts agree and matching
row and column parts are the same subsets of `Fin n`. -/
def IsSymmetric {n : ℕ} (D : MatrixDivision n n) : Prop :=
  ∃ hcuts : D.rowCuts = D.colCuts,
    ∀ i : Fin (D.rowCuts + 1),
      D.rowDiv.part i =
        D.colDiv.part
          ((finCongr (by omega : D.rowCuts + 1 = D.colCuts + 1)) i)

@[simp] theorem same_isSymmetric {n k : ℕ} (D : Division n (k + 1)) :
    (same D).IsSymmetric := by
  exact ⟨rfl, by intro i; rfl⟩

theorem finest_isSymmetric {n : ℕ} (hn : 0 < n) :
    (finest hn hn).IsSymmetric := by
  refine ⟨rfl, ?_⟩
  intro i
  simp [finest, Division.castIndex, Division.singleton]
  rfl

theorem toPartition_isSymmetric_of_isSymmetric {n : ℕ}
    {D : MatrixDivision n n} (hD : D.IsSymmetric) :
    D.toPartition.IsSymmetric := by
  classical
  rcases D with ⟨rowCuts, colCuts, rowDiv, colDiv⟩
  rcases hD with ⟨hcuts, hparts⟩
  dsimp at hcuts hparts ⊢
  subst colCuts
  ext A
  constructor
  · intro hA
    rcases Finset.mem_map.mp hA with ⟨i, _hi, rfl⟩
    refine Finset.mem_map.mpr
      ⟨(finCongr (by omega : rowCuts + 1 = rowCuts + 1)) i,
        Finset.mem_univ _, ?_⟩
    exact (hparts i).symm
  · intro hA
    rcases Finset.mem_map.mp hA with ⟨j, _hj, rfl⟩
    let i : Fin (rowCuts + 1) :=
      (finCongr (by omega : rowCuts + 1 = rowCuts + 1)).symm j
    refine Finset.mem_map.mpr ⟨i, Finset.mem_univ _, ?_⟩
    have h := hparts i
    simpa [i] using h

theorem profilePartition_isSymmetric_of_profile_eq {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {D : MatrixDivision n n}
    (hD : D.IsSymmetric)
    (hprofile :
      ∀ ⦃A⦄, A ∈ D.toPartition.rowParts → ∀ ⦃x⦄, x ∈ A →
        rowProfile (d := d) M D (rowIndexOfPartitionPart D A) x =
          colProfile (d := d) M D (colIndexOfPartitionPart D A) x) :
    (profilePartition (d := d) M D).IsSymmetric := by
  classical
  have hparts : D.toPartition.rowParts = D.toPartition.colParts :=
    toPartition_isSymmetric_of_isSymmetric hD
  unfold profilePartition
  exact MatrixPartition.splitPartsByLabel_eq_of_base_eq_of_labels
    hparts hprofile

/-- For a mirrored division, the row and column bad-item counters agree after
swapping the matrix across the diagonal. -/
theorem colBadBefore_same_eq_rowBadBefore_same_of_isSymmetricMatrix {n k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (i j : Fin (k + 1)) :
    colBadBefore M (same D) i j = rowBadBefore M (same D) i j := by
  classical
  simp [colBadBefore, rowBadBefore, same,
    rowMixedItems_eq_colMixedItems_swap_of_isSymmetricMatrix hM D (D.part i),
    colMixedItemPos, rowMixedItemPos]
  rfl

/-- The candidate indices used by row and column profiles are the same for a
symmetric matrix on a mirrored division. -/
theorem rowProfileCandidates_same_eq_colProfileCandidates_same_of_isSymmetricMatrix
    {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (i : Fin (k + 1)) (q : Fin (d + 1)) :
    rowProfileCandidates (d := d) M (same D) i q =
      colProfileCandidates (d := d) M (same D) i q := by
  classical
  ext j
  constructor
  · intro hj
    have hdata :
        ¬ ZoneMixed M (D.part i) (D.part j) ∧
          colBadBefore M (same D) i j = q.1 := by
      change j ∈ ((Finset.univ : Finset (Fin (k + 1))).filter fun j =>
        ¬ ZoneMixed M (D.part i) (D.part j) ∧
          colBadBefore M (same D) i j = q.1) at hj
      exact (Finset.mem_filter.mp hj).2
    have hout :
        ¬ ZoneMixed M (D.part j) (D.part i) ∧
          rowBadBefore M (same D) i j = q.1 := by
      constructor
      · intro hmix
        exact hdata.1
          ((zoneMixed_swap_iff_of_isSymmetricMatrix hM (D.part i) (D.part j)).mpr hmix)
      · simpa [(colBadBefore_same_eq_rowBadBefore_same_of_isSymmetricMatrix
          hM D i j).symm] using hdata.2
    change j ∈ ((Finset.univ : Finset (Fin (k + 1))).filter fun j =>
          ¬ ZoneMixed M (D.part j) (D.part i) ∧
            rowBadBefore M (same D) i j = q.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hout⟩
  · intro hj
    have hdata :
        ¬ ZoneMixed M (D.part j) (D.part i) ∧
          rowBadBefore M (same D) i j = q.1 := by
      change j ∈ ((Finset.univ : Finset (Fin (k + 1))).filter fun j =>
        ¬ ZoneMixed M (D.part j) (D.part i) ∧
          rowBadBefore M (same D) i j = q.1) at hj
      exact (Finset.mem_filter.mp hj).2
    have hout :
        ¬ ZoneMixed M (D.part i) (D.part j) ∧
          colBadBefore M (same D) i j = q.1 := by
      constructor
      · intro hmix
        exact hdata.1
          ((zoneMixed_swap_iff_of_isSymmetricMatrix hM (D.part i) (D.part j)).mp hmix)
      · simpa [colBadBefore_same_eq_rowBadBefore_same_of_isSymmetricMatrix
          hM D i j] using hdata.2
    change j ∈ ((Finset.univ : Finset (Fin (k + 1))).filter fun j =>
          ¬ ZoneMixed M (D.part i) (D.part j) ∧
            colBadBefore M (same D) i j = q.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hout⟩

/-- Row and column profiles agree pointwise on a symmetric matrix when the row
and column divisions are literally mirrored by the same interval division. -/
theorem rowProfile_same_eq_colProfile_same_of_isSymmetricMatrix {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1))
    (i : Fin (k + 1)) (x : Fin n) :
    rowProfile (d := d) M (same D) i x =
      colProfile (d := d) M (same D) i x := by
  classical
  funext q
  let Rset := rowProfileCandidates (d := d) M (same D) i q
  let Cset := colProfileCandidates (d := d) M (same D) i q
  have hsets : Rset = Cset := by
    simpa [Rset, Cset] using
      rowProfileCandidates_same_eq_colProfileCandidates_same_of_isSymmetricMatrix
        hM D i q
  by_cases hR : Rset.Nonempty
  · have hC : Cset.Nonempty := by simpa [← hsets] using hR
    have hmin : Rset.min' hR = Cset.min' hC := by
      apply le_antisymm
      · exact Finset.min'_le _ _ (by
          simpa [← hsets] using Finset.min'_mem Cset hC)
      · exact Finset.min'_le _ _ (by
          simpa [hsets] using Finset.min'_mem Rset hR)
    have hRactual :
        (rowProfileCandidates (d := d) M (same D) i q).Nonempty := by
      simpa [Rset] using hR
    have hCactual :
        (colProfileCandidates (d := d) M (same D) i q).Nonempty := by
      simpa [Cset] using hC
    have hminActual :
        (rowProfileCandidates (d := d) M (same D) i q).min' hRactual =
          (colProfileCandidates (d := d) M (same D) i q).min' hCactual := by
      simpa [Rset, Cset] using hmin
    have hRstruct :
        (rowProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).Nonempty := by
      simpa [same] using hRactual
    have hCstruct :
        (colProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).Nonempty := by
      simpa [same] using hCactual
    have hminStruct :
        (rowProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).min' hRstruct =
          (colProfileCandidates (d := d) M
            ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
              MatrixDivision n n) i q).min' hCstruct := by
      simpa [same] using hminActual
    have hentry :=
      hM x (D.first
        ((rowProfileCandidates (d := d) M (same D) i q).min' hRactual))
    simpa [rowProfile, colProfile, same, hRstruct, hCstruct, hminStruct] using hentry
  · have hC : ¬ Cset.Nonempty := by
      intro h
      exact hR (by simpa [hsets] using h)
    have hRactual :
        ¬ (rowProfileCandidates (d := d) M (same D) i q).Nonempty := by
      simpa [Rset] using hR
    have hCactual :
        ¬ (colProfileCandidates (d := d) M (same D) i q).Nonempty := by
      simpa [Cset] using hC
    have hRstruct :
        ¬ (rowProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).Nonempty := by
      simpa [same] using hRactual
    have hCstruct :
        ¬ (colProfileCandidates (d := d) M
          ({ rowCuts := k, colCuts := k, rowDiv := D, colDiv := D } :
            MatrixDivision n n) i q).Nonempty := by
      simpa [same] using hCactual
    simp [rowProfile, colProfile, same, hRstruct, hCstruct]

/-- The Section 5.8 profile partition is symmetric for a symmetric matrix when
the underlying division uses the same row and column intervals. -/
theorem profilePartition_same_isSymmetric_of_isSymmetricMatrix {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (D : Division n (k + 1)) :
    (profilePartition (d := d) M (same D)).IsSymmetric := by
  classical
  apply profilePartition_isSymmetric_of_profile_eq (same_isSymmetric D)
  intro A hA x hx
  have hAcol : A ∈ (same D).toPartition.colParts := by
    simpa [same] using hA
  have hrowSpec :=
    rowIndexOfPartitionPart_spec (same D) hA
  have hcolSpec :=
    colIndexOfPartitionPart_spec (same D) hAcol
  have hidx :
      rowIndexOfPartitionPart (same D) A =
        colIndexOfPartitionPart (same D) A := by
    apply D.part_injective
    calc
      D.part (rowIndexOfPartitionPart (same D) A) = A := by
        simpa [same] using hrowSpec
      _ = D.part (colIndexOfPartitionPart (same D) A) := by
        simpa [same] using hcolSpec.symm
  simpa [hidx] using
    rowProfile_same_eq_colProfile_same_of_isSymmetricMatrix
      (d := d) hM D (rowIndexOfPartitionPart (same D) A) x

/-- Mirrored fusion preserves bounded mixed value once the newly fused row
block has bounded column mixed value.  The row side follows by symmetry from
the column side. -/
theorem mixedValueAtMost_same_fuse_of_colMixedValue_fused_le {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M)
    (D : Division n (k + 2)) (hD : MixedValueAtMost M (same D) d)
    (i : Fin (k + 1))
    (hnew : colMixedValue M ((D.fuse i).part i) D ≤ d) :
    MixedValueAtMost M (same (D.fuse i)) d := by
  classical
  have hcol :
      ∀ a : Fin (k + 1),
        colMixedValue M ((D.fuse i).part a) (D.fuse i) ≤ d := by
    intro a
    have hmono :
        colMixedValue M ((D.fuse i).part a) (D.fuse i) ≤
          colMixedValue M ((D.fuse i).part a) D :=
      colMixedValue_fuse_le (M := M) ((D.fuse i).part a) D i
    refine le_trans hmono ?_
    by_cases hai : a = i
    · subst a
      exact hnew
    · by_cases hai_lt : a < i
      · have hpart := D.fuse_part_of_lt (i := i) (j := a) hai_lt
        rw [hpart]
        simpa [same] using hD.2 a.castSucc
      · have hia : i < a := lt_of_le_of_ne (le_of_not_gt hai_lt) (Ne.symm hai)
        have hpart := D.fuse_part_of_gt (i := i) (j := a) hia
        rw [hpart]
        simpa [same] using hD.2 a.succ
  constructor
  · intro j
    change rowMixedValue M (D.fuse i) ((D.fuse i).part j) ≤ d
    rw [rowMixedValue_eq_colMixedValue_swap_of_isSymmetricMatrix
      hM (D.fuse i) ((D.fuse i).part j)]
    exact hcol j
  · intro a
    change colMixedValue M ((D.fuse i).part a) (D.fuse i) ≤ d
    exact hcol a

/-- A local good cut for the mixed-value greedy proof.  This is the
non-contracted form of `GreedyFusionStep`, retaining the cut index needed by
the mirrored construction. -/
def HasGoodCut {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool)
    (D : MatrixDivision n n) (d : ℕ) : Prop :=
  (∃ hrow : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
    colMixedValue M
      ((D.rowFuse hrow i).rowDiv.part
        ((finCongr
          (by simp [rowFuse]; omega :
            D.rowCuts = (D.rowFuse hrow i).rowCuts + 1)) i))
      (D.rowFuse hrow i).colDiv ≤ d) ∨
    (∃ hcol : 0 < D.colCuts, ∃ j : Fin D.colCuts,
      rowMixedValue M
        (D.colFuse hcol j).rowDiv
        ((D.colFuse hcol j).colDiv.part
          ((finCongr
            (by simp [colFuse]; omega :
              D.colCuts = (D.colFuse hcol j).colCuts + 1)) j)) ≤ d)

/-- Lemma 13's local Marcus--Tardos step, retaining the good cut rather than
immediately packaging it as a one-sided fusion. -/
theorem hasGoodCut_of_marcusTardos
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n : ℕ} (M : _root_.Matrix (Fin n) (Fin n) Bool) (t : ℕ),
      MixedFree M t → ∀ D : MatrixDivision n n,
        MixedValueAtMost M D (lemma13MixedValueBound c t) →
          ¬ IsCoarsest D →
            HasGoodCut M D (lemma13MixedValueBound c t) := by
  intro n M t hfree D hD hcoarse
  by_cases ht : t = 0
  · subst t
    exact (False.elim (hfree (hasMixedMinor_zero M)))
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    by_cases hrow : 0 < D.rowCuts
    · by_cases hcol : 0 < D.colCuts
      · by_cases hgoodRow :
          ∃ hrow' : 0 < D.rowCuts, ∃ i : Fin D.rowCuts,
            colMixedValue M
              ((D.rowFuse hrow' i).rowDiv.part
                ((finCongr
                  (by simp [rowFuse]; omega :
                    D.rowCuts =
                      (D.rowFuse hrow' i).rowCuts + 1)) i))
              (D.rowFuse hrow' i).colDiv ≤
                lemma13MixedValueBound c t
        · exact Or.inl hgoodRow
        · by_cases hgoodCol :
            ∃ hcol' : 0 < D.colCuts, ∃ j : Fin D.colCuts,
              rowMixedValue M
                (D.colFuse hcol' j).rowDiv
                ((D.colFuse hcol' j).colDiv.part
                  ((finCongr
                    (by simp [colFuse]; omega :
                      D.colCuts =
                        (D.colFuse hcol' j).colCuts + 1)) j)) ≤
                lemma13MixedValueBound c t
          · exact Or.inr hgoodCol
          · exact False.elim
              (pairedMarcusTardosCountingStep
                M t (hMT t) hfree D hD hrow hcol hgoodRow hgoodCol)
      · have hcol0 : D.colCuts = 0 := Nat.eq_zero_of_not_pos hcol
        rcases exists_goodRowCut_of_colCuts_eq_zero
          (M := M) (hMT t) htpos D hrow hcol0 with ⟨i, hi⟩
        exact Or.inl ⟨hrow, i, le_trans hi (by
          have hcpos : 0 < c t := IsMarcusTardosConstant.pos (hMT t) htpos
          simp [lemma13MixedValueBound]
          omega)⟩
    · have hrow0 : D.rowCuts = 0 := Nat.eq_zero_of_not_pos hrow
      have hcol : 0 < D.colCuts := by
        by_contra hcolnot
        have hcol0 : D.colCuts = 0 := Nat.eq_zero_of_not_pos hcolnot
        exact hcoarse ⟨hrow0, hcol0⟩
      rcases exists_goodColCut_of_rowCuts_eq_zero
        (M := M) (hMT t) htpos D hcol hrow0 with ⟨j, hj⟩
      exact Or.inr ⟨hcol, j, le_trans hj (by
        have hcpos : 0 < c t := IsMarcusTardosConstant.pos (hMT t) htpos
        simp [lemma13MixedValueBound]
        omega)⟩

/-- The row-good-cut conclusion for `same D` is exactly the fused-row mixed
value bound needed by the mirrored fusion lemma. -/
theorem colMixedValue_fused_le_of_goodRow_same {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (D : Division n (k + 2))
    (hrow : 0 < (same D).rowCuts) (i : Fin (same D).rowCuts)
    (hgood :
      colMixedValue M
        (((same D).rowFuse hrow i).rowDiv.part
          ((finCongr
            (by simp [rowFuse]; omega :
              (same D).rowCuts = ((same D).rowFuse hrow i).rowCuts + 1)) i))
        ((same D).rowFuse hrow i).colDiv ≤ d) :
    colMixedValue M
      ((D.fuse ((finCongr (by rfl : (same D).rowCuts = k + 1)) i)).part
        ((finCongr (by rfl : (same D).rowCuts = k + 1)) i))
      D ≤ d := by
  simpa [same, rowFuse] using hgood

/-- The column-good-cut conclusion for `same D`, mirrored across a symmetric
matrix, gives the same fused-row column mixed value bound. -/
theorem colMixedValue_fused_le_of_goodCol_same {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M)
    (D : Division n (k + 2))
    (hcol : 0 < (same D).colCuts) (j : Fin (same D).colCuts)
    (hgood :
      rowMixedValue M
        ((same D).colFuse hcol j).rowDiv
        (((same D).colFuse hcol j).colDiv.part
          ((finCongr
            (by simp [colFuse]; omega :
              (same D).colCuts = ((same D).colFuse hcol j).colCuts + 1)) j)) ≤ d) :
    colMixedValue M
      ((D.fuse ((finCongr (by rfl : (same D).colCuts = k + 1)) j)).part
        ((finCongr (by rfl : (same D).colCuts = k + 1)) j))
      D ≤ d := by
  have hrow :
      rowMixedValue M D
        ((D.fuse ((finCongr (by rfl : (same D).colCuts = k + 1)) j)).part
          ((finCongr (by rfl : (same D).colCuts = k + 1)) j)) ≤ d := by
    simpa [same, colFuse] using hgood
  rwa [rowMixedValue_eq_colMixedValue_swap_of_isSymmetricMatrix
    hM D
      ((D.fuse ((finCongr (by rfl : (same D).colCuts = k + 1)) j)).part
        ((finCongr (by rfl : (same D).colCuts = k + 1)) j))] at hrow

end MatrixDivision

/-- One symmetric contraction block: either contract two row parts and mirror
the same contraction on columns, or contract two column parts and mirror it on
rows.  Since row and column parts are both subsets of `Fin n`, both cases are
represented by the same merged pair of parts. -/
def MatrixPartition.IsSymmetricContraction {n : ℕ}
    (P Q : MatrixPartition n n) : Prop :=
  ∃ A ∈ P.rowParts, ∃ B ∈ P.rowParts, A ≠ B ∧
    Q.rowParts = insert (A ∪ B) ((P.rowParts.erase A).erase B) ∧
    Q.colParts = insert (A ∪ B) ((P.colParts.erase A).erase B)

namespace MatrixPartition

/-- The unique empty partition used for `0 × 0` matrix zerology. -/
def emptyZero : MatrixPartition 0 0 where
  rowParts := ∅
  row_nonempty := by simp
  row_disjoint := by simp
  row_cover := by intro r; exact Fin.elim0 r
  colParts := ∅
  col_nonempty := by simp
  col_disjoint := by simp
  col_cover := by intro c; exact Fin.elim0 c

theorem emptyZero_isFinest : emptyZero.IsFinest := by
  constructor
  · simp [emptyZero]
  constructor
  · intro r
    exact Fin.elim0 r
  constructor
  · simp [emptyZero]
  · intro c
    exact Fin.elim0 c

theorem emptyZero_isCoarsest : emptyZero.IsCoarsest := by
  simp [emptyZero, IsCoarsest]

theorem emptyZero_isSymmetric : emptyZero.IsSymmetric := by
  rfl

/-- Simultaneously contract the same two parts in the rows and columns of a
symmetric square matrix partition. -/
noncomputable def symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) : MatrixPartition n n :=
  let Prow := P.rowContract hA hB hAB
  Prow.colContract
    (by
      simpa [Prow, IsSymmetric] using hP ▸ hA)
    (by
      simpa [Prow, IsSymmetric] using hP ▸ hB)
    hAB

@[simp] theorem rowParts_symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).rowParts =
      insert (A ∪ B) ((P.rowParts.erase A).erase B) := by
  simp [symContract]

@[simp] theorem colParts_symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).colParts =
      insert (A ∪ B) ((P.colParts.erase A).erase B) := by
  simp [symContract]

theorem isSymmetric_symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).IsSymmetric := by
  simp [IsSymmetric]
  rw [hP]

theorem isSymmetricContraction_symContract {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    P.IsSymmetricContraction (P.symContract hP hA hB hAB) := by
  exact ⟨A, hA, B, hB, hAB, by simp, by simp⟩

theorem rowParts_card_symContract_lt {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).rowParts.card < P.rowParts.card := by
  have hrowlt := MatrixPartition.rowParts_card_rowContract_lt P hA hB hAB
  simpa [symContract] using hrowlt

theorem colParts_card_symContract_lt {n : ℕ} (P : MatrixPartition n n)
    (hP : P.IsSymmetric)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B) :
    (P.symContract hP hA hB hAB).colParts.card < P.colParts.card := by
  let Prow : MatrixPartition n n := P.rowContract hA hB hAB
  have hAcol : A ∈ Prow.colParts := by
    simpa [Prow] using (hP ▸ hA)
  have hBcol : B ∈ Prow.colParts := by
    simpa [Prow] using (hP ▸ hB)
  have hcollt := MatrixPartition.colParts_card_colContract_lt Prow hAcol hBcol hAB
  simpa [symContract, Prow] using hcollt

end MatrixPartition

/-- A symmetric matrix contraction sequence of error value at most `d`. -/
structure SymmetricMatrixContractionSequence {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (d : ℕ) where
  /-- Number of paired contraction blocks. -/
  stepCount : ℕ
  /-- Symmetric partition at each time. -/
  partition : ℕ → MatrixPartition n n
  /-- Every partition has identical row and column families. -/
  symmetric : ∀ i, i ≤ stepCount → (partition i).IsSymmetric
  /-- The first partition is the singleton partition. -/
  starts : MatrixPartition.IsFinest (partition 0)
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Each step is a contraction together with its mirror about the diagonal. -/
  step_contracts :
    ∀ i, i < stepCount →
      MatrixPartition.IsSymmetricContraction (partition i) (partition (i + 1))
  /-- Every intermediate partition has error value at most `d`. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

/-- A square Boolean matrix has symmetric matrix twin-width at most `d` when it
has a symmetric contraction sequence of width `d`. -/
def SymmetricMatrixTwinWidthAtMost {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (d : ℕ) : Prop :=
  Nonempty (SymmetricMatrixContractionSequence M d)

/-- A symmetric contraction tail from a prescribed symmetric square partition
to a coarsest partition.  This is the tail object used to expand a bounded
refinement step into paired row/column contractions. -/
structure SymmetricMatrixContractionTail {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (d : ℕ)
    (P₀ : MatrixPartition n n) where
  /-- Number of remaining paired contraction blocks. -/
  stepCount : ℕ
  /-- Symmetric partition at each time. -/
  partition : ℕ → MatrixPartition n n
  /-- The first partition is the prescribed one. -/
  starts : partition 0 = P₀
  /-- Every partition in the tail is symmetric. -/
  symmetric : ∀ i, i ≤ stepCount → (partition i).IsSymmetric
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Consecutive partitions are paired symmetric contractions. -/
  step_contracts :
    ∀ i, i < stepCount →
      MatrixPartition.IsSymmetricContraction (partition i) (partition (i + 1))
  /-- Every partition in the tail has bounded error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) d

/-- A symmetric bounded-refinement partition sequence.  It is the square,
diagonal-mirrored version of the Lemma 8 input: every partition has the same
row and column families, each term boundedly refines the next, and every term
has error value at most `t`. -/
structure SymmetricBoundedErrorRefinementPartitionSequence {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (r t : ℕ) where
  /-- Number of coarse-graining steps. -/
  stepCount : ℕ
  /-- Symmetric partition at each time. -/
  partition : ℕ → MatrixPartition n n
  /-- The first partition is finest. -/
  starts : MatrixPartition.IsFinest (partition 0)
  /-- Every partition has the same row and column families. -/
  symmetric : ∀ i, i ≤ stepCount → (partition i).IsSymmetric
  /-- The final partition is coarsest. -/
  ends : MatrixPartition.IsCoarsest (partition stepCount)
  /-- Each partition boundedly refines the next. -/
  step_rrefines :
    ∀ i, i < stepCount → MatrixPartition.RRefines (partition i) (partition (i + 1)) r
  /-- Every partition in the sequence has bounded error value. -/
  errorValue_le : ∀ i, i ≤ stepCount → ErrorValueAtMost M (partition i) t

/-- Upgrade an ordinary bounded-refinement partition sequence to the symmetric
version once symmetry of every partition has been proved. -/
def symmetricBoundedErrorRefinement_of_boundedErrorRefinement
    {n r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (S : BoundedErrorRefinementPartitionSequence M r t)
    (hsym : ∀ i, i ≤ S.stepCount → (S.partition i).IsSymmetric) :
    SymmetricBoundedErrorRefinementPartitionSequence M r t where
  stepCount := S.stepCount
  partition := S.partition
  starts := S.starts
  symmetric := hsym
  ends := S.ends
  step_rrefines := S.step_rrefines
  errorValue_le := S.errorValue_le

/-- Section 5.8 profile refinement preserves symmetry for any bounded
mixed-value division sequence whose divisions are literally mirrored by the
same row/column interval division at every time.  The remaining symmetric
Lemma 13 task is therefore exactly to construct such a mirrored mixed-value
sequence. -/
theorem symmetricBoundedErrorRefinement_of_same_boundedMixedValue
    {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (hd : 0 < d)
    (S : BoundedMixedValueDivisionSequence M d)
    (hsame :
      ∀ i, i ≤ S.stepCount →
        ∃ k : ℕ, ∃ D : Division n (k + 1),
          S.division i = MatrixDivision.same D) :
    Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
      (2 * 2 ^ (d + 1)) (d * 2 ^ (d + 1))) := by
  classical
  let T : BoundedErrorRefinementPartitionSequence M
      (2 * Fintype.card Bool ^ (d + 1))
      (d * Fintype.card Bool ^ (d + 1)) :=
    boundedErrorRefinementPartitionSequence_of_boundedMixedValue
      (α := Bool) hd S
  have hsym : ∀ i, i ≤ T.stepCount → (T.partition i).IsSymmetric := by
    intro i hi
    by_cases hcur : i ≤ S.stepCount
    · rcases hsame i hcur with ⟨k, D, hD⟩
      simpa [T, boundedErrorRefinementPartitionSequence_of_boundedMixedValue,
        hcur, hD] using
        MatrixDivision.profilePartition_same_isSymmetric_of_isSymmetricMatrix
          (d := d) hM D
    · have hi_last : i = S.stepCount + 1 := by
        dsimp [T, boundedErrorRefinementPartitionSequence_of_boundedMixedValue] at hi
        omega
      subst i
      have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
      rcases hsame S.stepCount le_rfl with ⟨k, D, hD⟩
      simpa [T, boundedErrorRefinementPartitionSequence_of_boundedMixedValue,
        hnot, hD] using
        MatrixDivision.toPartition_isSymmetric_of_isSymmetric
          (MatrixDivision.same_isSymmetric D)
  refine ⟨?_⟩
  simpa using symmetricBoundedErrorRefinement_of_boundedErrorRefinement T hsym

/-- The bounded-refinement factor for one mirrored profile-refinement block.
This formalization composes the row-profile and column-profile refinements, so
the factor is the product of the two one-sided factors. -/
def symmetricProfileRefinementBlockBound (d : ℕ) : ℕ :=
  (2 * 2 ^ (d + 1)) * (2 * 2 ^ (d + 1))

/-- The profile-partition error bound over the Boolean alphabet. -/
def symmetricProfileErrorBound (d : ℕ) : ℕ :=
  d * 2 ^ (d + 1)

/-- A tail of mirrored mixed-value divisions.  Consecutive terms are not
ordinary one-sided fusions: each step has already been converted into the
profile-partition bounded-refinement block obtained by mirroring the cut. -/
structure SameMixedValueDivisionTail {n : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool) (d : ℕ)
    (D₀ : MatrixDivision n n) where
  /-- Number of remaining mirrored fusion blocks. -/
  stepCount : ℕ
  /-- Division at each time. -/
  division : ℕ → MatrixDivision n n
  /-- The first division is the prescribed one. -/
  starts : division 0 = D₀
  /-- Every division is literally the same row/column interval division. -/
  same :
    ∀ i, i ≤ stepCount →
      ∃ k : ℕ, ∃ D : Division n (k + 1),
        division i = MatrixDivision.same D
  /-- The final division is coarsest. -/
  ends : MatrixDivision.IsCoarsest (division stepCount)
  /-- Consecutive profile partitions satisfy the mirrored block refinement
  bound. -/
  step_rrefines :
    ∀ i, i < stepCount →
      MatrixPartition.RRefines
        (MatrixDivision.profilePartition (d := d) M (division i))
        (MatrixDivision.profilePartition (d := d) M (division (i + 1)))
        (symmetricProfileRefinementBlockBound d)
  /-- Every division has mixed value at most `d`. -/
  mixedValue_le :
    ∀ i, i ≤ stepCount →
      MatrixDivision.MixedValueAtMost M (division i) d

namespace SameMixedValueDivisionTail

/-- Empty mirrored mixed-value tail from a coarsest same division. -/
def nil {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {D₀ : MatrixDivision n n}
    (hsame : ∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D)
    (hcoarse : MatrixDivision.IsCoarsest D₀)
    (hmix : MatrixDivision.MixedValueAtMost M D₀ d) :
    SameMixedValueDivisionTail M d D₀ where
  stepCount := 0
  division := fun _ => D₀
  starts := rfl
  same := by intro i hi; simpa using hsame
  ends := hcoarse
  step_rrefines := by intro i hi; omega
  mixedValue_le := by intro i hi; simpa using hmix

/-- Prepend one mirrored fusion block to a same-division tail. -/
def cons {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {D₀ D₁ : MatrixDivision n n}
    (hsame₀ : ∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D)
    (hmix₀ : MatrixDivision.MixedValueAtMost M D₀ d)
    (hrefine :
      MatrixPartition.RRefines
        (MatrixDivision.profilePartition (d := d) M D₀)
        (MatrixDivision.profilePartition (d := d) M D₁)
        (symmetricProfileRefinementBlockBound d))
    (S : SameMixedValueDivisionTail M d D₁) :
    SameMixedValueDivisionTail M d D₀ where
  stepCount := S.stepCount + 1
  division := fun i =>
    match i with
    | 0 => D₀
    | j + 1 => S.division j
  starts := rfl
  same := by
    intro i hi
    cases i with
    | zero =>
        simpa using hsame₀
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.same j hj
  ends := by
    simpa using S.ends
  step_rrefines := by
    intro i hi
    cases i with
    | zero =>
        simpa [S.starts] using hrefine
    | succ j =>
        have hj : j < S.stepCount := by omega
        simpa using S.step_rrefines j hj
  mixedValue_le := by
    intro i hi
    cases i with
    | zero =>
        simpa using hmix₀
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.mixedValue_le j hj

end SameMixedValueDivisionTail

namespace SymmetricMatrixContractionSequence

/-- Relax the numerical error bound on a symmetric contraction sequence. -/
noncomputable def mono {n d e : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hde : d ≤ e) (S : SymmetricMatrixContractionSequence M d) :
    SymmetricMatrixContractionSequence M e where
  stepCount := S.stepCount
  partition := S.partition
  symmetric := S.symmetric
  starts := S.starts
  ends := S.ends
  step_contracts := S.step_contracts
  errorValue_le := by
    intro i hi
    exact MatrixPartition.errorValueAtMost_mono hde (S.errorValue_le i hi)

end SymmetricMatrixContractionSequence

namespace MatrixPartition

/-- Bounded refinement of finite partition families is transitive, with
multiplied bounds.  The partition hypotheses are the nonemptiness of fine
parts and disjointness of coarse parts, exactly as supplied by
`MatrixPartition`. -/
theorem partsRRefine_trans_of_partition {α : Type*} [DecidableEq α]
    {P Q R : Finset (Finset α)} {r s : ℕ}
    (hPnonempty : ∀ ⦃A⦄, A ∈ P → A.Nonempty)
    (hRdisjoint : ∀ ⦃A B⦄, A ∈ R → B ∈ R → A ≠ B → Disjoint A B)
    (hPQ : PartsRRefine P Q r) (hQR : PartsRRefine Q R s) :
    PartsRRefine P R (r * s) := by
  classical
  constructor
  · intro A hA
    rcases hPQ.1 hA with ⟨B, hB, hAB⟩
    rcases hQR.1 hB with ⟨C, hC, hBC⟩
    exact ⟨C, hC, fun x hx => hBC (hAB hx)⟩
  · intro C hC
    let baseInside : Finset (Finset α) := Q.filter fun B => B ⊆ C
    let candidates : Finset (Finset α) :=
      baseInside.biUnion fun B => P.filter fun A => A ⊆ B
    have hsubset : (P.filter fun A => A ⊆ C) ⊆ candidates := by
      intro A hAfilter
      have hA : A ∈ P := (Finset.mem_filter.mp hAfilter).1
      have hAC : A ⊆ C := (Finset.mem_filter.mp hAfilter).2
      rcases hPQ.1 hA with ⟨B, hB, hAB⟩
      rcases hQR.1 hB with ⟨C', hC', hBC'⟩
      have hC'C : C' = C := by
        rcases hPnonempty hA with ⟨x, hxA⟩
        have hxC' : x ∈ C' := hBC' (hAB hxA)
        have hxC : x ∈ C := hAC hxA
        by_contra hne
        exact Finset.disjoint_left.mp (hRdisjoint hC' hC hne) hxC' hxC
      have hBbase : B ∈ baseInside := by
        have hBC : B ⊆ C := by
          intro x hx
          simpa [hC'C] using hBC' hx
        simp [baseInside, hB, hBC]
      exact Finset.mem_biUnion.mpr
        ⟨B, hBbase, Finset.mem_filter.mpr ⟨hA, hAB⟩⟩
    have hcandidates :
        candidates.card ≤ baseInside.card * r := by
      unfold candidates
      refine Finset.card_biUnion_le_card_mul _ _ _ ?_
      intro B hBbase
      have hB : B ∈ Q := (Finset.mem_filter.mp hBbase).1
      exact hPQ.2 hB
    have hbase : baseInside.card ≤ s := by
      exact hQR.2 hC
    calc
      (P.filter fun A => A ⊆ C).card ≤ candidates.card :=
        Finset.card_le_card hsubset
      _ ≤ baseInside.card * r := hcandidates
      _ ≤ s * r := Nat.mul_le_mul_right r hbase
      _ = r * s := by rw [Nat.mul_comm]

/-- Matrix-partition bounded refinement is transitive, with multiplied
bounds. -/
theorem rrefines_trans {n m r s : ℕ}
    {P Q R : MatrixPartition n m}
    (hPQ : RRefines P Q r) (hQR : RRefines Q R s) :
    RRefines P R (r * s) := by
  constructor
  · exact partsRRefine_trans_of_partition
      P.row_nonempty R.row_disjoint hPQ.1 hQR.1
  · exact partsRRefine_trans_of_partition
      P.col_nonempty R.col_disjoint hPQ.2 hQR.2

theorem rrefines_profilePartition_same_fuse {n k d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {D : Division n (k + 2)}
    (hDmix : MatrixDivision.MixedValueAtMost M (MatrixDivision.same D) d)
    (i : Fin (k + 1))
    (hnew : colMixedValue M ((D.fuse i).part i) D ≤ d) :
    RRefines (MatrixDivision.profilePartition (d := d) M (MatrixDivision.same D))
      (MatrixDivision.profilePartition (d := d) M (MatrixDivision.same (D.fuse i)))
      ((2 * 2 ^ (d + 1)) * (2 * 2 ^ (d + 1))) := by
  classical
  let D₀ : MatrixDivision n n := MatrixDivision.same D
  have hrow : 0 < D₀.rowCuts := by
    dsimp [D₀, MatrixDivision.same]
    exact Nat.succ_pos k
  let i₀ : Fin D₀.rowCuts := i
  have hnewRow :
      colMixedValue M
        ((D₀.rowFuse hrow i₀).rowDiv.part
          ((finCongr
            (by simp [MatrixDivision.rowFuse]; omega :
              D₀.rowCuts = (D₀.rowFuse hrow i₀).rowCuts + 1)) i₀))
        (D₀.rowFuse hrow i₀).colDiv ≤ d := by
    simpa [D₀, i₀, MatrixDivision.same, MatrixDivision.rowFuse] using hnew
  have hDrowmix :
      MatrixDivision.MixedValueAtMost M (D₀.rowFuse hrow i₀) d :=
    MatrixDivision.mixedValueAtMost_rowFuse D₀ hDmix hrow i₀ hnewRow
  have hstep₁ :
      RRefines (MatrixDivision.profilePartition (d := d) M D₀)
        (MatrixDivision.profilePartition (d := d) M (D₀.rowFuse hrow i₀))
        (2 * Fintype.card Bool ^ (d + 1)) :=
    MatrixDivision.rrefines_profilePartition_of_hasExactFusion hDmix
      (Or.inl (MatrixDivision.hasRowFusion_rowFuse D₀ hrow i₀))
  let D₁ : MatrixDivision n n := D₀.rowFuse hrow i₀
  have hcol : 0 < D₁.colCuts := by
    dsimp [D₁, D₀, MatrixDivision.rowFuse, MatrixDivision.same]
    exact Nat.succ_pos k
  let j₀ : Fin D₁.colCuts := i
  have hstep₂ :
      RRefines (MatrixDivision.profilePartition (d := d) M D₁)
        (MatrixDivision.profilePartition (d := d) M (D₁.colFuse hcol j₀))
        (2 * Fintype.card Bool ^ (d + 1)) :=
    MatrixDivision.rrefines_profilePartition_of_hasExactFusion hDrowmix
      (Or.inr (MatrixDivision.hasColFusion_colFuse D₁ hcol j₀))
  have htrans := rrefines_trans hstep₁ hstep₂
  simpa [D₀, D₁, i₀, j₀, MatrixDivision.same, MatrixDivision.rowFuse,
    MatrixDivision.colFuse, Fintype.card_bool] using htrans

theorem rrefines_symContract {n r : ℕ}
    {P Q : MatrixPartition n n}
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPQ : RRefines P Q r)
    {A B : Finset (Fin n)} (hA : A ∈ P.rowParts) (hB : B ∈ P.rowParts)
    (hAB : A ≠ B)
    (hsame : ∃ C ∈ Q.rowParts, A ⊆ C ∧ B ⊆ C) :
    RRefines (P.symContract hP hA hB hAB) Q r := by
  classical
  let Prow : MatrixPartition n n := P.rowContract hA hB hAB
  have hrow : RRefines Prow Q r :=
    MatrixPartition.rrefines_rowContract hPQ hA hB hAB hsame
  have hAcol : A ∈ Prow.colParts := by
    simpa [Prow] using (hP ▸ hA)
  have hBcol : B ∈ Prow.colParts := by
    simpa [Prow] using (hP ▸ hB)
  have hsame_col : ∃ C ∈ Q.colParts, A ⊆ C ∧ B ⊆ C := by
    rcases hsame with ⟨C, hC, hAC, hBC⟩
    exact ⟨C, by simpa using (hQ ▸ hC), hAC, hBC⟩
  simpa [MatrixPartition.symContract, Prow] using
    MatrixPartition.rrefines_colContract hrow hAcol hBcol hAB hsame_col

end MatrixPartition

/-- Finite descent for mirrored mixed-value divisions, assuming the local good
cut oracle. -/
theorem exists_sameMixedValueDivisionTail_of_goodCut
    {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M)
    (hgood :
      ∀ D : MatrixDivision n n,
        MatrixDivision.MixedValueAtMost M D d →
          ¬ MatrixDivision.IsCoarsest D →
            MatrixDivision.HasGoodCut M D d) :
    ∀ D₀ : MatrixDivision n n,
      (∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D) →
        MatrixDivision.MixedValueAtMost M D₀ d →
          Nonempty (SameMixedValueDivisionTail M d D₀) := by
  classical
  intro D₀
  refine WellFounded.induction
    (C := fun D₀ : MatrixDivision n n =>
      (∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D) →
        MatrixDivision.MixedValueAtMost M D₀ d →
          Nonempty (SameMixedValueDivisionTail M d D₀))
    (InvImage.wf MatrixDivision.cutCount <| (Nat.lt_wfRel).2)
    D₀ ?_
  intro D₀ ih hsame hmix
  by_cases hcoarse : MatrixDivision.IsCoarsest D₀
  · exact ⟨SameMixedValueDivisionTail.nil hsame hcoarse hmix⟩
  · rcases hsame with ⟨k, D, rfl⟩
    cases k with
    | zero =>
        exact False.elim (hcoarse (by simp [MatrixDivision.same, MatrixDivision.IsCoarsest]))
    | succ k =>
        have hcurrent_same :
            ∃ q : ℕ, ∃ E : Division n (q + 1),
              MatrixDivision.same D = MatrixDivision.same E := ⟨k + 1, D, rfl⟩
        have hcut := hgood (MatrixDivision.same D) hmix hcoarse
        rcases hcut with hrowgood | hcolgood
        · rcases hrowgood with ⟨hrow, i, hnewRow⟩
          let iD : Fin (k + 1) :=
            (finCongr (by rfl : (MatrixDivision.same D).rowCuts = k + 1)) i
          have hnew :
              colMixedValue M ((D.fuse iD).part iD) D ≤ d := by
            simpa [iD] using
              MatrixDivision.colMixedValue_fused_le_of_goodRow_same
                (D := D) hrow i hnewRow
          let E : MatrixDivision n n := MatrixDivision.same (D.fuse iD)
          have hEmix : MatrixDivision.MixedValueAtMost M E d := by
            simpa [E] using
              MatrixDivision.mixedValueAtMost_same_fuse_of_colMixedValue_fused_le
                hM D hmix iD hnew
          have hEsame :
              ∃ q : ℕ, ∃ F : Division n (q + 1), E = MatrixDivision.same F :=
            ⟨k, D.fuse iD, rfl⟩
          have hlt :
              MatrixDivision.cutCount E < MatrixDivision.cutCount (MatrixDivision.same D) := by
            simp [E, MatrixDivision.same, MatrixDivision.cutCount]
            omega
          rcases ih E hlt hEsame hEmix with ⟨S⟩
          have hrefine :
              MatrixPartition.RRefines
                (MatrixDivision.profilePartition (d := d) M (MatrixDivision.same D))
                (MatrixDivision.profilePartition (d := d) M E)
                (symmetricProfileRefinementBlockBound d) := by
            simpa [E, symmetricProfileRefinementBlockBound] using
              MatrixPartition.rrefines_profilePartition_same_fuse
                (M := M) hmix iD hnew
          exact ⟨SameMixedValueDivisionTail.cons hcurrent_same hmix hrefine S⟩
        · rcases hcolgood with ⟨hcol, j, hnewCol⟩
          let jD : Fin (k + 1) :=
            (finCongr (by rfl : (MatrixDivision.same D).colCuts = k + 1)) j
          have hnew :
              colMixedValue M ((D.fuse jD).part jD) D ≤ d := by
            simpa [jD] using
              MatrixDivision.colMixedValue_fused_le_of_goodCol_same
                (hM := hM) (D := D) hcol j hnewCol
          let E : MatrixDivision n n := MatrixDivision.same (D.fuse jD)
          have hEmix : MatrixDivision.MixedValueAtMost M E d := by
            simpa [E] using
              MatrixDivision.mixedValueAtMost_same_fuse_of_colMixedValue_fused_le
                hM D hmix jD hnew
          have hEsame :
              ∃ q : ℕ, ∃ F : Division n (q + 1), E = MatrixDivision.same F :=
            ⟨k, D.fuse jD, rfl⟩
          have hlt :
              MatrixDivision.cutCount E < MatrixDivision.cutCount (MatrixDivision.same D) := by
            simp [E, MatrixDivision.same, MatrixDivision.cutCount]
            omega
          rcases ih E hlt hEsame hEmix with ⟨S⟩
          have hrefine :
              MatrixPartition.RRefines
                (MatrixDivision.profilePartition (d := d) M (MatrixDivision.same D))
                (MatrixDivision.profilePartition (d := d) M E)
                (symmetricProfileRefinementBlockBound d) := by
            simpa [E, symmetricProfileRefinementBlockBound] using
              MatrixPartition.rrefines_profilePartition_same_fuse
                (M := M) hmix jD hnew
          exact ⟨SameMixedValueDivisionTail.cons hcurrent_same hmix hrefine S⟩

/-- A mirrored mixed-value tail starting from a finest division gives a
symmetric bounded-error refinement sequence. -/
theorem symmetricBoundedErrorRefinement_of_sameMixedValueTail
    {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hM : IsSymmetricMatrix M) (hd : 0 < d)
    {D₀ : MatrixDivision n n}
    (hfinest : MatrixDivision.IsFinest D₀)
    (S : SameMixedValueDivisionTail M d D₀) :
    Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
      (symmetricProfileRefinementBlockBound d)
      (symmetricProfileErrorBound d)) := by
  classical
  refine ⟨?_⟩
  exact
    { stepCount := S.stepCount + 1
      partition := fun i =>
        if h : i ≤ S.stepCount then
          MatrixDivision.profilePartition (d := d) M (S.division i)
        else
          (S.division S.stepCount).toPartition
      starts := by
        have h0finest : MatrixDivision.IsFinest (S.division 0) := by
          simpa [S.starts] using hfinest
        exact MatrixDivision.profilePartition_isFinest_of_isFinest M h0finest
      symmetric := by
        intro i hi
        by_cases hcur : i ≤ S.stepCount
        · rcases S.same i hcur with ⟨k, D, hD⟩
          simp [hcur, hD,
            MatrixDivision.profilePartition_same_isSymmetric_of_isSymmetricMatrix
              (d := d) hM D]
        · have hi_last : i = S.stepCount + 1 := by omega
          subst i
          have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
          rcases S.same S.stepCount le_rfl with ⟨k, D, hD⟩
          simpa [hnot, hD] using
            MatrixDivision.toPartition_isSymmetric_of_isSymmetric
              (MatrixDivision.same_isSymmetric D)
      ends := by
        have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
        simp [hnot, MatrixDivision.toPartition_isCoarsest S.ends]
      step_rrefines := by
        intro i hi
        by_cases hlast : i = S.stepCount
        · subst i
          have hnext : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
          simp [hnext]
          exact MatrixPartition.rrefines_mono
            (by
              have hpow : 0 < 2 ^ (d + 1) :=
                pow_pos (by decide : 0 < 2) _
              have hleft : 2 ^ (d + 1) ≤ 2 * 2 ^ (d + 1) :=
                Nat.le_mul_of_pos_left (2 ^ (d + 1)) (by decide : 0 < 2)
              have hfactor_pos : 0 < 2 * 2 ^ (d + 1) :=
                Nat.mul_pos (by decide : 0 < 2) hpow
              calc
                Fintype.card Bool ^ (d + 1) = 2 ^ (d + 1) := by simp
                _ ≤ 2 * 2 ^ (d + 1) := hleft
                _ ≤ symmetricProfileRefinementBlockBound d := by
                  simpa [symmetricProfileRefinementBlockBound] using
                    Nat.le_mul_of_pos_right (2 * 2 ^ (d + 1)) hfactor_pos)
            (MatrixDivision.profilePartition_rrefines_toPartition
              (d := d) M (S.division S.stepCount))
        · have hiS : i < S.stepCount := by omega
          have hcur : i ≤ S.stepCount := by omega
          have hnext : i + 1 ≤ S.stepCount := by omega
          simpa [hcur, hnext] using S.step_rrefines i hiS
      errorValue_le := by
        intro i hi
        by_cases hcur : i ≤ S.stepCount
        · simp [hcur, symmetricProfileErrorBound]
          exact MatrixDivision.errorValueAtMost_profilePartition
            (S.mixedValue_le i hcur)
        · have hi_last : i = S.stepCount + 1 := by omega
          subst i
          have hnot : ¬ S.stepCount + 1 ≤ S.stepCount := by omega
          simp [hnot, symmetricProfileErrorBound]
          have hone :
              ErrorValueAtMost M (S.division S.stepCount).toPartition 1 :=
            errorValueAtMost_one_of_isCoarsest M
              (MatrixDivision.toPartition_isCoarsest S.ends)
          have hle : 1 ≤ d * 2 ^ (d + 1) := by
            have hpow : 0 < 2 ^ (d + 1) := pow_pos (by decide : 0 < 2) _
            exact Nat.succ_le_of_lt (Nat.mul_pos hd hpow)
          exact MatrixPartition.errorValueAtMost_mono hle hone }

namespace SymmetricMatrixContractionTail

/-- The empty symmetric contraction tail at a partition whose error is already
bounded. -/
def nil {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {P : MatrixPartition n n}
    (hP : P.IsSymmetric) (hErr : ErrorValueAtMost M P d)
    (hCoarse : MatrixPartition.IsCoarsest P) :
    SymmetricMatrixContractionTail M d P where
  stepCount := 0
  partition := fun _ => P
  starts := rfl
  symmetric := by intro i hi; simpa using hP
  ends := hCoarse
  step_contracts := by intro i hi; omega
  errorValue_le := by intro i hi; simpa using hErr

/-- Prepend one paired symmetric contraction to a symmetric contraction tail. -/
noncomputable def cons {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    {P Q : MatrixPartition n n}
    (hPQ : MatrixPartition.IsSymmetricContraction P Q)
    (hP : P.IsSymmetric)
    (hPerr : ErrorValueAtMost M P d)
    (S : SymmetricMatrixContractionTail M d Q) :
    SymmetricMatrixContractionTail M d P where
  stepCount := S.stepCount + 1
  partition := fun i =>
    match i with
    | 0 => P
    | j + 1 => S.partition j
  starts := rfl
  symmetric := by
    intro i hi
    cases i with
    | zero =>
        simpa using hP
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.symmetric j hj
  ends := by
    simpa using S.ends
  step_contracts := by
    intro i hi
    cases i with
    | zero =>
        simpa [S.starts] using hPQ
    | succ j =>
        have hj : j < S.stepCount := by omega
        simpa using S.step_contracts j hj
  errorValue_le := by
    intro i hi
    cases i with
    | zero =>
        simpa using hPerr
    | succ j =>
        have hj : j ≤ S.stepCount := by omega
        simpa using S.errorValue_le j hj

/-- Expand one symmetric bounded-refinement step into paired row/column
contractions before an already constructed symmetric tail from the coarse
partition. -/
theorem exists_of_symmetric_rrefines {n r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool} :
    ∀ (P Q : MatrixPartition n n),
      P.IsSymmetric →
      Q.IsSymmetric →
      MatrixPartition.RRefines P Q r →
      ErrorValueAtMost M Q t →
      SymmetricMatrixContractionTail M (r * t) Q →
      Nonempty (SymmetricMatrixContractionTail M (r * t) P) := by
  classical
  intro P
  refine WellFounded.induction
    (C := fun P : MatrixPartition n n =>
      ∀ Q : MatrixPartition n n,
        P.IsSymmetric →
        Q.IsSymmetric →
        MatrixPartition.RRefines P Q r →
        ErrorValueAtMost M Q t →
        SymmetricMatrixContractionTail M (r * t) Q →
        Nonempty (SymmetricMatrixContractionTail M (r * t) P))
    (InvImage.wf (fun P : MatrixPartition n n => P.rowParts.card)
      <| (Nat.lt_wfRel).2)
    P ?_
  intro P ih Q hP hQ hPQ hQerr T
  have hPerr : ErrorValueAtMost M P (r * t) :=
    MatrixPartition.errorValueAtMost_of_rrefines hPQ hQerr
  by_cases hrow : P.rowParts = Q.rowParts
  · have hcol : P.colParts = Q.colParts := by
      calc
        P.colParts = P.rowParts := hP.symm
        _ = Q.rowParts := hrow
        _ = Q.colParts := hQ
    have hPQeq : P = Q := MatrixPartition.ext_parts hrow hcol
    subst Q
    exact ⟨T⟩
  · rcases MatrixPartition.exists_two_rowParts_subset_of_refines_ne
      hPQ.1.1 hrow with
      ⟨C, hC, A, hA, B, hB, hAB, hAC, hBC⟩
    let P' : MatrixPartition n n := P.symContract hP hA hB hAB
    have hP'sym : P'.IsSymmetric :=
      MatrixPartition.isSymmetric_symContract P hP hA hB hAB
    have hP'Q : MatrixPartition.RRefines P' Q r :=
      MatrixPartition.rrefines_symContract hP hQ hPQ hA hB hAB
        ⟨C, hC, hAC, hBC⟩
    have hlt : P'.rowParts.card < P.rowParts.card := by
      simpa [P'] using
        MatrixPartition.rowParts_card_symContract_lt P hP hA hB hAB
    rcases ih P' hlt Q hP'sym hQ hP'Q hQerr T with ⟨T'⟩
    exact ⟨SymmetricMatrixContractionTail.cons
      (MatrixPartition.isSymmetricContraction_symContract P hP hA hB hAB)
      hP hPerr T'⟩

end SymmetricMatrixContractionTail

/-- Starting from any index in a symmetric bounded-refinement partition
sequence, the remaining suffix expands to paired symmetric contractions with
the multiplicative error bound `r * t`. -/
theorem exists_symmetricMatrixContractionTail_of_symmetricBoundedErrorRefinement
    {n r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hr : 0 < r)
    (S : SymmetricBoundedErrorRefinementPartitionSequence M r t) :
    ∀ i, i ≤ S.stepCount →
      Nonempty (SymmetricMatrixContractionTail M (r * t) (S.partition i)) := by
  classical
  intro i hi
  have ht_le : t ≤ r * t := by
    cases r with
    | zero => omega
    | succ r =>
        rw [Nat.succ_mul]
        exact Nat.le_add_left t (r * t)
  refine WellFounded.induction
    (C := fun a : {i // i ≤ S.stepCount} =>
      Nonempty (SymmetricMatrixContractionTail M (r * t) (S.partition a.1)))
    (InvImage.wf
      (fun a : {i // i ≤ S.stepCount} => S.stepCount - a.1)
      <| (Nat.lt_wfRel).2)
    ⟨i, hi⟩ ?_
  intro a ih
  by_cases hlast : a.1 = S.stepCount
  · have hsym : (S.partition a.1).IsSymmetric := by
      simpa [hlast] using S.symmetric S.stepCount le_rfl
    have herr : ErrorValueAtMost M (S.partition a.1) (r * t) := by
      exact MatrixPartition.errorValueAtMost_mono ht_le
        (by simpa [hlast] using S.errorValue_le S.stepCount le_rfl)
    have hcoarse : MatrixPartition.IsCoarsest (S.partition a.1) := by
      simpa [hlast] using S.ends
    exact ⟨SymmetricMatrixContractionTail.nil hsym herr hcoarse⟩
  · have hlt : a.1 < S.stepCount := lt_of_le_of_ne a.2 hlast
    let b : {i // i ≤ S.stepCount} := ⟨a.1 + 1, by omega⟩
    have hdec : S.stepCount - b.1 < S.stepCount - a.1 := by
      dsimp [b]
      omega
    rcases ih b hdec with ⟨Tnext⟩
    have hstep : MatrixPartition.RRefines
        (S.partition a.1) (S.partition (a.1 + 1)) r :=
      S.step_rrefines a.1 hlt
    have hnext_err : ErrorValueAtMost M (S.partition (a.1 + 1)) t :=
      S.errorValue_le (a.1 + 1) (by omega)
    exact SymmetricMatrixContractionTail.exists_of_symmetric_rrefines
      (S.partition a.1) (S.partition (a.1 + 1))
      (S.symmetric a.1 a.2)
      (S.symmetric (a.1 + 1) (by omega))
      hstep hnext_err Tnext

/-- Symmetric Lemma 8: a symmetric bounded-refinement partition sequence
expands into a symmetric matrix contraction sequence, using one paired
row/column contraction block for each fine merge. -/
theorem symmetricMatrixTwinWidthAtMost_of_symmetricBoundedErrorRefinement
    {n r t : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (hr : 0 < r)
    (S : Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M r t)) :
    SymmetricMatrixTwinWidthAtMost M (r * t) := by
  rcases S with ⟨S⟩
  rcases exists_symmetricMatrixContractionTail_of_symmetricBoundedErrorRefinement
      hr S 0 (Nat.zero_le S.stepCount) with ⟨T⟩
  exact ⟨{
    stepCount := T.stepCount
    partition := T.partition
    symmetric := T.symmetric
    starts := by
      rw [T.starts]
      exact S.starts
    ends := T.ends
    step_contracts := T.step_contracts
    errorValue_le := T.errorValue_le
  }⟩

/-- Symmetric Lemma 8 with the numerical parameters used by Theorem 10 for
Boolean matrices. -/
theorem symmetricMatrixTwinWidthAtMost_of_theorem10SymmetricErrorRefinement
    {n d : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (S : Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
      (2 * 2 ^ (d + 1)) (d * 2 ^ (d + 1)))) :
    SymmetricMatrixTwinWidthAtMost M
      (theorem10AlphabetErrorRefinementBound 2 d) := by
  have hr : 0 < 2 * 2 ^ (d + 1) := by
    exact Nat.mul_pos (by decide : 0 < 2) (pow_pos (by decide : 0 < 2) _)
  have h := symmetricMatrixTwinWidthAtMost_of_symmetricBoundedErrorRefinement
    (M := M) (r := 2 * 2 ^ (d + 1)) (t := d * 2 ^ (d + 1)) hr S
  have hmul :
      (2 * 2 ^ (d + 1)) * (d * 2 ^ (d + 1)) =
        theorem10AlphabetErrorRefinementBound 2 d := by
    unfold theorem10AlphabetErrorRefinementBound
    have hp : 2 ^ (d + 1) * 2 ^ (d + 1) = 2 ^ (2 * (d + 1)) := by
      rw [← pow_add]
      have hexp : d + 1 + (d + 1) = 2 * (d + 1) := by omega
      simp [hexp]
    calc
      (2 * 2 ^ (d + 1)) * (d * 2 ^ (d + 1))
          = 2 * d * (2 ^ (d + 1) * 2 ^ (d + 1)) := by ring
      _ = 2 * d * 2 ^ (2 * (d + 1)) := by rw [hp]
  simpa [hmul] using h

theorem SymmetricMatrixTwinWidthAtMost.mono {n d e : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) Bool}
    (h : SymmetricMatrixTwinWidthAtMost M d) (hde : d ≤ e) :
    SymmetricMatrixTwinWidthAtMost M e := by
  rcases h with ⟨S⟩
  exact ⟨S.mono hde⟩

theorem symmetricMatrixTwinWidthAtMost_zero (d : ℕ)
    (M : _root_.Matrix (Fin 0) (Fin 0) Bool) :
    SymmetricMatrixTwinWidthAtMost M d := by
  refine ⟨?_⟩
  exact
    { stepCount := 0
      partition := fun _ => MatrixPartition.emptyZero
      symmetric := by intro i hi; exact MatrixPartition.emptyZero_isSymmetric
      starts := MatrixPartition.emptyZero_isFinest
      ends := MatrixPartition.emptyZero_isCoarsest
      step_contracts := by intro i hi; omega
      errorValue_le := by
        intro i hi
        simp [MatrixPartition.emptyZero, ErrorValueAtMost, rowErrorSet, colErrorSet] }

/-- Empty square matrices have the degenerate symmetric bounded-refinement
sequence for any numerical parameters. -/
theorem symmetricBoundedErrorRefinement_zero (r t : ℕ)
    (M : _root_.Matrix (Fin 0) (Fin 0) Bool) :
    Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M r t) := by
  refine ⟨?_⟩
  exact
    { stepCount := 0
      partition := fun _ => MatrixPartition.emptyZero
      starts := MatrixPartition.emptyZero_isFinest
      symmetric := by intro i hi; exact MatrixPartition.emptyZero_isSymmetric
      ends := MatrixPartition.emptyZero_isCoarsest
      step_rrefines := by intro i hi; omega
      errorValue_le := by
        intro i hi
        simp [MatrixPartition.emptyZero, ErrorValueAtMost, rowErrorSet, colErrorSet] }

/-- The explicit width bound obtained by the mirrored symmetric construction
from a `t`-mixed-free square Boolean matrix.  The profile-refinement factor is
squared because each one-sided fusion is immediately mirrored across the
diagonal before the next mixed-value descent step. -/
def symmetricMatrixTwinWidthBoundOfMixedFree (t : ℕ) : ℕ :=
  let d := lemma13MixedValueBound marcusTardosConstant t
  symmetricProfileRefinementBlockBound d * symmetricProfileErrorBound d

/-- The finest positive square matrix division is a same row/column division. -/
theorem finest_same {n : ℕ} (hn : 0 < n) :
    ∃ k : ℕ, ∃ D : Division n (k + 1),
      MatrixDivision.finest hn hn = MatrixDivision.same D := by
  refine ⟨n - 1,
    Division.castIndex (by omega : n = (n - 1) + 1) (Division.singleton n), ?_⟩
  simp [MatrixDivision.finest, MatrixDivision.same]

/-- A mixed-free symmetric Boolean matrix admits the mirrored bounded-error
profile-refinement sequence.  This is the fully formalized symmetric version
of the Section 5.8 refinement construction: at every descent step the chosen
row cut or column cut is fused together with its mirror. -/
theorem symmetricBoundedErrorRefinement_of_mixedFree
    {n t : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool)
    (hM : IsSymmetricMatrix M)
    (hfree : MixedFree M t) :
    Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
      (symmetricProfileRefinementBlockBound
        (lemma13MixedValueBound marcusTardosConstant t))
      (symmetricProfileErrorBound
        (lemma13MixedValueBound marcusTardosConstant t))) := by
  classical
  by_cases hn0 : n = 0
  · subst n
    exact symmetricBoundedErrorRefinement_zero _ _ M
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let d : ℕ := lemma13MixedValueBound marcusTardosConstant t
    have htpos : 0 < t := by
      cases t with
      | zero =>
          exact False.elim (hfree (hasMixedMinor_zero M))
      | succ t =>
          exact Nat.succ_pos t
    have hd : 0 < d := by
      dsimp [d, lemma13MixedValueBound]
      exact Nat.mul_pos (by decide : 0 < 20)
        (IsMarcusTardosConstant.pos
          (isMarcusTardosConstant_marcusTardosConstant t) htpos)
    let D₀ : MatrixDivision n n := MatrixDivision.finest hn hn
    have hsame :
        ∃ k : ℕ, ∃ D : Division n (k + 1), D₀ = MatrixDivision.same D := by
      simpa [D₀] using finest_same hn
    have hfinest : MatrixDivision.IsFinest D₀ := by
      simpa [D₀] using MatrixDivision.finest_isFinest hn hn
    have hmix : MatrixDivision.MixedValueAtMost M D₀ d :=
      MatrixDivision.mixedValueAtMost_of_isFinest hfinest
    have hgood :
        ∀ D : MatrixDivision n n,
          MatrixDivision.MixedValueAtMost M D d →
            ¬ MatrixDivision.IsCoarsest D →
              MatrixDivision.HasGoodCut M D d := by
      simpa [d] using
        MatrixDivision.hasGoodCut_of_marcusTardos
          isMarcusTardosConstant_marcusTardosConstant M t hfree
    rcases exists_sameMixedValueDivisionTail_of_goodCut
        hM hgood D₀ hsame hmix with ⟨S⟩
    simpa [d] using
      symmetricBoundedErrorRefinement_of_sameMixedValueTail
        hM hd hfinest S

/-- The mirrored matrix construction turns a symmetric mixed-free Boolean
matrix into a paired row/column contraction sequence. -/
theorem symmetricMatrixTwinWidthAtMost_of_mixedFree
    {n t : ℕ}
    (M : _root_.Matrix (Fin n) (Fin n) Bool)
    (hM : IsSymmetricMatrix M)
    (hfree : MixedFree M t) :
    SymmetricMatrixTwinWidthAtMost M
      (symmetricMatrixTwinWidthBoundOfMixedFree t) := by
  classical
  let d : ℕ := lemma13MixedValueBound marcusTardosConstant t
  have hrefine :
      Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
        (symmetricProfileRefinementBlockBound d)
        (symmetricProfileErrorBound d)) := by
    simpa [d] using symmetricBoundedErrorRefinement_of_mixedFree M hM hfree
  have hr : 0 < symmetricProfileRefinementBlockBound d := by
    have hpow : 0 < 2 ^ (d + 1) := pow_pos (by decide : 0 < 2) _
    have hfactor : 0 < 2 * 2 ^ (d + 1) :=
      Nat.mul_pos (by decide : 0 < 2) hpow
    simp [symmetricProfileRefinementBlockBound, Nat.mul_pos hfactor hfactor]
  simpa [symmetricMatrixTwinWidthBoundOfMixedFree, d] using
    symmetricMatrixTwinWidthAtMost_of_symmetricBoundedErrorRefinement
      (M := M) (r := symmetricProfileRefinementBlockBound d)
      (t := symmetricProfileErrorBound d) hr hrefine

/-- The mirrored version of Theorem 10 needed by Theorem 14.

The symmetry hypothesis is essential: the paper applies this construction to
ordered adjacency matrices of undirected graphs, where every row operation can
be mirrored by the corresponding column operation without increasing the
mixed-value/error bound. -/
def SymmetricMatrixTwinWidthBoundedByMixedFree : Prop :=
  ∀ {n t : ℕ} (M : _root_.Matrix (Fin n) (Fin n) Bool),
    IsSymmetricMatrix M →
    MixedFree M t →
      SymmetricMatrixTwinWidthAtMost M
        (symmetricMatrixTwinWidthBoundOfMixedFree t)

/-- Symmetric refinement constructor needed for the mirrored matrix
construction in Theorem 14.  It states exactly the remaining refinement task:
from a symmetric `t`-mixed-free Boolean matrix, build the symmetric
bounded-refinement sequence with the Section 5.8 parameters. -/
def SymmetricMatrixErrorRefinementBoundedByMixedFree : Prop :=
  ∀ {n t : ℕ} (M : _root_.Matrix (Fin n) (Fin n) Bool),
    IsSymmetricMatrix M →
    MixedFree M t →
      Nonempty (SymmetricBoundedErrorRefinementPartitionSequence M
        (symmetricProfileRefinementBlockBound
          (lemma13MixedValueBound marcusTardosConstant t))
        (symmetricProfileErrorBound
          (lemma13MixedValueBound marcusTardosConstant t)))

/-- The mirrored matrix construction follows from the symmetric
bounded-refinement constructor by expanding every refinement step into paired
row/column contractions. -/
theorem symmetricMatrixTwinWidthBoundedByMixedFree_of_symmetricErrorRefinement
    (hrefine : SymmetricMatrixErrorRefinementBoundedByMixedFree) :
    SymmetricMatrixTwinWidthBoundedByMixedFree := by
  intro n t M hsym hfree
  let d : ℕ := lemma13MixedValueBound marcusTardosConstant t
  have hr : 0 < symmetricProfileRefinementBlockBound d := by
    have hpow : 0 < 2 ^ (d + 1) := pow_pos (by decide : 0 < 2) _
    have hfactor : 0 < 2 * 2 ^ (d + 1) :=
      Nat.mul_pos (by decide : 0 < 2) hpow
    simp [symmetricProfileRefinementBlockBound, Nat.mul_pos hfactor hfactor]
  simpa [symmetricMatrixTwinWidthBoundOfMixedFree, d] using
    symmetricMatrixTwinWidthAtMost_of_symmetricBoundedErrorRefinement
      (M := M) (r := symmetricProfileRefinementBlockBound d)
      (t := symmetricProfileErrorBound d) hr
      (by simpa [d] using hrefine M hsym hfree)

/-- Public theorem: the mirrored matrix construction is fully formalized for
finite square Boolean matrices. -/
theorem symmetricMatrixTwinWidthBoundedByMixedFree :
    SymmetricMatrixTwinWidthBoundedByMixedFree := by
  intro n t M hsym hfree
  exact symmetricMatrixTwinWidthAtMost_of_mixedFree M hsym hfree

end Matrix
end TwinWidth

/- ===== end Matrix/Symmetric.lean ===== -/

/- ===== begin Graph/Theorem14.lean ===== -/

/-
# Theorem 14: from mixed-free ordered adjacency matrices to graph twin-width

Theorem 14 of the first twin-width paper is the graph-facing consequence of
the symmetric version of the matrix Theorem 10 construction.  This file proves
the graph side of that bridge: once the symmetric construction supplies a
bounded graph partition sequence from a mixed-free ordered adjacency matrix,
the existing graph `twinWidth` definition obtains the advertised bound.
-/

namespace TwinWidth
namespace SimpleGraph

/-- Ordered adjacency matrices of undirected graphs are symmetric. -/
theorem orderedAdjacency_isSymmetricMatrix
    {V : Type*} {n : ℕ} [DecidableEq V]
    (G : _root_.SimpleGraph V) (σ : VertexOrder V n) :
    Matrix.IsSymmetricMatrix (Matrix.orderedAdjacency G σ) := by
  classical
  intro i j
  by_cases hij : G.Adj (σ.equiv i) (σ.equiv j)
  · have hji : G.Adj (σ.equiv j) (σ.equiv i) := G.symm hij
    simp [Matrix.orderedAdjacency, hij, hji]
  · have hji : ¬ G.Adj (σ.equiv j) (σ.equiv i) := fun h => hij (G.symm h)
    simp [Matrix.orderedAdjacency, hij, hji]

/-- Push a block of ordered matrix indices through a vertex order. -/
noncomputable def orderedImageBag {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (R : Finset (Fin n)) : Finset V :=
  by
    classical
    exact R.image σ.equiv

theorem orderedImageBag_injective {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) :
    Function.Injective (orderedImageBag σ) := by
  classical
  intro R S h
  ext r
  constructor
  · intro hr
    have hv : σ.equiv r ∈ orderedImageBag σ R := by
      simp [orderedImageBag, hr]
    rw [h] at hv
    rcases Finset.mem_image.mp hv with ⟨s, hs, hsv⟩
    have hsr : s = r := σ.equiv.injective hsv
    simpa [hsr] using hs
  · intro hs
    have hv : σ.equiv r ∈ orderedImageBag σ S := by
      simp [orderedImageBag, hs]
    rw [← h] at hv
    rcases Finset.mem_image.mp hv with ⟨s, hR, hsv⟩
    have hsr : s = r := σ.equiv.injective hsv
    simpa [hsr] using hR

theorem orderedImageBag_union {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (R S : Finset (Fin n)) :
    orderedImageBag σ (R ∪ S) = orderedImageBag σ R ∪ orderedImageBag σ S := by
  classical
  simp [orderedImageBag, Finset.image_union]

/-- The graph bag family induced by the row parts of a square matrix
partition in the chosen vertex order.  For symmetric matrix partitions the row
and column parts are the same family, so these are the graph bags used by the
mirrored Theorem 14 construction. -/
noncomputable def graphBagsOfMatrixPartition {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (P : Matrix.MatrixPartition n n) : Finset (Finset V) :=
  by
    classical
    exact P.rowParts.image (orderedImageBag σ)

theorem isBagPartition_graphBagsOfMatrixPartition {V : Type*} {n : ℕ}
    [DecidableEq V] (σ : VertexOrder V n) (P : Matrix.MatrixPartition n n) :
    IsBagPartition (graphBagsOfMatrixPartition σ P) := by
  classical
  constructor
  · intro A hA
    rcases Finset.mem_image.mp hA with ⟨R, hR, rfl⟩
    rcases P.row_nonempty hR with ⟨r, hr⟩
    exact ⟨σ.equiv r, by
      simp [orderedImageBag, hr]⟩
  constructor
  · intro A B hA hB hAB
    rcases Finset.mem_image.mp hA with ⟨R, hR, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨S, hS, rfl⟩
    have hRS : R ≠ S := by
      intro h
      apply hAB
      subst S
      rfl
    have hdis : Disjoint R S := P.row_disjoint hR hS hRS
    rw [Finset.disjoint_left]
    intro v hvR hvS
    rcases Finset.mem_image.mp hvR with ⟨r, hr, hrv⟩
    rcases Finset.mem_image.mp hvS with ⟨s, hs, hsv⟩
    have hrs : r = s := σ.equiv.injective (by
      rw [hrv, hsv])
    subst s
    exact (Finset.disjoint_left.mp hdis) hr hs
  · intro v
    rcases P.row_cover (σ.equiv.symm v) with ⟨R, hR, hr⟩
    refine ⟨orderedImageBag σ R, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
    · exact Finset.mem_image.mpr ⟨σ.equiv.symm v, hr, by simp⟩

theorem graphBagsOfMatrixPartition_card_le_of_row_card_le_one {V : Type*}
    {n : ℕ} [DecidableEq V] (σ : VertexOrder V n)
    {P : Matrix.MatrixPartition n n} (hP : P.rowParts.card ≤ 1) :
    (graphBagsOfMatrixPartition σ P).card ≤ 1 := by
  classical
  calc
    (graphBagsOfMatrixPartition σ P).card ≤ P.rowParts.card := by
      simp [graphBagsOfMatrixPartition]
      exact Finset.card_image_le
    _ ≤ 1 := hP

theorem graphBagsOfMatrixPartition_eq_singletonBags_of_isFinest {V : Type*}
    {n : ℕ} [Fintype V] [DecidableEq V]
    (σ : VertexOrder V n) {P : Matrix.MatrixPartition n n}
    (hP : Matrix.MatrixPartition.IsFinest P) :
    graphBagsOfMatrixPartition σ P = TrigraphState.singletonBags V := by
  classical
  ext A
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨R, hR, rfl⟩
    rcases hP.1 hR with ⟨r, rfl⟩
    exact Finset.mem_image.mpr ⟨σ.equiv r, by simp, by
      simp [orderedImageBag]⟩
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨v, _hv, rfl⟩
    let r : Fin n := σ.equiv.symm v
    refine Finset.mem_image.mpr ⟨({r} : Finset (Fin n)), hP.2.1 r, ?_⟩
    simp [orderedImageBag, r]

theorem isBagContraction_graphBagsOfMatrixPartition_of_isSymmetricContraction
    {V : Type*} {n : ℕ} [DecidableEq V] (σ : VertexOrder V n)
    {P Q : Matrix.MatrixPartition n n}
    (hPQ : Matrix.MatrixPartition.IsSymmetricContraction P Q) :
    IsBagContraction (graphBagsOfMatrixPartition σ P)
      (graphBagsOfMatrixPartition σ Q) := by
  classical
  rcases hPQ with ⟨R, hR, S, hS, hRS, hrow, _hcol⟩
  refine ⟨orderedImageBag σ R, ?_, orderedImageBag σ S, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
  · exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
  · intro h
    exact hRS ((orderedImageBag_injective σ) h)
  · rw [graphBagsOfMatrixPartition, graphBagsOfMatrixPartition, hrow]
    rw [Finset.image_insert]
    rw [Finset.image_erase (orderedImageBag_injective σ)]
    rw [Finset.image_erase (orderedImageBag_injective σ)]
    simp [orderedImageBag_union]

theorem homogeneousBetween_orderedImageBag_of_zoneConstant
    {V : Type*} {n : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {R C : Finset (Fin n)}
    (hR : R.Nonempty) (hC : C.Nonempty)
    (hconst :
      Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C) :
    HomogeneousBetween G (orderedImageBag σ R) (orderedImageBag σ C) := by
  classical
  rcases hR with ⟨r₀, hr₀⟩
  rcases hC with ⟨c₀, hc₀⟩
  by_cases hbase : G.Adj (σ.equiv r₀) (σ.equiv c₀)
  · refine Or.inl ?_
    intro a b ha hb
    rcases Finset.mem_image.mp ha with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨c, hc, rfl⟩
    have hEq := hconst hr₀ hr hc₀ hc
    have hdec : decide (G.Adj (σ.equiv r) (σ.equiv c)) = true := by
      simpa [Matrix.orderedAdjacency, hbase] using hEq.symm
    exact of_decide_eq_true hdec
  · refine Or.inr ?_
    intro a b ha hb hab
    rcases Finset.mem_image.mp ha with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨c, hc, rfl⟩
    have hEq := hconst hr₀ hr hc₀ hc
    have hdec : decide (G.Adj (σ.equiv r) (σ.equiv c)) = false := by
      simpa [Matrix.orderedAdjacency, hbase] using hEq.symm
    exact (of_decide_eq_false hdec) hab

theorem not_zoneConstant_of_partitionRedAdj_orderedImageBag
    {V : Type*} {n : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {R C : Finset (Fin n)}
    (hR : R.Nonempty) (hC : C.Nonempty)
    (hred : partitionRedAdj G (orderedImageBag σ R) (orderedImageBag σ C)) :
    ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C := by
  intro hconst
  exact hred.2 (homogeneousBetween_orderedImageBag_of_zoneConstant
    (G := G) σ hR hC hconst)

theorem partitionRedDegreeAtMost_graphBagsOfMatrixPartition
    {V : Type*} {n d : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {P : Matrix.MatrixPartition n n}
    (hsym : P.rowParts = P.colParts)
    (herror : Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G σ) P d) :
    PartitionRedDegreeAtMost G (graphBagsOfMatrixPartition σ P) d := by
  classical
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨R, hR, rfl⟩
  let graphErrors : Finset (Finset V) :=
    (P.rowParts.filter fun C =>
      ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C).image
        (orderedImageBag σ)
  have hsubset :
      (graphBagsOfMatrixPartition σ P).filter
          (fun B => partitionRedAdj G (orderedImageBag σ R) B) ⊆ graphErrors := by
    intro B hB
    rcases Finset.mem_filter.mp hB with ⟨hBbags, hred⟩
    rcases Finset.mem_image.mp hBbags with ⟨C, hC, rfl⟩
    have hnconst :
        ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C :=
      not_zoneConstant_of_partitionRedAdj_orderedImageBag
        (G := G) σ (P.row_nonempty hR) (P.row_nonempty hC) hred
    exact Finset.mem_image.mpr ⟨C, by simp [hnconst, hC], rfl⟩
  calc
    ((graphBagsOfMatrixPartition σ P).filter
        (fun B => partitionRedAdj G (orderedImageBag σ R) B)).card
        ≤ graphErrors.card := Finset.card_le_card hsubset
    _ ≤ (P.rowParts.filter fun C =>
          ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ) R C).card := by
        exact Finset.card_image_le
    _ = (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ) P R).card := by
        simp [Matrix.rowErrorSet, hsym]
    _ ≤ d := herror.1 hR

/-- A symmetric matrix contraction sequence induces the graph partition
sequence used by Theorem 14.

Rows and columns are the same family at every step.  Pushing each row block
through the chosen vertex order gives graph bags; each symmetric matrix
contraction is exactly the corresponding graph bag contraction, and the
complete/empty/non-homogeneous trigraph semantics agree with the contracted
matrix zones. -/
theorem graphPartitionSequence_of_symmetricMatrixContractionSequence
    {V : Type*} {n d : ℕ} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    (S : Matrix.SymmetricMatrixContractionSequence
      (Matrix.orderedAdjacency G σ) d) :
    Nonempty (GraphPartitionSequence G d) := by
  classical
  refine ⟨?_⟩
  refine
    { stepCount := S.stepCount
      bags := fun i => graphBagsOfMatrixPartition σ (S.partition i)
      isPartition := fun i _hi =>
        isBagPartition_graphBagsOfMatrixPartition σ (S.partition i)
      starts := ?_
      starts_state := ?_
      ends := ?_
      step_contracts := ?_
      redDegree_le := ?_ } <;> try intro i hi
  · exact graphBagsOfMatrixPartition_eq_singletonBags_of_isFinest σ S.starts
  · simpa [graphBagsOfMatrixPartition_eq_singletonBags_of_isFinest σ S.starts] using
      trigraphStateOfPartition_singletonBags_initial G
  · exact graphBagsOfMatrixPartition_card_le_of_row_card_le_one σ S.ends.1
  · exact isContractionStep_trigraphStateOfPartition_of_isBagContraction
      (isBagPartition_graphBagsOfMatrixPartition σ (S.partition i))
      (isBagPartition_graphBagsOfMatrixPartition σ (S.partition (i + 1)))
      (isBagContraction_graphBagsOfMatrixPartition_of_isSymmetricContraction
        σ (S.step_contracts i hi))
  · exact partitionRedDegreeAtMost_graphBagsOfMatrixPartition
      (G := G) σ (S.symmetric i hi) (S.errorValue_le i hi)

theorem graphPartitionSequence_of_symmetricMatrixTwinWidthAtMost
    {V : Type*} {n d : ℕ} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    (h :
      Matrix.SymmetricMatrixTwinWidthAtMost
        (Matrix.orderedAdjacency G σ) d) :
    Nonempty (GraphPartitionSequence G d) := by
  rcases h with ⟨S⟩
  exact graphPartitionSequence_of_symmetricMatrixContractionSequence σ S

/-- The explicit graph-facing bound obtained by applying the formalized
mirrored Theorem 10 refinement to a Boolean `t`-mixed-free ordered adjacency
matrix. -/
def theorem14MixedFreeTwinWidthBound (t : ℕ) : ℕ :=
  Matrix.symmetricMatrixTwinWidthBoundOfMixedFree t

@[simp] theorem theorem14MixedFreeTwinWidthBound_eq (t : ℕ) :
    theorem14MixedFreeTwinWidthBound t =
      Matrix.symmetricMatrixTwinWidthBoundOfMixedFree t := by
  rfl

/-- Theorem 14 in sequence-constructor form.

If the symmetric matrix construction turns a `t`-mixed-free ordered adjacency
matrix into a graph partition sequence of the Theorem 14 width, then the graph
has twin-width at most that width. -/
theorem theorem14_twinWidth_le_of_mixedFree_order_of_partitionSequence
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {n t : ℕ} {σ : VertexOrder V n}
    (hconstruct :
      Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
        Nonempty (GraphPartitionSequence G (theorem14MixedFreeTwinWidthBound t)))
    (hfree : Matrix.MixedFree (Matrix.orderedAdjacency G σ) t) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound t := by
  rcases hconstruct hfree with ⟨S⟩
  exact twinWidth_le_of_hasTwinWidthAtMost
    (GraphPartitionSequence.hasTwinWidthAtMost_of_graphPartitionSequence S)

/-- Ordered-adjacency mixed-number form of Theorem 14.

It suffices to build the symmetric graph partition sequence for the first
mixed-minor order that the ordered adjacency matrix avoids. -/
theorem theorem14_twinWidth_le_orderedAdjacencyMixedNumber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (σ : VertexOrder V (Fintype.card V))
    (hconstruct :
      ∀ t : ℕ,
        Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
          Nonempty (GraphPartitionSequence G (theorem14MixedFreeTwinWidthBound t))) :
    twinWidth G ≤
      theorem14MixedFreeTwinWidthBound
        (Matrix.orderedAdjacencyMixedNumber G σ + 1) := by
  let k := Matrix.orderedAdjacencyMixedNumber G σ
  have hfree : Matrix.MixedFree (Matrix.orderedAdjacency G σ) (k + 1) := by
    simpa [k, Matrix.orderedAdjacencyMixedNumber] using
      Matrix.not_hasMixedMinor_succ_matrixMixedNumber (Matrix.orderedAdjacency G σ)
  simpa [k] using
    theorem14_twinWidth_le_of_mixedFree_order_of_partitionSequence
      (G := G) (σ := σ) (t := k + 1) (hconstruct (k + 1)) hfree

/-- Graph mixed-minor-number form of Theorem 14.

Choose an order realizing `mixedMinorNumber`; the avoided order is then one
more than that minimum, which matches `theorem10MatrixTwinWidthBound`. -/
theorem theorem14_twinWidth_le_mixedMinorNumber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    (hconstruct :
      ∀ σ : VertexOrder V (Fintype.card V), ∀ t : ℕ,
        Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
          Nonempty (GraphPartitionSequence G (theorem14MixedFreeTwinWidthBound t))) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤
        theorem14MixedFreeTwinWidthBound
          (Matrix.orderedAdjacencyMixedNumber G σ + 1) :=
      theorem14_twinWidth_le_orderedAdjacencyMixedNumber G σ (hconstruct σ)
    _ = theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by rw [hσ]

/-- Theorem 14 from the mirrored matrix construction.

The first hypothesis is the symmetric matrix version of Theorem 10: mirror each
row contraction by its column contraction, and mirror each column contraction by
its row contraction.  The second hypothesis translates the resulting symmetric
matrix partition sequence for an ordered adjacency matrix into the graph
partition sequence used by `twinWidth`. -/
theorem theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixBridge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    (hmatrix :
      ∀ σ : VertexOrder V (Fintype.card V), ∀ t : ℕ,
        Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
          Matrix.SymmetricMatrixTwinWidthAtMost (Matrix.orderedAdjacency G σ)
            (theorem14MixedFreeTwinWidthBound t))
    (hbridge :
      ∀ σ : VertexOrder V (Fintype.card V), ∀ d : ℕ,
        Matrix.SymmetricMatrixTwinWidthAtMost (Matrix.orderedAdjacency G σ) d →
          Nonempty (GraphPartitionSequence G d)) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by
  apply theorem14_twinWidth_le_mixedMinorNumber
  intro σ t hfree
  exact hbridge σ (theorem14MixedFreeTwinWidthBound t) (hmatrix σ t hfree)

/-- Theorem 14 from the mirrored symmetric matrix construction.

The graph interpretation of symmetric matrix contractions is proved in this
file, so the only external mathematical input here is the symmetric matrix
construction itself: every mixed-free ordered adjacency matrix has a bounded
symmetric matrix contraction sequence. -/
theorem theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixConstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    (hmatrix :
      ∀ σ : VertexOrder V (Fintype.card V), ∀ t : ℕ,
        Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
          Matrix.SymmetricMatrixTwinWidthAtMost (Matrix.orderedAdjacency G σ)
            (theorem14MixedFreeTwinWidthBound t)) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by
  exact theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixBridge
    G hmatrix (fun σ _d h => graphPartitionSequence_of_symmetricMatrixTwinWidthAtMost σ h)

/-- Theorem 14 with the mirrored matrix construction discharged by
`Matrix.Symmetric`: graph twin-width is bounded by the explicit mixed-free
bound at one more than the graph mixed minor number. -/
theorem theorem14_twinWidth_le_mixedMinorNumber_explicit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by
  exact theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixConstruction G
    (fun σ t hfree => by
      simpa [theorem14MixedFreeTwinWidthBound] using
        Matrix.symmetricMatrixTwinWidthBoundedByMixedFree
          (Matrix.orderedAdjacency G σ)
          (orderedAdjacency_isSymmetricMatrix G σ) hfree)

end SimpleGraph
end TwinWidth

/- ===== end Graph/Theorem14.lean ===== -/

/- ===== begin Equivalence/MixedToTwinWidth.lean ===== -/

/-
# Mixed minor number to twin-width

This module records the opposite directional bound needed for functional
equivalence.  Section 5 gives an explicit elementary bound via the
Marcus-Tardos theorem, Lemma 13, and the finite-alphabet profile refinement.
-/

namespace TwinWidth
namespace SimpleGraph

/-- The proposition that twin-width is bounded by a numerical function of mixed
minor number. -/
def TwinWidthBoundedByMixedMinorNumber : Prop :=
  ∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
    twinWidth G ≤ f (mixedMinorNumber G)

/-- The concrete elementary bound supplied by the mirrored Boolean
Theorem 14 construction.  If an ordered adjacency matrix has mixed number `k`,
then it is `(k+1)`-mixed-free, so the graph-facing witness is the symmetric
mixed-free bound at `k+1`. -/
def twinWidthBoundOfMixedMinorNumber (k : ℕ) : ℕ :=
  theorem14MixedFreeTwinWidthBound (k + 1)

/-- Matrix-level ordered-adjacency form of the mixed-to-twin-width direction.

This is the graph-facing bridge required after the matrix theorem: the
twin-width of the graph represented by an ordered adjacency matrix is bounded
by a function of that matrix's mixed number. -/
def TwinWidthBoundedByOrderedAdjacencyMixedNumber (f : ℕ → ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
    (σ : VertexOrder V (Fintype.card V)),
      twinWidth G ≤ f (Matrix.orderedAdjacencyMixedNumber G σ)

/-- Passing from a bound for every ordered adjacency matrix to the graph mixed
minor number, using an order that realizes the minimum in `mixedMinorNumber`. -/
theorem twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyBound
    {f : ℕ → ℕ}
    (h : TwinWidthBoundedByOrderedAdjacencyMixedNumber f) :
    TwinWidthBoundedByMixedMinorNumber := by
  refine ⟨f, ?_⟩
  intro V _ _ G
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤ f (Matrix.orderedAdjacencyMixedNumber G σ) := h G σ
    _ = f (mixedMinorNumber G) := by rw [hσ]

/-- The concrete mixed-minor-to-twin-width direction, assuming the Section 5
ordered-adjacency matrix bound with the chosen elementary witness. -/
def TwinWidthBoundedByOrderedAdjacencyMixedNumberExplicit : Prop :=
  TwinWidthBoundedByOrderedAdjacencyMixedNumber twinWidthBoundOfMixedMinorNumber

/-- One functional-equivalence direction with the explicit mixed-minor witness,
obtained from the ordered-adjacency matrix bound. -/
theorem twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyExplicitBound
    (h : TwinWidthBoundedByOrderedAdjacencyMixedNumberExplicit) :
    TwinWidthBoundedByMixedMinorNumber :=
  twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyBound h

/-- The completed mixed-minor-to-twin-width direction, obtained from the
formalized mirrored Theorem 14 construction. -/
theorem twinWidth_le_twinWidthBoundOfMixedMinorNumber
    {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G) := by
  simpa [twinWidthBoundOfMixedMinorNumber] using
    theorem14_twinWidth_le_mixedMinorNumber_explicit G

/-- The completed graph-parameter direction from mixed minor number to
twin-width. -/
theorem twinWidthBoundedByMixedMinorNumber :
    TwinWidthBoundedByMixedMinorNumber := by
  refine ⟨twinWidthBoundOfMixedMinorNumber, ?_⟩
  intro V _ _ G
  exact twinWidth_le_twinWidthBoundOfMixedMinorNumber G

/-- Legacy ordered-adjacency Theorem 14 reduction: a bound for every ordered
adjacency matrix gives the graph-level bound by choosing an order that realizes
`mixedMinorNumber`. -/
theorem twin_width_le_theorem14_bound_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
        (σ : VertexOrder V (Fintype.card V)),
          twinWidth G ≤
            theorem14MixedFreeTwinWidthBound
              (Matrix.orderedAdjacencyMixedNumber G σ + 1)) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G) := by
  intro V _ _ G
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound
        (Matrix.orderedAdjacencyMixedNumber G σ + 1) := h G σ
    _ = twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G) := by
        rw [hσ]
        rfl

/-- Legacy double-exponential reduction retained as a plain consequence of any
ordered-adjacency bound with that numerical witness.  The main contract uses
the explicit Theorem 10 bound above. -/
theorem twin_width_le_double_exponential_mixed_minor_number_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
        (σ : VertexOrder V (Fintype.card V)),
          twinWidth G ≤ 2 ^ (2 ^ (Matrix.orderedAdjacencyMixedNumber G σ + 1))) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      twinWidth G ≤ 2 ^ (2 ^ (mixedMinorNumber G + 1)) := by
  intro V _ _ G
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤ 2 ^ (2 ^ (Matrix.orderedAdjacencyMixedNumber G σ + 1)) := h G σ
    _ = 2 ^ (2 ^ (mixedMinorNumber G + 1)) := by rw [hσ]

end SimpleGraph
end TwinWidth

/- ===== end Equivalence/MixedToTwinWidth.lean ===== -/

/- ===== begin Graph/TwinDecomposition.lean ===== -/

/-
# Twin-decomposition orders

The left-to-right order on the leaves of a contraction tree is the order used
to turn a graph `d`-sequence into a `d`-twin-ordered adjacency matrix.  This
file isolates the exact graph/matrix interface supplied by that construction:
a `TwinDecomposition` records the leaf order together with the matrix
twin-orderedness proof for the ordered adjacency matrix.
-/

namespace TwinWidth
namespace SimpleGraph

/-- Reindexing a division twice is the same as reindexing by the composed
cardinality equality. -/
theorem Division.castIndex_castIndex
    {n k l q : ℕ} (hkl : k = l) (hlq : l = q) (D : Division n k) :
    Division.castIndex hlq (Division.castIndex hkl D) =
      Division.castIndex (hkl.trans hlq) D := by
  subst l
  subst q
  rfl

@[simp] theorem Division.castIndex_proof_irrel
    {n k l : ℕ} (h h' : k = l) (D : Division n k) :
    Division.castIndex h D = Division.castIndex h' D := by
  subst l
  rfl

/-- Heterogeneous proof irrelevance for reindexing a fixed division. -/
theorem Division.castIndex_heq
    {n k l l' : ℕ} (h : k = l) (h' : k = l') (D : Division n k) :
    Division.castIndex h D ≍ Division.castIndex h' D := by
  subst l
  subst l'
  rfl

/-- Extensionality for matrix divisions with dependent division fields. -/
theorem matrixDivision_ext_heq {n m : ℕ}
    {D E : Matrix.MatrixDivision n m}
    (hrowCuts : D.rowCuts = E.rowCuts)
    (hcolCuts : D.colCuts = E.colCuts)
    (hrowDiv : D.rowDiv ≍ E.rowDiv)
    (hcolDiv : D.colDiv ≍ E.colDiv) :
    D = E := by
  cases D
  cases E
  simp at hrowCuts hcolCuts
  subst hrowCuts
  subst hcolCuts
  cases hrowDiv
  cases hcolDiv
  rfl

/-- Fin indices with the same value are heterogeneously equal after identifying
their ambient bounds. -/
theorem fin_heq_of_val_eq {n n' : ℕ} (hn : n = n')
    {i : Fin n} {j : Fin n'} (hval : i.1 = j.1) :
    i ≍ j := by
  subst n'
  exact heq_of_eq (Fin.ext hval)

/-- Pull a graph bag back to row/column indices in a vertex order. -/
noncomputable def orderedPreimageBag {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (A : Finset V) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun i => σ.equiv i ∈ A

@[simp] theorem mem_orderedPreimageBag {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (A : Finset V) (i : Fin n) :
    i ∈ orderedPreimageBag σ A ↔ σ.equiv i ∈ A := by
  classical
  simp [orderedPreimageBag]

theorem orderedImageBag_orderedPreimageBag {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (A : Finset V) :
    orderedImageBag σ (orderedPreimageBag σ A) = A := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    simpa using hi
  · intro hv
    refine Finset.mem_image.mpr ⟨σ.equiv.symm v, ?_, by simp⟩
    simp [orderedPreimageBag, hv]

theorem orderedPreimageBag_injective {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) :
    Function.Injective (orderedPreimageBag σ) := by
  intro A B h
  have hA := orderedImageBag_orderedPreimageBag σ A
  have hB := orderedImageBag_orderedPreimageBag σ B
  rw [← hA, h, hB]

theorem orderedPreimageBag_nonempty {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) {A : Finset V} :
    A.Nonempty → (orderedPreimageBag σ A).Nonempty := by
  classical
  rintro ⟨v, hv⟩
  exact ⟨σ.equiv.symm v, by simp [orderedPreimageBag, hv]⟩

theorem orderedPreimageBag_disjoint {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) {A B : Finset V} :
    Disjoint A B → Disjoint (orderedPreimageBag σ A) (orderedPreimageBag σ B) := by
  classical
  intro hAB
  rw [Finset.disjoint_left]
  intro i hiA hiB
  exact (Finset.disjoint_left.mp hAB) (by simpa using hiA) (by simpa using hiB)

@[simp] theorem orderedPreimageBag_union {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (A B : Finset V) :
    orderedPreimageBag σ (A ∪ B) =
      orderedPreimageBag σ A ∪ orderedPreimageBag σ B := by
  classical
  ext i
  simp [orderedPreimageBag]

@[simp] theorem orderedPreimageBag_singleton {V : Type*} {n : ℕ} [DecidableEq V]
    (σ : VertexOrder V n) (i : Fin n) :
    orderedPreimageBag σ ({σ.equiv i} : Finset V) = {i} := by
  classical
  ext j
  simp [orderedPreimageBag]

theorem zoneConstant_orderedAdjacency_of_homogeneousBetween_preimage
    {V : Type*} {n : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {A B : Finset V}
    (hhom : HomogeneousBetween G A B) :
    Matrix.ZoneConstant (Matrix.orderedAdjacency G σ)
      (orderedPreimageBag σ A) (orderedPreimageBag σ B) := by
  classical
  intro r₁ r₂ hr₁ hr₂ c₁ c₂ hc₁ hc₂
  rcases hhom with hcomp | hemp
  · have h₁ : G.Adj (σ.equiv r₁) (σ.equiv c₁) := hcomp (by simpa using hr₁) (by simpa using hc₁)
    have h₂ : G.Adj (σ.equiv r₂) (σ.equiv c₂) := hcomp (by simpa using hr₂) (by simpa using hc₂)
    simp [Matrix.orderedAdjacency, h₁, h₂]
  · have h₁ : ¬ G.Adj (σ.equiv r₁) (σ.equiv c₁) :=
      hemp (by simpa using hr₁) (by simpa using hc₁)
    have h₂ : ¬ G.Adj (σ.equiv r₂) (σ.equiv c₂) :=
      hemp (by simpa using hr₂) (by simpa using hc₂)
    simp [Matrix.orderedAdjacency, h₁, h₂]

theorem nonconstant_preimage_imp_red_or_same
    {V : Type*} {n : ℕ} [DecidableEq V]
    {G : _root_.SimpleGraph V} (σ : VertexOrder V n)
    {T : TrigraphState V} (hsem : IsSemanticState G T)
    {A B : Finset V} (hA : A ∈ T.bags) (hB : B ∈ T.bags)
    (hnon :
      ¬ Matrix.ZoneConstant (Matrix.orderedAdjacency G σ)
        (orderedPreimageBag σ A) (orderedPreimageBag σ B)) :
    T.redAdj A B ∨ B = A := by
  classical
  by_cases hBA : B = A
  · exact Or.inr hBA
  · left
    have hred : partitionRedAdj G A B := by
      refine ⟨?_, ?_⟩
      · exact fun hAB => hBA hAB.symm
      · intro hhom
        exact hnon (zoneConstant_orderedAdjacency_of_homogeneousBetween_preimage σ hhom)
    exact (hsem.1 hA hB).2 hred

namespace ContractionSequence

/-- The symmetric matrix partition obtained from a trigraph state by pulling
each graph bag back through the leaf order. -/
noncomputable def matrixPartitionOfState
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) (i : ℕ) : Matrix.MatrixPartition
      (Fintype.card V) (Fintype.card V) where
  rowParts := (S.state i).bags.image (orderedPreimageBag σ)
  row_nonempty := by
    classical
    intro R hR
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    exact orderedPreimageBag_nonempty σ ((S.state i).bag_nonempty hA)
  row_disjoint := by
    classical
    intro R Q hR hQ hRQ
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hQ with ⟨B, hB, rfl⟩
    have hAB : A ≠ B := by
      intro h
      subst B
      exact hRQ rfl
    exact orderedPreimageBag_disjoint σ ((S.state i).bag_disjoint hA hB hAB)
  row_cover := by
    classical
    intro r
    rcases (S.state i).bag_cover (σ.equiv r) with ⟨A, hA, hrA⟩
    refine ⟨orderedPreimageBag σ A, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    · simp [orderedPreimageBag, hrA]
  colParts := (S.state i).bags.image (orderedPreimageBag σ)
  col_nonempty := by
    classical
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    exact orderedPreimageBag_nonempty σ ((S.state i).bag_nonempty hA)
  col_disjoint := by
    classical
    intro C D hC hD hCD
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨B, hB, rfl⟩
    have hAB : A ≠ B := by
      intro h
      subst B
      exact hCD rfl
    exact orderedPreimageBag_disjoint σ ((S.state i).bag_disjoint hA hB hAB)
  col_cover := by
    classical
    intro c
    rcases (S.state i).bag_cover (σ.equiv c) with ⟨A, hA, hcA⟩
    refine ⟨orderedPreimageBag σ A, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    · simp [orderedPreimageBag, hcA]

@[simp] theorem rowParts_matrixPartitionOfState
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) (i : ℕ) :
    (S.matrixPartitionOfState σ i).rowParts =
      (S.state i).bags.image (orderedPreimageBag σ) := rfl

@[simp] theorem colParts_matrixPartitionOfState
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) (i : ℕ) :
    (S.matrixPartitionOfState σ i).colParts =
      (S.state i).bags.image (orderedPreimageBag σ) := rfl

/-- The rectangular matrix partition obtained by taking row bags from one
trigraph state and column bags from another.  This is used for the intermediate
matrix division after a row fusion has been mirrored but before the matching
column fusion has been performed. -/
noncomputable def matrixPartitionOfTwoStates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V))
    (rowTime colTime : ℕ) : Matrix.MatrixPartition
      (Fintype.card V) (Fintype.card V) where
  rowParts := (S.state rowTime).bags.image (orderedPreimageBag σ)
  row_nonempty := by
    classical
    intro R hR
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    exact orderedPreimageBag_nonempty σ ((S.state rowTime).bag_nonempty hA)
  row_disjoint := by
    classical
    intro R Q hR hQ hRQ
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hQ with ⟨B, hB, rfl⟩
    have hAB : A ≠ B := by
      intro h
      subst B
      exact hRQ rfl
    exact orderedPreimageBag_disjoint σ ((S.state rowTime).bag_disjoint hA hB hAB)
  row_cover := by
    classical
    intro r
    rcases (S.state rowTime).bag_cover (σ.equiv r) with ⟨A, hA, hrA⟩
    refine ⟨orderedPreimageBag σ A, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    · simp [orderedPreimageBag, hrA]
  colParts := (S.state colTime).bags.image (orderedPreimageBag σ)
  col_nonempty := by
    classical
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    exact orderedPreimageBag_nonempty σ ((S.state colTime).bag_nonempty hA)
  col_disjoint := by
    classical
    intro C D hC hD hCD
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨B, hB, rfl⟩
    have hAB : A ≠ B := by
      intro h
      subst B
      exact hCD rfl
    exact orderedPreimageBag_disjoint σ ((S.state colTime).bag_disjoint hA hB hAB)
  col_cover := by
    classical
    intro c
    rcases (S.state colTime).bag_cover (σ.equiv c) with ⟨A, hA, hcA⟩
    refine ⟨orderedPreimageBag σ A, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    · simp [orderedPreimageBag, hcA]

@[simp] theorem rowParts_matrixPartitionOfTwoStates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V))
    (rowTime colTime : ℕ) :
    (S.matrixPartitionOfTwoStates σ rowTime colTime).rowParts =
      (S.state rowTime).bags.image (orderedPreimageBag σ) := rfl

@[simp] theorem colParts_matrixPartitionOfTwoStates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V))
    (rowTime colTime : ℕ) :
    (S.matrixPartitionOfTwoStates σ rowTime colTime).colParts =
      (S.state colTime).bags.image (orderedPreimageBag σ) := rfl

/-- Taking the same state on both axes gives the symmetric state partition. -/
theorem matrixPartitionOfTwoStates_self_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) (i : ℕ) :
    S.matrixPartitionOfTwoStates σ i i = S.matrixPartitionOfState σ i := by
  apply Matrix.MatrixPartition.ext_parts <;> rfl

theorem matrixPartitionOfState_errorValueAtMost
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V)) {i : ℕ} (hi : i ≤ S.stepCount) :
    Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G σ)
      (S.matrixPartitionOfState σ i) (d + 1) := by
  classical
  have hsem := S.isSemanticState i hi
  constructor
  · intro R hR
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    let target : Finset (Finset V) :=
      ((S.state i).bags.filter fun B => (S.state i).redAdj A B) ∪ {A}
    have hsubset :
        (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ) ⊆ target := by
      intro B hB
      rcases Finset.mem_image.mp hB with ⟨C, hCerr, rfl⟩
      rcases Finset.mem_filter.mp hCerr with ⟨hCpart, hnon⟩
      rcases Finset.mem_image.mp hCpart with ⟨B₀, hB₀, rfl⟩
      have hred_or :=
        nonconstant_preimage_imp_red_or_same σ hsem hA hB₀ hnon
      rw [orderedImageBag_orderedPreimageBag]
      rcases hred_or with hred | hs
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hB₀, hred⟩)
      · subst B₀
        exact Finset.mem_union_right _ (by simp)
    have himage_card :
        ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ)).card =
          (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).card := by
      rw [Finset.card_image_of_injective]
      exact orderedImageBag_injective σ
    calc
      (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
          (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).card
          = ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ)).card := himage_card.symm
      _ ≤ target.card := Finset.card_le_card hsubset
      _ ≤ ((S.state i).bags.filter fun B => (S.state i).redAdj A B).card + 1 := by
        have h :=
          Finset.card_union_le
            ((S.state i).bags.filter fun B => (S.state i).redAdj A B)
            ({A} : Finset (Finset V))
        simpa [target] using h
      _ ≤ d + 1 := by
        have hred := S.redDegree_le i hi hA
        simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 1
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨A, hA, rfl⟩
    let target : Finset (Finset V) :=
      ((S.state i).bags.filter fun B => (S.state i).redAdj A B) ∪ {A}
    have hsubset :
        (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ) ⊆ target := by
      intro B hB
      rcases Finset.mem_image.mp hB with ⟨R, hRerr, rfl⟩
      rcases Finset.mem_filter.mp hRerr with ⟨hRpart, hnon⟩
      rcases Finset.mem_image.mp hRpart with ⟨B₀, hB₀, rfl⟩
      have hred_or_BA :=
        nonconstant_preimage_imp_red_or_same σ hsem hB₀ hA hnon
      rw [orderedImageBag_orderedPreimageBag]
      rcases hred_or_BA with hredBA | hsame
      · have hredAB := (S.state i).red_symm hB₀ hA hredBA
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hB₀, hredAB⟩)
      · subst B₀
        exact Finset.mem_union_right _ (by simp)
    have himage_card :
        ((Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ)).card =
          (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).card := by
      rw [Finset.card_image_of_injective]
      exact orderedImageBag_injective σ
    calc
      (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
          (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).card
          = ((Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfState σ i) (orderedPreimageBag σ A)).image
            (orderedImageBag σ)).card := himage_card.symm
      _ ≤ target.card := Finset.card_le_card hsubset
      _ ≤ ((S.state i).bags.filter fun B => (S.state i).redAdj A B).card + 1 := by
        have h :=
          Finset.card_union_le
            ((S.state i).bags.filter fun B => (S.state i).redAdj A B)
            ({A} : Finset (Finset V))
        simpa [target] using h
      _ ≤ d + 1 := by
        have hred := S.redDegree_le i hi hA
        simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 1

end ContractionSequence

namespace ContractionSequence

/-- The two bags contracted at a specified step, packaged with the bag-family
part of the contraction-step certificate. -/
noncomputable def stepPair
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    {p : Finset V × Finset V //
      p.1 ∈ (S.state i).bags ∧
      p.2 ∈ (S.state i).bags ∧
      p.1 ≠ p.2 ∧
      (S.state (i + 1)).bags =
        insert (p.1 ∪ p.2) (((S.state i).bags.erase p.1).erase p.2)} :=
  Classical.choice <| by
  classical
  rcases S.step_contracts i hi with ⟨A, hA, B, hB, hAB, hbags, _hred, _hblack⟩
  exact ⟨⟨(A, B), hA, hB, hAB, hbags⟩⟩

/-- The contracted pair at time `i`, with a harmless default outside the
declared time interval.  This proof-independent selector avoids carrying
irrelevant proof terms through the leaf-order recursion. -/
noncomputable def stepPairAt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (i : ℕ) : Finset V × Finset V :=
  if hi : i < S.stepCount then (S.stepPair hi).1 else (∅, ∅)

theorem stepPairAt_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    (S.stepPairAt i).1 ∈ (S.state i).bags ∧
      (S.stepPairAt i).2 ∈ (S.state i).bags ∧
      (S.stepPairAt i).1 ≠ (S.stepPairAt i).2 ∧
      (S.state (i + 1)).bags =
        insert ((S.stepPairAt i).1 ∪ (S.stepPairAt i).2)
          (((S.state i).bags.erase (S.stepPairAt i).1).erase (S.stepPairAt i).2) := by
  classical
  have hif : S.stepPairAt i = (S.stepPair hi).1 := by
    simp [stepPairAt, hi]
  simpa [hif] using (S.stepPair hi).2

/-- The merged bag produced by a step belongs to the next state. -/
theorem stepPairAt_union_mem_next
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    (S.stepPairAt i).1 ∪ (S.stepPairAt i).2 ∈ (S.state (i + 1)).bags := by
  classical
  have hspec := S.stepPairAt_spec hi
  rw [hspec.2.2.2]
  simp

/-- A current bag not among the two contracted bags survives into the next
state. -/
theorem stepPairAt_current_mem_next_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount)
    {X : Finset V} (hX : X ∈ (S.state i).bags)
    (hXA : X ≠ (S.stepPairAt i).1) (hXB : X ≠ (S.stepPairAt i).2) :
    X ∈ (S.state (i + 1)).bags := by
  classical
  have hspec := S.stepPairAt_spec hi
  rw [hspec.2.2.2]
  exact Finset.mem_insert.mpr (Or.inr (by simp [hX, hXA, hXB]))

/-- Every next-state bag is either the newly merged bag or an old bag distinct
from both contracted bags. -/
theorem stepPairAt_next_mem_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount)
    {X : Finset V} (hX : X ∈ (S.state (i + 1)).bags) :
    X = (S.stepPairAt i).1 ∪ (S.stepPairAt i).2 ∨
      X ∈ (S.state i).bags ∧
        X ≠ (S.stepPairAt i).1 ∧ X ≠ (S.stepPairAt i).2 := by
  classical
  have hspec := S.stepPairAt_spec hi
  rw [hspec.2.2.2] at hX
  rcases Finset.mem_insert.mp hX with hXU | hXold
  · exact Or.inl hXU
  ·
    rcases Finset.mem_erase.mp hXold with ⟨hXB, hXold'⟩
    rcases Finset.mem_erase.mp hXold' with ⟨hXA, hXold_current⟩
    exact Or.inr ⟨hXold_current, hXA, hXB⟩

/-- After one side of a graph contraction has been mirrored in the ordered
adjacency matrix, the intermediate rectangular partition still has bounded
nonconstant error.  The extra `+3` accounts for the two children of the merged
bag and the diagonal/self zone convention. -/
theorem matrixPartitionOfAdjacentStates_errorValueAtMost
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (σ : VertexOrder V (Fintype.card V))
    {i : ℕ} (hi : i < S.stepCount) :
    Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G σ)
      (S.matrixPartitionOfTwoStates σ (i + 1) i) (d + 3) := by
  classical
  let A : Finset V := (S.stepPairAt i).1
  let B : Finset V := (S.stepPairAt i).2
  let U : Finset V := A ∪ B
  have hspec := S.stepPairAt_spec hi
  have hA : A ∈ (S.state i).bags := by simpa [A] using hspec.1
  have hB : B ∈ (S.state i).bags := by simpa [B] using hspec.2.1
  have hAB : A ≠ B := by simpa [A, B] using hspec.2.2.1
  have hU : U ∈ (S.state (i + 1)).bags := by
    simpa [A, B, U] using S.stepPairAt_union_mem_next hi
  have hsemCur := S.isSemanticState i (by omega : i ≤ S.stepCount)
  have hsemNext := S.isSemanticState (i + 1) (by omega : i + 1 ≤ S.stepCount)
  constructor
  · intro R hR
    rcases Finset.mem_image.mp hR with ⟨X, hXnext, rfl⟩
    by_cases hXU : X = U
    · subst X
      let target : Finset (Finset V) :=
        ((S.state (i + 1)).bags.filter fun Y => (S.state (i + 1)).redAdj U Y) ∪
          ({A, B, U} : Finset (Finset V))
      have hsubset :
          (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i) (orderedPreimageBag σ U)).image
              (orderedImageBag σ) ⊆ target := by
        intro Y hY
        rcases Finset.mem_image.mp hY with ⟨C, hCerr, rfl⟩
        rcases Finset.mem_filter.mp hCerr with ⟨hCpart, hnon⟩
        rcases Finset.mem_image.mp hCpart with ⟨Y₀, hY₀old, rfl⟩
        rw [orderedImageBag_orderedPreimageBag]
        by_cases hYA : Y₀ = A
        · subst Y₀
          exact Finset.mem_union_right _ (by simp)
        by_cases hYB : Y₀ = B
        · subst Y₀
          exact Finset.mem_union_right _ (by simp)
        have hY₀next :
            Y₀ ∈ (S.state (i + 1)).bags := by
          simpa [A, B] using
            S.stepPairAt_current_mem_next_of_ne hi hY₀old hYA hYB
        have hred_or :=
          nonconstant_preimage_imp_red_or_same σ hsemNext hU hY₀next hnon
        rcases hred_or with hred | hsame
        · exact Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hY₀next, hred⟩)
        · subst Y₀
          exact Finset.mem_union_right _ (by simp)
      have himage_card :
          ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i)
                (orderedPreimageBag σ U)).image
              (orderedImageBag σ)).card =
            (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i)
                (orderedPreimageBag σ U)).card := by
        rw [Finset.card_image_of_injective]
        exact orderedImageBag_injective σ
      calc
        (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfTwoStates σ (i + 1) i)
              (orderedPreimageBag σ U)).card
            = ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                (S.matrixPartitionOfTwoStates σ (i + 1) i)
                  (orderedPreimageBag σ U)).image
                (orderedImageBag σ)).card := himage_card.symm
        _ ≤ target.card := Finset.card_le_card hsubset
        _ ≤ ((S.state (i + 1)).bags.filter fun Y =>
              (S.state (i + 1)).redAdj U Y).card + 3 := by
            have hcard :=
              Finset.card_union_le
                ((S.state (i + 1)).bags.filter fun Y => (S.state (i + 1)).redAdj U Y)
                ({A, B, U} : Finset (Finset V))
            have hspecial : ({A, B, U} : Finset (Finset V)).card ≤ 3 := by
              calc
                ({A, B, U} : Finset (Finset V)).card ≤
                    ({B, U} : Finset (Finset V)).card + 1 :=
                  Finset.card_insert_le _ _
                _ ≤ ({U} : Finset (Finset V)).card + 2 := by
                  have h := Finset.card_insert_le B ({U} : Finset (Finset V))
                  omega
                _ ≤ 3 := by simp
            have htarget_card :
                target.card ≤
                  ((S.state (i + 1)).bags.filter fun Y =>
                    (S.state (i + 1)).redAdj U Y).card +
                    ({A, B, U} : Finset (Finset V)).card := by
              simpa [target] using hcard
            omega
        _ ≤ d + 3 := by
            have hred := S.redDegree_le (i + 1) (by omega : i + 1 ≤ S.stepCount) hU
            simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 3
    · rcases S.stepPairAt_next_mem_cases hi hXnext with hmerged | hXold_data
      · exact (hXU (by simpa [A, B, U] using hmerged)).elim
      · rcases hXold_data with ⟨hXold, _hXA, _hXB⟩
        let target : Finset (Finset V) :=
          ((S.state i).bags.filter fun Y => (S.state i).redAdj X Y) ∪
            ({X} : Finset (Finset V))
        have hsubset :
            (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                (S.matrixPartitionOfTwoStates σ (i + 1) i)
                  (orderedPreimageBag σ X)).image
                (orderedImageBag σ) ⊆ target := by
          intro Y hY
          rcases Finset.mem_image.mp hY with ⟨C, hCerr, rfl⟩
          rcases Finset.mem_filter.mp hCerr with ⟨hCpart, hnon⟩
          rcases Finset.mem_image.mp hCpart with ⟨Y₀, hY₀old, rfl⟩
          rw [orderedImageBag_orderedPreimageBag]
          have hred_or :=
            nonconstant_preimage_imp_red_or_same σ hsemCur hXold hY₀old hnon
          rcases hred_or with hred | hsame
          · exact Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hY₀old, hred⟩)
          · subst Y₀
            exact Finset.mem_union_right _ (by simp)
        have himage_card :
            ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                (S.matrixPartitionOfTwoStates σ (i + 1) i)
                  (orderedPreimageBag σ X)).image
                (orderedImageBag σ)).card =
              (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                (S.matrixPartitionOfTwoStates σ (i + 1) i)
                  (orderedPreimageBag σ X)).card := by
          rw [Finset.card_image_of_injective]
          exact orderedImageBag_injective σ
        calc
          (Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i)
                (orderedPreimageBag σ X)).card
              = ((Matrix.rowErrorSet (Matrix.orderedAdjacency G σ)
                  (S.matrixPartitionOfTwoStates σ (i + 1) i)
                    (orderedPreimageBag σ X)).image
                  (orderedImageBag σ)).card := himage_card.symm
          _ ≤ target.card := Finset.card_le_card hsubset
          _ ≤ ((S.state i).bags.filter fun Y => (S.state i).redAdj X Y).card + 1 := by
              have hcard :=
                Finset.card_union_le
                  ((S.state i).bags.filter fun Y => (S.state i).redAdj X Y)
                  ({X} : Finset (Finset V))
              simpa [target] using hcard
          _ ≤ d + 3 := by
              have hred := S.redDegree_le i (by omega : i ≤ S.stepCount) hXold
              have hle : ((S.state i).bags.filter fun Y => (S.state i).redAdj X Y).card + 1
                  ≤ d + 1 := by
                simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 1
              omega
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨Y, hYold, rfl⟩
    let target : Finset (Finset V) :=
      ((S.state i).bags.filter fun X => (S.state i).redAdj Y X) ∪
        ({Y, U} : Finset (Finset V))
    have hsubset :
        (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfTwoStates σ (i + 1) i) (orderedPreimageBag σ Y)).image
            (orderedImageBag σ) ⊆ target := by
      intro X hX
      rcases Finset.mem_image.mp hX with ⟨R, hRerr, rfl⟩
      rcases Finset.mem_filter.mp hRerr with ⟨hRpart, hnon⟩
      rcases Finset.mem_image.mp hRpart with ⟨X₀, hX₀next, rfl⟩
      rw [orderedImageBag_orderedPreimageBag]
      rcases S.stepPairAt_next_mem_cases hi hX₀next with hmerged | hXold_data
      · have hXU : X₀ = U := by
          simpa [A, B, U] using hmerged
        rw [hXU]
        exact Finset.mem_union_right _ (by simp)
      · rcases hXold_data with ⟨hX₀old, _hXA, _hXB⟩
        have hred_or :=
          nonconstant_preimage_imp_red_or_same σ hsemCur hX₀old hYold hnon
        rcases hred_or with hred | hsame
        · have hredYX := (S.state i).red_symm hX₀old hYold hred
          exact Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hX₀old, hredYX⟩)
        · subst X₀
          exact Finset.mem_union_right _ (by simp)
    have himage_card :
        ((Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfTwoStates σ (i + 1) i)
              (orderedPreimageBag σ Y)).image
            (orderedImageBag σ)).card =
          (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
            (S.matrixPartitionOfTwoStates σ (i + 1) i)
              (orderedPreimageBag σ Y)).card := by
      rw [Finset.card_image_of_injective]
      exact orderedImageBag_injective σ
    calc
      (Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
          (S.matrixPartitionOfTwoStates σ (i + 1) i)
            (orderedPreimageBag σ Y)).card
          = ((Matrix.colErrorSet (Matrix.orderedAdjacency G σ)
              (S.matrixPartitionOfTwoStates σ (i + 1) i)
                (orderedPreimageBag σ Y)).image
              (orderedImageBag σ)).card := himage_card.symm
      _ ≤ target.card := Finset.card_le_card hsubset
      _ ≤ ((S.state i).bags.filter fun X => (S.state i).redAdj Y X).card + 2 := by
          have hcard :=
            Finset.card_union_le
              ((S.state i).bags.filter fun X => (S.state i).redAdj Y X)
              ({Y, U} : Finset (Finset V))
          have hspecial : ({Y, U} : Finset (Finset V)).card ≤ 2 := by
            calc
              ({Y, U} : Finset (Finset V)).card ≤
                  ({U} : Finset (Finset V)).card + 1 :=
                Finset.card_insert_le _ _
              _ ≤ 2 := by simp
          have htarget_card :
              target.card ≤
                ((S.state i).bags.filter fun X => (S.state i).redAdj Y X).card +
                  ({Y, U} : Finset (Finset V)).card := by
            simpa [target] using hcard
          omega
      _ ≤ d + 3 := by
          have hred := S.redDegree_le i (by omega : i ≤ S.stepCount) hYold
          have hle : ((S.state i).bags.filter fun X => (S.state i).redAdj Y X).card + 2
              ≤ d + 2 := by
            simpa [redDegree, TrigraphState.redDegree] using Nat.add_le_add_right hred 2
          omega

/-- Walk a contraction sequence backward for `r` steps, starting from the final
bag list and splitting each merged bag into its left and right children. -/
noncomputable def reverseBagList
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) : ℕ → List (Finset V)
  | 0 => (S.state S.stepCount).bags.toList
  | r + 1 =>
      let L := reverseBagList S r
      let i := S.stepCount - (r + 1)
      if i < S.stepCount then
        let p := S.stepPairAt i
        splitMergedBag p.1 p.2 L
      else
        L

/-- The ordered bag list at forward time `i`, read from left to right in the
eventual leaf order.  Outside the declared time interval it is pinned to the
initial list; all mathematical uses pass `i ≤ stepCount`. -/
noncomputable def bagListAt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (i : ℕ) : List (Finset V) :=
  S.reverseBagList (S.stepCount - i)

theorem reverseBagList_toFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ r, r ≤ S.stepCount →
      (S.reverseBagList r).toFinset = (S.state (S.stepCount - r)).bags := by
  classical
  intro r hr
  induction r with
  | zero =>
      simp [reverseBagList]
  | succ r ih =>
      have hrle : r ≤ S.stepCount := by omega
      have hrlt : r < S.stepCount := by omega
      let i := S.stepCount - (r + 1)
      have hi : i < S.stepCount := by dsimp [i]; omega
      have hnext : S.stepCount - r = i + 1 := by dsimp [i]; omega
      have hcur : S.stepCount - (r + 1) = i := by rfl
      let p := S.stepPairAt i
      have hpspec := S.stepPairAt_spec hi
      have hpA : p.1 ∈ (S.state i).bags := hpspec.1
      have hpB : p.2 ∈ (S.state i).bags := hpspec.2.1
      have hpAB : p.1 ≠ p.2 := hpspec.2.2.1
      have hmerge :
          (S.state (i + 1)).bags =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := hpspec.2.2.2
      have hL :
          (S.reverseBagList r).toFinset =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := by
        calc
          (S.reverseBagList r).toFinset = (S.state (S.stepCount - r)).bags := ih hrle
          _ = (S.state (i + 1)).bags := by rw [hnext]
          _ = insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := hmerge
      have hpart : IsBagPartition (S.state i).bags :=
        ⟨(S.state i).bag_nonempty, (S.state i).bag_disjoint, (S.state i).bag_cover⟩
      simp [reverseBagList, i, hi, p, hcur,
        splitMergedBag_toFinset_of_merge hpart hpA hpB hpAB hL]

theorem reverseBagList_nodup
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ r, r ≤ S.stepCount → (S.reverseBagList r).Nodup := by
  classical
  intro r hr
  induction r with
  | zero =>
      simp [reverseBagList, Finset.nodup_toList]
  | succ r ih =>
      have hrle : r ≤ S.stepCount := by omega
      have hrlt : r < S.stepCount := by omega
      let i := S.stepCount - (r + 1)
      have hi : i < S.stepCount := by dsimp [i]; omega
      have hnext : S.stepCount - r = i + 1 := by dsimp [i]; omega
      let p := S.stepPairAt i
      have hpspec := S.stepPairAt_spec hi
      have hpA : p.1 ∈ (S.state i).bags := hpspec.1
      have hpB : p.2 ∈ (S.state i).bags := hpspec.2.1
      have hpAB : p.1 ≠ p.2 := hpspec.2.2.1
      have hmerge :
          (S.state (i + 1)).bags =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := hpspec.2.2.2
      have hL :
          (S.reverseBagList r).toFinset =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := by
        calc
          (S.reverseBagList r).toFinset = (S.state (S.stepCount - r)).bags :=
            S.reverseBagList_toFinset r hrle
          _ = (S.state (i + 1)).bags := by rw [hnext]
          _ = insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := hmerge
      have hpart : IsBagPartition (S.state i).bags :=
        ⟨(S.state i).bag_nonempty, (S.state i).bag_disjoint, (S.state i).bag_cover⟩
      simp [reverseBagList, i, hi, p,
        splitMergedBag_nodup_of_merge hpart hpA hpB hpAB (ih hrle) hL]

theorem bagListAt_toFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    (S.bagListAt i).toFinset = (S.state i).bags := by
  have hsub : S.stepCount - (S.stepCount - i) = i := by omega
  simpa [bagListAt, hsub] using
    S.reverseBagList_toFinset (S.stepCount - i) (by omega : S.stepCount - i ≤ S.stepCount)

theorem bagListAt_nodup
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    (S.bagListAt i).Nodup := by
  simpa [bagListAt] using
    S.reverseBagList_nodup (S.stepCount - i) (by omega : S.stepCount - i ≤ S.stepCount)

/-- The ordered bag list at time `i` has exactly one entry per current bag. -/
theorem bagListAt_length
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    (S.bagListAt i).length = (S.state i).bags.card := by
  rw [← List.toFinset_card_of_nodup (S.bagListAt_nodup hi),
    S.bagListAt_toFinset hi]

/-- One graph contraction shortens the left-to-right bag list by one. -/
theorem bagListAt_length_succ_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    (S.bagListAt (i + 1)).length + 1 = (S.bagListAt i).length := by
  rw [S.bagListAt_length (by omega : i + 1 ≤ S.stepCount),
    S.bagListAt_length (by omega : i ≤ S.stepCount)]
  exact S.bags_card_add_one hi

/-- In a nonempty graph, the bag list at time `i` has `stepCount - i + 1`
entries. -/
theorem bagListAt_length_eq_stepCount_sub_add_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    (S.bagListAt i).length = S.stepCount - i + 1 := by
  have hlen := S.bagListAt_length hi
  have hcount := S.bags_card_add_index (i := i) hi
  have hsteps := S.stepCount_add_one_eq_card
  omega

theorem bagListAt_step_eq_split
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    S.bagListAt i =
      let p := S.stepPairAt i
      splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) := by
  classical
  let r := S.stepCount - (i + 1)
  have hstep : S.stepCount - i = r + 1 := by dsimp [r]; omega
  have hr_index : S.stepCount - (r + 1) = i := by dsimp [r]; omega
  by_cases h : i < S.stepCount
  · simp [bagListAt, hstep, reverseBagList, r, hr_index, h]
  · exact (h hi).elim

/-- The ordered list of singleton bags obtained by reading the leaves of the
contraction tree from left to right. -/
noncomputable def leafBagList
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) : List (Finset V) :=
  S.reverseBagList S.stepCount

theorem leafBagList_toFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.leafBagList.toFinset = TrigraphState.singletonBags V := by
  simpa [leafBagList, S.starts.1] using
    S.reverseBagList_toFinset S.stepCount le_rfl

theorem leafBagList_nodup
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.leafBagList.Nodup := by
  simpa [leafBagList] using S.reverseBagList_nodup S.stepCount le_rfl

theorem leafBagList_length
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.leafBagList.length = Fintype.card V := by
  classical
  rw [← List.toFinset_card_of_nodup S.leafBagList_nodup,
    S.leafBagList_toFinset, TrigraphState.card_singletonBags]

noncomputable def leafBagVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    (A : {A : Finset V // A ∈ S.leafBagList}) : V :=
  Classical.choose <| TrigraphState.mem_singletonBags.mp <| by
    have hA : A.1 ∈ S.leafBagList.toFinset := List.mem_toFinset.mpr A.2
    simpa [S.leafBagList_toFinset] using hA

theorem leafBagVertex_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    (A : {A : Finset V // A ∈ S.leafBagList}) :
    A.1 = {S.leafBagVertex A} := by
  unfold leafBagVertex
  exact Classical.choose_spec <| TrigraphState.mem_singletonBags.mp <| by
    have hA : A.1 ∈ S.leafBagList.toFinset := List.mem_toFinset.mpr A.2
    simpa [S.leafBagList_toFinset] using hA

/-- The equivalence from leaf singleton bags to vertices. -/
noncomputable def leafBagEquivVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    {A : Finset V // A ∈ S.leafBagList} ≃ V where
  toFun := S.leafBagVertex
  invFun v := ⟨{v}, by
    have h : ({v} : Finset V) ∈ S.leafBagList.toFinset := by
      rw [S.leafBagList_toFinset]
      exact TrigraphState.mem_singletonBags.mpr ⟨v, rfl⟩
    exact List.mem_toFinset.mp h⟩
  left_inv A := by
    apply Subtype.ext
    exact (S.leafBagVertex_spec A).symm
  right_inv v := by
    have h :=
      S.leafBagVertex_spec
        (⟨{v}, by
          have h : ({v} : Finset V) ∈ S.leafBagList.toFinset := by
            rw [S.leafBagList_toFinset]
            exact TrigraphState.mem_singletonBags.mpr ⟨v, rfl⟩
          exact List.mem_toFinset.mp h⟩ :
          {A : Finset V // A ∈ S.leafBagList})
    exact (Finset.singleton_inj.mp h).symm

/-- The left-to-right order on leaves of the contraction tree. -/
noncomputable def leafOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) : VertexOrder V (Fintype.card V) where
  equiv :=
    (finCongr S.leafBagList_length.symm).trans
      ((List.Nodup.getEquiv S.leafBagList S.leafBagList_nodup).trans
        S.leafBagEquivVertex)

theorem leafOrder_singleton_eq_get
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (i : Fin (Fintype.card V)) :
    ({S.leafOrder.equiv i} : Finset V) =
      S.leafBagList.get ((finCongr S.leafBagList_length.symm) i) := by
  classical
  let j : Fin S.leafBagList.length := (finCongr S.leafBagList_length.symm) i
  have hspec :=
    S.leafBagVertex_spec
      ((List.Nodup.getEquiv S.leafBagList S.leafBagList_nodup) j)
  change ({S.leafBagVertex
      ((List.Nodup.getEquiv S.leafBagList S.leafBagList_nodup) j)} : Finset V) =
      S.leafBagList.get j
  exact hspec.symm

/-- A certificate that an ordered bag list is represented by consecutive
interval parts in the leaf order. -/
structure BagListDivision
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (L : List (Finset V)) where
  /-- The interval division whose parts are the ordered preimages of `L`. -/
  div : Division (Fintype.card V) L.length
  /-- The `i`-th interval is exactly the preimage of the `i`-th bag. -/
  part_eq :
    ∀ i : Fin L.length,
      div.part i = orderedPreimageBag S.leafOrder (L.get i)

/-- The leaf bag list is represented by the finest interval division. -/
noncomputable def leafBagListDivision
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.BagListDivision S.leafBagList where
  div :=
    Division.castIndex S.leafBagList_length.symm
      (Division.singleton (Fintype.card V))
  part_eq := by
    classical
    intro i
    let r : Fin (Fintype.card V) := (finCongr S.leafBagList_length.symm).symm i
    have hget : ({S.leafOrder.equiv r} : Finset V) = S.leafBagList.get i := by
      simpa [r] using S.leafOrder_singleton_eq_get r
    ext x
    constructor
    · intro hx
      have hxrow : x = r := by
        simpa [Division.castIndex, Division.singleton, r] using hx
      subst x
      rw [← hget]
      simp [orderedPreimageBag]
    · intro hx
      have hxrow : x = r := by
        have hxmem_get : S.leafOrder.equiv x ∈ S.leafBagList.get i := by
          simpa [orderedPreimageBag] using hx
        have hxmem : S.leafOrder.equiv x ∈ ({S.leafOrder.equiv r} : Finset V) := by
          simpa [hget] using hxmem_get
        have heq : S.leafOrder.equiv x = S.leafOrder.equiv r := by
          simpa using hxmem
        exact S.leafOrder.equiv.injective heq
      simp [Division.castIndex, Division.singleton, r, hxrow]

namespace BagListDivision

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {d : ℕ}
variable (S : ContractionSequence G d)

/-- Reindex a bag-list division along an equality of its underlying list. -/
noncomputable def castList {L L' : List (Finset V)}
    (D : S.BagListDivision L) (h : L = L') :
    S.BagListDivision L' where
  div := Division.castIndex (congrArg List.length h) D.div
  part_eq := by
    subst L'
    intro i
    simpa [Division.castIndex] using D.part_eq i

omit [Fintype V] [DecidableEq V] in
private theorem get_pair_left
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    (P ++ [A, B] ++ Q).get ((finCongr hcur).symm idx.castSucc) = A := by
  classical
  dsimp
  simp

omit [Fintype V] [DecidableEq V] in
private theorem get_pair_right
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    (P ++ [A, B] ++ Q).get ((finCongr hcur).symm idx.succ) = B := by
  classical
  dsimp
  simp

omit [Fintype V] in
private theorem get_merged
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm idx) = A ∪ B := by
  classical
  dsimp
  simp

omit [Fintype V] in
private theorem get_before_fused_pair
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    ∀ (j : Fin (P ++ [A ∪ B] ++ Q).length),
      ((finCongr hnext) j).1 < P.length →
        (P ++ [A, B] ++ Q).get
            ((finCongr hcur).symm ((finCongr hnext) j).castSucc) =
          (P ++ [A ∪ B] ++ Q).get j := by
  classical
  dsimp
  intro j hj
  simp [List.getElem_append_left, hj]

omit [Fintype V] in
private theorem get_after_fused_pair
    (P Q : List (Finset V)) (A B : Finset V) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    ∀ (j : Fin (P ++ [A ∪ B] ++ Q).length),
      P.length < ((finCongr hnext) j).1 →
        (P ++ [A, B] ++ Q).get
            ((finCongr hcur).symm ((finCongr hnext) j).succ) =
          (P ++ [A ∪ B] ++ Q).get j := by
  classical
  dsimp
  intro j hj
  obtain ⟨t, ht⟩ : ∃ t, j.1 = P.length + 1 + t :=
    ⟨j.1 - P.length - 1, by omega⟩
  have hnot1 : ¬ P.length + 1 + t + 1 < P.length := by omega
  have hnot2 : ¬ P.length + 1 + t < P.length := by omega
  have hsub1 : P.length + 1 + t + 1 - P.length = t + 2 := by omega
  have hsub2 : P.length + 1 + t - P.length = t + 1 := by omega
  simp [List.getElem_append, ht, hnot1, hnot2, hsub1, hsub2]

/-- Fuse the two adjacent list entries `A` and `B` into `A ∪ B`, carrying the
associated interval division along by the corresponding division fusion. -/
noncomputable def mergeAdjacent
    {P Q : List (Finset V)} {A B : Finset V}
    (D : S.BagListDivision (P ++ [A, B] ++ Q)) :
    S.BagListDivision (P ++ [A ∪ B] ++ Q) :=
  let k := P.length + Q.length
  let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
  let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
  let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
  let Dcur : Division (Fintype.card V) (k + 2) := Division.castIndex hcur D.div
  let Dnext : Division (Fintype.card V) (k + 1) := Dcur.fuse idx
  { div := Division.castIndex hnext.symm Dnext
    part_eq := by
      classical
      intro j
      let j' : Fin (k + 1) := (finCongr hnext) j
      have hpart_cur :
          ∀ a : Fin (k + 2),
            Dcur.part a =
              orderedPreimageBag S.leafOrder
                ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm a)) := by
        intro a
        simpa [Dcur, Division.castIndex] using D.part_eq ((finCongr hcur).symm a)
      have htarget :
          (P ++ [A ∪ B] ++ Q).get j =
            (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j') := by
        simp [j']
      by_cases hji : j' = idx
      ·
        have hleft :
            Dcur.part idx.castSucc =
              orderedPreimageBag S.leafOrder A := by
          rw [hpart_cur idx.castSucc]
          rw [get_pair_left (V := V) P Q A B]
        have hright :
            Dcur.part idx.succ =
              orderedPreimageBag S.leafOrder B := by
          rw [hpart_cur idx.succ]
          rw [get_pair_right (V := V) P Q A B]
        have hget :
            (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm idx) = A ∪ B :=
          get_merged (V := V) P Q A B
        have hgetj :
            (P ++ [A ∪ B] ++ Q).get j = A ∪ B := by
          calc
            (P ++ [A ∪ B] ++ Q).get j
                = (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j') := htarget
            _ = (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm idx) := by
                rw [hji]
            _ = A ∪ B := hget
        calc
          (Division.castIndex hnext.symm Dnext).part j
              = Dnext.part j' := by
                  simp [Dnext, Division.castIndex, j']
          _ = Dnext.part idx := by
                  rw [hji]
          _ = Dcur.part idx.castSucc ∪ Dcur.part idx.succ := by
                  simp [Dnext, Division.fuse_part_self]
          _ = orderedPreimageBag S.leafOrder A ∪ orderedPreimageBag S.leafOrder B := by
                  rw [hleft, hright]
          _ = orderedPreimageBag S.leafOrder (A ∪ B) := by
                  rw [orderedPreimageBag_union]
          _ = orderedPreimageBag S.leafOrder
                ((P ++ [A ∪ B] ++ Q).get j) := by
                  rw [hgetj]
      · rcases lt_or_gt_of_ne hji with hlt | hgt
        · have hcur_get :
              (P ++ [A, B] ++ Q).get ((finCongr hcur).symm j'.castSucc) =
                (P ++ [A ∪ B] ++ Q).get j :=
            get_before_fused_pair (V := V) P Q A B j hlt
          calc
            (Division.castIndex hnext.symm Dnext).part j
                = Dnext.part j' := by simp [Dnext, Division.castIndex, j']
            _ = Dcur.part j'.castSucc := by
                exact Division.fuse_part_of_lt Dcur hlt
            _ = orderedPreimageBag S.leafOrder
                  ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm j'.castSucc)) := by
                rw [hpart_cur j'.castSucc]
            _ = orderedPreimageBag S.leafOrder ((P ++ [A ∪ B] ++ Q).get j) := by
                rw [hcur_get]
        · have hcur_get :
              (P ++ [A, B] ++ Q).get ((finCongr hcur).symm j'.succ) =
                (P ++ [A ∪ B] ++ Q).get j :=
            get_after_fused_pair (V := V) P Q A B j hgt
          calc
            (Division.castIndex hnext.symm Dnext).part j
                = Dnext.part j' := by simp [Dnext, Division.castIndex, j']
            _ = Dcur.part j'.succ := by
                exact Division.fuse_part_of_gt Dcur hgt
            _ = orderedPreimageBag S.leafOrder
                  ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm j'.succ)) := by
                rw [hpart_cur j'.succ]
            _ = orderedPreimageBag S.leafOrder ((P ++ [A ∪ B] ++ Q).get j) := by
                rw [hcur_get] }

/-- The division inside `mergeAdjacent` is exactly the fusion of the two
adjacent old parts corresponding to `A` and `B`. -/
theorem mergeAdjacent_isFusionAt
    {P Q : List (Finset V)} {A B : Finset V}
    (D : S.BagListDivision (P ++ [A, B] ++ Q)) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    let Dcur : Division (Fintype.card V) (k + 2) := Division.castIndex hcur D.div
    Division.IsFusionAt Dcur
      (Division.castIndex hnext (BagListDivision.mergeAdjacent (S := S) D).div)
      idx := by
  classical
  dsimp [mergeAdjacent]
  intro j
  exact Division.isFusionAt_fuse _ _ j

/-- Any interval certificates for two adjacent bag lists related by merging
`A` and `B` are related by the corresponding division fusion.  This removes
any dependence on which proof object was chosen for either list. -/
theorem isFusionAt_of_adjacent_merge
    {P Q : List (Finset V)} {A B : Finset V}
    (Dcur : S.BagListDivision (P ++ [A, B] ++ Q))
    (Dnext : S.BagListDivision (P ++ [A ∪ B] ++ Q)) :
    let k := P.length + Q.length
    let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
    let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
    let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
    Division.IsFusionAt
      (Division.castIndex hcur Dcur.div)
      (Division.castIndex hnext Dnext.div)
      idx := by
  classical
  dsimp
  intro j
  let k := P.length + Q.length
  let hcur : (P ++ [A, B] ++ Q).length = k + 2 := by simp [k]; omega
  let hnext : (P ++ [A ∪ B] ++ Q).length = k + 1 := by simp [k]; omega
  let idx : Fin (k + 1) := ⟨P.length, by simp [k]; omega⟩
  let DcurCast : Division (Fintype.card V) (k + 2) :=
    Division.castIndex hcur Dcur.div
  have hcur_part :
      ∀ a : Fin (k + 2),
        DcurCast.part a =
          orderedPreimageBag S.leafOrder
            ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm a)) := by
    intro a
    simpa [DcurCast, Division.castIndex] using Dcur.part_eq ((finCongr hcur).symm a)
  have hnext_part :
      ∀ a : Fin (k + 1),
        (Division.castIndex hnext Dnext.div).part a =
          orderedPreimageBag S.leafOrder
            ((P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm a)) := by
    intro a
    simpa [Division.castIndex] using Dnext.part_eq ((finCongr hnext).symm a)
  by_cases hji : j = idx
  · subst j
    have hleft :
        DcurCast.part idx.castSucc = orderedPreimageBag S.leafOrder A := by
      rw [hcur_part idx.castSucc]
      rw [get_pair_left (V := V) P Q A B]
    have hright :
        DcurCast.part idx.succ = orderedPreimageBag S.leafOrder B := by
      rw [hcur_part idx.succ]
      rw [get_pair_right (V := V) P Q A B]
    have hget :
        (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm idx) = A ∪ B :=
      get_merged (V := V) P Q A B
    calc
      (Division.castIndex hnext Dnext.div).part idx
          = orderedPreimageBag S.leafOrder (A ∪ B) := by
              rw [hnext_part idx, hget]
      _ = orderedPreimageBag S.leafOrder A ∪ orderedPreimageBag S.leafOrder B := by
              rw [orderedPreimageBag_union]
      _ = DcurCast.part idx.castSucc ∪ DcurCast.part idx.succ := by
              rw [hleft, hright]
      _ = DcurCast.fusePart idx idx := by
              simp [Division.fusePart]
  · rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hcur_get :
          (P ++ [A, B] ++ Q).get ((finCongr hcur).symm j.castSucc) =
            (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j) := by
        simpa using
          get_before_fused_pair (V := V) P Q A B ((finCongr hnext).symm j) hlt
      calc
        (Division.castIndex hnext Dnext.div).part j
            = orderedPreimageBag S.leafOrder
                ((P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j)) := hnext_part j
        _ = orderedPreimageBag S.leafOrder
                ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm j.castSucc)) := by
            rw [hcur_get]
        _ = DcurCast.part j.castSucc := by
            rw [hcur_part j.castSucc]
        _ = DcurCast.fusePart idx j := by
            simp [Division.fusePart, ne_of_lt hlt, hlt]
    · have hcur_get :
          (P ++ [A, B] ++ Q).get ((finCongr hcur).symm j.succ) =
            (P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j) := by
        simpa using
          get_after_fused_pair (V := V) P Q A B ((finCongr hnext).symm j) hgt
      have hnlt : ¬ j < idx := not_lt_of_ge (le_of_lt hgt)
      calc
        (Division.castIndex hnext Dnext.div).part j
            = orderedPreimageBag S.leafOrder
                ((P ++ [A ∪ B] ++ Q).get ((finCongr hnext).symm j)) := hnext_part j
        _ = orderedPreimageBag S.leafOrder
                ((P ++ [A, B] ++ Q).get ((finCongr hcur).symm j.succ)) := by
            rw [hcur_get]
        _ = DcurCast.part j.succ := by
            rw [hcur_part j.succ]
        _ = DcurCast.fusePart idx j := by
            simp [Division.fusePart, ne_of_gt hgt, hnlt]

end BagListDivision

/-- The matrix division obtained from row and column bag-list interval
certificates.  The positivity hypotheses are exactly the nonempty-graph
zerology needed to write the number of parts as `cuts + 1`. -/
noncomputable def matrixDivisionOfBagLists
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    {LR LC : List (Finset V)}
    (R : S.BagListDivision LR) (C : S.BagListDivision LC)
    (hR : 0 < LR.length) (hC : 0 < LC.length) :
    Matrix.MatrixDivision (Fintype.card V) (Fintype.card V) where
  rowCuts := LR.length - 1
  colCuts := LC.length - 1
  rowDiv := Division.castIndex (by omega : LR.length = (LR.length - 1) + 1) R.div
  colDiv := Division.castIndex (by omega : LC.length = (LC.length - 1) + 1) C.div

/-- Matrix division from bag-list certificates with explicit numbers of row
and column cuts.  This version is used in fusion proofs because the equations
`length = cuts + 1` avoid the casts introduced by `length - 1`. -/
noncomputable def matrixDivisionOfBagListsWithCuts
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    {LR LC : List (Finset V)}
    (R : S.BagListDivision LR) (C : S.BagListDivision LC)
    (r c : ℕ) (hR : LR.length = r + 1) (hC : LC.length = c + 1) :
    Matrix.MatrixDivision (Fintype.card V) (Fintype.card V) where
  rowCuts := r
  colCuts := c
  rowDiv := Division.castIndex hR R.div
  colDiv := Division.castIndex hC C.div

/-- The unordered partition underlying the explicit matrix division from
bag-list certificates is exactly the partition whose rows and columns are the
corresponding trigraph states. -/
theorem toPartition_matrixDivisionOfBagListsWithCuts_eq_matrixPartitionOfTwoStates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    {rowTime colTime r c : ℕ}
    (hrowTime : rowTime ≤ S.stepCount) (hcolTime : colTime ≤ S.stepCount)
    (R : S.BagListDivision (S.bagListAt rowTime))
    (C : S.BagListDivision (S.bagListAt colTime))
    (hR : (S.bagListAt rowTime).length = r + 1)
    (hC : (S.bagListAt colTime).length = c + 1) :
    (S.matrixDivisionOfBagListsWithCuts R C r c hR hC).toPartition =
      S.matrixPartitionOfTwoStates S.leafOrder rowTime colTime := by
  classical
  let D := S.matrixDivisionOfBagListsWithCuts R C r c hR hC
  apply Matrix.MatrixPartition.ext_parts
  · ext X
    constructor
    · intro hX
      rcases Finset.mem_map.mp hX with ⟨a, _ha, haX⟩
      change D.rowDiv.part a = X at haX
      let a' : Fin (S.bagListAt rowTime).length := (finCongr hR).symm a
      have hpart :
          D.rowDiv.part a =
            orderedPreimageBag S.leafOrder ((S.bagListAt rowTime).get a') := by
        simpa [D, matrixDivisionOfBagListsWithCuts, Division.castIndex, a'] using
          R.part_eq a'
      have hbag_state :
          (S.bagListAt rowTime).get a' ∈ (S.state rowTime).bags := by
        have hmem_list : (S.bagListAt rowTime).get a' ∈ S.bagListAt rowTime :=
          List.get_mem _ _
        have hmem_finset :
            (S.bagListAt rowTime).get a' ∈ (S.bagListAt rowTime).toFinset :=
          List.mem_toFinset.mpr hmem_list
        simpa [S.bagListAt_toFinset hrowTime] using hmem_finset
      refine Finset.mem_image.mpr
        ⟨(S.bagListAt rowTime).get a', hbag_state, ?_⟩
      rw [← hpart, haX]
    · intro hX
      rcases Finset.mem_image.mp hX with ⟨A, hAstate, rfl⟩
      have hA_finset : A ∈ (S.bagListAt rowTime).toFinset := by
        simpa [S.bagListAt_toFinset hrowTime] using hAstate
      have hA_list : A ∈ S.bagListAt rowTime := List.mem_toFinset.mp hA_finset
      rcases List.mem_iff_get.mp hA_list with ⟨a, ha⟩
      refine Finset.mem_map.mpr ⟨finCongr hR a, Finset.mem_univ _, ?_⟩
      change D.rowDiv.part (finCongr hR a) = orderedPreimageBag S.leafOrder A
      calc
        D.rowDiv.part (finCongr hR a) = R.div.part a := by
          simp [D, matrixDivisionOfBagListsWithCuts, Division.castIndex]
        _ = orderedPreimageBag S.leafOrder ((S.bagListAt rowTime).get a) := R.part_eq a
        _ = orderedPreimageBag S.leafOrder A := by rw [ha]
  · ext X
    constructor
    · intro hX
      rcases Finset.mem_map.mp hX with ⟨a, _ha, haX⟩
      change D.colDiv.part a = X at haX
      let a' : Fin (S.bagListAt colTime).length := (finCongr hC).symm a
      have hpart :
          D.colDiv.part a =
            orderedPreimageBag S.leafOrder ((S.bagListAt colTime).get a') := by
        simpa [D, matrixDivisionOfBagListsWithCuts, Division.castIndex, a'] using
          C.part_eq a'
      have hbag_state :
          (S.bagListAt colTime).get a' ∈ (S.state colTime).bags := by
        have hmem_list : (S.bagListAt colTime).get a' ∈ S.bagListAt colTime :=
          List.get_mem _ _
        have hmem_finset :
            (S.bagListAt colTime).get a' ∈ (S.bagListAt colTime).toFinset :=
          List.mem_toFinset.mpr hmem_list
        simpa [S.bagListAt_toFinset hcolTime] using hmem_finset
      refine Finset.mem_image.mpr
        ⟨(S.bagListAt colTime).get a', hbag_state, ?_⟩
      rw [← hpart, haX]
    · intro hX
      rcases Finset.mem_image.mp hX with ⟨A, hAstate, rfl⟩
      have hA_finset : A ∈ (S.bagListAt colTime).toFinset := by
        simpa [S.bagListAt_toFinset hcolTime] using hAstate
      have hA_list : A ∈ S.bagListAt colTime := List.mem_toFinset.mp hA_finset
      rcases List.mem_iff_get.mp hA_list with ⟨a, ha⟩
      refine Finset.mem_map.mpr ⟨finCongr hC a, Finset.mem_univ _, ?_⟩
      change D.colDiv.part (finCongr hC a) = orderedPreimageBag S.leafOrder A
      calc
        D.colDiv.part (finCongr hC a) = C.div.part a := by
          simp [D, matrixDivisionOfBagListsWithCuts, Division.castIndex]
        _ = orderedPreimageBag S.leafOrder ((S.bagListAt colTime).get a) := C.part_eq a
        _ = orderedPreimageBag S.leafOrder A := by rw [ha]

/-- Transfer an error-value bound on the row/column state partition to the
corresponding interval matrix division. -/
theorem nonconstantErrorValueAtMost_matrixDivisionOfBagListsWithCuts
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d t : ℕ}
    (S : ContractionSequence G d)
    {rowTime colTime r c : ℕ}
    (hrowTime : rowTime ≤ S.stepCount) (hcolTime : colTime ≤ S.stepCount)
    (R : S.BagListDivision (S.bagListAt rowTime))
    (C : S.BagListDivision (S.bagListAt colTime))
    (hR : (S.bagListAt rowTime).length = r + 1)
    (hC : (S.bagListAt colTime).length = c + 1)
    (herr :
      Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
        (S.matrixPartitionOfTwoStates S.leafOrder rowTime colTime) t) :
    Matrix.MatrixDivision.NonconstantErrorValueAtMost
      (Matrix.orderedAdjacency G S.leafOrder)
      (S.matrixDivisionOfBagListsWithCuts R C r c hR hC) t := by
  classical
  apply Matrix.MatrixDivision.nonconstantErrorValueAtMost_of_errorValueAtMost_toPartition
  have hpart :=
    S.toPartition_matrixDivisionOfBagListsWithCuts_eq_matrixPartitionOfTwoStates
      hrowTime hcolTime R C hR hC
  simpa [hpart] using herr

namespace BagListDivision

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {d : ℕ}
variable (S : ContractionSequence G d)

theorem hasRowFusion_matrixDivisionOfBagListsWithCuts_adjacent_merge
    {P Q L : List (Finset V)} {A B : Finset V} {c : ℕ}
    (Rcur : S.BagListDivision (P ++ [A, B] ++ Q))
    (Rnext : S.BagListDivision (P ++ [A ∪ B] ++ Q))
    (C : S.BagListDivision L)
    (hC : L.length = c + 1) :
    Matrix.MatrixDivision.HasRowFusion
      (S.matrixDivisionOfBagListsWithCuts Rcur C (P.length + Q.length + 1) c
        (by simp; omega) hC)
      (S.matrixDivisionOfBagListsWithCuts Rnext C (P.length + Q.length) c
        (by simp; omega) hC) := by
  classical
  refine ⟨rfl, rfl, ⟨P.length, by simp [matrixDivisionOfBagListsWithCuts]; omega⟩, ?_, ?_⟩
  · simpa [matrixDivisionOfBagListsWithCuts] using
      isFusionAt_of_adjacent_merge (S := S) Rcur Rnext
  · intro j
    apply congrArg C.div.part
    ext
    rfl

theorem hasColFusion_matrixDivisionOfBagListsWithCuts_adjacent_merge
    {P Q L : List (Finset V)} {A B : Finset V} {r : ℕ}
    (R : S.BagListDivision L)
    (Ccur : S.BagListDivision (P ++ [A, B] ++ Q))
    (Cnext : S.BagListDivision (P ++ [A ∪ B] ++ Q))
    (hR : L.length = r + 1) :
    Matrix.MatrixDivision.HasColFusion
      (S.matrixDivisionOfBagListsWithCuts R Ccur r (P.length + Q.length + 1)
        hR (by simp; omega))
      (S.matrixDivisionOfBagListsWithCuts R Cnext r (P.length + Q.length)
        hR (by simp; omega)) := by
  classical
  refine ⟨rfl, rfl, ⟨P.length, by simp [matrixDivisionOfBagListsWithCuts]; omega⟩, ?_, ?_⟩
  · intro i
    apply congrArg R.div.part
    ext
    rfl
  · simpa [matrixDivisionOfBagListsWithCuts] using
      isFusionAt_of_adjacent_merge (S := S) Ccur Cnext

end BagListDivision

namespace BagListDivision

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {d : ℕ}
variable (S : ContractionSequence G d)

end BagListDivision

/-- Every left-to-right bag list along the contraction sequence is represented
by consecutive intervals in the leaf order. -/
theorem exists_bagListDivisionAt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ i : ℕ, i ≤ S.stepCount → Nonempty (S.BagListDivision (S.bagListAt i))
  | 0, _ => by
      have h0 : S.bagListAt 0 = S.leafBagList := by
        simp [bagListAt, leafBagList]
      exact ⟨by simpa [h0] using S.leafBagListDivision⟩
  | i + 1, hi => by
      classical
      have hlt : i < S.stepCount := by omega
      let p := S.stepPairAt i
      rcases S.exists_bagListDivisionAt i (by omega) with ⟨Dcur⟩
      have hsplit_step :
          S.bagListAt i = splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) := by
        simpa [p] using S.bagListAt_step_eq_split hlt
      have hpspec := S.stepPairAt_spec hlt
      have hmerge :
          (S.state (i + 1)).bags =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := by
        simpa [p] using hpspec.2.2.2
      have hmerged_state : p.1 ∪ p.2 ∈ (S.state (i + 1)).bags := by
        rw [hmerge]
        simp
      have hmerged_list : p.1 ∪ p.2 ∈ S.bagListAt (i + 1) := by
        have hmem_finset : p.1 ∪ p.2 ∈ (S.bagListAt (i + 1)).toFinset := by
          rw [S.bagListAt_toFinset (by omega : i + 1 ≤ S.stepCount)]
          exact hmerged_state
        exact List.mem_toFinset.mp hmem_finset
      rcases exists_splitMergedBag_eq_append_of_mem_nodup
          (S.bagListAt_nodup (by omega : i + 1 ≤ S.stepCount)) hmerged_list with
        ⟨P, Q, hnext, _hnotP, _hnotQ, hsplit⟩
      have hcur : S.bagListAt i = P ++ [p.1, p.2] ++ Q := by
        rw [hsplit_step, hsplit]
      let Dcur' : S.BagListDivision (P ++ [p.1, p.2] ++ Q) := by
        simpa [hcur] using Dcur
      have Dnext : S.BagListDivision (P ++ [p.1 ∪ p.2] ++ Q) :=
        BagListDivision.mergeAdjacent (S := S) Dcur'
      exact ⟨by simpa [hnext] using Dnext⟩

/-- A chosen interval division certificate for the bag list at time `i`. -/
noncomputable def bagListDivisionAt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ i : ℕ, i ≤ S.stepCount → S.BagListDivision (S.bagListAt i)
  | 0, _ => by
      have h0 : S.bagListAt 0 = S.leafBagList := by
        simp [bagListAt, leafBagList]
      simpa [h0] using S.leafBagListDivision
  | i + 1, hi => by
      classical
      have hlt : i < S.stepCount := by omega
      let p := S.stepPairAt i
      have Dcur : S.BagListDivision (S.bagListAt i) :=
        S.bagListDivisionAt i (by omega)
      have hsplit_step :
          S.bagListAt i = splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) := by
        simpa [p] using S.bagListAt_step_eq_split hlt
      have hpspec := S.stepPairAt_spec hlt
      have hmerge :
          (S.state (i + 1)).bags =
            insert (p.1 ∪ p.2)
              (((S.state i).bags.erase p.1).erase p.2) := by
        simpa [p] using hpspec.2.2.2
      have hmerged_state : p.1 ∪ p.2 ∈ (S.state (i + 1)).bags := by
        rw [hmerge]
        simp
      have hmerged_list : p.1 ∪ p.2 ∈ S.bagListAt (i + 1) := by
        have hmem_finset : p.1 ∪ p.2 ∈ (S.bagListAt (i + 1)).toFinset := by
          rw [S.bagListAt_toFinset (by omega : i + 1 ≤ S.stepCount)]
          exact hmerged_state
        exact List.mem_toFinset.mp hmem_finset
      let hex :=
        exists_splitMergedBag_eq_append_of_mem_nodup
          (S.bagListAt_nodup (by omega : i + 1 ≤ S.stepCount)) hmerged_list
      let P : List (Finset V) := Classical.choose hex
      let hexQ := Classical.choose_spec hex
      let Q : List (Finset V) := Classical.choose hexQ
      have hdata :
          S.bagListAt (i + 1) = P ++ [p.1 ∪ p.2] ++ Q ∧
            p.1 ∪ p.2 ∉ P ∧ p.1 ∪ p.2 ∉ Q ∧
              splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) =
                P ++ [p.1, p.2] ++ Q := by
        simpa [P, Q, hexQ] using Classical.choose_spec hexQ
      have hnext : S.bagListAt (i + 1) = P ++ [p.1 ∪ p.2] ++ Q := hdata.1
      have hsplit :
          splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) =
            P ++ [p.1, p.2] ++ Q := hdata.2.2.2
      have hcur : S.bagListAt i = P ++ [p.1, p.2] ++ Q := by
        rw [hsplit_step, hsplit]
      let Dcur' : S.BagListDivision (P ++ [p.1, p.2] ++ Q) := by
        simpa [hcur] using Dcur
      have Dnext : S.BagListDivision (P ++ [p.1 ∪ p.2] ++ Q) :=
        BagListDivision.mergeAdjacent (S := S) Dcur'
      simpa [hnext] using Dnext

@[simp] theorem bagListDivisionAt_proof_irrel
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi hi' : i ≤ S.stepCount) :
    S.bagListDivisionAt i hi = S.bagListDivisionAt i hi' := by
  have h : hi = hi' := proof_irrel _ _
  subst h
  rfl

/-- Reindexing the interval certificate at a fixed time is independent of the
chosen proof that the time is in range. -/
theorem bagListDivisionAt_castIndex_div_heq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i l l' : ℕ}
    (hi hi' : i ≤ S.stepCount)
    (h : (S.bagListAt i).length = l)
    (h' : (S.bagListAt i).length = l') :
    Division.castIndex h (S.bagListDivisionAt i hi).div ≍
      Division.castIndex h' (S.bagListDivisionAt i hi').div := by
  have hD : S.bagListDivisionAt i hi = S.bagListDivisionAt i hi' :=
    S.bagListDivisionAt_proof_irrel hi hi'
  cases hD
  exact Division.castIndex_heq h h' _

/-- Adjacent bag lists around one graph contraction, in the leaf order. -/
theorem exists_bagListAt_succ_eq_append_merge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    ∃ P Q : List (Finset V),
      S.bagListAt (i + 1) =
        P ++ [(S.stepPairAt i).1 ∪ (S.stepPairAt i).2] ++ Q ∧
      S.bagListAt i =
        P ++ [(S.stepPairAt i).1, (S.stepPairAt i).2] ++ Q := by
  classical
  let p := S.stepPairAt i
  have hsplit_step :
      S.bagListAt i = splitMergedBag p.1 p.2 (S.bagListAt (i + 1)) := by
    simpa [p] using S.bagListAt_step_eq_split hi
  have hpspec := S.stepPairAt_spec hi
  have hmerge :
      (S.state (i + 1)).bags =
        insert (p.1 ∪ p.2)
          (((S.state i).bags.erase p.1).erase p.2) := by
    simpa [p] using hpspec.2.2.2
  have hmerged_state : p.1 ∪ p.2 ∈ (S.state (i + 1)).bags := by
    rw [hmerge]
    simp
  have hmerged_list : p.1 ∪ p.2 ∈ S.bagListAt (i + 1) := by
    have hmem_finset : p.1 ∪ p.2 ∈ (S.bagListAt (i + 1)).toFinset := by
      rw [S.bagListAt_toFinset (by omega : i + 1 ≤ S.stepCount)]
      exact hmerged_state
    exact List.mem_toFinset.mp hmem_finset
  rcases exists_splitMergedBag_eq_append_of_mem_nodup
      (S.bagListAt_nodup (by omega : i + 1 ≤ S.stepCount)) hmerged_list with
    ⟨P, Q, hnext, _hnotP, _hnotQ, hsplit⟩
  refine ⟨P, Q, ?_, ?_⟩
  · simpa [p] using hnext
  · rw [hsplit_step, hsplit]

/-- The matrix division whose row and column parts are the leaf-order interval
certificates for two times of the graph contraction sequence. -/
noncomputable def matrixDivisionAtTimes
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d)
    (rowTime colTime : ℕ)
    (hrowTime : rowTime ≤ S.stepCount) (hcolTime : colTime ≤ S.stepCount) :
    Matrix.MatrixDivision (Fintype.card V) (Fintype.card V) :=
  S.matrixDivisionOfBagListsWithCuts
    (S.bagListDivisionAt rowTime hrowTime)
    (S.bagListDivisionAt colTime hcolTime)
    (S.stepCount - rowTime) (S.stepCount - colTime)
    (S.bagListAt_length_eq_stepCount_sub_add_one hrowTime)
    (S.bagListAt_length_eq_stepCount_sub_add_one hcolTime)

/-- Error transfer for the time-indexed matrix division used in the interleaved
row/column sequence. -/
theorem matrixDivisionAtTimes_nonconstantErrorValueAtMost
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d t : ℕ}
    (S : ContractionSequence G d)
    {rowTime colTime : ℕ}
    (hrowTime : rowTime ≤ S.stepCount) (hcolTime : colTime ≤ S.stepCount)
    (herr :
      Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
        (S.matrixPartitionOfTwoStates S.leafOrder rowTime colTime) t) :
    Matrix.MatrixDivision.NonconstantErrorValueAtMost
      (Matrix.orderedAdjacency G S.leafOrder)
      (S.matrixDivisionAtTimes rowTime colTime hrowTime hcolTime) t := by
  simpa [matrixDivisionAtTimes] using
    S.nonconstantErrorValueAtMost_matrixDivisionOfBagListsWithCuts
      hrowTime hcolTime
      (S.bagListDivisionAt rowTime hrowTime)
      (S.bagListDivisionAt colTime hcolTime)
      (S.bagListAt_length_eq_stepCount_sub_add_one hrowTime)
      (S.bagListAt_length_eq_stepCount_sub_add_one hcolTime) herr

/-- The interleaved matrix division sequence associated with a graph
contraction sequence: at even times both axes use the same graph state; at odd
times the row axis has performed the next contraction and the column axis is
its mirror awaiting the matching column fusion. -/
noncomputable def matrixSequenceDivision
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) (s : ℕ) :
    Matrix.MatrixDivision (Fintype.card V) (Fintype.card V) :=
  if hs : s ≤ 2 * S.stepCount then
    S.matrixDivisionAtTimes ((s + 1) / 2) (s / 2)
      (by
        rw [Nat.div_le_iff_le_mul (by decide : 0 < 2)]
        omega)
      (Nat.div_le_of_le_mul (by omega : s ≤ 2 * S.stepCount))
  else
    S.matrixDivisionAtTimes S.stepCount S.stepCount le_rfl le_rfl

theorem matrixSequenceDivision_even
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i ≤ S.stepCount) :
    S.matrixSequenceDivision (2 * i) =
      S.matrixDivisionAtTimes i i hi hi := by
  classical
  unfold matrixSequenceDivision
  have hs : 2 * i ≤ 2 * S.stepCount := by omega
  have hrow : (2 * i + 1) / 2 = i := by
    simpa using Nat.mul_add_div (m := 2) (by decide : 0 < 2) i 1
  have hcol : (2 * i) / 2 = i := Nat.mul_div_right _ (by decide : 0 < 2)
  simp [hs, hrow, hcol]

theorem matrixSequenceDivision_odd
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    S.matrixSequenceDivision (2 * i + 1) =
      S.matrixDivisionAtTimes (i + 1) i (by omega) (by omega) := by
  classical
  unfold matrixSequenceDivision
  have hs : 2 * i + 1 ≤ 2 * S.stepCount := by omega
  have hrow : (2 * i + 1 + 1) / 2 = i + 1 := by
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega]
    exact Nat.mul_div_right _ (by decide : 0 < 2)
  have hcol : (2 * i + 1) / 2 = i := by
    simpa using Nat.mul_add_div (m := 2) (by decide : 0 < 2) i 1
  simp [hs, hrow, hcol]

/-- The even matrix step corresponding to graph step `i` fuses the two row
intervals for the contracted bags. -/
theorem hasRowFusion_matrixDivisionAtTimes_step
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    Matrix.MatrixDivision.HasRowFusion
      (S.matrixDivisionAtTimes i i (by omega) (by omega))
      (S.matrixDivisionAtTimes (i + 1) i (by omega) (by omega)) := by
  classical
  let A : Finset V := (S.stepPairAt i).1
  let B : Finset V := (S.stepPairAt i).2
  rcases S.exists_bagListAt_succ_eq_append_merge hi with ⟨P, Q, hnext, hcur⟩
  let Rcur : S.BagListDivision (P ++ [A, B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt i (by omega : i ≤ S.stepCount)) (by simpa [A, B] using hcur)
  let Rnext : S.BagListDivision (P ++ [A ∪ B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt (i + 1) (by omega : i + 1 ≤ S.stepCount))
        (by simpa [A, B] using hnext)
  let C : S.BagListDivision (P ++ [A, B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt i (by omega : i ≤ S.stepCount)) (by simpa [A, B] using hcur)
  have hC : (P ++ [A, B] ++ Q).length = (P.length + Q.length + 1) + 1 := by
    simp
    omega
  have hcurCuts : S.stepCount - i = P.length + Q.length + 1 := by
    have hlen := S.bagListAt_length_eq_stepCount_sub_add_one
      (i := i) (by omega : i ≤ S.stepCount)
    have hcurLen : (S.bagListAt i).length = P.length + Q.length + 2 := by
      rw [hcur]
      simp
      omega
    omega
  have hnextCuts : S.stepCount - (i + 1) = P.length + Q.length := by
    have hlen := S.bagListAt_length_eq_stepCount_sub_add_one
      (i := i + 1) (by omega : i + 1 ≤ S.stepCount)
    have hnextLen : (S.bagListAt (i + 1)).length = P.length + Q.length + 1 := by
      rw [hnext]
      simp
      omega
    omega
  refine ⟨?_, ?_, ⟨P.length, ?_⟩, ?_, ?_⟩
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hcurCuts, hnextCuts]
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hcurCuts]
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hnextCuts]
    omega
  · convert (BagListDivision.isFusionAt_of_adjacent_merge (S := S) Rcur Rnext) using 1
    · simp only [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, Rcur,
        BagListDivision.castList, Division.castIndex_castIndex]
      exact S.bagListDivisionAt_castIndex_div_heq
        (by omega : i ≤ S.stepCount) (by omega : i ≤ S.stepCount) _ _
    · simp only [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, Rnext,
        BagListDivision.castList, Division.castIndex_castIndex]
      exact S.bagListDivisionAt_castIndex_div_heq
        (by omega : i + 1 ≤ S.stepCount) (by omega : i + 1 ≤ S.stepCount) _ _
    · apply fin_heq_of_val_eq
      · omega
      · rfl
  · intro j
    simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hcurCuts,
      Division.castIndex_castIndex]

/-- The odd matrix step corresponding to graph step `i` mirrors the same
contraction as a column fusion. -/
theorem hasColFusion_matrixDivisionAtTimes_step
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    Matrix.MatrixDivision.HasColFusion
      (S.matrixDivisionAtTimes (i + 1) i (by omega) (by omega))
      (S.matrixDivisionAtTimes (i + 1) (i + 1) (by omega) (by omega)) := by
  classical
  let A : Finset V := (S.stepPairAt i).1
  let B : Finset V := (S.stepPairAt i).2
  rcases S.exists_bagListAt_succ_eq_append_merge hi with ⟨P, Q, hnext, hcur⟩
  let R : S.BagListDivision (P ++ [A ∪ B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt (i + 1) (by omega : i + 1 ≤ S.stepCount))
        (by simpa [A, B] using hnext)
  let Ccur : S.BagListDivision (P ++ [A, B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt i (by omega : i ≤ S.stepCount)) (by simpa [A, B] using hcur)
  let Cnext : S.BagListDivision (P ++ [A ∪ B] ++ Q) :=
    BagListDivision.castList (S := S)
      (S.bagListDivisionAt (i + 1) (by omega : i + 1 ≤ S.stepCount))
        (by simpa [A, B] using hnext)
  have hR : (P ++ [A ∪ B] ++ Q).length = (P.length + Q.length) + 1 := by
    simp
    omega
  have hcurCuts : S.stepCount - i = P.length + Q.length + 1 := by
    have hlen := S.bagListAt_length_eq_stepCount_sub_add_one
      (i := i) (by omega : i ≤ S.stepCount)
    have hcurLen : (S.bagListAt i).length = P.length + Q.length + 2 := by
      rw [hcur]
      simp
      omega
    omega
  have hnextCuts : S.stepCount - (i + 1) = P.length + Q.length := by
    have hlen := S.bagListAt_length_eq_stepCount_sub_add_one
      (i := i + 1) (by omega : i + 1 ≤ S.stepCount)
    have hnextLen : (S.bagListAt (i + 1)).length = P.length + Q.length + 1 := by
      rw [hnext]
      simp
      omega
    omega
  refine ⟨?_, ?_, ⟨P.length, ?_⟩, ?_, ?_⟩
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hnextCuts]
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hcurCuts, hnextCuts]
  · simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hnextCuts]
    omega
  · intro j
    simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, hnextCuts,
      Division.castIndex_castIndex]
  · convert (BagListDivision.isFusionAt_of_adjacent_merge (S := S) Ccur Cnext) using 1
    · simp only [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, Ccur,
        BagListDivision.castList, Division.castIndex_castIndex]
      exact S.bagListDivisionAt_castIndex_div_heq
        (by omega : i ≤ S.stepCount) (by omega : i ≤ S.stepCount) _ _
    · simp only [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts, Cnext,
        BagListDivision.castList, Division.castIndex_castIndex]
      exact S.bagListDivisionAt_castIndex_div_heq
        (by omega : i + 1 ≤ S.stepCount) (by omega : i + 1 ≤ S.stepCount) _ _
    · apply fin_heq_of_val_eq
      · omega
      · rfl

/-- The interleaved sequence starts from the finest division: the leaf bag list
is the singleton division in the leaf order. -/
theorem matrixDivisionAtTimes_zero_isFinest
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    Matrix.MatrixDivision.IsFinest
      (S.matrixDivisionAtTimes 0 0 (by omega) (by omega)) := by
  classical
  constructor
  · intro i
    let r : Fin (Fintype.card V) :=
      Fin.cast (by
        simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts]
        exact S.stepCount_add_one_eq_card) i
    refine ⟨r, ?_⟩
    ext x
    simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts,
      bagListDivisionAt, leafBagListDivision, bagListAt, leafBagList,
      Division.castIndex, Division.singleton, r]
  · intro j
    let c : Fin (Fintype.card V) :=
      Fin.cast (by
        simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts]
        exact S.stepCount_add_one_eq_card) j
    refine ⟨c, ?_⟩
    ext x
    simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts,
      bagListDivisionAt, leafBagListDivision, bagListAt, leafBagList,
      Division.castIndex, Division.singleton, c]

/-- The interleaved sequence ends at the coarsest one-by-one division. -/
theorem matrixDivisionAtTimes_final_isCoarsest
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    Matrix.MatrixDivision.IsCoarsest
      (S.matrixDivisionAtTimes S.stepCount S.stepCount le_rfl le_rfl) := by
  constructor <;> simp [matrixDivisionAtTimes, matrixDivisionOfBagListsWithCuts]

/-- Every adjacent pair in the interleaved sequence is one exact row or column
fusion.  Even steps contract rows; odd steps mirror the same graph contraction
as a column fusion. -/
theorem matrixSequenceDivision_step_fuses
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {s : ℕ} (hs : s < 2 * S.stepCount) :
    Matrix.MatrixDivision.HasExactFusion
      (S.matrixSequenceDivision s) (S.matrixSequenceDivision (s + 1)) := by
  classical
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · let i := s / 2
    have hs_eq : s = 2 * i := by
      have h := Nat.div_add_mod s 2
      omega
    have hi : i < S.stepCount := by omega
    rw [hs_eq]
    rw [S.matrixSequenceDivision_even (i := i) (by omega : i ≤ S.stepCount)]
    rw [S.matrixSequenceDivision_odd (i := i) hi]
    exact Or.inl (S.hasRowFusion_matrixDivisionAtTimes_step hi)
  · let i := s / 2
    have hs_eq : s = 2 * i + 1 := by
      have h := Nat.div_add_mod s 2
      omega
    have hi : i < S.stepCount := by omega
    have hi_next : i + 1 ≤ S.stepCount := by omega
    rw [hs_eq]
    rw [S.matrixSequenceDivision_odd (i := i) hi]
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega]
    rw [S.matrixSequenceDivision_even (i := i + 1) hi_next]
    exact Or.inr (S.hasColFusion_matrixDivisionAtTimes_step hi)

/-- Every division in the interleaved sequence has nonconstant error at most
`d + 3`.  At even times this is the symmetric trigraph-state partition; at odd
times it is the one-sided partition before the mirrored column fusion. -/
theorem matrixSequenceDivision_errorValueAtMost
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {s : ℕ} (hs : s ≤ 2 * S.stepCount) :
    Matrix.MatrixDivision.NonconstantErrorValueAtMost
      (Matrix.orderedAdjacency G S.leafOrder)
      (S.matrixSequenceDivision s) (d + 3) := by
  classical
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · let i := s / 2
    have hs_eq : s = 2 * i := by
      have h := Nat.div_add_mod s 2
      omega
    have hi : i ≤ S.stepCount := by omega
    rw [hs_eq]
    rw [S.matrixSequenceDivision_even (i := i) hi]
    have herr_state :
        Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
          (S.matrixPartitionOfState S.leafOrder i) (d + 1) :=
      S.matrixPartitionOfState_errorValueAtMost S.leafOrder hi
    have herr_two :
        Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
          (S.matrixPartitionOfTwoStates S.leafOrder i i) (d + 1) := by
      rw [S.matrixPartitionOfTwoStates_self_eq S.leafOrder i]
      exact herr_state
    have herr_wide :
        Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
          (S.matrixPartitionOfTwoStates S.leafOrder i i) (d + 3) :=
      Matrix.MatrixPartition.errorValueAtMost_mono (by omega : d + 1 ≤ d + 3) herr_two
    exact S.matrixDivisionAtTimes_nonconstantErrorValueAtMost hi hi herr_wide
  · let i := s / 2
    have hs_eq : s = 2 * i + 1 := by
      have h := Nat.div_add_mod s 2
      omega
    have hi : i < S.stepCount := by omega
    rw [hs_eq]
    rw [S.matrixSequenceDivision_odd (i := i) hi]
    have herr :
        Matrix.ErrorValueAtMost (Matrix.orderedAdjacency G S.leafOrder)
          (S.matrixPartitionOfTwoStates S.leafOrder (i + 1) i) (d + 3) :=
      S.matrixPartitionOfAdjacentStates_errorValueAtMost S.leafOrder hi
    exact S.matrixDivisionAtTimes_nonconstantErrorValueAtMost
      (by omega : i + 1 ≤ S.stepCount) (by omega : i ≤ S.stepCount) herr

/-- The division sequence extracted from a graph contraction sequence by using
the left-to-right leaf order and mirroring every graph contraction as a row
fusion followed by the matching column fusion. -/
noncomputable def matrixSequenceOfContractionSequence
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    Matrix.BoundedErrorValueDivisionSequence
      (Matrix.orderedAdjacency G S.leafOrder) (d + 3) where
  stepCount := 2 * S.stepCount
  division := S.matrixSequenceDivision
  starts := by
    rw [S.matrixSequenceDivision_even (i := 0) (by omega : 0 ≤ S.stepCount)]
    exact S.matrixDivisionAtTimes_zero_isFinest
  ends := by
    rw [S.matrixSequenceDivision_even (i := S.stepCount) le_rfl]
    exact S.matrixDivisionAtTimes_final_isCoarsest
  step_fuses := by
    intro s hs
    exact S.matrixSequenceDivision_step_fuses hs
  errorValue_le := by
    intro s hs
    exact S.matrixSequenceDivision_errorValueAtMost hs

end ContractionSequence

/-- A graph twin-decomposition at width `d`, represented only by the data
needed for the mixed-minor direction: the left-to-right leaf order of the
contraction tree and the proof that the ordered adjacency matrix is
`d`-twin-ordered.

The empty graph is a harmless zerology case: the division-sequence definition
of `MatrixTwinOrderedAtMost` has at least one row and column part, so a
`0 × 0` matrix is handled by the explicit `isEmpty` alternative. -/
structure TwinDecomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) where
  /-- The left-to-right order on leaves of the contraction tree. -/
  order : VertexOrder V (Fintype.card V)
  /-- Either the graph has no vertices, or in the leaf order the ordered
  adjacency matrix is `(d+3)`-twin-ordered.  The additive constant records the
  formal diagonal/self-zone convention and the two one-sided child zones that
  appear while a graph contraction is mirrored as one row fusion followed by
  one column fusion. -/
  empty_or_orderedAdjacency_twinOrdered :
    Fintype.card V = 0 ∨
      Matrix.MatrixTwinOrderedAtMost (Matrix.orderedAdjacency G order) (d + 3)

/-- The empty graph has the degenerate twin-decomposition certificate. -/
noncomputable def twinDecompositionOfCardEqZero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {d : ℕ} (hV : Fintype.card V = 0) :
    TwinDecomposition G d where
  order := ⟨(Fintype.equivFin V).symm⟩
  empty_or_orderedAdjacency_twinOrdered := Or.inl hV

/-- A contraction sequence gives a twin-decomposition: the vertex order is the
left-to-right order on the leaves of the contraction tree, and every graph
contraction is mirrored by a row fusion followed by a column fusion. -/
noncomputable def twinDecompositionOfContractionSequence
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    TwinDecomposition G d := by
  classical
  by_cases hV : Fintype.card V = 0
  · exact twinDecompositionOfCardEqZero G hV
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    exact
      { order := S.leafOrder
        empty_or_orderedAdjacency_twinOrdered :=
          Or.inr ⟨S.matrixSequenceOfContractionSequence⟩ }

/-- Every finite graph has the leaf-order twin-decomposition at its twin-width. -/
noncomputable def twinDecomposition_twinWidth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    TwinDecomposition G (twinWidth G) := by
  let S : ContractionSequence G (twinWidth G) :=
    Classical.choice (hasTwinWidthAtMost_twinWidth' G)
  exact twinDecompositionOfContractionSequence S

/-- The leaf order of a width-`d` twin-decomposition gives the first item of
Theorem 10 for graphs. -/
theorem mixedMinorNumber_le_of_twinDecomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (D : TwinDecomposition G d) :
    mixedMinorNumber G ≤ 2 * (d + 3) + 2 := by
  rcases D.empty_or_orderedAdjacency_twinOrdered with hcard | htwin
  · have hmix : mixedMinorNumber G = 0 := by
      exact Nat.eq_zero_of_le_zero (by simpa [hcard] using mixedMinorNumber_le_card G)
    rw [hmix]
    omega
  · have hmatrix :
        Matrix.orderedAdjacencyMixedNumber G D.order ≤ 2 * (d + 3) + 2 := by
      simpa [Matrix.orderedAdjacencyMixedNumber] using
        Matrix.theorem10_ordered_matrix_mixed_number_le_of_twin_ordered_at_most
          (Matrix.orderedAdjacency G D.order) htwin
    exact le_trans (mixedMinorNumber_le_orderedAdjacencyMixedNumber G D.order) hmatrix

/-- If every graph admits the leaf-order twin-decomposition at its own
`twinWidth`, then mixed minor number is linearly bounded by twin-width. -/
theorem mixed_minor_number_le_twice_twin_width_plus_eight_of_twinDecomposition
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G)) :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      mixedMinorNumber G ≤ 2 * (twinWidth G + 3) + 2 := by
  intro V _ _ G
  exact mixedMinorNumber_le_of_twinDecomposition (hdecomp G)

/-- The completed twin-width-to-mixed-minor bound from the leaf order of a
contraction sequence. -/
theorem mixed_minor_number_le_twice_twin_width_plus_eight
    {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    mixedMinorNumber G ≤ 2 * (twinWidth G + 3) + 2 :=
  mixedMinorNumber_le_of_twinDecomposition (twinDecomposition_twinWidth G)

end SimpleGraph
end TwinWidth

/- ===== end Graph/TwinDecomposition.lean ===== -/

/- ===== begin Equivalence/Main.lean ===== -/

/-
# Main equivalence statement from directional bounds

This file contains the theorem-combiner layer.  The two hard mathematical
ingredients are the directional bounds recorded in the imported modules.
-/

namespace TwinWidth

open SimpleGraph

/-- The two directional bounds imply functional equivalence of twin-width and
mixed minor number. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds
    (h₁ : TwinWidthBoundedByMixedMinorNumber)
    (h₂ : MixedMinorNumberBoundedByTwinWidth) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  exact ⟨h₁, h₂⟩

/-- Functional equivalence from the hard mixed-to-twin-width bound and the
Section 5 ordered-adjacency form of the twin-width-to-mixed direction. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_mixedToTwinWidth_and_orderedAdjacency
    (h₁ : TwinWidthBoundedByMixedMinorNumber)
    (h₂ : OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  exact twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds h₁
    (mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyLinearBound h₂)

/-- Functional equivalence from the two ordered-adjacency matrix bounds supplied
by the grid-minor theorem for twin-width. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_orderedAdjacencyBounds
    (h₁ : TwinWidthBoundedByOrderedAdjacencyMixedNumberExplicit)
    (h₂ : OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  exact twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds
    (twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyExplicitBound h₁)
    (mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyLinearBound h₂)

/-- Contract theorem for
`MainContract.twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds`.

The two explicit directional inequalities imply functional equivalence. -/
theorem twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds
    (h₁ :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G))
    (h₂ :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        mixedMinorNumber G ≤ 2 * (twinWidth G + 3) + 2) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  constructor
  · refine ⟨twinWidthBoundOfMixedMinorNumber, ?_⟩
    intro V _ _ G
    exact h₁ G
  · refine ⟨fun d => 2 * (d + 3) + 2, ?_⟩
    intro V _ _ G
    exact h₂ G

/-- Functional equivalence from the two graph/matrix bridge constructions:

* the left-to-right leaf order of a width-`twinWidth G` twin-decomposition
  makes the ordered adjacency matrix twin-ordered, and
* the symmetric version of the matrix Theorem 10 construction turns every
  mixed-free ordered adjacency matrix into a graph partition sequence.

These are precisely the two graph-facing constructions described around
Theorem 14. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_graph_matrix_bridges
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G))
    (hconstruct :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
        (σ : VertexOrder V (Fintype.card V)) (t : ℕ),
          Matrix.MixedFree (Matrix.orderedAdjacency G σ) t →
            Nonempty (GraphPartitionSequence G (theorem14MixedFreeTwinWidthBound t))) :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds
    (fun G => theorem14_twinWidth_le_mixedMinorNumber G (hconstruct G))
    (mixed_minor_number_le_twice_twin_width_plus_eight_of_twinDecomposition hdecomp)

/-- Functional equivalence from the two remaining natural-language
constructions:

* the left-to-right leaf order of a width-`twinWidth G` twin-decomposition
  makes the ordered adjacency matrix twin-ordered, and
* the mirrored matrix Theorem 10 construction gives symmetric matrix
  contraction sequences for mixed-free square Boolean matrices.

The graph interpretation of the symmetric matrix sequence is proved in
`Graph.Theorem14`. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition_and_symmetricMatrix
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G))
    (hmatrix : Matrix.SymmetricMatrixTwinWidthBoundedByMixedFree) :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds
    (fun G =>
      theorem14_twinWidth_le_mixedMinorNumber_of_symmetricMatrixConstruction G
        (fun σ t hfree => by
          simpa [theorem14MixedFreeTwinWidthBound] using
            hmatrix (Matrix.orderedAdjacency G σ)
              (orderedAdjacency_isSymmetricMatrix G σ) hfree))
    (mixed_minor_number_le_twice_twin_width_plus_eight_of_twinDecomposition hdecomp)

/-- Functional equivalence from the leaf-order twin-decomposition and the
remaining symmetric refinement constructor.  The expansion of that symmetric
refinement sequence into paired row/column matrix contractions is proved in
`Matrix.Symmetric`. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition_and_symmetricErrorRefinement
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G))
    (hrefine : Matrix.SymmetricMatrixErrorRefinementBoundedByMixedFree) :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition_and_symmetricMatrix
    hdecomp
    (Matrix.symmetricMatrixTwinWidthBoundedByMixedFree_of_symmetricErrorRefinement hrefine)

/-- Functional equivalence with the mirrored matrix/Theorem 14 side fully
discharged.  The only remaining graph-facing construction is the leaf-order
twin-decomposition for the twin-width-to-mixed direction. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition
    (hdecomp :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        TwinDecomposition G (twinWidth G)) :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds
    SimpleGraph.twinWidthBoundedByMixedMinorNumber
    ⟨mixedMinorNumberBoundOfTwinWidth,
      mixed_minor_number_le_twice_twin_width_plus_eight_of_twinDecomposition hdecomp⟩

/-- The completed functional equivalence between graph twin-width and graph
mixed minor number. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber :
    FunctionallyEquivalent twinWidth mixedMinorNumber :=
  twinWidth_functionallyEquivalent_mixedMinorNumber_of_twinDecomposition
    SimpleGraph.twinDecomposition_twinWidth

end TwinWidth

/- ===== end Equivalence/Main.lean ===== -/

/- ===== begin Equivalence/MainContract.lean ===== -/

/-
# Contract statement for the main equivalence theorem

This file exposes the final graph-parameter statement: twin-width and mixed
minor number are functionally equivalent for finite simple graphs.
-/

namespace TwinWidth
namespace MainContract

/-- Twin-width and mixed minor number are functionally equivalent finite-graph
parameters. -/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    FunctionallyEquivalent SimpleGraph.twinWidth SimpleGraph.mixedMinorNumber := by
  exact TwinWidth.twinWidth_functionallyEquivalent_mixedMinorNumber

end MainContract
end TwinWidth

/- ===== end Equivalence/MainContract.lean ===== -/

end Lax2.Source
