import Lax2Proofs.Source.TwinWidth.Contraction.TwinWidth

/-!
# Graph partitions and trigraph states

This file builds the graph-side partition language used by Theorem 14.  A
partition of the original vertex set determines a trigraph state: black edges
join complete homogeneous pairs of parts, red edges join non-homogeneous pairs
of parts, and empty homogeneous pairs carry neither color.
-/

namespace Lax2Proofs.TwinWidth
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
end Lax2Proofs.TwinWidth
