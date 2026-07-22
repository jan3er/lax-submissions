import Lax1Proofs.Source.TwinWidth.Graph.BonnetDepresLower
import Lax1.ExponentialSeparation

/-!
# Bridge to the submitted concepts

The source development phrases contraction sequences as trigraph states that
carry black and red adjacency data updated by explicit contraction rules; the
submitted concepts phrase them as bare partition sequences whose red degrees
are derived from homogeneity in the graph.  The bridge rests on the standard
invariant that along any contraction sequence a pair of distinct bags is
black exactly when the graph is complete between them and red exactly when it
is not homogeneous between them.  Both directions are proved below, and the
treewidth upper bound and twin-width lower bound transport across them.
-/

namespace Lax1Proofs.Main

noncomputable section

variable {V : Type} {G : SimpleGraph V}

/-! ## Complete, empty, and homogeneous pairs -/

/-- Every pair of vertices across `A` and `B` is adjacent. -/
def CompleteBetween (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

/-- No pair of vertices across `A` and `B` is adjacent. -/
def EmptyBetween (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

theorem homogeneous_iff {A B : Finset V} :
    Lax1.TwinWidth.Homogeneous G A B ↔
      CompleteBetween G A B ∨ EmptyBetween G A B :=
  Iff.rfl

theorem completeBetween_comm {A B : Finset V} :
    CompleteBetween G A B ↔ CompleteBetween G B A :=
  ⟨fun h b hb a ha => (h a ha b hb).symm, fun h a ha b hb => (h b hb a ha).symm⟩

theorem emptyBetween_comm {A B : Finset V} :
    EmptyBetween G A B ↔ EmptyBetween G B A :=
  ⟨fun h b hb a ha hadj => h a ha b hb hadj.symm,
   fun h a ha b hb hadj => h b hb a ha hadj.symm⟩

theorem homogeneous_comm {A B : Finset V} :
    Lax1.TwinWidth.Homogeneous G A B ↔ Lax1.TwinWidth.Homogeneous G B A := by
  rw [homogeneous_iff, homogeneous_iff, completeBetween_comm, emptyBetween_comm]

theorem completeBetween_union_left [DecidableEq V] {A B Y : Finset V} :
    CompleteBetween G (A ∪ B) Y ↔
      CompleteBetween G A Y ∧ CompleteBetween G B Y := by
  unfold CompleteBetween
  constructor
  · intro h
    exact ⟨fun a ha => h a (Finset.mem_union_left _ ha),
           fun b hb => h b (Finset.mem_union_right _ hb)⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact h1 x h
    · exact h2 x h

theorem emptyBetween_union_left [DecidableEq V] {A B Y : Finset V} :
    EmptyBetween G (A ∪ B) Y ↔ EmptyBetween G A Y ∧ EmptyBetween G B Y := by
  unfold EmptyBetween
  constructor
  · intro h
    exact ⟨fun a ha => h a (Finset.mem_union_left _ ha),
           fun b hb => h b (Finset.mem_union_right _ hb)⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact h1 x h
    · exact h2 x h

theorem not_completeBetween_of_emptyBetween {A Y : Finset V}
    (hA : A.Nonempty) (hY : Y.Nonempty) (h : EmptyBetween G A Y) :
    ¬ CompleteBetween G A Y := by
  rcases hA with ⟨a, ha⟩
  rcases hY with ⟨y, hy⟩
  intro hc
  exact h a ha y hy (hc a ha y hy)

/-- Homogeneity of a merged pair, for nonempty parts: both halves are
homogeneous with `Y` and of the same kind. -/
theorem homogeneous_union_left [DecidableEq V] {A B Y : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hY : Y.Nonempty) :
    Lax1.TwinWidth.Homogeneous G (A ∪ B) Y ↔
      (Lax1.TwinWidth.Homogeneous G A Y ∧ Lax1.TwinWidth.Homogeneous G B Y ∧
        (CompleteBetween G A Y ↔ CompleteBetween G B Y)) := by
  rw [homogeneous_iff, homogeneous_iff (A := A), homogeneous_iff (A := B),
    completeBetween_union_left, emptyBetween_union_left]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inl h1, Or.inl h2, iff_of_true h1 h2⟩
    · exact ⟨Or.inr h1, Or.inr h2,
        iff_of_false (not_completeBetween_of_emptyBetween hA hY h1)
          (not_completeBetween_of_emptyBetween hB hY h2)⟩
  · rintro ⟨hA', hB', hiff⟩
    rcases hA' with hc | he
    · exact Or.inl ⟨hc, hiff.mp hc⟩
    · rcases hB' with hc | he'
      · exact (not_completeBetween_of_emptyBetween hA hY he (hiff.mpr hc)).elim
      · exact Or.inr ⟨he, he'⟩

theorem completeBetween_union_right [DecidableEq V] {A B X : Finset V} :
    CompleteBetween G X (A ∪ B) ↔
      CompleteBetween G X A ∧ CompleteBetween G X B := by
  rw [completeBetween_comm (A := X) (B := A ∪ B), completeBetween_union_left,
    completeBetween_comm (A := A) (B := X), completeBetween_comm (A := B) (B := X)]

/-- Homogeneity with a merged pair on the right, for nonempty parts. -/
theorem homogeneous_union_right [DecidableEq V] {A B X : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hX : X.Nonempty) :
    Lax1.TwinWidth.Homogeneous G X (A ∪ B) ↔
      (Lax1.TwinWidth.Homogeneous G X A ∧ Lax1.TwinWidth.Homogeneous G X B ∧
        (CompleteBetween G X A ↔ CompleteBetween G X B)) := by
  rw [homogeneous_comm (A := X) (B := A ∪ B),
    homogeneous_union_left hA hB hX,
    homogeneous_comm (A := A) (B := X), homogeneous_comm (A := B) (B := X),
    completeBetween_comm (A := A) (B := X),
    completeBetween_comm (A := B) (B := X)]

theorem completeBetween_singleton {a b : V} :
    CompleteBetween G {a} {b} ↔ G.Adj a b := by
  unfold CompleteBetween
  simp

theorem homogeneous_singleton (a b : V) :
    Lax1.TwinWidth.Homogeneous G {a} {b} := by
  by_cases h : G.Adj a b
  · left
    intro x hx y hy
    rw [Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact h
  · right
    intro x hx y hy
    rw [Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact h

/-! ## Treewidth -/

/-- A source tree decomposition is a submitted one after forgetting the
decidability field. -/
def submittedTreeDecompositionOfSource
    {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (D : TwinWidth.SimpleGraph.TreeDecomposition G) :
    Lax1.Treewidth.TreeDecomposition G where
  Node := D.Node
  nodeFintype := D.nodeFintype
  tree := D.tree
  isTree := D.isTree
  bag := D.bag
  vertex_mem_bag := D.vertex_mem_bag
  edge_mem_bag := D.edge_mem_bag
  bag_indices_connected := D.bag_indices_connected

theorem treewidth_le_of_source
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w : ℕ}
    (D : TwinWidth.SimpleGraph.TreeDecomposition G)
    (hwidth : D.width ≤ w) :
    Lax1.Treewidth.treewidth G ≤ w := by
  have hbag : ∀ i : D.Node, (D.bag i).card ≤ w + 1 := by
    intro i
    letI : Fintype D.Node := D.nodeFintype
    have hle : (D.bag i).card ≤ Finset.univ.sup fun j : D.Node => (D.bag j).card :=
      Finset.le_sup (f := fun j : D.Node => (D.bag j).card) (Finset.mem_univ i)
    have hw : (Finset.univ.sup fun j : D.Node => (D.bag j).card) - 1 ≤ w := hwidth
    omega
  exact Nat.sInf_le ⟨submittedTreeDecompositionOfSource D, hbag⟩

/-! ## Faithful trigraph states

A trigraph state is faithful to `G` when its black and red relations agree,
on distinct bags, with completeness and non-homogeneity in `G`.  Initial
states are faithful and contraction steps preserve faithfulness, so every
state of a source contraction sequence is faithful.
-/

/-- The trigraph relations agree with the graph-derived relations on bags. -/
def Faithful (G : SimpleGraph V) (T : TwinWidth.TrigraphState V) : Prop :=
  ∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags → A ≠ B →
    (T.blackAdj A B ↔ CompleteBetween G A B) ∧
    (T.redAdj A B ↔ ¬ Lax1.TwinWidth.Homogeneous G A B)

theorem faithful_of_isInitialState
    [Fintype V] [DecidableEq V] {T : TwinWidth.TrigraphState V}
    (h : TwinWidth.SimpleGraph.IsInitialState G T) : Faithful G T := by
  intro A B hA hB hAB
  have hA' := hA
  have hB' := hB
  rw [h.1, TwinWidth.TrigraphState.mem_singletonBags] at hA' hB'
  obtain ⟨a, rfl⟩ := hA'
  obtain ⟨b, rfl⟩ := hB'
  constructor
  · rw [h.2.1 hA hB, completeBetween_singleton]
    simp
  · rw [iff_false_intro (h.2.2 hA hB), false_iff, not_not]
    exact homogeneous_singleton a b

/-- Members of the merged bag family are the union or old bags distinct from
the merged parts. -/
theorem mem_merged_iff [DecidableEq V] {T : TwinWidth.TrigraphState V}
    {A B Z : Finset V} :
    Z ∈ insert (A ∪ B) ((T.bags.erase A).erase B) ↔
      Z = A ∪ B ∨ (Z ∈ T.bags ∧ Z ≠ A ∧ Z ≠ B) := by
  constructor
  · intro hZ
    rcases Finset.mem_insert.mp hZ with h | h
    · exact Or.inl h
    · have h1 := Finset.mem_erase.mp h
      have h2 := Finset.mem_erase.mp h1.2
      exact Or.inr ⟨h2.2, h2.1, h1.1⟩
  · rintro (rfl | ⟨hZ, hZA, hZB⟩)
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hZB, Finset.mem_erase.mpr ⟨hZA, hZ⟩⟩)

/-- An old bag distinct from both merged parts differs from their union. -/
theorem rest_ne_union [DecidableEq V] {T : TwinWidth.TrigraphState V}
    {A B Z : Finset V} (hA : A ∈ T.bags)
    (hZ : Z ∈ T.bags) (hZA : Z ≠ A) :
    Z ≠ A ∪ B := by
  intro h
  rcases T.bag_nonempty hA with ⟨a, ha⟩
  have haZ : a ∈ Z := h ▸ Finset.mem_union_left _ ha
  exact (Finset.disjoint_left.mp (T.bag_disjoint hZ hA hZA)) haZ ha

/-- On a faithful state, the contracted red relation is non-homogeneity of
the corresponding merged bags. -/
theorem contractedRed_iff [DecidableEq V]
    {T : TwinWidth.TrigraphState V} (hT : Faithful G T)
    {A B : Finset V} (hA : A ∈ T.bags) (hB : B ∈ T.bags)
    {X Y : Finset V}
    (hX : X ∈ insert (A ∪ B) ((T.bags.erase A).erase B))
    (hY : Y ∈ insert (A ∪ B) ((T.bags.erase A).erase B))
    (hXY : X ≠ Y) :
    TwinWidth.SimpleGraph.contractedRed T A B X Y ↔
      ¬ Lax1.TwinWidth.Homogeneous G X Y := by
  have hAne : A.Nonempty := T.bag_nonempty hA
  have hBne : B.Nonempty := T.bag_nonempty hB
  rcases mem_merged_iff.mp hX with hXu | ⟨hXb, hXA, hXB⟩
  · rcases mem_merged_iff.mp hY with hYu | ⟨hYb, hYA, hYB⟩
    · exact absurd (hXu.trans hYu.symm) hXY
    · subst hXu
      have hYne : Y.Nonempty := T.bag_nonempty hYb
      have h1 := hT hA hYb (Ne.symm hYA)
      have h2 := hT hB hYb (Ne.symm hYB)
      rw [TwinWidth.SimpleGraph.contractedRed, if_neg hXY, if_pos rfl,
        propext h1.1, propext h1.2, propext h2.1, propext h2.2,
        homogeneous_union_left hAne hBne hYne, ne_eq, eq_iff_iff,
        not_and_or, not_and_or]
  · rcases mem_merged_iff.mp hY with hYu | ⟨hYb, hYA, hYB⟩
    · subst hYu
      have hXne : X.Nonempty := T.bag_nonempty hXb
      have h1 := hT hXb hA hXA
      have h2 := hT hXb hB hXB
      have hXu : X ≠ A ∪ B := rest_ne_union hA hXb hXA
      rw [TwinWidth.SimpleGraph.contractedRed, if_neg hXY, if_neg hXu,
        if_pos rfl, propext h1.1, propext h1.2, propext h2.1, propext h2.2,
        homogeneous_union_right hAne hBne hXne, ne_eq, eq_iff_iff,
        not_and_or, not_and_or]
    · have hXu : X ≠ A ∪ B := rest_ne_union hA hXb hXA
      have hYu : Y ≠ A ∪ B := rest_ne_union hA hYb hYA
      rw [TwinWidth.SimpleGraph.contractedRed, if_neg hXY, if_neg hXu,
        if_neg hYu]
      exact (hT hXb hYb hXY).2

/-- On a faithful state, the contracted black relation is completeness of the
corresponding merged bags. -/
theorem contractedBlack_iff [DecidableEq V]
    {T : TwinWidth.TrigraphState V} (hT : Faithful G T)
    {A B : Finset V} (hA : A ∈ T.bags) (hB : B ∈ T.bags)
    {X Y : Finset V}
    (hX : X ∈ insert (A ∪ B) ((T.bags.erase A).erase B))
    (hY : Y ∈ insert (A ∪ B) ((T.bags.erase A).erase B))
    (hXY : X ≠ Y) :
    TwinWidth.SimpleGraph.contractedBlack T A B X Y ↔
      CompleteBetween G X Y := by
  have hAne : A.Nonempty := T.bag_nonempty hA
  have hBne : B.Nonempty := T.bag_nonempty hB
  have hred := contractedRed_iff hT hA hB hX hY hXY
  rcases mem_merged_iff.mp hX with hXu | ⟨hXb, hXA, hXB⟩
  · rcases mem_merged_iff.mp hY with hYu | ⟨hYb, hYA, hYB⟩
    · exact absurd (hXu.trans hYu.symm) hXY
    · subst hXu
      have hYne : Y.Nonempty := T.bag_nonempty hYb
      have h1 := hT hA hYb (Ne.symm hYA)
      have h2 := hT hB hYb (Ne.symm hYB)
      rw [TwinWidth.SimpleGraph.contractedBlack, if_neg hXY, if_pos rfl,
        propext hred, propext h1.1, propext h2.1,
        completeBetween_union_left]
      constructor
      · rintro ⟨hcA, hcB, -⟩
        exact ⟨hcA, hcB⟩
      · rintro ⟨hcA, hcB⟩
        refine ⟨hcA, hcB, ?_⟩
        rw [not_not, homogeneous_union_left hAne hBne hYne]
        exact ⟨Or.inl hcA, Or.inl hcB, iff_of_true hcA hcB⟩
  · rcases mem_merged_iff.mp hY with hYu | ⟨hYb, hYA, hYB⟩
    · subst hYu
      have hXne : X.Nonempty := T.bag_nonempty hXb
      have h1 := hT hXb hA hXA
      have h2 := hT hXb hB hXB
      have hXu : X ≠ A ∪ B := rest_ne_union hA hXb hXA
      rw [TwinWidth.SimpleGraph.contractedBlack, if_neg hXY, if_neg hXu,
        if_pos rfl, propext hred, propext h1.1, propext h2.1,
        completeBetween_union_right]
      constructor
      · rintro ⟨hcA, hcB, -⟩
        exact ⟨hcA, hcB⟩
      · rintro ⟨hcA, hcB⟩
        refine ⟨hcA, hcB, ?_⟩
        rw [not_not, homogeneous_union_right hAne hBne hXne]
        exact ⟨Or.inl hcA, Or.inl hcB, iff_of_true hcA hcB⟩
    · have hXu : X ≠ A ∪ B := rest_ne_union hA hXb hXA
      have hYu : Y ≠ A ∪ B := rest_ne_union hA hYb hYA
      rw [TwinWidth.SimpleGraph.contractedBlack, if_neg hXY, if_neg hXu,
        if_neg hYu]
      exact (hT hXb hYb hXY).1

/-- Contraction steps preserve faithfulness. -/
theorem faithful_step [DecidableEq V]
    {T U : TwinWidth.TrigraphState V} (hT : Faithful G T)
    (h : TwinWidth.SimpleGraph.IsContractionStep T U) : Faithful G U := by
  obtain ⟨A, hA, B, hB, hAB, hbags, hred, hblack⟩ := h
  intro X Y hX hY hXY
  have hX' : X ∈ insert (A ∪ B) ((T.bags.erase A).erase B) := hbags ▸ hX
  have hY' : Y ∈ insert (A ∪ B) ((T.bags.erase A).erase B) := hbags ▸ hY
  constructor
  · rw [hblack hX hY]
    exact contractedBlack_iff hT hA hB hX' hY' hXY
  · rw [hred hX hY]
    exact contractedRed_iff hT hA hB hX' hY' hXY

/-- Every state of a source contraction sequence is faithful. -/
theorem faithful_state [Fintype V] [DecidableEq V] {d : ℕ}
    (S : TwinWidth.SimpleGraph.ContractionSequence G d) :
    ∀ i, i ≤ S.stepCount → Faithful G (S.state i) := by
  intro i
  induction i with
  | zero => exact fun _ => faithful_of_isInitialState S.starts
  | succ i ih =>
      intro hi
      have hlt : i < S.stepCount := by omega
      exact faithful_step (ih (by omega)) (S.step_contracts i hlt)

/-- On faithful states the submitted red degree equals the source red
degree. -/
theorem redDegree_eq_of_faithful [DecidableEq V]
    {T : TwinWidth.TrigraphState V} (hT : Faithful G T)
    {A : Finset V} (hA : A ∈ T.bags) :
    Lax1.TwinWidth.redDegree G T.bags A = T.redDegree A := by
  classical
  unfold Lax1.TwinWidth.redDegree TwinWidth.TrigraphState.redDegree
  rw [show {B | B ∈ T.bags ∧ B ≠ A ∧ ¬ Lax1.TwinWidth.Homogeneous G A B} =
      ↑(T.bags.filter fun B => T.redAdj A B) from ?_]
  · exact Set.ncard_coe_finset _
  ext B
  simp only [Set.mem_setOf_eq, Finset.coe_filter]
  constructor
  · rintro ⟨hB, hne, hnh⟩
    exact ⟨hB, (hT hA hB (Ne.symm hne)).2.mpr hnh⟩
  · rintro ⟨hB, hr⟩
    have hne : B ≠ A := by
      rintro rfl
      exact T.red_irrefl hB hr
    exact ⟨hB, hne, (hT hA hB (Ne.symm hne)).2.mp hr⟩

/-! ## From source sequences to submitted sequences -/

/-- The bag families of a source contraction sequence form a submitted
partition-based contraction sequence of the same width. -/
def submittedOfSource [Fintype V] [DecidableEq V] {d : ℕ}
    (S : TwinWidth.SimpleGraph.ContractionSequence G d) :
    Lax1.TwinWidth.ContractionSequence G d where
  stepCount := S.stepCount
  partition i := (S.state i).bags
  starts := S.starts.1
  ends := S.ends
  step_merges i hi := by
    obtain ⟨A, hA, B, hB, hAB, hbags, -, -⟩ := S.step_contracts i hi
    exact ⟨A, hA, B, hB, hAB, hbags⟩
  redDegree_le i hi A hA := by
    rw [redDegree_eq_of_faithful (faithful_state S i hi) hA]
    exact S.redDegree_le i hi hA

/-! ## From submitted sequences to source sequences -/

/-- The parts are nonempty, pairwise disjoint, and cover the vertex set. -/
def IsPartitionFamily (P : Finset (Finset V)) : Prop :=
  (∀ ⦃A⦄, A ∈ P → A.Nonempty) ∧
    (∀ ⦃A B⦄, A ∈ P → B ∈ P → A ≠ B → Disjoint A B) ∧
    (∀ v : V, ∃ A ∈ P, v ∈ A)

theorem isPartitionFamily_singletonPartition [Fintype V] [DecidableEq V] :
    IsPartitionFamily (Lax1.TwinWidth.singletonPartition V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    rcases TwinWidth.TrigraphState.mem_singletonBags.mp hA with ⟨v, rfl⟩
    exact ⟨v, Finset.mem_singleton_self v⟩
  · intro A B hA hB hAB
    rcases TwinWidth.TrigraphState.mem_singletonBags.mp hA with ⟨v, rfl⟩
    rcases TwinWidth.TrigraphState.mem_singletonBags.mp hB with ⟨w, rfl⟩
    rw [Finset.disjoint_singleton]
    intro h
    exact hAB (by rw [h])
  · intro v
    exact ⟨{v}, TwinWidth.TrigraphState.mem_singletonBags.mpr ⟨v, rfl⟩,
      Finset.mem_singleton_self v⟩

theorem isPartitionFamily_merge [DecidableEq V] {P : Finset (Finset V)}
    (hP : IsPartitionFamily P) {A B : Finset V}
    (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B) :
    IsPartitionFamily (insert (A ∪ B) ((P.erase A).erase B)) := by
  have hmem : ∀ {Z : Finset V}, Z ∈ (P.erase A).erase B →
      Z ∈ P ∧ Z ≠ A ∧ Z ≠ B := by
    intro Z hZ
    have h1 := Finset.mem_erase.mp hZ
    have h2 := Finset.mem_erase.mp h1.2
    exact ⟨h2.2, h2.1, h1.1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ
    rcases Finset.mem_insert.mp hZ with rfl | hZ
    · exact (hP.1 hA).mono Finset.subset_union_left
    · exact hP.1 (hmem hZ).1
  · intro X Y hX hY hXY
    rcases Finset.mem_insert.mp hX with rfl | hX
    · rcases Finset.mem_insert.mp hY with rfl | hY
      · exact absurd rfl hXY
      · obtain ⟨hYP, hYA, hYB⟩ := hmem hY
        rw [Finset.disjoint_union_left]
        exact ⟨hP.2.1 hA hYP (Ne.symm hYA), hP.2.1 hB hYP (Ne.symm hYB)⟩
    · rcases Finset.mem_insert.mp hY with rfl | hY
      · obtain ⟨hXP, hXA, hXB⟩ := hmem hX
        rw [Finset.disjoint_union_right]
        exact ⟨hP.2.1 hXP hA hXA, hP.2.1 hXP hB hXB⟩
      · exact hP.2.1 (hmem hX).1 (hmem hY).1 hXY
  · intro v
    obtain ⟨C, hC, hvC⟩ := hP.2.2 v
    by_cases hCA : C = A
    · subst hCA
      exact ⟨C ∪ B, Finset.mem_insert_self _ _, Finset.mem_union_left _ hvC⟩
    by_cases hCB : C = B
    · subst hCB
      exact ⟨A ∪ C, Finset.mem_insert_self _ _, Finset.mem_union_right _ hvC⟩
    · exact ⟨C, Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hCB, Finset.mem_erase.mpr ⟨hCA, hC⟩⟩), hvC⟩

/-- Every partition of a submitted contraction sequence is a partition
family. -/
theorem isPartitionFamily_partition [Fintype V] [DecidableEq V] {d : ℕ}
    (S : Lax1.TwinWidth.ContractionSequence G d) :
    ∀ i, i ≤ S.stepCount → IsPartitionFamily (S.partition i) := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [S.starts]
      exact isPartitionFamily_singletonPartition
  | succ i ih =>
      intro hi
      have hlt : i < S.stepCount := by omega
      obtain ⟨A, hA, B, hB, hAB, heq⟩ := S.step_merges i hlt
      rw [heq]
      exact isPartitionFamily_merge (ih (by omega)) hA hB hAB

/-- The trigraph state induced by a partition family: black is completeness,
red is non-homogeneity. -/
def stateOf (G : SimpleGraph V) (P : Finset (Finset V))
    (hP : IsPartitionFamily P) : TwinWidth.TrigraphState V where
  bags := P
  bag_nonempty := hP.1
  bag_disjoint := hP.2.1
  bag_cover := hP.2.2
  blackAdj A B := A ≠ B ∧ CompleteBetween G A B
  redAdj A B := A ≠ B ∧ ¬ Lax1.TwinWidth.Homogeneous G A B
  black_symm := fun _ _ _ _ h => ⟨h.1.symm, completeBetween_comm.mp h.2⟩
  red_symm := fun _ _ _ _ h =>
    ⟨h.1.symm, fun hh => h.2 (homogeneous_comm.mp hh)⟩
  black_irrefl := fun _ _ h => h.1 rfl
  red_irrefl := fun _ _ h => h.1 rfl
  black_red_disjoint := fun _ _ _ _ hb hr => hr.2 (Or.inl hb.2)

theorem faithful_stateOf {P : Finset (Finset V)} (hP : IsPartitionFamily P) :
    Faithful G (stateOf G P hP) := by
  intro A B _ _ hAB
  exact ⟨⟨fun h => h.2, fun h => ⟨hAB, h⟩⟩, ⟨fun h => h.2, fun h => ⟨hAB, h⟩⟩⟩

/-- The partitions of a submitted sequence, held constant after the final
step so that every index carries a partition family. -/
def clampedPartition [Fintype V] [DecidableEq V] {d : ℕ}
    (S : Lax1.TwinWidth.ContractionSequence G d) (i : ℕ) :
    Finset (Finset V) :=
  if i ≤ S.stepCount then S.partition i else S.partition S.stepCount

theorem clampedPartition_of_le [Fintype V] [DecidableEq V] {d : ℕ}
    (S : Lax1.TwinWidth.ContractionSequence G d) {i : ℕ}
    (hi : i ≤ S.stepCount) : clampedPartition S i = S.partition i :=
  if_pos hi

theorem isPartitionFamily_clampedPartition [Fintype V] [DecidableEq V] {d : ℕ}
    (S : Lax1.TwinWidth.ContractionSequence G d) (i : ℕ) :
    IsPartitionFamily (clampedPartition S i) := by
  unfold clampedPartition
  split
  · exact isPartitionFamily_partition S i ‹_›
  · exact isPartitionFamily_partition S S.stepCount le_rfl

/-- A submitted contraction sequence induces a source trigraph contraction
sequence of the same width. -/
def sourceOfSubmitted [Fintype V] [DecidableEq V] {d : ℕ}
    (S : Lax1.TwinWidth.ContractionSequence G d) :
    TwinWidth.SimpleGraph.ContractionSequence G d where
  stepCount := S.stepCount
  state i := stateOf G (clampedPartition S i)
    (isPartitionFamily_clampedPartition S i)
  starts := by
    have h0 : clampedPartition S 0 = Lax1.TwinWidth.singletonPartition V := by
      rw [clampedPartition_of_le S (Nat.zero_le _), S.starts]
    refine ⟨h0, ?_, ?_⟩
    · intro A B hA hB
      have hA' : A ∈ Lax1.TwinWidth.singletonPartition V := h0 ▸ hA
      have hB' : B ∈ Lax1.TwinWidth.singletonPartition V := h0 ▸ hB
      rcases TwinWidth.TrigraphState.mem_singletonBags.mp hA' with ⟨a, rfl⟩
      rcases TwinWidth.TrigraphState.mem_singletonBags.mp hB' with ⟨b, rfl⟩
      show ({a} : Finset V) ≠ {b} ∧ CompleteBetween G {a} {b} ↔ _
      by_cases hab : a = b
      · subst hab
        simp [completeBetween_singleton]
      · simp [completeBetween_singleton, Finset.singleton_inj, hab]
    · intro A B hA hB
      rintro ⟨hne, hnh⟩
      have hA' : A ∈ Lax1.TwinWidth.singletonPartition V := h0 ▸ hA
      have hB' : B ∈ Lax1.TwinWidth.singletonPartition V := h0 ▸ hB
      rcases TwinWidth.TrigraphState.mem_singletonBags.mp hA' with ⟨a, rfl⟩
      rcases TwinWidth.TrigraphState.mem_singletonBags.mp hB' with ⟨b, rfl⟩
      exact hnh (homogeneous_singleton a b)
  ends := by
    show (clampedPartition S S.stepCount).card ≤ 1
    rw [clampedPartition_of_le S le_rfl]
    exact S.ends
  step_contracts i hi := by
    obtain ⟨A, hA, B, hB, hAB, heq⟩ := S.step_merges i hi
    have hcur : clampedPartition S i = S.partition i :=
      clampedPartition_of_le S (by omega)
    have hnext : clampedPartition S (i + 1) = S.partition (i + 1) :=
      clampedPartition_of_le S (by omega)
    have hT : Faithful G (stateOf G (clampedPartition S i)
        (isPartitionFamily_clampedPartition S i)) := faithful_stateOf _
    have hA' : A ∈ clampedPartition S i := by rw [hcur]; exact hA
    have hB' : B ∈ clampedPartition S i := by rw [hcur]; exact hB
    have hbags : clampedPartition S (i + 1) =
        insert (A ∪ B) (((clampedPartition S i).erase A).erase B) := by
      rw [hnext, hcur, heq]
    refine ⟨A, hA', B, hB', hAB, hbags, ?_, ?_⟩
    · intro X Y hX hY
      have hX' : X ∈ insert (A ∪ B)
          (((clampedPartition S i).erase A).erase B) := hbags ▸ hX
      have hY' : Y ∈ insert (A ∪ B)
          (((clampedPartition S i).erase A).erase B) := hbags ▸ hY
      by_cases hXY : X = Y
      · subst hXY
        rw [TwinWidth.SimpleGraph.contractedRed, if_pos rfl]
        simp [stateOf]
      · rw [contractedRed_iff hT hA' hB' hX' hY' hXY]
        exact and_iff_right hXY
    · intro X Y hX hY
      have hX' : X ∈ insert (A ∪ B)
          (((clampedPartition S i).erase A).erase B) := hbags ▸ hX
      have hY' : Y ∈ insert (A ∪ B)
          (((clampedPartition S i).erase A).erase B) := hbags ▸ hY
      by_cases hXY : X = Y
      · subst hXY
        rw [TwinWidth.SimpleGraph.contractedBlack, if_pos rfl]
        simp [stateOf]
      · rw [contractedBlack_iff hT hA' hB' hX' hY' hXY]
        exact and_iff_right hXY
  redDegree_le i hi A hA := by
    have hA1 : A ∈ clampedPartition S i := hA
    have hA2 : A ∈ S.partition i := by
      rwa [clampedPartition_of_le S hi] at hA1
    have hred := redDegree_eq_of_faithful
      (faithful_stateOf (isPartitionFamily_clampedPartition S i)) hA
    show TwinWidth.TrigraphState.redDegree _ A ≤ d
    rw [← hred]
    show Lax1.TwinWidth.redDegree G (clampedPartition S i) A ≤ d
    rw [clampedPartition_of_le S hi]
    exact S.redDegree_le i hi hA2

/-! ## Twin-width transport -/

theorem hasTwinWidthAtMost_mono [Fintype V] [DecidableEq V] {d e : ℕ}
    (h : Lax1.TwinWidth.HasTwinWidthAtMost G d) (hde : d ≤ e) :
    Lax1.TwinWidth.HasTwinWidthAtMost G e := by
  obtain ⟨S⟩ := h
  exact ⟨{ S with
    redDegree_le := fun i hi A hA => le_trans (S.redDegree_le i hi hA) hde }⟩

theorem lt_twinWidth_of_not_hasTwinWidthAtMost
    [Fintype V] [DecidableEq V] {d : ℕ}
    (hnot : ¬ Lax1.TwinWidth.HasTwinWidthAtMost G d)
    (hex : ∃ e, Lax1.TwinWidth.HasTwinWidthAtMost G e) :
    d < Lax1.TwinWidth.twinWidth G := by
  have hne : {e | Lax1.TwinWidth.HasTwinWidthAtMost G e}.Nonempty := hex
  have hmem : Lax1.TwinWidth.HasTwinWidthAtMost G
      (Lax1.TwinWidth.twinWidth G) := Nat.sInf_mem hne
  by_contra hle
  exact hnot (hasTwinWidthAtMost_mono hmem (Nat.le_of_not_lt hle))

/-! ## Relabeling submitted sequences along a graph isomorphism -/

theorem completeBetween_image {V V' : Type} {G : SimpleGraph V}
    {G' : SimpleGraph V'} [DecidableEq V'] (e : G ≃g G') (A B : Finset V) :
    CompleteBetween G' (A.image e.toEquiv) (B.image e.toEquiv) ↔
      CompleteBetween G A B := by
  unfold CompleteBetween
  constructor
  · intro h a ha b hb
    exact e.map_adj_iff.mp
      (h _ (Finset.mem_image_of_mem _ ha) _ (Finset.mem_image_of_mem _ hb))
  · intro h a' ha' b' hb'
    rcases Finset.mem_image.mp ha' with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hb' with ⟨b, hb, rfl⟩
    exact e.map_adj_iff.mpr (h a ha b hb)

theorem emptyBetween_image {V V' : Type} {G : SimpleGraph V}
    {G' : SimpleGraph V'} [DecidableEq V'] (e : G ≃g G') (A B : Finset V) :
    EmptyBetween G' (A.image e.toEquiv) (B.image e.toEquiv) ↔
      EmptyBetween G A B := by
  unfold EmptyBetween
  constructor
  · intro h a ha b hb hadj
    exact h _ (Finset.mem_image_of_mem _ ha) _ (Finset.mem_image_of_mem _ hb)
      (e.map_adj_iff.mpr hadj)
  · intro h a' ha' b' hb' hadj
    rcases Finset.mem_image.mp ha' with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hb' with ⟨b, hb, rfl⟩
    exact h a ha b hb (e.map_adj_iff.mp hadj)

theorem homogeneous_image {V V' : Type} {G : SimpleGraph V}
    {G' : SimpleGraph V'} [DecidableEq V'] (e : G ≃g G') (A B : Finset V) :
    Lax1.TwinWidth.Homogeneous G' (A.image e.toEquiv) (B.image e.toEquiv) ↔
      Lax1.TwinWidth.Homogeneous G A B := by
  rw [homogeneous_iff, homogeneous_iff,
    completeBetween_image e A B, emptyBetween_image e A B]

theorem image_singletonPartition {V V' : Type} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] (φ : V ≃ V') :
    (Lax1.TwinWidth.singletonPartition V).image (Finset.image φ) =
      Lax1.TwinWidth.singletonPartition V' := by
  ext A
  simp only [Lax1.TwinWidth.singletonPartition, Finset.mem_image]
  constructor
  · rintro ⟨B, ⟨v, -, rfl⟩, rfl⟩
    exact ⟨φ v, Finset.mem_univ _, by simp⟩
  · rintro ⟨w, -, rfl⟩
    exact ⟨{φ.symm w}, ⟨φ.symm w, Finset.mem_univ _, rfl⟩, by simp⟩

theorem redDegree_image {V V' : Type} [DecidableEq V] [DecidableEq V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G')
    (P : Finset (Finset V)) (A : Finset V) :
    Lax1.TwinWidth.redDegree G' (P.image (Finset.image e.toEquiv))
        (A.image e.toEquiv) =
      Lax1.TwinWidth.redDegree G P A := by
  unfold Lax1.TwinWidth.redDegree
  have hinj : Function.Injective (Finset.image (e.toEquiv : V → V')) :=
    Finset.image_injective e.toEquiv.injective
  rw [show {B | B ∈ P.image (Finset.image e.toEquiv) ∧
        B ≠ A.image e.toEquiv ∧
        ¬ Lax1.TwinWidth.Homogeneous G' (A.image e.toEquiv) B} =
      Finset.image e.toEquiv ''
        {B | B ∈ P ∧ B ≠ A ∧ ¬ Lax1.TwinWidth.Homogeneous G A B} from ?_]
  · exact Set.ncard_image_of_injective _ hinj
  ext B'
  constructor
  · rintro ⟨hB', hne, hnh⟩
    rcases Finset.mem_image.mp hB' with ⟨B, hB, rfl⟩
    exact ⟨B, ⟨hB, fun h => hne (by rw [h]),
      fun h => hnh ((homogeneous_image e A B).mpr h)⟩, rfl⟩
  · rintro ⟨B, ⟨hB, hne, hnh⟩, rfl⟩
    exact ⟨Finset.mem_image_of_mem _ hB, fun h => hne (hinj h),
      fun h => hnh ((homogeneous_image e A B).mp h)⟩

/-- Relabel a submitted contraction sequence along a graph isomorphism. -/
def mapIsoContractionSequence {V V' : Type}
    [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G') {d : ℕ}
    (S : Lax1.TwinWidth.ContractionSequence G d) :
    Lax1.TwinWidth.ContractionSequence G' d where
  stepCount := S.stepCount
  partition i := (S.partition i).image (Finset.image e.toEquiv)
  starts := by rw [S.starts, image_singletonPartition]
  ends := by
    rw [Finset.card_image_of_injective _
      (Finset.image_injective e.toEquiv.injective)]
    exact S.ends
  step_merges i hi := by
    have hinj : Function.Injective (Finset.image (e.toEquiv : V → V')) :=
      Finset.image_injective e.toEquiv.injective
    obtain ⟨A, hA, B, hB, hAB, heq⟩ := S.step_merges i hi
    refine ⟨A.image e.toEquiv, Finset.mem_image_of_mem _ hA,
      B.image e.toEquiv, Finset.mem_image_of_mem _ hB,
      fun h => hAB (hinj h), ?_⟩
    rw [heq, Finset.image_insert, Finset.image_union,
      Finset.image_erase hinj, Finset.image_erase hinj]
  redDegree_le i hi A' hA' := by
    rcases Finset.mem_image.mp hA' with ⟨A, hA, rfl⟩
    rw [redDegree_image]
    exact S.redDegree_le i hi hA

/-! ## The separation theorem -/

/--
---
conclusion: Lax1.ExponentialSeparation.twin_width_can_be_exponential_in_treewidth
---
Self-contained proof of the Bonnet–Déprés exponential gap: for every `k`, the
Bonnet–Déprés graph `BD_k` has treewidth at most `2*k + 4` while its
twin-width exceeds `2^k`.  The source development phrases contraction
sequences as trigraph state machines; the proof bridges them to the submitted
partition-based sequences through the invariant that black and red edges
agree with completeness and non-homogeneity in the graph, and relabels the
result onto the canonical vertex type `Fin n`.
-/
theorem twin_width_can_be_exponential_in_treewidth (k : ℕ) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      Lax1.Treewidth.treewidth G ≤ 2 * k + 4 ∧
        2 ^ k < Lax1.TwinWidth.twinWidth G := by
  classical
  let G₀ := TwinWidth.SimpleGraph.bonnetDepresGraph k
  let n := Fintype.card (TwinWidth.SimpleGraph.BonnetDepresVertex k)
  let φ : TwinWidth.SimpleGraph.BonnetDepresVertex k ≃ Fin n :=
    Fintype.equivFin _
  let G' : SimpleGraph (Fin n) := SimpleGraph.comap (⇑φ.symm) G₀
  have hiso : G₀ ≃g G' := ⟨φ, by simp [G', SimpleGraph.comap]⟩
  refine ⟨n, G', ?_, ?_⟩
  · have hwidth :
        ((TwinWidth.SimpleGraph.bonnetDepresTreeDecomposition k).mapIso
          hiso).width ≤ 2 * k + 4 := by
      rw [TwinWidth.SimpleGraph.TreeDecomposition.mapIso_width]
      have h := TwinWidth.SimpleGraph.bonnetDepresTreeDecomposition_width_le k
      simpa [TwinWidth.SimpleGraph.bonnetDepresApexCount] using h
    exact treewidth_le_of_source _ hwidth
  · have hnot : ¬ Lax1.TwinWidth.HasTwinWidthAtMost G' (2 ^ k) := by
      rintro ⟨S'⟩
      have hsource : TwinWidth.SimpleGraph.HasTwinWidthAtMost G₀ (2 ^ k) :=
        ⟨sourceOfSubmitted (mapIsoContractionSequence hiso.symm S')⟩
      exact
        TwinWidth.SimpleGraph.BonnetDepres.bonnetDepres_not_hasTwinWidthAtMost_two_pow
          k hsource
    have hex : ∃ e, Lax1.TwinWidth.HasTwinWidthAtMost G' e := by
      obtain ⟨S⟩ := TwinWidth.SimpleGraph.hasTwinWidthAtMost_card G'
      exact ⟨_, ⟨submittedOfSource S⟩⟩
    exact lt_twinWidth_of_not_hasTwinWidthAtMost hnot hex

end

end Lax1Proofs.Main
