import Lax2Proofs.Source.TwinWidth.Equivalence.MainContract
import Lax2Proofs.Source.TwinWidth.Graph.MixedMinorNumber
import Lax2Proofs.Source.TwinWidth.Graph.Partition
import Lax1.TwinWidth
import Lax2.MixedMinorNumber
import Lax2.FunctionalEquivalence

/-!
# Bridge to the submitted concepts

Two bridges connect the source development to the submitted concepts.  For
twin-width, the source phrases contraction sequences as trigraph states with
black/red data and explicit update rules while submission Lax1 phrases them
as bare partition sequences; the bridge is the invariant that black pairs are
exactly the complete pairs and red pairs exactly the non-homogeneous pairs.
For the mixed minor number, the source works with Boolean matrices and
six-field divisions while the submitted concept uses propositional entries
and the four-field division (disjointness and convexity are derivable); the
bridge translates divisions and cells pointwise.  Both submitted parameters
are proved equal to their source counterparts, so the source equivalence
theorem transports directly.
-/

namespace Lax2Proofs.Main

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

/-! ## Faithful trigraph states -/

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

/-- An old bag distinct from a merged part differs from the union. -/
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

/-! ## Between source and submitted contraction sequences -/

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

/-! ## Twin-width equality -/

theorem submitted_hasTwinWidthAtMost_iff [Fintype V] [DecidableEq V] {d : ℕ} :
    Lax1.TwinWidth.HasTwinWidthAtMost G d ↔
      TwinWidth.SimpleGraph.HasTwinWidthAtMost G d := by
  constructor
  · rintro ⟨S⟩
    exact ⟨sourceOfSubmitted S⟩
  · rintro ⟨S⟩
    exact ⟨submittedOfSource S⟩

/-- The submitted twin-width parameter equals the source parameter. -/
theorem submitted_twinWidth_eq_source [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Lax1.TwinWidth.twinWidth G = TwinWidth.SimpleGraph.twinWidth G := by
  classical
  have hex : ∃ d, TwinWidth.SimpleGraph.HasTwinWidthAtMost G d :=
    ⟨Fintype.card V, TwinWidth.SimpleGraph.hasTwinWidthAtMost_card G⟩
  have hset : {d | Lax1.TwinWidth.HasTwinWidthAtMost G d} =
      {d | TwinWidth.SimpleGraph.HasTwinWidthAtMost G d} := by
    ext d
    exact submitted_hasTwinWidthAtMost_iff
  show sInf {d | Lax1.TwinWidth.HasTwinWidthAtMost G d} = _
  rw [hset, TwinWidth.SimpleGraph.twinWidth, dif_pos hex]
  apply le_antisymm
  · exact Nat.sInf_le (Nat.find_spec hex)
  · have hne : Set.Nonempty {d | TwinWidth.SimpleGraph.HasTwinWidthAtMost G d} :=
      ⟨Nat.find hex, Nat.find_spec hex⟩
    have hmem : sInf {d | TwinWidth.SimpleGraph.HasTwinWidthAtMost G d} ∈
        {d | TwinWidth.SimpleGraph.HasTwinWidthAtMost G d} := Nat.sInf_mem hne
    exact Nat.find_min' hex hmem

/-! ## Mixed minor number -/

/-- Disjointness of the parts of a submitted division, derived from the
ordering and covering fields. -/
theorem submittedDivision_disjoint {n k : ℕ}
    (D : Lax2.MixedMinorNumber.Division n k) ⦃i j : Fin k⦄ (hij : i ≠ j) :
    Disjoint (D.part i) (D.part j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [Finset.disjoint_left]
    intro x hxi hxj
    exact absurd (D.part_ordered h hxi hxj) (lt_irrefl x)
  · rw [Finset.disjoint_left]
    intro x hxi hxj
    exact absurd (D.part_ordered h hxj hxi) (lt_irrefl x)

/-- Convexity of the parts of a submitted division, derived from the
ordering and covering fields. -/
theorem submittedDivision_convex {n k : ℕ}
    (D : Lax2.MixedMinorNumber.Division n k) (i : Fin k) ⦃a b c : Fin n⦄
    (ha : a ∈ D.part i) (hc : c ∈ D.part i) (hab : a ≤ b) (hbc : b ≤ c) :
    b ∈ D.part i := by
  obtain ⟨j, hj⟩ := D.part_cover b
  rcases lt_trichotomy i j with h | rfl | h
  · exact absurd (D.part_ordered h hc hj) (not_lt.mpr hbc)
  · exact hj
  · exact absurd (D.part_ordered h hj ha) (not_lt.mpr hab)

/-- A submitted division is a source division; the two dropped fields are
derivable. -/
def sourceDivisionOfSubmitted {n k : ℕ}
    (D : Lax2.MixedMinorNumber.Division n k) : TwinWidth.Division n k where
  part := D.part
  part_nonempty := D.part_nonempty
  part_disjoint := submittedDivision_disjoint D
  part_cover := D.part_cover
  part_convex := submittedDivision_convex D
  part_ordered := D.part_ordered

/-- A source division is verbatim a submitted one. -/
def submittedDivisionOfSource {n k : ℕ} (D : TwinWidth.Division n k) :
    Lax2.MixedMinorNumber.Division n k where
  part := D.part
  part_nonempty := D.part_nonempty
  part_cover := D.part_cover
  part_ordered := D.part_ordered

private theorem bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) :
    a = b := by
  cases a <;> cases b <;> simp_all

private theorem bool_iff_of_eq {a b : Bool} (h : a = b) :
    (a = true) ↔ (b = true) := by
  rw [h]

section MatrixBridge

variable {n m k : ℕ} {M : _root_.Matrix (Fin n) (Fin m) Bool}
  {P : Fin n → Fin m → Prop}

theorem cellVertical_iff (hMP : ∀ r c, (M r c = true) ↔ P r c)
    (R : Lax2.MixedMinorNumber.Division n k)
    (C : Lax2.MixedMinorNumber.Division m k) (i j : Fin k) :
    TwinWidth.Matrix.CellVertical M (sourceDivisionOfSubmitted R)
        (sourceDivisionOfSubmitted C) i j ↔
      Lax2.MixedMinorNumber.cellVertical P R C i j := by
  constructor
  · intro h r₁ r₂ hr₁ hr₂ c hc
    rw [← hMP, ← hMP]
    exact bool_iff_of_eq (h hr₁ hr₂ hc)
  · intro h r₁ r₂ hr₁ hr₂ c hc
    exact bool_eq_of_iff (by rw [hMP, hMP]; exact h hr₁ hr₂ hc)

theorem cellHorizontal_iff (hMP : ∀ r c, (M r c = true) ↔ P r c)
    (R : Lax2.MixedMinorNumber.Division n k)
    (C : Lax2.MixedMinorNumber.Division m k) (i j : Fin k) :
    TwinWidth.Matrix.CellHorizontal M (sourceDivisionOfSubmitted R)
        (sourceDivisionOfSubmitted C) i j ↔
      Lax2.MixedMinorNumber.cellHorizontal P R C i j := by
  constructor
  · intro h r hr c₁ c₂ hc₁ hc₂
    rw [← hMP, ← hMP]
    exact bool_iff_of_eq (h hr hc₁ hc₂)
  · intro h r hr c₁ c₂ hc₁ hc₂
    exact bool_eq_of_iff (by rw [hMP, hMP]; exact h hr hc₁ hc₂)

theorem cellMixed_iff (hMP : ∀ r c, (M r c = true) ↔ P r c)
    (R : Lax2.MixedMinorNumber.Division n k)
    (C : Lax2.MixedMinorNumber.Division m k) (i j : Fin k) :
    TwinWidth.Matrix.CellMixed M (sourceDivisionOfSubmitted R)
        (sourceDivisionOfSubmitted C) i j ↔
      Lax2.MixedMinorNumber.cellMixed P R C i j :=
  and_congr (not_congr (cellVertical_iff hMP R C i j))
    (not_congr (cellHorizontal_iff hMP R C i j))

/-- The submitted and source mixed-minor predicates agree at positive
orders; the source `k = 0` hatch has no submitted counterpart. -/
theorem hasMixedMinor_iff (hMP : ∀ r c, (M r c = true) ↔ P r c)
    (hk : k ≠ 0) :
    Lax2.MixedMinorNumber.HasMixedMinor P k ↔
      TwinWidth.Matrix.HasMixedMinor M k := by
  constructor
  · rintro ⟨R, C, h⟩
    exact Or.inr ⟨sourceDivisionOfSubmitted R, sourceDivisionOfSubmitted C,
      fun i j => (cellMixed_iff hMP R C i j).mpr (h i j)⟩
  · rintro (rfl | ⟨R, C, h⟩)
    · exact absurd rfl hk
    · exact ⟨submittedDivisionOfSource R, submittedDivisionOfSource C,
        fun i j => (cellMixed_iff hMP (submittedDivisionOfSource R)
          (submittedDivisionOfSource C) i j).mp (h i j)⟩

/-- The order of a submitted mixed minor is bounded by both dimensions. -/
theorem hasMixedMinor_le_min
    (h : Lax2.MixedMinorNumber.HasMixedMinor P k) : k ≤ min n m := by
  obtain ⟨R, C, -⟩ := h
  exact le_min (TwinWidth.Division.card_parts_le (sourceDivisionOfSubmitted R))
    (TwinWidth.Division.card_parts_le (sourceDivisionOfSubmitted C))

/-- The submitted and source matrix mixed numbers agree. -/
theorem matrixMixedNumber_eq (hMP : ∀ r c, (M r c = true) ↔ P r c) :
    Lax2.MixedMinorNumber.matrixMixedNumber P =
      TwinWidth.Matrix.matrixMixedNumber M := by
  classical
  apply le_antisymm
  · rcases Set.eq_empty_or_nonempty
        {k | Lax2.MixedMinorNumber.HasMixedMinor P k} with he | hne
    · show sSup {k | Lax2.MixedMinorNumber.HasMixedMinor P k} ≤ _
      rw [he, csSup_empty]
      exact bot_le
    · show sSup {k | Lax2.MixedMinorNumber.HasMixedMinor P k} ≤ _
      apply csSup_le hne
      intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        exact Nat.zero_le _
      · show k ≤ Nat.findGreatest (TwinWidth.Matrix.HasMixedMinor M) (min n m)
        exact Nat.le_findGreatest (hasMixedMinor_le_min hk)
          ((hasMixedMinor_iff hMP hk0).mp hk)
  · have hsrc := TwinWidth.Matrix.hasMixedMinor_matrixMixedNumber M
    by_cases hg0 : TwinWidth.Matrix.matrixMixedNumber M = 0
    · rw [hg0]
      exact Nat.zero_le _
    · have hsub : Lax2.MixedMinorNumber.HasMixedMinor P
          (TwinWidth.Matrix.matrixMixedNumber M) :=
        (hasMixedMinor_iff hMP hg0).mpr hsrc
      show _ ≤ sSup {k | Lax2.MixedMinorNumber.HasMixedMinor P k}
      exact le_csSup ⟨min n m, fun k hk => hasMixedMinor_le_min hk⟩ hsub

end MatrixBridge

/-- The source Boolean adjacency matrix decides the submitted propositional
one. -/
theorem orderedAdjacency_bridge {n : ℕ} (G : SimpleGraph V) (e : Fin n ≃ V) :
    ∀ i j, (TwinWidth.Matrix.orderedAdjacency G ⟨e⟩ i j = true) ↔
      Lax2.MixedMinorNumber.orderedAdjacency G e i j := by
  intro i j
  unfold TwinWidth.Matrix.orderedAdjacency Lax2.MixedMinorNumber.orderedAdjacency
  simp

/-- The submitted mixed number of an ordered adjacency matrix is the source
one. -/
theorem submitted_orderedMixedNumber_eq {n : ℕ}
    (G : SimpleGraph V) (e : Fin n ≃ V) :
    Lax2.MixedMinorNumber.matrixMixedNumber
        (Lax2.MixedMinorNumber.orderedAdjacency G e) =
      TwinWidth.Matrix.orderedAdjacencyMixedNumber G ⟨e⟩ := by
  rw [TwinWidth.Matrix.orderedAdjacencyMixedNumber]
  exact matrixMixedNumber_eq (orderedAdjacency_bridge G e)

/-- The submitted mixed minor number parameter equals the source parameter. -/
theorem submitted_mixedMinorNumber_eq [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Lax2.MixedMinorNumber.mixedMinorNumber G =
      TwinWidth.SimpleGraph.mixedMinorNumber G := by
  show sInf (Set.range fun e : Fin (Fintype.card V) ≃ V =>
      Lax2.MixedMinorNumber.matrixMixedNumber
        (Lax2.MixedMinorNumber.orderedAdjacency G e)) = _
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ :=
      TwinWidth.SimpleGraph.exists_order_mixedNumber_eq_mixedMinorNumber G
    exact Nat.sInf_le
      ⟨σ.equiv, (submitted_orderedMixedNumber_eq G σ.equiv).trans hσ⟩
  · haveI : Nonempty (Fin (Fintype.card V) ≃ V) := ⟨(Fintype.equivFin V).symm⟩
    apply le_csInf (Set.range_nonempty _)
    rintro b ⟨e, rfl⟩
    show TwinWidth.SimpleGraph.mixedMinorNumber G ≤
      Lax2.MixedMinorNumber.matrixMixedNumber
        (Lax2.MixedMinorNumber.orderedAdjacency G e)
    rw [submitted_orderedMixedNumber_eq]
    exact TwinWidth.SimpleGraph.mixedMinorNumber_le_orderedAdjacencyMixedNumber
      G ⟨e⟩

/-! ## The equivalence theorem -/

/--
---
conclusion: Lax2.FunctionalEquivalence.twin_width_functionally_equivalent_mixed_minor_number
---
Self-contained proof that the submitted twin-width parameter (from submission
Lax1) and the submitted mixed minor number are functionally equivalent.  The
submitted partition-based twin-width and the propositional mixed minor number
are proved pointwise equal to their source counterparts — through the
black-is-complete / red-is-non-homogeneous invariant for contraction
sequences and a pointwise division-and-cell translation for mixed minors —
and the source equivalence theorem (Marcus–Tardos, the matrix grid-minor
theorem, and the twin-decomposition bridge) transports directly.
-/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    Lax2.FunctionalEquivalence.FunctionallyEquivalent
      Lax1.TwinWidth.twinWidth
      Lax2.MixedMinorNumber.mixedMinorNumber := by
  obtain ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ :=
    TwinWidth.MainContract.twin_width_functionally_equivalent_mixed_minor_number
  constructor
  · refine ⟨f, ?_⟩
    intro V _ _ G
    show Lax1.TwinWidth.twinWidth G ≤
      f (Lax2.MixedMinorNumber.mixedMinorNumber G)
    rw [submitted_twinWidth_eq_source, submitted_mixedMinorNumber_eq]
    exact hf G
  · refine ⟨g, ?_⟩
    intro V _ _ G
    show Lax2.MixedMinorNumber.mixedMinorNumber G ≤
      g (Lax1.TwinWidth.twinWidth G)
    rw [submitted_twinWidth_eq_source, submitted_mixedMinorNumber_eq]
    exact hg G

end

end Lax2Proofs.Main
