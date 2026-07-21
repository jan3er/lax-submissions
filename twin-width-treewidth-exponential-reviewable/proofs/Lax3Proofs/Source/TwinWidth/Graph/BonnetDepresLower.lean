import Lax3Proofs.Source.TwinWidth.Graph.BonnetDepresLowerBasic

namespace Lax3Proofs.TwinWidth
namespace SimpleGraph

namespace BonnetDepres

/-- Claim 14 with the witness part retained: a non-singleton tree part has a
large child-bag witness in itself or among its red neighbors. -/
theorem exists_largeChildBag_in_redOrSelfBags_of_nonSingleton_tree_bag
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hnotSingleton : A ≠ {Sum.inr u})
    (hlevel : u.1.val < bonnetDepresDepth k) :
    ∃ C ∈ largeChildBags P,
      C ∈ redOrSelfBags P A ∧
        manyChildrenThreshold k ≤ (C ∩ childVertexSet u hlevel).card := by
  classical
  have hexists :
      ∃ z ∈ A, z ≠ (Sum.inr u : BonnetDepresVertex k) := by
    by_contra hnone
    apply hnotSingleton
    ext z
    constructor
    · intro hz
      have hz_eq : z = (Sum.inr u : BonnetDepresVertex k) := by
        by_contra hne
        exact hnone ⟨z, hz, hne⟩
      simp [hz_eq]
    · intro hz
      rw [Finset.mem_singleton] at hz
      simpa [hz] using huA
  rcases hexists with ⟨z, hzA, hzu⟩
  cases z with
  | inl x =>
      have hAeq :
          A = ({Sum.inl x} : Finset (BonnetDepresVertex k)) :=
        eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
          hd hpart hroot hred hA hzA
      have huSingleton :
          (Sum.inr u : BonnetDepresVertex k) ∈
            ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
        rw [hAeq] at huA
        exact huA
      simp at huSingleton
  | inr w =>
      have hwu : w ≠ u := by
        intro hwu
        exact hzu (by simp [hwu])
      rcases hasManyChildrenInPart_of_two_tree_vertices_of_redDegreeAtMost
          (k := k) (d := d) (P := P) (A := A) (u := u) (w := w)
          hd hpart hred hA huA hzA hwu hlevel with
        ⟨C, hC, hmany⟩
      have hClarge : C ∈ largeChildBags P := by
        rw [mem_largeChildBags]
        exact ⟨hC, u, hlevel, hmany⟩
      have hCredOrSelf : C ∈ redOrSelfBags P A := by
        by_cases hCA : C = A
        · rw [hCA, redOrSelfBags]
          simp
        · rw [redOrSelfBags, Finset.mem_insert, Finset.mem_filter]
          right
          refine ⟨hC, ?_⟩
          exact partitionRedAdj_of_many_children_and_two_tree_vertices
            (k := k) (A := A) (C := C) (u := u) (w := w)
            (fun hAC => hCA hAC.symm) huA hzA hwu hlevel hmany
      exact ⟨C, hClarge, hCredOrSelf, hmany⟩

/-- Parts that contain an internal tree node and are not that node's singleton
bag.  These are the `B'`-type parts in the final lower-bound counting. -/
noncomputable def internalNonSingletonTreeBags {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k))) :
    Finset (Finset (BonnetDepresVertex k)) := by
  classical
  exact P.filter fun A =>
    ∃ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      IsInternal u ∧
        (Sum.inr u : BonnetDepresVertex k) ∈ A ∧
          A ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k))

@[simp] theorem mem_internalNonSingletonTreeBags {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)} :
    A ∈ internalNonSingletonTreeBags P ↔
      A ∈ P ∧
        ∃ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          IsInternal u ∧
            (Sum.inr u : BonnetDepresVertex k) ∈ A ∧
              A ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
  classical
  simp [internalNonSingletonTreeBags]

/-- A part containing an internal tree node and a distinct tree node belongs to
`internalNonSingletonTreeBags`. -/
theorem mem_internalNonSingletonTreeBags_of_two_tree_vertices {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hA : A ∈ P)
    (hlevel : IsInternal u)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hvA : (Sum.inr v : BonnetDepresVertex k) ∈ A)
    (huv : u ≠ v) :
    A ∈ internalNonSingletonTreeBags P := by
  rw [mem_internalNonSingletonTreeBags]
  refine ⟨hA, u, hlevel, huA, ?_⟩
  intro hsingleton
  have hvSingleton :
      (Sum.inr v : BonnetDepresVertex k) ∈
        ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
    simpa [hsingleton] using hvA
  rw [Finset.mem_singleton] at hvSingleton
  exact huv (Sum.inr.inj hvSingleton.symm)

/-- A non-singleton internal-tree bag is not any singleton tree-vertex bag. -/
theorem internalNonSingletonTreeBag_ne_singleton_tree {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hA : A ∈ internalNonSingletonTreeBags P)
    (p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    A ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
  rcases mem_internalNonSingletonTreeBags.mp hA with
    ⟨_hAP, u, _hlevel, huA, hnotSingleton⟩
  intro hAeq
  have hup : u = p := by
    have huSingleton :
        (Sum.inr u : BonnetDepresVertex k) ∈
          ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
      simpa [hAeq] using huA
    exact Sum.inr.inj (Finset.mem_singleton.mp huSingleton)
  exact hnotSingleton (by simpa [hup] using hAeq)

/-- A large child bag contains at least two vertices, so it cannot be a tree
singleton. -/
theorem largeChildBag_ne_singleton_tree {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hA : A ∈ largeChildBags P)
    (p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    A ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
  classical
  rcases (mem_largeChildBags.mp hA).2 with ⟨u, hlevel, hmany⟩
  have htwo : 1 < (A ∩ childVertexSet u hlevel).card := by
    have htwo' := two_le_manyChildrenThreshold k
    omega
  rcases Finset.one_lt_card.mp htwo with ⟨x, hx, y, hy, hxy⟩
  intro hsingleton
  have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
  have hyA : y ∈ A := (Finset.mem_inter.mp hy).1
  have hxSingleton : x ∈ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
    simpa [hsingleton] using hxA
  have hySingleton : y ∈ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
    simpa [hsingleton] using hyA
  rw [Finset.mem_singleton] at hxSingleton hySingleton
  exact hxy (hxSingleton.trans hySingleton.symm)

/-- Every non-singleton internal-tree part is itself a large bag or has a large
bag among its red neighbors. -/
theorem exists_largeChildBag_in_redOrSelfBags_of_internalNonSingletonTreeBag
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ internalNonSingletonTreeBags P) :
    ∃ C ∈ largeChildBags P, C ∈ redOrSelfBags P A := by
  rcases mem_internalNonSingletonTreeBags.mp hA with
    ⟨hAP, u, hlevel, huA, hnotSingleton⟩
  rcases exists_largeChildBag_in_redOrSelfBags_of_nonSingleton_tree_bag
      (k := k) (d := d) (P := P) (A := A) (u := u)
      hd hpart hroot hred hAP huA hnotSingleton hlevel with
    ⟨C, hC, hCredOrSelf, _hmany⟩
  exact ⟨C, hC, hCredOrSelf⟩

/-- Incidence count for the final lower-bound step: under bounded red degree,
there are at most `|B| * (d + 1)` non-singleton parts containing an internal tree
node, where `B` is the set of large child bags. -/
theorem internalNonSingletonTreeBags_card_le_largeChildBags_mul_succ
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d) :
    (internalNonSingletonTreeBags P).card ≤ (largeChildBags P).card * (d + 1) := by
  classical
  let I := internalNonSingletonTreeBags P
  let L := largeChildBags P
  let Ilarge := I.filter fun A => A ∈ L
  let Ismall := I.filter fun A => A ∉ L
  have hsplit : I.card = Ilarge.card + Ismall.card := by
    dsimp [Ilarge, Ismall]
    simpa [Nat.add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := I) (p := fun A => A ∈ L)).symm
  have hIlarge_card : Ilarge.card ≤ L.card := by
    exact Finset.card_le_card (by
      intro A hA
      exact (Finset.mem_filter.mp hA).2)
  have hIsmall_subset :
      Ismall ⊆ L.biUnion
        (fun C => P.filter fun A => partitionRedAdj (bonnetDepresGraph k) C A) := by
    intro A hA
    rw [Finset.mem_filter] at hA
    rcases hA with ⟨hAI, hAnotL⟩
    rcases exists_largeChildBag_in_redOrSelfBags_of_internalNonSingletonTreeBag
        (k := k) (d := d) (P := P) (A := A)
        hd hpart hroot hred (by simpa [I] using hAI) with
      ⟨C, hCL, hCredOrSelf⟩
    have hCA : C ≠ A := by
      intro h
      exact hAnotL (by simpa [L, h] using hCL)
    have hredCA : partitionRedAdj (bonnetDepresGraph k) C A := by
      rw [redOrSelfBags, Finset.mem_insert, Finset.mem_filter] at hCredOrSelf
      rcases hCredOrSelf with hCAeq | hredAC
      · exact False.elim (hCA hCAeq)
      · exact partitionRedAdj_symm hredAC.2
    rw [Finset.mem_biUnion]
    refine ⟨C, hCL, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hredCA⟩
    exact (mem_internalNonSingletonTreeBags.mp (by simpa [I] using hAI)).1
  have hIsmall_card : Ismall.card ≤ L.card * d := by
    calc
      Ismall.card
          ≤ (L.biUnion
              (fun C => P.filter fun A =>
                partitionRedAdj (bonnetDepresGraph k) C A)).card :=
        Finset.card_le_card hIsmall_subset
      _ ≤ ∑ C ∈ L, (P.filter fun A =>
          partitionRedAdj (bonnetDepresGraph k) C A).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _C ∈ L, d := by
        refine Finset.sum_le_sum ?_
        intro C hC
        exact hred (mem_largeChildBags.mp (by simpa [L] using hC)).1
      _ = L.card * d := by
        simp [Finset.sum_const, Nat.mul_comm]
  calc
    I.card = Ilarge.card + Ismall.card := hsplit
    _ ≤ L.card + L.card * d := Nat.add_le_add hIlarge_card hIsmall_card
    _ = L.card * (d + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]

/-- The chosen constants leave room beyond the red-degree upper bound for
non-singleton internal-tree parts. -/
theorem largeChildBags_mul_succ_lt_manyInternalBagsThreshold
    {k d Lcard : ℕ}
    (hLcard : Lcard ≤ 2 ^ (k + 2))
    (hd : d ≤ 2 ^ k) :
    Lcard * (d + 1) < manyInternalBagsThreshold k := by
  have hpow : 2 ^ k ≤ manyChildrenThreshold k := by
    unfold manyChildrenThreshold
    apply Nat.pow_le_pow_right
    · omega
    · omega
  have hupper :
      Lcard * (d + 1) ≤
        2 ^ (k + 2) * (manyChildrenThreshold k + 1) := by
    exact Nat.mul_le_mul hLcard (Nat.succ_le_succ (hd.trans hpow))
  unfold manyInternalBagsThreshold
  omega

/-- A state with red degree at most `2^k` cannot contain the final threshold
number of non-singleton internal-tree parts. -/
theorem false_of_many_internalNonSingletonTreeBags
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hmany : manyInternalBagsThreshold k ≤ (internalNonSingletonTreeBags P).card) :
    False := by
  have hupper :=
    internalNonSingletonTreeBags_card_le_largeChildBags_mul_succ
      (k := k) (d := d) (P := P) hd hpart hroot hred
  have hLcard :=
    largeChildBags_card_le (k := k) (d := d) (P := P) hd hpart hroot hred
  have hgap :=
    largeChildBags_mul_succ_lt_manyInternalBagsThreshold
      (k := k) (d := d) (Lcard := (largeChildBags P).card) hLcard hd
  omega

/-- Claim 14 in the form needed for contraction states: while root children are
singleton bags, any non-singleton bag containing a tree vertex with children
contains another tree vertex, hence has many children of the first vertex in one
part. -/
theorem hasManyChildrenInPart_of_nonSingleton_tree_bag_of_rootChildrenSingleton
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hnotSingleton : A ≠ {Sum.inr u})
    (hlevel : u.1.val < bonnetDepresDepth k) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  have hexists :
      ∃ z ∈ A, z ≠ (Sum.inr u : BonnetDepresVertex k) := by
    by_contra hnone
    apply hnotSingleton
    ext z
    constructor
    · intro hz
      have hz_eq : z = (Sum.inr u : BonnetDepresVertex k) := by
        by_contra hne
        exact hnone ⟨z, hz, hne⟩
      simp [hz_eq]
    · intro hz
      rw [Finset.mem_singleton] at hz
      simpa [hz] using huA
  rcases hexists with ⟨z, hzA, hzu⟩
  cases z with
  | inl x =>
      have hAeq :
          A = ({Sum.inl x} : Finset (BonnetDepresVertex k)) :=
        eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
          hd hpart hroot hred hA hzA
      have huSingleton :
          (Sum.inr u : BonnetDepresVertex k) ∈
            ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
        rw [hAeq] at huA
        exact huA
      simp at huSingleton
  | inr w =>
      have hwu : w ≠ u := by
        intro hwu
        exact hzu (by simp [hwu])
      exact hasManyChildrenInPart_of_two_tree_vertices_of_redDegreeAtMost
        hd hpart hred hA huA hzA hwu hlevel

/-- Claim 16: if a non-preleaf internal node satisfies property `P`, then many
of its children also satisfy property `P`. -/
theorem hasManyPChildren_of_hasManyChildrenInPart_of_nonpreleaf
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hP : HasManyChildrenInPart P u hlevel (manyChildrenThreshold k))
    (hnonpreleaf : IsNonPreleafInternal u) :
    HasManyPChildren P u hlevel (manyChildrenThreshold k) := by
  classical
  have hnonpreleaf_raw : u.1.val + 1 < bonnetDepresDepth k := by
    simpa [IsNonPreleafInternal] using hnonpreleaf
  rcases hP with ⟨A, hA, hcardA⟩
  refine ⟨childrenInBag A u hlevel, ?_, ?_, ?_⟩
  · intro c hc
    exact (mem_childrenInBag.mp hc).1
  · rwa [card_childrenInBag]
  · intro c hc
    have hcdata := mem_childrenInBag.mp hc
    have hcLevel : c.1.val < bonnetDepresDepth k := by
      rcases mem_childSet.mp hcdata.1 with ⟨label, rfl⟩
      simp [FullTreeNode.child]
      omega
    have hthreshold_two : 2 ≤ manyChildrenThreshold k := by
      unfold manyChildrenThreshold
      have hpow : 2 ^ 1 ≤ 2 ^ (k + 1) := by
        apply Nat.pow_le_pow_right
        · omega
        · omega
      simpa using hpow
    have hnotSingleton :
        A ≠ ({Sum.inr c} : Finset (BonnetDepresVertex k)) := by
      intro hAeq
      have hcard_le_one :
          (A ∩ childVertexSet u hlevel).card ≤ 1 := by
        calc
          (A ∩ childVertexSet u hlevel).card ≤ A.card :=
            Finset.card_le_card (by intro v hv; rw [Finset.mem_inter] at hv; exact hv.1)
          _ = 1 := by simp [hAeq]
      omega
    exact ⟨hcLevel,
      hasManyChildrenInPart_of_nonSingleton_tree_bag_of_rootChildrenSingleton
        (k := k) (d := d) (P := P) (A := A) (u := c)
        hd hpart hroot hred hA hcdata.2 hnotSingleton hcLevel⟩

/-- Claim 17: for every internal tree node in a bounded state, property `P`
implies property `Q`. -/
theorem qProperty_of_hasManyChildrenInPart
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : IsInternal u)
    (hP : HasManyChildrenInPart P u hlevel (manyChildrenThreshold k)) :
    QProperty P u := by
  classical
  let remaining
      (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : ℕ :=
    bonnetDepresDepth k - u.1.val
  have hmain :
      ∀ n : ℕ,
        ∀ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          ∀ hlevel : IsInternal u, remaining u = n →
            HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) →
              QProperty P u := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro u hlevel hn hP
        by_cases hpre : IsPreleaf u
        · exact qProperty_of_hasManyChildrenInPart_preleaf hpre hlevel hP
        · have hnonpreleaf : IsNonPreleafInternal u := by
            unfold IsPreleaf at hpre
            unfold IsInternal at hlevel
            unfold IsNonPreleafInternal
            omega
          have hchildren :
              HasManyPChildren P u hlevel (manyChildrenThreshold k) :=
            hasManyPChildren_of_hasManyChildrenInPart_of_nonpreleaf
              (k := k) (d := d) (P := P) (u := u) (hlevel := hlevel)
              hd hpart hroot hred hP hnonpreleaf
          rcases hchildren with ⟨S, hSsubset, hScard, hSprop⟩
          have htwo : 2 ≤ S.card :=
            (two_le_manyChildrenThreshold k).trans hScard
          have htwo_exists :
              ∃ c₁ ∈ S, ∃ c₂ ∈ S, c₁ ≠ c₂ := by
            by_contra hnone
            have hcard_le_one : S.card ≤ 1 := by
              rw [Finset.card_le_one_iff]
              intro a b ha hb
              by_contra hab
              exact hnone ⟨a, ha, b, hb, hab⟩
            omega
          rcases htwo_exists with ⟨c₁, hc₁S, c₂, hc₂S, hcne⟩
          rcases hSprop hc₁S with ⟨hc₁Level, hP₁⟩
          rcases hSprop hc₂S with ⟨hc₂Level, hP₂⟩
          have hc₁child : c₁ ∈ childSet u hlevel := hSsubset hc₁S
          have hc₂child : c₂ ∈ childSet u hlevel := hSsubset hc₂S
          have hc₁level_eq := level_eq_succ_of_mem_childSet hc₁child
          have hc₂level_eq := level_eq_succ_of_mem_childSet hc₂child
          have hc₁_lt : remaining c₁ < n := by
            unfold remaining
            rw [hc₁level_eq]
            unfold remaining at hn
            omega
          have hc₂_lt : remaining c₂ < n := by
            unfold remaining
            rw [hc₂level_eq]
            unfold remaining at hn
            omega
          have hq₁ : QProperty P c₁ :=
            ih (remaining c₁) hc₁_lt c₁ hc₁Level rfl hP₁
          have hq₂ : QProperty P c₂ :=
            ih (remaining c₂) hc₂_lt c₂ hc₂Level rfl hP₂
          exact qProperty_of_two_child_qProperties
            hnonpreleaf hc₁child hc₂child hcne hq₁ hq₂
  exact hmain (remaining u) u hlevel rfl hP

/-- If a contraction only merges the singleton `{u}` with another bag, then any
large child intersection present after the contraction was already present
before it. -/
theorem hasManyChildrenInPart_of_merge_singleton_parent_backward
    {k m : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hB : B ∈ P)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B))
    (hmany : HasManyChildrenInPart Q u hlevel m) :
    HasManyChildrenInPart P u hlevel m := by
  classical
  rcases hmany with ⟨C, hC, hcard⟩
  subst Q
  rw [mem_merge_family_iff] at hC
  rcases hC with hmerge | ⟨hCP, _hCneParent, _hCneB⟩
  · refine ⟨B, hB, ?_⟩
    have hcard' := hcard
    rw [hmerge] at hcard'
    change m ≤
      ((({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B) ∩
        childVertexSet u hlevel).card at hcard'
    rwa [singleton_parent_union_inter_childVertexSet u hlevel B] at hcard'
  · exact ⟨C, hCP, hcard⟩

/-- Symmetric form of `hasManyChildrenInPart_of_merge_singleton_parent_backward`
for a merged bag written as `B ∪ {u}`. -/
theorem hasManyChildrenInPart_of_merge_singleton_parent_backward'
    {k m : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hB : B ∈ P)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (B ∪ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
        ((P.erase B).erase ({Sum.inr u} : Finset (BonnetDepresVertex k))))
    (hmany : HasManyChildrenInPart Q u hlevel m) :
    HasManyChildrenInPart P u hlevel m := by
  classical
  have hQ' :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B) := by
    rw [hQ, Finset.union_comm]
    congr 1
    ext C
    by_cases hCu : C = ({Sum.inr u} : Finset (BonnetDepresVertex k))
    · subst C
      by_cases hBu : B = ({Sum.inr u} : Finset (BonnetDepresVertex k))
      · subst B
        simp
      · simp
    · by_cases hCB : C = B
      · subst C
        simp [hCu]
      · simp [hCu, hCB]
  exact hasManyChildrenInPart_of_merge_singleton_parent_backward hB hlevel hQ' hmany

/-- Claim-15 single-step form.  If `Q` is obtained from `P` by merging the
singleton `{u}` with a different bag `B`, and the next partition still satisfies
the root-child singleton hypotheses, then `u` already has property `P` in `P`. -/
theorem hasManyChildrenInPart_before_merge_singleton_parent
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpartP : IsBagPartition P)
    (hpartQ : IsBagPartition Q)
    (hrootQ : RootChildrenSingleton Q)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hsingleP : ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ P)
    (hB : B ∈ P)
    (hBne : B ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B)) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  let A : Finset (BonnetDepresVertex k) :=
    ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B
  have hA : A ∈ Q := by
    rw [hQ]
    exact Finset.mem_insert_self _ _
  have huA : (Sum.inr u : BonnetDepresVertex k) ∈ A := by
    simp [A]
  have hnotSingleton : A ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
    intro hAeq
    rcases hpartP.1 hB with ⟨b, hbB⟩
    have hbA : b ∈ A := by
      simp [A, hbB]
    have hbSingleton : b ∈ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
      simpa [hAeq] using hbA
    have hbNotSingleton :
        b ∉ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
      exact (Finset.disjoint_left.mp
        (hpartP.2.1 hB hsingleP hBne)) hbB
    exact hbNotSingleton hbSingleton
  have hmanyQ :
      HasManyChildrenInPart Q u hlevel (manyChildrenThreshold k) :=
    hasManyChildrenInPart_of_nonSingleton_tree_bag_of_rootChildrenSingleton
      (k := k) (d := d) (P := Q) (A := A) (u := u)
      hd hpartQ hrootQ hredQ hA huA hnotSingleton hlevel
  exact hasManyChildrenInPart_of_merge_singleton_parent_backward hB hlevel hQ hmanyQ

/-- Variant of Claim 15 for a singleton tree vertex merged with a bag already
containing another tree vertex.  This version does not require the next state to
keep all root children singleton. -/
theorem hasManyChildrenInPart_before_merge_singleton_parent_with_tree_witness
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpartP : IsBagPartition P)
    (hpartQ : IsBagPartition Q)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hsingleP : ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ P)
    (hB : B ∈ P)
    (hBne : B ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
    (hwB : (Sum.inr w : BonnetDepresVertex k) ∈ B)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B)) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  let A : Finset (BonnetDepresVertex k) :=
    ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B
  have hA : A ∈ Q := by
    rw [hQ]
    exact Finset.mem_insert_self _ _
  have huA : (Sum.inr u : BonnetDepresVertex k) ∈ A := by
    simp [A]
  have hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A := by
    simp [A, hwB]
  have hwu : w ≠ u := by
    intro hwu
    subst w
    have hdis := hpartP.2.1 hB hsingleP hBne
    exact (Finset.disjoint_left.mp hdis) hwB (by simp)
  have hmanyQ :
      HasManyChildrenInPart Q u hlevel (manyChildrenThreshold k) :=
    hasManyChildrenInPart_of_two_tree_vertices_of_redDegreeAtMost
      (k := k) (d := d) (P := Q) (A := A) (u := u) (w := w)
      hd hpartQ hredQ hA huA hwA hwu hlevel
  exact hasManyChildrenInPart_of_merge_singleton_parent_backward hB hlevel hQ hmanyQ

/-- Symmetric version of
`hasManyChildrenInPart_before_merge_singleton_parent_with_tree_witness`. -/
theorem hasManyChildrenInPart_before_merge_tree_witness_with_singleton_parent
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpartP : IsBagPartition P)
    (hpartQ : IsBagPartition Q)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hsingleP : ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ P)
    (hB : B ∈ P)
    (hBne : B ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
    (hwB : (Sum.inr w : BonnetDepresVertex k) ∈ B)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (B ∪ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
        ((P.erase B).erase ({Sum.inr u} : Finset (BonnetDepresVertex k)))) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  have hQ' :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B) := by
    rw [hQ, Finset.union_comm]
    congr 1
    ext C
    by_cases hCu : C = ({Sum.inr u} : Finset (BonnetDepresVertex k))
    · subst C
      by_cases hBu : B = ({Sum.inr u} : Finset (BonnetDepresVertex k))
      · subst B
        simp
      · simp
    · by_cases hCB : C = B
      · subst C
        simp [hCu]
      · simp [hCu, hCB]
  exact hasManyChildrenInPart_before_merge_singleton_parent_with_tree_witness
    (k := k) (d := d) (P := P) (Q := Q) (B := B) (u := u) (w := w)
    hd hpartP hpartQ hredQ hsingleP hB hBne hwB hlevel hQ'

/-- Claim 14 specialized to an actual contraction-sequence state. -/
theorem ContractionSequence.hasManyChildrenInPart_of_nonSingleton_tree_bag
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i ≤ S.stepCount)
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton (S.state i).bags)
    (hA : A ∈ (S.state i).bags)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hnotSingleton : A ≠ {Sum.inr u})
    (hlevel : u.1.val < bonnetDepresDepth k) :
    HasManyChildrenInPart (S.state i).bags u hlevel (manyChildrenThreshold k) :=
  hasManyChildrenInPart_of_nonSingleton_tree_bag_of_rootChildrenSingleton
    (k := k) (d := d) (P := (S.state i).bags) (A := A) (u := u)
    hd (Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot (Lax3Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state S hi)
    hA huA hnotSingleton hlevel

/-- Claim 16 specialized to an actual contraction-sequence state. -/
theorem ContractionSequence.hasManyPChildren_of_hasManyChildrenInPart_of_nonpreleaf
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i ≤ S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton (S.state i).bags)
    (hP :
      HasManyChildrenInPart (S.state i).bags u hlevel (manyChildrenThreshold k))
    (hnonpreleaf : IsNonPreleafInternal u) :
    HasManyPChildren (S.state i).bags u hlevel (manyChildrenThreshold k) :=
  Lax3Proofs.TwinWidth.SimpleGraph.BonnetDepres.hasManyPChildren_of_hasManyChildrenInPart_of_nonpreleaf
    (k := k) (d := d) (P := (S.state i).bags) (u := u) (hlevel := hlevel)
    hd (Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot (Lax3Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state S hi)
    hP hnonpreleaf

/-- Claim 17 specialized to an actual contraction-sequence state. -/
theorem ContractionSequence.qProperty_of_hasManyChildrenInPart
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i ≤ S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton (S.state i).bags)
    (hP :
      HasManyChildrenInPart (S.state i).bags u hlevel (manyChildrenThreshold k)) :
    QProperty (S.state i).bags u :=
  Lax3Proofs.TwinWidth.SimpleGraph.BonnetDepres.qProperty_of_hasManyChildrenInPart
    (k := k) (d := d) (P := (S.state i).bags) (u := u) (hlevel := hlevel)
    hd (Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot (Lax3Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state S hi)
    hP

/-- Property `P` is monotone along one step of a contraction sequence. -/
theorem ContractionSequence.hasManyChildrenInPart_step
    {k d m : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i < S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hP :
      HasManyChildrenInPart (S.state i).bags u hlevel m) :
    HasManyChildrenInPart (S.state (i + 1)).bags u hlevel m :=
  hasManyChildrenInPart_mono_of_isBagContraction
    (Lax3Proofs.TwinWidth.SimpleGraph.IsContractionStep.isBagContraction
      (S.step_contracts i hi)) hP

/-- Property `Q` is monotone along one step of a contraction sequence. -/
theorem ContractionSequence.qProperty_step
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i < S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ : QProperty (S.state i).bags u) :
    QProperty (S.state (i + 1)).bags u :=
  qProperty_mono_of_isBagContraction
    (Lax3Proofs.TwinWidth.SimpleGraph.IsContractionStep.isBagContraction
      (S.step_contracts i hi)) hQ

/-- Property `P` is monotone along any later state of a contraction sequence. -/
theorem ContractionSequence.hasManyChildrenInPart_mono
    {k d m : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hP :
      HasManyChildrenInPart (S.state i).bags u hlevel m) :
    HasManyChildrenInPart (S.state j).bags u hlevel m := by
  induction hij with
  | refl =>
      exact hP
  | @step n hij ih =>
      have hnle : n ≤ S.stepCount := Nat.le_trans (Nat.le_succ n) hj
      have hprev :
          HasManyChildrenInPart (S.state n).bags u hlevel m := ih hnle
      exact
        Lax3Proofs.TwinWidth.SimpleGraph.BonnetDepres.ContractionSequence.hasManyChildrenInPart_step
          S (Nat.lt_of_succ_le hj) hprev

/-- Property `Q` is monotone along any later state of a contraction sequence. -/
theorem ContractionSequence.qProperty_mono
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ : QProperty (S.state i).bags u) :
    QProperty (S.state j).bags u := by
  induction hij with
  | refl =>
      exact hQ
  | @step n hij ih =>
      have hnle : n ≤ S.stepCount := Nat.le_trans (Nat.le_succ n) hj
      have hprev : QProperty (S.state n).bags u := ih hnle
      exact
        Lax3Proofs.TwinWidth.SimpleGraph.BonnetDepres.ContractionSequence.qProperty_step
          S (Nat.lt_of_succ_le hj) hprev

/-- At time zero, every root child is still a singleton bag. -/
theorem ContractionSequence.rootChildrenSingleton_zero
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    RootChildrenSingleton (S.state 0).bags := by
  have hbags :
      (S.state 0).bags = TrigraphState.singletonBags (BonnetDepresVertex k) :=
    S.starts.1
  simp [hbags, rootChildrenSingleton_singletonBags k]

/-- At the final state of a contraction sequence, not all root children can still
be singleton bags. -/
theorem ContractionSequence.not_rootChildrenSingleton_final
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ¬ RootChildrenSingleton (S.state S.stepCount).bags :=
  not_rootChildrenSingleton_of_card_le_one S.ends

/-- Some state of every contraction sequence has lost the root-child singleton
invariant: the final state is enough. -/
theorem ContractionSequence.exists_not_rootChildrenSingleton
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ∃ i : ℕ, ¬ RootChildrenSingleton (S.state i).bags :=
  ⟨S.stepCount, ContractionSequence.not_rootChildrenSingleton_final S⟩

/-- The first time at which not all root children are singleton bags. -/
noncomputable def ContractionSequence.firstRootChildrenNonSingletonIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) : ℕ := by
  classical
  exact Nat.find (ContractionSequence.exists_not_rootChildrenSingleton S)

theorem ContractionSequence.not_rootChildrenSingleton_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ¬ RootChildrenSingleton
      (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags := by
  classical
  unfold ContractionSequence.firstRootChildrenNonSingletonIndex
  exact Nat.find_spec (ContractionSequence.exists_not_rootChildrenSingleton S)

theorem ContractionSequence.rootChildrenSingleton_before_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i < ContractionSequence.firstRootChildrenNonSingletonIndex S) :
    RootChildrenSingleton (S.state i).bags := by
  classical
  by_contra hnot
  unfold ContractionSequence.firstRootChildrenNonSingletonIndex at hi
  exact Nat.find_min (ContractionSequence.exists_not_rootChildrenSingleton S) hi hnot

theorem ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ContractionSequence.firstRootChildrenNonSingletonIndex S ≤ S.stepCount := by
  classical
  unfold ContractionSequence.firstRootChildrenNonSingletonIndex
  exact Nat.find_min' (ContractionSequence.exists_not_rootChildrenSingleton S)
    (ContractionSequence.not_rootChildrenSingleton_final S)

theorem ContractionSequence.firstRootChildrenNonSingletonIndex_pos
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    0 < ContractionSequence.firstRootChildrenNonSingletonIndex S := by
  by_contra hpos
  have hzero : ContractionSequence.firstRootChildrenNonSingletonIndex S = 0 := by omega
  have hnot := ContractionSequence.not_rootChildrenSingleton_first S
  have hroot := ContractionSequence.rootChildrenSingleton_zero S
  rw [hzero] at hnot
  exact hnot hroot

/-- The predecessor of the first failed root-child-singleton state still has
all root children singleton. -/
theorem ContractionSequence.rootChildrenSingleton_before_first_pred
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    RootChildrenSingleton
      (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags := by
  apply ContractionSequence.rootChildrenSingleton_before_first
  have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
  omega

/-- The predecessor of the first failed root-child-singleton state is a genuine
contraction step. -/
theorem ContractionSequence.first_pred_lt_stepCount
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 < S.stepCount := by
  have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
  have hle := ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
  omega

theorem ContractionSequence.first_pred_succ
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 + 1 =
      ContractionSequence.firstRootChildrenNonSingletonIndex S := by
  have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
  omega

/-- Claim-15 sequence form.  Before the first root-child contraction, if an
internal tree vertex is no longer a singleton part, then it already satisfied
property `P` at some earlier state. -/
theorem ContractionSequence.exists_hasManyChildrenInPart_before_of_not_tree_singleton
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {i : ℕ}
    (hi : i < ContractionSequence.firstRootChildrenNonSingletonIndex S)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : IsInternal u)
    (hnotSingleton :
      ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∉ (S.state i).bags) :
    ∃ j < i,
      HasManyChildrenInPart (S.state j).bags u hlevel (manyChildrenThreshold k) := by
  classical
  let U : Finset (BonnetDepresVertex k) := {Sum.inr u}
  have hex : ∃ t : ℕ, t ≤ i ∧ U ∉ (S.state t).bags :=
    ⟨i, le_rfl, by simpa [U] using hnotSingleton⟩
  let t := Nat.find hex
  have ht_spec : t ≤ i ∧ U ∉ (S.state t).bags := by
    simpa [t] using Nat.find_spec hex
  have hstart : U ∈ (S.state 0).bags := by
    rw [S.starts.1]
    exact Finset.mem_image.mpr ⟨Sum.inr u, by simp, by simp [U]⟩
  have ht_pos : 0 < t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    exact ht_spec.2 (by simpa [ht0] using hstart)
  let p := t - 1
  have hp_succ : p + 1 = t := by
    have := ht_pos
    omega
  have hp_lt_i : p < i := by
    have := ht_spec.1
    omega
  have hp_singleton : U ∈ (S.state p).bags := by
    by_contra hpnot
    have hp_lt_t : p < t := by
      have := ht_pos
      omega
    have hp_le_i : p ≤ i := le_of_lt hp_lt_i
    exact (Nat.find_min hex hp_lt_t) ⟨hp_le_i, hpnot⟩
  have hp_lt_step : p < S.stepCount := by
    have hfirst_le :=
      ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  rcases S.step_contracts p hp_lt_step with
    ⟨A, hA, B, hB, hAB, hbags, _hredStep, _hblackStep⟩
  have hnext_not : U ∉ (S.state (p + 1)).bags := by
    simpa [hp_succ] using ht_spec.2
  have hside : A = U ∨ B = U := by
    by_contra hno
    have hAU : A ≠ U := by
      intro h
      exact hno (Or.inl h)
    have hBU : B ≠ U := by
      intro h
      exact hno (Or.inr h)
    have hmem_next : U ∈ (S.state (p + 1)).bags := by
      rw [hbags, mem_merge_family_iff]
      right
      exact ⟨hp_singleton, hAU.symm, hBU.symm⟩
    exact hnext_not hmem_next
  have hrootNext :
      RootChildrenSingleton (S.state (p + 1)).bags :=
    ContractionSequence.rootChildrenSingleton_before_first S (by omega)
  have hpartP : IsBagPartition (S.state p).bags :=
    Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state p)
  have hpartQ : IsBagPartition (S.state (p + 1)).bags :=
    Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state (p + 1))
  have hredQ :
      PartitionRedDegreeAtMost (bonnetDepresGraph k) (S.state (p + 1)).bags d :=
    Lax3Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
      S (by
        have hfirst_le :=
          ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
        omega)
  rcases hside with hAU | hBU
  · refine ⟨p, hp_lt_i, ?_⟩
    have hBne : B ≠ U := by
      intro hBU
      exact hAB (by rw [hAU, hBU])
    have hQ :
        (S.state (p + 1)).bags =
          insert (U ∪ B) (((S.state p).bags.erase U).erase B) := by
      simpa [U, hAU] using hbags
    exact hasManyChildrenInPart_before_merge_singleton_parent
      (k := k) (d := d) (P := (S.state p).bags)
      (Q := (S.state (p + 1)).bags) (B := B) (u := u)
      hd hpartP hpartQ hrootNext hredQ
      (by simpa [U] using hp_singleton) hB (by simpa [U] using hBne)
      hlevel hQ
  · refine ⟨p, hp_lt_i, ?_⟩
    have hAne : A ≠ U := by
      intro hAU
      exact hAB (by rw [hAU, hBU])
    have hQ :
        (S.state (p + 1)).bags =
          insert (U ∪ A) (((S.state p).bags.erase U).erase A) := by
      rw [hbags, hBU, Finset.union_comm]
      congr 1
      ext C
      by_cases hCU : C = U
      · subst C
        by_cases hAU' : A = U
        · subst A
          simp
        · simp
      · by_cases hCA : C = A
        · subst C
          simp [hCU]
        · simp [hCU, hCA]
    exact hasManyChildrenInPart_before_merge_singleton_parent
      (k := k) (d := d) (P := (S.state p).bags)
      (Q := (S.state (p + 1)).bags) (B := A) (u := u)
      hd hpartP hpartQ hrootNext hredQ
      (by simpa [U] using hp_singleton) hA (by simpa [U] using hAne)
      hlevel hQ

/-- In the first step where the root-child singleton invariant fails, one of the
two merged bags is a root-child singleton bag. -/
theorem ContractionSequence.exists_rootChildBag_in_first_failed_step
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ∃ A ∈ (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags,
      ∃ B ∈ (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags,
        A ≠ B ∧
          (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
            insert (A ∪ B)
              (((S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags.erase A).erase B) ∧
          ∃ f : Fin (bonnetDepresApexCount k) → Bool,
            A = rootChildBag k f ∨ B = rootChildBag k f := by
  classical
  let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
  have hi : i < S.stepCount := ContractionSequence.first_pred_lt_stepCount S
  have hisucc :
      i + 1 = ContractionSequence.firstRootChildrenNonSingletonIndex S := by
    simpa [i] using ContractionSequence.first_pred_succ S
  rcases S.step_contracts i hi with
    ⟨A, hA, B, hB, hAB, hbags, _hred, _hblack⟩
  refine ⟨A, hA, B, hB, hAB, ?_, ?_⟩
  · simpa [i, hisucc] using hbags
  · by_contra hno
    have hAnot : ∀ f : Fin (bonnetDepresApexCount k) → Bool, A ≠ rootChildBag k f := by
      intro f hAf
      exact hno ⟨f, Or.inl hAf⟩
    have hBnot : ∀ f : Fin (bonnetDepresApexCount k) → Bool, B ≠ rootChildBag k f := by
      intro f hBf
      exact hno ⟨f, Or.inr hBf⟩
    have hrootPrev :
        RootChildrenSingleton
          (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags :=
      ContractionSequence.rootChildrenSingleton_before_first_pred S
    have hrootNext :
        RootChildrenSingleton (S.state (i + 1)).bags := by
      rw [hbags]
      exact rootChildrenSingleton_merge_of_not_rootChildBag
        (by simpa [i] using hrootPrev) hAnot hBnot
    have hnotFirst := ContractionSequence.not_rootChildrenSingleton_first S
    rw [← hisucc] at hnotFirst
    exact hnotFirst hrootNext

/-- At the last state before the first contraction involving a root child, some
root child already satisfies property `P`. -/
theorem ContractionSequence.exists_rootChild_hasManyChildrenInPart_before_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      HasManyChildrenInPart
        (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags
        (rootChildWithNeighborhood k f)
        (rootChildWithNeighborhood_isInternal k f)
        (manyChildrenThreshold k) := by
  classical
  let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
  have hfirst_le :
      ContractionSequence.firstRootChildrenNonSingletonIndex S ≤ S.stepCount :=
    ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
  have hprevRoot :
      RootChildrenSingleton (S.state i).bags := by
    simpa [i] using ContractionSequence.rootChildrenSingleton_before_first_pred S
  have hpartPrev : IsBagPartition (S.state i).bags :=
    Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i)
  have hpartFirst :
      IsBagPartition (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags :=
    Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition
      (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S))
  have hredFirst :
      PartitionRedDegreeAtMost (bonnetDepresGraph k)
        (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags d :=
    Lax3Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
      S hfirst_le
  rcases ContractionSequence.exists_rootChildBag_in_first_failed_step S with
    ⟨A, hA, B, hB, hAB, hbags, hrootSide⟩
  rcases hrootSide with ⟨f₀, hAroot | hBroot⟩
  · let u := rootChildWithNeighborhood k f₀
    have hsingleP :
        ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ (S.state i).bags := by
      simpa [i, u, rootChildBag] using (by simpa [hAroot] using hA)
    have hBne : B ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
      intro hBroot'
      apply hAB
      rw [hAroot, hBroot']
      simp [u, rootChildBag]
    rcases hpartPrev.1 hB with ⟨z, hzB⟩
    cases z with
    | inl x =>
        exfalso
        have hQ :
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
              insert (rootChildBag k f₀ ∪ B)
                (((S.state i).bags.erase (rootChildBag k f₀)).erase B) := by
          simpa [i, hAroot] using hbags
        exact false_of_merge_rootChildBag_with_apex
          (k := k) (d := d) (P := (S.state i).bags)
          (Q := (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags)
          (B := B) (x := x) (f₀ := f₀)
          hd hprevRoot hredFirst hzB hQ
    | inr w =>
        refine ⟨f₀, ?_⟩
        have hQ :
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
              insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
                (((S.state i).bags.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B) := by
          simpa [i, hAroot, u, rootChildBag] using hbags
        exact hasManyChildrenInPart_before_merge_singleton_parent_with_tree_witness
          (k := k) (d := d) (P := (S.state i).bags)
          (Q := (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags)
          (B := B) (u := u) (w := w)
          hd hpartPrev hpartFirst hredFirst hsingleP hB hBne hzB
          (rootChildWithNeighborhood_isInternal k f₀) hQ
  · let u := rootChildWithNeighborhood k f₀
    have hsingleP :
        ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ (S.state i).bags := by
      simpa [i, u, rootChildBag] using (by simpa [hBroot] using hB)
    have hAne : A ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
      intro hAroot'
      apply hAB
      rw [hAroot', hBroot]
      simp [u, rootChildBag]
    rcases hpartPrev.1 hA with ⟨z, hzA⟩
    cases z with
    | inl x =>
        exfalso
        have hQ :
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
              insert (A ∪ rootChildBag k f₀)
                (((S.state i).bags.erase A).erase (rootChildBag k f₀)) := by
          simpa [i, hBroot] using hbags
        exact false_of_merge_apex_with_rootChildBag
          (k := k) (d := d) (P := (S.state i).bags)
          (Q := (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags)
          (B := A) (x := x) (f₀ := f₀)
          hd hprevRoot hredFirst hzA hQ
    | inr w =>
        refine ⟨f₀, ?_⟩
        have hQ :
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
              insert (A ∪ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
                (((S.state i).bags.erase A).erase ({Sum.inr u} : Finset (BonnetDepresVertex k))) := by
          simpa [i, hBroot, u, rootChildBag] using hbags
        exact hasManyChildrenInPart_before_merge_tree_witness_with_singleton_parent
          (k := k) (d := d) (P := (S.state i).bags)
          (Q := (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags)
          (B := A) (u := u) (w := w)
          hd hpartPrev hpartFirst hredFirst hsingleP hA hAne hzA
          (rootChildWithNeighborhood_isInternal k f₀) hQ

/-- At the last state before the first root-child contraction, some child of the
root satisfies property `Q`. -/
theorem ContractionSequence.exists_rootChild_qProperty_before_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      QProperty
        (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags
        (rootChildWithNeighborhood k f) := by
  classical
  let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
  have hi_le : i ≤ S.stepCount :=
    (ContractionSequence.first_pred_lt_stepCount S).le
  have hroot :
      RootChildrenSingleton (S.state i).bags := by
    simpa [i] using ContractionSequence.rootChildrenSingleton_before_first_pred S
  have hred :
      PartitionRedDegreeAtMost (bonnetDepresGraph k) (S.state i).bags d :=
    Lax3Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
      S hi_le
  rcases ContractionSequence.exists_rootChild_hasManyChildrenInPart_before_first
    S hd with ⟨f, hP⟩
  refine ⟨f, ?_⟩
  exact
    Lax3Proofs.TwinWidth.SimpleGraph.BonnetDepres.qProperty_of_hasManyChildrenInPart
      (k := k) (d := d) (P := (S.state i).bags)
      (u := rootChildWithNeighborhood k f)
      (hlevel := rootChildWithNeighborhood_isInternal k f)
      hd (Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
      hroot hred (by simpa [i] using hP)

/-- A state has a root child satisfying property `Q`. -/
def ContractionSequence.RootChildQAt {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) (i : ℕ) : Prop :=
  ∃ f : Fin (bonnetDepresApexCount k) → Bool,
    QProperty (S.state i).bags (rootChildWithNeighborhood k f)

/-- The first state, before the first root-child contraction, in which a root
child satisfies `Q`. -/
noncomputable def ContractionSequence.firstRootChildQIndex {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) : ℕ :=
  by
    classical
    exact Nat.find (by
      let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
      rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with
        ⟨f, hQ⟩
      exact ⟨i, le_rfl, f, hQ⟩ :
        ∃ i : ℕ,
          i ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 ∧
            ContractionSequence.RootChildQAt S i)

theorem ContractionSequence.firstRootChildQIndex_le_before_first_pred {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ContractionSequence.firstRootChildQIndex S hd ≤
      ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 := by
  classical
  unfold ContractionSequence.firstRootChildQIndex
  exact (Nat.find_spec (by
    let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
    rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with
      ⟨f, hQ⟩
    exact ⟨i, le_rfl, f, hQ⟩ :
      ∃ i : ℕ,
        i ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 ∧
          ContractionSequence.RootChildQAt S i)).1

theorem ContractionSequence.rootChildQAt_firstRootChildQIndex {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ContractionSequence.RootChildQAt S
      (ContractionSequence.firstRootChildQIndex S hd) := by
  classical
  unfold ContractionSequence.firstRootChildQIndex
  exact (Nat.find_spec (by
    let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
    rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with
      ⟨f, hQ⟩
    exact ⟨i, le_rfl, f, hQ⟩ :
      ∃ i : ℕ,
        i ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 ∧
          ContractionSequence.RootChildQAt S i)).2

theorem ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {i : ℕ}
    (hi : i < ContractionSequence.firstRootChildQIndex S hd) :
    ¬ ContractionSequence.RootChildQAt S i := by
  classical
  intro hQ
  have hfirst_le :
      ContractionSequence.firstRootChildQIndex S hd ≤
        ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 :=
    ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
  have hi_bound :
      i ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 :=
    hi.le.trans hfirst_le
  unfold ContractionSequence.firstRootChildQIndex at hi
  exact (Nat.find_min (by
    let j := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
    rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with
      ⟨f, hQf⟩
    exact ⟨j, le_rfl, f, hQf⟩ :
      ∃ j : ℕ,
        j ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 ∧
          ContractionSequence.RootChildQAt S j) hi) ⟨hi_bound, hQ⟩

/-- The first root-child-`Q` state is not the initial singleton-bag state. -/
theorem ContractionSequence.firstRootChildQIndex_pos {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    0 < ContractionSequence.firstRootChildQIndex S hd := by
  by_contra hnot
  have hzero : ContractionSequence.firstRootChildQIndex S hd = 0 := by omega
  have hQ :
      ContractionSequence.RootChildQAt S 0 := by
    simpa [hzero] using
      ContractionSequence.rootChildQAt_firstRootChildQIndex S hd
  rcases hQ with ⟨f, hQf⟩
  have hQsingleton :
      QProperty (TrigraphState.singletonBags (BonnetDepresVertex k))
        (rootChildWithNeighborhood k f) := by
    simpa [S.starts.1] using hQf
  exact not_rootChildQAt_singletonBags ⟨f, hQsingleton⟩

/-- If an internal node did not already have property `Q` immediately before the
first root-child-`Q` state, then its current part is still a singleton. -/
theorem ContractionSequence.treeVertex_singleton_of_not_qProperty_before_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : IsInternal u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈
      (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags := by
  classical
  by_contra hnotSingleton
  let i := ContractionSequence.firstRootChildQIndex S hd
  have hi_first : i < ContractionSequence.firstRootChildrenNonSingletonIndex S := by
    have hle := ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
    have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
    omega
  rcases ContractionSequence.exists_hasManyChildrenInPart_before_of_not_tree_singleton
      S hd hi_first hlevel (by simpa [i] using hnotSingleton) with
    ⟨j, hj_lt_i, hPj⟩
  have hi_pos : 0 < i := by
    simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
  have hj_le_pred : j ≤ i - 1 := by omega
  have hpred_le_step : i - 1 ≤ S.stepCount := by
    have hfirst_le := ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  have hPpred :
      HasManyChildrenInPart (S.state (i - 1)).bags u hlevel
        (manyChildrenThreshold k) :=
    Lax3Proofs.TwinWidth.SimpleGraph.BonnetDepres.ContractionSequence.hasManyChildrenInPart_mono
      S hj_le_pred hpred_le_step hPj
  have hrootPred :
      RootChildrenSingleton (S.state (i - 1)).bags :=
    ContractionSequence.rootChildrenSingleton_before_first S (by omega)
  have hQpred :
      QProperty (S.state (i - 1)).bags u :=
    Lax3Proofs.TwinWidth.SimpleGraph.BonnetDepres.ContractionSequence.qProperty_of_hasManyChildrenInPart
      S hpred_le_step hd hrootPred hPpred
  exact hnotPrev (by simpa [i] using hQpred)

/-- The first root-child-`Q` state still lies in the protected initial segment. -/
theorem ContractionSequence.rootChildrenSingleton_firstRootChildQIndex {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    RootChildrenSingleton
      (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags := by
  apply ContractionSequence.rootChildrenSingleton_before_first
  have hle :=
    ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
  have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
  omega

/-- At the first root-child-`Q` state, the witnessing root child has two
children satisfying `Q`. -/
theorem ContractionSequence.exists_two_child_qProperties_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      ∃ hlevel : IsInternal (rootChildWithNeighborhood k f),
        ∃ c₁ ∈ childSet (rootChildWithNeighborhood k f) hlevel,
          ∃ c₂ ∈ childSet (rootChildWithNeighborhood k f) hlevel,
            c₁ ≠ c₂ ∧
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags c₁ ∧
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags c₂ := by
  rcases ContractionSequence.rootChildQAt_firstRootChildQIndex S hd with
    ⟨f, hQ⟩
  rcases exists_two_child_qProperties_of_qProperty_nonpreleaf
      (rootChildWithNeighborhood_isNonPreleafInternal k f) hQ with
    ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, hQ₂⟩
  exact ⟨f, hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, hQ₂⟩

/-- At the first root-child-`Q` state, one child of the witnessing root child is
itself a new `Q` witness, while a distinct sibling already supplies the side
branch. -/
theorem ContractionSequence.exists_new_child_and_sibling_qProperty_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      ∃ hlevel : IsInternal (rootChildWithNeighborhood k f),
        ∃ v ∈ childSet (rootChildWithNeighborhood k f) hlevel,
          ∃ q ∈ childSet (rootChildWithNeighborhood k f) hlevel,
            v ≠ q ∧
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags v ∧
              ¬ QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags v ∧
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q ∧
              ({Sum.inr (rootChildWithNeighborhood k f)} :
                Finset (BonnetDepresVertex k)) ∈
                  (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases ContractionSequence.exists_two_child_qProperties_firstRootChildQIndex S hd with
    ⟨f, hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, hQ₂⟩
  have hi_pos : 0 < i := by
    simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
  have hnotBoth :
      ¬ (QProperty (S.state (i - 1)).bags c₁ ∧
        QProperty (S.state (i - 1)).bags c₂) := by
    rintro ⟨hQ₁prev, hQ₂prev⟩
    have hRootPrev :
        QProperty (S.state (i - 1)).bags (rootChildWithNeighborhood k f) :=
      qProperty_of_two_child_qProperties
        (rootChildWithNeighborhood_isNonPreleafInternal k f)
        hc₁ hc₂ hcne hQ₁prev hQ₂prev
    have hRootChildPrev : ContractionSequence.RootChildQAt S (i - 1) :=
      ⟨f, hRootPrev⟩
    exact
      (ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex
        S hd (by omega : i - 1 < ContractionSequence.firstRootChildQIndex S hd))
        (by simpa [i] using hRootChildPrev)
  have hparentSingleton :
      ({Sum.inr (rootChildWithNeighborhood k f)} :
        Finset (BonnetDepresVertex k)) ∈ (S.state i).bags := by
    have hroot :=
      ContractionSequence.rootChildrenSingleton_firstRootChildQIndex S hd
    simpa [i] using hroot f
  by_cases hQ₁prev : QProperty (S.state (i - 1)).bags c₁
  · have hQ₂prev :
        ¬ QProperty (S.state (i - 1)).bags c₂ := by
      intro h
      exact hnotBoth ⟨hQ₁prev, h⟩
    refine ⟨f, hlevel, c₂, hc₂, c₁, hc₁, ?_, hQ₂, hQ₂prev, hQ₁, ?_⟩
    · exact hcne.symm
    · simpa [i] using hparentSingleton
  · refine ⟨f, hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, ?_, hQ₂, ?_⟩
    · simpa [i] using hQ₁prev
    · simpa [i] using hparentSingleton

/-- General first-state branching step: a non-preleaf internal node whose `Q`
appears for the first time at the first root-child-`Q` state has a new `Q` child
and a distinct `Q` sibling, and the node itself is still singleton. -/
theorem ContractionSequence.exists_new_child_and_sibling_qProperty_of_new_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hnonpreleaf : IsNonPreleafInternal u)
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ∃ hlevel : IsInternal u,
      ∃ v ∈ childSet u hlevel,
        ∃ q ∈ childSet u hlevel,
          v ≠ q ∧
            QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags v ∧
            ¬ QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags v ∧
            QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q ∧
            ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases exists_two_child_qProperties_of_qProperty_nonpreleaf hnonpreleaf hQ with
    ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, hQ₂⟩
  have hnotBoth :
      ¬ (QProperty (S.state (i - 1)).bags c₁ ∧
        QProperty (S.state (i - 1)).bags c₂) := by
    rintro ⟨hQ₁prev, hQ₂prev⟩
    have hQprev :
        QProperty (S.state (i - 1)).bags u :=
      qProperty_of_two_child_qProperties hnonpreleaf hc₁ hc₂ hcne hQ₁prev hQ₂prev
    exact hnotPrev (by simpa [i] using hQprev)
  have hparentSingleton :
      ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ (S.state i).bags := by
    exact
      ContractionSequence.treeVertex_singleton_of_not_qProperty_before_firstRootChildQIndex
        S hd (isNonPreleafInternal.isInternal hnonpreleaf) hnotPrev
  by_cases hQ₁prev : QProperty (S.state (i - 1)).bags c₁
  · have hQ₂prev :
        ¬ QProperty (S.state (i - 1)).bags c₂ := by
      intro h
      exact hnotBoth ⟨hQ₁prev, h⟩
    refine ⟨hlevel, c₂, hc₂, c₁, hc₁, ?_, hQ₂, ?_, hQ₁, ?_⟩
    · exact hcne.symm
    · simpa [i] using hQ₂prev
    · simpa [i] using hparentSingleton
  · refine ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, ?_, hQ₂, ?_⟩
    · simpa [i] using hQ₁prev
    · simpa [i] using hparentSingleton

/-- Claim-18 inductive core.  From a node whose `Q` first appears at the first
root-child-`Q` state, one can follow the newly appearing child and collect `n`
side branches satisfying `Q`; every collected side branch has a singleton parent
at that state. -/
theorem ContractionSequence.exists_sideBranchSet_of_new_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ∀ n : ℕ,
      n ≤ bonnetDepresDepth k - u.1.val - 1 →
        ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
          Qs.card = n ∧
            (∀ ⦃q⦄, q ∈ Qs →
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
            (∀ ⦃q⦄, q ∈ Qs →
              ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
                FullTreeNode.IsParent p q ∧
                  ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                    (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
            (∀ ⦃q⦄, q ∈ Qs → u.1.val < q.1.val) := by
  intro n
  induction n generalizing u with
  | zero =>
      intro _hn
      refine ⟨∅, by simp, ?_, ?_, ?_⟩
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
  | succ n ih =>
      intro hn
      have hnonpreleaf : IsNonPreleafInternal u := by
        unfold IsNonPreleafInternal
        omega
      rcases ContractionSequence.exists_new_child_and_sibling_qProperty_of_new_qProperty
          S hd hnonpreleaf hQ hnotPrev with
        ⟨hlevel, v, hvchild, q, hqchild, hvq, hQv, hnotPrevV, hQq, huSingleton⟩
      have hvLevel := level_eq_succ_of_mem_childSet hvchild
      have hqLevel := level_eq_succ_of_mem_childSet hqchild
      have hn_child : n ≤ bonnetDepresDepth k - v.1.val - 1 := by
        rw [hvLevel]
        omega
      rcases ih hQv hnotPrevV hn_child with
        ⟨Qs, hcard, hQmem, hparent, hlevel_gt⟩
      have hq_notMem : q ∉ Qs := by
        intro hqQs
        have hv_lt_qs := hlevel_gt hqQs
        rw [hqLevel, hvLevel] at hv_lt_qs
        omega
      refine ⟨insert q Qs, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hq_notMem, hcard]
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact hQq
        · exact hQmem hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact ⟨u, isParent_of_mem_childSet hqchild, huSingleton⟩
        · exact hparent hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · rw [hqLevel]
          omega
        · have hv_lt_r := hlevel_gt hr
          rw [hvLevel] at hv_lt_r
          omega

/-- Claim 18, without packaging the antichain relation: at the first
root-child-`Q` state there are `depth - 2` side-branch nodes satisfying `Q`,
each with a singleton parent. -/
theorem ContractionSequence.exists_sideBranchSet_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      Qs.card = bonnetDepresDepth k - 2 ∧
        (∀ ⦃q⦄, q ∈ Qs →
          QProperty
            (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
        (∀ ⦃q⦄, q ∈ Qs →
          ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            FullTreeNode.IsParent p q ∧
              ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases ContractionSequence.rootChildQAt_firstRootChildQIndex S hd with
    ⟨f, hQ⟩
  have hnotPrev :
      ¬ QProperty (S.state (i - 1)).bags (rootChildWithNeighborhood k f) := by
    intro hQprev
    have hRootChildPrev : ContractionSequence.RootChildQAt S (i - 1) :=
      ⟨f, hQprev⟩
    exact
      (ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex
        S hd (by
          have hi_pos : 0 < i := by
            simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
          omega : i - 1 < ContractionSequence.firstRootChildQIndex S hd))
        (by simpa [i] using hRootChildPrev)
  have hn :
      bonnetDepresDepth k - 2 ≤
        bonnetDepresDepth k - (rootChildWithNeighborhood k f).1.val - 1 := by
    rw [rootChildWithNeighborhood_level]
    have hdepth := two_lt_depth k
    omega
  rcases ContractionSequence.exists_sideBranchSet_of_new_qProperty
      S hd hQ (by simpa [i] using hnotPrev) (bonnetDepresDepth k - 2) hn with
    ⟨Qs, hcard, hQmem, hparent, _hlevel_gt⟩
  exact ⟨Qs, hcard, hQmem, hparent⟩

/-- Strengthened Claim-18 core: the collected side branches are descendants of
the starting node and form an ancestor-antichain. -/
theorem ContractionSequence.exists_antichain_sideBranchSet_of_new_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ∀ n : ℕ,
      n ≤ bonnetDepresDepth k - u.1.val - 1 →
        ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
          Qs.card = n ∧
            (∀ ⦃q⦄, q ∈ Qs →
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
            (∀ ⦃q⦄, q ∈ Qs →
              ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
                FullTreeNode.IsParent p q ∧
                  ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                    (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
            (∀ ⦃q⦄, q ∈ Qs → IsTreeAncestor u q) ∧
            (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
              ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) := by
  intro n
  induction n generalizing u with
  | zero =>
      intro _hn
      refine ⟨∅, by simp, ?_, ?_, ?_, ?_⟩
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro a ha
        simp at ha
  | succ n ih =>
      intro hn
      have hnonpreleaf : IsNonPreleafInternal u := by
        unfold IsNonPreleafInternal
        omega
      rcases ContractionSequence.exists_new_child_and_sibling_qProperty_of_new_qProperty
          S hd hnonpreleaf hQ hnotPrev with
        ⟨hlevel, v, hvchild, q, hqchild, hvq, hQv, hnotPrevV, hQq, huSingleton⟩
      have hvLevel := level_eq_succ_of_mem_childSet hvchild
      have hn_child : n ≤ bonnetDepresDepth k - v.1.val - 1 := by
        rw [hvLevel]
        omega
      rcases ih hQv hnotPrevV hn_child with
        ⟨Qs, hcard, hQmem, hparent, hdesc, hanti⟩
      have hq_notMem : q ∉ Qs := by
        intro hqQs
        exact not_isTreeAncestor_of_distinct_siblings
          hvchild hqchild hvq (hdesc hqQs) (isTreeAncestor_refl q)
      refine ⟨insert q Qs, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hq_notMem, hcard]
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact hQq
        · exact hQmem hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact ⟨u, isParent_of_mem_childSet hqchild, huSingleton⟩
        · exact hparent hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact isAncestor_of_mem_childSet hqchild
        · exact isTreeAncestor_trans (isAncestor_of_mem_childSet hvchild) (hdesc hr)
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with ha_eq | ha
        · rcases hb with hb_eq | hb
          · exact (hab (ha_eq.trans hb_eq.symm)).elim
          · constructor
            · intro hqb
              have hqb' : IsTreeAncestor q b := by
                simpa [ha_eq] using hqb
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq (hdesc hb) hqb'
            · intro hbq
              have hbq' : IsTreeAncestor b q := by
                simpa [ha_eq] using hbq
              have hvqAncestor : IsTreeAncestor v q :=
                isTreeAncestor_trans (hdesc hb) hbq'
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq hvqAncestor (isTreeAncestor_refl q)
        · rcases hb with hb_eq | hb
          · constructor
            · intro haq
              have haq' : IsTreeAncestor a q := by
                simpa [hb_eq] using haq
              have hvqAncestor : IsTreeAncestor v q :=
                isTreeAncestor_trans (hdesc ha) haq'
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq hvqAncestor (isTreeAncestor_refl q)
            · intro hqa
              have hqa' : IsTreeAncestor q a := by
                simpa [hb_eq] using hqa
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq (hdesc ha) hqa'
          · exact hanti ha hb hab

/-- Claim 18 with the ancestor-antichain property recorded explicitly. -/
theorem ContractionSequence.exists_antichain_sideBranchSet_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      Qs.card = bonnetDepresDepth k - 2 ∧
        (∀ ⦃q⦄, q ∈ Qs →
          QProperty
            (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
        (∀ ⦃q⦄, q ∈ Qs →
          ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            FullTreeNode.IsParent p q ∧
              ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
        (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
          ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases ContractionSequence.rootChildQAt_firstRootChildQIndex S hd with
    ⟨f, hQ⟩
  have hnotPrev :
      ¬ QProperty (S.state (i - 1)).bags (rootChildWithNeighborhood k f) := by
    intro hQprev
    have hRootChildPrev : ContractionSequence.RootChildQAt S (i - 1) :=
      ⟨f, hQprev⟩
    exact
      (ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex
        S hd (by
          have hi_pos : 0 < i := by
            simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
          omega : i - 1 < ContractionSequence.firstRootChildQIndex S hd))
        (by simpa [i] using hRootChildPrev)
  have hn :
      bonnetDepresDepth k - 2 ≤
        bonnetDepresDepth k - (rootChildWithNeighborhood k f).1.val - 1 := by
    rw [rootChildWithNeighborhood_level]
    have hdepth := two_lt_depth k
    omega
  rcases ContractionSequence.exists_antichain_sideBranchSet_of_new_qProperty
      S hd hQ (by simpa [i] using hnotPrev) (bonnetDepresDepth k - 2) hn with
    ⟨Qs, hcard, hQmem, hparent, _hdesc, hanti⟩
  exact ⟨Qs, hcard, hQmem, hparent, hanti⟩

/-- Strengthened Claim-18 core with the level ranking kept: collected side
branches are descendants of the starting node, form an ancestor-antichain, and
have pairwise distinct levels. -/
theorem ContractionSequence.exists_ranked_antichain_sideBranchSet_of_new_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ∀ n : ℕ,
      n ≤ bonnetDepresDepth k - u.1.val - 1 →
        ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
          Qs.card = n ∧
            (∀ ⦃q⦄, q ∈ Qs →
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
            (∀ ⦃q⦄, q ∈ Qs →
              ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
                FullTreeNode.IsParent p q ∧
                  ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                    (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
            (∀ ⦃q⦄, q ∈ Qs → IsTreeAncestor u q) ∧
            (∀ ⦃q⦄, q ∈ Qs → u.1.val < q.1.val) ∧
            (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
              ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) ∧
            (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
              a.1.val ≠ b.1.val) := by
  intro n
  induction n generalizing u with
  | zero =>
      intro _hn
      refine ⟨∅, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro a ha
        simp at ha
      · intro a ha
        simp at ha
  | succ n ih =>
      intro hn
      have hnonpreleaf : IsNonPreleafInternal u := by
        unfold IsNonPreleafInternal
        omega
      rcases ContractionSequence.exists_new_child_and_sibling_qProperty_of_new_qProperty
          S hd hnonpreleaf hQ hnotPrev with
        ⟨hlevel, v, hvchild, q, hqchild, hvq, hQv, hnotPrevV, hQq, huSingleton⟩
      have hvLevel := level_eq_succ_of_mem_childSet hvchild
      have hqLevel := level_eq_succ_of_mem_childSet hqchild
      have hn_child : n ≤ bonnetDepresDepth k - v.1.val - 1 := by
        rw [hvLevel]
        omega
      rcases ih hQv hnotPrevV hn_child with
        ⟨Qs, hcard, hQmem, hparent, hdesc, hlevel_gt, hanti, hlevel_ne⟩
      have hq_notMem : q ∉ Qs := by
        intro hqQs
        exact not_isTreeAncestor_of_distinct_siblings
          hvchild hqchild hvq (hdesc hqQs) (isTreeAncestor_refl q)
      refine ⟨insert q Qs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hq_notMem, hcard]
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact hQq
        · exact hQmem hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact ⟨u, isParent_of_mem_childSet hqchild, huSingleton⟩
        · exact hparent hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact isAncestor_of_mem_childSet hqchild
        · exact isTreeAncestor_trans (isAncestor_of_mem_childSet hvchild) (hdesc hr)
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · rw [hqLevel]
          omega
        · have hv_lt_r := hlevel_gt hr
          rw [hvLevel] at hv_lt_r
          omega
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with ha_eq | ha
        · rcases hb with hb_eq | hb
          · exact (hab (ha_eq.trans hb_eq.symm)).elim
          · constructor
            · intro hqb
              have hqb' : IsTreeAncestor q b := by
                simpa [ha_eq] using hqb
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq (hdesc hb) hqb'
            · intro hbq
              have hbq' : IsTreeAncestor b q := by
                simpa [ha_eq] using hbq
              have hvqAncestor : IsTreeAncestor v q :=
                isTreeAncestor_trans (hdesc hb) hbq'
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq hvqAncestor (isTreeAncestor_refl q)
        · rcases hb with hb_eq | hb
          · constructor
            · intro haq
              have haq' : IsTreeAncestor a q := by
                simpa [hb_eq] using haq
              have hvqAncestor : IsTreeAncestor v q :=
                isTreeAncestor_trans (hdesc ha) haq'
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq hvqAncestor (isTreeAncestor_refl q)
            · intro hqa
              have hqa' : IsTreeAncestor q a := by
                simpa [hb_eq] using hqa
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq (hdesc ha) hqa'
          · exact hanti ha hb hab
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with ha_eq | ha
        · rcases hb with hb_eq | hb
          · exact (hab (ha_eq.trans hb_eq.symm)).elim
          · intro hlevels
            have hv_lt_b := hlevel_gt hb
            have hq_eq_b : q.1.val = b.1.val := by
              simpa [ha_eq] using hlevels
            rw [← hq_eq_b, hqLevel, hvLevel] at hv_lt_b
            omega
        · rcases hb with hb_eq | hb
          · intro hlevels
            have hv_lt_a := hlevel_gt ha
            have ha_eq_q : a.1.val = q.1.val := by
              simpa [hb_eq] using hlevels
            rw [ha_eq_q, hqLevel, hvLevel] at hv_lt_a
            omega
          · exact hlevel_ne ha hb hab

/-- Claim 18 with level separation recorded explicitly. -/
theorem ContractionSequence.exists_ranked_antichain_sideBranchSet_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      Qs.card = bonnetDepresDepth k - 2 ∧
        (∀ ⦃q⦄, q ∈ Qs →
          QProperty
            (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
        (∀ ⦃q⦄, q ∈ Qs →
          ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            FullTreeNode.IsParent p q ∧
              ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
        (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
          ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) ∧
        (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
          a.1.val ≠ b.1.val) := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases ContractionSequence.rootChildQAt_firstRootChildQIndex S hd with
    ⟨f, hQ⟩
  have hnotPrev :
      ¬ QProperty (S.state (i - 1)).bags (rootChildWithNeighborhood k f) := by
    intro hQprev
    have hRootChildPrev : ContractionSequence.RootChildQAt S (i - 1) :=
      ⟨f, hQprev⟩
    exact
      (ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex
        S hd (by
          have hi_pos : 0 < i := by
            simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
          omega : i - 1 < ContractionSequence.firstRootChildQIndex S hd))
        (by simpa [i] using hRootChildPrev)
  have hn :
      bonnetDepresDepth k - 2 ≤
        bonnetDepresDepth k - (rootChildWithNeighborhood k f).1.val - 1 := by
    rw [rootChildWithNeighborhood_level]
    have hdepth := two_lt_depth k
    omega
  rcases ContractionSequence.exists_ranked_antichain_sideBranchSet_of_new_qProperty
      S hd hQ (by simpa [i] using hnotPrev) (bonnetDepresDepth k - 2) hn with
    ⟨Qs, hcard, hQmem, hparent, _hdesc, _hlevel_gt, hanti, hlevel_ne⟩
  exact ⟨Qs, hcard, hQmem, hparent, hanti, hlevel_ne⟩

/-- Every side-branch `Q` node at the first root-child-`Q` state has a
descendant preleaf whose `P` witness is a large child bag. -/
theorem ContractionSequence.exists_descendant_preleaf_largeChildBag_of_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) :
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      IsTreeAncestor q v ∧ IsPreleaf v ∧
        ∃ hlevel : IsInternal v,
          ∃ A ∈ largeChildBags
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
            manyChildrenThreshold k ≤ (A ∩ childVertexSet v hlevel).card := by
  rcases exists_preleaf_descendant_hasManyChildrenInPart_of_qProperty hQ with
    ⟨v, hqv, hpre, hlevel, hP⟩
  rcases exists_largeChildBag_of_hasManyChildrenInPart hP with
    ⟨A, hA, hmany⟩
  exact ⟨v, hqv, hpre, hlevel, A, hA, hmany⟩

/-- Side branches whose descendant preleaf uses the fixed large bag `A` as its
large child-bag witness. -/
noncomputable def sideBranchesWitnessedByLargeBag {k : ℕ}
    (Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)))
    (A : Finset (BonnetDepresVertex k)) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact Qs.filter fun q =>
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      IsTreeAncestor q v ∧ IsPreleaf v ∧
        ∃ hlevel : IsInternal v,
          manyChildrenThreshold k ≤ (A ∩ childVertexSet v hlevel).card

/-- A side branch witnessed by a fixed large bag is one of the original side
branches. -/
theorem sideBranchesWitnessedByLargeBag_subset {k : ℕ}
    {Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {A : Finset (BonnetDepresVertex k)} :
    sideBranchesWitnessedByLargeBag Qs A ⊆ Qs := by
  classical
  intro q hq
  rw [sideBranchesWitnessedByLargeBag, Finset.mem_filter] at hq
  exact hq.1

/-- Descendant choices from an ancestor-antichain are injective. -/
theorem descendant_choice_injective_of_antichain {k : ℕ}
    {Qs R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hRsubset : R ⊆ Qs)
    (hanti :
      ∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {vOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (vOf q)) :
    Function.Injective vOf := by
  intro a b hv
  by_contra hne
  have hab_ne : a.1 ≠ b.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hbdesc : IsTreeAncestor b.1 (vOf a) := by
    simpa [hv] using hdesc b
  have hcomp :=
    isTreeAncestor_or_isTreeAncestor_of_common_descendant
      (hdesc a) hbdesc
  have hanti_ab := hanti (hRsubset a.2) (hRsubset b.2) hab_ne
  rcases hcomp with hab | hba
  · exact hanti_ab.1 hab
  · exact hanti_ab.2 hba

/-- Parents of strict descendant choices from an ancestor-antichain are
injective. -/
theorem parent_choice_injective_of_antichain {k : ℕ}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q))
    (hstrict : ∀ q : {q // q ∈ R}, q.1.1.val < (zOf q).1.val) :
    Function.Injective pOf := by
  intro a b hpEq
  by_contra hne
  have hab_ne : a.1 ≠ b.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hap : IsTreeAncestor a.1 (pOf a) :=
    isTreeAncestor_parent_of_strict_descendant
      (hdesc a) (hparent a) (hstrict a)
  have hbp : IsTreeAncestor b.1 (pOf a) := by
    simpa [hpEq] using
      isTreeAncestor_parent_of_strict_descendant
        (hdesc b) (hparent b) (hstrict b)
  have hcomp :=
    isTreeAncestor_or_isTreeAncestor_of_common_descendant hap hbp
  have hanti_ab := hanti a.2 b.2 hab_ne
  rcases hcomp with hab | hba
  · exact hanti_ab.1 hab
  · exact hanti_ab.2 hba

/-- Parent choices remain injective for a ranked antichain even when a selected
descendant is allowed to be the side-branch node itself.  The only additional
case would be two siblings with the same parent, and the ranked-level invariant
rules that out. -/
theorem parent_choice_injective_of_ranked_antichain {k : ℕ}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q)) :
    Function.Injective pOf := by
  intro a b hpEq
  by_contra hne
  have hab_ne : a.1 ≠ b.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hanti_ab := hanti a.2 b.2 hab_ne
  have hlevel_ab := hlevel_ne a.2 b.2 hab_ne
  by_cases ha_strict : a.1.1.val < (zOf a).1.val
  · have hap : IsTreeAncestor a.1 (pOf a) :=
      isTreeAncestor_parent_of_strict_descendant
        (hdesc a) (hparent a) ha_strict
    by_cases hb_strict : b.1.1.val < (zOf b).1.val
    · have hbp : IsTreeAncestor b.1 (pOf a) := by
        simpa [hpEq] using
          isTreeAncestor_parent_of_strict_descendant
            (hdesc b) (hparent b) hb_strict
      rcases isTreeAncestor_or_isTreeAncestor_of_common_descendant hap hbp with
        hab | hba
      · exact hanti_ab.1 hab
      · exact hanti_ab.2 hba
    · have hb_level : b.1.1.val = (zOf b).1.val := by
        rcases hdesc b with ⟨hle, _⟩
        omega
      have hb_eq_z : b.1 = zOf b :=
        eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
          (hdesc b) (isTreeAncestor_refl (zOf b)) hb_level
      have hpb : FullTreeNode.IsParent (pOf a) b.1 := by
        simpa [hpEq, hb_eq_z] using hparent b
      have hab : IsTreeAncestor a.1 b.1 :=
        isTreeAncestor_trans hap (isTreeAncestor_of_isParent hpb)
      exact hanti_ab.1 hab
  · have ha_level : a.1.1.val = (zOf a).1.val := by
      rcases hdesc a with ⟨hle, _⟩
      omega
    have ha_eq_z : a.1 = zOf a :=
      eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
        (hdesc a) (isTreeAncestor_refl (zOf a)) ha_level
    have hpa : FullTreeNode.IsParent (pOf a) a.1 := by
      simpa [ha_eq_z] using hparent a
    by_cases hb_strict : b.1.1.val < (zOf b).1.val
    · have hbp : IsTreeAncestor b.1 (pOf a) := by
        simpa [hpEq] using
          isTreeAncestor_parent_of_strict_descendant
            (hdesc b) (hparent b) hb_strict
      have hba : IsTreeAncestor b.1 a.1 :=
        isTreeAncestor_trans hbp (isTreeAncestor_of_isParent hpa)
      exact hanti_ab.2 hba
    · have hb_level : b.1.1.val = (zOf b).1.val := by
        rcases hdesc b with ⟨hle, _⟩
        omega
      have hb_eq_z : b.1 = zOf b :=
        eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
          (hdesc b) (isTreeAncestor_refl (zOf b)) hb_level
      have hpb : FullTreeNode.IsParent (pOf a) b.1 := by
        simpa [hpEq, hb_eq_z] using hparent b
      have hpa_level := FullTreeNode.isParent_level hpa
      have hpb_level := FullTreeNode.isParent_level hpb
      exact hlevel_ab (by omega)

/-- The ancestor-antichain property passes to subsets. -/
theorem antichain_mono {k : ℕ}
    {R R' : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hsubset : R' ⊆ R)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) :
    ∀ ⦃a⦄, a ∈ R' → ∀ ⦃b⦄, b ∈ R' → a ≠ b →
      ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a := by
  intro a ha b hb hab
  exact hanti (hsubset ha) (hsubset hb) hab

/-- If one part contains the parent choices for at least two antichain branches,
then it is a non-singleton internal-tree part. -/
theorem mem_internalNonSingletonTreeBags_of_antichain_parent_family {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {C : Finset (BonnetDepresVertex k)}
    (hC : C ∈ P)
    (hRcard : 1 < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q))
    (hstrict : ∀ q : {q // q ∈ R}, q.1.1.val < (zOf q).1.val)
    (hpC : ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ C) :
    C ∈ internalNonSingletonTreeBags P := by
  classical
  rcases Finset.one_lt_card.mp hRcard with ⟨a, ha, b, hb, hab⟩
  let qa : {q // q ∈ R} := ⟨a, ha⟩
  let qb : {q // q ∈ R} := ⟨b, hb⟩
  have hinj : Function.Injective pOf :=
    parent_choice_injective_of_antichain
      (k := k) (R := R) hanti
      (zOf := zOf) (pOf := pOf) hdesc hparent hstrict
  have hp_ne : pOf qa ≠ pOf qb := by
    intro hp_eq
    exact hab (Subtype.ext_iff.mp (hinj hp_eq))
  exact mem_internalNonSingletonTreeBags_of_two_tree_vertices
    (k := k) (P := P) (A := C) (u := pOf qa) (v := pOf qb)
    hC (parent_level_lt_depth_of_isParent (hparent qa)) (hpC qa) (hpC qb) hp_ne

/-- One Claim-19 induction step, isolated from the bookkeeping that chooses the
current descendants.  The selected parents all lie outside the current bag `B`,
so red-degree pigeonholing finds one red-neighbor part containing many of them;
that part is a non-singleton internal-tree part. -/
theorem exists_internalNonSingletonTreeBag_of_antichain_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {COf : {q // q ∈ R} → Finset (BonnetDepresVertex k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hBz : ∀ q : {q // q ∈ R}, (Sum.inr (zOf q) : BonnetDepresVertex k) ∈ B)
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q))
    (hstrict : ∀ q : {q // q ∈ R}, q.1.1.val < (zOf q).1.val)
    (hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P)
    (hpC : ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q)
    (hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      n < (R.attach.filter fun q => COf q = C).card := by
  classical
  let redNeighbors := P.filter fun C => partitionRedAdj (bonnetDepresGraph k) B C
  have hmaps :
      ∀ q ∈ R.attach, COf q ∈ redNeighbors := by
    intro q _hq
    rw [Finset.mem_filter]
    refine ⟨hCOfP q, ?_⟩
    apply partitionRedAdj_symm
    exact partitionRedAdj_of_antichain_family_parent_part
      (k := k) (R := R) (B := B) (C := COf q) (a := q.1) (p := pOf q)
      q.2 hRone hanti
      (fun r hr => zOf ⟨r, hr⟩)
      (fun r hr => hdesc ⟨r, hr⟩)
      (fun r hr => hBz ⟨r, hr⟩)
      (hparent q) (hstrict q) (hCneB q).symm (hpC q)
  have hredCard : redNeighbors.card ≤ d := by
    simpa [redNeighbors] using hred hB
  have hpigeonMul :
      redNeighbors.card * n < R.attach.card := by
    have hle : redNeighbors.card * n ≤ d * n :=
      Nat.mul_le_mul_right _ hredCard
    exact hle.trans_lt (by simpa using hmul)
  rcases Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := R.attach) (t := redNeighbors) (f := COf) (n := n)
      hmaps hpigeonMul with
    ⟨C, hC, hfiber⟩
  let fiber := R.attach.filter fun q => COf q = C
  have hfiberOne : 1 < fiber.card := hn.trans_lt (by simpa [fiber] using hfiber)
  rcases Finset.one_lt_card.mp hfiberOne with
    ⟨qa, hqa, qb, hqb, hqab⟩
  have hqaC : COf qa = C := (Finset.mem_filter.mp hqa).2
  have hqbC : COf qb = C := (Finset.mem_filter.mp hqb).2
  have hinj : Function.Injective pOf :=
    parent_choice_injective_of_antichain
      (k := k) (R := R) hanti
      (zOf := zOf) (pOf := pOf) hdesc hparent hstrict
  have hp_ne : pOf qa ≠ pOf qb := by
    intro hp_eq
    exact hqab (hinj hp_eq)
  have hCP : C ∈ P := (Finset.mem_filter.mp hC).1
  have hCinternal : C ∈ internalNonSingletonTreeBags P :=
    mem_internalNonSingletonTreeBags_of_two_tree_vertices
      (k := k) (P := P) (A := C) (u := pOf qa) (v := pOf qb)
      hCP (parent_level_lt_depth_of_isParent (hparent qa))
      (by simpa [hqaC] using hpC qa)
      (by simpa [hqbC] using hpC qb)
      hp_ne
  exact ⟨C, hCinternal, by simpa [fiber] using hfiber⟩

/-- Avoiding version of the abstract Claim-19 step. -/
theorem exists_internalNonSingletonTreeBag_of_antichain_step_avoiding {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {COf : {q // q ∈ R} → Finset (BonnetDepresVertex k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hBz : ∀ q : {q // q ∈ R}, (Sum.inr (zOf q) : BonnetDepresVertex k) ∈ B)
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q))
    (hstrict : ∀ q : {q // q ∈ R}, q.1.1.val < (zOf q).1.val)
    (hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P)
    (hpC : ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q)
    (hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B)
    (havoid : ∀ q : {q // q ∈ R}, COf q ∉ F) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      C ∉ F ∧ n < (R.attach.filter fun q => COf q = C).card := by
  rcases exists_internalNonSingletonTreeBag_of_antichain_step
      (k := k) (d := d) (n := n) (P := P) (R := R) (B := B)
      hB hred hRone hn hmul hanti
      (zOf := zOf) (pOf := pOf) (COf := COf)
      hdesc hBz hparent hstrict hCOfP hpC hCneB with
    ⟨C, hCinternal, hfiber⟩
  have hfiberNonempty :
      (R.attach.filter fun q => COf q = C).Nonempty := by
    rw [← Finset.card_pos]
    exact (Nat.zero_le n).trans_lt hfiber
  rcases hfiberNonempty with ⟨q, hq⟩
  have hqC : COf q = C := (Finset.mem_filter.mp hq).2
  have hCnotF : C ∉ F := by
    intro hCF
    exact havoid q (by simpa [hqC] using hCF)
  exact ⟨C, hCinternal, hCnotF, hfiber⟩

/-- Concrete highest-descendant form of one Claim-19 step. -/
theorem exists_internalNonSingletonTreeBag_of_highestDescendant_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hnonempty :
      ∀ q : {q // q ∈ R}, (descendantsInBag B q.1).Nonempty)
    (hstrict :
      ∀ q : {q // q ∈ R},
        q.1.1.val < (highestDescendantInBag B q.1 (hnonempty q)).1.val) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      ∃ Rsub : Finset {q // q ∈ R},
        n < Rsub.card ∧
          ∀ q ∈ Rsub,
            (Sum.inr
              (highestParentInBag B q.1 (hnonempty q) (hstrict q)) :
                BonnetDepresVertex k) ∈ C := by
  classical
  let zOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestDescendantInBag B q.1 (hnonempty q)
  let pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestParentInBag B q.1 (hnonempty q) (hstrict q)
  let COf : {q // q ∈ R} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))
  have hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).1
  have hpC :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).2
  have hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B := by
    intro q hEq
    have hp_notMem :
        (Sum.inr (pOf q) : BonnetDepresVertex k) ∉ B := by
      dsimp [pOf]
      exact parent_notMem_bag_of_highestDescendant
        (A := B) (q := q.1) (h := hnonempty q)
        (hp := highestParentInBag_isParent) (hstrict q)
    exact hp_notMem (by simpa [hEq] using hpC q)
  rcases exists_internalNonSingletonTreeBag_of_antichain_step
      (k := k) (d := d) (n := n) (P := P) (R := R) (B := B)
      hB hred hRone hn hmul hanti
      (zOf := zOf) (pOf := pOf) (COf := COf)
      (by intro q; exact highestDescendantInBag_isAncestor (hnonempty q))
      (by intro q; exact highestDescendantInBag_mem_bag (hnonempty q))
      (by intro q; exact highestParentInBag_isParent)
      (by intro q; exact hstrict q)
      hCOfP hpC hCneB with
    ⟨C, hCinternal, hfiber⟩
  let Rsub := R.attach.filter fun q => COf q = C
  refine ⟨C, hCinternal, Rsub, by simpa [Rsub] using hfiber, ?_⟩
  intro q hq
  have hqC : COf q = C := (Finset.mem_filter.mp hq).2
  simpa [pOf, hqC] using hpC q

/-- Highest-descendant step with an explicit finite set of previously used bags
to avoid. -/
theorem exists_internalNonSingletonTreeBag_of_highestDescendant_step_avoiding
    {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hnonempty :
      ∀ q : {q // q ∈ R}, (descendantsInBag B q.1).Nonempty)
    (hstrict :
      ∀ q : {q // q ∈ R},
        q.1.1.val < (highestDescendantInBag B q.1 (hnonempty q)).1.val)
    (havoidParentParts :
      ∀ q : {q // q ∈ R},
        Classical.choose
          (hpart.2.2
            (Sum.inr
              (highestParentInBag B q.1 (hnonempty q) (hstrict q)) :
                BonnetDepresVertex k)) ∉ F) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      C ∉ F ∧
        ∃ Rsub : Finset {q // q ∈ R},
          n < Rsub.card ∧
            ∀ q ∈ Rsub,
              (Sum.inr
                (highestParentInBag B q.1 (hnonempty q) (hstrict q)) :
                  BonnetDepresVertex k) ∈ C := by
  classical
  let zOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestDescendantInBag B q.1 (hnonempty q)
  let pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestParentInBag B q.1 (hnonempty q) (hstrict q)
  let COf : {q // q ∈ R} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))
  have hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).1
  have hpC :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).2
  have hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B := by
    intro q hEq
    have hp_notMem :
        (Sum.inr (pOf q) : BonnetDepresVertex k) ∉ B := by
      dsimp [pOf]
      exact parent_notMem_bag_of_highestDescendant
        (A := B) (q := q.1) (h := hnonempty q)
        (hp := highestParentInBag_isParent) (hstrict q)
    exact hp_notMem (by simpa [hEq] using hpC q)
  have havoid : ∀ q : {q // q ∈ R}, COf q ∉ F := by
    intro q
    simpa [COf, pOf] using havoidParentParts q
  rcases exists_internalNonSingletonTreeBag_of_antichain_step_avoiding
      (k := k) (d := d) (n := n) (P := P) (R := R) (B := B)
      F hB hred hRone hn hmul hanti
      (zOf := zOf) (pOf := pOf) (COf := COf)
      (by intro q; exact highestDescendantInBag_isAncestor (hnonempty q))
      (by intro q; exact highestDescendantInBag_mem_bag (hnonempty q))
      (by intro q; exact highestParentInBag_isParent)
      (by intro q; exact hstrict q)
      hCOfP hpC hCneB havoid with
    ⟨C, hCinternal, hCnotF, hfiber⟩
  let Rsub := R.attach.filter fun q => COf q = C
  refine ⟨C, hCinternal, hCnotF, Rsub, by simpa [Rsub] using hfiber, ?_⟩
  intro q hq
  have hqC : COf q = C := (Finset.mem_filter.mp hq).2
  simpa [pOf, hqC] using hpC q

/-- Highest-descendant step packaged with the next branch set in the original
tree-node type. -/
theorem exists_nextBranches_of_highestDescendant_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hnonempty :
      ∀ q : {q // q ∈ R}, (descendantsInBag B q.1).Nonempty)
    (hstrict :
      ∀ q : {q // q ∈ R},
        q.1.1.val < (highestDescendantInBag B q.1 (hnonempty q)).1.val) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      ∃ Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
        Rnext ⊆ R ∧ n < Rnext.card ∧
          (∀ ⦃q⦄, q ∈ Rnext → (descendantsInBag C q).Nonempty) := by
  classical
  rcases exists_internalNonSingletonTreeBag_of_highestDescendant_step
      (k := k) (d := d) (n := n) (P := P) (R := R) (B := B)
      hpart hB hred hRone hn hmul hanti hnonempty hstrict with
    ⟨C, hC, Rsub, hRsubCard, hparentsC⟩
  let Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :=
    Rsub.image fun q => q.1
  have hRnextCard : Rnext.card = Rsub.card := by
    change (Rsub.image Subtype.val).card = Rsub.card
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact Subtype.ext hab
  refine ⟨C, hC, Rnext, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ Rsub.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, _hqsub, rfl⟩
    exact qsub.2
  · rwa [hRnextCard]
  · intro q hq
    change q ∈ Rsub.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, hqsub, rfl⟩
    refine ⟨highestParentInBag B qsub.1 (hnonempty qsub) (hstrict qsub), ?_⟩
    rw [mem_descendantsInBag]
    exact ⟨highestParentInBag_isAncestor, hparentsC qsub hqsub⟩

/-- Claim-19 one-step form matching the paper.  The selected descendant in the
current bag is the highest descendant and may equal the side branch.  The
ranked-level invariant and the singleton-parent invariant from Claim 18 ensure
that the pigeonholed next bag only keeps branches whose selected parent is
still a descendant of the original side branch. -/
theorem exists_nextBranches_of_ranked_highestDescendant_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val)
    (hparentSingleton :
      ∀ ⦃q⦄, q ∈ R →
        ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          FullTreeNode.IsParent p q ∧
            ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P)
    (hnonempty :
      ∀ q : {q // q ∈ R}, (descendantsInBag B q.1).Nonempty) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      ∃ Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
        Rnext ⊆ R ∧ n < Rnext.card ∧
          (∀ ⦃q⦄, q ∈ Rnext → (descendantsInBag C q).Nonempty) := by
  classical
  let zOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestDescendantInBag B q.1 (hnonempty q)
  have hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q) := by
    intro q
    exact highestDescendantInBag_isAncestor (hnonempty q)
  have hBz :
      ∀ q : {q // q ∈ R}, (Sum.inr (zOf q) : BonnetDepresVertex k) ∈ B := by
    intro q
    exact highestDescendantInBag_mem_bag (hnonempty q)
  have hz_pos : ∀ q : {q // q ∈ R}, 0 < (zOf q).1.val := by
    intro q
    rcases hparentSingleton q.2 with ⟨p, hp, _hpP⟩
    have hq_pos : 0 < q.1.1.val := by
      have hp_level := FullTreeNode.isParent_level hp
      omega
    rcases hdesc q with ⟨hqz, _⟩
    omega
  let pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => FullTreeNode.parent (zOf q) (hz_pos q)
  have hparent :
      ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q) := by
    intro q
    exact FullTreeNode.parent_isParent (zOf q) (hz_pos q)
  let COf : {q // q ∈ R} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))
  have hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).1
  have hpC :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).2
  have parentSingleton_of_nonstrict :
      ∀ q : {q // q ∈ R},
        ¬ q.1.1.val < (zOf q).1.val →
          ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) ∈ P := by
    intro q hnonstrict
    rcases hparentSingleton q.2 with ⟨p, hpq, hpP⟩
    have hz_level : q.1.1.val = (zOf q).1.val := by
      rcases hdesc q with ⟨hle, _⟩
      omega
    have hq_eq_z : q.1 = zOf q :=
      eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
        (hdesc q) (isTreeAncestor_refl (zOf q)) hz_level
    have hp_eq : pOf q = p :=
      FullTreeNode.isParent_unique (by simpa [hq_eq_z] using hparent q) hpq
    simpa [pOf, hp_eq] using hpP
  have hp_notMem_B :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∉ B := by
    intro q hpB
    by_cases hstrict : q.1.1.val < (zOf q).1.val
    · exact parent_notMem_bag_of_highestDescendant
        (A := B) (q := q.1) (p := pOf q) (h := hnonempty q)
        (hp := hparent q) hstrict hpB
    · have hsingletonP := parentSingleton_of_nonstrict q hstrict
      by_cases hBsingleton :
          B = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
      · have hzB : (Sum.inr (zOf q) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hBsingleton] using hBz q
        have hz_eq_p : zOf q = pOf q := by
          exact Sum.inr.inj (Finset.mem_singleton.mp hzB)
        exact FullTreeNode.not_isParent_self (zOf q) (by
          simpa [hz_eq_p] using hparent q)
      · have hdis := hpart.2.1 hB hsingletonP hBsingleton
        exact (Finset.disjoint_left.mp hdis) hpB (by simp)
  have hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B := by
    intro q hEq
    exact hp_notMem_B q (by simpa [hEq] using hpC q)
  let redNeighbors := P.filter fun C => partitionRedAdj (bonnetDepresGraph k) B C
  have hmaps :
      ∀ q ∈ R.attach, COf q ∈ redNeighbors := by
    intro q _hq
    rw [Finset.mem_filter]
    refine ⟨hCOfP q, ?_⟩
    apply partitionRedAdj_symm
    exact partitionRedAdj_of_ranked_antichain_family_parent_part
      (k := k) (R := R) (B := B) (C := COf q) (a := q.1) (p := pOf q)
      q.2 hRone hanti hlevel_ne
      (fun r hr => zOf ⟨r, hr⟩)
      (fun r hr => hdesc ⟨r, hr⟩)
      (fun r hr => hBz ⟨r, hr⟩)
      (hparent q) (hCneB q).symm (hpC q)
  have hredCard : redNeighbors.card ≤ d := by
    simpa [redNeighbors] using hred hB
  have hpigeonMul :
      redNeighbors.card * n < R.attach.card := by
    have hle : redNeighbors.card * n ≤ d * n :=
      Nat.mul_le_mul_right _ hredCard
    exact hle.trans_lt (by simpa using hmul)
  rcases Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := R.attach) (t := redNeighbors) (f := COf) (n := n)
      hmaps hpigeonMul with
    ⟨C, hC, hfiber⟩
  let fiber := R.attach.filter fun q => COf q = C
  have hfiberOne : 1 < fiber.card := hn.trans_lt (by simpa [fiber] using hfiber)
  have hCP : C ∈ P := (Finset.mem_filter.mp hC).1
  have hinj : Function.Injective pOf :=
    parent_choice_injective_of_ranked_antichain
      (k := k) (R := R) hanti hlevel_ne
      (zOf := zOf) (pOf := pOf) hdesc hparent
  have hstrict_of_fiber :
      ∀ q : {q // q ∈ R}, q ∈ fiber → q.1.1.val < (zOf q).1.val := by
    intro q hqfiber
    by_contra hnonstrict
    have hqC : COf q = C := (Finset.mem_filter.mp hqfiber).2
    have hsingletonP := parentSingleton_of_nonstrict q hnonstrict
    have hCsingleton :
        C = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
      by_cases hEq : C = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
      · exact hEq
      · have hdis := hpart.2.1 hCP hsingletonP hEq
        exact False.elim
          ((Finset.disjoint_left.mp hdis) (by simpa [← hqC] using hpC q) (by simp))
    have hfiber_le_one : fiber.card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro r s hr hs
      have hrC : COf r = C := (Finset.mem_filter.mp hr).2
      have hsC : COf s = C := (Finset.mem_filter.mp hs).2
      have hpr : pOf r = pOf q := by
        have hmem : (Sum.inr (pOf r) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hCsingleton, hrC] using hpC r
        exact Sum.inr.inj (Finset.mem_singleton.mp hmem)
      have hps : pOf s = pOf q := by
        have hmem : (Sum.inr (pOf s) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hCsingleton, hsC] using hpC s
        exact Sum.inr.inj (Finset.mem_singleton.mp hmem)
      exact (hinj (hpr.trans hps.symm))
    omega
  rcases Finset.one_lt_card.mp hfiberOne with ⟨qa, hqa, qb, hqb, hqab⟩
  have hqaC : COf qa = C := (Finset.mem_filter.mp hqa).2
  have hqbC : COf qb = C := (Finset.mem_filter.mp hqb).2
  have hp_ne : pOf qa ≠ pOf qb := by
    intro hp_eq
    exact hqab (hinj hp_eq)
  have hCinternal : C ∈ internalNonSingletonTreeBags P :=
    mem_internalNonSingletonTreeBags_of_two_tree_vertices
      (k := k) (P := P) (A := C) (u := pOf qa) (v := pOf qb)
      hCP (parent_level_lt_depth_of_isParent (hparent qa))
      (by simpa [hqaC] using hpC qa)
      (by simpa [hqbC] using hpC qb)
      hp_ne
  let Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :=
    fiber.image fun q => q.1
  have hRnextCard : Rnext.card = fiber.card := by
    change (fiber.image Subtype.val).card = fiber.card
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact Subtype.ext hab
  refine ⟨C, hCinternal, Rnext, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ fiber.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, _hqsub, rfl⟩
    exact qsub.2
  · rwa [hRnextCard]
  · intro q hq
    change q ∈ fiber.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, hqsub, rfl⟩
    refine descendantsInBag_nonempty_of_mem
      (q := qsub.1) (z := pOf qsub) ?_ ?_
    · exact isTreeAncestor_parent_of_strict_descendant
        (hdesc qsub) (hparent qsub) (hstrict_of_fiber qsub hqsub)
    · have hqC : COf qsub = C := (Finset.mem_filter.mp hqsub).2
      simpa [hqC] using hpC qsub

/-- Claim-19 step with the paper's path-avoidance invariant.  The next bag is
new with respect to the previously chosen bags, and the returned branch set has
available descendants for the enlarged previous-bag set. -/
theorem exists_nextBranches_of_availableDescendant_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val)
    (hparentSingleton :
      ∀ ⦃q⦄, q ∈ R →
        ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          FullTreeNode.IsParent p q ∧
            ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P)
    (hF_noSingleton :
      ∀ ⦃D⦄, D ∈ F →
        ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          D ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)))
    (havailable :
      ∀ q : {q // q ∈ R}, (availableDescendantsInBag F B q.1).Nonempty) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      C ∉ F ∧ C ≠ B ∧
        ∃ Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
          Rnext ⊆ R ∧ n < Rnext.card ∧
            (∀ ⦃q⦄, q ∈ Rnext →
              (availableDescendantsInBag (insert B F) C q).Nonempty) := by
  classical
  let zOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestAvailableDescendantInBag F B q.1 (havailable q)
  have hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q) := by
    intro q
    exact highestAvailableDescendantInBag_isAncestor (havailable q)
  have hBz :
      ∀ q : {q // q ∈ R}, (Sum.inr (zOf q) : BonnetDepresVertex k) ∈ B := by
    intro q
    exact highestAvailableDescendantInBag_mem_bag (havailable q)
  have hz_pos : ∀ q : {q // q ∈ R}, 0 < (zOf q).1.val := by
    intro q
    rcases hparentSingleton q.2 with ⟨p, hp, _hpP⟩
    have hq_pos : 0 < q.1.1.val := by
      have hp_level := FullTreeNode.isParent_level hp
      omega
    rcases hdesc q with ⟨hqz, _⟩
    omega
  let pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => FullTreeNode.parent (zOf q) (hz_pos q)
  have hparent :
      ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q) := by
    intro q
    exact FullTreeNode.parent_isParent (zOf q) (hz_pos q)
  let COf : {q // q ∈ R} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))
  have hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).1
  have hpC :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).2
  have parentSingleton_of_nonstrict :
      ∀ q : {q // q ∈ R},
        ¬ q.1.1.val < (zOf q).1.val →
          ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) ∈ P := by
    intro q hnonstrict
    rcases hparentSingleton q.2 with ⟨p, hpq, hpP⟩
    have hz_level : q.1.1.val = (zOf q).1.val := by
      rcases hdesc q with ⟨hle, _⟩
      omega
    have hq_eq_z : q.1 = zOf q :=
      eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
        (hdesc q) (isTreeAncestor_refl (zOf q)) hz_level
    have hp_eq : pOf q = p :=
      FullTreeNode.isParent_unique (by simpa [hq_eq_z] using hparent q) hpq
    simpa [pOf, hp_eq] using hpP
  have hp_notMem_B :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∉ B := by
    intro q hpB
    by_cases hstrict : q.1.1.val < (zOf q).1.val
    · exact parent_notMem_bag_of_highestAvailableDescendant
        (F := F) (B := B) (q := q.1) (p := pOf q) (h := havailable q)
        (hp := hparent q) hstrict hpB
    · have hsingletonP := parentSingleton_of_nonstrict q hstrict
      by_cases hBsingleton :
          B = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
      · have hzB : (Sum.inr (zOf q) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hBsingleton] using hBz q
        have hz_eq_p : zOf q = pOf q := by
          exact Sum.inr.inj (Finset.mem_singleton.mp hzB)
        exact FullTreeNode.not_isParent_self (zOf q) (by
          simpa [hz_eq_p] using hparent q)
      · have hdis := hpart.2.1 hB hsingletonP hBsingleton
        exact (Finset.disjoint_left.mp hdis) hpB (by simp)
  have hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B := by
    intro q hEq
    exact hp_notMem_B q (by simpa [hEq] using hpC q)
  have hCOf_notMem_F : ∀ q : {q // q ∈ R}, COf q ∉ F := by
    intro q hCF
    by_cases hstrict : q.1.1.val < (zOf q).1.val
    · have hqp : IsTreeAncestor q.1 (pOf q) :=
        isTreeAncestor_parent_of_strict_descendant
          (hdesc q) (hparent q) hstrict
      exact highestAvailableDescendantInBag_path_avoids (havailable q) hCF
        ⟨hqp, isTreeAncestor_of_isParent (hparent q)⟩ (hpC q)
    · have hsingletonP := parentSingleton_of_nonstrict q hstrict
      have hCsingleton : COf q = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
        by_cases hEq : COf q = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
        · exact hEq
        · have hdis := hpart.2.1 (hCOfP q) hsingletonP hEq
          exact False.elim
            ((Finset.disjoint_left.mp hdis) (hpC q) (by simp))
      exact hF_noSingleton hCF (pOf q) hCsingleton
  let redNeighbors := P.filter fun C => partitionRedAdj (bonnetDepresGraph k) B C
  have hmaps :
      ∀ q ∈ R.attach, COf q ∈ redNeighbors := by
    intro q _hq
    rw [Finset.mem_filter]
    refine ⟨hCOfP q, ?_⟩
    apply partitionRedAdj_symm
    exact partitionRedAdj_of_ranked_antichain_family_parent_part
      (k := k) (R := R) (B := B) (C := COf q) (a := q.1) (p := pOf q)
      q.2 hRone hanti hlevel_ne
      (fun r hr => zOf ⟨r, hr⟩)
      (fun r hr => hdesc ⟨r, hr⟩)
      (fun r hr => hBz ⟨r, hr⟩)
      (hparent q) (hCneB q).symm (hpC q)
  have hredCard : redNeighbors.card ≤ d := by
    simpa [redNeighbors] using hred hB
  have hpigeonMul :
      redNeighbors.card * n < R.attach.card := by
    have hle : redNeighbors.card * n ≤ d * n :=
      Nat.mul_le_mul_right _ hredCard
    exact hle.trans_lt (by simpa using hmul)
  rcases Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := R.attach) (t := redNeighbors) (f := COf) (n := n)
      hmaps hpigeonMul with
    ⟨C, hC, hfiber⟩
  let fiber := R.attach.filter fun q => COf q = C
  have hfiberOne : 1 < fiber.card := hn.trans_lt (by simpa [fiber] using hfiber)
  have hCP : C ∈ P := (Finset.mem_filter.mp hC).1
  have hinj : Function.Injective pOf :=
    parent_choice_injective_of_ranked_antichain
      (k := k) (R := R) hanti hlevel_ne
      (zOf := zOf) (pOf := pOf) hdesc hparent
  have hstrict_of_fiber :
      ∀ q : {q // q ∈ R}, q ∈ fiber → q.1.1.val < (zOf q).1.val := by
    intro q hqfiber
    by_contra hnonstrict
    have hqC : COf q = C := (Finset.mem_filter.mp hqfiber).2
    have hsingletonP := parentSingleton_of_nonstrict q hnonstrict
    have hCsingleton :
        C = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
      by_cases hEq : C = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
      · exact hEq
      · have hdis := hpart.2.1 hCP hsingletonP hEq
        exact False.elim
          ((Finset.disjoint_left.mp hdis) (by simpa [← hqC] using hpC q) (by simp))
    have hfiber_le_one : fiber.card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro r s hr hs
      have hrC : COf r = C := (Finset.mem_filter.mp hr).2
      have hsC : COf s = C := (Finset.mem_filter.mp hs).2
      have hpr : pOf r = pOf q := by
        have hmem : (Sum.inr (pOf r) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hCsingleton, hrC] using hpC r
        exact Sum.inr.inj (Finset.mem_singleton.mp hmem)
      have hps : pOf s = pOf q := by
        have hmem : (Sum.inr (pOf s) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hCsingleton, hsC] using hpC s
        exact Sum.inr.inj (Finset.mem_singleton.mp hmem)
      exact (hinj (hpr.trans hps.symm))
    omega
  rcases Finset.one_lt_card.mp hfiberOne with ⟨qa, hqa, qb, hqb, hqab⟩
  have hqaC : COf qa = C := (Finset.mem_filter.mp hqa).2
  have hqbC : COf qb = C := (Finset.mem_filter.mp hqb).2
  have hp_ne : pOf qa ≠ pOf qb := by
    intro hp_eq
    exact hqab (hinj hp_eq)
  have hCinternal : C ∈ internalNonSingletonTreeBags P :=
    mem_internalNonSingletonTreeBags_of_two_tree_vertices
      (k := k) (P := P) (A := C) (u := pOf qa) (v := pOf qb)
      hCP (parent_level_lt_depth_of_isParent (hparent qa))
      (by simpa [hqaC] using hpC qa)
      (by simpa [hqbC] using hpC qb)
      hp_ne
  have hCnotF : C ∉ F := by
    intro hCF
    exact hCOf_notMem_F qa (by simpa [hqaC] using hCF)
  have hCneB_final : C ≠ B := by
    intro hCB
    exact hCneB qa (by simp [hqaC, hCB])
  let Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :=
    fiber.image fun q => q.1
  have hRnextCard : Rnext.card = fiber.card := by
    change (fiber.image Subtype.val).card = fiber.card
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact Subtype.ext hab
  refine ⟨C, hCinternal, hCnotF, hCneB_final, Rnext, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ fiber.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, _hqsub, rfl⟩
    exact qsub.2
  · rwa [hRnextCard]
  · intro q hq
    change q ∈ fiber.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, hqsub, rfl⟩
    have hstrict := hstrict_of_fiber qsub hqsub
    have hqp : IsTreeAncestor qsub.1 (pOf qsub) :=
      isTreeAncestor_parent_of_strict_descendant
        (hdesc qsub) (hparent qsub) hstrict
    have hpCq : (Sum.inr (pOf qsub) : BonnetDepresVertex k) ∈ C := by
      have hqC : COf qsub = C := (Finset.mem_filter.mp hqsub).2
      simpa [hqC] using hpC qsub
    refine availableDescendantsInBag_nonempty_of_mem
      (F := insert B F) (B := C) (q := qsub.1) (z := pOf qsub)
      hqp hpCq ?_
    intro D hD x hxPath hxD
    rw [Finset.mem_insert] at hD
    rcases hD with hD_eq | hD_old
    · subst D
      have hxAvail : x ∈ availableDescendantsInBag F B qsub.1 := by
        rw [mem_availableDescendantsInBag]
        refine ⟨hxPath.1, hxD, ?_⟩
        intro D hD y hy
        exact highestAvailableDescendantInBag_path_avoids (havailable qsub) hD
          ⟨hy.1, isTreeAncestor_trans hy.2
            (isTreeAncestor_trans hxPath.2 (isTreeAncestor_of_isParent (hparent qsub)))⟩
      have hmin := (highestAvailableDescendantInBag_spec (havailable qsub)).2 x hxAvail
      have hz_le_x : (zOf qsub).1.val ≤ x.1.val := by
        simpa [zOf] using hmin
      have hx_le_p : x.1.val ≤ (pOf qsub).1.val := hxPath.2.1
      have hp_level : (zOf qsub).1.val = (pOf qsub).1.val + 1 :=
        FullTreeNode.isParent_level (hparent qsub)
      omega
    · exact highestAvailableDescendantInBag_path_avoids (havailable qsub) hD_old
        ⟨hxPath.1,
          isTreeAncestor_trans hxPath.2 (isTreeAncestor_of_isParent (hparent qsub))⟩ hxD

/-- Iterates the path-available Claim-19 step and accumulates distinct
non-singleton internal-tree bags. -/
theorem exists_internalNonSingletonTreeBags_of_available_iteration
    {k d steps : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    {Prev Count : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hPrev_noSingleton :
      ∀ ⦃D⦄, D ∈ Prev →
        ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          D ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)))
    (hB_noSingleton :
      ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        B ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)))
    (hCount_subset : Count ⊆ insert B Prev)
    (hCount_internal : Count ⊆ internalNonSingletonTreeBags P)
    (hcard : (manyChildrenThreshold k) ^ steps < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val)
    (hparentSingleton :
      ∀ ⦃q⦄, q ∈ R →
        ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          FullTreeNode.IsParent p q ∧
            ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P)
    (havailable :
      ∀ q : {q // q ∈ R}, (availableDescendantsInBag Prev B q.1).Nonempty) :
    ∃ Count' : Finset (Finset (BonnetDepresVertex k)),
      Count ⊆ Count' ∧ Count'.card = Count.card + steps ∧
        Count' ⊆ internalNonSingletonTreeBags P := by
  induction steps generalizing B Prev Count R with
  | zero =>
      refine ⟨Count, fun _ h => h, by omega, hCount_internal⟩
  | succ r ih =>
      have ht_one : 1 < (manyChildrenThreshold k) ^ (r + 1) := by
        exact one_lt_pow₀
          (lt_of_lt_of_le (by omega : 1 < 2) (two_le_manyChildrenThreshold k))
          (by omega)
      have hRone : 1 < R.card := by omega
      have hn : 1 ≤ (manyChildrenThreshold k) ^ r :=
        (pow_pos (manyChildrenThreshold_pos k) r).succ_le
      have hmul : d * (manyChildrenThreshold k) ^ r < R.card :=
        (redBound_mul_manyChildrenThreshold_pow_lt_succ
          (k := k) (d := d) (r := r) hd).trans hcard
      rcases exists_nextBranches_of_availableDescendant_step
          (k := k) (d := d) (n := (manyChildrenThreshold k) ^ r)
          (P := P) (R := R) (B := B)
          Prev hpart hB hred hRone hn hmul hanti hlevel_ne
          hparentSingleton hPrev_noSingleton havailable with
        ⟨C, hCinternal, hCnotPrev, hCneB, Rnext, hRnext_subset,
          hRnext_card, havailableNext⟩
      have hCnotCount : C ∉ Count := by
        intro hCCount
        have hCin : C ∈ insert B Prev := hCount_subset hCCount
        rw [Finset.mem_insert] at hCin
        rcases hCin with hCB | hCPrev
        · exact hCneB hCB
        · exact hCnotPrev hCPrev
      have hPrev_noSingleton' :
          ∀ ⦃D⦄, D ∈ insert B Prev →
            ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
              D ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
        intro D hD p
        rw [Finset.mem_insert] at hD
        rcases hD with rfl | hD
        · exact hB_noSingleton p
        · exact hPrev_noSingleton hD p
      have hCount_subset' : insert C Count ⊆ insert C (insert B Prev) := by
        intro D hD
        rw [Finset.mem_insert] at hD ⊢
        rcases hD with rfl | hD
        · exact Or.inl rfl
        · exact Or.inr (hCount_subset hD)
      have hCount_internal' : insert C Count ⊆ internalNonSingletonTreeBags P := by
        intro D hD
        rw [Finset.mem_insert] at hD
        rcases hD with rfl | hD
        · exact hCinternal
        · exact hCount_internal hD
      have hB_noSingleton' :
          ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            C ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
        intro p
        exact internalNonSingletonTreeBag_ne_singleton_tree hCinternal p
      have hantiNext :
          ∀ ⦃a⦄, a ∈ Rnext → ∀ ⦃b⦄, b ∈ Rnext → a ≠ b →
            ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a :=
        antichain_mono hRnext_subset hanti
      have hlevelNext :
          ∀ ⦃a⦄, a ∈ Rnext → ∀ ⦃b⦄, b ∈ Rnext → a ≠ b →
            a.1.val ≠ b.1.val := by
        intro a ha b hb hab
        exact hlevel_ne (hRnext_subset ha) (hRnext_subset hb) hab
      have hparentNext :
          ∀ ⦃q⦄, q ∈ Rnext →
            ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
              FullTreeNode.IsParent p q ∧
                ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P := by
        intro q hq
        exact hparentSingleton (hRnext_subset hq)
      have hCP : C ∈ P := (mem_internalNonSingletonTreeBags.mp hCinternal).1
      rcases ih
          (B := C) (Prev := insert B Prev) (Count := insert C Count)
          (R := Rnext)
          hCP hPrev_noSingleton' hB_noSingleton'
          hCount_subset' hCount_internal' hRnext_card
          hantiNext hlevelNext hparentNext (fun q => havailableNext q.2) with
        ⟨CountFinal, hinsert_subset, hcardFinal, hinternalFinal⟩
      refine ⟨CountFinal, ?_, ?_, hinternalFinal⟩
      · intro D hD
        exact hinsert_subset (by simp [hD])
      · have hinsert_card : (insert C Count).card = Count.card + 1 := by
          rw [Finset.card_insert_of_notMem hCnotCount]
        omega

/-- A large-bag fiber of side branches has the same number of distinct preleaf
descendants witnessed by that large bag. -/
theorem exists_distinct_preleaf_witnesses_of_largeBag {k : ℕ}
    {Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {A : Finset (BonnetDepresVertex k)}
    (hanti :
      ∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) :
    ∃ Vs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      Vs.card = (sideBranchesWitnessedByLargeBag Qs A).card ∧
        ∀ ⦃v⦄, v ∈ Vs →
          IsPreleaf v ∧
            ∃ q ∈ sideBranchesWitnessedByLargeBag Qs A,
              IsTreeAncestor q v ∧
                ∃ hlevel : IsInternal v,
                  manyChildrenThreshold k ≤
                    (A ∩ childVertexSet v hlevel).card := by
  classical
  let R := sideBranchesWitnessedByLargeBag Qs A
  let witness :
      ∀ q : {q // q ∈ R},
        ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          IsTreeAncestor q.1 v ∧ IsPreleaf v ∧
            ∃ hlevel : IsInternal v,
              manyChildrenThreshold k ≤
                (A ∩ childVertexSet v hlevel).card := by
    intro q
    have hq : q.1 ∈ sideBranchesWitnessedByLargeBag Qs A := by
      change q.1 ∈ R
      exact q.2
    rw [sideBranchesWitnessedByLargeBag, Finset.mem_filter] at hq
    exact hq.2
  let vOf :
      {q // q ∈ R} →
        FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => Classical.choose (witness q)
  have vOf_spec :
      ∀ q : {q // q ∈ R},
        IsTreeAncestor q.1 (vOf q) ∧ IsPreleaf (vOf q) ∧
          ∃ hlevel : IsInternal (vOf q),
            manyChildrenThreshold k ≤
              (A ∩ childVertexSet (vOf q) hlevel).card := by
    intro q
    exact Classical.choose_spec (witness q)
  have hRsubset : R ⊆ Qs := by
    simpa [R] using
      (sideBranchesWitnessedByLargeBag_subset (k := k) (Qs := Qs) (A := A))
  have hinj : Function.Injective vOf :=
    descendant_choice_injective_of_antichain
      (k := k) (Qs := Qs) (R := R) hRsubset hanti
      (vOf := vOf) (fun q => (vOf_spec q).1)
  let Vs := R.attach.image vOf
  refine ⟨Vs, ?_, ?_⟩
  · change (R.attach.image vOf).card = R.card
    rw [Finset.card_image_of_injective]
    · simp
    · exact hinj
  · intro v hv
    change v ∈ R.attach.image vOf at hv
    rw [Finset.mem_image] at hv
    rcases hv with ⟨q, _hq, rfl⟩
    refine ⟨(vOf_spec q).2.1, q.1, ?_, (vOf_spec q).1, ?_⟩
    · change q.1 ∈ R
      exact q.2
    · exact (vOf_spec q).2.2

/-- Pigeonholing Claim-18 side branches by the large bag supplied by their
descendant preleaf: one large bag receives many side branches. -/
theorem ContractionSequence.exists_largeChildBag_with_many_sideBranches
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hcard : Qs.card = bonnetDepresDepth k - 2)
    (hQmem :
      ∀ ⦃q⦄, q ∈ Qs →
        QProperty
          (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) :
    ∃ A ∈ largeChildBags
        (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
      manySideBranchesThreshold k ≤
        (sideBranchesWitnessedByLargeBag Qs A).card := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  let P := (S.state i).bags
  let L := largeChildBags P
  let witness :
      ∀ q : {q // q ∈ Qs},
        ∃ A ∈ L,
          ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            IsTreeAncestor q.1 v ∧ IsPreleaf v ∧
              ∃ hlevel : IsInternal v,
                manyChildrenThreshold k ≤
                  (A ∩ childVertexSet v hlevel).card := by
    intro q
    have hQq :
        QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q.1 :=
      hQmem q.2
    rcases ContractionSequence.exists_descendant_preleaf_largeChildBag_of_qProperty
        S hd hQq with
      ⟨v, hqv, hpre, hlevel, A, hA, hmany⟩
    exact ⟨A, by simpa [L, P, i] using hA, v, hqv, hpre, hlevel, hmany⟩
  let chosenA :
      {q // q ∈ Qs} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (witness q)
  have chosenA_mem :
      ∀ q : {q // q ∈ Qs}, chosenA q ∈ L := by
    intro q
    exact (Classical.choose_spec (witness q)).1
  have chosenA_spec :
      ∀ q : {q // q ∈ Qs},
        ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          IsTreeAncestor q.1 v ∧ IsPreleaf v ∧
            ∃ hlevel : IsInternal v,
              manyChildrenThreshold k ≤
                (chosenA q ∩ childVertexSet v hlevel).card := by
    intro q
    exact (Classical.choose_spec (witness q)).2
  have hi_le : i ≤ S.stepCount := by
    have hfirst :=
      ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
    have hstep :=
      ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  have hLcard : L.card ≤ 2 ^ (k + 2) := by
    have hroot : RootChildrenSingleton P := by
      simpa [P, i] using
        ContractionSequence.rootChildrenSingleton_firstRootChildQIndex S hd
    have hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d := by
      simpa [P, i] using
        Lax3Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
          S hi_le
    exact largeChildBags_card_le
      (k := k) (d := d) (P := P) hd
      (Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
      hroot hred
  have hLnonempty : L.Nonempty := by
    have hcard_pos : 0 < Qs.card := by
      rw [hcard]
      have hdepth := two_lt_depth k
      omega
    rcases Finset.card_pos.mp hcard_pos with ⟨q, hq⟩
    rcases witness ⟨q, hq⟩ with ⟨A, hA, _hv⟩
    exact ⟨A, hA⟩
  have hpigeon_mul :
      L.card * manySideBranchesThreshold k ≤ Qs.attach.card := by
    calc
      L.card * manySideBranchesThreshold k
          ≤ 2 ^ (k + 2) * manySideBranchesThreshold k :=
        Nat.mul_le_mul_right _ hLcard
      _ = Qs.card := by
        rw [hcard, depth_sub_two_eq_largeBagBound_mul_manySideBranchesThreshold]
      _ = Qs.attach.card := by
        simp
  rcases Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := Qs.attach) (t := L) (f := chosenA)
      (n := manySideBranchesThreshold k)
      (by intro q _hq; exact chosenA_mem q)
      hLnonempty hpigeon_mul with
    ⟨A, hA, hfiber⟩
  let Fattach := Qs.attach.filter fun q => chosenA q = A
  let F :=
    sideBranchesWitnessedByLargeBag Qs A
  have himage_card :
      (Fattach.image fun q => q.1).card = Fattach.card := by
    rw [Finset.card_image_of_injective]
    intro q r hqr
    exact Subtype.ext hqr
  have hsubset : (Fattach.image fun q => q.1) ⊆ F := by
    intro q hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, hqsub, rfl⟩
    change qsub.1 ∈ sideBranchesWitnessedByLargeBag Qs A
    rw [sideBranchesWitnessedByLargeBag, Finset.mem_filter]
    have hchosen : chosenA qsub = A := (Finset.mem_filter.mp hqsub).2
    rcases chosenA_spec qsub with ⟨v, hqv, hpre, hlevel, hmany⟩
    refine ⟨qsub.2, v, hqv, hpre, hlevel, ?_⟩
    simpa [hchosen] using hmany
  have hFcard : Fattach.card ≤ F.card := by
    rw [← himage_card]
    exact Finset.card_le_card hsubset
  refine ⟨A, by simpa [L, P, i] using hA, ?_⟩
  exact hfiber.trans (by simpa [Fattach, F] using hFcard)

/-- Claim 18 combined with the large-bag pigeonhole step. -/
theorem ContractionSequence.exists_antichain_sideBranchSet_largeChildBag_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      ∃ A ∈ largeChildBags
          (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
        Qs.card = bonnetDepresDepth k - 2 ∧
          (∀ ⦃q⦄, q ∈ Qs →
            QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
          (∀ ⦃q⦄, q ∈ Qs →
            ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
              FullTreeNode.IsParent p q ∧
                ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                  (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
          (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
            ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) ∧
          manySideBranchesThreshold k ≤
            (sideBranchesWitnessedByLargeBag Qs A).card := by
  rcases ContractionSequence.exists_antichain_sideBranchSet_firstRootChildQIndex
      S hd with
    ⟨Qs, hcard, hQmem, hparent, hanti⟩
  rcases ContractionSequence.exists_largeChildBag_with_many_sideBranches
      S hd hcard hQmem with
    ⟨A, hA, hmany⟩
  exact ⟨Qs, A, hA, hcard, hQmem, hparent, hanti, hmany⟩

/-- Ranked Claim 18 combined with the large-bag pigeonhole step. -/
theorem ContractionSequence.exists_ranked_antichain_sideBranchSet_largeChildBag_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      ∃ A ∈ largeChildBags
          (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
        Qs.card = bonnetDepresDepth k - 2 ∧
          (∀ ⦃q⦄, q ∈ Qs →
            QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
          (∀ ⦃q⦄, q ∈ Qs →
            ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
              FullTreeNode.IsParent p q ∧
                ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                  (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
          (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
            ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) ∧
          (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
            a.1.val ≠ b.1.val) ∧
          manySideBranchesThreshold k ≤
            (sideBranchesWitnessedByLargeBag Qs A).card := by
  rcases ContractionSequence.exists_ranked_antichain_sideBranchSet_firstRootChildQIndex
      S hd with
    ⟨Qs, hcard, hQmem, hparent, hanti, hlevel_ne⟩
  rcases ContractionSequence.exists_largeChildBag_with_many_sideBranches
      S hd hcard hQmem with
    ⟨A, hA, hmany⟩
  exact ⟨Qs, A, hA, hcard, hQmem, hparent, hanti, hlevel_ne, hmany⟩

/-- The base object for Claim 19: a large bag containing many children below
many distinct preleafs. -/
theorem ContractionSequence.exists_largeChildBag_with_many_distinct_preleafs
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ A ∈ largeChildBags
        (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
      ∃ Vs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
        manySideBranchesThreshold k ≤ Vs.card ∧
          ∀ ⦃v⦄, v ∈ Vs →
            IsPreleaf v ∧
              ∃ hlevel : IsInternal v,
                manyChildrenThreshold k ≤
                  (A ∩ childVertexSet v hlevel).card := by
  rcases ContractionSequence.exists_antichain_sideBranchSet_largeChildBag_firstRootChildQIndex
      S hd with
    ⟨Qs, A, hA, _hcard, _hQmem, _hparent, hanti, hmany⟩
  rcases exists_distinct_preleaf_witnesses_of_largeBag
      (k := k) (Qs := Qs) (A := A) hanti with
    ⟨Vs, hVsCard, hVs⟩
  refine ⟨A, hA, Vs, ?_, ?_⟩
  · rwa [hVsCard]
  · intro v hv
    rcases hVs hv with ⟨hpre, _q, _hq, _hqv, hlarge⟩
    exact ⟨hpre, hlarge⟩

/-- Claim 19 at the first root-child-`Q` state: the path-avoidance induction
produces enough distinct non-singleton parts containing internal tree nodes. -/
theorem ContractionSequence.many_internalNonSingletonTreeBags_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    manyInternalBagsThreshold k ≤
      (internalNonSingletonTreeBags
        (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags).card := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  let P := (S.state i).bags
  rcases ContractionSequence.exists_ranked_antichain_sideBranchSet_largeChildBag_firstRootChildQIndex
      S hd with
    ⟨Qs, A, hA_large, _hcardQs, _hQmem, hparentQs, hantiQs, hlevelQs, hmanyR⟩
  let R := sideBranchesWitnessedByLargeBag Qs A
  have hRsubset : R ⊆ Qs :=
    sideBranchesWitnessedByLargeBag_subset (k := k) (Qs := Qs) (A := A)
  have hi_le : i ≤ S.stepCount := by
    have hfirst :=
      ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
    have hstep :=
      ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  have hpart : IsBagPartition P :=
    Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i)
  have hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d := by
    simpa [P, i] using
      Lax3Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
        S hi_le
  have hA : A ∈ P := (mem_largeChildBags.mp (by simpa [P, i] using hA_large)).1
  have hB_noSingleton :
      ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        A ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
    intro p
    exact largeChildBag_ne_singleton_tree (by simpa [P, i] using hA_large) p
  have hantiR :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a :=
    antichain_mono hRsubset hantiQs
  have hlevelR :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val := by
    intro a ha b hb hab
    exact hlevelQs (hRsubset ha) (hRsubset hb) hab
  have hparentR :
      ∀ ⦃q⦄, q ∈ R →
        ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          FullTreeNode.IsParent p q ∧
            ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P := by
    intro q hq
    simpa [P, i] using hparentQs (hRsubset hq)
  have havailable0 :
      ∀ q : {q // q ∈ R}, (availableDescendantsInBag ∅ A q.1).Nonempty := by
    intro q
    have hqR : q.1 ∈ sideBranchesWitnessedByLargeBag Qs A := q.2
    rw [sideBranchesWitnessedByLargeBag, Finset.mem_filter] at hqR
    rcases hqR with ⟨_hqQs, v, hqv, _hpre, hlevel, hmany⟩
    rcases exists_child_mem_bag_of_manyChildren hmany with ⟨c, hc, hcA⟩
    refine availableDescendantsInBag_nonempty_of_mem
      (F := ∅) (B := A) (q := q.1) (z := c)
      (isTreeAncestor_trans hqv (isAncestor_of_mem_childSet hc)) hcA ?_
    intro D hD x hx
    simp at hD
  have hcardStart :
      (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) < R.card := by
    have ht_one : 1 < manyChildrenThreshold k :=
      lt_of_lt_of_le (by omega : 1 < 2) (two_le_manyChildrenThreshold k)
    have hpow_pos :
        0 < (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) :=
      pow_pos (manyChildrenThreshold_pos k) _
    have hpow_lt :
        (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) <
          (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k + 1) := by
      rw [Nat.pow_succ]
      calc
        (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k)
            = (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) * 1 := by omega
        _ < (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) *
              manyChildrenThreshold k :=
            Nat.mul_lt_mul_of_pos_left ht_one hpow_pos
    have hpow_le_R :
        (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k + 1) ≤ R.card := by
      rw [← manySideBranchesThreshold_eq_manyChildrenThreshold_pow]
      simpa [R] using hmanyR
    exact hpow_lt.trans_le hpow_le_R
  rcases exists_internalNonSingletonTreeBags_of_available_iteration
      (k := k) (d := d) (steps := manyInternalBagsThreshold k)
      (P := P) (R := R) (B := A) (Prev := ∅) (Count := ∅)
      hd hpart hA hred
      (by intro D hD p; simp at hD)
      hB_noSingleton
      (by intro D hD; simp at hD)
      (by intro D hD; simp at hD)
      hcardStart hantiR hlevelR hparentR havailable0 with
    ⟨CountFinal, _hEmptySubset, hCountCard, hCountInternal⟩
  have hcard_le :
      CountFinal.card ≤ (internalNonSingletonTreeBags P).card :=
    Finset.card_le_card hCountInternal
  have htarget : CountFinal.card = manyInternalBagsThreshold k := by
    simpa using hCountCard
  change manyInternalBagsThreshold k ≤ (internalNonSingletonTreeBags P).card
  omega

/-- Final contradiction at the first root-child-`Q` state, once Claim 19 has
produced enough non-singleton internal-tree parts. -/
theorem ContractionSequence.false_of_many_internalNonSingletonTreeBags_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    (hmany :
      manyInternalBagsThreshold k ≤
        (internalNonSingletonTreeBags
          (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags).card) :
    False := by
  let i := ContractionSequence.firstRootChildQIndex S hd
  have hi_le : i ≤ S.stepCount := by
    have hfirst :=
      ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
    have hstep :=
      ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  have hroot : RootChildrenSingleton (S.state i).bags := by
    simpa [i] using
      ContractionSequence.rootChildrenSingleton_firstRootChildQIndex S hd
  have hred :
      PartitionRedDegreeAtMost (bonnetDepresGraph k) (S.state i).bags d :=
    Lax3Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
      S hi_le
  exact false_of_many_internalNonSingletonTreeBags
    (k := k) (d := d) (P := (S.state i).bags)
    hd (Lax3Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot hred (by simpa [i] using hmany)

/-- Combiner for the remaining Claim-19 induction: if every `2^k`-bounded
sequence has the final number of non-singleton internal-tree parts at the first
root-child-`Q` state, then no such sequence exists. -/
theorem not_hasTwinWidthAtMost_of_many_internalNonSingletonTreeBags
    {k d : ℕ}
    (hd : d ≤ 2 ^ k)
    (hClaim19 :
      ∀ S : ContractionSequence (bonnetDepresGraph k) d,
        manyInternalBagsThreshold k ≤
          (internalNonSingletonTreeBags
            (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags).card) :
    ¬ HasTwinWidthAtMost (bonnetDepresGraph k) d := by
  rintro ⟨S⟩
  exact
    ContractionSequence.false_of_many_internalNonSingletonTreeBags_firstRootChildQIndex
      S hd (hClaim19 S)

/-- The Bonnet--Déprés graph has no contraction sequence of red degree at most
`2^k`. -/
theorem bonnetDepres_not_hasTwinWidthAtMost_two_pow (k : ℕ) :
    ¬ HasTwinWidthAtMost (bonnetDepresGraph k) (2 ^ k) := by
  exact not_hasTwinWidthAtMost_of_many_internalNonSingletonTreeBags
    (k := k) (d := 2 ^ k) le_rfl
    (fun S => ContractionSequence.many_internalNonSingletonTreeBags_firstRootChildQIndex
      S le_rfl)

/-- The concrete Bonnet--Déprés lower bound on twin-width. -/
theorem bonnetDepres_two_pow_lt_twinWidth (k : ℕ) :
    2 ^ k < twinWidth (bonnetDepresGraph k) :=
  Lax3Proofs.TwinWidth.SimpleGraph.lt_twinWidth_of_not_hasTwinWidthAtMost
    (bonnetDepres_not_hasTwinWidthAtMost_two_pow k)

/-- Concrete separation: for every `k` there is a finite graph of treewidth at
most `2*k+4` and twin-width greater than `2^k`. -/
theorem exists_graph_treewidth_linear_twin_width_exponential (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : _root_.SimpleGraph V),
      treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth G := by
  exact ⟨BonnetDepresVertex k, inferInstance, inferInstance, bonnetDepresGraph k,
    bonnetDepres_treewidth_le k, bonnetDepres_two_pow_lt_twinWidth k⟩

/-- Before the first contraction involving a root child, some preleaf already
satisfies property `P`. -/
theorem ContractionSequence.exists_preleaf_hasManyChildrenInPart_before_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      ∃ hlevel : IsInternal v,
        IsPreleaf v ∧
          HasManyChildrenInPart
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags
            v hlevel (manyChildrenThreshold k) := by
  rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with ⟨f, hQ⟩
  exact exists_preleaf_hasManyChildrenInPart_of_qProperty hQ

end BonnetDepres

end SimpleGraph
end Lax3Proofs.TwinWidth
