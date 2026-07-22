import Lax1Proofs.Source.TwinWidth.Graph.BonnetDepres
import Lax1Proofs.Source.TwinWidth.Graph.Partition
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Combinatorics.Pigeonhole

/-!
# Lower-bound infrastructure for the Bonnet--Déprés graphs

This file collects the concrete, reusable facts about the Bonnet--Déprés
construction that are used in the twin-width lower-bound proof.  The statements
are deliberately phrased in the semantic partition language from
`TwinWidth.Graph.Partition`: red adjacency means non-homogeneity of two bags in
the original graph.
-/

namespace Lax1Proofs.TwinWidth
namespace SimpleGraph

namespace BonnetDepres

/-- The explicit Bonnet--Déprés tree depth is positive. -/
theorem depth_pos (k : ℕ) : 0 < bonnetDepresDepth k := by
  simp [bonnetDepresDepth]

/-- The explicit depth is greater than `2`, so grandchildren have children. -/
theorem two_lt_depth (k : ℕ) : 2 < bonnetDepresDepth k := by
  simp [bonnetDepresDepth]

/-- The root is an internal tree node in the Bonnet--Déprés construction. -/
theorem root_level_lt_depth (k : ℕ) :
    (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k)).1.val <
      bonnetDepresDepth k := by
  simp [FullTreeNode.root, depth_pos k]

/-- Internal nodes of the Bonnet--Déprés tree are precisely nodes with children. -/
def IsInternal {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : Prop :=
  u.1.val < bonnetDepresDepth k

/-- A preleaf is an internal node whose children are leaves. -/
def IsPreleaf {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : Prop :=
  u.1.val + 1 = bonnetDepresDepth k

/-- A non-preleaf internal node is an internal node whose children are internal. -/
def IsNonPreleafInternal {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : Prop :=
  u.1.val + 1 < bonnetDepresDepth k

theorem isInternal_iff {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)} :
    IsInternal u ↔ u.1.val < bonnetDepresDepth k := Iff.rfl

theorem isNonPreleafInternal.isInternal {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : IsNonPreleafInternal u) :
    IsInternal u := by
  unfold IsNonPreleafInternal IsInternal at *
  omega

theorem child_isInternal_of_isNonPreleafInternal {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : IsNonPreleafInternal u)
    (label : Fin (bonnetDepresBranch k)) :
    IsInternal (FullTreeNode.child u
      (isNonPreleafInternal.isInternal h) label) := by
  unfold IsNonPreleafInternal at h
  unfold IsInternal
  simp [FullTreeNode.child]
  omega

/-- A canonical apex vertex distinct from `x`. -/
def otherApex (k : ℕ) (x : Fin (bonnetDepresApexCount k)) :
    Fin (bonnetDepresApexCount k) :=
  if hx : x.val = 0 then
    ⟨1, by
      unfold bonnetDepresApexCount
      omega⟩
  else
    ⟨0, by
      unfold bonnetDepresApexCount
      omega⟩

theorem otherApex_ne (k : ℕ) (x : Fin (bonnetDepresApexCount k)) :
    otherApex k x ≠ x := by
  unfold otherApex
  by_cases hx : x.val = 0
  · intro h
    have hval := congrArg Fin.val h
    simp [hx] at hval
  · intro h
    have hval := congrArg Fin.val h
    simp [hx] at hval
    exact hx hval.symm

/-- The bit vector coding the singleton apex neighborhood `{y}`. -/
def singletonApexNeighborhood {k : ℕ}
    (y : Fin (bonnetDepresApexCount k)) :
    Fin (bonnetDepresApexCount k) → Bool :=
  fun z => decide (z = y)

@[simp] theorem singletonApexNeighborhood_self {k : ℕ}
    (y : Fin (bonnetDepresApexCount k)) :
    singletonApexNeighborhood y y = true := by
  simp [singletonApexNeighborhood]

@[simp] theorem singletonApexNeighborhood_of_ne {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    singletonApexNeighborhood y x = false := by
  simp [singletonApexNeighborhood, hxy]

/-- The child label whose bits realize a prescribed neighborhood in the apex
set.  Bits are read little-endian, matching `Nat.testBit`. -/
def labelOfNeighborhood {k : ℕ}
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    Fin (bonnetDepresBranch k) := by
  simpa [bonnetDepresBranch] using
    (⟨Nat.ofBits f, Nat.ofBits_lt_two_pow f⟩ : Fin (2 ^ bonnetDepresApexCount k))

@[simp] theorem labelOfNeighborhood_testBit {k : ℕ}
    (f : Fin (bonnetDepresApexCount k) → Bool)
    (x : Fin (bonnetDepresApexCount k)) :
    (labelOfNeighborhood f).val.testBit x.val = f x := by
  unfold labelOfNeighborhood
  simp [bonnetDepresBranch, Nat.testBit_ofBits_lt f x.val x.isLt]

/-- Distinct prescribed apex neighborhoods give distinct child labels. -/
theorem labelOfNeighborhood_injective {k : ℕ} :
    Function.Injective
      (labelOfNeighborhood (k := k) :
        (Fin (bonnetDepresApexCount k) → Bool) →
          Fin (bonnetDepresBranch k)) := by
  intro f g h
  funext x
  have hbit := congrArg (fun label : Fin (bonnetDepresBranch k) =>
    label.val.testBit x.val) h
  simpa using hbit

/-- Two distinct labels below `2^n` differ on one of their first `n` bits. -/
theorem exists_bit_ne_of_fin_pow_ne {n : ℕ}
    {a b : Fin (2 ^ n)} (hab : a ≠ b) :
    ∃ x : Fin n, a.val.testBit x.val ≠ b.val.testBit x.val := by
  by_contra hnone
  have hbits : ∀ i : ℕ, a.val.testBit i = b.val.testBit i := by
    intro i
    by_cases hi : i < n
    · by_contra hbit
      exact hnone ⟨⟨i, hi⟩, hbit⟩
    · have hni : n ≤ i := le_of_not_gt hi
      have hpow : 2 ^ n ≤ 2 ^ i := by
        apply Nat.pow_le_pow_right
        · omega
        · exact hni
      have ha : a.val.testBit i = false :=
        Nat.testBit_eq_false_of_lt (a.isLt.trans_le hpow)
      have hb : b.val.testBit i = false :=
        Nat.testBit_eq_false_of_lt (b.isLt.trans_le hpow)
      rw [ha, hb]
  apply hab
  exact Fin.ext (Nat.eq_of_testBit_eq hbits)

/-- For a fixed internal node, child labels inject into actual children. -/
theorem child_injective_label {branch depth : ℕ}
    (parent : FullTreeNode branch depth) (hlevel : parent.1.val < depth) :
    Function.Injective (FullTreeNode.child parent hlevel) := by
  intro a b h
  have hposa : 0 < (FullTreeNode.child parent hlevel a).1.val := by
    simp [FullTreeNode.child]
  have hposb : 0 < (FullTreeNode.child parent hlevel b).1.val := by
    simp [FullTreeNode.child]
  have hposb' : 0 < (FullTreeNode.child parent hlevel a).1.val := by
    simpa [h] using hposb
  have hb :
      FullTreeNode.lastLabel (FullTreeNode.child parent hlevel a) hposb' = b := by
    simpa [h] using FullTreeNode.lastLabel_child parent hlevel b hposb
  calc
    a = FullTreeNode.lastLabel (FullTreeNode.child parent hlevel a) hposa :=
      (FullTreeNode.lastLabel_child parent hlevel a hposa).symm
    _ = FullTreeNode.lastLabel (FullTreeNode.child parent hlevel a) hposb' := by
      congr
    _ = b := hb

/-- Ancestor relation in the concrete full tree: `u` is an ancestor of `v` when
the path of `u` is a prefix of the path of `v`. -/
def IsTreeAncestor {branch depth : ℕ}
    (u v : FullTreeNode branch depth) : Prop :=
  ∃ hle : u.1.val ≤ v.1.val,
    ∀ i : Fin u.1.val, v.2 ⟨i.val, lt_of_lt_of_le i.isLt hle⟩ = u.2 i

theorem isTreeAncestor_refl {branch depth : ℕ}
    (u : FullTreeNode branch depth) :
    IsTreeAncestor u u := by
  refine ⟨le_rfl, ?_⟩
  intro i
  rfl

theorem isTreeAncestor_child {branch depth : ℕ}
    (u : FullTreeNode branch depth) (hlevel : u.1.val < depth)
    (label : Fin branch) :
    IsTreeAncestor u (FullTreeNode.child u hlevel label) := by
  refine ⟨by simp [FullTreeNode.child], ?_⟩
  intro i
  simp [FullTreeNode.child, i.isLt]

/-- A parent is an ancestor of its child. -/
theorem isTreeAncestor_of_isParent {branch depth : ℕ}
    {parent child : FullTreeNode branch depth}
    (h : FullTreeNode.IsParent parent child) :
    IsTreeAncestor parent child := by
  rcases h with ⟨hlevel, hpath⟩
  refine ⟨by omega, ?_⟩
  intro i
  exact hpath i

/-- The parent endpoint of a full-tree parent relation is internal. -/
theorem parent_level_lt_depth_of_isParent {branch depth : ℕ}
    {parent child : FullTreeNode branch depth}
    (h : FullTreeNode.IsParent parent child) :
    parent.1.val < depth := by
  rcases h with ⟨hlevel, _hpath⟩
  exact Nat.lt_of_succ_lt_succ (by simpa [hlevel] using child.1.isLt)

theorem isTreeAncestor_trans {branch depth : ℕ}
    {u v w : FullTreeNode branch depth}
    (huv : IsTreeAncestor u v) (hvw : IsTreeAncestor v w) :
    IsTreeAncestor u w := by
  rcases huv with ⟨huv_le, huv_path⟩
  rcases hvw with ⟨hvw_le, hvw_path⟩
  refine ⟨huv_le.trans hvw_le, ?_⟩
  intro i
  exact (hvw_path ⟨i.val, lt_of_lt_of_le i.isLt huv_le⟩).trans (huv_path i)

/-- Two ancestors of a common full-tree node are comparable. -/
theorem isTreeAncestor_or_isTreeAncestor_of_common_descendant {branch depth : ℕ}
    {u v w : FullTreeNode branch depth}
    (huw : IsTreeAncestor u w) (hvw : IsTreeAncestor v w) :
    IsTreeAncestor u v ∨ IsTreeAncestor v u := by
  rcases huw with ⟨huw_le, huw_path⟩
  rcases hvw with ⟨hvw_le, hvw_path⟩
  by_cases huv_level : u.1.val ≤ v.1.val
  · left
    refine ⟨huv_level, ?_⟩
    intro i
    have hvw_i :=
      hvw_path ⟨i.val, lt_of_lt_of_le i.isLt huv_level⟩
    have huw_i := huw_path i
    exact hvw_i.symm.trans (by simpa using huw_i)
  · right
    have hvu_level : v.1.val ≤ u.1.val := le_of_not_ge huv_level
    refine ⟨hvu_level, ?_⟩
    intro i
    have huw_i :=
      huw_path ⟨i.val, lt_of_lt_of_le i.isLt hvu_level⟩
    have hvw_i := hvw_path i
    exact huw_i.symm.trans (by simpa using hvw_i)

/-- Two ancestors of the same node at the same level are equal. -/
theorem eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq {branch depth : ℕ}
    {u v w : FullTreeNode branch depth}
    (huw : IsTreeAncestor u w) (hvw : IsTreeAncestor v w)
    (hlevel : u.1.val = v.1.val) :
    u = v := by
  rcases huw with ⟨huw_le, huw_path⟩
  rcases hvw with ⟨hvw_le, hvw_path⟩
  cases u with
  | mk ulevel upath =>
  cases v with
  | mk vlevel vpath =>
    simp only at hlevel huw_path hvw_path ⊢
    have hlevel_fin : ulevel = vlevel := Fin.ext hlevel
    subst vlevel
    congr
    funext i
    exact (huw_path i).symm.trans (hvw_path i)

/-- If `z` is a strict descendant of `q`, then the parent of `z` is still a
descendant of `q`. -/
theorem isTreeAncestor_parent_of_strict_descendant {branch depth : ℕ}
    {q p z : FullTreeNode branch depth}
    (hqz : IsTreeAncestor q z)
    (hpz : FullTreeNode.IsParent p z)
    (hqzLevel : q.1.val < z.1.val) :
    IsTreeAncestor q p := by
  rcases hqz with ⟨hqz_le, hqz_path⟩
  rcases hpz with ⟨hz_level, hpz_path⟩
  have hq_le_p : q.1.val ≤ p.1.val := by omega
  refine ⟨hq_le_p, ?_⟩
  intro i
  have hp := hpz_path ⟨i.val, lt_of_lt_of_le i.isLt hq_le_p⟩
  have hq := hqz_path i
  exact hp.symm.trans hq

/-- A parent on one branch of an ancestor-antichain is not adjacent to a
descendant on another branch. -/
theorem not_tree_adj_parent_descendant_of_antichain {branch depth : ℕ}
    {a b za zb p : FullTreeNode branch depth}
    (hanti : ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (haza : IsTreeAncestor a za)
    (hbzb : IsTreeAncestor b zb)
    (hpza : FullTreeNode.IsParent p za)
    (ha_strict : a.1.val < za.1.val) :
    ¬ (FullTreeNode.graph branch depth).Adj p zb := by
  intro hadj
  have hap : IsTreeAncestor a p :=
    isTreeAncestor_parent_of_strict_descendant haza hpza ha_strict
  rcases hadj with hpzb | hzbp
  · have hazb : IsTreeAncestor a zb :=
      isTreeAncestor_trans hap (isTreeAncestor_of_isParent hpzb)
    rcases isTreeAncestor_or_isTreeAncestor_of_common_descendant hazb hbzb with
      hab | hba
    · exact hanti.1 hab
    · exact hanti.2 hba
  · have hbp : IsTreeAncestor b p :=
      isTreeAncestor_trans hbzb (isTreeAncestor_of_isParent hzbp)
    rcases isTreeAncestor_or_isTreeAncestor_of_common_descendant hap hbp with
      hab | hba
    · exact hanti.1 hab
    · exact hanti.2 hba

/-- Ranked variant of `not_tree_adj_parent_descendant_of_antichain`: when the
selected descendant on the first branch is the branch node itself, the distinct
level invariant rules out the only sibling-parent obstruction. -/
theorem not_tree_adj_parent_descendant_of_ranked_antichain {branch depth : ℕ}
    {a b za zb p : FullTreeNode branch depth}
    (hanti : ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne : a.1.val ≠ b.1.val)
    (haza : IsTreeAncestor a za)
    (hbzb : IsTreeAncestor b zb)
    (hpza : FullTreeNode.IsParent p za) :
    ¬ (FullTreeNode.graph branch depth).Adj p zb := by
  by_cases ha_strict : a.1.val < za.1.val
  · exact not_tree_adj_parent_descendant_of_antichain
      hanti haza hbzb hpza ha_strict
  · intro hadj
    have hza_level : za.1.val = a.1.val := by
      rcases haza with ⟨hlevel, _⟩
      omega
    have hza_eq : a = za :=
      eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
        haza (isTreeAncestor_refl za) hza_level.symm
    subst za
    rcases hadj with hpzb | hzbp
    · have hp_level := FullTreeNode.isParent_level hpza
      have hzb_level := FullTreeNode.isParent_level hpzb
      by_cases hb_level : b.1.val = zb.1.val
      · have hb_eq_zb : b = zb :=
          eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
            hbzb (isTreeAncestor_refl zb) hb_level
        subst zb
        exact hlevel_ne (by omega)
      · have hb_lt_zb : b.1.val < zb.1.val := by
          rcases hbzb with ⟨hb_le, _⟩
          omega
        have hbp : IsTreeAncestor b p :=
          isTreeAncestor_parent_of_strict_descendant hbzb hpzb hb_lt_zb
        have hba : IsTreeAncestor b a :=
          isTreeAncestor_trans hbp (isTreeAncestor_of_isParent hpza)
        exact hanti.2 hba
    · have hbp : IsTreeAncestor b p :=
        isTreeAncestor_trans hbzb (isTreeAncestor_of_isParent hzbp)
      have hba : IsTreeAncestor b a :=
        isTreeAncestor_trans hbp (isTreeAncestor_of_isParent hpza)
      exact hanti.2 hba

/-- The root child realizing a prescribed apex neighborhood. -/
def rootChildWithNeighborhood (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  FullTreeNode.child
    (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
    (root_level_lt_depth k) (labelOfNeighborhood f)

@[simp] theorem rootChildWithNeighborhood_apexAdj (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool)
    (x : Fin (bonnetDepresApexCount k)) :
    bonnetDepresApexAdj x (rootChildWithNeighborhood k f) ↔
      f x = true := by
  rw [rootChildWithNeighborhood,
    bonnetDepresApexAdj_child x
      (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
      (root_level_lt_depth k) (labelOfNeighborhood f)]
  simp

/-- The tree root is adjacent to every root child. -/
theorem root_adj_rootChildWithNeighborhood (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    (bonnetDepresGraph k).Adj
      (Sum.inr (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k)) :
        BonnetDepresVertex k)
      (Sum.inr (rootChildWithNeighborhood k f)) := by
  simpa [bonnetDepresGraph, rootChildWithNeighborhood] using
    (Or.inl
      (FullTreeNode.isParent_child
        (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
        (root_level_lt_depth k) (labelOfNeighborhood f)))

@[simp] theorem rootChildWithNeighborhood_level (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    (rootChildWithNeighborhood k f).1.val = 1 := by
  simp [rootChildWithNeighborhood, FullTreeNode.child, FullTreeNode.root]

/-- Every root child is internal in the Bonnet--Déprés tree. -/
theorem rootChildWithNeighborhood_isInternal (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    IsInternal (rootChildWithNeighborhood k f) := by
  unfold IsInternal
  rw [rootChildWithNeighborhood_level]
  have hdepth := two_lt_depth k
  omega

/-- Every root child is a non-preleaf internal node in the chosen depth. -/
theorem rootChildWithNeighborhood_isNonPreleafInternal (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    IsNonPreleafInternal (rootChildWithNeighborhood k f) := by
  unfold IsNonPreleafInternal
  rw [rootChildWithNeighborhood_level]
  exact two_lt_depth k

/-- A tree vertex whose level is neither root level nor grandchild level is not
adjacent to any root child. -/
theorem not_adj_rootChildWithNeighborhood_of_level_ne_zero_ne_two (k : ℕ)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hzero : u.1.val ≠ 0) (htwo : u.1.val ≠ 2)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    ¬ (bonnetDepresGraph k).Adj
      (Sum.inr u : BonnetDepresVertex k)
      (Sum.inr (rootChildWithNeighborhood k f)) := by
  intro hadj
  have htree :
      (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj
        u (rootChildWithNeighborhood k f) := by
    simpa [bonnetDepresGraph] using hadj
  have hlevels :=
    FullTreeNode.adj_level_eq_succ_or_succ_eq htree
  rw [rootChildWithNeighborhood_level] at hlevels
  rcases hlevels with h | h
  · exact hzero (by omega)
  · exact htwo (by omega)

/-- The map from apex-neighborhood bit vectors to root children is injective. -/
theorem rootChildWithNeighborhood_injective (k : ℕ) :
    Function.Injective (rootChildWithNeighborhood k) := by
  intro f g h
  exact labelOfNeighborhood_injective
    ((child_injective_label
      (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
      (root_level_lt_depth k)) h)

/-- Every level-one tree node is one of the root children selected by a bit
vector. -/
theorem exists_rootChildWithNeighborhood_eq_of_level_one (k : ℕ)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val = 1) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      rootChildWithNeighborhood k f = u := by
  let hpos : 0 < u.1.val := by omega
  let f : Fin (bonnetDepresApexCount k) → Bool :=
    fun x => (FullTreeNode.lastLabel u hpos).val.testBit x.val
  refine ⟨f, ?_⟩
  have hlabel :
      labelOfNeighborhood f = FullTreeNode.lastLabel u hpos := by
    apply Fin.ext
    simp [labelOfNeighborhood, bonnetDepresBranch, f, Nat.ofBits_testBit,
      Nat.mod_eq_of_lt]
  cases u with
  | mk level path =>
    cases level with
    | mk n hn =>
      simp only at hlevel
      subst n
      simp [rootChildWithNeighborhood, FullTreeNode.child, FullTreeNode.root]
      funext i
      have hi : i = (0 : Fin 1) := Fin.ext (by omega)
      subst i
      simpa [FullTreeNode.lastLabel, f] using hlabel

/-- Bit vectors that contain `x` and omit `y`; these are exactly the root
children separating the two apex vertices `x` and `y`. -/
abbrev SeparatingApexBits {k : ℕ}
    (x y : Fin (bonnetDepresApexCount k)) : Type :=
  {f : Fin (bonnetDepresApexCount k) → Bool // f x = true ∧ f y = false}

/-- The free coordinates of a bit vector separating two distinct apex
vertices. -/
abbrev RemainingApexVertex {k : ℕ}
    (x y : Fin (bonnetDepresApexCount k)) : Type :=
  {z : Fin (bonnetDepresApexCount k) // z ≠ x ∧ z ≠ y}

/-- Bit vectors whose value at a fixed apex vertex is prescribed. -/
abbrev ApexBitFiber {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) : Type :=
  {f : Fin (bonnetDepresApexCount k) → Bool // f x = b}

/-- Apex coordinates other than a fixed one. -/
abbrev OtherApexVertex {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) : Type :=
  {z : Fin (bonnetDepresApexCount k) // z ≠ x}

/-- A fixed bit at `x` leaves arbitrary choices on all other apex vertices. -/
noncomputable def apexBitFiberEquiv {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) :
    ApexBitFiber x b ≃ (OtherApexVertex x → Bool) where
  toFun f z := f.1 z.1
  invFun g :=
    ⟨fun z => if hx : z = x then b else g ⟨z, hx⟩, by simp⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext z
    by_cases hx : z = x
    · subst z
      simp [f.2]
    · simp [hx]
  right_inv := by
    intro g
    funext z
    rcases z with ⟨z, hz⟩
    simp [hz]

/-- The number of apex coordinates other than one fixed coordinate. -/
theorem card_otherApexVertex {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) :
    Fintype.card (OtherApexVertex x) = bonnetDepresApexCount k - 1 := by
  classical
  have hcompl :
      Fintype.card {z : Fin (bonnetDepresApexCount k) // z ≠ x} =
        Fintype.card (Fin (bonnetDepresApexCount k)) -
          Fintype.card {z : Fin (bonnetDepresApexCount k) // z = x} :=
    Fintype.card_subtype_compl
      (fun z : Fin (bonnetDepresApexCount k) => z = x)
  rw [hcompl, Fintype.card_subtype_eq, Fintype.card_fin]

/-- Exactly half of the root-child labels realize a prescribed bit at a fixed
apex vertex. -/
theorem card_apexBitFiber {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) :
    Fintype.card (ApexBitFiber x b) =
      2 ^ (bonnetDepresApexCount k - 1) := by
  classical
  rw [Fintype.card_congr (apexBitFiberEquiv x b)]
  rw [Fintype.card_fun, Fintype.card_bool, card_otherApexVertex x]

/-- Separating bit vectors are equivalent to arbitrary choices on the remaining
apex vertices. -/
noncomputable def separatingApexBitsEquiv {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    SeparatingApexBits x y ≃ (RemainingApexVertex x y → Bool) where
  toFun f z := f.1 z.1
  invFun g :=
    ⟨fun z =>
      if hx : z = x then
        true
      else if hy : z = y then
        false
      else
        g ⟨z, hx, hy⟩,
      by simp,
      by simp [hxy.symm]⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext z
    by_cases hx : z = x
    · subst z
      simp [f.2.1]
    · by_cases hy : z = y
      · subst z
        simp [hx, f.2.2]
      · simp [hx, hy]
  right_inv := by
    intro g
    funext z
    rcases z with ⟨z, hz⟩
    simp [hz.1, hz.2]

/-- The number of remaining apex vertices after deleting two distinct ones. -/
theorem card_remainingApexVertex {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    Fintype.card (RemainingApexVertex x y) =
      bonnetDepresApexCount k - 2 := by
  classical
  calc
    Fintype.card {z : Fin (bonnetDepresApexCount k) // z ≠ x ∧ z ≠ y} =
        Fintype.card {z : Fin (bonnetDepresApexCount k) // ¬ (z = x ∨ z = y)} :=
      Fintype.card_congr <|
        Equiv.subtypeEquivRight fun z => by
          constructor
          · rintro ⟨hzx, hzy⟩ (rfl | rfl)
            · exact hzx rfl
            · exact hzy rfl
          · intro h
            exact ⟨fun hzx => h (Or.inl hzx), fun hzy => h (Or.inr hzy)⟩
    _ = bonnetDepresApexCount k - 2 := by
      have hcompl :
          Fintype.card
              {z : Fin (bonnetDepresApexCount k) // ¬ (z = x ∨ z = y)} =
            Fintype.card (Fin (bonnetDepresApexCount k)) -
              Fintype.card
                {z : Fin (bonnetDepresApexCount k) // z = x ∨ z = y} :=
        Fintype.card_subtype_compl
          (fun z : Fin (bonnetDepresApexCount k) => z = x ∨ z = y)
      rw [hcompl, Fintype.card_subtype_eq_or_eq_of_ne hxy, Fintype.card_fin]

/-- There are `2^(|X|-2)` root children separating two distinct apex vertices. -/
theorem card_separatingApexBits {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    Fintype.card (SeparatingApexBits x y) =
      2 ^ (bonnetDepresApexCount k - 2) := by
  classical
  rw [Fintype.card_congr (separatingApexBitsEquiv hxy)]
  rw [Fintype.card_fun, Fintype.card_bool, card_remainingApexVertex hxy]

/-- Root-child vertices whose apex neighborhoods contain `x` and omit `y`. -/
def separatingRootChildren {k : ℕ}
    (x y : Fin (bonnetDepresApexCount k)) :
    Finset (BonnetDepresVertex k) :=
  Finset.univ.image fun f : SeparatingApexBits x y =>
    (Sum.inr (rootChildWithNeighborhood k f.1) : BonnetDepresVertex k)

/-- The root children separating two distinct apex vertices are all distinct,
so their count is exactly `2^(|X|-2)`. -/
theorem card_separatingRootChildren {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    (separatingRootChildren x y).card =
      2 ^ (bonnetDepresApexCount k - 2) := by
  classical
  rw [separatingRootChildren, Finset.card_image_of_injective]
  · simp [card_separatingApexBits hxy]
  · intro f g h
    apply Subtype.ext
    exact rootChildWithNeighborhood_injective k (Sum.inr.inj h)

/-- Singleton bags of root children whose apex neighborhoods contain `x` and
omit `y`. -/
def separatingRootChildBags {k : ℕ}
    (x y : Fin (bonnetDepresApexCount k)) :
    Finset (Finset (BonnetDepresVertex k)) :=
  Finset.univ.image fun f : SeparatingApexBits x y =>
    ({Sum.inr (rootChildWithNeighborhood k f.1)} :
      Finset (BonnetDepresVertex k))

/-- A partition has kept every child of the root as a singleton bag.  This is
the condition used for the initial segment of the Bonnet--Déprés lower-bound
argument, before the first contraction involving a root child. -/
def RootChildrenSingleton {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k))) : Prop :=
  ∀ f : Fin (bonnetDepresApexCount k) → Bool,
    ({Sum.inr (rootChildWithNeighborhood k f)} :
      Finset (BonnetDepresVertex k)) ∈ P

/-- The singleton bag containing a root child with a prescribed apex
neighborhood. -/
def rootChildBag (k : ℕ) (f : Fin (bonnetDepresApexCount k) → Bool) :
    Finset (BonnetDepresVertex k) :=
  {Sum.inr (rootChildWithNeighborhood k f)}

theorem rootChildrenSingleton_iff {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))} :
    RootChildrenSingleton P ↔ ∀ f, rootChildBag k f ∈ P := by
  simp [RootChildrenSingleton, rootChildBag]

/-- Merging two bags that are not root-child singleton bags preserves the
`RootChildrenSingleton` invariant. -/
theorem rootChildrenSingleton_merge_of_not_rootChildBag {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A B : Finset (BonnetDepresVertex k)}
    (hroot : RootChildrenSingleton P)
    (hAnot : ∀ f : Fin (bonnetDepresApexCount k) → Bool, A ≠ rootChildBag k f)
    (hBnot : ∀ f : Fin (bonnetDepresApexCount k) → Bool, B ≠ rootChildBag k f) :
    RootChildrenSingleton
      (insert (A ∪ B) ((P.erase A).erase B)) := by
  intro f
  change rootChildBag k f ∈ insert (A ∪ B) ((P.erase A).erase B)
  rw [mem_merge_family_iff]
  right
  exact ⟨(rootChildrenSingleton_iff.mp hroot) f, (hAnot f).symm, (hBnot f).symm⟩

/-- The family of all singleton bags of root children. -/
def rootChildBags (k : ℕ) : Finset (Finset (BonnetDepresVertex k)) :=
  Finset.univ.image (rootChildBag k)

/-- Distinct apex-neighborhoods give distinct root-child singleton bags. -/
theorem rootChildBag_injective (k : ℕ) :
    Function.Injective (rootChildBag k) := by
  intro f g h
  apply rootChildWithNeighborhood_injective k
  exact Sum.inr.inj (Finset.singleton_inj.mp h)

@[simp] theorem card_rootChildBags (k : ℕ) :
    (rootChildBags k).card = bonnetDepresBranch k := by
  classical
  rw [rootChildBags, Finset.card_image_of_injective]
  · simp [bonnetDepresBranch]
  · exact rootChildBag_injective k

theorem rootChildBags_subset_of_rootChildrenSingleton {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hroot : RootChildrenSingleton P) :
    rootChildBags k ⊆ P := by
  classical
  intro B hB
  rw [rootChildBags, Finset.mem_image] at hB
  rcases hB with ⟨f, _hf, rfl⟩
  exact (rootChildrenSingleton_iff.mp hroot) f

theorem one_lt_bonnetDepresBranch (k : ℕ) :
    1 < bonnetDepresBranch k := by
  have hpow : 2 ^ 0 < 2 ^ bonnetDepresApexCount k := by
    apply Nat.pow_lt_pow_right
    · omega
    · unfold bonnetDepresApexCount
      omega
  simpa [bonnetDepresBranch] using hpow

/-- A bag family with at most one part cannot keep all root children as
singleton bags. -/
theorem not_rootChildrenSingleton_of_card_le_one {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hcard : P.card ≤ 1) :
    ¬ RootChildrenSingleton P := by
  intro hroot
  have hle : (rootChildBags k).card ≤ P.card :=
    Finset.card_le_card (rootChildBags_subset_of_rootChildrenSingleton hroot)
  rw [card_rootChildBags] at hle
  have hbranch := one_lt_bonnetDepresBranch k
  omega

/-- Singleton root-child bags whose labels have a prescribed bit at an apex. -/
def apexBitRootChildBags {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) :
    Finset (Finset (BonnetDepresVertex k)) :=
  Finset.univ.image fun f : ApexBitFiber x b =>
    ({Sum.inr (rootChildWithNeighborhood k f.1)} :
      Finset (BonnetDepresVertex k))

/-- The root-child singleton bags with a prescribed apex bit are all distinct. -/
theorem card_apexBitRootChildBags {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) :
    (apexBitRootChildBags x b).card =
      2 ^ (bonnetDepresApexCount k - 1) := by
  classical
  rw [apexBitRootChildBags, Finset.card_image_of_injective]
  · simp [card_apexBitFiber x b]
  · intro f g h
    apply Subtype.ext
    apply rootChildWithNeighborhood_injective k
    exact Sum.inr.inj (Finset.singleton_inj.mp h)

@[simp] theorem rootChildrenSingleton_singletonBags (k : ℕ) :
    RootChildrenSingleton
      (TrigraphState.singletonBags (BonnetDepresVertex k)) := by
  intro f
  exact Finset.mem_image.mpr ⟨Sum.inr (rootChildWithNeighborhood k f), by simp, rfl⟩

/-- The singleton root-child bags separating two distinct apex vertices are all
distinct. -/
theorem card_separatingRootChildBags {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    (separatingRootChildBags x y).card =
      2 ^ (bonnetDepresApexCount k - 2) := by
  classical
  rw [separatingRootChildBags, Finset.card_image_of_injective]
  · simp [card_separatingApexBits hxy]
  · intro f g h
    apply Subtype.ext
    apply rootChildWithNeighborhood_injective k
    exact Sum.inr.inj (Finset.singleton_inj.mp h)

@[simp] theorem apexAdj_child_labelOfNeighborhood {k : ℕ}
    (x : Fin (bonnetDepresApexCount k))
    (parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : parent.1.val < bonnetDepresDepth k)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    bonnetDepresApexAdj x
        (FullTreeNode.child parent hlevel (labelOfNeighborhood f)) ↔
      f x = true := by
  simpa using
    (bonnetDepresApexAdj_child x parent hlevel (labelOfNeighborhood f))

/-- The child of `u` whose apex neighborhood is exactly `{y}`. -/
def childWithSingletonApexNeighborhood {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k)
    (y : Fin (bonnetDepresApexCount k)) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  FullTreeNode.child u hlevel
    (labelOfNeighborhood (singletonApexNeighborhood y))

@[simp] theorem apexAdj_childWithSingletonApexNeighborhood {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k)
    (x y : Fin (bonnetDepresApexCount k)) :
    bonnetDepresApexAdj x
        (childWithSingletonApexNeighborhood u hlevel y) ↔
      x = y := by
  rw [childWithSingletonApexNeighborhood, apexAdj_child_labelOfNeighborhood]
  simp [singletonApexNeighborhood]

/-- The children of an internal full-tree node. -/
def childSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :=
  Finset.univ.image (FullTreeNode.child u hlevel)

/-- The graph vertices corresponding to the children of an internal tree node. -/
def childVertexSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (BonnetDepresVertex k) :=
  (childSet u hlevel).image Sum.inr

@[simp] theorem mem_childSet {k : ℕ}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k} :
    w ∈ childSet u hlevel ↔
      ∃ label : Fin (bonnetDepresBranch k),
        FullTreeNode.child u hlevel label = w := by
  classical
  simp [childSet, eq_comm]

/-- Membership in a child set fixes the child's level. -/
theorem level_eq_succ_of_mem_childSet {k : ℕ}
    {u c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hc : c ∈ childSet u hlevel) :
    c.1.val = u.1.val + 1 := by
  rcases mem_childSet.mp hc with ⟨label, rfl⟩
  simp [FullTreeNode.child]

/-- A child-set member is also a descendant of its parent. -/
theorem isAncestor_of_mem_childSet {k : ℕ}
    {u c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hc : c ∈ childSet u hlevel) :
    IsTreeAncestor u c := by
  rcases mem_childSet.mp hc with ⟨label, rfl⟩
  exact isTreeAncestor_child u hlevel label

/-- Distinct siblings cannot both be ancestors of the same tree node. -/
theorem not_isTreeAncestor_of_distinct_siblings {k : ℕ}
    {u c₁ c₂ w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hc₁ : c₁ ∈ childSet u hlevel)
    (hc₂ : c₂ ∈ childSet u hlevel)
    (hcne : c₁ ≠ c₂)
    (h₁ : IsTreeAncestor c₁ w)
    (h₂ : IsTreeAncestor c₂ w) :
    False := by
  apply hcne
  exact eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq h₁ h₂
    ((level_eq_succ_of_mem_childSet hc₁).trans
      (level_eq_succ_of_mem_childSet hc₂).symm)

/-- Descendants of `q` whose tree vertices lie in the bag `A`. -/
noncomputable def descendantsInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact Finset.univ.filter fun z =>
    IsTreeAncestor q z ∧ (Sum.inr z : BonnetDepresVertex k) ∈ A

@[simp] theorem mem_descendantsInBag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q z : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)} :
    z ∈ descendantsInBag A q ↔
      IsTreeAncestor q z ∧ (Sum.inr z : BonnetDepresVertex k) ∈ A := by
  classical
  simp [descendantsInBag]

theorem descendantsInBag_nonempty_of_mem {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q z : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hqz : IsTreeAncestor q z)
    (hzA : (Sum.inr z : BonnetDepresVertex k) ∈ A) :
    (descendantsInBag A q).Nonempty := by
  exact ⟨z, by rw [mem_descendantsInBag]; exact ⟨hqz, hzA⟩⟩

/-- `x` lies on the tree path from an ancestor `q` down to a descendant `z`.
Endpoints are included. -/
def OnTreePath {branch depth : ℕ}
    (q z x : FullTreeNode branch depth) : Prop :=
  IsTreeAncestor q x ∧ IsTreeAncestor x z

/-- Descendants of `q` in `B` whose whole path from `q` avoids the previously
chosen bags `F`.  This is the formal version of the `Q_i` path condition in
Claim 19. -/
noncomputable def availableDescendantsInBag {k : ℕ}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (B : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact Finset.univ.filter fun z =>
    IsTreeAncestor q z ∧ (Sum.inr z : BonnetDepresVertex k) ∈ B ∧
      ∀ ⦃D⦄, D ∈ F → ∀ ⦃x⦄, OnTreePath q z x →
        (Sum.inr x : BonnetDepresVertex k) ∉ D

@[simp] theorem mem_availableDescendantsInBag {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q z : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)} :
    z ∈ availableDescendantsInBag F B q ↔
      IsTreeAncestor q z ∧ (Sum.inr z : BonnetDepresVertex k) ∈ B ∧
        ∀ ⦃D⦄, D ∈ F → ∀ ⦃x⦄, OnTreePath q z x →
          (Sum.inr x : BonnetDepresVertex k) ∉ D := by
  classical
  simp [availableDescendantsInBag]

theorem availableDescendantsInBag_nonempty_of_mem {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q z : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hqz : IsTreeAncestor q z)
    (hzB : (Sum.inr z : BonnetDepresVertex k) ∈ B)
    (havoid :
      ∀ ⦃D⦄, D ∈ F → ∀ ⦃x⦄, OnTreePath q z x →
        (Sum.inr x : BonnetDepresVertex k) ∉ D) :
    (availableDescendantsInBag F B q).Nonempty := by
  exact ⟨z, by rw [mem_availableDescendantsInBag]; exact ⟨hqz, hzB, havoid⟩⟩

/-- The highest, i.e. minimum-level, currently available descendant. -/
noncomputable def highestAvailableDescendantInBag {k : ℕ}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (B : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (h : (availableDescendantsInBag F B q).Nonempty) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  Classical.choose
    (Finset.exists_min_image (availableDescendantsInBag F B q) (fun z => z.1.val) h)

theorem highestAvailableDescendantInBag_spec {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (availableDescendantsInBag F B q).Nonempty) :
    highestAvailableDescendantInBag F B q h ∈ availableDescendantsInBag F B q ∧
      ∀ z ∈ availableDescendantsInBag F B q,
        (highestAvailableDescendantInBag F B q h).1.val ≤ z.1.val :=
  Classical.choose_spec
    (Finset.exists_min_image (availableDescendantsInBag F B q) (fun z => z.1.val) h)

theorem highestAvailableDescendantInBag_isAncestor {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (availableDescendantsInBag F B q).Nonempty) :
    IsTreeAncestor q (highestAvailableDescendantInBag F B q h) := by
  exact (mem_availableDescendantsInBag.mp
    (highestAvailableDescendantInBag_spec h).1).1

theorem highestAvailableDescendantInBag_mem_bag {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (availableDescendantsInBag F B q).Nonempty) :
    (Sum.inr (highestAvailableDescendantInBag F B q h) : BonnetDepresVertex k) ∈ B := by
  exact (mem_availableDescendantsInBag.mp
    (highestAvailableDescendantInBag_spec h).1).2.1

theorem highestAvailableDescendantInBag_path_avoids {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (availableDescendantsInBag F B q).Nonempty) :
    ∀ ⦃D⦄, D ∈ F → ∀ ⦃x⦄,
      OnTreePath q (highestAvailableDescendantInBag F B q h) x →
        (Sum.inr x : BonnetDepresVertex k) ∉ D := by
  exact (mem_availableDescendantsInBag.mp
    (highestAvailableDescendantInBag_spec h).1).2.2

theorem parent_notMem_bag_of_highestAvailableDescendant {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (availableDescendantsInBag F B q).Nonempty}
    (hp : FullTreeNode.IsParent p (highestAvailableDescendantInBag F B q h))
    (hstrict : q.1.val < (highestAvailableDescendantInBag F B q h).1.val) :
    (Sum.inr p : BonnetDepresVertex k) ∉ B := by
  intro hpB
  have hqp : IsTreeAncestor q p :=
    isTreeAncestor_parent_of_strict_descendant
      (highestAvailableDescendantInBag_isAncestor h) hp hstrict
  have hpPath :
      OnTreePath q (highestAvailableDescendantInBag F B q h) p := by
    exact ⟨hqp, isTreeAncestor_of_isParent hp⟩
  have hpAvail : p ∈ availableDescendantsInBag F B q := by
    rw [mem_availableDescendantsInBag]
    refine ⟨hqp, hpB, ?_⟩
    intro D hD x hx
    exact highestAvailableDescendantInBag_path_avoids h hD
      ⟨hx.1, isTreeAncestor_trans hx.2 (isTreeAncestor_of_isParent hp)⟩
  have hmin := (highestAvailableDescendantInBag_spec h).2 p hpAvail
  have hpLevel : (highestAvailableDescendantInBag F B q h).1.val = p.1.val + 1 :=
    FullTreeNode.isParent_level hp
  omega

/-- The highest, i.e. minimum-level, descendant of `q` whose vertex lies in
`A`, assuming such a descendant exists. -/
noncomputable def highestDescendantInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (h : (descendantsInBag A q).Nonempty) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  Classical.choose
    (Finset.exists_min_image (descendantsInBag A q) (fun z => z.1.val) h)

theorem highestDescendantInBag_spec {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (descendantsInBag A q).Nonempty) :
    highestDescendantInBag A q h ∈ descendantsInBag A q ∧
      ∀ z ∈ descendantsInBag A q,
        (highestDescendantInBag A q h).1.val ≤ z.1.val :=
  Classical.choose_spec
    (Finset.exists_min_image (descendantsInBag A q) (fun z => z.1.val) h)

theorem highestDescendantInBag_isAncestor {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (descendantsInBag A q).Nonempty) :
    IsTreeAncestor q (highestDescendantInBag A q h) := by
  exact (mem_descendantsInBag.mp (highestDescendantInBag_spec h).1).1

theorem highestDescendantInBag_mem_bag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (descendantsInBag A q).Nonempty) :
    (Sum.inr (highestDescendantInBag A q h) : BonnetDepresVertex k) ∈ A := by
  exact (mem_descendantsInBag.mp (highestDescendantInBag_spec h).1).2

/-- The parent of a strict highest descendant in a bag. -/
noncomputable def highestParentInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (h : (descendantsInBag A q).Nonempty)
    (hstrict : q.1.val < (highestDescendantInBag A q h).1.val) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  FullTreeNode.parent (highestDescendantInBag A q h) (by omega)

theorem highestParentInBag_isParent {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (descendantsInBag A q).Nonempty}
    {hstrict : q.1.val < (highestDescendantInBag A q h).1.val} :
    FullTreeNode.IsParent (highestParentInBag A q h hstrict)
      (highestDescendantInBag A q h) := by
  exact FullTreeNode.parent_isParent
    (highestDescendantInBag A q h) (by omega)

theorem highestParentInBag_isAncestor {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (descendantsInBag A q).Nonempty}
    {hstrict : q.1.val < (highestDescendantInBag A q h).1.val} :
    IsTreeAncestor q (highestParentInBag A q h hstrict) :=
  isTreeAncestor_parent_of_strict_descendant
    (highestDescendantInBag_isAncestor h)
    highestParentInBag_isParent hstrict

theorem highestParentInBag_level_lt_highestDescendant {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (descendantsInBag A q).Nonempty}
    {hstrict : q.1.val < (highestDescendantInBag A q h).1.val} :
    (highestParentInBag A q h hstrict).1.val <
      (highestDescendantInBag A q h).1.val := by
  have hlevel :=
    FullTreeNode.isParent_level
      (highestParentInBag_isParent (A := A) (q := q) (h := h) (hstrict := hstrict))
  omega

/-- The parent of a strict highest descendant cannot already lie in the bag;
otherwise it would be a higher descendant in that bag. -/
theorem parent_notMem_bag_of_highestDescendant {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (descendantsInBag A q).Nonempty}
    (hp : FullTreeNode.IsParent p (highestDescendantInBag A q h))
    (hstrict : q.1.val < (highestDescendantInBag A q h).1.val) :
    (Sum.inr p : BonnetDepresVertex k) ∉ A := by
  intro hpA
  have hqp : IsTreeAncestor q p :=
    isTreeAncestor_parent_of_strict_descendant
      (highestDescendantInBag_isAncestor h) hp hstrict
  have hpCandidate : p ∈ descendantsInBag A q := by
    rw [mem_descendantsInBag]
    exact ⟨hqp, hpA⟩
  have hmin := (highestDescendantInBag_spec h).2 p hpCandidate
  have hpLevel : (highestDescendantInBag A q h).1.val = p.1.val + 1 :=
    FullTreeNode.isParent_level hp
  omega

@[simp] theorem card_childSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (childSet u hlevel).card = bonnetDepresBranch k := by
  classical
  rw [childSet, Finset.card_image_of_injective]
  · simp
  · exact child_injective_label u hlevel

@[simp] theorem card_childVertexSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (childVertexSet u hlevel).card = bonnetDepresBranch k := by
  classical
  rw [childVertexSet, Finset.card_image_of_injective]
  · exact card_childSet u hlevel
  · intro a b h
    exact Sum.inr.inj h

/-- Distinct children of one tree node differ on adjacency to at least one apex. -/
theorem exists_apexAdj_disagree_of_distinct_children {k : ℕ}
    {u c₁ c₂ : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hc₁ : c₁ ∈ childSet u hlevel)
    (hc₂ : c₂ ∈ childSet u hlevel)
    (hcne : c₁ ≠ c₂) :
    ∃ x : Fin (bonnetDepresApexCount k),
      (bonnetDepresApexAdj x c₁ ∧ ¬ bonnetDepresApexAdj x c₂) ∨
        (bonnetDepresApexAdj x c₂ ∧ ¬ bonnetDepresApexAdj x c₁) := by
  rcases mem_childSet.mp hc₁ with ⟨label₁, rfl⟩
  rcases mem_childSet.mp hc₂ with ⟨label₂, rfl⟩
  have hlabel_ne : label₁ ≠ label₂ := by
    intro hlabel
    exact hcne (by simp [hlabel])
  rcases exists_bit_ne_of_fin_pow_ne
      (n := bonnetDepresApexCount k) (a := label₁) (b := label₂)
      (by simpa [bonnetDepresBranch] using hlabel_ne) with
    ⟨x, hxbit⟩
  by_cases h₁ : label₁.val.testBit x.val = true
  · have h₂ : label₂.val.testBit x.val = false := by
      cases h₂bit : label₂.val.testBit x.val <;> simp [h₁, h₂bit] at hxbit ⊢
    refine ⟨x, Or.inl ⟨?_, ?_⟩⟩
    · rw [bonnetDepresApexAdj_child x u hlevel label₁]
      exact h₁
    · intro hAdj
      rw [bonnetDepresApexAdj_child x u hlevel label₂] at hAdj
      simp [h₂] at hAdj
  · have h₁f : label₁.val.testBit x.val = false := by
      cases h₁bit : label₁.val.testBit x.val
      · rfl
      · exact (h₁ h₁bit).elim
    have h₂ : label₂.val.testBit x.val = true := by
      cases h₂bit : label₂.val.testBit x.val <;> simp [h₁f, h₂bit] at hxbit ⊢
    refine ⟨x, Or.inr ⟨?_, ?_⟩⟩
    · rw [bonnetDepresApexAdj_child x u hlevel label₂]
      exact h₂
    · intro hAdj
      rw [bonnetDepresApexAdj_child x u hlevel label₁] at hAdj
      simp [h₁f] at hAdj

/-- If a bag contains two tree vertices that disagree on an apex, then it is
red-adjacent to the singleton bag of that apex. -/
theorem partitionRedAdj_of_apexAdj_disagree_in_bag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    {c₁ c₂ : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hc₁A : (Sum.inr c₁ : BonnetDepresVertex k) ∈ A)
    (hc₂A : (Sum.inr c₂ : BonnetDepresVertex k) ∈ A)
    (hadj₁ : bonnetDepresApexAdj x c₁)
    (hnot₂ : ¬ bonnetDepresApexAdj x c₂) :
    partitionRedAdj (bonnetDepresGraph k) A
      ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro hAeq
    have hc₁Singleton :
        (Sum.inr c₁ : BonnetDepresVertex k) ∈
          ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
      rw [hAeq] at hc₁A
      exact hc₁A
    simp at hc₁Singleton
  · intro hhom
    rcases hhom with hcomp | hemp
    · have hGraph :
          (bonnetDepresGraph k).Adj
            (Sum.inr c₂ : BonnetDepresVertex k) (Sum.inl x) :=
        hcomp hc₂A (by simp)
      have hAdj : bonnetDepresApexAdj x c₂ := by
        simpa [bonnetDepresGraph] using hGraph
      exact hnot₂ hAdj
    · have hGraph :
          (bonnetDepresGraph k).Adj
            (Sum.inr c₁ : BonnetDepresVertex k) (Sum.inl x) := by
        simpa [bonnetDepresGraph] using hadj₁
      exact hemp hc₁A (by simp) hGraph

/-- Two distinct children of one node in the same bag force some apex singleton
to be red-adjacent to that bag. -/
theorem exists_apex_partitionRedAdj_of_distinct_children_in_bag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u c₁ c₂ : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hc₁child : c₁ ∈ childSet u hlevel)
    (hc₂child : c₂ ∈ childSet u hlevel)
    (hcne : c₁ ≠ c₂)
    (hc₁A : (Sum.inr c₁ : BonnetDepresVertex k) ∈ A)
    (hc₂A : (Sum.inr c₂ : BonnetDepresVertex k) ∈ A) :
    ∃ x : Fin (bonnetDepresApexCount k),
      partitionRedAdj (bonnetDepresGraph k) A
        ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
  rcases exists_apexAdj_disagree_of_distinct_children
      hc₁child hc₂child hcne with
    ⟨x, hdisagree | hdisagree⟩
  · exact ⟨x,
      partitionRedAdj_of_apexAdj_disagree_in_bag
        hc₁A hc₂A hdisagree.1 hdisagree.2⟩
  · exact ⟨x,
      partitionRedAdj_of_apexAdj_disagree_in_bag
        hc₂A hc₁A hdisagree.1 hdisagree.2⟩

/-- Apex coordinates on which a set of siblings realizes both adjacency values. -/
noncomputable def childApexVariationSet {k : ℕ}
    (S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))) :
    Finset (Fin (bonnetDepresApexCount k)) := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ c₁ ∈ S, ∃ c₂ ∈ S,
      (bonnetDepresApexAdj x c₁ ∧ ¬ bonnetDepresApexAdj x c₂) ∨
        (bonnetDepresApexAdj x c₂ ∧ ¬ bonnetDepresApexAdj x c₁)

/-- A sibling set is encoded injectively by its values on the coordinates where
the set actually varies. -/
theorem card_le_pow_childApexVariationSet_card {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    {S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hS : S ⊆ childSet u hlevel) :
    S.card ≤ 2 ^ (childApexVariationSet S).card := by
  classical
  let code :
      {c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) // c ∈ S} →
        ({x : Fin (bonnetDepresApexCount k) // x ∈ childApexVariationSet S} → Bool) :=
    fun c x => decide (bonnetDepresApexAdj x.1 c.1)
  have hcode_inj : Function.Injective code := by
    intro c₁ c₂ hcode
    by_contra hne
    have hc₁child : c₁.1 ∈ childSet u hlevel := hS c₁.2
    have hc₂child : c₂.1 ∈ childSet u hlevel := hS c₂.2
    rcases exists_apexAdj_disagree_of_distinct_children
        hc₁child hc₂child (by intro h; exact hne (Subtype.ext h)) with
      ⟨x, hdisagree | hdisagree⟩
    · have hx :
          x ∈ childApexVariationSet S := by
        rw [childApexVariationSet, Finset.mem_filter]
        exact ⟨by simp, c₁.1, c₁.2, c₂.1, c₂.2, Or.inl hdisagree⟩
      have hbit := congrFun hcode ⟨x, hx⟩
      simp [code, hdisagree.1, hdisagree.2] at hbit
    · have hx :
          x ∈ childApexVariationSet S := by
        rw [childApexVariationSet, Finset.mem_filter]
        exact ⟨by simp, c₁.1, c₁.2, c₂.1, c₂.2, Or.inr hdisagree⟩
      have hbit := congrFun hcode ⟨x, hx⟩
      simp [code, hdisagree.1, hdisagree.2] at hbit
  calc
    S.card = Fintype.card
        {c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) // c ∈ S} := by
      simp
    _ ≤ Fintype.card
        ({x : Fin (bonnetDepresApexCount k) // x ∈ childApexVariationSet S} → Bool) :=
      Fintype.card_le_of_injective code hcode_inj
    _ = 2 ^ (childApexVariationSet S).card := by
      rw [Fintype.card_fun]
      simp [Fintype.card_bool]

/-- A set of at least `2^(k+1)` siblings varies on at least `k+1` apex
coordinates. -/
theorem le_childApexVariationSet_card_of_many_children {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    {S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hS : S ⊆ childSet u hlevel)
    (hmany : 2 ^ (k + 1) ≤ S.card) :
    k + 1 ≤ (childApexVariationSet S).card := by
  have hpow :
      2 ^ (k + 1) ≤ 2 ^ (childApexVariationSet S).card := by
    exact hmany.trans (card_le_pow_childApexVariationSet_card hS)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow

/-- A tree node is not one of its own children. -/
theorem parent_notMem_childVertexSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (Sum.inr u : BonnetDepresVertex k) ∉ childVertexSet u hlevel := by
  classical
  intro hmem
  rw [childVertexSet, Finset.mem_image] at hmem
  rcases hmem with ⟨c, hc, hcu⟩
  have hc_eq : c = u := Sum.inr.inj hcu
  rcases mem_childSet.mp hc with ⟨label, rfl⟩
  have hlevel_eq :
      (FullTreeNode.child u hlevel label).1.val = u.1.val := by
    exact congrArg (fun z => z.1.val) hc_eq
  simp [FullTreeNode.child] at hlevel_eq

/-- Adding the singleton parent vertex to a bag does not change its intersection
with the child set of that parent. -/
theorem singleton_parent_union_inter_childVertexSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k)
    (B : Finset (BonnetDepresVertex k)) :
    (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B) ∩
        childVertexSet u hlevel =
      B ∩ childVertexSet u hlevel := by
  classical
  ext v
  rw [Finset.mem_inter, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hv | hv, hvchild⟩
    · rw [Finset.mem_singleton] at hv
      subst v
      exact (parent_notMem_childVertexSet u hlevel hvchild).elim
    · exact ⟨hv, hvchild⟩
  · rintro ⟨hvB, hvchild⟩
    exact ⟨Or.inr hvB, hvchild⟩

/-- Children of `u` whose graph vertices lie in a specified bag. -/
noncomputable def childrenInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact (childSet u hlevel).filter fun c => (Sum.inr c : BonnetDepresVertex k) ∈ A

@[simp] theorem mem_childrenInBag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k} :
    c ∈ childrenInBag A u hlevel ↔
      c ∈ childSet u hlevel ∧ (Sum.inr c : BonnetDepresVertex k) ∈ A := by
  classical
  simp [childrenInBag]

/-- Counting children in a bag agrees with counting child vertices in that bag. -/
theorem card_childrenInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (childrenInBag A u hlevel).card =
      (A ∩ childVertexSet u hlevel).card := by
  classical
  have himage :
      (childrenInBag A u hlevel).image
          (Sum.inr : _ → BonnetDepresVertex k) =
        A ∩ childVertexSet u hlevel := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_image] at hv
      rcases hv with ⟨c, hc, rfl⟩
      rw [Finset.mem_inter]
      exact ⟨(mem_childrenInBag.mp hc).2,
        by
          rw [childVertexSet, Finset.mem_image]
          exact ⟨c, (mem_childrenInBag.mp hc).1, rfl⟩⟩
    · intro hv
      rw [Finset.mem_inter] at hv
      rw [childVertexSet, Finset.mem_image] at hv
      rcases hv with ⟨hvA, c, hc, rfl⟩
      rw [Finset.mem_image]
      exact ⟨c, mem_childrenInBag.mpr ⟨hc, hvA⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injective]
  intro a b h
  exact Sum.inr.inj h

/-- Children of `u` that are adjacent to `w` in the full tree. -/
noncomputable def childAdjSet {k : ℕ}
    (u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact (childSet u hlevel).filter
    fun c =>
      (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c

/-- A tree vertex distinct from `u` is adjacent to at most one child of `u`. -/
theorem card_childAdjSet_le_one {k : ℕ}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k) (hwu : w ≠ u) :
    (childAdjSet u w hlevel).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have ha' :
      a ∈ (childSet u hlevel).filter
        (fun c =>
          (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c) := by
    simpa [childAdjSet] using ha
  have hb' :
      b ∈ (childSet u hlevel).filter
        (fun c =>
          (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c) := by
    simpa [childAdjSet] using hb
  rw [Finset.mem_filter] at ha' hb'
  rcases ha' with ⟨ha_child, ha_adj⟩
  rcases hb' with ⟨hb_child, hb_adj⟩
  rcases mem_childSet.mp ha_child with ⟨la, rfl⟩
  rcases mem_childSet.mp hb_child with ⟨lb, rfl⟩
  have hua :
      FullTreeNode.IsParent u (FullTreeNode.child u hlevel la) :=
    FullTreeNode.isParent_child u hlevel la
  have hub :
      FullTreeNode.IsParent u (FullTreeNode.child u hlevel lb) :=
    FullTreeNode.isParent_child u hlevel lb
  have hpa :
      FullTreeNode.IsParent (FullTreeNode.child u hlevel la) w := by
    rcases ha_adj with h | h
    · have hwu_eq : w = u := FullTreeNode.isParent_unique h hua
      exact (hwu hwu_eq).elim
    · exact h
  have hpb :
      FullTreeNode.IsParent (FullTreeNode.child u hlevel lb) w := by
    rcases hb_adj with h | h
    · have hwu_eq : w = u := FullTreeNode.isParent_unique h hub
      exact (hwu hwu_eq).elim
    · exact h
  exact FullTreeNode.isParent_unique hpa hpb

/-- Children of `u` that are not adjacent to `w`, viewed as vertices of the
Bonnet--Déprés graph. -/
noncomputable def childNonAdjVertexSet {k : ℕ}
    (u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (BonnetDepresVertex k) :=
  childVertexSet u hlevel \ (childAdjSet u w hlevel).image Sum.inr

/-- Membership in the non-adjacent child set is exactly child membership plus
non-adjacency to the witness vertex. -/
theorem mem_childNonAdjVertexSet {k : ℕ}
    {u w c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (Sum.inr c : BonnetDepresVertex k) ∈ childNonAdjVertexSet u w hlevel ↔
      c ∈ childSet u hlevel ∧
        ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c := by
  classical
  constructor
  · intro hv
    rw [childNonAdjVertexSet, Finset.mem_sdiff] at hv
    rcases hv with ⟨hchildv, hnotbad⟩
    rw [childVertexSet, Finset.mem_image] at hchildv
    rcases hchildv with ⟨c', hc', hc'eq⟩
    have hc_eq : c' = c := Sum.inr.inj hc'eq
    subst c'
    refine ⟨hc', ?_⟩
    intro hadj
    apply hnotbad
    rw [Finset.mem_image]
    refine ⟨c, ?_, rfl⟩
    have hfilter :
        c ∈ (childSet u hlevel).filter
          (fun z =>
            (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w z) := by
      rw [Finset.mem_filter]
      exact ⟨hc', hadj⟩
    simpa [childAdjSet] using hfilter
  · rintro ⟨hcchild, hnotadj⟩
    rw [childNonAdjVertexSet, Finset.mem_sdiff]
    constructor
    · rw [childVertexSet, Finset.mem_image]
      exact ⟨c, hcchild, rfl⟩
    · intro hbad
      rw [Finset.mem_image] at hbad
      rcases hbad with ⟨c', hc', hc'eq⟩
      have hc_eq : c' = c := Sum.inr.inj hc'eq
      subst c'
      have hfilter :
          c ∈ (childSet u hlevel).filter
            (fun z =>
              (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w z) := by
        simpa [childAdjSet] using hc'
      rw [Finset.mem_filter] at hfilter
      exact hnotadj hfilter.2

/-- All but at most one child of `u` are non-adjacent to a fixed tree vertex
`w ≠ u`. -/
theorem card_childNonAdjVertexSet_ge {k : ℕ}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k) (hwu : w ≠ u) :
    bonnetDepresBranch k - 1 ≤ (childNonAdjVertexSet u w hlevel).card := by
  classical
  have hsubset :
      (childAdjSet u w hlevel).image Sum.inr ⊆ childVertexSet u hlevel := by
    intro v hv
    rw [Finset.mem_image] at hv
    rcases hv with ⟨c, hc, rfl⟩
    have hc_child : c ∈ childSet u hlevel := by
      have hc' :
          c ∈ (childSet u hlevel).filter
            (fun z =>
              (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w z) := by
        simpa [childAdjSet] using hc
      rw [Finset.mem_filter] at hc'
      exact hc'.1
    rw [childVertexSet, Finset.mem_image]
    exact ⟨c, hc_child, rfl⟩
  have hcard :
      (childNonAdjVertexSet u w hlevel).card =
        (childVertexSet u hlevel).card -
          ((childAdjSet u w hlevel).image
            (Sum.inr : _ → BonnetDepresVertex k)).card := by
    rw [childNonAdjVertexSet, Finset.card_sdiff_of_subset hsubset]
  have hbad :
      ((childAdjSet u w hlevel).image (Sum.inr : _ → BonnetDepresVertex k)).card ≤ 1 := by
    rw [Finset.card_image_of_injective]
    · exact card_childAdjSet_le_one hlevel hwu
    · intro a b h
      exact Sum.inr.inj h
  rw [hcard, card_childVertexSet]
  omega

/-- `P(v,H)` from the paper, with an explicit threshold: at least `m`
children of `u` lie in one current part. -/
def HasManyChildrenInPart {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) (m : ℕ) : Prop :=
  ∃ A ∈ P, m ≤ (A ∩ childVertexSet u hlevel).card

/-- A node has many children that themselves satisfy `HasManyChildrenInPart`.
This is the formal Claim-16 conclusion. -/
def HasManyPChildren {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) (m : ℕ) : Prop :=
  ∃ S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
    S ⊆ childSet u hlevel ∧ m ≤ S.card ∧
      ∀ ⦃c⦄, c ∈ S →
        ∃ hc : c.1.val < bonnetDepresDepth k,
          HasManyChildrenInPart P c hc m

/-- The threshold used for property `P` in the specialized lower-bound proof. -/
def manyChildrenThreshold (k : ℕ) : ℕ :=
  2 ^ (k + 1)

theorem two_le_manyChildrenThreshold (k : ℕ) :
    2 ≤ manyChildrenThreshold k := by
  unfold manyChildrenThreshold
  have hpow : 2 ^ 1 ≤ 2 ^ (k + 1) := by
    apply Nat.pow_le_pow_right
    · omega
    · omega
  simpa using hpow

theorem manyChildrenThreshold_pos (k : ℕ) :
    0 < manyChildrenThreshold k := by
  exact (Nat.zero_lt_two.trans_le (two_le_manyChildrenThreshold k))

/-- The number of side branches forced into a single large bag in the final
pigeonhole step of the lower-bound proof. -/
def manySideBranchesThreshold (k : ℕ) : ℕ :=
  2 ^ ((k + 1) * (2 + 2 ^ (k + 2) * (manyChildrenThreshold k + 1)))

/-- The number of non-singleton internal-tree parts that contradicts the
large-bag red-degree upper bound. -/
def manyInternalBagsThreshold (k : ℕ) : ℕ :=
  1 + 2 ^ (k + 2) * (manyChildrenThreshold k + 1)

/-- The depth of the Bonnet--Déprés tree is tuned to pigeonhole the
Claim-18 side branches among at most `2^(k+2)` large bags. -/
theorem depth_sub_two_eq_largeBagBound_mul_manySideBranchesThreshold (k : ℕ) :
    bonnetDepresDepth k - 2 =
      2 ^ (k + 2) * manySideBranchesThreshold k := by
  simp [bonnetDepresDepth, manySideBranchesThreshold, manyChildrenThreshold]

theorem manySideBranchesThreshold_eq_manyChildrenThreshold_pow (k : ℕ) :
    manySideBranchesThreshold k =
      (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k + 1) := by
  rw [manySideBranchesThreshold, manyChildrenThreshold, manyInternalBagsThreshold]
  rw [pow_mul]
  congr 1
  simp [manyChildrenThreshold]
  omega

theorem redBound_mul_manyChildrenThreshold_pow_lt_succ {k d r : ℕ}
    (hd : d ≤ 2 ^ k) :
    d * (manyChildrenThreshold k) ^ r <
      (manyChildrenThreshold k) ^ (r + 1) := by
  have hd_lt : d < manyChildrenThreshold k := by
    unfold manyChildrenThreshold
    have hpow : 2 ^ k < 2 ^ (k + 1) := by
      exact Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega : k < k + 1)
    exact lt_of_le_of_lt hd hpow
  have hpos : 0 < (manyChildrenThreshold k) ^ r :=
    pow_pos (manyChildrenThreshold_pos k) r
  calc
    d * (manyChildrenThreshold k) ^ r
        < manyChildrenThreshold k * (manyChildrenThreshold k) ^ r :=
          Nat.mul_lt_mul_of_pos_right hd_lt hpos
    _ = (manyChildrenThreshold k) ^ (r + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]

/-- A bag is large when it contains at least the threshold number of children of
one internal tree node.  This is the set `B` from the paper, phrased at the
partition level. -/
def IsLargeChildBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k)) : Prop :=
  ∃ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
    ∃ hlevel : u.1.val < bonnetDepresDepth k,
      manyChildrenThreshold k ≤ (A ∩ childVertexSet u hlevel).card

/-- The family of large child bags in a partition. -/
noncomputable def largeChildBags {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k))) :
    Finset (Finset (BonnetDepresVertex k)) := by
  classical
  exact P.filter IsLargeChildBag

@[simp] theorem mem_largeChildBags {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)} :
    A ∈ largeChildBags P ↔ A ∈ P ∧ IsLargeChildBag A := by
  classical
  simp [largeChildBags]

/-- A witness to property `P` is exactly a member of the large-child-bag family. -/
theorem exists_largeChildBag_of_hasManyChildrenInPart {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hP : HasManyChildrenInPart P u hlevel (manyChildrenThreshold k)) :
    ∃ A ∈ largeChildBags P,
      manyChildrenThreshold k ≤ (A ∩ childVertexSet u hlevel).card := by
  classical
  rcases hP with ⟨A, hA, hmany⟩
  refine ⟨A, ?_, hmany⟩
  rw [mem_largeChildBags]
  exact ⟨hA, u, hlevel, hmany⟩

/-- A large child-count witness contains at least one actual child vertex. -/
theorem exists_child_mem_bag_of_manyChildren {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hmany : manyChildrenThreshold k ≤ (A ∩ childVertexSet u hlevel).card) :
    ∃ c ∈ childSet u hlevel, (Sum.inr c : BonnetDepresVertex k) ∈ A := by
  classical
  have hpos : 0 < (A ∩ childVertexSet u hlevel).card :=
    (manyChildrenThreshold_pos k).trans_le hmany
  rcases Finset.card_pos.mp hpos with ⟨z, hz⟩
  rw [Finset.mem_inter] at hz
  rw [childVertexSet, Finset.mem_image] at hz
  rcases hz.2 with ⟨c, hc, rfl⟩
  exact ⟨c, hc, hz.1⟩

/-- The apex coordinates whose singleton bags are red-adjacent to `A`. -/
noncomputable def apexRedCoordinatesOfBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k)) :
    Finset (Fin (bonnetDepresApexCount k)) := by
  classical
  exact Finset.univ.filter fun x =>
    partitionRedAdj (bonnetDepresGraph k) A
      ({Sum.inl x} : Finset (BonnetDepresVertex k))

/-- Large bags that are red-adjacent to a fixed apex singleton. -/
noncomputable def largeChildBagsRedAdjacentToApex {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (x : Fin (bonnetDepresApexCount k)) :
    Finset (Finset (BonnetDepresVertex k)) := by
  classical
  exact (largeChildBags P).filter fun A =>
    partitionRedAdj (bonnetDepresGraph k) A
      ({Sum.inl x} : Finset (BonnetDepresVertex k))

/-- Incidences between large child bags and apex coordinates witnessing red
adjacency. -/
noncomputable def largeChildBagApexIncidences {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k))) :
    Finset (Finset (BonnetDepresVertex k) × Fin (bonnetDepresApexCount k)) := by
  classical
  exact ((largeChildBags P).product Finset.univ).filter fun pair =>
    partitionRedAdj (bonnetDepresGraph k) pair.1
      ({Sum.inl pair.2} : Finset (BonnetDepresVertex k))

/-- A large child bag is red-adjacent to at least `k+1` apex singleton bags:
`2^(k+1)` distinct sibling labels need at least `k+1` varying apex bits. -/
theorem le_card_apexRedCoordinatesOfBag_of_isLargeChildBag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    (hlarge : IsLargeChildBag A) :
    k + 1 ≤ (apexRedCoordinatesOfBag A).card := by
  classical
  rcases hlarge with ⟨u, hlevel, hmany⟩
  let S := childrenInBag A u hlevel
  have hSsubset : S ⊆ childSet u hlevel := by
    intro c hc
    exact (mem_childrenInBag.mp hc).1
  have hSA :
      ∀ ⦃c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)⦄,
        c ∈ S → (Sum.inr c : BonnetDepresVertex k) ∈ A := by
    intro c hc
    exact (mem_childrenInBag.mp hc).2
  have hmanyS : 2 ^ (k + 1) ≤ S.card := by
    simpa [S, manyChildrenThreshold, card_childrenInBag] using hmany
  have hvarLower :
      k + 1 ≤ (childApexVariationSet S).card :=
    le_childApexVariationSet_card_of_many_children hSsubset hmanyS
  have hvarSubset :
      childApexVariationSet S ⊆ apexRedCoordinatesOfBag A := by
    intro x hx
    rw [apexRedCoordinatesOfBag, Finset.mem_filter]
    refine ⟨by simp, ?_⟩
    rw [childApexVariationSet, Finset.mem_filter] at hx
    rcases hx.2 with ⟨c₁, hc₁, c₂, hc₂, hdisagree | hdisagree⟩
    · exact partitionRedAdj_of_apexAdj_disagree_in_bag
        (hSA hc₁) (hSA hc₂) hdisagree.1 hdisagree.2
    · exact partitionRedAdj_of_apexAdj_disagree_in_bag
        (hSA hc₂) (hSA hc₁) hdisagree.1 hdisagree.2
  exact hvarLower.trans (Finset.card_le_card hvarSubset)

/-- Fuelled form of the paper's property `Q`.

At a preleaf it is just property `P`; otherwise two distinct children must
satisfy `Q` at one lower fuel.  The public `QProperty` below supplies enough
fuel from the node height. -/
def QPropertyAtFuel {k : ℕ} :
    ℕ →
      Finset (Finset (BonnetDepresVertex k)) →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) → Prop
  | 0, _P, _u => False
  | fuel + 1, P, u =>
      (IsPreleaf u ∧
        ∃ hlevel : IsInternal u,
          HasManyChildrenInPart P u hlevel (manyChildrenThreshold k)) ∨
      (¬ IsPreleaf u ∧
        ∃ hlevel : IsInternal u,
          ∃ c₁ ∈ childSet u hlevel, ∃ c₂ ∈ childSet u hlevel,
            c₁ ≠ c₂ ∧ QPropertyAtFuel fuel P c₁ ∧ QPropertyAtFuel fuel P c₂)

/-- The paper's property `Q`, with fuel equal to the remaining tree height. -/
def QProperty {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : Prop :=
  QPropertyAtFuel (bonnetDepresDepth k - u.1.val) P u

/-- Property `P` is monotone under one bag contraction. -/
theorem hasManyChildrenInPart_mono_of_isBagContraction {k m : ℕ}
    {P Q : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hPQ : IsBagContraction P Q)
    (hP : HasManyChildrenInPart P u hlevel m) :
    HasManyChildrenInPart Q u hlevel m := by
  classical
  rcases hP with ⟨C, hC, hcard⟩
  rcases hPQ with ⟨A, hA, B, hB, hAB, rfl⟩
  by_cases hCA : C = A
  · refine ⟨A ∪ B, ?_, ?_⟩
    · exact Finset.mem_insert_self _ _
    · have hsubset :
          C ∩ childVertexSet u hlevel ⊆
            (A ∪ B) ∩ childVertexSet u hlevel := by
        intro v hv
        rw [Finset.mem_inter] at hv ⊢
        exact ⟨Finset.mem_union_left _ (by simpa [hCA] using hv.1), hv.2⟩
      exact hcard.trans (Finset.card_le_card hsubset)
  · by_cases hCB : C = B
    · refine ⟨A ∪ B, ?_, ?_⟩
      · exact Finset.mem_insert_self _ _
      · have hsubset :
            C ∩ childVertexSet u hlevel ⊆
              (A ∪ B) ∩ childVertexSet u hlevel := by
          intro v hv
          rw [Finset.mem_inter] at hv ⊢
          exact ⟨Finset.mem_union_right _ (by simpa [hCB] using hv.1), hv.2⟩
        exact hcard.trans (Finset.card_le_card hsubset)
    · refine ⟨C, ?_, hcard⟩
      rw [mem_merge_family_iff]
      exact Or.inr ⟨hC, hCA, hCB⟩

/-- Fuelled `Q` is monotone under one bag contraction. -/
theorem qPropertyAtFuel_mono_of_isBagContraction {k : ℕ}
    {P Q : Finset (Finset (BonnetDepresVertex k))}
    (hPQ : IsBagContraction P Q) :
    ∀ fuel : ℕ,
      ∀ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        QPropertyAtFuel fuel P u → QPropertyAtFuel fuel Q u := by
  intro fuel
  induction fuel with
  | zero =>
      intro u h
      exact h.elim
  | succ fuel ih =>
      intro u hq
      rcases hq with ⟨hpre, hP⟩ | ⟨hnotpre, hchildren⟩
      · left
        rcases hP with ⟨hlevel, hP⟩
        exact ⟨hpre, hlevel,
          hasManyChildrenInPart_mono_of_isBagContraction hPQ hP⟩
      · right
        rcases hchildren with ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, hq₁, hq₂⟩
        exact ⟨hnotpre, hlevel, c₁, hc₁, c₂, hc₂, hcne,
          ih c₁ hq₁, ih c₂ hq₂⟩

/-- Property `Q` is monotone under one bag contraction. -/
theorem qProperty_mono_of_isBagContraction {k : ℕ}
    {P Q : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hPQ : IsBagContraction P Q)
    (hQ : QProperty P u) :
    QProperty Q u :=
  qPropertyAtFuel_mono_of_isBagContraction hPQ
    (bonnetDepresDepth k - u.1.val) u hQ

/-- A fuelled `Q` witness contains a preleaf node satisfying property `P`. -/
theorem exists_preleaf_hasManyChildrenInPart_of_qPropertyAtFuel {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))} :
    ∀ fuel : ℕ,
      ∀ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        QPropertyAtFuel fuel P u →
          ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            ∃ hlevel : IsInternal v,
              IsPreleaf v ∧
                HasManyChildrenInPart P v hlevel (manyChildrenThreshold k) := by
  intro fuel
  induction fuel with
  | zero =>
      intro u hq
      exact hq.elim
  | succ fuel ih =>
      intro u hq
      rcases hq with ⟨hpre, hP⟩ | ⟨_hnotpre, hchildren⟩
      · rcases hP with ⟨hlevel, hP⟩
        exact ⟨u, hlevel, hpre, hP⟩
      · rcases hchildren with ⟨_hlevel, c₁, _hc₁, _c₂, _hc₂, _hcne, hq₁, _hq₂⟩
        exact ih c₁ hq₁

/-- Descendant-carrying version of
`exists_preleaf_hasManyChildrenInPart_of_qPropertyAtFuel`. -/
theorem exists_preleaf_descendant_hasManyChildrenInPart_of_qPropertyAtFuel {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))} :
    ∀ fuel : ℕ,
      ∀ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        QPropertyAtFuel fuel P u →
          ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            IsTreeAncestor u v ∧
              IsPreleaf v ∧
                ∃ hlevel : IsInternal v,
                  HasManyChildrenInPart P v hlevel (manyChildrenThreshold k) := by
  intro fuel
  induction fuel with
  | zero =>
      intro u hq
      exact hq.elim
  | succ fuel ih =>
      intro u hq
      rcases hq with ⟨hpre, hP⟩ | ⟨_hnotpre, hchildren⟩
      · rcases hP with ⟨hlevel, hP⟩
        exact ⟨u, isTreeAncestor_refl u, hpre, hlevel, hP⟩
      · rcases hchildren with ⟨hlevel, c₁, hc₁, _c₂, _hc₂, _hcne, hq₁, _hq₂⟩
        rcases ih c₁ hq₁ with ⟨v, hcv, hpre, hvlevel, hP⟩
        exact ⟨v, isTreeAncestor_trans (isAncestor_of_mem_childSet hc₁) hcv,
          hpre, hvlevel, hP⟩

/-- A `Q` witness contains a preleaf node satisfying property `P`. -/
theorem exists_preleaf_hasManyChildrenInPart_of_qProperty {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ : QProperty P u) :
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      ∃ hlevel : IsInternal v,
        IsPreleaf v ∧
          HasManyChildrenInPart P v hlevel (manyChildrenThreshold k) :=
  exists_preleaf_hasManyChildrenInPart_of_qPropertyAtFuel
    (bonnetDepresDepth k - u.1.val) u hQ

/-- A `Q` witness contains a descendant preleaf satisfying property `P`. -/
theorem exists_preleaf_descendant_hasManyChildrenInPart_of_qProperty {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ : QProperty P u) :
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      IsTreeAncestor u v ∧
        IsPreleaf v ∧
          ∃ hlevel : IsInternal v,
            HasManyChildrenInPart P v hlevel (manyChildrenThreshold k) :=
  exists_preleaf_descendant_hasManyChildrenInPart_of_qPropertyAtFuel
    (bonnetDepresDepth k - u.1.val) u hQ

/-- A singleton-bag partition cannot contain two children of the same parent in a
single part, hence cannot satisfy property `P` at threshold at least two. -/
theorem not_hasManyChildrenInPart_singletonBags {k m : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hm : 2 ≤ m) :
    ¬ HasManyChildrenInPart
      (TrigraphState.singletonBags (BonnetDepresVertex k)) u hlevel m := by
  classical
  rintro ⟨A, hA, hcard⟩
  rcases Finset.mem_image.mp hA with ⟨v, _hv, rfl⟩
  have hle :
      (({v} : Finset (BonnetDepresVertex k)) ∩ childVertexSet u hlevel).card ≤ 1 := by
    calc
      (({v} : Finset (BonnetDepresVertex k)) ∩ childVertexSet u hlevel).card
          ≤ ({v} : Finset (BonnetDepresVertex k)).card := by
        exact Finset.card_le_card (by intro z hz; exact (Finset.mem_inter.mp hz).1)
      _ = 1 := by simp
  omega

/-- No root child satisfies `Q` in the initial singleton-bag state. -/
theorem not_rootChildQAt_singletonBags {k : ℕ} :
    ¬ ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      QProperty (TrigraphState.singletonBags (BonnetDepresVertex k))
        (rootChildWithNeighborhood k f) := by
  rintro ⟨f, hQ⟩
  rcases exists_preleaf_hasManyChildrenInPart_of_qProperty hQ with
    ⟨v, hlevel, _hpre, hP⟩
  exact not_hasManyChildrenInPart_singletonBags (two_le_manyChildrenThreshold k) hP

/-- At a preleaf, property `P` immediately gives property `Q`. -/
theorem qProperty_of_hasManyChildrenInPart_preleaf {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hpre : IsPreleaf u)
    (hlevel : IsInternal u)
    (hP : HasManyChildrenInPart P u hlevel (manyChildrenThreshold k)) :
    QProperty P u := by
  unfold QProperty
  have hfuel : bonnetDepresDepth k - u.1.val = 1 := by
    unfold IsPreleaf at hpre
    omega
  rw [hfuel]
  left
  exact ⟨hpre, hlevel, hP⟩

/-- Membership in a child set gives the corresponding tree-parent relation. -/
theorem isParent_of_mem_childSet {k : ℕ}
    {u c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hc : c ∈ childSet u hlevel) :
    FullTreeNode.IsParent u c := by
  rcases mem_childSet.mp hc with ⟨label, rfl⟩
  exact FullTreeNode.isParent_child u hlevel label

/-- Non-preleaf constructor for property `Q`. -/
theorem qProperty_of_two_child_qProperties {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u c₁ c₂ : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hnonpreleaf : IsNonPreleafInternal u)
    (hc₁ : c₁ ∈ childSet u hlevel)
    (hc₂ : c₂ ∈ childSet u hlevel)
    (hcne : c₁ ≠ c₂)
    (hq₁ : QProperty P c₁)
    (hq₂ : QProperty P c₂) :
    QProperty P u := by
  unfold QProperty at hq₁ hq₂ ⊢
  have hnonpreleaf_raw : u.1.val + 1 < bonnetDepresDepth k := by
    simpa [IsNonPreleafInternal] using hnonpreleaf
  have hnotpre : ¬ IsPreleaf u := by
    intro hpre
    unfold IsPreleaf at hpre
    omega
  have hfuel :
      bonnetDepresDepth k - u.1.val =
        (bonnetDepresDepth k - (u.1.val + 1)) + 1 := by
    omega
  have hc₁level := level_eq_succ_of_mem_childSet hc₁
  have hc₂level := level_eq_succ_of_mem_childSet hc₂
  have hfuel₁ :
      bonnetDepresDepth k - c₁.1.val =
        bonnetDepresDepth k - (u.1.val + 1) := by
    rw [hc₁level]
  have hfuel₂ :
      bonnetDepresDepth k - c₂.1.val =
        bonnetDepresDepth k - (u.1.val + 1) := by
    rw [hc₂level]
  rw [hfuel]
  right
  refine ⟨hnotpre, hlevel, c₁, hc₁, c₂, hc₂, hcne, ?_, ?_⟩
  · simpa [hfuel₁] using hq₁
  · simpa [hfuel₂] using hq₂

/-- Non-preleaf destructor for property `Q`. -/
theorem exists_two_child_qProperties_of_qProperty_nonpreleaf {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hnonpreleaf : IsNonPreleafInternal u)
    (hQ : QProperty P u) :
    ∃ hlevel : IsInternal u,
      ∃ c₁ ∈ childSet u hlevel, ∃ c₂ ∈ childSet u hlevel,
        c₁ ≠ c₂ ∧ QProperty P c₁ ∧ QProperty P c₂ := by
  unfold QProperty at hQ
  have hnotpre : ¬ IsPreleaf u := by
    intro hpre
    unfold IsNonPreleafInternal at hnonpreleaf
    unfold IsPreleaf at hpre
    omega
  have hfuel :
      bonnetDepresDepth k - u.1.val =
        (bonnetDepresDepth k - (u.1.val + 1)) + 1 := by
    unfold IsNonPreleafInternal at hnonpreleaf
    omega
  rw [hfuel] at hQ
  rcases hQ with hpre | hchildren
  · exact (hnotpre hpre.1).elim
  · rcases hchildren with
      ⟨_hnotpre, hlevel, c₁, hc₁, c₂, hc₂, hcne, hq₁, hq₂⟩
    refine ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, ?_, ?_⟩
    · have hc₁level := level_eq_succ_of_mem_childSet hc₁
      simpa [QProperty, hc₁level] using hq₁
    · have hc₂level := level_eq_succ_of_mem_childSet hc₂
      simpa [QProperty, hc₂level] using hq₂

/-- The arithmetic gap used in the Claim-14 pigeonhole step. -/
theorem manyChildren_product_lt_branch_sub_one (k : ℕ) :
    (2 ^ k + 1) * (manyChildrenThreshold k - 1) <
      bonnetDepresBranch k - 1 := by
  have hfactor : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    rw [pow_succ]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  have hthreshold : manyChildrenThreshold k - 1 < 2 ^ (k + 1) := by
    unfold manyChildrenThreshold
    have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
    omega
  have hprod :
      (2 ^ k + 1) * (manyChildrenThreshold k - 1) <
        2 ^ (k + 1) * 2 ^ (k + 1) := by
    have hprod_le :
        (2 ^ k + 1) * (manyChildrenThreshold k - 1) ≤
          2 ^ (k + 1) * (manyChildrenThreshold k - 1) :=
      Nat.mul_le_mul_right _ hfactor
    have hprod_lt :
        2 ^ (k + 1) * (manyChildrenThreshold k - 1) <
          2 ^ (k + 1) * 2 ^ (k + 1) :=
      Nat.mul_lt_mul_of_pos_left hthreshold (Nat.two_pow_pos (k + 1))
    exact hprod_le.trans_lt hprod_lt
  have hpowmul :
      2 ^ (k + 1) * 2 ^ (k + 1) = 2 ^ (2 * k + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have htail :
      2 ^ (2 * k + 2) < bonnetDepresBranch k - 1 := by
    unfold bonnetDepresBranch bonnetDepresApexCount
    have hone : 1 < 2 ^ (2 * k + 2) := by
      have hpow : 2 ^ 0 < 2 ^ (2 * k + 2) := by
        apply Nat.pow_lt_pow_right
        · omega
        · omega
      simpa only [pow_zero] using hpow
    have hexp : 2 * k + 3 = 2 * k + 2 + 1 := by omega
    have htarget : 2 ^ (2 * k + 2) + 1 < 2 ^ (2 * k + 3) := by
      have hright : 2 ^ (2 * k + 3) = 2 ^ (2 * k + 2) * 2 := by
        rw [hexp, pow_succ]
      rw [hright, mul_two]
      omega
    exact Nat.lt_sub_iff_add_lt.mpr htarget
  have hprod' :
      (2 ^ k + 1) * (manyChildrenThreshold k - 1) <
        2 ^ (2 * k + 2) := by
    simpa [hpowmul] using hprod
  exact hprod'.trans htail

/-- If a bag contains two tree vertices `u,w`, and another bag contains a tree
vertex adjacent to `u` but not adjacent to `w`, then the two bags are
red-adjacent. -/
theorem partitionRedAdj_of_tree_edge_tree_nonedge {k : ℕ}
    {A B : Finset (BonnetDepresVertex k)}
    {u w c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hAB : A ≠ B)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hcB : (Sum.inr c : BonnetDepresVertex k) ∈ B)
    (huc :
      (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj u c)
    (hwc :
      ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c) :
    partitionRedAdj (bonnetDepresGraph k) A B := by
  refine ⟨hAB, ?_⟩
  intro hhom
  rcases hhom with hcomp | hemp
  · have hwcGraph :
        (bonnetDepresGraph k).Adj
          (Sum.inr w : BonnetDepresVertex k) (Sum.inr c) :=
      hcomp hwA hcB
    exact hwc (by simpa [bonnetDepresGraph] using hwcGraph)
  · have hucGraph :
        (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k) (Sum.inr c) := by
      simpa [bonnetDepresGraph] using huc
    exact hemp huA hcB hucGraph

/-- A child of `u` non-adjacent to another tree vertex `w` forces red adjacency
from a bag containing `u,w` to any different bag containing that child. -/
theorem partitionRedAdj_of_parent_child_nonadj_witness {k : ℕ}
    {A B : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k)
    {label : Fin (bonnetDepresBranch k)}
    (hAB : A ≠ B)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hcB :
      (Sum.inr (FullTreeNode.child u hlevel label) : BonnetDepresVertex k) ∈ B)
    (hwc :
      ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj
        w (FullTreeNode.child u hlevel label)) :
    partitionRedAdj (bonnetDepresGraph k) A B :=
  partitionRedAdj_of_tree_edge_tree_nonedge hAB huA hwA hcB
    (Or.inl (FullTreeNode.isParent_child u hlevel label)) hwc

/-- The bag `A` together with all red-neighbor bags of `A` in a partition. -/
noncomputable def redOrSelfBags {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (A : Finset (BonnetDepresVertex k)) :
    Finset (Finset (BonnetDepresVertex k)) := by
  classical
  exact insert A (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B)

/-- The union of the bag `A` and all its red-neighbor bags. -/
noncomputable def redOrSelfUnion {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (A : Finset (BonnetDepresVertex k)) :
    Finset (BonnetDepresVertex k) :=
  (redOrSelfBags P A).biUnion id

/-- Red-degree control bounds the number of bags in `redOrSelfBags`. -/
theorem card_redOrSelfBags_le {k d : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P) :
    (redOrSelfBags P A).card ≤ d + 1 := by
  classical
  have hneighbors :
      (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B).card ≤ d :=
    hred hA
  calc
    (redOrSelfBags P A).card
        ≤ (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B).card + 1 := by
          simpa [redOrSelfBags] using
            Finset.card_insert_le A
              (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B)
    _ ≤ d + 1 := by omega

/-- `redOrSelfBags` really is a subfamily of the ambient partition when `A` is
itself a part. -/
theorem redOrSelfBags_subset_partition {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hA : A ∈ P) :
    redOrSelfBags P A ⊆ P := by
  classical
  intro B hB
  rw [redOrSelfBags, Finset.mem_insert, Finset.mem_filter] at hB
  rcases hB with hBA | hB
  · simpa [hBA]
  · exact hB.1

/-- Non-adjacent children are, in particular, children of the parent. -/
theorem childNonAdjVertexSet_subset_childVertexSet {k : ℕ}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k) :
    childNonAdjVertexSet u w hlevel ⊆ childVertexSet u hlevel := by
  classical
  intro v hv
  have hv_sdiff :
      v ∈ childVertexSet u hlevel \
        (childAdjSet u w hlevel).image (Sum.inr : _ → BonnetDepresVertex k) := by
    simpa [childNonAdjVertexSet] using hv
  rw [Finset.mem_sdiff] at hv_sdiff
  exact hv_sdiff.1

/-- If every selected bag contains at most `m` relevant vertices, their union
contains at most `number of bags * m` relevant vertices. -/
theorem card_inter_redOrSelfUnion_le_mul {k m : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {X : Finset (BonnetDepresVertex k)}
    (hsmall : ∀ ⦃B⦄, B ∈ redOrSelfBags P A → (B ∩ X).card ≤ m) :
    (redOrSelfUnion P A ∩ X).card ≤ (redOrSelfBags P A).card * m := by
  classical
  rw [redOrSelfUnion, Finset.biUnion_inter]
  calc
    ((redOrSelfBags P A).biUnion fun B => B ∩ X).card
        ≤ ∑ B ∈ redOrSelfBags P A, (B ∩ X).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ B ∈ redOrSelfBags P A, m := by
      exact Finset.sum_le_sum fun B hB => hsmall hB
    _ = (redOrSelfBags P A).card * m := by
      simp [Finset.sum_const, Nat.mul_comm]

/-- Every non-adjacent child of `u` is in `A` or in a red-neighbor bag of `A`,
provided `A` contains both `u` and the witness tree vertex `w`. -/
theorem childNonAdjVertexSet_subset_redOrSelfUnion {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hpart : IsBagPartition P)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hlevel : u.1.val < bonnetDepresDepth k) :
    childNonAdjVertexSet u w hlevel ⊆ redOrSelfUnion P A := by
  classical
  intro v hv
  rw [redOrSelfUnion, Finset.mem_biUnion]
  have hv_child : v ∈ childVertexSet u hlevel := by
    have hv_sdiff :
        v ∈ childVertexSet u hlevel \
          (childAdjSet u w hlevel).image (Sum.inr : _ → BonnetDepresVertex k) := by
      simpa [childNonAdjVertexSet] using hv
    rw [Finset.mem_sdiff] at hv_sdiff
    exact hv_sdiff.1
  rw [childVertexSet, Finset.mem_image] at hv_child
  rcases hv_child with ⟨c, hc_child, rfl⟩
  have hnonadj :
      ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c :=
    (mem_childNonAdjVertexSet (k := k) (u := u) (w := w) (c := c) hlevel).mp hv |>.2
  rcases hpart.2.2 (Sum.inr c : BonnetDepresVertex k) with ⟨B, hB, hcB⟩
  by_cases hBA : B = A
  · refine ⟨A, ?_, ?_⟩
    · simp [redOrSelfBags]
    · simpa [hBA] using hcB
  · refine ⟨B, ?_, hcB⟩
    rw [redOrSelfBags, Finset.mem_insert, Finset.mem_filter]
    right
    refine ⟨hB, ?_⟩
    rcases mem_childSet.mp hc_child with ⟨label, rfl⟩
    exact partitionRedAdj_of_parent_child_nonadj_witness hlevel
      (by intro hAB; exact hBA hAB.symm) huA hwA hcB hnonadj

/-- Claim-14 core: under red-degree at most `2^k`, a part containing two
distinct tree vertices forces many children of the first one into a single part.

The proof follows the paper's counting argument.  A second tree vertex `w` in
the same part is non-adjacent to all but one child of `u`; every such child lies
either in the same part or in a red-neighbor part.  Since there are at most
`2^k + 1` such parts and the branching factor is much larger than
`(2^k + 1) * (2^(k+1)-1)`, one part contains at least `2^(k+1)` children. -/
theorem hasManyChildrenInPart_of_two_tree_vertices_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hwu : w ≠ u)
    (hlevel : u.1.val < bonnetDepresDepth k) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  by_contra hnot
  let X : Finset (BonnetDepresVertex k) := childNonAdjVertexSet u w hlevel
  have hthreshold_pos : 0 < manyChildrenThreshold k := by
    unfold manyChildrenThreshold
    exact Nat.two_pow_pos (k + 1)
  have hsmallP :
      ∀ ⦃B : Finset (BonnetDepresVertex k)⦄, B ∈ P →
        (B ∩ childVertexSet u hlevel).card ≤ manyChildrenThreshold k - 1 := by
    intro B hB
    have hlt : (B ∩ childVertexSet u hlevel).card < manyChildrenThreshold k := by
      exact Nat.lt_of_not_ge fun hlarge => hnot ⟨B, hB, hlarge⟩
    omega
  have hsmall :
      ∀ ⦃B : Finset (BonnetDepresVertex k)⦄, B ∈ redOrSelfBags P A →
        (B ∩ X).card ≤ manyChildrenThreshold k - 1 := by
    intro B hB
    have hBP : B ∈ P := redOrSelfBags_subset_partition hA hB
    have hchildSmall := hsmallP hBP
    have hsubset : B ∩ X ⊆ B ∩ childVertexSet u hlevel := by
      intro v hv
      rw [Finset.mem_inter] at hv ⊢
      exact ⟨hv.1, childNonAdjVertexSet_subset_childVertexSet hlevel hv.2⟩
    exact (Finset.card_le_card hsubset).trans hchildSmall
  have hcover : X ⊆ redOrSelfUnion P A := by
    simpa [X] using
      childNonAdjVertexSet_subset_redOrSelfUnion
        (P := P) (A := A) (u := u) (w := w) hpart huA hwA hlevel
  have hXeq : redOrSelfUnion P A ∩ X = X := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_inter] at hv
      exact hv.2
    · intro hv
      rw [Finset.mem_inter]
      exact ⟨hcover hv, hv⟩
  have hupper₁ :
      X.card ≤ (redOrSelfBags P A).card * (manyChildrenThreshold k - 1) := by
    rw [← hXeq]
    exact card_inter_redOrSelfUnion_le_mul hsmall
  have hupper₂ :
      X.card ≤ (d + 1) * (manyChildrenThreshold k - 1) := by
    exact hupper₁.trans
      (Nat.mul_le_mul_right _ (card_redOrSelfBags_le hred hA))
  have hupper :
      X.card ≤ (2 ^ k + 1) * (manyChildrenThreshold k - 1) := by
    exact hupper₂.trans (Nat.mul_le_mul_right _ (by omega))
  have hlower :
      bonnetDepresBranch k - 1 ≤ X.card := by
    simpa [X] using card_childNonAdjVertexSet_ge hlevel hwu
  have hgap := manyChildren_product_lt_branch_sub_one k
  omega

/-- If a different part contains many children of `u`, then a part containing
`u` and a distinct tree vertex `w` is red-adjacent to it. -/
theorem partitionRedAdj_of_many_children_and_two_tree_vertices
    {k : ℕ} {A C : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hAC : A ≠ C)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hwu : w ≠ u)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hmany : manyChildrenThreshold k ≤ (C ∩ childVertexSet u hlevel).card) :
    partitionRedAdj (bonnetDepresGraph k) A C := by
  classical
  have htwo : 2 ≤ (C ∩ childVertexSet u hlevel).card :=
    (two_le_manyChildrenThreshold k).trans hmany
  have hbadCard :
      ((childAdjSet u w hlevel).image
        (Sum.inr : _ → BonnetDepresVertex k)).card ≤ 1 := by
    rw [Finset.card_image_of_injective]
    · exact card_childAdjSet_le_one hlevel hwu
    · intro a b hab
      exact Sum.inr.inj hab
  have hexists :
      ∃ z,
        z ∈ C ∩ childVertexSet u hlevel ∧
          z ∉ (childAdjSet u w hlevel).image
            (Sum.inr : _ → BonnetDepresVertex k) := by
    by_contra hnone
    have hsubset :
        C ∩ childVertexSet u hlevel ⊆
          (childAdjSet u w hlevel).image
            (Sum.inr : _ → BonnetDepresVertex k) := by
      intro z hz
      by_contra hznot
      exact hnone ⟨z, hz, hznot⟩
    have hcard_le_one :
        (C ∩ childVertexSet u hlevel).card ≤ 1 :=
      (Finset.card_le_card hsubset).trans hbadCard
    omega
  rcases hexists with ⟨z, hz, hznotAdjImage⟩
  rw [Finset.mem_inter] at hz
  rw [childVertexSet, Finset.mem_image] at hz
  rcases hz.2 with ⟨c, hc_child, rfl⟩
  have hnonadj :
      ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj
        w c := by
    intro hadj
    have hcAdj : c ∈ childAdjSet u w hlevel := by
      rw [childAdjSet, Finset.mem_filter]
      exact ⟨hc_child, hadj⟩
    exact hznotAdjImage (by
      rw [Finset.mem_image]
      exact ⟨c, hcAdj, rfl⟩)
  rcases mem_childSet.mp hc_child with ⟨label, rfl⟩
  exact partitionRedAdj_of_parent_child_nonadj_witness
    hlevel hAC huA hwA hz.1 hnonadj

/-- If one bag contains strict descendants of two incomparable side branches
and another bag contains the parent of one selected descendant, then the two
bags are red-adjacent. -/
theorem partitionRedAdj_of_antichain_descendant_parent_parts
    {k : ℕ} {B C : Finset (BonnetDepresVertex k)}
    {a b za zb p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hBC : B ≠ C)
    (hanti : ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (haza : IsTreeAncestor a za)
    (hbzb : IsTreeAncestor b zb)
    (hpza : FullTreeNode.IsParent p za)
    (ha_strict : a.1.val < za.1.val)
    (hzaB : (Sum.inr za : BonnetDepresVertex k) ∈ B)
    (hzbB : (Sum.inr zb : BonnetDepresVertex k) ∈ B)
    (hpC : (Sum.inr p : BonnetDepresVertex k) ∈ C) :
    partitionRedAdj (bonnetDepresGraph k) C B := by
  apply partitionRedAdj_symm
  refine partitionRedAdj_of_tree_edge_tree_nonedge
    (k := k) (A := B) (B := C) (u := za) (w := zb) (c := p)
    hBC hzaB hzbB hpC ?_ ?_
  · exact Or.inr hpza
  · intro hAdj
    exact not_tree_adj_parent_descendant_of_antichain
      hanti haza hbzb hpza ha_strict
      ((FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).symm hAdj)

/-- Family form of the previous red-adjacency lemma: when `B` contains selected
descendants of more than one branch in an antichain, the part containing the
parent of any strict selected descendant is red-adjacent to `B`. -/
theorem partitionRedAdj_of_antichain_family_parent_part
    {k : ℕ}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B C : Finset (BonnetDepresVertex k)}
    {a p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (haR : a ∈ R)
    (hRcard : 1 < R.card)
    (hanti :
      ∀ ⦃x⦄, x ∈ R → ∀ ⦃y⦄, y ∈ R → x ≠ y →
        ¬ IsTreeAncestor x y ∧ ¬ IsTreeAncestor y x)
    (zOf :
      ∀ r : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        r ∈ R → FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hdesc :
      ∀ r hr, IsTreeAncestor r (zOf r hr))
    (hBz :
      ∀ r hr, (Sum.inr (zOf r hr) : BonnetDepresVertex k) ∈ B)
    (hpza : FullTreeNode.IsParent p (zOf a haR))
    (ha_strict : a.1.val < (zOf a haR).1.val)
    (hBC : B ≠ C)
    (hpC : (Sum.inr p : BonnetDepresVertex k) ∈ C) :
    partitionRedAdj (bonnetDepresGraph k) C B := by
  classical
  rcases Finset.one_lt_card.mp hRcard with ⟨x, hx, y, hy, hxy⟩
  obtain ⟨b, hbR, hba⟩ : ∃ b ∈ R, b ≠ a := by
    by_cases hxa : x = a
    · exact ⟨y, hy, by
        intro hya
        exact hxy (hxa.trans hya.symm)⟩
    · exact ⟨x, hx, hxa⟩
  exact partitionRedAdj_of_antichain_descendant_parent_parts
    (k := k) (B := B) (C := C) (a := a) (b := b)
    (za := zOf a haR) (zb := zOf b hbR) (p := p)
    hBC (hanti haR hbR (fun hab => hba hab.symm)) (hdesc a haR) (hdesc b hbR)
    hpza ha_strict (hBz a haR) (hBz b hbR) hpC

/-- Ranked family form of the red-adjacency step.  Unlike
`partitionRedAdj_of_antichain_family_parent_part`, this version does not assume
that the selected descendant of `a` is strict; the pairwise level distinction
rules out the sibling obstruction in that boundary case. -/
theorem partitionRedAdj_of_ranked_antichain_family_parent_part
    {k : ℕ}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B C : Finset (BonnetDepresVertex k)}
    {a p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (haR : a ∈ R)
    (hRcard : 1 < R.card)
    (hanti :
      ∀ ⦃x⦄, x ∈ R → ∀ ⦃y⦄, y ∈ R → x ≠ y →
        ¬ IsTreeAncestor x y ∧ ¬ IsTreeAncestor y x)
    (hlevel_ne :
      ∀ ⦃x⦄, x ∈ R → ∀ ⦃y⦄, y ∈ R → x ≠ y → x.1.val ≠ y.1.val)
    (zOf :
      ∀ r : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        r ∈ R → FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hdesc :
      ∀ r hr, IsTreeAncestor r (zOf r hr))
    (hBz :
      ∀ r hr, (Sum.inr (zOf r hr) : BonnetDepresVertex k) ∈ B)
    (hpza : FullTreeNode.IsParent p (zOf a haR))
    (hBC : B ≠ C)
    (hpC : (Sum.inr p : BonnetDepresVertex k) ∈ C) :
    partitionRedAdj (bonnetDepresGraph k) C B := by
  classical
  rcases Finset.one_lt_card.mp hRcard with ⟨x, hx, y, hy, hxy⟩
  obtain ⟨b, hbR, hba⟩ : ∃ b ∈ R, b ≠ a := by
    by_cases hxa : x = a
    · exact ⟨y, hy, by
        intro hya
        exact hxy (hxa.trans hya.symm)⟩
    · exact ⟨x, hx, hxa⟩
  apply partitionRedAdj_symm
  refine partitionRedAdj_of_tree_edge_tree_nonedge
    (k := k) (A := B) (B := C) (u := zOf a haR) (w := zOf b hbR) (c := p)
    hBC (hBz a haR) (hBz b hbR) hpC ?_ ?_
  · exact Or.inr hpza
  · intro hAdj
    exact not_tree_adj_parent_descendant_of_ranked_antichain
      (hanti haR hbR (fun hab => hba hab.symm))
      (hlevel_ne haR hbR (fun hab => hba hab.symm))
      (hdesc a haR) (hdesc b hbR) hpza
      ((FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).symm hAdj)

/-- A child whose label separates two apex vertices is red-adjacent to any bag
containing both apices. -/
theorem partitionRedAdj_of_apex_pair_child_disagree {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : parent.1.val < bonnetDepresDepth k)
    {label : Fin (bonnetDepresBranch k)}
    {x y : Fin (bonnetDepresApexCount k)}
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A)
    (hx : label.val.testBit x.val = true)
    (hy : label.val.testBit y.val = false) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (FullTreeNode.child parent hlevel label)} := by
  classical
  refine ⟨?_, ?_⟩
  · intro hAeq
    simp [hAeq] at hxA
  · intro hhom
    rcases hhom with hcomp | hemp
    · have hyAdj :
        (bonnetDepresGraph k).Adj
          (Sum.inl y : BonnetDepresVertex k)
          (Sum.inr (FullTreeNode.child parent hlevel label)) :=
        hcomp hyA (by simp)
      have hyAdj' :
          bonnetDepresApexAdj y
            (FullTreeNode.child parent hlevel label) := by
        simpa [bonnetDepresGraph] using hyAdj
      rw [bonnetDepresApexAdj_child y parent hlevel label] at hyAdj'
      simp [hy] at hyAdj'
    · have hxAdj :
          bonnetDepresApexAdj x
            (FullTreeNode.child parent hlevel label) := by
        rw [bonnetDepresApexAdj_child x parent hlevel label]
        exact hx
      have hxGraph :
          (bonnetDepresGraph k).Adj
            (Sum.inl x : BonnetDepresVertex k)
            (Sum.inr (FullTreeNode.child parent hlevel label)) := by
        simpa [bonnetDepresGraph] using hxAdj
      exact hemp hxA (by simp) hxGraph

/-- A prescribed apex-neighborhood child separating two apex vertices is
red-adjacent to any bag containing both apices. -/
theorem partitionRedAdj_of_apex_pair_child_neighborhood_disagree {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : parent.1.val < bonnetDepresDepth k)
    {x y : Fin (bonnetDepresApexCount k)}
    {f : Fin (bonnetDepresApexCount k) → Bool}
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A)
    (hx : f x = true) (hy : f y = false) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (FullTreeNode.child parent hlevel (labelOfNeighborhood f))} := by
  exact partitionRedAdj_of_apex_pair_child_disagree
    (k := k) (A := A) (parent := parent) hlevel hxA hyA
    (by simp [hx]) (by simp [hy])

/-- Every root child separating two apex vertices is red-adjacent to a bag that
contains both apices. -/
theorem partitionRedAdj_of_apex_pair_separatingRootChild {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {x y : Fin (bonnetDepresApexCount k)}
    (f : SeparatingApexBits x y)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (rootChildWithNeighborhood k f.1)} := by
  simpa [rootChildWithNeighborhood] using
    partitionRedAdj_of_apex_pair_child_neighborhood_disagree
      (k := k) (A := A)
      (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
      (root_level_lt_depth k)
      (x := x) (y := y) (f := f.1) hxA hyA f.2.1 f.2.2

/-- If all root children separating two apices remain singleton bags in a
partition, then a bag containing both apices has at least `2^(|X|-2)` red
neighbors. -/
theorem pow_apexCount_sub_two_le_of_apex_pair_redDegreeAtMost
    {k : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x y : Fin (bonnetDepresApexCount k)}
    {d : ℕ}
    (hxy : x ≠ y)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : SeparatingApexBits x y,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A) :
    2 ^ (bonnetDepresApexCount k - 2) ≤ d := by
  classical
  have hsubset :
      separatingRootChildBags x y ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rw [separatingRootChildBags, Finset.mem_image] at hB
    rcases hB with ⟨f, _hf, rfl⟩
    simp [hchildren f,
      partitionRedAdj_of_apex_pair_separatingRootChild f hxA hyA]
  have hcard := Finset.card_le_card hsubset
  rw [card_separatingRootChildBags hxy] at hcard
  exact hcard.trans (hred hA)

/-- In the specialized construction, the root-child family separating two
apices is already larger than `2^k`. -/
theorem pow_k_lt_pow_apexCount_sub_two (k : ℕ) :
    2 ^ k < 2 ^ (bonnetDepresApexCount k - 2) := by
  apply Nat.pow_lt_pow_right
  · omega
  · unfold bonnetDepresApexCount
    omega

/-- The half-root-child family is also larger than `2^k`. -/
theorem pow_k_lt_pow_apexCount_sub_one (k : ℕ) :
    2 ^ k < 2 ^ (bonnetDepresApexCount k - 1) := by
  apply Nat.pow_lt_pow_right
  · omega
  · unfold bonnetDepresApexCount
    omega

/-- Even after deleting one root child from a half-family, the remaining family
is larger than `2^k`. -/
theorem pow_k_lt_pow_apexCount_sub_one_sub_one (k : ℕ) :
    2 ^ k < 2 ^ (bonnetDepresApexCount k - 1) - 1 := by
  have hstep : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    rw [pow_succ]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  have hpow : 2 ^ (k + 1) < 2 ^ (bonnetDepresApexCount k - 1) := by
    apply Nat.pow_lt_pow_right
    · omega
    · unfold bonnetDepresApexCount
      omega
  omega

/-- Claim-11 core: while all root children remain singleton bags, no
`2^k`-bounded partition can have a bag containing two distinct apex vertices. -/
theorem false_of_apex_pair_of_root_children_singleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x y : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hxy : x ≠ y)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : SeparatingApexBits x y,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A) :
    False := by
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 2) ≤ d :=
    pow_apexCount_sub_two_le_of_apex_pair_redDegreeAtMost
      hxy hred hA hchildren hxA hyA
  have hlt := pow_k_lt_pow_apexCount_sub_two k
  omega

/-- A streamlined form of the Claim-11 core using the named
`RootChildrenSingleton` condition. -/
theorem false_of_apex_pair_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x y : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hxy : x ≠ y)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A) :
    False :=
  false_of_apex_pair_of_root_children_singleton_of_redDegreeAtMost
    hd hxy hred hA (fun f => hroot f.1) hxA hyA

/-- If a bag contains an apex vertex and a tree vertex, then any child whose
apex-neighborhood disagrees with the tree vertex on that apex witnesses
non-homogeneity. -/
theorem partitionRedAdj_of_apex_tree_child_disagree {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : parent.1.val < bonnetDepresDepth k)
    {label : Fin (bonnetDepresBranch k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hlabel : label.val.testBit x.val = true)
    (hu :
      ¬ (bonnetDepresGraph k).Adj
        (Sum.inr u : BonnetDepresVertex k)
        (Sum.inr (FullTreeNode.child parent hlevel label))) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (FullTreeNode.child parent hlevel label)} := by
  classical
  refine ⟨?_, ?_⟩
  · intro hAeq
    simp [hAeq] at hxA
  · intro hhom
    rcases hhom with hcomp | hemp
    · have huAdj :
        (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (FullTreeNode.child parent hlevel label)) :=
        hcomp huA (by simp)
      exact hu huAdj
    · have hxAdj :
          bonnetDepresApexAdj x
            (FullTreeNode.child parent hlevel label) := by
        rw [bonnetDepresApexAdj_child x parent hlevel label]
        exact hlabel
      have hxGraph :
          (bonnetDepresGraph k).Adj
            (Sum.inl x : BonnetDepresVertex k)
            (Sum.inr (FullTreeNode.child parent hlevel label)) := by
        simpa [bonnetDepresGraph] using hxAdj
      exact hemp hxA (by simp) hxGraph

/-- The complementary mixed apex/tree witness: if the tree vertex is adjacent
to a child while the apex is not, the two bags are non-homogeneous. -/
theorem partitionRedAdj_of_tree_apex_child_disagree {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : parent.1.val < bonnetDepresDepth k)
    {label : Fin (bonnetDepresBranch k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hlabel : label.val.testBit x.val = false)
    (hu :
      (bonnetDepresGraph k).Adj
        (Sum.inr u : BonnetDepresVertex k)
        (Sum.inr (FullTreeNode.child parent hlevel label))) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (FullTreeNode.child parent hlevel label)} := by
  classical
  refine ⟨?_, ?_⟩
  · intro hAeq
    simp [hAeq] at hxA
  · intro hhom
    have hxNotAdj :
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inl x : BonnetDepresVertex k)
          (Sum.inr (FullTreeNode.child parent hlevel label)) := by
      intro hxGraph
      have hxAdj :
          bonnetDepresApexAdj x
            (FullTreeNode.child parent hlevel label) := by
        simpa [bonnetDepresGraph] using hxGraph
      rw [bonnetDepresApexAdj_child x parent hlevel label] at hxAdj
      simp [hlabel] at hxAdj
    rcases hhom with hcomp | hemp
    · exact hxNotAdj (hcomp hxA (by simp))
    · exact hemp huA (by simp) hu

/-- If all root children with `x`-bit `true` are singleton bags and all of
them are non-adjacent to a tree vertex in `A`, then `A` has at least half of
the root children as red neighbors. -/
theorem pow_apexCount_sub_one_le_of_apex_tree_nonadj_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x true,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hnotAdj :
      ∀ f : ApexBitFiber x true,
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)))
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    2 ^ (bonnetDepresApexCount k - 1) ≤ d := by
  classical
  have hsubset :
      apexBitRootChildBags x true ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rw [apexBitRootChildBags, Finset.mem_image] at hB
    rcases hB with ⟨f, _hf, rfl⟩
    have hredChild :
        partitionRedAdj (bonnetDepresGraph k) A
          {Sum.inr (rootChildWithNeighborhood k f.1)} := by
      simpa [rootChildWithNeighborhood] using
        partitionRedAdj_of_apex_tree_child_disagree
          (k := k) (A := A)
          (u := u)
          (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
          (root_level_lt_depth k)
          (label := labelOfNeighborhood f.1)
          (x := x) hxA huA (by simpa using f.2) (by simpa [rootChildWithNeighborhood] using hnotAdj f)
    simp [hchildren f, hredChild]
  have hcard := Finset.card_le_card hsubset
  rw [card_apexBitRootChildBags x true] at hcard
  exact hcard.trans (hred hA)

/-- The dual half-root-child bound, when the tree vertex is adjacent to every
root child with `x`-bit `false`. -/
theorem pow_apexCount_sub_one_le_of_apex_tree_adj_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x false,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hadj :
      ∀ f : ApexBitFiber x false,
        (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)))
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    2 ^ (bonnetDepresApexCount k - 1) ≤ d := by
  classical
  have hsubset :
      apexBitRootChildBags x false ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rw [apexBitRootChildBags, Finset.mem_image] at hB
    rcases hB with ⟨f, _hf, rfl⟩
    have hredChild :
        partitionRedAdj (bonnetDepresGraph k) A
          {Sum.inr (rootChildWithNeighborhood k f.1)} := by
      simpa [rootChildWithNeighborhood] using
        partitionRedAdj_of_tree_apex_child_disagree
          (k := k) (A := A)
          (u := u)
          (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
          (root_level_lt_depth k)
          (label := labelOfNeighborhood f.1)
          (x := x) hxA huA (by simpa using f.2) (by simpa [rootChildWithNeighborhood] using hadj f)
    simp [hchildren f, hredChild]
  have hcard := Finset.card_le_card hsubset
  rw [card_apexBitRootChildBags x false] at hcard
  exact hcard.trans (hred hA)

/-- Contradiction form of the non-adjacent half-root-child bound. -/
theorem false_of_apex_tree_nonadj_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x true,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hnotAdj :
      ∀ f : ApexBitFiber x true,
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)))
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False := by
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 1) ≤ d :=
    pow_apexCount_sub_one_le_of_apex_tree_nonadj_redDegreeAtMost
      hred hA hchildren hnotAdj hxA huA
  have hlt := pow_k_lt_pow_apexCount_sub_one k
  omega

/-- Contradiction form of the adjacent half-root-child bound. -/
theorem false_of_apex_tree_adj_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x false,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hadj :
      ∀ f : ApexBitFiber x false,
        (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)))
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False := by
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 1) ≤ d :=
    pow_apexCount_sub_one_le_of_apex_tree_adj_redDegreeAtMost
      hred hA hchildren hadj hxA huA
  have hlt := pow_k_lt_pow_apexCount_sub_one k
  omega

/-- If a bag contains an apex and a root child, and all other root children with
that apex bit remain singleton bags, then the bag has too many red neighbors. -/
theorem false_of_apex_rootChild_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    {f₀ : Fin (bonnetDepresApexCount k) → Bool}
    (hd : d ≤ 2 ^ k)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x true,
        rootChildBag k f.1 ≠ rootChildBag k f₀ →
          rootChildBag k f.1 ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr (rootChildWithNeighborhood k f₀) : BonnetDepresVertex k) ∈ A) :
    False := by
  classical
  have hsubset :
      (apexBitRootChildBags x true).erase (rootChildBag k f₀) ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rcases Finset.mem_erase.mp hB with ⟨hBne, hBmem⟩
    rw [apexBitRootChildBags, Finset.mem_image] at hBmem
    rcases hBmem with ⟨f, _hf, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨hchildren f hBne, ?_⟩
    have hnotAdj :
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inr (rootChildWithNeighborhood k f₀) : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)) := by
      have hzero : (rootChildWithNeighborhood k f₀).1.val ≠ 0 := by
        simp
      have htwo : (rootChildWithNeighborhood k f₀).1.val ≠ 2 := by
        simp
      exact not_adj_rootChildWithNeighborhood_of_level_ne_zero_ne_two
        k hzero htwo f.1
    simpa [rootChildBag, rootChildWithNeighborhood] using
      partitionRedAdj_of_apex_tree_child_disagree
        (k := k) (A := A)
        (u := rootChildWithNeighborhood k f₀)
        (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
        (root_level_lt_depth k)
        (label := labelOfNeighborhood f.1)
        (x := x) hxA huA (by simpa using f.2) hnotAdj
  have hcard_subset := Finset.card_le_card hsubset
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 1) - 1 ≤ d := by
    calc
      2 ^ (bonnetDepresApexCount k - 1) - 1
          ≤ ((apexBitRootChildBags x true).erase (rootChildBag k f₀)).card := by
            simpa [card_apexBitRootChildBags x true] using
              (Finset.pred_card_le_card_erase
                (s := apexBitRootChildBags x true) (a := rootChildBag k f₀))
      _ ≤ (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B).card :=
            hcard_subset
      _ ≤ d := hred hA
  have hlt := pow_k_lt_pow_apexCount_sub_one_sub_one k
  omega

/-- A contraction that merges a root-child singleton bag with a bag containing
an apex immediately violates the red-degree bound. -/
theorem false_of_merge_rootChildBag_with_apex
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    {f₀ : Fin (bonnetDepresApexCount k) → Bool}
    (hd : d ≤ 2 ^ k)
    (hrootP : RootChildrenSingleton P)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hxB : (Sum.inl x : BonnetDepresVertex k) ∈ B)
    (hQ :
      Q = insert (rootChildBag k f₀ ∪ B)
        ((P.erase (rootChildBag k f₀)).erase B)) :
    False := by
  classical
  let A : Finset (BonnetDepresVertex k) := rootChildBag k f₀ ∪ B
  have hA : A ∈ Q := by
    rw [hQ]
    exact Finset.mem_insert_self _ _
  have hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A := by
    simp [A, hxB]
  have huA :
      (Sum.inr (rootChildWithNeighborhood k f₀) : BonnetDepresVertex k) ∈ A := by
    simp [A, rootChildBag]
  have hchildren :
      ∀ f : ApexBitFiber x true,
        rootChildBag k f.1 ≠ rootChildBag k f₀ →
          rootChildBag k f.1 ∈ Q := by
    intro f hfne
    rw [hQ, mem_merge_family_iff]
    right
    refine ⟨(rootChildrenSingleton_iff.mp hrootP) f.1, hfne, ?_⟩
    intro hEq
    have hxRoot : (Sum.inl x : BonnetDepresVertex k) ∈ rootChildBag k f.1 := by
      simpa [hEq] using hxB
    simp [rootChildBag] at hxRoot
  exact false_of_apex_rootChild_of_redDegreeAtMost
    (k := k) (d := d) (P := Q) (A := A) (x := x) (f₀ := f₀)
    hd hredQ hA hchildren hxA huA

/-- Symmetric version of `false_of_merge_rootChildBag_with_apex`. -/
theorem false_of_merge_apex_with_rootChildBag
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    {f₀ : Fin (bonnetDepresApexCount k) → Bool}
    (hd : d ≤ 2 ^ k)
    (hrootP : RootChildrenSingleton P)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hxB : (Sum.inl x : BonnetDepresVertex k) ∈ B)
    (hQ :
      Q = insert (B ∪ rootChildBag k f₀)
        ((P.erase B).erase (rootChildBag k f₀))) :
    False := by
  classical
  have hQ' :
      Q = insert (rootChildBag k f₀ ∪ B)
        ((P.erase (rootChildBag k f₀)).erase B) := by
    rw [hQ, Finset.union_comm]
    congr 1
    ext C
    by_cases hCr : C = rootChildBag k f₀
    · subst C
      by_cases hBr : B = rootChildBag k f₀
      · subst B
        simp
      · simp
    · by_cases hCB : C = B
      · subst C
        simp [hCr]
      · simp [hCr, hCB]
  exact false_of_merge_rootChildBag_with_apex
    (k := k) (d := d) (P := P) (Q := Q) (B := B) (x := x) (f₀ := f₀)
    hd hrootP hredQ hxB hQ'

/-- If `u` is a grandchild of the root, then among root children with `x`-bit
`true`, all but possibly the parent of `u` are non-adjacent to `u`.  Thus a bag
containing both `x` and `u` has at least `2^(|X|-1)-1` red neighbors. -/
theorem pow_apexCount_sub_one_sub_one_le_of_apex_grandchild_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hlevel : u.1.val = 2)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    2 ^ (bonnetDepresApexCount k - 1) - 1 ≤ d := by
  classical
  let hpos : 0 < u.1.val := by omega
  let parentBag : Finset (BonnetDepresVertex k) :=
    {Sum.inr (FullTreeNode.parent u hpos)}
  have hsubset :
      (apexBitRootChildBags x true).erase parentBag ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rcases Finset.mem_erase.mp hB with ⟨hBne, hBmem⟩
    rw [apexBitRootChildBags, Finset.mem_image] at hBmem
    rcases hBmem with ⟨f, _hf, rfl⟩
    have hnotAdj :
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)) := by
      intro hadj
      have htree :
          (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj
            u (rootChildWithNeighborhood k f.1) := by
        simpa [bonnetDepresGraph] using hadj
      have hroot_le : (rootChildWithNeighborhood k f.1).1.val ≤ u.1.val := by
        rw [rootChildWithNeighborhood_level, hlevel]
        omega
      have hparent :
          FullTreeNode.IsParent (rootChildWithNeighborhood k f.1) u :=
        FullTreeNode.isParent_of_adj_of_level_le htree hroot_le
      have hparent_eq :
          rootChildWithNeighborhood k f.1 = FullTreeNode.parent u hpos :=
        FullTreeNode.isParent_unique hparent
          (FullTreeNode.parent_isParent u hpos)
      exact hBne (by simp [parentBag, hparent_eq])
    have hredChild :
        partitionRedAdj (bonnetDepresGraph k) A
          {Sum.inr (rootChildWithNeighborhood k f.1)} := by
      simpa [rootChildWithNeighborhood] using
        partitionRedAdj_of_apex_tree_child_disagree
          (k := k) (A := A)
          (u := u)
          (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
          (root_level_lt_depth k)
          (label := labelOfNeighborhood f.1)
          (x := x) hxA huA (by simpa using f.2)
          (by simpa [rootChildWithNeighborhood] using hnotAdj)
    simp [hroot f.1, hredChild]
  have hcard := Finset.card_le_card hsubset
  have hpred :
      2 ^ (bonnetDepresApexCount k - 1) - 1 ≤
        ((apexBitRootChildBags x true).erase parentBag).card := by
    rw [← card_apexBitRootChildBags x true]
    exact Finset.pred_card_le_card_erase
  exact hpred.trans (hcard.trans (hred hA))

/-- Claim-12 grandchild case: before root children are contracted, a
`2^k`-bounded partition cannot mix an apex with a level-`2` tree vertex. -/
theorem false_of_apex_grandchild_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hlevel : u.1.val = 2)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False := by
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 1) - 1 ≤ d :=
    pow_apexCount_sub_one_sub_one_le_of_apex_grandchild_redDegreeAtMost
      hlevel hroot hred hA hxA huA
  have hlt := pow_k_lt_pow_apexCount_sub_one_sub_one k
  omega

/-- Claim-12 root case: before root children are contracted, a `2^k`-bounded
partition cannot have a bag containing an apex and the tree root. -/
theorem false_of_apex_root_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hrootA :
      (Sum.inr (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k)) :
        BonnetDepresVertex k) ∈ A) :
    False :=
  false_of_apex_tree_adj_of_redDegreeAtMost
    (k := k) (d := d) (P := P) (A := A)
    (u := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
    (x := x) hd hred hA (fun f => hroot f.1)
    (fun f => root_adj_rootChildWithNeighborhood k f.1) hxA hrootA

/-- Claim-12 non-root/non-grandchild case: before root children are contracted,
a `2^k`-bounded partition cannot mix an apex with a tree vertex whose level is
neither `0` nor `2`. -/
theorem false_of_apex_tree_level_ne_zero_ne_two_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hzero : u.1.val ≠ 0) (htwo : u.1.val ≠ 2)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False :=
  false_of_apex_tree_nonadj_of_redDegreeAtMost
    (k := k) (d := d) (P := P) (A := A) (u := u) (x := x)
    hd hred hA (fun f => hroot f.1)
    (fun f => not_adj_rootChildWithNeighborhood_of_level_ne_zero_ne_two
      k hzero htwo f.1)
    hxA huA

/-- Claim 12 in consolidated form: before any root child is contracted, a
`2^k`-bounded partition has no part meeting both the apex set and the tree
side. -/
theorem false_of_apex_tree_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False := by
  by_cases hzero : u.1.val = 0
  · have hu :
        u = FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k) :=
      FullTreeNode.eq_root_of_level_zero hzero
    subst u
    exact false_of_apex_root_of_rootChildrenSingleton_of_redDegreeAtMost
      hd hroot hred hA hxA huA
  · by_cases hone : u.1.val = 1
    · rcases exists_rootChildWithNeighborhood_eq_of_level_one k hone with ⟨f, hf⟩
      have hsingleton :
          ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ P := by
        rw [← hf]
        exact hroot f
      by_cases hAeq : A = ({Sum.inr u} : Finset (BonnetDepresVertex k))
      · subst A
        simp at hxA
      · exact (Finset.disjoint_left.mp (hpart.2.1 hA hsingleton hAeq))
          huA (by simp)
    · by_cases htwo : u.1.val = 2
      · exact false_of_apex_grandchild_of_rootChildrenSingleton_of_redDegreeAtMost
          hd htwo hroot hred hA hxA huA
      · exact false_of_apex_tree_level_ne_zero_ne_two_of_rootChildrenSingleton_of_redDegreeAtMost
          hd hzero htwo hroot hred hA hxA huA

/-- Claim 13: in the same initial segment, every part meeting the apex set is
an apex singleton. -/
theorem eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A) :
    A = {Sum.inl x} := by
  classical
  ext z
  constructor
  · intro hzA
    cases z with
    | inl y =>
        by_cases hyx : y = x
        · subst y
          simp
        · exfalso
          exact false_of_apex_pair_of_rootChildrenSingleton_of_redDegreeAtMost
            (k := k) (d := d) (P := P) (A := A)
            (x := x) (y := y) hd (fun hxy => hyx hxy.symm)
            hroot hred hA hxA hzA
    | inr u =>
        exfalso
        exact false_of_apex_tree_of_rootChildrenSingleton_of_redDegreeAtMost
          (k := k) (d := d) (P := P) (A := A) (u := u) (x := x)
          hd hpart hroot hred hA hxA hzA
  · intro hz
    rw [Finset.mem_singleton] at hz
    subst z
    exact hxA

/-- Claim 13 specialized to an actual contraction-sequence state. -/
theorem ContractionSequence.eq_singleton_of_apex_mem_of_rootChildrenSingleton
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i ≤ S.stepCount)
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton (S.state i).bags)
    (hA : A ∈ (S.state i).bags)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A) :
    A = {Sum.inl x} :=
  eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
    (k := k) (d := d) (P := (S.state i).bags) (A := A) (x := x)
    hd (Lax1Proofs.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot (Lax1Proofs.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state S hi)
    hA hxA

/-- During the protected initial segment, every apex vertex is represented by its
singleton bag. -/
theorem apexSingleton_mem_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (x : Fin (bonnetDepresApexCount k)) :
    ({Sum.inl x} : Finset (BonnetDepresVertex k)) ∈ P := by
  classical
  rcases hpart.2.2 (Sum.inl x : BonnetDepresVertex k) with ⟨A, hA, hxA⟩
  have hAeq :
      A = ({Sum.inl x} : Finset (BonnetDepresVertex k)) :=
    eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
      (k := k) (d := d) (P := P) (A := A) (x := x)
      hd hpart hroot hred hA hxA
  simpa [hAeq] using hA

/-- Singleton apex bags are injectively indexed by the apex vertex. -/
theorem apexSingletonBag_injective (k : ℕ) :
    Function.Injective
      (fun x : Fin (bonnetDepresApexCount k) =>
        ({Sum.inl x} : Finset (BonnetDepresVertex k))) := by
  intro x y hxy
  exact Sum.inl.inj (Finset.singleton_inj.mp hxy)

/-- If a bag contains a set of tree vertices, then every apex coordinate on which
that set varies gives a red-neighbor apex singleton bag. -/
theorem childApexVariationSet_card_le_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hSA :
      ∀ ⦃c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)⦄,
        c ∈ S → (Sum.inr c : BonnetDepresVertex k) ∈ A) :
    (childApexVariationSet S).card ≤ d := by
  classical
  let apexBag : Fin (bonnetDepresApexCount k) → Finset (BonnetDepresVertex k) :=
    fun x => {Sum.inl x}
  let redApexBags : Finset (Finset (BonnetDepresVertex k)) :=
    (childApexVariationSet S).image apexBag
  let redNeighbors : Finset (Finset (BonnetDepresVertex k)) :=
    P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B
  have hsubset : redApexBags ⊆ redNeighbors := by
    intro B hB
    change B ∈ (childApexVariationSet S).image apexBag at hB
    rw [Finset.mem_image] at hB
    rcases hB with ⟨x, hxvar, rfl⟩
    change apexBag x ∈ P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B
    rw [Finset.mem_filter]
    refine ⟨apexSingleton_mem_of_rootChildrenSingleton_of_redDegreeAtMost
      (k := k) (d := d) (P := P) hd hpart hroot hred x, ?_⟩
    rw [childApexVariationSet, Finset.mem_filter] at hxvar
    rcases hxvar.2 with ⟨c₁, hc₁, c₂, hc₂, hdisagree | hdisagree⟩
    · exact partitionRedAdj_of_apexAdj_disagree_in_bag
        (hSA hc₁) (hSA hc₂) hdisagree.1 hdisagree.2
    · exact partitionRedAdj_of_apexAdj_disagree_in_bag
        (hSA hc₂) (hSA hc₁) hdisagree.1 hdisagree.2
  have hcard_image :
      redApexBags.card = (childApexVariationSet S).card := by
    change ((childApexVariationSet S).image apexBag).card =
      (childApexVariationSet S).card
    rw [Finset.card_image_of_injective]
    exact apexSingletonBag_injective k
  calc
    (childApexVariationSet S).card = redApexBags.card := hcard_image.symm
    _ ≤ redNeighbors.card := Finset.card_le_card hsubset
    _ ≤ d := hred hA

/-- For a fixed apex singleton, red-degree control bounds how many large bags are
red-adjacent to it. -/
theorem card_largeChildBags_redAdjacent_to_apex_le {k d : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (x : Fin (bonnetDepresApexCount k)) :
    (largeChildBagsRedAdjacentToApex P x).card ≤ d := by
  classical
  let X : Finset (BonnetDepresVertex k) := {Sum.inl x}
  have hX : X ∈ P :=
    apexSingleton_mem_of_rootChildrenSingleton_of_redDegreeAtMost
      (k := k) (d := d) (P := P) hd hpart hroot hred x
  have hsubset :
      largeChildBagsRedAdjacentToApex P x ⊆
        P.filter fun A => partitionRedAdj (bonnetDepresGraph k) X A := by
    intro A hA
    change A ∈ (largeChildBags P).filter
      (fun A => partitionRedAdj (bonnetDepresGraph k) A X) at hA
    rw [Finset.mem_filter] at hA ⊢
    exact ⟨(mem_largeChildBags.mp hA.1).1, partitionRedAdj_symm hA.2⟩
  exact (Finset.card_le_card hsubset).trans (hred hX)

/-- Counting incidences by large bags: every large bag contributes at least
`k+1` apex-red incidences. -/
theorem largeChildBags_card_mul_le_incidences_card {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))} :
    (largeChildBags P).card * (k + 1) ≤
      (largeChildBagApexIncidences P).card := by
  classical
  let L := largeChildBags P
  let fiber :
      Finset (BonnetDepresVertex k) →
        Finset (Finset (BonnetDepresVertex k) × Fin (bonnetDepresApexCount k)) :=
    fun A => (apexRedCoordinatesOfBag A).image fun x => (A, x)
  have hInc :
      largeChildBagApexIncidences P = L.biUnion fiber := by
    ext pair
    rcases pair with ⟨A, x⟩
    simp [largeChildBagApexIncidences, L, fiber, apexRedCoordinatesOfBag]
  have hdisj :
      ∀ ⦃A⦄, A ∈ L → ∀ ⦃B⦄, B ∈ L → A ≠ B →
        Disjoint (fiber A) (fiber B) := by
    intro A _hA B _hB hAB
    rw [Finset.disjoint_left]
    intro pair hpairA hpairB
    change pair ∈ (apexRedCoordinatesOfBag A).image (fun x => (A, x)) at hpairA
    change pair ∈ (apexRedCoordinatesOfBag B).image (fun x => (B, x)) at hpairB
    rw [Finset.mem_image] at hpairA hpairB
    rcases hpairA with ⟨x, _hx, rfl⟩
    rcases hpairB with ⟨y, _hy, hpair⟩
    exact hAB (Prod.ext_iff.mp hpair).1.symm
  have hfiber_card :
      ∀ ⦃A⦄, A ∈ L → (fiber A).card = (apexRedCoordinatesOfBag A).card := by
    intro A _hA
    change ((apexRedCoordinatesOfBag A).image (fun x => (A, x))).card =
      (apexRedCoordinatesOfBag A).card
    rw [Finset.card_image_of_injective]
    intro x y hxy
    exact (Prod.ext_iff.mp hxy).2
  calc
    L.card * (k + 1) = ∑ A ∈ L, (k + 1) := by
      simp [Finset.sum_const, Nat.mul_comm]
    _ ≤ ∑ A ∈ L, (fiber A).card := by
      refine Finset.sum_le_sum ?_
      intro A hA
      rw [hfiber_card hA]
      exact le_card_apexRedCoordinatesOfBag_of_isLargeChildBag
        (mem_largeChildBags.mp (by simpa [L] using hA)).2
    _ = (largeChildBagApexIncidences P).card := by
      rw [hInc, Finset.card_biUnion hdisj]

/-- Counting incidences by apex coordinates: each apex singleton has at most `d`
large red-neighbor bags. -/
theorem largeChildBagApexIncidences_card_le {k d : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d) :
    (largeChildBagApexIncidences P).card ≤ bonnetDepresApexCount k * d := by
  classical
  let fiber :
      Fin (bonnetDepresApexCount k) →
        Finset (Finset (BonnetDepresVertex k) × Fin (bonnetDepresApexCount k)) :=
    fun x => (largeChildBagsRedAdjacentToApex P x).image fun A => (A, x)
  have hInc :
      largeChildBagApexIncidences P = Finset.univ.biUnion fiber := by
    ext pair
    rcases pair with ⟨A, x⟩
    simp [largeChildBagApexIncidences, largeChildBagsRedAdjacentToApex, fiber]
  calc
    (largeChildBagApexIncidences P).card =
        (Finset.univ.biUnion fiber).card := by rw [hInc]
    _ ≤ ∑ x : Fin (bonnetDepresApexCount k), (fiber x).card := by
      exact Finset.card_biUnion_le
    _ = ∑ x : Fin (bonnetDepresApexCount k),
        (largeChildBagsRedAdjacentToApex P x).card := by
      refine Finset.sum_congr rfl ?_
      intro x _hx
      change ((largeChildBagsRedAdjacentToApex P x).image (fun A => (A, x))).card =
        (largeChildBagsRedAdjacentToApex P x).card
      rw [Finset.card_image_of_injective]
      intro A B hAB
      exact (Prod.ext_iff.mp hAB).1
    _ ≤ ∑ _x : Fin (bonnetDepresApexCount k), d := by
      refine Finset.sum_le_sum ?_
      intro x _hx
      exact card_largeChildBags_redAdjacent_to_apex_le hd hpart hroot hred x
    _ = bonnetDepresApexCount k * d := by
      simp [Finset.sum_const, Nat.mul_comm]

/-- The paper's coarse bound on `B`: under red-degree at most `2^k`, at most
`2^(k+2)` parts can contain many children of a single tree node. -/
theorem largeChildBags_card_le {k d : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d) :
    (largeChildBags P).card ≤ 2 ^ (k + 2) := by
  have hincLower :=
    largeChildBags_card_mul_le_incidences_card (k := k) (P := P)
  have hincUpper :=
    largeChildBagApexIncidences_card_le
      (k := k) (d := d) (P := P) hd hpart hroot hred
  have harith :
      bonnetDepresApexCount k * d ≤ (k + 1) * 2 ^ (k + 2) := by
    calc
      bonnetDepresApexCount k * d
          ≤ bonnetDepresApexCount k * 2 ^ k :=
        Nat.mul_le_mul_left _ hd
      _ ≤ (4 * (k + 1)) * 2 ^ k := by
        apply Nat.mul_le_mul_right
        unfold bonnetDepresApexCount
        omega
      _ = (k + 1) * 2 ^ (k + 2) := by
        rw [show k + 2 = 2 + k by omega, pow_add]
        change (4 * (k + 1)) * 2 ^ k = (k + 1) * (4 * 2 ^ k)
        rw [Nat.mul_comm 4 (k + 1), Nat.mul_assoc]
  have hmul :
      (largeChildBags P).card * (k + 1) ≤ (2 ^ (k + 2)) * (k + 1) := by
    calc
      (largeChildBags P).card * (k + 1)
          ≤ (largeChildBagApexIncidences P).card := hincLower
      _ ≤ bonnetDepresApexCount k * d := hincUpper
      _ ≤ (k + 1) * 2 ^ (k + 2) := harith
      _ = (2 ^ (k + 2)) * (k + 1) := by rw [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_pos k)


end BonnetDepres

end SimpleGraph
end Lax1Proofs.TwinWidth
